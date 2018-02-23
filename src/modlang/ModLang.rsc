@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module modlang::ModLang

extend analysis::typepal::TypePal;
extend analysis::typepal::TestFramework;

// ----  ModLang syntax ----------------------------------

lexical Id      = ([a-z][a-z0-9]* !>> [a-z0-9]) \ Reserved;
lexical ModId   = ([A-Z][a-z0-9]* !>> [a-z0-9]) \ Reserved;
lexical Integer = [0-9]+ ; 
lexical String = "\"" ![\"]*  "\"";

keyword Reserved = "module" | "import" | "def" | "fun";

layout Layout = WhitespaceAndComment* !>> [\ \t\n\r%];

lexical WhitespaceAndComment 
   = [\ \t\n\r]
   | @category="Comment" ws2:
    "%" ![%]+ "%"
//   | @category="Comment" ws3: "{" ![\n}]*  "}"$
   ;

start syntax Program 
    = ModuleDecl* modules
    ;

syntax ModuleDecl
    = "module" ModId mid  "{" Decl* decls "}"
    ;
syntax Decl
    = ImportDecl importDecl
    | VarDecl varDecl
    ;
syntax ImportDecl
    = "import" ModId mid ";"
    ;

syntax VarDecl
    = "def" Id id "=" Expression expression ";"
    ;
     
syntax Expression 
   = Id id
   | Integer intcon 
   | String strcon
   | bracket "(" Expression e ")"     
   | abstraction: "fun" Id id "{" Expression exp "}"
   | left application: Expression exp1 "(" Expression exp2  ")" 
   > left Expression exp1 "*" Expression exp2 
   > left Expression exp1 "+" Expression exp2 
   ;

// ----  IdRoles, PathLabels and AType ------------------- 
     
data IdRole
    = moduleId()
    | parameterId()
    ;
    
data PathRole
    = importPath()
    ;

data AType   
    = intType()                                     // int type
    | strType()                                     // str type
    | functionType(AType from, AType to)            // function type
    ;
    
str prettyPrintAType(intType()) = "int";
str prettyPrintAType(strType()) = "str";

// ----  Collect facts & constraints ------------------------------------

void collect(current: (ModuleDecl) `module <ModId mid> { <Decl* decls> }`, TBuilder tb) {
     tb.define("<mid>", moduleId(), mid, noDefInfo());
     //tb.enterScope(current);
        collect(decls, tb);
     //tb.leaveScope(current);
}

void collect(current: (ImportDecl) `import <ModId mid> ;`, TBuilder tb){
     tb.useViaPath(mid, {moduleId()}, importPath());
}

void collect(current: (Expression) `fun <Id id> { <Expression body> }`, TBuilder tb) {
     tb.enterScope(current);
        tau1 = tb.newTypeVar(id); 
        tau2 = tb.newTypeVar(body);
     
        tb.define("<id>", parameterId(), id, defType(tau1));
        tb.calculate("function declaration", current, [body],  
            AType() {
                     res = functionType(tau1, tau2);
                     println("res = <res>");
                     return res;
                   });
        collect(body, tb);
     tb.leaveScope(current);
}

void collect(current: (VarDecl) `def <Id id> = <Expression expression> ;`, TBuilder tb)     {
     tb.define("<id>", variableId(), id, defType([expression], AType(){ return getType(expression); })); // <<<
     collect(expression, tb);
}

void collect(current: (Expression) `<Id name>`,  TBuilder tb){
     tb.use(name, {variableId(), parameterId()});
}

void collect(current: (Expression) `<Expression exp1>(<Expression exp2>)`, TBuilder tb) { 
     tau1 = tb.newTypeVar(exp1); 
     tau2 = tb.newTypeVar(exp2); 
     tb.calculateEager("application", current, [exp1, exp2],
        AType () { 
                   unify(functionType(tau1, tau2), getType(exp1)) || reportError(exp1, "Function type expected, found <fmt(exp1)>");
                   unify(getType(exp2), tau1) || reportError(exp2, "Expected <fmt(tau1)> as argument,  found <fmt(exp2)>");
                   return tau2;
            });
     collect(exp1, exp2, tb);
}

void collect(current: (Expression) `<Expression lhs> + <Expression rhs>`, TBuilder tb){
     tb.calculate("addition", current, [lhs,rhs],
         AType () { 
                    targs = atypeList([getType(lhs), getType(rhs)]);
                    if(unify(targs, atypeList([intType(), intType()]))) return intType();
                    if(unify(targs, atypeList([strType(), strType()]))) return strType();
                    reportError(current, "No version of + is applicable for <fmt([lhs, rhs])>");
                  });
     collect(lhs, rhs, tb);
}

void collect(current: (Expression) `<Expression lhs> * <Expression rhs>`, TBuilder tb){
     tb.calculate("multiplication", current, [lhs, rhs],
        AType () { unify(getType(lhs), intType()) || reportError(lhs, "Expected `int`, found <fmt(lhs)>");
                   unify(getType(rhs), intType()) || reportError(rhs, "Expected `int`, found <fmt(rhs)>");
                   return intType();
                  });
     collect(lhs, rhs, tb);
}

void collect(current: (Expression) `( <Expression exp> )`, TBuilder tb){
    tb.calculate("brackets", current, [exp],  AType() { return getType(exp); });
    collect(exp, tb);
}

void collect(current: (Expression) `<String string>`, TBuilder tb){
     tb.fact(current, strType());
}

void collect(current: (Expression) `<Integer intcon>`, TBuilder tb){
     tb.fact(current, intType());
}

// ---- Refine use/def: enforce def before use -----------

Accept modLangIsAcceptableSimple(TModel tm, Key def, Use use){
    res = variableId() in use.idRoles
           && def < use.scope 
           && !(use.occ.offset >= def.offset)
           ? ignoreContinue()
           : acceptBinding();
    println("modLangIsAcceptableSimple: <def>, <use> ==\> <res>");
    return res;
}

TypePalConfig modLangTypePalConfig()
    = tconfig(
        isAcceptableSimple            = modLangIsAcceptableSimple,
        lookup                        = lookupWide
    );

// ----  Examples & Tests --------------------------------

Program sample(str name) = parse(#start[Program], |project://typepal-examples/src/modlang/<name>.modlang|).top;

list[Message] validateModLang(str name, bool debug = false) = modLangTModel(name, debug=debug).messages;

TModel modLangTModel(str name, bool debug = false){
   return modLangTModelFromTree(sample(name), debug=debug);
}

TModel modLangTModelFromTree(Tree pt, bool debug=false){
    tb = newTBuilder(pt, config = modLangTypePalConfig());
    collect(pt, tb);
    tm = tb.build();
    return validate(tm, debug=debug);
}

void testModLang() {
    runTests([|project://typepal-examples/src/modlang/tests.ttl|], #Program, modLangTModelFromTree);
}