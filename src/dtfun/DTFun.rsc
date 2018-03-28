@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module dtfun::DTFun
 
// Functional language with declared types
 
extend analysis::typepal::TypePal;

import ParseTree;

// ----  DTFun syntax ---------------------------------------------------------

lexical Id  = ([a-z][a-z0-9]* !>> [a-z0-9]) \ Reserved;
lexical Integer = [0-9]+ !>> [0-9]; 
lexical Boolean = "true" | "false";

keyword Reserved = "true" | "false" | "if" | "then" | "else" | "fi" | "let" | "in" | "fun" | "end";

layout Layout = WhitespaceAndComment* !>> [\ \t\n\r%];

lexical WhitespaceAndComment 
   = [\ \t\n\r]
   | @category="Comment" ws2:
    "%" ![%]+ "%"
   | @category="Comment" ws3: "{" ![\n}]*  "}"$
   ;

syntax Type 
   = "int" 
   | "bool"
   | Type from "-\>" Type to
   ; 
   
start syntax Expression 
   = 
     Id name
   | Integer intcon 
   | Boolean boolcon
   | bracket "(" Expression e ")"                   
   > left ( Expression lhs "+" Expression rhs                                          
          | Expression lhs "&&" Expression rhs  
          )
   | "fun" Id name ":" Type tp "{" Expression exp "}"
   |  Expression exp1 "(" Expression exp2  ")"
   | "let" Id name ":" Type tp "=" Expression exp1 "in" Expression exp2 "end"
   | "if" Expression cond "then" Expression thenPart "else" Expression elsePart "fi" 
   ;

// ----  IdRoles, PathLabels and AType ---------------------------------------- 

data IdRole
    = variableId()
    ;

data AType   
    = intType()                                     // int type
    | boolType()                                    // bool type
    | functionType(AType from, AType to)            // function type
    ; 

AType transType((Type) `int`) = intType();
AType transType((Type) `bool`) = boolType(); 
AType transType((Type) `<Type from> -\> <Type to>`) = functionType(transType(from), transType(to)); 

str prettyPrintAType(intType()) = "int";
str prettyPrintAType(boolType()) = "bool";
str prettyPrintAType(functionType(AType from, AType to)) = "fun <prettyPrintAType(from)> -\> <prettyPrintAType(to)>";

// ----  function declaration

void collect(current: (Expression) `fun <Id name> : <Type tp> { <Expression body> }`, Collector c) {   
     c.enterScope(current);
        c.define("<name>", variableId(), name, defType(transType(tp)));
        c.calculate("function declaration", current, [body], AType(Solver s){ return functionType(transType(tp), s.getType(body)); });
        collect(body, c);
     c.leaveScope(current);
}

// ---- let

void collect(current: (Expression) `let <Id name> : <Type tp> = <Expression exp1> in <Expression exp2> end`, Collector c) {  
     c.enterScope(current);
         c.define("<name>", variableId(), name, defType(transType(tp)));
         c.calculate("let", current, [exp2], AType(Solver s) { return s.getType(exp2); } );
         collect(exp1, exp2, c);  
     c.leaveScope(current);
}

// ---- identifier
 
void collect(current: (Expression) `<Id name>`,  Collector c){
     c.use(name, {variableId()});
}

// ---- function application

void collect(current: (Expression) `<Expression exp1> (<Expression exp2>)`, Collector c) { 
     c.require("application", current, [exp1, exp2],
         void (Solver s) {  if(functionType(tau1, tau2) := s.getType(exp1)){
                  s.requireEqual(exp2, tau1, error(exp2, "Incorrect type of actual parameter"));
                  s.fact(current, tau2);
               } else {
                  s.report(error(exp1, "Function type expected"));
               }
        });
     collect(exp1, exp2, c);
}

// ---- if-then-else

void collect(current: (Expression) `if <Expression cond> then <Expression thenPart> else <Expression elsePart> fi`, Collector c){
     c.calculate("if", current, [cond, thenPart, elsePart],
        AType (Solver s) { 
            s.requireEqual(cond, boolType(), error(cond, "Condition"));
            s.requireEqual(thenPart, elsePart, error(current, "thenPart and elsePart should have same type"));
            return s.getType(thenPart);
        }); 
      collect(cond, thenPart, elsePart, c);
}

// ---- addition

void collect(current: (Expression) `<Expression lhs> + <Expression rhs>`, Collector c){
     c.calculate("addition", current, [lhs, rhs],
        AType (Solver s) { 
            s.requireEqual(lhs, intType(), error(lhs, "Lhs of +"));
            s.requireEqual(rhs, intType(), error(rhs, "Rhs of +"));
            return intType();
        });
      collect(lhs, rhs, c);
} 

// ---- and

void collect(current: (Expression) `<Expression lhs> && <Expression rhs>`, Collector c){
     c.calculate("and", current, [lhs, rhs],
        AType (Solver s) { 
            s.requireEqual(lhs, boolType(), error(lhs, "Lhs of &&"));
            s.requireEqual(rhs, boolType(), error(rhs, "Rhs of &&"));
            return intType();
        });
      collect(lhs, rhs, c);
} 

// ---- brackets

void collect(current: (Expression) `( <Expression exp> )`, Collector c){
     c.calculate("bracket", current, [exp], AType(Solver s){ return s.getType(exp); });
     collect(exp, c);
}

// ---- constants

void collect(current: (Expression) `<Boolean boolcon>`, Collector c){
     c.fact(current, boolType());
}

void collect(current: (Expression) `<Integer intcon>`, Collector c){
     c.fact(current, intType());
}

// ----  Testing --------------------------------------------------------------

private Expression sampleDT(str name) = parse(#Expression, |project://typepal-examples/src/dtfun/<name>.dt|);

TModel dtfunTModel(str name){
   return dtfunTModelFromTree(sampleDT(name));
}

TModel dtfunTModelFromTree(Tree pt, bool debug = false){
    return collectAndSolve(pt, debug=debug);
}

TModel dtfunTModelFromStr(str text){
    pt = parse(#start[Expression], text).top;
    return dtfunTModelFromTree(pt);
}

list[Message] dtfunValidate(str name) {
    tm = dtfunTModel(name);
    return tm.messages;
}

void testDTFun() {
     runTests([|project://typepal-examples/src/dtfun/tests.ttl|], #Expression, dtfunTModelFromTree);
}
