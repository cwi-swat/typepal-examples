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
extend analysis::typepal::TestFramework;

// ----  DTFun syntax ------------------------------------

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
   | Expression exp1 "(" Expression exp2  ")"
   | "let" Id name ":" Type tp "=" Expression exp1 "in" Expression exp2 "end"
   | "if" Expression cond "then" Expression thenPart "else" Expression elsePart "fi" 
   ;

// ----  IdRoles, PathLabels and AType ------------------- 

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

str AType2String(intType()) = "int";
str AType2String(boolType()) = "bool";
str AType2String(functionType(AType from, AType to)) = "fun <AType2String(from)> -\> <AType2String(to)>";

// ----  function declaration

void collect(current: (Expression) `fun <Id name> : <Type tp> { <Expression body> }`, TBuilder tb) {   
     tb.define("<name>", variableId(), name, defType(transType(tp)));
     tb.enterScope(current);
         tb.calculate("function declaration", current, [body], AType(){ return functionType(transType(tp), getType(body)); });
         collectParts(current, tb);
     tb.leaveScope(current);
}

// ---- let

void collect(current: (Expression) `let <Id name> : <Type tp> = <Expression exp1> in <Expression exp2> end`, TBuilder tb) {  
     tb.enterScope(current);
         tb.define("<name>", variableId(), name, defType(transType(tp)));
         tb.calculate("let", current, [exp2], AType() { return getType(exp2); } );
         collectParts(current, tb);  
     tb.leaveScope(current);
}

// ---- identifier
 
void collect(current: (Expression) `<Id name>`,  TBuilder tb){
     tb.use(name, {variableId()});
}

// ---- function application

void collect(current: (Expression) `<Expression exp1> (<Expression exp2>)`, TBuilder tb) { 
     tb.require("application", current, [exp1, exp2],
         () {  if(functionType(tau1, tau2) := getType(exp1)){
                  equal(getType(exp2), tau1, onError(exp2, "Incorrect type of actual parameter"));
                  fact(current, tau2);
               } else {
                  reportError(exp1, "Function type expected");
               }
            });
     collectParts(current, tb);
}

// ---- if-then-else

void collect(current: (Expression) `if <Expression cond> then <Expression thenPart> else <Expression elsePart> fi`, TBuilder tb){
     tb.calculate("if", current, [cond, thenPart, elsePart],
         () { equal(getType(cond), boolType(), onError(cond, "Condition"));
              equal(getType(thenPart), getType(elsePart), onError(current, "thenPart and elsePart should have same type"));
              return getType(thenPart);
            }); 
      collectParts(current, tb);
}

// ---- addition

void collect(current: (Expression) `<Expression lhs> + <Expression rhs>`, TBuilder tb){
     tb.calculate("addition", current, [lhs, rhs],
         () { equal(getType(lhs), intType(), onError(lhs, "Lhs of +"));
              equal(getType(rhs), intType(), onError(rhs, "Rhs of +"));
              return intType();
            });
      collectParts(current, tb);
} 

// ---- and

void collect(current: (Expression) `<Expression lhs> && <Expression rhs>`, TBuilder tb){
     tb.calculate("and", current, [lhs, rhs],
         () { equal(getType(lhs), boolType(), onError(lhs, "Lhs of &&"));
              equal(getType(rhs), boolType(), onError(rhs, "Rhs of &&"));
              return intType();
            });
      collectParts(current, tb);
} 

// ---- brackets

void collect(current: (Expression) `( <Expression exp> )`, TBuilder tb){
     tb.calculate("bracket", current, [exp], AType(){ return getType(exp); });
     collectParts(current, tb);
}

// ---- constants

void collect(current: (Expression) `<Boolean boolcon>`, TBuilder tb){
     tb.fact(current, boolType());
}

void collect(current: (Expression) `<Integer intcon>`, TBuilder tb){
     tb.fact(current, intType());
}

// ----  Examples & Tests --------------------------------

private Expression sampleDT(str name) = parse(#Expression, |project://typepal-examples/src/dtfun/<name>.dt|);

TModel dtfunTModel(str name){
   return dtfunTModel(sampleDT(name));
}

TModel dtfunTModel(Expression pt){
    tb = newTBuilder(pt);
    collect(pt, tb);
    return tb.build();
}

TModel dtfunTModelFromStr(str text){
    pt = parse(#start[Expression], text).top;
    return dtfunTModel(pt);
}

set[Message] dtfunValidate(str name) {
    tm = dtfunTModel(name);
    return validate(tm).messages;
}

void dtfunTest() {
     runTests([|project://typepal-examples/src/dtfun/tests.ttl|], dtfunTModelFromStr);
}
