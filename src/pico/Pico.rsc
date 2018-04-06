@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module pico::Pico
  
// Pico, a trivial, classic, language:
// - single scope, no functions
// - integers and strings as types and values
// - assignment, if and while statements
  
import Prelude;

extend analysis::typepal::TypePal;

// ----  Pico syntax -------------------------------------

lexical Id  = [a-z][a-z0-9]* !>> [a-z0-9];
lexical Natural = [0-9]+ ;
lexical String = "\"" ![\"]*  "\"";

layout Layout = WhitespaceAndComment* !>> [\ \t\n\r%];

lexical WhitespaceAndComment 
   = [\ \t\n\r]
   | @category="Comment" ws2: "%" ![%]+ "%"
   ;
 
start syntax Program 
   = program: "begin" Declarations decls {Statement  ";"}* body "end"
   ;

syntax Declarations 
   = "declare" {Declaration ","}* decls ";" ;  
 
syntax Declaration 
    = decl: Id id ":" Type tp
    ;  
 
syntax Type 
   = "natural" 
   | "string"
   ;

syntax Statement 
   = Id var ":=" Expression val                                                                      
   | "if" Expression cond "then" {Statement ";"}*  thenPart "else" {Statement ";"}* elsePart "fi"   
   | "while" Expression cond "do" {Statement ";"}* body "od"                                   
   ;  
      
syntax Expression 
   = Id name                                    
   | String string                          
   | Natural natcon                         
   | bracket "(" Expression e ")"                   
   > left ( Expression lhs "+" Expression rhs                                          
          | Expression lhs "-" Expression rhs  
          )
   ;

// ----  IdRoles, PathLabels and AType ------------------- 

data AType = intType() | strType();  

AType transType((Type) `natural`) = intType();
AType transType((Type) `string`) = strType(); 

str prettyPrintAType(intType()) = "int";
str prettyPrintAType(strType()) = "str";

// ----  Collect definitions, uses and requirements -----------------------

void collect(current: (Program) `begin <Declarations decls> <{Statement  ";"}* body> end`, Collector c){
    c.enterScope(current);
        collect(decls, body, c);
    c.leaveScope(current);
}
 
void collect(current:(Declaration) `<Id id> : <Type tp>`,  Collector c) {
     c.define("<id>", variableId(), id, defType(transType(tp)));
}

void collect(current: (Expression) `<Id name>`, Collector c){
     c.use(name, {variableId()});
}

void collect(current: (Statement) `<Id var> := <Expression val>`, Collector c){
     c.use(var, {variableId()});
     c.requireEqual(var, val, error(current, "Lhs %t should have same type as rhs", var));
     collect(val, c);
}

void collect(current: (Statement) `if <Expression cond> then <{Statement ";"}*  thenPart> else <{Statement ";"}* elsePart> fi`, Collector c){
     c.requireEqual(cond, intType(), error(cond, "Condition should be `int`, found %t", cond));
     collect(cond, thenPart, elsePart, c);
}

void collect(current: (Statement) `while <Expression cond> do <{Statement ";"}* body> od`, Collector c){
     c.requireEqual(cond, intType(), error(cond, "Condition should be `int`, found %t", cond));
     collect(cond, body, c);
}

void collect(current: (Expression) `<Expression lhs> + <Expression rhs>`, Collector c){
     c.calculate("addition", current, [lhs, rhs], 
        AType (Solver s) { switch([s.getType(lhs), s.getType(rhs)]){
                   case [intType(), intType()]: return intType();
                   case [strType(), strType()]: return strType();
                   default:
                       s.report(error(current, "Operator `+` cannot be applied to %t and %t", lhs, rhs));
                   }
                 });
     collect(lhs, rhs, c);
}

void collect(current: (Expression) `<Expression lhs> - <Expression rhs>`, Collector c){
    c.requireEqual(lhs, intType(), error(lhs, "Left argument of `-` should be `int`, found %t", lhs));
    c.requireEqual(rhs, intType(), error(rhs, "Right argument of `-` should be `int`, found %t", rhs));
    c.fact(current, intType());
    collect(lhs, rhs, c);
}
 
void collect(current: (Expression) `<String string>`, Collector c){
    c.fact(current, strType());
}

void collect(current: (Expression) `<Natural natcon>`, Collector c){
    c.fact(current, intType());
}

// ----  Examples & Tests --------------------------------

TModel picoTModelFromName(str name, bool debug = false) {
    Tree pt = parse(#Program, |project://typepal-examples/src/pico/<name>.pico|);
    return collectAndSolve(pt, debug=debug);
}

TModel picoTModelFromTree(Tree pt, bool debug = false) {
    return collectAndSolve(pt, debug=debug);
}

 
bool testPico(bool debug = false) {
    return runTests([|project://typepal-examples/src/pico/pico.ttl|], #start[Program], TModel (Tree t) {
        return picoTModelFromTree(t, debug=debug);
    });
}
