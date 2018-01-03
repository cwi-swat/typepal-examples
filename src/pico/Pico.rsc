@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module pico::Pico

// Pico, a trivial language, single scope, no functions

import Prelude;

extend analysis::typepal::TypePal;

// ----  Pico syntax -------------------------------------

lexical Id  = [a-z][a-z0-9]* !>> [a-z0-9];
lexical Natural = [0-9]+ ;
lexical String = "\"" ![\"]*  "\"";

layout Layout = WhitespaceAndComment* !>> [\ \t\n\r%];

lexical WhitespaceAndComment 
   = [\ \t\n\r]
   | @category="Comment" ws2:
    "%" ![%]+ "%"
//   | @category="Comment" ws3: "{" ![\n}]*  "}"$
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

data IdRole = variableId();

data AType = intType() | strType();  

AType transType((Type) `natural`) = intType();
AType transType((Type) `string`) = strType(); 

str prettyPrintAType(intType()) = "int";
str prettyPrintAType(strType()) = "str";

// ----  Collect definitions, uses and requirements -----------------------
 
void collect(current:(Declaration) `<Id id> : <Type tp>`,  TBuilder tb) {
     tb.define("<id>", variableId(), id, defType(transType(tp)));
}

void collect(current: (Expression) `<Id name>`, TBuilder tb){
     tb.use(name, {variableId()});
}

void collect(current: (Statement) `<Id var> := <Expression val>`, TBuilder tb){
     tb.use(var, {variableId()});
     tb.require("assignment", current, [var, val],
        (){ equal(getType(var), getType(val)) || reportError(current, "Lhs <fmt(var)> should have same type as rhs"); });
     collect(val, tb);
}

void collect(current: (Statement) `if <Expression cond> then <{Statement ";"}*  thenPart> else <{Statement ";"}* elsePart> fi`, TBuilder tb){
     tb.require("int_condition", current, [cond],
        () { equal(getType(cond), intType()) || reportError(cond, "Condition should be `int`, found <fmt(cond)>"); });
     collect(cond, thenPart, elsePart, tb);
}

void collect(current: (Statement) `while <Expression cond> do <{Statement ";"}* body> od`, TBuilder tb){
     tb.require("int_condition", current, [cond],
        () { equal(getType(cond), intType()) || reportError(cond, "Condition should be `int`, found <fmt(cond)>"); });
     collect(cond, body, tb);
}

void collect(current: (Expression) `<Expression lhs> + <Expression rhs>`, TBuilder tb){
     tb.calculate("addition", current, [lhs, rhs], 
        AType () { switch([getType(lhs), getType(rhs)]){
                   case [intType(), intType()]: return intType();
                   case [strType(), strType()]: return strType();
                   default:
                       reportError(current, "Operator `+` cannot be applied to <fmt(lhs)> and <fmt(rhs)>");
                   }
                 });
     collect(lhs, rhs, tb);
}

void collect(current: (Expression) `<Expression lhs> - <Expression rhs>`, TBuilder tb){
     tb.calculate("subtraction", current, [lhs, rhs],
        AType () { equal(getType(lhs), intType()) || reportError(lhs, "Left argument of `-` should be `int`, found <fmt(lhs)>");
                   equal(getType(rhs), intType()) || reportError(rhs, "Right argument of `-` should be `int`, found <fmt(rhs)>");
                   return intType();
                 });
     collect(lhs, rhs, tb);
}
 
void collect(current: (Expression) `<String string>`, TBuilder tb){
    tb.fact(current, strType());
}

void collect(current: (Expression) `<Natural natcon>`, TBuilder tb){
    tb.fact(current, intType());
}

// ----  Examples & Tests --------------------------------

public Program samplePico(str name) = parse(#Program, |project://typepal-examples/src/pico/<name>.pico|);
                     
list[Message] validatePico(str name) {
    Tree pt = samplePico(name);
    tb = newTBuilder(pt);
    collect(pt, tb);
    tm = tb.build();
    tm = validate(tm);
    return tm.messages;
}
 value main() = validatePico("e1");
