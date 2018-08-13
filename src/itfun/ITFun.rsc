@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module itfun::ITFun
// Functional language with inferred types (MiniML-like)

extend analysis::typepal::TypePal;
extend analysis::typepal::TestFramework;

import IO;
import ParseTree;

// ----  ITFun syntax ------------------------------------

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
 
start syntax Expression 
   = 
     Id name
   | Integer intcon 
   | Boolean boolcon
   | bracket "(" Expression e ")"                   
   > left ( Expression lhs "+" Expression rhs                                          
          | Expression lhs "&&" Expression rhs  
          )
   | "fun" Id arg "{" Expression exp "}"
   | Expression exp1 "(" Expression exp2  ")"
   | "let" Id name "=" Expression exp1 "in" Expression exp2 "end"
   | "if" Expression cond "then" Expression thenPart "else" Expression elsePart "fi" 
   ;

// ----  IdRoles, PathLabels and AType ------------------- 

data AType   
    = intType()                                     // int type
    | boolType()                                    // bool type
    | functionType(AType from, AType to)            // function type
    ;

str prettyPrintAType(intType()) = "int";
str prettyPrintAType(boolType()) = "bool";
str prettyPrintAType(functionType(AType from, AType to)) = "fun <prettyPrintAType(from)> -\> <prettyPrintAType(to)>";

// ----  Collect defines, uses & constraints --------------------------

void collect(current: (Expression) `fun <Id arg> { <Expression body> }`, Collector c) {
    c.enterScope(current);  
        tau1 = c.newTypeVar(arg); 
        tau2 = c.newTypeVar(body);
        c.fact(current, functionType(tau1, tau2));
        c.define("<arg>", variableId(), arg, defType(tau1));
        //c.requireUnify(tau2, body, error(body, "type of body"));
        collect(body, c);
     c.leaveScope(current);
}

void collect(current: (Expression) `<Expression exp1>(<Expression exp2>)`, Collector c) { 
     tau1 = c.newTypeVar(exp1); 
     tau2 = c.newTypeVar(exp2); 
  
     c.calculateEager("application", current, [exp1, exp2],
        AType (Solver s) { 
              s.requireUnify(functionType(tau1, tau2), exp1, error(exp1, "Function type expected, found %t", exp1));
              s.requireUnify(tau1, exp2, error(exp2, "Incorrect type of actual parameter"));  
              println(s.instantiate(tau2));            
              return tau2;
            });
      collect(exp1, exp2, c);
}


void collect(current: (Expression) `let <Id name> = <Expression exp1> in <Expression exp2> end`, Collector c) { 
    c.enterScope(current); 
        c.define("<name>", variableId(), name, defType(exp1)); // <<<
        c.fact(current, exp2);
        collect(exp1, exp2, c);
    c.leaveScope(current);
}

void collect(current: (Expression) `if <Expression cond> then <Expression thenPart> else <Expression elsePart> fi`, Collector c){
     c.calculate("if", current, [cond, thenPart, elsePart],
        AType (Solver s) { 
            s.requireUnify(cond, boolType(), error(cond, "Condition"));
            s.requireUnify(thenPart, elsePart, error(current, "thenPart and elsePart should have same type"));
            return s.getType(thenPart); 
        }); 
     collect(cond, thenPart, elsePart, c);
}

void collect(current: (Expression) `<Expression lhs> + <Expression rhs>`, Collector c){
     c.calculateEager("addition", current, [lhs,rhs],
         AType (Solver s) { 
            targs = atypeList([s.getType(lhs), s.getType(rhs)]);
            if(s.unify(targs, atypeList([intType(), intType()]))) return intType();
            s.report(error(current, "No version of + is applicable for %t and %t", lhs, rhs));
        });
     collect(lhs, rhs, c); 
}

void collect(current: (Expression) `<Expression lhs> && <Expression rhs>`, Collector c){
     c.calculateEager("and", current, [lhs, rhs],
        AType (Solver s) {
            s.requireUnify(lhs, boolType(), error(lhs, "Expected `bool`, found %t", lhs));
            s.requireUnify(rhs, boolType(), error(rhs, "Expected `bool`, found %t", rhs));
            return boolType();
        });
    collect(lhs, rhs, c);
}

void collect(current: (Expression) `( <Expression exp> )`, Collector c){
    c.fact(current, exp);
    collect(exp, c);
}

void collect(current: (Expression) `<Id name>`, Collector c){
     c.use(name, {variableId()});
}

void collect(current: (Expression) `<Boolean boolcon>`, Collector c){
     c.fact(current, boolType());
}

void collect(current: (Expression) `<Integer intcon>`, Collector c){
     c.fact(current, intType());
}

// ----  Examples & Tests --------------------------------

private Expression sample(str name) = parse(#start[Expression], |project://typepal-examples/src/itfun/<name>.it|).top;

list[Message] validateItFun(str name, bool debug = false){
    Tree pt =  parse(#start[Expression], |project://typepal-examples/src/itfun/<name>.it|).top;
    return itFunTModelFromTree(sample(name), debug=debug).messages;
}

TModel itFunTModelFromTree(Tree pt, bool debug=false){
    return collectAndSolve(pt, debug=debug);
}

void testItFun() {
    runTests([|project://typepal-examples/src/itfun/tests.ttl|], #Expression, itFunTModelFromTree);
}
