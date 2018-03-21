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
extend analysis::typepal::Collector;
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
   | "fun" Id name "{" Expression exp "}"
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

void collect(current: (Expression) `fun <Id name> { <Expression body> }`, TBuilder tb) {
    tb.enterScope(current);  
        tau1 = tb.newTypeVar(name); 
        tau2 = tb.newTypeVar(body);
        tb.define("<name>", variableId(), name, defType(tau1));
        tb.calculate("function declaration", current, [],  
            AType(TChecker c) {
                     res = functionType(tau1, tau2);
                     println("res = <res>");
                     return res;
                   });
        tb.requireEager("body", body, [body], 
            void (TChecker c){ c.unify(tau2, c.getType(body)) || c.reportError(body, "type of body");} );
        collect(body, tb);
     tb.leaveScope(current);
}

void collect(current: (Expression) `<Expression exp1>(<Expression exp2>)`, TBuilder tb) { 
iprintln(exp1);
     tau1 = tb.newTypeVar(exp1); 
     tau2 = tb.newTypeVar(exp2); 
     
     tb.calculateEager("application", current, [exp1, exp2],
        AType (TChecker c) { 
              c.unify(functionType(tau1, tau2), c.getType(exp1)) || c.reportError(exp1, "Function type expected, found <c.fmt(exp1)>");
              c.unify(c.getType(exp2), tau1) || c.reportError(exp2, "Incorrect type of actual parameter");
              return tau2;
            });
      collect(exp1, exp2, tb);
}


void collect(current: (Expression) `let <Id name> = <Expression exp1> in <Expression exp2> end`, TBuilder tb) { 
    tb.enterScope(current); 
        tb.define("<name>", variableId(), name, defType([exp1], AType(TChecker c) { return c.getType(exp1); })); // <<<
        tb.calculate("let body", current, [exp2],
            AType(TChecker c){ return c.getType(exp2); });
        collect(exp1, exp2, tb);
    tb.leaveScope(current);
}

void collect(current: (Expression) `if <Expression cond> then <Expression thenPart> else <Expression elsePart> fi`, TBuilder tb){
     tb.calculate("if", current, [cond, thenPart, elsePart],
        AType (TChecker c) { 
            c.unify(c.getType(cond), boolType()) || c.reportError(cond, "Condition");
            c.unify(c.getType(thenPart), c.getType(elsePart)) || reportError(current, "thenPart and elsePart should have same type");
            return c.getType(thenPart); 
        }); 
     collect(cond, thenPart, elsePart, tb);
}

void collect(current: (Expression) `<Expression lhs> + <Expression rhs>`, TBuilder tb){
     tb.calculate("addition", current, [lhs,rhs],
         AType (TChecker c) { 
            targs = atypeList([c.getType(lhs), c.getType(rhs)]);
            if(c.unify(targs, atypeList([intType(), intType()]))) return intType();
                reportError(current, "No version of + is applicable for <c.fmt([lhs, rhs])>");
        });
     collect(lhs, rhs, tb); 
}

void collect(current: (Expression) `<Expression lhs> && <Expression rhs>`, TBuilder tb){
     tb.calculate("and", current, [lhs, rhs],
        AType (TChecker c) {
            c.unify(c.getType(lhs), boolType()) || c.reportError(lhs, "Expected `bool`, found <c.fmt(lhs)>");
            c.unify(c.getType(rhs), boolType()) || c.reportError(rhs, "Expected `bool`, found <c.fmt(rhs)>");
            return boolType();
        });
    collect(lhs, rhs, tb);
}

void collect(current: (Expression) `( <Expression exp> )`, TBuilder tb){
    tb.calculate("brackets", current, [exp],  AType(TChecker c) { return c.getType(exp); });
    collect(exp, tb);
}

void collect(current: (Expression) `<Id name>`, TBuilder tb){
     tb.use(name, {variableId()});
}

void collect(current: (Expression) `<Boolean boolcon>`, TBuilder tb){
     tb.fact(current, boolType());
}

void collect(current: (Expression) `<Integer intcon>`, TBuilder tb){
     tb.fact(current, intType());
}

// ----  Examples & Tests --------------------------------

private Expression sample(str name) = parse(#start[Expression], |project://typepal-examples/src/itfun/<name>.it|).top;

list[Message] validateItFun(str name, bool debug = false){
    Tree pt =  parse(#start[Expression], |project://typepal-examples/src/itfun/<name>.it|).top;
    return itFunTModelFromTree(sample(name), debug=debug).messages;
}

TModel itFunTModelFromTree(Tree pt, bool debug=false){
    return collectAndCheck(pt, debug=debug);
}

void testItFun() {
    runTests([|project://typepal-examples/src/itfun/tests.ttl|], #Expression, itFunTModelFromTree);
}
