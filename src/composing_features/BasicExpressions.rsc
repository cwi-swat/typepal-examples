module composing_features::BasicExpressions

import analysis::typepal::TestFramework;
extend analysis::typepal::TypePal;
extend analysis::typepal::Collector;
import ParseTree;

extend lang::std::Layout;

// **** Base expression syntax

start syntax Expression 
    = Integer i
    | String s
    | Id use
    | left Expression lhs "+" Expression rhs
    ;
    
syntax PrimitiveType = "int" | "str";

syntax Type = PrimitiveType;

keyword Keywords = "int" | "str";

syntax Type =  Id typ;

lexical Id = ([a-z A-Z][a-z A-Z 0-9]* !>> [a-z A-Z 0-9]) \ Keywords;

lexical Integer = [0-9]+ !>> [0-9];

lexical String = [\"] ![\"]* [\"];

// **** Extend Typepal's ATypes, IdRoles and PathRoles

data AType
    = intType()
    | strType()
    ;

//AType convertType((Type)`int`) = intType();
//AType convertType((Type)`str`) = strType();

str prettyPrintAType(intType()) = "int";
str prettyPrintAType(strType()) = "str";

// **** Configure

data TypePalConfig(set[IdRole] useRoles = {});

// **** Collect facts and constraints

void collect(current:(Expression)`<Integer _>`, Collector c) {
    c.fact(current, intType());
}

void collect(current:(Expression)`<String _>`, Collector c) {
    c.fact(current, strType());
}

void collect(current:(Expression)`<Id use>`, Collector c) {
    c.use(use, c.getConfig().useRoles);
}

AType infixPlus(intType(), intType(), Tree current, Solver s) = intType();
AType infixPlus(strType(), strType(), Tree current, Solver s) = strType();

default AType infixPlus(AType lhsType, AType rhsType, Tree current, Solver s) {
   s.reportError(current, "+ not defined between <s.fmt(lhsType)> and <s.fmt(rhsType)>");
}

void collect(current:(Expression)`<Expression lhs> + <Expression rhs>`, Collector c) {
    c.calculate("+ types", current, [lhs, rhs], 
        AType (Solver s) {
            return infixPlus(s.getType(lhs), s.getType(rhs), current, s);
        });
    collect(lhs, rhs, c);
}

// **** Testing

TModel expressionTModule(Tree pt, bool debug){
    return collectAndSolve(pt, debug=debug);
}

bool testExpressions(bool debug = false) {
    return runTests([|project://typepal-examples/src/features/tests/expressions.ttl|], #start[Expression], TModel (Tree t) {
        return expressionTModule(t, debug);
    });
}