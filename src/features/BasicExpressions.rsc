module features::BasicExpressions

import analysis::typepal::TestFramework;
extend analysis::typepal::TypePal;

extend lang::std::Layout;

start syntax Expression 
    = Integer i
    | String s
    | Id use
    | left Expression lhs "+" Expression rhs
    ;
    
lexical Type = "int" | "str";

keyword Keywords = "int" | "str";

lexical Id = ([a-z A-Z][a-z A-Z 0-9]* !>> [a-z A-Z 0-9]) \ Keywords;

lexical Integer = [0-9]+ !>> [0-9];

lexical String = [\"] ![\"]* [\"];


data TypePalConfig(set[IdRole] useRoles = {});

data AType
    = intType()
    | strType()
    ;

AType convertType((Type)`int`) = intType();
AType convertType((Type)`str`) = strType();

str prettyPrintAType(intType()) = "int";
str prettyPrintAType(strType()) = "str";


void collect(current:(Expression)`<Integer _>`, TBuilder tb) {
    tb.fact(current, intType());
}

void collect(current:(Expression)`<String _>`, TBuilder tb) {
    tb.fact(current, strType());
}

void collect(current:(Expression)`<Id use>`, TBuilder tb) {
    tb.use(use, tb.getConfig().useRoles);
}

AType infixPlus(intType(), intType(), Tree current) = intType();
AType infixPlus(strType(), strType(), Tree current) = strType();

default AType infixPlus(AType lhsType, AType rhsType, Tree current) {
    reportError(current, "+ not defined between <fmt(lhsType)> and <fmt(rhsType)>");
}

void collect(current:(Expression)`<Expression lhs> + <Expression rhs>`, TBuilder tb) {
    tb.calculate("+ types", current, [lhs, rhs], AType () {
        return infixPlus(getType(lhs), getType(rhs), current);
    });
    collect(lhs, rhs, tb);
}


TModel expressionTModule(Tree pt, bool debug){
    if(pt has top) pt = pt.top;
    tb = newTBuilder(pt, debug=debug);
    collect(pt, tb);
    tm = tb.build();
    tm = validate(tm, debug=debug);
    return tm;
}

bool testExpressions(bool debug = false) {
    return runTests([|project://typepal-examples/src/features/tests/expressions.ttl|], #start[Expression], TModel (Tree t) {
        return expressionTModule(t, debug);
    });
}