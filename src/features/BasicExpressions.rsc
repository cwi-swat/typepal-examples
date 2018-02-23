module features::BasicExpressions

import analysis::typepal::TestFramework;
extend analysis::typepal::TypePal;

extend lang::std::Layout;

syntax Expression 
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

data AType
    = intType()
    | strType()
    ;

AType convertType((Type)`int`) = intType();
AType convertType((Type)`str`) = strType();


str BASIC_EXPRESSION_USE_ROLES = "___basicExpressionUseRoles";

void collect(current:(Expression)`<Integer _>`, TBuilder tb) {
    tb.fact(current, intType());
}

void collect(current:(Expression)`<String _>`, TBuilder tb) {
    tb.fact(current, strType());
}

void collect(current:(Expression)`<Id use>`, TBuilder tb) {
    if (set[IdRole] roles := tb.top(BASIC_EXPRESSION_USE_ROLES)) {
        tb.use(use, roles);
    }
    else {
        tb.reportError(current, "Cannot lookup relevant IdRoles");
    }
}

AType infixPlus(intType(), intType(), Tree current) = intType();

default AType infixPlus(AType lhsType, AType rhsType, Tree current) {
    reportError(current, "+ not defined between <fmt(lhsType)> and <fmt(rhsType)>");
}

void collect(current:(Expression)`<Expression lhs> + <Expression rhs>`, TBuilder tb) {
    tb.calculate("+ types", current, [lhs, rhs], AType () {
        return infixPlus(getType(lhs), getType(rhs), current);
    });
    collect(lhs, rhs, tb);
}