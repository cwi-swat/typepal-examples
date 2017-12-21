module smallOO::Checker

import analysis::typepal::TestFramework;
extend analysis::typepal::TypePal;
import util::Reflective;

import smallOO::Syntax;

data AType
    = intType()
    | strType()
    | classType(str nm)
    | functionType(AType returnType, AType formals)
    ;
    
data IdRole
    = fieldId()
    | parameterId()
    | functionId()
    | classId()
    ;


void collect(current:(Module)`module <Identifier _> <Import* _> <Declaration* decls>`, TBuilder tb) {
    collect(decls, tb);
}

void collect(current:(Declaration)`class <Identifier className> { <Declaration* decls> }`, TBuilder tb) {
    tb.define("<className>", classId(), className, defType(classType("<className>")));
    tb.enterScope(current); {
        collect(decls, tb);
    }
    tb.leaveScope(current);
}


void collect(current:(Declaration)`<Type returnType> <Identifier functionName> ( <{Parameter ","}* params> ) = <Expression returnExpression> ;`, TBuilder tb) {
    fStub = tb.newTypeVar();
    tb.define("<functionName>", functionId(), functionName, defType([returnType] + [p.name | p <- params], AType() { return getType(fStub); }));
    tb.enterScope(current); {
        tb.require("function type", functionName, [returnType] + [p.name | p <- params], () {
            retType = getType(returnType);
            formals = atypeList([getType(p.name) | p <- params]);
            unify(fStub, functionType(retType, formals)) || reportError(current, "Could not calculcate function type");
        });
        tb.require("function return expression", returnExpression, [returnExpression, returnType], () {
            equal(getType(returnType), getType(returnExpression)) || reportError(returnExpression, "Return expression is not the same type as the return type (<fmt(returnExpression)> instead of (<fmt(returnType)>)");
        });
        collect(returnType, params, returnExpression, tb);
    }
    tb.leaveScope(current);
}

void collect(current:(Declaration)`<Type fieldType> <Identifier fieldName>;`, TBuilder tb) {
    tb.define("<fieldName>", fieldId(), fieldName, defType([fieldType], AType() { return getType(fieldType); }));
    collect(fieldType, tb);
}

void collect(current:(Parameter)`<Type paramType> <Identifier paramName>`, TBuilder tb) {
    tb.define("<paramName>", parameterId(), paramName, defType([paramType], AType() { return getType(paramType); }));
    collect(paramType, tb);
}

void collect(current:(Expression)`<Identifier id>`, TBuilder tb) {
    tb.use(id, {fieldId(), parameterId()});
}

void collect(current:(Expression)`<Expression lhs> . <Identifier id>`, TBuilder tb) {
    throw "How to handle these scoped use?";
}

void collect(current:(Expression)`<Integer _>`, TBuilder tb) {
    tb.fact(current, intType());
}

void collect(current:(Expression)`<String _>`, TBuilder tb) {
    tb.fact(current, strType());
}


void collect(current:(Expression)`<Identifier functionName> ( <{Expression ","}* params> )`, TBuilder tb) {
    tb.use(functionName, {functionId()});
    collectFunctionCall(functionId, params, tb);
}

void collect(current:(Expression)`<Expression lhs> . <Identifier functionName> ( <{Expression ","}* params> )`, TBuilder tb) {
    throw "How to handle these scoped use?";
    tb.use(functionName, {functionId()});
    collectFunctionCall(functionId, params, tb);
}

void collectFunctionCall(Identifier functionName, {Expression ","}* params, TBuilder tb) {
    tb.calculate("return type", current, [functionName] + [ e | e <- params], AType() {
        paramTypes = atypeList([getType(e) | e <- params]);
        switch (getType(functionName)) {
            case overloadedAType({*_,<_,_, functionType(AType ret, paramTypes)>}) : return ret;
            case functionType(AType ret, paramTypes): return ret;
            default: reportError(current, "No function can be find that accepts these parameters (<fmt(paramTypes)>)");
        }
    });
    collect(params, tb);
}


AType infixPlus(intType(), intType(), _) = intType();

AType infixPlus(strType(), strType(), _) = strType();

default AType infixPlus(AType lhs, AType rhs, Tree context) {
    reportError(context, "+ is not defined for <fmt(lhs)> and <fmt(rhs)>");
}


void collect(current:(Expression)`<Expression lhs> + <Expression rhs>`, TBuilder tb) {
    tb.calculate("expression type",current, [lhs, rhs], AType() {
        return infixPlus(getType(lhs), getType(rhs), current);
    });
    collect(lhs, rhs, tb);
}

void collect(current:(Type)`int`, TBuilder tb) {
    tb.fact(current, intType()); 
}

void collect(current:(Type)`str`, TBuilder tb) {
    tb.fact(current, strType()); 
}
void collect(current:(Type)`<Identifier className>`, TBuilder tb) {
    tb.use(current, {classId()});
}


/***********************************************
 * Test infra
 ***********************************************/
 
TModel commonTModelFromTree(Tree pt, PathConfig pcfg, bool debug){
    if(pt has top) pt = pt.top;
    tb = newTBuilder(pt, debug=debug);
    collect(pt, tb);
    tm = tb.build();
    tm = validate(tm, debug=debug);
    return tm;
}

bool testClasses(bool debug = false, PathConfig pcfg = pathConfig()) {
    return runTests([|project://typepal-examples/src/smallOO/classes.ttl|], #Declaration, TModel (Tree t) {
        return commonTModelFromTree(t, pcfg, debug);
    });
}