module smallOO::Checker
 
import analysis::typepal::TestFramework;
extend analysis::typepal::TypePal;
import util::Reflective;
import ParseTree;

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

AType convertType((Type) `int`) = intType();
AType convertType((Type) `str`) = strType();
AType convertType((Type) `<Identifier className>`) = classType("<className>");

// ---- collect ---------------------------------------------------------------

void collect(current:(Module)`module <Identifier _> <Import* _> <Declaration* decls>`, TBuilder tb) {
    collect(decls, tb);
}

void collect(current:(Declaration)`class <Identifier className> { <Declaration* decls> }`, TBuilder tb) {
    tb.define("<className>", classId(), current, defType(classType("<className>")));
    tb.enterScope(current); {
        collect(decls, tb);
    }
    tb.leaveScope(current);
}

void collect(current:(Declaration)`<Type returnType> <Identifier functionName> ( <{Parameter ","}* params> ) = <Expression returnExpression> ;`, TBuilder tb) {
    classScope = tb.getScope(); 
    tb.enterScope(current); {
        retType = convertType(returnType);
        tb.defineInScope(classScope, "<functionName>", functionId(), functionName, defType([p.name | p <- params], 
           AType() {
                     formals = atypeList([getType(p.name) | p <- params]);
                     return functionType(retType, formals); 
                    }));
     
        tb.require("function return expression", returnExpression, [returnExpression], () {
            equal(retType, getType(returnExpression)) || reportError(returnExpression, "Return expression is not the same type as the return type (<fmt(returnExpression)> instead of (<fmt(retType)>)");
        });
        collect(params, returnExpression, tb);
    }
    tb.leaveScope(current);
}

void collect(current:(Declaration)`<Type fieldType> <Identifier fieldName>;`, TBuilder tb) {
    tb.define("<fieldName>", fieldId(), fieldName, defType(convertType(fieldType)));
}

void collect(current:(Parameter)`<Type paramType> <Identifier paramName>`, TBuilder tb) {
    tb.define("<paramName>", parameterId(), paramName, defType(convertType(paramType)));
}

void collect(current:(Expression)`<Identifier id>`, TBuilder tb) {
    tb.use(id, {fieldId(), parameterId()});  // <=== Hier functionId() toevoegen? Dan zijn de aparte uses in function calls niet meer nodig.
}

void collect(current:(Expression)`<Expression lhs> . <Identifier id>`, TBuilder tb) {
    //throw "How to handle these scoped use?";
    scope = tb.getScope();
    tb.calculate("field selection", current, [lhs],
       AType() { tp = getType(lhs);
                 if(classType(str nm) := tp) {
                    for(<Key outerScope, str className, classId(), Key classScope, DefInfo defInfo> <- getDefinitions(nm, scope, {classId()})){
                        return getType("<id>", classScope, {fieldId()});
                    }
                    reportError(lhs, "No class type found for <fmt("<lhs>")>");
                 } else {
                    reportError(lhs, "class type expected, found <fmt(tp)>");
                 }
                 }); 
    collect(lhs, tb);           
}

void collect(current:(Expression)`<Integer _>`, TBuilder tb) {
    tb.fact(current, intType());
}

void collect(current:(Expression)`<String _>`, TBuilder tb) {
    tb.fact(current, strType());
}


void collect(current:(Expression)`<Identifier functionName> ( <{Expression ","}* params> )`, TBuilder tb) {
    tb.use(functionName, {functionId()});  // <==
    collectFunctionCall(functionName, params, tb);
}

void collect(current:(Expression)`<Expression lhs> . <Identifier functionName> ( <{Expression ","}* params> )`, TBuilder tb) {

    scope = tb.getScope();
    the_params = [p | p <- params];     // hack as long as concrete lists do not work properly.
    tb.calculate("method call", current, lhs + the_params,
       AType() { tp = getType(lhs);
                 if(classType(str nm) := tp) {
                    for(<Key outerScope, str className, classId(), Key classScope, DefInfo defInfo> <- getDefinitions(nm, scope, {classId()})){
                        paramTypes = atypeList([getType(e) | e <- params]);
                        funType = getType("<functionName>", classScope, {functionId()});
                        switch (funType) {
                            case overloadedAType({*_,<_,_, functionType(AType ret, paramTypes)>}) : return ret;
                            case functionType(AType ret, paramTypes): return ret;
                            default: reportError(current, "No function can be found that accepts these parameters (<fmt(paramTypes)>)");
                        }
                    }
                    reportError(lhs, "No class type found for <fmt("<lhs>")>");
                 } else {
                    reportError(lhs, "class type expected, found <fmt(tp)>");
                 }
                 }); 
    collect(lhs,  params, tb);  
    
    tb.use(functionName, {functionId()});  // <==
}

void collectFunctionCall(Identifier functionName, {Expression ","}* params, TBuilder tb) {
    tb.calculate("return type", functionName, [functionName] + [ e | e <- params], AType() {
        paramTypes = atypeList([getType(e) | e <- params]);
        switch (getType(functionName)) {
            case overloadedAType({*_,<_,_, functionType(AType ret, paramTypes)>}) : return ret;
            case functionType(AType ret, paramTypes): return ret;
            default: reportError(functionName, "No function can be find that accepts these parameters (<fmt(paramTypes)>)");
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

/***********************************************
 * Test infra
 ***********************************************/

public PathConfig getDefaultPathConfig() = pathConfig(   
        srcs = [|project://typepal-examples/src|
               ]);
               
TModel commonTModelFromTree(Tree pt, PathConfig pcfg, bool debug){
    if(pt has top) pt = pt.top;
    tb = newTBuilder(pt, debug=debug);
    collect(pt, tb);
    tm = tb.build();
    tm = validate(tm, debug=debug);
    return tm;
}

TModel commonTModelFromName(str mname, PathConfig pcfg, bool debug){
    pt = parse(#start[Module], |project://typepal-examples/src/smallOO/<mname>.small|).top;
    return commonTModelFromTree(pt, pcfg,debug);
}

list[Message] validateModule(str mname, bool debug=false) {
    return commonTModelFromName(mname, getDefaultPathConfig(), debug).messages;
}

bool testClasses(bool debug = false, PathConfig pcfg = pathConfig()) {
    return runTests([|project://typepal-examples/src/smallOO/classes.ttl|], #Declaration, TModel (Tree t) {
        return commonTModelFromTree(t, pcfg, debug);
    });
}

bool testModules(bool debug = false, PathConfig pcfg = pathConfig()) {
    return runTests([|project://typepal-examples/src/smallOO/modules.ttl|], #start[Module], TModel (Tree t) {
        return commonTModelFromTree(t, pcfg, debug);
    });
}