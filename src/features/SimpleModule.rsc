module features::SimpleModule

import util::Reflective;
import analysis::typepal::TestFramework;
extend analysis::typepal::TypePal;

extend features::BasicExpressions;

start syntax TestModules = Module*;

start syntax Module = "module" Id name Import* imports Declaration* decls;

syntax Import = "import" Id name ";";

// only functions are exported over modules, variables are private
syntax Declaration
    = "var" Id name "=" Expression init ";"
    | "fun" Type returnType Id name "(" {Parameter ","}* ")" "=" Expression returnExpression ";"
    ;
    
syntax Parameter = Type paramType Id paramName;

syntax Expression = Id functionName "(" {Expression ","}* params ")";

//***** Type Pal 

data AType
    = functionType(AType returnType, AType formals)
    ;

str prettyPrintAType(functionType(ret, form)) = "<prettyPrintAType(ret)>(<prettyPrintAType(form)>)";
    
data IdRole
    = variableId()
    | parameterId()
    | functionId()
    | moduleId()
    ;

data PathRole
    = importPath()
    ;

private TypePalConfig getSimpleModuleConfig() = tconfig(
    isAcceptablePath = rejectVariables,
    useRoles = {variableId(), parameterId()}
);


Accept rejectVariables(TModel tm, Key defScope, Key def, Use use, PathRole pathRole) {
    try  {
        // if there are variables by that name, skip this module
        if (_ <- getDefinitions(use.id, defScope, {variableId()})) {
            return ignoreContinue();
        }
    }
    catch: {
        ;
    }
    return acceptBinding();
}

void collect(current:(TestModules)`<Module* modules>`, TBuilder tb) {
    collect(modules, tb);
}

void collect(current:(Module)`module <Id name> <Import* imports> <Declaration* decls>`, TBuilder tb) {
    tb.define("<name>", moduleId(), current, noDefInfo());
    tb.enterScope(current); {
        collect(imports, decls, tb);
    } tb.leaveScope(current);
}

void collect(current:(Import)`import <Id name>;`, TBuilder tb) {
    tb.useViaPath(name, {moduleId()}, importPath());
}

void collect(current:(Declaration)`var <Id name> = <Expression init>;`, TBuilder tb) {
    tb.define("<name>", variableId(), current, defType([init], AType() { return getType(init); }));
    collect(init, tb);
}

default void collectType(Type tp, TBuilder tb) {
    tb.fact(tp, convertType(tp));
}

void collect(Type current, TBuilder tb) {
    collectType(current, tb);
}


void collect(current:(Declaration)`fun <Type returnType> <Id name> ( <{Parameter ","}* params> ) = <Expression returnExpression>;`, TBuilder tb) {
    argTypes = [p.paramType | p <- params];
    tb.define("<name>", functionId(), current, defType(returnType + argTypes, AType() { return functionType(getType(returnType), atypeList([getType(pt) | pt <- argTypes])); }));
    collect(returnType + argTypes, tb);

    tb.enterScope(current);
        tb.require("return type expression", returnExpression, [returnType, returnExpression], () {
            equal(getType(returnType), getType(returnExpression)) || reportError(returnExpression, "is not of defined type <fmt(returnType)> (it is of <fmt(returnExpression)> type)");
        });
        collect(params, returnExpression, tb);
    tb.leaveScope(current);
}

void collect(current:(Parameter)`<Type tp> <Id name>`, TBuilder tb) {
    tb.define("<name>", parameterId(), current, defType([tp], AType() { return getType(tp); }));
    collect(tp, tb);
}

void collect(current:(Expression)`<Id functionName> ( <{Expression ","}* params> )`, TBuilder tb) {
    tb.use(functionName, {functionId()});

    tb.calculate("function return type", current, [functionName] + [p | p <- params], AType() {
        fType = getType(functionName);
        actuals = atypeList([getType(p) | p <- params]);
        equal(fType.formals, actuals) || reportError(current, "Type of parameters are incorrect. Got <fmt(actuals)>, expected <fmt(fType.formals)>");
        return fType.returnType;
    });
    
    collect(params, tb);
}


/***********************************************
 * Test infra
 ***********************************************/
               
TModel moduleTModelFromName(Tree pt, PathConfig pcfg, bool debug){
    if(pt has top) pt = pt.top;
    tb = newTBuilder(pt, config = getSimpleModuleConfig(), debug=debug);
    collect(pt, tb);
    tm = tb.build();
    tm = resolvePath(tm);
    tm = validate(tm, debug=debug, lookupFun=lookupWide);
    return tm;
}

TModel moduleTModelFromName(str mname, PathConfig pcfg, bool debug){
    pt = parse(#start[TestModules], |project://typepal-examples/src/features/tests/<mname>.simple|).top;
    return moduleTModelFromName(pt, pcfg, debug);
}

bool testModules(bool debug = false, PathConfig pcfg = pathConfig()) {
    return runTests([|project://typepal-examples/src/features/tests/modules.ttl|], #start[TestModules], TModel (Tree t) {
        return moduleTModelFromName(t, pcfg, debug);
    });
}
