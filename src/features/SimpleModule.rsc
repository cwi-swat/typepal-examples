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
    
data IdRole
    = variableId()
    | parameterId()
    | functionId()
    | moduleId()
    ;

data PathRole
    = importPath()
    ;


Accept isAcceptablePath(TModel tm, Key defScope, Key def, Use use, PathRole pathRole) {
    println("<def> <use>");
    try 
        // if there are variables by that name, skip this module
        if (_ <- getDefinitions(use.id, defScope, {variableId()})) {
            return ignoreContinue();
        }
    catch:
        ;
    return acceptBinding();
}

void collect(current:(TestModules)`<Module* modules>`, TBuilder tb) {
    collect(modules, tb);
}

void collect(current:(Module)`module <Id name> <Import* imports> <Declaration* decls>`, TBuilder tb) {
    tb.push(BASIC_EXPRESSION_USE_ROLES, {variableId(), parameterId()});
    tb.define("<name>", moduleId(), current, noDefInfo());
    tb.enterScope(current); {
        collect(imports, decls, tb);
    } tb.leaveScope(current);
    tb.pop(BASIC_EXPRESSION_USE_ROLES);
}

void collect(current:(Import)`import <Id name>;`, TBuilder tb) {
    tb.useViaPath(name, {moduleId()}, importPath());
}

void collect(current:(Declaration)`var <Id name> = <Expression init>;`, TBuilder tb) {
    tb.define("<name>", variableId(), current, defType([init], AType() { return getType(init); }));
    collect(init, tb);
}

void collect(current:(Declaration)`fun <Type returnType> <Id name> ( <{Parameter ","}* params> ) = <Expression returnExpression>;`, TBuilder tb) {
    retType = convertType(returnType);
    argType = atypeList([convertType(p.paramType) | p <- params]);
    tb.define("<name>", functionId(), current, defType(functionType(retType, argType)));

    tb.enterScope(current);
        tb.require("return type expression", returnExpression, [returnExpression], () {
            equal(retType, getType(returnExpression)) || reportError(returnExpression, "is not of defined type <fmt(retType)>");
        });
        collect(params, returnExpression, tb);
    tb.leaveScope(current);
}

void collect(current:(Parameter)`<Type tp> <Id name>`, TBuilder tb) {
    tb.define("<name>", parameterId(), current, defType(convertType(tp)));
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
               
TModel commonTModelFromTree(Tree pt, PathConfig pcfg, bool debug){
    if(pt has top) pt = pt.top;
    tb = newTBuilder(pt, debug=debug);
    collect(pt, tb);
    tm = tb.build();
    tm = resolvePath(tm);
    tm = validate(tm, debug=debug, lookupFun=lookupWide);
    return tm;
}

TModel commonTModelFromName(str mname, PathConfig pcfg, bool debug){
    pt = parse(#start[TestModules], |project://typepal-examples/src/features/<mname>.simple|).top;
    return commonTModelFromTree(pt, pcfg, debug);
}

bool testModules(bool debug = false, PathConfig pcfg = pathConfig()) {
    return runTests([|project://typepal-examples/src/features/modules.ttl|], #start[TestModules], TModel (Tree t) {
        return commonTModelFromTree(t, pcfg, debug);
    });
}
