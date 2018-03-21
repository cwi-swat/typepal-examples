module composing_features::SimpleModule

import util::Reflective;
import analysis::typepal::TestFramework;
extend analysis::typepal::TypePal;
extend analysis::typepal::Collector;
import ParseTree;

extend composing_features::BasicExpressions;

// **** Extend syntax

start syntax TestModules = Module*;

start syntax Module = "module" Id name Import* imports Declaration* decls;

syntax Import = "import" Id name ";";

// all functions are publicly visible to other modules, variables are private
syntax Declaration
    = "var" Id name "=" Expression init ";"
    | "fun" Type returnType Id name "(" {Parameter ","}* ")" "=" Expression returnExpression ";"
    ;
    
syntax Parameter = Type paramType Id paramName;

syntax Expression = Id functionName "(" {Expression ","}* params ")";

keyword Keywords
    = "module" | "import" | "var" | "fun"
    ;

// **** Extend Typepal's ATypes, IdRoles and PathRoles

data AType
    = functionType(AType returnType, AType formals)
    ;

AType convertType((Type)`int`) = intType();
AType convertType((Type)`str`) = strType();

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

// **** Configure

private TypePalConfig getSimpleModuleConfig() = tconfig(
    isAcceptablePath = rejectVariables,
    useRoles = {variableId(), parameterId()}
);

Accept rejectVariables(TModel tm, loc defScope, loc def, Use use, PathRole pathRole) {
    // Variables are not visible outside a module
    return variableId() in use.idRoles ? ignoreContinue() : acceptBinding();
}

// **** Collect facts and constraints

void collect(current:(TestModules)`<Module* modules>`, Collector c) {
    collect(modules, c);
}

void collect(current:(Module)`module <Id name> <Import* imports> <Declaration* decls>`, Collector c) {
    c.define("<name>", moduleId(), current, noDefInfo());
    c.enterScope(current);
        collect(imports, decls, c);
    c.leaveScope(current);
}

void collect(current:(Import)`import <Id name>;`, Collector c) {
    c.useViaPath(name, {moduleId()}, importPath());
}

void collect(current:(Declaration)`var <Id name> = <Expression init>;`, Collector c) {
    c.define("<name>", variableId(), current, defGetType(init));
    collect(init, c);
}

default void collectType(Type tp, Collector c) {
    c.fact(tp, convertType(tp));
}

void collect(Type current, Collector c) {
    collectType(current, c);
}

void collect(current:(Declaration)`fun <Type returnType> <Id name> ( <{Parameter ","}* params> ) = <Expression returnExpression>;`, Collector c) {
    argTypes = [p.paramType | p <- params];
    c.define("<name>", functionId(), current, defType(returnType + argTypes, AType(Solver s) { return functionType(s.getType(returnType), atypeList([s.getType(pt) | pt <- argTypes])); }));
    collect(returnType + argTypes, c);

    c.enterScope(current);
        c.require("return type expression", returnExpression, [returnType, returnExpression], 
            void (Solver s) {
                s.requireEqual(returnType, returnExpression) || s.reportError(returnExpression, "is not of defined type <s.fmt(returnType)> (it is of <fmt(returnExpression)> type)");
        });
        collect(params, returnExpression, c);
    c.leaveScope(current);
}

void collect(current:(Parameter)`<Type tp> <Id name>`, Collector c) {
    c.define("<name>", parameterId(), current, defGetType(tp));
    collect(tp, c);
}

void collect(current:(Expression)`<Id functionName> ( <{Expression ","}* params> )`, Collector c) {
    c.use(functionName, {functionId()});

    c.calculate("function return type", current, [functionName] + [p | p <- params], 
        AType(Solver s) {
            fType = s.getType(functionName);
            actuals = atypeList([s.getType(p) | p <- params]);
            s.requireEqual(fType.formals, actuals) || s.reportError(current, "Type of parameters are incorrect. Got <s.fmt(actuals)>, expected <s.fmt(fType.formals)>");
            return fType.returnType;
        });
    
    collect(params, c);
}

// **** Testing
               
TModel moduleTModelFromTree(Tree pt, PathConfig pcfg, bool debug){
    return collectAndSolve(pt, config = getSimpleModuleConfig(), debug=debug);
}

TModel moduleTModelFromName(str mname, PathConfig pcfg, bool debug){
    pt = parse(#start[TestModules], |project://typepal-examples/src/composing_features/tests/<mname>.simple|).top;
    return moduleTModelFromName(pt, pcfg, debug);
}

bool testModules(bool debug = false, PathConfig pcfg = pathConfig()) {
    return runTests([|project://typepal-examples/src/composing_features/tests/modules.ttl|], #start[TestModules], TModel (Tree t) {
        return moduleTModelFromTree(t, pcfg, debug);
    });
}

value yyy() = parse(#start[TestModules], "module A module B import A; fun int calc(int x1) = x1 + 2;");