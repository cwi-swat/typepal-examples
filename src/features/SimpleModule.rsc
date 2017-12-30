module features::SimpleModule

import util::Reflective;
import analysis::typepal::TestFramework;
extend analysis::typepal::TypePal;

extend lang::std::Layout;

start syntax TestModules = Module*;
start syntax Module = "module" Id name Import* imports Declaration* decls;

syntax Import = "import" Id name ";";

// only functions are exported over modules, variables are private
syntax Declaration
    = "var" Id name "=" Expression init ";"
    | "fun" Type returnType Id name "(" {Parameter ","}* ")" "=" Expression returnExpression ";"
    ;
    
syntax Parameter = Type paramType Id paramName;

syntax Expression 
    = Integer i
    | String s
    | Id use
    | Expression lhs "+" Expression rhs
    | Id functionName "(" {Expression ","}* params ")"
    ;
    
lexical Type = "int" | "str";

keyword Keywords = "int" | "str";

lexical Id = ([a-z A-Z][a-z A-Z 0-9]* !>> [a-z A-Z 0-9]) \ Keywords;

lexical Integer = [0-9]+ !>> [0-9];

lexical String = [\"] ![\"]* [\"];


//***** Type Pal 

data AType
    = intType()
    | strType()
    | functionType(AType returnType, AType formals)
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

AType convertType((Type)`int`) = intType();
AType convertType((Type)`str`) = strType();

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


void collect(current:(Expression)`<Integer _>`, TBuilder tb) {
    tb.fact(current, intType());
}

void collect(current:(Expression)`<String _>`, TBuilder tb) {
    tb.fact(current, strType());
}

void collect(current:(Expression)`<Id use>`, TBuilder tb) {
    tb.use(use, {parameterId(), variableId()});
}

void collect(current:(Expression)`<Expression lhs> + <Expression rhs>`, TBuilder tb) {
    tb.fact(current, intType());
    tb.require("only plus on integers", current, [lhs, rhs], () {
        equal(intType(), getType(lhs)) || reportError(lhs, "not of an integer type");
        equal(intType(), getType(rhs)) || reportError(rhs, "not of an integer type");
    });
    collect(lhs, rhs, tb);
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
    tm = validate(tm, debug=debug);
    return tm;
}

bool testModules(bool debug = false, PathConfig pcfg = pathConfig()) {
    return runTests([|project://typepal-examples/src/features/modules.ttl|], #start[TestModules], TModel (Tree t) {
        return commonTModelFromTree(t, pcfg, debug);
    });
}
