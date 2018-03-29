module composing_features::BasicStruct

extend composing_features::SimpleModule;
extend analysis::typepal::Collector;    // tmp
extend analysis::typepal::TestFramework;    // tmp
import ParseTree;

// **** Extend syntax

syntax Declaration = Struct;

syntax Struct = "struct" Id name "{" {Field ","}* fields "}" ";";

keyword Keywords = "struct";

syntax Type = Id structType;

syntax Field = Id name ":" Type typ;

syntax Expression = Expression lhs "." Id fieldName;

// **** Extend Typepal's ATypes, IdRoles and PathRoles

data AType
    = structType(str name)
    ;

AType convertType((Type)`<Id name>`) = structType(name);
str prettyPrintAType(structType(name)) = "struct <name>";
    
data IdRole
    = fieldId()
    | structId()
    ;

// **** Configure

data TypePalConfig(set[IdRole] typeRoles = {});

// **** Collect facts and constraints

void collect(current:(Struct)`struct <Id name> { <{Field ","}* fields> };`, Collector c) {
    c.define("<name>", structId(), current, defType(structType("<name>")));
    c.enterScope(current);
        collect(fields, c);
    c.leaveScope(current);
}

void collect(current:(Field)`<Id name> : <Type tp>`, Collector c) {
    c.define("<name>", fieldId(), current, defGetType(tp));
    collect(tp, c);
}

void collectType(current:(Type)`<Id _>`, Collector c) {
    c.use(current, c.getConfig().typeRoles + {structId()});
}

AType lookupFieldType(Solver s, tp:structType(str nm), loc scope, Tree current, str fieldName) {
    if (<_, _, _, loc structScope, _> <- s.getDefinitions(nm, scope, {structId()})) {
        return s.getTypeInScope(fieldName, structScope, {fieldId()});
    }
    else {
        reportError(current, "Cannot find <fieldName> in <fmt(tp)>");
    }
}

default AType lookupFieldType(AType typ, loc scope, Tree current, str fieldName) {
    reportError(current, "<fieldName> not defined for <fmt(typ)>");
} 

void collect(current:(Expression)`<Expression lhs> . <Id fieldName>`, Collector c) {
    currentScope = c.getScope();
    c.calculate("field select return type", current, [lhs], 
        AType(Solver s) {
            return lookupFieldType(c, s.getType(lhs), currentScope, current, "<fieldName>");
        });
    collect(lhs, c);
}

//void collect(current:(Expression)`<Expression lhs> . <Id fieldName>`, Collector c) {
//    //currentScope = c.getScope();
//    c.useIndirect(current, lhs, {structId()}, fieldName, {fieldId()});
//    //c.calculate("field select return type", current, [lhs], AType() {
//    //    return lookupFieldType(getType(lhs), currentScope, current, "<fieldName>");
//    //});
//    collect(lhs, c);
//}

// **** Testing

TModel structModuleTModelFromTree(Tree pt, PathConfig pcfg, bool debug){
    return collectAndSolve(pt, config = getSimpleModuleConfig(), debug=debug);
}

TModel structModuleTModelFromName(str mname, PathConfig pcfg, bool debug){
    pt = parse(#start[TestModules], |project://typepal-examples/src/composing_features/tests/<mname>.simple|).top;
    return structModuleTModelFromName(pt, pcfg, debug);
}

bool testStructModules(bool debug = false, PathConfig pcfg = pathConfig()) {
    return runTests([|project://typepal-examples/src/composing_features/tests/structs.ttl|], #start[TestModules], TModel (Tree t) {
        return structModuleTModelFromTree(t, pcfg, debug);
    });
}

value xxx() = parse(#start[TestModules], "module A");
//value xxx() = parse(#start[TestModules], "module A struct X { f1 : int }; module B import A; fun int calc(X x1) = x1.f1 + 2;");