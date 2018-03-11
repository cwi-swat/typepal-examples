module features::BasicStruct

extend features::SimpleModule;


// **** Extending syntax

syntax Declaration = Struct;

syntax Struct = "struct" Id name "{" {Field ","}* fields "}";

lexical Type = Id structType;

keyword Keywords = "struct";

syntax Field = Id name ":" Type typ;

syntax Expression = Expression lhs "." Id fieldName;



//**** Type Pal 

data AType
    = structType(str name)
    ;

str prettyPrintAType(structType(name)) = "struct <name>";
    
data IdRole
    = fieldId()
    | structId()
    ;

data TypePalConfig(set[IdRole] typeRoles = {});

void collect(current:(Struct)`struct <Id name> { <{Field ","}* fields> }`, TBuilder tb) {
    tb.define("<name>", structId(), current, defType(structType("<name>")));
    tb.enterScope(current); {
        collect(fields, tb);
    } tb.leaveScope(current);
}

void collect(current:(Field)`<Id name> : <Type tp>`, TBuilder tb) {
    tb.define("<name>", fieldId(), current, defType([tp], AType() { return getType(tp); }));
    collect(tp, tb);
}

void collectType(current:(Type)`<Id _>`, TBuilder tb) {
    tb.use(current, tb.getConfig().typeRoles + {structId()});
}

//AType lookupFieldType(tp:structType(str nm), Key scope, Tree current, str fieldName) {
//    if (<_, _, _, Key structScope, _> <- getDefinitions(nm, scope, {structId()})) {
//        return getType(fieldName, structScope, {fieldId()});
//    }
//    else {
//        reportError(current, "Cannot find <fieldName> in <fmt(tp)>");
//    }
//}

//default AType lookupFieldType(AType typ, Key scope, Tree current, str fieldName) {
//    reportError(current, "<fieldName> not defined for <fmt(typ)>");
//} 

void collect(current:(Expression)`<Expression lhs> . <Id fieldName>`, TBuilder tb) {
    //currentScope = tb.getScope();
    tb.useIndirect(current, lhs, {structId()}, fieldName, {fieldId()});
    //tb.calculate("field select return type", current, [lhs], AType() {
    //    return lookupFieldType(getType(lhs), currentScope, current, "<fieldName>");
    //});
    collect(lhs, tb);
}


// *** tests

bool testStructModules(bool debug = false, PathConfig pcfg = pathConfig()) {
    return runTests([|project://typepal-examples/src/features/tests/structs.ttl|], #start[TestModules], TModel (Tree t) {
        return moduleTModelFromName(t, pcfg, debug);
    });
}