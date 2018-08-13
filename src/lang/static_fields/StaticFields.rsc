module lang::static_fields::StaticFields

extend analysis::typepal::TypePal;
extend analysis::typepal::TestFramework;
extend lang::CommonLex;

import ParseTree;

// ---- Programs with struct declarations and uses ----------------------------

start syntax Program = Declaration*;

syntax Type = "int" | "str" | Id typ;

syntax Declaration
    = Type typ Id id "=" Expression exp ";"
    | "struct" Id name "{" {Field ","}* fields "}" ";"
    ;
    
syntax Field = Type typ Id name ;

syntax Expression 
    = Integer i
    | String s
    | Id use
    | Expression lhs "." Id fieldName
    | "new" Id name
    ;
    
keyword Keywords = "int" | "str" | "struct" | "new";

// ---- Extend Typepal's ATypes, IdRoles and PathRoles ------------------------

data AType
    = intType()
    | strType()
    | structType(str name)
    ;
    
data IdRole
    = fieldId()
    | structId()
    ;

str prettyPrintAType(intType()) = "int";
str prettyPrintAType(strType()) = "str";
str prettyPrintAType(structType(name)) = "struct <name>";


tuple[list[str] typeNames, set[IdRole] idRoles] staticFieldsGetTypeNamesAndRole(structType(str name)){
    return <[name], {structId()}>;
}

default tuple[list[str] typeNames, set[IdRole] idRoles] staticFieldsGetTypeNamesAndRole(AType t){
    return <[], {}>;
}

AType staticFieldsGetTypeInNamelessType(AType containerType, Tree selector, loc scope, Solver s){
    if(containerType == strType() && "<selector>" == "length") return intType();
    s.report(error(selector, "Undefined field %q on %t", selector, containerType));
}

TypePalConfig staticFieldsConfig() =
    tconfig(getTypeNamesAndRole = staticFieldsGetTypeNamesAndRole,
            getTypeInNamelessType = staticFieldsGetTypeInNamelessType);


// ---- Collect facts and constraints -----------------------------------------

void collect(current:(Declaration)`<Type typ> <Id id> = <Expression exp> ;`, Collector c) {
    c.define("<id>", variableId(), current, defType(typ));
    c.requireEqual(typ, exp, error(exp, "Incorrect initialization, expected %t, found %t", typ, exp));
    c.enterScope(current);
        collect(typ, exp, c);
    c.leaveScope(current);
}

void collect(current:(Declaration)`struct <Id name> { <{Field ","}* fields> };`, Collector c) {
    c.define("<name>", structId(), current, defType(structType("<name>"))); 
    c.enterScope(current);
        collect(fields, c);
    c.leaveScope(current);
}

void collect(current:(Field)`<Type typ> <Id name>`, Collector c) {
    c.define("<name>", fieldId(), current, defType(typ));
    collect(typ, c);
}

void collect(current:(Type)`int`, Collector c) {
    c.fact(current, intType());
}

void collect(current:(Type)`str`, Collector c) {
    c.fact(current, strType());
}

void collect(current:(Type)`<Id name>`, Collector c) {
    c.use(current, {structId()});
}

void collect(current:(Expression) `new <Id name>`, Collector c){
    c.use(name, {structId()});
    c.fact(current, structType("<name>"));
}
   
void collect(current:(Expression)`<Expression lhs> . <Id fieldName>`, Collector c) {
    c.useViaType(lhs, fieldName, {fieldId()});
    c.fact(current, fieldName);
    collect(lhs, c);
}

void collect(current:(Expression)`<Integer _>`, Collector c) {
    c.fact(current, intType());
}

void collect(current:(Expression)`<String _>`, Collector c) {
    c.fact(current, strType());
}

void collect(current:(Expression)`<Id use>`, Collector c) {
    c.use(use, {variableId()});
}

// ---- Testing ---------------------------------------------------------------

TModel staticFieldsTModelFromTree(Tree pt, bool debug){
    return collectAndSolve(pt, config=staticFieldsConfig(), debug=debug);
}

TModel staticFieldsTModelFromName(str mname, bool debug){
    pt = parse(#start[Program], |project://typepal-examples/src/lang/static_fields/<mname>.struct|).top;
    return staticFieldsTModelFromTree(pt, debug);
}

bool staticFieldsTests(bool debug = false) {
    return runTests([|project://typepal-examples/src/lang/static_fields/static_fields.ttl|], #start[Program], TModel (Tree t) {
        return staticFieldsTModelFromTree(t, debug);
    });
}

value main() { staticFieldsTests(); return true; }