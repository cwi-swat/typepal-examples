module lang::aliases::Aliases

extend analysis::typepal::TypePal;
extend analysis::typepal::TestFramework;

import ParseTree;
import IO;

extend lang::CommonLex;

// ---- Programs with struct declarations and aliases -------------------------

start syntax Program = Declaration*;

syntax Type = "int" | "str" | Id typ;

syntax Declaration
    = Type typ Id id "=" Expression exp ";"
    | "struct" Id name "{" {Field ","}* fields "}" ";"
    | "alias" Id name "=" Type typ ";"
    ;
    
syntax Field = Type typ Id name ;

syntax Expression 
    = Integer i
    | String s
    | Id use
    | Expression lhs "." Id fieldName
    | "new" Id name
    ;
    
keyword Keywords = "alias" | "int" | "str" | "struct" | "new";

// ---- Extend Typepal's ATypes, IdRoles and PathRoles ------------------------

data AType
    = intType()
    | strType()
    | structType(str name)
    ;
    
data IdRole
    = fieldId()
    | structId()
    | aliasId()
    ;
 
str prettyPrintAType(intType()) = "int";
str prettyPrintAType(strType()) = "str";
str prettyPrintAType(structType(name)) = "struct <name>";

tuple[list[str] typeNames, set[IdRole] idRoles] aliasesGetTypeNamesAndRole(structType(str name)){
    return <[name], {structId()}>;
}

default tuple[list[str] typeNames, set[IdRole] idRoles] aliasesGetTypeNamesAndRole(AType t){
    return <[], {}>;
}

TypePalConfig aliasesConfig() =
    tconfig(getTypeNamesAndRole = aliasesGetTypeNamesAndRole);

 
// ---- Collect facts and constraints -----------------------------------------

void collect(current: (Program) `<Declaration* decls>`, Collector c){
    c.enterScope(current);
        collect(decls, c);
    c.leaveScope(current);
}

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

void collect(current:(Declaration)`alias <Id name> = <Type typ>;`, Collector c) {
    c.define("<name>", aliasId(), current, defType(typ));
    c.enterScope(current);; 
        collect(typ, c);
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
    c.use(current, {structId(), aliasId()});
}

void collect(current:(Expression) `new <Id name>`, Collector c){
    c.use(name, {structId(), aliasId()});
    c.fact(current, name);
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

TModel aliasesTModelFromTree(Tree pt, bool debug = false){
    return collectAndSolve(pt, config = aliasesConfig(), debug=debug);
}

TModel aliasesTModelFromName(str mname, bool debug = false){
    pt = parse(#start[Program], |project://typepal-examples/src/aliases/<mname>.alias|).top;
    return aliasesTModelFromTree(pt, debug=debug);
}

bool aliasesTests(bool debug = false) {
    return runTests([|project://typepal-examples/src/lang/aliases/aliases.ttl|], #start[Program], TModel (Tree t) {
        return aliasesTModelFromTree(t, debug=debug);
    });
}

value main() { aliasesTests(); return true; }