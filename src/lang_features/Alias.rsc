module lang_features::Alias

extend analysis::typepal::TypePal;

import ParseTree;
import IO;

extend lang_features::CommonLex;

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
    //| userType(str name, loc scope)
    ;
    
data IdRole
    = fieldId()
    | structId()
    | aliasId()
    ;
 
str prettyPrintAType(intType()) = "int";
str prettyPrintAType(strType()) = "str";
str prettyPrintAType(structType(name)) = "struct <name>";
 
// ---- Collect facts and constraints -----------------------------------------

void collect(current: (Program) `<Declaration* decls>`, Collector c){
    c.enterScope(current);
        collect(decls, c);
    c.leaveScope(current);
}

void collect(current:(Declaration)`<Type typ> <Id id> = <Expression exp> ;`, Collector c) {
    c.define("<id>", variableId(), current, defGetType(typ));
    c.require("declaration of `<id>`", current, [typ, exp],
        void(Solver s){ s.requireEqual(typ, exp, error(exp, "Incorrect initialization, expected %t, found %t", typ, exp)); }
       );
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
    c.define("<name>", aliasId(), current, defGetType(typ));
    c.enterScope(current);; 
        collect(typ, c);
    c.leaveScope(current);
}

void collect(current:(Field)`<Type typ> <Id name>`, Collector c) {
    c.define("<name>", fieldId(), current, defGetType(typ));
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
    c.sameType(current, name);
}

void collect(current:(Expression)`<Expression lhs> . <Id fieldName>`, Collector c) {
    c.useViaNamedType(lhs, {structId()}, fieldName, {fieldId()});
    c.sameType(current, fieldName);
        
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

TModel aliasTModelFromTree(Tree pt, bool debug = false){
    return collectAndSolve(pt, debug=debug);
}

TModel aliasTModelFromName(str mname, bool debug = false){
    pt = parse(#start[Program], |project://typepal-examples/src/lang_features/tests/<mname>.alias|).top;
    return aliasTModelFromTree(pt, debug=debug);
}

bool testAlias(bool debug = false) {
    return runTests([|project://typepal-examples/src/lang_features/tests/struct.ttl|,
                     |project://typepal-examples/src/lang_features/tests/alias.ttl|], #start[Program], TModel (Tree t) {
        return aliasTModelFromTree(t, debug=debug);
    });
}