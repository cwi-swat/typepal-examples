module lang_features::StructWithParameters

extend analysis::typepal::TypePal;
extend lang_features::CommonLex;

import ParseTree;
import List;
import Set;

// ---- Programs with struct declarations and uses ----------------------------

start syntax Program = Declaration*;

syntax Type = "int" | "str" | Id TypeActuals;
    
syntax TypeActuals
    = noActuals: ()
    | withTypeActuals: "[" {Type ","}+ actuals "]"
    ;
    
syntax TypeHeader
    = Id TypeFormals
    ;

syntax TypeFormals
    = noTypeFormals: ()
    | withTypeFormals: "[" {TypeFormal ","}+ formals"]"
    ;
    
syntax TypeFormal
    = Id
    ;
    
syntax Declaration
    = Type typ Id id "=" Expression exp ";"
    | "struct" TypeHeader "{" {Field ","}* fields "}" ";"
    ;
    
syntax Field = Type typ Id name ;

syntax Expression 
    = Integer i
    | String s
    | Id use
    | Expression lhs "." Id fieldName
    | "new" Id name TypeActuals
    ;
    
keyword Keywords = "int" | "str" | "struct" | "new";

// ---- Extend Typepal's ATypes, IdRoles and PathRoles ------------------------

data AType
    = intType()
    | strType()
    | typeFormal(str name)
    | structDef(str name, list[str] formals)
    | structType(str name, list[AType] actuals)
    ;
    
data IdRole
    = fieldId()
    | structId()
    | typeFormalId()
    ;

str prettyPrintAType(intType()) = "int";
str prettyPrintAType(strType()) = "str";
str prettyPrintAType(typeFormal(name)) = "<name>";
str prettyPrintAType(structDef(name, formals)) = isEmpty(formals) ? "<name>" : "<name>[<intercalate(",", formals)>]";
str prettyPrintAType(structType(name, actuals)) = isEmpty(actuals) ? "<name>" : "<name>[<intercalate(",", [prettyPrintAType(a) | a <- actuals])>]";

AType instantiateTypeParametersSWP(structDef(str name, list[str] formals), structType(str name, list[AType] actuals), AType t){
    if(size(formals) != size(actuals)) throw checkFailed();
    bindings = (formals[i] : actuals [i] | int i <- index(formals));
    
    return visit(t) { case typeFormal(str x) => bindings[x] };
}

default AType instantiateTypeParametersSWP(AType def, AType ins, AType act) = act;


tuple[bool isNamedType, str typeName, set[IdRole] idRoles] getTypeNameAndRoleSWP(structType(str name, list[AType] actuals)){
    return <true, name, {structId()}>;
}

default tuple[bool isNamedType, str typeName, set[IdRole] idRoles] getTypeNameAndRoleSWP(AType t){
    return <false, "", {}>;
}

AType getTypeInNamelessTypeSWP(AType containerType, Tree selector, set[IdRole] idRolesSel, loc scope, Solver s){
    s.report(error(selector, "Undefined field %q on %t", selector, containerType));
}

TypePalConfig configSWP() =
    tconfig(getTypeNameAndRole = getTypeNameAndRoleSWP,
            getTypeInNamelessType = getTypeInNamelessTypeSWP,
            instantiateTypeParameters = instantiateTypeParametersSWP);

// ---- Collect facts and constraints -----------------------------------------

void collect(current:(Declaration)`<Type typ> <Id id> = <Expression exp> ;`, Collector c) {
    c.define("<id>", variableId(), current, defGetType(typ));
    c.require("declaration of <id>", current, [typ, exp],
        void(Solver s){ s.requireEqual(typ, exp, error(exp, "Incorrect initialization, expected %t, found %t", typ, exp)); }
       );
    c.enterScope(current);
        collect(typ, exp, c);
    c.leaveScope(current);
}

void collect(current:(Declaration) `struct <Id name> <TypeFormals formals> { <{Field ","}* fields> };`, Collector c) {
    type_formal_list = formals is noTypeFormals ? [] : [f | f <- formals.formals];
    c.define("<name>", structId(), current,  defType(structDef("<name>", [ "<tf>" | tf <- type_formal_list])));
    c.enterScope(current);
        for(tf <- type_formal_list){
            c.define("<tf>", typeFormalId(), tf, defType(typeFormal("<tf>")));
        }
        collect(formals, fields, c);
    c.leaveScope(current);
}

void collect(current:(Field)`<Type typ> <Id name>`, Collector c) {
    c.define("<name>", fieldId(), current, defGetType(typ));
    collect(typ, c);
} 

// ---- Types -----------------------------------------------------------------

void collect(current:(Type)`int`, Collector c) {
    c.fact(current, intType());
}

void collect(current:(Type)`str`, Collector c) {
    c.fact(current, strType());
}

void collect(current: (Type) `<Id name> <TypeActuals actuals>`, Collector c){
    c.use(name, {structId(), typeFormalId()});
    if(actuals is withTypeActuals){
        tpActuals = [tp | tp <- actuals.actuals];
        c.calculate("actual type", current, name + tpActuals,
            AType(Solver s) { return structType("<name>", [s.getType(tp) | tp <- tpActuals]);});
            
        collect(actuals, c);
    } else {
        c.sameType(current, name);
    }
}

void collect(current:(Expression) `new <Id name><TypeActuals actuals>`, Collector c){
    c.use(name, {structId()});
    actual_list = [a | a <- actuals.actuals];
    c.calculate("new `<name>`", current, name + actual_list,
        AType(Solver s){
            if(structDef(nm, formals) := s.getType(name)){
                formal_list = [f | f <- formals];
                if(size(actual_list) != size(formal_list)){
                    s.report(error(actuals, "Expected %v type parameters, but got %v", size(formal_list), size(actual_list)));
                }
            } else {
                s.report(error(name, "Illegal type in `new`, expected `struct` found %t", name));
            }
            return structType("<name>", [s.getType(a) | a <- actual_list]);
        });
    collect(actuals, c);
}
   
void collect(current:(Expression)`<Expression lhs> . <Id fieldName>`, Collector c) {
    c.useViaType(lhs, fieldName, {fieldId()});
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

TModel SWPTModelFromTree(Tree pt, bool debug){
    return collectAndSolve(pt, config = configSWP(), debug=debug);
}

TModel SWPTModelFromName(str mname, bool debug){
    pt = parse(#start[Program], |project://typepal-examples/src/lang_features/tests/<mname>.struct|).top;
    return SWPTModelFromTree(pt, debug);
}

bool testSWP(bool debug = false) {
    return runTests([|project://typepal-examples/src/lang_features/tests/struct_with_parameters.ttl|], #start[Program], TModel (Tree t) {
        return SWPTModelFromTree(t, debug);
    });
}