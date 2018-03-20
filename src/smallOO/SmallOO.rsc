module smallOO::SmallOO
 
import analysis::typepal::TestFramework;
extend analysis::typepal::TypePal;
extend analysis::typepal::ExtractTModel; 
import util::Reflective;
import ParseTree;

// ---- SmallOO syntax --------------------------------------------------------

extend lang::std::Layout;

start syntax Module = "module" Identifier moduleName Import* imports Declaration* declarations; 

syntax Import = "import" Identifier moduleName;

syntax Declaration 
    = "class" Identifier className "{" Declaration* declarations "}"
    | Type returnType Identifier functionName "(" {Parameter ","}* parameters ")" "=" Expression returnExpression ";"
    | Type fieldType Identifier fieldName ";"
    ;

syntax Parameter = Type tp Identifier name; 

syntax Expression
    = Identifier id
    | Expression "." Identifier id
    | Literal l
    | Identifier functionName "(" {Expression ","}* parameters ")"
    | Expression "." Identifier functionName "(" {Expression ","}* parameters ")"
    | Expression "+" Expression
    ;
    
lexical Identifier = ([a-z A-Z _][a-z A-Z _ 0-9]* !>> [a-z A-Z _ 0-9]) \ Keywords;
    
lexical Literal
    = Integer
    | String
    ;
    
lexical Integer = [0-9]+ !>> [0-9];
lexical String = [\"] ![\"]* [\"];
    
lexical Type
    = "int"
    | "str"
    | Identifier className
    ;

keyword Keywords = "module" | "class" | "import" | "int" | "str";
 
// ---- Extend Typepal's ATypes, IdRoles and PathRoles -----------------------
 
data AType
    = intType()
    | strType()
    | classType(str nm)
    | functionType(AType returnType, AType formals)
    ;
    
data IdRole
    = fieldId()
    | parameterId()
    | functionId()
    | classId()
    ;

AType convertType((Type) `int`) = intType();
AType convertType((Type) `str`) = strType();
AType convertType((Type) `<Identifier className>`) = classType("<className>");

str prettyPrintAType(intType()) = "int";
str prettyPrintAType(strType()) = "str";
str prettyPrintAType(classType(str name)) = name;

// ---- collect ---------------------------------------------------------------

void collect(current:(Module)`module <Identifier _> <Import* _> <Declaration* decls>`, Collector c) {
    collect(decls, c);
}

void collect(current:(Declaration)`class <Identifier className> { <Declaration* decls> }`, Collector c) {
    c.defineNamedType("<className>", classId(), current, defType(classType("<className>")));
    c.enterScope(current);
        collect(decls, c);
    c.leaveScope(current);
}

void collect(current:(Declaration)`<Type returnType> <Identifier functionName> ( <{Parameter ","}* params> ) = <Expression returnExpression> ;`, Collector c) {
    classScope = c.getScope(); 
    c.enterScope(current); {
        retType = convertType(returnType);
        c.defineInScope(classScope, "<functionName>", functionId(), functionName, 
            defType([p.name | p <- params], AType(Solver s) { return functionType(retType, atypeList([s.getType(p.name) | p <- params])); }));
     
        c.require("return expression", returnExpression, [returnExpression],
            void (Solver s) {
                s.equal(retType, returnExpression, error(returnExpression, "Return expression is not the same type as the return type (%t) instead of (%t)", returnExpression, retType));
        });
        collect(returnType, params, returnExpression, c);
    }
    c.leaveScope(current);
}

void collect(current:(Declaration)`<Type fieldType> <Identifier fieldName>;`, Collector c) {
    ft = convertType(fieldType);
    c.define("<fieldName>", fieldId(), fieldName, defType(ft));
    collect(fieldType, c);
}

void collect(current:(Parameter)`<Type paramType> <Identifier paramName>`, Collector c) {
    c.define("<paramName>", parameterId(), paramName, defType(convertType(paramType)));
    collect(paramType, c);
}

void collect(current:(Expression)`<Identifier id>`, Collector c) {
    c.use(id, {fieldId(), parameterId(), functionId()});
}

void collect(current:(Type)`<Type typ>`, Collector c) {
    if(classType(_) := convertType(typ)){
        c.use(typ, {classId()});
    }
}

void collect(current:(Expression)`<Integer _>`, Collector c) {
    c.fact(current, intType());
}

void collect(current:(Expression)`<String _>`, Collector c) {
    c.fact(current, strType());
}

void collect(current:(Expression)`<Identifier functionName> ( <{Expression ","}* params> )`, Collector c) {
    collectFunctionCall(functionName, params, c);
}

void collect(current:(Expression)`<Expression lhs> . <Identifier id>`, Collector c) {
    //c.useSourceType(lhs, id, {fieldId()});
    c.calculate("field `<id>`", current, [lhs],
        AType(Solver s) { return s.getTypeInSourceType(lhs, id, {fieldId()}); });
    collect(lhs, c);           
}

void collect(current:(Expression)`<Expression lhs> . <Identifier functionName> ( <{Expression ","}* params> )`, Collector c) {
    c.calculate("method `<functionName>`", current, lhs + [p | p <- params],
       AType(Solver s) { 
            funType = s.getTypeInSourceType(lhs, functionName, {functionId()});
            parType = atypeList([s.getType(e) | e <- params]);
            return computeCallType(functionName, funType, parType, s);
         }); 
    collect(lhs, functionName, params, c);  
}

void collectFunctionCall(Identifier functionName, {Expression ","}* params, Collector c) {
    c.calculate("call function `<functionName>`", functionName, [functionName] + [ e | e <- params], 
        AType(Solver s) {
            funType = s.getType(functionName);
            parType = atypeList([s.getType(e) | e <- params]);
            return computeCallType(functionName, funType, parType, s);
        });
    collect(params, c);
}

AType computeCallType(Identifier functionName, AType funType, AType parTypes, Solver s){
    switch (funType) {
        case overloadedAType({*_,<_,_, functionType(AType ret, parTypes)>}) : return ret;
        case functionType(AType ret, parTypes): return ret;
        default: s.report(error(functionName, "No function can be found that accepts these parameters: %t", parTypes));
    }
}

void collect(current:(Expression)`<Expression lhs> + <Expression rhs>`, Collector c) {
    c.calculate("expression",current, [lhs, rhs],
        AType(Solver s) {
            switch([s.getType(lhs), s.getType(rhs)]){
                case [intType(), intType()]: return intType();
                case[strType(), strType()]: return strType();
                default:
                     s.report(error(current, "+ is not defined on %t and %t", lhs, rhs));
            }
    });
    collect(lhs, rhs, c);
}

// ---- Testing ---------------------------------------------------------------
               
TModel smallOOTModelFromTree(Tree pt, bool debug){
    return collectAndSolve(pt, debug=debug);
}

TModel smallOOTModelFromName(str mname, bool debug){
    pt = parse(#start[Module], |project://typepal-examples/src/smallOO/<mname>.small|).top;
    return smallOOTModelFromTree(pt, debug);
}

list[Message] checkSmallOO(str mname, bool debug=false) {
    return smallOOTModelFromName(mname, debug).messages;
}

bool testSmallOO(bool debug = false) {
    return runTests([|project://typepal-examples/src/smallOO/modules.ttl|], #start[Module], TModel (Tree t) {
        return smallOOTModelFromTree(t, debug);
    });
}