module pascal::Checker

import pascal::Pascal;
import ParseTree;

extend ExtractFRModel;
extend Constraints;
extend TestFramework;


// ----  IdRoles, PathLabels and AType ------------------- 

data IdRole
    = fileId()
    | constantId()
    | typeId()
    | fieldId()
    | variableId()
    | formalId()
    | labelId()
    | functionId()
    | procedureId()
    ;

data AType
    = scalarType(list[str] elems)
    | subrangeType(AType associatedType)
    | arrayType(AType indexType, AType elemType)
    | setType(AType elemType)
    | fileType(AType elemType)
    | pointerType(AType elemType)
    | functionType(AType argTypes, AType resType)
    | procedureType(AType argTypes)
    | recordType(list[tuple[str, AType]] fixedPart)
    | definedType(str tname, Use use)
    | primitiveType(str tname)
    ;

AType constantType(Tree scope, Tree cname){
    return useType(use("<cname>", cname@\loc, scope@\loc, {constantId()}));
}

AType definedType(Tree scope, Tree tname){
    return definedType("<tname>", use("<tname>", tname@\loc, scope@\loc, {typeId()}));
}

AType useDefinedType(Tree scope, Tree tname){
    return useType(use("<tname>", tname@\loc, scope@\loc, {typeId()}));
}

str AType2String(scalarType(list[str] elems)) = "(<intercalate(", ", elems)>)";
str AType2String(subrangeType(AType associatedType)) = "subrange of <AType2String(associatedType)>";
str AType2String(arrayType(AType indexType, AType elemType)) = 
    "array <AType2String(indexType)> of <AType2String(elemType)>";
str AType2String(setType(AType elemType)) = 
    "set of <AType2String(elemType)>";
str AType2String(fileType(AType elemType)) =   
    "file of <AType2String(elemType)>";
str AType2String(pointerType(AType elemType)) = "^" + AType2String(elemType);
str AType2String(procedureType(AType argTypes)) = "procedure (<AType2String(argTypes)>)";
str AType2String(functionType(AType argTypes, AType resType)) = "function (<AType2String(argTypes)>) : <AType2String(resType)>";
str AType2String(definedType(str tname, Use use)) = tname;
str AType2String(primitiveType(str tname)) = tname;


AType getType(Tree scope, Type t){
   if(t is simple)
      return getSimpleType(scope, t.simpleType);
   if(t is structured)
      return getStructuredType(scope, t.structuredType);
    return pointerType(useDefinedType(scope, t.typeIdentifier));
}  

AType getSimpleType(Tree scope, SimpleType t){
    if(t is scalar)
       return scalarType(["<id>" | id <- t.scalarType.ids]);
    if(t is subrange)
        return subrangeType(getConstantType(scope, t.subrangeType.from));
    switch("<t.typeIdentifier>"){
    case "Boolean": return booleanType;
    case "integer": return integerType;
    case "real": return realType;
    case "string": return stringType;
    default:
        return  definedType(scope, t.typeIdentifier);
    }  
}

AType getStructuredType(Tree scope, StructuredType t){
    return getUnpackedStructuredType(scope, t.unpackedStructuredType, t is packed);
}

AType getUnpackedStructuredType(Tree scope, UnpackedStructuredType t, bool packed){
    if(t is array)
       return arrayType(listType([ getSimpleType(scope, idx) | idx <- t.arrayType.indexTypes ]), getType(scope, t.arrayType.rtype));
    if(t is record){
        fixedPart = [];
        for(rs <- t.recordType.fieldList.fixedPart.recordSections){
            for(fid <- rs.fieldIdentifiers){
                fixedPart  += <"<fid>", getType(scope, rs.rtype)>;
            }
        }
        return recordType(fixedPart);
    }
    if(t is \set)
        return setType(getSimpleType(scope, t.setType.simpleType));
    if(t is file)
        return fileType(getType(scope, t.fileType.\type));
}

AType getUnsignedConstantType(Tree scope, UnsignedConstant c){
    if(c is unumber)
        return c.unsignedNumber is integer ? integerType : realType;
    if(c is string)
        return stringType;
    return pointerType(anyPointerType);
}

AType getConstantType(Tree scope, Constant c){
    if(c is unumber || c is signedNumber)
        return c.unsignedNumber is integer ? integerType : realType;
    if(c is constantid || c is signedconstant)
        return constantType(scope, c);
    return stringType;
}

// ---- isSubtype

bool isSubtype(listType(list[AType] elems1), listType(list[AType] elems2), ScopeGraph sg)
    = size(elems1) == size(elems2) && all(int i <- index(elems1), isSubtype(elems1[i], elems2[i], sg));

bool isSubtype(primitiveType(str tname1), primitiveType(str tname2), ScopeGraph sg)
    = tname1 == "integer" && tname2 == "real" || tname1 == tname2;

bool isSubtype(t1: definedType(tname1, use1), AType t2, ScopeGraph sg){
    println("isSubtype: <t1>, <t2>");
    if(t1 == t2)
        return true;
    try { 
            def1 = lookup(sg, use1);
            println("sg.facts[def1]: <sg.facts[def1]>");
            return isSubtype(sg.facts[def1], t2, sg);
    } catch noKey: {
            return false;
    }
}
bool isSubtype(AType t1, t2: definedType(tname2, use2), ScopeGraph sg){  
    if(t1 == t2)
        return true;  
    try { 
            def2 = lookup(sg, use2);
            return isSubtype(t1, sg.facts[def2], sg);
    } catch noKey: {
           return false;
    }
}

bool isSubtype(subrangeType(AType associatedType), AType other, ScopeGraph sg)
    = isSubtype(associatedType, other, sg);
     
bool isSubtype(AType other, subrangeType(AType associatedType), ScopeGraph sg)
    = isSubtype(other, associatedType, sg);

bool isSubtype(pointerType(AType t1), pointerType(AType t2), ScopeGraph sg)
    = t1 == anyPointerType || isSubtype(t1, t2, sg);
    
bool isSubtype(AType atype, functionType(_, atype), ScopeGraph sg) = true;  // for assignment to function id

default bool isSubtype(AType atype1, AType atype2, ScopeGraph sg) = atype1 == atype2;

// ---- getLUB

AType getLUB(t1: definedType(tname1,use1), t2: definedType(tname2,use2), ScopeGraph sg){
    if(tname1 == "integer" && tname2 == "real"){
       return t2;
    } else if(tname1 == "real" && tname2 == "integer"){
       return t1;
    } else if(tname1 == tname2){
        return t1;
    } else {
       try {
        def1 = lookup(sg, use1);
        def2 = lookup(sg, use2);
        return isSubtype(sg.facts[def2], sg.facts[def2], sg);
       } catch noKey: {
            throw "NoLUB";
       }
    }
    throw "NoLUB";
}

default AType getLUB(AType atype, ScopeGraph sg){
    if(listType(atypes) := atype){
        if(all(int i <- [0 .. size(atypes)-1], atypes[i] == atypes[i+1]))
            return atypes[0];
    }
    throw "NoLUB";
}
 
// ----  Initialize --------------------------------------  

AType booleanType;
AType integerType;
AType realType;
AType stringType;
AType textType;
AType anyPointerType;
AType charType;

Tree mkTree(int n) = [Identifier] "<for(int i <- [0 .. n]){>x<}>"; // A unique tree

FRBuilder initializedFRB(Tree tree){
    booleanType = primitiveType("Boolean");
    integerType = primitiveType("integer");
    realType = primitiveType("real");
    stringType = primitiveType("string");
    textType = primitiveType("text");
    anyPointerType = primitiveType("anyPointer");
    charType = primitiveType("char");
    FRBuilder frb = makeFRBuilder();
    frb.define(tree, "true",    constantId(),   mkTree(10), defInfo(booleanType));
    frb.define(tree, "false",   constantId(),   mkTree(11), defInfo(booleanType));
    //frb.define(tree, "writeln", procedureId(),  mkTree(12), defInfo(procedureType(listType([]))));
    //frb.define(tree, "write",   procedureId(),  mkTree(13), defInfo(procedureType(listType([]))));
    //frb.define(tree, "odd",     functionId(),   mkTree(14), defInfo(functionType(listType([integerType]), booleanType)));
    //frb.define(tree, "abs",     functionId(),   mkTree(15), defInfo(functionType(listType([integerType]), integerType)));
    //frb.define(tree, "sqr",     functionId(),   mkTree(16), defInfo(functionType(listType([integerType]), integerType)));
    //frb.define(tree, "sin",     functionId(),   mkTree(17), defInfo(functionType(listType([realType]), realType)));
    //frb.define(tree, "cos",     functionId(),   mkTree(18), defInfo(functionType(listType([realType]), realType)));
    //frb.define(tree, "arctan",  functionId(),   mkTree(19), defInfo(functionType(listType([realType]), realType)));
    //frb.define(tree, "exp",     functionId(),   mkTree(20), defInfo(functionType(listType([realType]), realType)));
    //frb.define(tree, "ln",      functionId(),   mkTree(21), defInfo(functionType(listType([realType]), realType)));
    //frb.define(tree, "sqrt",    functionId(),   mkTree(22), defInfo(functionType(listType([realType]), realType)));
    //frb.define(tree, "round",   functionId(),   mkTree(23), defInfo(functionType(listType([realType]), integerType)));
    //frb.define(tree, "read",    procedureId(),  mkTree(24), defInfo(procedureType(listType([]))));
    //frb.define(tree, "new",     procedureId(),  mkTree(24), defInfo(procedureType(listType([]))));
    //
    frb.define(tree, "Boolean", typeId(),       mkTree(25), defInfo(booleanType));
    frb.define(tree, "integer", typeId(),       mkTree(26), defInfo(integerType));
    //frb.define(tree, "real",    typeId(),       mkTree(27), defInfo(realType));
    //frb.define(tree, "string",  typeId(),       mkTree(28), defInfo(stringType));
    //frb.define(tree, "text",    typeId(),       mkTree(29), defInfo(textType));
    //frb.define(tree, "any",     typeId(),       mkTree(30), defInfo(anyPointerType));
    //frb.define(tree, "char",    typeId(),       mkTree(31), defInfo(charType));
  
    return frb;
}

// ====  Begin of type checking rules ===================

// ----  Define -----------------------------------------

Tree define(ProgramHeading ph, Tree scope, FRBuilder frb) {
    for(fid <- ph.fileIdentifiers){
        frb.define(scope, "<fid>", fileId(), fid, defInfo(fileType(textType)));
    }
    return scope;
}

Tree define(TypeDefinition td, Tree scope, FRBuilder frb){
    if(td.rtype is simple){
       frb.define(scope, "<td.id>", typeId(), td.id, defInfo(getType(scope, td.rtype)));
       return scope;
    } else if(td.rtype is structured){
        frb.define(scope, "<td.id>", typeId(), td.id, defInfo(definedType(td, td.id)));
        return td;
    } else {
       frb.define(scope, "<td.id>", typeId(), td.id, defInfo(getType(scope, td.rtype)));
       return scope;
    }
}

Tree define(RecordSection rs, Tree scope, FRBuilder frb){
    for(fid <- rs.fieldIdentifiers){
        frb.define(scope, "<fid>", fieldId(), fid, defInfo(getType(scope, rs.rtype)));
    }
    return scope;
}

AType handleFormals({FormalParameterSection ";"}+ formals, Tree scope, FRBuilder frb){
    formalTypes = [];
    for(fps <- formals){
        g = fps.group;
        for(fid <- fps.group.ids){
            t = getType(scope, g.rtype);
            formalTypes += t;
            frb.define(scope, "<fid>", formalId(), fid, defInfo(t)); 
        }
    }
    return listType(formalTypes);
}

Tree define(FunctionDeclaration fd, Tree scope, FRBuilder frb){
    hd = fd.functionHeading;
    if(hd has formals){
      frb.define(scope, "<hd.id>", functionId(), hd.id, defInfo(functionType(handleFormals(hd.formals, scope, frb), useDefinedType(scope, hd.rtype))));
    } else {
       frb.define(scope, "<hd.id>", functionId(), hd.id, defInfo(functionType(listType([]), useDefinedType(scope, hd.rtype)))); 
    }
    return fd;
}

Tree define(ProcedureDeclaration pd, Tree scope, FRBuilder frb){
    hd = pd.procedureHeading;
    if(hd has formals){
       frb.define(scope, "<hd.id>", procedureId(), hd.id, defInfo(procedureType(handleFormals(hd.formals, scope, frb)))); 
    } else {
       frb.define(scope, "<hd.id>", procedureId(), hd.id, defInfo(procedureType(listType([])))); 
    }
    return pd;
}

Tree define(LabelDeclarationPart ldp, Tree scope, FRBuilder frb) {
    for(lab <- ldp.labels){
        frb.define(scope, "<lab>", labelId(), lab, noDefInfo());
    }
    return scope;
}

Tree define(Block b, Tree scope, FRBuilder frb) {
    return b;
}

Tree define(ConstantDefinition cd, Tree scope, FRBuilder frb) {
   frb.define(scope, "<cd.id>", constantId(), cd.id, defInfo(getConstantType(scope, cd.constant)));
    return scope;
}

Tree define(TypeDefinition td, Tree scope, FRBuilder frb) {
    frb.define(scope, "<td.id>", typeId(), td.id, defInfo(getType(scope, td.rtype)));
    return scope;
}

Tree define(VariableDeclaration vd, Tree scope, FRBuilder frb) {
    for(id <- vd.ids){
        frb.define(scope, "<id>", variableId(), id, defInfo(getType(scope, vd.\type)));
    }
    return scope;
}

Tree define(s: (Statement) `<Label label>: <UnlabelledStatement us>`, Tree scope, FRBuilder frb) {
    frb.define(scope, "<label>", labelId(), label, noDefInfo());
    return s;
}

// ---- Collect uses and requirements -----------------------------------

void collect(GoToStatement s, Tree scope, FRBuilder frb){
     frb.use(scope, s.label, {labelId()}, 0);
}

void collect(e: (EntireVariable) `<EntireVariable var>`, Tree scope, FRBuilder frb){
     frb.use(scope, var, {formalId(), variableId(), constantId()}, 0);
}

void collect(e: (ReferencedVariable) `<Variable var>^`, Tree scope, FRBuilder frb){
     //frb.use(scope, var, {formalId(), variableId(), constantId()}, 0);
     frb.require("referenced variable <e>", e, [var],
         () { println("typeof <var>: <typeof(var)>");
              if(pointerType(tau1) := typeof(var)){ 
                fact(e, tau1);
              } else {
                reportError(var, "Pointer type required", [var]);
              }
            });
}

void collect((TypeIdentifier) `<TypeIdentifier tvar>`, Tree scope, FRBuilder frb){
     frb.use(scope, tvar, {typeId()}, 0);
}

void collect(fd: (FieldDesignator) `<RecordVariable var> . <FieldIdentifier field>`, Tree scope, FRBuilder frb){
    if(var is entire)
        frb.use(scope, var, {formalId(), variableId(), constantId()}, 0);
     frb.fact(fd, [var], AType() { return typeof(var, field, {fieldId()}); });
}

void collect(e: (IndexedVariable) `<ArrayVariable var> [ <{Expression ","}+ indices> ]`, Tree scope, FRBuilder frb){
     frb.use(scope, var, {formalId(), variableId(), constantId()}, 0);
     Tree tvar = var;
     frb.require("indexed variable", e, [tvar] + [exp | Tree exp <- indices],
         (){ if(arrayType(tau1, tau2) := typeof(var)){
                subtype(listType([typeof(exp) | exp <- indices]), tau1, onError(e, "Index mismatch"));
                fact(e, tau2);
              } else {
                reportError(e, "Array type required", [var]);
              }
           });
}

void collect(f: (Expression) `<UnsignedConstant cons>`, Tree scope, FRBuilder frb){
     frb.atomicFact(cons, getUnsignedConstantType(scope, cons));
}

void collect(fd: (FunctionDesignator)  `<FunctionIdentifier fid> ( <{ ActualParameter ","}+  actuals> )`, Tree scope, FRBuilder frb){
     frb.use(scope, fid, {functionId()}, 0);
     actualList = [exp | Tree exp <- actuals];
     AType iirr() { switch(typeof(actualList[0])){
                        case integerType: return integerType;
                        case realType: return realType;
                        default:
                            reportError(fd, "Illegal call", actualList);
                      }
                    };
     AType irrr() { switch(typeof(actualList[0])){
                        case integerType: return realType;
                        case realType: return realType;
                        default:
                            reportError(fd, "Illegal call", actualList);
                      }
                    };
     switch("<fid>"){
     
     case "abs": 
        frb.overload("call `abs`", fd, actualList, iirr);  
     case "arctan": 
        frb.overload("call `arctan`", fd, actualList, iirr);
     case "cos": 
        frb.overload("call `cos`", fd, actualList, irrr);
     case "exp": 
        frb.overload("call `exp`", fd, actualList, iirr);
     case "ln": 
        frb.overload("call `ln`", fd, actualList, iirr);
     case "sin": 
        frb.overload("call `sin`", fd, actualList, irrr);
     case "sqr": 
        frb.overload("call `sqr`", fd, actualList, iirr);
     case "sqrt": 
        frb.overload("call `sqrt`", fd, actualList, iirr);
 
     default: {
        Tree tfid = fid;
        frb.require("function designator", fd, [tfid] + [exp | Tree exp <- actuals],
            () { if(functionType(tau1, tau2) := typeof(fid)){ 
                    subtype(listType([typeof(exp) | exp <- actuals]), tau1, onError(fd, "Parameter mismatch"));
                    fact(fd, tau2);
                  } else {
                    reportError(fd, "Function type required", [fid]);
                  }
               });
        }
      }
}

void collect(s: (ProcedureStatement)  `<ProcedureIdentifier fid>`, Tree scope, FRBuilder frb){
     frb.use(scope, fid, {procedureId(), functionId()}, 0);
}

void collect(s: (ProcedureStatement) `<ProcedureIdentifier id> ( <{ActualParameter ","}+ actuals> )`, Tree scope, FRBuilder frb){
     frb.use(scope, id, {procedureId(), functionId()}, 0);
     actualList = [exp | exp <- actuals];
         
     switch("<id>"){
     case "new":
        if(size(actualList) != 1){
            frb.error(s, "One argument required");
        }
     case "read":;
     case "write":;
     case "writeln":;
     
     default: {
        Tree tid = id;
        frb.require("procedure statement", s, [tid] + [exp | Tree exp <- actuals],
            () { if(procedureType(tau1) := typeof(id)){ 
                    subtype(listType([typeof(exp) | exp <- actuals]), tau1, onError(s, "Parameter mismatch"));
                  } else {
                    reportError(s, "Procedure type required", [id]);
                  }
               });
         }
     }
}

void collect(e: (Expression) `( <Expression exp> )`, Tree scope, FRBuilder frb){
    frb.fact(e, [exp], AType() { return typeof(exp); } );
}

void collect(s: (AssignmentStatement) `<Variable var> := <Expression exp>`, Tree scope, FRBuilder frb){
//   frb.use(scope, var, {formalId(), variableId(), functionId()}, 0);
    Tree tvar = var; Tree texp = exp;
    frb.require("assignment", s, [tvar, texp],
        () { subtype(typeof(exp), typeof(var), onError(s, "Incorrect assignment"));
           });
}

void collect(IfStatement s, Tree scope, FRBuilder frb){
    frb.require("condition", s.condition, [s.condition],
        () { equal(typeof(s.condition), booleanType, onError(s.condition, "Incorrect condition"));
           });
}

void collect(WhileStatement s, Tree scope, FRBuilder frb){
    frb.require("condition", s.condition, [s.condition],
        () { equal(typeof(s.condition), booleanType, onError(s.condition, "Incorrect condition"));
           });
} 

void collect(RepeatStatement s, Tree scope, FRBuilder frb){
    frb.require("condition", s.condition, [s.condition],
        () { equal(typeof(s.condition), booleanType, onError(s.condition, "Incorrect condition"));
           });
}

void collect(ForStatement s, Tree scope, FRBuilder frb){
    frb.require("for statement", s, [s.forList.initial, s.forList.final],
        () { subtype(typeof(s.forList.initial), integerType, onError(s.forList.initial, "Initial value should be integer"));
             subtype(typeof(s.forList.final), integerType, onError(s.forList.final, "Final value should be integer"));
             fact(s.control, integerType);
           });
}

// Case statement

//void collect(e: (Set) `{ <{Element ","}* elements> }`, Tree scope, FRBuilder frb){
//     elemTypes = listType([typeof(exp) | exp <- elements]);
//     frb.require("set", e, [exp | exp <- elements],
//            () { lub(tau1, elemTypes, onError(e, "Incompatible elements in set"));
//                 fact(e, setType(tau1));
//               });
//}

// Operator overloading

void overloadRelational(Expression e, str op, Expression exp1, Expression exp2, Tree scope, FRBuilder frb){
    frb.overload("relational operator `<op>`", e,  [exp1, exp2], 
        AType() { switch([typeof(exp1), typeof(exp2)]){
                  case [booleanType, booleanType]: return booleanType;
                  case [integerType, integerType]: return booleanType;
                  case [integerType, realType]: return booleanType;
                  case [realType, integerType]: return booleanType;
                  case [realType, realType]: return booleanType;
                  case [scalarType(tau1), scalarType(tau2)]: booleanType;
                  case [subrangeType(integerType), realType]: return realType;
                  case [realType, subrangeType(integerType)]: return realType;
                  case [subrangeType(tau1), tau1]: return tau1;
                  case [subrangeType(tau1), subrangeType(tau1)]: return tau1;
                  case [tau1, setType(tau1)]: return booleanType;
                  case [setType(tau1), setType(tau1)]: return booleanType;
                  default: {
                     if(op == "\<\>"){
                        switch([typeof(exp1), typeof(exp2)]){
                            case [pointerType(tau1), pointerType(tau1)]: return booleanType;
                            case [pointerType(anyPointerType), pointerType(tau1)]: return booleanType;
                            case [pointerType(tau1), pointerType(anyPointerType)]: return booleanType;
                        }
                     }
                     reportError(e, "No version of `<op>` is applicable", [exp1, exp2]); 
                   }
                }
              });
}

void collect(e: (Expression) `<Expression exp1> = <Expression exp2>`, Tree scope, FRBuilder frb)
    = overloadRelational(e, "=", exp1, exp2, scope, frb);

void collect(e: (Expression) `<Expression exp1> \<\> <Expression exp2>`, Tree scope, FRBuilder frb)
    = overloadRelational(e, "\<\>", exp1, exp2, scope, frb);

void collect(e: (Expression) `<Expression exp1> \< <Expression exp2>`, Tree scope, FRBuilder frb)
    = overloadRelational(e, "\<", exp1, exp2, scope, frb);
    
void collect(e: (Expression) `<Expression exp1> \<= <Expression exp2>`, Tree scope, FRBuilder frb)
    = overloadRelational(e, "\<=", exp1, exp2, scope, frb); 
    
void collect(e: (Expression) `<Expression exp1> \>= <Expression exp2>`, Tree scope, FRBuilder frb)
    = overloadRelational(e, "\>=", exp1, exp2, scope, frb); 
     
void collect(e: (Expression) `<Expression exp1> \> <Expression exp2>`, Tree scope, FRBuilder frb)
    = overloadRelational(e, "\>", exp1, exp2, scope, frb);           

void collect(e: (Expression) `<Expression exp1> in <Expression exp2>`, Tree scope, FRBuilder frb){
    frb.overload("relational operator", e, [exp1, exp2], 
        AType () { switch([typeof(exp1), typeof(exp2)]){
                       case [tau1, setType(tau1)]: return booleanType;
                       case [tau1, setType(tau1)]: return booleanType;
                       default:
                            reportError(e, "No version of `in` is applicable", [exp1, exp2]);  
                   }
                 });
}

void collect(e: (Expression) `<Expression exp1> * <Expression exp2>`, Tree scope, FRBuilder frb){
    frb.overload("multiplication", e, [exp1, exp2], 
        AType() { switch([typeof(exp1), typeof(exp2)]){
                      case [integerType, integerType]: return integerType;
                      case [integerType, realType]: return realType;
                      case [realType, integerType]: return realType;
                      case [realType, realType]: return realType;
                      case [subrangeType(integerType), realType]: return realType;
                      case [realType, subrangeType(integerType)]: realType;
                      case [subrangeType(tau1), tau1]: return tau1;
                      case [subrangeType(tau1), subrangeType(tau1)]: return tau1;
                      case [setType(tau1), setType(tau1)]: return setType(tau1);
                      default:
                           reportError(e, "No version of `*` is applicable", [exp1, exp2]);
                   }
                 }); 
}

void collect(e: (Expression) `<Expression exp1> / <Expression exp2>`, Tree scope, FRBuilder frb){
    frb.overload("division", e, [exp1, exp2], 
        AType () { switch([typeof(exp1), typeof(exp2)]){
                       case [integerType, integerType]: return realType;
                       case [integerType, realType]: return realType;
                       case [realType, integerType]: realType;
                       case [realType, realType]: return realType;
                       default:
                            reportError(e, "No version of `/` is applicable", [exp1, exp2]);
                     }
                   });
}

void collect(e: (Expression) `<Expression exp1> div <Expression exp2>`, Tree scope, FRBuilder frb){
    frb.overload("div", e, [exp1, exp2],
        AType () { switch([typeof(exp1), typeof(exp2)]){
                       case [integerType, integerType]: return integerType;
                       default:
                            reportError(e, "No version of `div` is applicable", [exp1, exp2]);
                   }
                 });  
}

void collect(e: (Expression) `<Expression exp1> mod <Expression exp2>`, Tree scope, FRBuilder frb){
    frb.overload("mod", e, [exp1, exp2], 
        AType () { switch([typeof(exp1), typeof(exp2)]){
                       case [integerType, integerType]: return realType;
                       default:
                            reportError(e, "No version of `mod` is applicable", [exp1, exp2]);
                     }
                   });  
}

void collect(e: (Expression) `<Expression exp1> and <Expression exp2>`, Tree scope, FRBuilder frb){
    frb.overload("and", e, [exp1, exp2], 
        AType () { switch([typeof(exp1), typeof(exp2)]){
                       case [booleanType, booleanType]: return booleanType;
                       default:
                            reportError(e, "No version of `and` is applicable", [exp1, exp2]);
                   }
                 });  
}

void collect(e: (Expression) `not <Expression exp>`, Tree scope, FRBuilder frb){
    frb.overload("not", e, [exp], 
        AType () { switch(typeof(exp)){
                       case booleanType: return booleanType;
                       default:
                            reportError(e, "No version of `not` is applicable", [exp]);
                   }
                 });  
}

void overloadAdding(Expression e, str op, Expression exp1, Expression exp2, Tree scope, FRBuilder frb){
 frb.overload("adding operator", e, [exp1, exp2], 
     AType() { switch([typeof(exp1), typeof(exp2)]){
                   case [integerType, integerType]: return integerType;
                   case [integerType, realType]: return realType;
                   case [realType, integerType]: return realType;
                   case [realType, realType]: return realType;
                   case [tau1, subrangeType(tau1)]:  tau1;
                   case [subrangeType(tau1), tau1]: tau1;
                   case [subrangeType(tau1), subrangeType(tau1)]: tau1;
                   case [setType(tau1), setType(tau1)]: return setType(tau1);
                   default:
                        reportError(e, "No version of `<op>` is applicable", [exp1, exp2]);  
               }
             });
}

void collect(e: (Expression) `<Expression exp1> + <Expression exp2>`, Tree scope, FRBuilder frb)
    = overloadAdding(e, "+", exp1, exp2, scope, frb);

void collect(e: (Expression) `<Expression exp1> - <Expression exp2>`, Tree scope, FRBuilder frb)
    = overloadAdding(e, "-", exp1, exp2, scope, frb);

void collect(e: (Expression) `<Expression exp1> or <Expression exp2>`, Tree scope, FRBuilder frb){
    frb.overload("and", e, [exp1, exp2], 
        AType() { switch([typeof(exp1), typeof(exp2)]){
                      case [booleanType, booleanType]: return booleanType;
                      default:      
                            reportError(e, "No version of `and` is applicable", [exp1, exp2]);
                  }
                });  
}

// ----  Examples & Tests --------------------------------

private Block sampleBlock(str name) = parse(#Block, |project://TypePal/src/pascal/<name>.pascal|);
private Program sampleProgram(str name) = parse(#Program, |project://TypePal/src/pascal/<name>.pascal|);
 
set[Message] validatePascalBlock(str name) {
    b = sampleBlock(name);
    return validate(extractScopesAndConstraints(b, initializedFRB(b)) , isSubtype=isSubtype, getLUB=getLUB);
}

set[Message] validatePascalProgram(str name) {
    p = sampleProgram(name);
    return validate(extractScopesAndConstraints(p, initializedFRB(p)), isSubtype=isSubtype, getLUB=getLUB);
}

void testPascalBlock() {
    runTests(|project://TypePal/src/pascal/blocktests.ttl|, #Block, initialFRBuilder=initializedFRB,isSubtype=isSubtype, getLUB=getLUB);
}