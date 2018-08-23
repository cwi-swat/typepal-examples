module lang::untypedFun::Test

extend lang::untypedFun::Checker;
extend analysis::typepal::TestFramework;

// ----  Examples & Tests --------------------------------

private Expression sample(str name) = parse(#start[Expression], |project://typepal-examples/src/lang/untypedFun/<name>.ufun|).top;

list[Message] untypedFunCheck(str name, bool debug = false){
    Tree pt =  parse(#start[Expression], |project://typepal-examples/src/lang/untypedFun/<name>.ufun|).top;
    return untypedFunTModelFromTree(sample(name), debug=debug).messages;
}

TModel untypedFunTModelFromTree(Tree pt, bool debug=false)
    = collectAndSolve(pt, debug=debug);

bool untypedFunTests()
    = runTests([|project://typepal-examples/src/lang/untypedFun/tests.ttl|], #Expression, untypedFunTModelFromTree);

value main() = untypedFunTests();
