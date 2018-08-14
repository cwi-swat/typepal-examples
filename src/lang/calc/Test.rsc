module lang::calc::Test

extend lang::calc::Checker;
extend analysis::typepal::TestFramework;    // TypePal test utilities
import ParseTree;                           // In order to parse tests

// ---- Testing ---------------------------------------------------------------

TModel calcTModelFromTree(Tree pt){
    return collectAndSolve(pt);
}

TModel calcTModelFromStr(str text){
    pt = parse(#start[Calc], text).top;
    return calcTModelFromTree(pt);
}

bool calcTests() {
     return runTests([|project://typepal-examples/src/lang/calc/tests.ttl|], #Calc, calcTModelFromTree);
}

bool main() = calcTests();