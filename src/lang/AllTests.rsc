module lang::AllTests

import lang::aliases::Test;
import lang::calc::Test;
import lang::extending::Test;
import lang::fixedMembers::Test;
import lang::fun::Test;
import lang::fwjava::Test;
import lang::modfun::Test;
import lang::pascal::Test;
import lang::pico::Test;
import lang::ql::Test;
import lang::smallOO::Test;
import lang::staticFields::Test;
import lang::struct::Test;
import lang::structParameters::Test;
import lang::untypedFun::Test;

bool allTests(){
    return  
           aliasesTests()
        && calcTests()
        && extendingTests()
        
        && fixedMembersTests()
        && funTests()
        && fwjTests()
        && modfunTests()
        && pascalTests()
        && picoTests()
        && qlTests()
        && smallOOTests()
        && staticFieldsTests()
        && structTests()
        && structParametersTests()
        && untypedFunTests()
        ;
}

test bool allTests1() = allTests();

bool main() = allTests();