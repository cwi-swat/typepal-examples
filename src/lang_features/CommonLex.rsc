module lang_features::CommonLex

extend lang::std::Layout;

lexical Id = ([a-z A-Z][a-z A-Z 0-9]* !>> [a-z A-Z 0-9]) \ Keywords;

lexical Integer = [0-9]+ !>> [0-9];

lexical String = [\"] ![\"]* [\"];

keyword Keywords =;