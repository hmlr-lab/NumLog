:-set_prolog_flag(stack_limit, 2_000_000_000).
:-style_check(-discontiguous).


learn(BK,Exs,Bias,range) :-
    use_module('Libs/numlogV1'),
    learnFromFile(BK,Exs,Bias).

learn(BK,Exs,Bias,gmm) :-
    use_module('Libs/numlogV2'),
    learnFromFile(BK,Exs,Bias).