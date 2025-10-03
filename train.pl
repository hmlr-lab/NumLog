:-set_prolog_flag(stack_limit, 2_000_000_000).
:-style_check(-discontiguous).
:-[numlog].

:-  
    learn('examples/ancestor/bk.pl',
          'examples/ancestor/exs.pl',
          'examples/ancestor/bias.pl',
          gmm).
    
