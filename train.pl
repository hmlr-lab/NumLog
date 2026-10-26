:-set_prolog_flag(stack_limit, 2_000_000_000).
:-style_check(-discontiguous).
:-[numlog].


:-  
    learn('ECG data/bk.pl',%background knowledge
          'ECG data/train_1_numlog_3D_HA_physionet_13_II_2026.pl',%examples
          'ECG data/bias.pl',%mode declaration
          gmm).% v1 =range, v2 =gmm
    
