module luderia

sig Cliente {}

abstract sig Jogo{}

sig jogoPequeno extends Jogo{}
sig jogoMedio extends Jogo{}
sig jogoGrande extends Jogo{}

sig Exemplar{
    jogo: one Jogo
}

sig Mesa {}

fact {
    #Mesa = 5    
}