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

sig Aluguel {
        cliente: one Cliente,
        exemplar: one Exemplar,
        duracao: one Int,
        diasDeAtraso: one Int
    }

    fact duracaoAluguel {
        all a: Aluguel | a.duracao = 2
    }

    run {} for 5