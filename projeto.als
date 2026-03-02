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
    duracaoAluguel: one Int,
    diasDeAtraso: one Int
}

fact duracaoAluguel {
    all a: Aluguel | a.duracaoAluguel = 2
}


sig Reserva {
    cliente: one Cliente,
    valor: one Int,
    qtdJogos: one Int,
    duracaoReserva: one Int,
}

fact {
    all r: Reserva | r.qtdJogos <= 5
    #duracaoReserva = 4
}

run {} for 5