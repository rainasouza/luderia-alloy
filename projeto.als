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
    horaExcedente: one Int,
    mesa: one Mesa,
}

fact reservaDeJogos{
    all r: Reserva | r.qtdJogos <= 5
}
fact valorReserva{
    all r: Reserva | r.valor = 15
}

fact duracaoReserva {
    all r: Reserva | r.duracaoReserva = 4 or r.duracaoReserva = 5 or r.duracaoReserva = 6
}
fact horaExcedente{ 
    all r: Reserva | r.horaExcedente = r.duracaoReserva - 4
}
fact mesaUnica{
    all disj r1, r2: Reserva | (r1.mesa = r2.mesa) implies r1 = r2
}
run {} for 5