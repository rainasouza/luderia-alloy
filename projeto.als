open util/integer
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
    diasDeAtraso: one Int,
    valorAluguel: one Int,
    valorMulta: one Int,
}

fact duracaoAluguel {
    all a: Aluguel | a.duracaoAluguel = 2
}

fact valoresValidos {
    all a: Aluguel | a.diasDeAtraso >= 0 and a.valorMulta >= 0
}

fact valorPorJogo {
    all a: Aluguel | (a.exemplar.jogo in jogoPequeno implies a.valorAluguel = 15) and 
    (a.exemplar.jogo in jogoMedio implies a.valorAluguel = 25) and 
    (a.exemplar.jogo in jogoGrande implies a.valorAluguel = 35)
}

fact regraMulta {
    all a: Aluguel | a.valorMulta = mul[ div[a.valorAluguel, 2], a.diasDeAtraso]
}

fact atrasadoNaoAluga {
    all c: Cliente | (some a: Aluguel | a.cliente = c and  a.diasDeAtraso > 0)
     implies
    (no b: Aluguel | b.cliente = c and b.diasDeAtraso = 0)
}

sig Reserva {
    cliente: one Cliente,
    valorReserva: one Int,
    qtdJogos: one Int,
    duracaoReserva: one Int,
    horaExcedente: one Int,
    mesa: one Mesa,
}

fact reservaDeJogos {
    all r: Reserva | r.qtdJogos <= 5
}
fact valorReserva {
    all r: Reserva | r.valorReserva = add[15, mul[r.horaExcedente, 3]]
}

fact duracaoReserva {
    all r: Reserva | r.duracaoReserva = 4 or r.duracaoReserva = 5 or r.duracaoReserva = 6
}
fact horaExcedente { 
    all r: Reserva | r.horaExcedente = r.duracaoReserva - 4
}
fact mesaUnica {
    all disj r1, r2: Reserva | (r1.mesa = r2.mesa) implies r1 = r2
}

// Se um cliente possui algum aluguel com dias de atraso maiores que zero,
// entao esse cliente nao pode ter nenhum outro aluguel com dias de atraso igual a 0.
assert clienteAtrasadoNaoAluga {
	all c: Cliente | (some a: Aluguel | a.cliente = c and a.diasDeAtraso > 0) implies (no b: Aluguel | b.cliente = c and b.diasDeAtraso = 0)
}
check clienteAtrasadoNaoAluga for 5

// Toda reserva deve conter no maximo 5 jogos.
assert limiteJogosReserva {
	all r: Reserva | r.qtdJogos <= 5
}
check limiteJogosReserva for 5

// O valor da multa deve ser um valor maior ou igual a 0.
assert multaNaoNegativa {
	all a: Aluguel | a.valorMulta >= 0
}
check multaNaoNegativa for 5

// O valor da reserva nunca ultrapassa 21 (15 reais base + (3 reais por hora adicional * 2 horas adicionais))
assert valorReservaNoMaximo21 {
	all r: Reserva | r.valorReserva <= 21
}
check valorReservaNoMaximo21

run {} for 5
