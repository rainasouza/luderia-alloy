open util/integer
module luderia

// Clientes da luderia
sig Cliente {}

// Jogo abstrato, especializado em tres tamanhos
abstract sig Jogo{}

sig jogoPequeno extends Jogo{}
sig jogoMedio extends Jogo{}
sig jogoGrande extends Jogo{}

// Exemplar fisico de um jogo
sig Exemplar{
    jogo: one Jogo
}

// Mesas disponiveis para reserva
sig Mesa {}

// A luderia possui exatamente 5 mesas
fact {
    #Mesa = 5    
}

// Representa o aluguel de um exemplar por um cliente
sig Aluguel {
    cliente: one Cliente,
    exemplar: one Exemplar,
    duracaoAluguel: one Int,
    diasDeAtraso: one Int,
    valorAluguel: one Int,
    valorMulta: one Int,
}

// Todo aluguel tem duracao fixa de 2 dias
fact duracaoAluguel {
    all a: Aluguel | a.duracaoAluguel = 2
}

// Dias de atraso e multa nao podem ser negativos
fact valoresValidos {
    all a: Aluguel | a.diasDeAtraso >= 0 and a.valorMulta >= 0
}

// Valor do aluguel depende do tipo do jogo: 15, 25 ou 35 reais
fact valorPorJogo {
    all a: Aluguel | (a.exemplar.jogo in jogoPequeno implies a.valorAluguel = 15) and 
    (a.exemplar.jogo in jogoMedio implies a.valorAluguel = 25) and 
    (a.exemplar.jogo in jogoGrande implies a.valorAluguel = 35)
}

// Multa = metade do valor do aluguel multiplicado pelos dias de atraso
fact regraMulta {
    all a: Aluguel | a.valorMulta = mul[ div[a.valorAluguel, 2], a.diasDeAtraso]
}

// Cliente com devolucao atrasada nao pode ter novo aluguel ativo
fact atrasadoNaoAluga {
    all c: Cliente | (some a: Aluguel | a.cliente = c and  a.diasDeAtraso > 0)
     implies
    (no b: Aluguel | b.cliente = c and b.diasDeAtraso = 0)
}

// Representa a reserva de uma mesa por um cliente para jogar na luderia
sig Reserva {
    cliente: one Cliente,
    valorReserva: one Int,
    qtdJogos: one Int,
    duracaoReserva: one Int,
    horaExcedente: one Int,
    mesa: one Mesa,
}

// Uma reserva pode incluir ate 5 jogos
fact reservaDeJogos {
    all r: Reserva | r.qtdJogos <= 5
}

// Valor da reserva: 15 reais base mais 3 reais por hora excedente
fact valorReserva {
    all r: Reserva | r.valorReserva = add[15, mul[r.horaExcedente, 3]]
}

// Duracao da reserva: 4, 5 ou 6 horas
fact duracaoReserva {
    all r: Reserva | r.duracaoReserva = 4 or r.duracaoReserva = 5 or r.duracaoReserva = 6
}

// Horas excedentes sao as horas alem das 4 horas base
fact horaExcedente { 
    all r: Reserva | r.horaExcedente = r.duracaoReserva - 4
}

// Duas reservas diferentes nao podem usar a mesma mesa
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

// Cenario exemplo: garante que existe ao menos um cliente inadimplente.
// Usa 7 Int (intervalo -64 a 63) pois os valores 25 e 35 de
// valorAluguel ultrapassam o limite de 5 Int (max 15), causando overflow.
pred exemplo {
    some a: Aluguel | a.diasDeAtraso > 0
}

run exemplo for 5 but 7 Int, 
    exactly 5 Cliente, 
    exactly 5 Exemplar,
    exactly 5 Mesa, 
    exactly 5 Aluguel, 
    exactly 3 Reserva,
    exactly 2 jogoPequeno, 
    exactly 2 jogoMedio, 
    exactly 1 jogoGrande