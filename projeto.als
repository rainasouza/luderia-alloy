open util/integer
module luderia

//Especificações do projeto:
//Uma luderia quer um sistema para organizar os aluguéis e reservas de jogos. 
//A luderia pode possuir vários exemplares do mesmo jogo. 
//Um cliente pode alugar um jogo para levar para casa ou fazer uma reserva para jogar na Luderia em uma determinada data.
//Todo aluguel deve estar associado a um cliente e um exemplar de jogo, e tem duração de 2 dias. 
//As reservas dependem da disponibilidade de mesas na Luderia e é possível reservar até 5 jogos, com duração base de 4 horas. 
//A luderia possui 5 mesas. 
//Os jogos na luderia podem ser classificados em pequenos, médios e grandes e o valor do aluguel é de 15, 25 e 35 reais, respectivamente, de acordo com o tipo do jogo. 
//Reservas têm duração base de 4 horas, pelo valor de 15 reais, podendo chegar até 6 horas com adicional de 3 reais a hora. 
//Um cliente não pode alugar novos jogos enquanto tem uma devolução atrasada. 
//A multa por atraso é de metade do valor do aluguel original por dia de atraso.

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

// Um cliente só pode ter 3 alugueis ativos por vez.
fact limiteAlugueisCliente {
    all c: Cliente |
        #({a: Aluguel | a.cliente = c}) <= 3
}

// Dias de atraso e multa nao podem ser negativos
fact valoresValidos {
    all a: Aluguel | a.diasDeAtraso >= 0 and a.valorMulta >= 0
}

// Valor do aluguel depende do tipo do jogo: 15, 25 ou 35 reais
fact valorPorJogo {
    all a: Aluguel |
        (a.exemplar.jogo in jogoPequeno and a.valorAluguel = 15) or
        (a.exemplar.jogo in jogoMedio and a.valorAluguel = 25) or
        (a.exemplar.jogo in jogoGrande and a.valorAluguel = 35)
}

// Multa = metade do valor do aluguel multiplicado pelos dias de atraso
fact regraMulta {
    all a: Aluguel | a.valorMulta = mul[div[a.valorAluguel, 2], a.diasDeAtraso]
}

// Cliente com devolucao atrasada nao pode alugar, Se existir pelo menos um aluguel
// com devolução atrasada, todos os alugueis estão atrasados.
fact clienteAtrasadoNaoAluga {
    all c: Cliente | (some a : Aluguel | a.cliente = c and a.diasDeAtraso > 0)
    implies
    (all b: Aluguel | b.cliente = c implies b.diasDeAtraso > 0)
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
