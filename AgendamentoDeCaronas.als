module AgendamentoDeCaronas

//Assinaturas

sig Sistema{
	alunos : set Usuario,
	caronas: set Carona,
	pedidos: set Pedido,
	usuariosAtivos: set Usuario
}

sig Usuario{
	regiao: one Regiao,
	matricula: one Matricula,
}

sig Motorista extends Usuario{}


sig Vaga{
     ocupante: lone Usuario,
}

sig Pedido{
	pedinte: one Usuario
}

sig Carona{
	caroneiros: set Usuario,
	motorista: one Motorista,
    vagas: set Vaga,
}

sig CaronaIda extends Carona {
	regiaoIda: one Regiao
}

sig CaronaVolta extends Carona{
	regiaoVolta: one Regiao
}

sig Matricula{}

abstract sig Regiao{}

one sig CATOLE, LIBERDADE, PRATA, CENTRO, CRUZEIRO, CIDADESVIZINHAS extends Regiao {}

//Predicados


pred alunosTemMatriculaDiferente{
	all m: Matricula | one m.~matricula
}

pred alunoEstaNoSistema{
	some u: Sistema | all a: Usuario | a in u.usuariosAtivos
}

pred caroneirosNaoContemOMotorista{
	all c:Carona | !(c.motorista in c.caroneiros)
}

pred regiaoDaCaronaIdaEhIgualARegiaoDoMotorista{
	all c:CaronaIda | c.motorista.regiao = c.regiaoIda
}

pred regiaoDaCaronaVoltaEhIgualARegiaoDoMotorista{
	all c:CaronaVolta | c.motorista.regiao = c.regiaoVolta
}

pred motoristaNaoEPedinte {
   all c:Carona, p:Pedido | !(c.motorista = p.pedinte)
}

//Fatos

fact{
	alunosTemMatriculaDiferente
	alunoEstaNoSistema
	caroneirosNaoContemOMotorista
	motoristaNaoEPedinte
	regiaoDaCaronaIdaEhIgualARegiaoDoMotorista
	regiaoDaCaronaVoltaEhIgualARegiaoDoMotorista
}


pred show []{
	some Sistema
}
run show for 4
