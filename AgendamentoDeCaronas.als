module AgendamentoDeCaronas

//Assinaturas

sig Sistema{
	alunos : set Usuario
	caronas: set Carona
	pedidos: set Pedido
	usuariosAtivos: set Usuario
}

sig Usuario{
	regioes: one Regiao,
	matricula: one Matricula,
}

sig Pedido{

}

sig Carona{
	
}

sig Matricula{}

abstract sig Regiao{}

one sig CATOLE, LIBERDADE, PRATA, CENTRO, CRUZEIRO, CIDADESVIZINHAS extends Regiao {}

//Predicados

pred alunosTemMatriculaDiferente{
	all m: Matricula | one m.~matricula
}

pred alunoEstaNaUfcg{
	some u: Sistema | all a: Usuario | a in u.usuariosAtivos
}

//Fatos

fact{
	alunosTemMatriculaDiferente
	alunoEstaNaUfcg
}


pred show []{
	some UFCG
}
run show
