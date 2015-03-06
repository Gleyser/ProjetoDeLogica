module AgendamentoDeCaronas

//Assinaturas
open util/ordering[Time] as to
sig Time {}

one sig Sistema{
	alunos : set Usuario,
	caronas: set Carona->Time,
	usuariosAtivos: set Usuario->Time,
	pedidos: set Pedido->Time,
}

abstract sig Usuario{
	regiao: one Regiao,
	matricula: one Matricula,
}

sig Motorista, Caroneiro extends Usuario{}

sig Vagas{
     ocupantes: set Usuario->Time,
	 regiao:one Regiao,
}

sig Pedido{
	pedinte: one Usuario
}

sig Carona{
    vagas: one Vagas,
	motorista: one Motorista,
	regiao: one Regiao
}

sig Matricula{}

abstract sig Regiao{}

one sig CATOLE, LIBERDADE, PRATA, CENTRO, CRUZEIRO, CIDADESVIZINHAS extends Regiao {}


//Fatos

fact alunosTemMatriculaDiferente{
	all m: Matricula | one m.~matricula
}

fact alunoEstaNoSistema{
	some u: Sistema | all a: Usuario | some t:Time | a in getUsuariosAtivos[u,t]
}

fact caroneirosNaoContemOMotorista{
	all c:Carona | all t:Time| !(c.motorista in caroneirosDeUmaCarona[c,t])
}

fact regiaoDaCaronaIdaEhIgualARegiaoDoMotorista{
	all c:Carona | c.motorista.regiao = c.regiao
}

fact motoristaNaoEPedinte {
   all c:Carona | all p:Pedido | !(c.motorista = p.pedinte)
}

fact regiaoDosCaroneirosDeveSerAMesmaDaVaga{
	all v:Vagas| some t:Time | all caroneiro:v.ocupantes.t | v.regiao = caroneiro.regiao
}

fact regiaoDosVagaDeveSerAMesmaDaCarona{
	all c:Carona| c.regiao = c.vagas.regiao
}

fact pedinteNaoEstaEmNenhumaCarona{
	all p:Pedido | all u:p.pedinte | all c:Carona|all t:Time | !(u in caroneirosDeUmaCarona[c,t])
}

fact numDeCaroneirosDeveSerMenorQueQuatro{
	all c:Carona | all t:Time | #caroneirosDeUmaCarona[c,t] <= 4
}

fact caroneirosNaoContemNenhumMotorista{
	all c:Carona | all m:Motorista | all t:Time | !(m in caroneirosDeUmaCarona[c,t])
}

fact caronasTemMotoristasDiferentes{
	all m:Motorista | one m.~motorista
}

fact usuariosJaAlocadoEmUmaCaronaNaoPodeFazerPedido{
	all c:Carona | all p:Pedido | all t:Time | !(p.pedinte in caroneirosDeUmaCarona[c,t])
}

fact cadaCaroneiroPodeFazerApenasUmPedido{
	all c:Caroneiro | one c.~pedinte
}

//Predicados

pred todaVagasTemUmOcupante[v:Vagas]{
	some v.ocupantes
}

pred addUsuarioAtivo[s:Sistema, u:Usuario,t,t':Time] {
u !in (s.usuariosAtivos).t
(s.usuariosAtivos).t' = (s.usuariosAtivos).t + u
}

pred removerUsuarioAtivo[s:Sistema, u:Usuario,t,t':Time] {
u in (s.usuariosAtivos).t
(s.usuariosAtivos).t' = (s.usuariosAtivos).t - u
}

pred addPedido[s:Sistema, p:Pedido,t,t':Time] {
p !in (s.pedidos).t
(s.pedidos).t' = (s.pedidos).t + p
}

pred removerPedido[s:Sistema, p:Pedido,t,t':Time] {
p in (s.pedidos).t
(s.pedidos).t' = (s.pedidos).t - p
}

pred addCaroneiroDaVaga[v:Vagas, u:Usuario,t,t':Time] {
u !in (v.ocupantes).t
(v.ocupantes).t' = (v.ocupantes.t) + u
}

pred removerCaroneiroDaVaga[v:Vagas, u:Usuario,t,t':Time] {
u in (v.ocupantes).t
(v.ocupantes).t' = (v.ocupantes.t) - u
}

pred addCaronaNoSistema[s:Sistema, c:Carona,t,t':Time] {
c !in (s.caronas).t
(s.caronas).t' = (s.caronas.t) + c
}

pred removerCaronaNoSistema[s:Sistema, c:Carona,t,t':Time] {
c in (s.caronas).t
(s.caronas).t' = (s.caronas.t) - c
}

pred init [t: Time] {
no (Sistema.caronas).t | no (Sistema.pedidos).t
}


//Funcoes

fun caroneirosDeUmaCarona[c:Carona, t:Time]: set Usuario{
    c.vagas.ocupantes.t
}

fun motoristaDeUmaCarona[c:Carona]: one Motorista{
	c.motorista
}

fun regiaoDeUmPedido[p:Pedido]: one Regiao{
	p.regiao
}

fun getUsuariosAtivos[s:Sistema, t:Time]: set Usuario{
	s.usuariosAtivos.t
}

pred show []{
	some Sistema
}
run show  for 12
