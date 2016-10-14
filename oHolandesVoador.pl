% Este programa esta dividido em 3 partes principais: tokenizador,
% gramatica e resolvedor.
%
% Cada parte eh acompanhada de comentarios para sua melhor compreensao.
% Obs.: este programa utiliza a biblioteca CLPFD como parte de sua
% solucao.
%
% por Andre Pinheiro Borba
%  RA122842
:- module(oHolandesVoador, [solver/2]).
:- use_module(library(clpfd)).



%Funcao principal SOLVER
solver(Arquivo, Resultado) :-
	abreArquivo(Arquivo, Lista),
	phrase(gramatica(Dominios, Restricoes), Lista),
	resolvedor(Dominios,Restricoes, Resultado).


%%% **** TOKENIZADOR ****
abreArquivo(File,L):-
	open(File, read, X),
	current_input(Stream),
	set_input(X),
	tokador(L), !,
	set_input(Stream),
	close(X).


% tokador(L) coloca em L a lista de tokens.
tokador(L) :-
    get_char(X),
    tokador(X, L).

%end of file
tokador(end_of_file, []):- !.

%tokador('\n', L) :- !, tokador(L).
tokador(' ', L) :-
    !,
    tokador(L).

tokador('\'', L) :-
	!,
	tokador(L).

tokador(X, L) :-
    (is_alnum(X); is_underscore(X)),
    !,
    palavra([X], L).

tokador(X, L) :-
    tokador(L1),
    L = [X | L1].

% palavra(LP, L) ja leu caracteres de palavra em LP e retorna L

palavra(LP, L) :-
    !,
    get_char(X),
    palavra(X, LP, L).

%LP eh uma lista de caracteres
%P eh uma palavra
%retorna a palavra dentro de uma lista
palavra(end_of_file, LP, [P]) :-
    !,
    reverse(LP, LPR),
    converte(LPR, P).

palavra(' ', LP, [P | L]) :-
    !,
    reverse(LP, LPR),
    converte(LPR, P),
    tokador(L).


palavra('\'', LP, [P | L]) :-
    !,
    reverse(LP, LPR),
    converte(LPR, P),
    tokador(L).


palavra(X, LP, L) :-
    (is_alnum(X); is_underscore(X)),
    !,
    palavra([X | LP], L).

palavra(X, LP, L) :-
    reverse(LP, LPR),
    converte(LPR, P),
    tokador(L1),
    L = [P, X | L1].

is_underscore('_').


%converte para numero caso seja algo do tipo ['1'].
converte([I],O) :-
	is_digit(I),
	atom_number(I, O).

%converte para um atomo.
converte(L, O):-
	isList(L),
	atom_chars(O, L).

%verifica se variavel eh uma lista.
isList([_|_]).
isList([]).


%%% **** GRAMATICA ****
gramatica(D,R) --> linhasDomain(D), fimDeLinha,linhasRestricao(R), !.

linhasDomain([L|Ls]) --> linhaDomain(L), linhasDomain(Ls).
linhasDomain([]) --> [].
linhaDomain([domain(Dn)|Dl]) --> atomo(Dn), doisPontos, domainList(Dl), fimDeLinha.
domainList([D| Dl]) --> atomo(D), virgula, domainList(Dl).
domainList([D]) --> atomo(D).


linhasRestricao([L|Ls]) --> linhaRestricao(L), linhasRestricao(Ls).
linhasRestricao([]) --> [].

linhaRestricao([or, P1,P2]) --> parcelaExp(P1), ou, {!}, parcelaExp(P2), fimDeLinha.
linhaRestricao([R, P1, P2]) --> parcelaExp(P1), restricao(R), parcelaExp(P2), fimDeLinha.

parcelaExp([R, P1, P2]) --> primeiraExp(P1), restricao(R), parcelaExp(P2).
parcelaExp([S, P1, P2]) --> primeiraExp(P1), sinal(S), parcelaExp(P2).
parcelaExp(P) --> primeiraExp(P).
parcelaExp(P) --> modulo(P).

modulo([abs, [S, P1, P2]]) --> barra, primeiraExp(P1), sinal(S), primeiraExp(P2), barra.

restricao('>') --> ['>'], {!}.
restricao('<') --> ['<'], {!}.
restricao('=') --> ['='], {!}.

sinal('+') --> ['+'], {!}.
sinal('-') --> ['-'], {!}.

primeiraExp(N) --> number(N), {!}.
primeiraExp(A) --> atomo(A), {!}.

number(D) --> [D], {number(D), !}.
atomo(A) --> [A], {!}.

virgula --> [','], {!}.
doisPontos --> [':'], {!}.
ou --> ['or'], {!}.
barra -->['|'], {!}.
fimDeLinha --> ['\n'], {!}.


%%% **** RESOLVEDOR ****

%gera solucao no formato ideal.
geraSolucao([], []).
geraSolucao([D-V|T],R):-
	geraSolucao(T,R1),
	X = [c(D,V)],
	append(X, R1, R).

% Resolvedor (-D, -C, +R)
resolvedor(D, C, R) :-
    maplist(criaVariaveis, D, ListaVars, NomeValor),  %para cada dominio executa o metodo criaVariaveis.
    append(ListaVars, ListaVarsFlat),	              %faz a lista de listas flat. ListaVarsFlat eh uma lista com todas as variaveis.
    append(NomeValor, NomeValorFlat),		      %faz a lista de listas flat. NomeValorFlat eh uma lista de pares (atomo-Var. ex.: alemao-Var).
    maplist(restricao(NomeValorFlat), C),             %interpreta cada restricao fornecida na lista e gera uma constraint do CLPFD.
    label(ListaVarsFlat),                             %Como cada problema tem apenas uma unica solucao, esta eh uma forma de informar ao CLPFD que encontre todas as solucoes numericas (no caso uma).
    geraSolucao(NomeValorFlat,R).                   %gera lista com a solucao final.


%Metodo que cria uma variavel para cada "membro" de um dominio.
% (-[], +NomeVars, +NomeValor).
criaVariaveis([domain(_)|Dominio], NomeVars, NomeValor) :-
    length(Dominio, N),			       %calcula length da lista.
    length(NomeVars, N),                           %gera uma lista Vars, preenchida com variaveis, de tamanho N.
    NomeVars ins 1 .. N,                           %os elementos de Vars devem assumir valores de 1 ate N.
    all_distinct(NomeVars),                        %os elementos de Vars devem ser todos distintos.
    pairs_keys_values(NomeValor, Dominio, NomeVars). %cria uma lista de pares da forma nome-Variavel (ex: alemao-Var), essa lista sera usada para gerar a lista de solucoes apos o calculo.


% Ha 4 tipos de restricoes: =, <, >, or.
% Cada restricao eh composta de um tipo (=,<,>,or) e 2 parcelas, que por
% sua vez podem ser compostas de outras parcelas (ex:
% [=,espanhol,[+,vermelha,1]]). Cada expressao eh interpretada, e no
% final uma restricao no moldes do CLPFD eh gerada.
restricao(Vars, [=, L, R]) :-
    parcelaExpS(L, Vars, X),   %interpreta parcela esquerda
    parcelaExpS(R, Vars, Y),   %interpreta parcela direita
    X #= Y.                   %gera restricao

restricao(Vars, [>, L, R]) :-
    parcelaExpS(L, Vars, X),
    parcelaExpS(R, Vars, Y),
    X #> Y.

restricao(Vars, [<, L, R]) :-
    parcelaExpS(L, Vars, X),
    parcelaExpS(R, Vars, Y),
    X #< Y.

restricao(Vars, [or,L , R]):-
    parcelaExpS(L, Vars, X),
    parcelaExpS(R, Vars, Y),
    (X ; Y).

%Interpreta cada parcela de expressao recursivamente
%Caso base: numero ou "membro de um dominio" (ex: brasileiro).
parcelaExpS(N, _, N) :- number(N).
parcelaExpS(S, Vars, X) :- member(S-X, Vars).

parcelaExpS([-, L, R], Vars, X - Y) :-
    parcelaExpS(L, Vars, X),
    parcelaExpS(R, Vars, Y).

parcelaExpS([+, L, R], Vars, X + Y) :-
    parcelaExpS(L, Vars, X),
    parcelaExpS(R, Vars, Y).

parcelaExpS([=,L,R], Vars, X = Y):-
	parcelaExpS(L, Vars, X),
	parcelaExpS(R, Vars, Y).

parcelaExpS([abs,E], Vars, abs(X) ):-
	parcelaExpS(E, Vars, X).
