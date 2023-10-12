
/* Conjuntos */
param o	;	set O := {o}			;	# deposito
param s ;	set S := {s}			;	# deposito ficticio
set R								;	# clientes

set A1 := {i in O, j in R} 			;	# arcos deposito - clientes
set A2 := {i in R, j in R: i != j } ;	# arcos clientes - clientes
set A3 := {i in R, j in S}			;	# arcos clientes - deposito ficticio

set N := O union R union S 			;	# conjunto de nodos de la red
set A := A1 union A2 union A3 		;	# conjunto de arcos de la red	
set K 								;	# conjunto de vehiculos
set M 								;	# conjunto de periodos de tiempo


/* Parametros */
param b										;	# capacidad de los vehiculos
param d{N}									;	# demanda de un cliente
param TTI{M} 								;	# cota inferior de cada periodo
param TTF{M} 								;	# cota superior de cada periodo
	
param TI{(i,j) in A, m in M} default 0		;	# cota inferior para un arco en un periodo
param TF{(i,j) in A, m in M} default 0		;	# cota superior para un arco en un periodo
	
param tt{N,M}  								;	# tiempo de atender un cliente en un perido
param cc{N,M} 								; 	# costo de atender un cliente en un periodo
param tf{N,M}								;	# tasa de fallo de un cliente en un periodo
param t{A,M} 								;	# tiempo de desplazarse por un arco en un periodo
param c{A,M} 								;	# costo de desplazarse por un arco en un periodo
param B := max {m in M}TTF[m] 				;	# numero suficientemente grande


/* Conjuntos, Parametros y Variables para la normalizaci�n */
param cantobj 							:= 	2				;	# cantidad de objetivos del problema
param cantejc 							:= 	11				;	# cantidad de ejecuciones para la frontera de pareto
set   objetivos 						:= 	{1..cantobj}	;	# conjunto de objetivos del problema
set   ejecuciones 						:= 	{1..cantejc}	;	# conjunto de ejecuciones para la frontera de pareto
param g 							default 0 				;	# identifica un objetivo en particular
param sigma{ejecuciones,objetivos}							;	# ponderadores para la frontera de pareto
param betha{objetivos} 				default 0				;	# ponderadores de cada objetivo
param MV{objetivos} 				default 999999999		;	# mejor valor alcanzado por cada objetivo
param PV{objetivos} 				default 0				;	# peor valor alcanzado por cada objetivo
var   F{objetivos} 						>= 	0				;	# funciones objetivos del problema


/* Variables */
var x{A,M,K} binary		;   # 1 si se cruza el arco i,j en el momento m por el vehiculo k
var y{N,K} binary 		;	# 1 si el vehiculo k sale del nodo i
var T{N,K} >= 0 		;	# instante de salida del nodo j del vehiculo k


/* Funcion objetivo */
minimize FO1 : F[g]																	;	# para minimizar cada objetivo por separado
minimize FO2 : sum {i in objetivos} betha[i] * (MV[i] - F[i])/(MV[i] - PV[i])		;	# para minimizar la funciones objetivos normalizadas
minimize FO3 : sum {i in objetivos} F[i] 											;	# funcion de prueba


/* Restricciones */
subject to

	/* Objetivos */
	O1 : F[1] = sum {(i,j) in A, m in M, k in K} (c[i,j,m] + cc[j,m])*x[i,j,m,k] 					;	# funcion de costo
	O2 : F[2] = sum {(i,j) in A, m in M, k in K} tf[j,m]*x[i,j,m,k]									;	# funcion de tasa de fallo

	/* Relacion de variables */                                                              
	R1 {i in N, k in K : i != s} : y[i,k] = sum {j in N, m in M: (i,j) in A} x[i,j,m,k] 			;	# si se viajo desde un nodo, entonces fue visitado
	R2 {i in N, k in K} : T[i,k] <= B*y[i,k]														;	# si un vehiculo sale de un nodo, entoces tiene tiempo de salida

	/* Balance de flujo */                                                                   
	R3 : sum {j in R, m in M, k in K : (o,j) in A} x[o,j,m,k] <= card (K)							;	# pueden salir hasta k vehiculos desde el origen
	R4 : sum {i in R, m in M, k in K : (i,s) in A} x[i,s,m,k] <= card (K)							;	# deben regresar hasta K vehiculos al nodo ficticio

	R5 {j in R} : sum {i in N, m in M, k in K : (i,j) in A} x[i,j,m,k] = 1							;	# se puede llegar a un nodo una vez
	R6 {i in R} : sum {j in N, m in M, k in K : (i,j) in A} x[i,j,m,k] = 1							;	# se puede salir de un nodo una vez

	/* Secuencialidad */                                                                            
	R8 {(i,j) in A, m in M, k in K} : T[j,k] >= T[i,k] + t[i,j,m] + tt[j,m] - B*(1 - x[i,j,m,k]) 	;   # el tiempo transcurrido siempre va en aumento (agrega tiempos de espera)
	R9 {(i,j) in A, m in M, k in K} : T[j,k] <= T[i,k] + t[i,j,m] + tt[j,m] + B*(1 - x[i,j,m,k])	;	# no se admiten tiempos de espera

	/* Intervalo de tiempo */                                                                
	R10 {(i,j) in A, m in M, k in K} : T[i,k] <= TF[i,j,m] + B*( 1 - x[i,j,m,k]) 					;	# el tiempo transcurrido esta dentro de un intervalo temporal
	R11 {(i,j) in A, m in M, k in K} : T[i,k] >= TI[i,j,m] - B*( 1 - x[i,j,m,k]) 					; 	# el tiempo esta fuera de un intervalo temporal anterior

	/* Restriccion de capacidad */                                                         
	R12 {k in K} : sum {i in N} d[i]*y[i,k] <= b 													;	# se debe respetar la capacidad de los vehiculos

