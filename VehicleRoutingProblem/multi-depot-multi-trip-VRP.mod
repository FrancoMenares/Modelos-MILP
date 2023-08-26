
/* CONJUNTOS */
set D := {-1, -2, -3}			; # CONJUNTO DE DEPOSITOS
set C := {1, 2, 3, 4, 5, 6, 7}	; # CONJUNTO DE CLIENTES
set N := D union C 				; # CONJUNTO DE NODOS DE LA RED

set A1 := {i in D, j in C}			; # CONJUNTO DE ARCOS DEPOSITO-CLIENTE
set A2 := {i in C, j in C: i != j}	; # CONJUNTO DE ARCOS CLIENTE-CLIENTE
set A3 := {i in C, j in D}			; # CONJUNTO DE ARCOS CLIENTE-DEPOSITO
set A  := A1 union A2 union A3		; # CONJUNTO DE ARCOS DE LA RED

set K := {1, 2, 3}	; # CONJUNTO DE VEHICULOS
set V := {1, 2, 3}	; # CONJUNTO DE VUELTAS


/* PARAMETROS */
param costo{A} 	 := Uniform(10, 100)		; # COSTO DE TRANSITAR POR CADA ARCO DE LA RED
param demanda{C} := 1						; # DEMANDA DE CADA NODO DE LA RED
param capacidad  := 1						; # CAPACIDAD DE LOS VEHICULOS 
param B 		 := 99999					; # NÚMERO LO SUFICIENTEMENTE GRANDE
param habilitado{D,K,V} binary default 1	; # 1 SI EL DEPOSITO ESTA HABILITADO PARA EL VEHICULO


/* VARIABLES */
var x{A, K, V} binary	; # 1 SI VEHICULO k UTILIZA EL ARCO (i,j) EN LA VUELTA v
var c{N, K, V} >= 0		; # COSTO OBJETIVO ACUMULADO DEL CAMION k EN EL CLIENTE n


/* FUNCION OBJETIVO */
minimize FO: sum {(i,j) in A, k in K, v in V} costo[i,j] * x[i,j,k,v]	; # MINIMIZAR COSTO DE VIAJE


/* RESTRICCIONES */
#r {}: ;

#r1 {d in D, v in V} : sum {j in C, k in K: (d,j) in A} x[d,j,k,v] <= card (K)	; # PUEDEN SALIR HASTA |K| DESDE EL DEPOSITO
#r2 {d in D, v in V} : sum {i in C, k in K: (i,d) in A} x[i,d,k,v] <= card (K)	; # PUEDEN REGRESAR HASTA |K| VEHICULOS AL DEPOSITO
#r1 {d in D, v in V} : sum {j in C, k in K: (d,j) in A} x[d,j,k,v] <= sum {k in K} habilitado[d,k,v]	; # PUEDEN SALIR DESDE EL DEPOSITO HASTA LA CANTIDAD DE VEHICULOS HABILITADOS PARA EL DEPOSITO
#r2 {d in D, v in V} : sum {i in C, k in K: (i,d) in A} x[i,d,k,v] <= sum {k in K} habilitado[d,k,v]	; # PUEDEN LLEGAR AL DEPOSITO HASTA LA CANTIDAD DE VEHICULOS HABILITADOS PARA EL DEPOSITO

r3 {d in D, k in K, v in V} : sum {j in C: (d,j) in A} x[d,j,k,v] <= habilitado[d,k,v]	; # LOS VEHICULOS SOLO PUEDEN SALIR DE UN DEPOSITO HABILITADO
r4 {d in D, k in K, v in V} : sum {i in C: (i,d) in A} x[i,d,k,v] <= 1 					; # LOS VEHICULOS SOLO PUEDEN LLEGAR A UN DEPOSITO

r5 {j in C} : sum{i in N, k in K, v in V: (i,j) in A} x[i,j,k,v] = 1 ; # SOLO SE PUEDE INGRESAR A UN CLIENTE UNA VEZ
r6 {i in C} : sum{j in N, k in K, v in V: (i,j) in A} x[i,j,k,v] = 1 ; # SOLO SE PUEDE SALIR DE UN CLIENTE UNA VEZ

r7 {m in C, k in K, v in V} : sum {i in N: (i,m) in A} x[i,m,k,v] = sum {j in N: (m,j) in A} x[m,j,k,v]	; # LOS CLIENTES SON VISITADOS POR UN UNICO VEHICULO

r8 {(i,j) in A, k in K, v in V: j not in D} : c[j,k,v] >= c[i,k,v] + costo[i,j] - B*(1 - x[i,j,k,v])	; # ELIMINA SUBTOURS

r9 {k in K, v in V} : sum {(i,j) in A : j in C} demanda[j]*x[i,j,k,v] <= capacidad	; # NO SE DEBE SUPERAR LA CAPACIDAD DE LOS VEHICULOS

r10 {d in D, k in K, v in V: v > 1} : sum {j in C: (d,j) in A} x[d,j,k,v] <= sum {i in C: (i,d) in A} x[i,d,k,v-1]	; # SECUENCIALIDAD DE LAS VUELTAS - LAS VUELTAS COMIENZAN DESDE EL DEPOSITO DE LLEGADA EN LA VUELTA ANTERIOR