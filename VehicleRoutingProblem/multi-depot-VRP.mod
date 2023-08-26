
/* CONJUNTOS */
set D := {-1, -2, -3}			; # CONJUNTO DE DEPOSITOS
set C := {1, 2, 3, 4, 5, 6, 7}	; # CONJUNTO DE CLIENTES
set N := D union C 				; # CONJUNTO DE NODOS DE LA RED

set A1 := {i in D, j in C}			; # CONJUNTO DE ARCOS DEPOSITO-CLIENTE
set A2 := {i in C, j in C: i != j}	; # CONJUNTO DE ARCOS CLIENTE-CLIENTE
set A3 := {i in C, j in D}			; # CONJUNTO DE ARCOS CLIENTE-DEPOSITO
set A  := A1 union A2 union A3		; # CONJUNTO DE ARCOS DE LA RED

set K := {1, 2, 3}	; # CONJUNTO DE VEHICULOS


/* PARAMETROS */
param costo{A} 	 := Uniform(10, 100); # COSTO DE TRANSITAR POR CADA ARCO DE LA RED
param demanda{C} := 1				; # DEMANDA DE CADA NODO DE LA RED
param capacidad	 := 3				; # CAPACIDAD DE LOS VEHICULOS 
param B 		 := 99999			; # NÚMERO LO SUFICIENTEMENTE GRANDE
param habilitado{D,K} binary		; # 1 SI EL DEPOSITO ESTA HABILITADO PARA EL VEHICULO

/* VARIABLES */
var x{A, K} binary	; # 1 SI VEHICULO k UTILIZA EL ARCO (i,j)
var c{N, K} >= 0	; # COSTO OBJETIVO ACUMULADO DEL CAMION k EN EL CLIENTE n


/* FUNCION OBJETIVO */
minimize FO: sum {(i,j) in A, k in K} costo[i,j] * x[i,j,k]	; # MINIMIZAR COSTO DE VIAJE


/* RESTRICCIONES */
#r {}: ; # 

#r1 {d in D} : sum {j in C, k in K: (d,j) in A} x[d,j,k] <= card (K)	; # PUEDEN SALIR HASTA |K| DESDE EL DEPOSITO
#r2 {d in D} : sum {i in C, k in K: (i,d) in A} x[i,d,k] <= card (K)	; # PUEDEN REGRESAR HASTA |K| VEHICULOS AL DEPOSITO
#r1 {d in D} : sum {j in C, k in K: (d,j) in A} x[d,j,k] <= sum {k in K} habilitado[d,k]	; # PUEDEN SALIR DESDE EL DEPOSITO HASTA LA CANTIDAD DE VEHICULOS HABILITADOS PARA EL DEPOSITO
#r2 {d in D} : sum {i in C, k in K: (i,d) in A} x[i,d,k] <= sum {k in K} habilitado[d,k]	; # PUEDEN LLEGAR AL DEPOSITO HASTA LA CANTIDAD DE VEHICULOS HABILITADOS PARA EL DEPOSITO

r3 {d in D, k in K} : sum {j in C: (d,j) in A} x[d,j,k] <= habilitado[d,k] ; # LOS VEHICULOS SOLO PUEDEN SALIR DE UN DEPOSITO HABILITADO
r4 {d in D, k in K} : sum {i in C: (i,d) in A} x[i,d,k] <= habilitado[d,k] ; # LOS VEHICULOS SOLO PUEDEN LLEGAR A UN DEPOSITO HABILITADO

r5 {j in C} : sum{i in N, k in K: (i,j) in A} x[i,j,k] = 1 ; # SOLO SE PUEDE INGRESAR A UN CLIENTE UNA VEZ
r6 {i in C} : sum{j in N, k in K: (i,j) in A} x[i,j,k] = 1 ; # SOLO SE PUEDE SALIR DE UN CLIENTE UNA VEZ

r7 {m in C, k in K} : sum {i in N: (i,m) in A} x[i,m,k] = sum {j in N: (m,j) in A} x[m,j,k]	; # LOS CLIENTES SON VISITADOS POR UN UNICO VEHICULO

r8 {(i,j) in A, k in K: j not in D} : c[j,k] >= c[i,k] + costo[i,j] - B*(1 - x[i,j,k])	; # ELIMINA SUBTOURS

r9 {k in K} : sum {(i,j) in A : j in C} demanda[j]*x[i,j,k] <= capacidad	; # NO SE DEBE SUPERAR LA CAPACIDAD DE LOS VEHICULOS

