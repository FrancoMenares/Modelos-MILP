
/* CONJUNTOS */
set D_ini := { -1, -2, -3 }				; # CONJUNTO DE DEPOSITOS INICIALES
set C := { 1, 2, 3, 4, 5, 6, 7 }		; # CONJUNTO DE CLIENTES
set D_int := { -1000, -2000, -3000 }	; # CONJUNTO DE DEPOSITOS FICTICIOS INTERMEDIOS
set D_fin := { -10000, -20000, -30000 }	; # CONJUNTO DE DEPOSITOS FICTICIOS FINALES
set N := D_ini union C union D_int union D_fin	; # CONJUNTO DE NODOS DE LA RED

set A0 := {i in D_ini, j in D_int : i* 1000 == j} ; # CONJUNTO DE ARCO RELACIONALES ENTRE DEPOSITO INICIAL E INTERMEDIO (RELACIÓN UNO A UNO)

set A1 := {i in D_ini, j in C}					; # CONJUNTO DE ARCOS DEPOSITO_INICIAL-CLIENTE
set A2 := {i in C, j in C : i != j}				; # CONJUNTO DE ARCOS CLIENTE-CLIENTE
set A3 := {i in C, j in D_int}					; # CONJUNTO DE ARCOS CLIENTE-DEPOSITO_INTERMEDIO
set A4 := {i in D_int, j in D_fin : i* 10 == j}	; # CONJUNTO DE ARCOS DEPOSITO_INTERMEDIO-DEPOSITO_FINAL
set A  := A1 union A2 union A3 union A4			; # CONJUNTO DE ARCOS DE LA RED

set K := { 1 }	; 									# CONJUNTO DE VEHICULOS
set V := { 1, 2, 3, 4, 5, 6, 7 }	; 				# CONJUNTO DE VUELTAS


/* PARAMETROS */
param costo{A} 	 default 0						; # COSTO DE TRANSITAR POR CADA ARCO DE LA RED
param demanda{N} default 0						; # DEMANDA DE CADA NODO DE LA RED
param capacidad  := 10							; # CAPACIDAD DE LOS VEHICULOS 
param habilitado_ini{D_ini,K} binary default 0	; # 1 SI EL DEPOSITO ESTA HABILITADO PARA EL VEHICULO COMIENCE SUS OPERACIONES EN EL (DEPOSITO INICIAL). 0 SI NO
param habilitado_fin{D_fin,K} binary default 0	; # 1 SI EL DEPOSITO ESTA HABILITADO PARA EL VEHICULO TERMINE SUS OPERACIONES EN EL (DEPOSITO FICTICIO FINAL). 0 SI NO
param compatible{D_int,K} binary default 0		; # 1 SI EL VEHICULO PUEDE VISITAR EL DEPOSITO. 0 SI NO
param B := sum {i in N: i not in D_int union D_fin}(max {j in N: (i,j) in A}(costo[i,j])) 	; # NÚMERO LO SUFICIENTEMENTE GRANDE


/* VARIABLES */
var x{A, K, V} binary	; # 1 SI VEHICULO k UTILIZA EL ARCO (i,j) EN LA VUELTA v
var c{N, K, V} >= 0		; # COSTO OBJETIVO ACUMULADO DEL CAMION k EN EL CLIENTE n


/* FUNCION OBJETIVO */
minimize FO: sum {(i,j) in A, k in K, v in V} costo[i,j] * x[i,j,k,v]	; # MINIMIZAR COSTO DE VIAJE


/* RESTRICCIONES */
#r {}: ;

# LOS VEHICULOS SOLO PUEDEN INICIAR OPERACIONES DESDE UN DEPOSITO INICIAL HABILITADO
r1 {i in D_ini, k in K, v in V: v=1} : sum {j in C : (i,j) in A} x[i,j,k,v] <= habilitado_ini[i,k]	; 

# LOS VEHICULOS SOLO PUEDEN SALIR DE UN DEPOSITO INTERMEDIO COMPATIBLE
r2 {i in D_int, k in K, v in V: v!=1} : sum {j in C : (i,j) in A} x[i,j,k,v] <= compatible[i,k]	; 
# LOS VEHICULOS SOLO PUEDEN LLEGAR A UN DEPOSITO INTERMEDIO COMPATIBLE
r3 {j in D_int, k in K, v in V} 	  : sum {i in C : (i,j) in A} x[i,j,k,v] <= compatible[j,k]	; 

# SOLO SE PUEDE INGRESAR A UN CLIENTE UNA VEZ
r4 {j in C} : sum{i in N, k in K, v in V : (i,j) in A} x[i,j,k,v] = 1 ; 
# SOLO SE PUEDE SALIR DE UN CLIENTE UNA VEZ
r5 {i in C} : sum{j in N, k in K, v in V : (i,j) in A} x[i,j,k,v] = 1 ; 

# LOS CLIENTES SON VISITADOS POR UN UNICO VEHICULO
r6 {m in C, k in K, v in V} : sum {i in N : (i,m) in A} x[i,m,k,v] = sum {j in N : (m,j) in A} x[m,j,k,v]	; 

# ELIMINA SUBTOURS - TIEMPOS SIEMPRE ASCENDENTES
r7 {(i,j) in A, k in K, v in V} : c[j,k,v] >= c[i,k,v] + costo[i,j] - B*(1 - x[i,j,k,v])	; 
# ELIMINA TIEMPOS DE ESPERA
r8 {(i,j) in A, k in K, v in V} : c[j,k,v] <= c[i,k,v] + costo[i,j] + B*(1 - x[i,j,k,v])	; 

# NO SE DEBE SUPERAR LA CAPACIDAD DE LOS VEHICULOS
r9 {k in K, v in V} : sum {(i,j) in A} demanda[j]*x[i,j,k,v] <= capacidad	; 

# SECUENCIALIDAD DE LAS VUELTAS - LAS VUELTAS COMIENZAN DESDE EL DEPOSITO INTERMEDIO DE LLEGADA EN LA VUELTA ANTERIOR
r10 {(m,n) in A0, k in K, v in V: v > 1} : sum {j in C : (m,j) in A} x[m,j,k,v] <= sum {i in C: (i,n) in A} x[i,n,k,v-1]	; 

# UN VEHICULO DEBE LLEGAR AL DEPOSITO DE TERMINO SI INICIO UNA RUTA
r12 {k in K} : sum {(i,j) in A4, v in V} x[i,j,k,v]*habilitado_fin[j,k] = sum {(i,j) in A1} x[i,j,k,1] 		; 
# SI SE LLEGA A UN DEPOSITO, ENTONCES SE PUEDE IR A UN DEPOSITO FICTICIO
r13 {m in D_int, k in K, v in V} : sum {i in C : (i,m) in A} x[i,m,k,v] >= sum {j in D_fin : (m,j) in A} x[m,j,k,v] ; 

# EL TIEMPO DE INICIO DE UNA VUELTA  EN UN DEPOSITO INICIAL ES IGUAL AL TIEMPO DE TERMINO DE LA VUETA ANTERIOR EN EL DEPOSITO INTERMEDIO
r14 {(i,j) in A0, k in K, v in V: v > 1} : c[i,k,v] >= c[j,k,v-1] 	; 
# PARA CADA VEHICULO EL TIEMPO AL DEPOSITO FICTICIO DEBE SER MAYOR A CUALQUIER OTRO NODO
r15 {j in N, k in K, v in V, u in V, i in D_fin} : c[i,k,v] >= c[j,k,u] ; 






