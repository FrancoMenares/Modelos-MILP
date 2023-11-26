
/* CONJUNTOS */
set nodos 						;
set arcos within {nodos, nodos}	;
set rutas 						;


/* PARAMETROS */
param origen{rutas}  ;
param destino{rutas} ;


/* VARIABLES */
var x{i in nodos, j in nodos, r in rutas: (i,j) in arcos} binary ;


/* FUNCION OBJETIVO */
minimize FO: sum {(i,j) in arcos, r in rutas}x[i,j,r] ;


/* RESTRICCIONES */
r1 {r in rutas}: sum{j in nodos: (origen[r],j) in arcos}x[origen[r],j,r] - sum{i in nodos: (i,origen[r]) in arcos}x[i,origen[r],r] = 1 ;
r2 {r in rutas}: sum{j in nodos: (destino[r],j) in arcos}x[destino[r],j,r] - sum{i in nodos: (i,destino[r]) in arcos}x[i,destino[r],r] = -1 ;
r3 {r in rutas, m in nodos: m != origen[r] and m != destino[r]}: sum{i in nodos: (i,m) in arcos}x[i,m,r] - sum{j in nodos: (m,j) in arcos}x[m,j,r] = 0 ;

r4 {i in nodos}: sum{j in nodos, r in rutas: (i,j) in arcos} x[i,j,r] <= 1 ;
r5 {j in nodos}: sum{i in nodos, r in rutas: (i,j) in arcos} x[i,j,r] <= 1 ;

#r {}: ;









