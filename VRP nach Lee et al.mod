/*********************************************
 * OPL 22.1.0.0 Model
 * Author: fabia
 * Creation Date: 29.04.2022 at 16:29:00
 *********************************************/

// parameters & sets
int n = ...; // amount of customers	

{int} N = asSet(1..n);  // set of customers

{int} N0 = {0} union N union {n+1}; // set of customer incl. depots

int m = ...; // amount of vehicles

{int} M = asSet(1..m); // set of vehicles

float Q = ...; // capacity

float r[N]= ...; // demand

float b[N]= ...;// deadline 

tuple Kanten {int i ; int j;};

{Kanten} A  = {<i,j> | i in N0, j in N0}; // set of arcs A

// Unidirektionale Kanten
{Kanten} A_unidirected = {<i,j> | i in N0, j in N0: i<j};

// Kardinalität A_unidirected
int cAu = card(A_unidirected);  					// amount of routes that can be delayed

// Kanten-Indexmenge
{int} subsets_1 = asSet(1..cAu);					// set of routes that can be delayed

Kanten B1[x in subsets_1];

execute{for (var f in subsets_1)
            for (var edge in A_unidirected)
                if (Opl.ord(A_unidirected,edge) == f-1){B1[f]= edge;};
          writeln("B1= "+ B1);
}

int u[N0,N0,subsets_1];

execute{for (var edge in A_unidirected)
            for (var x in subsets_1)
                if (edge == B1[x]) {u[edge.i][edge.j][x] = 1;
                                    u[edge.j][edge.i][x] = 1;};
    }   
    
 
{int} subsets_2 = asSet(cAu+1..ftoi((pow(cAu,2) -cAu)/2));
{int} subsets_1_2 = subsets_1 union subsets_2; 

int K = 999;	// large number

float d[N0,N0]= ...; 			// max deviation of travel time

float o [N]= ...;			// max deviation of demand

float G = ...;	// uncertainty budget of travel time				

float L = ...;	// uncertainty budget of demand

float t[N0,N0] = ...;				// travel time matrix

float c[N0,N0] =...;				// distance matrix

/*//Anlegen von Standorten (Alternative Formulierung)
tuple Standorte {int i; int j;}
Standorte Punkt [N0]= ...;

//Entfernung der Standorte
execute{function Entfernung (i,j)
		{return Opl.sqrt (Opl.pow(N0.i-N0.i,2) + Opl.pow(N0.i-N0.j,2));}
		for (var i in N0){	for (var j in N0){
		  c [i][j] = Entfernung (Punkt[i], Punkt[j])
		}}}*/

 // optimization model
// decision variables
dvar boolean x[A, M];						
dvar float+ s[N0, M, subsets_1];
dvar float+ p[N,M];
dvar float+ z[M];

// objective function
minimize sum(k in M) sum(i in N0) sum(j in N0) c[i,j]*x[<i,j>,k];

// constraints
subject to {
  // (2)
  NB2:forall (i in N) {
  sum (k in M) sum (j in N0: j!=i) x[<i,j>,k] == 1;
  };
  
  // (3) 
  NB3:forall (k in M) {
   sum (j in N0: j !=0) x[<0,j>,k] == 1;
  };

  // (4)
  NB4:forall (i in N, k in M) {
   sum (j in N0: j!=i) x[<i,j>,k] - sum (j in N0: j!=i) x[<j,i>,k] == 0;
  };   
  
  // (5)
  NB5:forall (k in M) {
     sum (i in N0: i!=n+1) x[<i,(n+1)>,k] == 1;
  };
  
   // (11)
  NB11: forall (k in M) {
	sum (i in N) r[i] * sum (j in N0: j!=i) x[<i,j>,k] + L*z[k] + sum (i in N) p[i,k] <= Q ;
  };    
  // (12)
  NB12: forall (k in M, i in N,j in N: i!=j) {
    z[k] + p[i,k] >= o[i] * r[i] * sum (j in N0: j!=i) x[<i,j>,k];
  };    
  // (13)
  NB13: forall (i in N0,j in N0: i!=j, k in M, f in subsets_1) {											
    s[i,k,f] + t[i,j] + d[i,j] * u [i,j,f] * t[i,j] - K * (1 - x[<i,j>,k]) <= s[j,k,f]	;		
  };
  
  // (14)
  NB14: forall (i in N, k in M, f in subsets_1) {									
    0 <= s[i,k,f] <= b[i];  
  };    
  // (15)																			
    NB15: forall (k in M, i in N0, j in N0: i==j) {
   x[<i,j>,k] == 0;  
  };
	// (16)
	NB16: forall (i,j in N0, k in M){
	  x[<0,n+1>,k] ==  0;
	}
};
