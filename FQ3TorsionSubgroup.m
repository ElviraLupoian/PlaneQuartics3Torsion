// this is the magma code used to verify that our computed orbits generate the 3-torsion subgroup 


// we work with the following model of the Fermat Quartic :  f := x^4 - y^3*z -4*y*z^3 //

// our 3-torsion points are of the form D s.t  3D = div h , h : y^2 = a1xy +a2y + a3x^3 + a4x^2 + a5x + a6 


Zx<x> := PolynomialRing(Integers());
f :=  x^32 - 8*x^31 + 28*x^30 - 64*x^29 + 130*x^28 - 216*x^27 + 120*x^26 + 420*x^25 - 1058*x^24 + 1032*x^23 - 516*x^22 - 128*x^21 + 3494*x^20 - 15256*x^19 + 39888*x^18 - 76812*x^17 + 119719*x^16 - 158376*x^15 + 182304*x^14 - 185360*x^13 + 168338*x^12 - 137584*x^11 + 101508*x^10 - 67596*x^9 + 40588*x^8 - 21912*x^7 + 10536*x^6 - 4440*x^5 + 1612*x^4 - 488*x^3 + 112*x^2 - 16*x + 1;
K := NumberField(f);

// all of our orbits are defined over the above number field 

OK := MaximalOrder(K) ;
PP := PrimesUpTo(130,K) ;
P := PP[4] ;
F37, pi := ResidueClassField(P) ;

Zxyz<x,y,z> := PolynomialRing(Integers(),3) ;
f := x^4 - y^3*z -4*y*z^3 ;
P2 := ProjectiveSpace(Zxyz) ;
X := Curve(P2, f) ;
X37 := BaseChange(X, F37);
Cl37, phi, psi := ClassGroup(X37);
Z := FreeAbelianGroup(1) ;
degr := hom< Cl37 -> Z | [ Degree(phi(g)) : g in OrderedGenerators(Cl37)]>;


J37 := Kernel(degr) ;

// note that reduction modulo P is injective on torsion 

FX37 := FunctionField(X37) ;
ZX<x> := PolynomialRing(K) ;
f1 := x^8 - 72*x^4 -432;
Zu<u> := PolynomialRing(K) ;
s := (1/864)*(u^7 -36*u^3 ) ;
R := Roots(f1, K) ;

a := [ [ 1, R[i,1], 2, Evaluate(s, R[i,1]), 0,0,0] : i in [1..8] ] ;
a1 := a;
add := [ [Denominator(b) : b in c] : c in a1] ;
add1 := [ Lcm(b) : b in add] ;
aa := [ [add1[i]*c : c in a1[i]] : i in [1..#a1] ];
aao := [ [ OK ! b : b in c] : c in aa] ;


aaao := [] ;
for i in [1..8] do ;
a1 := aao[i];                                   
a1 := [ Eltseq(b) : b in a1] ;
a1 := [ [Integers() ! c : c in b ] : b in a1];
ga1 := [ GCD(b) : b in a1];
ga1 := [ Integers() ! b : b in ga1] ;
g := GCD(ga1) ;
aa1 := [ [b/g : b in c] : c in a1];
aa1 := [ [ Integers() ! b : b in c] : c in aa1];
aa1 := [ OK ! b : b in aa1];
aaao[i] := aa1;
end for;


aa37 := [ [pi(b) : b in c] : c in aaao] ;

Zxyz<x,y,z> := PolynomialRing(F37,3) ;

Zxyz<x,y,z> := PolynomialRing(F37,3) ;
a := aa37;
Cubics := [ -b[1]*y^2*z + b[2]*x*y*z + b[3]*y*z^2 + b[4]*x^3 + b[5]*x^2*z + b[6]*x*z^2 + b[7]*z^3 : b in a];

Cubics2 := [ Evaluate(s, [FX37.1, FX37.2, 1]) : s in Cubics] ;
D := [ Divisor(c) : c in Cubics2];
DDd := [ Decomposition(a) : a in D ];
DDd1 := [ [ a[i,2] : i in [1..#a] ] :  a in DDd ];
DDd1 := [ [ 1/3*b : b in a ] : a in DDd1 ];
DDd1 := [ [ Integers() ! b : b in a ] : a in DDd1 ];
DDd2 := [ [ a[i,1] : i in [1..#a ] ] : a in DDd ];
divs := [ [ DDd1[i][j]*DDd2[i][j] : j in [1..#DDd1[i] ]  ] : i in [1..#DDd1] ];
divs := [ &+a :a in divs ];

H1 := [ psi(a) : a in divs] ;


ZX<x> := PolynomialRing(K) ;
f := x^8 - 8*x^7 + 28*x^6 - 56*x^5 + 52*x^4 + 16*x^3 - 80*x^2 + 64*x - 44 ;
Zu<u> := PolynomialRing(K) ;
s1 := -2*u;
s2 := (-u^7 + 7*u^6 - 21*u^5 + 35*u^4 - 26*u^3 - 6*u^2 - 34*u + 46)/108;
s3 := (u^7 - 7*u^6 + 21*u^5 - 35*u^4 + 26*u^3 + 6*u^2 - 2*u + 26)/18;
s4 := (-u^7 + 7*u^6 - 21*u^5 + 35*u^4 - 26*u^3 - 6*u^2 + 20*u - 26)/9;
s5 := (2*u^7 - 14*u^6 + 42*u^5 - 70*u^4 + 52*u^3 + 12*u^2 - 40*u + 16)/27;



R := Roots(f, K) ;

a := [ [ 1, R[i,1], Evaluate(s1, R[i,1]), Evaluate(s2, R[i,1]), Evaluate(s3, R[i,1]), Evaluate(s4, R[i,1]), Evaluate(s5, R[i,1]) ] : i in [1..8] ] ;
a1 := a;

add := [ [Denominator(b) : b in c] : c in a1] ;
add1 := [ Lcm(b) : b in add] ;
aa := [ [add1[i]*c : c in a1[i]] : i in [1..#a1] ];
aao := [ [ OK ! b : b in c] : c in aa] ;


aaao := [] ;
for i in [1..8] do ;
a1 := aao[i];                                   
a1 := [ Eltseq(b) : b in a1] ;
a1 := [ [Integers() ! c : c in b ] : b in a1];
ga1 := [ GCD(b) : b in a1];
ga1 := [ Integers() ! b : b in ga1] ;
g := GCD(ga1) ;
aa1 := [ [b/g : b in c] : c in a1];
aa1 := [ [ Integers() ! b : b in c] : c in aa1];
aa1 := [ OK ! b : b in aa1];
aaao[i] := aa1;
end for;


aa37 := [ [pi(b) : b in c] : c in aaao] ;

Zxyz<x,y,z> := PolynomialRing(F37,3) ;

Zxyz<x,y,z> := PolynomialRing(F37,3) ;
a := aa37 ;                                                        
Cubics := [ -b[1]*y^2*z + b[2]*x*y*z + b[3]*y*z^2 + b[4]*x^3 + b[5]*x^2*z + \
b[6]*x*z^2 + b[7]*z^3 : b in a];

Cubics2 := [ Evaluate(s, [FX37.1, FX37.2, 1]) : s in Cubics] ;
D := [ Divisor(c) : c in Cubics2];
DDd := [ Decomposition(a) : a in D ];
DDd1 := [ [ a[i,2] : i in [1..#a] ] :  a in DDd ];
DDd1 := [ [ 1/3*b : b in a ] : a in DDd1 ];
DDd1 := [ [ Integers() ! b : b in a ] : a in DDd1 ];
DDd2 := [ [ a[i,1] : i in [1..#a ] ] : a in DDd ];
divs := [ [ DDd1[i][j]*DDd2[i][j] : j in [1..#DDd1[i] ]  ] : i in [1..#DDd1] ];
divs := [ &+a :a in divs ];

H2 := [ psi(a) : a in divs] ;


ZX<x> := PolynomialRing(K) ;
s := x^8 - (1/6)*x^4 - 1/432;
Zu<u> := PolynomialRing(K) ;
s1 := 72*u^6 -14*u^2 ;
R := Roots(s, K) ;

a := [ [ 1, R[i,1], Evaluate(s1, R[i,1])] : i in [1..8] ];
a1 := a ;
add := [ [Denominator(b) : b in c] : c in a1] ;
add1 := [ Lcm(b) : b in add] ;
aa := [ [add1[i]*c : c in a1[i]] : i in [1..#a1] ];
aao := [ [ OK ! b : b in c] : c in aa] ;


aaao := [] ;
for i in [1..8] do ;
a1 := aao[i];                                   
a1 := [ Eltseq(b) : b in a1] ;
a1 := [ [Integers() ! c : c in b ] : b in a1];
ga1 := [ GCD(b) : b in a1];
ga1 := [ Integers() ! b : b in ga1] ;
g := GCD(ga1) ;
aa1 := [ [b/g : b in c] : c in a1];
aa1 := [ [ Integers() ! b : b in c] : c in aa1];
aa1 := [ OK ! b : b in aa1];
aaao[i] := aa1;
end for;


aa37 := [ [pi(b) : b in c] : c in aaao] ;

Zxyz<x,y,z> := PolynomialRing(F37,3) ;

Zxyz<x,y,z> := PolynomialRing(F37,3) ;
a := aa37 ;                            

Cubics := [ -b[1]*y*z + b[2]*x^2 + b[3]*z^2 : b in a];

Cubics2 := [ Evaluate(s, [FX37.1, FX37.2, 1]) : s in Cubics] ;



D := [ Divisor(c) : c in Cubics2];
DDd := [ Decomposition(a) : a in D ];
DDd1 := [ [ a[i,2] : i in [1..#a] ] :  a in DDd ];
DDd1 := [ [ 1/3*b : b in a ] : a in DDd1 ];
DDd1 := [ [ Integers() ! b : b in a ] : a in DDd1 ];
DDd2 := [ [ a[i,1] : i in [1..#a ] ] : a in DDd ];
divs := [ [ DDd1[i][j]*DDd2[i][j] : j in [1..#DDd1[i] ]  ] : i in [1..#DDd1] ];
divs := [ &+a :a in divs ];

H3 := [ psi(a) : a in divs] ;


H := H1 cat H2 cat H3;
ZN := FreeAbelianGroup(#H) ;
hh := hom< ZN -> J37 | [ a : a in H ] >;
ihh := Image(hh) ;

assert #ihh eq 3^6 ;
print "The 3 orbits generate the entire 3-torsion subgroup";
