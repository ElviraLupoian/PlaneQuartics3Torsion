// we compute the wild conductor exponent at 2 of the Fermat quartic

load "FermatQuartic3TorsionSubgroup.m";

Q2 := pAdicField(2, 500) ;
Zx<x> := PolynomialRing(Q2) ;
f := x^32 - 8*x^31 + 28*x^30 - 64*x^29 + 130*x^28 - 216*x^27 + 120*x^26 + 42\
0*x^25 - 1058*x^24 + 1032*x^23 - 516*x^22 - 128*x^21 + 3494*x^20 - 15256*x^19 \
+ 39888*x^18 - 76812*x^17 + 119719*x^16 - 158376*x^15 + 182304*x^14 - 185360*x\
^13 + 168338*x^12 - 137584*x^11 + 101508*x^10 - 67596*x^9 + 40588*x^8 - 21912*\
x^7 + 10536*x^6 - 4440*x^5 + 1612*x^4 - 488*x^3 + 112*x^2 - 16*x + 1;
L := LocalField(Q2,f) ;


G,a,b := AutomorphismGroup(L) ;

s1 := G.4 ;
s2 := G.5;
s3 := G.6;
s4 := G.3 ; 
s5 := G.2;

GG := sub<G | s1, s2, s3, s4,s5>;

assert G eq GG ;


G0 := RamificationGroup(L, 0) ;
G1 := RamificationGroup(L,1) ;
G2 := RamificationGroup(L,2) ;
G3 := RamificationGroup(L,3) ;
G4 := RamificationGroup(L,4) ;
G5 := RamificationGroup(L,5) ;
G6 := RamificationGroup(L,6) ;
G7 := RamificationGroup(L,7) ;
G8 := RamificationGroup(L,8) ;

assert #G8 eq 1;



GG0 := sub< G | s1, s2, s4, s5>;


assert GG0 eq G0 ;
assert  G0 eq G1 ;

GG2 := sub<G | s4, s5> ;
assert GG2 eq G2 ;
assert G2 eq G3 ;

GG4 := sub<G | s5> ;
assert GG4 eq G4 ;
assert G4 eq G5 ;
assert G5 eq G6 ;
assert G6 eq G7 ;


s1 := a(s1) ;
s2 := a(s2) ;
s4 := a(s4) ;
s5 := a(s5) ;


// we compute the Galois action of the generators on roots of the polynomials 

Zx<x> := PolynomialRing(Rationals()) ;
f := x^32 - 8*x^31 + 28*x^30 - 64*x^29 + 130*x^28 - 216*x^27 + 120*x^26 + 420*x^25 - 1058*x^24 + 1032*x^23 - 516*x^22 - 128*x^21 + 3494*x^20 - 15256*x^19 + 39888*x^18 - 76812*x^17 + 119719*x^16 - 158376*x^15 + 182304*x^14 - 185360*x^13 + 168338*x^12 - 137584*x^11 + 101508*x^10 - 67596*x^9 + 40588*x^8 - 21912*x^7 + 10536*x^6 - 4440*x^5 + 1612*x^4 - 488*x^3 + 112*x^2 - 16*x + 1;
 K := NumberField(f) ;

f1 := x^8 - 72*x^4 -432;
RR1 := Roots(f1,K) ;
RR1 := [ a[1] : a in RR1 ];
RR1 := [Eltseq(a) : a in RR1] ;
RR1 := [ &+[ a[i]*L.1^(i-1) : i in [1..32] ] : a in RR1 ];

R1 := Roots(f1, L) ;
R1 := [ a : a in R1];
R1 := [ a[1] : a in R1];
 
// permutation taking roots/L to roots/K 


RootsPerm := [ [ [i,Valuation(RR1[i] - R1[j])] : i in [1..8] ] : j in [1..8]];
perm1LK := [] ;

for i in [1..8] do ;                     
t := RootsPerm[i] ;
mt := Max([a[2] : a in t ] ) ;
d := [ j : j in [1..8] | t[j][2] eq mt ];
perm1LK[i] := d[1] ;
end for ;


// action of s1 on roots R1 


RootsPerm := [ [ [i,Valuation(R1[i] - s1(R1[j]))] : i in [1..8] ] : j in [1..8]];
permR1s1:= [] ;

for i in [1..8] do ;                     
t := RootsPerm[i] ;
mt := Max([a[2] : a in t ] ) ;
d := [ j : j in [1..8] | t[j][2] eq mt ];
permR1s1[i] := d[1] ;
end for ;


// action of s2 on roots R1 

RootsPerm := [ [ [i,Valuation(R1[i] - s2(R1[j]))] : i in [1..8] ] : j in [1..8]];
permR1s2:= [] ;

for i in [1..8] do ;                     
t := RootsPerm[i] ;
mt := Max([a[2] : a in t ] ) ;
d := [ j : j in [1..8] | t[j][2] eq mt ];
permR1s2[i] := d[1] ;
end for ;

// action of s4 on roots R1


RootsPerm := [ [ [i,Valuation(R1[i] - s4(R1[j]))] : i in [1..8] ] : j in [1..8]];
permR1s4:= [] ;

for i in [1..8] do ;                     
t := RootsPerm[i] ;
mt := Max([a[2] : a in t ] ) ;
d := [ j : j in [1..8] | t[j][2] eq mt ];
permR1s4[i] := d[1] ;
end for ;


// action of s5 on roots R1 

RootsPerm := [ [ [i,Valuation(R1[i] - s5(R1[j]))] : i in [1..8] ] : j in [1..8]];
permR1s5:= [] ;

for i in [1..8] do ;                     
t := RootsPerm[i] ;
mt := Max([a[2] : a in t ] ) ;
d := [ j : j in [1..8] | t[j][2] eq mt ];
permR1s5[i] := d[1] ;
end for ;



f2 := x^8 -8*x^7 + 28*x^6 -56*x^5 +52*x^4 + 16*x^3 -80*x^2 + 64*x - 44;

RR2 := Roots(f2,K) ;
RR2 := [ a[1] : a in RR2 ];
RR2 := [Eltseq(a) : a in RR2] ;
RR2 := [ &+[ a[i]*L.1^(i-1) : i in [1..32] ] : a in RR2 ];

R2 := Roots(f2, L) ;
R2 := [ a : a in R2];
R2 := [ a[1] : a in R2];



// permutation taking roots/L to roots/K


RootsPerm := [ [ [i,Valuation(RR2[i] - R2[j])] : i in [1..8] ] : j in [1..8]];
perm2LK := [] ;

for i in [1..8] do ;                     
t := RootsPerm[i] ;
mt := Max([a[2] : a in t ] ) ;
d := [ j : j in [1..8] | t[j][2] eq mt ];
perm2LK[i] := d[1] ;
end for ;

perm2LK := [ perm2LK[i] + 8 : i in [1..8] ] ;


// action of s1 on R2 

RootsPerm := [ [ [i,Valuation(R2[i] - s1(R2[j]))] : i in [1..8] ] : j in [1..8]];
permR2s1:= [] ;

for i in [1..8] do ;                     
t := RootsPerm[i] ;
mt := Max([a[2] : a in t ] ) ;
d := [ j : j in [1..8] | t[j][2] eq mt ];
permR2s1[i] := d[1] ;
end for ;

permR2s1 := [ permR2s1[i] + 8 : i in [1..8] ] ; 

// action of s2 on R2 

RootsPerm := [ [ [i,Valuation(R2[i] - s2(R2[j]))] : i in [1..8] ] : j in [1..8]];
permR2s2:= [] ;

for i in [1..8] do ;                     
t := RootsPerm[i] ;
mt := Max([a[2] : a in t ] ) ;
d := [ j : j in [1..8] | t[j][2] eq mt ];
permR2s2[i] := d[1] ;
end for ;

permR2s2 := [ permR2s2[i] + 8 : i in [1..8] ] ; 



// action of s4 on R2 

RootsPerm := [ [ [i,Valuation(R2[i] - s4(R2[j]))] : i in [1..8] ] : j in [1..8]];
permR2s4:= [] ;

for i in [1..8] do ;                     
t := RootsPerm[i] ;
mt := Max([a[2] : a in t ] ) ;
d := [ j : j in [1..8] | t[j][2] eq mt ];
permR2s4[i] := d[1] ;
end for ;

permR2s4 := [ permR2s4[i] + 8 : i in [1..8] ] ; 


// action of s5 on R2 

RootsPerm := [ [ [i,Valuation(R2[i] - s5(R2[j]))] : i in [1..8] ] : j in [1..8]];
permR2s5:= [] ;

for i in [1..8] do ;                     
t := RootsPerm[i] ;
mt := Max([a[2] : a in t ] ) ;
d := [ j : j in [1..8] | t[j][2] eq mt ];
permR2s5[i] := d[1] ;
end for ;

permR2s5 := [ permR2s5[i] + 8 : i in [1..8] ] ; 


f3 := x^8 - (1/6)*x^4 -1/432;

RR3 := Roots(f3,K) ;
RR3 := [ a[1] : a in RR3 ];
RR3 := [Eltseq(a) : a in RR3] ;
RR3 := [ &+[ a[i]*L.1^(i-1) : i in [1..32] ] : a in RR3 ];

R3 := Roots(f3, L) ;
R3 := [ a : a in R3];
R3 := [ a[1] : a in R3];

// permutation taking roots/L to roots/K


RootsPerm := [ [ [i,Valuation(RR3[i] - R3[j])] : i in [1..8] ] : j in [1..8]];
perm3LK := [] ;

for i in [1..8] do ;                     
t := RootsPerm[i] ;
mt := Max([a[2] : a in t ] ) ;
d := [ j : j in [1..8] | t[j][2] eq mt ];
perm3LK[i] := d[1] ;
end for ;

perm3LK := [ perm3LK[i] + 16 : i in [1..8] ] ;


// action of s1 on R3


RootsPerm := [ [ [i,Valuation(R3[i] - s1(R3[j]))] : i in [1..8] ] : j in [1..8]];
permR3s1:= [] ;

for i in [1..8] do ;                     
t := RootsPerm[i] ;
mt := Max([a[2] : a in t ] ) ;
d := [ j : j in [1..8] | t[j][2] eq mt ];
permR3s1[i] := d[1] ;
end for ;


permR3s1 := [ permR3s1[i] + 16 : i in [1..8] ] ; 


// action of s2 on R3


RootsPerm := [ [ [i,Valuation(R3[i] - s2(R3[j]))] : i in [1..8] ] : j in [1..8]];
permR3s2:= [] ;

for i in [1..8] do ;                     
t := RootsPerm[i] ;
mt := Max([a[2] : a in t ] ) ;
d := [ j : j in [1..8] | t[j][2] eq mt ];
permR3s2[i] := d[1] ;
end for ;


permR3s2 := [ permR3s2[i] + 16 : i in [1..8] ] ; 



// action of s4 on R3


RootsPerm := [ [ [i,Valuation(R3[i] - s4(R3[j]))] : i in [1..8] ] : j in [1..8]];
permR3s4:= [] ;

for i in [1..8] do ;                     
t := RootsPerm[i] ;
mt := Max([a[2] : a in t ] ) ;
d := [ j : j in [1..8] | t[j][2] eq mt ];
permR3s4[i] := d[1] ;
end for ;


permR3s4 := [ permR3s4[i] + 16 : i in [1..8] ] ; 


// action of s5 on R3


RootsPerm := [ [ [i,Valuation(R3[i] - s5(R3[j]))] : i in [1..8] ] : j in [1..8]];
permR3s5 := [] ;

for i in [1..8] do ;                     
t := RootsPerm[i] ;
mt := Max([a[2] : a in t ] ) ;
d := [ j : j in [1..8] | t[j][2] eq mt ];
permR3s5[i] := d[1] ;
end for ;


permR3s5 := [ permR3s5[i] + 16 : i in [1..8] ] ; 



// transformation taking roots/L to roots/K

cptLK := perm1LK cat perm2LK cat perm3LK ;

ZcptLK := [ZN.i : i in cptLK ];

conjLK := hom< ZN -> ZN | ZcptLK>;


// we also compute the transformation taking roots/K to root/L (=inverse of the above 

cptKL := [];

for i in [1..24] do ;
t := [ j : j in [1..24] | cptLK[j] eq i ];
cptKL[i] := t[1] ;
end for ;

ZcptKL := [ZN.i : i in cptKL ];

conjKL := hom< ZN -> ZN | ZcptKL >;


// action of s1 

c1 := permR1s1 cat permR2s1 cat permR3s1;

c1 := [ ZN.i : i in c1 ];

conjs1 := hom< ZN -> ZN | c1 >;

// action of s2 

c2 := permR2s1 cat permR2s2 cat permR3s2;

c2 := [ ZN.i : i in c2 ];

conjs2 := hom< ZN -> ZN | c2 >;


// action of s4

c4 := permR1s4 cat permR2s4 cat permR3s4;


c4 := [ ZN.i : i in c4 ];

conjs4 := hom< ZN -> ZN | c4 >;

// action of s5 

c5 := permR1s5 cat permR2s5 cat permR3s5 ;
c5 := [ ZN.i : i in c5] ;

conjs5 := hom< ZN -> ZN | c5 >;


// invariants of s1 

mu := hom< ZN -> J37 | [ hh(ZN.i) - hh(conjLK(conjs1(conjKL(ZN.i)))) : i in [1..24]]>;
ker := Kernel(mu);
K1 := sub<J37 | [hh(k) : k in Generators(ker)]>;


// invariants of s2 


mu := hom< ZN -> J37 | [ hh(ZN.i) - hh(conjLK(conjs2(conjKL(ZN.i)))) : i in [1..24]]>;
ker := Kernel(mu);
K2 := sub<J37 | [hh(k) : k in Generators(ker)]>;


// invariants of s4


mu := hom< ZN -> J37 | [ hh(ZN.i) - hh(conjLK(conjs4(conjKL(ZN.i)))) : i in [1..24]]>;
ker := Kernel(mu);
K4 := sub<J37 | [hh(k) : k in Generators(ker)]>;


// invariants of s5 

mu := hom< ZN -> J37 | [ hh(ZN.i) - hh(conjLK(conjs5(conjKL(ZN.i)))) : i in [1..24]]>;
ker := Kernel(mu);
K5 := sub<J37 | [hh(k) : k in Generators(ker)]>;


// invariants of G0, G1

Inv1 := K1 meet K2 meet K4 meet K5 ;


// invariants of G2, G3 

Inv2 := K4 meet K5 ;


// local conductor exponent at 2
invs := [  #Inv1, #Inv2, #Inv2, #K5, #K5,#K5,#K5,3^6] ;
invs := [ Valuation(invs[i],3) : i in [1..#invs] ] ;
invs := [ 6 - invs[i] : i in [1..#invs] ];
dens := [  #G1, #G2, #G3, #G4, #G5, #G6, #G7, #G8 ] ;

dens := [#G0/ dens[i] : i in [1..#dens] ] ;  
tt := [ invs[i]/dens[i] : i in [1..#dens] ] ;

n2 := &+tt ;

n2;
