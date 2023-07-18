// this is a set of equations parametrizing 3-torsion points on the Jacobian of>
// y^3*z - x^4 - z^4  = 0 //

Za<[a]> := PolynomialRing(Rationals(),10) ;
Zxy<x,y> := PolynomialRing(Za,2) ;
f := y^3 - x^4 -1 ;
l := y^2 + a[1]*x*y + a[2]*y - a[3]*x^3 - a[4]*x^2 -a[5]*x - a[6] ;
F1 := -y*(a[1]*x*y + a[2]*y - a[3]*x^3 - a[4]*x^2 -a[5]*x - a[6]) - x^4 -1;
t :=  - ( l - y^2 ) ;

F2 := F1 - MonomialCoefficient(F1, y^2)*y^2  -  MonomialCoefficient(F1, y^2)*( >


ZX<X> := PolynomialRing(Za,1) ;
ZY<Y>  := PolynomialRing(ZX,1) ;
F := Evaluate(F2, [X,Y]) ;
C := Coefficients(F);
c1 := C[1] ;
c2 := C[2] ;

R := Resultant(c1,c2, 1);

ZXY<X,Y> := FunctionField(Za, 2) ;
f := Y^3 - X^4 -1 ;
L := Y^2 + a[1]*X*Y + a[2]*Y - a[3]*X^3 - a[4]*X^2 -a[5]*X - a[6] ;
c2 := -X^4 + (-a[1]*a[3] - a[2]*a[3])*X^3 + (-a[1]*a[4] - a[2]*a[4])*X^2 + (-a[>
c1 := a[3]*X^3 + a[4]*X^2 + (a[1]^2 + a[1]*a[2] + a[5])*X + a[1]*a[2] + a[2]^2 >
t := -c2/c1;

FF := Evaluate(L, [ X, t] ) ;
NF := Numerator(FF) ;
t := -a[3]^3*(X^3 + a[7]*X^2 + a[8]*X + a[9])^3;
G := NF - t ;
CG := Coefficients(Numerator(G)) ;

EQNS := CG cat [ R ] ;
EQNS;
