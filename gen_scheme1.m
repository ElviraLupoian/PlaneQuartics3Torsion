Ra<a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5> := PolynomialRing(Rationals(), 11);
Rx<x> := PolynomialRing(Ra);
Ry<y> := PolynomialRing(Rx);

f := x^3*y + y^3 + x;

g := a1*x*y + a2*y + a3*x^3 + a4*x^2 + a5*x + a6;

red_f := f - Coefficient(f, 3) * y * (y^2 - g);
red_f := red_f - Coefficient(red_f, 2) * (y^2 - g);

h1 := Coefficient(red_f, 0);
h2 := Coefficient(red_f, 1);
R := Resultant(h1, h2);
locus := Rx ! (Evaluate(y^2 - g, -h1 / h2) * h2^2);

cubes := b1 * (x^3 + b2*x^2 + b3*x + b4)^3;
eqns := [];
for i := 0 to 9 do
	Append(~eqns, Coefficient(locus, i) + Coefficient(cubes, i));
end for;

Append(~eqns, R * b5 + 1);
