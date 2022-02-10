/* This code accompanies the paper ''Breaking the decisional Diffie-Hellman problem 
for class group actions using genus theory: extended version'' by Wouter Castryck,
Jana Sotáková and Frederik Vercauteren.
*/

// Functions to list all quadratic splittings of
// f and taking a (2,2)-step along a random such
// splitting

function QuadraticSplittings(f);
  quadsplits := {};
  facs := [fac[1] : fac in Factorization(f)];
  linfacs := {};
  quadfacs := {};
  for fac in facs do
    if Degree(fac) eq 1 then linfacs join:= {fac}; end if;
    if Degree(fac) eq 2 then quadfacs join:= {fac}; end if;
  end for; // note: #linfacs + 2*#quadfacs = 6
  if IsEmpty(linfacs) then
    quadsplits join:= {quadfacs};
  else
    for S1 in Subsets(linfacs, 2) do
      fac1 := &*S1;
      remS1 := linfacs diff S1;
      if IsEmpty(remS1) then
        quadsplits join:= {{fac1} join quadfacs};
      else
        for S2 in Subsets(remS1, 2) do
          fac2 := &*S2; 
          remS2 := remS1 diff S2;
          if IsEmpty(remS2) then
            quadsplits join:= {{fac1, fac2} join quadfacs};
          else
            fac3 := &*remS2;
            quadsplits join:= {{fac1, fac2, fac3}};
          end if;
        end for;
      end if;
    end for;
  end if;
  quadsplitsarr := [];
  for quadsplit in quadsplits do
    quadsplitarr := SetToSequence(quadsplit);
    quadsplitarr[1] *:= LeadingCoefficient(f);
    quadsplitsarr cat:= [quadsplitarr];
  end for;
  return quadsplitsarr;
end function;

function RandomRichelot(f);
  splitting := Random(QuadraticSplittings(f));
  G1 := splitting[1];
  G2 := splitting[2];
  G3 := splitting[3];
  delta := Matrix(BaseRing(Parent(f)), 3, 3, 
    Eltseq(G1) cat Eltseq(G2) cat Eltseq(G3));
  delta := Determinant(delta);
  H1 := delta^(-1)*(Derivative(G2)*G3 - G2*Derivative(G3));
  H2 := delta^(-1)*(Derivative(G3)*G1 - G3*Derivative(G1));
  H3 := delta^(-1)*(Derivative(G1)*G2 - G1*Derivative(G2));
  return H1*H2*H3;
end function;

// Functions to check whether there is a uniqe
// 3-torsion point up to sign, and to compute
// the self-pairing of this 3-torsion point

function CheckSimple3(f)
  F := BaseRing(Parent(f));
  AA7 := AffineSpace(F, 7);
  R<b1,b2,b3,b4,b5,b6,b7> := CoordinateRing(AA7);
  S<x> := PolynomialRing(R);
  coeffpoly := (b4*x^3 + b3*x^2 + b2*x + b1)^2 + b7*(x^2 + b5*x + b6)^3 - (S ! f); 
  S := Scheme(AA7, Coefficients(coeffpoly));
  pts := Points(S);
  return #pts eq 2;
end function;

function Tate3(f);
  F := BaseRing(Parent(f));
  AA7 := AffineSpace(F, 7);
  R<b1,b2,b3,b4,b5,b6,b7> := CoordinateRing(AA7);
  S<x> := PolynomialRing(R);
  coeffpoly := 
    (b4*x^3 + b3*x^2 + b2*x + b1)^2 + b7*(x^2 + b5*x + b6)^3 - (S ! f);
  S := Scheme(AA7, Coefficients(coeffpoly));
  pts := Points(S);
  B1 := pts[1];
  B2 := pts[2];
  S<x> := Parent(f);
  G1 := B1[4]*x^3 + B1[3]*x^2 + B1[2]*x + B1[1];
  H1 := x^2 + B1[5]*x + B1[6];
  lambda1 := B1[7];
  G2 := B2[4]*x^3 + B2[3]*x^2 + B2[2]*x + B2[1];
  H2 := x^2 + B2[5]*x + B2[6];
  lambda2 := B2[7];
  pairing12 := Resultant(G1 - G2, H2)/lambda1;
  return 1/pairing12;
end function;

// Find p = 1 mod 6 of size about approxp along
// with a genus-2 curve as in Section 6.5. Fix
// chain length r

approxp := 2^60;
p := approxp; repeat p := NextPrime(p); until p mod 3 eq 1;
exp := (p-1) div 3;
Fp := GF(p); R<x> := PolynomialRing(Fp);
repeat
  f := &*[x - Random(Fp) : i in [1..6]];
until CheckSimple3(f) and Tate3(f)^exp ne 1;

r := 100;

// The following loop shows how the Tate pairings
// alternate between the two primitive third roots
// of unity in Fp as we walk along our (2,2)-path.

previous_tate := Tate3(f)^exp;
print "Initial 3-Tate pairing :", previous_tate;
for i in [1..r] do
  f := RandomRichelot(f);
  tate := Tate3(f)^exp;
  print "3-Tate pairing at iteration", i, ":", tate;
  if tate eq previous_tate then 
    print "ALERT!"; 
    break; 
  else 
    previous_tate := tate; 
  end if;
end for;
