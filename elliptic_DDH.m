/* This code accompanies the paper ''Breaking the decisional Diffie-Hellman problem 
for class group actions using genus theory: extended version'' by Wouter Castryck,
Jana Sotáková and Frederik Vercauteren.
*/

// Returns factors with multiplicity up to bound B

function SimpleTrialDivision(a, B)
  facs := TrialDivision(a, B);
  if (#facs gt 0 and facs[#facs][1] gt B) then  
     // removing last factor if too large
     Remove(~facs, #facs);
  end if;
  return facs;
end function;

// The next four functions allow us to walk to the floor
// They also return the distance to the floor

function OnFloor(E, m, numpts)
  v := Valuation(numpts, m);
  onfloor := false;
  for i in [1..80] do
    if m^(v-1)*(numpts div m^v)*Random(E) ne E ! 0 then
      onfloor := true;
      break i;
    end if;
  end for;
  return onfloor;
end function;

// Random point of order m whose Weil pairing with Q is 
// non-trivial assumes m-torsion is fully rational

function FindIndependentOrdermPoint(E, Q, m)
  Fq := BaseField(E);
  R<X> := PolynomialRing(Fq);
  coeffs := Eltseq(E);
  defpol := X^3 + coeffs[2]*X^2 + coeffs[4]*X + coeffs[5];
  xcoords := [rt[1] : rt in Roots(DivisionPolynomial(E,m))];
  repeat
    x := Random(xcoords);
    y := Sqrt(Evaluate(defpol,x));
    P := E ! [x,y,1];
  until WeilPairing(P,Q,m) ne 1;
  return P;
end function;

// Random point of order m

function FindOrdermPoint(E, m) 
  Fq := BaseField(E);
  R<X> := PolynomialRing(Fq);
  coeffs := Eltseq(E);
  defpol := X^3 + coeffs[2]*X^2 + coeffs[4]*X + coeffs[5];
  xcoords := [rt[1] : rt in Roots(DivisionPolynomial(E,m))];
  x := Random(xcoords);
  y := Sqrt(Evaluate(defpol,x));
  return E ! [x,y,1];
end function;

// Walking to the floor of the volcano
// Returns height and distance to the floor
// Assumes existence of point of order m

function ToFloor(E, m, numpts)
  Fq := BaseField(E);
  q := #Fq;
  t := q + 1 - numpts;
  disc_frob := t^2 - 4*q;
  h := Floor(Valuation(disc_frob,m)/2); // height of the volcano
  if m eq 2 and (disc_frob div 4^h) mod 4 in {2,3} then 
     h -:= 1; 
  end if;
  if OnFloor(E, m, numpts) then
    return E, h, 0;
  else
    R<X> := PolynomialRing(Fq);
    repeat
      pathtofloor := 0;
      Efloor := E;
      Q := FindOrdermPoint(Efloor, m);
      repeat
        P := FindIndependentOrdermPoint(Efloor, Q, m);
        if m eq 2 then
          Efloor, phi := IsogenyFromKernel(Efloor, X - P[1]);
        else
          Efloor, phi := IsogenyFromKernel(Efloor, &*[X - (i*P)[1] : i in [1..(m-1) div 2]]);
        end if;
        Q := phi(Q);
        pathtofloor +:= 1;
      until pathtofloor gt h or OnFloor(Efloor, m, numpts);
    until pathtofloor le h; // otherwise we passed through surface
    return Efloor, h, pathtofloor;
  end if;
end function;

// Computes minimal extension such that m-torsion is rational
// Returns extension degree and number of points over extension

function MinimalExtensionmTorsion(m, p, numpts)
  t := p+1-numpts;
  Ts := [t, t^2 - 2*p];
  Ns := [numpts, p^2 + 1 - Ts[2]];
  for i := 3 to m-1 do
    Append(~Ts, t*Ts[i-1] - p*Ts[i-2]);
  end for;
  for d in Divisors(m-1) do
    if (Valuation(p^d + 1 - Ts[d], m) ge 1) then
	   return d, p^d + 1 - Ts[d];
	end if;
  end for;
  return 0, 0;
end function;

// Listing available characters smaller than bound B
// Odd primes m appearing in t^2 - 4*p to an even power, 
// or for which we need to go to a large extension to see 
// some m-torsion are currently ignored.

function ListCharacters(E, B, numpts)

  p := #BaseField(E);
  t := p+1-numpts;
  disc_frob := t^2 - 4*p;

  factors := SimpleTrialDivision(disc_frob, B);

  even_chars := [];
  odd_chars := [];
  for fac in factors do
    if fac[1] ne 2 then
      if IsOdd(fac[2]) then // prime definitely divides Delta_O
        m := fac[1];
        if (MinimalExtensionmTorsion(m, p, numpts) lt 50) then
          odd_chars cat:= [m];
        end if;
      end if;
    else
      ext, numpts_ext := MinimalExtensionmTorsion(2, p, numpts);
      q := p^ext;
      Fq := GF(p, ext);
      E_ext := BaseChange(E, Fq);
      _, h, pathtofloor := ToFloor(E_ext, 2, numpts_ext);
      real_disc := disc_frob div 4^pathtofloor; // locally around 2, but enough
      if IsEven(real_disc) then
        if (-real_disc div 4) mod 4 le 1 then
          even_chars := ["delta"];
        end if;
        case (-real_disc div 4) mod 8:
          when 0, 6: Append(~even_chars, "epsilon");
          when 2: Append(~even_chars, "delta*epsilon");
        end case;
      end if;
    end if;
  end for;

  return even_chars, odd_chars;
end function;

// This function computes characters associated to odd prime

function ComputeOddCharacter(m, E, Eisog, numpts)

  print "Computing character associated with odd prime m =", m;

  p := #BaseField(E);
  t := p+1-numpts;

  ext, numpts_ext := MinimalExtensionmTorsion(m, p, numpts);
  v := Valuation(numpts_ext, m);
  q := p^ext;
  print "    (constructing field Fq of degree", ext,"over Fp)";
  Fq := GF(p, ext);

  Tm := [];
  if v eq 1 then
    print "    Base case using self-pairing";
    for ell_curve in [E, Eisog] do
      ell_ext := BaseChange(ell_curve, Fq);
      repeat
        P := (numpts_ext div m)*Random(ell_ext);
      until P ne ell_ext ! 0;
      Tm cat:= [TatePairing(P,P,m)^((q-1) div m)];
    end for;
  else
    for ell_curve in [E, Eisog] do
      ell_ext := BaseChange(ell_curve, Fq);
	  print "	Walking to floor...";
      Efloor, h := ToFloor(ell_ext, m, numpts_ext);
	  print "	Heigth of volcano is ", h;
      repeat
        P := (numpts_ext div m)*Random(Efloor);
      until P ne Efloor ! 0;
      repeat
        Q := (numpts_ext div m^v)*Random(Efloor);
      until m^(v-1)*Q eq P;
      Tm cat:= [TatePairing(P,Q,m)^((q - 1) div m)];
    end for;
  end if;

  // Computing discrete log naively

  for expo in [1..m-1] do
    if Tm[2] eq Tm[1]^expo then
      return LegendreSymbol(expo, m);
    end if;
  end for;

  return 0;

end function;

// This procedure computes characters associated to prime 2

function ComputeEvenCharacters(even_chars, E, Eisog, numpts)

  print "Computing characters associated with m = 2:";

  p := #BaseField(E);
  t := p+1-numpts;
  S<X> := PolynomialRing(Integers());

  ext := 0;
  repeat
    ext +:= 1;
    numpts_ext := Resultant(1 - X^ext, X^2 - t*X + p);
    v := Valuation(numpts_ext, 2);
    q := p^ext;
  until q mod 8 eq 1 and v ge 3; // v ge 2 would have sufficed for delta
  q := p^ext;
  print "    Constructing field Fq of degree", ext,"over Fp";
  Fq := GF(p, ext);

  T8 := [];

  for ell_curve in [E, Eisog] do
    ell_ext := BaseChange(ell_curve, Fq);
	print "    Walking to floor..."; 
    Efloor, h := ToFloor(ell_ext, 2, numpts_ext);
	print "    Heigth of volcano is ", h;
    repeat
      P := (numpts_ext div 2^3)*Random(Efloor);
    until 4*P ne Efloor ! 0;
    repeat
      Q := (numpts_ext div 2^v)*Random(Efloor);
    until 2^(v-3)*Q eq P;
    T8 cat:= [TatePairing(P,Q,8)^((q-1) div 8)];
  end for;

  for e in [1,3,5,7] do
    if T8[2] eq T8[1]^e then
      expo := e;
    end if;
  end for;

  delta := (-1)^((expo - 1) div 2);
  epsilon := (-1)^((expo^2 - 1) div 8);
  result := [];
  for char in even_chars do
    case char:
      when "delta": Append(~result, delta);
      when "epsilon": Append(~result, epsilon);
      when "delta*epsilon": Append(~result, delta*epsilon);
    end case;
  end for;

  return result;
end function;

// Computes character delta for supersingular curve 
// over F_p with p = 1 mod 4

function ComputeSuperingularDelta(E, Eisog)

  Fpx<x> := PolynomialRing(BaseField(E));
  Ew := WeierstrassModel(E);
  Eisogw := WeierstrassModel(Eisog);
  a := Coefficients(Ew)[4];
  r := Roots(x^3 + Fpx ! Reverse(Coefficients(Ew)), BaseField(E))[1][1];
  aiso := Coefficients(Eisogw)[4];
  riso := Roots(x^3 + Fpx ! Reverse(Coefficients(Eisogw)), BaseField(E))[1][1];
  
  char := ((aiso + 3*riso^2)/(a + 3*r^2))^((#BaseField(E) - 1) div 4);
  if (char ne 1) then char := -1; end if;
  
  return char;

end function;

// Computes even character given degree ell

function ComputeEvenChar(cha, ell)
  case cha:
    when "delta": return (-1)^((ell-1) div 2);
    when "epsilon": return (-1)^((ell^2-1) div 8);
    when "delta*epsilon": return (-1)^( ((ell-1) div 2) + ((ell^2-1) div 8));
  end case;
  return 0;
end function;

// Defining Kieffer-de Feo-Smith example

p := 120373407382088450343833839782228011370920294512701979\
23071397735408251586669938291587857560356890516069961904754\
171956588530344066457839297755929645858769;
A := 1086133850464928038385995014077294700770364640837283193\
432466056688873279777893214248825356514560367259194460221057\
1423767689240032829444439469242521864171;
ell := 523;
N := 1203734073820884503438338397822280113709202945127019792\
307139773540825158667008548113803008846179093820187417165277\
1344144043268298219947026188471598838060;
Fp := GF(p);
R<x> := PolynomialRing(Fp);
E := EllipticCurve([0, Fp ! A, 0, 1, 0]);

// constructing isogeneous curve
  
repeat 
  P := (N div ell)*Random(E);
until (P ne E ! 0);
Eisog := IsogenyFromKernel(E, &*[x - (i*P)[1] : i in [1..Floor(ell/2)]]);
even_chars, odd_chars := ListCharacters(E, 1000, N);  // bound 1000 on character

if #even_chars ne 0 then
  r_even := ComputeEvenCharacters(even_chars, E, Eisog, N);
  ind := 0;
  for char in even_chars do
    ind := ind+1;
	print "Computed char ", char, " = ", r_even[ind], "vs ", char, " = ", ComputeEvenChar(char, ell);
  end for;
end if;

for m in odd_chars do
  char_m := ComputeOddCharacter(m, E, Eisog, N);
  print "Computed char = ", char_m, "vs Leg(ell, m) = ",  LegendreSymbol(ell, m);
end for;
  

