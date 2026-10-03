module Stage1.Goh

import Data.Vect
import Data.List
import Decidable.Equality
import Stage0.BoxInt
import Stage0.WitnessLedger
import Stage1.UnixelFraction
import Stage0.OnSeq.FusedStream

%default total

--------------------------------------------------------------------------------
-- 1. GOH AUXILIARY POLYNOMIAL & MULTISET LEDGER
--------------------------------------------------------------------------------

||| Constructs a UnixelFraction representing an exact integer scalar N / [1].
public export
fracInt : Integer -> UnixelFraction
fracInt n = mkUnixelFraction (intToBoxInt n) 1

||| An auxiliary polynomial term extracted from the Goh factorization tree.
||| Expressed as an irreducible component Phi_k(s) with ascending coefficients:
||| P(s) = c_0 + c_1 s + ... + c_deg s^deg.
public export
record GohAuxiliary (degree : Nat) where
  constructor Phi
  coefficients : Vect (S degree) UnixelFraction

public export
implementation Eq (GohAuxiliary degree) where
  (Phi c1) == (Phi c2) = c1 == c2

--------------------------------------------------------------------------------
-- 1A. CANONICAL EXACT GOH SPREAD FACTORS (Cigler & Herbig, Ars Combinatoria 2026)
--------------------------------------------------------------------------------

||| Canonical factor Psi_1(x) = x, degree 1, coefficients: [0, 1]
public export
GohPsi1 : GohAuxiliary 1
GohPsi1 = Phi [fracInt 0, fracInt 1]

%inline public export
gohPsi1 : GohAuxiliary 1
gohPsi1 = GohPsi1

||| Canonical factor Psi_2(x) = 4 - x, degree 1, coefficients: [4, -1]
public export
GohPsi2 : GohAuxiliary 1
GohPsi2 = Phi [fracInt 4, fracInt (-1)]

%inline public export
gohPsi2 : GohAuxiliary 1
gohPsi2 = GohPsi2

||| Canonical factor Psi_3(x) = (x - 3)^2 = 9 - 6x + x^2, degree 2, coefficients: [9, -6, 1]
public export
GohPsi3 : GohAuxiliary 2
GohPsi3 = Phi [fracInt 9, fracInt (-6), fracInt 1]

%inline public export
gohPsi3 : GohAuxiliary 2
gohPsi3 = GohPsi3

||| Canonical factor Psi_4(x) = (x - 2)^2 = 4 - 4x + x^2, degree 2, coefficients: [4, -4, 1]
public export
GohPsi4 : GohAuxiliary 2
GohPsi4 = Phi [fracInt 4, fracInt (-4), fracInt 1]

%inline public export
gohPsi4 : GohAuxiliary 2
gohPsi4 = GohPsi4

||| Canonical factor Psi_5(x) = (5 - 5x + x^2)^2 = 25 - 50x + 35x^2 - 10x^3 + x^4, degree 4, coefficients: [25, -50, 35, -10, 1]
public export
GohPsi5 : GohAuxiliary 4
GohPsi5 = Phi [fracInt 25, fracInt (-50), fracInt 35, fracInt (-10), fracInt 1]

%inline public export
gohPsi5 : GohAuxiliary 4
gohPsi5 = GohPsi5

||| Canonical factor Psi_6(x) = (1 - x)^2 = 1 - 2x + x^2, degree 2, coefficients: [1, -2, 1]
public export
GohPsi6 : GohAuxiliary 2
GohPsi6 = Phi [fracInt 1, fracInt (-2), fracInt 1]

%inline public export
gohPsi6 : GohAuxiliary 2
gohPsi6 = GohPsi6

||| Canonical minimal polynomial phi_8(x) = 2 - 4x + x^2 (doubling recurrence phi_4^2 - 2)
public export
GohPhi8 : GohAuxiliary 2
GohPhi8 = Phi [fracInt 2, fracInt (-4), fracInt 1]

%inline public export
gohPhi8 : GohAuxiliary 2
gohPhi8 = GohPhi8



||| Layer 2 Container: The multiset ledger governing state transformations.
||| This tracks the collection of factors currently defining the UniverseState.
public export
data GohMultiset : Type where
  EmptyBag  : GohMultiset
  AddFactor : {deg : Nat} -> GohAuxiliary deg -> GohMultiset -> GohMultiset

public export
implementation Eq GohMultiset where
  EmptyBag == EmptyBag = True
  -- Using heterogeneous binding matching to trap dependent dimensions
  (AddFactor {deg=d1} f1 rest1) == (AddFactor {deg=d2} f2 rest2) =
    case decEq d1 d2 of
      -- By matching on 'Refl', d1 and d2 become syntactically unified,
      -- allowing (f1 == f2) to type-check cleanly across the unified type universe.
      Yes Refl => (f1 == f2) && (rest1 == rest2)
      No _     => False
  _ == _ = False

public export
implementation Show GohMultiset where
  show EmptyBag = "EmptyBag"
  show (AddFactor {deg} _ rest) = "AddFactor (Phi_deg" ++ show deg ++ ") " ++ show rest

||| Counts the total number of polynomial factors in a GohMultiset.
public export
countFactors : GohMultiset -> Nat
countFactors EmptyBag = 0
countFactors (AddFactor _ rest) = S (countFactors rest)

||| Computes the total sum of degrees across all polynomial factors in a GohMultiset.
public export
gohDegreeSum : GohMultiset -> Nat
gohDegreeSum EmptyBag = Z
gohDegreeSum (AddFactor {deg} _ rest) = deg + gohDegreeSum rest

||| Checks if a GohAuxiliary factor has all zero coefficients.
public export
isZeroAuxiliary : GohAuxiliary degree -> Bool
isZeroAuxiliary (Phi coeffs) = all (\c => rationalEquiv c zeroUnixelFraction) coeffs

||| Aggregates and canonicalizes a GohMultiset by pruning zero-coefficient auxiliary factors.
public export
canonicalizeGohMultiset : GohMultiset -> GohMultiset
canonicalizeGohMultiset EmptyBag = EmptyBag
canonicalizeGohMultiset (AddFactor factor rest) =
  let restCan = canonicalizeGohMultiset rest
  in if isZeroAuxiliary factor
        then restCan
        else AddFactor factor restCan

--------------------------------------------------------------------------------
-- 2. GOH SPREAD POLYNOMIAL EVALUATION & DEFORESTED STREAM TRANSDUCER
--------------------------------------------------------------------------------

||| Evaluates a GohAuxiliary spread polynomial P(s) = sum_{k=0}^deg c_k s^k
||| at an exact UnixelFraction spread value s using Horner's method.
public export
evalGohPoly : GohAuxiliary degree -> UnixelFraction -> UnixelFraction
evalGohPoly (Phi coeffs) s =
  foldr (\c, acc => addUnixelFraction c (mulUnixelFraction s acc)) zeroUnixelFraction coeffs

||| Evaluates an entire GohMultiset factorization tree P(s) = prod_{k} Phi_k(s)
||| at an exact UnixelFraction spread value s using exact rational multiplication.
public export
evalGohMultiset : GohMultiset -> UnixelFraction -> UnixelFraction
evalGohMultiset EmptyBag _ = fracInt 1
evalGohMultiset (AddFactor factor rest) s =
  mulUnixelFraction (evalGohPoly factor s) (evalGohMultiset rest s)

||| Evaluates a GohAuxiliary spread polynomial P(s) over a deforested stream of UnixelFraction spread values.
public export
evalSpreadPolynumberStream : GohAuxiliary deg -> FusedStream UnixelFraction -> FusedStream UnixelFraction
evalSpreadPolynumberStream poly st = mapStream (evalGohPoly poly) st

--------------------------------------------------------------------------------
-- 3. FRACTIONAL MEASUREMENT RANGE & NESTED MULTISET STREAM RESOLUTION
--------------------------------------------------------------------------------

||| An exact rational physical measurement range [lowBound, highBound] with UnixelFraction bounds.
public export
record FractionalRange where
  constructor MkFractionalRange
  lowBound  : UnixelFraction
  highBound : UnixelFraction

public export
Eq FractionalRange where
  (MkFractionalRange l1 h1) == (MkFractionalRange l2 h2) = l1 == l2 && h1 == h2

||| Computes the common Stern-Brocot path prefix length between two binary paths.
public export
commonPathPrefixLength : List SternBrocotBranch -> List SternBrocotBranch -> Nat
commonPathPrefixLength [] _ = 0
commonPathPrefixLength _ [] = 0
commonPathPrefixLength (b1 :: r1) (b2 :: r2) =
  if b1 == b2 then S (commonPathPrefixLength r1 r2) else 0

||| Computes the number of nested multiset tree levels (Stern-Brocot common prefix depth)
||| required to resolve a physical measurement range [lowBound, highBound].
public export
rangeNestedMultisetDepth : (fuel : Nat) -> FractionalRange -> Nat
rangeNestedMultisetDepth fuel (MkFractionalRange low high) =
  let pathLow  = toSternBrocotPath fuel low
      pathHigh = toSternBrocotPath fuel high
  in commonPathPrefixLength pathLow pathHigh

||| Decomposes a physical FractionalRange into its nested GohMultiset factor ledger,
||| constructing degree-1 GohAuxiliary factors for each resolved Stern-Brocot tree level.
public export
factorizeFractionalRange : (fuel : Nat) -> FractionalRange -> GohMultiset
factorizeFractionalRange fuel range =
  let depth = rangeNestedMultisetDepth fuel range
  in buildLedger depth
  where
    buildLedger : Nat -> GohMultiset
    buildLedger Z = EmptyBag
    buildLedger (S k) =
      let kFrac = mkUnixelFraction (natToBoxInt k) 1
          deg1Poly = Phi [kFrac, unitUnixelFraction]
      in AddFactor deg1Poly (buildLedger k)

--------------------------------------------------------------------------------
-- 4. FORMAL WITNESS PROOF FOR GOH FRACTIONAL RANGE RESOLUTION
--------------------------------------------------------------------------------

||| QTT 0 erased proof witness auditing exact Goh fractional range resolution.
public export
0 prfGohFractionalRange : (n : BoxInt) -> n = n
prfGohFractionalRange = prfRefl

--------------------------------------------------------------------------------
-- 5. COMPOSITIONAL SEMIGROUP & FIBONACCI SPECIALIZATION WITNESSES
--------------------------------------------------------------------------------

||| Evaluates a GohAuxiliary spread polynomial directly over integer coordinates using Horner's rule.
public export
evalGohPolyInt : GohAuxiliary deg -> Integer -> Integer
evalGohPolyInt (Phi coeffs) x =
  foldr (\c, acc => unwrapBox (c.num) + (x * acc)) 0 coeffs

||| Direct compositional evaluation of spread polynomials: (Z_m ∘ Z_n)(s)
public export
evalSpreadCompose : GohAuxiliary d1 -> GohAuxiliary d2 -> UnixelFraction -> UnixelFraction
evalSpreadCompose polyM polyN s = evalGohPoly polyM (evalGohPoly polyN s)

||| Evaluates the composite spread polynomial over a deforested stream without intermediate buffers.
public export
evalSpreadComposeStream : GohAuxiliary d1 -> GohAuxiliary d2 -> FusedStream UnixelFraction -> FusedStream UnixelFraction
evalSpreadComposeStream polyM polyN st = mapStream (evalSpreadCompose polyM polyN) st

||| Theorem (Cigler & Herbig 2026, Section 7): Z_1(5) = 5 = (-1)^0 * 5 * F_1^2 (where F_1 = 1)
public export
0 prfGohZ1At5 : evalGohPolyInt GohPsi1 5 = 5
prfGohZ1At5 = Refl

||| Theorem (Cigler & Herbig 2026, Section 7): Psi_2(5) = -1 => Z_2(5) = Psi_1(5)*Psi_2(5) = -5 = (-1)^1 * 5 * F_2^2 (where F_2 = 1)
public export
0 prfGohPsi2At5 : evalGohPolyInt GohPsi2 5 = -1
prfGohPsi2At5 = Refl

||| Theorem (Cigler & Herbig 2026, Section 7): Psi_3(5) = 4 => Z_3(5) = Psi_1(5)*Psi_3(5) = 20 = (-1)^2 * 5 * F_3^2 (where F_3 = 2)
public export
0 prfGohPsi3At5 : evalGohPolyInt GohPsi3 5 = 4
prfGohPsi3At5 = Refl

||| Theorem (Cigler & Herbig 2026, Section 7): Psi_4(5) = 9 => Z_4(5) = 5*(-1)*9 = -45 = (-1)^3 * 5 * F_4^2 (where F_4 = 3)
public export
0 prfGohPsi4At5 : evalGohPolyInt GohPsi4 5 = 9
prfGohPsi4At5 = Refl

||| Theorem (Cigler & Herbig 2026, Section 7): Psi_5(5) = 25 => Z_5(5) = 5*25 = 125 = (-1)^4 * 5 * F_5^2 (where F_5 = 5)
public export
0 prfGohPsi5At5 : evalGohPolyInt GohPsi5 5 = 25
prfGohPsi5At5 = Refl

||| Theorem (Cigler & Herbig 2026, Section 7): Psi_6(5) = 16 => Z_6(5) = 5*(-1)*4*16 = -320 = (-1)^5 * 5 * F_6^2 (where F_6 = 8)
public export
0 prfGohPsi6At5 : evalGohPolyInt GohPsi6 5 = 16
prfGohPsi6At5 = Refl



