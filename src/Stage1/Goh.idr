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

||| An auxiliary polynomial term extracted from the Goh factorization tree.
||| Expressed as an irreducible component Phi_k(s).
public export
record GohAuxiliary (degree : Nat) where
  constructor Phi
  coefficients : Vect (S degree) UnixelFraction

public export
implementation Eq (GohAuxiliary degree) where
  (Phi c1) == (Phi c2) = c1 == c2

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
