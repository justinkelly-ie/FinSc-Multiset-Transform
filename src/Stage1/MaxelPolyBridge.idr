module Stage1.MaxelPolyBridge

import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.StructuralFuel
import Stage0.OnSeq.FusedStream as FS
import Stage0.StreamPolynumber
import Stage1.ConjugateHylo
import Stage1.VexelMaxel as VM
import Stage1.VexelStream as VS
import Stage1.Goh.Factor
import Data.Fuel
import Data.List
import Data.Vect
import Stage1.MultisetTree

%default total

------------------------------------------------------------------------
-- 1. COMPANION MATRIX NATURAL TRANSFORMATION (1D POLY -> 2D MAXEL)
------------------------------------------------------------------------

||| Constructs the 2x2 companion Maxel matrix for a monic quadratic polynomial
||| P(x) = x^2 - c1 * x - c0 = 0.
||| In Wild Linear Algebra, the companion matrix represents the 2D directed step graph:
|||   [ 0   c0 ]
|||   [ 1   c1 ]
||| Active support edges:
||| - [2, 1] (shift edge: S_{n-1} -> S_n, weight 1)
||| - [1, 2] (feedback edge: c0, omitted if c0 == 0)
||| - [2, 2] (self-loop: c1, omitted if c1 == 0)
public export
companionMaxel2D : BoxInt -> BoxInt -> VM.Maxel
companionMaxel2D c0 c1 =
  let baseShift = [(VM.MkPixel 2 1, intToBoxInt 1)]
      c0Edge = if unwrapBox c0 == 0 then [] else [(VM.MkPixel 1 2, c0)]
      c1Edge = if unwrapBox c1 == 0 then [] else [(VM.MkPixel 2 2, c1)]
  in VM.MkMaxel (baseShift ++ c0Edge ++ c1Edge)

||| Natural transformation eta from a quadratic StreamPolynumber to its 2D companion Maxel.
||| Extracts the c0 (degree 0) and c1 (degree 1) coefficients from the sparse stream.
public export
companionMaxelFromPoly : StreamPolynumber -> VM.Maxel
companionMaxelFromPoly p =
  let terms = streamPolyToListNat 5 p
      c0 = case find (\(d, _) => d == 0) terms of
             Just (_, w) => w
             Nothing     => intToBoxInt 0
      c1 = case find (\(d, _) => d == 1) terms of
             Just (_, w) => w
             Nothing     => intToBoxInt 0
  in companionMaxel2D c0 c1

||| Constructs an N-dimensional companion Maxel for monic polynomial
||| P(x) = x^N - sum_{i=0}^{N-1} c_i x^i.
||| Subdiagonal entries [k+2, k+1] have weight 1 for 0 <= k < N-1.
||| Rightmost column entries [k+1, N] have weight coeffs[k] for 0 <= k < N.
public export
companionMaxelND : (n : Nat) -> (coeffs : Vect n BoxInt) -> VM.Maxel
companionMaxelND Z [] = VM.MkMaxel []
companionMaxelND (S Z) [c0] =
  if unwrapBox c0 == 0
     then VM.MkMaxel []
     else VM.MkMaxel [(VM.MkPixel 1 1, c0)]
companionMaxelND (S (S k)) coeffs =
  let dim = S (S k)
      subDiag = map (\i => (VM.MkPixel (i + 2) (i + 1), intToBoxInt 1)) (the (List Nat) [0..k])
      colEntries = filterMap (\(i, c) => if unwrapBox c /= 0 then Just (VM.MkPixel (i + 1) dim, c) else Nothing)
                             (zip (the (List Nat) [0..(S k)]) (toList coeffs))
  in VM.MkMaxel (subDiag ++ colEntries)
  where
    filterMap : (a -> Maybe b) -> List a -> List b
    filterMap _ [] = []
    filterMap f (x :: xs) = case f x of
                              Just y => y :: filterMap f xs
                              Nothing => filterMap f xs

||| Looks up the coefficient for a specific degree in an unfolded term list.
public export
lookupCoeffDeg : Nat -> List (Nat, BoxInt) -> BoxInt
lookupCoeffDeg target terms =
  case find (\(d, _) => d == target) terms of
    Just (_, w) => w
    Nothing     => intToBoxInt 0

||| Extracts the first deg coefficients [c0, c1, ..., c_{deg-1}] as a Vect.
public export
extractCoeffsVect : (deg : Nat) -> (idx : Nat) -> List (Nat, BoxInt) -> Vect deg BoxInt
extractCoeffsVect Z _ _ = []
extractCoeffsVect (S k) idx terms =
  lookupCoeffDeg idx terms :: extractCoeffsVect k (S idx) terms

||| Generalized natural transformation eta from a degree-d StreamPolynumber to its d x d companion Maxel.
||| Extracts [c0, c1, ..., c_{d-1}] from the sparse stream and builds companionMaxelND.
public export
companionMaxelFromPolyDeg : (deg : Nat) -> StreamPolynumber -> VM.Maxel
companionMaxelFromPolyDeg deg p =
  let terms = streamPolyToListNat (S deg) p
      coeffs = extractCoeffsVect deg 0 terms
  in companionMaxelND deg coeffs

||| Extracts sparse polynomial terms directly into a balanced BoxMultisetTree Nat in O(N log N) time.
||| Prunes zero coefficients to preserve active physical support.
public export
extractCoeffsTree : List (Nat, BoxInt) -> BoxMultisetTree Nat
extractCoeffsTree terms =
  foldl (\acc, (deg, w) => setBoxTree deg w acc) BoxLeaf terms

||| Converts a StreamPolynumber directly to a balanced BoxMultisetTree Nat bounded by fuel.
public export
streamPolyToBoxTree : (fuel : Nat) -> StreamPolynumber -> BoxMultisetTree Nat
streamPolyToBoxTree fuel p =
  let terms = streamPolyToListNat fuel p
  in extractCoeffsTree terms

------------------------------------------------------------------------
-- 2. WILDBERGER MULTIPLE SPREAD RECURRENCE TRANSFER MAXEL
------------------------------------------------------------------------

||| Wildberger Multiple Spread Recurrence Transfer Maxel:
||| S_{n+1} = (2 - 4s) S_n - S_{n-1} + 2s.
||| In homogeneous 3x3 coordinates (S_n, S_{n-1}, 1)^T:
|||   [ 2 - 4s   -1   2s ]
|||   [   1       0    0 ]
|||   [   0       0    1 ]
||| Active support topology:
||| - [1, 1]: weight (2 - 4s)
||| - [1, 2]: weight -1
||| - [1, 3]: weight 2s (omitted if s == 0!)
||| - [2, 1]: weight 1 (state shift)
||| - [3, 3]: weight 1 (affine identity)
public export
spreadTransferMaxel : BoxInt -> VM.Maxel
spreadTransferMaxel s =
  let w11 = subBox (intToBoxInt 2) (mulBox (intToBoxInt 4) s)
      w12 = intToBoxInt (-1)
      w13 = mulBox (intToBoxInt 2) s
      e11 = [(VM.MkPixel 1 1, w11)]
      e12 = [(VM.MkPixel 1 2, w12)]
      e13 = if unwrapBox w13 == 0 then [] else [(VM.MkPixel 1 3, w13)]
      e21 = [(VM.MkPixel 2 1, intToBoxInt 1)]
      e33 = [(VM.MkPixel 3 3, intToBoxInt 1)]
  in VM.MkMaxel (e11 ++ e12 ++ e13 ++ e21 ++ e33)

||| Applies the 3x3 Spread Transfer Maxel to an affine state triple (S_n, S_{n-1}, 1).
||| Computes the successor state (S_{n+1}, S_n, 1) in exact BoxInt coordinates.
public export
stepSpreadAffine : BoxInt -> (BoxInt, BoxInt, BoxInt) -> (BoxInt, BoxInt, BoxInt)
stepSpreadAffine s (sn, snMinus1, aff) =
  let w11 = subBox (intToBoxInt 2) (mulBox (intToBoxInt 4) s)
      term1 = mulBox w11 sn
      term2 = mulBox (intToBoxInt (-1)) snMinus1
      term3 = mulBox (mulBox (intToBoxInt 2) s) aff
      snNext = addBox term1 (addBox term2 term3)
  in (snNext, sn, aff)

------------------------------------------------------------------------
-- 3. CONJUGATE HYLOMORPHISM SPREAD RECURRENCE PIPELINE
------------------------------------------------------------------------

||| Generates the n-th Wildberger Spread S_n(s) using bounded Conjugate Hylomorphism.
||| Starting from initial condition S_0 = 0, S_1 = s, affine = 1.
public export
spreadRecurrenceHylo : Fuel -> BoxInt -> BoxInt
spreadRecurrenceHylo fuel s =
  let init = (s, intToBoxInt 0, intToBoxInt 1)
      res = iterateFuel fuel (stepSpreadAffine s) init
  in case res of
        (sn, _, _) => sn
  where
    iterateFuel : Fuel -> (a -> a) -> a -> a
    iterateFuel Dry _ acc = acc
    iterateFuel (More f) step acc = iterateFuel f step (step acc)

||| Generates the n-th Wildberger Spread S_n(s) using Nat-step bounded Conjugate Hylomorphism.
public export
spreadRecurrenceHyloNat : (steps : Nat) -> BoxInt -> BoxInt
spreadRecurrenceHyloNat steps s =
  let init = (s, intToBoxInt 0, intToBoxInt 1)
      res = iterateNat steps (stepSpreadAffine s) init
  in case res of
        (sn, _, _) => sn
  where
    iterateNat : Nat -> (a -> a) -> a -> a
    iterateNat Z _ acc = acc
    iterateNat (S k) step acc = iterateNat k step (step acc)

||| Generates the n-th Wildberger Spread S_n(s) using model-indexed GohFuel.
public export
spreadRecurrenceHyloFuelModel : GohFuel cap -> BoxInt -> BoxInt
spreadRecurrenceHyloFuelModel fuel = spreadRecurrenceHyloNat (gohSteps fuel)

||| Normalizes a Maxel by consolidating duplicate pixels and removing zero weights
||| via canonical single-pass multiset insertion without quadratic list scans.
public export
compressMaxel : VM.Maxel -> VM.Maxel
compressMaxel = VM.canonicalizeMaxel

||| Constructs canonical identity Maxel for small dimensions.
public export
identityMaxelDim : Nat -> VM.Maxel
identityMaxelDim 2 = VM.MkMaxel [ (VM.MkPixel 1 1, intToBoxInt 1), (VM.MkPixel 2 2, intToBoxInt 1) ]
identityMaxelDim 3 = VM.MkMaxel [ (VM.MkPixel 1 1, intToBoxInt 1), (VM.MkPixel 2 2, intToBoxInt 1), (VM.MkPixel 3 3, intToBoxInt 1) ]
identityMaxelDim _ = VM.MkMaxel [ (VM.MkPixel 1 1, intToBoxInt 1) ]

||| Fast logarithmic binary exponentiation for Maxel operators (Rule 04).
||| Computes M^exp in O(log exp) steps via repeated squaring of consolidated Maxels.
public export
fastMaxelPower : Fuel -> (exp : Nat) -> (dim : Nat) -> (m : VM.Maxel) -> VM.Maxel
fastMaxelPower Dry _ dim _ = identityMaxelDim dim
fastMaxelPower (More f) Z dim _ = identityMaxelDim dim
fastMaxelPower (More f) (S Z) _ m = compressMaxel m
fastMaxelPower (More f) exp dim m =
  loop f exp (compressMaxel m) (identityMaxelDim dim)
  where
    loop : Fuel -> Nat -> VM.Maxel -> VM.Maxel -> VM.Maxel
    loop Dry _ _ acc = acc
    loop (More _) Z _ acc = acc
    loop (More f') e base acc =
      let acc' = if (e `mod` 2 == 1) then compressMaxel (VM.mulMaxel acc base) else acc
          base' = compressMaxel (VM.mulMaxel base base)
          e' = e `div` 2
      in loop f' e' base' acc'

||| Evaluates the n-th Wildberger multiple spread S_n in O(log n) steps via companion Maxel repeated squaring:
||| S_0 = 0, S_1 = s, S_2 = (4s - 4s^2), ...
public export
fastSpreadPower : Fuel -> (n : Nat) -> (s : BoxInt) -> BoxInt
fastSpreadPower _ Z _ = intToBoxInt 0
fastSpreadPower _ 1 s = s
fastSpreadPower fuel (S k) s =
  let m = spreadTransferMaxel s
      mPow = fastMaxelPower fuel k 3 m
      vInit = VM.MkVexel [ (VM.MkUnixel 1, s)
                         , (VM.MkUnixel 2, intToBoxInt 0)
                         , (VM.MkUnixel 3, intToBoxInt 1)
                         ]
      vFinal = VM.actMaxelVexel mPow vInit
  in VM.lookupUnixel (VM.MkUnixel 1) vFinal

------------------------------------------------------------------------
-- 4. COMPILE-TIME INVARIANT AUDITS (RULE 01)
------------------------------------------------------------------------

||| Verifies companion matrix support for P(x) = x^2 - 3x - 2 = 0:
||| Supp = {[2, 1], [1, 2], [2, 2]}.
public export
auditCompanionSupportProof : Bool
auditCompanionSupportProof =
  let cMaxel = companionMaxel2D (intToBoxInt 2) (intToBoxInt 3)
      supp = VM.supportMaxel cMaxel
  in supp == [VM.MkPixel 2 1, VM.MkPixel 1 2, VM.MkPixel 2 2]

||| Verifies dynamic support pruning: for s = 0, edge [1, 3] drops from the support!
||| For s = 1, edge [1, 3] is present with weight 2.
public export
auditSpreadSupportPruningProof : Bool
auditSpreadSupportPruningProof =
  let m0 = spreadTransferMaxel (intToBoxInt 0)
      m1 = spreadTransferMaxel (intToBoxInt 1)
      s0 = VM.supportMaxel m0
      s1 = VM.supportMaxel m1
      has13_in_0 = any (\(VM.MkPixel r c) => r == 1 && c == 3) s0
      has13_in_1 = any (\(VM.MkPixel r c) => r == 1 && c == 3) s1
  in not has13_in_0 && has13_in_1

||| Verifies orthogonal spread oscillation (s = 1):
||| S_0 = 0, S_1 = 1, S_2 = 0, S_3 = 1, S_4 = 0.
||| Proves 2-cycle periodic spread invariance under Wildberger recurrence.
public export
auditSpreadOrthogonalOscillationProof : Bool
auditSpreadOrthogonalOscillationProof =
  let s = intToBoxInt 1
      s1 = spreadRecurrenceHyloNat 0 s -- initial S_1 = 1
      s2 = spreadRecurrenceHyloNat 1 s -- S_2 = 0
      s3 = spreadRecurrenceHyloNat 2 s -- S_3 = 1
      s4 = spreadRecurrenceHyloNat 3 s -- S_4 = 0
  in boxEq s1 (intToBoxInt 1) &&
     boxEq s2 (intToBoxInt 0) &&
     boxEq s3 (intToBoxInt 1) &&
     boxEq s4 (intToBoxInt 0)

||| Fast logarithmic binary exponentiation for Maxel operators with Nat fuel (Rule 04).
||| Computes M^exp in O(log exp) steps via repeated squaring of consolidated Maxels using constructive halving.
public export
fastMaxelPowerNat : (fuel : Nat) -> (exp : Nat) -> (dim : Nat) -> (m : VM.Maxel) -> VM.Maxel
fastMaxelPowerNat Z _ dim _ = identityMaxelDim dim
fastMaxelPowerNat (S _) Z dim _ = identityMaxelDim dim
fastMaxelPowerNat (S _) (S Z) _ m = compressMaxel m
fastMaxelPowerNat (S f) exp dim m =
  loop f exp (compressMaxel m) (identityMaxelDim dim)
  where
    loop : Nat -> Nat -> VM.Maxel -> VM.Maxel -> VM.Maxel
    loop Z _ _ acc = acc
    loop (S _) Z _ acc = acc
    loop (S f') e base acc =
      let isOdd = (cast {to = Integer} e `mod` 2) == 1
          acc' = if isOdd then compressMaxel (VM.mulMaxel acc base) else acc
          base' = compressMaxel (VM.mulMaxel base base)
          e' = half e
      in loop f' e' base' acc'

||| Evaluates the n-th Wildberger multiple spread S_n in O(log n) steps with Nat fuel:
public export
fastSpreadPowerNat : (fuel : Nat) -> (n : Nat) -> (s : BoxInt) -> BoxInt
fastSpreadPowerNat _ Z _ = intToBoxInt 0
fastSpreadPowerNat _ 1 s = s
fastSpreadPowerNat fuel (S k) s =
  let m = spreadTransferMaxel s
      mPow = fastMaxelPowerNat fuel k 3 m
      vInit = VM.MkVexel [ (VM.MkUnixel 1, s)
                         , (VM.MkUnixel 2, intToBoxInt 0)
                         , (VM.MkUnixel 3, intToBoxInt 1)
                         ]
      vFinal = VM.actMaxelVexel mPow vInit
  in VM.lookupUnixel (VM.MkUnixel 1) vFinal

||| Verifies fast O(log N) repeated squaring produces identical results to linear hylomorphism:
||| Tests S_1, S_2, S_3, S_4 for both s = 1 (orthogonal) and s = 2 (hyperbolic).
public export
auditFastSpreadEquivalenceProof : Bool
auditFastSpreadEquivalenceProof =
  let sOrth = intToBoxInt 1
      sHyp = intToBoxInt 2
      f1 = fastSpreadPowerNat 10 1 sOrth
      f2 = fastSpreadPowerNat 10 2 sOrth
      f3 = fastSpreadPowerNat 10 3 sOrth
      f4 = fastSpreadPowerNat 10 4 sOrth
      h1 = spreadRecurrenceHyloNat 0 sOrth
      h2 = spreadRecurrenceHyloNat 1 sOrth
      h3 = spreadRecurrenceHyloNat 2 sOrth
      h4 = spreadRecurrenceHyloNat 3 sOrth
      hf1 = fastSpreadPowerNat 10 1 sHyp
      hf2 = fastSpreadPowerNat 10 2 sHyp
      hh1 = spreadRecurrenceHyloNat 0 sHyp
      hh2 = spreadRecurrenceHyloNat 1 sHyp
  in (f1 == h1) && (f2 == h2) && (f3 == h3) && (f4 == h4) &&
     (hf1 == hh1) && (hf2 == hh2)

||| Verifies fast O(log N) repeated squaring with Nat fuel produces identical results to linear hylomorphism.
public export
auditFastSpreadPowerNatEquivalenceProof : Bool
auditFastSpreadPowerNatEquivalenceProof =
  let sOrth = intToBoxInt 1
      sHyp = intToBoxInt 2
      f1 = fastSpreadPowerNat 10 1 sOrth
      f2 = fastSpreadPowerNat 10 2 sOrth
      f3 = fastSpreadPowerNat 10 3 sOrth
      f4 = fastSpreadPowerNat 10 4 sOrth
      h1 = spreadRecurrenceHyloNat 0 sOrth
      h2 = spreadRecurrenceHyloNat 1 sOrth
      h3 = spreadRecurrenceHyloNat 2 sOrth
      h4 = spreadRecurrenceHyloNat 3 sOrth
      hf1 = fastSpreadPowerNat 10 1 sHyp
      hf2 = fastSpreadPowerNat 10 2 sHyp
      hh1 = spreadRecurrenceHyloNat 0 sHyp
      hh2 = spreadRecurrenceHyloNat 1 sHyp
  in (f1 == h1) && (f2 == h2) && (f3 == h3) && (f4 == h4) &&
     (hf1 == hh1) && (hf2 == hh2)

||| Verifies the Support Commutation Theorem across irreducible prime factors:
||| For P = Factor2, Factor3, Factor5, the 2D companion Maxel support size
||| strictly matches the predicted values 1, 3, 7.
public export
auditGohMaxelSupportCommutationProof : Bool
auditGohMaxelSupportCommutationProof =
  let p2 = gohFactorToStreamPoly Factor2
      p3 = gohFactorToStreamPoly Factor3
      p5 = gohFactorToStreamPoly Factor5
      m2 = companionMaxelFromPolyDeg 1 p2
      m3 = companionMaxelFromPolyDeg 2 p3
      m5 = companionMaxelFromPolyDeg 4 p5
      s2 = length (VM.supportMaxel m2)
      s3 = length (VM.supportMaxel m3)
      s5 = length (VM.supportMaxel m5)
  in (s2 == 1) && (s3 == 3) && (s5 == 7)

