module Stage1.MaxelPolyBridge

import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.StructuralFuel
import Stage0.OnSeq.FusedStream as FS
import Stage0.StreamPolynumber
import Stage1.ConjugateHylo
import Stage1.VexelMaxel as VM
import Stage1.VexelStream as VS
import Data.Fuel
import Data.List

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
  let terms = streamPolyToList (limit 5) p
      c0 = case find (\(d, _) => d == 0) terms of
             Just (_, w) => w
             Nothing     => intToBoxInt 0
      c1 = case find (\(d, _) => d == 1) terms of
             Just (_, w) => w
             Nothing     => intToBoxInt 0
  in companionMaxel2D c0 c1

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
      s1 = spreadRecurrenceHylo (limit 0) s -- initial S_1 = 1
      s2 = spreadRecurrenceHylo (limit 1) s -- S_2 = 0
      s3 = spreadRecurrenceHylo (limit 2) s -- S_3 = 1
      s4 = spreadRecurrenceHylo (limit 3) s -- S_4 = 0
  in boxEq s1 (intToBoxInt 1) &&
     boxEq s2 (intToBoxInt 0) &&
     boxEq s3 (intToBoxInt 1) &&
     boxEq s4 (intToBoxInt 0)
