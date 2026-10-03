module Stage1.MaxelStaging

import Stage0.BoxInt
import Stage1.VexelMaxel
import Stage1.TypeTheory.Staging
import Stage1.TypeTheory.TwoLevel

%default total

------------------------------------------------------------------------
-- 2LTT STAGED MAXEL ALGEBRA
------------------------------------------------------------------------

||| 2LTT Staged Maxel Multiplication (discrete matrix multiplication):
||| Evaluates discrete matrix multiplication at Stage 1 (U_1) and splices to Stage 0 (U_0).
%inline public export
stagedMaxelMul : Lift Maxel -> Lift Maxel -> Maxel
stagedMaxelMul m1 m2 = mulMaxel (splice m1) (splice m2)

||| QTT 0 Erased Proof Witness: Staged Maxel Multiplication Invariant
public export
0 prfStagedMaxelMul : (m1 : Maxel) -> (m2 : Maxel) ->
                      stagedMaxelMul (quote m1) (quote m2) = mulMaxel m1 m2
prfStagedMaxelMul _ _ = Refl

||| 2LTT Staged Maxel Addition: Concatenates pixel multisets at Stage 1.
%inline public export
stagedMaxelAdd : Lift Maxel -> Lift Maxel -> Maxel
stagedMaxelAdd m1 m2 = addMaxel (splice m1) (splice m2)

||| QTT 0 Erased Proof Witness: Staged Maxel Addition Invariant
public export
0 prfStagedMaxelAdd : (m1 : Maxel) -> (m2 : Maxel) ->
                      stagedMaxelAdd (quote m1) (quote m2) = addMaxel m1 m2
prfStagedMaxelAdd _ _ = Refl

||| 2LTT Staged Maxel Scalar Scaling.
%inline public export
stagedMaxelScale : Lift BoxInt -> Lift Maxel -> Maxel
stagedMaxelScale s m = scaleMaxel (splice s) (splice m)

||| QTT 0 Erased Proof Witness: Staged Maxel Scaling Invariant
public export
0 prfStagedMaxelScale : (s : BoxInt) -> (m : Maxel) ->
                        stagedMaxelScale (quote s) (quote m) = scaleMaxel s m
prfStagedMaxelScale _ _ = Refl

||| 2LTT Staged Matrix-Vector Contraction (actMaxelVexel).
%inline public export
stagedActMaxelVexel : Lift Maxel -> Lift Vexel -> Vexel
stagedActMaxelVexel m v = actMaxelVexel (splice m) (splice v)

||| QTT 0 Erased Proof Witness: Staged Action Invariant
public export
0 prfStagedActMaxelVexel : (m : Maxel) -> (v : Vexel) ->
                           stagedActMaxelVexel (quote m) (quote v) = actMaxelVexel m v
prfStagedActMaxelVexel _ _ = Refl

||| 2LTT Staged Maxel Canonicalization: Aggregates duplicates and eliminates zero-weight entries.
%inline public export
stagedCanonicalizeMaxel : Lift Maxel -> Maxel
stagedCanonicalizeMaxel m = canonicalizeMaxel (splice m)

||| QTT 0 Erased Proof Witness: Staged Canonicalization Invariant
public export
0 prfStagedCanonicalizeMaxel : (m : Maxel) ->
                               stagedCanonicalizeMaxel (quote m) = canonicalizeMaxel m
prfStagedCanonicalizeMaxel _ = Refl

||| 2LTT Staged Total Weight Evaluation.
%inline public export
stagedTotalMaxelWeight : Lift Maxel -> BoxInt
stagedTotalMaxelWeight m = totalMaxelWeight (splice m)

||| QTT 0 Erased Proof Witness: Staged Weight Invariant
public export
0 prfStagedTotalMaxelWeight : (m : Maxel) ->
                              stagedTotalMaxelWeight (quote m) = totalMaxelWeight m
prfStagedTotalMaxelWeight _ = Refl
