module Stage1.MaxelStaging

import Stage0.BoxInt
import Stage1.Basis.Coordinate
import Stage1.TypeTheory.Staging
import Stage1.TypeTheory.TwoLevel
import Data.Vect

%default total

------------------------------------------------------------------------
-- 2LTT STAGED MAXEL ALGEBRA
------------------------------------------------------------------------

||| 2LTT Staged Maxel Multiplication (discrete matrix multiplication):
||| Evaluates discrete matrix multiplication at Stage 1 (U_1) and returns reified Code at Level 1.
%inline public export
stagedMaxelMul : Lift Maxel -> Lift Maxel -> Code Maxel
stagedMaxelMul m1 m2 = quote (mulMaxel (splice m1) (splice m2))

||| Staged evaluation of Maxel multiplication:
%inline public export
evalStagedMaxelMul : Lift Maxel -> Lift Maxel -> Maxel
evalStagedMaxelMul m1 m2 = splice (stagedMaxelMul m1 m2)

||| QTT 0 Erased Proof Witness: Staged Maxel Multiplication Invariant
public export
0 prfStagedMaxelMul : (m1 : Maxel) -> (m2 : Maxel) ->
                      splice (stagedMaxelMul (quote m1) (quote m2)) = mulMaxel m1 m2
prfStagedMaxelMul _ _ = Refl

||| 2LTT Staged Maxel Addition: Concatenates pixel multisets at Stage 1.
%inline public export
stagedMaxelAdd : Lift Maxel -> Lift Maxel -> Code Maxel
stagedMaxelAdd m1 m2 = quote (addCellMultiset (splice m1) (splice m2))

||| Staged evaluation of Maxel addition:
%inline public export
evalStagedMaxelAdd : Lift Maxel -> Lift Maxel -> Maxel
evalStagedMaxelAdd m1 m2 = splice (stagedMaxelAdd m1 m2)

||| QTT 0 Erased Proof Witness: Staged Maxel Addition Invariant
public export
0 prfStagedMaxelAdd : (m1 : Maxel) -> (m2 : Maxel) ->
                      splice (stagedMaxelAdd (quote m1) (quote m2)) = addCellMultiset m1 m2
prfStagedMaxelAdd _ _ = Refl

||| 2LTT Staged Maxel Scalar Scaling.
%inline public export
stagedMaxelScale : Lift BoxInt -> Lift Maxel -> Code Maxel
stagedMaxelScale s m = quote (scaleCellMultiset (splice s) (splice m))

||| Staged evaluation of Maxel scaling:
%inline public export
evalStagedMaxelScale : Lift BoxInt -> Lift Maxel -> Maxel
evalStagedMaxelScale s m = splice (stagedMaxelScale s m)

||| QTT 0 Erased Proof Witness: Staged Maxel Scaling Invariant
public export
0 prfStagedMaxelScale : (s : BoxInt) -> (m : Maxel) ->
                        splice (stagedMaxelScale (quote s) (quote m)) = scaleCellMultiset s m
prfStagedMaxelScale _ _ = Refl

||| 2LTT Staged Matrix-Vector Contraction (actMaxelVexel).
%inline public export
stagedActMaxelVexel : Lift Maxel -> Lift Vexel -> Code Vexel
stagedActMaxelVexel m v = quote (actMaxelVexel (splice m) (splice v))

||| Staged evaluation of matrix-vector contraction:
%inline public export
evalStagedActMaxelVexel : Lift Maxel -> Lift Vexel -> Vexel
evalStagedActMaxelVexel m v = splice (stagedActMaxelVexel m v)

||| QTT 0 Erased Proof Witness: Staged Action Invariant
public export
0 prfStagedActMaxelVexel : (m : Maxel) -> (v : Vexel) ->
                           splice (stagedActMaxelVexel (quote m) (quote v)) = actMaxelVexel m v
prfStagedActMaxelVexel _ _ = Refl

||| 2LTT Staged Maxel Canonicalization: Aggregates duplicates and eliminates zero-weight entries.
%inline public export
stagedCanonicalizeMaxel : Lift Maxel -> Code Maxel
stagedCanonicalizeMaxel m = quote (canonicalizeCellMultiset (splice m))

||| Staged evaluation of Maxel canonicalization:
%inline public export
evalStagedCanonicalizeMaxel : Lift Maxel -> Maxel
evalStagedCanonicalizeMaxel m = splice (stagedCanonicalizeMaxel m)

||| QTT 0 Erased Proof Witness: Staged Canonicalization Invariant
public export
0 prfStagedCanonicalizeMaxel : (m : Maxel) ->
                               splice (stagedCanonicalizeMaxel (quote m)) = canonicalizeCellMultiset m
prfStagedCanonicalizeMaxel _ = Refl

||| 2LTT Staged Total Weight Evaluation.
%inline public export
stagedTotalMaxelWeight : Lift Maxel -> Code BoxInt
stagedTotalMaxelWeight m = quote (totalCellMultisetWeight (splice m))

||| Staged evaluation of total weight:
%inline public export
evalStagedTotalMaxelWeight : Lift Maxel -> BoxInt
evalStagedTotalMaxelWeight m = splice (stagedTotalMaxelWeight m)

||| QTT 0 Erased Proof Witness: Staged Weight Invariant
public export
0 prfStagedTotalMaxelWeight : (m : Maxel) ->
                              splice (stagedTotalMaxelWeight (quote m)) = totalCellMultisetWeight m
prfStagedTotalMaxelWeight _ = Refl

------------------------------------------------------------------------
-- 2LTT STAGED DIMENSION-INDEXED MATRIX ENGINE
------------------------------------------------------------------------

||| 2LTT Staged N x N Matrix Multiplication:
||| Evaluates dimension-indexed matrix multiplication at compile time (Stage 1)
||| via deforested dot products and returns reified Code at Level 1.
public export
stagedMatrixMul : Num a => {n : Nat} -> Lift (Vect n (Vect n a)) -> Lift (Vect n (Vect n a)) -> Code (Vect n (Vect n a))
stagedMatrixMul matA matB = quote (stagedUnrollMatMul (splice matA) (splice matB))

||| Staged evaluation of matrix multiplication:
public export
evalStagedMatrixMul : Num a => {n : Nat} -> Lift (Vect n (Vect n a)) -> Lift (Vect n (Vect n a)) -> Vect n (Vect n a)
evalStagedMatrixMul matA matB = splice (stagedMatrixMul matA matB)

||| 2LTT Staged N x N Matrix-Vector Contraction:
public export
stagedMatrixVec : Num a => {n : Nat} -> Lift (Vect n (Vect n a)) -> Lift (Vect n a) -> Code (Vect n a)
stagedMatrixVec mat v = quote (stagedUnrollMatVec (splice mat) (splice v))

||| Staged evaluation of matrix-vector contraction:
public export
evalStagedMatrixVec : Num a => {n : Nat} -> Lift (Vect n (Vect n a)) -> Lift (Vect n a) -> Vect n a
evalStagedMatrixVec mat v = splice (stagedMatrixVec mat v)

||| 2LTT Staged N x N Matrix Power:
public export
stagedMatrixPower : Num a => (fuel : Nat) -> {n : Nat} -> Lift (Vect n (Vect n a)) -> Nat -> Code (Vect n (Vect n a))
stagedMatrixPower fuel mat exp = quote (stagedFastMatPower fuel (splice mat) exp)

||| Staged evaluation of matrix power:
public export
evalStagedMatrixPower : Num a => (fuel : Nat) -> {n : Nat} -> Lift (Vect n (Vect n a)) -> Nat -> Vect n (Vect n a)
evalStagedMatrixPower fuel mat exp = splice (stagedMatrixPower fuel mat exp)

||| Converts a 2x2 matrix of BoxInt into a Maxel representation.
public export
vect2x2ToMaxel : Vect 2 (Vect 2 BoxInt) -> Maxel
vect2x2ToMaxel [[m11, m12], [m21, m22]] =
  let p11 = singletonCell (mkCell2 1 1) m11
      p12 = singletonCell (mkCell2 1 2) m12
      p21 = singletonCell (mkCell2 2 1) m21
      p22 = singletonCell (mkCell2 2 2) m22
  in canonicalizeCellMultiset (p11 <+> p12 <+> p21 <+> p22)

||| Staged 2x2 companion Maxel multiplication evaluating straight-line scalar dot products:
public export
stagedCompanion2x2Mul : Lift (Vect 2 (Vect 2 BoxInt)) -> Lift (Vect 2 (Vect 2 BoxInt)) -> Code Maxel
stagedCompanion2x2Mul mA mB = quote (vect2x2ToMaxel (evalStagedMatrixMul mA mB))

||| Staged evaluation of 2x2 companion Maxel multiplication:
public export
evalStagedCompanion2x2Mul : Lift (Vect 2 (Vect 2 BoxInt)) -> Lift (Vect 2 (Vect 2 BoxInt)) -> Maxel
evalStagedCompanion2x2Mul mA mB = splice (stagedCompanion2x2Mul mA mB)
