module Stage1.PixelStaging

import Stage0.Pixel
import Stage1.Basis.Coordinate
import Stage1.TypeTheory.Staging
import Stage1.TypeTheory.TwoLevel

%default total

------------------------------------------------------------------------
-- 2LTT STAGED PIXEL MULTIPLICATION
------------------------------------------------------------------------

||| 2LTT Staged Pixel Multiplication: Pre-evaluates non-linear pixel multiplication at Stage 1 (U_1)
||| and returns reified Code at Level 1.
%inline public export
stagedPixelMul : Eq a => Lift (Pixel metric a) -> Lift (Pixel metric a) -> Code (Maybe (Pixel metric a))
stagedPixelMul p1 p2 = quote (mulPixel (splice p1) (splice p2))

||| Staged evaluation of pixel multiplication:
%inline public export
evalStagedPixelMul : Eq a => Lift (Pixel metric a) -> Lift (Pixel metric a) -> Maybe (Pixel metric a)
evalStagedPixelMul p1 p2 = splice (stagedPixelMul p1 p2)

||| QTT 0 Erased Proof Witness: Staged Pixel Multiplication Invariant
public export
0 prfStagedPixelMul : Eq a => (p1 : Pixel metric a) -> (p2 : Pixel metric a) ->
                      splice (stagedPixelMul (quote p1) (quote p2)) = mulPixel p1 p2
prfStagedPixelMul _ _ = Refl

||| 2LTT Staged Token-Based Pixel Multiplication (Rule 03 §6):
||| Evaluates directional token annihilation [A, B] · [B, C] = [A, C] at Stage 1 (U_1)
||| and emits reified Code at Level 1.
public export
stagedCoordCellMulTokens : Lift (CoordCell 2) -> Lift (CoordCell 2) -> Code (Maybe (CoordCell 2))
stagedCoordCellMulTokens qp1 qp2 = quote (mulPixelTokens (splice qp1) (splice qp2))

||| Staged evaluation of token-based pixel multiplication:
public export
evalStagedCoordCellMulTokens : Lift (CoordCell 2) -> Lift (CoordCell 2) -> Maybe (CoordCell 2)
evalStagedCoordCellMulTokens qp1 qp2 = splice (stagedCoordCellMulTokens qp1 qp2)

||| QTT 0 Erased Proof Witness: Staged Token Pixel Multiplication Invariant
public export
0 prfStagedCoordCellMulTokens : (p1 : CoordCell 2) -> (p2 : CoordCell 2) ->
                               splice (stagedCoordCellMulTokens (quote p1) (quote p2)) = mulPixelTokens p1 p2
prfStagedCoordCellMulTokens _ _ = Refl

------------------------------------------------------------------------
-- 2LTT STAGED UNROLLED COORDCELL OPERATIONS
------------------------------------------------------------------------

||| 2LTT Staged Canonical CoordCell 2 Unrolled Multiplication.
public export
stagedCoordCellMul2D : Lift (CoordCell 2) -> Lift (CoordCell 2) -> Code (CoordCell 2)
stagedCoordCellMul2D = stagedUnrollMul 2

||| 2LTT Staged Universal Coordinate Cell Translation:
||| Translates a CellMultiset by a CoordCell offset using 2LTT staging.
public export
stagedTranslateCell : {dim : Nat} -> Lift (CoordCell dim) -> Lift (CellMultiset dim) -> Code (CellMultiset dim)
stagedTranslateCell qc qm = quote (translateCell (splice qc) (splice qm))

||| Staged evaluation of coordinate cell translation:
public export
evalStagedTranslateCell : {dim : Nat} -> Lift (CoordCell dim) -> Lift (CellMultiset dim) -> CellMultiset dim
evalStagedTranslateCell qc qm = splice (stagedTranslateCell qc qm)

||| QTT 0 Erased Proof Witness: Staged Cell Translation Invariant
public export
0 prfStagedTranslateCell : {dim : Nat} -> (c : CoordCell dim) -> (m : CellMultiset dim) ->
                           splice (stagedTranslateCell (quote c) (quote m)) = translateCell c m
prfStagedTranslateCell _ _ = Refl
