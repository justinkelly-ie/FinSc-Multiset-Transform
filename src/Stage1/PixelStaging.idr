module Stage1.PixelStaging

import Stage0.Pixel
import Stage1.TypeTheory.Staging
import Stage1.TypeTheory.TwoLevel

%default total

------------------------------------------------------------------------
-- 2LTT STAGED PIXEL MULTIPLICATION
------------------------------------------------------------------------

||| 2LTT Staged Pixel Multiplication: Pre-evaluates non-linear pixel multiplication at Stage 1 (U_1)
||| and splices out the resulting Pixel down to Stage 0 (U_0).
%inline public export
stagedPixelMul : Eq a => Lift (Pixel metric a) -> Lift (Pixel metric a) -> Maybe (Pixel metric a)
stagedPixelMul p1 p2 = mulPixel (splice p1) (splice p2)

||| QTT 0 Erased Proof Witness: Staged Pixel Multiplication Invariant
public export
0 prfStagedPixelMul : Eq a => (p1 : Pixel metric a) -> (p2 : Pixel metric a) ->
                      stagedPixelMul (quote p1) (quote p2) = mulPixel p1 p2
prfStagedPixelMul _ _ = Refl
