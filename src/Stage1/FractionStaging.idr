module Stage1.FractionStaging

import Stage0.BoxInt
import Stage0.SignedFraction
import Stage1.UnixelFraction
import Stage1.TypeTheory.Staging
import Stage1.TypeTheory.TwoLevel

%default total

------------------------------------------------------------------------
-- 2LTT STAGED FRACTION ARITHMETIC
------------------------------------------------------------------------

||| 2LTT Staged Fraction Addition: Pre-evaluates cross-multiplied addition at Stage 1 (U_1)
||| and splices out the resulting MSetFraction down to Stage 0 (U_0).
%inline public export
stagedFractionAdd : Lift MSetFraction -> Lift MSetFraction -> MSetFraction
stagedFractionAdd f1 f2 = addMSF (splice f1) (splice f2)

||| QTT 0 Erased Proof Witness: Staged Fraction Addition Invariant
public export
0 prfStagedFractionAdd : (f1 : MSetFraction) -> (f2 : MSetFraction) ->
                         stagedFractionAdd (quote f1) (quote f2) = addMSF f1 f2
prfStagedFractionAdd _ _ = Refl

||| 2LTT Staged Fraction Multiplication: Pre-evaluates cross-multiplied multiplication at Stage 1 (U_1)
||| and splices out the resulting MSetFraction down to Stage 0 (U_0).
%inline public export
stagedFractionMul : Lift MSetFraction -> Lift MSetFraction -> MSetFraction
stagedFractionMul f1 f2 = mulMSF (splice f1) (splice f2)

||| QTT 0 Erased Proof Witness: Staged Fraction Multiplication Invariant
public export
0 prfStagedFractionMul : (f1 : MSetFraction) -> (f2 : MSetFraction) ->
                         stagedFractionMul (quote f1) (quote f2) = mulMSF f1 f2
prfStagedFractionMul _ _ = Refl

||| 2LTT Staged Fraction Subtraction: Pre-evaluates cross-multiplied subtraction at Stage 1 (U_1).
%inline public export
stagedFractionSub : Lift MSetFraction -> Lift MSetFraction -> MSetFraction
stagedFractionSub f1 f2 = subMSF (splice f1) (splice f2)

||| QTT 0 Erased Proof Witness: Staged Fraction Subtraction Invariant
public export
0 prfStagedFractionSub : (f1 : MSetFraction) -> (f2 : MSetFraction) ->
                         stagedFractionSub (quote f1) (quote f2) = subMSF f1 f2
prfStagedFractionSub _ _ = Refl

||| 2LTT Staged Scalar Multiplication of a Fraction by a BoxInt scalar.
%inline public export
stagedFractionScale : Lift BoxInt -> Lift MSetFraction -> MSetFraction
stagedFractionScale s f = scaleMSF (splice s) (splice f)

||| QTT 0 Erased Proof Witness: Staged Fraction Scaling Invariant
public export
0 prfStagedFractionScale : (s : BoxInt) -> (f : MSetFraction) ->
                           stagedFractionScale (quote s) (quote f) = scaleMSF s f
prfStagedFractionScale _ _ = Refl

||| 2LTT Staged Exact Fraction Equality Comparison.
%inline public export
stagedFractionEq : Lift MSetFraction -> Lift MSetFraction -> Bool
stagedFractionEq f1 f2 = eqMSF (splice f1) (splice f2)

||| QTT 0 Erased Proof Witness: Staged Fraction Equality Invariant
public export
0 prfStagedFractionEq : (f1 : MSetFraction) -> (f2 : MSetFraction) ->
                        stagedFractionEq (quote f1) (quote f2) = eqMSF f1 f2
prfStagedFractionEq _ _ = Refl

------------------------------------------------------------------------
-- 2LTT STAGED FRACTION BRIDGE (U_0 MSetFraction <-> U_1 UnixelFraction)
------------------------------------------------------------------------

||| 2LTT Staged Elevation: Lifts an MSetFraction to a UnixelFraction at Stage 1.
%inline public export
stagedToUnixelFraction : Lift MSetFraction -> UnixelFraction
stagedToUnixelFraction f = msetFractionToUnixelFraction (splice f)

||| 2LTT Staged Demotion: Splices a Stage 1 UnixelFraction down to Stage 0 MSetFraction.
%inline public export
stagedToMSetFraction : Lift UnixelFraction -> MSetFraction
stagedToMSetFraction f = unixelFractionToMSetFraction (splice f)

||| QTT 0 Erased Proof Witness: Staged Round-trip preservation for positive denominators
public export
0 prfStagedFractionRoundTrip : (n : BoxInt) -> (k : Nat) ->
                               stagedToMSetFraction (quote (stagedToUnixelFraction (quote (MkMSF n (S k))))) = MkMSF n (S k)
prfStagedFractionRoundTrip _ _ = Refl

