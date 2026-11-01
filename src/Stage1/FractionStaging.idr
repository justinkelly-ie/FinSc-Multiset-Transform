module Stage1.FractionStaging

import Stage0.BoxInt
import Stage0.SignedFraction
import Stage1.Basis.Coordinate
import Stage1.UnixelFraction
import Stage1.TypeTheory.Staging
import Stage1.TypeTheory.TwoLevel

%default total

------------------------------------------------------------------------
-- 2LTT STAGED FRACTION ARITHMETIC
------------------------------------------------------------------------

||| 2LTT Staged Fraction Addition: Pre-evaluates cross-multiplied addition at Stage 1 (U_1)
||| and returns reified Code at Level 1.
%inline public export
stagedFractionAdd : Lift MSetFraction -> Lift MSetFraction -> Code MSetFraction
stagedFractionAdd f1 f2 = quote (addMSF (splice f1) (splice f2))

||| Staged evaluation of fraction addition:
%inline public export
evalStagedFractionAdd : Lift MSetFraction -> Lift MSetFraction -> MSetFraction
evalStagedFractionAdd f1 f2 = splice (stagedFractionAdd f1 f2)

||| QTT 0 Erased Proof Witness: Staged Fraction Addition Invariant
public export
0 prfStagedFractionAdd : (f1 : MSetFraction) -> (f2 : MSetFraction) ->
                         splice (stagedFractionAdd (quote f1) (quote f2)) = addMSF f1 f2
prfStagedFractionAdd _ _ = Refl

||| 2LTT Staged Fraction Multiplication: Pre-evaluates cross-multiplied multiplication at Stage 1 (U_1)
||| and returns reified Code at Level 1.
%inline public export
stagedFractionMul : Lift MSetFraction -> Lift MSetFraction -> Code MSetFraction
stagedFractionMul f1 f2 = quote (mulMSF (splice f1) (splice f2))

||| Staged evaluation of fraction multiplication:
%inline public export
evalStagedFractionMul : Lift MSetFraction -> Lift MSetFraction -> MSetFraction
evalStagedFractionMul f1 f2 = splice (stagedFractionMul f1 f2)

||| QTT 0 Erased Proof Witness: Staged Fraction Multiplication Invariant
public export
0 prfStagedFractionMul : (f1 : MSetFraction) -> (f2 : MSetFraction) ->
                         splice (stagedFractionMul (quote f1) (quote f2)) = mulMSF f1 f2
prfStagedFractionMul _ _ = Refl

||| 2LTT Staged Fraction Subtraction: Pre-evaluates cross-multiplied subtraction at Stage 1 (U_1)
||| and returns reified Code at Level 1.
%inline public export
stagedFractionSub : Lift MSetFraction -> Lift MSetFraction -> Code MSetFraction
stagedFractionSub f1 f2 = quote (subMSF (splice f1) (splice f2))

||| Staged evaluation of fraction subtraction:
%inline public export
evalStagedFractionSub : Lift MSetFraction -> Lift MSetFraction -> MSetFraction
evalStagedFractionSub f1 f2 = splice (stagedFractionSub f1 f2)

||| QTT 0 Erased Proof Witness: Staged Fraction Subtraction Invariant
public export
0 prfStagedFractionSub : (f1 : MSetFraction) -> (f2 : MSetFraction) ->
                         splice (stagedFractionSub (quote f1) (quote f2)) = subMSF f1 f2
prfStagedFractionSub _ _ = Refl

||| 2LTT Staged Scalar Multiplication of a Fraction by a BoxInt scalar.
%inline public export
stagedFractionScale : Lift BoxInt -> Lift MSetFraction -> Code MSetFraction
stagedFractionScale s f = quote (scaleMSF (splice s) (splice f))

||| Staged evaluation of fraction scaling:
%inline public export
evalStagedFractionScale : Lift BoxInt -> Lift MSetFraction -> MSetFraction
evalStagedFractionScale s f = splice (stagedFractionScale s f)

||| QTT 0 Erased Proof Witness: Staged Fraction Scaling Invariant
public export
0 prfStagedFractionScale : (s : BoxInt) -> (f : MSetFraction) ->
                           splice (stagedFractionScale (quote s) (quote f)) = scaleMSF s f
prfStagedFractionScale _ _ = Refl

||| 2LTT Staged Exact Fraction Equality Comparison.
%inline public export
stagedFractionEq : Lift MSetFraction -> Lift MSetFraction -> Code Bool
stagedFractionEq f1 f2 = quote (eqMSF (splice f1) (splice f2))

||| Staged evaluation of fraction equality:
%inline public export
evalStagedFractionEq : Lift MSetFraction -> Lift MSetFraction -> Bool
evalStagedFractionEq f1 f2 = splice (stagedFractionEq f1 f2)

||| QTT 0 Erased Proof Witness: Staged Fraction Equality Invariant
public export
0 prfStagedFractionEq : (f1 : MSetFraction) -> (f2 : MSetFraction) ->
                        splice (stagedFractionEq (quote f1) (quote f2)) = eqMSF f1 f2
prfStagedFractionEq _ _ = Refl

------------------------------------------------------------------------
-- 2LTT STAGED FRACTION BRIDGE (U_0 MSetFraction <-> U_1 UnixelFraction)
------------------------------------------------------------------------

||| 2LTT Staged Elevation: Lifts an MSetFraction to a UnixelFraction at Stage 1.
%inline public export
stagedToUnixelFraction : Lift MSetFraction -> Code UnixelFraction
stagedToUnixelFraction f = quote (msetFractionToUnixelFraction (splice f))

||| Staged evaluation of fraction elevation:
%inline public export
evalStagedToUnixelFraction : Lift MSetFraction -> UnixelFraction
evalStagedToUnixelFraction f = splice (stagedToUnixelFraction f)

||| 2LTT Staged Demotion: Splices a Stage 1 UnixelFraction down to Stage 0 MSetFraction.
%inline public export
stagedToMSetFraction : Lift UnixelFraction -> Code MSetFraction
stagedToMSetFraction f = quote (unixelFractionToMSetFraction (splice f))

||| Staged evaluation of fraction demotion:
%inline public export
evalStagedToMSetFraction : Lift UnixelFraction -> MSetFraction
evalStagedToMSetFraction f = splice (stagedToMSetFraction f)

||| QTT 0 Erased Proof Witness: Staged Round-trip preservation for positive denominators
public export
0 prfStagedFractionRoundTrip : (n : BoxInt) -> (k : Nat) ->
                               splice (stagedToMSetFraction (stagedToUnixelFraction (quote (MkMSF n (S k))))) = MkMSF n (S k)
prfStagedFractionRoundTrip _ _ = Refl

