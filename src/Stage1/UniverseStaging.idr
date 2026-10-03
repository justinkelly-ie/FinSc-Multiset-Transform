module Stage1.UniverseStaging

import Data.Fin
import Data.Vect
import Stage0.BoxInt
import Stage0.UniverseState
import Stage0.LinearBuffer
import Stage1.TypeTheory.Staging
import Stage1.TypeTheory.TwoLevel

%default total

------------------------------------------------------------------------
-- 1. STAGED LINEAR STATE TRANSITIONS (UNIVERSE STATE)
------------------------------------------------------------------------

||| 2LTT Staged Single-Step Linear Universe State Transition:
||| Pre-evaluates a discrete state transition at Stage 1 (U_1) and splices out to Stage 0 (U_0).
%inline public export
stagedStepUniverseLinear : {vm, de, dm, k : Nat} ->
                           Lift (UniverseState vm de dm) ->
                           Lift (Vect k BoxInt) ->
                           UniverseState (vm + k) de (S dm)
stagedStepUniverseLinear qState qMatter =
  stepUniverseLinear (splice qState) (splice qMatter)

||| QTT 0 Erased Proof Witness: Staged Single-Step Invariant
public export
0 prfStagedStepUniverseLinear : {vm, de, dm, k : Nat} ->
                                (state : UniverseState vm de dm) ->
                                (matter : Vect k BoxInt) ->
                                stagedStepUniverseLinear (quote state) (quote matter) = stepUniverseLinear state matter
prfStagedStepUniverseLinear _ _ = Refl

||| 2LTT Staged Two-Step Unfolded State Transition:
||| Statically sequences two consecutive matter injections at compile-time without intermediate heap allocations.
%inline public export
stagedStepUniverse2 : {vm, de, dm, k1, k2 : Nat} ->
                      Lift (UniverseState vm de dm) ->
                      Lift (Vect k1 BoxInt) ->
                      Lift (Vect k2 BoxInt) ->
                      UniverseState ((vm + k1) + k2) de (S (S dm))
stagedStepUniverse2 qState qM1 qM2 =
  stepUniverseLinear (stagedStepUniverseLinear qState qM1) (splice qM2)

||| QTT 0 Erased Proof Witness: Staged Two-Step Invariant
public export
0 prfStagedStepUniverse2 : {vm, de, dm, k1, k2 : Nat} ->
                           (state : UniverseState vm de dm) ->
                           (m1 : Vect k1 BoxInt) ->
                           (m2 : Vect k2 BoxInt) ->
                           stagedStepUniverse2 (quote state) (quote m1) (quote m2) =
                             stepUniverseLinear (stepUniverseLinear state m1) m2
prfStagedStepUniverse2 _ _ _ = Refl

||| 2LTT Staged Three-Step Unfolded State Transition (Tri-Metric Genesis Cycle: Red, Green, Blue):
||| Pre-evaluates 3 sequential spatial field expansions into an exact unrolled composite state.
%inline public export
stagedStepUniverse3 : {vm, de, dm, k1, k2, k3 : Nat} ->
                      Lift (UniverseState vm de dm) ->
                      Lift (Vect k1 BoxInt) ->
                      Lift (Vect k2 BoxInt) ->
                      Lift (Vect k3 BoxInt) ->
                      UniverseState (((vm + k1) + k2) + k3) de (S (S (S dm)))
stagedStepUniverse3 qState qM1 qM2 qM3 =
  stepUniverseLinear (stagedStepUniverse2 qState qM1 qM2) (splice qM3)

||| QTT 0 Erased Proof Witness: Staged Three-Step Invariant
public export
0 prfStagedStepUniverse3 : {vm, de, dm, k1, k2, k3 : Nat} ->
                           (state : UniverseState vm de dm) ->
                           (m1 : Vect k1 BoxInt) ->
                           (m2 : Vect k2 BoxInt) ->
                           (m3 : Vect k3 BoxInt) ->
                           stagedStepUniverse3 (quote state) (quote m1) (quote m2) (quote m3) =
                             stepUniverseLinear (stepUniverseLinear (stepUniverseLinear state m1) m2) m3
prfStagedStepUniverse3 _ _ _ _ = Refl

------------------------------------------------------------------------
-- 2. STAGED LINEAR BUFFER MANIPULATION
------------------------------------------------------------------------

||| 2LTT Staged Linear Buffer Write Update:
||| Evaluates linear index replacement at Stage 1, eliminating lookup overhead.
%inline public export
stagedWriteLinearBuffer : {capacity : Nat} ->
                          Lift (LinearBuffer capacity) ->
                          Lift (Fin capacity) ->
                          Lift BoxInt ->
                          LinearBuffer capacity
stagedWriteLinearBuffer qBuf qIdx qVal =
  writeLinearBuffer (splice qBuf) (splice qIdx) (splice qVal)

||| QTT 0 Erased Proof Witness: Staged Buffer Write Invariant
public export
0 prfStagedWriteLinearBuffer : {capacity : Nat} ->
                              (buf : LinearBuffer capacity) ->
                              (idx : Fin capacity) ->
                              (val : BoxInt) ->
                              stagedWriteLinearBuffer (quote buf) (quote idx) (quote val) = writeLinearBuffer buf idx val
prfStagedWriteLinearBuffer _ _ _ = Refl
