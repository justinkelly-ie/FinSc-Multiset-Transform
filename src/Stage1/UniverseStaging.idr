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
||| Pre-evaluates a discrete state transition at Stage 1 (U_1) and returns reified Code at Level 1.
%inline public export
stagedStepUniverseLinear : {vm, de, dm, k : Nat} ->
                           Lift (UniverseState vm de dm) ->
                           Lift (Vect k BoxInt) ->
                           Code (UniverseState (vm + k) de (S dm))
stagedStepUniverseLinear qState qMatter =
  quote (stepUniverseLinear (splice qState) (splice qMatter))

||| Staged evaluation of single-step linear universe state transition:
%inline public export
evalStagedStepUniverseLinear : {vm, de, dm, k : Nat} ->
                               Lift (UniverseState vm de dm) ->
                               Lift (Vect k BoxInt) ->
                               UniverseState (vm + k) de (S dm)
evalStagedStepUniverseLinear qState qMatter =
  splice (stagedStepUniverseLinear qState qMatter)

||| QTT 0 Erased Proof Witness: Staged Single-Step Invariant
public export
0 prfStagedStepUniverseLinear : {vm, de, dm, k : Nat} ->
                                (state : UniverseState vm de dm) ->
                                (matter : Vect k BoxInt) ->
                                splice (stagedStepUniverseLinear (quote state) (quote matter)) = stepUniverseLinear state matter
prfStagedStepUniverseLinear _ _ = Refl

||| Linear 2LTT (LQTT) Staged State Transition:
||| Consumes the LinearLift container and the underlying UniverseState with linear multiplicity 1,
||| guaranteeing at compile time that state capacity cannot be cloned, dropped, or leaked.
public export
stagedStepUniverseLQTT : {vm, de, dm, k : Nat} ->
                         (1 qState : LinearLift (UniverseState vm de dm)) ->
                         Lift (Vect k BoxInt) ->
                         LinearLift (UniverseState (vm + k) de (S dm))
stagedStepUniverseLQTT qState qMatter =
  quoteLinear (stepUniverseLinear (spliceLinear qState) (splice qMatter))

||| Staged evaluation of LQTT state transition:
public export
evalStagedStepUniverseLQTT : {vm, de, dm, k : Nat} ->
                             (1 qState : LinearLift (UniverseState vm de dm)) ->
                             Lift (Vect k BoxInt) ->
                             UniverseState (vm + k) de (S dm)
evalStagedStepUniverseLQTT qState qMatter =
  spliceLinear (stagedStepUniverseLQTT qState qMatter)

||| 2LTT Staged Triad Genesis Specialization under strict LQTT linearity:
public export
stagedStepGenesisTriadLQTT : {vm, de, dm, kR, kG, kB : Nat} ->
                             (1 qState : LinearLift (UniverseState vm de dm)) ->
                             Lift (Vect kR BoxInt) ->
                             Lift (Vect kG BoxInt) ->
                             Lift (Vect kB BoxInt) ->
                             LinearLift (UniverseState (((vm + kR) + kG) + kB) de (S (S (S dm))))
stagedStepGenesisTriadLQTT qState qR qG qB =
  stagedStepUniverseLQTT (stagedStepUniverseLQTT (stagedStepUniverseLQTT qState qR) qG) qB

||| Staged evaluation of Triad Genesis under strict LQTT linearity:
public export
evalStagedStepGenesisTriadLQTT : {vm, de, dm, kR, kG, kB : Nat} ->
                                 (1 qState : LinearLift (UniverseState vm de dm)) ->
                                 Lift (Vect kR BoxInt) ->
                                 Lift (Vect kG BoxInt) ->
                                 Lift (Vect kB BoxInt) ->
                                 UniverseState (((vm + kR) + kG) + kB) de (S (S (S dm)))
evalStagedStepGenesisTriadLQTT qState qR qG qB =
  spliceLinear (stagedStepGenesisTriadLQTT qState qR qG qB)

||| QTT 0 Erased Proof Witness: Triad Genesis Staged Equivalence
public export
0 prfStagedStepGenesisTriadLQTT : {vm, de, dm, kR, kG, kB : Nat} ->
                                 (state : UniverseState vm de dm) ->
                                 (mR : Vect kR BoxInt) ->
                                 (mG : Vect kG BoxInt) ->
                                 (mB : Vect kB BoxInt) ->
                                 spliceLinear (stagedStepGenesisTriadLQTT (quoteLinear state) (quote mR) (quote mG) (quote mB)) =
                                   stepUniverseLinear (stepUniverseLinear (stepUniverseLinear state mR) mG) mB
prfStagedStepGenesisTriadLQTT _ _ _ _ = Refl

------------------------------------------------------------------------
-- 1B. THE LINEAR 2LTT COSMOLOGICAL TRAJECTORY ALGEBRA (LQTTTrajectory)
------------------------------------------------------------------------

||| An inductive algebraic specification of cosmological evolution:
||| Encapsulates an arbitrary sequence of matter injections under linear state evolution,
||| indexed by initial configuration (vm, de, dm) and final configuration (vm', dm').
public export
data UniverseTrajectory : (vm : Nat) -> (de : Nat) -> (dm : Nat) -> (vm' : Nat) -> (dm' : Nat) -> Type where
  IdTrajectory   : UniverseTrajectory vm de dm vm dm
  StepTrajectory : {vm, de, dm, vm', dm', k : Nat} ->
                   UniverseTrajectory vm de dm vm' dm' ->
                   Vect k BoxInt ->
                   UniverseTrajectory vm de dm (vm' + k) (S dm')

||| Helper to construct a single-step trajectory from an initial universe state:
public export
singleStepTrajectory : {vm, de, dm, k : Nat} -> Vect k BoxInt -> UniverseTrajectory vm de dm (vm + k) (S dm)
singleStepTrajectory m = StepTrajectory IdTrajectory m

||| Linearly executes an entire cosmological trajectory under strict QTT linearity (multiplicity 1):
public export
runTrajectoryLinear : {vm, de, dm, vm', dm' : Nat} ->
                      (1 state : UniverseState vm de dm) ->
                      UniverseTrajectory vm de dm vm' dm' ->
                      UniverseState vm' de dm'
runTrajectoryLinear state IdTrajectory = state
runTrajectoryLinear state (StepTrajectory rest m) =
  stepUniverseLinear (runTrajectoryLinear state rest) m

||| 2LTT Staged Linear Trajectory Runner under strict LQTT linearity:
||| Consumes the linear state and the lifted trajectory at Level 1 with zero runtime overhead.
public export
stagedRunTrajectoryLQTT : {vm, de, dm, vm', dm' : Nat} ->
                          (1 qState : LinearLift (UniverseState vm de dm)) ->
                          Lift (UniverseTrajectory vm de dm vm' dm') ->
                          LinearLift (UniverseState vm' de dm')
stagedRunTrajectoryLQTT qState qTraj =
  quoteLinear (runTrajectoryLinear (spliceLinear qState) (splice qTraj))

||| Staged evaluation of cosmological trajectory:
public export
evalStagedRunTrajectoryLQTT : {vm, de, dm, vm', dm' : Nat} ->
                              (1 qState : LinearLift (UniverseState vm de dm)) ->
                              Lift (UniverseTrajectory vm de dm vm' dm') ->
                              UniverseState vm' de dm'
evalStagedRunTrajectoryLQTT qState qTraj =
  spliceLinear (stagedRunTrajectoryLQTT qState qTraj)

||| QTT 0 Erased Proof Witness: Trajectory Execution Invariant
public export
0 prfStagedRunTrajectoryLQTT : {vm, de, dm, vm', dm' : Nat} ->
                              (state : UniverseState vm de dm) ->
                              (traj : UniverseTrajectory vm de dm vm' dm') ->
                              spliceLinear (stagedRunTrajectoryLQTT (quoteLinear state) (quote traj)) =
                                runTrajectoryLinear state traj
prfStagedRunTrajectoryLQTT _ _ = Refl

||| Linear 2LTT (LQTT) Direct Linear Staged Transition:
public export
stagedStepUniverseDirectLQTT : {vm, de, dm, k : Nat} ->
                               (1 state : UniverseState vm de dm) ->
                               Lift (Vect k BoxInt) ->
                               UniverseState (vm + k) de (S dm)
stagedStepUniverseDirectLQTT state qMatter =
  stepUniverseLinear state (splice qMatter)

||| 2LTT Staged Two-Step Unfolded State Transition:
||| Statically sequences two consecutive matter injections at Level 1 without intermediate heap allocations.
%inline public export
stagedStepUniverse2 : {vm, de, dm, k1, k2 : Nat} ->
                      Lift (UniverseState vm de dm) ->
                      Lift (Vect k1 BoxInt) ->
                      Lift (Vect k2 BoxInt) ->
                      Code (UniverseState ((vm + k1) + k2) de (S (S dm)))
stagedStepUniverse2 qState qM1 qM2 =
  stagedStepUniverseLinear (stagedStepUniverseLinear qState qM1) qM2

||| Staged evaluation of two-step unfolded state transition:
%inline public export
evalStagedStepUniverse2 : {vm, de, dm, k1, k2 : Nat} ->
                          Lift (UniverseState vm de dm) ->
                          Lift (Vect k1 BoxInt) ->
                          Lift (Vect k2 BoxInt) ->
                          UniverseState ((vm + k1) + k2) de (S (S dm))
evalStagedStepUniverse2 qState qM1 qM2 =
  splice (stagedStepUniverse2 qState qM1 qM2)

||| QTT 0 Erased Proof Witness: Staged Two-Step Invariant
public export
0 prfStagedStepUniverse2 : {vm, de, dm, k1, k2 : Nat} ->
                           (state : UniverseState vm de dm) ->
                           (m1 : Vect k1 BoxInt) ->
                           (m2 : Vect k2 BoxInt) ->
                           splice (stagedStepUniverse2 (quote state) (quote m1) (quote m2)) =
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
                      Code (UniverseState (((vm + k1) + k2) + k3) de (S (S (S dm))))
stagedStepUniverse3 qState qM1 qM2 qM3 =
  stagedStepUniverseLinear (stagedStepUniverse2 qState qM1 qM2) qM3

||| Staged evaluation of three-step unfolded state transition:
%inline public export
evalStagedStepUniverse3 : {vm, de, dm, k1, k2, k3 : Nat} ->
                          Lift (UniverseState vm de dm) ->
                          Lift (Vect k1 BoxInt) ->
                          Lift (Vect k2 BoxInt) ->
                          Lift (Vect k3 BoxInt) ->
                          UniverseState (((vm + k1) + k2) + k3) de (S (S (S dm)))
evalStagedStepUniverse3 qState qM1 qM2 qM3 =
  splice (stagedStepUniverse3 qState qM1 qM2 qM3)

||| QTT 0 Erased Proof Witness: Staged Three-Step Invariant
public export
0 prfStagedStepUniverse3 : {vm, de, dm, k1, k2, k3 : Nat} ->
                           (state : UniverseState vm de dm) ->
                           (m1 : Vect k1 BoxInt) ->
                           (m2 : Vect k2 BoxInt) ->
                           (m3 : Vect k3 BoxInt) ->
                           splice (stagedStepUniverse3 (quote state) (quote m1) (quote m2) (quote m3)) =
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
                          Code (LinearBuffer capacity)
stagedWriteLinearBuffer qBuf qIdx qVal =
  quote (writeLinearBuffer (splice qBuf) (splice qIdx) (splice qVal))

||| Staged evaluation of linear buffer write:
%inline public export
evalStagedWriteLinearBuffer : {capacity : Nat} ->
                              Lift (LinearBuffer capacity) ->
                              Lift (Fin capacity) ->
                              Lift BoxInt ->
                              LinearBuffer capacity
evalStagedWriteLinearBuffer qBuf qIdx qVal =
  splice (stagedWriteLinearBuffer qBuf qIdx qVal)

||| QTT 0 Erased Proof Witness: Staged Buffer Write Invariant
public export
0 prfStagedWriteLinearBuffer : {capacity : Nat} ->
                              (buf : LinearBuffer capacity) ->
                              (idx : Fin capacity) ->
                              (val : BoxInt) ->
                              splice (stagedWriteLinearBuffer (quote buf) (quote idx) (quote val)) = writeLinearBuffer buf idx val
prfStagedWriteLinearBuffer _ _ _ = Refl
