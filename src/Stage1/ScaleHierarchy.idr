module Stage1.ScaleHierarchy

import Stage0.BoxInt
import Stage0.Multiset
import Stage1.UnixelFraction
import Stage1.MaxelTransform
import Stage1.TypeTheory.Staging
import Stage1.TypeTheory.TwoLevel

%default total

------------------------------------------------------------------------
-- 1. HIERARCHY OF PHYSICAL SCALE LEVELS
------------------------------------------------------------------------

||| Discrete physical scale levels across the universe hierarchy.
public export
data ScaleLevel = SubatomicLevel | HadronLevel | AtomLevel | MoleculeLevel | CellLevel

public export
Eq ScaleLevel where
  SubatomicLevel == SubatomicLevel = True
  HadronLevel == HadronLevel = True
  AtomLevel == AtomLevel = True
  MoleculeLevel == MoleculeLevel = True
  CellLevel == CellLevel = True
  _ == _ = False

||| A ScaleTransition represents a discrete multiset matrix transform between scale levels.
||| In 2LTT, this replaces abstract category-theoretic functors with concrete Maxel transforms.
public export
record ScaleTransition (src : ScaleLevel) (tgt : ScaleLevel) (srcToken : Type) (tgtToken : Type) where
  constructor MkScaleTransition
  transform : MaxelTransform srcToken tgtToken

||| Identity scale transition for a scale level.
public export
identityScaleTransition : {0 srcToken : Type} -> ScaleTransition src src srcToken srcToken
identityScaleTransition = MkScaleTransition (mkMaxelTransform EllipticSector (mkUnixelFraction (intToBoxInt 1) 1) [])

||| Sequential composition of discrete scale transitions.
public export
composeScaleTransitions : {0 a, b, c : ScaleLevel} ->
                          {0 tokA, tokB, tokC : Type} ->
                          (Eq tokA, Eq tokB, Eq tokC) =>
                          ScaleTransition a b tokA tokB ->
                          ScaleTransition b c tokB tokC ->
                          ScaleTransition a c tokA tokC
composeScaleTransitions (MkScaleTransition f) (MkScaleTransition g) =
  MkScaleTransition (composeMaxels f g)

||| 2LTT Staged Scale Transition constructor:
||| Lifts a static matrix transform into a staged scale transition code block at Level 1.
%inline public export
stagedScaleTransition : {src, tgt : ScaleLevel} ->
                        Lift (MaxelTransform srcToken tgtToken) ->
                        Code (ScaleTransition src tgt srcToken tgtToken)
stagedScaleTransition qM = quote (MkScaleTransition (splice qM))

||| Staged evaluation of scale transition:
%inline public export
evalStagedScaleTransition : {src, tgt : ScaleLevel} ->
                            Lift (MaxelTransform srcToken tgtToken) ->
                            ScaleTransition src tgt srcToken tgtToken
evalStagedScaleTransition qM = splice (stagedScaleTransition qM)

||| 2LTT Staged Composition of Scale Transitions:
||| Fuses two sequential scale transitions at Level 1 without intermediate splices.
public export
stagedComposeScaleTransitions : {0 a, b, c : ScaleLevel} ->
                                {0 tokA, tokB, tokC : Type} ->
                                (Eq tokA, Eq tokB, Eq tokC) =>
                                Lift (ScaleTransition a b tokA tokB) ->
                                Lift (ScaleTransition b c tokB tokC) ->
                                Code (ScaleTransition a c tokA tokC)
stagedComposeScaleTransitions qT1 qT2 =
  quote (composeScaleTransitions (splice qT1) (splice qT2))

||| Staged evaluation of composed scale transitions:
public export
evalStagedComposeScaleTransitions : {0 a, b, c : ScaleLevel} ->
                                    {0 tokA, tokB, tokC : Type} ->
                                    (Eq tokA, Eq tokB, Eq tokC) =>
                                    Lift (ScaleTransition a b tokA tokB) ->
                                    Lift (ScaleTransition b c tokB tokC) ->
                                    ScaleTransition a c tokA tokC
evalStagedComposeScaleTransitions qT1 qT2 = splice (stagedComposeScaleTransitions qT1 qT2)

||| QTT 0 Erased Proof Witness: Staged Scale Transition Invariant
public export
0 prfStagedScaleTransition : {src, tgt : ScaleLevel} ->
                             (m : MaxelTransform srcToken tgtToken) ->
                             splice (stagedScaleTransition (quote m)) = MkScaleTransition m
prfStagedScaleTransition _ = Refl

||| QTT 0 Erased Proof Witness: Staged Composed Scale Transitions Invariant
public export
0 prfStagedComposeScaleTransitions : {0 a, b, c : ScaleLevel} ->
                                     {0 tokA, tokB, tokC : Type} ->
                                     (Eq tokA, Eq tokB, Eq tokC) =>
                                     (t1 : ScaleTransition a b tokA tokB) ->
                                     (t2 : ScaleTransition b c tokB tokC) ->
                                     splice (stagedComposeScaleTransitions (quote t1) (quote t2)) =
                                       composeScaleTransitions t1 t2
prfStagedComposeScaleTransitions _ _ = Refl

------------------------------------------------------------------------
-- 2. THE CATEGORICAL SCALE PATH ALGEBRA (Path(Scale))
------------------------------------------------------------------------

||| An inductive path in the small category of scale transitions:
||| Represents the free category Path(Scale) generated by discrete scale transitions.
public export
data ScalePath : ScaleLevel -> ScaleLevel -> Type -> Type -> Type where
  IdScalePath   : (0 a : ScaleLevel) -> (0 tok : Type) -> ScalePath a a tok tok
  StepScalePath : {0 a, b, c : ScaleLevel} -> {0 tokA, tokB, tokC : Type} ->
                  (Eq tokA, Eq tokB, Eq tokC) =>
                  ScaleTransition a b tokA tokB ->
                  ScalePath b c tokB tokC ->
                  ScalePath a c tokA tokC

||| Single-step path helper constructor:
public export
singleStepPath : {0 a, b : ScaleLevel} -> {0 tokA, tokB : Type} ->
                 (Eq tokA, Eq tokB) =>
                 ScaleTransition a b tokA tokB -> ScalePath a b tokA tokB
singleStepPath tr = StepScalePath tr (IdScalePath _ _)

||| Evaluates and collapses a ScalePath into a single composite ScaleTransition:
public export
collapseScalePath : {0 a, b : ScaleLevel} -> {0 tokA, tokB : Type} ->
                    (Eq tokA, Eq tokB) =>
                    ScalePath a b tokA tokB ->
                    ScaleTransition a b tokA tokB
collapseScalePath (IdScalePath a tok) = identityScaleTransition
collapseScalePath (StepScalePath tr (IdScalePath _ _)) = tr
collapseScalePath (StepScalePath tr (StepScalePath tr2 rest)) =
  composeScaleTransitions tr (collapseScalePath (StepScalePath tr2 rest))

||| 2LTT Staged Scale Path Compiler:
||| Folds an entire multi-scale path into a single composite ScaleTransition at Level 1,
||| producing zero runtime intermediate allocations.
public export
stagedCompileScalePath : {0 a, b : ScaleLevel} -> {0 tokA, tokB : Type} ->
                         (Eq tokA, Eq tokB) =>
                         Lift (ScalePath a b tokA tokB) ->
                         Code (ScaleTransition a b tokA tokB)
stagedCompileScalePath qPath =
  quote (collapseScalePath (splice qPath))

||| Staged evaluation of scale path:
public export
evalStagedCompileScalePath : {0 a, b : ScaleLevel} -> {0 tokA, tokB : Type} ->
                             (Eq tokA, Eq tokB) =>
                             Lift (ScalePath a b tokA tokB) ->
                             ScaleTransition a b tokA tokB
evalStagedCompileScalePath qPath =
  splice (stagedCompileScalePath qPath)

||| QTT 0 Erased Proof Witness: Scale Path Compilation Invariance
public export
0 prfStagedCompileScalePath : {0 a, b : ScaleLevel} -> {0 tokA, tokB : Type} ->
                             (Eq tokA, Eq tokB) =>
                             (p : ScalePath a b tokA tokB) ->
                             splice (stagedCompileScalePath (quote p)) = collapseScalePath p
prfStagedCompileScalePath _ = Refl

