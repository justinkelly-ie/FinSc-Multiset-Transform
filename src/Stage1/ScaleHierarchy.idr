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
||| Evaluates and splices static matrix transforms down to object-level scale transitions.
%inline public export
stagedScaleTransition : {src, tgt : ScaleLevel} ->
                        Lift (MaxelTransform srcToken tgtToken) ->
                        ScaleTransition src tgt srcToken tgtToken
stagedScaleTransition qM = MkScaleTransition (splice qM)

