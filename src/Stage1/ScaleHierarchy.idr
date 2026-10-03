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

------------------------------------------------------------------------
-- BACKWARDS COMPATIBILITY ALIASES FOR CATEGORY-THEORETIC NAMES
------------------------------------------------------------------------

||| @deprecated ScaleFunctor record preserved for 100% backwards compatibility with pattern matches.
||| Use ScaleTransition for new 2LTT code.
public export
record ScaleFunctor (src : ScaleLevel) (tgt : ScaleLevel) (srcToken : Type) (tgtToken : Type) where
  constructor MkScaleFunctor
  transform : MaxelTransform srcToken tgtToken

public export
toScaleTransition : ScaleFunctor src tgt a b -> ScaleTransition src tgt a b
toScaleTransition (MkScaleFunctor t) = MkScaleTransition t

public export
fromScaleTransition : ScaleTransition src tgt a b -> ScaleFunctor src tgt a b
fromScaleTransition (MkScaleTransition t) = MkScaleFunctor t

||| @deprecated Use identityScaleTransition.
public export
identityScaleFunctor : {0 srcToken : Type} -> ScaleFunctor src src srcToken srcToken
identityScaleFunctor = MkScaleFunctor (mkMaxelTransform EllipticSector (mkUnixelFraction (intToBoxInt 1) 1) [])

||| @deprecated Use composeScaleTransitions.
public export
composeScaleFunctors : {0 a, b, c : ScaleLevel} ->
                       {0 tokA, tokB, tokC : Type} ->
                       (Eq tokA, Eq tokB, Eq tokC) =>
                       ScaleFunctor a b tokA tokB ->
                       ScaleFunctor b c tokB tokC ->
                       ScaleFunctor a c tokA tokC
composeScaleFunctors (MkScaleFunctor f) (MkScaleFunctor g) =
  MkScaleFunctor (composeMaxels f g)

