module Stage1.StratifiedState

import Data.Vect
import Data.Fin
import Stage0.BoxInt
import Stage0.WitnessLedger
import Stage0.UniverseState
import Stage1.VexelMaxel
import Stage1.TypeTheory.TwoLevel
import Stage1.TypeTheory.Smoothness
import Stage1.SmoothUniverseState

%default total

------------------------------------------------------------------------
-- UNIFIED DIRECT-SUM MULTISET
------------------------------------------------------------------------

||| Bounded direct-sum multiset encoding 3D Boxel, 2D Maxel, and 1D Vexel.
public export
record CosmicMultiset where
  constructor MkCosmicMultiset
  visible    : Boxel
  darkEnergy : Stage1.VexelMaxel.Maxel
  darkMatter : Vexel

||| Calculates total active budget across the direct-sum multiset.
public export
totalCosmicMultisetBudget : CosmicMultiset -> Nat
totalCosmicMultisetBudget (MkCosmicMultiset (MkBoxel v) (Stage1.VexelMaxel.MkMaxel de) (MkVexel dm)) =
  length v + length de + length dm

||| Embeds a UniverseState into the CosmicMultiset.
public export
stateToCosmicMultiset : {vm, de, dm : Nat} -> UniverseState vm de dm -> CosmicMultiset
stateToCosmicMultiset (MkUniverseState vmVect deVect dmVect) =
  let vmTerms = toList (tabulate (\idx => (MkVoxel (finToNat idx + 1) 1 1, index idx vmVect)))
      deTerms = toList (tabulate (\idx => (MkPixel (finToNat idx + 1) 1, index idx deVect)))
      dmTerms = toList (tabulate (\idx => (MkUnixel (finToNat idx + 1), index idx dmVect)))
  in MkCosmicMultiset (canonicalizeBoxel (MkBoxel vmTerms)) (canonicalizeMaxel (Stage1.VexelMaxel.MkMaxel deTerms)) (canonicalizeVexel (MkVexel dmTerms))

------------------------------------------------------------------------
-- 2LTT SUBFIBRATION STATE STRATIFICATION & QTT 0 BUDGET CONSERVATION
------------------------------------------------------------------------

||| 2LTT Subfibration State Wrapping for UniverseState, linking strict deforested outer states
||| and inner physical homotopy manifolds under zero runtime memory cost.
public export
record StratifiedUniverseState (vm : Nat) (de : Nat) (dm : Nat) where
  constructor MkStratifiedUniverseState
  strictState   : StrictLevel (UniverseState vm de dm)
  homotopyState : HomotopyLevel (UniverseState vm de dm)

||| Constructs a 2LTT StratifiedUniverseState from a concrete UniverseState.
public export
mkStratifiedUniverseState : UniverseState vm de dm -> StratifiedUniverseState vm de dm
mkStratifiedUniverseState st = MkStratifiedUniverseState (MkStrict st) (MkHomotopy st)

||| Equality compares only the strict (runtime) inner UniverseState contents.
public export
{vm, de, dm : Nat} -> Eq (StratifiedUniverseState vm de dm) where
  (MkStratifiedUniverseState (MkStrict s1) _) == (MkStratifiedUniverseState (MkStrict s2) _) =
    s1.visibleMatter == s2.visibleMatter &&
    s1.darkEnergy    == s2.darkEnergy    &&
    s1.darkMatter    == s2.darkMatter

||| Executes a 2LTT stratified state transition preserving strict outer deforested evaluation.
public export
stepStratifiedUniverse : {vm, de, dm, k : Nat} ->
                         StratifiedUniverseState vm de dm ->
                         Vect k BoxInt ->
                         StratifiedUniverseState (vm + k) de (S dm)
stepStratifiedUniverse (MkStratifiedUniverseState (MkStrict st) _) newMatter =
  let updated = stepUniverseLinear st newMatter
  in mkStratifiedUniverseState updated

||| A 2LTT StratifiedUniverseState whose total capacity (vm + de + dm) is certified smooth at compile time
public export
record SmoothStratifiedUniverseState (bound : Nat) (vm : Nat) (de : Nat) (dm : Nat) where
  constructor MkSmoothStratifiedUniverseState
  stratifiedState : StratifiedUniverseState vm de dm
  smoothProof     : SmoothDimensionWitness bound (vm + de + dm)

public export
{bound, vm, de, dm : Nat} -> Eq (SmoothStratifiedUniverseState bound vm de dm) where
  (MkSmoothStratifiedUniverseState s1 _) == (MkSmoothStratifiedUniverseState s2 _) = s1 == s2

public export
{bound, vm, de, dm : Nat} -> Show (SmoothStratifiedUniverseState bound vm de dm) where
  show (MkSmoothStratifiedUniverseState _ _) = "SmoothStratifiedUniverseState(" ++ show bound ++ ", " ++ show (vm + de + dm) ++ ")"

||| Canonical 13-smooth stratified universe state carrier.
public export
CosmicSmoothStratifiedUniverseState : (vm : Nat) -> (de : Nat) -> (dm : Nat) -> Type
CosmicSmoothStratifiedUniverseState = SmoothStratifiedUniverseState CosmicSmoothHorizon

||| Constructs a 2LTT SmoothStratifiedUniverseState from a SmoothUniverseState
public export
mkSmoothStratifiedUniverseState : SmoothUniverseState bound vm de dm -> SmoothStratifiedUniverseState bound vm de dm
mkSmoothStratifiedUniverseState (MkSmoothUniverseState st prf) =
  MkSmoothStratifiedUniverseState (mkStratifiedUniverseState st) prf

------------------------------------------------------------------------
-- BACKWARD-COMPATIBILITY ALIASES
------------------------------------------------------------------------

public export
Smooth13StratifiedUniverseState : (vm : Nat) -> (de : Nat) -> (dm : Nat) -> Type
Smooth13StratifiedUniverseState = CosmicSmoothStratifiedUniverseState

public export
mkSmooth13StratifiedUniverseState : CosmicSmoothUniverseState vm de dm -> CosmicSmoothStratifiedUniverseState vm de dm
mkSmooth13StratifiedUniverseState = mkSmoothStratifiedUniverseState

||| QTT 0 erased proof witness verifying Primorial 210 Cosmic Multiset Budget Conservation (27 + 128 + 55 = 210).
public export
0 prfCosmicMultisetBudgetConservation :
  addBox (intToBoxInt 27) (addBox (intToBoxInt 128) (intToBoxInt 55)) = intToBoxInt 210
prfCosmicMultisetBudgetConservation = Refl
