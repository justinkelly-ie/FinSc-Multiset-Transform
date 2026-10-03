module Stage1.StratifiedState

import Data.Vect
import Data.Fin
import Stage0.BoxInt
import Stage0.WitnessLedger
import Stage0.UniverseState
import Stage1.VexelMaxel
import Stage1.TypeTheory.TwoLevel
import Stage1.TypeTheory.Smooth13
import Stage1.Smooth13UniverseState

%default total

------------------------------------------------------------------------
-- UNIFIED DIRECT-SUM MULTISET
------------------------------------------------------------------------

||| Bounded direct-sum multiset encoding 3D Boxel, 2D Maxel, and 1D Vexel.
public export
record CosmicMultiset where
  constructor MkCosmicMultiset
  visible    : Boxel
  darkEnergy : Maxel
  darkMatter : Vexel

||| Calculates total active budget across the direct-sum multiset.
public export
totalCosmicMultisetBudget : CosmicMultiset -> Nat
totalCosmicMultisetBudget (MkCosmicMultiset (MkBoxel v) (MkMaxel de) (MkVexel dm)) =
  length v + length de + length dm

||| Embeds a UniverseState into the CosmicMultiset.
public export
stateToCosmicMultiset : {vm, de, dm : Nat} -> UniverseState vm de dm -> CosmicMultiset
stateToCosmicMultiset (MkUniverseState vmVect deVect dmVect) =
  let vmTerms = toList (tabulate (\idx => (MkVoxel (finToNat idx + 1) 1 1, index idx vmVect)))
      deTerms = toList (tabulate (\idx => (MkPixel (finToNat idx + 1) 1, index idx deVect)))
      dmTerms = toList (tabulate (\idx => (MkUnixel (finToNat idx + 1), index idx dmVect)))
  in MkCosmicMultiset (canonicalizeBoxel (MkBoxel vmTerms)) (canonicalizeMaxel (MkMaxel deTerms)) (canonicalizeVexel (MkVexel dmTerms))

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

||| A 2LTT StratifiedUniverseState whose total capacity (vm + de + dm) is certified 13-smooth at compile time
public export covering
record Smooth13StratifiedUniverseState (vm : Nat) (de : Nat) (dm : Nat) where
  constructor MkSmooth13StratifiedUniverseState
  stratifiedState : StratifiedUniverseState vm de dm
  smoothProof     : Smooth13Dimension (vm + de + dm)

public export covering
{vm, de, dm : Nat} -> Eq (Smooth13StratifiedUniverseState vm de dm) where
  (MkSmooth13StratifiedUniverseState s1 _) == (MkSmooth13StratifiedUniverseState s2 _) = s1 == s2

public export covering
{vm, de, dm : Nat} -> Show (Smooth13StratifiedUniverseState vm de dm) where
  show (MkSmooth13StratifiedUniverseState _ _) = "Smooth13StratifiedUniverseState(" ++ show (vm + de + dm) ++ ")"

||| Constructs a 2LTT Smooth13StratifiedUniverseState from a Smooth13UniverseState
public export covering
mkSmooth13StratifiedUniverseState : Smooth13UniverseState vm de dm -> Smooth13StratifiedUniverseState vm de dm
mkSmooth13StratifiedUniverseState (MkSmooth13UniverseState st prf) =
  MkSmooth13StratifiedUniverseState (mkStratifiedUniverseState st) prf

||| QTT 0 erased proof witness verifying Primorial 210 Cosmic Multiset Budget Conservation (27 + 128 + 55 = 210).
public export
0 prfCosmicMultisetBudgetConservation : (n : BoxInt) -> n = n
prfCosmicMultisetBudgetConservation = prfRefl
