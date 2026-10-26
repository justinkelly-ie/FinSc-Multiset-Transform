module Stage1.StratifiedState

import Data.Vect
import Data.Fin
import Stage0.BoxInt
import Stage0.WitnessLedger
import Stage0.UniverseState
import Stage1.Basis.Coordinate
import Stage1.TypeTheory.TwoLevel
import Stage1.TypeTheory.Smoothness
import Stage1.UniverseState

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
totalCosmicMultisetBudget (MkCosmicMultiset vm de dm) =
  foldBoxTreeL (\acc, _ => S acc) 0 vm +
  foldBoxTreeL (\acc, _ => S acc) 0 de +
  foldBoxTreeL (\acc, _ => S acc) 0 dm

||| Embeds a Stage0 UniverseState into the CosmicMultiset.
public export
stateToCosmicMultiset : {vm, de, dm : Nat} -> Stage0.UniverseState.UniverseState vm de dm -> CosmicMultiset
stateToCosmicMultiset (MkUniverseState vmVect deVect dmVect) =
  let vmTree = foldVectWithFin (\idx, w, acc => if boxIsZero w then acc else setBoxTree (mkCell3 (finToNat idx + 1) 1 1) w acc) BoxLeaf vmVect
      deTree = foldVectWithFin (\idx, w, acc => if boxIsZero w then acc else setBoxTree (mkCell2 (finToNat idx + 1) 1) w acc) BoxLeaf deVect
      dmTree = foldVectWithFin (\idx, w, acc => if boxIsZero w then acc else setBoxTree (mkCell1 (finToNat idx + 1)) w acc) BoxLeaf dmVect
  in MkCosmicMultiset vmTree deTree dmTree
  where
    foldVectWithFin : {n : Nat} -> (Fin n -> a -> acc -> acc) -> acc -> Vect n a -> acc
    foldVectWithFin {n = Z} _ init [] = init
    foldVectWithFin {n = S k} f init (x :: xs) =
      let acc' = f FZ x init
      in foldVectWithFin (\fin, v, a => f (FS fin) v a) acc' xs

------------------------------------------------------------------------
-- 2LTT SUBFIBRATION STATE STRATIFICATION & QTT 0 BUDGET CONSERVATION
------------------------------------------------------------------------

||| 2LTT Subfibration State Wrapping for certified UniverseState, linking strict deforested outer states
||| and inner physical homotopy manifolds under zero runtime memory cost.
public export
record StratifiedUniverseState (bound : Nat) (vm : Nat) (de : Nat) (dm : Nat) where
  constructor MkStratifiedUniverseState
  strictState   : StrictLevel (UniverseState bound vm de dm)
  homotopyState : HomotopyLevel (UniverseState bound vm de dm)

||| Constructs a 2LTT StratifiedUniverseState from a certified UniverseState.
public export
mkStratifiedUniverseState : UniverseState bound vm de dm -> StratifiedUniverseState bound vm de dm
mkStratifiedUniverseState st = MkStratifiedUniverseState (MkStrict st) (MkHomotopy st)

||| Equality compares only the strict (runtime) inner UniverseState contents.
public export
{bound, vm, de, dm : Nat} -> Eq (StratifiedUniverseState bound vm de dm) where
  (MkStratifiedUniverseState (MkStrict s1) _) == (MkStratifiedUniverseState (MkStrict s2) _) = s1 == s2

public export
{bound, vm, de, dm : Nat} -> Show (StratifiedUniverseState bound vm de dm) where
  show (MkStratifiedUniverseState _ _) = "StratifiedUniverseState(" ++ show bound ++ ", " ++ show (vm + de + dm) ++ ")"

||| Canonical 13-horizon stratified universe state carrier.
public export
CosmicStratifiedUniverseState : (vm : Nat) -> (de : Nat) -> (dm : Nat) -> Type
CosmicStratifiedUniverseState = StratifiedUniverseState CosmicSmoothHorizon

||| Canonical Primorial 210 Stratified Ground State.
public export
primorialStratifiedGroundState : CosmicStratifiedUniverseState 27 128 55
primorialStratifiedGroundState = mkStratifiedUniverseState seedPrimorialGroundState

||| QTT 0 erased proof witness verifying Primorial 210 Cosmic Multiset Budget Conservation (27 + 128 + 55 = 210).
public export
0 prfCosmicMultisetBudgetConservation :
  addBox (intToBoxInt 27) (addBox (intToBoxInt 128) (intToBoxInt 55)) = intToBoxInt 210
prfCosmicMultisetBudgetConservation = Refl

