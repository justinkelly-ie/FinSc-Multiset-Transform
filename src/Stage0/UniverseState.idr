module Stage0.UniverseState

import Data.Vect
import Stage0.BoxInt
import Stage1.TypeTheory.Smooth13

%default total

||| Bounded 3-pool discrete multiset state representation.
||| Dimensions are tracked relationally through dependent parameters.
||| All data slots store exact BoxInt discrete particle/quadrance tokens.
public export
record UniverseState (vmSize : Nat) (deSize : Nat) (dmSize : Nat) where
  constructor MkUniverseState
  visibleMatter : Vect vmSize BoxInt -- Active spatial field lattice
  darkEnergy    : Vect deSize BoxInt -- Background ROM capacity
  darkMatter    : Vect dmSize BoxInt -- Historical error/residue ledger

||| Extracts the residue log as a read-only reference.
public export
dmLog : UniverseState vm de dm -> Vect dm BoxInt
dmLog (MkUniverseState _ _ dmData) = dmData

||| Calculates total active state energy across all memory pools.
public export
totalStateCapacity : {vm, de, dm : Nat} -> UniverseState vm de dm -> Nat
totalStateCapacity {vm} {de} {dm} _ = vm + de + dm

||| Seed constructor for a vacuum state with 0 values across memory pools.
public export
seedCosmicVacuum : (vm : Nat) -> (de : Nat) -> (dm : Nat) -> UniverseState vm de dm
seedCosmicVacuum vm de dm = MkUniverseState (replicate vm (intToBoxInt 0)) (replicate de (intToBoxInt 0)) (replicate dm (intToBoxInt 0))

||| Linear vector combination appending two Vect states.
public export
linearVectCombine : Vect n a -> Vect m a -> Vect (n + m) a
linearVectCombine [] ys = ys
linearVectCombine (x :: xs) ys = x :: linearVectCombine xs ys

||| Strict QTT linear multiplicity state transition.
public export
stepUniverseLinear : {vm, de, dm, k : Nat} ->
                     (1 state : UniverseState vm de dm) ->
                     (newMatter : Vect k BoxInt) ->
                     UniverseState (vm + k) de (S dm)
stepUniverseLinear (MkUniverseState vm de dm) newMatter =
  let updatedVM = linearVectCombine vm newMatter
      updatedDM = (intToBoxInt 1) :: dm
  in MkUniverseState updatedVM de updatedDM

------------------------------------------------------------------------
-- 2. TYPE-LEVEL 13-SMOOTH BOUNDED UNIVERSE STATE
------------------------------------------------------------------------

||| A UniverseState whose total capacity (vm + de + dm) is certified 13-smooth at compile time
public export covering
record Smooth13UniverseState (vm : Nat) (de : Nat) (dm : Nat) where
  constructor MkSmooth13UniverseState
  state       : UniverseState vm de dm
  smoothProof : Smooth13Dimension (vm + de + dm)

public export covering
{vm, de, dm : Nat} -> Eq (Smooth13UniverseState vm de dm) where
  (MkSmooth13UniverseState s1 _) == (MkSmooth13UniverseState s2 _) =
    s1.visibleMatter == s2.visibleMatter &&
    s1.darkEnergy == s2.darkEnergy &&
    s1.darkMatter == s2.darkMatter

public export covering
{vm, de, dm : Nat} -> Show (Smooth13UniverseState vm de dm) where
  show (MkSmooth13UniverseState _ _) = "Smooth13UniverseState(" ++ show (vm + de + dm) ++ ")"

||| Seed constructor for a 13-smooth certified vacuum state
public export covering
seedSmoothCosmicVacuum : (vm : Nat) -> (de : Nat) -> (dm : Nat) -> Smooth13Witness (vm + de + dm) -> Smooth13UniverseState vm de dm
seedSmoothCosmicVacuum vm de dm prf =
  MkSmooth13UniverseState (seedCosmicVacuum vm de dm) (MkSmooth13Dimension {n=vm + de + dm} prf)
