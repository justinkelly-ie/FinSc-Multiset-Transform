module Stage1.UniverseState

import Data.Vect
import Stage0.BoxInt
import Stage0.UniverseState
import Stage1.TypeTheory.Smoothness

%default total

------------------------------------------------------------------------
-- 1. TYPE-LEVEL BOUNDED UNIVERSE STATE
------------------------------------------------------------------------

||| A UniverseState whose total capacity (vm + de + dm) is certified under a prime bound at compile time.
public export
record UniverseState (bound : Nat) (vm : Nat) (de : Nat) (dm : Nat) where
  constructor MkUniverseState
  state         : Stage0.UniverseState.UniverseState vm de dm
  capacityProof : DimensionWitness bound (vm + de + dm)

public export
{bound, vm, de, dm : Nat} -> Eq (UniverseState bound vm de dm) where
  (MkUniverseState s1 _) == (MkUniverseState s2 _) =
    visibleMatter s1 == visibleMatter s2 &&
    darkEnergy s1 == darkEnergy s2 &&
    darkMatter s1 == darkMatter s2

public export
{bound, vm, de, dm : Nat} -> Show (UniverseState bound vm de dm) where
  show (MkUniverseState _ _) = "UniverseState(" ++ show bound ++ ", " ++ show (vm + de + dm) ++ ")"

||| Projects the verified capacity dimension from the universe state.
public export
0 dimension : UniverseState bound vm de dm -> Dimension bound
dimension (MkUniverseState _ (MkDimensionWitness prf)) = ((vm + de + dm) ** prf)

||| Extracts the dimension witness record from the universe state.
public export
dimensionWitness : UniverseState bound vm de dm -> DimensionWitness bound (vm + de + dm)
dimensionWitness (MkUniverseState _ w) = w

||| Constructs a UniverseState by supplying a compile-time SmoothWitness for any prime bound.
public export
seedCosmicVacuumBounded : (bound : Nat) -> (vm : Nat) -> (de : Nat) -> (dm : Nat) -> SmoothWitness bound (vm + de + dm) -> UniverseState bound vm de dm
seedCosmicVacuumBounded bound vm de dm prf =
  MkUniverseState (seedCosmicVacuum vm de dm) (MkDimensionWitness prf)

------------------------------------------------------------------------
-- 2. CANONICAL COSMIC UNIVERSE STATE (Law of Coherent Matter)
------------------------------------------------------------------------

||| Canonical cosmological 13-horizon universe state carrier.
public export
CosmicUniverseState : (vm : Nat) -> (de : Nat) -> (dm : Nat) -> Type
CosmicUniverseState = UniverseState CosmicSmoothHorizon

||| Constructs a canonical CosmicUniverseState with compile-time 13-horizon witness.
public export
seedCosmicVacuumCertified : (vm : Nat) -> (de : Nat) -> (dm : Nat) -> SmoothWitness CosmicSmoothHorizon (vm + de + dm) -> CosmicUniverseState vm de dm
seedCosmicVacuumCertified vm de dm prf =
  seedCosmicVacuumBounded CosmicSmoothHorizon vm de dm prf

||| Canonical Primorial 210 Ground State (27 VM, 128 DE, 55 DM, unique F = -1320 minimum).
public export
seedPrimorialGroundState : CosmicUniverseState 27 128 55
seedPrimorialGroundState = seedCosmicVacuumCertified 27 128 55 prfSmooth210
