module Stage1.SmoothUniverseState

import Data.Vect
import Stage0.BoxInt
import Stage0.UniverseState
import Stage1.TypeTheory.Smoothness

%default total

------------------------------------------------------------------------
-- TYPE-LEVEL SMOOTH BOUNDED UNIVERSE STATE
------------------------------------------------------------------------

||| A UniverseState whose total capacity (vm + de + dm) is certified smooth up to bound at compile time.
public export
record SmoothUniverseState (bound : Nat) (vm : Nat) (de : Nat) (dm : Nat) where
  constructor MkSmoothUniverseState
  state       : UniverseState vm de dm
  smoothProof : SmoothDimensionWitness bound (vm + de + dm)

public export
{bound, vm, de, dm : Nat} -> Eq (SmoothUniverseState bound vm de dm) where
  (MkSmoothUniverseState s1 _) == (MkSmoothUniverseState s2 _) =
    visibleMatter s1 == visibleMatter s2 &&
    darkEnergy s1 == darkEnergy s2 &&
    darkMatter s1 == darkMatter s2

public export
{bound, vm, de, dm : Nat} -> Show (SmoothUniverseState bound vm de dm) where
  show (MkSmoothUniverseState _ _) = "SmoothUniverseState(" ++ show bound ++ ", " ++ show (vm + de + dm) ++ ")"

||| Constructs a SmoothUniverseState by supplying a compile-time SmoothWitness for any prime bound.
public export
seedSmoothVacuumBounded : (bound : Nat) -> (vm : Nat) -> (de : Nat) -> (dm : Nat) -> SmoothWitness bound (vm + de + dm) -> SmoothUniverseState bound vm de dm
seedSmoothVacuumBounded bound vm de dm prf =
  MkSmoothUniverseState (seedCosmicVacuum vm de dm) (MkSmoothDimensionWitness prf)

------------------------------------------------------------------------
-- CANONICAL 13-SMOOTH COSMIC UNIVERSE STATE (Law of Coherent Matter)
------------------------------------------------------------------------

||| Canonical cosmological 13-smooth universe state carrier.
public export
CosmicSmoothUniverseState : (vm : Nat) -> (de : Nat) -> (dm : Nat) -> Type
CosmicSmoothUniverseState = SmoothUniverseState CosmicSmoothHorizon

||| Constructs a canonical CosmicSmoothUniverseState with compile-time 13-smooth witness.
public export
seedSmoothCosmicVacuum : (vm : Nat) -> (de : Nat) -> (dm : Nat) -> SmoothWitness CosmicSmoothHorizon (vm + de + dm) -> CosmicSmoothUniverseState vm de dm
seedSmoothCosmicVacuum vm de dm prf =
  seedSmoothVacuumBounded CosmicSmoothHorizon vm de dm prf

------------------------------------------------------------------------
-- BACKWARD-COMPATIBILITY ALIASES
------------------------------------------------------------------------

||| Backward-compatible alias for CosmicSmoothUniverseState.
public export
Smooth13UniverseState : (vm : Nat) -> (de : Nat) -> (dm : Nat) -> Type
Smooth13UniverseState = CosmicSmoothUniverseState

||| Backward-compatible constructor alias.
public export
mkSmooth13UniverseState : UniverseState vm de dm -> SmoothDimensionWitness CosmicSmoothHorizon (vm + de + dm) -> Smooth13UniverseState vm de dm
mkSmooth13UniverseState st prf = MkSmoothUniverseState st prf
