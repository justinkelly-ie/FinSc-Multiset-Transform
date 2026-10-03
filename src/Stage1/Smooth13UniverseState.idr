module Stage1.Smooth13UniverseState

import Data.Vect
import Stage0.BoxInt
import Stage0.UniverseState
import Stage1.TypeTheory.Smooth13

%default total

------------------------------------------------------------------------
-- TYPE-LEVEL 13-SMOOTH BOUNDED UNIVERSE STATE
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
    visibleMatter s1 == visibleMatter s2 &&
    darkEnergy s1 == darkEnergy s2 &&
    darkMatter s1 == darkMatter s2

public export covering
{vm, de, dm : Nat} -> Show (Smooth13UniverseState vm de dm) where
  show (MkSmooth13UniverseState _ _) = "Smooth13UniverseState(" ++ show (vm + de + dm) ++ ")"

||| Constructs a Smooth13UniverseState by supplying a compile-time Smooth13Witness.
public export covering
seedSmoothCosmicVacuum : (vm : Nat) -> (de : Nat) -> (dm : Nat) -> Smooth13Witness (vm + de + dm) -> Smooth13UniverseState vm de dm
seedSmoothCosmicVacuum vm de dm prf =
  MkSmooth13UniverseState (seedCosmicVacuum vm de dm) (MkSmooth13Dimension {n=vm + de + dm} prf)
