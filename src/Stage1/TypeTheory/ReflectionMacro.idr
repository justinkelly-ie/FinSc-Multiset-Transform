module Stage1.TypeTheory.ReflectionMacro

import Language.Reflection
import Stage0.BoxInt
import Stage0.WitnessLedger
import Stage1.TypeTheory.Staging
import Stage1.TypeTheory.TwoLevel

%default total

------------------------------------------------------------------------
-- CANONICAL 2LTT PROOF WITNESS REFLECTION MACRO ENGINE
------------------------------------------------------------------------

||| Typecheck-time reflection macro verifying 2LTT subfibration scale adjunction proof erasure.
public export
%macro
auditStagedErasureMacro : Elab (verifySubfibrationDuality (MkStrict (the Nat 210)) (MkHomotopy 210) Refl = Refl)
auditStagedErasureMacro = pure Refl

