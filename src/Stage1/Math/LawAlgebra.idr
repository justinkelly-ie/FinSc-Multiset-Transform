module Stage1.Math.LawAlgebra

import Stage0.BoxInt
import Stage0.Multiset
import Stage0.UniverseState
import Stage1.UnixelFraction
import Stage1.MaxelTransform
import Stage1.TypeTheory.Smooth13
import Stage1.Smooth13UniverseState
import Stage1.Order.Preorder
import Stage0.OnSeq.FusedStream
import Data.Fuel
import Data.List

%default total

------------------------------------------------------------------------
-- 1. TYPED LAW ALGEBRA PUSHFORWARD & PULLBACK OPERATORS
------------------------------------------------------------------------


------------------------------------------------------------------------
-- 2. LAW ALGEBRA MONOID
------------------------------------------------------------------------

||| Combines two law aggregations under multiset union monoid operation:
||| (M1 • M2) = M1 ∪ M2.
public export
combineLaws : Eq a => Box a -> Box a -> Box a
combineLaws m1 m2 = unionBox m1 m2

||| Multiset lattice order (subsumption): M1 <= M2 iff count M1 x <= count M2 x for all x.
public export
subsumesBox : Eq a => List a -> Box a -> Box a -> Bool
subsumesBox [] m1 m2 = True
subsumesBox (x :: xs) m1 m2 =
  (unwrapBox (lookupBox x m1) <= unwrapBox (lookupBox x m2)) && subsumesBox xs m1 m2

||| A Law Algebra state carrying 13-smooth UniverseState capacity certification
public export
record Smooth13LawState (vm : Nat) (de : Nat) (dm : Nat) where
  constructor MkSmooth13LawState
  lawState    : Smooth13UniverseState vm de dm
  smoothProof : Smooth13Dimension (vm + de + dm)

public export
{vm, de, dm : Nat} -> Eq (Smooth13LawState vm de dm) where
  (MkSmooth13LawState s1 _) == (MkSmooth13LawState s2 _) = s1 == s2

------------------------------------------------------------------------
-- 3. FORMAL INVARIANT AUDIT PROOFS
------------------------------------------------------------------------

||| QTT 0 erased proof witness verifying the Left Identity of the Law Algebra Monoid:
||| (emptyBox • m) = m definitionally for all multiset law states.
public export
0 prfLawAlgebraMonoidLeftIdentity : Eq a => (m : Box a) -> combineLaws (Stage0.Multiset.emptyBox {a}) m = m
prfLawAlgebraMonoidLeftIdentity (MkBox ys) = Refl

||| QTT 0 erased proof witness verifying the Right Identity on the canonical empty law aggregation:
||| (emptyBox • emptyBox) = emptyBox definitionally.
public export
0 prfLawAlgebraMonoidEmptyRightIdentity : Eq a => combineLaws (Stage0.Multiset.emptyBox {a}) (Stage0.Multiset.emptyBox {a}) = Stage0.Multiset.emptyBox {a}
prfLawAlgebraMonoidEmptyRightIdentity = Refl

||| QTT 0 erased proof witness verifying that combining a single unixel law with emptyBox preserves the law:
public export
0 prfLawAlgebraMonoidUnixelLeftIdentity : Eq a => (x : a) -> (w : BoxInt) ->
  combineLaws (Stage0.Multiset.emptyBox {a}) (unixelBox x w) = unixelBox x w
prfLawAlgebraMonoidUnixelLeftIdentity x w = Refl


||| Static audit witness for Law Algebra Monoid verifying left and right identities on concrete law boxes.
public export
auditLawAlgebraMonoidProof : Bool
auditLawAlgebraMonoidProof =
  let m1 = unixelBox (intToBoxInt 1) (intToBoxInt 2)
      resLeft = combineLaws emptyBox m1 == m1
      resRight = combineLaws m1 emptyBox == m1
  in resLeft && resRight

||| QTT 0 erased proof witness auditing Law Algebra Monoid identity evaluation.
public export
0 verifyLawAlgebraMonoidAudit : Stage1.Math.LawAlgebra.auditLawAlgebraMonoidProof = True
verifyLawAlgebraMonoidAudit = Refl


------------------------------------------------------------------------
-- 4. COMPILE-TIME LAW ALGEBRA HOMOMORPHISM WITNESSES
------------------------------------------------------------------------

||| Evaluates linear addition preservation under law transform scaling: s * (v1 + v2) == s * v1 + s * v2.
public export
preservesLinearAddition : BoxInt -> BoxInt -> BoxInt -> Bool
preservesLinearAddition s v1 v2 =
  boxEq (mulBox s (addBox v1 v2)) (addBox (mulBox s v1) (mulBox s v2))

||| Erased compile-time proof witness verifying linearity preservation under scale transformation.
||| 2LTT Staging Operation: Quoting (⟨t⟩) - Encapsulates scale linearity checks into erased proof terms.
public export
0 HomomorphismWitness : (s : BoxInt) -> (v1 : BoxInt) -> (v2 : BoxInt) -> Type
HomomorphismWitness s v1 v2 = preservesLinearAddition s v1 v2 = True

||| Static compile-time witness for scalar s=2 and vectors v1=10, v2=20.
public export
0 prfScaleTransformHomomorphism : HomomorphismWitness (intToBoxInt 2) (intToBoxInt 10) (intToBoxInt 20)
prfScaleTransformHomomorphism = Refl

||| Verified law scale transformation carrying compile-time erased homomorphism witness.
||| 2LTT Staging Operation: Quoting (⟨t⟩) - Quoted transform record embedding an erased proof witness.
public export
record VerifiedLawTransform (s : BoxInt) (v1 : BoxInt) (v2 : BoxInt) where
  constructor MkVerifiedLawTransform
  scaleFactor : BoxInt
  0 homPrf : HomomorphismWitness s v1 v2

------------------------------------------------------------------------
-- 5. DEFORESTED MULTISET TRANSFORMATION STREAMS
------------------------------------------------------------------------

||| Discrete law transformation step record.
public export
record TransformStep where
  constructor MkTransformStep
  stepId   : Int
  outValue : BoxInt

public export
Eq TransformStep where
  (MkTransformStep id1 o1) == (MkTransformStep id2 o2) =
    id1 == id2 && o1 == o2

||| O(1) allocation deforested stream transducer scaling a multiset vector stream by a scale factor.
||| 2LTT Staging Operation: Splicing (~t) - Evaluates compile-time stream transducers into executable transformed vector streams.
public export covering
fusedMultisetTransformStream : Fuel -> BoxInt -> List BoxInt -> List BoxInt
fusedMultisetTransformStream f s steps =
  fusedHylomorphism f
    (\(idx, st) => case st of
                     [] => Done
                     v :: rest => Yield (MkTransformStep idx (mulBox s v)) (idx + 1, rest))
    (\step, acc => outValue step :: acc)
    []
    (1, steps)

||| Total Nat fuel-bounded deforested stream transducer scaling a multiset vector stream.
public export
fusedMultisetTransformStreamNat : (fuel : Nat) -> BoxInt -> List BoxInt -> List BoxInt
fusedMultisetTransformStreamNat Z _ _ = []
fusedMultisetTransformStreamNat (S f) s steps =
  loop f (1, steps) []
  where
    loop : Nat -> (Int, List BoxInt) -> List BoxInt -> List BoxInt
    loop Z _ acc = acc
    loop (S k) (idx, []) acc = acc
    loop (S k) (idx, v :: rest) acc =
      let step = MkTransformStep idx (mulBox s v)
      in loop k (idx + 1, rest) (outValue step :: acc)

||| O(1) allocation deforested stream transducer evaluating total sum of transformed values across a stream.
public export covering
fusedComputeTotalTransformedSum : Fuel -> BoxInt -> List BoxInt -> BoxInt
fusedComputeTotalTransformedSum f s steps =
  fusedHylomorphism f
    (\(idx, st) => case st of
                     [] => Done
                     v :: rest => Yield (MkTransformStep idx (mulBox s v)) (idx + 1, rest))
    (\step, acc => addBox (outValue step) acc)
    (intToBoxInt 0)
    (1, steps)

||| Total Nat fuel-bounded stream transducer evaluating total sum of transformed values.
public export
fusedComputeTotalTransformedSumNat : (fuel : Nat) -> BoxInt -> List BoxInt -> BoxInt
fusedComputeTotalTransformedSumNat Z _ _ = intToBoxInt 0
fusedComputeTotalTransformedSumNat (S f) s steps =
  loop f (1, steps) (intToBoxInt 0)
  where
    loop : Nat -> (Int, List BoxInt) -> BoxInt -> BoxInt
    loop Z _ acc = acc
    loop (S k) (idx, []) acc = acc
    loop (S k) (idx, v :: rest) acc =
      let step = MkTransformStep idx (mulBox s v)
      in loop k (idx + 1, rest) (addBox (outValue step) acc)

||| Structurally total deforested multiset stream transformation without Fuel.
||| Uses structural recursion directly over the input list of tokens.
public export
structuralMultisetTransformStream : BoxInt -> List BoxInt -> List BoxInt
structuralMultisetTransformStream s steps =
  map (\v => mulBox s v) steps

||| Structurally total evaluation of total sum of transformed values across a list.
public export
structuralComputeTotalTransformedSum : BoxInt -> List BoxInt -> BoxInt
structuralComputeTotalTransformedSum s steps =
  foldl (\acc, v => addBox (mulBox s v) acc) (intToBoxInt 0) steps

||| Pure multiset container evaluation: computes the transformed sum over Box a with integer multiplicities.
||| Eliminates intermediate List buffers in favor of first-class Multiset Box arithmetic.
public export
boxComputeTotalTransformedSum : (a -> BoxInt) -> Box a -> BoxInt
boxComputeTotalTransformedSum f (MkBox items) =
  foldl (\acc, (k, w) => addBox (mulBox (f k) w) acc) (intToBoxInt 0) items

||| Stream evaluation: folds directly over a FusedStream without allocating intermediate list buffers.
public export covering
fusedStreamTotalSum : FusedStream BoxInt -> BoxInt
fusedStreamTotalSum st = foldStream addBox (intToBoxInt 0) st

||| Total stream evaluation: folds directly over a FusedStream using Nat fuel.
public export
fusedStreamTotalSumNat : (fuel : Nat) -> FusedStream BoxInt -> BoxInt
fusedStreamTotalSumNat fuel st = foldStreamNat fuel addBox (intToBoxInt 0) st

||| Total stream evaluation: folds directly over a FusedStream using Data.Fuel.
public export
fusedStreamTotalSumFuel : Fuel -> FusedStream BoxInt -> BoxInt
fusedStreamTotalSumFuel fuel st = foldStreamFuel fuel addBox (intToBoxInt 0) st



------------------------------------------------------------------------
-- 6. LET-INSERTION & SHARING FOR STAGED MULTI-SCALE TRANSITIONS
------------------------------------------------------------------------

||| Evaluates a two-scale transition pipeline with let-binding sharing,
||| preventing exponential code duplication during staging expansion.
public export
stagedTwoScaleTransition : (m1 : BoxInt -> BoxInt) -> (m2 : BoxInt -> BoxInt) -> BoxInt -> BoxInt
stagedTwoScaleTransition m1 m2 x =
  let intermediate = m1 x
  in m2 intermediate

||| Evaluates a three-scale transition pipeline with let-binding sharing.
public export
stagedThreeScaleTransition : (m1 : BoxInt -> BoxInt) -> (m2 : BoxInt -> BoxInt) -> (m3 : BoxInt -> BoxInt) -> BoxInt -> BoxInt
stagedThreeScaleTransition m1 m2 m3 x =
  let s1 = m1 x
      s2 = m2 s1
  in m3 s2

