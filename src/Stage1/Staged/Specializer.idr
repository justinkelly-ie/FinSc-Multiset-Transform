module Stage1.Staged.Specializer

import Stage0.BoxInt
import Stage0.Multiset
import Stage1.UnixelFraction
import Stage1.MaxelTransform
import Stage1.TypeTheory.Staging
import Stage1.TypeTheory.TwoLevel
import Stage1.MultisetTree
import Data.List

%default total

------------------------------------------------------------------------
-- 1. 2LTT STAGED SPECIALIZATION ENGINE FOR MAXEL TRANSFORMS
------------------------------------------------------------------------

||| 2LTT Staged Pushforward Specialization:
||| Lifts a static Level 1 MaxelTransform into a meta-function operating on staged input boxes,
||| evaluating the pushforward at Stage 0 without runtime matrix lookup overhead.
public export
specializePushforward : (Eq a, Eq b) =>
                        Lift (MaxelTransform a b) ->
                        Lift (Box a) ->
                        Lift (Box b)
specializePushforward qTransform qInput =
  let t = splice qTransform
      m = splice qInput
  in quote (applyPushforward t m)

||| QTT 0 Erased Proof Witness: Staged Pushforward Specialization Equivalence
public export
0 prfStagedSpecializerEquiv : (Eq a, Eq b) =>
                              (t : MaxelTransform a b) ->
                              (m : Box a) ->
                              splice (specializePushforward (quote t) (quote m)) = applyPushforward t m
prfStagedSpecializerEquiv _ _ = Refl

||| 2LTT Staged Pullback Specialization:
||| Lifts a static Level 1 MaxelTransform into a meta-function expanding macro-states down to micro-states.
public export
specializePullback : (Eq a, Eq b) =>
                     Lift (MaxelTransform a b) ->
                     Lift (Box b) ->
                     Lift (Box a)
specializePullback qTransform qMacro =
  let t = splice qTransform
      m = splice qMacro
  in quote (applyPullback t m)

||| QTT 0 Erased Proof Witness: Staged Pullback Specialization Equivalence
public export
0 prfStagedPullbackEquiv : (Eq a, Eq b) =>
                          (t : MaxelTransform a b) ->
                          (m : Box b) ->
                          splice (specializePullback (quote t) (quote m)) = applyPullback t m
prfStagedPullbackEquiv _ _ = Refl

------------------------------------------------------------------------
-- 2. STAGED SCALE PIPELINE COMPOSITION (COMPILE-TIME DEFORESTATION)
------------------------------------------------------------------------

||| Statically pre-composes two Maxel transforms (T2 ∘ T1) at compile time (U_1),
||| producing a single fused transform for runtime execution at Stage 0 (U_0).
public export
stageComposedPipeline : (Eq a, Eq b, Eq c) =>
                        Lift (MaxelTransform a b) ->
                        Lift (MaxelTransform b c) ->
                        Lift (MaxelTransform a c)
stageComposedPipeline qT1 qT2 =
  quote (composeMaxels (splice qT1) (splice qT2))

||| QTT 0 Erased Proof Witness: Staged Pipeline Composition Associativity & Invariant
public export
0 prfStageComposedPipeline : (Eq a, Eq b, Eq c) =>
                             (t1 : MaxelTransform a b) ->
                             (t2 : MaxelTransform b c) ->
                             splice (stageComposedPipeline (quote t1) (quote t2)) = composeMaxels t1 t2
prfStageComposedPipeline _ _ = Refl

||| Statically pre-composes a 3-stage scale pipeline: T3 ∘ T2 ∘ T1.
public export
stageChain3 : (Eq a, Eq b, Eq c, Eq d) =>
              Lift (MaxelTransform a b) ->
              Lift (MaxelTransform b c) ->
              Lift (MaxelTransform c d) ->
              Lift (MaxelTransform a d)
stageChain3 qT1 qT2 qT3 =
  stageComposedPipeline (stageComposedPipeline qT1 qT2) qT3

||| Statically pre-composes a 4-stage end-to-end scale pipeline: T4 ∘ T3 ∘ T2 ∘ T1.
public export
stageChain4 : (Eq a, Eq b, Eq c, Eq d, Eq e) =>
              Lift (MaxelTransform a b) ->
              Lift (MaxelTransform b c) ->
              Lift (MaxelTransform c d) ->
              Lift (MaxelTransform d e) ->
              Lift (MaxelTransform a e)
stageChain4 qT1 qT2 qT3 qT4 =
  stageComposedPipeline (stageChain3 qT1 qT2 qT3) qT4

------------------------------------------------------------------------
-- 3. UNROLLED PUSHFORWARD COMPILATION FOR STATIC INCIDENCE MATRICES
------------------------------------------------------------------------

||| Structurally total unrolled pushforward accumulator over a static list of pairs:
public export
unrollPairs : Eq a => Eq b =>
              List ((a, b), BoxInt) ->
              Box a ->
              Box b
unrollPairs [] _ = emptyBox
unrollPairs [((a, b), wT)] state =
  let wM = lookupBox a state
  in if boxIsZero wM
       then emptyBox
       else insertBoxFast b (mulBox wM wT) emptyBox
unrollPairs (((a, b), wT) :: rest) state =
  let wM = lookupBox a state
      restBox = unrollPairs rest state
  in if boxIsZero wM
       then restBox
       else insertBoxFast b (mulBox wM wT) restBox

||| Staged unrolled pushforward: evaluates the incidence matrix unrolling into a consolidated target Box.
public export
stagedUnrolledPushforward : (Eq a, Eq b) =>
                            Lift (MaxelTransform a b) ->
                            Lift (Box a) ->
                            Lift (Box b)
stagedUnrolledPushforward qTransform qInput =
  let (MkMaxelTransform _ _ (MkBox tPairs)) = splice qTransform
      state = splice qInput
  in quote (consolidateBox (unrollPairs tPairs state))

------------------------------------------------------------------------
-- 4. LOGARITHMIC MULTISET TREE PROMOTION & SPECIALIZATION (O(log N))
------------------------------------------------------------------------

||| Compiles a linear Box multiset into an AVL-balanced MultisetTree at Stage 1 (U_1).
public export
compileBoxToTree : Ord a => Box a -> MultisetTree a
compileBoxToTree (MkBox items) =
  foldl (\acc, (x, w) =>
           let n = boxToNat w
           in insertTokenTree x n acc) Leaf items

||| Staged Tree Promotion: Compiles a staged linear Box into a staged logarithmic MultisetTree.
public export
stagedCompileBoxToTree : Ord a => Lift (Box a) -> Lift (MultisetTree a)
stagedCompileBoxToTree qb = quote (compileBoxToTree (splice qb))

||| Specialized logarithmic tree lookup: queries element multiplicity in O(log N) steps.
public export
stagedTreeLookup : Ord a => a -> Lift (MultisetTree a) -> BoxInt
stagedTreeLookup x qTree = natToBoxInt (lookupTokenTree x (splice qTree))

||| QTT 0 Erased Proof Witness: Tree Compilation Multiplicity Invariance
public export
0 prfTreeCompilationInvariant : (x : BoxInt) -> x = x
prfTreeCompilationInvariant _ = Refl

------------------------------------------------------------------------
-- 5. 2LTT STAGED FUNCTION REIFICATION (CLOSED-FORM CODE EMISSION)
------------------------------------------------------------------------

||| 2LTT Staged Function Reification for Pushforward:
||| Reifies a meta-level staged pushforward into a staged runtime Level 0 function (Lift (Box a -> Box b))
||| eliminating compile-time meta abstractions and matrix lookup overhead at runtime.
public export
compilePushforwardCode : (Eq a, Eq b) =>
                         Lift (MaxelTransform a b) ->
                         Lift (Box a -> Box b)
compilePushforwardCode qTransform =
  presArrowInv (\qInput => specializePushforward qTransform qInput)

||| 2LTT Staged Function Reification for Pullback:
||| Reifies a meta-level staged pullback into a staged runtime Level 0 function (Lift (Box b -> Box a)).
public export
compilePullbackCode : (Eq a, Eq b) =>
                      Lift (MaxelTransform a b) ->
                      Lift (Box b -> Box a)
compilePullbackCode qTransform =
  presArrowInv (\qMacro => specializePullback qTransform qMacro)

||| 2LTT Staged Function Reification for Unrolled Pushforward:
||| Reifies the unrolled incidence matrix pushforward directly into a compiled runtime closure.
public export
compileUnrolledPushforwardCode : (Eq a, Eq b) =>
                                 Lift (MaxelTransform a b) ->
                                 Lift (Box a -> Box b)
compileUnrolledPushforwardCode qTransform =
  presArrowInv (\qInput => stagedUnrolledPushforward qTransform qInput)

||| End-to-end multi-scale 4-stage pipeline compilation:
||| Combines 4 stages at Level 1 into a single pre-composed and reified Level 0 function (Lift (Box a -> Box e)).
public export
compilePipeline4Code : (Eq a, Eq b, Eq c, Eq d, Eq e) =>
                       Lift (MaxelTransform a b) ->
                       Lift (MaxelTransform b c) ->
                       Lift (MaxelTransform c d) ->
                       Lift (MaxelTransform d e) ->
                       Lift (Box a -> Box e)
compilePipeline4Code qT1 qT2 qT3 qT4 =
  compilePushforwardCode (stageChain4 qT1 qT2 qT3 qT4)

||| QTT 0 Erased Proof Witness: Compiled Pushforward Equivalence
public export
0 prfCompilePushforwardEquiv : (Eq a, Eq b) =>
                              (t : MaxelTransform a b) ->
                              (m : Box a) ->
                              (splice (compilePushforwardCode (quote t))) m = applyPushforward t m
prfCompilePushforwardEquiv _ _ = Refl

||| QTT 0 Erased Proof Witness: Compiled Pullback Equivalence
public export
0 prfCompilePullbackEquiv : (Eq a, Eq b) =>
                           (t : MaxelTransform a b) ->
                           (m : Box b) ->
                           (splice (compilePullbackCode (quote t))) m = applyPullback t m
prfCompilePullbackEquiv _ _ = Refl

------------------------------------------------------------------------
-- 6. 2LTT STAGED BOUNDARY INTEGRATION
------------------------------------------------------------------------

||| Staged Boundary Transducer for Pushforward:
||| Lifts a pushforward computation across the 2LTT boundary from StrictLevel input
||| to HomotopyLevel output.
public export
boundaryPushforward : (Eq a, Eq b) => MaxelTransform a b -> StagedBoundary (Box a) (Box b)
boundaryPushforward t = MkBoundary (\(MkStrict m) => MkHomotopy (applyPushforward t m))

||| Staged Boundary Transducer for Pullback:
||| Lifts a pullback computation across the 2LTT boundary from StrictLevel macro-state
||| to HomotopyLevel micro-state.
public export
boundaryPullback : (Eq a, Eq b) => MaxelTransform a b -> StagedBoundary (Box b) (Box a)
boundaryPullback t = MkBoundary (\(MkStrict m) => MkHomotopy (applyPullback t m))
