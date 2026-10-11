module Stage1.Goh.Functor.StreamTransducer

import Stage0.BoxInt
import Stage0.OnSeq.FusedStream
import Stage1.Goh.Functor.LawLifter

%default total

------------------------------------------------------------------------
-- LEVEL 1 COINDUCTIVE LAW STREAM TRANSDUCERS (O(1) STREAM FUSION)
------------------------------------------------------------------------

||| A physical conservation law transducer operating over coinductive FusedStream pipelines.
||| Parameterized by its carrier scale index (scale : Nat).
public export
record LawStreamTransducer (scale : Nat) where
  constructor MkLawTransducer
  channelIndex : Nat
  transduce    : FusedStream BoxInt -> FusedStream BoxInt

||| Applies a ScaleLawFunctor to lift a physical law transducer from sourceScale to targetScale.
||| Preserves single-pass deforestation in O(1) registers without heap allocation.
public export
liftLawTransducer : ScaleLawFunctor s t -> LawStreamTransducer s -> LawStreamTransducer t
liftLawTransducer functor (MkLawTransducer ch tr) =
  let mul = scaleMultiplier functor
      scaledStep = mapStream (\(MkBoxInt v) => MkBoxInt (v * cast mul))
  in MkLawTransducer ch (scaledStep . tr)
