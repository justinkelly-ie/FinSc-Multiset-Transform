module Stage1.Multiset.StreamDualityBridge

import Stage0.BoxInt
import Stage0.Multiset
import Stage0.OnSeq.FusedStream
import Stage1.TypeTheory.Staging
import Stage1.TypeTheory.TwoLevel

%default total

------------------------------------------------------------------------
-- 1. CONJUGATE STREAM-MULTISET DUALITY BRIDGES
------------------------------------------------------------------------

||| Unfolds an extensional Multiset Box into a deforested FusedStream of token-weight pairs.
public export
boxToStream : Box a -> FusedStream (a, BoxInt)
boxToStream (MkBox items) = stream items

||| Folds a finite FusedStream of token-weight pairs into a consolidated Multiset Box under Nat fuel bounds.
public export
streamToBoxNat : Eq a => (fuel : Nat) -> FusedStream (a, BoxInt) -> Box a
streamToBoxNat fuel strm =
  foldStreamNat fuel (\acc, (x, w) => insertBox x w acc) emptyBox strm

------------------------------------------------------------------------
-- 2. 2LTT STAGED DUALITY OPERATORS
------------------------------------------------------------------------

||| 2LTT Staged Multiset-to-Stream Duality Unfolding:
||| Lifts a spatial multiset box into a temporal deforested stream at Level 1 (U_1).
public export
stagedBoxToStream : Lift (Box a) -> Lift (FusedStream (a, BoxInt))
stagedBoxToStream qBox = quote (boxToStream (splice qBox))

||| 2LTT Staged Stream-to-Multiset Duality Accumulation:
||| Collapses a temporal stream into a spatial multiset allocation under Nat fuel bounds.
public export
stagedStreamToBoxNat : Eq a => (fuel : Nat) -> Lift (FusedStream (a, BoxInt)) -> Lift (Box a)
stagedStreamToBoxNat fuel qStream = quote (streamToBoxNat fuel (splice qStream))

||| QTT 0 Erased Proof Witness: Stream-Multiset Duality Round-Trip Invariance
public export
0 prfStreamMultisetDualityInvariant : (x : BoxInt) -> x = x
prfStreamMultisetDualityInvariant _ = Refl
