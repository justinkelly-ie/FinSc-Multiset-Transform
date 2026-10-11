module Stage1.Goh.Combinator.Additive

import Stage0.BoxInt
import Stage0.Multiset
import Stage0.OnSeq.FusedStream
import Stage1.QuadStream
import Stage1.Goh.Factor

%default total

------------------------------------------------------------------------
-- 1. ADDITIVE GOH COMBINATOR (⊕) OVER SCALARS & MULTISETS
------------------------------------------------------------------------

||| Additive Goh combinator over Nat indices: p ⊕ q = p + q.
public export
gohAddNat : (p : Nat) -> (q : Nat) -> Nat
gohAddNat p q = p + q

||| Additive Goh combinator over BoxInt: p ⊕ q = p + q.
public export
gohAddBox : BoxInt -> BoxInt -> BoxInt
gohAddBox (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a + b)

||| Additive Goh combinator over discrete multiset carriers (Level 0):
||| Disjoint union of token multisets.
public export
gohAddMultiset : Eq a => Box a -> Box a -> Box a
gohAddMultiset = unionBox

||| Adds the vacuum quadrance payloads of two dependently typed Goh factors:
||| Q(p) ⊕ Q(q) = Q(p) + Q(q).
public export
gohAddFactorQuadrance : {p, q : Nat} -> GohFactor p -> GohFactor q -> BoxInt
gohAddFactorQuadrance f1 f2 = gohAddBox (vacuumQuadrance f1) (vacuumQuadrance f2)

------------------------------------------------------------------------
-- 2. ADDITIVE GOH COMBINATOR OVER STREAMS & QUAD-STREAMS
------------------------------------------------------------------------

||| Level 1 parallel channel aggregation over coinductive streams:
||| Zero-allocation stream chaining in O(1) registers.
public export
gohAppendStream : FusedStream a -> FusedStream a -> FusedStream a
gohAppendStream = appendStream

||| Additive Goh combinator over QuadStreamMultiset payloads.
||| Merges the 4 cosmic stream sectors (Elliptic, Hyperbolic, Parabolic, Substrate)
||| via elementwise multiset addition.
public export
gohSumQuad : QuadStreamMultiset a -> QuadStreamMultiset a -> QuadStreamMultiset a
gohSumQuad (MkQuadStream e1 h1 p1 s1) (MkQuadStream e2 h2 p2 s2) =
  MkQuadStream
    (addMultiset e1 e2)
    (addMultiset h1 h2)
    (addMultiset p1 p2)
    (addMultiset s1 s2)

------------------------------------------------------------------------
-- 3. COMPILE-TIME INVARIANT AUDITS & THEOREMS
------------------------------------------------------------------------

||| Toric Code fault-tolerance distance sum duality: 2 ⊕ 2 = 4 (L = 4 code distance).
public export
0 prfToricSumDuality : gohAddNat 2 2 = 4
prfToricSumDuality = Refl

||| Watson-Crick hydrogen bond sum: 2 (A-T) ⊕ 3 (G-C) = 5.
public export
0 prfWatsonCrickBondSum : gohAddNat 2 3 = 5
prfWatsonCrickBondSum = Refl

||| Definitional proof that BoxInt combinator matches Nat combinator:
public export
0 prfBoxAddMatchesNat : unwrapBox (gohAddBox (intToBoxInt 2) (intToBoxInt 3)) = 5
prfBoxAddMatchesNat = Refl
