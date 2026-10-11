module Stage1.Goh.Combinators

import Stage0.BoxInt
import Stage0.Multiset
import Stage1.QuadStream
import Stage1.FourGeometries

%default total

------------------------------------------------------------------------
-- 1. THE GOH PRIME SPECTRUM (DEPENDENTLY INDEXED BY BOXINT)
------------------------------------------------------------------------

||| Formal Constructive Goh Prime Factor family dependently indexed by BoxInt.
||| Eliminates magic number hardcoding and guarantees compile-time prime index alignment.
public export
data GohPrime : (p : BoxInt) -> Type where
  Prime2  : GohPrime (MkBoxInt 2)   -- p = 2: Dyadic DE Canvas & Toric Syndrome Parity
  Prime3  : GohPrime (MkBoxInt 3)   -- p = 3: 3D Spatial Grid & Chromogeometric Triad (3^3 = 27)
  Prime5  : GohPrime (MkBoxInt 5)   -- p = 5: Rational Spread Fixed Point & Watson-Crick (2 + 3 = 5)
  Prime7  : GohPrime (MkBoxInt 7)   -- p = 7: Dyadic Horizon Depth (2^7 = 128) & Red Flux
  Prime11 : GohPrime (MkBoxInt 11)  -- p = 11: Phase Space Boundary Prime (T_10 = 10 * 11 / 2 = 55)
  Prime13 : GohPrime (MkBoxInt 13)  -- p = 13: Gate-Purity Sieve Horizon & Observer Prime (39 = 3 * 13)

public export
gohPrimeValue : GohPrime p -> BoxInt
gohPrimeValue Prime2  = MkBoxInt 2
gohPrimeValue Prime3  = MkBoxInt 3
gohPrimeValue Prime5  = MkBoxInt 5
gohPrimeValue Prime7  = MkBoxInt 7
gohPrimeValue Prime11 = MkBoxInt 11
gohPrimeValue Prime13 = MkBoxInt 13

------------------------------------------------------------------------
-- 2. GOH COMBINATORS: ADDITIVE SUM (⊕) & MULTIPLICATIVE COMPOSITION (⊗)
------------------------------------------------------------------------

||| Additive Goh combinator over BoxInt: p ⊕ q = p + q.
||| Definitionally reducible during compile-time elaboration.
public export
gohAddBox : BoxInt -> BoxInt -> BoxInt
gohAddBox (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a + b)

||| Multiplicative Goh combinator over BoxInt: p ⊗ q = p * q.
||| Definitionally reducible during compile-time elaboration.
public export
gohMulBox : BoxInt -> BoxInt -> BoxInt
gohMulBox (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a * b)

||| Additive Goh Combinator over QuadStreamMultiset payloads.
||| Merges the 4 stream carriers (Elliptic, Hyperbolic, Parabolic, Substrate)
||| via multiset addition.
public export
gohSum : QuadStreamMultiset a -> QuadStreamMultiset a -> QuadStreamMultiset a
gohSum (MkQuadStream e1 h1 p1 s1) (MkQuadStream e2 h2 p2 s2) =
  MkQuadStream
    (addMultiset e1 e2)
    (addMultiset h1 h2)
    (addMultiset p1 p2)
    (addMultiset s1 s2)

||| Multiplicative Goh Combinator over stream step transducers: f ⊗ g = g ∘ f.
||| Chains sequential cosmological phase pushforwards without heap allocation.
public export
gohCompose : (QuadStreamMultiset a -> QuadStreamMultiset a)
          -> (QuadStreamMultiset a -> QuadStreamMultiset a)
          -> (QuadStreamMultiset a -> QuadStreamMultiset a)
gohCompose step1 step2 = step2 . step1

------------------------------------------------------------------------
-- 3. INVARIANT AUDIT PROOFS & COMPILE-TIME WITNESSES
------------------------------------------------------------------------

||| Toric Code fault-tolerance distance sum duality: 2 ⊕ 2 = 4.
public export
0 prfToricSumDuality : unwrapBox (gohAddBox (intToBoxInt 2) (intToBoxInt 2)) = 4
prfToricSumDuality = Refl

||| Watson-Crick hydrogen bond sum: 2 (A-T) ⊕ 3 (G-C) = 5.
public export
0 prfWatsonCrickBondSum : unwrapBox (gohAddBox (intToBoxInt 2) (intToBoxInt 3)) = 5
prfWatsonCrickBondSum = Refl

||| Observer Epoch composite scale factorization: 3 ⊗ 13 = 39 (Epoch k=38).
public export
0 prfObserverCompositeDuality : unwrapBox (gohMulBox (intToBoxInt 3) (intToBoxInt 13)) = 39
prfObserverCompositeDuality = Refl

||| Primorial Master Capacity factorization: 2 ⊗ 3 ⊗ 5 ⊗ 7 = 210.
public export
0 prfPrimorial210Factorization :
  unwrapBox (gohMulBox (gohMulBox (intToBoxInt 2) (intToBoxInt 3)) (gohMulBox (intToBoxInt 5) (intToBoxInt 7))) = 210
prfPrimorial210Factorization = Refl

||| Dark Matter triangular capacity residue from Phase Space Boundary: 10 * 11 / 2 = 55.
public export
0 prfDarkMatterTriangularFactorization :
  unwrapBox (MkBoxInt (div (10 * 11) 2)) = 55
prfDarkMatterTriangularFactorization = Refl
