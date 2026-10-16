module Stage1.Goh.Combinator.Multiplicative

import Stage0.BoxInt
import Stage0.Multiset
import Stage1.QuadStream
import Stage1.Goh.Factor
import Stage1.TypeTheory.Smoothness

%default total

------------------------------------------------------------------------
-- 1. MULTIPLICATIVE GOH COMBINATOR (⊗) OVER SCALARS & FACTORS
------------------------------------------------------------------------

||| Multiplicative Goh combinator over Nat indices: p ⊗ q = p * q.
public export
gohMulNat : (p : Nat) -> (q : Nat) -> Nat
gohMulNat p q = p * q

||| Multiplicative Goh combinator over BoxInt: p ⊗ q = p * q.
public export
gohMulBox : BoxInt -> BoxInt -> BoxInt
gohMulBox (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a * b)

||| Multiplies the vacuum quadrance payloads of two dependently typed Goh factors:
||| Q(p) ⊗ Q(q) = Q(p) * Q(q).
public export
gohMulFactorQuadrance : {p, q : Nat} -> GohFactor p -> GohFactor q -> BoxInt
gohMulFactorQuadrance f1 f2 = gohMulBox (vacuumQuadrance f1) (vacuumQuadrance f2)

------------------------------------------------------------------------
-- 2. MULTIPLICATIVE GOH COMBINATOR OVER TRANSDUCERS (∘)
------------------------------------------------------------------------

||| Multiplicative Goh Combinator over stream step transducers: f ⊗ g = g ∘ f.
||| Chains sequential cosmological phase pushforwards without intermediate heap allocation.
public export
gohCompose : (QuadStreamMultiset a -> QuadStreamMultiset a)
          -> (QuadStreamMultiset a -> QuadStreamMultiset a)
          -> (QuadStreamMultiset a -> QuadStreamMultiset a)
gohCompose step1 step2 = step2 . step1

------------------------------------------------------------------------
-- 3. COMPILE-TIME INVARIANT AUDITS & THEOREMS
------------------------------------------------------------------------

||| Observer Epoch composite scale factorization: 3 ⊗ 13 = 39 (Epoch k=38).
public export
0 prfObserverCompositeDuality : gohMulNat 3 13 = 39
prfObserverCompositeDuality = Refl

||| Primorial Master Capacity factorization: 2 ⊗ 3 ⊗ 5 ⊗ 7 = 210 (Primorial Ground State F = -1320).
public export
0 prfPrimorial210Factorization : gohMulNat (gohMulNat 2 3) (gohMulNat 5 7) = 210
prfPrimorial210Factorization = Refl

||| BoxInt representation matches Nat index factorization.
public export
0 prfBoxMulMatchesNat : unwrapBox (gohMulBox (intToBoxInt 3) (intToBoxInt 13)) = 39
prfBoxMulMatchesNat = Refl

||| Validated 13-smooth composite dimension of the Observer Epoch (3 ⊗ 13 = 39).
public export
observerDimension : CosmicDimension
observerDimension = (the Nat 39 ** prfSmooth39)

||| Validated 13-smooth composite dimension of the Primorial 210 Ground State (2 ⊗ 3 ⊗ 5 ⊗ 7 = 210).
public export
primorialDimension : CosmicDimension
primorialDimension = (the Nat 210 ** prfSmooth210)

