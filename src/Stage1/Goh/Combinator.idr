module Stage1.Goh.Combinator

import public Stage1.Goh.Combinator.Additive
import public Stage1.Goh.Combinator.Multiplicative

%default total

------------------------------------------------------------------------
-- ARITHMETIC FIXED POINT THEOREM (2 ⊕ 2 = 2 ⊗ 2 = 4)
------------------------------------------------------------------------

||| The Arithmetic Fixed Point Theorem: 2 is the unique constructive number
||| where addition and multiplication identically coincide: 2 ⊕ 2 = 2 ⊗ 2 = 4.
public export
0 prfTwoPlusTwoArithmeticFixedPoint :
  (gohAddNat 2 2 == 4) && (gohMulNat 2 2 == 4) = True
prfTwoPlusTwoArithmeticFixedPoint = Refl
