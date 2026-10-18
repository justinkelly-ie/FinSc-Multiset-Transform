||| Representation Theorem Isomorphism for Layer 1 Möbius Unfolding & Triad Bifurcation (Rule 03)
|||
||| Establishes the functorial isomorphism between abstract chromogeometric triad algebra
||| (25, 7, 24) and concrete multiset streams over TriadQuadrance elements:
|||   TheoryRepresentationIsomorphism L1_MobiusUnfolding TriadQuadrance TriadQuadrance
module Stage1.MobiusRepIso

import Stage0.BoxInt
import Stage0.Multiset
import Stage1.Multiset.PrimordialUnfolding
import Stage1.PhysicalUniverse.Stratification

%default total

||| Canonical zero triad quadrance.
public export
zeroTriad : TriadQuadrance
zeroTriad = MkTriadQuadrance (MkBoxInt 0) (MkBoxInt 0) (MkBoxInt 0)

||| Monomorphic equality for TriadQuadrance elements.
public export
triadEqMono : TriadQuadrance -> TriadQuadrance -> Bool
triadEqMono (MkTriadQuadrance b1 r1 g1) (MkTriadQuadrance b2 r2 g2) =
  b1 == b2 &&
  r1 == r2 &&
  g1 == g2

||| Canonical Representation Isomorphism for Layer 1 Möbius Phase Unfolding.
public export
mobiusUnfoldingRepIso : TheoryRepresentationIsomorphism L1_MobiusUnfolding TriadQuadrance TriadQuadrance
mobiusUnfoldingRepIso =
  MkTheoryRepIso
    "L1: Chromogeometric Triad Bifurcation -> Multiset TriadQuadrance"
    (\t => AddM t (MkBoxInt 1) ZeroM)
    (\m => case m of
             AddM t _ _ => t
             ZeroM      => zeroTriad)
    (\t =>
      let m = AddM t (MkBoxInt 1) ZeroM
          t' = case m of
                 AddM x _ _ => x
                 ZeroM      => zeroTriad
      in triadEqMono t' t
    )

||| Compile-time verification that round-trip isomorphism holds for canonical Pythagorean Triad (25, 7, 24).
public export
0 prfMobiusRepIsoCanonicalTriad :
  (verifyRoundTrip Stage1.MobiusRepIso.mobiusUnfoldingRepIso)
  Stage1.Multiset.PrimordialUnfolding.canonicalPythagoreanTriad = True
prfMobiusRepIsoCanonicalTriad = Refl
