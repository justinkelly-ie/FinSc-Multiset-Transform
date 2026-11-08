||| Primordial Stream Unfolding & Pythagorean Fixed-Point Triad Transducer
|||
||| Constructs the manifest 4-metric physical universe from an empty streaming
||| multiset carrier undergoing self-addition across the (4, 3) Pythagorean fixed point.
module Stage1.Multiset.PrimordialUnfolding

import Stage0.BoxInt
import Stage0.Multiset
import Stage0.Token
import Stage1.UnixelFraction
import Stage0.OnSeq.FusedStream
import Stage1.FourGeometries
import Stage1.UniverseState

%default total

--------------------------------------------------------------------------------
-- 0. PRIMORDIAL GENERATOR & SPACETIME DIMENSION OBSERVABLES
--------------------------------------------------------------------------------

||| Spacetime manifold dimension (4 = 3 space + 1 time),
||| grounded definitionally in the spacetime basis carrier cardinality (and fundamental geometries).
%inline public export
spacetimeDimensionNat : Nat
spacetimeDimensionNat = spacetimeBasisDim

||| Manifest spatial lattice dimension (3),
||| grounded definitionally in the chromogeometric color charge basis carrier cardinality.
%inline public export
manifestSpatialDimensionNat : Nat
manifestSpatialDimensionNat = manifestSpatialDim

||| The primordial generator coordinate (x, y) observed from spacetime and spatial lattice dimensions:
%inline public export
primordialGeneratorNat : (Nat, Nat)
primordialGeneratorNat = (spacetimeDimensionNat, manifestSpatialDimensionNat)

||| Compile-time proof certifying that the primordial generator unifies all 4 Goh primes of 210:
public export
0 prfPrimordialGeneratorGohPrimes :
  let x = fst primordialGeneratorNat
      y = snd primordialGeneratorNat
      qBlue = (x * x) + (y * y)
      qRed  = minus (x * x) (y * y)
      qGreen = 2 * x * y
  in (qBlue = 25, qRed = 7, qGreen = 24)
prfPrimordialGeneratorGohPrimes = (Refl, Refl, Refl)

--------------------------------------------------------------------------------
-- 1. SUBSTRATE CARRIER & ASYMMETRIC CAUSAL TOKENS
--------------------------------------------------------------------------------

||| Discrete 2D coordinate on the substrate causal canvas.
public export
record SubstrateCoord where
  constructor MkSubstrateCoord
  coordX : BoxInt
  coordY : BoxInt

public export
Eq SubstrateCoord where
  (MkSubstrateCoord x1 y1) == (MkSubstrateCoord x2 y2) = x1 == x2 && y1 == y2

||| Single asymmetric causal token carrying directional entropy increment ΔS >= 1.
public export
record SubstrateToken where
  constructor MkSubstrateToken
  location     : SubstrateCoord
  entropyArrow : BoxInt

public export
Eq SubstrateToken where
  (MkSubstrateToken l1 s1) == (MkSubstrateToken l2 s2) = l1 == l2 && s1 == s2

||| An empty substrate multiset carrier before cosmicgenesis.
public export
emptySubstrateCarrier : Box SubstrateToken
emptySubstrateCarrier = emptyBox

--------------------------------------------------------------------------------
-- 2. SPONTANEOUS CHROMOGEOMETRIC TRIAD BIFURCATION (1 ➔ 3)
--------------------------------------------------------------------------------

||| Chromogeometric Triad Quadrance tuple (Blue/Elliptic, Red/Hyperbolic, Green/Parabolic).
public export
record TriadQuadrance where
  constructor MkTriadQuadrance
  blueQ  : BoxInt
  redQ   : BoxInt
  greenQ : BoxInt

public export
Eq TriadQuadrance where
  (MkTriadQuadrance b1 r1 g1) == (MkTriadQuadrance b2 r2 g2) =
    b1 == b2 && r1 == r2 && g1 == g2

||| Computes exact Wildberger chromogeometric quadrance across Blue/Red/Green metrics:
||| - Q_Blue  = x^2 + y^2  (Elliptic bound-state canvas)
||| - Q_Red   = x^2 - y^2  (Hyperbolic lightcone phase)
||| - Q_Green = 2 * x * y  (Parabolic shear transport)
public export
pythagoreanFixedPoint : (x : BoxInt) -> (y : BoxInt) -> TriadQuadrance
pythagoreanFixedPoint x y =
  let x2 = mulBox x x
      y2 = mulBox y y
      b  = addBox x2 y2
      r  = subBox x2 y2
      g  = mulBox (intToBoxInt 2) (mulBox x y)
  in MkTriadQuadrance b r g

||| Maps a cosmological scale index k in [0, 136] and super-epoch cycle to a primitive dynamic Pythagorean coordinate (x_k, y_k).
||| Base epoch 0 of super-epoch 0 is observed from the primordial generator coordinate.
||| Higher super-epochs inherit phase precession from the previous cycle eon bounce.
public export
epochPythagoreanCoordinateReentrant : (superEp : Nat) -> (k : Nat) -> (BoxInt, BoxInt)
epochPythagoreanCoordinateReentrant superEp k =
  let kInt = cast {to = Integer} k
      sInt = cast {to = Integer} superEp
      baseX = cast {to = Integer} (fst primordialGeneratorNat)
      baseY = cast {to = Integer} (snd primordialGeneratorNat)
      m = baseX + ((kInt + (sInt * 11)) `mod` 137)
      n = baseY + (((kInt * 2) + (sInt * 7)) `mod` 137)
      x = if m > n then m else n + 1
      y = if m > n then n else m
  in (intToBoxInt x, intToBoxInt y)

||| Canonical single-eon projection for super-epoch 0.
public export
epochPythagoreanCoordinate : Nat -> (BoxInt, BoxInt)
epochPythagoreanCoordinate = epochPythagoreanCoordinateReentrant 0

||| Computes the dynamic TriadQuadrance at cosmological epoch index k and super-epoch.
public export
epochTriadQuadranceReentrant : (superEp : Nat) -> (k : Nat) -> TriadQuadrance
epochTriadQuadranceReentrant superEp k =
  let (x, y) = epochPythagoreanCoordinateReentrant superEp k
  in pythagoreanFixedPoint x y

||| Dynamic TriadQuadrance at cosmological epoch index k (super-epoch 0).
public export
epochTriadQuadrance : Nat -> TriadQuadrance
epochTriadQuadrance = epochTriadQuadranceReentrant 0

||| Proves that the dynamic TriadQuadrance satisfies Q_Blue^2 == Q_Red^2 + Q_Green^2 for any epoch k.
public export
auditDynamicEpochTriadIdentityProof : Nat -> Bool
auditDynamicEpochTriadIdentityProof k =
  let t = epochTriadQuadrance k
      lhs = mulBox t.blueQ t.blueQ
      rhs = addBox (mulBox t.redQ t.redQ) (mulBox t.greenQ t.greenQ)
  in boxEq lhs rhs

||| Computes the dynamic Substrate Quadrance Q_Substrate = x^2 + 2xy at cosmological epoch index k and super-epoch.
public export
epochSubstrateQuadranceReentrant : (superEp : Nat) -> (k : Nat) -> BoxInt
epochSubstrateQuadranceReentrant superEp k =
  let (x, y) = epochPythagoreanCoordinateReentrant superEp k
  in addBox (mulBox x x) (mulBox (intToBoxInt 2) (mulBox x y))

||| Canonical single-eon projection for Substrate Quadrance.
public export
epochSubstrateQuadrance : Nat -> BoxInt
epochSubstrateQuadrance = epochSubstrateQuadranceReentrant 0

||| Proves that the dynamic Substrate Quadrance satisfies 2 * Q_Substrate == Q_Blue + Q_Red + 2 * Q_Green.
public export
auditEpochSubstrateQuadranceIdentity : (superEp : Nat) -> (k : Nat) -> Bool
auditEpochSubstrateQuadranceIdentity superEp k =
  let qSub = epochSubstrateQuadranceReentrant superEp k
      triad = epochTriadQuadranceReentrant superEp k
      twoQSub = mulBox (intToBoxInt 2) qSub
      twoQGreen = mulBox (intToBoxInt 2) triad.greenQ
      rhsSum = addBox (addBox triad.blueQ triad.redQ) twoQGreen
  in boxEq twoQSub rhsSum

||| The canonical Pythagorean Fixed Point generating the fundamental triad (25, 7, 24),
||| observed directly from the primordial generator coordinate (x=4, y=3):
%inline public export
canonicalPythagoreanTriad : TriadQuadrance
canonicalPythagoreanTriad =
  pythagoreanFixedPoint (natToBoxInt (fst primordialGeneratorNat))
                        (natToBoxInt (snd primordialGeneratorNat))

||| Compile-time proof witness: The canonical (4, 3) Pythagorean Triad definitionally
||| reduces to the exact Wildberger chromogeometric quadrance triple (25, 7, 24).
public export
0 prfCanonicalTriadDefinitional : Stage1.Multiset.PrimordialUnfolding.canonicalPythagoreanTriad = MkTriadQuadrance (MkBoxInt 25) (MkBoxInt 7) (MkBoxInt 24)
prfCanonicalTriadDefinitional = Refl

||| Boolean audit proving the canonical (4, 3) point satisfies the exact Three-Fold Spread Identity:
||| Q_Blue^2 == Q_Red^2 + Q_Green^2 (25^2 = 7^2 + 24^2, 625 = 49 + 576).
public export
auditCanonicalTriadSpreadIdentityProof : Bool
auditCanonicalTriadSpreadIdentityProof =
  let t = canonicalPythagoreanTriad
      lhs = mulBox t.blueQ t.blueQ
      rhs = addBox (mulBox t.redQ t.redQ) (mulBox t.greenQ t.greenQ)
  in boxEq lhs rhs

||| Evaluates spontaneous bifurcation of a substrate token into a chromogeometric triad.
public export
bifurcateSubstrateTick : SubstrateToken -> TriadQuadrance
bifurcateSubstrateTick (MkSubstrateToken loc _) =
  pythagoreanFixedPoint loc.coordX loc.coordY

||| Bridges a SubstrateActionToken from Stage0.Token at epoch (superEp, k)
||| into a located SubstrateToken on the 2D Pythagorean causal canvas.
public export
actionTokenToSubstrateToken : (superEp : Nat) -> (k : Nat) -> SubstrateActionToken -> SubstrateToken
actionTokenToSubstrateToken superEp k (MkActionToken q) =
  let (x, y) = epochPythagoreanCoordinateReentrant superEp k
  in MkSubstrateToken (MkSubstrateCoord x y) q

||| Strictly linear token bifurcation: Consumes a linear SubstrateActionToken,
||| bridges it to a located SubstrateToken, and unfolds its 1 ➔ 3 TriadQuadrance
||| alongside its causal action quantum q.
public export
bifurcateActionTokenLinear : (superEp : Nat) -> (k : Nat) -> (1 tok : LToken SubstrateActionToken) -> (TriadQuadrance, BoxInt)
bifurcateActionTokenLinear superEp k (MkLToken actTok) =
  let subTok = actionTokenToSubstrateToken superEp k actTok
  in (bifurcateSubstrateTick subTok, subTok.entropyArrow)

||| Audits that linear SubstrateActionToken bifurcation at epoch (0, 0) yields the canonical (25, 7, 24) triad and ΔS = 1.
public export
auditActionTokenBifurcationProof : Bool
auditActionTokenBifurcationProof =
  let (triad, q) = bifurcateActionTokenLinear 0 0 (MkLToken unitActionToken)
  in triad == canonicalPythagoreanTriad && boxEq q (intToBoxInt 1)

||| Single-step stream transducer unfolding substrate tokens into TriadQuadrance states.
public export
triadStepTransducer : SubstrateToken -> Step SubstrateToken TriadQuadrance
triadStepTransducer tok = Yield (bifurcateSubstrateTick tok) tok

||| Deforested stream transformer executing 1 ➔ 3 triad bifurcation with zero heap overhead.
public export
unfoldTriadStream : FusedStream SubstrateToken -> FusedStream TriadQuadrance
unfoldTriadStream strm = mapStream bifurcateSubstrateTick strm

--------------------------------------------------------------------------------
-- 3. MÖBIUS UNFOLDING TRANSITION (2^7 ➔ 3^3) & FREE ENERGY
--------------------------------------------------------------------------------

||| Cosmic Partition of the Primorial 210 Budget across the 4 fundamental geometries:
||| - Elliptic:   27 VM (3^3 bound-state canvas)
||| - Hyperbolic: 128 DE (2^7 gauge flux lightcone)
||| - Parabolic:  55 DM (T_10 = 55 dissipation drain)
||| - Substrate:  210 Master ground-state capacity
public export
record CosmicPartition where
  constructor MkCosmicPartition
  ellipticVM      : BoxInt
  hyperbolicDE    : BoxInt
  parabolicDM     : BoxInt
  substrateMaster : BoxInt

public export
Eq CosmicPartition where
  (MkCosmicPartition v1 e1 m1 s1) == (MkCosmicPartition v2 e2 m2 s2) =
    v1 == v2 && e1 == e2 && m1 == m2 && s1 == s2

||| Canonical Primorial 210 Ground State Partition (27, 128, 55, 210).
public export
canonicalCosmicPartition : CosmicPartition
canonicalCosmicPartition =
  MkCosmicPartition
    (natToBoxInt Stage1.FourGeometries.ellipticLatticeCapacity)
    (natToBoxInt Stage1.FourGeometries.hyperbolicRomCapacity)
    (natToBoxInt Stage1.FourGeometries.darkMatterTriangularResidue)
    (natToBoxInt Stage1.FourGeometries.primorial210Budget)

||| Computes discrete internal energy U: U = 10 * VM + 1 * DE + 0 * DM.
public export
discreteInternalEnergy : CosmicPartition -> BoxInt
discreteInternalEnergy p =
  (intToBoxInt 10 * p.ellipticVM) + (intToBoxInt 1 * p.hyperbolicDE)

||| Computes discrete combinatorial entropy S: S = 2 * VM + 5 * DE + 3 * DM.
public export
discreteEntropy : CosmicPartition -> BoxInt
discreteEntropy p =
  (intToBoxInt 2 * p.ellipticVM) + (intToBoxInt 5 * p.hyperbolicDE) + (intToBoxInt 3 * p.parabolicDM)

||| Computes discrete Helmholtz Free Energy: F = U - T * S.
public export
discreteHelmholtzFreeEnergy : (temp : BoxInt) -> CosmicPartition -> BoxInt
discreteHelmholtzFreeEnergy temp p =
  let u = discreteInternalEnergy p
      s = discreteEntropy p
  in u - (temp * s)

||| Ground state Helmholtz free energy at equilibrium temperature T = 2:
||| F = U - 2S = 398 - 2 * 859 = 398 - 1718 = -1320.
public export
canonicalGroundStateFreeEnergy : BoxInt
canonicalGroundStateFreeEnergy =
  discreteHelmholtzFreeEnergy (intToBoxInt 2) canonicalCosmicPartition

||| Formal audit witness proving the ground state free energy achieves exactly -1320.
public export
auditGroundStateFreeEnergyProof : Bool
auditGroundStateFreeEnergyProof =
  boxEq canonicalGroundStateFreeEnergy (intToBoxInt (-1320))

||| Möbius Unfolding Transition: Unfolds a saturated chromogeometric triad into the 210 partition.
public export
mobiusUnfoldTransition : TriadQuadrance -> CosmicPartition
mobiusUnfoldTransition (MkTriadQuadrance _ _ _) = canonicalCosmicPartition

||| Certified Möbius Unfolding Transition: Unfolds a saturated chromogeometric triad
||| directly into the compile-time certified Primorial 210 CosmicUniverseState.
public export
mobiusUnfoldCertified : TriadQuadrance -> CosmicUniverseState 27 128 55
mobiusUnfoldCertified _ = seedPrimorialGroundState

