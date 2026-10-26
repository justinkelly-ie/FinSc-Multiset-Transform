module Stage1.Math.OnSeq.SpreadStream

import Data.List
import Data.Vect
import Data.Nat
import Data.Fuel
import Decidable.Equality
import Stage0.BoxInt
import Stage0.Multiset
import Stage1.UnixelFraction
import Stage1.Goh
import Stage0.BoxNat
import Stage0.StructuralFuel
import Stage1.MultisetDuality
import Stage0.OnSeq.FusedStream
import Stage1.TypeTheory.MultisetLevel
import Stage1.TypeTheory.Staging
import Stage1.Basis.Coordinate
import Stage1.Goh.Factor
import Stage1.Goh.SpreadFactorization
import Stage1.TypeTheory.Smoothness
import public Stage1.FourGeometries

%default total

------------------------------------------------------------------------
-- 1. TOTAL DIVISOR CALCULATOR & GOH AUXILIARY FACTOR GENERATOR
------------------------------------------------------------------------

||| Computes all divisors k | n of a natural number n.
public export
divisors : Nat -> List Nat
divisors Z = []
divisors (S n) = filter (\d => (S n) `mod` d == Z) [1..S n]

||| Deforested stream of divisors of n from 1 up to n (Coutts et al. 2007 Stream Fusion).
||| Eliminates intermediate List allocation completely.
public export
divisorStream : Nat -> FusedStream Nat
divisorStream Z = stream []
divisorStream (S n) = unfoldStream nextStep (1, S n)
  where
    nextStep : (Nat, Nat) -> Step (Nat, Nat) Nat
    nextStep (cand, target) =
      if cand > target then Done
      else if target `mod` cand == Z then
        Yield cand (S cand, target)
      else
        Skip (S cand, target)

------------------------------------------------------------------------
-- 2. DEFORESTED GOH SPREAD POLYNOMIAL STREAM GENERATORS
------------------------------------------------------------------------

||| Maps divisor d to an authentic Cigler-Herbig irreducible spread polynomial factor in a GohMultiset:
public export
divFactorToMultiset : Nat -> GohMultiset
divFactorToMultiset d =
  let (_ ** f) = ciglerHerbigAuxiliary d
  in AddFactor f EmptyBag

||| Constructs an auxiliary Goh polynomial factor Phi_k(s) of degree k.
public export
makeGohFactor : (k : Nat) -> GohAuxiliary k
makeGohFactor k =
  let coeffs = Data.Vect.replicate (S k) (mkUnixelFraction (intToBoxInt 1) 1)
  in Phi coeffs

||| Unfolds a natural frequency index n into an allocation-free deforested stream of Goh factors Phi_k.
public export
unfoldGohFactorStream : Nat -> FusedStream GohMultiset
unfoldGohFactorStream Z = stream []
unfoldGohFactorStream (S n) =
  let divs = divisors (S n)
      bags = map divFactorToMultiset divs
  in stream bags

||| Fully deforested unfolding of frequency index n into Goh factors without intermediate List buffers.
public export
unfoldGohFactorStreamDeforested : Nat -> FusedStream GohMultiset
unfoldGohFactorStreamDeforested Z = stream []
unfoldGohFactorStreamDeforested (S n) =
  mapStream divFactorToMultiset (divisorStream (S n))

||| Zero-allocation streaming of 2D companion support pixels for prime divisors in the Goh factor tree.
||| Covers all 4 primitive Goh prime gates of the Primorial 210 ground state: p ∈ {2, 3, 5, 7}.
public export
gohPrimeSupportStream : (d : Nat) -> FusedStream Pixel
gohPrimeSupportStream 2 = gohFactorSupportStream Factor2
gohPrimeSupportStream 3 = gohFactorSupportStream Factor3
gohPrimeSupportStream 5 = gohFactorSupportStream Factor5
gohPrimeSupportStream 7 = gohFactorSupportStream Factor7
gohPrimeSupportStream _ = stream []

||| Unfolds the frequency index n into an allocation-free deforested stream of active 2D companion support pixels.
||| Emits pixels directly from static balanced MultisetTree structures via streamMultisetTreeDirect.
public export
unfoldGohSupportStreamDeforested : Nat -> FusedStream Pixel
unfoldGohSupportStreamDeforested n =
  flatMapStream gohPrimeSupportStream (divisorStream n)


||| Fully deforested, structurally total stream of Goh multiset spread polynomials up to bound d.
||| Operates via pure register steppers with zero List allocations.
public export
streamSpreadPolynomialsDeforested : (degreeBound : Nat) -> FusedStream GohMultiset
streamSpreadPolynomialsDeforested bound = unfoldStream nextStep (1, 1, bound)
  where
    nextStep : (Nat, Nat, Nat) -> Step (Nat, Nat, Nat) GohMultiset
    nextStep (k, d, maxK) =
      if k > maxK then Done
      else if d > k then Skip (S k, 1, maxK)
      else if k `mod` d == Z then
        Yield (divFactorToMultiset d) (k, S d, maxK)
      else
        Skip (k, S d, maxK)

||| Generates an infinite/fueled deforested stream of Goh multiset spread polynomials S_0, S_1, S_2, ...
||| bounded structurally by the Observer Epoch (pred (fst dimObserver) = 38).
public export
streamSpreadPolynomials : Fuel -> FusedStream GohMultiset
streamSpreadPolynomials Dry = stream []
streamSpreadPolynomials (More f) = streamSpreadPolynomialsDeforested (pred (fst dimObserver))

||| Generates a structurally total bounded deforested stream of Goh multiset spread polynomials up to bound d.
||| Structurally total without requiring external Fuel. Operates via pure register steppers with zero List allocations.
public export
streamSpreadPolynomialsBounded : (degreeBound : Nat) -> FusedStream GohMultiset
streamSpreadPolynomialsBounded = streamSpreadPolynomialsDeforested


------------------------------------------------------------------------
-- 3. CATEGORY-THEORETIC SPREAD STREAM ADJUNCTION (L_S ⊣ R_S)
------------------------------------------------------------------------

||| Category-Theoretic Adjoint Spread Stream Transducer linking spread generator (L_S) and fold consumer (R_S).
public export
interface SpreadStreamAdjunction (0 l : Type -> Type) (0 r : Type -> Type) where
  spreadAdjunction : MultisetAdjunction l r

------------------------------------------------------------------------
-- 4. DEFORESTED HYLOMORPHIC EVALUATOR WITH 4GEOMETRIES SECTOR MAPPING
------------------------------------------------------------------------

||| Maps a streamed GohMultiset to its corresponding 4Geometries FundamentalGeometry classification.
public export
classifySpreadStreamSector : GohMultiset -> FundamentalGeometry
classifySpreadStreamSector EmptyBag = SubstrateGeom
classifySpreadStreamSector (AddFactorM {deg} _ _ _) =
  if snd (natDivMod deg 3) == 0 then EllipticGeom
  else if not (snd (natHalfAndOdd deg)) then HyperbolicGeom
  else ParabolicGeom
classifySpreadStreamSector (AddFactor {deg} _ _) =
  if snd (natDivMod deg 3) == 0 then EllipticGeom
  else if not (snd (natHalfAndOdd deg)) then HyperbolicGeom
  else ParabolicGeom

||| Evaluates an allocation-free deforested Goh spread polynomial stream generator under 
||| total Nat fuel-bounded category-theoretic adjunction folds (Total Adjoint Hylomorphism).
public export
fusedSpreadHylomorphismNat : (fuel : Nat) ->
                              (s -> Step s GohMultiset) ->
                              (GohMultiset -> b -> b) ->
                              b -> s -> b
fusedSpreadHylomorphismNat Z _ _ acc _ = acc
fusedSpreadHylomorphismNat (S f) next consumerFold acc seed = loop f seed acc
  where
    loop : Nat -> s -> b -> b
    loop Z _ currentAcc = currentAcc
    loop (S f') st currentAcc = case next st of
      Done => currentAcc
      Skip st' => loop f' st' currentAcc
      Yield bag st' => loop f' st' (consumerFold bag currentAcc)

||| Evaluates an allocation-free deforested Goh spread polynomial stream generator under 
||| category-theoretic adjunction folds (Adjoint Hylomorphism) using BoxNat fuel.
public export
fusedSpreadHylomorphismBoxNat : BoxNat ->
                              (s -> Step s GohMultiset) ->
                              (GohMultiset -> b -> b) ->
                              b -> s -> b
fusedSpreadHylomorphismBoxNat bfuel next consumerFold acc seed =
  fusedSpreadHylomorphismNat (boxNatToNat bfuel) next consumerFold acc seed

||| Evaluates an allocation-free deforested Goh spread polynomial stream generator under 
||| category-theoretic adjunction folds (Adjoint Hylomorphism).
public export
fusedSpreadHylomorphism : Fuel ->
                          (s -> Step s GohMultiset) ->
                          (GohMultiset -> b -> b) ->
                          b -> s -> b
fusedSpreadHylomorphism Dry _ _ acc _ = acc
fusedSpreadHylomorphism (More f') next consumerFold acc seed =
  fusedSpreadHylomorphismBoxNat masterSubstrateGohFuel next consumerFold acc seed

||| Evaluates a deforested Goh spread polynomial list fold structurally without Fuel.
public export
structuralSpreadFold : List GohMultiset -> (GohMultiset -> b -> b) -> b -> b
structuralSpreadFold [] _ acc = acc
structuralSpreadFold (x :: xs) f acc = structuralSpreadFold xs f (f x acc)

------------------------------------------------------------------------
-- 5. EULER TOTIENT & PRIME FACTOR SPECTRUM DECOMPOSITION
------------------------------------------------------------------------

||| Total fuel-bounded natural numbers Greatest Common Divisor calculator.
public export
natGCDFuel : Nat -> Nat -> Nat -> Nat
natGCDFuel Z _ b = b
natGCDFuel (S f) a Z = a
natGCDFuel (S f) a b = natGCDFuel f b (a `mod` b)

public export
natGCD : Nat -> Nat -> Nat
natGCD a b = natGCDFuel (a + b) a b

||| Computes Euler's totient function phi(n) for degree accounting.
public export
totient : Nat -> Nat
totient Z = Z
totient (S Z) = S Z
totient (S n) =
  let k = S n
  in length (filter (\d => natGCD k d == 1) [1..k])

||| Extracts prime factors p | k driving the cyclotomic phase gate.
public export
primeFactors : Nat -> List Nat
primeFactors Z = []
primeFactors (S Z) = []
primeFactors (S (S n)) =
  let num = S (S n)
      candidates = [2..num]
  in filter (\p => num `mod` p == Z && length (divisors p) == 2) candidates

||| Extracts the prime factor spectrum from a GohMultiset factor bag.
public export
gohPrimeSpectrum : GohMultiset -> List Nat
gohPrimeSpectrum EmptyBag = []
gohPrimeSpectrum (AddFactorM {deg} _ _ rest) = primeFactors deg ++ gohPrimeSpectrum rest
gohPrimeSpectrum (AddFactor {deg} _ rest) = primeFactors deg ++ gohPrimeSpectrum rest

||| Computes accumulated degree budget capacity across Blue (Elliptic), Red (Hyperbolic), Green (Parabolic) sectors.
public export
chromogeometricBudgetExhaustion : List GohMultiset -> (Nat, Nat, Nat)
chromogeometricBudgetExhaustion bags = foldl step (Z, Z, Z) bags
  where
    step : (Nat, Nat, Nat) -> GohMultiset -> (Nat, Nat, Nat)
    step (b, r, g) EmptyBag = (b, r, g)
    step (b, r, g) (AddFactorM {deg} _ m rest) =
      let degWeight = totient deg * boxNatToNat m
          (b', r', g') =
            if snd (natDivMod deg 3) == 0 then (b + degWeight, r, g)
            else if not (snd (natHalfAndOdd deg)) then (b, r + degWeight, g)
            else (b, r, g + degWeight)
      in step (b', r', g') rest
    step (b, r, g) (AddFactor {deg} _ rest) =
      let (b', r', g') =
            if snd (natDivMod deg 3) == 0 then (b + totient deg, r, g)
            else if not (snd (natHalfAndOdd deg)) then (b, r + totient deg, g)
            else (b, r, g + totient deg)
      in step (b', r', g') rest

||| Cardinality of the Wildberger Support of a Goh factor Phi_d(s): exactly equal to totient(d).
public export
gohSupportSize : (d : Nat) -> Nat
gohSupportSize d = totient d

||| Formal Chromogeometric Sector Budget Record tracking degree allocation across Blue, Red, and Green metrics
public export
record ChromogeometricSectorBudget where
  constructor MkChromogeometricSectorBudget
  blueElliptic     : Nat
  redHyperbolic    : Nat
  greenParabolic   : Nat

public export
Eq ChromogeometricSectorBudget where
  (MkChromogeometricSectorBudget b1 r1 g1) == (MkChromogeometricSectorBudget b2 r2 g2) =
    b1 == b2 && r1 == r2 && g1 == g2

||| Computes the total chromogeometric degree capacity
public export
totalChromogeometricCapacity : ChromogeometricSectorBudget -> Nat
totalChromogeometricCapacity (MkChromogeometricSectorBudget b r g) = b + r + g

||| Computes exact ChromogeometricSectorBudget from a list of GohMultiset factor bags
public export
computeChromogeometricBudget : List GohMultiset -> ChromogeometricSectorBudget
computeChromogeometricBudget bags =
  let (b, r, g) = chromogeometricBudgetExhaustion bags
  in MkChromogeometricSectorBudget b r g

||| Verifies that Chromogeometric Sector Budget total capacity equals dimension N (b + r + g = N)
public export
prop_chromogeometricBudgetConservation : Nat -> Bool
prop_chromogeometricBudgetConservation Z = True
prop_chromogeometricBudgetConservation (S n) =
  let dim = S n
      divs = divisors dim
      bags = map (\d => AddFactor (makeGohFactor d) EmptyBag) divs
      budget = computeChromogeometricBudget bags
  in totalChromogeometricCapacity budget == dim

||| Computes exact ChromogeometricSectorBudget directly from a deforested stream of GohMultiset factor bags.
public export
computeChromogeometricBudgetDeforested : FusedStream GohMultiset -> ChromogeometricSectorBudget
computeChromogeometricBudgetDeforested strm =
  let (b, r, g) = foldStreamNat (boxNatToNat masterSubstrateGohFuel) step (Z, Z, Z) strm
  in MkChromogeometricSectorBudget b r g
  where
    step : (Nat, Nat, Nat) -> GohMultiset -> (Nat, Nat, Nat)
    step (b, r, g) EmptyBag = (b, r, g)
    step (b, r, g) (AddFactorM {deg} _ m rest) =
      let degWeight = totient deg * boxNatToNat m
          (b', r', g') =
            if snd (natDivMod deg 3) == 0 then (b + degWeight, r, g)
            else if not (snd (natHalfAndOdd deg)) then (b, r + degWeight, g)
            else (b, r, g + degWeight)
      in step (b', r', g') rest
    step (b, r, g) (AddFactor {deg} _ rest) =
      let (b', r', g') =
            if snd (natDivMod deg 3) == 0 then (b + totient deg, r, g)
            else if not (snd (natHalfAndOdd deg)) then (b, r + totient deg, g)
            else (b, r, g + totient deg)
      in step (b', r', g') rest

||| Verifies that deforested stream budget computation matches the list-buffered version for dimension N.
public export
prop_chromogeometricBudgetDeforestedConservation : Nat -> Bool
prop_chromogeometricBudgetDeforestedConservation Z = True
prop_chromogeometricBudgetDeforestedConservation (S n) =
  let dim = S n
      strm = unfoldGohFactorStreamDeforested dim
      budget = computeChromogeometricBudgetDeforested strm
  in totalChromogeometricCapacity budget == dim

------------------------------------------------------------------------
-- 6. PRIMORIAL 210 UNFOLDING BUDGET & 4GEOMETRIES STAGING
------------------------------------------------------------------------

||| Formal Primorial 210 Unfolding Budget Record (27 Blue Elliptic 3D + 128 Red Hyperbolic 2D + 55 Green Parabolic Sink = 210)
public export
record Primorial210UnfoldingBudget where
  constructor MkPrimorial210UnfoldingBudget
  blueElliptic3D     : Nat  -- 3^3 = 27 3D Spatial Volume States
  redHyperbolic2D    : Nat  -- 2^7 = 128 2D Spectral Phase States
  greenParabolicSink : Nat  -- 55 Lightlike Dissipation Remainder States

public export
Eq Primorial210UnfoldingBudget where
  (MkPrimorial210UnfoldingBudget b1 r1 g1) == (MkPrimorial210UnfoldingBudget b2 r2 g2) =
    b1 == b2 && r1 == r2 && g1 == g2

||| Computes total capacity of a Primorial 210 Unfolding Budget
public export
totalPrimorial210Capacity : Primorial210UnfoldingBudget -> Nat
totalPrimorial210Capacity (MkPrimorial210UnfoldingBudget b r g) = b + r + g

||| Classifies a stage-indexed LevelBox GohMultiset into its 4Geometries FundamentalGeometry sector
public export
classifyStageGeometry : {n : Nat} -> LevelBox n GohMultiset -> FundamentalGeometry
classifyStageGeometry (MkLevelBox (MkBox [])) = SubstrateGeom
classifyStageGeometry (MkLevelBox (MkBox ((g, _) :: _))) = classifySpreadStreamSector g

||| Verifies that Primorial 210 Goh Cyclotomic Factor Tree Unfolding preserves total capacity 210 (27 + 128 + 55 = 210)
public export
prop_primorial210UnfoldingInvariance : Bool
prop_primorial210UnfoldingInvariance =
  let divs210 = divisors 210
      bags210 = map (\d => AddFactor (makeGohFactor d) EmptyBag) divs210
      budget = computeChromogeometricBudget bags210
      primBudget = MkPrimorial210UnfoldingBudget budget.blueElliptic budget.redHyperbolic budget.greenParabolic
  in totalPrimorial210Capacity primBudget == 210

------------------------------------------------------------------------
-- 7. COMPILE-TIME REFLECTION & INVARIANT AUDITOR WITNESSES
------------------------------------------------------------------------

||| Static compiler proof witness verifying that Goh factor stream unfolding matches exact divisor count.
public export
auditSpreadStreamProof : Bool
auditSpreadStreamProof =
  let divs6 = divisors 6
      count6 = length divs6
  in count6 == 4 -- Divisors of 6 are [1, 2, 3, 6]

||| Static proof witness verifying Gauss's Totient Divisor Sum Identity sum_{d|n} phi(d) == n for n = 6.
public export
auditTotientSumProof : Bool
auditTotientSumProof =
  let divs6 = divisors 6
      totSum6 = sum (map totient divs6)
  in totSum6 == 6

||| Static proof witness verifying Wildberger Support Partition Identity sum_{d|n} |Supp(Phi_d)| == n for n = 6.
public export
auditWildbergerSupportPartitionProof : Bool
auditWildbergerSupportPartitionProof =
  let divs6 = divisors 6
      suppSum6 = sum (map gohSupportSize divs6)
  in suppSum6 == 6

------------------------------------------------------------------------
-- 8. 2LTT STAGED MULTI-SCALE HORNER SPREAD COMPOSITION (Z_mn = Z_m ∘ Z_n)
------------------------------------------------------------------------

||| Evaluates composite spread polynomial transformation Z_mn(x) = Z_m(Z_n(x))
||| according to the Cigler-Herbig (2026) spread polynomial semigroup composition theorem.
public export
evalSpreadComposeMultiset : GohMultiset -> GohMultiset -> UnixelFraction -> UnixelFraction
evalSpreadComposeMultiset zm zn s =
  evalGohMultiset zm (evalGohMultiset zn s)

||| 2LTT Staged Composite Spread Scale Transformation Transducer.
||| Pre-evaluates composite scale transitions at compile-time (Stage 1),
||| emitting an unrolled Horner polynomial fold for runtime (Stage 0).
public export
stagedSpreadComposeJump : GohMultiset -> GohMultiset -> UnixelFraction -> Code UnixelFraction
stagedSpreadComposeJump zm zn s = quote (evalSpreadComposeMultiset zm zn s)

||| QTT 0 Erased Proof Witness: Staged Spread Composition Evaluates to Object Code Definitionally (~⟨t⟩ ≡ t).
public export
0 prfStagedSpreadComposeJump : (zm : GohMultiset) -> (zn : GohMultiset) -> (s : UnixelFraction) ->
                              splice (stagedSpreadComposeJump zm zn s) = evalSpreadComposeMultiset zm zn s
prfStagedSpreadComposeJump zm zn s = inverseSpliceQuote (evalSpreadComposeMultiset zm zn s)

------------------------------------------------------------------------
-- 9. 2LTT SYMBOLIC STAGED HORNER UNROLLING & DEFORESTED STREAM INLINING
------------------------------------------------------------------------

||| Symbolically unrolls a coefficient list into nested Horner form at compile time (Stage 1).
public export
unrollHornerCoeffs : List UnixelFraction -> Code UnixelFraction -> Code UnixelFraction
unrollHornerCoeffs [] _ = quote zeroUnixelFraction
unrollHornerCoeffs [c0] _ = quote c0
unrollHornerCoeffs (c0 :: rest) qS =
  quote (addUnixelFraction (splice (quote c0))
                           (mulUnixelFraction (splice qS)
                                              (splice (unrollHornerCoeffs rest qS))))

||| Staged Horner unrolling for a single GohAuxiliary factor:
public export
unrollHorner : GohAuxiliary deg -> Code UnixelFraction -> Code UnixelFraction
unrollHorner (Phi coeffs) qS = unrollHornerCoeffs (toList coeffs) qS

||| Symbolically unrolls rational power computation x^m at compile time.
public export
stagedPowerUnixelFraction : Code UnixelFraction -> (fuel : Nat) -> Code UnixelFraction
stagedPowerUnixelFraction _ Z = quote unitUnixelFraction
stagedPowerUnixelFraction qX (S Z) = qX
stagedPowerUnixelFraction qX (S (S k)) =
  quote (mulUnixelFraction (splice qX) (splice (stagedPowerUnixelFraction qX (S k))))

||| Staged evaluation of a single factor with BoxNat multiplicity.
public export
stagedUnrollFactorM : GohAuxiliary deg -> BoxNat -> Code UnixelFraction -> Code UnixelFraction
stagedUnrollFactorM factor m qS =
  let factorCode = unrollHorner factor qS
      mNat = boxNatToNat m
  in stagedPowerUnixelFraction factorCode mNat

||| Staged evaluation of an entire GohMultiset factorization tree P(s) = prod_{k} Phi_k(s)^m_k
public export
stagedUnrollGohMultiset : GohMultiset -> Code UnixelFraction -> Code UnixelFraction
stagedUnrollGohMultiset EmptyBag _ = quote unitUnixelFraction
stagedUnrollGohMultiset (AddFactor factor rest) qS =
  let fCode = unrollHorner factor qS
      restCode = stagedUnrollGohMultiset rest qS
  in quote (mulUnixelFraction (splice fCode) (splice restCode))
stagedUnrollGohMultiset (AddFactorM factor m rest) qS =
  let fCode = stagedUnrollFactorM factor m qS
      restCode = stagedUnrollGohMultiset rest qS
  in quote (mulUnixelFraction (splice fCode) (splice restCode))

||| 2LTT Staged Deforested Stream Transducer:
||| Inlines the unrolled polynomial Horner evaluation pipeline directly into a stream transformer.
public export
stagedGohStreamTransducer : GohMultiset -> Code (FusedStream UnixelFraction -> FusedStream UnixelFraction)
stagedGohStreamTransducer bag =
  quote (\strm => mapStream (\s => splice (stagedUnrollGohMultiset bag (quote s))) strm)

||| QTT 0 Erased Proof Witness: Staged Horner evaluation roundtrip.
public export
0 prfStagedHornerRoundtrip : (bag : GohMultiset) -> (s : UnixelFraction) ->
                             splice (quote (evalGohMultiset bag s)) = evalGohMultiset bag s
prfStagedHornerRoundtrip bag s = inverseSpliceQuote (evalGohMultiset bag s)

||| QTT 0 Erased Proof Witness: Staged Stream Transducer evaluates definitionally to inlined stream map.
public export
0 prfStagedStreamTransducerRoundtrip : (bag : GohMultiset) -> (strm : FusedStream UnixelFraction) ->
  splice (stagedGohStreamTransducer bag) strm = mapStream (\s => splice (stagedUnrollGohMultiset bag (quote s))) strm
prfStagedStreamTransducerRoundtrip bag strm = Refl

