module Stage1.Goh.Factor

import Stage0.BoxInt
import Stage1.UnixelFraction
import Stage1.FourGeometries
import Stage1.TypeTheory.Smoothness
import Data.Vect
import Decidable.Equality

%default total

------------------------------------------------------------------------
-- 1. CONSTRUCTIVIST GOH PRIME SPECTRUM & POLYNOMIAL DEGREE
------------------------------------------------------------------------

||| Constructivist Goh prime family indexed by its exact prime number p.
||| Bounded by the 13-smooth horizon: {2, 3, 5, 7, 11, 13}.
public export
data GohPrime : (p : Nat) -> Type where
  Prime2  : GohPrime 2
  Prime3  : GohPrime 3
  Prime5  : GohPrime 5
  Prime7  : GohPrime 7
  Prime11 : GohPrime 11
  Prime13 : GohPrime 13

-- Dependently typed canonical constants:
public export gohPrime2  : GohPrime 2;  gohPrime2  = Prime2
public export gohPrime3  : GohPrime 3;  gohPrime3  = Prime3
public export gohPrime5  : GohPrime 5;  gohPrime5  = Prime5
public export gohPrime7  : GohPrime 7;  gohPrime7  = Prime7
public export gohPrime11 : GohPrime 11; gohPrime11 = Prime11
public export gohPrime13 : GohPrime 13; gohPrime13 = Prime13

||| Existential Sigma-pair used when prime indices vary dynamically
||| (e.g. lists of prime factors extracted from an arbitrary Nat n).
public export
AnyGohPrime : Type
AnyGohPrime = (p : Nat ** GohPrime p)

||| Project the underlying Nat prime from an existential pair.
public export
gohPrimeNat : AnyGohPrime -> Nat
gohPrimeNat (p ** _) = p

public export
allGohPrimes : Vect 6 AnyGohPrime
allGohPrimes = [(2 ** Prime2), (3 ** Prime3), (5 ** Prime5), (7 ** Prime7), (11 ** Prime11), (13 ** Prime13)]

public export
decideGohPrime : (p : Nat) -> Dec (GohPrime p)
decideGohPrime 2  = Yes Prime2
decideGohPrime 3  = Yes Prime3
decideGohPrime 5  = Yes Prime5
decideGohPrime 7  = Yes Prime7
decideGohPrime 11 = Yes Prime11
decideGohPrime 13 = Yes Prime13
decideGohPrime 0  = No (\case Prime2 impossible)
decideGohPrime 1  = No (\case Prime2 impossible)
decideGohPrime 4  = No (\case Prime2 impossible)
decideGohPrime 6  = No (\case Prime2 impossible)
decideGohPrime 8  = No (\case Prime2 impossible)
decideGohPrime 9  = No (\case Prime2 impossible)
decideGohPrime 10 = No (\case Prime2 impossible)
decideGohPrime 12 = No (\case Prime2 impossible)
decideGohPrime (S (S (S (S (S (S (S (S (S (S (S (S (S (S _)))))))))))))) =
  No (\case Prime2 impossible; Prime3 impossible; Prime5 impossible; Prime7 impossible; Prime11 impossible; Prime13 impossible)

public export
toGohPrime : (p : Nat) -> Maybe AnyGohPrime
toGohPrime p = case decideGohPrime p of
  Yes prf => Just (p ** prf)
  No _    => Nothing

public export
Eq AnyGohPrime where
  (p1 ** _) == (p2 ** _) = p1 == p2

public export
Show AnyGohPrime where
  show (p ** _) = "GohPrime(" ++ show p ++ ")"

||| Constructive mapping from any constructivist Goh prime to its 13-smooth certificate.
public export
gohPrimeWitness : GohPrime p -> SmoothWitness CosmicSmoothHorizon p
gohPrimeWitness Prime2  = prfSmooth2
gohPrimeWitness Prime3  = Refl
gohPrimeWitness Prime5  = Refl
gohPrimeWitness Prime7  = Refl
gohPrimeWitness Prime11 = Refl
gohPrimeWitness Prime13 = Refl

public export
gohPrimeDimension : {p : Nat} -> GohPrime p -> CosmicDimension
gohPrimeDimension prf = (p ** gohPrimeWitness prf)

public export
anyGohPrimeDimension : AnyGohPrime -> CosmicDimension
anyGohPrimeDimension (p ** prf) = (p ** gohPrimeWitness prf)

||| Determines the exact algebraic degree of the cyclotomic factor Phi_p(x).
public export
gohDegree : (p : Nat) -> Nat
gohDegree 2  = 1
gohDegree 3  = 2
gohDegree 5  = 4
gohDegree 7  = 6
gohDegree 11 = 10
gohDegree 13 = 12
gohDegree (S n) = n
gohDegree Z  = Z

||| Auxiliary UnixelFraction constructor for exact integer scalars.
private
fracInt : Integer -> UnixelFraction
fracInt n = mkUnixelFraction (intToBoxInt n) 1

------------------------------------------------------------------------
-- 2. DEPENDENTLY TYPED GOH PRIME FACTOR RECORD
------------------------------------------------------------------------

||| Dependently typed Goh Prime Factor parameterized by its exact prime number p.
||| Statically guarantees that the coefficient vector length matches the cyclotomic degree S (gohDegree p).
public export
record GohFactor (p : Nat) where
  constructor MkGohFactor
  0 primeWitness   : GohPrime p
  coefficients     : Vect (S (gohDegree p)) UnixelFraction
  geometrySector   : FundamentalGeometry
  vacuumQuadrance  : BoxInt
  domainRole       : String

public export
{p : Nat} -> Show (GohFactor p) where
  show (MkGohFactor _ _ geom q role) =
    "GohFactor(" ++ show p ++ " | " ++ show geom ++ " | Q=" ++ show (unwrapBox q) ++ " | " ++ role ++ ")"

||| Projects a dependently typed GohFactor into the canonical CosmicDimension Sigma-pair.
public export
0 gohFactorDimension : GohFactor p -> CosmicDimension
gohFactorDimension (MkGohFactor prf _ _ _ _) = (p ** gohPrimeWitness prf)

------------------------------------------------------------------------
-- 3. CANONICAL CONSTRUCTIVE FACTOR INSTANCES ACROSS THE 4 GEOMETRIES
-- (Cigler & Herbig, Ars Combinatoria 2026)
------------------------------------------------------------------------

||| Factor p = 2: Dyadic Hyperbolic DE ROM bit & Toric Code Parity Syndrome (Law 36).
||| Psi_2(x) = 4 - x, degree 1, coefficients: [4, -1].
public export
Factor2 : GohFactor 2
Factor2 =
  MkGohFactor
    Prime2
    [fracInt 4, fracInt (-1)]
    HyperbolicGeom
    (intToBoxInt 4)
    "Dyadic DE ROM & Toric Parity"

public export
factor2 : GohFactor 2
factor2 = Factor2

||| Factor p = 3: 3D Spatial Bound-State Canvas & Codon Triplet Reading Frame.
||| Psi_3(x) = (x - 3)^2 = 9 - 6x + x^2, degree 2, coefficients: [9, -6, 1].
public export
Factor3 : GohFactor 3
Factor3 =
  MkGohFactor
    Prime3
    [fracInt 9, fracInt (-6), fracInt 1]
    EllipticGeom
    (intToBoxInt 9)
    "3D Manifest Spatial Grid & Triplet"

public export
factor3 : GohFactor 3
factor3 = Factor3

||| Factor p = 5: Parabolic Blue Spread Hypotenuse & Pentose Nucleic Ring.
||| Psi_5(x) = (5 - 5x + x^2)^2 = 25 - 50x + 35x^2 - 10x^3 + x^4, degree 4.
public export
Factor5 : GohFactor 5
Factor5 =
  MkGohFactor
    Prime5
    [fracInt 25, fracInt (-50), fracInt 35, fracInt (-10), fracInt 1]
    ParabolicGeom
    (intToBoxInt 25)
    "Blue Spread Hypotenuse & Pentose"

public export
factor5 : GohFactor 5
factor5 = Factor5

||| Factor p = 7: Substrate Causal Arrow & Primorial 210 Ground State Budget.
||| Degree 6 cyclotomic polynomial over the Clifford generator dimension D = 7.
public export
Factor7 : GohFactor 7
Factor7 =
  MkGohFactor
    Prime7
    [fracInt 49, fracInt (-98), fracInt 70, fracInt (-28), fracInt 7, fracInt (-1), fracInt 1]
    SubstrateGeom
    (intToBoxInt 49)
    "Substrate Causal Arrow & Primorial 210"

public export
factor7 : GohFactor 7
factor7 = Factor7

||| Factor p = 11: Phase Space Boundary & Dark Matter Triangular Residue (T_10 = 55).
public export
Factor11 : GohFactor 11
Factor11 =
  MkGohFactor
    Prime11
    (replicate 11 (fracInt 1))
    ParabolicGeom
    (intToBoxInt 55)
    "Phase Space Boundary & DM T_10 Residue"

public export
factor11 : GohFactor 11
factor11 = Factor11

||| Factor p = 13: 13-Smooth Gate-Purity Boundary & Observer Epoch (n = 39 = 3 * 13).
public export
Factor13 : GohFactor 13
Factor13 =
  MkGohFactor
    Prime13
    (replicate 13 (fracInt 1))
    EllipticGeom
    (intToBoxInt 39)
    "13-Smooth Gate-Purity & Observer Epoch"

public export
factor13 : GohFactor 13
factor13 = Factor13

||| Canonical association mapping each GohPrime to its corresponding constructivist GohFactor.
public export
gohFactorForPrime : (p : Nat) -> GohPrime p -> GohFactor p
gohFactorForPrime 2 Prime2   = Factor2
gohFactorForPrime 3 Prime3   = Factor3
gohFactorForPrime 5 Prime5   = Factor5
gohFactorForPrime 7 Prime7   = Factor7
gohFactorForPrime 11 Prime11 = Factor11
gohFactorForPrime 13 Prime13 = Factor13


------------------------------------------------------------------------
-- 4. POLYNOMIAL HORNER EVALUATION & DEFINITIONAL THEOREMS
------------------------------------------------------------------------

||| Pure integer Horner polynomial evaluation over integer coefficient vector.
public export
evalHornerInteger : List Integer -> Integer -> Integer
evalHornerInteger [] _ = 0
evalHornerInteger (c :: cs) x = c + x * (evalHornerInteger cs x)

||| Evaluates factor 2: Psi_2(x) = 4 - x.
public export
evalFactor2 : Integer -> Integer
evalFactor2 x = 4 - x

||| Evaluates factor 3: Psi_3(x) = 9 - 6x + x^2.
public export
evalFactor3 : Integer -> Integer
evalFactor3 x = 9 - 6 * x + x * x

||| Invariant witness: Psi_2 fixed point at x = 2 is 2.
public export
0 prfFactor2FixedPoint : evalFactor2 2 = 2
prfFactor2FixedPoint = Refl

||| Invariant witness: Psi_3 root at manifest spatial dimension x = 3 is 0.
public export
0 prfFactor3RootAt3 : evalFactor3 3 = 0
prfFactor3RootAt3 = Refl

||| Invariant witness: Factor 2 and 3 vacuum quadrance sum matches Factor 5 vacuum root:
||| Q(2) + Q(3) = 4 + 9 = 13 (13-smooth prime).
public export
0 prfVacuumQuadranceSumIs13 : unwrapBox (vacuumQuadrance Factor2) + unwrapBox (vacuumQuadrance Factor3) = 13
prfVacuumQuadranceSumIs13 = Refl

||| Invariant witness: Dyadic Factor 2 vacuum quadrance Q(2) = 4 embodies the 2 + 2 factorisation:
||| Q(2) = 2^2 = 2 + 2 = 4.
public export
0 prfFactor2QuadranceIs4 : unwrapBox (vacuumQuadrance Factor2) = 4
prfFactor2QuadranceIs4 = Refl

