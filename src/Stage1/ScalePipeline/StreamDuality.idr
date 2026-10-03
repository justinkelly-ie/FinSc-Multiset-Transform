module Stage1.ScalePipeline.StreamDuality

import Stage0.OnSeq.FusedStream
import Data.List
import Data.SortedMap

%default total

------------------------------------------------------------------------
-- 1. FREE / FORGETFUL DUALITY (FreeWave ⇋ ForgetfulMonoid)
------------------------------------------------------------------------

||| Free wave multiset representation carrying coordinate payloads and amplitudes.
public export
data FreeWave : (coord : Type) -> Type where
  MkWave : List (coord, Integer) -> FreeWave coord

public export
Functor FreeWave where
  map f (MkWave kvs) = MkWave (map (\(x, i) => (f x, i)) kvs)

||| Forgetful monoid view shielding underlying coordinate structures.
public export
data ForgetfulMonoid : (a : Type) -> Type where
  MkMonoidView : (underlying : a) -> ForgetfulMonoid a

public export
Functor ForgetfulMonoid where
  map f (MkMonoidView x) = MkMonoidView (f x)

||| Discrete Wave Duality Interface (replaces category-theoretic Adjunction).
public export
interface (Functor f, Functor g) => Adjunction f g where
  unit   : a -> g (f a)
  counit : f (g a) -> a

||| Canonical 2LTT Wave Duality alias
public export
WaveDuality : (Type -> Type) -> (Type -> Type) -> Type
WaveDuality = Adjunction

public export covering
Adjunction FreeWave ForgetfulMonoid where
  unit x = MkMonoidView (MkWave [(x, 1)])
  counit (MkWave ((MkMonoidView val, _) :: _)) = val
  counit (MkWave []) = assert_total (idris_crash "Absurd Empty State in Adjunction Counit")

------------------------------------------------------------------------
-- 2. DUAL WAVE CONTEXT / STENCIL (FreeWave ∘ ForgetfulMonoid)
------------------------------------------------------------------------

||| Discrete Spatial Stencil Interface (replaces category-theoretic Comonad).
public export
interface Functor w => Comonad w where
  extract  : w a -> a
  duplicate : w a -> w (w a)
  extend   : (w a -> b) -> w a -> w b
  extend f wa = map f (duplicate wa)

||| Canonical 2LTT Wave Stencil alias
public export
WaveStencil : (Type -> Type) -> Type
WaveStencil = Comonad

||| Dual Wave Context induced by Duality FreeWave ⇋ ForgetfulMonoid.
public export
WaveContext : Type -> Type
WaveContext a = FreeWave (ForgetfulMonoid a)

public export
Functor WaveContext where
  map f (MkWave kvs) = MkWave (map (\(MkMonoidView x, i) => (MkMonoidView (f x), i)) kvs)

public export
duplicateWaveContext : WaveContext a -> WaveContext (WaveContext a)
duplicateWaveContext (MkWave kvs) =
  let duped = map (\(MkMonoidView x, i) => (MkMonoidView (MkWave [(MkMonoidView x, 1)]), i)) kvs
  in MkWave duped

public export covering
Comonad WaveContext where
  extract (MkWave ((MkMonoidView val, _) :: _)) = val
  extract (MkWave []) = assert_total (idris_crash "Absurd Empty State in WaveContext Comonad Extract")

  duplicate = duplicateWaveContext

  extend f wa = map {f = WaveContext} f (duplicateWaveContext wa)

||| Computes net wave interference mass over local comonadic wave context.
public export
coevalInterference : WaveContext a -> Integer
coevalInterference (MkWave kvs) = sum (map snd kvs)

------------------------------------------------------------------------
-- 3. STATE TRANSITION DERIVED MONAD ENGINE
------------------------------------------------------------------------

||| Monadic state transition wrapping a Forgetful Monoid view over Free Wave.
public export
record StateTransition (a : Type) where
  constructor MkTransition
  runTransition : ForgetfulMonoid (FreeWave a)

public export
Functor StateTransition where
  map f (MkTransition (MkMonoidView wave)) = MkTransition (MkMonoidView (map f wave))

public export
Applicative StateTransition where
  pure x = MkTransition (MkMonoidView (MkWave [(x, 1)]))
  (MkTransition (MkMonoidView (MkWave fs))) <*> (MkTransition (MkMonoidView (MkWave xs))) =
    let cross = [ (f x, fi * xi) | (f, fi) <- fs, (x, xi) <- xs ]
    in MkTransition (MkMonoidView (MkWave cross))

public export
Monad StateTransition where
  (MkTransition (MkMonoidView (MkWave kvs))) >>= f =
    let
      nested = map (\(x, i) => (f x, i)) kvs
      flat   = concatMap unpackAndScale nested
    in
      MkTransition (MkMonoidView (MkWave flat))
    where
      unpackAndScale : (StateTransition b, Integer) -> List (b, Integer)
      unpackAndScale (MkTransition (MkMonoidView (MkWave inner)), outerI) =
        map (\(boxel, innerI) => (boxel, innerI * outerI)) inner

------------------------------------------------------------------------
-- 4. 3D TERNARY SHIFT & SPATIAL TRANSITION DRIVER (T^3 CANVAS)
------------------------------------------------------------------------

||| Spatial Boxel Canvas representation carrying 3D toroidal coordinates (x, y, z) and intensity.
public export
record Boxel where
  constructor MkBoxel
  coords : (Int, Int, Int)
  intensity : Integer

public export
Eq Boxel where
  (MkBoxel c1 _) == (MkBoxel c2 _) = c1 == c2

public export
Ord Boxel where
  compare (MkBoxel c1 _) (MkBoxel c2 _) = compare c1 c2

public export
gridSize : Int
gridSize = 8

public export
wrap : Int -> Int
wrap x = let m = x `mod` gridSize in if m < 0 then m + gridSize else m

||| Converts a Ternary configuration element into an integer displacement delta.
public export
ternaryToDelta : Ternary -> Int
ternaryToDelta Neg  = -1
ternaryToDelta Zero = 0
ternaryToDelta Pos  = 1

||| Compute 3D spatial shift vector (dx, dy, dz) from internal TernaryMatrix entries.
public export
matrixToShift : TernaryMatrix -> (Int, Int, Int)
matrixToShift m =
  let
    dx = ternaryToDelta (topLeft m) + ternaryToDelta (topRight m)
    dy = ternaryToDelta (bottomLeft m) + ternaryToDelta (bottomRight m)
    dz = ternaryToDelta (topLeft m) - ternaryToDelta (bottomRight m)
  in
    (dx, dy, dz)

||| Computes chromogeometric quadrance based on sector tag and 3D displacement deltas.
public export
computeQuadrance : GeometrySector -> (Int, Int, Int) -> Integer
computeQuadrance Elliptic   (dx, dy, dz) = cast (dx * dx + dy * dy + dz * dz + 1)
computeQuadrance Hyperbolic (dx, dy, dz) = cast (dx * dx + dy * dy - dz * dz + 1)
computeQuadrance Parabolic  (dx, dy, dz) = cast (dx * dx + dy * dy + 1)
computeQuadrance Substrate  _            = 1

||| The evolution operator over 3D Toroidal Boxel Canvas T^3.
||| Transforms a Boxel spatial state according to a TernaryMatrix operator key and sector tag.
public export
driveSpatialUpdate : GeometrySector -> TernaryMatrix -> Boxel -> StateTransition Boxel
driveSpatialUpdate sector matrix (MkBoxel (x, y, z) intensity) =
  let
    (dx, dy, dz) = matrixToShift matrix
    newX = wrap (x + dx)
    newY = wrap (y + dy)
    newZ = wrap (z + dz)
    phaseScale = cast (source matrix + target matrix)
    quadrance  = computeQuadrance sector (dx, dy, dz)
  in
    MkTransition $ MkMonoidView $ MkWave
      [ (MkBoxel (newX, newY, newZ) (intensity * phaseScale * quadrance), 1) ]

------------------------------------------------------------------------
-- 5. STREAM DEFORESTATION FOR WAVE & BOXEL CANVAS PIPELINES
------------------------------------------------------------------------

||| Converts a FreeWave representation into a deforested FusedStream.
%inline public export
streamFreeWave : FreeWave coord -> FusedStream (coord, Integer)
streamFreeWave (MkWave kvs) = stream kvs

||| Reconstructs a FreeWave from a List of coordinate-amplitude pairs.
%inline public export
unstreamFreeWave : List (coord, Integer) -> FreeWave coord
unstreamFreeWave kvs = MkWave kvs

||| Zero-allocation stream pipeline map over FreeWave components.
%inline public export
fusedMapWave : (a -> b) -> FreeWave a -> FusedStream (b, Integer)
fusedMapWave f (MkWave kvs) =
  mapStream (\(x, i) => (f x, i)) (stream kvs)

||| Zero-allocation stream pipeline filter over FreeWave components.
%inline public export
fusedFilterWave : (a -> Bool) -> FreeWave a -> FusedStream (a, Integer)
fusedFilterWave p (MkWave kvs) =
  filterStream (\(x, _) => p x) (stream kvs)

||| Deforested spatial Boxel update stream pipeline.
%inline public export
fusedDriveSpatialUpdate : GeometrySector -> TernaryMatrix -> Boxel -> FusedStream (Boxel, Integer)
fusedDriveSpatialUpdate sector matrix boxel =
  let MkTransition (MkMonoidView wave) = driveSpatialUpdate sector matrix boxel
  in streamFreeWave wave
