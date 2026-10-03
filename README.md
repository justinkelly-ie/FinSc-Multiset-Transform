# FinSc-Multiset-Transform

[![Idris 2 Verification](https://img.shields.io/badge/Idris_2-0.8.0-blue.svg)](https://www.idris-lang.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

**Layer 2 Staged Scale Category, Goh Polynomial Factorization & Duality Streams for Idris 2**

`FinSc-Multiset-Transform` forms **Layer 2** of the 10-layer constructive non-linear multiset science framework. Operating directly on top of the discrete kernel in `FinSc-Multiset-Core`, it provides the formal 5-stage scale category (`ScaleCategory` & `ScalePipeline`), Goh spread polynomial factorizations (`Stage1.Goh`), categorical duality streams (`ConjugateDuality`, `QuadStreamDuality`, `StreamDuality`), multiset active inference, and compile-time certified 13-smooth universe states.

---

## 📦 Core Architecture & Modules

### 1. Scale Category & Hierarchy (`Stage1.ScaleCategory`, `Stage1.ScaleHierarchy`, `Stage1.ScalePipeline`)
- **Formal Scale Category:** Stratified physical scale levels (`ScaleLevel`: SubatomicLevel, HadronLevel, AtomLevel, MoleculeLevel, CellLevel) and functorial scale morphisms (`ScaleFunctor`).
- **Functorial Composition:** Associative scale composition (`composeScaleFunctors`) mapping micro-quanta states to macroscopic structures.
- **5-Stage Scale Pipeline:** Unified scale pipeline (`sf1_QuarkToHadron` .. `sfTotalFunctorialPipeline`) formalizing the physical ascent from subatomic color charges to complex biological cells.

### 2. Goh Polynomial Factorization (`Stage1.Goh`, `Stage1.Math.Transform.Reflect.Goh`)
- **Spread Polynumbers:** Goh auxiliary polynomial factorization ($\Phi_d(s)$) over discrete Wildberger rational spread polynomials.
- **Multiset Wave Propagation:** `GohMultiset` trees storing factorized spread polynomials, evaluating wave propagation and multi-turn particle evolutions via exact polynomial multiplication.

### 3. Categorical Stream Dualities (`Stage1.ScalePipeline.StreamDuality`, `Stage1.Math.OnSeq.ConjugateDuality`, `Stage1.Math.Transform.QuadStreamDuality`)
- **Stream Duality:** Hom-tensor stream isomorphisms preserving exact integer proof witnesses across scale boundaries.
- **Conjugate Unfoldings:** Bounded, totalized conjugate unfoldings mapping dual multiset streams.
- **QuadStream Transformation:** 4-stream interleaving and cross-scale projection.

### 4. Active Inference & Dynamical Transducers (`Stage1.ActiveInference`, `Stage1.Multiset.Dynamics`, `Stage1.Multiset.StreamTransducer`)
- **Discrete Active Inference:** Free energy minimization and Markov blanket state transducers over multiset observations.
- **Stream Transducers:** Mealy/Moore-style state machines consuming and emitting discrete multiset tokens.

### 5. Stratified Universe State (`Stage1.StratifiedState`, `Stage1.Smooth13UniverseState`)
- **13-Smooth Physical State:** `Smooth13UniverseState` certifying at compile time that total cosmic capacity ($V_m + DE + DM$) is 13-smooth without prime factors $> 13$.
- **Vacuum Seeding:** Strict zero-leakage state seeding (`seedSmoothCosmicVacuum`) conserving physical quanta across cosmic epochs.

---

## 🚀 Building & Installing

Built with Idris 2 (`0.8.0`) via `pack`:

```bash
pack build FinSc-Multiset-Transform.ipkg
pack install FinSc-Multiset-Transform.ipkg
```

---

## 🔬 Architectural Principles

- **Total Constructivism:** Enforces `%default total` across all transformation modules.
- **Zero Floating-Point Drift:** Exact integer box and rational arithmetic eliminating numerical rounding defects.
- **2LTT Staging Discipline:** Clean separation between object-level dynamical computation and meta-level scale verification.
- **Functorial Scale Categories:** Structure-preserving `ScaleFunctor` pipelines mapping micro-states to macro-envelopes.
