/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

-- The Challenges in `palomar/` import exactly these modules.
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Data.EReal.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Hom.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Semicontinuity.Defs

/-!
# Rank-one convexity and quasiconvexity

The standard notions of the vectorial calculus of variations (see S. Müller, *Variational models
for microstructure and phase transitions*, lecture notes, MPI MiS Leipzig, 1998, Definition 4.2,
and Theorem 4.5 (ii) for the quasiconvex envelope; B. Dacorogna, *Direct Methods in the Calculus of
Variations*, 2nd ed., Springer, 2008, Definition 5.1 and Section 6.3), for integrands
`f : ℝ^{d×m} → ℝ`, with the conventions of this package: test maps are Lipschitz, and
quasiconvexity is tested on the unit cube.

* `grad φ x`: the derivative matrix of `φ : ℝ^m → ℝ^d` (rows are the components);
* `IsLocallyBounded f`;
* `RankOneConvex f`: `t ↦ f (A + t B)` is convex for every `A` and every `B` of rank one;
  `RankOneAffine f`: `f` and `−f` are rank-one convex;
* `QuasiconvexAtOn Ω f A`: `|Ω| f (A) ≤ ∫_Ω f (A + ∇φ)` for every Lipschitz `φ` vanishing outside
  `Ω` (for a Lipschitz domain `Ω`, `φ ∈ W^{1,∞}_0 (Ω, ℝ^d)` extended by `0`) for which the integral
  exists; `QuasiconvexAtPeriodic f A`: the same on the unit cube for `ℤ^m`-periodic Lipschitz `φ`
  (`φ ∈ W^{1,∞}_per (𝕋^m, ℝ^d)`);
* `Quasiconvex f`: quasiconvexity on the unit cube at every matrix;
* `quasiconvexEnvelope f`, the supremum of the Borel, locally bounded, quasiconvex minorants of `f`,
  and `qcEnvelope f`, that of the lower semicontinuous ones (in `EReal`, `⊥` when there is none);
  they are equal (`quasiconvexEnvelope_eq_qcEnvelope`);
* `domainInf Ω f`, the infimum formula `inf_φ ⨍_Ω f (A + ∇φ)`;
* `minor A r c`: the minor of `A` with the rows `r` and the columns `c`.

The marked blocks of definitions are copied word for word into the Challenges in `palomar/` by
`scripts/sync_challenge_defs.py`.
-/

@[expose] public section

open MeasureTheory

namespace CalculusOfVariations

-- BEGIN SHARED DEFINITIONS: core

variable {d m : ℕ}

/-- The derivative matrix of `φ : ℝ^m → ℝ^d` at `x`: the `d × m` matrix with the entries
`∂_k φ_i (x)` (rows are the components). For a Lipschitz `φ` it is the gradient almost everywhere
(Rademacher's theorem); an entry is `0` where `φ_i` is not differentiable. -/
noncomputable def grad (φ : (Fin m → ℝ) → Fin d → ℝ) (x : Fin m → ℝ) :
    Matrix (Fin d) (Fin m) ℝ :=
  Matrix.of fun i k => fderiv ℝ (fun y => φ y i) x (Pi.single k 1)

/-- The open unit cube `(0, 1)^m`. -/
def unitCube (m : ℕ) : Set (Fin m → ℝ) :=
  Set.pi Set.univ fun _ => Set.Ioo 0 1

/-- `f` is bounded on a neighbourhood of every matrix. -/
def IsLocallyBounded (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Prop :=
  ∀ A, ∃ U ∈ nhds A, ∃ C : ℝ, ∀ B ∈ U, |f B| ≤ C

/-- Rank-one convexity: `t ↦ f (A + t B)` is convex on `ℝ` for every `A` and every `B` of rank
one. -/
def RankOneConvex (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Prop :=
  ∀ A B : Matrix (Fin d) (Fin m) ℝ, B.rank = 1 → ConvexOn ℝ Set.univ fun t : ℝ => f (A + t • B)

/-- Quasiconvexity at `A` on the domain `Ω`: `|Ω| f (A) ≤ ∫_Ω f (A + ∇φ)` for every Lipschitz `φ`
vanishing outside `Ω` for which the integral exists (for a Borel, locally bounded `f` and a bounded
`Ω`, it always does). It is used for bounded `Ω` only: if `|Ω| = ∞`, `(volume Ω).toReal` is `0`. -/
def QuasiconvexAtOn (Ω : Set (Fin m → ℝ)) (f : Matrix (Fin d) (Fin m) ℝ → ℝ)
    (A : Matrix (Fin d) (Fin m) ℝ) : Prop :=
  ∀ (φ : (Fin m → ℝ) → Fin d → ℝ) (K : NNReal), LipschitzWith K φ → (∀ x ∉ Ω, φ x = 0) →
    IntegrableOn (fun x => f (A + grad φ x)) Ω →
      (volume Ω).toReal * f A ≤ ∫ x in Ω, f (A + grad φ x)

/-- Quasiconvexity: quasiconvexity on the unit cube at every matrix. -/
def Quasiconvex (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Prop :=
  ∀ A, QuasiconvexAtOn (unitCube m) f A

-- END SHARED DEFINITIONS: core

-- BEGIN SHARED DEFINITIONS: periodic

/-- Quasiconvexity at `A` with periodic test maps: `f (A) ≤ ∫_{(0,1)^m} f (A + ∇φ)` for every
`ℤ^m`-periodic Lipschitz `φ` for which the integral exists. -/
def QuasiconvexAtPeriodic (f : Matrix (Fin d) (Fin m) ℝ → ℝ) (A : Matrix (Fin d) (Fin m) ℝ) :
    Prop :=
  ∀ (φ : (Fin m → ℝ) → Fin d → ℝ) (K : NNReal), LipschitzWith K φ →
    (∀ (x : Fin m → ℝ) (z : Fin m → ℤ), φ (x + fun i => (z i : ℝ)) = φ x) →
    IntegrableOn (fun x => f (A + grad φ x)) (unitCube m) →
      f A ≤ ∫ x in unitCube m, f (A + grad φ x)

-- END SHARED DEFINITIONS: periodic

-- BEGIN SHARED DEFINITIONS: envelope

/-- The quasiconvex envelope of `f` at `A`: the supremum of `g (A)` over the quasiconvex `g ≤ f`
(`g` Borel, locally bounded, and quasiconvex at every matrix), with values in `EReal`: it is
`⊥ = −∞` when there is no such `g`. -/
noncomputable def quasiconvexEnvelope (f : Matrix (Fin d) (Fin m) ℝ → ℝ)
    (A : Matrix (Fin d) (Fin m) ℝ) : EReal :=
  ⨆ (g : Matrix (Fin d) (Fin m) ℝ → ℝ)
    (_ : Measurable g ∧ IsLocallyBounded g ∧ Quasiconvex g ∧ ∀ B, g B ≤ f B), (g A : EReal)

/-- The infimum formula on `Ω`: `inf_φ ⨍_Ω f (A + ∇φ)`, where `⨍_Ω = |Ω|⁻¹ ∫_Ω`, over the Lipschitz
`φ` vanishing outside `Ω`, with values in `EReal`. It is used for bounded open `Ω ≠ ∅` and
continuous `f`, for which the integrals exist. -/
noncomputable def domainInf (Ω : Set (Fin m → ℝ)) (f : Matrix (Fin d) (Fin m) ℝ → ℝ)
    (A : Matrix (Fin d) (Fin m) ℝ) : EReal :=
  ⨅ (φ : (Fin m → ℝ) → Fin d → ℝ) (_ : (∃ K, LipschitzWith K φ) ∧ ∀ x ∉ Ω, φ x = 0),
    (((volume Ω).toReal⁻¹ * ∫ x in Ω, f (A + grad φ x) : ℝ) : EReal)

-- END SHARED DEFINITIONS: envelope

-- BEGIN SHARED DEFINITIONS: minors

/-- Rank-one affinity: `f` and `−f` are rank-one convex. -/
def RankOneAffine (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Prop :=
  RankOneConvex f ∧ RankOneConvex (-f)

/-- The `k × k` minor of `A` with the rows `r` and the columns `c` (strictly increasing). -/
noncomputable def minor (A : Matrix (Fin d) (Fin m) ℝ) {k : ℕ} (r : Fin k ↪o Fin d)
    (c : Fin k ↪o Fin m) : ℝ :=
  (A.submatrix r c).det

-- END SHARED DEFINITIONS: minors

/-- The open Euclidean unit ball of `ℝ^m`. -/
def unitBall (m : ℕ) : Set (Fin m → ℝ) :=
  {x | ∑ i, x i ^ 2 < 1}

/-- The quasiconvex envelope, over the quasiconvex minorants `g ≤ f` that are lower semicontinuous
and locally bounded (`⊥` when there is none). It is equal to `quasiconvexEnvelope`
(`quasiconvexEnvelope_eq_qcEnvelope`). -/
noncomputable def qcEnvelope (f : Matrix (Fin d) (Fin m) ℝ → ℝ) (A : Matrix (Fin d) (Fin m) ℝ) :
    EReal :=
  ⨆ (g : Matrix (Fin d) (Fin m) ℝ → ℝ)
    (_ : LowerSemicontinuous g ∧ IsLocallyBounded g ∧ Quasiconvex g ∧ ∀ B, g B ≤ f B),
    (g A : EReal)

end CalculusOfVariations
