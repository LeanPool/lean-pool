/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.MongeAmpere
public import Mathlib.Data.Fintype.Perm

/-!
# Mixed Hessian densities and local mixed Bedford–Taylor testing

The coefficient is the sum of determinants of matrices with one row from
each Hessian. Individual row-selected matrices need not be Hermitian or PSD.
The measure constructor therefore requires nonnegativity of the actual sum,
in addition to the scalar smooth PSH certificates. The normalization remains
`ddC = i ∂∂bar / (2π)`, so the mixed density is `Re C / π^n`.

The bounded mixed BT relation uses only compact subsets inside the domain
and all componentwise decreasing certified smooth approximations. It makes
no claim about unbounded products, boundary finiteness, or total mass.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere

open MongeAmpere

variable {n : ℕ}

/-- The coefficient of `t₁ ⋯ tₙ` in `det (∑ i, tᵢ Hᵢ)`, given explicitly
by row multilinearity. No positivity of an individual summand is assumed. -/
def mixedCoefficient (H : Fin n → Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), Matrix.det (fun j k => H (σ j) j k)

@[simp] theorem mixedCoefficient_diagonal (H : Matrix (Fin n) (Fin n) ℂ) :
    mixedCoefficient (fun _ => H) = (n.factorial : ℂ) * H.det := by
  simp [mixedCoefficient, Fintype.card_perm]

/-- Relabeling the slots reindexes the permutation sum by left multiplication. -/
@[simp] theorem mixedCoefficient_perm
    (H : Fin n → Matrix (Fin n) (Fin n) ℂ) (τ : Equiv.Perm (Fin n)) :
    mixedCoefficient (fun i => H (τ i)) = mixedCoefficient H := by
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ : Equiv.Perm (Fin n) =>
    Matrix.det (fun j k => H (σ j) j k))

/-- The real mixed Monge–Ampère density of smooth potentials in coordinates. -/
def mixedDensity (u : Fin n → ComplexModel n → ℝ) (z : ComplexModel n) : ℝ :=
  (mixedCoefficient (fun i => complexHessian (u i) z)).re / Real.pi ^ n

@[simp] theorem mixedDensity_diagonal (u : ComplexModel n → ℝ) (z : ComplexModel n) :
    mixedDensity (fun _ => u) z = smoothDensity u z := by
  simp only [mixedDensity, mixedCoefficient_diagonal, Complex.mul_re,
    Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, smoothDensity]
  ring

@[simp] theorem mixedDensity_perm (u : Fin n → ComplexModel n → ℝ)
    (τ : Equiv.Perm (Fin n)) (z : ComplexModel n) :
    mixedDensity (fun i => u (τ i)) z = mixedDensity u z := by
  exact congrArg (fun c : ℂ => c.re / Real.pi ^ n)
    (mixedCoefficient_perm (fun i => complexHessian (u i) z) τ)

/-- Smooth PSH components and nonnegativity of the genuine mixed density.
Recovering the second field from the first is a separate algebraic theorem. -/
structure IsSmoothMixedPshOn (U : Opens (ComplexModel n))
    (u : Fin n → ComplexModel n → ℝ) : Prop where
  component : ∀ i, IsSmoothPshOn U (u i)
  density_nonneg : ∀ z ∈ U, 0 ≤ mixedDensity u z

theorem IsSmoothMixedPshOn.diagonal {U : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsSmoothPshOn U u) :
    IsSmoothMixedPshOn U (fun _ => u) := by
  refine ⟨fun _ => hu, fun z hz => ?_⟩
  rw [mixedDensity_diagonal]
  exact smoothDensity_nonneg (hu.2.2 z hz)

theorem IsSmoothMixedPshOn.perm {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (hu : IsSmoothMixedPshOn U u)
    (τ : Equiv.Perm (Fin n)) : IsSmoothMixedPshOn U (fun i => u (τ i)) := by
  refine ⟨fun i => hu.component (τ i), fun z hz => ?_⟩
  rw [mixedDensity_perm]
  exact hu.density_nonneg z hz

theorem IsSmoothMixedPshOn.mono {U V : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (hu : IsSmoothMixedPshOn U u) (hVU : V ≤ U) :
    IsSmoothMixedPshOn V u := by
  refine ⟨fun i => ?_, fun z hz => hu.density_nonneg z (hVU hz)⟩
  exact ⟨(hu.component i).1.mono hVU, (hu.component i).2.1.mono hVU,
    fun z hz => (hu.component i).2.2 z (hVU hz)⟩

/-- Standard Lebesgue measure with the certified mixed density, zero off U. -/
def smoothMixedMeasure (U : Opens (ComplexModel n)) (u : Fin n → ComplexModel n → ℝ)
    (_hu : IsSmoothMixedPshOn U u) : Measure (ComplexModel n) :=
  (volume.restrict (U : Set (ComplexModel n))).withDensity
    (fun z => ENNReal.ofReal (mixedDensity u z))

theorem smoothMixedMeasure_proof_independent {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (hu hv : IsSmoothMixedPshOn U u) :
    smoothMixedMeasure U u hu = smoothMixedMeasure U u hv := rfl

theorem smoothMixedMeasure_weight_toReal {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (hu : IsSmoothMixedPshOn U u)
    {z : ComplexModel n} (hz : z ∈ U) :
    (ENNReal.ofReal (mixedDensity u z)).toReal = mixedDensity u z :=
  ENNReal.toReal_ofReal (hu.density_nonneg z hz)

@[simp] theorem smoothMixedMeasure_diagonal (U : Opens (ComplexModel n))
    (u : ComplexModel n → ℝ) (hu : IsSmoothPshOn U u)
    (hm : IsSmoothMixedPshOn U (fun _ => u)) :
    smoothMixedMeasure U (fun _ => u) hm = smoothMeasure U u hu := by
  simp only [smoothMixedMeasure, smoothMeasure, mixedDensity_diagonal]

theorem smoothMixedMeasure_perm (U : Opens (ComplexModel n))
    (u : Fin n → ComplexModel n → ℝ) (hu : IsSmoothMixedPshOn U u)
    (τ : Equiv.Perm (Fin n)) (hv : IsSmoothMixedPshOn U (fun i => u (τ i))) :
    smoothMixedMeasure U (fun i => u (τ i)) hv = smoothMixedMeasure U u hu := by
  simp only [smoothMixedMeasure, mixedDensity_perm]

theorem smoothMixedMeasure_restrict {U V : Opens (ComplexModel n)} (hVU : V ≤ U)
    (u : Fin n → ComplexModel n → ℝ) (hu : IsSmoothMixedPshOn U u)
    (hv : IsSmoothMixedPshOn V u) :
    (smoothMixedMeasure U u hu).restrict (V : Set (ComplexModel n)) =
      smoothMixedMeasure V u hv := by
  rw [smoothMixedMeasure, restrict_withDensity V.isOpen.measurableSet,
    Measure.restrict_restrict_of_subset hVU]
  rfl

/-- There are exactly n real locally bounded PSH components. -/
def IsLocallyBoundedMixedPshOn (Ω : Opens (ComplexModel n))
    (u : Fin n → ComplexModel n → ℝ) : Prop :=
  ∀ i, IsLocallyBoundedPshOn Ω (u i)

/-- A common sequence index, with pointwise decrease and convergence in each
slot; every tuple has the genuine mixed nonnegativity certificate. -/
def IsDecreasingMixedApproximation (U : Opens (ComplexModel n))
    (u : Fin n → ComplexModel n → ℝ) (f : ℕ → Fin n → ComplexModel n → ℝ) : Prop :=
  (∀ j, IsSmoothMixedPshOn U (f j)) ∧
    (∀ i z, z ∈ U → Antitone (fun j => f j i z)) ∧
    ∀ i z, z ∈ U → Tendsto (fun j => f j i z) atTop (𝓝 (u i z))

theorem IsDecreasingMixedApproximation.component {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {f : ℕ → Fin n → ComplexModel n → ℝ}
    (hf : IsDecreasingMixedApproximation U u f) (i : Fin n) :
    IsDecreasingApproximation U (u i) (fun j => f j i) :=
  ⟨fun j => (hf.1 j).component i, hf.2.1 i, hf.2.2 i⟩

theorem IsDecreasingMixedApproximation.diagonal {U : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} {f : ℕ → ComplexModel n → ℝ}
    (hf : IsDecreasingApproximation U u f) :
    IsDecreasingMixedApproximation U (fun _ => u) (fun j _ => f j) :=
  ⟨fun j => IsSmoothMixedPshOn.diagonal (hf.1 j), fun _ => hf.2.1, fun _ => hf.2.2⟩

theorem IsDecreasingMixedApproximation.perm {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {f : ℕ → Fin n → ComplexModel n → ℝ}
    (hf : IsDecreasingMixedApproximation U u f) (τ : Equiv.Perm (Fin n)) :
    IsDecreasingMixedApproximation U (fun i => u (τ i)) (fun j i => f j (τ i)) :=
  ⟨fun j => (hf.1 j).perm τ, fun i => hf.2.1 (τ i), fun i => hf.2.2 (τ i)⟩

theorem IsSmoothMixedPshOn.constantApproximation {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (hu : IsSmoothMixedPshOn U u) :
    IsDecreasingMixedApproximation U u (fun _ => u) :=
  ⟨fun _ => hu, fun _ _ _ _ _ _ => le_rfl, fun _ _ _ => tendsto_const_nhds⟩

/-- Vague convergence on U; tests have compact topological support in U. -/
def MixedWeaklyTendsTo (U : Opens (ComplexModel n))
    (f : ℕ → Fin n → ComplexModel n → ℝ) (hf : ∀ j, IsSmoothMixedPshOn U (f j))
    (μ : Measure (ComplexModel n)) : Prop :=
  ∀ φ : ComplexModel n → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U →
    Tendsto (fun j => ∫ z, φ z ∂(smoothMixedMeasure U (f j) (hf j))) atTop
      (𝓝 (∫ z, φ z ∂μ))

/-- The actual mixed bounded BT relation. The existence clause prevents
vacuous testing. No finiteness at boundary points of Ω is required. -/
def IsLocalMixedBedfordTaylorMeasure (Ω : Opens (ComplexModel n))
    (u : Fin n → ComplexModel n → ℝ) (μ : Measure (ComplexModel n)) : Prop :=
  IsLocallyBoundedMixedPshOn Ω u ∧
    μ (Ω : Set (ComplexModel n))ᶜ = 0 ∧
    (∀ K : Set (ComplexModel n), IsCompact K → K ⊆ Ω → μ K < ⊤) ∧
    ∀ U : Opens (ComplexModel n), RelativelyCompactIn U Ω →
      (∃ f, IsDecreasingMixedApproximation U u f) ∧
      ∀ f (hf : IsDecreasingMixedApproximation U u f), MixedWeaklyTendsTo U f hf.1 μ

theorem IsLocalMixedBedfordTaylorMeasure.approximations_exist
    {Ω U : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → ℝ}
    {μ : Measure (ComplexModel n)} (hμ : IsLocalMixedBedfordTaylorMeasure Ω u μ)
    (hU : RelativelyCompactIn U Ω) : ∃ f, IsDecreasingMixedApproximation U u f :=
  (hμ.2.2.2 U hU).1

theorem IsLocalMixedBedfordTaylorMeasure.sequence_independent
    {Ω U : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → ℝ}
    {μ : Measure (ComplexModel n)} (hμ : IsLocalMixedBedfordTaylorMeasure Ω u μ)
    (hU : RelativelyCompactIn U Ω) {f g : ℕ → Fin n → ComplexModel n → ℝ}
    (hf : IsDecreasingMixedApproximation U u f) (hg : IsDecreasingMixedApproximation U u g) :
    MixedWeaklyTendsTo U f hf.1 μ ∧ MixedWeaklyTendsTo U g hg.1 μ :=
  ⟨(hμ.2.2.2 U hU).2 f hf, (hμ.2.2.2 U hU).2 g hg⟩

end SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
