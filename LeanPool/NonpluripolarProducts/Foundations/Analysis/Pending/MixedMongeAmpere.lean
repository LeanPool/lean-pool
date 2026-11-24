/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.MixedMongeAmpere
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BTTruncations
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PositiveDistributionMeasure
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MixedCoefficientPositivity

/-!
# Pending mixed bounded Bedford–Taylor foundation

Existence of the actual mixed bounded BT measure follows from the scalar-slot
Bedford–Taylor convergence theorem (`Pending.BedfordTaylor`), and uniqueness from
test-function separation. PSD mixed-coefficient positivity is proved by
Gram decomposition and determinant multilinearity. Mixed approximation
existence is derived from the existing scalar approximation theorem and that
coefficient theorem; it is not a separate hole.

The canonical measure is chosen from existence. Its diagonal specialization
uses only mixed-to-scalar testing on diagonal approximations and scalar
uniqueness, never the converse for arbitrary mixed approximations.

Sources: revised `sec:npp`; BEGZ §1.2 and `equ:nonpp`, `equ:welldef`,
`pro:basic` for the later non-pluripolar context. We retain the revised
`ddC = i ∂∂bar / (2π)` normalization, not an unspecified BEGZ normalization.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.MixedMongeAmpere

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

theorem isSmoothMixedPshOn_of_components {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (hu : ∀ i, IsSmoothPshOn U (u i)) :
    IsSmoothMixedPshOn U u := by
  refine ⟨hu, fun z hz => ?_⟩
  exact div_nonneg
    (mixedCoefficient_re_nonneg (fun i => complexHessian (u i) z)
      (fun i => (hu i).2.2 z hz)) (pow_nonneg Real.pi_pos.le n)

/-- Finite choice of scalar sequences gives a common tuple sequence. The
only additional mathematical dependency is PSD mixed-coefficient positivity. -/
theorem exists_decreasingMixedApproximation {Ω U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (hu : IsLocallyBoundedMixedPshOn Ω u)
    (hU : RelativelyCompactIn U Ω) :
    ∃ f, IsDecreasingMixedApproximation U u f := by
  have hex : ∀ i, ∃ f, IsDecreasingApproximation U (u i) f :=
    fun i => MongeAmpere.exists_decreasingApproximation (hu i) hU
  choose f hf using hex
  exact ⟨fun j i => f i j,
    fun j => isSmoothMixedPshOn_of_components (fun i => (hf i).1 j),
    fun i => (hf i).2.1, fun i => (hf i).2.2⟩

/-- Existence of a positive Borel measure, zero off Ω, finite on interior
compact sets, with convergence for every certified mixed smooth approximation.
All n components are genuine real locally bounded PSH functions. -/
theorem exists_localMixedBedfordTaylorMeasure {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (hu : IsLocallyBoundedMixedPshOn Ω u) :
    ∃ μ : Measure (ComplexModel n), IsLocalMixedBedfordTaylorMeasure Ω u μ :=
  BedfordTaylor.exists_isLocalMixedBedfordTaylorMeasure hu fun _ hU ↦
    exists_decreasingMixedApproximation hu hU

open scoped Distributions in
/-- Separation is on Ω, where interior compact finiteness gives locally finite
measures; zero extensions are not assumed locally finite at the boundary. -/
theorem localMixedBedfordTaylorMeasure_unique {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {μ ν : Measure (ComplexModel n)}
    (hμ : IsLocalMixedBedfordTaylorMeasure Ω u μ)
    (hν : IsLocalMixedBedfordTaylorMeasure Ω u ν) : μ = ν := by
  have hint : ∀ φ : 𝓓(Ω, ℝ), (∫ z, φ z ∂μ) = ∫ z, φ z ∂ν := by
    intro φ
    obtain ⟨δ, hδ, hδΩ⟩ :=
      φ.hasCompactSupport.exists_cthickening_subset_open Ω.isOpen φ.tsupport_subset
    let U : Opens (ComplexModel n) :=
      ⟨Metric.thickening δ (tsupport φ), Metric.isOpen_thickening⟩
    have hclosure :
        closure (U : Set (ComplexModel n)) ⊆ Metric.cthickening δ (tsupport φ) :=
      Metric.closure_thickening_subset_cthickening δ (tsupport φ)
    have hU : RelativelyCompactIn U Ω :=
      ⟨(φ.hasCompactSupport.cthickening).of_isClosed_subset isClosed_closure hclosure,
        hclosure.trans hδΩ⟩
    have hφU : tsupport φ ⊆ (U : Set (ComplexModel n)) :=
      Metric.self_subset_thickening hδ (tsupport φ)
    obtain ⟨f, hf⟩ := (hμ.2.2.2 U hU).1
    exact tendsto_nhds_unique ((hμ.2.2.2 U hU).2 f hf φ φ.continuous φ.hasCompactSupport hφU)
      ((hν.2.2.2 U hU).2 f hf φ φ.continuous φ.hasCompactSupport hφU)
  have hμrestrict : μ.restrict (Ω : Set (ComplexModel n)) = μ :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hμ.2.1)
  have hνrestrict : ν.restrict (Ω : Set (ComplexModel n)) = ν :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hν.2.1)
  exact hμrestrict.symm.trans
    ((BedfordTaylor.restrict_eq_of_testFunction_integral_eq hμ.2.2.1 hν.2.2.1 hint).trans
      hνrestrict)

/-- The mixed measure obtained from the diagonal Bedford–Taylor construction. -/
def canonicalMixedBedfordTaylorMeasure (Ω : Opens (ComplexModel n))
    (u : Fin n → ComplexModel n → ℝ) (hu : IsLocallyBoundedMixedPshOn Ω u) :
    Measure (ComplexModel n) :=
  Classical.choose (exists_localMixedBedfordTaylorMeasure hu)

theorem canonicalMixedBedfordTaylorMeasure_spec (Ω : Opens (ComplexModel n))
    (u : Fin n → ComplexModel n → ℝ) (hu : IsLocallyBoundedMixedPshOn Ω u) :
    IsLocalMixedBedfordTaylorMeasure Ω u (canonicalMixedBedfordTaylorMeasure Ω u hu) :=
  Classical.choose_spec (exists_localMixedBedfordTaylorMeasure hu)

theorem canonicalMixedBedfordTaylorMeasure_eq {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (hu : IsLocallyBoundedMixedPshOn Ω u)
    {μ : Measure (ComplexModel n)} (hμ : IsLocalMixedBedfordTaylorMeasure Ω u μ) :
    canonicalMixedBedfordTaylorMeasure Ω u hu = μ :=
  localMixedBedfordTaylorMeasure_unique (canonicalMixedBedfordTaylorMeasure_spec Ω u hu) hμ

theorem canonicalMixedBedfordTaylorMeasure_proof_independent
    {Ω : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → ℝ}
    (hu hv : IsLocallyBoundedMixedPshOn Ω u) :
    canonicalMixedBedfordTaylorMeasure Ω u hu = canonicalMixedBedfordTaylorMeasure Ω u hv := rfl

theorem canonicalMixedBedfordTaylorMeasure_compl (Ω : Opens (ComplexModel n))
    (u : Fin n → ComplexModel n → ℝ) (hu : IsLocallyBoundedMixedPshOn Ω u) :
    canonicalMixedBedfordTaylorMeasure Ω u hu (Ω : Set (ComplexModel n))ᶜ = 0 :=
  (canonicalMixedBedfordTaylorMeasure_spec Ω u hu).2.1

theorem canonicalMixedBedfordTaylorMeasure_finiteOnCompacts
    {Ω : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → ℝ}
    (hu : IsLocallyBoundedMixedPshOn Ω u)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    canonicalMixedBedfordTaylorMeasure Ω u hu K < ⊤ :=
  (canonicalMixedBedfordTaylorMeasure_spec Ω u hu).2.2.1 K hK hKΩ

theorem canonicalMixedBedfordTaylorMeasure_tendsto
    {Ω U : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → ℝ}
    (hu : IsLocallyBoundedMixedPshOn Ω u) (hU : RelativelyCompactIn U Ω)
    {f : ℕ → Fin n → ComplexModel n → ℝ} (hf : IsDecreasingMixedApproximation U u f) :
    MixedWeaklyTendsTo U f hf.1 (canonicalMixedBedfordTaylorMeasure Ω u hu) :=
  ((canonicalMixedBedfordTaylorMeasure_spec Ω u hu).2.2.2 U hU).2 f hf

/-- The scalar local-boundedness hypothesis is explicit even when n=0, when
the mixed tuple is empty. Only diagonal approximations are used here. -/
theorem localMixedBedfordTaylorMeasure_diagonal_to_scalar
    {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) {μ : Measure (ComplexModel n)}
    (hμ : IsLocalMixedBedfordTaylorMeasure Ω (fun _ => u) μ) :
    IsLocalBedfordTaylorMeasure Ω u μ := by
  refine ⟨hu, hμ.2.1, hμ.2.2.1, fun U hU => ?_⟩
  refine ⟨MongeAmpere.exists_decreasingApproximation hu hU, fun f hf => ?_⟩
  have hm := (hμ.2.2.2 U hU).2 (fun j _ => f j)
    (IsDecreasingMixedApproximation.diagonal hf)
  intro φ hφ hK hsupport
  simpa only [smoothMixedMeasure_diagonal U _ (hf.1 _)] using hm φ hφ hK hsupport

theorem canonicalMixedBedfordTaylorMeasure_diagonal (Ω : Opens (ComplexModel n))
    (u : ComplexModel n → ℝ) (hu : IsLocallyBoundedPshOn Ω u) :
    canonicalMixedBedfordTaylorMeasure Ω (fun _ => u) (fun _ => hu) =
      MongeAmpere.canonicalBedfordTaylorMeasure Ω u hu := by
  exact MongeAmpere.localBedfordTaylorMeasure_unique
    (localMixedBedfordTaylorMeasure_diagonal_to_scalar hu
      (canonicalMixedBedfordTaylorMeasure_spec Ω (fun _ => u) (fun _ => hu)))
    (MongeAmpere.canonicalBedfordTaylorMeasure_spec Ω u hu)

/-- Local boundedness of a tuple is symmetric in the slots. -/
theorem IsLocallyBoundedMixedPshOn.perm {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (hu : IsLocallyBoundedMixedPshOn Ω u)
    (τ : Equiv.Perm (Fin n)) : IsLocallyBoundedMixedPshOn Ω (fun i => u (τ i)) :=
  fun i => hu (τ i)

/-- **The bounded mixed Bedford–Taylor relation is symmetric in the slots.**
The mixed coefficient is a symmetric function of the Hessians, so permuting the
tuple leaves every smooth approximating measure — and hence the limit —
unchanged. -/
theorem IsLocalMixedBedfordTaylorMeasure.perm {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {μ : Measure (ComplexModel n)}
    (hμ : IsLocalMixedBedfordTaylorMeasure Ω u μ) (τ : Equiv.Perm (Fin n)) :
    IsLocalMixedBedfordTaylorMeasure Ω (fun i => u (τ i)) μ := by
  refine ⟨fun i => hμ.1 (τ i), hμ.2.1, hμ.2.2.1, fun U hU => ⟨?_, ?_⟩⟩
  · obtain ⟨f, hf⟩ := (hμ.2.2.2 U hU).1
    exact ⟨fun j i => f j (τ i), hf.perm τ⟩
  · intro f hf
    have hback : (fun i => u (τ (τ.symm i))) = u := funext fun i => by simp
    have hg : IsDecreasingMixedApproximation U u (fun j i => f j (τ.symm i)) := by
      simpa only [hback] using hf.perm τ.symm
    have hgm := (hμ.2.2.2 U hU).2 _ hg
    intro φ hφ hφc hφU
    have hdens : ∀ j, smoothMixedMeasure U (f j) (hf.1 j) =
        smoothMixedMeasure U (fun i => f j (τ.symm i)) (hg.1 j) := by
      intro j
      simp only [smoothMixedMeasure]
      refine congrArg _ (funext fun z => congrArg ENNReal.ofReal ?_)
      simp
    simpa only [hdens] using hgm φ hφ hφc hφU

/-- Permuting the slots does not change the canonical bounded mixed
Bedford–Taylor measure. -/
theorem canonicalMixedBedfordTaylorMeasure_perm {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (hu : IsLocallyBoundedMixedPshOn Ω u)
    (τ : Equiv.Perm (Fin n)) (hv : IsLocallyBoundedMixedPshOn Ω (fun i => u (τ i))) :
    canonicalMixedBedfordTaylorMeasure Ω (fun i => u (τ i)) hv =
      canonicalMixedBedfordTaylorMeasure Ω u hu :=
  canonicalMixedBedfordTaylorMeasure_eq hv
    (IsLocalMixedBedfordTaylorMeasure.perm (canonicalMixedBedfordTaylorMeasure_spec Ω u hu) τ)

end SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
