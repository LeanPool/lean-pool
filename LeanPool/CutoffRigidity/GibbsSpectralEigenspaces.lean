/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsCompactEmbedding
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Actual form-operator eigenspaces from the genuine compact resolvent

The operator eigenspace is identified exactly with its compact-resolvent
counterpart. Thus finite dimensionality is derived for actual Hilbert
operator eigenvectors, without assuming any differentiable representative.
-/

public section

namespace CutoffRigidity

open MeasureTheory

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Distinct actual self-adjoint operator eigenspaces are orthogonal,
without any smoothness assumption on the eigenvectors. -/
theorem gibbsOperatorEigen_inner_eq_zero_of_ne {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) {a b : ℝ} (hab : a ≠ b)
    (u : gibbsOperatorEigenspace hV hprob a) (v : gibbsOperatorEigenspace hV hprob b) :
    inner ℝ (u : E →₂[gibbsMeasure volume V] ℝ) (v : E →₂[gibbsMeasure volume V] ℝ) = 0 := by
  let A := gibbsPositiveGenerator hV hprob
  obtain ⟨uv, huv, hau⟩ := A.mem_graph_iff.mp u.property
  obtain ⟨vv, hvv, hav⟩ := A.mem_graph_iff.mp v.property
  change (uv : E →₂[gibbsMeasure volume V] ℝ) = (u : E →₂[gibbsMeasure volume V] ℝ) at huv
  change (vv : E →₂[gibbsMeasure volume V] ℝ) = (v : E →₂[gibbsMeasure volume V] ℝ) at hvv
  change A uv = a • (u : E →₂[gibbsMeasure volume V] ℝ) at hau
  change A vv = b • (v : E →₂[gibbsMeasure volume V] ℝ) at hav
  have hp := positiveResolventOperator_formalAdjoint (gibbsL2Resolvent hV hprob)
    (gibbsL2Resolvent_injective hV hprob) (gibbsL2Resolvent_symmetric hV hprob) uv vv
  change inner ℝ (A uv) (vv : E →₂[gibbsMeasure volume V] ℝ) =
    inner ℝ (uv : E →₂[gibbsMeasure volume V] ℝ) (A vv) at hp
  rw [hau, hav, huv, hvv, real_inner_smul_left, real_inner_smul_right] at hp
  exact (mul_eq_zero.mp (show (a - b) * inner ℝ
    (u : E →₂[gibbsMeasure volume V] ℝ) (v : E →₂[gibbsMeasure volume V] ℝ) = 0 by
      nlinarith)).resolve_left
      (sub_ne_zero.mpr hab)

/-- Exact equality of actual Hilbert eigenspaces, with no regularity premise. -/
theorem gibbsOperatorEigenspace_eq_resolvent_eigenspace {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ) (hrate : 1 + rate ≠ 0) :
    gibbsOperatorEigenspace hV hprob rate =
      Module.End.eigenspace (gibbsL2Resolvent hV hprob).toLinearMap ((1 + rate)⁻¹) := by
  ext u
  rw [mem_gibbsOperatorEigenspace_iff_resolvent, Module.End.mem_eigenspace_iff]
  change gibbsL2Resolvent hV hprob ((1 + rate) • u) = u ↔
    gibbsL2Resolvent hV hprob u = (1 + rate)⁻¹ • u
  rw [map_smul]
  constructor
  · intro h
    have hi := congrArg (fun v => (1 + rate)⁻¹ • v) h
    simpa only [smul_smul, inv_mul_cancel₀ hrate, one_smul] using hi
  · intro h
    rw [h, smul_smul, mul_inv_cancel₀ hrate, one_smul]

/-- Every nonnegative actual operator eigenspace is finite dimensional,
by compactness proved from the source curvature assumptions. -/
theorem gibbsOperatorEigenspace_finiteDimensional {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (rate : ℝ) (hrate : 0 ≤ rate) : FiniteDimensional ℝ (gibbsOperatorEigenspace hV hprob rate)
      := by
  rw [gibbsOperatorEigenspace_eq_resolvent_eigenspace hV hprob rate (by positivity)]
  exact ContinuousLinearMap.finite_dimensional_eigenspace
    (gibbsL2Resolvent_isCompactOperator hV hprob ρ hρ hHess)
    ((1 + rate)⁻¹) (inv_ne_zero (by positivity))

/-- The compact actual Gibbs resolvent has a complete family of Hilbert
operator eigenspaces; this invokes the genuine compact spectral theorem. -/
theorem gibbsL2Resolvent_eigenspaces_orthogonal_eq_bot {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    (⨆ r : ℝ, Module.End.eigenspace (gibbsL2Resolvent hV hprob).toLinearMap r)ᗮ = ⊥ := by
  apply ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (gibbsL2Resolvent_isCompactOperator hV hprob ρ hρ hHess)
  intro f g
  exact gibbsL2Resolvent_symmetric hV hprob f g

/-- Every actual resolvent eigenvector belongs to an actual form-operator
eigenspace. The zero resolvent eigenspace vanishes by proved injectivity. -/
theorem gibbsL2Resolvent_eigenspaces_le_operator_eigenspaces {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    (⨆ r : ℝ, Module.End.eigenspace (gibbsL2Resolvent hV hprob).toLinearMap r) ≤
      ⨆ rate : ℝ, gibbsOperatorEigenspace hV hprob rate := by
  apply iSup_le
  intro r u hu
  by_cases hr : r = 0
  · subst r
    have hzero : gibbsL2Resolvent hV hprob u = 0 := by
      simpa only [Module.End.mem_eigenspace_iff, zero_smul, ContinuousLinearMap.coe_coe] using hu
    have hu0 : u = 0 := gibbsL2Resolvent_injective hV hprob (by simpa only [map_zero] using hzero)
    subst u
    exact Submodule.zero_mem _
  · have hone : 1 + (r⁻¹ - 1) = r⁻¹ := by ring
    have heq : gibbsOperatorEigenspace hV hprob (r⁻¹ - 1) =
        Module.End.eigenspace (gibbsL2Resolvent hV hprob).toLinearMap r := by
      rw [gibbsOperatorEigenspace_eq_resolvent_eigenspace hV hprob _
        (by rw [hone]; exact inv_ne_zero hr), hone, inv_inv]
    exact (le_iSup (fun rate : ℝ => gibbsOperatorEigenspace hV hprob rate) (r⁻¹ - 1))
      (heq.symm ▸ hu)

/-- Actual eigenspaces of the constructed self-adjoint form operator have
dense Hilbert span. This is a genuine compact-resolvent spectral conclusion,
without any eigenfunction regularity assumption. -/
theorem gibbsOperator_eigenspaces_orthogonal_eq_bot {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    (⨆ rate : ℝ, gibbsOperatorEigenspace hV hprob rate)ᗮ = ⊥ := by
  have hle := Submodule.orthogonal_le (gibbsL2Resolvent_eigenspaces_le_operator_eigenspaces hV
    hprob)
  rw [gibbsL2Resolvent_eigenspaces_orthogonal_eq_bot hV hprob ρ hρ hHess] at hle
  exact le_antisymm hle bot_le

end CutoffRigidity
