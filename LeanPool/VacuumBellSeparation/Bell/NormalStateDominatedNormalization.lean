/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.SeparatingVectorDominatedDensity
public import LeanPool.VacuumBellSeparation.Bell.NormalStateCompression

/-!
# Normalizing positive dominated approximants in the full dual norm

The normalizing mass is the actual positive-functional norm, equal to its
value at identity. Closeness to a state makes this mass nonzero. The error
after normalization is at most twice the original dual-norm error.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open scoped ComplexOrder Topology

section CStar
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Unit mass positive functional. -/
def unitMassPositiveFunctional (ψ : A →ₚ[ℂ] ℂ) : A →ₚ[ℂ] ℂ :=
  distillationScaleFunctional
    ‖(PositiveContinuousLinearMap.ofClass ψ).toContinuousLinearMap‖⁻¹
    (inv_nonneg.mpr (norm_nonneg _)) ψ

theorem unitMassPositiveFunctional_one (ψ : A →ₚ[ℂ] ℂ)
    (hp : 0 < ‖(PositiveContinuousLinearMap.ofClass ψ).toContinuousLinearMap‖) :
    unitMassPositiveFunctional ψ 1 = 1 := by
  change ‖(PositiveContinuousLinearMap.ofClass ψ).toContinuousLinearMap‖⁻¹ • ψ 1 = 1
  rw [positiveFunctional_one_eq_norm ψ, Complex.real_smul, ← Complex.ofReal_mul,
    inv_mul_cancel₀ hp.ne', Complex.ofReal_one]

theorem unitMassPositiveFunctional_dual_error_le (ψ ω : A →ₚ[ℂ] ℂ)
    (hω : ω 1 = 1)
    (hp : 0 < ‖(PositiveContinuousLinearMap.ofClass ψ).toContinuousLinearMap‖) :
    ‖(PositiveContinuousLinearMap.ofClass ω).toContinuousLinearMap -
      (PositiveContinuousLinearMap.ofClass (unitMassPositiveFunctional ψ)).toContinuousLinearMap‖ ≤
      2 * ‖(PositiveContinuousLinearMap.ofClass ω).toContinuousLinearMap -
        (PositiveContinuousLinearMap.ofClass ψ).toContinuousLinearMap‖ := by
  let f := (PositiveContinuousLinearMap.ofClass ψ).toContinuousLinearMap
  let g := (PositiveContinuousLinearMap.ofClass ω).toContinuousLinearMap
  let r := (PositiveContinuousLinearMap.ofClass (unitMassPositiveFunctional
    ψ)).toContinuousLinearMap
  have hg : ‖g‖ = 1 := by
    have h := congrArg Complex.re (positiveFunctional_one_eq_norm ω)
    simpa only [hω, Complex.one_re, Complex.ofReal_re] using h.symm
  have hr : ‖r‖ = 1 := by
    have h := congrArg Complex.re (positiveFunctional_one_eq_norm (unitMassPositiveFunctional ψ))
    simpa only [unitMassPositiveFunctional_one ψ hp, Complex.one_re, Complex.ofReal_re] using h.symm
  have he : f = ‖f‖ • r := by
    change f = ‖f‖ • (‖f‖⁻¹ • f)
    rw [smul_smul, mul_inv_cancel₀ hp.ne', one_smul]
  have hfr : ‖f - r‖ ≤ ‖g - f‖ := by
    have hd : f - r = (‖f‖ - 1) • r := by rw [sub_smul, one_smul, ← he]
    rw [hd, norm_smul, Real.norm_eq_abs, hr, mul_one]
    simpa only [hg, norm_sub_rev] using abs_norm_sub_norm_le f g
  change ‖g - r‖ ≤ 2 * ‖g - f‖
  have h := norm_sub_le_norm_sub_add_norm_sub g f r
  linarith

end CStar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance unitMass_vna_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_vonNeumannAlgebra M

/-- A bound by a finite nonnegative multiple gives a strictly positive
coefficient below one. The reference need not have unit mass here. -/
theorem exists_small_dual_domination (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (f : StrongDual ℂ M.toStarSubalgebra)
    (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ X : M.toStarSubalgebra, 0 ≤ X → f X ≤ C • φ X) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ X : M.toStarSubalgebra,
      0 ≤ X → t • f X ≤ φ X := by
  let t : ℝ := (C + 2)⁻¹
  have hd : 0 < C + 2 := by linarith
  have ht : 0 < t := inv_pos.mpr hd
  have he : t * (C + 2) = 1 := inv_mul_cancel₀ hd.ne'
  have htc : 0 ≤ t * C := mul_nonneg ht.le hC
  have ht1 : t < 1 := by nlinarith
  have htc1 : t * C ≤ 1 := by nlinarith
  refine ⟨t, ht, ht1, ?_⟩
  intro X hX
  have h := smul_le_smul_of_nonneg_left (hdom X hX) ht.le
  have hb : (t * C) • φ X ≤ φ X := by
    simpa only [one_smul] using smul_le_smul_of_nonneg_right htc1 (φ.map_nonneg hX)
  have h' : t • f X ≤ (t * C) • φ X := by
    simpa only [smul_smul] using h
  exact h'.trans hb

/-- This generic normalization step assumes the displayed positive-cone
closure premise; separate density theorems discharge it for faithful references. -/
theorem normalState_mem_closure_dominated_of_positive_closure (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hnφ : IsNormalFunctional M φ)
    (ω : HC00.NormalStateSpace M)
    (hc : ω.1 ∈ (dominatedPositiveDualMonoid M φ).topologicalClosure) :
    ω ∈ closure {ρ : HC00.NormalStateSpace M |
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ X : M.toStarSubalgebra,
        0 ≤ X → t • ρ.1 X ≤ φ X} := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨g, hg, hd⟩ := Metric.mem_closure_iff.mp hc (min (1 / 2) (ε / 3))
    (lt_min (by norm_num) (by positivity))
  obtain ⟨hgpos, C, hC, hdom⟩ := hg
  let ψ : M.toStarSubalgebra →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ g.toLinearMap hgpos
  obtain ⟨ωp, hωp, hωeq⟩ := ω.2.1
  have heω : (PositiveContinuousLinearMap.ofClass ωp).toContinuousLinearMap = ω.1 :=
    ContinuousLinearMap.ext hωeq
  have hgω : ‖ω.1 - g‖ < min (1 / 2) (ε / 3) := by simpa only [dist_eq_norm] using hd
  have hnω : ‖ω.1‖ = 1 := by
    have h := congrArg Complex.re (positiveFunctional_one_eq_norm ωp)
    simpa only [hωp, Complex.one_re, Complex.ofReal_re, heω] using h.symm
  have hp : 0 < ‖g‖ := by
    have h := norm_sub_norm_le ω.1 g
    have hb := hgω.trans_le (min_le_left _ _)
    rw [hnω] at h
    linarith
  let r := (PositiveContinuousLinearMap.ofClass (unitMassPositiveFunctional
    ψ)).toContinuousLinearMap
  have hrpos (X : M.toStarSubalgebra) (hX : 0 ≤ X) : 0 ≤ r X :=
    (unitMassPositiveFunctional ψ).map_nonneg hX
  have hrdom (X : M.toStarSubalgebra) (hX : 0 ≤ X) : r X ≤ (‖g‖⁻¹ * C) • φ X := by
    change ‖g‖⁻¹ • g X ≤ _
    simpa only [smul_smul] using
      smul_le_smul_of_nonneg_left (hdom X hX) (inv_nonneg.mpr (norm_nonneg _))
  have hrn : IsNormalStateFunctional M r :=
    ⟨⟨unitMassPositiveFunctional ψ, unitMassPositiveFunctional_one ψ hp, fun _ => rfl⟩,
      isNormalFunctional_of_dual_domination M φ hnφ r hrpos
        (‖g‖⁻¹ * C) (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) hC) hrdom⟩
  refine ⟨⟨r, hrn⟩, exists_small_dual_domination M φ r (‖g‖⁻¹ * C)
    (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) hC) hrdom, ?_⟩
  change dist ω.1 r < ε
  rw [dist_eq_norm]
  have hb := unitMassPositiveFunctional_dual_error_le ψ ωp hωp hp
  rw [heω] at hb
  have hdε := hgω.trans_le (min_le_right _ _)
  change ‖ω.1 - r‖ ≤ 2 * ‖ω.1 - g‖ at hb
  linarith

end VacuumBellSeparation.Bipartite
