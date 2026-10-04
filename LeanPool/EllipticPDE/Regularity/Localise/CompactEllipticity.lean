/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.Localise.LocalOp


/-!
# Uniform ellipticity from pointwise positive definiteness

`SmoothOpOn.elliptic` asks directly for a uniform ellipticity constant on `U`. In practice a
coefficient matrix is more often known through pointwise positive definiteness together with
continuity, with no uniform constant given in advance: this file supplies the compactness
argument that produces one on any compact subset, an alternative route to discharging
`SmoothOpOn.elliptic` when `U` is exhausted by compact sets.

The constant comes from a minimum of the quadratic form over the compact product of the base set
with the unit sphere of directions, which is positive because the integrand is, by continuity and
compactness of that product.

## Main declarations

* `exists_uniform_elliptic_of_continuousOn`: a matrix field continuous and pointwise positive
  definite on a compact set is uniformly elliptic there, with an explicit ellipticity constant.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-- **Uniform ellipticity on a compact set from pointwise positivity.** A matrix field continuous
on a compact `K` and positive definite at every point of `K` is uniformly elliptic on `K`. The
constant is a minimum of the quadratic form over `K` against the unit sphere of directions,
attained and positive by continuity and compactness. -/
theorem exists_uniform_elliptic_of_continuousOn {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {a : X → Fin d → Fin d → ℝ}
    (ha : ∀ i j, ContinuousOn (fun x => a x i j) K)
    (hpos : ∀ x ∈ K, ∀ ξ : Fin d → ℝ, ξ ≠ 0 → 0 < ∑ i, ∑ j, a x i j * ξ i * ξ j) :
    ∃ lam > 0, ∀ x ∈ K, ∀ ξ : Fin d → ℝ, lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j := by
  set S : Set (Fin d → ℝ) := {ξ | ∑ i, ξ i ^ 2 = 1} with hSdef
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact isClosed_eq (continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2)
        continuous_const
    · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun ξ hξ => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      have hle : ξ i ^ 2 ≤ ∑ j, ξ j ^ 2 :=
        Finset.single_le_sum (f := fun j => ξ j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      rw [hξ] at hle
      rw [Real.norm_eq_abs]
      nlinarith [abs_nonneg (ξ i), sq_abs (ξ i)]
  set F : X × (Fin d → ℝ) → ℝ := fun p => ∑ i, ∑ j, a p.1 i j * p.2 i * p.2 j with hF
  have hFc : ContinuousOn F (K ×ˢ S) := by
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    exact (((ha i j).comp continuousOn_fst (fun p hp => hp.1)).mul
      ((continuous_apply i).comp continuous_snd).continuousOn).mul
      ((continuous_apply j).comp continuous_snd).continuousOn
  have scale : ∀ m : ℝ, 0 < m → (∀ x ∈ K, ∀ η ∈ S, m ≤ F (x, η)) →
      ∀ x ∈ K, ∀ ξ : Fin d → ℝ, m * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j := by
    intro m _ hm x hx ξ
    set s := Real.sqrt (∑ i, ξ i ^ 2) with hs
    have hsum0 : 0 ≤ ∑ i, ξ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    by_cases h0 : ∑ i, ξ i ^ 2 = 0
    · have hξ : ∀ i, ξ i = 0 := fun i => by
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (ξ i))).1 h0 i
          (Finset.mem_univ i)
        exact pow_eq_zero_iff (two_ne_zero) |>.1 this
      simp [hξ]
    · have hspos : 0 < s := Real.sqrt_pos.2 (lt_of_le_of_ne hsum0 (Ne.symm h0))
      have hs2 : s ^ 2 = ∑ i, ξ i ^ 2 := Real.sq_sqrt hsum0
      have hη : (fun i => ξ i / s) ∈ S := by
        change ∑ i, (ξ i / s) ^ 2 = 1
        simp_rw [div_pow]
        rw [← Finset.sum_div, ← hs2, div_self (by positivity)]
      have hq := hm x hx _ hη
      simp only [hF] at hq
      have hexp : ∑ i, ∑ j, a x i j * (ξ i / s) * (ξ j / s)
          = (∑ i, ∑ j, a x i j * ξ i * ξ j) / s ^ 2 := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ => ?_
        field_simp
      rw [hexp, le_div_iff₀ (by positivity), hs2] at hq
      linarith
  rcases (K ×ˢ S).eq_empty_or_nonempty with hE | hne
  · refine ⟨1, one_pos, scale 1 one_pos fun x hx η hη => ?_⟩
    exact absurd (show (x, η) ∈ K ×ˢ S from ⟨hx, hη⟩) (by simp [hE])
  · obtain ⟨p, hp, hmin⟩ := (hK.prod hSc).exists_isMinOn hne hFc
    have hp2 : p.2 ≠ 0 := by
      intro h
      have := hp.2
      simp [hSdef, h] at this
    have hFp : 0 < F p := hpos p.1 hp.1 p.2 hp2
    exact ⟨F p, hFp, scale (F p) hFp fun x hx η hη => hmin ⟨hx, hη⟩⟩

end EllipticPdes.Regularity
