/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MonotoneStrongLimit

/-!
# Bounded increasing positive operator nets

The index is an arbitrary nonempty directed preorder. No countable cofinal
subset or sequential normality assumption is used. Vectorwise Cauchy filters
are obtained from the supremum of each real quadratic form.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]

/-- A bounded increasing positive operator net is Cauchy on every vector. -/
theorem cauchy_map_apply_of_monotone_nonneg_bounded
    (A : ι → E →L[ℂ] E) (hmono : Monotone A) (hpos : ∀ i, 0 ≤ A i)
    (C : E →L[ℂ] E) (hbound : ∀ i, A i ≤ C) (x : E) :
    Cauchy (Filter.map (fun i => A i x) atTop) := by
  let q : ι → ℝ := fun i => (inner ℂ x (A i x)).re
  have hqmono : Monotone q := by
    intro i j hij
    have h := (ContinuousLinearMap.le_def.mp (hmono hij)).re_inner_nonneg_right x
    simpa [q, inner_sub_right, sub_nonneg] using h
  have hqb : BddAbove (Set.range q) := by
    refine ⟨(inner ℂ x (C x)).re, ?_⟩
    rintro _ ⟨i, rfl⟩
    have h := (ContinuousLinearMap.le_def.mp (hbound i)).re_inner_nonneg_right x
    simpa [q, inner_sub_right, sub_nonneg] using h
  have hqle (i : ι) : q i ≤ sSup (Set.range q) := le_csSup hqb ⟨i, rfl⟩
  apply Metric.cauchy_iff.mpr
  refine ⟨inferInstance, ?_⟩
  intro ε hε
  let K : ℝ := ‖C‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hεhalf : 0 < ε / 2 := half_pos hε
  have hδ : 0 < (ε / 2) ^ 2 / K := by positivity
  obtain ⟨_, ⟨N, rfl⟩, hN⟩ := exists_lt_of_lt_csSup (Set.range_nonempty q)
    (show sSup (Set.range q) - (ε / 2) ^ 2 / K < sSup (Set.range q) by linarith)
  have hnear (i : ι) (hi : N ≤ i) : dist (A i x) (A N x) < ε / 2 := by
    have hD : 0 ≤ A i - A N := sub_nonneg.mpr (hmono hi)
    have hDC : A i - A N ≤ C := (sub_le_self _ (hpos N)).trans (hbound i)
    have hDn : ‖A i - A N‖ ≤ ‖C‖ :=
      CStarAlgebra.norm_le_norm_of_le_of_nonneg hDC hD
    have hq : 0 ≤ q i - q N := sub_nonneg.mpr (hqmono hi)
    have hsmall : q i - q N < (ε / 2) ^ 2 / K := by linarith [hqle i]
    have he : (inner ℂ x ((A i - A N) x)).re = q i - q N := by
      simp [q]
    have hsq : ‖(A i - A N) x‖ ^ 2 < (ε / 2) ^ 2 := calc
      _ ≤ ‖A i - A N‖ * (q i - q N) := by
        simpa only [he] using norm_apply_sq_le_norm_mul_inner hD x
      _ ≤ ‖C‖ * (q i - q N) := mul_le_mul_of_nonneg_right hDn hq
      _ ≤ K * (q i - q N) := by dsimp [K]; nlinarith
      _ < (ε / 2) ^ 2 := by
        have hh := mul_lt_mul_of_pos_left hsmall hK
        rwa [mul_div_cancel₀ _ hK.ne'] at hh
    have hn : ‖(A i - A N) x‖ < ε / 2 :=
      (sq_lt_sq₀ (norm_nonneg _) hεhalf.le).mp hsq
    simpa only [dist_eq_norm, sub_apply] using hn
  refine ⟨(fun i => A i x) '' Set.Ici N, ?_, ?_⟩
  · apply Filter.mem_map.mpr
    exact Filter.eventually_atTop.mpr ⟨N, fun i hi => ⟨i, hi, rfl⟩⟩
  · rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    have hj' : dist (A N x) (A j x) < ε / 2 := by
      rw [dist_comm]
      exact hnear j hj
    calc
      dist (A i x) (A j x) ≤ dist (A i x) (A N x) + dist (A N x) (A j x) :=
        dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hnear i hi) hj'
      _ = ε := add_halves ε

/-- The actual strong limit is the supremum in the full operator order. -/
theorem exists_strongLimit_of_monotone_nonneg_bounded
    (A : ι → E →L[ℂ] E) (hmono : Monotone A) (hpos : ∀ i, 0 ≤ A i)
    (C : E →L[ℂ] E) (hbound : ∀ i, A i ≤ C) :
    ∃ B : E →L[ℂ] E, (∀ x, Tendsto (fun i => A i x) atTop (𝓝 (B x))) ∧
      0 ≤ B ∧ IsLUB (Set.range A) B := by
  classical
  have hex (x : E) : ∃ y, Tendsto (fun i => A i x) atTop (𝓝 y) :=
    cauchy_map_iff_exists_tendsto.mp
      (cauchy_map_apply_of_monotone_nonneg_bounded A hmono hpos C hbound x)
  let f : E → E := fun x => Classical.choose (hex x)
  have hf (x : E) : Tendsto (fun i => A i x) atTop (𝓝 (f x)) :=
    Classical.choose_spec (hex x)
  let L : E →ₗ[ℂ] E :=
    { toFun := f
      map_add' := fun x y => tendsto_nhds_unique (hf (x + y))
        (by simpa using (hf x).add (hf y))
      map_smul' := fun c x => tendsto_nhds_unique (hf (c • x))
        (by simpa using (hf x).const_smul c) }
  have hb (x : E) : ‖L x‖ ≤ ‖C‖ * ‖x‖ := by
    apply le_of_tendsto (hf x).norm
    exact Filter.Eventually.of_forall fun i => (A i).le_opNorm x |>.trans
      (mul_le_mul_of_nonneg_right
        (CStarAlgebra.norm_le_norm_of_le_of_nonneg (hbound i) (hpos i))
        (norm_nonneg x))
  let B : E →L[ℂ] E := L.mkContinuous ‖C‖ hb
  have hB (x : E) : Tendsto (fun i => A i x) atTop (𝓝 (B x)) := hf x
  refine ⟨B, hB, ?_, ?_⟩
  · exact operator_le_of_strong_tendsto (fun _ => tendsto_const_nhds) hB
      (Filter.Eventually.of_forall hpos)
  · constructor
    · rintro _ ⟨i, rfl⟩
      exact operator_le_of_strong_tendsto (fun _ => tendsto_const_nhds) hB
        (Filter.eventually_atTop.mpr ⟨i, fun j hij => hmono hij⟩)
    · intro D hD
      exact operator_le_of_strong_tendsto hB (fun _ => tendsto_const_nhds)
        (Filter.Eventually.of_forall fun i => hD ⟨i, rfl⟩)

end VacuumBellSeparation.Gaussian
