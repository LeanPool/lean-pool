/-
Copyright (c) 2026 Joseph K. Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph K. Miller
-/
module

public import LeanPool.Vlasov.OT.LocalWellPosedness
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Continuation of local Vlasov solutions

Boundary gluing and iteration extend a local Lagrangian solution to any finite
horizon. Stability and the global theorem use this continuation independently.
-/

@[expose] public section

namespace Vlasov

open MeasureTheory ENNReal

/-! ## Banked infrastructure: localized `hasDerivAt_of_hasDerivAt_of_ne` -/
-- Generic real-analysis helper banked for `vlasovWellPosedness_glue` case (a)'s substantive
-- close.  Mathlib's `hasDerivAt_of_hasDerivAt_of_ne`
-- (Mathlib/Analysis/Calculus/FDeriv/Extend.lean) requires a UNIVERSAL
-- `∀ y ≠ x, HasDerivAt f (g y) y` hypothesis; the `vlasovWellPosedness_glue` setting only
-- gives HasDerivAt on a bounded interval `Ioo 0 (T + T_0)`.  This helper
-- localizes the Mathlib pattern to a neighborhood-eventually hypothesis,
-- enabling case (a)'s close via union of one-sided extension lemmas.

section HasDerivAtPunctured
open scoped Topology
open Filter

/-- Local version of `hasDerivAt_of_hasDerivAt_of_ne` (Mathlib/Analysis/Calculus/
FDeriv/Extend.lean): if `f : ℝ → ℝ` has HasDerivAt with derivative `g(y)` at
every `y ≠ x₀` in some neighborhood of `x₀`, and both `f` and `g` are continuous
at `x₀`, then `f` has HasDerivAt with derivative `g(x₀)` at `x₀`.

The proof composes `hasDerivWithinAt_Iic_of_tendsto_deriv` (left side) +
`hasDerivWithinAt_Ici_of_tendsto_deriv` (right side) + `HasDerivWithinAt.union`,
following the Mathlib lemma's proof structure but with locally-quantified
hypothesis (enabling use when the punctured-HasDerivAt holds only on a bounded
interval, not all of ℝ). -/
theorem hasDerivAt_of_hasDerivAt_of_ne_in_nhds
    {f g : ℝ → ℝ} {x₀ : ℝ}
    (h_diff_ne : ∀ᶠ y in 𝓝 x₀, y ≠ x₀ → HasDerivAt f (g y) y)
    (hf : ContinuousAt f x₀) (hg : ContinuousAt g x₀) :
    HasDerivAt f (g x₀) x₀ := by
  -- Extract an open ball around x₀ on which the punctured HasDerivAt holds.
  obtain ⟨U, hU_sub, hU_open, hx₀_U⟩ := mem_nhds_iff.mp h_diff_ne
  obtain ⟨ε, ε_pos, hε⟩ := Metric.isOpen_iff.mp hU_open x₀ hx₀_U
  -- Right side: HasDerivWithinAt on Ici x₀ via hasDerivWithinAt_Ici_of_tendsto_deriv.
  have h_right : HasDerivWithinAt f (g x₀) (Set.Ici x₀) x₀ := by
    have hs_right : Set.Ioo x₀ (x₀ + ε) ∈ 𝓝[>] x₀ :=
      Ioo_mem_nhdsGT (by linarith : x₀ < x₀ + ε)
    have h_diff_right : DifferentiableOn ℝ f (Set.Ioo x₀ (x₀ + ε)) := by
      intro y hy
      have hy_U : y ∈ U := hε (by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        exact ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩)
      exact (hU_sub hy_U (ne_of_gt hy.1)).differentiableAt.differentiableWithinAt
    apply hasDerivWithinAt_Ici_of_tendsto_deriv h_diff_right hf.continuousWithinAt hs_right
    have h_g_tendsto : Tendsto g (𝓝[>] x₀) (𝓝 (g x₀)) := tendsto_inf_left hg
    apply h_g_tendsto.congr'
    apply mem_of_superset hs_right
    intro y hy
    have hy_U : y ∈ U := hε (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩)
    exact (hU_sub hy_U (ne_of_gt hy.1)).deriv.symm
  -- Left side: symmetric.
  have h_left : HasDerivWithinAt f (g x₀) (Set.Iic x₀) x₀ := by
    have hs_left : Set.Ioo (x₀ - ε) x₀ ∈ 𝓝[<] x₀ :=
      Ioo_mem_nhdsLT (by linarith : x₀ - ε < x₀)
    have h_diff_left : DifferentiableOn ℝ f (Set.Ioo (x₀ - ε) x₀) := by
      intro y hy
      have hy_U : y ∈ U := hε (by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        exact ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩)
      exact (hU_sub hy_U (ne_of_lt hy.2)).differentiableAt.differentiableWithinAt
    apply hasDerivWithinAt_Iic_of_tendsto_deriv h_diff_left hf.continuousWithinAt hs_left
    have h_g_tendsto : Tendsto g (𝓝[<] x₀) (𝓝 (g x₀)) := tendsto_inf_left hg
    apply h_g_tendsto.congr'
    apply mem_of_superset hs_left
    intro y hy
    have hy_U : y ∈ U := hε (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩)
    exact (hU_sub hy_U (ne_of_lt hy.2)).deriv.symm
  -- Union via Set.Iic_union_Ici = Set.univ → HasDerivAt at x₀.
  simpa using h_left.union h_right

end HasDerivAtPunctured

/-! ## Variable-`T_target` continuation via fixed-`T_0` iteration -/
-- Composes `vlasovWellPosedness_local` against itself to extend the local
-- solution from `[0, T_0]` to `[0, T_target]` for any `T_target > 0`.  The
-- contraction time `T_0` is *fixed* (depends only on `L`, not on iteration-
-- accumulated moment bounds) — see the docstring on `vlasovWellPosedness_local`
-- (above) for why fixed-`T_0` is the correct iteration shape (the
-- `Phi_supW1_contraction` factor `q` depends only on `L` and `T`).
--
-- Two sub-theorems:
-- * `vlasovWellPosedness_glue`: extend a solution on `[0, T]` by one
--   window of length `T_0`, gluing at `t = T`.
-- * `vlasovWellPosedness_forward`: `Nat.rec` iteration of `vlasovWellPosedness_glue`
--   to reach any `T_target`.
--
-- The universal-in-`t` bridge (below) then goes from
-- `IsLagrangianVlasovSolutionOn` (any `T_target`) to
-- `IsLagrangianVlasovSolution` (universal-in-`t`), and uniqueness follows.

/-- The `t = T` seam of the glue: both one-sided derivatives of the spliced
flow at the junction agree (`g`'s flow starts at the identity on
`f_prev T`'s data), so `HasDerivWithinAt.union` on `Iic T ∪ Ici T = univ`
gives the two-sided derivative, restricted back to `Icc 0 (T + T_0)`. -/
private lemma vlasovWellPosedness_glue_boundary_seam {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    {T T_0 : ℝ} (hT_pos : 0 < T) (hT_0_pos : 0 < T_0)
    (f_prev g f_next : ℝ → Measure (PhaseSpace d))
    (charX_prev charV_prev charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    (hdef_f : f_next = fun t => if t ≤ T then f_prev t else g (t - T))
    (h_prev_boundary : ∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
        HasDerivWithinAt (fun s => charX_prev s z) (charV_prev t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV_prev s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (f_prev t)) (charX_prev t z)))
          (Set.Icc 0 T) t)
    (hg_boundary : ∀ (w : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T_0 →
        HasDerivWithinAt (fun s => charX_g s w) (charV_g t w) (Set.Icc 0 T_0) t ∧
        HasDerivWithinAt (fun s => charV_g s w)
          (-(convolveFunctionMeasure gradW (spatialMarginal (g t)) (charX_g t w)))
          (Set.Icc 0 T_0) t)
    (hg_init : g 0 = f_prev T)
    (hg_init_cond : ∀ (w : PhaseSpace d), charX_g 0 w = w.1 ∧ charV_g 0 w = w.2)
    (z : PhaseSpace d) :
    HasDerivWithinAt
      (fun s => if s ≤ T then charX_prev s z
        else charX_g (s - T) (charX_prev T z, charV_prev T z))
      (charV_prev T z) (Set.Icc 0 (T + T_0)) T ∧
    HasDerivWithinAt
      (fun s => if s ≤ T then charV_prev s z
        else charV_g (s - T) (charX_prev T z, charV_prev T z))
      (-(convolveFunctionMeasure gradW (spatialMarginal (f_next T)) (charX_prev T z)))
      (Set.Icc 0 (T + T_0)) T := by
  have hT_in : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
  have h_bX := (h_prev_boundary z T hT_in).1
  have h_bV := (h_prev_boundary z T hT_in).2
  have h0_T0_in : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T_0 := ⟨le_refl 0, hT_0_pos.le⟩
  have h_g_bX := (hg_boundary (charX_prev T z, charV_prev T z) 0 h0_T0_in).1
  have h_g_bV := (hg_boundary (charX_prev T z, charV_prev T z) 0 h0_T0_in).2
  have h_nhd_L : Set.Icc 0 T ∈ nhdsWithin T (Set.Iic T) := Icc_mem_nhdsLE hT_pos
  have h_nhd_R : Set.Icc 0 T_0 ∈ nhdsWithin (0 : ℝ) (Set.Ici 0) := Icc_mem_nhdsGE hT_0_pos
  -- charX: left one-sided
  have hX_Lic := h_bX.mono_of_mem_nhdsWithin h_nhd_L
  have hX_left : HasDerivWithinAt
      (fun s => if s ≤ T then charX_prev s z
        else charX_g (s - T) (charX_prev T z, charV_prev T z))
      (charV_prev T z) (Set.Iic T) T :=
    hX_Lic.congr_of_mem (fun s hs => by simp [Set.mem_Iic.mp hs]) Set.self_mem_Iic
  -- charX: right one-sided via chain rule on g's boundary
  have hX_Ici0 := h_g_bX.mono_of_mem_nhdsWithin h_nhd_R
  have h_sub_R : HasDerivWithinAt (· - T) 1 (Set.Ici T) T :=
    ((hasDerivAt_id' T).sub_const T).hasDerivWithinAt
  have h_mapR : Set.MapsTo (· - T) (Set.Ici T) (Set.Ici 0) :=
    fun s hs => Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp hs])
  have h_chainX : HasDerivWithinAt
      (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z))
      (charV_g 0 (charX_prev T z, charV_prev T z)) (Set.Ici T) T := by
    have := HasDerivWithinAt.scomp_of_eq T hX_Ici0 h_sub_R h_mapR (sub_self T).symm
    simpa [Function.comp_def, one_smul] using this
  have hVg0_eq : charV_g 0 (charX_prev T z, charV_prev T z) = charV_prev T z :=
    (hg_init_cond (charX_prev T z, charV_prev T z)).2
  rw [hVg0_eq] at h_chainX
  have hX_right : HasDerivWithinAt
      (fun s => if s ≤ T then charX_prev s z
        else charX_g (s - T) (charX_prev T z, charV_prev T z))
      (charV_prev T z) (Set.Ici T) T :=
    h_chainX.congr_of_mem
      (fun s hs => by
        by_cases hle : s ≤ T
        · have heq : s = T := le_antisymm hle (Set.mem_Ici.mp hs)
          simp [heq, sub_self,
            (hg_init_cond (charX_prev T z, charV_prev T z)).1]
        · simp [hle])
      Set.self_mem_Ici
  have hX_union := hX_left.union hX_right
  rw [Set.Iic_union_Ici] at hX_union
  -- charV: analogously
  have hV_Lic := h_bV.mono_of_mem_nhdsWithin h_nhd_L
  have hV_left : HasDerivWithinAt
      (fun s => if s ≤ T then charV_prev s z
        else charV_g (s - T) (charX_prev T z, charV_prev T z))
      (-(convolveFunctionMeasure gradW (spatialMarginal (f_next T)) (charX_prev T z)))
      (Set.Iic T) T := by
    simp only [hdef_f, ite_eq_left (le_refl T)]
    exact hV_Lic.congr_of_mem (fun s hs => by simp [Set.mem_Iic.mp hs]) Set.self_mem_Iic
  have hV_Ici0 := h_g_bV.mono_of_mem_nhdsWithin h_nhd_R
  have h_chainV : HasDerivWithinAt
      (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z))
      (-(convolveFunctionMeasure gradW
        (spatialMarginal (g 0))
        (charX_g 0 (charX_prev T z, charV_prev T z))))
      (Set.Ici T) T := by
    have := HasDerivWithinAt.scomp_of_eq T hV_Ici0 h_sub_R h_mapR (sub_self T).symm
    simpa [Function.comp_def, one_smul] using this
  have hXg0_eq : charX_g 0 (charX_prev T z, charV_prev T z) = charX_prev T z :=
    (hg_init_cond (charX_prev T z, charV_prev T z)).1
  have hg0_spat : spatialMarginal (g 0) = spatialMarginal (f_prev T) :=
    congrArg spatialMarginal hg_init
  have hfnextT : spatialMarginal (f_next T) = spatialMarginal (f_prev T) :=
    congrArg spatialMarginal (by rw [hdef_f]; simp only [ite_eq_left (le_refl T)])
  rw [hXg0_eq, hg0_spat, ← hfnextT] at h_chainV
  have hV_right : HasDerivWithinAt
      (fun s => if s ≤ T then charV_prev s z
        else charV_g (s - T) (charX_prev T z, charV_prev T z))
      (-(convolveFunctionMeasure gradW (spatialMarginal (f_next T)) (charX_prev T z)))
      (Set.Ici T) T :=
    h_chainV.congr_of_mem
      (fun s hs => by
        by_cases hle : s ≤ T
        · have heq : s = T := le_antisymm hle (Set.mem_Ici.mp hs)
          simp [heq, sub_self,
            (hg_init_cond (charX_prev T z, charV_prev T z)).2]
        · simp [hle])
      Set.self_mem_Ici
  have hV_union := hV_left.union hV_right
  rw [Set.Iic_union_Ici] at hV_union
  exact ⟨hX_union.hasDerivAt Filter.univ_mem |>.hasDerivWithinAt,
    hV_union.hasDerivAt Filter.univ_mem |>.hasDerivWithinAt⟩

private lemma vlasovWellPosedness_glue_boundary {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    {T T_0 : ℝ} (hT_pos : 0 < T) (hT_0_pos : 0 < T_0)
    (f_prev g f_next : ℝ → Measure (PhaseSpace d))
    (charX_prev charV_prev charX_g charV_g charX_next charV_next :
        ℝ → PhaseSpace d → PhysSpace d)
    (hdef_X : charX_next = fun t z =>
        if t ≤ T then charX_prev t z else charX_g (t - T) (charX_prev T z, charV_prev T z))
    (hdef_V : charV_next = fun t z =>
        if t ≤ T then charV_prev t z else charV_g (t - T) (charX_prev T z, charV_prev T z))
    (hdef_f : f_next = fun t => if t ≤ T then f_prev t else g (t - T))
    (h_prev_boundary : ∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
        HasDerivWithinAt (fun s => charX_prev s z) (charV_prev t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV_prev s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (f_prev t)) (charX_prev t z)))
          (Set.Icc 0 T) t)
    (hg_boundary : ∀ (w : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T_0 →
        HasDerivWithinAt (fun s => charX_g s w) (charV_g t w) (Set.Icc 0 T_0) t ∧
        HasDerivWithinAt (fun s => charV_g s w)
          (-(convolveFunctionMeasure gradW (spatialMarginal (g t)) (charX_g t w)))
          (Set.Icc 0 T_0) t)
    (hg_init : g 0 = f_prev T)
    (hg_init_cond : ∀ (w : PhaseSpace d), charX_g 0 w = w.1 ∧ charV_g 0 w = w.2) :
    ∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) (T + T_0) →
      HasDerivWithinAt (fun s => charX_next s z) (charV_next t z) (Set.Icc 0 (T + T_0)) t ∧
      HasDerivWithinAt (fun s => charV_next s z)
        (-(convolveFunctionMeasure gradW (spatialMarginal (f_next t)) (charX_next t z)))
        (Set.Icc 0 (T + T_0)) t := by
  subst hdef_X hdef_V
  intro z t ht
  simp only []
  -- Abbreviate the initial phase-space point for g
  have hz₀_def : (charX_prev T z, charV_prev T z) = (charX_prev T z, charV_prev T z) := rfl
  by_cases ht_le : t ≤ T
  · -- t ≤ T: use h_prev_boundary + upgrade to Icc 0 (T + T_0)
    simp only [ite_eq_left ht_le]
    have ht_in : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1, ht_le⟩
    have h_bX := (h_prev_boundary z t ht_in).1
    have h_bV := (h_prev_boundary z t ht_in).2
    by_cases ht_eqT : t = T
    · -- t = T: the seam case, extracted as `_glue_boundary_seam`.
      rw [ht_eqT]
      exact vlasovWellPosedness_glue_boundary_seam gradW hT_pos hT_0_pos f_prev g f_next
        charX_prev charV_prev charX_g charV_g hdef_f h_prev_boundary hg_boundary
        hg_init hg_init_cond z
    · -- t < T: use mono_of_mem_nhdsWithin to extend to Icc 0 (T + T_0)
      have ht_ltT : t < T := lt_of_le_of_ne ht_le ht_eqT
      -- Get Icc 0 T ∈ nhdsWithin t (Icc 0 (T + T_0))
      have h_mem : Set.Icc (0 : ℝ) T ∈ nhdsWithin t (Set.Icc 0 (T + T_0)) := by
        rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
        · exact (nhdsWithin_mono 0 Set.Icc_subset_Ici_self) (Icc_mem_nhdsGE hT_pos)
        · exact mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds ht_pos ht_ltT)
      -- Upgrade HasDerivWithinAt from Icc 0 T to Icc 0 (T + T_0)
      have hX_big := h_bX.mono_of_mem_nhdsWithin h_mem
      have hV_big := h_bV.mono_of_mem_nhdsWithin h_mem
      -- Congr: charX_next = charX_prev on Icc 0 T (within Icc 0 (T+T_0))
      have hX_ev : (fun s => if s ≤ T then charX_prev s z
            else charX_g (s - T) (charX_prev T z, charV_prev T z))
          =ᶠ[nhdsWithin t (Set.Icc 0 (T + T_0))] (charX_prev · z) :=
        Filter.Eventually.mono h_mem (fun s hs => by simp [hs.2])
      have hV_ev : (fun s => if s ≤ T then charV_prev s z
            else charV_g (s - T) (charX_prev T z, charV_prev T z))
          =ᶠ[nhdsWithin t (Set.Icc 0 (T + T_0))] (charV_prev · z) :=
        Filter.Eventually.mono h_mem (fun s hs => by simp [hs.2])
      -- f_next t = f_prev t, so marginals match
      have hfnext : f_next t = f_prev t := by rw [hdef_f]; simp only [ite_eq_left ht_le]
      have hfnext_spat : spatialMarginal (f_next t) = spatialMarginal (f_prev t) :=
        congrArg spatialMarginal hfnext
      rw [← hfnext_spat] at hV_big
      constructor
      · exact hX_big.congr_of_eventuallyEq_of_mem hX_ev ht
      · exact hV_big.congr_of_eventuallyEq_of_mem hV_ev ht
  · -- T < t: use hg_boundary + chain rule
    push Not at ht_le
    simp only [ite_eq_right (not_le.mpr ht_le)]
    have htT_mem : t - T ∈ Set.Icc (0 : ℝ) T_0 := ⟨by linarith, by linarith [ht.2]⟩
    have h_bdry_gX := (hg_boundary (charX_prev T z, charV_prev T z) (t - T) htT_mem).1
    have h_bdry_gV := (hg_boundary (charX_prev T z, charV_prev T z) (t - T) htT_mem).2
    by_cases ht_ltTT0 : t < T + T_0
    · -- t ∈ Ioo T (T + T_0): interior case, use HasDerivAt + congr
      have htT_Ioo : t - T ∈ Set.Ioo (0 : ℝ) T_0 := ⟨by linarith, by linarith⟩
      have hX_da := h_bdry_gX.hasDerivAt (Icc_mem_nhds htT_Ioo.1 htT_Ioo.2)
      have hV_da := h_bdry_gV.hasDerivAt (Icc_mem_nhds htT_Ioo.1 htT_Ioo.2)
      have h_sub : HasDerivAt (· - T) 1 t := (hasDerivAt_id' t).sub_const T
      have h_chainX : HasDerivAt (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z))
          (charV_g (t - T) (charX_prev T z, charV_prev T z)) t := by
        have := HasDerivAt.scomp_of_eq t hX_da h_sub rfl
        simpa [Function.comp_def, one_smul] using this
      have h_chainV : HasDerivAt (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z))
          (-(convolveFunctionMeasure gradW
            (spatialMarginal (g (t - T)))
            (charX_g (t - T) (charX_prev T z, charV_prev T z)))) t := by
        have := HasDerivAt.scomp_of_eq t hV_da h_sub rfl
        simpa [Function.comp_def, one_smul] using this
      -- f_next t = g (t - T), so marginals match
      have h_fnext_t : f_next t = g (t - T) := by
        rw [hdef_f]; simp only [ite_eq_right (not_le.mpr ht_le)]
      rw [← congrArg spatialMarginal h_fnext_t] at h_chainV
      -- piecewise = charX_g (· - T) (charX_prev T z, charV_prev T z) near t (since T < t)
      have h_ev_gt : ∀ᶠ s in nhds t, T < s := eventually_gt_nhds ht_le
      have hX_ev : (fun s => if s ≤ T then charX_prev s z
            else charX_g (s - T) (charX_prev T z, charV_prev T z))
          =ᶠ[nhds t] (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z)) :=
        Filter.Eventually.mono h_ev_gt (fun s hs => by simp [not_le.mpr hs])
      have hV_ev : (fun s => if s ≤ T then charV_prev s z
            else charV_g (s - T) (charX_prev T z, charV_prev T z))
          =ᶠ[nhds t] (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z)) :=
        Filter.Eventually.mono h_ev_gt (fun s hs => by simp [not_le.mpr hs])
      exact ⟨(h_chainX.congr_of_eventuallyEq hX_ev).hasDerivWithinAt,
             (h_chainV.congr_of_eventuallyEq hV_ev).hasDerivWithinAt⟩
    · -- t = T + T_0: endpoint, use mono_of_mem_nhdsWithin + chain rule + mono
      push Not at ht_ltTT0
      have htT0 : t = T + T_0 := le_antisymm ht.2 ht_ltTT0
      rw [show t - T = T_0 from by linarith] at h_bdry_gX h_bdry_gV
      -- Upgrade to Iic T_0 via Icc_mem_nhdsLE
      have h_nhd_LE : Set.Icc 0 T_0 ∈ nhdsWithin T_0 (Set.Iic T_0) := Icc_mem_nhdsLE hT_0_pos
      have hX_Lic := h_bdry_gX.mono_of_mem_nhdsWithin h_nhd_LE
      have hV_Lic := h_bdry_gV.mono_of_mem_nhdsWithin h_nhd_LE
      -- Chain rule: (· - T) maps Iic (T + T_0) to Iic T_0
      have h_sub_LE : HasDerivWithinAt (· - T) 1 (Set.Iic (T + T_0)) (T + T_0) :=
        ((hasDerivAt_id' (T + T_0)).sub_const T).hasDerivWithinAt.mono
          (fun _ _ => Set.mem_univ _)
      have h_mapLE : Set.MapsTo (· - T) (Set.Iic (T + T_0)) (Set.Iic T_0) :=
        fun s hs => Set.mem_Iic.mpr (by linarith [Set.mem_Iic.mp hs])
      have h_chainX : HasDerivWithinAt
          (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z))
          (charV_g T_0 (charX_prev T z, charV_prev T z)) (Set.Iic (T + T_0)) (T + T_0) := by
        have := HasDerivWithinAt.scomp_of_eq (T + T_0) hX_Lic h_sub_LE h_mapLE
          (show T_0 = (T + T_0) - T by ring)
        simpa [Function.comp_def, one_smul] using this
      have h_chainV : HasDerivWithinAt
          (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z))
          (-(convolveFunctionMeasure gradW
            (spatialMarginal (g T_0))
            (charX_g T_0 (charX_prev T z, charV_prev T z))))
          (Set.Iic (T + T_0)) (T + T_0) := by
        have := HasDerivWithinAt.scomp_of_eq (T + T_0) hV_Lic h_sub_LE h_mapLE
          (show T_0 = (T + T_0) - T by ring)
        simpa [Function.comp_def, one_smul] using this
      -- Congr: near T+T_0 within Iic (T+T_0), points > T eventually
      have h_ev_gt2 : ∀ᶠ s in nhdsWithin (T + T_0) (Set.Iic (T + T_0)), T < s :=
        (eventually_gt_nhds (show T < T + T_0 by linarith)).filter_mono nhdsWithin_le_nhds
      have hX_ev2 : (fun s => if s ≤ T then charX_prev s z
            else charX_g (s - T) (charX_prev T z, charV_prev T z))
          =ᶠ[nhdsWithin (T + T_0) (Set.Iic (T + T_0))]
          (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z)) :=
        Filter.Eventually.mono h_ev_gt2 (fun s hs => by simp [not_le.mpr hs])
      have hV_ev2 : (fun s => if s ≤ T then charV_prev s z
            else charV_g (s - T) (charX_prev T z, charV_prev T z))
          =ᶠ[nhdsWithin (T + T_0) (Set.Iic (T + T_0))]
          (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z)) :=
        Filter.Eventually.mono h_ev_gt2 (fun s hs => by simp [not_le.mpr hs])
      have h_Iic_sub : Set.Icc 0 (T + T_0) ⊆ Set.Iic (T + T_0) := Set.Icc_subset_Iic_self
      have h_TT0_Iic : (T + T_0) ∈ Set.Iic (T + T_0) := Set.mem_Iic.mpr (le_refl _)
      -- f_next (T + T_0) = g T_0
      have h_fnext_TT0 : f_next (T + T_0) = g T_0 := by
        simp [hdef_f, not_le.mpr (show T < T + T_0 by linarith)]
      constructor
      · have h_cX : HasDerivWithinAt
            (fun s => if s ≤ T then charX_prev s z
              else charX_g (s - T) (charX_prev T z, charV_prev T z))
            (charV_g T_0 (charX_prev T z, charV_prev T z))
            (Set.Icc 0 (T + T_0)) (T + T_0) :=
          (h_chainX.congr_of_eventuallyEq_of_mem hX_ev2 h_TT0_Iic).mono h_Iic_sub
        rw [htT0]
        rw [show T + T_0 - T = T_0 from by ring]
        exact h_cX
      · have h_cV : HasDerivWithinAt
            (fun s => if s ≤ T then charV_prev s z
              else charV_g (s - T) (charX_prev T z, charV_prev T z))
            (-(convolveFunctionMeasure gradW
              (spatialMarginal (g T_0))
              (charX_g T_0 (charX_prev T z, charV_prev T z))))
            (Set.Icc 0 (T + T_0)) (T + T_0) :=
          (h_chainV.congr_of_eventuallyEq_of_mem hV_ev2 h_TT0_Iic).mono h_Iic_sub
        rw [htT0]
        rw [h_fnext_TT0]
        rw [show T + T_0 - T = T_0 from by ring]
        exact h_cV


/-- **Route 2 inner kernel for `glue_step` `h_cont_g`** (LEFT / `Iic T`): continuity
at the seam `T` of `s ↦ (∇W ∗ μ_s)(charX s z)`, where the window measure curve `μ` is
the flow-pushforward of `f₀`.

Proven from PROVEN tools only (no deferred OT).  The pushforward rewrite
`(∇W ∗ μ_s)(x) = ∫ z', gradW (x − charX s z') ∂f₀` (`integral_map`) turns the
moving-measure convolution into a fixed-`f₀` integral with moving integrand, closed by
dominated convergence: convergence from the flow's seam continuity `h_charX_cont`,
domination from the Gronwall growth bound `hC_T` (Piece A) against `f₀`'s finite first
moment.  This is the structural reason `h_cont_g` does NOT need the general narrow→W₁
kernel — its consumer carries a pushforward representation. -/
lemma flowConv_continuousWithinAt_Iic_seam
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (μ : ℝ → Measure (PhysSpace d))
    (h_push : ∀ s ∈ Set.Icc (0 : ℝ) T,
        μ s = Measure.map (fun z : PhaseSpace d => charX s z) f₀)
    (h_aemeas : ∀ s ∈ Set.Icc (0 : ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => charX s z) f₀)
    (h_charX_cont : ∀ z : PhaseSpace d,
        ContinuousWithinAt (fun s => charX s z) (Set.Icc (0 : ℝ) T) T)
    (C_T : ℝ) (_hC_T_nn : 0 ≤ C_T)
    (hC_T : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d, ‖charX s z‖ ≤ C_T * (‖z‖ + 1))
    (z : PhaseSpace d) :
    ContinuousWithinAt (fun s => convolveFunctionMeasure gradW (μ s) (charX s z))
      (Set.Iic T) T := by
  have h_nhd_L : Set.Icc (0 : ℝ) T ∈ nhdsWithin T (Set.Iic T) := Icc_mem_nhdsLE hT
  have hgradW_cont : Continuous gradW := hL.continuous
  have hL_nn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  -- Pushforward rewrite of the convolution, eventually in s (on the window).
  have h_eq : (fun s => convolveFunctionMeasure gradW (μ s) (charX s z))
      =ᶠ[nhdsWithin T (Set.Iic T)]
      (fun s => ∫ z', gradW (charX s z - charX s z') ∂f₀) := by
    apply Filter.Eventually.mono h_nhd_L
    intro s hs
    change ∫ y, gradW (charX s z - y) ∂(μ s)
        = ∫ z', gradW (charX s z - charX s z') ∂f₀
    rw [h_push s hs]
    exact integral_map (h_aemeas s hs)
      (hgradW_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  -- The rewritten f₀-integral is continuous at T by dominated convergence.
  have h_cont_rhs : ContinuousWithinAt
      (fun s => ∫ z', gradW (charX s z - charX s z') ∂f₀) (Set.Iic T) T := by
    apply continuousWithinAt_of_dominated
      (bound := fun z' => ‖gradW 0‖ + (L : ℝ) * (C_T * (‖z‖ + 1))
        + (L : ℝ) * (C_T * (‖z'‖ + 1)))
    · -- AEStronglyMeasurable in z', eventually in s
      apply Filter.Eventually.mono h_nhd_L
      intro s hs
      exact (hgradW_cont.measurable.comp_aemeasurable
        (aemeasurable_const.sub (h_aemeas s hs))).aestronglyMeasurable
    · -- pointwise dominator bound, eventually in s
      apply Filter.Eventually.mono h_nhd_L
      intro s hs
      apply Filter.Eventually.of_forall
      intro z'
      have h1 : ‖gradW (charX s z - charX s z')‖
          ≤ ‖gradW 0‖ + (L : ℝ) * ‖charX s z - charX s z'‖ := by
        have hd := hL.dist_le_mul (charX s z - charX s z') 0
        simp only [dist_eq_norm, sub_zero] at hd
        have htri : ‖gradW (charX s z - charX s z')‖
            ≤ ‖gradW 0‖ + ‖gradW (charX s z - charX s z') - gradW 0‖ := by
          have := norm_add_le (gradW (charX s z - charX s z') - gradW 0) (gradW 0)
          simp only [sub_add_cancel] at this; linarith
        linarith
      have h2 : ‖charX s z - charX s z'‖ ≤ ‖charX s z‖ + ‖charX s z'‖ := norm_sub_le _ _
      have h3 : ‖charX s z‖ ≤ C_T * (‖z‖ + 1) := hC_T s hs z
      have h4 : ‖charX s z'‖ ≤ C_T * (‖z'‖ + 1) := hC_T s hs z'
      nlinarith [mul_le_mul_of_nonneg_left (h2.trans (add_le_add h3 h4)) hL_nn]
    · -- integrability of the dominator
      apply Integrable.add (integrable_const _)
      exact ((hf₀_int.add (integrable_const (1 : ℝ))).const_mul C_T).const_mul (L : ℝ)
    · -- pointwise continuity in s, a.e. z'
      apply Filter.Eventually.of_forall
      intro z'
      have hcz : ContinuousWithinAt (fun s => charX s z) (Set.Iic T) T :=
        (h_charX_cont z).mono_of_mem_nhdsWithin h_nhd_L
      have hcz' : ContinuousWithinAt (fun s => charX s z') (Set.Iic T) T :=
        (h_charX_cont z').mono_of_mem_nhdsWithin h_nhd_L
      exact hgradW_cont.continuousAt.comp_continuousWithinAt (hcz.sub hcz')
  -- Bridge value at T and conclude.
  have h_val_T : convolveFunctionMeasure gradW (μ T) (charX T z)
      = ∫ z', gradW (charX T z - charX T z') ∂f₀ := by
    have hT_mem : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_refl T⟩
    change ∫ y, gradW (charX T z - y) ∂(μ T)
        = ∫ z', gradW (charX T z - charX T z') ∂f₀
    rw [h_push T hT_mem]
    exact integral_map (h_aemeas T hT_mem)
      (hgradW_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  exact h_cont_rhs.congr_of_eventuallyEq h_eq h_val_T

/-- **Route 2 inner kernel for `glue_step` `h_cont_g`** (RIGHT / `Ici a`): the
exact mirror of `flowConv_continuousWithinAt_Iic_seam`, but on `Set.Ici a` over a
generic window `[a, b]` with the seam at the lower endpoint `a`.  Same proof shape;
the only set-dependent swaps are `Iic T → Ici a`, `Icc_mem_nhdsLE → Icc_mem_nhdsGE`,
and the window `[0, T] → [a, b]`.  Used for the RIGHT side of the seam at `T` where
`charX` is the composed position flow `Z_s z = charX_g (s-T) (charX_prev T z, …)` and
`μ s = spatialMarginal (g (s-T))` is its pushforward of `f₀`. -/
lemma flowConv_continuousWithinAt_Ici_seam
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {a b : ℝ} (hab : a < b)
    (μ : ℝ → Measure (PhysSpace d))
    (h_push : ∀ s ∈ Set.Icc a b,
        μ s = Measure.map (fun z : PhaseSpace d => charX s z) f₀)
    (h_aemeas : ∀ s ∈ Set.Icc a b,
        AEMeasurable (fun z : PhaseSpace d => charX s z) f₀)
    (h_charX_cont : ∀ z : PhaseSpace d,
        ContinuousWithinAt (fun s => charX s z) (Set.Ici a) a)
    (C_T : ℝ) (_hC_T_nn : 0 ≤ C_T)
    (hC_T : ∀ s ∈ Set.Icc a b, ∀ z : PhaseSpace d, ‖charX s z‖ ≤ C_T * (‖z‖ + 1))
    (z : PhaseSpace d) :
    ContinuousWithinAt (fun s => convolveFunctionMeasure gradW (μ s) (charX s z))
      (Set.Ici a) a := by
  have h_nhd_R : Set.Icc a b ∈ nhdsWithin a (Set.Ici a) := Icc_mem_nhdsGE hab
  have hgradW_cont : Continuous gradW := hL.continuous
  have hL_nn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  -- Pushforward rewrite of the convolution, eventually in s (on the window).
  have h_eq : (fun s => convolveFunctionMeasure gradW (μ s) (charX s z))
      =ᶠ[nhdsWithin a (Set.Ici a)]
      (fun s => ∫ z', gradW (charX s z - charX s z') ∂f₀) := by
    apply Filter.Eventually.mono h_nhd_R
    intro s hs
    change ∫ y, gradW (charX s z - y) ∂(μ s)
        = ∫ z', gradW (charX s z - charX s z') ∂f₀
    rw [h_push s hs]
    exact integral_map (h_aemeas s hs)
      (hgradW_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  -- The rewritten f₀-integral is continuous at a by dominated convergence.
  have h_cont_rhs : ContinuousWithinAt
      (fun s => ∫ z', gradW (charX s z - charX s z') ∂f₀) (Set.Ici a) a := by
    apply continuousWithinAt_of_dominated
      (bound := fun z' => ‖gradW 0‖ + (L : ℝ) * (C_T * (‖z‖ + 1))
        + (L : ℝ) * (C_T * (‖z'‖ + 1)))
    · -- AEStronglyMeasurable in z', eventually in s
      apply Filter.Eventually.mono h_nhd_R
      intro s hs
      exact (hgradW_cont.measurable.comp_aemeasurable
        (aemeasurable_const.sub (h_aemeas s hs))).aestronglyMeasurable
    · -- pointwise dominator bound, eventually in s
      apply Filter.Eventually.mono h_nhd_R
      intro s hs
      apply Filter.Eventually.of_forall
      intro z'
      have h1 : ‖gradW (charX s z - charX s z')‖
          ≤ ‖gradW 0‖ + (L : ℝ) * ‖charX s z - charX s z'‖ := by
        have hd := hL.dist_le_mul (charX s z - charX s z') 0
        simp only [dist_eq_norm, sub_zero] at hd
        have htri : ‖gradW (charX s z - charX s z')‖
            ≤ ‖gradW 0‖ + ‖gradW (charX s z - charX s z') - gradW 0‖ := by
          have := norm_add_le (gradW (charX s z - charX s z') - gradW 0) (gradW 0)
          simp only [sub_add_cancel] at this; linarith
        linarith
      have h2 : ‖charX s z - charX s z'‖ ≤ ‖charX s z‖ + ‖charX s z'‖ := norm_sub_le _ _
      have h3 : ‖charX s z‖ ≤ C_T * (‖z‖ + 1) := hC_T s hs z
      have h4 : ‖charX s z'‖ ≤ C_T * (‖z'‖ + 1) := hC_T s hs z'
      nlinarith [mul_le_mul_of_nonneg_left (h2.trans (add_le_add h3 h4)) hL_nn]
    · -- integrability of the dominator
      apply Integrable.add (integrable_const _)
      exact ((hf₀_int.add (integrable_const (1 : ℝ))).const_mul C_T).const_mul (L : ℝ)
    · -- pointwise continuity in s, a.e. z'
      apply Filter.Eventually.of_forall
      intro z'
      have hcz : ContinuousWithinAt (fun s => charX s z) (Set.Ici a) a := h_charX_cont z
      have hcz' : ContinuousWithinAt (fun s => charX s z') (Set.Ici a) a := h_charX_cont z'
      exact hgradW_cont.continuousAt.comp_continuousWithinAt (hcz.sub hcz')
  -- Bridge value at a and conclude.
  have h_val_a : convolveFunctionMeasure gradW (μ a) (charX a z)
      = ∫ z', gradW (charX a z - charX a z') ∂f₀ := by
    have ha_mem : a ∈ Set.Icc a b := ⟨le_refl a, hab.le⟩
    change ∫ y, gradW (charX a z - y) ∂(μ a)
        = ∫ z', gradW (charX a z - charX a z') ∂f₀
    rw [h_push a ha_mem]
    exact integral_map (h_aemeas a ha_mem)
      (hgradW_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  exact h_cont_rhs.congr_of_eventuallyEq h_eq h_val_a

/-- gradW-kernel integrability on the spatial marginals of a finite-first-moment
curve (window-generic over the curve `μ`).  The first-moment transfer to the
marginal feeds `integrable_gradW_shift`. -/
private lemma dobrushinFlow_marginal_gradW_integrable
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (T : ℝ) (μ : ℝ → Measure (PhaseSpace d))
    (hμ_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (μ t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x_pt : PhysSpace d),
      Integrable (fun y => gradW (x_pt - y)) (spatialMarginal (μ t)) := by
  intro t ht x_pt
  have : IsProbabilityMeasure (μ t) := (hμ_mom t ht).1
  have : IsProbabilityMeasure (spatialMarginal (μ t)) :=
    (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mpr inferInstance
  have h_y_int : Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal (μ t)) := by
    unfold spatialMarginal
    rw [integrable_map_measure
      (by exact (continuous_norm.measurable).aestronglyMeasurable)
      measurable_fst.aemeasurable]
    refine Integrable.mono' (hμ_mom t ht).2
      ((continuous_norm.comp continuous_fst).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => ?_)
    change |‖z.1‖| ≤ ‖z‖
    rw [abs_of_nonneg (norm_nonneg _)]; exact norm_fst_le z
  exact integrable_gradW_shift gradW L hL (spatialMarginal (μ t)) h_y_int x_pt

/-- First-moment integrability transfers to the spatial marginal:
`∫ ‖z‖ ∂μ < ∞` gives `∫ ‖y‖ ∂(spatialMarginal μ) < ∞`. -/
private lemma vlasovGlue_marginal_norm_integrable
    {d : ℕ}
    (μ : Measure (PhaseSpace d)) (hμ : HasFiniteFirstMoment μ) :
    Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal μ) := by
  have : IsProbabilityMeasure μ := hμ.1
  unfold spatialMarginal
  rw [integrable_map_measure
    (by exact (continuous_norm.measurable).aestronglyMeasurable)
    measurable_fst.aemeasurable]
  refine Integrable.mono' hμ.2
    ((continuous_norm.comp continuous_fst).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => ?_)
  change |‖z.1‖| ≤ ‖z‖
  rw [abs_of_nonneg (norm_nonneg _)]; exact norm_fst_le z

/-- Continuity of the spatial-gradient component `gradXφ` of a smooth test
function `φ` on phase space. -/
private lemma vlasovGlue_gradXφ_continuous
    {d : ℕ}
    (φ : PhaseSpace d → ℝ) (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (gradXφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z : PhaseSpace d, gradXφ z = gradient (fun x => φ (x, z.2)) z.1) :
    Continuous gradXφ := by
  have hfderiv_X : ∀ z : PhaseSpace d,
      fderiv ℝ (fun x => φ (x, z.2)) z.1 =
      (fderiv ℝ φ z).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) :=
    fun z => by
      have h1 : HasFDerivAt φ (fderiv ℝ φ z) z :=
        (hφ_smooth.differentiable (by simp) z).hasFDerivAt
      have h2 : HasFDerivAt (fun x : PhysSpace d => (x, z.2))
          (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) z.1 :=
        hasFDerivAt_prodMk_left z.1 z.2
      exact (h1.comp z.1 h2).fderiv
  have heqX : gradXφ = fun z => gradient (fun x => φ (x, z.2)) z.1 :=
    funext hgradXφ
  rw [heqX]
  simp_rw [gradient, hfderiv_X]
  exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
    ((ContinuousLinearMap.isBoundedLinearMap_comp_right
      (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d))).continuous.comp
      (hφ_smooth.continuous_fderiv (by simp)))

/-- Continuity of the velocity-gradient component `gradVφ` of a smooth test
function `φ` on phase space. -/
private lemma vlasovGlue_gradVφ_continuous
    {d : ℕ}
    (φ : PhaseSpace d → ℝ) (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (gradVφ : PhaseSpace d → PhysSpace d)
    (hgradVφ : ∀ z : PhaseSpace d, gradVφ z = gradient (fun v => φ (z.1, v)) z.2) :
    Continuous gradVφ := by
  have hfderiv_V : ∀ z : PhaseSpace d,
      fderiv ℝ (fun v => φ (z.1, v)) z.2 =
      (fderiv ℝ φ z).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) :=
    fun z => by
      have h1 : HasFDerivAt φ (fderiv ℝ φ z) z :=
        (hφ_smooth.differentiable (by simp) z).hasFDerivAt
      have h2 : HasFDerivAt (fun v : PhysSpace d => (z.1, v))
          (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) z.2 :=
        hasFDerivAt_prodMk_right z.1 z.2
      exact (h1.comp z.2 h2).fderiv
  have heqV : gradVφ = fun z => gradient (fun v => φ (z.1, v)) z.2 :=
    funext hgradVφ
  rw [heqV]
  simp_rw [gradient, hfderiv_V]
  exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
    ((ContinuousLinearMap.isBoundedLinearMap_comp_right
      (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d))).continuous.comp
      (hφ_smooth.continuous_fderiv (by simp)))

/-- Uniform sup-bound on both gradient components of a compactly supported
smooth test function: `‖∇_x φ‖, ‖∇_v φ‖ ≤ M_φ := sup ‖fderiv φ‖`. -/
private lemma vlasovGlue_gradφ_bound
    {d : ℕ}
    (φ : PhaseSpace d → ℝ) (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z : PhaseSpace d, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z : PhaseSpace d, gradVφ z = gradient (fun v => φ (z.1, v)) z.2) :
    ∃ M_φ : ℝ, (∀ z : PhaseSpace d, ‖gradXφ z‖ ≤ M_φ) ∧
      (∀ z : PhaseSpace d, ‖gradVφ z‖ ≤ M_φ) := by
  have hfderiv_cont : Continuous (fderiv ℝ φ) :=
    hφ_smooth.continuous_fderiv (by norm_num)
  have hfderiv_compact : HasCompactSupport (fderiv ℝ φ) :=
    HasCompactSupport.fderiv (𝕜 := ℝ) hφ_compact
  obtain ⟨M_φ, hM_φ⟩ := hfderiv_cont.bounded_above_of_compact_support hfderiv_compact
  refine ⟨M_φ, fun z => ?_, fun z => ?_⟩
  · have hfd : fderiv ℝ (fun x => φ (x, z.2)) z.1 =
        (fderiv ℝ φ z).comp
          (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) := by
      have h1 : HasFDerivAt φ (fderiv ℝ φ z) z :=
        (hφ_smooth.differentiable (by simp) z).hasFDerivAt
      have h2 : HasFDerivAt (fun x : PhysSpace d => (x, z.2))
          (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) z.1 :=
        hasFDerivAt_prodMk_left z.1 z.2
      exact (h1.comp z.1 h2).fderiv
    rw [hgradXφ z, gradient, hfd,
      (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.norm_map]
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.norm_inl_le_one (𝕜 := ℝ)
        (E := PhysSpace d) (F := PhysSpace d)) (norm_nonneg _)) ?_
    rw [mul_one]; exact hM_φ z
  · have hfd : fderiv ℝ (fun v => φ (z.1, v)) z.2 =
        (fderiv ℝ φ z).comp
          (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) := by
      have h1 : HasFDerivAt φ (fderiv ℝ φ z) z :=
        (hφ_smooth.differentiable (by simp) z).hasFDerivAt
      have h2 : HasFDerivAt (fun v : PhysSpace d => (z.1, v))
          (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) z.2 :=
        hasFDerivAt_prodMk_right z.1 z.2
      exact (h1.comp z.2 h2).fderiv
    rw [hgradVφ z, gradient, hfd,
      (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.norm_map]
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.norm_inr_le_one (𝕜 := ℝ)
        (E := PhysSpace d) (F := PhysSpace d)) (norm_nonneg _)) ?_
    rw [mul_one]; exact hM_φ z

/-- Convolution force bound from a first-moment envelope:
`‖(gradW ⋆ ρ) x‖ ≤ ‖gradW 0‖ + L·‖x‖ + L·M` for a probability measure `ρ`
with `∫ ‖y‖ ∂ρ ≤ M`. -/
private lemma vlasovGlue_conv_force_bound
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : Measure (PhysSpace d)) [IsProbabilityMeasure ρ]
    (M : ℝ) (hM : ∫ y, ‖y‖ ∂ρ ≤ M)
    (h_y_int : Integrable (fun y : PhysSpace d => ‖y‖) ρ)
    (h_int : ∀ x : PhysSpace d, Integrable (fun y => gradW (x - y)) ρ)
    (x : PhysSpace d) :
    ‖convolveFunctionMeasure gradW ρ x‖
      ≤ ‖gradW 0‖ + (L : ℝ) * ‖x‖ + (L : ℝ) * M := by
  unfold convolveFunctionMeasure
  have h_sub_int : Integrable (fun y => ‖x - y‖) ρ :=
    Integrable.mono' ((integrable_const ‖x‖).add h_y_int)
      ((aestronglyMeasurable_const (b := x)).sub aestronglyMeasurable_id |>.norm)
      (Filter.Eventually.of_forall fun y => by
        simp only [Real.norm_of_nonneg (norm_nonneg _)]; exact norm_sub_le x y)
  have h_pt : ∀ y : PhysSpace d,
      ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + (L : ℝ) * ‖x - y‖ := by
    intro y
    have hd := hL.dist_le_mul (x - y) 0
    simp only [dist_eq_norm, sub_zero] at hd
    have h_tri : ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x - y) - gradW 0‖ := by
      have := norm_add_le (gradW (x - y) - gradW 0) (gradW 0)
      simp only [sub_add_cancel] at this; linarith
    linarith
  have h_bnd_int :
      Integrable (fun y => ‖gradW 0‖ + (L : ℝ) * ‖x - y‖) ρ :=
    (integrable_const _).add (h_sub_int.const_mul _)
  calc ‖∫ y, gradW (x - y) ∂ρ‖
      ≤ ∫ y, ‖gradW (x - y)‖ ∂ρ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y, (‖gradW 0‖ + (L : ℝ) * ‖x - y‖) ∂ρ :=
        integral_mono (h_int x).norm h_bnd_int h_pt
    _ = ‖gradW 0‖ + (L : ℝ) * ∫ y, ‖x - y‖ ∂ρ := by
        rw [integral_add (integrable_const _) (h_sub_int.const_mul _)]
        simp [integral_const, measureReal_def, measure_univ, integral_const_mul]
    _ ≤ ‖gradW 0‖ + (L : ℝ) * ‖x‖ + (L : ℝ) * M := by
        have h_int_le : ∫ y, ‖x - y‖ ∂ρ ≤ ‖x‖ + M := by
          calc ∫ y, ‖x - y‖ ∂ρ
              ≤ ∫ y, (‖x‖ + ‖y‖) ∂ρ :=
                integral_mono h_sub_int ((integrable_const _).add h_y_int)
                  (fun y => norm_sub_le x y)
            _ = ‖x‖ + ∫ y, ‖y‖ ∂ρ := by
                rw [integral_add (integrable_const _) h_y_int]
                simp [integral_const, measureReal_def, measure_univ]
            _ ≤ ‖x‖ + M := by linarith
        nlinarith [mul_le_mul_of_nonneg_left h_int_le L.coe_nonneg]

/-- Window growth bound for a characteristic flow given boundary regularity:
clamps the marginal curve into `[0, T]` (for the universal probability
instance), derives the interior `IsCharacteristicFlowOn` from the boundary
bundle, and applies `characteristicFlow_boundary_regularity` +
`flow_distance_growth_bound_on`.  Returns the linear growth constant `C`
together with per-`z` window continuity of the joint flow curve. -/
private lemma vlasovGlue_flow_growthBound
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (μ : ℝ → Measure (PhaseSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT_pos : 0 < T)
    (hμ_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (μ t))
    (hM : ∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (μ t)) ≤ M)
    (h_ic : ∀ z : PhaseSpace d, charX 0 z = z.1 ∧ charV 0 z = z.2)
    (h_boundary : ∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
        HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (μ t)) (charX t z)))
          (Set.Icc 0 T) t) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
        ‖(charX s z, charV s z)‖ ≤ C * (‖z‖ + 1)) ∧
      (∀ z : PhaseSpace d,
        ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T)) := by
  obtain ⟨M, hM_nn, hM_bd⟩ := hM
  set clampT : ℝ → ℝ := fun t => max 0 (min t T) with hclampT_def
  have hclampT_mem : ∀ t, clampT t ∈ Set.Icc (0 : ℝ) T := by
    intro t
    simp only [hclampT_def, Set.mem_Icc]
    exact ⟨le_max_left _ _, max_le hT_pos.le (min_le_right _ _)⟩
  have hclampT_id : ∀ t ∈ Set.Icc (0 : ℝ) T, clampT t = t := by
    intro t ht
    simp only [hclampT_def, min_eq_left ht.2, max_eq_right ht.1]
  set ρc : ℝ → Measure (PhysSpace d) :=
    fun t => spatialMarginal (μ (clampT t)) with hρc_def
  have hρc_isProb : ∀ t, IsProbabilityMeasure (ρc t) := by
    intro t
    have : IsProbabilityMeasure (μ (clampT t)) :=
      (hμ_mom (clampT t) (hclampT_mem t)).1
    exact (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mpr inferInstance
  have hM_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(ρc t) ≤ M := by
    intro t _ht
    rw [hρc_def]
    exact hM_bd (clampT t) (hclampT_mem t)
  have h_y_int_ρc : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖) (ρc t) := by
    intro t ht
    have h_eq : ρc t = spatialMarginal (μ t) := by
      simp only [hρc_def, hclampT_id t ht]
    rw [h_eq]
    exact vlasovGlue_marginal_norm_integrable (μ t) (hμ_mom t ht)
  have h_int_ρc : ∀ t (x : PhysSpace d),
      Integrable (fun y => gradW (x - y)) (ρc t) :=
    fun t x => by
      have := dobrushinFlow_marginal_gradW_integrable gradW L hL T μ hμ_mom
        (clampT t) (hclampT_mem t) x
      simpa only [hρc_def] using this
  have h_bdry_ρc : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
      HasDerivWithinAt (fun s => charV s z)
        (-(convolveFunctionMeasure gradW (ρc t) (charX t z)))
        (Set.Icc 0 T) t := by
    intro z t ht
    have h_eq : ρc t = spatialMarginal (μ t) := by
      simp only [hρc_def, hclampT_id t ht]
    rw [h_eq]
    exact h_boundary z t ht
  have h_flow_ρc : IsCharacteristicFlowOn gradW ρc charX charV
      (Set.Ioo 0 T) Set.univ := by
    refine ⟨fun z _ => h_ic z, fun t ht z _ => ?_, fun t ht z _ => ?_⟩
    · have ht_Icc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
      exact ((h_bdry_ρc z t ht_Icc).1).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    · have ht_Icc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
      exact ((h_bdry_ρc z t ht_Icc).2).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  obtain ⟨h_init_ρc, h_cont_Icc_ρc, h_deriv_Ico_ρc⟩ :=
    characteristicFlow_boundary_regularity gradW ρc charX charV T hT_pos.le
      h_flow_ρc h_bdry_ρc
  obtain ⟨C, hC_nn, hC_pair⟩ :=
    flow_distance_growth_bound_on gradW L hL ρc charX charV T hT_pos.le
      h_init_ρc h_cont_Icc_ρc h_deriv_Ico_ρc M hM_nn hM_ρ h_y_int_ρc h_int_ρc
  exact ⟨C, hC_nn, hC_pair, h_cont_Icc_ρc⟩

/-- Generic seam continuity of the force-integral functional
`s ↦ ∫ ⟪V s z, ∇ₓφ(Φ s z)⟫ − ⟪(gradW ⋆ ρ s)(X s z), ∇ᵥφ(Φ s z)⟫ ∂f₀`
at a window endpoint, by dominated convergence.  `S` is the one-sided
neighborhood filter set (`Iic T` or `Ici T`), `W` the compact window
(`Icc 0 T` or `Icc T (T+T₀)`) carrying the uniform data: a linear growth
bound `C` on the flow, a moment envelope `M` on the marginal curve `ρ`, and
kernel integrability.  Instantiated on the LEFT by `f_prev`'s window flow and
on the RIGHT by the composed flow off `g`. -/
private lemma vlasovGlue_seam_forceIntegral_cont
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ_cont : Continuous gradXφ) (hgradVφ_cont : Continuous gradVφ)
    (M_φ : ℝ)
    (hgradXφ_bd : ∀ z : PhaseSpace d, ‖gradXφ z‖ ≤ M_φ)
    (hgradVφ_bd : ∀ z : PhaseSpace d, ‖gradVφ z‖ ≤ M_φ)
    (ρ : ℝ → Measure (PhysSpace d))
    (X V : ℝ → PhaseSpace d → PhysSpace d)
    (T₀ : ℝ) (S : Set ℝ) (W : Set ℝ)
    (hW_nhd : W ∈ nhdsWithin T₀ S)
    (hρ_prob : ∀ s ∈ W, IsProbabilityMeasure (ρ s))
    (M : ℝ) (hM : ∀ s ∈ W, ∫ y, ‖y‖ ∂(ρ s) ≤ M)
    (h_y_int : ∀ s ∈ W, Integrable (fun y : PhysSpace d => ‖y‖) (ρ s))
    (h_int : ∀ s ∈ W, ∀ x : PhysSpace d, Integrable (fun y => gradW (x - y)) (ρ s))
    (C : ℝ)
    (hC_pair : ∀ s ∈ W, ∀ z : PhaseSpace d, ‖(X s z, V s z)‖ ≤ C * (‖z‖ + 1))
    (h_aemeas : ∀ s ∈ W, AEMeasurable (fun z : PhaseSpace d => (X s z, V s z)) f₀)
    (h_X_cont : ∀ z : PhaseSpace d, ContinuousWithinAt (fun s => X s z) S T₀)
    (h_V_cont : ∀ z : PhaseSpace d, ContinuousWithinAt (fun s => V s z) S T₀)
    (h_conv_cwn : ∀ z : PhaseSpace d, ContinuousWithinAt
        (fun s => convolveFunctionMeasure gradW (ρ s) (X s z)) S T₀) :
    ContinuousWithinAt
      (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ (V s z) (gradXφ (X s z, V s z)) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (ρ s) (X s z))
            (gradVφ (X s z, V s z))) ∂f₀) S T₀ := by
  set bound_fn : PhaseSpace d → ℝ := fun z =>
    M_φ * (C * (‖z‖ + 1))
    + (‖gradW 0‖ + (L : ℝ) * (C * (‖z‖ + 1)) + (L : ℝ) * M) * M_φ
    with hbound_def
  have hbound_int : Integrable bound_fn f₀ := by
    have ha : Integrable
        (fun z : PhaseSpace d =>
          (M_φ * C + L * M_φ * C) * ‖z‖
          + (M_φ * C + (‖gradW 0‖ + L * C + L * M) * M_φ)) f₀ :=
      (hf₀_int.const_mul _).add (integrable_const _)
    refine ha.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [hbound_def]; ring
  have h_conv_force : ∀ s ∈ W, ∀ x : PhysSpace d,
      ‖convolveFunctionMeasure gradW (ρ s) x‖
        ≤ ‖gradW 0‖ + (L : ℝ) * ‖x‖ + (L : ℝ) * M := by
    intro s hs x
    have := hρ_prob s hs
    exact vlasovGlue_conv_force_bound gradW L hL (ρ s) M (hM s hs)
      (h_y_int s hs) (h_int s hs) x
  have hB : ∀ s ∈ W, ∀ z : PhaseSpace d,
      ‖@inner ℝ (PhysSpace d) _ (V s z) (gradXφ (X s z, V s z)) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (ρ s) (X s z))
            (gradVφ (X s z, V s z))‖ ≤ bound_fn z := by
    intro s hs z
    have hV : ‖V s z‖ ≤ C * (‖z‖ + 1) :=
      le_trans (norm_snd_le (X s z, V s z)) (hC_pair s hs z)
    have hX : ‖X s z‖ ≤ C * (‖z‖ + 1) :=
      le_trans (norm_fst_le (X s z, V s z)) (hC_pair s hs z)
    have ht1 : ‖@inner ℝ (PhysSpace d) _ (V s z) (gradXφ (X s z, V s z))‖
        ≤ M_φ * (C * (‖z‖ + 1)) := by
      refine le_trans (norm_inner_le_norm _ _) ?_
      have := mul_le_mul hV (hgradXφ_bd (X s z, V s z))
        (norm_nonneg _) (le_trans (norm_nonneg _) hV)
      calc ‖V s z‖ * ‖gradXφ (X s z, V s z)‖
          ≤ (C * (‖z‖ + 1)) * M_φ := this
        _ = M_φ * (C * (‖z‖ + 1)) := by ring
    have ht2 : ‖@inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ s) (X s z))
          (gradVφ (X s z, V s z))‖
        ≤ (‖gradW 0‖ + (L : ℝ) * (C * (‖z‖ + 1)) + (L : ℝ) * M) * M_φ := by
      refine le_trans (norm_inner_le_norm _ _) ?_
      have hc : ‖convolveFunctionMeasure gradW (ρ s) (X s z)‖
          ≤ ‖gradW 0‖ + (L : ℝ) * (C * (‖z‖ + 1)) + (L : ℝ) * M := by
        refine le_trans (h_conv_force s hs (X s z)) ?_
        have := mul_le_mul_of_nonneg_left hX L.coe_nonneg
        linarith
      have hcnn : 0 ≤ ‖gradW 0‖ + (L : ℝ) * (C * (‖z‖ + 1)) + (L : ℝ) * M :=
        le_trans (norm_nonneg _) hc
      exact mul_le_mul hc (hgradVφ_bd (X s z, V s z)) (norm_nonneg _) hcnn
    calc ‖_ - _‖
        ≤ ‖@inner ℝ (PhysSpace d) _ (V s z) (gradXφ (X s z, V s z))‖
          + ‖@inner ℝ (PhysSpace d) _
              (convolveFunctionMeasure gradW (ρ s) (X s z))
              (gradVφ (X s z, V s z))‖ := norm_sub_le _ _
      _ ≤ bound_fn z := by simp only [hbound_def]; linarith
  apply continuousWithinAt_of_dominated (bound := bound_fn)
  · -- AEStronglyMeasurable in z, eventually in s
    apply Filter.Eventually.mono hW_nhd
    intro s hs
    have h_aem_pair := h_aemeas s hs
    have h_aem_X : AEMeasurable (fun z : PhaseSpace d => X s z) f₀ :=
      measurable_fst.comp_aemeasurable h_aem_pair
    have h_aem_V : AEMeasurable (fun z : PhaseSpace d => V s z) f₀ :=
      measurable_snd.comp_aemeasurable h_aem_pair
    have h1 : AEStronglyMeasurable
        (fun z : PhaseSpace d => @inner ℝ (PhysSpace d) _ (V s z)
          (gradXφ (X s z, V s z))) f₀ := by
      have hg : AEMeasurable (fun z : PhaseSpace d => gradXφ (X s z, V s z)) f₀ :=
        hgradXφ_cont.measurable.comp_aemeasurable (h_aem_X.prodMk h_aem_V)
      exact (continuous_inner.measurable.comp_aemeasurable
        (h_aem_V.prodMk hg)).aestronglyMeasurable
    have h2 : AEStronglyMeasurable
        (fun z : PhaseSpace d => @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ s) (X s z))
          (gradVφ (X s z, V s z))) f₀ := by
      have hconv_aem : AEMeasurable
          (fun z : PhaseSpace d => convolveFunctionMeasure gradW (ρ s) (X s z)) f₀ := by
        have hconv_cont' : Continuous (fun x : PhysSpace d =>
            convolveFunctionMeasure gradW (ρ s) x) := by
          have := hρ_prob s hs
          exact (convolveFunctionMeasure_lipschitz_in_x gradW L hL
            (ρ s) (h_int s hs)).continuous
        exact hconv_cont'.measurable.comp_aemeasurable h_aem_X
      have hg : AEMeasurable (fun z : PhaseSpace d => gradVφ (X s z, V s z)) f₀ :=
        hgradVφ_cont.measurable.comp_aemeasurable (h_aem_X.prodMk h_aem_V)
      exact (continuous_inner.measurable.comp_aemeasurable
        (hconv_aem.prodMk hg)).aestronglyMeasurable
    exact h1.sub h2
  · -- dominator bound, eventually in s
    apply Filter.Eventually.mono hW_nhd
    intro s hs
    exact Filter.Eventually.of_forall fun z => hB s hs z
  · exact hbound_int
  · -- pointwise continuity in s, for every z
    apply Filter.Eventually.of_forall
    intro z
    have h_pair_cwn : ContinuousWithinAt (fun s => (X s z, V s z)) S T₀ :=
      (h_X_cont z).prodMk (h_V_cont z)
    have h_gX_cwn : ContinuousWithinAt
        (fun s => gradXφ (X s z, V s z)) S T₀ :=
      hgradXφ_cont.continuousAt.comp_continuousWithinAt h_pair_cwn
    have h_gV_cwn : ContinuousWithinAt
        (fun s => gradVφ (X s z, V s z)) S T₀ :=
      hgradVφ_cont.continuousAt.comp_continuousWithinAt h_pair_cwn
    have h_term1 : ContinuousWithinAt
        (fun s => @inner ℝ (PhysSpace d) _ (V s z)
          (gradXφ (X s z, V s z))) S T₀ :=
      (h_V_cont z).inner h_gX_cwn
    have h_term2 : ContinuousWithinAt
        (fun s => @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ s) (X s z))
          (gradVφ (X s z, V s z))) S T₀ :=
      (h_conv_cwn z).inner h_gV_cwn
    exact h_term1.sub h_term2

/-- LEFT seam continuity of the force-integral functional at `T`: on `Iic T`
the glued solution agrees with `f_prev` (via `hf_next_le`), whose window
pushforward representation reduces the claim to the generic seam DCT lemma
`vlasovGlue_seam_forceIntegral_cont` on `f_prev`'s window flow. -/
private lemma vlasovGlue_seam_contLeft
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT_pos : 0 < T)
    (f_prev : ℝ → Measure (PhaseSpace d))
    (h_prev_init : f_prev 0 = f₀)
    (h_prev_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f_prev t))
    (hM_prev : ∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f_prev t)) ≤ M)
    (charX_prev charV_prev : ℝ → PhaseSpace d → PhysSpace d)
    (h_prev_push : ∀ t ∈ Set.Icc (0 : ℝ) T,
        f_prev t =
          Measure.map (fun z : PhaseSpace d => (charX_prev t z, charV_prev t z)) (f_prev 0))
    (h_prev_aemeas : ∀ s ∈ Set.Icc (0 : ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) (f_prev 0))
    (h_prev_boundary : ∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
        HasDerivWithinAt (fun s => charX_prev s z) (charV_prev t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV_prev s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (f_prev t)) (charX_prev t z)))
          (Set.Icc 0 T) t)
    (h_prev_ic : ∀ z : PhaseSpace d, charX_prev 0 z = z.1 ∧ charV_prev 0 z = z.2)
    (f_next : ℝ → Measure (PhaseSpace d))
    (hf_next_le : ∀ s, s ≤ T → f_next s = f_prev s)
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z : PhaseSpace d, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z : PhaseSpace d, gradVφ z = gradient (fun v => φ (z.1, v)) z.2) :
    ContinuousWithinAt
      (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
              @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW (spatialMarginal (f_next s)) z.1)
                (gradVφ z)) ∂(f_next s)) (Set.Iic T) T := by
  have h_nhd_L : Set.Icc (0 : ℝ) T ∈ nhdsWithin T (Set.Iic T) :=
    Icc_mem_nhdsLE hT_pos
  have hgradXφ_cont : Continuous gradXφ :=
    vlasovGlue_gradXφ_continuous φ hφ_smooth gradXφ hgradXφ
  have hgradVφ_cont : Continuous gradVφ :=
    vlasovGlue_gradVφ_continuous φ hφ_smooth gradVφ hgradVφ
  have h_int_marg := dobrushinFlow_marginal_gradW_integrable gradW L hL T
    f_prev h_prev_mom
  have h_push_marg : ∀ s ∈ Set.Icc (0 : ℝ) T,
      spatialMarginal (f_prev s)
        = Measure.map (fun z : PhaseSpace d => charX_prev s z) f₀ := by
    intro s hs
    have h_pair_aem : AEMeasurable
        (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) f₀ :=
      h_prev_init ▸ h_prev_aemeas s hs
    unfold spatialMarginal
    rw [h_prev_push s hs, h_prev_init,
        AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable h_pair_aem]
    rfl
  have h_aemeas_marg : ∀ s ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => charX_prev s z) f₀ := by
    intro s hs
    have h_pair_aem : AEMeasurable
        (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) f₀ :=
      h_prev_init ▸ h_prev_aemeas s hs
    exact measurable_fst.comp_aemeasurable h_pair_aem
  obtain ⟨M_ρ, hM_ρ_nn, hM_ρ⟩ := hM_prev
  have h_y_int_marg : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal (f_prev t)) :=
    fun t ht => vlasovGlue_marginal_norm_integrable (f_prev t) (h_prev_mom t ht)
  obtain ⟨C_T, hC_T_nn, hC_T_pair, h_cont_Icc_prev⟩ :=
    vlasovGlue_flow_growthBound gradW L hL f_prev charX_prev charV_prev
      T hT_pos h_prev_mom ⟨M_ρ, hM_ρ_nn, hM_ρ⟩ h_prev_ic h_prev_boundary
  have hC_T : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖charX_prev s z‖ ≤ C_T * (‖z‖ + 1) := by
    intro s hs z
    exact le_trans (norm_fst_le (charX_prev s z, charV_prev s z))
      (hC_T_pair s hs z)
  have h_conv_z_cont : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Continuous (fun z : PhaseSpace d =>
        convolveFunctionMeasure gradW (spatialMarginal (f_prev s)) z.1) := by
    intro s hs
    have : IsProbabilityMeasure (f_prev s) := (h_prev_mom s hs).1
    have : IsProbabilityMeasure (spatialMarginal (f_prev s)) :=
      (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mpr inferInstance
    exact (convolveFunctionMeasure_lipschitz_in_x gradW L hL
      (spatialMarginal (f_prev s)) (h_int_marg s hs)).continuous.comp continuous_fst
  have h_integrand_cont : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Continuous (fun z : PhaseSpace d =>
        @inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
        @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (spatialMarginal (f_prev s)) z.1)
          (gradVφ z)) := by
    intro s hs
    exact (continuous_snd.inner hgradXφ_cont).sub
      ((h_conv_z_cont s hs).inner hgradVφ_cont)
  have h_eq_L : (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (f_next s)) z.1)
            (gradVφ z)) ∂(f_next s))
      =ᶠ[nhdsWithin T (Set.Iic T)]
      (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ (charV_prev s z)
            (gradXφ (charX_prev s z, charV_prev s z)) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (f_prev s))
              (charX_prev s z))
            (gradVφ (charX_prev s z, charV_prev s z))) ∂f₀) := by
    apply Filter.Eventually.mono h_nhd_L
    intro s hs
    have h_fnext : f_next s = f_prev s := hf_next_le s hs.2
    have h_marg : spatialMarginal (f_next s) = spatialMarginal (f_prev s) :=
      congrArg spatialMarginal h_fnext
    have h_aemeas_f₀ : AEMeasurable
        (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) f₀ :=
      h_prev_init ▸ h_prev_aemeas s hs
    change (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
            @inner ℝ (PhysSpace d) _
              (convolveFunctionMeasure gradW (spatialMarginal (f_next s)) z.1)
              (gradVφ z)) ∂(f_next s))
        = ∫ z, (@inner ℝ (PhysSpace d) _ (charV_prev s z)
              (gradXφ (charX_prev s z, charV_prev s z)) -
            @inner ℝ (PhysSpace d) _
              (convolveFunctionMeasure gradW (spatialMarginal (f_prev s))
                (charX_prev s z))
              (gradVφ (charX_prev s z, charV_prev s z))) ∂f₀
    have h_meq : f_next s
        = Measure.map
            (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) f₀ := by
      rw [h_fnext, h_prev_push s hs, h_prev_init]
    rw [h_marg, h_meq,
        integral_map h_aemeas_f₀
          (h_integrand_cont s hs).aestronglyMeasurable]
  obtain ⟨M_φ, hgradXφ_bd, hgradVφ_bd⟩ :=
    vlasovGlue_gradφ_bound φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ
  have h_X_cont : ∀ z : PhaseSpace d,
      ContinuousWithinAt (fun s => charX_prev s z) (Set.Iic T) T := fun z =>
    ((h_prev_boundary z T
        ⟨hT_pos.le, le_refl T⟩).1.continuousWithinAt).mono_of_mem_nhdsWithin h_nhd_L
  have h_V_cont : ∀ z : PhaseSpace d,
      ContinuousWithinAt (fun s => charV_prev s z) (Set.Iic T) T := fun z =>
    ((h_prev_boundary z T
        ⟨hT_pos.le, le_refl T⟩).2.continuousWithinAt).mono_of_mem_nhdsWithin h_nhd_L
  have h_conv_cwn : ∀ z : PhaseSpace d, ContinuousWithinAt
      (fun s => convolveFunctionMeasure gradW (spatialMarginal (f_prev s))
        (charX_prev s z)) (Set.Iic T) T := fun z =>
    flowConv_continuousWithinAt_Iic_seam gradW L hL charX_prev f₀
      hf₀_int hT_pos (fun s => spatialMarginal (f_prev s))
      h_push_marg h_aemeas_marg
      (fun z' => (h_cont_Icc_prev z').continuousWithinAt
        (Set.right_mem_Icc.mpr hT_pos.le) |>.fst) C_T hC_T_nn hC_T z
  have h_cont_pf : ContinuousWithinAt
      (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ (charV_prev s z)
            (gradXφ (charX_prev s z, charV_prev s z)) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (f_prev s))
              (charX_prev s z))
            (gradVφ (charX_prev s z, charV_prev s z))) ∂f₀)
      (Set.Iic T) T :=
    vlasovGlue_seam_forceIntegral_cont gradW L hL f₀ hf₀_int gradXφ gradVφ
      hgradXφ_cont hgradVφ_cont M_φ hgradXφ_bd hgradVφ_bd
      (fun s => spatialMarginal (f_prev s)) charX_prev charV_prev
      T (Set.Iic T) (Set.Icc 0 T) h_nhd_L
      (fun s hs => by
        have : IsProbabilityMeasure (f_prev s) := (h_prev_mom s hs).1
        exact (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mpr inferInstance)
      M_ρ hM_ρ h_y_int_marg h_int_marg C_T hC_T_pair
      (fun s hs => h_prev_init ▸ h_prev_aemeas s hs)
      h_X_cont h_V_cont h_conv_cwn
  have h_val_T : (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (f_next T)) z.1)
            (gradVφ z)) ∂(f_next T))
      = ∫ z, (@inner ℝ (PhysSpace d) _ (charV_prev T z)
            (gradXφ (charX_prev T z, charV_prev T z)) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (f_prev T))
              (charX_prev T z))
            (gradVφ (charX_prev T z, charV_prev T z))) ∂f₀ := by
    have hT_Icc : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
    have h_fnext_T : f_next T = f_prev T := hf_next_le T (le_refl T)
    have h_marg : spatialMarginal (f_next T) = spatialMarginal (f_prev T) :=
      congrArg spatialMarginal h_fnext_T
    have h_aemeas_f₀_T : AEMeasurable
        (fun z : PhaseSpace d => (charX_prev T z, charV_prev T z)) f₀ :=
      h_prev_init ▸ h_prev_aemeas T hT_Icc
    have h_meq : f_next T
        = Measure.map
            (fun z : PhaseSpace d => (charX_prev T z, charV_prev T z)) f₀ := by
      rw [h_fnext_T, h_prev_push T hT_Icc, h_prev_init]
    rw [h_marg, h_meq,
        integral_map h_aemeas_f₀_T (h_integrand_cont T hT_Icc).aestronglyMeasurable]
  exact h_cont_pf.congr_of_eventuallyEq h_eq_L h_val_T

/-- A shifted flow curve `s ↦ Φ (s − T) w` is continuous within `Ici T` at `T`
when the unshifted curve has a one-sided derivative at `0` on `[0, T_0]`. -/
private lemma vlasovGlue_shifted_flow_contWithin
    {d : ℕ}
    (charW : ℝ → PhaseSpace d → PhysSpace d) (w : PhaseSpace d) {v₀ : PhysSpace d}
    (T : ℝ) {T_0 : ℝ} (hT_0_pos : 0 < T_0)
    (hb : HasDerivWithinAt (fun s => charW s w) v₀ (Set.Icc 0 T_0) 0) :
    ContinuousWithinAt (fun s => charW (s - T) w) (Set.Ici T) T := by
  have h_nhdsW_0 : Set.Icc (0 : ℝ) T_0 ∈ nhdsWithin 0 (Set.Ici 0) :=
    Icc_mem_nhdsGE hT_0_pos
  have h_cont : ContinuousWithinAt (fun s => charW s w) (Set.Ici 0) 0 :=
    hb.continuousWithinAt.mono_of_mem_nhdsWithin h_nhdsW_0
  have h_sub_cont : ContinuousWithinAt (fun s : ℝ => s - T) (Set.Ici T) T :=
    ((continuous_id.sub continuous_const).continuousAt).continuousWithinAt
  have h_sub_maps : Set.MapsTo (fun s : ℝ => s - T) (Set.Ici T) (Set.Ici 0) :=
    fun s hs => Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp hs])
  exact ContinuousWithinAt.comp_of_eq h_cont h_sub_cont h_sub_maps (sub_self T)

/-- Composed-pushforward infrastructure on the glued window `[T, T+T_0]`:
`g (s−T)` is the pushforward of `f₀` by the composed phase-space flow
(`g`'s window flow after the outer time-`T` map `(XT, VT)`), its spatial
marginal is the pushforward by the composed position map, and both composed
maps are a.e.-measurable. -/
private lemma vlasovGlue_composed_pushforward
    {d : ℕ}
    (f₀ : Measure (PhaseSpace d))
    (g : ℝ → Measure (PhaseSpace d))
    (f_prevT : Measure (PhaseSpace d))
    (charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    (XT VT : PhaseSpace d → PhysSpace d)
    {T T_0 : ℝ}
    (h_outer_aemeas : AEMeasurable (fun z : PhaseSpace d => (XT z, VT z)) f₀)
    (h_prevT_push : f_prevT = Measure.map (fun z : PhaseSpace d => (XT z, VT z)) f₀)
    (hg_init : g 0 = f_prevT)
    (hg_push_ex : ∀ t ∈ Set.Icc (0 : ℝ) T_0,
        g t = Measure.map (fun z : PhaseSpace d => (charX_g t z, charV_g t z)) (g 0))
    (hg_aemeas_ex : ∀ s ∈ Set.Icc (0 : ℝ) T_0,
        AEMeasurable (fun z : PhaseSpace d => (charX_g s z, charV_g s z)) (g 0)) :
    (∀ τ ∈ Set.Icc (0 : ℝ) T_0,
        AEMeasurable (fun z : PhaseSpace d =>
          (charX_g τ (XT z, VT z), charV_g τ (XT z, VT z))) f₀) ∧
    (∀ s ∈ Set.Icc T (T + T_0),
        g (s - T) = Measure.map (fun z : PhaseSpace d =>
          (charX_g (s - T) (XT z, VT z), charV_g (s - T) (XT z, VT z))) f₀) ∧
    (∀ s ∈ Set.Icc T (T + T_0),
        spatialMarginal (g (s - T)) = Measure.map (fun z : PhaseSpace d =>
          charX_g (s - T) (XT z, VT z)) f₀) ∧
    (∀ s ∈ Set.Icc T (T + T_0),
        AEMeasurable (fun z : PhaseSpace d => charX_g (s - T) (XT z, VT z)) f₀) := by
  have h_g_at_aemeas : ∀ τ ∈ Set.Icc (0 : ℝ) T_0,
      AEMeasurable (fun z : PhaseSpace d => (charX_g τ z, charV_g τ z))
        (Measure.map (fun z : PhaseSpace d => (XT z, VT z)) f₀) := by
    intro τ hτ
    have := hg_aemeas_ex τ hτ
    rw [hg_init, h_prevT_push] at this
    exact this
  have h_comp_aemeas : ∀ τ ∈ Set.Icc (0 : ℝ) T_0,
      AEMeasurable (fun z : PhaseSpace d =>
        (charX_g τ (XT z, VT z), charV_g τ (XT z, VT z))) f₀ := by
    intro τ hτ
    exact (h_g_at_aemeas τ hτ).comp_aemeasurable h_outer_aemeas
  have h_push_comp : ∀ s ∈ Set.Icc T (T + T_0),
      g (s - T) = Measure.map (fun z : PhaseSpace d =>
        (charX_g (s - T) (XT z, VT z), charV_g (s - T) (XT z, VT z))) f₀ := by
    intro s hs
    have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rw [hg_push_ex (s - T) hsT_Icc, hg_init, h_prevT_push,
        AEMeasurable.map_map_of_aemeasurable
          (h_g_at_aemeas (s - T) hsT_Icc) h_outer_aemeas]
    rfl
  refine ⟨h_comp_aemeas, h_push_comp, fun s hs => ?_, fun s hs => ?_⟩
  · have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    unfold spatialMarginal
    rw [h_push_comp s hs,
        AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable
          (h_comp_aemeas (s - T) hsT_Icc)]
    rfl
  · have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact measurable_fst.comp_aemeasurable (h_comp_aemeas (s - T) hsT_Icc)

/-- Pointwise composed-pushforward rewrite of the force integral on the glued
window: for `s ∈ [T, T+T_0]` the integral of the force integrand against
`f_next s` equals the integral of the flow-composed integrand against `f₀`.
Serves both the eventually-equal rewrite and the value-at-`T` bridge of the
RIGHT seam close. -/
private lemma vlasovGlue_composed_integral_eq
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d))
    {T T_0 : ℝ} (hT_pos : 0 < T)
    (f_prev g : ℝ → Measure (PhaseSpace d))
    (h_prev_init : f_prev 0 = f₀)
    (charX_prev charV_prev charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    (h_prev_push : ∀ t ∈ Set.Icc (0 : ℝ) T,
        f_prev t =
          Measure.map (fun z : PhaseSpace d => (charX_prev t z, charV_prev t z)) (f_prev 0))
    (hg_init : g 0 = f_prev T)
    (hg_init_cond : ∀ z : PhaseSpace d, charX_g 0 z = z.1 ∧ charV_g 0 z = z.2)
    (f_next : ℝ → Measure (PhaseSpace d))
    (hf_next_T : f_next T = f_prev T)
    (hf_next_gt : ∀ s, T < s → f_next s = g (s - T))
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (h_comp_aemeas : ∀ τ ∈ Set.Icc (0 : ℝ) T_0,
        AEMeasurable (fun z : PhaseSpace d =>
          (charX_g τ (charX_prev T z, charV_prev T z),
           charV_g τ (charX_prev T z, charV_prev T z))) f₀)
    (h_g_push_comp : ∀ s ∈ Set.Icc T (T + T_0),
        g (s - T) = Measure.map (fun z : PhaseSpace d =>
          (charX_g (s - T) (charX_prev T z, charV_prev T z),
           charV_g (s - T) (charX_prev T z, charV_prev T z))) f₀)
    (h_integrand_cont : ∀ τ ∈ Set.Icc (0 : ℝ) T_0,
        Continuous (fun z : PhaseSpace d =>
          @inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (g τ)) z.1)
            (gradVφ z)))
    (s : ℝ) (hs : s ∈ Set.Icc T (T + T_0)) :
    (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
        @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (spatialMarginal (f_next s)) z.1)
          (gradVφ z)) ∂(f_next s))
      = ∫ z, (@inner ℝ (PhysSpace d) _
            (charV_g (s - T) (charX_prev T z, charV_prev T z))
            (gradXφ (charX_g (s - T) (charX_prev T z, charV_prev T z),
                     charV_g (s - T) (charX_prev T z, charV_prev T z))) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (g (s - T)))
              (charX_g (s - T) (charX_prev T z, charV_prev T z)))
            (gradVφ (charX_g (s - T) (charX_prev T z, charV_prev T z),
                     charV_g (s - T) (charX_prev T z, charV_prev T z)))) ∂f₀ := by
  have hT_Icc : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
  have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  by_cases hs_eq : s = T
  · -- s = T: f_next T = f_prev T = composed pushforward (collapse g at 0 = id)
    have hs_T_zero : s - T = 0 := by rw [hs_eq]; exact sub_self T
    have h_fnext_s : f_next s = f_prev T := by
      rw [hs_eq]; exact hf_next_T
    have h_marg_eq : spatialMarginal (f_next s) = spatialMarginal (g (s - T)) := by
      rw [h_fnext_s, hs_T_zero, hg_init]
    have h_meq : f_next s = Measure.map
        (fun z : PhaseSpace d =>
          (charX_g (s - T) (charX_prev T z, charV_prev T z),
           charV_g (s - T) (charX_prev T z, charV_prev T z))) f₀ := by
      rw [h_fnext_s, h_prev_push T hT_Icc, h_prev_init]
      apply Measure.map_congr
      apply Filter.Eventually.of_forall
      intro z
      simp only [hs_T_zero, (hg_init_cond _).1, (hg_init_cond _).2]
    rw [h_marg_eq, h_meq,
        integral_map (h_comp_aemeas (s - T) hsT_Icc)
          (h_integrand_cont (s - T) hsT_Icc).aestronglyMeasurable]
  · -- s > T: f_next s = g (s − T) = composed pushforward
    have hs_gt : T < s := lt_of_le_of_ne hs.1 (Ne.symm hs_eq)
    have h_fnext_s : f_next s = g (s - T) := hf_next_gt s hs_gt
    have h_marg_eq : spatialMarginal (f_next s) = spatialMarginal (g (s - T)) :=
      congrArg spatialMarginal h_fnext_s
    have h_meq : f_next s = Measure.map
        (fun z : PhaseSpace d =>
          (charX_g (s - T) (charX_prev T z, charV_prev T z),
           charV_g (s - T) (charX_prev T z, charV_prev T z))) f₀ := by
      rw [h_fnext_s]; exact h_g_push_comp s hs
    rw [h_marg_eq, h_meq,
        integral_map (h_comp_aemeas (s - T) hsT_Icc)
          (h_integrand_cont (s - T) hsT_Icc).aestronglyMeasurable]

/-- RIGHT seam continuity of the force-integral functional at `T`: on `Ici T`
the glued solution is `g (·−T)` (via `hf_next_T`/`hf_next_gt`), represented as
the composed pushforward of `f₀` by `g`'s window flow after `f_prev`'s time-`T`
flow; the claim reduces to the generic seam DCT lemma
`vlasovGlue_seam_forceIntegral_cont` on the composed flow. -/
private lemma vlasovGlue_seam_contRight
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT_pos : 0 < T) {T_0 : ℝ} (hT_0_pos : 0 < T_0)
    (f_prev : ℝ → Measure (PhaseSpace d))
    (h_prev_init : f_prev 0 = f₀)
    (h_prev_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f_prev t))
    (hM_prev : ∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f_prev t)) ≤ M)
    (charX_prev charV_prev : ℝ → PhaseSpace d → PhysSpace d)
    (h_prev_push : ∀ t ∈ Set.Icc (0 : ℝ) T,
        f_prev t =
          Measure.map (fun z : PhaseSpace d => (charX_prev t z, charV_prev t z)) (f_prev 0))
    (h_prev_aemeas : ∀ s ∈ Set.Icc (0 : ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) (f_prev 0))
    (h_prev_boundary : ∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
        HasDerivWithinAt (fun s => charX_prev s z) (charV_prev t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV_prev s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (f_prev t)) (charX_prev t z)))
          (Set.Icc 0 T) t)
    (h_prev_ic : ∀ z : PhaseSpace d, charX_prev 0 z = z.1 ∧ charV_prev 0 z = z.2)
    (g : ℝ → Measure (PhaseSpace d))
    (charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    (hg_init : g 0 = f_prev T)
    (hg_mom : ∀ t ∈ Set.Icc (0 : ℝ) T_0, HasFiniteFirstMoment (g t))
    (hg_mom_unif : ∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T_0, ∫ y, ‖y‖ ∂(spatialMarginal (g t)) ≤ M)
    (hg_push_ex : ∀ t ∈ Set.Icc (0 : ℝ) T_0,
        g t = Measure.map (fun z : PhaseSpace d => (charX_g t z, charV_g t z)) (g 0))
    (hg_aemeas_ex : ∀ s ∈ Set.Icc (0 : ℝ) T_0,
        AEMeasurable (fun z : PhaseSpace d => (charX_g s z, charV_g s z)) (g 0))
    (hg_boundary : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T_0,
        HasDerivWithinAt (fun s => charX_g s z) (charV_g t z) (Set.Icc 0 T_0) t ∧
        HasDerivWithinAt (fun s => charV_g s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (g t)) (charX_g t z)))
          (Set.Icc 0 T_0) t)
    (hg_init_cond : ∀ z : PhaseSpace d, charX_g 0 z = z.1 ∧ charV_g 0 z = z.2)
    (f_next : ℝ → Measure (PhaseSpace d))
    (hf_next_T : f_next T = f_prev T)
    (hf_next_gt : ∀ s, T < s → f_next s = g (s - T))
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z : PhaseSpace d, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z : PhaseSpace d, gradVφ z = gradient (fun v => φ (z.1, v)) z.2) :
    ContinuousWithinAt
      (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
              @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW (spatialMarginal (f_next s)) z.1)
                (gradVφ z)) ∂(f_next s)) (Set.Ici T) T := by
  have hT_Icc : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
  have h_nhd_R : Set.Icc T (T + T_0) ∈ nhdsWithin T (Set.Ici T) :=
    Icc_mem_nhdsGE (by linarith : T < T + T_0)
  have h_outer_aemeas : AEMeasurable
      (fun z : PhaseSpace d => (charX_prev T z, charV_prev T z)) f₀ :=
    h_prev_init ▸ h_prev_aemeas T hT_Icc
  set Zpos : ℝ → PhaseSpace d → PhysSpace d :=
    fun s z => charX_g (s - T) (charX_prev T z, charV_prev T z) with hZpos_def
  set Zvel : ℝ → PhaseSpace d → PhysSpace d :=
    fun s z => charV_g (s - T) (charX_prev T z, charV_prev T z) with hZvel_def
  have hgradXφ_cont : Continuous gradXφ :=
    vlasovGlue_gradXφ_continuous φ hφ_smooth gradXφ hgradXφ
  have hgradVφ_cont : Continuous gradVφ :=
    vlasovGlue_gradVφ_continuous φ hφ_smooth gradVφ hgradVφ
  have h_int_marg_g := dobrushinFlow_marginal_gradW_integrable gradW L hL T_0
    g hg_mom
  -- Composed pushforward of g's spatial marginal (hoisted helper), bridged to
  -- the Zpos/Zvel forms.
  have h_prevT_push : f_prev T
      = Measure.map (fun z : PhaseSpace d => (charX_prev T z, charV_prev T z)) f₀ := by
    rw [h_prev_push T hT_Icc, h_prev_init]
  obtain ⟨h_comp_aemeas, h_g_push_comp', h_push_marg', h_aemeas_marg'⟩ :=
    vlasovGlue_composed_pushforward f₀ g (f_prev T) charX_g charV_g
      (charX_prev T) (charV_prev T) h_outer_aemeas h_prevT_push hg_init
      hg_push_ex hg_aemeas_ex
  have h_g_push_comp : ∀ s ∈ Set.Icc T (T + T_0),
      g (s - T) = Measure.map
        (fun z : PhaseSpace d => (Zpos s z, Zvel s z)) f₀ := by
    intro s hs
    simpa only [hZpos_def, hZvel_def] using h_g_push_comp' s hs
  have h_push_marg : ∀ s ∈ Set.Icc T (T + T_0),
      spatialMarginal (g (s - T))
        = Measure.map (fun z : PhaseSpace d => Zpos s z) f₀ := by
    intro s hs
    simpa only [hZpos_def] using h_push_marg' s hs
  have h_aemeas_marg : ∀ s ∈ Set.Icc T (T + T_0),
      AEMeasurable (fun z : PhaseSpace d => Zpos s z) f₀ := by
    intro s hs
    simpa only [hZpos_def] using h_aemeas_marg' s hs
  -- Composed growth bound: Piece A on g over [0,T_0] composed with Piece A on
  -- prev at T (both via the hoisted clamp construction).
  obtain ⟨C_prev, hC_prev_nn, hC_prev_pair, _h_cont_Icc_prev⟩ :=
    vlasovGlue_flow_growthBound gradW L hL f_prev charX_prev charV_prev
      T hT_pos h_prev_mom hM_prev h_prev_ic h_prev_boundary
  obtain ⟨C_g, hC_g_nn, hC_g_pair, _h_cont_Icc_g⟩ :=
    vlasovGlue_flow_growthBound gradW L hL g charX_g charV_g
      T_0 hT_0_pos hg_mom hg_mom_unif hg_init_cond hg_boundary
  obtain ⟨M_g, _hM_g_nn, hM_g_bd⟩ := hg_mom_unif
  have h_y_int_marg_g : ∀ τ ∈ Set.Icc (0 : ℝ) T_0,
      Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal (g τ)) :=
    fun τ hτ => vlasovGlue_marginal_norm_integrable (g τ) (hg_mom τ hτ)
  set C_comp : ℝ := C_g * C_prev + C_g with hC_comp_def
  have hC_comp_nn : 0 ≤ C_comp := by positivity
  have hC_comp_pair : ∀ s ∈ Set.Icc T (T + T_0), ∀ z : PhaseSpace d,
      ‖(Zpos s z, Zvel s z)‖ ≤ C_comp * (‖z‖ + 1) := by
    intro s hs z
    have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h_prev : ‖(charX_prev T z, charV_prev T z)‖ ≤ C_prev * (‖z‖ + 1) :=
      hC_prev_pair T hT_Icc z
    have h_g : ‖(charX_g (s - T) (charX_prev T z, charV_prev T z),
                 charV_g (s - T) (charX_prev T z, charV_prev T z))‖
        ≤ C_g * (‖(charX_prev T z, charV_prev T z)‖ + 1) :=
      hC_g_pair (s - T) hsT_Icc (charX_prev T z, charV_prev T z)
    have hz1 : (0 : ℝ) ≤ ‖z‖ + 1 := by positivity
    calc ‖(Zpos s z, Zvel s z)‖
        = ‖(charX_g (s - T) (charX_prev T z, charV_prev T z),
            charV_g (s - T) (charX_prev T z, charV_prev T z))‖ := by
          simp only [hZpos_def, hZvel_def]
      _ ≤ C_g * (‖(charX_prev T z, charV_prev T z)‖ + 1) := h_g
      _ ≤ C_g * (C_prev * (‖z‖ + 1) + 1) := by
          apply mul_le_mul_of_nonneg_left _ hC_g_nn; linarith
      _ ≤ C_comp * (‖z‖ + 1) := by
          simp only [hC_comp_def]
          nlinarith [mul_nonneg hC_g_nn (norm_nonneg z),
            mul_nonneg (mul_nonneg hC_g_nn hC_prev_nn) hz1]
  have hC_comp_X : ∀ s ∈ Set.Icc T (T + T_0), ∀ z : PhaseSpace d,
      ‖Zpos s z‖ ≤ C_comp * (‖z‖ + 1) := by
    intro s hs z
    exact le_trans (norm_fst_le (Zpos s z, Zvel s z)) (hC_comp_pair s hs z)
  -- Seam continuity of the composed flow at T (hoisted shift helper).
  have h_Zpos_cont : ∀ z : PhaseSpace d,
      ContinuousWithinAt (fun s => Zpos s z) (Set.Ici T) T := by
    intro z
    have := vlasovGlue_shifted_flow_contWithin charX_g
      (charX_prev T z, charV_prev T z) T hT_0_pos
      (hg_boundary (charX_prev T z, charV_prev T z) 0 ⟨le_refl 0, hT_0_pos.le⟩).1
    simpa only [hZpos_def] using this
  have h_Zvel_cont : ∀ z : PhaseSpace d,
      ContinuousWithinAt (fun s => Zvel s z) (Set.Ici T) T := by
    intro z
    have := vlasovGlue_shifted_flow_contWithin charV_g
      (charX_prev T z, charV_prev T z) T hT_0_pos
      (hg_boundary (charX_prev T z, charV_prev T z) 0 ⟨le_refl 0, hT_0_pos.le⟩).2
    simpa only [hZvel_def] using this
  -- Continuity of the un-pushed integrand in z (for integral_map's
  -- AEStronglyMeasurable side).
  have h_conv_z_cont : ∀ τ ∈ Set.Icc (0 : ℝ) T_0,
      Continuous (fun z : PhaseSpace d =>
        convolveFunctionMeasure gradW (spatialMarginal (g τ)) z.1) := by
    intro τ hτ
    have : IsProbabilityMeasure (g τ) := (hg_mom τ hτ).1
    have : IsProbabilityMeasure (spatialMarginal (g τ)) :=
      (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mpr inferInstance
    exact (convolveFunctionMeasure_lipschitz_in_x gradW L hL
      (spatialMarginal (g τ)) (h_int_marg_g τ hτ)).continuous.comp continuous_fst
  have h_integrand_cont : ∀ τ ∈ Set.Icc (0 : ℝ) T_0,
      Continuous (fun z : PhaseSpace d =>
        @inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
        @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (spatialMarginal (g τ)) z.1)
          (gradVφ z)) := by
    intro τ hτ
    exact (continuous_snd.inner hgradXφ_cont).sub
      ((h_conv_z_cont τ hτ).inner hgradVφ_cont)
  -- Eventually-equal rewrite to the composed-pushforward form (pointwise helper).
  have h_intg_eq := vlasovGlue_composed_integral_eq gradW f₀ hT_pos f_prev g
    h_prev_init charX_prev charV_prev charX_g charV_g h_prev_push hg_init
    hg_init_cond f_next hf_next_T hf_next_gt gradXφ gradVφ h_comp_aemeas
    h_g_push_comp' h_integrand_cont
  have h_eq_R : (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (f_next s)) z.1)
            (gradVφ z)) ∂(f_next s))
      =ᶠ[nhdsWithin T (Set.Ici T)]
      (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ (Zvel s z)
            (gradXφ (Zpos s z, Zvel s z)) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (g (s - T)))
              (Zpos s z))
            (gradVφ (Zpos s z, Zvel s z))) ∂f₀) := by
    apply Filter.Eventually.mono h_nhd_R
    intro s hs
    simpa only [hZpos_def, hZvel_def] using h_intg_eq s hs
  obtain ⟨M_φ, hgradXφ_bd, hgradVφ_bd⟩ :=
    vlasovGlue_gradφ_bound φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ
  -- DCT via the generic seam lemma on the composed flow.
  have h_conv_cwn : ∀ z : PhaseSpace d, ContinuousWithinAt
      (fun s => convolveFunctionMeasure gradW (spatialMarginal (g (s - T)))
        (Zpos s z)) (Set.Ici T) T := fun z =>
    flowConv_continuousWithinAt_Ici_seam gradW L hL Zpos f₀
      hf₀_int (by linarith : T < T + T_0)
      (fun s => spatialMarginal (g (s - T)))
      h_push_marg h_aemeas_marg h_Zpos_cont C_comp hC_comp_nn hC_comp_X z
  have h_aemeas_W : ∀ s ∈ Set.Icc T (T + T_0),
      AEMeasurable (fun z : PhaseSpace d => (Zpos s z, Zvel s z)) f₀ := by
    intro s hs
    have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    simpa only [hZpos_def, hZvel_def] using h_comp_aemeas (s - T) hsT_Icc
  have h_cont_pf : ContinuousWithinAt
      (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ (Zvel s z)
            (gradXφ (Zpos s z, Zvel s z)) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (g (s - T)))
              (Zpos s z))
            (gradVφ (Zpos s z, Zvel s z))) ∂f₀)
      (Set.Ici T) T :=
    vlasovGlue_seam_forceIntegral_cont gradW L hL f₀ hf₀_int gradXφ gradVφ
      hgradXφ_cont hgradVφ_cont M_φ hgradXφ_bd hgradVφ_bd
      (fun s => spatialMarginal (g (s - T))) Zpos Zvel
      T (Set.Ici T) (Set.Icc T (T + T_0)) h_nhd_R
      (fun s hs => by
        have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
          ⟨by linarith [hs.1], by linarith [hs.2]⟩
        have : IsProbabilityMeasure (g (s - T)) := (hg_mom (s - T) hsT_Icc).1
        exact (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mpr inferInstance)
      M_g
      (fun s hs => hM_g_bd (s - T) ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      (fun s hs => h_y_int_marg_g (s - T) ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      (fun s hs => h_int_marg_g (s - T) ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      C_comp hC_comp_pair h_aemeas_W h_Zpos_cont h_Zvel_cont h_conv_cwn
  -- Value at T bridge (pointwise helper at s = T).
  have h_val_T : (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (f_next T)) z.1)
            (gradVφ z)) ∂(f_next T))
      = ∫ z, (@inner ℝ (PhysSpace d) _ (Zvel T z)
            (gradXφ (Zpos T z, Zvel T z)) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (g (T - T)))
              (Zpos T z))
            (gradVφ (Zpos T z, Zvel T z))) ∂f₀ := by
    simpa only [hZpos_def, hZvel_def] using
      h_intg_eq T ⟨le_refl T, by linarith⟩
  exact h_cont_pf.congr_of_eventuallyEq h_eq_R h_val_T

/-- `HasDerivAt` of the glued position flow at interior times of the extended
window: piecewise from `f_prev`'s flow (`t < T`), the two-sided union of the
boundary bundles (`t = T`), and `g`'s shifted flow (`t > T`).  Pure ODE gluing —
takes only the position projections of the flow hypotheses. -/
private lemma vlasovGlue_flowX_hasDerivAt
    {d : ℕ}
    (charX_prev charV_prev charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    {T T_0 : ℝ} (hT_pos : 0 < T) (hT_0_pos : 0 < T_0)
    (h_prev_flowX : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ z : PhaseSpace d,
        HasDerivAt (fun s => charX_prev s z) (charV_prev t z) t)
    (h_prev_boundaryX : ∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
        HasDerivWithinAt (fun s => charX_prev s z) (charV_prev t z) (Set.Icc 0 T) t)
    (hg_boundaryX : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T_0,
        HasDerivWithinAt (fun s => charX_g s z) (charV_g t z) (Set.Icc 0 T_0) t)
    (hg_init_cond : ∀ z : PhaseSpace d, charX_g 0 z = z.1 ∧ charV_g 0 z = z.2)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) (T + T_0)) (z : PhaseSpace d) :
    HasDerivAt (fun s => if s ≤ T then charX_prev s z
        else charX_g (s - T) (charX_prev T z, charV_prev T z))
      (if t ≤ T then charV_prev t z
        else charV_g (t - T) (charX_prev T z, charV_prev T z)) t := by
  by_cases ht_le : t ≤ T
  · simp only [ite_eq_left ht_le]
    -- Sub-case: t < T (strict interior) vs t = T (boundary)
    by_cases ht_lt : t < T
    · -- t < T strict: piecewise function = charX_prev · z near t
      have h_ev : (fun s => if s ≤ T then charX_prev s z
          else charX_g (s - T) (charX_prev T z, charV_prev T z)) =ᶠ[nhds t]
          (fun s => charX_prev s z) := by
        apply Filter.Eventually.mono (eventually_lt_nhds ht_lt)
        intro s hs; simp [le_of_lt hs]
      exact ((h_prev_flowX t ⟨ht.1, ht_lt⟩ z).congr_of_eventuallyEq h_ev)
    · -- t = T: boundary HasDerivAt via HasDerivWithinAt.union (Iic T ∪ Ici T = univ)
      push Not at ht_lt
      have h_t_eq : t = T := le_antisymm ht_le ht_lt
      have hT_in : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
      have h_bX := h_prev_boundaryX z T hT_in
      have h0_T0_in : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T_0 := ⟨le_refl 0, hT_0_pos.le⟩
      have h_g_bX := hg_boundaryX (charX_prev T z, charV_prev T z) 0 h0_T0_in
      have h_nhd_L : Set.Icc 0 T ∈ nhdsWithin T (Set.Iic T) := Icc_mem_nhdsLE hT_pos
      have h_nhd_R : Set.Icc 0 T_0 ∈ nhdsWithin (0 : ℝ) (Set.Ici 0) :=
        Icc_mem_nhdsGE hT_0_pos
      -- LEFT: HasDerivWithinAt charX_prev on Iic T at T
      have hX_Lic := h_bX.mono_of_mem_nhdsWithin h_nhd_L
      have hX_left : HasDerivWithinAt
          (fun s => if s ≤ T then charX_prev s z
            else charX_g (s - T) (charX_prev T z, charV_prev T z))
          (charV_prev T z) (Set.Iic T) T :=
        hX_Lic.congr_of_mem (fun s hs => by simp [Set.mem_Iic.mp hs]) Set.self_mem_Iic
      -- RIGHT: chain rule from g's boundary at 0
      have hX_Ici0 := h_g_bX.mono_of_mem_nhdsWithin h_nhd_R
      have h_sub_R : HasDerivWithinAt (· - T) 1 (Set.Ici T) T :=
        ((hasDerivAt_id' T).sub_const T).hasDerivWithinAt
      have h_mapR : Set.MapsTo (· - T) (Set.Ici T) (Set.Ici 0) :=
        fun s hs => Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp hs])
      have h_chainX : HasDerivWithinAt
          (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z))
          (charV_g 0 (charX_prev T z, charV_prev T z)) (Set.Ici T) T := by
        have := HasDerivWithinAt.scomp_of_eq T hX_Ici0 h_sub_R h_mapR (sub_self T).symm
        simpa [Function.comp_def, one_smul] using this
      have hVg0_eq : charV_g 0 (charX_prev T z, charV_prev T z) = charV_prev T z :=
        (hg_init_cond (charX_prev T z, charV_prev T z)).2
      rw [hVg0_eq] at h_chainX
      have hX_right : HasDerivWithinAt
          (fun s => if s ≤ T then charX_prev s z
            else charX_g (s - T) (charX_prev T z, charV_prev T z))
          (charV_prev T z) (Set.Ici T) T :=
        h_chainX.congr_of_mem
          (fun s hs => by
            by_cases hle : s ≤ T
            · have heq : s = T := le_antisymm hle (Set.mem_Ici.mp hs)
              simp [heq, sub_self,
                (hg_init_cond (charX_prev T z, charV_prev T z)).1]
            · simp [hle])
          Set.self_mem_Ici
      have hX_union := hX_left.union hX_right
      rw [Set.Iic_union_Ici] at hX_union
      rw [h_t_eq]
      exact hX_union.hasDerivAt Filter.univ_mem
  · simp only [ite_eq_right ht_le]
    push Not at ht_le
    -- t > T: use hg_boundaryX at (t - T) with chain rule for (s ↦ s - T)
    have htT_mem : t - T ∈ Set.Ioo (0 : ℝ) T_0 := ⟨by linarith, by linarith [ht.2]⟩
    have h_g_deriv : HasDerivAt (fun s => charX_g s (charX_prev T z, charV_prev T z))
        (charV_g (t - T) (charX_prev T z, charV_prev T z)) (t - T) :=
      (hg_boundaryX (charX_prev T z, charV_prev T z) (t - T)
          (Set.Ioo_subset_Icc_self htT_mem)).hasDerivAt
        (Icc_mem_nhds htT_mem.1 htT_mem.2)
    have h_sub : HasDerivAt (· - T) 1 t := (hasDerivAt_id' t).sub_const T
    have h_chain : HasDerivAt (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z))
        (charV_g (t - T) (charX_prev T z, charV_prev T z)) t := by
      have := HasDerivAt.scomp_of_eq t h_g_deriv h_sub rfl
      simpa [Function.comp_def, one_smul] using this
    have h_ev : (fun s => if s ≤ T then charX_prev s z
        else charX_g (s - T) (charX_prev T z, charV_prev T z)) =ᶠ[nhds t]
        (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z)) := by
      apply Filter.Eventually.mono (eventually_gt_nhds ht_le)
      intro s hs; simp [not_le.mpr hs]
    exact h_chain.congr_of_eventuallyEq h_ev

/-- `HasDerivAt` of the glued velocity flow at interior times of the extended
window, with the force term against the glued measure `f_next` (consumed only
through its value hypotheses).  Mirrors `vlasovGlue_flowX_hasDerivAt` with the
velocity projections and the marginal bridges. -/
private lemma vlasovGlue_flowV_hasDerivAt
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (f_prev g : ℝ → Measure (PhaseSpace d))
    (charX_prev charV_prev charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    {T T_0 : ℝ} (hT_pos : 0 < T) (hT_0_pos : 0 < T_0)
    (h_prev_flowV : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ z : PhaseSpace d,
        HasDerivAt (fun s => charV_prev s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (f_prev t))
              (charX_prev t z))) t)
    (h_prev_boundaryV : ∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
        HasDerivWithinAt (fun s => charV_prev s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (f_prev t)) (charX_prev t z)))
          (Set.Icc 0 T) t)
    (hg_boundaryV : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T_0,
        HasDerivWithinAt (fun s => charV_g s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (g t)) (charX_g t z)))
          (Set.Icc 0 T_0) t)
    (hg_init : g 0 = f_prev T)
    (hg_init_cond : ∀ z : PhaseSpace d, charX_g 0 z = z.1 ∧ charV_g 0 z = z.2)
    (f_next : ℝ → Measure (PhaseSpace d))
    (hf_next_le : ∀ s, s ≤ T → f_next s = f_prev s)
    (hf_next_gt : ∀ s, T < s → f_next s = g (s - T))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) (T + T_0)) (z : PhaseSpace d) :
    HasDerivAt (fun s => if s ≤ T then charV_prev s z
        else charV_g (s - T) (charX_prev T z, charV_prev T z))
      (-(convolveFunctionMeasure gradW (spatialMarginal (f_next t))
          (if t ≤ T then charX_prev t z
            else charX_g (t - T) (charX_prev T z, charV_prev T z)))) t := by
  by_cases ht_le : t ≤ T
  · simp only [ite_eq_left ht_le]
    -- Sub-case: t < T (strict interior) vs t = T (boundary)
    by_cases ht_lt : t < T
    · -- t < T strict: piecewise function = charV_prev · z near t
      have h_ev : (fun s => if s ≤ T then charV_prev s z
          else charV_g (s - T) (charX_prev T z, charV_prev T z)) =ᶠ[nhds t]
          (fun s => charV_prev s z) := by
        apply Filter.Eventually.mono (eventually_lt_nhds ht_lt)
        intro s hs; simp [le_of_lt hs]
      have h_fnext_t : f_next t = f_prev t := hf_next_le t ht_le
      have h_prev_deriv := h_prev_flowV t ⟨ht.1, ht_lt⟩ z
      have h_eq_marg : spatialMarginal (f_prev t) = spatialMarginal (f_next t) :=
        congrArg spatialMarginal h_fnext_t.symm
      simp only [h_eq_marg] at h_prev_deriv
      exact h_prev_deriv.congr_of_eventuallyEq h_ev
    · -- t = T: boundary HasDerivAt via HasDerivWithinAt.union (same as charX case)
      push Not at ht_lt
      have h_t_eq : t = T := le_antisymm ht_le ht_lt
      have hT_in : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
      have h_bV := h_prev_boundaryV z T hT_in
      have h0_T0_in : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T_0 := ⟨le_refl 0, hT_0_pos.le⟩
      have h_g_bV := hg_boundaryV (charX_prev T z, charV_prev T z) 0 h0_T0_in
      have h_nhd_L : Set.Icc 0 T ∈ nhdsWithin T (Set.Iic T) := Icc_mem_nhdsLE hT_pos
      have h_nhd_R : Set.Icc 0 T_0 ∈ nhdsWithin (0 : ℝ) (Set.Ici 0) :=
        Icc_mem_nhdsGE hT_0_pos
      -- Bridge f_prev T ↔ f_next T (for spatial marginal in goal vs h_bV)
      have hfnextT : f_next T = f_prev T := hf_next_le T (le_refl T)
      have hfnextT_spat : spatialMarginal (f_next T) = spatialMarginal (f_prev T) :=
        congrArg spatialMarginal hfnextT
      -- LEFT: HasDerivWithinAt charV_prev on Iic T at T
      have hV_Lic := h_bV.mono_of_mem_nhdsWithin h_nhd_L
      have hV_left : HasDerivWithinAt
          (fun s => if s ≤ T then charV_prev s z
            else charV_g (s - T) (charX_prev T z, charV_prev T z))
          (-(convolveFunctionMeasure gradW (spatialMarginal (f_next T))
              (charX_prev T z)))
          (Set.Iic T) T := by
        rw [hfnextT_spat]
        exact hV_Lic.congr_of_mem (fun s hs => by simp [Set.mem_Iic.mp hs])
          Set.self_mem_Iic
      -- RIGHT: chain rule from g's boundary at 0
      have hV_Ici0 := h_g_bV.mono_of_mem_nhdsWithin h_nhd_R
      have h_sub_R : HasDerivWithinAt (· - T) 1 (Set.Ici T) T :=
        ((hasDerivAt_id' T).sub_const T).hasDerivWithinAt
      have h_mapR : Set.MapsTo (· - T) (Set.Ici T) (Set.Ici 0) :=
        fun s hs => Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp hs])
      have h_chainV : HasDerivWithinAt
          (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z))
          (-(convolveFunctionMeasure gradW
            (spatialMarginal (g 0))
            (charX_g 0 (charX_prev T z, charV_prev T z))))
          (Set.Ici T) T := by
        have := HasDerivWithinAt.scomp_of_eq T hV_Ici0 h_sub_R h_mapR (sub_self T).symm
        simpa [Function.comp_def, one_smul] using this
      have hXg0_eq : charX_g 0 (charX_prev T z, charV_prev T z) = charX_prev T z :=
        (hg_init_cond (charX_prev T z, charV_prev T z)).1
      have hg0_spat : spatialMarginal (g 0) = spatialMarginal (f_prev T) :=
        congrArg spatialMarginal hg_init
      rw [hXg0_eq, hg0_spat, ← hfnextT_spat] at h_chainV
      have hV_right : HasDerivWithinAt
          (fun s => if s ≤ T then charV_prev s z
            else charV_g (s - T) (charX_prev T z, charV_prev T z))
          (-(convolveFunctionMeasure gradW (spatialMarginal (f_next T))
              (charX_prev T z)))
          (Set.Ici T) T :=
        h_chainV.congr_of_mem
          (fun s hs => by
            by_cases hle : s ≤ T
            · have heq : s = T := le_antisymm hle (Set.mem_Ici.mp hs)
              simp [heq, sub_self,
                (hg_init_cond (charX_prev T z, charV_prev T z)).2]
            · simp [hle])
          Set.self_mem_Ici
      have hV_union := hV_left.union hV_right
      rw [Set.Iic_union_Ici] at hV_union
      rw [h_t_eq]
      exact hV_union.hasDerivAt Filter.univ_mem
  · simp only [ite_eq_right ht_le]
    push Not at ht_le
    -- t > T: use hg_boundaryV at (t - T)
    have htT_mem : t - T ∈ Set.Ioo (0 : ℝ) T_0 := ⟨by linarith, by linarith [ht.2]⟩
    have h_g_deriv : HasDerivAt (fun s => charV_g s (charX_prev T z, charV_prev T z))
        (-(convolveFunctionMeasure gradW (spatialMarginal (g (t - T)))
            (charX_g (t - T) (charX_prev T z, charV_prev T z)))) (t - T) :=
      (hg_boundaryV (charX_prev T z, charV_prev T z) (t - T)
          (Set.Ioo_subset_Icc_self htT_mem)).hasDerivAt
        (Icc_mem_nhds htT_mem.1 htT_mem.2)
    have h_sub : HasDerivAt (· - T) 1 t := (hasDerivAt_id' t).sub_const T
    have h_chain : HasDerivAt (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z))
        (-(convolveFunctionMeasure gradW (spatialMarginal (g (t - T)))
            (charX_g (t - T) (charX_prev T z, charV_prev T z)))) t := by
      have := HasDerivAt.scomp_of_eq t h_g_deriv h_sub rfl
      simpa [Function.comp_def, one_smul] using this
    -- f_next t = g (t - T) when t > T
    have h_fnext_t : f_next t = g (t - T) := hf_next_gt t ht_le
    -- Rewrite derivative value: g (t-T) → f_next t
    rw [← congrArg spatialMarginal h_fnext_t] at h_chain
    have h_ev : (fun s => if s ≤ T then charV_prev s z
        else charV_g (s - T) (charX_prev T z, charV_prev T z)) =ᶠ[nhds t]
        (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z)) := by
      apply Filter.Eventually.mono (eventually_gt_nhds ht_le)
      intro s hs; simp [not_le.mpr hs]
    exact h_chain.congr_of_eventuallyEq h_ev

/-- The weak PDE holds at every time `t' ≠ T` near the seam: to the left the
glued solution is `f_prev` (use its weak PDE), to the right it is `g (·−T)`
(use `g`'s weak PDE with the shift chain rule). -/
private lemma vlasovGlue_diff_ne
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (f_prev g : ℝ → Measure (PhaseSpace d))
    {T T_0 : ℝ}
    (h_prev_vlasov : IsVlasovSolutionOn gradW f_prev T)
    (h_g_vlasov : IsVlasovSolutionOn gradW g T_0)
    (f_next : ℝ → Measure (PhaseSpace d))
    (hf_next_le : ∀ s, s ≤ T → f_next s = f_prev s)
    (hf_next_gt : ∀ s, T < s → f_next s = g (s - T))
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z : PhaseSpace d, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z : PhaseSpace d, gradVφ z = gradient (fun v => φ (z.1, v)) z.2) :
    ∀ t' ∈ Set.Ioo (0 : ℝ) (T + T_0), t' ≠ T → HasDerivAt
      (fun s => ∫ z, φ z ∂f_next s)
      ((∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
              @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW (spatialMarginal (f_next t')) z.1)
                (gradVφ z)) ∂(f_next t')) + 0) t' := by
  intro t' ht' ht'_ne
  rcases lt_or_gt_of_ne ht'_ne with ht'_lt | ht'_gt
  · -- t' < T: use h_prev_vlasov + bridge f_next = f_prev on left of T
    have ht'_prev : t' ∈ Set.Ioo (0 : ℝ) T := ⟨ht'.1, ht'_lt⟩
    have h_ev : (fun s => ∫ z, φ z ∂f_next s) =ᶠ[nhds t']
        (fun s => ∫ z, φ z ∂f_prev s) := by
      apply Filter.Eventually.mono (eventually_lt_nhds ht'_lt)
      intro s hs; simp [hf_next_le s (le_of_lt hs)]
    have h_fnext_t' : f_next t' = f_prev t' := hf_next_le t' (le_of_lt ht'_lt)
    have h_deriv := h_prev_vlasov φ hφ_smooth hφ_compact gradXφ gradVφ
        hgradXφ hgradVφ t' ht'_prev
    rw [show (fun _ => (0 : ℝ)) t' = 0 from rfl, add_zero] at h_deriv
    have h_marg : spatialMarginal (f_next t') = spatialMarginal (f_prev t') :=
      congrArg spatialMarginal h_fnext_t'
    rw [add_zero, h_marg, h_fnext_t']
    exact h_deriv.congr_of_eventuallyEq h_ev
  · -- t' > T: use h_g_vlasov + chain rule + bridge f_next = g (·-T)
    have ht'_g : t' - T ∈ Set.Ioo (0 : ℝ) T_0 := ⟨by linarith, by linarith [ht'.2]⟩
    have h_ev : (fun s => ∫ z, φ z ∂f_next s) =ᶠ[nhds t']
        (fun s => ∫ z, φ z ∂g (s - T)) := by
      apply Filter.Eventually.mono (eventually_gt_nhds ht'_gt)
      intro s hs; simp [hf_next_gt s hs]
    have h_fnext_t' : f_next t' = g (t' - T) := hf_next_gt t' ht'_gt
    have h_g_deriv := h_g_vlasov φ hφ_smooth hφ_compact gradXφ gradVφ
        hgradXφ hgradVφ (t' - T) ht'_g
    rw [show (fun _ => (0 : ℝ)) (t' - T) = 0 from rfl, add_zero] at h_g_deriv
    have h_sub : HasDerivAt (· - T) 1 t' := (hasDerivAt_id' t').sub_const T
    have h_chain : HasDerivAt (fun s => ∫ z, φ z ∂g (s - T))
        (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (g (t' - T))) z.1)
            (gradVφ z)) ∂g (t' - T)) t' := by
      have := HasDerivAt.comp_of_eq t' h_g_deriv h_sub rfl
      simpa [Function.comp_def, mul_one] using this
    have h_marg : spatialMarginal (f_next t') = spatialMarginal (g (t' - T)) :=
      congrArg spatialMarginal h_fnext_t'
    rw [add_zero, h_marg, h_fnext_t']
    exact h_chain.congr_of_eventuallyEq h_ev

/-- LEFT seam continuity of the plain test-function integral at `T`: on `Iic T`
the glued solution agrees with `f_prev`; DCT with the constant dominator `Cφ`
against the window pushforward. -/
private lemma vlasovGlue_intCont_left
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    {T : ℝ} (hT_pos : 0 < T)
    (f_prev : ℝ → Measure (PhaseSpace d))
    (h_prev_init : f_prev 0 = f₀)
    (charX_prev charV_prev : ℝ → PhaseSpace d → PhysSpace d)
    (h_prev_push : ∀ t ∈ Set.Icc (0 : ℝ) T,
        f_prev t =
          Measure.map (fun z : PhaseSpace d => (charX_prev t z, charV_prev t z)) (f_prev 0))
    (h_prev_aemeas : ∀ s ∈ Set.Icc (0 : ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) (f_prev 0))
    (h_prev_boundary : ∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
        HasDerivWithinAt (fun s => charX_prev s z) (charV_prev t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV_prev s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (f_prev t)) (charX_prev t z)))
          (Set.Icc 0 T) t)
    (f_next : ℝ → Measure (PhaseSpace d))
    (hf_next_le : ∀ s, s ≤ T → f_next s = f_prev s)
    (φ : PhaseSpace d → ℝ) (hφ_cont : Continuous φ)
    (Cφ : ℝ) (hCφ : ∀ z : PhaseSpace d, ‖φ z‖ ≤ Cφ) :
    ContinuousWithinAt (fun s => ∫ z, φ z ∂f_next s) (Set.Iic T) T := by
  have h_nhd_L : Set.Icc (0 : ℝ) T ∈ nhdsWithin T (Set.Iic T) :=
    Icc_mem_nhdsLE hT_pos
  -- Equation: f_next = f_prev = pushforward of f₀ on Icc 0 T
  have h_eq_L : (fun s => ∫ z, φ z ∂f_next s) =ᶠ[nhdsWithin T (Set.Iic T)]
      (fun s => ∫ z, φ (charX_prev s z, charV_prev s z) ∂f₀) := by
    apply Filter.Eventually.mono h_nhd_L
    intro s hs
    change ∫ z, φ z ∂f_next s = ∫ z, φ (charX_prev s z, charV_prev s z) ∂f₀
    have h_fnext : f_next s = f_prev s := hf_next_le s hs.2
    have h_aemeas_f₀ : AEMeasurable
        (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) f₀ :=
      h_prev_init ▸ h_prev_aemeas s hs
    rw [h_fnext, h_prev_push s hs, h_prev_init]
    exact integral_map h_aemeas_f₀ hφ_cont.aestronglyMeasurable
  -- DCT for the pushforward-composed form
  have h_cont_pf : ContinuousWithinAt
      (fun s => ∫ z, φ (charX_prev s z, charV_prev s z) ∂f₀) (Set.Iic T) T := by
    apply continuousWithinAt_of_dominated (bound := fun _ => Cφ)
    · apply Filter.Eventually.mono h_nhd_L
      intro s hs
      have h_pair_aem : AEMeasurable
          (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) f₀ :=
        h_prev_init ▸ h_prev_aemeas s hs
      exact (hφ_cont.measurable.comp_aemeasurable h_pair_aem).aestronglyMeasurable
    · apply Filter.Eventually.mono h_nhd_L
      intro s _
      exact Filter.Eventually.of_forall fun z => hCφ _
    · exact integrable_const _
    · apply Filter.Eventually.of_forall
      intro z
      have hT_Icc : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
      have h_bX := (h_prev_boundary z T hT_Icc).1
      have h_bV := (h_prev_boundary z T hT_Icc).2
      have h_pair_Icc : ContinuousWithinAt
          (fun s => (charX_prev s z, charV_prev s z)) (Set.Icc 0 T) T :=
        h_bX.continuousWithinAt.prodMk h_bV.continuousWithinAt
      have h_pair_Iic : ContinuousWithinAt
          (fun s => (charX_prev s z, charV_prev s z)) (Set.Iic T) T :=
        h_pair_Icc.mono_of_mem_nhdsWithin h_nhd_L
      exact hφ_cont.continuousAt.comp_continuousWithinAt h_pair_Iic
  -- Value at T: bridge via the pushforward formula
  have h_val_T : (∫ z, φ z ∂f_next T)
      = ∫ z, φ (charX_prev T z, charV_prev T z) ∂f₀ := by
    have hT_Icc : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
    have h_fnext_T : f_next T = f_prev T := hf_next_le T (le_refl T)
    have h_aemeas_f₀_T : AEMeasurable
        (fun z : PhaseSpace d => (charX_prev T z, charV_prev T z)) f₀ :=
      h_prev_init ▸ h_prev_aemeas T hT_Icc
    rw [h_fnext_T, h_prev_push T hT_Icc, h_prev_init]
    exact integral_map h_aemeas_f₀_T hφ_cont.aestronglyMeasurable
  exact h_cont_pf.congr_of_eventuallyEq h_eq_L h_val_T

/-- RIGHT seam continuity of the plain test-function integral at `T`: on
`Ici T` the glued solution is the composed pushforward off `g`; DCT with the
constant dominator `Cφ`. -/
private lemma vlasovGlue_intCont_right
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    {T : ℝ} (hT_pos : 0 < T) {T_0 : ℝ} (hT_0_pos : 0 < T_0)
    (f_prev : ℝ → Measure (PhaseSpace d))
    (h_prev_init : f_prev 0 = f₀)
    (charX_prev charV_prev : ℝ → PhaseSpace d → PhysSpace d)
    (h_prev_push : ∀ t ∈ Set.Icc (0 : ℝ) T,
        f_prev t =
          Measure.map (fun z : PhaseSpace d => (charX_prev t z, charV_prev t z)) (f_prev 0))
    (h_prev_aemeas : ∀ s ∈ Set.Icc (0 : ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) (f_prev 0))
    (g : ℝ → Measure (PhaseSpace d))
    (charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    (hg_init : g 0 = f_prev T)
    (hg_push_ex : ∀ t ∈ Set.Icc (0 : ℝ) T_0,
        g t = Measure.map (fun z : PhaseSpace d => (charX_g t z, charV_g t z)) (g 0))
    (hg_aemeas_ex : ∀ s ∈ Set.Icc (0 : ℝ) T_0,
        AEMeasurable (fun z : PhaseSpace d => (charX_g s z, charV_g s z)) (g 0))
    (hg_boundary : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T_0,
        HasDerivWithinAt (fun s => charX_g s z) (charV_g t z) (Set.Icc 0 T_0) t ∧
        HasDerivWithinAt (fun s => charV_g s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (g t)) (charX_g t z)))
          (Set.Icc 0 T_0) t)
    (hg_init_cond : ∀ z : PhaseSpace d, charX_g 0 z = z.1 ∧ charV_g 0 z = z.2)
    (f_next : ℝ → Measure (PhaseSpace d))
    (hf_next_T : f_next T = f_prev T)
    (hf_next_gt : ∀ s, T < s → f_next s = g (s - T))
    (φ : PhaseSpace d → ℝ) (hφ_cont : Continuous φ)
    (Cφ : ℝ) (hCφ : ∀ z : PhaseSpace d, ‖φ z‖ ≤ Cφ) :
    ContinuousWithinAt (fun s => ∫ z, φ z ∂f_next s) (Set.Ici T) T := by
  have h_nhd_R : Set.Icc T (T + T_0) ∈ nhdsWithin T (Set.Ici T) :=
    Icc_mem_nhdsGE (by linarith : T < T + T_0)
  have hT_Icc : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
  have h_outer_aemeas : AEMeasurable
      (fun z : PhaseSpace d => (charX_prev T z, charV_prev T z)) f₀ :=
    h_prev_init ▸ h_prev_aemeas T hT_Icc
  -- Eventually-equal: f_next s = composed pushforward on Icc T (T+T_0)
  have h_eq_R : (fun s => ∫ z, φ z ∂f_next s) =ᶠ[nhdsWithin T (Set.Ici T)]
      (fun s => ∫ z, φ
        (charX_g (s - T) (charX_prev T z, charV_prev T z),
         charV_g (s - T) (charX_prev T z, charV_prev T z)) ∂f₀) := by
    apply Filter.Eventually.mono h_nhd_R
    intro s hs
    change ∫ z, φ z ∂f_next s = ∫ z, φ
        (charX_g (s - T) (charX_prev T z, charV_prev T z),
         charV_g (s - T) (charX_prev T z, charV_prev T z)) ∂f₀
    have hs_T : T ≤ s := hs.1
    have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
      ⟨by linarith, by linarith [hs.2]⟩
    by_cases hs_eq : s = T
    · -- s = T: f_next s = f_next T = f_prev T = (charX_prev T, charV_prev T)#f₀
      --   RHS at s = T uses hg_init_cond to collapse (charX_g 0, charV_g 0) = id
      have hs_T_zero : s - T = 0 := by rw [hs_eq]; exact sub_self T
      have h_fnext_s : f_next s = f_prev T := by
        rw [hs_eq]; exact hf_next_T
      rw [h_fnext_s, h_prev_push T hT_Icc, h_prev_init,
          integral_map h_outer_aemeas hφ_cont.aestronglyMeasurable]
      congr 1
      funext z
      rw [hs_T_zero, (hg_init_cond _).1, (hg_init_cond _).2]
    · -- s > T: f_next s = g (s - T) = composed pushforward
      have hs_gt : T < s := lt_of_le_of_ne hs_T (Ne.symm hs_eq)
      have h_fnext_s : f_next s = g (s - T) := hf_next_gt s hs_gt
      rw [h_fnext_s, hg_push_ex (s - T) hsT_Icc, hg_init,
          h_prev_push T hT_Icc, h_prev_init]
      have h_g_at_sT : AEMeasurable
          (fun z : PhaseSpace d => (charX_g (s - T) z, charV_g (s - T) z))
          (Measure.map (fun z : PhaseSpace d =>
            (charX_prev T z, charV_prev T z)) f₀) := by
        have := hg_aemeas_ex (s - T) hsT_Icc
        rw [hg_init, h_prev_push T hT_Icc, h_prev_init] at this
        exact this
      have h_comp_aem : AEMeasurable
          (fun z : PhaseSpace d =>
            (charX_g (s - T) (charX_prev T z, charV_prev T z),
             charV_g (s - T) (charX_prev T z, charV_prev T z))) f₀ :=
        h_g_at_sT.comp_aemeasurable h_outer_aemeas
      rw [AEMeasurable.map_map_of_aemeasurable h_g_at_sT h_outer_aemeas]
      exact integral_map h_comp_aem hφ_cont.aestronglyMeasurable
  -- DCT for the composed-pushforward form
  have h_cont_pf : ContinuousWithinAt
      (fun s => ∫ z, φ
        (charX_g (s - T) (charX_prev T z, charV_prev T z),
         charV_g (s - T) (charX_prev T z, charV_prev T z)) ∂f₀)
      (Set.Ici T) T := by
    apply continuousWithinAt_of_dominated (bound := fun _ => Cφ)
    · apply Filter.Eventually.mono h_nhd_R
      intro s hs
      have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
        ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have h_g_at_sT : AEMeasurable
          (fun z : PhaseSpace d => (charX_g (s - T) z, charV_g (s - T) z))
          (Measure.map (fun z : PhaseSpace d =>
            (charX_prev T z, charV_prev T z)) f₀) := by
        have := hg_aemeas_ex (s - T) hsT_Icc
        rw [hg_init, h_prev_push T hT_Icc, h_prev_init] at this
        exact this
      have h_comp_aem : AEMeasurable
          (fun z : PhaseSpace d =>
            (charX_g (s - T) (charX_prev T z, charV_prev T z),
             charV_g (s - T) (charX_prev T z, charV_prev T z))) f₀ :=
        h_g_at_sT.comp_aemeasurable h_outer_aemeas
      exact (hφ_cont.measurable.comp_aemeasurable h_comp_aem).aestronglyMeasurable
    · apply Filter.Eventually.mono h_nhd_R
      intro s _
      exact Filter.Eventually.of_forall fun z => hCφ _
    · exact integrable_const _
    · -- Pointwise continuity: chain rule for (· - T) at T with charX_g/charV_g at 0
      apply Filter.Eventually.of_forall
      intro z
      have h0_Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T_0 := ⟨le_refl 0, hT_0_pos.le⟩
      have h_g_bX := (hg_boundary (charX_prev T z, charV_prev T z) 0 h0_Icc).1
      have h_g_bV := (hg_boundary (charX_prev T z, charV_prev T z) 0 h0_Icc).2
      have h_nhdsW_0 : Set.Icc (0 : ℝ) T_0 ∈ nhdsWithin 0 (Set.Ici 0) :=
        Icc_mem_nhdsGE hT_0_pos
      have h_g_bX_cont : ContinuousWithinAt
          (fun s' => charX_g s' (charX_prev T z, charV_prev T z))
          (Set.Ici 0) 0 :=
        h_g_bX.continuousWithinAt.mono_of_mem_nhdsWithin h_nhdsW_0
      have h_g_bV_cont : ContinuousWithinAt
          (fun s' => charV_g s' (charX_prev T z, charV_prev T z))
          (Set.Ici 0) 0 :=
        h_g_bV.continuousWithinAt.mono_of_mem_nhdsWithin h_nhdsW_0
      have h_sub_cont : ContinuousWithinAt (fun s : ℝ => s - T) (Set.Ici T) T :=
        ((continuous_id.sub continuous_const).continuousAt).continuousWithinAt
      have h_sub_maps : Set.MapsTo (fun s : ℝ => s - T) (Set.Ici T) (Set.Ici 0) :=
        fun s hs => Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp hs])
      have h_chainX : ContinuousWithinAt
          (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z))
          (Set.Ici T) T :=
        ContinuousWithinAt.comp_of_eq h_g_bX_cont h_sub_cont h_sub_maps (sub_self T)
      have h_chainV : ContinuousWithinAt
          (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z))
          (Set.Ici T) T :=
        ContinuousWithinAt.comp_of_eq h_g_bV_cont h_sub_cont h_sub_maps (sub_self T)
      have h_pair : ContinuousWithinAt
          (fun s => (charX_g (s - T) (charX_prev T z, charV_prev T z),
                     charV_g (s - T) (charX_prev T z, charV_prev T z)))
          (Set.Ici T) T :=
        h_chainX.prodMk h_chainV
      exact hφ_cont.continuousAt.comp_continuousWithinAt h_pair
  -- Value at T: integrate the s = T case
  have h_val_T : (∫ z, φ z ∂f_next T) = ∫ z, φ
      (charX_g (T - T) (charX_prev T z, charV_prev T z),
       charV_g (T - T) (charX_prev T z, charV_prev T z)) ∂f₀ := by
    rw [hf_next_T, h_prev_push T hT_Icc, h_prev_init,
        integral_map h_outer_aemeas hφ_cont.aestronglyMeasurable]
    congr 1; funext z
    rw [show T - T = (0 : ℝ) from sub_self T,
        (hg_init_cond _).1, (hg_init_cond _).2]
  exact h_cont_pf.congr_of_eventuallyEq h_eq_R h_val_T

/-- Pushforward equation for the glued solution against the glued piecewise
flow, on the extended window.  Serves both `IsLagrangianVlasovSolutionOn`'s
pushforward conjunct and the explicit conjunct (v). -/
private lemma vlasovGlue_pushforward_eq
    {d : ℕ}
    (f_prev g : ℝ → Measure (PhaseSpace d))
    (charX_prev charV_prev charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    {T T_0 : ℝ} (hT_pos : 0 < T)
    (h_prev_push : ∀ t ∈ Set.Icc (0 : ℝ) T,
        f_prev t =
          Measure.map (fun z : PhaseSpace d => (charX_prev t z, charV_prev t z)) (f_prev 0))
    (h_prev_aemeas : ∀ s ∈ Set.Icc (0 : ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) (f_prev 0))
    (hg_init : g 0 = f_prev T)
    (hg_push_ex : ∀ t ∈ Set.Icc (0 : ℝ) T_0,
        g t = Measure.map (fun z : PhaseSpace d => (charX_g t z, charV_g t z)) (g 0))
    (hg_aemeas_ex : ∀ s ∈ Set.Icc (0 : ℝ) T_0,
        AEMeasurable (fun z : PhaseSpace d => (charX_g s z, charV_g s z)) (g 0))
    (f_next : ℝ → Measure (PhaseSpace d))
    (hf_next_le : ∀ s, s ≤ T → f_next s = f_prev s)
    (hf_next_gt : ∀ s, T < s → f_next s = g (s - T))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (T + T_0)) :
    f_next t = Measure.map (fun z : PhaseSpace d =>
      ((if t ≤ T then charX_prev t z
         else charX_g (t - T) (charX_prev T z, charV_prev T z)),
       (if t ≤ T then charV_prev t z
         else charV_g (t - T) (charX_prev T z, charV_prev T z)))) (f_next 0) := by
  rw [hf_next_le 0 hT_pos.le]
  by_cases ht_le : t ≤ T
  · simp only [ite_eq_left ht_le]
    rw [hf_next_le t ht_le]
    exact h_prev_push t ⟨ht.1, ht_le⟩
  · simp only [ite_eq_right ht_le]
    push Not at ht_le
    rw [hf_next_gt t ht_le]
    have hT_mem : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
    have htT_mem : t - T ∈ Set.Icc (0 : ℝ) T_0 := ⟨by linarith, by linarith [ht.2]⟩
    rw [hg_push_ex (t - T) htT_mem, hg_init, h_prev_push T hT_mem]
    have h_prev_T_aemeas := h_prev_aemeas T hT_mem
    have h_g_at_tT := hg_aemeas_ex (t - T) htT_mem
    rw [hg_init, h_prev_push T hT_mem] at h_g_at_tT
    rw [AEMeasurable.map_map_of_aemeasurable h_g_at_tT h_prev_T_aemeas]
    rfl

/-- AEMeasurability of the glued piecewise flow against `f_next 0` on the
extended window.  Serves both `IsLagrangianVlasovSolutionOn`'s conjunct and
the explicit conjunct (vi). -/
private lemma vlasovGlue_flow_aemeasurable
    {d : ℕ}
    (f_prev g : ℝ → Measure (PhaseSpace d))
    (charX_prev charV_prev charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    {T T_0 : ℝ} (hT_pos : 0 < T)
    (h_prev_push : ∀ t ∈ Set.Icc (0 : ℝ) T,
        f_prev t =
          Measure.map (fun z : PhaseSpace d => (charX_prev t z, charV_prev t z)) (f_prev 0))
    (h_prev_aemeas : ∀ s ∈ Set.Icc (0 : ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) (f_prev 0))
    (hg_init : g 0 = f_prev T)
    (hg_aemeas_ex : ∀ s ∈ Set.Icc (0 : ℝ) T_0,
        AEMeasurable (fun z : PhaseSpace d => (charX_g s z, charV_g s z)) (g 0))
    (f_next : ℝ → Measure (PhaseSpace d))
    (hf_next_le : ∀ s, s ≤ T → f_next s = f_prev s)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) (T + T_0)) :
    AEMeasurable (fun z : PhaseSpace d =>
      ((if s ≤ T then charX_prev s z
         else charX_g (s - T) (charX_prev T z, charV_prev T z)),
       (if s ≤ T then charV_prev s z
         else charV_g (s - T) (charX_prev T z, charV_prev T z)))) (f_next 0) := by
  rw [hf_next_le 0 hT_pos.le]
  by_cases hs_le : s ≤ T
  · simp only [ite_eq_left hs_le]
    exact h_prev_aemeas s ⟨hs.1, hs_le⟩
  · simp only [ite_eq_right hs_le]
    push Not at hs_le
    have hT_mem : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
    have hsT_mem : s - T ∈ Set.Icc (0 : ℝ) T_0 := ⟨by linarith, by linarith [hs.2]⟩
    have h_g_at_sT := hg_aemeas_ex (s - T) hsT_mem
    rw [hg_init, h_prev_push T hT_mem] at h_g_at_sT
    exact h_g_at_sT.comp_aemeasurable (h_prev_aemeas T hT_mem)

/-- Finite first moment of the glued solution on the extended window,
piecewise from the two window moment hypotheses. -/
private lemma vlasovGlue_moment
    {d : ℕ}
    (f_prev g : ℝ → Measure (PhaseSpace d))
    {T T_0 : ℝ}
    (h_prev_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f_prev t))
    (hg_mom : ∀ t ∈ Set.Icc (0 : ℝ) T_0, HasFiniteFirstMoment (g t))
    (f_next : ℝ → Measure (PhaseSpace d))
    (hf_next_le : ∀ s, s ≤ T → f_next s = f_prev s)
    (hf_next_gt : ∀ s, T < s → f_next s = g (s - T)) :
    ∀ t ∈ Set.Icc (0 : ℝ) (T + T_0), HasFiniteFirstMoment (f_next t) := by
  intro t ht
  by_cases ht_le : t ≤ T
  · rw [hf_next_le t ht_le]
    exact h_prev_mom t ⟨ht.1, ht_le⟩
  · push Not at ht_le
    rw [hf_next_gt t ht_le]
    exact hg_mom (t - T) ⟨by linarith, by linarith [ht.2]⟩

/-- FLAT uniform first-moment bound on the glued solution's spatial marginal:
`max` of the two window envelopes, no cross-term. -/
private lemma vlasovGlue_moment_flat
    {d : ℕ}
    (f_prev g : ℝ → Measure (PhaseSpace d))
    {T T_0 : ℝ}
    (hM_prev : ∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f_prev t)) ≤ M)
    (hg_mom_unif : ∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T_0, ∫ y, ‖y‖ ∂(spatialMarginal (g t)) ≤ M)
    (f_next : ℝ → Measure (PhaseSpace d))
    (hf_next_le : ∀ s, s ≤ T → f_next s = f_prev s)
    (hf_next_gt : ∀ s, T < s → f_next s = g (s - T)) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ t ∈ Set.Icc (0 : ℝ) (T + T_0),
        ∫ y, ‖y‖ ∂(spatialMarginal (f_next t)) ≤ M := by
  obtain ⟨M_prev, hM_prev_nn, hM_prev_bd⟩ := hM_prev
  obtain ⟨M_g, _hM_g_nn, hM_g_bd⟩ := hg_mom_unif
  refine ⟨max M_prev M_g, le_trans hM_prev_nn (le_max_left _ _), fun t ht => ?_⟩
  by_cases ht_le : t ≤ T
  · rw [hf_next_le t ht_le]
    exact le_trans (hM_prev_bd t ⟨ht.1, ht_le⟩) (le_max_left _ _)
  · push Not at ht_le
    rw [hf_next_gt t ht_le]
    exact le_trans (hM_g_bd (t - T) ⟨by linarith, by linarith [ht.2]⟩) (le_max_right _ _)

/-- **One-window glue step.**

Given a solution `f_prev : ℝ → Measure (PhaseSpace d)` on `[0, T]`
satisfying the local-existence conjuncts (initial condition + finite first
moment + `IsLagrangianVlasovSolutionOn`), and a window length `T_0`
satisfying the smallness constraints `LocalSmallnessPLBuffer L T_0` +
`LocalSmallnessContraction L T_0`, produces a glued solution
`f_next : ℝ → Measure (PhaseSpace d)` on `[0, T + T_0]` that agrees with
`f_prev` on `[0, T]`.

**Proof strategy**:

1. Shift the initial condition: apply `vlasovWellPosedness_local` to
   `f_prev T` (which has finite first moment by `h_prev_mom T`) with
   window length `T_0`.  Gives a solution `g : ℝ → Measure (PhaseSpace d)`
   on `[0, T_0]` with `g 0 = f_prev T`.

2. Glue: define `f_next t := if t ≤ T then f_prev t else g (t - T)`.
   Agreement at `t = T` is by `g 0 = f_prev T`.

3. Verify the four output conjuncts:
   - Initial: `f_next 0 = f_prev 0 = f₀`.
   - Moment: piecewise from `h_prev_mom` and `g`'s moment bound.
   - `IsLagrangianVlasovSolutionOn` on `[0, T + T_0]`:
     * `IsVlasovSolutionOn`: weak PDE on `Ioo 0 (T + T_0)` — split at `T`,
       use `h_prev_lag.1` for `Ioo 0 T` part and `g`'s for `Ioo T (T+T_0)`,
       continuity at `T` from the integral being continuous.
     * Flow: glue the per-window flows via standard ODE composition
       (charX_next(t, z) := if t ≤ T then charX_prev(t, z) else
       charX_g(t - T, (charX_prev(T, z), charV_prev(T, z)))).
     * Pushforward equation: holds piecewise.
     * AEMeasurable witness: composition of AEMeasurable maps. -/
theorem vlasovWellPosedness_glue
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d))
    (hf₀ : HasFiniteFirstMoment f₀)
    {T : ℝ} (hT_pos : 0 < T)
    (f_prev : ℝ → Measure (PhaseSpace d))
    (h_prev_init : f_prev 0 = f₀)
    (h_prev_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f_prev t))
    -- FLAT (window-constant) uniform first-moment bound on f_prev's spatial marginal.
    (hM_prev : ∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f_prev t)) ≤ M)
    -- Explicit flow witnesses for f_prev (avoids witness-identity issues with
    -- IsLagrangianVlasovSolutionOn)
    (charX_prev charV_prev : ℝ → PhaseSpace d → PhysSpace d)
    (h_prev_vlasov : IsVlasovSolutionOn gradW f_prev T)
    (h_prev_flow : IsCharacteristicFlowOn gradW (fun t => spatialMarginal (f_prev t))
        charX_prev charV_prev (Set.Ioo 0 T) Set.univ)
    (h_prev_push : ∀ t ∈ Set.Icc (0 : ℝ) T,
        f_prev t =
          Measure.map (fun z : PhaseSpace d => (charX_prev t z, charV_prev t z)) (f_prev 0))
    (h_prev_aemeas : ∀ s ∈ Set.Icc (0 : ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) (f_prev 0))
    (h_prev_boundary : ∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
        HasDerivWithinAt (fun s => charX_prev s z) (charV_prev t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV_prev s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (f_prev t)) (charX_prev t z)))
          (Set.Icc 0 T) t)
    (h_prev_ic : ∀ z : PhaseSpace d, charX_prev 0 z = z.1 ∧ charV_prev 0 z = z.2)
    {T_0 : ℝ} (hT_0_pos : 0 < T_0)
    (hT_0_small_PL : LocalSmallnessPLBuffer L T_0)
    (hT_0_small_con : LocalSmallnessContraction L T_0)
    (hT_0_small_B : (L : ℝ) / (1 + (L : ℝ)) * (Real.exp ((1 + (L : ℝ)) * T_0) - 1) < 1) :
    ∃ (f_next : ℝ → Measure (PhaseSpace d))
      (charX_next charV_next : ℝ → PhaseSpace d → PhysSpace d),
      (∀ t ∈ Set.Icc (0 : ℝ) T, f_next t = f_prev t) ∧
      f_next 0 = f₀ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) (T + T_0), HasFiniteFirstMoment (f_next t)) ∧
      -- FLAT (window-constant) uniform first-moment bound on the spatial marginal.
      (∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ Set.Icc (0 : ℝ) (T + T_0), ∫ y, ‖y‖ ∂(spatialMarginal (f_next t)) ≤ M) ∧
      IsLagrangianVlasovSolutionOn gradW f_next (T + T_0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) (T + T_0),
          f_next t =
            Measure.map (fun z : PhaseSpace d => (charX_next t z, charV_next t z)) (f_next 0)) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) (T + T_0),
          AEMeasurable (fun z : PhaseSpace d => (charX_next s z, charV_next s z)) (f_next 0)) ∧
      (∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) (T + T_0) →
          HasDerivWithinAt (fun s => charX_next s z) (charV_next t z) (Set.Icc 0 (T + T_0)) t ∧
          HasDerivWithinAt (fun s => charV_next s z)
            (-(convolveFunctionMeasure gradW (spatialMarginal (f_next t)) (charX_next t z)))
            (Set.Icc 0 (T + T_0)) t) ∧
      (∀ z : PhaseSpace d, charX_next 0 z = z.1 ∧ charV_next 0 z = z.2) := by
  -- The gluing closes the boundary at `t = T` by combining the boundary
  -- regularity bundles from both windows: HasDerivWithinAt at T from the
  -- LEFT (via f_prev's boundary bundle at endpoint T) and HasDerivWithinAt
  -- at 0 from the RIGHT (via g's boundary bundle at endpoint 0), giving
  -- HasDerivAt at t = T in `f_next`'s frame.
  --
  -- Step 1: invoke vlasovWellPosedness_local on f_prev T to get g on [0, T_0]
  have h_prev_T_mom : HasFiniteFirstMoment (f_prev T) :=
    h_prev_mom T (Set.right_mem_Icc.mpr hT_pos.le)
  obtain ⟨g, charX_g, charV_g, hg_init, hg_mom, hg_mom_unif, hg_lag, hg_push_ex, hg_aemeas_ex,
          hg_boundary, hg_init_cond⟩ :=
    vlasovWellPosedness_local W gradW hgradW L hL
      (f_prev T) h_prev_T_mom hT_0_pos hT_0_small_PL hT_0_small_con hT_0_small_B
  -- Step 2: define the glued solution piecewise
  let f_next : ℝ → Measure (PhaseSpace d) :=
    fun t => if t ≤ T then f_prev t else g (t - T)
  -- Step 3: verify the output conjuncts
  -- Piecewise flow: for t ≤ T use charX_prev, for t > T compose with charX_g shifted
  let charX_next : ℝ → PhaseSpace d → PhysSpace d := fun t z =>
    if t ≤ T then charX_prev t z else charX_g (t - T) (charX_prev T z, charV_prev T z)
  let charV_next : ℝ → PhaseSpace d → PhysSpace d := fun t z =>
    if t ≤ T then charV_prev t z else charV_g (t - T) (charX_prev T z, charV_prev T z)
  have h_g_vlasov : IsVlasovSolutionOn gradW g T_0 := hg_lag.1
  refine ⟨f_next, charX_next, charV_next, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Conjunct (i): agreement on [0, T]
    intro t ht
    simp only [f_next]
    have ht_le : t ≤ T := ht.2
    simp [ht_le]
  · -- Conjunct (ii): initial condition f_next 0 = f₀
    simp only [f_next]
    have h0_le : (0 : ℝ) ≤ T := hT_pos.le
    simp [h0_le, h_prev_init]
  · -- Conjunct (iii): HasFiniteFirstMoment on [0, T + T_0] (hoisted helper)
    exact vlasovGlue_moment f_prev g h_prev_mom hg_mom f_next
      (fun s hs => ite_eq_left hs) (fun s hs => ite_eq_right (not_le.mpr hs))
  · -- Conjunct (iii′): FLAT uniform first-moment bound (hoisted helper)
    exact vlasovGlue_moment_flat f_prev g hM_prev hg_mom_unif f_next
      (fun s hs => ite_eq_left hs) (fun s hs => ite_eq_right (not_le.mpr hs))
  · -- Conjunct (iv): IsLagrangianVlasovSolutionOn gradW f_next (T + T_0)
    refine ⟨?_, charX_next, charV_next, ?_, ?_, ?_⟩
    · -- IsVlasovSolutionOn gradW f_next (T + T_0)
      -- Sub-sorry: PDE gluing — on Ioo 0 (T + T_0), piecewise from h_prev_vlasov and h_g_vlasov
      -- Sub-sorry (a): IsVlasovSolutionOn for the glued solution.
      -- Strategy: for t ∈ Ioo 0 T use h_prev_vlasov (with f_next = f_prev near t);
      -- for t ∈ Ioo T (T+T_0) use h_g_vlasov shifted (f_next t = g (t-T));
      -- at t = T use continuity of t ↦ ∫ φ ∂f_next t from both sides.
      have h_vlasov_glue : IsVlasovSolutionOn gradW f_next (T + T_0) := by
        intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ t ht
        -- Off-seam weak PDE at every t' ≠ T (hoisted helper); the two strict
        -- branches consume it directly, the seam derives its eventual form.
        have h_diff_ne := vlasovGlue_diff_ne gradW f_prev g
          h_prev_vlasov h_g_vlasov f_next (fun s hs => ite_eq_left hs)
          (fun s hs => ite_eq_right (not_le.mpr hs)) φ hφ_smooth hφ_compact
          gradXφ gradVφ hgradXφ hgradVφ
        by_cases ht_lt : t < T
        · -- t ∈ Ioo 0 T: off-seam weak PDE
          rw [show (fun _ => (0 : ℝ)) t = 0 from rfl]
          exact h_diff_ne t ht (ne_of_lt ht_lt)
        · by_cases ht_gt : T < t
          · -- t ∈ Ioo T (T + T_0): off-seam weak PDE
            rw [show (fun _ => (0 : ℝ)) t = 0 from rfl]
            exact h_diff_ne t ht (ne_of_gt ht_gt)
          · -- t = T: boundary case via `hasDerivAt_of_hasDerivAt_of_ne_in_nhds`.
            -- Three sub-arguments: (1) HasDerivAt at every nearby t' ≠ T from the
            -- off-seam helper; (2) ContinuousAt of the integral function at T;
            -- (3) ContinuousAt of the derivative function at T.
            push Not at ht_gt
            have h_t_eq : t = T := le_antisymm ht_gt (not_lt.mp ht_lt)
            -- Step 1: HasDerivAt at every nearby t' ≠ T, in eventual form.
            have h_diff_ne_ev : ∀ᶠ t' in nhds T, t' ≠ T → HasDerivAt
                (fun s => ∫ z, φ z ∂f_next s)
                ((∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                        @inner ℝ (PhysSpace d) _
                          (convolveFunctionMeasure gradW (spatialMarginal (f_next t')) z.1)
                          (gradVφ z)) ∂(f_next t')) + 0) t' := by
              have hU_mem : Set.Ioo (0 : ℝ) (T + T_0) ∈ nhds T :=
                Ioo_mem_nhds hT_pos (by linarith)
              exact Filter.Eventually.mono hU_mem (fun t' ht' => h_diff_ne t' ht')
            -- Step 2: ContinuousAt of integral function at T.
            -- Decomposed into LEFT (Iic T) + RIGHT (Ici T) closes, joined via
            -- `Iic_union_Ici = univ`.
            have hφ_cont : Continuous φ := hφ_smooth.continuous
            obtain ⟨Cφ, hCφ⟩ := hφ_cont.bounded_above_of_compact_support hφ_compact
            obtain ⟨hf₀_prob, hf₀_int⟩ := hf₀
            have : IsProbabilityMeasure f₀ := hf₀_prob
            -- LEFT side: substantive close via DCT on f_prev's pushforward.
            have h_cont_f_left : ContinuousWithinAt (fun s => ∫ z, φ z ∂f_next s)
                (Set.Iic T) T :=
              vlasovGlue_intCont_left gradW f₀ hT_pos f_prev h_prev_init
                charX_prev charV_prev h_prev_push h_prev_aemeas h_prev_boundary
                f_next (fun s hs => ite_eq_left hs) φ hφ_cont Cφ hCφ
            -- RIGHT side: substantive close via DCT on the composed pushforward
            -- (charX_g (s-T), charV_g (s-T)) ∘ (charX_prev T, charV_prev T).
            -- At s = T, hg_init_cond bridges (charX_g 0, charV_g 0) = id, matching f_prev T.
            have h_cont_f_right : ContinuousWithinAt (fun s => ∫ z, φ z ∂f_next s)
                (Set.Ici T) T :=
              vlasovGlue_intCont_right gradW f₀ hT_pos hT_0_pos f_prev h_prev_init
                charX_prev charV_prev h_prev_push h_prev_aemeas g charX_g charV_g
                hg_init hg_push_ex hg_aemeas_ex hg_boundary hg_init_cond
                f_next (ite_eq_left (le_refl T)) (fun s hs => ite_eq_right (not_le.mpr hs))
                φ hφ_cont Cφ hCφ
            -- Combine via union
            have h_cont_f : ContinuousAt (fun s => ∫ z, φ z ∂f_next s) T := by
              have h_union := h_cont_f_left.union h_cont_f_right
              rw [Set.Iic_union_Ici] at h_union
              exact h_union.continuousAt Filter.univ_mem
            -- Step 3: ContinuousAt of the derivative functional at the seam T.
            -- Mirror `h_cont_f`'s one-sided-union structure (Iic/Ici +
            -- `Set.Iic_union_Ici`).  Each side discharges by push-to-f₀ +
            -- DCT; the integrand's force term carries
            -- `convolveFunctionMeasure gradW (spatialMarginal (f_next ·)) z.1`, whose
            -- seam continuity closes from PROVEN TOOLS via the pushforward
            -- representation: `f_prev`/`g` are flow-pushforwards of `f₀`, so the
            -- convolution rewrites by `integral_map` to a fixed-`f₀` integral, closed
            -- by the inner kernels `flowConv_continuousWithinAt_{Iic,Ici}_seam`
            -- (Piece-A-dominated DCT).  LEFT uses `spatialMarginal (f_prev ·)`,
            -- RIGHT the composed flow off `g`.
            have h_cont_g : ContinuousAt (fun t' =>
                (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                        @inner ℝ (PhysSpace d) _
                          (convolveFunctionMeasure gradW (spatialMarginal (f_next t')) z.1)
                          (gradVφ z)) ∂(f_next t')) + 0) T := by
              simp only [add_zero]
              -- LEFT side (s ≤ T): f_next = f_prev = pushforward of f₀; force term
              -- uses `spatialMarginal (f_prev ·)`.  Discharge: push-to-f₀ + DCT.
              have h_left : ContinuousWithinAt
                  (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                          @inner ℝ (PhysSpace d) _
                            (convolveFunctionMeasure gradW (spatialMarginal (f_next s)) z.1)
                            (gradVφ z)) ∂(f_next s)) (Set.Iic T) T :=
                vlasovGlue_seam_contLeft gradW L hL f₀ hf₀_int hT_pos f_prev h_prev_init
                  h_prev_mom hM_prev charX_prev charV_prev h_prev_push h_prev_aemeas
                  h_prev_boundary h_prev_ic f_next (fun s hs => ite_eq_left hs)
                  φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ
              -- RIGHT side (s ≥ T): f_next = g (·−T) = composed pushforward; symmetric
              -- to `h_left`.  The flow is the COMPOSED phase-space flow
              -- `Φ_s z = (charX_g (s−T) (charX_prev T z, charV_prev T z),
              --           charV_g (s−T) (charX_prev T z, charV_prev T z))`, and the
              -- position part `Z_s z = charX_g (s−T) (charX_prev T z, charV_prev T z)`
              -- is what the force-term convolution sees.  Pushforward, AEMeasurability,
              -- and seam continuity are copied/adapted from the PROVEN
              -- `h_cont_f_right` (composed-pushforward machinery); the growth bound is
              -- the composed Piece A (g over [0,T_0] ∘ prev at T); the force-term seam
              -- continuity uses the `Ici` sibling kernel `flowConv_continuousWithinAt_Ici_seam`.
              have h_right : ContinuousWithinAt
                  (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                          @inner ℝ (PhysSpace d) _
                            (convolveFunctionMeasure gradW (spatialMarginal (f_next s)) z.1)
                            (gradVφ z)) ∂(f_next s)) (Set.Ici T) T :=
                vlasovGlue_seam_contRight gradW L hL f₀ hf₀_int hT_pos hT_0_pos
                  f_prev h_prev_init h_prev_mom hM_prev charX_prev charV_prev
                  h_prev_push h_prev_aemeas h_prev_boundary h_prev_ic
                  g charX_g charV_g hg_init hg_mom hg_mom_unif hg_push_ex
                  hg_aemeas_ex hg_boundary hg_init_cond f_next
                  (ite_eq_left (le_refl T)) (fun s hs => ite_eq_right (not_le.mpr hs))
                  φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ
              have h_union := h_left.union h_right
              rw [Set.Iic_union_Ici] at h_union
              exact h_union.continuousAt Filter.univ_mem
            -- Step 4: Apply the localized helper.
            rw [h_t_eq]
            exact hasDerivAt_of_hasDerivAt_of_ne_in_nhds h_diff_ne_ev h_cont_f h_cont_g
      exact h_vlasov_glue
    · -- IsCharacteristicFlowOn for the glued flow
      -- Sub-sorry: flow initial condition + HasDerivAt for piecewise flow
      have h_flow_glue : IsCharacteristicFlowOn gradW
          (fun t => spatialMarginal (f_next t)) charX_next charV_next
          (Set.Ioo 0 (T + T_0)) Set.univ := by
        refine ⟨?_, ?_, ?_⟩
        · -- Initial condition: charX_next 0 z = z.1 ∧ charV_next 0 z = z.2
          intro z _
          simp only [charX_next, charV_next, ite_eq_left hT_pos.le]
          exact h_prev_flow.1 z (Set.mem_univ z)
        · -- HasDerivAt charX_next at t for t ∈ Ioo 0 (T + T_0) (hoisted helper)
          intro t ht z _
          simp only [charX_next, charV_next]
          exact vlasovGlue_flowX_hasDerivAt charX_prev charV_prev charX_g charV_g
            hT_pos hT_0_pos
            (fun t' ht' z' => h_prev_flow.2.1 t' ht' z' (Set.mem_univ z'))
            (fun z' t' ht' => (h_prev_boundary z' t' ht').1)
            (fun z' t' ht' => (hg_boundary z' t' ht').1)
            hg_init_cond t ht z
        · -- HasDerivAt charV_next at t for t ∈ Ioo 0 (T + T_0) (hoisted helper)
          intro t ht z _
          simp only [charX_next, charV_next]
          exact vlasovGlue_flowV_hasDerivAt gradW f_prev g charX_prev charV_prev
            charX_g charV_g hT_pos hT_0_pos
            (fun t' ht' z' => h_prev_flow.2.2 t' ht' z' (Set.mem_univ z'))
            (fun z' t' ht' => (h_prev_boundary z' t' ht').2)
            (fun z' t' ht' => (hg_boundary z' t' ht').2)
            hg_init hg_init_cond f_next (fun s hs => ite_eq_left hs)
            (fun s hs => ite_eq_right (not_le.mpr hs)) t ht z
      exact h_flow_glue
    · -- Pushforward equation for f_next on Icc 0 (T + T_0) (hoisted helper)
      intro t ht
      simp only [charX_next, charV_next]
      exact vlasovGlue_pushforward_eq f_prev g charX_prev charV_prev charX_g charV_g
        hT_pos h_prev_push h_prev_aemeas hg_init hg_push_ex hg_aemeas_ex f_next
        (fun s hs => ite_eq_left hs) (fun s hs => ite_eq_right (not_le.mpr hs)) t ht
    · -- AEMeasurability ∧ boundary ContinuousOn on Icc 0 (T + T_0).
      refine ⟨?_, ?_⟩
      · -- AEMeasurability of the glued flow (hoisted helper).
        intro s hs
        simp only [charX_next, charV_next]
        exact vlasovGlue_flow_aemeasurable f_prev g charX_prev charV_prev
          charX_g charV_g hT_pos h_prev_push h_prev_aemeas hg_init hg_aemeas_ex
          f_next (fun s' hs' => ite_eq_left hs') s hs
      · -- Boundary ContinuousOn on Icc 0 (T + T_0): project the boundary bundle.
        intro z s hs
        exact ((vlasovWellPosedness_glue_boundary gradW hT_pos hT_0_pos f_prev g f_next
          charX_prev charV_prev charX_g charV_g charX_next charV_next rfl rfl rfl
          h_prev_boundary hg_boundary hg_init hg_init_cond z s hs).1.continuousWithinAt.prodMk
          (vlasovWellPosedness_glue_boundary gradW hT_pos hT_0_pos f_prev g f_next
            charX_prev charV_prev charX_g charV_g charX_next charV_next rfl rfl rfl
            h_prev_boundary hg_boundary hg_init hg_init_cond z s hs).2.continuousWithinAt)
  · -- Conjunct (v): explicit pushforward for charX_next charV_next (hoisted helper)
    intro t ht
    simp only [charX_next, charV_next]
    exact vlasovGlue_pushforward_eq f_prev g charX_prev charV_prev charX_g charV_g
      hT_pos h_prev_push h_prev_aemeas hg_init hg_push_ex hg_aemeas_ex f_next
      (fun s hs => ite_eq_left hs) (fun s hs => ite_eq_right (not_le.mpr hs)) t ht
  · -- Conjunct (vi): AEMeasurable for charX_next charV_next (hoisted helper)
    intro s hs
    simp only [charX_next, charV_next]
    exact vlasovGlue_flow_aemeasurable f_prev g charX_prev charV_prev
      charX_g charV_g hT_pos h_prev_push h_prev_aemeas hg_init hg_aemeas_ex
      f_next (fun s' hs' => ite_eq_left hs') s hs
  · -- Conjunct (vii): boundary bundle for charX_next charV_next on Icc 0 (T + T_0)
    exact vlasovWellPosedness_glue_boundary gradW hT_pos hT_0_pos f_prev g f_next
      charX_prev charV_prev charX_g charV_g charX_next charV_next rfl rfl rfl
      h_prev_boundary hg_boundary hg_init hg_init_cond
  · -- Conjunct (viii): initial condition for charX_next charV_next
    intro z
    simp only [charX_next, charV_next, ite_eq_left hT_pos.le]
    exact h_prev_ic z

/-- For every positive Lipschitz constant there is a window length satisfying all
three per-window smallness constraints — the PL buffer, the contraction, and the
envelope closure.  Pure threshold arithmetic: `T_0 := min(1/√L, T_0_con, T_0_env)/2`
with each threshold positive for every `L > 0` (no `L < 1` restriction). -/
lemma exists_localSmallness_window (L : NNReal) (hL_pos : (0 : ℝ) < L) :
    ∃ T_0 : ℝ, 0 < T_0 ∧ LocalSmallnessPLBuffer L T_0 ∧ LocalSmallnessContraction L T_0 ∧
      (L : ℝ) / (1 + (L : ℝ)) * (Real.exp ((1 + (L : ℝ)) * T_0) - 1) < 1 := by
  let T_0_PL : ℝ := 1 / Real.sqrt L
  let T_0_con : ℝ := Real.log (max 1 (L : ℝ) / (L : ℝ) + 1) / max 1 (L : ℝ)
  let T_0_env : ℝ := Real.log (1 + (1 + (L : ℝ)) / (L : ℝ)) / (1 + (L : ℝ))
  let T_0 : ℝ := min (min T_0_PL T_0_con) T_0_env / 2
  have hL_nn : (0 : ℝ) ≤ L := NNReal.coe_nonneg L
  have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt hL_pos
  have hsqrtL_pos : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.mpr hL_pos
  have hs_eq : (Real.sqrt (L : ℝ)) ^ 2 = (L : ℝ) := Real.sq_sqrt hL_nn
  have hK_pos : (0 : ℝ) < max 1 (L : ℝ) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hT_0_PL_pos : 0 < T_0_PL := by
    change 0 < 1 / Real.sqrt (L : ℝ); positivity
  have hKL_gt1 : 1 < max 1 (L : ℝ) / (L : ℝ) + 1 := by
    have : 0 < max 1 (L : ℝ) / (L : ℝ) := div_pos hK_pos hL_pos
    linarith
  have hT_0_con_pos : 0 < T_0_con :=
    div_pos (Real.log_pos hKL_gt1) hK_pos
  have h_1L_pos : (0 : ℝ) < 1 + (L : ℝ) := by linarith [hL_pos]
  have hT_0_env_pos : 0 < T_0_env := by
    change 0 < Real.log (1 + (1 + (L : ℝ)) / (L : ℝ)) / (1 + (L : ℝ))
    have h_arg_gt1 : 1 < 1 + (1 + (L : ℝ)) / (L : ℝ) := by
      have : 0 < (1 + (L : ℝ)) / (L : ℝ) := by positivity
      linarith
    exact div_pos (Real.log_pos h_arg_gt1) h_1L_pos
  have hT_0_min_pos : 0 < min (min T_0_PL T_0_con) T_0_env :=
    lt_min (lt_min hT_0_PL_pos hT_0_con_pos) hT_0_env_pos
  have hT0_pos : 0 < T_0 := by
    change 0 < min (min T_0_PL T_0_con) T_0_env / 2; linarith
  have hTL_T0_PL : LocalSmallnessPLBuffer L T_0 := by
    change (L : ℝ) * T_0 ^ 2 < 1
    have h_T_0_le : T_0 ≤ 1 / (2 * Real.sqrt (L : ℝ)) := by
      change min (min T_0_PL T_0_con) T_0_env / 2 ≤ 1 / (2 * Real.sqrt (L : ℝ))
      have h_min_le : min (min T_0_PL T_0_con) T_0_env ≤ T_0_PL :=
        le_trans (min_le_left _ _) (min_le_left _ _)
      have hrw : (1 : ℝ) / (2 * Real.sqrt (L : ℝ)) = (1 / Real.sqrt (L : ℝ)) / 2 := by
        rw [div_div, mul_comm (2 : ℝ) (Real.sqrt (L : ℝ))]
      rw [hrw]
      have hTPL : T_0_PL = 1 / Real.sqrt (L : ℝ) := rfl
      rw [hTPL] at h_min_le; linarith
    have h_T_0_nn : 0 ≤ T_0 := le_of_lt hT0_pos
    have h_sq_le : T_0 ^ 2 ≤ (1 / (2 * Real.sqrt (L : ℝ))) ^ 2 :=
      pow_le_pow_left₀ h_T_0_nn h_T_0_le 2
    have h_mul_le : (L : ℝ) * T_0 ^ 2 ≤ (L : ℝ) * (1 / (2 * Real.sqrt (L : ℝ))) ^ 2 :=
      mul_le_mul_of_nonneg_left h_sq_le hL_nn
    have h_eq : (L : ℝ) * (1 / (2 * Real.sqrt (L : ℝ))) ^ 2 = 1 / 4 := by
      rw [div_pow, one_pow, mul_pow, hs_eq]; field_simp; ring
    rw [h_eq] at h_mul_le; linarith
  have hTL_T0_con : LocalSmallnessContraction L T_0 := by
    change (L : ℝ) * (Real.exp ((max 1 (L : ℝ)) * T_0) - 1) / (max 1 (L : ℝ)) < 1
    set K : ℝ := max 1 (L : ℝ) with hK_def
    have h_T_0_lt : T_0 < T_0_con := by
      change min (min T_0_PL T_0_con) T_0_env / 2 < T_0_con
      have h_min_le : min (min T_0_PL T_0_con) T_0_env ≤ T_0_con :=
        le_trans (min_le_left _ _) (min_le_right _ _)
      linarith
    have hKL1_pos : (0 : ℝ) < K / (L : ℝ) + 1 := by
      have : 0 < K / (L : ℝ) := div_pos hK_pos hL_pos
      linarith
    have h_KT0_lt : K * T_0 < Real.log (K / (L : ℝ) + 1) := by
      have hTcon : T_0_con = Real.log (K / (L : ℝ) + 1) / K := rfl
      rw [hTcon] at h_T_0_lt
      have hh := (lt_div_iff₀ hK_pos).mp h_T_0_lt
      nlinarith [hh]
    have h_exp_lt : Real.exp (K * T_0) < K / (L : ℝ) + 1 := by
      have := Real.exp_lt_exp.mpr h_KT0_lt
      rwa [Real.exp_log hKL1_pos] at this
    have h_sub_lt : Real.exp (K * T_0) - 1 < K / (L : ℝ) := by linarith
    have h_num_lt : (L : ℝ) * (Real.exp (K * T_0) - 1) < K := by
      have := mul_lt_mul_of_pos_left h_sub_lt hL_pos
      rwa [mul_div_cancel₀ _ hL_ne] at this
    rw [div_lt_one hK_pos]
    exact h_num_lt
  have hTL_T0_B :
      (L : ℝ) / (1 + (L : ℝ)) * (Real.exp ((1 + (L : ℝ)) * T_0) - 1) < 1 := by
    have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt hL_pos
    have h_1L_ne : (1 + (L : ℝ)) ≠ 0 := ne_of_gt h_1L_pos
    have h_ratio_pos : (0 : ℝ) < (1 + (L : ℝ)) / (L : ℝ) := div_pos h_1L_pos hL_pos
    have h_arg_pos : (0 : ℝ) < 1 + (1 + (L : ℝ)) / (L : ℝ) := by linarith
    have h_T_0_lt_env : T_0 < T_0_env := by
      change min (min T_0_PL T_0_con) T_0_env / 2 < T_0_env
      have h_min_le : min (min T_0_PL T_0_con) T_0_env ≤ T_0_env := min_le_right _ _
      linarith
    have h_lin_lt : (1 + (L : ℝ)) * T_0
        < Real.log (1 + (1 + (L : ℝ)) / (L : ℝ)) := by
      have h_env_eq : (1 + (L : ℝ)) * T_0_env
          = Real.log (1 + (1 + (L : ℝ)) / (L : ℝ)) := by
        change (1 + (L : ℝ)) *
            (Real.log (1 + (1 + (L : ℝ)) / (L : ℝ)) / (1 + (L : ℝ)))
          = Real.log (1 + (1 + (L : ℝ)) / (L : ℝ))
        field_simp
      calc (1 + (L : ℝ)) * T_0
          < (1 + (L : ℝ)) * T_0_env := mul_lt_mul_of_pos_left h_T_0_lt_env h_1L_pos
        _ = Real.log (1 + (1 + (L : ℝ)) / (L : ℝ)) := h_env_eq
    have h_exp_lt : Real.exp ((1 + (L : ℝ)) * T_0)
        < 1 + (1 + (L : ℝ)) / (L : ℝ) := by
      calc Real.exp ((1 + (L : ℝ)) * T_0)
          < Real.exp (Real.log (1 + (1 + (L : ℝ)) / (L : ℝ))) :=
            Real.exp_lt_exp.mpr h_lin_lt
        _ = 1 + (1 + (L : ℝ)) / (L : ℝ) := Real.exp_log h_arg_pos
    have h_diff_lt : Real.exp ((1 + (L : ℝ)) * T_0) - 1 < (1 + (L : ℝ)) / (L : ℝ) := by
      linarith
    have hcoef_pos : (0 : ℝ) < (L : ℝ) / (1 + (L : ℝ)) := div_pos hL_pos h_1L_pos
    calc (L : ℝ) / (1 + (L : ℝ)) * (Real.exp ((1 + (L : ℝ)) * T_0) - 1)
        < (L : ℝ) / (1 + (L : ℝ)) * ((1 + (L : ℝ)) / (L : ℝ)) :=
          mul_lt_mul_of_pos_left h_diff_lt hcoef_pos
      _ = 1 := by field_simp
  exact ⟨T_0, hT0_pos, hTL_T0_PL, hTL_T0_con, hTL_T0_B⟩

/-- **Forward iteration to arbitrary `T_target`.**

Extends the local-existence theorem from its small-`T` smallness window
to any `T_target > 0`, by iterating the local theorem with shifted initial
data at a fixed step `T_0` depending only on `L` (no `L < 1` hypothesis).

**Proof strategy**:

1. Pick `T_0 := min(T_0_PL, T_0_con, T_0_env) / 2`, with `T_0_PL := 1/√L`
   (the PL-buffer threshold for `L · T_0² < 1`), `T_0_con`/`T_0_env` the
   contraction/envelope thresholds.  Each is positive for every `L > 0`, so
   `T_0 > 0` and all three smallness constraints hold.

2. Pick `N := ⌈T_target / T_0⌉₊` so that `N · T_0 ≥ T_target`.

3. `Nat.rec` construction: a solution holding the conjuncts at `T = n·T_0`.
   - Base case: apply `vlasovWellPosedness_local` directly.
   - Step case (`n → n+1`): apply `vlasovWellPosedness_glue` to extend.

4. Take `f := f_N` and verify the conjuncts for `T_target ≤ N · T_0` via
   `IsLagrangianVlasovSolutionOn`'s monotonicity in `T` (project down). -/
theorem vlasovWellPosedness_forward
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (hL_pos : (0 : ℝ) < L)
    (f₀ : Measure (PhaseSpace d))
    (hf₀ : HasFiniteFirstMoment f₀)
    {T_target : ℝ} (hT_target : 0 < T_target) :
    ∃ f : ℝ → Measure (PhaseSpace d),
      f 0 = f₀ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T_target, HasFiniteFirstMoment (f t)) ∧
      IsLagrangianVlasovSolutionOn gradW f T_target := by
  -- T_0 must satisfy the PL-buffer, contraction, and envelope constraints —
  -- all supplied by the pure-arithmetic `exists_localSmallness_window`.
  obtain ⟨T_0, hT0_pos, hTL_T0_PL, hTL_T0_con, hTL_T0_B⟩ :=
    exists_localSmallness_window L hL_pos
  -- Step 2: N = ⌈T_target / T_0⌉₊ windows of size T_0 cover T_target.
  let N : ℕ := ⌈T_target / T_0⌉₊
  have hN_pos : 0 < N := by
    change 0 < ⌈T_target / T_0⌉₊
    rw [Nat.ceil_pos]
    exact div_pos hT_target hT0_pos
  have hN_covers : T_target ≤ (N : ℝ) * T_0 := by
    have hle := Nat.le_ceil (T_target / T_0)
    have hT0_pos' := hT0_pos
    calc T_target = T_target / T_0 * T_0 := by field_simp
         _ ≤ (⌈T_target / T_0⌉₊ : ℝ) * T_0 :=
              mul_le_mul_of_nonneg_right hle (le_of_lt hT0_pos)
  -- Step 3: Induction on n : ℕ — solution exists on [0, (n+1)·T_0].
  -- The induction carries explicit flow witnesses (charX, charV) and the full
  -- 7-component bundle to enable vlasovWellPosedness_glue calls without witness-identity issues.
  let T_n := fun n : ℕ => ((n + 1 : ℕ) : ℝ) * T_0
  have h_ind : ∀ n : ℕ,
      ∃ (f : ℝ → Measure (PhaseSpace d))
        (charX charV : ℝ → PhaseSpace d → PhysSpace d),
        f 0 = f₀ ∧
        (∀ t ∈ Set.Icc (0 : ℝ) (T_n n), HasFiniteFirstMoment (f t)) ∧
        -- FLAT (window-constant) uniform first-moment bound on the spatial marginal.
        (∃ M : ℝ, 0 ≤ M ∧
          ∀ t ∈ Set.Icc (0 : ℝ) (T_n n), ∫ y, ‖y‖ ∂(spatialMarginal (f t)) ≤ M) ∧
        IsVlasovSolutionOn gradW f (T_n n) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) (T_n n),
            f t = Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) (f 0)) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) (T_n n),
            AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) (f 0)) ∧
        (∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) (T_n n) →
            HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 (T_n n)) t ∧
            HasDerivWithinAt (fun s => charV s z)
              (-(convolveFunctionMeasure gradW (spatialMarginal (f t)) (charX t z)))
              (Set.Icc 0 (T_n n)) t) ∧
        (∀ z : PhaseSpace d, charX 0 z = z.1 ∧ charV 0 z = z.2) := by
    intro n
    induction n with
    | zero =>
      -- Base: n = 0, need solution on [0, 1·T_0] = [0, T_0].
      simp only [T_n, zero_add, Nat.cast_one, one_mul]
      obtain ⟨f, charX, charV, hf_init, hf_mom, hf_mom_unif, hf_lag, hf_push, hf_aemeas,
        hf_boundary, hf_ic⟩ :=
        vlasovWellPosedness_local W gradW hgradW L hL f₀ hf₀ hT0_pos hTL_T0_PL hTL_T0_con hTL_T0_B
      exact ⟨f, charX, charV, hf_init, hf_mom, hf_mom_unif, hf_lag.1, hf_push, hf_aemeas,
        hf_boundary, hf_ic⟩
    | succ n ih =>
      -- Step: n+1 → (n+2)·T_0.  Use vlasovWellPosedness_glue with T = (n+1)·T_0 > 0.
      obtain ⟨f_n, charX_n, charV_n, hfn_init, hfn_mom, hfn_mom_unif, hfn_vlasov,
              hfn_push, hfn_aemeas, hfn_boundary, hfn_ic⟩ := ih
      simp only [T_n] at hfn_mom hfn_mom_unif hfn_vlasov hfn_push hfn_aemeas hfn_boundary
      have hT_n_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) * T_0 :=
        mul_pos (by exact_mod_cast Nat.succ_pos n) hT0_pos
      -- Derive IsCharacteristicFlowOn from h_prev_boundary + hasDerivAt
      -- (interior points t ∈ Ioo 0 T_n have Icc 0 T_n ∈ 𝓝 t, so HasDerivWithinAt → HasDerivAt)
      have hfn_flow : IsCharacteristicFlowOn gradW (fun t => spatialMarginal (f_n t))
          charX_n charV_n (Set.Ioo 0 (((n + 1 : ℕ) : ℝ) * T_0)) Set.univ := by
        refine ⟨fun z _ => hfn_ic z, ?_, ?_⟩
        · intro t ht z _
          exact ((hfn_boundary z t (Set.Ioo_subset_Icc_self ht)).1).hasDerivAt
            (Icc_mem_nhds ht.1 ht.2)
        · intro t ht z _
          exact ((hfn_boundary z t (Set.Ioo_subset_Icc_self ht)).2).hasDerivAt
            (Icc_mem_nhds ht.1 ht.2)
      obtain ⟨f_next, charX_next, charV_next, _h_agree, h_init, h_mom, h_mom_unif, h_lag,
              h_push, h_aemeas, h_boundary, h_ic⟩ :=
        vlasovWellPosedness_glue W gradW hgradW L hL f₀ hf₀ hT_n_pos
          f_n hfn_init hfn_mom hfn_mom_unif
          charX_n charV_n hfn_vlasov hfn_flow
          hfn_push hfn_aemeas hfn_boundary hfn_ic
          hT0_pos hTL_T0_PL hTL_T0_con hTL_T0_B
      -- Need: T_n (n+1) = T_n n + T_0
      have h_T_eq : T_n (n + 1) = T_n n + T_0 := by
        simp only [T_n]; push_cast; ring
      refine ⟨f_next, charX_next, charV_next, h_init, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h_T_eq]; exact h_mom
      · rw [h_T_eq]; exact h_mom_unif
      · rw [h_T_eq]; exact h_lag.1
      · rw [h_T_eq]; exact h_push
      · rw [h_T_eq]; exact h_aemeas
      · rw [h_T_eq]; exact h_boundary
      · exact h_ic
  -- Step 4: Apply h_ind at n = N - 1 (since N ≥ 1).
  have hN_pred : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos hN_pos
  obtain ⟨f, charX_f, charV_f, hf_init, hf_mom, _hf_mom_unif, hf_vlasov,
          hf_push, hf_aemeas, hf_boundary, hf_ic⟩ := h_ind (N - 1)
  simp only [T_n] at hf_mom hf_vlasov hf_push hf_aemeas hf_boundary
  rw [hN_pred] at hf_mom hf_vlasov hf_push hf_aemeas hf_boundary
  -- Step 5: Restrict from [0, N·T_0] down to [0, T_target].
  refine ⟨f, hf_init, ?_, ?_⟩
  · -- Moment bound on [0, T_target] ⊆ [0, N·T_0].
    intro t ht
    exact hf_mom t ⟨ht.1, le_trans ht.2 hN_covers⟩
  · -- IsLagrangianVlasovSolutionOn on [0, T_target] ≤ [0, N·T_0].
    -- Derive IsCharacteristicFlowOn for T_target from hf_boundary (restrict to Ioo 0 T_target).
    have hf_flow : IsCharacteristicFlowOn gradW (fun t => spatialMarginal (f t))
        charX_f charV_f (Set.Ioo 0 T_target) Set.univ := by
      refine ⟨fun z _ => hf_ic z, ?_, ?_⟩
      · intro t ht z _
        have ht_lt_NT0 : t < (N : ℝ) * T_0 := lt_of_lt_of_le ht.2 hN_covers
        exact ((hf_boundary z t ⟨le_of_lt ht.1, le_of_lt ht_lt_NT0⟩).1).hasDerivAt
          (Icc_mem_nhds ht.1 ht_lt_NT0)
      · intro t ht z _
        have ht_lt_NT0 : t < (N : ℝ) * T_0 := lt_of_lt_of_le ht.2 hN_covers
        exact ((hf_boundary z t ⟨le_of_lt ht.1, le_of_lt ht_lt_NT0⟩).2).hasDerivAt
          (Icc_mem_nhds ht.1 ht_lt_NT0)
    refine ⟨?_, charX_f, charV_f, ?_, ?_, ?_⟩
    · -- IsVlasovSolutionOn: restrict Ioo 0 T_target ⊆ Ioo 0 (N·T_0)
      intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ t ht
      exact hf_vlasov φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ t
        ⟨ht.1, lt_of_lt_of_le ht.2 hN_covers⟩
    · exact hf_flow
    · -- pushforward eq: restrict Icc 0 T_target ⊆ Icc 0 (N·T_0)
      intro t ht
      exact hf_push t ⟨ht.1, le_trans ht.2 hN_covers⟩
    · -- AEMeasurable ∧ boundary ContinuousOn, restricted to Icc 0 T_target.
      refine ⟨?_, ?_⟩
      · intro s hs
        exact hf_aemeas s ⟨hs.1, le_trans hs.2 hN_covers⟩
      · intro z
        have h_big : ContinuousOn (fun s => (charX_f s z, charV_f s z))
            (Set.Icc 0 ((N : ℝ) * T_0)) := fun t ht =>
          ((hf_boundary z t ht).1.continuousWithinAt).prodMk
            ((hf_boundary z t ht).2.continuousWithinAt)
        exact h_big.mono (fun t ht => ⟨ht.1, le_trans ht.2 hN_covers⟩)

end Vlasov
