/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitSliceBounds
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitRepresentativeExtension
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitClausesWeak

/-!
# The terminal slice of the blow-up sequence

Clause (e) of `prop:blowup-limit` at the level of the rescaled sequence: the
terminal slices `v^k(·, 0)`, built from the `L³(B_{3/4})` class of
`lem:weak-cont-L3` at the base time, tend to zero in `L²` of every compact
set, so they converge weakly in `L²_loc` to the zero slice.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Convergence to zero in `L²` of every unit ball gives convergence to zero
in `L²` of every compact set. -/
theorem blowupLimitClauses_tendsto_zero_of_unit_balls
    (f : ℕ → Vec3 → Vec3) (hfm : ∀ k, AEStronglyMeasurable (f k) volume)
    (hf : ∀ c : Vec3, Tendsto (fun k => eLpNorm (f k) 2 (volume.restrict (vec3Ball c 1)))
      atTop (𝓝 0))
    {C : Set Vec3} (hC : IsCompact C) :
    Tendsto (fun k => eLpNorm (f k) 2 (volume.restrict C)) atTop (𝓝 0) := by
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun c : Vec3 => vec3Ball c 1)
    (fun c => isOpen_vec3Ball c 1) (by
      intro x _
      refine mem_iUnion.2 ⟨x, ?_⟩
      rw [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero]
      norm_num)
  have hbound : ∀ k, eLpNorm (f k) 2 (volume.restrict C) ≤
      ∑ c ∈ t, eLpNorm (f k) 2 (volume.restrict (vec3Ball c 1)) := by
    intro k
    have hind : eLpNorm (f k) 2 (volume.restrict C) =
        eLpNorm (C.indicator (f k)) 2 volume :=
      (eLpNorm_indicator_eq_eLpNorm_restrict hC.measurableSet).symm
    rw [hind]
    calc
      eLpNorm (C.indicator (f k)) 2 volume ≤
          eLpNorm (fun x => ∑ c ∈ t, (fun y => ‖(vec3Ball c 1).indicator (f k) y‖) x)
            2 volume := by
        refine eLpNorm_mono_real ((hfm k).indicator hC.measurableSet) ?_
        intro x
        by_cases hx : x ∈ C
        · rw [Set.indicator_of_mem hx]
          obtain ⟨c, hc, hxc⟩ : ∃ c ∈ t, x ∈ vec3Ball c 1 := by
            have := ht hx
            simpa only [mem_iUnion, exists_prop] using this
          have hle : ‖(vec3Ball c 1).indicator (f k) x‖ ≤
              ∑ c ∈ t, ‖(vec3Ball c 1).indicator (f k) x‖ :=
            Finset.single_le_sum (f := fun c => ‖(vec3Ball c 1).indicator (f k) x‖)
              (fun _ _ => norm_nonneg _) hc
          rw [Set.indicator_of_mem hxc] at hle
          exact hle
        · rw [Set.indicator_of_notMem hx, norm_zero]
          exact Finset.sum_nonneg fun _ _ => norm_nonneg _
      _ ≤ ∑ c ∈ t, eLpNorm (fun y => ‖(vec3Ball c 1).indicator (f k) y‖) 2 volume := by
        have h := eLpNorm_sum_le (μ := volume) (p := 2) (s := t)
          (f := fun c => fun y => ‖(vec3Ball c 1).indicator (f k) y‖) (by norm_num)
        convert h using 2
        funext x
        simp only [Finset.sum_apply]
      _ = ∑ c ∈ t, eLpNorm (f k) 2 (volume.restrict (vec3Ball c 1)) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [eLpNorm_norm _ ((hfm k).indicator (isOpen_vec3Ball c 1).measurableSet),
          eLpNorm_indicator_eq_eLpNorm_restrict (isOpen_vec3Ball c 1).measurableSet]
  have hsum : Tendsto (fun k => ∑ c ∈ t, eLpNorm (f k) 2 (volume.restrict (vec3Ball c 1)))
      atTop (𝓝 0) := by
    have h := tendsto_finsetSum t (fun c _ => hf c)
    simpa only [Finset.sum_const_zero] using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) hbound

/-- Fields tending to zero in `L²` of a set have vanishing pairings with every
square-integrable test on that set. -/
theorem blowupLimitClauses_pairing_tendsto_zero
    {C : Set Vec3} (f : ℕ → Vec3 → Vec3)
    (hfm : ∀ k, MemLp (f k) 2 (volume.restrict C))
    (hf : Tendsto (fun k => eLpNorm (f k) 2 (volume.restrict C)) atTop (𝓝 0))
    {g : Vec3 → Vec3} (hg : MemLp g 2 (volume.restrict C)) :
    Tendsto (fun k => ∫ x in C, ∑ i : Fin 3, f k x i * g x i) atTop (𝓝 0) := by
  have hcomp : ∀ i : Fin 3, Tendsto (fun k => ∫ x in C, f k x i * g x i) atTop (𝓝 0) := by
    intro i
    have hgi : MemLp (fun x => g x i) 2 (volume.restrict C) := hg.eval i
    have hfi : ∀ k, MemLp (fun x => f k x i) 2 (volume.restrict C) := fun k => (hfm k).eval i
    have hnorm : Tendsto (fun k => (eLpNorm (fun x => f k x i) 2 (volume.restrict C)).toReal)
        atTop (𝓝 0) := by
      have h0 : Tendsto (fun k => (eLpNorm (f k) 2 (volume.restrict C)).toReal) atTop (𝓝 0) := by
        have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hf
        rw [ENNReal.toReal_zero] at this
        exact this
      apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) _ h0
      intro k
      apply ENNReal.toReal_mono (hfm k).eLpNorm_ne_top
      exact eLpNorm_mono (hfi k).aestronglyMeasurable (fun x => norm_le_pi_norm (f k x) i)
    have hprod : Tendsto (fun k => (eLpNorm (fun x => f k x i) 2 (volume.restrict C)).toReal *
        (eLpNorm (fun x => g x i) 2 (volume.restrict C)).toReal) atTop (𝓝 0) := by
      simpa only [zero_mul] using hnorm.mul_const _
    apply squeeze_zero_norm _ hprod
    intro k
    rw [Real.norm_eq_abs]
    exact blowupLimitClauses_abs_integral_mul_le (hfi k) hgi
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hcomp i)
  simp only [Finset.sum_const_zero] at hsum
  refine hsum.congr fun k => ?_
  rw [integral_finsetSum]
  intro i _
  exact ((hfm k).eval i).integrable_mul (hg.eval i)

/-- The terminal slice of the rescaled trace representative is the fixed
`L³(B_{3/4})` class at the base time, rescaled. -/
theorem blowupLimitClauses_terminal_slice_eq
    (W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0) (x₀ : Vec3) (r : ℝ) (x : Vec3) :
    blowupLimitTraceRescaling W x₀ t₀ r (x, 0) =
      r • (vec3Ball (0 : Vec3) (3 / 4 : ℝ)).indicator (fun y => W (y, ⟨t₀, ht₀⟩))
        (x₀ + r • x) := by
  by_cases hx : x₀ + r • x ∈ vec3Ball (0 : Vec3) (3 / 4 : ℝ)
  · simp [blowupLimitTraceRescaling, blowupLimitTraceZeroExtension,
      parabolicTranslate, parabolicScale, hx, ht₀]
  · simp [blowupLimitTraceRescaling, blowupLimitTraceZeroExtension,
      parabolicTranslate, parabolicScale, hx]

/-- The terminal slices of the rescaled sequence tend to zero in `L²` of every
compact set, and so converge weakly in `L²_loc` to the zero slice
(`prop:blowup-limit`, clause (e)). -/
theorem blowupLimitClauses_terminal_tendsto_zero
    (W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3) (hWm : Measurable W)
    (hsource : ∀ t, MemLp ((vec3Ball (0 : Vec3) (3 / 4 : ℝ)).indicator
      (fun x => W (x, t))) 3 volume)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0) (x₀ : Vec3)
    (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0))
    {C : Set Vec3} (hC : IsCompact C) :
    Tendsto (fun k => eLpNorm (fun x => blowupLimitTraceRescaling W x₀ t₀ (r k) (x, 0)) 2
      (volume.restrict C)) atTop (𝓝 0) ∧
    ∀ g : Vec3 → Vec3, MemLp g 2 (volume.restrict C) →
      Tendsto (fun k => ∫ x in C, ∑ i : Fin 3,
        blowupLimitTraceRescaling W x₀ t₀ (r k) (x, 0) i * g x i) atTop (𝓝 0) := by
  have hunit : ∀ c : Vec3, Tendsto (fun k => eLpNorm
      (fun x => blowupLimitTraceRescaling W x₀ t₀ (r k) (x, 0)) 2
      (volume.restrict (vec3Ball c 1))) atTop (𝓝 0) := by
    intro c
    have h := blowup_limit_trace_terminal_rescaling_tendsto_zero W hsource ⟨t₀, ht₀⟩ x₀ c r
      hr hr0
    refine h.congr fun k => ?_
    congr 1
    funext x
    rw [blowupLimitClauses_terminal_slice_eq W ht₀ x₀ (r k) x]
  have hmeasAll : ∀ k, AEStronglyMeasurable
      (fun x => blowupLimitTraceRescaling W x₀ t₀ (r k) (x, 0)) volume :=
    fun k => ((measurable_blowupLimitTraceRescaling W hWm x₀ t₀ (r k)).comp
      measurable_prodMk_right).aestronglyMeasurable
  have hC0 := blowupLimitClauses_tendsto_zero_of_unit_balls
    (fun k x => blowupLimitTraceRescaling W x₀ t₀ (r k) (x, 0)) hmeasAll hunit hC
  refine ⟨hC0, fun g hg => ?_⟩
  obtain ⟨K, hK⟩ := (hC0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))).exists_forall_of_atTop
  have hmem : ∀ k, K ≤ k → MemLp (fun x => blowupLimitTraceRescaling W x₀ t₀ (r k) (x, 0)) 2
      (volume.restrict C) := fun k hk =>
    memLp_iff.2 ((hK k hk).trans ENNReal.one_lt_top)
  have hshift := blowupLimitClauses_pairing_tendsto_zero
    (fun k x => blowupLimitTraceRescaling W x₀ t₀ (r (k + K)) (x, 0))
    (fun k => hmem (k + K) (Nat.le_add_left K k))
    (hC0.comp (tendsto_add_atTop_nat K)) hg
  exact (tendsto_add_atTop_iff_nat K).1 hshift

end ESS

end
