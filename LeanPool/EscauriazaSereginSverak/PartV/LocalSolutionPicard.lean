/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Picard iteration for a quadratic map in the intersection of two Lebesgue spaces

The fixed point of `prop:pv-local-solution` is obtained by iterating the Duhamel
map from the heat orbit. We record the iteration abstractly: a map on functions
which is quadratically Lipschitz for the norm `‖·‖_p + ‖·‖_q` has a fixed point
(up to null sets) as soon as its value at the origin is small.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology


noncomputable section

namespace ESS

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]

/-- A sequence of functions whose consecutive `L^p` distances decay
geometrically has an `L^p` limit. -/
theorem picard_limit_of_geometric [CompleteSpace E] {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ℕ → α → E}
    (hf : ∀ n, MemLp (f n) p μ) {d : ℝ≥0∞} (hd : d ≠ ⊤)
    (hstep : ∀ n, 2 ^ n * eLpNorm (f (n + 1) - f n) p μ ≤ d) :
    ∃ g : α → E, MemLp g p μ ∧ Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  have : Fact (1 ≤ p) := ⟨hp⟩
  set F : ℕ → Lp E p μ := fun n => (hf n).toLp (f n)
  have hdist (n : ℕ) : dist (F n) (F (n + 1)) ≤ 2 * d.toReal / 2 / 2 ^ n := by
    rw [dist_comm, Lp.dist_def]
    have hae : ((F (n + 1) : α → E) - F n) =ᵐ[μ] f (n + 1) - f n := by
      filter_upwards [(hf (n + 1)).coeFn_toLp, (hf n).coeFn_toLp] with x h1 h2
      exact congrArg₂ (· - ·) h1 h2
    rw [eLpNorm_congr_ae hae]
    have h1 : (2 ^ n * eLpNorm (f (n + 1) - f n) p μ).toReal ≤ d.toReal :=
      ENNReal.toReal_mono hd (hstep n)
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at h1
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    rw [mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℝ) ≠ 0), le_div_iff₀ h2, mul_comm]
    exact h1
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two hdist)
  refine ⟨G, Lp.memLp G, ?_⟩
  have hG' : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 ((Lp.memLp G).toLp G)) := by
    simpa [F] using hG
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf G (Lp.memLp G)).1 hG'

/-- Limits in two Lebesgue norms of the same sequence agree almost everywhere. -/
theorem picard_limits_ae_eq {p q : ℝ≥0∞} (hp : p ≠ 0) (hq : q ≠ 0) {f : ℕ → α → E}
    {g g' : α → E} (hg : Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0))
    (hg' : Tendsto (fun n => eLpNorm (f n - g') q μ) atTop (𝓝 0)) : g =ᵐ[μ] g' :=
  tendstoInMeasure_ae_unique (tendstoInMeasure_of_tendsto_eLpNorm hp hg)
    (tendstoInMeasure_of_tendsto_eLpNorm hq hg')

/-- The Picard iteration of a quadratically Lipschitz map for the norm
`‖·‖_p + ‖·‖_q`, started from its small value at the origin, converges to a
fixed point up to null sets. -/
theorem picard_fixedPoint [CompleteSpace E] {p q : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (Φ : (α → E) → α → E) (h : α → E) {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hhp : MemLp h p μ) (hhq : MemLp h q μ)
    (hmaps : ∀ U, MemLp U p μ → MemLp U q μ → MemLp (Φ U) p μ ∧ MemLp (Φ U) q μ)
    (hlip : ∀ U V, MemLp U p μ → MemLp U q μ → MemLp V p μ → MemLp V q μ →
      eLpNorm (Φ U - Φ V) p μ + eLpNorm (Φ U - Φ V) q μ ≤
        K * (eLpNorm (U - V) p μ + eLpNorm (U - V) q μ) *
          (eLpNorm U p μ + eLpNorm U q μ + (eLpNorm V p μ + eLpNorm V q μ)))
    (h0 : Φ 0 =ᵐ[μ] h)
    (hsmall : 8 * K * (eLpNorm h p μ + eLpNorm h q μ) ≤ 1) :
    ∃ U : α → E, MemLp U p μ ∧ MemLp U q μ ∧ Φ U =ᵐ[μ] U := by
  set N : (α → E) → ℝ≥0∞ := fun f => eLpNorm f p μ + eLpNorm f q μ with hNdef
  set Nh := N h with hNh
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hq0 : q ≠ 0 := (lt_of_lt_of_le zero_lt_one hq).ne'
  have hNh_top : Nh ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hhp.eLpNorm_ne_top, hhq.eLpNorm_ne_top⟩
  let U : ℕ → α → E := fun n => Nat.rec h (fun _ u => Φ u) n
  have hU0 : U 0 = h := rfl
  have hUs (n : ℕ) : U (n + 1) = Φ (U n) := rfl
  have hmem (n : ℕ) : MemLp (U n) p μ ∧ MemLp (U n) q μ := by
    induction n with
    | zero => exact ⟨hhp, hhq⟩
    | succ n ih => rw [hUs]; exact hmaps _ ih.1 ih.2
  -- the value relative to the heat term
  have hrel (V : α → E) (hVp : MemLp V p μ) (hVq : MemLp V q μ) :
      N (Φ V - h) ≤ K * N V * N V := by
    have hae : Φ V - h =ᵐ[μ] Φ V - Φ 0 := by
      filter_upwards [h0] with x hx
      simp [hx]
    have hl := hlip V 0 hVp hVq (MemLp.zero) (MemLp.zero)
    simp only [sub_zero, eLpNorm_zero, add_zero] at hl
    simp only [hNdef, eLpNorm_congr_ae hae]
    exact hl
  have hnorm_le (V : α → E) (hVp : MemLp V p μ) (hVq : MemLp V q μ) :
      N (Φ V) ≤ Nh + N (Φ V - h) := by
    have hΦ := hmaps V hVp hVq
    have hsplit : Φ V = h + (Φ V - h) := by abel
    have h1 : eLpNorm (Φ V) p μ ≤ eLpNorm h p μ + eLpNorm (Φ V - h) p μ := by
      conv_lhs => rw [hsplit]
      exact eLpNorm_add_le hp
    have h2 : eLpNorm (Φ V) q μ ≤ eLpNorm h q μ + eLpNorm (Φ V - h) q μ := by
      conv_lhs => rw [hsplit]
      exact eLpNorm_add_le hq
    calc N (Φ V) ≤ (eLpNorm h p μ + eLpNorm (Φ V - h) p μ) +
          (eLpNorm h q μ + eLpNorm (Φ V - h) q μ) := add_le_add h1 h2
      _ = Nh + N (Φ V - h) := by simp only [hNh, hNdef]; ring
  have hquad : K * (2 * Nh) * (2 * Nh) ≤ Nh := by
    calc K * (2 * Nh) * (2 * Nh) ≤ 2 * (K * (2 * Nh) * (2 * Nh)) :=
          le_add_self.trans (two_mul _).symm.le
      _ = (8 * K * Nh) * Nh := by ring
      _ ≤ 1 * Nh := by gcongr
      _ = Nh := one_mul _
  have hbound (n : ℕ) : N (U n) ≤ 2 * Nh := by
    induction n with
    | zero => rw [hU0, two_mul]; exact le_add_self
    | succ n ih =>
      rw [hUs]
      calc N (Φ (U n)) ≤ Nh + N (Φ (U n) - h) := hnorm_le _ (hmem n).1 (hmem n).2
        _ ≤ Nh + K * N (U n) * N (U n) := by gcongr; exact hrel _ (hmem n).1 (hmem n).2
        _ ≤ Nh + K * (2 * Nh) * (2 * Nh) := by gcongr
        _ ≤ Nh + Nh := by gcongr
        _ = 2 * Nh := (two_mul _).symm
  -- geometric decay of the increments
  set d : ℕ → ℝ≥0∞ := fun n => N (U (n + 1) - U n) with hd
  have hd0 : d 0 ≠ ⊤ := by
    have := hrel h hhp hhq
    have hlt : K * Nh * Nh ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top hK hNh_top) hNh_top
    exact ne_top_of_le_ne_top hlt (by simpa [hd, hUs, hU0] using this)
  have hdstep (n : ℕ) : 2 * d (n + 1) ≤ d n := by
    have hl := hlip (U (n + 1)) (U n) (hmem (n + 1)).1 (hmem (n + 1)).2 (hmem n).1 (hmem n).2
    have hl' : d (n + 1) ≤ K * d n * (2 * Nh + 2 * Nh) := by
      calc d (n + 1) = N (Φ (U (n + 1)) - Φ (U n)) := rfl
        _ ≤ K * d n * (N (U (n + 1)) + N (U n)) := hl
        _ ≤ K * d n * (2 * Nh + 2 * Nh) := by gcongr; exacts [hbound (n + 1), hbound n]
    calc 2 * d (n + 1) ≤ 2 * (K * d n * (2 * Nh + 2 * Nh)) := by gcongr
      _ = (8 * K * Nh) * d n := by ring
      _ ≤ 1 * d n := by gcongr
      _ = d n := one_mul _
  have hgeom (n : ℕ) : 2 ^ n * d n ≤ d 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc 2 ^ (n + 1) * d (n + 1) = 2 ^ n * (2 * d (n + 1)) := by ring
        _ ≤ 2 ^ n * d n := by gcongr; exact hdstep n
        _ ≤ d 0 := ih
  have hgp (n : ℕ) : 2 ^ n * eLpNorm (U (n + 1) - U n) p μ ≤ d 0 :=
    le_trans (by gcongr; exact le_self_add) (hgeom n)
  have hgq (n : ℕ) : 2 ^ n * eLpNorm (U (n + 1) - U n) q μ ≤ d 0 :=
    le_trans (by gcongr; exact le_add_self) (hgeom n)
  obtain ⟨g, hg, hgt⟩ := picard_limit_of_geometric hp (fun n => (hmem n).1) hd0 hgp
  obtain ⟨g', hg', hgt'⟩ := picard_limit_of_geometric hq (fun n => (hmem n).2) hd0 hgq
  have hgg := picard_limits_ae_eq hp0 hq0 hgt hgt'
  have hgq' : MemLp g q μ := (memLp_congr_ae hgg).2 hg'
  have hgt'' : Tendsto (fun n => eLpNorm (U n - g) q μ) atTop (𝓝 0) := by
    refine hgt'.congr fun n => eLpNorm_congr_ae ?_
    filter_upwards [hgg] with x hx
    simp [hx]
  -- the fixed point identity
  have hNg : N g ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hg.eLpNorm_ne_top, hgq'.eLpNorm_ne_top⟩
  have hdiff (n : ℕ) : eLpNorm (Φ g - g) p μ ≤
      K * N (g - U n) * (N g + 2 * Nh) + eLpNorm (U (n + 1) - g) p μ := by
    have hΦg := hmaps g hg hgq'
    have hsplit : Φ g - g = (Φ g - U (n + 1)) + (U (n + 1) - g) := by abel
    have hl := hlip g (U n) hg hgq' (hmem n).1 (hmem n).2
    rw [hsplit]
    refine (eLpNorm_add_le hp).trans ?_
    refine add_le_add ?_ le_rfl
    calc eLpNorm (Φ g - U (n + 1)) p μ ≤ N (Φ g - Φ (U n)) := le_self_add
      _ ≤ K * N (g - U n) * (N g + N (U n)) := hl
      _ ≤ K * N (g - U n) * (N g + 2 * Nh) := by gcongr; exact hbound n
  have hlim : Tendsto (fun n => K * N (g - U n) * (N g + 2 * Nh) +
      eLpNorm (U (n + 1) - g) p μ) atTop (𝓝 0) := by
    have hN : Tendsto (fun n => N (g - U n)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => eLpNorm (g - U n) p μ) atTop (𝓝 0) :=
        hgt.congr fun n => eLpNorm_sub_comm _ _ _ _
      have h2 : Tendsto (fun n => eLpNorm (g - U n) q μ) atTop (𝓝 0) :=
        hgt''.congr fun n => eLpNorm_sub_comm _ _ _ _
      simpa using h1.add h2
    have hK' : Tendsto (fun n => K * N (g - U n)) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hN (Or.inr hK)
    have hK'' : Tendsto (fun n => K * N (g - U n) * (N g + 2 * Nh)) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const hK'
        (Or.inr (ENNReal.add_ne_top.2 ⟨hNg, ENNReal.mul_ne_top (by simp) hNh_top⟩))
    simpa using hK''.add (hgt.comp (tendsto_add_atTop_nat 1))
  have hzero : eLpNorm (Φ g - g) p μ = 0 :=
    le_antisymm (ge_of_tendsto' hlim hdiff) bot_le
  refine ⟨g, hg, hgq', ?_⟩
  have hae := (eLpNorm_eq_zero_iff hp0).1 hzero
  filter_upwards [hae] with x hx
  exact sub_eq_zero.1 hx

end ESS

end
