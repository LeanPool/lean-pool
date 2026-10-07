/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedSolution
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildInitialTrace

/-!
# The forced regularized solution for all times

The solutions of `eq:reg-mild-forced` on the intervals `[0, T]` agree on
common times by uniqueness and causality, so they define one continuous
divergence-free `L²` curve on `[0, ∞)`, as stated at the end of the proof of
`lem:regularised-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

noncomputable section

namespace CKN.Leray

variable (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (b : RealVectorL2)
  (hb : RegularizedMildJData b) {h : ℝ → RealVectorL2} (hh : StronglyMeasurable h)
  (hH2 : ∀ T : ℝ, IntegrableOn (fun s => ‖h s‖ ^ 2) (Ioc 0 T))

/-- The solution of `eq:reg-mild-forced` on `[0, T]`. -/
@[expose]
def forcedSolutionOn (T : ℝ) (hT : 0 ≤ T) : C(RegularizedMildTimeInterval T, RealVectorL2) :=
  Classical.choose (exists_forcedMildSolution ρ ε hε b hb hh hH2 T hT)

theorem forcedSolutionOn_spec (T : ℝ) (hT : 0 ≤ T) :
    (∀ t : RegularizedMildTimeInterval T, forcedSolutionOn ρ ε hε b hb hh hH2 T hT t =
      forcedMildRHS b h (regularizedMildClampedTensorTrajectory ρ ε hε T hT
        (forcedSolutionOn ρ ε hε b hb hh hH2 T hT)) t.1 t.2.1) ∧
    ∀ t, ‖forcedSolutionOn ρ ε hε b hb hh hH2 T hT t‖ ^ 2 ≤
      (‖b‖ ^ 2 + ∫ s in Ioc 0 T, ‖h s‖ ^ 2) * Real.exp T :=
  Classical.choose_spec (exists_forcedMildSolution ρ ε hε b hb hh hH2 T hT)

/-- Solutions on nested intervals agree on the smaller interval. -/
theorem forcedSolutionOn_consistent {T T' : ℝ} (hT : 0 ≤ T) (hTT' : T ≤ T') {s : ℝ}
    (hs : s ∈ RegularizedMildTimeInterval T) :
    forcedSolutionOn ρ ε hε b hb hh hH2 T hT ⟨s, hs⟩ =
      forcedSolutionOn ρ ε hε b hb hh hH2 T' (hT.trans hTT') ⟨s, hs.1, hs.2.trans hTT'⟩ := by
  have hT' : 0 ≤ T' := hT.trans hTT'
  let ι : RegularizedMildTimeInterval T → RegularizedMildTimeInterval T' :=
    fun t => ⟨t.1, t.2.1, t.2.2.trans hTT'⟩
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  let w : C(RegularizedMildTimeInterval T, RealVectorL2) :=
    ⟨fun t => forcedSolutionOn ρ ε hε b hb hh hH2 T' hT' (ι t),
      (forcedSolutionOn ρ ε hε b hb hh hH2 T' hT').continuous.comp hι⟩
  have hw : ∀ t : RegularizedMildTimeInterval T, w t = forcedMildRHS b h
      (regularizedMildClampedTensorTrajectory ρ ε hε T hT w) t.1 t.2.1 := by
    intro t
    change forcedSolutionOn ρ ε hε b hb hh hH2 T' hT' (ι t) = _
    rw [(forcedSolutionOn_spec ρ ε hε b hb hh hH2 T' hT').1 (ι t)]
    refine forcedMildRHS_congr_Icc b h t.2.1 fun r hr => ?_
    have hrT : r ∈ RegularizedMildTimeInterval T := ⟨hr.1, hr.2.trans t.2.2⟩
    have hrT' : r ∈ RegularizedMildTimeInterval T' := ⟨hr.1, hr.2.trans (t.2.2.trans hTT')⟩
    simp only [regularizedMildClampedTensorTrajectory,
      regularizedMildTimeClamp_eq_of_mem T' hT' hrT', regularizedMildTimeClamp_eq_of_mem T hT hrT]
    rfl
  have heq := forcedMildSolution_unique ρ ε hε b hh (fun T => integrableOn_norm_of_sq hh (hH2 T))
    T hT (forcedSolutionOn ρ ε hε b hb hh hH2 T hT) w
    (forcedSolutionOn_spec ρ ε hε b hb hh hH2 T hT).1 hw
  rw [heq]
  rfl

theorem forcedSolutionOn_congr {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : A = B)
    (x : RegularizedMildTimeInterval A) (y : RegularizedMildTimeInterval B) (hxy : x.1 = y.1) :
    forcedSolutionOn ρ ε hε b hb hh hH2 A hA x = forcedSolutionOn ρ ε hε b hb hh hH2 B hB y := by
  subst hAB
  congr 1
  exact Subtype.ext hxy

/-- The forced regularized solution curve on the real line; negative times
are mapped to time zero. -/
@[expose]
def forcedSolutionCurve (t : ℝ) : RealVectorL2 :=
  forcedSolutionOn ρ ε hε b hb hh hH2 (max t 0 + 1) (by positivity)
    ⟨max t 0, le_max_right _ _, by linarith only⟩

/-- On `[0, T]` the solution curve is the solution on `[0, T]`. -/
theorem forcedSolutionCurve_eq {T : ℝ} (hT : 0 ≤ T) {t : ℝ}
    (ht : t ∈ RegularizedMildTimeInterval T) :
    forcedSolutionCurve ρ ε hε b hb hh hH2 t =
      forcedSolutionOn ρ ε hε b hb hh hH2 T hT ⟨t, ht⟩ := by
  unfold forcedSolutionCurve
  have hmax : max t 0 = t := max_eq_left ht.1
  have hs : t ∈ RegularizedMildTimeInterval (t + 1) := ⟨ht.1, by linarith only⟩
  rw [forcedSolutionOn_congr ρ ε hε b hb hh hH2 _ (by linarith only [ht.1] : (0 : ℝ) ≤ t + 1)
    (by rw [hmax]) _ ⟨t, hs⟩ hmax]
  rcases le_total (t + 1) T with h1 | h1
  · exact forcedSolutionOn_consistent ρ ε hε b hb hh hH2 (by linarith only [ht.1]) h1 hs
  · exact (forcedSolutionOn_consistent ρ ε hε b hb hh hH2 hT h1 ht).symm

/-- At negative times the solution curve takes its initial value. -/
theorem forcedSolutionCurve_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    forcedSolutionCurve ρ ε hε b hb hh hH2 t = forcedSolutionCurve ρ ε hε b hb hh hH2 0 := by
  unfold forcedSolutionCurve
  exact forcedSolutionOn_congr ρ ε hε b hb hh hH2 _ _ (by simp [max_eq_right ht]) _ _
    (by simp [max_eq_right ht])

theorem continuous_forcedSolutionCurve : Continuous (forcedSolutionCurve ρ ε hε b hb hh hH2) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  set N : ℝ := |t₀| + 1 with hN
  have hN0 : 0 ≤ N := by positivity
  let g : ℝ → RealVectorL2 := fun t => forcedSolutionOn ρ ε hε b hb hh hH2 N hN0
    (regularizedMildTimeClamp N hN0 (max t 0))
  have hg : Continuous g := (forcedSolutionOn ρ ε hε b hb hh hH2 N hN0).continuous.comp
    ((regularizedMildTimeClamp_continuous N hN0).comp (continuous_id.max continuous_const))
  refine hg.continuousAt.congr ?_
  have ht₀N : t₀ < N := by
    have := le_abs_self t₀
    linarith only [this, hN]
  filter_upwards [eventually_lt_nhds ht₀N] with t ht
  have hmem : max t 0 ∈ RegularizedMildTimeInterval N :=
    ⟨le_max_right _ _, max_le ht.le hN0⟩
  simp only [g, regularizedMildTimeClamp_eq_of_mem N hN0 hmem]
  rcases le_total 0 t with h0 | h0
  · have hmem' : t ∈ RegularizedMildTimeInterval N := ⟨h0, ht.le⟩
    rw [forcedSolutionCurve_eq ρ ε hε b hb hh hH2 hN0 hmem']
    exact forcedSolutionOn_congr ρ ε hε b hb hh hH2 _ _ rfl _ _ (max_eq_left h0)
  · have hmem' : (0 : ℝ) ∈ RegularizedMildTimeInterval N := ⟨le_rfl, hN0⟩
    rw [forcedSolutionCurve_of_nonpos ρ ε hε b hb hh hH2 h0,
      forcedSolutionCurve_eq ρ ε hε b hb hh hH2 hN0 hmem']
    exact forcedSolutionOn_congr ρ ε hε b hb hh hH2 _ _ rfl _ _ (max_eq_right h0)

/-- The solution curve solves `eq:reg-mild-forced` at every nonnegative time. -/
theorem forcedSolutionCurve_mild {t : ℝ} (ht : 0 ≤ t) :
    forcedSolutionCurve ρ ε hε b hb hh hH2 t = forcedMildRHS b h
      (fun s => regularizedMildTensor ρ ε hε (forcedSolutionCurve ρ ε hε b hb hh hH2 s)) t ht := by
  have htt : t ∈ RegularizedMildTimeInterval t := ⟨ht, le_rfl⟩
  rw [forcedSolutionCurve_eq ρ ε hε b hb hh hH2 ht htt,
    (forcedSolutionOn_spec ρ ε hε b hb hh hH2 t ht).1 ⟨t, htt⟩]
  refine forcedMildRHS_congr_Icc b h ht fun r hr => ?_
  simp only [regularizedMildClampedTensorTrajectory, regularizedMildTimeClamp_eq_of_mem t ht hr]
  rw [forcedSolutionCurve_eq ρ ε hε b hb hh hH2 ht hr]

theorem forcedForceDuhamel_zero_time (h : ℝ → RealVectorL2) : forcedForceDuhamel h 0 = 0 := by
  unfold forcedForceDuhamel
  rw [Ioc_self, Measure.restrict_empty, integral_zero_measure]

/-- The solution curve starts at the datum. -/
theorem forcedSolutionCurve_zero : forcedSolutionCurve ρ ε hε b hb hh hH2 0 = b := by
  rw [forcedSolutionCurve_mild ρ ε hε b hb hh hH2 le_rfl]
  unfold forcedMildRHS
  have hS : ∀ F : ℝ → RealTensorL2, regularizedMildStokesIntegral F 0 = 0 := fun F => by
    unfold regularizedMildStokesIntegral
    rw [integral_Icc_eq_integral_Ioc, Ioc_self, Measure.restrict_empty, integral_zero_measure]
  rw [realHeatOperator_zero, hS,
    forcedForceDuhamel_zero_time, sub_zero, add_zero]

/-- The solution curve takes values in the divergence-free space. -/
theorem forcedSolutionCurve_mildJData {t : ℝ} (ht : 0 ≤ t) :
    RegularizedMildJData (forcedSolutionCurve ρ ε hε b hb hh hH2 t) := by
  set u := forcedSolutionOn ρ ε hε b hb hh hH2 t ht with hudef
  set F := regularizedMildClampedTensorTrajectory ρ ε hε t ht u with hFdef
  have htt : t ∈ RegularizedMildTimeInterval t := ⟨ht, le_rfl⟩
  have hFm : StronglyMeasurable F :=
    (regularizedMildClampedTensorTrajectory_continuous ρ ε hε t ht u).stronglyMeasurable
  have hFC : ∀ s ∈ Ioc 0 t, ‖F s‖ ≤ regularizedMildMollifierConstant ρ ε * ‖u‖ ^ 2 :=
    fun s _ => regularizedMildClampedTensorTrajectory_norm_le ρ ε hε t ht u ‖u‖ (norm_nonneg _)
      (fun r => u.norm_coe_le_norm r) s
  have hcurve : forcedMildCurve b h F t = forcedSolutionCurve ρ ε hε b hb hh hH2 t := by
    unfold forcedMildCurve
    rw [dite_eq_left ht, forcedSolutionCurve_eq ρ ε hε b hb hh hH2 ht htt,
      (forcedSolutionOn_spec ρ ε hε b hb hh hH2 t ht).1 ⟨t, htt⟩]
  rw [← hcurve]
  exact forcedMildCurve_mildJData b hb hFm hh hFC (hH2 t) ht le_rfl

/-- The energy inequality `eq:reg-energy-forced` for the solution curve on
`[0, T]`. -/
theorem forcedSolutionCurve_energy {T : ℝ} (hT : 0 ≤ T) :
    ∃ v : ℝ → ComplexVectorL2,
      (∀ s ∈ RegularizedMildTimeInterval T,
        realPartVectorL2 (v s) = forcedSolutionCurve ρ ε hε b hb hh hH2 s) ∧
      (∀ᵐ s ∂(volume.restrict (Ioc 0 T)), MemLp (forcedFourierGradHat (v s)) 2 volume) ∧
      IntegrableOn (fun s => forcedFourierDissipation (v s)) (Ioc 0 T) ∧
      ∀ τ ∈ RegularizedMildTimeInterval T,
        ‖forcedSolutionCurve ρ ε hε b hb hh hH2 τ‖ ^ 2 +
            2 * ∫ s in Ioc 0 τ, forcedFourierDissipation (v s) ≤
          ‖b‖ ^ 2 + 2 * ∫ s in Ioc 0 τ,
            inner ℝ (forcedSolutionCurve ρ ε hε b hb hh hH2 s) (h s) := by
  set u := forcedSolutionOn ρ ε hε b hb hh hH2 T hT with hudef
  obtain ⟨v, hre, hmem, hint, hen⟩ := forcedMildSolution_energy ρ ε hε b hb hh hH2 T hT u
    (forcedSolutionOn_spec ρ ε hε b hb hh hH2 T hT).1
  refine ⟨v, fun s hs => ?_, hmem, hint, fun τ hτ => ?_⟩
  · rw [hre s hs, forcedSolutionCurve_eq ρ ε hε b hb hh hH2 hT hs]
  · have h1 := hen τ hτ
    rw [← forcedSolutionCurve_eq ρ ε hε b hb hh hH2 hT hτ] at h1
    have h2 : ∫ s in Ioc 0 τ, inner ℝ (u (regularizedMildTimeClamp T hT s)) (h s) =
        ∫ s in Ioc 0 τ, inner ℝ (forcedSolutionCurve ρ ε hε b hb hh hH2 s) (h s) := by
      refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
      have hsT : s ∈ RegularizedMildTimeInterval T := ⟨hs.1.le, hs.2.trans hτ.2⟩
      rw [regularizedMildTimeClamp_eq_of_mem T hT hsT,
        forcedSolutionCurve_eq ρ ε hε b hb hh hH2 hT hsT]
    rw [h2] at h1
    exact h1

end CKN.Leray

end
