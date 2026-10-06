/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.HeatSliceIBP
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Calculus

/-!
# The commutator-term slice integration by parts

Before the time `s`, `∫ Γ (w (∂ₜχ − Δχ) − 2 ∇χ · ∇w) = ∫ w K₀`, where `χ` is the backward
parabolic cutoff and `K₀ = Γ (∂ₜχ + Δχ) + 2 ∇_zΓ · ∇χ` is the commutator kernel. The proof
integrates by parts in each spatial direction `i` against `F_i := Γ ∂ᵢχ`, which (unlike `Γχ`
itself) is compactly supported inside the window before the time `s`, since `∂ᵢχ` already
vanishes off the window there; this gives `∫ F_i ∂ᵢw = -∫ (∂ᵢΓ · ∂ᵢχ + Γ ∂ᵢ²χ) w`, and summing
over `i` and rearranging produces exactly `K₀`. This is the third and last of the three slice
integrations by parts in the cut-off heat representation of the interior estimates in the proof
of `lem:aniso:annulus`.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN CKN.Foundation.Heat

noncomputable section
namespace CIV



/-- `Γ ∂ᵢχ`, the summand of the divergence term of `K₀`. -/
@[expose] def serrinHeatWeightDeriv (x : Vec3) (s ρ : ℝ) (i : Fin 3) (z : ParabolicPoint) : ℝ :=
  heatKernel (x - z.1) (s - z.2) * spatialPartial (serrinCutoff x s ρ) i z

/-- The directional derivative of the ball cutoff vanishes strictly outside its radius. -/
theorem fderiv_serrinBallCutoff_eq_zero_of_lt (x : Vec3) {ρ : ℝ} (hρ : 0 < ρ) (i : Fin 3)
    {y : Vec3} (hy : ρ < vec3EuclideanNorm (y - x)) :
    fderiv ℝ (serrinBallCutoff x ρ) y (basisVec i) = 0 := by
  have houter : IsOpen {y' : Vec3 | ρ < vec3EuclideanNorm (y' - x)} := by
    have hc : Continuous (fun y' : Vec3 => vec3EuclideanNorm (y' - x)) := by
      unfold vec3EuclideanNorm; fun_prop
    exact isOpen_lt continuous_const hc
  have hBall0 : ∀ y' ∈ {y' : Vec3 | ρ < vec3EuclideanNorm (y' - x)}, serrinBallCutoff x ρ y' = 0 :=
    fun y' hy' => (serrinBallCutoff_support x hρ y').2.1 hy'.le
  exact fderiv_apply_eq_zero_of_eqOn_const houter hBall0 (basisVec i) y hy

/-- Before the time `s` and off the window, `serrinHeatWeightDeriv` vanishes; at or after `s`
it vanishes because the heat kernel itself does. -/
theorem serrinHeatWeightDeriv_eq_zero_off_window (x : Vec3) {s ρ : ℝ} (hρ : 0 < ρ) (i : Fin 3)
    {z : ParabolicPoint}
    (hout : z ∉ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s) :
    serrinHeatWeightDeriv x s ρ i z = 0 := by
  unfold serrinHeatWeightDeriv
  by_cases hzs : z.2 < s
  · have hderiv_eq : spatialPartial (serrinCutoff x s ρ) i z =
        fderiv ℝ (serrinBallCutoff x ρ) z.1 (basisVec i) * serrinTimeCut s ρ z.2 :=
      congrFun (serrinCutoff_partials x (s := s) hρ i).2.1 z
    rw [hderiv_eq]
    by_cases hball : vec3EuclideanNorm (z.1 - x) ≤ ρ
    · have htime : z.2 < s - ρ ^ 2 := by
        by_contra htime'
        exact hout ⟨hball, le_of_not_gt htime', hzs.le⟩
      have hzero : serrinTimeCut s ρ z.2 = 0 := by
        unfold serrinTimeCut
        exact (serrinTimeBump_support (s := s) hρ z.2).2.1 htime.le
      rw [hzero, mul_zero, mul_zero]
    · rw [fderiv_serrinBallCutoff_eq_zero_of_lt x hρ i (lt_of_not_ge hball), zero_mul, mul_zero]
  · push Not at hzs
    rw [heatKernel_eq_zero_of_nonpos (by linarith only [hzs]), zero_mul]

/-- Before the time `s`, `serrinHeatWeightDeriv` is smooth on the whole slice, compactly
supported in the window's spatial ball, and its own spatial partial in the same direction
recovers the two pieces of the divergence-form expansion of `K₀`. -/
theorem serrinHeatWeightDeriv_slice (x : Vec3) {s ρ : ℝ} (hρ : 0 < ρ) {τ : ℝ} (hτ : τ < s)
    (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => serrinHeatWeightDeriv x s ρ i (y, τ)) ∧
      HasCompactSupport (fun y : Vec3 => serrinHeatWeightDeriv x s ρ i (y, τ)) ∧
      tsupport (fun y : Vec3 => serrinHeatWeightDeriv x s ρ i (y, τ)) ⊆
        {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} := by
  have ht : 0 < s - τ := by linarith only [hτ]
  have hΓsm : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => heatKernel (x - y) (s - τ)) :=
    (contDiff_heatKernel_space ht).comp (contDiff_const.sub contDiff_id)
  have hdχsm : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => spatialPartial (serrinCutoff x s ρ) i z) :=
    CKN.spatialPartial_contDiff (contDiff_serrinCutoff x (s := s) hρ) i
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => serrinHeatWeightDeriv x s ρ i (y, τ)) := by
    unfold serrinHeatWeightDeriv
    exact hΓsm.mul (hdχsm.comp (contDiff_id.prodMk contDiff_const))
  have hcnorm : Continuous (fun y' : Vec3 => vec3EuclideanNorm (y' - x)) := by
    unfold vec3EuclideanNorm; fun_prop
  have hsupp : tsupport (fun y : Vec3 => serrinHeatWeightDeriv x s ρ i (y, τ)) ⊆
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} := by
    refine closure_minimal (fun y hy => ?_) (isClosed_le hcnorm continuous_const)
    by_contra hout
    apply hy
    refine serrinHeatWeightDeriv_eq_zero_off_window x hρ i (z := (y, τ)) ?_
    intro hmem
    exact hout hmem.1
  have hc : IsCompact (tsupport fun y : Vec3 => serrinHeatWeightDeriv x s ρ i (y, τ)) :=
    (isCompact_closure_vec3Ball hρ).of_isClosed_subset (isClosed_tsupport _)
      (hsupp.trans (fun y hy => by rw [closure_vec3Ball hρ]; exact hy))
  exact ⟨hsm, hc, hsupp⟩

/-- The spatial partial of `serrinHeatWeightDeriv` in the same direction, before the time `s`,
by the product rule. -/
theorem spatialPartial_serrinHeatWeightDeriv (x : Vec3) {s ρ : ℝ} (hρ : 0 < ρ) {z : ParabolicPoint}
    (hz : z.2 < s) (i : Fin 3) :
    spatialPartial (serrinHeatWeightDeriv x s ρ i) i z =
      spatialPartial (fun w : ParabolicPoint => heatKernel (x - w.1) (s - w.2)) i z *
          spatialPartial (serrinCutoff x s ρ) i z +
        heatKernel (x - z.1) (s - z.2) * spatialSecondPartial (serrinCutoff x s ρ) i i z := by
  have ht : 0 < s - z.2 := by linarith only [hz]
  have hΓd : DifferentiableAt ℝ (fun y : Vec3 =>
      heatKernel (x - y) (s - z.2)) z.1 := by
    have hΓsm : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => heatKernel (x - y) (s - z.2)) :=
      (contDiff_heatKernel_space ht).comp (contDiff_const.sub contDiff_id)
    exact hΓsm.differentiable (by simp) z.1
  have hdχd : DifferentiableAt ℝ (fun y : Vec3 =>
      spatialPartial (serrinCutoff x s ρ) i (y, z.2)) z.1 := by
    have hdχsm : ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => spatialPartial (serrinCutoff x s ρ) i
      w) :=
      CKN.spatialPartial_contDiff (contDiff_serrinCutoff x (s := s) hρ) i
    exact (hdχsm.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) z.1
  unfold serrinHeatWeightDeriv
  rw [spatialPartial_mul_of_differentiableAt hΓd hdχd]
  have hbridge : spatialPartial (spatialPartial (serrinCutoff x s ρ) i) i z =
      spatialSecondPartial (serrinCutoff x s ρ) i i z := rfl
  rw [hbridge]
  ring

/-- `serrinHeatWeightDeriv` vanishes on a whole neighbourhood of any point before the time `s`
that lies off the window. -/
theorem serrinHeatWeightDeriv_eventually_eq_zero (x : Vec3) {s ρ : ℝ} (hρ : 0 < ρ) (i : Fin 3)
    {z : ParabolicPoint}
    (hout : z ∉ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s) (hz : z.2 < s) :
    ∀ᶠ w : Vec3 × ℝ in nhds z, serrinHeatWeightDeriv x s ρ i w = 0 := by
  have hderiv_eq : ∀ w : Vec3 × ℝ, spatialPartial (serrinCutoff x s ρ) i w =
      fderiv ℝ (serrinBallCutoff x ρ) w.1 (basisVec i) * serrinTimeCut s ρ w.2 :=
    fun w => congrFun (serrinCutoff_partials x (s := s) hρ i).2.1 w
  by_cases hball : vec3EuclideanNorm (z.1 - x) ≤ ρ
  · have htime : z.2 < s - ρ ^ 2 := by
      by_contra htime'
      exact hout ⟨hball, le_of_not_gt htime', hz.le⟩
    have hopen : IsOpen {w : Vec3 × ℝ | w.2 < s - ρ ^ 2} :=
      isOpen_lt continuous_snd continuous_const
    filter_upwards [hopen.mem_nhds htime] with w hw
    unfold serrinHeatWeightDeriv
    rw [hderiv_eq]
    have hzero : serrinTimeCut s ρ w.2 = 0 := by
      unfold serrinTimeCut
      exact (serrinTimeBump_support (s := s) hρ w.2).2.1 hw.le
    rw [hzero, mul_zero, mul_zero]
  · have hball' : ρ < vec3EuclideanNorm (z.1 - x) := lt_of_not_ge hball
    have hopen : IsOpen {w : Vec3 × ℝ | ρ < vec3EuclideanNorm (w.1 - x)} := by
      have hc : Continuous (fun w : Vec3 × ℝ => vec3EuclideanNorm (w.1 - x)) := by
        unfold vec3EuclideanNorm; fun_prop
      exact isOpen_lt continuous_const hc
    filter_upwards [hopen.mem_nhds hball'] with w hw
    unfold serrinHeatWeightDeriv
    rw [hderiv_eq, fderiv_serrinBallCutoff_eq_zero_of_lt x hρ i hw, zero_mul, mul_zero]

/-- Before the time `s` and off the window, the spatial partial of `serrinHeatWeightDeriv`
vanishes. -/
theorem spatialPartial_serrinHeatWeightDeriv_eq_zero_off_window (x : Vec3) {s ρ : ℝ} (hρ : 0 < ρ)
    (i : Fin 3) {z : ParabolicPoint}
    (hout : z ∉ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s) (hz : z.2 < s) :
    spatialPartial (serrinHeatWeightDeriv x s ρ i) i z = 0 :=
  spatialPartial_eq_zero_of_eventually_eq_zero
    (serrinHeatWeightDeriv_eventually_eq_zero x hρ i hout hz) i

/-- `serrinHeatWeightDeriv` is smooth before the time `s`. -/
theorem contDiffOn_serrinHeatWeightDeriv (x : Vec3) {s ρ : ℝ} (hρ : 0 < ρ) (i : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => serrinHeatWeightDeriv x s ρ i z)
      {z : Vec3 × ℝ | z.2 < s} := by
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => ((x - z.1, s - z.2) : Vec3 × ℝ)) := by
    fun_prop
  have hΓ := (heatKernel_contDiffOn_pos.of_le (by exact_mod_cast le_top)).comp hmap.contDiffOn
    (s := {z : Vec3 × ℝ | z.2 < s}) (fun z hz =>
      ⟨mem_univ _, show (0 : ℝ) < s - z.2 by linarith only [show z.2 < s from hz]⟩)
  exact hΓ.mul (CKN.spatialPartial_contDiff (contDiff_serrinCutoff x (s := s) hρ) i).contDiffOn

/-- The commutator-term integration by parts in a single spatial direction: before `s`,
`∫ (Γ ∂ᵢχ) ∂ᵢw = -∫ ∂ᵢ(Γ ∂ᵢχ) w`, together with the integrability of the left integrand. -/
theorem integral_serrinHeatWeightDeriv_mul_spatialPartial {w : ParabolicPoint → ℝ}
    {O : Set ParabolicPoint} {x : Vec3} {s ρ : ℝ} (hO : IsOpen (X := Vec3 × ℝ) O) (hρ : 0 < ρ)
    (hwin : {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s ⊆ O)
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => w z) O) (i : Fin 3) :
    IntegrableOn (fun z : Vec3 × ℝ => serrinHeatWeightDeriv x s ρ i z * spatialPartial w i z)
        {z : ParabolicPoint | z.2 < s} ∧
    IntegrableOn (fun z : Vec3 × ℝ => spatialPartial (serrinHeatWeightDeriv x s ρ i) i z * w z)
        {z : ParabolicPoint | z.2 < s} ∧
    ∫ z in {z : ParabolicPoint | z.2 < s}, serrinHeatWeightDeriv x s ρ i z * spatialPartial w i z =
      -∫ z in {z : ParabolicPoint | z.2 < s},
        spatialPartial (serrinHeatWeightDeriv x s ρ i) i z * w z := by
  set W : Set (Vec3 × ℝ) := {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s
    with hW
  set U : Set (Vec3 × ℝ) := {z | z.2 < s} with hU
  have hUo : IsOpen U := isOpen_lt continuous_snd continuous_const
  have hUm : MeasurableSet U := hUo.measurableSet
  have hWc : IsCompact W := isCompact_serrinWindow x hρ
  have hWm : MeasurableSet W := hWc.isClosed.measurableSet
  have hWfin : volume W < ⊤ := hWc.measure_lt_top
  have hc0 : ((x, s) : Vec3 × ℝ) ∈ W := ⟨by
    change vec3EuclideanNorm (x - x) ≤ ρ; rw [sub_self, vec3EuclideanNorm_zero]; exact hρ.le,
    by have := sq_nonneg ρ; linarith only [this], le_rfl⟩
  have hwc : ContinuousOn (fun z : Vec3 × ℝ => w z) O := hw.continuousOn
  have hdwc := continuousOn_spatialPartial_of_isOpen hO hw i
  obtain ⟨CW, hCW⟩ := hWc.exists_bound_of_continuousOn (hwc.mono hwin)
  obtain ⟨CdW, hCdW⟩ := hWc.exists_bound_of_continuousOn (hdwc.mono hwin)
  have hCW0 : 0 ≤ CW := (norm_nonneg _).trans (hCW _ hc0)
  have hCdW0 : 0 ≤ CdW := (norm_nonneg _).trans (hCdW _ hc0)
  obtain ⟨C, hC0, hC⟩ := serrin_kernel_pieces_bounds
  have hFc : ContinuousOn (fun z : Vec3 × ℝ => serrinHeatWeightDeriv x s ρ i z) U :=
    (contDiffOn_serrinHeatWeightDeriv x hρ i).continuousOn
  have hdFc : ContinuousOn (fun z : Vec3 × ℝ =>
      spatialPartial (serrinHeatWeightDeriv x s ρ i) i z) U :=
    continuousOn_spatialPartial_of_isOpen hUo (contDiffOn_serrinHeatWeightDeriv x hρ i) i
  have hi1 : IntegrableOn (fun z : Vec3 × ℝ =>
      serrinHeatWeightDeriv x s ρ i z * spatialPartial w i z) U := by
    refine integrableOn_of_window (g := W.indicator (fun _ => C / ρ ^ 4 * CdW)) hWm hUm
      ((hFc.mono inter_subset_right).mul (hdwc.mono (inter_subset_left.trans hwin)))
      (fun z hz hzW => by
        rw [serrinHeatWeightDeriv_eq_zero_off_window x hρ i hzW, zero_mul])
      ((integrable_indicator_iff hWm).mpr (integrableOn_const hWfin.ne)).integrableOn
      (fun z _ => indicator_nonneg (fun _ _ => by positivity) z) ?_
    intro z hz hzW
    rw [indicator_of_mem hzW, abs_mul]
    have h2 := hCdW z hzW
    rw [Real.norm_eq_abs] at h2
    exact mul_le_mul (hC x s ρ hρ z hz hzW i).2.2.1 h2 (abs_nonneg _) (by positivity)
  have hi2 : IntegrableOn (fun z : Vec3 × ℝ =>
      spatialPartial (serrinHeatWeightDeriv x s ρ i) i z * w z) U := by
    refine integrableOn_of_window
      (g := W.indicator (fun _ => (C / ρ ^ 5 + C / ρ ^ 5) * CW)) hWm hUm
      ((hdFc.mono inter_subset_right).mul (hwc.mono (inter_subset_left.trans hwin)))
      (fun z hz hzW => by
        rw [spatialPartial_serrinHeatWeightDeriv_eq_zero_off_window x hρ i hzW hz, zero_mul])
      ((integrable_indicator_iff hWm).mpr (integrableOn_const hWfin.ne)).integrableOn
      (fun z _ => indicator_nonneg (fun _ _ => by positivity) z) ?_
    intro z hz hzW
    rw [indicator_of_mem hzW, abs_mul]
    have h2 := hCW z hzW
    rw [Real.norm_eq_abs] at h2
    have hderiv := spatialPartial_serrinHeatWeightDeriv x hρ hz i
    have hb1 := (hC x s ρ hρ z hz hzW i).2.2.2
    have hb2 := (hC x s ρ hρ z hz hzW i).2.1
    have hbound : |spatialPartial (serrinHeatWeightDeriv x s ρ i) i z| ≤ C / ρ ^ 5 + C / ρ ^ 5 :=
      hderiv ▸ (abs_add_le _ _).trans (add_le_add hb1 hb2)
    exact mul_le_mul hbound h2 (abs_nonneg _) (by positivity)
  have hslice := integral_mul_spatialPartial_eq_neg_of_slices
    (F := serrinHeatWeightDeriv x s ρ i) (G := w) (s := s) i
    (fun τ hτ => (serrinHeatWeightDeriv_slice x hρ hτ i).1)
    (fun τ hτ => (serrinHeatWeightDeriv_slice x hρ hτ i).2.1)
    (fun τ hτ => ⟨{y : Vec3 | ((y, τ) : Vec3 × ℝ) ∈ O}, hO.preimage (by fun_prop),
      fun y hy => by
        have hyball : vec3EuclideanNorm (y - x) ≤ ρ :=
          (serrinHeatWeightDeriv_slice x hρ hτ i).2.2 hy
        by_cases hτwin : τ ∈ Icc (s - ρ ^ 2) s
        · exact hwin ⟨hyball, hτwin⟩
        · exfalso
          have htlt : τ < s - ρ ^ 2 := by
            rcases lt_or_ge τ (s - ρ ^ 2) with h | h
            · exact h
            · exact absurd ⟨h, hτ.le⟩ hτwin
          have hallzero : (fun y' : Vec3 => serrinHeatWeightDeriv x s ρ i (y', τ)) =
              fun _ : Vec3 => (0 : ℝ) := by
            funext y'
            unfold serrinHeatWeightDeriv
            have hderiv_eq : spatialPartial (serrinCutoff x s ρ) i (y', τ) =
                fderiv ℝ (serrinBallCutoff x ρ) y' (basisVec i) * serrinTimeCut s ρ τ :=
              congrFun (serrinCutoff_partials x (s := s) hρ i).2.1 (y', τ)
            rw [hderiv_eq]
            have : serrinTimeCut s ρ τ = 0 := by
              unfold serrinTimeCut
              exact (serrinTimeBump_support (s := s) hρ τ).2.1 htlt.le
            rw [this, mul_zero, mul_zero]
          rw [hallzero] at hy
          simp at hy,
      hw.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun y hy => hy)⟩)
    hi1 hi2
  exact ⟨hi1, hi2, hslice⟩

/-- The commutator-term slice integration by parts: before `s`,
`∫ Γ (w (∂ₜχ − Δχ) − 2 ∇χ · ∇w) = ∫ w K₀`. -/
theorem HB2c_commutator_slice_ibp {w : ParabolicPoint → ℝ} {O : Set ParabolicPoint} {x : Vec3}
    {s ρ : ℝ} (hO : IsOpen (X := Vec3 × ℝ) O) (hρ : 0 < ρ)
    (hwin : {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s ⊆ O)
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => w z) O) :
    ∫ z in {z : ParabolicPoint | z.2 < s}, heatKernel (x - z.1) (s - z.2) *
        (w z * (timePartial (serrinCutoff x s ρ) z -
            ∑ i, spatialSecondPartial (serrinCutoff x s ρ) i i z) -
          2 * ∑ i, spatialPartial (serrinCutoff x s ρ) i z * spatialPartial w i z) =
      ∫ z in {z : ParabolicPoint | z.2 < s}, w z * serrinCutoffKernel x s ρ z := by
  set W : Set (Vec3 × ℝ) := {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s
    with hW
  set U : Set ParabolicPoint := {z : ParabolicPoint | z.2 < s} with hU
  have hUm : MeasurableSet U := measurableSet_lt measurable_snd measurable_const
  have hWc : IsCompact W := isCompact_serrinWindow x hρ
  have hWm : MeasurableSet W := hWc.isClosed.measurableSet
  have hWfin : volume W < ⊤ := hWc.measure_lt_top
  have hc0 : ((x, s) : Vec3 × ℝ) ∈ W := ⟨by
    change vec3EuclideanNorm (x - x) ≤ ρ; rw [sub_self, vec3EuclideanNorm_zero]; exact hρ.le,
    by have := sq_nonneg ρ; linarith only [this], le_rfl⟩
  have hwc : ContinuousOn (fun z : Vec3 × ℝ => w z) O := hw.continuousOn
  obtain ⟨CW, hCW⟩ := hWc.exists_bound_of_continuousOn (hwc.mono hwin)
  have hCW0 : 0 ≤ CW := (norm_nonneg _).trans (hCW _ hc0)
  obtain ⟨CK, hCK0, hCK⟩ := abs_serrinCutoffKernel_le
  have hKs : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => serrinCutoffKernel x s ρ z) U := by
    have hVeq : spaceTimeSet univ (Iio s) = U := by
      ext z; exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩
    rw [← hVeq]; exact contDiffOn_serrinCutoffKernel x hρ
  have hRHSint : IntegrableOn (fun z : Vec3 × ℝ => w z * serrinCutoffKernel x s ρ z) U := by
    refine integrableOn_of_window (g := W.indicator (fun _ => CW * (CK / ρ ^ 5))) hWm hUm
      ((hwc.mono (inter_subset_left.trans hwin)).mul (hKs.continuousOn.mono inter_subset_right))
      (fun z hz hzW => by rw [serrinCutoffKernel_eq_zero_off_window x hρ hz hzW, mul_zero])
      ((integrable_indicator_iff hWm).mpr (integrableOn_const hWfin.ne)).integrableOn
      (fun z _ => indicator_nonneg (fun _ _ => by positivity) z) ?_
    intro z hz hzW
    rw [indicator_of_mem hzW, abs_mul]
    have h2 := hCW z hzW
    rw [Real.norm_eq_abs] at h2
    exact mul_le_mul h2 (hCK x s ρ hρ z hz hzW) (abs_nonneg _) hCW0
  have hpiece : ∀ i : Fin 3,
      IntegrableOn (fun z : ParabolicPoint => serrinHeatWeightDeriv x s ρ i z * spatialPartial w
        i z) U ∧
      IntegrableOn (fun z : ParabolicPoint =>
          (spatialPartial (fun w' : ParabolicPoint => heatKernel (x - w'.1) (s - w'.2)) i z *
              spatialPartial (serrinCutoff x s ρ) i z +
            heatKernel (x - z.1) (s - z.2) * spatialSecondPartial (serrinCutoff x s ρ) i i z) *
            w z) U ∧
      ∫ z in U, (serrinHeatWeightDeriv x s ρ i z * spatialPartial w i z +
          (spatialPartial (fun w' : ParabolicPoint => heatKernel (x - w'.1) (s - w'.2)) i z *
              spatialPartial (serrinCutoff x s ρ) i z +
            heatKernel (x - z.1) (s - z.2) * spatialSecondPartial (serrinCutoff x s ρ) i i z) *
            w z) = 0 :=
    fun i => by
      obtain ⟨hi1, hi2, heq⟩ := integral_serrinHeatWeightDeriv_mul_spatialPartial hO hρ hwin hw i
      have hEq : Set.EqOn
          (fun z : ParabolicPoint => spatialPartial (serrinHeatWeightDeriv x s ρ i) i z * w z)
          (fun z : ParabolicPoint =>
            (spatialPartial (fun w' : ParabolicPoint => heatKernel (x - w'.1) (s - w'.2)) i z *
                spatialPartial (serrinCutoff x s ρ) i z +
              heatKernel (x - z.1) (s - z.2) * spatialSecondPartial (serrinCutoff x s ρ) i i z) *
              w z) U :=
        fun z hz => congrArg (· * w z) (spatialPartial_serrinHeatWeightDeriv x hρ hz i)
      have hi2' := hi2.congr_fun hEq hUm
      have heq' : ∫ z in U, serrinHeatWeightDeriv x s ρ i z * spatialPartial w i z =
          -∫ z in U,
            (spatialPartial (fun w' : ParabolicPoint => heatKernel (x - w'.1) (s - w'.2)) i z *
                spatialPartial (serrinCutoff x s ρ) i z +
              heatKernel (x - z.1) (s - z.2) * spatialSecondPartial (serrinCutoff x s ρ) i i z) *
              w z := by
        rw [heq]; congr 1; exact setIntegral_congr_fun hUm hEq
      refine ⟨hi1, hi2', ?_⟩
      calc ∫ z in U, (serrinHeatWeightDeriv x s ρ i z * spatialPartial w i z +
            (spatialPartial (fun w' : ParabolicPoint => heatKernel (x - w'.1) (s - w'.2)) i z *
                spatialPartial (serrinCutoff x s ρ) i z +
              heatKernel (x - z.1) (s - z.2) * spatialSecondPartial (serrinCutoff x s ρ) i i z)
                * w z)
          = (∫ z in U, serrinHeatWeightDeriv x s ρ i z * spatialPartial w i z) +
            ∫ z in U,
              (spatialPartial (fun w' : ParabolicPoint => heatKernel (x - w'.1) (s - w'.2)) i z *
                  spatialPartial (serrinCutoff x s ρ) i z +
                heatKernel (x - z.1) (s - z.2) * spatialSecondPartial (serrinCutoff x s ρ) i i z) *
                w z := integral_add hi1 hi2'
        _ = 0 := by rw [heq']; ring
  have hDsum : ∑ i : Fin 3, ∫ z in U, (serrinHeatWeightDeriv x s ρ i z * spatialPartial w i z +
      (spatialPartial (fun w' : ParabolicPoint => heatKernel (x - w'.1) (s - w'.2)) i z *
          spatialPartial (serrinCutoff x s ρ) i z +
        heatKernel (x - z.1) (s - z.2) * spatialSecondPartial (serrinCutoff x s ρ) i i z) *
        w z) = 0 :=
    Finset.sum_eq_zero (fun i _ => (hpiece i).2.2)
  have hDint : ∀ i : Fin 3, IntegrableOn (fun z : ParabolicPoint =>
      serrinHeatWeightDeriv x s ρ i z * spatialPartial w i z +
        (spatialPartial (fun w' : ParabolicPoint => heatKernel (x - w'.1) (s - w'.2)) i z *
            spatialPartial (serrinCutoff x s ρ) i z +
          heatKernel (x - z.1) (s - z.2) * spatialSecondPartial (serrinCutoff x s ρ) i i z) *
          w z) U := fun i => (hpiece i).1.add (hpiece i).2.1
  have hDsum' : ∫ z in U, ∑ i : Fin 3,
      (serrinHeatWeightDeriv x s ρ i z * spatialPartial w i z +
        (spatialPartial (fun w' : ParabolicPoint => heatKernel (x - w'.1) (s - w'.2)) i z *
            spatialPartial (serrinCutoff x s ρ) i z +
          heatKernel (x - z.1) (s - z.2) * spatialSecondPartial (serrinCutoff x s ρ) i i z) *
          w z) = 0 := by
    rw [integral_finsetSum Finset.univ (fun i _ => hDint i)]
    exact hDsum
  have hDintSum : IntegrableOn (fun z : ParabolicPoint => ∑ i : Fin 3,
      (serrinHeatWeightDeriv x s ρ i z * spatialPartial w i z +
        (spatialPartial (fun w' : ParabolicPoint => heatKernel (x - w'.1) (s - w'.2)) i z *
            spatialPartial (serrinCutoff x s ρ) i z +
          heatKernel (x - z.1) (s - z.2) * spatialSecondPartial (serrinCutoff x s ρ) i i z) *
          w z)) U :=
    integrable_finsetSum Finset.univ (fun i _ => hDint i)
  have hpointwise : ∀ z ∈ U, heatKernel (x - z.1) (s - z.2) *
      (w z * (timePartial (serrinCutoff x s ρ) z -
          ∑ i, spatialSecondPartial (serrinCutoff x s ρ) i i z) -
        2 * ∑ i, spatialPartial (serrinCutoff x s ρ) i z * spatialPartial w i z) =
      w z * serrinCutoffKernel x s ρ z - 2 * ∑ i : Fin 3,
        (serrinHeatWeightDeriv x s ρ i z * spatialPartial w i z +
          (spatialPartial (fun w' : ParabolicPoint => heatKernel (x - w'.1) (s - w'.2)) i z *
              spatialPartial (serrinCutoff x s ρ) i z +
            heatKernel (x - z.1) (s - z.2) * spatialSecondPartial (serrinCutoff x s ρ) i i z) *
            w z) := by
    intro z _
    have hK0 : serrinCutoffKernel x s ρ z = heatKernel (x - z.1) (s - z.2) *
        (timePartial (serrinCutoff x s ρ) z + ∑ i, spatialSecondPartial (serrinCutoff x s ρ) i i
          z) +
      2 * ∑ i, spatialPartial (fun w' : ParabolicPoint => heatKernel (x - w'.1) (s - w'.2)) i z *
        spatialPartial (serrinCutoff x s ρ) i z := rfl
    have hF0 : ∀ i : Fin 3, serrinHeatWeightDeriv x s ρ i z =
        heatKernel (x - z.1) (s - z.2) * spatialPartial (serrinCutoff x s ρ) i z := fun i => rfl
    rw [hK0]
    simp_rw [hF0]
    simp only [Fin.sum_univ_three]
    ring
  have hLHSeq : ∫ z in U, heatKernel (x - z.1) (s - z.2) *
      (w z * (timePartial (serrinCutoff x s ρ) z -
          ∑ i, spatialSecondPartial (serrinCutoff x s ρ) i i z) -
        2 * ∑ i, spatialPartial (serrinCutoff x s ρ) i z * spatialPartial w i z) =
      ∫ z in U, (w z * serrinCutoffKernel x s ρ z - 2 * ∑ i : Fin 3,
        (serrinHeatWeightDeriv x s ρ i z * spatialPartial w i z +
          (spatialPartial (fun w' : ParabolicPoint => heatKernel (x - w'.1) (s - w'.2)) i z *
              spatialPartial (serrinCutoff x s ρ) i z +
            heatKernel (x - z.1) (s - z.2) * spatialSecondPartial (serrinCutoff x s ρ) i i z) *
            w z)) :=
    setIntegral_congr_fun hUm hpointwise
  change ∫ z in U, heatKernel (x - z.1) (s - z.2) *
      (w z * (timePartial (serrinCutoff x s ρ) z -
          ∑ i, spatialSecondPartial (serrinCutoff x s ρ) i i z) -
        2 * ∑ i, spatialPartial (serrinCutoff x s ρ) i z * spatialPartial w i z) =
    ∫ z in U, w z * serrinCutoffKernel x s ρ z
  calc ∫ z in U, heatKernel (x - z.1) (s - z.2) *
        (w z * (timePartial (serrinCutoff x s ρ) z -
            ∑ i, spatialSecondPartial (serrinCutoff x s ρ) i i z) -
          2 * ∑ i, spatialPartial (serrinCutoff x s ρ) i z * spatialPartial w i z)
      = ∫ z in U, (w z * serrinCutoffKernel x s ρ z - 2 * ∑ i : Fin 3,
          (serrinHeatWeightDeriv x s ρ i z * spatialPartial w i z +
            (spatialPartial (fun w' : ParabolicPoint => heatKernel (x - w'.1) (s - w'.2)) i z *
                spatialPartial (serrinCutoff x s ρ) i z +
              heatKernel (x - z.1) (s - z.2) * spatialSecondPartial (serrinCutoff x s ρ) i i z) *
              w z)) := hLHSeq
    _ = (∫ z in U, w z * serrinCutoffKernel x s ρ z) -
          ∫ z in U, 2 * ∑ i : Fin 3,
            (serrinHeatWeightDeriv x s ρ i z * spatialPartial w i z +
              (spatialPartial (fun w' : ParabolicPoint => heatKernel (x - w'.1) (s - w'.2)) i z *
                  spatialPartial (serrinCutoff x s ρ) i z +
                heatKernel (x - z.1) (s - z.2) * spatialSecondPartial (serrinCutoff x s ρ) i i z) *
                w z) :=
        integral_sub hRHSint (hDintSum.const_mul 2)
    _ = (∫ z in U, w z * serrinCutoffKernel x s ρ z) -
          2 * ∫ z in U, ∑ i : Fin 3,
            (serrinHeatWeightDeriv x s ρ i z * spatialPartial w i z +
              (spatialPartial (fun w' : ParabolicPoint => heatKernel (x - w'.1) (s - w'.2)) i z *
                  spatialPartial (serrinCutoff x s ρ) i z +
                heatKernel (x - z.1) (s - z.2) * spatialSecondPartial (serrinCutoff x s ρ) i i z) *
                w z) := by rw [integral_const_mul]
    _ = ∫ z in U, w z * serrinCutoffKernel x s ρ z := by rw [hDsum']; ring

end CIV
