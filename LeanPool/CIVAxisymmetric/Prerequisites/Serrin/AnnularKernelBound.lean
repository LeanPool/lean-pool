/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.AnnularKernelIBP
public import LeanPool.CIVAxisymmetric.Reduction.ClassicalIBPIntegrability
public import LeanPool.CIVAxisymmetric.Identities.PartialCalculus
public import LeanPool.CIVAxisymmetric.Reduction.AxisDerivSymm
public import LeanPool.CIVAxisymmetric.Reduction.IteratedDerivBridge
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CIVAxisymmetric.Reduction.MultiPartialOrderShift
public import LeanPool.CIVAxisymmetric.Analysis.AxisDerivProductRule

/-!
# The annular kernel integration-by-parts bound

A kernel estimate for the interior estimates of `lem:aniso:annulus`: for `F` smooth with compact
support (here specialised to a
spatial multi-index derivative of the ball cutoff), moving the `γ₂` spatial derivatives off an
arbitrary `g` bounded only by `|g| ≤ M`, using the cutoff-times-kernel product's compact support
in the annulus `ρ/2 ≤ |y - x| ≤ ρ` to justify the integration by parts, and the Euclidean-norm
kernel and ρ-scaled cutoff bounds (`AnnularKernelIBP.lean`) to close each resulting term.
-/

public section

open Set MeasureTheory
open CKN.Foundation.Parabolic CKN CKN.Foundation.Heat

noncomputable section

namespace CIV



/-! ## Part A: the kernel factor's shift chain rule -/

private theorem spatialDeriv_shift {k : Vec3 → ℝ} {x y : Vec3} (hk : DifferentiableAt ℝ k (x - y))
    (i : Fin 3) :
    spatialDeriv (fun w : Vec3 => k (x - w)) i y = -spatialDeriv k i (x - y) := by
  have h1 : HasFDerivAt (fun w : Vec3 => x - w) (-(ContinuousLinearMap.id ℝ Vec3)) y :=
    (hasFDerivAt_id y).const_sub x
  have hcomp : HasFDerivAt (fun w : Vec3 => k (x - w))
      ((fderiv ℝ k (x - y)).comp (-(ContinuousLinearMap.id ℝ Vec3))) y :=
    hk.hasFDerivAt.comp y h1
  rw [spatialDeriv, hcomp.fderiv]
  simp [spatialDeriv]

/-! ## Part B: smoothness and compact support of a kernel-times-cutoff term -/

private theorem cutoff_vanishes_near_center {x : Vec3} {ρ : ℝ} (hρ : 0 < ρ) {γ : Fin 3 → ℕ}
    (hγ : γ 0 + γ 1 + γ 2 ≠ 0) (t : ℝ) {w : Vec3} (hw : vec3EuclideanNorm (w - x) < ρ / 2) :
    multiPartial (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ (w, t) = 0 := by
  by_contra hne
  have hmem : w ∈ Function.support (fun w : Vec3 => multiPartial
      (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ (w, t)) := hne
  have hin := support_multiPartial_cutoff_subset hρ hγ t hmem
  linarith only [hin.1, hw]

private theorem multiPartialVec3_eq_foldr (k : Vec3 → ℝ) (γ : Fin 3 → ℕ) :
    multiPartialVec3 k γ = List.foldr axisDeriv k
      (List.replicate (γ 0) (0 : Fin 3) ++ List.replicate (γ 1) (1 : Fin 3) ++
        List.replicate (γ 2) (2 : Fin 3)) := by
  change (axisDeriv 0)^[γ 0] ((axisDeriv 1)^[γ 1] ((axisDeriv 2)^[γ 2] k)) = _
  simp [foldr_axisDeriv_replicate, List.foldr_append]

private theorem contDiffOn_multiPartialVec3_ne_zero {l : Fin 3} (β : Fin 3 → ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (multiPartialVec3 (spatialDeriv newtonianKernel l) β)
      {z : Vec3 | z ≠ 0} := by
  rw [multiPartialVec3_eq_foldr]
  apply contDiffOn_foldr_axisDeriv {z : Vec3 | z ≠ 0} isOpen_ne
  intro z hz
  exact (contDiffAt_infty.mpr (fun n => contDiffAt_newtonianKernel_spatialDeriv l n z hz))
    |>.contDiffWithinAt

/-- A derivative of the Newtonian kernel at `x - y` times a derivative of the ball cutoff at
`(y, t)`: the integrand of `abs_integral_kernelCutoffTerm_mul_le`. -/
@[expose] def kernelCutoffTerm (l : Fin 3) (β : Fin 3 → ℕ) (x : Vec3) (ρ : ℝ) (γ : Fin 3 → ℕ)
    (t : ℝ) (y : Vec3) : ℝ :=
  multiPartialVec3 (spatialDeriv newtonianKernel l) β (x - y) *
    multiPartial (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ (y, t)

private theorem contDiff_kernelCutoffTerm (l : Fin 3) (β : Fin 3 → ℕ) (x : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (γ : Fin 3 → ℕ) (hγ : γ 0 + γ 1 + γ 2 ≠ 0) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (kernelCutoffTerm l β x ρ γ t) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : vec3EuclideanNorm (y - x) < ρ / 2
  · have hev : kernelCutoffTerm l β x ρ γ t =ᶠ[nhds y] (fun _ => (0 : ℝ)) := by
      filter_upwards [(isOpen_vec3Ball x (ρ / 2)).mem_nhds (mem_vec3Ball.mpr hy)] with w hw
      unfold kernelCutoffTerm
      rw [cutoff_vanishes_near_center hρ hγ t (mem_vec3Ball.mp hw), mul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · rw [not_lt] at hy
    have hxy : x - y ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      rw [h, sub_self] at hy
      unfold vec3EuclideanNorm at hy
      simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Finset.sum_const_zero, Real.sqrt_zero] at hy
      linarith only [hy, hρ]
    have hker : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : Vec3 => multiPartialVec3
        (spatialDeriv newtonianKernel l) β (x - w)) y := by
      have hcd : ContDiffAt ℝ (⊤ : ℕ∞) (multiPartialVec3 (spatialDeriv newtonianKernel l) β)
          (x - y) :=
        (contDiffOn_multiPartialVec3_ne_zero β).contDiffAt
          (isOpen_ne.mem_nhds hxy)
      exact hcd.comp y (contDiffAt_const.sub contDiffAt_id)
    exact hker.mul (contDiff_multiPartial_cutoff x hρ γ t).contDiffAt

private theorem support_kernelCutoffTerm_subset (l : Fin 3) (β : Fin 3 → ℕ) (x : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (γ : Fin 3 → ℕ) (hγ : γ 0 + γ 1 + γ 2 ≠ 0) (t : ℝ) :
    Function.support (kernelCutoffTerm l β x ρ γ t) ⊆
      {y : Vec3 | ρ / 2 ≤ vec3EuclideanNorm (y - x) ∧ vec3EuclideanNorm (y - x) ≤ ρ} := by
  intro y hy
  by_contra hcon
  apply hy
  simp only [Set.mem_ofPred_eq, not_and_or, not_le] at hcon
  unfold kernelCutoffTerm
  rcases hcon with h | h
  · rw [cutoff_vanishes_near_center hρ hγ t h, mul_zero]
  · by_contra hne
    have hmem : y ∈ Function.support (fun w : Vec3 => multiPartial
        (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ (w, t)) := by
      intro hz
      apply hne
      have hz' : multiPartial (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ (y, t) = 0 :=
        hz
      change multiPartialVec3 (spatialDeriv newtonianKernel l) β (x - y) *
          multiPartial (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ (y, t) = 0
      rw [hz', mul_zero]
    exact absurd (support_multiPartial_cutoff_subset hρ hγ t hmem).2 (not_le.mpr h)

private theorem hasCompactSupport_kernelCutoffTerm (l : Fin 3) (β : Fin 3 → ℕ) (x : Vec3)
    {ρ : ℝ} (hρ : 0 < ρ) (γ : Fin 3 → ℕ) (hγ : γ 0 + γ 1 + γ 2 ≠ 0) (t : ℝ) :
    HasCompactSupport (kernelCutoffTerm l β x ρ γ t) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_cutoffAnnulus hρ)
    (support_kernelCutoffTerm_subset l β x hρ γ hγ t)

/-! ## Part C: the volume of the annulus, and the base term bound -/

private theorem volume_real_cutoffAnnulus_le (x : Vec3) {ρ : ℝ} (hρ : 0 < ρ) :
    volume.real {y : Vec3 | ρ / 2 ≤ vec3EuclideanNorm (y - x) ∧ vec3EuclideanNorm (y - x) ≤ ρ} ≤
      ρ ^ 3 * volume.real (Metric.ball (0 : Vec3) 1) := by
  have hsub : {y : Vec3 | ρ / 2 ≤ vec3EuclideanNorm (y - x) ∧ vec3EuclideanNorm (y - x) ≤ ρ} ⊆
      Metric.closedBall x ρ := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖y - x‖ ≤ vec3EuclideanNorm (y - x) := space_norm_le_euclideanNorm _
      _ ≤ ρ := hy.2
  calc volume.real {y : Vec3 | ρ / 2 ≤ vec3EuclideanNorm (y - x) ∧ vec3EuclideanNorm (y - x) ≤ ρ}
      ≤ volume.real (Metric.closedBall x ρ) :=
        measureReal_mono hsub (isCompact_closedBall x ρ).measure_lt_top.ne
    _ = ρ ^ 3 * volume.real (Metric.ball (0 : Vec3) 1) := by
        rw [Measure.addHaar_real_closedBall (μ := volume) x hρ.le]
        congr 2
        change Module.finrank ℝ Vec3 = 3
        rw [Module.finrank_fin_fun]

private theorem integral_kernelCutoffTerm_mul_eq_setIntegral (l : Fin 3) (β : Fin 3 → ℕ) (x : Vec3)
    {ρ : ℝ} (hρ : 0 < ρ) (γ : Fin 3 → ℕ) (hγ : γ 0 + γ 1 + γ 2 ≠ 0) (t : ℝ) (h : Vec3 → ℝ) :
    ∫ y : Vec3, kernelCutoffTerm l β x ρ γ t y * h y =
      ∫ y in {y : Vec3 | ρ / 2 ≤ vec3EuclideanNorm (y - x) ∧ vec3EuclideanNorm (y - x) ≤ ρ},
        kernelCutoffTerm l β x ρ γ t y * h y := by
  rw [← MeasureTheory.integral_indicator (isCompact_cutoffAnnulus hρ).measurableSet]
  congr 1
  funext y
  by_cases hy : y ∈ {y : Vec3 | ρ / 2 ≤ vec3EuclideanNorm (y - x) ∧ vec3EuclideanNorm (y - x) ≤ ρ}
  · rw [Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem hy]
    have hz : kernelCutoffTerm l β x ρ γ t y = 0 :=
      by_contra fun hne => hy (support_kernelCutoffTerm_subset l β x hρ γ hγ t hne)
    rw [hz, zero_mul]

/-- The generic bound on the integral of a kernel-times-cutoff term against a function bounded
on the ball. -/
theorem abs_integral_kernelCutoffTerm_mul_le (l : Fin 3) {β : Fin 3 → ℕ}
    (hβ : β 0 + β 1 + β 2 ≤ 2) (x : Vec3) {ρ : ℝ} (hρ0 : 0 < ρ) {γ : Fin 3 → ℕ}
    (hγ : γ 0 + γ 1 + γ 2 ≠ 0) (t M : ℝ) (hM : 0 ≤ M) (h : Vec3 → ℝ)
    (hh : ∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → |h y| ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ |∫ y : Vec3, kernelCutoffTerm l β x ρ γ t y * h y| ≤
      C * M * ρ / ρ ^ (β 0 + β 1 + β 2 + (γ 0 + γ 1 + γ 2)) := by
  obtain ⟨ck, hck0, hck⟩ := abs_multiPartialVec3_spatialDeriv_newtonianKernel_le l β hβ
  obtain ⟨cc, hcc0, hcc⟩ := exists_bound_multiPartial_serrinBallCutoff_scaled x hρ0 γ t
  set V0 : ℝ := volume.real (Metric.ball (0 : Vec3) 1) with hV0def
  have hV0 : 0 ≤ V0 := measureReal_nonneg
  set n : ℕ := β 0 + β 1 + β 2 + (γ 0 + γ 1 + γ 2) with hndef
  refine ⟨ck * cc * 2 ^ (2 + (β 0 + β 1 + β 2)) * V0, by positivity, ?_⟩
  set B : ℝ := ck * cc * 2 ^ (2 + (β 0 + β 1 + β 2)) / ρ ^ (2 + n) * M with hBdef
  have hbound : ∀ y ∈ {y : Vec3 | ρ / 2 ≤ vec3EuclideanNorm (y - x) ∧
      vec3EuclideanNorm (y - x) ≤ ρ}, ‖kernelCutoffTerm l β x ρ γ t y * h y‖ ≤ B := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hxy0 : x - y ≠ 0 := by
      intro hcontra
      rw [sub_eq_zero] at hcontra
      rw [hcontra, sub_self] at hy1
      unfold vec3EuclideanNorm at hy1
      simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Finset.sum_const_zero, Real.sqrt_zero] at hy1
      linarith only [hy1, hρ0]
    have heuc : vec3EuclideanNorm (x - y) = vec3EuclideanNorm (y - x) := by
      rw [show x - y = -(y - x) from by ring]; exact vec3EuclideanNorm_neg _
    have hkbound : |multiPartialVec3 (spatialDeriv newtonianKernel l) β (x - y)| ≤
        ck * (2 : ℝ) ^ (2 + (β 0 + β 1 + β 2)) / ρ ^ (2 + (β 0 + β 1 + β 2)) := by
      have h1 := hck (x - y) hxy0
      rw [heuc] at h1
      have h2 : (ρ / 2) ^ (2 + (β 0 + β 1 + β 2)) ≤ vec3EuclideanNorm (y - x) ^
          (2 + (β 0 + β 1 + β 2)) := pow_le_pow_left₀ (by positivity) hy1 _
      have h3 : (0:ℝ) < (ρ / 2) ^ (2 + (β 0 + β 1 + β 2)) := by positivity
      calc |multiPartialVec3 (spatialDeriv newtonianKernel l) β (x - y)| ≤
          ck * (vec3EuclideanNorm (y - x) ^ (2 + (β 0 + β 1 + β 2)))⁻¹ := h1
        _ ≤ ck * ((ρ / 2) ^ (2 + (β 0 + β 1 + β 2)))⁻¹ := by
            apply mul_le_mul_of_nonneg_left _ hck0
            rw [inv_eq_one_div, inv_eq_one_div]
            exact one_div_le_one_div_of_le h3 h2
        _ = ck * (2:ℝ) ^ (2 + (β 0 + β 1 + β 2)) / ρ ^ (2 + (β 0 + β 1 + β 2)) := by
            rw [div_pow]
            field_simp
    have hcbound : |multiPartial (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ (y, t)| ≤
        cc / ρ ^ (γ 0 + γ 1 + γ 2) := hcc y
    have hhbound : |h y| ≤ M := hh y hy2
    unfold kernelCutoffTerm
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |multiPartialVec3 (spatialDeriv newtonianKernel l) β (x - y)| *
        |multiPartial (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ (y, t)| * |h y| ≤
        (ck * (2:ℝ) ^ (2 + (β 0 + β 1 + β 2)) / ρ ^ (2 + (β 0 + β 1 + β 2))) *
          (cc / ρ ^ (γ 0 + γ 1 + γ 2)) * M := by
          apply mul_le_mul (mul_le_mul hkbound hcbound (abs_nonneg _) (by positivity))
            hhbound (abs_nonneg _) (by positivity)
      _ = B := by rw [hBdef, hndef]; field_simp; ring
  have hmeas : volume {y : Vec3 | ρ / 2 ≤ vec3EuclideanNorm (y - x) ∧
      vec3EuclideanNorm (y - x) ≤ ρ} < ⊤ := (isCompact_cutoffAnnulus hρ0).measure_lt_top
  calc |∫ y : Vec3, kernelCutoffTerm l β x ρ γ t y * h y| =
      ‖∫ y in {y : Vec3 | ρ / 2 ≤ vec3EuclideanNorm (y - x) ∧ vec3EuclideanNorm (y - x) ≤ ρ},
        kernelCutoffTerm l β x ρ γ t y * h y‖ := by
        rw [integral_kernelCutoffTerm_mul_eq_setIntegral l β x hρ0 γ hγ t h, Real.norm_eq_abs]
    _ ≤ B * volume.real {y : Vec3 | ρ / 2 ≤ vec3EuclideanNorm (y - x) ∧
          vec3EuclideanNorm (y - x) ≤ ρ} :=
        norm_setIntegral_le_of_norm_le_const hmeas hbound
    _ ≤ B * (ρ ^ 3 * V0) := by
        apply mul_le_mul_of_nonneg_left (volume_real_cutoffAnnulus_le x hρ0) (by
          rw [hBdef]
          positivity)
    _ = ck * cc * 2 ^ (2 + (β 0 + β 1 + β 2)) * V0 * M * ρ / ρ ^ n := by
        rw [hBdef, hndef]; field_simp; ring

/-! ## Part D: pushing one more derivative onto the kernel factor -/

private theorem axisDeriv_multiPartialVec3_eq {K : Vec3 → ℝ} {s : Set Vec3} (hs : IsOpen s)
    (hK : ContDiffOn ℝ (⊤ : ℕ∞) K s) (β : Fin 3 → ℕ) (k : Fin 3) {z : Vec3} (hz : z ∈ s) :
    axisDeriv k (multiPartialVec3 K β) z = multiPartialVec3 K (β + Pi.single k 1) z := by
  set l : List (Fin 3) := List.replicate (β 0) (0 : Fin 3) ++ List.replicate (β 1) (1 : Fin 3)
    ++ List.replicate (β 2) (2 : Fin 3) with hldef
  have h_fun_eq : multiPartialVec3 K β = List.foldr axisDeriv K l := multiPartialVec3_eq_foldr K β
  set γ : Fin 3 → ℕ := fun i => β i + (if i = k then 1 else 0) with hγdef
  have hγeq : γ = β + Pi.single k 1 := by ext i; simp [hγdef, Pi.single_apply]
  have h_target_eq : multiPartialVec3 K γ =
      List.foldr axisDeriv K (List.replicate (γ 0) (0 : Fin 3) ++
        List.replicate (γ 1) (1 : Fin 3) ++ List.replicate (γ 2) (2 : Fin 3)) :=
    multiPartialVec3_eq_foldr K γ
  set l' : List (Fin 3) := List.replicate (γ 0) (0 : Fin 3) ++ List.replicate (γ 1) (1 : Fin 3)
    ++ List.replicate (γ 2) (2 : Fin 3) with hl'def
  have h_perm : (k :: l).Perm l' := by
    rw [List.perm_iff_count]
    intro c
    fin_cases c <;> fin_cases k <;> dsimp [l, l', γ] <;>
      simp [List.count_append, List.count_replicate]
  have h_eq_on := eqOn_foldr_axisDeriv_of_perm s hs K hK h_perm
  calc axisDeriv k (multiPartialVec3 K β) z
      = axisDeriv k (List.foldr axisDeriv K l) z := by rw [h_fun_eq]
    _ = List.foldr axisDeriv K (k :: l) z := rfl
    _ = List.foldr axisDeriv K l' z := h_eq_on hz
    _ = multiPartialVec3 K γ z := by rw [h_target_eq]
    _ = multiPartialVec3 K (β + Pi.single k 1) z := by rw [hγeq]

/-! ## Part E: the Leibniz expansion of one more derivative of a kernel-cutoff term -/

private theorem contDiff_liftedCutoff (x : Vec3) {ρ : ℝ} (hρ : 0 < ρ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec3 => serrinBallCutoff x ρ w) :=
  (serrinBallCutoff_support x hρ 0).2.2

private theorem contDiffOn_spatialDeriv_newtonianKernel_ne_zero (l : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (spatialDeriv newtonianKernel l) {z : Vec3 | z ≠ 0} := by
  intro z hz
  exact (contDiffAt_infty.mpr (fun n => contDiffAt_newtonianKernel_spatialDeriv l n z hz))
    |>.contDiffWithinAt

private theorem axisDeriv_kernelCutoffTerm_eq (l : Fin 3) (β : Fin 3 → ℕ) (x : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (γ : Fin 3 → ℕ) (t : ℝ) (k : Fin 3) {y : Vec3} (hy : x - y ≠ 0) :
    axisDeriv k (kernelCutoffTerm l β x ρ γ t) y =
      -kernelCutoffTerm l (β + Pi.single k 1) x ρ γ t y +
        multiPartialVec3 (spatialDeriv newtonianKernel l) β (x - y) *
          multiPartial (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1)
            (γ + Pi.single k 1) (y, t) := by
  have hdiffK : DifferentiableAt ℝ (multiPartialVec3 (spatialDeriv newtonianKernel l) β) (x - y) :=
    (contDiffOn_multiPartialVec3_ne_zero β).contDiffAt (isOpen_ne.mem_nhds hy) |>.differentiableAt
      (by simp)
  have hdiffShift : DifferentiableAt ℝ
      (fun w : Vec3 => multiPartialVec3 (spatialDeriv newtonianKernel l) β (x - w)) y :=
    hdiffK.comp y (differentiableAt_const x |>.sub differentiableAt_id)
  have hdiffC : DifferentiableAt ℝ
      (fun w : Vec3 => multiPartial (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ
        (w, t)) y :=
    (contDiff_multiPartial_cutoff x hρ γ t).differentiable (by simp) y
  have hterm1 : axisDeriv k (fun w : Vec3 =>
      multiPartialVec3 (spatialDeriv newtonianKernel l) β (x - w)) y =
      -multiPartialVec3 (spatialDeriv newtonianKernel l) (β + Pi.single k 1) (x - y) := by
    have hshift := spatialDeriv_shift (k := multiPartialVec3
      (spatialDeriv newtonianKernel l) β) hdiffK (x := x) (y := y) k
    change spatialDeriv (fun w : Vec3 => multiPartialVec3
      (spatialDeriv newtonianKernel l) β (x - w)) k y = _
    rw [hshift]
    congr 1
    exact axisDeriv_multiPartialVec3_eq isOpen_ne
      (contDiffOn_spatialDeriv_newtonianKernel_ne_zero l) β k hy
  have hterm2 : axisDeriv k (fun w : Vec3 => multiPartial
      (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ (w, t)) y =
      multiPartial (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) (γ + Pi.single k 1)
        (y, t) :=
    axisDeriv_multiPartial_slice_eq isOpen_univ t
      ((contDiff_liftedCutoff x hρ).contDiffOn) γ k (mem_univ y)
  change fderiv ℝ (kernelCutoffTerm l β x ρ γ t) y (basisVec k) = _
  unfold kernelCutoffTerm
  have hmul := axisDeriv_mul hdiffShift hdiffC k
  change axisDeriv k (fun w : Vec3 => multiPartialVec3 (spatialDeriv newtonianKernel l) β (x - w) *
    multiPartial (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ (w, t)) y = _
  rw [hmul, hterm1, hterm2]
  ring

/-! ## Part F: the integration-by-parts step -/

private theorem multiPartial_order_zero_eq (g : ParabolicPoint → ℝ) : multiPartial g 0 = g := by
  have h0 : (0 : Fin 3 → ℕ) 0 = 0 := rfl
  have h1 : (0 : Fin 3 → ℕ) 1 = 0 := rfl
  have h2 : (0 : Fin 3 → ℕ) 2 = 0 := rfl
  simp only [multiPartial, h0, h1, h2, Function.iterate_zero, id_eq]

private theorem integral_kernelCutoffTerm_mul_multiPartial_succ_eq (l : Fin 3) (β : Fin 3 → ℕ)
    (x : Vec3) {ρ : ℝ} (hρ : 0 < ρ) (γ : Fin 3 → ℕ) (hγ : γ 0 + γ 1 + γ 2 ≠ 0) (t : ℝ) (k : Fin 3)
    {g : ParabolicPoint → ℝ} {O : Set (Vec3 × ℝ)} (hO : IsOpen O)
    (hball : ∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → (y, t) ∈ O)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) O) (γ' : Fin 3 → ℕ) :
    ∫ y : Vec3, kernelCutoffTerm l β x ρ γ t y * multiPartial g (γ' + Pi.single k 1) (y, t) =
      -∫ y : Vec3, multiPartial g γ' (y, t) * axisDeriv k (kernelCutoffTerm l β x ρ γ t) y := by
  set S : Set Vec3 := {y : Vec3 | (y, t) ∈ O} with hSdef
  have hSopen : IsOpen S := hO.preimage (by fun_prop)
  have hKS : {y : Vec3 | ρ / 2 ≤ vec3EuclideanNorm (y - x) ∧ vec3EuclideanNorm (y - x) ≤ ρ} ⊆ S :=
    fun y hy => hball y hy.2
  have hmgS : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec3 => multiPartial g γ' (y, t)) S :=
    contDiffOn_multiPartial_openSlice hO hg γ' t
  have hmain := integral_mul_fderiv_eq_neg_fderiv_mul_of_continuousOn (μ := volume)
    (h := fun y : Vec3 => multiPartial g γ' (y, t)) (ψ := kernelCutoffTerm l β x ρ γ t)
    (v := basisVec k) hSopen (isCompact_cutoffAnnulus hρ) hKS hmgS
    (contDiff_kernelCutoffTerm l β x hρ γ hγ t)
    (hasCompactSupport_kernelCutoffTerm l β x hρ γ hγ t)
    (closure_minimal (support_kernelCutoffTerm_subset l β x hρ γ hγ t)
      (isCompact_cutoffAnnulus hρ).isClosed)
  have hg0 : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec3 => g (y, t)) S :=
    (contDiffOn_multiPartial_openSlice hO hg 0 t).congr
      (fun z _ => congrFun (multiPartial_order_zero_eq g) (z, t))
  have hLHS : (fun y : Vec3 => kernelCutoffTerm l β x ρ γ t y *
      multiPartial g (γ' + Pi.single k 1) (y, t)) =
      fun y : Vec3 => kernelCutoffTerm l β x ρ γ t y *
        axisDeriv k (fun w : Vec3 => multiPartial g γ' (w, t)) y := by
    funext y
    by_cases hy : y ∈ S
    · rw [axisDeriv_multiPartial_slice_eq hSopen t hg0 γ' k hy]
    · have hz : kernelCutoffTerm l β x ρ γ t y = 0 :=
        by_contra fun hne => hy (hKS (support_kernelCutoffTerm_subset l β x hρ γ hγ t hne))
      rw [hz, zero_mul, zero_mul]
  rw [hLHS]
  have hcomm : (fun y : Vec3 => kernelCutoffTerm l β x ρ γ t y *
      axisDeriv k (fun w : Vec3 => multiPartial g γ' (w, t)) y) =
      fun y : Vec3 => axisDeriv k (fun w : Vec3 => multiPartial g γ' (w, t)) y *
        kernelCutoffTerm l β x ρ γ t y := funext fun y => by ring
  rw [hcomm]
  have h2 : (∫ y : Vec3, multiPartial g γ' (y, t) * axisDeriv k (kernelCutoffTerm l β x ρ γ t) y)
      = -∫ y : Vec3, axisDeriv k (fun w : Vec3 => multiPartial g γ' (w, t)) y *
        kernelCutoffTerm l β x ρ γ t y := hmain
  linarith only [h2]

/-! ## Part G: integrability of a kernel-cutoff term times a slice-continuous function -/

private theorem continuous_kernelCutoffTerm_mul (l : Fin 3) (β : Fin 3 → ℕ) (x : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (γ : Fin 3 → ℕ) (hγ : γ 0 + γ 1 + γ 2 ≠ 0) (t : ℝ) {S : Set Vec3}
    (hS : IsOpen S)
    (hSuper : {y : Vec3 | ρ / 2 ≤ vec3EuclideanNorm (y - x) ∧ vec3EuclideanNorm (y - x) ≤ ρ} ⊆ S)
    {g : Vec3 → ℝ} (hg : ContinuousOn g S) :
    Continuous (fun y : Vec3 => kernelCutoffTerm l β x ρ γ t y * g y) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ S
  · exact ((contDiff_kernelCutoffTerm l β x hρ γ hγ t).continuous.continuousAt).mul
      (hg.continuousAt (hS.mem_nhds hy))
  · have hyAnn : y ∉ {y : Vec3 | ρ / 2 ≤ vec3EuclideanNorm (y - x) ∧
        vec3EuclideanNorm (y - x) ≤ ρ} := fun h => hy (hSuper h)
    have hopen : IsOpen {y : Vec3 | ρ / 2 ≤ vec3EuclideanNorm (y - x) ∧
        vec3EuclideanNorm (y - x) ≤ ρ}ᶜ := (isCompact_cutoffAnnulus hρ).isClosed.isOpen_compl
    have hev : (fun y : Vec3 => kernelCutoffTerm l β x ρ γ t y * g y) =ᶠ[nhds y]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [hopen.mem_nhds hyAnn] with w hw
      have hz : kernelCutoffTerm l β x ρ γ t w = 0 :=
        by_contra fun hne => hw (support_kernelCutoffTerm_subset l β x hρ γ hγ t hne)
      rw [hz, zero_mul]
    exact continuousAt_const.congr_of_eventuallyEq hev

private theorem integrable_kernelCutoffTerm_mul (l : Fin 3) (β : Fin 3 → ℕ) (x : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (γ : Fin 3 → ℕ) (hγ : γ 0 + γ 1 + γ 2 ≠ 0) (t : ℝ) {S : Set Vec3} (hS : IsOpen S)
    (hSuper : {y : Vec3 | ρ / 2 ≤ vec3EuclideanNorm (y - x) ∧ vec3EuclideanNorm (y - x) ≤ ρ} ⊆ S)
    {g : Vec3 → ℝ} (hg : ContinuousOn g S) :
    Integrable (fun y : Vec3 => kernelCutoffTerm l β x ρ γ t y * g y) := by
  apply Continuous.integrable_of_hasCompactSupport
    (continuous_kernelCutoffTerm_mul l β x hρ γ hγ t hS hSuper hg)
  exact HasCompactSupport.mul_right (hasCompactSupport_kernelCutoffTerm l β x hρ γ hγ t)

/-! ## Part H2: the open-set version, for functions singular off an open set -/

private theorem contDiffOn_spatialDeriv_of_contDiffOn {K : Vec3 → ℝ} {O : Set Vec3}
    (hO : IsOpen O) (hK : ContDiffOn ℝ (⊤ : ℕ∞) K O) (j : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (spatialDeriv K j) O :=
  (hK.fderiv_of_isOpen (m := (⊤ : ℕ∞)) hO (by simp)).clm_apply contDiffOn_const

private theorem abs_multiPartialVec3_le_norm_iteratedFDeriv_on :
    ∀ (n : ℕ) (γ : Fin 3 → ℕ), γ 0 + γ 1 + γ 2 = n →
      ∀ (K : Vec3 → ℝ) (O : Set Vec3), IsOpen O → ContDiffOn ℝ (⊤ : ℕ∞) K O →
        ∀ z : Vec3, z ∈ O → |multiPartialVec3 K γ z| ≤ ‖iteratedFDeriv ℝ n K z‖ := by
  intro n
  induction n with
  | zero =>
      intro γ hγ K O hO hK z hz
      have h0 : γ 0 = 0 := by omega
      have h1 : γ 1 = 0 := by omega
      have h2 : γ 2 = 0 := by omega
      have hz0 : multiPartialVec3 K γ z = K z := by
        simp only [multiPartialVec3, h0, h1, h2, Function.iterate_zero, id_eq]
      rw [hz0, norm_iteratedFDeriv_zero]
      exact le_of_eq (Real.norm_eq_abs _).symm
  | succ m ih =>
      intro γ hγ K O hO hK z hz
      rcases Nat.eq_zero_or_pos (γ 2) with h2 | h2
      · rcases Nat.eq_zero_or_pos (γ 1) with h1 | h1
        · have h0 : γ 0 = m + 1 := by omega
          have hu1 : Function.update γ 0 m 1 = γ 1 := Function.update_of_ne (by decide) _ _
          have hu2 : Function.update γ 0 m 2 = γ 2 := Function.update_of_ne (by decide) _ _
          have hu0 : Function.update γ 0 m 0 = m := Function.update_self 0 m γ
          have hstep : multiPartialVec3 K γ z
              = multiPartialVec3 (spatialDeriv K 0) (Function.update γ 0 m) z := by
            change (fun h => spatialDeriv h 0)^[γ 0] ((fun h => spatialDeriv h 1)^[γ 1]
              ((fun h => spatialDeriv h 2)^[γ 2] K)) z
                = (fun h => spatialDeriv h 0)^[Function.update γ 0 m 0]
                    ((fun h => spatialDeriv h 1)^[Function.update γ 0 m 1]
                      ((fun h => spatialDeriv h 2)^[Function.update γ 0 m 2] (spatialDeriv K 0))) z
            rw [hu0, hu1, hu2, h0, h1, h2]
            simp only [Function.iterate_zero, id_eq]
            rw [show m + 1 = m.succ from rfl, Function.iterate_succ_apply]
          rw [hstep]
          have hγ' : Function.update γ 0 m 0 + Function.update γ 0 m 1
              + Function.update γ 0 m 2 = m := by rw [hu0, hu1, hu2]; omega
          have hK' : ContDiffOn ℝ (⊤ : ℕ∞) (spatialDeriv K 0) O :=
            contDiffOn_spatialDeriv_of_contDiffOn hO hK 0
          calc |multiPartialVec3 (spatialDeriv K 0) (Function.update γ 0 m) z|
              ≤ ‖iteratedFDeriv ℝ m (spatialDeriv K 0) z‖ := ih _ hγ' _ _ hO hK' z hz
            _ ≤ ‖iteratedFDeriv ℝ (m + 1) K z‖ := by
                calc ‖iteratedFDeriv ℝ m (spatialDeriv K 0) z‖
                    = ‖iteratedFDeriv ℝ m (fun w => (fderiv ℝ K w) (basisVec 0)) z‖ := rfl
                  _ ≤ ‖basisVec (0 : Fin 3)‖ * ‖iteratedFDeriv ℝ m (fderiv ℝ K) z‖ :=
                      norm_iteratedFDeriv_clm_apply_const
                        ((hK.fderiv_of_isOpen (m := (⊤ : ℕ∞)) hO (by simp)).contDiffAt
                          (hO.mem_nhds hz))
                        (by exact_mod_cast le_top)
                  _ ≤ 1 * ‖iteratedFDeriv ℝ m (fderiv ℝ K) z‖ :=
                      mul_le_mul_of_nonneg_right (norm_basisVec_le_one _) (norm_nonneg _)
                  _ = ‖iteratedFDeriv ℝ (m + 1) K z‖ := by
                      rw [one_mul, norm_iteratedFDeriv_fderiv]
        · set p : ℕ := γ 1 - 1 with hpdef
          have h1 : γ 1 = p + 1 := by omega
          have hu0 : Function.update γ 1 p 0 = γ 0 := Function.update_of_ne (by decide) _ _
          have hu2 : Function.update γ 1 p 2 = γ 2 := Function.update_of_ne (by decide) _ _
          have hu1 : Function.update γ 1 p 1 = p := Function.update_self 1 p γ
          have hstep : multiPartialVec3 K γ z
              = multiPartialVec3 (spatialDeriv K 1) (Function.update γ 1 p) z := by
            change (fun h => spatialDeriv h 0)^[γ 0] ((fun h => spatialDeriv h 1)^[γ 1]
              ((fun h => spatialDeriv h 2)^[γ 2] K)) z
                = (fun h => spatialDeriv h 0)^[Function.update γ 1 p 0]
                    ((fun h => spatialDeriv h 1)^[Function.update γ 1 p 1]
                      ((fun h => spatialDeriv h 2)^[Function.update γ 1 p 2] (spatialDeriv K 1))) z
            rw [hu0, hu1, hu2, h1, h2]
            simp only [Function.iterate_zero, id_eq]
            rw [show p + 1 = p.succ from rfl, Function.iterate_succ_apply]
          rw [hstep]
          have hγ' : Function.update γ 1 p 0 + Function.update γ 1 p 1
              + Function.update γ 1 p 2 = m := by rw [hu0, hu1, hu2]; omega
          have hK' : ContDiffOn ℝ (⊤ : ℕ∞) (spatialDeriv K 1) O :=
            contDiffOn_spatialDeriv_of_contDiffOn hO hK 1
          calc |multiPartialVec3 (spatialDeriv K 1) (Function.update γ 1 p) z|
              ≤ ‖iteratedFDeriv ℝ m (spatialDeriv K 1) z‖ := ih _ hγ' _ _ hO hK' z hz
            _ ≤ ‖iteratedFDeriv ℝ (m + 1) K z‖ := by
                calc ‖iteratedFDeriv ℝ m (spatialDeriv K 1) z‖
                    = ‖iteratedFDeriv ℝ m (fun w => (fderiv ℝ K w) (basisVec 1)) z‖ := rfl
                  _ ≤ ‖basisVec (1 : Fin 3)‖ * ‖iteratedFDeriv ℝ m (fderiv ℝ K) z‖ :=
                      norm_iteratedFDeriv_clm_apply_const
                        ((hK.fderiv_of_isOpen (m := (⊤ : ℕ∞)) hO (by simp)).contDiffAt
                          (hO.mem_nhds hz))
                        (by exact_mod_cast le_top)
                  _ ≤ 1 * ‖iteratedFDeriv ℝ m (fderiv ℝ K) z‖ :=
                      mul_le_mul_of_nonneg_right (norm_basisVec_le_one _) (norm_nonneg _)
                  _ = ‖iteratedFDeriv ℝ (m + 1) K z‖ := by
                      rw [one_mul, norm_iteratedFDeriv_fderiv]
      · set q : ℕ := γ 2 - 1 with hqdef
        have h2 : γ 2 = q + 1 := by omega
        have hu0 : Function.update γ 2 q 0 = γ 0 := Function.update_of_ne (by decide) _ _
        have hu1 : Function.update γ 2 q 1 = γ 1 := Function.update_of_ne (by decide) _ _
        have hu2 : Function.update γ 2 q 2 = q := Function.update_self 2 q γ
        have hstep : multiPartialVec3 K γ z
            = multiPartialVec3 (spatialDeriv K 2) (Function.update γ 2 q) z := by
          change (fun h => spatialDeriv h 0)^[γ 0] ((fun h => spatialDeriv h 1)^[γ 1]
            ((fun h => spatialDeriv h 2)^[γ 2] K)) z
              = (fun h => spatialDeriv h 0)^[Function.update γ 2 q 0]
                  ((fun h => spatialDeriv h 1)^[Function.update γ 2 q 1]
                    ((fun h => spatialDeriv h 2)^[Function.update γ 2 q 2] (spatialDeriv K 2))) z
          rw [hu0, hu1, hu2, h2]
          rw [show q + 1 = q.succ from rfl, Function.iterate_succ_apply]
        rw [hstep]
        have hγ' : Function.update γ 2 q 0 + Function.update γ 2 q 1
            + Function.update γ 2 q 2 = m := by rw [hu0, hu1, hu2]; omega
        have hK' : ContDiffOn ℝ (⊤ : ℕ∞) (spatialDeriv K 2) O :=
          contDiffOn_spatialDeriv_of_contDiffOn hO hK 2
        calc |multiPartialVec3 (spatialDeriv K 2) (Function.update γ 2 q) z|
            ≤ ‖iteratedFDeriv ℝ m (spatialDeriv K 2) z‖ := ih _ hγ' _ _ hO hK' z hz
          _ ≤ ‖iteratedFDeriv ℝ (m + 1) K z‖ := by
              calc ‖iteratedFDeriv ℝ m (spatialDeriv K 2) z‖
                  = ‖iteratedFDeriv ℝ m (fun w => (fderiv ℝ K w) (basisVec 2)) z‖ := rfl
                _ ≤ ‖basisVec (2 : Fin 3)‖ * ‖iteratedFDeriv ℝ m (fderiv ℝ K) z‖ :=
                    norm_iteratedFDeriv_clm_apply_const
                      ((hK.fderiv_of_isOpen (m := (⊤ : ℕ∞)) hO (by simp)).contDiffAt
                        (hO.mem_nhds hz))
                      (by exact_mod_cast le_top)
                _ ≤ 1 * ‖iteratedFDeriv ℝ m (fderiv ℝ K) z‖ :=
                    mul_le_mul_of_nonneg_right (norm_basisVec_le_one _) (norm_nonneg _)
                _ = ‖iteratedFDeriv ℝ (m + 1) K z‖ := by
                    rw [one_mul, norm_iteratedFDeriv_fderiv]

/-! ## Part I: order-uniform bounds for the kernel and the cutoff -/

private theorem exists_kernel_iteratedFDeriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (l : Fin 3) (n : ℕ), n ≤ 2 → ∀ z : Vec3, z ≠ 0 →
      ‖iteratedFDeriv ℝ n (spatialDeriv newtonianKernel l) z‖ ≤
        C * (vec3EuclideanNorm z ^ (2 + n))⁻¹ := by
  obtain ⟨c00, _, hc00⟩ := exists_norm_iteratedFDeriv_newtonianKernel_spatialDeriv_le 0 0
  obtain ⟨c01, _, hc01⟩ := exists_norm_iteratedFDeriv_newtonianKernel_spatialDeriv_le 0 1
  obtain ⟨c02, _, hc02⟩ := exists_norm_iteratedFDeriv_newtonianKernel_spatialDeriv_le 0 2
  obtain ⟨c10, _, hc10⟩ := exists_norm_iteratedFDeriv_newtonianKernel_spatialDeriv_le 1 0
  obtain ⟨c11, _, hc11⟩ := exists_norm_iteratedFDeriv_newtonianKernel_spatialDeriv_le 1 1
  obtain ⟨c12, _, hc12⟩ := exists_norm_iteratedFDeriv_newtonianKernel_spatialDeriv_le 1 2
  obtain ⟨c20, _, hc20⟩ := exists_norm_iteratedFDeriv_newtonianKernel_spatialDeriv_le 2 0
  obtain ⟨c21, _, hc21⟩ := exists_norm_iteratedFDeriv_newtonianKernel_spatialDeriv_le 2 1
  obtain ⟨c22, _, hc22⟩ := exists_norm_iteratedFDeriv_newtonianKernel_spatialDeriv_le 2 2
  refine ⟨max c00 (max c01 (max c02 (max c10 (max c11 (max c12 (max c20 (max c21 c22))))))),
    by positivity, fun l n hn z hz => ?_⟩
  have hn' : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  fin_cases l <;> rcases hn' with rfl | rfl | rfl <;>
    first
    | exact (hc00 z hz).trans (mul_le_mul_of_nonneg_right (by simp [le_max_iff])
        (inv_nonneg.mpr (pow_nonneg (vec3EuclideanNorm_nonneg z) _)))
    | exact (hc01 z hz).trans (mul_le_mul_of_nonneg_right (by simp [le_max_iff])
        (inv_nonneg.mpr (pow_nonneg (vec3EuclideanNorm_nonneg z) _)))
    | exact (hc02 z hz).trans (mul_le_mul_of_nonneg_right (by simp [le_max_iff])
        (inv_nonneg.mpr (pow_nonneg (vec3EuclideanNorm_nonneg z) _)))
    | exact (hc10 z hz).trans (mul_le_mul_of_nonneg_right (by simp [le_max_iff])
        (inv_nonneg.mpr (pow_nonneg (vec3EuclideanNorm_nonneg z) _)))
    | exact (hc11 z hz).trans (mul_le_mul_of_nonneg_right (by simp [le_max_iff])
        (inv_nonneg.mpr (pow_nonneg (vec3EuclideanNorm_nonneg z) _)))
    | exact (hc12 z hz).trans (mul_le_mul_of_nonneg_right (by simp [le_max_iff])
        (inv_nonneg.mpr (pow_nonneg (vec3EuclideanNorm_nonneg z) _)))
    | exact (hc20 z hz).trans (mul_le_mul_of_nonneg_right (by simp [le_max_iff])
        (inv_nonneg.mpr (pow_nonneg (vec3EuclideanNorm_nonneg z) _)))
    | exact (hc21 z hz).trans (mul_le_mul_of_nonneg_right (by simp [le_max_iff])
        (inv_nonneg.mpr (pow_nonneg (vec3EuclideanNorm_nonneg z) _)))
    | exact (hc22 z hz).trans (mul_le_mul_of_nonneg_right (by simp [le_max_iff])
        (inv_nonneg.mpr (pow_nonneg (vec3EuclideanNorm_nonneg z) _)))

private theorem exists_cutoff_iteratedFDeriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), n ≤ 3 → ∀ (x : Vec3) (ρ : ℝ), 0 < ρ → ∀ y : Vec3,
      ‖iteratedFDeriv ℝ n (serrinBallCutoff x ρ) y‖ ≤ C / ρ ^ n := by
  obtain ⟨Cf, hCf⟩ := norm_iteratedFDeriv_serrinBallCutoff_le
  have hCfnn : ∀ n : ℕ, 0 ≤ Cf n := fun n => by
    have := hCf n 0 1 one_pos 0
    simpa using (norm_nonneg _).trans this
  refine ⟨max (Cf 0) (max (Cf 1) (max (Cf 2) (Cf 3))), by
    have := hCfnn 0; positivity, fun n hn x ρ hρ y => ?_⟩
  have hn' : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hn' with rfl | rfl | rfl | rfl <;>
    first
    | exact (hCf 0 x ρ hρ y).trans
        (div_le_div_of_nonneg_right (by simp [le_max_iff]) (pow_nonneg hρ.le _))
    | exact (hCf 1 x ρ hρ y).trans
        (div_le_div_of_nonneg_right (by simp [le_max_iff]) (pow_nonneg hρ.le _))
    | exact (hCf 2 x ρ hρ y).trans
        (div_le_div_of_nonneg_right (by simp [le_max_iff]) (pow_nonneg hρ.le _))
    | exact (hCf 3 x ρ hρ y).trans
        (div_le_div_of_nonneg_right (by simp [le_max_iff]) (pow_nonneg hρ.le _))

private theorem abs_multiPartialVec3_spatialDeriv_newtonianKernel_le_uniform
    {Ck : ℝ} (hCk : ∀ (l : Fin 3) (n : ℕ), n ≤ 2 → ∀ z : Vec3, z ≠ 0 →
      ‖iteratedFDeriv ℝ n (spatialDeriv newtonianKernel l) z‖ ≤ Ck * (vec3EuclideanNorm z ^ (2 +
        n))⁻¹)
    (l : Fin 3) {β : Fin 3 → ℕ} (hβ : β 0 + β 1 + β 2 ≤ 2) {z : Vec3} (hz : z ≠ 0) :
    |multiPartialVec3 (spatialDeriv newtonianKernel l) β z| ≤
      Ck * (vec3EuclideanNorm z ^ (2 + (β 0 + β 1 + β 2)))⁻¹ :=
  (abs_multiPartialVec3_le_norm_iteratedFDeriv_on _ β rfl _ {w : Vec3 | w ≠ 0} isOpen_ne
    (contDiffOn_spatialDeriv_newtonianKernel_ne_zero l) z hz).trans (hCk l _ hβ z hz)

private theorem abs_multiPartial_serrinBallCutoff_le_uniform
    {Ccut : ℝ} (hCcut : ∀ (n : ℕ), n ≤ 3 → ∀ (x : Vec3) (ρ : ℝ), 0 < ρ → ∀ y : Vec3,
      ‖iteratedFDeriv ℝ n (serrinBallCutoff x ρ) y‖ ≤ Ccut / ρ ^ n)
    (x : Vec3) {ρ : ℝ} (hρ : 0 < ρ) {γ : Fin 3 → ℕ} (hγ3 : γ 0 + γ 1 + γ 2 ≤ 3) (t : ℝ) (y : Vec3) :
    |multiPartial (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ (y, t)| ≤
      Ccut / ρ ^ (γ 0 + γ 1 + γ 2) := by
  rw [show multiPartial (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ (y, t) =
      multiPartialVec3 (serrinBallCutoff x ρ) γ y from
      multiPartial_lift_eq (serrinBallCutoff x ρ) γ (y, t)]
  exact (abs_multiPartialVec3_le_norm_iteratedFDeriv_on _ γ rfl _ Set.univ isOpen_univ
    ((serrinBallCutoff_support x hρ 0).2.2).contDiffOn y (Set.mem_univ y)).trans
    (hCcut _ hγ3 x ρ hρ y)

/-! ## Part J: the uniform-constant integral bound, and the final assembly -/

private theorem abs_integral_kernelCutoffTerm_mul_le_uniform
    {Ck Ccut : ℝ}
    (hCk : ∀ (l : Fin 3) (n : ℕ), n ≤ 2 → ∀ z : Vec3, z ≠ 0 →
      ‖iteratedFDeriv ℝ n (spatialDeriv newtonianKernel l) z‖ ≤ Ck * (vec3EuclideanNorm z ^ (2 +
        n))⁻¹)
    (hCcut : ∀ (n : ℕ), n ≤ 3 → ∀ (x : Vec3) (ρ : ℝ), 0 < ρ → ∀ y : Vec3,
      ‖iteratedFDeriv ℝ n (serrinBallCutoff x ρ) y‖ ≤ Ccut / ρ ^ n)
    (l : Fin 3) {β : Fin 3 → ℕ} (hβ : β 0 + β 1 + β 2 ≤ 2) (x : Vec3) {ρ : ℝ} (hρ0 : 0 < ρ)
    {γ : Fin 3 → ℕ} (hγ : γ 0 + γ 1 + γ 2 ≠ 0) (hγ3 : γ 0 + γ 1 + γ 2 ≤ 3) (t M : ℝ) (hM : 0 ≤ M)
    (h : Vec3 → ℝ) (hh : ∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → |h y| ≤ M) :
    |∫ y : Vec3, kernelCutoffTerm l β x ρ γ t y * h y| ≤
      max Ck 0 * max Ccut 0 * 2 ^ (2 + (β 0 + β 1 + β 2)) *
        volume.real (Metric.ball (0 : Vec3) 1) * M * ρ / ρ ^ (β 0 + β 1 + β 2 + (γ 0 + γ 1 + γ
          2)) := by
  set ck : ℝ := max Ck 0 with hckdef
  set cc : ℝ := max Ccut 0 with hccdef
  have hck0 : 0 ≤ ck := le_max_right _ _
  have hcc0 : 0 ≤ cc := le_max_right _ _
  have hck : ∀ z : Vec3, z ≠ 0 → |multiPartialVec3 (spatialDeriv newtonianKernel l) β z| ≤
      ck * (vec3EuclideanNorm z ^ (2 + (β 0 + β 1 + β 2)))⁻¹ := by
    intro z hz
    refine (abs_multiPartialVec3_spatialDeriv_newtonianKernel_le_uniform
      (Ck := Ck) hCk l hβ hz).trans ?_
    apply mul_le_mul_of_nonneg_right (le_max_left _ _)
      (inv_nonneg.mpr (pow_nonneg (vec3EuclideanNorm_nonneg z) _))
  have hcc : ∀ y : Vec3, |multiPartial (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ
      (y, t)| ≤ cc / ρ ^ (γ 0 + γ 1 + γ 2) := by
    intro y
    refine (abs_multiPartial_serrinBallCutoff_le_uniform
      (Ccut := Ccut) hCcut x hρ0 hγ3 t y).trans ?_
    apply div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
  set V0 : ℝ := volume.real (Metric.ball (0 : Vec3) 1) with hV0def
  have hV0 : 0 ≤ V0 := measureReal_nonneg
  set n : ℕ := β 0 + β 1 + β 2 + (γ 0 + γ 1 + γ 2) with hndef
  set B : ℝ := ck * cc * 2 ^ (2 + (β 0 + β 1 + β 2)) / ρ ^ (2 + n) * M with hBdef
  have hbound : ∀ y ∈ {y : Vec3 | ρ / 2 ≤ vec3EuclideanNorm (y - x) ∧
      vec3EuclideanNorm (y - x) ≤ ρ}, ‖kernelCutoffTerm l β x ρ γ t y * h y‖ ≤ B := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hxy0 : x - y ≠ 0 := by
      intro hcontra
      rw [sub_eq_zero] at hcontra
      rw [hcontra, sub_self] at hy1
      unfold vec3EuclideanNorm at hy1
      simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Finset.sum_const_zero, Real.sqrt_zero] at hy1
      linarith only [hy1, hρ0]
    have heuc : vec3EuclideanNorm (x - y) = vec3EuclideanNorm (y - x) := by
      rw [show x - y = -(y - x) from by ring]; exact vec3EuclideanNorm_neg _
    have hkbound : |multiPartialVec3 (spatialDeriv newtonianKernel l) β (x - y)| ≤
        ck * (2 : ℝ) ^ (2 + (β 0 + β 1 + β 2)) / ρ ^ (2 + (β 0 + β 1 + β 2)) := by
      have h1 := hck (x - y) hxy0
      rw [heuc] at h1
      have h2 : (ρ / 2) ^ (2 + (β 0 + β 1 + β 2)) ≤ vec3EuclideanNorm (y - x) ^
          (2 + (β 0 + β 1 + β 2)) := pow_le_pow_left₀ (by positivity) hy1 _
      have h3 : (0:ℝ) < (ρ / 2) ^ (2 + (β 0 + β 1 + β 2)) := by positivity
      calc |multiPartialVec3 (spatialDeriv newtonianKernel l) β (x - y)| ≤
          ck * (vec3EuclideanNorm (y - x) ^ (2 + (β 0 + β 1 + β 2)))⁻¹ := h1
        _ ≤ ck * ((ρ / 2) ^ (2 + (β 0 + β 1 + β 2)))⁻¹ := by
            apply mul_le_mul_of_nonneg_left _ hck0
            rw [inv_eq_one_div, inv_eq_one_div]
            exact one_div_le_one_div_of_le h3 h2
        _ = ck * (2:ℝ) ^ (2 + (β 0 + β 1 + β 2)) / ρ ^ (2 + (β 0 + β 1 + β 2)) := by
            rw [div_pow]
            field_simp
    have hcbound : |multiPartial (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ (y, t)| ≤
        cc / ρ ^ (γ 0 + γ 1 + γ 2) := hcc y
    have hhbound : |h y| ≤ M := hh y hy2
    unfold kernelCutoffTerm
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |multiPartialVec3 (spatialDeriv newtonianKernel l) β (x - y)| *
        |multiPartial (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ (y, t)| * |h y| ≤
        (ck * (2:ℝ) ^ (2 + (β 0 + β 1 + β 2)) / ρ ^ (2 + (β 0 + β 1 + β 2))) *
          (cc / ρ ^ (γ 0 + γ 1 + γ 2)) * M := by
          apply mul_le_mul (mul_le_mul hkbound hcbound (abs_nonneg _) (by positivity))
            hhbound (abs_nonneg _) (by positivity)
      _ = B := by rw [hBdef, hndef]; field_simp; ring
  have hmeas : volume {y : Vec3 | ρ / 2 ≤ vec3EuclideanNorm (y - x) ∧
      vec3EuclideanNorm (y - x) ≤ ρ} < ⊤ := (isCompact_cutoffAnnulus hρ0).measure_lt_top
  calc |∫ y : Vec3, kernelCutoffTerm l β x ρ γ t y * h y| =
      ‖∫ y in {y : Vec3 | ρ / 2 ≤ vec3EuclideanNorm (y - x) ∧ vec3EuclideanNorm (y - x) ≤ ρ},
        kernelCutoffTerm l β x ρ γ t y * h y‖ := by
        rw [integral_kernelCutoffTerm_mul_eq_setIntegral l β x hρ0 γ hγ t h, Real.norm_eq_abs]
    _ ≤ B * volume.real {y : Vec3 | ρ / 2 ≤ vec3EuclideanNorm (y - x) ∧
          vec3EuclideanNorm (y - x) ≤ ρ} :=
        norm_setIntegral_le_of_norm_le_const hmeas hbound
    _ ≤ B * (ρ ^ 3 * V0) := by
        apply mul_le_mul_of_nonneg_left (volume_real_cutoffAnnulus_le x hρ0) (by
          rw [hBdef]
          positivity)
    _ = max Ck 0 * max Ccut 0 * 2 ^ (2 + (β 0 + β 1 + β 2)) * V0 * M * ρ / ρ ^ n := by
        rw [hBdef, hndef, hckdef, hccdef]; field_simp; ring

/-! ## Part K: multi-index bookkeeping and the reusable Leibniz-split step -/

private theorem multiIndex_eq_zero_of_sum_eq_zero {γ : Fin 3 → ℕ} (h : γ 0 + γ 1 + γ 2 = 0) :
    γ = 0 := by
  have h0 : γ 0 = 0 := by omega
  have h1 : γ 1 = 0 := by omega
  have h2 : γ 2 = 0 := by omega
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

private theorem multiPartialVec3_zero_eq (k : Vec3 → ℝ) : multiPartialVec3 k 0 = k := by
  simp only [multiPartialVec3, Pi.zero_apply, Function.iterate_zero, id_eq]

private theorem peelDir_ne_zero {γ : Fin 3 → ℕ} (hγ : γ 0 + γ 1 + γ 2 ≠ 0) :
    γ (peelDir γ) ≠ 0 := by
  unfold peelDir
  split_ifs with h0 h1
  · exact h0
  · exact h1
  · omega

private theorem peelRest_add_single_eq {γ : Fin 3 → ℕ} (hγ : γ 0 + γ 1 + γ 2 ≠ 0) :
    peelRest γ + Pi.single (peelDir γ) 1 = γ := by
  have hne := peelDir_ne_zero hγ
  funext i
  simp only [Pi.add_apply]
  by_cases hi : i = peelDir γ
  · subst hi
    simp only [peelRest, Function.update_self, Pi.single_eq_same]
    omega
  · simp only [peelRest, Function.update_of_ne hi, Pi.single_eq_of_ne hi, add_zero]

private theorem continuousOn_multiPartial_slice {g : ParabolicPoint → ℝ} {O : Set (Vec3 × ℝ)}
    (hO : IsOpen O) (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) O) (γ' : Fin 3 → ℕ)
    (t : ℝ) : ContinuousOn (fun y : Vec3 => multiPartial g γ' (y, t)) {y : Vec3 | (y, t) ∈ O} :=
  (contDiffOn_multiPartial_openSlice hO hg γ' t).continuousOn

private theorem integral_kernelCutoffTerm_mul_multiPartial_leibniz_split (l : Fin 3)
    (β : Fin 3 → ℕ) (x : Vec3) {ρ : ℝ} (hρ0 : 0 < ρ) (γ : Fin 3 → ℕ) (hγ : γ 0 + γ 1 + γ 2 ≠ 0)
    (t : ℝ) (k : Fin 3) {g : ParabolicPoint → ℝ} {O : Set (Vec3 × ℝ)} (hO : IsOpen O)
    (hball : ∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → (y, t) ∈ O)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) O) (γ' : Fin 3 → ℕ) :
    ∫ y : Vec3, kernelCutoffTerm l β x ρ γ t y * multiPartial g (γ' + Pi.single k 1) (y, t) =
      (∫ y : Vec3, multiPartial g γ' (y, t) * kernelCutoffTerm l (β + Pi.single k 1) x ρ γ t y) -
      ∫ y : Vec3, multiPartial g γ' (y, t) * kernelCutoffTerm l β x ρ (γ + Pi.single k 1) t y := by
  rw [integral_kernelCutoffTerm_mul_multiPartial_succ_eq l β x hρ0 γ hγ t k hO hball hg γ']
  set S : Set Vec3 := {y : Vec3 | (y, t) ∈ O} with hSdef
  have hSopen : IsOpen S := hO.preimage (by fun_prop)
  have hgS : ContinuousOn (fun y : Vec3 => multiPartial g γ' (y, t)) S :=
    continuousOn_multiPartial_slice hO hg γ' t
  have hSuper : {y : Vec3 | ρ / 2 ≤ vec3EuclideanNorm (y - x) ∧ vec3EuclideanNorm (y - x) ≤ ρ} ⊆
      S := fun y hy => hball y hy.2
  have hintA : Integrable (fun y : Vec3 =>
      multiPartial g γ' (y, t) * kernelCutoffTerm l (β + Pi.single k 1) x ρ γ t y) := by
    have hI := integrable_kernelCutoffTerm_mul l (β + Pi.single k 1) x hρ0 γ hγ t hSopen hSuper hgS
    simpa [mul_comm] using hI
  have hintB : Integrable (fun y : Vec3 =>
      multiPartial g γ' (y, t) * kernelCutoffTerm l β x ρ (γ + Pi.single k 1) t y) := by
    have hγ2 : (γ + Pi.single k 1 : Fin 3 → ℕ) 0 + (γ + Pi.single k 1 : Fin 3 → ℕ) 1 +
        (γ + Pi.single k 1 : Fin 3 → ℕ) 2 ≠ 0 := by
      intro hz
      have hzero := multiIndex_eq_zero_of_sum_eq_zero hz
      have hk := congrFun hzero k
      rw [Pi.add_apply, Pi.single_eq_same, Pi.zero_apply] at hk
      omega
    have hI := integrable_kernelCutoffTerm_mul l β x hρ0 (γ + Pi.single k 1) hγ2 t hSopen hSuper hgS
    simpa [mul_comm] using hI
  have hae : (fun y : Vec3 => multiPartial g γ' (y, t) *
      axisDeriv k (kernelCutoffTerm l β x ρ γ t) y) =ᶠ[MeasureTheory.ae MeasureTheory.volume]
      (fun y : Vec3 => multiPartial g γ' (y, t) * kernelCutoffTerm l β x ρ (γ + Pi.single k 1) t y
        - multiPartial g γ' (y, t) * kernelCutoffTerm l (β + Pi.single k 1) x ρ γ t y) := by
    filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume x] with y hy
    have hxy : x - y ≠ 0 := fun h => hy (by rw [sub_eq_zero] at h; exact h.symm)
    rw [axisDeriv_kernelCutoffTerm_eq l β x hρ0 γ t k hxy]
    unfold kernelCutoffTerm
    ring
  rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_sub hintB hintA, neg_sub]

private theorem integral_multiPartial_mul_kernelCutoffTerm_leibniz_split (l : Fin 3)
    (β : Fin 3 → ℕ) (x : Vec3) {ρ : ℝ} (hρ0 : 0 < ρ) (γ : Fin 3 → ℕ) (hγ : γ 0 + γ 1 + γ 2 ≠ 0)
    (t : ℝ) (k : Fin 3) {g : ParabolicPoint → ℝ} {O : Set (Vec3 × ℝ)} (hO : IsOpen O)
    (hball : ∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → (y, t) ∈ O)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) O) (γ' : Fin 3 → ℕ) :
    ∫ y : Vec3, multiPartial g (γ' + Pi.single k 1) (y, t) * kernelCutoffTerm l β x ρ γ t y =
      (∫ y : Vec3, multiPartial g γ' (y, t) * kernelCutoffTerm l (β + Pi.single k 1) x ρ γ t y) -
      ∫ y : Vec3, multiPartial g γ' (y, t) * kernelCutoffTerm l β x ρ (γ + Pi.single k 1) t y := by
  rw [← integral_kernelCutoffTerm_mul_multiPartial_leibniz_split l β x hρ0 γ hγ t k hO hball hg γ']
  congr 1
  funext y
  ring

/-! ## Part L: the final assembly -/

private theorem multiPartial_slice_zero_eq (g : ParabolicPoint → ℝ) (y : Vec3) (t : ℝ) :
    multiPartial g 0 (y, t) = g (y, t) := congrFun (multiPartial_order_zero_eq g) (y, t)

private theorem sum_pi_single_one (k : Fin 3) :
    (Pi.single k (1 : ℕ) : Fin 3 → ℕ) 0 + (Pi.single k (1 : ℕ) : Fin 3 → ℕ) 1 +
      (Pi.single k (1 : ℕ) : Fin 3 → ℕ) 2 = 1 := by
  fin_cases k <;> simp

private theorem abs_sub_le_add_abs (A B : ℝ) : |A - B| ≤ |A| + |B| := by
  calc |A - B| = |A + (-B)| := by ring_nf
    _ ≤ |A| + |-B| := abs_add_le A (-B)
    _ = |A| + |B| := by rw [abs_neg]

private theorem abs_integral_kernelCutoffTerm_mul_comm_le_uniform
    {Ck Ccut : ℝ}
    (hCk : ∀ (l : Fin 3) (n : ℕ), n ≤ 2 → ∀ z : Vec3, z ≠ 0 →
      ‖iteratedFDeriv ℝ n (spatialDeriv newtonianKernel l) z‖ ≤ Ck * (vec3EuclideanNorm z ^ (2 +
        n))⁻¹)
    (hCcut : ∀ (n : ℕ), n ≤ 3 → ∀ (x : Vec3) (ρ : ℝ), 0 < ρ → ∀ y : Vec3,
      ‖iteratedFDeriv ℝ n (serrinBallCutoff x ρ) y‖ ≤ Ccut / ρ ^ n)
    (l : Fin 3) {β : Fin 3 → ℕ} (hβ : β 0 + β 1 + β 2 ≤ 2) (x : Vec3) {ρ : ℝ} (hρ0 : 0 < ρ)
    {γ : Fin 3 → ℕ} (hγ : γ 0 + γ 1 + γ 2 ≠ 0) (hγ3 : γ 0 + γ 1 + γ 2 ≤ 3) (t M : ℝ) (hM : 0 ≤ M)
    (g : ParabolicPoint → ℝ) (hgM : ∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → |g (y, t)| ≤ M) :
    |∫ y : Vec3, g (y, t) * kernelCutoffTerm l β x ρ γ t y| ≤
      max Ck 0 * max Ccut 0 * 2 ^ (2 + (β 0 + β 1 + β 2)) * volume.real (Metric.ball (0 : Vec3) 1)
        * M * ρ / ρ ^ (β 0 + β 1 + β 2 + (γ 0 + γ 1 + γ 2)) := by
  have hb := abs_integral_kernelCutoffTerm_mul_le_uniform hCk hCcut l hβ x hρ0 hγ hγ3 t M hM
    (fun y => g (y, t)) hgM
  simpa [mul_comm] using hb

private theorem abs_integral_kernelCutoffTerm_mul_comm_le_C0
    {Ck Ccut : ℝ}
    (hCk : ∀ (l : Fin 3) (n : ℕ), n ≤ 2 → ∀ z : Vec3, z ≠ 0 →
      ‖iteratedFDeriv ℝ n (spatialDeriv newtonianKernel l) z‖ ≤ Ck * (vec3EuclideanNorm z ^ (2 +
        n))⁻¹)
    (hCcut : ∀ (n : ℕ), n ≤ 3 → ∀ (x : Vec3) (ρ : ℝ), 0 < ρ → ∀ y : Vec3,
      ‖iteratedFDeriv ℝ n (serrinBallCutoff x ρ) y‖ ≤ Ccut / ρ ^ n)
    (l : Fin 3) {β : Fin 3 → ℕ} (hβ : β 0 + β 1 + β 2 ≤ 2) (x : Vec3) {ρ : ℝ} (hρ0 : 0 < ρ)
    {γ : Fin 3 → ℕ} (hγ : γ 0 + γ 1 + γ 2 ≠ 0) (hγ3 : γ 0 + γ 1 + γ 2 ≤ 3) (t M : ℝ) (hM : 0 ≤ M)
    (g : ParabolicPoint → ℝ) (hgM : ∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → |g (y, t)| ≤ M)
    {V0 : ℝ} (hV0 : 0 ≤ V0) (hV0eq : V0 = volume.real (Metric.ball (0 : Vec3) 1)) {ntarget : ℕ}
    (hexp : β 0 + β 1 + β 2 + (γ 0 + γ 1 + γ 2) = ntarget) :
    |∫ y : Vec3, g (y, t) * kernelCutoffTerm l β x ρ γ t y| ≤
      16 * (max Ck 0 * max Ccut 0 * V0) * M * ρ / ρ ^ ntarget := by
  have hb := abs_integral_kernelCutoffTerm_mul_comm_le_uniform hCk hCcut l hβ x hρ0 hγ hγ3 t M hM
    g hgM
  rw [hexp, ← hV0eq] at hb
  refine hb.trans ?_
  have h2 : (2 : ℝ) ^ (2 + (β 0 + β 1 + β 2)) ≤ 16 := by
    have hcases : β 0 + β 1 + β 2 = 0 ∨ β 0 + β 1 + β 2 = 1 ∨ β 0 + β 1 + β 2 = 2 := by omega
    rcases hcases with h | h | h <;> rw [h] <;> norm_num
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ hρ0.le
  apply mul_le_mul_of_nonneg_right _ hM
  nlinarith only [h2, mul_nonneg (mul_nonneg (le_max_right Ck 0) (le_max_right Ccut 0)) hV0]

private theorem annular_uniform_bound_mono {a Cstep C0 M ρ : ℝ} {n : ℕ}
    (hρ0 : 0 < ρ) (hM0 : 0 ≤ M) (hCsteple : Cstep ≤ 64 * C0)
    (hbound : a ≤ Cstep * M * ρ / ρ ^ n) :
    a ≤ (64 * C0 + 1) * M * ρ / ρ ^ n := by
  refine hbound.trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ hρ0.le
  apply mul_le_mul_of_nonneg_right (by linarith only [hCsteple]) hM0

theorem ELc_annular_kernel_ibp : ∃ C : ℝ, 0 < C ∧ ∀ (g : ParabolicPoint → ℝ)
    (O : Set ParabolicPoint) (x : Vec3) (t ρ M : ℝ) (γ₁ γ₂ : Fin 3 → ℕ) (l : Fin 3),
    IsOpen (X := Vec3 × ℝ) O → 0 < ρ → ρ ≤ 1 →
    (∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → (y, t) ∈ O) →
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) O →
    (∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → |g (y, t)| ≤ M) →
    γ₁ ≠ 0 → γ₁ 0 + γ₁ 1 + γ₁ 2 + (γ₂ 0 + γ₂ 1 + γ₂ 2) ≤ 3 →
    |∫ y : Vec3, spatialDeriv newtonianKernel l (x - y) *
        multiPartial (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ₁ (y, t) *
        multiPartial g γ₂ (y, t)| ≤
      C * M * ρ / ρ ^ (γ₁ 0 + γ₁ 1 + γ₁ 2 + (γ₂ 0 + γ₂ 1 + γ₂ 2)) := by
  obtain ⟨Ck, hCk0, hCk⟩ := exists_kernel_iteratedFDeriv_bound
  obtain ⟨Ccut, hCcut0, hCcut⟩ := exists_cutoff_iteratedFDeriv_bound
  set V0 : ℝ := volume.real (Metric.ball (0 : Vec3) 1) with hV0def
  have hV0 : 0 ≤ V0 := measureReal_nonneg
  set C0 : ℝ := max Ck 0 * max Ccut 0 * V0 with hC0def
  have hC00 : 0 ≤ C0 := by positivity
  refine ⟨64 * C0 + 1, by positivity, ?_⟩
  intro g O x t ρ M γ₁ γ₂ l hO hρ0 hρ1 hball hg hgM hγ1ne hle
  have hγ1sum : γ₁ 0 + γ₁ 1 + γ₁ 2 ≠ 0 := fun hsum => hγ1ne (multiIndex_eq_zero_of_sum_eq_zero hsum)
  have hx0 : vec3EuclideanNorm (x - x) ≤ ρ := by
    simpa only [sub_self, vec3EuclideanNorm_zero] using hρ0.le
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hgM x hx0)
  set n1 : ℕ := γ₁ 0 + γ₁ 1 + γ₁ 2 with hn1def
  set n2 : ℕ := γ₂ 0 + γ₂ 1 + γ₂ 2 with hn2def
  have hn1pos : 1 ≤ n1 := Nat.one_le_iff_ne_zero.mpr hγ1sum
  have hpteq : (fun y : Vec3 => spatialDeriv newtonianKernel l (x - y) *
        multiPartial (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ₁ (y, t) *
        multiPartial g γ₂ (y, t)) =
      (fun y : Vec3 => kernelCutoffTerm l 0 x ρ γ₁ t y * multiPartial g γ₂ (y, t)) := by
    funext y
    unfold kernelCutoffTerm
    rw [multiPartialVec3_zero_eq]
  rw [hpteq]
  have hn2cases : n2 = 0 ∨ n2 = 1 ∨ n2 = 2 := by omega
  rcases hn2cases with hn2 | hn2 | hn2
  · -- n2 = 0
    have hγ2zero : γ₂ = 0 := multiIndex_eq_zero_of_sum_eq_zero (by omega)
    have hCsteple : max Ck 0 * max Ccut 0 * 2 ^ (2 + (0 : ℕ)) * V0 ≤ 64 * C0 := by
      have h4 : max Ck 0 * max Ccut 0 * 2 ^ (2 + (0 : ℕ)) * V0 = 4 * C0 := by
        rw [hC0def]; norm_num; ring
      rw [h4]; linarith only [hC00]
    apply annular_uniform_bound_mono hρ0 hM0 hCsteple
    have hb := abs_integral_kernelCutoffTerm_mul_le_uniform hCk hCcut l
      (β := (0 : Fin 3 → ℕ)) (by norm_num) x hρ0 (γ := γ₁) hγ1sum (by omega) t M hM0
      (fun y => g (y, t)) hgM
    simp only [Pi.zero_apply] at hb
    simp only [hγ2zero, multiPartial_slice_zero_eq]
    have hexp : (0 : ℕ) + 0 + 0 + (γ₁ 0 + γ₁ 1 + γ₁ 2) = n1 + n2 := by omega
    rw [hexp] at hb
    exact hb
  · -- n2 = 1
    have hγ2sum : γ₂ 0 + γ₂ 1 + γ₂ 2 ≠ 0 := by omega
    set k1 : Fin 3 := peelDir γ₂ with hk1def
    have hpeelrest_ord : peelRest γ₂ 0 + peelRest γ₂ 1 + peelRest γ₂ 2 = 0 := by
      have := peelRest_order (γ := γ₂) hγ2sum; omega
    have hpeelrest0 : peelRest γ₂ = 0 := multiIndex_eq_zero_of_sum_eq_zero hpeelrest_ord
    have hγ2eq : peelRest γ₂ + Pi.single k1 1 = γ₂ := peelRest_add_single_eq hγ2sum
    have hsingle := sum_pi_single_one k1
    have hCsteple : max Ck 0 * max Ccut 0 * 2 ^ (2 + (1 : ℕ)) * V0 +
        max Ck 0 * max Ccut 0 * 2 ^ (2 + (0 : ℕ)) * V0 ≤ 64 * C0 := by
      have h8 : max Ck 0 * max Ccut 0 * 2 ^ (2 + (1 : ℕ)) * V0 = 8 * C0 := by rw [hC0def]; ring
      have h4 : max Ck 0 * max Ccut 0 * 2 ^ (2 + (0 : ℕ)) * V0 = 4 * C0 := by rw [hC0def]; ring
      rw [h8, h4]; linarith only [hC00]
    apply annular_uniform_bound_mono hρ0 hM0 hCsteple
    rw [← hγ2eq, integral_kernelCutoffTerm_mul_multiPartial_leibniz_split l 0 x hρ0 γ₁ hγ1sum t k1
      hO hball hg (peelRest γ₂), hpeelrest0]
    simp only [multiPartial_slice_zero_eq]
    refine (abs_sub_le_add_abs _ _).trans ?_
    have hβAord : ((0 : Fin 3 → ℕ) + Pi.single k1 1 : Fin 3 → ℕ) 0 +
        ((0 : Fin 3 → ℕ) + Pi.single k1 1 : Fin 3 → ℕ) 1 +
        ((0 : Fin 3 → ℕ) + Pi.single k1 1 : Fin 3 → ℕ) 2 ≤ 2 := by
      simp only [Pi.add_apply, Pi.zero_apply, zero_add]
      omega
    have hγ1e0 : γ₁ 0 + γ₁ 1 + γ₁ 2 ≤ 3 := by omega
    have hγBord : (γ₁ + Pi.single k1 1 : Fin 3 → ℕ) 0 + (γ₁ + Pi.single k1 1 : Fin 3 → ℕ) 1 +
        (γ₁ + Pi.single k1 1 : Fin 3 → ℕ) 2 ≠ 0 := by
      simp only [Pi.add_apply]
      omega
    have hγBord3 : (γ₁ + Pi.single k1 1 : Fin 3 → ℕ) 0 + (γ₁ + Pi.single k1 1 : Fin 3 → ℕ) 1 +
        (γ₁ + Pi.single k1 1 : Fin 3 → ℕ) 2 ≤ 3 := by
      simp only [Pi.add_apply]
      omega
    have hbA := abs_integral_kernelCutoffTerm_mul_comm_le_uniform hCk hCcut l
      (β := (0 : Fin 3 → ℕ) + Pi.single k1 1) hβAord x hρ0 (γ := γ₁) hγ1sum hγ1e0 t M hM0 g hgM
    have hbB := abs_integral_kernelCutoffTerm_mul_comm_le_uniform hCk hCcut l
      (β := (0 : Fin 3 → ℕ)) (by norm_num) x hρ0 (γ := γ₁ + Pi.single k1 1) hγBord hγBord3 t M hM0
      g hgM
    simp only [Pi.add_apply, Pi.zero_apply, zero_add] at hbA
    rw [hsingle] at hbA
    have hexpA : 1 + (γ₁ 0 + γ₁ 1 + γ₁ 2) = n1 + n2 := by omega
    rw [hexpA] at hbA
    simp only [Pi.zero_apply, zero_add] at hbB
    have hexpB : (γ₁ + Pi.single k1 1 : Fin 3 → ℕ) 0 +
        (γ₁ + Pi.single k1 1 : Fin 3 → ℕ) 1 + (γ₁ + Pi.single k1 1 : Fin 3 → ℕ) 2 = n1 + n2 := by
      simp only [Pi.add_apply] at *; omega
    rw [hexpB] at hbB
    simp only [zero_add]
    calc |(∫ y : Vec3, g (y, t) * kernelCutoffTerm l (Pi.single k1 1) x ρ γ₁ t
          y)| + |(∫ y : Vec3, g (y, t) * kernelCutoffTerm l 0 x ρ (γ₁ + Pi.single k1 1) t y)| ≤
        max Ck 0 * max Ccut 0 * 2 ^ (2 + (1 : ℕ)) * V0 * M * ρ / ρ ^ (n1 + n2) +
          max Ck 0 * max Ccut 0 * 2 ^ (2 + (0 : ℕ)) * V0 * M * ρ / ρ ^ (n1 + n2) :=
        add_le_add hbA hbB
      _ = (max Ck 0 * max Ccut 0 * 2 ^ (2 + (1 : ℕ)) * V0 +
            max Ck 0 * max Ccut 0 * 2 ^ (2 + (0 : ℕ)) * V0) * M * ρ / ρ ^ (n1 + n2) := by ring
  · -- n2 = 2
    have hγ2sum : γ₂ 0 + γ₂ 1 + γ₂ 2 ≠ 0 := by omega
    set k1 : Fin 3 := peelDir γ₂ with hk1def
    set γ' : Fin 3 → ℕ := peelRest γ₂ with hγ'def
    have hγ2eq : γ' + Pi.single k1 1 = γ₂ := peelRest_add_single_eq hγ2sum
    have hγ'ord : γ' 0 + γ' 1 + γ' 2 = 1 := by
      have hpo := peelRest_order (γ := γ₂) hγ2sum
      rw [← hγ'def] at hpo
      omega
    have hγ'sum : γ' 0 + γ' 1 + γ' 2 ≠ 0 := by omega
    set k2 : Fin 3 := peelDir γ' with hk2def
    have hpeelrest'_ord : peelRest γ' 0 + peelRest γ' 1 + peelRest γ' 2 = 0 := by
      have := peelRest_order (γ := γ') hγ'sum; omega
    have hpeelrest'0 : peelRest γ' = 0 := multiIndex_eq_zero_of_sum_eq_zero hpeelrest'_ord
    have hγ'eq : peelRest γ' + Pi.single k2 1 = γ' := peelRest_add_single_eq hγ'sum
    have hsingle1 := sum_pi_single_one k1
    have hsingle2 := sum_pi_single_one k2
    have hγ1e0 : γ₁ 0 + γ₁ 1 + γ₁ 2 ≤ 3 := by omega
    have hγBord : (γ₁ + Pi.single k1 1 : Fin 3 → ℕ) 0 + (γ₁ + Pi.single k1 1 : Fin 3 → ℕ) 1 +
        (γ₁ + Pi.single k1 1 : Fin 3 → ℕ) 2 ≠ 0 := by
      simp only [Pi.add_apply]; omega
    have hCsteple : 16 * C0 + 16 * C0 + (16 * C0 + 16 * C0) ≤ 64 * C0 := by linarith only [hC00]
    apply annular_uniform_bound_mono hρ0 hM0 hCsteple
    rw [← hγ2eq, integral_kernelCutoffTerm_mul_multiPartial_leibniz_split l 0 x hρ0 γ₁ hγ1sum t k1
      hO hball hg γ', ← hγ'eq]
    simp only [zero_add]
    rw [integral_multiPartial_mul_kernelCutoffTerm_leibniz_split l (Pi.single k1 1) x hρ0 γ₁
        hγ1sum t k2 hO hball hg (peelRest γ'),
      integral_multiPartial_mul_kernelCutoffTerm_leibniz_split l 0 x hρ0
        (γ₁ + Pi.single k1 1) hγBord t k2 hO hball hg (peelRest γ'),
      hpeelrest'0]
    simp only [multiPartial_slice_zero_eq]
    refine (abs_sub_le_add_abs _ _).trans ?_
    refine (add_le_add (abs_sub_le_add_abs _ _) (abs_sub_le_add_abs _ _)).trans ?_
    have hβ1ord : (Pi.single k1 1 + Pi.single k2 1 : Fin 3 → ℕ) 0 +
        (Pi.single k1 1 + Pi.single k2 1 : Fin 3 → ℕ) 1 +
        (Pi.single k1 1 + Pi.single k2 1 : Fin 3 → ℕ) 2 ≤ 2 := by
      simp only [Pi.add_apply]; omega
    have hβ2ord : ((0 : Fin 3 → ℕ) + Pi.single k2 1 : Fin 3 → ℕ) 0 +
        ((0 : Fin 3 → ℕ) + Pi.single k2 1 : Fin 3 → ℕ) 1 +
        ((0 : Fin 3 → ℕ) + Pi.single k2 1 : Fin 3 → ℕ) 2 ≤ 2 := by
      simp only [Pi.add_apply, Pi.zero_apply]; omega
    have hγCord : (γ₁ + Pi.single k2 1 : Fin 3 → ℕ) 0 + (γ₁ + Pi.single k2 1 : Fin 3 → ℕ) 1 +
        (γ₁ + Pi.single k2 1 : Fin 3 → ℕ) 2 ≠ 0 := by
      simp only [Pi.add_apply]; omega
    have hγCord3 : (γ₁ + Pi.single k2 1 : Fin 3 → ℕ) 0 + (γ₁ + Pi.single k2 1 : Fin 3 → ℕ) 1 +
        (γ₁ + Pi.single k2 1 : Fin 3 → ℕ) 2 ≤ 3 := by
      simp only [Pi.add_apply]; omega
    have hγDord : (γ₁ + Pi.single k1 1 + Pi.single k2 1 : Fin 3 → ℕ) 0 +
        (γ₁ + Pi.single k1 1 + Pi.single k2 1 : Fin 3 → ℕ) 1 +
        (γ₁ + Pi.single k1 1 + Pi.single k2 1 : Fin 3 → ℕ) 2 ≤ 3 := by
      simp only [Pi.add_apply]; omega
    have hexpA : (Pi.single k1 1 + Pi.single k2 1 : Fin 3 → ℕ) 0 +
        (Pi.single k1 1 + Pi.single k2 1 : Fin 3 → ℕ) 1 +
        (Pi.single k1 1 + Pi.single k2 1 : Fin 3 → ℕ) 2 + (γ₁ 0 + γ₁ 1 + γ₁ 2) = n1 + n2 := by
      simp only [Pi.add_apply] at *; omega
    have hexpB : (Pi.single k1 1 : Fin 3 → ℕ) 0 + (Pi.single k1 1 : Fin 3 → ℕ) 1 +
        (Pi.single k1 1 : Fin 3 → ℕ) 2 +
        ((γ₁ + Pi.single k2 1 : Fin 3 → ℕ) 0 + (γ₁ + Pi.single k2 1 : Fin 3 → ℕ) 1 +
          (γ₁ + Pi.single k2 1 : Fin 3 → ℕ) 2) = n1 + n2 := by
      simp only [Pi.add_apply] at *; omega
    have hexpC : ((0 : Fin 3 → ℕ) + Pi.single k2 1 : Fin 3 → ℕ) 0 +
        ((0 : Fin 3 → ℕ) + Pi.single k2 1 : Fin 3 → ℕ) 1 +
        ((0 : Fin 3 → ℕ) + Pi.single k2 1 : Fin 3 → ℕ) 2 +
        ((γ₁ + Pi.single k1 1 : Fin 3 → ℕ) 0 + (γ₁ + Pi.single k1 1 : Fin 3 → ℕ) 1 +
          (γ₁ + Pi.single k1 1 : Fin 3 → ℕ) 2) = n1 + n2 := by
      simp only [Pi.add_apply, Pi.zero_apply, zero_add] at *; omega
    have hexpD : (0 : Fin 3 → ℕ) 0 + (0 : Fin 3 → ℕ) 1 + (0 : Fin 3 → ℕ) 2 +
        ((γ₁ + Pi.single k1 1 + Pi.single k2 1 : Fin 3 → ℕ) 0 +
          (γ₁ + Pi.single k1 1 + Pi.single k2 1 : Fin 3 → ℕ) 1 +
          (γ₁ + Pi.single k1 1 + Pi.single k2 1 : Fin 3 → ℕ) 2) = n1 + n2 := by
      simp only [Pi.add_apply, Pi.zero_apply] at *; omega
    have hbA := abs_integral_kernelCutoffTerm_mul_comm_le_C0 hCk hCcut l
      (β := Pi.single k1 1 + Pi.single k2 1) hβ1ord x hρ0 (γ := γ₁) hγ1sum hγ1e0 t M hM0 g hgM
      hV0 hV0def hexpA
    have hbB := abs_integral_kernelCutoffTerm_mul_comm_le_C0 hCk hCcut l
      (β := Pi.single k1 1) (by omega) x hρ0
      (γ := γ₁ + Pi.single k2 1) hγCord hγCord3 t M hM0 g hgM hV0 hV0def hexpB
    have hbC := abs_integral_kernelCutoffTerm_mul_comm_le_C0 hCk hCcut l
      (β := (0 : Fin 3 → ℕ) + Pi.single k2 1) hβ2ord x hρ0 (γ := γ₁ + Pi.single k1 1) hγBord
      (by simp only [Pi.add_apply]; omega) t M hM0 g hgM hV0 hV0def hexpC
    have hbD := abs_integral_kernelCutoffTerm_mul_comm_le_C0 hCk hCcut l
      (β := (0 : Fin 3 → ℕ)) (by norm_num) x hρ0 (γ := γ₁ + Pi.single k1 1 + Pi.single k2 1)
      (by simp only [Pi.add_apply]; omega) hγDord t M hM0 g hgM hV0 hV0def hexpD
    calc |(∫ y : Vec3, g (y, t) * kernelCutoffTerm l (Pi.single k1 1 + Pi.single k2 1) x ρ γ₁ t
          y)| + |(∫ y : Vec3, g (y, t) *
            kernelCutoffTerm l (Pi.single k1 1) x ρ (γ₁ + Pi.single k2 1) t y)| +
        (|(∫ y : Vec3, g (y, t) * kernelCutoffTerm l ((0 : Fin 3 → ℕ) + Pi.single k2 1) x ρ
              (γ₁ + Pi.single k1 1) t y)| +
          |(∫ y : Vec3, g (y, t) * kernelCutoffTerm l 0 x ρ
              (γ₁ + Pi.single k1 1 + Pi.single k2 1) t y)|) ≤
        16 * C0 * M * ρ / ρ ^ (n1 + n2) + 16 * C0 * M * ρ / ρ ^ (n1 + n2) +
          (16 * C0 * M * ρ / ρ ^ (n1 + n2) + 16 * C0 * M * ρ / ρ ^ (n1 + n2)) :=
        add_le_add (add_le_add hbA hbB) (add_le_add hbC hbD)
      _ = (16 * C0 + 16 * C0 + (16 * C0 + 16 * C0)) * M * ρ / ρ ^ (n1 + n2) := by ring

end CIV
