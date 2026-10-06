/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.HeatCutoffKernels
public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.CutoffDerivs
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.IntegralBounds
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Integrability
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Smooth
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.KernelAllOrdersBounds
public import LeanPool.CIVAxisymmetric.Prerequisites.Kahane.MixedCalculus
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Integrals of the cut-off heat kernels

Before the time `s`, the spatial derivative of the cut-off backward heat weight
`Ψ = Γ(x - ·, s - ·) χ` has integral of size `ρ`; this is the gain in the pointwise heat bound
of the interior estimates in the proof of `lem:aniso:annulus`.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN CKN.Foundation.Heat

noncomputable section
namespace CIV



/-- The reflection-translation `z ↦ a - z` preserves Lebesgue measure on `Vec3 × ℝ`. -/
theorem measurePreserving_sub_left_prod (a : Vec3 × ℝ) :
    MeasurePreserving (fun z : Vec3 × ℝ => a - z) volume volume := by
  have hneg : MeasurePreserving (Neg.neg : Vec3 × ℝ → Vec3 × ℝ)
      ((volume : Measure Vec3).prod (volume : Measure ℝ))
      ((volume : Measure Vec3).prod (volume : Measure ℝ)) := by
    have := (Measure.measurePreserving_neg (volume : Measure Vec3)).prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))
    convert this using 1
    funext z; rfl
  have hadd := measurePreserving_add_left ((volume : Measure Vec3).prod (volume : Measure ℝ)) a
  have := hadd.comp hneg
  convert this using 1
  funext z
  simp [sub_eq_add_neg]

/-- Reflection-translation invariance of Lebesgue measure on `Vec3 × ℝ`. -/
theorem integral_comp_sub_left_prod (g : Vec3 × ℝ → ℝ) (a : Vec3 × ℝ) :
    ∫ z : Vec3 × ℝ, g (a - z) = ∫ z : Vec3 × ℝ, g z := by
  have hneg : MeasurePreserving (Neg.neg : Vec3 × ℝ → Vec3 × ℝ)
      ((volume : Measure Vec3).prod (volume : Measure ℝ))
      ((volume : Measure Vec3).prod (volume : Measure ℝ)) := by
    have := (Measure.measurePreserving_neg (volume : Measure Vec3)).prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))
    convert this using 1
    funext z; rfl
  have h1 := hneg.integral_comp (MeasurableEquiv.neg (Vec3 × ℝ)).measurableEmbedding
    (fun w => g (a + w))
  have h2 := integral_add_left_eq_self g (μ := (volume : Measure Vec3).prod (volume : Measure ℝ)) a
  have e1 : (fun z : Vec3 × ℝ => g (a - z)) = fun z => (fun w => g (a + w)) (-z) := by
    funext z; simp [sub_eq_add_neg]
  change ∫ z, g (a - z) ∂((volume : Measure Vec3).prod (volume : Measure ℝ)) =
    ∫ z, g z ∂((volume : Measure Vec3).prod (volume : Measure ℝ))
  rw [e1]
  exact h1.trans h2

/-- The heat kernel is differentiable in space at positive times. -/
theorem differentiableAt_heatKernel_space {t : ℝ} (ht : 0 < t) (y : Vec3) :
    DifferentiableAt ℝ (fun w : Vec3 => heatKernel w t) y := by
  rw [show (fun w : Vec3 => heatKernel w t) = fun w : Vec3 =>
      (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * Real.exp (-(∑ j, w j ^ 2) / (4 * t)) by
    funext w
    exact heatKernel_eq_formula_sum ht]
  fun_prop (disch := positivity)

/-- The backward cutoff is bounded by one. -/
theorem abs_serrinCutoff_le_one (x : Vec3) (s ρ : ℝ) (z : ParabolicPoint) :
    |serrinCutoff x s ρ z| ≤ 1 := by
  unfold serrinCutoff
  have h1 := serrinBallCutoff_mem_Icc x ρ z.1
  have h2 : serrinTimeBump ((z.2 - s) / ρ ^ 2) ∈ Icc (0 : ℝ) 1 := by
    unfold serrinTimeBump
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  rw [abs_mul, abs_of_nonneg h1.1, abs_of_nonneg h2.1]
  calc serrinBallCutoff x ρ z.1 * serrinTimeBump ((z.2 - s) / ρ ^ 2) ≤ 1 * 1 :=
        mul_le_mul h1.2 h2.2 h2.1 zero_le_one
    _ = 1 := one_mul 1

/-- Scaling bound for the spatial partials of the backward cutoff. -/
theorem abs_spatialPartial_serrinCutoff_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Vec3) (s ρ : ℝ), 0 < ρ →
    ∀ (z : ParabolicPoint) (j : Fin 3), |spatialPartial (serrinCutoff x s ρ) j z| ≤ C / ρ := by
  obtain ⟨C, hC⟩ := norm_iteratedFDeriv_serrinBallCutoff_le
  refine ⟨max (C 1) 0, le_max_right _ _, fun x s ρ hρ z j => ?_⟩
  have hB : ContDiff ℝ (⊤ : ℕ∞) (serrinBallCutoff x ρ) := (serrinBallCutoff_support x hρ x).2.2
  set T : ℝ := serrinTimeBump ((z.2 - s) / ρ ^ 2) with hT
  have hT1 : |T| ≤ 1 := by
    have h2 : T ∈ Icc (0 : ℝ) 1 := by
      rw [hT]; unfold serrinTimeBump
      exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
    rw [abs_of_nonneg h2.1]; exact h2.2
  have hsp : spatialPartial (serrinCutoff x s ρ) j z =
      fderiv ℝ (serrinBallCutoff x ρ) z.1 (basisVec j) * T := by
    unfold spatialPartial serrinCutoff
    change fderiv ℝ (fun y : Vec3 => serrinBallCutoff x ρ y * T) z.1 (basisVec j) = _
    rw [fderiv_mul_const ((hB.differentiable (by simp)) z.1)]
    simp only [smul_apply, smul_eq_mul]
    ring
  rw [hsp, abs_mul]
  have hd : |fderiv ℝ (serrinBallCutoff x ρ) z.1 (basisVec j)| ≤ C 1 / ρ := by
    rw [← Real.norm_eq_abs]
    refine ((fderiv ℝ (serrinBallCutoff x ρ) z.1).le_opNorm _).trans ?_
    refine (mul_le_of_le_one_right (norm_nonneg _) (norm_basisVec_le_one j)).trans ?_
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
    simpa using hC 1 x ρ hρ z.1
  have hd' : |fderiv ℝ (serrinBallCutoff x ρ) z.1 (basisVec j)| ≤ max (C 1) 0 / ρ :=
    hd.trans (div_le_div_of_nonneg_right (le_max_left _ _) hρ.le)
  calc |fderiv ℝ (serrinBallCutoff x ρ) z.1 (basisVec j)| * |T| ≤ max (C 1) 0 / ρ * 1 :=
        mul_le_mul hd' hT1 (abs_nonneg _) (by positivity)
    _ = max (C 1) 0 / ρ := mul_one _

/-- Before the time `s`, the spatial partial of the cut-off heat weight splits into the
derivative of the heat kernel and the derivative of the cutoff. -/
theorem spatialPartial_serrinHeatWeight_eq (x : Vec3) {s ρ : ℝ} (hρ : 0 < ρ)
    (z : ParabolicPoint) (hz : z.2 < s) (j : Fin 3) :
    spatialPartial (serrinHeatWeight x s ρ) j z =
      -heatKernelSpaceDerivative (x - z.1) (s - z.2) j * serrinCutoff x s ρ z +
        heatKernel (x - z.1) (s - z.2) * spatialPartial (serrinCutoff x s ρ) j z := by
  have ht : 0 < s - z.2 := by linarith only [hz]
  have hχ := contDiff_serrinCutoff x (s := s) hρ
  have hdχ : DifferentiableAt ℝ (fun y : Vec3 => serrinCutoff x s ρ (y, z.2)) z.1 :=
    ((hχ.differentiable (by simp)).comp (differentiable_id.prodMk (differentiable_const _))) z.1
  have hdΓ0 := differentiableAt_heatKernel_space ht (x - z.1)
  have hdΓ : DifferentiableAt ℝ (fun y : Vec3 => heatKernel (x - y) (s - z.2)) z.1 :=
    hdΓ0.comp z.1 ((differentiable_const _).sub differentiable_id z.1)
  have hcomp : fderiv ℝ (fun y : Vec3 => heatKernel (x - y) (s - z.2)) z.1 (basisVec j) =
      -heatKernelSpaceDerivative (x - z.1) (s - z.2) j := by
    have hsub : HasFDerivAt (fun y : Vec3 => x - y) (-ContinuousLinearMap.id ℝ Vec3) z.1 := by
      simpa using (hasFDerivAt_const (𝕜 := ℝ) x z.1).sub (hasFDerivAt_id (𝕜 := ℝ) z.1)
    have := (hdΓ0.hasFDerivAt.comp z.1 hsub).fderiv
    have e : (fun y : Vec3 => heatKernel (x - y) (s - z.2)) =
        (fun w => heatKernel w (s - z.2)) ∘ HSub.hSub x := rfl
    rw [e, this]
    simp [heatKernel_fderiv_apply_basisVec ht]
  have hm : fderiv ℝ (fun y : Vec3 => heatKernel (x - y) (s - z.2) *
        serrinCutoff x s ρ (y, z.2)) z.1 (basisVec j) =
      heatKernel (x - z.1) (s - z.2) *
          fderiv ℝ (fun y : Vec3 => serrinCutoff x s ρ (y, z.2)) z.1 (basisVec j) +
        serrinCutoff x s ρ (z.1, z.2) *
          fderiv ℝ (fun y : Vec3 => heatKernel (x - y) (s - z.2)) z.1 (basisVec j) := by
    have h := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec j)) (fderiv_mul hdΓ hdχ)
    exact h.trans (by simp only [add_apply, smul_apply, smul_eq_mul])
  have hz12 : serrinCutoff x s ρ (z.1, z.2) = serrinCutoff x s ρ z := rfl
  have hL : spatialPartial (serrinHeatWeight x s ρ) j z = fderiv ℝ (fun y : Vec3 =>
      heatKernel (x - y) (s - z.2) * serrinCutoff x s ρ (y, z.2)) z.1 (basisVec j) := rfl
  have hR : spatialPartial (serrinCutoff x s ρ) j z =
      fderiv ℝ (fun y : Vec3 => serrinCutoff x s ρ (y, z.2)) z.1 (basisVec j) := rfl
  linear_combination hL + hm + serrinCutoff x s ρ (z.1, z.2) * hcomp -
    heatKernelSpaceDerivative (x - z.1) (s - z.2) j * hz12 -
    heatKernel (x - z.1) (s - z.2) * hR

/-- The spatial partial of the cut-off heat weight is continuous before the time `s`. -/
theorem continuousOn_spatialPartial_serrinHeatWeight (x : Vec3) {s ρ : ℝ} (hρ : 0 < ρ)
    (j : Fin 3) :
    ContinuousOn (fun z : Vec3 × ℝ => spatialPartial (serrinHeatWeight x s ρ) j z)
      (spaceTimeSet univ (Iio s)) := by
  have hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => heatKernel (x - z.1) (s - z.2))
      (spaceTimeSet univ (Iio s)) := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => ((x - z.1, s - z.2) : Vec3 × ℝ)) := by
      fun_prop
    refine (heatKernel_contDiffOn_pos.of_le (by exact_mod_cast le_top)).comp hmap.contDiffOn ?_
    intro z hz
    exact ⟨mem_univ _, show (0 : ℝ) < s - z.2 by linarith only [show z.2 < s from hz.2]⟩
  have hΨ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => serrinHeatWeight x s ρ z)
      (spaceTimeSet univ (Iio s)) :=
    hΓ.mul (contDiff_serrinCutoff x (s := s) hρ).contDiffOn
  have := contDiffOn_spatialPartial_iterate_spaceTimeSet isOpen_univ isOpen_Iio hΨ j 1
  exact this.continuousOn

/-- The majorant of the heat-weight derivative, in the variable `(x - z.1, s - z.2)`. -/
@[expose] def serrinHeatMajorant (ρ C₁ : ℝ) (p : Vec3 × ℝ) : ℝ :=
  {q : Vec3 × ℝ | vec3EuclideanNorm q.1 ≤ ρ ∧ 0 < q.2 ∧ q.2 ≤ ρ ^ 2}.indicator
    (fun q => heatKernelGradientNorm q.1 q.2 + C₁ / ρ * heatKernelPlus q) p

/-- The gradient norm of the heat kernel is nonnegative. -/
theorem heatKernelGradientNorm_nonneg_all (y : Vec3) (t : ℝ) : 0 ≤ heatKernelGradientNorm y t :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- The majorant is nonnegative. -/
theorem serrinHeatMajorant_nonneg {ρ C₁ : ℝ} (hρ : 0 < ρ) (hC₁ : 0 ≤ C₁) (p : Vec3 × ℝ) :
    0 ≤ serrinHeatMajorant ρ C₁ p := by
  unfold serrinHeatMajorant
  refine indicator_nonneg (fun q _ => ?_) p
  have := heatKernelPlus_nonneg q
  have := heatKernelGradientNorm_nonneg_all q.1 q.2
  positivity

/-- The parabolic size `|y| + √t` is continuous. -/
theorem rhoTwo_continuous : Continuous (fun p : Vec3 × ℝ => rhoTwo p.1 p.2) := by
  unfold rhoTwo vec3EuclideanNorm
  fun_prop

/-- The majorant is integrable, with integral of size `ρ`. -/
theorem integrable_and_integral_serrinHeatMajorant {ρ C₁ : ℝ} (hρ : 0 < ρ) (hC₁ : 0 ≤ C₁) :
    Integrable (serrinHeatMajorant ρ C₁) ∧
      ∫ p, serrinHeatMajorant ρ C₁ p ≤ (300000 + 9000 * C₁) * ρ := by
  set S : Set (Vec3 × ℝ) := {q : Vec3 × ℝ | vec3EuclideanNorm q.1 ≤ ρ ∧ 0 < q.2 ∧ q.2 ≤ ρ ^ 2}
    with hS
  set R : Set (Vec3 × ℝ) := {p | rhoTwo p.1 p.2 < 3 * ρ} with hR
  set St : Set (Vec3 × ℝ) := univ ×ˢ Ioc 0 ((3 * ρ) ^ 2) with hSt
  have hRm : MeasurableSet R := (isOpen_lt rhoTwo_continuous continuous_const).measurableSet
  have hSm : MeasurableSet S := by
    have hc : Continuous (fun q : Vec3 × ℝ => vec3EuclideanNorm q.1) := by
      unfold vec3EuclideanNorm; fun_prop
    exact (measurableSet_le hc.measurable measurable_const).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const))
  have hSR : S ⊆ R := by
    intro q hq
    have h1 : Real.sqrt q.2 ≤ ρ := by
      rw [Real.sqrt_le_left hρ.le]; exact hq.2.2
    change vec3EuclideanNorm q.1 + Real.sqrt q.2 < 3 * ρ
    linarith only [hq.1, h1, hρ]
  -- integrability of the two kernels on the strip and on `R`
  have hT : 0 < (3 * ρ) ^ 2 := by positivity
  have hG1 : IntegrableOn (fun q : Vec3 × ℝ => heatKernelGradientNorm q.1 q.2) St := by
    have := heatKernelGradientNorm_integrable_prod hT
    have e : (volume : Measure (Vec3 × ℝ)).restrict (univ ×ˢ Ioc 0 ((3 * ρ) ^ 2)) =
        (volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioc 0 ((3 * ρ) ^ 2))) := by
      rw [← Measure.restrict_univ (μ := (volume : Measure Vec3)), Measure.prod_restrict]
      rfl
    rw [hSt, IntegrableOn, e]
    exact this
  have hG2 : IntegrableOn (fun q : Vec3 × ℝ => heatKernelPlus q) St :=
    heatKernelPlus_integrableOn_time
  have hRSt : ∀ q ∈ R \ St, q.2 ≤ 0 := by
    intro q ⟨hqR, hqS⟩
    by_contra hpos'
    have hpos : 0 < q.2 := lt_of_not_ge hpos'
    apply hqS
    refine ⟨mem_univ _, hpos, ?_⟩
    have h1 : Real.sqrt q.2 < 3 * ρ := by
      have := vec3EuclideanNorm_nonneg q.1
      have hq : vec3EuclideanNorm q.1 + Real.sqrt q.2 < 3 * ρ := hqR
      linarith only [this, hq]
    have h2 := (Real.sqrt_lt' (by positivity)).mp h1
    exact h2.le
  have hR1 : IntegrableOn (fun q : Vec3 × ℝ => heatKernelGradientNorm q.1 q.2) R :=
    hG1.of_forall_sdiff_eq_zero hRm (fun q hq => by
      unfold heatKernelGradientNorm heatKernelSpaceDerivative
      simp [not_lt.mpr (hRSt q hq)])
  have hR2 : IntegrableOn (fun q : Vec3 × ℝ => heatKernelPlus q) R :=
    hG2.of_forall_sdiff_eq_zero hRm (fun q hq => heatKernelPlus_eq_zero_of_nonpos (hRSt q hq))
  have hF : IntegrableOn (fun q : Vec3 × ℝ => heatKernelGradientNorm q.1 q.2 +
      C₁ / ρ * heatKernelPlus q) R := hR1.add (hR2.const_mul _)
  refine ⟨(integrable_indicator_iff hSm).mpr (hF.mono_set hSR), ?_⟩
  have hB1 : ∫ q in R, heatKernelGradientNorm q.1 q.2 ≤ 100000 * (3 * ρ) :=
    heatKernelGradientNorm_integral_rho_lt_le (R := 3 * ρ) (by positivity)
  have hB2 : ∫ q in R, heatKernelPlus q ≤ 1000 * (3 * ρ) ^ 2 :=
    heatKernelPlus_integral_rho_lt_le (R := 3 * ρ) (by positivity)
  have hnn : ∀ q, 0 ≤ heatKernelGradientNorm q.1 q.2 + C₁ / ρ * heatKernelPlus q := by
    intro q
    have := heatKernelPlus_nonneg q
    have := heatKernelGradientNorm_nonneg_all q.1 q.2
    positivity
  calc ∫ p, serrinHeatMajorant ρ C₁ p
      = ∫ q in S, (heatKernelGradientNorm q.1 q.2 + C₁ / ρ * heatKernelPlus q) := by
        unfold serrinHeatMajorant
        exact integral_indicator hSm
    _ ≤ ∫ q in R, (heatKernelGradientNorm q.1 q.2 + C₁ / ρ * heatKernelPlus q) :=
        setIntegral_mono_set hF (Filter.Eventually.of_forall (fun q => hnn q))
          (Filter.Eventually.of_forall hSR)
    _ = (∫ q in R, heatKernelGradientNorm q.1 q.2) + C₁ / ρ * ∫ q in R, heatKernelPlus q := by
        rw [integral_add hR1 (hR2.const_mul _)]
        congr 1
        exact integral_const_mul _ _
    _ ≤ 100000 * (3 * ρ) + C₁ / ρ * (1000 * (3 * ρ) ^ 2) := by
        gcongr
    _ = (300000 + 9000 * C₁) * ρ := by
        field_simp
        ring

/-- The spatial derivative of the cut-off heat weight is integrable before the time `s`, with
integral of size `ρ`. -/
theorem serrinHeatWeight_spatialPartial_integral : ∃ C : ℝ, 0 < C ∧ ∀ (x : Vec3) (s ρ : ℝ),
    0 < ρ → ρ ≤ 1 → ∀ j : Fin 3,
      IntegrableOn (fun z => spatialPartial (serrinHeatWeight x s ρ) j z)
        {z : ParabolicPoint | z.2 < s} ∧
      ∫ z in {z : ParabolicPoint | z.2 < s}, |spatialPartial (serrinHeatWeight x s ρ) j z| ≤
        C * ρ := by
  obtain ⟨C₁, hC₁, hC₁b⟩ := abs_spatialPartial_serrinCutoff_le
  refine ⟨300000 + 9000 * C₁ + 1, by positivity, fun x s ρ hρ _ j => ?_⟩
  set a : Vec3 × ℝ := (x, s) with ha
  obtain ⟨hMi, hMint⟩ := integrable_and_integral_serrinHeatMajorant hρ hC₁
  have hMa : Integrable (fun z : Vec3 × ℝ => serrinHeatMajorant ρ C₁ (a - z)) :=
    ((measurePreserving_sub_left_prod a).integrable_comp_emb
      (measurableEmbedding_subLeft a)).mpr hMi
  set U : Set (Vec3 × ℝ) := {z | z.2 < s} with hU
  have hUm : MeasurableSet U := measurableSet_lt measurable_snd measurable_const
  have hbound : ∀ z : Vec3 × ℝ, z.2 < s →
      |spatialPartial (serrinHeatWeight x s ρ) j z| ≤ serrinHeatMajorant ρ C₁ (a - z) := by
    intro z hz
    by_cases hw : z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s
    · have ht : 0 < s - z.2 := by linarith only [hz]
      have hmem : a - z ∈ {q : Vec3 × ℝ | vec3EuclideanNorm q.1 ≤ ρ ∧ 0 < q.2 ∧ q.2 ≤ ρ ^ 2} := by
        refine ⟨?_, ht, ?_⟩
        · change vec3EuclideanNorm (x - z.1) ≤ ρ
          rw [← vec3EuclideanNorm_neg, neg_sub]
          exact hw.1
        · change s - z.2 ≤ ρ ^ 2
          linarith only [hw.2.1]
      unfold serrinHeatMajorant
      rw [indicator_of_mem hmem]
      change _ ≤ heatKernelGradientNorm (x - z.1) (s - z.2) +
        C₁ / ρ * heatKernelPlus ((x - z.1, s - z.2) : ParabolicPoint)
      rw [spatialPartial_serrinHeatWeight_eq x hρ z hz j]
      have hD : |heatKernelSpaceDerivative (x - z.1) (s - z.2) j| ≤
          heatKernelGradientNorm (x - z.1) (s - z.2) := by
        unfold heatKernelGradientNorm
        exact Finset.single_le_sum (f := fun i => |heatKernelSpaceDerivative (x - z.1) (s - z.2) i|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      have hχ := abs_serrinCutoff_le_one x s ρ z
      have hdχ := hC₁b x s ρ hρ z j
      have hΓ : 0 ≤ heatKernel (x - z.1) (s - z.2) := heatKernel_nonneg _ _
      have hG0 := heatKernelGradientNorm_nonneg_all (x - z.1) (s - z.2)
      have hP : heatKernelPlus ((x - z.1, s - z.2) : ParabolicPoint) =
          heatKernel (x - z.1) (s - z.2) := heatKernelPlus_eq_heatKernel _
      calc |-heatKernelSpaceDerivative (x - z.1) (s - z.2) j * serrinCutoff x s ρ z +
            heatKernel (x - z.1) (s - z.2) * spatialPartial (serrinCutoff x s ρ) j z|
          ≤ |heatKernelSpaceDerivative (x - z.1) (s - z.2) j| * |serrinCutoff x s ρ z| +
            heatKernel (x - z.1) (s - z.2) * |spatialPartial (serrinCutoff x s ρ) j z| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hΓ]
        _ ≤ heatKernelGradientNorm (x - z.1) (s - z.2) * 1 +
            heatKernel (x - z.1) (s - z.2) * (C₁ / ρ) := by
            gcongr
        _ = heatKernelGradientNorm (x - z.1) (s - z.2) +
            C₁ / ρ * heatKernelPlus ((x - z.1, s - z.2) : ParabolicPoint) := by
            linear_combination (-(C₁ / ρ)) * hP
    · rw [(spatialPartial_serrinKernels_eq_zero x hρ hz hw j).1, abs_zero]
      exact serrinHeatMajorant_nonneg hρ hC₁ _
  have hmeas : AEStronglyMeasurable (fun z : Vec3 × ℝ =>
      spatialPartial (serrinHeatWeight x s ρ) j z) (volume.restrict U) := by
    have hc := continuousOn_spatialPartial_serrinHeatWeight x (s := s) hρ j
    have hUeq : spaceTimeSet univ (Iio s) = U := by
      ext z; exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩
    rw [hUeq] at hc
    exact hc.aestronglyMeasurable hUm
  have hae : ∀ᵐ z : Vec3 × ℝ ∂(volume.restrict U),
      ‖spatialPartial (serrinHeatWeight x s ρ) j z‖ ≤ serrinHeatMajorant ρ C₁ (a - z) :=
    (ae_restrict_iff' hUm).mpr (Filter.Eventually.of_forall (fun z hz => hbound z hz))
  have hint : IntegrableOn (fun z : Vec3 × ℝ => spatialPartial (serrinHeatWeight x s ρ) j z) U :=
    Integrable.mono' hMa.integrableOn hmeas hae
  refine ⟨hint, ?_⟩
  have h1 : ∫ z in U, |spatialPartial (serrinHeatWeight x s ρ) j z| ≤
      ∫ z in U, serrinHeatMajorant ρ C₁ (a - z) :=
    setIntegral_mono_on hint.abs hMa.integrableOn hUm (fun z hz => hbound z hz)
  have h2 : ∫ z in U, serrinHeatMajorant ρ C₁ (a - z) ≤ ∫ z, serrinHeatMajorant ρ C₁ (a - z) :=
    setIntegral_le_integral hMa (Filter.Eventually.of_forall
      (fun z => serrinHeatMajorant_nonneg hρ hC₁ _))
  have h3 := integral_comp_sub_left_prod (serrinHeatMajorant ρ C₁) a
  have h4 : (300000 + 9000 * C₁) * ρ ≤ (300000 + 9000 * C₁ + 1) * ρ := by nlinarith only [hρ]
  exact h1.trans (h2.trans (h3.le.trans (hMint.trans h4)))

end CIV
