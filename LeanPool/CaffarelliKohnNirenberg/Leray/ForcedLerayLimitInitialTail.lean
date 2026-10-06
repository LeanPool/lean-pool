/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedTransportField
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# The spatial tail of the mollified initial datum

`eq:forced-initial-tail` in `lem:forced-tails`: the regularizing kernel is
nonnegative, has total mass one and is supported in the ball of radius
`ε ≤ 1`, so by the Cauchy–Schwarz inequality for the kernel measure, Tonelli
and translation invariance, the exterior energy of `J_ε a` outside the ball of
radius `R` is at most the exterior energy of `a` outside the ball of radius
`R - 1`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Convolution
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The physical regularizing kernel is nonnegative, has total mass one, and
vanishes outside the Euclidean ball of radius `ε`. -/
private theorem forcedInitialTail_kernel (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    (∀ y, 0 ≤ forcedTransportKernel ρ ε hε y) ∧
    ∫⁻ y : Vec3, ENNReal.ofReal (forcedTransportKernel ρ ε hε y) = 1 ∧
    ∀ y, forcedTransportKernel ρ ε hε y ≠ 0 → vec3EuclideanNorm y < ε := by
  have hnn : ∀ y, 0 ≤ forcedTransportKernel ρ ε hε y := fun y =>
    regMollifierKernel_nonneg ρ ε hε _
  refine ⟨hnn, ?_, fun y hy => ?_⟩
  · have hint : Integrable (forcedTransportKernel ρ ε hε) :=
      (forcedTransportKernel_contDiff ρ ε hε).continuous.integrable_of_hasCompactSupport
        (forcedTransportKernel_hasCompactSupport ρ ε hε)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn)]
    have h1 : ∫ y : Vec3, forcedTransportKernel ρ ε hε y = 1 := by
      have hEmb : MeasurableEmbedding (WithLp.toLp 2 : Vec3 → L2Vec3) :=
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.measurableEmbedding
      have h := vec3ToL2Vec3_measurePreserving.integral_comp hEmb (regMollifierKernel ρ ε hε)
      rw [← regMollifierKernel_integral_eq_one ρ ε hε, ← h]
      rfl
    rw [h1, ENNReal.ofReal_one]
  · have hy' : ρ.rho (ε⁻¹ • WithLp.toLp 2 y) ≠ 0 := by
      intro h0
      apply hy
      change (ε ^ 3)⁻¹ * ρ.rho (ε⁻¹ • WithLp.toLp 2 y) = 0
      rw [h0, mul_zero]
    have hmem := ρ.support_unit (subset_tsupport _ (Function.mem_support.2 hy'))
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hε)] at hmem
    rw [vec3EuclideanNorm_eq_l2]
    have := (inv_mul_lt_iff₀ hε).1 hmem
    linarith only [this]

/-- `eq:forced-initial-tail` in lower-integral form: for `0 < ε ≤ 1` and every
`R`, the exterior energy of the mollified datum `J_ε a` outside the ball of
radius `R` is at most the exterior energy of `a` outside the ball of radius
`R - 1`. -/
theorem forcedLerayLimit_initialTail_lintegral (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (a : Vec3 → Vec3) (ha : MemLp a 2 volume) (R : ℝ) :
    ∫⁻ x in {x : Vec3 | R < vec3EuclideanNorm x},
        ∑ i : Fin 3, ‖regUniformMollifiedInitial ρ ε hε a x i‖ₑ ^ (2 : ℝ) ≤
      ∫⁻ x in {x : Vec3 | R - 1 < vec3EuclideanNorm x},
        ∑ i : Fin 3, ‖a x i‖ₑ ^ (2 : ℝ) := by
  obtain ⟨hnn, hmass, hsupp⟩ := forcedInitialTail_kernel ρ ε hε
  let k : Vec3 → ℝ := forcedTransportKernel ρ ε hε
  let kE : Vec3 → ℝ≥0∞ := fun y => ENNReal.ofReal (k y)
  have hkm : Measurable k := (forcedTransportKernel_contDiff ρ ε hε).continuous.measurable
  have hkEm : Measurable kE := ENNReal.measurable_ofReal.comp hkm
  let A : Vec3 → ℝ≥0∞ := fun z => ∑ i : Fin 3, ‖a z i‖ₑ ^ (2 : ℝ)
  have hAi : ∀ i : Fin 3, AEMeasurable (fun z : Vec3 => ‖a z i‖ₑ ^ (2 : ℝ)) volume := fun i =>
    ((ha.eval i).aestronglyMeasurable.aemeasurable.enorm).pow_const _
  have hAm : AEMeasurable A volume := Finset.aemeasurable_fun_sum _ fun i _ => hAi i
  let ext : ℝ → Set Vec3 := fun r => {x : Vec3 | r < vec3EuclideanNorm x}
  have hext : ∀ r, MeasurableSet (ext r) := fun r =>
    measurableSet_lt measurable_const continuous_vec3EuclideanNorm.measurable
  have h22 : (2 : ℝ).HolderConjugate 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  -- the pointwise Cauchy–Schwarz inequality for the kernel
  have hcomp : ∀ (x : Vec3) (i : Fin 3),
      ‖regUniformMollifiedInitial ρ ε hε a x i‖ₑ ^ (2 : ℝ) ≤
        ∫⁻ y, kE y * ‖a (x - y) i‖ₑ ^ (2 : ℝ) := by
    intro x i
    have hshift : AEMeasurable (fun y : Vec3 => ‖a (x - y) i‖ₑ) volume :=
      ((ha.eval i).aestronglyMeasurable.aemeasurable.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_left_of_right_invariant volume x)).enorm
    have heq := forcedTransport_component_eq (ρ := ρ) hε ha x i
    rw [convolution_def] at heq
    have h1 : ‖regUniformMollifiedInitial ρ ε hε a x i‖ₑ ≤
        ∫⁻ y, kE y * ‖a (x - y) i‖ₑ := by
      rw [heq]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      refine lintegral_congr fun y => ?_
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, enorm_mul]
      rw [Real.enorm_eq_ofReal (hnn y)]
    have hsplit : (fun y => kE y * ‖a (x - y) i‖ₑ) =
        (fun y => kE y ^ (1 / 2 : ℝ)) * fun y => kE y ^ (1 / 2 : ℝ) * ‖a (x - y) i‖ₑ := by
      funext y
      simp only [Pi.mul_apply]
      rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num
    have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq volume h22
      (hkEm.pow_const (1 / 2 : ℝ)).aemeasurable
      ((hkEm.pow_const (1 / 2 : ℝ)).aemeasurable.mul hshift)
    have hk1 : (∫⁻ y, (kE y ^ (1 / 2 : ℝ)) ^ (2 : ℝ)) = 1 := by
      rw [← hmass]
      refine lintegral_congr fun y => ?_
      rw [← ENNReal.rpow_mul]
      norm_num
      rfl
    have hk2 : (∫⁻ y, (kE y ^ (1 / 2 : ℝ) * ‖a (x - y) i‖ₑ) ^ (2 : ℝ)) =
        ∫⁻ y, kE y * ‖a (x - y) i‖ₑ ^ (2 : ℝ) := by
      refine lintegral_congr fun y => ?_
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
      norm_num
    simp only [Pi.mul_apply] at h2
    rw [hk1, hk2, ENNReal.one_rpow, one_mul] at h2
    have h12 : ‖regUniformMollifiedInitial ρ ε hε a x i‖ₑ ≤
        (∫⁻ y, kE y * ‖a (x - y) i‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
      h1.trans (le_of_eq_of_le (lintegral_congr fun y => by
        simpa only [Pi.mul_apply] using congrFun hsplit y) h2)
    have h3 := ENNReal.rpow_le_rpow h12 (by norm_num : (0 : ℝ) ≤ 2)
    rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one] at h3
    exact h3
  have hpoint : ∀ x : Vec3,
      ∑ i : Fin 3, ‖regUniformMollifiedInitial ρ ε hε a x i‖ₑ ^ (2 : ℝ) ≤
        ∫⁻ y, kE y * A (x - y) := by
    intro x
    have hmi : ∀ i : Fin 3, AEMeasurable (fun y => kE y * ‖a (x - y) i‖ₑ ^ (2 : ℝ)) volume :=
      fun i => hkEm.aemeasurable.mul
        ((((ha.eval i).aestronglyMeasurable.aemeasurable.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_left_of_right_invariant volume x)).enorm).pow_const _)
    calc ∑ i : Fin 3, ‖regUniformMollifiedInitial ρ ε hε a x i‖ₑ ^ (2 : ℝ)
        ≤ ∑ i : Fin 3, ∫⁻ y, kE y * ‖a (x - y) i‖ₑ ^ (2 : ℝ) :=
          Finset.sum_le_sum fun i _ => hcomp x i
      _ = ∫⁻ y, kE y * A (x - y) := by
          rw [← lintegral_finsetSum' _ fun i _ => hmi i]
          refine lintegral_congr fun y => ?_
          simp only [A, Finset.mul_sum]
  -- Tonelli and translation
  have hprodm : AEMeasurable (fun q : Vec3 × Vec3 => kE q.2 * A (q.1 - q.2))
      ((volume : Measure Vec3).prod volume) :=
    (hkEm.comp measurable_snd).aemeasurable.mul
      (hAm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant _ _))
  have hprodm' : AEMeasurable (Function.uncurry fun (x y : Vec3) => kE y * A (x - y))
      (((volume : Measure Vec3).restrict (ext R)).prod volume) :=
    hprodm.mono_ac (Measure.AbsolutelyContinuous.prod
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
      Measure.AbsolutelyContinuous.rfl)
  have htrans : ∀ y : Vec3, kE y * ∫⁻ x in ext R, A (x - y) ≤
      kE y * ∫⁻ z in ext (R - 1), A z := by
    intro y
    by_cases hy : k y = 0
    · simp [kE, hy]
    have hyε : vec3EuclideanNorm y < 1 := (hsupp y hy).trans_le hε1
    refine mul_le_mul' le_rfl ?_
    rw [← lintegral_indicator (hext R), ← lintegral_indicator (hext (R - 1))]
    have hshift := lintegral_add_right_eq_self
      (μ := (volume : Measure Vec3)) ((ext R).indicator fun x => A (x - y)) y
    rw [← hshift]
    refine lintegral_mono fun z => ?_
    by_cases hz : z + y ∈ ext R
    · have hz' : z ∈ ext (R - 1) := by
        have h1 : R < vec3EuclideanNorm (z + y) := hz
        have h2 := CKN.Foundation.Parabolic.vec3EuclideanNorm_add_le z y
        change R - 1 < vec3EuclideanNorm z
        linarith only [h1, h2, hyε]
      rw [indicator_of_mem hz, indicator_of_mem hz', add_sub_cancel_right]
    · rw [indicator_of_notMem hz]
      exact bot_le
  calc ∫⁻ x in ext R, ∑ i : Fin 3, ‖regUniformMollifiedInitial ρ ε hε a x i‖ₑ ^ (2 : ℝ)
      ≤ ∫⁻ x in ext R, ∫⁻ y, kE y * A (x - y) := lintegral_mono fun x => hpoint x
    _ = ∫⁻ y, ∫⁻ x in ext R, kE y * A (x - y) := lintegral_lintegral_swap hprodm'
    _ = ∫⁻ y, kE y * ∫⁻ x in ext R, A (x - y) := by
        refine lintegral_congr fun y => ?_
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ∫⁻ y, kE y * ∫⁻ z in ext (R - 1), A z := lintegral_mono htrans
    _ = ∫⁻ z in ext (R - 1), A z := by
        rw [lintegral_mul_const _ hkEm, hmass, one_mul]

/-- The integral of the squared Euclidean norm of a vector field over a set is
the real part of the lower integral of the sum of the squared component
norms. -/
private theorem forcedInitialTail_integral_eq {S : Set Vec3} {g : Vec3 → Vec3}
    (hg : AEStronglyMeasurable g (volume.restrict S)) :
    ∫ x in S, vec3EuclideanNorm (g x) ^ (2 : ℕ) =
      (∫⁻ x in S, ∑ i : Fin 3, ‖g x i‖ₑ ^ (2 : ℝ)).toReal := by
  have hm : AEStronglyMeasurable (fun x => vec3EuclideanNorm (g x) ^ (2 : ℕ))
      (volume.restrict S) :=
    (continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hg).pow 2
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => by positivity) hm]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [vec3EuclideanNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _),
    ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]

/-- `eq:forced-initial-tail`: for `0 < ε ≤ 1` and every `R`,
`∫_{|x|>R} |J_ε a|² ≤ ∫_{|x|>R-1} |a|²`. -/
theorem forcedLerayLimit_initialTail (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (a : Vec3 → Vec3) (ha : MemLp a 2 volume) (R : ℝ) :
    ∫ x in {x : Vec3 | R < vec3EuclideanNorm x},
        vec3EuclideanNorm (regUniformMollifiedInitial ρ ε hε a x) ^ (2 : ℕ) ≤
      ∫ x in {x : Vec3 | R - 1 < vec3EuclideanNorm x}, vec3EuclideanNorm (a x) ^ (2 : ℕ) := by
  have hJm : Measurable (regUniformMollifiedInitial ρ ε hε a) :=
    measurable_pi_iff.2 fun i => (forcedTransport_contDiff (ρ := ρ) hε ha i).continuous.measurable
  rw [forcedInitialTail_integral_eq hJm.aestronglyMeasurable,
    forcedInitialTail_integral_eq ha.aestronglyMeasurable.restrict]
  refine ENNReal.toReal_mono ?_ (forcedLerayLimit_initialTail_lintegral ρ ε hε hε1 a ha R)
  refine ne_top_of_le_ne_top ?_ (setLIntegral_le_lintegral _ _)
  rw [lintegral_finsetSum' _ fun i _ =>
    ((ha.eval i).aestronglyMeasurable.aemeasurable.enorm).pow_const _]
  refine ENNReal.sum_ne_top.2 fun i _ => ?_
  rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' (by norm_num : (0 : ℝ) < 2)]
  have h := (ha.eval i).eLpNorm_ne_top
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) (ha.eval i).aestronglyMeasurable,
    ENNReal.toReal_ofNat] at h
  exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) h

end CKN.Leray

end
