/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.NewtonianRepresentation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Interior
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.HessianL2
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SpatialDerivSupport
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# The singular integration by parts for the Newtonian kernel

For a smooth compactly supported `F : Vec3 → ℝ`, moving one spatial derivative across the
Newtonian kernel singularity,
`∫ N(x - y) ∂ₗF(y) dy = ∫ ∂ₗN(x - y) F(y) dy`,
and the resulting representation of the gradient of a smooth compactly supported `v` by the
Newtonian potential of its Laplacian gradient,
`∂ₗv(x) = -∫ ∂ₗN(x - y) Δv(y) dy`.
Both kernels here are absolutely, not merely improperly, integrable in three dimensions, so no
principal value or excision argument is needed. The route regularizes the kernel by
`N_ε(z) = (4π)⁻¹ (|z|² + ε²)^{-1/2}`, which is smooth on all of `Vec3`, applies the ordinary
(non-singular) integration by parts identity to `N_ε`, and passes to the limit `ε → 0` along the
sequence `ε_n = 1/(n+1)` by dominated convergence, using that `|N_ε| ≤ N` and `|∂ₗN_ε| ≤ |∂ₗN|`
pointwise away from the singularity. It is the elliptic analogue of the heat-kernel integration
by parts in the
interior estimates of `lem:aniso:annulus`.
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open CKN.Foundation.Parabolic CKN CKN.Foundation.Heat

noncomputable section

namespace CIV



/-! ## Part 1: the regularized kernel -/

@[expose] private def regQ (ε : ℝ) (z : Vec3) : ℝ := (∑ i : Fin 3, z i ^ 2) + ε ^ 2

@[expose] private def regKernel (ε : ℝ) (z : Vec3) : ℝ := (4 * Real.pi)⁻¹ * (regQ ε z) ^ (-(1 :
  ℝ) / 2)

private theorem regQ_pos {ε : ℝ} (hε : ε ≠ 0) (z : Vec3) : 0 < regQ ε z := by
  have h1 : 0 ≤ ∑ i : Fin 3, z i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h2 : 0 < ε ^ 2 := by positivity
  unfold regQ
  linarith only [h1, h2]

private theorem hasFDerivAt_sumSq (z : Vec3) :
    HasFDerivAt (fun w : Vec3 => ∑ i : Fin 3, w i ^ 2)
      (∑ i : Fin 3, (2 * z i) • (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)) z := by
  have hfun : (fun w : Vec3 => ∑ i : Fin 3, w i ^ 2) =
      ∑ i : Fin 3, (fun w : Vec3 => w i * w i) := by
    funext w
    simp [pow_two]
  rw [hfun]
  apply HasFDerivAt.sum
  intro i _
  have hprod := (hasFDerivAt_apply (𝕜 := ℝ) i z).mul (hasFDerivAt_apply (𝕜 := ℝ) i z)
  convert hprod using 1
  ext v
  simp [smul_eq_mul]
  ring

private theorem hasFDerivAt_regQ (ε : ℝ) (z : Vec3) :
    HasFDerivAt (regQ ε)
      (∑ i : Fin 3, (2 * z i) • (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)) z :=
  (hasFDerivAt_sumSq z).add_const (ε ^ 2)

private theorem contDiff_regQ (ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (regQ ε) := by
  unfold regQ
  fun_prop

private theorem contDiff_regKernel {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (regKernel ε) := by
  unfold regKernel
  exact contDiff_const.mul ((contDiff_regQ ε).rpow_const_of_ne (fun z => (regQ_pos hε z).ne'))

private theorem hasFDerivAt_regKernel {ε : ℝ} (hε : ε ≠ 0) (z : Vec3) :
    HasFDerivAt (regKernel ε)
      ((4 * Real.pi)⁻¹ •
        ((-(1 : ℝ) / 2 * (regQ ε z) ^ (-(1 : ℝ) / 2 - 1)) •
          ∑ i : Fin 3, (2 * z i) • (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ))) z := by
  have hq : HasFDerivAt (fun w : Vec3 => (regQ ε w) ^ (-(1 : ℝ) / 2))
      ((-(1 : ℝ) / 2 * (regQ ε z) ^ (-(1 : ℝ) / 2 - 1)) •
        ∑ i : Fin 3, (2 * z i) • (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)) z :=
    (hasFDerivAt_regQ ε z).rpow_const (p := -(1 : ℝ) / 2) (Or.inl (regQ_pos hε z).ne')
  exact hq.const_mul _

private theorem spatialDeriv_regKernel_formula {ε : ℝ} (hε : ε ≠ 0) (z : Vec3) (i : Fin 3) :
    spatialDeriv (regKernel ε) i z = -(4 * Real.pi)⁻¹ * z i * (regQ ε z) ^ (-(3 : ℝ) / 2) := by
  have hdirect := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i))
    (hasFDerivAt_regKernel hε z).fderiv
  change spatialDeriv (regKernel ε) i z = _ at hdirect
  rw [hdirect]
  simp only [smul_apply, sum_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [basisVec_apply, hj]) (by simp)]
  simp [basisVec_apply]
  ring_nf

/-! ## Part 2: comparison with the unregularized kernel -/

private theorem regQ_eq_q_add (ε : ℝ) (z : Vec3) : regQ ε z = q z + ε ^ 2 := rfl

private theorem sumSq_le_regQ (ε : ℝ) (z : Vec3) : (∑ i : Fin 3, z i ^ 2) ≤ regQ ε z := by
  unfold regQ
  linarith only [sq_nonneg ε]

private theorem regKernel_eq_inv_sqrt {ε : ℝ} (hε : ε ≠ 0) (z : Vec3) :
    regKernel ε z = (4 * Real.pi * Real.sqrt (regQ ε z))⁻¹ := by
  have hx := regQ_pos hε z
  unfold regKernel
  rw [show (4 * Real.pi * Real.sqrt (regQ ε z))⁻¹ =
      (4 * Real.pi)⁻¹ * (Real.sqrt (regQ ε z))⁻¹ from mul_inv _ _,
    Real.sqrt_eq_rpow, ← Real.rpow_neg hx.le]
  congr 2
  ring

private theorem regKernel_nonneg (ε : ℝ) (z : Vec3) : 0 ≤ regKernel ε z := by
  unfold regKernel regQ
  positivity

private theorem abs_regKernel_le_newtonianKernel {ε : ℝ} (hε : ε ≠ 0) {z : Vec3} (hz : z ≠ 0) :
    |regKernel ε z| ≤ |newtonianKernel z| := by
  rw [abs_of_nonneg (regKernel_nonneg ε z)]
  have hzpos : 0 < vec3EuclideanNorm z := by
    rw [vec3EuclideanNorm_eq_l2, norm_pos_iff]
    intro hz0
    exact hz ((WithLp.toLp_eq_zero 2).mp hz0)
  have hnn : 0 ≤ newtonianKernel z := by
    unfold newtonianKernel
    positivity
  rw [abs_of_nonneg hnn, regKernel_eq_inv_sqrt hε z]
  unfold newtonianKernel
  have hle : vec3EuclideanNorm z ≤ Real.sqrt (regQ ε z) := by
    have hsq : vec3EuclideanNorm z ^ 2 ≤ regQ ε z := by
      unfold vec3EuclideanNorm
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (z i)))]
      exact sumSq_le_regQ ε z
    calc vec3EuclideanNorm z = Real.sqrt (vec3EuclideanNorm z ^ 2) :=
          (Real.sqrt_sq (vec3EuclideanNorm_nonneg z)).symm
      _ ≤ Real.sqrt (regQ ε z) := Real.sqrt_le_sqrt hsq
  have hpossqrt : 0 < Real.sqrt (regQ ε z) := lt_of_lt_of_le hzpos hle
  rw [inv_eq_one_div]
  apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 4 * Real.pi * vec3EuclideanNorm z)
  exact mul_le_mul_of_nonneg_left hle (by positivity)

private theorem abs_neg_mul_mul_rpow_nonneg (a b : ℝ) {X : ℝ} (hX : 0 ≤ X) :
    |(-a * b * X)| = |a| * |b| * X := by
  rw [show -a * b * X = -(a * b * X) from by ring, abs_neg, abs_mul, abs_mul,
    abs_of_nonneg hX]

private theorem abs_spatialDeriv_regKernel_le {ε : ℝ} (hε : ε ≠ 0) {z : Vec3} (hz : z ≠ 0)
    (i : Fin 3) :
    |spatialDeriv (regKernel ε) i z| ≤ |spatialDeriv newtonianKernel i z| := by
  rw [spatialDeriv_regKernel_formula hε z i, newtonianKernel_spatialDeriv_formula hz i]
  have hq0 : 0 < q z := q_pos hz
  have hqle : q z ≤ regQ ε z := by rw [regQ_eq_q_add]; linarith only [sq_nonneg ε]
  have hle : (regQ ε z) ^ (-(3 : ℝ) / 2) ≤ (q z) ^ (-(3 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos hq0 hqle (by norm_num)
  have hnn1 : 0 ≤ (regQ ε z) ^ (-(3 : ℝ) / 2) := Real.rpow_nonneg (regQ_pos hε z).le _
  have hnn2 : 0 ≤ (q z) ^ (-(3 : ℝ) / 2) := Real.rpow_nonneg hq0.le _
  rw [abs_neg_mul_mul_rpow_nonneg (4 * Real.pi)⁻¹ (z i) hnn1,
    abs_neg_mul_mul_rpow_nonneg (4 * Real.pi)⁻¹ (z i) hnn2]
  exact mul_le_mul_of_nonneg_left hle (by positivity)

private theorem continuous_regKernel {ε : ℝ} (hε : ε ≠ 0) : Continuous (regKernel ε) :=
  (contDiff_regKernel hε).continuous

private theorem continuous_spatialDeriv_regKernel {ε : ℝ} (hε : ε ≠ 0) (i : Fin 3) :
    Continuous (spatialDeriv (regKernel ε) i) :=
  (contDiff_spatialDeriv_smooth (contDiff_regKernel hε) i).continuous

/-! ## Part 3: the regularized integration by parts identity -/

private theorem hasFDerivAt_shift_sub {g : Vec3 → ℝ} (hg : Differentiable ℝ g) (x y : Vec3) :
    HasFDerivAt (fun w : Vec3 => g (x - w))
      ((fderiv ℝ g (x - y)).comp (-(ContinuousLinearMap.id ℝ Vec3))) y :=
  (hg (x - y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)

private theorem differentiableAt_shift_sub {g : Vec3 → ℝ} (hg : Differentiable ℝ g) (x y : Vec3) :
    DifferentiableAt ℝ (fun w : Vec3 => g (x - w)) y :=
  (hasFDerivAt_shift_sub hg x y).differentiableAt

private theorem fderiv_shift_sub {g : Vec3 → ℝ} (hg : Differentiable ℝ g) (x y : Vec3)
    (l : Fin 3) :
    fderiv ℝ (fun w : Vec3 => g (x - w)) y (basisVec l) = -spatialDeriv g l (x - y) := by
  rw [(hasFDerivAt_shift_sub hg x y).fderiv]
  simp [spatialDeriv]

private theorem regularized_ibp {F : Vec3 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (x : Vec3) (l : Fin 3) {ε : ℝ} (hε : ε ≠ 0) :
    ∫ y : Vec3, regKernel ε (x - y) * spatialDeriv F l y =
      ∫ y : Vec3, spatialDeriv (regKernel ε) l (x - y) * F y := by
  have hfdiff : Differentiable ℝ (regKernel ε) := (contDiff_regKernel hε).differentiable (by simp)
  have hgdiff : Differentiable ℝ F := hF.differentiable (by simp)
  have hf'g : Integrable (fun y : Vec3 =>
      fderiv ℝ (fun w : Vec3 => regKernel ε (x - w)) y (basisVec l) * F y) := by
    have heq : (fun y : Vec3 =>
        fderiv ℝ (fun w : Vec3 => regKernel ε (x - w)) y (basisVec l) * F y) =
        fun y : Vec3 => -(spatialDeriv (regKernel ε) l (x - y) * F y) := by
      funext y
      rw [fderiv_shift_sub hfdiff x y l]
      ring
    rw [heq]
    apply Integrable.neg
    apply Continuous.integrable_of_hasCompactSupport
    · exact ((continuous_spatialDeriv_regKernel hε l).comp
        (continuous_const.sub continuous_id)).mul hF.continuous
    · exact HasCompactSupport.mul_left hFc
  have hfg' : Integrable (fun y : Vec3 => regKernel ε (x - y) * spatialDeriv F l y) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact ((continuous_regKernel hε).comp (continuous_const.sub continuous_id)).mul
        (contDiff_spatialDeriv_smooth hF l).continuous
    · exact HasCompactSupport.mul_left (hasCompactSupport_spatialDeriv hFc l)
  have hfg : Integrable (fun y : Vec3 => regKernel ε (x - y) * F y) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact ((continuous_regKernel hε).comp (continuous_const.sub continuous_id)).mul
        hF.continuous
    · exact HasCompactSupport.mul_left hFc
  have hmain := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun y : Vec3 => regKernel ε (x - y)) (g := F) (v := basisVec l)
    hf'g hfg' hfg
    (fun y _ => differentiableAt_shift_sub hfdiff x y)
    (fun y _ => hgdiff y)
  show ∫ y : Vec3, regKernel ε (x - y) * fderiv ℝ F y (basisVec l) =
      ∫ y : Vec3, spatialDeriv (regKernel ε) l (x - y) * F y
  rw [hmain, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [fderiv_shift_sub hfdiff x y l]
  ring

/-! ## Part 4: passing to the limit -/

private theorem locallyIntegrable_spatialDeriv_newtonianKernel (l : Fin 3) :
    LocallyIntegrable (fun z : Vec3 => spatialDeriv newtonianKernel l z) volume := by
  have hbound : ∀ᵐ z : Vec3 ∂volume, ‖spatialDeriv newtonianKernel l z‖ ≤
      (4 * Real.pi)⁻¹ * ‖z‖ ^ (-2 : ℝ) := by
    filter_upwards [Measure.ae_ne volume (0 : Vec3)] with z hz
    rw [Real.norm_eq_abs, show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg (norm_nonneg _),
      Real.rpow_natCast]
    exact newtonianKernel_spatialDeriv_size_bound hz l
  have hmeas : AEStronglyMeasurable (fun z : Vec3 => spatialDeriv newtonianKernel l z) volume :=
    (measurable_fderiv_apply_const ℝ newtonianKernel (basisVec l)).aestronglyMeasurable
  exact locallyIntegrable_of_norm_le_rpow (E := Vec3) (F := ℝ)
    (by change 1 ≤ Module.finrank ℝ (Fin 3 → ℝ); rw [Module.finrank_fin_fun]; norm_num)
    (by norm_num) hbound hmeas

private theorem locallyIntegrable_spatialDeriv_newtonianKernel_sub (x : Vec3) (l : Fin 3) :
    LocallyIntegrable (fun y : Vec3 => spatialDeriv newtonianKernel l (x - y)) volume := by
  have hmp := Measure.measurePreserving_sub_left (volume : Measure Vec3) x
  have hmap : Measure.map (fun y : Vec3 => x - y) volume = volume := hmp.map_eq
  have hmap' : LocallyIntegrable (fun z : Vec3 => spatialDeriv newtonianKernel l z)
      (Measure.map (Homeomorph.subLeft x) volume) := by
    change LocallyIntegrable (fun z : Vec3 => spatialDeriv newtonianKernel l z)
      (Measure.map (fun y : Vec3 => x - y) volume)
    rw [hmap]
    exact locallyIntegrable_spatialDeriv_newtonianKernel l
  have hcomp := (locallyIntegrable_map_homeomorph (Homeomorph.subLeft x)
    (f := fun z : Vec3 => spatialDeriv newtonianKernel l z)).1 hmap'
  change LocallyIntegrable (fun y : Vec3 => spatialDeriv newtonianKernel l (x - y)) volume at hcomp
  exact hcomp

private theorem newtonianKernel_eq_rpow {z : Vec3} (hz : z ≠ 0) :
    newtonianKernel z = (4 * Real.pi)⁻¹ * (q z) ^ (-(1 : ℝ) / 2) := by
  have hveq : vec3EuclideanNorm z = Real.sqrt (q z) := by unfold vec3EuclideanNorm q; rfl
  unfold newtonianKernel
  rw [hveq, one_div, show (4 * Real.pi * Real.sqrt (q z))⁻¹ =
      (4 * Real.pi)⁻¹ * (Real.sqrt (q z))⁻¹ from mul_inv _ _,
    Real.sqrt_eq_rpow, ← Real.rpow_neg (q_pos hz).le]
  congr 2
  ring

private theorem tendsto_regQ {ε : ℕ → ℝ} (hε0 : Tendsto ε atTop (𝓝 0)) (z : Vec3) :
    Tendsto (fun n => regQ (ε n) z) atTop (𝓝 (q z)) := by
  have h1 : Tendsto (fun n => (ε n) ^ 2) atTop (𝓝 (0 : ℝ)) := by simpa using hε0.pow 2
  have h2 := (tendsto_const_nhds (x := q z) (f := (atTop : Filter ℕ))).add h1
  simpa [regQ_eq_q_add] using h2

private theorem tendsto_regKernel {ε : ℕ → ℝ} (hε0 : Tendsto ε atTop (𝓝 0)) {z : Vec3}
    (hz : z ≠ 0) :
    Tendsto (fun n => regKernel (ε n) z) atTop (𝓝 (newtonianKernel z)) := by
  have hq : Tendsto (fun n => (regQ (ε n) z) ^ (-(1 : ℝ) / 2)) atTop
      (𝓝 ((q z) ^ (-(1 : ℝ) / 2))) :=
    (tendsto_regQ hε0 z).rpow_const (Or.inl (q_pos hz).ne')
  have hmul := hq.const_mul ((4 * Real.pi)⁻¹)
  rw [newtonianKernel_eq_rpow hz]
  exact hmul

private theorem tendsto_spatialDeriv_regKernel {ε : ℕ → ℝ} (hε0 : Tendsto ε atTop (𝓝 0))
    (hεpos : ∀ n, ε n ≠ 0) {z : Vec3} (hz : z ≠ 0) (i : Fin 3) :
    Tendsto (fun n => spatialDeriv (regKernel (ε n)) i z) atTop
      (𝓝 (spatialDeriv newtonianKernel i z)) := by
  have hq : Tendsto (fun n => (regQ (ε n) z) ^ (-(3 : ℝ) / 2)) atTop
      (𝓝 ((q z) ^ (-(3 : ℝ) / 2))) :=
    (tendsto_regQ hε0 z).rpow_const (Or.inl (q_pos hz).ne')
  have hmul := hq.const_mul (-(4 * Real.pi)⁻¹ * z i)
  have heq : (fun n => spatialDeriv (regKernel (ε n)) i z) =
      fun n => -(4 * Real.pi)⁻¹ * z i * (regQ (ε n) z) ^ (-(3 : ℝ) / 2) :=
    funext fun n => spatialDeriv_regKernel_formula (hεpos n) z i
  rw [heq, newtonianKernel_spatialDeriv_formula hz i]
  exact hmul

private theorem singular_ibp_newtonianKernel {F : Vec3 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (x : Vec3) (l : Fin 3) :
    ∫ y : Vec3, newtonianKernel (x - y) * spatialDeriv F l y =
      ∫ y : Vec3, spatialDeriv newtonianKernel l (x - y) * F y := by
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεdef
  have hεpos : ∀ n, 0 < ε n := fun n => by rw [hεdef]; positivity
  have hε0 : Tendsto ε atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hK : IsCompact (tsupport F) := hFc
  obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn
    (contDiff_spatialDeriv_smooth hF l).continuous.continuousOn (f := spatialDeriv F l)
  obtain ⟨C2, hC2⟩ := hK.exists_bound_of_continuousOn hF.continuous.continuousOn (f := F)
  have hb1 : Integrable (fun y : Vec3 => (tsupport F).indicator
      (fun y => C1 * newtonianKernel (x - y)) y) :=
    IntegrableOn.integrable_indicator
      (((locallyIntegrable_newtonianKernel_sub x).integrableOn_isCompact hK).const_mul C1)
      hK.measurableSet
  have hb2 : Integrable (fun y : Vec3 => (tsupport F).indicator
      (fun y => C2 * |spatialDeriv newtonianKernel l (x - y)|) y) :=
    IntegrableOn.integrable_indicator
      (((locallyIntegrable_spatialDeriv_newtonianKernel_sub x l).integrableOn_isCompact
        hK).abs.const_mul C2)
      hK.measurableSet
  have hA : Tendsto (fun n => ∫ y : Vec3, regKernel (ε n) (x - y) * spatialDeriv F l y) atTop
      (𝓝 (∫ y : Vec3, newtonianKernel (x - y) * spatialDeriv F l y)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun y => (tsupport F).indicator (fun y => C1 * newtonianKernel (x - y)) y)
    · intro n
      exact (((continuous_regKernel (hεpos n).ne').comp
        (continuous_const.sub continuous_id)).mul
        (contDiff_spatialDeriv_smooth hF l).continuous).aestronglyMeasurable
    · exact hb1
    · intro n
      filter_upwards [Measure.ae_ne volume x] with y hy
      by_cases hyK : y ∈ tsupport F
      · rw [Set.indicator_of_mem hyK]
        rw [Real.norm_eq_abs, abs_mul]
        have hxy : x - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
        calc |regKernel (ε n) (x - y)| * |spatialDeriv F l y| ≤
            newtonianKernel (x - y) * C1 := by
              apply mul_le_mul (le_trans (abs_regKernel_le_newtonianKernel
                (hεpos n).ne' hxy) (le_of_eq (abs_of_nonneg (by
                  unfold newtonianKernel vec3EuclideanNorm; positivity))))
                (hC1 y hyK) (abs_nonneg _)
                (by unfold newtonianKernel vec3EuclideanNorm; positivity)
          _ = C1 * newtonianKernel (x - y) := by ring
      · have hzero : spatialDeriv F l y = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hyK (tsupport_spatialDeriv_subset l h))
        rw [Set.indicator_of_notMem hyK, hzero]
        simp
    · filter_upwards [Measure.ae_ne volume x] with y hy
      exact (tendsto_regKernel hε0 (sub_ne_zero.mpr (Ne.symm hy))).mul_const _
  have hB : Tendsto (fun n => ∫ y : Vec3, spatialDeriv (regKernel (ε n)) l (x - y) * F y) atTop
      (𝓝 (∫ y : Vec3, spatialDeriv newtonianKernel l (x - y) * F y)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun y => (tsupport F).indicator (fun y => C2 * |spatialDeriv newtonianKernel l (x - y)|) y)
    · intro n
      exact ((continuous_spatialDeriv_regKernel (hεpos n).ne' l).comp
        (continuous_const.sub continuous_id)).mul hF.continuous |>.aestronglyMeasurable
    · exact hb2
    · intro n
      filter_upwards [Measure.ae_ne volume x] with y hy
      by_cases hyK : y ∈ tsupport F
      · rw [Set.indicator_of_mem hyK]
        rw [Real.norm_eq_abs, abs_mul]
        have hxy : x - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
        calc |spatialDeriv (regKernel (ε n)) l (x - y)| * |F y| ≤
            |spatialDeriv newtonianKernel l (x - y)| * C2 :=
              mul_le_mul (abs_spatialDeriv_regKernel_le (hεpos n).ne' hxy l) (hC2 y hyK)
                (abs_nonneg _) (abs_nonneg _)
          _ = C2 * |spatialDeriv newtonianKernel l (x - y)| := by ring
      · have hzero : F y = 0 := image_eq_zero_of_notMem_tsupport hyK
        rw [Set.indicator_of_notMem hyK, hzero]
        simp
    · filter_upwards [Measure.ae_ne volume x] with y hy
      exact (tendsto_spatialDeriv_regKernel hε0 (fun n => (hεpos n).ne')
        (sub_ne_zero.mpr (Ne.symm hy)) l).mul_const _
  have hAB : (fun n => ∫ y : Vec3, regKernel (ε n) (x - y) * spatialDeriv F l y) =
      fun n => ∫ y : Vec3, spatialDeriv (regKernel (ε n)) l (x - y) * F y :=
    funext fun n => regularized_ibp hF hFc x l (hεpos n).ne'
  exact tendsto_nhds_unique hA (hAB ▸ hB)

/-! ## Part 5: ELa -/

theorem ELa_gradient_newton_representation {v : Vec3 → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvc : HasCompactSupport v) (x : Vec3) (l : Fin 3) :
    spatialDeriv v l x =
      -∫ y : Vec3, spatialDeriv newtonianKernel l (x - y) * spatialLaplacian v y := by
  have hG : ContDiff ℝ (⊤ : ℕ∞) (spatialLaplacian v) := contDiff_spatialLaplacian_smooth hv
  have hGc : HasCompactSupport (spatialLaplacian v) := hasCompactSupport_spatialLaplacian hvc
  have hrep : v = fun z => pressureNewtonianPotential (spatialLaplacian v) z := by
    funext z
    rw [newtonian_representation_smooth hv hvc z]
    unfold pressureNewtonianPotential
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  have hderiv := pressureNewtonianPotential_spatialDeriv_convolution hG hGc l x
  have hsingIBP := singular_ibp_newtonianKernel hG hGc x l
  calc spatialDeriv v l x =
        spatialDeriv (pressureNewtonianPotential (spatialLaplacian v)) l x :=
      congrArg (fun f : Vec3 → ℝ => spatialDeriv f l x) hrep
    _ = ∫ y : Vec3, spatialDeriv (spatialLaplacian v) l y * (-newtonianKernel (x - y)) := hderiv
    _ = -∫ y : Vec3, newtonianKernel (x - y) * spatialDeriv (spatialLaplacian v) l y := by
        rw [← integral_neg]
        apply congrArg
        funext y
        ring
    _ = -∫ y : Vec3, spatialDeriv newtonianKernel l (x - y) * spatialLaplacian v y := by
        rw [hsingIBP]

end CIV
