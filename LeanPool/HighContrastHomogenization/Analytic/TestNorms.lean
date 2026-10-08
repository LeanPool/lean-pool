/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.SingularKernel
public import LeanPool.HighContrastHomogenization.Analytic.EuclideanAmbient
public import LeanPool.HighContrastHomogenization.Analytic.ConvexDomains

/-!
# High-contrast homogenization: Analytic.TestNorms

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Homogeneity and finiteness of the normalized norms on a test field

The dual norms `‖·‖_{H^{-s}(V)}` and `‖·‖_{H_underlined^{-1}(V)}` of
`e.physical.negative.norm` are suprema over the admissible tests, that is over
the smooth compactly supported fields of unit normalized norm.  For that index
family to be nontrivial one needs two things about the
normalized norms themselves: they are homogeneous of degree two under scalar
multiplication, so a nonzero test of finite nonzero norm can be rescaled to unit
norm; and they are finite on every test field over a bounded domain.

This module supplies both.  Homogeneity is a direct computation, once the
`ℝ≥0∞`-valued volume average is seen to commute with multiplication by a finite
constant.  Finiteness has three pieces:

* the `L²` term is bounded because a smooth compactly supported field is
  uniformly bounded and the domain has finite volume;
* the gradient term is bounded because the derivative is uniformly bounded, each
  coordinate of the derivative being controlled by the operator norm;
* the fractional term is bounded by the uniform kernel bound, the field being
  globally Lipschitz and every point of a bounded domain seeing the whole domain
  inside one ball of a fixed radius.

The fractional term is where the constraint `s < 1` enters, through the
requirement `2 - (d + 2s) > -d` on the kernel exponent.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Averages and their scaling -/

theorem eVolumeAverage_const_mul (V : Set (Vec d)) (a : ℝ≥0∞) (ha : a ≠ ⊤)
    (f : Vec d → ℝ≥0∞) :
    eVolumeAverage V (fun x => a * f x) = a * eVolumeAverage V f := by
  simp only [eVolumeAverage]
  rw [lintegral_const_mul' a f ha, mul_div_assoc]

theorem eVolumeAverage_lt_top {V : Set (Vec d)} (hV0 : volume V ≠ 0) {f : Vec d → ℝ≥0∞}
    (hf : (∫⁻ x in V, f x ∂volume) ≠ ⊤) : eVolumeAverage V f < ⊤ :=
  ENNReal.div_lt_top hf hV0

theorem fracSeminormSq_smul (V : Set (Vec d)) (s c : ℝ) (ψ : Vec d → Vec d) :
    fracSeminormSq V s (fun x => c • ψ x)
      = ENNReal.ofReal (c ^ 2) * fracSeminormSq V s ψ := by
  have hkey : ∀ x : Vec d,
      (∫⁻ y in V, ENNReal.ofReal (vecNormSq (c • ψ x - c • ψ y) /
        Real.sqrt (vecNormSq (x - y)) ^ ((d : ℝ) + 2 * s)) ∂volume)
      = ENNReal.ofReal (c ^ 2) * ∫⁻ y in V, ENNReal.ofReal (vecNormSq (ψ x - ψ y) /
        Real.sqrt (vecNormSq (x - y)) ^ ((d : ℝ) + 2 * s)) ∂volume := by
    intro x
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun y => ?_
    rw [← smul_sub, vecNormSq_smul, mul_div_assoc, ENNReal.ofReal_mul (sq_nonneg c)]
  simp only [fracSeminormSq]
  rw [← eVolumeAverage_const_mul V _ ENNReal.ofReal_ne_top]
  exact congrArg _ (funext hkey)

theorem hsNormSq_smul (V : Set (Vec d)) (s c : ℝ) (ψ : Vec d → Vec d) :
    hsNormSq V s (fun x => c • ψ x) = ENNReal.ofReal (c ^ 2) * hsNormSq V s ψ := by
  have hL2 : (eVolumeAverage V fun x => ENNReal.ofReal (vecNormSq (c • ψ x)))
      = ENNReal.ofReal (c ^ 2) *
        eVolumeAverage V (fun x => ENNReal.ofReal (vecNormSq (ψ x))) := by
    rw [← eVolumeAverage_const_mul V _ ENNReal.ofReal_ne_top]
    refine congrArg _ (funext fun x => ?_)
    rw [vecNormSq_smul, ENNReal.ofReal_mul (sq_nonneg c)]
  simp only [hsNormSq]
  rw [hL2, fracSeminormSq_smul, mul_add, ← mul_assoc, ← mul_assoc,
    mul_comm (volume V ^ (-(2 * s) / (d : ℝ))) (ENNReal.ofReal (c ^ 2))]

theorem smoothGrad_const_mul {f : Vec d → ℝ} (hf : Differentiable ℝ f) (c : ℝ) (x : Vec d) :
    smoothGrad (fun y => c * f y) x = c • smoothGrad f x := by
  funext i
  simp only [smoothGrad, Pi.smul_apply, smul_eq_mul]
  rw [fderiv_const_mul (hf x) c]
  simp

theorem h1NormSq_smul (V : Set (Vec d)) (c : ℝ) {ψ : Vec d → Vec d}
    (hψ : Differentiable ℝ ψ) :
    h1NormSq V (fun x => c • ψ x) = ENNReal.ofReal (c ^ 2) * h1NormSq V ψ := by
  have hcomp : ∀ j : Fin d, Differentiable ℝ (fun y => ψ y j) := by
    intro j x
    have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j).hasFDerivAt.comp x
      (hψ x).hasFDerivAt
    exact h.differentiableAt
  have hL2 : (eVolumeAverage V fun x => ENNReal.ofReal (vecNormSq (c • ψ x)))
      = ENNReal.ofReal (c ^ 2) *
        eVolumeAverage V (fun x => ENNReal.ofReal (vecNormSq (ψ x))) := by
    rw [← eVolumeAverage_const_mul V _ ENNReal.ofReal_ne_top]
    refine congrArg _ (funext fun x => ?_)
    rw [vecNormSq_smul, ENNReal.ofReal_mul (sq_nonneg c)]
  have hgrad : (eVolumeAverage V fun x =>
        ENNReal.ofReal (∑ j, vecNormSq (smoothGrad (fun y => (c • ψ y) j) x)))
      = ENNReal.ofReal (c ^ 2) * eVolumeAverage V (fun x =>
        ENNReal.ofReal (∑ j, vecNormSq (smoothGrad (fun y => ψ y j) x))) := by
    rw [← eVolumeAverage_const_mul V _ ENNReal.ofReal_ne_top]
    refine congrArg _ (funext fun x => ?_)
    have hsum : (∑ j, vecNormSq (smoothGrad (fun y => (c • ψ y) j) x))
        = c ^ 2 * ∑ j, vecNormSq (smoothGrad (fun y => ψ y j) x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hfun : (fun y => (c • ψ y) j) = fun y => c * ψ y j := by
        funext y; simp
      rw [hfun, smoothGrad_const_mul (hcomp j) c, vecNormSq_smul]
    rw [hsum, ENNReal.ofReal_mul (sq_nonneg c)]
  simp only [h1NormSq]
  rw [hL2, hgrad, mul_add, ← mul_assoc, ← mul_assoc,
    mul_comm (volume V ^ (-(2 : ℝ) / (d : ℝ))) (ENNReal.ofReal (c ^ 2))]

/-! ## Finiteness of the normalized norms on a local test -/

/-- Every point of a bounded domain sees the whole domain inside a fixed ball. -/
theorem exists_uniform_ball {U : Set (Vec d)} (hUb : IsBoundedDomain U) :
    ∃ D : ℝ, 0 < D ∧ ∀ x ∈ U, U ⊆ Metric.ball x D := by
  obtain ⟨R, hR, hb⟩ := hUb
  have hnorm : ∀ z ∈ U, ‖z‖ ≤ R := by
    intro z hz
    refine (pi_norm_le_iff_of_nonneg hR.le).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    exact hb z hz i
  refine ⟨2 * R + 1, by linarith only [hR], fun x hx y hy => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm]
  calc ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
    _ ≤ R + R := add_le_add (hnorm y hy) (hnorm x hx)
    _ < 2 * R + 1 := by linarith only [hR]

theorem lintegral_vecNormSq_ne_top {U : Set (Vec d)} (hUb : IsBoundedDomain U)
    {ψ : Vec d → Vec d} (hcont : Continuous ψ) (hcs : HasCompactSupport ψ) :
    (∫⁻ x in U, ENNReal.ofReal (vecNormSq (ψ x)) ∂volume) ≠ ⊤ := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_bound_of_hasCompactSupport hcont hcs
  have hbound : ∀ x : Vec d, ENNReal.ofReal (vecNormSq (ψ x))
      ≤ ENNReal.ofReal ((d : ℝ) * M ^ 2) := by
    intro x
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : vecNormSq (ψ x) ≤ (d : ℝ) * ‖ψ x‖ ^ 2 := vecNormSq_le_dim_mul_norm_sq _
    have h2 : ‖ψ x‖ ^ 2 ≤ M ^ 2 := by
      calc ‖ψ x‖ ^ 2 = ‖ψ x‖ * ‖ψ x‖ := pow_two _
        _ ≤ M * M := mul_self_le_mul_self (norm_nonneg _) (hM x)
        _ = M ^ 2 := (pow_two _).symm
    calc vecNormSq (ψ x) ≤ (d : ℝ) * ‖ψ x‖ ^ 2 := h1
      _ ≤ (d : ℝ) * M ^ 2 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg d)
  have hlt : (∫⁻ x in U, ENNReal.ofReal (vecNormSq (ψ x)) ∂volume)
      ≤ ENNReal.ofReal ((d : ℝ) * M ^ 2) * volume U := by
    calc (∫⁻ x in U, ENNReal.ofReal (vecNormSq (ψ x)) ∂volume)
        ≤ ∫⁻ _ in U, ENNReal.ofReal ((d : ℝ) * M ^ 2) ∂volume :=
          lintegral_mono fun x => hbound x
      _ = ENNReal.ofReal ((d : ℝ) * M ^ 2) * volume U := setLIntegral_const _ _
  exact ne_of_lt (lt_of_le_of_lt hlt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hUb.volume_lt_top))

theorem lintegral_fracSeminorm_ne_top {U : Set (Vec d)} (hUm : MeasurableSet U)
    (hUb : IsBoundedDomain U) {s : ℝ} (hs0 : 0 ≤ (d : ℝ) + 2 * s) (hs1 : s < 1)
    {ψ : Vec d → Vec d} (hsm : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcs : HasCompactSupport ψ) :
    (∫⁻ x in U, (∫⁻ y in U, ENNReal.ofReal (vecNormSq (ψ x - ψ y) /
      Real.sqrt (vecNormSq (x - y)) ^ ((d : ℝ) + 2 * s)) ∂volume) ∂volume) ≠ ⊤ := by
  obtain ⟨L, -, hlip⟩ := exists_lipschitz_of_hasCompactSupport hsm hcs
  obtain ⟨D, hD, hDsub⟩ := exists_uniform_ball hUb
  have he : -(d : ℝ) < 2 - ((d : ℝ) + 2 * s) := by linarith only [hs1]
  obtain ⟨B, hBtop, hB⟩ := exists_bound_lintegral_ball_rpow d hD he
  set K : ℝ := (d : ℝ) * L ^ 2 with hKdef
  have hK0 : (0 : ℝ) ≤ K := by rw [hKdef]; positivity
  have hinner : ∀ x ∈ U, (∫⁻ y in U, ENNReal.ofReal (vecNormSq (ψ x - ψ y) /
      Real.sqrt (vecNormSq (x - y)) ^ ((d : ℝ) + 2 * s)) ∂volume)
      ≤ ENNReal.ofReal K * B := by
    intro x hx
    calc (∫⁻ y in U, ENNReal.ofReal (vecNormSq (ψ x - ψ y) /
          Real.sqrt (vecNormSq (x - y)) ^ ((d : ℝ) + 2 * s)) ∂volume)
        ≤ ∫⁻ y in U, ENNReal.ofReal K *
            ENNReal.ofReal (‖x - y‖ ^ (2 - ((d : ℝ) + 2 * s))) ∂volume := by
          refine lintegral_mono fun y => ?_
          rw [← ENNReal.ofReal_mul hK0]
          exact ENNReal.ofReal_le_ofReal (gagliardo_kernel_le hlip hs0 x y)
      _ ≤ ∫⁻ y in Metric.ball x D, ENNReal.ofReal K *
            ENNReal.ofReal (‖x - y‖ ^ (2 - ((d : ℝ) + 2 * s))) ∂volume :=
          lintegral_mono_set (hDsub x hx)
      _ = ENNReal.ofReal K * ∫⁻ y in Metric.ball x D,
            ENNReal.ofReal (‖x - y‖ ^ (2 - ((d : ℝ) + 2 * s))) ∂volume :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal K * B := mul_le_mul' (le_refl _) (hB x)
  have houter : (∫⁻ x in U, (∫⁻ y in U, ENNReal.ofReal (vecNormSq (ψ x - ψ y) /
      Real.sqrt (vecNormSq (x - y)) ^ ((d : ℝ) + 2 * s)) ∂volume) ∂volume)
      ≤ (ENNReal.ofReal K * B) * volume U := by
    calc (∫⁻ x in U, (∫⁻ y in U, ENNReal.ofReal (vecNormSq (ψ x - ψ y) /
          Real.sqrt (vecNormSq (x - y)) ^ ((d : ℝ) + 2 * s)) ∂volume) ∂volume)
        ≤ ∫⁻ _ in U, (ENNReal.ofReal K * B) ∂volume := by
          refine lintegral_mono_ae ?_
          filter_upwards [self_mem_ae_restrict hUm] with x hx
          exact hinner x hx
      _ = (ENNReal.ofReal K * B) * volume U := setLIntegral_const _ _
  refine ne_of_lt (lt_of_le_of_lt houter (ENNReal.mul_lt_top ?_ hUb.volume_lt_top))
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hBtop)

theorem hsNormSq_ne_top {U : Set (Vec d)} (hUm : MeasurableSet U)
    (hUb : IsBoundedDomain U)
    (hV0 : volume U ≠ 0) {s : ℝ} (hs0 : 0 ≤ (d : ℝ) + 2 * s) (hs1 : s < 1)
    {ψ : Vec d → Vec d} (hψ : IsLocalVecTest U ψ) : hsNormSq U s ψ ≠ ⊤ := by
  have hVT : volume U ≠ ⊤ := ne_of_lt hUb.volume_lt_top
  have hpre : volume U ^ (-(2 * s) / (d : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hV0 hVT
  have hA : eVolumeAverage U (fun x => ENNReal.ofReal (vecNormSq (ψ x))) ≠ ⊤ :=
    ne_of_lt (eVolumeAverage_lt_top hV0
      (lintegral_vecNormSq_ne_top hUb (hψ.contDiff.continuous) hψ.hasCompactSupport))
  have hF : fracSeminormSq U s ψ ≠ ⊤ := by
    refine ne_of_lt (eVolumeAverage_lt_top hV0 ?_)
    exact lintegral_fracSeminorm_ne_top hUm hUb hs0 hs1 hψ.contDiff hψ.hasCompactSupport
  simp only [hsNormSq]
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hpre hA, hF⟩

theorem h1NormSq_ne_top {U : Set (Vec d)} (hUb : IsBoundedDomain U)
    (hV0 : volume U ≠ 0) {ψ : Vec d → Vec d} (hψ : IsLocalVecTest U ψ) :
    h1NormSq U ψ ≠ ⊤ := by
  have hVT : volume U ≠ ⊤ := ne_of_lt hUb.volume_lt_top
  have hpre : volume U ^ (-(2 : ℝ) / (d : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hV0 hVT
  have hA : eVolumeAverage U (fun x => ENNReal.ofReal (vecNormSq (ψ x))) ≠ ⊤ :=
    ne_of_lt (eVolumeAverage_lt_top hV0
      (lintegral_vecNormSq_ne_top hUb (hψ.contDiff.continuous) hψ.hasCompactSupport))
  -- The gradient term: a uniform bound through the bound on `fderiv ψ`.
  obtain ⟨C, hC0, hC⟩ :=
    exists_fderiv_bound_of_hasCompactSupport hψ.contDiff hψ.hasCompactSupport
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hdiff : Differentiable ℝ ψ := hψ.contDiff.differentiable hne
  have hgradbd : ∀ x : Fin d → ℝ, ∀ j i : Fin d,
      |smoothGrad (fun y => ψ y j) x i| ≤ C := by
    intro x j i
    have hfd : fderiv ℝ (fun y => ψ y j) x
        = (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j).comp
          (fderiv ℝ ψ x) := by
      have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j).hasFDerivAt.comp x
        (hdiff x).hasFDerivAt
      exact h.fderiv
    change |fderiv ℝ (fun y => ψ y j) x (basisVec i)| ≤ C
    rw [hfd]
    have hval : ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j).comp
        (fderiv ℝ ψ x)) (basisVec i) = (fderiv ℝ ψ x (basisVec i)) j := rfl
    rw [hval, ← Real.norm_eq_abs]
    calc ‖(fderiv ℝ ψ x (basisVec i)) j‖ ≤ ‖fderiv ℝ ψ x (basisVec i)‖ :=
          norm_le_pi_norm (fderiv ℝ ψ x (basisVec i)) j
      _ ≤ ‖fderiv ℝ ψ x‖ * ‖(basisVec i : Vec d)‖ := (fderiv ℝ ψ x).le_opNorm _
      _ ≤ C * 1 := by
          exact mul_le_mul (hC x) (norm_basisVec_le_one i) (norm_nonneg _) hC0
      _ = C := mul_one C
  have hsumbd : ∀ x : Vec d,
      (∑ j, vecNormSq (smoothGrad (fun y => ψ y j) x)) ≤ (d : ℝ) * ((d : ℝ) * C ^ 2) := by
    intro x
    have hone' : ∀ j : Fin d,
        vecNormSq (smoothGrad (fun y => ψ y j) x) ≤ (d : ℝ) * C ^ 2 := by
      intro j
      rw [vecNormSq_eq_sum_sq]
      have hb : ∀ i : Fin d, (smoothGrad (fun y => ψ y j) x) i ^ 2 ≤ C ^ 2 := by
        intro i
        have h := hgradbd x j i
        calc (smoothGrad (fun y => ψ y j) x) i ^ 2
            = |smoothGrad (fun y => ψ y j) x i| * |smoothGrad (fun y => ψ y j) x i| := by
              rw [← sq_abs, pow_two]
          _ ≤ C * C := mul_self_le_mul_self (abs_nonneg _) h
          _ = C ^ 2 := (pow_two _).symm
      have hconst : ∑ _i : Fin d, C ^ 2 = (d : ℝ) * C ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      calc ∑ i, (smoothGrad (fun y => ψ y j) x) i ^ 2 ≤ ∑ _i : Fin d, C ^ 2 :=
            Finset.sum_le_sum fun i _ => hb i
        _ = (d : ℝ) * C ^ 2 := hconst
    have hconst : ∑ _j : Fin d, ((d : ℝ) * C ^ 2) = (d : ℝ) * ((d : ℝ) * C ^ 2) := by
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc (∑ j, vecNormSq (smoothGrad (fun y => ψ y j) x))
        ≤ ∑ _j : Fin d, ((d : ℝ) * C ^ 2) := Finset.sum_le_sum fun j _ => hone' j
      _ = (d : ℝ) * ((d : ℝ) * C ^ 2) := hconst
  have hG : eVolumeAverage U (fun x =>
      ENNReal.ofReal (∑ j, vecNormSq (smoothGrad (fun y => ψ y j) x))) ≠ ⊤ := by
    refine ne_of_lt (eVolumeAverage_lt_top hV0 ?_)
    have hle : (∫⁻ x in U, ENNReal.ofReal
        (∑ j, vecNormSq (smoothGrad (fun y => ψ y j) x)) ∂volume)
        ≤ ENNReal.ofReal ((d : ℝ) * ((d : ℝ) * C ^ 2)) * volume U := by
      calc (∫⁻ x in U, ENNReal.ofReal
            (∑ j, vecNormSq (smoothGrad (fun y => ψ y j) x)) ∂volume)
          ≤ ∫⁻ _ in U, ENNReal.ofReal ((d : ℝ) * ((d : ℝ) * C ^ 2)) ∂volume :=
            lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hsumbd x)
        _ = ENNReal.ofReal ((d : ℝ) * ((d : ℝ) * C ^ 2)) * volume U := setLIntegral_const _ _
    exact ne_of_lt (lt_of_le_of_lt hle
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hUb.volume_lt_top))
  simp only [h1NormSq]
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hpre hA, hG⟩

end

end HighContrast
end HCPolySupport
