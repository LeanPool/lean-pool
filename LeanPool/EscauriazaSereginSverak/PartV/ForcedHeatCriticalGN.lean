/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatCriticalEnergy
public import LeanPool.CaffarelliKohnNirenberg.Foundation.GagliardoNirenberg
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Real-valued interpolation and the regularized critical profile

The Gagliardo–Nirenberg inequality of `lem:u-ten-thirds` of the CKN manuscript in real integral form
for continuously differentiable functions, and the elementary bounds and limits
of the regularized critical profile `heatRegG η` and entropy `heatRegEnergy η`
as `η → 0`, as used in `lem:pv-stokes`.
-/

public section

open CKN

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The whole-space Gagliardo–Nirenberg inequality in real integral form:
`∫ |f|^{10/3} ≤ K² (∫ f²)^{2/3} ∫ |∇f|²`, with `K` the real Sobolev constant of
`CKN.h1_gagliardoNirenberg_tenThirds`. -/
theorem integral_rpow_tenThirds_le {f : Vec3 → ℝ} (hf : ContDiff ℝ 1 f)
    (h2 : Integrable (fun x => f x ^ 2))
    (hD : ∀ j : Fin 3, Integrable (fun x => (fderiv ℝ f x (CKN.basisVec j)) ^ 2))
    (h103 : Integrable (fun x => |f x| ^ (10 / 3 : ℝ))) :
    ∫ x, |f x| ^ (10 / 3 : ℝ) ≤
      gagliardoNirenbergSobolevConstant.toReal ^ 2 * (∫ x, f x ^ 2) ^ (2 / 3 : ℝ) *
        ∫ x, ∑ j : Fin 3, (fderiv ℝ f x (CKN.basisVec j)) ^ 2 := by
  have hfm : AEStronglyMeasurable f volume := hf.continuous.aestronglyMeasurable
  have hDc (j : Fin 3) : Continuous (fun x => fderiv ℝ f x (CKN.basisVec j)) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hmem2 : MemLp f 2 volume := (memLp_two_iff_integrable_sq hfm).2 h2
  have hmemD (j : Fin 3) : MemLp (fun x => fderiv ℝ f x (CKN.basisVec j)) 2 volume :=
    (memLp_two_iff_integrable_sq (hDc j).aestronglyMeasurable).2 (hD j)
  let v : CKN.H1Function (Set.univ : Set Vec3) :=
    { toFun := f
      grad := fun x j => fderiv ℝ f x (CKN.basisVec j)
      memL2 := by
        simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using hmem2
      gradMemL2 := by
        intro j
        simpa [CKN.GradMemL2On, CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn,
          Measure.restrict_univ] using hmemD j
      hasWeakGradient := CKN.HasWeakGradientOn.of_contDiff hf }
  have hGN := h1_gagliardoNirenberg_tenThirds v
  change eLpNorm f (ENNReal.ofReal (10 / 3 : ℝ)) volume ≤
    gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ) * eLpNorm f 2 volume ^ (2 / 5 : ℝ) *
      eLpNorm (fun x => vec3EuclideanNorm (fun j => fderiv ℝ f x (CKN.basisVec j))) 2 volume ^
        (3 / 5 : ℝ) at hGN
  set a : ℝ := ∫ x, |f x| ^ (10 / 3 : ℝ) with ha
  set b : ℝ := ∫ x, f x ^ 2 with hb
  set c : ℝ := ∫ x, ∑ j : Fin 3, (fderiv ℝ f x (CKN.basisVec j)) ^ 2 with hc
  have ha0 : 0 ≤ a := integral_nonneg fun x => by positivity
  have hb0 : 0 ≤ b := integral_nonneg fun x => sq_nonneg _
  have hc0 : 0 ≤ c := integral_nonneg fun x => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hp103 : ENNReal.ofReal (10 / 3 : ℝ) ≠ 0 := by norm_num
  have hmem103 : MemLp f (ENNReal.ofReal (10 / 3 : ℝ)) volume := by
    rw [← integrable_norm_rpow_iff hfm hp103 ENNReal.ofReal_ne_top]
    rw [ENNReal.toReal_ofReal (by norm_num)]
    simpa [Real.norm_eq_abs] using h103
  have hLHS : eLpNorm f (ENNReal.ofReal (10 / 3 : ℝ)) volume =
      ENNReal.ofReal (a ^ (3 / 10 : ℝ)) := by
    rw [hmem103.eLpNorm_eq_integral_rpow_norm hp103 ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by norm_num)]
    simp only [Real.norm_eq_abs, ha]
    norm_num
  have hL2 : eLpNorm f 2 volume = ENNReal.ofReal (b ^ (1 / 2 : ℝ)) := by
    rw [hmem2.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp only [Real.norm_eq_abs, ENNReal.toReal_ofNat, hb]
    congr 2
    · congr 1
      funext x
      rw [Real.rpow_two, sq_abs]
    · norm_num
  let gn : Vec3 → ℝ := fun x => vec3EuclideanNorm (fun j => fderiv ℝ f x (CKN.basisVec j))
  have hgnsq (x : Vec3) : gn x ^ 2 = ∑ j : Fin 3, (fderiv ℝ f x (CKN.basisVec j)) ^ 2 :=
    vec3EuclideanNorm_sq _
  have hgnc : Continuous gn :=
    continuous_vec3EuclideanNorm.comp (continuous_pi fun j => hDc j)
  have hgn2 : Integrable (fun x => gn x ^ 2) := by
    simp_rw [hgnsq]
    exact integrable_finsetSum _ fun j _ => hD j
  have hmemgn : MemLp gn 2 volume :=
    (memLp_two_iff_integrable_sq hgnc.aestronglyMeasurable).2 hgn2
  have hD2 : eLpNorm gn 2 volume = ENNReal.ofReal (c ^ (1 / 2 : ℝ)) := by
    rw [hmemgn.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp only [Real.norm_eq_abs, ENNReal.toReal_ofNat, hc]
    congr 2
    · congr 1
      funext x
      rw [Real.rpow_two, sq_abs, hgnsq]
    · norm_num
  change eLpNorm f (ENNReal.ofReal (10 / 3 : ℝ)) volume ≤
    gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ) * eLpNorm f 2 volume ^ (2 / 5 : ℝ) *
      eLpNorm gn 2 volume ^ (3 / 5 : ℝ) at hGN
  rw [hLHS, hL2, hD2] at hGN
  have hKtop : gagliardoNirenbergSobolevConstant ≠ ∞ :=
    (Classical.choose_spec CKN.sobolev_L6_global).1
  set κ : ℝ := gagliardoNirenbergSobolevConstant.toReal with hκ
  have hκ0 : 0 ≤ κ := ENNReal.toReal_nonneg
  have hK : gagliardoNirenbergSobolevConstant = ENNReal.ofReal κ :=
    (ENNReal.ofReal_toReal hKtop).symm
  rw [hK, ENNReal.ofReal_rpow_of_nonneg hκ0 (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hGN
  -- hGN : a^(3/10) ≤ κ^(3/5) * (b^(1/2))^(2/5) * (c^(1/2))^(3/5)
  have hpow := Real.rpow_le_rpow (by positivity) hGN (by norm_num : (0 : ℝ) ≤ 10 / 3)
  have e0 : (a ^ (3 / 10 : ℝ)) ^ (10 / 3 : ℝ) = a := by
    rw [← Real.rpow_mul ha0]
    norm_num
  have e1 : (κ ^ (3 / 5 : ℝ)) ^ (10 / 3 : ℝ) = κ ^ 2 := by
    rw [← Real.rpow_mul hκ0]
    norm_num
  have e2 : ((b ^ (1 / 2 : ℝ)) ^ (2 / 5 : ℝ)) ^ (10 / 3 : ℝ) = b ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_mul hb0, ← Real.rpow_mul hb0]
    norm_num
  have e3 : ((c ^ (1 / 2 : ℝ)) ^ (3 / 5 : ℝ)) ^ (10 / 3 : ℝ) = c := by
    rw [← Real.rpow_mul hc0, ← Real.rpow_mul hc0]
    norm_num
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity), e0, e1, e2, e3] at hpow
  exact hpow

/-- The regularized critical profile lies between `0` and `(∑ v_i²)^{3/4}`. -/
theorem heatRegG_nonneg_le_rpow {η : ℝ} (hη : 0 < η) (v : Vec3) :
    0 ≤ heatRegG η v ∧ heatRegG η v ≤ (∑ i : Fin 3, v i ^ 2) ^ (3 / 4 : ℝ) := by
  set q : ℝ := ∑ i : Fin 3, v i ^ 2 with hq
  have hq0 : 0 ≤ q := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsq : heatRegSq η v = q + η ^ 2 := rfl
  have hη32 : η ^ (3 / 2 : ℝ) = (η ^ 2) ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hη.le]
    norm_num
  unfold heatRegG
  rw [hsq, hη32]
  constructor
  · exact sub_nonneg.mpr (Real.rpow_le_rpow (by positivity) (by linarith only [hq0])
      (by norm_num))
  · have h := NNReal.rpow_add_le_add_rpow (⟨q, hq0⟩ : ℝ≥0) ⟨η ^ 2, by positivity⟩
      (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num)
    have h' : (q + η ^ 2) ^ (3 / 4 : ℝ) ≤ q ^ (3 / 4 : ℝ) + (η ^ 2) ^ (3 / 4 : ℝ) := by
      exact_mod_cast h
    linarith only [h']

/-- As the regularization vanishes, the regularized critical profile tends to
`(∑ v_i²)^{3/4} = |v|^{3/2}`. -/
theorem heatRegG_tendsto_rpow (v : Vec3) :
    Tendsto (fun η : ℝ => heatRegG η v) (𝓝[>] 0)
      (𝓝 ((∑ i : Fin 3, v i ^ 2) ^ (3 / 4 : ℝ))) := by
  set q : ℝ := ∑ i : Fin 3, v i ^ 2
  have hcont : ContinuousAt (fun η : ℝ => (q + η ^ 2) ^ (3 / 4 : ℝ) - η ^ (3 / 2 : ℝ)) 0 := by
    have h1 : ContinuousAt (fun η : ℝ => (q + η ^ 2) ^ (3 / 4 : ℝ)) 0 :=
      (Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))).comp
        (by fun_prop : ContinuousAt (fun η : ℝ => q + η ^ 2) 0)
    have h2 : ContinuousAt (fun η : ℝ => η ^ (3 / 2 : ℝ)) 0 :=
      Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))
    exact h1.sub h2
  have hval : (q + (0 : ℝ) ^ 2) ^ (3 / 4 : ℝ) - (0 : ℝ) ^ (3 / 2 : ℝ) = q ^ (3 / 4 : ℝ) := by
    rw [Real.zero_rpow (by norm_num)]
    simp
  have ht := hcont.tendsto
  rw [hval] at ht
  exact ht.mono_left nhdsWithin_le_nhds

/-- As the regularization vanishes, the regularized entropy tends to
`⅓ (∑ v_i²)^{3/2} = ⅓ |v|³`. -/
theorem heatRegEnergy_tendsto_rpow (v : Vec3) :
    Tendsto (fun η : ℝ => heatRegEnergy η v) (𝓝[>] 0)
      (𝓝 ((1 / 3 : ℝ) * (∑ i : Fin 3, v i ^ 2) ^ (3 / 2 : ℝ))) := by
  set q : ℝ := ∑ i : Fin 3, v i ^ 2
  have hcont : ContinuousAt (fun η : ℝ => (1 / 3 : ℝ) * (q + η ^ 2) ^ (3 / 2 : ℝ) -
      (η / 2) * (q + η ^ 2) + η ^ 3 / 6) 0 := by
    have h1 : ContinuousAt (fun η : ℝ => (q + η ^ 2) ^ (3 / 2 : ℝ)) 0 :=
      (Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))).comp
        (by fun_prop : ContinuousAt (fun η : ℝ => q + η ^ 2) 0)
    exact ((continuousAt_const.mul h1).sub (by fun_prop)).add (by fun_prop)
  have ht := hcont.tendsto
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, zero_div,
    zero_mul, sub_zero] at ht
  exact ht.mono_left nhdsWithin_le_nhds

/-- Chain rule for a scalar map applied to a time slice of a smooth vector
field. -/
theorem fderiv_scalar_comp_slice_apply {φ : Vec3 → ℝ} (hφ : Differentiable ℝ φ)
    {U : Fin 3 → Vec3 × ℝ → ℝ} (hU : ∀ k, Differentiable ℝ (U k))
    (x : Vec3) (t : ℝ) (v : Vec3) :
    fderiv ℝ (fun y : Vec3 => φ (fun k => U k (y, t))) x v =
      fderiv ℝ φ (fun k => U k (x, t)) (fun k => fderiv ℝ (U k) (x, t) (v, 0)) := by
  have hslice (k : Fin 3) : Differentiable ℝ (fun y : Vec3 => U k (y, t)) :=
    (hU k).comp (differentiable_id.prodMk (differentiable_const t))
  have hZ : HasFDerivAt (fun y : Vec3 => fun k => U k (y, t))
      (ContinuousLinearMap.pi fun k => fderiv ℝ (fun y : Vec3 => U k (y, t)) x) x :=
    hasFDerivAt_pi.2 fun k => (hslice k x).hasFDerivAt
  have hcomp := (hφ (fun k => U k (x, t))).hasFDerivAt.comp x hZ
  change fderiv ℝ (φ ∘ fun y : Vec3 => fun k => U k (y, t)) x v = _
  rw [hcomp.fderiv]
  change fderiv ℝ φ (fun k => U k (x, t))
      ((ContinuousLinearMap.pi fun k => fderiv ℝ (fun y : Vec3 => U k (y, t)) x) v) = _
  have hvec : (ContinuousLinearMap.pi fun k => fderiv ℝ (fun y : Vec3 => U k (y, t)) x) v =
      fun k => fderiv ℝ (U k) (x, t) (v, 0) := by
    funext k
    exact fderiv_slice_apply (hU k) x t v
  rw [hvec]

/-- A time window as a restriction of the space-time product measure. -/
theorem window_prod_eq (τ : ℝ) :
    (volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ)) =
      ((volume : Measure Vec3).prod volume).restrict (univ ×ˢ Ioc 0 τ) := by
  rw [← Measure.prod_restrict, Measure.restrict_univ]

/-- Integrals of a nonnegative function over growing time windows increase. -/
theorem window_integral_mono {F : Vec3 × ℝ → ℝ} {t₁ τ : ℝ} (ht₁ : t₁ ≤ τ)
    (hF : Integrable F ((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ))))
    (hF0 : ∀ p, 0 ≤ F p) :
    ∫ p, F p ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 t₁))) ≤
      ∫ p, F p ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ))) := by
  have hprod (a : ℝ) : (volume : Measure Vec3).prod (volume.restrict (Ioc 0 a)) =
      ((volume : Measure Vec3).prod volume).restrict (univ ×ˢ Ioc 0 a) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hprod] at hF ⊢
  rw [hprod]
  refine setIntegral_mono_set hF (Eventually.of_forall hF0) (Eventually.of_forall ?_)
  intro p hp
  exact ⟨hp.1, hp.2.1, hp.2.2.trans ht₁⟩

end ESS

end
