/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Testing
public import LeanPool.KLS.FunctionalInequalities.Analysis.Cutoff.Profile
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Coercivity
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.Instances.Matrix

/-!
# Weak inverse-Hessian height cutoffs for C1 Monge–Ampère potentials

Height cutoffs χ_R = smoothTransition(2 − (u − c)/R) for the inverse-Hessian diffusion
L f = tr((∇²u)⁻¹ ∇²f) − DV(∇u)(∇f) of a convex, normalized C1 potential u with Lipschitz gradient,
Lipschitz
Monge–Ampère exponent −u + V(∇u) and det ∇²u = exp(−u + V(∇u)), ∇²u positive definite almost
everywhere
(Letwin arXiv:2607.24164v1, the cutoffs of Lemma A.4 in C1/Lipschitz-gradient form):

* `exists_scaled_weak_inverse_hessian_cutoffs`: one shift c and one constant C such that, for every
  real R ≥ 1,
  χ_R is C1, compactly supported, has Lipschitz gradient and values in [0, 1], increases in R to 1
  pointwise,
  its literal generator L χ_R is integrable for ν = e^{−u} dx with ‖L χ_R‖_{L¹(ν)} ≤ C/R, and the
  defect vanishes;
* `exists_weak_inverse_hessian_cutoffs`: the same family at R = m + 1.

Every finite dimension is included. No C2 regularity of u, global inverse-Hessian bound or energy
estimate is assumed.
A.5 consumption, the weak trace identity, the energy comparison (2.14) and Theorem 2.5 are not
proved here. One-use
supports, including the generator-defect core, are private.
-/

@[expose] public section

noncomputable section
open MeasureTheory Filter Set Metric Matrix
open FunctionalInequalities.Probability.Stein
open scoped ContDiff Topology RealInnerProductSpace
namespace FunctionalInequalities.Analysis

private theorem integrable_compact_C1_inverse_energy {n : ℕ}
    {u V η w : EuclideanSpace ℝ (Fin n) → ℝ} {G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (hw : ContDiff ℝ 1 w) :
    Integrable (fun x =>
      (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ η x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hi (i j : Fin n) : Integrable
      (fun x => (hessianMatrix u x)⁻¹ i j *
        (fderiv ℝ η x (e i) * fderiv ℝ w x (e j) * Real.exp (-u x)))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hc : Continuous
        (fun x => fderiv ℝ η x (e i) * fderiv ℝ w x (e j) * Real.exp (-u x)) :=
      (((hη.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
        ((hw.continuous_fderiv one_ne_zero).clm_apply continuous_const)).mul
        (Real.continuous_exp.comp hu.continuous.neg)
    have hs : HasCompactSupport
        (fun x => fderiv ℝ η x (e i) * fderiv ℝ w x (e j) * Real.exp (-u x)) :=
      (hηc.fderiv_apply ℝ (e i)).mul_right.mul_right
    obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous hc
    exact integrable_inv_hessianMatrix_mul_of_bounded_compact
      hG hF.continuous hdet hc.measurable hs hC i j
  have hs := integrable_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))
  simpa only [Finset.sum_mul, mul_assoc] using hs

private theorem integral_profile_inverse_energy_eq_drift {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {ζ : ℝ → ℝ} {G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V)
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport (fun x => ζ (u x))) :
    Integrable (fun x =>
      (deriv ζ (u x) * (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j))) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, -(deriv ζ (u x) * (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j))) * Real.exp (-u x)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
    ∫ x, ζ (u x) * ((n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)) *
      Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hη : ContDiff ℝ 1 (fun x => ζ (u x)) := hζ.comp hu
  have hchain (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
      fderiv ℝ (fun y => ζ (u y)) x (e i) =
        deriv ζ (u x) * fderiv ℝ u x (e i) := by
    have hd := ((hζ.differentiable one_ne_zero (u x)).hasDerivAt.comp_hasFDerivAt
      x (hu.differentiable one_ne_zero x).hasFDerivAt).fderiv
    change fderiv ℝ (fun y => ζ (u y)) x = _ at hd
    rw [hd]
    rfl
  have heq (x : EuclideanSpace ℝ (Fin n)) :
      (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ (fun y => ζ (u y)) x (e i) * fderiv ℝ u x (e j)) =
      deriv ζ (u x) * (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (e i) * fderiv ℝ u x (e j)) := by
    simp only [hchain, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi := integrable_compact_C1_inverse_energy hu hG hF hdet hη hζc hu
  have hp := integral_mul_generator_eq_neg_energy_of_contDiff_one
    hu hG hV hF hdet hu hG hη hζc
  have htr : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ((hessianMatrix u x)⁻¹ * hessianMatrix u x).trace = (n : ℝ) := by
    filter_upwards [hdet] with x hx
    rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
      (hx.trans_ne (Real.exp_ne_zero _)))]
    simp only [Matrix.trace_one, Fintype.card_fin]
  have hiq := hi.congr (Filter.Eventually.of_forall fun x =>
    congrArg (fun t : ℝ => t * Real.exp (-u x)) (heq x))
  have hEq :
      (∫ x, (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ (fun y => ζ (u y)) x (e i) * fderiv ℝ u x (e j)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ x, (deriv ζ (u x) * (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (e i) * fderiv ℝ u x (e j))) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x =>
      congrArg (fun t : ℝ => t * Real.exp (-u x)) (heq x))
  refine ⟨hiq, ?_⟩
  calc
    _ = -(∫ x, (deriv ζ (u x) * (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (e i) * fderiv ℝ u x (e j))) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
      simpa only [neg_mul] using integral_neg
        (fun x => (deriv ζ (u x) * (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
          fderiv ℝ u x (e i) * fderiv ℝ u x (e j))) * Real.exp (-u x))
    _ = _ := (congrArg Neg.neg hEq).symm
    _ = _ := hp.symm
    _ = _ := integral_congr_ae (htr.mono fun x hx =>
      congrArg (fun t : ℝ => ζ (u x) *
        (t - fderiv ℝ V (gradient u x) (gradient u x)) * Real.exp (-u x)) hx)

private theorem integrable_profile_energy_and_integral_le {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {ζ : ℝ → ℝ} {G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V)
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport (fun x => ζ (u x)))
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    {D B : ℝ} (hD : 0 ≤ D)
    (hζbound : ∀ x, 0 ≤ ζ (u x) ∧ ζ (u x) ≤ B)
    (hdrift : ∀ x, |(n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)| ≤ D) :
    Integrable (fun x =>
      -(deriv ζ (u x) * (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j))) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, -(deriv ζ (u x) * (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j))) * Real.exp (-u x)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤ D * B := by
  have hp := integral_profile_inverse_energy_eq_drift hu hG hV hF hdet hζ hζc
  have hc : Continuous (fun x => (n : ℝ) -
      fderiv ℝ V (gradient u x) (gradient u x)) :=
    continuous_const.sub
      (((hV.continuous_fderiv one_ne_zero).comp hG.continuous).clm_apply hG.continuous)
  have hi : Integrable (fun x => ζ (u x) *
      ((n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (((hζ.continuous.comp hu.continuous).mul hc).mul
      (Real.continuous_exp.comp hu.continuous.neg)).integrable_of_hasCompactSupport
        hζc.mul_right.mul_right
  have hexp := BakryEmery.integrable_exp_neg_of_integral_eq_one
    (volume : Measure (EuclideanSpace ℝ (Fin n))) u hnorm
  have hpoint (x : EuclideanSpace ℝ (Fin n)) :
      ζ (u x) * ((n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)) * Real.exp (-u x) ≤
        (D * B) * Real.exp (-u x) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    calc
      _ ≤ ζ (u x) * D := mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (hdrift x)) (hζbound x).1
      _ ≤ B * D := mul_le_mul_of_nonneg_right (hζbound x).2 hD
      _ = _ := mul_comm _ _
  refine ⟨hp.1.neg.congr (Filter.Eventually.of_forall fun x => by
    change -(_ * _) = -_ * _
    ring), ?_⟩
  calc
    _ = _ := hp.2
    _ ≤ ∫ x, (D * B) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      integral_mono hi (hexp.const_mul (D * B)) hpoint
    _ = D * B := by rw [integral_const_mul, hnorm, mul_one]

private theorem integrable_majorant_inverse_energy_and_integral_le {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    (hsub : ∀ t : ℝ, IsCompact {x | u x ≤ t}) {D : ℝ} (hD : 0 ≤ D)
    (hdrift : ∀ x, |(n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)| ≤ D)
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hw0 : ∀ t, 0 ≤ w t)
    (hws : ∀ t, t ≤ 0 ∨ 3 ≤ t → w t = 0) {R : ℝ} (hR : 0 < R) (c : ℝ) :
    Integrable (fun x => (R ^ 2)⁻¹ * w ((u x - c) / R) *
      (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, (R ^ 2)⁻¹ * w ((u x - c) / R) *
      (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        D * (R⁻¹ * ∫ t in (0 : ℝ)..3, w t) := by
  let ζ : ℝ → ℝ := fun s => R⁻¹ * ∫ t in (s - c) / R..3, w t
  obtain ⟨hζ, hζd, hζbound, hζzero⟩ :=
    shifted_inv_mul_intervalIntegral_div_three_cutoff hw hw0 hws hR c
  have hζc : HasCompactSupport (fun x => ζ (u x)) :=
    hasCompactSupport_comp_of_isCompact_sublevel hu.continuous (hsub (c + 3 * R)) hζzero
  obtain ⟨_hq, _hqd, hq0, _hqb, _hqz⟩ :=
    inv_mul_intervalIntegral_div_three_cutoff hw hw0 hws hR
  have hp := integrable_profile_energy_and_integral_le hu hG hV hF hdet
    (hζ.of_le (WithTop.coe_le_coe.mpr le_top)) hζc hnorm hD
    (fun x => ⟨hq0 (u x - c), (le_abs_self _).trans (hζbound (u x))⟩) hdrift
  have heq (x : EuclideanSpace ℝ (Fin n)) :
      -(deriv ζ (u x) * (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j))) * Real.exp (-u x) =
      (R ^ 2)⁻¹ * w ((u x - c) / R) *
        (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
          fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
          fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x) := by
    rw [show deriv ζ (u x) = -((R ^ 2)⁻¹ * w ((u x - c) / R)) from hζd (u x)]
    ring
  refine ⟨hp.1.congr (Filter.Eventually.of_forall heq), ?_⟩
  exact (integral_congr_ae (Filter.Eventually.of_forall fun x => (heq x).symm)).le.trans hp.2

private theorem contDiff_one_and_exists_lipschitz_gradient_comp_profile {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {ζ : ℝ → ℝ} {G : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
    (hζ : ContDiff ℝ 2 ζ)
    (hc : HasCompactSupport (fun x => deriv ζ (u x))) :
    ContDiff ℝ 1 (fun x => ζ (u x)) ∧
      ∃ K : NNReal, LipschitzWith K (gradient (fun x => ζ (u x))) := by
  have hζd : ContDiff ℝ 1 (deriv ζ) := hζ.deriv'
  have hcoeff : ContDiff ℝ 1 (fun x => deriv ζ (u x)) := hζd.comp hu
  obtain ⟨Kc, hKc⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hcoeff one_ne_zero
  obtain ⟨⟨K, hK⟩, _⟩ :=
    FunctionalInequalities.Probability.Diffusion.exists_lipschitzWith_smul_of_locallyLipschitz
      hKc hc hG.locallyLipschitz
  refine ⟨(hζ.of_le one_le_two).comp hu, K, ?_⟩
  have heq : gradient (fun x => ζ (u x)) = fun x => deriv ζ (u x) • gradient u x := by
    funext x
    exact BakryEmery.gradient_comp
      ((hζ.differentiable (by norm_num)).differentiableAt)
      ((hu.differentiable one_ne_zero).differentiableAt)
  rw [heq]
  exact hK

private theorem scaled_C1_height_cutoff_family {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
    (hsub : ∀ t : ℝ, IsCompact {x | u x ≤ t}) (c : ℝ) :
    let χ := fun R x => Real.smoothTransition (2 - (u x - c) / R)
    (∀ R : ℝ, 1 ≤ R →
      ContDiff ℝ 1 (χ R) ∧ HasCompactSupport (χ R) ∧
      (∃ K : NNReal, LipschitzWith K (gradient (χ R))) ∧
      HasCompactSupport
        (fun x => deriv (fun s : ℝ => Real.smoothTransition (2 - (s - c) / R)) (u x)) ∧
      ∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧
    (∀ x, MonotoneOn (fun R => χ R x) (Set.Ici 1)) ∧
    ∀ x, Tendsto (fun R => χ R x) atTop (𝓝 1) := by
  let η : ℝ → ℝ := fun s => Real.smoothTransition (2 - s)
  let ζ : ℝ → ℝ → ℝ := fun R s => η ((s - c) / R)
  obtain ⟨hη, _hηanti, hηbounds, _hηone, hηzero, hηderiv,
    _hηsupp, _hηsupp₂, _B, _hB0, _hB⟩ := smoothTransition_two_sub_cutoff
  have hζ (R : ℝ) : ContDiff ℝ ∞ (ζ R) :=
    hη.comp ((contDiff_id.sub contDiff_const).div_const R)
  refine ⟨?_, ?_, ?_⟩
  · intro R hR
    have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
    have hχc : HasCompactSupport (fun x => ζ R (u x)) := by
      apply hasCompactSupport_comp_of_isCompact_sublevel hu.continuous (hsub (c + 2 * R))
      intro s hs
      apply hηzero
      apply (le_div_iff₀ hRp).2
      linarith
    have hcoeff : HasCompactSupport (fun x => deriv (ζ R) (u x)) := by
      apply hasCompactSupport_comp_of_isCompact_sublevel hu.continuous (hsub (c + 3 * R))
      intro s hs
      change deriv (fun t => η ((t - c) / R)) s = 0
      rw [(deriv_comp_sub_div_and_deriv_deriv η c R s).1]
      have ht : 2 < (s - c) / R := by
        apply (lt_div_iff₀ hRp).2
        nlinarith
      rw [(hηderiv ((s - c) / R) (Or.inr ht)).1, mul_zero]
    have hreg := contDiff_one_and_exists_lipschitz_gradient_comp_profile hu hG
      ((hζ R).of_le (WithTop.coe_le_coe.mpr le_top)) hcoeff
    exact ⟨hreg.1, hχc, hreg.2, hcoeff, fun x => hηbounds ((u x - c) / R)⟩
  · intro x
    exact (monotoneOn_and_tendsto_smoothTransition_two_sub_div (u x - c)).1.mono
      (fun R hR => show (0 : ℝ) < R from lt_of_lt_of_le zero_lt_one hR)
  · intro x
    exact (monotoneOn_and_tendsto_smoothTransition_two_sub_div (u x - c)).2

private theorem ae_hessianMatrix_comp_profile {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {ζ : ℝ → ℝ} {G : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
    (hζ : ContDiff ℝ 2 ζ) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ i j : Fin n,
      hessianMatrix (fun y => ζ (u y)) x i j =
        deriv ζ (u x) * hessianMatrix u x i j +
          deriv (deriv ζ) (u x) *
            fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
            fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let χ := fun y => ζ (u y)
  let coeff := fun y => deriv ζ (u y)
  have hζd : ContDiff ℝ 1 (deriv ζ) := hζ.deriv'
  have hcoeff : ContDiff ℝ 1 coeff := hζd.comp hu
  have hgrad : gradient χ = fun y => coeff y • gradient u y := by
    funext y
    exact BakryEmery.gradient_comp
      ((hζ.differentiable (by norm_num)).differentiableAt)
      ((hu.differentiable one_ne_zero).differentiableAt)
  have hcoord (j : Fin n) :
      (fun y => fderiv ℝ χ y (e j)) =
        (fun y => coeff y * fderiv ℝ u y (e j)) := by
    funext y
    have hd := ((hζ.differentiable (by norm_num) (u y)).hasDerivAt.comp_hasFDerivAt
      y (hu.differentiable one_ne_zero y).hasFDerivAt).fderiv
    change fderiv ℝ χ y (e j) = _
    change fderiv ℝ χ y = _ at hd
    rw [hd]
    rfl
  filter_upwards [hG.ae_differentiableAt (μ := volume)] with x hx
  have hχx : DifferentiableAt ℝ (gradient χ) x := by
    rw [hgrad]
    exact ((hcoeff.differentiable one_ne_zero).differentiableAt).smul hx
  have hux := (hu.differentiable one_ne_zero x).hasFDerivAt
  have hcderiv : HasFDerivAt coeff
      (deriv (deriv ζ) (u x) • fderiv ℝ u x) x :=
    (hζd.differentiable one_ne_zero (u x)).hasDerivAt.comp_hasFDerivAt x hux
  intro i j
  have hduj : DifferentiableAt ℝ (fun y => fderiv ℝ u y (e j)) x := by
    simpa [Function.comp_def, inner_gradient_left] using
      (((innerSL ℝ) (e j)).differentiableAt.comp x hx)
  have hprod := (hcderiv.mul hduj.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => coeff y * fderiv ℝ u y (e j)) x = _ at hprod
  calc
    hessianMatrix χ x i j = fderiv ℝ (fun y => fderiv ℝ χ y (e j)) x (e i) :=
      (hessian_coord_of_gradient_diff hχx).symm
    _ = fderiv ℝ (fun y => coeff y * fderiv ℝ u y (e j)) x (e i) := by rw [hcoord j]
    _ = _ := by
      rw [hprod]
      simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
      rw [hessian_coord_of_gradient_diff hx]
      dsimp only [coeff]
      ring

private theorem trace_mul_of_profile_entries {n : ℕ}
    (R H K : Matrix (Fin n) (Fin n) ℝ) (α β : ℝ) (v : Fin n → ℝ)
    (hK : ∀ i j, K i j = α * H i j + β * v i * v j) :
    (R * K).trace = α * (R * H).trace +
      β * (∑ i : Fin n, ∑ j : Fin n, R i j * v i * v j) := by
  have hentry (i j : Fin n) : R i j * K j i =
      α * (R i j * H j i) + β * (R i j * v i * v j) := by
    rw [hK j i]
    ring
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, hentry,
    Finset.sum_add_distrib, ← Finset.mul_sum]

private theorem ae_inverse_hessian_generator_comp_profile {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {ζ : ℝ → ℝ} {G : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
    (hζ : ContDiff ℝ 2 ζ)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det ≠ 0)
    (V : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ((hessianMatrix u x)⁻¹ * hessianMatrix (fun y => ζ (u y)) x).trace -
          fderiv ℝ V (gradient u x) (gradient (fun y => ζ (u y)) x) =
        deriv ζ (u x) * ((n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)) +
          deriv (deriv ζ) (u x) *
            (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
              fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
              fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
  filter_upwards [ae_hessianMatrix_comp_profile hu hG hζ, hdet] with x hc hd
  have htrace := trace_mul_of_profile_entries (hessianMatrix u x)⁻¹
    (hessianMatrix u x) (hessianMatrix (fun y => ζ (u y)) x)
    (deriv ζ (u x)) (deriv (deriv ζ) (u x))
    (fun i => fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i)) hc
  have hRH : (hessianMatrix u x)⁻¹ * hessianMatrix u x = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd)
  have hgrad : gradient (fun y => ζ (u y)) x = deriv ζ (u x) • gradient u x :=
    BakryEmery.gradient_comp ((hζ.differentiable (by norm_num)).differentiableAt)
      ((hu.differentiable one_ne_zero).differentiableAt)
  rw [htrace, hRH, hgrad, map_smul]
  simp only [Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  ring

private theorem exists_bound_moment_gradient_drift {n : ℕ} {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    {L : NNReal} (hL : LipschitzWith L u) (hV : ContDiff ℝ 1 V) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x, |(n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)| ≤ D := by
  have hDV : Continuous (fderiv ℝ V) := hV.continuous_fderiv one_ne_zero
  obtain ⟨M, hM⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (L : ℝ)).exists_bound_of_continuousOn
      hDV.continuousOn
  have hgrad (x : EuclideanSpace ℝ (Fin n)) : ‖gradient u x‖ ≤ (L : ℝ) := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      (norm_fderiv_le_of_lipschitz (x₀ := x) ℝ hL)
  refine
    ⟨(n : ℝ) + max M 0 * (L : ℝ),
      add_nonneg (Nat.cast_nonneg n) (mul_nonneg (le_max_right _ _) L.coe_nonneg), ?_⟩
  intro x
  have hx : gradient u x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (L : ℝ) := by
    simpa only [mem_closedBall, dist_zero_right] using hgrad x
  have hnorm : ‖fderiv ℝ V (gradient u x) (gradient u x)‖ ≤ max M 0 * (L : ℝ) :=
    ((fderiv ℝ V (gradient u x)).le_opNorm (gradient u x)).trans
      (mul_le_mul ((hM _ hx).trans (le_max_left _ _)) (hgrad x) (norm_nonneg _)
        (le_max_right _ _))
  calc
    _ ≤ ‖(n : ℝ)‖ + ‖fderiv ℝ V (gradient u x) (gradient u x)‖ := by
      simpa only [Real.norm_eq_abs] using
        norm_sub_le (n : ℝ) (fderiv ℝ V (gradient u x) (gradient u x))
    _ ≤ _ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
      linarith [hnorm]

private theorem sum_inverse_quadratic_nonneg_of_posDef {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (v : Fin n → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, A⁻¹ i j * v i * v j := by
  calc
    0 ≤ star v ⬝ᵥ (A⁻¹ *ᵥ v) := hA.inv.posSemidef.dotProduct_mulVec_nonneg v
    _ = _ := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

private theorem exists_C1_height_cutoff_generator_majorant_data {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {L G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u) (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V)
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (hessianMatrix u x).PosDef)
    (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1) :
    ∃ c D : ℝ, 0 ≤ D ∧ (∀ x, 1 ≤ u x - c) ∧
      (∀ t : ℝ, IsCompact {x | u x ≤ t}) ∧
      (∀ x, |(n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)| ≤ D) ∧
      let χ := fun R x => Real.smoothTransition (2 - (u x - c) / R)
      let Γ := fun x => ∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j)
      (∀ R : ℝ, 1 ≤ R → ContDiff ℝ 1 (χ R) ∧ HasCompactSupport (χ R) ∧
        (∃ K : NNReal, LipschitzWith K (gradient (χ R))) ∧
        HasCompactSupport
          (fun x => deriv (fun s : ℝ => Real.smoothTransition (2 - (s - c) / R)) (u x)) ∧
        ∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧
      (∀ x, MonotoneOn (fun R => χ R x) (Ici 1)) ∧
      (∀ x, Tendsto (fun R => χ R x) atTop (𝓝 1)) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ Γ x) ∧
      (∀ R : ℝ, 1 ≤ R →
        ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * hessianMatrix (χ R) x).trace -
            fderiv ℝ V (gradient u x) (gradient (χ R) x) =
          deriv (fun s : ℝ => Real.smoothTransition (2 - (s - c) / R)) (u x) *
            ((n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)) +
          deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - (s - c) / R))) (u x) * Γ x) ∧
      ∀ w : ℝ → ℝ, ContDiff ℝ ∞ w → (∀ t, 0 ≤ w t) →
        (∀ t, t ≤ 0 ∨ 3 ≤ t → w t = 0) → ∀ R : ℝ, 0 < R →
        Integrable (fun x => (R ^ 2)⁻¹ * w ((u x - c) / R) * Γ x * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∫ x, (R ^ 2)⁻¹ * w ((u x - c) / R) * Γ x * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
            D * (R⁻¹ * ∫ t in (0 : ℝ)..3, w t) := by
  obtain ⟨⟨y₀, hy₀⟩, hsub⟩ :=
    exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg
      (volume : Measure (EuclideanSpace ℝ (Fin n))) hconv
      (BakryEmery.integrable_exp_neg_of_integral_eq_one
        (volume : Measure (EuclideanSpace ℝ (Fin n))) u hnorm)
  let c : ℝ := u y₀ - 1
  have hshift (x : EuclideanSpace ℝ (Fin n)) : 1 ≤ u x - c := by
    dsimp only [c]
    linarith [hy₀ x]
  obtain ⟨D, hD, hdrift⟩ := exists_bound_moment_gradient_drift hL hV
  obtain ⟨hχ, hmono, hlim⟩ := scaled_C1_height_cutoff_family hu hG hsub c
  refine ⟨c, D, hD, hshift, hsub, hdrift, ?_⟩
  dsimp only
  refine ⟨hχ, hmono, hlim, ?_, ?_, ?_⟩
  · filter_upwards [hPD] with x hx
    exact sum_inverse_quadratic_nonneg_of_posDef (hessianMatrix u x) hx
      (fun i => fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i))
  · intro R _hR
    obtain ⟨hη, _⟩ := smoothTransition_two_sub_cutoff
    have hζ : ContDiff ℝ 2 (fun s : ℝ => Real.smoothTransition (2 - (s - c) / R)) :=
      (hη.comp ((contDiff_id.sub contDiff_const).div_const R)).of_le
        (WithTop.coe_le_coe.mpr le_top)
    exact ae_inverse_hessian_generator_comp_profile hu hG hζ
      (hdet.mono fun x hx => hx.trans_ne (Real.exp_ne_zero _)) V
  · intro w hw hw0 hws R hR
    exact integrable_majorant_inverse_energy_and_integral_le hu hG hV hF hdet
      hnorm hsub hD hdrift hw hw0 hws hR c

private theorem measurable_inverse_hessianMatrix_entry_total {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (i j : Fin n) :
    Measurable (fun x => (hessianMatrix u x)⁻¹ i j) := by
  classical
  let : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (MeasurableSpace (Fin n → Fin n → ℝ))
  let : BorelSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (BorelSpace (Fin n → Fin n → ℝ))
  have hH : Measurable (fun x => hessianMatrix u x) :=
    Measurable.of_eval fun a => Measurable.of_eval fun b =>
      measurable_hessianMatrix_entry u a b
  have hdet : Measurable (fun x => (hessianMatrix u x).det) :=
    (show Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A.det) from
      continuous_id.matrix_det).measurable.comp hH
  have hadj : Measurable (fun x => (hessianMatrix u x).adjugate i j) :=
    ((show Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A.adjugate) from
      continuous_id.matrix_adjugate).matrix_elem i j).measurable.comp hH
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul] using
    hdet.fun_inv.fun_mul hadj

private theorem measurable_inverse_hessian_generator_of_contDiff_one {n : ℕ}
    {u V f : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V) (hf : ContDiff ℝ 1 f) :
    Measurable (fun x => ((hessianMatrix u x)⁻¹ * hessianMatrix f x).trace -
      fderiv ℝ V (gradient u x) (gradient f x)) := by
  classical
  have hsum := Finset.measurable_fun_sum Finset.univ fun i _ =>
    Finset.measurable_fun_sum Finset.univ fun j _ =>
      (measurable_inverse_hessianMatrix_entry_total u i j).fun_mul
        (measurable_hessianMatrix_entry f j i)
  have htrace : Measurable (fun x => ((hessianMatrix u x)⁻¹ * hessianMatrix f x).trace) := by
    simpa only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply] using hsum
  have hdrift : Continuous (fun x => fderiv ℝ V (gradient u x) (gradient f x)) :=
    ((hV.continuous_fderiv one_ne_zero).comp hG.continuous).clm_apply
      (BakryEmery.continuous_gradient hf)
  exact htrace.fun_sub hdrift.measurable

private theorem exists_C1_height_generator_defect_bound {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V)
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).PosDef)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    (hsub : ∀ t : ℝ, IsCompact {x | u x ≤ t})
    {D : ℝ} (hD : 0 ≤ D)
    (hdrift : ∀ x, |(n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)| ≤ D)
    (c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      let χ := fun x => Real.smoothTransition (2 - (u x - c) / R)
      let Lχ := fun x => ((hessianMatrix u x)⁻¹ * hessianMatrix χ x).trace -
        fderiv ℝ V (gradient u x) (gradient χ x)
      Integrable (fun x => Lχ x * Real.exp (-u x))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, |Lχ x| * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤ C / R := by
  classical
  let η : ℝ → ℝ := fun t => Real.smoothTransition (2 - t)
  obtain ⟨hη, _, _, _, _, _, _, _, B, hB, hBbound⟩ :=
    smoothTransition_two_sub_cutoff
  obtain ⟨w, hw, _, hw0, hws, hwbound⟩ :=
    exists_majorant_abs_deriv_deriv_smoothTransition_two_sub
  have hIw : 0 ≤ ∫ t in (0 : ℝ)..3, w t :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) hw0
  refine ⟨D * (B + ∫ t in (0 : ℝ)..3, w t),
    mul_nonneg hD (add_nonneg hB hIw), ?_⟩
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hRi : 0 ≤ R⁻¹ := inv_nonneg.mpr hRpos.le
  let ζ : ℝ → ℝ := fun s => η ((s - c) / R)
  let χ : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ζ (u x)
  let L : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    ((hessianMatrix u x)⁻¹ * hessianMatrix χ x).trace -
      fderiv ℝ V (gradient u x) (gradient χ x)
  let Γ : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    ∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
      fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
      fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j)
  let q : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    (R ^ 2)⁻¹ * w ((u x - c) / R) * Γ x * Real.exp (-u x)
  change Integrable (fun x => L x * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, |L x| * Real.exp (-u x)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        D * (B + ∫ t in (0 : ℝ)..3, w t) / R
  have hζ : ContDiff ℝ ∞ ζ :=
    hη.comp ((contDiff_id.sub contDiff_const).div_const R)
  have hζ1 : ContDiff ℝ 1 ζ :=
    hζ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hζ2 : ContDiff ℝ 2 ζ :=
    hζ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hL : Measurable L :=
    measurable_inverse_hessian_generator_of_contDiff_one hG hV (hζ1.comp hu)
  have hexpm : Measurable (fun x => Real.exp (-u x)) :=
    (Real.continuous_exp.comp hu.continuous.neg).measurable
  have hexp := BakryEmery.integrable_exp_neg_of_integral_eq_one
    (volume : Measure (EuclideanSpace ℝ (Fin n))) u hnorm
  have hp := integrable_majorant_inverse_energy_and_integral_le
    hu hG hV hF hdet hnorm hsub hD hdrift hw hw0 hws hRpos c
  have hq : Integrable q (volume : Measure (EuclideanSpace ℝ (Fin n))) := hp.1
  have hqbound :
      (∫ x, q x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        D * (R⁻¹ * ∫ t in (0 : ℝ)..3, w t) := hp.2
  have hfirst := hexp.const_mul (B * D / R)
  have hmajor : Integrable
      (fun x => (B * D / R) * Real.exp (-u x) + q x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := hfirst.add hq
  have hdet0 : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det ≠ 0 :=
    hdet.mono fun x hx => hx.trans_ne (Real.exp_ne_zero _)
  have hgen := ae_inverse_hessian_generator_comp_profile hu hG hζ2 hdet0 V
  have hpoint : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      |L x| * Real.exp (-u x) ≤
        (B * D / R) * Real.exp (-u x) + q x := by
    filter_upwards [hgen, hPD] with x hx hPx
    change L x =
      deriv ζ (u x) * ((n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)) +
        deriv (deriv ζ) (u x) * Γ x at hx
    have hΓ : 0 ≤ Γ x :=
      sum_inverse_quadratic_nonneg_of_posDef (hessianMatrix u x) hPx
        (fun i => fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i))
    have hd :
        deriv ζ (u x) = R⁻¹ * deriv η ((u x - c) / R) ∧
        deriv (deriv ζ) (u x) =
          (R⁻¹) ^ 2 * deriv (deriv η) ((u x - c) / R) :=
      deriv_comp_sub_div_and_deriv_deriv η c R (u x)
    have habs1 :
        |R⁻¹ * deriv η ((u x - c) / R) *
          ((n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x))| ≤ B * D / R := by
      calc
        _ = R⁻¹ * (|deriv η ((u x - c) / R)| *
            |(n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)|) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hRi]
          ring
        _ ≤ R⁻¹ * (B * D) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (hBbound ((u x - c) / R)).1 (hdrift x)
              (abs_nonneg _) hB) hRi
        _ = B * D / R := by
          rw [div_eq_mul_inv]
          ring
    have habs2 :
        |(R⁻¹) ^ 2 * deriv (deriv η) ((u x - c) / R) * Γ x| ≤
          (R ^ 2)⁻¹ * w ((u x - c) / R) * Γ x := by
      rw [abs_mul, abs_mul, abs_of_nonneg hΓ,
        abs_of_nonneg (sq_nonneg R⁻¹), inv_pow]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hwbound ((u x - c) / R))
          (inv_nonneg.mpr (sq_nonneg R))) hΓ
    calc
      |L x| * Real.exp (-u x) =
          |R⁻¹ * deriv η ((u x - c) / R) *
              ((n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)) +
            (R⁻¹) ^ 2 * deriv (deriv η) ((u x - c) / R) * Γ x| *
              Real.exp (-u x) := by rw [hx, hd.1, hd.2]
      _ ≤ (|R⁻¹ * deriv η ((u x - c) / R) *
              ((n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x))| +
            |(R⁻¹) ^ 2 * deriv (deriv η) ((u x - c) / R) * Γ x|) *
              Real.exp (-u x) :=
        mul_le_mul_of_nonneg_right (abs_add_le _ _) (Real.exp_pos _).le
      _ ≤ (B * D / R + (R ^ 2)⁻¹ * w ((u x - c) / R) * Γ x) *
              Real.exp (-u x) :=
        mul_le_mul_of_nonneg_right (add_le_add habs1 habs2) (Real.exp_pos _).le
      _ = (B * D / R) * Real.exp (-u x) + q x := by
        dsimp only [q]
        ring
  have hweighted : Integrable (fun x => L x * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hmajor.mono' (hL.fun_mul hexpm).aestronglyMeasurable
      (hpoint.mono fun x hx => by
        simpa only [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (Real.exp_pos (-u x)).le] using hx)
  have habsweighted : Integrable (fun x => |L x| * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hweighted.abs.congr (Filter.Eventually.of_forall fun x => by
      change |L x * Real.exp (-u x)| = |L x| * Real.exp (-u x)
      rw [abs_mul, abs_of_nonneg (Real.exp_pos (-u x)).le])
  refine ⟨hweighted, ?_⟩
  calc
    _ ≤ ∫ x, (B * D / R) * Real.exp (-u x) + q x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      integral_mono_ae habsweighted hmajor hpoint
    _ = B * D / R + ∫ x, q x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      rw [integral_add hfirst hq, integral_const_mul, hnorm, mul_one]
    _ ≤ B * D / R + D * (R⁻¹ * ∫ t in (0 : ℝ)..3, w t) :=
      add_le_add le_rfl hqbound
    _ = D * (B + ∫ t in (0 : ℝ)..3, w t) / R := by
      simp only [div_eq_mul_inv]
      ring


/-- The real-parameter weak C1 inverse-Hessian height cutoffs, with vanishing generator defect. -/
theorem exists_scaled_weak_inverse_hessian_cutoffs {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {L G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u) (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V)
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (hessianMatrix u x).PosDef)
    (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1) :
    ∃ c C : ℝ, 0 ≤ C ∧ (∀ x, 1 ≤ u x - c) ∧
      let χ := fun R x => Real.smoothTransition (2 - (u x - c) / R)
      let Lχ := fun R x => ((hessianMatrix u x)⁻¹ * hessianMatrix (χ R) x).trace -
        fderiv ℝ V (gradient u x) (gradient (χ R) x)
      (∀ R : ℝ, 1 ≤ R → ContDiff ℝ 1 (χ R) ∧ HasCompactSupport (χ R) ∧
        (∃ K : NNReal, LipschitzWith K (gradient (χ R))) ∧
        ∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧
      (∀ x, MonotoneOn (fun R => χ R x) (Ici 1)) ∧
      (∀ x, Tendsto (fun R => χ R x) atTop (𝓝 1)) ∧
      (∀ R : ℝ, 1 ≤ R → Integrable (Lχ R)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ∧
      (∀ R : ℝ, 1 ≤ R → (∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ C / R) ∧
      Tendsto (fun R : ℝ => ∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) atTop (𝓝 0) := by
  obtain ⟨c, D, hD, hshift, hsub, hdrift, hχ, hmono, hlim, _hΓ, _hgen, _hmajor⟩ :=
    exists_C1_height_cutoff_generator_majorant_data hu hL hG hV hF hdet hPD hconv hnorm
  obtain ⟨C, hC, hcore⟩ := exists_C1_height_generator_defect_bound
    hu hG hV hF hdet hPD hnorm hsub hD hdrift c
  let χ := fun R x => Real.smoothTransition (2 - (u x - c) / R)
  let Lχ := fun R x => ((hessianMatrix u x)⁻¹ * hessianMatrix (χ R) x).trace -
    fderiv ℝ V (gradient u x) (gradient (χ R) x)
  have hexp := BakryEmery.integrable_exp_neg_of_integral_eq_one
    (volume : Measure (EuclideanSpace ℝ (Fin n))) u hnorm
  have hweighted (R : ℝ) (hR : 1 ≤ R) :
      Integrable (fun x => Lχ R x * Real.exp (-u x))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, |Lχ R x| * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤ C / R := hcore R hR
  have hint (R : ℝ) (hR : 1 ≤ R) : Integrable (Lχ R)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) := by
    apply (integrable_tilted_iff hexp (Lχ R)).mpr
    simpa only [Pi.neg_apply, smul_eq_mul, mul_comm] using (hweighted R hR).1
  have heq (R : ℝ) :
      (∫ x, |Lχ R x| ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
      ∫ x, |Lχ R x| * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [integral_tilted]
    simp only [Pi.neg_apply, hnorm, div_one, smul_eq_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have hbound (R : ℝ) (hR : 1 ≤ R) :
      (∫ x, |Lχ R x| ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ C / R := by
    rw [heq]
    exact (hweighted R hR).2
  have hdecay : Tendsto (fun R : ℝ => ∫ x, |Lχ R x|
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) atTop (𝓝 0) := by
    have hCdiv : Tendsto (fun R : ℝ => C / R) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using
        (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0)).const_mul C
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hCdiv
    · exact Filter.Eventually.of_forall fun R => integral_nonneg fun x => abs_nonneg _
    · exact Filter.eventually_atTop.mpr ⟨1, fun R hR => hbound R hR⟩
  refine ⟨c, C, hC, hshift, ?_, hmono, hlim, hint, hbound, hdecay⟩
  intro R hR
  obtain ⟨hC1, hcomp, hLip, _hderiv, hRange⟩ := hχ R hR
  exact ⟨hC1, hcomp, hLip, hRange⟩

/-- The natural-index form, using the same height cutoffs at radius m+1. -/
theorem exists_weak_inverse_hessian_cutoffs {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {L G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u) (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V)
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (hessianMatrix u x).PosDef)
    (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1) :
    ∃ c C : ℝ, 0 ≤ C ∧ (∀ x, 1 ≤ u x - c) ∧
      let χ := fun (m : ℕ) x => Real.smoothTransition (2 - (u x - c) / ((m : ℝ) + 1))
      let Lχ := fun m x => ((hessianMatrix u x)⁻¹ * hessianMatrix (χ m) x).trace -
        fderiv ℝ V (gradient u x) (gradient (χ m) x)
      (∀ m : ℕ, ContDiff ℝ 1 (χ m) ∧ HasCompactSupport (χ m) ∧
        (∃ K : NNReal, LipschitzWith K (gradient (χ m))) ∧
        ∀ x, 0 ≤ χ m x ∧ χ m x ≤ 1) ∧
      (∀ x, Monotone (fun m : ℕ => χ m x)) ∧
      (∀ x, Tendsto (fun m : ℕ => χ m x) atTop (𝓝 1)) ∧
      (∀ m : ℕ, Integrable (Lχ m)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ∧
      (∀ m : ℕ, (∫ x, |Lχ m x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ C / ((m : ℝ) + 1)) ∧
      Tendsto (fun m : ℕ => ∫ x, |Lχ m x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) atTop (𝓝 0) := by
  obtain ⟨c, C, hC, hshift, hχ, hmono, hlim, hint, hbound, hdecay⟩ :=
    exists_scaled_weak_inverse_hessian_cutoffs hu hL hG hV hF hdet hPD hconv hnorm
  have h1 (m : ℕ) : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hT : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  refine ⟨c, C, hC, hshift, (fun m => hχ _ (h1 m)), ?_,
    (fun x => (hlim x).comp hT), (fun m => hint _ (h1 m)),
    (fun m => hbound _ (h1 m)), hdecay.comp hT⟩
  intro x a b hab
  apply hmono x (Set.mem_Ici.mpr (h1 a)) (Set.mem_Ici.mpr (h1 b))
  have hab' : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr hab
  linarith

private theorem hasCompactSupport_inverse_hessian_cutoff_flux_generator {n : ℕ}
    (u V χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : HasCompactSupport χ) :
    (∀ i j : Fin n, HasCompactSupport (fun x => hessianMatrix χ x i j)) ∧
    (∀ i : Fin n, HasCompactSupport (fun x => Real.exp (-u x) *
      ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ j))) ∧
    HasCompactSupport (fun x =>
      (((hessianMatrix u x)⁻¹ * hessianMatrix χ x).trace -
        fderiv ℝ V (gradient u x) (gradient χ x)) * Real.exp (-u x)) := by
  have hd (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ tsupport χ) :
      fderiv ℝ χ x = 0 := fderiv_of_notMem_tsupport ℝ hx
  have hdd (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ tsupport χ) :
      fderiv ℝ (fderiv ℝ χ) x = 0 := by
    exact fderiv_of_notMem_tsupport ℝ (fun h => hx ((tsupport_fderiv_subset ℝ) h))
  have hH (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ tsupport χ) :
      hessianMatrix χ x = 0 := by
    ext i j
    simp [hessianMatrix, bilinearIteratedFDerivTwo, hdd x hx]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    apply HasCompactSupport.intro hχ
    intro x hx
    simp [hH x hx]
  · intro i
    apply HasCompactSupport.intro hχ
    intro x hx
    simp [hd x hx]
  · apply HasCompactSupport.intro hχ
    intro x hx
    have hg : gradient χ x = 0 := by simp [gradient, hd x hx]
    simp [hH x hx, hg]

/--
A globally bounded locally integrable weak function `η` with compact-local L2 coordinate weak
derivatives `aᵢ`,
paired with the inverse-Hessian generator of a compactly supported C1 cutoff `χ` with Lipschitz
gradient at a C1
Monge–Ampère potential `u`: both pairings are integrable and the generator pairing equals minus the
weighted energy
pairing `∫ ∑ (∇²u)⁻¹ᵢⱼ aᵢ ∂ⱼχ e^{-u}`. -/
theorem integral_rough_mul_generator_eq_neg_energy_of_contDiff_one {n : ℕ}
    {u V χ η : EuclideanSpace ℝ (Fin n) → ℝ} {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hχ : ContDiff ℝ 1 χ) {Gχ : NNReal} (hGχ : LipschitzWith Gχ (gradient χ))
    (hχc : HasCompactSupport χ)
    (hInv :
      ∀ i j : Fin n,
        ∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
              ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hForce :
      Integrable
        (fun x =>
          (((hessianMatrix u x)⁻¹ * hessianMatrix χ x).trace -
              fderiv ℝ V (gradient u x) (gradient χ x)) *
            Real.exp (-u x))
        (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n)))) {C : ℝ}
    (hbound : ∀ x, ‖η x‖ ≤ C)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 :
      ∀ i : Fin n,
        ∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    Integrable
        (fun x =>
          η x *
              (((hessianMatrix u x)⁻¹ * hessianMatrix χ x).trace -
                fderiv ℝ V (gradient u x) (gradient χ x)) *
            Real.exp (-u x))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      Integrable
          (fun x =>
            (∑ i : Fin n,
                ∑ j : Fin n,
                  (hessianMatrix u x)⁻¹ i j * a i x *
                    fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ j)) *
              Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∫ x,
            η x *
                (((hessianMatrix u x)⁻¹ * hessianMatrix χ x).trace -
                  fderiv ℝ V (gradient u x) (gradient χ x)) *
              Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          -(∫ x,
              (∑ i : Fin n,
                  ∑ j : Fin n,
                    (hessianMatrix u x)⁻¹ i j * a i x *
                      fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ j)) *
                Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let J := fun i x =>
    Real.exp (-u x) * ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j * fderiv ℝ χ x (e j)
  let F := fun x =>
    (((hessianMatrix u x)⁻¹ * hessianMatrix χ x).trace -
        fderiv ℝ V (gradient u x) (gradient χ x)) *
      Real.exp (-u x)
  have he : Continuous (fun x => Real.exp (-u x)) := Real.continuous_exp.comp hu.continuous.neg
  have hcoord (j : Fin n) : Continuous (fun x => fderiv ℝ χ x (e j)) :=
    (hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hJ (i : Fin n) (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
    MemLp (J i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    have hsum :
      MemLp (fun x => ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j * fderiv ℝ χ x (e j)) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
      apply memLp_finsetSum Finset.univ
      intro j _
      exact (hInv i j S hS).fun_mul (memLp_top_restrict_of_continuous (hcoord j) S hS)
    have hp :
      MemLp (J i) (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      (memLp_top_restrict_of_continuous he S hS).fun_mul hsum
    exact hp.mono_exponent (by norm_num)
  have hsupport := hasCompactSupport_inverse_hessian_cutoff_flux_generator u V χ hχc
  have hJeq (b : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    (∑ i : Fin n, J i x * b i x) =
      (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j * b i x * fderiv ℝ χ x (e j)) *
        Real.exp (-u x) := by
    simp only [J, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hFeq (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    F x * ψ x =
      ψ x *
          (((hessianMatrix u x)⁻¹ * hessianMatrix χ x).trace -
            fderiv ℝ V (gradient u x) (gradient χ x)) *
        Real.exp (-u x) := by
    dsimp only [F]; ring
  have hId (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) :
    (∫ x,
        ∑ i : Fin n,
          J i x * fderiv ℝ ψ x (e i) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    have hp :=
      integral_mul_generator_eq_neg_energy_of_contDiff_one hu hG hV hF hdet hχ hGχ hψ hψc
    have hj :=
      integral_congr_ae (μ := volume)
        (Filter.Eventually.of_forall (hJeq (fun i x => fderiv ℝ ψ x (e i))))
    have hf := integral_congr_ae (μ := volume) (Filter.Eventually.of_forall (hFeq ψ))
    rw [hj, hf]
    simpa only [neg_neg] using (congrArg Neg.neg hp).symm
  obtain ⟨hprod, hforce, hEq⟩ :=
    integral_compact_flux_eq_neg_forcing_of_global_bounded_weak_test hJ hForce.locallyIntegrable
      hsupport.2.1 hsupport.2.2 hId hη hbound hweak ha2
  have hE :
    Integrable (fun x => ∑ i : Fin n, J i x * a i x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    integrable_finsetSum Finset.univ fun i _ => hprod i
  refine
    ⟨hforce.congr (Filter.Eventually.of_forall (hFeq η)),
      hE.congr (Filter.Eventually.of_forall (hJeq a)), ?_⟩
  have hj := integral_congr_ae (μ := volume) (Filter.Eventually.of_forall (hJeq a))
  have hf := integral_congr_ae (μ := volume) (Filter.Eventually.of_forall (hFeq η))
  rw [hj, hf] at hEq
  simpa only [neg_neg] using (congrArg Neg.neg hEq).symm

end FunctionalInequalities.Analysis
