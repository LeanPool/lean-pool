/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.MongeAmpere
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# A regularized maximum preserving smooth plurisubharmonicity

`smoothMax x y = y + P(x - y)`, where `P` is a smooth convex primitive of a
smooth transition, equal to `0` on `(-∞, -1]` and to `t` on `[1, ∞)`. It is
nondecreasing in both arguments, equals `max x y` when `|x - y| ≥ 1`, and the
complex Hessian of `smoothMax f g` is
`(1 - S) H_g + S H_f + S' · ∂(f-g) ∂(f-g)*`, which is positive semidefinite
whenever `H_f` and `H_g` are.
-/

@[expose] public section

open Set Filter Real
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.SmoothMax

noncomputable section

/-- The smooth transition from `0` at `-1` to `1` at `1`. -/
def trans (t : ℝ) : ℝ := smoothTransition ((t + 1) / 2)

theorem smoothTransition_one_sub (x : ℝ) : smoothTransition (1 - x) = 1 - smoothTransition x := by
  have hd := smoothTransition.pos_denom x
  simp only [smoothTransition, sub_sub_cancel]
  rw [eq_sub_iff_add_eq, add_comm (expNegInvGlue (1 - x)), ← add_div, add_comm (expNegInvGlue (1 -
    x)),
    div_self hd.ne']

theorem trans_neg (t : ℝ) : trans (-t) = 1 - trans t := by
  rw [trans, trans, ← smoothTransition_one_sub]
  congr 1
  ring

theorem contDiff_trans : ContDiff ℝ ∞ trans :=
  smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const 2)

theorem trans_nonneg (t : ℝ) : 0 ≤ trans t := smoothTransition.nonneg _

theorem trans_le_one (t : ℝ) : trans t ≤ 1 := smoothTransition.le_one _

theorem trans_eq_zero {t : ℝ} (ht : t ≤ -1) : trans t = 0 :=
  smoothTransition.zero_of_nonpos (by linarith)

theorem trans_eq_one {t : ℝ} (ht : 1 ≤ t) : trans t = 1 :=
  smoothTransition.one_of_one_le (by linarith)

theorem trans_monotone : Monotone trans := fun _ _ h ↦
  smoothTransition.monotone (by linarith)

theorem continuous_trans : Continuous trans := contDiff_trans.continuous

/-- The smooth positive part: `0` on `(-∞, -1]`, `t` on `[1, ∞)`, with derivative `trans`. -/
def posPart (t : ℝ) : ℝ := ∫ s in (-1 : ℝ)..t, trans s

theorem hasDerivAt_posPart (t : ℝ) : HasDerivAt posPart (trans t) t :=
  (continuous_trans.integral_hasStrictDerivAt (-1) t).hasDerivAt

theorem deriv_posPart : deriv posPart = trans := funext fun t ↦ (hasDerivAt_posPart t).deriv

theorem contDiff_posPart : ContDiff ℝ ∞ posPart := by
  rw [contDiff_infty_iff_deriv, deriv_posPart]
  exact ⟨fun t ↦ (hasDerivAt_posPart t).differentiableAt, contDiff_trans⟩

theorem posPart_eq_zero {t : ℝ} (ht : t ≤ -1) : posPart t = 0 := by
  unfold posPart
  rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun s hs ↦ ?_]
  · simp
  · rw [uIcc_of_ge ht] at hs
    exact trans_eq_zero hs.2

theorem integral_trans_symm : ∫ s in (-1 : ℝ)..1, trans s = 1 := by
  have hint : IntervalIntegrable trans MeasureTheory.volume (-1) 1 :=
    continuous_trans.intervalIntegrable _ _
  have hneg : ∫ s in (-1 : ℝ)..1, trans (-s) = ∫ s in (-1 : ℝ)..1, trans s := by
    rw [intervalIntegral.integral_comp_neg]
    norm_num
  have hsum : ∫ s in (-1 : ℝ)..1, (trans s + trans (-s)) = 2 := by
    simp only [trans_neg, add_sub_cancel]
    norm_num
  have hint' : IntervalIntegrable (fun s ↦ trans (-s)) MeasureTheory.volume (-1) 1 :=
    (continuous_trans.comp continuous_neg).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hint hint', hneg] at hsum
  linarith

theorem posPart_eq_self {t : ℝ} (ht : 1 ≤ t) : posPart t = t := by
  unfold posPart
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1)
    (continuous_trans.intervalIntegrable _ _) (continuous_trans.intervalIntegrable _ _),
    integral_trans_symm, intervalIntegral.integral_congr (g := fun _ ↦ (1 : ℝ)) fun s hs ↦ ?_]
  · simp
  · rw [uIcc_of_le ht] at hs
    exact trans_eq_one hs.1

section Chain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Second-order chain rule for a smooth scalar function of a `C²` function. -/
theorem realHessian_comp {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {k : E → ℝ} {z : E}
    (hk : ContDiffAt ℝ 2 k z) (v w : E) :
    realHessian (φ ∘ k) z v w =
      deriv (deriv φ) (k z) * (fderiv ℝ k z v * fderiv ℝ k z w) +
        deriv φ (k z) * realHessian k z v w := by
  have hD : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ k y :=
    (hk.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by simp)
  have hDD : DifferentiableAt ℝ (fderiv ℝ k) z :=
    (hk.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hφ1 : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφ2 : Differentiable ℝ (deriv φ) :=
    (contDiff_infty_iff_deriv.mp hφ).2.differentiable (by simp)
  have hev : fderiv ℝ (φ ∘ k) =ᶠ[𝓝 z] fun y ↦ deriv φ (k y) • fderiv ℝ k y := by
    filter_upwards [hD] with y hy
    rw [fderiv_comp y (hφ1 (k y)) hy]
    ext u
    simp [fderiv_eq_smul_deriv, mul_comm]
  have hc : HasFDerivAt (fun y ↦ deriv φ (k y))
      (deriv (deriv φ) (k z) • fderiv ℝ k z) z := by
    have := (hφ2 (k z)).hasDerivAt.comp_hasFDerivAt z (hk.differentiableAt (by simp)).hasFDerivAt
    simpa [Function.comp_def] using this
  have hsm : HasFDerivAt (fun y ↦ deriv φ (k y) • fderiv ℝ k y)
      (deriv φ (k z) • fderiv ℝ (fderiv ℝ k) z +
        (deriv (deriv φ) (k z) • fderiv ℝ k z).smulRight (fderiv ℝ k z)) z :=
    hc.smul hDD.hasFDerivAt
  rw [realHessian_eq_fderiv, hev.fderiv_eq, hsm.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rw [realHessian_eq_fderiv]
  ring

end Chain

section Hessian

open FirstPass FirstPass.MongeAmpere Complex

variable {n : ℕ}

/-- The `∂`-gradient `(∂k/∂zⱼ)ⱼ` of a real function. -/
def delGrad (k : ComplexModel n → ℝ) (z : ComplexModel n) : Fin n → ℂ := fun j ↦
  ((fderiv ℝ k z (coordinateVector j) : ℂ) - I * (fderiv ℝ k z (I • coordinateVector j) : ℂ)) / 2

theorem complexHessian_comp {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {k : ComplexModel n → ℝ}
    {z : ComplexModel n} (hk : ContDiffAt ℝ 2 k z) :
    complexHessian (φ ∘ k) z =
      deriv φ (k z) • complexHessian k z +
        deriv (deriv φ) (k z) • Matrix.vecMulVec (delGrad k z) (star (delGrad k z)) := by
  ext j l
  simp only [complexHessian, realHessian_comp hφ hk, Matrix.add_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, delGrad, Pi.star_apply, real_smul]
  simp only [star_div₀, star_sub, star_mul', conj_I, ofReal_add, ofReal_mul, ofReal_sub,
    Complex.star_def, conj_ofReal, map_ofNat]
  ring_nf
  rw [I_sq]
  ring

/-- The quadratic collar vanishes at distance `R` from its center. -/
def quadraticCollar {V : Type*} [NormedAddCommGroup V] (center : V)
    (amplitude radius : ℝ) (z : V) : ℝ :=
  amplitude * (‖z - center‖ ^ 2 - radius ^ 2)

/-- The quadratic collar is smooth on a real inner product space. -/
theorem contDiff_quadraticCollar {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (center : V) (amplitude radius : ℝ) : ContDiff ℝ ∞ (quadraticCollar center amplitude radius) :=
  contDiff_const.mul (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).sub
    contDiff_const)

/-- The regularized maximum `smoothMax f g = g + P(f - g)`. -/
def smoothMax {E : Type*} (f g : E → ℝ) : E → ℝ := fun z ↦ g z + posPart (f z - g z)

theorem posPart_monotone : Monotone posPart :=
  monotone_of_deriv_nonneg (contDiff_posPart.differentiable (by simp))
    fun t ↦ by rw [deriv_posPart]; exact trans_nonneg t

theorem sub_posPart_monotone : Monotone fun t ↦ t - posPart t := by
  have hd : Differentiable ℝ fun t ↦ t - posPart t :=
    differentiable_id.sub (contDiff_posPart.differentiable (by simp))
  refine monotone_of_deriv_nonneg hd fun t ↦ ?_
  have h : HasDerivAt (fun t ↦ t - posPart t) (1 - trans t) t :=
    (hasDerivAt_id' t).sub (hasDerivAt_posPart t)
  rw [h.deriv]
  linarith [trans_le_one t]

/-- The smooth positive part majorizes the identity. -/
theorem le_posPart (t : ℝ) : t ≤ posPart t := by
  rcases le_total t 1 with h | h
  · have := sub_posPart_monotone h
    simp only [posPart_eq_self le_rfl, sub_self] at this
    linarith
  · rw [posPart_eq_self h]

/-- The smooth positive part is nonnegative. -/
theorem posPart_nonneg (t : ℝ) : 0 ≤ posPart t := by
  rcases le_total t (-1) with h | h
  · rw [posPart_eq_zero h]
  · have := posPart_monotone h
    rwa [posPart_eq_zero le_rfl] at this

/-- The positive part at inputs at most one is at most one. -/
theorem posPart_le_one {t : ℝ} (ht : t ≤ 1) : posPart t ≤ 1 := by
  have := posPart_monotone ht
  rwa [posPart_eq_self le_rfl] at this

theorem smoothMax_mono {E : Type*} {f f' g g' : E → ℝ} {z : E} (hf : f z ≤ f' z)
    (hg : g z ≤ g' z) : smoothMax f g z ≤ smoothMax f' g' z := by
  unfold smoothMax
  have h1 : posPart (f z - g z) ≤ posPart (f' z - g z) := posPart_monotone (by linarith)
  have h2 := sub_posPart_monotone (show f' z - g' z ≤ f' z - g z by linarith)
  simp only at h2
  linarith

theorem smoothMax_eq_left {E : Type*} {f g : E → ℝ} {z : E} (h : g z + 1 ≤ f z) :
    smoothMax f g z = f z := by
  simp [smoothMax, posPart_eq_self (show 1 ≤ f z - g z by linarith)]

theorem smoothMax_eq_right {E : Type*} {f g : E → ℝ} {z : E} (h : f z + 1 ≤ g z) :
    smoothMax f g z = g z := by
  simp [smoothMax, posPart_eq_zero (show f z - g z ≤ -1 by linarith)]

theorem complexHessian_smoothMax_posSemidef {f g : ComplexModel n → ℝ} {z : ComplexModel n}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (hHf : (complexHessian f z).PosSemidef) (hHg : (complexHessian g z).PosSemidef) :
    (complexHessian (smoothMax f g) z).PosSemidef := by
  have hk : ContDiffAt ℝ 2 (f - g) z := hf.sub hg
  have hP : ContDiffAt ℝ 2 (posPart ∘ (f - g)) z :=
    (contDiff_posPart.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp z hk
  have hsm : smoothMax f g = g + posPart ∘ (f - g) := rfl
  have hsub : complexHessian (f - g) z = complexHessian f z - complexHessian g z := by
    rw [show f - g = f + (-1 : ℝ) • g by funext x; simp [sub_eq_add_neg],
      complexHessian_add (v := (-1 : ℝ) • g) hf (hg.const_smul (-1 : ℝ)),
      complexHessian_smul hg]
    simp [sub_eq_add_neg]
  rw [hsm, complexHessian_add hg hP, complexHessian_comp contDiff_posPart hk, deriv_posPart, hsub]
  set S := trans ((f - g) z)
  have hS0 := trans_nonneg ((f - g) z)
  have hS1 := trans_le_one ((f - g) z)
  have hS' : 0 ≤ deriv trans ((f - g) z) := trans_monotone.deriv_nonneg
  have e : complexHessian g z + (S • (complexHessian f z - complexHessian g z) +
      deriv trans ((f - g) z) • Matrix.vecMulVec (delGrad (f - g) z) (star (delGrad (f - g) z))) =
      ((1 - S) • complexHessian g z + S • complexHessian f z) +
        deriv trans ((f - g) z) • Matrix.vecMulVec (delGrad (f - g) z)
          (star (delGrad (f - g) z)) := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  rw [e]
  exact ((hHg.smul (by linarith)).add (hHf.smul hS0)).add
    ((Matrix.posSemidef_vecMulVec_self_star _).smul hS')

end Hessian

end

end SGPT.Foundations.Analysis.Pending.SmoothMax
