/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierSpace

/-!
# The energy identity of one damped frequency

At a fixed frequency the mild equation of `lem:regularised-forced` is the
damped Duhamel formula `y(t) = e^{-λt} y₀ + ∫₀ᵗ e^{-λ(t-s)} g(s) ds` with an
integrable source. Its squared modulus satisfies the energy identity
`|y(t)|² + 2λ ∫₀ᵗ |y|² = |y₀|² + 2 ∫₀ᵗ Re ⟨y, g⟩`, first for real components
through the fundamental theorem of calculus for absolutely continuous
functions, then for complex three-vectors.
-/

public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace CKN.Leray

/-- The energy identity for a real damped Duhamel formula with integrable
source. -/
theorem damped_duhamel_sq_identity (lam a0 : ℝ) (g a : ℝ → ℝ) {t : ℝ}
    (hg : IntervalIntegrable g volume 0 t)
    (ha : ∀ τ ∈ uIcc 0 t, a τ = Real.exp (-lam * τ) * a0 +
      ∫ s in (0 : ℝ)..τ, Real.exp (-lam * (τ - s)) * g s) :
    a t ^ 2 + 2 * lam * ∫ s in (0 : ℝ)..t, a s ^ 2 =
      a0 ^ 2 + 2 * ∫ s in (0 : ℝ)..t, a s * g s := by
  let e : ℝ → ℝ := fun s => Real.exp (lam * s) * g s
  have heint : IntervalIntegrable e volume 0 t :=
    hg.continuousOn_mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  let A : ℝ → ℝ := fun τ => a0 + ∫ s in (0 : ℝ)..τ, e s
  have haA : ∀ τ ∈ uIcc 0 t, a τ = Real.exp (-lam * τ) * A τ := by
    intro τ hτ
    rw [ha τ hτ]
    simp only [A, mul_add]
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    simp only [e]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hAac : AbsolutelyContinuousOnInterval A 0 t := by
    have h1 : AbsolutelyContinuousOnInterval (fun _ : ℝ => a0) 0 t :=
      (contDiffOn_const (c := a0)).absolutelyContinuousOnInterval
    have h2 := heint.absolutelyContinuousOnInterval_intervalIntegral
      (c := 0) Set.left_mem_uIcc
    exact h1.add h2
  let E : ℝ → ℝ := fun τ => Real.exp (-(2 * lam) * τ)
  have hEdiff : ∀ τ, HasDerivAt E (-(2 * lam) * E τ) τ := by
    intro τ
    have h := ((hasDerivAt_id τ).const_mul (-(2 * lam))).exp
    simpa [E, mul_comm] using h
  have hEac : AbsolutelyContinuousOnInterval E 0 t := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    exact (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffOn
  let φ : ℝ → ℝ := fun τ => E τ * (A τ * A τ)
  have hφac : AbsolutelyContinuousOnInterval φ 0 t :=
    hEac.fun_mul (hAac.fun_mul hAac)
  have hφa : ∀ τ ∈ uIcc 0 t, φ τ = a τ ^ 2 := by
    intro τ hτ
    simp only [φ, E, haA τ hτ]
    rw [show -(2 * lam) * τ = -lam * τ + -lam * τ by ring, Real.exp_add]
    ring
  have hAcont : ContinuousOn A (uIcc 0 t) := hAac.continuousOn
  have hacont : ContinuousOn a (uIcc 0 t) := by
    have : ContinuousOn (fun τ => Real.exp (-lam * τ) * A τ) (uIcc 0 t) :=
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul hAcont
    exact this.congr fun τ hτ => haA τ hτ
  have hderiv : ∀ᵐ s, s ∈ uIoc 0 t →
      deriv φ s = -(2 * lam) * a s ^ 2 + 2 * (a s * g s) := by
    filter_upwards [heint.ae_hasDerivAt_integral] with s hs hsmem
    have hsI : s ∈ uIcc 0 t := uIoc_subset_uIcc hsmem
    have hAd : HasDerivAt A (e s) s := by
      have := hs hsI 0 Set.left_mem_uIcc
      simpa [A] using this.const_add a0
    have hφd : HasDerivAt φ (-(2 * lam) * E s * (A s * A s) +
        E s * (e s * A s + A s * e s)) s :=
      (hEdiff s).mul (hAd.mul hAd)
    rw [hφd.deriv, haA s hsI]
    simp only [E, e]
    rw [show -(2 * lam) * s = -lam * s + -lam * s by ring, Real.exp_add]
    have hexp : Real.exp (-lam * s) * Real.exp (lam * s) = 1 := by
      rw [← Real.exp_add]; simp
    linear_combination (2 * Real.exp (-lam * s) * A s * g s) * hexp
  have hFTC := hφac.integral_deriv_eq_sub
  have hsq_int : IntervalIntegrable (fun s => a s ^ 2) volume 0 t :=
    (hacont.pow 2).intervalIntegrable
  have hag_int : IntervalIntegrable (fun s => a s * g s) volume 0 t :=
    hg.continuousOn_mul hacont
  rw [intervalIntegral.integral_congr_ae hderiv, intervalIntegral.integral_add
      (hsq_int.const_mul _) (hag_int.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    hφa t Set.right_mem_uIcc, hφa 0 Set.left_mem_uIcc] at hFTC
  have ha0 : a 0 = a0 := by simp [ha 0 Set.left_mem_uIcc]
  rw [ha0] at hFTC
  linear_combination -hFTC

/-- A real damped Duhamel formula with integrable source is continuous on the
time interval. -/
theorem damped_duhamel_continuousOn (lam a0 : ℝ) (g a : ℝ → ℝ) {t : ℝ}
    (hg : IntervalIntegrable g volume 0 t)
    (ha : ∀ τ ∈ uIcc 0 t, a τ = Real.exp (-lam * τ) * a0 +
      ∫ s in (0 : ℝ)..τ, Real.exp (-lam * (τ - s)) * g s) :
    ContinuousOn a (uIcc 0 t) := by
  let e : ℝ → ℝ := fun s => Real.exp (lam * s) * g s
  have heint : IntervalIntegrable e volume 0 t :=
    hg.continuousOn_mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  let A : ℝ → ℝ := fun τ => a0 + ∫ s in (0 : ℝ)..τ, e s
  have hAcont : ContinuousOn A (uIcc 0 t) := by
    have h1 : AbsolutelyContinuousOnInterval (fun _ : ℝ => a0) 0 t :=
      (contDiffOn_const (c := a0)).absolutelyContinuousOnInterval
    exact (h1.add (heint.absolutelyContinuousOnInterval_intervalIntegral
      (c := 0) Set.left_mem_uIcc)).continuousOn
  have hform : ContinuousOn (fun τ => Real.exp (-lam * τ) * A τ) (uIcc 0 t) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul hAcont
  refine hform.congr fun τ hτ => ?_
  rw [ha τ hτ]
  simp only [A, mul_add]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [e]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The real and imaginary parts of the coordinates of a complex three-vector,
as real continuous linear functionals. -/
@[expose]
def complexVec3RealCoord (k : Fin 3 × Bool) : ComplexVec3 →L[ℝ] ℝ :=
  (if k.2 then Complex.reCLM else Complex.imCLM).comp
    ((PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin 3 => ℂ) k.1).restrictScalars ℝ)

theorem complexVec3RealCoord_true (i : Fin 3) (x : ComplexVec3) :
    complexVec3RealCoord (i, true) x = (x.ofLp i).re := by
  simp [complexVec3RealCoord]

theorem complexVec3RealCoord_false (i : Fin 3) (x : ComplexVec3) :
    complexVec3RealCoord (i, false) x = (x.ofLp i).im := by
  simp [complexVec3RealCoord]

theorem complexVec3_norm_sq_eq_sum_realCoord (x : ComplexVec3) :
    ‖x‖ ^ 2 = ∑ k : Fin 3 × Bool, complexVec3RealCoord k x ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_bool, complexVec3RealCoord_true, complexVec3RealCoord_false,
    Complex.sq_norm, Complex.normSq_apply]
  ring

theorem complexVec3_inner_re_eq_sum_realCoord (x y : ComplexVec3) :
    (inner ℂ x y).re =
      ∑ k : Fin 3 × Bool, complexVec3RealCoord k x * complexVec3RealCoord k y := by
  rw [PiLp.inner_apply, Complex.re_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_bool, complexVec3RealCoord_true, complexVec3RealCoord_false,
    complexVec3RealCoord_true, complexVec3RealCoord_false]
  simp only [RCLike.inner_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The energy identity for a damped Duhamel formula with values in complex
three-vectors: `‖y(t)‖² + 2λ ∫₀ᵗ ‖y‖² = ‖y₀‖² + 2 ∫₀ᵗ Re ⟨y, g⟩`. -/
theorem damped_duhamel_complexVec3_identity (lam : ℝ) (y0 : ComplexVec3)
    (g y : ℝ → ComplexVec3) {t : ℝ} (hg : IntervalIntegrable g volume 0 t)
    (hy : ∀ τ ∈ uIcc 0 t, y τ = (Real.exp (-lam * τ) : ℂ) • y0 +
      ∫ s in (0 : ℝ)..τ, (Real.exp (-lam * (τ - s)) : ℂ) • g s) :
    ‖y t‖ ^ 2 + 2 * lam * ∫ s in (0 : ℝ)..t, ‖y s‖ ^ 2 =
      ‖y0‖ ^ 2 + 2 * ∫ s in (0 : ℝ)..t, (inner ℂ (y s) (g s)).re := by
  let L := complexVec3RealCoord
  have hgk : ∀ k, IntervalIntegrable (fun s => L k (g s)) volume 0 t := fun k =>
    ⟨(L k).integrable_comp hg.1, (L k).integrable_comp hg.2⟩
  have hsmul : ∀ (k : Fin 3 × Bool) (c : ℝ) (x : ComplexVec3),
      L k ((c : ℂ) • x) = c * L k x := by
    intro k c x
    rcases k with ⟨i, b⟩
    cases b
    · simp only [L, complexVec3RealCoord_false, PiLp.smul_apply, smul_eq_mul,
        Complex.im_ofReal_mul]
    · simp only [L, complexVec3RealCoord_true, PiLp.smul_apply, smul_eq_mul,
        Complex.re_ofReal_mul]
  have hcomp : ∀ k, ∀ τ ∈ uIcc 0 t, L k (y τ) = Real.exp (-lam * τ) * L k y0 +
      ∫ s in (0 : ℝ)..τ, Real.exp (-lam * (τ - s)) * L k (g s) := by
    intro k τ hτ
    have hsub : uIcc 0 τ ⊆ uIcc 0 t := Set.uIcc_subset_uIcc Set.left_mem_uIcc hτ
    have hint : IntervalIntegrable
        (fun s => (Real.exp (-lam * (τ - s)) : ℂ) • g s) volume 0 τ := by
      refine (hg.mono_set hsub).continuousOn_smul ?_
      exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_const.mul (continuous_const.sub continuous_id)))).continuousOn
    rw [hy τ hτ, map_add, hsmul, ← (L k).intervalIntegral_comp_comm hint]
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    exact hsmul k _ _
  have hid : ∀ k, (L k (y t)) ^ 2 + 2 * lam * ∫ s in (0 : ℝ)..t, (L k (y s)) ^ 2 =
      (L k y0) ^ 2 + 2 * ∫ s in (0 : ℝ)..t, L k (y s) * L k (g s) := fun k =>
    damped_duhamel_sq_identity lam (L k y0) (fun s => L k (g s)) (fun s => L k (y s))
      (hgk k) (hcomp k)
  have hcont : ∀ k, ContinuousOn (fun s => L k (y s)) (uIcc 0 t) := fun k =>
    damped_duhamel_continuousOn lam (L k y0) (fun s => L k (g s)) (fun s => L k (y s))
      (hgk k) (hcomp k)
  have hsqint : ∀ k, IntervalIntegrable (fun s => (L k (y s)) ^ 2) volume 0 t := fun k =>
    ((hcont k).pow 2).intervalIntegrable
  have hprodint : ∀ k, IntervalIntegrable (fun s => L k (y s) * L k (g s)) volume 0 t :=
    fun k => (hgk k).continuousOn_mul (hcont k)
  have hnorm : ∀ s, ‖y s‖ ^ 2 = ∑ k, (L k (y s)) ^ 2 := fun s =>
    complexVec3_norm_sq_eq_sum_realCoord (y s)
  have hinner : ∀ s, (inner ℂ (y s) (g s)).re = ∑ k, L k (y s) * L k (g s) := fun s =>
    complexVec3_inner_re_eq_sum_realCoord (y s) (g s)
  simp_rw [hnorm, hinner]
  rw [complexVec3_norm_sq_eq_sum_realCoord y0]
  rw [intervalIntegral.integral_finsetSum fun k _ => hsqint k,
    intervalIntegral.integral_finsetSum fun k _ => hprodint k, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => hid k

end CKN.Leray

end
