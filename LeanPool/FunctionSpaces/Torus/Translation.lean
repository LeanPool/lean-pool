/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Torus.Coefficients
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Translations on the torus and their Fourier coefficients

The translate of `f ∈ L_2(𝕋^d)` by `h ∈ 𝕋^d` is `(τ_h f)(x) = f(x + h)` (`Torus.translate`),
defined through Mathlib's `MeasureTheory.Lp.compMeasurePreserving` and the translation
invariance of the Haar measure.  Its Fourier coefficients are

`(τ_h f)^(k) = e_k(h) f̂(k)`   (`Torus.mFourierCoeff_translate`),

so by Parseval

`‖τ_h f - f‖_2² = ∑_k |e_k(h) - 1|² |f̂(k)|²`   (`Torus.enorm_translate_sub_sq`).

The multiplier is controlled by `|e_k(h) - 1| ≤ 2π · d · deg k · ‖h‖`
(`Torus.norm_mFourier_sub_one_le`), from `|e^(iθ) - 1| ≤ |θ|` in each coordinate.  These are the
facts behind the moduli of smoothness of `FunctionSpaces.Torus.Modulus`.
-/

@[expose] public section

open MeasureTheory UnitAddTorus
open scoped ENNReal TorusHaar lp Real

namespace Torus

variable {d : Type*} [Fintype d]

/-- `|e^(2πinx) - 1| ≤ 2π |n| ‖x‖` on the circle. -/
theorem norm_fourier_sub_one_le (n : ℤ) (x : UnitAddCircle) :
    ‖fourier n x - 1‖ ≤ 2 * π * |(n : ℝ)| * ‖x‖ := by
  induction x using QuotientAddGroup.induction_on with
  | H y =>
  set θ : ℝ := 2 * π * n * (y - round y)
  have hfy : fourier n (y : UnitAddCircle) = Complex.exp (Complex.I * θ) := by
    rw [fourier_coe_apply]
    have h1 : 2 * π * Complex.I * n * y / (1 : ℝ) =
        Complex.I * θ + ((n * round y : ℤ) : ℂ) * (2 * π * Complex.I) := by
      simp only [θ]; push_cast; ring
    rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hfy]
  calc ‖Complex.exp (Complex.I * θ) - 1‖ ≤ ‖θ‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * π * |(n : ℝ)| * ‖((y : ℝ) : UnitAddCircle)‖ := by
        rw [UnitAddCircle.norm_eq, Real.norm_eq_abs]
        simp only [θ, abs_mul, abs_of_pos Real.pi_pos, abs_two]

/-- For complex numbers of modulus `1`, `|∏ aᵢ - 1| ≤ ∑ |aᵢ - 1|`. -/
theorem norm_prod_sub_one_le {ι : Type*} (s : Finset ι) (a : ι → ℂ) (ha : ∀ i, ‖a i‖ = 1) :
    ‖∏ i ∈ s, a i - 1‖ ≤ ∑ i ∈ s, ‖a i - 1‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    have hP : ‖∏ j ∈ s, a j‖ = 1 := by rw [norm_prod]; exact Finset.prod_eq_one fun j _ => ha j
    calc ‖a i * ∏ j ∈ s, a j - 1‖ = ‖(a i - 1) * ∏ j ∈ s, a j + (∏ j ∈ s, a j - 1)‖ := by
          congr 1; ring
      _ ≤ ‖a i - 1‖ * ‖∏ j ∈ s, a j‖ + ‖∏ j ∈ s, a j - 1‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ ‖a i - 1‖ + ∑ j ∈ s, ‖a j - 1‖ := by rw [hP, mul_one]; gcongr

/-- **The Fourier multiplier of a translation**: `|e_k(h) - 1| ≤ 2π · d · deg k · ‖h‖`. -/
theorem norm_mFourier_sub_one_le (k : d → ℤ) (h : UnitAddTorus d) :
    ‖mFourier k h - 1‖ ≤ 2 * π * Fintype.card d * deg k * ‖h‖ := by
  have h1 : ‖mFourier k h - 1‖ ≤ ∑ i, ‖fourier (k i) (h i) - 1‖ :=
    norm_prod_sub_one_le Finset.univ _ fun i => by simp [fourier_apply, Circle.norm_coe]
  refine h1.trans ?_
  calc ∑ i, ‖fourier (k i) (h i) - 1‖ ≤ ∑ _i : d, 2 * π * (deg k : ℝ) * ‖h‖ := by
        refine Finset.sum_le_sum fun i _ => (norm_fourier_sub_one_le (k i) (h i)).trans ?_
        gcongr
        · rw [← Int.cast_abs, ← Int.natCast_natAbs]; exact_mod_cast natAbs_le_deg k i
        · exact norm_le_pi_norm h i
    _ = 2 * π * Fintype.card d * deg k * ‖h‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- A trigonometric monomial is a character: `e_k(x + h) = e_k(x) e_k(h)`. -/
theorem mFourier_add_apply (k : d → ℤ) (x h : UnitAddTorus d) :
    mFourier k (x + h) = mFourier k x * mFourier k h := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, smul_add,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

/-- `e_k(0) = 1`. -/
@[simp]
theorem mFourier_apply_zero (k : d → ℤ) : mFourier k (0 : UnitAddTorus d) = 1 := by
  simp [mFourier]

/-- `e_{-k}(-h) = e_k(h)`. -/
theorem mFourier_neg_neg (k : d → ℤ) (h : UnitAddTorus d) : mFourier (-k) (-h) = mFourier k h := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_apply, neg_smul_neg]

/-- The **translate** `(τ_h f)(x) = f(x + h)` on `L_2(𝕋^d)`. -/
noncomputable def translate (h : UnitAddTorus d) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus d)) →+ Lp ℂ 2 (volume : Measure (UnitAddTorus d)) :=
  Lp.compMeasurePreserving (· + h) (measurePreserving_add_right volume h)

/-- `τ_h f` is a.e. the function `x ↦ f(x + h)`. -/
theorem coeFn_translate (h : UnitAddTorus d) (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    translate h f =ᵐ[volume] fun x => f (x + h) :=
  Lp.coeFn_compMeasurePreserving f _

/-- **The Fourier coefficients of a translate**: `(τ_h f)^(k) = e_k(h) f̂(k)`. -/
theorem mFourierCoeff_translate (h : UnitAddTorus d)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (k : d → ℤ) :
    mFourierCoeff (translate h f) k = mFourier k h * mFourierCoeff f k := by
  simp only [mFourierCoeff]
  rw [integral_congr_ae ((coeFn_translate h f).mono fun x hx => by
    simp only [smul_eq_mul]; rw [hx])]
  have hsub : ∀ x : UnitAddTorus d, mFourier (-k) x = mFourier (-k) (x + h) * mFourier k h := by
    intro x
    rw [mFourier_add_apply, mul_assoc, ← mFourier_neg_neg k h, ← mFourier_add_apply,
      add_neg_cancel, mFourier_apply_zero, mul_one]
  have hfun : (fun x => mFourier (-k) x * f (x + h)) =
      fun x => mFourier (-k) (x + h) * mFourier k h * f (x + h) := funext fun x => by rw [hsub x]
  rw [hfun]
  have := integral_add_right_eq_self (μ := (volume : Measure (UnitAddTorus d)))
    (fun y => mFourier (-k) y * mFourier k h * f y) h
  calc ∫ x, mFourier (-k) (x + h) * mFourier k h * f (x + h)
      = ∫ y, mFourier (-k) y * mFourier k h * f y := this
    _ = mFourier k h * ∫ y, mFourier (-k) y • f y := by
        rw [← integral_const_mul]; congr 1; funext y; simp only [smul_eq_mul]; ring

/-- The coefficients of `τ_h f` in the Fourier basis are `e_k(h) f̂(k)`. -/
theorem repr_translate (h : UnitAddTorus d) (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (k : d → ℤ) :
    mFourierBasis.repr (translate h f) k = mFourier k h * mFourierBasis.repr f k := by
  rw [mFourierBasis_repr, mFourierBasis_repr, mFourierCoeff_translate]

/-- **Parseval for differences**: `‖τ_h f - f‖_2² = ∑_k |e_k(h) - 1|² |f̂(k)|²`. -/
theorem enorm_translate_sub_sq (h : UnitAddTorus d)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ‖translate h f - f‖ₑ ^ 2 = ∑' k, ‖mFourier k h - 1‖ₑ ^ 2 * ‖mFourierCoeff f k‖ₑ ^ 2 := by
  rw [← mFourierBasis.repr.eNorm_map, lp.enorm_sq_eq_tsum]
  congr 1; funext k
  rw [map_sub, lp.coeFn_sub, Pi.sub_apply, repr_translate, mFourierBasis_repr, ← sub_one_mul,
    eNorm_mul, mul_pow]

end Torus
