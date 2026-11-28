/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Differences.Differences
public import LeanPool.FunctionSpaces.Torus.Translation
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The modulus of smoothness in `L_2(𝕋^d)` and Jackson's theorem

The **modulus of smoothness** (of first order) of `f ∈ L_2(𝕋^d)` is

`ω(f, t)_2 = sup_{‖h‖ ≤ t} ‖f(· + h) - f‖_2`   (`Torus.modulus`, `Torus.modulus_eq_iSup`),

the modulus of order `1` in `L_2` of `Rd.modulus` for the Haar measure on `𝕋^d`, with the sup
norm `‖h‖ = max_i ‖h_i‖` on `𝕋^d`.  For every order `r` and `1 ≤ p` the modulus
`ω_r(f, t)_p` of `Rd.modulus` on the torus satisfies `ω_r(f, c t)_p ≤ (1 + c)^r ω_r(f, t)_p`
(`Torus.modulus_mul_le`).  This file proves
**Jackson's theorem**

`E_n(f)_2² ≤ d · ω(f, 1/n)_2²`   (`Torus.approxError_sq_le_card_mul_modulus_sq`),

the error of best approximation by trigonometric polynomials of degree `< n` controlled by the
modulus.  The proof averages over translations in the coordinate directions: by Parseval,
`∫_0^t ‖f(· + u eᵢ) - f‖² du = ∑_k |f̂(k)|² ∫_0^t |e^(2πi kᵢ u) - 1|² du`, and the last integral,
`2t - sin(2π kᵢ t)/(π kᵢ)`, is at least `t` as soon as `|kᵢ| t ≥ 1`
(`le_integral_norm_fourier_sub_one_sq`).  Choosing for each frequency the coordinate of
largest modulus gives the theorem.
-/

@[expose] public section

open MeasureTheory UnitAddTorus Set
open scoped ENNReal TorusHaar lp Real

namespace Torus

variable {d : Type*} [Fintype d]

/-- The **modulus of smoothness** `ω(f, t)_2 = sup_{‖h‖ ≤ t} ‖f(· + h) - f‖_2`, the modulus of
order `1` in `L_2` of `Rd.modulus` for the Haar measure on `𝕋^d`. -/
noncomputable def modulus (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (t : ℝ) : ℝ≥0∞ :=
  Rd.modulus volume 1 2 (f : UnitAddTorus d → ℂ) t

/-- `‖τ_h f - f‖_2 = ‖Δ_h f‖_2` for the representative of `f`. -/
theorem enorm_translate_sub_eq (h : UnitAddTorus d)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ‖translate h f - f‖ₑ = eLpNorm ((fwdDiff h)^[1] (f : UnitAddTorus d → ℂ)) 2 volume := by
  rw [Lp.eNorm_def, Function.iterate_one]
  refine eLpNorm_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (translate h f) f, coeFn_translate h f] with x h1 h2
  rw [h1, Pi.sub_apply, h2]
  rfl

/-- **The modulus through translations**: `ω(f, t)_2 = sup_{‖h‖ ≤ t} ‖τ_h f - f‖_2`. -/
theorem modulus_eq_iSup (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (t : ℝ) :
    modulus f t = ⨆ (h : UnitAddTorus d) (_ : ‖h‖ ≤ t), ‖translate h f - f‖ₑ := by
  simp only [enorm_translate_sub_eq]
  rfl

variable {f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))}

/-- `‖τ_h f - f‖_2 ≤ ω(f, t)_2` for `‖h‖ ≤ t`. -/
theorem enorm_translate_sub_le_modulus {t : ℝ} {h : UnitAddTorus d} (hh : ‖h‖ ≤ t) :
    ‖translate h f - f‖ₑ ≤ modulus f t := by
  rw [enorm_translate_sub_eq]
  exact Rd.eLpNorm_higherDiff_le_modulus hh

/-- The modulus of smoothness increases in `t`. -/
theorem modulus_mono (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) : Monotone (modulus f) :=
  Rd.modulus_mono 1 2 _

/-- The norm on the circle is at most the absolute value of a representative. -/
theorem norm_coe_le_abs (u : ℝ) : ‖(u : UnitAddCircle)‖ ≤ |u| := by
  simpa using QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (1 : ℝ)) (m := u)

/-- Translation is an isometry of `L_2(𝕋^d)`. -/
theorem enorm_translate (h : UnitAddTorus d) (g : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ‖translate h g‖ₑ = ‖g‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, translate, Lp.norm_compMeasurePreserving]

/-- `τ_0 = id`. -/
theorem translate_zero (g : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) : translate 0 g = g := by
  ext1
  filter_upwards [coeFn_translate 0 g] with x hx
  rw [hx, add_zero]

/-- `τ_{a+b} = τ_a τ_b`. -/
theorem translate_add (a b : UnitAddTorus d) (g : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    translate (a + b) g = translate a (translate b g) := by
  ext1
  filter_upwards [coeFn_translate (a + b) g, coeFn_translate a (translate b g),
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae_eq_comp
      (coeFn_translate b g)] with x h1 h2 h3
  simp only [Function.comp_apply] at h3
  rw [h1, h2, h3, add_assoc]

/-- `‖τ_{n h} f - f‖_2 ≤ n ‖τ_h f - f‖_2`, by telescoping. -/
theorem enorm_translate_nsmul_sub_le (n : ℕ) (h : UnitAddTorus d)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ‖translate (n • h) f - f‖ₑ ≤ n * ‖translate h f - f‖ₑ := by
  induction n with
  | zero => simp [translate_zero]
  | succ n ih =>
    rw [succ_nsmul', translate_add, ← sub_add_sub_cancel _ (translate h f), ← map_sub,
      Nat.cast_succ, add_mul, one_mul]
    exact (eNorm_add_le _ _).trans (add_le_add_left ((enorm_translate _ _).trans_le ih) _)

/-- Every point of the circle has a representative `x ∈ ℝ` with `|x| = ‖u‖`. -/
theorem exists_coe_eq_abs_eq_norm (u : UnitAddCircle) :
    ∃ x : ℝ, (x : UnitAddCircle) = u ∧ |x| = ‖u‖ := by
  induction u using QuotientAddGroup.induction_on with
  | H y =>
  refine ⟨y - round y, ?_, UnitAddCircle.norm_eq.symm⟩
  rw [AddCircle.coe_sub,
    (AddCircle.coe_eq_zero_iff 1 (x := ((round y : ℤ) : ℝ))).2 ⟨round y, by simp⟩, sub_zero]

/-- **Scaling the modulus of order `r`**: `ω_r(f, m t)_p ≤ m^r ω_r(f, t)_p` on the torus for
`m ≥ 1` and `1 ≤ p`, since every `h` with `‖h‖ ≤ m t` is `m h'` with `‖h'‖ ≤ t`
(`Torus.exists_coe_eq_abs_eq_norm`, `Rd.modulus_nat_mul_le_of_forall_exists_nsmul`). -/
theorem modulus_nat_mul_le {f : UnitAddTorus d → ℂ} (hf : AEStronglyMeasurable f volume)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (r : ℕ) {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : 0 ≤ t) :
    Rd.modulus volume r p f (m * t) ≤ (m : ℝ≥0∞) ^ r * Rd.modulus volume r p f t := by
  refine Rd.modulus_nat_mul_le_of_forall_exists_nsmul hf hp r fun h hh => ?_
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  choose x hx1 hx2 using fun i => exists_coe_eq_abs_eq_norm (h i)
  refine ⟨fun i => ((x i / m : ℝ) : UnitAddCircle), (pi_norm_le_iff_of_nonneg ht).2 fun i =>
    (norm_coe_le_abs _).trans ?_, funext fun i => ?_⟩
  · rw [abs_div, Nat.abs_cast, div_le_iff₀ hm', hx2, mul_comm]
    exact (norm_le_pi_norm h i).trans hh
  · rw [Pi.smul_apply, ← hx1 i, ← AddCircle.coe_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ hm'.ne']

/-- **The modulus of order `r` grows polynomially**: `ω_r(f, c t)_p ≤ (1 + c)^r ω_r(f, t)_p` on the
torus for `c, t ≥ 0` (`Torus.modulus_nat_mul_le`, `Rd.modulus_mul_le_of_nat_mul_le`). -/
theorem modulus_mul_le {f : UnitAddTorus d → ℂ} (hf : AEStronglyMeasurable f volume)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (r : ℕ) {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    Rd.modulus volume r p f (c * t) ≤ ENNReal.ofReal (1 + c) ^ r * Rd.modulus volume r p f t :=
  Rd.modulus_mul_le_of_nat_mul_le hc ht fun _ hm => modulus_nat_mul_le hf hp r hm ht

/-- `|e^(ix) - 1|² = 2 - 2 cos x`. -/
theorem norm_exp_I_mul_sub_one_sq (x : ℝ) :
    ‖Complex.exp (Complex.I * x) - 1‖ ^ 2 = 2 - 2 * Real.cos x := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    mul_pow, sq_abs]
  have h1 := Real.cos_two_mul (x / 2)
  rw [mul_div_cancel₀ x two_ne_zero] at h1
  have h2 := Real.sin_sq_add_cos_sq (x / 2)
  norm_num
  nlinarith

/-- The character `e_a` at the point `u ∈ ℝ` of the circle is `exp(2πi a u)`. -/
theorem fourier_coe_eq_exp (a : ℤ) (u : ℝ) :
    fourier a (u : UnitAddCircle) = Complex.exp (Complex.I * ((2 * π * a * u : ℝ) : ℂ)) := by
  rw [fourier_coe_apply]; congr 1; push_cast; ring

/-- `|e_a(u) - 1|² = 2 - 2 cos(2π a u)`. -/
theorem norm_fourier_sub_one_sq (a : ℤ) (u : ℝ) :
    ‖fourier a (u : UnitAddCircle) - 1‖ ^ 2 = 2 - 2 * Real.cos (2 * π * a * u) := by
  rw [fourier_coe_eq_exp, norm_exp_I_mul_sub_one_sq]

/-- `∫_0^t |e^(2πiau) - 1|² du = 2t - sin(2πat)/(πa)` for `a ≠ 0`. -/
theorem integral_norm_fourier_sub_one_sq (a : ℤ) (ha : a ≠ 0) (t : ℝ) :
    ∫ u in (0 : ℝ)..t, ‖fourier a (u : UnitAddCircle) - 1‖ ^ 2 =
      2 * t - Real.sin (2 * π * a * t) / (π * a) := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hc : 2 * π * (a : ℝ) ≠ 0 := by positivity
  simp_rw [norm_fourier_sub_one_sq]
  have hcos : Continuous fun u : ℝ => 2 * Real.cos (2 * π * a * u) := by fun_prop
  rw [intervalIntegral.integral_sub intervalIntegrable_const (hcos.intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos]
  simp only [sub_zero, smul_eq_mul, mul_zero, Real.sin_zero]
  field_simp

/-- **The averaged multiplier is large at high frequencies**: for `|a| t ≥ 1`,
`t ≤ ∫_0^t |e^(2πiau) - 1|² du`. -/
theorem le_integral_norm_fourier_sub_one_sq (a : ℤ) {t : ℝ} (hat : 1 ≤ |(a : ℝ)| * t) :
    t ≤ ∫ u in (0 : ℝ)..t, ‖fourier a (u : UnitAddCircle) - 1‖ ^ 2 := by
  have ha : a ≠ 0 := by rintro rfl; simp at hat; linarith
  have ha' : 0 < |(a : ℝ)| := abs_pos.2 (by exact_mod_cast ha)
  rw [integral_norm_fourier_sub_one_sq a ha t]
  have hsin : |Real.sin (2 * π * a * t) / (π * a)| ≤ t := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, div_le_iff₀ (by positivity)]
    calc |Real.sin (2 * π * a * t)| ≤ 1 := Real.abs_sin_le_one _
      _ ≤ |(a : ℝ)| * t := hat
      _ ≤ t * (π * |(a : ℝ)|) := by nlinarith [Real.one_le_pi_div_two]
  have := le_abs_self (Real.sin (2 * π * a * t) / (π * a))
  linarith

/-- The averaged multiplier in `ℝ≥0∞`, over `(0, t]`. -/
theorem ofReal_le_lintegral_enorm_fourier_sub_one_sq (a : ℤ) {t : ℝ} (ht : 0 ≤ t)
    (hat : 1 ≤ |(a : ℝ)| * t) :
    ENNReal.ofReal t ≤ ∫⁻ u in Ioc 0 t, ‖fourier a (u : UnitAddCircle) - 1‖ₑ ^ 2 := by
  have hcont : Continuous fun u : ℝ => ‖fourier a (u : UnitAddCircle) - 1‖ ^ 2 :=
    (((fourier a).continuous.comp continuous_quotient_mk').sub continuous_const).norm.pow 2
  have hint : IntegrableOn (fun u : ℝ => ‖fourier a (u : UnitAddCircle) - 1‖ ^ 2) (Ioc 0 t) :=
    (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have heq : (fun u : ℝ => ‖fourier a (u : UnitAddCircle) - 1‖ₑ ^ 2) =
      fun u : ℝ => ENNReal.ofReal (‖fourier a (u : UnitAddCircle) - 1‖ ^ 2) := by
    funext u; rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [heq, ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ => by
    positivity),
    ← intervalIntegral.integral_of_le ht]
  exact ENNReal.ofReal_le_ofReal (le_integral_norm_fourier_sub_one_sq a hat)

/-- On a coordinate axis, `e_k(u eᵢ) = e^(2πi kᵢ u)`. -/
theorem mFourier_single [DecidableEq d] (k : d → ℤ) (i : d) (u : UnitAddCircle) :
    mFourier k (Pi.single i u) = fourier (k i) u := by
  simp only [mFourier, ContinuousMap.coe_mk]
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
  simp

/-- The error of best approximation is at most the tail of the Fourier series:
`E_n(f)_2² ≤ ∑_{deg k ≥ n} |f̂(k)|²`. -/
theorem approxError_sq_le_tsum (n : ℕ) (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ((trigScheme d).toLp volume 2).approxError f n ^ 2 ≤
      ∑' k, if n ≤ deg k then ‖mFourierCoeff f k‖ₑ ^ 2 else 0 := by
  rw [toLp_trigScheme_eq]
  have h1 := (fourierScheme d).projectionScheme.approxError_le_enorm_sub n f
  refine (pow_le_pow_left₀ bot_le h1 2).trans (le_of_eq ?_)
  rw [SpectralScheme.projectionScheme_P, ← mFourierBasis.repr.eNorm_map,
    lp.enorm_sq_eq_tsum]
  congr 1; funext k
  change ‖(fourierScheme d).basis.repr (f - (fourierScheme d).truncate n f) k‖ₑ ^ 2 = _
  rw [SpectralScheme.repr_sub_truncate]
  change (‖if deg k < n then 0 else mFourierBasis.repr f k‖ₑ) ^ 2 = _
  rw [mFourierBasis_repr]
  split_ifs with h1 h2 h2
  · omega
  · simp
  · rfl
  · omega

/-- **Jackson's theorem in `L_2(𝕋^d)`**: `E_n(f)_2² ≤ d · ω(f, 1/n)_2²` for `n ≥ 1`. -/
theorem approxError_sq_le_card_mul_modulus_sq {n : ℕ} (hn : 1 ≤ n)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ((trigScheme d).toLp volume 2).approxError f n ^ 2 ≤
      (Fintype.card d : ℝ≥0∞) * modulus f (1 / n) ^ 2 := by
  classical
  set t : ℝ := 1 / n
  have ht : 0 < t := by positivity
  set ω := modulus f t
  set c : (d → ℤ) → ℝ≥0∞ := fun k => ‖mFourierCoeff f k‖ₑ ^ 2
  set I : d → (d → ℤ) → ℝ≥0∞ := fun i k =>
    ∫⁻ u in Ioc 0 t, ‖fourier (k i) (u : UnitAddCircle) - 1‖ₑ ^ 2
  -- averaging in one coordinate direction
  have hdir : ∀ i, ∑' k, c k * I i k ≤ ω ^ 2 * ENNReal.ofReal t := by
    intro i
    have hmeas : ∀ k, AEMeasurable
        (fun u : ℝ => ‖fourier (k i) (u : UnitAddCircle) - 1‖ₑ ^ 2 * c k)
        (volume.restrict (Ioc 0 t)) := fun k =>
      (Measurable.mul_const ((((fourier (k i)).continuous.comp continuous_quotient_mk').sub
        continuous_const).measurable.eNorm.pow_const 2) _).aemeasurable
    calc ∑' k, c k * I i k
        = ∫⁻ u in Ioc 0 t, ∑' k, ‖fourier (k i) (u : UnitAddCircle) - 1‖ₑ ^ 2 * c k := by
          rw [lintegral_tsum hmeas]
          congr 1; funext k
          rw [lintegral_mul_const' _ _ (ENNReal.pow_ne_top eNorm_ne_top), mul_comm]
      _ = ∫⁻ u in Ioc 0 t, ‖translate (Pi.single i (u : UnitAddCircle)) f - f‖ₑ ^ 2 := by
          congr 1; funext u
          rw [enorm_translate_sub_sq]
          simp_rw [mFourier_single]
          rfl
      _ ≤ ∫⁻ _u in Ioc 0 t, ω ^ 2 := by
          refine setLIntegral_mono measurable_const fun u hu => ?_
          gcongr
          refine enorm_translate_sub_le_modulus ?_
          rw [Pi.norm_single]
          exact (norm_coe_le_abs u).trans (by rw [abs_of_pos hu.1]; exact hu.2)
      _ = ω ^ 2 * ENNReal.ofReal t := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
  -- each frequency of degree `≥ n` is seen by one coordinate
  have hfreq : ∀ k, (if n ≤ deg k then ENNReal.ofReal t * c k else 0) ≤ c k * ∑ i, I i k := by
    intro k
    split_ifs with hk
    · have hne : (Finset.univ : Finset d).Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty] at h
        have : deg k = 0 := by simp [deg, h]
        omega
      obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup _ hne fun i => (k i).natAbs
      have hat : 1 ≤ |((k i : ℤ) : ℝ)| * t := by
        rw [← Int.cast_abs, ← Int.natCast_natAbs]
        have : (n : ℝ) ≤ (k i).natAbs := by
          have := hk; rw [deg, hi] at this; exact_mod_cast this
        simp only [t]
        rw [mul_one_div, le_div_iff₀ (by positivity), one_mul]
        exact this
      calc ENNReal.ofReal t * c k = c k * ENNReal.ofReal t := mul_comm _ _
        _ ≤ c k * I i k := by gcongr; exact ofReal_le_lintegral_enorm_fourier_sub_one_sq _ ht.le hat
        _ ≤ c k * ∑ i, I i k := by
            gcongr; exact Finset.single_le_sum (f := fun j => I j k) (fun _ _ => bot_le)
              (Finset.mem_univ i)
    · exact bot_le
  have hsum : ENNReal.ofReal t * ∑' k, (if n ≤ deg k then c k else 0) ≤
      ENNReal.ofReal t * ((Fintype.card d : ℝ≥0∞) * ω ^ 2) := by
    calc ENNReal.ofReal t * ∑' k, (if n ≤ deg k then c k else 0)
        = ∑' k, (if n ≤ deg k then ENNReal.ofReal t * c k else 0) := by
          rw [← ENNReal.tsum_mul_left]; congr 1; funext k; split_ifs <;> simp
      _ ≤ ∑' k, c k * ∑ i, I i k := tsum_le_tsum hfreq
      _ = ∑ i, ∑' k, c k * I i k := by
          simp_rw [Finset.mul_sum]
          exact (Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable)
      _ ≤ ∑ _i : d, ω ^ 2 * ENNReal.ofReal t := Finset.sum_le_sum fun i _ => hdir i
      _ = ENNReal.ofReal t * ((Fintype.card d : ℝ≥0∞) * ω ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hcancel := (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 ht).ne'
    ENNReal.ofReal_ne_top).1 hsum
  exact (approxError_sq_le_tsum n f).trans hcancel

end Torus
