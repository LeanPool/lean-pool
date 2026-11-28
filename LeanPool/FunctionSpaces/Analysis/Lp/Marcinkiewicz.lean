/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Lp.WeakType
public import LeanPool.FunctionSpaces.Analysis.Lp.LintegralForm
public import LeanPool.FunctionSpaces.Analysis.Lp.MixedNorms
public import LeanPool.FunctionSpaces.Analysis.Lp.LayerCake

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Marcinkiewicz interpolation between weak type `(1,1)` and strong type `(2,2)`

For `1 < p < 2`, an operator that is subadditive almost everywhere, of weak type `(1,1)` and of
strong type `(2,2)` has strong type `(p,p)`. The constant for the integrals of `p`-th powers is
`MeasureTheory.marcinkiewiczConst p C₁ C₂ = p (2 C₁/(p - 1) + 4 C₂/(2 - p))`, where `C₁` is the
weak type constant and `C₂` the constant of `∫ (Tf)² ≤ C₂ ∫ f²`. The measure on the input space
is s-finite.

* **Chebyshev's inequality and level sets**: `μ{F > t} ≤ t^(-r) ∫ F^r`
  (`MeasureTheory.measure_lt_le_inv_rpow_mul_lintegral`, the lintegral form of the
  distribution bound `MeasureTheory.distribution_le_inv_rpow_mul_eLpNorm_rpow` of
  `FunctionSpaces.Analysis.Lp.WeakType`), its forms at half height
  (`MeasureTheory.measure_half_lt_le_lintegral_sq`,
  `MeasureTheory.measure_half_lt_le_add_setLIntegral_compl`) and the level sets of a function
  split into a part controlled in `L_2` and a part controlled in `L_1` off an exceptional set
  (`MeasureTheory.measure_lt_le_of_ae_le_add`), the bookkeeping of Calderón–Zygmund arguments,
  with `t < a + b ⇒ t/2 < a ∨ t/2 < b` (`ENNReal.half_lt_or_half_lt_of_lt_add`) and `L_2`
  membership from `∫ ‖f‖² < ∞` (`MeasureTheory.memLp_two_of_lintegral_enorm_sq_ne_top`).
* **The parts above and below a level** (`MeasureTheory.lintegral_indicator_lt_le`,
  `MeasureTheory.lintegral_indicator_compl_rpow_le`): `∫_{F > s} F ≤ s^(1-p) ∫ F^p` and
  `∫_{F ≤ s} F^r ≤ s^(r-p) ∫ F^p`.
* **Two Tonelli steps** on s-finite measure spaces
  (`MeasureTheory.lintegral_Ioi_lintegral_indicator_lt_mul_rpow`,
  `MeasureTheory.lintegral_Ioi_lintegral_indicator_compl_mul_rpow_le`).
* **The layer cake argument** (`MeasureTheory.lintegral_rpow_le_of_forall_le_add`): if at every
  level `τ > 0` a function `F` splits as `F ≤ F₁ + F₂` with
  `ν{F₁ > τ/2} ≤ C₁ (τ/2)⁻¹ ∫_{G > τ} G` and `∫ F₂² ≤ C₂ ∫_{G ≤ τ} G²`, then
  `∫ F^p ≤ marcinkiewiczConst p C₁ C₂ ∫ G^p`. It combines the level estimate
  (`MeasureTheory.measure_lt_mul_rpow_le_of_le_add`) with the layer cake formula and the two
  Tonelli steps, collected in `MeasureTheory.lintegral_rpow_le_of_measure_lt_mul_rpow_le`.
* **Operators on an abstract input type** (`MeasureTheory.lintegral_rpow_le_of_weak_one_strong_two`,
  in `L_p` norms `MeasureTheory.eLpNorm_le_of_weak_one_strong_two`): inputs `x : X` with a size
  `G x : α → [0, ∞]` and restrictions `res x S` to measurable sets, such as families of functions
  with their pointwise `ℓ_2` norms.
* **In the terms of the Carleson project**
  (`MeasureTheory.hasStrongType_of_hasWeakType_one_of_hasStrongType_two`): `HasWeakType T 1 1`,
  `HasStrongType T 2 2` and `AESubadditiveOn` with constant `A` give `HasStrongType T p p` with the
  constant `MeasureTheory.marcinkiewiczNormConst`. Since strong type `(2,2)` implies weak type
  `(2,2)`, the Carleson project's `exists_hasStrongType_real_interpolation` with
  `(p₀, q₀) = (1, 1)`, `(p₁, q₁) = (2, 2)` gives strong type `(p,p)` for `A ≥ 1` and positive
  finite constants. Here the layer cake argument gives it on s-finite measure spaces for every
  `A ≥ 0` and `C₁, C₂ ∈ [0, ∞]`, with the constant
  `(p (2 A C₁/(p - 1) + 4 A² C₂²/(2 - p)))^(1/p)`.

The layer cake formula and the integrals of powers over `(0, ∞)` come from
`FunctionSpaces.Analysis.Lp.LayerCake`.
-/

@[expose] public section

open Set
open scoped ENNReal NNReal

namespace ENNReal

/-- `a^r a^(p-r) ≤ a^p` in `[0, ∞]` for `0 < r` and `p < r`, with equality for `0 < a < ∞`; for
`a = ∞` the left side is `∞ · 0 = 0`. -/
theorem rpow_mul_rpow_sub_le (a : ℝ≥0∞) {p r : ℝ} (hr : 0 < r) (hpr : p < r) :
    a ^ r * a ^ (p - r) ≤ a ^ p := by
  rcases eq_or_ne a 0 with rfl | h0
  · rw [ENNReal.zero_rpow_of_pos hr, zero_mul]
    exact zero_le
  rcases eq_or_ne a ∞ with rfl | ht
  · rw [ENNReal.top_rpow_of_neg (by linarith : p - r < 0), mul_zero]
    exact zero_le
  rw [← ENNReal.rpow_add _ _ h0 ht]
  exact le_of_eq (by ring_nf)

/-- `(τ/2)⁻¹ τ^(p-1) = 2 τ^(p-2)` in `[0, ∞]` for `τ > 0`. -/
theorem inv_half_mul_ofReal_rpow {τ : ℝ} (hτ : 0 < τ) (p : ℝ) :
    (ENNReal.ofReal τ / 2)⁻¹ * ENNReal.ofReal (τ ^ (p - 1)) = 2 * ENNReal.ofReal (τ ^ (p - 2)) := by
  rw [ENNReal.inv_div (Or.inl ENNReal.ofNat_ne_top) (Or.inl two_ne_zero), div_eq_mul_inv,
    mul_assoc, show p - 1 = 1 + (p - 2) by ring, Real.rpow_add hτ, Real.rpow_one,
    ENNReal.ofReal_mul hτ.le, ← mul_assoc (ENNReal.ofReal τ)⁻¹,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hτ).ne' ENNReal.ofReal_ne_top, one_mul]

/-- `((τ/2)^r)⁻¹ τ^(p-1) = 2^r τ^(p-1-r)` in `[0, ∞]` for `τ > 0`. -/
theorem inv_half_rpow_mul_ofReal_rpow {τ : ℝ} (hτ : 0 < τ) (p r : ℝ) :
    ((ENNReal.ofReal τ / 2) ^ r)⁻¹ * ENNReal.ofReal (τ ^ (p - 1)) =
      2 ^ r * ENNReal.ofReal (τ ^ (p - 1 - r)) := by
  have h2 : ENNReal.ofReal τ / 2 = ENNReal.ofReal (τ / 2) := by
    rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]
  have hreal : ((τ / 2) ^ r)⁻¹ * τ ^ (p - 1) = 2 ^ r * τ ^ (p - 1 - r) := by
    rw [Real.div_rpow hτ.le zero_le_two, inv_div, Real.rpow_sub hτ (p - 1) r]
    have : 0 < τ ^ r := Real.rpow_pos_of_pos hτ r
    field_simp
  rw [h2, ENNReal.ofReal_rpow_of_pos (by positivity), ← ENNReal.ofReal_inv_of_pos (by positivity),
    ← ENNReal.ofReal_mul (by positivity), hreal, ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_rpow_of_pos two_pos, ENNReal.ofReal_ofNat]

/-- If `t < a + b` in `[0, ∞]`, then `t/2 < a` or `t/2 < b`: Mathlib's `lt_or_lt_of_add_lt_add`
applied to `t/2 + t/2 = t`. -/
theorem half_lt_or_half_lt_of_lt_add {t a b : ℝ≥0∞} (h : t < a + b) : t / 2 < a ∨ t / 2 < b :=
  lt_or_lt_of_add_lt_add (by rwa [ENNReal.add_halves])

end ENNReal

namespace MeasureTheory

variable {α α' : Type*} [MeasurableSpace α] [MeasurableSpace α'] {μ : Measure α}
  {ν : Measure α'}

/-! ### Chebyshev's inequality and level sets -/

section Chebyshev

variable {t : ℝ≥0∞}

/-- **Chebyshev's inequality with a power**: for an almost everywhere measurable
`F : α → [0, ∞]`, `r > 0` and `0 < t < ∞`, `μ {F > t} ≤ t^(-r) ∫ F^r`, from Mathlib's
`mul_meas_ge_le_lintegral₀` for `F^r`. This is the lintegral form of
`MeasureTheory.distribution_le_inv_rpow_mul_eLpNorm_rpow`. The bound holds for `t ∈ {0, ∞}` as
well (at `t = ∞` the level set is empty, at `t = 0` the right side is `∞` unless `F = 0` almost
everywhere); the callers use `0 < t < ∞`. -/
theorem measure_lt_le_inv_rpow_mul_lintegral {F : α → ℝ≥0∞} (hF : AEMeasurable F μ) {r : ℝ}
    (hr : 0 < r) (ht0 : t ≠ 0) (ht : t ≠ ∞) :
    μ {x | t < F x} ≤ (t ^ r)⁻¹ * ∫⁻ x, F x ^ r ∂μ := by
  rw [← ENNReal.mul_le_iff_le_inv (ENNReal.rpow_pos (pos_iff_ne_zero.2 ht0) ht).ne'
    (ENNReal.rpow_ne_top_of_nonneg hr.le ht)]
  calc t ^ r * μ {x | t < F x} ≤ t ^ r * μ {x | t ^ r ≤ F x ^ r} :=
        mul_le_mul_right (measure_mono fun x hx => ENNReal.rpow_le_rpow (le_of_lt hx) hr.le) _
    _ ≤ ∫⁻ x, F x ^ r ∂μ := mul_meas_ge_le_lintegral₀ (hF.pow_const r) _

/-- **Chebyshev's inequality with squares at half height**: for an almost everywhere measurable
`a : α → [0, ∞]` and `0 < t < ∞`, `μ {a > t/2} ≤ 4 t⁻² ∫ a²`
(`MeasureTheory.measure_lt_le_inv_rpow_mul_lintegral` with `r = 2`). -/
theorem measure_half_lt_le_lintegral_sq {a : α → ℝ≥0∞} (ha : AEMeasurable a μ) (ht0 : 0 < t)
    (ht : t ≠ ∞) : μ {x | t / 2 < a x} ≤ 4 * (t ^ 2)⁻¹ * ∫⁻ x, a x ^ 2 ∂μ := by
  have h4 : (t / 2) ^ 2 = 4⁻¹ * t ^ 2 := by
    rw [ENNReal.div_eq_inv_mul, mul_pow, ← ENNReal.inv_pow]
    norm_num
  have h := measure_lt_le_inv_rpow_mul_lintegral ha two_pos (ENNReal.half_pos ht0.ne').ne'
    (ENNReal.div_ne_top ht two_ne_zero)
  simp_rw [ENNReal.rpow_two] at h
  rwa [h4, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), inv_inv] at h

/-- **Chebyshev's inequality off a set, at half height**: for an almost everywhere measurable
`b : α → [0, ∞]`, a measurable set `S` and `0 < t < ∞`,
`μ {b > t/2} ≤ μ(S) + 2 t⁻¹ ∫_{Sᶜ} b`. -/
theorem measure_half_lt_le_add_setLIntegral_compl {b : α → ℝ≥0∞} (hb : AEMeasurable b μ)
    {S : Set α} (hS : MeasurableSet S) (ht0 : 0 < t) (ht : t ≠ ∞) :
    μ {x | t / 2 < b x} ≤ μ S + 2 * t⁻¹ * ∫⁻ x in Sᶜ, b x ∂μ := by
  have hc : t / 2 ≠ 0 := (ENNReal.div_pos ht0.ne' (by norm_num)).ne'
  have hc' : t / 2 ≠ ∞ := ENNReal.div_ne_top ht two_ne_zero
  calc μ {x | t / 2 < b x} ≤ μ S + μ {x | t / 2 ≤ Sᶜ.indicator b x} := by
        refine (measure_mono fun x hx => ?_).trans (measure_union_le _ _)
        by_cases hxS : x ∈ S
        · exact Or.inl hxS
        · exact Or.inr (show t / 2 ≤ Sᶜ.indicator b x by
            rw [Set.indicator_of_mem (show x ∈ Sᶜ from hxS)]; exact le_of_lt hx)
    _ ≤ μ S + (∫⁻ x, Sᶜ.indicator b x ∂μ) / (t / 2) :=
        add_le_add le_rfl (meas_ge_le_lintegral_div (hb.indicator hS.compl) hc hc')
    _ = μ S + 2 * t⁻¹ * ∫⁻ x in Sᶜ, b x ∂μ := by
        rw [lintegral_indicator hS.compl, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
          ENNReal.mul_inv (Or.inr ht) (Or.inl (by norm_num)), inv_inv]

/-- A function with `∫ ‖f‖² < ∞` that is almost everywhere strongly measurable lies in `L_2`
(Mathlib's `eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top`). -/
theorem memLp_two_of_lintegral_enorm_sq_ne_top {E : Type*} [NormedAddCommGroup E] {f : α → E}
    (hf : AEStronglyMeasurable f μ) (h : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≠ ∞) : MemLp f 2 μ :=
  memLp_iff.2 ((eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
    hf).2 (by simpa [ENNReal.rpow_two] using h.lt_top))

/-- **The level sets of a split function**: let `u ≤ a + b` almost everywhere, with almost
everywhere measurable `a, b : α → [0, ∞]`, let `S` be measurable and `0 < t < ∞`. If
`∫ a² ≤ A t I`, `μ(S) ≤ D t⁻¹ I` and `∫_{Sᶜ} b ≤ K I`, then `μ {u > t} ≤ (4A + D + 2K) t⁻¹ I`.
This is the bookkeeping of the Calderón–Zygmund argument: `a` is the good part, controlled in
`L_2`, and `b` the bad part, controlled in `L_1` off the exceptional set `S`. -/
theorem measure_lt_le_of_ae_le_add {u a b : α → ℝ≥0∞} (ha : AEMeasurable a μ)
    (hb : AEMeasurable b μ) (hu : ∀ᵐ x ∂μ, u x ≤ a x + b x) {S : Set α} (hS : MeasurableSet S)
    (ht0 : 0 < t) (ht : t ≠ ∞) {A D K I : ℝ≥0∞} (haI : ∫⁻ x, a x ^ 2 ∂μ ≤ A * t * I)
    (hSI : μ S ≤ D * (t⁻¹ * I)) (hbI : ∫⁻ x in Sᶜ, b x ∂μ ≤ K * I) :
    μ {x | t < u x} ≤ (4 * A + D + 2 * K) * t⁻¹ * I := by
  have htt : (t ^ 2)⁻¹ * t = t⁻¹ := by
    rw [pow_two, ENNReal.mul_inv (Or.inr ht) (Or.inl ht), mul_assoc,
      ENNReal.inv_mul_cancel ht0.ne' ht, mul_one]
  calc μ {x | t < u x} ≤ μ ({x | t / 2 < a x} ∪ {x | t / 2 < b x}) :=
        measure_mono_ae (hu.mono fun x hx hxt =>
          ENNReal.half_lt_or_half_lt_of_lt_add (lt_of_lt_of_le hxt hx))
    _ ≤ μ {x | t / 2 < a x} + μ {x | t / 2 < b x} := measure_union_le _ _
    _ ≤ 4 * (t ^ 2)⁻¹ * (A * t * I) + (μ S + 2 * t⁻¹ * (K * I)) := by
        gcongr
        · exact (measure_half_lt_le_lintegral_sq ha ht0 ht).trans (by gcongr)
        · exact (measure_half_lt_le_add_setLIntegral_compl hb hS ht0 ht).trans (by gcongr)
    _ ≤ 4 * (t ^ 2)⁻¹ * (A * t * I) + (D * (t⁻¹ * I) + 2 * t⁻¹ * (K * I)) := by gcongr
    _ = (4 * A + D + 2 * K) * t⁻¹ * I := by
        rw [show 4 * (t ^ 2)⁻¹ * (A * t * I) = 4 * A * ((t ^ 2)⁻¹ * t) * I by ring, htt]
        ring

end Chebyshev

/-! ### The parts above and below a level -/

/-- **The part above a level**: `∫_{F > s} F ≤ s^(1-p) ∫ F^p` for `p ≥ 1`, `0 < s < ∞` and every
`F : α → [0, ∞]`, since `s^(p-1) F ≤ F^p` where `F > s`. -/
theorem lintegral_indicator_lt_le {p : ℝ} (hp : 1 ≤ p) {s : ℝ≥0∞} (hs0 : s ≠ 0) (hs : s ≠ ∞)
    (F : α → ℝ≥0∞) :
    ∫⁻ x, {y | s < F y}.indicator F x ∂μ ≤ (s ^ (p - 1))⁻¹ * ∫⁻ x, F x ^ p ∂μ := by
  have hc0 : s ^ (p - 1) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hs0) hs).ne'
  have hct : s ^ (p - 1) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by linarith) hs
  rw [← ENNReal.mul_le_iff_le_inv hc0 hct]
  refine (lintegral_const_mul_le _ _).trans (lintegral_mono fun x => ?_)
  by_cases hx : s < F x
  · rw [Set.indicator_of_mem (show x ∈ {y | s < F y} from hx)]
    calc s ^ (p - 1) * F x = F x * s ^ (p - 1) := mul_comm _ _
      _ ≤ F x * F x ^ (p - 1) := mul_le_mul_right (ENNReal.rpow_le_rpow hx.le (by linarith)) _
      _ = F x ^ p := (ENNReal.rpow_eq_mul_rpow_sub_one _ hp).symm
  · rw [Set.indicator_of_notMem (show x ∉ {y | s < F y} from hx), mul_zero]
    exact zero_le

/-- **The part below a level**: `∫_{F ≤ s} F^r ≤ s^(r-p) ∫ F^p` for `0 ≤ p ≤ r`, `0 < r`,
`s < ∞` and every `F : α → [0, ∞]`, since `F^r = F^p F^(r-p) ≤ F^p s^(r-p)` where `F ≤ s`. -/
theorem lintegral_indicator_compl_rpow_le {p r : ℝ} (hp : 0 ≤ p) (hpr : p ≤ r) (hr : 0 < r)
    {s : ℝ≥0∞} (hs : s ≠ ∞) (F : α → ℝ≥0∞) :
    ∫⁻ x, {y | s < F y}ᶜ.indicator F x ^ r ∂μ ≤ s ^ (r - p) * ∫⁻ x, F x ^ p ∂μ := by
  rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) hs)]
  refine lintegral_mono fun x => ?_
  by_cases hx : s < F x
  · rw [Set.indicator_of_notMem (show x ∉ {y | s < F y}ᶜ from not_not.2 hx),
      ENNReal.zero_rpow_of_pos hr]
    exact zero_le
  · rw [Set.indicator_of_mem (show x ∈ {y | s < F y}ᶜ from hx)]
    calc F x ^ r = F x ^ p * F x ^ (r - p) := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ hp (by linarith)]
          congr 1
          ring
      _ ≤ F x ^ p * s ^ (r - p) :=
          mul_le_mul_right (ENNReal.rpow_le_rpow (not_lt.1 hx) (by linarith)) _
      _ = s ^ (r - p) * F x ^ p := mul_comm _ _

/-- **The part above a level has finite integral**: if `∫ F^p < ∞` for some `p ≥ 1`, then
`∫_{F > s} F < ∞` for every `0 < s < ∞` (`MeasureTheory.lintegral_indicator_lt_le`). -/
theorem lintegral_indicator_lt_ne_top {p : ℝ} (hp : 1 ≤ p) {s : ℝ≥0∞} (hs0 : s ≠ 0)
    (hs : s ≠ ∞) {F : α → ℝ≥0∞} (hF : ∫⁻ x, F x ^ p ∂μ ≠ ∞) :
    ∫⁻ x, {y | s < F y}.indicator F x ∂μ ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 hs0) hs).ne') hF) (lintegral_indicator_lt_le hp hs0 hs F)

/-- **The part below a level has finite integral**: if `∫ F^p < ∞` for some `0 ≤ p ≤ r` with
`0 < r`, then `∫_{F ≤ s} F^r < ∞` for every `s < ∞`
(`MeasureTheory.lintegral_indicator_compl_rpow_le`). -/
theorem lintegral_indicator_compl_rpow_ne_top {p r : ℝ} (hp : 0 ≤ p) (hpr : p ≤ r) (hr : 0 < r)
    {s : ℝ≥0∞} (hs : s ≠ ∞) {F : α → ℝ≥0∞} (hF : ∫⁻ x, F x ^ p ∂μ ≠ ∞) :
    ∫⁻ x, {y | s < F y}ᶜ.indicator F x ^ r ∂μ ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) hs) hF)
    (lintegral_indicator_compl_rpow_le hp hpr hr hs F)

/-! ### Two Tonelli steps -/

/-- For a measurable set `S ⊆ ℝ × α` and measurable `F : α → [0, ∞]`, the function
`(τ, x) ↦ 1_{S_τ}(x) F(x)` with the sections `S_τ = {y : (τ, y) ∈ S}` is measurable. -/
theorem measurable_indicator_section {S : Set (ℝ × α)} (hS : MeasurableSet S) {F : α → ℝ≥0∞}
    (hF : Measurable F) : Measurable fun z : ℝ × α => {y | (z.1, y) ∈ S}.indicator F z.2 := by
  have h : (fun z : ℝ × α => {y | (z.1, y) ∈ S}.indicator F z.2) =
      S.indicator (fun z => F z.2) := by
    funext z
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem (show z.2 ∈ {y | (z.1, y) ∈ S} from hz), Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem (show z.2 ∉ {y | (z.1, y) ∈ S} from hz),
        Set.indicator_of_notMem hz]
  rw [h]
  exact (hF.comp measurable_snd).indicator hS

/-- The set `{(τ, y) : ofReal τ < F(y)}` is measurable for measurable `F : α → [0, ∞]`. -/
theorem measurableSet_ofReal_lt {F : α → ℝ≥0∞} (hF : Measurable F) :
    MeasurableSet {z : ℝ × α | ENNReal.ofReal z.1 < F z.2} :=
  measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst) (hF.comp measurable_snd)

/-- **The first Tonelli step**: for every s-finite measure `μ`, measurable `F : α → [0, ∞]` and
`p > 1`, `∫_0^∞ (∫_{F > τ} F dμ) τ^(p-2) dτ = (p - 1)⁻¹ ∫ F^p dμ`, since
`∫_0^F τ^(p-2) dτ = F^(p-1)/(p-1)`. -/
theorem lintegral_Ioi_lintegral_indicator_lt_mul_rpow [SFinite μ] {F : α → ℝ≥0∞}
    (hF : Measurable F) {p : ℝ} (hp : 1 < p) :
    ∫⁻ τ in Ioi (0 : ℝ), (∫⁻ x, {y | ENNReal.ofReal τ < F y}.indicator F x ∂μ) *
        ENNReal.ofReal (τ ^ (p - 2)) = (ENNReal.ofReal (p - 1))⁻¹ * ∫⁻ x, F x ^ p ∂μ := by
  have hJ : AEMeasurable (Function.uncurry fun (τ : ℝ) (x : α) =>
      {y | ENNReal.ofReal τ < F y}.indicator F x * ENNReal.ofReal (τ ^ (p - 2)))
      ((volume.restrict (Ioi (0 : ℝ))).prod μ) :=
    ((measurable_indicator_section (measurableSet_ofReal_lt hF) hF).mul
      (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _))).aemeasurable
  have hpt : ∀ (τ : ℝ) (x : α), {y | ENNReal.ofReal τ < F y}.indicator F x *
      ENNReal.ofReal (τ ^ (p - 2)) =
      F x * {s : ℝ | ENNReal.ofReal s < F x}.indicator (fun s => ENNReal.ofReal (s ^ (p - 2))) τ :=
      fun τ x => by
    by_cases hτ : ENNReal.ofReal τ < F x
    · rw [Set.indicator_of_mem (show x ∈ {y | ENNReal.ofReal τ < F y} from hτ),
        Set.indicator_of_mem (show τ ∈ {s : ℝ | ENNReal.ofReal s < F x} from hτ)]
    · rw [Set.indicator_of_notMem (show x ∉ {y | ENNReal.ofReal τ < F y} from hτ),
        Set.indicator_of_notMem (show τ ∉ {s : ℝ | ENNReal.ofReal s < F x} from hτ), zero_mul,
        mul_zero]
  have hm : ∀ x, Measurable fun s : ℝ =>
      {s : ℝ | ENNReal.ofReal s < F x}.indicator (fun s => ENNReal.ofReal (s ^ (p - 2))) s :=
    fun x => (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).indicator
      (measurableSet_lt ENNReal.measurable_ofReal measurable_const)
  simp_rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_lintegral_swap hJ, ← lintegral_const_mul' _ _
    (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (by linarith)).ne')]
  refine lintegral_congr fun x => ?_
  simp_rw [hpt]
  rw [lintegral_const_mul _ (hm x), lintegral_Ioi_rpow_indicator_lt (by linarith),
    show p - 2 + 1 = p - 1 by ring, div_eq_mul_inv, ← mul_assoc,
    ← ENNReal.rpow_eq_mul_rpow_sub_one _ hp.le, mul_comm]

/-- **The second Tonelli step**: for every s-finite measure `μ`, measurable `F : α → [0, ∞]`,
`0 < r` and `p < r`, `∫_0^∞ (∫_{F ≤ τ} F^r dμ) τ^(p-1-r) dτ ≤ (r - p)⁻¹ ∫ F^p dμ`, since
`∫_F^∞ τ^(p-1-r) dτ = F^(p-r)/(r-p)` and `F^r F^(p-r) ≤ F^p`. -/
theorem lintegral_Ioi_lintegral_indicator_compl_mul_rpow_le [SFinite μ] {F : α → ℝ≥0∞}
    (hF : Measurable F) {p r : ℝ} (hr : 0 < r) (hpr : p < r) :
    ∫⁻ τ in Ioi (0 : ℝ), (∫⁻ x, {y | ENNReal.ofReal τ < F y}ᶜ.indicator F x ^ r ∂μ) *
        ENNReal.ofReal (τ ^ (p - 1 - r)) ≤ (ENNReal.ofReal (r - p))⁻¹ * ∫⁻ x, F x ^ p ∂μ := by
  have hJ : AEMeasurable (Function.uncurry fun (τ : ℝ) (x : α) =>
      {y | ENNReal.ofReal τ < F y}ᶜ.indicator F x ^ r * ENNReal.ofReal (τ ^ (p - 1 - r)))
      ((volume.restrict (Ioi (0 : ℝ))).prod μ) :=
    (((measurable_indicator_section (measurableSet_ofReal_lt hF).compl hF).pow_const r).mul
      (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _))).aemeasurable
  have hpt : ∀ (τ : ℝ) (x : α), {y | ENNReal.ofReal τ < F y}ᶜ.indicator F x ^ r *
      ENNReal.ofReal (τ ^ (p - 1 - r)) = F x ^ r *
        {s : ℝ | F x ≤ ENNReal.ofReal s}.indicator (fun s => ENNReal.ofReal (s ^ (p - 1 - r))) τ :=
      fun τ x => by
    by_cases hτ : ENNReal.ofReal τ < F x
    · rw [Set.indicator_of_notMem (show x ∉ {y | ENNReal.ofReal τ < F y}ᶜ from not_not.2 hτ),
        Set.indicator_of_notMem (show τ ∉ {s : ℝ | F x ≤ ENNReal.ofReal s} from not_le.2 hτ),
        ENNReal.zero_rpow_of_pos hr, zero_mul, mul_zero]
    · rw [Set.indicator_of_mem (show x ∈ {y | ENNReal.ofReal τ < F y}ᶜ from hτ),
        Set.indicator_of_mem (show τ ∈ {s : ℝ | F x ≤ ENNReal.ofReal s} from not_lt.1 hτ)]
  have hm : ∀ x, Measurable fun s : ℝ =>
      {s : ℝ | F x ≤ ENNReal.ofReal s}.indicator (fun s => ENNReal.ofReal (s ^ (p - 1 - r))) s :=
    fun x => (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).indicator
      (measurableSet_le measurable_const ENNReal.measurable_ofReal)
  simp_rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_lintegral_swap hJ, ← lintegral_const_mul' _ _
    (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (by linarith)).ne')]
  refine lintegral_mono fun x => ?_
  simp_rw [hpt]
  rw [lintegral_const_mul _ (hm x), lintegral_Ioi_rpow_indicator_ge (by linarith),
    show p - 1 - r + 1 = p - r by ring, show -(p - r) = r - p by ring, div_eq_mul_inv,
    ← mul_assoc, mul_comm _ (ENNReal.ofReal (r - p))⁻¹]
  exact mul_le_mul_right (ENNReal.rpow_mul_rpow_sub_le _ hr hpr) _

/-! ### The layer cake argument -/

/-- **Integrals of powers from bounds at every level**: let `μ` be s-finite, `F : α' → [0, ∞]`
almost everywhere measurable, `G : α → [0, ∞]` measurable, `1 < p < r` and `K₁, K₂ ∈ [0, ∞]`. If
for every `τ > 0`
`ν{F > τ} τ^(p-1) ≤ K₁ τ^(p-2) ∫_{G > τ} G dμ + K₂ τ^(p-1-r) ∫_{G ≤ τ} G^r dμ`, then
`∫ F^p dν ≤ p (K₁/(p - 1) + K₂/(r - p)) ∫ G^p dμ`: the layer cake formula and the two Tonelli
steps. -/
theorem lintegral_rpow_le_of_measure_lt_mul_rpow_le [SFinite μ] {F : α' → ℝ≥0∞}
    {G : α → ℝ≥0∞} (hF : AEMeasurable F ν) (hG : Measurable G) {p r : ℝ} (hp1 : 1 < p)
    (hpr : p < r) {K₁ K₂ : ℝ≥0∞}
    (h : ∀ τ : ℝ, 0 < τ → ν {x | ENNReal.ofReal τ < F x} * ENNReal.ofReal (τ ^ (p - 1)) ≤
      K₁ * ((∫⁻ x, {y | ENNReal.ofReal τ < G y}.indicator G x ∂μ) *
          ENNReal.ofReal (τ ^ (p - 2))) +
        K₂ * ((∫⁻ x, {y | ENNReal.ofReal τ < G y}ᶜ.indicator G x ^ r ∂μ) *
          ENNReal.ofReal (τ ^ (p - 1 - r)))) :
    ∫⁻ x, F x ^ p ∂ν ≤ ENNReal.ofReal p *
      (K₁ * (ENNReal.ofReal (p - 1))⁻¹ + K₂ * (ENNReal.ofReal (r - p))⁻¹) * ∫⁻ x, G x ^ p ∂μ := by
  have hm1 : Measurable fun τ : ℝ =>
      (∫⁻ x, {y | ENNReal.ofReal τ < G y}.indicator G x ∂μ) * ENNReal.ofReal (τ ^ (p - 2)) :=
    (Measurable.lintegral_prod_right'
      (measurable_indicator_section (measurableSet_ofReal_lt hG) hG)).mul
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))
  have hm2 : Measurable fun τ : ℝ =>
      (∫⁻ x, {y | ENNReal.ofReal τ < G y}ᶜ.indicator G x ^ r ∂μ) *
        ENNReal.ofReal (τ ^ (p - 1 - r)) :=
    (Measurable.lintegral_prod_right'
      ((measurable_indicator_section (measurableSet_ofReal_lt hG).compl hG).pow_const r)).mul
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul_ennreal ν hF (by linarith)]
  calc ENNReal.ofReal p * ∫⁻ τ in Ioi (0 : ℝ),
        ν {x | ENNReal.ofReal τ < F x} * ENNReal.ofReal (τ ^ (p - 1))
      ≤ ENNReal.ofReal p * ∫⁻ τ in Ioi (0 : ℝ),
          (K₁ * ((∫⁻ x, {y | ENNReal.ofReal τ < G y}.indicator G x ∂μ) *
            ENNReal.ofReal (τ ^ (p - 2))) +
          K₂ * ((∫⁻ x, {y | ENNReal.ofReal τ < G y}ᶜ.indicator G x ^ r ∂μ) *
            ENNReal.ofReal (τ ^ (p - 1 - r)))) :=
        mul_le_mul_right (setLIntegral_mono' measurableSet_Ioi fun τ hτ => h τ hτ) _
    _ = ENNReal.ofReal p * (K₁ * ((ENNReal.ofReal (p - 1))⁻¹ * ∫⁻ x, G x ^ p ∂μ) +
          K₂ * ∫⁻ τ in Ioi (0 : ℝ),
            (∫⁻ x, {y | ENNReal.ofReal τ < G y}ᶜ.indicator G x ^ r ∂μ) *
              ENNReal.ofReal (τ ^ (p - 1 - r))) := by
        rw [lintegral_add_left (hm1.const_mul _), lintegral_const_mul _ hm1,
          lintegral_const_mul _ hm2, lintegral_Ioi_lintegral_indicator_lt_mul_rpow hG hp1]
    _ ≤ ENNReal.ofReal p * (K₁ * ((ENNReal.ofReal (p - 1))⁻¹ * ∫⁻ x, G x ^ p ∂μ) +
          K₂ * ((ENNReal.ofReal (r - p))⁻¹ * ∫⁻ x, G x ^ p ∂μ)) := by
        gcongr
        exact lintegral_Ioi_lintegral_indicator_compl_mul_rpow_le hG (by linarith) hpr
    _ = _ := by ring

/-- **The level estimate**: let `τ > 0` and `F ≤ F₁ + F₂` almost everywhere, with `F₂` almost
everywhere measurable. If `ν{F₁ > τ/2} ≤ C₁ (τ/2)⁻¹ I₁` and `∫ F₂² dν ≤ C₂ I₂`, then
`ν{F > τ} τ^(p-1) ≤ 2 C₁ τ^(p-2) I₁ + 4 C₂ τ^(p-3) I₂` for every real `p`: `{F > τ}` lies in
`{F₁ > τ/2} ∪ {F₂ > τ/2}` almost everywhere (`MeasureTheory.distribution_add_le_of_enorm`), and
Chebyshev's inequality bounds the second set. -/
theorem measure_lt_mul_rpow_le_of_le_add {F F₁ F₂ : α' → ℝ≥0∞} (hF₂ : AEMeasurable F₂ ν)
    (hsplit : ∀ᵐ x ∂ν, F x ≤ F₁ x + F₂ x) {τ : ℝ} (hτ : 0 < τ) (p : ℝ) {C₁ C₂ I₁ I₂ : ℝ≥0∞}
    (hweak : ν {x | ENNReal.ofReal τ / 2 < F₁ x} ≤ C₁ * (ENNReal.ofReal τ / 2)⁻¹ * I₁)
    (hstrong : ∫⁻ x, F₂ x ^ 2 ∂ν ≤ C₂ * I₂) :
    ν {x | ENNReal.ofReal τ < F x} * ENNReal.ofReal (τ ^ (p - 1)) ≤
      2 * C₁ * (I₁ * ENNReal.ofReal (τ ^ (p - 2))) +
        4 * C₂ * (I₂ * ENNReal.ofReal (τ ^ (p - 1 - 2))) := by
  have ht0 : ENNReal.ofReal τ / 2 ≠ 0 := (ENNReal.half_pos (ENNReal.ofReal_pos.2 hτ).ne').ne'
  have htt : ENNReal.ofReal τ / 2 ≠ ∞ := ENNReal.div_ne_top ENNReal.ofReal_ne_top two_ne_zero
  have h2 : ν {x | ENNReal.ofReal τ / 2 < F₂ x} ≤
      ((ENNReal.ofReal τ / 2) ^ (2 : ℝ))⁻¹ * (C₂ * I₂) :=
    (measure_lt_le_inv_rpow_mul_lintegral hF₂ two_pos ht0 htt).trans
      (by gcongr; simpa only [ENNReal.rpow_two] using hstrong)
  have hunion : ν {x | ENNReal.ofReal τ < F x} ≤
      ν {x | ENNReal.ofReal τ / 2 < F₁ x} + ν {x | ENNReal.ofReal τ / 2 < F₂ x} := by
    have h := distribution_add_le_of_enorm (μ := ν) (c := 1) (t := ENNReal.ofReal τ / 2)
      (s := ENNReal.ofReal τ / 2) (f := F) (g₁ := F₁) (g₂ := F₂)
      (hsplit.mono fun x hx => by simpa only [eNorm_eq_self, one_mul] using hx)
    simpa only [distribution, eNorm_eq_self, one_mul, ENNReal.add_halves] using h
  have h4 : (2 : ℝ≥0∞) ^ (2 : ℝ) = 4 := by rw [ENNReal.rpow_two]; norm_num
  calc ν {x | ENNReal.ofReal τ < F x} * ENNReal.ofReal (τ ^ (p - 1))
      ≤ (C₁ * (ENNReal.ofReal τ / 2)⁻¹ * I₁ +
          ((ENNReal.ofReal τ / 2) ^ (2 : ℝ))⁻¹ * (C₂ * I₂)) * ENNReal.ofReal (τ ^ (p - 1)) :=
        mul_le_mul_left (hunion.trans (add_le_add hweak h2)) _
    _ = C₁ * I₁ * ((ENNReal.ofReal τ / 2)⁻¹ * ENNReal.ofReal (τ ^ (p - 1))) +
          C₂ * I₂ * (((ENNReal.ofReal τ / 2) ^ (2 : ℝ))⁻¹ * ENNReal.ofReal (τ ^ (p - 1))) := by
        ring
    _ = _ := by
        rw [ENNReal.inv_half_mul_ofReal_rpow hτ p, ENNReal.inv_half_rpow_mul_ofReal_rpow hτ p 2,
          h4]
        ring

/-- The constant of Marcinkiewicz interpolation between weak type `(1,1)` with constant `C₁`
and the bound `∫ (T f)² ≤ C₂ ∫ f²`, for the integrals of `p`-th powers:
`p (2 C₁/(p - 1) + 4 C₂/(2 - p))` for `1 < p < 2`, the range where it is used. -/
noncomputable def marcinkiewiczConst (p : ℝ) (C₁ C₂ : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal p * (2 * C₁ * (ENNReal.ofReal (p - 1))⁻¹ + 4 * C₂ * (ENNReal.ofReal (2 - p))⁻¹)

/-- `marcinkiewiczConst p C₁ C₂` is finite for `1 < p < 2` and finite `C₁`, `C₂`. -/
theorem marcinkiewiczConst_ne_top {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) {C₁ C₂ : ℝ≥0∞}
    (hC₁ : C₁ ≠ ∞) (hC₂ : C₂ ≠ ∞) : marcinkiewiczConst p C₁ C₂ ≠ ∞ := by
  have h1 : (ENNReal.ofReal (p - 1))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have h2 : (ENNReal.ofReal (2 - p))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (by linarith)).ne'
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hC₁) h1,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hC₂) h2⟩)

/-- **The layer cake argument of Marcinkiewicz interpolation**: let `μ` be s-finite,
`F : α' → [0, ∞]` almost everywhere measurable, `G : α → [0, ∞]` measurable and `1 < p < 2`.
Suppose that for every `τ > 0` there are `F₁ τ`, `F₂ τ` with `F ≤ F₁ τ + F₂ τ` almost
everywhere, `F₂ τ` almost everywhere measurable,
`ν{F₁ τ > τ/2} ≤ C₁ (τ/2)⁻¹ ∫_{G > τ} G dμ` and `∫ (F₂ τ)² dν ≤ C₂ ∫_{G ≤ τ} G² dμ`. Then
`∫ F^p dν ≤ marcinkiewiczConst p C₁ C₂ ∫ G^p dμ`. -/
theorem lintegral_rpow_le_of_forall_le_add [SFinite μ] {F : α' → ℝ≥0∞} {G : α → ℝ≥0∞}
    (F₁ F₂ : ℝ → α' → ℝ≥0∞) (hF : AEMeasurable F ν) (hG : Measurable G)
    (hF₂ : ∀ τ : ℝ, 0 < τ → AEMeasurable (F₂ τ) ν)
    (hsplit : ∀ τ : ℝ, 0 < τ → ∀ᵐ x ∂ν, F x ≤ F₁ τ x + F₂ τ x) {C₁ C₂ : ℝ≥0∞}
    (hweak : ∀ τ : ℝ, 0 < τ → ν {x | ENNReal.ofReal τ / 2 < F₁ τ x} ≤
      C₁ * (ENNReal.ofReal τ / 2)⁻¹ * ∫⁻ x, {y | ENNReal.ofReal τ < G y}.indicator G x ∂μ)
    (hstrong : ∀ τ : ℝ, 0 < τ → ∫⁻ x, F₂ τ x ^ 2 ∂ν ≤
      C₂ * ∫⁻ x, {y | ENNReal.ofReal τ < G y}ᶜ.indicator G x ^ 2 ∂μ)
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    ∫⁻ x, F x ^ p ∂ν ≤ marcinkiewiczConst p C₁ C₂ * ∫⁻ x, G x ^ p ∂μ :=
  lintegral_rpow_le_of_measure_lt_mul_rpow_le (r := 2) hF hG hp1 hp2 fun τ hτ => by
    simp only [ENNReal.rpow_two]
    exact measure_lt_mul_rpow_le_of_le_add (hF₂ τ hτ) (hsplit τ hτ) hτ p (hweak τ hτ)
      (hstrong τ hτ)

/-! ### Operators on an abstract input type -/

/-- **Marcinkiewicz interpolation for operators on an abstract input type**: let `μ` be
s-finite and `1 < p < 2`. Every input `x : X` has a measurable size `G x : α → [0, ∞]` and an
almost everywhere measurable output `T x : α' → [0, ∞]`, and `res x S` restricts `x` to a
measurable set `S`, with size `1_S G x`. Suppose that `T x ≤ T (res x S) + T (res x Sᶜ)` almost
everywhere when `∫ (G x)^p < ∞`, that `ν{T x > t} ≤ C₁ t⁻¹ ∫ G x` for `0 < t < ∞` when
`∫ G x < ∞` (weak type `(1,1)`), and that `∫ (T x)² ≤ C₂ ∫ (G x)²` when `∫ (G x)² < ∞`
(strong type `(2,2)`). Then `∫ (T x)^p ≤ marcinkiewiczConst p C₁ C₂ ∫ (G x)^p` for every `x`
with `∫ (G x)^p < ∞`. At the level `τ` the input is split along `{G x > τ}`. -/
theorem lintegral_rpow_le_of_weak_one_strong_two [SFinite μ] {X : Type*} (G : X → α → ℝ≥0∞)
    (T : X → α' → ℝ≥0∞) (res : X → Set α → X) {p : ℝ} {C₁ C₂ : ℝ≥0∞}
    (hG : ∀ x, Measurable (G x)) (hT : ∀ x, AEMeasurable (T x) ν)
    (hres : ∀ x S, MeasurableSet S → G (res x S) = S.indicator (G x))
    (hsub : ∀ x S, MeasurableSet S → ∫⁻ a, G x a ^ p ∂μ ≠ ∞ →
      ∀ᵐ a ∂ν, T x a ≤ T (res x S) a + T (res x Sᶜ) a)
    (hweak : ∀ x, ∫⁻ a, G x a ∂μ ≠ ∞ → ∀ t, 0 < t → t ≠ ∞ →
      ν {a | t < T x a} ≤ C₁ * t⁻¹ * ∫⁻ a, G x a ∂μ)
    (hstrong : ∀ x, ∫⁻ a, G x a ^ 2 ∂μ ≠ ∞ → ∫⁻ a, T x a ^ 2 ∂ν ≤ C₂ * ∫⁻ a, G x a ^ 2 ∂μ)
    (hp1 : 1 < p) (hp2 : p < 2) (x : X) (hx : ∫⁻ a, G x a ^ p ∂μ ≠ ∞) :
    ∫⁻ a, T x a ^ p ∂ν ≤ marcinkiewiczConst p C₁ C₂ * ∫⁻ a, G x a ^ p ∂μ := by
  have hS : ∀ τ : ℝ, MeasurableSet {y | ENNReal.ofReal τ < G x y} := fun τ =>
    measurableSet_lt measurable_const (hG x)
  refine lintegral_rpow_le_of_forall_le_add (fun τ => T (res x {y | ENNReal.ofReal τ < G x y}))
    (fun τ => T (res x {y | ENNReal.ofReal τ < G x y}ᶜ)) (hT x) (hG x) (fun τ _ => hT _)
    (fun τ _ => hsub x _ (hS τ) hx) (fun τ hτ => ?_) (fun τ hτ => ?_) hp1 hp2
  · have hτ0 : ENNReal.ofReal τ ≠ 0 := (ENNReal.ofReal_pos.2 hτ).ne'
    have hfin : ∫⁻ a, G (res x {y | ENNReal.ofReal τ < G x y}) a ∂μ ≠ ∞ := by
      rw [hres x _ (hS τ)]
      exact lintegral_indicator_lt_ne_top hp1.le hτ0 ENNReal.ofReal_ne_top hx
    have h := hweak _ hfin (ENNReal.ofReal τ / 2) (ENNReal.half_pos hτ0)
      (ENNReal.div_ne_top ENNReal.ofReal_ne_top two_ne_zero)
    rwa [hres x _ (hS τ)] at h
  · have hfin : ∫⁻ a, G (res x {y | ENNReal.ofReal τ < G x y}ᶜ) a ^ 2 ∂μ ≠ ∞ := by
      rw [hres x _ (hS τ).compl]
      simpa only [ENNReal.rpow_two] using lintegral_indicator_compl_rpow_ne_top (r := 2)
        (by linarith) hp2.le two_pos ENNReal.ofReal_ne_top hx
    have h := hstrong _ hfin
    rwa [hres x _ (hS τ).compl] at h

/-- **Marcinkiewicz interpolation for operators on an abstract input type, in `L_p` norms**:
under the hypotheses of `MeasureTheory.lintegral_rpow_le_of_weak_one_strong_two` with
`p ∈ (1, 2)` in `[0, ∞]`, `‖T x‖_p ≤ (marcinkiewiczConst p C₁ C₂)^(1/p) ‖G x‖_p` for every `x`
with `‖G x‖_p < ∞`. -/
theorem eLpNorm_le_of_weak_one_strong_two [SFinite μ] {X : Type*} (G : X → α → ℝ≥0∞)
    (T : X → α' → ℝ≥0∞) (res : X → Set α → X) {p : ℝ≥0∞} {C₁ C₂ : ℝ≥0∞}
    (hG : ∀ x, Measurable (G x)) (hT : ∀ x, AEMeasurable (T x) ν)
    (hres : ∀ x S, MeasurableSet S → G (res x S) = S.indicator (G x))
    (hsub : ∀ x S, MeasurableSet S → ∫⁻ a, G x a ^ p.toReal ∂μ ≠ ∞ →
      ∀ᵐ a ∂ν, T x a ≤ T (res x S) a + T (res x Sᶜ) a)
    (hweak : ∀ x, ∫⁻ a, G x a ∂μ ≠ ∞ → ∀ t, 0 < t → t ≠ ∞ →
      ν {a | t < T x a} ≤ C₁ * t⁻¹ * ∫⁻ a, G x a ∂μ)
    (hstrong : ∀ x, ∫⁻ a, G x a ^ 2 ∂μ ≠ ∞ → ∫⁻ a, T x a ^ 2 ∂ν ≤ C₂ * ∫⁻ a, G x a ^ 2 ∂μ)
    (hp1 : 1 < p) (hp2 : p < 2) (x : X) (hx : eLpNorm (G x) p μ ≠ ∞) :
    eLpNorm (T x) p ν ≤ marcinkiewiczConst p.toReal C₁ C₂ ^ (1 / p.toReal) * eLpNorm (G x) p μ := by
  have hp : p ≠ ∞ := ne_top_of_lt hp2
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
  refine eLpNorm_le_rpow_mul_of_lintegral_enorm_le hp0 hp (hT x).aestronglyMeasurable
    (hG x).aestronglyMeasurable ?_
  simp only [eNorm_eq_self]
  refine lintegral_rpow_le_of_weak_one_strong_two G T res hG hT hres hsub hweak hstrong
    (ENNReal.one_lt_toReal hp1 hp) (ENNReal.toReal_lt_of_lt_ofReal (by rwa [ENNReal.ofReal_ofNat]))
    x ?_
  rw [← eLpNorm_rpow_eq_lintegral hp0 hp (hG x).aemeasurable]
  exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hx

/-! ### Operators in the terms of the Carleson project -/

/-- **Level sets of a multiple from the weak `L_1` norm**: for `g : α' → ε`, `A ≥ 0` and
`0 < t < ∞`, `ν{A ‖g‖ > t} ≤ A t⁻¹ ‖g‖_{1,∞}`. -/
theorem measure_lt_mul_enorm_le_wnorm_one {ε : Type*} [ENorm ε] (g : α' → ε) (A : ℝ≥0)
    {t : ℝ≥0∞} (ht0 : t ≠ 0) (ht : t ≠ ∞) :
    ν {x | t < A * ‖g x‖ₑ} ≤ A * t⁻¹ * wnorm g 1 ν := by
  rcases eq_or_ne A 0 with rfl | hA
  · have : {x | t < ((0 : ℝ≥0) : ℝ≥0∞) * ‖g x‖ₑ} = ∅ := by
      ext x
      simp
    rw [this, measure_empty]
    exact zero_le
  have hA0 : (A : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hA
  have hset : {x | t < A * ‖g x‖ₑ} = {x | t / A < ‖g x‖ₑ} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [ENNReal.div_lt_iff (Or.inl hA0) (Or.inl ENNReal.coe_ne_top), mul_comm]
  have hs0 : t / A ≠ 0 := (ENNReal.div_pos_iff.2 ⟨ht0, ENNReal.coe_ne_top⟩).ne'
  have hst : t / A ≠ ∞ := ENNReal.div_ne_top ht hA0
  have h := mul_distribution_le_wnorm_one (μ := ν) g (t / A)
  rw [ENNReal.mul_le_iff_le_inv hs0 hst, ENNReal.inv_div (Or.inl ENNReal.coe_ne_top) (Or.inl hA0),
    div_eq_mul_inv] at h
  rw [hset]
  exact h

/-- **Squares of a multiple from the strong type `(2,2)`**: if `T` has strong type `(2,2)` with
constant `C₂`, then `∫ (A ‖T g‖)² dν ≤ A² C₂² ∫ ‖g‖² dμ` for every `g ∈ L_2(μ)` and `A ≥ 0`. -/
theorem lintegral_mul_enorm_sq_le_of_hasStrongType {ε₁ ε₂ : Type*} [TopologicalSpace ε₁]
    [ContinuousENorm ε₁] [TopologicalSpace ε₂] [ContinuousENorm ε₂] {T : (α → ε₁) → (α' → ε₂)}
    {C₂ : ℝ≥0∞} (h₂ : HasStrongType T 2 2 μ ν C₂) (A : ℝ≥0) {g : α → ε₁} (hg : MemLp g 2 μ) :
    ∫⁻ x, ((A : ℝ≥0∞) * ‖T g x‖ₑ) ^ 2 ∂ν ≤ A ^ 2 * C₂ ^ 2 * ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ := by
  obtain ⟨hm, hle⟩ := h₂ g hg
  simp_rw [mul_pow]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top),
    lintegral_enorm_sq_eq_eLpNorm_sq hm, lintegral_enorm_sq_eq_eLpNorm_sq hg.aestronglyMeasurable]
  calc (A : ℝ≥0∞) ^ 2 * eLpNorm (T g) 2 ν ^ 2 ≤ (A : ℝ≥0∞) ^ 2 * (C₂ * eLpNorm g 2 μ) ^ 2 := by
        gcongr
    _ = _ := by ring

/-- Restricting a function and its extended norm to a set: if `‖f‖ = G` almost everywhere,
then `‖1_S f‖ = 1_S G` almost everywhere, for every set `S`. -/
theorem ae_enorm_indicator_eq {ε₁ : Type*} [TopologicalSpace ε₁] [ESeminormedAddMonoid ε₁]
    {f : α → ε₁} {G : α → ℝ≥0∞} (hfG : ∀ᵐ x ∂μ, ‖f x‖ₑ = G x) (S : Set α) :
    ∀ᵐ x ∂μ, ‖S.indicator f x‖ₑ = S.indicator G x :=
  hfG.mono fun x hx => by
    rw [eNorm_indicator_eq_indicator_eNorm]
    by_cases h : x ∈ S
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, hx]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]

/-- Integrals of powers of a restricted function: if `‖f‖ = G` almost everywhere, then
`∫ ‖1_S f‖^r = ∫ (1_S G)^r` for every set `S` and every real `r`. -/
theorem lintegral_enorm_indicator_rpow_eq {ε₁ : Type*} [TopologicalSpace ε₁]
    [ESeminormedAddMonoid ε₁] {f : α → ε₁} {G : α → ℝ≥0∞} (hfG : ∀ᵐ x ∂μ, ‖f x‖ₑ = G x)
    (S : Set α) (r : ℝ) : ∫⁻ x, ‖S.indicator f x‖ₑ ^ r ∂μ = ∫⁻ x, S.indicator G x ^ r ∂μ :=
  lintegral_congr_ae ((ae_enorm_indicator_eq hfG S).mono fun x hx => by simp only [hx])

/-- **The part above a level lies in `L_1`**: for almost everywhere strongly measurable `f` with
`‖f‖ = G` almost everywhere, where `G` is measurable with `∫ G^p < ∞` for some `p ≥ 1`,
`1_{G > τ} f ∈ L_1` for every `τ > 0`, since `∫_{G > τ} G ≤ τ^(1-p) ∫ G^p`. -/
theorem memLp_one_indicator_lt {ε₁ : Type*} [TopologicalSpace ε₁] [ESeminormedAddMonoid ε₁]
    {f : α → ε₁} {G : α → ℝ≥0∞} (hf : AEStronglyMeasurable f μ)
    (hfG : ∀ᵐ x ∂μ, ‖f x‖ₑ = G x) (hG : Measurable G) {p : ℝ} (hp : 1 ≤ p)
    (hGp : ∫⁻ x, G x ^ p ∂μ ≠ ∞) {τ : ℝ} (hτ : 0 < τ) :
    MemLp ({y | ENNReal.ofReal τ < G y}.indicator f) 1 μ := by
  have hm := hf.indicator (measurableSet_lt (measurable_const (a := ENNReal.ofReal τ)) hG)
  rw [MemLp, eLpNorm_one_eq_lintegral_eNorm hm, lintegral_congr_ae (ae_enorm_indicator_eq hfG _)]
  exact (lintegral_indicator_lt_ne_top hp (ENNReal.ofReal_pos.2 hτ).ne' ENNReal.ofReal_ne_top
    hGp).lt_top

/-- **The part below a level lies in `L_2`**: for almost everywhere strongly measurable `f` with
`‖f‖ = G` almost everywhere, where `G` is measurable with `∫ G^p < ∞` for some `0 ≤ p ≤ 2`,
`1_{G ≤ τ} f ∈ L_2` for every real `τ`, since `∫_{G ≤ τ} G² ≤ τ^(2-p) ∫ G^p`. -/
theorem memLp_two_indicator_compl {ε₁ : Type*} [TopologicalSpace ε₁] [ESeminormedAddMonoid ε₁]
    {f : α → ε₁} {G : α → ℝ≥0∞} (hf : AEStronglyMeasurable f μ)
    (hfG : ∀ᵐ x ∂μ, ‖f x‖ₑ = G x) (hG : Measurable G) {p : ℝ} (hp0 : 0 ≤ p) (hp2 : p ≤ 2)
    (hGp : ∫⁻ x, G x ^ p ∂μ ≠ ∞) (τ : ℝ) :
    MemLp ({y | ENNReal.ofReal τ < G y}ᶜ.indicator f) 2 μ := by
  have hm := hf.indicator (measurableSet_lt (measurable_const (a := ENNReal.ofReal τ)) hG).compl
  refine (eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hm).2 ?_
  rw [ENNReal.toReal_ofNat,
    lintegral_enorm_indicator_rpow_eq hfG {y | ENNReal.ofReal τ < G y}ᶜ 2]
  exact (lintegral_indicator_compl_rpow_ne_top hp0 hp2 two_pos ENNReal.ofReal_ne_top hGp).lt_top

/-- The constant of Marcinkiewicz interpolation in `L_p` norms, for an operator of weak type
`(1,1)` with constant `C₁`, of strong type `(2,2)` with constant `C₂` and subadditive with
constant `A`: `(marcinkiewiczConst p (A C₁) (A² C₂²))^(1/p)` for `1 < p < 2`, the range where it
is used. -/
noncomputable def marcinkiewiczNormConst (p A C₁ C₂ : ℝ≥0∞) : ℝ≥0∞ :=
  marcinkiewiczConst p.toReal (A * C₁) (A ^ 2 * C₂ ^ 2) ^ (1 / p.toReal)

/-- `marcinkiewiczNormConst p A C₁ C₂` is finite for `1 < p < 2` and finite `A`, `C₁`, `C₂`. -/
theorem marcinkiewiczNormConst_ne_top {p A C₁ C₂ : ℝ≥0∞} (hp1 : 1 < p) (hp2 : p < 2)
    (hA : A ≠ ∞) (hC₁ : C₁ ≠ ∞) (hC₂ : C₂ ≠ ∞) : marcinkiewiczNormConst p A C₁ C₂ ≠ ∞ :=
  ENNReal.rpow_ne_top_of_nonneg (by positivity) (marcinkiewiczConst_ne_top
    (ENNReal.one_lt_toReal hp1 (ne_top_of_lt hp2))
    (ENNReal.toReal_lt_of_lt_ofReal (by rwa [ENNReal.ofReal_ofNat])) (ENNReal.mul_ne_top hA hC₁)
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top hA) (ENNReal.pow_ne_top hC₂)))

/-- **Marcinkiewicz interpolation in integral form, in the terms of the Carleson project**: let
`μ` be s-finite, `1 < p < 2`, and let `T` be almost everywhere subadditive with constant `A` on
`L_1(μ) ∪ L_2(μ)`, of weak type `(1,1)` with constant `C₁` and of strong type `(2,2)` with
constant `C₂`. Then `∫ ‖T f‖^p dν ≤ marcinkiewiczConst p (A C₁) (A² C₂²) ∫ ‖f‖^p dμ` for every
almost everywhere strongly measurable `f` with `∫ ‖f‖^p < ∞` and almost everywhere strongly
measurable `T f`. At the level `τ`, `f` splits into `1_{‖f‖ > τ} f ∈ L_1` and
`1_{‖f‖ ≤ τ} f ∈ L_2`. -/
theorem lintegral_enorm_rpow_le_of_hasWeakType_of_hasStrongType [SFinite μ]
    {ε₁ ε₂ : Type*} [TopologicalSpace ε₁] [ESeminormedAddMonoid ε₁] [TopologicalSpace ε₂]
    [ContinuousENorm ε₂] {T : (α → ε₁) → (α' → ε₂)} {A : ℝ≥0} {C₁ C₂ : ℝ≥0∞} {p : ℝ}
    (hp1 : 1 < p) (hp2 : p < 2) (hT : AESubadditiveOn T (fun f => MemLp f 1 μ ∨ MemLp f 2 μ) A ν)
    (h₁ : HasWeakType T 1 1 μ ν C₁) (h₂ : HasStrongType T 2 2 μ ν C₂) {f : α → ε₁}
    (hf : AEStronglyMeasurable f μ) (hfp : ∫⁻ x, ‖f x‖ₑ ^ p ∂μ ≠ ∞)
    (hTf : AEStronglyMeasurable (T f) ν) :
    ∫⁻ x, ‖T f x‖ₑ ^ p ∂ν ≤
      marcinkiewiczConst p (A * C₁) (A ^ 2 * C₂ ^ 2) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  obtain ⟨G, hG, hfG⟩ := hf.eNorm
  have hGf : ∫⁻ x, ‖f x‖ₑ ^ p ∂μ = ∫⁻ x, G x ^ p ∂μ :=
    lintegral_congr_ae (hfG.mono fun x (hx : ‖f x‖ₑ = G x) => by simp only [hx])
  rw [hGf] at hfp ⊢
  have h1 : ∀ τ : ℝ, 0 < τ → MemLp ({y | ENNReal.ofReal τ < G y}.indicator f) 1 μ := fun τ hτ =>
    memLp_one_indicator_lt hf hfG hG hp1.le hfp hτ
  have h2 : ∀ τ : ℝ, MemLp ({y | ENNReal.ofReal τ < G y}ᶜ.indicator f) 2 μ := fun τ =>
    memLp_two_indicator_compl hf hfG hG (by linarith) hp2.le hfp τ
  refine lintegral_rpow_le_of_forall_le_add
    (fun τ x => A * ‖T ({y | ENNReal.ofReal τ < G y}.indicator f) x‖ₑ)
    (fun τ x => A * ‖T ({y | ENNReal.ofReal τ < G y}ᶜ.indicator f) x‖ₑ) hTf.eNorm hG
    (fun τ _ => ((h₂ _ (h2 τ)).1.eNorm.const_mul _)) (fun τ hτ => ?_) (fun τ hτ => ?_)
    (fun τ _ => ?_) hp1 hp2
  · filter_upwards [hT _ _ (Or.inl (h1 τ hτ)) (Or.inr (h2 τ))] with x hx
    rw [Set.indicator_self_add_compl, mul_add] at hx
    exact hx
  · have ht0 : ENNReal.ofReal τ / 2 ≠ 0 := (ENNReal.half_pos (ENNReal.ofReal_pos.2 hτ).ne').ne'
    have hm := (h1 τ hτ).aestronglyMeasurable
    refine (measure_lt_mul_enorm_le_wnorm_one _ A ht0
      (ENNReal.div_ne_top ENNReal.ofReal_ne_top two_ne_zero)).trans ?_
    rw [← lintegral_congr_ae (ae_enorm_indicator_eq hfG _), ← eLpNorm_one_eq_lintegral_eNorm hm]
    calc (A : ℝ≥0∞) * (ENNReal.ofReal τ / 2)⁻¹ *
          wnorm (T ({y | ENNReal.ofReal τ < G y}.indicator f)) 1 ν
        ≤ A * (ENNReal.ofReal τ / 2)⁻¹ *
          (C₁ * eLpNorm ({y | ENNReal.ofReal τ < G y}.indicator f) 1 μ) := by
          gcongr
          exact (h₁ _ (h1 τ hτ)).2
      _ = _ := by ring
  · refine (lintegral_mul_enorm_sq_le_of_hasStrongType h₂ A (h2 τ)).trans (le_of_eq ?_)
    have he := lintegral_enorm_indicator_rpow_eq hfG {y | ENNReal.ofReal τ < G y}ᶜ 2
    simp only [ENNReal.rpow_two] at he
    rw [he]

/-- **Marcinkiewicz interpolation between weak type `(1,1)` and strong type `(2,2)`, in the terms
of the Carleson project**: let `μ` be s-finite, `1 < p < 2`, and let `T` map functions in
`L_p(μ)` to almost everywhere strongly measurable functions, be almost everywhere subadditive
with constant `A` on `L_1(μ) ∪ L_2(μ)`, of weak type `(1,1)` with constant `C₁` and of strong
type `(2,2)` with constant `C₂`. Then `T` has strong type `(p, p)` with constant
`marcinkiewiczNormConst p A C₁ C₂ = (p (2 A C₁/(p - 1) + 4 A² C₂²/(2 - p)))^(1/p)`. Since strong
type `(2,2)` implies weak type `(2,2)` (`MeasureTheory.HasStrongType.hasWeakType`), the Carleson
project's `exists_hasStrongType_real_interpolation` with `(p₀, q₀) = (1, 1)`,
`(p₁, q₁) = (2, 2)` gives strong type `(p,p)` for `A ≥ 1` and positive finite constants; here
the layer cake argument gives it on s-finite measure spaces for every `A ≥ 0` and
`C₁, C₂ ∈ [0, ∞]`, with this constant. -/
theorem hasStrongType_of_hasWeakType_one_of_hasStrongType_two [SFinite μ] {ε₁ ε₂ : Type*}
    [TopologicalSpace ε₁] [ESeminormedAddMonoid ε₁] [TopologicalSpace ε₂] [ContinuousENorm ε₂]
    {T : (α → ε₁) → (α' → ε₂)} {p : ℝ≥0∞} {A : ℝ≥0} {C₁ C₂ : ℝ≥0∞} (hp1 : 1 < p)
    (hp2 : p < 2) (hmT : ∀ f, MemLp f p μ → AEStronglyMeasurable (T f) ν)
    (hT : AESubadditiveOn T (fun f => MemLp f 1 μ ∨ MemLp f 2 μ) A ν)
    (h₁ : HasWeakType T 1 1 μ ν C₁) (h₂ : HasStrongType T 2 2 μ ν C₂) :
    HasStrongType T p p μ ν (marcinkiewiczNormConst p A C₁ C₂) := by
  intro f hf
  have hp : p ≠ ∞ := ne_top_of_lt hp2
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
  have hTf := hmT f hf
  refine ⟨hTf, ?_⟩
  refine eLpNorm_le_rpow_mul_of_lintegral_enorm_le hp0 hp hTf hf.aestronglyMeasurable ?_
  exact lintegral_enorm_rpow_le_of_hasWeakType_of_hasStrongType
    (ENNReal.one_lt_toReal hp1 hp) (ENNReal.toReal_lt_of_lt_ofReal (by rwa [ENNReal.ofReal_ofNat]))
    hT h₁ h₂ hf.aestronglyMeasurable
    ((eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top hp0 hp hf.aestronglyMeasurable).1 hf).ne hTf

end MeasureTheory
