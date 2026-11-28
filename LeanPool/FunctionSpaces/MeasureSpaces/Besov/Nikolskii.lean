/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.MeasureSpaces.Besov.ElementaryEmbeddings
public import LeanPool.FunctionSpaces.Analysis.Lp.Interpolation
public import LeanPool.FunctionSpaces.ApproximationSpaces.Lift

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The Nikolskii inequality of a scheme

A scheme of functions `S` has the **Nikolskii property of dimension `D`** for the measure `μ`
if for every `1 ≤ p ≤ ∞` there is `C` with

`‖a‖_∞ ≤ C n^(D/p) ‖a‖_p`   for all `a ∈ S n`, `n ≥ 1`

(`FunctionScheme.HasNikolskii`), a hypothesis on the scheme.  For trigonometric polynomials of
degree `< n` on `𝕋^d` it holds with `D = d` (`Torus.trigScheme_hasNikolskii`,
`Torus.hasNikolskii_fourierEigenbasis`); these torus instances are the ones proved in this
library.  The property is stated against the sup norm only; the general
**Nikolskii inequality**

`‖a‖_r ≤ C' n^(D (1/p - 1/r)) ‖a‖_p`,   `p ≤ r`

follows by interpolation, `‖a‖_r ≤ ‖a‖_∞^(1 - p/r) ‖a‖_p^(p/r)`
(`HasNikolskii.eLpNorm_le`).  The exponent `D (1/p - 1/r)` is `nikolskiiExponent D p r`; for
`D > 0`, `1 ≤ p < ∞` and `r > 0` it is positive iff `p < r` and nonnegative iff `p ≤ r`
(`nikolskiiExponent_pos`, `lt_of_nikolskiiExponent_pos`, `le_of_nikolskiiExponent_nonneg`).
With `θ = p₀/p₁` and `s₀ - s₁ = D(1/p₀ - 1/p₁)`, `θ s₀ + (1 - θ)(s₀ - D/p₀) = s₁`
(`nikolskiiExponent_interp_eq`). For the Gagliardo–Nirenberg–Sobolev inequality,
`D(1/p - 1/r) = 1` with `D ≥ 0` means `p < ∞` and `1/r = 1/p - 1/D`
(`toReal_inv_eq_of_nikolskiiExponent_eq_one`), which follows from `1/r + 1/n = 1/p` for `D = n`
(`nikolskiiExponent_eq_one_of_inv_add_inv`), and `n(1 - 1/r) = m ≥ 2` passes through the
conjugate exponent `n/(n - 1)` (`nikolskiiExponent_conjExponent_of_eq`).

In the language of `ApproximationSpaces.Lift` this is a lifting bound for the inclusion
`L_r ↪ L_p` and the scheme in `L_p` (`HasNikolskii.liftBound`): the approximant `a` in `L_p` is
the inclusion of the same function in `L_r`, of norm at most `C' n^(D(1/p - 1/r)) ‖a‖_p`.

The norms are written with `eLpNorm`, so that the hypothesis does not need an `L_p` space, and
hence no instance `Fact (1 ≤ p)`, for every `p` at once.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BoundedContinuousFunction

/-- The **Nikolskii exponent** `D (1/p - 1/r)`.  With `1/∞ = 0` (in Lean `∞.toReal = 0` and
`0⁻¹ = 0`) it is `D/p` for `r = ∞`. -/
noncomputable def nikolskiiExponent (D : ℝ) (p r : ℝ≥0∞) : ℝ := D * (p.toReal⁻¹ - r.toReal⁻¹)

/-- `D(1/p - 1/r) ≥ 0` for `D ≥ 0` and `1 ≤ p ≤ r`. -/
theorem nikolskiiExponent_nonneg {D : ℝ} (hD : 0 ≤ D) {p r : ℝ≥0∞} (hp : 1 ≤ p) (hpr : p ≤ r) :
    0 ≤ nikolskiiExponent D p r := by
  unfold nikolskiiExponent
  refine mul_nonneg hD (sub_nonneg.2 ?_)
  rcases eq_or_ne r ∞ with rfl | hr
  · simp
  have hp' : p ≠ ∞ := ne_top_of_le_ne_top hr hpr
  exact inv_anti₀ (ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp')
    (ENNReal.toReal_mono hr hpr)

/-- A natural number `m` above the Nikolskii exponent is at least `1`: for `D ≥ 0`,
`1 ≤ p ≤ r` and `m ∈ ℕ` with `m > D(1/p - 1/r)`, `m ≥ 1`, since the exponent is nonnegative
(`nikolskiiExponent_nonneg`). -/
theorem one_le_of_nikolskiiExponent_lt {D : ℝ} (hD : 0 ≤ D) {p r : ℝ≥0∞} (hp : 1 ≤ p)
    (hpr : p ≤ r) {m : ℕ} (hm : nikolskiiExponent D p r < m) : 1 ≤ m :=
  Nat.one_le_iff_ne_zero.2 (Nat.cast_pos.1 ((nikolskiiExponent_nonneg hD hp hpr).trans_lt hm)).ne'

/-- **The Nikolskii exponent is positive** for `D > 0` and `1 ≤ p < r ≤ ∞`, since then
`1/r < 1/p`. -/
theorem nikolskiiExponent_pos {D : ℝ} (hD : 0 < D) {p r : ℝ≥0∞} (hp : 1 ≤ p) (hpr : p < r) :
    0 < nikolskiiExponent D p r := by
  unfold nikolskiiExponent
  refine mul_pos hD (sub_pos.2 ?_)
  have hp0 : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' (hpr.trans_le le_top).ne
  rcases eq_or_ne r ∞ with rfl | hr
  · simpa using hp0
  exact inv_strictAnti₀ hp0 (ENNReal.toReal_strict_mono hr hpr)

/-- **A positive Nikolskii exponent forces `p < r`**: for `D ≥ 0`, `p < ∞` and `r > 0`, if
`D(1/p - 1/r) > 0`, then `p < r`; for `r ≤ p` the exponent is `≤ 0`. -/
theorem lt_of_nikolskiiExponent_pos {D : ℝ} (hD : 0 ≤ D) {p r : ℝ≥0∞} (hp : p ≠ ∞) (hr : 0 < r)
    (h : 0 < nikolskiiExponent D p r) : p < r := by
  by_contra hrp
  rw [not_lt] at hrp
  have hr' : r ≠ ∞ := ne_top_of_le_ne_top hp hrp
  have hle : p.toReal⁻¹ ≤ r.toReal⁻¹ :=
    inv_anti₀ (ENNReal.toReal_pos hr.ne' hr') (ENNReal.toReal_mono hp hrp)
  unfold nikolskiiExponent at h
  nlinarith

/-- **A nonnegative Nikolskii exponent forces `p ≤ r`**: for `D > 0`, `p < ∞` and `r > 0`, if
`D(1/p - 1/r) ≥ 0`, then `p ≤ r`; for `r < p` the exponent is `< 0`. -/
theorem le_of_nikolskiiExponent_nonneg {D : ℝ} (hD : 0 < D) {p r : ℝ≥0∞} (hp : p ≠ ∞)
    (hr : 0 < r) (h : 0 ≤ nikolskiiExponent D p r) : p ≤ r := by
  by_contra hrp
  rw [not_le] at hrp
  have hr' : r ≠ ∞ := ne_top_of_lt hrp
  have hlt : p.toReal⁻¹ < r.toReal⁻¹ :=
    inv_strictAnti₀ (ENNReal.toReal_pos hr.ne' hr') (ENNReal.toReal_strict_mono hp hrp)
  unfold nikolskiiExponent at h
  nlinarith

/-- **The interpolation identity of the Nikolskii exponent**: for `0 < p₀ < ∞`, `θ = p₀/p₁` and
`s₀ - s₁ = D(1/p₀ - 1/p₁)`, `θ s₀ + (1 - θ)(s₀ - D/p₀) = s₁`, since `θ/p₀ = 1/p₁`. -/
theorem nikolskiiExponent_interp_eq {D s₀ s₁ : ℝ} {p₀ p₁ : ℝ≥0∞} (hp₀0 : p₀ ≠ 0) (hp₀ : p₀ ≠ ∞)
    (hs : s₀ - s₁ = nikolskiiExponent D p₀ p₁) :
    p₀.toReal / p₁.toReal * s₀ + (1 - p₀.toReal / p₁.toReal) * (s₀ - D / p₀.toReal) = s₁ := by
  have h0 : p₀.toReal ≠ 0 := (ENNReal.toReal_pos hp₀0 hp₀).ne'
  unfold nikolskiiExponent at hs
  rw [show s₁ = s₀ - D * (p₀.toReal⁻¹ - p₁.toReal⁻¹) by linarith]
  field_simp
  ring

/-- `α(D, p, ∞) = D/p`. -/
@[simp]
theorem nikolskiiExponent_top (D : ℝ) (p : ℝ≥0∞) : nikolskiiExponent D p ∞ = D * p.toReal⁻¹ := by
  simp [nikolskiiExponent]

/-- `α(D, p, p) = 0`. -/
@[simp]
theorem nikolskiiExponent_self (D : ℝ) (p : ℝ≥0∞) : nikolskiiExponent D p p = 0 := by
  simp [nikolskiiExponent]

/-- **The Nikolskii exponent `1`**: for `D ≥ 0`, `D(1/p - 1/r) = 1` forces `D > 0`, `p < ∞` and
`1/r = 1/p - 1/D`; for `p = ∞` the exponent is `-D/r ≤ 0`. -/
theorem toReal_inv_eq_of_nikolskiiExponent_eq_one {D : ℝ} (hD : 0 ≤ D) {p r : ℝ≥0∞}
    (hs : nikolskiiExponent D p r = 1) : 0 < D ∧ p ≠ ∞ ∧ r.toReal⁻¹ = p.toReal⁻¹ - D⁻¹ := by
  unfold nikolskiiExponent at hs
  have hD0 : D ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hs
    exact zero_ne_one hs
  refine ⟨lt_of_le_of_ne hD (Ne.symm hD0), fun hp => ?_, ?_⟩
  · rw [hp, ENNReal.toReal_top, inv_zero, zero_sub] at hs
    have : 0 ≤ r.toReal⁻¹ := inv_nonneg.2 ENNReal.toReal_nonneg
    nlinarith
  · have h : p.toReal⁻¹ - r.toReal⁻¹ = D⁻¹ := eq_inv_of_mul_eq_one_right hs
    linarith

/-- **The exponents in the form `1/r + 1/n = 1/p`**: for `n ∈ ℕ`, `1 ≤ p` and
`r⁻¹ + n⁻¹ = p⁻¹` in `[0, ∞]` (where `1/0 = ∞`), `p < ∞` and `n(1/p - 1/r) = 1`. -/
theorem nikolskiiExponent_eq_one_of_inv_add_inv {n : ℕ} {p r : ℝ≥0∞} (hp : 1 ≤ p)
    (hexp : r⁻¹ + (n : ℝ≥0∞)⁻¹ = p⁻¹) : p ≠ ∞ ∧ nikolskiiExponent n p r = 1 := by
  have hp1 : p⁻¹ ≤ 1 := ENNReal.inv_le_one.2 hp
  have hr0 : r⁻¹ ≠ ∞ := (le_self_add.trans (hexp.le.trans hp1)).trans_lt ENNReal.one_lt_top |>.ne
  have hn0 : (n : ℝ≥0∞)⁻¹ ≠ ∞ :=
    (le_add_self.trans (hexp.le.trans hp1)).trans_lt ENNReal.one_lt_top |>.ne
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hn0
  refine ⟨fun hpt => ?_, ?_⟩
  · rw [hpt, ENNReal.inv_top, add_eq_zero] at hexp
    exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n) hexp.2
  have h := congrArg ENNReal.toReal hexp
  rw [ENNReal.toReal_add hr0 hn0, ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_inv,
    ENNReal.toReal_natCast] at h
  unfold nikolskiiExponent
  rw [← h, add_sub_cancel_left, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn)]

/-- For `m ≥ 2`, `n(1 - 1/r) = m` forces `n > 1`, since `1/r ≥ 0`. -/
theorem one_lt_of_nikolskiiExponent_one_eq {n m : ℕ} (hm : 2 ≤ m) {r : ℝ≥0∞}
    (hs : nikolskiiExponent n 1 r = m) : 1 < n := by
  unfold nikolskiiExponent at hs
  rw [ENNReal.toReal_one, inv_one] at hs
  have ha : 0 ≤ r.toReal⁻¹ := inv_nonneg.2 ENNReal.toReal_nonneg
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h : (1 : ℝ) < n := by nlinarith
  exact_mod_cast h

/-- **The intermediate exponent `q = n/(n - 1)`**: for `m ≥ 2`, every `r ∈ [0, ∞]` with
`n(1 - 1/r) = m` and the conjugate exponent `q = n/(n - 1)` of `n` (Mathlib's
`ENNReal.conjExponent`), `1 < q < ∞`, `n(1 - 1/q) = 1` and `n(1/q - 1/r) = m - 1`: Hölder
conjugacy gives `1/q + 1/n = 1` (`nikolskiiExponent_eq_one_of_inv_add_inv`), and
`n > 1` (`one_lt_of_nikolskiiExponent_one_eq`). -/
theorem nikolskiiExponent_conjExponent_of_eq {n m : ℕ} (hm : 2 ≤ m) {r : ℝ≥0∞}
    (hs : nikolskiiExponent n 1 r = m) :
    1 < ENNReal.conjExponent n ∧ ENNReal.conjExponent n ≠ ∞ ∧
      nikolskiiExponent n 1 (ENNReal.conjExponent n) = 1 ∧
      nikolskiiExponent n (ENNReal.conjExponent n) r = ((m - 1 : ℕ) : ℝ) := by
  have hn : (1 : ℝ≥0∞) < n := by exact_mod_cast one_lt_of_nikolskiiExponent_one_eq hm hs
  have : (n : ℝ≥0∞).HolderConjugate (ENNReal.conjExponent n) := .conjExponent hn.le
  have h1 : nikolskiiExponent n 1 (ENNReal.conjExponent n) = 1 :=
    (nikolskiiExponent_eq_one_of_inv_add_inv le_rfl (by
      rw [inv_one, add_comm]
      exact ENNReal.HolderConjugate.inv_add_inv_eq_one _ _)).2
  refine ⟨(ENNReal.HolderConjugate.lt_top_iff_one_lt _ _).1 (ENNReal.natCast_lt_top n),
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt _ _).2 hn).ne, h1, ?_⟩
  obtain ⟨-, -, hq⟩ := toReal_inv_eq_of_nikolskiiExponent_eq_one (Nat.cast_nonneg n) h1
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (one_lt_of_nikolskiiExponent_one_eq hm hs).ne_bot
  unfold nikolskiiExponent at hs ⊢
  rw [ENNReal.toReal_one, inv_one] at hs hq
  rw [hq, Nat.cast_sub (by omega), Nat.cast_one, ← hs]
  field_simp
  ring

namespace FunctionScheme

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]

/-- The **Nikolskii property of dimension `D`**: for every `1 ≤ p ≤ ∞`,
`‖a‖_∞ ≤ C n^(D/p) ‖a‖_p` for all approximants `a ∈ S n`, `n ≥ 1`. A hypothesis on the scheme;
the torus has it (`Torus.trigScheme_hasNikolskii`). -/
structure HasNikolskii (S : FunctionScheme Ω) (μ : Measure Ω) (D : ℝ) : Prop where
  exists_const : ∀ p : ℝ≥0∞, 1 ≤ p → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ∀ a ∈ S n,
    ‖a‖ ≤ C * (n : ℝ) ^ (D * p.toReal⁻¹) * (eLpNorm a p μ).toReal

variable {S : FunctionScheme Ω} {μ : Measure Ω} [IsFiniteMeasure μ] {D : ℝ}

omit [IsFiniteMeasure μ] in
/-- The `L_∞` norm of a bounded continuous function is at most its sup norm. -/
theorem toReal_eLpNorm_top_le_norm (a : Ω →ᵇ ℂ) :
    (eLpNorm a ∞ μ).toReal ≤ ‖a‖ := by
  have : eLpNorm a ∞ μ ≤ ‖a‖ₑ := by
    rw [eLpNorm_exponent_top a.continuous.aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_eNorm_bound (Filter.Eventually.of_forall fun x => by
      rw [← ofReal_norm, ← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (a.norm_coe_le_norm x))
  rw [← toReal_eNorm]
  exact ENNReal.toReal_mono eNorm_ne_top this

/-- **The Nikolskii inequality**: under the Nikolskii property of dimension `D ≥ 0`, for
`1 ≤ p ≤ r ≤ ∞` there is `C` with `‖a‖_r ≤ C n^(D(1/p - 1/r)) ‖a‖_p` for all `a ∈ S n`,
`n ≥ 1`. -/
theorem HasNikolskii.eLpNorm_le (h : S.HasNikolskii μ D) {p r : ℝ≥0∞} (hp : 1 ≤ p)
    (hpr : p ≤ r) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ∀ a ∈ S n,
      (eLpNorm a r μ).toReal ≤ C * (n : ℝ) ^ nikolskiiExponent D p r * (eLpNorm a p μ).toReal := by
  obtain ⟨C, hC, hCa⟩ := h.exists_const p hp
  rcases eq_or_ne r ∞ with rfl | hr
  · refine ⟨C, hC, fun n hn a ha => ?_⟩
    rw [nikolskiiExponent_top]
    exact (toReal_eLpNorm_top_le_norm a).trans (hCa n hn a ha)
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hp' : p ≠ ∞ := ne_top_of_le_ne_top hr hpr
  have hr0 : r ≠ 0 := (zero_lt_one.trans_le (hp.trans hpr)).ne'
  have hpp : 0 < p.toReal := ENNReal.toReal_pos hp0 hp'
  have hrr : 0 < r.toReal := ENNReal.toReal_pos hr0 hr
  set θ := p.toReal / r.toReal
  have hθ1 : 0 ≤ 1 - θ := ENNReal.one_sub_toReal_div_nonneg hpr
  refine ⟨C ^ (1 - θ), Real.rpow_nonneg hC _, fun n hn a ha => ?_⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set Np := (eLpNorm a p μ).toReal
  have hNp : 0 ≤ Np := ENNReal.toReal_nonneg
  have hint := toReal_eLpNorm_le_rpow_mul (μ := μ) a.continuous.aestronglyMeasurable
    (norm_nonneg a) (Filter.Eventually.of_forall a.norm_coe_le_norm) hp0 hpr hr
  calc (eLpNorm a r μ).toReal ≤ ‖a‖ ^ (1 - θ) * Np ^ θ := hint
    _ ≤ (C * (n : ℝ) ^ (D * p.toReal⁻¹) * Np) ^ (1 - θ) * Np ^ θ := by
        gcongr; exact hCa n hn a ha
    _ = C ^ (1 - θ) * (n : ℝ) ^ nikolskiiExponent D p r * (Np ^ (1 - θ) * Np ^ θ) := by
        rw [Real.mul_rpow (by positivity) hNp, Real.mul_rpow hC (by positivity),
          ← Real.rpow_mul hn0]
        have : D * p.toReal⁻¹ * (1 - θ) = nikolskiiExponent D p r := by
          simp only [nikolskiiExponent, θ]; field_simp
        rw [this]; ring
    _ = C ^ (1 - θ) * (n : ℝ) ^ nikolskiiExponent D p r * Np := by
        rw [← Real.rpow_add' hNp (by norm_num), sub_add_cancel, Real.rpow_one]

/-- **The Nikolskii inequality as a lifting bound** for the inclusion `L_r ↪ L_p`: every
approximant of the scheme in `L_p` is the inclusion of an approximant in `L_r` whose norm is at
most `C n^(D(1/p - 1/r))` times its `L_p` norm. -/
theorem HasNikolskii.liftBound (h : S.HasNikolskii μ D) {p r : ℝ≥0∞} [Fact (1 ≤ p)]
    [Fact (1 ≤ r)] (hpr : p ≤ r) : ∃ C : ℝ, 0 ≤ C ∧
      ApproximationScheme.LiftBound (Lp.inclusionOfExponentLe (E := ℂ) (𝕜 := ℝ) μ hpr)
        (S.toLp μ p) (nikolskiiExponent D p r) C := by
  obtain ⟨C, hC, hCa⟩ := h.eLpNorm_le (Fact.out : 1 ≤ p) hpr
  refine ⟨C, hC, fun n hn g hg => ?_⟩
  obtain ⟨a, ha, rfl⟩ := hg
  refine ⟨BoundedContinuousFunction.toLp (E := ℂ) r μ ℝ a,
    BoundedContinuousFunction.inclusionOfExponentLe_toLp hpr a, ?_⟩
  change ‖BoundedContinuousFunction.toLp (E := ℂ) r μ ℝ a‖ ≤
    C * (n : ℝ) ^ nikolskiiExponent D p r * ‖BoundedContinuousFunction.toLp (E := ℂ) p μ ℝ a‖
  rw [BoundedContinuousFunction.norm_toLp_eq_toReal_eLpNorm,
    BoundedContinuousFunction.norm_toLp_eq_toReal_eLpNorm]
  exact hCa n hn a ha

end FunctionScheme
