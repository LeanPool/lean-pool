/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.D4
public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.FejerRiesz

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Daubechies masks of every order

For every `N ≥ 1` there is a Daubechies mask of order `N` (`Daubechies.exists_mask`), so
`Nonempty (Mask N) ↔ 1 ≤ N` (`Daubechies.nonempty_mask_iff`). The polynomial factor `L` of the
mask comes from the Fejér–Riesz theorem (`Polynomial.fejer_riesz_outer`), applied to the
Daubechies polynomial in the variable `cos θ`,

`Q_N(t) = P_N((1 - t)/2)` (`Daubechies.daubCosPoly`).

Since `(1 - cos θ)/2 = sin²(θ/2)`, `Q_N(cos 2πξ) = P_N(sin²(πξ)) = P(ξ)`
(`Daubechies.eval_daubCosPoly_cos_two_pi_mul`). For `t ∈ [-1, 1]` the point `(1 - t)/2` lies in
`[0, 1]`, where `P_N ≥ 1`, so `Q_N > 0` on `[-1, 1]` (`Daubechies.eval_daubCosPoly_pos`), and
`deg Q_N ≤ N - 1` (`Daubechies.natDegree_daubCosPoly_le`). The Fejér–Riesz theorem gives a real
polynomial `L` with `deg L ≤ N - 1`, `L(1) > 0`, no zeros in the closed unit disk, and
`|L(e^{iθ})|² = Q_N(cos θ)` for all `θ ∈ ℝ`. At `θ = -2πξ` this is the mask identity
`|L(e^(-2πiξ))|² = P(ξ)`, and at `θ = 0` it reads `L(1)² = Q_N(1) = P_N(0) = 1`, so `L(1) = 1`
(`Daubechies.Mask.ofNormSqCos`).

The mask chosen in this way is `Daubechies.daubMask`; its polynomial factor has no zeros in the
closed unit disk (`Daubechies.aeval_daubMask_L_ne_zero`). For `N = 2` this property singles out
D4: the polynomial factor of a mask of order `2` is `L(z) = α + βz` with `α + β = 1` and
`(α - β)² = 3` (`Daubechies.Mask.exists_L_eq_of_two`), and of the two solutions only
`α = (1 + √3)/2`, `β = (1 - √3)/2` has its root `2 + √3` outside the disk
(`Daubechies.eq_d4_iff_aeval_ne_zero`). Hence the Fejér–Riesz construction reproduces D4
(`Daubechies.daubMask_two`).
-/

@[expose] public section

open Polynomial
open scoped Real

namespace Daubechies

/-! ### The Daubechies polynomial in the variable `cos θ` -/

/-- **The Daubechies polynomial in the variable `cos θ`**: `Q_N(t) = P_N((1 - t)/2)`, with the
Daubechies polynomial `P_N` (`Daubechies.daubPoly`). Since `(1 - cos θ)/2 = sin²(θ/2)`, it
satisfies `Q_N(cos θ) = P_N(sin²(θ/2))` (`Daubechies.eval_daubCosPoly_cos`), in particular
`Q_N(cos 2πξ) = P(ξ)` (`Daubechies.eval_daubCosPoly_cos_two_pi_mul`). -/
noncomputable def daubCosPoly (N : ℕ) : ℝ[X] := (daubPoly N).comp (C (1 / 2 : ℝ) * (1 - X))

/-- The value of `Q_N` at a real number `t`: `Q_N(t) = P_N((1 - t)/2)`. -/
theorem eval_daubCosPoly (N : ℕ) (t : ℝ) :
    (daubCosPoly N).eval t = (daubPoly N).eval ((1 - t) / 2) := by
  rw [daubCosPoly, eval_comp]
  congr 1
  simp only [eval_mul, eval_C, eval_sub, eval_one, eval_X]
  ring

/-- `Q_N` has degree at most `N - 1`, the degree bound of `P_N`: substituting the linear
polynomial `(1 - X)/2` does not raise the degree (Mathlib's `Polynomial.natDegree_comp_le`). -/
theorem natDegree_daubCosPoly_le (N : ℕ) : (daubCosPoly N).natDegree ≤ N - 1 := by
  have h : (C (1 / 2 : ℝ) * (1 - X)).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans (by compute_degree)
  calc (daubCosPoly N).natDegree
      ≤ (daubPoly N).natDegree * (C (1 / 2 : ℝ) * (1 - X)).natDegree := natDegree_comp_le
    _ ≤ (N - 1) * 1 := Nat.mul_le_mul (natDegree_daubPoly_le N) h
    _ = N - 1 := mul_one _

/-- `Q_N(t) ≥ 1` for `t ≤ 1` and `N ≥ 1`: then `(1 - t)/2 ≥ 0`, where `P_N ≥ 1`
(`Daubechies.one_le_eval_daubPoly`). -/
theorem one_le_eval_daubCosPoly {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : t ≤ 1) :
    1 ≤ (daubCosPoly N).eval t := by
  rw [eval_daubCosPoly]
  exact one_le_eval_daubPoly hN (by linarith)

/-- `Q_N(t) > 0` for every `t ∈ [-1, 1]` and `N ≥ 1` (`Daubechies.one_le_eval_daubCosPoly`),
the hypothesis of the Fejér–Riesz theorem. -/
theorem eval_daubCosPoly_pos {N : ℕ} (hN : 1 ≤ N) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 < (daubCosPoly N).eval t := fun _ ht =>
  one_pos.trans_le (one_le_eval_daubCosPoly hN ht.2)

/-- `Q_N(1) = P_N(0) = 1` for `N ≥ 1`. -/
theorem eval_one_daubCosPoly {N : ℕ} (hN : 1 ≤ N) : (daubCosPoly N).eval 1 = 1 := by
  rw [eval_daubCosPoly, sub_self, zero_div, eval_zero_daubPoly hN]

/-- **`Q_N` at the cosines**: `Q_N(cos θ) = P_N(sin²(θ/2))` for every `θ ∈ ℝ`, since
`cos θ = 1 - 2 sin²(θ/2)` (Mathlib's `Real.cos_two_mul_eq_one_sub`). -/
theorem eval_daubCosPoly_cos (N : ℕ) (θ : ℝ) :
    (daubCosPoly N).eval (Real.cos θ) = (daubPoly N).eval (Real.sin (θ / 2) ^ 2) := by
  have h := Real.cos_two_mul_eq_one_sub (θ / 2)
  rw [mul_div_cancel₀ θ two_ne_zero] at h
  rw [eval_daubCosPoly, h]
  congr 1
  ring

/-- `Q_N(cos 2πξ) = P_N(sin²(πξ)) = P(ξ)` for every `ξ ∈ ℝ`, with the trigonometric Daubechies
polynomial `P` (`Daubechies.daubFun`). -/
theorem eval_daubCosPoly_cos_two_pi_mul (N : ℕ) (ξ : ℝ) :
    (daubCosPoly N).eval (Real.cos (2 * π * ξ)) = daubFun N ξ := by
  rw [eval_daubCosPoly_cos, daubFun, show 2 * π * ξ / 2 = π * ξ by ring]

/-! ### Masks from the Fejér–Riesz theorem -/

/-- **Normalisation at `1`.** For `N ≥ 1`, a real polynomial `L` with `L(1) > 0` and
`|L(e^{iθ})|² = Q_N(cos θ)` for all `θ ∈ ℝ` has `L(1) = 1`: at `θ = 0` the identity reads
`L(1)² = Q_N(1) = 1` (`Polynomial.eval_one_sq_of_norm_aeval_exp_sq`). -/
theorem eval_one_eq_one_of_norm_aeval_exp_sq {N : ℕ} (hN : 1 ≤ N) {L : ℝ[X]}
    (hpos : 0 < L.eval 1)
    (hL : ∀ θ : ℝ, ‖aeval (Complex.exp ((θ : ℂ) * Complex.I)) L‖ ^ 2 =
      (daubCosPoly N).eval (Real.cos θ)) :
    L.eval 1 = 1 := by
  have h := eval_one_sq_of_norm_aeval_exp_sq hL
  rw [eval_one_daubCosPoly hN] at h
  nlinarith

/-- **From the cosine form to the mask form.** If `|L(e^{iθ})|² = Q_N(cos θ)` for all `θ ∈ ℝ`,
then `|L(e^(-2πiξ))|² = P(ξ) = P_N(sin²(πξ))` for all `ξ ∈ ℝ`: for `θ = -2πξ` the point
`e^{iθ}` is `e^(-2πiξ)` (`Daubechies.expFreq`), and `Q_N(cos(-2πξ)) = Q_N(cos 2πξ) = P(ξ)`
(`Daubechies.eval_daubCosPoly_cos_two_pi_mul`). -/
theorem normSq_aeval_expFreq_of_norm_aeval_exp_sq {N : ℕ} {L : ℝ[X]}
    (hL : ∀ θ : ℝ, ‖aeval (Complex.exp ((θ : ℂ) * Complex.I)) L‖ ^ 2 =
      (daubCosPoly N).eval (Real.cos θ)) (ξ : ℝ) :
    ‖aeval (expFreq ξ) L‖ ^ 2 = daubFun N ξ := by
  rw [expFreq, hL, Real.cos_neg, eval_daubCosPoly_cos_two_pi_mul]

/-- **A mask from the cosine form.** A real polynomial `L` with `deg L < N`, `L(1) > 0` and
`|L(e^{iθ})|² = Q_N(cos θ)` for all `θ ∈ ℝ` is the polynomial factor of a Daubechies mask of
order `N`: `L(1) = 1` by `Daubechies.eval_one_eq_one_of_norm_aeval_exp_sq` (here `N ≥ 1`, since
`0 ≤ deg L < N`), and `|L(e^(-2πiξ))|² = P(ξ)` by
`Daubechies.normSq_aeval_expFreq_of_norm_aeval_exp_sq`. -/
def Mask.ofNormSqCos {N : ℕ} (L : ℝ[X]) (hdeg : L.natDegree < N) (hpos : 0 < L.eval 1)
    (hL : ∀ θ : ℝ, ‖aeval (Complex.exp ((θ : ℂ) * Complex.I)) L‖ ^ 2 =
      (daubCosPoly N).eval (Real.cos θ)) : Mask N where
  L := L
  natDegree_L_lt := hdeg
  eval_L_one := eval_one_eq_one_of_norm_aeval_exp_sq (by omega) hpos hL
  normSq_L := normSq_aeval_expFreq_of_norm_aeval_exp_sq hL

/-! ### Existence -/

/-- **Existence of outer Daubechies masks.** For every `N ≥ 1` there is a Daubechies mask of
order `N` whose polynomial factor `L` has no zeros in the closed unit disk. Apply the
Fejér–Riesz theorem with an outer factor (`Polynomial.fejer_riesz_outer`) to `Q_N`, which is
positive on `[-1, 1]` (`Daubechies.eval_daubCosPoly_pos`) and of degree `≤ N - 1`
(`Daubechies.natDegree_daubCosPoly_le`): it gives `L` with `deg L ≤ N - 1`, `L(1) > 0`, no
zeros in the closed unit disk and `|L(e^{iθ})|² = Q_N(cos θ)`, a mask by
`Daubechies.Mask.ofNormSqCos`. -/
theorem exists_mask_outer {N : ℕ} (hN : 1 ≤ N) :
    ∃ m : Mask N, ∀ z : ℂ, ‖z‖ ≤ 1 → aeval z m.L ≠ 0 := by
  obtain ⟨L, hdeg, hpos, hne, hL⟩ := fejer_riesz_outer (eval_daubCosPoly_pos hN)
  have hlt : L.natDegree < N := by
    have := natDegree_daubCosPoly_le N
    omega
  exact ⟨Mask.ofNormSqCos L hlt hpos hL, hne⟩

/-- **Existence of Daubechies masks of every order** `N ≥ 1` (`Daubechies.exists_mask_outer`). -/
theorem exists_mask {N : ℕ} (hN : 1 ≤ N) : Nonempty (Mask N) := by
  obtain ⟨m, -⟩ := exists_mask_outer hN
  exact ⟨m⟩

/-- There is a Daubechies mask of order `N` exactly when `N ≥ 1` (`Daubechies.exists_mask`,
`Daubechies.Mask.one_le`). -/
theorem nonempty_mask_iff {N : ℕ} : Nonempty (Mask N) ↔ 1 ≤ N :=
  ⟨fun ⟨m⟩ => m.one_le, exists_mask⟩

/-- **The Daubechies mask of order `N`**, for `N ≥ 1`: a mask chosen among those whose
polynomial factor `L` has no zeros in the closed unit disk (`Daubechies.exists_mask_outer`,
`Daubechies.aeval_daubMask_L_ne_zero`), the minimum-phase choice of signal processing. For
`N = 2` it is the mask D4 (`Daubechies.daubMask_two`). -/
noncomputable def daubMask {N : ℕ} (hN : 1 ≤ N) : Mask N := (exists_mask_outer hN).choose

/-- The polynomial factor of the Daubechies mask `Daubechies.daubMask` has no zeros in the
closed unit disk: `L(z) ≠ 0` for every `z ∈ ℂ` with `|z| ≤ 1`. -/
theorem aeval_daubMask_L_ne_zero {N : ℕ} (hN : 1 ≤ N) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    aeval z (daubMask hN).L ≠ 0 :=
  (exists_mask_outer hN).choose_spec z hz

/-! ### Order `2`: the mask D4 -/

/-- Two masks of the same order with the same polynomial factor `L` are equal: the other fields
of `Daubechies.Mask` are properties of `L`. -/
@[ext]
theorem Mask.ext {N : ℕ} {m₁ m₂ : Mask N} (h : m₁.L = m₂.L) : m₁ = m₂ := by
  cases m₁
  cases m₂
  cases h
  rfl

/-- **The polynomial factor of D4 has no zeros in the closed unit disk**: the root of
`L(z) = (1 + √3)/2 + ((1 - √3)/2) z` is `z = (1 + √3)/(√3 - 1) = 2 + √3 > 1`. -/
theorem aeval_d4_L_ne_zero {z : ℂ} (hz : ‖z‖ ≤ 1) : aeval z d4.L ≠ 0 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h1 : 1 < √3 := by nlinarith [Real.sqrt_nonneg 3]
  rw [d4_L, map_add, map_mul, aeval_C, aeval_C, aeval_X, Complex.coe_algebraMap]
  intro h
  have h' : (((1 - √3) / 2 : ℝ) : ℂ) * z = -(((1 + √3) / 2 : ℝ) : ℂ) := by
    linear_combination h
  have hn := congrArg norm h'
  rw [norm_neg, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_neg (show (1 - √3) / 2 < 0 by linarith),
    abs_of_pos (show 0 < (1 + √3) / 2 by linarith)] at hn
  nlinarith [mul_nonneg (sub_nonneg.2 h1.le) (sub_nonneg.2 hz)]

/-- **The polynomial factor of a mask of order `2`** is `L(z) = α + βz` with real `α, β` such
that `α + β = 1` and `(α - β)² = 3`. The degree of `L` is `≤ 1` (Mathlib's
`Polynomial.exists_eq_X_add_C_of_natDegree_le_one`); `α + β = L(1) = 1`; and at `ξ = 1/2` the
mask identity `α² + β² + 2αβ cos(2πξ) = P(ξ) = 2 - cos(2πξ)` (`Daubechies.normSq_add_mul_expFreq`,
`Daubechies.daubFun_two_eq_two_sub_cos`) reads `(α - β)² = 3`. -/
theorem Mask.exists_L_eq_of_two (m : Mask 2) :
    ∃ α β : ℝ, m.L = C α + C β * X ∧ α + β = 1 ∧ (α - β) ^ 2 = 3 := by
  obtain ⟨β, α, hL⟩ := exists_eq_X_add_C_of_natDegree_le_one
    (show m.L.natDegree ≤ 1 by have := m.natDegree_L_lt; omega)
  rw [add_comm] at hL
  refine ⟨α, β, hL, ?_, ?_⟩
  · have h := m.eval_L_one
    rw [hL] at h
    simpa only [eval_add, eval_C, eval_mul, eval_X, mul_one] using h
  · have h := m.normSq_L (1 / 2)
    rw [hL, map_add, map_mul, aeval_C, aeval_C, aeval_X, Complex.coe_algebraMap,
      normSq_add_mul_expFreq, daubFun_two_eq_two_sub_cos,
      show 2 * π * (1 / 2) = π by ring, Real.cos_pi] at h
    linear_combination h

/-- **The outer mask of order `2` is D4.** A mask of order `2` whose polynomial factor has no
zeros in the closed unit disk is the mask D4. By `Daubechies.Mask.exists_L_eq_of_two`,
`L(z) = α + βz` with `α + β = 1` and `α - β = ±√3`. The sign `-` gives `α = (1 - √3)/2`,
`β = (1 + √3)/2`, and then `L` has the root `2 - √3` in the disk; the sign `+` gives the
coefficients `α = (1 + √3)/2`, `β = (1 - √3)/2` of D4. -/
theorem eq_d4_of_aeval_ne_zero (m : Mask 2) (hm : ∀ z : ℂ, ‖z‖ ≤ 1 → aeval z m.L ≠ 0) :
    m = d4 := by
  obtain ⟨α, β, hL, hsum, hsq⟩ := m.exists_L_eq_of_two
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h1 : 1 < √3 := by nlinarith [Real.sqrt_nonneg 3]
  have h2 : √3 < 2 := by nlinarith [Real.sqrt_nonneg 3]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hsq.trans h3.symm) with h | h
  · refine Mask.ext ?_
    rw [hL, d4_L, show α = (1 + √3) / 2 by linarith, show β = (1 - √3) / 2 by linarith]
  · refine absurd ?_ (hm ((2 - √3 : ℝ) : ℂ) ?_)
    · rw [hL, Complex.aeval_ofReal, Complex.ofReal_eq_zero]
      simp only [eval_add, eval_C, eval_mul, eval_X]
      rw [show α = (1 - √3) / 2 by linarith, show β = (1 + √3) / 2 by linarith]
      linear_combination (-1 / 2 : ℝ) * h3
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith

/-- **D4 is the outer mask of order `2`**: a mask of order `2` is D4 exactly when its polynomial
factor has no zeros in the closed unit disk (`Daubechies.eq_d4_of_aeval_ne_zero`,
`Daubechies.aeval_d4_L_ne_zero`). -/
theorem eq_d4_iff_aeval_ne_zero (m : Mask 2) :
    m = d4 ↔ ∀ z : ℂ, ‖z‖ ≤ 1 → aeval z m.L ≠ 0 := by
  refine ⟨?_, eq_d4_of_aeval_ne_zero m⟩
  rintro rfl
  exact fun _ hz => aeval_d4_L_ne_zero hz

/-- **The Daubechies mask of order `2` is D4**: the mask chosen by the Fejér–Riesz construction
is the mask D4, with the polynomial factor `L(z) = (1 + √3)/2 + ((1 - √3)/2) z`
(`Daubechies.eq_d4_of_aeval_ne_zero`). -/
theorem daubMask_two (h : 1 ≤ 2) : daubMask h = d4 :=
  eq_d4_of_aeval_ne_zero _ fun _ hz => aeval_daubMask_L_ne_zero h hz

end Daubechies
