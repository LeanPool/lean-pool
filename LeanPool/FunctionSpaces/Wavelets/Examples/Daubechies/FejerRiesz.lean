/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The Fejér–Riesz theorem

For a real polynomial `Q` that is positive on `[-1, 1]`, `Q(cos θ)` is a squared modulus on the
unit circle (`Polynomial.fejer_riesz`): there is a real polynomial `L` with `deg L ≤ deg Q`,
`L(1) > 0` and

`|L(e^{iθ})|² = Q(cos θ)` for all `θ ∈ ℝ`.

The `L` constructed here has no zeros in the closed unit disk (`Polynomial.fejer_riesz_outer`),
and the identity holds with `e^{-iθ}` as well (`Polynomial.forall_norm_aeval_exp_neg_sq_iff`,
`Polynomial.fejer_riesz_exp_neg`), the form used for the masks of the Daubechies wavelets. In
Lean the modulus is the norm `‖·‖` of `ℂ`, and `L(e^{iθ})` is
`Polynomial.aeval (Complex.exp (θ * I)) L`.

**The inverse of the Joukowsky map.** The Joukowsky map `a ↦ (a + a⁻¹)/2` takes `e^{iφ}` to
`cos φ`. For `t ∈ ℂ` outside `[-1, 1]` the equation `a² - 2ta + 1 = 0`, that is
`(a + a⁻¹)/2 = t`, has exactly one root `a(t)` with `|a(t)| < 1` (`Complex.joukowskyInv`): the
two roots have product `1`, and a root on the unit circle would give `t = Re a ∈ [-1, 1]`
(`Complex.exists_joukowsky_root`, `Complex.joukowsky_root_unique`). Uniqueness gives
`a(tBar) = conj (a(t))` (`Complex.joukowskyInv_conj`). On the unit circle the factor `cos θ - t` of
`Q` splits into two linear factors: for `z = e^{iθ}`,
`2 |a| |cos θ - t| = |1 - a z| |1 - ā z|` (`Complex.joukowsky_two_mul_norm_mul_norm_re_sub`).

**The proof.** Over `ℂ`, `Q(z) = c ∏_t (z - t)` with the leading coefficient `c` and the complex
roots `t` of `Q`, counted with multiplicity (`Polynomial.aeval_eq_mul_prod_aroots`). No root lies
in `[-1, 1]`, and the roots are invariant under conjugation (`Polynomial.map_conj_aroots`). The
product `L₀ = ∏_t (1 - a(t) X)` (`Polynomial.fejerRieszFactor`) has its roots `1/a(t)` outside
the closed unit disk (`Polynomial.eval_fejerRieszFactor_ne_zero`) and coefficients fixed by
conjugation, so it is a real polynomial (`Polynomial.exists_map_eq_of_map_conj_eq`). With
`∏_t |1 - ā(t) z| = ∏_t |1 - a(tBar) z| = ∏_t |1 - a(t) z|` the identity above gives
`Q(cos θ) = K |L₀(e^{iθ})|²` with `K = |c| / ∏_t 2|a(t)| > 0`
(`Polynomial.exists_eval_cos_eq_mul_norm_sq`). Finally `L = ±√K L₀`, the sign chosen such that
`L(1) > 0` (`Polynomial.exists_eval_one_pos_of_aeval_ne_zero`); here `L(1) ≠ 0` since `L` has no
zeros in the disk, and `L(1)² = Q(1)` (`Polynomial.eval_one_sq_of_norm_aeval_exp_sq`).

With the roots `1/a(t)` outside the disk, `Q(t) = 2 - t` (root `t = 2`, `a = 2 - √3`) gives
`L = ((1 + √3) + (1 - √3) X)/2`, the polynomial of the Daubechies wavelet D4.
-/

@[expose] public section

open Polynomial
open scoped ComplexConjugate

namespace Complex

/-- For a real polynomial `p` and `x ∈ ℝ`, evaluating `p` at the complex number `x` gives the
real number `p(x)`. This is Mathlib's `Polynomial.aeval_ofReal` for the coercion `ℝ → ℂ`;
Mathlib states it for every `RCLike` field with the coercion `RCLike.ofReal`, and the form
here, with the coercion of `ℂ`, is the one that `rw` matches in this file. -/
protected theorem aeval_ofReal (p : ℝ[X]) (x : ℝ) :
    aeval (x : ℂ) p = ((p.eval x : ℝ) : ℂ) :=
  Polynomial.aeval_ofReal p x

/-! ### The inverse of the Joukowsky map -/

/-- A root `a` of `a² - 2ta + 1 = 0` on the unit circle forces `t = Re a`: then `a⁻¹ = ā`, and
the equation says `2t = a + a⁻¹ = a + ā`. So `t` is real and lies in `[-1, 1]`. -/
theorem joukowsky_eq_re_of_norm_eq_one {a t : ℂ} (h : a ^ 2 - 2 * t * a + 1 = 0)
    (ha : ‖a‖ = 1) : t = (a.re : ℂ) := by
  have h1 : a * conj a = 1 := by
    rw [mul_conj, normSq_eq_norm_sq, ha]
    norm_num
  have h2 : a + conj a = 2 * (a.re : ℂ) := by
    rw [add_conj]
    push_cast
    ring
  linear_combination (-1 / 2 : ℂ) * conj a * h + (a / 2 - t) * h1 + (1 / 2 : ℂ) * h2

/-- **Existence of the root in the disk.** For `t ∈ ℂ` outside `[-1, 1]` (no real `r ∈ [-1, 1]`
equals `t`), the equation `a² - 2ta + 1 = 0` has a root with `|a| < 1`. Its two roots
`t ± s`, `s² = t² - 1`, have product `1`, and neither has modulus `1`
(`Complex.joukowsky_eq_re_of_norm_eq_one`), so one of them lies in the open unit disk. -/
theorem exists_joukowsky_root {t : ℂ} (ht : ∀ r ∈ Set.Icc (-1 : ℝ) 1, (r : ℂ) ≠ t) :
    ∃ a : ℂ, ‖a‖ < 1 ∧ a ^ 2 - 2 * t * a + 1 = 0 := by
  obtain ⟨s, hs⟩ := IsAlgClosed.isSquare (t ^ 2 - 1)
  have hne : ∀ a : ℂ, a ^ 2 - 2 * t * a + 1 = 0 → ‖a‖ ≠ 1 := fun a h ha => by
    refine ht a.re ⟨?_, ?_⟩ (joukowsky_eq_re_of_norm_eq_one h ha).symm
    · linarith [neg_abs_le a.re, abs_re_le_norm a]
    · linarith [le_abs_self a.re, abs_re_le_norm a]
  have h₁ : (t + s) ^ 2 - 2 * t * (t + s) + 1 = 0 := by linear_combination -hs
  have h₂ : (t - s) ^ 2 - 2 * t * (t - s) + 1 = 0 := by linear_combination -hs
  have hprod : ‖t + s‖ * ‖t - s‖ = 1 := by
    rw [← norm_mul]
    have : (t + s) * (t - s) = 1 := by linear_combination hs
    rw [this, norm_one]
  rcases lt_or_gt_of_ne (hne _ h₁) with h | h
  · exact ⟨t + s, h, h₁⟩
  · refine ⟨t - s, ?_, h₂⟩
    nlinarith [norm_nonneg (t - s)]

/-- **Uniqueness of the root in the disk.** The equation `a² - 2ta + 1 = 0` has at most one root
with `|a| < 1`: two different roots `a ≠ b` are the two roots, so `ab = 1`, which is impossible
for `|a|, |b| < 1`. -/
theorem joukowsky_root_unique {a b t : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1)
    (ha' : a ^ 2 - 2 * t * a + 1 = 0) (hb' : b ^ 2 - 2 * t * b + 1 = 0) : a = b := by
  by_contra hab
  have h1 : a + b - 2 * t = 0 := by
    have : (a - b) * (a + b - 2 * t) = 0 := by linear_combination ha' - hb'
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hab)
  have h2 : a * b = 1 := by linear_combination -ha' + a * h1
  have h3 : ‖a‖ * ‖b‖ = 1 := by rw [← norm_mul, h2, norm_one]
  nlinarith [norm_nonneg a, norm_nonneg b]

/-- A root of `a² - 2ta + 1 = 0` is nonzero. -/
theorem joukowsky_root_ne_zero {a t : ℂ} (h : a ^ 2 - 2 * t * a + 1 = 0) : a ≠ 0 := by
  rintro rfl
  norm_num at h

/-- If `a² - 2ta + 1 = 0`, then `ā² - 2 tBar ā + 1 = 0`: conjugation is a ring homomorphism. -/
theorem joukowsky_root_conj {a t : ℂ} (h : a ^ 2 - 2 * t * a + 1 = 0) :
    conj a ^ 2 - 2 * conj t * conj a + 1 = 0 := by
  have := congrArg conj h
  rw [map_add, map_sub, map_mul, map_mul, map_pow, map_ofNat, map_one, map_zero] at this
  exact this

open Classical in
/-- **The inverse of the Joukowsky map** `a ↦ (a + a⁻¹)/2` on the punctured open unit disk: for
`t ∈ ℂ` outside `[-1, 1]`, `joukowskyInv t` is the unique root `a` of `a² - 2ta + 1 = 0`, that is
of `(a + a⁻¹)/2 = t`, with `|a| < 1` (`Complex.exists_joukowsky_root`,
`Complex.joukowsky_root_unique`). For `t ∈ [-1, 1]` both roots lie on the unit circle, and the
value is `0`. -/
noncomputable def joukowskyInv (t : ℂ) : ℂ :=
  if h : ∃ a : ℂ, ‖a‖ < 1 ∧ a ^ 2 - 2 * t * a + 1 = 0 then h.choose else 0

/-- If `a² - 2ta + 1 = 0` has a root in the open unit disk, then `a = joukowskyInv t` is one:
`|a| < 1` and `a² - 2ta + 1 = 0`. -/
theorem joukowskyInv_spec {t : ℂ} (h : ∃ a : ℂ, ‖a‖ < 1 ∧ a ^ 2 - 2 * t * a + 1 = 0) :
    ‖joukowskyInv t‖ < 1 ∧ joukowskyInv t ^ 2 - 2 * t * joukowskyInv t + 1 = 0 := by
  rw [joukowskyInv, dite_eq_left h]
  exact h.choose_spec

/-- Every root `a` of `a² - 2ta + 1 = 0` with `|a| < 1` is `joukowskyInv t`. -/
theorem joukowskyInv_eq {a t : ℂ} (ha : ‖a‖ < 1) (h : a ^ 2 - 2 * t * a + 1 = 0) :
    joukowskyInv t = a :=
  have hspec := joukowskyInv_spec ⟨a, ha, h⟩
  joukowsky_root_unique hspec.1 ha hspec.2 h

/-- **The inverse of the Joukowsky map commutes with conjugation**, `a(tBar) = conj (a(t))`, for
every `t ∈ ℂ`: conjugation maps the roots of `a² - 2ta + 1` in the disk to those of
`a² - 2tBara + 1`, and the root in the disk is unique. -/
theorem joukowskyInv_conj (t : ℂ) : joukowskyInv (conj t) = conj (joukowskyInv t) := by
  by_cases h : ∃ a : ℂ, ‖a‖ < 1 ∧ a ^ 2 - 2 * t * a + 1 = 0
  · have hspec := joukowskyInv_spec h
    exact joukowskyInv_eq (by rw [norm_conj]; exact hspec.1) (joukowsky_root_conj hspec.2)
  · have h' : ¬ ∃ a : ℂ, ‖a‖ < 1 ∧ a ^ 2 - 2 * conj t * a + 1 = 0 := fun ⟨b, hb, hb'⟩ =>
      h ⟨conj b, by rw [norm_conj]; exact hb, by simpa using joukowsky_root_conj hb'⟩
    rw [joukowskyInv, dite_eq_right h', joukowskyInv, dite_eq_right h, map_zero]

/-- **The factorisation on the unit circle**, algebraic form: if `a² - 2ta + 1 = 0` and
`z zBar = 1`, then `2a (Re z - t) = -(1 - a z)(1 - a zBar)`, from `z + zBar = 2 Re z`. -/
theorem joukowsky_two_mul_mul_re_sub {a t z : ℂ} (h : a ^ 2 - 2 * t * a + 1 = 0)
    (hz : z * conj z = 1) : 2 * a * ((z.re : ℂ) - t) = -((1 - a * z) * (1 - a * conj z)) := by
  have h2 : z + conj z = 2 * (z.re : ℂ) := by
    rw [add_conj]
    push_cast
    ring
  linear_combination h + a ^ 2 * hz - a * h2

/-- **The factorisation on the unit circle.** If `a² - 2ta + 1 = 0` and `|z| = 1`, then
`2 |a| |Re z - t| = |1 - a z| |1 - ā z|`; for `z = e^{iθ}` the left side contains
`|cos θ - t|`. Here `|1 - a zBar| = |1 - ā z|` by conjugation. -/
theorem joukowsky_two_mul_norm_mul_norm_re_sub {a t z : ℂ} (h : a ^ 2 - 2 * t * a + 1 = 0)
    (hz : ‖z‖ = 1) : 2 * ‖a‖ * ‖(z.re : ℂ) - t‖ = ‖1 - a * z‖ * ‖1 - conj a * z‖ := by
  have hz' : z * conj z = 1 := by
    rw [mul_conj, normSq_eq_norm_sq, hz]
    norm_num
  have h1 : ‖1 - a * conj z‖ = ‖1 - conj a * z‖ := by
    rw [← norm_conj (1 - a * conj z), map_sub, map_one, map_mul, conj_conj]
  have h2 := congrArg norm (joukowsky_two_mul_mul_re_sub h hz')
  rw [norm_mul, norm_mul, norm_neg, norm_mul, h1, Complex.norm_two] at h2
  exact h2

end Complex

namespace Polynomial

/-! ### The complex roots of a real polynomial -/

/-- **The complex roots of a real polynomial are invariant under conjugation**, with
multiplicities: the multiset `tBar` over the roots `t` of `Q` is the multiset of roots of `Q`. -/
theorem map_conj_aroots (Q : ℝ[X]) : (Q.aroots ℂ).map conj = Q.aroots ℂ := by
  rw [aroots_def, roots_map_of_injective_of_card_eq_natDegree (RingHom.injective _)
    IsAlgClosed.card_roots_eq_natDegree, Polynomial.map_map]
  congr 2
  exact RingHom.ext fun r => by simp

/-- Conjugation can be dropped inside a function of the complex roots of a real polynomial:
the multisets `g(tBar)` and `g(t)` over the roots `t` of `Q` agree
(`Polynomial.map_conj_aroots`). -/
theorem map_comp_conj_aroots {M : Type*} (Q : ℝ[X]) (g : ℂ → M) :
    (Q.aroots ℂ).map (fun t => g (conj t)) = (Q.aroots ℂ).map g := by
  calc (Q.aroots ℂ).map (fun t => g (conj t)) = ((Q.aroots ℂ).map conj).map g :=
        (Multiset.map_map g conj _).symm
    _ = (Q.aroots ℂ).map g := by rw [map_conj_aroots]

/-- A real point `r` with `Q(r) ≠ 0` is no complex root of `Q`. -/
theorem ofReal_ne_of_mem_aroots {Q : ℝ[X]} {t : ℂ} (ht : t ∈ Q.aroots ℂ) {r : ℝ}
    (hr : Q.eval r ≠ 0) : (r : ℂ) ≠ t := by
  intro hrt
  have h0 := (mem_aroots.1 ht).2
  rw [← hrt, Complex.aeval_ofReal, Complex.ofReal_eq_zero] at h0
  exact hr h0

/-- **Factorisation over `ℂ`**: a real polynomial `Q` with leading coefficient `c` is, at every
`z ∈ ℂ`, the product `Q(z) = c ∏_t (z - t)` over its complex roots `t`, counted with
multiplicity (Mathlib's `C_leadingCoeff_mul_prod_multiset_X_sub_C`; `ℂ` is algebraically
closed). -/
theorem aeval_eq_mul_prod_aroots (Q : ℝ[X]) (z : ℂ) :
    aeval z Q = (Q.leadingCoeff : ℂ) * ((Q.aroots ℂ).map fun t => z - t).prod := by
  have h := congrArg (eval z) (C_leadingCoeff_mul_prod_multiset_X_sub_C
    (p := Q.map (algebraMap ℝ ℂ)) IsAlgClosed.card_roots_eq_natDegree)
  rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, eval_map_algebraMap,
    leadingCoeff_map] at h
  rw [← h]
  simp

/-- At a real point `x` with `Q(x) ≥ 0`, `Q(x) = |c| ∏_t |x - t|` with the leading coefficient
`c` and the complex roots `t` of `Q` (`Polynomial.aeval_eq_mul_prod_aroots`, moduli). -/
theorem eval_eq_abs_leadingCoeff_mul_prod_norm {Q : ℝ[X]} {x : ℝ} (hx : 0 ≤ Q.eval x) :
    Q.eval x = |Q.leadingCoeff| * ((Q.aroots ℂ).map fun t => ‖(x : ℂ) - t‖).prod := by
  have h := congrArg norm (aeval_eq_mul_prod_aroots Q x)
  rw [Complex.aeval_ofReal, norm_mul, Multiset.norm_prod, Multiset.map_map, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx] at h
  exact h

/-- If `Q > 0` on `[-1, 1]`, then each complex root `t` of `Q` lies outside `[-1, 1]`, so
`a = a(t)` (`Complex.joukowskyInv`) is a root of `a² - 2ta + 1 = 0` with `|a| < 1`. -/
theorem joukowskyInv_spec_of_mem_aroots {Q : ℝ[X]}
    (hQ : ∀ r ∈ Set.Icc (-1 : ℝ) 1, 0 < Q.eval r) {t : ℂ} (ht : t ∈ Q.aroots ℂ) :
    ‖Complex.joukowskyInv t‖ < 1 ∧
      Complex.joukowskyInv t ^ 2 - 2 * t * Complex.joukowskyInv t + 1 = 0 :=
  Complex.joukowskyInv_spec (Complex.exists_joukowsky_root fun r hr =>
    ofReal_ne_of_mem_aroots ht (hQ r hr).ne')

/-! ### The Fejér–Riesz factor -/

/-- **The Fejér–Riesz factor** of a real polynomial `Q`: the complex polynomial
`L₀ = ∏_t (1 - a(t) X)` over the complex roots `t` of `Q`, counted with multiplicity, with
`a(t) = Complex.joukowskyInv t` the root in the unit disk of `a² - 2ta + 1`. For `Q > 0` on
`[-1, 1]` its roots `1/a(t)` lie outside the closed unit disk. -/
noncomputable def fejerRieszFactor (Q : ℝ[X]) : ℂ[X] :=
  ((Q.aroots ℂ).map fun t => 1 - C (Complex.joukowskyInv t) * X).prod

/-- The Fejér–Riesz factor has degree at most `deg Q`: it has one factor of degree `≤ 1` for each
of the at most `deg Q` complex roots of `Q`. -/
theorem natDegree_fejerRieszFactor_le (Q : ℝ[X]) :
    (fejerRieszFactor Q).natDegree ≤ Q.natDegree := by
  refine (natDegree_multiset_prod_le _).trans ?_
  rw [Multiset.map_map]
  refine (Multiset.sum_le_card_nsmul _ 1 fun n hn => ?_).trans ?_
  · obtain ⟨t, -, rfl⟩ := Multiset.mem_map.1 hn
    simp only [Function.comp_apply]
    compute_degree
  · rw [Multiset.card_map, smul_eq_mul, mul_one]
    exact card_roots_map_le_natDegree Q

/-- **The Fejér–Riesz factor has coefficients fixed by conjugation**: conjugating the
coefficients replaces `a(t)` by `conj (a(t)) = a(tBar)` (`Complex.joukowskyInv_conj`), and the roots
`t` of `Q` are invariant under conjugation (`Polynomial.map_comp_conj_aroots`). -/
theorem map_conj_fejerRieszFactor (Q : ℝ[X]) :
    (fejerRieszFactor Q).map (starRingEnd ℂ) = fejerRieszFactor Q := by
  rw [fejerRieszFactor, Polynomial.map_multiset_prod, Multiset.map_map]
  have h : ∀ t : ℂ,
      (Polynomial.map (starRingEnd ℂ) ∘ fun t => 1 - C (Complex.joukowskyInv t) * X) t =
        1 - C (Complex.joukowskyInv (conj t)) * X := fun t => by
    simp [Complex.joukowskyInv_conj]
  rw [Multiset.map_congr rfl fun t _ => h t,
    map_comp_conj_aroots Q fun t => 1 - C (Complex.joukowskyInv t) * X]

/-- The value of the Fejér–Riesz factor at `z ∈ ℂ` is `∏_t (1 - a(t) z)`. -/
theorem eval_fejerRieszFactor (Q : ℝ[X]) (z : ℂ) :
    (fejerRieszFactor Q).eval z =
      ((Q.aroots ℂ).map fun t => 1 - Complex.joukowskyInv t * z).prod := by
  rw [fejerRieszFactor, eval_multiset_prod, Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl fun t _ => by simp

/-- **The Fejér–Riesz factor has no zeros in the closed unit disk** if `Q > 0` on `[-1, 1]`:
for `|z| ≤ 1` each factor `1 - a(t) z` has `|a(t) z| < 1`. -/
theorem eval_fejerRieszFactor_ne_zero {Q : ℝ[X]} (hQ : ∀ r ∈ Set.Icc (-1 : ℝ) 1, 0 < Q.eval r)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : (fejerRieszFactor Q).eval z ≠ 0 := by
  rw [eval_fejerRieszFactor]
  refine Multiset.prod_ne_zero fun h0 => ?_
  obtain ⟨t, ht, h⟩ := Multiset.mem_map.1 h0
  have h1 : ‖Complex.joukowskyInv t * z‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hz).trans_lt
      (joukowskyInv_spec_of_mem_aroots hQ ht).1
  rw [← sub_eq_zero.1 h, norm_one] at h1
  exact lt_irrefl _ h1

/-- **A complex polynomial with coefficients fixed by conjugation is real**: if `PBar = P`
coefficientwise, then `P` is the image of a real polynomial (each coefficient equals its real
part; Mathlib's `Polynomial.lifts`). -/
theorem exists_map_eq_of_map_conj_eq {P : ℂ[X]} (h : P.map (starRingEnd ℂ) = P) :
    ∃ L : ℝ[X], L.map (algebraMap ℝ ℂ) = P := by
  refine (mem_lifts P).1 ((lifts_iff_coeff_lifts P).2 fun n => ⟨(P.coeff n).re, ?_⟩)
  have hn : conj (P.coeff n) = P.coeff n := by
    rw [← coeff_map, h]
  exact Complex.conj_eq_iff_re.1 hn

/-- **The squared modulus of the Fejér–Riesz factor on the unit circle.** If `Q > 0` on
`[-1, 1]`, then for every `θ ∈ ℝ`
`∏_t 2|a(t)| · ∏_t |cos θ - t| = |L₀(e^{iθ})|²`
over the complex roots `t` of `Q`: each factor is `|1 - a(t) z| |1 - conj (a(t)) z|` with
`z = e^{iθ}` (`Complex.joukowsky_two_mul_norm_mul_norm_re_sub`), and
`∏_t |1 - conj (a(t)) z| = ∏_t |1 - a(tBar) z| = ∏_t |1 - a(t) z|`. -/
theorem prod_two_mul_norm_mul_prod_norm_eq {Q : ℝ[X]}
    (hQ : ∀ r ∈ Set.Icc (-1 : ℝ) 1, 0 < Q.eval r) (θ : ℝ) :
    ((Q.aroots ℂ).map fun t => 2 * ‖Complex.joukowskyInv t‖).prod *
        ((Q.aroots ℂ).map fun t => ‖((Real.cos θ : ℝ) : ℂ) - t‖).prod =
      ‖(fejerRieszFactor Q).eval (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2 := by
  have hz : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hre : (Complex.exp ((θ : ℂ) * Complex.I)).re = Real.cos θ :=
    Complex.exp_ofReal_mul_I_re θ
  have h1 : ∀ t ∈ Q.aroots ℂ, 2 * ‖Complex.joukowskyInv t‖ * ‖((Real.cos θ : ℝ) : ℂ) - t‖ =
      ‖1 - Complex.joukowskyInv t * Complex.exp ((θ : ℂ) * Complex.I)‖ *
        ‖1 - conj (Complex.joukowskyInv t) * Complex.exp ((θ : ℂ) * Complex.I)‖ :=
    fun t ht => by
      rw [← hre]
      exact Complex.joukowsky_two_mul_norm_mul_norm_re_sub
        (joukowskyInv_spec_of_mem_aroots hQ ht).2 hz
  have h2 : ((Q.aroots ℂ).map fun t =>
      ‖1 - conj (Complex.joukowskyInv t) * Complex.exp ((θ : ℂ) * Complex.I)‖) =
      (Q.aroots ℂ).map fun t =>
        ‖1 - Complex.joukowskyInv t * Complex.exp ((θ : ℂ) * Complex.I)‖ := by
    rw [← map_comp_conj_aroots Q fun t =>
      ‖1 - Complex.joukowskyInv t * Complex.exp ((θ : ℂ) * Complex.I)‖]
    simp only [Complex.joukowskyInv_conj]
  rw [← Multiset.prod_map_mul, Multiset.map_congr rfl h1, Multiset.prod_map_mul, h2,
    eval_fejerRieszFactor, Multiset.norm_prod, Multiset.map_map, sq]
  rfl

/-- **Fejér–Riesz up to a constant.** If `Q > 0` on `[-1, 1]`, there are a constant `K > 0` and
a real polynomial `L` of degree `≤ deg Q`, without zeros in the closed unit disk, with
`Q(cos θ) = K |L(e^{iθ})|²` for all `θ ∈ ℝ`: `L` is the Fejér–Riesz factor read as a real
polynomial and `K = |c| / ∏_t 2|a(t)|`, with the leading coefficient `c` of `Q`
(`Polynomial.eval_eq_abs_leadingCoeff_mul_prod_norm`,
`Polynomial.prod_two_mul_norm_mul_prod_norm_eq`). -/
theorem exists_eval_cos_eq_mul_norm_sq {Q : ℝ[X]}
    (hQ : ∀ r ∈ Set.Icc (-1 : ℝ) 1, 0 < Q.eval r) :
    ∃ K : ℝ, 0 < K ∧ ∃ L : ℝ[X], L.natDegree ≤ Q.natDegree ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → aeval z L ≠ 0) ∧
      ∀ θ : ℝ, Q.eval (Real.cos θ) = K * ‖aeval (Complex.exp ((θ : ℂ) * Complex.I)) L‖ ^ 2 := by
  have hQ0 : Q ≠ 0 := fun h => by simpa [h] using hQ 0 ⟨by norm_num, by norm_num⟩
  obtain ⟨L, hL⟩ := exists_map_eq_of_map_conj_eq (map_conj_fejerRieszFactor Q)
  have hD : 0 < ((Q.aroots ℂ).map fun t => 2 * ‖Complex.joukowskyInv t‖).prod :=
    Multiset.prod_pos fun x hx => by
      obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hx
      exact mul_pos two_pos (norm_pos_iff.2
        (Complex.joukowsky_root_ne_zero (joukowskyInv_spec_of_mem_aroots hQ ht).2))
  refine ⟨|Q.leadingCoeff| / ((Q.aroots ℂ).map fun t => 2 * ‖Complex.joukowskyInv t‖).prod,
    div_pos (abs_pos.2 (leadingCoeff_ne_zero.2 hQ0)) hD, L, ?_, fun z hz => ?_, fun θ => ?_⟩
  · rw [← natDegree_map_eq_of_injective (RingHom.injective (algebraMap ℝ ℂ)), hL]
    exact natDegree_fejerRieszFactor_le Q
  · rw [← eval_map_algebraMap, hL]
    exact eval_fejerRieszFactor_ne_zero hQ hz
  · have hx : Real.cos θ ∈ Set.Icc (-1 : ℝ) 1 := ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
    rw [eval_eq_abs_leadingCoeff_mul_prod_norm (hQ _ hx).le, ← eval_map_algebraMap, hL,
      ← prod_two_mul_norm_mul_prod_norm_eq hQ θ]
    field_simp

/-- At `θ = 0` the identity `|L(e^{iθ})|² = Q(cos θ)` reads `L(1)² = Q(1)`. -/
theorem eval_one_sq_of_norm_aeval_exp_sq {Q L : ℝ[X]}
    (h : ∀ θ : ℝ, ‖aeval (Complex.exp ((θ : ℂ) * Complex.I)) L‖ ^ 2 = Q.eval (Real.cos θ)) :
    L.eval 1 ^ 2 = Q.eval 1 := by
  have h0 := h 0
  rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero, Real.cos_zero, ← Complex.ofReal_one,
    Complex.aeval_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h0
  exact h0

/-- **Fixing the sign.** A real polynomial `L` without zeros in the closed unit disk has
`L(1) ≠ 0`, so `L` or `-L` is positive at `1`. Both have the degree of `L`, no zeros in the closed
unit disk, and the moduli `|L(z)|`, `z ∈ ℂ`, of `L`. -/
theorem exists_eval_one_pos_of_aeval_ne_zero {L : ℝ[X]} (hne : ∀ z : ℂ, ‖z‖ ≤ 1 → aeval z L ≠ 0) :
    ∃ L' : ℝ[X], L'.natDegree = L.natDegree ∧ 0 < L'.eval 1 ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → aeval z L' ≠ 0) ∧ ∀ z : ℂ, ‖aeval z L'‖ = ‖aeval z L‖ := by
  have h1 : L.eval 1 ≠ 0 := by
    have h := hne 1 (by rw [norm_one])
    rwa [← Complex.ofReal_one, Complex.aeval_ofReal, Complex.ofReal_ne_zero] at h
  rcases lt_or_gt_of_ne h1 with hneg | hpos
  · refine ⟨-L, natDegree_neg L, by rw [eval_neg]; linarith, fun z hz => ?_, fun z => ?_⟩
    · rw [map_neg, neg_ne_zero]
      exact hne z hz
    · rw [map_neg, norm_neg]
  · exact ⟨L, rfl, hpos, hne, fun z => rfl⟩

/-- **The Fejér–Riesz theorem with an outer factor.** A real polynomial `Q` with `Q(t) > 0`
for all `t ∈ [-1, 1]` has a real polynomial `L` with `deg L ≤ deg Q`, `L(1) > 0`, no zeros in
the closed unit disk (an outer polynomial), and `|L(e^{iθ})|² = Q(cos θ)` for all `θ ∈ ℝ`.
Here `L = ±√K L₀` with the Fejér–Riesz factor `L₀ = ∏_t (1 - a(t) X)` and the constant `K` of
`Polynomial.exists_eval_cos_eq_mul_norm_sq`, the sign from
`Polynomial.exists_eval_one_pos_of_aeval_ne_zero`. -/
theorem fejer_riesz_outer {Q : ℝ[X]} (hQ : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 < Q.eval t) :
    ∃ L : ℝ[X], L.natDegree ≤ Q.natDegree ∧ 0 < L.eval 1 ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → aeval z L ≠ 0) ∧
      ∀ θ : ℝ, ‖aeval (Complex.exp ((θ : ℂ) * Complex.I)) L‖ ^ 2 = Q.eval (Real.cos θ) := by
  obtain ⟨K, hK, L, hdeg, hne, hL⟩ := exists_eval_cos_eq_mul_norm_sq hQ
  have hnorm : ∀ z : ℂ, ‖aeval z (C (Real.sqrt K) * L)‖ = Real.sqrt K * ‖aeval z L‖ :=
    fun z => by
      rw [map_mul, aeval_C, norm_mul, norm_algebraMap', Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg K)]
  obtain ⟨L', hdeg', hpos, hne', hL'⟩ :=
    exists_eval_one_pos_of_aeval_ne_zero (L := C (Real.sqrt K) * L) fun z hz => by
      rw [← norm_ne_zero_iff, hnorm]
      exact mul_ne_zero (Real.sqrt_pos.2 hK).ne' (norm_ne_zero_iff.2 (hne z hz))
  refine ⟨L', hdeg'.trans_le ((natDegree_C_mul_le _ _).trans hdeg), hpos, hne', fun θ => ?_⟩
  rw [hL', hnorm, mul_pow, Real.sq_sqrt hK.le, hL θ]

/-- **The Fejér–Riesz theorem.** For a real polynomial `Q` with `Q(t) > 0` for all `t ∈ [-1, 1]`,
`Q(cos θ)` is a squared modulus on the unit circle: there is a real polynomial `L` with
`deg L ≤ deg Q` and `L(1) > 0` such that `|L(e^{iθ})|² = Q(cos θ)` for all `θ ∈ ℝ`
(`Polynomial.fejer_riesz_outer`, which also gives `L` without zeros in the closed unit disk). -/
theorem fejer_riesz {Q : ℝ[X]} (hQ : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 < Q.eval t) :
    ∃ L : ℝ[X], L.natDegree ≤ Q.natDegree ∧ 0 < L.eval 1 ∧
      ∀ θ : ℝ, ‖aeval (Complex.exp ((θ : ℂ) * Complex.I)) L‖ ^ 2 = Q.eval (Real.cos θ) := by
  obtain ⟨L, hdeg, hpos, -, h⟩ := fejer_riesz_outer hQ
  exact ⟨L, hdeg, hpos, h⟩

/-- The identity of the Fejér–Riesz theorem holds with `e^{-iθ}` exactly when it holds with
`e^{iθ}`: substitute `-θ` and use `cos (-θ) = cos θ`. -/
theorem forall_norm_aeval_exp_neg_sq_iff {Q L : ℝ[X]} :
    (∀ θ : ℝ, ‖aeval (Complex.exp (-(θ : ℂ) * Complex.I)) L‖ ^ 2 = Q.eval (Real.cos θ)) ↔
      ∀ θ : ℝ, ‖aeval (Complex.exp ((θ : ℂ) * Complex.I)) L‖ ^ 2 = Q.eval (Real.cos θ) := by
  constructor
  · intro h θ
    have h' := h (-θ)
    rwa [Complex.ofReal_neg, neg_neg, Real.cos_neg] at h'
  · intro h θ
    have h' := h (-θ)
    rwa [Complex.ofReal_neg, Real.cos_neg] at h'

/-- **The Fejér–Riesz theorem with `e^{-iθ}`.** A real polynomial `Q` with `Q(t) > 0` for all
`t ∈ [-1, 1]` has a real polynomial `L` with `deg L ≤ deg Q`, `L(1) > 0` and
`|L(e^{-iθ})|² = Q(cos θ)` for all `θ ∈ ℝ` (`Polynomial.fejer_riesz`,
`Polynomial.forall_norm_aeval_exp_neg_sq_iff`). This is the form of the Daubechies masks, with
`θ = 2πξ`. -/
theorem fejer_riesz_exp_neg {Q : ℝ[X]} (hQ : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 < Q.eval t) :
    ∃ L : ℝ[X], L.natDegree ≤ Q.natDegree ∧ 0 < L.eval 1 ∧
      ∀ θ : ℝ, ‖aeval (Complex.exp (-(θ : ℂ) * Complex.I)) L‖ ^ 2 = Q.eval (Real.cos θ) := by
  obtain ⟨L, hdeg, hpos, h⟩ := fejer_riesz hQ
  exact ⟨L, hdeg, hpos, forall_norm_aeval_exp_neg_sq_iff.2 h⟩

end Polynomial
