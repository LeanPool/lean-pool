/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import LeanPool.IwaniecBeurlingAhlfors.BanachProbability.Martingale.Burkholder.Function

/-!
# Baernstein and Montgomery-Smith: the Burkholder–Šverák function and its Mellin transforms

A. Baernstein II and S. J. Montgomery-Smith, *Some conjectures about integral means of `∂f` and
`∂_zbar f`*, in: Complex analysis and differential equations (Uppsala, 1997), Acta Univ. Upsaliensis
Skr. Uppsala Univ. C Organ. Hist. 64 (1999), 92–109; arXiv:math/9709215v2 (the version read).

In the source's own terms, for `z, w ∈ ℂ` (TeX of arXiv:math/9709215v2, §1):

* `L (z, w) = |z|² − |w|²` if `|z| + |w| ≤ 1`, `2|z| − 1` if `|z| + |w| > 1`;
* `p* = max (p, p')`, `1/p + 1/p' = 1`, and
  `Φ_p (z, w) = α_p ((p* − 1)|z| − |w|)(|z| + |w|)^{p−1}`, `α_p = p (1 − 1/p*)^{p−1}`;
* (1.2a): `∫_0^∞ t^{p−1} L (z/t, w/t) dt = β_p Φ_p (z, w)` for `1 < p < 2`,
  `β_p = (½ p (2 − p) α_p)⁻¹`;
* (1.2b): with `M (z, w) = L (z, w) − (|z|² − |w|²)`,
  `∫_0^∞ t^{p−1} M (w/t, z/t) dt = γ_p Φ_p (z, w)` for `2 < p < ∞`,
  `γ_p = (½ p (p − 1)(p − 2) α_p)⁻¹`;
* "From [Bu3, p. 77] follows the inequality" `Φ_p (z, w) ≤ (p* − 1)^p |z|^p − |w|^p`
  (`1 < p < ∞`); [Bu3] is D. L. Burkholder, *Sharp inequalities for martingales and stochastic
  integrals*, Colloque Paul Lévy (Palaiseau, 1987), Astérisque 157–158 (1988), 75–94 (as listed in
  the source).

The paper (arXiv:2609.28311, TeX line 301) proves its Corollary 2 "by the arguments in
[Baernstein1997a]": these identities, the null Lagrangian `∫ |∂f|² − |∂_zbar f|² = 0`, and this
inequality.

Proofs. (1.2a) and (1.2b) are proved by direct integration: with `S = |z| + |w|`, the integrands
are combinations of powers `t^a` on `(0, S]` and on `(S, ∞)`, integrated by Mathlib's
`integral_rpow` and `integral_Ioi_rpow_of_lt`. The inequality is Burkholder's majorization
`V ≤ U` (Burkholder 1988, (1.10)), as formalized in the package `BanachProbability`
(`BanachProbability.Burkholder.burkholderU_ge`).
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace External.BaernsteinMontgomerySmith

/-- The Burkholder–Šverák function `L : ℂ × ℂ → ℝ`. -/
def L (z w : ℂ) : ℝ :=
  if ‖z‖ + ‖w‖ ≤ 1 then ‖z‖ ^ 2 - ‖w‖ ^ 2 else 2 * ‖z‖ - 1

/-- `M (z, w) = L (z, w) − (|z|² − |w|²)`. -/
def M (z w : ℂ) : ℝ := L z w - (‖z‖ ^ 2 - ‖w‖ ^ 2)

/-- `p* = max (p, p')`, `p' = p / (p − 1)`. -/
def pStar (p : ℝ) : ℝ := max p (p / (p - 1))

/-- `α_p = p (1 − 1/p*)^{p−1}`. -/
def alpha (p : ℝ) : ℝ := p * (1 - 1 / pStar p) ^ (p - 1)

/-- `Φ_p (z, w) = α_p ((p* − 1)|z| − |w|)(|z| + |w|)^{p−1}`. -/
def Phi (p : ℝ) (z w : ℂ) : ℝ :=
  alpha p * ((pStar p - 1) * ‖z‖ - ‖w‖) * (‖z‖ + ‖w‖) ^ (p - 1)

/-- `β_p = (½ p (2 − p) α_p)⁻¹`. -/
def beta (p : ℝ) : ℝ := (p * (2 - p) * alpha p / 2)⁻¹

/-- `γ_p = (½ p (p − 1)(p − 2) α_p)⁻¹`. -/
def gamma (p : ℝ) : ℝ := (p * (p - 1) * (p - 2) * alpha p / 2)⁻¹

/-! ### The integrands on `(0, |z| + |w|]` and on `(|z| + |w|, ∞)` -/

/-- `L (z/t, w/t)` for `t > 0`: `|z/t| + |w/t| ≤ 1` exactly when `|z| + |w| ≤ t`. -/
private lemma L_div {z w : ℂ} {t : ℝ} (ht : 0 < t) :
    L (z / t) (w / t) =
      if ‖z‖ + ‖w‖ ≤ t then (‖z‖ ^ 2 - ‖w‖ ^ 2) / t ^ 2 else 2 * ‖z‖ / t - 1 := by
  have hn : ∀ u : ℂ, ‖u / (t : ℂ)‖ = ‖u‖ / t := fun u => by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ht.le]
  have hc : ‖z‖ / t + ‖w‖ / t ≤ 1 ↔ ‖z‖ + ‖w‖ ≤ t := by rw [← add_div, div_le_one ht]
  unfold L
  rw [hn, hn]
  by_cases h : ‖z‖ + ‖w‖ ≤ t
  · rw [ite_eq_left (hc.2 h), ite_eq_left h]; ring
  · rw [ite_eq_right (mt hc.1 h), ite_eq_right h]; ring

/-- For `0 < t ≤ |z| + |w|`, `L (z/t, w/t) = 2|z|/t − 1` (at `t = |z| + |w|` the two expressions
agree). -/
private lemma L_div_of_le {z w : ℂ} {t : ℝ} (ht : 0 < t) (hts : t ≤ ‖z‖ + ‖w‖) :
    L (z / t) (w / t) = 2 * ‖z‖ / t - 1 := by
  rw [L_div ht]
  split_ifs with h
  · have he : t = ‖z‖ + ‖w‖ := le_antisymm hts h
    rw [he]
    have hS : ‖z‖ + ‖w‖ ≠ 0 := by rw [← he]; exact ht.ne'
    field_simp
    ring
  · rfl

/-- For `|z| + |w| ≤ t`, `L (z/t, w/t) = (|z|² − |w|²)/t²`. -/
private lemma L_div_of_ge {z w : ℂ} {t : ℝ} (ht : 0 < t) (hts : ‖z‖ + ‖w‖ ≤ t) :
    L (z / t) (w / t) = (‖z‖ ^ 2 - ‖w‖ ^ 2) / t ^ 2 := by
  rw [L_div ht, ite_eq_left hts]

private lemma norm_div_ofReal {t : ℝ} (ht : 0 < t) (u : ℂ) : ‖u / (t : ℂ)‖ = ‖u‖ / t := by
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ht.le]

private lemma rpow_sub_one' {t : ℝ} (ht : 0 < t) (a : ℝ) : t ^ (a - 1) = t ^ a * t⁻¹ := by
  rw [Real.rpow_sub ht, Real.rpow_one, div_eq_mul_inv]

private lemma rpow_sub_two' {t : ℝ} (ht : 0 < t) (a : ℝ) : t ^ (a - 2) = t ^ a * (t ^ 2)⁻¹ := by
  rw [Real.rpow_sub ht, div_eq_mul_inv]
  norm_cast

/-- The integrand of (1.2a) on `(0, |z| + |w|]`. -/
private lemma eqOn_Ioc_2a (p : ℝ) (z w : ℂ) :
    Set.EqOn (fun t : ℝ => t ^ (p - 1) * L (z / t) (w / t))
      (fun t => 2 * ‖z‖ * t ^ (p - 2) - t ^ (p - 1)) (Set.Ioc 0 (‖z‖ + ‖w‖)) := by
  intro t ht
  simp only
  rw [L_div_of_le ht.1 ht.2, show p - 2 = p - 1 - 1 by ring, rpow_sub_one' ht.1 (p - 1)]
  ring

/-- The integrand of (1.2a) on `(|z| + |w|, ∞)`. -/
private lemma eqOn_Ioi_2a (p : ℝ) (z w : ℂ) :
    Set.EqOn (fun t : ℝ => t ^ (p - 1) * L (z / t) (w / t))
      (fun t => (‖z‖ ^ 2 - ‖w‖ ^ 2) * t ^ (p - 3)) (Set.Ioi (‖z‖ + ‖w‖)) := by
  intro t ht
  have ht0 : 0 < t := lt_of_le_of_lt (by positivity) ht
  simp only
  rw [L_div_of_ge ht0 (le_of_lt ht), show p - 3 = p - 1 - 2 by ring, rpow_sub_two' ht0 (p - 1)]
  ring

/-- The integrand of (1.2b) on `(0, |z| + |w|]`. -/
private lemma eqOn_Ioc_2b (p : ℝ) (z w : ℂ) :
    Set.EqOn (fun t : ℝ => t ^ (p - 1) * M (w / t) (z / t))
      (fun t => 2 * ‖w‖ * t ^ (p - 2) - t ^ (p - 1) - (‖w‖ ^ 2 - ‖z‖ ^ 2) * t ^ (p - 3))
      (Set.Ioc 0 (‖w‖ + ‖z‖)) := by
  intro t ht
  simp only
  rw [M, L_div_of_le ht.1 ht.2, norm_div_ofReal ht.1, norm_div_ofReal ht.1,
    show p - 2 = p - 1 - 1 by ring, rpow_sub_one' ht.1 (p - 1), show p - 3 = p - 1 - 2 by ring,
    rpow_sub_two' ht.1 (p - 1)]
  ring

/-- The integrand of (1.2b) vanishes on `(|z| + |w|, ∞)`. -/
private lemma eqOn_Ioi_2b (p : ℝ) (z w : ℂ) :
    Set.EqOn (fun t : ℝ => t ^ (p - 1) * M (w / t) (z / t)) (fun _ => 0)
      (Set.Ioi (‖w‖ + ‖z‖)) := by
  intro t ht
  have ht0 : 0 < t := lt_of_le_of_lt (by positivity) ht
  simp only
  rw [M, L_div_of_ge ht0 (le_of_lt ht), norm_div_ofReal ht0, norm_div_ofReal ht0]
  ring

/-! ### The integrals of the powers -/

private lemma intervalIntegrable_rpow_comb {a b : ℝ} (ha : -1 < a) (hb : -1 < b) (c d S : ℝ) :
    IntervalIntegrable (fun t : ℝ => c * t ^ a - d * t ^ b) volume 0 S :=
  ((intervalIntegral.intervalIntegrable_rpow' ha).const_mul c).sub
    ((intervalIntegral.intervalIntegrable_rpow' hb).const_mul d)

private lemma integral_rpow_comb {a b : ℝ} (ha : -1 < a) (hb : -1 < b) (c d S : ℝ) :
    ∫ t in (0 : ℝ)..S, (c * t ^ a - d * t ^ b) =
      c * (S ^ (a + 1) / (a + 1)) - d * (S ^ (b + 1) / (b + 1)) := by
  rw [intervalIntegral.integral_sub ((intervalIntegral.intervalIntegrable_rpow' ha).const_mul c)
      ((intervalIntegral.intervalIntegrable_rpow' hb).const_mul d),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl ha), integral_rpow (Or.inl hb), Real.zero_rpow (by linarith),
    Real.zero_rpow (by linarith), sub_zero, sub_zero]

/-! ### The constants -/

/-- `α_p > 0` for `1 < p`. -/
theorem alpha_pos {p : ℝ} (hp : 1 < p) : 0 < alpha p := by
  have hps : p ≤ pStar p := le_max_left _ _
  have h1 : 0 < 1 - 1 / pStar p := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  exact mul_pos (by linarith) (Real.rpow_pos_of_pos h1 _)

private lemma pStar_sub_one_of_lt_two {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    pStar p - 1 = (p - 1)⁻¹ := by
  have h : pStar p = p / (p - 1) :=
    max_eq_right (by rw [le_div_iff₀ (by linarith)]; nlinarith)
  have hp0 : p - 1 ≠ 0 := by linarith
  rw [h]
  field_simp
  ring

private lemma pStar_of_two_lt {p : ℝ} (hp : 2 < p) : pStar p = p :=
  max_eq_left (by rw [div_le_iff₀ (by linarith)]; nlinarith)

/-! ### (1.2a) and (1.2b) -/

/-- The integrand of (1.2a) is integrable on `(0, ∞)` for `1 < p < 2`.

Proof: direct integration. With `S = |z| + |w|`, the integrand is `2|z| t^{p−2} − t^{p−1}` on
`(0, S]` and `(|z|² − |w|²) t^{p−3}` on `(S, ∞)`; `p − 2 > −1` and `p − 3 < −1`. -/
theorem integrableOn_equation1_2a {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (z w : ℂ) :
    IntegrableOn (fun t : ℝ => t ^ (p - 1) * L (z / t) (w / t)) (Set.Ioi 0) := by
  rcases (add_nonneg (norm_nonneg z) (norm_nonneg w)).eq_or_lt with hS | hS
  · have hz : z = 0 := norm_eq_zero.1 (by linarith [norm_nonneg z, norm_nonneg w])
    have hw : w = 0 := norm_eq_zero.1 (by linarith [norm_nonneg z, norm_nonneg w])
    subst hz hw
    simp [L]
  · rw [← Set.Ioc_union_Ioi_eq_Ioi hS.le]
    refine IntegrableOn.union ?_ ?_
    · refine IntegrableOn.congr_fun ?_ (eqOn_Ioc_2a p z w).symm measurableSet_Ioc
      have := intervalIntegrable_rpow_comb (a := p - 2) (b := p - 1) (by linarith) (by linarith)
        (2 * ‖z‖) 1 (‖z‖ + ‖w‖)
      simp only [one_mul] at this
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hS.le).1 this
    · exact IntegrableOn.congr_fun
        ((integrableOn_Ioi_rpow_of_lt (a := p - 3) (by linarith) hS).const_mul
          (‖z‖ ^ 2 - ‖w‖ ^ 2)) (eqOn_Ioi_2a p z w).symm measurableSet_Ioi

/-- **(1.2a)**: `∫_0^∞ t^{p−1} L (z/t, w/t) dt = β_p Φ_p (z, w)` for `1 < p < 2`.

Proof: direct integration. With `S = |z| + |w|`, the integral over `(0, S]` is
`2|z| S^{p−1}/(p − 1) − S^p/p` and the integral over `(S, ∞)` is `(|z|² − |w|²) S^{p−2}/(2 − p)`;
the sum is `(2/(p (2 − p))) S^{p−1} (|z|/(p − 1) − |w|) = β_p Φ_p (z, w)`, since
`p* − 1 = 1/(p − 1)`. -/
theorem equation1_2a {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (z w : ℂ) :
    ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) * L (z / t) (w / t) = beta p * Phi p z w := by
  rcases (add_nonneg (norm_nonneg z) (norm_nonneg w)).eq_or_lt with hS | hS
  · have hz : z = 0 := norm_eq_zero.1 (by linarith [norm_nonneg z, norm_nonneg w])
    have hw : w = 0 := norm_eq_zero.1 (by linarith [norm_nonneg z, norm_nonneg w])
    subst hz hw
    simp [L, Phi]
  · have hI := integrableOn_equation1_2a hp1 hp2 z w
    rw [← Set.Ioc_union_Ioi_eq_Ioi hS.le] at hI ⊢
    rw [setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hI.mono_set Set.subset_union_left) (hI.mono_set Set.subset_union_right),
      setIntegral_congr_fun measurableSet_Ioc (eqOn_Ioc_2a p z w),
      setIntegral_congr_fun measurableSet_Ioi (eqOn_Ioi_2a p z w),
      integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hS]
    have h1 := integral_rpow_comb (a := p - 2) (b := p - 1) (by linarith) (by linarith)
        (2 * ‖z‖) 1 (‖z‖ + ‖w‖)
    simp only [one_mul] at h1
    rw [← intervalIntegral.integral_of_le hS.le, h1]
    set s := ‖z‖
    set r := ‖w‖
    have hα := (alpha_pos hp1).ne'
    have hSp : (s + r) ^ p = (s + r) ^ (p - 1) * (s + r) := by
      rw [rpow_sub_one' hS, mul_assoc, inv_mul_cancel₀ hS.ne', mul_one]
    have hS2 : (s + r) ^ (p - 3 + 1) = (s + r) ^ (p - 1) * (s + r)⁻¹ := by
      rw [show p - 3 + 1 = p - 1 - 1 by ring, rpow_sub_one' hS]
    rw [show p - 2 + 1 = p - 1 by ring, show p - 1 + 1 = p by ring, hSp, hS2, beta, Phi,
      pStar_sub_one_of_lt_two hp1 hp2]
    have hp0 : p - 1 ≠ 0 := by linarith
    have hp2' : 2 - p ≠ 0 := by linarith
    have hp3 : p - 3 + 1 ≠ 0 := by linarith
    have hpp : p ≠ 0 := by linarith
    field_simp
    ring

/-- The integrand of (1.2b) is integrable on `(0, ∞)` for `2 < p`.

Proof: direct integration. With `S = |z| + |w|`, the integrand is
`2|w| t^{p−2} − t^{p−1} − (|w|² − |z|²) t^{p−3}` on `(0, S]` and `0` on `(S, ∞)`; `p − 3 > −1`. -/
theorem integrableOn_equation1_2b {p : ℝ} (hp : 2 < p) (z w : ℂ) :
    IntegrableOn (fun t : ℝ => t ^ (p - 1) * M (w / t) (z / t)) (Set.Ioi 0) := by
  have hS : 0 ≤ ‖w‖ + ‖z‖ := by positivity
  rw [← Set.Ioc_union_Ioi_eq_Ioi hS]
  refine IntegrableOn.union ?_ ?_
  · refine IntegrableOn.congr_fun ?_ (eqOn_Ioc_2b p z w).symm measurableSet_Ioc
    have := (intervalIntegrable_rpow_comb (a := p - 2) (b := p - 1) (by linarith) (by linarith)
      (2 * ‖w‖) 1 (‖w‖ + ‖z‖)).sub
      ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := ‖w‖ + ‖z‖)
        (r := p - 3) (by linarith)).const_mul (‖w‖ ^ 2 - ‖z‖ ^ 2))
    simp only [one_mul] at this
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hS).1 this
  · exact integrableOn_zero.congr_fun (eqOn_Ioi_2b p z w).symm measurableSet_Ioi

/-- **(1.2b)**: `∫_0^∞ t^{p−1} M (w/t, z/t) dt = γ_p Φ_p (z, w)` for `2 < p < ∞`.

Proof: direct integration. With `S = |z| + |w|`, the integrand vanishes on `(S, ∞)`, and its
integral over `(0, S]` is `2|w| S^{p−1}/(p − 1) − S^p/p − (|w|² − |z|²) S^{p−2}/(p − 2)
= (2/(p (p − 1)(p − 2))) S^{p−1} ((p − 1)|z| − |w|) = γ_p Φ_p (z, w)`, since `p* = p`. -/
theorem equation1_2b {p : ℝ} (hp : 2 < p) (z w : ℂ) :
    ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) * M (w / t) (z / t) = gamma p * Phi p z w := by
  rcases (add_nonneg (norm_nonneg w) (norm_nonneg z)).eq_or_lt with hS | hS
  · have hz : z = 0 := norm_eq_zero.1 (by linarith [norm_nonneg z, norm_nonneg w])
    have hw : w = 0 := norm_eq_zero.1 (by linarith [norm_nonneg z, norm_nonneg w])
    subst hz hw
    simp [M, L, Phi]
  · have hI := integrableOn_equation1_2b hp z w
    rw [← Set.Ioc_union_Ioi_eq_Ioi hS.le] at hI ⊢
    rw [setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hI.mono_set Set.subset_union_left) (hI.mono_set Set.subset_union_right),
      setIntegral_congr_fun measurableSet_Ioc (eqOn_Ioc_2b p z w),
      setIntegral_congr_fun measurableSet_Ioi (eqOn_Ioi_2b p z w), integral_zero, add_zero,
      ← intervalIntegral.integral_of_le hS.le,
      intervalIntegral.integral_sub (intervalIntegrable_rpow_comb (a := p - 2) (b := p - 1)
        (by linarith) (by linarith) (2 * ‖w‖) 1 (‖w‖ + ‖z‖) |>.congr fun t _ => by ring)
        ((intervalIntegral.intervalIntegrable_rpow' (r := p - 3) (by linarith)).const_mul _)]
    have h1 := integral_rpow_comb (a := p - 2) (b := p - 1) (by linarith) (by linarith)
        (2 * ‖w‖) 1 (‖w‖ + ‖z‖)
    simp only [one_mul] at h1
    rw [h1, intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
      Real.zero_rpow (by linarith), sub_zero]
    set s := ‖z‖
    set r := ‖w‖
    have hα := (alpha_pos (by linarith : (1 : ℝ) < p)).ne'
    have hSp : (r + s) ^ p = (r + s) ^ (p - 1) * (r + s) := by
      rw [rpow_sub_one' hS, mul_assoc, inv_mul_cancel₀ hS.ne', mul_one]
    have hS2 : (r + s) ^ (p - 3 + 1) = (r + s) ^ (p - 1) * (r + s)⁻¹ := by
      rw [show p - 3 + 1 = p - 1 - 1 by ring, rpow_sub_one' hS]
    rw [show p - 2 + 1 = p - 1 by ring, show p - 1 + 1 = p by ring, hSp, hS2, gamma, Phi,
      pStar_of_two_lt hp, add_comm s r]
    have hp0 : p - 1 ≠ 0 := by linarith
    have hp2' : p - 2 ≠ 0 := by linarith
    have hp3 : p - 3 + 1 ≠ 0 := by linarith
    have hpp : p ≠ 0 := by linarith
    field_simp
    ring

/-- **Burkholder's inequality** as the source uses it ("From [Bu3, p. 77] follows the
inequality", §1): `Φ_p (z, w) ≤ (p* − 1)^p |z|^p − |w|^p` for `1 < p < ∞`.

Proof: Burkholder's majorization, as formalized in BanachProbability
(`BanachProbability.Burkholder.burkholderU_ge`, Burkholder 1988, (1.10)), at `s = |w|`, `r = |z|`:
`Φ_p (z, w) = −U (|w|, |z|)`. -/
theorem phi_le {p : ℝ} (hp : 1 < p) (z w : ℂ) :
    Phi p z w ≤ (pStar p - 1) ^ p * ‖z‖ ^ p - ‖w‖ ^ p := by
  have h := BanachProbability.Burkholder.burkholderU_ge hp (norm_nonneg w) (norm_nonneg z)
  have he : Phi p z w = -BanachProbability.Burkholder.burkholderU p ‖w‖ ‖z‖ := by
    unfold Phi alpha pStar BanachProbability.Burkholder.burkholderU
    rw [add_comm ‖w‖ ‖z‖]
    ring
  rw [he]
  unfold pStar
  linarith

end External.BaernsteinMontgomerySmith
