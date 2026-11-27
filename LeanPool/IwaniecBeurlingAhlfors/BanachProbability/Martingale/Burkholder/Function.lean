/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.BanachProbability.Defs
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Burkholder's function

D. L. Burkholder, *Sharp inequalities for martingales and stochastic integrals*, Colloque Paul
Lévy sur les processus stochastiques, Astérisque 157–158 (1988), 75–94: the function (1.6), its
majorization (1.10), and its concavity along lines, Remark 1.2 (1.17), by the arguments of the paper
(§1). The paper states Remark 1.2 without proof; it is completed from the concavity of `G` in the
paper's proof of (1.12), by (1.14), and the shift of its proof of (1.8) (steps 3 and 4 below).

For `p > 1`, `p* = max (p, p / (p − 1))` and `x`, `y` in a normed group, Burkholder's function is
`u_p (x, y) = α_p (|y| − (p* − 1) |x|) (|x| + |y|)^{p−1}`, `α_p = p (1 − 1/p*)^{p−1}`
(`burkholderFun`), where, in Burkholder's notation, `x` is the position of the dominating martingale
and `y` that of the subordinate one. `burkholderU` is the same function of the norms, with the
subordinate position first: `u_p (x, y) = U (|y|, |x|)` (`burkholderFun_eq_burkholderU`).

## Main results

* `burkholderU_ge`, `burkholderFun_ge`: `u_p ≥ v_p`, `v_p (x, y) = |y|^p − (p* − 1)^p |x|^p`
  (Burkholder's (1.10)).
* `burkholderU_concaveOn_line`, `burkholderFun_concaveOn_line`: in a real inner product space, if
  `|k| ≤ |h|`, then `t ↦ u_p (x + t h, y + t k)` is concave on `ℝ` (Burkholder's Remark 1.2,
  (1.17)).
* `burkholderFun_of_two_le`: for `p ≥ 2`, `p* = p` and
  `u_p (x, y) = p (1 − 1/p)^{p−1} (|y| − (p − 1) |x|) (|x| + |y|)^{p−1}`.

## The proofs (Burkholder 1988, §1), in the notation of `burkholderU`

1. (1.11) `φ (p) = (p − 1)^{p−1} / p^{p−2}` is `≤ 1` for `1 < p ≤ 2` and `≥ 1` for `p ≥ 2`
   (`phi_le_one`, `one_le_phi`): `log φ` vanishes at `1` and `2`, is convex on `[1, 2]` and concave
   on `[2, ∞)` (its second derivative is `(2 − p) / (p² (p − 1))`), and tends to `∞` (it is at
   least `log p − 1`).
2. (1.10) `V ≤ U` (`burkholderU_ge`): by homogeneity, on `|x| + |y| = 1` and with `t` the norm
   of the dominating martingale's position, `U − V = F (t) = α_p (1 − p* t) − (1 − t)^p +
   (p* − 1)^p t^p` (`bF`). If `p = 2`, `F ≡ 0`. If `p > 2`, `F` is concave on `[0, s₀]` and convex
   on `[s₀, 1]` for some `s₀ ≤ 1/p*`, `F (1/p*) = F' (1/p*) = 0`, and `F (0) = α_p − 1 ≥ 0` by
   (1.11). If `p < 2`, `F` is convex on `[0, s₀]` for some `s₀ ≥ 1/p*` and concave on `[s₀, 1]`,
   and `F (1) ≥ 0` by (1.11) (`bF_nonneg`). Burkholder asserts that `s₀` exists; here it is
   `1/(1 + (p* − 1)^{p/(p−2)})`, read off from `F''`.
3. The concavity of `G` in the proof of (1.12), by (1.14): if `x + t h` and `y + t k` never vanish,
   `G (t) = U (x + t h, y + t k)` is twice differentiable.
   For `p ≥ 2`, `U = α_p ψ (|x|, |y|)` with `ψ (s, r) = (s − (p − 1) r)(s + r)^{p−1}` (`psi`, not
   to be confused with Burkholder's gradient `ψ`), and the
   second derivative of `t ↦ ψ (S, R)`, `S = |x + t h|`, `R = |y + t k|`, is
   `p (S + R)^{p−3} (−(p − 1)(p − 2) R (S' + R')² − (p − 2)(S + R)² S''
   − (p − 1)(S + R)(|k|² − |h|²))` (`psi_hasDerivAt_two`): its three terms are Burkholder's
   `−C`, `−B`, `−A` of (1.14), each `≤ 0` (`psi_two_sign`). For `p ≤ 2`, `(p − 1) U` is `−α_p ψ`
   with the arguments exchanged. So `G` is concave (`psi_line_of_ne`).
4. Remark 1.2 (`burkholderU_concaveOn_line`) states the concavity on every line without proof. It
   follows from step 3 by the device of the proof of (1.8): in `H ⊕ ℝ` the lines through `(x, δ)`
   and `(y, δ)` with directions `(h, 0)` and `(k, 0)` never vanish for `δ ≠ 0`; let `δ → 0`.
-/

@[expose] public section

open Filter Set
open scoped Topology InnerProductSpace RealInnerProductSpace

namespace BanachProbability.Burkholder

/-! ### The function `ψ (s, r) = (s − (p − 1) r) (s + r)^{p−1}` and its derivatives -/

/-- `ψ (s, r) = (s − (p − 1) r) (s + r)^{p−1}`; Burkholder's function in the argument order of
`burkholderU` (subordinate first) is `α ψ (|x|, |y|)` for `p ≥ 2` and `−α (p − 1)⁻¹ ψ (|y|, |x|)`
for `p ≤ 2`. Not Burkholder's `ψ`, which is a gradient. -/
private noncomputable def psi (p s r : ℝ) : ℝ := (s - (p - 1) * r) * (s + r) ^ (p - 1)

/-- `∂ψ/∂s = p (s + r)^{p−2} (s − (p − 2) r)`. -/
private noncomputable def psiS (p s r : ℝ) : ℝ := p * (s + r) ^ (p - 2) * (s - (p - 2) * r)

/-- `∂ψ/∂r = −p (p − 1) r (s + r)^{p−2}`. -/
private noncomputable def psiR (p s r : ℝ) : ℝ := -(p * (p - 1)) * r * (s + r) ^ (p - 2)

/-- The (one-sided) derivative of `ψ` along a curve `(S, R)`: `ψ_s S' + ψ_r R'`. -/
private theorem psi_hasDerivWithinAt {p : ℝ} {S R : ℝ → ℝ} {S1 R1 t : ℝ} {s : Set ℝ}
    (hS : HasDerivWithinAt S S1 s t) (hR : HasDerivWithinAt R R1 s t) (hpos : 0 < S t + R t) :
    HasDerivWithinAt (fun u => psi p (S u) (R u))
      (psiS p (S t) (R t) * S1 + psiR p (S t) (R t) * R1) s t := by
  have h := (hS.sub (hR.const_mul (p - 1))).mul
    ((hS.add hR).rpow_const (p := p - 1) (Or.inl hpos.ne'))
  have e : (S t + R t) ^ (p - 1) = (S t + R t) ^ (p - 2) * (S t + R t) := by
    rw [show p - 1 = p - 2 + 1 by ring, Real.rpow_add_one hpos.ne']
  have e2 : p - 1 - 1 = p - 2 := by ring
  unfold psi psiS psiR
  convert h using 1
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [e2, e]; ring

private theorem psi_hasDerivAt {p : ℝ} {S R : ℝ → ℝ} {S1 R1 t : ℝ}
    (hS : HasDerivAt S S1 t) (hR : HasDerivAt R R1 t) (hpos : 0 < S t + R t) :
    HasDerivAt (fun u => psi p (S u) (R u))
      (psiS p (S t) (R t) * S1 + psiR p (S t) (R t) * R1) t := by
  rw [← hasDerivWithinAt_univ] at *
  exact psi_hasDerivWithinAt hS hR hpos

/-- The second derivative of `ψ` along a curve `(S, R)`:
`p (S + R)^{p−3} (−(p − 1)(p − 2) R (S' + R')² − (p − 2)(S + R)² S'' − (p − 1)(S + R)(K − H))`
with `H = S'² + S S''`, `K = R'² + R R''`. -/
private theorem psi_hasDerivAt_two {p : ℝ} {S R S1 R1 : ℝ → ℝ} {S2 R2 t : ℝ}
    (hS : HasDerivAt S (S1 t) t) (hR : HasDerivAt R (R1 t) t)
    (hS1 : HasDerivAt S1 S2 t) (hR1 : HasDerivAt R1 R2 t) (hpos : 0 < S t + R t) :
    HasDerivAt (fun u => psiS p (S u) (R u) * S1 u + psiR p (S u) (R u) * R1 u)
      (p * (S t + R t) ^ (p - 3) * (-(p - 1) * (p - 2) * R t * (S1 t + R1 t) ^ 2
        - (p - 2) * (S t + R t) ^ 2 * S2
        - (p - 1) * (S t + R t) * ((R1 t ^ 2 + R t * R2) - (S1 t ^ 2 + S t * S2)))) t := by
  have hP := (hS.add hR).rpow_const (p := p - 2) (Or.inl hpos.ne')
  have h1 := ((hP.const_mul p).mul (hS.sub (hR.const_mul (p - 2)))).mul hS1
  have h2 := (((hR.const_mul (-(p * (p - 1)))).mul hP)).mul hR1
  have h := h1.add h2
  have e : (S t + R t) ^ (p - 2) = (S t + R t) ^ (p - 3) * (S t + R t) := by
    rw [show p - 2 = p - 3 + 1 by ring, Real.rpow_add_one hpos.ne']
  have e2 : p - 2 - 1 = p - 3 := by ring
  unfold psiS psiR
  convert h using 1
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  rw [e2, e]; ring

/-- The sign of the second derivative of `ψ` along a curve (`psi_hasDerivAt_two`): with
`S, R ≥ 0`, `S'' ≥ 0`, `H = S'² + S S''` and `K = R'² + R R''`, it is `≤ 0` if `p ≥ 2` and `H ≤ K`,
and `≥ 0` if `p ≤ 2` and `K ≤ H`. -/
private theorem psi_two_sign {p S R S1 R1 S2 R2 : ℝ} (hp : 1 < p) (hS : 0 ≤ S) (hR : 0 ≤ R)
    (hS2 : 0 ≤ S2) :
    ((2 ≤ p ∧ S1 ^ 2 + S * S2 ≤ R1 ^ 2 + R * R2) →
      p * (S + R) ^ (p - 3) * (-(p - 1) * (p - 2) * R * (S1 + R1) ^ 2
        - (p - 2) * (S + R) ^ 2 * S2 - (p - 1) * (S + R) * ((R1 ^ 2 + R * R2) - (S1 ^ 2 + S * S2)))
        ≤ 0) ∧
    ((p ≤ 2 ∧ R1 ^ 2 + R * R2 ≤ S1 ^ 2 + S * S2) →
      0 ≤ p * (S + R) ^ (p - 3) * (-(p - 1) * (p - 2) * R * (S1 + R1) ^ 2
        - (p - 2) * (S + R) ^ 2 * S2 - (p - 1) * (S + R) * ((R1 ^ 2 + R * R2) - (S1 ^ 2 + S * S2))))
    := by
  have hp1 : 0 ≤ p - 1 := by linarith
  have hW : 0 ≤ S + R := add_nonneg hS hR
  have hpow : 0 ≤ p * (S + R) ^ (p - 3) := mul_nonneg (by linarith) (Real.rpow_nonneg hW _)
  refine ⟨fun ⟨hp2, hHK⟩ => mul_nonpos_of_nonneg_of_nonpos hpow ?_,
    fun ⟨hp2, hHK⟩ => mul_nonneg hpow ?_⟩
  · have h2 : 0 ≤ p - 2 := by linarith
    have := mul_nonneg (mul_nonneg (mul_nonneg hp1 h2) hR) (sq_nonneg (S1 + R1))
    have := mul_nonneg (mul_nonneg h2 (sq_nonneg (S + R))) hS2
    have := mul_nonneg (mul_nonneg hp1 hW) (sub_nonneg.2 hHK)
    nlinarith
  · have h2 : 0 ≤ 2 - p := by linarith
    have := mul_nonneg (mul_nonneg (mul_nonneg hp1 h2) hR) (sq_nonneg (S1 + R1))
    have := mul_nonneg (mul_nonneg h2 (sq_nonneg (S + R))) hS2
    have := mul_nonneg (mul_nonneg hp1 hW) (sub_nonneg.2 hHK)
    nlinarith

/-! ### The concavity property of `ψ` along lines in a Hilbert space -/

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `S' (t) = ⟨x + t h, h⟩ / |x + t h|`, the derivative of `S (t) = |x + t h|` where
`x + t h ≠ 0`. -/
private noncomputable def lineD (x h : H) (t : ℝ) : ℝ := ⟪x + t • h, h⟫ / ‖x + t • h‖

/-- `S'' (t) = (|h|² − S' (t)²) / S (t)`. -/
private noncomputable def lineD2 (x h : H) (t : ℝ) : ℝ :=
  (‖h‖ ^ 2 - lineD x h t ^ 2) / ‖x + t • h‖

/-- `S (t) = |x + t h|` is smooth where `x + t h ≠ 0` (and constant if `h = 0`), with `S'' ≥ 0` and
`S'² + S S'' = |h|²`. -/
private theorem line_facts (x h : H) {t : ℝ} (ht : x + t • h ≠ 0 ∨ h = 0) :
    HasDerivAt (fun u : ℝ => ‖x + u • h‖) (lineD x h t) t ∧
      HasDerivAt (lineD x h) (lineD2 x h t) t ∧ 0 ≤ lineD2 x h t ∧
      lineD x h t ^ 2 + ‖x + t • h‖ * lineD2 x h t = ‖h‖ ^ 2 := by
  rcases ht with ht | rfl
  · have hN : 0 < ‖x + t • h‖ := norm_pos_iff.2 ht
    have hlin : HasDerivAt (fun u : ℝ => x + u • h) h t := by
      simpa using ((hasDerivAt_id' t).smul_const h).const_add x
    have dS : HasDerivAt (fun u : ℝ => ‖x + u • h‖) (lineD x h t) t := by
      have h3 := hlin.norm_sq.sqrt (pow_pos hN 2).ne'
      simp only [Real.sqrt_sq_eq_abs, abs_norm] at h3
      convert h3 using 1
      unfold lineD; field_simp
    have dN : HasDerivAt (fun u : ℝ => ⟪x + u • h, h⟫) (‖h‖ ^ 2) t := by
      have e : ∀ u : ℝ, ⟪x + u • h, h⟫ = ⟪x, h⟫ + u * ‖h‖ ^ 2 := fun u => by
        rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
      simp only [e]
      simpa using ((hasDerivAt_id' t).mul_const (‖h‖ ^ 2)).const_add ⟪x, h⟫
    have hcs : lineD x h t ^ 2 ≤ ‖h‖ ^ 2 := by
      unfold lineD
      rw [div_pow, div_le_iff₀ (by positivity)]
      have h1 := abs_real_inner_le_norm (x + t • h) h
      have h2 : ⟪x + t • h, h⟫ ^ 2 ≤ (‖x + t • h‖ * ‖h‖) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      nlinarith
    refine ⟨dS, ?_, div_nonneg (sub_nonneg.2 hcs) hN.le, ?_⟩
    · convert dN.div dS hN.ne' using 1
      · funext u; simp [lineD]
      · unfold lineD2 lineD
        field_simp
    · unfold lineD2; field_simp; ring
  · have e1 : (fun u : ℝ => ‖x + u • (0 : H)‖) = fun _ => ‖x‖ := by funext u; simp
    have e2 : lineD x (0 : H) = fun _ => 0 := by funext u; simp [lineD]
    have e3 : lineD2 x (0 : H) t = 0 := by simp [lineD2, lineD]
    rw [e1, e2, e3]
    exact ⟨hasDerivAt_const _ _, hasDerivAt_const _ _, le_rfl, by simp⟩

/-- `G (t) = ψ (|x + t h|, |y + t k|)`, `ψ` along the line through `(x, y)` with direction
`(h, k)`. -/
private noncomputable def psiLine (p : ℝ) (x y h k : H) (t : ℝ) : ℝ :=
  psi p ‖x + t • h‖ ‖y + t • k‖

/-- `G' (t) = ψ_s S' + ψ_r R'`, the derivative of `G` where `x + t h ≠ 0` and `y + t k ≠ 0`. -/
private noncomputable def psiLineD (p : ℝ) (x y h k : H) (t : ℝ) : ℝ :=
  psiS p ‖x + t • h‖ ‖y + t • k‖ * lineD x h t + psiR p ‖x + t • h‖ ‖y + t • k‖ * lineD y k t

/-- **(1.14)** at one point: where `x + t h ≠ 0` (or `h = 0`) and `y + t k ≠ 0` (or `k = 0`), `G`
is twice differentiable, with `G'' ≤ 0` if `p ≥ 2`, `|h| ≤ |k|`, and `G'' ≥ 0` if `p ≤ 2`,
`|k| ≤ |h|` (`psi_hasDerivAt_two`, `psi_two_sign`, with `H = |h|²`, `K = |k|²`). -/
private theorem psi_line_smooth {p : ℝ} (hp : 1 < p) (x y h k : H) {t : ℝ}
    (hx : x + t • h ≠ 0 ∨ h = 0) (hy : y + t • k ≠ 0 ∨ k = 0)
    (hW : 0 < ‖x + t • h‖ + ‖y + t • k‖) :
    HasDerivAt (psiLine p x y h k) (psiLineD p x y h k t) t ∧
      ∃ c, HasDerivAt (psiLineD p x y h k) c t ∧ ((2 ≤ p ∧ ‖h‖ ≤ ‖k‖) → c ≤ 0) ∧
        ((p ≤ 2 ∧ ‖k‖ ≤ ‖h‖) → 0 ≤ c) := by
  obtain ⟨dS, dS1, hS2, hH⟩ := line_facts x h hx
  obtain ⟨dR, dR1, -, hK⟩ := line_facts y k hy
  have hsign := psi_two_sign hp (norm_nonneg (x + t • h)) (norm_nonneg (y + t • k)) hS2
    (S1 := lineD x h t) (R1 := lineD y k t) (R2 := lineD2 y k t)
  refine ⟨psi_hasDerivAt dS dR hW, _, psi_hasDerivAt_two (p := p) dS dR dS1 dR1 hW,
    fun ⟨hp2, hhk⟩ => hsign.1 ⟨hp2, ?_⟩, fun ⟨hp2, hhk⟩ => hsign.2 ⟨hp2, ?_⟩⟩
  · rw [hH, hK]; exact pow_le_pow_left₀ (norm_nonneg _) hhk 2
  · rw [hH, hK]; exact pow_le_pow_left₀ (norm_nonneg _) hhk 2

/-- **The concavity of `G`** in the proof of (1.12), by (1.14): if `x + t h ≠ 0` and `y + t k ≠ 0`
for every `t`, `G (t) = ψ (|x + t h|, |y + t k|)` is twice differentiable on `ℝ`
(`psi_line_smooth`), with `G'' ≤ 0` if `p ≥ 2` and `|h| ≤ |k|` and `G'' ≥ 0` if `p ≤ 2` and
`|k| ≤ |h|`: `G` is concave, resp. convex, on `ℝ`. -/
private theorem psi_line_of_ne {p : ℝ} (hp : 1 < p) (x y h k : H)
    (hx : ∀ t : ℝ, x + t • h ≠ 0) (hy : ∀ t : ℝ, y + t • k ≠ 0) :
    ((2 ≤ p ∧ ‖h‖ ≤ ‖k‖) → ConcaveOn ℝ univ (psiLine p x y h k)) ∧
      ((p ≤ 2 ∧ ‖k‖ ≤ ‖h‖) → ConvexOn ℝ univ (psiLine p x y h k)) := by
  have hcont : Continuous (psiLine p x y h k) := by
    have h1 : Continuous fun t : ℝ => ‖x + t • h‖ := by fun_prop
    have h2 : Continuous fun t : ℝ => ‖y + t • k‖ := by fun_prop
    unfold psiLine psi
    exact (h1.sub (h2.const_mul _)).mul ((h1.add h2).rpow_const fun _ => Or.inr (by linarith))
  have hs := fun t : ℝ => psi_line_smooth hp x y h k (Or.inl (hx t)) (Or.inl (hy t))
    (add_pos_of_pos_of_nonneg (norm_pos_iff.2 (hx t)) (norm_nonneg _))
  refine ⟨fun hA => ?_, fun hB => ?_⟩
  · refine concaveOn_of_hasDerivWithinAt2_nonpos (f' := psiLineD p x y h k)
      (f'' := deriv (psiLineD p x y h k)) convex_univ hcont.continuousOn
      (fun t _ => (hs t).1.hasDerivWithinAt) (fun t _ => ?_) (fun t _ => ?_)
    · obtain ⟨c, hc, -⟩ := (hs t).2
      rw [hc.deriv]; exact hc.hasDerivWithinAt
    · obtain ⟨c, hc, hc0, -⟩ := (hs t).2
      rw [hc.deriv]; exact hc0 hA
  · refine convexOn_of_hasDerivWithinAt2_nonneg (f' := psiLineD p x y h k)
      (f'' := deriv (psiLineD p x y h k)) convex_univ hcont.continuousOn
      (fun t _ => (hs t).1.hasDerivWithinAt) (fun t _ => ?_) (fun t _ => ?_)
    · obtain ⟨c, hc, -⟩ := (hs t).2
      rw [hc.deriv]; exact hc.hasDerivWithinAt
    · obtain ⟨c, hc, -, hc0⟩ := (hs t).2
      rw [hc.deriv]; exact hc0 hB

end Hilbert

/-! ### Burkholder's function (1.6) -/

/-- **Burkholder's function** (Burkholder 1988, (1.6)), as a function of `s = |x|`, `r = |y|`:
`U (x, y) = p (1 − 1/p*)^{p−1} (|x| − (p* − 1)|y|)(|x| + |y|)^{p−1}`, `p* = max (p, p/(p − 1))`.
Here `x` is the position of the subordinate martingale and `y` that of the dominating one. -/
noncomputable def burkholderU (p s r : ℝ) : ℝ :=
  p * (1 - 1 / max p (p / (p - 1))) ^ (p - 1) * (s - (max p (p / (p - 1)) - 1) * r) *
    (s + r) ^ (p - 1)

/-- For `p ≥ 2`, `p* = p`. -/
theorem max_div_sub_one_eq_self {p : ℝ} (hp : 2 ≤ p) : max p (p / (p - 1)) = p :=
  max_eq_left (by rw [div_le_iff₀ (by linarith)]; nlinarith)

private theorem max_eq_B {p : ℝ} (hp1 : 1 < p) (hp : p ≤ 2) : max p (p / (p - 1)) = p / (p - 1) :=
  max_eq_right (by rw [le_div_iff₀ (by linarith)]; nlinarith)

private theorem U_eq_A {p : ℝ} (hp : 2 ≤ p) (s r : ℝ) :
    burkholderU p s r = p * (1 - 1 / p) ^ (p - 1) * psi p s r := by
  unfold burkholderU psi; rw [max_div_sub_one_eq_self hp]; ring

private theorem U_eq_B {p : ℝ} (hp1 : 1 < p) (hp : p ≤ 2) (s r : ℝ) :
    burkholderU p s r = -(p * (1 / p) ^ (p - 1) / (p - 1)) * psi p r s := by
  unfold burkholderU psi; rw [max_eq_B hp1 hp]
  have hp0 : p - 1 ≠ 0 := by linarith
  have h1 : 1 - 1 / (p / (p - 1)) = 1 / p := by field_simp; ring
  rw [h1, add_comm r s]; field_simp; ring

/-! ### The elementary inequality (1.11) -/

/-- `log φ (p) = (p − 1) log (p − 1) − (p − 2) log p`, the logarithm of
`φ (p) = (p − 1)^{p−1} / p^{p−2}` (Burkholder's (1.11)); `log φ (1) = 0` (`0 · log 0 = 0`). -/
private noncomputable def logPhi (p : ℝ) : ℝ := (p - 1) * Real.log (p - 1) - (p - 2) * Real.log p

private theorem logPhi_hasDerivAt {p : ℝ} (hp : 1 < p) :
    HasDerivAt logPhi (Real.log (p - 1) + 1 - (Real.log p + (p - 2) / p)) p := by
  have h1 : HasDerivAt (fun x : ℝ => x - 1) 1 p := (hasDerivAt_id' p).sub_const 1
  have h2 : HasDerivAt (fun x : ℝ => x - 2) 1 p := (hasDerivAt_id' p).sub_const 2
  have hl1 := h1.log (by linarith : p - 1 ≠ 0)
  have hl2 := Real.hasDerivAt_log (by linarith : p ≠ 0)
  have h := (h1.mul hl1).sub (h2.mul hl2)
  change HasDerivAt (fun x => (x - 1) * Real.log (x - 1) - (x - 2) * Real.log x) _ p
  convert h using 1
  have : p - 1 ≠ 0 := by linarith
  field_simp

/-- `(log φ)'' (p) = 1/(p − 1) − 1/p − 2/p² = (2 − p) / (p² (p − 1))`. -/
private theorem logPhi_deriv_hasDerivAt {p : ℝ} (hp : 1 < p) :
    HasDerivAt (fun x => Real.log (x - 1) + 1 - (Real.log x + (x - 2) / x))
      ((2 - p) / (p ^ 2 * (p - 1))) p := by
  have h1 : HasDerivAt (fun x : ℝ => x - 1) 1 p := (hasDerivAt_id' p).sub_const 1
  have hl1 := h1.log (by linarith : p - 1 ≠ 0)
  have hl2 := Real.hasDerivAt_log (by linarith : p ≠ 0)
  have hq := ((hasDerivAt_id' p).sub_const 2).div (hasDerivAt_id' p) (by linarith : p ≠ 0)
  have h := (hl1.add_const 1).sub (hl2.add hq)
  convert h using 1
  have : p - 1 ≠ 0 := by linarith
  have : p ≠ 0 := by linarith
  field_simp
  ring

private theorem logPhi_continuousOn : ContinuousOn logPhi (Ici 1) := by
  have h1 : Continuous fun x : ℝ => (x - 1) * Real.log (x - 1) :=
    Real.continuous_mul_log.comp (continuous_id.sub continuous_const)
  have h2 : ContinuousOn (fun x : ℝ => (x - 2) * Real.log x) (Ici 1) :=
    (continuous_id.sub continuous_const).continuousOn.mul (Real.continuousOn_log.mono
      fun x hx => by simp only [mem_compl_iff, mem_singleton_iff]; linarith [mem_Ici.1 hx])
  exact h1.continuousOn.sub h2

private theorem logPhi_two : logPhi 2 = 0 := by norm_num [logPhi]

/-- `log φ` is convex on `[1, 2]` and vanishes at both ends, so `log φ ≤ 0` there. -/
private theorem logPhi_nonpos {p : ℝ} (hp1 : 1 ≤ p) (hp : p ≤ 2) : logPhi p ≤ 0 := by
  have hconv : ConvexOn ℝ (Icc 1 2) logPhi := by
    refine convexOn_of_hasDerivWithinAt2_nonneg
      (f' := fun x => Real.log (x - 1) + 1 - (Real.log x + (x - 2) / x))
      (f'' := fun x => (2 - x) / (x ^ 2 * (x - 1))) (convex_Icc 1 2)
      (logPhi_continuousOn.mono Icc_subset_Ici_self) (fun x hx => ?_) (fun x hx => ?_)
      (fun x hx => ?_) <;> rw [interior_Icc] at hx
    · exact (logPhi_hasDerivAt hx.1).hasDerivWithinAt
    · exact (logPhi_deriv_hasDerivAt hx.1).hasDerivWithinAt
    · exact div_nonneg (by linarith [hx.2]) (mul_nonneg (sq_nonneg _) (by linarith [hx.1]))
  have h := hconv.le_on_segment (x := 1) (y := 2) ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩
    (by rw [segment_eq_Icc (by norm_num)]; exact ⟨hp1, hp⟩)
  have e1 : logPhi 1 = 0 := by simp [logPhi]
  rwa [e1, logPhi_two, max_self] at h

/-- `log φ (p) ≥ log p − 1`, so `log φ → ∞`: `log φ (p) = log p − (p − 1) log (p / (p − 1))` and
`log (p / (p − 1)) ≤ 1 / (p − 1)`. -/
private theorem logPhi_ge {p : ℝ} (hp : 1 < p) : Real.log p - 1 ≤ logPhi p := by
  have hp1 : 0 < p - 1 := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < p) hp1)
  rw [Real.log_div (by linarith) hp1.ne'] at h
  have h' : (p - 1) * (Real.log p - Real.log (p - 1)) ≤ 1 :=
    calc (p - 1) * (Real.log p - Real.log (p - 1)) ≤ (p - 1) * (p / (p - 1) - 1) :=
          mul_le_mul_of_nonneg_left h hp1.le
      _ = 1 := by field_simp; ring
  unfold logPhi
  nlinarith [h']

/-- `log φ` is concave on `[2, ∞)`, vanishes at `2` and tends to `∞`, so `log φ ≥ 0` there. -/
private theorem logPhi_nonneg {p : ℝ} (hp : 2 ≤ p) : 0 ≤ logPhi p := by
  have hconc : ConcaveOn ℝ (Ici 2) logPhi := by
    refine concaveOn_of_hasDerivWithinAt2_nonpos
      (f' := fun x => Real.log (x - 1) + 1 - (Real.log x + (x - 2) / x))
      (f'' := fun x => (2 - x) / (x ^ 2 * (x - 1))) (convex_Ici 2)
      (logPhi_continuousOn.mono (Ici_subset_Ici.2 (by norm_num))) (fun x hx => ?_)
      (fun x hx => ?_) (fun x hx => ?_) <;> rw [interior_Ici] at hx <;> have hx' := mem_Ioi.1 hx
    · exact (logPhi_hasDerivAt (by linarith)).hasDerivWithinAt
    · exact (logPhi_deriv_hasDerivAt (by linarith)).hasDerivWithinAt
    · exact div_nonpos_of_nonpos_of_nonneg (by linarith)
        (mul_nonneg (sq_nonneg _) (by linarith))
  -- a point `p₂ ≥ p` with `log φ (p₂) ≥ 0`
  set p₂ := max p (Real.exp 1)
  have hp₂ : p ≤ p₂ := le_max_left _ _
  have h2 : 0 ≤ logPhi p₂ := by
    have h := logPhi_ge (p := p₂) (by linarith)
    have : 1 ≤ Real.log p₂ := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) (le_max_right _ _)
    linarith
  have h := hconc.ge_on_segment (x := 2) (y := p₂) self_mem_Ici (mem_Ici.2 (hp.trans hp₂))
    (by rw [segment_eq_Icc (hp.trans hp₂)]; exact ⟨hp, hp₂⟩)
  rw [logPhi_two] at h
  exact (le_min le_rfl h2).trans h

private theorem phi_eq_exp {p : ℝ} (hp : 1 < p) :
    (p - 1) ^ (p - 1) / p ^ (p - 2) = Real.exp (logPhi p) := by
  rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos (by linarith), ← Real.exp_sub,
    logPhi]
  ring_nf

/-- **(1.11)**, `1 < p ≤ 2`: `(p − 1)^{p−1} / p^{p−2} ≤ 1`. -/
private theorem phi_le_one {p : ℝ} (hp1 : 1 < p) (hp : p ≤ 2) :
    (p - 1) ^ (p - 1) / p ^ (p - 2) ≤ 1 := by
  rw [phi_eq_exp hp1, Real.exp_le_one_iff]; exact logPhi_nonpos hp1.le hp

/-- **(1.11)**, `p ≥ 2`: `(p − 1)^{p−1} / p^{p−2} ≥ 1`. -/
private theorem one_le_phi {p : ℝ} (hp : 2 ≤ p) : 1 ≤ (p - 1) ^ (p - 1) / p ^ (p - 2) := by
  rw [phi_eq_exp (by linarith), Real.one_le_exp_iff]; exact logPhi_nonneg hp

/-! ### The majorization `v ≤ u` (1.10) -/

/-- Burkholder's `F (t) = α_p (1 − P t) − (1 − t)^p + (P − 1)^p t^p`, `α_p = p (1 − 1/P)^{p−1}`:
for `P = p*`, `U − V` on `|x| + |y| = 1`, as a function of the norm `t` of the dominating
martingale's position. -/
private noncomputable def bF (p P t : ℝ) : ℝ :=
  p * (1 - 1 / P) ^ (p - 1) * (1 - P * t) - (1 - t) ^ p + (P - 1) ^ p * t ^ p

/-- `F'`. -/
private noncomputable def bF1 (p P t : ℝ) : ℝ :=
  -(p * (1 - 1 / P) ^ (p - 1) * P) + p * (1 - t) ^ (p - 1) + p * (P - 1) ^ p * t ^ (p - 1)

/-- `F''`. -/
private noncomputable def bF2 (p P t : ℝ) : ℝ :=
  -(p * (p - 1) * (1 - t) ^ (p - 2)) + p * (p - 1) * (P - 1) ^ p * t ^ (p - 2)

private theorem bF_hasDerivAt (p P : ℝ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (bF p P) (bF1 p P t) t ∧ HasDerivAt (bF1 p P) (bF2 p P t) t := by
  have hl : HasDerivAt (fun u : ℝ => 1 - u) (-1) t := by
    simpa using (hasDerivAt_id' t).const_sub 1
  have h1t : 1 - t ≠ 0 := by linarith
  constructor
  · have hA := (((hasDerivAt_id' t).const_mul P).const_sub 1).const_mul
      (p * (1 - 1 / P) ^ (p - 1))
    have hB := hl.rpow_const (p := p) (Or.inl h1t)
    have hC := (Real.hasDerivAt_rpow_const (p := p) (Or.inl ht0.ne')).const_mul ((P - 1) ^ p)
    change HasDerivAt (fun u => p * (1 - 1 / P) ^ (p - 1) * (1 - P * u) - (1 - u) ^ p +
      (P - 1) ^ p * u ^ p) _ t
    convert (hA.sub hB).add hC using 1
    unfold bF1; ring
  · have hB := hl.rpow_const (p := p - 1) (Or.inl h1t)
    have hC := (Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl ht0.ne')).const_mul
      (p * (P - 1) ^ p)
    change HasDerivAt (fun u => -(p * (1 - 1 / P) ^ (p - 1) * P) + p * (1 - u) ^ (p - 1) +
      p * (P - 1) ^ p * u ^ (p - 1)) _ t
    convert ((hB.const_mul p).const_add (-(p * (1 - 1 / P) ^ (p - 1) * P))).add hC using 1
    rw [show p - 1 - 1 = p - 2 by ring]
    unfold bF2; ring

private theorem continuous_bF {p : ℝ} (hp : 0 < p) (P : ℝ) : Continuous (bF p P) := by
  unfold bF
  exact ((continuous_const.mul (continuous_const.sub (continuous_const.mul continuous_id))).sub
    ((continuous_const.sub continuous_id).rpow_const fun _ => Or.inr hp.le)).add
    (continuous_const.mul (continuous_id.rpow_const fun _ => Or.inr hp.le))

/-- `F (1/P) = F' (1/P) = 0`. -/
private theorem bF_crit {p P : ℝ} (hP : 1 < P) : bF p P (1 / P) = 0 ∧ bF1 p P (1 / P) = 0 := by
  have hP0 : 0 < P := by linarith
  have hβ : 0 ≤ P - 1 := by linarith
  have e : 1 - 1 / P = (P - 1) * (1 / P) := by field_simp
  have hpow : ∀ a : ℝ, (P - 1) ^ a * (1 / P) ^ a = (1 - 1 / P) ^ a := fun a => by
    rw [e, Real.mul_rpow hβ (by positivity)]
  have e0 : 1 - P * (1 / P) = 0 := by field_simp; ring
  constructor
  · unfold bF
    rw [e0, hpow p]; ring
  · have hPp : (P - 1) ^ p = (P - 1) * (P - 1) ^ (p - 1) := by
      conv_lhs => rw [show p = 1 + (p - 1) by ring]
      rw [Real.rpow_add (by linarith), Real.rpow_one]
    unfold bF1
    rw [hPp]
    linear_combination (p * (P - 1)) * hpow (p - 1)

/-- `F'' (t) = p (p − 1) ((d t)^{p−2} − (1 − t)^{p−2})` with `d = (P − 1)^{p/(p−2)}`
(`p ≠ 2`). -/
private theorem bF2_eq {p P t : ℝ} (hp2 : p ≠ 2) (hP : 1 < P) (ht : 0 < t) :
    bF2 p P t = p * (p - 1) * (((P - 1) ^ (p / (p - 2)) * t) ^ (p - 2) - (1 - t) ^ (p - 2)) := by
  have hβ : 0 ≤ P - 1 := by linarith
  rw [Real.mul_rpow (Real.rpow_nonneg hβ _) ht.le, ← Real.rpow_mul hβ,
    div_mul_cancel₀ _ (sub_ne_zero.2 hp2)]
  unfold bF2; ring

/-- A convex function on `[a, b]` with `F (c) = F' (c) = 0` at a point `c ∈ [a, b]` is `≥ 0` on
`[a, b]` (it lies above its tangent at `c`). -/
private theorem nonneg_of_convexOn_tangent {F : ℝ → ℝ} {a b c : ℝ} (hF : ConvexOn ℝ (Icc a b) F)
    (hc : c ∈ Icc a b) (hd : HasDerivAt F 0 c) (h0 : F c = 0) {t : ℝ} (ht : t ∈ Icc a b) :
    0 ≤ F t := by
  rcases lt_trichotomy t c with htc | rfl | htc
  · have := hF.slope_le_of_hasDerivAt ht hc htc hd
    rw [slope_def_field, h0, div_le_iff₀ (sub_pos.2 htc)] at this
    linarith
  · rw [h0]
  · have := hF.le_slope_of_hasDerivAt hc ht htc hd
    rw [slope_def_field, h0, le_div_iff₀ (sub_pos.2 htc)] at this
    linarith

/-- A concave function on `[a, b]` that is `≥ 0` at `a` and at `b` is `≥ 0` on `[a, b]`. -/
private theorem nonneg_of_concaveOn {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ConcaveOn ℝ (Icc a b) F) (ha : 0 ≤ F a) (hb : 0 ≤ F b) {t : ℝ} (ht : t ∈ Icc a b) :
    0 ≤ F t :=
  (le_min ha hb).trans (hF.ge_on_segment ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ (by rwa [segment_eq_Icc hab]))

/-- `F` is convex (resp. concave) on a subinterval `[a, b]` of `[0, 1]` on whose interior
`F'' ≥ 0` (resp. `≤ 0`). -/
private theorem bF_convexOn {p P a b : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (hb : b ≤ 1)
    (h2 : ∀ t, a < t → t < b → 0 ≤ bF2 p P t) : ConvexOn ℝ (Icc a b) (bF p P) := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (f' := bF1 p P) (f'' := bF2 p P) (convex_Icc a b)
    (continuous_bF hp P).continuousOn (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_) <;>
    rw [interior_Icc] at ht
  · exact (bF_hasDerivAt p P (by linarith [ht.1]) (by linarith [ht.2])).1.hasDerivWithinAt
  · exact (bF_hasDerivAt p P (by linarith [ht.1]) (by linarith [ht.2])).2.hasDerivWithinAt
  · exact h2 t ht.1 ht.2

private theorem bF_concaveOn {p P a b : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (hb : b ≤ 1)
    (h2 : ∀ t, a < t → t < b → bF2 p P t ≤ 0) : ConcaveOn ℝ (Icc a b) (bF p P) := by
  refine concaveOn_of_hasDerivWithinAt2_nonpos (f' := bF1 p P) (f'' := bF2 p P) (convex_Icc a b)
    (continuous_bF hp P).continuousOn (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_) <;>
    rw [interior_Icc] at ht
  · exact (bF_hasDerivAt p P (by linarith [ht.1]) (by linarith [ht.2])).1.hasDerivWithinAt
  · exact (bF_hasDerivAt p P (by linarith [ht.1]) (by linarith [ht.2])).2.hasDerivWithinAt
  · exact h2 t ht.1 ht.2

/-- `α_p = p (1 − 1/p)^{p−1} = (p − 1)^{p−1} / p^{p−2}`. -/
private theorem alpha_eq_phi {p : ℝ} (hp : 1 < p) :
    p * (1 - 1 / p) ^ (p - 1) = (p - 1) ^ (p - 1) / p ^ (p - 2) := by
  have hp0 : 0 < p := by linarith
  have e : 1 - 1 / p = (p - 1) / p := by field_simp
  have hpp : p ^ (p - 1) = p ^ (p - 2) * p := by
    rw [show p - 1 = p - 2 + 1 by ring, Real.rpow_add_one hp0.ne']
  have hp2 : p ^ (p - 2) ≠ 0 := (Real.rpow_pos_of_pos hp0 _).ne'
  rw [e, Real.div_rpow (by linarith) hp0.le, hpp]
  field_simp

/-- **`F ≥ 0` on `[0, 1]`** (Burkholder 1988, proof of (1.10)). If `p = 2`, `F ≡ 0`. With
`d = (p* − 1)^{p/(p−2)}` and `s₀ = 1/(1 + d)` (Burkholder asserts that such an `s₀` exists; this
value is read off from `F''`, `bF2_eq`): if `p > 2`, `F` is concave on `[0, s₀]` and convex on
`[s₀, 1]`, `s₀ ≤ 1/p*`; `F (1/p*) = F' (1/p*) = 0` gives `F ≥ 0` on `[s₀, 1]`, and `F (0) ≥ 0` by
(1.11) gives it on `[0, s₀]`. If `p < 2`, `F` is convex on `[0, s₀]`, `s₀ ≥ 1/p*`, and concave on
`[s₀, 1]`, and `F (1) ≥ 0` by (1.11). -/
private theorem bF_nonneg {p : ℝ} (hp : 1 < p) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ bF p (max p (p / (p - 1))) t := by
  have hp0 : 0 < p := by linarith
  set P := max p (p / (p - 1)) with hPdef
  have hP : 1 < P := lt_of_lt_of_le hp (le_max_left _ _)
  have hβ : 0 < P - 1 := by linarith
  have hpp : 0 < p * (p - 1) := mul_pos hp0 (by linarith)
  obtain ⟨hcrit, hcrit1⟩ := bF_crit (p := p) hP
  have hd1 : HasDerivAt (bF p P) 0 (1 / P) := by
    rw [← hcrit1]
    exact (bF_hasDerivAt p P (by positivity) ((div_lt_one (by linarith)).2 hP)).1
  have hcP : 1 / P ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, (div_lt_one (by linarith)).2 hP⟩
  rcases lt_trichotomy p 2 with hp2 | rfl | hp2
  · -- `1 < p < 2`: `P = p / (p − 1)`
    have hPe : P = p / (p - 1) := max_eq_right (by rw [le_div_iff₀ (by linarith)]; nlinarith)
    set d := (P - 1) ^ (p / (p - 2)) with hd
    have hd0 : 0 < d := Real.rpow_pos_of_pos hβ _
    have hβ1 : 1 ≤ P - 1 := by
      rw [hPe, le_sub_iff_add_le, le_div_iff₀ (by linarith)]; linarith
    have hd1' : d ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hβ1
      (div_nonpos_of_nonneg_of_nonpos hp0.le (by linarith))
    set s₀ := 1 / (1 + d)
    have hs₀1 : s₀ ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    have hPs₀ : 1 / P ≤ s₀ := one_div_le_one_div_of_le (by linarith) (by linarith)
    have hdt : ∀ u, 0 < u → (u ≤ s₀ ↔ d * u ≤ 1 - u) := fun u hu => by
      rw [le_div_iff₀ (by linarith)]; constructor <;> intro h <;> linarith
    -- convex on `[0, s₀]`, concave on `[s₀, 1]`
    have hconv : ConvexOn ℝ (Icc 0 s₀) (bF p P) := bF_convexOn hp0 le_rfl hs₀1 fun u hu0 hu1 => by
      rw [bF2_eq hp2.ne hP hu0]
      refine mul_nonneg hpp.le (sub_nonneg.2 (Real.rpow_le_rpow_of_nonpos (by positivity)
        ((hdt u hu0).1 hu1.le) (by linarith)))
    have hconc : ConcaveOn ℝ (Icc s₀ 1) (bF p P) := bF_concaveOn hp0 (by positivity) le_rfl
      fun u hu0 hu1 => by
        have hu : 0 < u := lt_of_le_of_lt (by positivity) hu0
        rw [bF2_eq hp2.ne hP hu]
        have : 1 - u ≤ d * u := by
          by_contra hc; exact absurd ((hdt u hu).2 (by linarith)) (not_le.2 hu0)
        exact mul_nonpos_of_nonneg_of_nonpos hpp.le (sub_nonpos.2 (Real.rpow_le_rpow_of_nonpos
          (by linarith) this (by linarith)))
    have hleft : ∀ u ∈ Icc 0 s₀, 0 ≤ bF p P u := fun u hu =>
      nonneg_of_convexOn_tangent hconv ⟨hcP.1.le, hPs₀⟩ hd1 hcrit hu
    -- `F (1) = (P − 1) ((P − 1)^{p−1} − α_p) ≥ 0` by (1.11)
    have hF1 : 0 ≤ bF p P 1 := by
      have hφ := phi_le_one hp hp2.le
      have hα : p * (1 - 1 / P) ^ (p - 1) = 1 / p ^ (p - 2) := by
        rw [hPe, show 1 - 1 / (p / (p - 1)) = 1 / p by field_simp; ring,
          Real.div_rpow zero_le_one hp0.le, Real.one_rpow,
          show p - 1 = p - 2 + 1 by ring, Real.rpow_add_one hp0.ne']
        field_simp
      have hb : (P - 1) ^ (p - 1) = 1 / (p - 1) ^ (p - 1) := by
        rw [hPe, show p / (p - 1) - 1 = 1 / (p - 1) by field_simp; ring,
          Real.div_rpow zero_le_one (by linarith), Real.one_rpow]
      have hPp : (P - 1) ^ p = (P - 1) * (P - 1) ^ (p - 1) := by
        conv_lhs => rw [show p = 1 + (p - 1) by ring]
        rw [Real.rpow_add hβ, Real.rpow_one]
      have hq : 1 / p ^ (p - 2) ≤ 1 / (p - 1) ^ (p - 1) := by
        rw [div_le_iff₀ (Real.rpow_pos_of_pos hp0 _)] at hφ
        exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by linarith) _) hφ |>.trans_eq'
          (by rw [one_mul])
      unfold bF
      rw [hα, hPp, hb, sub_self, Real.zero_rpow hp0.ne', Real.one_rpow]
      nlinarith [hq, hβ]
    rcases le_total t s₀ with hts | hts
    · exact hleft t ⟨ht0, hts⟩
    · exact nonneg_of_concaveOn hs₀1 hconc (hleft s₀ ⟨by positivity, le_rfl⟩) hF1 ⟨hts, ht1⟩
  · -- `p = 2`: `F ≡ 0`
    have hP2 : P = 2 := by rw [hPdef]; norm_num
    rw [hP2]
    unfold bF
    norm_num [Real.rpow_two]
    ring_nf
    exact le_rfl
  · -- `p > 2`: `P = p`
    have hPe : P = p := max_eq_left (by rw [div_le_iff₀ (by linarith)]; nlinarith)
    set d := (P - 1) ^ (p / (p - 2)) with hd
    have hd0 : 0 < d := Real.rpow_pos_of_pos hβ _
    have hβ1 : 1 < P - 1 := by rw [hPe]; linarith
    have hdβ : P - 1 < d := by
      conv_lhs => rw [← Real.rpow_one (P - 1)]
      exact Real.rpow_lt_rpow_of_exponent_lt hβ1 (by rw [one_lt_div (by linarith)]; linarith)
    set s₀ := 1 / (1 + d)
    have hs₀0 : 0 ≤ s₀ := by positivity
    have hs₀P : s₀ ≤ 1 / P := one_div_le_one_div_of_le (by linarith) (by linarith)
    have hdt : ∀ u, 0 < u → (u ≤ s₀ ↔ d * u ≤ 1 - u) := fun u hu => by
      rw [le_div_iff₀ (by linarith)]; constructor <;> intro h <;> linarith
    -- concave on `[0, s₀]`, convex on `[s₀, 1]`
    have hconc : ConcaveOn ℝ (Icc 0 s₀) (bF p P) := bF_concaveOn hp0 le_rfl
      (hs₀P.trans hcP.2.le) fun u hu0 hu1 => by
        rw [bF2_eq hp2.ne' hP hu0]
        exact mul_nonpos_of_nonneg_of_nonpos hpp.le (sub_nonpos.2 (Real.rpow_le_rpow
          (by positivity) ((hdt u hu0).1 hu1.le) (by linarith)))
    have hconv : ConvexOn ℝ (Icc s₀ 1) (bF p P) := bF_convexOn hp0 hs₀0 le_rfl fun u hu0 hu1 => by
      have hu : 0 < u := lt_of_le_of_lt hs₀0 hu0
      rw [bF2_eq hp2.ne' hP hu]
      have : 1 - u ≤ d * u := by
        by_contra hc; exact absurd ((hdt u hu).2 (by linarith)) (not_le.2 hu0)
      exact mul_nonneg hpp.le (sub_nonneg.2 (Real.rpow_le_rpow (by linarith) this (by linarith)))
    have hright : ∀ u ∈ Icc s₀ 1, 0 ≤ bF p P u := fun u hu =>
      nonneg_of_convexOn_tangent hconv ⟨hs₀P, hcP.2.le⟩ hd1 hcrit hu
    -- `F (0) = α_p − 1 ≥ 0` by (1.11)
    have hF0 : 0 ≤ bF p P 0 := by
      have hφ := one_le_phi hp2.le
      unfold bF
      rw [hPe, alpha_eq_phi hp, Real.zero_rpow hp0.ne', sub_zero, Real.one_rpow]
      linarith
    rcases le_total t s₀ with hts | hts
    · exact nonneg_of_concaveOn hs₀0 hconc hF0 (hright s₀ ⟨le_rfl, (hs₀P.trans hcP.2.le)⟩)
        ⟨ht0, hts⟩
    · exact hright t ⟨hts, ht1⟩

/-- **Majorization** (Burkholder 1988, (1.10)): `V ≤ U`, that is
`|x|^p − (p* − 1)^p |y|^p ≤ U (x, y)`, with `s = |x|` (subordinate), `r = |y|` (dominating). If
`s + r = 0` both sides vanish; otherwise, by homogeneity,
`U (s, r) − V (s, r) = (s + r)^p F (r / (s + r)) ≥ 0` (`bF_nonneg`). -/
theorem burkholderU_ge {p s r : ℝ} (hp : 1 < p) (hs : 0 ≤ s) (hr : 0 ≤ r) :
    s ^ p - (max p (p / (p - 1)) - 1) ^ p * r ^ p ≤ burkholderU p s r := by
  have hp0 : 0 < p := by linarith
  rcases (add_nonneg hs hr).eq_or_lt with hw | hw
  · have hs0 : s = 0 := by linarith
    have hr0 : r = 0 := by linarith
    subst hs0 hr0
    simp [burkholderU, Real.zero_rpow hp0.ne']
  · have ht0 : 0 ≤ r / (s + r) := div_nonneg hr hw.le
    have ht1 : r / (s + r) ≤ 1 := (div_le_one hw).2 (by linarith)
    have hF := bF_nonneg hp ht0 ht1
    have hwp : 0 < (s + r) ^ p := Real.rpow_pos_of_pos hw p
    have key : burkholderU p s r - (s ^ p - (max p (p / (p - 1)) - 1) ^ p * r ^ p) =
        (s + r) ^ p * bF p (max p (p / (p - 1))) (r / (s + r)) := by
      unfold burkholderU bF
      have e1 : 1 - r / (s + r) = s / (s + r) := by field_simp; ring
      rw [e1, Real.div_rpow hs hw.le, Real.div_rpow hr hw.le, Real.rpow_sub_one hw.ne']
      field_simp
      ring
    nlinarith [mul_nonneg hwp.le hF]

/-! ### The concavity of `U` along lines: the proof of (1.12), and Remark 1.2 -/

/-- `α_p = p (1 − 1/p)^{p−1} ≥ 0`. -/
private theorem alpha_nonneg {p : ℝ} (hp : 1 < p) : 0 ≤ p * (1 - 1 / p) ^ (p - 1) := by
  have h : 0 ≤ 1 - 1 / p := by rw [sub_nonneg, div_le_one (by linarith)]; linarith
  exact mul_nonneg (by linarith) (Real.rpow_nonneg h _)

/-- **The concavity of `G`** in the proof of (1.12), by (1.14), for `U`: if `x + t h ≠ 0`,
`y + t k ≠ 0` for every `t` and `|h| ≤ |k|`, `t ↦ U (x + t h, y + t k)` is concave on `ℝ`
(`psi_line_of_ne`). -/
private theorem burkholderU_concaveOn_line_of_ne {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {p : ℝ} (hp : 1 < p) (x y h k : H) (hhk : ‖h‖ ≤ ‖k‖)
    (hx : ∀ t : ℝ, x + t • h ≠ 0) (hy : ∀ t : ℝ, y + t • k ≠ 0) :
    ConcaveOn ℝ univ fun t : ℝ => burkholderU p ‖x + t • h‖ ‖y + t • k‖ := by
  rcases le_total 2 p with h2 | h2
  · have e : (fun t : ℝ => burkholderU p ‖x + t • h‖ ‖y + t • k‖) =
        fun t => (p * (1 - 1 / p) ^ (p - 1)) • psiLine p x y h k t := by
      funext t; rw [U_eq_A h2, psiLine, smul_eq_mul]
    rw [e]
    exact ((psi_line_of_ne hp x y h k hx hy).1 ⟨h2, hhk⟩).smul
      (alpha_nonneg hp)
  · have e : (fun t : ℝ => burkholderU p ‖x + t • h‖ ‖y + t • k‖) =
        fun t => (p * (1 / p) ^ (p - 1) / (p - 1)) • (-psiLine p y x k h) t := by
      funext t; rw [U_eq_B hp h2, Pi.neg_apply, psiLine, smul_eq_mul]; ring
    rw [e]
    exact ((psi_line_of_ne hp y x k h hy hx).2 ⟨h2, hhk⟩).neg.smul
      (div_nonneg (by positivity) (by linarith))

/-- `‖(v, δ)‖ = √(‖v‖² + δ²)` in `H ⊕ ℝ` (`WithLp 2 (H × ℝ)`). -/
private theorem norm_toLp_shift {H : Type*} [NormedAddCommGroup H] (v : H) (δ : ℝ) :
    ‖(WithLp.toLp 2 (v, δ) : WithLp 2 (H × ℝ))‖ = √(‖v‖ ^ 2 + δ ^ 2) := by
  rw [WithLp.prod_norm_eq_of_L2]
  simp [Real.norm_eq_abs, sq_abs]

/-- In `H ⊕ ℝ`, the line through `(v, δ)` with direction `(w, 0)`: `(v + t w, δ)`. -/
private theorem toLp_line {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (v w : H)
    (δ t : ℝ) : (WithLp.toLp 2 (v, δ) : WithLp 2 (H × ℝ)) + t • WithLp.toLp 2 (w, 0) =
      WithLp.toLp 2 (v + t • w, δ) := by
  rw [← WithLp.toLp_smul, ← WithLp.toLp_add, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]

private theorem toLp_ne_zero {H : Type*} [NormedAddCommGroup H] (v : H) {δ : ℝ} (hδ : δ ≠ 0) :
    (WithLp.toLp 2 (v, δ) : WithLp 2 (H × ℝ)) ≠ 0 := fun h =>
  hδ (by simpa using congrArg (fun z : WithLp 2 (H × ℝ) => z.snd) h)

/-- A pointwise limit of concave functions on `ℝ` is concave. -/
private theorem concaveOn_univ_of_tendsto {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ m, ConcaveOn ℝ univ (f m)) (hlim : ∀ t, Tendsto (fun m => f m t) atTop (𝓝 (g t))) :
    ConcaveOn ℝ univ g := by
  refine ⟨convex_univ, fun a _ b _ μ ν hμ hν hμν => ?_⟩
  exact le_of_tendsto_of_tendsto' (((hlim a).const_smul μ).add ((hlim b).const_smul ν))
    (hlim _) fun m => (hf m).2 (mem_univ a) (mem_univ b) hμ hν hμν

private theorem continuous_burkholderU {p : ℝ} (hp : 1 < p) :
    Continuous fun z : ℝ × ℝ => burkholderU p z.1 z.2 := by
  unfold burkholderU
  exact (continuous_const.mul (continuous_fst.sub (continuous_const.mul continuous_snd))).mul
    ((continuous_fst.add continuous_snd).rpow_const fun _ => Or.inr (by linarith))

/-- `δ ↦ U (√(a² + δ²), √(b² + δ²))` is continuous, with value `U (a, b)` at `δ = 0` for
`a, b ≥ 0`. -/
private theorem tendsto_burkholderU_shift {p a b : ℝ} (hp : 1 < p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Tendsto (fun m : ℕ => burkholderU p √(a ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2)
      √(b ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2)) atTop (𝓝 (burkholderU p a b)) := by
  have hc : Continuous fun δ : ℝ => burkholderU p √(a ^ 2 + δ ^ 2) √(b ^ 2 + δ ^ 2) :=
    (continuous_burkholderU hp).comp
      ((Real.continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2))).prodMk
        (Real.continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2))))
  have := (hc.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  simpa [Function.comp_def, Real.sqrt_sq ha, Real.sqrt_sq hb] using this

/-- **Concavity of Burkholder's function along lines** (Burkholder 1988, Remark 1.2, (1.17)):
for `x, y, h, k` in a real inner product space with `|h| ≤ |k|`,
`t ↦ U (x + t h, y + t k)` is concave on `ℝ` (`x` the position of the subordinate martingale,
`y` that of the dominating one). Gap of the source: the paper states this without proof. It is
completed here from two steps of the paper, an assembly of the formalization: the proof of (1.12)
covers the lines on which `x + t h` and `y + t k` never vanish
(`burkholderU_concaveOn_line_of_ne`), and the other lines are reached by the device of the proof of
(1.8): in `H ⊕ ℝ` (`WithLp 2 (H × ℝ)`),
the lines through `(x, δ)` and `(y, δ)` with directions `(h, 0)` and `(k, 0)` never vanish for
`δ ≠ 0`, so `t ↦ U (√(|x + t h|² + δ²), √(|y + t k|² + δ²))` is concave, and these functions tend
to `t ↦ U (|x + t h|, |y + t k|)` as `δ → 0` (`concaveOn_univ_of_tendsto`). -/
theorem burkholderU_concaveOn_line {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {p : ℝ} (hp : 1 < p) (x y h k : H) (hhk : ‖h‖ ≤ ‖k‖) :
    ConcaveOn ℝ univ fun t : ℝ => burkholderU p ‖x + t • h‖ ‖y + t • k‖ := by
  have hδ : ∀ m : ℕ, ConcaveOn ℝ univ fun t : ℝ =>
      burkholderU p √(‖x + t • h‖ ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2)
        √(‖y + t • k‖ ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2) := fun m => by
    have hδ0 : (1 / ((m : ℝ) + 1)) ≠ 0 := by positivity
    have := burkholderU_concaveOn_line_of_ne hp (WithLp.toLp 2 (x, 1 / ((m : ℝ) + 1)))
      (WithLp.toLp 2 (y, 1 / ((m : ℝ) + 1))) (WithLp.toLp 2 (h, (0 : ℝ)))
      (WithLp.toLp 2 (k, (0 : ℝ))) (by rwa [WithLp.norm_toLp_fst, WithLp.norm_toLp_fst])
      (fun t => by rw [toLp_line]; exact toLp_ne_zero _ hδ0)
      (fun t => by rw [toLp_line]; exact toLp_ne_zero _ hδ0)
    simpa only [toLp_line, norm_toLp_shift] using this
  exact concaveOn_univ_of_tendsto hδ fun t =>
    tendsto_burkholderU_shift hp (norm_nonneg _) (norm_nonneg _)

/-! ### Burkholder's function in Burkholder's notation -/

section Fun

variable {H : Type*} [NormedAddCommGroup H]

/-- `u_p (x, y) = U (|y|, |x|)`, `U = burkholderU`. -/
theorem burkholderFun_eq_burkholderU (p : ℝ) (x y : H) :
    burkholderFun p x y = burkholderU p ‖y‖ ‖x‖ := by
  rw [burkholderFun, burkholderU, add_comm ‖x‖]

/-- **Majorization** (Burkholder 1988, (1.10)): `v_p ≤ u_p`, that is
`|y|^p − (p* − 1)^p |x|^p ≤ u_p (x, y)` (`burkholderU_ge`). -/
theorem burkholderFun_ge {p : ℝ} (hp : 1 < p) (x y : H) :
    ‖y‖ ^ p - (max p (p / (p - 1)) - 1) ^ p * ‖x‖ ^ p ≤ burkholderFun p x y := by
  rw [burkholderFun_eq_burkholderU]
  exact burkholderU_ge hp (norm_nonneg y) (norm_nonneg x)

/-- **Concavity along lines** (Burkholder 1988, Remark 1.2, (1.17)): in a real inner product
space, if `|k| ≤ |h|`, then `t ↦ u_p (x + t h, y + t k)` is concave on `ℝ`
(`burkholderU_concaveOn_line`). -/
theorem burkholderFun_concaveOn_line [InnerProductSpace ℝ H] {p : ℝ} (hp : 1 < p) (x y h k : H)
    (hk : ‖k‖ ≤ ‖h‖) :
    ConcaveOn ℝ univ fun t : ℝ => burkholderFun p (x + t • h) (y + t • k) := by
  simp only [burkholderFun_eq_burkholderU]
  exact burkholderU_concaveOn_line hp y x k h hk

/-- For `p ≥ 2`: `u_p (x, y) = p (1 − 1/p)^{p−1} (|y| − (p − 1) |x|) (|x| + |y|)^{p−1}`. -/
theorem burkholderFun_of_two_le {p : ℝ} (hp : 2 ≤ p) (x y : H) :
    burkholderFun p x y =
      p * (1 - 1 / p) ^ (p - 1) * (‖y‖ - (p - 1) * ‖x‖) * (‖x‖ + ‖y‖) ^ (p - 1) := by
  rw [burkholderFun, max_div_sub_one_eq_self hp]

end Fun

end BanachProbability.Burkholder
