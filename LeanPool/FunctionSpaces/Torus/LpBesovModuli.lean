/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Torus.LpJackson
public import LeanPool.FunctionSpaces.MeasureSpaces.Besov.Basic
public import LeanPool.FunctionSpaces.ApproximationSpaces.Moduli

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Besov spaces on the torus through moduli of smoothness, for all `1 ≤ p < ∞`

For `1 ≤ p < ∞` and an order `r ≥ 1`, the modulus of smoothness `ω_r(f, 2^(-k))_p` of
`f ∈ L_p(𝕋^d)` is compatible with the trigonometric polynomials (`Torus.lpModulusData`):

* Jackson's inequality `E_{2^k}(f)_p ≤ 2^r C ω_r(f, 2^(-k))_p` for `k ≥ 1`
  (`Torus.approxError_trigScheme_le` and the halving of the step,
  `Torus.lpModulus_le_two_pow_mul_succ`);
* the inverse inequality `ω_r(a, 2^(-k))_p ≤ C 2^(-(k-j) r) ‖a‖_p` for trigonometric polynomials
  of degree `< 2^j` (`Torus.lpModulus_le_of_mem_trigPolyLp`).

Hence, for `0 < s < r` and `1 ≤ q ≤ ∞`, the Besov space `B^s_{p,q}(𝕋^d)` of the trigonometric
scheme is described by moduli of smoothness (`Torus.memBesov_iff_modNorm_lt_top_lp`):

`f ∈ B^s_{p,q}(𝕋^d) ↔ ‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞`,

with equivalent quasi-norms (`Torus.approxNormDyadic_le_modNorm_lp`,
`Torus.modNorm_le_approxNormDyadic_lp`).
-/

@[expose] public section

open MeasureTheory UnitAddTorus
open scoped ENNReal TorusHaar

open ENNReal (lqNorm dyadicWeight)

namespace Torus

variable {d : Type*} [Fintype d] {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (d) in
/-- **The modulus of order `r` is compatible with the trigonometric polynomials in `L_p(𝕋^d)`**,
with inverse order `r`: Jackson's inequality from level `1` on, and the inverse inequality. -/
noncomputable def lpModulusData (hp : p ≠ ∞) (r : ℕ) :
    ApproximationScheme.ModulusData ((trigScheme d).toLp volume p) r where
  modulus f k := Rd.lpModulus p r f k
  add_le f g k := Rd.lpModulus_add_le r f g k
  C0 := 2 ^ r
  C0_ne_top := by simp
  le_enorm f k := Rd.lpModulus_le r f k
  jacksonStart := 1
  CJ := Rd.jacksonConst (EuclideanSpace ℝ d) r p * 2 ^ r
  CJ_ne_top := ENNReal.mul_ne_top (Rd.jacksonConst_ne_top Fact.out hp r) (by simp)
  jackson f k hk := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    refine (approxError_trigScheme_le hp r k' f).trans ?_
    rw [mul_assoc]
    exact mul_le_mul' le_rfl (lpModulus_le_two_pow_mul_succ r k' f)
  CB := bernsteinConst d r
  CB_ne_top := bernsteinConst_ne_top r
  inverse _ _ _ ha := lpModulus_le_of_mem_trigPolyLp hp r (mem_toLp_trigScheme_iff.1 ha)

/-- **The approximation quasi-norm is at most the moduli quasi-norm** on `L_p(𝕋^d)`:
`‖f‖_{A^s_q} ≤ C (‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q})`. -/
theorem approxNormDyadic_le_modNorm_lp (hp : p ≠ ∞) (r : ℕ) {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ((trigScheme d).toLp volume p).approxNormDyadic s q f ≤
      (lpModulusData d hp r).directConst s * (lpModulusData d hp r).modNorm s q f :=
  (lpModulusData d hp r).approxNormDyadic_le_modNorm hq f

/-- **The moduli quasi-norm is at most the approximation quasi-norm** on `L_p(𝕋^d)`, for
`0 ≤ s < r`. -/
theorem modNorm_le_approxNormDyadic_lp (hp : p ≠ ∞) {r : ℕ} {s : ℝ} (hs : 0 ≤ s) (hsr : s < r)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    (lpModulusData d hp r).modNorm s q f ≤
      (lpModulusData d hp r).inverseConst s *
        ((trigScheme d).toLp volume p).approxNormDyadic s q f :=
  (lpModulusData d hp r).modNorm_le_approxNormDyadic hq hs hsr f

/-- **Besov spaces on the torus by moduli of smoothness, for all `1 ≤ p < ∞`**: for `0 < s < r`
and `1 ≤ q ≤ ∞`, `f ∈ B^s_{p,q}(𝕋^d)` (the approximation space of the trigonometric
polynomials in `L_p`) iff `‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞`. -/
theorem memBesov_iff_modNorm_lt_top_lp (hp : p ≠ ∞) {r : ℕ} {s : ℝ} (hs : 0 < s) (hsr : s < r)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    (trigScheme d).MemBesov volume p s q f ↔
      ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p r f k) < ∞ :=
  (lpModulusData d hp r).memApprox_iff_modNorm_lt_top hq hs.le hsr f

end Torus
