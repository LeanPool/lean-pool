/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Interval.Taylor
public import Mathlib.Analysis.Calculus.MeanValue

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Differences of polynomials of every order

For a polynomial `P` of degree `< r` the difference of order `m ≥ r` vanishes
(`Interval.higherDiff_polynomial`); differences of lower order are small instead. If
`|P^(m)| ≤ M` on `[y, y + mσ]`, `σ ≥ 0`, then `|Δ_σ^m P(y)| ≤ σ^m M`
(`Interval.norm_higherDiff_polyFun_le`), by induction on `m` with the mean value theorem, since the
derivative of `Δ_σ^m P` is `Δ_σ^m P'` (`Interval.hasDerivAt_higherDiff_polyFun`).

On the finite-dimensional space of polynomials of degree `< r` every linear map is bounded by
the `L_p` norm on an interval (`Interval.exists_enorm_linearMap_le_eLpNorm`, in
`FunctionSpaces.Domains.Interval.Polynomials`); for the `m`-th derivative this is a form of Markov's
inequality. After rescaling, the polynomials satisfy a
**difference bound** of order `m` (`Interval.DiffBound`, `Interval.exists_diffBound`):
`|Δ_t^m P(x)| ≤ K (t/L)^m L^(-1/p) ‖P‖_{L_p[u, u + L]}` for `x, x + mt ∈ [u, u + 2L]`. For `m = 0`
this is Nikolskii's bound (`Interval.NikolskiiBound`).
-/

@[expose] public section

open MeasureTheory Set Polynomial
open Rd (higherDiff)
open scoped ENNReal

namespace Interval

/-- The derivatives of polynomials of degree `< r` have degree `< r`. -/
theorem iterate_derivative_mem_degreeLT {r : ℕ} {P : ℂ[X]} (hP : P ∈ degreeLT ℂ r) (m : ℕ) :
    derivative^[m] P ∈ degreeLT ℂ r := by
  induction m with
  | zero => exact hP
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    rw [mem_degreeLT] at ih ⊢
    exact degree_derivative_le.trans_lt ih

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Differences of polynomials and derivatives -/

/-- The derivative of a difference of a polynomial is the difference of its derivative:
`(Δ_σ^m P)' = Δ_σ^m P'`. -/
theorem hasDerivAt_higherDiff_polyFun (m : ℕ) (σ : ℝ) (P : ℂ[X]) (z : ℝ) :
    HasDerivAt (higherDiff m σ (polyFun P)) (higherDiff m σ (polyFun (derivative P)) z) z := by
  have h : higherDiff m σ (polyFun P) = fun z => ∑ k ∈ Finset.range (m + 1),
      ((-1 : ℂ) ^ (m - k) * (m.choose k : ℂ)) * polyFun P (z + k * σ) :=
    funext fun z => higherDiff_apply m σ _ z
  rw [h, higherDiff_apply]
  exact HasDerivAt.fun_sum fun k _ =>
    ((hasDerivAt_polyFun P (z + k * σ)).comp_add_const z (k * σ)).const_mul _

/-- **Differences of polynomials by derivatives**: if `|P^(m)| ≤ M` on `[y, y + mσ]` with
`σ ≥ 0`, then `|Δ_σ^m P(y)| ≤ σ^m M`. Induction on `m`: `Δ_σ^(m+1) P(y) = Δ_σ^m P(y + σ) -
Δ_σ^m P(y)`, and the mean value theorem (Mathlib's
`norm_image_sub_le_of_norm_deriv_le_segment'`) applies to `Δ_σ^m P` with derivative
`Δ_σ^m P'`. -/
theorem norm_higherDiff_polyFun_le (m : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) {M : ℝ} :
    ∀ (P : ℂ[X]) (y : ℝ), (∀ z ∈ Icc y (y + m * σ), ‖polyFun (derivative^[m] P) z‖ ≤ M) →
      ‖higherDiff m σ (polyFun P) y‖ ≤ σ ^ m * M := by
  induction m with
  | zero =>
    intro P y h
    simpa using h y ⟨le_rfl, by simp⟩
  | succ m ih =>
    intro P y h
    rw [higherDiff_succ]
    have hd : ∀ z ∈ Icc y (y + σ), HasDerivWithinAt (higherDiff m σ (polyFun P))
        (higherDiff m σ (polyFun (derivative P)) z) (Icc y (y + σ)) z :=
      fun z _ => (hasDerivAt_higherDiff_polyFun m σ P z).hasDerivWithinAt
    have hb : ∀ z ∈ Ico y (y + σ), ‖higherDiff m σ (polyFun (derivative P)) z‖ ≤ σ ^ m * M :=
      fun z hz => ih (derivative P) z fun w hw => by
        have hw' : w ∈ Icc y (y + ((m + 1 : ℕ) : ℝ) * σ) := by
          push_cast
          constructor <;> nlinarith [hz.1, hz.2, hw.1, hw.2]
        have := h w hw'
        rwa [Function.iterate_succ_apply] at this
    have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hd hb (y + σ)
      ⟨by linarith, le_rfl⟩
    calc ‖higherDiff m σ (polyFun P) (y + σ) - higherDiff m σ (polyFun P) y‖
        ≤ σ ^ m * M * (y + σ - y) := hmvt
      _ = σ ^ (m + 1) * M := by ring

/-! ### The difference bound -/

variable (p) in
/-- The **difference bound** of order `m` with constant `K` for the polynomials of degree `< r`:
`|Δ_t^m P(x)| ≤ K (t/L)^m L^(-1/p) ‖P‖_{L_p[u, u + L]}` for `t ≥ 0` and `u ≤ x`,
`x + mt ≤ u + 2L`. For `m = 0` this is Nikolskii's bound `Interval.NikolskiiBound`. -/
def DiffBound (r m : ℕ) (K : ℝ≥0∞) : Prop :=
  ∀ P ∈ degreeLT ℂ r, ∀ (u : ℝ) {L : ℝ}, 0 < L → ∀ {t : ℝ}, 0 ≤ t → ∀ x, u ≤ x →
    x + m * t ≤ u + 2 * L →
      ‖higherDiff m t (polyFun P) x‖ₑ ≤ K * ENNReal.ofReal (t / L) ^ m *
        ENNReal.ofReal L⁻¹ ^ (1 / p.toReal) *
          eLpNorm (polyFun P) p (volume.restrict (Icc u (u + L)))

/-- **Differences of polynomials are small**: for `1 ≤ p < ∞` and every order `m` there is a
difference bound for the polynomials of degree `< r`. On `[0, 1]` the derivative `P^(m)` is
bounded by `K ‖P‖_{L_p[0, 1/2]}` (`Interval.exists_enorm_linearMap_le_eLpNorm`), so
`|Δ_σ^m P(y)| ≤ σ^m K ‖P‖_{L_p[0, 1/2]}` (`Interval.norm_higherDiff_polyFun_le`); the substitution
`x = u + 2L y` rescales. -/
theorem exists_diffBound (r m : ℕ) (hp : p ≠ ∞) : ∃ K : ℝ≥0∞, K ≠ ∞ ∧ DiffBound p r m K := by
  obtain ⟨K, hK, hKb⟩ := exists_enorm_linearMap_le_eLpNorm (p := p) r
    ((derivative : ℂ[X] →ₗ[ℂ] ℂ[X]) ^ m)
    (fun P hP => by rw [pow_apply_eq_iterate]; exact iterate_derivative_mem_degreeLT hP m)
    (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨K, hK, fun P hPr u L hL t ht x hux hxu => ?_⟩
  have h2L : 0 < 2 * L := by positivity
  set Q := P.comp (C (u : ℂ) + C ((2 * L : ℝ) : ℂ) * X)
  have hQ : Q ∈ degreeLT ℂ r := comp_affine_mem_degreeLT hPr _ _
  set σ := t / (2 * L)
  set y := (x - u) / (2 * L)
  have hσ : 0 ≤ σ := div_nonneg ht h2L.le
  -- the difference in the new variable
  have hdiff : higherDiff m t (polyFun P) x = higherDiff m σ (polyFun Q) y := by
    rw [higherDiff_apply, higherDiff_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [polyFun_comp_affine]
    congr 2
    simp only [σ, y]
    field_simp
    ring
  -- the bound of the derivative on `[0, 1]`
  have hfin : eLpNorm (polyFun Q) p (volume.restrict (Icc 0 (1 / 2))) ≠ ∞ :=
    (memLp_polyFun Q p 0 (1 / 2)).eLpNorm_ne_top
  have hKQ : K * eLpNorm (polyFun Q) p (volume.restrict (Icc 0 (1 / 2))) ≠ ∞ :=
    ENNReal.mul_ne_top hK hfin
  have hder : ∀ z ∈ Icc y (y + m * σ), ‖polyFun (derivative^[m] Q) z‖ ≤
      (K * eLpNorm (polyFun Q) p (volume.restrict (Icc 0 (1 / 2)))).toReal := fun z hz => by
    have hz01 : z ∈ Icc (0 : ℝ) 1 := by
      have hy0 : 0 ≤ y := div_nonneg (by linarith) h2L.le
      have hy1 : y + m * σ ≤ 1 := by
        rw [show y + m * σ = (x - u + m * t) / (2 * L) by simp only [y, σ]; ring,
          div_le_one h2L]
        linarith
      exact ⟨hy0.trans hz.1, hz.2.trans hy1⟩
    have h := hKb Q hQ z hz01
    rw [pow_apply_eq_iterate] at h
    rw [← ofReal_norm] at h
    exact (ENNReal.ofReal_le_iff_le_toReal hKQ).1 h
  have hval := norm_higherDiff_polyFun_le m hσ Q y hder
  -- the norm of `Q` on `[0, 1/2]`
  have hnorm := eLpNorm_comp_affine (measurable_polyFun P) hp u h2L 0 (1 / 2)
  rw [mul_zero, add_zero, show 2 * L * (1 / 2) = L by ring] at hnorm
  have hQfun : (fun y => polyFun P (u + 2 * L * y)) = polyFun Q :=
    funext fun y => (polyFun_comp_affine P u (2 * L) y).symm
  rw [hQfun] at hnorm
  have hσL : σ ≤ t / L := div_le_div_of_nonneg_left ht hL (by linarith)
  rw [hdiff, ← ofReal_norm]
  calc ENNReal.ofReal ‖higherDiff m σ (polyFun Q) y‖
      ≤ ENNReal.ofReal (σ ^ m * (K * eLpNorm (polyFun Q) p
          (volume.restrict (Icc 0 (1 / 2)))).toReal) := ENNReal.ofReal_le_ofReal hval
    _ = ENNReal.ofReal σ ^ m * (K * eLpNorm (polyFun Q) p (volume.restrict (Icc 0 (1 / 2)))) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hσ, ENNReal.ofReal_toReal hKQ]
    _ = K * ENNReal.ofReal σ ^ m * ENNReal.ofReal (2 * L)⁻¹ ^ (1 / p.toReal) *
          eLpNorm (polyFun P) p (volume.restrict (Icc u (u + L))) := by
        rw [hnorm]; ring
    _ ≤ K * ENNReal.ofReal (t / L) ^ m * ENNReal.ofReal L⁻¹ ^ (1 / p.toReal) *
          eLpNorm (polyFun P) p (volume.restrict (Icc u (u + L))) := by
        gcongr
        linarith

end Interval
