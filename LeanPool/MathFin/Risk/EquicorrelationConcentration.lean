/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Risk.Concentration
public import LeanPool.MathFin.Choice.Portfolio.MarkowitzNAsset

/-!
# Equicorrelated variance is concentration plus a systematic floor

For a covariance kernel with a common variance `v` and a common pairwise covariance `ρ v`
(`σᵢᵢ = v`, and `σᵢⱼ = ρ v` for `i ≠ j`), the Markowitz portfolio variance splits as

  `Var(w) = v · ((1 − ρ) · HHI(w) + ρ · (∑ wᵢ)²)`

(`portfolioVarN_equicorrelated_eq_herfindahl`). For fully invested weights (`∑ wᵢ = 1`) this
reads `Var(w) = v · ((1 − ρ) · HHI(w) + ρ)` (`portfolioVarN_equicorrelated_of_sum_eq_one`).

* The diversifiable part `(1 − ρ) v · HHI(w)` is the Herfindahl–Hirschman concentration of the
  weights. Since `HHI ≥ 1/n` on a fully invested portfolio (`herfindahl_card_inv_le_of_sum_one`),
  for `ρ ≤ 1` no fully invested portfolio has variance below `v ((1 − ρ)/n + ρ)`
  (`portfolioVarN_equicorrelated_ge`), and equal weights attain it
  (`portfolioVarN_equicorrelated_equal_weights`).
* The systematic part `ρ v` does not depend on the weights at all. For `v ≥ 0` and `ρ ≤ 1` no
  fully invested portfolio, however diversified, has variance below `ρ v`
  (`mul_le_portfolioVarN_equicorrelated`).

The uncorrelated case `ρ = 0` is `Risk/ConcentrationVariance.lean`
(`portfolioVarN_diag_eq_herfindahl`): there the floor vanishes and variance is pure concentration.
The floor `ρ v` is the Markowitz face of the large-portfolio limit of the one-factor credit model
(`Risk/Credit/VasicekIRB.lean`): there too the idiosyncratic risk averages out and the factor risk
remains. A certified unification of two known textbook facts, not new finance.

## Main results

* `portfolioVarN_equicorrelated_eq_herfindahl`: `Var(w) = v ((1 − ρ) HHI(w) + ρ (∑ wᵢ)²)`.
* `portfolioVarN_equicorrelated_of_sum_eq_one`: `Var(w) = v ((1 − ρ) HHI(w) + ρ)` when fully
  invested.
* `portfolioVarN_equicorrelated_ge`, `portfolioVarN_equicorrelated_equal_weights`: equal weights
  minimize the variance of a fully invested equicorrelated portfolio (`ρ ≤ 1`, `v ≥ 0`).
* `mul_le_portfolioVarN_equicorrelated`: the systematic floor `ρ v ≤ Var(w)`.

## References

* [*QRM Exercise Book*][QRMExerciseBook], Ex. 6.16

## Tags

equicorrelation, Herfindahl index, minimum variance portfolio, systematic risk, diversification,
MSC 91G10, JEL G11
-/

@[expose] public section

namespace MathFin

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Equicorrelation × concentration bridge.** A kernel with common variance `v` and common
covariance `ρ v` ⇒ `Var(w) = v · ((1 − ρ) · HHI(w) + ρ · (∑ wᵢ)²)`. At `ρ = 0` this is
`portfolioVarN_diag_eq_herfindahl`. -/
theorem portfolioVarN_equicorrelated_eq_herfindahl (s : Finset ι) (w : ι → ℝ)
    (σ : ι → ι → ℝ) (v ρ : ℝ) (h_var : ∀ i ∈ s, σ i i = v)
    (h_cov : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → σ i j = ρ * v) :
    portfolioVarN s w σ = v * ((1 - ρ) * herfindahl s w + ρ * (∑ i ∈ s, w i) ^ 2) := by
  classical
  have hterm (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) : w i * w j * σ i j =
      ρ * v * (w i * w j) + (1 - ρ) * v * (if i = j then w i * w j else 0) := by
    by_cases hij : i = j
    · subst hij
      rw [h_var i hi, ite_eq_left rfl]
      ring
    · rw [h_cov i hi j hj hij, ite_eq_right hij]
      ring
  have hdiag (i : ι) (hi : i ∈ s) : ∑ j ∈ s, (if i = j then w i * w j else 0) = w i ^ 2 := by
    rw [Finset.sum_ite_eq, ite_eq_left hi, sq]
  calc portfolioVarN s w σ
      = ∑ i ∈ s, ∑ j ∈ s,
          (ρ * v * (w i * w j) + (1 - ρ) * v * (if i = j then w i * w j else 0)) :=
        Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ hterm i hi j hj
    _ = ρ * v * ∑ i ∈ s, ∑ j ∈ s, w i * w j + (1 - ρ) * v * ∑ i ∈ s, w i ^ 2 := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [Finset.sum_congr rfl hdiag]
    _ = v * ((1 - ρ) * herfindahl s w + ρ * (∑ i ∈ s, w i) ^ 2) := by
        rw [herfindahl, sq (∑ i ∈ s, w i), Finset.sum_mul_sum]
        ring

variable {s : Finset ι} {w : ι → ℝ} {σ : ι → ι → ℝ} {v ρ : ℝ}

omit [DecidableEq ι] in
/-- For fully invested weights the equicorrelated variance is `v · ((1 − ρ) · HHI(w) + ρ)`. -/
theorem portfolioVarN_equicorrelated_of_sum_eq_one (h_var : ∀ i ∈ s, σ i i = v)
    (h_cov : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → σ i j = ρ * v) (h_sum : ∑ i ∈ s, w i = 1) :
    portfolioVarN s w σ = v * ((1 - ρ) * herfindahl s w + ρ) := by
  rw [portfolioVarN_equicorrelated_eq_herfindahl s w σ v ρ h_var h_cov, h_sum, one_pow, mul_one]

omit [DecidableEq ι] in
/-- **Equal weights are variance-minimal** under equicorrelation: for `v ≥ 0` and `ρ ≤ 1`, every
fully invested portfolio of `n` assets has `Var(w) ≥ v · ((1 − ρ)/n + ρ)`, because `HHI ≥ 1/n`. -/
theorem portfolioVarN_equicorrelated_ge (h_var : ∀ i ∈ s, σ i i = v)
    (h_cov : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → σ i j = ρ * v) (h_sum : ∑ i ∈ s, w i = 1) (hv : 0 ≤ v)
    (hρ : ρ ≤ 1) :
    v * ((1 - ρ) / s.card + ρ) ≤ portfolioVarN s w σ := by
  have hH := herfindahl_card_inv_le_of_sum_one s w h_sum
  have h1ρ : 0 ≤ 1 - ρ := sub_nonneg.2 hρ
  rw [portfolioVarN_equicorrelated_of_sum_eq_one h_var h_cov h_sum, div_eq_mul_inv]
  gcongr

omit [DecidableEq ι] in
/-- Equal weights attain the bound of `portfolioVarN_equicorrelated_ge`:
`Var(1/n, …, 1/n) = v · ((1 − ρ)/n + ρ)`. -/
theorem portfolioVarN_equicorrelated_equal_weights (h_var : ∀ i ∈ s, σ i i = v)
    (h_cov : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → σ i j = ρ * v) (hs : s.Nonempty) :
    portfolioVarN s (fun _ ↦ (s.card : ℝ)⁻¹) σ = v * ((1 - ρ) / s.card + ρ) := by
  have hc : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hs.card_pos.ne'
  rw [portfolioVarN_equicorrelated_eq_herfindahl s _ σ v ρ h_var h_cov, herfindahl]
  simp only [Finset.sum_const, nsmul_eq_mul]
  field_simp

omit [DecidableEq ι] in
/-- **The systematic floor**: for `v ≥ 0` and `ρ ≤ 1`, no fully invested equicorrelated portfolio,
however diversified, has variance below `ρ v`. -/
theorem mul_le_portfolioVarN_equicorrelated (h_var : ∀ i ∈ s, σ i i = v)
    (h_cov : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → σ i j = ρ * v) (h_sum : ∑ i ∈ s, w i = 1) (hv : 0 ≤ v)
    (hρ : ρ ≤ 1) :
    ρ * v ≤ portfolioVarN s w σ := by
  rw [portfolioVarN_equicorrelated_of_sum_eq_one h_var h_cov h_sum]
  nlinarith [mul_nonneg hv (mul_nonneg (sub_nonneg.2 hρ) (herfindahl_nonneg s w))]

end MathFin
