/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Real
public import LeanPool.AiyagariEquilibrium.Models.MonotoneTransitions

/-!
# Tauchen (1986) chains have monotone transitions

Tauchen's discretisation of `z' = ρ z + σ ε`, `ε ~ N(0,1)`, on the grid `lo, lo + w, …, lo + n w`
puts on state `j` the normal mass of the interval of half-width `w/2` about `lo + j w`, with the
end states taking the tails. Written through the row's cumulative mass on states below `k`,

  `F_i(k) = Φ((lo + k w - w/2 - ρ(lo + i w)) / σ)`  for `0 < k ≤ n`,  `F_i(0) = 0`,  `F_i(n+1) = 1`,

the entry is `F_i(j+1) - F_i(j)`. Everything about the chain is then one fact about `Φ`: it is
monotone. Entries are non-negative and rows sum to one because `F_i` rises from `0` to `1` in
`k`; the rows are ordered by first-order stochastic dominance because `F_i(k)` FALLS in `i` when
`ρ ≥ 0`; and the lowest state is reachable from everywhere because `Φ > 0`.

There is nothing special about seven states. Aiyagari (1994) used seven; the results here are for
`n + 1` states, any `n`.

## First-order stochastic dominance on a finite chain

`sum_mul_le_of_cum_le` is the finite FOSD lemma: if `q` puts no more mass than `p` on every
initial segment, then `q` gives the smaller expectation to every antitone `f`. Summation by parts
(`Finset.sum_range_by_parts`) does it in one line.
-/

@[expose] public section

open Set Finset MeasureTheory ProbabilityTheory

namespace LeanEconomics

/-! ### The standard normal cdf -/

/-- The standard normal distribution function `Φ`. -/
noncomputable def normalCdf : ℝ → ℝ := cdf (gaussianReal 0 1)

theorem normalCdf_mono : Monotone normalCdf := monotone_cdf _

theorem normalCdf_nonneg (x : ℝ) : 0 ≤ normalCdf x := cdf_nonneg _ x

theorem normalCdf_le_one (x : ℝ) : normalCdf x ≤ 1 := cdf_le_one _ x

/-- `Φ > 0` everywhere: the normal density is positive and `Iic x` has positive Lebesgue
measure. -/
theorem normalCdf_pos (x : ℝ) : 0 < normalCdf x := by
  have h1 : (1 : NNReal) ≠ 0 := one_ne_zero
  have hint : 0 < ∫ y in Iic x, gaussianPDFReal 0 1 y := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun y => gaussianPDFReal_nonneg 0 1 y)
      (integrable_gaussianPDFReal 0 1).integrableOn]
    have hsupp : Function.support (gaussianPDFReal 0 1) = univ := by
      ext y; simp [Function.mem_support, (gaussianPDFReal_pos 0 1 y h1).ne']
    rw [hsupp, univ_inter, Real.volume_Iic]
    exact ENNReal.zero_lt_top
  unfold normalCdf
  rw [cdf_eq_real, Measure.real, gaussianReal_apply_eq_integral 0 h1, ENNReal.toReal_ofReal hint.le]
  exact hint

/-! ### The finite FOSD lemma -/

/-- **First-order stochastic dominance on `{0, …, n}`.** Two probability vectors given through
cumulative functions `F` and `G` (`p j = F (j+1) - F j`, `F 0 = 0`, `F (n+1) = 1`, likewise `G`),
with `G ≤ F` pointwise — `q` puts no more mass on any initial segment — give, for every antitone
`f`, the inequality `∑ q f ≤ ∑ p f`. -/
theorem sum_mul_le_of_cum_le {n : ℕ} {p q : Fin (n + 1) → ℝ} {F G : ℕ → ℝ}
    (hp : ∀ j : Fin (n + 1), p j = F (j.val + 1) - F j.val)
    (hq : ∀ j : Fin (n + 1), q j = G (j.val + 1) - G j.val)
    (hF0 : F 0 = 0) (hG0 : G 0 = 0) (hFn : F (n + 1) = 1) (hGn : G (n + 1) = 1)
    (hle : ∀ k, G k ≤ F k) {f : Fin (n + 1) → ℝ} (hf : ∀ j j' : Fin (n + 1), j ≤ j' → f j' ≤ f j) :
    ∑ j, q j * f j ≤ ∑ j, p j * f j := by
  -- extend `f` to `ℕ`
  set fe : ℕ → ℝ := fun k => if h : k < n + 1 then f ⟨k, h⟩ else 0 with hfe
  have hfe_eq : ∀ j : Fin (n + 1), fe j.val = f j := by
    intro j; simp only [hfe, j.isLt, ↓reduceDIte]
  have hfe_anti : ∀ k, k < n → fe (k + 1) ≤ fe k := by
    intro k hk
    have h1 : k < n + 1 := by omega
    have h2 : k + 1 < n + 1 := by omega
    simp only [hfe, h1, h2, ↓reduceDIte]
    exact hf ⟨k, h1⟩ ⟨k + 1, h2⟩ (Fin.mk_le_mk.mpr (Nat.le_succ k))
  -- the two sums as range sums, then summation by parts
  have key : ∀ (H : ℕ → ℝ) (r : Fin (n + 1) → ℝ),
      (∀ j : Fin (n + 1), r j = H (j.val + 1) - H j.val) → H 0 = 0 → H (n + 1) = 1 →
      ∑ j, r j * f j = fe n - ∑ i ∈ range n, (fe (i + 1) - fe i) * H (i + 1) := by
    intro H r hr hH0 hHn
    have h1 : ∑ j, r j * f j = ∑ i ∈ range (n + 1), fe i • (H (i + 1) - H i) := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => fe i • (H (i + 1) - H i)) (n + 1)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hr j, hfe_eq j, smul_eq_mul, mul_comm]
    rw [h1, Finset.sum_range_by_parts fe (fun i => H (i + 1) - H i) (n + 1)]
    simp only [Nat.add_sub_cancel, Finset.sum_range_sub, hH0, hHn, sub_zero, smul_eq_mul, mul_one]
  rw [key F p hp hF0 hFn, key G q hq hG0 hGn]
  have hterm : ∀ i ∈ range n,
      (fe (i + 1) - fe i) * F (i + 1) ≤ (fe (i + 1) - fe i) * G (i + 1) := by
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    exact mul_le_mul_of_nonpos_left (hle (i + 1)) (by linarith [hfe_anti i hi'])
  linarith [Finset.sum_le_sum hterm]

/-! ### The chain -/

/-- **Tauchen's cumulative row**: the mass row `i` puts on states below `k`. -/
noncomputable def tauchenCum (ρ σ lo w : ℝ) (n : ℕ) (i : Fin (n + 1)) (k : ℕ) : ℝ :=
  if k = 0 then 0 else if n + 1 ≤ k then 1
  else normalCdf ((lo + k * w - w / 2 - ρ * (lo + i * w)) / σ)

/-- **Tauchen's transition matrix** on `n + 1` states. -/
noncomputable def tauchen (ρ σ lo w : ℝ) (n : ℕ) (i j : Fin (n + 1)) : ℝ :=
  tauchenCum ρ σ lo w n i (j.val + 1) - tauchenCum ρ σ lo w n i j.val

variable {ρ σ lo w : ℝ} {n : ℕ}

theorem tauchenCum_zero (i : Fin (n + 1)) : tauchenCum ρ σ lo w n i 0 = 0 := by
  simp [tauchenCum]

theorem tauchenCum_top (i : Fin (n + 1)) : tauchenCum ρ σ lo w n i (n + 1) = 1 := by
  simp [tauchenCum]

/-- The cumulative row rises in `k`. -/
theorem tauchenCum_mono (hσ : 0 < σ) (hw : 0 < w) (i : Fin (n + 1)) :
    Monotone (tauchenCum ρ σ lo w n i) := by
  intro k k' hkk'
  unfold tauchenCum
  by_cases hk : k = 0
  · subst hk
    simp only [ite_true]
    split_ifs <;> first | exact le_rfl | exact zero_le_one | exact normalCdf_nonneg _
  · have hk' : k' ≠ 0 := by omega
    simp only [hk, hk', ite_false]
    by_cases htop : n + 1 ≤ k
    · have htop' : n + 1 ≤ k' := le_trans htop hkk'
      simp [htop, htop']
    · simp only [htop, ite_false]
      split_ifs with htop'
      · exact normalCdf_le_one _
      · apply normalCdf_mono
        apply div_le_div_of_nonneg_right _ hσ.le
        have : (k : ℝ) ≤ k' := by exact_mod_cast hkk'
        nlinarith

/-- The cumulative row falls in the state when `ρ ≥ 0`: first-order stochastic dominance. -/
theorem tauchenCum_anti (hρ : 0 ≤ ρ) (hσ : 0 < σ) (hw : 0 < w) {i i' : Fin (n + 1)} (hii' : i ≤ i')
    (k : ℕ) : tauchenCum ρ σ lo w n i' k ≤ tauchenCum ρ σ lo w n i k := by
  unfold tauchenCum
  split_ifs
  · exact le_rfl
  · exact le_rfl
  · apply normalCdf_mono
    apply div_le_div_of_nonneg_right _ hσ.le
    have : (i : ℝ) ≤ i' := by exact_mod_cast hii'
    nlinarith [mul_nonneg hρ hw.le]

theorem tauchen_nonneg (hσ : 0 < σ) (hw : 0 < w) (i j : Fin (n + 1)) :
    0 ≤ tauchen ρ σ lo w n i j :=
  sub_nonneg.mpr (tauchenCum_mono hσ hw i (Nat.le_succ _))

theorem tauchen_sum (i : Fin (n + 1)) : ∑ j, tauchen ρ σ lo w n i j = 1 := by
  unfold tauchen
  rw [Fin.sum_univ_eq_sum_range
    (fun k => tauchenCum ρ σ lo w n i (k + 1) - tauchenCum ρ σ lo w n i k) (n + 1),
    Finset.sum_range_sub, tauchenCum_top, tauchenCum_zero, sub_zero]

/-- The lowest state is reached from everywhere in one step. -/
theorem tauchen_pos_zero (i : Fin (n + 1)) : 0 < tauchen ρ σ lo w n i 0 := by
  unfold tauchen
  simp only [Fin.val_zero, zero_add]
  rw [tauchenCum_zero, sub_zero]
  unfold tauchenCum
  simp only [one_ne_zero, ite_false]
  split_ifs
  · exact one_pos
  · exact normalCdf_pos _

/-- **A Tauchen chain with `ρ ≥ 0` has monotone transitions**, for any economy whose income is
strictly increasing in the state. -/
theorem monotoneTransitions_of_tauchen {assetFloor assetCap : ℝ}
    (P : IncomeFluctuation.{0} (Fin (n + 1)) assetFloor assetCap)
    (hπ : P.transitionMatrix = tauchen ρ σ lo w n) (hinc : StrictMono P.income)
    (hρ : 0 ≤ ρ) (hσ : 0 < σ) (hw : 0 < w) : P.MonotoneTransitions := by
  intro z₁ z₂ hz f hf
  rw [hπ]
  have hz' : z₁ ≤ z₂ := hinc.le_iff_le.mp hz
  refine sum_mul_le_of_cum_le (F := tauchenCum ρ σ lo w n z₁) (G := tauchenCum ρ σ lo w n z₂)
    (fun j => rfl) (fun j => rfl) (tauchenCum_zero _) (tauchenCum_zero _) (tauchenCum_top _)
    (tauchenCum_top _) (fun k => tauchenCum_anti hρ hσ hw hz' k) ?_
  intro j j' hjj'
  exact hf j j' (hinc.monotone hjj')

end LeanEconomics
