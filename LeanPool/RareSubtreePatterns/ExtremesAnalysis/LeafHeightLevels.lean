/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.ExtremesAnalysis.Rary
public import LeanPool.RareSubtreePatterns.LeafHeight.Tree

import Mathlib.Tactic.Linarith

/-!
# Level intensities for the leaf-height and the complete `r`-ary heights

Specializations of `ExtremesAnalysis.Unary` and `ExtremesAnalysis.Rary` to the actual tails
(Theorems `thm:max_string` and `thm:max_lh`, inventory P20, P24, U03):

* `π_k = P(λ_∅(𝒯) ≥ k)` for the Bienaymé tree, written
  `(PlaneTree.bienayme μ).real {T | k ≤ T.rootLeafHeight}` (the `markProb` of the marks
  `G_k = 1{λ_∅ ≥ k}`), with `π_k / μ_1^k → C_μ = leafC μ` if `μ_1 > 0` and
  `π_k ∼ μ_κ^{-1/(κ-1)} D_μ^{κ^k}`, `D_μ = leafD μ`, if `μ_1 = 0` (`lem_ell_asymp_i_tree`,
  `lem_ell_asymp_ii_tree`).
* `μ_1 > 0` (Theorem `thm:max_lh`(i), source lines 3298–3326): with
  `k_n^* = (log n + log((1 - μ_1) C_μ)) / log(1/μ_1)` and `c_B = 1 - μ_1`,
  `exp(-c_B n π_{⌊k_n^* + t⌋ + 1}) - exp(-μ_1^{t + 1 - {k_n^* + t}}) → 0`, `n π_{h_n}` bounded,
  `h_n = n^{o(1)}` (`lh_unary_inputs`).
* `μ_1 = 0` (Theorem `thm:max_lh`(ii) with `c > 0`, source lines 3328–3383): with
  `k_n^{**} = log_κ log n - log_κ log(1/D_μ)`: `n π_{m_n + j} ∼ μ_κ^{-1/(κ-1)} n^{1 - κ^{j - θ_n}}`
  (`lh_isEquivalent_level`), the two-point and interior thresholds (`lh_twoPoint_thresholds`,
  `lh_interior_thresholds`) and the level sizes (`lh_levels_le_rpow`). The positivity `c > 0` is
  not used by these analytic statements (it is used by Lemma `lem:C_lh`).
* `c = 0` (source lines 3274–3296): `k_n^{**} = t_n^{**}` with `r = κ`, `μ_r = μ_κ`
  (`lh_center_eq_tStarStar`), so the two-point law case is Theorem `thm:max_string`(ii).
* For a critical law and `r ≥ 2`: `μ_r < 1` (`toReal_lt_one_of_two_le`), the side condition of the
  `r`-ary lemmas.
-/

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace PoissonDeclumping
namespace ExtremesAnalysis

open LeafHeight

variable {μ : PMF ℕ}

/-- For a critical law, `μ_r ≤ 1/r < 1` whenever `r ≥ 2`. -/
theorem toReal_lt_one_of_two_le (hc : IsCritical μ) {r : ℕ} (hr : 2 ≤ r) : (μ r).toReal < 1 := by
  have h := le_hasSum (hasSum_mean hc) r fun j _ => mul_nonneg (Nat.cast_nonneg j)
    (mass_nonneg (μ := μ) j)
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hm := mass_nonneg (μ := μ) r
  change mass μ r < 1
  nlinarith

/-! ### `μ_1 > 0` -/

/-- Theorem `thm:max_lh`(i), deterministic inputs, with `C = C_μ = leafC μ`, `c_B = 1 - μ_1` and
the level `h_n = ⌊k_n^* + t⌋ + 1`:
`exp(-c_B n π_{h_n}) - exp(-μ_1^{t + 1 - {k_n^* + t}}) → 0`, `n π_{h_n}` is eventually bounded,
and `h_n ≤ n^δ` eventually for every `δ > 0`. -/
theorem lh_unary_inputs (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (hpos : 0 < μ 1) {x : ℕ → ℝ}
    (hx : ∀ n, x n = (Real.log n + Real.log ((1 - (μ 1).toReal) * leafC μ)) /
      Real.log (1 / (μ 1).toReal)) (t : ℝ) :
    Tendsto (fun n : ℕ => Real.exp (-((1 - (μ 1).toReal) * ((n : ℝ) *
        (PlaneTree.bienayme μ).real {T | (⌊x n + t⌋ + 1).toNat ≤ T.rootLeafHeight}))) -
      Real.exp (-((μ 1).toReal ^ (t + 1 - Int.fract (x n + t))))) atTop (𝓝 0) ∧
    (∃ K : ℝ, ∀ᶠ n : ℕ in atTop, (n : ℝ) *
      (PlaneTree.bienayme μ).real {T | (⌊x n + t⌋ + 1).toNat ≤ T.rootLeafHeight} ≤ K) ∧
    (∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      ((((⌊x n + t⌋ + 1).toNat : ℕ)) : ℝ) ≤ (n : ℝ) ^ δ) := by
  have hq0 : 0 < (μ 1).toReal := (mass_pos_iff 1).mpr hpos
  have hq1 : (μ 1).toReal < 1 := mass_one_lt_one h1
  obtain ⟨hC, hlim, -⟩ := lem_ell_asymp_i_tree hc h1 hpos
  have hc' : 0 < 1 - (μ 1).toReal := by linarith
  exact ⟨tendsto_exp_sub_lattice hq0 hq1 hc' hC hlim hx t,
    exists_eventually_mul_le hq0 hq1 hc' hC hlim hx t, unaryLevel_le_rpow hq0 hq1 hx t⟩

/-! ### `μ_1 = 0` -/

section Superexp

variable (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (h0 : μ 1 = 0) {x : ℕ → ℝ}
  (hx : ∀ n, x n = Real.logb (kappa μ) (Real.log n) - Real.logb (kappa μ) (Real.log (1 / leafD μ)))
include hc h1 h0 hx

/-- Source lines 3336–3342: for every fixed `j ∈ ℤ`,
`n π_{m_n + j} ∼ μ_κ^{-1/(κ-1)} n^{1 - κ^{j - θ_n}}`, `m_n = ⌊k_n^{**}⌋`, `θ_n = {k_n^{**}}`. -/
theorem lh_isEquivalent_level (j : ℤ) :
    (fun n : ℕ => (n : ℝ) *
        (PlaneTree.bienayme μ).real {T | (⌊x n⌋ + j).toNat ≤ T.rootLeafHeight}) ~[atTop]
      fun n : ℕ => (μ (kappa μ)).toReal ^ (-1 / ((kappa μ : ℝ) - 1)) *
        (n : ℝ) ^ (1 - (kappa μ : ℝ) ^ ((j : ℝ) - Int.fract (x n))) := by
  obtain ⟨-, hD0, hD1, -, hp⟩ := lem_ell_asymp_ii_tree hc h1 h0
  exact isEquivalent_level (two_le_kappa hc h1 h0) hD0 hD1 hx hp j

/-- Two-point levels for the leaf-height (source lines 3358–3374), along any `l ≤ atTop`: with
`a_n = twoPointLow k_n^{**}`, `n π_{a_n} → ∞` and `n π_{a_n + 2} → 0`. -/
theorem lh_twoPoint_thresholds {l : Filter ℕ} (hl : l ≤ atTop) :
    Tendsto (fun n : ℕ => (n : ℝ) *
        (PlaneTree.bienayme μ).real {T | (twoPointLow (x n)).toNat ≤ T.rootLeafHeight})
        l atTop ∧
      Tendsto (fun n : ℕ => (n : ℝ) *
        (PlaneTree.bienayme μ).real {T | (twoPointLow (x n) + 2).toNat ≤ T.rootLeafHeight})
        l (𝓝 0) := by
  obtain ⟨-, hD0, hD1, -, hp⟩ := lem_ell_asymp_ii_tree hc h1 h0
  exact twoPoint_thresholds (two_le_kappa hc h1 h0) hD0 hD1 hx hp
    (Real.rpow_pos_of_pos ((mass_pos_iff _).mpr (kappa_mem hc h1).2) _) hl

/-- Interior phase for the leaf-height (source lines 3375–3381): if
`δ ≤ min(θ_n, 1 - θ_n)` eventually along `l ≤ atTop`, then `n π_{m_n} → ∞` and
`n π_{m_n + 1} → 0` along `l`. -/
theorem lh_interior_thresholds {l : Filter ℕ} (hl : l ≤ atTop) {δ : ℝ} (hδ : 0 < δ)
    (hθ : ∀ᶠ n in l, δ ≤ min (Int.fract (x n)) (1 - Int.fract (x n))) :
    Tendsto (fun n : ℕ => (n : ℝ) *
        (PlaneTree.bienayme μ).real {T | (⌊x n⌋).toNat ≤ T.rootLeafHeight}) l atTop ∧
      Tendsto (fun n : ℕ => (n : ℝ) *
        (PlaneTree.bienayme μ).real {T | (⌊x n⌋ + 1).toNat ≤ T.rootLeafHeight}) l (𝓝 0) := by
  obtain ⟨-, hD0, hD1, -, hp⟩ := lem_ell_asymp_ii_tree hc h1 h0
  exact interior_thresholds (two_le_kappa hc h1 h0) hD0 hD1 hx hp
    (Real.rpow_pos_of_pos ((mass_pos_iff _).mpr (kappa_mem hc h1).2) _) hl hδ hθ

/-- Level sizes for the leaf-height (`κ^{h_n} = O(log n)`, hypothesis of Lemma `lem:S_lh`(i)):
`κ^{a_n}`, `κ^{a_n+2}`, `κ^{m_n + j}` (`j ≤ 2`) are `≤ n^δ` eventually, for every `δ > 0`. -/
theorem lh_levels_le_rpow :
    (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      (kappa μ : ℝ) ^ (twoPointLow (x n)).toNat ≤ (n : ℝ) ^ δ) ∧
    (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      (kappa μ : ℝ) ^ (twoPointLow (x n) + 2).toNat ≤ (n : ℝ) ^ δ) ∧
    (∀ j : ℤ, j ≤ 2 → ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      (kappa μ : ℝ) ^ (⌊x n⌋ + j).toNat ≤ (n : ℝ) ^ δ) :=
  levels_le_rpow (two_le_kappa hc h1 h0) (leafD_pos hc h1 h0) (leafD_lt_one hc h1 h0) hx

end Superexp

/-! ### `c = 0`: reduction to complete `κ`-ary trees -/

/-- If `c = 1 - κ μ_κ = 0` (source lines 3274–3296): `k_n^{**} = t_n^{**}` with `r = κ`. -/
theorem lh_center_eq_tStarStar (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (hc0 : cConst μ = 0)
    (n : ℕ) :
    Real.logb (kappa μ) (Real.log n) - Real.logb (kappa μ) (Real.log (1 / leafD μ)) =
      tStarStar (kappa μ) (μ (kappa μ)).toReal n :=
  centering_eq_of_cConst_eq_zero hc h1 hc0 n

end ExtremesAnalysis
end PoissonDeclumping
