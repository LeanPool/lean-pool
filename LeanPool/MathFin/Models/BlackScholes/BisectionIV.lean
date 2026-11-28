/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.ImpliedVolatility
public import LeanPool.MathFin.Probability.Analysis.Bisection

/-!
# Implied volatility by bisection

For `K, S, T > 0` the Black–Scholes call price is continuous and strictly
increasing in `σ > 0` (`bsV_continuousOn_sigma`, `bsV_strictMonoOn_sigma`). Take
a volatility bracket `0 < σ_lo < σ_hi` whose prices straddle a market price
`C_obs`. The intermediate value theorem puts an implied volatility `σ` strictly
inside the bracket, and strict monotonicity makes it the only positive one. It
also makes `σ` the threshold of the price against `C_obs`, which is all the
bisection method (`Probability/Analysis/Bisection.lean`) needs to converge to it.

## Main results

* `impliedVol_bracket_exists`: for `f` continuous and strictly increasing on
  `[σ_lo, σ_hi]`, a target strictly between `f σ_lo` and `f σ_hi` is attained
  at a unique `σ ∈ (σ_lo, σ_hi)`.
* `impliedVol_bisection_converges`: bisection on the BS call price converges to
  the implied volatility, within `(σ_hi − σ_lo) / 2ⁿ⁺¹` after `n` steps.

## References

* [Burden and Faires, *Numerical Analysis*][BurdenFaires], §2.1
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull]
* [Press and others, *Numerical Recipes*][PressEtAlNumericalRecipes], §9.1

## Tags

implied volatility, bisection method, intermediate value, volatility bracket, root finding,
MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open Filter Topology

/-- **Bracket existence and uniqueness** (the existence half of bisection): for
`f` continuous and strictly increasing on `[σ_lo, σ_hi]`, any target strictly
between `f σ_lo` and `f σ_hi` is attained at a unique `σ ∈ (σ_lo, σ_hi)`. The
intermediate value theorem gives a root strictly inside the bracket; strict
monotonicity makes it unique. -/
lemma impliedVol_bracket_exists
    {f : ℝ → ℝ} {σ_lo σ_hi C_obs : ℝ}
    (h_lo_lt_hi : σ_lo < σ_hi)
    (h_cont : ContinuousOn f (Set.Icc σ_lo σ_hi))
    (h_mono : StrictMonoOn f (Set.Icc σ_lo σ_hi))
    (h_brkt : f σ_lo < C_obs ∧ C_obs < f σ_hi) :
    ∃! σ : ℝ, σ ∈ Set.Ioo σ_lo σ_hi ∧ f σ = C_obs := by
  obtain ⟨σ, hσ, rfl⟩ := intermediate_value_Ioo h_lo_lt_hi.le h_cont h_brkt
  exact ⟨σ, ⟨hσ, rfl⟩, fun σ' ⟨hσ', h⟩ ↦
    h_mono.injOn (Set.Ioo_subset_Icc_self hσ') (Set.Ioo_subset_Icc_self hσ) h⟩

/-- **Bisection converges to the implied volatility.** For `K, S, T > 0`, any
rate `r`, and a bracket `0 < σ_lo < σ_hi` whose Black–Scholes call prices
straddle the market price `C_obs`, there is an implied volatility
`σ ∈ (σ_lo, σ_hi)`, it is the only positive one, and the bisection estimates
converge to it, within `(σ_hi − σ_lo) / 2ⁿ⁺¹` after `n` steps. -/
theorem impliedVol_bisection_converges {K r T S σ_lo σ_hi C_obs : ℝ}
    (hK : 0 < K) (hT : 0 < T) (hS : 0 < S) (h_lo : 0 < σ_lo) (h_lo_hi : σ_lo < σ_hi)
    (h_brkt : bsV K r σ_lo S T < C_obs ∧ C_obs < bsV K r σ_hi S T) :
    ∃ σ ∈ Set.Ioo σ_lo σ_hi, bsV K r σ S T = C_obs ∧
      (∀ σ' > 0, bsV K r σ' S T = C_obs → σ' = σ) ∧
      (∀ n, |bisectMid (fun v ↦ bsV K r v S T) C_obs σ_lo σ_hi n - σ| ≤
        (σ_hi - σ_lo) / 2 ^ (n + 1)) ∧
      Tendsto (bisectMid (fun v ↦ bsV K r v S T) C_obs σ_lo σ_hi) atTop (𝓝 σ) := by
  have hpos : Set.Icc σ_lo σ_hi ⊆ Set.Ioi 0 := fun v hv ↦ h_lo.trans_le hv.1
  have hmono := (bsV_strictMonoOn_sigma (r := r) hK hT hS).mono hpos
  obtain ⟨σ, ⟨hσ, rfl⟩, -⟩ := impliedVol_bracket_exists h_lo_hi
    ((bsV_continuousOn_sigma hK hT hS).mono hpos) hmono h_brkt
  have hσ' := Set.Ioo_subset_Icc_self hσ
  have hC (x : ℝ) (hx : x ∈ Set.Icc σ_lo σ_hi) := hmono.lt_iff_lt hx hσ'
  exact ⟨σ, hσ, rfl, fun σ' hσ'0 h ↦ implied_volatility_unique hK hT hS hσ'0
    (h_lo.trans hσ.1) h, abs_bisectMid_sub_le hC hσ', tendsto_bisectMid hC hσ'⟩

end MathFin
