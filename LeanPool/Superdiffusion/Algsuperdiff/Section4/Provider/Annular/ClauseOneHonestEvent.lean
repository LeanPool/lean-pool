/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.DichotomyDisplay

/-!
# ClauseOneHonestEvent

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The honest Section 4.1 clause-(i) event: amplitude and output constant

The A6a conditional endpoint is stated at
`Support.goodEventBase M Ccg m s ε = 𝒢₀ ∩ 𝒢₁(m; s, s ε √c⋆ γ^{−1/2}) ∩
𝒢₂(m; s, ε)`.  The Section 4.1 clause-(i) display is stated at the **larger**
event

```
𝒢₀(m) ∩ 𝒢₁(m; s, √c⋆ γ^{−1/2}),
```

with no `𝒢₂` factor and with the `𝒢₁` amplitude *not* damped by `s ε`.  A6a's
finding (d) recorded the divergence and finding (e) mapped the route out.  This
module carries the two arithmetic facts that route consumes:
`annularEventAmplitude_sq`, the square `T'² = c⋆ γ^{−1}` of the honest
amplitude, and `clauseOneOutConstant_pos`, the positivity of the composite's
output constant.

## What changes with the larger event, and what does not

* `𝒢₂` is gone.  Its **only** consumer was the `hsumE` binder of
  `ClauseOne.clauseOne_bound`, and `DichotomyDisplay` supplies that binder from
  finiteness of the display's own first term, with no event at all.
* The `𝒢₁` amplitude rises from `T = s ε √c⋆ γ^{−1/2}` to `T' = √c⋆ γ^{−1/2}`,
  i.e. the event gets **larger** and the reading gets **weaker**.  Nothing in the
  clause-(i) composite is harmed, because every `𝒢₁` consumer on this lane is a
  *summability* statement:
  `EventReading.summable_annFam_annularL2Block_of_eventG1`,
  `…_annularGradBlock_of_eventG1` and
  `…_summable_shellBlockLatticeReal_of_eventG1` each need only `0 ≤ T` and the
  membership.  The threshold enters those proofs solely through the auxiliary
  constant `K_sh = 3^{s/4} T²` of `AssemblyFeed.summable_annFam_grad` /
  `…_l2`, which is quantified inside a `Summable` claim and never reaches the
  display.  **No output constant changes**: the endpoint's constant is the same
  `clauseOneOutConstant C₁ C₂ K_tail C_shom` as in A6a.
* `ε` disappears from the statement entirely, together with `0 ≤ ε` and the
  containment side condition `s ε ≤ 1` of
  `ClauseOneConditional.goodEventBase_subset_annularEvent`.
* `0 ≤ C₁`, `0 ≤ C₂` are strengthened to `0 < C₁`, `0 < C₂`, so that the output
  constant is positive.  This is what the `⊤` branch of the dichotomy consumes,
  and it is the positivity the frozen `∃ C, 0 < C` already carries.

The quadratic `𝒢₁` readings of `EventReading` (`tsum_shellQuarter_le_of_eventG1`
and its kin) — the ones that would degrade from `T²` to `T'² = c⋆ γ^{−1}` — are
**not** used by clause (i) at all.  They are consumed by
the clause-(ii) budget `ClauseTwo.clauseOneDisplayRhs_le_of_goodEventBase`, which
legitimately runs on the smaller `goodEventBase` (the manuscript's own
`e.lambda.good.events`) and is untouched here.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Section3
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the honest amplitude and the positive output constant -/

/-- The square of the honest amplitude: `T'² = c⋆ γ^{−1}`. -/
theorem annularEventAmplitude_sq (M : ABKModel d) :
    (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) ^ 2
      = Disorder.cstar M * (M.gamma)⁻¹ := by
  have hc : Real.sqrt (Disorder.cstar M) ^ 2 = Disorder.cstar M :=
    Real.sq_sqrt (Disorder.cstar_characterization M).1.le
  have hg : Real.sqrt M.gamma ^ 2 = M.gamma :=
    Real.sq_sqrt M.shellPrefix.gamma_pos.le
  have hexp : (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) ^ 2
      = Real.sqrt (Disorder.cstar M) ^ 2 * ((Real.sqrt M.gamma) ^ 2)⁻¹ := by
    rw [← inv_pow]
    ring
  rw [hexp, hc, hg]

/-- The output constant of the clause-(i) composite is **positive** as soon as
the two slot constants are.  This is the input of the dichotomy's `⊤` branch. -/
theorem clauseOneOutConstant_pos {C₁ C₂ Ktail Cshom : ℝ} (hC₁ : 0 < C₁)
    (hC₂ : 0 < C₂) (hKtail : 0 ≤ Ktail) (hCshom : 6 ≤ Cshom) :
    0 < clauseOneOutConstant C₁ C₂ Ktail Cshom := by
  have h1 : (0 : ℝ) < 1 + Ktail := by linarith only [hKtail]
  have hleg : (0 : ℝ) < clauseOneLegConstant C₁ C₂ Ktail := by
    unfold clauseOneLegConstant
    exact mul_pos (mul_pos (by norm_num) hC₁) (mul_pos h1 hC₂)
  have hCs2 : (36 : ℝ) ≤ Cshom ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 6) hCshom 2
    calc (36 : ℝ) = (6 : ℝ) ^ 2 := by norm_num
      _ ≤ Cshom ^ 2 := h
  have hbig : (0 : ℝ) < 7000 * Cshom ^ 2 := by linarith only [hCs2]
  unfold clauseOneOutConstant
  exact mul_pos (by linarith only [hleg]) hbig

end

end Algsuperdiff.Section4.Provider.Annular
