/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastHvarFamily

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastAccountClauses

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The remaining account clauses

Beyond the three `scaleVariance` slots and the mean-drop slot,
`exists_account_one_step_entry_of_block_at_level` asks for three further
families of hypotheses.  This file produces all of them, grouped by kind:

* **the exponent pack** — `0 < ρ`, `ρ < 1`, `g ≤ ρ` at `ρ = contrastRho g`,
  and `0 < α ≤ 1/2` at `α = recursionAlpha g`;
* **the Schur pack** — the Schur data of the terminal adapted mean, together
  with the identity that makes the `htr` clause an *equality* at
  `eps = hatExcessAt P q t`;
* **the smallness pack** — `heps1`, `hsmall`, `hdrop` and `hdropSmall`, all
  from the single scalar `hatExcessAt P q k ≤ δ` with `δ ≤ 1/9`.

Only `hpos : 0 < eps` is left to the caller: at `eps = 0` the one-step
conclusion is trivial (its right side is nonnegative), so the composition
case-splits there.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The exponent pack -/

/-! ## The Schur pack -/

/-- **The Schur pack at the terminal mean.**  The Schur data exists, and the
account's `htr` clause holds with equality at `eps = hatExcessAt P q t`. -/
theorem schur_pack_at_terminal
    {P : Measure (CoeffSpace d)}
    {q : Mat d} {t : ℤ}
    (hsym : IsSymmetricBlockMat (adaptedMean P q t))
    (hpd : BlockPosDef (adaptedMean P q t)) :
    ∃ S0 SStar0 K0 : Mat d, S0.PosDef ∧ SStar0.PosDef ∧
      toFullBlockMat (adaptedMean P q t) = schurBlock S0 SStar0 K0 ∧
      (d : ℝ) * (schurHattedContrast S0 SStar0 - 1) = hatExcessAt P q t := by
  have hfull : (toFullBlockMat (adaptedMean P q t)).PosDef :=
    posDef_toFullBlockMat hsym hpd
  obtain ⟨S0, SStar0, K0, hS0, hStar0, hform⟩ := exists_schurBlock hfull
  refine ⟨S0, SStar0, K0, hS0, hStar0, hform, ?_⟩
  have hid : hattedContrast (adaptedMean P q t) =
      schurHattedContrast S0 SStar0 :=
    hattedContrast_eq_schurHattedContrast hStar0 hform
  rw [hatExcessAt, adaptedHattedContrast, hid]

/-! ## The smallness pack -/

/-- **The full smallness pack.**  From `δ ≤ 1/9` on the hatted excess over the
whole range, every remaining scalar clause of the account follows. -/
theorem account_smallness_pack [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q)
    (hfin : ∀ k : ℤ, HasFiniteAdaptedMean P q k)
    {t : ℤ} (hlt : l ≤ t) {delta : ℝ} (hdelta9 : delta ≤ 1 / 9)
    (hsm : ∀ k : ℤ, l ≤ k → k ≤ t → hatExcessAt P q k ≤ delta) :
    hatExcessAt P q t ≤ 1 ∧
      6 * (blockContrast (adaptedMean P q t) - 1) ≤ 1 ∧
      (∀ x y : ℤ, l ≤ x → x ≤ t →
        (d : ℝ) * (adaptedHattedContrast P q x -
          adaptedHattedContrast P q y) ≤ 1) := by
  have heps1 : hatExcessAt P q t ≤ 1 := by
    have := hsm t hlt le_rfl
    linarith only [this, hdelta9]
  refine ⟨heps1, contrast_smallness_of_hatExcess hgrid (hfin t)
    (hsm t hlt le_rfl) hdelta9, ?_⟩
  intro x y hlx hxt
  have hdr := hat_drop_le_hatExcess (P := P) (q := q) (j := x) (p := y)
    hgrid (hfin y)
  have hsmx := hsm x hlx hxt
  have : (d : ℝ) * (adaptedHattedContrast P q x -
      adaptedHattedContrast P q y) ≤ delta := le_trans hdr hsmx
  linarith only [this, hdelta9]

end

end HCPolySupport.HighContrast.Quenched
