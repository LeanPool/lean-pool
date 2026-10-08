/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAdjointMirrors
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAnnealedEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAverageDrops
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCenteringCap
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastLineProducer
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRowAtCenters
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakCap
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakValue
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormAdjointAlgebra
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungFixedGridCells
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowOscillationSum
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowSchur
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowSkewCarriers

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastRealClauses

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Three structural clauses for the generation-indexed estimate

This file supplies three hypotheses of `exists_one_step_with_slots_of_block_at_level_conv_split`
uniformly
in the generation.

* **The source clause is a threshold, and thresholds are monotone.**  Its
  exponent `(t - Hw) + (Gacc + 1) - sKw` is increasing in `n`, so assuming it at
  the delayed start `ns` gives it at every later generation by
  `zpow_le_zpow_right₀`.

* **The bootstrap floor is a hypothesis of Proposition 4.2, not a lemma.**
  `account_smallness_pack` *takes* `∀ k, l ≤ k → k ≤ t → hatExcessAt P q k ≤ δ`
  and does not produce it.  Stated over the whole ray `l ≤ k`, this hypothesis
  restricts to every `t = N₀ + n`.

* **The Schur data is structural.**  `schur_pack_at_terminal` needs only that
  `adaptedMean P q t` is symmetric and positive definite, and both hold at every
  scale (`isSymmetricBlockMat_adaptedMean`,
  `blockPosDef_adaptedMean_of_isRoundedGrid`).

Thus one clause is monotonicity of a threshold, one is a standing floor
hypothesis, and one follows from the Schur structure.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## Clause 1: the source threshold -/

/-! ## Clause 2: the bootstrap floor -/

/-! ## Clause 3: the Schur data -/

/-- **The Schur data exists at every generation**, from the structural facts
about the adapted mean alone. -/
theorem schur_data_at_generation {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q)
    (hfin : ∀ k : ℤ, HasFiniteAdaptedMean P q k) (t : ℤ) :
    ∃ S0 SStar0 K0 : Mat d, S0.PosDef ∧ SStar0.PosDef ∧
      toFullBlockMat (adaptedMean P q t) = schurBlock S0 SStar0 K0 ∧
      (d : ℝ) * (schurHattedContrast S0 SStar0 - 1) = hatExcessAt P q t :=
  schur_pack_at_terminal (Recurrence.isSymmetricBlockMat_adaptedMean P q t)
    (Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hq t (hfin t))

/-! ## The `eps = 0` case split -/

end

end HCPolySupport.HighContrast.Quenched
