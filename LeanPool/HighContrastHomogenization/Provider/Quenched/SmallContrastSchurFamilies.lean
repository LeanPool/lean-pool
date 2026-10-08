/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBurnInUniform
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSubdivisionSupply

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSchurFamilies

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Schur families, chosen once

The account core body takes the Schur data as `ℕ`-indexed families
`S0 SStar0 K0 : ℕ → Mat d` — the choice-free design.
`schur_data_at_generation` supplies the data at
each generation individually; this file turns that pointwise existence into the
families, and it is **the only place in the whole development where choice is
introduced deliberately**.

Everything downstream of the account core body therefore has a clean
provenance for its `Classical.choice`: it enters here, once, by `choose` on a
generation-indexed family, and nowhere else in the account.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- **The Schur families.**  Pointwise Schur data at every generation, chosen
into three `ℕ`-indexed families with their three properties. -/
theorem exists_schur_families {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q)
    (hfin : ∀ k : ℤ, HasFiniteAdaptedMean P q k) (N₀ : ℕ) :
    ∃ S0 SStar0 K0 : ℕ → Mat d,
      (∀ m : ℕ, (S0 m).PosDef) ∧ (∀ m : ℕ, (SStar0 m).PosDef) ∧
        (∀ m : ℕ, toFullBlockMat (adaptedMean P q ((N₀ : ℤ) + (m : ℤ))) =
          schurBlock (S0 m) (SStar0 m) (K0 m)) := by
  classical
  choose S0 SStar0 K0 hS0 hSStar0 hform _hcon using
    fun m : ℕ => schur_data_at_generation hq hfin ((N₀ : ℤ) + (m : ℤ))
  exact ⟨S0, SStar0, K0, hS0, hSStar0, hform⟩

end

end HCPolySupport.HighContrast.Quenched
