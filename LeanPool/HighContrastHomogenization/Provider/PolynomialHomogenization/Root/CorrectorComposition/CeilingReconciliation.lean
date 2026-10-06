/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.LargeScaleLipschitzFromProjection

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.CeilingReconciliation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Reconciling the five ceilings

Under the ceiling-exporting smallness interface ceiling-exporting interface the assembly
instantiates at the
minimum of the five ceilings.  This module proves that this is always
possible: from five
holes each exporting its own `g`-indexed ceiling, one **function**
`cStar : ℝ → ℝ` is produced that satisfies all five simultaneously at every
admissible `g`, together with `hhomogenized` at that same smallness.

Threading a function rather than a constant is what makes the interface
compatible with the assembly's binder order: its `GoodScale` is bound before
`g`, so the smallness cannot be a constant chosen after `g` — but it can be
`cStar g` for a `cStar` bound before `GoodScale`.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set
open RowSupply (eccentricityFoldFactor)

noncomputable section

variable {d : ℕ}

/-- **The five-ceiling reconciliation.**  Each `Qᵢ` is a hole's obligation at a
given smallness; each hole exports a ceiling below which its obligation holds.
One `g`-indexed smallness serves all five. -/
theorem exists_commonCeiling (Q₁ Q₂ Q₃ Q₄ Q₅ : ℝ → ℝ → Prop)
    (h₁ : ∀ g : ℝ, g ∈ Ico (0 : ℝ) 1 → ∃ cMax : ℝ, cMax ∈ Ioo (0 : ℝ) 1 ∧
      ∀ c : ℝ, c ∈ Ioo (0 : ℝ) 1 → c ≤ cMax → Q₁ g c)
    (h₂ : ∀ g : ℝ, g ∈ Ico (0 : ℝ) 1 → ∃ cMax : ℝ, cMax ∈ Ioo (0 : ℝ) 1 ∧
      ∀ c : ℝ, c ∈ Ioo (0 : ℝ) 1 → c ≤ cMax → Q₂ g c)
    (h₃ : ∀ g : ℝ, g ∈ Ico (0 : ℝ) 1 → ∃ cMax : ℝ, cMax ∈ Ioo (0 : ℝ) 1 ∧
      ∀ c : ℝ, c ∈ Ioo (0 : ℝ) 1 → c ≤ cMax → Q₃ g c)
    (h₄ : ∀ g : ℝ, g ∈ Ico (0 : ℝ) 1 → ∃ cMax : ℝ, cMax ∈ Ioo (0 : ℝ) 1 ∧
      ∀ c : ℝ, c ∈ Ioo (0 : ℝ) 1 → c ≤ cMax → Q₄ g c)
    (h₅ : ∀ g : ℝ, g ∈ Ico (0 : ℝ) 1 → ∃ cMax : ℝ, cMax ∈ Ioo (0 : ℝ) 1 ∧
      ∀ c : ℝ, c ∈ Ioo (0 : ℝ) 1 → c ≤ cMax → Q₅ g c) :
    ∃ cStar : ℝ → ℝ, ∀ g : ℝ, g ∈ Ico (0 : ℝ) 1 →
      cStar g ∈ Ioo (0 : ℝ) 1 ∧
      Q₁ g (cStar g) ∧ Q₂ g (cStar g) ∧ Q₃ g (cStar g) ∧
      Q₄ g (cStar g) ∧ Q₅ g (cStar g) := by
  classical
  refine ⟨fun g ↦ if hg : g ∈ Ico (0 : ℝ) 1 then
      min (Classical.choose (h₁ g hg))
        (min (Classical.choose (h₂ g hg))
          (min (Classical.choose (h₃ g hg))
            (min (Classical.choose (h₄ g hg))
              (Classical.choose (h₅ g hg))))) else 1 / 2, ?_⟩
  intro g hg
  obtain ⟨hm₁, hq₁⟩ := Classical.choose_spec (h₁ g hg)
  obtain ⟨hm₂, hq₂⟩ := Classical.choose_spec (h₂ g hg)
  obtain ⟨hm₃, hq₃⟩ := Classical.choose_spec (h₃ g hg)
  obtain ⟨hm₄, hq₄⟩ := Classical.choose_spec (h₄ g hg)
  obtain ⟨hm₅, hq₅⟩ := Classical.choose_spec (h₅ g hg)
  have hval : (if hg' : g ∈ Ico (0 : ℝ) 1 then
      min (Classical.choose (h₁ g hg'))
        (min (Classical.choose (h₂ g hg'))
          (min (Classical.choose (h₃ g hg'))
            (min (Classical.choose (h₄ g hg'))
              (Classical.choose (h₅ g hg'))))) else 1 / 2) =
      min (Classical.choose (h₁ g hg))
        (min (Classical.choose (h₂ g hg))
          (min (Classical.choose (h₃ g hg))
            (min (Classical.choose (h₄ g hg))
              (Classical.choose (h₅ g hg))))) := dite_eq_left hg
  simp only [hval]
  have hmem := minCeiling_mem hm₁ hm₂ hm₃ hm₄ hm₅
  exact ⟨hmem,
    hq₁ _ hmem minCeiling_le_one,
    hq₂ _ hmem minCeiling_le_two,
    hq₃ _ hmem minCeiling_le_three,
    hq₄ _ hmem minCeiling_le_four,
    hq₅ _ hmem minCeiling_le_five⟩

end

end CorrectorComposition
end HighContrast
end HCPolySupport
