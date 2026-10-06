/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Geometry.TwoGridWhitney
public import LeanPool.HighContrastHomogenization.Entry.Geometry.RoundedGridBasic
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# High-contrast homogenization: Entry.TwoGridWhitney

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The two-grid Whitney lemma

The type of `l.two.grid.whitney`.
The source-constant family is chosen before `K₀`; the geometric constant
is chosen before `γ`. The constant-one family only supplies the unused
standing threshold of this pure geometry theorem, not a stochastic source
estimate. No definition or selection rule is replaced.
-/

open HCPolySupport.HighContrast (gridRatio)
namespace HCPolySupport.HighContrast.Entry

open MeasureTheory

/-- Both Whitney constructions, with finite center rows, null
exhaustion, the genuine infinite mass identity, and all printed bounds. -/
theorem two_grid_whitney
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ Csrc : ℝ → ℝ, (∀ γ : ℝ, γ ∈ Set.Ico (0 : ℝ) 1 → 0 < Csrc γ) ∧
      ∀ (K₀ : ℝ) (_hK₀ : 1 ≤ K₀),
      ∃ C : ℝ, 0 < C ∧
      ∀ γ : ℝ, γ ∈ Set.Ico (0 : ℝ) 1 →
      ∀ K : ℝ, 1 < K →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
        ⌈Csrc γ * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
        ∀ (m m' : Mat d), m.PosDef → m'.PosDef →
          gridRatio (Geometry.explicitRoundedGrid jStar m) (Geometry.explicitRoundedGrid jStar m') ≤ K₀ →
            ∀ (j : ℤ) (ℓ : ℕ), 1 ≤ ℓ →
              (∀ y ∈ adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar m') j,
                ∃ hfin : ∀ r : ℤ, r ≤ j - (ℓ : ℤ) →
                    (maximalAdaptedCellCenters
                      (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m') j y)
                      (Geometry.explicitRoundedGrid jStar m) (j - (ℓ : ℤ)) r).Finite,
                  (∀ (r : ℤ) (w : Fin d → ℤ),
                      IsMaximalAdaptedCellIn
                        (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m') j y)
                        (Geometry.explicitRoundedGrid jStar m) (j - (ℓ : ℤ)) r w →
                      adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar m) r w ⊆
                        HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m') j y) ∧
                    Set.PairwiseDisjoint
                      {p : ℤ × (Fin d → ℤ) |
                        IsMaximalAdaptedCellIn
                          (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m') j y)
                          (Geometry.explicitRoundedGrid jStar m) (j - (ℓ : ℤ)) p.1 p.2}
                      (fun p => adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar m) p.1 p.2) ∧
                    volume
                        (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m') j y \
                          ⋃ p ∈ {p : ℤ × (Fin d → ℤ) |
                              IsMaximalAdaptedCellIn
                                (HighContrast.adaptedCellTranslate
                                  (Geometry.explicitRoundedGrid jStar m') j y)
                                (Geometry.explicitRoundedGrid jStar m) (j - (ℓ : ℤ)) p.1 p.2},
                            adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar m) p.1 p.2) = 0 ∧
                    (∀ r : ℤ, r ≤ j - (ℓ : ℤ) →
                      (volume (HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) r)).toReal /
                          (volume (HighContrast.adaptedCellTranslate
                            (Geometry.explicitRoundedGrid jStar m') j y)).toReal ≤
                        C * (3 : ℝ) ^ (-(d : ℝ) * ((j : ℝ) - (r : ℝ)))) ∧
                    (((hfin (j - (ℓ : ℤ)) le_rfl).toFinset.card : ℝ) ≤
                      C * (3 : ℝ) ^ ((d : ℝ) * (ℓ : ℝ))) ∧
                    (∀ (r : ℤ) (hr : r < j - (ℓ : ℤ)),
                      ((hfin r hr.le).toFinset.card : ℝ) ≤
                        C * (3 : ℝ) ^ (((d : ℝ) - 1) * ((j : ℝ) - (r : ℝ)))) ∧
                    (∑' r : {r : ℤ // r ≤ j - (ℓ : ℤ)},
                        ∑ _z ∈ (hfin r.1 r.2).toFinset,
                          (volume (HighContrast.adaptedCell
                              (Geometry.explicitRoundedGrid jStar m) r.1)).toReal /
                            (volume (HighContrast.adaptedCellTranslate
                              (Geometry.explicitRoundedGrid jStar m') j y)).toReal) = 1 ∧
                    (∀ (r : ℤ) (hr : r < j - (ℓ : ℤ)),
                      ∑ _z ∈ (hfin r hr.le).toFinset,
                          (volume (HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) r)).toReal /
                            (volume (HighContrast.adaptedCellTranslate
                              (Geometry.explicitRoundedGrid jStar m') j y)).toReal ≤
                        C * (3 : ℝ) ^ ((r : ℝ) - (j : ℝ)))) ∧
                (∀ y ∈ adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar m) j,
                  ∃ hfin : ∀ r : ℤ, r ≤ j - (ℓ : ℤ) →
                      (maximalAdaptedCellCenters
                        (adaptedUncoveredPart
                          (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j y)
                          (Geometry.explicitRoundedGrid jStar m') (j - (ℓ : ℤ)))
                        (Geometry.explicitRoundedGrid jStar m) (j - (ℓ : ℤ)) r).Finite,
                    (∀ (r : ℤ) (w : Fin d → ℤ),
                        IsMaximalAdaptedCellIn
                          (adaptedUncoveredPart
                            (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j y)
                            (Geometry.explicitRoundedGrid jStar m') (j - (ℓ : ℤ)))
                          (Geometry.explicitRoundedGrid jStar m) (j - (ℓ : ℤ)) r w →
                        adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar m) r w ⊆
                          adaptedUncoveredPart
                            (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j y)
                            (Geometry.explicitRoundedGrid jStar m') (j - (ℓ : ℤ))) ∧
                      Set.PairwiseDisjoint
                        {p : ℤ × (Fin d → ℤ) |
                          IsMaximalAdaptedCellIn
                            (adaptedUncoveredPart
                              (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j y)
                              (Geometry.explicitRoundedGrid jStar m') (j - (ℓ : ℤ)))
                            (Geometry.explicitRoundedGrid jStar m) (j - (ℓ : ℤ)) p.1 p.2}
                        (fun p => adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar m) p.1 p.2) ∧
                      volume
                          (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j y \
                            (adaptedCoveredPart
                                (HighContrast.adaptedCellTranslate
                                  (Geometry.explicitRoundedGrid jStar m) j y)
                                (Geometry.explicitRoundedGrid jStar m') (j - (ℓ : ℤ)) ∪
                              ⋃ p ∈ {p : ℤ × (Fin d → ℤ) |
                                  IsMaximalAdaptedCellIn
                                    (adaptedUncoveredPart
                                      (HighContrast.adaptedCellTranslate
                                        (Geometry.explicitRoundedGrid jStar m) j y)
                                      (Geometry.explicitRoundedGrid jStar m') (j - (ℓ : ℤ)))
                                    (Geometry.explicitRoundedGrid jStar m) (j - (ℓ : ℤ)) p.1 p.2},
                                adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar m) p.1 p.2)) = 0 ∧
                      (∀ (r : ℤ) (hr : r ≤ j - (ℓ : ℤ)),
                        ∑ _z ∈ (hfin r hr).toFinset,
                            (volume (HighContrast.adaptedCell
                                (Geometry.explicitRoundedGrid jStar m) r)).toReal /
                              (volume (HighContrast.adaptedCellTranslate
                                (Geometry.explicitRoundedGrid jStar m) j y)).toReal ≤
                          C * (3 : ℝ) ^ ((r : ℝ) - (j : ℝ)))) := by
  let : NeZero d := ⟨by omega⟩
  refine ⟨fun _ => 1, fun _ _ => zero_lt_one, ?_⟩
  intro K₀ hK₀
  obtain ⟨C₁, hC₁, hfirst⟩ := Geometry.two_grid_whitney_part_one d hd K₀ hK₀
  obtain ⟨C₂, _hC₂, hsecond⟩ := Geometry.two_grid_whitney_part_two d hd K₀ hK₀
  refine ⟨max C₁ C₂, hC₁.trans_le (le_max_left _ _), ?_⟩
  intro _γ _hγ _K _hK jStar hj _hsrc m m' hm hm' hratio j ℓ hℓ
  have hq := Geometry.isUnit_roundedGrid hj hm
  have hq' := Geometry.isUnit_roundedGrid hj hm'
  have hℓz : (1 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast hℓ
  constructor
  · intro y _hy
    obtain ⟨hfin, hsub, hdis, hnull, hvol, hcap, hcount, hsum, hrow⟩ :=
      hfirst (Geometry.explicitRoundedGrid jStar m) (Geometry.explicitRoundedGrid jStar m')
        hq hq' hratio j (ℓ : ℤ) hℓz y
    refine ⟨hfin, hsub, hdis, hnull, ?_, ?_, ?_, hsum, ?_⟩
    · intro r hr
      exact (hvol r hr).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · exact hcap.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · intro r hr
      exact (hcount r hr).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · intro r hr
      exact (hrow r hr).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · intro y _hy
    obtain ⟨hfin, hsub, hdis, hnull, hrow⟩ :=
      hsecond (Geometry.explicitRoundedGrid jStar m) (Geometry.explicitRoundedGrid jStar m')
        hq hq' hratio j (j - (ℓ : ℤ)) y
    refine ⟨hfin, hsub, hdis, hnull, ?_⟩
    intro r hr
    exact (hrow r hr).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end HCPolySupport.HighContrast.Entry
