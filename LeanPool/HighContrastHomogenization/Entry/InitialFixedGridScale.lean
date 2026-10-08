/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Initial.EntryGeneration

/-!
# High-contrast homogenization: Entry.InitialFixedGridScale

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Initialization fixed-grid-scale

The type repeats the initialization statement
`HCPoly/Entry/Statements/InitialFixedGridScale.lean` (`p.initial.fixed.grid.scale`): same binders,
same binder kinds and
order, same six conjuncts, the source-lower-scale premise where the statement has it, and no
additional hypothesis.  The two unused ∀ binders carry a leading underscore: `_hγ`, `_hS`.

The proof combines the entry generation from Step 3 and the geometry from Step 4. It
chooses `Cgeom` before `γ` and `S`, `Csrc` after `S` and before `ηinit`, and `C` after
`ηinit` and before the remaining data.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean aspectRatio blockScale)
namespace HCPolySupport.HighContrast.Entry

open MeasureTheory

noncomputable section

/-- **Proof of `p.initial.fixed.grid.scale`.**  Repeats the statement of
`HCPolySupport.HighContrast.initial_fixed_grid_scale`
(`HCPoly/Entry/Statements/InitialFixedGridScale.lean`,
`p.initial.fixed.grid.scale`) byte for byte up to the
underscore-prefixed unused binders `_hγ`, `_hS`: same binder kinds and order, `Cgeom` before
`γ` and `S`, `Csrc` after `S` and before `η_init`, `C` after `η_init` and before `ε`, `σ`, the
law, `j_*` and `B`, the source-scale premise, and the six conjuncts in the printed order. -/
theorem initial_fixed_grid_scale
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ Cgeom : ℝ, 0 < Cgeom ∧
      ∀ (γ : ℝ) (_hγ : γ ∈ Set.Ico (0 : ℝ) 1),
      ∀ (S : SelectionData) (_hS : S.Selects d γ),
      ∃ Csrc : ℝ, 0 < Csrc ∧
        ∀ ηinit : ℝ, ηinit ∈ Set.Ioc (0 : ℝ) 1 →
          ∃ C : ℝ, 0 < C ∧
            ∀ ε σ : ℝ, 0 < σ → σ ≤ ε → ε ≤ S.eps0 →
              ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
                (Src : CoeffSpace d → ℝ),
                IsProbabilityMeasure P →
                IsStationaryLaw P →
                IsUnitRangeLaw P →
                CoarseEllipticityDagger P γ E Ψ K Src →
                ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
                  ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
                    ∀ B : ℝ, S.B0 ε σ ≤ B →
                      ∃ n₀ : ℤ,
                        (jStar : ℤ) + ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ ≤ n₀ ∧
                          n₀ ≤ (jStar : ℤ) + ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ +
                            ⌈C * Real.logb 3 (2 + aspectRatio E)⌉ ∧
                          profile P γ (1 : Mat d) jStar n₀ n₀ +
                              determinantDrift P γ (1 : Mat d) jStar n₀ ≤ ηinit ∧
                          BlockMatLoewnerLE
                            (blockScale (1 / 2)
                              (ofFullBlockMat
                                (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ *
                                  toFullBlockMat (blockSwap d))))
                            (adaptedMean P (1 : Mat d) n₀) ∧
                          BlockMatLoewnerLE (adaptedMean P (1 : Mat d) n₀) (blockScale 2 E) ∧
                          projectiveDistance (1 : Mat d)
                              (explicitCanonicalMetric (adaptedMean P (1 : Mat d) n₀)) ≤
                            Cgeom * Real.log (2 + 4 * aspectRatio E) := by
  obtain ⟨Cgeom, hCgeom, hgeo⟩ := Multiscale.geometry_at_generation d hd
  refine ⟨Cgeom, hCgeom, ?_⟩
  intro γ hγ S _hS
  obtain ⟨Cs₁, hCs₁, hgeoγ⟩ := hgeo γ hγ
  obtain ⟨Cs₂, hCs₂, hgen⟩ := Multiscale.exists_entry_generation d hd γ hγ
  refine ⟨max Cs₁ Cs₂, lt_of_lt_of_le hCs₁ (le_max_left _ _), ?_⟩
  intro ηinit hηinit
  obtain ⟨C, hCpos, hgen'⟩ := hgen ηinit hηinit
  refine ⟨C, hCpos, ?_⟩
  intro ε σ hσ hσε hε P E Ψ K Src hP hstat hunit hdag jStar hjStar hthr B hB
  have : NeZero d := ⟨by omega⟩
  have := hP
  have h₁ : ⌈Cs₁ * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    Multiscale.ceil_source_threshold_le_of_le K hdag.one_lt_growthWitness Cs₁ (max Cs₁ Cs₂)
      (le_max_left _ _) jStar hthr
  have h₂ : ⌈Cs₂ * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    Multiscale.ceil_source_threshold_le_of_le K hdag.one_lt_growthWitness Cs₂ (max Cs₁ Cs₂)
      (le_max_right _ _) jStar hthr
  have hB1 : (1 : ℝ) ≤ B :=
    le_trans (S.one_le_B0 ε σ ⟨lt_of_lt_of_le hσ hσε, hε⟩ ⟨hσ, hσε⟩) hB
  have hPi := HCPolySupport.HighContrast.Annealed.aspectRatio_pos_and_three_le hdag
  have hlogb1 : 1 ≤ Real.logb 3 (2 + aspectRatio E) :=
    Multiscale.one_le_logb_three_of_three_le (2 + aspectRatio E) hPi.2
  have hceilnn : (0 : ℤ) ≤ ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ :=
    Int.ceil_nonneg (by nlinarith only [hB1, hlogb1])
  have hR : (jStar : ℤ) ≤ (jStar : ℤ) + ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ := by
    linarith only [hceilnn]
  obtain ⟨n₀, hn₀lo, hn₀hi, hn₀small⟩ :=
    hgen' P E Ψ K Src hP hstat hunit hdag jStar hjStar h₂
      ((jStar : ℤ) + ⌈B * Real.logb 3 (2 + aspectRatio E)⌉) hR
  obtain ⟨hg1, hg2, hg3⟩ :=
    hgeoγ P E Ψ K Src hP hstat hunit hdag jStar hjStar h₁ n₀ (le_trans hR hn₀lo)
  exact ⟨n₀, hn₀lo, by linarith only [hn₀hi], hn₀small, hg1, hg2, hg3⟩

end

end HCPolySupport.HighContrast.Entry
