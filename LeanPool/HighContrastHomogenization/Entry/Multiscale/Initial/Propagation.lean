/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Initial.CrudeProfile
public import LeanPool.HighContrastHomogenization.Entry.OneGridPropagation

/-!
# High-contrast homogenization: Entry.Multiscale.Initial.Propagation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Initialization: the one-grid propagation statement at the Euclidean grid

The one-grid propagation statement
`HCPolySupport.HighContrast.Entry.fixed_geometry_one_grid_propagation_full`
(`HCPoly/Entry/OneGridPropagation.lean`, `p.fixed.geometry.one.grid.propagation`) is specialized
to the
Euclidean grid `metric = 1`, where `Geometry.explicitRoundedGrid jStar 1 = 1`: its conjuncts 5, 6
and 7 become the carried-history majorization, the synchronized propagation step and the
synchronized multiplicity budget used in Steps 2 and 3 of
`p.initial.fixed.grid.scale`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator MatrixOrder

noncomputable section

/-! ## E. Steps 2–3 — logarithmic decrement and the hitting index
(`p.initial.fixed.grid.scale`).  The one-grid propagation statement enters through
`one_grid_propagation_input`, which repeats the exact type of
`HCPolySupport.HighContrast.Entry.fixed_geometry_one_grid_propagation_full`
(`HCPoly/Entry/Statements/OneGridPropagation.lean`, byte for byte) and is discharged by one direct
application of the statement proved in `HCPoly/Entry/OneGridPropagation.lean`. -/

/-- Exact bridge to the one-grid propagation statement. -/
theorem one_grid_propagation_input
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (h : ℕ), 2 * bigQ d γ ≤ h →
          ∀ L : ℤ, 1 ≤ L →
            ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
              ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
              ∀ (metric : Mat d), metric.PosDef →
                ∀ n m : ℤ, (jStar : ℤ) ≤ n → n ≤ m →
                  history P γ (Geometry.explicitRoundedGrid jStar metric) jStar m ≤
                      C * profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m ∧
                    (n + (h : ℤ) ≤ m →
                      profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + (h :
                        ℤ)) ≤
                        1 / 8 *
                            Real.exp ((bigQ d γ : ℝ) *
                              synchCharge P (Geometry.explicitRoundedGrid jStar metric)
                                (h : ℤ) m) *
                            profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                          C *
                            (Real.exp ((bigQ d γ : ℝ) *
                                synchCharge P (Geometry.explicitRoundedGrid jStar metric)
                                  (h : ℤ) m) - 1)) ∧
                    (n + (h : ℤ) ≤ m →
                      profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m ≤ 1 →
                        profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + L) ≤
                          C * (L : ℝ) *
                            (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                              Real.exp ((bigQ d γ : ℝ) *
                                detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m
                                  + L)) - 1)) ∧
                    (m = n →
                      history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n ≤ 1 →
                        profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (n + L) ≤
                          C * (L : ℝ) *
                            (history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n +
                              Real.exp ((bigQ d γ : ℝ) *
                                detIncrement P (Geometry.explicitRoundedGrid jStar metric) n (n
                                  + L)) - 1)) ∧
                    fluctuationHistory P γ (Geometry.explicitRoundedGrid jStar metric) jStar m +
                          meanHistory P γ (Geometry.explicitRoundedGrid jStar metric) (jStar :
                            ℤ) m +
                          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m ≤
                        C * (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar
                            m) ∧
                    (n + (h : ℤ) ≤ m →
                      profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + (h :
                        ℤ)) +
                          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar
                            (m + (h : ℤ)) ≤
                        1 / 8 *
                            Real.exp ((bigQ d γ : ℝ) *
                              synchCharge P (Geometry.explicitRoundedGrid jStar metric)
                                (h : ℤ) m) *
                            (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                              determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric)
                                jStar m) +
                          C *
                            (Real.exp ((bigQ d γ : ℝ) *
                                synchCharge P (Geometry.explicitRoundedGrid jStar metric)
                                  (h : ℤ) m) - 1)) ∧
                    (∀ m₀ : ℤ, (jStar : ℤ) + (h : ℤ) ≤ m₀ →
                      ∀ Ksteps : ℕ, 1 ≤ Ksteps →
                        ∑ k ∈ Finset.range Ksteps,
                            synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ)
                              (m₀ + (k : ℤ) * (h : ℤ)) ≤
                          (h : ℝ) *
                            detIncrement P (Geometry.explicitRoundedGrid jStar metric)
                              (m₀ + 1 - (h : ℤ)) (m₀ + (Ksteps : ℤ) * (h : ℤ))) ∧
                    ((m = n ∨ n + (h : ℤ) ≤ m) →
                      profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar
                            m ≤ 1 →
                        profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + L) +
                            determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric)
                              jStar (m + L) ≤
                          C * (L : ℝ) *
                            (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                              determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric)
                                jStar m +
                              Real.exp ((bigQ d γ : ℝ) *
                                detIncrement P (Geometry.explicitRoundedGrid jStar metric) m
                                  (m + L)) - 1)) := by
  exact HCPolySupport.HighContrast.Entry.fixed_geometry_one_grid_propagation_full d hd γ hγ

/-- E1. `e.fixed.geometry.carried.majorization` on the Euclidean grid (the one-grid statement's
conjunct 5 at
`metric = 1`, `h = 2Q`, `L = 1`). -/
theorem carried_history_majorization_one (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
          (Src : CoeffSpace d → ℝ),
          IsProbabilityMeasure P →
          IsStationaryLaw P →
          IsUnitRangeLaw P →
          CoarseEllipticityDagger P γ E Ψ K Src →
          ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
            ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
            ∀ n m : ℤ, (jStar : ℤ) ≤ n → n ≤ m →
              fluctuationHistory P γ (1 : Mat d) jStar m +
                    meanHistory P γ (1 : Mat d) (jStar : ℤ) m +
                    determinantDrift P γ (1 : Mat d) jStar m ≤
                  C * (profile P γ (1 : Mat d) jStar n m +
                    determinantDrift P γ (1 : Mat d) jStar m) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Csrc, hCsrc, C, hC, hprov⟩ := one_grid_propagation_input d hd γ hγ
  refine ⟨Csrc, hCsrc, C, hC, ?_⟩
  intro P E Ψ K Src hP hstat hunit hdag jStar hjStar hthr n m hn hnm
  have H := hprov P E Ψ K Src hP hstat hunit hdag (2 * bigQ d γ) le_rfl 1 le_rfl jStar hjStar
    hthr (1 : Mat d) (Geometry.one_posDef d) n m hn hnm
  simpa only [Geometry.explicitRoundedGrid_one (d := d) jStar] using H.2.2.2.2.1

/-- E2. `e.fixed.geometry.synchronized.propagation` on the Euclidean grid (the one-grid statement's
conjunct 6 at `metric = 1`). -/
theorem synchronized_propagation_one (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
          (Src : CoeffSpace d → ℝ),
          IsProbabilityMeasure P →
          IsStationaryLaw P →
          IsUnitRangeLaw P →
          CoarseEllipticityDagger P γ E Ψ K Src →
          ∀ (h : ℕ), 2 * bigQ d γ ≤ h →
            ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
              ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
              ∀ n m : ℤ, (jStar : ℤ) ≤ n → n + (h : ℤ) ≤ m →
                profile P γ (1 : Mat d) jStar n (m + (h : ℤ)) +
                    determinantDrift P γ (1 : Mat d) jStar (m + (h : ℤ)) ≤
                  1 / 8 *
                      Real.exp ((bigQ d γ : ℝ) *
                        synchCharge P (1 : Mat d) (h : ℤ) m) *
                      (profile P γ (1 : Mat d) jStar n m +
                        determinantDrift P γ (1 : Mat d) jStar m) +
                    C * (Real.exp ((bigQ d γ : ℝ) *
                      synchCharge P (1 : Mat d) (h : ℤ) m) - 1) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Csrc, hCsrc, C, hC, hprov⟩ := one_grid_propagation_input d hd γ hγ
  refine ⟨Csrc, hCsrc, C, hC, ?_⟩
  intro P E Ψ K Src hP hstat hunit hdag h hh jStar hjStar hthr n m hn hnm
  have H := hprov P E Ψ K Src hP hstat hunit hdag h hh 1 le_rfl jStar hjStar hthr
    (1 : Mat d) (Geometry.one_posDef d) n m hn (by omega)
  simpa only [Geometry.explicitRoundedGrid_one (d := d) jStar] using H.2.2.2.2.2.1 hnm

/-- E3. `e.fixed.geometry.synchronized.multiplicity` on the Euclidean grid (the one-grid statement's
conjunct 7 at `metric = 1`). -/
theorem synchronized_multiplicity_one (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (Src : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K Src →
        ∀ (h : ℕ), 2 * bigQ d γ ≤ h →
          ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
            ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
            ∀ m₀ : ℤ, (jStar : ℤ) + (h : ℤ) ≤ m₀ →
              ∀ Ksteps : ℕ, 1 ≤ Ksteps →
                ∑ k ∈ Finset.range Ksteps,
                    synchCharge P (1 : Mat d) (h : ℤ) (m₀ + (k : ℤ) * (h : ℤ)) ≤
                  (h : ℝ) *
                    detIncrement P (1 : Mat d) (m₀ + 1 - (h : ℤ))
                      (m₀ + (Ksteps : ℤ) * (h : ℤ)) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Csrc, hCsrc, _C, _hC, hprov⟩ := one_grid_propagation_input d hd γ hγ
  refine ⟨Csrc, hCsrc, ?_⟩
  intro P E Ψ K Src hP hstat hunit hdag h hh jStar hjStar hthr m₀ hm₀ Ksteps hK
  have H := hprov P E Ψ K Src hP hstat hunit hdag h hh 1 le_rfl jStar hjStar hthr
    (1 : Mat d) (Geometry.one_posDef d) (jStar : ℤ) (jStar : ℤ) le_rfl le_rfl
  simpa only [Geometry.explicitRoundedGrid_one (d := d) jStar] using H.2.2.2.2.2.2.1 m₀ hm₀
    Ksteps hK

end

end HCPolySupport.HighContrast.Multiscale
