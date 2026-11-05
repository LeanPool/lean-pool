/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.AffineExcess
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.IterationLemmaProvider

/-!
# IterationLemma

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open HCPolySupport MeasureTheory

/-!
# The iteration lemma — [ABK] `l.iteration.lemma`

A one-step affine excess decay by a factor `theta^h`, valid at every scale
outside a bad set `B`, iterates across the whole range of scales.  The two
conclusions are a normalized `L^2` oscillation bound and an affine excess
bound at the bottom scale, both losing only `exp(C (h+1)(|B|+1))` and an
additive `theta`-power for the bad scales, plus the accumulated defects.

Proved; reduces to the standard axioms.
-/

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section4.iteration_lemma
    (d : ℕ) (hd : d ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (h : ℕ) (θ : ℝ), θ ∈ Set.Ioo (0 : ℝ) 1 → θ ^ h ∈ Set.Ioo (0 : ℝ) (3 / 5) →
        ∀ n m : ℤ, n < m →
          ∀ U : ℤ → Set (HCPolySupport.Vec d),
            (∀ j : ℤ, j ≤ m → MeasurableSet (U j)) →
            (∀ j : ℤ, j ≤ m → U (j - 1) ⊆ U j) →
            (∀ j : ℤ, j ≤ m →
                ∃ x y : HCPolySupport.Vec d,
                  (fun v => x + v) ''
                      HCPolySupport.openCubeSet
                        (HCPolySupport.originCube d (j - 2)) ⊆ U j ∧
                    U j ⊆
                      (fun v => y + v) ''
                        HCPolySupport.openCubeSet (HCPolySupport.originCube d j)) →
            ∀ u : HCPolySupport.Vec d → ℝ,
              MeasureTheory.MemLp u 2 (MeasureTheory.volume.restrict (U m)) →
              ∀ B : Finset ℤ, B ⊆ Finset.Icc n m →
                ∀ ε δ : ℤ → ℝ,
                  (∀ j : ℤ, n ≤ j → j ≤ m → 0 ≤ ε j) →
                  (∀ j : ℤ, n ≤ j → j ≤ m → 0 ≤ δ j) →
                  ∀ (c : ℤ → ℝ) (g : ℤ → HCPolySupport.Vec d),
                    (∀ j : ℤ, j ≤ m →
                        Algsuperdiff.Section4.Support.IsAffineMinimizer
                          (U j) u (c j) (g j)) →
                    (∀ j : ℤ, n ≤ j → j ≤ m → j ∉ B →
                        Algsuperdiff.Section4.Support.affineExcess
                            (U (j - (h : ℤ))) u ≤
                          θ ^ h *
                              Algsuperdiff.Section4.Support.affineExcess (U j) u +
                            ε j *
                              Algsuperdiff.Section4.Support.slopeMagnitude (g j) +
                            δ j) →
                    ((3 : ℝ) ^ (-n) *
                        Algsuperdiff.Section4.Support.normalizedL2On (U n)
                          (fun x => u x - HCPolySupport.volumeAverage (U n) u) ≤
                      Real.exp
                          (C * ((h : ℝ) + 1) * ((B.card : ℝ) + 1) +
                            C * ∑ j ∈ Finset.Icc n m, ε j) *
                        ((3 : ℝ) ^ (-m) *
                            Algsuperdiff.Section4.Support.normalizedL2On (U m)
                              (fun x => u x - HCPolySupport.volumeAverage (U m) u) +
                          ∑ j ∈ Finset.Icc n m, δ j)) ∧
                      ∀ M : ℝ, (∀ j : ℤ, n ≤ j → j ≤ m → ε j ≤ M) →
                          Algsuperdiff.Section4.Support.affineExcess (U n) u ≤
                            Real.rpow θ
                                  (-(C * ((h : ℝ) + 1) * ((B.card : ℝ) + 1))) *
                                Real.exp
                                  (C * ((h : ℝ) + 1) * ((B.card : ℝ) + 1) +
                                    C * ∑ j ∈ Finset.Icc n m, ε j) *
                              (θ ^ (m - n) *
                                  Algsuperdiff.Section4.Support.affineExcess (U m) u +
                                M *
                                    ((3 : ℝ) ^ (-m) *
                                      Algsuperdiff.Section4.Support.normalizedL2On (U m)
                                        (fun x => u x - HCPolySupport.volumeAverage (U m) u)) +
                                (1 + M) * ∑ j ∈ Finset.Icc n m, δ j)
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section4.Provider.ExcessDecay.iteration_lemma_provider d hd
