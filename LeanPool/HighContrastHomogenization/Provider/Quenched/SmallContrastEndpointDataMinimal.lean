/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBurnInPolynomial

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastEndpointDataMinimal

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The endpoint's frozen-side data, with the burn-in's own upper bound

This is the half the polynomial burn-in cannot supply on its own.

`exists_endpoint_frozen_data_minimal` returns the burn-in `N1` as an existential
and records only `sK + 1 ≤ N1`.  That is everything the *account* needs and
nothing `hentry` needs: `hentry` must bound `3 ^ N1` **above** by a power of the
telescope's base, and an existential burn-in admits no upper bound at all.

The repair is the same one applied to the source scale and the gap
separately: expose the burn-in's decomposition.  `N1 = sK + 1 + gap` is how
`exists_bootstrap_smallness_uniform_minimal` builds it, and `gap` comes from the
gap existence statement, whose minimal companion
`exists_gap_three_pow_le_minimal` carries the upper bound
`3 ^ gap ≤ 3 * max 1 (CB * factor / sigma)` at no cost — the same `⌈log₃ ·⌉` witness, one more
conclusion.

So this file is a parallel restatement, not new mathematics: the same constant,
the same proof, with `gap` returned beside the data it determines.  With it and
`exists_source_scale_minimal`, `exists_burnIn_exponent_canonical` applies and `hentry`
closes.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

/-- **The bootstrap floor at a minimally chosen gap.**  The parallel of
`exists_bootstrap_smallness_uniform_minimal` that returns the gap it built the burn-in
from, together with the gap's own upper bound. -/
theorem exists_bootstrap_smallness_uniform_minimal (d : ℕ) (hd : 2 ≤ d) (g : ℝ)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    ∃ CB : ℝ, 0 < CB ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P → HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.IsUnitRangeLaw P →
        HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
        ∀ Cd : ℝ, max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd →
          ∀ sK : ℤ, 0 ≤ sK → growthBar K ≤ (3 : ℝ) ^ sK →
            ∀ mAl : Mat d, mAl.PosDef →
              ∀ sigma delta cStar : ℝ, 0 < sigma →
                (d : ℝ) *
                    bootstrapTiltPolynomial sigma ((d : ℝ) * cStar) ≤ delta →
                  annealedContrast P 0 - 1 ≤ cStar →
                  ∃ gap : ℤ, 1 ≤ gap ∧
                    (3 : ℝ) ^ gap ≤
                      3 * max 1 (CB * bootstrapAdapterFactor Cd g K E mAl /
                        sigma) ∧
                    ∀ lq : ℤ, (kZero d : ℤ) ≤ lq →
                      ∀ n : ℤ, sK + 1 + gap ≤ n →
                        hatExcessAt P (roundedGrid lq mAl) n ≤ delta := by
  classical
  obtain ⟨CB, hCB0, hCB⟩ := exists_bootstrap_tilt_bound d hd g hg
  refine ⟨CB, hCB0, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag Cd hCd sK hsK0 hsK mAl hmAl sigma
    delta cStar hsigma0 hcal hsmall
  have := hP
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have : NeZero d := ⟨by omega⟩
  have hone : (1 : ℝ) ≤ euclideanReferenceRatio Cd g K E := by
    have hburn : sK + 1 ≤ sK + 1 := le_rfl
    exact (reference_le_annealedBlock_centeredCube hd hg hdag hCd hsK hburn).1
  have hecc1 : (1 : ℝ) ≤ witnessEccentricity mAl :=
    Initialization.one_le_witnessEccentricity hmAl
  have hfac0 : 0 < bootstrapAdapterFactor Cd g K E mAl := by
    rw [bootstrapAdapterFactor]
    have hK : (0 : ℝ) < (1 + K ^ 2) ^ g :=
      Real.rpow_pos_of_pos (by positivity) g
    have h1 : (0 : ℝ) < (1 + K ^ 2) ^ g * euclideanReferenceRatio Cd g K E :=
      mul_pos hK (by linarith only [hone])
    exact mul_pos (by linarith only [hecc1]) h1
  obtain ⟨gap, hgap1, hgaple, hgapub⟩ :=
    exists_gap_three_pow_le_minimal (mul_pos hCB0 hfac0) hsigma0
  refine ⟨gap, hgap1, hgapub, ?_⟩
  intro lq hlq n hn
  exact le_trans (hCB P E Ψ K S hP hstat hunit hdag Cd hCd sK hsK0 hsK lq hlq
    mAl hmAl sigma cStar hsmall gap hgap1 hgaple n hn) hcal

/-- **The endpoint's frozen-side data, with the gap exposed.**  Identical to
`exists_endpoint_frozen_data_minimal` except that the burn-in is presented as
`sK + 1 + gap` with the gap's upper bound — which is exactly what
`exists_burnIn_exponent_canonical` consumes. -/
theorem exists_endpoint_frozen_data_minimal (d : ℕ) (hd : 2 ≤ d) (g : ℝ)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csub CB : ℝ, 0 < Csub ∧ 0 < CB ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P → HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.IsUnitRangeLaw P →
        HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
        ∀ Cd : ℝ, max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd →
          ∀ sK : ℤ, (kZero d : ℤ) ≤ sK → growthBar K ≤ (3 : ℝ) ^ sK →
            ∀ mAl : Mat d, mAl.PosDef →
              ∀ sigma delta cStar : ℝ, 0 < sigma →
                (d : ℝ) *
                    bootstrapTiltPolynomial sigma ((d : ℝ) * cStar) ≤ delta →
                  annealedContrast P 0 - 1 ≤ cStar →
                  ∃ gap : ℤ, 1 ≤ gap ∧
                    (3 : ℝ) ^ gap ≤
                      3 * max 1 (CB * bootstrapAdapterFactor Cd g K E mAl /
                        sigma) ∧
                    (kZero d : ℤ) ≤ sK + 1 + gap ∧
                    IsRoundedGrid (sK + 1 + gap)
                      (roundedGrid (sK + 1 + gap) mAl) ∧
                    (∀ k : ℤ, sK + 1 + gap ≤ k →
                      hatExcessAt P (roundedGrid (sK + 1 + gap) mAl) k ≤
                        delta) ∧
                    (∀ j' p' : ℤ, sK + 1 + gap ≤ j' → j' ≤ p' →
                      ∃ Z : Finset (Fin d → ℤ),
                        (↑Z : Set (Fin d → ℤ)) =
                            {w | adaptedCellCenter
                              (roundedGrid (sK + 1 + gap) mAl) j' w ∈
                              adaptedCell (roundedGrid (sK + 1 + gap) mAl) p'} ∧
                          Z.card = 3 ^ (d * (p' - j').toNat) ∧ Z.Nonempty ∧
                          lqSchattenSize P 2
                              (fun a ↦ blockSub
                                (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
                                  ∑ w ∈ Z,
                                    toFullBlockMat
                                      (coarseBlock
                                        (adaptedCellAt
                                          (roundedGrid (sK + 1 + gap) mAl)
                                          j' w) a)))
                                (adaptedMean P
                                  (roundedGrid (sK + 1 + gap) mAl) j'))
                                (adaptedMean P
                                  (roundedGrid (sK + 1 + gap) mAl) p') ≤
                            ENNReal.ofReal
                                (Csub * (Z.card : ℝ) ^ (-(2 : ℝ)⁻¹)) *
                              lqSchattenSize P 2
                                (fun a ↦ blockSub
                                  (coarseBlock
                                    (adaptedCell
                                      (roundedGrid (sK + 1 + gap) mAl) j') a)
                                  (adaptedMean P
                                    (roundedGrid (sK + 1 + gap) mAl) j'))
                                (adaptedMean P
                                  (roundedGrid (sK + 1 + gap) mAl) p')) := by
  classical
  obtain ⟨Csub, hCsub0, hsub⟩ := exists_repaired_subdivision_supply d hd
  obtain ⟨CB, hCB0, hboot⟩ := exists_bootstrap_smallness_uniform_minimal d hd g hg
  refine ⟨Csub, CB, hCsub0, hCB0, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag Cd hCd sK hsK hsKb mAl hmAl sigma delta
    cStar hsigma0 hcal hentry
  have hsK0 : (0 : ℤ) ≤ sK := le_trans (by positivity) hsK
  obtain ⟨gap, hgap1, hgapub, hfloor⟩ :=
    hboot P E Ψ K S hP hstat hunit hdag Cd hCd sK hsK0 hsKb mAl hmAl sigma
      delta cStar hsigma0 hcal hentry
  have hkzN1 : (kZero d : ℤ) ≤ sK + 1 + gap := by omega
  have hgridN1 : IsRoundedGrid (sK + 1 + gap)
      (roundedGrid (sK + 1 + gap) mAl) := ⟨hkzN1, mAl, hmAl, rfl⟩
  refine ⟨gap, hgap1, hgapub, hkzN1, hgridN1, ?_, ?_⟩
  · exact bootstrap_floor_from_base hkzN1 hfloor
  · exact hsub P g E Ψ K S hP hstat hunit hdag (sK + 1 + gap) mAl hgridN1

end

end HCPolySupport.HighContrast.Quenched
