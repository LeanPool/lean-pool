/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.CoupledMixingScaleEngineAdapter
public import LeanPool.HighContrastHomogenization.Provider.Quenched.PhysicalScaleBlockRow
public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeGaussianGauge

/-!
# High-contrast homogenization: Provider.Quenched.CoupledWitnessAssembly

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Assembly of the coupled mixing-scale witness

The finite-range engine fixes its stretched-exponential tail constant before
the exponent and before the coefficient law.  This file records the remaining
outer composition: a normalized reference-family package supplies the decay,
row-series and polynomial-cost data for each law, while the unit-range
renormalization theorem constructs the coupled witness.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The lawwise data left after selecting the exponent and the uniform
polynomial cost.  It contains no coupled witness: that witness is constructed
by the finite-range renormalization engine. -/
structure CoupledWitnessEngineData
    (P : Measure (CoeffSpace d)) (gamma : ℝ) (E : BlockMat d)
    (Psi : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ) (Abar : BlockMat d)
    (Nann : ℕ) (theta deltaOut Cmix : ℝ) where
  mu : ℝ
  nstar : ℕ
  qfb : ℕ
  b : ℕ
  N0 : ℕ
  radius : ℕ → CoeffSpace d → ℝ
  F : ℕ → CoeffSpace d → ℝ
  Cblk : ℝ
  Bconst : ℝ
  C1 : ℝ
  C2 : ℝ
  C3 : ℝ
  Cstop : ℝ
  Cround : ℝ
  mu_eq : mu = (d : ℝ) / 2 - gamma
  mu_pos : 0 < mu
  radius_tail : ∀ n q : ℕ, nstar ≤ n →
    P.real {a : CoeffSpace d | (3 : ℝ) ^ (n + q + b) < radius n a} ≤
      Real.exp (-(frGaugeConst d * (3 : ℝ) ^ (2 * mu * (q : ℝ))))
  Cblk_pos : 0 < Cblk
  F_measurable : ∀ n, Measurable (F n)
  row_decay : ∀ᵐ a ∂P, ∀ (m : ℕ), nstar ≤ m →
    quenched_block_row ((1 + 3 * gamma) / 4) Abar
        (max 1 (S a / (3 : ℝ) ^ Nann)) (physical_scale_coeff Nann a) m ≤
      Cblk * deltaOut *
        (3 : ℝ) ^ (-theta *
          ((m : ℝ) -
            (stoppingGeneration nstar qfb radius m a : ℝ) -
            (nstar : ℝ)))
  row_nonnegative : ∀ m a,
    0 ≤ quenched_block_row ((1 + 3 * gamma) / 4) Abar
      (max 1 (S a / (3 : ℝ) ^ Nann)) (physical_scale_coeff Nann a) m
  row_hasSum : ∀ᵐ a ∂P, ∀ k : ℕ,
    HasSum (fun j : ℕ =>
      (3 : ℝ) ^ (theta / 2 * (j : ℝ)) *
        quenched_block_row ((1 + 3 * gamma) / 4) Abar
          (max 1 (S a / (3 : ℝ) ^ Nann))
          (physical_scale_coeff Nann a) (k + j)) (F k a)
  nstar_le_N0 : nstar ≤ N0
  one_le_Bconst : 1 ≤ Bconst
  threshold_low :
    (qfb : ℝ) + (b : ℝ) + 1 + rowSplitOffset theta Cblk ≤
      (N0 : ℝ) - (nstar : ℝ)
  threshold_gain :
    Real.log 2 ≤
      frGaugeConst d * (3 : ℝ) ^ (2 * mu * ((N0 : ℝ) - (nstar : ℝ) -
        badTailOffset theta Cblk qfb b)) * ((3 : ℝ) ^ (mu / 2) - 1)
  threshold_absolute :
    2 * Real.log 4 ≤
      frGaugeConst d * (3 : ℝ) ^ (2 * mu * ((N0 : ℝ) - (nstar : ℝ) -
        badTailOffset theta Cblk qfb b))
  normalizer_relation :
    (3 : ℝ) ^ (2 * mu *
        ((nstar : ℝ) + badTailOffset theta Cblk qfb b - (N0 : ℝ))) ≤
      frGaugeConst d / 2 * Bconst ^ (2 * mu)
  one_le_base : 1 ≤ 2 + aspectRatio E * K
  three_le_base_pow :
    (3 : ℝ) ≤ (2 + aspectRatio E * K) ^ C3
  generation_cost :
    (3 : ℝ) ^ N0 ≤ (2 + aspectRatio E * K) ^ C1
  normalizer_cost :
    Bconst ≤ (2 + aspectRatio E * K) ^ C2
  raw_cost : C1 + C2 + C3 ≤ Cstop
  rounding_cost :
    (3 : ℝ) ≤ (2 + aspectRatio E * K) ^ Cround
  final_cost : Cround + Cstop ≤ Cmix

/-- Assemble the coupled witness in the quantifier order used by the random
homogenization root.  In particular, the dimensional tail constant is selected
before the exponent, and the four witness constants are selected before the
law and all of its coefficient data. -/
theorem exists_coupledWitnessAssembly (d : ℕ) (_hd : 2 ≤ d)
    (hdata :
      ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
        ∀ alpha : ℝ, 0 < alpha →
        ∃ Cmix theta deltaOut : ℝ,
          0 < Cmix ∧ 0 < theta ∧ deltaOut ∈ Set.Ioo (0 : ℝ) 1 ∧
          ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d)
            (Psi : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
            (Abar : BlockMat d) (Nann : ℕ),
            IsProbabilityMeasure P →
            HCPoly.Frozen.IsStationaryLaw P →
            HCPoly.Frozen.IsUnitRangeLaw P →
            HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S →
            IsSymmetricBlockMat Abar →
            Book.Ch02.BlockPosDef Abar →
            (∀ j : ℕ,
              annealedContrast P ((Nann + j : ℕ) : ℤ) - 1 ≤
                (3 : ℝ) ^ (-alpha * (j : ℝ))) →
            (∀ j : ℕ,
              BlockMatLoewnerLE Abar
                  (annealedBlock P
                    (centeredCube d ((Nann + j : ℕ) : ℤ))) ∧
                BlockMatLoewnerLE
                  (annealedBlock P
                    (centeredCube d ((Nann + j : ℕ) : ℤ)))
                  (blockScale
                    (1 + 6 * (3 : ℝ) ^ (-alpha * (j : ℝ))) Abar)) →
            Nonempty (CoupledWitnessEngineData P g E Psi K S Abar Nann
              theta deltaOut Cmix)) :
    ∃ cd : ℝ, 0 < cd ∧
      ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
        ∀ alpha : ℝ, 0 < alpha →
        ∃ Cmix cMix kappa delta : ℝ,
          0 < Cmix ∧ 0 < cMix ∧ 0 < kappa ∧
          delta ∈ Set.Ioo (0 : ℝ) 1 ∧
          ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d)
            (Psi : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
            (Abar : BlockMat d) (Nann : ℕ),
            IsProbabilityMeasure P →
            HCPoly.Frozen.IsStationaryLaw P →
            HCPoly.Frozen.IsUnitRangeLaw P →
            HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S →
            IsSymmetricBlockMat Abar →
            Book.Ch02.BlockPosDef Abar →
            (∀ j : ℕ,
              annealedContrast P ((Nann + j : ℕ) : ℤ) - 1 ≤
                (3 : ℝ) ^ (-alpha * (j : ℝ))) →
            (∀ j : ℕ,
              BlockMatLoewnerLE Abar
                  (annealedBlock P
                    (centeredCube d ((Nann + j : ℕ) : ℤ))) ∧
                BlockMatLoewnerLE
                  (annealedBlock P
                    (centeredCube d ((Nann + j : ℕ) : ℤ)))
                  (blockScale
                    (1 + 6 * (3 : ℝ) ^ (-alpha * (j : ℝ))) Abar)) →
            ∃ W : CoupledMixingScaleWitness P
              (fun m a => quenched_block_row ((1 + 3 * g) / 4) Abar
                (max 1 (S a / (3 : ℝ) ^ Nann))
                (physical_scale_coeff Nann a) m)
              cMix cd ((d : ℝ) - 2 * g) kappa delta,
              W.normalization ≤ (2 + aspectRatio E * K) ^ Cmix := by
  refine ⟨1, by norm_num, ?_⟩
  intro g hg alpha halpha
  obtain ⟨Cmix, theta, deltaOut, hCmix, htheta, hdeltaOut, hdata⟩ :=
    hdata g hg alpha halpha
  refine ⟨Cmix, 2, theta / 2, deltaOut, hCmix, by norm_num, ?_, hdeltaOut, ?_⟩
  · positivity
  intro P E Psi K S Abar Nann hP hstat hunit hdag hAbar hAbarPos
    hcontrast hsandwich
  let : IsProbabilityMeasure P := hP
  obtain ⟨D⟩ := hdata P E Psi K S Abar Nann hP hstat hunit hdag hAbar
    hAbarPos hcontrast hsandwich
  have heta : (d : ℝ) - 2 * g = 2 * D.mu := by
    rw [D.mu_eq]
    ring
  exact exists_coupledMixingScaleWitness_of_polynomial_engine htheta D.mu_pos heta
    (frGaugeConst_pos d) hdeltaOut.1 D.Cblk_pos D.F_measurable D.radius_tail
    D.row_decay D.row_nonnegative
    D.row_hasSum D.nstar_le_N0 D.one_le_Bconst D.threshold_low D.threshold_gain
    D.threshold_absolute D.normalizer_relation D.one_le_base D.three_le_base_pow
    D.generation_cost D.normalizer_cost D.raw_cost D.rounding_cost D.final_cost

end

end Quenched
end HighContrast
end HCPolySupport
