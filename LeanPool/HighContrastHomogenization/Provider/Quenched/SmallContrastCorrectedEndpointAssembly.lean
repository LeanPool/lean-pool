/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCorrectedEndpointCore

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastCorrectedEndpointAssembly

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

open HCPolySupport.HighContrast
  HCPolySupport MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

theorem endpoint_hcore_body_corrected (d : ℕ) (hd : 2 ≤ d) :
    ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
      ∃ cSc : ℝ, 0 < cSc ∧
        ∃ alpha Cdelay : ℝ, 0 < alpha ∧ 0 ≤ Cdelay ∧
          ∀ (cStar gBase : ℝ) (Pbase : Measure (CoeffSpace d))
            (Ebase : BlockMat d) (Ψbase : ℝ → ℝ) (Kbase : ℝ)
            (Sbase : CoeffSpace d → ℝ),
            cStar ∈ Set.Ioc 0 cSc →
            gBase = (1 + g) / 2 →
            MeasureTheory.IsProbabilityMeasure Pbase →
            HCPoly.Frozen.IsStationaryLaw Pbase →
            HCPoly.Frozen.IsUnitRangeLaw Pbase →
            HCPoly.Frozen.CoarseEllipticityDagger Pbase gBase Ebase Ψbase
              Kbase Sbase →
            annealedContrast Pbase 0 - 1 ≤ cStar →
            blockContrast Ebase ≤ 1 + cSc →
            ∃ m0 : ℕ,
              (3 : ℝ) ^ m0 ≤ (2 + aspectRatio Ebase * Kbase) ^ Cdelay ∧
              ∀ j : ℕ,
                annealedContrast Pbase ((m0 + j : ℕ) : ℤ) - 1 ≤
                  (3 : ℝ) ^ (-alpha * (j : ℝ)) := by
  exact endpoint_hcore_body_corrected_core d hd
