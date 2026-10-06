/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.ReconciledSmallnessCertificate
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1ExactGaugeFrameConditional

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.ExactRootGaugeTerminalDefinition

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The large-scale C¹ slope approximation clause, conditional on the exact-gauge terminal

The large-scale C¹ slope approximation clause has **no unconditional provider**;
its exact missing provider is an exact-gauge ball terminal whose delay `L` and constant `A` are
chosen before `kappa`, `abar`, `Phi`, `gradPhi`, `a`, `x`, `R` and the
solution.  This module composes that terminal with the physical return
`Root.exists_rangeCompletePhysicalC1_of_exactRootGaugeTerminal` and the root
corrector-family hypothesis, and obtains the frozen the large-scale C¹ slope approximation clause
body at the reconciled-smallness certificate.

The terminal itself is *not* proved here.  What the corrector-cone lift does
buy is that the two reasons for the terminal being unreachable
are gone:

* the order gap (`printCertificateOrder g ≥ 1/4` against the C¹
  theorem's `s < 1/12`) — removed, see
  `Root.exists_printOrderInfiniteCorrectorC1Constants`;
* the sample-dependent restart — removed, see
  `Root.exists_printOrderUndelayedExactGaugeRow`, which delivers the
  simultaneous-slope row on *cubes* at start `triadicCeilingIndex x` with
  constants fixed by `(d, g, ϑ)` alone.

What is left between that cube row and this terminal is the **cube-to-ball
packaging** at continuous radii, together with the identification of the
identity-gauge family with the normalized-root coefficient `bRef`.  That is
the exact rendered residue.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- **The exact-gauge ball terminal**: the
delay `L` and the constant `A` are chosen before the rate, the matrix, the
family, the sample, the scale, the radius and the solution. -/
@[expose]
def ExactRootGaugeTerminal (d : ℕ) [NeZero d]
    (GoodScale : Mat d → CoeffSpace d → ℝ → Prop)
    (CorrectorFamily : Mat d →
      (Vec d → CoeffSpace d → Vec d → ℝ) →
      (Vec d → CoeffSpace d → Vec d → Vec d) → Prop)
    (eta : ℝ) : Prop :=
  ∃ (L : ℕ) (A : ℝ), 0 < A ∧
    ∀ (abar : Mat d) (hS : (symmPart abar).PosDef)
      (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
      (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
      CorrectorFamily abar Phi gradPhi →
      ∀ (a : CoeffSpace d) (x : ℝ), 1 ≤ x → GoodScale abar a x →
        ∃ PhiRef : Vec d → NormalizedLocalH1Carrier d,
          (∀ e : Vec d,
            (fun y ↦ matVecMul (Selection.normalizedRoot (symmPart abar))
              (e + gradPhi e a
                (matVecMul (Selection.normalizedRoot (symmPart abar)) y))) =ᵐ[volume]
              fun y ↦ matVecMul (Selection.normalizedRoot (symmPart abar)) e +
                (PhiRef (matVecMul (Selection.normalizedRoot (symmPart abar))
                  e)).globalGradientRepresentative y) ∧
          ∀ (R : ℝ) (u : Vec d → ℝ) (Du : Vec d → Vec d),
            MemH1a (fun y ↦ a.1 y) (ellipsoid abar R) u Du →
            IsWeakSolutionOn (fun y ↦ a.1 y) (ellipsoid abar R) Du →
            (let q := Selection.normalizedRoot (symmPart abar)
              let hq : IsUnit q.det :=
                (Matrix.isUnit_iff_isUnit_det _).mp
                  (normalizedRoot_posDef_of_posDef hS).isUnit
              let bRef := affineCoefficient q hq
                (⇑(normalizedCenteredCoeff a abar hS).1)
              let rStart := (3 : ℝ) ^ (Quenched.triadicCeilingIndex x + L)
              rStart ≤ R →
                ∃ eRef : Vec d, ∀ r : ℝ, r ∈ Icc rStart R →
                  weightedGradNorm bRef {y | vecNormSq y ≤ r ^ 2}
                      (fun y ↦ matVecMul q (Du (matVecMul q y)) -
                        (eRef +
                          (PhiRef eRef).globalGradientRepresentative y)) ≤
                    ENNReal.ofReal
                        (A * (r / R) ^ max eta (1 / 2 : ℝ)) *
                      weightedGradNorm bRef {y | vecNormSq y ≤ R ^ 2}
                        (fun y ↦ matVecMul q (Du (matVecMul q y))))

end

end CorrectorComposition
end HighContrast
end HCPolySupport
