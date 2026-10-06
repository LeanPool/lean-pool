/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1ExactGaugeFrameTransport

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1ExactGaugeFrameConditional

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Conditional exact-frame C1 composition

This module isolates the terminal estimate that remains subject to the gauge
frame decision.  Once that estimate is supplied for the exact normalized
coefficient and canonical joint corrector, affine transport and finite-prefix
absorption give the full physical-radius conclusion.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The exact gauge-frame terminal, affine return, and deterministic prefix
compose to the physical C1 estimate on every radius above the root scale. -/
theorem exists_rangeCompletePhysicalC1_of_exactRootGaugeTerminal
    (L : ℕ) (eta A : ℝ) (heta : 0 ≤ eta) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (abar : Mat d) (hS : (symmPart abar).PosDef),
        ∀ (a : CoeffSpace d) (x : ℝ), 1 ≤ x →
          ∀ (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
            (∀ (c : ℝ) (e e' : Vec d),
              gradPhi (c • e + e') a =ᵐ[volume]
                fun y ↦ c • gradPhi e a y + gradPhi e' a y) →
            ∀ (PhiRef : Vec d → NormalizedLocalH1Carrier d),
              (∀ e : Vec d,
                (fun y ↦ matVecMul (Selection.normalizedRoot (symmPart abar))
                  (e + gradPhi e a
                    (matVecMul (Selection.normalizedRoot (symmPart abar)) y))) =ᵐ[volume]
                  fun y ↦ matVecMul (Selection.normalizedRoot (symmPart abar)) e +
                    (PhiRef (matVecMul
                      (Selection.normalizedRoot (symmPart abar))
                        e)).globalGradientRepresentative y) →
              ∀ R : ℝ, x ≤ R →
                ∀ (u : Vec d → ℝ) (Du : Vec d → Vec d),
                  MemH1a (fun y ↦ a.1 y) (ellipsoid abar R) u Du →
                  IsWeakSolutionOn (fun y ↦ a.1 y) (ellipsoid abar R) Du →
                  (let q := Selection.normalizedRoot (symmPart abar)
                    let hq : IsUnit q.det :=
                      (Matrix.isUnit_iff_isUnit_det _).mp
                        (normalizedRoot_posDef_of_posDef hS).isUnit
                    let bRef := affineCoefficient q hq
                      (⇑(normalizedCenteredCoeff a abar hS).1)
                    let rStart := (3 : ℝ) ^
                      (Quenched.triadicCeilingIndex x + L)
                    rStart ≤ R →
                      ∃ eRef : Vec d, ∀ r : ℝ, r ∈ Icc rStart R →
                        weightedGradNorm bRef {y | vecNormSq y ≤ r ^ 2}
                            (fun y ↦ matVecMul q (Du (matVecMul q y)) -
                              (eRef +
                                (PhiRef eRef).globalGradientRepresentative y)) ≤
                          ENNReal.ofReal
                              (A * (r / R) ^ max eta (1 / 2 : ℝ)) *
                            weightedGradNorm bRef
                              {y | vecNormSq y ≤ R ^ 2}
                              (fun y ↦ matVecMul q
                                (Du (matVecMul q y)))) →
                    ∃ e : Vec d, ∀ r : ℝ, r ∈ Icc x R →
                      weightedGradNorm (fun y ↦ a.1 y)
                          (ellipsoid abar r)
                          (fun y ↦ Du y - (e + gradPhi e a y)) ≤
                        ENNReal.ofReal (K * (r / R) ^ eta) *
                          weightedGradNorm (fun y ↦ a.1 y)
                            (ellipsoid abar R) Du := by
  obtain ⟨K, hK, hprefix⟩ :=
    exists_rangeCompletePhysicalC1_of_boundedStart (d := d)
      L eta A heta hA
  refine ⟨K, hK, ?_⟩
  intro abar hS a x hx gradPhi hlinear PhiRef hpullback
    R hxR u Du hu hweak hGauge
  exact hprefix abar hS a x hx gradPhi hlinear R hxR u Du hu hweak (by
    dsimp only
    intro hStartR
    obtain ⟨e, he⟩ := delayedPhysicalC1_of_exactRootGaugeFrame (d := d)
      hS a gradPhi PhiRef hpullback L (max eta (1 / 2 : ℝ)) A x R Du
      hStartR (by
        dsimp only at hGauge
        exact hGauge hStartR)
    refine ⟨e, ?_⟩
    intro r hr
    exact c1DecayBound_weaken_exponent A eta (max eta (1 / 2 : ℝ))
      r R hA.le ((by positivity :
        0 < (3 : ℝ) ^ (Quenched.triadicCeilingIndex x + L)).trans_le hr.1)
      (zero_lt_one.trans_le (hx.trans hxR)) hr.2 (le_max_left _ _) (he r hr))

end


end Root
end HighContrast
end HCPolySupport
