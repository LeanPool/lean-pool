/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.GaugeFrameTerminalAtCertificate
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.EventRetainingCertificate

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.CorrectorDecayAtCertificate

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# the corrector-and-flux decay clause at the event-retaining certificate, unconditional

The corrector-and-flux decay clause was carried with one hypothesis: the corrector family's
canonical
corrector-family hypothesis **at the printed certificate**
`PrintOrderRateBearingCommonAffineGoodScale d g (canonicalCorrectorSmallness
d g hg) κc`.  That is not a smallness or an order question — it is a *certificate
mismatch*.  The printed certificate is a per-sample predicate carrying no
translation-invariant block row, so the event-retaining certificate, which supplies the stationary
corrector family clause event from
the event-retaining root certificate, cannot discharge it: the event-retaining certificate's
samples are
a strictly smaller set than the printed certificate's.

the reconciled-smallness certificate removes the mismatch at its source.  The terminal
The gauge-frame corrector-decay constant uses its family premise in
**exactly one place**, `hfamily.normalizedJoint a x hGood`, at the very sample it
is applied to; so the corrector-family hypothesis may be read at *any* certificate that projects to
the printed one.  `CorrectorComposition.exists_gaugeFrameCorrectorDecayConstant_atCertificate`
is that generalisation, with the proof otherwise unchanged, and the printed
form is its special case.

With it, the corrector-and-flux decay clause reads its corrector-family hypothesis at the **same**
event-retaining certificate the stationary corrector family clause and the Liouville
characterization clause use,
and `rootPushCanonicalFamily_of_rootGoodScaleOn` discharges it outright.  **the corrector-and-flux
decay clause is
unconditional on the whole of `g ∈ Ico 0 1`.**
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-- The event-retaining certificate projects to the printed certificate at the canonical
canonical smallness, with no `1 ≤ x` needed. -/
theorem printOrderGoodScale_of_reconciledRootGoodScaleOn (d : ℕ) [NeZero d]
    (cStar : ℝ → ℝ) {g : ℝ} (hg : g ∈ Ico (0 : ℝ) 1)
    (hceil : cStar g ∈ Ioo (0 : ℝ) 1 ∧
      cStar g ≤ canonicalCorrectorSmallness d g hg)
    {κc : ℝ} (hκc : 0 < κc) (abar : Mat d) (a : CoeffSpace d) (x : ℝ)
    (h : reconciledRootGoodScaleOn d cStar g κc abar a x) :
    PrintOrderRateBearingCommonAffineGoodScale d g
      (canonicalCorrectorSmallness d g hg) κc abar a x :=
  printOrderGoodScale_of_rootGoodScaleAt_mono
    (reconciledRootGoodScale_of_reconciledRootGoodScaleOn cStar h) hκc hceil.1.1 hceil.2

/-- **the corrector-and-flux decay clause at the event-retaining certificate, with no hypothesis
beyond the
smallness reconciliation.**  The corrector-family hypothesis is discharged by
`rootPushCanonicalFamily_of_rootGoodScaleOn`, which the event-retaining certificate
supplies for every `g ∈ Ico 0 1`. -/
theorem exists_correctorDecay_of_reconciledRootGoodScaleOn (d : ℕ) [NeZero d] (cStar : ℝ → ℝ)
    (hceil : ∀ (g : ℝ) (hg : g ∈ Ico (0 : ℝ) 1),
      cStar g ∈ Ioo (0 : ℝ) 1 ∧
      cStar g ≤ canonicalCorrectorSmallness d g hg) :
    ∀ g : ℝ, g ∈ Ico (0 : ℝ) 1 →
      ∀ κc : ℝ, 0 < κc →
        ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
          ∀ (abar : Mat d) (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
            (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
            Root.RootPushCorrectorFamilyPredicate d abar Phi gradPhi →
            ∀ (a : CoeffSpace d) (x : ℝ), 1 ≤ x →
              reconciledRootGoodScaleOn d cStar g κc abar a x →
              ∀ (e : Vec d) (r : ℝ), x ≤ r →
                ENNReal.ofReal r⁻¹ *
                    negOneNorm (ellipsoid abar r)
                      (fun y ↦ matVecMul (matSqrt (symmPart abar))
                        (gradPhi e a y)) +
                  ENNReal.ofReal r⁻¹ *
                    negOneNorm (ellipsoid abar r)
                      (fun y ↦ matVecMul (matSqrt (symmPart abar))⁻¹
                        (matVecMul ((a.1 y : Mat d) - skewPart abar)
                            (e + gradPhi e a y) -
                          matVecMul (symmPart abar) e)) ≤
                  ENNReal.ofReal
                    (C * Real.sqrt (vecDot e (matVecMul (symmPart abar) e)) *
                      (r / x) ^ (-κ)) := by
  intro g hg κc hκc
  obtain ⟨C, hC, hmain⟩ :=
    exists_gaugeFrameCorrectorDecayConstant_atCertificate d g hg
  dsimp only at hmain
  refine ⟨C, κc, hC, hκc, ?_⟩
  intro abar Phi gradPhi hmarker a x hx hgood e r hxr
  exact hmain (reconciledRootGoodScaleOn d cStar g κc) κc abar Phi gradPhi
    (fun a' x' h' ↦ printOrderGoodScale_of_reconciledRootGoodScaleOn d cStar hg
      (hceil g hg) hκc abar a' x' h')
    (Root.canonicalPullbackFamily_of_pushforwardMarker
      (rootPushCanonicalFamily_of_rootGoodScaleOn d hg) abar Phi gradPhi hmarker)
    a x hx hgood e r hxr

end

end CorrectorComposition
end HighContrast
end HCPolySupport
