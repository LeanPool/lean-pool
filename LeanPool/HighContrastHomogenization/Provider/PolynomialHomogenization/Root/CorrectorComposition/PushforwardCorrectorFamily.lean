/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.PushforwardFamilyClauses
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1EquivariantPullbackEliminator

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.PushforwardCorrectorFamily

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The pushforward marker, and what the corrector-side holes read off it

The corrector-side holes read their family corrector-family hypothesis off the pushforward marker
`RootPushCorrectorFamilyPredicate` (= `RootPushCorrectorFamily`).  This module
supplies that corrector-family hypothesis, together with the pullback identities and the reference
data it rests on:

* the marker bridge itself is one `rintro` (`canonicalPullbackFamily_of_pushforwardMarker`);
* the two *pullback* clauses of `CanonicalPullbackCorrectorFamily.normalizedJoint`
  become **definitional** under the pushforward — `pushforwardValue_pullback_identity`
  and `pushforwardGradient_pullback_identity` below — with the reference carrier being
  the root joint carrier itself and the additive constant `0`;
* the reference family, its local-Cauchy witness, its tolerance window, its
  good tail and its joint local equation all come straight out of
  `RootCorrectorData`, i.e. out of `RootNormalizedSupply`;
* **exactly one clause is left**: the selected reference family's *pointwise*
  normalized-root coefficient identity (the datum carries only an a.e. identity
  against `Book.Ch03.publicCoeffField` on origin cubes), together with a
  natural-number delay placing the datum's start below
  `Quenched.triadicCeilingIndex x + L`.

The order arithmetic also records why the order re-base is a hard prerequisite:
`rootCorrectorOrder = 3 / 16`, and `¬ (3 / 16 < 1 / 12)`, so before the
`1/12 → 1/2` re-base of `CanonicalPullbackCorrectorFamily.normalizedJoint` the
pushforward datum could not satisfy that field at all.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-! ## The pullback identities are definitional -/

private theorem pushforward_pullback_aux [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) (e v : Vec d) :
    matVecMul (gaugeRoot abar) (e + matVecMul (gaugeRoot abar)⁻¹ v) =
      matVecMul (gaugeRoot abar) e + v := by
  rw [matVecMul_add, gaugeRoot_apply_inv hS]

/-- The pushforward value read in the gauge frame is the carrier's own global
value representative — the `normalizedJoint` value clause, with `c₀ = 0`. -/
theorem pushforwardValue_pullback_identity [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) (G : NormalizedLocalH1Carrier d) (y : Vec d) :
    pushforwardValue abar G (matVecMul (gaugeRoot abar) y) =
      G.globalValueRepresentative y := by
  simp only [pushforwardValue, gaugeRoot_inv_apply hS]

/-- The pushforward slope read in the gauge frame is the carrier's own global
gradient representative — the `normalizedJoint` gradient clause. -/
theorem pushforwardGradient_pullback_identity [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) (G : NormalizedLocalH1Carrier d) (e y : Vec d) :
    matVecMul (gaugeRoot abar)
        (e + pushforwardGradient abar G (matVecMul (gaugeRoot abar) y)) =
      matVecMul (gaugeRoot abar) e + G.globalGradientRepresentative y := by
  have h1 : pushforwardGradient abar G (matVecMul (gaugeRoot abar) y) =
      matVecMul (gaugeRoot abar)⁻¹ (G.globalGradientRepresentative y) := by
    simp only [pushforwardGradient, gaugeRoot_inv_apply hS]
  rw [h1]
  exact pushforward_pullback_aux hS e _

/-! ## The order interface -/

/-! ## The marker re-point -/

/-- The canonical predicate at the pushforward pair, for every homogenized
matrix — the pushforward analogue of the canonical corrector-family
predicate. -/
@[expose]
def RootPushCanonicalFamily (d : ℕ) [NeZero d]
    (GoodScale : Mat d → CoeffSpace d → ℝ → Prop) : Prop :=
  ∀ (abar : Mat d) (hS : (symmPart abar).PosDef),
    CanonicalPullbackCorrectorFamily GoodScale abar
      (pushforwardPhysicalPhi d abar hS) (pushforwardPhysicalGradPhi d abar hS)

/-- **The retained-corrector-family hypothesis row, re-pointed at the pushforward marker.**  This is
the hypothesis the generic-root the decay and Liouville clauses and the large-scale Lipschitz
estimate clause adapters consume; it is one
`rintro` off the marker's definitional shape. -/
theorem canonicalPullbackFamily_of_pushforwardMarker [NeZero d]
    {GoodScale : Mat d → CoeffSpace d → ℝ → Prop}
    (hcustody : RootPushCanonicalFamily d GoodScale) :
    ∀ (abar : Mat d) (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
      (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
      RootPushCorrectorFamilyPredicate d abar Phi gradPhi →
        CanonicalPullbackCorrectorFamily GoodScale abar Phi gradPhi := by
  rintro abar Phi gradPhi ⟨hS, rfl, rfl⟩
  exact hcustody abar hS

/-! ## What is left of the canonical predicate under the pushforward -/

end

end Root
end HighContrast
end HCPolySupport
