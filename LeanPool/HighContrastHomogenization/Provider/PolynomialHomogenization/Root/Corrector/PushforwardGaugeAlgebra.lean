/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.PushforwardFamilyCore

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.PushforwardGaugeAlgebra

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Gauge algebra for the pushforward

Three elaboration hazards are avoided here deliberately; each of them costs a
runaway when it is not.

* Every rewrite runs with the value and gradient fields as **bare function
  variables**.  `rw [matVecMul_add]` has to decide, for each subterm
  `matVecMul L⁻¹ (Ψ …)`, whether `Ψ …` is an addition; when `Ψ` is
  `NormalizedLocalH1Carrier.globalGradientRepresentative G` that decision
  delta-unfolds the carrier and, through it, the spectral selector inside
  `gaugeRoot`.  With `Ψ` a local function variable it fails on the head symbol
  at once.
* Almost-everywhere statements are moved with `EventuallyEq.comp_tendsto` and
  `EventuallyEq.fun_comp`, never by `filter_upwards` on a goal whose sides are
  partially applied `pushforwardGradient`, and never by ascribing a type to the raw
  `QuasiMeasurePreserving.tendsto_ae` application.
* The algebra lemmas are applied with every argument explicit, so no
  higher-order unification is attempted.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-- Pushing a translation through an invertible linear change of variables. -/
private theorem matVecMul_translate_algebra (A : Mat d) (F : Vec d → Vec d)
    (x w : Vec d) :
    matVecMul A (F (matVecMul A x + matVecMul A w)) =
      matVecMul A (F (matVecMul A (x + w))) := by
  rw [matVecMul_add A x w]

/-- Pushing a linear combination through an invertible linear change of
variables. -/
private theorem matVecMul_linear_algebra (A : Mat d) (G1 G2 : Vec d → Vec d)
    (c : ℝ) (y : Vec d) :
    matVecMul A (c • G1 y + G2 y) =
      c • matVecMul A (G1 y) + matVecMul A (G2 y) := by
  rw [matVecMul_add A (c • G1 y) (G2 y), matVecMul_smul A c (G1 y)]

/-- The pushforward of a carrier whose gradient representative is a translate is
the translate of the pushforward, with the translation vector pushed forward. -/
theorem pushforwardGradient_translate_ae [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) {G H : NormalizedLocalH1Carrier d} (w : Vec d)
    (h : (fun y ↦ G.globalGradientRepresentative
        (y + matVecMul (gaugeRoot abar)⁻¹ w)) =ᵐ[volume]
      H.globalGradientRepresentative) :
    pushforwardGradient abar H =ᵐ[volume] fun x ↦ pushforwardGradient abar G (x + w) := by
  have hpush := (h.symm.comp_tendsto
    (quasiMeasurePreserving_matVecMul_gaugeRootInv hS).tendsto_ae).fun_comp
      (matVecMul (gaugeRoot abar)⁻¹)
  refine hpush.trans (Filter.Eventually.of_forall fun x ↦ ?_)
  exact matVecMul_translate_algebra (gaugeRoot abar)⁻¹
    G.globalGradientRepresentative x w

/-- The pushforward is linear in the carrier, almost everywhere. -/
theorem pushforwardGradient_linear_ae [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) (c : ℝ)
    {G G1 G2 : NormalizedLocalH1Carrier d}
    (h : G.globalGradientRepresentative =ᵐ[volume] fun y ↦
      c • G1.globalGradientRepresentative y +
        G2.globalGradientRepresentative y) :
    pushforwardGradient abar G =ᵐ[volume] fun x ↦
      c • pushforwardGradient abar G1 x + pushforwardGradient abar G2 x := by
  have hpush := (h.comp_tendsto
    (quasiMeasurePreserving_matVecMul_gaugeRootInv hS).tendsto_ae).fun_comp
      (matVecMul (gaugeRoot abar)⁻¹)
  refine hpush.trans (Filter.Eventually.of_forall fun x ↦ ?_)
  exact matVecMul_linear_algebra (gaugeRoot abar)⁻¹
    G1.globalGradientRepresentative G2.globalGradientRepresentative c
    (matVecMul (gaugeRoot abar)⁻¹ x)

end

end Root
end HighContrast
end HCPolySupport
