/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.DeGiorgiCutoffTest
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.ScalarWeakSolution
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalL2

/-!
# CutoffTest

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Smooth localizations of an `H¹` function as zero-trace tests

The weighted energy estimates of this directory test the divergence-form
equation with `phi * u`, where `u` is the solution itself and `phi` is a
smooth compactly supported multiplier whose topological support lies in the
domain.  This file records that product as an honest `H10Function` together
with its value and its product-rule weak gradient.

There are two ways for a multiplier to be admissible.  Either its topological
support lies in the domain, in which case the product is a zero-trace function
for every `H¹` factor; or the factor itself already has zero trace, in which
case no support condition on the multiplier is needed.  Both are recorded as
`IsAdmissibleMultiplier`, which is what the weighted estimates consume.  The
first uses the localized product of the cutoff-test module,
`DivergenceFormProcess.Form.localizedProductToH10`.

## Main definitions

- `DivergenceFormProcess.Decay.IsAdmissibleMultiplier`.

## Main results

- `DivergenceFormProcess.Decay.isAdmissibleMultiplier_of_tsupport_subset`
- `DivergenceFormProcess.Decay.isAdmissibleMultiplier_of_zeroTrace`
-/

noncomputable section

namespace DivergenceFormProcess.Decay

open HCPolySupport MeasureTheory
open DivergenceFormProcess.Form

variable {d : ℕ} {U : Set (Vec d)}

/-- A multiplier is admissible for `u` when the product `phi * u` is realized
by a zero-trace function whose weak gradient obeys the product rule.  This is
the only property of the test function the weighted estimates use. -/
def IsAdmissibleMultiplier (U : Set (Vec d)) (u : H1Function U)
    (phi : Vec d → ℝ) : Prop :=
  ∃ w : H10Function U,
    w.toH1Function.toFun = (fun x => phi x * u.toFun x) ∧
    (∀ᵐ x ∂volumeMeasureOn U, w.toH1Function.grad x =
      fun i => phi x * u.grad x i +
        u.toFun x * (fderiv ℝ phi x) (basisVec i))

/-- A smooth compactly supported multiplier supported in the domain is
admissible for every `H¹` function. -/
theorem isAdmissibleMultiplier_of_tsupport_subset
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U)
    {phi : Vec d → ℝ} (hphi : ContDiff ℝ (⊤ : ℕ∞) phi)
    (hphiCompact : HasCompactSupport phi) (hphiU : tsupport phi ⊆ U) :
    IsAdmissibleMultiplier U u phi := by
  refine ⟨localizedProductToH10 hU u hphi hphiCompact hphiU,
    localizedProductToH10_toFun hU u hphi hphiCompact hphiU, ?_⟩
  filter_upwards [localizedProductToH10_grad_ae hU u hphi hphiCompact hphiU]
    with x hx
  rw [hx, H1Function.mulContDiffHasCompactSupport_grad]

/-- For a factor with zero trace, every smooth compactly supported multiplier
is admissible: no support condition inside the domain is needed. -/
theorem isAdmissibleMultiplier_of_zeroTrace (z : H10Function U)
    {phi : Vec d → ℝ} (hphi : ContDiff ℝ (⊤ : ℕ∞) phi)
    (hphiCompact : HasCompactSupport phi) :
    IsAdmissibleMultiplier U z.toH1Function phi := by
  refine ⟨z.mulContDiffHasCompactSupport hphi hphiCompact, ?_, ?_⟩
  · exact H10Function.mulContDiffHasCompactSupport_toFun z hphi hphiCompact
  · refine Filter.Eventually.of_forall fun x => ?_
    change (z.toH1Function.mulContDiffHasCompactSupport hphi hphiCompact).grad x = _
    rw [H1Function.mulContDiffHasCompactSupport_grad]

end DivergenceFormProcess.Decay
