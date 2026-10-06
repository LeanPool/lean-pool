/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.CorrectorDecayAtCertificate
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.DirichletHoleInhabitant
public import LeanPool.HighContrastHomogenization.Provider.Quenched.AnnealedToQuenchedTransfer
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCorrectedEndpointAssembly
public import LeanPool.HighContrastHomogenization.Provider.Quenched.Prop211Rebase
public import LeanPool.HighContrastHomogenization.Provider.Quenched.CoupledWitnessAssembly
public import LeanPool.HighContrastHomogenization.Provider.Quenched.EndpointRelativeEngineData
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RootAssembly

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.DirichletHoleBridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The root, composed end to end

Every binder of the root is supplied here, against the assembly
`RootInterface.polynomial_homogenization_of_quenched_scale`.  The composition
`RootInterface.polynomial_homogenization_random_source_of_providers` is
reproduced by its own one-line proof: the coupled step, then the assembly.

The binders:

* the three **coupled** premises, from `endpoint_hcore_body_corrected`,
  `exists_prop211_rebase_provider` and
  `exists_coupledWitnessAssembly ∘ exists_coupledWitnessEngineData_of_endpoint`
  — all unconditional in `(d, 2 ≤ d)`;
* `hhomogenized`, from `exists_rootGoodScaleOn_of_quenchedEventRow`;
* **the negative-Sobolev Dirichlet error clause**, from the Dirichlet module's
  `RowSupply.dirichletHole_inhabited`, bridged from
  `RootInterface.RootGoodScale` to the event-retaining certificate by the
  projection below — **no new hypothesis**;
* **the stationary corrector family, decay, Liouville and Lipschitz clauses**,
  unconditional;
* **the large-scale C¹ slope approximation clause**, still conditional on
  `ExactRootGaugeTerminal`.

The conclusion is the frozen statement's type, taken from the statement region
of `HCPoly.Frozen.PolynomialHomogenization`, with the frozen signature line
`(d : ℕ) (hd : 2 ≤ d) :` replaced by this theorem's own binders.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set

noncomputable section

/-! ## the negative-Sobolev Dirichlet error clause, bridged to the event-retaining certificate -/

/-- The Dirichlet clause is **antitone** in the certificate: it consumes
`GoodScale` as a hypothesis, so a *stronger* certificate weakens the hole. -/
theorem dirichletHole_antitone {d : ℕ} [NeZero d]
    {G G' : ℝ → ℝ → Mat d → CoeffSpace d → ℝ → Prop}
    (hproj : ∀ (g κ : ℝ) (abar : Mat d) (a : CoeffSpace d) (x : ℝ),
      G' g κ abar a x → G g κ abar a x)
    (h : RowSupply.DirichletHole d G) :
    RowSupply.DirichletHole d G' := by
  obtain ⟨C₀, hC₀, hmain⟩ := h
  refine ⟨C₀, hC₀, ?_⟩
  intro g hg κ hκ hκle
  obtain ⟨Lg, pEcc, hLg, hpEcc, hbody⟩ := hmain g hg κ hκ hκle
  exact ⟨Lg, pEcc, hLg, hpEcc, fun abar a x hx hgood =>
    hbody abar a x hx (hproj g κ abar a x hgood)⟩

/-- **The exact certificate delta, and its bridge.**  The Dirichlet module states
its hole at `RootInterface.RootGoodScale d`, whose smallness is hidden behind
`∃ c ∈ Ioo 0 1`; this module's event-retaining certificate `rootGoodScaleOn` exposes the
smallness as a binder and additionally carries the producing block-row event.
The delta is therefore **two forgetful steps and nothing else**: forget the
event (`reconciledRootGoodScale_of_reconciledRootGoodScaleOn`), then hide the smallness
(`rootGoodScale_of_rootGoodScaleAt`).  No hypothesis is added. -/
theorem rootGoodScale_of_reconciledRootGoodScaleOn (d : ℕ) [NeZero d] (cStar : ℝ → ℝ)
    (g κ : ℝ) (abar : Mat d) (a : CoeffSpace d) (x : ℝ)
    (h : reconciledRootGoodScaleOn d cStar g κ abar a x) :
    RootInterface.RootGoodScale d g κ abar a x :=
  rootGoodScale_of_rootGoodScaleAt (reconciledRootGoodScale_of_reconciledRootGoodScaleOn cStar h)

/-- **the negative-Sobolev Dirichlet error clause at the event-retaining certificate,
unconditional.** -/
theorem dirichletHole_reconciledRootGoodScaleOn (d : ℕ) [NeZero d] (cStar : ℝ → ℝ) :
    RowSupply.DirichletHole d (reconciledRootGoodScaleOn d cStar) :=
  dirichletHole_antitone (rootGoodScale_of_reconciledRootGoodScaleOn d cStar)
    (RowSupply.dirichletHole_inhabited d)

end

end CorrectorComposition
end HighContrast
end HCPolySupport

/-! ## The root, at the frozen statement's own signature -/

open HCPolySupport HCPolySupport.HighContrast
open HCPolySupport.HighContrast.CorrectorComposition
