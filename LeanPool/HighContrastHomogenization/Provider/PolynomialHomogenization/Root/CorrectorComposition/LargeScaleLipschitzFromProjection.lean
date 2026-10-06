/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.CeilingInterface
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RootInterface.SmallnessMonotone
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.TargetedGaugeSpine
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.AffineRateAbsorption
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.GaugeRepresentativeJoin
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorRealRadiusGrowth
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.DecoupledRootPhysicalLipschitz
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.PhysicalLiouvilleDoubleInclusion

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.LargeScaleLipschitzFromProjection

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# the decay, Liouville and Lipschitz clauses restated to the root interface

Two mechanical changes are needed for the corrector-and-flux decay clause and the large-scale
Lipschitz estimate clause:

* **(i)** absorptions `g` to a leading binder — the adapters bind `g` *inside*
  their corrector-family premise, so eta-wrapping them would force the caller to supply
  the certificate projection for **every** internal `g'`, not just the outer
  one, which would strengthen the hypothesis;
* **(ii)** accept the *given* rate instead of choosing one — under the re-key
  the rate is the hole's leading `κc`, so the premise's `∃ kappa` becomes
  `∀ κc, 0 < κc →`.

the Liouville characterization clause's root key must also move off
`CanonicalPullbackCorrectorFamily
GoodScale` — after the re-key `GoodScale` is `(g, c, κ)`-dependent while the
root's `CorrectorFamily` binder precedes `g`, `c` and `κ` — onto a
`(g, c, κ)`-free family predicate plus a corrector-family hypothesis bridge.  Here that predicate
is the opaque parameter `CorrectorFamily`, which is exactly as strong and does
not couple this module to a live producer.

The the ceiling-exporting smallness interface ceiling is threaded through all three: each hole
exports its own
`cMax ∈ Ioo 0 1` and accepts every smallness `c ≤ cMax`.

Nothing analytic is added.  Every conclusion is the estimate; only the
binder surface changes, and every premise is corrector-family hypothesis (a projection of the root
predicates onto the indexed ones), never an inequality.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The corrector-and-flux decay clause: the quantitative corrector estimate -/

/-! ## The large-scale Lipschitz estimate clause -/

/-- **the large-scale Lipschitz estimate clause at the root interface.**  Same two mechanical
changes and the same
ceiling export.  The ceiling is the constant `(2 * Crec)⁻¹` that the decoupled terminal itself
selects, so the hole cannot be asked for a smaller
one. -/
theorem exists_largeScaleLipschitz_of_goodScaleProjection (d : ℕ) [NeZero d]
    (GoodScale : ℝ → ℝ → ℝ → Mat d → CoeffSpace d → ℝ → Prop)
    (hcustody : ∀ (g : ℝ), g ∈ Ico (0 : ℝ) 1 →
      ∀ (Crec cD : ℝ), 1 ≤ Crec → cD = (2 * Crec)⁻¹ → cD ∈ Ioo (0 : ℝ) 1 →
        ∀ (c : ℝ), c ∈ Ioo (0 : ℝ) 1 → c ≤ cD →
          ∀ κc : ℝ, 0 < κc →
            ∀ (abar : Mat d) (a : CoeffSpace d) (x : ℝ), 1 ≤ x →
              GoodScale g c κc abar a x →
                Root.DecoupledRootGoodScale d g cD κc abar a x) :
    ∀ g : ℝ, g ∈ Ico (0 : ℝ) 1 →
      ∃ cMax : ℝ, cMax ∈ Ioo (0 : ℝ) 1 ∧
        ∀ c : ℝ, c ∈ Ioo (0 : ℝ) 1 → c ≤ cMax →
          ∀ κc : ℝ, 0 < κc →
            ∃ C : ℝ, 0 < C ∧
              ∀ (abar : Mat d) (a : CoeffSpace d) (x : ℝ), 1 ≤ x →
                GoodScale g c κc abar a x →
                ∀ R : ℝ, x ≤ R →
                  ∀ (u : Vec d → ℝ) (Du : Vec d → Vec d),
                    MemH1a (fun y ↦ a.1 y) (ellipsoid abar R) u Du →
                    IsWeakSolutionOn (fun y ↦ a.1 y) (ellipsoid abar R) Du →
                      ∀ r : ℝ, r ∈ Icc x R →
                        weightedGradNorm (fun y ↦ a.1 y)
                            (ellipsoid abar r) Du ≤
                          ENNReal.ofReal C *
                            weightedGradNorm (fun y ↦ a.1 y)
                              (ellipsoid abar R) Du := by
  intro g hg
  obtain ⟨Crec, cD, hCrec, hcD, hcDRange, hindexed⟩ :=
    Root.exists_decoupledRootPhysicalLipschitz d g hg
  refine ⟨cD, hcDRange, ?_⟩
  intro c hc hccD κc hκc
  obtain ⟨C, hC, hrow⟩ := hindexed κc
  refine ⟨C, hC, ?_⟩
  intro abar a x hx hgood R hxR u Du hu hweak r hr
  exact hrow abar a x hx
    (hcustody g hg Crec cD hCrec hcD hcDRange c hc hccD κc hκc abar a x hx hgood)
    R hxR u Du hu hweak r hr

/-! ## The Liouville characterization clause: the double inclusion -/

end

end CorrectorComposition
end HighContrast
end HCPolySupport
