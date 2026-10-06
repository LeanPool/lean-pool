/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.BlockRowSupplyProjection
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.PushCorrectorFamilyDischarge
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.PushforwardNormalizedSupply

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.EventRetainingCertificate

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# the event-retaining certificate: the event-retaining certificate, and the stationary corrector
family clause inside the assembly

`Root.RootBlockRowSupply` is not dischargeable from the ceiling-exporting
smallness interface, because `hhomogenized`'s binder surface is applied one
sample at a time and drops `hquenched`'s translation-invariant event.  This
module carries out the repair end to end:

* the root assembly `polynomial_homogenization_of_quenched_scale` carries
  `hhomogenized` widened to the event-level row — the binder and its single
  application site (the proof already had `Ωend` and its invariance in scope);
* `exists_rootGoodScaleOn_of_quenchedEventRow` proves the widened
  `hhomogenized` at the event-retaining certificate `rootGoodScaleOn`, from
  exactly `hquenched`'s own data, and the fit is machine-checked below;
* `rootBlockRowSupply_of_rootGoodScaleOn` discharges the **real**
  `Root.RootBlockRowSupply`, and with the stationary corrector family clause's own
  `rootNormalizedSupply_of_blockRow` and `correctorFamilyHole_of_blockRow`
  the stationary corrector family clause is inhabited with **no hypothesis**,
  on the whole of `g ∈ Ico 0 1`, once the order is free.

## The admitted range, exactly

**The range is the whole of `g ∈ Ico 0 1`.**  At a *fixed* construction
order `s` the window `rho < 2 * s` reads `g < (8 s - 1)/3`, and the corrector
cone forces `s < 1/2`, so no constant order covers `[0,1)` — at the frozen
`3/16` it read `g < 1/6`.  The corrector datum now records its order as a
**field**, so the event, the selected carrier and the marker
`RootPushCorrectorFamilyPredicate` are order-free and the supply may choose
the order *after* `g`.  At the printed certificate order `(1 + g) / 4` both
constraints — `s < 1/2` and `rho < 2 * s` — are equivalent to `g < 1`.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-! ## The event-retaining certificate at a reconciled smallness -/

/-- The event-retaining certificate threaded through a `g`-indexed smallness, exactly as
`reconciledRootGoodScale` threads the ceiling-exporting smallness interface one. -/
@[expose]
def reconciledRootGoodScaleOn (d : ℕ) [NeZero d] (cStar : ℝ → ℝ) :
    ℝ → ℝ → Mat d → CoeffSpace d → ℝ → Prop :=
  fun g kappaRate abar a x => rootGoodScaleOn d g (cStar g) kappaRate abar a x

/-- Forgetting the event recovers the ceiling-exporting smallness interface, so
every result about the decay, Liouville, Lipschitz and C¹ clauses applies
unchanged at the widened certificate. -/
theorem reconciledRootGoodScale_of_reconciledRootGoodScaleOn [NeZero d] (cStar : ℝ → ℝ)
    {g kappaRate : ℝ} {abar : Mat d} {a : CoeffSpace d} {x : ℝ}
    (h : reconciledRootGoodScaleOn d cStar g kappaRate abar a x) :
    reconciledRootGoodScale d cStar g kappaRate abar a x := h.1

/-! ## The real block-row supply -/

/-- **`Root.RootBlockRowSupply` from the event-retaining certificate, on the
whole root range.**  Every field is read off the event; nothing is estimated.
The order is the printed `(1 + g) / 4`, chosen after `g`. -/
theorem rootBlockRowSupply_of_rootGoodScaleOn (d : ℕ) [NeZero d]
    {g c kappaRate : ℝ} (hg : g ∈ Ico (0 : ℝ) 1) :
    Root.RootBlockRowSupply d (rootGoodScaleOn d g c kappaRate) := by
  intro abar _hS a _x hgood
  obtain ⟨-, Omega, kappa, delta, S, X, ha, hinv, hkappa, hdelta, hrow⟩ := hgood
  obtain ⟨hrho0, hrho1⟩ := printRowOrder_mem hg
  exact ⟨Omega, (1 + g) / 4, (1 + 3 * g) / 4, kappa, delta, S, X, ha, hinv,
    printCertificateOrder_pos hg,
    (printCertificateOrder_lt_half_iff g).mpr hg.2, hrho0, hrho1,
    (printRowOrder_lt_twice_printCertificateOrder_iff g).mpr hg.2,
    hkappa, hdelta, hrow⟩

/-- The normalized supply, unconditional on the whole root range. -/
theorem rootNormalizedSupply_of_rootGoodScaleOn (d : ℕ) [NeZero d]
    {g c kappaRate : ℝ} (hg : g ∈ Ico (0 : ℝ) 1) :
    Root.RootNormalizedSupply d (rootGoodScaleOn d g c kappaRate) :=
  Root.rootNormalizedSupply_of_blockRow
    (rootBlockRowSupply_of_rootGoodScaleOn d hg)

/-- **The corrector-and-flux decay clause/the Liouville and C¹ clauses family corrector-family
hypothesis, unconditional on the whole root range.** -/
theorem rootPushCanonicalFamily_of_rootGoodScaleOn (d : ℕ) [NeZero d]
    {g c kappaRate : ℝ} (hg : g ∈ Ico (0 : ℝ) 1) :
    Root.RootPushCanonicalFamily d (rootGoodScaleOn d g c kappaRate) :=
  rootPushCanonicalFamily_of_normalizedSupply
    (rootNormalizedSupply_of_rootGoodScaleOn d hg)

/-! ## the stationary corrector family clause, unconditional on the whole root range -/

/-- **the stationary corrector family clause at the event-retaining certificate, with no
hypothesis, for
every `g ∈ Ico 0 1`.** -/
theorem correctorFamilyHole_of_reconciledRootGoodScaleOn (d : ℕ) [NeZero d] (cStar : ℝ → ℝ)
    {g : ℝ} (hg : g ∈ Ico (0 : ℝ) 1) (κ : ℝ) :
    ∀ abar : Mat d, (symmPart abar).PosDef →
      ∃ (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
        (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
        Root.RootPushCorrectorFamilyPredicate d abar Phi gradPhi ∧
        (∀ (c : ℝ) (e e' : Vec d) (a : CoeffSpace d),
          gradPhi (c • e + e') a
            =ᵐ[volume] fun x => c • gradPhi e a x + gradPhi e' a x) ∧
        (∀ (z : Fin d → ℤ) (e : Vec d) (a : CoeffSpace d),
          gradPhi e (translateCoeff z a)
            =ᵐ[volume] fun x => gradPhi e a (x + Source.AKL.intTranslation z)) ∧
        ∀ (a : CoeffSpace d) (x : ℝ),
          reconciledRootGoodScaleOn d cStar g κ abar a x →
          ∀ e : Vec d,
            HasWeakGradientOn Set.univ (Phi e a) (gradPhi e a) ∧
              IsWeakSolutionOn (fun y => a.1 y) Set.univ
                (fun y => e + gradPhi e a y) :=
  Root.correctorFamilyHole_of_blockRow d
    (rootGoodScaleOn d g (cStar g) κ)
    (rootBlockRowSupply_of_rootGoodScaleOn d hg)

end

end CorrectorComposition
end HighContrast
end HCPolySupport
