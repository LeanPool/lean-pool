/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddValue
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderComposeBoundary

/-!
# OneStepOddCompose

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Plumbing for the boundary producer: local identification and `EqOn` transfer

`OneStepOddValue` runs the boundary branch's Schauder producer from an
almost-everywhere odd competitor.  This module supplies the two pieces of
plumbing that producer needs once its datum is the **variationally** harmonic
`H¹` datum on the doubled window: the local identification of the two Weyl
representatives, and the transfer of the representative's two consumers along
the resulting `EqOn`.

## The local identification device

's `eqOn_of_ae_eq_of_continuous` needs *global* continuity, which no Weyl
representative has: harmonicity is asserted only on the window.  The local twin
`eqOn_of_ae_eq_of_continuousOn` is the same proof with `ContinuousOn` in place
of `Continuous`: on an open `S` the disagreement set is open, hence null
implies empty.  Continuity on the window comes from harmonicity for free
(`HarmonicAt` carries `ContDiffAt ℝ 2`), which is
`continuousOn_of_harmonicOnNhd`.

This settles the identification of the **two Weyl representatives** the boundary
branch produces: the interior route applies Weyl's lemma on the anchor's moved
replacement cube `R_mov`, the boundary route on the doubled window
`reflectedWindow`, and neither set contains the other — but both contain `U₂`,
both representatives are continuous there and both agree almost everywhere with
the competitor, so they agree *pointwise* on `U₂`
(two continuous harmonic representatives agreeing a.e. agree pointwise).  The
two consumers of the representative then transfer: `gradField` because `fderiv`
is local, and `affineExcess` because it is an integral over `U₂`
(`affineExcess_congr_eqOn`).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec vecDot openCubeSet originCube coordFaceReflection H1Function)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The local identification device -/

/-- Classical harmonicity on a window gives continuity on that window: `HarmonicAt`
carries `ContDiffAt ℝ 2`. -/
theorem continuousOn_of_harmonicOnNhd {S : Set (Vec d)} {V : Vec d → ℝ}
    (hV : HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' S)) :
    ContinuousOn V S := by
  exact continuousOn_of_harmonicOnNhd_toEuc hV

/-! ## 2. Transfer of the two consumers along an `EqOn` -/

/-- An `EqOn` on a measurable window is an almost-everywhere equality there. -/
theorem ae_eq_restrict_of_eqOn {W : Set (Vec d)} (hW : MeasurableSet W)
    {f g : Vec d → ℝ} (h : Set.EqOn f g W) : f =ᵐ[volume.restrict W] g :=
  (MeasureTheory.ae_restrict_iff' hW).2 (Filter.Eventually.of_forall fun _ hp => h hp)

/-- The excess minimum is an almost-everywhere invariant: the competitor set is
unchanged. -/
theorem affineExcessRaw_congr_ae {W : Set (Vec d)} {f g : Vec d → ℝ}
    (h : f =ᵐ[volume.restrict W] g) : affineExcessRaw W f = affineExcessRaw W g := by
  have hset : affineDistSet W f = affineDistSet W g := by
    simp only [affineDistSet]
    congr 1
    funext p
    exact affineDistOn_congr_ae h p.1 p.2
  simp only [affineExcessRaw, hset]

/-- The excess is an almost-everywhere invariant. -/
theorem affineExcess_congr_ae {W : Set (Vec d)} {f g : Vec d → ℝ}
    (h : f =ᵐ[volume.restrict W] g) : affineExcess W f = affineExcess W g := by
  simp only [affineExcess, affineExcessRaw_congr_ae h]

/-- The excess transfers along an `EqOn` on a measurable window. -/
theorem affineExcess_congr_eqOn {W : Set (Vec d)} (hW : MeasurableSet W)
    {f g : Vec d → ℝ} (h : Set.EqOn f g W) : affineExcess W f = affineExcess W g :=
  affineExcess_congr_ae (ae_eq_restrict_of_eqOn hW h)

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

end

end Algsuperdiff.Section4.Provider.ExcessDecay
