/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalNonPluripolar
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.OneSlotMassInvariance
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalSlotStokes

/-!
# The compact Kähler uniform truncation-mass estimate

Kept apart from `Pending.GlobalNonPluripolar`, which does not need a Kähler
background. Everything in this module is a consequence of `patch_uniformCompactTruncationMass`
    through the patch-mass
interface; the unconditional bounded case of that interface is proved in
`Pending.BoundedGlobalProduct`.

Everything here follows from `oneSlotMassInvariance`, a statement about bounded
potentials only, proved in `Pending.GlobalSlotStokes` with bounded BT products
and a partition-of-unity Stokes argument, without assuming the unbounded global
product's finite mass or mass calculus.
Sources: BEGZ `pro:finite`, `equ:welldef`.
-/

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar

open FirstPass FirstPass.GlobalPotentialPatches FirstPass.PositiveClasses
open MixedNonPluripolar

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}

variable [compactM : CompactSpace M]

include compactM in
/-- **One-slot mass invariance** (BEGZ `pro:finite`, `equ:welldef`). Replacing the
potential of one slot by another *bounded* theta-PSH potential does not change
the total mass of the global mixed measure: the compact integration-by-parts
identity `∫ ddᶜ(a - b) ∧ T = 0`, proved in `Pending.GlobalSlotStokes` from
bounded Bedford–Taylor products, a chart-smooth partition of unity and a
Kähler regularizer. No truncation level, no `⊥` value and no strict locus
occurs in the statement. -/
theorem oneSlotMassInvariance (omega : KahlerBackground n M)
    (η : Fin n → ClosedRealOneOneForm n M) :
    UniformBoundedGlobalMass.HasOneSlotMassInvariance η :=
  fun _ i₀ _ hv hva hb ha =>
    GlobalSlotStokes.globalMixedMeasure_update_univ_eq omega hv hb i₀ hva ha

include compactM in
/-- BEGZ uniform compact mass on a compact Kähler manifold. This interface
needs the global theta-PSH functions, not just a single valid local patch.
It is a consequence of `oneSlotMassInvariance`. -/
theorem patch_uniformCompactTruncationMass (omega : KahlerBackground n M)
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) (P : Patch θ u) :
    HasUniformCompactMixedTruncationMass P.domain P.corrected P.plurisubharmonic :=
  UniformBoundedGlobalMass.hasPatchTruncationMass_of_uniformBoundedGlobalMass omega
    (fun η => UniformBoundedGlobalMass.hasUniformBoundedGlobalMass_of_oneSlot
      (oneSlotMassInvariance omega η)) hu P

theorem patch_coordinateMeasure_finiteOnCompacts (omega : KahlerBackground n M)
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) (P : Patch θ u)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKP : K ⊆ P.domain) :
    mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic K < ⊤ :=
  coordinateMeasure_finiteOnCompacts_of_patchMass
    (patch_uniformCompactTruncationMass omega hu) P hK hKP

/-- Finite mass is proved on neighborhoods lying inside an active patch.
Zero extension need not be locally finite at a patch boundary. -/
theorem globalMixedMeasure_isLocallyFiniteMeasure (omega : KahlerBackground n M)
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) :
    IsLocallyFiniteMeasure (globalMixedMeasure θ u hu) :=
  globalMixedMeasure_isLocallyFiniteMeasure_of_patchMass hu
    (patch_uniformCompactTruncationMass omega hu)

theorem globalMixedMeasure_isFiniteMeasure (omega : KahlerBackground n M)
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) :
    IsFiniteMeasure (globalMixedMeasure θ u hu) :=
  globalMixedMeasure_isFiniteMeasure_of_patchMass hu
    (patch_uniformCompactTruncationMass omega hu)

theorem globalMixedMeasure_apply_lt_top (omega : KahlerBackground n M)
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) (S : Set M) :
    globalMixedMeasure θ u hu S < ⊤ :=
  globalMixedMeasure_apply_lt_top_of_patchMass hu
    (patch_uniformCompactTruncationMass omega hu) S

end

end SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
