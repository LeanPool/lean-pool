/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothProductDensity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SmoothBedfordTaylorMeasure

/-!
# Trace measures of smooth Bedford–Taylor products

Computes the trace measure for a product of smooth plurisubharmonic potentials.
-/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff
namespace SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothTraceMeasure
open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
  LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
  LocalBedfordTaylorDecreasing LocalBedfordTaylorSmoothProductDensity
variable {n : ℕ}

/-- The independently constructed positive recursive current's genuine Riesz trace. -/
def recursiveMixedTraceMeasure (U : Opens (ComplexModel n))
    (u : Fin n → ComplexModel n → ℝ) (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) :
    Measure (ComplexModel n) :=
  (isPositive_btProduct n 0 u (oneCurrentOf (U := U) (Nat.zero_add n))
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) hu).1.traceMeasure

/-- Natural smoothness and PSH internally produce both genuine measure domains. -/
theorem recursiveMixedTraceMeasure_eq_smoothMixedMeasure {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ}
    (hg : ∀ i, ContDiffOn ℝ ∞ (u i) U)
    (hp : ∀ i, PlurisubharmonicOn (fun z => (u i z : EReal)) U) :
    let hsm := MixedMongeAmpere.isSmoothMixedPshOn_of_components
      (fun i => isSmoothPshOn_of_psh (hg i) (hp i))
    let hu := fun i => isLocallyBoundedPshOn_of_isSmoothPshOn (isSmoothPshOn_of_psh (hg i) (hp i))
    recursiveMixedTraceMeasure U u hu = smoothMixedMeasure U u hsm := by
  dsimp only
  let hsm := MixedMongeAmpere.isSmoothMixedPshOn_of_components
    (fun i => isSmoothPshOn_of_psh (hg i) (hp i))
  let hu := fun i => isLocallyBoundedPshOn_of_isSmoothPshOn (isSmoothPshOn_of_psh (hg i) (hp i))
  let hT := (isPositive_btProduct n 0 u (oneCurrentOf (U := U) (Nat.zero_add n))
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) hu).1
  change hT.traceMeasure = smoothMixedMeasure U u hsm
  apply eq_of_forall_testFunction_integral_eq (U := U) hT.traceMeasure_compl
    (BedfordTaylor.densityMeasure_compl U u)
    (fun K hK hKU => hT.traceMeasure_lt_top hK hKU)
    (fun K hK hKU => MixedMongeAmpere.smoothMixedMeasure_finiteOnCompacts hsm hK hKU)
  intro φ
  rw [hT.integral_traceMeasure, btProduct_oneCurrent_apply hg hp]
  exact (BedfordTaylor.integral_densityMeasure
    (fun i => ⟨(hsm.component i).1, (hsm.component i).2.2⟩) φ.tsupport_subset).symm

end SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothTraceMeasure
