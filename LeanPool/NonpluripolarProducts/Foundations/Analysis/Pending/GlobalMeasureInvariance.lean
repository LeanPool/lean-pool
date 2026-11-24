/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GlobalPotentialTransforms
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalNonPluripolar

/-!
# Global measure invariance under smooth changes of representative

For `η = θ + ddᶜf`, replacing `u` by `u-f` leaves every corrected local
potential unchanged. The actual coordinate measures and matched finite-cover
constructions therefore agree. Cover independence identifies the canonical
global measures. No new analytic hole, mass bound, or nondegeneracy assumption
is needed. These compositions use the proved local product theory and overlap
compatibility; they inherit no unfinished hole.

This is a change of the pair (background form, potential). Same singularity
type with a fixed background only implies equality of total masses, and is
not asserted to identify measures here.
-/

@[expose] public section

open Set MeasureTheory
open scoped ContDiff

namespace SGPT.Foundations.Analysis.Pending.GlobalMeasureInvariance

open FirstPass FirstPass.GlobalPotentialPatches FirstPass.GlobalPotentialTransforms
open GlobalNonPluripolar

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ η : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}
  {f : Fin n → M → ℝ}

variable (hf : ∀ i, ChartSmooth (n := n) (f i))
  (hθη : ∀ (i : Fin n) (e : ComplexChart n M) (z : ComplexModel n),
    z ∈ e.val.target → (η i).val.coeff e z = (θ i).val.coeff e z +
      smoothDDC (fun y => f i (e.val.symm y)) z)

/-- The corrected tuple, coordinate domain, and transport are identical. -/
theorem patchMeasure_changeRepresentative (P : Patch θ u) :
    patchMeasure (P.changeRepresentative hf hθη) = patchMeasure P := by
  simp only [patchMeasure, Patch.changeRepresentative_domain,
    Patch.changeRepresentative_corrected, Patch.changeRepresentative_pushMeasure]

/-- Transport a finite cover without changing its actual source sets. -/
def changeRepresentativeCover (C : FiniteCover θ u) :
    FiniteCover η (fun i x => u i x - (f i x : EReal)) where
  count := C.count
  patch i := (C.patch i).changeRepresentative hf hθη
  covers := C.covers

/-- Matched finite covers give exactly the same measure, without any bound
on total mass or use of overlap compatibility. -/
theorem measureFromCover_changeRepresentative (C : FiniteCover θ u) :
    measureFromCover (changeRepresentativeCover hf hθη C) = measureFromCover C := by
  simp only [measureFromCover, changeRepresentativeCover,
    Patch.changeRepresentative_source, patchMeasure_changeRepresentative]

variable [BorelSpace M] [CompactSpace M]

/-- Cover independence turns equality of matched constructions into equality
of the canonical global measures. The Kähler mass bound is not used. -/
theorem globalMixedMeasure_changeRepresentative
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) :
    globalMixedMeasure η (fun i x => u i x - (f i x : EReal))
        (fun i => thetaPlurisubharmonic_sub_smooth (hf i) (hθη i) (hu i)) =
      globalMixedMeasure θ u hu := by
  let C : FiniteCover θ u := Classical.choice (nonempty_finiteCover hu)
  rw [globalMixedMeasure_eq_measureFromCover _ (changeRepresentativeCover hf hθη C),
    globalMixedMeasure_eq_measureFromCover hu C]
  exact measureFromCover_changeRepresentative hf hθη C

/-- Finite additive constants do not change the global measure. No
nondegeneracy or positive-dimension assumption is required. -/
theorem globalMixedMeasure_sub_const
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) (c : Fin n → ℝ) :
    globalMixedMeasure θ (fun i x => u i x - (c i : EReal))
        (fun i => thetaPlurisubharmonic_sub_const (hu i) (c i)) =
      globalMixedMeasure θ u hu := by
  apply globalMixedMeasure_changeRepresentative (f := fun i _ => c i)
    (fun _ _ => contDiffOn_const) _ hu
  intro i e z _
  rw [smoothDDC_const, add_zero]

end

end SGPT.Foundations.Analysis.Pending.GlobalMeasureInvariance
