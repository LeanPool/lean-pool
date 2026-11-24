/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalNonPluripolar

/-!
# Slot symmetry of global mixed non-pluripolar measures

Relabeling the slots of a tuple of `θ`-PSH functions does not change the global
mixed non-pluripolar measure.

* Bounded case: `MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure_perm`, since
  the mixed coefficient is a symmetric function of the Hessians.
* Truncations: truncating commutes with relabeling, and the common strict locus
  quantifies over all slots, so every truncation measure and hence the increasing
  limit are invariant.
* Global: a patch of `u` with permuted potentials is a patch of the permuted
  tuple with the same chart and coordinate domain; its corrected tuple is the
  permuted corrected tuple, so the two patch measures coincide. Uniqueness of the
  global measure from its patch restrictions concludes.
-/

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.GlobalSlotPerm

open FirstPass FirstPass.GlobalPotentialPatches FirstPass.PositiveClasses
open FirstPass.MixedNonPluripolar MixedMongeAmpere MixedNonPluripolar GlobalNonPluripolar

noncomputable section

section Local

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → EReal}

theorem mixedTruncationReal_perm (u : Fin n → ComplexModel n → EReal)
    (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    mixedTruncationReal (fun i => u (σ i)) k = fun i => mixedTruncationReal u k (σ i) :=
  rfl

theorem commonStrictLocus_perm (Ω : Opens (ComplexModel n))
    (u : Fin n → ComplexModel n → EReal) (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    commonStrictLocus Ω (fun i => u (σ i)) k = commonStrictLocus Ω u k := by
  ext z
  refine and_congr_right fun _ => ⟨fun h i => ?_, fun h i => h (σ i)⟩
  simpa using h (σ.symm i)

/-- Truncation measures are symmetric in the slots. -/
theorem mixedTruncationMeasure_perm (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (σ : Equiv.Perm (Fin n)) (hv : ∀ i, PlurisubharmonicOn (u (σ i)) Ω) (k : ℕ) :
    mixedTruncationMeasure Ω (fun i => u (σ i)) hv k = mixedTruncationMeasure Ω u hu k := by
  unfold mixedTruncationMeasure
  rw [commonStrictLocus_perm]
  congr 1
  exact canonicalMixedBedfordTaylorMeasure_perm (mixedTruncationReal_isLocallyBounded hu k) σ _

/-- The truncation limit measure is symmetric in the slots. -/
theorem mixedTruncationLimitMeasure_perm (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (σ : Equiv.Perm (Fin n)) (hv : ∀ i, PlurisubharmonicOn (u (σ i)) Ω) :
    mixedTruncationLimitMeasure Ω (fun i => u (σ i)) hv =
      mixedTruncationLimitMeasure Ω u hu := by
  ext s
  rw [mixedTruncationLimitMeasure_apply, mixedTruncationLimitMeasure_apply]
  simp only [mixedTruncationMeasure_perm hu σ hv]

end Local

section Global

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}

/-- A patch of `u`, with its potentials relabeled, is a patch of the relabeled
tuple on the same chart and coordinate domain. -/
def permPatch (P : Patch θ u) (σ : Equiv.Perm (Fin n)) :
    Patch (fun i => θ (σ i)) (fun i => u (σ i)) where
  chart := P.chart
  domain := P.domain
  domain_le_target := P.domain_le_target
  potential i := P.potential (σ i)
  localPotential i := P.localPotential (σ i)
  plurisubharmonic i := P.plurisubharmonic (σ i)

@[simp] theorem permPatch_source (P : Patch θ u) (σ : Equiv.Perm (Fin n)) :
    (permPatch P σ).source = P.source := rfl

theorem permPatch_corrected (P : Patch θ u) (σ : Equiv.Perm (Fin n)) :
    (permPatch P σ).corrected = fun i => P.corrected (σ i) := rfl

variable [MeasurableSpace M] [BorelSpace M]

theorem patchMeasure_perm (P : Patch θ u) (σ : Equiv.Perm (Fin n)) :
    patchMeasure (permPatch P σ) = patchMeasure P := by
  ext s
  rw [patchMeasure, patchMeasure, Patch.pushMeasure_apply, Patch.pushMeasure_apply]
  exact congrArg (fun μ : Measure (ComplexModel n) =>
      μ ((P.domain : Set (ComplexModel n)) ∩ P.chart.val.symm ⁻¹' s))
    (mixedTruncationLimitMeasure_perm (Ω := P.domain) (u := P.corrected)
      P.plurisubharmonic σ fun i => P.plurisubharmonic (σ i))

/-- **Slot symmetry of the global mixed non-pluripolar measure.** -/
theorem globalMixedMeasure_perm [CompactSpace M] {θ : Fin n → ClosedRealOneOneForm n M}
    {u : Fin n → M → EReal} (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    (σ : Equiv.Perm (Fin n)) :
    globalMixedMeasure (fun i => θ (σ i)) (fun i => u (σ i)) (fun i => hu (σ i)) =
      globalMixedMeasure θ u hu := by
  refine globalMixedMeasure_unique hu _ fun P => ?_
  rw [← permPatch_source P σ, globalMixedMeasure_restrict_patch, patchMeasure_perm]

end Global

end

end SGPT.Foundations.Analysis.Pending.GlobalSlotPerm
