/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GlobalMeasureNoncharging
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PositiveClasses
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MixedNonPluripolar
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PatchOverlap

/-!
# Actual global mixed non-pluripolar measures

Coordinate truncation-limit measures are transported through actual patch
homeomorphisms, then glued by a finite cover. Neither existence of a global
measure nor its uniqueness is assumed in a structure. Coordinate/potential
overlap compatibility is proved in Pending.PatchOverlap (gauge invariance and
holomorphic covariance of the truncation limits). One analytic gap is explicit:
the compact Kähler uniform truncation-mass estimate. All other assertions below
are derived from that interface, the local mixed theory, and proved measure calculus.

Overlap compatibility does not assume local finiteness. The mass estimate
retains global theta-PSH hypotheses: local patch data alone would not suffice.
The constructor also permits degenerate potentials and the empty tuple; no
claim identifying arbitrary closed positive currents with potentials is made.
Sources: BEGZ 1.2, pro:basic, pro:finite; revised manuscript sec:npp.
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

/-- The actual local mixed limit, transported and extended by zero from the
genuine coordinate domain. Its BT inputs still depend on Pending existence. -/
def patchMeasure (P : Patch θ u) : Measure M :=
  P.pushMeasure (mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic)

theorem patchMeasure_source_compl (P : Patch θ u) :
    patchMeasure P (P.source : Set M)ᶜ = 0 :=
  P.pushMeasure_source_compl _

theorem patchMeasure_restrict_source (P : Patch θ u) :
    (patchMeasure P).restrict (P.source : Set M) = patchMeasure P :=
  P.pushMeasure_restrict_source _

/-- Holomorphic covariance and smooth pluriharmonic gauge invariance on the
overlap. The measures may have infinite mass on compact subsets. -/
theorem patchMeasure_overlap (P Q : Patch θ u) :
    (patchMeasure P).restrict ((P.source : Set M) ∩ Q.source) =
      (patchMeasure Q).restrict ((P.source : Set M) ∩ Q.source) :=
  PatchOverlap.pushMeasure_restrict_inter_eq P Q
    (PatchOverlap.mixedTruncationLimitMeasure_overlap P Q)

theorem patchMeasure_doesNotChargeManifoldPluripolar (P : Patch θ u) :
    DoesNotChargeManifoldPluripolar (n := n) (patchMeasure P) :=
  P.pushMeasure_doesNotChargeManifoldPluripolar _
    (mixedTruncationLimitMeasure_doesNotChargePluripolarOn P.plurisubharmonic)

/-- A sum of restrictions to disjointified patch sources. Construction itself
does not require the analytic overlap theorem or compactness. -/
def measureFromCover (C : FiniteCover θ u) : Measure M :=
  FiniteMeasureGluing.glue (fun i => ((C.patch i).source : Set M))
    (fun i => patchMeasure (C.patch i))

/-- Every patch, including one outside the chosen cover, recovers its local
measure by restricting the glued measure. -/
theorem measureFromCover_restrict_patch (C : FiniteCover θ u) (P : Patch θ u) :
    (measureFromCover C).restrict (P.source : Set M) = patchMeasure P := by
  have hcover : (P.source : Set M) ⊆ ⋃ i, ((C.patch i).source : Set M) := by
    intro x _
    obtain ⟨i, hx⟩ := C.covers x
    exact mem_iUnion.mpr ⟨i, hx⟩
  exact (FiniteMeasureGluing.glue_restrict _ _
    (fun i => (C.patch i).source.isOpen.measurableSet) P.source.isOpen.measurableSet
    hcover (patchMeasure P) (fun i => patchMeasure_overlap (C.patch i) P)).trans
      (patchMeasure_restrict_source P)

/-- Genuine local restrictions determine a measure on the whole manifold. -/
theorem measureFromCover_unique (C : FiniteCover θ u) (ν : Measure M)
    (hν : ∀ P : Patch θ u, ν.restrict (P.source : Set M) = patchMeasure P) :
    ν = measureFromCover C := by
  have hcover : (⋃ i, ((C.patch i).source : Set M)) = univ := by
    apply eq_univ_iff_forall.mpr
    intro x
    obtain ⟨i, hx⟩ := C.covers x
    exact mem_iUnion.mpr ⟨i, hx⟩
  apply FiniteMeasureGluing.ext_of_restrict_eq _
    (fun i => (C.patch i).source.isOpen.measurableSet) hcover
  intro i
  exact (hν (C.patch i)).trans (measureFromCover_restrict_patch C (C.patch i)).symm

theorem measureFromCover_independent (C D : FiniteCover θ u) :
    measureFromCover C = measureFromCover D :=
  measureFromCover_unique D _ (measureFromCover_restrict_patch C)

theorem measureFromCover_doesNotChargeManifoldPluripolar (C : FiniteCover θ u) :
    DoesNotChargeManifoldPluripolar (n := n) (measureFromCover C) :=
  FiniteMeasureGluing.glue_doesNotChargeManifoldPluripolar _ _
    (fun i => patchMeasure_doesNotChargeManifoldPluripolar (C.patch i))

/-- Compactness chooses an actual finite potential cover; no measure is chosen
from an assumed global existence statement. -/
def globalMixedMeasure [CompactSpace M]
    (θ : Fin n → ClosedRealOneOneForm n M) (u : Fin n → M → EReal)
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) : Measure M :=
  measureFromCover (Classical.choice (nonempty_finiteCover hu))

variable [compactM : CompactSpace M]

theorem globalMixedMeasure_restrict_patch
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) (P : Patch θ u) :
    (globalMixedMeasure θ u hu).restrict (P.source : Set M) = patchMeasure P :=
  measureFromCover_restrict_patch _ P

theorem globalMixedMeasure_unique
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) (ν : Measure M)
    (hν : ∀ P : Patch θ u, ν.restrict (P.source : Set M) = patchMeasure P) :
    ν = globalMixedMeasure θ u hu :=
  measureFromCover_unique _ ν hν

theorem globalMixedMeasure_eq_measureFromCover
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) (C : FiniteCover θ u) :
    globalMixedMeasure θ u hu = measureFromCover C :=
  measureFromCover_independent _ C

omit [BorelSpace M] in
theorem globalMixedMeasure_proof_independent
    (hu hv : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) :
    globalMixedMeasure θ u hu = globalMixedMeasure θ u hv := rfl

theorem globalMixedMeasure_doesNotChargeManifoldPluripolar
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) :
    DoesNotChargeManifoldPluripolar (n := n) (globalMixedMeasure θ u hu) :=
  measureFromCover_doesNotChargeManifoldPluripolar _

/-- The patch mass condition, as a property of the tuple rather than of one
patch. Its only proofs are the Kähler theorem below and the unconditional
bounded case of `Pending.BoundedGlobalProduct`. -/
def HasPatchTruncationMass (θ : Fin n → ClosedRealOneOneForm n M) (u : Fin n → M → EReal) :
    Prop :=
  ∀ P : Patch θ u, HasUniformCompactMixedTruncationMass P.domain P.corrected P.plurisubharmonic

omit [MeasurableSpace M] [BorelSpace M] compactM in
theorem coordinateMeasure_finiteOnCompacts_of_patchMass
    (hmass : HasPatchTruncationMass θ u) (P : Patch θ u)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKP : K ⊆ P.domain) :
    mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic K < ⊤ :=
  (mixedTruncationLimitMeasure_finiteOnCompacts_iff P.plurisubharmonic).mpr
    (hmass P) K hK hKP

/-- Finite mass is proved on neighborhoods lying inside an active patch.
Zero extension need not be locally finite at a patch boundary. Only the patch
mass condition is used; no Kähler background enters. -/
theorem globalMixedMeasure_isLocallyFiniteMeasure_of_patchMass
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) (hmass : HasPatchTruncationMass θ u) :
    IsLocallyFiniteMeasure (globalMixedMeasure θ u hu) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨P, hx⟩ := exists_patch_containing hu x
  obtain ⟨V, hV, hfinite⟩ := P.pushMeasure_finiteAtNhds
    (mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic)
    (fun _ hK hKP => coordinateMeasure_finiteOnCompacts_of_patchMass hmass P hK hKP) hx
  refine ⟨V ∩ (P.source : Set M), inter_mem hV (P.source.isOpen.mem_nhds hx), ?_⟩
  calc
    globalMixedMeasure θ u hu (V ∩ (P.source : Set M)) =
        (globalMixedMeasure θ u hu).restrict (P.source : Set M) V :=
      (Measure.restrict_apply' P.source.isOpen.measurableSet).symm
    _ = patchMeasure P V := congrArg (fun μ : Measure M => μ V)
      (globalMixedMeasure_restrict_patch hu P)
    _ < ⊤ := hfinite

theorem globalMixedMeasure_isFiniteMeasure_of_patchMass
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) (hmass : HasPatchTruncationMass θ u) :
    IsFiniteMeasure (globalMixedMeasure θ u hu) := by
  let := globalMixedMeasure_isLocallyFiniteMeasure_of_patchMass hu hmass
  infer_instance

theorem globalMixedMeasure_apply_lt_top_of_patchMass
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) (hmass : HasPatchTruncationMass θ u)
    (S : Set M) : globalMixedMeasure θ u hu S < ⊤ := by
  let := globalMixedMeasure_isFiniteMeasure_of_patchMass hu hmass
  exact measure_lt_top _ _

end

end SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
