/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GlobalPotentialPatches
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Transport of coordinate measures through genuine potential patches

The coordinate measure is first pulled back to the open domain subtype, then
pushed forward along the inverse patch homeomorphism and the source inclusion.
Thus no arbitrary chart extension is required to be globally measurable.
The construction applies to arbitrary Borel measures, including infinite mass.
Local finiteness is proved only under finiteness on compact subsets of the
coordinate domain; it is not part of the definition.
-/

@[expose] public section

open Set MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches.Patch

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}

/-- The actual inverse coordinate map, with its domain restricted to the patch. -/
def toManifold (P : Patch θ u) : P.domain → M :=
  fun z => (P.homeomorph.symm z : M)

@[simp] theorem toManifold_apply (P : Patch θ u) (z : P.domain) :
    P.toManifold z = P.chart.val.symm z := rfl

variable [MeasurableSpace M] [BorelSpace M]

theorem measurableEmbedding_toManifold (P : Patch θ u) :
    MeasurableEmbedding P.toManifold :=
  (MeasurableEmbedding.subtype_coe P.source.isOpen.measurableSet).comp
    P.homeomorph.symm.measurableEmbedding

/-- Restrict a coordinate measure to the domain subtype, then transport it to
the manifold. The resulting measure is extended by zero outside the source. -/
def pushMeasure (P : Patch θ u) (μ : Measure (ComplexModel n)) : Measure M :=
  (μ.comap (Subtype.val : P.domain → ComplexModel n)).map P.toManifold

/-- This evaluation formula holds even for nonmeasurable sets. Only the inverse
chart's values on the actual coordinate domain occur on the right. -/
theorem pushMeasure_apply (P : Patch θ u) (μ : Measure (ComplexModel n)) (s : Set M) :
    P.pushMeasure μ s = μ ((P.domain : Set (ComplexModel n)) ∩ P.chart.val.symm ⁻¹' s) := by
  have hsub : MeasurableEmbedding (Subtype.val : P.domain → ComplexModel n) :=
    MeasurableEmbedding.subtype_coe P.domain.isOpen.measurableSet
  rw [pushMeasure, P.measurableEmbedding_toManifold.map_apply, hsub.comap_apply]
  congr 1
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩
  · rintro ⟨hz, hzs⟩
    exact ⟨⟨z, hz⟩, hzs, rfl⟩

/-- Equivalently, evaluate the original measure on the genuine coordinate image
of the part of the set lying in the source. -/
theorem pushMeasure_apply_image (P : Patch θ u) (μ : Measure (ComplexModel n))
    (s : Set M) :
    P.pushMeasure μ s = μ (P.chart.val '' (s ∩ (P.source : Set M))) := by
  rw [P.pushMeasure_apply]
  congr 1
  ext z
  constructor
  · rintro ⟨hz, hzs⟩
    exact ⟨P.chart.val.symm z, ⟨hzs, P.map_target hz⟩,
      P.chart.val.right_inv (P.domain_le_target hz)⟩
  · rintro ⟨x, ⟨hxs, hx⟩, rfl⟩
    refine ⟨P.map_source hx, ?_⟩
    change P.chart.val.symm (P.chart.val x) ∈ s
    rwa [P.chart.val.left_inv (P.source_subset hx)]

theorem pushMeasure_source_compl (P : Patch θ u) (μ : Measure (ComplexModel n)) :
    P.pushMeasure μ (P.source : Set M)ᶜ = 0 := by
  rw [P.pushMeasure_apply_image, compl_inter_self, image_empty, measure_empty]

theorem pushMeasure_restrict_source (P : Patch θ u) (μ : Measure (ComplexModel n)) :
    (P.pushMeasure μ).restrict P.source = P.pushMeasure μ := by
  apply Measure.restrict_eq_self_of_ae_mem
  exact ae_iff.mpr (P.pushMeasure_source_compl μ)

/-- Finiteness on compact subsets of the coordinate domain gives a finite-mass
neighborhood of each point of the source. Nothing is asserted at its boundary. -/
theorem pushMeasure_finiteAtNhds (P : Patch θ u) (μ : Measure (ComplexModel n))
    (hμ : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ P.domain → μ K < ∞)
    {x : M} (hx : x ∈ P.source) : (P.pushMeasure μ).FiniteAtFilter (𝓝 x) := by
  obtain ⟨K, hK, hxK, hKP⟩ := exists_compact_subset P.domain.isOpen (P.map_source hx)
  let V : Set M := P.chart.val.source ∩ P.chart.val ⁻¹' interior K
  have hV : IsOpen V := P.chart.val.isOpen_inter_preimage isOpen_interior
  have hxV : x ∈ V := ⟨P.source_subset hx, hxK⟩
  refine ⟨V, hV.mem_nhds hxV, ?_⟩
  rw [P.pushMeasure_apply_image]
  refine lt_of_le_of_lt (measure_mono ?_) (hμ K hK hKP)
  rintro _ ⟨y, ⟨hyV, _⟩, rfl⟩
  exact interior_subset hyV.2

end

end SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches.Patch
