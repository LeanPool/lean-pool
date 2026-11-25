/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ComplexManifold

/-!
# Coordinate domains and overlaps
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace

namespace SGPT.Foundations.Analysis.FirstPass

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- The open coordinate domain of an actual atlas chart. -/
def chartTarget (e : ComplexChart n M) : Opens (ComplexModel n) :=
  ⟨e.val.target, e.val.open_target⟩

/-- The coordinate domain `e(e.source ∩ U)` of an open `U ⊆ M` in the chart `e`. -/
def _root_.SGPT.NPP.chartDomain (e : ComplexChart n M) (U : Opens M) : Opens (ComplexModel n) :=
  ⟨e.val.target ∩ e.val.symm ⁻¹' U, e.val.isOpen_inter_preimage_symm U.isOpen⟩

theorem _root_.SGPT.NPP.chartDomain_le (e : ComplexChart n M) (U : Opens M) :
    SGPT.NPP.chartDomain e U ≤ chartTarget e :=
  fun _ hz => hz.1

theorem _root_.SGPT.NPP.mem_chartDomain {e : ComplexChart n M} {U : Opens M} {z : ComplexModel n} :
    z ∈ SGPT.NPP.chartDomain e U ↔ z ∈ e.val.target ∧ e.val.symm z ∈ U := Iff.rfl

/-- The coordinate domain of the whole manifold is the chart target. -/
theorem _root_.SGPT.NPP.chartDomain_top (e : ComplexChart n M) :
    SGPT.NPP.chartDomain e ⊤ = chartTarget e := by
  ext z
  simp [SGPT.NPP.mem_chartDomain, chartTarget]

/-- Overlap in the first chart's coordinates. -/
def overlapSource (e f : ComplexChart n M) : Opens (ComplexModel n) :=
  ⟨(chartTransition e f).source, (chartTransition e f).open_source⟩

/-- The same overlap in the second chart's coordinates. -/
def overlapTarget (e f : ComplexChart n M) : Opens (ComplexModel n) :=
  ⟨(chartTransition e f).target, (chartTransition e f).open_target⟩

theorem overlapSource_le (e f : ComplexChart n M) : overlapSource e f ≤ chartTarget e :=
  fun _ hz => hz.1

theorem overlapTarget_le (e f : ComplexChart n M) : overlapTarget e f ≤ chartTarget f :=
  fun _ hz => hz.1

/-- On an overlap, `φ ∘ e⁻¹ = (φ ∘ f⁻¹) ∘ (f ∘ e⁻¹)`. -/
theorem chart_comp_transition {α : Type*} (φ : M → α) (e f : ComplexChart n M) :
    ∀ x ∈ overlapSource e f, φ (e.val.symm x) = φ (f.val.symm (chartTransition e f x)) := by
  intro x hx
  have hx' : x ∈ (chartTransition e f).source := hx
  have hxf : e.val.symm x ∈ f.val.source := by
    simp only [chartTransition, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage] at hx'
    exact hx'.2
  simp only [chartTransition, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    f.val.left_inv hxf]

end SGPT.Foundations.Analysis.FirstPass
