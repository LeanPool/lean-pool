/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GlobalPatchMeasures
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.FiniteMeasureGluing
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ManifoldPluripolar

/-!
# Pluripolar noncharging under coordinate transport and finite gluing

Transport through an actual potential patch preserves noncharging of local
pluripolar sets. Finite gluing preserves noncharging because each restricted
summand is dominated by its original measure. Neither argument assumes that
the exceptional set is measurable, and no Haar-nullity comparison is used.
-/

@[expose] public section

open Set MeasureTheory

namespace SGPT.Foundations.Analysis.FirstPass

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M]

namespace GlobalPotentialPatches.Patch

variable [BorelSpace M]
  {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}

/-- Coordinate noncharging gives noncharging of every manifold pluripolar set,
including sets which are not measurable. -/
theorem pushMeasure_doesNotChargeManifoldPluripolar (P : Patch θ u)
    (μ : Measure (ComplexModel n)) (hμ : DoesNotChargePluripolarOn μ P.domain) :
    DoesNotChargeManifoldPluripolar (n := n) (P.pushMeasure μ) := by
  intro S hS
  rw [P.pushMeasure_apply]
  apply measure_mono_null ?_
    (hμ (pluripolarChartSet S P.chart)
      ((hS P.chart).mono_domain P.domain_le_target))
  intro z hz
  exact ⟨⟨P.domain_le_target hz.1, hz.2⟩, hz.1⟩

end GlobalPotentialPatches.Patch

namespace FiniteMeasureGluing

omit [IsComplexManifold n M] in
/-- Finite gluing preserves noncharging without assuming compatibility or that
the gluing sets are measurable or cover the manifold. -/
theorem glue_doesNotChargeManifoldPluripolar {m : ℕ} (U : Fin m → Set M)
    (μ : Fin m → Measure M)
    (hμ : ∀ i, DoesNotChargeManifoldPluripolar (n := n) (μ i)) :
    DoesNotChargeManifoldPluripolar (n := n) (glue U μ) := by
  intro S hS
  change Measure.sum (fun i => (μ i).restrict (disjointed U i)) S = 0
  apply Measure.sum_apply_eq_zero.mpr
  intro i
  apply le_antisymm ?_ bot_le
  calc
    ((μ i).restrict (disjointed U i)) S ≤ (μ i) S :=
      Measure.restrict_apply_le _ _
    _ = 0 := hμ i S hS

end FiniteMeasureGluing

end SGPT.Foundations.Analysis.FirstPass
