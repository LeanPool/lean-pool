/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# Complex manifolds and real differential forms in charts

The manifold structure is mathlib's holomorphic chart compatibility, together
with the usual Hausdorff and second-countability conditions. A real differential
form is represented by smooth continuous alternating forms in these charts,
with the ordinary real derivative in the change-of-coordinates equation.

Coefficient functions are extended arbitrarily outside their chart targets;
only their restrictions to those open targets have geometric meaning. No global
exterior-derivative operator or coordinate-independence theorem is assumed here.
-/

@[expose] public section

open scoped Manifold ContDiff
open Set

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

/-- The standard complex vector space of complex dimension `n`. -/
abbrev ComplexModel (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- A Hausdorff, second-countable complex manifold, using mathlib's actual
charts and holomorphic transition maps. This imposes no metric or compactness. -/
class IsComplexManifold (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] : Prop extends
    T2Space M, SecondCountableTopology M, IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M

instance (n : ℕ) : IsComplexManifold n (ComplexModel n) where

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

/-- A chart belonging to the specified atlas (not an arbitrary homeomorphism). -/
abbrev ComplexChart (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] :=
  {e : OpenPartialHomeomorph M (ComplexModel n) // e ∈ atlas (ComplexModel n) M}

/-- The preferred chart around a point. -/
def complexChartAt (x : M) : ComplexChart n M :=
  ⟨chartAt (ComplexModel n) x, chart_mem_atlas (ComplexModel n) x⟩

theorem mem_complexChartAt_source (x : M) :
    x ∈ (complexChartAt (n := n) x).val.source :=
  mem_chart_source (ComplexModel n) x

/-- Change from `e`-coordinates to `f`-coordinates, on its actual overlap. -/
def chartTransition (e f : ComplexChart n M) :
    OpenPartialHomeomorph (ComplexModel n) (ComplexModel n) :=
  e.val.symm.trans f.val

/-- The derivative used to transport real tangent vectors between charts. -/
noncomputable def chartTransitionDerivative (e f : ComplexChart n M)
    (z : ComplexModel n) : ComplexModel n →L[ℝ] ComplexModel n :=
  fderiv ℝ (chartTransition e f) z

/-- Holomorphic overlap compatibility comes from the manifold structure. -/
theorem chartTransition_mem_groupoid [IsComplexManifold n M]
    (e f : ComplexChart n M) :
    chartTransition e f ∈ contDiffGroupoid ∞ (𝓘(ℂ, ComplexModel n)) :=
  StructureGroupoid.compatible _ e.property f.property

/-- A smooth real `k`-form, represented in the specified holomorphic atlas.
The compatibility field is the tensor transformation law, not an abstract
predicate standing in for differential geometry. -/
structure SmoothRealForm (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] (k : ℕ) where
  /-- The alternating coefficient form in each complex chart. -/
  coeff : ComplexChart n M → ComplexModel n →
    (ComplexModel n) [⋀^Fin k]→L[ℝ] ℝ
  smooth : ∀ e, ContDiffOn ℝ ∞ (coeff e) e.val.target
  compatible : ∀ e f z, z ∈ (chartTransition e f).source →
    ∀ v : Fin k → ComplexModel n,
      coeff e z v = coeff f (chartTransition e f z)
        (fun i => chartTransitionDerivative e f z (v i))

namespace SmoothRealForm

variable [IsComplexManifold n M] {k : ℕ}

/-- Closedness is vanishing of mathlib's exterior derivative in every chart.
Only points of the open chart target are tested. -/
def IsClosed (form : SmoothRealForm n M k) : Prop :=
  ∀ e z, z ∈ e.val.target → extDeriv (form.coeff e) z = 0

/-- The zero differential form satisfies the genuine overlap equation. -/
def zero : SmoothRealForm n M k where
  coeff := fun _ _ => 0
  smooth := fun _ => contDiffOn_const
  compatible := by intros; simp

end SmoothRealForm

end

end SGPT.Foundations.Analysis.FirstPass
