/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import Mathlib.MeasureTheory.Integral.Prod

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.CountableDisjointDiagonal

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Diagonal integrals over a countable disjoint family

The diagonal products of pairwise disjoint measurable sets are again pairwise
disjoint.  Their nonnegative integrals therefore sum to at most the integral
over any common containing set.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal
open scoped Function

variable {ι α : Type*} [Countable ι] [MeasurableSpace α]

/-- The sum of diagonal product integrals over a countable disjoint family is
bounded by the product integral over a containing set. -/
theorem tsum_setLIntegral_prod_self_le
    (μ : Measure α) {A : ι → Set α} {U : Set α}
    (hAmeas : ∀ i, MeasurableSet (A i))
    (hAdisj : Pairwise (Disjoint on A))
    (hAsub : ∀ i, A i ⊆ U) (f : α × α → ℝ≥0∞) :
    (∑' i, ∫⁻ z in A i ×ˢ A i, f z ∂(μ.prod μ)) ≤
      ∫⁻ z in U ×ˢ U, f z ∂(μ.prod μ) := by
  have hprodMeas : ∀ i, MeasurableSet (A i ×ˢ A i) := fun i =>
    (hAmeas i).prod (hAmeas i)
  have hprodDisj : Pairwise (Disjoint on fun i => A i ×ˢ A i) := by
    intro i j hij
    exact Set.disjoint_prod.mpr (Or.inl (hAdisj hij))
  have hprodSub : (⋃ i, A i ×ˢ A i) ⊆ U ×ˢ U := by
    intro z hz
    obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz
    exact ⟨hAsub i hzi.1, hAsub i hzi.2⟩
  rw [← lintegral_iUnion hprodMeas hprodDisj]
  exact lintegral_mono_set hprodSub

end HighContrast
end HCPolySupport
