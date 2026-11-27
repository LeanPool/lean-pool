/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.L2ProductVectors
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Totality of actual products of total ℓ² families

A bounded linear map taking a dense spanning family into a closed subspace
takes the whole space into it. Applying this twice to the actual product
bilinear map, followed by the actual coordinate Hilbert basis, proves
product totality without assuming a Hilbert tensor-product equivalence.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open scoped lp

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Closed-subspace membership extends from a dense spanning family along
an actual bounded linear map. -/
theorem continuousLinearMap_mem_of_dense_span {α : Type*} (f : α → E)
    (hf : (Submodule.span ℂ (Set.range f)).topologicalClosure = ⊤)
    (P : Submodule ℂ F) (hP : IsClosed (P : Set F)) (L : E →L[ℂ] F)
    (hL : ∀ a, L (f a) ∈ P) : ∀ x, L x ∈ P := by
  have hspan : Submodule.span ℂ (Set.range f) ≤ P.comap L.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact hL a
  have hclosed : IsClosed ((P.comap L.toLinearMap : Submodule ℂ E) : Set E) :=
    hP.preimage L.continuous
  have h := (Submodule.span ℂ (Set.range f)).topologicalClosure_minimal hspan hclosed
  rw [hf] at h
  exact fun x => h (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ E))

/-- Products of two total families are total in the genuine full ℓ² product
index space. The arbitrary index equivalence permits occupation tuples. -/
theorem l2Product_dense_span {ι κ η α β : Type*} (e : κ ≃ ι × η)
    (f : α → ℓ²(ι, ℂ)) (g : β → ℓ²(η, ℂ))
    (hf : (Submodule.span ℂ (Set.range f)).topologicalClosure = ⊤)
    (hg : (Submodule.span ℂ (Set.range g)).topologicalClosure = ⊤) :
    (Submodule.span ℂ (Set.range (fun p : α × β =>
      l2ProductVector e (f p.1) (g p.2)))).topologicalClosure = ⊤ := by
  classical
  let P := (Submodule.span ℂ (Set.range (fun p : α × β =>
    l2ProductVector e (f p.1) (g p.2)))).topologicalClosure
  have hP : IsClosed (P : Set ℓ²(κ, ℂ)) := Submodule.isClosed_topologicalClosure _
  have hfixed (a : α) : ∀ y, l2ProductVector e (f a) y ∈ P := by
    apply continuousLinearMap_mem_of_dense_span g hg P hP (l2ProductContinuous e (f a))
    intro b
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(a, b), rfl⟩)
  have hall (x : ℓ²(ι, ℂ)) (y : ℓ²(η, ℂ)) : l2ProductVector e x y ∈ P := by
    exact continuousLinearMap_mem_of_dense_span f hf P hP
      ((l2ProductContinuous e).flip y) (fun a => hfixed a y) x
  let b : HilbertBasis κ ℂ ℓ²(κ, ℂ) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hspan : Submodule.span ℂ (Set.range b) ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    change lp.single 2 k (1 : ℂ) ∈ P
    have h := hall (lp.single 2 (e k).1 1) (lp.single 2 (e k).2 1)
    simpa only [l2ProductVector_single, Prod.eta, Equiv.symm_apply_apply] using h
  have h := (Submodule.span ℂ (Set.range b)).topologicalClosure_minimal hspan hP
  rw [b.dense_span] at h
  exact top_unique h

end VacuumBellSeparation.Gaussian
