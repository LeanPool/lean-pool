/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3AlphaReduction
public import LeanPool.GraphMinor.GM12.Section3EmptyClasses
import Mathlib.Data.Fintype.EquivFin

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# The alpha reduction for arbitrary partition families

XII (3.1), page 245, asks for connecting subdrawings for a partition.
The interface also permits empty parts. Enumerate the nonempty parts,
apply the proved alpha reduction to them, then restore the empty parts
with empty subdrawings. The feasibility discs restrict to the same
subfamily, so no extra geometric assumption is needed.
-/

public section

namespace GraphMinor.GM12

open Set Surface

universe u

/-- The final application of VII for XII (3.1), allowing empty parts
in the disjoint family used to state the partition. The hypotheses are
those of the alpha reduction, with no nonemptiness requirement on parts. -/
theorem connecting_subdrawings_of_alpha_bound_allowing_empty
    {S : Type u} [TopologicalSpace S] [T2Space S] {t p : ℕ}
    (hS : IsClosedSurface S) (Γ : Drawing S) (Δ : Fin t → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (havoid : ∀ i, Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i))
    (Zs : Fin p → Set S) (hcover : ⋃ j, Zs j = discBoundaryVertices Γ Δ)
    (hdisZ : ∀ i j, i ≠ j → Disjoint (Zs i) (Zs j))
    (hfeasible : IsTopologicallyFeasible Δ Zs)
    (hbound : ∀ F : Set S, Γ.IsNormal F → IsOArc F → F ⊆ discComplement Δ →
      ∀ D : Set S, IsClosedDisc D → discBd D = F →
      ∀ i, (∀ j, Δ j ⊆ D ↔ j = i) →
        (Γ.V ∩ discBd (Δ i)).ncard ≤ (Γ.V ∩ F).ncard)
    (a b c z : ℕ) (hcomplex : 3 ≤ 3 * a + 3 * b + c)
    (hmodel : Nonempty (discComplement Δ ≃ₜ SurfaceModel a b c))
    (hcount : (discBoundaryVertices Γ Δ).ncard ≤ z)
    (hα : 42 * (z + c + 1) * GM07.vModel a b (c + 1) (z + c + 1) ≤
      GM07.alpha (drawingInSubspace Γ (discComplement Δ)
        (drawing_support_subset_discComplement hS Γ Δ hΔ hdisj havoid))) :
    HasConnectingSubdrawings Γ (discBoundaryVertices Γ Δ) Zs := by
  classical
  let I := {j : Fin p // (Zs j).Nonempty}
  let := Fintype.ofFinite I
  let q := Fintype.card I
  let e : I ≃ Fin q := Fintype.equivFin I
  let f : Fin q → Fin p := fun j => (e.symm j).val
  have hf : Function.Injective f := by
    intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  have hcover' : (⋃ j, Zs (f j)) = discBoundaryVertices Γ Δ := by
    rw [← hcover]
    apply Subset.antisymm
    · intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨f j, hj⟩
    · intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      let k : I := ⟨j, x, hj⟩
      refine mem_iUnion.mpr ⟨e k, ?_⟩
      simpa only [f, e.symm_apply_apply] using hj
  have hfeasible' : IsTopologicallyFeasible Δ (fun j => Zs (f j)) := by
    obtain ⟨D, hD, hDD, hDZ⟩ := hfeasible
    exact ⟨fun j => D (f j), fun j => hD (f j),
      fun i j hij => hDD (f i) (f j) (fun he => hij (hf he)), fun j => hDZ (f j)⟩
  apply hasConnectingSubdrawings_of_nonempty_restriction e
  exact connecting_subdrawings_of_alpha_bound hS Γ Δ hΔ hdisj havoid
    (fun j => Zs (f j)) hcover' (fun j => (e.symm j).property)
    (fun i j hij => hdisZ (f i) (f j) (fun he => hij (hf he)))
    hfeasible' hbound a b c z hcomplex hmodel hcount hα

end GraphMinor.GM12
