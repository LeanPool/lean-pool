/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3ForestConnections
public import LeanPool.GraphMinor.GM12.Section3EmptyClasses
import Mathlib.Data.Fintype.EquivFin

/-!
# Feasible-forest connections with empty partition parts

The forest form of the VII reduction used in XII (3.1) and (3.2)
permits empty boundary parts. Apply the connection lemma to the
nonempty parts, then restore the empty parts with empty drawings.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM07

/-- A feasible forest realizes its boundary connection classes even
when some partition parts are empty. -/
theorem hasConnectingSubdrawings_of_feasible_forest_allowing_empty
    {S : Type*} [TopologicalSpace S] [T1Space S] {Γ H : Drawing S}
    (hfeasible : IsGFeasible Γ H) {p : ℕ} {Zs : Fin p → Set S}
    (hparts : ∀ j, Zs j ⊆ H.V ∩ bd S)
    (hdis : ∀ i j, i ≠ j → Disjoint (Zs i) (Zs j))
    (hclasses : ∀ j, ∀ x ∈ Zs j, ∀ y ∈ H.V ∩ bd S,
      Nonempty (GraphWalk H.toGraph x y) ↔ y ∈ Zs j) :
    HasConnectingSubdrawings Γ (H.V ∩ bd S) Zs := by
  classical
  let I := {j : Fin p // (Zs j).Nonempty}
  let := Fintype.ofFinite I
  let q := Fintype.card I
  let e : I ≃ Fin q := Fintype.equivFin I
  let f : Fin q → Fin p := fun j => (e.symm j).val
  have hf : Function.Injective f := by
    intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  apply hasConnectingSubdrawings_of_nonempty_restriction e
  exact hasConnectingSubdrawings_of_feasible_forest hfeasible (fun j => hparts (f j))
    (fun j => (e.symm j).property)
    (fun i j hij => hdis (f i) (f j) (fun he => hij (hf he)))
    (fun j => hclasses (f j))

end GraphMinor.GM12
