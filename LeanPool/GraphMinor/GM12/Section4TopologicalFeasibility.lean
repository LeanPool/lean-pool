/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4EndPartition
public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM12.Section4DiscFamilyMatch
import LeanPool.GraphMinor.GM12.Section4FiniteSourceDiscs
import LeanPool.GraphMinor.GM12.Section4FeasibilityTransport

/-!
# Topological feasibility for the oriented target

This proves XII (4.3), claim (7), page 251. Replace the vertices of
the drawn target by disjoint discs and thicken the residual edges.
Match these residual edge discs, including their two ordered marks,
to the prescribed discs. The images of the vertex discs then have
exactly the required contacts with the prescribed end classes.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- XII (4.3), claim (7), page 251: the oriented target drawing
supplies the topological feasibility condition for any disjoint
prescribed edge discs with two boundary marks each. -/
theorem topologicallyFeasible_of_drawn_target
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {p t : ℕ} (L : Graph (Fin p) (Fin t))
    (hV : L.vertexSet = univ) (hE : L.edgeSet = univ) (D : GraphDrawing L S)
    (κ : Fin t × Bool → Fin p)
    (hl : ∀ i, L.IsLink i (κ (i, true)) (κ (i, false)))
    (hne : ∀ i, κ (i, true) ≠ κ (i, false))
    (Δ : Fin t → Set S) (a b : Fin t → S)
    (hΔ : ∀ i, IsClosedDisc (Δ i) ∧ a i ≠ b i ∧ ({a i, b i} : Set S) ⊆ discBd (Δ i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Δ i) (Δ j)) :
    IsTopologicallyFeasible Δ
      (edgeEndClass (fun q : Fin t × Bool => if q.2 then a q.1 else b q.1) κ) := by
  let σV : Fin p ≃ L.vertexSet := {
    toFun := fun v => ⟨v, by rw [hV]; trivial⟩
    invFun := Subtype.val
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let σE : Fin t ≃ L.edgeSet := {
    toFun := fun e => ⟨e, by rw [hE]; trivial⟩
    invFun := Subtype.val
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let ν : Fin p ≃ D.drawing.V := σV.trans D.iso.vertexEquiv
  let ε : Fin t ≃ D.drawing.E := σE.trans D.iso.edgeEquiv
  have hl' : ∀ i, D.drawing.toGraph.IsLink (ε i).val
      (ν (κ (i, true))).val (ν (κ (i, false))).val := by
    intro i
    exact (D.iso.isLink_iff (σE i) (σV (κ (i, true))) (σV (κ (i, false)))).mp (hl i)
  obtain ⟨Δ₀, a₀, b₀, hΔ₀, hdisj₀, hfeas₀⟩ :=
    exists_finite_source_disc_system hS D.drawing ν ε κ hl' hne
  obtain ⟨e, he⟩ := exists_disc_family_match hS Δ₀ Δ
    (fun i => (hΔ₀ i).1) (fun i => (hΔ i).1)
    (fun i j hij => hdisj₀ i j hij) (fun i j hij => hdisj i j hij)
    a₀ b₀ a b (fun i => (hΔ₀ i).2.2 (by simp)) (fun i => (hΔ₀ i).2.2 (by simp))
    (fun i => (hΔ₀ i).2.1) (fun i => (hΔ i).2.2 (by simp))
    (fun i => (hΔ i).2.2 (by simp)) (fun i => (hΔ i).2.1)
  apply topologicallyFeasible_of_homeomorph hfeas₀ e (fun i => (he i).1)
  intro v
  change e '' ((fun q : Fin t × Bool => if q.2 then a₀ q.1 else b₀ q.1) '' {q | κ q = v}) =
    (fun q : Fin t × Bool => if q.2 then a q.1 else b q.1) '' {q | κ q = v}
  rw [image_image]
  apply image_congr
  rintro ⟨i, c⟩ _
  cases c
  · exact (he i).2.2
  · exact (he i).2.1

end GraphMinor.GM12
