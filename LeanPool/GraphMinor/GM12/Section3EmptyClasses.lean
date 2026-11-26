/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM11.Walks

/-!
# Empty classes in the connecting-subdrawing statement

The partition in XII (3.1) and (3.2), pages 245--246, is stated in the
interfaces as a disjoint family whose union is the prescribed vertex
set. Such a family may include empty parts. Prove the connecting result
for its nonempty parts, then assign the empty subdrawing to each empty
part. This also proves the vacuous case with no prescribed vertices.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- The empty subdrawing is connected in the vertex-walk definition
used in the connecting-subdrawing statement. -/
theorem exists_empty_connected_subdrawing
    {S : Type*} [TopologicalSpace S] [T1Space S] (Γ : Drawing S) :
    ∃ H : Drawing S, H.IsSubdrawing Γ ∧ IsConnectedDrawing H ∧ H.V = ∅ := by
  let H := Γ.span ∅ ∅
  have hV : H.V = ∅ := by simp [H, Drawing.span_V, Drawing.spanV]
  refine ⟨H, Γ.span_isSubdrawing _ _, ?_, hV⟩
  intro x hx
  rw [hV] at hx
  exact hx.elim

/-- Connecting the nonempty classes suffices for the conclusion (*)
of XII Section 3. The empty classes receive empty subdrawings. -/
theorem hasConnectingSubdrawings_of_nonempty_classes
    {S : Type*} [TopologicalSpace S] [T1Space S]
    {Γ : Drawing S} {p : ℕ} {Z : Set S} {Zs : Fin p → Set S}
    (H : {j : Fin p // (Zs j).Nonempty} → Drawing S)
    (hsub : ∀ j, (H j).IsSubdrawing Γ)
    (hconn : ∀ j, IsConnectedDrawing (H j))
    (hdis : ∀ i j, i ≠ j → Disjoint (H i).V (H j).V)
    (hboundary : ∀ j, (H j).V ∩ Z = Zs j.val) :
    HasConnectingSubdrawings Γ Z Zs := by
  classical
  obtain ⟨O, hOsub, hOconn, hOV⟩ := exists_empty_connected_subdrawing Γ
  let K : Fin p → Drawing S := fun j => if h : (Zs j).Nonempty then H ⟨j, h⟩ else O
  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · intro j
    dsimp only [K]
    split
    · exact hsub _
    · exact hOsub
  · intro j
    dsimp only [K]
    split
    · exact hconn _
    · exact hOconn
  · intro i j hij
    dsimp only [K]
    split <;> split
    · exact hdis _ _ (fun he => hij (congrArg Subtype.val he))
    · rw [hOV]
      exact disjoint_empty _
    · rw [hOV]
      exact empty_disjoint _
    · rw [hOV]
      exact empty_disjoint _
  · intro j
    dsimp only [K]
    split
    · exact hboundary _
    · rename_i hj
      rw [hOV, empty_inter]
      exact (Set.not_nonempty_iff_eq_empty.mp hj).symm

/-- An enumeration of the nonempty partition parts can be used in
(*) and extended to the original family. -/
theorem hasConnectingSubdrawings_of_nonempty_restriction
    {S : Type*} [TopologicalSpace S] [T1Space S]
    {Γ : Drawing S} {p q : ℕ} {Z : Set S} {Zs : Fin p → Set S}
    (e : {j : Fin p // (Zs j).Nonempty} ≃ Fin q)
    (hc : HasConnectingSubdrawings Γ Z (fun j => Zs (e.symm j).val)) :
    HasConnectingSubdrawings Γ Z Zs := by
  obtain ⟨H, hsub, hconn, hdis, hboundary⟩ := hc
  exact hasConnectingSubdrawings_of_nonempty_classes (fun j => H (e j))
    (fun j => hsub (e j)) (fun j => hconn (e j))
    (fun i j hij => hdis (e i) (e j) (fun he => hij (e.injective he)))
    (fun j => by simpa only [e.symm_apply_apply] using hboundary (e j))

/-- When the prescribed union is empty, empty subdrawings give (*).
This includes the case `t = 0` in XII (3.2), page 247. -/
theorem hasConnectingSubdrawings_of_empty_union
    {S : Type*} [TopologicalSpace S] [T1Space S]
    (Γ : Drawing S) {p : ℕ} (Zs : Fin p → Set S) (hZs : (⋃ j, Zs j) = ∅) :
    HasConnectingSubdrawings Γ ∅ Zs := by
  obtain ⟨O, hsub, hconn, hOV⟩ := exists_empty_connected_subdrawing Γ
  refine ⟨fun _ => O, fun _ => hsub, fun _ => hconn, ?_, ?_⟩
  · intro i j _
    rw [hOV]
    exact empty_disjoint _
  · intro j
    rw [inter_empty]
    apply (Set.eq_empty_iff_forall_notMem.mpr ?_).symm
    intro x hx
    have : x ∈ ⋃ j, Zs j := mem_iUnion.mpr ⟨j, hx⟩
    rw [hZs] at this
    exact this

/-- Graph Minors XII, (3.2), the case of no deleted discs, page 247.
The prescribed boundary union is empty, so every partition part is
empty and the empty subdrawings give the desired conclusion. -/
theorem theorem_3_2_zero_discs
    {S : Type*} [TopologicalSpace S] [T1Space S]
    (Γ : Drawing S) (Δ : Fin 0 → Set S) {p : ℕ} (Zs : Fin p → Set S)
    (hcover : (⋃ j, Zs j) = ⋃ i, Γ.V ∩ subBd (Δ i)) :
    HasConnectingSubdrawings Γ (⋃ i, Γ.V ∩ subBd (Δ i)) Zs := by
  have hZ : (⋃ i, Γ.V ∩ subBd (Δ i)) = ∅ := by simp
  rw [hZ] at hcover ⊢
  exact hasConnectingSubdrawings_of_empty_union Γ Zs hcover

end GraphMinor.GM12
