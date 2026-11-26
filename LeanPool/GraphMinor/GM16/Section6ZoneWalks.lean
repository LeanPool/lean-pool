/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section6
import LeanPool.GraphMinor.GM16.DrawingConnected
import LeanPool.GraphMinor.GM16.Section9Zones
import LeanPool.GraphMinor.GM14.Section3
import LeanPool.GraphMinor.GM11.OArcCircuit
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM11.Walks

/-!
# Connections inside a zone in XVI (6.3)

A zone boundary is a circuit of the drawing. A drawing path from a
vertex in the closed zone to that circuit can be stopped at its first
boundary vertex, and all its edges up to that point stay in the closed
zone. Paths along the boundary then join any two vertices in the closed
zone. In (6.3), these are the far ends `v(y)`, correcting the printed
occurrence of `Y₄` on page 60.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S]

/-- The closed smaller zone lies inside the larger zone if the latter
contains all atoms at distance less than `lam + 1`. This is the nesting
step in XVI (6.3), page 60. -/
theorem zone_closure_subset_of_atom_neighborhood [ConnectedSpace S]
    {H : Drawing S} {d : Set S → Set S → ℕ} {z Λ₁ Λ : Set S} {lam : ℕ}
    (h₁ : IsLambdaZoneAround H d lam z Λ₁)
    (hΛ : ∀ a ∈ H.A, d z a < lam + 1 → a ⊆ Λ) : closure Λ₁ ⊆ Λ := by
  intro x hx
  obtain ⟨a, ha, hxa⟩ := exists_atom H x
  have hd := h₁.dist_le a ha (zone_atom_subset_closure h₁ ha ⟨x, hxa, hx⟩)
  exact hΛ a ha (by omega) hxa

/-- A walk from the closed zone to its boundary has an initial segment
inside the closed zone ending on the boundary. An edge starting in the
open zone cannot lie in its closed complement. -/
theorem walk_to_zone_boundary
    {H : Drawing S} {d : Set S → Set S → ℕ} {z Λ : Set S} {lam : ℕ}
    (hZone : IsLambdaZoneAround H d lam z Λ) {a b : S} (W : GraphWalk H.toGraph a b) :
    a ∈ closure Λ → b ∈ subBd Λ →
    ∃ c ∈ subBd Λ, Nonempty (GraphWalk (H.interSet (closure Λ)).toGraph a c) := by
  have hSub : (H.interSet (closure Λ)).IsSubdrawing H := H.span_isSubdrawing _ _
  have hmem : ∀ a ∈ H.V, a ∈ closure Λ → a ∈ (H.interSet (closure Λ)).V := by
    intro a ha hcl
    exact Or.inl ⟨⟨ha, hcl⟩, ha⟩
  induction W with
  | @nil a ha =>
    intro hcl hb
    exact ⟨a, hb, ⟨.nil (hmem a ha hcl)⟩⟩
  | @cons a c b e he W ih =>
    intro ha hb
    by_cases habd : a ∈ subBd Λ
    · exact ⟨a, habd, ⟨.nil (hmem a he.2.1 ha)⟩⟩
    have haΛ : a ∈ Λ := by
      rw [(isOpen_disjoint_subBd_and_closure_eq hZone.isOpenDisc.1).2] at ha
      exact ha.resolve_right habd
    have hacl : a ∈ closure e := (he.2.2.2 ▸ mem_insert a {c}).1
    have hccl : c ∈ closure e := (he.2.2.2 ▸ mem_insert_of_mem a (mem_singleton c)).1
    have heΛ : e ⊆ Λ := by
      rcases edge_subset_or_subset_compl_of_zone hZone he.1 with heΛ | heout
      · exact heΛ
      · have hout : closure e ⊆ univ \ Λ := closure_minimal heout
          (by simpa only [← compl_eq_univ_sdiff] using hZone.isOpenDisc.1.isClosed_compl)
        exact False.elim ((hout hacl).2 haΛ)
    have hecl : closure e ⊆ closure Λ := closure_mono heΛ
    obtain ⟨w, hwbd, ⟨W'⟩⟩ := ih (hecl hccl) hb
    have heH' : e ∈ (H.interSet (closure Λ)).E := by
      change e ∈ (H.span _ _).E
      rw [H.span_E]
      exact ⟨⟨he.1, heΛ.trans subset_closure⟩, he.1⟩
    exact ⟨w, hwbd, ⟨.cons ((hSub.isLink_iff heH').mpr he) W'⟩⟩

omit [T2Space S] in
private theorem subdrawing_mem_V_of_mem_U
    {C H : Drawing S} (hCH : C.IsSubdrawing H) {x : S} (hxU : x ∈ C.U) (hxH : x ∈ H.V) :
    x ∈ C.V := by
  rw [C.U_eq] at hxU
  rcases hxU with hx | hx
  · exact hx
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
    have hx : x ∈ closure e ∩ C.V := by
      rw [hCH.closure_inter_V he]
      exact ⟨hxe, hxH⟩
    exact hx.2

omit [T2Space S] in
private theorem circuit_walk_between
    {C : Drawing S} (hC : C.IsCircuit) {a b : S} (ha : a ∈ C.V) (hb : b ∈ C.V) :
    Nonempty (GraphWalk C.toGraph a b) := by
  obtain ⟨u, W, _, _, hV, _⟩ := hC
  rw [hV] at ha hb
  obtain ⟨W₁, _, _⟩ := W.exists_append_of_mem ha
  obtain ⟨W₂, _, _⟩ := W.exists_append_of_mem hb
  exact ⟨W₁.reverse.append W₂⟩

/-- The part of a two-cell drawing in the closed zone is connected.
This supplies the connected subgraph joining the far ends in XVI (6.3),
page 60. The paper prints `Y₄` instead of their far ends at this point. -/
theorem zone_interSet_connected (hS : IsClosedSurface S) [ConnectedSpace S]
    {H : Drawing S} {d : Set S → Set S → ℕ} {z Λ : Set S} {lam : ℕ}
    (hH : (PaintingOrDrawing.drawing H).IsTwoCell)
    (hZone : IsLambdaZoneAround H d lam z Λ) :
    (H.interSet (closure Λ)).IsConnected := by
  obtain ⟨C, hC, hCH, hCU⟩ := exists_circuit_of_oArc hZone.isOArc_bd hZone.bd_subset_U
  obtain ⟨b, W₀, hclosed, hpos, hCV, hCE⟩ := hC
  have hC' : C.IsCircuit := ⟨b, W₀, hclosed, hpos, hCV, hCE⟩
  have hbC : b ∈ C.V := hCV.symm ▸ W₀.start_mem_support
  have hbH : b ∈ H.V := hCH.1 hbC
  have hbbd : b ∈ subBd Λ := hCU ▸ C.V_subset_U hbC
  have hCJ : C.IsSubdrawing (H.interSet (closure Λ)) :=
    subdrawing_interSet_of_U_subset hCH (by rw [hCU]; exact fun _ h => h.1)
  have htoB : ∀ a ∈ (H.interSet (closure Λ)).V,
      Nonempty (GraphWalk (H.interSet (closure Λ)).toGraph a b) := by
    intro a ha
    have haH : a ∈ H.V := (Drawing.span_isSubdrawing H _ _).1 ha
    have hacl : a ∈ closure Λ :=
      interSet_U_subset isClosed_closure ((H.interSet (closure Λ)).V_subset_U ha)
    obtain ⟨W⟩ := drawing_walk_of_twoCell hS hH haH hbH
    obtain ⟨c, hcbd, ⟨W₁⟩⟩ := walk_to_zone_boundary hZone W hacl hbbd
    have hcH : c ∈ H.V := (Drawing.span_isSubdrawing H _ _).1
      (W₁.mem_vertexSet_of_mem_support W₁.end_mem_support)
    have hcC : c ∈ C.V := subdrawing_mem_V_of_mem_U hCH (hCU.symm ▸ hcbd) hcH
    obtain ⟨W₂⟩ := circuit_walk_between hC' hcC hbC
    obtain ⟨W₂', _, _⟩ := hCJ.exists_walk_up W₂
    exact ⟨W₁.append W₂'⟩
  refine ⟨⟨b, hCJ.1 hbC⟩, ?_⟩
  intro a ha b' hb'
  obtain ⟨W₁⟩ := htoB a ha
  obtain ⟨W₂⟩ := htoB b' hb'
  exact ⟨W₁.append W₂.reverse⟩

end GraphMinor.GM16
