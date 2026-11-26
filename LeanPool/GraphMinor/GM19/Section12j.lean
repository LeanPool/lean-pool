/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section12i

/-!
# Graph Minors XIX, Section 12: tools for the wheels of (12.4)

Atoms are disjoint (`atom_eq_of_mem`). The set of a walk is connected
(`isPreconnected_walkDrawing_U`). Two vertices of a
closed walk are joined along it by at most half of it (`exists_walk_on_closed_walk`). Each point of
the boundary of a wheel
lies in the atom of a vertex that is next to a vertex of `Γ` on the boundary (`exists_atom_on_bd`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

/-- The set of a walk is connected. -/
theorem isPreconnected_walkDrawing_U {T : Type} [TopologicalSpace T] [T2Space T] {G : Drawing T} {u
  v : T}
    (W : GraphWalk G.toGraph u v) : IsPreconnected (walkDrawing G W).U :=
  GraphWalk.drawing_U_isPreconnected G W

/-- Two vertices of a closed walk are joined by a walk of at most half its length, with its vertices
on the closed walk. -/
theorem exists_walk_on_closed_walk {α' β : Type*} {G : Graph α' β} {u a b : α'}
  (K : GraphWalk G u u) (ha : a ∈ K.support)
    (hb : b ∈ K.support) : ∃ W : GraphWalk G a b, 2 * W.length ≤ K.length := by
  obtain ⟨P, Q, rfl⟩ := K.exists_append_of_mem ha
  have hl : (P.append Q).length = P.length + Q.length := GraphWalk.length_append _ _
  rw [hl]
  have hmin : ∀ {A B : GraphWalk G a b}, A.length + B.length = P.length + Q.length →
      ∃ W : GraphWalk G a b, 2 * W.length ≤ P.length + Q.length := by
    intro A B h
    by_cases hle : A.length ≤ B.length
    · exact ⟨A, by omega⟩
    · exact ⟨B, by omega⟩
  rcases (GraphWalk.mem_support_append P Q).mp hb with h | h
  · obtain ⟨P₁, P₂, rfl⟩ := P.exists_append_of_mem h
    refine hmin (A := P₂.reverse) (B := Q.append P₁) ?_
    rw [GraphWalk.length_reverse, GraphWalk.length_append, GraphWalk.length_append]
    omega
  · obtain ⟨Q₁, Q₂, rfl⟩ := Q.exists_append_of_mem h
    refine hmin (A := Q₁) (B := P.reverse.append Q₂.reverse) ?_
    rw [GraphWalk.length_append, GraphWalk.length_append, GraphWalk.length_reverse,
      GraphWalk.length_reverse]
    omega

namespace TangleDatum

omit [T2Space S] [T2Space Shat] in
/-- Atoms are disjoint or equal. -/
theorem atom_eq_of_mem (D : TangleDatum cap χ) {a b : Set Shat} (ha : a ∈ D.P.Γ.atoms cap)
  (hb : b ∈ D.P.Γ.atoms cap) {p : Shat}
    (hpa : p ∈ a) (hpb : p ∈ b) : a = b := by
  have hinj := cap.isEmbedding.injective
  have hregU : ∀ {r : Set Shat}, r ∈ D.P.Γ.hatRegions cap → p ∈ r → p ∉ D.P.Γ.hatU cap
    := fun hr hp ↦ by
    obtain ⟨x, -, rfl⟩ := hr
    exact connectedComponentIn_subset _ _ hp
  have hUv : ∀ {v : S}, v ∈ D.P.Γ.V → cap.emb v ∈ D.P.Γ.hatU cap := fun hv ↦ mem_image_of_mem _
    (D.P.Γ.V_subset hv)
  have hUe : ∀ {e : Set S}, e ∈ D.P.Γ.E → ∀ {x}, x ∈ e → cap.emb x ∈ D.P.Γ.hatU cap := fun he _ hx ↦
    mem_image_of_mem _ (he.2.1 hx).1
  rcases atom_cases ha with ⟨v, hv, rfl⟩ | ⟨e, he, rfl⟩ | hr <;> rcases atom_cases hb with ⟨v',
    hv', rfl⟩ | ⟨e', he', rfl⟩ | hr'
  · obtain rfl : p = _ := hpa
    have hvv : cap.emb v = cap.emb v' := hpb
    rw [hvv]
  · obtain rfl : p = _ := hpa
    obtain ⟨x, hx, hxe⟩ := hpb
    obtain rfl := hinj hxe
    exact absurd hv ((he'.2.1 hx).2)
  · obtain rfl : p = _ := hpa
    exact absurd (hUv hv) (hregU hr' hpb)
  · obtain rfl : p = _ := hpb
    obtain ⟨x, hx, hxe⟩ := hpa
    obtain rfl := hinj hxe
    exact absurd hv' ((he.2.1 hx).2)
  · obtain ⟨x, hx, rfl⟩ := hpa
    obtain ⟨x', hx', hxe⟩ := hpb
    obtain rfl := hinj hxe
    have hun : IsPathConnected (e ∪ e') := he.2.2.1.union he'.2.2.1 ⟨x', hx, hx'⟩
    have h₁ := he.2.2.2 (e ∪ e') (union_subset he.2.1 he'.2.1) hun subset_union_left
    have h₂ := he'.2.2.2 (e ∪ e') (union_subset he.2.1 he'.2.1) hun subset_union_right
    rw [h₁.symm.trans h₂]
  · obtain ⟨x, hx, rfl⟩ := hpa
    exact absurd (hUe he hx) (hregU hr' hpb)
  · obtain rfl : p = _ := hpb
    exact absurd (hUv hv') (hregU hr hpa)
  · obtain ⟨x, hx, rfl⟩ := hpb
    exact absurd (hUe he' hx) (hregU hr hpa)
  · obtain ⟨x, -, rfl⟩ := hr
    obtain ⟨y, -, rfl⟩ := hr'
    exact (connectedComponentIn_eq hpa).trans (connectedComponentIn_eq hpb).symm

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ}

omit [T2Space S] in
/-- A vertex of a circuit of `Γ*` outside `V(Γ)` has an edge of the circuit, to a vertex of `Γ`. -/
theorem exists_edge_at_Rstar {C : Drawing Shat} (hC : Drawing.IsCircuitOf C D.rad.G) {t : Shat}
  (ht : t ∈ C.V)
    (hth : t ∉ D.P.Γ.hatV cap) : ∃ g ∈ C.E, ∃ v ∈ C.V, v ∈ D.P.Γ.hatV cap ∧ closure g ∩ D.rad.G.V
      = {t, v} := by
  classical
  obtain ⟨b, hb, hbt⟩ : ∃ b ∈ C.V, b ≠ t := by
    obtain ⟨u, W₀, -, hpos, hCV, -⟩ := id hC.2
    cases W₀ with
    | nil h' => simp [GraphWalk.length] at hpos
    | @cons _ x _ e hl r =>
      have huC : u ∈ C.V := by rw [hCV]; exact .head _
      have hxC : x ∈ C.V := by
        rw [hCV]
        exact .tail _ r.start_mem_support
      have hlG : D.rad.G.toGraph.IsLink e u x :=
        ⟨hC.1.2 hl.1, hC.1.1 hl.2.1, hC.1.1 hl.2.2.1, by rw [← hC.1.closure_inter_V hl.1]; exact
          hl.2.2.2⟩
      by_cases hu : u = t
      · refine ⟨x, hxC, fun hxt ↦ ?_⟩
        have hq := hatV_of_not_hatV D hlG.1 hlG.2.2.2 (by rw [hu]; exact hth)
        exact hth (hxt ▸ hq)
      · exact ⟨u, huC, hu⟩
  obtain ⟨P, Q, hP, hQ, hPs, hQs, -, -, -, hdisj, -⟩ := hC.2.exists_two_paths ht hb hbt.symm
  obtain ⟨g₁, hg₁, w₁, hw₁, -, hc₁, -⟩ := first_step (hPs.trans hC.1) hbt.symm hP
  exact ⟨g₁, hPs.2 hg₁, w₁, hPs.1 hw₁, hatV_of_not_hatV D (hC.1.2 (hPs.2 hg₁)) hc₁ hth, hc₁⟩

/-- Each point of the boundary of a wheel lies in the atom of a vertex that equals, or is next to, a
vertex of `Γ` on
the boundary. -/
theorem IsWheelHubOfRadius.exists_atom_on_bd (h : D.IsWheelHubOfRadius W H ρ) {p : Shat}
  (hp : p ∈ discBd W) :
    ∃ v, v ∈ (cap.emb '' D.Γ.V) ∩ discBd W ∧ ∃ w, p ∈ D.rad.atomOf w ∧
      (w ∈ D.rad.G.V) ∧ (w = v ∨ ∃ g, D.rad.G.toGraph.IsLink g v w) := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨F, hFc, hFs, hFU⟩ := exists_circuit_of_oArc h.is_disc.isOArc_discBd h.bd_sub
  have hFG : Drawing.IsCircuitOf F D.rad.G := ⟨hFs, hFc⟩
  have hVb : ∀ {x}, x ∈ F.V → x ∈ discBd W := fun hx ↦ hFU ▸ F.V_subset_U hx
  by_cases hpV : p ∈ F.V
  · by_cases hph : p ∈ D.P.Γ.hatV cap
    · exact ⟨p, ⟨hph, hp⟩, p, D.mem_atomOf (hFs.1 hpV), hFs.1 hpV, .inl rfl⟩
    · obtain ⟨g, hg, v, hv, hvh, hcap⟩ := exists_edge_at_Rstar hFG hpV hph
      refine ⟨v, ⟨hvh, hVb hv⟩, p, D.mem_atomOf (hFs.1 hpV), hFs.1 hpV, .inr ⟨g, hFs.2 hg,
        hFs.1 hv, hFs.1 hpV, ?_⟩⟩
      rw [hcap, pair_comm]
  · rw [← hFU] at hp
    obtain ⟨g, hg, hpg⟩ := F.exists_edge_of_mem hp hpV
    have hgG := hFs.2 hg
    obtain ⟨a, ha, r, hr, hcap⟩ := D.rad.isPreRadial.2.2.2.2.1 g hgG
    have ham : a ∈ closure g ∩ D.rad.G.V := by
      rw [hcap]
      exact .inl rfl
    have hrm : r ∈ closure g ∩ D.rad.G.V := by
      rw [hcap]
      exact .inr rfl
    have haF : a ∈ F.V := ((hFs.closure_inter_V hg).symm ▸ ham : a ∈ closure g ∩ F.V).2
    refine ⟨a, ⟨ha, hVb haF⟩, r, ?_, hr.1, .inr ⟨g, hgG, ham.2, hrm.2, hcap⟩⟩
    rw [atomOf_Rstar D hr]
    exact edge_subset_regionOf D hr hgG hrm.1 hpg

end TangleDatum

end GraphMinor.GM19
