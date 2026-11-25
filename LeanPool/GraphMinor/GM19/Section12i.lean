/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section12h

import LeanPool.GraphMinor.GM07.Bridge

/-!
# Graph Minors XIX, Section 12: the set around a centre in (12.4)

The proof of (12.4) picks, for each `x ∈ X₂`, a circuit `C_x` and a hub `H_x`, each of which may be
a single vertex. To
treat the cases at once we call a *patch* a circuit with its inside, or a single vertex with the
empty set. `IsCentre`
records what the proof of (12.4) knows about `x`, `y(x)`, `C_x`, `H_x`. `IsCentre.isZoneSet` says
that the union of the
two insides can play the part of `Y` in (12.1), and `IsCentre.exists_wheel` gives the wheel `W_x`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace TangleDatum

/-- `F` is a circuit of `Γ*` of at most `m` edges with `A` its inside, or a single vertex with `A`
empty. -/
def IsPatch (D : TangleDatum cap χ) (F : Drawing Shat) (A : Set Shat) (m : ℕ) : Prop :=
  F.IsSubdrawing D.rad.G ∧ IsPreconnected F.U ∧ F.V.Nonempty ∧
    ((Drawing.IsCircuitOf F D.rad.G ∧ F.E.ncard ≤ m ∧ A = D.ins F) ∨ (A = ∅ ∧ F.E = ∅
      ∧ F.V.Subsingleton))

variable {D : TangleDatum cap χ} {F C H : Drawing Shat} {A B : Set Shat} {m t : ℕ} {x y : Shat}

/-- The set of a circuit is connected. -/
theorem isPreconnected_U_of_isCircuit {T : Type} [TopologicalSpace T] [T2Space T] {F : Drawing T}
  (hF : F.IsCircuit) :
    IsPreconnected F.U := by
  exact (IsCircuit.isOArc_U hF).isPreconnected

omit [T2Space S] in
theorem IsPatch.of_circuit (hF : Drawing.IsCircuitOf F D.rad.G) (hm : F.E.ncard ≤ m) : IsPatch D F
  (D.ins F) m := by
  obtain ⟨u, W, -, -, hV, -⟩ := id hF.2
  exact ⟨hF.1, isPreconnected_U_of_isCircuit hF.2, ⟨u, by rw [hV]; exact W.start_mem_support⟩, .inl
    ⟨hF, hm, rfl⟩⟩

omit [T2Space S] in
/-- Facts on the set of a patch, for `2 m` below the bound of the slope. -/
theorem IsPatch.closed (h : IsPatch D F A m) (hrep : m < 2 * D.rep) : IsClosed A := by
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨-, -, -, ⟨hF, hm, rfl⟩ | ⟨rfl, -⟩⟩ := h
  · exact (ins_facts_of_length (D.isSlope (by omega)) hF.2 hF.1 (show F.length < _ from by
      exact lt_of_le_of_lt hm hrep)).1
  · exact isClosed_empty

omit [T2Space S] in
theorem IsPatch.frontier_subset (h : IsPatch D F A m) (hrep : m < 2 * D.rep) : frontier A ⊆ F.U
  := by
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨-, -, -, ⟨hF, hm, rfl⟩ | ⟨rfl, -⟩⟩ := h
  · exact (ins_facts_of_length (D.isSlope (by omega)) hF.2 hF.1 (show F.length < _ from by
      exact lt_of_le_of_lt hm hrep)).2.1.le
  · simp

omit [T2Space S] in
theorem IsPatch.mem_interior (h : IsPatch D F A m) (hrep : m < 2 * D.rep)
  (hx : x ∈ A \ F.U) : x ∈ interior A := by
  by_contra hn
  exact hx.2 (h.frontier_subset hrep ⟨subset_closure hx.1, hn⟩)

omit [T2Space S] in
theorem IsPatch.region_side (h : IsPatch D F A m) (hrep : m < 2 * D.rep) {q : Set Shat}
  (hq : q ∈ D.rad.G.R)
    (hm : (q ∩ A).Nonempty) : q ⊆ A := by
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨-, -, -, ⟨hF, hle, rfl⟩ | ⟨rfl, -⟩⟩ := h
  · rcases region_subset_or_disjoint (D.isSlope (by omega)) hF.2 hF.1
      (lt_of_le_of_lt hle hrep) hq with h' | h'
    · exact h'
    · obtain ⟨z, h₁, h₂⟩ := hm
      exact absurd h₂ (disjoint_left.mp h' h₁)
  · simp at hm

omit [T2Space S] in
/-- A region of `Γ*` with a point of the interior of a patch in its closure lies in the patch. -/
theorem IsPatch.region_side_of_closure (h : IsPatch D F A m) (hrep : m < 2 * D.rep) {q : Set Shat}
  (hq : q ∈ D.rad.G.R)
    (hx : x ∈ A \ F.U) (hcl : x ∈ closure q) : q ⊆ A := by
  obtain ⟨z, hz₁, hz₂⟩ := mem_closure_iff.mp hcl _ isOpen_interior (h.mem_interior hrep hx)
  exact h.region_side hrep hq ⟨z, hz₂, interior_subset hz₁⟩

omit [T2Space S] in
/-- An edge of `Γ*` that meets a patch lies in it. -/
theorem IsPatch.edge_side (h : IsPatch D F A m) (hrep : m < 2 * D.rep) {g : Set Shat}
  (hg : g ∈ D.rad.G.E)
    (hm : (g ∩ A).Nonempty) : g ⊆ A := by
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨-, -, -, ⟨hF, hle, rfl⟩ | ⟨rfl, -⟩⟩ := h
  · rcases edge_subset_or_disjoint_of_length (D.isSlope (by omega)) hF.2 hF.1
      (lt_of_le_of_lt hle hrep) hg with h' | h'
    · exact h'
    · obtain ⟨z, h₁, h₂⟩ := hm
      exact absurd h₂ (disjoint_left.mp h' h₁)
  · simp at hm

omit [T2Space S] in
/-- An edge of `Γ*` with an end in the interior of a patch lies in it. -/
theorem IsPatch.edge_side_of_closure (h : IsPatch D F A m) (hrep : m < 2 * D.rep) {g : Set Shat}
  (hg : g ∈ D.rad.G.E)
    (hx : x ∈ A \ F.U) (hcl : x ∈ closure g) : g ⊆ A := by
  obtain ⟨z, hz₁, hz₂⟩ := mem_closure_iff.mp hcl _ isOpen_interior (h.mem_interior hrep hx)
  exact h.edge_side hrep hg ⟨z, hz₂, interior_subset hz₁⟩

omit [T2Space S] in
theorem IsPatch.isPreconnected (h : IsPatch D F A m) (hrep : m < 2 * D.rep) : IsPreconnected A := by
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨-, -, -, ⟨hF, hle, rfl⟩ | ⟨rfl, -⟩⟩ := h
  · have hd := (D.isSlope (by omega)).isClosedDisc F hF.2 hF.1 (lt_of_le_of_lt hle hrep)
    exact hd.isPreconnected_discInt.subset_closure sdiff_subset hd.subset_closure_discInt
  · exact isPreconnected_empty

theorem IsPatch.dist_le (h : IsPatch D F A m) (hr : 1 ≤ D.rep) (hrep : m < 2 * D.rep) {a b : Set
  Shat}
    (ha : (a ∩ A).Nonempty) (hb : (b ∩ A).Nonempty) : 2 * D.dist a b ≤ m := by
  obtain ⟨-, -, -, ⟨hF, hle, rfl⟩ | ⟨rfl, -⟩⟩ := h
  · exact (dist_le_of_circuit D hr hF (lt_of_le_of_lt hle hrep) ha hb).trans hle
  · simp at ha

omit [T2Space S] in
theorem IsPatch.U_subset (h : IsPatch D F A m) (hrep : m < 2 * D.rep) (hn : A.Nonempty) : F.U ⊆ A
  := by
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨-, -, -, ⟨hF, hle, rfl⟩ | ⟨rfl, -⟩⟩ := h
  · exact (ins_facts_of_length (D.isSlope (by omega)) hF.2 hF.1 (lt_of_le_of_lt hle hrep)).2.2
  · simp at hn

omit [T2Space S] in
theorem IsPatch.subsingleton_of_empty (h : IsPatch D F A m) (hrep : m < 2 * D.rep) (hA : A
  = ∅) : F.V.Subsingleton := by
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨-, -, ⟨v, hv⟩, ⟨hF, hle, rfl⟩ | ⟨-, -, hs⟩⟩ := h
  · have := (ins_facts_of_length (D.isSlope (by omega)) hF.2 hF.1 (lt_of_le_of_lt hle hrep)).2.2
      (F.V_subset_U hv)
    rw [hA] at this
    exact absurd this (notMem_empty v)
  · exact hs

/-- What the proof of (12.4) knows about a vertex `x`, the vertex `y = y(x)`, `C = C_x`, `H = H_x`.
-/
structure IsCentre (D : TangleDatum cap χ) (t : ℕ) (x y : Shat) (C H : Drawing Shat)
  (A B : Set Shat) : Prop where
  four_le : 4 ≤ t
  x_mem : x ∈ D.rad.G.V
  rep_ge : 25 * t ≤ D.rep
  patchC : IsPatch D C A (2 * t)
  patchH : IsPatch D H B (8 * t + 4)
  y_mem : y ∈ C.V
  x_cases : x ∈ A \ C.U ∨ (A = ∅ ∧ y = x)
  y_cases : y ∈ B \ H.U ∨ (B = ∅ ∧ y ∈ H.V)

namespace IsCentre

variable (h : IsCentre D t x y C H A B)
include h

omit [T2Space S] in
omit [T2Space Shat] in
theorem rep₁ : 2 * t < 2 * D.rep := by
  have := h.four_le
  have := h.rep_ge
  omega

omit [T2Space S] in
omit [T2Space Shat] in
theorem rep₂ : 8 * t + 4 < 2 * D.rep := by
  have := h.four_le
  have := h.rep_ge
  omega

omit [T2Space S] in
omit [T2Space Shat] in
theorem hsub : H.IsSubdrawing D.rad.G := h.patchH.1

omit [T2Space S] in
/-- A vertex of `C` is joined to `y` by a walk of at most `t` edges. -/
theorem exists_walk_C {c : Shat} (hc : c ∈ C.V) : ∃ W : GraphWalk D.rad.G.toGraph c y, W.length ≤ t
  := by
  obtain ⟨hs, -, -, ⟨hF, hm, -⟩ | ⟨-, -, hss⟩⟩ := h.patchC
  · obtain ⟨W, hl, -⟩ := exists_walk_on_circuit hF hc h.y_mem
    exact ⟨W, by omega⟩
  · obtain rfl := hss hc h.y_mem
    exact ⟨.nil (hs.1 hc), Nat.zero_le _⟩

omit [T2Space S] in
/-- A walk to `y` from outside the interior of `H` shows that its start is near `H`. -/
theorem isNear_of_walk {c : Shat} (W : GraphWalk D.rad.G.toGraph c y) (hc : c ∉ B \ H.U) :
    D.IsNear H W.length c := by
  rcases h.y_cases with hy | ⟨-, hy⟩
  · obtain ⟨-, -, -, ⟨hF, hm, rfl⟩ | ⟨rfl, -⟩⟩ := h.patchH
    · have hrep : 1 ≤ D.rep := by
        have hrep_ge := h.rep_ge
        have ht := h.four_le
        omega
      obtain ⟨z, hz, W', hW'⟩ :=
        exists_walk_to_circuit D hrep hF (lt_of_le_of_lt hm h.rep₂) W hc hy
      exact ⟨z, hz, W', hW'⟩
    · exact absurd hy.1 (notMem_empty y)
  · exact ⟨y, hy, W, le_rfl⟩

omit [T2Space S] [T2Space Shat] h in
/-- A vertex within `2t - 2` steps of `H` lies in the zone, as does a vertex of `R*` one step
further. -/
theorem mem_zone {k j : ℕ} {c : Shat} (hN : D.IsNear H j c) (h₁ : c ∈ D.P.Γ.hatV cap → j ≤ k + 1)
  (h₂ : j ≤ k + 2) :
    D.rad.atomOf c ⊆ nearZone D H k := by
  by_cases hx : c ∈ D.P.Γ.hatV cap
  · obtain ⟨v, hv, rfl⟩ := hx
    rw [D.atomOf_emb hv]
    rintro _ rfl
    exact .inl ⟨mem_image_of_mem _ hv, hN.mono (h₁ (mem_image_of_mem _ hv))⟩
  · have hw : c ∈ D.rad.Rstar := ⟨hN.mem_V, hx⟩
    rw [atomOf_Rstar D hw]
    exact fun z hz ↦ .inr (mem_iUnion₂.mpr ⟨c, ⟨hw, hN.mono h₂⟩, hz⟩)

/-- The frontier of the set lies in the zone. -/
theorem frontier_sub {k : ℕ} (hk : k + 3 = 2 * t) : frontier (A ∪ B) ⊆ nearZone D H k := by
  have : ConnectedSpace Shat := cap.connected
  have ht := h.four_le
  have hzH : H.U ⊆ nearZone D H k := subset_nearZone h.hsub
  refine (frontier_union_subset A B).trans (union_subset ?_ ?_)
  · rintro p ⟨hp, hpB⟩
    have hpI : p ∉ interior B := fun hi ↦ by
      rw [closure_compl] at hpB
      exact hpB hi
    have hpB' : p ∉ B \ H.U := fun h' ↦ hpI (h.patchH.mem_interior h.rep₂ h')
    have hpC := h.patchC.frontier_subset h.rep₁ hp
    have hCs := h.patchC.1
    by_cases hpV : p ∈ C.V
    · obtain ⟨W, hW⟩ := h.exists_walk_C hpV
      exact mem_zone ((h.isNear_of_walk W hpB').mono hW) (fun _ ↦ by omega) (by omega)
        (D.mem_atomOf (hCs.1 hpV))
    obtain ⟨g, hg, hpg⟩ := C.exists_edge_of_mem hpC hpV
    by_cases hpB₂ : p ∈ B
    · by_contra hn
      exact hpB' ⟨hpB₂, fun h' ↦ hn (hzH h')⟩
    have hgG := hCs.2 hg
    obtain ⟨a, ha, w, hw, hcap⟩ := D.rad.isPreRadial.2.2.2.2.1 g hgG
    have hwm : w ∈ closure g ∩ D.rad.G.V := by
      rw [hcap]
      exact .inr rfl
    have hwC : w ∈ C.V := by
      have := (hCs.closure_inter_V hg).symm ▸ hwm
      exact this.2
    have hwB : w ∉ B \ H.U := fun h' ↦ hpB₂ (h.patchH.edge_side_of_closure h.rep₂ hgG h' hwm.1 hpg)
    obtain ⟨W, hW⟩ := h.exists_walk_C hwC
    have hN := (h.isNear_of_walk W hwB).mono hW
    have hsub := mem_zone (k := k) hN (fun _ ↦ by omega) (by omega)
    rw [atomOf_Rstar D hw] at hsub
    exact hsub (edge_subset_regionOf D hw hgG hwm.1 hpg)
  · rintro p ⟨-, hp⟩
    exact hzH (h.patchH.frontier_subset h.rep₂ hp)

omit [T2Space S] in
omit [T2Space Shat] in
theorem rep₀ : 4 ≤ D.rep := by
  have := h.four_le
  have := h.rep_ge
  omega

omit [T2Space S] in
omit [T2Space Shat] in
theorem y_G : y ∈ D.rad.G.V := h.patchC.1.1 h.y_mem

/-- The bound between `x` and `y`. -/
theorem dist_x_y : D.dist (D.rad.atomOf x) (D.rad.atomOf y) ≤ t := by
  rcases h.x_cases with hx | ⟨-, rfl⟩
  · have hy := h.patchC.U_subset h.rep₁ ⟨x, hx.1⟩ (C.V_subset_U h.y_mem)
    have := h.patchC.dist_le (by have := h.rep₀; omega) h.rep₁ (a := D.rad.atomOf x) (b
      := D.rad.atomOf y)
      ⟨x, D.mem_atomOf h.x_mem, hx.1⟩ ⟨y, D.mem_atomOf h.y_G, hy⟩
    omega
  · rw [D.dist_self]
    exact Nat.zero_le _

/-- The bound between `y` and a vertex of `H`. -/
theorem dist_h_y {z : Shat} (hz : z ∈ H.V) : D.dist (D.rad.atomOf z) (D.rad.atomOf y) ≤ 4 * t + 2
  := by
  rcases h.y_cases with hy | ⟨hB, hy⟩
  · have hz' := h.patchH.U_subset h.rep₂ ⟨y, hy.1⟩ (H.V_subset_U hz)
    have := h.patchH.dist_le (by have := h.rep₀; omega) h.rep₂ (a := D.rad.atomOf z) (b
      := D.rad.atomOf y)
      ⟨z, D.mem_atomOf (h.hsub.1 hz), hz'⟩ ⟨y, D.mem_atomOf h.y_G, hy.1⟩
    omega
  · obtain rfl := h.patchH.subsingleton_of_empty h.rep₂ hB hz hy
    rw [D.dist_self]
    exact Nat.zero_le _

/-- Two vertices of `H` are close. -/
theorem dist_h_h {z z' : Shat} (hz : z ∈ H.V) (hz' : z' ∈ H.V) :
    D.dist (D.rad.atomOf z) (D.rad.atomOf z') ≤ 4 * t + 2 := by
  by_cases hB : B = ∅
  · obtain rfl := h.patchH.subsingleton_of_empty h.rep₂ hB hz hz'
    rw [D.dist_self]
    exact Nat.zero_le _
  · obtain ⟨b, hb⟩ := nonempty_iff_ne_empty.mpr hB
    have hU := h.patchH.U_subset h.rep₂ ⟨b, hb⟩
    have := h.patchH.dist_le (by have := h.rep₀; omega) h.rep₂ (a := D.rad.atomOf z) (b
      := D.rad.atomOf z')
      ⟨z, D.mem_atomOf (h.hsub.1 hz), hU (H.V_subset_U hz)⟩ ⟨z', D.mem_atomOf (h.hsub.1 hz'), hU
        (H.V_subset_U hz')⟩
    omega

/-- An atom that meets the set of `C ∪ H` is close to a vertex of `H`. -/
theorem dist_h_atom {z : Shat} (hz : z ∈ H.V) {a : Set Shat} (ha : (a ∩ (A ∪ B)).Nonempty) :
    D.dist (D.rad.atomOf z) a ≤ 5 * t + 2 := by
  have hr := h.rep₀
  rcases ha with ⟨p, hpa, hp | hp⟩
  · have hy := h.patchC.U_subset h.rep₁ ⟨p, hp⟩ (C.V_subset_U h.y_mem)
    have h₁ := h.patchC.dist_le (by omega) h.rep₁ (a := D.rad.atomOf y) (b := a)
      ⟨y, D.mem_atomOf h.y_G, hy⟩ ⟨p, hpa, hp⟩
    have h₂ := h.dist_h_y hz
    have h₃ := D.dist_triangle hr (a := D.rad.atomOf z) (c := a) (D.atomOf_mem h.y_G)
    omega
  · have hz' := h.patchH.U_subset h.rep₂ ⟨p, hp⟩ (H.V_subset_U hz)
    have h₁ := h.patchH.dist_le (by omega) h.rep₂ (a := D.rad.atomOf z) (b := a)
      ⟨z, D.mem_atomOf (h.hsub.1 hz), hz'⟩ ⟨p, hpa, hp⟩
    omega

/-- The zone and the two patches together are connected. -/
theorem isPreconnected_union {k : ℕ} : IsPreconnected (nearZone D H k ∪ (A ∪ B)) := by
  have hzone : IsPreconnected (nearZone D H k) := isPreconnected_nearZone h.hsub h.patchH.2.1
    h.patchH.2.2.1
  have hzH : H.U ⊆ nearZone D H k := subset_nearZone h.hsub
  have h₁ : IsPreconnected (nearZone D H k ∪ B) := by
    by_cases hB : B = ∅
    · rw [hB, union_empty]
      exact hzone
    · obtain ⟨b, hb⟩ := nonempty_iff_ne_empty.mpr hB
      obtain ⟨v, hv⟩ := h.patchH.2.2.1
      have hvU := H.V_subset_U hv
      exact hzone.union v (hzH hvU) (h.patchH.U_subset h.rep₂ ⟨b,
        hb⟩ hvU) (h.patchH.isPreconnected h.rep₂)
  have hyz : y ∈ nearZone D H k ∪ B := by
    rcases h.y_cases with hy | ⟨-, hy⟩
    · exact .inr hy.1
    · exact .inl (hzH (H.V_subset_U hy))
  have h₂ : IsPreconnected ((nearZone D H k ∪ B) ∪ A) := by
    by_cases hA : A = ∅
    · rw [hA, union_empty]
      exact h₁
    · obtain ⟨b, hb⟩ := nonempty_iff_ne_empty.mpr hA
      exact h₁.union y hyz (h.patchC.U_subset h.rep₁ ⟨b, hb⟩ (C.V_subset_U h.y_mem))
        (h.patchC.isPreconnected h.rep₁)
  have he : nearZone D H k ∪ (A ∪ B) = (nearZone D H k ∪ B) ∪ A := by
    ext p
    simp only [mem_union]
    tauto
  rw [he]
  exact h₂

/-- The condition at a cuff. If an edge with a vertex on a cuff has a near corner, then the cuff has
pole `x`, by the
distance between the members of `X₂`. So this vertex is next to `x` or on `C`, and the ends of the
edge are near `H`. -/
theorem cuff {k : ℕ} (hk : k + 3 = 2 * t) (hsep : ∀ p ∈ D.rad.poles, p ≠ x
  → 24 * t < D.vDist x p) {q : Set Shat}
    (hq : q ∈ D.rad.G.R) {e : Set S} (he : e ∈ D.P.Γ.E) (heq : cap.emb '' e ⊆ q) (h3 :
      (tilde e).ncard = 3)
    (hb : (closure e ∩ bd S).Nonempty) {w : Shat} (hw : w ∈ D.rad.Rstar) (hN : D.IsNear H (k + 2) w)
    (hm : (q ∩ D.rad.regionOf w).Nonempty) : q ⊆ A ∪ B ∨ ∀ v ∈ tilde e, D.IsNear H (k + 3)
      (cap.emb v) := by
  classical
  have : ConnectedSpace Shat := cap.connected
  have hS := χ.isSurface
  have h3c := D.P.fits.internally_three_connected
  have hr := h.rep₀
  have ht := h.four_le
  have hre := h.rep_ge
  obtain ⟨a, hae, hab⟩ := hb
  have haV : a ∈ tilde e := by
    refine ⟨hae, fun hae' ↦ ?_⟩
    have := (D.P.Γ.border_edge e he ⟨a, hae', hab⟩).1
    omega
  have haG : a ∈ D.P.Γ.V := D.P.Γ.tilde_subset_V he haV
  obtain ⟨Θ, hΘ, haΘ⟩ := mem_sUnion.mp ((sUnion_cuffs (S := S)).symm ▸ hab : a ∈ ⋃₀ cuffs S)
  obtain ⟨p, hp, -, hreg⟩ := D.rad.exists_pole hΘ
  obtain ⟨g, hg, hcap⟩ := D.rad.exists_pole_edge hS h3c hp hΘ hreg haG haΘ
  have hag : cap.emb a ∈ D.rad.G.V := D.rad.isPreRadial.2.1 (mem_image_of_mem _ haG)
  have hlink : D.rad.G.toGraph.IsLink g (cap.emb a) p := ⟨hg, hag, hp.1.1, hcap⟩
  have hacl : cap.emb a ∈ closure q :=
    closure_mono heq (image_closure_subset_closure_image cap.isEmbedding.continuous
      (mem_image_of_mem _ hae))
  by_cases hpx : p = x
  · subst hpx
    have hpcl : p ∈ closure g ∩ D.rad.G.V := by
      rw [hcap]
      exact .inr rfl
    have hacl' : cap.emb a ∈ closure g ∩ D.rad.G.V := by
      rw [hcap]
      exact .inl rfl
    have hwalk : (q ⊆ A ∪ B) ∨ ∃ W : GraphWalk D.rad.G.toGraph (cap.emb a) y, W.length ≤ t := by
      rcases h.x_cases with hx | ⟨-, rfl⟩
      · have hgA := h.patchC.edge_side_of_closure h.rep₁ hg hx hpcl.1
        have haA : cap.emb a ∈ A := closure_minimal hgA (h.patchC.closed h.rep₁) hacl'.1
        by_cases haU : cap.emb a ∈ C.U
        · exact .inr (h.exists_walk_C (mem_V_of_mem_U h.patchC.1 haU hag))
        · exact .inl ((h.patchC.region_side_of_closure h.rep₁ hq ⟨haA,
            haU⟩ hacl).trans subset_union_left)
      · exact .inr ⟨.cons hlink (.nil hp.1.1), by
          rw [GraphWalk.length_cons]
          change 0 + 1 ≤ t
          omega⟩
    rcases hwalk with hsub | ⟨W, hW⟩
    · exact .inl hsub
    by_cases haB : cap.emb a ∈ B \ H.U
    · exact .inl ((h.patchH.region_side_of_closure h.rep₂ hq haB hacl).trans subset_union_right)
    have hNa : D.IsNear H t (cap.emb a) := (h.isNear_of_walk W haB).mono hW
    refine .inr fun v hv ↦ ?_
    by_cases hva : a = v
    · exact hva ▸ hNa.mono (by omega)
    · exact (IsNear.across_side he h3 haV hv hva hNa).mono (by omega)
  · exfalso
    obtain ⟨z, hz, W, hWl⟩ := hN
    have hs := hsep p hp (Ne.symm (Ne.symm hpx))
    change 24 * t < D.dist _ _ at hs
    have d₁ := h.dist_x_y
    have d₂ := h.dist_h_y hz
    rw [D.dist_comm] at d₂
    have d₃ : D.dist (D.rad.atomOf z) (D.rad.atomOf w) ≤ W.length := by
      rw [D.dist_comm]
      exact D.dist_atomOf_le_of_walk W (by omega)
    have d₄ : D.dist (D.rad.atomOf w) (D.rad.atomOf (cap.emb a)) ≤ 3 := by
      rw [atomOf_Rstar D hw]
      exact dist_closure_region_le D hr hq hm ⟨cap.emb a, D.mem_atomOf hag, hacl⟩
    have d₅ : D.dist (D.rad.atomOf (cap.emb a)) (D.rad.atomOf p) ≤ 1 :=
      D.dist_atomOf_le_of_walk (.cons hlink (.nil hp.1.1)) (by
        rw [GraphWalk.length_cons]
        change 0 + 1 < D.rep
        omega)
    have t₁ := D.dist_triangle hr (a := D.rad.atomOf x) (c := D.rad.atomOf p) (D.atomOf_mem h.y_G)
    have t₂ := D.dist_triangle hr (a := D.rad.atomOf y) (c := D.rad.atomOf p) (D.atomOf_mem
      (h.hsub.1 hz))
    have t₃ := D.dist_triangle hr (a := D.rad.atomOf z) (c := D.rad.atomOf p) (D.atomOf_mem hw.1)
    have t₄ := D.dist_triangle hr (a := D.rad.atomOf w) (c := D.rad.atomOf p) (D.atomOf_mem hag)
    omega

/-- The set around the centre can play the part of `Y` in (12.1). -/
theorem isZoneSet {k : ℕ} (hk : k + 3 = 2 * t) (hsep : ∀ p ∈ D.rad.poles, p ≠ x
  → 24 * t < D.vDist x p) :
    IsZoneSet D H k (A ∪ B) where
  closed := (h.patchC.closed h.rep₁).union (h.patchH.closed h.rep₂)
  meet := by
    rintro q hq ⟨p, hp, hA | hB⟩
    · exact (h.patchC.region_side h.rep₁ hq ⟨p, hp, hA⟩).trans subset_union_left
    · exact (h.patchH.region_side h.rep₂ hq ⟨p, hp, hB⟩).trans subset_union_right
  frontier_sub := h.frontier_sub hk
  cuff := fun q hq e he heq h3 hb w hw hN hm ↦ h.cuff hk hsep hq he heq h3 hb hw hN hm

/-- The wheel `W_x` of the proof of (12.4). -/
theorem exists_wheel (hsep : ∀ p ∈ D.rad.poles, p ≠ x → 24 * t < D.vDist x p)
    (hhub : (H.V.ncard = 1 ∧ H.E = ∅ ∧
      ∀ H' : Drawing Shat, IsEnclave D.tb D.ord D.𝒯 H' → H'.E.ncard ≤ 4 * (2 * t) + 4 →
        ¬ (H.V ⊆ D.ins H' \ H'.U)) ∨
      (IsEnclave D.tb D.ord D.𝒯 H ∧ H.E.ncard ≤ 4 * (2 * t) + 4 ∧
      ∀ H' : Drawing Shat, IsEnclave D.tb D.ord D.𝒯 H' → H' ≠ H → H'.E.ncard ≤ 4 * (2 * t) + 4 →
        ¬ (H.U ⊆ D.ins H'))) :
    ∃ W k, k + 3 = 2 * t ∧ D.IsWheelHubOfRadius W H (2 * t) ∧ nearZone D H k ∪
      (A ∪ B) ⊆ W \ discBd W ∧
      ∀ p ∈ W, ∃ a ∈ D.P.Γ.atoms cap, p ∈ a ∧ D.dist (D.rad.atomOf x) a ≤ 11 * t + 13 := by
  have ht := h.four_le
  have hre := h.rep_ge
  have hr := h.rep₀
  obtain ⟨k, hk⟩ : ∃ k, k + 3 = 2 * t := ⟨2 * t - 3, by omega⟩
  obtain ⟨z, hz⟩ := h.patchH.2.2.1
  rw [← hk] at hhub
  obtain ⟨W, hW, hzone, hfar⟩ := GraphMinor.GM19.TangleDatum.exists_wheel (by omega) h.hsub hz
    (h.isZoneSet hk hsep) h.isPreconnected_union
    (fun z' hz' ↦ (h.dist_h_h hz hz').trans (by omega))
    (fun a _ ha ↦ (h.dist_h_atom hz ha).trans (by omega)) hhub
  rw [hk] at hW
  refine ⟨W, k, hk, hW, hzone, fun p hp ↦ ?_⟩
  obtain ⟨a, ha, hpa, hd⟩ := hfar p hp
  refine ⟨a, ha, hpa, ?_⟩
  have d₁ := h.dist_x_y
  have d₂ := h.dist_h_y hz
  rw [D.dist_comm] at d₂
  have t₁ := D.dist_triangle hr (a := D.rad.atomOf x) (c := a) (D.atomOf_mem h.y_G)
  have t₂ := D.dist_triangle hr (a := D.rad.atomOf y) (c := a) (D.atomOf_mem (h.hsub.1 hz))
  omega

end IsCentre

end TangleDatum

end GraphMinor.GM19
