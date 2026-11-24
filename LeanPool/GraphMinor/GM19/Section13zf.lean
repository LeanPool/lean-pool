/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13ze

/-!
# Graph Minors XIX, Section 13: the bigon of a fan, and (13.7)

Two spokes that meet, with the edges at `r`, make a bigon. It has no short cut, by (13.1). Then
(13.7) follows from the paths in the disc, since by (13.4) the common part of the spokes is outside
the disc, apart from `u`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM06

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

omit [T2Space Shat] in
theorem GraphWalk.vertexAt_cons {G : Drawing Shat} {a x b : Shat} {e : Set Shat}
  (hl : G.toGraph.IsLink e a x) (t : GraphWalk G.toGraph x b) (p : ℕ) :
    GraphWalk.vertexAt (.cons hl t) (p + 1) = GraphWalk.vertexAt t p := by
  simp [GraphWalk.vertexAt, GraphWalk.support]

omit [T2Space Shat] in
theorem GraphWalk.length_cons' {G : Drawing Shat} {a x b : Shat} {e : Set Shat}
  (hl : G.toGraph.IsLink e a x) (t : GraphWalk G.toGraph x b) : (GraphWalk.cons hl t).length
    = t.length + 1 := by
  simp [GraphWalk.length]

omit [T2Space Shat] in
theorem GraphWalk.meet_of_simple_append {G : Drawing Shat} {a b c : Shat}
  (P : GraphWalk G.toGraph a b) (Q : GraphWalk G.toGraph b c) (hs : (P.append Q).IsSimple) {y :
    Shat}
    (h₁ : y ∈ P.support) (h₂ : y ∈ Q.support) : y = b := by
  by_contra hne
  have hn : (P.support ++ Q.support.tail).Nodup := by
    have h' : (P.append Q).support.Nodup := hs
    rwa [GraphWalk.support_append] at h'
  have hy : y ∈ Q.support.tail := by
    cases Q with
    | nil h =>
      rw [GraphWalk.support_nil, List.mem_singleton] at h₂
      exact (hne h₂).elim
    | cons hl t =>
      rw [GraphWalk.support_cons] at h₂ ⊢
      simpa [hne] using h₂
  exact (List.nodup_append.mp hn).2.2 y h₁ y hy rfl

omit [T2Space Shat] in
/-- A walk splits at each vertex position, with named ends. -/
theorem GraphWalk.exists_split_vertex {G : Drawing Shat} {a b z : Shat}
  (K : GraphWalk G.toGraph a b) {p : ℕ} (hp : p ≤ K.length) (hz : z = GraphWalk.vertexAt K p) :
    ∃ (P : GraphWalk G.toGraph a z) (Q : GraphWalk G.toGraph z b), P.length = p ∧ Q.length + p
      = K.length := by
  subst hz
  obtain ⟨P, Q, h, hl⟩ := GraphWalk.exists_split_at K hp
  refine ⟨P, Q, hl, ?_⟩
  conv_rhs => rw [h, GraphWalk.length_append]
  omega

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {r u h v v₁ v₂ : Shat}
  {f f₁ f₂ : Set Shat} {Δv : Set Shat} {Dv : Drawing Shat}
  {A₁ : GraphWalk D.rad.G.toGraph v₁ u} {A₂ : GraphWalk D.rad.G.toGraph v₂ u} {T : GraphWalk
    D.rad.G.toGraph u h}

omit [T2Space Shat] in
theorem hatV_of_link (hr : r ∈ D.rad.Rstar) (hl : D.rad.G.toGraph.IsLink f r v) : v ∈ D.P.Γ.hatV
  cap := by
  have h₁ := D.even_length_walk (.cons hl (.nil hl.2.2.1))
  have h₂ : ¬ Even (GraphWalk.cons hl (.nil hl.2.2.1)).length := by
    simp [GraphWalk.length, GraphWalk.edges]
  have h₃ : r ∉ D.P.Γ.hatV cap := hr.2
  tauto

/-- The sides of the bigon of a fan. -/
def fanSide (hl₁ : D.rad.G.toGraph.IsLink f₁ r v₁) (hl₂ : D.rad.G.toGraph.IsLink f₂ r v₂)
  (A₁ : GraphWalk D.rad.G.toGraph v₁ u) (A₂ : GraphWalk D.rad.G.toGraph v₂ u) :
    Bool → GraphWalk D.rad.G.toGraph r u
  | false => .cons hl₁ A₁
  | true => .cons hl₂ A₂

theorem IsFan.length_eq (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) :
    A₁.length = A₂.length := by
  have h₁ := hf.hub.spoke_length hf.spoke₁
  have h₂ := hf.hub.spoke_length hf.spoke₂
  rw [GraphWalk.length_append] at h₁ h₂
  have e₁ := D.even_length_walk (A₁.append T)
  have e₂ := D.even_length_walk (A₂.append T)
  have hv₁ := hatV_of_link hf.r_mem hf.link₁
  have hv₂ := hatV_of_link hf.r_mem hf.link₂
  rw [GraphWalk.length_append] at e₁ e₂
  have hev : Even (A₁.length + T.length) ↔ Even (A₂.length + T.length) := by tauto
  rw [Nat.even_iff, Nat.even_iff] at hev
  omega

/-- No walk from a side of the bigon is shorter than the difference of positions. This uses that
spokes are shortest, for a walk starting at `r` with (13.1). -/
theorem IsFan.far_aux (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) (hbdS : discBd W ⊆ cap.emb ''
  (univ \ bd S)) (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty)
    {v v' : Shat} {g g' : Set Shat} {A : GraphWalk D.rad.G.toGraph v u} {A' : GraphWalk
      D.rad.G.toGraph v' u} (hl : D.rad.G.toGraph.IsLink g r v) (hl' : D.rad.G.toGraph.IsLink g' r
        v')
    (hs : D.IsSpokeWalk W H (A.append T)) (hlen : A.length
      = A₁.length) (hlen' : A'.length = A₁.length) {p q : ℕ} (hpq : p ≤ q) (hq : q ≤
        (GraphWalk.cons hl' A').length)
    (K : GraphWalk D.rad.G.toGraph (GraphWalk.vertexAt (.cons hl A) p) (GraphWalk.vertexAt
      (.cons hl' A') q)) : q - p ≤ K.length := by
  have hc' := GraphWalk.length_cons' hl' A'
  obtain ⟨P', Q', hP', hQ'⟩ := GraphWalk.exists_split_vertex (GraphWalk.cons hl' A') hq rfl
  have hW := hf.hub
  have hsl := hW.spoke_length hs
  rw [GraphWalk.length_append] at hsl
  cases p with
  | zero =>
    have e : GraphWalk.vertexAt (GraphWalk.cons hl A) 0 = r := GraphWalk.vertexAt_zero _
    revert K
    rw [e]
    intro K
    have hW₂ := hf.walk_from_r hs.2.h_mem (K.append (Q'.append T))
    rw [GraphWalk.length_append, GraphWalk.length_append] at hW₂
    have e₁ := D.even_length_walk K
    have e₂ := D.even_length_walk P'
    rw [hP'] at e₂
    have hev : Even K.length ↔ Even q := by rw [e₁, e₂]
    rw [Nat.even_iff, Nat.even_iff] at hev
    omega
  | succ p =>
    have hp₀ : p ≤ A.length := by
      have := GraphWalk.length_cons' hl' A'
      omega
    revert K
    rw [GraphWalk.vertexAt_cons]
    intro K
    obtain ⟨P, Q, hP, hQ⟩ := GraphWalk.exists_split_vertex A hp₀ rfl
    have hb := hs.2.v_mem.2
    have := (IsSpokeWalk.le_walk_of_bd hW hbdS hin hs (P.append (K.append
      (Q'.append T))) hl.2.2.1 hb).1
    rw [GraphWalk.length_append, GraphWalk.length_append, GraphWalk.length_append,
      GraphWalk.length_append] at this
    omega

theorem IsFan.isBigon (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) (hbdS : discBd W ⊆ cap.emb ''
  (univ \ bd S)) (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty) :
    D.IsBigon (fanSide hf.link₁ hf.link₂ A₁ A₂) := by
  have hlen := hf.length_eq
  have hr₁ := hf.r_notMem_spoke hf.spoke₁
  have hr₂ := hf.r_notMem_spoke hf.spoke₂
  have hnot : ∀ {v : Shat} {A : GraphWalk D.rad.G.toGraph v u}, r ∉ (A.append T).support
    → r ∉ A.support := fun hn hm ↦ hn ((GraphWalk.mem_support_append _ _).mpr (.inl hm))
  have hsim : ∀ {v g} (hl : D.rad.G.toGraph.IsLink g r v) (A : GraphWalk D.rad.G.toGraph v u),
    (A.append T).IsSimple → r ∉ (A.append T).support → (GraphWalk.cons hl A).IsSimple
      := fun hl A hs hn ↦ by
    have h₁ : A.support.Nodup := (isSimple_of_append hs).1
    change (GraphWalk.cons hl A).support.Nodup
    rw [GraphWalk.support_cons]
    exact List.nodup_cons.mpr ⟨hnot hn, h₁⟩
  refine ⟨hf.r_mem, fun e ↦ hnot hr₁ (e ▸ A₁.end_mem_support), ?_, ?_, ?_, ?_⟩
  · rintro (_ | _)
    · exact hsim _ _ hf.spoke₁.1 hr₁
    · exact hsim _ _ hf.spoke₂.1 hr₂
  · rintro (_ | _) (_ | _) <;> simp [fanSide, hlen]
  · have key : ∀ y, y ∈ (fanSide hf.link₁ hf.link₂ A₁ A₂ false).support → y ∈
      (fanSide hf.link₁ hf.link₂ A₁ A₂ true).support → y = r ∨ y = u := fun y h₁ h₂ ↦ by
      simp only [fanSide, GraphWalk.support_cons, List.mem_cons] at h₁ h₂
      rcases h₁ with h₁ | h₁
      · exact .inl h₁
      rcases h₂ with h₂ | h₂
      · exact .inl h₂
      exact .inr (hf.meet y h₁ h₂)
    rintro (_ | _) (_ | _) hne y h₁ h₂
    · exact absurd rfl hne
    · exact key y h₁ h₂
    · exact key y h₂ h₁
    · exact absurd rfl hne
  · rintro (_ | _) (_ | _) p q hpq hq K
    · exact hf.far_aux hbdS hin hf.link₁ hf.link₁ hf.spoke₁ rfl rfl hpq hq K
    · exact hf.far_aux hbdS hin hf.link₁ hf.link₂ hf.spoke₁ rfl hlen.symm hpq hq K
    · exact hf.far_aux hbdS hin hf.link₂ hf.link₁ hf.spoke₂ hlen.symm rfl hpq hq K
    · exact hf.far_aux hbdS hin hf.link₂ hf.link₂ hf.spoke₂ hlen.symm hlen.symm hpq hq K

/-- The common part of the two spokes is outside the disc, apart from `u`, by (13.4). -/
theorem IsFan.off_disc (hopt : D.IsOptimalWheelHub W H ρ) (hbdS : discBd W ⊆ cap.emb ''
  (univ \ bd S)) (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty)
    (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) (hC : D.IsFanCircuit r f₁ f₂ A₁ A₂ Dv)
      (hs : D.IsBoundarySector W H r Δv Dv) {y : Shat} (hy : y ∈ T.support) (hne : y ≠ u) : y ∉ Δv
        := by
  intro hyΔ
  have hS₁ := hf.spoke₁
  have hS₂ := hf.spoke₂
  have hu₁ : u ∈ (A₁.append T).support := (GraphWalk.mem_support_append _ _).mpr
    (.inl A₁.end_mem_support)
  have hu₂ : u ∈ (A₂.append T).support := (GraphWalk.mem_support_append _ _).mpr
    (.inl A₂.end_mem_support)
  have hQV : (walkDrawing D.rad.G T).V = (walkDrawing D.rad.G (A₁.append T)).V ∩
    (walkDrawing D.rad.G (A₂.append T)).V := by
    ext x
    simp only [walkDrawing_V, mem_inter_iff, mem_ofPred_eq, GraphWalk.mem_support_append]
    constructor
    · exact fun h' ↦ ⟨.inr h', .inr h'⟩
    · rintro ⟨h₁ | h₁, h₂ | h₂⟩
      · exact hf.meet x h₁ h₂ ▸ T.start_mem_support
      · exact h₂
      · exact h₁
      · exact h₁
  have hQE : (walkDrawing D.rad.G T).E = (walkDrawing D.rad.G (A₁.append T)).E ∩
    (walkDrawing D.rad.G (A₂.append T)).E := by
    ext e
    simp only [walkDrawing_E, mem_inter_iff, mem_ofPred_eq, GraphWalk.edges_append, List.mem_append]
    constructor
    · exact fun h' ↦ ⟨.inr h', .inr h'⟩
    · rintro ⟨h₁ | h₁, h₂ | h₂⟩
      · exact absurd h₂ (hf.edges_disjoint e h₁)
      · exact h₂
      · exact h₁
      · exact h₁
  have hsT : T.IsSimple := (isSimple_of_append hS₁.1).2
  have hQ : Drawing.IsPathOf (walkDrawing D.rad.G T) D.rad.G u h := ⟨walkDrawing_isSubdrawing _ _,
    walkDrawing_isPathBetween _ hsT⟩
  have hbd : discBd Δv = ((walkDrawing D.rad.G (A₁.append T)).U ∪ (walkDrawing D.rad.G
    (A₂.append T)).U) \ ((walkDrawing D.rad.G (A₁.append T)).U ∩ (walkDrawing D.rad.G
      (A₂.append T)).U) ∪ {u} ∪ closure f₁ ∪ closure f₂ := by
    rw [hf.formula_eq hC, hs.Dv_U]
  have hl₁ : f₁ ∈ D.rad.G.E ∧ tilde f₁ = {r, v₁} := ⟨hf.link₁.1, by
    rw [← closure_inter_V_eq_tilde hf.link₁.1]
    exact hf.link₁.2.2.2⟩
  have hl₂ : f₂ ∈ D.rad.G.E ∧ tilde f₂ = {r, v₂} := ⟨hf.link₂.1, by
    rw [← closure_inter_V_eq_tilde hf.link₂.1]
    exact hf.link₂.2.2.2⟩
  have h13 := theorem_13_4_proof hopt hbdS hin ⟨hf.r_mem, hf.r_bd⟩ hf.ne hl₁.1 hl₁.2
    hl₂.1 hl₂.2 hS₁.2 hS₂.2
    hQ hQV hQE ⟨u, by rwa [walkDrawing_V], by rwa [walkDrawing_V]⟩ hs.is_disc hs.Δv_sub hbd
  have hyS : y ∈ (A₁.append T).support := (GraphWalk.mem_support_append _ _).mpr (.inr hy)
  have hb : y ∈ discBd Δv := h13.2.2 _ _ _ hS₁.2 ⟨hyΔ, (mem_walkDrawing_U _ _).mpr (.inl hyS)⟩
  rw [hs.Dv_U.symm] at hb
  have hyG : y ∈ D.rad.G.V := T.mem_vertexSet_of_mem_support hy
  rcases (hC.mem_V y).mp (mem_V_of_mem_U hC.circuit.1 hb hyG) with rfl | h₁ | h₂
  · exact hf.r_notMem_spoke hS₁ hyS
  · exact hne (GraphWalk.meet_of_simple_append _ _ hS₁.1 h₁ hy)
  · exact hne (GraphWalk.meet_of_simple_append _ _ hS₂.1 h₂ hy)

omit [T2Space S] in
theorem IsFan.bd_eq_sides (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) (hC : D.IsFanCircuit r f₁ f₂ A₁ A₂
  Dv) (hU : discBd Δv = Dv.U) :
    discBd Δv = ⋃ i, (walkDrawing D.rad.G (fanSide hf.link₁ hf.link₂ A₁ A₂ i)).U := by
  have hside : ∀ {v g} (hl : D.rad.G.toGraph.IsLink g r v) (A : GraphWalk D.rad.G.toGraph v u),
    (walkDrawing D.rad.G (.cons hl A)).U = (walkDrawing D.rad.G A).U ∪ closure g
      := fun {v g} hl A ↦ by
    ext x
    simp only [mem_walkDrawing_U, GraphWalk.support_cons, List.mem_cons, GraphWalk.edges_cons,
      mem_union, exists_eq_or_imp]
    have hr : r ∈ closure g ∩ D.rad.G.V := by rw [hl.2.2.2]; exact .inl rfl
    constructor
    · rintro ((rfl | h₁) | (h₁ | ⟨e, he, hxe⟩))
      · exact .inr hr.1
      · exact .inl (.inl h₁)
      · exact .inr h₁
      · exact .inl (.inr ⟨e, he, hxe⟩)
    · rintro ((h₁ | ⟨e, he, hxe⟩) | h₁)
      · exact .inl (.inr h₁)
      · exact .inr (.inr ⟨e, he, hxe⟩)
      · exact .inr (.inl h₁)
  rw [hU, hf.U_eq hC]
  ext x
  simp only [mem_iUnion, Bool.exists_bool, fanSide, hside, mem_union]
  tauto

/-- **(13.7)**. Let the spokes of `v₁, v₂` meet. The vertices of `Γ` on a spoke are those at even
position. There are mutually disjoint vertex sets `P j`, one for each even position `2 * j` on the
spokes, such
that either the two vertices at that position are the same vertex, on both spokes, and `P j` is this
vertex, or neither is on the other spoke, and `P j` holds a path between them of
`sk(Γ)` in `Δ_v`. -/
theorem IsFan.theorem_13_7_proof (hopt : D.IsOptimalWheelHub W H ρ) (hbdS : discBd W ⊆ cap.emb ''
  (univ \ bd S)) (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty)
    (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) (hC : D.IsFanCircuit r f₁ f₂ A₁ A₂ Dv)
      (hs : D.IsBoundarySector W H r Δv Dv) :
    ∃ (Sk : Drawing Shat) (G : Drawing Δv), D.IsSkPart Δv Sk G ∧ ∃ P : ℕ → Set Shat,
      (∀ j k, 2 * j ≤ (A₁.append T).length → 2 * k ≤ (A₁.append T).length → j ≠ k → Disjoint (P j)
        (P k)) ∧
      ∀ j, 2 * j ≤ (A₁.append T).length →
        (GraphWalk.vertexAt (A₁.append T) (2 * j) = GraphWalk.vertexAt (A₂.append T) (2 * j)
          ∧ GraphWalk.vertexAt (A₁.append T) (2 * j) ∈ (A₁.append T).support ∧
          GraphWalk.vertexAt (A₁.append T) (2 * j) ∈ (A₂.append T).support ∧ P j
            = {GraphWalk.vertexAt (A₁.append T) (2 * j)}) ∨
        (GraphWalk.vertexAt (A₁.append T) (2 * j) ∉ (A₂.append T).support ∧ GraphWalk.vertexAt
          (A₂.append T) (2 * j) ∉ (A₁.append T).support ∧ P j ⊆ Δv ∧
          ∃ a b : Δv, a.1 = GraphWalk.vertexAt (A₁.append T) (2 * j) ∧ b.1 = GraphWalk.vertexAt
            (A₂.append T) (2 * j) ∧
            ∃ K : GraphWalk G.toGraph a b, K.IsSimple ∧ ∀ z ∈ K.support, z.1 ∈ P j) := by
  classical
  have hlen := hf.length_eq
  have hbdU : discBd Δv ⊆ D.rad.G.U := by
    rw [← hs.Dv_U]
    exact hC.circuit.1.U_subset
  obtain ⟨Sk, G, hsk⟩ := D.exists_isSkPart hs.is_disc hbdU
  have hBD : D.IsBigonDisc (fanSide hf.link₁ hf.link₂ A₁ A₂) Δv Sk G := ⟨hf.isBigon hbdS hin, hsk,
    hs.is_disc, hf.bd_eq_sides hC hs.Dv_U.symm⟩
  obtain ⟨Q, hdis, hQ⟩ := hBD.exists_paths
  set L := A₁.length with hL
  have hB : (fanSide hf.link₁ hf.link₂ A₁ A₂ false).length = L + 1 := GraphWalk.length_cons' _ _
  have hn : (A₁.append T).length = L + T.length := GraphWalk.length_append _ _
  have hn₂ : (A₂.append T).length = L + T.length := by rw [GraphWalk.length_append, ← hlen]
  have left₁ : ∀ j, 2 * j ≤ L → GraphWalk.vertexAt (A₁.append T) (2 * j) = GraphWalk.vertexAt
    (fanSide hf.link₁ hf.link₂ A₁ A₂ false) (2 * j + 1) := fun j hj ↦
    (GraphWalk.vertexAt_append_left _ _ hj).trans (GraphWalk.vertexAt_cons _ _ _).symm
  have left₂ : ∀ j, 2 * j ≤ L → GraphWalk.vertexAt (A₂.append T) (2 * j) = GraphWalk.vertexAt
    (fanSide hf.link₁ hf.link₂ A₁ A₂ true) (2 * j + 1) := fun j hj ↦
    (GraphWalk.vertexAt_append_left _ _ (hlen ▸ hj)).trans (GraphWalk.vertexAt_cons _ _ _).symm
  have right₁ : ∀ t, t ≤ T.length → GraphWalk.vertexAt (A₁.append T) (L + t)
    = GraphWalk.vertexAt T t := fun t ht ↦ GraphWalk.vertexAt_append_right _ _ ht
  have right₂ : ∀ t, t ≤ T.length → GraphWalk.vertexAt (A₂.append T) (L + t)
    = GraphWalk.vertexAt T t := fun t ht ↦ by
    rw [hlen]
    exact GraphWalk.vertexAt_append_right _ _ ht
  have hat₁ : GraphWalk.vertexAt (A₁.append T) L = u := GraphWalk.vertexAt_append _ _
  have hother : ∀ {v v' : Shat} (A : GraphWalk D.rad.G.toGraph v u) (A' : GraphWalk D.rad.G.toGraph
    v' u), (A.append T).IsSimple → (A'.append T).IsSimple → A.length = L →
      (∀ y, y ∈ A.support → y ∈ A'.support → y = u) → ∀ j, 2 * j < L → GraphWalk.vertexAt
        (A.append T) (2 * j) ∉ (A'.append T).support := fun {v v'} A A' hs₁ hs₂ hAL hm j hj hmem ↦
          by
    have hx : GraphWalk.vertexAt (A.append T) (2 * j) ∈ A.support := by
      rw [GraphWalk.vertexAt_append_left _ _ (by omega)]
      exact GraphWalk.vertexAt_mem _ (by omega)
    have hu : GraphWalk.vertexAt (A.append T) (2 * j) = u := by
      rcases (GraphWalk.mem_support_append _ _).mp hmem with h' | h'
      · exact hm _ hx h'
      · exact GraphWalk.meet_of_simple_append _ _ hs₁ hx h'
    have he : GraphWalk.vertexAt (A.append T) A.length = u := GraphWalk.vertexAt_append _ _
    have hlA : (A.append T).length = A.length + T.length := GraphWalk.length_append _ _
    have := GraphWalk.vertexAt_inj _ hs₁ (p := 2 * j) (q := A.length) (by omega) (by omega)
      (hu.trans he.symm)
    omega
  have hTj : ∀ j, L ≤ 2 * j → 2 * j ≤ (A₁.append T).length → GraphWalk.vertexAt (A₁.append T)
    (2 * j) ∈ T.support := fun j h₁ h₂ ↦ by
    have e := right₁ (2 * j - L) (by omega)
    rw [show L + (2 * j - L) = 2 * j by omega] at e
    rw [e]
    exact GraphWalk.vertexAt_mem _ (by omega)
  let parts (j : ℕ) : Set Shat :=
    if 2 * j < L then Subtype.val '' Q j else {GraphWalk.vertexAt (A₁.append T) (2 * j)}
  refine ⟨Sk, G, hsk, parts, ?_, fun j hj ↦ ?_⟩
  · have hcross : ∀ j k, 2 * j < L → L ≤ 2 * k → 2 * k ≤ (A₁.append T).length → GraphWalk.vertexAt
      (A₁.append T) (2 * k) ∉ Subtype.val '' Q j := fun j k hj hk hk' ⟨z, hz, e⟩ ↦ by
      have hzT := hTj k hk hk'
      have hzΔ : GraphWalk.vertexAt (A₁.append T) (2 * k) ∈ Δv := e ▸ z.2
      by_cases hu : GraphWalk.vertexAt (A₁.append T) (2 * k) = u
      · have hk2 : 2 * k = L := GraphWalk.vertexAt_inj _ hf.spoke₁.1 hk' (by omega)
          (hu.trans hat₁.symm)
        have hmem : z ∈ block (fanSide hf.link₁ hf.link₂ A₁ A₂) Δv k := by
          refine ⟨false, ?_⟩
          simp only
          rw [e, ← left₁ k (by omega)]
        exact disjoint_left.mp (hdis j k (by omega) (by omega) (by omega)) hz ((hQ k
          (by omega)).1 hmem)
      · exact hf.off_disc hopt hbdS hin hC hs hzT hu hzΔ
    intro j k hj hk hjk
    by_cases h₁ : 2 * j < L <;> by_cases h₂ : 2 * k < L
    · simp only [parts, h₁, h₂, ite_true]
      exact (disjoint_image_iff Subtype.val_injective).mpr (hdis j k (by omega) (by omega) hjk)
    · simp only [parts, h₁, h₂, ite_true, ite_false]
      exact disjoint_singleton_right.mpr (hcross j k h₁ (by omega) hk)
    · simp only [parts, h₁, h₂, ite_true, ite_false]
      exact disjoint_singleton_left.mpr (hcross k j h₂ (by omega) hj)
    · simp only [parts, h₁, h₂, ite_false]
      refine disjoint_singleton.mpr fun e ↦ hjk ?_
      have := GraphWalk.vertexAt_inj _ hf.spoke₁.1 hj hk e
      omega
  · by_cases h₁ : 2 * j < L
    · right
      simp only [parts, h₁, ite_true]
      have hj' : 2 * j + 1 ≤ (fanSide hf.link₁ hf.link₂ A₁ A₂ false).length := by omega
      have m₁ : GraphWalk.vertexAt (A₁.append T) (2 * j) ∈ Δv := by
        rw [left₁ j (by omega)]
        exact Surface.discBd_subset _ (hBD.vertex_mem hj')
      have m₂ : GraphWalk.vertexAt (A₂.append T) (2 * j) ∈ Δv := by
        rw [left₂ j (by omega)]
        exact Surface.discBd_subset _ (hBD.vertex_mem hj')
      have b₁ : (⟨_, m₁⟩ : Δv) ∈ block (fanSide hf.link₁ hf.link₂ A₁ A₂) Δv j := ⟨false, (left₁ j
        (by omega)).symm⟩
      have b₂ : (⟨_, m₂⟩ : Δv) ∈ block (fanSide hf.link₁ hf.link₂ A₁ A₂) Δv j := ⟨true, (left₂ j
        (by omega)).symm⟩
      obtain ⟨K, hKs, hK⟩ := (hQ j hj').2 _ b₁ _ b₂
      refine ⟨hother A₁ A₂ hf.spoke₁.1 hf.spoke₂.1 rfl hf.meet j h₁, hother A₂ A₁ hf.spoke₂.1
        hf.spoke₁.1 hlen.symm (fun y h₂ h₃ ↦ hf.meet y h₃ h₂) j h₁, ?_, _, _, rfl, rfl, K, hKs, fun
          z hz ↦ ⟨z, hK z hz, rfl⟩⟩
      rintro _ ⟨z, -, rfl⟩
      exact z.2
    · left
      simp only [parts, h₁, ite_false, and_true]
      have e₁ := right₁ (2 * j - L) (by omega)
      have e₂ := right₂ (2 * j - L) (by omega)
      rw [show L + (2 * j - L) = 2 * j by omega] at e₁ e₂
      have heq := e₁.trans e₂.symm
      refine ⟨heq, GraphWalk.vertexAt_mem _ hj, ?_⟩
      rw [heq]
      exact GraphWalk.vertexAt_mem _ (by omega)

end TangleDatum

end GraphMinor.GM19
