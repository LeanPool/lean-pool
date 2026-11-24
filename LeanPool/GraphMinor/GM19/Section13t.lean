/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13s

/-!
# Graph Minors XIX, Section 13: steps (8) to (10) of (13.6)

Two arcs with a common edge are the same. By (13.3) `F` runs along the spokes between its vertices
on them, and that closes up `F` in many cases, which leaves no room for an inner arc.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

omit [T2Space Shat] in
/-- The last edge of a walk with distinct ends. -/
theorem GraphWalk.exists_edge_at_end {G : Drawing Shat} {a b : Shat} (K : GraphWalk G.toGraph a b)
  (hab : a ≠ b) : ∃ e ∈ K.edges, b ∈ closure e := by
  induction K with
  | nil _ => exact absurd rfl hab
  | @cons x y z e hl t ih =>
    by_cases hyz : y = z
    · subst hyz
      exact ⟨e, List.mem_cons_self, TangleDatum.IsLink.right_mem_closure hl⟩
    · obtain ⟨g, hg, hc⟩ := ih hyz
      exact ⟨g, List.mem_cons_of_mem _ hg, hc⟩

omit [T2Space Shat] in
/-- The first edge of a walk with distinct ends. -/
theorem GraphWalk.exists_edge_at_start {G : Drawing Shat} {a b : Shat}
  (K : GraphWalk G.toGraph a b) (hab : a ≠ b) : ∃ e ∈ K.edges, a ∈ closure e := by
  obtain ⟨e, he, hc⟩ := GraphWalk.exists_edge_at_end K.reverse hab.symm
  exact ⟨e, by rwa [GraphWalk.edges_reverse, List.mem_reverse] at he, hc⟩

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {r : Shat} {Δv : Set
  Shat} {Dv F : Drawing Shat}
  {ord' : ℕ} {𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {Δ₀ Δ : Set Shat} {C :
    Drawing Shat} {h : Shat}

omit [T2Space S] in
/-- If an arc shares an edge with `P`, then its first end is on `P`. Otherwise it would enter `P` at
an end of `P`, which is a vertex of `D_v` inside the arc. -/
theorem IsArcOn.start_mem_of_share {a b a' b' : Shat} {P : GraphWalk D.rad.G.toGraph a b} {P' :
  GraphWalk D.rad.G.toGraph a' b'} {R : GraphWalk D.rad.G.toGraph b a}
    (hP : IsArcOn D.rad.G Dv F P) (hP' : IsArcOn D.rad.G Dv F P') (hs : Splits F P R) {e : Set
      Shat} (he : e ∈ P.edges) (he' : e ∈ P'.edges) : a' ∈ P.support := by
  by_contra hn
  obtain ⟨x, y, hl, L, M, hEq⟩ := GraphWalk.exists_split_edge P' he'
  have hx : x ∈ P.support := (D.ends_mem_support P he hl.2.2.2).1
  obtain ⟨w, hw, L₁, L₂, hL, hfirst⟩ := GraphWalk.exists_first_mem L (X
    := {z | z ∈ P.support}) ⟨x, L.end_mem_support, hx⟩
  subst hL
  have hEq' : P' = L₁.append (L₂.append (GraphWalk.cons hl M)) := by
    rw [hEq, GraphWalk.append_assoc']
  have hsim := hEq' ▸ hP'.simple
  have hL₁s : L₁.IsSimple := (isSimple_of_append hsim).1
  have hnea : w ≠ a' := fun h' ↦ hn (h' ▸ hw)
  obtain ⟨z, g, hg, t, hrev⟩ : ∃ (z : Shat) (g : Set Shat) (hg : D.rad.G.toGraph.IsLink g w z)
    (t : GraphWalk D.rad.G.toGraph z a'), L₁.reverse = .cons hg t := by
    cases hR : L₁.reverse with
    | nil _ => exact absurd rfl hnea
    | cons hl t => exact ⟨_, _, hl, t, rfl⟩
  have hgL : g ∈ L₁.edges := by
    have : g ∈ L₁.reverse.edges := by rw [hrev]; exact List.mem_cons_self
    rwa [GraphWalk.edges_reverse, List.mem_reverse] at this
  have hzL : z ∈ L₁.support := by
    have : z ∈ L₁.reverse.support := by rw [hrev]; simp [t.start_mem_support]
    rwa [GraphWalk.support_reverse, List.mem_reverse] at this
  have hzw : z ≠ w := fun h' ↦ by
    have hr := hL₁s.reverse
    rw [hrev] at hr
    exact (List.nodup_cons.mp hr).1 (h' ▸ t.start_mem_support)
  have hzP : z ∉ P.support := fun h' ↦ hzw (hfirst z hzL h')
  have hgP : g ∉ P.edges := fun h' ↦ hzP (D.ends_mem_support P h' hg.2.2.2).2
  have hgP' : g ∈ P'.edges := by
    rw [hEq', GraphWalk.edges_append]
    exact List.mem_append_left _ hgL
  have hgR : g ∈ R.edges := ((hs.E g).mp (hP'.inF g hgP')).resolve_left hgP
  have hwR : w ∈ R.support := (D.ends_mem_support R hgR hg.2.2.2).1
  have hwD : w ∈ Dv.V := by
    rcases hs.meet w hw hwR with rfl | rfl
    · exact hP.left
    · exact hP.right
  have hwP' : w ∈ P'.support := by
    rw [hEq', GraphWalk.mem_support_append]
    exact .inl L₁.end_mem_support
  rcases hP'.inner w hwP' hwD with h' | h'
  · exact hnea h'
  · subst h'
    have hc := GraphWalk.edges_of_closed (L₂.append (GraphWalk.cons hl M))
      (isSimple_of_append hsim).2
    rw [GraphWalk.edges_append] at hc
    simp at hc

omit [T2Space S] in
/-- Two arcs with a common edge have the same edges. -/
theorem IsArcOn.edges_of_share {a b a' b' : Shat} {P : GraphWalk D.rad.G.toGraph a b} {P' :
  GraphWalk D.rad.G.toGraph a' b'} (hF : F.IsCircuitOf D.rad.G)
    (hP : IsArcOn D.rad.G Dv F P) (hP' : IsArcOn D.rad.G Dv F P') {e : Set Shat} (he : e ∈ P.edges)
      (he' : e ∈ P'.edges) : ∀ g ∈ P.edges, g ∈ P'.edges := by
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨W₁, W₂, h₀⟩ := exists_splits hF.2 hF.1 (hP.mem_F hF.1 _ P.start_mem_support)
    (hP.mem_F hF.1 _ P.end_mem_support) hP.ne
  obtain ⟨R, hs⟩ := exists_side_of_walk (D := D) hP.ne hP.simple hP.inF h₀
  have hrev : IsArcOn D.rad.G Dv F P'.reverse := IsArcOn.reverse hP'
  have he'' : e ∈ P'.reverse.edges := by rwa [GraphWalk.edges_reverse, List.mem_reverse]
  have ha' := IsArcOn.start_mem_of_share hP hP' hs he he'
  have hb' := IsArcOn.start_mem_of_share hP hrev hs he he''
  rcases hP.inner a' ha' hP'.left with rfl | rfl <;> rcases hP.inner b' hb' hP'.right with rfl | rfl
  · exact absurd rfl hP'.ne
  · rcases eq_side_of_walk (D := D) hP'.ne hP'.simple hP'.inF hs with rfl | rfl
    · exact fun _ hg ↦ hg
    · rw [GraphWalk.edges_reverse, List.mem_reverse] at he'
      exact absurd he' (hs.edge e he)
  · rcases eq_side_of_walk (D := D) hrev.ne hrev.simple hrev.inF hs with h' | h'
    · intro g hg
      rw [← h', GraphWalk.edges_reverse, List.mem_reverse] at hg
      exact hg
    · rw [h', GraphWalk.edges_reverse, List.mem_reverse] at he''
      exact absurd he'' (hs.edge e he)
  · exact absurd rfl hP'.ne

omit [T2Space S] in
/-- Two arcs that differ in an edge have no common edge. -/
theorem IsArcOn.edges_disjoint {a b a' b' : Shat} {P : GraphWalk D.rad.G.toGraph a b} {P' :
  GraphWalk D.rad.G.toGraph a' b'} (hF : F.IsCircuitOf D.rad.G)
    (hP : IsArcOn D.rad.G Dv F P) (hP' : IsArcOn D.rad.G Dv F P') (hne : ∃ e ∈ P.edges, e ∉
      P'.edges) : ∀ e ∈ P'.edges, e ∉ P.edges := fun e he' he ↦ by
  obtain ⟨g, hg, hg'⟩ := hne
  exact hg' (IsArcOn.edges_of_share hF hP hP' he he' g hg)

variable {v₁ v₂ c₁ c₂ h₁ h₂ : Shat} {f₁ f₂ : Set Shat} {A₁ : GraphWalk D.rad.G.toGraph v₁ c₁} {A₂ :
  GraphWalk D.rad.G.toGraph v₂ c₂} {T₁ : GraphWalk D.rad.G.toGraph c₁ h₁}
  {T₂ : GraphWalk D.rad.G.toGraph c₂ h₂}

/-- By (13.3), `F` includes the part of `A₁` between two of its vertices. -/
theorem IsShape.middle_in_enclave (s : D.IsShape W H r Δv Dv F f₁ f₂ A₁ A₂ T₁ T₂)
  (hE : IsEnclave D.tb D.ord D.𝒯 F) {p q : Shat} {X : GraphWalk D.rad.G.toGraph v₁ p}
    {Y : GraphWalk D.rad.G.toGraph p q} {Z : GraphWalk D.rad.G.toGraph q c₁} (hA : A₁ = X.append
      (Y.append Z)) (hp : p ∈ F.V) (hq : q ∈ F.V) : ∀ e ∈ Y.edges, e ∈ F.E := by
  subst hA
  have heq : (X.append (Y.append Z)).append T₁ = X.append (Y.append (Z.append T₁)) := by
    rw [GraphWalk.append_assoc', GraphWalk.append_assoc']
  refine s.spoke₁.2.subwalk_in_enclave hE (A := X) Y (B := Z.append T₁) (heq ▸ s.spoke₁.1)
    (fun e ↦ ?_) hp hq
  rw [walkDrawing_E, ← heq]
  rfl

/-- The part of `A₁` between two vertices of `F`, in `F`. -/
theorem IsShape.exists_seg (s : D.IsShape W H r Δv Dv F f₁ f₂ A₁ A₂ T₁ T₂)
  (hE : IsEnclave D.tb D.ord D.𝒯 F) {a b : Shat} (ha : a ∈ A₁.support) (hb : b ∈ A₁.support)
    (haF : a ∈ F.V) (hbF : b ∈ F.V) : ∃ Y : GraphWalk D.rad.G.toGraph a b, Y.IsSimple ∧
      (∀ e ∈ Y.edges, e ∈ A₁.edges ∧ e ∈ F.E) ∧ ∀ x ∈ Y.support, x ∈ A₁.support := by
  have hA₁s : A₁.IsSimple := (isSimple_of_append s.spoke₁.1).1
  have key : ∀ {p q : Shat} (X : GraphWalk D.rad.G.toGraph v₁ p) (Y : GraphWalk D.rad.G.toGraph p
    q) (Z : GraphWalk D.rad.G.toGraph q c₁), A₁ = X.append (Y.append Z) →
      p ∈ F.V → q ∈ F.V → Y.IsSimple ∧ (∀ e ∈ Y.edges, e ∈ A₁.edges ∧ e ∈ F.E)
        ∧ ∀ x ∈ Y.support, x ∈ A₁.support := by
    intro p q X Y Z hA hp hq
    refine ⟨?_, fun e he ↦ ⟨?_, s.middle_in_enclave hE hA hp hq e he⟩, fun x hx ↦ ?_⟩
    · rw [hA] at hA₁s
      exact (isSimple_of_append (isSimple_of_append hA₁s).2).1
    · rw [hA, GraphWalk.edges_append, GraphWalk.edges_append]
      exact List.mem_append_right _ (List.mem_append_left _ he)
    · rw [hA, GraphWalk.mem_support_append, GraphWalk.mem_support_append]
      exact .inr (.inl hx)
  obtain ⟨X, Y, hXY⟩ := A₁.exists_append_of_mem ha
  have hbm : b ∈ (X.append Y).support := hXY ▸ hb
  rcases (GraphWalk.mem_support_append _ _).mp hbm with hb' | hb'
  · obtain ⟨X', Y', hX⟩ := X.exists_append_of_mem hb'
    obtain ⟨h₁', h₂', h₃'⟩ := key X' Y' Y (by rw [hXY, hX, GraphWalk.append_assoc']) hbF haF
    refine ⟨Y'.reverse, h₁'.reverse, fun e he ↦ h₂' e ?_, fun x hx ↦ h₃' x ?_⟩
    · rwa [GraphWalk.edges_reverse, List.mem_reverse] at he
    · rwa [GraphWalk.support_reverse, List.mem_reverse] at hx
  · obtain ⟨Y', Z, hY⟩ := Y.exists_append_of_mem hb'
    exact ⟨Y', key X Y' Z (by rw [hXY, hY]) haF hbF⟩

namespace IsFar

/-- If `F` is one simple walk and another walk, with all edges in `D_v` or outside `Δ_v`, then `F`
has no edge inside `Δ_v`, which is false. -/
theorem closing (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h) {a b : Shat} {P : GraphWalk
  D.rad.G.toGraph a b} {J : GraphWalk D.rad.G.toGraph b a} (hab : a ≠ b)
    (hP : P.IsSimple) (hPF : ∀ e ∈ P.edges, e ∈ F.E) (hJF : ∀ e ∈ J.edges, e ∈ F.E)
      (hd : ∀ e ∈ J.edges, e ∉ P.edges)
    (hout : ∀ e, e ∈ P.edges ∨ e ∈ J.edges → e ∈ Dv.E ∨ Disjoint e Δv) : False := by
  obtain ⟨e, he, hin⟩ := hf.exists_edge_in
  have hFi := hf.enc.isInsOf_F
  have hc := circuit_cover hFi.1 hab hP hPF J hJF hd e he
  obtain ⟨x, hx⟩ := (hFi.1.1.2 he).1
  rcases hout e hc with h₁ | h₁
  · have hU : x ∈ Dv.U := Dv.closure_subset_U h₁ (subset_closure hx)
    rw [hf.enc.sector.Dv_U] at hU
    exact (hin hx).2 hU
  · exact disjoint_left.mp h₁ hx (discInt_subset _ (hin hx))

/-- Step (8), second part: no outer arc has both ends on `A₁`. -/
theorem not_both (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h) (s : D.IsShape W H r Δv Dv F f₁ f₂
  A₁ A₂ T₁ T₂) {a b : Shat} {Q : GraphWalk D.rad.G.toGraph a b}
    (hQ : IsArcOn D.rad.G Dv F Q) (ho : ∀ e ∈ Q.edges, Disjoint e Δv) (ha : a ∈ A₁.support)
      (hb : b ∈ A₁.support) : False := by
  have hFs := hf.enc.isInsOf_F.1.1
  obtain ⟨Y, -, hY, -⟩ := s.exists_seg hf.enc.isEnclave hb ha (hQ.mem_F hFs _ Q.end_mem_support)
    (hQ.mem_F hFs _ Q.start_mem_support)
  refine hf.closing hQ.ne hQ.simple hQ.inF (fun e he ↦ (hY e he).2) (fun e he hq ↦ hQ.off e hq
    (s.edge₁ e (hY e he).1)) ?_
  rintro e (he | he)
  · exact .inr (ho e he)
  · exact .inl (s.edge₁ e (hY e he).1)

/-- Each outer arc, in one of its directions, goes from `r*` to `A₁ ∪ A₂` or from `A₁` to `A₂`. -/
theorem normal_form (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h) (s : D.IsShape W H r Δv Dv F f₁
  f₂ A₁ A₂ T₁ T₂) {a b : Shat} {Q : GraphWalk D.rad.G.toGraph a b}
    (hQ : IsArcOn D.rad.G Dv F Q) (ho : ∀ e ∈ Q.edges, Disjoint e Δv) : ∃ (a' b' : Shat)
      (Q' : GraphWalk D.rad.G.toGraph a' b'), IsArcOn D.rad.G Dv F Q' ∧
      (∀ e, e ∈ Q'.edges ↔ e ∈ Q.edges) ∧ (∀ x, x ∈ Q'.support ↔ x ∈ Q.support) ∧
        (∀ L, ¬ PushesInto (Δ₀ \ {h}) (Δv \ {h}) L a b → ¬ PushesInto (Δ₀ \ {h})
          (Δv \ {h}) L a' b') ∧
      ((a' = r ∧ (b' ∈ A₁.support ∨ b' ∈ A₂.support)) ∨ (a' ∈ A₁.support ∧ b' ∈ A₂.support)) := by
  have hrev : IsArcOn D.rad.G Dv F Q.reverse := IsArcOn.reverse hQ
  have hrE : ∀ e, e ∈ Q.reverse.edges ↔ e ∈ Q.edges := fun e ↦ by
    rw [GraphWalk.edges_reverse, List.mem_reverse]
  have ho' : ∀ e ∈ Q.reverse.edges, Disjoint e Δv := fun e he ↦ ho e ((hrE e).mp he)
  have hrS : ∀ x, x ∈ Q.reverse.support ↔ x ∈ Q.support := fun x ↦ by
    rw [GraphWalk.support_reverse, List.mem_reverse]
  have keep : (∀ L, ¬ PushesInto (Δ₀ \ {h}) (Δv \ {h}) L a b → ¬ PushesInto (Δ₀ \ {h})
    (Δv \ {h}) L a b) := fun _ h' ↦ h'
  have flip : (∀ L, ¬ PushesInto (Δ₀ \ {h}) (Δv \ {h}) L a b → ¬ PushesInto (Δ₀ \ {h})
    (Δv \ {h}) L b a) := fun _ h' h'' ↦ h' h''.symm
  rcases s.outer_end hQ ho with ha | ha | ha <;> rcases s.outer_end hrev ho' with hb | hb | hb
  · exact absurd (ha.trans hb.symm) hQ.ne
  · exact ⟨a, b, Q, hQ, fun _ ↦ Iff.rfl, fun _ ↦ Iff.rfl, keep, .inl ⟨ha, .inl hb⟩⟩
  · exact ⟨a, b, Q, hQ, fun _ ↦ Iff.rfl, fun _ ↦ Iff.rfl, keep, .inl ⟨ha, .inr hb⟩⟩
  · exact ⟨b, a, Q.reverse, hrev, hrE, hrS, flip, .inl ⟨hb, .inl ha⟩⟩
  · exact (hf.not_both s hQ ho ha hb).elim
  · exact ⟨a, b, Q, hQ, fun _ ↦ Iff.rfl, fun _ ↦ Iff.rfl, keep, .inr ⟨ha, hb⟩⟩
  · exact ⟨b, a, Q.reverse, hrev, hrE, hrS, flip, .inl ⟨hb, .inr ha⟩⟩
  · exact ⟨b, a, Q.reverse, hrev, hrE, hrS, flip, .inr ⟨hb, ha⟩⟩
  · exact (hf.not_both s.swap hQ ho ha hb).elim

/-- Step (9) of the proof of (13.6): two outer arcs do not both go from `A₁` to `A₂`, since `F`
would then have no inner arc. -/
theorem not_cross (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h) (s : D.IsShape W H r Δv Dv F f₁
  f₂ A₁ A₂ T₁ T₂) {a₀ b₀ a₁ b₁ : Shat} {F₀ : GraphWalk D.rad.G.toGraph a₀ b₀}
    {F₁ : GraphWalk D.rad.G.toGraph a₁ b₁} (h₀ : IsArcOn D.rad.G Dv F F₀)
      (h₁ : IsArcOn D.rad.G Dv F F₁) (o₀ : ∀ e ∈ F₀.edges, Disjoint e Δv)
        (o₁ : ∀ e ∈ F₁.edges, Disjoint e Δv)
    (hd : ∀ e ∈ F₁.edges, e ∉ F₀.edges) (ha₀ : a₀ ∈ A₁.support) (ha₁ : a₁ ∈ A₁.support)
      (hb₀ : b₀ ∈ A₂.support) (hb₁ : b₁ ∈ A₂.support) : False := by
  have hFs := hf.enc.isInsOf_F.1.1
  have hE := hf.enc.isEnclave
  obtain ⟨Y₂, -, hY₂, -⟩ := s.swap.exists_seg hE hb₀ hb₁ (h₀.mem_F hFs _ F₀.end_mem_support)
    (h₁.mem_F hFs _ F₁.end_mem_support)
  obtain ⟨Y₁, -, hY₁, -⟩ := s.exists_seg hE ha₁ ha₀ (h₁.mem_F hFs _ F₁.start_mem_support)
    (h₀.mem_F hFs _ F₀.start_mem_support)
  have hJ : ∀ e, e ∈ (Y₂.append (F₁.reverse.append Y₁)).edges → e ∈ Y₂.edges ∨ e ∈ F₁.edges
    ∨ e ∈ Y₁.edges := fun e he ↦ by
    rwa [GraphWalk.edges_append, List.mem_append, GraphWalk.edges_append, List.mem_append,
      GraphWalk.edges_reverse, List.mem_reverse] at he
  refine hf.closing h₀.ne h₀.simple h₀.inF (J := Y₂.append (F₁.reverse.append Y₁)) (fun e he ↦ ?_)
    (fun e he hq ↦ ?_) ?_
  · rcases hJ e he with h' | h' | h'
    · exact (hY₂ e h').2
    · exact h₁.inF e h'
    · exact (hY₁ e h').2
  · rcases hJ e he with h' | h' | h'
    · exact h₀.off e hq (s.edge₂ e (hY₂ e h').1)
    · exact hd e h' hq
    · exact h₀.off e hq (s.edge₁ e (hY₁ e h').1)
  · rintro e (he | he)
    · exact .inr (o₀ e he)
    · rcases hJ e he with h' | h' | h'
      · exact .inl (s.edge₂ e (hY₂ e h').1)
      · exact .inr (o₁ e h')
      · exact .inl (s.edge₁ e (hY₁ e h').1)

end IsFar

/-- By (13.3), `F` includes the spoke from a vertex on `A₁` to a vertex on the tail. -/
theorem IsShape.tail_part (s : D.IsShape W H r Δv Dv F f₁ f₂ A₁ A₂ T₁ T₂)
  (hE : IsEnclave D.tb D.ord D.𝒯 F) {p x : Shat} {X : GraphWalk D.rad.G.toGraph v₁ p}
    {Y : GraphWalk D.rad.G.toGraph p c₁} (hA : A₁ = X.append Y) {T' : GraphWalk D.rad.G.toGraph c₁
      x} {T'' : GraphWalk D.rad.G.toGraph x h₁} (hT : T₁ = T'.append T'') (hp : p ∈ F.V)
    (hx : x ∈ F.V) : ∀ e ∈ (Y.append T').edges, e ∈ F.E := by
  subst hA hT
  have heq : (X.append Y).append (T'.append T'') = X.append ((Y.append T').append T'') := by
    rw [GraphWalk.append_assoc', GraphWalk.append_assoc']
  refine s.spoke₁.2.subwalk_in_enclave hE (A := X) (Y.append T') (B := T'') (heq ▸ s.spoke₁.1)
    (fun e ↦ ?_) hp hx
  rw [walkDrawing_E, ← heq]
  rfl

namespace IsFar

variable {u : Shat} {A₁' : GraphWalk D.rad.G.toGraph v₁ u} {A₂' : GraphWalk D.rad.G.toGraph v₂ u}
  {T : GraphWalk D.rad.G.toGraph u h₁}

/-- No outer arc among two ends at the common vertex `u` of the spokes. -/
theorem end_ne_common (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h)
  (s : D.IsShape W H r Δv Dv F f₁ f₂ A₁' A₂' T T) {a₀ b₀ a₁ b₁ : Shat} {F₀ : GraphWalk
    D.rad.G.toGraph a₀ b₀}
    {F₁ : GraphWalk D.rad.G.toGraph a₁ b₁} (h₀ : IsArcOn D.rad.G Dv F F₀)
      (h₁' : IsArcOn D.rad.G Dv F F₁) (o₀ : ∀ e ∈ F₀.edges, Disjoint e Δv)
        (o₁ : ∀ e ∈ F₁.edges, Disjoint e Δv)
    (hd : ∀ e ∈ F₁.edges, e ∉ F₀.edges) (n₀ : (a₀ = r ∧ (b₀ ∈ A₁'.support ∨ b₀ ∈ A₂'.support)) ∨
      (a₀ ∈ A₁'.support ∧ b₀ ∈ A₂'.support))
    (n₁ : (a₁ = r ∧ (b₁ ∈ A₁'.support ∨ b₁ ∈ A₂'.support)) ∨ (a₁ ∈ A₁'.support
      ∧ b₁ ∈ A₂'.support)) : a₀ ≠ u ∧ b₀ ≠ u := by
  have hFs := hf.enc.isInsOf_F.1.1
  have hE := hf.enc.isEnclave
  have hW := hf.enc.wheel
  have hu₁ : u ∈ A₁'.support := A₁'.end_mem_support
  have hu₂ : u ∈ A₂'.support := A₂'.end_mem_support
  have hrne : r ≠ u := fun h' ↦ IsWheelHubOfRadius.r_notMem_spoke hW hf.enc.hbdS hf.enc.hin
    ⟨hf.enc.sector.rstar_mem.1, hf.enc.sector.rstar_mem.2⟩ s.spoke₁
    ((GraphWalk.mem_support_append _ _).mpr (.inl (h' ▸ hu₁)))
  rcases n₀ with ⟨ra, hb⟩ | ⟨ha, hb⟩
  · subst ra
    refine ⟨hrne, ?_⟩
    rintro rfl
    have hF₀ : b₀ ∈ F.V := h₀.mem_F hFs _ F₀.end_mem_support
    have hF₁ := h₁'.mem_F hFs _ F₁.end_mem_support
    rcases n₁ with ⟨ra', hb'⟩ | ⟨ha', hb'⟩
    · subst ra'
      have side : ∃ Y : GraphWalk D.rad.G.toGraph b₀ b₁, ∀ e ∈ Y.edges, e ∈ Dv.E ∧ e ∈ F.E := by
        rcases hb' with hb' | hb'
        · obtain ⟨Y, -, hY, -⟩ := s.exists_seg hE hu₁ hb' hF₀ hF₁
          exact ⟨Y, fun e he ↦ ⟨s.edge₁ e (hY e he).1, (hY e he).2⟩⟩
        · obtain ⟨Y, -, hY, -⟩ := s.swap.exists_seg hE hu₂ hb' hF₀ hF₁
          exact ⟨Y, fun e he ↦ ⟨s.edge₂ e (hY e he).1, (hY e he).2⟩⟩
      obtain ⟨Y, hY⟩ := side
      have hJ : ∀ e, e ∈ (Y.append F₁.reverse).edges → e ∈ Y.edges ∨ e ∈ F₁.edges := fun e he ↦ by
        rwa [GraphWalk.edges_append, List.mem_append, GraphWalk.edges_reverse,
          List.mem_reverse] at he
      refine hf.closing h₀.ne h₀.simple h₀.inF (J := Y.append F₁.reverse) (fun e he ↦ ?_)
        (fun e he hq ↦ ?_) ?_
      · rcases hJ e he with h' | h'
        · exact (hY e h').2
        · exact h₁'.inF e h'
      · rcases hJ e he with h' | h'
        · exact h₀.off e hq (hY e h').1
        · exact hd e h' hq
      · rintro e (he | he)
        · exact .inr (o₀ e he)
        · rcases hJ e he with h' | h'
          · exact .inl (hY e h').1
          · exact .inr (o₁ e h')
    · obtain ⟨Y₂, -, hY₂, -⟩ := s.swap.exists_seg hE hb' hu₂ hF₁ hF₀
      obtain ⟨Y₁, -, hY₁, -⟩ := s.exists_seg hE hu₁ ha' hF₀ (h₁'.mem_F hFs _ F₁.start_mem_support)
      have hJ : ∀ e, e ∈ (Y₂.append Y₁).edges → e ∈ Y₂.edges ∨ e ∈ Y₁.edges := fun e he ↦ by
        rwa [GraphWalk.edges_append, List.mem_append] at he
      refine hf.closing h₁'.ne h₁'.simple h₁'.inF (J := Y₂.append Y₁) (fun e he ↦ ?_)
        (fun e he hq ↦ ?_) ?_
      · rcases hJ e he with h' | h'
        · exact (hY₂ e h').2
        · exact (hY₁ e h').2
      · rcases hJ e he with h' | h'
        · exact h₁'.off e hq (s.edge₂ e (hY₂ e h').1)
        · exact h₁'.off e hq (s.edge₁ e (hY₁ e h').1)
      · rintro e (he | he)
        · exact .inr (o₁ e he)
        · rcases hJ e he with h' | h'
          · exact .inl (s.edge₂ e (hY₂ e h').1)
          · exact .inl (s.edge₁ e (hY₁ e h').1)
  · refine ⟨?_, ?_⟩
    · rintro rfl
      exact hf.not_both s.swap h₀ o₀ hu₂ hb
    · rintro rfl
      exact hf.not_both s h₀ o₀ ha hu₁

/-- If two arcs end on `A₁`, away from `u`, then `F` has no vertex further along the spoke, since it
would have three edges at the later end. -/
theorem beyond_ordered (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h)
  (s : D.IsShape W H r Δv Dv F f₁ f₂ A₁' A₂' T T) {p q : Shat} {X : GraphWalk D.rad.G.toGraph v₁ p}
    {Y : GraphWalk D.rad.G.toGraph p q} {Z : GraphWalk D.rad.G.toGraph q u} (hA : A₁' = X.append
      (Y.append Z)) (hpF : p ∈ F.V) (hqF : q ∈ F.V) (hqu : q ≠ u) {g₁ g₂ : Set Shat}
    (hg₁ : g₁ ∈ F.E) (hg₂ : g₂ ∈ F.E) (nd₁ : g₁ ∉ Dv.E) (nd₂ : g₂ ∉ Dv.E) (c₁' : p ∈ closure g₁)
      (c₂' : q ∈ closure g₂) (hne : g₁ ≠ g₂) {x : Shat} (hx : x ∈ T.support)
        (hxF : x ∈ F.V) : False := by
  have : ConnectedSpace Shat := cap.connected
  have hE := hf.enc.isEnclave
  have hFc := hf.enc.isInsOf_F.1
  obtain ⟨T', T'', hT⟩ := T.exists_append_of_mem hx
  have hA' : A₁' = (X.append Y).append Z := by rw [hA, GraphWalk.append_assoc']
  have hZF : ∀ e ∈ (Z.append T').edges, e ∈ F.E := s.tail_part hE hA' hT hqF hxF
  have hYF : ∀ e ∈ Y.edges, e ∈ F.E := s.middle_in_enclave hE hA hpF hqF
  obtain ⟨z₁, hz, hzc⟩ := GraphWalk.exists_edge_at_start Z hqu
  have hzF : z₁ ∈ F.E := hZF z₁ (by rw [GraphWalk.edges_append]; exact List.mem_append_left _ hz)
  have hzD : z₁ ∈ Dv.E := s.edge₁ z₁ (by
    rw [hA, GraphWalk.edges_append, GraphWalk.edges_append]
    exact List.mem_append_right _ (List.mem_append_right _ hz))
  by_cases hpq : p = q
  · subst hpq
    exact no_three_edges hFc D.edge_two_ends hqF hzF hg₁ hg₂ hzc c₁' c₂' (fun h' ↦ nd₁ (h' ▸ hzD))
      (fun h' ↦ nd₂ (h' ▸ hzD)) hne
  · obtain ⟨y₁, hy, hyc⟩ := GraphWalk.exists_edge_at_end Y hpq
    have hyD : y₁ ∈ Dv.E := s.edge₁ y₁ (by
      rw [hA, GraphWalk.edges_append, GraphWalk.edges_append]
      exact List.mem_append_right _ (List.mem_append_left _ hy))
    have hs : (Y.append Z).IsSimple := by
      have := (isSimple_of_append s.spoke₁.1).1
      rw [hA] at this
      exact (isSimple_of_append this).2
    exact no_three_edges hFc D.edge_two_ends hqF (hYF y₁ hy) hzF hg₂ hyc hzc c₂'
      (fun h' ↦ Splits.append_edge hs hy (h' ▸ hz)) (fun h' ↦ nd₂ (h' ▸ hyD)) (fun h' ↦ nd₂
        (h' ▸ hzD))

/-- Either order of the two ends. -/
theorem beyond (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h) (s : D.IsShape W H r Δv Dv F f₁ f₂
  A₁' A₂' T T) {p q : Shat} (hp : p ∈ A₁'.support) (hq : q ∈ A₁'.support)
    (hpF : p ∈ F.V) (hqF : q ∈ F.V) (hpu : p ≠ u) (hqu : q ≠ u) {g₁ g₂ : Set Shat} (hg₁ : g₁ ∈ F.E)
      (hg₂ : g₂ ∈ F.E) (nd₁ : g₁ ∉ Dv.E) (nd₂ : g₂ ∉ Dv.E)
    (c₁' : p ∈ closure g₁) (c₂' : q ∈ closure g₂) (hne : g₁ ≠ g₂) {x : Shat} (hx : x ∈ T.support)
      (hxF : x ∈ F.V) : False := by
  obtain ⟨X, Y, hXY⟩ := A₁'.exists_append_of_mem hp
  have hbm : q ∈ (X.append Y).support := hXY ▸ hq
  rcases (GraphWalk.mem_support_append _ _).mp hbm with hb' | hb'
  · obtain ⟨X', Y', hX⟩ := X.exists_append_of_mem hb'
    exact hf.beyond_ordered s (X := X') (Y := Y') (Z := Y) (by rw [hXY, hX,
      GraphWalk.append_assoc']) hqF hpF hpu hg₂ hg₁ nd₂ nd₁ c₂' c₁' hne.symm hx hxF
  · obtain ⟨Y', Z, hY⟩ := Y.exists_append_of_mem hb'
    exact hf.beyond_ordered s (X := X) (Y := Y') (Z := Z) (by rw [hXY,
      hY]) hpF hqF hqu hg₁ hg₂ nd₁ nd₂ c₁' c₂' hne hx hxF

/-- The case of step (10) where both arcs start at `r*` and end on different sides. -/
theorem two_sides (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h) (s : D.IsShape W H r Δv Dv F f₁
  f₂ A₁' A₂' T T) (hfan : D.IsFan W H ρ r f₁ f₂ A₁' A₂' T) {p q : Shat}
    {F₀ : GraphWalk D.rad.G.toGraph r p} {F₁ : GraphWalk D.rad.G.toGraph r q}
      (h₀ : IsArcOn D.rad.G Dv F F₀) (h₁' : IsArcOn D.rad.G Dv F F₁) (o₀ : ∀ e ∈ F₀.edges, Disjoint
        e Δv)
    (o₁ : ∀ e ∈ F₁.edges, Disjoint e Δv) (hd : ∀ e ∈ F₁.edges, e ∉ F₀.edges) (hp : p ∈ A₁'.support)
      (hq : q ∈ A₂'.support) (hpu : p ≠ u) (hqu : q ≠ u) {x : Shat}
    (hx : x ∈ T.support) (hxF : x ∈ F.V) : False := by
  have : ConnectedSpace Shat := cap.connected
  have hFi := hf.enc.isInsOf_F
  have hFc := hFi.1
  have hFs := hFc.1
  have hE := hf.enc.isEnclave
  have hpF := h₀.mem_F hFs _ F₀.end_mem_support
  have hqF := h₁'.mem_F hFs _ F₁.end_mem_support
  obtain ⟨X₁, Y₁, hA₁⟩ := A₁'.exists_append_of_mem hp
  obtain ⟨X₂, Y₂, hA₂⟩ := A₂'.exists_append_of_mem hq
  obtain ⟨T', T'', hT⟩ := T.exists_append_of_mem hx
  have h₁F : ∀ e ∈ (Y₁.append T').edges, e ∈ F.E := s.tail_part hE hA₁ hT hpF hxF
  have h₂F : ∀ e ∈ (Y₂.append T').edges, e ∈ F.E := s.swap.tail_part hE hA₂ hT hqF hxF
  obtain ⟨e₁, he₁, hc₁⟩ := GraphWalk.exists_edge_at_end Y₁ hpu
  obtain ⟨e₂, he₂, hc₂⟩ := GraphWalk.exists_edge_at_end Y₂ hqu
  have hm₁ : e₁ ∈ A₁'.edges := by
    rw [hA₁, GraphWalk.edges_append]
    exact List.mem_append_right _ he₁
  have hm₂ : e₂ ∈ A₂'.edges := by
    rw [hA₂, GraphWalk.edges_append]
    exact List.mem_append_right _ he₂
  have hF₁ : e₁ ∈ F.E := h₁F e₁ (by rw [GraphWalk.edges_append]; exact List.mem_append_left _ he₁)
  have hF₂ : e₂ ∈ F.E := h₂F e₂ (by rw [GraphWalk.edges_append]; exact List.mem_append_left _ he₂)
  have huF : u ∈ F.V := mem_V_of_mem_U hFs (F.closure_subset_U hF₁ hc₁)
    (Y₁.mem_vertexSet_of_mem_support Y₁.end_mem_support)
  have hxu : x = u := by
    by_contra hne
    obtain ⟨t, ht, htc⟩ := GraphWalk.exists_edge_at_start T' (Ne.symm hne)
    have hmT : t ∈ T.edges := by rw [hT, GraphWalk.edges_append]; exact List.mem_append_left _ ht
    have htF : t ∈ F.E := h₁F t (by
      rw [GraphWalk.edges_append]
      exact List.mem_append_right _ ht)
    exact no_three_edges hFc D.edge_two_ends huF hF₁ hF₂ htF hc₁ hc₂ htc
      (fun h' ↦ hfan.edges_disjoint e₁ hm₁ (h' ▸ hm₂)) (fun h' ↦ hfan.edges_disjoint_T e₁ hm₁
        (h' ▸ hmT)) (fun h' ↦ hfan.swap.edges_disjoint_T e₂ hm₂ (h' ▸ hmT))
  obtain ⟨S₁, -, hS₁, -⟩ := s.exists_seg hE hp A₁'.end_mem_support hpF huF
  obtain ⟨S₂, -, hS₂, -⟩ := s.swap.exists_seg hE A₂'.end_mem_support hq huF hqF
  have hJ : ∀ e, e ∈ (S₁.append (S₂.append F₁.reverse)).edges → e ∈ S₁.edges ∨ e ∈ S₂.edges
    ∨ e ∈ F₁.edges := fun e he ↦ by
    rwa [GraphWalk.edges_append, List.mem_append, GraphWalk.edges_append, List.mem_append,
      GraphWalk.edges_reverse, List.mem_reverse] at he
  refine hf.closing h₀.ne h₀.simple h₀.inF (J := S₁.append (S₂.append F₁.reverse)) (fun e he ↦ ?_)
    (fun e he hq' ↦ ?_) ?_
  · rcases hJ e he with h' | h' | h'
    · exact (hS₁ e h').2
    · exact (hS₂ e h').2
    · exact h₁'.inF e h'
  · rcases hJ e he with h' | h' | h'
    · exact h₀.off e hq' (s.edge₁ e (hS₁ e h').1)
    · exact h₀.off e hq' (s.edge₂ e (hS₂ e h').1)
    · exact hd e h' hq'
  · rintro e (he | he)
    · exact .inr (o₀ e he)
    · rcases hJ e he with h' | h' | h'
      · exact .inl (s.edge₁ e (hS₁ e h').1)
      · exact .inl (s.edge₂ e (hS₂ e h').1)
      · exact .inr (o₁ e h')

/-- Step (10) of the proof of (13.6): `F` has no vertex on the common tail of the two spokes. -/
theorem off_tail (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h) (s : D.IsShape W H r Δv Dv F f₁ f₂
  A₁' A₂' T T) (hfan : D.IsFan W H ρ r f₁ f₂ A₁' A₂' T) {a₀ b₀ a₁ b₁ : Shat}
    {F₀ : GraphWalk D.rad.G.toGraph a₀ b₀} {F₁ : GraphWalk D.rad.G.toGraph a₁ b₁}
      (h₀ : IsArcOn D.rad.G Dv F F₀) (h₁' : IsArcOn D.rad.G Dv F F₁) (o₀ : ∀ e ∈ F₀.edges, Disjoint
        e Δv)
    (o₁ : ∀ e ∈ F₁.edges, Disjoint e Δv) (hd : ∀ e ∈ F₁.edges, e ∉ F₀.edges) (n₀ : (a₀ = r ∧
      (b₀ ∈ A₁'.support ∨ b₀ ∈ A₂'.support)) ∨ (a₀ ∈ A₁'.support ∧ b₀ ∈ A₂'.support))
    (n₁ : (a₁ = r ∧ (b₁ ∈ A₁'.support ∨ b₁ ∈ A₂'.support)) ∨ (a₁ ∈ A₁'.support
      ∧ b₁ ∈ A₂'.support)) {x : Shat} (hx : x ∈ T.support) : x ∉ F.V := by
  intro hxF
  have hFs := hf.enc.isInsOf_F.1.1
  have hd' : ∀ e ∈ F₀.edges, e ∉ F₁.edges := fun e he he' ↦ hd e he' he
  obtain ⟨u₁, u₂⟩ := hf.end_ne_common s h₀ h₁' o₀ o₁ hd n₀ n₁
  obtain ⟨u₃, u₄⟩ := hf.end_ne_common s h₁' h₀ o₁ o₀ hd' n₁ n₀
  obtain ⟨gs₀, hgs₀, cs₀⟩ := GraphWalk.exists_edge_at_start F₀ h₀.ne
  obtain ⟨ge₀, hge₀, ce₀⟩ := GraphWalk.exists_edge_at_end F₀ h₀.ne
  obtain ⟨gs₁, hgs₁, cs₁⟩ := GraphWalk.exists_edge_at_start F₁ h₁'.ne
  obtain ⟨ge₁, hge₁, ce₁⟩ := GraphWalk.exists_edge_at_end F₁ h₁'.ne
  have F₀b := h₀.mem_F hFs _ F₀.end_mem_support
  have F₀a := h₀.mem_F hFs _ F₀.start_mem_support
  have F₁b := h₁'.mem_F hFs _ F₁.end_mem_support
  have F₁a := h₁'.mem_F hFs _ F₁.start_mem_support
  rcases n₀ with ⟨ra, hb | hb⟩ | ⟨ha, hb⟩ <;> rcases n₁ with ⟨ra', hb' | hb'⟩ | ⟨ha', hb'⟩
  · exact hf.beyond s hb hb' F₀b F₁b u₂ u₄ (h₀.inF _ hge₀) (h₁'.inF _ hge₁) (h₀.off _ hge₀)
      (h₁'.off _ hge₁) ce₀ ce₁ (fun h' ↦ hd _ hge₁ (h' ▸ hge₀)) hx hxF
  · subst ra ra'
    exact hf.two_sides s hfan h₀ h₁' o₀ o₁ hd hb hb' u₂ u₄ hx hxF
  · exact hf.beyond s hb ha' F₀b F₁a u₂ u₃ (h₀.inF _ hge₀) (h₁'.inF _ hgs₁) (h₀.off _ hge₀)
      (h₁'.off _ hgs₁) ce₀ cs₁ (fun h' ↦ hd _ hgs₁ (h' ▸ hge₀)) hx hxF
  · subst ra ra'
    exact hf.two_sides s.swap hfan.swap h₀ h₁' o₀ o₁ hd hb hb' u₂ u₄ hx hxF
  · exact hf.beyond s.swap hb hb' F₀b F₁b u₂ u₄ (h₀.inF _ hge₀) (h₁'.inF _ hge₁) (h₀.off _ hge₀)
      (h₁'.off _ hge₁) ce₀ ce₁ (fun h' ↦ hd _ hge₁ (h' ▸ hge₀)) hx hxF
  · exact hf.beyond s.swap hb hb' F₀b F₁b u₂ u₄ (h₀.inF _ hge₀) (h₁'.inF _ hge₁) (h₀.off _ hge₀)
      (h₁'.off _ hge₁) ce₀ ce₁ (fun h' ↦ hd _ hge₁ (h' ▸ hge₀)) hx hxF
  · exact hf.beyond s ha hb' F₀a F₁b u₁ u₄ (h₀.inF _ hgs₀) (h₁'.inF _ hge₁) (h₀.off _ hgs₀)
      (h₁'.off _ hge₁) cs₀ ce₁ (fun h' ↦ hd _ hge₁ (h' ▸ hgs₀)) hx hxF
  · exact hf.beyond s.swap hb hb' F₀b F₁b u₂ u₄ (h₀.inF _ hge₀) (h₁'.inF _ hge₁) (h₀.off _ hge₀)
      (h₁'.off _ hge₁) ce₀ ce₁ (fun h' ↦ hd _ hge₁ (h' ▸ hge₀)) hx hxF
  · exact hf.not_cross s h₀ h₁' o₀ o₁ hd ha ha' hb hb'

end IsFar

end TangleDatum

end GraphMinor.GM19
