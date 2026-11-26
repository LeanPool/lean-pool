/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13i

/-!
# Graph Minors XIX, Section 13: two outer arcs that do not push into `Δ'_v`

This is the paragraph of the proof of (13.6) before its step (9). We have a disc `Δ₀`, a point `h ∈
Δ \ U(C)`, and `Y = Δ'_v`
simply-connected. If each arc of `C` is homotopic in `Δ₀ \ {h}` to a curve in `Y`, then `U(C)` is
null-homotopic in `Δ₀ \ {h}`, and
by Graph Minors XI (7.2) it bounds a disc in `Δ₀ \ {h}`, which is false. So some arc is not. Since
`U(F)` is null-homotopic in `Δ₀ \ {h}`
there cannot be just one such arc.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 unitInterval

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

/-- An *arc* of `F` on `D_v` (Graph Minors XIX, proof of (13.6)): a path of `F` with distinct ends
both in `V(D_v)`, with no internal
vertex in `V(D_v)` and no edge in `E(D_v)`. -/
structure IsArcOn (G Dv F : Drawing Shat) {a b : Shat} (P : GraphWalk G.toGraph a b) : Prop where
  ne : a ≠ b
  simple : P.IsSimple
  left : a ∈ Dv.V
  right : b ∈ Dv.V
  inner : ∀ x ∈ P.support, x ∈ Dv.V → x = a ∨ x = b
  off : ∀ e ∈ P.edges, e ∉ Dv.E
  inF : ∀ e ∈ P.edges, e ∈ F.E

/-- There is a path along a simple walk. -/
theorem exists_walk_path (G : Drawing Shat) {a b : Shat}
  (K : GraphWalk G.toGraph a b) (hs : K.IsSimple) :
    ∃ p : Path a b, ∀ t, p t ∈ (walkDrawing G K).U := by
  by_cases hab : a = b
  · subst hab
    refine ⟨Path.refl a, fun t ↦ ?_⟩
    exact (walkDrawing G K).V_subset_U (by rw [walkDrawing_V]; exact K.start_mem_support)
  · exact IsLineWithEnds.exists_path (isLine_of_isPathBetween (walkDrawing_isPathBetween G hs) hab)

/-- Two discs in a third disc with the same boundary are equal. -/
theorem disc_eq_of_subset_disc {T : Type} [TopologicalSpace T] [ConnectedSpace T]
  (hT : IsClosedSurface T) {Δ₀ Δ₁ Δ₂ : Set T} (h₀ : IsClosedDisc Δ₀)
    (h₁ : IsClosedDisc Δ₁) (h₂ : IsClosedDisc Δ₂) (s₁ : Δ₁ ⊆ Δ₀) (s₂ : Δ₂ ⊆ Δ₀) (hb : discBd Δ₁
      = discBd Δ₂) : Δ₁ = Δ₂ := by
  by_contra hne
  have hcov := cover_of_discBd_eq hT h₁ h₂ hb hne
  have hu : Δ₀ = univ := eq_univ_of_univ_subset (hcov ▸ union_subset s₁ s₂)
  have hf := IsClosedDisc.frontier_eq_discBd hT h₀
  rw [hu, frontier_univ] at hf
  have hne' : (discBd Δ₀).Nonempty := by
    obtain ⟨e⟩ := h₀.isOArc_discBd
    exact ⟨_, (e 1).2⟩
  rw [hu, ← hf] at hne'
  exact not_nonempty_empty hne'

/-- All the edges of a simple walk that starts on one of two walks, and is on an edge of one or the
other, stay on that one. -/
theorem walk_stays {α' β : Type*} {G : Graph α' β} {s t a₁ b₁ a₂ b₂ : α'} (K : GraphWalk G s t)
  (hs : K.IsSimple)
    (W₁ : GraphWalk G a₁ b₁) (W₂ : GraphWalk G a₂ b₂) (hE : ∀ e ∈ K.edges, e ∈ W₁.edges
      ∨ e ∈ W₂.edges)
    (hV : ∀ x ∈ K.support, x ∈ W₁.support → x ∈ W₂.support → x = t) (hst : s ∈ W₁.support)
    (hside : ∀ {e x y}, G.IsLink e x y → e ∈ W₁.edges → x ∈ W₁.support → y ∈ W₁.support)
    (hside₂ : ∀ {e x y}, G.IsLink e x y → e ∈ W₂.edges → x ∈ W₂.support) : ∀ e ∈ K.edges, e ∈
      W₁.edges := by
  induction K with
  | nil h => simp
  | @cons a c b e hl r ih =>
    have hnd : (GraphWalk.cons hl r).support.Nodup := hs
    simp only [GraphWalk.support_cons, List.nodup_cons] at hnd
    have he : e ∈ W₁.edges := by
      rcases hE e (by simp) with h | h
      · exact h
      · have ha := hV a (by simp) hst (hside₂ hl h)
        subst ha
        exact absurd r.end_mem_support hnd.1
    have hc := hside hl he hst
    have ih' := ih hnd.2 (fun f hf ↦ hE f (by simp [hf])) (fun x hx ↦ hV x (by simp [hx])) hc
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf'
    · exact he
    · exact ih' f hf'

namespace TangleDatum

variable {D : TangleDatum cap χ} {F Dv C : Drawing Shat}

omit [T2Space S] in
theorem mem_V_of_link_edge {H : Drawing Shat} (hH : H.IsSubdrawing D.rad.G) {a b : Shat} {K :
  GraphWalk D.rad.G.toGraph a b} {e : Set Shat} (he : e ∈ K.edges) (heH : e ∈ H.E) :
    ∃ x y, x ≠ y ∧ x ∈ K.support ∧ y ∈ K.support ∧ x ∈ H.V ∧ y ∈ H.V := by
  obtain ⟨x, y, hne, hx, hy, hcap⟩ := exists_ends_of_mem_edges D K he
  have hxm : x ∈ closure e ∩ D.rad.G.V := by rw [hcap]; exact .inl rfl
  have hym : y ∈ closure e ∩ D.rad.G.V := by rw [hcap]; exact .inr rfl
  have hl : D.rad.G.toGraph.IsLink e x y := ⟨TieBreaker.mem_edges_E K he, hxm.2, hym.2, hcap⟩
  have := Drawing.IsLink.mem_V_of_sub hH hl heH
  exact ⟨x, y, hne, hx, hy, this.1, this.2⟩

omit [T2Space S] in
/-- **Pushing a walk.** Let `K` be a simple walk of `F ∪ D_v` with ends on `D_v`, in `Z`. If each
arc in `K` pushes into `Y`, then
so does `K`. -/
theorem walk_pushes (hDv : Dv.IsSubdrawing D.rad.G) {Z Y : Set Shat} (hY : ∀ x ∈ Dv.U, x ∈ Z
  → x ∈ Y) (n : ℕ) :
    ∀ {a b : Shat} (K : GraphWalk D.rad.G.toGraph a b), K.length = n → K.IsSimple → a ∈ Dv.V
      → b ∈ Dv.V →
      (∀ e ∈ K.edges, e ∈ Dv.E ∨ e ∈ F.E) → (walkDrawing D.rad.G K).U ⊆ Z →
      (∀ (u v : Shat) (M : GraphWalk D.rad.G.toGraph u v), IsArcOn D.rad.G Dv F M →
        (∀ e ∈ M.edges, e ∈ K.edges) →
        PushesInto Z Y (walkDrawing D.rad.G M).U u v) →
      PushesInto Z Y (walkDrawing D.rad.G K).U a b := by
  classical
  have : ConnectedSpace Shat := cap.connected
  set G := D.rad.G with hG
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b K hn hs ha hb hKe hKZ harc
    cases K with
    | nil hv =>
      refine PushesInto.of_subset fun x hx ↦ hY x ?_ (hKZ hx)
      have hx' := (point_drawing_facts G hv).2.2 ▸ hx
      rw [mem_singleton_iff.mp hx']
      exact Dv.V_subset_U ha
    | @cons a y b e hl r =>
      obtain ⟨u, huX, A, B, rfl, hA⟩ := GraphWalk.exists_first_mem r (X
        := Dv.V) ⟨b, r.end_mem_support, hb⟩
      have hsK : (GraphWalk.cons hl (A.append B)).IsSimple := hs
      have hsplit : GraphWalk.cons hl (A.append B) = (GraphWalk.cons hl A).append B := rfl
      have hnd : (GraphWalk.cons hl (A.append B)).support.Nodup := hsK
      simp only [GraphWalk.support_cons, List.nodup_cons] at hnd
      have hab : a ≠ b := fun h ↦ hnd.1 (h ▸ (A.append B).end_mem_support)
      have hau : a ≠ u := fun h ↦ hnd.1 (h ▸ (GraphWalk.mem_support_append A B).mpr
        (.inr B.start_mem_support))
      have hlen : B.length < n := by
        have h₁ : (GraphWalk.cons hl (A.append B)).length = (A.append B).length + 1 := rfl
        rw [GraphWalk.length_append] at h₁
        omega
      rw [hsplit] at hsK hKZ hKe harc ⊢
      obtain ⟨hsM, hsB⟩ := GraphMinor.GM19.GraphWalk.IsSimple.of_append hsK
      have hUK := U_append G (GraphWalk.cons hl A) B
      have hEdges : ∀ f, f ∈ ((GraphWalk.cons hl A).append B).edges ↔ f ∈
        (GraphWalk.cons hl A).edges ∨ f ∈ B.edges := fun f ↦ by
        rw [GraphWalk.edges_append, List.mem_append]
      have hm₁ : (walkDrawing G (GraphWalk.cons hl A)).U ⊆ Z := subset_union_left.trans (hUK ▸ hKZ)
      have hm₂ : (walkDrawing G B).U ⊆ Z := subset_union_right.trans (hUK ▸ hKZ)
      have hpM : PushesInto Z Y (walkDrawing G (GraphWalk.cons hl A)).U a u := by
        by_cases he : e ∈ Dv.E
        · have hyV : y ∈ Dv.V := (Drawing.IsLink.mem_V_of_sub hDv hl he).2
          obtain rfl : y = u := hA y A.start_mem_support hyV
          have hsA : A.IsSimple := (GraphWalk.IsSimple.of_cons hsM)
          obtain ⟨hAe, hAs⟩ := simple_self hsA
          refine PushesInto.of_subset fun x hx ↦ hY x ?_ (hm₁ hx)
          rw [mem_walkDrawing_U] at hx
          rcases hx with hx | ⟨f, hf, hxf⟩
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact Dv.V_subset_U ha
            · rw [hAs, List.mem_singleton] at hx
              rw [hx]
              exact Dv.V_subset_U hyV
          · rcases List.mem_cons.mp hf with rfl | hf
            · exact Dv.closure_subset_U he hxf
            · rw [hAe] at hf
              simp at hf
        · have hoff : ∀ f ∈ (GraphWalk.cons hl A).edges, f ∉ Dv.E := by
            intro f hf hfD
            rcases List.mem_cons.mp hf with rfl | hf
            · exact he hfD
            · obtain ⟨x, z, hne, hx, hz, hxV, hzV⟩ := mem_V_of_link_edge hDv hf hfD
              exact hne ((hA x hx hxV).trans (hA z hz hzV).symm)
          refine harc a u _ ⟨hau, hsM, ha, huX, ?_, hoff, fun f hf ↦ ?_⟩ fun f hf ↦ (hEdges f).mpr
            (.inl hf)
          · intro x hx hxV
            rcases List.mem_cons.mp hx with rfl | hx
            · exact .inl rfl
            · exact .inr (hA x hx hxV)
          · exact (hKe f ((hEdges f).mpr (.inl hf))).resolve_left (hoff f hf)
      have hpB : PushesInto Z Y (walkDrawing G B).U u b := by
        exact ih B.length hlen B rfl hsB huX hb (fun f hf ↦ hKe f ((hEdges f).mpr (.inr hf))) hm₂
          fun v w M hM hMe ↦ harc v w M hM fun f hf ↦ (hEdges f).mpr (.inr (hMe f hf))
      obtain ⟨p₁, hp₁⟩ := exists_walk_path G _ hsM
      obtain ⟨p₂, hp₂⟩ := exists_walk_path G _ hsB
      exact hpM.trans hpB (IsLineWithEnds.isSimplyConnectedSet (isLine_of_isPathBetween
        (walkDrawing_isPathBetween G hsK) hab)) hKZ
        (by rw [hUK]; exact subset_union_left) (by rw [hUK]; exact subset_union_right) hp₁ hp₂

omit [T2Space S] in
/-- A circuit in two pieces, each pushing into the simply-connected set `Y`, is null-homotopic in
`Z`. -/
theorem split_null {Z Y : Set Shat} (hYs : IsSimplyConnectedSet Y) (hYZ : Y ⊆ Z) {a b : Shat} {W₁ :
  GraphWalk D.rad.G.toGraph a b}
    {W₂ : GraphWalk D.rad.G.toGraph b a} (hs : Splits C W₁ W₂) (hab : a ≠ b) (hz : C.U ⊆ Z)
      (ha : a ∈ Y) (hb : b ∈ Y)
    (h₁ : PushesInto Z Y (walkDrawing D.rad.G W₁).U a b) (h₂ : PushesInto Z Y
      (walkDrawing D.rad.G W₂).U b a) : IsNullHomotopicOArcIn Z C.U := by
  have : ConnectedSpace Shat := cap.connected
  have hU₂ : (walkDrawing D.rad.G W₂.reverse).U = (walkDrawing D.rad.G W₂).U := by
    ext x
    simp only [mem_walkDrawing_U, GraphWalk.support_reverse, GraphWalk.edges_reverse,
      List.mem_reverse]
  have hCU : C.U = (walkDrawing D.rad.G W₁).U ∪ (walkDrawing D.rad.G W₂).U := U_union (by
    ext x
    rw [hs.V x, walkDrawing_V, walkDrawing_V]
    rfl) (by
    ext e
    rw [hs.E e, walkDrawing_E, walkDrawing_E]
    rfl)
  obtain ⟨f₁, f₁0, f₁1⟩ := isLine_of_isPathBetween (walkDrawing_isPathBetween D.rad.G hs.s₁) hab
  obtain ⟨f₂, f₂0, f₂1⟩ := isLine_of_isPathBetween (walkDrawing_isPathBetween D.rad.G
    hs.s₂.reverse) hab
  let p : Path a b := ⟨⟨fun t ↦ (f₁ t).1, by fun_prop⟩, f₁0, f₁1⟩
  let q : Path a b := ⟨⟨fun t ↦ (f₂ t).1, by fun_prop⟩, f₂0, f₂1⟩
  have hpi : Function.Injective p := fun s t h ↦ f₁.injective (Subtype.ext h)
  have hqi : Function.Injective q := fun s t h ↦ f₂.injective (Subtype.ext h)
  have hpm : ∀ t, p t ∈ (walkDrawing D.rad.G W₁).U := fun t ↦ (f₁ t).2
  have hqm : ∀ t, q t ∈ (walkDrawing D.rad.G W₂).U := fun t ↦ hU₂ ▸ (f₂ t).2
  have hrp : range p = (walkDrawing D.rad.G W₁).U := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact hpm t
    · intro hx
      obtain ⟨t, ht⟩ := f₁.surjective ⟨x, hx⟩
      exact ⟨t, congrArg Subtype.val ht⟩
  have hrq : range q = (walkDrawing D.rad.G W₂).U := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact hqm t
    · intro hx
      obtain ⟨t, ht⟩ := f₂.surjective ⟨x, hU₂.symm ▸ hx⟩
      exact ⟨t, congrArg Subtype.val ht⟩
  have haZ := hYZ ha
  have hbZ := hYZ hb
  have hzp : ∀ t, p t ∈ Z := fun t ↦ hz (hCU ▸ Or.inl (hpm t))
  have hzq : ∀ t, q.symm t ∈ Z := fun t ↦ hz (hCU ▸ Or.inr (hqm _))
  let P' : Path (⟨a, haZ⟩ : Z) ⟨b, hbZ⟩ := pathCod p haZ hbZ hzp
  let Q' : Path (⟨b, hbZ⟩ : Z) ⟨a, haZ⟩ := pathCod q.symm hbZ haZ hzq
  obtain ⟨y₁, hy₁, ho₁⟩ := h₁ haZ hbZ P' hpm
  obtain ⟨y₂, hy₂, ho₂⟩ := h₂ hbZ haZ Q' fun t ↦ hqm _
  have hval : ∀ t, ((P'.trans Q') t).1 = (p.trans q.symm) t := fun t ↦ by
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs <;> rfl
  have hnull : (P'.trans Q').Homotopic (Path.refl _) :=
    (ho₁.hcomp ho₂).trans (homotopic_of_mem hYs hYZ _ _ ha ha (fun t ↦ by
      rw [Path.trans_apply]
      split_ifs
      · exact hy₁ _
      · exact hy₂ _) fun _ ↦ ha)
  refine null_oArc_of_loop (P'.trans Q') ?_ (fun s t hst ↦ ?_) hnull
  · have : (fun t ↦ ((P'.trans Q') t).1) = ⇑(p.trans q.symm) := funext hval
    rw [this, Path.trans_range, hrp, Path.symm_range, hrq, hCU]
  · rw [hval, hval] at hst
    refine loop_trans_injective p q hpi hqi (fun s t he ↦ ?_) s t hst
    have hin := U_inter_of_disjoint (walkDrawing_isSubdrawing D.rad.G W₁)
      (walkDrawing_isSubdrawing D.rad.G W₂)
      (disjoint_left.mpr fun e h₁' h₂' ↦ hs.edge e (by rwa [walkDrawing_E] at h₁')
        (by rwa [walkDrawing_E] at h₂'))
    have hm : p s ∈ (walkDrawing D.rad.G W₁).V ∩ (walkDrawing D.rad.G W₂).V := by
      rw [← hin]
      exact ⟨hpm s, he ▸ hqm t⟩
    rw [walkDrawing_V, walkDrawing_V] at hm
    rcases hs.meet _ hm.1 hm.2 with h' | h'
    · left
      exact ⟨hpi (h'.trans p.source.symm), hqi ((he.symm.trans h').trans q.source.symm)⟩
    · right
      exact ⟨hpi (h'.trans p.target.symm), hqi ((he.symm.trans h').trans q.target.symm)⟩

omit [T2Space S] [T2Space Shat] in
/-- An arc of `F` with ends `a`, `b` is one of the two pieces of `F` between `a` and `b`. -/
theorem eq_side_of_walk {a b : Shat} {P : GraphWalk D.rad.G.toGraph a b} (hne : a ≠ b)
  (hsim : P.IsSimple) (hinF : ∀ e ∈ P.edges, e ∈ F.E)
    {W₁ : GraphWalk D.rad.G.toGraph a b} {W₂ : GraphWalk D.rad.G.toGraph b a}
      (hs : Splits F W₁ W₂) : P = W₁ ∨ P = W₂.reverse := by
  have key : (∀ e ∈ P.edges, e ∈ W₁.edges) ∨ (∀ e ∈ P.edges, e ∈ W₂.edges) := by
    cases P with
    | nil _ => exact absurd rfl hne
    | @cons _ y _ e hl r =>
      have hnd : (GraphWalk.cons hl r).support.Nodup := hsim
      simp only [GraphWalk.support_cons, List.nodup_cons] at hnd
      have hE : ∀ f ∈ r.edges, f ∈ W₁.edges ∨ f ∈ W₂.edges := fun f hf ↦ (hs.E f).mp (hinF f
        (by simp [hf]))
      have he := (hs.E e).mp (hinF e (by simp))
      have hmeet : ∀ x ∈ r.support, x ∈ W₁.support → x ∈ W₂.support → x = b := fun x hx h₁ h₂ ↦
        (hs.meet x h₁ h₂).resolve_left fun h' ↦ hnd.1 (h' ▸ hx)
      rcases he with he | he
      · left
        have := walk_stays r hnd.2 W₁ W₂ hE hmeet (W₁.left_mem_support_of_mem_edges he hl.symm)
          (fun {f x z} hl' hf _ ↦ W₁.left_mem_support_of_mem_edges hf hl'.symm)
          (fun {f x z} hl' hf ↦ W₂.left_mem_support_of_mem_edges hf hl')
        intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact he
        · exact this f hf
      · right
        have := walk_stays r hnd.2 W₂ W₁ (fun f hf ↦ (hE f hf).symm) (fun x hx h₁ h₂ ↦ hmeet x hx
          h₂ h₁)
          (W₂.left_mem_support_of_mem_edges he hl.symm)
          (fun {f x z} hl' hf _ ↦ W₂.left_mem_support_of_mem_edges hf hl'.symm)
          (fun {f x z} hl' hf ↦ W₁.left_mem_support_of_mem_edges hf hl')
        intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact he
        · exact this f hf
  rcases key with h | h
  · exact .inl (simple_walk_unique W₁ P hs.s₁ hsim h).symm
  · refine .inr (simple_walk_unique W₂.reverse P hs.s₂.reverse hsim fun e he ↦ ?_).symm
    rw [GraphWalk.edges_reverse, List.mem_reverse]
    exact h e he

omit [T2Space S] [T2Space Shat] in
theorem exists_side_of_walk {a b : Shat} {P : GraphWalk D.rad.G.toGraph a b} (hne : a ≠ b)
  (hsim : P.IsSimple) (hinF : ∀ e ∈ P.edges, e ∈ F.E)
    {W₁ : GraphWalk D.rad.G.toGraph a b} {W₂ : GraphWalk D.rad.G.toGraph b a}
      (hs : Splits F W₁ W₂) :
    ∃ R : GraphWalk D.rad.G.toGraph b a, Splits F P R := by
  rcases eq_side_of_walk hne hsim hinF hs with rfl | rfl
  · exact ⟨W₂, hs⟩
  · exact ⟨W₁.reverse, hs.rev⟩

omit [T2Space S] in
/-- **The two outer arcs of (13.6).** -/
theorem exists_two_arcs (hDv : Dv.IsCircuitOf D.rad.G) (hF : F.IsCircuitOf D.rad.G)
  (hC : C.IsCircuitOf D.rad.G) {Δ₀ Δc Δf Δv : Set Shat} {h : Shat}
    (h₀ : IsClosedDisc Δ₀) (hΔc : IsClosedDisc Δc) (hc₀ : Δc ⊆ Δ₀) (hbc : discBd Δc = C.U)
      (hhc : h ∈ Δc) (hhC : h ∉ C.U)
    (hΔf : IsClosedDisc Δf) (hf₀ : Δf ⊆ Δ₀) (hbf : discBd Δf = F.U) (hhf : h ∉ Δf)
    (hΔv : IsClosedDisc Δv) (hv₀ : Δv ⊆ Δ₀) (hbv : discBd Δv = Dv.U) (hhv : h ∈ Δv → h ∈ Dv.U)
    (hCE : ∀ e ∈ C.E, e ∈ F.E ∨ e ∈ Dv.E) :
    ∃ (a₀ b₀ a₁ b₁ : Shat) (P₀ : GraphWalk D.rad.G.toGraph a₀ b₀) (P₁ : GraphWalk D.rad.G.toGraph
      a₁ b₁),
      IsArcOn D.rad.G Dv F P₀ ∧ IsArcOn D.rad.G Dv F P₁ ∧ ¬ PushesInto (Δ₀ \ {h}) (Δv \ {h})
        (walkDrawing D.rad.G P₀).U a₀ b₀ ∧
      ¬ PushesInto (Δ₀ \ {h}) (Δv \ {h}) (walkDrawing D.rad.G P₁).U a₁ b₁
        ∧ ∃ e ∈ P₀.edges, e ∉ P₁.edges := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hsurf := Surface.IsClosedSurface.isSurface hT
  set G := D.rad.G with hG
  set Z := Δ₀ \ {h} with hZ
  set Y := Δv \ {h} with hYd
  have hYs : IsSimplyConnectedSet Y := by
    by_cases hm : h ∈ Δv
    · exact isSimplyConnectedSet_disc_diff hΔv (hbv ▸ hhv hm)
    · rw [hYd, sdiff_singleton_eq_self hm]
      exact hΔv.isSimplyConnectedSet
  have hYZ : Y ⊆ Z := fun x hx ↦ ⟨hv₀ hx.1, hx.2⟩
  have hDY : ∀ x ∈ Dv.U, x ∈ Z → x ∈ Y := fun x hx hxZ ↦ ⟨by
    rw [← hbv] at hx
    exact Surface.discBd_subset _ hx, hxZ.2⟩
  have hFΔ : F.U ⊆ Δf := by
    rw [← hbf]
    exact Surface.discBd_subset _
  have hCΔ : C.U ⊆ Δc := by
    rw [← hbc]
    exact Surface.discBd_subset _
  have hCZ : C.U ⊆ Z := fun x hx ↦ ⟨hc₀ (hCΔ hx), fun he ↦ hhC (he ▸ hx)⟩
  have hFZ : F.U ⊆ Z := fun x hx ↦ ⟨hf₀ (hFΔ hx), fun he ↦ hhf (he ▸ hFΔ hx)⟩
  -- the two vertices of `C` on `D_v`
  have hCF : ∃ e ∈ C.E, e ∉ F.E := by
    by_contra hn
    push Not at hn
    have hE := circuit_E_eq_of_subset hF.2 hC.2 hF.1 hC.1 hn
    obtain rfl := circuit_eq_of_E hC.2 hF.2 hC.1 hF.1 hE
    exact hhf ((disc_eq_of_subset_disc hT h₀ hΔc hΔf hc₀ hf₀ (hbc.trans hbf.symm)) ▸ hhc)
  have hsubW : ∀ {a b : Shat} (W : GraphWalk G.toGraph a b), (∀ e ∈ W.edges, e ∈ C.E) → a ∈ C.V →
    (walkDrawing G W).U ⊆ C.U := by
    intro a b W hE ha x hx
    rw [mem_walkDrawing_U] at hx
    rcases hx with hx | ⟨e, he, hxe⟩
    · exact C.V_subset_U (support_subset_of_edges hC.1 W ha hE x hx)
    · exact C.closure_subset_U (hE e he) hxe
  obtain ⟨a₀, b₀, P₀, hP₀, hP₀C, hP₀n⟩ : ∃ (a₀ b₀ : Shat) (P₀ : GraphWalk G.toGraph a₀ b₀), IsArcOn
    G Dv F P₀ ∧ (∀ e ∈ P₀.edges, e ∈ C.E) ∧
      ¬ PushesInto Z Y (walkDrawing G P₀).U a₀ b₀ := by
    by_contra hn
    push Not at hn
    obtain ⟨e, heC, heF⟩ := hCF
    have heD := (hCE e heC).resolve_left heF
    obtain ⟨x, y, hne, hxC, hyC, hcap⟩ : ∃ x y, x ≠ y ∧ x ∈ C.V ∧ y ∈ C.V ∧ closure e ∩ G.V
      = {x, y} := by
      obtain ⟨x, hx, y, hy, hcap⟩ := D.rad.isPreRadial.2.2.2.2.1 e (hC.1.2 heC)
      have hl : G.toGraph.IsLink e x y := ⟨hC.1.2 heC, D.rad.isPreRadial.2.1 hx, hy.1, hcap⟩
      have := Drawing.IsLink.mem_V_of_sub hC.1 hl heC
      exact ⟨x, y, fun h' ↦ hy.2 (h' ▸ hx), this.1, this.2, hcap⟩
    have hl : G.toGraph.IsLink e x y := by
      have hx : x ∈ closure e ∩ G.V := by rw [hcap]; exact .inl rfl
      have hy : y ∈ closure e ∩ G.V := by rw [hcap]; exact .inr rfl
      exact ⟨hC.1.2 heC, hx.2, hy.2, hcap⟩
    have hxD := (Drawing.IsLink.mem_V_of_sub hDv.1 hl heD).1
    have hyD := (Drawing.IsLink.mem_V_of_sub hDv.1 hl heD).2
    obtain ⟨W₁, W₂, hs⟩ := exists_splits hC.2 hC.1 hxC hyC hne
    have hin₁ : ∀ f ∈ W₁.edges, f ∈ C.E := fun f hf ↦ (hs.E f).mpr (.inl hf)
    have hin₂ : ∀ f ∈ W₂.edges, f ∈ C.E := fun f hf ↦ (hs.E f).mpr (.inr hf)
    have hswap : ∀ f ∈ C.E, f ∈ Dv.E ∨ f ∈ F.E := fun f hf ↦ (hCE f hf).symm
    have hU₁ := hsubW W₁ hin₁ hxC
    have hU₂ := hsubW W₂ hin₂ hyC
    have hp₁ := walk_pushes (F := F) hDv.1 hDY _ W₁ rfl hs.s₁ hxD hyD (fun f hf ↦ hswap f
      (hin₁ f hf)) (hU₁.trans hCZ)
      fun u v M hM hMe ↦ hn u v M hM fun f hf ↦ hin₁ f (hMe f hf)
    have hp₂ := walk_pushes (F := F) hDv.1 hDY _ W₂ rfl hs.s₂ hyD hxD (fun f hf ↦ hswap f
      (hin₂ f hf)) (hU₂.trans hCZ)
      fun u v M hM hMe ↦ hn u v M hM fun f hf ↦ hin₂ f (hMe f hf)
    have hxY : x ∈ Y := hDY x (Dv.V_subset_U hxD) (hCZ (C.V_subset_U hxC))
    have hyY : y ∈ Y := hDY y (Dv.V_subset_U hyD) (hCZ (C.V_subset_U hyC))
    have hnull := split_null hYs hYZ hs hne hCZ hxY hyY hp₁ hp₂
    have hbd : Disjoint C.U (bd Shat) := disjoint_left.mpr fun x _ hx ↦ hx (hT.2.2 x)
    obtain ⟨Δ', hΔ'Z, hΔ', hb'⟩ := (epstein Shat Z C.U hsurf inferInstance
      (GM14.isOArc_of_isCircuit hC.2) hCZ hbd).1 hnull
    have heq := disc_eq_of_subset_disc hT h₀ hΔ' hΔc (hΔ'Z.trans sdiff_subset) hc₀
      (hb'.trans hbc.symm)
    exact (hΔ'Z (heq ▸ hhc)).2 rfl
  by_contra hn
  have hall : ∀ (u v : Shat) (M : GraphWalk G.toGraph u v), IsArcOn G Dv F M → ¬ PushesInto Z Y
    (walkDrawing G M).U u v →
      ∀ e ∈ P₀.edges, e ∈ M.edges := by
    intro u v M hM hMn e he
    by_contra hem
    exact hn ⟨a₀, b₀, u, v, P₀, M, hP₀, hM, hP₀n, hMn, e, he, hem⟩
  obtain ⟨e₀, he₀⟩ : ∃ e, e ∈ P₀.edges := by
    have hne := hP₀.ne
    cases P₀ with
    | nil _ => exact absurd rfl hne
    | @cons _ y _ e hl r => exact ⟨e, by simp⟩
  have ha₀F : a₀ ∈ F.V := by
    have hinF := hP₀.inF
    have hne := hP₀.ne
    cases P₀ with
    | nil _ => exact absurd rfl hne
    | @cons _ y _ e hl r => exact (Drawing.IsLink.mem_V_of_sub hF.1 hl (hinF e (by simp))).1
  have hb₀F : b₀ ∈ F.V := support_subset_of_edges hF.1 P₀ ha₀F hP₀.inF _ P₀.end_mem_support
  obtain ⟨W₁, W₂, hs⟩ := exists_splits hF.2 hF.1 ha₀F hb₀F hP₀.ne
  obtain ⟨R, hR⟩ := exists_side_of_walk hP₀.ne hP₀.simple hP₀.inF hs
  have hRE : ∀ f ∈ R.edges, f ∈ F.E := fun f hf ↦ (hR.E f).mpr (.inr hf)
  have hRU : (walkDrawing G R).U ⊆ F.U := by
    intro x hx
    rw [mem_walkDrawing_U] at hx
    rcases hx with hx | ⟨e, he, hxe⟩
    · exact F.V_subset_U ((hR.V x).mpr (.inr hx))
    · exact F.closure_subset_U (hRE e he) hxe
  have hPU : (walkDrawing G P₀).U ⊆ F.U := by
    intro x hx
    rw [mem_walkDrawing_U] at hx
    rcases hx with hx | ⟨e, he, hxe⟩
    · exact F.V_subset_U ((hR.V x).mpr (.inl hx))
    · exact F.closure_subset_U (hP₀.inF e he) hxe
  have hpR : PushesInto Z Y (walkDrawing G R).U b₀ a₀ := by
    refine walk_pushes (F := F) hDv.1 hDY _ R rfl hR.s₂ hP₀.right hP₀.left (fun f hf ↦ .inr
      (hRE f hf)) (hRU.trans hFZ) fun u v M hM hMe ↦ ?_
    by_contra hMn
    exact hR.edge e₀ he₀ (hMe e₀ (hall u v M hM hMn e₀ he₀))
  apply hP₀n
  intro ha' hb' p hp
  obtain ⟨r₀, hr₀⟩ := exists_walk_path G R hR.s₂
  obtain ⟨r, hr⟩ := exists_path_in (hRU.trans hFZ) hr₀ hb' ha'
  obtain ⟨y, hy, ho⟩ := hpR hb' ha' r fun t ↦ by rw [hr]; exact hr₀ t
  have hΔfZ : Δf ⊆ Z := fun x hx ↦ ⟨hf₀ hx, fun he ↦ hhf (he ▸ hx)⟩
  have ha₀Δ : a₀ ∈ Δf := hFΔ (F.V_subset_U ha₀F)
  have hb₀Δ : b₀ ∈ Δf := hFΔ (F.V_subset_U hb₀F)
  refine ⟨y.symm, fun t ↦ hy _, ?_⟩
  refine Path.Homotopic.trans (homotopic_of_mem hΔf.isSimplyConnectedSet hΔfZ p r.symm ha₀Δ hb₀Δ
    (fun t ↦ hFΔ (hPU (hp t))) fun t ↦ ?_) ho.symm₂
  rw [Path.symm_apply]
  change (r _).1 ∈ Δf
  rw [hr]
  exact hFΔ (hRU (hr₀ _))

end TangleDatum

end GraphMinor.GM19
