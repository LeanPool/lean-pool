/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section810

/-!
# Tools for the ties of Graph Minors XI, Section 9

The proof of (9.2) builds its tie `X` from closed discs, a line, and an edge or a vertex, glued at
single points. This file has the facts about such gluing that need no drawing: an `O`-arc in a union
of
two closed sets that meet in at most one point lies in one of them (`IsOArc.subset_or_subset`), a
line
contains no `O`-arc (`not_isOArc_of_subset_line`), and the gluing of lines (`IsArm`). It also has
the
choice of a segment of a walk from a set `A` to a set `B` (`exists_crossing`), and the notion of a
set that holds `ins(C)` for each circuit `C` drawn in it (`IsAbsorbing`).
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- An `O`-arc in the union of two closed sets that meet in at most the point `p` lies in one of
them, since removing one point from an `O`-arc leaves a connected set. -/
theorem IsOArc.subset_or_subset {J P Q : Set S} {p : S} (hJ : IsOArc J) (hP : IsClosed P)
    (hQ : IsClosed Q) (hsub : J ⊆ P ∪ Q) (hPQ : P ∩ Q ⊆ {p}) : J ⊆ P ∨ J ⊆ Q := by
  obtain ⟨f⟩ := id hJ
  have hT : IsPreconnected (J \ {p}) := by
    by_cases hp : p ∈ J
    · have heq : J \ {p} = (fun w => (f w).1) '' {f.symm ⟨p, hp⟩}ᶜ := by
        ext x
        constructor
        · rintro ⟨hx, hxp⟩
          refine ⟨f.symm ⟨x, hx⟩, fun h => hxp ?_, by simp⟩
          have := f.symm.injective h
          exact congrArg Subtype.val this
        · rintro ⟨w, hw, rfl⟩
          refine ⟨(f w).2, fun h => hw ?_⟩
          have : f w = ⟨p, hp⟩ := Subtype.ext h
          simp [← this]
      rw [heq]
      exact (Circle.isPathConnected_compl_singleton _).isConnected.isPreconnected.image _
        (by fun_prop : Continuous fun w => (f w).1).continuousOn
    · have : J \ {p} = J := by
        ext x
        exact ⟨fun h => h.1, fun h => ⟨h, fun e => hp (e ▸ h)⟩⟩
      rw [this]
      exact hJ.isPreconnected
  have hcl : J ⊆ closure (J \ {p}) := by
    have hd : J ⊆ closure (J \ {p}) ∪ {p} := fun x hx => by
      by_cases h : x = p
      · exact Or.inr h
      · exact Or.inl (subset_closure ⟨hx, h⟩)
    by_cases hp : p ∈ closure (J \ {p})
    · intro x hx
      rcases hd hx with h | h
      · exact h
      · exact (mem_singleton_iff.mp h) ▸ hp
    · rcases isPreconnected_iff_subset_of_disjoint_closed.mp hJ.isPreconnected _ _ isClosed_closure
        isClosed_singleton hd (by
          ext x
          simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false]
          rintro ⟨-, h, rfl⟩
          exact hp h) with h | h
      · exact h
      · exact ((infinite_of_isOArc hJ).mono h (finite_singleton p)).elim
  have hcov : J \ {p} ⊆ P ∪ Q := sdiff_subset.trans hsub
  have hdis : (J \ {p}) ∩ (P ∩ Q) = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
    rintro ⟨⟨-, hx⟩, h⟩
    exact hx (hPQ h)
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hT P Q hP hQ hcov hdis with h | h
  · exact Or.inl (hcl.trans (closure_minimal h hP))
  · exact Or.inr (hcl.trans (closure_minimal h hQ))

/-- A line contains no `O`-arc: three points of the `O`-arc lie in order along the line, and the
middle one cuts the line into two closed pieces, which meet only there. -/
theorem not_isOArc_of_subset_line {L J : Set S} (hL : IsLine L) (hJ : IsOArc J) (h : J ⊆ L) : False
  := by
  classical
  obtain ⟨f⟩ := hL
  let g : I → S := fun t => (f t).1
  have hg : Continuous g := by fun_prop
  have hginj : Function.Injective g := fun a b hab => f.injective (Subtype.ext hab)
  have hrange : ∀ x ∈ L, ∃ t, g t = x := fun x hx => ⟨f.symm ⟨x, hx⟩, by simp [g]⟩
  have hinf : (g ⁻¹' J).Infinite := by
    intro hfin
    refine infinite_of_isOArc hJ ((hfin.image g).subset fun x hx => ?_)
    obtain ⟨t, rfl⟩ := hrange x (h hx)
    exact ⟨t, hx, rfl⟩
  obtain ⟨s, hs, hcard⟩ := hinf.exists_subset_card_eq 3
  let e := s.orderEmbOfFin hcard
  have hmem : ∀ i, g (e i) ∈ J := fun i => hs (s.orderEmbOfFin_mem hcard i)
  have h01 : e 0 < e 1 := e.strictMono (by decide)
  have h12 : e 1 < e 2 := e.strictMono (by decide)
  have hclosed : ∀ T : Set I, IsClosed T → IsClosed (g '' T) := fun T hT =>
    (hT.isCompact.image hg).isClosed
  rcases IsOArc.subset_or_subset (p := g (e 1)) hJ (hclosed (Iic (e 1)) isClosed_Iic)
    (hclosed (Ici (e 1)) isClosed_Ici) (fun x hx => by
      obtain ⟨t, rfl⟩ := hrange x (h hx)
      rcases le_total t (e 1) with ht | ht
      · exact Or.inl ⟨t, ht, rfl⟩
      · exact Or.inr ⟨t, ht, rfl⟩) (by
      rintro _ ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
      obtain rfl := hginj hab
      exact congrArg g (le_antisymm ha hb)) with hc | hc
  · obtain ⟨t, ht, hte⟩ := hc (hmem 2)
    exact absurd (ht.trans_lt h12) (by rw [hginj hte]; exact lt_irrefl _)
  · obtain ⟨t, ht, hte⟩ := hc (hmem 0)
    exact absurd (h01.trans_le ht) (by rw [hginj hte]; exact lt_irrefl _)

/-- `T` is the point `p`, or a line with `p` as an end. The sets `A` of (9.2) that are not discs are
of this kind, and so is `A` with the line `F` added. -/
def IsArm (T : Set S) (p : S) : Prop := T = {p} ∨ ∃ q, IsLineWithEnds T p q

omit [T2Space S] in
theorem IsLineWithEnds.left_mem {L : Set S} {a b : S} (h : IsLineWithEnds L a b) : a ∈ L := by
  obtain ⟨f, h₀, -⟩ := h
  exact h₀ ▸ (f 0).2

omit [T2Space S] in
theorem IsLineWithEnds.right_mem {L : Set S} {a b : S} (h : IsLineWithEnds L a b) : b ∈ L := by
  obtain ⟨f, -, h₁⟩ := h
  exact h₁ ▸ (f 1).2

omit [T2Space S] in
theorem IsLineWithEnds.isLine {L : Set S} {a b : S} (h : IsLineWithEnds L a b) : IsLine L := by
  obtain ⟨f, -, -⟩ := h
  exact ⟨f⟩

theorem IsArm.isClosed {T : Set S} {p : S} (h : IsArm T p) : IsClosed T := by
  rcases h with rfl | ⟨q, f, -, -⟩
  · exact isClosed_singleton
  · have hc : IsCompact (range fun t : I => (f t).1) := isCompact_range (by fun_prop)
    have : (range fun t : I => (f t).1) = T := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        exact (f t).2
      · intro hx
        exact ⟨f.symm ⟨x, hx⟩, by simp⟩
    exact this ▸ hc.isClosed

/-- Adding at the end `p` of an arm a line from `p` to `b` gives an arm with end `b`. -/
theorem IsArm.extend {T F : Set S} {p b : S} (hT : IsArm T p) (hF : IsLineWithEnds F p b)
    (h : T ∩ F = {p}) : IsArm (T ∪ F) b := by
  rcases hT with rfl | ⟨q, hq⟩
  · have : ({p} : Set S) ∪ F = F := union_eq_right.mpr (singleton_subset_iff.mpr
      (IsLineWithEnds.left_mem hF))
    rw [this]
    exact Or.inr ⟨p, IsLineWithEnds.symm hF⟩
  · exact Or.inr ⟨q, IsLineWithEnds.symm (IsLineWithEnds.union hq hF h)⟩

/-- The six shapes of a tie (Graph Minors XI, page 104). -/
def IsTieShape (X : Set S) : Prop :=
  X.ncard = 1 ∧ X.Finite ∨
    IsLine X ∨
    IsClosedDisc X ∨
    (∃ D₁ D₂ : Set S, IsClosedDisc D₁ ∧ IsClosedDisc D₂ ∧ (D₁ ∩ D₂).ncard = 1 ∧
      (D₁ ∩ D₂).Finite ∧ X = D₁ ∪ D₂) ∨
    (∃ (D F : Set S) (a b : S), IsClosedDisc D ∧ IsLineWithEnds F a b ∧ F ∩ D = {a} ∧
      X = D ∪ F) ∨
    (∃ (D₁ D₂ F : Set S) (a b : S), IsClosedDisc D₁ ∧ IsClosedDisc D₂ ∧ Disjoint D₁ D₂ ∧
      IsLineWithEnds F a b ∧ F ∩ D₁ = {a} ∧ F ∩ D₂ = {b} ∧ X = D₁ ∪ D₂ ∪ F)

omit [T2Space S] in
theorem IsArm.isTieShape {T : Set S} {p : S} (h : IsArm T p) : IsTieShape T := by
  rcases h with rfl | ⟨q, hq⟩
  · exact Or.inl ⟨by simp, by simp⟩
  · exact Or.inr (Or.inl (IsLineWithEnds.isLine hq))

/-- Two arms with the same end, which meet only there, form a point or a line. -/
theorem IsArm.isTieShape_union {T T' : Set S} {p : S} (h : IsArm T p) (h' : IsArm T' p)
    (hi : T ∩ T' = {p}) : IsTieShape (T ∪ T') := by
  rcases h with rfl | ⟨q, hq⟩
  · have : p ∈ T' := by
      have : p ∈ ({p} : Set S) ∩ T' := by rw [hi]; rfl
      exact this.2
    rw [union_eq_right.mpr (singleton_subset_iff.mpr this)]
    exact h'.isTieShape
  · rcases h' with rfl | ⟨q', hq'⟩
    · rw [union_eq_left.mpr (singleton_subset_iff.mpr (IsLineWithEnds.left_mem hq))]
      exact Or.inr (Or.inl (IsLineWithEnds.isLine hq))
    · exact Or.inr (Or.inl (IsLineWithEnds.isLine (IsLineWithEnds.union hq hq' hi)))

omit [T2Space S] in
/-- A closed disc and an arm that meet only at the end of the arm have the shape of a tie. -/
theorem IsArm.isTieShape_disc {D T : Set S} {p : S} (hD : IsClosedDisc D) (h : IsArm T p)
    (hi : D ∩ T = {p}) : IsTieShape (D ∪ T) := by
  have hp : p ∈ D ∩ T := by rw [hi]; rfl
  rcases h with rfl | ⟨q, hq⟩
  · rw [union_eq_left.mpr (singleton_subset_iff.mpr hp.1)]
    exact Or.inr (Or.inr (Or.inl hD))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨D, T, p, q, hD, hq, by rw [inter_comm, hi],
      rfl⟩))))

section Crossing

variable {α β : Type*} {G : Graph α β}

/-- If a walk meets `A`, then it has a final segment that starts in `A` and meets `A` in no other
vertex. -/
theorem exists_last_in (A : Set α) {a b : α} (T : GraphWalk G a b) (h : ∃ x ∈ T.support, x ∈ A) :
    ∃ a' ∈ A, ∃ T' : GraphWalk G a' b, T'.edges.Sublist T.edges ∧ (∀ x ∈ T'.support, x ∈ T.support)
      ∧
      ∀ x ∈ T'.support, x ∈ A → x = a' := by
  induction T with
  | nil hu =>
    obtain ⟨x, hx, hxA⟩ := h
    obtain rfl : x = _ := by simpa using hx
    exact ⟨_, hxA, .nil hu, List.Sublist.refl _, fun _ hy => hy, fun y hy _ => by simpa using hy⟩
  | @cons u v w e hl r ih =>
    by_cases hr : ∃ x ∈ r.support, x ∈ A
    · obtain ⟨a', ha', T', h₁, h₂, h₃⟩ := ih hr
      refine ⟨a', ha', T', h₁.trans (List.sublist_cons_self _ _), fun x hx => ?_, h₃⟩
      exact List.mem_cons_of_mem _ (h₂ x hx)
    · push Not at hr
      obtain ⟨x, hx, hxA⟩ := h
      have hu : u ∈ A := by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hxA
        · exact (hr x hx hxA).elim
      refine ⟨u, hu, .cons hl r, List.Sublist.refl _, fun _ hy => hy, fun y hy hyA => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · rfl
      · exact (hr y hy hyA).elim

/-- **A crossing.** A walk from a vertex of `A` to a vertex of `B` has a segment from `A` to `B`
that
meets `A` only in its first vertex and `B` only in its last vertex. -/
theorem exists_crossing (A B : Set α) {a b : α} (T : GraphWalk G a b) (ha : a ∈ A) (hb : b ∈ B) :
    ∃ a' ∈ A, ∃ b' ∈ B, ∃ T' : GraphWalk G a' b', T'.edges.Sublist T.edges ∧
      (∀ x ∈ T'.support, x ∈ T.support) ∧ (∀ x ∈ T'.support, x ∈ A → x = a') ∧
      ∀ x ∈ T'.support, x ∈ B → x = b' := by
  obtain ⟨a', ha', T₁, h₁, h₂, h₃⟩ := exists_last_in A T ⟨a, T.start_mem_support, ha⟩
  obtain ⟨b', hb', T₂, h₄, h₅, h₆⟩ := exists_last_in B T₁.reverse
    ⟨b, T₁.reverse.start_mem_support, hb⟩
  have hs : ∀ x ∈ T₂.reverse.support, x ∈ T₂.support := fun x hx => by
    rw [GraphWalk.support_reverse] at hx
    exact List.mem_reverse.mp hx
  have hs' : ∀ x ∈ T₂.support, x ∈ T₁.support := fun x hx => by
    have := h₅ x hx
    rw [GraphWalk.support_reverse] at this
    exact List.mem_reverse.mp this
  refine ⟨a', ha', b', hb', T₂.reverse, ?_, fun x hx => h₂ x (hs' x (hs x hx)),
    fun x hx hxA => h₃ x (hs' x (hs x hx)) hxA, fun x hx hxB => h₆ x (hs x hx) hxB⟩
  rw [GraphWalk.edges_reverse]
  rw [GraphWalk.edges_reverse] at h₄
  have := h₄.reverse
  rw [List.reverse_reverse] at this
  exact this.trans h₁

end Crossing

section Absorbing

variable {Γ : Drawing S} {ins : Drawing S → Set S} {k : ℕ}

/-- `X` is closed and holds `ins(C)` for each circuit `C` drawn in `X`. Closed discs `ins(C)` have
this
property, and so do lines. -/
def IsAbsorbing (Γ : Drawing S) (ins : Drawing S → Set S) (k : ℕ) (X : Set S) : Prop :=
  IsClosed X ∧ ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ → C.length < k → C.U ⊆ X → ins C ⊆ X

theorem IsAbsorbing.union {A B : Set S} {p : S} (hA : IsAbsorbing Γ ins k A)
    (hB : IsAbsorbing Γ ins k B) (h : A ∩ B ⊆ {p}) : IsAbsorbing Γ ins k (A ∪ B) := by
  refine ⟨hA.1.union hB.1, fun C hC hs hl hU => ?_⟩
  rcases IsOArc.subset_or_subset (IsCircuit.isOArc_U hC) hA.1 hB.1 hU h with h' | h'
  · exact (hA.2 C hC hs hl h').trans subset_union_left
  · exact (hB.2 C hC hs hl h').trans subset_union_right

theorem IsArm.isAbsorbing {T : Set S} {p : S} (h : IsArm T p) : IsAbsorbing Γ ins k T := by
  refine ⟨h.isClosed, fun C hC _ _ hU => ?_⟩
  exfalso
  rcases h with rfl | ⟨q, hq⟩
  · exact (infinite_of_isOArc (IsCircuit.isOArc_U hC)).mono hU (finite_singleton p)
  · exact not_isOArc_of_subset_line (IsLineWithEnds.isLine hq) (IsCircuit.isOArc_U hC) hU

theorem isAbsorbing_ins (hs : IsSlope Γ k ins) {C : Drawing S} (hC : C.IsCircuit)
    (hCs : C.IsSubdrawing Γ) (hl : C.length < k) : IsAbsorbing Γ ins k (ins C) :=
  ⟨(hs.isClosedDisc C hC hCs hl).isCompact.isClosed, fun C' hC' hs' hl' hU =>
    hs.monotone C' C hC' hs' hl' hC hCs hl hU⟩

/-- `ins(W)` lies in an absorbing set that holds `W`. -/
theorem insWalk_subset {X : Set S} {u : S} (Z : GraphWalk Γ.toGraph u u) (hZ : Z.length < k)
    (hX : IsAbsorbing Γ ins k X) (hU : (walkDrawing Γ Z).U ⊆ X) : insWalk ins Γ Z ⊆ X := by
  rintro x (hx | hx)
  · exact hU hx
  · obtain ⟨C, ⟨hC, hCs⟩, hxC⟩ := mem_iUnion₂.mp hx
    exact hX.2 C hC (hCs.trans (walkDrawing_isSubdrawing Γ Z)) (isConfined_walk Z hZ C hC hCs)
      (hCs.U_subset.trans hU) hxC

end Absorbing

section Block

variable {D : Drawing S} {H₁ H₂ H : Hypergraph S (Set S)}

omit [T2Space S] in
private theorem end_mem (hle : H ≤ D.toHypergraph) {e : Set S} {v : S} (he : e ∈ H.edgeSet)
    (hv : v ∈ D.V) (hve : v ∈ closure e) : v ∈ H.vertexSet := by
  have hl : H.IsSubhypergraph D.toHypergraph := hle
  have : v ∈ D.toHypergraph.ends e := ⟨hl.edgeSet_subset he, hv, hve⟩
  rw [hl.ends_eq e he] at this
  exact H.vertex_mem_of_inc this

omit [T2Space S] in
private theorem mem_sides (hsep : D.toHypergraph.IsSeparation H₁ H₂) {e : Set S} (he : e ∈ D.E) :
    e ∈ H₁.edgeSet ∨ e ∈ H₂.edgeSet := by
  have : e ∈ (H₁ ∪ H₂).edgeSet := by
    rw [hsep.union_eq]
    exact he
  exact this

omit [T2Space S] in
private theorem not_mem_both (hsep : D.toHypergraph.IsSeparation H₁ H₂) {e : Set S}
    (h₁ : e ∈ H₁.edgeSet) (h₂ : e ∈ H₂.edgeSet) : False := by
  have : e ∈ (H₁ ∩ H₂).edgeSet := ⟨h₁, h₂⟩
  rw [hsep.edgeSet_inter_eq] at this
  exact this

omit [T2Space S] in
/-- All edges of a walk lie on one side of a separation of order one, if the cut vertex `p` is not
an
inner vertex of the walk. -/
private theorem same_side (hsep : D.toHypergraph.IsSeparation H₁ H₂) {p : S}
    (hp : ∀ x, x ∈ H₁.vertexSet → x ∈ H₂.vertexSet → x = p) {a b : S}
    (R : GraphWalk D.toGraph a b)
    (hR : ∀ (x : S) (R₁ : GraphWalk D.toGraph a x) (R₂ : GraphWalk D.toGraph x b), R = R₁.append R₂
      →
      0 < R₁.length → 0 < R₂.length → x ≠ p) :
    (∀ e ∈ R.edges, e ∈ H₁.edgeSet) ∨ (∀ e ∈ R.edges, e ∈ H₂.edgeSet) := by
  induction R with
  | nil _ => exact Or.inl (by simp)
  | @cons a c b e hl r ih =>
    have ih' := ih fun x R₁ R₂ hr h₁ h₂ =>
      hR x (.cons hl R₁) R₂ (by subst hr; rfl) (by simp) h₂
    cases r with
    | nil hc =>
      rcases mem_sides hsep hl.1 with h | h
      · exact Or.inl (by simpa using h)
      · exact Or.inr (by simpa using h)
    | @cons c d b f hl' r' =>
      have hcp : c ≠ p := hR c (.cons hl (.nil hl.2.2.1)) (.cons hl' r') rfl (by simp) (by simp)
      have hce : c ∈ closure e := (hl.2.2.2.symm ▸ (Or.inr rfl : c ∈ ({a, c} : Set S)) :
        c ∈ closure e ∩ D.V).1
      have hcf : c ∈ closure f := (hl'.2.2.2.symm ▸ (Or.inl rfl : c ∈ ({c, d} : Set S)) :
        c ∈ closure f ∩ D.V).1
      have hcV : c ∈ D.V := hl.2.2.1
      rcases ih' with h | h
      · have hfm : f ∈ H₁.edgeSet := h f (by simp)
        have hc₁ := end_mem hsep.left_le hfm hcV hcf
        refine Or.inl fun g hg => ?_
        rcases List.mem_cons.mp hg with rfl | hg
        · rcases mem_sides hsep hl.1 with h' | h'
          · exact h'
          · exact (hcp (hp c hc₁ (end_mem hsep.right_le h' hcV hce))).elim
        · exact h g hg
      · have hfm : f ∈ H₂.edgeSet := h f (by simp)
        have hc₂ := end_mem hsep.right_le hfm hcV hcf
        refine Or.inr fun g hg => ?_
        rcases List.mem_cons.mp hg with rfl | hg
        · rcases mem_sides hsep hl.1 with h' | h'
          · exact (hcp (hp c (end_mem hsep.left_le h' hcV hce) hc₂)).elim
          · exact h'
        · exact h g hg

/-- `G` is a block: in each drawing that holds `G`, all edges of `G` lie on one side of each
separation of order one. -/
def IsBlock (G : Drawing S) : Prop :=
  ∀ (D : Drawing S) (H₁ H₂ : Hypergraph S (Set S)), G.IsSubdrawing D → D.toHypergraph.IsSeparation
    H₁ H₂ →
    Hypergraph.separationOrder H₁ H₂ = 1 → (∀ e ∈ G.E, e ∈ H₁.edgeSet) ∨ (∀ e ∈ G.E, e ∈ H₂.edgeSet)

omit [T2Space S] in
theorem isBlock_of_subsingleton {G : Drawing S} (hG : G.E.Subsingleton) : IsBlock G := by
  intro D H₁ H₂ hs hsep _
  by_cases hne : G.E.Nonempty
  · obtain ⟨e, he⟩ := hne
    rcases mem_sides hsep (hs.2 he) with h | h
    · exact Or.inl fun f hf => hG hf he ▸ h
    · exact Or.inr fun f hf => hG hf he ▸ h
  · exact Or.inl fun f hf => (hne ⟨f, hf⟩).elim

omit [T2Space S] in
private theorem end_mem_tail {α β : Type*} {G : Graph α β} {a b : α} (R : GraphWalk G a b)
    (h : 0 < R.length) : b ∈ R.support.tail := by
  cases R with
  | nil _ => simp at h
  | cons _ r => simpa using r.end_mem_support

omit [T2Space S] in
/-- A circuit is a block: it can be cut only at two vertices. -/
theorem isBlock_of_isCircuit {C : Drawing S} (hC : C.IsCircuit) : IsBlock C := by
  intro D H₁ H₂ hs hsep hord
  obtain ⟨p, hp⟩ := ncard_eq_one.mp hord
  have hpp : ∀ x, x ∈ H₁.vertexSet → x ∈ H₂.vertexSet → x = p := fun x h₁ h₂ => by
    have : x ∈ (H₁ ∩ H₂).vertexSet := ⟨h₁, h₂⟩
    rw [hp] at this
    exact this
  have hsimple : ∀ v (W : GraphWalk C.toGraph v v), W.IsSimpleClosed → C.E = {e | e ∈ W.edges} →
      C.V = {x | x ∈ W.support} → (p ∈ C.V → v = p) →
      (∀ e ∈ C.E, e ∈ H₁.edgeSet) ∨ (∀ e ∈ C.E, e ∈ H₂.edgeSet) := by
    intro v W hW hE hV hvp
    obtain ⟨W', hsu, hed⟩ := hs.exists_walk_up W
    have := same_side hsep hpp W' (fun x R₁ R₂ hr h₁ h₂ hxp => by
      subst hxp
      have hxs : x ∈ W'.support := by
        rw [hr]
        exact (GraphWalk.mem_support_append _ _).mpr (Or.inr R₂.start_mem_support)
      have hvx : v = x := hvp (by rw [hV]; rw [hsu] at hxs; exact hxs)
      subst hvx
      have hnd : W'.support.tail.Nodup := by
        rw [hsu]
        exact hW.1
      rw [hr, GraphWalk.support_append, R₁.support_eq_cons] at hnd
      simp only [List.cons_append, List.tail_cons] at hnd
      exact (List.nodup_append.mp hnd).2.2 _ (end_mem_tail R₁ h₁) _ (end_mem_tail R₂ h₂) rfl)
    rw [hed] at this
    rcases this with h | h
    · exact Or.inl fun e he => h e (by rw [hE] at he; exact he)
    · exact Or.inr fun e he => h e (by rw [hE] at he; exact he)
  by_cases hpC : p ∈ C.V
  · obtain ⟨W, hW, -, hV, hE⟩ := exists_walk_at hC hpC
    exact hsimple p W hW hE hV fun _ => rfl
  · obtain ⟨v, W, hW, -, hV, hE⟩ := hC
    exact hsimple v W hW hE hV fun h => (hpC h).elim

variable {Γ : Drawing S}

theorem walkDrawing_mono {u v u' v' : S} {Z : GraphWalk Γ.toGraph u v} {Z' : GraphWalk Γ.toGraph u'
  v'}
    (hs : ∀ x ∈ Z.support, x ∈ Z'.support) (he : ∀ e ∈ Z.edges, e ∈ Z'.edges) :
    (walkDrawing Γ Z).IsSubdrawing (walkDrawing Γ Z') := by
  refine ⟨?_, ?_⟩
  · rw [walkDrawing_V, walkDrawing_V]
    exact hs
  · rw [walkDrawing_E, walkDrawing_E]
    exact he

/-- A point of `Γ | W` is a vertex of `W` or lies on an edge of `W`. -/
theorem walk_U_cases {u v : S} {W : GraphWalk Γ.toGraph u v} {z : S} (hz : z ∈
  (walkDrawing Γ W).U) :
    z ∈ W.support ∨ ∃ e ∈ W.edges, z ∈ e := by
  by_cases hV : z ∈ (walkDrawing Γ W).V
  · rw [walkDrawing_V] at hV
    exact Or.inl hV
  · rcases (mem_walkDrawing_U Γ W).mp hz with h | ⟨e, he, hze⟩
    · exact Or.inl h
    · have he' : e ∈ (walkDrawing Γ W).E := by
        rw [walkDrawing_E]
        exact he
      exact Or.inr ⟨e, he, (walkDrawing Γ W).closure_diff_V he' ▸ ⟨hze, hV⟩⟩

theorem mem_U_append {u v w : S} {P : GraphWalk Γ.toGraph u v} {Q : GraphWalk Γ.toGraph v w} {x :
  S} :
    x ∈ (walkDrawing Γ (P.append Q)).U ↔ x ∈ (walkDrawing Γ P).U ∨ x ∈ (walkDrawing Γ Q).U := by
  rw [GraphWalk.drawing_U_append, mem_union]

theorem mem_U_reverse {u v : S} {P : GraphWalk Γ.toGraph u v} {x : S} :
    x ∈ (walkDrawing Γ P.reverse).U ↔ x ∈ (walkDrawing Γ P).U := by
  simp only [mem_walkDrawing_U, GraphWalk.support_reverse, GraphWalk.edges_reverse,
    List.mem_reverse]

/-- Two blocks that share two points, each with an edge at each vertex, form a non-separable
drawing. -/
theorem isNonSeparable_walk {v₀ : S} (Z₁ Z₂ : GraphWalk Γ.toGraph v₀ v₀)
    (hb₁ : IsBlock (walkDrawing Γ Z₁)) (hb₂ : IsBlock (walkDrawing Γ Z₂))
    (hv₁ : ∀ x ∈ Z₁.support, ∃ e ∈ Z₁.edges, x ∈ closure e)
    (hv₂ : ∀ x ∈ Z₂.support, ∃ e ∈ Z₂.edges, x ∈ closure e) {x y : S} (hxy : x ≠ y)
    (hx₁ : x ∈ (walkDrawing Γ Z₁).U) (hx₂ : x ∈ (walkDrawing Γ Z₂).U)
    (hy₁ : y ∈ (walkDrawing Γ Z₁).U) (hy₂ : y ∈ (walkDrawing Γ Z₂).U) :
    (walkDrawing Γ (Z₁.append Z₂)).IsNonSeparable := by
  classical
  set Z := Z₁.append Z₂ with hZ
  have hEZ : ∀ e, e ∈ Z.edges ↔ e ∈ Z₁.edges ∨ e ∈ Z₂.edges := fun e => by
    rw [hZ, GraphWalk.edges_append, List.mem_append]
  have hSZ : ∀ x, x ∈ Z.support ↔ x ∈ Z₁.support ∨ x ∈ Z₂.support := fun x =>
    GraphWalk.mem_support_append _ _
  have hs₁ := walkDrawing_mono (Z := Z₁) (Z' := Z) (fun x h => (hSZ x).mpr (Or.inl h))
    (fun e h => (hEZ e).mpr (Or.inl h))
  have hs₂ := walkDrawing_mono (Z := Z₂) (Z' := Z) (fun x h => (hSZ x).mpr (Or.inr h))
    (fun e h => (hEZ e).mpr (Or.inr h))
  have hZsub := walkDrawing_isSubdrawing Γ Z
  refine ⟨⟨⟨v₀, by rw [walkDrawing_V]; exact Z.start_mem_support⟩, ?_⟩, ?_⟩
  · intro a ha b hb
    rw [walkDrawing_V] at ha hb
    obtain ⟨Z', hsZ, -⟩ := hZsub.exists_walk_down Z
      (by rw [walkDrawing_V]; exact fun _ h => h) (by rw [walkDrawing_E]; exact fun _ h => h)
    exact exists_walk_of_mem_support Z' (hsZ ▸ ha) (hsZ ▸ hb)
  intro H₁ H₂ hsep hord hne₁ hne₂
  obtain ⟨p, hp⟩ := ncard_eq_one.mp hord
  have hpp : ∀ x, x ∈ H₁.vertexSet → x ∈ H₂.vertexSet → x = p := fun x h₁ h₂ => by
    have : x ∈ (H₁ ∩ H₂).vertexSet := ⟨h₁, h₂⟩
    rw [hp] at this
    exact this
  have hall : ∀ {H H' : Hypergraph S (Set S)}, H' ≤ (walkDrawing Γ Z).toHypergraph →
      (∀ e, e ∈ H.edgeSet → e ∈ H'.edgeSet → False) →
      (∀ e ∈ (walkDrawing Γ Z).E, e ∈ H.edgeSet ∨ e ∈ H'.edgeSet) →
      (∀ e ∈ (walkDrawing Γ Z₁).E, e ∈ H.edgeSet) → (∀ e ∈ (walkDrawing Γ Z₂).E, e ∈ H.edgeSet) →
      H'.edgeSet.Nonempty → False := by
    intro H H' hle hnb _ h₁ h₂ ⟨e, he⟩
    have hl : H'.IsSubhypergraph (walkDrawing Γ Z).toHypergraph := hle
    have heZ : e ∈ Z.edges := by
      have := hl.edgeSet_subset he
      change e ∈ (walkDrawing Γ Z).E at this
      rwa [walkDrawing_E] at this
    rcases (hEZ e).mp heZ with h | h
    · exact hnb e (h₁ e (by rw [walkDrawing_E]; exact h)) he
    · exact hnb e (h₂ e (by rw [walkDrawing_E]; exact h)) he
  -- A point of both blocks is a vertex of both, when the blocks lie on opposite sides.
  have hcommon : ∀ {H H' : Hypergraph S (Set S)}, (∀ e, e ∈ H.edgeSet → e ∈ H'.edgeSet → False) →
      (∀ e ∈ (walkDrawing Γ Z₁).E, e ∈ H.edgeSet) → (∀ e ∈ (walkDrawing Γ Z₂).E, e ∈ H'.edgeSet) →
      ∀ z, z ∈ (walkDrawing Γ Z₁).U → z ∈ (walkDrawing Γ Z₂).U → z ∈ Z₁.support ∧ z ∈ Z₂.support
        := by
    intro H H' hnb h₁ h₂ z hz₁ hz₂
    rcases walk_U_cases hz₁ with hz₁ | ⟨e, he, hze⟩ <;> rcases walk_U_cases hz₂ with hz₂ | ⟨f, hf,
      hzf⟩
    · exact ⟨hz₁, hz₂⟩
    · exact (edge_notMem_V (mem_E_of_mem_edges Z₂ hf) hzf (mem_V_of_mem_support Z₁ hz₁)).elim
    · exact (edge_notMem_V (mem_E_of_mem_edges Z₁ he) hze (mem_V_of_mem_support Z₂ hz₂)).elim
    · obtain rfl : e = f := Γ.edge_eq_of_mem (mem_E_of_mem_edges Z₁ he)
        (mem_E_of_mem_edges Z₂ hf) hze hzf
      exact (hnb e (h₁ e (by rw [walkDrawing_E]; exact he))
        (h₂ e (by rw [walkDrawing_E]; exact hf))).elim
  have hVin : ∀ {W : GraphWalk Γ.toGraph v₀ v₀} {H : Hypergraph S (Set S)}, H ≤
    (walkDrawing Γ Z).toHypergraph →
      (∀ e ∈ W.edges, e ∈ H.edgeSet) → (∀ x ∈ W.support, ∃ e ∈ W.edges, x ∈ closure e) →
      (∀ x ∈ W.support, x ∈ Z.support) → ∀ x ∈ W.support, x ∈ H.vertexSet := by
    intro W H hle hE hv hsu x hx
    obtain ⟨e, he, hxe⟩ := hv x hx
    exact end_mem hle (hE e he) (by rw [walkDrawing_V]; exact hsu x hx) hxe
  have hnb : ∀ e, e ∈ H₁.edgeSet → e ∈ H₂.edgeSet → False := fun e h₁ h₂ => not_mem_both hsep h₁ h₂
  have hnb' : ∀ e, e ∈ H₂.edgeSet → e ∈ H₁.edgeSet → False := fun e h₁ h₂ => not_mem_both hsep h₂ h₁
  have hcov : ∀ e ∈ (walkDrawing Γ Z).E, e ∈ H₁.edgeSet ∨ e ∈ H₂.edgeSet := fun e he =>
    mem_sides hsep he
  have hcov' : ∀ e ∈ (walkDrawing Γ Z).E, e ∈ H₂.edgeSet ∨ e ∈ H₁.edgeSet := fun e he =>
    (mem_sides hsep he).symm
  have hS₁ : ∀ x ∈ Z₁.support, x ∈ Z.support := fun x h => (hSZ x).mpr (Or.inl h)
  have hS₂ : ∀ x ∈ Z₂.support, x ∈ Z.support := fun x h => (hSZ x).mpr (Or.inr h)
  have hE' : ∀ {W : GraphWalk Γ.toGraph v₀ v₀} {H : Hypergraph S (Set S)},
      (∀ e ∈ (walkDrawing Γ W).E, e ∈ H.edgeSet) → ∀ e ∈ W.edges, e ∈ H.edgeSet := fun h e he =>
    h e (by rw [walkDrawing_E]; exact he)
  rcases hb₁ _ H₁ H₂ hs₁ hsep hord with h₁ | h₁ <;> rcases hb₂ _ H₁ H₂ hs₂ hsep hord with h₂ | h₂
  · exact hall hsep.right_le hnb hcov h₁ h₂ hne₂
  · obtain ⟨a₁, a₂⟩ := hcommon hnb h₁ h₂ x hx₁ hx₂
    obtain ⟨b₁, b₂⟩ := hcommon hnb h₁ h₂ y hy₁ hy₂
    have hx' := hpp x (hVin hsep.left_le (hE' h₁) hv₁ hS₁ x a₁) (hVin hsep.right_le
      (hE' h₂) hv₂ hS₂ x a₂)
    have hy' := hpp y (hVin hsep.left_le (hE' h₁) hv₁ hS₁ y b₁) (hVin hsep.right_le
      (hE' h₂) hv₂ hS₂ y b₂)
    exact hxy (hx'.trans hy'.symm)
  · obtain ⟨a₁, a₂⟩ := hcommon hnb' h₁ h₂ x hx₁ hx₂
    obtain ⟨b₁, b₂⟩ := hcommon hnb' h₁ h₂ y hy₁ hy₂
    have hx' := hpp x (hVin hsep.left_le (hE' h₂) hv₂ hS₂ x a₂) (hVin hsep.right_le
      (hE' h₁) hv₁ hS₁ x a₁)
    have hy' := hpp y (hVin hsep.left_le (hE' h₂) hv₂ hS₂ y b₂) (hVin hsep.right_le
      (hE' h₁) hv₁ hS₁ y b₁)
    exact hxy (hx'.trans hy'.symm)
  · exact hall hsep.left_le hnb' hcov' h₁ h₂ hne₁

end Block

end GraphMinor.GM11
