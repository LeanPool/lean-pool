/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.FewCircuits
public import LeanPool.GraphMinor.GM14.RigidGood
public import LeanPool.GraphMinor.GM14.Section8a

/-!
# Claim (2) of (8.4), the case of a forest

Let `(A, Ω)` be a member of the segregation. Suppose that `H ∩ A` is a forest. The paper takes a
maximal
forest `B` of `A` with `H ∩ A ⊆ B`, and adds one edge `e` to `B`. The paper's `e` joins the two
sides of
`B` at the vertex `w`, but `B \ w` may have a third side, and then `B + e` need not join `u` and
`v`.

So we choose `B` with care. Among the good forests, we take one where the side of `u` is as large as
possible (`exists_forest_step` is the exchange that makes this side larger). This needs the fact
that
each leaf of `H ∩ A` is in `ΩBar`, which holds since `H` is rigid. Without it the step fails. For
example, let `ΩBar = {u, v, w}`, let `A` have edges `wu, wv, wt, ut, tv` with `t ∉ ΩBar`, and let
`H ∩ A` be the star `wu, wv, wt`. Then `B` is the star, and `B + e` has no `u`–`v` path off `w`
for either choice of `e`. See the correction to the proof of (8.4) in `corrections/GM14.md`.
-/


@[expose] public section

namespace GraphMinor.GM14

open Set Graph GraphMinor GraphMinor.GM09 GraphMinor.Surface GraphMinor.GM11

universe u v

variable {α : Type u} {β : Type v}

section Walks

variable {G : Graph α β}

/-- `x` and `y` are joined by a walk that misses `w`. -/
def Off (G : Graph α β) (w x y : α) : Prop := ∃ W : GraphWalk G x y, w ∉ W.support

theorem Off.ne_left {w x y : α} (h : Off G w x y) : x ≠ w := by
  obtain ⟨W, hW⟩ := h
  rintro rfl
  cases W <;> simp [GraphWalk.support] at hW

theorem Off.symm {w x y : α} (h : Off G w x y) : Off G w y x := by
  obtain ⟨W, hW⟩ := h
  exact ⟨W.reverse, by rwa [GraphWalk.support_reverse, List.mem_reverse]⟩

theorem Off.ne_right {w x y : α} (h : Off G w x y) : y ≠ w := h.symm.ne_left

theorem Off.trans {w x y z : α} (h : Off G w x y) (h' : Off G w y z) : Off G w x z := by
  obtain ⟨W, hW⟩ := h
  obtain ⟨W', hW'⟩ := h'
  refine ⟨W.append W', fun hm => ?_⟩
  rcases (GraphWalk.mem_support_append W W').mp hm with h₁ | h₁
  · exact hW h₁
  · exact hW' h₁

theorem walk_end_mem {x y : α} (W : GraphWalk G x y) : y ∈ V(G) := by
  induction W with
  | nil h => exact h
  | cons _ _ ih => exact ih

theorem Off.of_link {w x y : α} {e : β} (hl : G.IsLink e x y) (hx : x ≠ w) (hy : y ≠ w) :
    Off G w x y :=
  ⟨.cons hl (.nil hl.right_mem), by
    simp only [GraphWalk.support, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fun h => hx h.symm, fun h => hy h.symm⟩⟩

theorem Off.refl {w x : α} (hx : x ∈ V(G)) (hxw : x ≠ w) : Off G w x x :=
  ⟨.nil hx, by
    simp only [GraphWalk.support, List.mem_singleton]
    exact fun h => hxw h.symm⟩

/-- A walk off `w` from inside a set to outside has an edge that leaves the set. -/
theorem exists_exit {K : Set α} {x y : α} (W : GraphWalk G x y) (hx : x ∈ K) (hy : y ∉ K) :
    ∃ a b e, G.IsLink e a b ∧ e ∈ W.edges ∧ a ∈ W.support ∧ b ∈ W.support ∧ a ∈ K ∧ b ∉ K := by
  induction W with
  | nil _ => exact absurd hx hy
  | @cons u t b e hl rest ih =>
    by_cases ht : t ∈ K
    · obtain ⟨a', b', e', h₁, h₂, h₃, h₄, h₅, h₆⟩ := ih ht hy
      exact ⟨a', b', e', h₁, List.mem_cons_of_mem _ h₂, List.mem_cons_of_mem _ h₃,
        List.mem_cons_of_mem _ h₄, h₅, h₆⟩
    · refine ⟨u, t, e, hl, List.mem_cons_self, List.mem_cons_self, List.mem_cons_of_mem _ ?_, hx,
        ht⟩
      cases rest <;> simp [GraphWalk.support]

/-- The last step of a walk to `w`. -/
theorem exists_last_step {x w : α} (W : GraphWalk G x w) (hx : x ≠ w) :
    ∃ z f, G.IsLink f z w ∧ Off G w x z := by
  classical
  induction W with
  | nil _ => exact absurd rfl hx
  | @cons u t b e hl rest ih =>
    by_cases ht : t = b
    · subst ht
      exact ⟨u, e, hl, Off.refl hl.left_mem hx⟩
    · obtain ⟨z, f, h₁, h₂⟩ := ih ht
      exact ⟨z, f, h₁, (Off.of_link hl hx ht).trans h₂⟩

/-- An edge of a walk has its ends on the walk. -/
theorem ends_mem_support {x y : α} (W : GraphWalk G x y) {e : β} (he : e ∈ W.edges) {a b : α}
    (hl : G.IsLink e a b) : a ∈ W.support ∧ b ∈ W.support := by
  induction W with
  | nil _ => simp [GraphWalk.edges] at he
  | @cons u t c e' hl' rest ih =>
    rcases List.mem_cons.mp he with rfl | he'
    · have hs : t ∈ rest.support := by cases rest <;> simp [GraphWalk.support]
      rcases hl.eq_and_eq_or_eq_and_eq hl' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ hs⟩
      · exact ⟨List.mem_cons_of_mem _ hs, List.mem_cons_self⟩
    · obtain ⟨h₁, h₂⟩ := ih he'
      exact ⟨List.mem_cons_of_mem _ h₁, List.mem_cons_of_mem _ h₂⟩

/-- A walk whose steps are joined in `G'` gives a walk of `G'`. -/
theorem walk_lift {G' : Graph α β} (h : ∀ e a b, G.IsLink e a b → Nonempty (GraphWalk G' a b))
    (hV : V(G) ⊆ V(G')) {x y : α} (W : GraphWalk G x y) : Nonempty (GraphWalk G' x y) := by
  induction W with
  | nil hv => exact ⟨.nil (hV hv)⟩
  | cons hl _ ih =>
    obtain ⟨W₁⟩ := h _ _ _ hl
    obtain ⟨W₂⟩ := ih
    exact ⟨W₁.append W₂⟩

theorem no_circuit_mono {G₁ G₂ : Graph α β} (hle : G₁ ≤ G₂) (hno : ¬ ∃ C, IsGraphCircuit G₂ C) :
    ¬ ∃ C, IsGraphCircuit G₁ C := by
  rintro ⟨C, hC, hrest⟩
  exact hno ⟨C, hC.trans hle, hrest⟩

/-- A closed walk through `g` gives a walk between the ends of `g`. -/
theorem exists_split_edge {C : Graph α β} {a b : α} (W : GraphWalk C a b) {g : β}
    (hg : g ∈ W.edges) : ∃ p q, C.IsLink g p q ∧ ∃ (W₁ : GraphWalk C a p) (W₂ : GraphWalk C q b),
      W.edges = W₁.edges ++ g :: W₂.edges := by
  obtain ⟨p, q, h, W₁, W₂, heq⟩ := W.split_at_edge hg
  exact ⟨p, q, h, W₁, W₂, by rw [heq, GraphWalk.edges_append, GraphWalk.edges_cons]⟩

/-- Adding an edge between two parts of a forest gives a forest. -/
theorem no_circuit_insert {A : Graph α β} {Z : Set β} {g : β} {x y : α}
    (hno : ¬ ∃ C, IsGraphCircuit (A.restrict Z) C) (hl : A.IsLink g x y)
    (hnc : IsEmpty (GraphWalk (A.restrict Z) x y)) :
    ¬ ∃ C, IsGraphCircuit (A.restrict (insert g Z)) C := by
  rintro ⟨C, hle, u, W, ⟨hs, hd⟩, hlen, hV, hE⟩
  have htrans : ∀ {a b : α} (W' : GraphWalk C a b), g ∉ W'.edges →
      Nonempty (GraphWalk (A.restrict Z) a b) := by
    intro a b W' hg
    obtain ⟨W'', -, -⟩ := W'.exists_transfer (G' := A.restrict Z)
      (fun e p q he hlk => by
        have hl' := hlk.mono hle
        refine ⟨(hl'.1.resolve_left ?_), hl'.2⟩
        rintro rfl
        exact hg he)
      (fun z hz => hle.vertexSet_mono (W'.mem_vertexSet_of_mem_support hz))
    exact ⟨W''⟩
  by_cases hg : g ∈ W.edges
  · obtain ⟨p, q, h₁, W₁, W₂, h₂⟩ := exists_split_edge W hg
    rw [h₂] at hd
    have hd' := (List.nodup_cons.mp (List.nodup_middle.mp hd)).1
    have hg₁ : g ∉ W₁.edges := fun h => hd' (List.mem_append_left _ h)
    have hg₂ : g ∉ W₂.edges := fun h => hd' (List.mem_append_right _ h)
    obtain ⟨Y⟩ := htrans (W₂.append W₁) (by
      rw [GraphWalk.edges_append]
      simp [hg₁, hg₂])
    have h₃ := h₁.mono hle
    rcases hl.eq_and_eq_or_eq_and_eq h₃.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hnc.false Y.reverse
    · exact hnc.false Y
  · refine hno ⟨C, ?_, u, W, ⟨hs, hd⟩, hlen, hV, hE⟩
    refine ⟨hle.vertexSet_mono, fun e p q hlk => ?_⟩
    have he : e ∈ W.edges := by
      have : e ∈ E(C) := hlk.edge_mem
      rwa [hE] at this
    have hl' := hlk.mono hle
    refine ⟨hl'.1.resolve_left ?_, hl'.2⟩
    rintro rfl
    exact hg he

/-- An edge of a forest is a bridge. -/
theorem not_joined_of_forest {G : Graph α β} {e : β} {x y : α}
    (hno : ¬ ∃ C, IsGraphCircuit G C) (hl : G.IsLink e x y) (hxy : x ≠ y) :
    IsEmpty (GraphWalk (G.restrict {e}ᶜ) x y) := by
  refine ⟨fun W => ?_⟩
  obtain ⟨P, hP, -, hE⟩ := exists_isGraphPathWithEnds_of_walk W
  have hP' := hP.mono (restrict_le (G := G))
  have hR := isGraphPathWithEnds_edge hl hxy
  refine hno ⟨_, isGraphCircuit_subgraphUnion hP' hR hxy ?_ ?_⟩
  · have hVR : V(walkSubgraph (GraphWalk.cons hl (GraphWalk.nil hl.right_mem))) = {x, y} := by
      ext z
      simp [vertexSet_walkSubgraph, GraphWalk.support]
    rw [hVR]
    ext z
    constructor
    · exact fun h => h.2
    · rintro (rfl | rfl)
      · exact ⟨hP.left_mem, Or.inl rfl⟩
      · exact ⟨hP.right_mem, Or.inr rfl⟩
  · refine disjoint_left.mpr fun f hf hf' => ?_
    have hfe : f = e := by
      have : f ∈ E(walkSubgraph (GraphWalk.cons hl (GraphWalk.nil hl.right_mem))) := hf'
      rw [edgeSet_walkSubgraph] at this
      simpa [GraphWalk.edges] using this
    have h₁ : f ∈ E(G.restrict {e}ᶜ) := hP.1.edgeSet_mono hf
    exact ((edgeSet_restrict _ _).subset h₁).2 hfe

end Walks

section Forest

variable {A F P : Graph α β}

/-- `Z` is the edge set of a spanning forest of `A` that includes `F`. -/
structure GoodForest (A F : Graph α β) (Z : Set β) : Prop where
  hF : E(F) ⊆ Z
  hZ : Z ⊆ E(A)
  forest : ¬ ∃ C, IsGraphCircuit (A.restrict Z) C
  conn : ∀ e a b, A.IsLink e a b → Nonempty (GraphWalk (A.restrict Z) a b)

theorem GoodForest.vertexSet {Z : Set β} : V(A.restrict Z) = V(A) := rfl

theorem GoodForest.walk {Z : Set β} (h : GoodForest A F Z) {a b : α} (W : GraphWalk A a b) :
    Nonempty (GraphWalk (A.restrict Z) a b) :=
  walk_lift h.conn Subset.rfl W

theorem le_restrict {Z : Set β} (hF : F ≤ A) (hZ : E(F) ⊆ Z) : F ≤ A.restrict Z :=
  ⟨hF.vertexSet_mono, fun _ _ _ hl => ⟨hZ hl.edge_mem, hl.mono hF⟩⟩

/-- A circuit whose edges are in a subgraph is a circuit of the subgraph. -/
theorem no_circuit_restrict (hF : F ≤ A) (hno : ¬ ∃ C, IsGraphCircuit F C) :
    ¬ ∃ C, IsGraphCircuit (A.restrict E(F)) C := by
  rintro ⟨C, hle, u, W, hs, hlen, hV, hE⟩
  have hlink : ∀ {e x y}, C.IsLink e x y → F.IsLink e x y := by
    intro e x y hl
    have hl' := hl.mono hle
    exact (hF.isLink_iff hl'.1).mpr hl'.2
  have hmem : ∀ {a b : α} (W' : GraphWalk C a b), 0 < W'.length → ∀ x ∈ W'.support, x ∈ V(F) := by
    intro a b W' hl
    induction W' with
    | nil _ => simp [GraphWalk.length, GraphWalk.edges] at hl
    | @cons p t c e hlk rest ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (hlink hlk).left_mem
      · cases rest with
        | nil _ =>
          simp only [GraphWalk.support, List.mem_singleton] at hx
          subst hx
          exact (hlink hlk).right_mem
        | cons h' r' =>
          exact ih (by simp [GraphWalk.length, GraphWalk.edges]) x hx
  refine hno ⟨C, ⟨?_, fun e x y hl => hlink hl⟩, u, W, hs, hlen, hV, hE⟩
  intro x hx
  exact hmem W hlen x (hV.subset hx)

/-- There is a good forest. -/
theorem exists_goodForest (hF : F ≤ A) (hE : E(A).Finite) (hno : ¬ ∃ C, IsGraphCircuit F C) :
    ∃ Z, GoodForest A F Z := by
  classical
  let 𝓕 : Set (Set β) := {Z | E(F) ⊆ Z ∧ Z ⊆ E(A) ∧ ¬ ∃ C, IsGraphCircuit (A.restrict Z) C}
  have hfin : 𝓕.Finite := hE.finite_subsets.subset fun Z h => h.2.1
  have hne : 𝓕.Nonempty := ⟨E(F), Subset.rfl, hF.edgeSet_mono, no_circuit_restrict hF hno⟩
  obtain ⟨Z, ⟨h₁, h₂, h₃⟩, hmax⟩ := Set.exists_max_image 𝓕 ncard hfin hne
  refine ⟨Z, h₁, h₂, h₃, fun e a b hl => ?_⟩
  by_contra hnc
  have hnc' : IsEmpty (GraphWalk (A.restrict Z) a b) := not_nonempty_iff.mp hnc
  have heZ : e ∉ Z := fun heZ => hnc ⟨.cons ⟨heZ, hl⟩ (.nil hl.right_mem)⟩
  have hin : insert e Z ∈ 𝓕 := ⟨h₁.trans (subset_insert _ _), insert_subset hl.edge_mem h₂,
    no_circuit_insert h₃ hl hnc'⟩
  have := hmax _ hin
  rw [ncard_insert_of_notMem heZ (hE.subset h₂)] at this
  omega

/-- The exchange step. Take a good forest `B` with a path `P` that goes from `u` through `w` to `v`.
Let `g` be an edge from the side `K` of `u` in `B - w` to a side that has neither `u` nor `v`.
Remove the
edge from that side to `w`, and add `g`. The result is good, it holds `P`, and the side of `u` is
larger. -/
theorem exists_forest_step {S₀ : Set α} {Z : Set β} (hF : F ≤ A) (hgf : GoodForest A F Z)
    (hno : ¬ ∃ C, IsGraphCircuit F C) (hVf : V(A).Finite)
    (hleaf : ∀ t ∈ V(F), t ∉ S₀ → ∀ e, F.Inc e t → ∃ e', e' ≠ e ∧ F.Inc e' t)
    (hPA : P ≤ A) (hPZ : E(P) ⊆ Z) {u v w x y : α} {g : β} (W₁ : GraphWalk P u w)
    (hside : ∀ p ∈ V(P), p ≠ w → Off (A.restrict Z) w u p ∨ Off (A.restrict Z) w v p)
    (hxu : Off (A.restrict Z) w u x) (hl : A.IsLink g x y) (hyw : y ≠ w)
    (hyu : ¬ Off (A.restrict Z) w u y) (hyv : ¬ Off (A.restrict Z) w y v)
    (hKbar : ∀ t, Off (A.restrict Z) w y t → t ∉ S₀) :
    ∃ Z', GoodForest A F Z' ∧ E(P) ⊆ Z' ∧
      {t | Off (A.restrict Z) w u t} ⊂ {t | Off (A.restrict Z') w u t} := by
  classical
  set B := A.restrict Z with hB
  have hPB : P ≤ B := le_restrict hPA hPZ
  have hxw : x ≠ w := hxu.ne_right
  -- The side of `y`.
  obtain ⟨W₀⟩ : Nonempty (GraphWalk B y w) := by
    obtain ⟨W₁'⟩ := hgf.conn g y x hl.symm
    obtain ⟨W₂', -⟩ := hxu.symm
    obtain ⟨W₃', -, -⟩ := exists_walk_up_of_le hPB W₁
    exact ⟨(W₁'.append W₂').append W₃'⟩
  obtain ⟨z, f, hfz, hyz⟩ := exists_last_step W₀ hyw
  have hzw : z ≠ w := hyz.ne_right
  have hfZ : f ∈ Z := hfz.1
  -- Each edge of `B` that leaves the side of `y` goes to `w`.
  have hstay : ∀ e p q, B.IsLink e p q → Off B w y p → q ≠ w → Off B w y q := fun e p q h hp hq =>
    hp.trans (Off.of_link h hp.ne_right hq)
  -- The side of `y` holds a leaf of `F` if `f` is an edge of `F`.
  have hfF : f ∉ E(F) := by
    intro hfF
    let K₁ : Set α := {t | Off B w y t} ∪ {w}
    let F₁ : Graph α β := F.induce (V(F) ∩ K₁)
    have hF₁F : F₁ ≤ F := induce_le inter_subset_left
    have hfl : F.IsLink f z w := (hF.isLink_iff hfF).mpr hfz.2
    have hfl₁ : F₁.IsLink f z w := ⟨hfl, ⟨hfl.left_mem, Or.inl hyz⟩, ⟨hfl.right_mem, Or.inr rfl⟩⟩
    have hno₁ := no_circuit_mono hF₁F hno
    have hVF₁ : V(F₁).Finite := (hVf.subset hF.vertexSet_mono).subset inter_subset_left
    obtain ⟨Q, a, b, hQ, hab, hmax⟩ := exists_longest_path hVF₁ hno₁ ⟨f, hfl₁.edge_mem⟩
    -- One end of `Q` is off `w`.
    have key : ∀ {Q : Graph α β} {a b : α}, IsGraphPathWithEnds F₁ Q a b → a ≠ b → a ≠ w →
        (∀ (Q' : Graph α β) (a' b' : α), IsGraphPathWithEnds F₁ Q' a' b' →
          V(Q').ncard ≤ V(Q).ncard) → False := by
      intro Q a b hQ hab haw hmax
      have haK : a ∈ V(F) ∩ K₁ := hQ.left_mem |> hQ.1.vertexSet_mono
      have haS : Off B w y a := haK.2.resolve_right haw
      obtain ⟨hQle, W, hs, hV, hE⟩ := id hQ
      -- The first edge of `Q`.
      obtain ⟨e₁, a₁, hl₁, he₁⟩ : ∃ e₁ a₁, Q.IsLink e₁ a a₁ ∧ e₁ ∈ W.edges := by
        cases W with
        | nil _ => exact absurd rfl hab
        | cons h r => exact ⟨_, _, h, List.mem_cons_self⟩
      have hl₁F : F.IsLink e₁ a a₁ := (hl₁.mono hQle).mono hF₁F
      obtain ⟨e', hne, a', hl'⟩ := hleaf a haK.1 (hKbar a haS) e₁ ⟨a₁, hl₁F⟩
      have hle' : F₁.IsLink e' a a' := by
        refine ⟨hl', haK, hl'.right_mem, ?_⟩
        by_cases ha' : a' = w
        · exact Or.inr ha'
        · refine Or.inl (hstay e' a a' ?_ haS ha')
          exact ⟨hgf.hF hl'.edge_mem, hl'.mono hF⟩
      have he' : e' ∈ E(Q) := mem_edgeSet_of_longest hno₁ hVF₁ hQ hmax hle'
      have hQe' : Q.IsLink e' a a' := (hQle.isLink_iff he').mpr hle'
      exact hne (Whitney.edge_at_start W hs (hE.subset he') he₁ ⟨_, hQe'⟩ ⟨_, hl₁⟩)
    by_cases haw : a = w
    · have hbw : b ≠ w := fun h => hab (haw.trans h.symm)
      refine key hQ.symm hab.symm hbw fun Q' a' b' h => ?_
      exact hmax Q' a' b' h
    · exact key hQ hab haw hmax
  -- Edges of `B` other than `f` stay in the side of `y`.
  have hbridge : ∀ e p q, B.IsLink e p q → Off B w y p → ¬ Off B w y q → e = f := by
    intro e p q hlk hp hq
    by_contra hef
    have hqw : q = w := by
      by_contra hqw
      exact hq (hstay e p q hlk hp hqw)
    subst hqw
    have hpz : Off B q p z := hp.symm.trans hyz
    obtain ⟨Wp, hWp⟩ := hpz
    have hbr := not_joined_of_forest hgf.forest hlk hp.ne_right
    have hW' : ∀ e' ∈ Wp.edges, e' ≠ e := by
      rintro e' he' rfl
      exact hWp (ends_mem_support Wp he' hlk).2
    obtain ⟨Y, -, -⟩ := Wp.exists_transfer (G' := B.restrict {e}ᶜ)
      (fun e' a b he' h => ⟨hW' e' he', h⟩) (fun t ht => Wp.mem_vertexSet_of_mem_support ht)
    exact hbr.false (Y.append (.cons ⟨hef ∘ Eq.symm, hfz⟩ (.nil hfz.right_mem)))
  -- The new forest.
  have hxsplit : ¬ Off B w y x := fun h => hyu (hxu.trans h.symm)
  have hgZ : IsEmpty (GraphWalk (A.restrict (Z \ {f})) x y) := by
    refine ⟨fun Y => ?_⟩
    obtain ⟨a, b, e, h₁, -, -, -, h₅, h₆⟩ := exists_exit Y.reverse
      (show y ∈ {t | Off B w y t} from Off.refl hl.right_mem hyw) hxsplit
    have h₂ : (A.restrict (Z \ {f})).IsLink e a b := h₁
    have heZ : e ∈ Z := h₂.1.1
    exact h₂.1.2 (hbridge e a b ⟨heZ, h₂.2⟩ h₅ h₆)
  have hforest₀ : ¬ ∃ C, IsGraphCircuit (A.restrict (Z \ {f})) C :=
    no_circuit_mono (G₂ := B) ⟨le_rfl, fun e a b (h : e ∈ Z \ {f} ∧ A.IsLink e a b) =>
      (⟨h.1.1, h.2⟩ : e ∈ Z ∧ A.IsLink e a b)⟩ hgf.forest
  have hforest := no_circuit_insert hforest₀ hl hgZ
  set Z' := insert g (Z \ {f}) with hZ'
  set B' := A.restrict Z' with hB'
  have hsubZ : ∀ e ∈ Z, e ≠ f → e ∈ Z' := fun e he hef => Or.inr ⟨he, hef⟩
  have hfP : f ∉ E(P) := by
    intro hfP
    have hlP : P.IsLink f z w := (hPB.isLink_iff hfP).mpr hfz
    rcases hside z hlP.left_mem hzw with h | h
    · exact hyu (h.trans hyz.symm)
    · exact hyv (hyz.trans h.symm)
  -- Walks off `w` of `B` are walks of `B'`.
  have hoff : ∀ {p q}, Off B w p q → Off B' w p q := by
    rintro p q ⟨Wp, hWp⟩
    have hW' : ∀ e' ∈ Wp.edges, e' ≠ f := by
      rintro e' he' rfl
      exact hWp (ends_mem_support Wp he' hfz).2
    obtain ⟨Y, hs, -⟩ := Wp.exists_transfer (G' := B')
      (fun e' a b he' h => ⟨hsubZ e' h.1 (hW' e' he'), h.2⟩)
      (fun t ht => Wp.mem_vertexSet_of_mem_support ht)
    exact ⟨Y, hs ▸ hWp⟩
  have hPB' : P ≤ B' := le_restrict hPA fun e he => hsubZ e (hPZ he) (fun h => hfP (h ▸ he))
  have hconn : ∀ e a b, A.IsLink e a b → Nonempty (GraphWalk B' a b) := by
    have hB'step : ∀ e a b, B.IsLink e a b → Nonempty (GraphWalk B' a b) := by
      intro e a b hlk
      by_cases hef : e = f
      · subst hef
        rcases hlk.eq_and_eq_or_eq_and_eq hfz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · obtain ⟨Y₁, -⟩ := hoff hyz
          obtain ⟨Y₂, -⟩ := hoff hxu
          obtain ⟨Y₃, -, -⟩ := exists_walk_up_of_le hPB' W₁
          have hg' : B'.IsLink g y x := ⟨mem_insert _ _, hl.symm⟩
          exact ⟨Y₁.reverse.append ((GraphWalk.cons hg' Y₂.reverse).append Y₃)⟩
        · obtain ⟨Y₁, -⟩ := hoff hyz
          obtain ⟨Y₂, -⟩ := hoff hxu
          obtain ⟨Y₃, -, -⟩ := exists_walk_up_of_le hPB' W₁
          have hg' : B'.IsLink g y x := ⟨mem_insert _ _, hl.symm⟩
          exact ⟨(Y₁.reverse.append ((GraphWalk.cons hg' Y₂.reverse).append Y₃)).reverse⟩
      · exact ⟨.cons ⟨hsubZ e hlk.1 hef, hlk.2⟩ (.nil hlk.2.right_mem)⟩
    intro e a b hlk
    obtain ⟨Y⟩ := hgf.conn e a b hlk
    exact walk_lift hB'step Subset.rfl Y
  refine ⟨Z', ⟨fun e he => hsubZ e (hgf.hF he) (fun h => hfF (h ▸ he)),
    insert_subset hl.edge_mem (sdiff_subset.trans hgf.hZ), hforest, hconn⟩,
    fun e he => hsubZ e (hPZ he) (fun h => hfP (h ▸ he)), fun t ht => hoff ht, fun hsub => hyu ?_⟩
  have hy' : Off B' w u y := (hoff hxu).trans (Off.of_link ⟨mem_insert _ _, hl⟩ hxw hyw)
  exact hsub hy'

/-- A vertex of a path, off the far end, is joined to the near end by a walk off the far end. -/
theorem off_of_path {G B R : Graph α β} {a b p : α} (hR : IsGraphPathWithEnds G R a b)
    (hle : R ≤ B) (hp : p ∈ V(R)) (hpb : p ≠ b) : Off B b a p := by
  obtain ⟨R₁, R₂, hR₁R, -, hR₁, hR₂, -, hcap, -⟩ := hR.exists_split_at hp
  obtain ⟨-, W, -, hV, -⟩ := hR₁
  obtain ⟨Y, hs, -⟩ := exists_walk_up_of_le (hR₁R.trans hle) W
  refine ⟨Y, fun hb => ?_⟩
  rw [hs] at hb
  have h₁ : b ∈ V(R₁) := hV ▸ hb
  have h₂ : b ∈ V(R₁) ∩ V(R₂) := ⟨h₁, hR₂.right_mem⟩
  rw [hcap] at h₂
  exact hpb h₂.symm

private theorem first_subpath_has_two_boundary_vertices
    {S₀ : Society α β} {P P₁ P₂ : Graph α β} {u v w : α}
    (hu : u ∈ S₀.Ω.bar) (hwbar : w ∈ S₀.Ω.bar) (hwv : w ≠ v)
    (hbar : ∀ t ∈ S₀.Ω.bar, t = u ∨ t = v ∨ t = w)
    (hP₁ : IsGraphPathWithEnds P P₁ u w) (hP₂ : IsGraphPathWithEnds P P₂ w v)
    (hcap : V(P₁) ∩ V(P₂) = {w}) :
    V(P₁) ∩ S₀.Ω.bar = {u, w} := by
  ext t
  constructor
  · rintro ⟨h₁, h₂⟩
    rcases hbar t h₂ with rfl | rfl | rfl
    · exact Or.inl rfl
    · have : t ∈ V(P₁) ∩ V(P₂) := ⟨h₁, hP₂.right_mem⟩
      rw [hcap] at this
      exact absurd this.symm hwv
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨hP₁.left_mem, hu⟩
    · exact ⟨hP₁.right_mem, hwbar⟩

private theorem last_subpath_has_two_boundary_vertices
    {S₀ : Society α β} {P P₁ P₂ : Graph α β} {u v w : α}
    (hv : v ∈ S₀.Ω.bar) (hwbar : w ∈ S₀.Ω.bar) (hwu : w ≠ u)
    (hbar : ∀ t ∈ S₀.Ω.bar, t = u ∨ t = v ∨ t = w)
    (hP₁ : IsGraphPathWithEnds P P₁ u w) (hP₂ : IsGraphPathWithEnds P P₂ w v)
    (hcap : V(P₁) ∩ V(P₂) = {w}) :
    V(P₂) ∩ S₀.Ω.bar = {w, v} := by
  ext t
  constructor
  · rintro ⟨h₁, h₂⟩
    rcases hbar t h₂ with rfl | rfl | rfl
    · have : t ∈ V(P₁) ∩ V(P₂) := ⟨hP₁.left_mem, h₁⟩
      rw [hcap] at this
      exact absurd this.symm hwu
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rintro (rfl | rfl)
    · exact ⟨hP₂.left_mem, hwbar⟩
    · exact ⟨hP₂.right_mem, hv⟩

private theorem retained_paths_preserve_boundary_pairs
    {S₀ : Society α β} {P P₁ P₂ : Graph α β} {u v w : α}
    (hbar : ∀ t ∈ S₀.Ω.bar, t = u ∨ t = v ∨ t = w)
    (hP₁ : IsGraphPathWithEnds P P₁ u w) (hP₂ : IsGraphPathWithEnds P P₂ w v)
    (hbarP₁ : V(P₁) ∩ S₀.Ω.bar = {u, w})
    (hbarP₂ : V(P₂) ∩ S₀.Ω.bar = {w, v}) :
    ∀ {G' : Graph α β}, P ≤ G' → (∃ R, IsGraphPathWithEnds G' R u v ∧ V(R) ∩ S₀.Ω.bar = {u, v}) →
      (∃ R, IsGraphPathWithEnds G' R v u ∧ V(R) ∩ S₀.Ω.bar = {v, u}) → PreservesBarPaths S₀ G' := by
  intro G' hG' h₁ h₂ a ha b hb hab _
  have h₃ : IsGraphPathWithEnds G' P₁ u w := hP₁.mono hG'
  have h₄ : IsGraphPathWithEnds G' P₂ w v := hP₂.mono hG'
  rcases hbar a ha with rfl | rfl | rfl <;> rcases hbar b hb with rfl | rfl | rfl
  · exact absurd rfl hab
  · exact h₁
  · exact ⟨P₁, h₃, hbarP₁⟩
  · exact h₂
  · exact absurd rfl hab
  · exact ⟨P₂, h₄.symm, by rw [hbarP₂, pair_comm]⟩
  · exact ⟨P₁, h₃.symm, by rw [hbarP₁, pair_comm]⟩
  · exact ⟨P₂, h₄, hbarP₂⟩
  · exact absurd rfl hab

/-- **Claim (2) of (8.4), when `H ∩ A` is a forest.** -/
theorem few_circuits_of_forest {S₀ : Society α β} (hF : F ≤ S₀.G) (hBar3 : S₀.Ω.bar.ncard ≤ 3)
    (hClaim1 : ∀ A' : Graph α β, A' ≤ S₀.G → S₀.Ω.bar ⊆ V(A') →
      F ≤ A' → E(A').Nonempty → PreservesBarPaths S₀ A' → A' = S₀.G)
    (hno : ¬ ∃ C, IsGraphCircuit F C)
    (hleaf : ∀ t ∈ V(F), t ∉ S₀.Ω.bar → ∀ e, F.Inc e t → ∃ e', e' ≠ e ∧ F.Inc e' t) :
    {C : Graph α β | IsGraphCircuit S₀.G C}.ncard ≤ 1 := by
  classical
  set A := S₀.G with hA
  have hbarV : S₀.Ω.bar ⊆ V(A) := S₀.bar_subset
  have hVf : V(A).Finite := S₀.finite_V
  have hEf : E(A).Finite := S₀.finite_E
  obtain ⟨Z₀, hZ₀⟩ := exists_goodForest hF hEf hno
  by_cases hZne : Z₀.Nonempty
  swap
  · -- The case `E(B) = ∅`: every edge of `A` is a loop, and by (1), `|E(A)| ≤ 1`.
    have hZe : Z₀ = ∅ := not_nonempty_iff_eq_empty.mp hZne
    refine ncard_circuits_le_one_of_ncard_edges_le_one fun g hg g' hg' => ?_
    have hA' : A.restrict {g} = A := by
      refine hClaim1 _ restrict_le hbarV (le_restrict hF ?_) ⟨g, ?_⟩ ?_
      · have := hZ₀.hF
        rw [hZe] at this
        exact this.trans (empty_subset _)
      · exact (edgeSet_restrict _ _).superset ⟨hg, rfl⟩
      · rintro u - v - huv ⟨Q, hQ, -⟩
        exfalso
        obtain ⟨hle, W, -⟩ := hQ
        obtain ⟨Y, -, -⟩ := exists_walk_up_of_le hle W
        obtain ⟨Y'⟩ := hZ₀.walk Y
        cases Y' with
        | nil _ => exact huv rfl
        | cons h _ =>
          have := h.1
          rw [hZe] at this
          exact this
    have h' : g' ∈ E(A.restrict {g}) := hA'.symm ▸ hg'
    exact ((edgeSet_restrict _ _).subset h').2.symm
  by_cases hpres : PreservesBarPaths S₀ (A.restrict Z₀)
  · have hEne : E(A.restrict Z₀).Nonempty := by
      obtain ⟨g, hg⟩ := hZne
      exact ⟨g, (edgeSet_restrict _ _).superset ⟨hZ₀.hZ hg, hg⟩⟩
    have hAB := hClaim1 _ restrict_le hbarV (le_restrict hF hZ₀.hF) hEne hpres
    refine ncard_circuits_le_one_of_no_circuits ?_
    have := hZ₀.forest
    rwa [hAB] at this
  -- There are `u, v` joined in `A` but not in `B`.
  unfold PreservesBarPaths at hpres
  push Not at hpres
  obtain ⟨u, hu, v, hv, huv, ⟨Q, hQ, hQbar⟩, hnotB⟩ := hpres
  obtain ⟨hQle, WQ, -, hVQ, -⟩ := id hQ
  obtain ⟨WQ', hWQs, -⟩ := exists_walk_up_of_le hQle WQ
  obtain ⟨Y⟩ := hZ₀.walk WQ'
  obtain ⟨P, hP, -, -⟩ := exists_isGraphPathWithEnds_of_walk Y
  obtain ⟨w, hwP, hwbar, hwu, hwv⟩ : ∃ w ∈ V(P), w ∈ S₀.Ω.bar ∧ w ≠ u ∧ w ≠ v := by
    by_contra hcon
    push Not at hcon
    refine hnotB P hP ?_
    ext t
    constructor
    · rintro ⟨h₁, h₂⟩
      by_cases htu : t = u
      · exact Or.inl htu
      · exact Or.inr (hcon t h₁ h₂ htu)
    · rintro (rfl | rfl)
      · exact ⟨hP.left_mem, hu⟩
      · exact ⟨hP.right_mem, hv⟩
  have hbar : ∀ t ∈ S₀.Ω.bar, t = u ∨ t = v ∨ t = w := by
    have hfinbar : S₀.Ω.bar.Finite := hVf.subset hbarV
    have hsub : ({u, v, w} : Set α) ⊆ S₀.Ω.bar := by
      rintro t (rfl | rfl | rfl)
      · exact hu
      · exact hv
      · exact hwbar
    have hc : ({u, v, w} : Set α).ncard = 3 := by
      rw [ncard_insert_of_notMem (by simp [huv, hwu.symm]) (by simp), ncard_pair hwv.symm]
    have heq := eq_of_subset_of_ncard_le hsub (by omega) hfinbar
    intro t ht
    rw [← heq] at ht
    exact ht
  -- The good forests that hold `P`.
  have hPZ₀ : E(P) ⊆ Z₀ := fun e he => ((edgeSet_restrict _ _).subset (hP.1.edgeSet_mono he)).2
  have hPA : IsGraphPathWithEnds A P u v := hP.mono restrict_le
  obtain ⟨P₁, P₂, hP₁P, hP₂P, hP₁, hP₂, hun, hcap, -⟩ := hPA.exists_split_at hwP
  let 𝓒 : Set (Set β) := {Z | GoodForest A F Z ∧ E(P) ⊆ Z}
  have hfin : 𝓒.Finite := hEf.finite_subsets.subset fun Z h => h.1.hZ
  obtain ⟨Z, ⟨hgf, hPZ⟩, hmax⟩ := Set.exists_max_image 𝓒
    (fun Z => {t | Off (A.restrict Z) w u t}.ncard) hfin ⟨Z₀, hZ₀, hPZ₀⟩
  set B := A.restrict Z with hB
  have hPB : P ≤ B := le_restrict hPA.1 hPZ
  have hbarP₁ : V(P₁) ∩ S₀.Ω.bar = {u, w} := by
    exact first_subpath_has_two_boundary_vertices (S₀ := S₀) hu hwbar hwv hbar hP₁ hP₂ hcap
  have hbarP₂ : V(P₂) ∩ S₀.Ω.bar = {w, v} := by
    exact last_subpath_has_two_boundary_vertices (S₀ := S₀) hv hwbar hwu hbar hP₁ hP₂ hcap
  have hVPun : V(P) = V(P₁) ∪ V(P₂) := by
    rw [← vertexSet_subgraphUnion P P₁ P₂, hun]
  have hside : ∀ p ∈ V(P), p ≠ w → Off B w u p ∨ Off B w v p := by
    intro p hp hpw
    rcases hVPun.subset hp with h | h
    · exact Or.inl (off_of_path hP₁ (hP₁P.trans hPB) h hpw)
    · exact Or.inr (off_of_path hP₂.symm (hP₂P.trans hPB) h hpw)
  -- The cases of a pair of vertices of `ΩBar`.
  have hpairs : ∀ {G' : Graph α β}, P ≤ G' →
      (∃ R, IsGraphPathWithEnds G' R u v ∧ V(R) ∩ S₀.Ω.bar = {u, v}) →
      (∃ R, IsGraphPathWithEnds G' R v u ∧ V(R) ∩ S₀.Ω.bar = {v, u}) →
      PreservesBarPaths S₀ G' := by
    exact retained_paths_preserve_boundary_pairs (S₀ := S₀) hbar hP₁ hP₂ hbarP₁ hbarP₂
  have hEB : E(B).Nonempty := by
    have huE : E(P).Nonempty := by
      obtain ⟨-, W, -, -, hE⟩ := hP
      cases W with
      | nil _ => exact absurd rfl huv
      | cons h _ => exact ⟨_, hE.superset (List.mem_cons_self)⟩
    obtain ⟨e, he⟩ := huE
    exact ⟨e, hPB.edgeSet_mono he⟩
  by_cases hoff : Off B w u v
  · -- The forest `B` keeps all the pairs, so `A = B`.
    obtain ⟨X, hX⟩ := hoff
    obtain ⟨R, hR, hRV, -⟩ := exists_isGraphPathWithEnds_of_walk X
    have hRbar : V(R) ∩ S₀.Ω.bar = {u, v} := by
      ext t
      constructor
      · rintro ⟨h₁, h₂⟩
        rcases hbar t h₂ with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd (hRV h₁) hX
      · rintro (rfl | rfl)
        · exact ⟨hR.left_mem, hu⟩
        · exact ⟨hR.right_mem, hv⟩
    have hp := hpairs hPB ⟨R, hR, hRbar⟩ ⟨R, hR.symm, by rw [hRbar, pair_comm]⟩
    have hAB := hClaim1 _ restrict_le hbarV (le_restrict hF hgf.hF) hEB hp
    refine ncard_circuits_le_one_of_no_circuits ?_
    have := hgf.forest
    rwa [hAB] at this
  -- Take the first edge of the path of `A` that leaves the side of `u`.
  have hwQ : w ∉ WQ'.support := by
    intro h
    have h₁ : w ∈ V(Q) := by
      rw [hVQ]
      exact (hWQs ▸ h : w ∈ WQ.support)
    have h₂ : w ∈ V(Q) ∩ S₀.Ω.bar := ⟨h₁, hwbar⟩
    rw [hQbar] at h₂
    rcases h₂ with h₃ | h₃
    · exact hwu h₃
    · exact hwv h₃
  obtain ⟨a, b, e, hl, -, ha, hb, haK, hbK⟩ := exists_exit WQ' (K := {t | Off B w u t})
    (Off.refl (hbarV hu) hwu.symm) hoff
  have hbw : b ≠ w := fun h => hwQ (h ▸ hb)
  have haw : a ≠ w := fun h => hwQ (h ▸ ha)
  by_cases hbv : Off B w b v
  · -- The paper's edge: `B + e` keeps all the pairs, so `A = B + e`.
    have hle : B ≤ A.restrict (insert e Z) :=
      ⟨le_rfl, fun e' p q (h : e' ∈ Z ∧ A.IsLink e' p q) =>
        (⟨Or.inr h.1, h.2⟩ : e' ∈ insert e Z ∧ A.IsLink e' p q)⟩
    obtain ⟨X₁, hX₁⟩ := id haK
    obtain ⟨X₂, hX₂⟩ := hbv
    obtain ⟨R₁, hR₁, hR₁V, -⟩ := exists_isGraphPathWithEnds_of_walk X₁
    obtain ⟨R₂, hR₂, hR₂V, -⟩ := exists_isGraphPathWithEnds_of_walk X₂
    have hsub : ∀ {R : Graph α β}, (∀ t ∈ V(R), t ≠ w) → V(R) ∩ S₀.Ω.bar ⊆ {u, v} := by
      rintro R hR t ⟨h₁, h₂⟩
      rcases hbar t h₂ with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h (hR t h₁)
    have h₁ : ∀ t ∈ V(R₁), t ≠ w := fun t ht h => hX₁ (h ▸ hR₁V ht)
    have h₂ : ∀ t ∈ V(R₂), t ≠ w := fun t ht h => hX₂ (h ▸ hR₂V ht)
    have hl' : (A.restrict (insert e Z)).IsLink e a b := ⟨mem_insert _ _, hl⟩
    have hp := hpairs (hPB.trans hle)
      (exists_bar_chord_of_link_between_branches hu hv (hR₁.mono hle) (hsub h₁) hl'
        (hR₂.mono hle) (hsub h₂))
      (exists_bar_chord_of_link_between_branches hv hu (hR₂.mono hle).symm
        (by rw [pair_comm]; exact hsub h₂) hl'.symm (hR₁.mono hle).symm
        (by rw [pair_comm]; exact hsub h₁))
    have hEA' : E(A.restrict (insert e Z)).Nonempty := hEB.mono hle.edgeSet_mono
    have hAe := hClaim1 _ restrict_le hbarV ((le_restrict hF hgf.hF).trans hle) hEA' hp
    have hab : a ≠ b := fun h => hbK (h ▸ haK)
    refine ncard_circuits_le_one_of_insert_edge (B := B) (e := e) restrict_le hgf.forest hl hab rfl
      ?_
    intro t ht
    have ht' : t ∈ E(A.restrict (insert e Z)) := hAe.symm ▸ ht
    rcases ((edgeSet_restrict _ _).subset ht').2 with rfl | h
    · exact mem_insert _ _
    · exact Or.inr ((edgeSet_restrict _ _).superset ⟨ht, h⟩)
  · -- A third side: exchange, and the side of `u` grows.
    exfalso
    obtain ⟨W₁, -, -, -⟩ : ∃ W₁ : GraphWalk P u w, True ∧ True ∧ True := by
      obtain ⟨-, W₁, -⟩ := hP₁
      obtain ⟨Y₁, -, -⟩ := exists_walk_up_of_le hP₁P W₁
      exact ⟨Y₁, trivial, trivial, trivial⟩
    have hKbar : ∀ t, Off B w b t → t ∉ S₀.Ω.bar := by
      intro t ht ht'
      rcases hbar t ht' with rfl | rfl | rfl
      · exact hbK ht.symm
      · exact hbv ht
      · exact ht.ne_right rfl
    obtain ⟨Z', hZ', hPZ', hss⟩ := exists_forest_step (S₀ := S₀.Ω.bar) hF hgf hno hVf hleaf hPA.1
      hPZ
      W₁ hside haK hl hbw hbK hbv hKbar
    have hfinS : {t | Off (A.restrict Z') w u t}.Finite := hVf.subset fun t ht => by
      obtain ⟨X, -⟩ := ht
      exact (show t ∈ V(A.restrict Z') from walk_end_mem X)
    have hlt := ncard_lt_ncard hss hfinS
    exact absurd (hmax Z' ⟨hZ', hPZ'⟩) (not_le.mpr hlt)

end Forest

/-- Graph Minors XIV, (8.4), Claim (2) (page 42):
"For each $(A, \Omega) \in \mathscr{S}$ either $A \subseteq H$ or $A$ has at most one circuit."
Proved from Claim (1). If `H ∩ A` has a circuit `C`, three disjoint paths from `V(C)` to `ΩBar`
imply
that `A' = H ∩ A` satisfies the conditions of Claim (1), so `A = H ∩ A`. Otherwise `H ∩ A` is a
forest,
and this is `few_circuits_of_forest`. The hypothesis `hleaf` says that each leaf of `H ∩ A` is in
`ΩBar`;
it follows from the rigidity of `H`, and the claim fails without it. -/
theorem claim_2_of_8_4 {α : Type u} {β : Type v}
    {S₀ : Society α β} {H_inter_A : Graph α β}
    (hHA : H_inter_A ≤ S₀.G)
    (hBar3 : S₀.Ω.bar.ncard ≤ 3)
    (hClaim1 : ∀ A' : Graph α β, A' ≤ S₀.G → S₀.Ω.bar ⊆ V(A') →
      H_inter_A ≤ A' → E(A').Nonempty → PreservesBarPaths S₀ A' → A' = S₀.G)
    (hCircuit : ∀ C : Graph α β, IsGraphCircuit H_inter_A C →
      ∃ (P : Fin 3 → Graph α β) (x y : Fin 3 → α),
        (∀ i, IsFromToPathWithEnds H_inter_A (P i) V(C) S₀.Ω.bar (x i) (y i)) ∧
        Pairwise (fun i j => Disjoint V(P i) V(P j)))
    (hleaf : ∀ t ∈ V(H_inter_A), t ∉ S₀.Ω.bar → ∀ e, H_inter_A.Inc e t →
      ∃ e', e' ≠ e ∧ H_inter_A.Inc e' t) :
    S₀.G = H_inter_A ∨ {C : Graph α β | IsGraphCircuit S₀.G C}.ncard ≤ 1 := by
  by_cases hcirc : ∃ C : Graph α β, IsGraphCircuit H_inter_A C
  · obtain ⟨C, hC⟩ := hcirc
    obtain ⟨P, x, y, hP, hDisj⟩ := hCircuit C hC
    obtain ⟨hbar, hE, hpres⟩ :=
      preservesBarPaths_of_three_disjoint_paths_from_circuit hBar3 hC hP hDisj
    exact Or.inl (hClaim1 H_inter_A hHA hbar le_rfl hE hpres).symm
  · exact Or.inr (few_circuits_of_forest hHA hBar3 hClaim1 hcirc hleaf)

end GraphMinor.GM14
