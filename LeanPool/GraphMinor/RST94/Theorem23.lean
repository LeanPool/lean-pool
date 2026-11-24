/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.RST94.Section5f
public import LeanPool.GraphMinor.GM16.Cited
public import LeanPool.GraphMinor.GM16.Section7
import Mathlib.Tactic.Positivity

/-!
# (2.3) of "Quickly excluding a planar graph", in the form XVI cites

Sets as in (5.1) (page 339) give a grid minor (`grid_model`), and `𝒯` dominates it in the sense XVI
uses (`no_row`). This is the proof of (5.1), with the sides of the separation swapped as in the
docstring of `GM16.RST94Theorem23Statement`. Together with (5.7) this proves the statement.
-/

@[expose] public section

namespace GraphMinor.RST94

open Hypergraph GM10 Set Graph

variable {α β : Type*}

theorem link_of_adj {G : Graph α β} {hV : V(G).Finite} {hE : E(G).Finite} {x y : α} (h :
  (Hypergraph.ofGraph G hV hE).skeleton.Adj x y) : ∃ f, G.IsLink f x y := by
  obtain ⟨hne, f, ⟨a, ha⟩, ⟨b, hb⟩⟩ := h
  refine ⟨f, ?_⟩
  rcases hb.left_eq_or_eq ha with rfl | rfl
  · exact absurd rfl hne
  · exact ha

/-- A connected set in the hypergraph gives a connected induced graph, when the deleted edges do not
lie inside the set. -/
theorem graphConnected_of_conn {G : Graph α β} {hV : V(G).Finite} {hE : E(G).Finite} {X : Set α} {F
  : Set β} (hX : Conn (Hypergraph.ofGraph G hV hE) X) (hF : ∀ f ∈ F, ∀ x y, G.IsLink f x y → x ∈ X
    → y ∉ X) :
    GraphConnected ((G.deleteEdges F).induce X) := by
  refine ⟨hX.1, fun x hx y hy => ?_⟩
  obtain ⟨w, hw⟩ := hX.2 x hx y hy
  induction w with
  | nil => exact Relation.ReflTransGen.refl
  | @cons a b c h q ih =>
    refine Relation.ReflTransGen.head ?_ (ih (hw b (by simp)) hy fun t ht => hw t (by simp [ht]))
    obtain ⟨f, hf⟩ := link_of_adj h
    have ha := hw a (by simp)
    have hb := hw b (by simp)
    refine ⟨f, ?_⟩
    simp only [induce_isLink, deleteEdges_isLink]
    exact ⟨⟨hf, fun hfF => hF f hfF a b hf ha hb⟩, ha, hb⟩

/-- The grid minor made from sets as in (5.1). -/
theorem grid_model {G : Graph α β} {hV : V(G).Finite} {hE : E(G).Finite} {T : Set
  (Hypergraph α β × Hypergraph α β)} {θ g : ℕ} {W : ℕ → ℕ → Set α} (hW : IsGrid
    (Hypergraph.ofGraph G hV hE) T θ g W) (hg : 2 ≤ g) :
    ∃ ηe : Sym2 (Fin g × Fin g) → β, IsMinorModel (GM01.gridGraph g) G (fun u => W u.1 u.2) ηe ∧
      ∀ e ∈ E(GM01.gridGraph g), ∃ u v x y, e = s(u, v) ∧ u ≠ v ∧ x ∈ W u.1 u.2 ∧ y ∈ W v.1 v.2
        ∧ G.IsLink (ηe e) x y := by
  classical
  have hdisj : ∀ u v : Fin g × Fin g, u ≠ v → Disjoint (W u.1 u.2) (W v.1 v.2) := fun u v hne =>
    hW.disj _ u.1.2 _ u.2.2 _ v.1.2 _ v.2.2 fun e => hne (Prod.ext (Fin.ext (Prod.ext_iff.1 e).1)
      (Fin.ext (Prod.ext_iff.1 e).2))
  have hadj : ∀ u v : Fin g × Fin g, (SimpleGraph.pathGraph g □ SimpleGraph.pathGraph g).Adj u v
    → ∃ x ∈ W u.1 u.2, ∃ y ∈ W v.1 v.2, ∃ f, G.IsLink f x y := by
    have key : ∀ (a b : ℕ) (c : ℕ), c < g → b = a + 1 → b < g → (∃ x ∈ W a c, ∃ y ∈ W b c, ∃ f,
      G.IsLink f x y) ∧ ∃ x ∈ W c a, ∃ y ∈ W c b, ∃ f, G.IsLink f x y := by
      rintro a _ c hc rfl hb
      obtain ⟨x, hx, y, hy, hxy⟩ := hW.col a hb c hc
      obtain ⟨x', hx', y', hy', hxy'⟩ := hW.row c hc a hb
      exact ⟨⟨x, hx, y, hy, link_of_adj hxy⟩, x', hx', y', hy', link_of_adj hxy'⟩
    have hsym : ∀ {a b : Set α}, (∃ x ∈ a, ∃ y ∈ b, ∃ f, G.IsLink f x y)
      → ∃ x ∈ b, ∃ y ∈ a, ∃ f, G.IsLink f x y := fun ⟨x, hx, y, hy, f, hf⟩
        => ⟨y, hy, x, hx, f, hf.symm⟩
    rintro ⟨u₁, u₂⟩ ⟨v₁, v₂⟩ h
    rw [SimpleGraph.boxProd_adj] at h
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · simp only at h₁ h₂
      subst h₂
      rcases SimpleGraph.pathGraph_adj.1 h₁ with h | h
      · exact (key u₁.1 v₁.1 u₂.1 u₂.2 h.symm v₁.2).1
      · exact hsym (key v₁.1 u₁.1 u₂.1 u₂.2 h.symm u₁.2).1
    · simp only at h₁ h₂
      subst h₂
      rcases SimpleGraph.pathGraph_adj.1 h₁ with h | h
      · exact (key u₂.1 v₂.1 u₁.1 u₁.2 h.symm v₂.2).2
      · exact hsym (key v₂.1 u₂.1 u₁.1 u₁.2 h.symm u₂.2).2
  have hch : ∀ e : Sym2 (Fin g × Fin g), ∃ f, e ∈ E(GM01.gridGraph g) → ∃ u v x y, e = s(u, v)
    ∧ u ≠ v ∧ x ∈ W u.1 u.2 ∧ y ∈ W v.1 v.2 ∧ G.IsLink f x y := fun e => by
    by_cases he : e ∈ E(GM01.gridGraph g)
    · induction e with
      | _ u v =>
        have hAdj : (SimpleGraph.pathGraph g □ SimpleGraph.pathGraph g).Adj u v := he
        obtain ⟨x, hx, y, hy, f, hf⟩ := hadj u v hAdj
        exact ⟨f, fun _ => ⟨u, v, x, y, rfl, hAdj.ne, hx, hy, hf⟩⟩
    · obtain ⟨x₀, -, y₀, -, h₀⟩ := hW.row 0 (by omega) 0 (by omega)
      obtain ⟨f₀, -⟩ := link_of_adj h₀
      exact ⟨f₀, fun h => absurd h he⟩
  choose ηe hηe using hch
  have hsame : ∀ {u u' : Fin g × Fin g} {x : α}, x ∈ W u.1 u.2 → x ∈ W u'.1 u'.2 → u = u'
    := fun {u u' x} h h' => by
    by_contra hne
    exact disjoint_left.1 (hdisj u u' hne) h h'
  have hinc : ∀ {e u v}, e ∈ E(GM01.gridGraph g) → e = s(u, v) → ∀ w,
    (GM01.gridGraph g).Inc e w ↔ w = u ∨ w = v := fun {e u v} he heq w => by
    constructor
    · rintro ⟨z, hz, -⟩
      rcases Sym2.eq_iff.1 (heq.symm.trans hz) with ⟨h, -⟩ | ⟨-, h⟩
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rintro (rfl | rfl)
      · exact ⟨v, heq, he⟩
      · exact ⟨u, heq.trans Sym2.eq_swap, he⟩
  refine ⟨ηe, ⟨fun v _ => (hW.conn _ v.1.2 _ v.2.2).1, fun v _ => hW.sub _ v.1.2 _ v.2.2, fun e he
    => ?_, fun v₁ _ v₂ _ hne => hdisj v₁ v₂ hne, fun e₁ he₁ e₂ he₂ hee => ?_, fun w _ e he
      => ?_, fun w _ e he => ?_, fun v _ => ?_⟩, hηe⟩
  · obtain ⟨_, _, _, _, -, -, -, -, h⟩ := hηe e he
    exact h.edge_mem
  · obtain ⟨u, v, x, y, rfl, -, hx, hy, h⟩ := hηe e₁ he₁
    obtain ⟨u', v', x', y', rfl, -, hx', hy', h'⟩ := hηe e₂ he₂
    rw [← hee] at h'
    rcases h.eq_and_eq_or_eq_and_eq h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hsame hx hx', hsame hy hy']
    · rw [hsame hx hy', hsame hy hx', Sym2.eq_swap]
  · obtain ⟨u, v, x, y, heq, -, hx, hy, h⟩ := hηe e he
    rw [hinc he heq w]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨x, hx, h.inc_left⟩
      · exact ⟨y, hy, h.inc_right⟩
    · rintro ⟨x', hx', hinc'⟩
      rcases hinc'.eq_or_eq_of_isLink h with rfl | rfl
      · exact Or.inl (hsame hx' hx)
      · exact Or.inr (hsame hx' hy)
  · obtain ⟨u, v, x, y, heq, hne, hx, hy, h⟩ := hηe e he
    constructor
    · rintro ⟨h₁, h₂⟩
      exfalso
      obtain h₃ := Sym2.eq_iff.1 (heq.symm.trans h₁)
      rcases h₃ with ⟨rfl, h₄⟩ | ⟨rfl, h₄⟩
      · exact hne h₄.symm
      · exact hne h₄.symm
    · intro hall
      exact absurd ((hsame (hall x h.inc_left) hx).symm.trans (hsame (hall y h.inc_right) hy)) hne
  · refine ⟨(G.deleteEdges (ηe '' E(GM01.gridGraph g))).induce (W v.1 v.2), induce_le
      (hW.sub _ v.1.2 _ v.2.2), rfl, graphConnected_of_conn (hW.conn _ v.1.2 _ v.2.2) ?_⟩
    rintro _ ⟨e, he, rfl⟩ a b hab ha hb
    obtain ⟨u, v', x, y, -, hne, hx, hy, h⟩ := hηe e he
    rcases hab.eq_and_eq_or_eq_and_eq h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hne ((hsame hx ha).trans (hsame hb hy))
    · exact hne ((hsame hx hb).trans (hsame ha hy))

/-- The proof of (5.1) (page 339), for a separation `(A, B)` of `𝒯` with `E(A)` containing a row. -/
theorem no_row {G : Graph α β} {hV : V(G).Finite} {hE : E(G).Finite} {T : Set
  (Hypergraph α β × Hypergraph α β)} {θ g : ℕ} {W : ℕ → ℕ → Set α} (hT : IsTangle
    (Hypergraph.ofGraph G hV hE) θ T)
    (hW : IsGrid (Hypergraph.ofGraph G hV hE) T θ g W) (hg : 2 ≤ g) {ηe : Sym2 (Fin g × Fin g) → β}
    (hηe : ∀ e ∈ E(GM01.gridGraph g), ∃ u v x y, e = s(u, v) ∧ u ≠ v ∧ x ∈ W u.1 u.2
      ∧ y ∈ W v.1 v.2 ∧ G.IsLink (ηe e) x y) {A B : Hypergraph α β} (hAB : (A, B) ∈ T)
        (hord : separationOrder A B < g)
    (i : Fin g) (hrow : ηe '' (GM10.gridRowPath g i).edgeSet ⊆ A.edgeSet) : False := by
  classical
  have hs := hT.isSeparation hAB
  have hmeet : ∀ j, (hj : j < g) → ∃ x ∈ W i j, x ∈ A.vertexSet := fun j hj => by
    obtain ⟨j', hj', hd⟩ : ∃ j', ∃ _ : j' < g, j + 1 = j' ∨ j' + 1 = j := by
      rcases Nat.lt_or_ge (j + 1) g with h | h
      · exact ⟨j + 1, h, Or.inl rfl⟩
      · exact ⟨j - 1, by omega, Or.inr (by omega)⟩
    let u : Fin g × Fin g := (i, ⟨j, hj⟩)
    let v : Fin g × Fin g := (i, ⟨j', hj'⟩)
    have hadj : (SimpleGraph.pathGraph g □ SimpleGraph.pathGraph g).Adj u v := by
      rw [SimpleGraph.boxProd_adj]
      exact Or.inr ⟨SimpleGraph.pathGraph_adj.2 (by simpa using hd), rfl⟩
    have he : s(u, v) ∈ E(GM01.gridGraph g) := hadj
    have hrow₂ : s(u, v) ∈ (GM10.gridRowPath g i).edgeSet := by
      refine ⟨he, ?_⟩
      rintro w ⟨z, hz, -⟩
      rcases Sym2.eq_iff.1 hz with ⟨h, -⟩ | ⟨-, h⟩
      · rw [← h]
      · rw [← h]
    have hfA : ηe s(u, v) ∈ A.edgeSet := hrow (mem_image_of_mem _ hrow₂)
    obtain ⟨u', v', x, y, heq, -, hx, hy, h⟩ := hηe _ he
    have hmem : ∀ {t}, G.Inc (ηe s(u, v)) t → t ∈ A.vertexSet := fun {t} ht =>
      A.vertex_mem_of_inc ((inc_iff_of_le hs.left_le hfA).2 ht)
    rcases Sym2.eq_iff.1 heq with ⟨h₁, -⟩ | ⟨h₁, -⟩
    · subst h₁
      exact ⟨x, hx, hmem h.inc_left⟩
    · subst h₁
      exact ⟨y, hy, hmem h.inc_right⟩
  have hcol : ∀ j < g, ∀ r, r < g → Conn (Hypergraph.ofGraph G hV hE) {v | ∃ a ≤ r, v ∈ W a j}
    := fun j hj r => by
    induction r with
    | zero =>
      intro _
      have : {v | ∃ a ≤ 0, v ∈ W a j} = W 0 j := by
        ext v
        constructor
        · rintro ⟨a, ha, hv⟩
          obtain rfl : a = 0 := by omega
          exact hv
        · exact fun h => ⟨0, le_rfl, h⟩
      rw [this]
      exact hW.conn 0 (by omega) j hj
    | succ r ih =>
      intro hr
      obtain ⟨x, hx, y, hy, hxy⟩ := hW.col r hr j hj
      have h₁ := (ih (by omega)).union_adj (hW.conn (r + 1) hr j hj) ⟨r, le_rfl, hx⟩ hy hxy
      have : {v | ∃ a ≤ r + 1, v ∈ W a j} = {v | ∃ a ≤ r, v ∈ W a j} ∪ W (r + 1) j := by
        ext v
        constructor
        · rintro ⟨a, ha, hv⟩
          rcases Nat.lt_or_ge r a with h | h
          · obtain rfl : a = r + 1 := by omega
            exact Or.inr hv
          · exact Or.inl ⟨a, h, hv⟩
        · rintro (⟨a, ha, hv⟩ | h)
          · exact ⟨a, by omega, hv⟩
          · exact ⟨r + 1, le_rfl, h⟩
      rw [this]
      exact h₁
  let C : ℕ → Set α := fun j => {v | ∃ a < g, v ∈ W a j}
  have hCc : ∀ j < g, Conn (Hypergraph.ofGraph G hV hE) (C j) := fun j hj => by
    have h₁ := hcol j hj (g - 1) (by omega)
    have : {v | ∃ a ≤ g - 1, v ∈ W a j} = C j := by
      ext v
      constructor
      · rintro ⟨a, ha, hv⟩
        exact ⟨a, by omega, hv⟩
      · rintro ⟨a, ha, hv⟩
        exact ⟨a, by omega, hv⟩
    rw [this] at h₁
    exact h₁
  have hCd : ∀ j ∈ Finset.range g, ∀ j' ∈ Finset.range g, j ≠ j' → Disjoint (C j) (C j')
    := fun j hj j' hj' hne => disjoint_left.2 fun v hv hv' => by
    obtain ⟨a, ha, h₁⟩ := hv
    obtain ⟨a', ha', h₂⟩ := hv'
    exact disjoint_left.1 (hW.disj a ha j (Finset.mem_range.1 hj) a' ha' j'
      (Finset.mem_range.1 hj') fun e => hne (Prod.ext_iff.1 e).2) h₁ h₂
  obtain ⟨j, hj, hd⟩ :=
    exists_avoid (Finset.range g) C hCd (A ∩ B).vertexSet_finite (by rwa [Finset.card_range])
  have hj' := Finset.mem_range.1 hj
  obtain ⟨x, hx, hxA⟩ := hmeet j hj'
  have hCA : C j ⊆ A.vertexSet := fun b hb => by
    by_contra hbA
    obtain ⟨a, ha, hba⟩ := hb
    have hbB : b ∈ B.vertexSet := (mem_V_or hs (hW.sub a ha j hj' hba)).resolve_left hbA
    obtain ⟨v, hv, hvS⟩ := (hCc j hj').meets_sep hs ⟨i, i.2, hx⟩ ⟨a, ha, hba⟩ hxA hbB
    exact disjoint_left.1 hd hv hvS
  have h₁ := hW.rank j hj'
  have heq : (⋃ a ∈ {a | a < g}, W a j) = C j := by
    ext v
    simp [C]
  rw [heq] at h₁
  have h₂ := tangleRank_le_separationOrder (θ := θ) hAB hCA
  omega

/-- (2.3) of Robertson, Seymour and Thomas, *Quickly excluding a planar graph* (page 327), in the
form XVI cites. -/
theorem rst94_theorem_2_3 : GM16.RST94Theorem23Statement := by
  intro θ _
  refine ⟨20 ^ ((2 * θ + 1) ^ 4 * (2 * (2 * θ + 1) - 1)), Nat.pos_of_ne_zero (by positivity),
    fun {α β} G θ_G T hT hle => ?_⟩
  obtain ⟨W, hW⟩ := theorem_5_7 (GM16.isGraph_ofGraph G hT.finite_V hT.finite_E) hT.isTangle (g
    := 2 * θ + 1) (by omega) hle
  obtain ⟨ηe, hm, hp⟩ := grid_model hW (by omega)
  exact ⟨_, ηe, hm, fun A B hAB hord i hrow => no_row hT.isTangle hW (by omega) hp hAB
    (by omega) i hrow⟩

end GraphMinor.RST94
