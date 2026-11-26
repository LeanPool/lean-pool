/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.RST94.Section5a
import Mathlib.Tactic.Positivity

/-!
# Section 5 of "Quickly excluding a planar graph": grids

A family of sets as in the hypothesis of (5.1) (page 339) is what we use for "a grid minor dominated
by the tangle": (5.1) turns the family into a grid minor, and in the proofs of (5.2) to (5.6) the
hypothesis that `𝒯` dominates no grid minor is used only through (5.1). So here `HasGrid G T θ g`
says that such a family exists, (5.2) becomes `HasGrid.of_conformal`, and the grid minor itself is
made in the last file.

The proof of (5.3) picks `g` values of `r` at the end, once all `2g - 1` steps are known. We do the
same count by carrying the columns found so far (`Cols`) for each of the two directions.
-/

@[expose] public section

namespace GraphMinor.RST94

open Hypergraph GM10 Set

variable {α β ι : Type*} {G : Hypergraph α β}

/-- The sets `W i j` of (5.1) (page 339), with indices from `0`. -/
structure IsGrid (G : Hypergraph α β) (T : Set (Hypergraph α β × Hypergraph α β)) (θ g : ℕ) (W : ℕ
  → ℕ → Set α) : Prop where
  sub : ∀ i < g, ∀ j < g, W i j ⊆ G.vertexSet
  conn : ∀ i < g, ∀ j < g, Conn G (W i j)
  disj : ∀ i < g, ∀ j < g, ∀ i' < g, ∀ j' < g, (i, j) ≠ (i', j') → Disjoint (W i j) (W i' j')
  row : ∀ i < g, ∀ j, j + 1 < g → ∃ x ∈ W i j, ∃ y ∈ W i (j + 1), G.skeleton.Adj x y
  col : ∀ i, i + 1 < g → ∀ j < g, ∃ x ∈ W i j, ∃ y ∈ W (i + 1) j, G.skeleton.Adj x y
  rank : ∀ j < g, g ≤ tangleRank T θ (⋃ i ∈ {i | i < g}, W i j)

/-- `𝒯` has a family of sets as in (5.1). -/
def HasGrid (G : Hypergraph α β) (T : Set (Hypergraph α β × Hypergraph α β)) (θ g : ℕ) : Prop :=
  ∃ W, IsGrid G T θ g W

/-- **(5.2)** (page 339), in the form we use: a family for a conformal tangle of a subgraph is a
family for `𝒯`. The rank goes up by (2.7). -/
theorem HasGrid.of_conformal {H : Hypergraph α β} {T' : Set (Hypergraph α β × Hypergraph α β)} {θ
  θ' g : ℕ} {T : Set (Hypergraph α β × Hypergraph α β)} (hH : H ≤ G) (hT : IsTangle G θ T)
    (hT' : IsTangle H θ' T') (hc : Conformal G H T T' θ θ') (h : HasGrid H T' θ' g) : HasGrid G T θ
      g := by
  obtain ⟨W, hW⟩ := h
  have hadj : ∀ {x y}, H.skeleton.Adj x y → G.skeleton.Adj x y := fun h => skeleton_mono hH h
  refine ⟨W, ⟨fun i hi j hj => (hW.sub i hi j hj).trans hH.vertexSet_subset, fun i hi j hj =>
    (hW.conn i hi j hj).mono hH, hW.disj, fun i hi j hj => ?_, fun i hi j hj => ?_, fun j hj => ?_⟩⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := hW.row i hi j hj
    exact ⟨x, hx, y, hy, hadj hxy⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := hW.col i hi j hj
    exact ⟨x, hx, y, hy, hadj hxy⟩
  · exact (hW.rank j hj).trans (rank_le_of_conformal hH hT hT' hc (iUnion₂_subset fun i hi
    => hW.sub i hi j hj))

/-- A path without its last vertex. -/
theorem exists_butlast {K : SimpleGraph α} {a b : α} (p : K.Walk a b) (hp : p.IsPath)
  (hab : a ≠ b) :
    ∃ (c : α) (q : K.Walk a c), K.Adj c b ∧ ∀ x, x ∈ q.support ↔ x ∈ p.support ∧ x ≠ b := by
  induction p with
  | nil => exact absurd rfl hab
  | @cons u v w h p ih =>
    have hp₂ := hp.of_cons
    by_cases hvw : v = w
    · subst hvw
      have hnil : p = SimpleGraph.Walk.nil := (SimpleGraph.Walk.isPath_iff_nil.1 hp₂).eq_nil
      subst hnil
      refine ⟨u, SimpleGraph.Walk.nil, h, fun x => ?_⟩
      simp only [SimpleGraph.Walk.support_nil, SimpleGraph.Walk.support_cons, List.mem_cons,
        List.not_mem_nil, or_false]
      exact ⟨fun e => ⟨Or.inl e, e ▸ hab⟩, fun ⟨h₁, h₂⟩ => h₁.resolve_right h₂⟩
    · obtain ⟨c, q, hq, hx⟩ := ih hp₂ hvw
      refine ⟨c, SimpleGraph.Walk.cons h q, hq, fun x => ?_⟩
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons, hx]
      constructor
      · rintro (rfl | ⟨h₁, h₂⟩)
        · exact ⟨Or.inl rfl, hab⟩
        · exact ⟨Or.inr h₁, h₂⟩
      · rintro ⟨h₁ | h₁, h₂⟩
        · exact Or.inl h₁
        · exact Or.inr ⟨h₁, h₂⟩

/-- The columns built so far in the proof of (5.3), and the heads `H i` of the next column. The
vertex `w i` is the current end of the `i`th path. -/
structure Cols (G : Hypergraph α β) (T : Set (Hypergraph α β × Hypergraph α β)) (θ g a : ℕ)
  (G' : Hypergraph α β) (w : ℕ → α) (W : ℕ → ℕ → Set α) (H : ℕ → Set α) : Prop where
  sub : ∀ i < g, ∀ j < a, W i j ⊆ G.vertexSet
  conn : ∀ i < g, ∀ j < a, Conn G (W i j)
  disj : ∀ i < g, ∀ j < a, ∀ i' < g, ∀ j' < a, (i, j) ≠ (i', j') → Disjoint (W i j) (W i' j')
  off : ∀ i < g, ∀ j < a, ∀ x ∈ W i j, x ∉ G'.vertexSet
  row : ∀ i < g, ∀ j, j + 1 < a → ∃ x ∈ W i j, ∃ y ∈ W i (j + 1), G.skeleton.Adj x y
  col : ∀ i, i + 1 < g → ∀ j < a, ∃ x ∈ W i j, ∃ y ∈ W (i + 1) j, G.skeleton.Adj x y
  rank : ∀ j < a, g ≤ tangleRank T θ (⋃ i ∈ {i | i < g}, W i j)
  hsub : ∀ i < g, H i ⊆ G.vertexSet
  hconn : ∀ i < g, Conn G (H i)
  hdisj : ∀ i < g, ∀ i' < g, i ≠ i' → Disjoint (H i) (H i')
  hW : ∀ i < g, ∀ i' < g, ∀ j < a, Disjoint (H i) (W i' j)
  hmem : ∀ i < g, w i ∈ H i
  hoff : ∀ i < g, ∀ x ∈ H i, x ∈ G'.vertexSet → x = w i
  hrank : g ≤ tangleRank T θ (⋃ i ∈ {i | i < g}, H i)
  hadj : ∀ i < g, ∀ j, j + 1 = a → ∃ x ∈ W i j, ∃ y ∈ H i, G.skeleton.Adj x y

/-- `g` columns make a grid. -/
theorem Cols.hasGrid {T : Set (Hypergraph α β × Hypergraph α β)} {θ g a : ℕ} {G' : Hypergraph α β}
  {w : ℕ → α} {W : ℕ → ℕ → Set α} {H : ℕ → Set α}
    (h : Cols G T θ g a G' w W H) (ha : g ≤ a) : HasGrid G T θ g :=
  ⟨W, ⟨fun i hi j hj => h.sub i hi j (by omega), fun i hi j hj => h.conn i hi j
    (by omega), fun i hi j hj i' hi' j' hj' => h.disj i hi j (by omega) i' hi' j' (by omega),
    fun i hi j hj => h.row i hi j (by omega), fun i hi j hj => h.col i hi j (by omega), fun j hj
      => h.rank j (by omega)⟩⟩

/-- A step that does not make a new column: the paths grow, and the heads with them. -/
theorem Cols.extend {T : Set (Hypergraph α β × Hypergraph α β)} {θ g a : ℕ}
  (hT : IsTangle G θ T) {G' G₂ : Hypergraph α β} {y y₂ : ι → α} {f : ℕ → ι} {W : ℕ → ℕ
    → Set α} {H : ℕ → Set α}
    (h : Cols G T θ g a G' (fun i => y (f i)) W H) (hle : G' ≤ G) (hle₂ : G₂ ≤ G')
      (hy : range y ⊆ G'.vertexSet) (hf : ∀ i < g, ∀ i' < g, i ≠ i' → f i ≠ f i') {p : ∀ c,
        G'.skeleton.Walk (y c) (y₂ c)} (hp : IsLinkage G' G₂ y y₂ p)
    (hav : ∀ c, y c ∉ G₂.vertexSet) :
    Cols G T θ g a G₂ (fun i => y₂ (f i)) W (fun i => H i ∪ {x | x ∈ (p (f i)).support}) := by
  obtain ⟨hp₁, hp₂, hp₃⟩ := hp
  have hG₂ : ∀ {x}, x ∈ G₂.vertexSet → x ∈ G'.vertexSet := fun hx => hle₂.vertexSet_subset hx
  have hpG : ∀ c t, t ∈ (p c).support → t ∈ G'.vertexSet := fun c t ht => support_mem (p c) (hy
    (mem_range_self c)) ht
  refine ⟨h.sub, h.conn, h.disj, fun i hi j hj x hx hxG => h.off i hi j hj x hx
    (hG₂ hxG), h.row, h.col, h.rank, fun i hi => ?_, fun i hi => ?_, fun i hi i' hi' hne
      => ?_, fun i hi i' hi' j hj => ?_,
    fun i hi => Or.inr (p (f i)).end_mem_support, fun i hi x hx hxG => ?_, ?_, fun i hi j hj => ?_⟩
  · exact union_subset (h.hsub i hi) fun t ht => hle.vertexSet_subset (hpG _ t ht)
  · exact (h.hconn i hi).union ((conn_support (p (f i))).mono hle) ⟨y (f i), h.hmem i hi, (p
    (f i)).start_mem_support⟩
  · have hc : ∀ i i', i < g → i' < g → i ≠ i' → Disjoint (H i) {x | x ∈ (p (f i')).support}
    := fun i i' hi hi' hne => disjoint_left.2 fun x hx hx' => by
      have := h.hoff i hi x hx (hpG _ x hx')
      subst this
      exact disjoint_left.1 (hp₃ (hf i hi i' hi' hne)) (p (f i)).start_mem_support hx'
    refine disjoint_union_left.2 ⟨disjoint_union_right.2 ⟨h.hdisj i hi i' hi' hne, hc i i' hi hi'
      hne⟩, disjoint_union_right.2 ⟨(hc i' i hi' hi hne.symm).symm, hp₃ (hf i hi i' hi' hne)⟩⟩
  · exact disjoint_union_left.2 ⟨h.hW i hi i' hi' j hj, disjoint_left.2 fun x hx hx'
    => h.off i' hi' j hj x hx' (hpG _ x hx)⟩
  · rcases hx with hx | hx
    · exact absurd ((h.hoff i hi x hx (hG₂ hxG)) ▸ hxG) (hav _)
    · exact hp₂ _ x hx hxG
  · exact h.hrank.trans (tangleRank_mono hT (iUnion₂_mono fun i _ => subset_union_left))
  · obtain ⟨x, hx, t, ht, hxt⟩ := h.hadj i hi j hj
    exact ⟨x, hx, t, Or.inl ht, hxt⟩

/-- A step that makes a new column, from the sets `T' i` of `Segs`. -/
theorem Cols.column {T : Set (Hypergraph α β × Hypergraph α β)} {θ g a : ℕ}
  (hT : IsTangle G θ T) {G' G₂ : Hypergraph α β} {y y₂ : ι → α} {f : ℕ → ι} {W : ℕ → ℕ
    → Set α} {H : ℕ → Set α}
    (h : Cols G T θ g a G' (fun i => y (f i)) W H) (hle : G' ≤ G) (hle₂ : G₂ ≤ G')
      (hy : range y ⊆ G'.vertexSet) (hy₂ : range y₂ ⊆ G₂.vertexSet) (hf : ∀ i < g, ∀ i' < g, i ≠ i'
        → f i ≠ f i') {p : ∀ c, G'.skeleton.Walk (y c) (y₂ c)} (hp : IsLinkage G' G₂ y y₂ p)
    (hav : ∀ c, y c ∉ G₂.vertexSet) {Y : Set α} {T' : ℕ → Set α} {x' y' : ℕ → α} (hS : Segs G'
      (fun c => {t | t ∈ (p c).support}) f g 0 Y T' x' y') (hYG : Y ⊆ G'.vertexSet)
        (hY : ∀ t ∈ Y, t ∉ G₂.vertexSet)
    (hrank : g ≤ tangleRank T θ (⋃ i ∈ {i | i < g}, {y₂ (f i)})) :
    ∃ W₂ H₂, Cols G T θ g (a + 1) G₂ (fun i => y₂ (f i)) W₂ H₂ := by
  classical
  obtain ⟨hp₁, hp₂, hp₃⟩ := hp
  have hG₂ : ∀ {x}, x ∈ G₂.vertexSet → x ∈ G'.vertexSet := fun hx => hle₂.vertexSet_subset hx
  have hpG : ∀ c t, t ∈ (p c).support → t ∈ G'.vertexSet := fun c t ht => support_mem (p c) (hy
    (mem_range_self c)) ht
  have hne : ∀ c, y c ≠ y₂ c := fun c e => hav c (e ▸ hy₂ (mem_range_self c))
  have hlast : ∀ c, ∃ (d : α) (q : G'.skeleton.Walk (y c) d), G'.skeleton.Adj d (y₂ c)
    ∧ ∀ x, x ∈ q.support ↔ x ∈ (p c).support ∧ x ≠ y₂ c := fun c =>
    exists_butlast (p c) (hp₁ c) (hne c)
  choose d q hd hq using hlast
  let B : ℕ → Set α := fun i => {x | x ∈ (q (f i)).support}
  let N : ℕ → Set α := fun i => H i ∪ B i ∪ {t | i + 1 < g ∧ t ∈ T' i}
  have hBoff : ∀ i, ∀ x ∈ B i, x ∉ G₂.vertexSet := fun i x hx hxG => ((hq _ x).1 hx).2 (hp₂ _ x
    ((hq _ x).1 hx).1 hxG)
  have hNoff : ∀ i < g, ∀ x ∈ N i, x ∉ G₂.vertexSet := by
    rintro i hi x ((hx | hx) | ⟨h₁, hx⟩) hxG
    · exact hav _ ((h.hoff i hi x hx (hG₂ hxG)) ▸ hxG)
    · exact hBoff i x hx hxG
    · exact hY x (hS.sub i (Nat.zero_le _) h₁ hx) hxG
  have hNconn : ∀ i < g, Conn G (N i) := fun i hi => by
    have h₁ : Conn G (H i ∪ B i) := (h.hconn i hi).union ((conn_support (q (f i))).mono hle) ⟨y
      (f i), h.hmem i hi, (q (f i)).start_mem_support⟩
    by_cases hi' : i + 1 < g
    · have heq : N i = H i ∪ B i ∪ T' i := by
        ext t
        simp [N, hi']
      rw [heq]
      refine h₁.union ((hS.conn i (Nat.zero_le _) hi').mono hle) ⟨x' i, Or.inr
        ((hq _ _).2 ⟨hS.x_V i (Nat.zero_le _) hi', fun e => ?_⟩), hS.x_T i (Nat.zero_le _) hi'⟩
      exact hY _ (hS.sub i (Nat.zero_le _) hi' (hS.x_T i (Nat.zero_le _) hi')) (e ▸ hy₂
        (mem_range_self _))
    · have heq : N i = H i ∪ B i := by
        ext t
        simp [N, hi']
      rw [heq]
      exact h₁
  -- A vertex of `N i` in `G'` is on the `i`th path, or it is on no path.
  have hlab : ∀ i < g, ∀ x ∈ N i, x ∈ G'.vertexSet → x ∈ (p (f i)).support ∨ (x ∈ T' i ∧ i + 1 < g
    ∧ ∀ l, x ∉ (p l).support) := by
    rintro i hi x ((hx | hx) | ⟨h₁, hx⟩) hxG
    · exact Or.inl (h.hoff i hi x hx hxG ▸ (p (f i)).start_mem_support)
    · exact Or.inl ((hq _ x).1 hx).1
    · by_cases he : x = x' i
      · exact Or.inl (he ▸ hS.x_V i (Nat.zero_le _) h₁)
      · exact Or.inr ⟨hx, h₁, hS.label i (Nat.zero_le _) h₁ x hx he⟩
  have hNH : ∀ i < g, ∀ x ∈ N i, x ∉ G'.vertexSet → x ∈ H i := by
    rintro i hi x ((hx | hx) | ⟨h₁, hx⟩) hxG
    · exact hx
    · exact absurd (hpG _ x ((hq _ x).1 hx).1) hxG
    · exact absurd (hYG (hS.sub i (Nat.zero_le _) h₁ hx)) hxG
  have hNN : ∀ i < g, ∀ i' < g, i ≠ i' → Disjoint (N i) (N i') := fun i hi i' hi' hii
    => disjoint_left.2 fun x hx hx' => by
    by_cases hxG : x ∈ G'.vertexSet
    · rcases hlab i hi x hx hxG with h₁ | ⟨h₁, h₂, h₃⟩ <;> rcases hlab i' hi' x hx' hxG with h₄ |
      ⟨h₄, h₅, h₆⟩
      · exact disjoint_left.1 (hp₃ (hf i hi i' hi' hii)) h₁ h₄
      · exact h₆ _ h₁
      · exact h₃ _ h₄
      · exact disjoint_left.1 (hS.disj i i' (Nat.zero_le _) h₂ (Nat.zero_le _) h₅ hii) h₁ h₄
    · exact disjoint_left.1 (h.hdisj i hi i' hi' hii) (hNH i hi x hx hxG) (hNH i' hi' x hx' hxG)
  have hNW : ∀ i < g, ∀ i' < g, ∀ j < a, Disjoint (N i) (W i' j) := fun i hi i' hi' j hj
    => disjoint_left.2 fun x hx hx' => by
    by_cases hxG : x ∈ G'.vertexSet
    · exact h.off i' hi' j hj x hx' hxG
    · exact disjoint_left.1 (h.hW i hi i' hi' j hj) (hNH i hi x hx hxG) hx'
  have hNsub : ∀ i < g, N i ⊆ G.vertexSet := fun i hi x hx => by
    by_cases hxG : x ∈ G'.vertexSet
    · exact hle.vertexSet_subset hxG
    · exact h.hsub i hi (hNH i hi x hx hxG)
  let W₂ : ℕ → ℕ → Set α := fun i j => if j = a then N i else W i j
  have hW₂a : ∀ i, W₂ i a = N i := fun i => by simp [W₂]
  have hW₂o : ∀ i j, j < a → W₂ i j = W i j := fun i j hj => by simp [W₂, hj.ne]
  have hcases : ∀ j, j < a + 1 → j < a ∨ j = a := fun j hj => by omega
  have hoff₂ : ∀ i < g, ∀ j < a + 1, ∀ x ∈ W₂ i j, x ∉ G₂.vertexSet := fun i hi j hj x hx hxG => by
    rcases hcases j hj with h₁ | rfl
    · rw [hW₂o _ _ h₁] at hx
      exact h.off i hi j h₁ x hx (hG₂ hxG)
    · rw [hW₂a] at hx
      exact hNoff i hi x hx hxG
  refine ⟨W₂, fun i => {y₂ (f i)}, ⟨fun i hi j hj => ?_, fun i hi j hj
    => ?_, fun i hi j hj i' hi' j' hj' hij => ?_, fun i hi j hj x hx hxG => ?_, fun i hi j hj
      => ?_, fun i hi j hj => ?_, fun j hj => ?_,
    fun i hi => ?_, fun i hi => conn_singleton, fun i hi i' hi' hii => ?_, fun i hi i' hi' j hj
      => ?_, fun i hi => rfl, fun i hi x hx _ => hx, hrank, fun i hi j hj => ?_⟩⟩
  · rcases hcases j hj with h₁ | rfl
    · rw [hW₂o _ _ h₁]
      exact h.sub i hi j h₁
    · rw [hW₂a]
      exact hNsub i hi
  · rcases hcases j hj with h₁ | rfl
    · rw [hW₂o _ _ h₁]
      exact h.conn i hi j h₁
    · rw [hW₂a]
      exact hNconn i hi
  · rcases hcases j hj with h₁ | rfl <;> rcases hcases j' hj' with h₂ | rfl
    · rw [hW₂o _ _ h₁, hW₂o _ _ h₂]
      exact h.disj i hi j h₁ i' hi' j' h₂ hij
    · rw [hW₂o _ _ h₁, hW₂a]
      exact (hNW i' hi' i hi j h₁).symm
    · rw [hW₂a, hW₂o _ _ h₂]
      exact hNW i hi i' hi' j' h₂
    · rw [hW₂a, hW₂a]
      exact hNN i hi i' hi' fun e => hij (by rw [e])
  · exact hoff₂ i hi j hj x hx hxG
  · rcases hcases (j + 1) hj with h₁ | h₁
    · rw [hW₂o _ _ h₁, hW₂o _ _ (by omega)]
      exact h.row i hi j h₁
    · obtain ⟨x, hx, t, ht, hxt⟩ := h.hadj i hi j h₁
      subst h₁
      rw [hW₂a, hW₂o _ _ (by omega)]
      exact ⟨x, hx, t, Or.inl (Or.inl ht), hxt⟩
  · rcases hcases j hj with h₁ | rfl
    · rw [hW₂o _ _ h₁, hW₂o _ _ h₁]
      exact h.col i hi j h₁
    · rw [hW₂a, hW₂a]
      obtain ⟨t, ht, hadj⟩ := hS.touch i (Nat.zero_le _) hi
      refine ⟨t, Or.inr ⟨hi, ht⟩, y' i, Or.inl (Or.inr ?_), skeleton_mono hle hadj⟩
      refine (hq _ _).2 ⟨hS.y_V i (Nat.zero_le _) hi, fun e => ?_⟩
      exact hY _ (hS.y_Y i (Nat.zero_le _) hi) (e ▸ hy₂ (mem_range_self _))
  · rcases hcases j hj with h₁ | rfl
    · simp only [hW₂o _ _ h₁]
      exact h.rank j h₁
    · simp only [hW₂a]
      exact h.hrank.trans (tangleRank_mono hT (iUnion₂_mono fun i _ x hx => Or.inl (Or.inl hx)))
  · rintro x rfl
    exact hle.vertexSet_subset (hle₂.vertexSet_subset (hy₂ (mem_range_self _)))
  · rw [disjoint_singleton_left, mem_singleton_iff]
    intro e
    have hmem : y₂ (f i) ∈ (p (f i')).support := by
      rw [e]
      exact (p (f i')).end_mem_support
    exact disjoint_left.1 (hp₃ (hf i hi i' hi' hii)) (p (f i)).end_mem_support hmem
  · rw [disjoint_singleton_left]
    exact fun hx => hoff₂ i' hi' j hj _ hx (hy₂ (mem_range_self _))
  · obtain rfl : j = a := by omega
    rw [hW₂a]
    exact ⟨d (f i), Or.inl (Or.inr (q (f i)).end_mem_support), _, rfl, skeleton_mono hle (hd (f i))⟩

/-- The state after `r` steps of the proof of (5.3): `z'` is `z^r`, and `P` is the union of `P^1, …,
P^r`. -/
structure Stage (G : Hypergraph α β) (T : Set (Hypergraph α β × Hypergraph α β)) (θ : ℕ) (z : ι
  → α) (r : ℕ) (G' : Hypergraph α β)
    (T' : Set (Hypergraph α β × Hypergraph α β)) (θ' : ℕ) (z' : ι → α) (P : ∀ c, G.skeleton.Walk
      (z c) (z' c)) : Prop where
  nodule : Nodule G' T' θ' z'
  le : G' ≤ G
  conformal : Conformal G G' T T' θ θ'
  link : IsLinkage G G' z z' P
  avoid : r ≠ 0 → ∀ c, z c ∉ G'.vertexSet
  fix : r = 0 → ∀ c, z' c = z c

/-- The start: `G` itself, with one-vertex paths. -/
theorem stage_zero {T : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ} {z : ι → α}
  (hN : Nodule G T θ z) :
    Stage G T θ z 0 G T θ z (fun _ => SimpleGraph.Walk.nil) :=
  ⟨hN, le_rfl, conformal_of_subset hN.tangle le_rfl subset_rfl, ⟨fun _
    => SimpleGraph.Walk.IsPath.nil, fun c t ht _ => by simpa using ht,
    fun i j hij => by simpa using fun e => hij (hN.inj e)⟩, fun h => absurd rfl h, fun _ _ => rfl⟩

/-- Adding one residual nodule to a stage. -/
theorem Stage.step {T T' T₂ : Set (Hypergraph α β × Hypergraph α β)} {θ θ' θ₂ r : ℕ}
  (hT : IsTangle G θ T) {z z' z₂ : ι → α} {G' G₂ : Hypergraph α β} {P : ∀ c, G.skeleton.Walk (z c)
    (z' c)}
    {p : ∀ c, G'.skeleton.Walk (z' c) (z₂ c)} (hc : Stage G T θ z r G' T' θ' z' P)
      (hR : Residual G' T' θ' z' G₂ T₂ θ₂ z₂) (hl : IsLinkage G' G₂ z' z₂ p) :
    Stage G T θ z (r + 1) G₂ T₂ θ₂ z₂ (fun c => (P c).append ((p c).mapLe (skeleton_mono hc.le)))
      := by
  obtain ⟨hp₁, hp₂, hp₃⟩ := hl
  obtain ⟨hP₁, hP₂, hP₃⟩ := hc.link
  have hmem : ∀ c t, t ∈ ((P c).append ((p c).mapLe (skeleton_mono hc.le))).support ↔ t ∈
    (P c).support ∨ t ∈ (p c).support := fun c t => by
    simp [SimpleGraph.Walk.mem_support_append_iff]
  have hpG : ∀ c t, t ∈ (p c).support → t ∈ G'.vertexSet := fun c t ht =>
    support_mem (p c) (hc.nodule.free.1 (mem_range_self c)) ht
  have hG₂ : ∀ {x}, x ∈ G₂.vertexSet → x ∈ G'.vertexSet := fun hx => hR.le.vertexSet_subset hx
  refine ⟨hR.nodule, hR.le.trans hc.le, Conformal.trans hc.le hR.le hT hc.nodule.tangle
    hR.nodule.tangle hc.conformal hR.conformal, ⟨fun c => ?_, fun c t ht htG => ?_,
    fun i j hij => disjoint_left.2 fun t ht ht' => ?_⟩, fun _ c hcG => ?_, fun h => absurd h
      (Nat.succ_ne_zero r)⟩
  · exact isPath_append (hP₁ c) ((hp₁ c).mapLe _) fun x hx hx' => hP₂ c x hx (hpG c x
    (by simpa using hx'))
  · rcases (hmem c t).1 ht with h | h
    · have := hP₂ c t h (hG₂ htG)
      exact absurd (this ▸ htG) (hR.avoid c)
    · exact hp₂ c t h htG
  · have hx : ∀ i j, i ≠ j → t ∈ (P i).support → t ∉ (p j).support := fun i j hij hi hj => by
      have := hP₂ i t hi (hpG j t hj)
      subst this
      exact disjoint_left.1 (hp₃ hij) (p i).start_mem_support hj
    rcases (hmem i t).1 ht with h₁ | h₁ <;> rcases (hmem j t).1 ht' with h₂ | h₂
    · exact disjoint_left.1 (hP₃ hij) h₁ h₂
    · exact hx i j hij h₁ h₂
    · exact hx j i hij.symm h₂ h₁
    · exact disjoint_left.1 (hp₃ hij) h₁ h₂
  · by_cases hr : r = 0
    · subst hr
      exact hR.avoid c (hc.fix rfl c ▸ hcG)
    · exact hc.avoid hr c (hG₂ hcG)

/-- A stage after at least one step is a residual nodule. -/
theorem Stage.residual {T T' : Set (Hypergraph α β × Hypergraph α β)} {θ θ' r : ℕ} {z z' : ι
  → α} {G' : Hypergraph α β} {P : ∀ c, G.skeleton.Walk (z c) (z' c)}
    (hc : Stage G T θ z r G' T' θ' z' P) (hr : r ≠ 0) : Residual G T θ z G' T' θ' z' :=
  ⟨hc.nodule, hc.le, hc.avoid hr, hc.conformal, P, hc.link⟩

/-- `g` vertices of a nodule keep rank `g` in `𝒯`, by (2.7). This is the display on page 340. -/
theorem nodule_rank {T T' : Set (Hypergraph α β × Hypergraph α β)} {θ θ' g : ℕ}
  (hT : IsTangle G θ T) {z' : ι → α} {G' : Hypergraph α β} {f : ℕ → ι} (hN : Nodule G' T' θ' z')
    (hle : G' ≤ G)
    (hc : Conformal G G' T T' θ θ') (hf : ∀ i < g, ∀ i' < g, i ≠ i' → f i ≠ f i') : g
      ≤ tangleRank T θ (⋃ i ∈ {i | i < g}, {z' (f i)}) := by
  have heq : (⋃ i ∈ {i | i < g}, ({z' (f i)} : Set α)) = (fun i => z' (f i)) '' {i | i < g} := by
    ext x
    simp [eq_comm]
  have hsub : (⋃ i ∈ {i | i < g}, ({z' (f i)} : Set α)) ⊆ range z' := by
    rw [heq]
    rintro _ ⟨i, -, rfl⟩
    exact mem_range_self _
  have hfree := hN.free.subset hN.tangle hsub
  have hcard : (⋃ i ∈ {i | i < g}, ({z' (f i)} : Set α)).ncard = g := by
    rw [heq, InjOn.ncard_image]
    · have : {i | i < g} = ((Finset.range g : Finset ℕ) : Set ℕ) := by
        ext i
        simp
      rw [this, ncard_coe_finset, Finset.card_range]
    · intro i hi i' hi' he
      by_contra hne
      exact hf i hi i' hi' hne (hN.inj he)
  have h₂ := ((isFreeSet_iff_tangleRank_eq hN.tangle).1 hfree).2
  rw [hcard] at h₂
  exact h₂.symm.le.trans (rank_le_of_conformal hle hT hN.tangle hc hfree.1)

/-- The columns at the start. -/
theorem cols_zero {T : Set (Hypergraph α β × Hypergraph α β)} {θ g : ℕ}
  (hT : IsTangle G θ T) {z : ι → α} {f : ℕ → ι} (hN : Nodule G T θ z)
    (hf : ∀ i < g, ∀ i' < g, i ≠ i' → f i ≠ f i') :
    ∃ W H, Cols G T θ g 0 G (fun i => z (f i)) W H := by
  refine ⟨fun _ _ => ∅, fun i => {z (f i)}, ⟨fun i _ j hj => absurd hj
    (Nat.not_lt_zero j), fun i _ j hj => absurd hj (Nat.not_lt_zero j), fun i _ j hj => absurd hj
      (Nat.not_lt_zero j),
    fun i _ j hj => absurd hj (Nat.not_lt_zero j), fun i _ j hj => absurd hj
      (Nat.not_lt_zero _), fun i _ j hj => absurd hj (Nat.not_lt_zero j), fun j hj => absurd hj
        (Nat.not_lt_zero j),
    fun i _ => ?_, fun i _ => conn_singleton, fun i hi i' hi' hne => ?_, fun i _ i' _ j hj
      => absurd hj (Nat.not_lt_zero j), fun _ _ => rfl, fun _ _ _ hx _ => hx, ?_, fun i _ j hj
        => absurd hj (Nat.succ_ne_zero j)⟩⟩
  · rintro x rfl
    exact hN.free.1 (mem_range_self _)
  · rw [disjoint_singleton]
    exact fun e => hf i hi i' hi' hne (hN.inj e)
  · exact nodule_rank hT hN le_rfl (conformal_of_subset hN.tangle le_rfl subset_rfl) hf

/-- The conclusion of (5.3): a residual nodule with a linkage, and a piece `q` of `Q` that joins
`P_{c p}` to `P_b`. -/
def JumpEnd (G : Hypergraph α β) (T : Set (Hypergraph α β × Hypergraph α β)) (θ : ℕ) (z : ι → α)
  (k g : ℕ) (c : ℕ → ι) : Prop :=
  ∃ (G' : Hypergraph α β) (T' : Set (Hypergraph α β × Hypergraph α β)) (θ' : ℕ) (z' : ι → α)
    (P : ∀ c, G.skeleton.Walk (z c) (z' c)) (p : ℕ) (b : ι) (Y : Set α),
    Residual G T θ z G' T' θ' z' ∧ k ≤ θ' ∧ IsLinkage G G' z z' P ∧ 1 ≤ p ∧ p + 2 ≤ 2 * g - 1
      ∧ b ≠ c (p - 1) ∧ b ≠ c p ∧ b ≠ c (p + 1) ∧
      JumpData G (fun l => {t | t ∈ (P l).support}) Y (c p) b ∧ ∀ t ∈ Y, t ∉ G'.vertexSet

/-- The induction in the proof of (5.3): after `r` steps we have stopped with a jump, or we have `a`
columns of the first kind and `b` of the second, with `a + b = r`. -/
theorem exists_stage [Fintype ι] (hG : G.IsGraph) {T : Set (Hypergraph α β × Hypergraph α β)} {θ :
  ℕ} {z : ι → α} (hN : Nodule G T θ z) {g k : ℕ} (hg : 2 ≤ g) {c : ℕ → ι}
    (hc : ∀ a b, a < 2 * g - 1 → b < 2 * g - 1 → c a = c b → a = b) (hn : Fintype.card ι ≤ 2 * k)
      (hθ : k * 20 ^ (2 * g) ≤ θ) (r : ℕ) (hr : r ≤ 2 * g - 1) :
    JumpEnd G T θ z k g c ∨ ∃ (G' : Hypergraph α β) (T' : Set (Hypergraph α β × Hypergraph α β))
      (θ' : ℕ) (z' : ι → α) (P : ∀ c, G.skeleton.Walk (z c) (z' c)) (W₁ W₂ : ℕ → ℕ → Set α)
        (H₁ H₂ : ℕ → Set α) (a b : ℕ),
      Stage G T θ z r G' T' θ' z' P ∧ k * 20 ^ (2 * g - r) ≤ θ' ∧ Cols G T θ g a G' (fun i => z' (c
        (g - 1 - i))) W₁ H₁ ∧ Cols G T θ g b G' (fun i => z' (c (g - 1 + i))) W₂ H₂ ∧ a + b = r
          := by
  have hf₁ : ∀ i < g, ∀ i' < g, i ≠ i' → c (g - 1 - i) ≠ c (g - 1 - i') := fun i hi i' hi' hne e
    => by
    have := hc _ _ (by omega) (by omega) e
    omega
  have hf₂ : ∀ i < g, ∀ i' < g, i ≠ i' → c (g - 1 + i) ≠ c (g - 1 + i') := fun i hi i' hi' hne e
    => by
    have := hc _ _ (by omega) (by omega) e
    omega
  have hT := hN.tangle
  induction r with
  | zero =>
    obtain ⟨W₁, H₁, h₁⟩ := cols_zero hT hN hf₁
    obtain ⟨W₂, H₂, h₂⟩ := cols_zero hT hN hf₂
    exact Or.inr ⟨G, T, θ, z, _, W₁, W₂, H₁, H₂, 0, 0, stage_zero hN, hθ, h₁, h₂, rfl⟩
  | succ r ih =>
    rcases ih (by omega) with hj | ⟨G', T', θ', z', P, W₁, W₂, H₁, H₂, a, b, hS, hb, hC₁, hC₂, hab⟩
    · exact Or.inl hj
    have hne : c (g - 1) ≠ c 0 := fun e => by
      have := hc _ _ (by omega) (by omega) e
      omega
    have h2n : 2 ≤ Fintype.card ι := by
      have : Nontrivial ι := ⟨_, _, hne⟩
      exact Fintype.one_lt_card
    obtain ⟨e, he⟩ : ∃ e, 2 * g - (r + 1) = e + 1 := ⟨2 * g - (r + 1) - 1, by omega⟩
    have hsplit : 2 * g - r = e + 1 + 1 := by omega
    set K := k * 20 ^ (2 * g - (r + 1)) with hK
    have hK₂ : 20 * k ≤ K := by
      rw [hK, he, pow_succ, Nat.mul_comm (20 ^ e), ← Nat.mul_assoc, Nat.mul_comm k]
      exact Nat.le_mul_of_pos_right _ (by positivity)
    have hK₃ : K * 20 ≤ θ' := by
      have : k * 20 ^ (2 * g - r) = K * 20 := by
        rw [hK, he, hsplit, pow_succ _ (e + 1), Nat.mul_assoc]
      rwa [this] at hb
    have hG' : G'.IsGraph := IsGraph.of_le hG hS.le
    obtain ⟨G₂, T₂, z₂, p, Q, hR, hl, hQp, hQo, hQn⟩ := theorem_4_2 hG' hS.nodule (k := K)
      (by omega) (by omega) hne
    have hS₂ := hS.step hT hR hl
    have hy : range z' ⊆ G'.vertexSet := hS.nodule.free.1
    have hy₂ : range z₂ ⊆ G₂.vertexSet := hR.nodule.free.1
    have hYG : {t | t ∈ Q.support} ⊆ G'.vertexSet := fun t ht => support_mem Q (hy
      (mem_range_self _)) ht
    have hr₁ : ∀ {f : ℕ → ι}, (∀ i < g, ∀ i' < g, i ≠ i' → f i ≠ f i') → g ≤ tangleRank T θ
      (⋃ i ∈ {i | i < g}, {z₂ (f i)}) := fun hf =>
      nodule_rank hT hR.nodule hS₂.le hS₂.conformal hf
    rcases walk_trichotomy (Gr := G') (V := fun l => {t | t ∈ (p l).support}) hl.2.2 hg hc Q hQp
      hQn (p _).start_mem_support (p _).start_mem_support with ⟨T₁, x₁, y₁, hs⟩ | ⟨T₁, x₁, y₁, hs⟩
        | ⟨q, b', h₁, h₂, h₃, h₄, h₅, h₆⟩
    · obtain ⟨W, H, hC⟩ := hC₁.column hT hS.le hR.le hy hy₂ hf₁ hl hR.avoid hs hYG hQo (hr₁ hf₁)
      exact Or.inr ⟨G₂, T₂, K, z₂, _, W, W₂, H, _, a + 1, b, hS₂, le_rfl, hC,
        hC₂.extend hT hS.le hR.le hy hf₂ hl hR.avoid, by omega⟩
    · obtain ⟨W, H, hC⟩ := hC₂.column hT hS.le hR.le hy hy₂ hf₂ hl hR.avoid hs hYG hQo (hr₁ hf₂)
      exact Or.inr ⟨G₂, T₂, K, z₂, _, W₁, W, _, H, a, b + 1, hS₂, le_rfl,
        hC₁.extend hT hS.le hR.le hy hf₁ hl hR.avoid, hC, by omega⟩
    · refine Or.inl ⟨G₂, T₂, K, z₂, _, q, b', {t | t ∈ Q.support}, hS₂.residual
      (Nat.succ_ne_zero r), by omega,
        hS₂.link, h₁, h₂, h₃, h₄, h₅, ?_, hQo⟩
      obtain ⟨x, t, y, q', h₁', h₂', h₃', h₄', h₅', h₆'⟩ := h₆
      refine ⟨x, t, y, q'.mapLe (skeleton_mono hS.le), skeleton_mono hS.le h₁', ?_, ?_,
        fun v hv hvx l hl' => ?_, fun v hv => h₅' v (by simpa using hv), h₆'⟩
      · simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_map,
          SimpleGraph.Hom.coe_ofLE, List.map_id_fun, id_eq, mem_ofPred_eq]
        exact Or.inr h₂'
      · simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_map,
          SimpleGraph.Hom.coe_ofLE, List.map_id_fun, id_eq, mem_ofPred_eq]
        exact Or.inr h₃'
      · have hv' : v ∈ q'.support := by simpa using hv
        have hlab := h₄' v hv' hvx
        have hl₂ : v ∈ (P l).support ∨ v ∈ (p l).support := by
          simpa [SimpleGraph.Walk.mem_support_append_iff] using hl'
        rcases hl₂ with h₇ | h₇
        · have hxG : x ∈ G'.vertexSet := support_mem (p _) (hy (mem_range_self _)) h₂'
          have := hS.link.2.1 l v h₇ (support_mem q' hxG hv')
          exact hlab l (this ▸ (p l).start_mem_support)
        · exact hlab l h₇

/-- **(5.3)** (page 340). The numbers `i, j` of the paper are `c p` and `b`, and `{z_1, …,
z_{2g-1}}` are the values `c 0, c 1, …`. In place of the hypothesis on grid minors we have that no
family as in (5.1) exists. -/
theorem theorem_5_3 [Fintype ι] (hG : G.IsGraph) {T : Set (Hypergraph α β × Hypergraph α β)} {θ :
  ℕ} {z : ι → α} (hN : Nodule G T θ z) {g k : ℕ} (hg : 2 ≤ g) {c : ℕ → ι}
    (hc : ∀ a b, a < 2 * g - 1 → b < 2 * g - 1 → c a = c b → a = b) (hn : Fintype.card ι ≤ 2 * k)
      (hθ : k * 20 ^ (2 * g) ≤ θ) (hno : ¬ HasGrid G T θ g) : JumpEnd G T θ z k g c := by
  rcases exists_stage hG hN hg hc hn hθ (2 * g - 1) le_rfl with hj | ⟨G', T', θ', z', P, W₁, W₂,
    H₁, H₂, a, b, -, -, hC₁, hC₂, hab⟩
  · exact hj
  · rcases Nat.lt_or_ge a g with h | h
    · exact absurd (hC₂.hasGrid (by omega)) hno
    · exact absurd (hC₁.hasGrid h) hno

end GraphMinor.RST94
