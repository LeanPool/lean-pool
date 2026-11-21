/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.NestedDissection.Spec

/-!
# The filled graph of an elimination order

Let `G` be a simple graph and let the vertices be eliminated in increasing order of a rank
function `r : V → ℕ` (injective).  The *elimination game* eliminates the vertices one at a time;
eliminating `v` joins all neighbours of `v` that are eliminated after `v` into a clique.  The
graph of all original and added edges is the *filled graph*: it is the zero pattern of the
triangular factors of a symmetric matrix with graph `G` eliminated in this order.

Rose, Tarjan and Lueker [D. J. Rose, R. E. Tarjan, G. S. Lueker, *Algorithmic aspects of vertex
elimination on graphs*, SIAM J. Comput. 5 (1976), 266–283] characterize the filled graph by
paths: `u ≠ w` are adjacent in the filled graph iff `G` has a path from `u` to `w` all of whose
interior vertices are eliminated before both `u` and `w`.  This file takes that
characterization (with walks, `LowWalk`) as the definition of `fill`, proves that it agrees
with the elimination game (`game_adj_iff_fill`) and with the path form
(`fill_adj_iff_path`).

## Main definitions

`LowWalk`, `fill` and `laterNbrs` are defined in `NestedDissection/Spec.lean`, `game` here.

* `NestedDissection.LowWalk G r k u w`: a walk of positive length from `u` to `w` in `G` whose
  interior vertices all have rank `< k`.
* `NestedDissection.fill G r`: the filled graph.
* `NestedDissection.game G r k`: the graph after eliminating the vertices of rank `< k`.
* `NestedDissection.laterNbrs H r v`: the neighbours of `v` in `H` of larger rank.
-/

namespace NestedDissection

@[expose] public section

universe u v

variable {V : Type u} (G : SimpleGraph V) (r : V → ℕ)

namespace LowWalk

variable {G r} {k : ℕ} {u w : V}

theorem mono {k' : ℕ} (hk : k ≤ k') (h : LowWalk G r k u w) : LowWalk G r k' u w := by
  induction h with
  | adj h => exact .adj h
  | cons h hx _ ih => exact .cons h (lt_of_lt_of_le hx hk) ih

theorem zero_iff : LowWalk G r 0 u w ↔ G.Adj u w := by
  refine ⟨fun h => ?_, .adj⟩
  cases h with
  | adj h => exact h
  | cons _ hx _ => exact absurd hx (Nat.not_lt_zero _)

/-- Splitting a walk below `k + 1` at the (unique, by injectivity) vertex of rank `k`. -/
theorem succ_iff (hr : Function.Injective r) :
    LowWalk G r (k + 1) u w ↔
      LowWalk G r k u w ∨ ∃ v, r v = k ∧ LowWalk G r k u v ∧ LowWalk G r k v w := by
  constructor
  · intro h
    induction h with
    | adj h => exact .inl (.adj h)
    | @cons u x w hux hx _ ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | hx
      · rcases ih with ih | ⟨v, hv, h₁, h₂⟩
        · exact .inl (.cons hux hx ih)
        · exact .inr ⟨v, hv, .cons hux hx h₁, h₂⟩
      · refine .inr ⟨x, hx, .adj hux, ?_⟩
        rcases ih with ih | ⟨v, hv, _, h₂⟩
        · exact ih
        · rwa [hr (hv.trans hx.symm)] at h₂
  · rintro (h | ⟨v, hv, h₁, h₂⟩)
    · exact h.mono (Nat.le_succ k)
    · exact (h₁.mono (Nat.le_succ k)).trans (by omega) (h₂.mono (Nat.le_succ k))

/-- A low walk yields a walk in `G` whose vertices other than the endpoints have rank `< k`. -/
theorem exists_walk (h : LowWalk G r k u w) :
    ∃ p : G.Walk u w, ∀ x ∈ p.support, x ≠ u → x ≠ w → r x < k := by
  induction h with
  | @adj u w h =>
    refine ⟨.cons h .nil, fun x hx hxu hxw => ?_⟩
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> contradiction
  | @cons u x w hux hx _ ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨.cons hux p, fun y hy hyu hyw => ?_⟩
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact absurd rfl hyu
    by_cases hyx : y = x
    · rwa [hyx]
    · exact hp y hy hyx hyw

/-- A path whose interior vertices have rank `< k` gives a low walk. -/
theorem of_path {p : G.Walk u w} (hp : p.IsPath) (hne : u ≠ w)
    (h : ∀ x ∈ p.support, x ≠ u → x ≠ w → r x < k) : LowWalk G r k u w := by
  induction p with
  | nil => exact absurd rfl hne
  | @cons u x w hux p ih =>
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    by_cases hxw : x = w
    · subst hxw; exact .adj hux
    have hxu : x ≠ u := (G.ne_of_adj hux).symm
    refine .cons hux (h x (by simp) hxu hxw) (ih hp.1 hxw fun y hy hyx hyw => ?_)
    have hyu : y ≠ u := fun hyu => hp.2 (hyu ▸ hy)
    exact h y (by simp [hy]) hyu hyw

end LowWalk

variable {G r}

theorem fill_adj {u w : V} :
    (fill G r).Adj u w ↔ u ≠ w ∧ LowWalk G r (min (r u) (r w)) u w := Iff.rfl

theorem le_fill : G ≤ fill G r := fun _ _ h => ⟨G.ne_of_adj h, .adj h⟩

/-- **Path characterization of fill** (Rose–Tarjan–Lueker): `u` and `w` are adjacent in the
filled graph iff `u ≠ w` and `G` has a path from `u` to `w` whose interior vertices are all
eliminated before both `u` and `w`. -/
theorem fill_adj_iff_path {u w : V} :
    (fill G r).Adj u w ↔
      u ≠ w ∧ ∃ p : G.Walk u w, p.IsPath ∧
        ∀ x ∈ p.support, x ≠ u → x ≠ w → r x < r u ∧ r x < r w := by
  classical
  constructor
  · rintro ⟨hne, h⟩
    obtain ⟨p, hp⟩ := h.exists_walk
    refine ⟨hne, p.bypass, p.bypass_isPath, fun x hx hxu hxw => ?_⟩
    exact lt_min_iff.mp (hp x (p.support_bypass_subset_support hx) hxu hxw)
  · rintro ⟨hne, p, hp, h⟩
    exact ⟨hne, LowWalk.of_path hp hne fun x hx hxu hxw => lt_min_iff.mpr (h x hx hxu hxw)⟩

/-- A low walk below `k ≥ min (r u) (r w)` already gives a fill edge. -/
theorem fill_adj_of_lowWalk {u w : V} {k : ℕ} (hne : u ≠ w) (h : LowWalk G r k u w)
    (hk : k ≤ min (r u) (r w)) : (fill G r).Adj u w :=
  ⟨hne, h.mono hk⟩

/-! ### The elimination game -/

variable (G r)

/-- One move of the elimination game: eliminating the vertices of rank `k` joins any two of
their neighbours of rank `> k`. -/
def gameStep (k : ℕ) (H : SimpleGraph V) : SimpleGraph V :=
  H ⊔ SimpleGraph.fromRel fun u w => k < r u ∧ k < r w ∧ ∃ v, r v = k ∧ H.Adj u v ∧ H.Adj v w

/-- The graph of the elimination game after the vertices of rank `< k` are eliminated. -/
def game : ℕ → SimpleGraph V
  | 0 => G
  | k + 1 => gameStep r k (game k)

variable {G r}

theorem game_succ_adj {k : ℕ} {u w : V} :
    (game G r (k + 1)).Adj u w ↔
      (game G r k).Adj u w ∨
        (u ≠ w ∧ k < r u ∧ k < r w ∧ ∃ v, r v = k ∧ (game G r k).Adj u v ∧
          (game G r k).Adj v w) := by
  simp only [game, gameStep, SimpleGraph.sup_adj, SimpleGraph.fromRel_adj]
  constructor
  · rintro (h | ⟨hne, h | ⟨h₁, h₂, v, hv, a, b⟩⟩)
    · exact .inl h
    · exact .inr ⟨hne, h⟩
    · exact .inr ⟨hne, h₂, h₁, v, hv, b.symm, a.symm⟩
  · rintro (h | ⟨hne, h⟩)
    · exact .inl h
    · exact .inr ⟨hne, .inl h⟩

/-- The game graph restricted to vertices not yet eliminated is described by low walks. -/
theorem game_adj_iff (hr : Function.Injective r) {k : ℕ} {u w : V} (hu : k ≤ r u)
    (hw : k ≤ r w) : (game G r k).Adj u w ↔ u ≠ w ∧ LowWalk G r k u w := by
  induction k generalizing u w with
  | zero => exact ⟨fun h => ⟨G.ne_of_adj h, .adj h⟩, fun h => LowWalk.zero_iff.mp h.2⟩
  | succ k ih =>
    rw [game_succ_adj, ih (by omega) (by omega), LowWalk.succ_iff hr]
    constructor
    · rintro (⟨hne, h⟩ | ⟨hne, -, -, v, hv, h₁, h₂⟩)
      · exact ⟨hne, .inl h⟩
      · rw [ih (by omega) (by omega)] at h₁
        rw [ih (by omega) (by omega)] at h₂
        exact ⟨hne, .inr ⟨v, hv, h₁.2, h₂.2⟩⟩
    · rintro ⟨hne, h | ⟨v, hv, h₁, h₂⟩⟩
      · exact .inl ⟨hne, h⟩
      · refine .inr ⟨hne, by omega, by omega, v, hv, ?_, ?_⟩
        · rw [ih (by omega) (by omega)]; exact ⟨fun h => by subst h; omega, h₁⟩
        · rw [ih (by omega) (by omega)]; exact ⟨fun h => by subst h; omega, h₂⟩

/-- Edges at a vertex that has been eliminated never change afterwards. -/
theorem game_adj_stable {k : ℕ} {u w : V} (hk : min (r u) (r w) ≤ k) (m : ℕ) :
    (game G r (k + m)).Adj u w ↔ (game G r k).Adj u w := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← Nat.add_assoc, game_succ_adj, ih]
    constructor
    · rintro (h | ⟨-, hu, hw, -⟩)
      · exact h
      · exact absurd hk (by omega)
    · exact .inl

/-- **The elimination game computes the filled graph**: once the earlier of `u`, `w` has been
eliminated, they are adjacent in the game graph iff they are adjacent in `fill G r`. -/
theorem game_adj_iff_fill (hr : Function.Injective r) {k : ℕ} {u w : V}
    (hk : min (r u) (r w) ≤ k) : (game G r k).Adj u w ↔ (fill G r).Adj u w := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [game_adj_stable le_rfl, game_adj_iff hr (min_le_left _ _) (min_le_right _ _)]
  rfl

/-- For the natural order on `Fin n`, the final graph of the elimination game is `fill`. -/
theorem game_eq_fill {n : ℕ} (G : SimpleGraph (Fin n)) : game G Fin.val n = fill G Fin.val := by
  ext u w
  exact game_adj_iff_fill Fin.val_injective (by have := u.2; omega)

/-! ### Relabeling -/

theorem lowWalk_comap_iff {W : Type v} (e : W ≃ V) {k : ℕ} {u w : W} :
    LowWalk (G.comap e) (r ∘ e) k u w ↔ LowWalk G r k (e u) (e w) := by
  constructor
  · intro h
    induction h with
    | adj h => exact .adj h
    | cons h hx _ ih => exact .cons h hx ih
  · intro h
    generalize hu : e u = a at h
    generalize hw : e w = b at h
    induction h generalizing u with
    | adj h =>
      subst hu hw; exact .adj (by simpa using h)
    | @cons a x b h hx _ ih =>
      subst hu hw
      refine .cons (x := e.symm x) (by simpa using h) (by simpa using hx) (ih (by simp) rfl)

/-- The filled graph is compatible with relabeling the vertices. -/
theorem fill_comap {W : Type v} (e : W ≃ V) :
    fill (G.comap e) (r ∘ e) = (fill G r).comap e := by
  ext u w
  simp only [fill_adj, SimpleGraph.comap_adj, Function.comp_apply, lowWalk_comap_iff,
    e.injective.ne_iff]

/-! ### Later neighbours -/

theorem mem_laterNbrs [Fintype V] {H : SimpleGraph V} [DecidableRel H.Adj] {v w : V} :
    w ∈ laterNbrs r H v ↔ H.Adj v w ∧ r v < r w := by
  simp [laterNbrs]

/-- The number of edges of `H` is the sum over vertices of the number of later neighbours. -/
theorem sum_card_laterNbrs [Fintype V] (hr : Function.Injective r)
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∑ v, (laterNbrs r H v).card = H.edgeFinset.card := by
  classical
  rw [← Finset.card_sigma]
  refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
  · rintro ⟨v, w⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, mem_laterNbrs] at hp
    simpa using hp.1
  · rintro ⟨v, w⟩ hp ⟨v', w'⟩ hp' heq
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, mem_laterNbrs] at hp hp'
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd hp.2 (by have := hp'.2; dsimp only at this ⊢; omega)
  · intro e he
    induction e using Sym2.ind with
    | h v w =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      have hne : r v ≠ r w := fun h => H.ne_of_adj he (hr h)
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact ⟨⟨v, w⟩, by simp [mem_laterNbrs, he, h], rfl⟩
      · exact ⟨⟨w, v⟩, by simp [mem_laterNbrs, he.symm, h], Sym2.eq_swap⟩

end

end NestedDissection
