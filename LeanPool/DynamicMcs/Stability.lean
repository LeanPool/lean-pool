/-
Copyright (c) 2026 Md Thoriqul Islam Thonmay and Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Md Thoriqul Islam Thonmay, Gregory Morse
-/

-- Modified for Lean Pool.

module

public import LeanPool.DynamicMcs.Correctness

/-!
# Stability of MCS orderings under one-sided edge updates

`MCS(G)` denotes the set of MCS orderings of `G` under arbitrary tie-breaking
(`IsMCSOrderingAny`).

* `exists_common_ordering_prefix`: if along every proper common MCS prefix each
  unchosen vertex's count in `G'` is its count in `G` plus `0` or `1`, then
  `MCS(G) ∩ MCS(G') ≠ ∅`. `exists_common_ordering` is the every-subset special
  case, which is equivalent to `G'` being `G` plus a matching.
* Hence inserting a matching, deleting a matching, or flipping a single edge
  always leaves a common MCS ordering.
* The bound is sharp in two directions: flipping a matching whose edges are
  partly inserted and partly deleted (`n = 4`), or inserting a triangle
  (`n = 5`) or a path on four vertices (`n = 6`), can leave no common ordering.
  These are checked by a pruned search whose soundness is proved here and
  whose result is evaluated by the kernel.
-/

@[expose] public section

noncomputable section

namespace DynamicMcs
namespace Proofs

open UGraph

variable {n : ℕ}

lemma neigh_mono {G G' : UGraph n} (h : ∀ x y, G.adj x y → G'.adj x y)
    (S : Finset (Vert n)) (x : Vert n) : G.neigh S x ≤ G'.neigh S x := by
  classical
  rw [neigh_eq_filter_adj_card, neigh_eq_filter_adj_card]
  apply Finset.card_le_card
  intro y hy
  rw [Finset.mem_filter] at hy ⊢
  exact ⟨hy.1, h x y hy.2⟩

lemma neigh_le_add_one {G F G' : UGraph n} (hadd : AddsEdges G F G') (hF : IsMatching F)
    (S : Finset (Vert n)) (x : Vert n) : G'.neigh S x ≤ G.neigh S x + 1 := by
  classical
  rw [neigh_eq_filter_adj_card, neigh_eq_filter_adj_card]
  have hsub : S.filter (fun y => G'.adj x y) ⊆
      S.filter (fun y => G.adj x y) ∪ S.filter (fun y => F.adj x y) := by
    intro y hy
    rw [Finset.mem_filter] at hy
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases (hadd x y).1 hy.2 with h | h
    · exact Or.inl ⟨hy.1, h⟩
    · exact Or.inr ⟨hy.1, h⟩
  have hF1 : (S.filter (fun y => F.adj x y)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro y hy z hz
    exact hF x y z (Finset.mem_filter.1 hy).2 (Finset.mem_filter.1 hz).2
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (S.filter (fun y => G.adj x y)) (S.filter (fun y => F.adj x y))
  omega

/-- Some unchosen vertex is an MCS step in both graphs. Only the counts of
unchosen vertices matter, so the bounds are required only for `x ∉ S`. -/
theorem exists_common_pick (G G' : UGraph n) (S : Finset (Vert n))
    (hlo : ∀ x, x ∉ S → G.neigh S x ≤ G'.neigh S x)
    (hhi : ∀ x, x ∉ S → G'.neigh S x ≤ G.neigh S x + 1)
    (hS : S ≠ (Finset.univ : Finset (Vert n))) :
    ∃ w, IsMCSNextAny G S w ∧ IsMCSNextAny G' S w := by
  have hU : ((Finset.univ : Finset (Vert n)) \ S).Nonempty :=
    Finset.sdiff_nonempty.2 (fun hs => hS (Finset.univ_subset_iff.1 hs))
  obtain ⟨w, hwU, hw⟩ := Finset.exists_max_image _ (G.neigh S) hU
  obtain ⟨w', hw'U, hw'⟩ := Finset.exists_max_image _ (G'.neigh S) hU
  by_cases h : G'.neigh S w' ≤ G'.neigh S w
  · exact ⟨w, ⟨hwU, hw⟩, ⟨hwU, fun x hx => (hw' x hx).trans h⟩⟩
  · refine ⟨w', ⟨hw'U, fun x hx => ?_⟩, ⟨hw'U, hw'⟩⟩
    have h1 := hlo w (Finset.mem_sdiff.1 hwU).2
    have h2 := hhi w' (Finset.mem_sdiff.1 hw'U).2
    have h3 := hw x hx
    have h4 := hw w' hw'U
    omega

/-- Online form of the common-ordering theorem: any common MCS prefix — a
duplicate-free list `P` whose every step is a legal MCS step in *both* graphs —
extends to a full common MCS ordering of both graphs.  The count bounds are
required only along proper common prefixes and only for unchosen vertices,
exactly as in `exists_common_ordering_prefix`.  This is the constructive content
of that theorem: a maintainer that, at each step, picks any vertex that is
maximum in both graphs can extend its prefix forever, with no lookahead and no
backtracking. -/
theorem common_order_extends_prefix (G G' : UGraph n)
    (hlo : ∀ P, IsCommonPrefix G G' P → P.length < n →
             ∀ x, x ∉ P → G.neigh P.toFinset x ≤ G'.neigh P.toFinset x)
    (hhi : ∀ P, IsCommonPrefix G G' P → P.length < n →
             ∀ x, x ∉ P → G'.neigh P.toFinset x ≤ G.neigh P.toFinset x + 1)
    (P : List (Vert n)) (hnd : P.Nodup)
    (hsteps : ∀ i (hi : i < P.length),
      IsMCSNextAny G (P.take i).toFinset (P.get ⟨i, hi⟩) ∧
      IsMCSNextAny G' (P.take i).toFinset (P.get ⟨i, hi⟩)) :
    ∃ ord, G.IsMCSOrderingAny ord ∧ G'.IsMCSOrderingAny ord ∧ P <+: ord := by
  -- Strong induction on the number of vertices still to place, `n - P.length`.
  suffices h : ∀ m, ∀ P : List (Vert n), n - P.length = m → P.Nodup →
      (∀ i (hi : i < P.length),
        IsMCSNextAny G (P.take i).toFinset (P.get ⟨i, hi⟩) ∧
        IsMCSNextAny G' (P.take i).toFinset (P.get ⟨i, hi⟩)) →
      ∃ ord, G.IsMCSOrderingAny ord ∧ G'.IsMCSOrderingAny ord ∧ P <+: ord by
    exact h (n - P.length) P rfl hnd hsteps
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro P hm hnd hsteps
    by_cases hfull : P.length = n
    · exact ⟨P, ⟨hnd, hfull, fun i hi => (hsteps i hi).1⟩,
                  ⟨hnd, hfull, fun i hi => (hsteps i hi).2⟩, List.prefix_refl P⟩
    · have hPle : P.length ≤ n := by
        rw [← List.toFinset_card_of_nodup hnd]
        simpa using Finset.card_le_univ (P.toFinset : Finset (Vert n))
      have hlt : P.length < n := lt_of_le_of_ne hPle hfull
      have hne : P.toFinset ≠ (Finset.univ : Finset (Vert n)) := by
        intro h
        have hc : P.toFinset.card = n := by rw [h, Finset.card_univ, Fintype.card_fin]
        rw [List.toFinset_card_of_nodup hnd] at hc
        omega
      obtain ⟨w, hwG, hwG'⟩ :=
        exists_common_pick G G' P.toFinset
          (fun x hx => hlo P ⟨hnd, hsteps⟩ hlt x (fun hm => hx (List.mem_toFinset.2 hm)))
          (fun x hx => hhi P ⟨hnd, hsteps⟩ hlt x (fun hm => hx (List.mem_toFinset.2 hm))) hne
      have hwP : w ∉ P :=
        fun hmem => (Finset.mem_sdiff.1 hwG.1).2 (List.mem_toFinset.2 hmem)
      have hnd' : (P ++ [w]).Nodup := by
        rw [List.nodup_append]
        exact ⟨hnd, List.nodup_singleton w, fun x hx y hy => by
          rw [List.mem_singleton] at hy
          subst hy
          intro hxy
          subst hxy
          exact hwP hx⟩
      have hsteps' : ∀ i (hi : i < (P ++ [w]).length),
          IsMCSNextAny G ((P ++ [w]).take i).toFinset ((P ++ [w]).get ⟨i, hi⟩) ∧
          IsMCSNextAny G' ((P ++ [w]).take i).toFinset ((P ++ [w]).get ⟨i, hi⟩) :=
        fun i hi => steps_append (Q := fun S x =>
          IsMCSNextAny G S x ∧ IsMCSNextAny G' S x) P w hsteps ⟨hwG, hwG'⟩ i hi
      have hltm : n - (P ++ [w]).length < m := by
        have hlen_app : (P ++ [w]).length = P.length + 1 := List.length_append ..
        omega
      obtain ⟨ord, hordG, hordG', hpref⟩ :=
        ih (n - (P ++ [w]).length) hltm (P ++ [w]) rfl hnd' hsteps'
      exact ⟨ord, hordG, hordG', (List.prefix_append P [w]).trans hpref⟩

/-- If, along every *proper common MCS prefix* `P` (the sets the constructive
proof actually visits), the count of every vertex not in `P` in `G'` is its count
in `G` plus `0` or `1`, the two graphs share an MCS ordering. This is strictly
more general than `exists_common_ordering`: the bound is required only on
reachable prefixes and only for unchosen vertices, not on every subset. -/
theorem exists_common_ordering_prefix (G G' : UGraph n)
    (hlo : ∀ P, IsCommonPrefix G G' P → P.length < n →
             ∀ x, x ∉ P → G.neigh P.toFinset x ≤ G'.neigh P.toFinset x)
    (hhi : ∀ P, IsCommonPrefix G G' P → P.length < n →
             ∀ x, x ∉ P → G'.neigh P.toFinset x ≤ G.neigh P.toFinset x + 1) :
    ∃ ord, IsMCSOrderingAny G ord ∧ IsMCSOrderingAny G' ord := by
  obtain ⟨order, oldValid, newValid, _⟩ :=
    common_order_extends_prefix G G' hlo hhi [] List.nodup_nil (fun i hi => by simp at hi)
  exact ⟨order, oldValid, newValid⟩

/-- If counts in `G'` exceed counts in `G` by `0` or `1` for every vertex and
every subset `S`, some ordering is an MCS ordering of both graphs. This
every-subset hypothesis is equivalent to `G'` being `G` plus a matching; it is
the special case of `exists_common_ordering_prefix` in which the bound holds
everywhere, not only on common prefixes. -/
theorem exists_common_ordering (G G' : UGraph n)
    (hlo : ∀ S x, G.neigh S x ≤ G'.neigh S x) (hhi : ∀ S x, G'.neigh S x ≤ G.neigh S x + 1) :
    ∃ ord, IsMCSOrderingAny G ord ∧ IsMCSOrderingAny G' ord :=
  exists_common_ordering_prefix G G'
    (fun _ _ _ x _ => hlo _ x) (fun _ _ _ x _ => hhi _ x)

/-- Inserting a matching leaves a common MCS ordering. -/
theorem insert_matching_common_order {G F G' : UGraph n} (hadd : AddsEdges G F G')
    (hF : IsMatching F) : ∃ ord, IsMCSOrderingAny G ord ∧ IsMCSOrderingAny G' ord :=
  exists_common_ordering G G'
    (fun S x => neigh_mono (fun x y h => (hadd x y).2 (Or.inl h)) S x)
    (fun S x => neigh_le_add_one hadd hF S x)

/-- Deleting a matching leaves a common MCS ordering. -/
theorem delete_matching_common_order {G F G' : UGraph n} (hadd : AddsEdges G' F G)
    (hF : IsMatching F) : ∃ ord, IsMCSOrderingAny G ord ∧ IsMCSOrderingAny G' ord := by
  obtain ⟨ord, h₁, h₂⟩ := insert_matching_common_order hadd hF
  exact ⟨ord, h₂, h₁⟩

/-- The graph with the single edge `{u, v}`. -/
def edgeGraph (u v : Vert n) (huv : u ≠ v) : UGraph n where
  adj x y := (x = u ∧ y = v) ∨ (x = v ∧ y = u)
  symm := by
    rintro x y (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inl ⟨h2, h1⟩
  loopless := by
    rintro x (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact huv (h1.symm.trans h2)
    · exact huv (h2.symm.trans h1)

/-- The graph with no edges. -/
def emptyGraph (n : ℕ) : UGraph n where
  adj _ _ := False
  symm h := h
  loopless _ h := h

lemma edgeGraph_isMatching (u v : Vert n) (huv : u ≠ v) : IsMatching (edgeGraph u v huv) := by
  intro x y z hy hz
  rcases hy with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rcases hz with ⟨hx', hz⟩ | ⟨hx', hz⟩
  · exact hy.trans hz.symm
  · exact absurd (hx.symm.trans hx') huv
  · exact absurd (hx'.symm.trans hx) huv
  · exact hy.trans hz.symm

lemma emptyGraph_isMatching : IsMatching (emptyGraph n) := fun _ _ _ h => h.elim

lemma flip_adj_iff {G G' : UGraph n} {u v : Vert n} (hflip : FlipOf G G' u v) (x y : Vert n)
    (hp : ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))) : G'.adj x y ↔ G.adj x y := by
  rcases hflip.2 x y with he | he | he
  · rw [he]
  · exact absurd (Or.inl he) hp
  · exact absurd (Or.inr he) hp

/-- Flipping a single edge leaves a common MCS ordering. -/
theorem flip_common_order {G G' : UGraph n} {u v : Vert n} (hflip : FlipOf G G' u v) :
    ∃ ord, IsMCSOrderingAny G ord ∧ IsMCSOrderingAny G' ord := by
  have huv := hflip.1
  by_cases h' : G'.adj u v
  · refine insert_matching_common_order (F := edgeGraph u v huv) (fun x y => ?_)
      (edgeGraph_isMatching u v huv)
    by_cases hp : (x = u ∧ y = v) ∨ (x = v ∧ y = u)
    · refine ⟨fun _ => Or.inr hp, fun _ => ?_⟩
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h'
      · exact G'.symm h'
    · rw [flip_adj_iff hflip x y hp]
      exact ⟨Or.inl, fun h => h.elim id (fun hF => absurd hF hp)⟩
  · by_cases h : G.adj u v
    · refine delete_matching_common_order (F := edgeGraph u v huv) (fun x y => ?_)
        (edgeGraph_isMatching u v huv)
      by_cases hp : (x = u ∧ y = v) ∨ (x = v ∧ y = u)
      · refine ⟨fun _ => Or.inr hp, fun _ => ?_⟩
        rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h
        · exact G.symm h
      · rw [flip_adj_iff hflip x y hp]
        exact ⟨Or.inl, fun h => h.elim id (fun hF => absurd hF hp)⟩
    · refine insert_matching_common_order (F := emptyGraph n) (fun x y => ?_) emptyGraph_isMatching
      by_cases hp : (x = u ∧ y = v) ∨ (x = v ∧ y = u)
      · have hG' : ¬ G'.adj x y := by
          rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact h'
          · exact fun hvu => h' (G'.symm hvu)
        have hG : ¬ G.adj x y := by
          rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact h
          · exact fun hvu => h (G.symm hvu)
        exact ⟨fun hx => absurd hx hG', fun hx => hx.elim (fun hx => absurd hx hG) False.elim⟩
      · rw [flip_adj_iff hflip x y hp]
        exact ⟨Or.inl, fun h => h.elim id False.elim⟩

/-! ## Certified counterexamples -/

instance ofEdgesDecidableRel (E : List (ℕ × ℕ)) : DecidableRel (ofEdges n E).adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧ ((x.val, y.val) ∈ E ∨ (y.val, x.val) ∈ E)))

/-- Number of neighbors of `w` in the list `L`, in the graph `ofEdges n E`. -/
def cntB (E : List (ℕ × ℕ)) (L : List (Fin n)) (w : Fin n) : ℕ :=
  (L.filter (fun y => decide ((ofEdges n E).adj w y))).length

/-- Boolean check that `w` is an MCS step (any tie-break) after the prefix `L`. -/
def stepB (E : List (ℕ × ℕ)) (L : List (Fin n)) (w : Fin n) : Bool :=
  !(L.contains w) &&
    (List.finRange n).all (fun x => L.contains x || decide (cntB E L x ≤ cntB E L w))

/-- Search for a common MCS ordering of `ofEdges n E₁` and `ofEdges n E₂`
extending `L` by `k` more steps, branching only over common MCS steps. -/
def commonSearch (E₁ E₂ : List (ℕ × ℕ)) : ℕ → List (Fin n) → Bool
  | 0, _ => true
  | k + 1, L => (List.finRange n).any
      (fun x => stepB E₁ L x && stepB E₂ L x && commonSearch E₁ E₂ k (L ++ [x]))

lemma neigh_ofEdges (E : List (ℕ × ℕ)) (L : List (Fin n)) (hL : L.Nodup) (w : Fin n) :
    (ofEdges n E).neigh L.toFinset w = cntB E L w := by
  rw [neigh_eq_filter_adj_card, cntB, ← List.toFinset_card_of_nodup (hL.filter _),
    List.toFinset_filter]
  congr 1
  exact Finset.ext fun y => by simp [Finset.mem_filter]

lemma stepB_of_any (E : List (ℕ × ℕ)) (L : List (Fin n)) (hL : L.Nodup) (w : Fin n)
    (h : IsMCSNextAny (ofEdges n E) L.toFinset w) : stepB E L w = true := by
  obtain ⟨hw, hmax⟩ := h
  have hwL : w ∉ L := fun hm => (Finset.mem_sdiff.1 hw).2 (List.mem_toFinset.2 hm)
  unfold stepB
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨by simpa using hwL, fun x _ => ?_⟩
  by_cases hx : x ∈ L
  · simp [hx]
  · have hle := hmax x (Finset.mem_sdiff.2
      ⟨Finset.mem_univ x, fun hm => hx (List.mem_toFinset.1 hm)⟩)
    rw [neigh_ofEdges E L hL, neigh_ofEdges E L hL] at hle
    simp [hx, hle]

lemma commonSearch_of_common (E₁ E₂ : List (ℕ × ℕ)) (ord : List (Fin n))
    (h₁ : IsMCSOrderingAny (ofEdges n E₁) ord) (h₂ : IsMCSOrderingAny (ofEdges n E₂) ord) :
    ∀ j i, i + j = n → commonSearch E₁ E₂ j (ord.take i) = true := by
  intro j
  induction j with
  | zero => intro i _; simp [commonSearch]
  | succ j ih =>
      intro i hij
      have hi : i < ord.length := by rw [h₁.2.1]; omega
      have hnd : (ord.take i).Nodup := h₁.1.sublist (List.take_sublist _ _)
      have hcat : ord.take i ++ [ord[i]] = ord.take (i + 1) := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi]
        rfl
      simp only [commonSearch, List.any_eq_true, Bool.and_eq_true]
      refine ⟨ord[i], List.mem_finRange _, ⟨?_, ?_⟩, ?_⟩
      · exact stepB_of_any E₁ _ hnd _ (h₁.2.2 i hi)
      · exact stepB_of_any E₂ _ hnd _ (h₂.2.2 i hi)
      · rw [hcat]
        exact ih (i + 1) (by omega)

/-- A failed search certifies that no common MCS ordering exists. -/
theorem no_common_order_of_search (E₁ E₂ : List (ℕ × ℕ))
    (hsearch : commonSearch (n := n) E₁ E₂ n [] = false) :
    ¬ ∃ ord, IsMCSOrderingAny (ofEdges n E₁) ord ∧ IsMCSOrderingAny (ofEdges n E₂) ord := by
  rintro ⟨ord, h₁, h₂⟩
  have h := commonSearch_of_common E₁ E₂ ord h₁ h₂ n 0 (by omega)
  rw [List.take_zero, hsearch] at h
  exact Bool.false_ne_true h

/-! ## Concrete counterexamples (no common MCS ordering)

Each theorem asserts that two specific graphs (given as edge lists) have no
common MCS ordering, proved by applying `no_common_order_of_search` and
discharging its search hypothesis by kernel `decide`. Each theorem proves one
explicit witness. The witnesses were found by the exhaustive harnesses in
`scripts/mcs_stability.py` and `scripts/stab.c`, which also report that no
smaller host works; that minimality is a computer-search result, not a Lean
theorem. -/

/-- Inserting the triangle on `{2,3,4}` into `G` leaves no common MCS ordering. -/
theorem triangle_no_common_order :
    ¬ ∃ ord, IsMCSOrderingAny (ofEdges 5 [(0,2),(0,4),(1,2),(1,3)]) ord ∧
      IsMCSOrderingAny (ofEdges 5 ([(0,2),(0,4),(1,2),(1,3)] ++ [(2,3),(2,4),(3,4)])) ord := by
  apply no_common_order_of_search (n := 5)
  decide

/-- Inserting the path `2-5-4-3` (= P4 on `{2,3,4,5}`) into `G` leaves no common
MCS ordering. -/
theorem p4_no_common_order :
    ¬ ∃ ord, IsMCSOrderingAny (ofEdges 6 [(0,3),(0,5),(1,2),(1,4),(2,3)]) ord ∧
      IsMCSOrderingAny
        (ofEdges 6 ([(0,3),(0,5),(1,2),(1,4),(2,3)] ++ [(2,5),(3,4),(4,5)])) ord := by
  apply no_common_order_of_search (n := 6)
  decide

/-- Flipping a matching whose edges are partly inserted and partly deleted
(deleting `01`, inserting `23`) leaves no common MCS ordering. -/
theorem mixed_matching_no_common_order :
    ¬ ∃ ord, IsMCSOrderingAny (ofEdges 4 [(0,1),(0,3),(1,2)]) ord ∧
      IsMCSOrderingAny (ofEdges 4 [(0,3),(1,2),(2,3)]) ord := by
  apply no_common_order_of_search (n := 4)
  decide

/-- Inserting the matching-like one-sided update `2P3` (the four edges
`01, 02, 34, 35`, forming two disjoint length-2 paths) into the five-edge graph
on eight vertices leaves no common MCS ordering. Only this witness is proved
here. The exhaustive sweep in `scripts/stab.c` finds no failing host for `2P3`
on `n ≤ 7` and 13,644 failing hosts out of 2^24 on `n = 8`; that search result
is not a Lean theorem. -/
theorem two_p3_no_common_order :
    ¬ ∃ ord,
      IsMCSOrderingAny (ofEdges 8 [(1,5),(1,7),(2,4),(2,6),(4,5)]) ord ∧
      IsMCSOrderingAny
        (ofEdges 8 ([(1,5),(1,7),(2,4),(2,6),(4,5)] ++
          [(0,1),(0,2),(3,4),(3,5)])) ord := by
  apply no_common_order_of_search (n := 8)
  decide

end Proofs
end DynamicMcs
