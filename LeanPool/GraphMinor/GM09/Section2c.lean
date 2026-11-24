/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
public import LeanPool.GraphMinor.GM09.Basic

/-!
# Graph Minors IX, Section 2 (Part 3): Disjoint `X → Y` Paths and Lemma (2.2)

This file formalizes Lemma (2.2) from Section 2 of
N. Robertson and P. D. Seymour, *Graph Minors. IX. Disjoint crossed paths*,
J. Combin. Theory Ser. B **49** (1990) 40–77 (page 44), proving that a family of mutually
disjoint `X → Y` paths witnessing `X' ⇒ Y'` can be extended to size `k` when `k` mutually
disjoint `X → Y` paths exist, via an augmenting path argument.
-/

public section

namespace GraphMinor.GM09

open Set Graph Surface

universe u v

variable {α : Type u} {β : Type v}

theorem IsFromToPathWithEnds.left_mem_X {G P : Graph α β} {X Y : Set α} {x y : α}
    (h : IsFromToPathWithEnds G P X Y x y) : x ∈ X := by
  have hx : x ∈ V(P) ∩ X := by rw [h.2.1]; exact rfl
  exact hx.2

theorem IsFromToPathWithEnds.right_mem_Y {G P : Graph α β} {X Y : Set α} {x y : α}
    (h : IsFromToPathWithEnds G P X Y x y) : y ∈ Y := by
  have hy : y ∈ V(P) ∩ Y := by rw [h.2.2]; exact rfl
  exact hy.2

theorem IsFromToPathWithEnds.eq_left_of_mem_X {G P : Graph α β} {X Y : Set α} {x y z : α}
    (h : IsFromToPathWithEnds G P X Y x y) (hzP : z ∈ V(P)) (hzX : z ∈ X) : z = x := by
  have : z ∈ V(P) ∩ X := ⟨hzP, hzX⟩
  rwa [h.2.1, mem_singleton_iff] at this

theorem IsFromToPathWithEnds.eq_right_of_mem_Y {G P : Graph α β} {X Y : Set α} {x y z : α}
    (h : IsFromToPathWithEnds G P X Y x y) (hzP : z ∈ V(P)) (hzY : z ∈ Y) : z = y := by
  have : z ∈ V(P) ∩ Y := ⟨hzP, hzY⟩
  rwa [h.2.2, mem_singleton_iff] at this

/-- If `P : Fin r → Graph α β` is a family of `r` mutually disjoint `X → Y` paths with starts
`x : Fin r → α` and ends `y : Fin r → α`, then `x` and `y` are injective, `(range x).ncard = r`,
`(range y).ncard = r`, and `RedirectsTo G X Y (range x) (range y)` holds. -/
theorem redirectsTo_of_disjoint_fromToPaths {G : Graph α β} {X Y : Set α} {r : ℕ}
    {P : Fin r → Graph α β} {x y : Fin r → α}
    (hdisj : Pairwise (fun i j => Disjoint V(P i) V(P j)))
    (hP : ∀ i : Fin r, IsFromToPathWithEnds G (P i) X Y (x i) (y i)) :
    Function.Injective x ∧ Function.Injective y ∧
    (range x).ncard = r ∧ (range y).ncard = r ∧
    RedirectsTo G X Y (range x) (range y) := by
  have hx_inj : Function.Injective x := by
    intro i j hij
    by_contra hne
    exact disjoint_left.mp (hdisj hne) (hP i).1.left_mem (hij ▸ (hP j).1.left_mem)
  have hy_inj : Function.Injective y := by
    intro i j hij
    by_contra hne
    exact disjoint_left.mp (hdisj hne) (hP i).1.right_mem (hij ▸ (hP j).1.right_mem)
  have hx_card : (range x).ncard = r := by
    rw [ncard_range_of_injective hx_inj, Nat.card_fin]
  have hy_card : (range y).ncard = r := by
    rw [ncard_range_of_injective hy_inj, Nat.card_fin]
  refine ⟨hx_inj, hy_inj, hx_card, hy_card, ?_⟩
  refine ⟨?_, ?_, hx_card.trans hy_card.symm, ?_⟩
  · rintro _ ⟨i, rfl⟩; exact (hP i).left_mem_X
  · rintro _ ⟨i, rfl⟩; exact (hP i).right_mem_Y
  · refine ⟨fun i => P (Fin.cast hx_card i),
      fun i j hij => hdisj (fun h => hij (Fin.cast_injective hx_card h)),
      fun i => ⟨x (Fin.cast hx_card i), mem_range_self _,
        y (Fin.cast hx_card i), mem_range_self _, hP (Fin.cast hx_card i)⟩⟩

/-- Conversely, if `RedirectsTo G X Y X' Y'` holds with `X'.Finite`, `Y'.Finite`, and `X'.ncard =
r`,
there exist `P : Fin r → Graph α β` and `x, y : Fin r → α` with `range x = X'` and `range y = Y'`.
-/
theorem exists_indexed_of_redirectsTo {G : Graph α β} {X Y X' Y' : Set α} {r : ℕ}
    (hX'_fin : X'.Finite) (hY'_fin : Y'.Finite)
    (hred : RedirectsTo G X Y X' Y') (hr : X'.ncard = r) :
    ∃ (P : Fin r → Graph α β) (x y : Fin r → α),
      Pairwise (fun i j => Disjoint V(P i) V(P j)) ∧
      (∀ i : Fin r, IsFromToPathWithEnds G (P i) X Y (x i) (y i)) ∧
      range x = X' ∧ range y = Y' := by
  classical
  rcases hred with ⟨hX', hY', hcard_eq, P₀, hdisj₀, hP₀⟩
  let P : Fin r → Graph α β := fun i => P₀ (Fin.cast hr.symm i)
  have hdisj : Pairwise (fun i j => Disjoint V(P i) V(P j)) :=
    fun i j hij => hdisj₀ (fun h => hij (Fin.cast_injective hr.symm h))
  have hP_ex : ∀ i : Fin r, ∃ xi ∈ X', ∃ yi ∈ Y', IsFromToPathWithEnds G (P i) X Y xi yi :=
    fun i => hP₀ (Fin.cast hr.symm i)
  choose x hx y hy hP using hP_ex
  obtain ⟨hx_inj, hy_inj, hx_card, hy_card, _⟩ := redirectsTo_of_disjoint_fromToPaths hdisj hP
  have hx_range_sub : range x ⊆ X' := by rintro _ ⟨i, rfl⟩; exact hx i
  have hy_range_sub : range y ⊆ Y' := by rintro _ ⟨i, rfl⟩; exact hy i
  have hx_eq : range x = X' :=
    eq_of_subset_of_ncard_le hx_range_sub (by omega) hX'_fin
  have hy_eq : range y = Y' :=
    eq_of_subset_of_ncard_le hy_range_sub (by omega) hY'_fin
  exact ⟨P, x, y, hdisj, hP, hx_eq, hy_eq⟩

/-- Given `r < k`, a family `P : Fin r → Graph α β` of `r` mutually disjoint `X → Y` paths with ends
`x i` and `y i`, and a family `Q : Fin k → Graph α β` of `k` mutually disjoint `X → Y` paths with
ends `a j` and `b j`, there exists an index `j₀ : Fin k` such that `a j₀ ∉ range x`, and any such
`Q j₀` is disjoint from `range x`. -/
theorem exists_unmatched_start {G : Graph α β} {X Y : Set α} {r k : ℕ} (hrk : r < k)
    {P : Fin r → Graph α β} {x y : Fin r → α}
    (hdisjP : Pairwise (fun i j => Disjoint V(P i) V(P j)))
    (hP : ∀ i : Fin r, IsFromToPathWithEnds G (P i) X Y (x i) (y i))
    {Q : Fin k → Graph α β} {a b : Fin k → α}
    (hdisjQ : Pairwise (fun i j => Disjoint V(Q i) V(Q j)))
    (hQ : ∀ j : Fin k, IsFromToPathWithEnds G (Q j) X Y (a j) (b j)) :
    ∃ j₀ : Fin k, a j₀ ∉ range x ∧ Disjoint V(Q j₀) (range x) := by
  obtain ⟨hx_inj, _, hx_card, _, _⟩ := redirectsTo_of_disjoint_fromToPaths hdisjP hP
  obtain ⟨ha_inj, _, ha_card, _, _⟩ := redirectsTo_of_disjoint_fromToPaths hdisjQ hQ
  have hnot_sub : ¬ range a ⊆ range x := by
    intro hsub
    have hle := ncard_le_ncard hsub (finite_range x)
    omega
  obtain ⟨_, ⟨j₀, rfl⟩, hj₀_not⟩ := not_subset.mp hnot_sub
  refine ⟨j₀, hj₀_not, disjoint_left.mpr fun z hzQ ⟨i, hi⟩ => ?_⟩
  subst hi
  have hza : x i = a j₀ := (hQ j₀).eq_left_of_mem_X hzQ (hP i).left_mem_X
  exact hj₀_not ⟨i, hza⟩

/-- If `P` is a path in `G` from `u` to `v` and `V(P)` meets a set `S`, then there is a last vertex
`z ∈ V(P) ∩ S` along `P` (closest to `v`), so the subpath `P₂` of `P` from `z` to `v` satisfies
`V(P₂) ∩ S = {z}` and `(u ∈ V(P₂) → z = u)`. -/
theorem IsGraphPathWithEnds.exists_last_hit {G P : Graph α β} {u v : α}
    (hP : IsGraphPathWithEnds G P u v) {S : Set α} (hne : (V(P) ∩ S).Nonempty) :
    ∃ z ∈ V(P) ∩ S, ∃ P₂ : Graph α β,
      P₂ ≤ P ∧ IsGraphPathWithEnds P P₂ z v ∧ V(P₂) ∩ S = {z} ∧ (u ∈ V(P₂) → z = u) := by
  classical
  have hind : ∀ (n : ℕ) {a : α} {Q : Graph α β},
      Q ≤ P → IsGraphPathWithEnds P Q a v → V(Q).ncard = n → (V(Q) ∩ S).Nonempty →
      ∃ z ∈ V(Q) ∩ S, ∃ Q₂ : Graph α β,
        Q₂ ≤ Q ∧ IsGraphPathWithEnds Q Q₂ z v ∧ V(Q₂) ∩ S = {z} ∧ (a ∈ V(Q₂) → z = a) := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro a Q hQP hQ hcard ⟨w, hwQ, hwS⟩
      by_cases hhit : ∃ w' ∈ V(Q) ∩ S, w' ≠ a
      · obtain ⟨w', ⟨hw'Q, hw'S⟩, hw'a⟩ := hhit
        obtain ⟨Q₁, Q₂, _, hQ₂Q, hQ₁, hQ₂, _, hinter, _⟩ := hQ.exists_split_at hw'Q
        have ha_not_Q₂ : a ∉ V(Q₂) := by
          intro haQ₂
          have : a ∈ V(Q₁) ∩ V(Q₂) := ⟨hQ₁.left_mem, haQ₂⟩
          rw [hinter, mem_singleton_iff] at this
          exact hw'a this.symm
        have hlt : V(Q₂).ncard < n := by
          rw [← hcard]
          exact ncard_lt_ncard ⟨hQ₂Q.vertexSet_mono, fun h => ha_not_Q₂ (h hQ.left_mem)⟩
            hQ.vertexSet_finite
        obtain ⟨z, ⟨hzQ₂, hzS⟩, R₂, hR₂Q₂, hR₂, hR₂S, _⟩ :=
          ih V(Q₂).ncard hlt (hQ₂Q.trans hQP) (hQ₂.mono hQP) rfl ⟨w', hQ₂.left_mem, hw'S⟩
        exact ⟨z, ⟨hQ₂Q.vertexSet_mono hzQ₂, hzS⟩, R₂, hR₂Q₂.trans hQ₂Q, hR₂.mono hQ₂Q, hR₂S,
          fun haR₂ => (ha_not_Q₂ (hR₂Q₂.vertexSet_mono haR₂)).elim⟩
      · have haS : a ∈ S := by
          by_contra ha_not_S
          exact hhit ⟨w, ⟨hwQ, hwS⟩, fun h => ha_not_S (h ▸ hwS)⟩
        refine ⟨a, ⟨hQ.left_mem, haS⟩, Q, le_rfl, hQ.of_le le_rfl, ?_, fun _ => rfl⟩
        ext x
        simp only [mem_inter_iff, mem_singleton_iff]
        exact ⟨fun ⟨hxQ, hxS⟩ => by_contra fun hne => hhit ⟨x, ⟨hxQ, hxS⟩, hne⟩,
          fun h => h ▸ ⟨hQ.left_mem, haS⟩⟩
  exact hind V(P).ncard le_rfl (hP.of_le le_rfl) rfl hne

/-- Similarly, if `P` is a path in `G` from `u` to `v` and `V(P)` meets a set `S`, then there is a
first vertex `z ∈ V(P) ∩ S` along `P` (closest to `u`), so the subpath `P₁` of `P` from `u` to `z`
satisfies `V(P₁) ∩ S = {z}` and `(v ∈ V(P₁) → z = v)`. -/
theorem IsGraphPathWithEnds.exists_first_hit {G P : Graph α β} {u v : α}
    (hP : IsGraphPathWithEnds G P u v) {S : Set α} (hne : (V(P) ∩ S).Nonempty) :
    ∃ z ∈ V(P) ∩ S, ∃ P₁ : Graph α β,
      P₁ ≤ P ∧ IsGraphPathWithEnds P P₁ u z ∧ V(P₁) ∩ S = {z} ∧ (v ∈ V(P₁) → z = v) := by
  obtain ⟨z, hz, P₁, hP₁, hpath₁, hS, hv⟩ := hP.symm.exists_last_hit hne
  exact ⟨z, hz, P₁, hP₁, hpath₁.symm, hS, hv⟩

/-- If `Q` is an `X → Y` path with ends `u, v` and `z ∈ V(Q) \ {u}`, then the subpath `Q₂` of `Q`
from `z` to `v` satisfies `Disjoint V(Q₂) X` and `V(Q₂) ∩ Y = {v}`. -/
theorem IsFromToPathWithEnds.exists_suffix_disjoint_X {G Q : Graph α β} {X Y : Set α} {u v z : α}
    (hQ : IsFromToPathWithEnds G Q X Y u v) (hz : z ∈ V(Q)) (hzu : z ≠ u) :
    ∃ Q₂ : Graph α β, Q₂ ≤ Q ∧ IsGraphPathWithEnds G Q₂ z v ∧
      Disjoint V(Q₂) X ∧ V(Q₂) ∩ Y = {v} := by
  obtain ⟨Q₁, Q₂, _, hQ₂Q, hQ₁, hQ₂, _, hinter, _⟩ := hQ.1.exists_split_at hz
  refine ⟨Q₂, hQ₂Q, hQ₂.mono hQ.1.le, ?_, ?_⟩
  · rw [disjoint_left]
    intro w hwQ₂ hwX
    have hwu : w = u := hQ.eq_left_of_mem_X (hQ₂Q.vertexSet_mono hwQ₂) hwX
    subst hwu
    have : w ∈ V(Q₁) ∩ V(Q₂) := ⟨hQ₁.left_mem, hwQ₂⟩
    rw [hinter, mem_singleton_iff] at this
    exact hzu this.symm
  · ext w
    simp only [mem_inter_iff, mem_singleton_iff]
    exact ⟨fun ⟨hwQ₂, hwY⟩ => hQ.eq_right_of_mem_Y (hQ₂Q.vertexSet_mono hwQ₂) hwY,
      fun h => h ▸ ⟨hQ₂.right_mem, hQ.right_mem_Y⟩⟩

/-- If `P` is an `X → Y` path with ends `u, v` and `z ∈ V(P) \ {v}`, then the subpath `P₁` of `P`
from `u` to `z` satisfies `V(P₁) ∩ X = {u}` and `Disjoint V(P₁) Y`. -/
theorem IsFromToPathWithEnds.exists_prefix_disjoint_Y {G P : Graph α β} {X Y : Set α} {u v z : α}
    (hP : IsFromToPathWithEnds G P X Y u v) (hz : z ∈ V(P)) (hzv : z ≠ v) :
    ∃ P₁ : Graph α β, P₁ ≤ P ∧ IsGraphPathWithEnds G P₁ u z ∧
      V(P₁) ∩ X = {u} ∧ Disjoint V(P₁) Y := by
  obtain ⟨P₁, P₂, hP₁P, _, hP₁, hP₂, _, hinter, _⟩ := hP.1.exists_split_at hz
  refine ⟨P₁, hP₁P, hP₁.mono hP.1.le, ?_, ?_⟩
  · ext w
    simp only [mem_inter_iff, mem_singleton_iff]
    exact ⟨fun ⟨hwP₁, hwX⟩ => hP.eq_left_of_mem_X (hP₁P.vertexSet_mono hwP₁) hwX,
      fun h => h ▸ ⟨hP₁.left_mem, hP.left_mem_X⟩⟩
  · rw [disjoint_left]
    intro w hwP₁ hwY
    have hwv : w = v := hP.eq_right_of_mem_Y (hP₁P.vertexSet_mono hwP₁) hwY
    subst hwv
    have : w ∈ V(P₁) ∩ V(P₂) := ⟨hwP₁, hP₂.right_mem⟩
    rw [hinter, mem_singleton_iff] at this
    exact hzv this.symm

/-- If `P₁` is a path in `G` from `u ∈ X` to `z` with `V(P₁) ∩ X = {u}` and `Disjoint V(P₁) Y`,
and `Q₂` is a path in `G` from `z` to `v ∈ Y` with `Disjoint V(Q₂) X` and `V(Q₂) ∩ Y = {v}`,
and `V(P₁) ∩ V(Q₂) = {z}`, then `subgraphUnion G P₁ Q₂` is an `X → Y` path in `G` from `u` to `v`.
-/
theorem isFromToPathWithEnds_subgraphUnion_at {G P₁ Q₂ : Graph α β} {X Y : Set α} {u z v : α}
    (hP₁ : IsGraphPathWithEnds G P₁ u z) (hP₁X : V(P₁) ∩ X = {u}) (hP₁Y : Disjoint V(P₁) Y)
    (hQ₂ : IsGraphPathWithEnds G Q₂ z v) (hQ₂X : Disjoint V(Q₂) X) (hQ₂Y : V(Q₂) ∩ Y = {v})
    (hinter : V(P₁) ∩ V(Q₂) = {z}) :
    IsFromToPathWithEnds G (subgraphUnion G P₁ Q₂) X Y u v := by
  refine ⟨hP₁.subgraphUnion hQ₂ hinter, ?_, ?_⟩
  · rw [vertexSet_subgraphUnion, union_inter_distrib_right, hP₁X,
      disjoint_iff_inter_eq_empty.mp hQ₂X, union_empty]
  · rw [vertexSet_subgraphUnion, union_inter_distrib_right,
      disjoint_iff_inter_eq_empty.mp hP₁Y, hQ₂Y, empty_union]

/-- If `Q₁` is a path in `G` from `a` to `z`, `P : Fin r → Graph α β` is a pairwise vertex-disjoint
family of subgraphs of `G`, `z ∈ V(P i₀)`, and `E(Q₁) ⊆ ⋃ i : Fin r, E(P i)`, then `a ∈ V(P i₀)`. -/
theorem left_mem_of_edgeSet_subset_iUnion_disjoint {G Q₁ : Graph α β} {a z : α} {r : ℕ}
    {P : Fin r → Graph α β} {i₀ : Fin r}
    (hQ₁ : IsGraphPathWithEnds G Q₁ a z)
    (hdisjP : Pairwise (fun i₁ i₂ => Disjoint V(P i₁) V(P i₂)))
    (hP_le : ∀ i : Fin r, P i ≤ G)
    (hzi₀ : z ∈ V(P i₀))
    (hE_sub : E(Q₁) ⊆ ⋃ i : Fin r, E(P i)) :
    a ∈ V(P i₀) := by
  rcases hQ₁ with ⟨hQ₁G, W, _, _, hEQ₁⟩
  have hwalk : ∀ {u v : α} (W' : GraphWalk Q₁ u v),
      (∀ e ∈ W'.edges, e ∈ E(Q₁)) → v ∈ V(P i₀) → u ∈ V(P i₀) := by
    intro u v W'
    induction W' with
    | nil _ => exact fun _ hv => hv
    | @cons u w v e huw rest ih =>
      intro hE hv
      have hw : w ∈ V(P i₀) :=
        ih (fun f hf => hE f (List.mem_cons_of_mem _ hf)) hv
      have he_in : e ∈ ⋃ i : Fin r, E(P i) := hE_sub (hE e List.mem_cons_self)
      obtain ⟨i₁, hei₁⟩ := mem_iUnion.mp he_in
      obtain ⟨x₁, y₁, hx₁y₁⟩ := (P i₁).exists_isLink_of_mem_edgeSet hei₁
      have heq := (huw.mono hQ₁G).left_eq_or_eq (hx₁y₁.mono (hP_le i₁))
      have hw_i₁ : w ∈ V(P i₁) := by
        have symm_eq := (huw.symm.mono hQ₁G).left_eq_or_eq (hx₁y₁.mono (hP_le i₁))
        rcases symm_eq with rfl | rfl
        · exact hx₁y₁.left_mem
        · exact hx₁y₁.right_mem
      have hi₁_eq : i₁ = i₀ := by
        by_contra hne
        exact disjoint_left.mp (hdisjP hne) hw_i₁ hw
      subst hi₁_eq
      rcases heq with rfl | rfl
      · exact hx₁y₁.left_mem
      · exact hx₁y₁.right_mem
  exact hwalk W (fun e he => by rw [hEQ₁]; exact he) hzi₀

private theorem replace_with_disjoint_path {G : Graph α β} {X Y : Set α} {r k : ℕ}
    (hrk : r ≤ k)
    {P : Fin r → Graph α β} {x y : Fin r → α}
    (hdisjP : Pairwise (fun i j => Disjoint V(P i) V(P j)))
    (hP : ∀ i, IsFromToPathWithEnds G (P i) X Y (x i) (y i))
    {Q : Fin k → Graph α β} {a b : Fin k → α}
    (hdisjQ : Pairwise (fun i j => Disjoint V(Q i) V(Q j)))
    (hQ : ∀ j, IsFromToPathWithEnds G (Q j) X Y (a j) (b j)) {i₁ : Fin r}
    (hi₁_disj : Disjoint V(P i₁) (⋃ j : Fin k, V(Q j))) :
    ∃ (Q₁ : Fin k → Graph α β) (a₁ b₁ : Fin k → α),
      Pairwise (fun i j => Disjoint V(Q₁ i) V(Q₁ j)) ∧
      (∀ j, IsFromToPathWithEnds G (Q₁ j) X Y (a₁ j) (b₁ j)) ∧
      (r - (range x ∩ range a₁).ncard) +
          ((⋃ j : Fin k, E(Q₁ j)) \ (⋃ i : Fin r, E(P i))).ncard <
        (r - (range x ∩ range a).ncard) +
          ((⋃ j : Fin k, E(Q j)) \ (⋃ i : Fin r, E(P i))).ncard ∧
      ¬ range y ⊆ range b := by
  classical
  have hdiff_fin : ((⋃ j : Fin k, E(Q j)) \ (⋃ i : Fin r, E(P i))).Finite :=
    (finite_iUnion fun j => (hQ j).1.edgeSet_finite).sdiff
  have hx₁_not_a : x i₁ ∉ range a := by
    rintro ⟨j, hj⟩
    exact disjoint_left.mp hi₁_disj (hP i₁).1.left_mem
      (mem_iUnion.mpr ⟨j, hj ▸ (hQ j).1.left_mem⟩)
  have hnot_y_sub_b : ¬ range y ⊆ range b := by
    intro hy_sub_b
    obtain ⟨j, hj⟩ := hy_sub_b (mem_range_self i₁)
    exact disjoint_left.mp hi₁_disj (hP i₁).1.right_mem
      (mem_iUnion.mpr ⟨j, hj ▸ (hQ j).1.right_mem⟩)
  obtain ⟨hx_inj, hy_inj, hx_card, hy_card, _⟩ := redirectsTo_of_disjoint_fromToPaths hdisjP hP
  obtain ⟨ha_inj, hb_inj, ha_card, hb_card, _⟩ := redirectsTo_of_disjoint_fromToPaths hdisjQ hQ
  have hnot_a_sub_x : ¬ range a ⊆ range x := by
    intro ha_sub_x
    have hssub : range a ⊂ range x :=
      ⟨ha_sub_x, fun h => hx₁_not_a (h (mem_range_self i₁))⟩
    have hlt := ncard_lt_ncard hssub (finite_range x)
    omega
  obtain ⟨_, ⟨j₀, rfl⟩, ha_not_x⟩ := not_subset.mp hnot_a_sub_x
  let Q₁ : Fin k → Graph α β := Function.update Q j₀ (P i₁)
  let a₁ : Fin k → α := Function.update a j₀ (x i₁)
  let b₁ : Fin k → α := Function.update b j₀ (y i₁)
  have hdisjQ₁ : Pairwise (fun j₁ j₂ => Disjoint V(Q₁ j₁) V(Q₁ j₂)) := by
    intro j₁ j₂ hne
    by_cases hj₁ : j₁ = j₀ <;> by_cases hj₂ : j₂ = j₀
    · exact (hne (hj₁.trans hj₂.symm)).elim
    · subst hj₁
      simp only [Q₁, Function.update_self, Function.update_of_ne hj₂]
      exact hi₁_disj.mono_right (subset_iUnion (fun j => V(Q j)) j₂)
    · subst hj₂
      simp only [Q₁, Function.update_self, Function.update_of_ne hj₁]
      exact (hi₁_disj.mono_right (subset_iUnion (fun j => V(Q j)) j₁)).symm
    · simp only [Q₁, Function.update_of_ne hj₁, Function.update_of_ne hj₂]
      exact hdisjQ hne
  have hQ₁ : ∀ j : Fin k, IsFromToPathWithEnds G (Q₁ j) X Y (a₁ j) (b₁ j) := by
    intro j
    by_cases hj : j = j₀
    · subst hj; simp [Q₁, a₁, b₁, hP i₁]
    · simp [Q₁, a₁, b₁, hj, hQ j]
  have hrange_inter_eq : range x ∩ range a₁ = insert (x i₁) (range x ∩ range a) := by
    ext w
    simp only [mem_inter_iff, mem_range, mem_insert_iff]
    constructor
    · rintro ⟨⟨i, rfl⟩, ⟨j, hj⟩⟩
      by_cases hj₀ : j = j₀
      · subst hj₀; simp only [a₁, Function.update_self] at hj
        exact Or.inl hj.symm
      · simp only [a₁, Function.update_of_ne hj₀] at hj
        exact Or.inr ⟨⟨i, rfl⟩, ⟨j, hj⟩⟩
    · rintro (rfl | ⟨⟨i, rfl⟩, ⟨j, hj⟩⟩)
      · exact ⟨⟨i₁, rfl⟩, ⟨j₀, by simp [a₁]⟩⟩
      · have hj₀ : j ≠ j₀ := fun h => ha_not_x ⟨i, h ▸ hj.symm⟩
        exact ⟨⟨i, rfl⟩, ⟨j, by simp [a₁, hj₀, hj]⟩⟩
  have hx₁_not_inter : x i₁ ∉ range x ∩ range a := fun h => hx₁_not_a h.2
  have hcard_inter : (range x ∩ range a₁).ncard = (range x ∩ range a).ncard + 1 := by
    rw [hrange_inter_eq]
    exact ncard_insert_of_notMem hx₁_not_inter ((finite_range x).subset inter_subset_left)
  have hcard_lt_r : (range x ∩ range a).ncard < r := by
    have hlt_x : (range x ∩ range a).ncard < (range x).ncard :=
      ncard_lt_ncard
        ⟨inter_subset_left, fun h => hx₁_not_a (h (mem_range_self i₁)).2⟩
        (finite_range x)
    omega
  have hE_sub : (⋃ j : Fin k, E(Q₁ j)) \ (⋃ i : Fin r, E(P i)) ⊆
      (⋃ j : Fin k, E(Q j)) \ (⋃ i : Fin r, E(P i)) := by
    rintro e ⟨he_in, he_not_P⟩
    obtain ⟨j, hej⟩ := mem_iUnion.mp he_in
    by_cases hj : j = j₀
    · subst hj
      simp only [Q₁, Function.update_self] at hej
      exact (he_not_P (mem_iUnion.mpr ⟨i₁, hej⟩)).elim
    · simp only [Q₁, Function.update_of_ne hj] at hej
      exact ⟨mem_iUnion.mpr ⟨j, hej⟩, he_not_P⟩
  have hE_le : ((⋃ j : Fin k, E(Q₁ j)) \ (⋃ i : Fin r, E(P i))).ncard ≤
      ((⋃ j : Fin k, E(Q j)) \ (⋃ i : Fin r, E(P i))).ncard :=
    ncard_le_ncard hE_sub hdiff_fin
  have hlt : (r - (range x ∩ range a₁).ncard) +
      ((⋃ j : Fin k, E(Q₁ j)) \ (⋃ i : Fin r, E(P i))).ncard <
      (r - (range x ∩ range a).ncard) +
        ((⋃ j : Fin k, E(Q j)) \ (⋃ i : Fin r, E(P i))).ncard := by
    omega
  exact ⟨Q₁, a₁, b₁, hdisjQ₁, hQ₁, hlt, hnot_y_sub_b⟩

/-- Given `r ≤ k`, a family `P : Fin r → Graph α β` of `r` mutually disjoint `X → Y` paths with ends
`x i` and `y i` in `G`, and a family `Q : Fin k → Graph α β` of `k` mutually disjoint `X → Y` paths
with ends `a j` and `b j` in `G`, there exists a family `Q' : Fin k → Graph α β` of `k` mutually
disjoint `X → Y` paths with ends `a' j` and `b' j` in `G` such that `range x ⊆ range a'` and
(when every `P i` meets `⋃ j, V(Q j)`, for example, when `range y ⊆ range b`) `b' = b`. -/
theorem exists_replace_starts_disjoint_fromToPaths {G : Graph α β} {X Y : Set α} {r k : ℕ}
    (hrk : r ≤ k)
    {P : Fin r → Graph α β} {x y : Fin r → α}
    (hdisjP : Pairwise (fun i j => Disjoint V(P i) V(P j)))
    (hP : ∀ i : Fin r, IsFromToPathWithEnds G (P i) X Y (x i) (y i))
    {Q : Fin k → Graph α β} {a b : Fin k → α}
    (hdisjQ : Pairwise (fun i j => Disjoint V(Q i) V(Q j)))
    (hQ : ∀ j : Fin k, IsFromToPathWithEnds G (Q j) X Y (a j) (b j)) :
    ∃ (Q' : Fin k → Graph α β) (a' b' : Fin k → α),
      Pairwise (fun i j => Disjoint V(Q' i) V(Q' j)) ∧
      (∀ j : Fin k, IsFromToPathWithEnds G (Q' j) X Y (a' j) (b' j)) ∧
      range x ⊆ range a' ∧
      (range y ⊆ range b → b' = b) := by
  classical
  -- Induct on `m = (r - (range x ∩ range a).ncard) + ((⋃ j : Fin k, E(Q j)) \ (⋃ i : Fin r, E(P
  -- i))).ncard`.
  have hind : ∀ (m : ℕ) (Q : Fin k → Graph α β) (a b : Fin k → α),
      Pairwise (fun i j => Disjoint V(Q i) V(Q j)) →
      (∀ j : Fin k, IsFromToPathWithEnds G (Q j) X Y (a j) (b j)) →
      (r - (range x ∩ range a).ncard) +
        ((⋃ j : Fin k, E(Q j)) \ (⋃ i : Fin r, E(P i))).ncard = m →
      ∃ (Q' : Fin k → Graph α β) (a' b' : Fin k → α),
        Pairwise (fun i j => Disjoint V(Q' i) V(Q' j)) ∧
        (∀ j : Fin k, IsFromToPathWithEnds G (Q' j) X Y (a' j) (b' j)) ∧
        range x ⊆ range a' ∧
        (range y ⊆ range b → b' = b) := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro Q a b hdisjQ hQ hm
      have hEQ_fin : (⋃ j : Fin k, E(Q j)).Finite :=
        finite_iUnion fun j => (hQ j).1.edgeSet_finite
      have hdiff_fin : ((⋃ j : Fin k, E(Q j)) \ (⋃ i : Fin r, E(P i))).Finite :=
        hEQ_fin.sdiff
      by_cases hsub : range x ⊆ range a
      · exact ⟨Q, a, b, hdisjQ, hQ, hsub, fun _ => rfl⟩
      · obtain ⟨_, ⟨i₀, rfl⟩, hx_not_a⟩ := not_subset.mp hsub
        -- Either some `P i₁` is completely disjoint from `⋃ j : Fin k, V(Q j)`, OR every `P i`
        -- meets `⋃ j, V(Q j)`:
        by_cases hfreeP : ∃ i₁ : Fin r, Disjoint V(P i₁) (⋃ j : Fin k, V(Q j))
        · obtain ⟨i₁, hi₁_disj⟩ := hfreeP
          obtain ⟨Q₁, a₁, b₁, hdisjQ₁, hQ₁, hlt, hnot_y_sub_b⟩ :=
            replace_with_disjoint_path hrk hdisjP hP hdisjQ hQ hi₁_disj
          obtain ⟨Q', a', b', hdisjQ', hQ', hsub', _⟩ :=
            ih _ (hm ▸ hlt) Q₁ a₁ b₁ hdisjQ₁ hQ₁ rfl
          exact ⟨Q', a', b', hdisjQ', hQ', hsub', fun hy => (hnot_y_sub_b hy).elim⟩
        · -- Every `P i` meets `⋃ j : Fin k, V(Q j)`.
          -- In particular, `P i₀` meets `⋃ j : Fin k, V(Q j)`.
          have hne_i₀ : (V(P i₀) ∩ (⋃ j : Fin k, V(Q j))).Nonempty := by
            by_contra hemp
            rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hemp
            exact hfreeP ⟨i₀, hemp⟩
          -- Let `z` be the FIRST vertex of `P i₀` in `⋃ j : Fin k, V(Q j)`, and `P₁` the subpath of
          -- `P i₀` from `x i₀` to `z`.
          obtain ⟨z, ⟨hzP, hzUQ⟩, P₁, hP₁_le, hP₁_path, hP₁_inter, hy_z⟩ :=
            (hP i₀).1.exists_first_hit hne_i₀
          obtain ⟨j₀, hzj₀⟩ := mem_iUnion.mp hzUQ
          have hza_ne : z ≠ a j₀ := by
            intro hza
            have hzx : z = x i₀ := (hP i₀).eq_left_of_mem_X hzP (hza ▸ (hQ j₀).left_mem_X)
            exact hx_not_a ⟨j₀, hza.symm.trans hzx⟩
          obtain ⟨Q_pref, Q_suff, hQ_pref_le, hQ_suff_le, hpath_Q_pref, hpath_Q_suff,
            hQ_union, hinter_Q, hdisj_EQ⟩ := (hQ j₀).1.exists_split_at hzj₀
          let R := subgraphUnion G P₁ Q_suff
          have hP₁G : IsGraphPathWithEnds G P₁ (x i₀) z := hP₁_path.mono (hP i₀).1.le
          have hQ_suffG : IsGraphPathWithEnds G Q_suff z (b j₀) := hpath_Q_suff.mono (hQ j₀).1.le
          have hinter_P₁_Qsuff : V(P₁) ∩ V(Q_suff) = {z} := by
            ext w
            simp only [mem_inter_iff, mem_singleton_iff]
            exact ⟨fun ⟨hw₁, hw₂⟩ => by
              have : w ∈ V(P₁) ∩ (⋃ j : Fin k, V(Q j)) :=
                ⟨hw₁, mem_iUnion.mpr ⟨j₀, hQ_suff_le.vertexSet_mono hw₂⟩⟩
              rwa [hP₁_inter, mem_singleton_iff] at this,
              fun h => h ▸ ⟨hP₁_path.right_mem, hpath_Q_suff.left_mem⟩⟩
          have hR_path : IsGraphPathWithEnds G R (x i₀) (b j₀) :=
            hP₁G.subgraphUnion hQ_suffG hinter_P₁_Qsuff
          have hR_X : V(R) ∩ X = {x i₀} := by
            rw [vertexSet_subgraphUnion, union_inter_distrib_right]
            ext w
            simp only [mem_union, mem_inter_iff, mem_singleton_iff]
            constructor
            · rintro (⟨hw₁, hwX⟩ | ⟨hw₂, hwX⟩)
              · exact (hP i₀).eq_left_of_mem_X (hP₁_le.vertexSet_mono hw₁) hwX
              · have hwa : w = a j₀ := (hQ j₀).eq_left_of_mem_X (hQ_suff_le.vertexSet_mono hw₂) hwX
                have : a j₀ ∈ V(Q_pref) ∩ V(Q_suff) := ⟨hpath_Q_pref.left_mem, hwa ▸ hw₂⟩
                rw [hinter_Q, mem_singleton_iff] at this
                exact (hza_ne this.symm).elim
            · rintro rfl
              exact Or.inl ⟨hP₁_path.left_mem, (hP i₀).left_mem_X⟩
          have hR_Y : V(R) ∩ Y = {b j₀} := by
            rw [vertexSet_subgraphUnion, union_inter_distrib_right]
            ext w
            simp only [mem_union, mem_inter_iff, mem_singleton_iff]
            constructor
            · rintro (⟨hw₁, hwY⟩ | ⟨hw₂, hwY⟩)
              · have hwy : w = y i₀ := (hP i₀).eq_right_of_mem_Y (hP₁_le.vertexSet_mono hw₁) hwY
                have hzy : z = y i₀ := hy_z (hwy ▸ hw₁)
                have hzb : z = b j₀ := (hQ j₀).eq_right_of_mem_Y hzj₀ (hzy ▸ (hP i₀).right_mem_Y)
                exact hwy.trans (hzy.symm.trans hzb)
              · exact (hQ j₀).eq_right_of_mem_Y (hQ_suff_le.vertexSet_mono hw₂) hwY
            · rintro rfl
              exact Or.inr ⟨hpath_Q_suff.right_mem, (hQ j₀).right_mem_Y⟩
          have hR_fromTo : IsFromToPathWithEnds G R X Y (x i₀) (b j₀) := ⟨hR_path, hR_X, hR_Y⟩
          let Q₁ : Fin k → Graph α β := Function.update Q j₀ R
          let a₁ : Fin k → α := Function.update a j₀ (x i₀)
          have hdisj_R_other : ∀ j : Fin k, j ≠ j₀ → Disjoint V(R) V(Q j) := by
            intro j hj
            rw [vertexSet_subgraphUnion, disjoint_union_left]
            refine ⟨disjoint_left.mpr fun w hw₁ hwQ => ?_,
              (hdisjQ (Ne.symm hj)).mono_left hQ_suff_le.vertexSet_mono⟩
            have hw_inter : w ∈ V(P₁) ∩ (⋃ j' : Fin k, V(Q j')) :=
              ⟨hw₁, mem_iUnion.mpr ⟨j, hwQ⟩⟩
            rw [hP₁_inter, mem_singleton_iff] at hw_inter
            subst hw_inter
            exact disjoint_left.mp (hdisjQ (Ne.symm hj)) hzj₀ hwQ
          have hdisjQ₁ : Pairwise (fun j₁ j₂ => Disjoint V(Q₁ j₁) V(Q₁ j₂)) := by
            intro j₁ j₂ hne
            by_cases hj₁ : j₁ = j₀ <;> by_cases hj₂ : j₂ = j₀
            · exact (hne (hj₁.trans hj₂.symm)).elim
            · subst hj₁
              simp only [Q₁, Function.update_self, Function.update_of_ne hj₂]
              exact hdisj_R_other j₂ hj₂
            · subst hj₂
              simp only [Q₁, Function.update_self, Function.update_of_ne hj₁]
              exact (hdisj_R_other j₁ hj₁).symm
            · simp only [Q₁, Function.update_of_ne hj₁, Function.update_of_ne hj₂]
              exact hdisjQ hne
          have hQ₁ : ∀ j : Fin k, IsFromToPathWithEnds G (Q₁ j) X Y (a₁ j) (b j) := by
            intro j
            by_cases hj : j = j₀
            · subst hj; simp [Q₁, a₁, hR_fromTo]
            · simp [Q₁, a₁, hj, hQ j]
          -- Show `(range x ∩ range a).ncard ≤ (range x ∩ range a₁).ncard`.
          have hsub_insert : insert (x i₀) ((range x ∩ range a) \ {a j₀}) ⊆ range x ∩ range a₁ := by
            rintro w (rfl | ⟨⟨⟨i, rfl⟩, ⟨j, hj⟩⟩, hne_aj₀⟩)
            · exact ⟨⟨i₀, rfl⟩, ⟨j₀, by simp [a₁]⟩⟩
            · have hj_ne : j ≠ j₀ := fun h => hne_aj₀ (by rw [mem_singleton_iff, ← hj, h])
              exact ⟨⟨i, rfl⟩, ⟨j, by simp [a₁, hj_ne, hj]⟩⟩
          have hx₀_not_diff : x i₀ ∉ (range x ∩ range a) \ {a j₀} :=
            fun h => hx_not_a h.1.2
          have hfin_inter : (range x ∩ range a).Finite := (finite_range x).subset inter_subset_left
          have hfin_inter₁ : (range x ∩ range a₁).Finite := (finite_range x).subset
            inter_subset_left
          have hcard_inter_le : (range x ∩ range a).ncard ≤ (range x ∩ range a₁).ncard := by
            have h1 : (insert (x i₀) ((range x ∩ range a) \ {a j₀})).ncard ≤
                (range x ∩ range a₁).ncard :=
              ncard_le_ncard hsub_insert hfin_inter₁
            rw [ncard_insert_of_notMem hx₀_not_diff hfin_inter.sdiff] at h1
            have h2 : (range x ∩ range a).ncard ≤
                (insert (a j₀) ((range x ∩ range a) \ {a j₀})).ncard :=
              ncard_le_ncard (subset_insert_sdiff_singleton (a j₀) _)
                (hfin_inter.sdiff.insert (a j₀))
            have h3 := ncard_insert_le (a j₀) ((range x ∩ range a) \ {a j₀})
            omega
          -- Show `((⋃ j, E(Q₁ j)) \ (⋃ i, E(P i))).ncard < ((⋃ j, E(Q j)) \ (⋃ i, E(P i))).ncard`.
          have hE_sub : (⋃ j : Fin k, E(Q₁ j)) \ (⋃ i : Fin r, E(P i)) ⊆
              (⋃ j : Fin k, E(Q j)) \ (⋃ i : Fin r, E(P i)) := by
            rintro e ⟨he_in, he_not_P⟩
            obtain ⟨j, hej⟩ := mem_iUnion.mp he_in
            by_cases hj : j = j₀
            · subst hj
              simp only [Q₁, Function.update_self, R] at hej
              rw [edgeSet_subgraphUnion hP₁G.le hQ_suffG.le, mem_union] at hej
              rcases hej with heP₁ | heQsuff
              · exact (he_not_P (mem_iUnion.mpr ⟨i₀, hP₁_le.edgeSet_mono heP₁⟩)).elim
              · exact ⟨mem_iUnion.mpr ⟨j, hQ_suff_le.edgeSet_mono heQsuff⟩, he_not_P⟩
            · simp only [Q₁, Function.update_of_ne hj] at hej
              exact ⟨mem_iUnion.mpr ⟨j, hej⟩, he_not_P⟩
          have hnot_Qpref_sub : ¬ E(Q_pref) ⊆ ⋃ i : Fin r, E(P i) := by
            intro hsub_pref
            have ha_in_Pi₀ : a j₀ ∈ V(P i₀) :=
              left_mem_of_edgeSet_subset_iUnion_disjoint
                (hpath_Q_pref.mono (hQ j₀).1.le) hdisjP (fun i => (hP i).1.le) hzP hsub_pref
            have ha_eq_xi₀ : a j₀ = x i₀ :=
              (hP i₀).eq_left_of_mem_X ha_in_Pi₀ (hQ j₀).left_mem_X
            exact hx_not_a ⟨j₀, ha_eq_xi₀⟩
          obtain ⟨e₀, he₀_pref, he₀_not_P⟩ := not_subset.mp hnot_Qpref_sub
          have he₀_in_old : e₀ ∈ (⋃ j : Fin k, E(Q j)) \ (⋃ i : Fin r, E(P i)) :=
            ⟨mem_iUnion.mpr ⟨j₀, hQ_pref_le.edgeSet_mono he₀_pref⟩, he₀_not_P⟩
          have he₀_not_new : e₀ ∉ (⋃ j : Fin k, E(Q₁ j)) \ (⋃ i : Fin r, E(P i)) := by
            rintro ⟨he₀_Q₁, _⟩
            obtain ⟨j, he₀_j⟩ := mem_iUnion.mp he₀_Q₁
            by_cases hj : j = j₀
            · subst hj
              simp only [Q₁, Function.update_self, R] at he₀_j
              rw [edgeSet_subgraphUnion hP₁G.le hQ_suffG.le, mem_union] at he₀_j
              rcases he₀_j with he₀_P₁ | he₀_Qsuff
              · exact he₀_not_P (mem_iUnion.mpr ⟨i₀, hP₁_le.edgeSet_mono he₀_P₁⟩)
              · exact disjoint_left.mp hdisj_EQ he₀_pref he₀_Qsuff
            · simp only [Q₁, Function.update_of_ne hj] at he₀_j
              obtain ⟨u₀, v₀, huv₀⟩ := (Q j₀).exists_isLink_of_mem_edgeSet
                (hQ_pref_le.edgeSet_mono he₀_pref)
              obtain ⟨u₁, v₁, huv₁⟩ := (Q j).exists_isLink_of_mem_edgeSet he₀_j
              have heq := (huv₀.mono (hQ j₀).1.le).left_eq_or_eq (huv₁.mono (hQ j).1.le)
              have hu₀_in_j : u₀ ∈ V(Q j) := by
                rcases heq with rfl | rfl
                · exact huv₁.left_mem
                · exact huv₁.right_mem
              exact disjoint_left.mp (hdisjQ (Ne.symm hj)) huv₀.left_mem hu₀_in_j
          have hE_lt : ((⋃ j : Fin k, E(Q₁ j)) \ (⋃ i : Fin r, E(P i))).ncard <
              ((⋃ j : Fin k, E(Q j)) \ (⋃ i : Fin r, E(P i))).ncard :=
            ncard_lt_ncard ⟨hE_sub, fun h => he₀_not_new (h he₀_in_old)⟩ hdiff_fin
          have hlt : (r - (range x ∩ range a₁).ncard) +
              ((⋃ j : Fin k, E(Q₁ j)) \ (⋃ i : Fin r, E(P i))).ncard < m := by
            omega
          obtain ⟨Q', a', b', hdisjQ', hQ', hsub', hb'⟩ :=
            ih _ hlt Q₁ a₁ b hdisjQ₁ hQ₁ rfl
          exact ⟨Q', a', b', hdisjQ', hQ', hsub', hb'⟩
  exact hind _ Q a b hdisjQ hQ rfl

/-- Given a path `P` from `x` to `y` that is an `X → Y` path in `G`, the same subgraph `P` viewed
in reverse is a `Y → X` path in `G` from `y` to `x`. -/
theorem IsFromToPathWithEnds.symm {G P : Graph α β} {X Y : Set α} {x y : α}
    (h : IsFromToPathWithEnds G P X Y x y) :
    IsFromToPathWithEnds G P Y X y x :=
  ⟨h.1.symm, h.2.2, h.2.1⟩

/-- **Graph Minors IX, (2.2)** (page 44):
"Let $G$ be a graph and let $X, Y \subseteq V(G)$. Let $k \ge 0$ be an integer such that there are
$k$ mutually disjoint $X \to Y$ paths. Let $X' \subseteq X$, $Y' \subseteq Y$ be such that
$|X'| = |Y'| \le k$ and such that $X' \Rightarrow Y'$ with respect to $X, Y$. Then there exist
$X'' \subseteq X$ and $Y'' \subseteq Y$ such that $X' \subseteq X''$, $Y' \subseteq Y''$,
$|X''| = |Y''| = k$ and $X'' \Rightarrow Y''$ with respect to $X, Y$." -/
theorem theorem_2_2_proof {G : Graph α β} [Finite V(G)] {X Y X' Y' : Set α} {k : ℕ}
    (hX : X ⊆ V(G)) (hY : Y ⊆ V(G))
    (hk : ∃ Q : Fin k → Graph α β, Pairwise (fun i j => Disjoint V(Q i) V(Q j)) ∧
      ∀ i : Fin k, IsFromToPath G (Q i) X Y)
    (hX' : X' ⊆ X) (hY' : Y' ⊆ Y) (_hcard : X'.ncard = Y'.ncard) (hle : X'.ncard ≤ k)
    (hred : RedirectsTo G X Y X' Y') :
    ∃ X'' Y'' : Set α, X'' ⊆ X ∧ Y'' ⊆ Y ∧ X' ⊆ X'' ∧ Y' ⊆ Y'' ∧
      X''.ncard = k ∧ Y''.ncard = k ∧ RedirectsTo G X Y X'' Y'' := by
  classical
  have hVG_fin : V(G).Finite := toFinite V(G)
  have hX'_fin : X'.Finite := hVG_fin.subset (hX'.trans hX)
  have hY'_fin : Y'.Finite := hVG_fin.subset (hY'.trans hY)
  obtain ⟨P, x, y, hdisjP, hP, hx_eq, hy_eq⟩ :=
    exists_indexed_of_redirectsTo hX'_fin hY'_fin hred rfl
  obtain ⟨Q, hdisjQ, hQ_ex⟩ := hk
  choose a b hQ using hQ_ex
  -- Pass 1: replace initial vertices so that `X' = range x ⊆ range a₁`.
  obtain ⟨Q₁, a₁, b₁, hdisjQ₁, hQ₁, hsub_x, _⟩ :=
    exists_replace_starts_disjoint_fromToPaths hle hdisjP hP hdisjQ hQ
  -- Pass 2: reverse `X` and `Y` and replace initial vertices of the reversed paths so that
  -- `Y' = range y ⊆ range b₂`, while keeping `a₂ = a₁` (since `range x ⊆ range a₁`).
  have hP_symm : ∀ i : Fin X'.ncard, IsFromToPathWithEnds G (P i) Y X (y i) (x i) :=
    fun i => (hP i).symm
  have hQ₁_symm : ∀ j : Fin k, IsFromToPathWithEnds G (Q₁ j) Y X (b₁ j) (a₁ j) :=
    fun j => (hQ₁ j).symm
  obtain ⟨Q₂, b₂, a₂, hdisjQ₂, hQ₂_symm, hsub_y, ha₂_eq⟩ :=
    exists_replace_starts_disjoint_fromToPaths hle hdisjP hP_symm hdisjQ₁ hQ₁_symm
  have hQ₂ : ∀ j : Fin k, IsFromToPathWithEnds G (Q₂ j) X Y (a₂ j) (b₂ j) :=
    fun j => (hQ₂_symm j).symm
  obtain ⟨_, _, ha₂_card, hb₂_card, hred₂⟩ :=
    redirectsTo_of_disjoint_fromToPaths hdisjQ₂ hQ₂
  refine ⟨range a₂, range b₂, hred₂.1, hred₂.2.1, ?_, ?_, ha₂_card, hb₂_card, hred₂⟩
  · rw [← hx_eq, ha₂_eq hsub_x]; exact hsub_x
  · rwa [← hy_eq]

end GraphMinor.GM09
