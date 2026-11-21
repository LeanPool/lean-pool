/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.NestedDissection.Sparse
public import Mathlib.Data.Finset.Sort

/-!
# Separator trees and the nested dissection order

A *separator tree* (`SepTree`) of a graph `G` recursively splits a vertex set `W` into a
separator `S` and two parts `A`, `B` with no edge of `G` between `A` and `B`; the recursion stops
at leaves.  The *nested dissection order* numbers, recursively, the vertices of `A` first, then
those of `B`, and the separator `S` last [A. George, *Nested dissection of a regular finite
element mesh*, SIAM J. Numer. Anal. 10 (1973), 345–363; R. J. Lipton, D. J. Rose,
R. E. Tarjan, *Generalized nested dissection*, SIAM J. Numer. Anal. 16 (1979), 346–358].

The basic structural fact is that elimination never creates fill between the vertex set of a
subtree and the rest of the graph except through its *boundary* `bdry G W` (the vertices outside
`W` adjacent to `W`): for a vertex `u` of the separator (or leaf set) `own t` of a subtree `t`,
every later neighbour of `u` in the filled graph lies in `own t` or in the boundary of `t`
(`laterNbrs_fill_subset`).  Summing over the tree bounds the fill and the cost of elimination by
sums over the nodes (`sum_laterNbrs_le_sumNodes`).

## Main definitions

`SepTree`, `own`, `verts`, `IsDissection`, `bdry` and `order` are defined in
`NestedDissection/Spec.lean`; `ndPerm`, `sumNodes` and `Consistent` here.

* `NestedDissection.SepTree V`, with `own` (separator, or the whole set at a leaf), `verts`
  (all vertices of the subtree) and `sumNodes f` (the sum of `f` over all subtrees).
* `NestedDissection.SepTree.IsDissection G t`: `t` is a separator tree of `G`.
* `NestedDissection.SepTree.Consistent r t`: in the order `r`, the vertices of the parts of each
  node precede its separator.
* `NestedDissection.bdry G W`: the boundary of a vertex set.
* `NestedDissection.SepTree.order t`: the nested dissection order as a list.
* `NestedDissection.SepTree.ndPerm`: the corresponding permutation of `Fin n`.
-/

namespace NestedDissection

@[expose] public section

universe u v w

section Bdry

variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

variable {G}

theorem mem_bdry {W : Finset V} {y : V} : y ∈ bdry G W ↔ y ∉ W ∧ ∃ x ∈ W, G.Adj x y := by
  simp [bdry]

@[simp] theorem bdry_univ : bdry G Finset.univ = ∅ := by
  ext y; simp [mem_bdry]

/-- A low walk leaving `W` must pass through the boundary of `W`: if all boundary vertices
have rank `≥ k`, a walk from `W` with interior of rank `< k` ends in `W` or on its boundary. -/
theorem LowWalk.mem_or_mem_bdry {r : V → ℕ} {W : Finset V} {k : ℕ} {x w : V} (hx : x ∈ W)
    (h : LowWalk G r k x w) (hb : ∀ y ∈ bdry G W, k ≤ r y) : w ∈ W ∨ w ∈ bdry G W := by
  induction h with
  | @adj u w h =>
    by_cases hw : w ∈ W
    · exact .inl hw
    · exact .inr (mem_bdry.mpr ⟨hw, u, hx, h⟩)
  | @cons u y w h hy _ ih =>
    apply ih
    by_contra hy'
    exact absurd (hb y (mem_bdry.mpr ⟨hy', u, hx, h⟩)) (by omega)

end Bdry

namespace SepTree

variable {V : Type u}

/-- The sum of `f` over all subtrees (nodes) of a tree. -/
def sumNodes {R : Type w} [AddCommMonoid R] (f : SepTree V → R) : SepTree V → R
  | leaf s => f (leaf s)
  | node s a b => f (node s a b) + sumNodes f a + sumNodes f b

theorem sumNodes_mono {R : Type w} [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
    {f g : SepTree V → R} (h : ∀ s, f s ≤ g s) (t : SepTree V) :
    sumNodes f t ≤ sumNodes g t := by
  induction t with
  | leaf s => exact h _
  | node s a b iha ihb => exact add_le_add (add_le_add (h _) iha) ihb

variable [DecidableEq V]

theorem own_subset_verts (t : SepTree V) : t.own ⊆ t.verts := by
  cases t with
  | leaf s => exact subset_rfl
  | node s a b => exact Finset.subset_union_left.trans Finset.subset_union_left

/-- The order `r` is consistent with `t`: at every node, all vertices of the two parts come
before all vertices of the separator. -/
def Consistent (r : V → ℕ) : SepTree V → Prop
  | leaf _ => True
  | node s a b =>
      (∀ x ∈ a.verts ∪ b.verts, ∀ y ∈ s, r x < r y) ∧ Consistent r a ∧ Consistent r b

theorem card_verts_node_le {G : SimpleGraph V} {s : Finset V} {a b : SepTree V}
    (h : IsDissection G (node s a b)) :
    a.verts.card + b.verts.card ≤ (node s a b).verts.card := by
  rw [← Finset.card_union_of_disjoint h.2.2.1]
  exact Finset.card_le_card fun x hx => by
    simp only [verts, Finset.mem_union] at hx ⊢; tauto

section Fill

variable [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℕ}

theorem bdry_left_subset {s : Finset V} {a b : SepTree V} (h : IsDissection G (node s a b)) :
    bdry G a.verts ⊆ bdry G (node s a b).verts ∪ s := by
  intro y hy
  obtain ⟨hya, x, hx, hxy⟩ := mem_bdry.mp hy
  rw [Finset.mem_union]
  by_cases hy' : y ∈ (node s a b).verts
  · simp only [verts, Finset.mem_union] at hy'
    rcases hy' with (hs | ha) | hb
    · exact .inr hs
    · exact absurd ha hya
    · exact absurd hxy (h.2.2.2.1 x hx y hb)
  · exact .inl (mem_bdry.mpr ⟨hy', x, by simp [verts, hx], hxy⟩)

theorem bdry_right_subset {s : Finset V} {a b : SepTree V} (h : IsDissection G (node s a b)) :
    bdry G b.verts ⊆ bdry G (node s a b).verts ∪ s := by
  intro y hy
  obtain ⟨hyb, x, hx, hxy⟩ := mem_bdry.mp hy
  rw [Finset.mem_union]
  by_cases hy' : y ∈ (node s a b).verts
  · simp only [verts, Finset.mem_union] at hy'
    rcases hy' with (hs | ha) | hb
    · exact .inr hs
    · exact absurd hxy.symm (h.2.2.2.1 y ha x hx)
    · exact absurd hb hyb
  · exact .inl (mem_bdry.mpr ⟨hy', x, by simp [verts, hx], hxy⟩)

/-- The boundary of a subtree comes after it in the order `r`. -/
def BdryLater (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℕ) (t : SepTree V) : Prop :=
  ∀ x ∈ t.verts, ∀ y ∈ bdry G t.verts, r x < r y

theorem BdryLater.left {s : Finset V} {a b : SepTree V} (hd : IsDissection G (node s a b))
    (hc : Consistent r (node s a b)) (hb : BdryLater G r (node s a b)) : BdryLater G r a := by
  intro x hx y hy
  rcases Finset.mem_union.mp (bdry_left_subset hd hy) with hy | hy
  · exact hb x (by simp [verts, hx]) y hy
  · exact hc.1 x (Finset.mem_union_left _ hx) y hy

theorem BdryLater.right {s : Finset V} {a b : SepTree V} (hd : IsDissection G (node s a b))
    (hc : Consistent r (node s a b)) (hb : BdryLater G r (node s a b)) : BdryLater G r b := by
  intro x hx y hy
  rcases Finset.mem_union.mp (bdry_right_subset hd hy) with hy | hy
  · exact hb x (by simp [verts, hx]) y hy
  · exact hc.1 x (Finset.mem_union_right _ hx) y hy

theorem bdryLater_of_verts_eq_univ {t : SepTree V} (h : t.verts = Finset.univ) :
    BdryLater G r t := by
  intro x _ y hy
  rw [h, bdry_univ] at hy
  exact absurd hy (Finset.notMem_empty y)

variable [DecidableRel (fill G r).Adj]

/-- **Fill stays inside a subtree and its boundary**: the later neighbours in the filled graph
of a vertex `u` numbered at the root of a subtree `t` lie in `own t` or in the boundary of `t`. -/
theorem laterNbrs_fill_subset {t : SepTree V} (hc : Consistent r t) (hb : BdryLater G r t)
    {u : V} (hu : u ∈ t.own) :
    laterNbrs r (fill G r) u ⊆ t.own.erase u ∪ bdry G t.verts := by
  intro w hw
  obtain ⟨⟨hne, hwalk⟩, hlt⟩ := mem_laterNbrs.mp hw
  rw [min_eq_left hlt.le] at hwalk
  have hu' := t.own_subset_verts hu
  rcases hwalk.mem_or_mem_bdry hu' fun y hy => (hb u hu' y hy).le with hw' | hw'
  · refine Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne.symm, ?_⟩)
    cases t with
    | leaf s => exact hw'
    | node s a b =>
      simp only [verts, Finset.mem_union] at hw'
      rcases hw' with (hs | ha) | hb'
      · exact hs
      · exact absurd (hc.1 w (Finset.mem_union_left _ ha) u hu) (by omega)
      · exact absurd (hc.1 w (Finset.mem_union_right _ hb') u hu) (by omega)
  · exact Finset.mem_union_right _ hw'

theorem card_laterNbrs_fill_add_one_le {t : SepTree V} (hc : Consistent r t)
    (hb : BdryLater G r t) {u : V} (hu : u ∈ t.own) :
    (laterNbrs r (fill G r) u).card + 1 ≤ t.own.card + (bdry G t.verts).card := by
  have h1 := Finset.card_le_card (laterNbrs_fill_subset hc hb hu)
  have h2 := Finset.card_union_le (t.own.erase u) (bdry G t.verts)
  have h3 := Finset.card_erase_of_mem hu
  have h4 := Finset.card_pos.mpr ⟨u, hu⟩
  omega

/-- **Fill and work bounded by a sum over the separator tree.**  For every monotone `φ`,
`∑ u, φ (deg⁺ u + 1) ≤ ∑ over nodes t, |own t| * φ (|own t| + |bdry t|)`, where `deg⁺ u` is
the number of later neighbours of `u` in the filled graph. -/
theorem sum_laterNbrs_le_sumNodes (φ : ℕ → ℕ) (hφ : Monotone φ) (t : SepTree V)
    (hd : IsDissection G t) (hc : Consistent r t) (hb : BdryLater G r t) :
    ∑ u ∈ t.verts, φ ((laterNbrs r (fill G r) u).card + 1) ≤
      t.sumNodes fun s => s.own.card * φ (s.own.card + (bdry G s.verts).card) := by
  have hown : ∀ t : SepTree V, Consistent r t → BdryLater G r t →
      ∑ u ∈ t.own, φ ((laterNbrs r (fill G r) u).card + 1) ≤
        t.own.card * φ (t.own.card + (bdry G t.verts).card) := by
    intro t hc hb
    rw [← smul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ fun u hu =>
      hφ (card_laterNbrs_fill_add_one_le hc hb hu)
  induction t with
  | leaf s => exact hown (leaf s) hc hb
  | node s a b iha ihb =>
    have hsa : Disjoint s a.verts := hd.1
    have hsab : Disjoint (s ∪ a.verts) b.verts :=
      Finset.disjoint_union_left.mpr ⟨hd.2.1, hd.2.2.1⟩
    simp only [verts] at *
    rw [Finset.sum_union hsab, Finset.sum_union hsa, sumNodes]
    exact add_le_add (add_le_add (hown (node s a b) hc hb)
      (iha hd.2.2.2.2.1 hc.2.1 (hb.left hd hc)))
      (ihb hd.2.2.2.2.2 hc.2.2 (hb.right hd hc))

end Fill

/-! ### The nested dissection order -/

section Order

variable [LinearOrder V]

theorem mem_order {t : SepTree V} {x : V} : x ∈ t.order ↔ x ∈ t.verts := by
  induction t with
  | leaf s => simp [order, verts]
  | node s a b iha ihb => simp [order, verts, iha, ihb]; tauto

theorem nodup_order {G : SimpleGraph V} {t : SepTree V} (hd : IsDissection G t) :
    t.order.Nodup := by
  induction t with
  | leaf s => exact Finset.sort_nodup _ _
  | node s a b iha ihb =>
    simp only [order]
    refine List.Nodup.append (List.Nodup.append (iha hd.2.2.2.2.1) (ihb hd.2.2.2.2.2) ?_)
      (Finset.sort_nodup _ _) ?_
    · intro x hxa hxb
      rw [mem_order] at hxa hxb
      exact Finset.disjoint_left.mp hd.2.2.1 hxa hxb
    · intro x hx hxs
      rw [List.mem_append, mem_order, mem_order] at hx
      rw [Finset.mem_sort] at hxs
      rcases hx with hx | hx
      · exact Finset.disjoint_left.mp hd.1 hxs hx
      · exact Finset.disjoint_left.mp hd.2.1 hxs hx

omit [LinearOrder V] in
theorem idxOf_lt_idxOf {X Y : List V} (hnd : (X ++ Y).Nodup) {x y : V} (hx : x ∈ X)
    (hy : y ∈ Y) : (X ++ Y).idxOf x < (X ++ Y).idxOf y := by
  have hyX : y ∉ X := fun hyX => List.disjoint_of_nodup_append hnd hyX hy
  rw [List.idxOf_append_of_mem hx, List.idxOf_append_of_notMem hyX]
  have := List.idxOf_lt_length_of_mem hx
  omega

/-- Positions in any list containing `order t` as a contiguous block are consistent with `t`. -/
theorem consistent_idxOf {G : SimpleGraph V} (t : SepTree V) (hd : IsDissection G t)
    (P S : List V) (hnd : (P ++ t.order ++ S).Nodup) :
    Consistent (fun x => (P ++ t.order ++ S).idxOf x) t := by
  induction t generalizing P S with
  | leaf s => trivial
  | node s a b iha ihb =>
    refine ⟨fun x hx y hy => ?_, ?_, ?_⟩
    · have e : P ++ (node s a b).order ++ S =
          (P ++ a.order ++ b.order) ++ (s.sort (· ≤ ·) ++ S) := by
        simp [order]
      rw [e] at hnd ⊢
      refine idxOf_lt_idxOf hnd ?_ (List.mem_append_left _ ((Finset.mem_sort _).mpr hy))
      rw [Finset.mem_union] at hx
      rcases hx with hx | hx
      · exact List.mem_append_left _ (List.mem_append_right _ (mem_order.mpr hx))
      · exact List.mem_append_right _ (mem_order.mpr hx)
    · have e : P ++ (node s a b).order ++ S =
          P ++ a.order ++ (b.order ++ s.sort (· ≤ ·) ++ S) := by
        simp [order]
      rw [e] at hnd ⊢
      exact iha hd.2.2.2.2.1 _ _ hnd
    · have e : P ++ (node s a b).order ++ S =
          (P ++ a.order) ++ b.order ++ (s.sort (· ≤ ·) ++ S) := by
        simp [order]
      rw [e] at hnd ⊢
      exact ihb hd.2.2.2.2.2 _ _ hnd

theorem consistent_order {G : SimpleGraph V} (t : SepTree V) (hd : IsDissection G t) :
    Consistent (fun x => t.order.idxOf x) t := by
  simpa using consistent_idxOf t hd [] [] (by simpa using nodup_order hd)

end Order

/-- The nested dissection order of a separator tree covering `Fin n`, as a permutation:
`ndPerm t hd hv k` is the vertex eliminated at step `k`. -/
def ndPerm {n : ℕ} {G : SimpleGraph (Fin n)} (t : SepTree (Fin n)) (hd : IsDissection G t)
    (hv : t.verts = Finset.univ) : Equiv.Perm (Fin n) :=
  have hlen : t.order.length = n := by
    rw [← List.toFinset_card_of_nodup (nodup_order hd)]
    have : t.order.toFinset = Finset.univ := by
      ext x; simp [mem_order, hv]
    rw [this, Finset.card_univ, Fintype.card_fin]
  have hmem : ∀ x, x ∈ t.order := fun x => mem_order.mpr (hv ▸ Finset.mem_univ x)
  { toFun := fun k => t.order[k.val]'(lt_of_lt_of_eq k.2 hlen.symm)
    invFun := fun x => ⟨t.order.idxOf x, lt_of_lt_of_eq (List.idxOf_lt_length_of_mem (hmem x)) hlen⟩
    left_inv := fun k => Fin.ext ((nodup_order hd).idxOf_getElem _ _)
    right_inv := fun x => List.getElem_idxOf _ }

theorem ndPerm_symm_apply {n : ℕ} {G : SimpleGraph (Fin n)} (t : SepTree (Fin n))
    (hd : IsDissection G t) (hv : t.verts = Finset.univ) (x : Fin n) :
    ((ndPerm t hd hv).symm x : ℕ) = t.order.idxOf x := rfl

end SepTree

end

end NestedDissection
