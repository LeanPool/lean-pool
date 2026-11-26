/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas

/-!
# Counting for the graph `δ(I)`

This is the counting behind Claims (3) and (4) of the proof of (11.1) of Graph Minors XVII, pages
190 and 191. We do not draw the graph `H`. It is enough to
know the arcs between consecutive nodes on the boundaries of the regions and cuffs. Each arc has two
ends and lies on one face and on one cell. Mark some arcs. We call
`(f, n)` a change if an odd number of marked arcs of the face `f` end at `n`. Every face has an even
number of changes (`even_face`). If a cell has an even
number of arcs at each node, and arcs of a cell are all marked or all unmarked, then every node has
an even number of changes (`even_node`). So `δ(I)` has even valency.
If the faces with changes have pairs of change nodes that are all different, within three nodes,
then these faces form a triangle (`exists_triangle`). Claim (4) is `triangle_of_system`: under the
facts of `ArcSystem` every class of cells with at most three shared nodes, and with neither class on
all nodes, has such a triangle, by induction on the number of faces with changes. Two faces with the
same pair give a cell whose class we flip.
-/

@[expose] public section

namespace GraphMinor.GM17

open Finset

variable {Arc Face Cell Node : Type*}

open Classical in
/-- The number of marked arcs of a face at a node. -/
noncomputable def markCount (A : Finset Arc) (fc : Arc → Face) (ends : Arc → Finset Node) (m : Arc
  → Prop) (f : Face) (n : Node) : ℕ :=
  #{a ∈ A | fc a = f ∧ n ∈ ends a ∧ m a}

theorem even_face (A : Finset Arc) (fc : Arc → Face) (ends : Arc → Finset Node) (m : Arc → Prop)
  (f : Face) (Nd : Finset Node)
    (hends : ∀ a ∈ A, fc a = f → ends a ⊆ Nd ∧ #(ends a) = 2) :
    Even #{n ∈ Nd | Odd (markCount A fc ends m f n)} := by
  classical
  rw [← Finset.even_sum_iff_even_card_odd]
  have h1 : ∀ n ∈ Nd, markCount A fc ends m f n = ∑ a ∈ A with fc a = f
    ∧ m a, if n ∈ ends a then 1 else 0 := fun n _ => by
    rw [markCount, card_filter, sum_filter]
    refine sum_congr rfl fun a _ => ?_
    by_cases h : fc a = f <;> by_cases h' : m a <;> by_cases h'' : n ∈ ends a <;> simp [h, h', h'']
  rw [sum_congr rfl h1, sum_comm]
  have h2 : ∀ a ∈ ({a ∈ A | fc a = f ∧ m a} : Finset Arc), (∑ n ∈ Nd, if n ∈ ends a then 1 else 0)
    = 2 := fun a ha => by
    obtain ⟨ha1, ha2⟩ := mem_filter.mp ha
    obtain ⟨h3, h4⟩ := hends a ha1 ha2.1
    rw [← card_filter, ← h4]
    congr 1
    ext n
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨h3 h, h⟩⟩
  rw [sum_congr rfl h2, sum_const, nsmul_eq_mul, Nat.cast_id]
  exact even_two.mul_left _

open Classical in
theorem even_node (A : Finset Arc) (fc : Arc → Face) (ce : Arc → Cell) (ends : Arc → Finset Node)
  (m : Cell → Prop) (Fc : Finset Face) (Cl : Finset Cell) (n : Node)
    (hfc : ∀ a ∈ A, fc a ∈ Fc) (hce : ∀ a ∈ A, ce a ∈ Cl) (hcell : ∀ c ∈ Cl, Even #{a ∈ A | ce a
      = c ∧ n ∈ ends a}) :
    Even #{f ∈ Fc | Odd (markCount A fc ends (fun a => m (ce a)) f n)} := by
  classical
  rw [← Finset.even_sum_iff_even_card_odd]
  have h1 : ∑ f ∈ Fc, markCount A fc ends (fun a => m (ce a)) f n = #{a ∈ A | n ∈ ends a ∧ m
    (ce a)} := by
    rw [card_eq_sum_card_fiberwise (f := fc) (t := Fc) (fun a ha => hfc a (mem_filter.mp ha).1)]
    refine sum_congr rfl fun f _ => ?_
    rw [markCount, filter_filter]
    congr 1
    ext a
    simp only [mem_filter]
    tauto
  rw [h1, card_eq_sum_card_fiberwise (f := ce) (t := Cl) (fun a ha => hce a (mem_filter.mp ha).1)]
  refine even_sum _ fun c hc => ?_
  by_cases hm : m c
  · have h2 : ({a ∈ ({a ∈ A | n ∈ ends a ∧ m (ce a)} : Finset Arc) | ce a = c} : Finset Arc)
    = {a ∈ A | ce a = c ∧ n ∈ ends a} := by
      ext a
      simp only [mem_filter]
      constructor
      · rintro ⟨⟨h1, h2, -⟩, h3⟩
        exact ⟨h1, h3, h2⟩
      · rintro ⟨h1, h3, h2⟩
        exact ⟨⟨h1, h2, h3 ▸ hm⟩, h3⟩
    rw [h2]
    exact hcell c hc
  · have h2 : ({a ∈ ({a ∈ A | n ∈ ends a ∧ m (ce a)} : Finset Arc) | ce a = c} : Finset Arc) = ∅
    := by
      ext a
      simp only [mem_filter, notMem_empty, iff_false]
      rintro ⟨⟨-, -, h3⟩, h4⟩
      exact hm (h4 ▸ h3)
    rw [h2]
    simp

open Classical in
/-- **Faces with different pairs of change nodes form a triangle.** -/
theorem exists_triangle (P : Finset Face) (Z : Finset Node) (p : Face → Finset Node) (hZ : #Z ≤ 3)
  (hp : ∀ f ∈ P, p f ⊆ Z ∧ #(p f) = 2)
    (hinj : Set.InjOn p P) (hne : P.Nonempty) (heven : ∀ n ∈ Z, Even #{f ∈ P | n ∈ p f}) :
    ∃ x y z f g h, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ Z = {x, y, z} ∧ P = {f, g, h} ∧ f ≠ g ∧ g ≠ h ∧ f ≠ h
      ∧ p f = {x, y} ∧ p g = {y, z} ∧ p h = {x, z} := by
  classical
  obtain ⟨f, hf⟩ := hne
  obtain ⟨u, v, huv, hfe⟩ := card_eq_two.mp (hp f hf).2
  have hu : u ∈ p f := by simp [hfe]
  have hv : v ∈ p f := by simp [hfe]
  have hother : ∀ {n}, n ∈ p f → ∃ g ∈ P, g ≠ f ∧ n ∈ p g := fun {n} hn => by
    have hnZ := (hp f hf).1 hn
    have hm : f ∈ ({f ∈ P | n ∈ p f} : Finset Face) := mem_filter.mpr ⟨hf, hn⟩
    have h2 : 1 < #({f ∈ P | n ∈ p f} : Finset Face) := by
      have hpos := card_pos.mpr ⟨f, hm⟩
      obtain ⟨k, hk⟩ := heven n hnZ
      omega
    obtain ⟨g, hg, hne⟩ := exists_mem_ne h2 f
    exact ⟨g, (mem_filter.mp hg).1, hne, (mem_filter.mp hg).2⟩
  obtain ⟨g, hg, hgf, hug⟩ := hother hu
  obtain ⟨a, b, hab, hge⟩ := card_eq_two.mp (hp g hg).2
  have hgne : p g ≠ p f := fun h => hgf (hinj hg hf h)
  obtain ⟨w, huw, hgw⟩ : ∃ w, u ≠ w ∧ p g = {u, w} := by
    rw [hge] at hug ⊢
    simp only [mem_insert, mem_singleton] at hug
    rcases hug with rfl | rfl
    · exact ⟨b, hab, rfl⟩
    · exact ⟨a, hab.symm, pair_comm _ _⟩
  have hvw : v ≠ w := fun h => hgne (by rw [hgw, hfe, h])
  have hwZ : w ∈ Z := (hp g hg).1 (by simp [hgw])
  have hZe : Z = {u, v, w} := by
    refine (eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact (hp f hf).1 hu
      · exact (hp f hf).1 hv
      · exact hwZ
    · rw [card_insert_of_notMem (by simp [huv, huw]), card_insert_of_notMem
      (by simpa using hvw), card_singleton]
      exact hZ
  have hpairs : ∀ e ∈ P, p e = {u, v} ∨ p e = {u, w} ∨ p e = {v, w} := fun e he => by
    obtain ⟨hs, hc⟩ := hp e he
    obtain ⟨a, b, hab, hee⟩ := card_eq_two.mp hc
    have ha : a ∈ Z := hs (by simp [hee])
    have hb : b ∈ Z := hs (by simp [hee])
    rw [hZe] at ha hb
    simp only [mem_insert, mem_singleton] at ha hb
    rw [hee]
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp_all [pair_comm]
  obtain ⟨h, hh, hhf, hvh⟩ := hother hv
  have hhe : p h = {v, w} := by
    rcases hpairs h hh with h3 | h3 | h3
    · exact absurd (hinj hh hf (h3.trans hfe.symm)) hhf
    · rw [h3] at hvh
      simp only [mem_insert, mem_singleton] at hvh
      rcases hvh with h4 | h4
      · exact absurd h4 huv.symm
      · exact absurd h4 hvw
    · exact h3
  have hgh : g ≠ h := fun e => by
    have h3 := (e ▸ hgw : p h = {u, w}).symm.trans hhe
    have h4 : u ∈ ({v, w} : Finset Node) := h3 ▸ by simp
    simp only [mem_insert, mem_singleton] at h4
    rcases h4 with h4 | h4
    · exact huv h4
    · exact huw h4
  refine ⟨v, u, w, f, g, h, huv.symm, huw, hvw, ?_, ?_, hgf.symm, hgh, hhf.symm, by rw [hfe,
    pair_comm], hgw, hhe⟩
  · rw [hZe]
    ext x
    simp only [mem_insert, mem_singleton]
    tauto
  · ext e
    simp only [mem_insert, mem_singleton]
    constructor
    · intro he
      rcases hpairs e he with h3 | h3 | h3
      · exact .inl (hinj he hf (h3.trans hfe.symm))
      · exact .inr (.inl (hinj he hg (h3.trans hgw.symm)))
      · exact .inr (.inr (hinj he hh (h3.trans hhe.symm)))
    · rintro (rfl | rfl | rfl)
      · exact hf
      · exact hg
      · exact hh

section System

variable [Fintype Arc] [Fintype Cell] (ce : Arc → Cell) (fc : Arc → Face) (ends : Arc → Finset Node)

open Classical in
/-- `(f, n)` is a change of the class `I`: an edge of `δ(I)` in the proof of (11.1). -/
def Chg (I : Finset Cell) (f : Face) (n : Node) : Prop :=
  Odd (markCount univ fc ends (fun a => ce a ∈ I) f n)

omit [Fintype Cell] in
open Classical in
/-- The changes of a symmetric difference are the symmetric difference of the changes. -/
theorem chg_symmDiff (I K : Finset Cell) (f : Face) (n : Node) :
    Chg ce fc ends (symmDiff I K) f n ↔ ¬ (Chg ce fc ends I f n ↔ Chg ce fc ends K f n) := by
  classical
  have h : markCount univ fc ends (fun a => ce a ∈ I) f n + markCount univ fc ends (fun a
    => ce a ∈ K) f n =
      markCount univ fc ends (fun a => ce a ∈ symmDiff I K) f n + 2 * #{a | fc a = f ∧ n ∈ ends a
        ∧ ce a ∈ I ∧ ce a ∈ K} := by
    simp only [markCount, card_filter, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun a _ => ?_
    by_cases h1 : fc a = f <;> by_cases h2 : n ∈ ends a <;> by_cases h3 : ce a ∈ I
      <;> by_cases h4 : ce a ∈ K <;> simp [h1, h2, h3, h4, mem_symmDiff]
  simp only [Chg, Nat.odd_iff]
  revert h
  generalize markCount univ fc ends (fun a => ce a ∈ I) f n = x
  generalize markCount univ fc ends (fun a => ce a ∈ K) f n = y
  generalize markCount univ fc ends (fun a => ce a ∈ symmDiff I K) f n = z
  generalize #{a | fc a = f ∧ n ∈ ends a ∧ ce a ∈ I ∧ ce a ∈ K} = w
  intro h
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;> rcases Nat.mod_two_eq_zero_or_one y with hy
    | hy <;> rcases Nat.mod_two_eq_zero_or_one z with hz | hz <;>
    first | (simp [hx, hy, hz]; done) | omega

open Classical in
/-- The facts on arcs, cells and faces that the proof of Claims (3) and (4) uses. `ti c` is the set
of nodes of the cell `c`. -/
structure ArcSystem (ti : Cell → Finset Node) (Nd : Finset Node) : Prop where
  ends_card : ∀ a, #(ends a) = 2
  ends_sub : ∀ a, ends a ⊆ ti (ce a)
  ti_sub : ∀ c, ti c ⊆ Nd
  cover : ∀ n ∈ Nd, ∃ c, n ∈ ti c
  cell_two : ∀ c, ∀ n ∈ ti c, #{a | ce a = c ∧ n ∈ ends a} = 2
  face_two : ∀ a, ∀ n ∈ ends a, #{b | fc b = fc a ∧ n ∈ ends b} = 2
  empty : ∀ K : Finset Cell, (∀ f n, ¬ Chg ce fc ends K f n) → K = ∅ ∨ K = univ
  par : ∀ f g : Face, ∀ u v : Node, f ≠ g → u ≠ v → (∃ a, fc a = f ∧ u ∈ ends a) → (∃ a, fc a = f
    ∧ v ∈ ends a) → (∃ a, fc a = g ∧ u ∈ ends a) → (∃ a, fc a = g ∧ v ∈ ends a) →
    ∃ c a b, ti c = {u, v} ∧ ce a = c ∧ ce b = c ∧ fc a = f ∧ fc b = g ∧ ends a = {u, v} ∧ ends b
      = {u, v}

variable {ce fc ends} {ti : Cell → Finset Node} {Nd : Finset Node}

open Classical in
/-- The nodes of a class of cells. -/
noncomputable def nodesOf (ti : Cell → Finset Node) (I : Finset Cell) : Finset Node := I.biUnion ti

open Classical in
/-- The nodes with a change of `I` at the face `f`. -/
noncomputable def chgNodes (ce : Arc → Cell) (fc : Arc → Face) (ends : Arc → Finset Node)
  (Nd : Finset Node) (I : Finset Cell) (f : Face) : Finset Node :=
  {n ∈ Nd | Chg ce fc ends I f n}

open Classical in
theorem nodesOf_sub (h : ArcSystem ce fc ends ti Nd) (I : Finset Cell) : nodesOf ti I ⊆ Nd :=
  biUnion_subset.mpr fun c _ => h.ti_sub c

theorem chg_arcs (h : ArcSystem ce fc ends ti Nd) {I : Finset Cell} {f : Face} {n : Node}
  (hc : Chg ce fc ends I f n) :
    ∃ a b, fc a = f ∧ fc b = f ∧ n ∈ ends a ∧ n ∈ ends b ∧ ce a ∈ I ∧ ce b ∉ I := by
  classical
  have hpos := hc.pos
  rw [markCount, card_pos] at hpos
  obtain ⟨a, ha⟩ := hpos
  simp only [mem_filter, mem_univ, true_and] at ha
  obtain ⟨ha1, ha2, ha3⟩ := ha
  have htot := h.face_two a n ha2
  rw [ha1] at htot
  have hsplit : #({b | fc b = f ∧ n ∈ ends b} : Finset Arc) = markCount univ fc ends (fun a
    => ce a ∈ I) f n + #{b | fc b = f ∧ n ∈ ends b ∧ ce b ∉ I} := by
    simp only [markCount, card_filter, ← sum_add_distrib]
    refine sum_congr rfl fun b _ => ?_
    by_cases h1 : fc b = f <;> by_cases h2 : n ∈ ends b <;> by_cases h3 : ce b ∈ I
      <;> simp [h1, h2, h3]
  obtain ⟨k, hk⟩ := hc
  obtain ⟨b, hb⟩ : (({b | fc b = f ∧ n ∈ ends b ∧ ce b ∉ I} : Finset Arc)).Nonempty := by
    rw [← card_pos]
    omega
  simp only [mem_filter, mem_univ, true_and] at hb
  obtain ⟨hb1, hb2, hb3⟩ := hb
  exact ⟨a, b, ha1, hb1, ha2, hb2, ha3, hb3⟩

open Classical in
theorem chg_shared (h : ArcSystem ce fc ends ti Nd) {I : Finset Cell} {f : Face} {n : Node}
  (hc : Chg ce fc ends I f n) :
    n ∈ nodesOf ti I ∩ nodesOf ti Iᶜ := by
  classical
  obtain ⟨a, b, -, -, ha, hb, hI, hJ⟩ := chg_arcs h hc
  exact mem_inter.mpr ⟨mem_biUnion.mpr ⟨_, hI, h.ends_sub a ha⟩, mem_biUnion.mpr ⟨_, mem_compl.mpr
    hJ, h.ends_sub b hb⟩⟩

open Classical in
theorem chg_mem (h : ArcSystem ce fc ends ti Nd) {I : Finset Cell} {f : Face} {n : Node}
  (hc : Chg ce fc ends I f n) : n ∈ Nd :=
  nodesOf_sub h I (mem_inter.mp (chg_shared h hc)).1

open Classical in
/-- Two different arcs of a face at a node with a change have cells in different classes. -/
theorem cells_differ (h : ArcSystem ce fc ends ti Nd) {I : Finset Cell} {f : Face} {n : Node} {a b
  : Arc} (hc : Chg ce fc ends I f n) (ha : fc a = f) (hb : fc b = f)
    (han : n ∈ ends a) (hbn : n ∈ ends b) (hab : a ≠ b) : ¬ (ce a ∈ I ↔ ce b ∈ I) := by
  classical
  intro hiff
  have htot := h.face_two a n han
  rw [ha] at htot
  have hset : ({x | fc x = f ∧ n ∈ ends x} : Finset Arc) = {a, b} := by
    refine (eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact mem_filter.mpr ⟨mem_univ _, ha, han⟩
      · exact mem_filter.mpr ⟨mem_univ _, hb, hbn⟩
    · rw [htot, card_pair hab]
  have hm : Even (markCount univ fc ends (fun a => ce a ∈ I) f n) := by
    by_cases hI : ce a ∈ I
    · have h2 : markCount univ fc ends (fun a => ce a ∈ I) f n = 2 := by
        rw [markCount]
        refine (congrArg card (?_ : _ = ({a, b} : Finset Arc))).trans (card_pair hab)
        rw [← hset]
        ext x
        simp only [mem_filter, mem_univ, true_and]
        constructor
        · exact fun h => ⟨h.1, h.2.1⟩
        · intro hx
          have hx' : x ∈ ({a, b} : Finset Arc) := hset ▸ mem_filter.mpr ⟨mem_univ _, hx.1, hx.2⟩
          simp only [mem_insert, mem_singleton] at hx'
          rcases hx' with rfl | rfl
          · exact ⟨hx.1, hx.2, hI⟩
          · exact ⟨hx.1, hx.2, hiff.mp hI⟩
      rw [h2]
      exact even_two
    · have h2 : markCount univ fc ends (fun a => ce a ∈ I) f n = 0 := by
        rw [markCount]
        refine (congrArg card (?_ : _ = (∅ : Finset Arc))).trans card_empty
        ext x
        simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
        rintro ⟨h1, h2, h3⟩
        have hx' : x ∈ ({a, b} : Finset Arc) := hset ▸ mem_filter.mpr ⟨mem_univ _, h1, h2⟩
        simp only [mem_insert, mem_singleton] at hx'
        rcases hx' with rfl | rfl
        · exact hI h3
        · exact hI (hiff.mpr h3)
      rw [h2]
      exact Even.zero
  exact (Nat.not_even_iff_odd.mpr hc) hm

omit [Fintype Cell] in
open Classical in
/-- Two arcs of a face at a node with cells in different classes make a change there. -/
theorem chg_of_differ (htwo : ∀ a, ∀ n ∈ ends a, #{b | fc b = fc a ∧ n ∈ ends b}
  = 2) {I : Finset Cell} {f : Face} {n : Node} {a b : Arc} (ha : fc a = f) (hb : fc b = f)
    (han : n ∈ ends a) (hbn : n ∈ ends b) (hab : a ≠ b) (hd : ¬ (ce a ∈ I ↔ ce b ∈ I)) : Chg ce fc
      ends I f n := by
  classical
  have htot := htwo a n han
  rw [ha] at htot
  have hset : ({x | fc x = f ∧ n ∈ ends x} : Finset Arc) = {a, b} := by
    refine (eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact mem_filter.mpr ⟨mem_univ _, ha, han⟩
      · exact mem_filter.mpr ⟨mem_univ _, hb, hbn⟩
    · rw [htot, card_pair hab]
  have hmem : ∀ x, fc x = f → n ∈ ends x → x = a ∨ x = b := fun x h1 h2 => by
    have hx' : x ∈ ({a, b} : Finset Arc) := hset ▸ mem_filter.mpr ⟨mem_univ _, h1, h2⟩
    simpa using hx'
  have hone : markCount univ fc ends (fun a => ce a ∈ I) f n = 1 := by
    rw [markCount]
    by_cases hI : ce a ∈ I
    · refine (congrArg card (?_ : _ = ({a} : Finset Arc))).trans (card_singleton _)
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨h1, h2, h3⟩
        rcases hmem x h1 h2 with rfl | rfl
        · rfl
        · exact absurd (iff_of_true hI h3) hd
      · rintro rfl
        exact ⟨ha, han, hI⟩
    · have hJ : ce b ∈ I := by
        by_contra hJ
        exact hd (iff_of_false hI hJ)
      refine (congrArg card (?_ : _ = ({b} : Finset Arc))).trans (card_singleton _)
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨h1, h2, h3⟩
        rcases hmem x h1 h2 with rfl | rfl
        · exact absurd h3 hI
        · rfl
      · rintro rfl
        exact ⟨hb, hbn, hJ⟩
  rw [Chg, hone]
  exact odd_one

open Classical in
/-- The arcs of a cell with two nodes are the two arcs given. -/
theorem arcs_of_cell (h : ArcSystem ce fc ends ti Nd) {c : Cell} {u v : Node} {a b : Arc}
  (ht : ti c = {u, v}) (ha : ce a = c) (hb : ce b = c) (hae : ends a = {u, v}) (hbe : ends b
    = {u, v})
    (hab : a ≠ b) (x : Arc) (hx : ce x = c) : x = a ∨ x = b := by
  classical
  have hu : u ∈ ti c := by simp [ht]
  have htot := h.cell_two c u hu
  have hset : ({x | ce x = c ∧ u ∈ ends x} : Finset Arc) = {a, b} := by
    refine (eq_of_subset_of_card_le ?_ ?_).symm
    · intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact mem_filter.mpr ⟨mem_univ _, ha, by simp [hae]⟩
      · exact mem_filter.mpr ⟨mem_univ _, hb, by simp [hbe]⟩
    · rw [htot, card_pair hab]
  have hxe : ends x = {u, v} := by
    refine eq_of_subset_of_card_le (ht ▸ hx ▸ h.ends_sub x) ?_
    rw [h.ends_card x]
    exact card_le_two
  have hm : x ∈ ({a, b} : Finset Arc) := hset ▸ mem_filter.mpr ⟨mem_univ _, hx, by simp [hxe]⟩
  simpa using hm

theorem mem_chgNodes (h : ArcSystem ce fc ends ti Nd) {I : Finset Cell} {f : Face} {n : Node} : n ∈
  chgNodes ce fc ends Nd I f ↔ Chg ce fc ends I f n := by
  classical
  simp only [chgNodes, mem_filter, and_iff_right_iff_imp]
  exact chg_mem h

open Classical in
theorem chgNodes_card (h : ArcSystem ce fc ends ti Nd) {I : Finset Cell}
  (hZ : #(nodesOf ti I ∩ nodesOf ti Iᶜ) ≤ 3) (f : Face) :
    chgNodes ce fc ends Nd I f ⊆ nodesOf ti I ∩ nodesOf ti Iᶜ ∧ (#(chgNodes ce fc ends Nd I f) = 0
      ∨ #(chgNodes ce fc ends Nd I f) = 2) := by
  classical
  have hsub : chgNodes ce fc ends Nd I f ⊆ nodesOf ti I ∩ nodesOf ti Iᶜ := fun n hn => chg_shared h
    ((mem_chgNodes h).mp hn)
  have hev : Even #(chgNodes ce fc ends Nd I f) := by
    have := even_face univ fc ends (fun a => ce a ∈ I) f Nd fun a _ _ => ⟨(h.ends_sub a).trans
      (h.ti_sub _), h.ends_card a⟩
    convert this using 2
    ext n
    rw [mem_filter, chgNodes, mem_filter]
    rfl
  have hle := (card_le_card hsub).trans hZ
  obtain ⟨k, hk⟩ := hev
  exact ⟨hsub, by omega⟩

variable (ce fc ends Nd) in
open Classical in
/-- The faces with a change of `I`. -/
noncomputable def chgFaces (I : Finset Cell) : Finset Face :=
  {f ∈ univ.image fc | (chgNodes ce fc ends Nd I f).Nonempty}

theorem mem_chgFaces (h : ArcSystem ce fc ends ti Nd) {I : Finset Cell} {f : Face} : f ∈ chgFaces
  ce fc ends Nd I ↔ (chgNodes ce fc ends Nd I f).Nonempty := by
  classical
  simp only [chgFaces, mem_filter, and_iff_right_iff_imp]
  rintro ⟨n, hn⟩
  obtain ⟨a, -, ha, -⟩ := chg_arcs h ((mem_chgNodes h).mp hn)
  exact mem_image.mpr ⟨a, mem_univ _, ha⟩

open Classical in
theorem even_at_node (h : ArcSystem ce fc ends ti Nd) (I : Finset Cell) {n : Node} (_hn : n ∈ Nd) :
    Even #{f ∈ chgFaces ce fc ends Nd I | n ∈ chgNodes ce fc ends Nd I f} := by
  classical
  have hc : ∀ c ∈ (univ : Finset Cell), Even #{a ∈ (univ : Finset Arc) | ce a = c ∧ n ∈ ends a}
    := fun c _ => by
    by_cases hnc : n ∈ ti c
    · have h2 := h.cell_two c n hnc
      have h3 : Even #({a | ce a = c ∧ n ∈ ends a} : Finset Arc) := h2 ▸ even_two
      convert h3
    · have h0 : ({a ∈ (univ : Finset Arc) | ce a = c ∧ n ∈ ends a}) = ∅ := by
        ext a
        simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
        rintro ⟨rfl, h2⟩
        exact hnc (h.ends_sub a h2)
      rw [h0]
      simp
  have := even_node univ fc ce ends (· ∈ I) (univ.image fc) univ n (fun a _ => mem_image_of_mem fc
    (mem_univ a)) (fun a _ => mem_univ _) hc
  convert this using 2
  ext f
  simp only [mem_filter, mem_chgFaces h, mem_chgNodes h]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨m, hm⟩ := h1
    exact ⟨(mem_filter.mp (mem_chgFaces h |>.mpr ⟨m, hm⟩)).1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨n, (mem_chgNodes h).mpr h2⟩, h2⟩

open Classical in
/-- The arc of a pair of parallel faces at the first face is not that of another pair. -/
theorem arcs_ne (h : ArcSystem ce fc ends ti Nd) {c c' : Cell} {u v : Node} {a b a' b' : Arc} {e e₁
  e₂ : Face} (ht : ti c = {u, v}) (ha : ce a = c) (hb : ce b = c) (hae : ends a = {u, v})
    (hbe : ends b = {u, v})
    (hfa : fc a = e) (hfb : fc b = e₁) (ha' : ce a' = c') (hb' : ce b' = c') (hfa' : fc a' = e)
      (hfb' : fc b' = e₂) (h1 : e ≠ e₁) (h2 : e ≠ e₂) (h3 : e₁ ≠ e₂) : a ≠ a' := by
  classical
  rintro rfl
  have hab : a ≠ b := fun e' => h1 (hfa.symm.trans ((congrArg fc e').trans hfb))
  obtain rfl : c = c' := ha.symm.trans ha'
  rcases arcs_of_cell h ht ha hb hae hbe hab b' hb' with rfl | rfl
  · exact h2 (hfa.symm.trans hfb')
  · exact h3 (hfb.symm.trans hfb')

open Classical in
/-- Three faces with the same pair of changes cannot exist, by Claim (2): the three cells of the
three pairs would lie in pairwise different classes. -/
theorem no_three_faces (h : ArcSystem ce fc ends ti Nd) {I : Finset Cell} {f g k : Face} {u v :
  Node} (huv : u ≠ v) (hf : chgNodes ce fc ends Nd I f = {u, v}) (hg : chgNodes ce fc ends Nd I g
    = {u, v})
    (hk : chgNodes ce fc ends Nd I k = {u, v}) (hfg : f ≠ g) (hfk : f ≠ k) (hgk : g ≠ k) : False
      := by
  classical
  have hch : ∀ {e}, chgNodes ce fc ends Nd I e = {u, v} → Chg ce fc ends I e u
    ∧ Chg ce fc ends I e v := fun {e} he =>
    ⟨(mem_chgNodes h).mp (by simp [he]), (mem_chgNodes h).mp (by simp [he])⟩
  have hon : ∀ {e n}, Chg ce fc ends I e n → ∃ a, fc a = e ∧ n ∈ ends a := fun {e n} hc => by
    obtain ⟨a, -, ha, -, han, -⟩ := chg_arcs h hc
    exact ⟨a, ha, han⟩
  obtain ⟨hfu, hfv⟩ := hch hf
  obtain ⟨hgu, hgv⟩ := hch hg
  obtain ⟨hku, hkv⟩ := hch hk
  obtain ⟨c₁, a₁, b₁, ht₁, ha₁, hb₁, hfa₁, hfb₁, hae₁, hbe₁⟩ := h.par f g u v hfg huv (hon hfu)
    (hon hfv) (hon hgu) (hon hgv)
  obtain ⟨c₂, a₂, b₂, ht₂, ha₂, hb₂, hfa₂, hfb₂, hae₂, hbe₂⟩ := h.par f k u v hfk huv (hon hfu)
    (hon hfv) (hon hku) (hon hkv)
  obtain ⟨c₃, a₃, b₃, ht₃, ha₃, hb₃, hfa₃, hfb₃, hae₃, hbe₃⟩ := h.par g k u v hgk huv (hon hgu)
    (hon hgv) (hon hku) (hon hkv)
  have hmem : ∀ {a}, ends a = {u, v} → u ∈ ends a := fun {a} he => by simp [he]
  have d1 := cells_differ h hfu hfa₁ hfa₂ (hmem hae₁) (hmem hae₂) (arcs_ne h ht₁ ha₁ hb₁ hae₁ hbe₁
    hfa₁ hfb₁ ha₂ hb₂ hfa₂ hfb₂ hfg hfk hgk)
  have d2 := cells_differ h hgu hfb₁ hfa₃ (hmem hbe₁) (hmem hae₃) (arcs_ne h ht₁ hb₁ ha₁ hbe₁ hae₁
    hfb₁ hfa₁ ha₃ hb₃ hfa₃ hfb₃ hfg.symm hgk hfk)
  have d3 := cells_differ h hku hfb₂ hfb₃ (hmem hbe₂) (hmem hbe₃) (arcs_ne h ht₂ hb₂ ha₂ hbe₂ hae₂
    hfb₂ hfa₂ hb₃ ha₃ hfb₃ hfa₃ hfk.symm hgk.symm hfg)
  rw [ha₁, ha₂] at d1
  rw [hb₁, ha₃] at d2
  rw [hb₂, hb₃] at d3
  tauto

open Classical in
/-- The changes of one cell with two nodes, whose two arcs are on the faces `f` and `g`. -/
theorem chg_single (h : ArcSystem ce fc ends ti Nd) {c : Cell} {u v : Node} {a b : Arc} {f g :
  Face} (ht : ti c = {u, v}) (ha : ce a = c) (hb : ce b = c) (hfa : fc a = f) (hfb : fc b = g)
    (hae : ends a = {u, v}) (hbe : ends b = {u, v})
    (hfg : f ≠ g) (e : Face) (n : Node) : Chg ce fc ends {c} e n ↔ (e = f ∨ e = g) ∧ (n = u ∨ n
      = v) := by
  classical
  have hab : a ≠ b := fun e' => hfg (hfa.symm.trans ((congrArg fc e').trans hfb))
  have harcs := arcs_of_cell h ht ha hb hae hbe hab
  have hin : ∀ {x}, n ∈ ends x → ends x = {u, v} → n = u ∨ n = v := fun {x} hx he
    => by simpa [he] using hx
  have hm : ∀ x, (fc x = e ∧ n ∈ ends x ∧ ce x = c) ↔ (x = a ∧ e = f ∧ (n = u ∨ n = v)) ∨ (x = b
    ∧ e = g ∧ (n = u ∨ n = v)) := fun x => by
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases harcs x h3 with rfl | rfl
      · exact .inl ⟨rfl, h1.symm.trans hfa, hin h2 hae⟩
      · exact .inr ⟨rfl, h1.symm.trans hfb, hin h2 hbe⟩
    · rintro (⟨rfl, rfl, h2⟩ | ⟨rfl, rfl, h2⟩)
      · exact ⟨hfa, by simpa [hae] using h2, ha⟩
      · exact ⟨hfb, by simpa [hbe] using h2, hb⟩
  rw [Chg, markCount]
  by_cases hn : n = u ∨ n = v
  · by_cases hf : e = f
    · have hc : ({x | fc x = e ∧ n ∈ ends x ∧ ce x ∈ ({c} : Finset Cell)} : Finset Arc).card = 1
      := by
        refine (congrArg card (?_ : _ = ({a} : Finset Arc))).trans (card_singleton _)
        ext x
        simp only [mem_filter, mem_univ, true_and, mem_singleton, hm x]
        have hne : e ≠ g := hf ▸ hfg
        constructor
        · rintro (⟨h1, -⟩ | ⟨-, h1, -⟩)
          · exact h1
          · exact absurd h1 hne
        · exact fun h1 => .inl ⟨h1, hf, hn⟩
      have hc' : Odd (({x | fc x = e ∧ n ∈ ends x ∧ ce x ∈ ({c} : Finset Cell)} : Finset Arc).card)
        := hc ▸ odd_one
      exact ⟨fun _ => ⟨.inl hf, hn⟩, fun _ => by convert hc'⟩
    · by_cases hg : e = g
      · have hc : ({x | fc x = e ∧ n ∈ ends x ∧ ce x ∈ ({c} : Finset Cell)} : Finset Arc).card = 1
        := by
          refine (congrArg card (?_ : _ = ({b} : Finset Arc))).trans (card_singleton _)
          ext x
          simp only [mem_filter, mem_univ, true_and, mem_singleton, hm x]
          constructor
          · rintro (⟨-, h1, -⟩ | ⟨h1, -⟩)
            · exact absurd h1 hf
            · exact h1
          · exact fun h1 => .inr ⟨h1, hg, hn⟩
        have hc' : Odd (({x | fc x = e ∧ n ∈ ends x ∧ ce x ∈ ({c} : Finset Cell)} : Finset
          Arc).card) := hc ▸ odd_one
        exact ⟨fun _ => ⟨.inr hg, hn⟩, fun _ => by convert hc'⟩
      · have hc : ({x | fc x = e ∧ n ∈ ends x ∧ ce x ∈ ({c} : Finset Cell)} : Finset Arc) = ∅ := by
          ext x
          simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false, mem_singleton, hm x]
          tauto
        constructor
        · intro hodd
          have : Odd (({x | fc x = e ∧ n ∈ ends x ∧ ce x ∈ ({c} : Finset Cell)} : Finset Arc).card)
            := by convert hodd
          rw [hc] at this
          simp at this
        · rintro ⟨h3 | h3, -⟩
          · exact absurd h3 hf
          · exact absurd h3 hg
  · have hc : ({x | fc x = e ∧ n ∈ ends x ∧ ce x ∈ ({c} : Finset Cell)} : Finset Arc) = ∅ := by
      ext x
      simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false, mem_singleton, hm x]
      tauto
    constructor
    · intro hodd
      have : Odd (({x | fc x = e ∧ n ∈ ends x ∧ ce x ∈ ({c} : Finset Cell)} : Finset Arc).card)
        := by convert hodd
      rw [hc] at this
      simp at this
    · rintro ⟨-, h3⟩
      exact absurd h3 hn

theorem nodesOf_univ (h : ArcSystem ce fc ends ti Nd) : nodesOf ti (univ : Finset Cell) = Nd := by
  classical
  refine Subset.antisymm (nodesOf_sub h _) fun n hn => ?_
  obtain ⟨c, hc⟩ := h.cover n hn
  exact mem_biUnion.mpr ⟨c, mem_univ _, hc⟩

variable (ce fc ends Nd ti) in
open Classical in
/-- `δ(I)` is a circuit of length six in the sense of Claim (4): three faces and three nodes in a
triangle. -/
def IsTri (I : Finset Cell) : Prop :=
  ∃ x y z f g k, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ nodesOf ti I ∩ nodesOf ti Iᶜ = {x, y, z}
    ∧ chgFaces ce fc ends Nd I = {f, g, k} ∧ f ≠ g ∧ g ≠ k ∧ f ≠ k ∧
    chgNodes ce fc ends Nd I f = {x, y} ∧ chgNodes ce fc ends Nd I g = {y, z}
      ∧ chgNodes ce fc ends Nd I k = {x, z}

open Classical in
/-- **Claim (4) of the proof of (11.1)**, page 191, by induction on the number of faces with
changes. If two faces have the same pair of changes, then the cell of Claim (2) on them is moved to
the other class. This removes these two faces and no others, and adds no shared nodes. The induction
gives a third face with the same pair, against `no_three_faces`. -/
theorem triangle_of_system (h : ArcSystem ce fc ends ti Nd) : ∀ (m : ℕ)
  (I : Finset Cell), #(chgFaces ce fc ends Nd I) = m → nodesOf ti I ≠ Nd → nodesOf ti Iᶜ ≠ Nd →
    #(nodesOf ti I ∩ nodesOf ti Iᶜ) ≤ 3 → IsTri ce fc ends ti Nd I := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro I hm hI hJ hZ
  by_cases hinj : Set.InjOn (chgNodes ce fc ends Nd I) (chgFaces ce fc ends Nd I : Set Face)
  · have hne : (chgFaces ce fc ends Nd I).Nonempty := by
      by_contra hne
      have hno : ∀ f n, ¬ Chg ce fc ends I f n := fun f n hc => hne ⟨f, (mem_chgFaces h).mpr ⟨n,
        (mem_chgNodes h).mpr hc⟩⟩
      rcases h.empty I hno with rfl | rfl
      · exact hJ (by rw [compl_empty, nodesOf_univ h])
      · exact hI (nodesOf_univ h)
    have hp : ∀ f ∈ chgFaces ce fc ends Nd I, chgNodes ce fc ends Nd I f ⊆ nodesOf ti I ∩ nodesOf
      ti Iᶜ ∧ #(chgNodes ce fc ends Nd I f) = 2 := fun f hf => by
      obtain ⟨h1, h2⟩ := chgNodes_card h hZ f
      have h3 := card_pos.mpr ((mem_chgFaces h).mp hf)
      exact ⟨h1, by omega⟩
    have heven : ∀ n ∈ nodesOf ti I ∩ nodesOf ti Iᶜ, Even #{f ∈ chgFaces ce fc ends Nd I | n ∈
      chgNodes ce fc ends Nd I f} := fun n hn =>
      even_at_node h I (nodesOf_sub h I (mem_inter.mp hn).1)
    obtain ⟨x, y, z, f, g, k, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
      := exists_triangle _ _ _ hZ hp hinj hne heven
    exact ⟨x, y, z, f, g, k, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  · exfalso
    simp only [Set.InjOn, not_forall] at hinj
    obtain ⟨f, hf, g, hg, hEq, hfg⟩ := hinj
    have hf' : f ∈ chgFaces ce fc ends Nd I := hf
    have hg' : g ∈ chgFaces ce fc ends Nd I := hg
    have hcard : #(chgNodes ce fc ends Nd I f) = 2 := by
      obtain ⟨-, h2⟩ := chgNodes_card h hZ f
      have h3 := card_pos.mpr ((mem_chgFaces h).mp hf')
      omega
    obtain ⟨u, v, huv, hfe⟩ := card_eq_two.mp hcard
    have hge : chgNodes ce fc ends Nd I g = {u, v} := hEq ▸ hfe
    have hDf : ∀ n, Chg ce fc ends I f n ↔ n = u ∨ n = v := fun n => by
      rw [← mem_chgNodes h, hfe]
      simp
    have hDg : ∀ n, Chg ce fc ends I g n ↔ n = u ∨ n = v := fun n => by
      rw [← mem_chgNodes h, hge]
      simp
    have hon : ∀ {e n}, Chg ce fc ends I e n → ∃ a, fc a = e ∧ n ∈ ends a := fun {e n} hc => by
      obtain ⟨a, -, ha, -, han, -⟩ := chg_arcs h hc
      exact ⟨a, ha, han⟩
    have hfu := (hDf u).mpr (.inl rfl)
    have hfv := (hDf v).mpr (.inr rfl)
    have hgu := (hDg u).mpr (.inl rfl)
    have hgv := (hDg v).mpr (.inr rfl)
    obtain ⟨c, a, b, ht, ha, hb, hfa, hfb, hae, hbe⟩ := h.par f g u v hfg huv (hon hfu) (hon hfv)
      (hon hgu) (hon hgv)
    have hS := chg_single h ht ha hb hfa hfb hae hbe hfg
    set I' := symmDiff I {c} with hI'def
    have hX : ∀ e n, Chg ce fc ends I' e n ↔ ¬ (Chg ce fc ends I e n ↔ ((e = f ∨ e = g) ∧ (n = u
      ∨ n = v))) := fun e n => by
      rw [hI'def, chg_symmDiff, hS e n]
    have hoff : ∀ e, e ≠ f → e ≠ g → chgNodes ce fc ends Nd I' e = chgNodes ce fc ends Nd I e
      := fun e h1 h2 => by
      ext n
      rw [mem_chgNodes h, mem_chgNodes h, hX]
      simp [h1, h2]
    have hf0 : chgNodes ce fc ends Nd I' f = ∅ := by
      ext n
      rw [mem_chgNodes h, hX, hDf]
      simp only [notMem_empty, iff_false]
      tauto
    have hg0 : chgNodes ce fc ends Nd I' g = ∅ := by
      ext n
      rw [mem_chgNodes h, hX, hDg]
      simp only [notMem_empty, iff_false]
      tauto
    have hF : chgFaces ce fc ends Nd I' = ((chgFaces ce fc ends Nd I).erase f).erase g := by
      ext e
      simp only [mem_erase, mem_chgFaces h]
      by_cases h1 : e = f
      · subst h1
        simp [hf0]
      · by_cases h2 : e = g
        · subst h2
          simp [hg0]
        · simp [h1, h2, hoff e h1 h2]
    have hlt : #(chgFaces ce fc ends Nd I') < m := by
      rw [hF, card_erase_of_mem (mem_erase.mpr ⟨fun e => hfg e.symm, hg'⟩), card_erase_of_mem hf',
        ← hm]
      have := card_pos.mpr ⟨f, hf'⟩
      omega
    have hc2 : ∀ x ∈ ti c, x ∈ nodesOf ti I ∩ nodesOf ti Iᶜ := fun x hx => by
      have hx' : x = u ∨ x = v := by simpa [ht] using hx
      rcases hx' with rfl | rfl
      · exact chg_shared h hfu
      · exact chg_shared h hfv
    have hsub1 : nodesOf ti I' ⊆ nodesOf ti I := fun x hx => by
      obtain ⟨c', hc', hxc⟩ := mem_biUnion.mp hx
      by_cases e : c' = c
      · exact (mem_inter.mp (hc2 x (e ▸ hxc))).1
      · refine mem_biUnion.mpr ⟨c', ?_, hxc⟩
        rcases mem_symmDiff.mp hc' with h3 | h3
        · exact h3.1
        · exact absurd (mem_singleton.mp h3.1) e
    have hsub2 : nodesOf ti I'ᶜ ⊆ nodesOf ti Iᶜ := fun x hx => by
      obtain ⟨c', hc', hxc⟩ := mem_biUnion.mp hx
      by_cases e : c' = c
      · exact (mem_inter.mp (hc2 x (e ▸ hxc))).2
      · refine mem_biUnion.mpr ⟨c', mem_compl.mpr fun h3 => ?_, hxc⟩
        exact (mem_compl.mp hc') (mem_symmDiff.mpr (.inl ⟨h3, fun h4 => e (mem_singleton.mp h4)⟩))
    have hI1 : nodesOf ti I' ≠ Nd := fun e => hI (Subset.antisymm (nodesOf_sub h I) (e ▸ hsub1))
    have hJ1 : nodesOf ti I'ᶜ ≠ Nd := fun e => hJ (Subset.antisymm (nodesOf_sub h _) (e ▸ hsub2))
    have hZs : nodesOf ti I' ∩ nodesOf ti I'ᶜ ⊆ nodesOf ti I ∩ nodesOf ti Iᶜ
      := inter_subset_inter hsub1 hsub2
    obtain ⟨x, y, z, f', g', k', hxy, hyz, hxz, hZe, hP, hfg', hgk', hfk', hDf', hDg', hDk'⟩
      := ih _ hlt I' rfl hI1 hJ1 ((card_le_card hZs).trans hZ)
    have hZeq : nodesOf ti I' ∩ nodesOf ti I'ᶜ = nodesOf ti I ∩ nodesOf ti Iᶜ := by
      refine eq_of_subset_of_card_le hZs ?_
      have h3 : #(nodesOf ti I' ∩ nodesOf ti I'ᶜ) = 3 := by
        rw [hZe, card_insert_of_notMem (by simp [hxy, hxz]), card_insert_of_notMem
          (by simpa using hyz), card_singleton]
      omega
    have hu : u ∈ ({x, y, z} : Finset Node) := hZe ▸ hZeq ▸ chg_shared h hfu
    have hv : v ∈ ({x, y, z} : Finset Node) := hZe ▸ hZeq ▸ chg_shared h hfv
    obtain ⟨e, heP, hee⟩ : ∃ e ∈ ({f', g', k'} : Finset Face), chgNodes ce fc ends Nd I' e = {u, v}
      := by
      simp only [mem_insert, mem_singleton] at hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
        first
        | exact absurd rfl huv
        | exact ⟨f', by simp, hDf'⟩
        | exact ⟨f', by simp, hDf'.trans (pair_comm _ _)⟩
        | exact ⟨g', by simp, hDg'⟩
        | exact ⟨g', by simp, hDg'.trans (pair_comm _ _)⟩
        | exact ⟨k', by simp, hDk'⟩
        | exact ⟨k', by simp, hDk'.trans (pair_comm _ _)⟩
    have hef : e ≠ f := fun e' => by
      have h3 : u ∈ chgNodes ce fc ends Nd I' e := by
        rw [hee]
        simp
      rw [e', hf0] at h3
      simp at h3
    have heg : e ≠ g := fun e' => by
      have h3 : u ∈ chgNodes ce fc ends Nd I' e := by
        rw [hee]
        simp
      rw [e', hg0] at h3
      simp at h3
    exact no_three_faces h huv hfe hge ((hoff e hef heg).symm.trans hee) hfg hef.symm heg.symm

end System

end GraphMinor.GM17
