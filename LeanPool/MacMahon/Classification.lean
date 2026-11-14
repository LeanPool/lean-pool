/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
-- Modified for Lean Pool integration.
module

public import LeanPool.MacMahon.Structure
public import LeanPool.MacMahon.Partitions

public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators

/-!
# Classification of minimum universal inventories
-/

@[expose] public section
namespace MacMahon
open scoped BigOperators

/-!
The first row of a symmetric degree-two inventory has either one doubled edge
or two distinct neighbours. Relabel these to 01 or to 01 and 02. The ten
partition-cover inequalities exclude the doubled edge and force 12 in the
second case. The degree equations then force the two triangles completely.
-/

/-- Pull an inventory back along a permutation of the tableau labels. -/
def relabel (e : Equiv.Perm Label) (a : Inventory) : Inventory :=
  fun p => a (e p.1, e p.2)

lemma row_relabel (e : Equiv.Perm Label) (a : Inventory) (i : Label) :
    row (relabel e a) i = row a (e i) :=
  Equiv.sum_comp e (fun j => a (e i, j))

lemma partition_sum_relabel (e : Equiv.Perm Label) (a : Inventory) (s : Finset Label) :
    (∑ p, twoTriangles s p * relabel e a p) =
      ∑ p, twoTriangles (s.map e.toEmbedding) p * a p := by
  rw [← (e.prodCongr e).sum_comp (fun p => twoTriangles (s.map e.toEmbedding) p * a p)]
  apply Finset.sum_congr rfl
  intro p _
  simp [twoTriangles, relabel, Prod.map]

lemma partition_cover_relabel (e : Equiv.Perm Label) (a : Inventory)
    (hp : ∀ b : Fin 10, 0 < ∑ p : Pair, winner b p * a p) :
    ∀ b : Fin 10, 0 < ∑ p : Pair, winner b p * relabel e a p := by
  intro b
  obtain ⟨c, hc⟩ := partition_complete ((triple b).map e.toEmbedding)
    (by simp [(winner_two_triangles b).1])
  change 0 < ∑ p, twoTriangles (triple b) p * relabel e a p
  rw [partition_sum_relabel, hc]
  exact hp c

private lemma row_shape (f : Label → ℕ) (hz : f 0 = 0) (hs : ∑ i, f i = 2) :
    (∃ i, i ≠ 0 ∧ f i = 2) ∨
    (∃ i j, i ≠ 0 ∧ j ≠ 0 ∧ i ≠ j ∧ f i = 1 ∧ f j = 1) := by
  obtain ⟨i, _, hi⟩ := Finset.sum_pos_iff.mp (show 0 < ∑ i, f i by omega)
  have hi0 : i ≠ 0 := by rintro rfl; omega
  have hib : f i ≤ 2 := by
    calc f i ≤ ∑ j, f j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
         _ = 2 := hs
  by_cases hi2 : f i = 2
  · exact Or.inl ⟨i, hi0, hi2⟩
  have hi1 : f i = 1 := by omega
  have hrest : ∑ j ∈ Finset.univ.erase i, f j = 1 := by
    have := Finset.sum_erase_add (Finset.univ) f (Finset.mem_univ i)
    omega
  obtain ⟨j, hj, hjp⟩ := Finset.sum_pos_iff.mp
    (show 0 < ∑ j ∈ Finset.univ.erase i, f j by omega)
  have hj0 : j ≠ 0 := by rintro rfl; omega
  have hjb : f j ≤ 1 := by
    calc f j ≤ ∑ k ∈ Finset.univ.erase i, f k :=
           Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj
         _ = 1 := hrest
  exact Or.inr ⟨i, j, hi0, hj0, (Finset.mem_erase.mp hj).1.symm, hi1, by omega⟩

/-- Partition cover excludes a doubled edge at the normalized position 01. -/
lemma no_normalized_doubled_edge (a : Inventory) (hz : DiagonalZero a)
    (hr : ∀ i, row a i = 2) (hs : ∀ i j, a (i, j) = a (j, i))
    (hp : ∀ b : Fin 10, 0 < ∑ p : Pair, winner b p * a p) : a (0, 1) ≠ 2 := by
  norm_num [DiagonalZero, row, Fin.forall_fin_succ, Fin.sum_univ_succ] at hz hr hs
  norm_num [Fin.forall_fin_succ, winner, twoTriangles, triple,
    Fintype.sum_prod_type, Fin.sum_univ_succ, -add_pos_iff] at hp
  omega

/-- Two unit edges from 0 must close to the triangle on labels 0, 1 and 2. -/
lemma normalized_triangle_closes (a : Inventory) (hz : DiagonalZero a)
    (hr : ∀ i, row a i = 2) (hs : ∀ i j, a (i, j) = a (j, i))
    (hp : ∀ b : Fin 10, 0 < ∑ p : Pair, winner b p * a p)
    (h01 : a (0, 1) = 1) (h02 : a (0, 2) = 1) : a (1, 2) = 1 := by
  norm_num [DiagonalZero, row, Fin.forall_fin_succ, Fin.sum_univ_succ] at hz hr hs
  norm_num [Fin.forall_fin_succ, winner, twoTriangles, triple,
    Fintype.sum_prod_type, Fin.sum_univ_succ, -add_pos_iff] at hp
  omega

private lemma winner_zero_matrix : ∀ i j : Label, winner 0 (i, j) =
    ![![0, 1, 1, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![1, 1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 1, 1], ![0, 0, 0, 1, 0, 1], ![0, 0, 0, 1, 1, 0]] i j := by
  decide +kernel

/-- Two local configurations suffice after permuting the labels. -/
private lemma classify_normalized (a : Inventory) (hz : DiagonalZero a)
    (hr : ∀ i, row a i = 2) (hs : ∀ i j, a (i, j) = a (j, i))
    (hp : ∀ b : Fin 10, 0 < ∑ p : Pair, winner b p * a p)
    (hn : a (0, 1) = 2 ∨ (a (0, 1) = 1 ∧ a (0, 2) = 1)) : a = winner 0 := by
  rcases hn with hdouble | ⟨h01, h02⟩
  · exact (no_normalized_doubled_edge a hz hr hs hp hdouble).elim
  have h12 := normalized_triangle_closes a hz hr hs hp h01 h02
  clear hp
  have hrow := hr
  have hsym := hs
  have r0 := row_eq_of_two_unit_entries a 0 1 2 (by decide) (hr 0) h01 h02
  have r1 := row_eq_of_two_unit_entries a 1 0 2 (by decide) (hr 1)
    ((hs 1 0).trans h01) h12
  have r2 := row_eq_of_two_unit_entries a 2 0 1 (by decide) (hr 2)
    ((hs 2 0).trans h02) ((hs 2 1).trans h12)
  norm_num [DiagonalZero, row, Fin.forall_fin_succ, Fin.sum_univ_succ] at hz hr hs
  have hzero : a (0, 3) = 0 ∧ a (0, 4) = 0 ∧ a (0, 5) = 0 ∧
      a (1, 3) = 0 ∧ a (1, 4) = 0 ∧ a (1, 5) = 0 ∧
      a (2, 3) = 0 ∧ a (2, 4) = 0 ∧ a (2, 5) = 0 := by omega
  have hone : a (3, 4) = 1 ∧ a (3, 5) = 1 ∧ a (4, 5) = 1 := by omega
  obtain ⟨h34, h35, h45⟩ := hone
  have r3 := row_eq_of_two_unit_entries a 3 4 5 (by decide) (hrow 3) h34 h35
  have r4 := row_eq_of_two_unit_entries a 4 3 5 (by decide) (hrow 4)
    ((hsym 4 3).trans h34) h45
  have r5 := row_eq_of_two_unit_entries a 5 3 4 (by decide) (hrow 5)
    ((hsym 5 3).trans h35) ((hsym 5 4).trans h45)
  funext ⟨i, j⟩
  rw [winner_zero_matrix]
  fin_cases i
  · fin_cases j <;> exact r0 _
  · fin_cases j <;> exact r1 _
  · fin_cases j <;> exact r2 _
  · fin_cases j <;> exact r3 _
  · fin_cases j <;> exact r4 _
  · fin_cases j <;> exact r5 _

/-- Complete classification using two local configurations, up to relabelling. -/
lemma classify_degree_two (a : Inventory) (hz : DiagonalZero a)
    (hr : ∀ i, row a i = 2) (hs : ∀ i j, a (i, j) = a (j, i))
    (hp : ∀ b : Fin 10, 0 < ∑ p : Pair, winner b p * a p) :
    ∃ b : Fin 10, a = winner b := by
  suffices he : ∃ e : Equiv.Perm Label, relabel e a = winner 0 by
    obtain ⟨e, he⟩ := he
    apply (winners_iff_two_triangles a).mpr
    refine ⟨(triple 0).map e.toEmbedding, by simp [(winner_two_triangles 0).1], ?_⟩
    funext p
    have hh := congrFun he (e.symm p.1, e.symm p.2)
    simpa [relabel, winner, twoTriangles] using hh
  have normalize (e : Equiv.Perm Label)
      (hn : relabel e a (0, 1) = 2 ∨
        (relabel e a (0, 1) = 1 ∧ relabel e a (0, 2) = 1)) :
      relabel e a = winner 0 :=
    classify_normalized (relabel e a) (fun i => hz (e i))
      (fun i => (row_relabel e a i).trans (hr (e i)))
      (fun i j => hs (e i) (e j)) (partition_cover_relabel e a hp) hn
  rcases row_shape (fun j => a (0, j)) (hz 0) (hr 0) with
    ⟨i, hi0, hi⟩ | ⟨i, j, hi0, hj0, hij, hi, hj⟩
  · let e : Equiv.Perm Label := Equiv.swap 1 i
    have he0 : e 0 = 0 := Equiv.swap_apply_of_ne_of_ne (by decide) hi0.symm
    refine ⟨e, normalize e (Or.inl ?_)⟩
    simpa [relabel, he0, e] using hi
  · let f : Fin 3 → Label := ![0, 1, 2]
    let g : Fin 3 → Label := ![0, i, j]
    have hf : Function.Injective f := by decide +kernel
    have hg : Function.Injective g := by
      simp [Function.Injective, Fin.forall_fin_succ, g,
        hi0, hj0, hij, hi0.symm, hj0.symm, hij.symm]
    obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair f g hf hg
    have he0 : e 0 = 0 := he 0
    have he1 : e 1 = i := he 1
    have he2 : e 2 = j := he 2
    refine ⟨e, normalize e (Or.inr ?_)⟩
    simpa [relabel, he0, he1, he2] using And.intro hi hj

end MacMahon
