/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — assembling the block family from a coarse-cell placement

This file turns a *placement* — the output of `Nibble.AX1.BoxAllocationResidual`, i.e. a set of
coarse cells per copy and per cluster, three-way coherent and pairwise disjoint in every cluster
pair — into the family of block sub-triples that `Nibble.AX1.BlockCoverResidualCoupled` asks for.

* `Nibble.AX1.exists_gridSubTriple_family_of_placement` — the family, its two clauses
  (`IsGridSubTriple` and pairwise disjoint vertex-pair rectangles) and the identity between its
  covering value and the total value of the placed copies.

Nothing quantitative happens here: the sizes, the densities and the accuracy are inputs.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoarseCellBlocks
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapBlockShape
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapClusterHost
public import Mathlib.Data.List.GetD

/-! # CoarseCellAssembly -/

@[expose] public section

open Finset SimpleGraph

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The block family of a coarse-cell placement.**  Every copy of `Good` becomes a member of the
family: its block at the position `a` is the prescribed number `bs c a` of vertices inside the union
of the coarse cells `I c a` of its cluster `cl c a`. -/
theorem exists_gridSubTriple_family_of_placement
    (G : SimpleGraph V) [DecidableRel G.Adj] (Pp : Finpartition (univ : Finset V))
    {ep de α τ : ℝ} {l Pn : ℕ} (hl : 0 < l)
    {κ : Type}
    (cl : κ → ZMod 3 → {S : Finset V // S ∈ Pp.parts})
    (sz bs : κ → ZMod 3 → ℕ) (I : κ → ZMod 3 → Finset (Fin Pn)) (Good : Finset κ)
    (hcard : ∀ c a, #(I c a) = sz c a)
    (hfitS : ∀ S ∈ Pp.parts, Pn * l ≤ #S)
    (hbs : ∀ c a, bs c a ≤ sz c a * l)
    (hdisjI : ∀ c ∈ Good, ∀ c' ∈ Good, c ≠ c' → ∀ a b a' b' : ZMod 3, a ≠ b → a' ≠ b' →
      cl c a = cl c' a' → cl c b = cl c' b' →
      Disjoint (I c a) (I c' a') ∨ Disjoint (I c b) (I c' b'))
    (hgood : ∀ c ∈ Good,
      GoodTriple G Pp ep de (cl c 0 : Finset V) (cl c 1 : Finset V) (cl c 2 : Finset V))
    (hrel : ∀ c ∈ Good, ∀ a : ZMod 3, α * (#(cl c a : Finset V) : ℝ) ≤ (bs c a : ℝ))
    (hshape : ∀ c ∈ Good, ∀ a : ZMod 3,
      |(bs c a : ℝ)
        - τ * (G.edgeDensity (cl c (a + 1) : Finset V) (cl c (a + 2) : Finset V) : ℝ)| ≤ 1) :
    ∃ (k : ℕ) (U W X A B C : ℕ → Finset V),
      k ≤ #Good ∧
      (∀ i < k, IsGridSubTriple G Pp ep de α τ (U i) (W i) (X i) (A i) (B i) (C i)) ∧
      (∀ i < k, ∀ j < k, i ≠ j →
        Disjoint (tripleRect (A i) (B i) (C i)) (tripleRect (A j) (B j) (C j))) ∧
      (∑ i ∈ Finset.range k, τ ^ 2 * ((G.edgeDensity (U i) (W i) : ℝ)
          * (G.edgeDensity (U i) (X i) : ℝ) * (G.edgeDensity (W i) (X i) : ℝ)))
        = ∑ c ∈ Good, τ ^ 2 * ((G.edgeDensity (cl c 0 : Finset V) (cl c 1 : Finset V) : ℝ)
            * (G.edgeDensity (cl c 0 : Finset V) (cl c 2 : Finset V) : ℝ)
            * (G.edgeDensity (cl c 1 : Finset V) (cl c 2 : Finset V) : ℝ)) := by
  classical
  -- the block of the copy `c` at the position `a`
  set blk : κ → ZMod 3 → Finset V :=
    fun c a => cellBlock (cl c a : Finset V) l (I c a) (bs c a) with hblkdef
  have hblksub : ∀ c a, blk c a ⊆ (cl c a : Finset V) := fun c a => cellBlock_subset _ _ _ _
  have hblkcard : ∀ c a, #(blk c a) = bs c a := by
    intro c a
    refine card_cellBlock _ hl _ (hfitS _ (cl c a).2) ?_
    rw [hcard]
    exact hbs c a
  -- two placed copies have disjoint vertex-pair rectangles
  have hrect : ∀ c ∈ Good, ∀ c' ∈ Good, c ≠ c' →
      Disjoint (tripleRect (blk c 0) (blk c 1) (blk c 2))
        (tripleRect (blk c' 0) (blk c' 1) (blk c' 2)) := by
    intro c hc c' hc' hne
    refine tripleRect_disjoint_of_shared_pairs
      (clA := fun a => (cl c a : Finset V)) (clB := fun a => (cl c' a : Finset V))
      (fun a => hblksub c a) (fun a => hblksub c' a) ?_ ?_
    · intro a b v hv hv'
      by_contra hcon
      exact (Finset.disjoint_left.mp (Pp.disjoint (cl c a).2 (cl c' b).2 hcon) hv) hv'
    · intro a b a' b' hab hab' hca hcb
      have hca' : cl c a = cl c' a' := Subtype.ext hca
      have hcb' : cl c b = cl c' b' := Subtype.ext hcb
      rcases hdisjI c hc c' hc' hne a b a' b' hab hab' hca' hcb' with h | h
      · refine Or.inl (Finset.disjoint_of_subset_left (cellBlock_subset_cellUnion _ _ _ _)
          (Finset.disjoint_of_subset_right (cellBlock_subset_cellUnion _ _ _ _) ?_))
        have hEq : (cl c' a' : Finset V) = (cl c a : Finset V) := by rw [hca']
        rw [hEq]
        exact cellUnion_disjoint _ _ h
      · refine Or.inr (Finset.disjoint_of_subset_left (cellBlock_subset_cellUnion _ _ _ _)
          (Finset.disjoint_of_subset_right (cellBlock_subset_cellUnion _ _ _ _) ?_))
        have hEq : (cl c' b' : Finset V) = (cl c b : Finset V) := by rw [hcb']
        rw [hEq]
        exact cellUnion_disjoint _ _ h
  -- the shape of one member
  have hmem : ∀ c ∈ Good, IsGridSubTriple G Pp ep de α τ
      (cl c 0 : Finset V) (cl c 1 : Finset V) (cl c 2 : Finset V)
      (blk c 0) (blk c 1) (blk c 2) := by
    intro c hc
    have h0 := hshape c hc 0
    have h1 := hshape c hc 1
    have h2 := hshape c hc 2
    have e0 : ((0 : ZMod 3) + 1) = 1 := by decide +kernel
    have e0' : ((0 : ZMod 3) + 2) = 2 := by decide +kernel
    have e1 : ((1 : ZMod 3) + 1) = 2 := by decide +kernel
    have e1' : ((1 : ZMod 3) + 2) = 0 := by decide +kernel
    have e2 : ((2 : ZMod 3) + 1) = 0 := by decide +kernel
    have e2' : ((2 : ZMod 3) + 2) = 1 := by decide +kernel
    rw [e0, e0'] at h0
    rw [e1, e1'] at h1
    rw [e2, e2'] at h2
    have hd10 : (G.edgeDensity (cl c 2 : Finset V) (cl c 0 : Finset V) : ℝ)
        = (G.edgeDensity (cl c 0 : Finset V) (cl c 2 : Finset V) : ℝ) := by
      rw [SimpleGraph.edgeDensity_comm]
    have hd20 : (G.edgeDensity (cl c 0 : Finset V) (cl c 1 : Finset V) : ℝ)
        = (G.edgeDensity (cl c 0 : Finset V) (cl c 1 : Finset V) : ℝ) := rfl
    rw [hd10] at h1
    refine ⟨hgood c hc, hblksub c 0, hblksub c 1, hblksub c 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hblkcard]; exact hrel c hc 0
    · rw [hblkcard]; exact hrel c hc 1
    · rw [hblkcard]; exact hrel c hc 2
    · rw [hblkcard]; exact h0
    · rw [hblkcard]; exact h1
    · rw [hblkcard]; rw [hd20] at h2; exact h2
  -- enumerate the placed copies
  rcases Finset.eq_empty_or_nonempty Good with hempty | ⟨c₀, hc₀⟩
  · refine ⟨0, (fun _ => ∅), (fun _ => ∅), (fun _ => ∅), (fun _ => ∅), (fun _ => ∅),
      (fun _ => ∅), Nat.zero_le _, ?_, ?_, ?_⟩
    · intro i hi; omega
    · intro i hi; omega
    · simp [hempty]
  · set L : List κ := Good.toList with hLdef
    set k : ℕ := #Good with hkdef
    have hlen : L.length = k := Finset.length_toList _
    set mem : ℕ → κ := fun i => L.getD i c₀ with hmemdef
    have hmemGood : ∀ i < k, mem i ∈ Good := by
      intro i hi
      rw [hmemdef]
      simp only
      rw [List.getD_eq_getElem L c₀ (by omega : i < L.length)]
      exact Finset.mem_toList.mp (List.getElem_mem _)
    have hmemInj : ∀ i < k, ∀ j < k, i ≠ j → mem i ≠ mem j := by
      intro i hi j hj hij
      rw [hmemdef]
      simp only
      rw [List.getD_eq_getElem L c₀ (by omega : i < L.length),
        List.getD_eq_getElem L c₀ (by omega : j < L.length)]
      intro h
      exact hij ((Finset.nodup_toList Good).getElem_inj_iff.mp h)
    refine ⟨k, fun i => (cl (mem i) 0 : Finset V), fun i => (cl (mem i) 1 : Finset V),
      fun i => (cl (mem i) 2 : Finset V), fun i => blk (mem i) 0, fun i => blk (mem i) 1,
      fun i => blk (mem i) 2, le_of_eq hkdef, ?_, ?_, ?_⟩
    · intro i hi
      exact hmem (mem i) (hmemGood i hi)
    · intro i hi j hj hij
      exact hrect (mem i) (hmemGood i hi) (mem j) (hmemGood j hj) (hmemInj i hi j hj hij)
    · refine Finset.sum_bij (fun i _ => mem i) ?_ ?_ ?_ ?_
      · intro i hi
        exact hmemGood i (Finset.mem_range.mp hi)
      · intro i hi j hj h
        by_contra hij
        exact hmemInj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij h
      · intro c hc
        have hmemL : c ∈ L := Finset.mem_toList.mpr hc
        obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmemL
        refine ⟨i, Finset.mem_range.mpr (by omega), ?_⟩
        rw [hmemdef]
        simp only
        rw [List.getD_eq_getElem L c₀ hi, hget]
      · intro i hi
        rfl

end Nibble.AX1
