/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the diagonal design on a *rectangular* grid of sub-blocks

`Nibble.AX1.gridDesign_pairwise_edgeDisjoint` (`Nibble.GridDesign`) proves edge-disjointness of the
diagonal family of sub-triples when all three clusters are split into the *same* number `n` of
blocks.  The construction the residual actually needs is rectangular: in a triple of clusters with
densities `p ≥ q ≥ r` the block **sizes** must be proportional to the opposite densities, so the
block **counts** `nA, nB, nC` differ, with `nB, nC ≤ nA`.

This file

* isolates the general principle — `Nibble.AX1.tripleFamily_pairwise_edgeDisjoint`: a family of
  sub-triples indexed by three block-index functions is edge-disjoint as soon as each *pair* of
  index functions is jointly injective;
* records the rectangular diagonal indices `Nibble.AX1.rectIdxA`, `Nibble.AX1.rectIdxB`,
  `Nibble.AX1.rectIdxC` (`i ↦ ((i / nC + i % nC) % nA, i / nC, i % nC)`, `i < nB * nC`) and their
  pairwise injectivity, and
* deduces `Nibble.AX1.rectDesign_pairwise_edgeDisjoint`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.GridDesign

/-! # GridDesignRect -/

@[expose] public section

open Finset SimpleGraph

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### The general principle -/

omit [Fintype V] [DecidableEq V] in
/-- **A family of sub-triples with pairwise jointly injective index functions is edge-disjoint.**

`IA i`, `IB i`, `IC i` are the indices of the three blocks of the `i`-th sub-triple.  A common edge
of two members determines which *pair* of clusters carries it, and — the blocks of a cluster being
pairwise disjoint and blocks of different clusters being disjoint — the two indices of that pair;
joint injectivity of that pair of index functions then forces the two members to coincide. -/
theorem tripleFamily_pairwise_edgeDisjoint (G : SimpleGraph V) {nA nB nC k : ℕ}
    (Ub Wb Xb : ℕ → Finset V) (IA IB IC : ℕ → ℕ)
    (hIA : ∀ i < k, IA i < nA) (hIB : ∀ i < k, IB i < nB) (hIC : ∀ i < k, IC i < nC)
    (hUU : ∀ a < nA, ∀ b < nA, a ≠ b → Disjoint (Ub a) (Ub b))
    (hWW : ∀ a < nB, ∀ b < nB, a ≠ b → Disjoint (Wb a) (Wb b))
    (hXX : ∀ a < nC, ∀ b < nC, a ≠ b → Disjoint (Xb a) (Xb b))
    (hUW : ∀ a < nA, ∀ b < nB, Disjoint (Ub a) (Wb b))
    (hUX : ∀ a < nA, ∀ b < nC, Disjoint (Ub a) (Xb b))
    (hWX : ∀ a < nB, ∀ b < nC, Disjoint (Wb a) (Xb b))
    (hABinj : ∀ i < k, ∀ i' < k, IA i = IA i' → IB i = IB i' → i = i')
    (hACinj : ∀ i < k, ∀ i' < k, IA i = IA i' → IC i = IC i' → i = i')
    (hBCinj : ∀ i < k, ∀ i' < k, IB i = IB i' → IC i = IC i' → i = i')
    {i : ℕ} (hi : i < k) {i' : ℕ} (hi' : i' < k) (hne : i ≠ i') (x y : V)
    (h : (tripleGraph G (Ub (IA i)) (Wb (IB i)) (Xb (IC i))).Adj x y) :
    ¬ (tripleGraph G (Ub (IA i')) (Wb (IB i')) (Xb (IC i'))).Adj x y := by
  intro h'
  set a := IA i with ha
  set b := IB i with hb
  set c := IC i with hc
  set a' := IA i' with ha'
  set b' := IB i' with hb'
  set c' := IC i' with hc'
  have hai : a < nA := hIA i hi
  have hbi : b < nB := hIB i hi
  have hci : c < nC := hIC i hi
  have hai' : a' < nA := hIA i' hi'
  have hbi' : b' < nB := hIB i' hi'
  have hci' : c' < nC := hIC i' hi'
  have hcross : pairIn (Ub a) (Wb b) x y ∨ pairIn (Ub a) (Xb c) x y ∨ pairIn (Wb b) (Xb c) x y :=
    crossAdj_iff_pairIn.mp h.2
  have hcross' : pairIn (Ub a') (Wb b') x y ∨ pairIn (Ub a') (Xb c') x y
      ∨ pairIn (Wb b') (Xb c') x y := crossAdj_iff_pairIn.mp h'.2
  have hUeq : ∀ p q, p < nA → q < nA → ¬ Disjoint (Ub p) (Ub q) → p = q := by
    intro p q hp hq hd; by_contra hpq; exact hd (hUU p hp q hq hpq)
  have hWeq : ∀ p q, p < nB → q < nB → ¬ Disjoint (Wb p) (Wb q) → p = q := by
    intro p q hp hq hd; by_contra hpq; exact hd (hWW p hp q hq hpq)
  have hXeq : ∀ p q, p < nC → q < nC → ¬ Disjoint (Xb p) (Xb q) → p = q := by
    intro p q hp hq hd; by_contra hpq; exact hd (hXX p hp q hq hpq)
  refine hne ?_
  rcases hcross with hUW1 | hUX1 | hWX1
  · rcases hcross' with hUW2 | hUX2 | hWX2
    · obtain ⟨h1, h2⟩ := pairIn_match hUW1 hUW2 (hUW a hai b' hbi')
        (Disjoint.symm (hUW a' hai' b hbi))
      exact hABinj i hi i' hi' (hUeq a a' hai hai' h1) (hWeq b b' hbi hbi' h2)
    · exact absurd (pairIn_absurd (pairIn_symm hUW1) hUX2
        (Disjoint.symm (hUW a' hai' b hbi)) (hWX b hbi c' hci')) not_false
    · exact absurd (pairIn_absurd hUW1 hWX2 (hUW a hai b' hbi') (hUX a hai c' hci')) not_false
  · rcases hcross' with hUW2 | hUX2 | hWX2
    · exact absurd (pairIn_absurd (pairIn_symm hUX1) hUW2
        (Disjoint.symm (hUX a' hai' c hci)) (Disjoint.symm (hWX b' hbi' c hci))) not_false
    · obtain ⟨h1, h2⟩ := pairIn_match hUX1 hUX2 (hUX a hai c' hci')
        (Disjoint.symm (hUX a' hai' c hci))
      exact hACinj i hi i' hi' (hUeq a a' hai hai' h1) (hXeq c c' hci hci' h2)
    · exact absurd (pairIn_absurd hUX1 hWX2 (hUW a hai b' hbi') (hUX a hai c' hci')) not_false
  · rcases hcross' with hUW2 | hUX2 | hWX2
    · exact absurd (pairIn_absurd (pairIn_symm hWX1) hUW2
        (Disjoint.symm (hUX a' hai' c hci)) (Disjoint.symm (hWX b' hbi' c hci))) not_false
    · exact absurd (pairIn_absurd hUX2 hWX1 (hUW a' hai' b hbi) (hUX a' hai' c hci)) not_false
    · obtain ⟨h1, h2⟩ := pairIn_match hWX1 hWX2 (hWX b hbi c' hci')
        (Disjoint.symm (hWX b' hbi' c hci))
      exact hBCinj i hi i' hi' (hWeq b b' hbi hbi' h1) (hXeq c c' hci hci' h2)

/-! ### The rectangular diagonal indices -/

/-- The `U`-block index of the `i`-th member of the rectangular diagonal design. -/
def rectIdxA (nA nC i : ℕ) : ℕ := (i / nC + i % nC) % nA

/-- The `W`-block index of the `i`-th member of the rectangular diagonal design. -/
def rectIdxB (nC i : ℕ) : ℕ := i / nC

/-- The `X`-block index of the `i`-th member of the rectangular diagonal design. -/
def rectIdxC (nC i : ℕ) : ℕ := i % nC

theorem rectIdxA_lt {nA nC : ℕ} (hnA : 0 < nA) (i : ℕ) : rectIdxA nA nC i < nA :=
  Nat.mod_lt _ hnA

theorem rectIdxB_lt {nB nC i : ℕ} (hi : i < nB * nC) : rectIdxB nC i < nB := by
  have hnC : 0 < nC := by
    rcases Nat.eq_zero_or_pos nC with rfl | h
    · simp at hi
    · exact h
  exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi)

theorem rectIdxC_lt {nC : ℕ} (hnC : 0 < nC) (i : ℕ) : rectIdxC nC i < nC :=
  Nat.mod_lt _ hnC

/-- **The `U`–`W` block pair is used at most once** — provided there are at least as many `U`-blocks
as `X`-blocks. -/
theorem rectIdx_AB_inj {nA nB nC i i' : ℕ} (hCA : nC ≤ nA) (hi : i < nB * nC) (hi' : i' < nB * nC)
    (hA : rectIdxA nA nC i = rectIdxA nA nC i') (hB : rectIdxB nC i = rectIdxB nC i') : i = i' := by
  have hnC : 0 < nC := by
    rcases Nat.eq_zero_or_pos nC with rfl | h
    · simp at hi
    · exact h
  have hnA : 0 < nA := lt_of_lt_of_le hnC hCA
  refine eq_of_div_mod_eq hB ?_
  simp only [rectIdxA, rectIdxB] at hA hB
  rw [hB] at hA
  have h1 : (i' / nC + i % nC) % nA = (i' / nC + i' % nC) % nA := hA
  have hr : i % nC < nA := lt_of_lt_of_le (Nat.mod_lt _ hnC) hCA
  have hr' : i' % nC < nA := lt_of_lt_of_le (Nat.mod_lt _ hnC) hCA
  have h2 : (i % nC) % nA = (i' % nC) % nA :=
    Nat.ModEq.add_left_cancel' (i' / nC) (by simpa [Nat.ModEq] using h1)
  rwa [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr'] at h2

/-- **The `U`–`X` block pair is used at most once** — provided there are at least as many `U`-blocks
as `W`-blocks. -/
theorem rectIdx_AC_inj {nA nB nC i i' : ℕ} (hBA : nB ≤ nA) (hi : i < nB * nC) (hi' : i' < nB * nC)
    (hA : rectIdxA nA nC i = rectIdxA nA nC i') (hC : rectIdxC nC i = rectIdxC nC i') : i = i' := by
  have hnC : 0 < nC := by
    rcases Nat.eq_zero_or_pos nC with rfl | h
    · simp at hi
    · exact h
  have hnB : 0 < nB := by
    rcases Nat.eq_zero_or_pos nB with rfl | h
    · simp at hi
    · exact h
  have hnA : 0 < nA := lt_of_lt_of_le hnB hBA
  refine eq_of_div_mod_eq ?_ hC
  simp only [rectIdxA, rectIdxC] at hA hC
  rw [hC] at hA
  have h1 : (i' % nC + i / nC) % nA = (i' % nC + i' / nC) % nA := by
    rw [Nat.add_comm (i' % nC) (i / nC), Nat.add_comm (i' % nC) (i' / nC)]; exact hA
  have h2 : (i / nC) % nA = (i' / nC) % nA :=
    Nat.ModEq.add_left_cancel' (i' % nC) (by simpa [Nat.ModEq] using h1)
  have hdi : i / nC < nA := lt_of_lt_of_le (rectIdxB_lt hi) hBA
  have hdi' : i' / nC < nA := lt_of_lt_of_le (rectIdxB_lt hi') hBA
  rwa [Nat.mod_eq_of_lt hdi, Nat.mod_eq_of_lt hdi'] at h2

/-- **The `W`–`X` block pair is used at most once.** -/
theorem rectIdx_BC_inj {nC i i' : ℕ}
    (hB : rectIdxB nC i = rectIdxB nC i') (hC : rectIdxC nC i = rectIdxC nC i') : i = i' :=
  eq_of_div_mod_eq hB hC

/-! ### The rectangular design -/

omit [Fintype V] [DecidableEq V] in
/-- **The rectangular diagonal design is edge-disjoint.**  The clusters `U`, `W`, `X` are split into
`nA`, `nB`, `nC` pairwise disjoint blocks with `nB, nC ≤ nA`, and the `nB · nC` sub-triples
`(U_{(j+k) mod nA}, W_j, X_k)` have pairwise no common edge. -/
theorem rectDesign_pairwise_edgeDisjoint (G : SimpleGraph V) {nA nB nC : ℕ}
    (Ub Wb Xb : ℕ → Finset V) (hBA : nB ≤ nA) (hCA : nC ≤ nA)
    (hUU : ∀ a < nA, ∀ b < nA, a ≠ b → Disjoint (Ub a) (Ub b))
    (hWW : ∀ a < nB, ∀ b < nB, a ≠ b → Disjoint (Wb a) (Wb b))
    (hXX : ∀ a < nC, ∀ b < nC, a ≠ b → Disjoint (Xb a) (Xb b))
    (hUW : ∀ a < nA, ∀ b < nB, Disjoint (Ub a) (Wb b))
    (hUX : ∀ a < nA, ∀ b < nC, Disjoint (Ub a) (Xb b))
    (hWX : ∀ a < nB, ∀ b < nC, Disjoint (Wb a) (Xb b))
    {i : ℕ} (hi : i < nB * nC) {i' : ℕ} (hi' : i' < nB * nC) (hne : i ≠ i') (x y : V)
    (h : (tripleGraph G (Ub (rectIdxA nA nC i)) (Wb (rectIdxB nC i))
      (Xb (rectIdxC nC i))).Adj x y) :
    ¬ (tripleGraph G (Ub (rectIdxA nA nC i')) (Wb (rectIdxB nC i'))
        (Xb (rectIdxC nC i'))).Adj x y := by
  have hnC : 0 < nC := by
    rcases Nat.eq_zero_or_pos nC with rfl | hpos
    · simp at hi
    · exact hpos
  have hnA : 0 < nA := lt_of_lt_of_le hnC hCA
  refine tripleFamily_pairwise_edgeDisjoint (nA := nA) (nB := nB) (nC := nC) (k := nB * nC)
    G Ub Wb Xb _ _ _ (fun j _ => rectIdxA_lt hnA j) (fun j hj => rectIdxB_lt hj)
    (fun j _ => rectIdxC_lt hnC j) hUU hWW hXX hUW hUX hWX
    (fun p hp p' hp' h1 h2 => rectIdx_AB_inj hCA hp hp' h1 h2)
    (fun p hp p' hp' h1 h2 => rectIdx_AC_inj hBA hp hp' h1 h2)
    (fun p _ p' _ h1 h2 => rectIdx_BC_inj h1 h2) hi hi' hne x y h

end Nibble.AX1
