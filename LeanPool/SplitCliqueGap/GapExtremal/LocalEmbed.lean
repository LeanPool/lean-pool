/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.Global
public import LeanPool.SplitCliqueGap.GapExtremal.LocalH12
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

/-!
# The local lemma on a block (ledger §6 → §7)

A block `ℓ` whose points carry injective colours `f : V → F`, with `B`-edges inside `ℓ` only
between colours
`σ i, σ j` with `ij ∈ H12` (`σ : Fin 6 ↪ F`; the other colours are isolated), satisfies the
hypothesis of
`global_bound` with `c = 8`:

  `∑_{Q ∈ T} (4 w(Q) - e(Q)) ≤ 32 - e(ℓ)`   for packings `T` inside `ℓ`.
-/

@[expose] public section

namespace GapExtremal

open Finset

namespace H12

/-- `H12` as a simple graph on `Fin 6`. -/
def graph : SimpleGraph (Fin 6) where
  Adj i j := adj i j = true ∨ adj j i = true
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel graph.Adj := fun i j =>
  inferInstanceAs (Decidable (adj i j = true ∨ adj j i = true))

theorem e_graph_eq : ∀ Q : Finset (Fin 6), e graph Q = eH Q := by decide +kernel

end H12

variable {V : Type*} [Fintype V] [DecidableEq V] {B : SimpleGraph V} [DecidableRel B.Adj]

/-- Transport of edge counts along a map injective on the column. -/
theorem e_le_e_image {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel
  H.Adj]
    (g : V → W) {Q : Finset V} (hg : Set.InjOn g Q)
    (hadj : ∀ u ∈ Q, ∀ v ∈ Q, B.Adj u v → H.Adj (g u) (g v)) : e B Q ≤ e H (Q.image g) := by
  unfold e
  refine Finset.card_le_card_of_injOn (Sym2.map g) ?_ ?_
  · intro s hs
    induction s using Sym2.ind with
    | h u v =>
      rw [Finset.mem_coe, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hs
      rw [Sym2.map_mk, Finset.mem_coe, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact ⟨hadj u hs.2.1 v hs.2.2 hs.1, Finset.mem_image_of_mem g hs.2.1,
        Finset.mem_image_of_mem g hs.2.2⟩
  · intro s hs t ht hst
    induction s using Sym2.ind with
    | h a b =>
    induction t using Sym2.ind with
    | h c d =>
      rw [Finset.mem_coe, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hs ht
      simp only [Sym2.map_mk, Sym2.eq_iff] at hst
      rw [Sym2.eq_iff]
      rcases hst with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨hg hs.2.1 ht.2.1 h1, hg hs.2.2 ht.2.2 h2⟩
      · exact Or.inr ⟨hg hs.2.1 ht.2.2 h1, hg hs.2.2 ht.2.1 h2⟩

/-- **Local lemma on a coloured block.** -/
theorem block_local {F : Type*} (f : V → F) (σ : Fin 6 ↪ F) {ℓ : Finset V}
    (hf : Set.InjOn f ℓ)
    (hadj : ∀ u ∈ ℓ, ∀ v ∈ ℓ, B.Adj u v → ∃ i j, σ i = f u ∧ σ j = f v ∧ H12.graph.Adj i j)
    (T : Finset (Finset V)) (hTsub : ∀ Q ∈ T, Q ⊆ ℓ) (hT : IsPack T) :
    ∑ Q ∈ T, (4 * w B Q - e B Q) ≤ 32 - e B ℓ := by
  classical
  -- the colour index map, defined on active points
  let g : V → Fin 6 := fun u => Function.invFun σ (f u)
  let act : Finset V → Finset V := fun Q => Q.filter (fun u => ∃ i, σ i = f u)
  have hg_spec : ∀ u, (∃ i, σ i = f u) → σ (g u) = f u := fun u h => Function.invFun_eq h
  have hinj : ∀ Q ⊆ ℓ, Set.InjOn g (act Q) := by
    intro Q hQ u hu v hv huv
    have hu' := (Finset.mem_filter.mp hu)
    have hv' := (Finset.mem_filter.mp hv)
    apply hf (hQ hu'.1) (hQ hv'.1)
    rw [← hg_spec u hu'.2, ← hg_spec v hv'.2]
    exact congrArg σ huv
  -- edges of `Q` live on active points and inject into `H12`
  have he : ∀ Q ⊆ ℓ, e B Q ≤ H12.eH ((act Q).image g) := by
    intro Q hQ
    have h1 : e B Q ≤ e B (act Q) := by
      unfold e
      refine Finset.card_le_card fun s hs => ?_
      induction s using Sym2.ind with
      | h u v =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hs ⊢
        obtain ⟨i, j, hi, hj, -⟩ := hadj u (hQ hs.2.1) v (hQ hs.2.2) hs.1
        exact ⟨hs.1, Finset.mem_filter.mpr ⟨hs.2.1, i, hi⟩, Finset.mem_filter.mpr ⟨hs.2.2, j, hj⟩⟩
    have h2 : e B (act Q) ≤ e H12.graph ((act Q).image g) := by
      refine e_le_e_image H12.graph g (hinj Q hQ) fun u hu v hv huv => ?_
      have hu' := Finset.mem_filter.mp hu
      have hv' := Finset.mem_filter.mp hv
      obtain ⟨i, j, hi, hj, hij⟩ := hadj u (hQ hu'.1) v (hQ hv'.1) huv
      have : g u = i := σ.injective (by rw [hg_spec u hu'.2, hi])
      have : g v = j := σ.injective (by rw [hg_spec v hv'.2, hj])
      simp [*]
    rw [← H12.e_graph_eq]
    exact h1.trans h2
  have hcardQ : ∀ Q, ((act Q).image g).card ≤ Q.card :=
    fun Q => Finset.card_image_le.trans (Finset.card_filter_le _ _)
  -- pointwise comparison with the `Fin 6` objective
  have hpt : ∀ Q ⊆ ℓ, 4 * w B Q - e B Q ≤ H12.f ((act Q).image g) := by
    intro Q hQ
    have h1 := he Q hQ
    have h2 := hcardQ Q
    have hc : (((act Q).image g).card.choose 2 : ℤ) ≤ (Q.card.choose 2 : ℤ) := by
      exact_mod_cast Nat.choose_le_choose 2 h2
    unfold w H12.f
    have h1' : (e B Q : ℤ) ≤ H12.eH ((act Q).image g) := by exact_mod_cast h1
    linarith
  -- images of distinct pieces share at most one colour
  have hcompat : ∀ Q ∈ T, ∀ Q' ∈ T, Q ≠ Q' →
      (((act Q).image g) ∩ ((act Q').image g)).card ≤ 1 := by
    intro Q hQ Q' hQ' hne
    have hsub : act Q ∪ act Q' ⊆ act ℓ := Finset.union_subset
      (Finset.filter_subset_filter _ (hTsub Q hQ)) (Finset.filter_subset_filter _ (hTsub Q' hQ'))
    rw [← Finset.image_inter_of_injOn]
    · refine Finset.card_image_le.trans ((Finset.card_le_card ?_).trans (hT Q hQ Q' hQ' hne))
      exact Finset.inter_subset_inter (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    · exact (hinj ℓ subset_rfl).mono (by exact_mod_cast hsub)
  -- reduce to the positive pieces, which have distinct images
  set T' := T.filter (fun Q => 0 < H12.f ((act Q).image g)) with hT'
  have hstep1 : ∑ Q ∈ T, (4 * w B Q - e B Q) ≤ ∑ Q ∈ T', H12.f ((act Q).image g) := by
    refine (Finset.sum_le_sum fun Q hQ => hpt Q (hTsub Q hQ)).trans ?_
    rw [hT', Finset.sum_filter]
    exact Finset.sum_le_sum fun Q _ => by split_ifs with h <;> [exact le_rfl; exact not_lt.mp h]
  have himg : Set.InjOn (fun Q => (act Q).image g) (T' : Set (Finset V)) := by
    intro Q hQ Q' hQ' heq
    by_contra hne
    have hQT := (Finset.mem_filter.mp hQ)
    have hQT' := (Finset.mem_filter.mp hQ')
    have h3 := H12.three_le_card_of_pos _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQT.2⟩)
    have h1 := hcompat Q hQT.1 Q' hQT'.1 hne
    simp only at heq
    rw [heq, Finset.inter_self] at h1
    rw [heq] at h3
    omega
  rw [← Finset.sum_image himg] at hstep1
  have hfin := H12.local_bound (T'.image fun Q => (act Q).image g) (by
    intro P hP P' hP' hne
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hP'
    exact hcompat Q (Finset.mem_filter.mp hQ).1 Q' (Finset.mem_filter.mp hQ').1
      (fun h => hne (by rw [h])))
  have heℓ : (e B ℓ : ℤ) ≤ 12 := by
    have := he ℓ subset_rfl
    have h12 : ∀ P : Finset (Fin 6), H12.eH P ≤ 12 := by decide +kernel
    exact_mod_cast this.trans (h12 _)
  linarith

end GapExtremal
