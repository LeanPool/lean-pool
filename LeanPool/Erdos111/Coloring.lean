/-
Copyright (c) 2026 Jacob Parish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Parish
-/

module

public import LeanPool.Erdos111.Greedy
public import LeanPool.Erdos111.HilbertClasses
public import LeanPool.Erdos111.LimitMeasure

/-!
# Countable colorings of linear graphs

**Theorem.** For every `C`, every `C`-linear graph has a proper coloring by `ℕ`.

*Proof.* Induct on `#V`; countable graphs are colored injectively. For uncountable `V`,
take a chain. Each layer has fewer than `#V` vertices and induces a `C`-linear graph, so
it is countably colorable by induction. Proposition L gives a law under which every
vertex with infinite trace has trace energy at most `C`, and Proposition C splits the
vertices into countably many classes within which any two signs agree with probability at
least `η > 0`. Within a class, a vertex has only finitely many neighbours in earlier
layers: they lie in its trace, which is finite or has energy at most `C`. Greedy coloring
along the layers colors the edges between layers inside each class. The class, the
greedy color and the color within the layer together color `G`.
-/

@[expose] public section

open Cardinal
open scoped NNReal

universe u

namespace Erdos111

variable {V : Type u}

/-- Induced subgraphs of a `C`-linear graph are `C`-linear. -/
theorem Linear.induce {G : SimpleGraph V} {C : ℝ≥0} (hG : Linear G C) (s : Set V) :
    Linear (G.induce s) C := by
  classical
  intro t E hE hEt
  set f : Sym2 s ↪ Sym2 V := (Function.Embedding.subtype (· ∈ s)).sym2Map
  have hmono : ∀ τ : V → Bool, monoCount (E.map f) τ = monoCount E (τ ∘ Subtype.val) := by
    intro τ
    unfold monoCount
    rw [Finset.filter_map, Finset.card_map]
    congr 1
    refine Finset.filter_congr fun e _ => ?_
    induction e using Sym2.ind with
    | _ a b => simp [f, mono]
  have hcost : edgeCost E ≤ edgeCost (E.map f) :=
    le_ciInf fun τ => (hmono τ).symm ▸ ciInf_le (OrderBot.bddBelow _) _
  have hmap := hG (t.map (Function.Embedding.subtype (· ∈ s))) (E.map f) ?_ ?_
  · rw [Finset.card_map] at hmap
    exact le_trans (by exact_mod_cast hcost) hmap
  · intro e he
    obtain ⟨e, he', rfl⟩ := Finset.mem_map.1 he
    have := hE he'
    induction e using Sym2.ind with
    | _ a b => simpa [f] using this
  · intro e he v hv
    obtain ⟨e, he', rfl⟩ := Finset.mem_map.1 he
    obtain ⟨w, hw, rfl⟩ := Sym2.mem_map.1 hv
    exact Finset.mem_map_of_mem _ (hEt e he' w hw)

/-- Lemma T: the trace bounds of one law and countable colorings of the layers give a
countable coloring. -/
theorem nonempty_coloring_of_traceBound {G : SimpleGraph V} {C : ℝ≥0} (c : Chain G)
    {ν : MeasureTheory.Measure (V → Bool)} [MeasureTheory.IsProbabilityMeasure ν]
    (hν : ∀ v, (c.trace v).Infinite → TraceBound C ν v (c.trace v))
    (hlayer : ∀ ξ, Nonempty ((G.induce {v | c.layer v = ξ}).Coloring ℕ)) :
    Nonempty (G.Coloring ℕ) := by
  classical
  obtain ⟨cls, η, hη, hcls⟩ := exists_sign_classes ν
  -- The edges between layers inside each class.
  let H : SimpleGraph V :=
    { Adj := fun u v => G.Adj u v ∧ cls u = cls v ∧ c.layer u ≠ c.layer v
      symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩⟩
      loopless := ⟨fun _ h => h.2.2 rfl⟩ }
  have hfin : ∀ v, {u | c.layer u < c.layer v ∧ H.Adj u v}.Finite := by
    intro v
    have hsub : {u | c.layer u < c.layer v ∧ H.Adj u v} ⊆
        {u | u ∈ c.trace v ∧ cls u = cls v} :=
      fun u hu => ⟨c.mem_trace_of_layer_lt hu.2.1.symm hu.1, hu.2.2.1⟩
    refine Set.Finite.subset ?_ hsub
    by_cases ht : (c.trace v).Finite
    · exact ht.subset fun u hu => hu.1
    by_contra hT
    obtain ⟨n, hn⟩ := exists_nat_gt (C / η (cls v))
    have hCn : C < n * η (cls v) := (div_lt_iff₀ (hη _)).1 hn
    obtain ⟨B, hB, hBn⟩ := Set.Infinite.exists_subset_card_eq hT n
    have hsum := hν v ht B fun u hu => (hB hu).1
    have hle : B.card • (η (cls v) : ENNReal) ≤ ∑ u ∈ B, ν {ω | ω u = ω v} :=
      Finset.card_nsmul_le_sum _ _ _ fun u hu => (hB hu).2 ▸ hcls u v (hB hu).2
    rw [hBn, nsmul_eq_mul] at hle
    have : ((n * η (cls v) : ℝ≥0) : ENNReal) ≤ C := by
      push_cast
      exact hle.trans hsum
    exact absurd (ENNReal.coe_le_coe.1 this) (not_le.2 hCn)
  obtain ⟨hg⟩ := nonempty_coloring_of_wellFounded H (r := fun u v => c.layer u < c.layer v)
    (InvImage.wf c.layer wellFounded_lt) (fun u v h => lt_or_gt_of_ne h.2.2) hfin
  -- The color of each vertex within its layer.
  have hcol : ∀ {u v} (ξ : Ordinal.{u}) (hu : c.layer u = ξ) (hv : c.layer v = ξ),
      G.Adj u v → (hlayer ξ).some ⟨u, hu⟩ ≠ (hlayer ξ).some ⟨v, hv⟩ :=
    fun ξ hu hv h => (hlayer ξ).some.valid (SimpleGraph.induce_adj.2 h)
  have heq : ∀ {u} (ξ : Ordinal.{u}) (hu : c.layer u = ξ),
      (hlayer (c.layer u)).some ⟨u, rfl⟩ = (hlayer ξ).some ⟨u, hu⟩ := by
    intro u ξ hu
    subst hu
    rfl
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => Nat.pair (cls v) (Nat.pair (hg v) ((hlayer (c.layer v)).some ⟨v, rfl⟩))) ?_⟩
  intro u v h huv
  simp only [Nat.pair_eq_pair] at huv
  obtain ⟨hc, hgc, hl⟩ := huv
  by_cases hξ : c.layer u = c.layer v
  · rw [heq (c.layer v) hξ] at hl
    exact hcol (c.layer v) hξ rfl h hl
  · exact hg.valid (show H.Adj u v from ⟨h, hc, hξ⟩) hgc

/-- Every `C`-linear graph has a proper coloring by `ℕ`. -/
theorem nonempty_coloring_of_linear (G : SimpleGraph V) {C : ℝ≥0} (hG : Linear G C) :
    Nonempty (G.Coloring ℕ) := by
  suffices h : ∀ κ : Cardinal.{u}, ∀ (W : Type u) (H : SimpleGraph W), #W = κ → Linear H C →
      Nonempty (H.Coloring ℕ) from h _ V G rfl hG
  intro κ
  induction κ using Cardinal.lt_wf.induction with
  | _ κ ih =>
  intro W H hW hH
  rcases le_or_gt #W ℵ₀ with hc | hc
  · -- Countable graphs are colored injectively.
    have : Countable W := Cardinal.mk_le_aleph0_iff.1 hc
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat W
    exact ⟨SimpleGraph.Coloring.mk f fun h heq => H.ne_of_adj h (hf heq)⟩
  · obtain ⟨c⟩ := exists_chain H hc
    obtain ⟨ν, hν, htr⟩ := exists_traceBound_law hH c
    refine nonempty_coloring_of_traceBound c htr fun ξ => ?_
    exact ih _ (hW ▸ c.card_layer_lt hc.le ξ) _ (H.induce {v | c.layer v = ξ}) rfl (hH.induce _)

end Erdos111
