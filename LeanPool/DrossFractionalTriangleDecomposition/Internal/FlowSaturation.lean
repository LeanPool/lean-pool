/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.DrossNetwork
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Saturation in Dross's auxiliary network

When a flow meets the network demand, the source and sink arcs of real graph
edges are saturated. This is the accounting step before reconstructing weights.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*} [DecidableEq V]

/-- The four vertices of a four-element set are pairwise distinct. -/
public lemma card4_pairwise {a b c d : V} (h : ({a, b, c, d} : Finset V).card = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have hb3 : ({b, c, d} : Finset V).card ≤ 3 := by
    have h1 := Finset.card_insert_le b ({c, d} : Finset V)
    have h2 := Finset.card_insert_le c ({d} : Finset V)
    simp only [Finset.card_singleton] at h1 h2
    omega
  have ha : a ∉ ({b, c, d} : Finset V) := fun hmem => by
    rw [Finset.card_insert_of_mem hmem] at h
    omega
  have hbcd : ({b, c, d} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem ha] at h
    omega
  have hb : b ∉ ({c, d} : Finset V) := fun hmem => by
    rw [Finset.card_insert_of_mem hmem] at hbcd
    have h2 := Finset.card_insert_le c ({d} : Finset V)
    simp only [Finset.card_singleton] at h2
    omega
  have hcd1 : ({c, d} : Finset V).card = 2 := by
    rw [Finset.card_insert_of_notMem hb] at hbcd
    omega
  have hc : c ≠ d := by
    intro hmem
    rw [hmem] at hcd1
    simp at hcd1
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb
  exact ⟨ha.1, ha.2.1, ha.2.2, hb.1, hb.2, hc⟩

/-- A rooted-K₄ pair on `uv` is exactly a 4-clique on the four endpoints. -/
public theorem k4pair_iff_clique (G : SimpleGraph V) (u v c d : V) :
    K4pair G (s(u, v)) (s(c, d)) ↔ G.IsNClique 4 {u, v, c, d} := by
  constructor
  · rintro ⟨a, b, c', d', hab, hcd, hcard, hclq⟩
    have hset : ({a, b, c', d'} : Finset V) = {u, v, c, d} := by
      rw [Sym2.eq_iff] at hab hcd
      ext x
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto
    rwa [hset] at hclq
  · intro hclq
    exact ⟨u, v, c, d, rfl, rfl, hclq.card_eq, hclq⟩

/-- The rooted-K₄ pair relation is symmetric. -/
public theorem k4pair_symm (G : SimpleGraph V) (e₁ e₂ : Sym2 V) :
    K4pair G e₁ e₂ ↔ K4pair G e₂ e₁ := by
  have hone : ∀ f₁ f₂ : Sym2 V, K4pair G f₁ f₂ → K4pair G f₂ f₁ := by
    rintro f₁ f₂ ⟨a, b, c, d, h1, h2, hcard, hclq⟩
    have hset : ({c, d, a, b} : Finset V) = {a, b, c, d} := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact ⟨c, d, a, b, h2, h1, by rw [hset]; exact hcard, by rw [hset]; exact hclq⟩
  exact ⟨hone e₁ e₂, hone e₂ e₁⟩

/-- A non-edge is in no rooted-K₄ pair. -/
public lemma not_K4pair_of_notMem (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype V] {e : Sym2 V} (he : e ∉ G.edgeFinset) (e' : Sym2 V) :
    ¬ K4pair G e e' := by
  rintro ⟨a, b, c, d, hab, _, hcard, hclq⟩
  apply he
  have hne : a ≠ b := (card4_pairwise hcard).1
  have hadj : G.Adj a b := hclq.1 (by simp) (by simp) hne
  rw [hab, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  exact hadj

/-- At a non-edge node the flow to the sink vanishes. -/
public lemma sinkflow_zero_of_notMem (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ)
    [Fintype V]
    (F : Contrib.MaxFlowMinCut.Flow (drossNet G wΔ)) {e : Sym2 V} (he : e ∉ G.edgeFinset) :
    F.f (Ghat.edge e) Ghat.snk = 0 := by
  have hT0 : triThrough G e = 0 := triThrough_eq_zero_of_notMem G he
  have hk0 : ∀ e' : Sym2 V, F.f (Ghat.edge e) (Ghat.edge e') = 0 := by
    intro e'
    have hle : F.f (Ghat.edge e) (Ghat.edge e') ≤ 0 := by
      have := F.capacitated (Ghat.edge e) (Ghat.edge e')
      simp only [drossNet, dcap, ite_eq_right (not_K4pair_of_notMem G he e')] at this
      exact this
    have hge : F.f (Ghat.edge e') (Ghat.edge e) ≤ 0 := by
      have := F.capacitated (Ghat.edge e') (Ghat.edge e)
      simp only [drossNet, dcap,
        ite_eq_right
          (fun hp => not_K4pair_of_notMem G he e' ((k4pair_symm G e' e).mp hp))] at this
      exact this
    have hsk := F.skew (Ghat.edge e) (Ghat.edge e')
    linarith
  have hsrc0 : F.f (Ghat.edge e) Ghat.src = 0 := by
    have hle : F.f Ghat.src (Ghat.edge e) ≤ 0 := by
      have := F.capacitated Ghat.src (Ghat.edge e)
      simp only [drossNet, dcap, hT0, Nat.cast_zero, zero_mul, zero_sub] at this
      rwa [max_eq_right (by norm_num)] at this
    have hge : F.f (Ghat.edge e) Ghat.src ≤ 0 := F.capacitated (Ghat.edge e) Ghat.src
    have hsk := F.skew Ghat.src (Ghat.edge e)
    linarith
  have hsnkge : 0 ≤ F.f (Ghat.edge e) Ghat.snk := by
    have hge : F.f Ghat.snk (Ghat.edge e) ≤ 0 := F.capacitated Ghat.snk (Ghat.edge e)
    have hsk := F.skew Ghat.snk (Ghat.edge e)
    linarith
  have hcons := F.conserved (Ghat.edge e) (by simp [drossNet]) (by simp [drossNet])
  rw [sum_Ghat (fun v => F.f (Ghat.edge e) v), Finset.sum_eq_zero (fun e' _ => hk0 e'),
    hsrc0, add_zero, zero_add] at hcons
  linarith

/-- If the flow meets the demand, every real-edge sink arc is saturated. -/
public theorem sink_saturated (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ)
    [Fintype V]
    (hbal : ∑ e ∈ G.edgeFinset, ((triThrough G e : ℝ) * wΔ - 1) = 0)
    (F : Contrib.MaxFlowMinCut.Flow (drossNet G wΔ)) (hF : F.value = demand G wΔ) :
    ∀ e ∈ G.edgeFinset,
      F.f (Ghat.edge e) Ghat.snk = max (1 - (triThrough G e : ℝ) * wΔ) 0 := by
  have hle : ∀ e : Sym2 V, F.f (Ghat.edge e) Ghat.snk ≤
      max (1 - (triThrough G e : ℝ) * wΔ) 0 :=
    fun e => F.capacitated (Ghat.edge e) Ghat.snk
  have hcap : ∑ e ∈ G.edgeFinset, max (1 - (triThrough G e : ℝ) * wΔ) 0 =
      demand G wΔ := by
    rw [demand]
    have hpt : ∀ e, max (1 - (triThrough G e : ℝ) * wΔ) 0 =
        max ((triThrough G e : ℝ) * wΔ - 1) 0 +
          (1 - (triThrough G e : ℝ) * wΔ) := by
      intro e
      rcases le_total ((triThrough G e : ℝ) * wΔ) 1 with hc | hc
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
        ring
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
        ring
    rw [Finset.sum_congr rfl (fun e _ => hpt e), Finset.sum_add_distrib]
    have hb2 : ∑ e ∈ G.edgeFinset, (1 - (triThrough G e : ℝ) * wΔ) = 0 := by
      have h := hbal
      rw [← neg_eq_zero, ← Finset.sum_neg_distrib] at h
      rw [← h]
      exact Finset.sum_congr rfl (fun e _ => by ring)
    rw [hb2, add_zero]
  have hsumeq : ∑ e ∈ G.edgeFinset, F.f (Ghat.edge e) Ghat.snk =
      ∑ e ∈ G.edgeFinset, max (1 - (triThrough G e : ℝ) * wΔ) 0 := by
    rw [hcap]
    have hall : ∑ e ∈ G.edgeFinset, F.f (Ghat.edge e) Ghat.snk =
        ∑ e : Sym2 V, F.f (Ghat.edge e) Ghat.snk :=
      Finset.sum_subset (Finset.subset_univ _)
        (fun e _ he => sinkflow_zero_of_notMem G wΔ F he)
    rw [hall, ← value_eq_sink_sum, hF]
  intro e he
  exact (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).mp hsumeq e he

/-- Conservation gives the signed source excess at each real edge node. -/
public lemma edgeNode_flow_sum (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ)
    [Fintype V]
    (hbal : ∑ e ∈ G.edgeFinset, ((triThrough G e : ℝ) * wΔ - 1) = 0)
    (F : Contrib.MaxFlowMinCut.Flow (drossNet G wΔ)) (hF : F.value = demand G wΔ)
    {f₀ : Sym2 V} (hf₀ : f₀ ∈ G.edgeFinset) :
    ∑ e' : Sym2 V, F.f (Ghat.edge f₀) (Ghat.edge e') =
      (triThrough G f₀ : ℝ) * wΔ - 1 := by
  have hcons := F.conserved (Ghat.edge f₀) (by simp [drossNet]) (by simp [drossNet])
  rw [sum_Ghat (fun v => F.f (Ghat.edge f₀) v)] at hcons
  have hsrc : F.f (Ghat.edge f₀) Ghat.src =
      -(max ((triThrough G f₀ : ℝ) * wΔ - 1) 0) := by
    rw [F.skew (Ghat.edge f₀) Ghat.src, source_saturated G wΔ F hF f₀]
  have hsnk : F.f (Ghat.edge f₀) Ghat.snk =
      max (1 - (triThrough G f₀ : ℝ) * wΔ) 0 :=
    sink_saturated G wΔ hbal F hF f₀ hf₀
  rw [hsrc, hsnk] at hcons
  have hmax : max ((triThrough G f₀ : ℝ) * wΔ - 1) 0 -
      max (1 - (triThrough G f₀ : ℝ) * wΔ) 0 =
      (triThrough G f₀ : ℝ) * wΔ - 1 := by
    rcases le_total 0 ((triThrough G f₀ : ℝ) * wΔ - 1) with hz | hz
    · rw [max_eq_left hz, max_eq_right (by linarith)]
      ring
    · rw [max_eq_right hz, max_eq_left (by linarith)]
      ring
  linarith [hcons, hmax]

end LeanPool.DrossFractionalTriangleDecomposition
