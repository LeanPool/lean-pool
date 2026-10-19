/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Tactic

/-!

Adapted from [jtraverso/turan-stability](https://github.com/jtraverso/turan-stability/blob/3eb99033cc931add291781f77b7446dcba8f5f9d/StabilityLib/Furedi.lean) (Palomar-registered source).
# Füredi's stability theorem for Turán's theorem

For a finite simple graph `G` and a map `f : V → Fin p`, the graph
`(⊤ : SimpleGraph (Fin p)).comap f` is the complete `p`-partite graph whose parts are the fibres
of `f`; `G \ (⊤.comap f)` consists of the edges of `G` inside the parts.

* `Furedi.card_edgeSet_add_le`: **Füredi (2015), partition inequality.** If `G` is
  `K_{p+1}`-free, there is a partition `f` with `e(G) + Σᵢ e(G[Vᵢ]) ≤ e(K(V₁, …, V_p))`.
* `Furedi.furedi`: **Füredi (2015).** A `K_{p+1}`-free graph with at least
  `turanNumber n p - t` edges has a `p`-partite subgraph with at least `e(G) - t` edges.
* `Furedi.exists_partition_symmDiff_le`: such a graph is at edit distance at most `3 t` from a
  complete `p`-partite graph, with at most `t` edges inside the parts.
* `Furedi.erdos_simonovits_stability`: **Erdős–Simonovits stability for cliques.** For every
  `ε > 0` there is `δ > 0` such that every `K_{p+1}`-free graph with at least
  `(1 - 1/p) n² / 2 - δ n²` edges can be turned into a complete `p`-partite graph by changing
  at most `ε n²` edges.
-/

@[expose] public section

open Finset Fintype SimpleGraph

namespace Furedi

variable {V : Type*} [Fintype V]

section Aux

variable {W : Type*} (G : SimpleGraph W) [DecidableRel G.Adj]

/-- Ordered count of `G`-edges plus `G`-edges inside fibres of `f`, within `S`. -/
def lhsCount (S : Finset W) (f : W → ℕ) : ℕ :=
  ∑ u ∈ S, ∑ v ∈ S, ((if G.Adj u v then 1 else 0) + (if G.Adj u v ∧ f u = f v then 1 else 0))

/-- Ordered count of pairs in `S` with different `f`-values. -/
def rhsCount (S : Finset W) (f : W → ℕ) : ℕ :=
  ∑ u ∈ S, ∑ v ∈ S, if f u ≠ f v then 1 else 0

lemma key_ineq (p : ℕ) : ∀ S : Finset W, (∀ t ⊆ S, ¬ G.IsNClique (p + 1) t) →
    ∃ f : W → ℕ, (∀ w ∈ S, f w < p) ∧ lhsCount G S f ≤ rhsCount S f := by
  induction p with
  | zero =>
    intro S hS
    have hSe : S = ∅ := by
      by_contra h
      obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr h
      exact hS {a} (by simpa using ha) (isNClique_one.mpr ⟨a, rfl⟩)
    subst hSe
    exact ⟨fun _ => 0, by simp, by simp [lhsCount, rhsCount]⟩
  | succ p ih =>
    intro S hS
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · subst hSe
      exact ⟨fun _ => 0, by simp, by simp [lhsCount, rhsCount]⟩
    classical
    obtain ⟨x, hxS, hxmax⟩ := Finset.exists_max_image S
      (fun u => ∑ v ∈ S, if G.Adj u v then 1 else 0) hSne
    set N := S.filter (G.Adj x) with hN
    set V₁ := S.filter (fun w => ¬ G.Adj x w) with hV₁
    have hNcl : ∀ t ⊆ N, ¬ G.IsNClique (p + 1) t := by
      intro t ht hcl
      have hxt : x ∉ t := fun h => by
        have := (Finset.mem_filter.mp (ht h)).2
        exact G.loopless.irrefl x this
      refine hS (insert x t) ?_ (hcl.insert fun b hb => (Finset.mem_filter.mp (ht hb)).2)
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hxS
      · exact (Finset.mem_filter.mp (ht hy)).1
    obtain ⟨g, hg, hgle⟩ := ih N hNcl
    refine ⟨fun w => if G.Adj x w then g w + 1 else 0, ?_, ?_⟩
    · intro w hw
      by_cases h : G.Adj x w
      · simp only [h, ite_true]
        have := hg w (Finset.mem_filter.mpr ⟨hw, h⟩)
        omega
      · simp [h]
    set f : W → ℕ := fun w => if G.Adj x w then g w + 1 else 0 with hf
    have fN : ∀ u ∈ N, f u = g u + 1 := fun u hu => by
      simp [hf, (Finset.mem_filter.mp hu).2]
    have fV : ∀ u ∈ V₁, f u = 0 := fun u hu => by
      simp [hf, (Finset.mem_filter.mp hu).2]
    have split1 : ∀ F : W → ℕ, ∑ v ∈ S, F v = ∑ v ∈ N, F v + ∑ v ∈ V₁, F v :=
      fun F => (sum_filter_add_sum_filter_not _ _ _).symm
    have split2 : ∀ F : W → W → ℕ, ∑ u ∈ S, ∑ v ∈ S, F u v =
        ∑ u ∈ N, ∑ v ∈ N, F u v + ∑ u ∈ N, ∑ v ∈ V₁, F u v +
        ∑ u ∈ V₁, ∑ v ∈ N, F u v + ∑ u ∈ V₁, ∑ v ∈ V₁, F u v := by
      intro F
      calc ∑ u ∈ S, ∑ v ∈ S, F u v = ∑ u ∈ S, (∑ v ∈ N, F u v + ∑ v ∈ V₁, F u v) :=
            sum_congr rfl fun u _ => split1 _
        _ = _ := by rw [split1]; simp only [sum_add_distrib]; ring
    let A : W → W → ℕ := fun u v => if G.Adj u v then 1 else 0
    have hNN : ∑ u ∈ N, ∑ v ∈ N, ((if G.Adj u v then 1 else 0) +
        (if G.Adj u v ∧ f u = f v then 1 else 0)) = lhsCount G N g := by
      unfold lhsCount
      refine sum_congr rfl fun u hu => sum_congr rfl fun v hv => ?_
      rw [fN u hu, fN v hv]; simp
    have hNV : ∑ u ∈ N, ∑ v ∈ V₁, ((if G.Adj u v then 1 else 0) +
        (if G.Adj u v ∧ f u = f v then 1 else 0)) = ∑ u ∈ N, ∑ v ∈ V₁, A u v := by
      refine sum_congr rfl fun u hu => sum_congr rfl fun v hv => ?_
      rw [fN u hu, fV v hv]; simp [A]
    have hVN : ∑ u ∈ V₁, ∑ v ∈ N, ((if G.Adj u v then 1 else 0) +
        (if G.Adj u v ∧ f u = f v then 1 else 0)) = ∑ u ∈ V₁, ∑ v ∈ N, A u v := by
      refine sum_congr rfl fun u hu => sum_congr rfl fun v hv => ?_
      rw [fV u hu, fN v hv]; simp [A]
    have hVV : ∑ u ∈ V₁, ∑ v ∈ V₁, ((if G.Adj u v then 1 else 0) +
        (if G.Adj u v ∧ f u = f v then 1 else 0)) = 2 * ∑ u ∈ V₁, ∑ v ∈ V₁, A u v := by
      rw [mul_sum]
      refine sum_congr rfl fun u hu => ?_
      rw [mul_sum]
      refine sum_congr rfl fun v hv => ?_
      rw [fV u hu, fV v hv]; simp [A]; split_ifs <;> simp
    have hNVc : ∑ u ∈ N, ∑ v ∈ V₁, A u v = ∑ u ∈ V₁, ∑ v ∈ N, A u v := by
      rw [sum_comm]
      exact sum_congr rfl fun u _ => sum_congr rfl fun v _ => by simp [A, G.adj_comm]
    have hdeg : ∑ u ∈ V₁, ∑ v ∈ N, A u v + ∑ u ∈ V₁, ∑ v ∈ V₁, A u v ≤ #V₁ * #N := by
      rw [← sum_add_distrib]
      have : ∀ u ∈ V₁, ∑ v ∈ N, A u v + ∑ v ∈ V₁, A u v ≤ #N := by
        intro u hu
        rw [← split1 (A u), hN, card_filter]
        exact hxmax u (Finset.mem_filter.mp hu).1
      calc _ ≤ ∑ u ∈ V₁, #N := sum_le_sum this
        _ = _ := by simp
    have rNN : ∑ u ∈ N, ∑ v ∈ N, (if f u ≠ f v then 1 else 0) = rhsCount N g := by
      unfold rhsCount
      refine sum_congr rfl fun u hu => sum_congr rfl fun v hv => ?_
      rw [fN u hu, fN v hv]; simp
    have rNV : ∑ u ∈ N, ∑ v ∈ V₁, (if f u ≠ f v then 1 else 0) = #N * #V₁ := by
      rw [card_eq_sum_ones, sum_mul]
      refine sum_congr rfl fun u hu => ?_
      rw [one_mul, card_eq_sum_ones]
      refine sum_congr rfl fun v hv => ?_
      rw [fN u hu, fV v hv]; simp
    have rVN : ∑ u ∈ V₁, ∑ v ∈ N, (if f u ≠ f v then 1 else 0) = #V₁ * #N := by
      rw [card_eq_sum_ones, sum_mul]
      refine sum_congr rfl fun u hu => ?_
      rw [one_mul, card_eq_sum_ones]
      refine sum_congr rfl fun v hv => ?_
      rw [fV u hu, fN v hv]; simp
    have rVV : ∑ u ∈ V₁, ∑ v ∈ V₁, (if f u ≠ f v then 1 else 0) = 0 := by
      refine sum_eq_zero fun u hu => sum_eq_zero fun v hv => ?_
      rw [fV u hu, fV v hv]; simp
    change lhsCount G S f ≤ rhsCount S f
    unfold lhsCount rhsCount
    rw [split2, split2 (fun u v => if f u ≠ f v then 1 else 0), hNN, hNV, hVN, hVV, rNN, rNV,
      rVN, rVV, hNVc]
    rw [mul_comm #N]
    linarith

end Aux

lemma two_mul_ncard_edgeSet {W : Type*} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj] :
    2 * H.edgeSet.ncard = ∑ u, ∑ v, if H.Adj u v then 1 else 0 := by
  classical
  rw [← coe_edgeFinset, Set.ncard_coe_finset, ← sum_degrees_eq_twice_card_edges]
  refine sum_congr rfl fun u _ => ?_
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, card_filter]

/-- **Füredi's partition inequality.** Every `K_{p+1}`-free finite graph has a partition into
`p` parts (the fibres of `f`) such that the number of edges of `G` plus the number of edges of
`G` inside the parts is at most the number of edges of the complete `p`-partite graph on these
parts. -/
theorem card_edgeSet_add_le {W : Type*} [Finite W] (G : SimpleGraph W) {p : ℕ} (hp : 0 < p)
    (hG : G.CliqueFree (p + 1)) :
    ∃ f : W → Fin p, G.edgeSet.ncard + (G \ (⊤ : SimpleGraph (Fin p)).comap f).edgeSet.ncard ≤
      ((⊤ : SimpleGraph (Fin p)).comap f).edgeSet.ncard := by
  have _ : 0 < p := hp
  classical
  have := Fintype.ofFinite W
  obtain ⟨f, hf, hle⟩ := key_ineq G p univ (fun t _ => hG t)
  let f' : W → Fin p := fun w => ⟨f w, hf w (mem_univ w)⟩
  refine ⟨f', ?_⟩
  have e1 := two_mul_ncard_edgeSet G
  have e2 := two_mul_ncard_edgeSet (G \ (⊤ : SimpleGraph (Fin p)).comap f')
  have e3 := two_mul_ncard_edgeSet ((⊤ : SimpleGraph (Fin p)).comap f')
  have hl : lhsCount G univ f = (∑ u, ∑ v, if G.Adj u v then 1 else 0) +
      ∑ u, ∑ v, if (G \ (⊤ : SimpleGraph (Fin p)).comap f').Adj u v then 1 else 0 := by
    unfold lhsCount
    rw [← sum_add_distrib]
    refine sum_congr rfl fun u _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun v _ => ?_
    by_cases h1 : G.Adj u v <;> by_cases h2 : f u = f v <;> simp [h1, h2, f', Fin.ext_iff]
  have hr : rhsCount univ f =
      ∑ u, ∑ v, if ((⊤ : SimpleGraph (Fin p)).comap f').Adj u v then 1 else 0 := by
    unfold rhsCount
    refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
    by_cases h2 : f u = f v <;> simp [h2, f', Fin.ext_iff]
  omega

lemma ncard_comap_le_turanNumber {p : ℕ} (f : V → Fin p) :
    ((⊤ : SimpleGraph (Fin p)).comap f).edgeSet.ncard ≤ turanNumber (card V) p := by
  classical
  have hc : ((⊤ : SimpleGraph (Fin p)).comap f).Colorable p := by
    simpa using (Coloring.mk f (fun h => by simpa using h) :
      ((⊤ : SimpleGraph (Fin p)).comap f).Coloring (Fin p)).colorable
  have := (hc.cliqueFree (Nat.lt_succ_self p)).card_edgeFinset_le
  rwa [← Set.ncard_coe_finset, coe_edgeFinset] at this

/-- **Füredi's theorem (2015).** If `G` is a `K_{p+1}`-free graph on `n` vertices with at least
`turanNumber n p - t` edges, then `G` has a `p`-colourable (i.e. `p`-partite) subgraph `H` with
at least `e(G) - t` edges. -/
theorem furedi (G : SimpleGraph V) {p t : ℕ} (hp : 0 < p) (hG : G.CliqueFree (p + 1))
    (ht : turanNumber (card V) p ≤ G.edgeSet.ncard + t) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.Colorable p ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard + t := by
  obtain ⟨f, hf⟩ := card_edgeSet_add_le G hp hG
  have hK := ncard_comap_le_turanNumber f
  refine ⟨G ⊓ (⊤ : SimpleGraph (Fin p)).comap f, inf_le_left, ?_, ?_⟩
  · have hc : ((⊤ : SimpleGraph (Fin p)).comap f).Colorable p := by
      simpa using (Coloring.mk f (fun h => by simpa using h) :
        ((⊤ : SimpleGraph (Fin p)).comap f).Coloring (Fin p)).colorable
    exact hc.mono_left inf_le_right
  · have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard G.edgeSet
      ((⊤ : SimpleGraph (Fin p)).comap f).edgeSet
    rw [← edgeSet_inf, ← edgeSet_sdiff] at hsplit
    omega

/-- **Füredi's theorem, edit-distance form.** Under the hypotheses of `furedi`, there is a
partition into `p` parts with at most `t` edges of `G` inside the parts, and `G` differs from the
complete `p`-partite graph on these parts in at most `3 t` edges. -/
theorem exists_partition_symmDiff_le (G : SimpleGraph V) {p t : ℕ} (hp : 0 < p)
    (hG : G.CliqueFree (p + 1)) (ht : turanNumber (card V) p ≤ G.edgeSet.ncard + t) :
    ∃ f : V → Fin p, (G \ (⊤ : SimpleGraph (Fin p)).comap f).edgeSet.ncard ≤ t ∧
      (symmDiff G ((⊤ : SimpleGraph (Fin p)).comap f)).edgeSet.ncard ≤ 3 * t := by
  obtain ⟨f, hf⟩ := card_edgeSet_add_le G hp hG
  have hK := ncard_comap_le_turanNumber f
  refine ⟨f, ?_⟩
  set K := (⊤ : SimpleGraph (Fin p)).comap f
  have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard G.edgeSet K.edgeSet
  have hsplit2 := Set.ncard_inter_add_ncard_sdiff_eq_ncard K.edgeSet G.edgeSet
  rw [Set.inter_comm, ← edgeSet_inf, ← edgeSet_sdiff] at hsplit2
  rw [← edgeSet_inf, ← edgeSet_sdiff] at hsplit
  refine ⟨by omega, ?_⟩
  have hu : (symmDiff G K).edgeSet.ncard ≤ (G \ K).edgeSet.ncard + (K \ G).edgeSet.ncard := by
    rw [symmDiff_def, edgeSet_sup]
    exact Set.ncard_union_le _ _
  omega

/-- **Erdős–Simonovits stability theorem for cliques** (Erdős 1967, Simonovits 1968), in the
form obtained from Füredi's theorem: for every `ε > 0` there is `δ > 0` such that every
`K_{p+1}`-free graph on `n` vertices with at least `(1 - 1/p) n² / 2 - δ n²` edges differs from
some complete `p`-partite graph on the same vertices in at most `ε n²` edges. -/
theorem erdos_simonovits_stability {p : ℕ} (hp : 0 < p) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (W : Type) [Fintype W] (G : SimpleGraph W), G.CliqueFree (p + 1) →
      (1 - 1 / (p : ℝ)) * (card W : ℝ) ^ 2 / 2 - δ * (card W : ℝ) ^ 2 ≤ G.edgeSet.ncard →
      ∃ f : W → Fin p,
        ((symmDiff G ((⊤ : SimpleGraph (Fin p)).comap f)).edgeSet.ncard : ℝ) ≤
          ε * (card W : ℝ) ^ 2 := by
  refine ⟨ε / 3, by positivity, fun W _ G hG hedge => ?_⟩
  set n := card W
  set T := turanNumber n p
  set e := G.edgeSet.ncard
  obtain ⟨f, -, h2⟩ := exists_partition_symmDiff_le G hp hG (t := T - e) le_add_tsub
  refine ⟨f, ?_⟩
  have hT : (T : ℝ) ≤ (1 - 1 / (p : ℝ)) * (n : ℝ) ^ 2 / 2 := by
    have h := mul_turanNumber_le (r := p) (n := n)
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    have hc : (2 * p * T : ℝ) ≤ ((p : ℝ) - 1) * (n : ℝ) ^ 2 := by
      have := (Nat.cast_le (α := ℝ)).mpr h
      push_cast [Nat.cast_sub (show 1 ≤ p from hp)] at this
      exact this
    rw [show (1 - 1 / (p : ℝ)) * (n : ℝ) ^ 2 / 2 = ((p - 1) * (n : ℝ) ^ 2) / (2 * p) by
      field_simp]
    rw [le_div_iff₀ (by positivity)]
    linarith
  have ht : ((T - e : ℕ) : ℝ) ≤ ε / 3 * (n : ℝ) ^ 2 := by
    rcases le_total T e with h | h
    · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]; positivity
    · rw [Nat.cast_sub h]; linarith
  have := (Nat.cast_le (α := ℝ)).mpr h2
  push_cast at this
  linarith

end Furedi
