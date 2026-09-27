/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the packing gap for graphs with near-regular triangle degrees, at every density

The dense branch `Nibble.AX1.nibbleGap_denseCore` runs the unconditional nibble
(`Nibble.nibbleTheoremMostCeil_holds`) on the triangle hypergraph at the single scale `d = |V|`,
which it can only reach through a *minimum degree* hypothesis `θ|V|` with `θ` close to `1`.  But the
nibble itself needs no density at all: the triangle hypergraph of *any* graph has codegree at most
`1` (two distinct edges lie in at most one common triangle), so the only real hypothesis is
near-regularity of the triangle degrees at *some* scale `d`.

This file records exactly that.

* `Nibble.AX1.edgeTriangleDegree` — the number of triangles of `G` through an edge.
* `Nibble.AX1.gap_le_of_regular_triangle_degrees` — **the near-regular branch**: for every `ε > 0`
  there are `μ, η > 0` and `d₀` such that every graph whose triangle degrees lie in
  `[(1−μ)d, (1+μ)d]` for some `d ≥ d₀`, with the lower bound allowed to fail on an exceptional set
  of at most `η|E|` edges, has packing gap at most `ε|V|²`.  No density hypothesis whatsoever: `d`
  is arbitrary above the absolute constant `d₀`.
* `Nibble.AX1.gap_le_of_regular_triangle_degrees'` — the same with an empty exceptional set.

This strictly extends the dense branch: a graph of minimum degree `θ|V|` has all triangle degrees
in `[(1−μ)|V|, |V|]`, which is the case `d = |V|`, `Exc = ∅`; but the branch also covers, e.g.,
graphs of *constant* density with regular triangle degrees, which the dense branch cannot see.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapNearComplete

/-! # CoreGapRegularDegrees -/

@[expose] public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The **triangle degree of an edge**: the number of triangles of `G` containing it. -/
def edgeTriangleDegree (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : ℕ :=
  ((G.cliqueFinset 3).filter (fun t => e ⊆ t)).card

/-- The triangle degree of an edge is its degree in the edge-based triangle hypergraph. -/
theorem edgeTriangleDegree_eq (G : SimpleGraph V) [DecidableRel G.Adj] (E : EdgeV G) :
    Hypergraph.degree (triangleHypergraphSub G) E = edgeTriangleDegree G E.val :=
  triangleHypergraphSub_degree_eq G E

/-- **The near-regular branch.**  For every `ε > 0` there are `μ, η > 0` and `d₀ > 0` such that any
graph whose edges all have triangle degree at most `(1+μ)d`, and at least `(1−μ)d` outside an
exceptional set of at most `η|E|` edges, for some `d ≥ d₀`, has packing gap at most `ε|V|²`.

The triangle hypergraph is `3`-uniform with codegree at most `1 ≤ μd`, so these hypotheses are
exactly the input of the unconditional nibble `Nibble.nibbleTheoremMostCeil_holds`; the resulting
matching covers all but a `3ε`-fraction of the edges, which is the packing-gap accounting
`Nibble.AX1.gap_le_of_sub_matching`. -/
theorem gap_le_of_regular_triangle_degrees (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (d : ℝ) (Exc : Finset (Finset V)), d₀ ≤ d →
        (Exc.card : ℝ) ≤ η * ((G.cliqueFinset 2).card : ℝ) →
        (∀ e ∈ G.cliqueFinset 2, (edgeTriangleDegree G e : ℝ) ≤ (1 + μ) * d) →
        (∀ e ∈ G.cliqueFinset 2, e ∉ Exc → (1 - μ) * d ≤ (edgeTriangleDegree G e : ℝ)) →
        nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  classical
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ :=
    nibbleTheoremMostCeil_holds 3 (by norm_num) (3 * ε) (by linarith)
  refine ⟨μ, hμ, η, hη, max d₀ (max (1 / μ) 1), ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) (le_max_right _ _))
  intro V _ _ G _ d Exc hd hExc hhi hlo
  have hdd₀ : d₀ ≤ d := le_trans (le_max_left _ _) hd
  have hd1 : (1 : ℝ) ≤ d := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hinv : 1 / μ ≤ d := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hd
  have hcodeg : (1 : ℝ) ≤ μ * d := by
    rw [div_le_iff₀ hμ] at hinv; linarith
  -- the exceptional set, transported to the edge vertex type
  set Exc' : Finset (EdgeV G) := (univ : Finset (EdgeV G)).filter (fun E => E.val ∈ Exc)
    with hExc'def
  have hExc'card : Exc'.card ≤ Exc.card := by
    refine Finset.card_le_card_of_injOn (fun E => E.val) (fun E hE => ?_) ?_
    · exact (Finset.mem_filter.mp hE).2
    · intro E _ E' _ h
      exact Subtype.ext h
  have hcardEdge : (Fintype.card (EdgeV G) : ℝ) = ((G.cliqueFinset 2).card : ℝ) := by
    exact_mod_cast card_EdgeV G
  have hExc' : (Exc'.card : ℝ) ≤ η * (Fintype.card (EdgeV G) : ℝ) := by
    rw [hcardEdge]
    have : (Exc'.card : ℝ) ≤ (Exc.card : ℝ) := by exact_mod_cast hExc'card
    linarith
  have hhi' : ∀ E : EdgeV G, (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) ≤ (1 + μ) * d := by
    intro E
    rw [edgeTriangleDegree_eq G E]
    exact hhi E.val E.property
  have hlo' : ∀ E ∉ Exc', (1 - μ) * d ≤ (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) := by
    intro E hE
    rw [edgeTriangleDegree_eq G E]
    refine hlo E.val E.property (fun hc => hE ?_)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ E, hc⟩
  have hreg : NearlyRegularMost (triangleHypergraphSub G) d μ η :=
    triangleHypergraphSub_nearlyRegularMost_of_bounds G Exc' hExc' hlo' (fun E _ => hhi' E)
  have hcod : CodegreeBounded (triangleHypergraphSub G) (μ * d) :=
    triangleHypergraphSub_codegreeBounded G hcodeg
  obtain ⟨M, hM, hMcard⟩ :=
    hmain (triangleHypergraphSub G) d hdpos hdd₀ (triangleHypergraphSub_uniform G) hreg hcod hhi'
  refine gap_le_of_sub_matching G hε hM ?_
  simpa using hMcard

/-- **The near-regular branch, no exceptional edges.** -/
theorem gap_le_of_regular_triangle_degrees' (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (d : ℝ), d₀ ≤ d →
        (∀ e ∈ G.cliqueFinset 2, (1 - μ) * d ≤ (edgeTriangleDegree G e : ℝ) ∧
          (edgeTriangleDegree G e : ℝ) ≤ (1 + μ) * d) →
        nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := gap_le_of_regular_triangle_degrees ε hε
  refine ⟨μ, hμ, d₀, hd₀, ?_⟩
  intro V _ _ G _ d hd hwin
  refine hmain V G d ∅ hd ?_ (fun e he => (hwin e he).2) (fun e he _ => (hwin e he).1)
  rw [Finset.card_empty, Nat.cast_zero]
  positivity

/-- **The near-regular branch, up to a small deletion.**  If a graph becomes near-regular in its
triangle degrees after deleting at most `(ε/2)|V|²` edges, its packing gap is at most `ε|V|²`:
deleting `k` edges moves `ν₃*` by at most `k` and can only decrease `ν₃`
(`Nibble.AX1.gap_le_core_gap`).

This is to `Nibble.AX1.gap_le_of_regular_triangle_degrees` what
`Nibble.AX1.nibbleGap_of_dense_core` is to the dense branch. -/
theorem gap_le_of_regular_triangle_degrees_core (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (G' : SimpleGraph V) (_ : DecidableRel G'.Adj) (d : ℝ) (Exc : Finset (Finset V)),
        G' ≤ G →
        ((G.cliqueFinset 2 \ G'.cliqueFinset 2).card : ℝ) ≤ (ε / 2) * (Fintype.card V : ℝ) ^ 2 →
        d₀ ≤ d →
        (Exc.card : ℝ) ≤ η * ((G'.cliqueFinset 2).card : ℝ) →
        (∀ e ∈ G'.cliqueFinset 2, (edgeTriangleDegree G' e : ℝ) ≤ (1 + μ) * d) →
        (∀ e ∈ G'.cliqueFinset 2, e ∉ Exc → (1 - μ) * d ≤ (edgeTriangleDegree G' e : ℝ)) →
        nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := gap_le_of_regular_triangle_degrees (ε / 2) (by linarith)
  refine ⟨μ, hμ, η, hη, d₀, hd₀, ?_⟩
  intro V _ _ G _ G' _ d Exc hle hdel hd hExc hhi hlo
  have hgap' := hmain V G' d Exc hd hExc hhi hlo
  have hstab := gap_le_core_gap G G' hle
  linarith only [hdel, hgap', hstab]

/-! ### The complementary branch: uniformly small triangle degrees -/

/-- **The small-degree branch.**  For every `ε > 0` there is `ρ > 0` such that a graph all of whose
edges lie in at most `ρ|V|` triangles has packing gap at most `ε|V|²`.

The handshake identity `∑_e t(e) = 3·#triangles` turns the degree bound into
`#triangles ≤ ρ|V|³/6`, which is the removal branch `Nibble.AX1.nu3star_le_of_few_triangles`.
Together with `Nibble.AX1.gap_le_of_regular_triangle_degrees` this leaves only the graphs whose
triangle degrees are simultaneously large somewhere and far from regular. -/
theorem gap_le_of_small_triangle_degrees (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ e ∈ G.cliqueFinset 2, (edgeTriangleDegree G e : ℝ) ≤ ρ * (Fintype.card V : ℝ)) →
        nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  classical
  refine ⟨SimpleGraph.triangleRemovalBound ε, SimpleGraph.triangleRemovalBound_pos hε, ?_⟩
  intro V _ _ G _ hdeg
  set ρ : ℝ := SimpleGraph.triangleRemovalBound ε with hρdef
  have hρ : 0 < ρ := SimpleGraph.triangleRemovalBound_pos hε
  have hnu3 : (0 : ℝ) ≤ (nu3 G : ℝ) := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hn0 | hnpos
  · -- no vertices: no triangles at all
    have htri : (G.cliqueFinset 3).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro t ht
      have : t.Nonempty := by
        rw [← Finset.card_pos, (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq]
        norm_num
      obtain ⟨x, -⟩ := this
      have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨x⟩
      omega
    have h1 := nu3star_le_card_triangles G
    rw [htri, Nat.cast_zero] at h1
    have : (0 : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by positivity
    linarith only [h1, this]
  have hnR : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hnpos
  -- the handshake bound on the number of triangles
  have hsum : ∑ E : EdgeV G, degree (triangleHypergraphSub G) E = 3 * (G.cliqueFinset 3).card :=
    sum_degree_triangleHypergraphSub G
  have hsumR : (3 : ℝ) * ((G.cliqueFinset 3).card : ℝ)
      = ∑ E : EdgeV G, (degree (triangleHypergraphSub G) E : ℝ) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hsum
    push_cast at this
    linarith only [this]
  have hbound : ∑ E : EdgeV G, (degree (triangleHypergraphSub G) E : ℝ)
      ≤ (Fintype.card (EdgeV G) : ℝ) * (ρ * (Fintype.card V : ℝ)) := by
    calc ∑ E : EdgeV G, (degree (triangleHypergraphSub G) E : ℝ)
        ≤ ∑ _E : EdgeV G, ρ * (Fintype.card V : ℝ) := by
          refine Finset.sum_le_sum (fun E _ => ?_)
          rw [edgeTriangleDegree_eq G E]
          exact hdeg E.val E.property
      _ = (Fintype.card (EdgeV G) : ℝ) * (ρ * (Fintype.card V : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hcardE : (Fintype.card (EdgeV G) : ℝ) = ((G.cliqueFinset 2).card : ℝ) := by
    exact_mod_cast card_EdgeV G
  have hE : ((G.cliqueFinset 2).card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 2 :=
    Nibble.edge_card_le_half_card_sq G
  rw [hcardE] at hbound
  have hfew : ((G.cliqueFinset 3).card : ℝ) < ρ * (Fintype.card V : ℝ) ^ 3 := by
    have hpos : (0 : ℝ) < ρ * (Fintype.card V : ℝ) ^ 3 := by positivity
    have hstep : ((G.cliqueFinset 2).card : ℝ) * (ρ * (Fintype.card V : ℝ))
        ≤ ((Fintype.card V : ℝ) ^ 2 / 2) * (ρ * (Fintype.card V : ℝ)) :=
      mul_le_mul_of_nonneg_right hE (by positivity)
    have hring : ((Fintype.card V : ℝ) ^ 2 / 2) * (ρ * (Fintype.card V : ℝ))
        = ρ * (Fintype.card V : ℝ) ^ 3 / 2 := by ring
    rw [hring] at hstep
    linarith only [hsumR, hbound, hstep, hpos]
  have h1 := nu3star_le_of_few_triangles G hfew
  linarith only [h1]

/-! ### Deleting the heavy edges -/

/-- `G` with every edge of triangle degree above `c` deleted. -/
def deleteHeavy (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ (edgeTriangleDegree G {x, y} : ℝ) ≤ c
  symm := ⟨by
    rintro x y ⟨h1, h2⟩
    refine ⟨h1.symm, ?_⟩
    rwa [Finset.pair_comm]⟩
  loopless := ⟨fun x h => G.irrefl h.1⟩

noncomputable instance instDecidableRelDeleteHeavy (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) :
    DecidableRel (deleteHeavy G c).Adj :=
  fun x y => inferInstanceAs (Decidable (G.Adj x y ∧ (edgeTriangleDegree G {x, y} : ℝ) ≤ c))

theorem deleteHeavy_adj (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) (x y : V) :
    (deleteHeavy G c).Adj x y ↔ G.Adj x y ∧ (edgeTriangleDegree G {x, y} : ℝ) ≤ c := Iff.rfl

theorem deleteHeavy_le (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) :
    deleteHeavy G c ≤ G := fun _ _ h => h.1

/-- The `2`-cliques deleted by `Nibble.AX1.deleteHeavy` are exactly heavy edges. -/
theorem deleted_subset_heavy (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) :
    G.cliqueFinset 2 \ (deleteHeavy G c).cliqueFinset 2
      ⊆ (G.cliqueFinset 2).filter (fun e => c < (edgeTriangleDegree G e : ℝ)) := by
  intro e he
  rw [Finset.mem_sdiff] at he
  refine Finset.mem_filter.mpr ⟨he.1, ?_⟩
  obtain ⟨hmem, hnot⟩ := he
  have hcl := SimpleGraph.mem_cliqueFinset_iff.mp hmem
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcl.card_eq
  have hadj : G.Adj a b := hcl.1 (by simp) (by simp) hab
  by_contra hcon
  push Not at hcon
  refine hnot (SimpleGraph.mem_cliqueFinset_iff.mpr ⟨?_, Finset.card_pair hab⟩)
  have hadj' : (deleteHeavy G c).Adj a b := (deleteHeavy_adj G c a b).mpr ⟨hadj, hcon⟩
  simpa using SimpleGraph.isClique_pair.mpr (fun _ => hadj')

/-- Triangle degrees only decrease when passing to a subgraph. -/
theorem edgeTriangleDegree_mono (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (hle : G' ≤ G) (e : Finset V) : edgeTriangleDegree G' e ≤ edgeTriangleDegree G e :=
  Finset.card_le_card
    (Finset.filter_subset_filter _ (SimpleGraph.cliqueFinset_mono G hle))

/-- **The few-heavy-edges branch.**  For every `ε > 0` there is `ρ > 0` such that if the edges lying
in more than `ρ|V|` triangles number at most `(ε/2)|V|²`, then the packing gap is at most `ε|V|²`:
delete them (which costs at most that many edges of the gap) and apply
`Nibble.AX1.gap_le_of_small_triangle_degrees` to what is left.

So the only graphs left open are those with at least `(ε/2)|V|²` edges each lying in more than
`ρ|V|` triangles. -/
theorem gap_le_of_few_heavy_edges (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (((G.cliqueFinset 2).filter
            (fun e => ρ * (Fintype.card V : ℝ) < (edgeTriangleDegree G e : ℝ))).card : ℝ)
          ≤ (ε / 2) * (Fintype.card V : ℝ) ^ 2 →
        nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  classical
  obtain ⟨ρ, hρ, hsmall⟩ := gap_le_of_small_triangle_degrees (ε / 2) (by linarith)
  refine ⟨ρ, hρ, ?_⟩
  intro V _ _ G _ hheavy
  set G' : SimpleGraph V := deleteHeavy G (ρ * (Fintype.card V : ℝ)) with hG'def
  have hle : G' ≤ G := deleteHeavy_le G _
  have hdel : ((G.cliqueFinset 2 \ G'.cliqueFinset 2).card : ℝ)
      ≤ (ε / 2) * (Fintype.card V : ℝ) ^ 2 := by
    have h1 : (G.cliqueFinset 2 \ G'.cliqueFinset 2).card
        ≤ ((G.cliqueFinset 2).filter
            (fun e => ρ * (Fintype.card V : ℝ) < (edgeTriangleDegree G e : ℝ))).card :=
      Finset.card_le_card (deleted_subset_heavy G _)
    have h2 : ((G.cliqueFinset 2 \ G'.cliqueFinset 2).card : ℝ)
        ≤ (((G.cliqueFinset 2).filter
            (fun e => ρ * (Fintype.card V : ℝ) < (edgeTriangleDegree G e : ℝ))).card : ℝ) := by
      exact_mod_cast h1
    linarith only [hheavy, h2]
  have hdeg : ∀ e ∈ G'.cliqueFinset 2, (edgeTriangleDegree G' e : ℝ)
      ≤ ρ * (Fintype.card V : ℝ) := by
    intro e he
    rw [SimpleGraph.mem_cliqueFinset_iff] at he
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he.card_eq
    have hadj : (deleteHeavy G (ρ * (Fintype.card V : ℝ))).Adj a b := he.1 (by simp) (by simp) hab
    have hmono : edgeTriangleDegree G' ({a, b} : Finset V)
        ≤ edgeTriangleDegree G ({a, b} : Finset V) := edgeTriangleDegree_mono G G' hle _
    have hbound : (edgeTriangleDegree G ({a, b} : Finset V) : ℝ) ≤ ρ * (Fintype.card V : ℝ) :=
      hadj.2
    have : (edgeTriangleDegree G' ({a, b} : Finset V) : ℝ)
        ≤ (edgeTriangleDegree G ({a, b} : Finset V) : ℝ) := by exact_mod_cast hmono
    linarith only [hbound, this]
  have hgap' := hsmall V G' hdeg
  have hstab := gap_le_core_gap G G' hle
  linarith only [hdel, hgap', hstab]

end Nibble.AX1
