/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Basic
public import LeanPool.MaxFlowMinCut
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dross's auxiliary network

The nodes are graph edges, a source, and a sink. We use Lean Pool's existing finite
max-flow/min-cut structures rather than porting a second copy of that development.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*} [DecidableEq V]

/-- The number of graph triangles containing an edge. -/
@[expose] public def triThrough (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (e : Sym2 V) : ℕ :=
  ((G.cliqueFinset 3).filter (fun t => e ∈ triEdges t)).card

/-- An edge node, source, or sink in Dross's auxiliary network. -/
public inductive Ghat (V : Type*) where
  | src : Ghat V
  | snk : Ghat V
  | edge : Sym2 V → Ghat V
  deriving DecidableEq

public instance [Fintype V] : Fintype (Ghat V) where
  elems := {Ghat.src, Ghat.snk} ∪ (Finset.univ.image Ghat.edge)
  complete := by rintro (_ | _ | e) <;> simp

/-- Two disjoint graph edges whose four endpoints form a clique. -/
@[expose] public def K4pair (G : SimpleGraph V) (e₁ e₂ : Sym2 V) : Prop :=
  ∃ a b c d : V, e₁ = s(a, b) ∧ e₂ = s(c, d) ∧
    ({a, b, c, d} : Finset V).card = 4 ∧ G.IsNClique 4 {a, b, c, d}

variable [Fintype V]

public instance (G : SimpleGraph V) [DecidableRel G.Adj] (e₁ e₂ : Sym2 V) :
    Decidable (K4pair G e₁ e₂) := by
  unfold K4pair
  infer_instance

/-- Per-arc capacity on the edge-to-edge arcs. -/
@[expose] public noncomputable def cc (G : SimpleGraph V) [DecidableRel G.Adj]
    (wΔ : ℝ) : ℝ :=
  2 * wΔ / (3 * (G.minDegree : ℝ) - 3)

/-- Capacities of the auxiliary network. -/
@[expose] public noncomputable def dcap (G : SimpleGraph V) [DecidableRel G.Adj]
    (wΔ : ℝ) : Ghat V → Ghat V → ℝ
  | Ghat.src, Ghat.edge e => max ((triThrough G e : ℝ) * wΔ - 1) 0
  | Ghat.edge e, Ghat.snk => max (1 - (triThrough G e : ℝ) * wΔ) 0
  | Ghat.edge e₁, Ghat.edge e₂ => if K4pair G e₁ e₂ then max (cc G wΔ) 0 else 0
  | _, _ => 0

/-- Dross's network in the already pooled finite-network API. -/
@[expose] public noncomputable def drossNet (G : SimpleGraph V) [DecidableRel G.Adj]
    (wΔ : ℝ) : Contrib.MaxFlowMinCut.Network (Ghat V) where
  cap := dcap G wΔ
  capNonneg u v := by
    cases u <;> cases v <;> simp only [dcap] <;> positivity
  s := Ghat.src
  t := Ghat.snk
  st := by simp

/-- Total source-arc capacity, the demand that a maximum flow must meet. -/
@[expose] public noncomputable def demand (G : SimpleGraph V) [DecidableRel G.Adj]
    (wΔ : ℝ) : ℝ :=
  ∑ e ∈ G.edgeFinset, max ((triThrough G e : ℝ) * wΔ - 1) 0

/-- Summing the number of triangles through each edge counts each triangle three times. -/
public theorem handshake (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ e ∈ G.edgeFinset, triThrough G e = 3 * (G.cliqueFinset 3).card := by
  simp_rw [triThrough, Finset.card_filter]
  rw [Finset.sum_comm,
    show 3 * (G.cliqueFinset 3).card = ∑ _t ∈ G.cliqueFinset 3, 3 by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← Finset.card_filter, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr (triEdges_subset_edgeFinset G ht)]
  exact triEdges_card_of_isNClique G ((SimpleGraph.mem_cliqueFinset_iff).mp ht)

/-- The balanced initial weight makes the signed source excess sum to zero. -/
public theorem balance (G : SimpleGraph V) [DecidableRel G.Adj] {wΔ : ℝ}
    (hT : 0 < (G.cliqueFinset 3).card)
    (hwΔ : wΔ = (G.edgeFinset.card : ℝ) / (3 * (G.cliqueFinset 3).card)) :
    ∑ e ∈ G.edgeFinset, ((triThrough G e : ℝ) * wΔ - 1) = 0 := by
  have hsum : (∑ e ∈ G.edgeFinset, (triThrough G e : ℝ)) =
      3 * (G.cliqueFinset 3).card := by
    rw [← Nat.cast_sum, handshake]
    push_cast
    ring
  have h3T : (3 : ℝ) * (G.cliqueFinset 3).card ≠ 0 := by positivity
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_const, hsum, hwΔ,
    nsmul_eq_mul, mul_one]
  field_simp
  ring

/-- A sum over network nodes splits into source, sink, and edge nodes. -/
public theorem sum_Ghat (f : Ghat V → ℝ) :
    ∑ v, f v = f Ghat.src + f Ghat.snk + ∑ e : Sym2 V, f (Ghat.edge e) := by
  have huniv : (Finset.univ : Finset (Ghat V)) =
      insert Ghat.src (insert Ghat.snk ((Finset.univ : Finset (Sym2 V)).image Ghat.edge)) := by
    ext v
    cases v <;> simp
  rw [huniv, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_image (by intro a _ b _ h; injection h)]
  ring

/-- A nonedge lies in no graph triangle. -/
public theorem triThrough_eq_zero_of_notMem (G : SimpleGraph V) [DecidableRel G.Adj]
    {e : Sym2 V} (he : e ∉ G.edgeFinset) : triThrough G e = 0 := by
  rw [triThrough, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro t ht hmem
  exact he (triEdges_subset_edgeFinset G ht hmem)

/-- The flow value is the sum of the source-to-edge flows. -/
public theorem value_eq_source_sum (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ)
    (F : Contrib.MaxFlowMinCut.Flow (drossNet G wΔ)) :
    F.value = ∑ e : Sym2 V, F.f Ghat.src (Ghat.edge e) := by
  have h1 : F.f Ghat.src Ghat.src = 0 := by
    have := F.skew Ghat.src Ghat.src
    linarith
  have h2 : F.f Ghat.src Ghat.snk = 0 := by
    have hle : F.f Ghat.src Ghat.snk ≤ 0 := F.capacitated Ghat.src Ghat.snk
    have hge : F.f Ghat.snk Ghat.src ≤ 0 := F.capacitated Ghat.snk Ghat.src
    have hsk := F.skew Ghat.src Ghat.snk
    linarith
  change ∑ v, F.f Ghat.src v = _
  rw [sum_Ghat (fun v => F.f Ghat.src v), h1, h2]
  ring

/-- If total source flow meets demand, every source arc is saturated. -/
public theorem source_saturated (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ)
    (F : Contrib.MaxFlowMinCut.Flow (drossNet G wΔ)) (hF : F.value = demand G wΔ) :
    ∀ e : Sym2 V, F.f Ghat.src (Ghat.edge e) =
      max ((triThrough G e : ℝ) * wΔ - 1) 0 := by
  have hle : ∀ e : Sym2 V, F.f Ghat.src (Ghat.edge e) ≤
      max ((triThrough G e : ℝ) * wΔ - 1) 0 :=
    fun e => F.capacitated Ghat.src (Ghat.edge e)
  have hdemand : demand G wΔ =
      ∑ e : Sym2 V, max ((triThrough G e : ℝ) * wΔ - 1) 0 := by
    rw [demand]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    rw [triThrough_eq_zero_of_notMem G he]
    simp
  have hsum : ∑ e : Sym2 V, F.f Ghat.src (Ghat.edge e) =
      ∑ e : Sym2 V, max ((triThrough G e : ℝ) * wΔ - 1) 0 := by
    rw [← value_eq_source_sum, hF, hdemand]
  intro e
  exact (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).mp hsum e (Finset.mem_univ e)

/-- The flow value also equals the total flow into the sink from edge nodes. -/
public theorem value_eq_sink_sum (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ)
    (F : Contrib.MaxFlowMinCut.Flow (drossNet G wΔ)) :
    F.value = ∑ e : Sym2 V, F.f (Ghat.edge e) Ghat.snk := by
  have hsrcsnk : F.f Ghat.src Ghat.snk = 0 := by
    have hle : F.f Ghat.src Ghat.snk ≤ 0 := F.capacitated Ghat.src Ghat.snk
    have hge : F.f Ghat.snk Ghat.src ≤ 0 := F.capacitated Ghat.snk Ghat.src
    have hsk := F.skew Ghat.src Ghat.snk
    linarith
  have hsnksnk : F.f Ghat.snk Ghat.snk = 0 := by
    have := F.skew Ghat.snk Ghat.snk
    linarith
  have htot : ∑ u : Ghat V, ∑ v : Ghat V, F.f u v = 0 := by
    have hSS : (∑ u : Ghat V, ∑ v : Ghat V, F.f u v) =
        - ∑ u : Ghat V, ∑ v : Ghat V, F.f u v := by
      calc ∑ u : Ghat V, ∑ v : Ghat V, F.f u v
          = ∑ u : Ghat V, ∑ v : Ghat V, - F.f v u :=
            Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => F.skew u v))
        _ = ∑ v : Ghat V, ∑ u : Ghat V, - F.f v u := Finset.sum_comm
        _ = - ∑ v : Ghat V, ∑ u : Ghat V, F.f v u := by
            simp only [Finset.sum_neg_distrib]
    linarith
  have hrows : ∑ u : Ghat V, ∑ v : Ghat V, F.f u v =
      (∑ v, F.f Ghat.src v) + (∑ v, F.f Ghat.snk v) +
        ∑ e : Sym2 V, ∑ v, F.f (Ghat.edge e) v :=
    sum_Ghat (fun u => ∑ v, F.f u v)
  have hedgesum0 : ∑ e : Sym2 V, ∑ v, F.f (Ghat.edge e) v = 0 :=
    Finset.sum_eq_zero (fun e _ =>
      F.conserved (Ghat.edge e) (by simp [drossNet]) (by simp [drossNet]))
  have hsnkrow : ∑ v, F.f Ghat.snk v =
      - ∑ e : Sym2 V, F.f (Ghat.edge e) Ghat.snk := by
    rw [sum_Ghat (fun v => F.f Ghat.snk v)]
    have h1 : F.f Ghat.snk Ghat.src = - F.f Ghat.src Ghat.snk :=
      F.skew Ghat.snk Ghat.src
    rw [h1, hsrcsnk, hsnksnk, ← Finset.sum_neg_distrib]
    simp only [neg_zero, add_zero, zero_add]
    exact Finset.sum_congr rfl (fun e _ => F.skew Ghat.snk (Ghat.edge e))
  rw [hrows, hedgesum0, hsnkrow, add_zero] at htot
  have hval : F.value = ∑ v, F.f Ghat.src v := rfl
  rw [hval]
  linarith

end LeanPool.DrossFractionalTriangleDecomposition
