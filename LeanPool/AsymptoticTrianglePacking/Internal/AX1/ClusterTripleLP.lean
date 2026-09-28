/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the **cluster-triple LP** with density capacities

The coarse-cell route to `Nibble.AX1.BlockCoverResidualCoupled` (`Nibble.CoreGapBlockCoverCoupled`)
needs the fractional triangle packing number of the regularity-reduced graph to be bounded by the
optimum of a *linear program on the cluster triples*, in which each cluster pair `(S,T)` carries the
capacity `d(S,T)·|S||T|` — the number of edges of `G` it holds.  This is strictly stronger than the
full-capacity bound `Nibble.AX1.nu3star_regularityReduced_le_cluster_capacity`: the latter charges
each pair its whole capacity independently of the other two pairs of a triple, whereas the block
construction can only realise a *coherent* allocation, one that the LP already sees.

This file supplies the two LP facts the construction consumes.

* `Nibble.AX1.clusterPairCap`, `Nibble.AX1.IsClusterTripleLP`, `Nibble.AX1.clusterLPValue` — the
  program: nonnegative weights on cluster triples, supported on triangles of the cluster graph, with
  the pair capacity constraints;
* `Nibble.AX1.exists_clusterTripleLP` — **the bridge**: `ν₃*` of the regularity-reduced graph is at
  most the value of a feasible point, up to any positive slack.  The feasible point is the
  aggregation of a near-optimal fractional packing along cluster triples, exactly as in
  `Nibble.AX1.nu3star_regularityReduced_le_host`, but with the true per-pair capacities in
  place of a
  uniform one;
* `Nibble.AX1.exists_sparse_clusterTripleLP` — **sparsification**: a feasible point can be replaced
  by one of at least the same value whose support has at most `#P.parts ^ 2` triples.  This is the
  standard "basic feasible solution" move (a linear dependency among the columns of the support is
  pushed until a coordinate vanishes), and it is what bounds, in the geometric step, the number of
  distinct block *shapes* that a single cluster pair has to accommodate: summed over all pairs, the
  number of (pair, active triple) incidences is at most `3·#P.parts²`, i.e. `O(1)` per pair on
  average.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapClusterHost
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapBlockAlloc

/-! # ClusterTripleLP -/

@[expose] public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### The program -/

/-- **The density capacity of a cluster pair**: `d(S,T)·|S|·|T|`, the number of edges of `G`
between `S` and `T`. -/
def clusterPairCap (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) : ℝ :=
  (G.edgeDensity S T : ℝ) * (#S : ℝ) * (#T : ℝ)

/-- The cluster triples through a given pair of clusters. -/
def triplesThrough (P : Finpartition (univ : Finset V))
    (S T : {S : Finset V // S ∈ P.parts}) : Finset (Finset {S : Finset V // S ∈ P.parts}) :=
  univ.filter (fun th => S ∈ th ∧ T ∈ th)

/-- **Feasibility for the cluster-triple LP**: nonnegative weights on the cluster triples, supported
on the triangles of the cluster graph, whose total through any cluster pair is at most the density
capacity of that pair. -/
def IsClusterTripleLP (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ)
    (x : Finset {S : Finset V // S ∈ P.parts} → ℝ) : Prop :=
  (∀ th, 0 ≤ x th) ∧
  (∀ th, x th ≠ 0 → th ∈ (hostGraph G P ep de).cliqueFinset 3) ∧
  (∀ S T : {S : Finset V // S ∈ P.parts}, S ≠ T →
    ∑ th ∈ triplesThrough P S T, x th ≤ clusterPairCap G (S : Finset V) (T : Finset V))

/-- The value of a point of the cluster-triple LP. -/
def clusterLPValue {P : Finpartition (univ : Finset V)}
    (x : Finset {S : Finset V // S ∈ P.parts} → ℝ) : ℝ := ∑ th, x th

/-- The support of a point of the cluster-triple LP. -/
noncomputable def clusterLPSupport {P : Finpartition (univ : Finset V)}
    (x : Finset {S : Finset V // S ∈ P.parts} → ℝ) :
    Finset (Finset {S : Finset V // S ∈ P.parts}) := univ.filter (fun th => x th ≠ 0)

/-! ### The bridge: `ν₃*` of the reduced graph is below the LP -/

/-- The fibre decomposition of a sum over the triangles of the reduced graph along cluster
triples. -/
private theorem sum_fiber_hostTri (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ)
    (f : Finset V → ℝ) (A : Finset (Finset {S : Finset V // S ∈ P.parts})) :
    ∑ th ∈ A, (∑ t ∈ ((G.regularityReduced P ep de).cliqueFinset 3).filter
        (fun t => hostTri P t = th), f t)
      = ∑ t ∈ ((G.regularityReduced P ep de).cliqueFinset 3).filter
          (fun t => hostTri P t ∈ A), f t := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := hostTri P)
    (s := ((G.regularityReduced P ep de).cliqueFinset 3).filter (fun t => hostTri P t ∈ A))
    (t := A) (fun t ht => (Finset.mem_filter.mp ht).2) f]
  refine Finset.sum_congr rfl fun th hth => ?_
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext t
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨ht, rfl⟩; exact ⟨⟨ht, hth⟩, rfl⟩
  · rintro ⟨⟨ht, -⟩, hEq⟩; exact ⟨ht, hEq⟩

/-- **The bridge.**  For every slack `η > 0` there is a feasible point of the cluster-triple LP
whose value is within `η` of `ν₃*` of the regularity-reduced graph. -/
theorem exists_clusterTripleLP (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ x : Finset {S : Finset V // S ∈ P.parts} → ℝ, IsClusterTripleLP G P ep de x ∧
      nu3star (G.regularityReduced P ep de) ≤ clusterLPValue x + η := by
  classical
  set R : SimpleGraph V := G.regularityReduced P ep de with hR
  have hne : Set.Nonempty
      {x : ℝ | ∃ w, IsFracPacking R w ∧ x = ∑ T ∈ triangleHypergraphE R, w T} :=
    ⟨0, ⟨fun _ => 0, isFracPacking_zero R, by simp⟩⟩
  obtain ⟨v, ⟨w, hw, rfl⟩, hv⟩ :=
    exists_lt_of_lt_csSup hne (show nu3star R - η < nu3star R by linarith)
  refine ⟨fun th => ∑ t ∈ (R.cliqueFinset 3).filter (fun t => hostTri P t = th),
    w (t.powersetCard 2), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact fun th => Finset.sum_nonneg fun t _ => hw.1 _
  · -- the support consists of cluster triples of triangles
    intro th hth
    by_contra hnot
    refine hth (Finset.sum_eq_zero fun t ht => ?_)
    rw [Finset.mem_filter] at ht
    exact absurd (ht.2 ▸ hostTri_mem_cliqueFinset G P ep de ht.1) hnot
  · -- the capacity constraint
    intro S T hST
    have hEq : ∑ th ∈ triplesThrough P S T,
          (∑ t ∈ (R.cliqueFinset 3).filter (fun t => hostTri P t = th), w (t.powersetCard 2))
        = ∑ t ∈ (R.cliqueFinset 3).filter (fun t => hostTri P t ∈ triplesThrough P S T),
            w (t.powersetCard 2) :=
      sum_fiber_hostTri G P ep de (fun t => w (t.powersetCard 2)) _
    rw [hEq]
    -- the triangles counted are injectively charged to hyperedges through the pair
    set C := (R.cliqueFinset 3).filter (fun t => hostTri P t ∈ triplesThrough P S T) with hC
    have hinj : Set.InjOn (fun t : Finset V => t.powersetCard 2) (C : Set (Finset V)) :=
      (triangle_powersetCard_two_injOn R).mono (by
        intro t ht
        exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).1)
    have himg : ∑ t ∈ C, w (t.powersetCard 2)
        = ∑ T' ∈ C.image (fun t => t.powersetCard 2), w T' := (Finset.sum_image hinj).symm
    have hsub : C.image (fun t => t.powersetCard 2)
        ⊆ (triangleHypergraphE R).filter
          (fun T' => ∃ a ∈ (S : Finset V), ∃ b ∈ (T : Finset V), ({a, b} : Finset V) ∈ T') := by
      intro T' hT'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hT'
      rw [Finset.mem_filter] at ht
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_image_of_mem _ ht.1, ?_⟩
      have h2 := Finset.mem_filter.mp ht.2
      exact exists_edge_of_mem_hostTri P hST h2.2.1 h2.2.2
    have hmono : ∑ T' ∈ C.image (fun t => t.powersetCard 2), w T'
        ≤ ∑ T' ∈ (triangleHypergraphE R).filter
            (fun T' => ∃ a ∈ (S : Finset V), ∃ b ∈ (T : Finset V), ({a, b} : Finset V) ∈ T'),
            w T' :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun T' _ _ => hw.1 T'
    have hcapR := sum_fracPacking_cluster_pair_le R hw (S : Finset V) (T : Finset V)
    have hmono2 : (#(R.interedges (S : Finset V) (T : Finset V)) : ℝ)
        ≤ (#(G.interedges (S : Finset V) (T : Finset V)) : ℝ) := by
      exact_mod_cast card_interedges_mono (G := G) (H := R)
        (hR ▸ SimpleGraph.regularityReduced_le) (S : Finset V) (T : Finset V)
    have hcapG : (#(G.interedges (S : Finset V) (T : Finset V)) : ℝ)
        = clusterPairCap G (S : Finset V) (T : Finset V) :=
      (edgeDensity_mul_card_mul_card G (S : Finset V) (T : Finset V)).symm
    rw [himg]
    rw [hcapG] at hmono2
    linarith
  · -- the value
    have hval : clusterLPValue (P := P)
        (fun th => ∑ t ∈ (R.cliqueFinset 3).filter (fun t => hostTri P t = th),
          w (t.powersetCard 2))
        = ∑ T ∈ triangleHypergraphE R, w T := by
      rw [clusterLPValue, sum_triangleHypergraphE R w]
      exact sum_fiber_hostTri G P ep de (fun t => w (t.powersetCard 2)) univ |>.trans
        (Finset.sum_congr (Finset.filter_true_of_mem fun t _ => Finset.mem_univ _) fun _ _ => rfl)
    rw [hval]
    linarith

/-! ### Sparsification -/

/-- The column of a cluster triple: its indicator on ordered pairs of distinct clusters. -/
private def lpCol (P : Finpartition (univ : Finset V))
    (th : Finset {S : Finset V // S ∈ P.parts}) :
    ({S : Finset V // S ∈ P.parts} × {S : Finset V // S ∈ P.parts}) → ℝ :=
  fun p => if p.1 ≠ p.2 ∧ p.1 ∈ th ∧ p.2 ∈ th then 1 else 0

/-- The pair sums of a weighting, read off the columns. -/
private theorem sum_triplesThrough_eq (P : Finpartition (univ : Finset V))
    (x : Finset {S : Finset V // S ∈ P.parts} → ℝ)
    {S T : {S : Finset V // S ∈ P.parts}} (hST : S ≠ T) :
    ∑ th ∈ triplesThrough P S T, x th = ∑ th, x th * lpCol P th (S, T) := by
  classical
  rw [triplesThrough, Finset.sum_filter]
  refine Finset.sum_congr rfl fun th _ => ?_
  by_cases h : S ∈ th ∧ T ∈ th
  · simp [lpCol, h, hST]
  · simp [lpCol, h, hST]

/-- A triple in the support of a feasible point contains two distinct clusters. -/
private theorem exists_pair_of_support (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ)
    {y : Finset {S : Finset V // S ∈ P.parts} → ℝ} (hy : IsClusterTripleLP G P ep de y)
    {th : Finset {S : Finset V // S ∈ P.parts}} (hth : th ∈ clusterLPSupport y) :
    ∃ S T : {S : Finset V // S ∈ P.parts}, S ≠ T ∧ th ∈ triplesThrough P S T := by
  classical
  have hne : y th ≠ 0 := (Finset.mem_filter.mp hth).2
  have htri := hy.2.1 th hne
  have hcard : #th = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp htri).card_eq
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
  exact ⟨a, b, hab, by simp [triplesThrough]⟩

/-- **Sparsification of the cluster-triple LP.**  A feasible point can be replaced by a feasible
point of at least the same value whose support has at most `#P.parts ^ 2` triples. -/
theorem exists_sparse_clusterTripleLP (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ)
    {x : Finset {S : Finset V // S ∈ P.parts} → ℝ} (hx : IsClusterTripleLP G P ep de x) :
    ∃ y : Finset {S : Finset V // S ∈ P.parts} → ℝ, IsClusterTripleLP G P ep de y ∧
      clusterLPValue x ≤ clusterLPValue y ∧ #(clusterLPSupport y) ≤ #P.parts ^ 2 := by
  classical
  set Good : ℕ → Prop := fun n => ∃ y, IsClusterTripleLP G P ep de y ∧
    clusterLPValue x ≤ clusterLPValue y ∧ #(clusterLPSupport y) = n with hGoodDef
  have hGne : ∃ n, Good n := ⟨_, x, hx, le_rfl, rfl⟩
  obtain ⟨y, hy, hxy, hysupp⟩ := Nat.find_spec hGne
  have hmin : ∀ m, m < Nat.find hGne → ¬ Good m := fun m hm => Nat.find_min hGne hm
  refine ⟨y, hy, hxy, ?_⟩
  by_contra hbig
  push Not at hbig
  -- more support than the dimension of the pair space: a linear dependency among the columns
  have hdim : Module.finrank ℝ
      (({S : Finset V // S ∈ P.parts} × {S : Finset V // S ∈ P.parts}) → ℝ) = #P.parts ^ 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, card_hostGraph_vertices, sq]
  have hnli : ¬ LinearIndependent ℝ
      (fun th : {th // th ∈ clusterLPSupport y} => lpCol P (th : Finset _)) := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [Fintype.card_coe, hdim] at this
    omega
  obtain ⟨g, hg0, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hnli
  -- extend the relation by zero off the support
  set z : Finset {S : Finset V // S ∈ P.parts} → ℝ :=
    fun th => if h : th ∈ clusterLPSupport y then g ⟨th, h⟩ else 0 with hzdef
  have hzsupp : ∀ th, z th ≠ 0 → th ∈ clusterLPSupport y := by
    intro th hth
    by_contra h
    rw [hzdef] at hth
    simp only [dite_eq_right h, ne_eq, not_true_eq_false] at hth
  have hzcoe : ∀ i : {th // th ∈ clusterLPSupport y}, z (i : Finset _) = g i := by
    intro i
    rw [hzdef]
    simp [i.2]
  have hzne : z (i₀ : Finset _) ≠ 0 := by rw [hzcoe i₀]; exact hi₀
  have hzrel : ∀ S T : {S : Finset V // S ∈ P.parts}, S ≠ T →
      ∑ th ∈ triplesThrough P S T, z th = 0 := by
    intro S T hST
    have hcol : ∑ i : {th // th ∈ clusterLPSupport y},
        g i * lpCol P (i : Finset _) (S, T) = 0 := by
      have h := congrFun hg0 (S, T)
      simpa [Finset.sum_apply] using h
    rw [sum_triplesThrough_eq P z hST]
    have hsplit : ∑ th, z th * lpCol P th (S, T)
        = ∑ th ∈ clusterLPSupport y, z th * lpCol P th (S, T) := by
      refine (Finset.sum_subset (Finset.subset_univ _) fun th _ hth => ?_).symm
      have hz : z th = 0 := by
        by_contra hzz
        exact hth (hzsupp th hzz)
      rw [hz, zero_mul]
    rw [hsplit, ← Finset.sum_coe_sort (clusterLPSupport y)
      (fun th => z th * lpCol P th (S, T))]
    rw [← hcol]
    exact Finset.sum_congr rfl fun i _ => by rw [hzcoe i]
  -- choose the sign so that the value does not decrease
  obtain ⟨u, husupp, hurel, huval, th₀, hth₀⟩ :
      ∃ u : Finset {S : Finset V // S ∈ P.parts} → ℝ,
        (∀ th, u th ≠ 0 → th ∈ clusterLPSupport y) ∧
        (∀ S T : {S : Finset V // S ∈ P.parts}, S ≠ T → ∑ th ∈ triplesThrough P S T, u th = 0) ∧
        0 ≤ ∑ th, u th ∧ ∃ th₀, u th₀ ≠ 0 := by
    by_cases hsum : 0 ≤ ∑ th, z th
    · exact ⟨z, hzsupp, hzrel, hsum, (i₀ : Finset _), hzne⟩
    · refine ⟨fun th => -z th, fun th hth => hzsupp th (by simpa using hth), ?_, ?_,
        (i₀ : Finset _), by simpa using hzne⟩
      · intro S T hST
        simp only [Finset.sum_neg_distrib, hzrel S T hST, neg_zero]
      · simp only [Finset.sum_neg_distrib]
        linarith only [not_le.mp hsum]
  by_cases hallpos : ∀ th, 0 ≤ u th
  · -- a nonnegative relation must vanish: its pair sum is zero
    exfalso
    have hpos : 0 < u th₀ := lt_of_le_of_ne (hallpos th₀) (Ne.symm hth₀)
    obtain ⟨S, T, hST, hmem⟩ := exists_pair_of_support G P ep de hy (husupp th₀ hth₀)
    have hle : u th₀ ≤ ∑ th ∈ triplesThrough P S T, u th :=
      Finset.single_le_sum (fun th _ => hallpos th) hmem
    rw [hurel S T hST] at hle
    linarith
  · -- push along the relation until a coordinate vanishes
    push Not at hallpos
    obtain ⟨θ, hθ⟩ := hallpos
    set Neg : Finset (Finset {S : Finset V // S ∈ P.parts}) := univ.filter (fun th => u th < 0)
      with hNegDef
    have hNegne : Neg.Nonempty := ⟨θ, by simp [hNegDef, hθ]⟩
    obtain ⟨θ₁, hθ₁mem, hθ₁min⟩ := Finset.exists_min_image Neg (fun th => y th / (-u th)) hNegne
    set t : ℝ := y θ₁ / (-u θ₁) with htdef
    have hθ₁neg : u θ₁ < 0 := (Finset.mem_filter.mp hθ₁mem).2
    have hθ₁supp : θ₁ ∈ clusterLPSupport y := husupp θ₁ (ne_of_lt hθ₁neg)
    have hyθ₁ : 0 < y θ₁ :=
      lt_of_le_of_ne (hy.1 θ₁) (Ne.symm (Finset.mem_filter.mp hθ₁supp).2)
    have ht0 : 0 < t := div_pos hyθ₁ (by linarith)
    set y' : Finset {S : Finset V // S ∈ P.parts} → ℝ := fun th => y th + t * u th with hy'def
    have hy'nonneg : ∀ th, 0 ≤ y' th := by
      intro th
      rcases lt_or_ge (u th) 0 with hneg | hpos
      · have hmemN : th ∈ Neg := by simp [hNegDef, hneg]
        have hle := hθ₁min th hmemN
        have hposth : (0:ℝ) < -u th := by linarith
        have h1 : t * (-u th) ≤ y th := by
          have h2 := mul_le_mul_of_nonneg_right hle hposth.le
          rwa [div_mul_cancel₀ _ (ne_of_gt hposth)] at h2
        simp only [hy'def]
        nlinarith only [h1]
      · have : 0 ≤ t * u th := mul_nonneg ht0.le hpos
        simp only [hy'def]
        linarith [hy.1 th]
    have hy'supp : ∀ th, y' th ≠ 0 → th ∈ clusterLPSupport y := by
      intro th hth
      by_contra hnot
      have h1 : y th = 0 := by
        by_contra h
        exact hnot (by simp [clusterLPSupport, h])
      have h2 : u th = 0 := by
        by_contra h
        exact hnot (husupp th h)
      simp [hy'def, h1, h2] at hth
    have hy'sum : ∀ S T : {S : Finset V // S ∈ P.parts}, S ≠ T →
        ∑ th ∈ triplesThrough P S T, y' th = ∑ th ∈ triplesThrough P S T, y th := by
      intro S T hST
      simp only [hy'def, Finset.sum_add_distrib, ← Finset.mul_sum, hurel S T hST, mul_zero,
        add_zero]
    have hy'val : ∑ th, y' th = (∑ th, y th) + t * ∑ th, u th := by
      simp only [hy'def, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hy'feas : IsClusterTripleLP G P ep de y' := by
      refine ⟨hy'nonneg, fun th hth => hy.2.1 th ?_, fun S T hST => ?_⟩
      · exact (Finset.mem_filter.mp (hy'supp th hth)).2
      · rw [hy'sum S T hST]; exact hy.2.2 S T hST
    have hy'value : clusterLPValue x ≤ clusterLPValue y' := by
      have : 0 ≤ t * ∑ th, u th := mul_nonneg ht0.le huval
      simp only [clusterLPValue] at hxy ⊢
      rw [hy'val]
      linarith
    -- the support has strictly shrunk
    have hsubset : clusterLPSupport y' ⊆ clusterLPSupport y := by
      intro th hth
      exact hy'supp th (Finset.mem_filter.mp hth).2
    have hcancel : y θ₁ / (-u θ₁) * (-u θ₁) = y θ₁ :=
      div_mul_cancel₀ _ (by linarith : (-u θ₁) ≠ 0)
    have hθ₁zero : y' θ₁ = 0 := by
      simp only [hy'def, htdef]
      linear_combination -hcancel
    have hstrict : clusterLPSupport y' ⊂ clusterLPSupport y := by
      refine ⟨hsubset, fun hsup => ?_⟩
      have : θ₁ ∈ clusterLPSupport y' := hsup hθ₁supp
      exact (Finset.mem_filter.mp this).2 hθ₁zero
    have hlt : #(clusterLPSupport y') < Nat.find hGne := by
      rw [← hysupp]
      exact Finset.card_lt_card hstrict
    exact hmin _ hlt ⟨y', hy'feas, hy'value, rfl⟩

/-- **The bridge and the sparsification, combined.**  For every slack `η > 0` there is a feasible
point of the cluster-triple LP with at most `#P.parts ^ 2` triples in its support whose value is
within `η` of `ν₃*` of the regularity-reduced graph. -/
theorem exists_sparse_clusterTripleLP_nu3star (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ y : Finset {S : Finset V // S ∈ P.parts} → ℝ, IsClusterTripleLP G P ep de y ∧
      #(clusterLPSupport y) ≤ #P.parts ^ 2 ∧
      nu3star (G.regularityReduced P ep de) ≤ clusterLPValue y + η := by
  obtain ⟨x, hx, hxnu⟩ := exists_clusterTripleLP G P ep de hη
  obtain ⟨y, hy, hxy, hcard⟩ := exists_sparse_clusterTripleLP G P ep de hx
  exact ⟨y, hy, hcard, by linarith⟩

/-! ### The covering clause, in LP form -/

/-- **The covering clause of the residual, in LP form.**  If the total *value* `τ²·xyz` of a family
of block sub-triples recovers the value of a point of the cluster-triple LP that itself dominates
`ν₃*` (up to `η`), then the covering clause of `Nibble.AX1.BlockCoverResidualCoupled` holds with
total error `E + η + k·(2τ + 1)`.

This is the LP-form replacement of `Nibble.AX1.nu3star_le_cover_of_family_value`, whose right-hand
side is the *full* cluster capacity: the full capacity is not reachable by a coherent family of
block sub-triples — a cluster triple with `d(S,T) = 1` and `d(S,Y) = d(T,Y) = θ` cannot tile
`S × T` — whereas the LP optimum is exactly what the coarse-cell construction realises. -/
theorem nu3star_le_cover_of_family_lp_value
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finpartition (univ : Finset V))
    {ep de ep₀ de₀ α τ E η : ℝ} {k : ℕ} (U W X A B C : ℕ → Finset V) (hτ : 0 ≤ τ)
    (hgrid : ∀ i < k, IsGridSubTriple G P ep₀ de₀ α τ (U i) (W i) (X i) (A i) (B i) (C i))
    {x : Finset {S : Finset V // S ∈ P.parts} → ℝ}
    (hnu : nu3star (G.regularityReduced P ep de) ≤ clusterLPValue x + η)
    (hval : clusterLPValue x
        ≤ (∑ i ∈ Finset.range k, τ ^ 2 * ((G.edgeDensity (U i) (W i) : ℝ)
            * (G.edgeDensity (U i) (X i) : ℝ) * (G.edgeDensity (W i) (X i) : ℝ))) + E) :
    nu3star (G.regularityReduced P ep de)
      ≤ (∑ i ∈ Finset.range k,
          ((G.edgeDensity (U i) (W i) : ℝ) * (#(A i) : ℝ) * (#(B i) : ℝ)
            + (G.edgeDensity (U i) (X i) : ℝ) * (#(A i) : ℝ) * (#(C i) : ℝ)
            + (G.edgeDensity (W i) (X i) : ℝ) * (#(B i) : ℝ) * (#(C i) : ℝ))) / 3
        + (E + η + (k : ℝ) * (2 * τ + 1)) := by
  classical
  have hterm : ∀ i ∈ Finset.range k,
      τ ^ 2 * ((G.edgeDensity (U i) (W i) : ℝ) * (G.edgeDensity (U i) (X i) : ℝ)
          * (G.edgeDensity (W i) (X i) : ℝ))
        ≤ ((G.edgeDensity (U i) (W i) : ℝ) * (#(A i) : ℝ) * (#(B i) : ℝ)
            + (G.edgeDensity (U i) (X i) : ℝ) * (#(A i) : ℝ) * (#(C i) : ℝ)
            + (G.edgeDensity (W i) (X i) : ℝ) * (#(B i) : ℝ) * (#(C i) : ℝ)) / 3
          + (2 * τ + 1) := by
    intro i hi
    have h := cover_approx_of_gridSubTriple G P hτ (hgrid i (Finset.mem_range.mp hi))
    have := (abs_le.mp h).1
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_range,
    ← Finset.sum_div] at hsum
  linarith

/-! ### Axiom check -/

section AxCheck






end AxCheck

end Nibble.AX1
