/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM04.Decomposition.Basic

/-!
# Linked tree-decompositions (Graph Minors IV, (3.3))

This file proves Graph Minors IV, (3.3) (pages 235–236): if `𝒮` is a good class of
star-decompositions and `(T_i, τ_i)` is a sequence of linked tree-decompositions all of whose
branchings belong to `𝒮`, then there exist `i < i'` such that `τ_i × T_i` is simulated in
`τ_{i'} × T_{i'}`.

The proof follows the paper: we form disjoint copies `T'_i` of the trees `T_i` in `ℕ × ι`, define
the infinite graph `M` and edge weights `φ_i` by `edgeOrder`, prove Claims (1) and (2), and apply
(2.2) (`TreeLemma22Statement`).
-/

public section

namespace GraphMinor.GM04

open Hypergraph

universe u

variable {α β : Type*} {R : Set (RootedHypergraph α β)}
  {sim : RootedHypergraph α β → RootedHypergraph α β → Prop}

/-- Disjoint copy of `T i` in `ℕ × ι` with first coordinate `i`. -/
noncomputable def indexedTree {ι : Type*} (T : ℕ → RootedTree ι) (i : ℕ) :
    RootedTree (ℕ × ι) where
  verts := (T i).verts.map ⟨Prod.mk i, Prod.mk_right_injective i⟩
  root := (i, (T i).root)
  parent p := (i, (T i).parent p.2)
  root_mem := Finset.mem_map_of_mem _ (T i).root_mem
  parent_mem p hp := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hp
    exact Finset.mem_map_of_mem _ ((T i).parent_mem v hv)
  parent_root := congrArg (Prod.mk i) (T i).parent_root
  exists_iterate_eq_root p hp := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hp
    obtain ⟨n, hn⟩ := (T i).exists_iterate_eq_root v hv
    refine ⟨n, ?_⟩
    have hiter : ∀ k (w : ι), ((fun q : ℕ × ι ↦ (i, (T i).parent q.2))^[k] (i, w)) =
        (i, (T i).parent^[k] w) := by
      intro k
      induction k with
      | zero => intro w; rfl
      | succ k ih =>
        intro w
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    change (fun q : ℕ × ι ↦ (i, (T i).parent q.2))^[n] (i, v) = (i, (T i).root)
    rw [hiter, hn]

private theorem indexedTree_parent_iterate {ι : Type*} (T : ℕ → RootedTree ι) (i : ℕ)
    (k : ℕ) (p : ℕ × ι) :
    (indexedTree T i).parent^[k] p =
      if k = 0 then p else (i, (T i).parent^[k] p.2) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    cases k with
    | zero =>
      simp [indexedTree]
    | succ m =>
      simp [indexedTree, Function.iterate_succ_apply]

@[simp]
private theorem mem_indexedTree_verts {ι : Type*} (T : ℕ → RootedTree ι) (i : ℕ) (p : ℕ × ι) :
    p ∈ (indexedTree T i).verts ↔ p.1 = i ∧ p.2 ∈ (T i).verts := by
  simp only [indexedTree, Finset.mem_map, Function.Embedding.coeFn_mk]
  refine ⟨?_, ?_⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨rfl, hv⟩
  · rintro ⟨rfl, hv⟩
    exact ⟨p.2, hv, Prod.eta p⟩

private theorem mem_indexedTree_edges {ι : Type*} (T : ℕ → RootedTree ι) (i : ℕ) (p : ℕ × ι) :
    p ∈ (indexedTree T i).edges ↔ p.1 = i ∧ p.2 ∈ (T i).edges := by
  rw [RootedTree.mem_edges_iff, mem_indexedTree_verts, RootedTree.mem_edges_iff]
  simp only [indexedTree, ne_eq, Prod.ext_iff, not_and]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ ↦ ⟨h1, h2, h3 h1⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨⟨h1, h2⟩, fun _ ↦ h3⟩⟩

private theorem indexedTree_reaches_iff {ι : Type*} (T : ℕ → RootedTree ι) (i : ℕ)
    (p q : ℕ × ι) :
    (indexedTree T i).Reaches p q ↔ p.1 = i ∧ q.1 = i ∧ (T i).Reaches p.2 q.2 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨hq, n, hn⟩
    obtain ⟨hq1, hq2⟩ := (mem_indexedTree_verts T i q).mp hq
    rw [indexedTree_parent_iterate] at hn
    split_ifs at hn with h0
    · subst h0
      subst hn
      exact ⟨hq1, hq1, (T i).reaches_refl hq2⟩
    · rw [Prod.ext_iff] at hn
      exact ⟨hn.1.symm, hq1, hq2, n, hn.2⟩
  · rintro ⟨hp1, hq1, hq2, n, hn⟩
    refine ⟨(mem_indexedTree_verts T i q).mpr ⟨hq1, hq2⟩, n, ?_⟩
    rw [indexedTree_parent_iterate]
    split_ifs with h0
    · subst h0
      rw [Function.iterate_zero_apply] at hn
      exact Prod.ext (hq1.trans hp1.symm) hn
    · exact Prod.ext hp1.symm hn

private theorem indexedTree_precedes_iff {ι : Type*} (T : ℕ → RootedTree ι)
    (ψ : ι → ℕ) (i : ℕ) (v w : ι) :
    (indexedTree T i).Precedes (fun p ↦ ψ p.2) (i, v) (i, w) ↔
      (T i).Precedes ψ v w := by
  simp only [RootedTree.Precedes, indexedTree_reaches_iff, true_and]
  refine and_congr ⟨fun h hv ↦ h (congrArg (Prod.mk i) hv),
      fun h hv ↦ h (Prod.mk_right_injective i hv)⟩
    (and_congr_right fun _ ↦ and_congr_right fun _ ↦ ⟨?_, ?_⟩)
  · intro h g hgv hvg hgw
    exact h (i, g) (fun h' ↦ hgv (Prod.mk_right_injective i h')) ⟨rfl, hvg⟩ ⟨rfl, hgw⟩
  · intro h p hp ⟨hp1, hvp⟩ ⟨_, hpw⟩
    have hp_eq : p = (i, p.2) := Prod.ext hp1 rfl
    have hpv : p.2 ≠ v := fun h' ↦ hp (hp_eq.trans (congrArg (Prod.mk i) h'))
    exact h p.2 hpv hvp hpw

/-- The infinite graph `M` on `ℕ × ι` in the proof of Graph Minors IV, (3.3). -/
def simGraph {ι : Type*} (sim : RootedHypergraph α β → RootedHypergraph α β → Prop)
    (T : ℕ → RootedTree ι) (τ : ℕ → ι → RootedHypergraph α β) : SimpleGraph (ℕ × ι) where
  Adj p q :=
    (p.1 < q.1 ∧ p.2 ∈ (T p.1).verts ∧ q.2 ∈ (T q.1).verts ∧
      sim (cross (τ p.1) ((T p.1).subtreeAt p.2) p.2)
        (cross (τ q.1) ((T q.1).subtreeAt q.2) q.2)) ∨
    (q.1 < p.1 ∧ q.2 ∈ (T q.1).verts ∧ p.2 ∈ (T p.1).verts ∧
      sim (cross (τ q.1) ((T q.1).subtreeAt q.2) q.2)
        (cross (τ p.1) ((T p.1).subtreeAt p.2) p.2))
  symm := ⟨fun _ _ h ↦ h.symm⟩
  loopless := ⟨fun p h ↦ by rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> exact lt_irrefl p.1 h⟩

private theorem simGraph_adj_of_lt {ι : Type*}
    {sim : RootedHypergraph α β → RootedHypergraph α β → Prop}
    {T : ℕ → RootedTree ι} {τ : ℕ → ι → RootedHypergraph α β}
    {i i' : ℕ} (hii' : i < i') {u w : ι} :
    (simGraph sim T τ).Adj (i, u) (i', w) ↔
      u ∈ (T i).verts ∧ w ∈ (T i').verts ∧
        sim (cross (τ i) ((T i).subtreeAt u) u) (cross (τ i') ((T i').subtreeAt w) w) := by
  simp only [simGraph, hii', true_and]
  refine ⟨?_, Or.inl⟩
  rintro (h | ⟨h, _⟩)
  · exact h
  · exact absurd hii' (not_lt_of_gt h)

private theorem cross_subtreeAt_mem_R {ι : Type*}
    {𝒮 : Set (RootedTree ι × (ι → RootedHypergraph α β))} (h𝒮 : IsGood R sim 𝒮)
    {T : ℕ → RootedTree ι} {τ : ℕ → ι → RootedHypergraph α β}
    (hbr : ∀ i, ∀ s ∈ (T i).verts, ((T i).starAt s, branching (T i) (τ i) s) ∈ 𝒮)
    (i : ℕ) {s : ι} (hs : s ∈ (T i).verts) :
    cross (τ i) ((T i).subtreeAt s) s ∈ R := by
  have h := h𝒮.2.1 ((T i).starAt s, branching (T i) (τ i) s) (hbr i s hs)
  dsimp only at h
  rwa [cross_branching_eq (T i) (τ i) hs] at h

/-- Graph Minors IV, (3.3), Claim (1) (page 236): if `i < i'`, `u ∈ V(T_i)` is `M`-adjacent to
`w ∈ V(T_{i'})`, and `v ∈ V(T_{i'})` precedes `w`, then `u` is `M`-adjacent to `v`. -/
theorem theorem_3_3_claim_1 {ι : Type*} (hA2 : Axiom2 R sim)
    {𝒮 : Set (RootedTree ι × (ι → RootedHypergraph α β))} (h𝒮 : IsGood R sim 𝒮)
    {T : ℕ → RootedTree ι} {τ : ℕ → ι → RootedHypergraph α β}
    (hlinked : ∀ i, IsLinked sim (T i) (τ i) (T i).edges)
    (hbr : ∀ i, ∀ s ∈ (T i).verts, ((T i).starAt s, branching (T i) (τ i) s) ∈ 𝒮)
    {i i' : ℕ} (hii' : i < i') {u w v : ℕ × ι}
    (hu : u ∈ (indexedTree T i).verts) (hw : w ∈ (indexedTree T i').verts)
    (hadj : (simGraph sim T τ).Adj u w)
    (hprec : (indexedTree T i').Precedes (fun p ↦ edgeOrder (T i') (τ i') p.2) v w) :
    (simGraph sim T τ).Adj u v := by
  rcases u with ⟨iu, u2⟩
  rcases w with ⟨iw, w2⟩
  rcases v with ⟨iv, v2⟩
  obtain ⟨rfl, hu2⟩ := (mem_indexedTree_verts T i (iu, u2)).mp hu
  obtain ⟨rfl, hw2⟩ := (mem_indexedTree_verts T i' (iw, w2)).mp hw
  dsimp only at hu2 hw2 hii' hprec
  have hv1 : iw = iv := ((indexedTree_reaches_iff T iw (iv, v2) (iw, w2)).mp hprec.2.1).1.symm
  subst hv1
  rw [indexedTree_precedes_iff] at hprec
  obtain ⟨hvr, hvw, hord, hmin⟩ := hprec
  have hv2 : v2 ∈ (T iw).verts := (T iw).reaches_mem_left hvw
  have hve : v2 ∈ (T iw).edges := (T iw).mem_edges_iff.mpr ⟨hv2, hvr⟩
  have hwe : w2 ∈ (T iw).edges := by
    refine (T iw).mem_edges_iff.mpr ⟨hw2, ?_⟩
    rintro rfl
    exact hvr ((T iw).reaches_root_iff.mp hvw)
  rw [simGraph_adj_of_lt hii'] at hadj ⊢
  refine ⟨hu2, hv2, ?_⟩
  have hsim_wv : sim (cross (τ iw) ((T iw).subtreeAt w2) w2)
      (cross (τ iw) ((T iw).subtreeAt v2) v2) := by
    refine hlinked iw w2 hwe v2 hve hvw hord.symm ?_
    rintro g ⟨⟨hvg, hgw⟩, _⟩
    by_cases hgv : g = v2
    · subst hgv
      exact le_of_eq hord.symm
    · exact hmin g hgv hvg hgw
  exact hA2.2 _ (cross_subtreeAt_mem_R h𝒮 hbr iu hu2)
    _ (cross_subtreeAt_mem_R h𝒮 hbr iw hw2)
    _ (cross_subtreeAt_mem_R h𝒮 hbr iw hv2) hadj.2.2 hsim_wv

/-- Graph Minors IV, (3.3), Claim (2) (page 236): there is no infinite `M`-stable set `X` meeting
each `V(T_i)` in at most one vertex such that the set of heads of edges with tails in `X` is
`M`-rich. -/
theorem theorem_3_3_claim_2 {ι : Type*} (hA2 : Axiom2 R sim)
    {𝒮 : Set (RootedTree ι × (ι → RootedHypergraph α β))} (h𝒮 : IsGood R sim 𝒮)
    {T : ℕ → RootedTree ι} {τ : ℕ → ι → RootedHypergraph α β}
    (hbr : ∀ i, ∀ s ∈ (T i).verts, ((T i).starAt s, branching (T i) (τ i) s) ∈ 𝒮)
    {X : Set (ℕ × ι)} (hX_inf : X.Infinite) (hX_indep : (simGraph sim T τ).IsIndepSet X)
    (hX_sub : X ⊆ ⋃ i, ((indexedTree T i).verts : Set (ℕ × ι)))
    (hX_subsingle : ∀ i, (X ∩ (indexedTree T i).verts).Subsingleton) :
    ¬ IsRich (simGraph sim T τ)
      {v | ∃ i, v ∈ (indexedTree T i).edges ∧ (indexedTree T i).parent v ∈ X} := by
  classical
  intro hrich
  have h_mem_verts : ∀ p ∈ X, p.2 ∈ (T p.1).verts := by
    intro p hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hX_sub hp)
    obtain ⟨rfl, hp2⟩ := (mem_indexedTree_verts T i p).mp hi
    exact hp2
  have h_fst_injOn : Set.InjOn Prod.fst X := by
    intro p hp q hq (heq : p.1 = q.1)
    have hp' : p ∈ X ∩ (indexedTree T p.1).verts :=
      ⟨hp, (mem_indexedTree_verts T p.1 p).mpr ⟨rfl, h_mem_verts p hp⟩⟩
    have hq' : q ∈ X ∩ (indexedTree T p.1).verts :=
      ⟨hq, (mem_indexedTree_verts T p.1 q).mpr ⟨heq.symm, heq ▸ h_mem_verts q hq⟩⟩
    exact hX_subsingle p.1 hp' hq'
  have hI_inf : (Prod.fst '' X).Infinite := hX_inf.image h_fst_injOn
  have hX_nonempty : ∃ i₀ u₀, (i₀, u₀) ∈ X := by
    obtain ⟨⟨i₀, u₀⟩, h₀⟩ := hX_inf.nonempty
    exact ⟨i₀, u₀, h₀⟩
  obtain ⟨i₀, u₀, hu₀⟩ := hX_nonempty
  have h_exists_gt : ∀ B : ℕ, ∃ i, B < i ∧ ∃ u, (i, u) ∈ X := by
    intro B
    obtain ⟨i, ⟨p, hp, rfl⟩, hiB⟩ :=
      (hI_inf.sdiff (Set.finite_le_nat B)).nonempty
    exact ⟨p.1, not_le.mp hiB, p.2, hp⟩
  choose nextIdx hnextIdx_lt hnextIdx_mem using h_exists_gt
  let idx : ℕ → ℕ := fun j ↦ Nat.rec i₀ (fun _ prev ↦ nextIdx prev) j
  have hidx_mono : StrictMono idx := strictMono_nat_of_lt_succ fun j ↦ hnextIdx_lt (idx j)
  have hidx_mem : ∀ j, ∃ u, (idx j, u) ∈ X := by
    intro j
    cases j with
    | zero => exact ⟨u₀, hu₀⟩
    | succ m => exact hnextIdx_mem (idx m)
  choose u huX using hidx_mem
  have hu_verts : ∀ j, u j ∈ (T (idx j)).verts := fun j ↦ h_mem_verts (idx j, u j) (huX j)
  let x : ℕ → RootedTree ι × (ι → RootedHypergraph α β) :=
    fun j ↦ ((T (idx j)).starAt (u j), branching (T (idx j)) (τ (idx j)) (u j))
  have hx_mem : ∀ j, x j ∈ 𝒮 := fun j ↦ hbr (idx j) (u j) (hu_verts j)
  have h_not_ws : ¬ WellSimulated sim (⋃ j, tips (x j).1 (x j).2) := by
    intro hws
    obtain ⟨j, j', hjj', hsim⟩ := h𝒮.2.2.2 x hx_mem hws
    rw [cross_branching_eq (T (idx j)) (τ (idx j)) (hu_verts j),
      cross_branching_eq (T (idx j')) (τ (idx j')) (hu_verts j')] at hsim
    have hne : (idx j, u j) ≠ (idx j', u j') := fun h ↦
      ne_of_lt (hidx_mono hjj') (congrArg Prod.fst h)
    have hadj : (simGraph sim T τ).Adj (idx j, u j) (idx j', u j') :=
      (simGraph_adj_of_lt (hidx_mono hjj')).mpr ⟨hu_verts j, hu_verts j', hsim⟩
    exact hX_indep (huX j) (huX j') hne hadj
  unfold WellSimulated at h_not_ws
  push Not at h_not_ws
  obtain ⟨L, hL_mem, hL_not_sim⟩ := h_not_ws
  have hL_unpack : ∀ k, ∃ j w, w ∈ (T (idx j)).children (u j) ∧
      L k = cross (τ (idx j)) ((T (idx j)).subtreeAt w) w := by
    intro k
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hL_mem k)
    obtain ⟨w, hw, hLw⟩ := hj
    change w ∈ ((T (idx j)).starAt (u j)).edges at hw
    rw [RootedTree.starAt_edges] at hw
    refine ⟨j, w, hw, ?_⟩
    rw [hLw]
    exact branching_of_mem_children (T (idx j)) (τ (idx j)) hw
  choose j w hw_child hL_eq using hL_unpack
  let v : ℕ → ℕ × ι := fun k ↦ (idx (j k), w k)
  have hw_verts : ∀ k, w k ∈ (T (idx (j k))).verts :=
    fun k ↦ (T (idx (j k))).children_subset_verts (u (j k)) (hw_child k)
  have hv_inj : Function.Injective v := by
    intro k₁ k₂ h_eq
    by_contra hne
    have h_idx : idx (j k₁) = idx (j k₂) := congrArg Prod.fst h_eq
    have hj_eq : j k₁ = j k₂ := hidx_mono.injective h_idx
    have hw_eq : w k₁ = w k₂ := congrArg Prod.snd h_eq
    have hL_same : L k₁ = L k₂ := by rw [hL_eq k₁, hL_eq k₂, hj_eq, hw_eq]
    have hL_R : L k₁ ∈ R := by
      rw [hL_eq k₁]
      exact cross_subtreeAt_mem_R h𝒮 hbr (idx (j k₁)) (hw_verts k₁)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hL_not_sim k₁ k₂ hlt (hL_same ▸ hA2.1 (L k₁) hL_R)
    · exact hL_not_sim k₂ k₁ hgt (hL_same ▸ hA2.1 (L k₁) hL_R)
  have h_exists_next : ∀ K B : ℕ, ∃ k, K < k ∧ B < j k := by
    intro K B
    let F : Finset (ℕ × ι) := (Finset.Iic B).biUnion fun b ↦ (indexedTree T (idx b)).verts
    have h_fin : ({k : ℕ | k ≤ K} ∪ v ⁻¹' (F : Set (ℕ × ι))).Finite :=
      (Set.finite_le_nat K).union (F.finite_toSet.preimage hv_inj.injOn)
    obtain ⟨k, _, hk⟩ := (Set.infinite_univ.sdiff h_fin).nonempty
    have hk1 : K < k := not_le.mp fun hle ↦ hk (Or.inl hle)
    refine ⟨k, hk1, ?_⟩
    by_contra hle
    push Not at hle
    apply hk
    right
    change v k ∈ (F : Set (ℕ × ι))
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨j k, Finset.mem_Iic.mpr hle,
      (mem_indexedTree_verts T (idx (j k)) (v k)).mpr ⟨rfl, hw_verts k⟩⟩
  choose next hnext_K hnext_B using h_exists_next
  let subseq : ℕ → ℕ := fun m ↦ Nat.rec 0 (fun _ prev ↦ next prev (j prev)) m
  have hsub_mono : StrictMono subseq := strictMono_nat_of_lt_succ fun m ↦ hnext_K (subseq m) _
  have hjsub_mono : StrictMono (fun m ↦ j (subseq m)) :=
    strictMono_nat_of_lt_succ fun m ↦ hnext_B (subseq m) (j (subseq m))
  let v' : ℕ → ℕ × ι := fun m ↦ v (subseq m)
  have hv'_sub : Set.range v' ⊆
      {z | ∃ i, z ∈ (indexedTree T i).edges ∧ (indexedTree T i).parent z ∈ X} := by
    rintro _ ⟨m, rfl⟩
    have hwc := (T (idx (j (subseq m)))).mem_children_iff.mp (hw_child (subseq m))
    refine ⟨idx (j (subseq m)),
      (mem_indexedTree_edges T (idx (j (subseq m))) (v' m)).mpr ⟨rfl, hwc.1⟩, ?_⟩
    change (idx (j (subseq m)), (T (idx (j (subseq m)))).parent (w (subseq m))) ∈ X
    rw [hwc.2]
    exact huX (j (subseq m))
  have hv'_indep : (simGraph sim T τ).IsIndepSet (Set.range v') := by
    rintro _ ⟨m₁, rfl⟩ _ ⟨m₂, rfl⟩ _ hadj
    have h_wlog : ∀ a b, a < b → ¬ (simGraph sim T τ).Adj (v' a) (v' b) := by
      intro a b hab hadj'
      have h_lt : idx (j (subseq a)) < idx (j (subseq b)) := hidx_mono (hjsub_mono hab)
      obtain ⟨_, _, hsim⟩ := (simGraph_adj_of_lt h_lt).mp hadj'
      rw [← hL_eq (subseq a), ← hL_eq (subseq b)] at hsim
      exact hL_not_sim (subseq a) (subseq b) (hsub_mono hab) hsim
    rcases lt_trichotomy m₁ m₂ with hlt | rfl | hgt
    · exact h_wlog m₁ m₂ hlt hadj
    · exact (simGraph sim T τ).loopless.irrefl _ hadj
    · exact h_wlog m₂ m₁ hgt ((simGraph sim T τ).adj_symm hadj)
  have hv'_inf : (Set.range v').Infinite :=
    Set.infinite_range_of_injective (hv_inj.comp hsub_mono.injective)
  exact hv'_inf (hrich (Set.range v') hv'_sub hv'_indep)

/-- Graph Minors IV, (3.3). -/
theorem theorem_3_3_proof (h22 : TreeLemma22Statement.{u}) {ι : Type u}
    (_hA1 : Axiom1 R) (hA2 : Axiom2 R sim)
    (𝒮 : Set (RootedTree ι × (ι → RootedHypergraph α β))) (h𝒮 : IsGood R sim 𝒮)
    (T : ℕ → RootedTree ι) (τ : ℕ → ι → RootedHypergraph α β)
    (hdec : ∀ i, IsTreeDecomposition (cross (τ i) (T i).verts (T i).root) (T i) (τ i))
    (hlinked : ∀ i, IsLinked sim (T i) (τ i) (T i).edges)
    (hbr : ∀ i, ∀ s ∈ (T i).verts, ((T i).starAt s, branching (T i) (τ i) s) ∈ 𝒮) :
    ∃ i i', i < i' ∧
      sim (cross (τ i) (T i).verts (T i).root) (cross (τ i') (T i').verts (T i').root) := by
  obtain ⟨n, hn⟩ := h𝒮.2.2.1
  let T' : ℕ → RootedTree (ℕ × ι) := indexedTree T
  let φ : ℕ → ℕ × ι → ℕ := fun i p ↦ edgeOrder (T i) (τ i) p.2
  let M : SimpleGraph (ℕ × ι) := simGraph sim T τ
  have hdisj : Pairwise (fun i j ↦ Disjoint (T' i).verts (T' j).verts) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    have h1 := ((mem_indexedTree_verts T i p).mp hp₁).1
    have h2 := ((mem_indexedTree_verts T j p).mp hp₂).1
    exact hij (h1.symm.trans h2)
  have hφ : ∀ i, ∀ f ∈ (T' i).edges, φ i f ≤ n := by
    intro i f hf
    obtain ⟨_, hfe⟩ := (mem_indexedTree_edges T i f).mp hf
    have hfv : f.2 ∈ (T i).verts := (T i).edges_subset_verts hfe
    have h_ind : index ((T i).starAt f.2) (branching (T i) (τ i) f.2) ≤ n :=
      hn _ (hbr i f.2 hfv)
    have h_root_le : (branching (T i) (τ i) f.2 f.2).roots.length ≤
        index ((T i).starAt f.2) (branching (T i) (τ i) f.2) :=
      Finset.le_sup (f := fun s ↦ (branching (T i) (τ i) f.2 s).roots.length)
        ((T i).starAt f.2).root_mem
    rw [branching_self, ← (hdec i).edgeOrder_eq_length_roots hfe] at h_root_le
    exact h_root_le.trans h_ind
  have hM_prec : ∀ i i', i < i' → ∀ u ∈ (T' i).verts, ∀ w ∈ (T' i').verts, ∀ v,
      M.Adj u w → (T' i').Precedes (φ i') v w → M.Adj u v :=
    fun _ _ hii' _ hu _ hw _ hadj hprec ↦
      theorem_3_3_claim_1 hA2 h𝒮 hlinked hbr hii' hu hw hadj hprec
  by_contra h_no_sim
  have h_root_indep : M.IsIndepSet (Set.range fun i ↦ (T' i).root) := by
    rintro _ ⟨i, rfl⟩ _ ⟨i', rfl⟩ _ hadj
    rcases hadj with ⟨hii', _, _, hsim⟩ | ⟨hi'i, _, _, hsim⟩
    · dsimp [T', indexedTree] at hii' hsim
      rw [cross_subtreeAt_root, cross_subtreeAt_root] at hsim
      exact h_no_sim ⟨i, i', hii', hsim⟩
    · dsimp [T', indexedTree] at hi'i hsim
      rw [cross_subtreeAt_root, cross_subtreeAt_root] at hsim
      exact h_no_sim ⟨i', i, hi'i, hsim⟩
  obtain ⟨X, hX_inf, hX_indep, hX_sub, hX_subsingle, hrich⟩ :=
    h22 T' n φ M hdisj hφ hM_prec h_root_indep
  exact theorem_3_3_claim_2 hA2 h𝒮 hbr hX_inf hX_indep hX_sub hX_subsingle hrich

end GraphMinor.GM04
