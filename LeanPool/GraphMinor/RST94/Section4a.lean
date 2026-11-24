/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.RST94.Section3d
public import LeanPool.GraphMinor.RST94.Contract

/-!
# Section 4 of "Quickly excluding a planar graph": nodules, and Case 2 of (4.1)

Robertson, Seymour and Thomas, J. Combin. Theory Ser. B 62 (1994), pages 334–337. A nodule `G, 𝒯, Z`
is written with an injective `z : ι → α` with
range `Z`, so that the linkage of a residual nodule joins `z i` to `z' i`.
-/

@[expose] public section

namespace GraphMinor.RST94

open Hypergraph GM10 Set

variable {α β ι : Type*} {G A B : Hypergraph α β} {θ : ℕ} {T : Set (Hypergraph α β × Hypergraph α
  β)}

/-- A nodule of order `θ` (page 335): `Z` is free relative to the tangle `𝒯`. -/
structure Nodule (G : Hypergraph α β) (T : Set (Hypergraph α β × Hypergraph α β)) (θ : ℕ) (z : ι
  → α) : Prop where
  tangle : IsTangle G θ T
  inj : Function.Injective z
  free : IsFreeSet G T θ (range z)

/-- `G', 𝒯', Z'` is a residual nodule of `G, 𝒯, Z` (page 335). The paper's condition that `G'` is a
subgraph of `G \ Z` is the two conditions `le`
and `avoid`, since each end of an edge of `G'` is a vertex of `G'`. The paths `P i` from `z i` to
`z' i` are the linkage. -/
structure Residual (G : Hypergraph α β) (T : Set (Hypergraph α β × Hypergraph α β)) (θ : ℕ) (z : ι
  → α)
    (G' : Hypergraph α β) (T' : Set (Hypergraph α β × Hypergraph α β)) (θ' : ℕ) (z' : ι
      → α) : Prop where
  nodule : Nodule G' T' θ' z'
  le : G' ≤ G
  avoid : ∀ i, z i ∉ G'.vertexSet
  conformal : Conformal G G' T T' θ θ'
  link : ∃ P : ∀ i, G.skeleton.Walk (z i) (z' i), (∀ i, (P i).IsPath) ∧
    (∀ i, ∀ x ∈ (P i).support, x ∈ G'.vertexSet → x = z' i) ∧
    Pairwise fun i j => Disjoint {x | x ∈ (P i).support} {x | x ∈ (P j).support}

theorem ncard_range [Fintype ι] {z : ι → α} (hz : Function.Injective z) : (range z).ncard
  = Fintype.card ι := by
  rw [← image_univ, ncard_image_of_injective _ hz, ncard_univ, Nat.card_eq_fintype_card]

variable [Fintype ι]

/-- The claim in Case 2 of (4.1) (page 336): `X = V(A ∩ B)` is free relative to `𝒯₀`. -/
theorem free_of_sep {Z : Set α} (hT : IsTangle G θ T) (hfree : IsFreeSet G T θ Z) (hAB : (A, B) ∈ T)
    (ho : separationOrder A B = Z.ncard) (hZ : Z ⊆ A.vertexSet) : IsFreeSet G T θ (A ∩ B).vertexSet
      := by
  have hs := hT.isSeparation hAB
  have hc : (A ∩ B).vertexSet.ncard = Z.ncard := ho
  have hX : (A ∩ B).vertexSet ⊆ G.vertexSet := fun x hx => hs.left_le.vertexSet_subset hx.1
  refine ⟨hX, hc ▸ hfree.2.1, fun A₀ B₀ hm hXA => ?_⟩
  by_contra hlt
  push Not at hlt
  have hs₀ := hT.isSeparation hm
  have hs₁ : G.IsSeparation (A ∪ A₀) (B ∩ B₀) := hs.union_inter hs₀
  have hsub : ((A ∪ A₀) ∩ (B ∩ B₀)).vertexSet ⊆ (A₀ ∩ B₀).vertexSet := by
    rintro x ⟨hx | hx, hxB, hxB₀⟩
    · exact ⟨hXA ⟨hx, hxB⟩, hxB₀⟩
    · exact ⟨hx, hxB₀⟩
  have ho₁ : separationOrder (A ∪ A₀) (B ∩ B₀) < Z.ncard :=
    (order_le_of_subset (A₀ ∩ B₀).vertexSet_finite hsub).trans_lt (hc ▸ hlt)
  have hθ := hT.order_lt hAB
  have hn : (A ∪ A₀, B ∩ B₀) ∉ T := fun hm₁ => by
    have := hfree.2.2 hm₁ fun x hx => Or.inl (hZ hx)
    omega
  have hm₂ := (hT.axiom1 hs₁ (by omega)).resolve_left hn
  refine hT.axiom2 hAB hm hm₂ ?_
  rw [GM10.union_comm A A₀] at hs₁
  exact (GM10.union_comm A A₀) ▸ hs₁.union_eq

/-- The other claim in Case 2 of (4.1) (page 337): there are `|Z|` disjoint paths of `A` between `Z`
and `X = V(A ∩ B)`. -/
theorem paths_of_sep {Z : Set α} (hT : IsTangle G θ T) (hfree : IsFreeSet G T θ Z) (hAB :
  (A, B) ∈ T)
    (hZ : Z ⊆ A.vertexSet) : HasDisjointPaths A.skeleton Z (A ∩ B).vertexSet Z.ncard := by
  have hs := hT.isSeparation hAB
  refine (menger A Z (A ∩ B).vertexSet hZ (fun _ hx => hx.1) _).1 fun A₁ B₁ hs₁ hZ₁ hX₁ => ?_
  by_contra hlt
  push Not at hlt
  have hs₂ : G.IsSeparation A₁ (B ∪ B₁) := (sep_union_left hs.symm hs₁.symm).symm
  have hsub : (A₁ ∩ (B ∪ B₁)).vertexSet ⊆ (A₁ ∩ B₁).vertexSet := by
    rintro x ⟨hx, hx' | hx'⟩
    · exact ⟨hx, hX₁ ⟨hs₁.left_le.vertexSet_subset hx, hx'⟩⟩
    · exact ⟨hx, hx'⟩
  have ho := (order_le_of_subset (A₁ ∩ B₁).vertexSet_finite hsub).trans_lt hlt
  have hθ : Z.ncard ≤ θ := hfree.2.1
  have hm : (A₁, B ∪ B₁) ∈ T := GraphMinor.GM10.theorem_2_9_proof hT hAB hs₂ (by omega) (Or.inr
    (Or.inl hs₁.left_le.vertexSet_subset))
  have := hfree.2.2 hm hZ₁
  omega

/-- `A \ X ≤ G \ X` for `A ≤ G`. -/
theorem deleteVertices_mono (hA : A ≤ G) (X : Set α) : A.deleteVertices X ≤ G.deleteVertices X :=
  le_of_sets ((deleteVertices_le _ _).trans hA) (deleteVertices_le _ _)
    (fun _ hx => ⟨hA.vertexSet_subset hx.1, hx.2⟩)
    fun _f hf => ⟨hA.edgeSet_subset hf.1, fun v hv hi => hf.2 v hv (inc_le hA hf.1 hi)⟩

/-- A separation `(A, B)` of `G` gives a separation `(A \ X, B \ X)` of `G \ X`. -/
theorem IsSeparation_deleteVertices (hs : G.IsSeparation A B) (X : Set α) :
    (G.deleteVertices X).IsSeparation (A.deleteVertices X) (B.deleteVertices X) := by
  refine sep_of_sets (deleteVertices_mono hs.left_le X) (deleteVertices_mono hs.right_le X)
    (fun x hx => ?_) (fun f hf => ?_) ?_
  · exact (mem_V_or hs hx.1).imp (fun h => ⟨h, hx.2⟩) fun h => ⟨h, hx.2⟩
  · refine (mem_E_or hs hf.1).imp (fun h => ⟨h, fun v hv hi => hf.2 v hv (inc_of_le hs.left_le hi)⟩)
      fun h => ⟨h, fun v hv hi => hf.2 v hv (inc_of_le hs.right_le hi)⟩
  · exact fun f hf hf' => hs.notMem_edgeSet_right hf.1 hf'.1

/-- Case 2 of the proof of (4.1) (pages 336–337): `(A, B)` of order `|Z|` with `Z ⊆ V(A)` gives the
residual nodule on `B \ V(A ∩ B)`. -/
theorem residual_of_sep (hG : G.IsGraph) {z : ι → α} (hT : IsTangle G θ T)
  (hz : Function.Injective z)
    (hfree : IsFreeSet G T θ (range z)) (hθ : 2 * Fintype.card ι ≤ θ) (hAB : (A, B) ∈ T)
    (ho : separationOrder A B = Fintype.card ι) (hZ : range z ⊆ A.vertexSet) :
    ∃ T' z', Residual G T θ z (B.deleteVertices (A ∩ B).vertexSet) T' (θ - Fintype.card ι) z' := by
  classical
  have hs := hT.isSeparation hAB
  have hZc := ncard_range hz
  have hXfree := free_of_sep hT hfree hAB (ho.trans hZc.symm) hZ
  have hθ₁ := hT.one_le
  have hXc : (A ∩ B).vertexSet.ncard = Fintype.card ι := ho
  obtain ⟨P, hP⟩ := paths_of_sep hT hfree hAB hZ
  have hdis : Pairwise fun i j => Disjoint (pathV (P i)) (pathV (P j)) := hP
  have hstart : ∀ i, (P i).first ∈ pathV (P i) := fun i => (P i).walk.start_mem_support
  have hend : ∀ i, (P i).last ∈ pathV (P i) := fun i => (P i).walk.end_mem_support
  have hinj₁ : Function.Injective fun i => (P i).first := fun i j he => by
    by_contra hij
    exact disjoint_left.1 (hdis hij) (hstart i) ((show (P i).first = (P j).first from he) ▸ hstart
      j)
  have hinj₂ : Function.Injective fun i => (P i).last := fun i j he => by
    by_contra hij
    exact disjoint_left.1 (hdis hij) (hend i) ((show (P i).last = (P j).last from he) ▸ hend j)
  have hZfin : (range z).Finite := toFinite _
  have hZ' : ∀ i, (P i).first ∈ A.vertexSet := fun i => hZ (P i).first_mem
  have hc : ∀ i, ∃ j, (P j).first = z i := fun i =>
    exists_index _ hZfin rfl hinj₁ (fun j => (P j).first_mem) (mem_range_self i)
  choose c hc using hc
  have hcinj : Function.Injective c := fun i j he => hz (by rw [← hc i, ← hc j, he])
  let x : ι → α := fun i => (P (c i)).last
  have hxinj : Function.Injective x := hinj₂.comp hcinj
  have hrx : range x = (A ∩ B).vertexSet :=
    eq_of_subset_of_ncard_le (range_subset_iff.2 fun i => (P (c i)).last_mem)
      (by rw [ncard_range hxinj, hXc]) (A ∩ B).vertexSet_finite
  have hXsub : (A ∩ B).vertexSet ⊆ G.vertexSet := fun t ht => hs.left_le.vertexSet_subset ht.1
  have hXlt : (A ∩ B).vertexSet.ncard < θ := by omega
  obtain ⟨y, hyinj, hyV, hyadj, hyfree⟩ := theorem_2_10 hG hT x hxinj (by rw [hrx]; exact hXfree) hθ
  rw [hrx, hXc] at hyfree
  rw [hrx] at hyV
  have hTx := GraphMinor.GM10.theorem_8_5_proof hG hT hXsub hXlt
  have hcx := conformal_deleteVertices hG hT hXsub hXlt
  rw [hXc] at hTx hcx
  let X := (A ∩ B).vertexSet
  let C₀ := A.deleteVertices X
  let D := B.deleteVertices X
  have hsep : (G.deleteVertices X).IsSeparation C₀ D := IsSeparation_deleteVertices hs X
  have hempty : (C₀ ∩ D).vertexSet = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro t ⟨h₁, h₂⟩
    exact h₁.2 ⟨h₁.1, h₂.1⟩
  have h0 : separationOrder C₀ D = 0 := by
    unfold separationOrder
    rw [hempty, ncard_empty]
  have hm : (C₀, D) ∈ deleteVerticesTangle G X T θ := by
    refine ⟨hsep, ?_, (A, B), hAB, subset_rfl, rfl, rfl⟩
    change separationOrder C₀ D < θ - X.ncard
    rw [h0, show X.ncard = Fintype.card ι from hXc]
    omega
  have hTr := isTangle_restrictTangle hTx hm h0
  have hcr := conformal_restrictTangle hTx hm h0
  have hconf := Conformal.trans (deleteVertices_le _ _) hsep.right_le hT hTx hTr hcx hcr
  have hDG : D ≤ G := deleteVertices_le _ _ |>.trans hs.right_le
  have hyA : ∀ i, y i ∉ A.vertexSet := fun i hi => by
    have h₁ : IsFreeSet (G.deleteVertices X) (deleteVerticesTangle G X T θ)
      (θ - Fintype.card ι) {y i} :=
      hyfree.subset hTx (singleton_subset_iff.2 (mem_range_self i))
    have h₂ := h₁.2.2 hm (singleton_subset_iff.2 ⟨hi, (hyV i).2⟩)
    rw [ncard_singleton, h0] at h₂
    omega
  have hyD : ∀ i, y i ∈ D.vertexSet := fun i =>
    ⟨(mem_V_or hs (hyV i).1).resolve_left (hyA i), (hyV i).2⟩
  have hDA : ∀ t ∈ A.vertexSet, t ∉ D.vertexSet := fun t ht ht' => ht'.2 ⟨ht, ht'.1⟩
  refine ⟨_, y, ⟨⟨hTr, hyinj, ?_⟩, hDG, fun i => hDA _ (hZ (mem_range_self i)), hconf, ?_⟩⟩
  · refine ⟨range_subset_iff.2 hyD, hyfree.2.1, ?_⟩
    rintro _ _ ⟨A₁, B₁, hm₁, heq⟩ hY
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    have hmem := union_inter_mem hTx hm h0 hm₁
    have h₁ := hyfree.2.2 hmem fun t ht => Or.inl (hY ht).1
    refine h₁.trans (order_le_of_subset (((A₁ ∩ D) ∩ (B₁ ∩ D))).vertexSet_finite ?_)
    rintro t ⟨ht | ht, ht', htD⟩
    · exact ⟨⟨ht, htD⟩, ht', htD⟩
    · exact (ht.2 ⟨ht.1, htD.1⟩).elim
  · let R : ∀ i, G.skeleton.Walk (z i) (y i) := fun i =>
      (((P (c i)).walk.copy (hc i) rfl).mapLe (skeleton_mono hs.left_le)).concat (hyadj i)
    have hRs : ∀ i t, t ∈ (R i).support → t ∈ pathV (P (c i)) ∨ t = y i := fun i t ht => by
      simpa [R, pathV] using ht
    have hPA : ∀ i, pathV (P i) ⊆ A.vertexSet := fun i _ ht => support_mem (P i).walk (hZ' i) ht
    refine ⟨R, fun i => ?_, fun i t ht htD => ?_, fun i j hij => disjoint_left.2 fun t ht ht' => ?_⟩
    · have h₁ : (((P (c i)).walk.copy (hc i) rfl).mapLe (skeleton_mono hs.left_le)).IsPath :=
        ((SimpleGraph.Walk.isPath_copy ..).2 (P (c i)).isPath).mapLe _
      refine h₁.concat (fun hn => hyA i (hPA (c i) ?_)) (hyadj i)
      simpa [pathV] using hn
    · exact (hRs i t ht).resolve_left fun h => hDA t (hPA _ h) htD
    · rcases hRs i t ht with h₁ | h₁ <;> rcases hRs j t ht' with h₂ | h₂
      · exact disjoint_left.1 (hdis fun e => hij (hcinj e)) h₁ h₂
      · exact hyA j (h₂ ▸ hPA _ h₁)
      · exact hyA i (h₁ ▸ hPA _ h₂)
      · exact hij (hyinj (h₁.symm.trans h₂))

end GraphMinor.RST94
