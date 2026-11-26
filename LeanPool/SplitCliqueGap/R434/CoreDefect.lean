/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.LocalPacking
public import LeanPool.SplitCliqueGap.R434.PackingTriangles
public import LeanPool.SplitCliqueGap.R434.PartitionEnergy
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The signed energy forces an integer score defect on the physical core. -/

@[expose] public section

open Finset
open scoped BigOperators

namespace GapExtremal.R434.H54

variable {R : Type} [Fintype R] [DecidableEq R] [CommRing R]

/-- Recovers the slope, intercept, and template index of an edge in an affine block. -/
noncomputable def decodeEdge (e : Sym2 (Role × R)) : R × R × Edge :=
  Function.invFun (fun z : R × R × Edge => blockEdge z.1 z.2.1 z.2.2) e

omit [DecidableEq R] [Fintype R] in
theorem decode_blockEdge (h : R) (hh : 2 * h = 1) (a x : R) (e : Edge) :
    decodeEdge (blockEdge a x e) = (a,x,e) :=
  Function.leftInverse_invFun (blockEdge_injective h hh) (a,x,e)

theorem blockEdge_mem_core (h : R) (hh : 2 * h = 1) (A : Finset R) (a x : R) (e : Edge) :
    blockEdge a x e ∈ (coreGraph h A).edgeFinset ↔ a ∈ A ∧ e ∈ edges := by
  rw [core_edges_image h hh, mem_image]
  constructor
  · rintro ⟨⟨b,y,d⟩, hbd, hbe⟩
    have he : ((b,y,d) : R × R × Edge) = (a,x,e) := blockEdge_injective h hh hbe
    simpa only [he, mem_product, mem_univ, true_and] using hbd
  · intro he
    exact ⟨(a,x,e), by simpa using he, rfl⟩

omit [DecidableEq R] [Fintype R] in
theorem decode_ordered (h : R) (hh : 2 * h = 1) {u v : Role × R} (huv : u.1.1 < v.1.1) :
    let a := pairDirection (roleStep h) u v
    decodeEdge s(u,v) = (a, u.2 - (u.1.1.val : R) * a, edgeKind u.1.1 v.1.1, u.1.2, v.1.2) := by
  let a := pairDirection (roleStep h) u v
  let x := u.2 - (u.1.1.val : R) * a
  have he : blockEdge a x (edgeKind u.1.1 v.1.1,u.1.2,v.1.2) = s(u,v) := by
    unfold blockEdge
    rw [(parts_of_order huv).1, (parts_of_order huv).2]
    have hu : affineVertex a x u.1 = u := Prod.ext rfl (sub_add_cancel _ _)
    have hv : affineVertex a x v.1 = v := position_eq_of_direction h hh huv u.2 v.2
    rw [show (u.1.1,u.1.2) = u.1 from rfl, show (v.1.1,v.1.2) = v.1 from rfl, hu,hv]
  dsimp only
  rw [← he, decode_blockEdge h hh]

/-- The signed price assigned using the block slope and edge kind. -/
noncomputable def edgePrice (R₀ : ℝ) (f : R → ℝ) (e : Sym2 (Role × R)) : ℝ :=
  signedPrice R₀ f (decodeEdge e).1 (decodeEdge e).2.2.1

theorem core_edgePrice_sum (h : R) (hh : 2 * h = 1) (A : Finset R) (R₀ : ℝ) (f : R → ℝ) :
    ∑ e ∈ (coreGraph h A).edgeFinset, edgePrice R₀ f e = 0 := by
  classical
  rw [core_edges_image h hh, sum_image (fun _ _ _ _ he => blockEdge_injective h hh he)]
  simp only [edgePrice, decode_blockEdge h hh, Finset.sum_product, signedPrice_block,
    sum_const_zero]

omit [Fintype R] in
theorem core_edgePrice_triangle (h : R) (hh : 2 * h = 1) (R₀ : ℝ) (f : R → ℝ)
    (u v z : Role × R) (hu : u.1.1 = 0) (hv : v.1.1 = 1) (hz : z.1.1 = 2) :
    ∑ e ∈ triangleEdges (u,v,z), edgePrice R₀ f e =
      f (pairDirection (roleStep h) u v) + f (pairDirection (roleStep h) v z) -
        2 * f (pairDirection (roleStep h) u z) := by
  classical
  have huv : u.1.1 < v.1.1 := by rw [hu,hv]; decide
  have hvz : v.1.1 < z.1.1 := by rw [hv,hz]; decide
  have he₁ : s(u,v) ≠ s(v,z) := by
    intro he
    rcases Sym2.eq_iff.mp he with hp | hp
    · exact (ne_of_lt huv) (congrArg (fun x : Role × R => x.1.1) hp.1)
    · exact (ne_of_lt (huv.trans hvz)) (congrArg (fun x : Role × R => x.1.1) hp.1)
  have he₂ : s(u,v) ≠ s(u,z) := by
    intro he
    rcases Sym2.eq_iff.mp he with hp | hp
    · exact (ne_of_lt hvz) (congrArg (fun x : Role × R => x.1.1) hp.2)
    · exact (ne_of_lt (huv.trans hvz)) (congrArg (fun x : Role × R => x.1.1) hp.1)
  have he₃ : s(v,z) ≠ s(u,z) := by
    intro he
    rcases Sym2.eq_iff.mp he with hp | hp
    · exact (ne_of_gt huv) (congrArg (fun x : Role × R => x.1.1) hp.1)
    · exact (ne_of_lt hvz) (congrArg (fun x : Role × R => x.1.1) hp.1)
  unfold triangleEdges
  change ∑ e ∈ ({s(u,v),s(v,z),s(u,z)} : Finset (Sym2 (Role × R))), edgePrice R₀ f e = _
  rw [sum_insert (by simp [he₁,he₂]), sum_insert (by simp [he₃]), sum_singleton, ← add_assoc]
  simp only [edgePrice, decode_ordered h hh huv, decode_ordered h hh hvz,
    decode_ordered h hh (huv.trans hvz), hu,hv,hz, edgeKind]
  norm_num
  exact signedPrice_triangle _ _ _ _ _

/-- The triangles in the packing whose vertices lie outside any single affine block. -/
noncomputable def mixedTriangles (h : R) (T : Finset (OrderedTriangle (Role × R))) :
    Finset (OrderedTriangle (Role × R)) :=
  T.filter fun t => pairDirection (roleStep h) t.1 t.2.1 ≠ pairDirection (roleStep h) t.2.1 t.2.2

theorem owner_covered (h : R) (hh : 2 * h = 1) (A : Finset R)
    (T : Finset (OrderedTriangle (Role × R))) (X : Finset (Sym2 (Role × R)))
    (hc : ∀ t ∈ T, t.1.1.1 = 0 ∧ t.2.1.1.1 = 1 ∧ t.2.2.1.1 = 2)
    (hpack : (T : Set (OrderedTriangle (Role × R))).PairwiseDisjoint triangleEdges)
    (hpart : X ∪ T.biUnion triangleEdges = (coreGraph h A).edgeFinset) :
    A ×ˢ (univ : Finset R) ⊆
      (X ∪ (mixedTriangles h T).biUnion triangleEdges).image
        (fun e => ((decodeEdge e).1, (decodeEdge e).2.1)) := by
  classical
  rintro ⟨a,x⟩ hax
  have ha := (mem_product.mp hax).1
  by_contra hn
  let g (t : Triangle) : ℤ := if blockTriangle a x t ∈ T then 1 else 0
  apply no_integral_cover g (by intro t _; unfold g; split <;> decide)
  intro e he
  have hB := (blockEdge_mem_core h hh A a x e).mpr ⟨ha,he⟩
  have hnot : blockEdge a x e ∉ X ∪ (mixedTriangles h T).biUnion triangleEdges := by
    intro hmem
    exact hn (mem_image.mpr ⟨_,hmem,by rw [decode_blockEdge h hh]⟩)
  have ht' : blockEdge a x e ∈ T.biUnion triangleEdges := by
    rcases mem_union.mp (hpart.symm ▸ hB) with hx | ht
    · exact (hnot (mem_union_left _ hx)).elim
    · exact ht
  obtain ⟨t,ht,het⟩ := mem_biUnion.mp ht'
  have hm : t ∉ mixedTriangles h T := fun hx => hnot (mem_union_right _
    (mem_biUnion.mpr ⟨t,hx,het⟩))
  have hloc : pairDirection (roleStep h) t.1 t.2.1 = pairDirection (roleStep h) t.2.1 t.2.2 := by
    by_contra hf
    exact hm (mem_filter.mpr ⟨ht,hf⟩)
  obtain ⟨b,y,k,hk⟩ := is_blockTriangle_of_local h (hc t ht) hloc
  rw [← hk] at het ht
  obtain ⟨rfl,rfl,he_on⟩ := (blockEdge_mem_blockTriangle h hh).mp het
  have hkin (i : Fin 3) : onTriangleIndex k i ∈ edges := by
    have h₁ : blockEdge a x (onTriangleIndex k i) ∈ triangleEdges (blockTriangle a x k) := by
      rw [triangleEdges_block]
      exact mem_image.mpr ⟨i,mem_univ _,rfl⟩
    have h₂ : blockEdge a x (onTriangleIndex k i) ∈ (coreGraph h A).edgeFinset :=
      hpart ▸ mem_union_right _ (mem_biUnion.mpr ⟨_,ht,h₁⟩)
    exact ((blockEdge_mem_core h hh A _ _ _).mp h₂).2
  have hktri : k ∈ triangles := by
    exact mem_filter.mpr ⟨mem_univ _, hkin 0, hkin 1, hkin 2⟩
  have hfilt :
      ((triangles.filter (onEdge · e)).filter (fun j => blockTriangle a x j ∈ T)) = {k} := by
    ext j
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨⟨_,hon⟩,hj⟩
      have h₁ : blockEdge a x e ∈ triangleEdges (blockTriangle a x j) :=
        (blockEdge_mem_blockTriangle h hh).mpr ⟨rfl,rfl,hon⟩
      have heq : blockTriangle a x j = blockTriangle a x k := by
        by_contra hne
        exact disjoint_left.mp (hpack hj ht hne) h₁ het
      have h : ((a,x,j) : R × R × Triangle) = (a,x,k) :=
        blockTriangle_injective h hh heq
      exact congrArg (fun z : R × R × Triangle => z.2.2) h
    · rintro rfl
      exact ⟨⟨hktri,he_on⟩,ht⟩
  unfold load g
  rw [sum_eq_single k]
  · simp [ht]
  · intro j hj hne
    have hn : blockTriangle a x j ∉ T := by
      intro hjT
      have hmem : j ∈ (triangles.filter (onEdge · e)).filter
          (fun j => blockTriangle a x j ∈ T) := by
        have hhj := mem_filter.mp hj
        exact mem_filter.mpr ⟨mem_filter.mpr hhj, hjT⟩
      rw [hfilt, mem_singleton] at hmem
      exact hne hmem
    simp [hn]
  · intro hn
    exact (hn (mem_filter.mpr ⟨hktri, he_on⟩)).elim

theorem six_edges_per_block (h : R) (hh : 2 * h = 1) (A : Finset R)
    (T : Finset (OrderedTriangle (Role × R))) (X : Finset (Sym2 (Role × R)))
    (hc : ∀ t ∈ T, t.1.1.1 = 0 ∧ t.2.1.1.1 = 1 ∧ t.2.2.1.1 = 2)
    (hpack : (T : Set (OrderedTriangle (Role × R))).PairwiseDisjoint triangleEdges)
    (hpart : X ∪ T.biUnion triangleEdges = (coreGraph h A).edgeFinset) :
    6 * (A.card * Fintype.card R) ≤ X.card + 3 * (mixedTriangles h T).card := by
  classical
  let owners := A ×ˢ (univ : Finset R)
  let L (o : R × R) := triangles.filter fun k => blockTriangle o.1 o.2 k ∈ T
  let family (o : R × R) := (L o).image (blockTriangle o.1 o.2)
  have hcap (o) : (family o).card ≤ 16 := by
    apply card_image_le.trans
    apply local_packing_le_sixteen _ (filter_subset _ _)
    intro i u hu v hv eq
    change onTriangleIndex u i = onTriangleIndex v i at eq
    have eu : blockEdge o.1 o.2 (onTriangleIndex u i) ∈ triangleEdges (blockTriangle o.1 o.2 u) :=
      by
      rw [triangleEdges_block]; exact mem_image.mpr ⟨i,mem_univ _,rfl⟩
    have ev : blockEdge o.1 o.2 (onTriangleIndex u i) ∈ triangleEdges (blockTriangle o.1 o.2 v) :=
      by
      rw [eq,triangleEdges_block]; exact mem_image.mpr ⟨i,mem_univ _,rfl⟩
    by_contra ne
    have hne : blockTriangle o.1 o.2 u ≠ blockTriangle o.1 o.2 v :=
      fun he => ne (congrArg (fun z : R × R × Triangle => z.2.2)
        (show ((o.1,o.2,u) : R × R × Triangle) = (o.1,o.2,v) from blockTriangle_injective h hh he))
    exact disjoint_left.mp (hpack (mem_filter.mp hu).2 (mem_filter.mp hv).2 hne) eu ev
  let Z := mixedTriangles h T
  have hloc : T \ Z ⊆ owners.biUnion family := by
    intro t ht
    obtain ⟨ht,hn⟩ := mem_sdiff.mp ht
    have heq : pairDirection (roleStep h) t.1 t.2.1 = pairDirection (roleStep h) t.2.1 t.2.2 :=
      by by_contra he; exact hn (mem_filter.mpr ⟨ht,he⟩)
    obtain ⟨a,x,k,rfl⟩ := is_blockTriangle_of_local h (hc t ht) heq
    have hparts (i : Fin 3) : a ∈ A ∧ onTriangleIndex k i ∈ edges := by
      apply (blockEdge_mem_core h hh A a x _).mp
      rw [← hpart]
      apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨_,ht,?_⟩
      rw [triangleEdges_block]; exact mem_image.mpr ⟨i,mem_univ _,rfl⟩
    have hk : k ∈ triangles := mem_filter.mpr
      ⟨mem_univ _, (hparts 0).2, (hparts 1).2, (hparts 2).2⟩
    exact mem_biUnion.mpr ⟨(a,x), mem_product.mpr ⟨(hparts 0).1,mem_univ _⟩,
      mem_image.mpr ⟨k,mem_filter.mpr ⟨hk,ht⟩,rfl⟩⟩
  have hlocal := (card_le_card hloc).trans
    (card_biUnion_le_card_mul owners family 16 (fun o _ => hcap o))
  have hz : Z ⊆ T := filter_subset _ _
  rw [card_sdiff_of_subset hz] at hlocal
  have hzc := card_le_card hz
  have htot := (card_union_le X (T.biUnion triangleEdges)).trans
    (Nat.add_le_add_left (card_biUnion_le_card_mul T triangleEdges 3
      (fun t _ => triangleEdges_card_le t)) X.card)
  rw [hpart,core_edge_count h hh A] at htot
  simp only [owners,card_product,card_univ] at hlocal
  change 6 * (A.card * Fintype.card R) ≤ X.card + 3 * Z.card
  omega

theorem core_integer_defect_six (h : R) (hh : 2 * h = 1) (A : Finset R) (R₀ δ : ℝ)
    (hR : 0 ≤ R₀) (hδ : 0 < δ) (f : R → ℝ) (hf : ∀ a ∈ A, 0 ≤ f a ∧ f a ≤ R₀)
    (hmid : ∀ a b c, a ∈ A → b ∈ A → c ∈ A → a ≠ b → a + b = 2 * c →
      δ ≤ f a + f b - 2 * f c)
    {P : Finset (Finset (Role × R))} (hP : IsPack P) :
    6 * ((A.card * Fintype.card R : ℕ) : ℝ) / (27 * (1 + 2 * R₀ / δ)) ≤
      36 * ((A.card * Fintype.card R : ℕ) : ℝ) - ∑ Q ∈ P, (w (coreGraph h A) Q : ℝ) := by
  classical
  let B := coreGraph h A
  obtain ⟨T,X,hc,hpack,hpart,hdisj,hslack⟩ :=
    packing_to_triangles B (fun u : Role × R => u.1.1) (fun _ _ he => core_is_tripartite h A he) hP
  let Z := mixedTriangles h T
  have hBcard : (B.edgeFinset.card : ℝ) = 54 * ((A.card * Fintype.card R : ℕ) : ℝ) := by
    exact_mod_cast core_edge_count h hh A
  rw [hBcard] at hslack
  have hb : ∀ t ∈ T, triangleEdges t ⊆ B.edgeFinset :=
    fun t ht e he => hpart ▸ mem_union_right _ (mem_biUnion.mpr ⟨t,ht,he⟩)
  have hdir_in (u v : Role × R) (hs : s(u,v) ∈ B.edgeFinset) : pairDirection (roleStep h) u v ∈ A :=
    (show B.Adj u v from SimpleGraph.mem_edgeFinset.mp hs).2
  have hgap := edge_partition_gap_of_count B.edgeFinset X T Z triangleEdges
    (6 * (A.card * Fintype.card R)) (edgePrice R₀ f) R₀ δ
    (36 * ((A.card * Fintype.card R : ℕ) : ℝ) - ∑ Q ∈ P, (w B Q : ℝ))
    hR hδ hpart hdisj hpack (filter_subset _ _)
    (six_edges_per_block h hh A T X hc hpack hpart) (core_edgePrice_sum h hh A R₀ f)
  have hprice (e : Sym2 (Role × R)) (he : e ∈ X) : -(2 * R₀ / 3) ≤ edgePrice R₀ f e := by
    have heB : e ∈ B.edgeFinset := hpart ▸ mem_union_left _ he
    rw [core_edges_image h hh A] at heB
    obtain ⟨⟨a,x,k⟩,hm,rfl⟩ := mem_image.mp heB
    have hfa := hf a (mem_product.mp hm).1
    simpa only [edgePrice, decode_blockEdge h hh] using signedPrice_lower R₀ f hfa.1 hfa.2 k.1
  have hzero (t : OrderedTriangle (Role × R)) (ht : t ∈ T) (hn : t ∉ Z) :
      ∑ e ∈ triangleEdges t, edgePrice R₀ f e = 0 := by
    obtain ⟨u,v,z⟩ := t
    obtain ⟨hu,hv,hz⟩ := hc _ ht
    have hloc : pairDirection (roleStep h) u v = pairDirection (roleStep h) v z := by
      by_contra he
      exact hn (mem_filter.mpr ⟨ht,he⟩)
    have hpr := triangle_directions_of_parts h hh hu hv hz
    rw [← hloc, ← two_mul] at hpr
    have hlast : pairDirection (roleStep h) u v = pairDirection (roleStep h) u z := by
      have he := congrArg (fun a : R => h * a) hpr
      simpa only [← mul_assoc, mul_comm h (2 : R), hh, one_mul] using he
    rw [core_edgePrice_triangle h hh R₀ f u v z hu hv hz, ← hloc, ← hlast]
    ring
  have hmix (t : OrderedTriangle (Role × R)) (ht : t ∈ Z) :
      δ ≤ ∑ e ∈ triangleEdges t, edgePrice R₀ f e := by
    obtain ⟨u,v,z⟩ := t
    obtain ⟨htT, hne⟩ := mem_filter.mp ht
    obtain ⟨hu,hv,hz⟩ := hc _ htT
    rw [core_edgePrice_triangle h hh R₀ f u v z hu hv hz]
    apply hmid
    · exact hdir_in u v (hb _ htT (by simp [triangleEdges]))
    · exact hdir_in v z (hb _ htT (by simp [triangleEdges]))
    · exact hdir_in u z (hb _ htT (by simp [triangleEdges]))
    · exact hne
    · exact triangle_directions_of_parts h hh hu hv hz
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hgap hprice hzero hmix (by linarith only [hslack])

theorem core_integer_defect (h : R) (hh : 2 * h = 1) (A : Finset R) (R₀ δ : ℝ)
    (hR : 0 ≤ R₀) (hδ : 0 < δ) (f : R → ℝ) (hf : ∀ a ∈ A, 0 ≤ f a ∧ f a ≤ R₀)
    (hmid : ∀ a b c, a ∈ A → b ∈ A → c ∈ A → a ≠ b → a + b = 2 * c →
      δ ≤ f a + f b - 2 * f c)
    {P : Finset (Finset (Role × R))} (hP : IsPack P) :
    ((A.card * Fintype.card R : ℕ) : ℝ) / (27 * (1 + 2 * R₀ / δ)) ≤
      36 * ((A.card * Fintype.card R : ℕ) : ℝ) - ∑ Q ∈ P, (w (coreGraph h A) Q : ℝ) := by
  have hstrong := core_integer_defect_six h hh A R₀ δ hR hδ f hf hmid hP
  apply le_trans _ hstrong
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith only [Nat.cast_nonneg (α := ℝ) (A.card * Fintype.card R)]

end GapExtremal.R434.H54
