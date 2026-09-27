/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the **blow-up scaling** of the fractional triangle packing number

The block-allocation residual `Nibble.AX1.BlockCoverResidualCoupled` (`Nibble.CoreGapBlockCover`)
asks for an integral family of block rectangles realising a near-optimal solution of the fractional
triangle packing LP of the weighted cluster graph.  The model case of that statement — all cluster
densities equal to `1` — is the *blow-up* problem: how much of `ν₃*` of a graph `H` survives when
each vertex of `H` is replaced by `q` copies.

This file proves the LP half of that question, exactly:

`ν₃*(H[q]) = q² · ν₃*(H)`  (`Nibble.AX1.nu3star_blowUp`),

where `H[q]` (`Nibble.AX1.blowUp`) is the `q`-blow-up of `H`, the graph on `W × Fin q` with
`(a, i) ~ (b, j) ↔ H.Adj a b`.

* `≥` (`Nibble.AX1.nu3star_blowUp_ge`) lifts a fractional packing `w` of `H` to the blow-up by
  spreading the weight of a triangle `T` evenly over the `q³` triangles above it, at `w T / q` each:
  a blow-up edge lies above one edge of `H` and is in `q` triangles above each triangle through that
  edge, so the capacity constraint is inherited verbatim.
* `≤` (`Nibble.AX1.nu3star_blowUp_le`) projects a fractional packing `w'` of `H[q]` back down, a
  triangle of `H` receiving `1/q²` of the total weight of the triangles above it: the `q²` blow-up
  copies of an edge of `H` carry capacity `q²` in total, and every blow-up triangle above a triangle
  through that edge uses exactly one of those copies.

Neither direction uses probability, regularity or counting: both are the two halves of a linear
programming identity.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapClusterCapacity
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Ring.Star

/-! # CoreGapBlowUp -/

@[expose] public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

/-! ### Triangle hyperedges and their vertex sets

A hyperedge of `Nibble.YusterE.triangleHypergraphE` is the set of the three *edges* of a triangle.
`Nibble.AX1.vtxSet` recovers the three vertices, so that sums over the triangle hypergraph can be
rewritten as sums over `cliqueFinset 3`. -/

/-- The set of vertices covered by a set of edges. -/
def vtxSet {X : Type} [DecidableEq X] (T : Finset (Finset X)) : Finset X := T.biUnion id

/-- The vertex set of the edge set of a set with at least two elements is the set itself. -/
theorem vtxSet_powersetCard_two {X : Type} [DecidableEq X] {t : Finset X} (ht : 2 ≤ #t) :
    vtxSet (t.powersetCard 2) = t := by
  classical
  ext v
  simp only [vtxSet, Finset.mem_biUnion, id_eq, Finset.mem_powersetCard]
  constructor
  · rintro ⟨e, ⟨hsub, -⟩, hve⟩
    exact hsub hve
  · intro hv
    obtain ⟨u, hu, hune⟩ : ∃ u ∈ t, u ≠ v := by
      by_contra hcon
      push Not at hcon
      have hsub : t ⊆ {v} := fun x hx => by simp [hcon x hx]
      have := Finset.card_le_card hsub
      simp at this
      omega
    refine ⟨{v, u}, ⟨?_, ?_⟩, by simp⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hv
      · exact hu
    · rw [Finset.card_insert_of_notMem (by simp [Ne.symm hune]), Finset.card_singleton]

/-- A sum over the triangle hypergraph is a sum over the triangles. -/
theorem sum_triangleHypergraphE {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (f : Finset (Finset V) → ℝ) :
    ∑ T ∈ triangleHypergraphE G, f T = ∑ t ∈ G.cliqueFinset 3, f (t.powersetCard 2) := by
  classical
  unfold triangleHypergraphE
  rw [Finset.sum_image]
  intro s hs t ht hst
  simp only [Finset.mem_coe, SimpleGraph.mem_cliqueFinset_iff] at hs ht
  exact powersetCard_two_inj (by have := hs.card_eq; omega) (by have := ht.card_eq; omega) hst

/-- A sum over the triangle hyperedges through a fixed edge is a sum over the triangles containing
that edge. -/
theorem sum_triangleHypergraphE_filter {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {e : Finset V} (he : #e = 2) (f : Finset (Finset V) → ℝ) :
    ∑ T ∈ (triangleHypergraphE G).filter (fun T => e ∈ T), f T
      = ∑ t ∈ (G.cliqueFinset 3).filter (fun t => e ⊆ t), f (t.powersetCard 2) := by
  classical
  have hfil : (triangleHypergraphE G).filter (fun T => e ∈ T)
      = ((G.cliqueFinset 3).filter (fun t => e ⊆ t)).image (fun t => t.powersetCard 2) := by
    ext T
    simp only [triangleHypergraphE, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, heT⟩
      rw [Finset.mem_powersetCard] at heT
      exact ⟨t, ⟨ht, heT.1⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hsub⟩, rfl⟩
      exact ⟨⟨t, ht, rfl⟩, Finset.mem_powersetCard.mpr ⟨hsub, he⟩⟩
  rw [hfil, Finset.sum_image]
  intro s hs t ht hst
  simp only [Finset.mem_coe, Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at hs ht
  exact powersetCard_two_inj (by have := hs.1.card_eq; omega) (by have := ht.1.card_eq; omega) hst

/-! ### The blow-up -/

variable {W : Type} [Fintype W] [DecidableEq W]

/-- **The `q`-blow-up of `H`**: every vertex is replaced by `q` copies, and two copies are adjacent
exactly when the vertices they lie above are. -/
def blowUp (H : SimpleGraph W) (q : ℕ) : SimpleGraph (W × Fin q) := SimpleGraph.comap Prod.fst H

instance instDecidableRelBlowUpAdj (H : SimpleGraph W) [DecidableRel H.Adj] (q : ℕ) :
    DecidableRel (blowUp H q).Adj := fun x y => inferInstanceAs (Decidable (H.Adj x.1 y.1))

omit [Fintype W] [DecidableEq W] in
@[simp] theorem blowUp_adj {H : SimpleGraph W} {q : ℕ} {x y : W × Fin q} :
    (blowUp H q).Adj x y ↔ H.Adj x.1 y.1 := Iff.rfl

omit [Fintype W] in
/-- The projection of a triangle of the blow-up is a triangle of `H`. -/
theorem isNClique_image_fst {H : SimpleGraph W} {q : ℕ} {t' : Finset (W × Fin q)}
    (ht' : (blowUp H q).IsNClique 3 t') : H.IsNClique 3 (t'.image Prod.fst) := by
  classical
  have hinj : Set.InjOn Prod.fst (t' : Set (W × Fin q)) := by
    intro x hx y hy hxy
    by_contra hne
    have := ht'.1 hx hy hne
    rw [blowUp_adj, hxy] at this
    exact this.ne rfl
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_image] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    have hxy : x ≠ y := fun h => hab (by rw [h])
    exact ht'.1 hx hy hxy
  · rw [Finset.card_image_of_injOn hinj, ht'.card_eq]

/-- **The fibre of the projection has `q³` elements**: a triangle of `H` is the projection of
exactly `q³` triangles of the blow-up. -/
theorem card_blowUp_fiber (H : SimpleGraph W) [DecidableRel H.Adj] (q : ℕ) {t : Finset W}
    (ht : H.IsNClique 3 t) :
    #(((blowUp H q).cliqueFinset 3).filter (fun t' => t'.image Prod.fst = t)) = q ^ 3 := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp ht.card_eq
  have hAab : H.Adj a b := ht.1 (by simp) (by simp) hab
  have hAac : H.Adj a c := ht.1 (by simp) (by simp) hac
  have hAbc : H.Adj b c := ht.1 (by simp) (by simp) hbc
  set f : Fin q × Fin q × Fin q → Finset (W × Fin q) :=
    fun p => {(a, p.1), (b, p.2.1), (c, p.2.2)} with hf
  have hinj : Function.Injective f := by
    rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
    simp only [hf] at h
    have h1 : ((a, i) : W × Fin q) ∈ ({(a, i'), (b, j'), (c, k')} : Finset (W × Fin q)) := by
      rw [← h]; simp
    have h2 : ((b, j) : W × Fin q) ∈ ({(a, i'), (b, j'), (c, k')} : Finset (W × Fin q)) := by
      rw [← h]; simp
    have h3 : ((c, k) : W × Fin q) ∈ ({(a, i'), (b, j'), (c, k')} : Finset (W × Fin q)) := by
      rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h1 h2 h3
    have e1 : i = i' := by
      rcases h1 with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hab
      · exact absurd h hac
    have e2 : j = j' := by
      rcases h2 with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd h.symm hab
      · exact h
      · exact absurd h hbc
    have e3 : k = k' := by
      rcases h3 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h.symm hac
      · exact absurd h.symm hbc
      · exact h
    simp [e1, e2, e3]
  have himg : ((blowUp H q).cliqueFinset 3).filter
        (fun t' => t'.image Prod.fst = ({a, b, c} : Finset W))
      = (univ : Finset (Fin q × Fin q × Fin q)).image f := by
    ext t'
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      SimpleGraph.mem_cliqueFinset_iff]
    constructor
    · rintro ⟨hcl, himg⟩
      have hax : ∃ x ∈ t', x.1 = a := by
        have : a ∈ t'.image Prod.fst := by rw [himg]; simp
        simpa [Finset.mem_image] using this
      have hbx : ∃ x ∈ t', x.1 = b := by
        have : b ∈ t'.image Prod.fst := by rw [himg]; simp
        simpa [Finset.mem_image] using this
      have hcx : ∃ x ∈ t', x.1 = c := by
        have : c ∈ t'.image Prod.fst := by rw [himg]; simp
        simpa [Finset.mem_image] using this
      obtain ⟨x, hx, hxa⟩ := hax
      obtain ⟨y, hy, hyb⟩ := hbx
      obtain ⟨z, hz, hzc⟩ := hcx
      have hxy : x ≠ y := fun h => hab (by rw [← hxa, ← hyb, h])
      have hxz : x ≠ z := fun h => hac (by rw [← hxa, ← hzc, h])
      have hyz : y ≠ z := fun h => hbc (by rw [← hyb, ← hzc, h])
      have hsub : ({x, y, z} : Finset (W × Fin q)) ⊆ t' := by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl <;> assumption
      have hcard : #({x, y, z} : Finset (W × Fin q)) = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
          Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
      have heq : ({x, y, z} : Finset (W × Fin q)) = t' :=
        Finset.eq_of_subset_of_card_le hsub (by rw [hcl.card_eq, hcard])
      have ex : ((a, x.2) : W × Fin q) = x := by rw [Prod.ext_iff]; exact ⟨hxa.symm, rfl⟩
      have ey : ((b, y.2) : W × Fin q) = y := by rw [Prod.ext_iff]; exact ⟨hyb.symm, rfl⟩
      have ez : ((c, z.2) : W × Fin q) = z := by rw [Prod.ext_iff]; exact ⟨hzc.symm, rfl⟩
      refine ⟨(x.2, y.2, z.2), ?_⟩
      rw [← heq]
      simp only [hf]
      rw [ex, ey, ez]
    · rintro ⟨⟨i, j, k⟩, rfl⟩
      constructor
      · constructor
        · intro u hu v hv huv
          simp only [hf, Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
            Set.mem_singleton_iff] at hu hv
          rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
            simp_all [blowUp_adj, hAab.symm, hAac.symm, hAbc.symm]
        · simp only [hf]
          rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
            Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
      · simp [hf]
  rw [himg, Finset.card_image_of_injective _ hinj]
  simp [Finset.card_univ, pow_succ, mul_assoc]

/-- **The fibre of the projection through a fixed blow-up edge has `q` elements.** -/
theorem card_blowUp_fiber_edge (H : SimpleGraph W) [DecidableRel H.Adj] (q : ℕ) {t : Finset W}
    (ht : H.IsNClique 3 t) {x y : W × Fin q} (hne : x.1 ≠ y.1) (hx : x.1 ∈ t) (hy : y.1 ∈ t) :
    #(((blowUp H q).cliqueFinset 3).filter
        (fun t' => t'.image Prod.fst = t ∧ ({x, y} : Finset (W × Fin q)) ⊆ t')) = q := by
  classical
  have hxy : x ≠ y := fun h => hne (by rw [h])
  have hsub : ({x.1, y.1} : Finset W) ⊆ t := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption
  have hcard2 : #({x.1, y.1} : Finset W) = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  have hcard1 : #(t \ ({x.1, y.1} : Finset W)) = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, ht.card_eq, hcard2]
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard1
  have hcmem : c ∈ t \ ({x.1, y.1} : Finset W) := by rw [hc]; simp
  have hct : c ∈ t := (Finset.mem_sdiff.mp hcmem).1
  have hcab : c ∉ ({x.1, y.1} : Finset W) := (Finset.mem_sdiff.mp hcmem).2
  have hca : c ≠ x.1 := by intro h; exact hcab (by simp [h])
  have hcb : c ≠ y.1 := by intro h; exact hcab (by simp [h])
  have htabc : t = ({x.1, y.1, c} : Finset W) := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    · rw [ht.card_eq, Finset.card_insert_of_notMem (by simp [hne, Ne.symm hca]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hcb]), Finset.card_singleton]
  have hAab : H.Adj x.1 y.1 := ht.1 hx hy hne
  have hAac : H.Adj x.1 c := (ht.1 hct hx hca).symm
  have hAbc : H.Adj y.1 c := (ht.1 hct hy hcb).symm
  set f : Fin q → Finset (W × Fin q) := fun k => {x, y, (c, k)} with hf
  have hinj : Function.Injective f := by
    intro k k' h
    simp only [hf] at h
    have hmem : ((c, k) : W × Fin q) ∈ ({x, y, (c, k')} : Finset (W × Fin q)) := by
      rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1 | h1
    · exact absurd (congrArg Prod.fst h1) hca
    · exact absurd (congrArg Prod.fst h1) hcb
    · exact (Prod.ext_iff.mp h1).2
  have himg : ((blowUp H q).cliqueFinset 3).filter
      (fun t' => t'.image Prod.fst = t ∧ ({x, y} : Finset (W × Fin q)) ⊆ t')
      = (univ : Finset (Fin q)).image f := by
    ext t'
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      SimpleGraph.mem_cliqueFinset_iff]
    constructor
    · rintro ⟨hcl, himgt, hxysub⟩
      have hxt : x ∈ t' := hxysub (by simp)
      have hyt : y ∈ t' := hxysub (by simp)
      have hcx : ∃ z ∈ t', z.1 = c := by
        have : c ∈ t'.image Prod.fst := by rw [himgt]; exact hct
        simpa [Finset.mem_image] using this
      obtain ⟨z, hz, hzc⟩ := hcx
      have hxz : x ≠ z := fun h => hca (by rw [← hzc, ← h])
      have hyz : y ≠ z := fun h => hcb (by rw [← hzc, ← h])
      have hsub' : ({x, y, z} : Finset (W × Fin q)) ⊆ t' := by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl <;> assumption
      have hcard : #({x, y, z} : Finset (W × Fin q)) = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
          Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
      have heq : ({x, y, z} : Finset (W × Fin q)) = t' :=
        Finset.eq_of_subset_of_card_le hsub' (by rw [hcl.card_eq, hcard])
      have ez : ((c, z.2) : W × Fin q) = z := by rw [Prod.ext_iff]; exact ⟨hzc.symm, rfl⟩
      exact ⟨z.2, by rw [← heq]; simp only [hf]; rw [ez]⟩
    · rintro ⟨k, rfl⟩
      have hxck : x ≠ (c, k) := fun h => hca (congrArg Prod.fst h).symm
      have hyck : y ≠ (c, k) := fun h => hcb (congrArg Prod.fst h).symm
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · intro u hu v hv huv
        simp only [blowUp_adj]
        simp only [hf, Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
          Set.mem_singleton_iff] at hu hv
        rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
          first
            | exact absurd rfl huv
            | exact hAab
            | exact hAab.symm
            | exact hAac
            | exact hAac.symm
            | exact hAbc
            | exact hAbc.symm
      · simp only [hf]
        rw [Finset.card_insert_of_notMem (by simp [hxy, hxck]),
          Finset.card_insert_of_notMem (by simp [hyck]), Finset.card_singleton]
      · simp only [hf, Finset.image_insert, Finset.image_singleton]
        exact htabc.symm
      · simp [hf]
  rw [himg, Finset.card_image_of_injective _ hinj]
  simp

/-! ### Lifting a fractional packing to the blow-up -/

/-- The lift of a weight function on the triangles of `H` to the triangles of the blow-up: the
weight of a triangle is `1/q` of the weight of the triangle below it. -/
noncomputable def liftWeight (H : SimpleGraph W) [DecidableRel H.Adj] (q : ℕ)
    (w : Finset (Finset W) → ℝ) : Finset (Finset (W × Fin q)) → ℝ :=
  fun T' => if T' ∈ triangleHypergraphE (blowUp H q) then
    w (((vtxSet T').image Prod.fst).powersetCard 2) / q else 0

/-- **The lift of a fractional packing is a fractional packing.** -/
theorem isFracPacking_liftWeight (H : SimpleGraph W) [DecidableRel H.Adj] {q : ℕ} (hq : 0 < q)
    {w : Finset (Finset W) → ℝ} (hw : IsFracPacking H w) :
    IsFracPacking (blowUp H q) (liftWeight H q w) := by
  classical
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  refine ⟨fun T' => ?_, fun T' hT' => ?_, fun e' => ?_⟩
  · rw [liftWeight]; split_ifs
    · exact div_nonneg (hw.1 _) hqR.le
    · exact le_rfl
  · rw [liftWeight, ite_eq_right hT']
  · by_cases he2 : #e' = 2
    swap
    · have hemp : (triangleHypergraphE (blowUp H q)).filter (fun T => e' ∈ T) = ∅ := by
        ext T
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hT heT
        rw [triangleHypergraphE, Finset.mem_image] at hT
        obtain ⟨t', ht', rfl⟩ := hT
        rw [Finset.mem_powersetCard] at heT
        exact he2 heT.2
      rw [hemp, Finset.sum_empty]; norm_num
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp he2
    rw [sum_triangleHypergraphE_filter (blowUp H q) he2]
    have hstep : ∀ t' ∈ ((blowUp H q).cliqueFinset 3).filter
        (fun t' => ({x, y} : Finset (W × Fin q)) ⊆ t'),
        liftWeight H q w (t'.powersetCard 2) = w ((t'.image Prod.fst).powersetCard 2) / q := by
      intro t' ht'
      rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht'
      have hmem : t'.powersetCard 2 ∈ triangleHypergraphE (blowUp H q) := by
        rw [triangleHypergraphE, Finset.mem_image]
        exact ⟨t', SimpleGraph.mem_cliqueFinset_iff.mpr ht'.1, rfl⟩
      rw [liftWeight, ite_eq_left hmem, vtxSet_powersetCard_two (by rw [ht'.1.card_eq]; norm_num)]
    by_cases hfst : x.1 = y.1
    · have hempty : ((blowUp H q).cliqueFinset 3).filter
          (fun t' => ({x, y} : Finset (W × Fin q)) ⊆ t') = ∅ := by
        ext t'
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro ht' hsub
        rw [SimpleGraph.mem_cliqueFinset_iff] at ht'
        have hx : x ∈ t' := hsub (by simp)
        have hy : y ∈ t' := hsub (by simp)
        have := ht'.1 (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
        rw [blowUp_adj, hfst] at this
        exact this.ne rfl
      rw [hempty, Finset.sum_empty]; norm_num
    · have hcard2 : #({x.1, y.1} : Finset W) = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [hfst]), Finset.card_singleton]
      rw [Finset.sum_congr rfl hstep,
        ← Finset.sum_fiberwise_of_maps_to (g := fun t' => t'.image Prod.fst)
          (t := (H.cliqueFinset 3).filter (fun t => ({x.1, y.1} : Finset W) ⊆ t))
          (fun t' ht' => by
            rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht' ⊢
            refine ⟨isNClique_image_fst ht'.1, ?_⟩
            intro v hv
            simp only [Finset.mem_insert, Finset.mem_singleton] at hv
            rcases hv with rfl | rfl
            · exact Finset.mem_image.mpr ⟨x, ht'.2 (by simp), rfl⟩
            · exact Finset.mem_image.mpr ⟨y, ht'.2 (by simp), rfl⟩)]
      refine le_trans (le_of_eq ?_) (hw.2.2 ({x.1, y.1} : Finset W))
      rw [sum_triangleHypergraphE_filter H hcard2 w]
      refine Finset.sum_congr rfl (fun t ht => ?_)
      rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
      have hconst : ∀ t' ∈ (((blowUp H q).cliqueFinset 3).filter
          (fun t' => ({x, y} : Finset (W × Fin q)) ⊆ t')).filter
            (fun t' => t'.image Prod.fst = t),
          w ((t'.image Prod.fst).powersetCard 2) / q = w (t.powersetCard 2) / q :=
        fun t' ht' => by rw [(Finset.mem_filter.mp ht').2]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const]
      have hcardeq : #((((blowUp H q).cliqueFinset 3).filter
          (fun t' => ({x, y} : Finset (W × Fin q)) ⊆ t')).filter
            (fun t' => t'.image Prod.fst = t)) = q := by
        rw [Finset.filter_filter]
        have hcomm : ((blowUp H q).cliqueFinset 3).filter
            (fun t' => ({x, y} : Finset (W × Fin q)) ⊆ t' ∧ t'.image Prod.fst = t)
            = ((blowUp H q).cliqueFinset 3).filter
            (fun t' => t'.image Prod.fst = t ∧ ({x, y} : Finset (W × Fin q)) ⊆ t') := by
          apply Finset.filter_congr
          intro t' _
          exact and_comm
        rw [hcomm]
        exact card_blowUp_fiber_edge H q ht.1 hfst (ht.2 (by simp)) (ht.2 (by simp))
      rw [hcardeq, nsmul_eq_mul]
      field_simp

/-- **The value of the lift is `q²` times the value.** -/
theorem sum_liftWeight (H : SimpleGraph W) [DecidableRel H.Adj] {q : ℕ} (hq : 0 < q)
    (w : Finset (Finset W) → ℝ) :
    ∑ T' ∈ triangleHypergraphE (blowUp H q), liftWeight H q w T'
      = (q : ℝ) ^ 2 * ∑ T ∈ triangleHypergraphE H, w T := by
  classical
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  rw [sum_triangleHypergraphE (blowUp H q) (liftWeight H q w)]
  have hstep : ∀ t' ∈ (blowUp H q).cliqueFinset 3,
      liftWeight H q w (t'.powersetCard 2) = w ((t'.image Prod.fst).powersetCard 2) / q := by
    intro t' ht'
    rw [SimpleGraph.mem_cliqueFinset_iff] at ht'
    have hmem : t'.powersetCard 2 ∈ triangleHypergraphE (blowUp H q) := by
      rw [triangleHypergraphE, Finset.mem_image]
      exact ⟨t', SimpleGraph.mem_cliqueFinset_iff.mpr ht', rfl⟩
    rw [liftWeight, ite_eq_left hmem, vtxSet_powersetCard_two (by rw [ht'.card_eq]; norm_num)]
  rw [Finset.sum_congr rfl hstep,
    ← Finset.sum_fiberwise_of_maps_to (g := fun t' => t'.image Prod.fst)
      (t := H.cliqueFinset 3) (fun t' ht' => by
        rw [SimpleGraph.mem_cliqueFinset_iff] at ht' ⊢
        exact isNClique_image_fst ht')]
  rw [sum_triangleHypergraphE H w, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [SimpleGraph.mem_cliqueFinset_iff] at ht
  have hconst : ∀ t' ∈ ((blowUp H q).cliqueFinset 3).filter (fun t' => t'.image Prod.fst = t),
      w ((t'.image Prod.fst).powersetCard 2) / q = w (t.powersetCard 2) / q := by
    intro t' ht'
    rw [(Finset.mem_filter.mp ht').2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, card_blowUp_fiber H q ht, nsmul_eq_mul]
  push_cast
  field_simp

/-- **The blow-up bound `q²·ν₃*(H) ≤ ν₃*(H[q])`.** -/
theorem nu3star_blowUp_ge (H : SimpleGraph W) [DecidableRel H.Adj] {q : ℕ} (hq : 0 < q) :
    (q : ℝ) ^ 2 * nu3star H ≤ nu3star (blowUp H q) := by
  classical
  have hq2 : (0:ℝ) < (q:ℝ)^2 := by
    have : (0:ℝ) < q := by exact_mod_cast hq
    positivity
  have hne : {x : ℝ | ∃ w, IsFracPacking H w ∧ x = ∑ T ∈ triangleHypergraphE H, w T}.Nonempty :=
    ⟨0, fun _ => 0, ⟨fun _ => le_rfl, fun _ _ => rfl, fun e => by simp⟩, by simp⟩
  have hbound : nu3star H ≤ nu3star (blowUp H q) / (q:ℝ)^2 := by
    rw [nu3star]
    refine csSup_le hne ?_
    rintro x ⟨w, hw, rfl⟩
    rw [le_div_iff₀ hq2]
    calc (∑ T ∈ triangleHypergraphE H, w T) * (q:ℝ)^2
        = ∑ T' ∈ triangleHypergraphE (blowUp H q), liftWeight H q w T' := by
          rw [sum_liftWeight H hq w]; ring
      _ ≤ nu3star (blowUp H q) :=
          le_csSup (nu3star_bddAbove _) ⟨liftWeight H q w, isFracPacking_liftWeight H hq hw, rfl⟩
  rw [mul_comm]
  exact (le_div_iff₀ hq2).mp hbound

omit [Fintype W] in
/-- A triangle of the blow-up whose projection contains the edge `{a, b}` contains exactly one
vertex over `a` and one over `b`. -/
theorem blowUp_filter_pair {H : SimpleGraph W} [DecidableRel H.Adj] {q : ℕ} {a b : W}
    {t' : Finset (W × Fin q)} (ht' : (blowUp H q).IsNClique 3 t')
    (hsub : ({a, b} : Finset W) ⊆ t'.image Prod.fst) :
    ∃ i j : Fin q, t'.filter (fun v => v.1 = a ∨ v.1 = b) = {(a, i), (b, j)} ∧
      ({(a, i), (b, j)} : Finset (W × Fin q)) ⊆ t' := by
  classical
  obtain ⟨x, hx, hxa⟩ : ∃ x ∈ t', x.1 = a := by
    simpa [Finset.mem_image] using hsub (by simp : a ∈ ({a, b} : Finset W))
  obtain ⟨y, hy, hyb⟩ : ∃ y ∈ t', y.1 = b := by
    simpa [Finset.mem_image] using hsub (by simp : b ∈ ({a, b} : Finset W))
  have hunique : ∀ v ∈ t', v.1 = a → v = x := by
    intro v hv hva
    by_contra hne
    have := ht'.1 (Finset.mem_coe.mpr hv) (Finset.mem_coe.mpr hx) hne
    rw [blowUp_adj, hva, hxa] at this
    exact this.ne rfl
  have hunique' : ∀ v ∈ t', v.1 = b → v = y := by
    intro v hv hvb
    by_contra hne
    have := ht'.1 (Finset.mem_coe.mpr hv) (Finset.mem_coe.mpr hy) hne
    rw [blowUp_adj, hvb, hyb] at this
    exact this.ne rfl
  have ex : ((a, x.2) : W × Fin q) = x := by rw [Prod.ext_iff]; exact ⟨hxa.symm, rfl⟩
  have ey : ((b, y.2) : W × Fin q) = y := by rw [Prod.ext_iff]; exact ⟨hyb.symm, rfl⟩
  refine ⟨x.2, y.2, ?_, ?_⟩
  · rw [ex, ey]
    ext v
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hv, hva | hvb⟩
      · exact Or.inl (hunique v hv hva)
      · exact Or.inr (hunique' v hv hvb)
    · rintro (rfl | rfl)
      · exact ⟨hx, Or.inl hxa⟩
      · exact ⟨hy, Or.inr hyb⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · rw [ex]; exact hx
    · rw [ey]; exact hy

/-! ### Projecting a fractional packing of the blow-up -/

/-- The projection of a weight function on the triangles of the blow-up: a triangle of `H` receives
`1/q²` of the total weight of the triangles above it. -/
noncomputable def projWeight (H : SimpleGraph W) [DecidableRel H.Adj] (q : ℕ)
    (w' : Finset (Finset (W × Fin q)) → ℝ) : Finset (Finset W) → ℝ :=
  fun T => if T ∈ triangleHypergraphE H then
    (∑ t' ∈ ((blowUp H q).cliqueFinset 3).filter (fun t' => t'.image Prod.fst = vtxSet T),
      w' (t'.powersetCard 2)) / (q : ℝ) ^ 2 else 0

/-- **The projection of a fractional packing is a fractional packing.** -/
theorem isFracPacking_projWeight (H : SimpleGraph W) [DecidableRel H.Adj] {q : ℕ} (hq : 0 < q)
    {w' : Finset (Finset (W × Fin q)) → ℝ} (hw' : IsFracPacking (blowUp H q) w') :
    IsFracPacking H (projWeight H q w') := by
  classical
  have hq2 : (0:ℝ) < (q:ℝ)^2 := by
    have : (0:ℝ) < q := by exact_mod_cast hq
    positivity
  refine ⟨fun T => ?_, fun T hT => ?_, fun e => ?_⟩
  · rw [projWeight]; split_ifs
    · exact div_nonneg (Finset.sum_nonneg fun _ _ => hw'.1 _) hq2.le
    · exact le_rfl
  · rw [projWeight, ite_eq_right hT]
  · by_cases he2 : #e = 2
    swap
    · have hemp : (triangleHypergraphE H).filter (fun T => e ∈ T) = ∅ := by
        ext T
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hT heT
        rw [triangleHypergraphE, Finset.mem_image] at hT
        obtain ⟨t, ht, rfl⟩ := hT
        rw [Finset.mem_powersetCard] at heT
        exact he2 heT.2
      rw [hemp, Finset.sum_empty]; norm_num
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he2
    set S : Finset (Finset (W × Fin q)) := ((blowUp H q).cliqueFinset 3).filter
      (fun t' => ({a, b} : Finset W) ⊆ t'.image Prod.fst) with hSdef
    set E₀ : Finset (Finset (W × Fin q)) := (univ : Finset (Fin q × Fin q)).image
      (fun p => ({(a, p.1), (b, p.2)} : Finset (W × Fin q))) with hE₀
    rw [sum_triangleHypergraphE_filter H he2 (projWeight H q w')]
    have hstep : ∀ t ∈ (H.cliqueFinset 3).filter (fun t => ({a, b} : Finset W) ⊆ t),
        projWeight H q w' (t.powersetCard 2)
          = (∑ t' ∈ ((blowUp H q).cliqueFinset 3).filter (fun t' => t'.image Prod.fst = t),
              w' (t'.powersetCard 2)) / (q:ℝ)^2 := by
      intro t ht
      rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
      have hmem : t.powersetCard 2 ∈ triangleHypergraphE H := by
        rw [triangleHypergraphE, Finset.mem_image]
        exact ⟨t, SimpleGraph.mem_cliqueFinset_iff.mpr ht.1, rfl⟩
      rw [projWeight, ite_eq_left hmem, vtxSet_powersetCard_two (by rw [ht.1.card_eq]; norm_num)]
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_div, div_le_one hq2]
    have hfibeq : ∀ t ∈ (H.cliqueFinset 3).filter (fun t => ({a, b} : Finset W) ⊆ t),
        ((blowUp H q).cliqueFinset 3).filter (fun t' => t'.image Prod.fst = t)
          = S.filter (fun t' => t'.image Prod.fst = t) := by
      intro t ht
      ext t'
      simp only [hSdef, Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, by rw [h2]; exact (Finset.mem_filter.mp ht).2⟩, h2⟩
      · rintro ⟨⟨h1, -⟩, h2⟩
        exact ⟨h1, h2⟩
    rw [Finset.sum_congr rfl (fun t ht => by rw [hfibeq t ht])]
    have hfib : ∑ t ∈ (H.cliqueFinset 3).filter (fun t => ({a, b} : Finset W) ⊆ t),
        ∑ t' ∈ S.filter (fun t' => t'.image Prod.fst = t), w' (t'.powersetCard 2)
        = ∑ t' ∈ S, w' (t'.powersetCard 2) := by
      apply Finset.sum_fiberwise_of_maps_to
      intro t' ht'
      rw [hSdef, Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht'
      rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff]
      exact ⟨isNClique_image_fst ht'.1, ht'.2⟩
    rw [hfib]
    have hmaps : ∀ t' ∈ S, t'.filter (fun v => v.1 = a ∨ v.1 = b) ∈ E₀ := by
      intro t' ht'
      rw [hSdef, Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht'
      obtain ⟨i, j, hij, -⟩ := blowUp_filter_pair ht'.1 ht'.2
      rw [hij, hE₀, Finset.mem_image]
      exact ⟨(i, j), Finset.mem_univ _, rfl⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    have hinner : ∀ e' ∈ E₀,
        ∑ t' ∈ S.filter (fun t' => t'.filter (fun v => v.1 = a ∨ v.1 = b) = e'),
          w' (t'.powersetCard 2) ≤ 1 := by
      intro e' _
      have hinj : Set.InjOn (fun t' : Finset (W × Fin q) => t'.powersetCard 2)
          ↑(S.filter (fun t' => t'.filter (fun v => v.1 = a ∨ v.1 = b) = e')) := by
        intro s hs t ht hst
        rw [Finset.mem_coe, Finset.mem_filter, hSdef, Finset.mem_filter,
          SimpleGraph.mem_cliqueFinset_iff] at hs ht
        exact powersetCard_two_inj (by have := hs.1.1.card_eq; omega)
          (by have := ht.1.1.card_eq; omega) hst
      rw [← Finset.sum_image (f := w') hinj]
      have hsub : (S.filter (fun t' => t'.filter (fun v => v.1 = a ∨ v.1 = b) = e')).image
          (fun t' => t'.powersetCard 2)
          ⊆ (triangleHypergraphE (blowUp H q)).filter (fun T => e' ∈ T) := by
        intro T hT
        rw [Finset.mem_image] at hT
        obtain ⟨t', ht', rfl⟩ := hT
        rw [Finset.mem_filter, hSdef, Finset.mem_filter,
          SimpleGraph.mem_cliqueFinset_iff] at ht'
        obtain ⟨i, j, hij, -⟩ := blowUp_filter_pair ht'.1.1 ht'.1.2
        have he'2 : #e' = 2 := by
          rw [← ht'.2, hij, Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · rw [triangleHypergraphE, Finset.mem_image]
          exact ⟨t', SimpleGraph.mem_cliqueFinset_iff.mpr ht'.1.1, rfl⟩
        · rw [Finset.mem_powersetCard]
          refine ⟨?_, he'2⟩
          rw [← ht'.2]
          exact Finset.filter_subset _ _
      exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun T' _ _ => hw'.1 T'))
        (hw'.2.2 e')
    calc ∑ e' ∈ E₀, ∑ t' ∈ S.filter (fun t' => t'.filter (fun v => v.1 = a ∨ v.1 = b) = e'),
          w' (t'.powersetCard 2)
        ≤ ∑ _e' ∈ E₀, (1:ℝ) := Finset.sum_le_sum hinner
      _ = (#E₀ : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (q:ℝ)^2 := by
          have hcard : #E₀ ≤ q * q := by
            calc #E₀ ≤ #(univ : Finset (Fin q × Fin q)) := Finset.card_image_le
              _ = q * q := by simp
          calc (#E₀ : ℝ) ≤ ((q * q : ℕ) : ℝ) := by exact_mod_cast hcard
            _ = (q:ℝ)^2 := by push_cast; ring

/-- **The value of the projection is `1/q²` of the value.** -/
theorem sum_projWeight (H : SimpleGraph W) [DecidableRel H.Adj] {q : ℕ} (hq : 0 < q)
    (w' : Finset (Finset (W × Fin q)) → ℝ) :
    (q : ℝ) ^ 2 * ∑ T ∈ triangleHypergraphE H, projWeight H q w' T
      = ∑ T' ∈ triangleHypergraphE (blowUp H q), w' T' := by
  classical
  have hq2 : (0:ℝ) < (q:ℝ)^2 := by
    have : (0:ℝ) < q := by exact_mod_cast hq
    positivity
  have hfib : ∑ t ∈ H.cliqueFinset 3,
      ∑ t' ∈ ((blowUp H q).cliqueFinset 3).filter (fun t' => t'.image Prod.fst = t),
        w' (t'.powersetCard 2)
      = ∑ t' ∈ (blowUp H q).cliqueFinset 3, w' (t'.powersetCard 2) := by
    apply Finset.sum_fiberwise_of_maps_to
    intro t' ht'
    rw [SimpleGraph.mem_cliqueFinset_iff] at ht' ⊢
    exact isNClique_image_fst ht'
  rw [sum_triangleHypergraphE H, sum_triangleHypergraphE (blowUp H q) w']
  have hstep : ∀ t ∈ H.cliqueFinset 3, projWeight H q w' (t.powersetCard 2)
      = (∑ t' ∈ ((blowUp H q).cliqueFinset 3).filter (fun t' => t'.image Prod.fst = t),
          w' (t'.powersetCard 2)) / (q:ℝ)^2 := by
    intro t ht
    rw [SimpleGraph.mem_cliqueFinset_iff] at ht
    have hmem : t.powersetCard 2 ∈ triangleHypergraphE H := by
      rw [triangleHypergraphE, Finset.mem_image]
      exact ⟨t, SimpleGraph.mem_cliqueFinset_iff.mpr ht, rfl⟩
    rw [projWeight, ite_eq_left hmem, vtxSet_powersetCard_two (by rw [ht.card_eq]; norm_num)]
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_div, hfib, mul_comm, div_mul_cancel₀ _ hq2.ne']

/-- **The blow-up bound `ν₃*(H[q]) ≤ q²·ν₃*(H)`.** -/
theorem nu3star_blowUp_le (H : SimpleGraph W) [DecidableRel H.Adj] {q : ℕ} (hq : 0 < q) :
    nu3star (blowUp H q) ≤ (q : ℝ) ^ 2 * nu3star H := by
  classical
  have hq2 : (0:ℝ) < (q:ℝ)^2 := by
    have : (0:ℝ) < q := by exact_mod_cast hq
    positivity
  have hne : {x : ℝ | ∃ w, IsFracPacking (blowUp H q) w ∧
      x = ∑ T ∈ triangleHypergraphE (blowUp H q), w T}.Nonempty :=
    ⟨0, fun _ => 0, ⟨fun _ => le_rfl, fun _ _ => rfl, fun e => by simp⟩, by simp⟩
  rw [nu3star]
  refine csSup_le hne ?_
  rintro x ⟨w', hw', rfl⟩
  rw [← sum_projWeight H hq w']
  exact mul_le_mul_of_nonneg_left
    (le_csSup (nu3star_bddAbove H)
      ⟨projWeight H q w', isFracPacking_projWeight H hq hw', rfl⟩) hq2.le

/-- **The blow-up scaling of the fractional triangle packing number.** -/
theorem nu3star_blowUp (H : SimpleGraph W) [DecidableRel H.Adj] {q : ℕ} (hq : 0 < q) :
    nu3star (blowUp H q) = (q : ℝ) ^ 2 * nu3star H :=
  le_antisymm (nu3star_blowUp_le H hq) (nu3star_blowUp_ge H hq)

/-! ### Axiom check -/

section AxCheck

open Nibble.AX1



end AxCheck

end Nibble.AX1
