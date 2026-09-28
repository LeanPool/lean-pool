/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — two structural facts about families of block sub-triples

The block-allocation residual `Nibble.AX1.BlockCoverResidualFine` (`Nibble.CoreGapBlockCover`) asks
for a family of block sub-triples `A ⊆ U, B ⊆ W, C ⊆ X` with *prescribed* sizes
`#A ≈ τ·d(W,X)`, `#B ≈ τ·d(U,X)`, `#C ≈ τ·d(U,W)` and pairwise disjoint vertex-pair rectangles.
This file records the two facts a construction uses over and over.

* `Nibble.AX1.cover_approx_of_gridSubTriple` — **the covering sum of one member is balanced**: with
  the prescribed sizes, each of the three terms of the covering sum equals `τ²·xyz` (the product of
  the three cluster densities) up to `2τ + 1`, so the member's whole covering sum is
  `3τ²·xyz ± (6τ + 3)`.  This is what the size prescription of `Nibble.AX1.IsGridSubTriple` is for:
  it *balances* the three cluster pairs of a member, which is exactly the property that fails for
  cluster-edge-disjoint families (`Nibble.AX1.not_blockCoverResidualFineClusterPacking`).

* `Nibble.AX1.tripleRect_disjoint_of_clusters` — **members on nearly disjoint cluster triples never
  clash**: if two members' cluster triples share at most one cluster, their vertex-pair rectangles
  are automatically disjoint.  So the disjointness clause of the residual only has to be checked
  for two members sharing a *cluster pair*, which is what turns the residual into a per-pair
  rectangle-packing problem.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapBlockShape
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapClusterLP

/-! # CoreGapBlockAlloc -/

@[expose] public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### The covering sum of one member -/

/-- A product of two prescribed sizes is the product of the two scaled densities, up to `2τ + 1`. -/
theorem prod_approx_of_sizes {τ y z a b : ℝ} (hτ : 0 ≤ τ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (ha : |a - τ * z| ≤ 1) (hb : |b - τ * y| ≤ 1) :
    |a * b - τ ^ 2 * (y * z)| ≤ 2 * τ + 1 := by
  have key : a * b - τ ^ 2 * (y * z)
      = (a - τ * z) * (b - τ * y) + (τ * z) * (b - τ * y) + (τ * y) * (a - τ * z) := by ring
  have h1 : |(a - τ * z) * (b - τ * y)| ≤ 1 := by
    rw [abs_mul]
    calc |a - τ * z| * |b - τ * y| ≤ 1 * 1 :=
          mul_le_mul ha hb (abs_nonneg _) zero_le_one
      _ = 1 := by ring
  have h2 : |(τ * z) * (b - τ * y)| ≤ τ := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ τ * z)]
    calc τ * z * |b - τ * y| ≤ τ * 1 * 1 := by
          apply mul_le_mul _ hb (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hz1 hτ
      _ = τ := by ring
  have h3 : |(τ * y) * (a - τ * z)| ≤ τ := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ τ * y)]
    calc τ * y * |a - τ * z| ≤ τ * 1 * 1 := by
          apply mul_le_mul _ ha (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hy1 hτ
      _ = τ := by ring
  calc |a * b - τ ^ 2 * (y * z)|
      = |(a - τ * z) * (b - τ * y) + (τ * z) * (b - τ * y) + (τ * y) * (a - τ * z)| := by
        rw [key]
    _ ≤ |(a - τ * z) * (b - τ * y) + (τ * z) * (b - τ * y)| + |(τ * y) * (a - τ * z)| :=
        abs_add_le _ _
    _ ≤ (|(a - τ * z) * (b - τ * y)| + |(τ * z) * (b - τ * y)|) + |(τ * y) * (a - τ * z)| := by
        have := abs_add_le ((a - τ * z) * (b - τ * y)) ((τ * z) * (b - τ * y))
        linarith
    _ ≤ (1 + τ) + τ := by linarith
    _ = 2 * τ + 1 := by ring

/-- **The covering sum of one block sub-triple is balanced.**  With the prescribed sizes of
`Nibble.AX1.IsGridSubTriple`, the covering sum of a member is three times `τ²` times the product of
its three cluster densities, up to an additive `6τ + 3`. -/
theorem cover_approx_of_gridSubTriple (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) {ep de α τ : ℝ} {U W X A B C : Finset V}
    (hτ : 0 ≤ τ) (h : IsGridSubTriple G P ep de α τ U W X A B C) :
    |((G.edgeDensity U W : ℝ) * (#A : ℝ) * (#B : ℝ)
        + (G.edgeDensity U X : ℝ) * (#A : ℝ) * (#C : ℝ)
        + (G.edgeDensity W X : ℝ) * (#B : ℝ) * (#C : ℝ))
      - 3 * τ ^ 2 * ((G.edgeDensity U W : ℝ) * (G.edgeDensity U X : ℝ)
          * (G.edgeDensity W X : ℝ))| ≤ 6 * τ + 3 := by
  obtain ⟨-, -, -, -, -, -, -, hsA, hsB, hsC⟩ := h
  set x : ℝ := (G.edgeDensity U W : ℝ) with hx
  set y : ℝ := (G.edgeDensity U X : ℝ) with hy
  set z : ℝ := (G.edgeDensity W X : ℝ) with hz
  have hx0 : 0 ≤ x := by rw [hx]; exact_mod_cast G.edgeDensity_nonneg U W
  have hx1 : x ≤ 1 := by rw [hx]; exact_mod_cast G.edgeDensity_le_one U W
  have hy0 : 0 ≤ y := by rw [hy]; exact_mod_cast G.edgeDensity_nonneg U X
  have hy1 : y ≤ 1 := by rw [hy]; exact_mod_cast G.edgeDensity_le_one U X
  have hz0 : 0 ≤ z := by rw [hz]; exact_mod_cast G.edgeDensity_nonneg W X
  have hz1 : z ≤ 1 := by rw [hz]; exact_mod_cast G.edgeDensity_le_one W X
  -- the three balanced products
  have hAB : |(#A : ℝ) * (#B : ℝ) - τ ^ 2 * (y * z)| ≤ 2 * τ + 1 :=
    prod_approx_of_sizes hτ hy0 hy1 hz0 hz1 hsA hsB
  have hAC : |(#A : ℝ) * (#C : ℝ) - τ ^ 2 * (x * z)| ≤ 2 * τ + 1 :=
    prod_approx_of_sizes hτ hx0 hx1 hz0 hz1 hsA hsC
  have hBC : |(#B : ℝ) * (#C : ℝ) - τ ^ 2 * (x * y)| ≤ 2 * τ + 1 :=
    prod_approx_of_sizes hτ hx0 hx1 hy0 hy1 hsB hsC
  -- multiply the `i`-th of them by the density of the `i`-th pair
  have step : ∀ {d u : ℝ}, 0 ≤ d → d ≤ 1 → |u| ≤ 2 * τ + 1 → |d * u| ≤ 2 * τ + 1 := by
    intro d u hd0 hd1 hu
    rw [abs_mul, abs_of_nonneg hd0]
    calc d * |u| ≤ 1 * (2 * τ + 1) :=
          mul_le_mul hd1 hu (abs_nonneg _) zero_le_one
      _ = 2 * τ + 1 := by ring
  have h1 : |x * ((#A : ℝ) * (#B : ℝ) - τ ^ 2 * (y * z))| ≤ 2 * τ + 1 := step hx0 hx1 hAB
  have h2 : |y * ((#A : ℝ) * (#C : ℝ) - τ ^ 2 * (x * z))| ≤ 2 * τ + 1 := step hy0 hy1 hAC
  have h3 : |z * ((#B : ℝ) * (#C : ℝ) - τ ^ 2 * (x * y))| ≤ 2 * τ + 1 := step hz0 hz1 hBC
  have hsum : (x * (#A : ℝ) * (#B : ℝ) + y * (#A : ℝ) * (#C : ℝ) + z * (#B : ℝ) * (#C : ℝ))
      - 3 * τ ^ 2 * (x * y * z)
      = x * ((#A : ℝ) * (#B : ℝ) - τ ^ 2 * (y * z))
        + y * ((#A : ℝ) * (#C : ℝ) - τ ^ 2 * (x * z))
        + z * ((#B : ℝ) * (#C : ℝ) - τ ^ 2 * (x * y)) := by ring
  have habs : |(x * (#A : ℝ) * (#B : ℝ) + y * (#A : ℝ) * (#C : ℝ) + z * (#B : ℝ) * (#C : ℝ))
      - 3 * τ ^ 2 * (x * y * z)| ≤ 6 * τ + 3 := by
    rw [hsum]
    calc |x * ((#A : ℝ) * (#B : ℝ) - τ ^ 2 * (y * z))
            + y * ((#A : ℝ) * (#C : ℝ) - τ ^ 2 * (x * z))
            + z * ((#B : ℝ) * (#C : ℝ) - τ ^ 2 * (x * y))|
        ≤ |x * ((#A : ℝ) * (#B : ℝ) - τ ^ 2 * (y * z))
            + y * ((#A : ℝ) * (#C : ℝ) - τ ^ 2 * (x * z))|
          + |z * ((#B : ℝ) * (#C : ℝ) - τ ^ 2 * (x * y))| := abs_add_le _ _
      _ ≤ (|x * ((#A : ℝ) * (#B : ℝ) - τ ^ 2 * (y * z))|
            + |y * ((#A : ℝ) * (#C : ℝ) - τ ^ 2 * (x * z))|)
          + |z * ((#B : ℝ) * (#C : ℝ) - τ ^ 2 * (x * y))| := by
            have := abs_add_le (x * ((#A : ℝ) * (#B : ℝ) - τ ^ 2 * (y * z)))
              (y * ((#A : ℝ) * (#C : ℝ) - τ ^ 2 * (x * z)))
            linarith
      _ ≤ 6 * τ + 3 := by linarith
  exact habs

/-! ### Members on nearly disjoint cluster triples never clash -/

omit [Fintype V] in
/-- The two coordinates of a point of a rectangle lie in **two different** clusters of the
triple. -/
theorem exists_clusters_of_mem_tripleRect {U W X A B C : Finset V}
    (hUW : U ≠ W) (hUX : U ≠ X) (hWX : W ≠ X)
    (hA : A ⊆ U) (hB : B ⊆ W) (hC : C ⊆ X) {u v : V} (h : (u, v) ∈ tripleRect A B C) :
    ∃ S ∈ ({U, W, X} : Finset (Finset V)), ∃ T ∈ ({U, W, X} : Finset (Finset V)),
      S ≠ T ∧ u ∈ S ∧ v ∈ T := by
  classical
  rw [mem_tripleRect_iff, crossAdj] at h
  rcases h with h | h | h | h | h | h
  · exact ⟨U, by simp, W, by simp, hUW, hA h.1, hB h.2⟩
  · exact ⟨W, by simp, U, by simp, hUW.symm, hB h.1, hA h.2⟩
  · exact ⟨U, by simp, X, by simp, hUX, hA h.1, hC h.2⟩
  · exact ⟨X, by simp, U, by simp, hUX.symm, hC h.1, hA h.2⟩
  · exact ⟨W, by simp, X, by simp, hWX, hB h.1, hC h.2⟩
  · exact ⟨X, by simp, W, by simp, hWX.symm, hC h.1, hB h.2⟩

/-- **Automatic disjointness.**  If the cluster triples of two members share at most one cluster,
their vertex-pair rectangles are disjoint.  Hence the disjointness clause of the residual only ever
has to be verified for two members sharing a whole cluster *pair*. -/
theorem tripleRect_disjoint_of_clusters (P : Finpartition (univ : Finset V))
    {U W X U' W' X' A B C A' B' C' : Finset V}
    (hU : U ∈ P.parts) (hW : W ∈ P.parts) (hX : X ∈ P.parts)
    (hU' : U' ∈ P.parts) (hW' : W' ∈ P.parts) (hX' : X' ∈ P.parts)
    (hUW : U ≠ W) (hUX : U ≠ X) (hWX : W ≠ X)
    (hUW' : U' ≠ W') (hUX' : U' ≠ X') (hWX' : W' ≠ X')
    (hA : A ⊆ U) (hB : B ⊆ W) (hC : C ⊆ X)
    (hA' : A' ⊆ U') (hB' : B' ⊆ W') (hC' : C' ⊆ X')
    (hshare : #(({U, W, X} : Finset (Finset V)) ∩ ({U', W', X'} : Finset (Finset V))) ≤ 1) :
    Disjoint (tripleRect A B C) (tripleRect A' B' C') := by
  classical
  rw [Finset.disjoint_left]
  rintro ⟨u, v⟩ hmem hmem'
  obtain ⟨S, hS, T, hT, hST, huS, hvT⟩ :=
    exists_clusters_of_mem_tripleRect hUW hUX hWX hA hB hC hmem
  obtain ⟨S', hS', T', hT', -, huS', hvT'⟩ :=
    exists_clusters_of_mem_tripleRect hUW' hUX' hWX' hA' hB' hC' hmem'
  have hmemP : ∀ {Y : Finset V}, Y ∈ ({U, W, X} : Finset (Finset V)) → Y ∈ P.parts := by
    intro Y hY
    simp only [Finset.mem_insert, Finset.mem_singleton] at hY
    rcases hY with rfl | rfl | rfl <;> assumption
  have hmemP' : ∀ {Y : Finset V}, Y ∈ ({U', W', X'} : Finset (Finset V)) → Y ∈ P.parts := by
    intro Y hY
    simp only [Finset.mem_insert, Finset.mem_singleton] at hY
    rcases hY with rfl | rfl | rfl <;> assumption
  have hSS' : S = S' := P.eq_of_mem_parts (hmemP hS) (hmemP' hS') huS huS'
  have hTT' : T = T' := P.eq_of_mem_parts (hmemP hT) (hmemP' hT') hvT hvT'
  have hSin : S ∈ ({U, W, X} : Finset (Finset V)) ∩ ({U', W', X'} : Finset (Finset V)) :=
    Finset.mem_inter.mpr ⟨hS, hSS' ▸ hS'⟩
  have hTin : T ∈ ({U, W, X} : Finset (Finset V)) ∩ ({U', W', X'} : Finset (Finset V)) :=
    Finset.mem_inter.mpr ⟨hT, hTT' ▸ hT'⟩
  have h2 : 1 < #(({U, W, X} : Finset (Finset V)) ∩ ({U', W', X'} : Finset (Finset V))) :=
    Finset.one_lt_card.mpr ⟨S, hSin, T, hTin, hST⟩
  omega

/-! ### The bookkeeping bridge: value of the family ⟹ the covering clause -/

/-- **The covering clause of the residual follows from a lower bound on the *value* of the
family.**  Write `x, y, z` for the three cluster densities of a member; its *value* is `τ²·xyz`,
one third of its balanced covering sum (`Nibble.AX1.cover_approx_of_gridSubTriple`).  If the total
value of the family recovers the cluster capacity LP of the cluster pairs of density at least `θ`,
up to `E`, then the covering clause of `Nibble.AX1.BlockCoverResidualFine` holds with total error
`θ·|V|²/6 + E + k·(2τ + 1)`.

This is the *tight bookkeeping* of the block-allocation route: by
`Nibble.AX1.cover_sum_le_cluster_capacity` the covering sum of a disjoint family can never exceed
the same capacity LP, so the hypothesis `hval` is not only sufficient but essentially necessary. -/
theorem nu3star_le_cover_of_family_value
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finpartition (univ : Finset V))
    {ep de ep₀ de₀ α τ θ E : ℝ} {k : ℕ} (U W X A B C : ℕ → Finset V)
    (hτ : 0 ≤ τ) (hθ : 0 ≤ θ)
    (hgrid : ∀ i < k, IsGridSubTriple G P ep₀ de₀ α τ (U i) (W i) (X i) (A i) (B i) (C i))
    (hval : (∑ p ∈ P.parts.offDiag.filter (fun p => θ ≤ (G.edgeDensity p.1 p.2 : ℝ)),
              (G.edgeDensity p.1 p.2 : ℝ) * (#p.1 : ℝ) * (#p.2 : ℝ)) / 6
            ≤ (∑ i ∈ Finset.range k, τ ^ 2 * ((G.edgeDensity (U i) (W i) : ℝ)
                * (G.edgeDensity (U i) (X i) : ℝ) * (G.edgeDensity (W i) (X i) : ℝ))) + E) :
    nu3star (G.regularityReduced P ep de)
      ≤ (∑ i ∈ Finset.range k,
          ((G.edgeDensity (U i) (W i) : ℝ) * (#(A i) : ℝ) * (#(B i) : ℝ)
            + (G.edgeDensity (U i) (X i) : ℝ) * (#(A i) : ℝ) * (#(C i) : ℝ)
            + (G.edgeDensity (W i) (X i) : ℝ) * (#(B i) : ℝ) * (#(C i) : ℝ))) / 3
        + (θ * (Fintype.card V : ℝ) ^ 2 / 6 + E + (k : ℝ) * (2 * τ + 1)) := by
  classical
  -- each member's value is at most a third of its covering sum, up to `2τ + 1`
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
  have hcap := nu3star_regularityReduced_le_dense_cluster_capacity G P ep de (θ := θ) hθ
  linarith

/-! ### Axiom check -/

section AxCheck





end AxCheck

end Nibble.AX1
