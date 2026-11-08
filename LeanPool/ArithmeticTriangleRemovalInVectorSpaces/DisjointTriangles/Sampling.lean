/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Exponent
public import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.Triangle.Basic
import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.LinearMap.Card
import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.TensorPower
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Tactic.Positivity.Finset

/-!
# Few triangles when all degrees are small

This file proves Lemma 5 of Fox and Lovász: if every vertex of `X × Y × Z` lies in at most
`R = ρ * N` triangles, then there are at most `125 * p ^ 2 * ρ ^ (1 + c p) * N ^ 2` triangles. As in
the paper, the first two vertices of each triangle are linearly independent, and no plane contains
the first two vertices of two triangles. The paper intersects `X`, `Y` and `Z` with a uniformly
random subspace of dimension `d`; we use the kernel of a uniformly random linear map
`A : V →ₗ[ZMod p] W`. Its kernel contains `r` given independent vectors with probability
`#W ^ (-r)`, and the expected value of `#(ker A) ^ (1 - c p)` is at most `(1 + #V / #W) ^ (1 - c p)`
by Jensen's inequality.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.adjacentTriangles X Y Z x y z`: the triangles of
  `X × Y × Z` other than `(x, y, z)` that share a vertex with it.
* `ArithmeticTriangleRemovalInVectorSpaces.goodTriangles X Y Z`: the triangles of `X × Y × Z` that
  share no vertex with another triangle of `X × Y × Z`.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.isMulticoloredSumFree_goodTriangles`: the good triangles
  form a multicolored sum-free family.
* `ArithmeticTriangleRemovalInVectorSpaces.card_filter_mem_goodTriangles_ge`: a triangle is good in
  the kernel of at least a proportion `(1 - 3 * R / #W) / #W ^ 2` of the linear maps.
* `ArithmeticTriangleRemovalInVectorSpaces.two_mul_card_triangles_le`: the bound
  `2 * #(triangles X Y Z) ≤ 5 * #W ^ 2 * (1 + #V / #W) ^ (1 - c p)` when `5 * R ≤ #W`.
* `ArithmeticTriangleRemovalInVectorSpaces.card_triangles_le_of_degree_le`: Lemma 5 of Fox and
  Lovász.
-/

public section

open Finset Module Submodule

namespace ArithmeticTriangleRemovalInVectorSpaces

section Good

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The triangles of `X × Y × Z` other than `(x, y, z)` that share a vertex with it. -/
private def adjacentTriangles (X Y Z : Finset G) (x y z : G) : Finset (G × G × G) :=
  (triangles X Y Z).filter fun (x', y', z') ↦ (x' = x ∨ y' = y ∨ z' = z) ∧ (x', y', z') ≠ (x, y, z)

/-- The good triangles of Fox and Lovász: the triangles of `X × Y × Z` that share no vertex with
another triangle of `X × Y × Z`. -/
private def goodTriangles (X Y Z : Finset G) : Finset (G × G × G) :=
  (triangles X Y Z).filter fun (x, y, z) ↦ adjacentTriangles X Y Z x y z = ∅

variable {X Y Z X' Y' Z' : Finset G} {x y z x' y' z' : G}

@[simp]
private lemma mem_adjacentTriangles :
    (x', y', z') ∈ adjacentTriangles X Y Z x y z ↔
      (x', y', z') ∈ triangles X Y Z ∧ (x' = x ∨ y' = y ∨ z' = z) ∧ (x', y', z') ≠ (x, y, z) :=
  mem_filter

@[simp]
private lemma mem_goodTriangles :
    (x, y, z) ∈ goodTriangles X Y Z ↔
      (x, y, z) ∈ triangles X Y Z ∧ adjacentTriangles X Y Z x y z = ∅ :=
  mem_filter

private lemma goodTriangles_subset (X Y Z : Finset G) : goodTriangles X Y Z ⊆ triangles X Y Z :=
  filter_subset _ _

private lemma adjacentTriangles_mono (hX : X' ⊆ X) (hY : Y' ⊆ Y) (hZ : Z' ⊆ Z) :
    adjacentTriangles X' Y' Z' x y z ⊆ adjacentTriangles X Y Z x y z :=
  filter_subset_filter _ (triangles_mono hX hY hZ)

/-- A triangle that shares a vertex with a good triangle `(x, y, z)` is `(x, y, z)` itself. -/
private lemma eq_of_mem_goodTriangles (ht : (x, y, z) ∈ goodTriangles X Y Z)
    (ht' : (x', y', z') ∈ triangles X Y Z) (h : x' = x ∨ y' = y ∨ z' = z) :
    x' = x ∧ y' = y ∧ z' = z := by
  obtain ⟨-, hempty⟩ := mem_goodTriangles.1 ht
  by_contra hne
  have := mem_adjacentTriangles.2 ⟨ht', h, by simpa using hne⟩
  simp [hempty] at this

/-- If every vertex lies in at most `R` triangles, then at most `3 * R` triangles share a vertex
with a given triangle. -/
private lemma card_adjacentTriangles_le {R : ℝ}
    (hX : ∀ v, #((triangles X Y Z).filter fun (x, _, _) ↦ x = v) ≤ R)
    (hY : ∀ v, #((triangles X Y Z).filter fun (_, y, _) ↦ y = v) ≤ R)
    (hZ : ∀ v, #((triangles X Y Z).filter fun (_, _, z) ↦ z = v) ≤ R) (x y z : G) :
    #(adjacentTriangles X Y Z x y z) ≤ 3 * R := by
  have h : adjacentTriangles X Y Z x y z ⊆ ((triangles X Y Z).filter fun (x', _, _) ↦ x' = x) ∪
      ((triangles X Y Z).filter fun (_, y', _) ↦ y' = y) ∪
      (triangles X Y Z).filter fun (_, _, z') ↦ z' = z := by
    rintro ⟨x', y', z'⟩
    simp only [mem_adjacentTriangles, mem_union, mem_filter]
    tauto
  grw [card_le_card h, card_union_le, card_union_le]
  push_cast
  linarith [hX x, hY y, hZ z]

/-- The good triangles form a multicolored sum-free family: if `(x, y, z)`, `(x', y', z')` and
`(x'', y'', z'')` are good, then `x + y' + z'' = 0` only when the three triangles coincide. -/
private lemma isMulticoloredSumFree_goodTriangles :
    IsMulticoloredSumFree (fun (⟨(x, _, _), _⟩ : goodTriangles X Y Z) ↦ x)
      (fun ⟨(_, y, _), _⟩ ↦ y) fun ⟨(_, _, z), _⟩ ↦ z := by
  rintro ⟨⟨x, y, z⟩, hs⟩ ⟨⟨x', y', z'⟩, ht⟩ ⟨⟨x'', y'', z''⟩, hu⟩
  obtain ⟨hx, hy, hz, hsum⟩ := mem_triangles.1 (goodTriangles_subset X Y Z hs)
  obtain ⟨-, hy', -, -⟩ := mem_triangles.1 (goodTriangles_subset X Y Z ht)
  obtain ⟨-, -, hz'', -⟩ := mem_triangles.1 (goodTriangles_subset X Y Z hu)
  simp only [Subtype.mk.injEq, Prod.mk.injEq]
  constructor
  · intro h
    obtain ⟨-, rfl, rfl⟩ := eq_of_mem_goodTriangles hs (mem_triangles.2 ⟨hx, hy', hz'', h⟩)
      (Or.inl rfl)
    obtain ⟨rfl, -, rfl⟩ := eq_of_mem_goodTriangles ht (goodTriangles_subset X Y Z hs)
      (Or.inr (Or.inl rfl))
    obtain ⟨rfl, rfl, -⟩ := eq_of_mem_goodTriangles hu (goodTriangles_subset X Y Z hs)
      (Or.inr (Or.inr rfl))
    simp
  · rintro ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
    exact hsum

end Good

variable {p : ℕ} [Fact p.Prime] {V W ι : Type*} [AddCommGroup V] [Module (ZMod p) V] [Fintype V]
  [DecidableEq V] [AddCommGroup W] [Module (ZMod p) W] [Fintype W] [DecidableEq W]
  {X Y Z : Finset V} {x y z x' y' z' : V}

omit [Fintype V] [DecidableEq V] in
/-- A multicolored sum-free family inside a subspace `U` has at most `Nat.card U ^ (1 - c p)`
members. -/
private lemma IsMulticoloredSumFree.card_le_natCard_rpow [Finite V] [Fintype ι] {x y z : ι → V}
    (h : IsMulticoloredSumFree x y z) {U : Submodule (ZMod p) V} (hx : ∀ i, x i ∈ U)
    (hy : ∀ i, y i ∈ U) (hz : ∀ i, z i ∈ U) :
    (Fintype.card ι : ℝ) ≤ Nat.card U ^ (1 - c p) := by
  have := Fintype.ofFinite U
  have hU : IsMulticoloredSumFree (fun i ↦ (⟨x i, hx i⟩ : U)) (fun i ↦ ⟨y i, hy i⟩)
      fun i ↦ ⟨z i, hz i⟩ := by
    intro i j k
    simpa [Subtype.ext_iff] using h i j k
  simpa [Nat.card_eq_fintype_card] using hU.card_le_card_rpow (p := p)

omit [Fintype V] in
/-- The good triangles of sets inside a subspace `U` form a multicolored sum-free family in `U`,
so there are at most `Nat.card U ^ (1 - c p)` of them. -/
private lemma card_goodTriangles_le [Finite V] (U : Submodule (ZMod p) V) (hX : ∀ x ∈ X, x ∈ U)
    (hY : ∀ y ∈ Y, y ∈ U) (hZ : ∀ z ∈ Z, z ∈ U) :
    (#(goodTriangles X Y Z) : ℝ) ≤ Nat.card U ^ (1 - c p) := by
  rw [← Fintype.card_coe]
  apply IsMulticoloredSumFree.card_le_natCard_rpow isMulticoloredSumFree_goodTriangles
  · rintro ⟨⟨x, y, z⟩, ht⟩
    exact hX x (by simp_all)
  · rintro ⟨⟨x, y, z⟩, ht⟩
    exact hY y (by simp_all)
  · rintro ⟨⟨x, y, z⟩, ht⟩
    exact hZ z (by simp_all)

/-- The arithmetic of Lemma 5 of Fox and Lovász: if `5 * ρ * N ≤ w ≤ 5 * p * ρ * N` and
`0 < ρ ≤ 1`, then `w ^ 2 * (1 + N / w) ^ (1 - c) ≤ 30 * p ^ 2 * ρ ^ (1 + c) * N ^ 2`. -/
private lemma sq_mul_one_add_div_rpow_le {p ρ N w c : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hN : 0 < N)
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) (hw₁ : 5 * (ρ * N) ≤ w) (hw₂ : w ≤ p * (5 * (ρ * N))) :
    w ^ 2 * (1 + N / w) ^ (1 - c) ≤ 30 * p ^ 2 * ρ ^ (1 + c) * N ^ 2 := by
  have hw : 0 < w := lt_of_lt_of_le (by positivity) hw₁
  calc w ^ 2 * (1 + N / w) ^ (1 - c)
      ≤ (p * (5 * (ρ * N))) ^ 2 * (6 / 5 / ρ) ^ (1 - c) := by
        gcongr
        grw [div_le_div_of_nonneg_left hN.le (by positivity) hw₁]
        field_simp
        linarith
    _ = 25 * p ^ 2 * N ^ 2 * (6 / 5) ^ (1 - c) * (ρ ^ 2 / ρ ^ (1 - c)) := by
        rw [Real.div_rpow (by norm_num) hρ₀.le]
        ring
    _ = 25 * p ^ 2 * N ^ 2 * (6 / 5) ^ (1 - c) * ρ ^ (1 + c) := by
        rw [← Real.rpow_two ρ, ← Real.rpow_sub hρ₀]
        ring_nf
    _ ≤ 25 * p ^ 2 * N ^ 2 * (6 / 5) * ρ ^ (1 + c) := by
        grw [Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 6 / 5)
          (by linarith : 1 - c ≤ 1), Real.rpow_one]
    _ = 30 * p ^ 2 * ρ ^ (1 + c) * N ^ 2 := by ring

/-- **Jensen's inequality** for `t ↦ t ^ q` with `0 ≤ q ≤ 1`: a sum of `q`-th powers is at most the
number of terms times the `q`-th power of the mean. -/
private lemma sum_rpow_le_card_mul_rpow {κ : Type*} (s : Finset κ) {f : κ → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∑ i ∈ s, f i ^ q ≤ #s * ((∑ i ∈ s, f i) / #s) ^ q := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hs' : (0 : ℝ) < #s := by exact_mod_cast hs.card_pos
  have := ConcaveOn.le_map_sum (Real.concaveOn_rpow hq₀ hq₁) (t := s)
    (w := fun _ ↦ (#s : ℝ)⁻¹) (p := f) (fun _ _ ↦ by positivity) (by simp [hs'.ne']) hf
  simp only [smul_eq_mul, ← mul_sum] at this
  rwa [inv_mul_le_iff₀ hs', ← div_eq_inv_mul] at this

section Count

variable [Fintype (V →ₗ[ZMod p] W)]

omit [Fintype V] [DecidableEq V] in
/-- The linear maps vanishing at linearly independent vectors `v 0, …, v (r - 1)` form a
proportion `#W ^ (-r)` of all linear maps. -/
private lemma card_filter_forall_apply_eq_zero {r : ℕ} {v : Fin r → V}
    (hv : LinearIndependent (ZMod p) v) :
    (#{A : V →ₗ[ZMod p] W | ∀ i, A (v i) = 0} : ℝ) =
      Fintype.card (V →ₗ[ZMod p] W) / Fintype.card W ^ r := by
  have h := hv.natCard_mul_pow_eq_natCard (K := ZMod p) (W := W)
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  rw [eq_div_iff (pow_pos (Nat.cast_pos.2 Fintype.card_pos) r).ne']
  exact_mod_cast h

omit [Fintype V] [DecidableEq V] in
/-- The linear maps vanishing at a nonzero vector `v` form a proportion `1 / #W` of all linear
maps. -/
private lemma card_filter_apply_eq_zero_of_ne_zero {v : V} (hv : v ≠ 0) :
    (#{A : V →ₗ[ZMod p] W | A v = 0} : ℝ) = Fintype.card (V →ₗ[ZMod p] W) / Fintype.card W := by
  rw [← pow_one (Fintype.card W : ℝ), ← card_filter_forall_apply_eq_zero
    (linearIndependent_unique_iff.2 (by simpa using hv) : LinearIndependent (ZMod p) ![v])]
  simp

omit [Fintype V] [DecidableEq V] in
/-- The linear maps vanishing at linearly independent vectors `x` and `y` form a proportion
`#W ^ (-2)` of all linear maps. -/
private lemma card_filter_apply_eq_zero_of_linearIndependent
    (hli : LinearIndependent (ZMod p) ![x, y]) :
    (#{A : V →ₗ[ZMod p] W | A x = 0 ∧ A y = 0} : ℝ) =
      Fintype.card (V →ₗ[ZMod p] W) / Fintype.card W ^ 2 := by
  rw [← card_filter_forall_apply_eq_zero hli]
  simp [Fin.forall_fin_two]

omit [Fintype V] [DecidableEq V] in
/-- If `x` and `y` are linearly independent and `u` lies outside their span, then the linear maps
vanishing at `u`, `x` and `y` form a proportion `#W ^ (-3)` of all linear maps. -/
private lemma card_filter_apply_eq_zero_of_notMem_span {u : V}
    (hli : LinearIndependent (ZMod p) ![x, y]) (hu : u ∉ span (ZMod p) {x, y}) :
    (#{A : V →ₗ[ZMod p] W | A u = 0 ∧ A x = 0 ∧ A y = 0} : ℝ) =
      Fintype.card (V →ₗ[ZMod p] W) / Fintype.card W ^ 3 := by
  have hv : LinearIndependent (ZMod p) ![u, x, y] :=
    linearIndependent_finCons.2 ⟨hli, by rwa [Matrix.range_cons_cons_empty]⟩
  rw [← card_filter_forall_apply_eq_zero hv]
  simp [Fin.forall_fin_succ]

omit [Fintype V] [DecidableEq V] in
/-- If `x` and `y` are linearly independent and `x'` or `y'` lies outside their span, then the
linear maps vanishing at `x`, `y`, `x'` and `y'` form a proportion at most `#W ^ (-3)` of all
linear maps. -/
private lemma card_filter_apply_eq_zero_le_of_not_and_mem_span
    (hli : LinearIndependent (ZMod p) ![x, y])
    (h : ¬(x' ∈ span (ZMod p) {x, y} ∧ y' ∈ span (ZMod p) {x, y})) :
    (#{A : V →ₗ[ZMod p] W | A x = 0 ∧ A y = 0 ∧ A x' = 0 ∧ A y' = 0} : ℝ) ≤
      Fintype.card (V →ₗ[ZMod p] W) / Fintype.card W ^ 3 := by
  rcases not_and_or.1 h with h | h <;>
  · rw [← card_filter_apply_eq_zero_of_notMem_span hli h]
    exact_mod_cast card_le_card (monotone_filter_right _ fun A ↦ by tauto)

omit [Fintype V] [Module (ZMod p) V] in
/-- If the span of the first two vertices of a triangle `(x, y, z)` contains the first two vertices
of no other triangle, then each triangle sharing a vertex with `(x, y, z)` has one of its first two
vertices outside that span. -/
private lemma not_and_mem_span_of_mem_adjacentTriangles [Module (ZMod p) V]
    (hspan : ∀ x y z, (x, y, z) ∈ triangles X Y Z → ∀ x' y' z', (x', y', z') ∈ triangles X Y Z →
      x' ∈ span (ZMod p) {x, y} → y' ∈ span (ZMod p) {x, y} → x' = x ∧ y' = y)
    (ht : (x, y, z) ∈ triangles X Y Z) (ht' : (x', y', z') ∈ adjacentTriangles X Y Z x y z) :
    ¬(x' ∈ span (ZMod p) {x, y} ∧ y' ∈ span (ZMod p) {x, y}) := by
  rintro ⟨hx', hy'⟩
  obtain ⟨ht'', -, hne⟩ := mem_adjacentTriangles.1 ht'
  obtain ⟨rfl, rfl⟩ := hspan x y z ht x' y' z' ht'' hx' hy'
  simp only [mem_triangles] at ht ht''
  grind

omit [Fintype V] [Fintype W] in
/-- If a linear map `A` vanishes at the first two vertices of a triangle `(x, y, z)` that is not
good in the kernel of `A`, then `A` vanishes at the first two vertices of a triangle sharing a
vertex with `(x, y, z)`. -/
private lemma filter_apply_eq_zero_subset [DecidableEq (V →ₗ[ZMod p] W)]
    (ht : (x, y, z) ∈ triangles X Y Z) :
    ({A : V →ₗ[ZMod p] W | A x = 0 ∧ A y = 0} : Finset _) ⊆
      ({A : V →ₗ[ZMod p] W | (x, y, z) ∈
        goodTriangles (X.filter (A · = 0)) (Y.filter (A · = 0)) (Z.filter (A · = 0))} : Finset _) ∪
      (adjacentTriangles X Y Z x y z).biUnion fun (x', y', _) ↦
        {A : V →ₗ[ZMod p] W | A x = 0 ∧ A y = 0 ∧ A x' = 0 ∧ A y' = 0} := by
  intro A hA
  obtain ⟨-, hAx, hAy⟩ := mem_filter.1 hA
  obtain ⟨hx, hy, hz, hsum⟩ := mem_triangles.1 ht
  have hAz : A z = 0 := by simpa [hAx, hAy] using congr(A $hsum)
  rw [mem_union, or_iff_not_imp_left]
  intro hgood
  obtain ⟨⟨x', y', z'⟩, ht'⟩ := nonempty_iff_ne_empty.2
    (by simpa [hx, hy, hz, hsum, hAx, hAy, hAz] using hgood)
  simp only [mem_biUnion, mem_filter, mem_univ, true_and]
  refine ⟨(x', y', z'), adjacentTriangles_mono (filter_subset _ _) (filter_subset _ _)
    (filter_subset _ _) ht', hAx, hAy, ?_⟩
  simp only [mem_adjacentTriangles, mem_triangles, mem_filter] at ht'
  tauto

omit [Fintype V] in
/-- A triangle `(x, y, z)` is good in the kernel of at least a proportion
`(1 - 3 * R / #W) / #W ^ 2` of the linear maps `A`: its first two vertices lie in the kernel with
probability `#W ^ (-2)`, and each of the at most `3 * R` triangles sharing a vertex with it lies in
the kernel as well with probability at most `#W ^ (-3)`. -/
private lemma card_filter_mem_goodTriangles_ge {R : ℝ}
    (hli : ∀ x y z, (x, y, z) ∈ triangles X Y Z → LinearIndependent (ZMod p) ![x, y])
    (hspan : ∀ x y z, (x, y, z) ∈ triangles X Y Z → ∀ x' y' z', (x', y', z') ∈ triangles X Y Z →
      x' ∈ span (ZMod p) {x, y} → y' ∈ span (ZMod p) {x, y} → x' = x ∧ y' = y)
    (hX : ∀ v, #((triangles X Y Z).filter fun (x, _, _) ↦ x = v) ≤ R)
    (hY : ∀ v, #((triangles X Y Z).filter fun (_, y, _) ↦ y = v) ≤ R)
    (hZ : ∀ v, #((triangles X Y Z).filter fun (_, _, z) ↦ z = v) ≤ R)
    (ht : (x, y, z) ∈ triangles X Y Z) :
    Fintype.card (V →ₗ[ZMod p] W) * (1 - 3 * R / Fintype.card W) / Fintype.card W ^ 2 ≤
      #{A : V →ₗ[ZMod p] W | (x, y, z) ∈
        goodTriangles (X.filter (A · = 0)) (Y.filter (A · = 0)) (Z.filter (A · = 0))} := by
  classical
  have h := card_le_card (filter_apply_eq_zero_subset (p := p) (W := W) ht)
  grw [card_union_le, card_biUnion_le] at h
  rw [← Nat.cast_le (α := ℝ), Nat.cast_add, Nat.cast_sum,
    card_filter_apply_eq_zero_of_linearIndependent (hli x y z ht)] at h
  grw [sum_le_card_nsmul _ _ (Fintype.card (V →ₗ[ZMod p] W) / Fintype.card W ^ 3 : ℝ),
    nsmul_eq_mul, card_adjacentTriangles_le hX hY hZ] at h
  · field_simp at h ⊢
    linarith
  · rintro ⟨x', y', z'⟩ ht'
    exact card_filter_apply_eq_zero_le_of_not_and_mem_span (hli x y z ht)
      (not_and_mem_span_of_mem_adjacentTriangles hspan ht ht')

omit [DecidableEq V] in
/-- The kernels of the linear maps `A : V →ₗ[ZMod p] W` have at most
`#(V →ₗ[ZMod p] W) * (1 + #V / #W)` elements in total: each nonzero vector lies in a proportion
`1 / #W` of the kernels. -/
private lemma sum_card_ker_le :
    ∑ A : V →ₗ[ZMod p] W, (#{v | A v = 0} : ℝ) ≤
      Fintype.card (V →ₗ[ZMod p] W) * (1 + Fintype.card V / Fintype.card W) := by
  classical
  rw [← Nat.cast_sum]
  simp only [card_filter]
  rw [sum_comm]
  simp only [← card_filter]
  rw [Nat.cast_sum, ← add_sum_erase _ _ (mem_univ 0)]
  grw [sum_le_card_nsmul _ _ (Fintype.card (V →ₗ[ZMod p] W) / Fintype.card W : ℝ)]
  · rw [card_erase_of_mem (mem_univ 0), card_univ, nsmul_eq_mul,
      Nat.cast_pred Fintype.card_pos]
    simp only [map_zero, filter_true, card_univ]
    rw [mul_one_add, mul_div_left_comm]
    gcongr
    linarith
  · intro v hv
    rw [card_filter_apply_eq_zero_of_ne_zero (ne_of_mem_erase hv)]

omit [Fintype W] [Fintype (V →ₗ[ZMod p] W)] in
/-- The good triangles in the kernel of `A` number at most `#(ker A) ^ (1 - c p)`. -/
private lemma card_goodTriangles_filter_le (A : V →ₗ[ZMod p] W) :
    (#(goodTriangles (X.filter (A · = 0)) (Y.filter (A · = 0)) (Z.filter (A · = 0))) : ℝ) ≤
      (#{v | A v = 0} : ℝ) ^ (1 - c p) := by
  grw [card_goodTriangles_le (LinearMap.ker A) (fun x hx ↦ by simp_all) (fun y hy ↦ by simp_all)
    fun z hz ↦ by simp_all]
  simp [Nat.card_eq_fintype_card, ← Fintype.card_subtype]

/-- Summing the bound of `card_goodTriangles_le` over the kernels of all linear maps `A`, with
Jensen's inequality for the average size of the kernels. -/
private lemma sum_card_goodTriangles_le :
    ∑ A : V →ₗ[ZMod p] W,
      (#(goodTriangles (X.filter (A · = 0)) (Y.filter (A · = 0)) (Z.filter (A · = 0))) : ℝ) ≤
      Fintype.card (V →ₗ[ZMod p] W) * (1 + Fintype.card V / Fintype.card W) ^ (1 - c p) := by
  have hp := (Fact.out : p.Prime).two_le
  calc ∑ A : V →ₗ[ZMod p] W,
        (#(goodTriangles (X.filter (A · = 0)) (Y.filter (A · = 0)) (Z.filter (A · = 0))) : ℝ)
      ≤ ∑ A : V →ₗ[ZMod p] W, (#{v | A v = 0} : ℝ) ^ (1 - c p) := by
        gcongr with A
        exact card_goodTriangles_filter_le A
    _ ≤ Fintype.card (V →ₗ[ZMod p] W) *
          ((∑ A : V →ₗ[ZMod p] W, (#{v | A v = 0} : ℝ)) / Fintype.card (V →ₗ[ZMod p] W)) ^
            (1 - c p) := by
        simpa using sum_rpow_le_card_mul_rpow univ (fun _ _ ↦ by positivity)
          (by linarith [c_lt_one hp]) (by linarith [c_pos hp])
    _ ≤ Fintype.card (V →ₗ[ZMod p] W) * (1 + Fintype.card V / Fintype.card W) ^ (1 - c p) := by
        grw [sum_card_ker_le, mul_div_cancel_left₀ _ (Nat.cast_pos.2 Fintype.card_pos).ne']
        linarith [c_lt_one hp]

omit [Fintype V] [Fintype W] in
/-- Double counting the pairs `(t, A)` such that the triangle `t` is good in the kernel of `A`. -/
private lemma sum_card_filter_mem_goodTriangles_eq :
    ∑ t ∈ triangles X Y Z, #{A : V →ₗ[ZMod p] W |
      t ∈ goodTriangles (X.filter (A · = 0)) (Y.filter (A · = 0)) (Z.filter (A · = 0))} =
      ∑ A : V →ₗ[ZMod p] W,
        #(goodTriangles (X.filter (A · = 0)) (Y.filter (A · = 0)) (Z.filter (A · = 0))) := by
  simp only [card_filter]
  rw [sum_comm]
  congr with A
  rw [← card_filter, filter_mem_eq_inter, inter_eq_right.2]
  exact (goodTriangles_subset _ _ _).trans
    (triangles_mono (filter_subset _ _) (filter_subset _ _) (filter_subset _ _))

omit [DecidableEq W] [Fintype (V →ₗ[ZMod p] W)] in
/-- Double counting the pairs `(t, A)` such that the triangle `t` is good in the kernel of `A`
bounds the number of triangles. -/
private lemma card_triangles_mul_le {R : ℝ}
    (hli : ∀ x y z, (x, y, z) ∈ triangles X Y Z → LinearIndependent (ZMod p) ![x, y])
    (hspan : ∀ x y z, (x, y, z) ∈ triangles X Y Z → ∀ x' y' z', (x', y', z') ∈ triangles X Y Z →
      x' ∈ span (ZMod p) {x, y} → y' ∈ span (ZMod p) {x, y} → x' = x ∧ y' = y)
    (hX : ∀ v, #((triangles X Y Z).filter fun (x, _, _) ↦ x = v) ≤ R)
    (hY : ∀ v, #((triangles X Y Z).filter fun (_, y, _) ↦ y = v) ≤ R)
    (hZ : ∀ v, #((triangles X Y Z).filter fun (_, _, z) ↦ z = v) ≤ R) :
    #(triangles X Y Z) * (1 - 3 * R / Fintype.card W) ≤
      Fintype.card W ^ 2 * (1 + Fintype.card V / Fintype.card W) ^ (1 - c p) := by
  have := Classical.decEq W
  have := Fintype.ofFinite (V →ₗ[ZMod p] W)
  have h := card_nsmul_le_sum (triangles X Y Z) (fun t ↦ (#{A : V →ₗ[ZMod p] W |
    t ∈ goodTriangles (X.filter (A · = 0)) (Y.filter (A · = 0)) (Z.filter (A · = 0))} : ℝ)) _
    fun ⟨x, y, z⟩ ht ↦ card_filter_mem_goodTriangles_ge hli hspan hX hY hZ ht
  rw [nsmul_eq_mul, ← Nat.cast_sum, sum_card_filter_mem_goodTriangles_eq, Nat.cast_sum] at h
  grw [sum_card_goodTriangles_le] at h
  rw [← mul_le_mul_iff_of_pos_left (by positivity :
    (0 : ℝ) < Fintype.card (V →ₗ[ZMod p] W) / Fintype.card W ^ 2)]
  convert h using 1 <;> field_simp

omit [DecidableEq W] [Fintype (V →ₗ[ZMod p] W)] in
/-- If every vertex lies in at most `R` triangles and `5 * R ≤ #W`, then
`2 * #(triangles X Y Z) ≤ 5 * #W ^ 2 * (1 + #V / #W) ^ (1 - c p)`. -/
private lemma two_mul_card_triangles_le {R : ℝ}
    (hli : ∀ x y z, (x, y, z) ∈ triangles X Y Z → LinearIndependent (ZMod p) ![x, y])
    (hspan : ∀ x y z, (x, y, z) ∈ triangles X Y Z → ∀ x' y' z', (x', y', z') ∈ triangles X Y Z →
      x' ∈ span (ZMod p) {x, y} → y' ∈ span (ZMod p) {x, y} → x' = x ∧ y' = y)
    (hX : ∀ v, #((triangles X Y Z).filter fun (x, _, _) ↦ x = v) ≤ R)
    (hY : ∀ v, #((triangles X Y Z).filter fun (_, y, _) ↦ y = v) ≤ R)
    (hZ : ∀ v, #((triangles X Y Z).filter fun (_, _, z) ↦ z = v) ≤ R)
    (hR : 5 * R ≤ Fintype.card W) :
    (2 : ℝ) * #(triangles X Y Z) ≤
      5 * Fintype.card W ^ 2 * (1 + Fintype.card V / Fintype.card W) ^ (1 - c p) := by
  have h := card_triangles_mul_le (W := W) hli hspan hX hY hZ
  have hR' : (2 / 5 : ℝ) ≤ 1 - 3 * R / Fintype.card W := by
    rw [le_sub_comm, div_le_iff₀ (Nat.cast_pos.2 Fintype.card_pos)]
    linarith
  grw [← hR'] at h
  linarith

end Count

/-- Lemma 5 of Fox and Lovász for `ρ ≤ 1`, given `p ^ n ≤ 5 * ρ * #V < p ^ (n + 1)`. The proof
samples linear maps to `Fin (n + 1) → ZMod p`. -/
private lemma card_triangles_le_of_degree_le_of_pow_le {ρ : ℝ} {n : ℕ}
    (hli : ∀ x y z, (x, y, z) ∈ triangles X Y Z → LinearIndependent (ZMod p) ![x, y])
    (hspan : ∀ x y z, (x, y, z) ∈ triangles X Y Z → ∀ x' y' z', (x', y', z') ∈ triangles X Y Z →
      x' ∈ span (ZMod p) {x, y} → y' ∈ span (ZMod p) {x, y} → x' = x ∧ y' = y)
    (hX : ∀ v, #((triangles X Y Z).filter fun (x, _, _) ↦ x = v) ≤ ρ * Fintype.card V)
    (hY : ∀ v, #((triangles X Y Z).filter fun (_, y, _) ↦ y = v) ≤ ρ * Fintype.card V)
    (hZ : ∀ v, #((triangles X Y Z).filter fun (_, _, z) ↦ z = v) ≤ ρ * Fintype.card V)
    (hρ₀ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hn₁ : p ^ n ≤ 5 * (ρ * Fintype.card V))
    (hn₂ : 5 * (ρ * Fintype.card V) < p ^ (n + 1)) :
    #(triangles X Y Z) ≤ 125 * p ^ 2 * ρ ^ (1 + c p) * Fintype.card V ^ 2 := by
  have hp := (Fact.out : p.Prime).two_le
  have hw : (p : ℝ) ^ (n + 1) ≤ p * (5 * (ρ * Fintype.card V)) := by
    rw [pow_succ']
    gcongr
  have h := two_mul_card_triangles_le (W := Fin (n + 1) → ZMod p) hli hspan hX hY hZ
    (by simpa using hn₂.le)
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow] at h
  linarith [sq_mul_one_add_div_rpow_le hρ₀ hρ₁ (by positivity) (c_pos hp).le (c_lt_one hp).le
    hn₂.le hw, (by positivity : 0 ≤ (p : ℝ) ^ 2 * ρ ^ (1 + c p) * Fintype.card V ^ 2)]

/-- **Lemma 5 of Fox and Lovász.** Let `X`, `Y` and `Z` be sets in a finite vector space `V` over
`ZMod p` such that the first two vertices of each triangle are linearly independent and their span
contains the first two vertices of no other triangle. If every vertex lies in at most `ρ * #V`
triangles, then there are at most `125 * p ^ 2 * ρ ^ (1 + c p) * #V ^ 2` triangles. -/
lemma card_triangles_le_of_degree_le {ρ : ℝ}
    (hli : ∀ x y z, (x, y, z) ∈ triangles X Y Z → LinearIndependent (ZMod p) ![x, y])
    (hspan : ∀ x y z, (x, y, z) ∈ triangles X Y Z → ∀ x' y' z', (x', y', z') ∈ triangles X Y Z →
      x' ∈ span (ZMod p) {x, y} → y' ∈ span (ZMod p) {x, y} → x' = x ∧ y' = y)
    (hX : ∀ v, #((triangles X Y Z).filter fun (x, _, _) ↦ x = v) ≤ ρ * Fintype.card V)
    (hY : ∀ v, #((triangles X Y Z).filter fun (_, y, _) ↦ y = v) ≤ ρ * Fintype.card V)
    (hZ : ∀ v, #((triangles X Y Z).filter fun (_, _, z) ↦ z = v) ≤ ρ * Fintype.card V) :
    #(triangles X Y Z) ≤ 125 * p ^ 2 * ρ ^ (1 + c p) * Fintype.card V ^ 2 := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hN : (0 : ℝ) < Fintype.card V := Nat.cast_pos.2 Fintype.card_pos
  obtain hT | ⟨⟨x, y, z⟩, ht⟩ := (triangles X Y Z).eq_empty_or_nonempty
  · have : 0 ≤ ρ := nonneg_of_mul_nonneg_left ((Nat.cast_nonneg _).trans (hX 0)) hN
    rw [hT, card_empty, Nat.cast_zero]
    positivity
  have hρN : 1 ≤ ρ * Fintype.card V :=
    (hX x).trans' (Nat.one_le_cast.2 (card_pos.2 ⟨_, mem_filter.2 ⟨ht, rfl⟩⟩))
  obtain hρ | hρ := le_or_gt 1 ρ
  · grw [card_triangles_le_card_sq]
    push_cast
    exact le_mul_of_one_le_left (by positivity) (one_le_mul_of_one_le_of_one_le (by nlinarith)
      (Real.one_le_rpow hρ (by linarith [c_pos (p := p) (by exact_mod_cast hp)])))
  obtain ⟨n, hn₁, hn₂⟩ := exists_nat_pow_near (by linarith : 1 ≤ 5 * (ρ * Fintype.card V))
    (by linarith : (1 : ℝ) < p)
  exact card_triangles_le_of_degree_le_of_pow_le hli hspan hX hY hZ
    (pos_of_mul_pos_left (one_pos.trans_le hρN) hN.le) hρ.le hn₁ hn₂

end ArithmeticTriangleRemovalInVectorSpaces
