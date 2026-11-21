/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Nested

/-!
# Separators of squares of graphs of bounded degree

`square` is defined in `NestedDissection/Spec.lean`.

The *square* `square G` of a graph `G` joins two distinct vertices at distance at most `2` in `G`.
The nonzero pattern of a product `Kᵀ K` of matrices with pattern `G` is contained in `square G`.

If `G` has `c √m`-separators and maximum degree at most `Δ`, then `square G` has
`c (Δ + 1) √(Δ + 1) √m`-separators (`PlanarSeparator.HasSqrtSeparators.square`): to separate a
vertex set `U` in the square, separate its closed neighbourhood `U'` (at most `(Δ + 1) #U`
vertices) in `G`, with the weights restricted to `U`, and add to the separator `S` all vertices of
`U` adjacent to `S`. Two remaining vertices of `U` on different sides are neither adjacent nor
have a common neighbour: a common neighbour lies in `U'`, not in `S`, hence on one of the two
sides, adjacent to a vertex of the other side.

Consequently squares of plane graphs of bounded degree have separator trees with boundary bounds
(`PlanarSeparator.exists_sepTree_square`), and nested dissection eliminates matrices with such a
pattern in `O(n ^ (3/2))` operations (`PlanarSeparator.square_nestedDissection_elimination`).

## References

* R. J. Lipton, D. J. Rose, R. E. Tarjan, *Generalized nested dissection*, SIAM J. Numer. Anal.
  16 (1979), 346–358.
-/

@[expose] public section

namespace PlanarSeparator

open Finset NestedDissection NestedDissection.SepTree

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {R : Kasteleyn.RotationSystem G}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma square_adj {i j : V} :
    (square G).Adj i j ↔ i ≠ j ∧ (G.Adj i j ∨ ∃ k, G.Adj i k ∧ G.Adj k j) := Iff.rfl

variable (G) in
/-- The closed neighbourhood of a vertex set. -/
def closedNbhd (U : Finset V) : Finset V := U.biUnion fun u => insert u (G.neighborFinset u)

lemma subset_closedNbhd (U : Finset V) : U ⊆ closedNbhd G U := fun u hu =>
  mem_biUnion.2 ⟨u, hu, mem_insert_self _ _⟩

lemma mem_closedNbhd_of_adj {U : Finset V} {u v : V} (hu : u ∈ U) (h : G.Adj u v) :
    v ∈ closedNbhd G U :=
  mem_biUnion.2 ⟨u, hu, mem_insert_of_mem ((G.mem_neighborFinset u v).2 h)⟩

lemma card_closedNbhd_le {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (U : Finset V) :
    #(closedNbhd G U) ≤ (Δ + 1) * #U := by
  refine card_biUnion_le.trans ?_
  rw [mul_comm, ← smul_eq_mul, ← sum_const]
  exact sum_le_sum fun u _ => (card_insert_le _ _).trans (by simpa using hΔ u)

omit [Fintype V] [DecidableRel G.Adj] in
/-- Separators are also separators for any larger constant. -/
lemma HasSqrtSeparators.mono {c c' : ℝ} (hG : HasSqrtSeparators G c) (h : c ≤ c') :
    HasSqrtSeparators G c' := fun U w hw h1 => by
  obtain ⟨S, A, B, hsep, hS, hA, hB⟩ := hG U w hw h1
  exact ⟨S, A, B, hsep, hS.trans (by gcongr), hA, hB⟩

/-- **Separators of the square.** If `G` has `c √m`-separators and maximum degree at most `Δ`,
then its square has `c (Δ + 1) √(Δ + 1) √m`-separators. -/
theorem HasSqrtSeparators.square {c : ℝ} (hG : HasSqrtSeparators G c) (hc : 0 ≤ c) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) :
    HasSqrtSeparators (square G) (c * (Δ + 1) * √((Δ : ℝ) + 1)) := by
  intro U w hw h1
  set U' := closedNbhd G U
  have hUU' : U ⊆ U' := subset_closedNbhd U
  set w' : V → ℝ := fun v => if v ∈ U then w v else 0
  have hw' : ∀ v, 0 ≤ w' v := fun v => by
    simp only [w']
    split_ifs
    · exact hw v
    · exact le_rfl
  have hw'U : ∀ s : Finset V, s ⊆ U → ∑ v ∈ s, w v = ∑ v ∈ s, w' v := fun s hs =>
    sum_congr rfl fun v hv => by simp [w', hs hv]
  have h1' : ∑ v ∈ U', w' v ≤ 1 := by
    have : ∑ v ∈ U', w' v = ∑ v ∈ U, w v := by
      rw [← sum_subset hUU' fun v _ hv => by simp [w', hv], hw'U U subset_rfl]
    rw [this]
    exact h1
  obtain ⟨S, A, B, hsep, hS, hA, hB⟩ := hG U' w' hw' h1'
  set N := closedNbhd G S
  have hSN : S ⊆ N := subset_closedNbhd S
  set A' := (A ∩ U) \ N
  set B' := (B ∩ U) \ N
  have hA'U : A' ⊆ U := fun v hv => (mem_inter.1 (mem_sdiff.1 hv).1).2
  have hB'U : B' ⊆ U := fun v hv => (mem_inter.1 (mem_sdiff.1 hv).1).2
  refine ⟨U ∩ N, A', B', ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · ext v
    simp only [A', B', mem_union, mem_inter, mem_sdiff]
    constructor
    · rintro ((h | h) | h)
      · exact h.1
      · exact h.1.2
      · exact h.1.2
    · intro hv
      by_cases hvN : v ∈ N
      · exact Or.inl (Or.inl ⟨hv, hvN⟩)
      have hvU' : v ∈ S ∪ A ∪ B := hsep.union_eq ▸ hUU' hv
      simp only [mem_union] at hvU'
      rcases hvU' with (h | h) | h
      · exact absurd (hSN h) hvN
      · exact Or.inl (Or.inr ⟨⟨h, hv⟩, hvN⟩)
      · exact Or.inr ⟨⟨h, hv⟩, hvN⟩
  · exact disjoint_left.2 fun v hv hv' => (mem_sdiff.1 hv').2 (mem_inter.1 hv).2
  · exact disjoint_left.2 fun v hv hv' => (mem_sdiff.1 hv').2 (mem_inter.1 hv).2
  · exact disjoint_of_subset_left (fun v hv => (mem_inter.1 (mem_sdiff.1 hv).1).1)
      (disjoint_of_subset_right (fun v hv => (mem_inter.1 (mem_sdiff.1 hv).1).1) hsep.disjoint)
  · intro a ha b hb hab
    obtain ⟨hai, haN⟩ := mem_sdiff.1 ha
    obtain ⟨haA, haU⟩ := mem_inter.1 hai
    have hbB := (mem_inter.1 (mem_sdiff.1 hb).1).1
    rcases hab.2 with h | ⟨k, hak, hkb⟩
    · exact hsep.not_adj a haA b hbB h
    · have hkU' : k ∈ S ∪ A ∪ B := hsep.union_eq ▸ mem_closedNbhd_of_adj haU hak
      simp only [mem_union] at hkU'
      rcases hkU' with (h | h) | h
      · exact haN (mem_closedNbhd_of_adj h hak.symm)
      · exact hsep.not_adj k h b hbB hkb
      · exact hsep.not_adj a haA k h hak
  · have h1 : #(U ∩ N) ≤ (Δ + 1) * #S :=
      (card_le_card inter_subset_right).trans (card_closedNbhd_le hΔ S)
    have h2 : (#U' : ℝ) ≤ (Δ + 1) * #U := by exact_mod_cast card_closedNbhd_le hΔ U
    have h3 : √(#U' : ℝ) ≤ √((Δ : ℝ) + 1) * √(#U : ℝ) := by
      rw [← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt h2
    have h1' : (#(U ∩ N) : ℝ) ≤ (Δ + 1) * #S := by exact_mod_cast h1
    calc (#(U ∩ N) : ℝ) ≤ (Δ + 1) * #S := h1'
      _ ≤ (Δ + 1) * (c * √(#U' : ℝ)) := by gcongr
      _ ≤ (Δ + 1) * (c * (√((Δ : ℝ) + 1) * √(#U : ℝ))) := by gcongr
      _ = c * (Δ + 1) * √((Δ : ℝ) + 1) * √(#U : ℝ) := by ring
  · rw [hw'U A' hA'U]
    exact (sum_le_sum_of_subset_of_nonneg (fun v hv => (mem_inter.1 (mem_sdiff.1 hv).1).1)
      fun v _ _ => hw' v).trans hA
  · rw [hw'U B' hB'U]
    exact (sum_le_sum_of_subset_of_nonneg (fun v hv => (mem_inter.1 (mem_sdiff.1 hv).1).1)
      fun v _ _ => hw' v).trans hB

/-- The constant of the separator trees of squares of plane graphs of maximum degree `Δ`. -/
def squareTreeConst (Δ : ℕ) : ℝ := 40 * (1062 * ((Δ : ℝ) + 1) ^ 2 + 1)

/-- **Squares of plane graphs of bounded degree have `6 (Δ + 1)² √m`-separators.** -/
theorem hasSqrtSeparators_square_of_isPlane (hR : R.IsPlane) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) : HasSqrtSeparators (square G) (6 * ((Δ : ℝ) + 1) ^ 2) := by
  refine ((hasSqrtSeparators_of_isPlane hR).square (by norm_num) hΔ).mono ?_
  have h0 : (0 : ℝ) ≤ Δ := Nat.cast_nonneg Δ
  have h : √((Δ : ℝ) + 1) ≤ (Δ : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  calc 6 * ((Δ : ℝ) + 1) * √((Δ : ℝ) + 1) ≤ 6 * ((Δ : ℝ) + 1) * ((Δ : ℝ) + 1) := by gcongr
    _ = 6 * ((Δ : ℝ) + 1) ^ 2 := by ring

/-- **Separator trees of squares of plane graphs of bounded degree.** If `G` is plane with maximum
degree at most `Δ`, its square has a separator tree with separator and boundary bounds `T √m`,
`T = 40 (1062 (Δ + 1)² + 1)`, at every subtree with `m` vertices, and parts of at most `2m/3`
vertices. -/
theorem exists_sepTree_square (hR : R.IsPlane) {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) :
    ∃ t : SepTree V, t.verts = univ ∧ IsDissection (square G) t ∧
      AllNodes (SqrtBound (square G) (squareTreeConst Δ) (squareTreeConst Δ)) t ∧
        AllNodes Shrinks t :=
  exists_sepTree_of_separators (hasSqrtSeparators_square_of_isPlane hR hΔ) (by positivity)
    (by rw [sepTreeConst, squareTreeConst]; nlinarith)

/-- **Nested dissection for squares of plane graphs of bounded degree in `O(n ^ (3/2))`
operations.** Let `G` be a plane graph on `Fin n` of maximum degree at most `Δ`. There is a
separator tree `t` of the square of `G` such that, for every matrix `A` whose off-diagonal nonzero
entries join vertices at distance at most `2` in `G` (for instance `Kᵀ K` for a matrix `K` with
pattern `G`), elimination of `A` in the nested dissection order of `t`, restricted to the filled
pattern, computes the stages of Gaussian elimination with at most `12 T (T + T)² n √n`
arithmetic operations, where `T = 40 (1062 (Δ + 1)² + 1)`. -/
theorem square_nestedDissection_elimination {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) :
    ∃ (t : SepTree (Fin n)) (hd : IsDissection (square G) t) (hv : t.verts = univ),
      ∀ {K : Type*} [Field K] (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
        H = fill ((square G).comap (ndPerm t hd hv)) Fin.val →
        ∀ (A : Matrix (Fin n) (Fin n) K), (∀ i j, i ≠ j → A i j ≠ 0 → (square G).Adj i j) →
          (sparseCounted H (A.submatrix (ndPerm t hd hv) (ndPerm t hd hv)) n).val =
              stage (A.submatrix (ndPerm t hd hv) (ndPerm t hd hv)) n ∧
            ((sparseCounted H (A.submatrix (ndPerm t hd hv) (ndPerm t hd hv)) n).cost.total :
                ℝ) ≤ 12 * squareTreeConst Δ * (squareTreeConst Δ + squareTreeConst Δ) ^ 2 *
                  (n * √n) := by
  obtain ⟨t, hv, hd, hsq, hs⟩ := exists_sepTree_square hR hΔ
  exact ⟨t, hd, hv, fun H _ hH A hA =>
    nestedDissection_elimination (by rw [squareTreeConst]; positivity) t hd hv hsq hs H hH A hA⟩

end PlanarSeparator
