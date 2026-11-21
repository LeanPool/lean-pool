/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.NestedDissection.Bounds

/-!
# Nested dissection: fill and operation count

The main theorems for a graph `G` on `Fin n` with a separator tree `t` satisfying the bounds of
`NestedDissection.Bounds` (separators of size `≤ α √m`, boundaries of size `≤ β √m`, parts of
size `≤ 2m/3`), eliminated in the nested dissection order `ndPerm t`
[R. J. Lipton, D. J. Rose, R. E. Tarjan, *Generalized nested dissection*, SIAM J. Numer. Anal.
16 (1979), 346–358]:

* `NestedDissection.card_edgeFinset_fill_le`: the filled graph has at most
  `α * (α + β) * n * (1 + log_{3/2} n)` edges, i.e. `O(n log n)`.
* `NestedDissection.nestedDissection_elimination`: for every matrix `A` over a field whose
  off-diagonal nonzero entries are edges of `G`, elimination of the symmetrically permuted
  matrix restricted to the filled pattern computes exactly the matrix after all `n` steps of
  Gaussian elimination (which holds all pivots and both triangular factors) using at most
  `12 * α * (α + β) ^ 2 * n ^ (3/2)` arithmetic operations, i.e. `O(n ^ (3/2))`.
* `NestedDissection.nestedDissection_det`: the determinant is the product of the diagonal of the
  computed matrix (when all pivots but the last are nonzero, e.g. when all proper leading
  principal minors of the permuted matrix are nonzero, `pivots_ne_zero`).
-/

namespace NestedDissection

open SepTree

@[expose] public section

universe u v

/-- Relabeling preserves the number of later neighbours. -/
theorem card_laterNbrs_comap {W : Type u} {V : Type v} [Fintype W] [Fintype V] (e : W ≃ V)
    {H₀ : SimpleGraph V} [DecidableRel H₀.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]
    (hH : H = H₀.comap e) {r : V → ℕ} {r' : W → ℕ} (hr : ∀ k, r' k = r (e k)) (k : W) :
    (laterNbrs r' H k).card = (laterNbrs r H₀ (e k)).card := by
  subst hH
  refine Finset.card_bij (fun w _ => e w) ?_ ?_ ?_
  · intro w hw
    rw [mem_laterNbrs] at hw ⊢
    simpa [hr] using hw
  · intro a _ b _ h
    exact e.injective h
  · intro x hx
    refine ⟨e.symm x, ?_, by simp⟩
    rw [mem_laterNbrs] at hx ⊢
    simpa [hr] using hx

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
/-- The rank function of the nested dissection order. -/
theorem ndRank_eq {t : SepTree (Fin n)} (hd : IsDissection G t) (hv : t.verts = Finset.univ) :
    (fun x => t.order.idxOf x) = fun x => ((ndPerm t hd hv).symm x : ℕ) :=
  funext fun x => (ndPerm_symm_apply t hd hv x).symm

omit [DecidableRel G.Adj] in
theorem ndRank_injective {t : SepTree (Fin n)} (hd : IsDissection G t)
    (hv : t.verts = Finset.univ) : Function.Injective fun x => t.order.idxOf x := by
  rw [ndRank_eq hd hv]
  exact Fin.val_injective.comp (ndPerm t hd hv).symm.injective

theorem card_verts_eq {t : SepTree (Fin n)} (hv : t.verts = Finset.univ) : t.verts.card = n := by
  rw [hv, Finset.card_univ, Fintype.card_fin]

/-- **Fill of nested dissection is `O(n log n)`.** -/
theorem card_edgeFinset_fill_le {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (t : SepTree (Fin n))
    (hd : IsDissection G t) (hv : t.verts = Finset.univ)
    (hsq : AllNodes (SqrtBound G α β) t) (hs : AllNodes Shrinks t)
    [DecidableRel (fill G fun x => t.order.idxOf x).Adj] :
    ((fill G fun x => t.order.idxOf x).edgeFinset.card : ℝ) ≤
      α * (α + β) * (n * (1 + Real.logb (3 / 2) n)) := by
  rw [← sum_card_laterNbrs (ndRank_injective hd hv) _, ← hv]
  have := sum_card_laterNbrs_le hα hβ t hd (consistent_order t hd)
    (bdryLater_of_verts_eq_univ hv) hsq hs
  rwa [card_verts_eq hv] at this

/-- **Nested dissection elimination in `O(n ^ (3/2))` operations.**  Let `σ = ndPerm t` be the
nested dissection order and `H` the filled graph of the permuted graph.  For every matrix `A`
whose off-diagonal nonzero entries are edges of `G`, elimination of `A.submatrix σ σ`
restricted to `H` computes the stages of Gaussian elimination without pivoting (so its pivots,
`pivots_eq_stage`, and its triangular factors, `upperFactor_eq_stage`,
`lowerFactor_eq_stage`) with at most `12 * α * (α + β) ^ 2 * n ^ (3/2)` operations. -/
theorem nestedDissection_elimination {K : Type u} [Field K] {α β : ℝ} (hα : 0 ≤ α)
    (t : SepTree (Fin n)) (hd : IsDissection G t) (hv : t.verts = Finset.univ)
    (hsq : AllNodes (SqrtBound G α β) t) (hs : AllNodes Shrinks t)
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hH : H = fill (G.comap (ndPerm t hd hv)) Fin.val)
    (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, i ≠ j → A i j ≠ 0 → G.Adj i j) :
    (sparseCounted H (A.submatrix (ndPerm t hd hv) (ndPerm t hd hv)) n).val =
        stage (A.submatrix (ndPerm t hd hv) (ndPerm t hd hv)) n ∧
      ((sparseCounted H (A.submatrix (ndPerm t hd hv) (ndPerm t hd hv)) n).cost.total : ℝ) ≤
        12 * α * (α + β) ^ 2 * (n * √n) := by
  classical
  set σ := ndPerm t hd hv
  set r : Fin n → ℕ := fun x => t.order.idxOf x with hr
  have hrσ : ∀ k : Fin n, (k : ℕ) = r (σ k) := by
    intro k
    rw [hr, ndRank_eq hd hv]
    simp [σ]
  have hcomap : H = (fill G r).comap σ := by
    rw [hH, ← fill_comap]
    congr 1
    funext k
    exact hrσ k
  refine ⟨sparseCounted_val _ (fun i j hij h => ?_) (le_of_eq hH.symm) n, ?_⟩
  · exact hA (σ i) (σ j) (σ.injective.ne hij) h
  have h1 := sparseCounted_total_le H (A.submatrix σ σ)
  have h2 : ∑ k : Fin n, ((laterNbrs Fin.val H k).card + 1) ^ 2 =
      ∑ x ∈ t.verts, ((laterNbrs r (fill G r) x).card + 1) ^ 2 := by
    rw [hv]
    refine (Finset.sum_congr rfl fun k _ => by
      rw [card_laterNbrs_comap σ hcomap (r' := Fin.val) hrσ]).trans ?_
    exact Equiv.sum_comp σ fun x => ((laterNbrs r (fill G r) x).card + 1) ^ 2
  rw [h2] at h1
  have h3 := sum_sq_le hα t hd (consistent_order t hd) (bdryLater_of_verts_eq_univ hv) hsq hs
  rw [card_verts_eq hv] at h3
  have h1' : ((sparseCounted H (A.submatrix σ σ) n).cost.total : ℝ) ≤
      2 * ((∑ x ∈ t.verts, ((laterNbrs r (fill G r) x).card + 1) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast h1
  calc _ ≤ _ := h1'
    _ ≤ 2 * (6 * α * (α + β) ^ 2 * (n * √n)) := by linarith
    _ = _ := by ring

omit [DecidableRel G.Adj] in
/-- **Determinant by nested dissection.**  Under the hypotheses of
`nestedDissection_elimination`, if all pivots but the last of elimination in the nested
dissection order are nonzero, the determinant of `A` is the product of the diagonal entries of
the matrix computed by restricted elimination. -/
theorem nestedDissection_det {K : Type u} [Field K] (t : SepTree (Fin n))
    (hd : IsDissection G t) (hv : t.verts = Finset.univ)
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hH : H = fill (G.comap (ndPerm t hd hv)) Fin.val)
    (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, i ≠ j → A i j ≠ 0 → G.Adj i j)
    (hpiv : ∀ k : Fin n, (k : ℕ) + 1 < n → pivotsIn (ndPerm t hd hv) A k ≠ 0) :
    A.det = ∏ k, (sparseCounted H (A.submatrix (ndPerm t hd hv) (ndPerm t hd hv)) n).val k k := by
  have hval := sparseCounted_val (G := G.comap (ndPerm t hd hv))
    (A.submatrix (ndPerm t hd hv) (ndPerm t hd hv))
    (fun i j hij h => hA _ _ ((ndPerm t hd hv).injective.ne hij) h) (le_of_eq hH.symm) n
  rw [hval, ← det_eq_prod_stage_final _ hpiv, Matrix.det_submatrix_equiv_self]

end

end NestedDissection
