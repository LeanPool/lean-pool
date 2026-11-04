/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hypersurface.GraphHyperplaneRestriction
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Plane.HyperplanePlaneAvoidance
import LeanPool.CCDN.Plane.IntegerPlaneHeight
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
Constructing a good rational hyperplane with a bounded integer normal.
The degree-nine bound is a polynomial replacement for the precise avoidance
polynomial in corrected CCDN Lemma 4.3.7.

A bounded integral equation obtained from three independent rows.
Cramer's rule uses row-replacement determinants, so the same elementary
3! T³ bound controls both the coefficients and their common denominator.
-/

@[expose] public section
namespace CCDN
noncomputable section

private lemma three_by_three_det_abs_le (M : Matrix (Fin 3) (Fin 3) ℤ) (T : ℕ)
    (hM : ∀ i j, |M i j| ≤ (T : ℤ)) :
    |M.det| ≤ 6 * (T : ℤ) ^ 3 := by
  have hh := Matrix.det_le (abv := AbsoluteValue.abs) hM
  simpa only [AbsoluteValue.abs_apply, Fintype.card_fin, Nat.factorial_succ,
    Nat.factorial_zero, Nat.reduceAdd, Nat.reduceMul, nsmul_eq_mul, Nat.cast_ofNat] using hh

/-- The bounded row relation in integral coordinates. In particular the
coefficient multiplying the extra row is nonzero, without clearing a further
denominator after solving the linear system. -/
private theorem exists_bounded_three_row_relation
    (M : Matrix (Fin 3) (Fin 3) ℤ) (w : Fin 3 → ℤ) (T : ℕ)
    (hM : ∀ i j, |M i j| ≤ (T : ℤ))
    (hw : ∀ j, |w j| ≤ (T : ℤ)) (hdet : M.det ≠ 0) :
    ∃ a : Fin 3 → ℤ,
      (∀ j, ∑ i, a i * M i j = M.det * w j) ∧
      (∀ i, |a i| ≤ 6 * (T : ℤ) ^ 3) ∧
      M.det ≠ 0 ∧ |M.det| ≤ 6 * (T : ℤ) ^ 3 := by
  let a := M.transpose.cramer w
  refine ⟨a, ?_, ?_, hdet, three_by_three_det_abs_le M T hM⟩
  · have hh := Matrix.mulVec_cramer M.transpose w
    rw [Matrix.mulVec_transpose, Matrix.det_transpose] at hh
    intro j
    simpa only [a, Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] using congrFun hh j
  · intro i
    change |M.transpose.cramer w i| ≤ _
    rw [Matrix.cramer_transpose_apply]
    apply three_by_three_det_abs_le (M.updateRow i w) T
    intro j k
    by_cases hji : j = i
    · subst j
      simpa using hw k
    · rw [Matrix.updateRow_ne hji]
      exact hM j k

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial
local notation "K" => AlgebraicClosure ℚ

/-- The height bound `6 * (2 * d ^ 3 + 3) ^ 3` for the integer normal of a good hyperplane
section of a degree-`d` hypersurface. -/
def goodHyperplaneHeight (d : ℕ) : ℕ := 6 * (2 * d ^ 3 + 3) ^ 3

/-- In at least four variables there is a hyperplane
`D*x₀ = ∑ aᵢ*xᵢ` whose restriction is geometrically irreducible of full
degree. Its integer normal has height polynomial in the degree and is
independent of the coefficient height of the original equation. -/
theorem exists_bounded_geometrically_good_hyperplane {n : ℕ}
    (f : MvPolynomial (Option (Fin (3 + n))) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) :
    ∃ (D : ℤ) (a : Fin (3 + n) → ℤ),
      D ≠ 0 ∧ |D| ≤ (goodHyperplaneHeight f.totalDegree : ℤ) ∧
      (∀ i, |a i| ≤ (goodHyperplaneHeight f.totalDegree : ℤ)) ∧
      (graphHyperplaneRestriction (fun i => (a i : ℚ) / D)
        (map (Int.castRingHom ℚ) f)).totalDegree = f.totalDegree ∧
      AbsolutelyIrreducibleRat (graphHyperplaneRestriction (fun i => (a i : ℚ) / D)
        (map (Int.castRingHom ℚ) f)) := by
  classical
  let T := 2 * f.totalDegree ^ 3 + 3
  obtain ⟨v, hv, hminor, _, hplanedegree, hplaneir⟩ :=
    exists_integer_good_plane_with_anchor f hir hd
  let M : Matrix (Fin 3) (Fin 3) ℤ :=
    Matrix.of (fun i j => v (some (i.castAdd n), j))
  let w : Fin 3 → ℤ := fun j => v (none, j)
  have hvT (p : PlaneParameters (Option (Fin (3 + n)))) : |v p| ≤ (T : ℤ) := by
    rw [abs_of_nonneg (hv p).1]
    simpa only [T, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using (hv p).2
  obtain ⟨b, hrelation, hb, hD, hDb⟩ := exists_bounded_three_row_relation M w T
    (fun i j => hvT (some (i.castAdd n), j)) (fun j => hvT (none, j)) hminor
  let D := M.det
  let a : Fin (3 + n) → ℤ := Fin.addCases b (fun _ : Fin n => 0)
  have hrel (j : Fin 3) : D * v (none, j) = ∑ i, a i * v (some i, j) := by
    rw [Fin.sum_univ_add]
    simpa only [a, Fin.addCases_left, Fin.addCases_right, zero_mul,
      Finset.sum_const_zero, add_zero, M, w, D, Matrix.of_apply] using (hrelation j).symm
  have hheight : (6 : ℤ) * (T : ℤ) ^ 3 = (goodHyperplaneHeight f.totalDegree : ℤ) := by
    simp only [goodHyperplaneHeight, T, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat]
  have haheight (i : Fin (3 + n)) : |a i| ≤ (goodHyperplaneHeight f.totalDegree : ℤ) := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [a, Fin.addCases_left, hheight] using hb j
    · simp only [a, Fin.addCases_right, abs_zero]
      exact Nat.cast_nonneg _
  let α : Fin (3 + n) → ℚ := fun i => (a i : ℚ) / D
  let αK : Fin (3 + n) → K := fun i => (a i : K) / D
  let vK : PlaneParameters (Option (Fin (3 + n))) → K := (Int.castRingHom K) ∘ v
  have hDK : (D : K) ≠ 0 := by exact_mod_cast hD
  have hcontain (j : Fin 3) : vK (none, j) = ∑ i, αK i * vK (some i, j) := by
    have hh : (D : K) * (v (none, j) : K) = ∑ i, (a i : K) * (v (some i, j) : K) := by
      exact_mod_cast hrel j
    change (v (none, j) : K) = ∑ i, ((a i : K) / D) * (v (some i, j) : K)
    calc
      _ = ((D : K) * (v (none, j) : K)) / D := by field_simp [hDK]
      _ = (∑ i, (a i : K) * (v (some i, j) : K)) / D := by rw [hh]
      _ = _ := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hfdegree : (map (Int.castRingHom K) f).totalDegree = f.totalDegree :=
      totalDegree_map_of_injective Int.cast_injective _
  have hsection := universalPlaneSection_map (Int.castRingHom K) f v
  have hgood := graphHyperplaneRestriction_irreducible_of_plane
    (map (Int.castRingHom K) f) αK vK hcontain
    (by simpa only [vK, hsection] using hplaneir)
    (by simpa only [vK, hsection, hfdegree] using hplanedegree)
  let φ : ℚ →+* K := algebraMap ℚ K
  have hmapf : map φ (map (Int.castRingHom ℚ) f) = map (Int.castRingHom K) f := by
    rw [map_map]
    congr 1
  have hα : φ ∘ α = αK := by
    funext i
    simp [φ, α, αK]
  have hmap : map φ (graphHyperplaneRestriction α (map (Int.castRingHom ℚ) f)) =
      graphHyperplaneRestriction αK (map (Int.castRingHom K) f) := by
    rw [graphHyperplaneRestriction_map, hα, hmapf]
  have hmapdegree (g : MvPolynomial (Fin (3 + n)) ℚ) :
      (map φ g).totalDegree = g.totalDegree := totalDegree_map_of_injective φ.injective _
  refine ⟨D, a, hD, hDb.trans_eq hheight, haheight, ?_, ?_⟩
  · rw [← hmapdegree, hmap, hgood.1, hfdegree]
  · change Irreducible (map φ (graphHyperplaneRestriction α (map (Int.castRingHom ℚ) f)))
    rw [hmap]
    exact hgood.2

end
end CCDN
