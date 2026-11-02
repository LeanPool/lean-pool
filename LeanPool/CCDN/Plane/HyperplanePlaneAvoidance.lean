/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.PolynomialPredicates
public import LeanPool.CCDN.Plane.FiniteFieldBadPlanes
import LeanPool.CCDN.Noether.ClosedFormParameterDegree
import LeanPool.CCDN.Noether.UniversalPlaneSpecialization

/-! A bounded geometrically good plane whose three parameter columns have
an invertible minor in three selected ambient coordinates. This additional
condition allows an effective containing hyperplane to be constructed. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private def planeAnchorMinor (n : ℕ) :
    MvPolynomial (PlaneParameters (Option (Fin (3 + n)))) ℤ :=
  Matrix.det (Matrix.of (fun i j : Fin 3 => X (some (i.castAdd n), j)))

private lemma planeAnchorMinor_eval (n : ℕ)
    (v : PlaneParameters (Option (Fin (3 + n))) → ℤ) :
    eval v (planeAnchorMinor n) =
      Matrix.det (Matrix.of (fun i j : Fin 3 => v (some (i.castAdd n), j))) := by
  simp [planeAnchorMinor, Matrix.det_fin_three]

private lemma planeAnchorMinor_degree (n : ℕ) : (planeAnchorMinor n).totalDegree ≤ 3 := by
  have hh := matrix_det_parameterDegree
    (Matrix.of (fun i j : Fin 3 => (X (some (i.castAdd n), j) :
      MvPolynomial (PlaneParameters (Option (Fin (3 + n)))) ℤ))) 1 (by intros; simp)
  simpa only [planeAnchorMinor, Fintype.card_fin, Nat.mul_one] using hh

private lemma planeAnchorMinor_ne_zero (n : ℕ) : planeAnchorMinor n ≠ 0 := by
  let v : PlaneParameters (Option (Fin (3 + n))) → ℤ :=
    fun p => Option.elim p.1 0 (fun i => if i.val = p.2.val then 1 else 0)
  have hv : eval v (planeAnchorMinor n) = 1 := by
    rw [planeAnchorMinor_eval]
    norm_num [v, Matrix.det_fin_three]
  intro hz
  rw [hz, map_zero] at hv
  norm_num at hv

/-- The extra determinant condition costs only three in the integer grid
size. -/
theorem exists_integer_good_plane_with_anchor {n : ℕ}
    (f : MvPolynomial (Option (Fin (3 + n))) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) :
    ∃ v : PlaneParameters (Option (Fin (3 + n))) → ℤ,
      (∀ p, 0 ≤ v p ∧ v p ≤ 2 * f.totalDegree ^ 3 + 3) ∧
      Matrix.det (Matrix.of (fun i j : Fin 3 => v (some (i.castAdd n), j))) ≠ 0 ∧
      (bivariateMap (Int.castRingHom (AlgebraicClosure ℚ))
        (universalPlaneSection f v)).natDegree = f.totalDegree ∧
      bivariateTotalDegree (bivariateMap (Int.castRingHom (AlgebraicClosure ℚ))
        (universalPlaneSection f v)) = f.totalDegree ∧
      Irreducible (bivariateMap (Int.castRingHom (AlgebraicClosure ℚ))
        (universalPlaneSection f v)) := by
  obtain ⟨v, hv, hminor, hgood⟩ := exists_integer_geometrically_good_plane_avoiding
    f hir hd (planeAnchorMinor n) (planeAnchorMinor_ne_zero n)
  refine ⟨v, ?_, ?_, hgood⟩
  · intro p
    refine ⟨(hv p).1, (hv p).2.trans ?_⟩
    exact_mod_cast Nat.add_le_add_left (planeAnchorMinor_degree n) (2 * f.totalDegree ^ 3)
  · simpa only [planeAnchorMinor_eval] using hminor

end
end CCDN
