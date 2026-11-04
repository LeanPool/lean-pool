/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.ProjectivePlaneResidueDeterminant
public import LeanPool.CCDN.Determinant.SingularReduction
import LeanPool.CCDN.Algebra.ProjectiveAffineChart
import LeanPool.CCDN.Plane.ProjectivePlaneBezout

/-! Projective finite-field points consist of the standard affine chart and
at most d points at infinity. The infinity bound is proved by projective
Bezout and introduces no extra leading multiple of p. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem projectivePlaneResidue_infinity_card_le {p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d)
    (hir : Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hproper : ¬ map (Int.castRingHom (ZMod p)) f ∣ X 0) :
    Fintype.card {r : ProjectivePlaneResidue f p // r.val.rep 0 = 0} ≤ d := by
  classical
  let S := {r : ProjectivePlaneResidue f p // r.val.rep 0 = 0}
  have h := projective_plane_common_zeros_card_le (map (Int.castRingHom (ZMod p)) f)
    (X 0) (hf.map _) hir (isHomogeneous_X _ _) hproper
    (fun r : S => r.val.val) (Subtype.val_injective.comp Subtype.val_injective)
    (fun r => r.val.property)
    (fun r => by change eval r.val.val.rep (X 0) = 0; simpa using r.property)
  simpa only [mul_one] using h

private theorem projectivePlaneResidue_affine_card_le {p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) :
    Fintype.card {r : ProjectivePlaneResidue f p // r.val.rep 0 ≠ 0} ≤
      Fintype.card (PlaneResidue (affineChart 2 f) p) := by
  classical
  let S := {r : ProjectivePlaneResidue f p // r.val.rep 0 ≠ 0}
  let ψ : S → PlaneResidue (affineChart 2 f) p := fun r =>
    ⟨projectiveAffineCoordinates r.val.val, by
      have h := projectiveAffineCoordinates_zero (map (Int.castRingHom (ZMod p)) f)
        (hf.map _) r.val.val r.property r.val.property
      rw [affineChart_map, eval_map] at h
      exact h⟩
  apply Fintype.card_le_of_injective ψ
  intro r t he
  apply Subtype.ext
  apply Subtype.ext
  exact projectiveAffineCoordinates_injective r.property t.property (congrArg Subtype.val he)

/-- The projective correction is at most d, preserving the leading p term
in the already proved affine finite-field estimate. -/
theorem projectivePlaneResidue_card_le_affine_add_degree {p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d)
    (hir : Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hproper : ¬ map (Int.castRingHom (ZMod p)) f ∣ X 0) :
    Fintype.card (ProjectivePlaneResidue f p) ≤
      Fintype.card (PlaneResidue (affineChart 2 f) p) + d := by
  classical
  have htotal : Fintype.card {r : ProjectivePlaneResidue f p // r.val.rep 0 ≠ 0} =
      Fintype.card (ProjectivePlaneResidue f p) -
        Fintype.card {r : ProjectivePlaneResidue f p // r.val.rep 0 = 0} :=
    Fintype.card_subtype_compl (fun r : ProjectivePlaneResidue f p => r.val.rep 0 = 0)
  have hle := Fintype.card_subtype_le
    (fun r : ProjectivePlaneResidue f p => r.val.rep 0 = 0)
  have hi := projectivePlaneResidue_infinity_card_le f hf hir hproper
  have ha := projectivePlaneResidue_affine_card_le (p := p) f hf
  omega

end
end CCDN
