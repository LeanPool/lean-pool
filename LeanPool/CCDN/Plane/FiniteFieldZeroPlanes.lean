/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Plane.FiniteFieldBadPlanes
import LeanPool.CCDN.Noether.UniversalPlaneSpecialization
import LeanPool.CCDN.Plane.FiniteFieldPolynomialZeros

/-! Identically zero sections are bounded separately using their three
defining points. This gives three powers of the field size in the
denominator, even with degenerate parameterizations included. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The usual degree-times-q^(m-1) bound, for arbitrary nonempty finite
coordinate types and affine zeros. -/
lemma finite_field_polynomial_zeros_card {K τ : Type*} [Field K] [Fintype K]
    [Fintype τ] [Nonempty τ] (f : MvPolynomial τ K) (hf : f ≠ 0) :
    Nat.card {x : τ → K // eval x f = 0} ≤
      f.totalDegree * Fintype.card K ^ (Fintype.card τ - 1) := by
  have h := finite_field_polynomial_zeros_mul_card f hf
  have he : Fintype.card K ^ Fintype.card τ =
      Fintype.card K ^ (Fintype.card τ - 1) * Fintype.card K := by
    rw [← pow_succ, Nat.sub_add_cancel Fintype.card_pos]
  rw [he, ← Nat.mul_assoc] at h
  exact Nat.le_of_mul_le_mul_right h Fintype.card_pos

/-- All parameter triples whose restricted polynomial is identically zero. -/
def ZeroPlaneParameters {K σ : Type*} [CommRing K] (f : MvPolynomial σ K) :=
  {v : PlaneParameters σ → K // universalPlaneSection f v = 0}

/-- Sending a zero section to its three defining hypersurface points is
injective. -/
private theorem zero_plane_parameters_card_le_cube {K σ : Type*} [CommRing K]
    [Finite K] [Finite σ] (f : MvPolynomial σ K) :
    Nat.card (ZeroPlaneParameters f) ≤
      (Nat.card {x : σ → K // eval x f = 0}) ^ 3 := by
  classical
  let := Fintype.ofFinite K
  let := Fintype.ofFinite σ
  let Z := {x : σ → K // eval x f = 0}
  let ψ : ZeroPlaneParameters f → (Fin 3 → Z) := fun v j =>
    ⟨planeTriplePointsEquiv v.val j, zero_universalPlaneSection_three_points f v.val v.property j⟩
  have hψ : Function.Injective ψ := by
    intro x y h
    apply Subtype.ext
    apply planeTriplePointsEquiv.injective
    funext j
    exact congrArg Subtype.val (congrFun h j)
  have h := Nat.card_le_card_of_injective ψ hψ
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin] using h

/-- In m ambient coordinates, zero restrictions have at most d^3*q^(3*m-3)
parameter triples. This is substantially smaller than the general bad-plane
bound and controls their q^2-point contribution to incidence averaging. -/
theorem finite_field_zero_plane_parameters_card
    {K σ : Type*} [Field K] [Fintype K] [Fintype σ]
    (f : MvPolynomial (Option σ) K) (hf : f ≠ 0) :
    Nat.card (ZeroPlaneParameters f) ≤
      f.totalDegree ^ 3 * Fintype.card K ^ (3 * Fintype.card σ) := by
  have h := (zero_plane_parameters_card_le_cube f).trans
    (Nat.pow_le_pow_left (finite_field_polynomial_zeros_card f hf) 3)
  simpa only [Fintype.card_option, Nat.add_sub_cancel, mul_pow, ← pow_mul, Nat.mul_comm] using h

end
end CCDN
