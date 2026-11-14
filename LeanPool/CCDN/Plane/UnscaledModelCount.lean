/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Plane.ScaledModelCoordinates
public import LeanPool.CCDN.Plane.ScaledPlaneCount
import LeanPool.CCDN.Algebra.HomogeneousSlice
import LeanPool.CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import LeanPool.CCDN.AuxiliaryPolynomial.PolynomialMapAuxiliary
import LeanPool.CCDN.Plane.ScaledModelPosition

/-! The unit-scaled model gives a coefficient-uniform 2/d fallback and a
large-coefficient O(d^4) count, without requiring a scaling prime. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Real

/-- The homogenization (with scaling factor `1`) of a primitive integer polynomial is
primitive. -/
lemma PrimitiveIntegerPolynomial.scaledHomogenize_one {n : ℕ}
    {f : MvPolynomial (Fin n) ℤ} (hf : PrimitiveIntegerPolynomial f) (d : ℕ) :
    PrimitiveIntegerPolynomial (CCDN.scaledHomogenize d 1 f) := by
  intro c hc
  apply hf c
  intro m
  have h := hc (homogenizedExponent d m)
  simpa only [scaledHomogenize_coefficient, one_pow, one_mul] using h

private lemma unscaled_positioned_points_card_le {M t : ℕ}
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) f))
    (a : Fin 2 → ℤ) (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z)
    (hz : ∀ i, eval (z i) f = 0) (g : MvPolynomial (Fin 3) ℤ)
    (hg : IsPointAuxiliary (homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree 1 f))
      g M (fun i j => eval (z i) (scaledModelCoordinates 1 a j))) :
    t ≤ f.totalDegree * M := by
  obtain ⟨g', hg', he, hnd'⟩ := scaledModelCoordinates_auxiliary_transport 1 a f g
    hg.isHomogeneous hg.not_dvd
  have hf0 : f ≠ 0 := fun h => hir.ne_zero (by simp [h])
  have hchart : affineChart 2 (scaledHomogenize f.totalDegree 1 f) = f := by
    change homogeneousSlice 2 1 (scaledHomogenize f.totalDegree 1 f) = f
    simp only [homogeneousSlice_scaledHomogenize 1 f le_rfl, one_pow, map_one, one_mul]
  have hh := plane_chart_points_card_le_auxiliary_degree (scaledHomogenize f.totalDegree 1 f) g'
    (scaledHomogenize_homogeneous _ _ le_rfl) (scaledHomogenize_ne_zero _ one_ne_zero hf0)
    hg' (hprim.scaledHomogenize_one _) (by rw [hchart]) (by rwa [hchart]) hnd' z hinj
    (by simpa only [hchart] using hz) (fun i => (he (z i)).trans (hg.eval_eq_zero i))
  exact hh

/-- Coefficient positioning removes the coefficient height from the 2/d
fallback bound. This holds for any primitive absolutely irreducible equation. -/
theorem unscaled_plane_finite_count
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {t : ℕ}
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) f)) (hd : 0 < f.totalDegree)
    (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z) {B C : ℝ} (hzB : IsBoxZeroFamily f B z)
    (hC : 0 ≤ C)
    (hcount : PlaneResidueCountBound C f.totalDegree f) :
    (t : ℝ) ≤ max
      ((f.totalDegree : ℝ) * scaledPlaneAuxiliaryDegreeBound f.totalDegree C
        (((f.totalDegree : ℝ) + 1) * B) 1)
      ((34 + 8 * Real.exp (heightDeterminantError C + 20)) * (f.totalDegree : ℝ) ^ 4) := by
  simpa only [Int.cast_one] using
    (scaled_model_plane_count_bounds f hir hd 1 le_rfl z hzB
      (by simpa only [Int.cast_one] using hzB.one_le_radius) hC hcount (fun a M g hg =>
        unscaled_positioned_points_card_le f hprim
          (rational_irreducible_of_charZero_map f hir) a z hinj hzB.eval_eq_zero g hg)).1

/-- A sufficiently large coefficient forces the large-height branch
and gives O(d^4). -/
theorem unscaled_plane_finite_count_large_coefficient
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {t : ℕ}
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) f)) (hd : 0 < f.totalDegree)
    (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z) {B C : ℝ} (hzB : IsBoxZeroFamily f B z)
    (hC : 0 ≤ C)
    (m : Fin 2 →₀ ℕ) (hm : f.coeff m ≠ 0)
    (hheight : 4 * (f.totalDegree : ℝ) * Real.log (((f.totalDegree : ℝ) + 1) * B) ≤
      Real.log |(f.coeff m : ℝ)|)
    (hcount : PlaneResidueCountBound C f.totalDegree f) :
    (t : ℝ) ≤ (34 + 8 * Real.exp (heightDeterminantError C + 20)) * (f.totalDegree : ℝ) ^ 4 := by
  simpa only [Int.cast_one] using
    (scaled_model_plane_count_bounds f hir hd 1 le_rfl z hzB
      (by simpa only [Int.cast_one] using hzB.one_le_radius) hC hcount (fun a M g hg =>
        unscaled_positioned_points_card_le f hprim
          (rational_irreducible_of_charZero_map f hir) a z hinj
          hzB.eval_eq_zero g hg)).2 m hm hheight

end
end CCDN
