/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.HeightDeterminant
public import LeanPool.CCDN.Height.CountingHypotheses
public import LeanPool.CCDN.Height.PrimitiveIntegerPolynomial
import LeanPool.CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import LeanPool.CCDN.AuxiliaryPolynomial.PolynomialMapAuxiliary
import LeanPool.CCDN.Plane.ScaledModelCoordinates
import LeanPool.CCDN.Plane.ScaledModelPosition

/-! A prime-scaled plane point bound with the arbitrary coefficient
height eliminated. The sharp finite-field count and a suitable scaling prime
remain explicit hypotheses. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Real

/-- The auxiliary degree bound for a plane equation of degree `d` after translation into a box
of radius `R` and scaling by `p`, with residue constant `C`. The constants `23` and `exp 14` are
explained in `projectivePlaneAbsoluteConstant`. -/
def scaledPlaneAuxiliaryDegreeBound (d : ℕ) (C R p : ℝ) : ℝ :=
  d + Real.log R + 2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 *
    (d : ℝ) ^ 3 * (1 + Real.log p / d) * R ^ (2 / (d : ℝ)) / p ^ (1 / (d : ℝ)) + 2

/-- Count original integer plane points using the translated scaled
model. The determinant estimate is applied to polynomial columns on the
original curve, so its sharp residue-count hypothesis concerns that curve. -/
theorem scaled_plane_finite_count
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {t : ℕ}
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) f))
    (hd : 0 < f.totalDegree) {p : ℕ} (hp : p.Prime) (hp0 : ¬ (p : ℤ) ∣ f.coeff 0)
    (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z)
    {B C : ℝ} (hzB : IsBoxZeroFamily f B z) (hpB : (p : ℝ) ≤ B) (hC : 0 ≤ C)
    (hcount : PlaneResidueCountBound C f.totalDegree f) :
    (t : ℝ) ≤ max
      ((f.totalDegree : ℝ) * scaledPlaneAuxiliaryDegreeBound f.totalDegree C
        (((f.totalDegree : ℝ) + 1) * B) p)
      ((34 + 8 * Real.exp (heightDeterminantError C + 20)) * (f.totalDegree : ℝ) ^ 4) := by
  obtain ⟨hB, hz, hbox⟩ := hzB
  let d := f.totalDegree
  let R := ((d : ℝ) + 1) * B
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hR : 1 ≤ R := one_le_mul_of_one_le_of_one_le (by linarith) hB
  have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hf0 : f ≠ 0 := fun h => hir.ne_zero (by simp [h])
  obtain ⟨a, H, ha, hH, hpH, hc, hlo, hhi⟩ := exists_scaled_model_position f hf0 hd hp1
  let model := homogeneousTranslation ℤ a (scaledHomogenize d (p : ℤ) f)
  have hmhom : model.IsHomogeneous d :=
    homogeneousTranslation_homogeneous a (scaledHomogenize_homogeneous _ _ le_rfl)
  have hm0 : model ≠ 0 := by
    have he := (homogeneousTranslation ℤ a).injective.ne (scaledHomogenize_ne_zero d
      (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero) hf0)
    simpa only [map_zero] using he
  let τ := scaledModelCoordinates (p : ℤ) a
  have hmodel : ∀ i, eval (fun j => eval (z i) (τ j)) model = 0 := by
    intro i
    change eval (fun j => eval (z i) (scaledModelCoordinates (p : ℤ) a j))
      (homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree (p : ℤ) f)) = 0
    rw [scaledModelCoordinates_model_eval, hz i, mul_zero]
  have himagebox : ∀ i j, |(eval (z i) (τ j) : ℝ)| ≤ R := by
    intro i j
    exact scaledModelCoordinates_box hB (by positivity) (by exact_mod_cast hpB) a (z i) ha
      (hbox i) j
  have hirq := rational_irreducible_of_charZero_map f hir
  by_cases hsmall : Real.log H ≤ 4 * d * Real.log R
  · obtain ⟨M, hM, g, hg⟩ := polynomial_map_auxiliary_small_height_degree
      MonomialOrder.lex model hmhom hm0 hd ⟨rfl, hir, hH, hc⟩ τ z hz ⟨hR, hmodel, himagebox⟩ hC
      (hlo.trans hsmall) hcount
    have ht := scaled_positioned_points_card_le f hprim hirq hp hp0 a z hinj hz g hg
    have htR : (t : ℝ) ≤ d * (M : ℝ) := by exact_mod_cast ht
    have hL : 0 < |((MonomialOrder.lex.leadingCoeff model : ℤ) : ℝ)| := by
      exact abs_pos.mpr (Int.cast_ne_zero.mpr (MonomialOrder.lex.leadingCoeff_ne_zero_iff.mpr hm0))
    have hratio := scaled_positioned_height_ratio_le hd hpR (by exact_mod_cast hpH) hL hhi
    have hterm : 2 * Real.exp (heightDeterminantError C + 23) * (d : ℝ) ^ 3 *
        (1 + Real.log H / (d : ℝ) ^ 2) * R ^ (2 / (d : ℝ)) /
          |((MonomialOrder.lex.leadingCoeff model : ℤ) : ℝ)| ^ (1 / (d : ℝ) ^ 2) ≤
        2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 * (d : ℝ) ^ 3 *
          (1 + Real.log p / d) * R ^ (2 / (d : ℝ)) / (p : ℝ) ^ (1 / (d : ℝ)) := by
      let A := 2 * Real.exp (heightDeterminantError C + 23) * (d : ℝ) ^ 3 * R ^ (2 / (d : ℝ))
      have hA : 0 ≤ A := by dsimp [A]; positivity
      convert mul_le_mul_of_nonneg_left hratio hA using 1 <;> dsimp [A] <;> ring
    have hMb : (M : ℝ) ≤ scaledPlaneAuxiliaryDegreeBound d C R p := by
      unfold scaledPlaneAuxiliaryDegreeBound
      linarith
    exact (htR.trans (mul_le_mul_of_nonneg_left hMb hdR.le)).trans (le_max_left _ _)
  · obtain ⟨M, hM, g, hg⟩ := polynomial_map_auxiliary_large_height_degree
      MonomialOrder.lex model hmhom hm0 hd ⟨rfl, hir, hH, hc⟩ τ z hz ⟨hR, hmodel, himagebox⟩ hC
      14 (by norm_num) (le_of_lt (lt_of_not_ge hsmall)) hhi hcount
    have ht := scaled_positioned_points_card_le f hprim hirq hp hp0 a z hinj hz g hg
    have htR : (t : ℝ) ≤ d * (M : ℝ) := by exact_mod_cast ht
    apply (htR.trans (mul_le_mul_of_nonneg_left hM hdR.le)).trans
    calc
      _ = (34 + 8 * Real.exp (heightDeterminantError C + 20)) * (d : ℝ) ^ 4 := by
        rw [show heightDeterminantError C + 6 + 14 = heightDeterminantError C + 20 by ring]
        ring
      _ ≤ _ := le_max_right _ _

end
end CCDN
