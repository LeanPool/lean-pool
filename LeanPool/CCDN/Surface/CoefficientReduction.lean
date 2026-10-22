/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.IdealZeroLocus
public import LeanPool.CCDN.Height.Box
public import LeanPool.CCDN.Height.IntegerCoefficientHeight
public import LeanPool.CCDN.Height.PrimitiveIntegerPolynomial
public import LeanPool.CCDN.Hilbert.AffineCurveDegree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LeanPool.CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import LeanPool.CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceAuxiliary
import LeanPool.CCDN.Hypersurface.NonabsoluteSurfaceCount
import LeanPool.CCDN.Surface.CompleteIntersectionDegreeBudget

/-! Coefficients of a primitive surface equation can be restricted to
polynomial height in the box radius. The complementary case already has
a linear point bound from a degree-at-most-d auxiliary. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem surface_section_count_le
    (f g : CoordinatePolynomial 3) (hf : Irreducible f) (hfg : ¬ f ∣ g)
    {B : ℝ} (hB : 0 ≤ B) :
    (count (zeroLocus f ∩ zeroLocus g) B : ℝ) ≤
      (f.totalDegree : ℝ) * g.totalDegree * (2 * B + 1) := by
  obtain ⟨S, δ, hcurve, hcover, hbudget, _⟩ :=
    exists_completeIntersection_curve_components f g hf hfg
  rw [hcover]
  have hsum : (∑ P ∈ S, (δ P : ℝ)) ≤
      (f.totalDegree : ℝ) * g.totalDegree := by exact_mod_cast hbudget
  exact (finite_curve_union_count_le_box_side S δ (fun P hP =>
    ⟨(hcurve P hP).isPrime, (hcurve P hP).height_eq, (hcurve P hP).degree⟩) hB).trans
      (mul_le_mul_of_nonneg_right hsum (by linarith))

private theorem integer_surface_count_le_of_auxiliary
    (f g : MvPolynomial (Fin 3) ℤ)
    (hf : Irreducible (map (Int.castRingHom ℚ) f))
    (hfg : ¬ map (Int.castRingHom ℚ) f ∣ map (Int.castRingHom ℚ) g)
    {B : ℝ} (hB : 0 ≤ B)
    (hzero : ∀ x : IntPoint 3, InBox x B →
      eval x f = 0 → eval x g = 0) :
    (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
      (f.totalDegree : ℝ) * g.totalDegree * (2 * B + 1) := by
  have hcount : count (zeroLocus (map (Int.castRingHom ℚ) f)) B ≤
      count (zeroLocus (map (Int.castRingHom ℚ) f) ∩
        zeroLocus (map (Int.castRingHom ℚ) g)) B := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hxB, hxf⟩ := mem_integralPoints.mp hx
    have hf0 : eval x f = 0 := by
      apply (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective)
      rw [map_zero, map_eval]
      exact hxf
    have hg0 : eval (rationalPoint x) (map (Int.castRingHom ℚ) g) = 0 := by
      have hh := congrArg (Int.castRingHom ℚ) (hzero x hxB hf0)
      rw [map_eval, map_zero] at hh
      exact hh
    exact mem_integralPoints.mpr ⟨hxB, hxf, hg0⟩
  have hbound := surface_section_count_le (map (Int.castRingHom ℚ) f)
    (map (Int.castRingHom ℚ) g) hf hfg hB
  rw [rational_map_totalDegree, rational_map_totalDegree] at hbound
  exact le_trans (by exact_mod_cast hcount) hbound

/-- The constant `N (log N + d) + 1`, where `N = binom(d + 3, d)` is the number of monomials of
degree at most `d` in three variables, in the logarithmic coefficient-height bound for primitive
surface equations of degree `d`. -/
def surfaceCoefficientLogConstant (d : ℕ) : ℝ :=
  ((3 + d).choose d : ℝ) * (Real.log ((3 + d).choose d) + d) + 1

/-- The coefficient-height constant `surfaceCoefficientLogConstant d` is positive. -/
theorem surfaceCoefficientLogConstant_pos (d : ℕ) :
    0 < surfaceCoefficientLogConstant d := by
  have hh := Real.log_natCast_nonneg ((3 + d).choose d)
  unfold surfaceCoefficientLogConstant
  positivity

/-- The alternative to controlled coefficient height is already O(d²B).
The height constant depends on the degree alone. -/
theorem primitive_surface_coefficient_reduction
    (f : MvPolynomial (Fin 3) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hf : Irreducible (map (Int.castRingHom ℚ) f))
    {B : ℝ} (hB : 1 ≤ B) :
    Real.log (integerCoefficientHeight f : ℝ) ≤
      surfaceCoefficientLogConstant f.totalDegree * (Real.log B + 1) ∨
    (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
      3 * (f.totalDegree : ℝ) ^ 2 * B := by
  have hf0 : f ≠ 0 := by intro h; exact hf.ne_zero (by rw [h, map_zero])
  rcases affine_coefficient_height_dichotomy f hf0 hprim hB with
    hheight | ⟨g, ⟨_, hproper, hzero⟩, hdeg⟩
  · left
    have hlog := Real.log_nonneg hB
    have hNlog := Real.log_natCast_nonneg ((3 + f.totalDegree).choose f.totalDegree)
    have hNd : (0 : ℝ) ≤ ((3 + f.totalDegree).choose f.totalDegree : ℝ) * f.totalDegree := by
      positivity
    have hNlog' : (0 : ℝ) ≤ ((3 + f.totalDegree).choose f.totalDegree : ℝ) *
        Real.log ((3 + f.totalDegree).choose f.totalDegree) := by positivity
    unfold surfaceCoefficientLogConstant
    nlinarith
  · right
    have hproperQ : ¬ map (Int.castRingHom ℚ) f ∣ map (Int.castRingHom ℚ) g :=
      fun h => hproper (hprim.rational_map_dvd_iff.mp h)
    have hcount := integer_surface_count_le_of_auxiliary f g hf hproperQ
      (show 0 ≤ B by linarith) hzero
    have hdegR : (g.totalDegree : ℝ) ≤ f.totalDegree := by exact_mod_cast hdeg
    calc
      _ ≤ (f.totalDegree : ℝ) * g.totalDegree * (2 * B + 1) := hcount
      _ ≤ (f.totalDegree : ℝ) * f.totalDegree * (3 * B) := by
        gcongr
        linarith
      _ = _ := by ring

end
end CCDN
