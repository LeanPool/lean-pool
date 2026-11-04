/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.PolynomialPredicates
public import LeanPool.CCDN.Height.Box
public import LeanPool.CCDN.Height.PrimitiveIntegerPolynomial
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LeanPool.CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import LeanPool.CCDN.Surface.CoefficientReduction
import LeanPool.CCDN.Surface.ResidueLinearCount
import LeanPool.CCDN.Surface.RetainedCurveCount
import LeanPool.CCDN.Surface.SmallCurveCover
import LeanPool.CCDN.Surface.TopFormBadPrimes
import Mathlib.Algebra.Order.Star.Real

/-! A coefficient-uniform linear bound for primitive affine surface
polynomials of each fixed degree at least five. The argument constructs
its congruence auxiliaries and curve cover. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- For each degree `d ≥ 5`, there is a constant `C` such that every primitive integer
surface equation of degree `d` with absolutely irreducible top-degree form has at most `C B`
integral points of height at most `B` on its zero set, for every `B ≥ 1`. -/
theorem primitive_surface_fixed_degree_linear_bound (d : ℕ) (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin 3) ℤ, PrimitiveIntegerPolynomial f →
      HasAbsIrreducibleTopForm f →
      f.totalDegree = d → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤ C * B := by
  let K := surfaceCoefficientLogConstant d
  have hK : 0 ≤ K := (surfaceCoefficientLogConstant_pos d).le
  let A := surfaceCongruenceDegreeConstant d K
  have hA : 0 ≤ A := (surfaceCongruenceDegreeConstant_pos d K).le
  let A₀ := 2 * (d : ℝ) * A
  have hA₀ : 0 ≤ A₀ := by dsimp only [A₀]; positivity
  let D := A₀ * surfaceResidueLogScale d K
  have hlogscale := surfaceResidueLogScale_one_le d hK
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  obtain ⟨Ccurve, hCcurve, hcurve⟩ := retained_surface_curve_union_bound
  obtain ⟨Cres, hCres, hres⟩ := surface_residue_linear_count d hd K A hK hA
  let Cret := Ccurve * ((d : ℝ) ^ 6 + A₀ * (D ^ 2 * (D + 1) + 1))
  have hCret : 0 ≤ Cret := by dsimp only [Cret]; positivity
  refine ⟨12 * (d : ℝ) ^ 2 + Cret + Cres + 1, by positivity, ?_⟩
  intro f hprim htop hfd B hB
  subst d
  have habs := absolute_irreducible_of_top_homogeneousComponent_irreducible f htop
  have hir := rational_irreducible_of_charZero_map f habs
  have hf0 : f ≠ 0 := by intro hz; exact hir.ne_zero (by rw [hz, map_zero])
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hlogB := Real.log_nonneg hB
  rcases primitive_surface_coefficient_reduction f hprim hir hB with hheight | hlarge
  · have hH : 1 ≤ (integerCoefficientHeight f : ℝ) := by
      exact_mod_cast integerCoefficientHeight_pos f hf0
    have hheight' : Real.log (integerCoefficientHeight f : ℝ) ≤
        K * (Real.log B + 1) := hheight
    have hL := surfaceResidueWindow_one_le f.totalDegree hK hB
    obtain ⟨F, S, δ, hS, hbudget, hcover⟩ :=
      exists_surface_small_curve_residual_cover f habs (by omega) hK hheight'
        (isSurfaceResidueWindow_of_log_height (by omega) hK hB hH
          (coefficient_abs_le_integerCoefficientHeight f) hheight')
    let small := S.filter (fun I => (δ I : ℝ) ≤
      2 * f.totalDegree * A * surfaceResidueLogBudget B
        (surfaceResidueWindow f.totalDegree K B))
    have hsmall (I : Ideal (CoordinatePolynomial 3)) (hI : I ∈ small) :
        IsSurfaceCurve (map (Int.castRingHom ℚ) f) I (δ I) ∧ 0 < δ I :=
      ⟨(hS I (mem_filter.mp hI).1).toIsSurfaceCurve, (hS I (mem_filter.mp hI).1).pos⟩
    have hcap (I : Ideal (CoordinatePolynomial 3)) (hI : I ∈ small) :
        (δ I : ℝ) ≤ D * (Real.log B + 1) := by
      have hh := (mem_filter.mp hI).2
      rw [surfaceResidueLogBudget_window] at hh
      simpa only [D, A₀, mul_assoc] using hh
    have hroot : 1 ≤ B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) :=
      Real.one_le_rpow hB (by positivity)
    have hbudget' : (∑ I ∈ small, (δ I : ℝ)) ≤
        A₀ * B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) * (Real.log B + 1) := by
      calc
        _ ≤ ∑ I ∈ S, (δ I : ℝ) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
        _ ≤ (f.totalDegree : ℝ) * A *
            (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) + 1) * (1 + Real.log B) := hbudget
        _ ≤ (f.totalDegree : ℝ) * A *
            (2 * B ^ (1 / Real.sqrt (f.totalDegree : ℝ))) * (1 + Real.log B) := by
          gcongr
          linarith
        _ = _ := by dsimp only [A₀]; ring
    have hret : (count (⋃ I ∈ small, idealZeroLocus I) B : ℝ) ≤ Cret * B :=
      hcurve f htop hd small δ A₀ D B hA₀ hD hB hsmall hcap hbudget'
    have hresidual := hres f rfl B hB F hir S δ (fun I hI => (hS I hI).toIsSurfaceCurve)
    have hsingular : (count (singularHypersurfaceLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        9 * (f.totalDegree : ℝ) ^ 2 * B := by
      have hh := singular_hypersurface_dimension_growth (n := 1)
        (map (Int.castRingHom ℚ) f) hir hB
      simpa only [rational_map_totalDegree, Nat.cast_one, Nat.cast_ofNat, pow_one,
        show (3 * (1 + 2) : ℝ) = 9 by norm_num] using hh
    have hcoverR : (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        (count (singularHypersurfaceLocus (map (Int.castRingHom ℚ) f)) B : ℝ) +
          count (⋃ I ∈ small, idealZeroLocus I) B +
          count (surfaceResidueResidualLocus F S (surfaceResidueWindow f.totalDegree K B)
            (2 * B ^ (1 / Real.sqrt (f.totalDegree : ℝ))) hL) B := by
      simpa only [Nat.cast_add, small, A] using (Nat.cast_le (α := ℝ)).mpr hcover
    nlinarith [hcoverR, hret, hresidual, hsingular, sq_nonneg (f.totalDegree : ℝ)]
  · nlinarith [hlarge, sq_nonneg (f.totalDegree : ℝ)]

end
end CCDN
