/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.AuxiliaryPolynomial.AffineHypersurfaceAuxiliary
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Height.ScaledHypersurfaceHeight
import LeanPool.CCDN.Surface.TopFormAuxiliaryEstimate
import LeanPool.CCDN.Surface.TopFormBadPrimes

/-! A coefficient-uniform auxiliary for an affine hypersurface with absolutely
irreducible leading form. This is the dimension-general form of CCDN (4-3-1). -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The constant in the degree bound of the auxiliary polynomial for affine hypersurfaces in
`n + 2` variables with absolutely irreducible top-degree form, independent of the
coefficients. -/
def topFormAuxiliaryConstant (n : ℕ) : ℝ :=
  affineHypersurfaceAuxiliaryConstant n *
    ((n + 1 : ℝ) * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 2) + 2)

/-- The auxiliary constant `topFormAuxiliaryConstant n` is positive. -/
lemma topFormAuxiliaryConstant_pos (n : ℕ) : 0 < topFormAuxiliaryConstant n := by
  have hC := affineHypersurfaceAuxiliaryConstant_pos n
  have hH := zero_le_one.trans (hypersurfaceHeightConstant_one_le (n + 2))
  unfold topFormAuxiliaryConstant
  positivity

private theorem primitive_top_form_auxiliary {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : HasAbsIrreducibleTopForm f)
    {B : ℝ} (hB : 1 ≤ B) :
    ∃ g, IsBoxAuxiliary f g B ∧
      (g.totalDegree : ℝ) ≤ topFormAuxiliaryConstant n *
        (f.totalDegree : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) *
          B ^ (1 / (f.totalDegree : ℝ) ^ (1 / (n + 1 : ℝ))) := by
  have hfIr := hprim.irreducible_of_absolute_top hir
  have habs := absolute_irreducible_of_top_homogeneousComponent_irreducible f hir
  have hd := absolute_integer_polynomial_totalDegree_pos f habs
  let d := f.totalDegree
  let F := homogeneousComponent d f
  have hF0 : F ≠ 0 := homogeneousComponent_totalDegree_ne_zero hfIr.ne_zero
  have hFd : F.totalDegree = d := (homogeneousComponent_isHomogeneous d f).totalDegree hF0
  let L := (integerCoefficientHeight F : ℝ)
  let q := 1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
  let K := (n + 1 : ℝ) * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 2)
  have hL : 1 ≤ L := leading_height_one_le f hfIr.ne_zero
  have hratio : hypersurfaceBadPrimeFactor f / L ^ q ≤ K := by
    calc
      _ ≤ hypersurfaceBadPrimeFactor F / L ^ q := div_le_div_of_nonneg_right
        (hypersurfaceBadPrimeFactor_le_top_homogeneousComponent f hir) (by positivity)
      _ ≤ _ := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          hypersurface_badPrime_fractional_height_bound F hF0 hFd (r := n + 1) (by omega) hd
  obtain ⟨g, hg, hgdeg⟩ := affine_hypersurface_auxiliary f hprim hfIr hd hB
  refine ⟨g, hg, hgdeg.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_left
    (affineAuxiliaryDegreeExpression_le_of_badPrime_ratio n hd hB hL hratio)
    (affineHypersurfaceAuxiliaryConstant_pos n).le
  unfold topFormAuxiliaryConstant
  convert hh using 1
  ring

/-- Uniform auxiliary existence for every integer equation whose highest
homogeneous component is absolutely irreducible. Integer content is removed
inside the proof; the final constant depends only on ambient dimension. -/
theorem top_form_auxiliary_rational {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ)
    (hir : HasAbsIrreducibleTopForm f)
    {B : ℝ} (hB : 1 ≤ B) :
    ∃ g : MvPolynomial (Fin (n + 2)) ℤ, g ≠ 0 ∧
      ¬ map (Int.castRingHom ℚ) f ∣ map (Int.castRingHom ℚ) g ∧
      (g.totalDegree : ℝ) ≤ topFormAuxiliaryConstant n *
        (f.totalDegree : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) *
          B ^ (1 / (f.totalDegree : ℝ) ^ (1 / (n + 1 : ℝ))) ∧
      ∀ x : IntPoint (n + 2), InBox x B → eval x f = 0 → eval x g = 0 := by
  have hf0 : f ≠ 0 := by intro hz; exact hir.ne_zero (by simp [hz])
  obtain ⟨c, u, hc, huprim, he⟩ := exists_primitive_integer_factor f hf0
  obtain ⟨huDegree, huTop⟩ := absolute_top_irreducible_of_integer_scalar_factor hc he hir
  obtain ⟨g, ⟨hg0, hgnd, hgz⟩, hgdeg⟩ := primitive_top_form_auxiliary u huprim huTop hB
  have hudvd : u ∣ f := ⟨C c, by rw [he]; ring⟩
  refine ⟨g, hg0, ?_, ?_, ?_⟩
  · intro h
    exact hgnd (huprim.rational_map_dvd_iff.mp ((map_dvd (map (Int.castRingHom ℚ)) hudvd).trans h))
  · simpa only [huDegree] using hgdeg
  · intro x hx hxf
    apply hgz x hx
    rw [he, eval_mul, eval_C] at hxf
    exact (mul_eq_zero.mp hxf).resolve_left hc

end
end CCDN
