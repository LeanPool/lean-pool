/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.ScaledHomogenization
public import LeanPool.CCDN.AuxiliaryPolynomial.AbsoluteAuxiliary
public import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor
import LeanPool.CCDN.Algebra.ScaledHypersurfaceModel
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceAuxiliaryTheorem
import LeanPool.CCDN.AuxiliaryPolynomial.ScaledAuxiliaryCount
import LeanPool.CCDN.Height.ProjectiveIntegerHeight

/-! The affine auxiliary polynomial obtained from a prime-scaled
homogeneous model. All point and nondivisibility transports are proved. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- For any prime p<=B avoiding the constant coefficient, construct an
affine auxiliary nonmultiple. The degree retains the exact height and bad-prime
factor of the scaled model, ready for their quantitative estimates. -/
theorem prime_scaled_affine_auxiliary {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f) (hd : 0 < f.totalDegree)
    {p : ℕ} (hp : p.Prime) (hp0 : ¬ (p : ℤ) ∣ f.coeff 0)
    {B : ℝ} (hB : 1 ≤ B) (hpB : (p : ℝ) ≤ B) :
    ∃ g, IsBoxAuxiliary f g B ∧
      (g.totalDegree : ℝ) ≤ hypersurfaceAuxiliaryDegreeBound n f.totalDegree B
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree (p : ℤ) f))
        (integerCoefficientHeight (scaledHomogenize f.totalDegree (p : ℤ) f) : ℝ) := by
  let F := scaledHomogenize f.totalDegree (p : ℤ) f
  have hFhom : F.IsHomogeneous f.totalDegree := scaledHomogenize_homogeneous _ _ le_rfl
  have hFir : Irreducible F := scaledHomogenize_integer_irreducible f hprim hir hd hp hp0
  obtain ⟨M, hM, G, _, hGhom, hGzero, hGnd⟩ := hypersurface_projective_auxiliary F hFhom hd hFir hB
  let g := homogeneousSlice (n + 2) (p : ℤ) G
  have hgndQ := scaled_auxiliary_rational_not_dvd f hir.ne_zero hprim hp hp0 G hGhom hGnd
  have hgnd : ¬ f ∣ g := fun h => hgndQ (map_dvd (map (Int.castRingHom ℚ)) h)
  have hg0 : g ≠ 0 := fun h => hgnd (by rw [h]; exact dvd_zero _)
  refine ⟨g, ⟨hg0, hgnd, ?_⟩, ?_⟩
  swap
  · have hgM : (g.totalDegree : ℝ) ≤ M := by exact_mod_cast homogeneousSlice_degree_le (p : ℤ) hGhom
    exact hgM.trans hM
  · intro x hx hxf
    let v : IntPoint (n + 3) := Fin.cons (p : ℤ) x
    have hv0 : v ≠ 0 := by
      intro hz
      have hh := congrFun hz 0
      have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      exact hpZ hh
    let P := Projectivization.mk ℚ (rationalPoint v) (rationalPoint_ne_zero hv0)
    have hvbox (j : Fin (n + 3)) : |(v j : ℝ)| ≤ B := by
      refine Fin.cases ?_ (fun k => hx k) j
      simpa only [v, Fin.cons_zero, Int.cast_natCast,
        abs_of_nonneg (Nat.cast_nonneg (α := ℝ) p)] using hpB
    have hPB : P.mulHeight ≤ B := projective_integer_height_le v hv0 hvbox
    have hvF : eval v F = 0 := by
      rw [scaledHomogenize_eval _ _ le_rfl, hxf, mul_zero]
    have hPF : P ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) F) := by
      apply (mem_projectiveZeroLocus_mk (hFhom.map _) _ _).mpr
      have hh := congrArg (Int.castRingHom ℚ) hvF
      rw [map_eval, map_zero] at hh
      exact hh
    have hPG := hGzero P hPB hPF
    have hcast := (mem_projectiveZeroLocus_mk (hGhom.map _) _ _).mp hPG
    have hvG : eval v G = 0 := by
      apply Int.cast_injective (α := ℚ)
      have he := map_eval (Int.castRingHom ℚ) v G
      change (Int.castRingHom ℚ) (eval v G) = (Int.castRingHom ℚ) 0
      rw [he, map_zero]
      exact hcast
    rw [homogeneousSlice_eval]
    exact hvG

end
end CCDN
