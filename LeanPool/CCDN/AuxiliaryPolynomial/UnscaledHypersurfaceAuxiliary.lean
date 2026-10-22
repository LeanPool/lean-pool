/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.HomogeneousSlice
public import LeanPool.CCDN.AuxiliaryPolynomial.AbsoluteAuxiliary
public import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor
import LeanPool.CCDN.Algebra.IntegerRationalIrreducibility
import LeanPool.CCDN.Algebra.ScaledHypersurfaceModel
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceAuxiliaryTheorem
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceCoefficientDichotomy
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Height.ProjectiveIntegerHeight
import LeanPool.CCDN.Plane.UnscaledModelCount

/-! The ordinary homogenization provides an affine auxiliary without a
scaling-prime hypothesis and transfers the coefficient-height dichotomy. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The ordinary homogenization (scaling factor one) of an integer polynomial has the same
coefficient height as the polynomial. -/
lemma integerCoefficientHeight_scaledHomogenize_one {n : ℕ} (d : ℕ)
    (f : MvPolynomial (Fin n) ℤ) :
    integerCoefficientHeight (scaledHomogenize d 1 f) = integerCoefficientHeight f := by
  classical
  have hupper : (integerCoefficientHeight (scaledHomogenize d 1 f) : ℝ) ≤
      integerCoefficientHeight f := by
    apply integerCoefficientHeight_le _ (Nat.cast_nonneg _)
    intro m
    by_cases hm : ∃ k, homogenizedExponent d k = m
    · obtain ⟨k, rfl⟩ := hm
      simpa only [scaledHomogenize_coefficient, one_pow, one_mul] using
        coefficient_abs_le_integerCoefficientHeight f k
    · have hz : (scaledHomogenize d 1 f).coeff m = 0 := by
        simp only [scaledHomogenize, coeff_sum]
        apply Finset.sum_eq_zero
        intro k _
        simp only [coeff_monomial, ite_eq_right (fun h => hm ⟨k, h⟩)]
      rw [hz, Int.cast_zero, abs_zero]
      positivity
  have hlower : (integerCoefficientHeight f : ℝ) ≤
      integerCoefficientHeight (scaledHomogenize d 1 f) := by
    apply integerCoefficientHeight_le _ (Nat.cast_nonneg _)
    intro m
    simpa only [scaledHomogenize_coefficient, one_pow, one_mul] using
      coefficient_abs_le_integerCoefficientHeight (scaledHomogenize d 1 f)
        (homogenizedExponent d m)
  exact_mod_cast le_antisymm hupper hlower

private lemma scaledHomogenize_one_integer_irreducible {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f) (hd : 0 < f.totalDegree) :
    Irreducible (scaledHomogenize f.totalDegree 1 f) := by
  apply (hprim.scaledHomogenize_one _).irreducible_of_rational_map
  rw [scaledHomogenize_map]
  have hdeg : (map (Int.castRingHom ℚ) f).totalDegree = f.totalDegree :=
      totalDegree_map_of_injective Int.cast_injective _
  rw [← hdeg]
  exact scaledHomogenize_irreducible _ (rational_map_irreducible_of_integer f hir hd)
    (by simp)

/-- If a form `G` is not divisible by the ordinary homogenization of a nonzero primitive integer
polynomial `f`, then its dehomogenization at `x₀ = 1` is not divisible by `f`. -/
lemma unscaled_auxiliary_not_dvd {n M : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf0 : f ≠ 0) (hprim : PrimitiveIntegerPolynomial f)
    (G : MvPolynomial (Fin (n + 1)) ℤ) (hGhom : G.IsHomogeneous M)
    (hGnd : ¬ scaledHomogenize f.totalDegree 1 f ∣ G) :
    ¬ f ∣ homogeneousSlice n 1 G := by
  have hslice : homogeneousSlice n 1 (scaledHomogenize f.totalDegree 1 f) = f := by
    simp only [homogeneousSlice_scaledHomogenize 1 f le_rfl, one_pow, map_one, one_mul]
  have hndQ := rational_homogeneousSlice_not_dvd one_ne_zero
    (scaledHomogenize_homogeneous 1 f le_rfl) (scaledHomogenize_ne_zero _ one_ne_zero hf0)
    hGhom (hprim.scaledHomogenize_one _) (by rw [hslice]) hGnd
  rw [hslice] at hndQ
  exact fun h => hndQ (map_dvd (map (Int.castRingHom ℚ)) h)

private lemma unscaled_auxiliary_vanishes {n M : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (G : MvPolynomial (Fin (n + 1)) ℤ)
    (hGhom : G.IsHomogeneous M) {B : ℝ} (hB : 1 ≤ B)
    (hGzero : ∀ P : ProjectivePoint n, P.mulHeight ≤ B →
      P ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) (scaledHomogenize f.totalDegree 1 f)) →
      P ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) G)) :
    ∀ x : IntPoint n, InBox x B → eval x f = 0 →
      eval x (homogeneousSlice n 1 G) = 0 := by
  intro x hx hxf
  let v : IntPoint (n + 1) := Fin.cons 1 x
  have hv0 : v ≠ 0 := by
    intro hz
    have hh := congrFun hz 0
    exact one_ne_zero hh
  let P := Projectivization.mk ℚ (rationalPoint v) (rationalPoint_ne_zero hv0)
  have hvbox (j : Fin (n + 1)) : |(v j : ℝ)| ≤ B := by
    refine Fin.cases ?_ (fun k => hx k) j
    simpa only [v, Fin.cons_zero, Int.cast_one, abs_one] using hB
  have hPB : P.mulHeight ≤ B := projective_integer_height_le v hv0 hvbox
  have hvF : eval v (scaledHomogenize f.totalDegree 1 f) = 0 := by
    rw [scaledHomogenize_eval _ _ le_rfl, hxf, mul_zero]
  have hPF : P ∈ projectiveZeroLocus
      (map (Int.castRingHom ℚ) (scaledHomogenize f.totalDegree 1 f)) := by
    apply (mem_projectiveZeroLocus_mk ((scaledHomogenize_homogeneous 1 f le_rfl).map _) _ _).mpr
    have hh := congrArg (Int.castRingHom ℚ) hvF
    rw [map_eval, map_zero] at hh
    exact hh
  have hcast := (mem_projectiveZeroLocus_mk (hGhom.map _) _ _).mp (hGzero P hPB hPF)
  rw [homogeneousSlice_eval]
  apply Int.cast_injective (α := ℚ)
  change (Int.castRingHom ℚ) (eval v G) = (Int.castRingHom ℚ) 0
  rw [map_eval, map_zero]
  exact hcast

/-- Ordinary homogenization gives an auxiliary in every affine
box, with the height and bad-prime factor of the unscaled model. -/
theorem unscaled_affine_auxiliary {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f) (hd : 0 < f.totalDegree) {B : ℝ} (hB : 1 ≤ B) :
    ∃ g, IsBoxAuxiliary f g B ∧
      (g.totalDegree : ℝ) ≤ hypersurfaceAuxiliaryDegreeBound n f.totalDegree B
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f))
        (integerCoefficientHeight f : ℝ) := by
  let F := scaledHomogenize f.totalDegree 1 f
  have hFhom : F.IsHomogeneous f.totalDegree := scaledHomogenize_homogeneous _ _ le_rfl
  have hFir : Irreducible F := scaledHomogenize_one_integer_irreducible f hprim hir hd
  obtain ⟨M, hM, G, _, hGhom, hGzero, hGnd⟩ := hypersurface_projective_auxiliary F hFhom hd hFir hB
  let g := homogeneousSlice (n + 2) 1 G
  have hgnd : ¬ f ∣ g := unscaled_auxiliary_not_dvd f hir.ne_zero hprim G hGhom hGnd
  refine ⟨g, ⟨fun h => hgnd (by rw [h]; exact dvd_zero _), hgnd,
    unscaled_auxiliary_vanishes f G hGhom hB hGzero⟩, ?_⟩
  have hgM : (g.totalDegree : ℝ) ≤ M := by
    exact_mod_cast homogeneousSlice_degree_le (1 : ℤ) hGhom
  have hh := hgM.trans hM
  simpa only [F, integerCoefficientHeight_scaledHomogenize_one,
    hypersurfaceAuxiliaryDegreeBound, auxDegreeBound, auxMainTerm] using hh

/-- Either the affine equation has controlled coefficient height, or a
degree-at-most-d nonmultiple vanishes on every bounded integer zero. -/
theorem affine_coefficient_height_dichotomy {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf0 : f ≠ 0) (hprim : PrimitiveIntegerPolynomial f)
    {B : ℝ} (hB : 1 ≤ B) :
    Real.log (integerCoefficientHeight f : ℝ) ≤
      ((n + f.totalDegree).choose f.totalDegree : ℝ) *
        Real.log ((n + f.totalDegree).choose f.totalDegree) +
      ((n + f.totalDegree).choose f.totalDegree : ℝ) * f.totalDegree * Real.log B ∨
    ∃ g, IsBoxAuxiliary f g B ∧ g.totalDegree ≤ f.totalDegree := by
  rcases projective_coefficient_height_dichotomy (scaledHomogenize f.totalDegree 1 f)
      (scaledHomogenize_homogeneous 1 f le_rfl) (scaledHomogenize_ne_zero _ one_ne_zero hf0) hB with
    hheight | ⟨G, _, hGhom, hGzero, hGnd⟩
  · left
    simpa only [integerCoefficientHeight_scaledHomogenize_one] using hheight
  · right
    let g := homogeneousSlice n 1 G
    have hgnd : ¬ f ∣ g := unscaled_auxiliary_not_dvd f hf0 hprim G hGhom hGnd
    exact ⟨g, ⟨fun h => hgnd (by rw [h]; exact dvd_zero _), hgnd,
      unscaled_auxiliary_vanishes f G hGhom hB hGzero⟩, homogeneousSlice_degree_le (1 : ℤ) hGhom⟩

end
end CCDN
