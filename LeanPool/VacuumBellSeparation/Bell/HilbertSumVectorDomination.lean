/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.FiniteVectorDomination
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Lp.lpHolder

/-!
Diagonal amplification on the actual Hilbert sum of copies of the original
Hilbert space. A positive functional represented by one matrix coefficient
in any representation is a sum of two genuine vector functionals in that
same representation. The proof uses bounded vector Radon--Nikodym on its
finite amplification, with no cyclicity or separability hypothesis.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open ContinuousLinearMap
open scoped BigOperators InnerProductSpace ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (ι : Type*)

/-- Hilbert sum diagonal operator given by `lp.mapCLM 2 (fun _ => T) (norm_nonneg T) (fun _ =>
le_rfl)`. -/
def hilbertSumDiagonalOperator (T : H →L[ℂ] H) :
    lp (fun _ : ι => H) 2 →L[ℂ] lp (fun _ : ι => H) 2 :=
  lp.mapCLM 2 (fun _ => T) (norm_nonneg T) (fun _ => le_rfl)

omit [CompleteSpace H] in
@[simp] theorem hilbertSumDiagonalOperator_apply (T : H →L[ℂ] H)
    (x : lp (fun _ : ι => H) 2) (i : ι) :
    hilbertSumDiagonalOperator ι T x i = T (x i) := rfl

/-- Hilbert sum diagonal star alg hom. -/
def hilbertSumDiagonalStarAlgHom : (H →L[ℂ] H) →⋆ₐ[ℂ]
    (lp (fun _ : ι => H) 2 →L[ℂ] lp (fun _ : ι => H) 2) where
  toFun := hilbertSumDiagonalOperator ι
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    rfl
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    rfl
  map_add' T S := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    rfl
  map_mul' T S := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    rfl
  commutes' c := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    rfl
  map_star' T := by
    change hilbertSumDiagonalOperator ι (star T) =
      (hilbertSumDiagonalOperator ι T).adjoint
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    apply tsum_congr
    intro i
    simpa only [hilbertSumDiagonalOperator_apply, ContinuousLinearMap.star_eq_adjoint] using
      T.adjoint_inner_left (y i) (x i)

@[simp] theorem hilbertSumDiagonalStarAlgHom_apply (T : H →L[ℂ] H)
    (x : lp (fun _ : ι => H) 2) (i : ι) :
    hilbertSumDiagonalStarAlgHom (H := H) ι T x i = T (x i) := rfl

variable {ι}

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem hilbertSum_hasSum_norm_sq (x : lp (fun _ : ι => H) 2) :
    HasSum (fun i => ‖x i‖ ^ 2) (‖x‖ ^ 2) := by
  simpa [Real.rpow_two] using lp.hasSum_norm (p := 2) (by norm_num) x

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Representation vector positive linear map. -/
def representationVectorPositiveLinearMap
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (x : H) : A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    (((innerSL ℂ x).toLinearMap.comp
      (ContinuousLinearMap.apply ℂ H x).toLinearMap).comp π.toLinearMap)
    (fun _a ha => (nonneg_iff_isPositive.mp (map_nonneg π ha)).inner_nonneg_right x)

@[simp] theorem representationVectorPositiveLinearMap_apply
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (x : H) (a : A) :
    representationVectorPositiveLinearMap π x a = inner ℂ x (π a x) := rfl

/-- Positivity turns an off-diagonal coefficient into a two-vector positive
representation. The reference functional is constructed, not assumed. -/
theorem exists_two_vectors_of_positive_coefficient
    (ψ : A →ₚ[ℂ] ℂ) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (x y : H)
    (he : ∀ a : A, ψ a = inner ℂ x (π a y)) :
    ∃ z : Fin 2 → H, ∀ a : A,
      ψ a = ∑ j, inner ℂ (z j) (π a (z j)) := by
  let χ := representationVectorPositiveLinearMap π x +
    representationVectorPositiveLinearMap π y
  have hχ (a : A) : χ a = inner ℂ x (π a x) + inner ℂ y (π a y) := rfl
  have hdom (a : A) (ha : 0 ≤ a) : ψ a ≤ (1 : ℝ) • χ a := by
    rw [one_smul]
    have hP := nonneg_iff_isPositive.mp (map_nonneg π ha)
    have hd := hP.re_inner_nonneg_right (x - y)
    have hs : (inner ℂ y (π a x)).re = (inner ℂ x (π a y)).re := by
      calc
        _ = (inner ℂ (π a x) y).re := inner_re_symm (𝕜 := ℂ) _ _
        _ = _ := congrArg Complex.re (hP.isSymmetric x y)
    simp only [map_sub, inner_sub_left, inner_sub_right, RCLike.re_eq_complex_re,
      hs] at hd
    have hn := (Complex.nonneg_iff.mp (χ.map_nonneg ha)).1
    have hiψ := (Complex.nonneg_iff.mp (ψ.map_nonneg ha)).2
    have hiχ := (Complex.nonneg_iff.mp (χ.map_nonneg ha)).2
    apply Complex.le_def.mpr
    refine ⟨?_, hiψ.symm.trans hiχ⟩
    rw [he, hχ, Complex.add_re]
    rw [hχ, Complex.add_re] at hn
    linarith
  let π₂ := (finiteDiagonalStarAlgHom (H := H) (Fin 2)).comp π
  let Ω : PiLp 2 (fun _ : Fin 2 => H) := WithLp.toLp 2 ![x, y]
  have hΩ (a : A) : χ a = inner ℂ Ω (π₂ a Ω) := by
    rw [hχ, PiLp.inner_apply]
    simp only [π₂, StarAlgHom.comp_apply, finiteDiagonalStarAlgHom_apply,
      finiteDiagonalOperator_apply, Fin.sum_univ_two]; rfl
  obtain ⟨z, _, hz⟩ := exists_dominated_vector_in_representation χ ψ π₂ Ω hΩ
    1 zero_le_one hdom
  refine ⟨fun j => z j, ?_⟩
  intro a
  calc
    ψ a = inner ℂ z (π₂ a z) := (hz a).symm
    _ = ∑ j, inner ℂ (z j) (π a (z j)) := PiLp.inner_apply z (π₂ a z)

end VacuumBellSeparation.Bipartite
