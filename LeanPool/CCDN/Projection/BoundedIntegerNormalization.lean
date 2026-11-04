/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.IntegerLinearForms
public import LeanPool.CCDN.Hilbert.FilteredHilbertPolynomial
public import LeanPool.CCDN.Projection.ProjectiveClosureProjection
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import LeanPool.CCDN.Hilbert.FullDimension
import LeanPool.CCDN.Projection.BoundedClosureElimination
import LeanPool.CCDN.Projection.ClosureIntegralComposition
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! Constructive bounded linear Noether normalization. The coefficients of
the integer linear forms are bounded by n! (d+1)^n, and the map of projective closures
fixing the homogenizing coordinate is integral as well. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The coefficient bound `n! * (d + 1) ^ n` for the bounded linear Noether normalization of a
degree-`d` variety in `n` variables. -/
def integerNormalizationHeight (n d : ℕ) : ℕ := n.factorial * (d + 1) ^ n

/-- The normalization height is positive. -/
lemma integerNormalizationHeight_pos (n d : ℕ) : 0 < integerNormalizationHeight n d := by
  dsimp [integerNormalizationHeight]
  positivity

private lemma integerNormalizationHeight_mono (n : ℕ) {d e : ℕ} (h : d ≤ e) :
    integerNormalizationHeight n d ≤ integerNormalizationHeight n e := by
  dsimp [integerNormalizationHeight]
  gcongr

private lemma integerNormalizationHeight_step (n d : ℕ) :
    n * integerNormalizationHeight n d * (d + 1) ≤
      integerNormalizationHeight (n + 1) d := by
  dsimp [integerNormalizationHeight]
  rw [Nat.factorial_succ, pow_succ]
  nlinarith [Nat.zero_le (n.factorial * (d + 1) ^ n * (d + 1))]

/-- Integer linear normalization of a prime quotient of positive Hilbert dimension. The
resulting polynomial map is injective and integral, and so is the induced map of projective
closures fixing the homogenizing coordinate. -/
theorem exists_bounded_integer_closure_normalization (m k : ℕ)
    (I : Ideal (MvPolynomial (Fin (m + 1 + k)) ℚ)) [I.IsPrime] (d : ℕ)
    (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ a : Fin (m + 1) → Fin (m + 1 + k) → ℤ,
      (∀ i j, |a i j| ≤ integerNormalizationHeight (m + 1 + k) d) ∧
      (projectionCoordinateMap I (fun i => integerLinearForm (a i))).IsIntegral ∧
      Function.Injective (projectionCoordinateMap I (fun i => integerLinearForm (a i))) ∧
      (projectionCoordinateMap (projectiveClosureIdeal I)
        (closureProjectionCoordinates (fun i => integerLinearForm (a i)))).IsIntegral := by
  induction k generalizing d with
  | zero =>
    let a : Fin (m + 1) → Fin (m + 1) → ℤ := fun i j => if j = i then 1 else 0
    have heq : projectionCoordinateMap I (fun i => integerLinearForm (a i)) =
        Ideal.Quotient.mkₐ ℚ I := by
      ext i
      simp [projectionCoordinateMap, a, integerLinearForm_identity]
    have hI0 : I = ⊥ := ideal_eq_bot_of_full_hilbert_dimension I (Ideal.IsPrime.ne_top ‹I.IsPrime›)
      (by simpa only [Fintype.card_fin] using hdimdeg.natDegree_eq)
    refine ⟨a, ?_, ?_, ?_, ?_⟩
    · intro i j
      have hH : (1 : ℤ) ≤ integerNormalizationHeight (m + 1) d := by
        exact_mod_cast Nat.succ_le_of_lt (integerNormalizationHeight_pos (m + 1) d)
      by_cases he : j = i
      · simpa [a, he] using hH
      · simp only [a, ite_eq_right he, abs_zero]
        exact Nat.cast_nonneg _
    · rw [heq]
      exact RingHom.isIntegral_of_surjective _ (Ideal.Quotient.mkₐ_surjective ℚ I)
    · rw [heq]
      apply (RingHom.injective_iff_ker_eq_bot _).mpr
      change RingHom.ker ((Ideal.Quotient.mkₐ ℚ I) :
        MvPolynomial (Fin (m + 1)) ℚ →+* MvPolynomial (Fin (m + 1)) ℚ ⧸ I) = ⊥
      rwa [Ideal.Quotient.mkₐ_ker]
    · have heqcone : projectionCoordinateMap (projectiveClosureIdeal I)
          (closureProjectionCoordinates (fun i => integerLinearForm (a i))) =
            Ideal.Quotient.mkₐ ℚ (projectiveClosureIdeal I) := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;>
          simp [projectionCoordinateMap, closureProjectionCoordinates, a,
            integerLinearForm_identity]
      rw [heqcone]
      exact RingHom.isIntegral_of_surjective _ (Ideal.Quotient.mkₐ_surjective _ _)
  | succ k ih =>
    obtain ⟨c, e, hc, he, hed, hintc, hprime, hdimdegJ, hconec⟩ :=
      exists_fin_integer_closure_elimination_step (n := m + 1 + k) (m := m) I d hdimdeg
        (by omega)
    let ψ := projectionCoordinateMap I (fun i => integerLinearForm (c i))
    let J := RingHom.ker ψ
    have : J.IsPrime := hprime
    obtain ⟨a, ha, hinta, hinja, hconea⟩ := ih J e hdimdegJ
    let a' : Fin (m + 1) → Fin (m + 1 + (k + 1)) → ℤ :=
      fun i j => ∑ t, a i t * c t j
    let ψa := projectionCoordinateMap J (fun i => integerLinearForm (a i))
    let φ := Ideal.kerLiftAlg ψ
    have hφ : φ.IsIntegral := hintc.kerLift
    have hcomp := RingHom.IsIntegral.trans ψa.toRingHom φ.toRingHom hinta hφ
    have heq : φ.comp ψa = projectionCoordinateMap I (fun i => integerLinearForm (a' i)) := by
      ext i
      simp only [AlgHom.comp_apply, ψa, projectionCoordinateMap, aeval_X,
        Ideal.Quotient.mkₐ_eq_mk]
      change (Ideal.Quotient.mk I)
        (aeval (fun t => integerLinearForm (c t)) (integerLinearForm (a i))) =
          (Ideal.Quotient.mk I) (integerLinearForm (a' i))
      rw [integerLinearForm_comp]
      rfl
    refine ⟨a', ?_, ?_, ?_, ?_⟩
    · intro i j
      have hbound := integerLinearForm_matrix_height (a i) c
        (integerNormalizationHeight (m + 1 + k) e) (d + 1) (ha i)
        (fun i j => by exact_mod_cast hc i j) j
      simp only [Fintype.card_fin] at hbound
      apply hbound.trans
      have hmono := integerNormalizationHeight_mono (m + 1 + k) hed
      have hstep := integerNormalizationHeight_step (m + 1 + k) d
      exact_mod_cast (Nat.mul_le_mul_right (d + 1)
        (Nat.mul_le_mul_left (m + 1 + k) hmono)).trans hstep
    · change (φ.comp ψa).IsIntegral at hcomp
      rwa [heq] at hcomp
    · rw [← heq]
      exact (Ideal.kerLiftAlg_injective ψ).comp hinja
    · have hcone := closure_projection_integral_comp I
        (fun i => integerLinearForm (c i))
        (fun i => linearForm_isHomogeneous _)
        (fun i => integerLinearForm (a i)) hconec hconea
      simpa only [integerLinearForm_comp] using hcone

/-- Integer linear normalization of a prime quotient of positive
Hilbert dimension. The resulting polynomial map is both injective and integral. -/
theorem exists_bounded_integer_normalization (m k : ℕ)
    (I : Ideal (MvPolynomial (Fin (m + 1 + k)) ℚ)) [I.IsPrime] (d : ℕ)
    (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ a : Fin (m + 1) → Fin (m + 1 + k) → ℤ,
      (∀ i j, |a i j| ≤ integerNormalizationHeight (m + 1 + k) d) ∧
      (projectionCoordinateMap I (fun i => integerLinearForm (a i))).IsIntegral ∧
      Function.Injective (projectionCoordinateMap I (fun i => integerLinearForm (a i))) := by
  obtain ⟨a, ha, hint, hinj, -⟩ := exists_bounded_integer_closure_normalization m k I d hdimdeg
  exact ⟨a, ha, hint, hinj⟩

end
end CCDN
