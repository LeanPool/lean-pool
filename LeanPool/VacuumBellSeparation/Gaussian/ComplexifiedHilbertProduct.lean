/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.HilbertProductOperator

/-!
# Complexification commutes with the actual Hilbert product

The unitary below explicitly rearranges four real coordinates. It relates
the product of the two regional complex Hilbert spaces to the complexified
real product used in the full-source covariance compression.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap HilbertComplexification

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Complexification product equivalence. -/
def complexificationProductEquiv :
    HilbertComplexification (WithLp 2 (E × F)) ≃ₗᵢ[ℂ]
      WithLp 2 (HilbertComplexification E × HilbertComplexification F) where
  toFun z := WithLp.toLp 2
    (mk z.re.fst z.im.fst, mk z.re.snd z.im.snd)
  invFun w := mk (WithLp.toLp 2 (w.fst.re, w.snd.re))
    (WithLp.toLp 2 (w.fst.im, w.snd.im))
  left_inv z := by
    apply HilbertComplexification.ext <;> apply WithLp.ofLp_injective 2 <;> rfl
  right_inv w := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> apply HilbertComplexification.ext <;> rfl
  map_add' z w := rfl
  map_smul' c z := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> apply HilbertComplexification.ext <;> rfl
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2, HilbertComplexification.norm_sq,
      HilbertComplexification.norm_sq, HilbertComplexification.norm_sq,
      WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    change (‖z.re.fst‖ ^ 2 + ‖z.im.fst‖ ^ 2) +
      (‖z.re.snd‖ ^ 2 + ‖z.im.snd‖ ^ 2) =
        (‖z.re.fst‖ ^ 2 + ‖z.re.snd‖ ^ 2) + (‖z.im.fst‖ ^ 2 + ‖z.im.snd‖ ^ 2)
    ring

@[simp] theorem complexificationProductEquiv_fst
    (z : HilbertComplexification (WithLp 2 (E × F))) :
    (complexificationProductEquiv z).fst = mk z.re.fst z.im.fst := rfl

@[simp] theorem complexificationProductEquiv_snd
    (z : HilbertComplexification (WithLp 2 (E × F))) :
    (complexificationProductEquiv z).snd = mk z.re.snd z.im.snd := rfl

section ComplexOperators

variable {G H : Type*}
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Continuous linear map for the complex Hilbert product operator, of type `WithLp 2 (G × H) →L[ℂ]
WithLp 2 (G × H)`. -/
def complexHilbertProductOperator (A : G →L[ℂ] G) (B : H →L[ℂ] H) :
    WithLp 2 (G × H) →L[ℂ] WithLp 2 (G × H) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ G H).symm.toContinuousLinearMap.comp
    ((A.prodMap B).comp (WithLp.prodContinuousLinearEquiv 2 ℂ G H).toContinuousLinearMap)

@[simp] theorem complexHilbertProductOperator_apply (A : G →L[ℂ] G) (B : H →L[ℂ] H)
    (z : WithLp 2 (G × H)) :
    complexHilbertProductOperator A B z = WithLp.toLp 2 (A z.fst, B z.snd) := rfl

theorem norm_complexHilbertProductOperator_le (A : G →L[ℂ] G) (B : H →L[ℂ] H)
    {c : ℝ} (hc : 0 ≤ c) (hA : ‖A‖ ≤ c) (hB : ‖B‖ ≤ c) :
    ‖complexHilbertProductOperator A B‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro z
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp
  rw [complexHilbertProductOperator_apply, WithLp.prod_norm_sq_eq_of_L2, mul_pow,
    WithLp.prod_norm_sq_eq_of_L2]
  change ‖A z.fst‖ ^ 2 + ‖B z.snd‖ ^ 2 ≤ c ^ 2 * (‖z.fst‖ ^ 2 + ‖z.snd‖ ^ 2)
  have ha := (A.le_opNorm z.fst).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hb := (B.le_opNorm z.snd).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  calc
    _ ≤ (c * ‖z.fst‖) ^ 2 + (c * ‖z.snd‖) ^ 2 := by gcongr
    _ = _ := by ring

end ComplexOperators

variable [CompleteSpace E] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
theorem complexificationProductEquiv_intertwines (A : E →L[ℝ] E) (B : F →L[ℝ] F)
    (z : HilbertComplexification (WithLp 2 (E × F))) :
    complexificationProductEquiv (complexify (realHilbertProductOperator A B) z) =
      complexHilbertProductOperator (complexify A) (complexify B)
        (complexificationProductEquiv z) := rfl

theorem complexificationProductEquiv_conjugate (A : E →L[ℝ] E) (B : F →L[ℝ] F) :
    (complexificationProductEquiv (E := E) (F := F)).conjStarAlgEquiv
      (complexify (realHilbertProductOperator A B)) =
        complexHilbertProductOperator (complexify A) (complexify B) := by
  ext z
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    complexificationProductEquiv_intertwines, LinearIsometryEquiv.apply_symm_apply]

end VacuumBellSeparation.Gaussian
