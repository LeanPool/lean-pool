/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.BicommutantOrbit
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite diagonal amplification and operator blocks

The amplified Hilbert space is the genuine finite Hilbert direct sum of
the original space. Operators act diagonally; arbitrary amplified
operators have bounded operator-valued blocks. No finite-dimensionality
of the original Hilbert space is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- Finite amplification. -/
noncomputable def finiteAmplification (A : H →L[ℂ] H) :
    PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H) where
  toFun v := WithLp.toLp 2 (fun i => A (v i))
  map_add' v w := by ext i; simp
  map_smul' c v := by ext i; simp
  cont := (PiLp.continuous_toLp 2 (fun _ : ι => H)).comp (continuous_pi (fun i =>
    A.continuous.comp (PiLp.continuous_apply 2 (fun _ : ι => H) i)))

omit [CompleteSpace H] [DecidableEq ι] [Fintype ι] in
@[simp] theorem finiteAmplification_apply (A : H →L[ℂ] H)
    (v : PiLp 2 (fun _ : ι => H)) (i : ι) : finiteAmplification ι A v i = A (v i) := rfl

omit [DecidableEq ι] in
theorem finiteAmplification_star (A : H →L[ℂ] H) :
    finiteAmplification ι (star A) = star (finiteAmplification ι A) := by
  classical
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro v w
  simp only [PiLp.inner_apply, finiteAmplification_apply,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

/-- Amplification is a genuine unital complex star algebra homomorphism. -/
noncomputable def finiteAmplificationHom : (H →L[ℂ] H) →⋆ₐ[ℂ]
    (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)) where
  toFun := finiteAmplification ι
  map_zero' := by ext v i; simp
  map_one' := by ext v i; simp
  map_add' A B := by ext v i; simp
  map_mul' A B := by ext v i; rfl
  commutes' c := by ext v i; simp [Algebra.algebraMap_eq_smul_one]
  map_star' := finiteAmplification_star ι

/-- Continuous linear map for the amplification block, of type `H →L[ℂ] H`. -/
noncomputable def amplificationBlock
    (B : PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)) (i j : ι) : H →L[ℂ] H := by
  classical
  exact (ContinuousLinearMap.proj i).comp
    ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).toContinuousLinearMap.comp
      (B.comp ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.single ℂ (fun _ : ι => H) j))))

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem amplificationBlock_apply
    (B : PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)) (i j : ι) (x : H) :
    amplificationBlock ι B i j x = B (PiLp.single 2 j x) i := by
  classical
  rfl

omit [CompleteSpace H] [Fintype ι] in
theorem finiteAmplification_single (A : H →L[ℂ] H) (j : ι) (x : H) :
    finiteAmplification ι A (PiLp.single 2 j x) = PiLp.single 2 j (A x) := by
  classical
  ext i
  by_cases h : i = j
  · subst i; simp
  · simp only [finiteAmplification_apply, PiLp.single_eq_of_ne 2 h, map_zero]

omit [CompleteSpace H] in
theorem amplification_sum_single (v : PiLp 2 (fun _ : ι => H)) :
    ∑ j, PiLp.single 2 j (v j) = v := by
  classical
  ext i
  change (PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : ι => H) i) (∑ j, PiLp.single 2 j (v j)) = v i
  rw [map_sum]
  change (∑ j, (PiLp.single 2 j (v j)) i) = v i
  rw [Finset.sum_eq_single i]
  · exact PiLp.single_eq_same (β := fun _ : ι => H) 2 i (v i)
  · intro j hj hji
    exact PiLp.single_eq_of_ne (β := fun _ : ι => H) 2 hji.symm (v j)
  · simp

omit [CompleteSpace H] in
/-- The literal operator block decomposition. -/
theorem amplification_apply_eq_sum_blocks
    (B : PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H))
    (v : PiLp 2 (fun _ : ι => H)) (i : ι) :
    B v i = ∑ j, amplificationBlock ι B i j (v j) := by
  classical
  conv_lhs => rw [← amplification_sum_single ι v, map_sum]
  change (PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : ι => H) i) (∑ j, B (PiLp.single 2 j (v j))) = _
  rw [map_sum]
  rfl

omit [CompleteSpace H] [Fintype ι] in
/-- Commutation with the diagonal algebra is exactly blockwise commutation. -/
theorem finiteAmplification_commutes_iff [Finite ι] (A : H →L[ℂ] H)
    (B : PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)) :
    finiteAmplification ι A * B = B * finiteAmplification ι A ↔
      ∀ i j, A * amplificationBlock ι B i j = amplificationBlock ι B i j * A := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  constructor
  · intro h i j
    ext x
    have he := congrArg (fun C => C (PiLp.single 2 j x) i) h
    simpa only [mul_apply_eq_comp, finiteAmplification_apply,
      finiteAmplification_single, amplificationBlock_apply] using he
  · intro h
    ext v i
    change A (B v i) = B (finiteAmplification ι A v) i
    rw [amplification_apply_eq_sum_blocks, map_sum, amplification_apply_eq_sum_blocks]
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg (fun C : H →L[ℂ] H => C (v j)) (h i j)

end VacuumBellSeparation
