/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.VectorFunctionalNormal
public import LeanPool.VacuumBellSeparation.Bell.VectorStateApproximation
public import LeanPool.VacuumBellSeparation.Bell.GenericBellCorrelationDefs
public import LeanPool.VacuumBellSeparation.Bell.StateExtension
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

/-!
# Domination of actual commutant-orbit vector states

The reference functional and its competitors are evaluated on the same concrete
von Neumann algebra. The estimate holds on every positive element, with the
actual operator norm of the commutant operator. No representation of arbitrary
normal states by vectors is presumed.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite.SW88

open scoped InnerProductSpace ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance commutant_vector_vna_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_vonNeumannAlgebra M

/-- The actual vector functional, bundled with its full dual norm. -/
def vectorDual (M : VonNeumannAlgebra H) (x : H) : StrongDual ℂ M.toStarSubalgebra :=
  (PositiveContinuousLinearMap.ofClass (vectorPositiveLinearMap M x)).toContinuousLinearMap

@[simp] theorem vectorDual_apply (M : VonNeumannAlgebra H) (x : H)
    (T : M.toStarSubalgebra) : vectorDual M x T = vectorFunctional M x T := rfl

theorem vectorDual_isNormalState (M : VonNeumannAlgebra H) (x : H) (hx : ‖x‖ = 1) :
    IsNormalStateFunctional M (vectorDual M x) :=
  vectorFunctional_isNormalState M x hx

/-- The topology in this estimate is the norm on the whole continuous dual. -/
theorem vectorDual_difference_norm_le (M : VonNeumannAlgebra H) (x y : H) :
    ‖vectorDual M x - vectorDual M y‖ ≤ (‖x‖ + ‖y‖) * ‖x - y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro T
  exact vectorState_uniform_difference_bound x y (T : H →L[ℂ] H)

/-- Square-root factorization occurs inside M; the commutant therefore commutes
with the actual factor, without assuming a polynomial approximation theorem. -/
theorem vectorDual_commutant_le (M : VonNeumannAlgebra H) (Ω : H)
    {S : H →L[ℂ] H} (hS : S ∈ M.commutant)
    (T : M.toStarSubalgebra) (hT : 0 ≤ T) :
    vectorDual M (S Ω) T ≤ ‖S‖ ^ 2 • vectorDual M Ω T := by
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hT
  have he (x : H) : vectorDual M x T = ((‖(R : H →L[ℂ] H) x‖ ^ 2 : ℝ) : ℂ) := by
    rw [vectorDual_apply, hR]
    change inner ℂ x ((star (R : H →L[ℂ] H)) ((R : H →L[ℂ] H) x)) = _
    simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow]
  have hc : (R : H →L[ℂ] H) (S Ω) = S ((R : H →L[ℂ] H) Ω) := by
    simpa only [mul_apply_eq_comp] using congrArg
      (fun A : H →L[ℂ] H => A Ω)
      ((VonNeumannAlgebra.mem_commutant_iff.mp hS) (R : H →L[ℂ] H) R.2)
  rw [he (S Ω), he Ω, hc, Complex.real_smul, ← Complex.ofReal_mul]
  apply Complex.real_le_real.mpr
  have hn := S.le_opNorm ((R : H →L[ℂ] H) Ω)
  have hs := mul_le_mul hn hn (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  simpa only [pow_two, mul_assoc, mul_left_comm, mul_comm] using hs

/-- A positive coefficient strictly below one is chosen from the actual norm.
The reference vector need not be normalized for this domination inequality. -/
theorem exists_small_vector_domination (M : VonNeumannAlgebra H) (Ω : H)
    {S : H →L[ℂ] H} (hS : S ∈ M.commutant) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ T : M.toStarSubalgebra,
      0 ≤ T → t • vectorDual M (S Ω) T ≤ vectorDual M Ω T := by
  let C : ℝ := ‖S‖ ^ 2
  let t : ℝ := (C + 2)⁻¹
  have hC : 0 ≤ C := sq_nonneg _
  have hd : 0 < C + 2 := by linarith
  have ht : 0 < t := inv_pos.mpr hd
  have he : t * (C + 2) = 1 := inv_mul_cancel₀ hd.ne'
  have htC0 : 0 ≤ t * C := mul_nonneg ht.le hC
  have ht1 : t < 1 := by nlinarith
  have htC : t * C ≤ 1 := by nlinarith
  refine ⟨t, ht, ht1, ?_⟩
  intro T hT
  have hz : 0 ≤ vectorDual M Ω T := (vectorPositiveLinearMap M Ω).map_nonneg hT
  have hfirst := smul_le_smul_of_nonneg_left (vectorDual_commutant_le M Ω hS T hT) ht.le
  have hlast : (t * C) • vectorDual M Ω T ≤ vectorDual M Ω T := by
    simpa only [one_smul] using smul_le_smul_of_nonneg_right htC hz
  have hfirst' : t • vectorDual M (S Ω) T ≤ (t * C) • vectorDual M Ω T := by
    simpa only [smul_smul] using hfirst
  exact hfirst'.trans hlast

/-- A unit vector gives a member of the actual all-directed normal-state space. -/
def vectorNormalState (M : VonNeumannAlgebra H) (x : H) (hx : ‖x‖ = 1) :
    HC00.NormalStateSpace M := ⟨vectorDual M x, vectorDual_isNormalState M x hx⟩

end VacuumBellSeparation.Bipartite.SW88
