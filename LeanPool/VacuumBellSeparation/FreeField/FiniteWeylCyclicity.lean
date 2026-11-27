/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.FiniteCanonicalCoordinates
public import LeanPool.VacuumBellSeparation.Bell.ProjectiveCyclicEquivalence
public import LeanPool.VacuumBellSeparation.Gaussian.QuadratureMatrices

/-!
# The actual finite-source cyclic subspace is reducing

All operators remain the original physical time-zero Weyl operators. Zero
and adjoint identities are derived from their true unitary Weyl relations.
The closed vacuum orbit and its reduction property are constructed directly.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation

open Gaussian ContinuousLinearMap
open scoped Matrix InnerProductSpace

variable {m : ℝ} (hm : 0 < m) (S : Submodule ℝ TimeZeroSource)
  [FiniteDimensional ℝ S] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι ℝ (FiniteSourceSpace hm S))
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (V : FreeFieldVacuum m H)

omit [DecidableEq ι] in
theorem finitePhysicalWeyl_zero : finitePhysicalWeyl hm S b V 0 = 1 := by
  have he := finitePhysicalWeyl_mul hm S b V 0 0
  simp only [Matrix.mulVec_zero, dotProduct_zero, zero_div, Complex.ofReal_zero,
    mul_zero, neg_zero, Complex.exp_zero, one_smul, zero_add] at he
  have hu := Unitary.star_mul_self_of_mem (finitePhysicalWeyl_mem_unitary hm S b V 0)
  calc
    finitePhysicalWeyl hm S b V 0 =
        (star (finitePhysicalWeyl hm S b V 0) * finitePhysicalWeyl hm S b V 0) *
          finitePhysicalWeyl hm S b V 0 := by rw [hu, one_mul]
    _ = star (finitePhysicalWeyl hm S b V 0) *
        (finitePhysicalWeyl hm S b V 0 * finitePhysicalWeyl hm S b V 0) := mul_assoc _ _ _
    _ = 1 := by rw [he, hu]

/-- Finite physical cyclic space defined as `closedCyclicSpan (fun x => finitePhysicalWeyl hm S b V
x V.vacuum)`. -/
def finitePhysicalCyclicSpace : Submodule ℂ H :=
  closedCyclicSpan (fun x => finitePhysicalWeyl hm S b V x V.vacuum)

/-- Finite physical cyclic vacuum. -/
noncomputable def finitePhysicalCyclicVacuum : finitePhysicalCyclicSpace hm S b V :=
  ⟨V.vacuum, by
    have h := mem_closedCyclicSpan (fun x => finitePhysicalWeyl hm S b V x V.vacuum) 0
    simpa only [finitePhysicalCyclicSpace, finitePhysicalWeyl_zero, one_apply_eq_self] using h⟩

omit [DecidableEq ι] in
theorem finitePhysicalCyclicVacuum_norm : ‖finitePhysicalCyclicVacuum hm S b V‖ = 1 :=
  V.vacuum_norm

variable {n : ℕ} (c : Module.Basis (Fin n × Fin 2) ℝ (FiniteSourceSpace hm S))

theorem finitePhysicalWeyl_star_of_canonical
    (hσ : finiteSourceSymplecticMatrix hm S c = modeSymplecticForm)
    (x : Fin n × Fin 2 → ℝ) :
    star (finitePhysicalWeyl hm S c V x) = finitePhysicalWeyl hm S c V (-x) := by
  have hform : x ⬝ᵥ (modeSymplecticForm *ᵥ (-x)) = 0 := by
    rw [dotProduct_modeSymplecticForm]
    apply Finset.sum_eq_zero
    intro j hj
    simp only [quadratureSymplectic, modeQuadratureTuple, Pi.neg_apply]
    ring
  have he := finitePhysicalWeyl_mul hm S c V x (-x)
  rw [hσ, hform, zero_div, Complex.ofReal_zero, mul_zero, neg_zero,
    Complex.exp_zero, one_smul, add_neg_cancel, finitePhysicalWeyl_zero] at he
  have hu := Unitary.star_mul_self_of_mem (finitePhysicalWeyl_mem_unitary hm S c V x)
  calc
    star (finitePhysicalWeyl hm S c V x) = star (finitePhysicalWeyl hm S c V x) * 1 :=
      (mul_one _).symm
    _ = star (finitePhysicalWeyl hm S c V x) *
        (finitePhysicalWeyl hm S c V x * finitePhysicalWeyl hm S c V (-x)) := by rw [he]
    _ = (star (finitePhysicalWeyl hm S c V x) * finitePhysicalWeyl hm S c V x) *
        finitePhysicalWeyl hm S c V (-x) := (mul_assoc _ _ _).symm
    _ = finitePhysicalWeyl hm S c V (-x) := by rw [hu, one_mul]

theorem finitePhysicalCyclicSpace_reducing
    (hσ : finiteSourceSymplecticMatrix hm S c = modeSymplecticForm)
    (A : H →L[ℂ] H) (hA : A ∈ Set.range (finitePhysicalWeyl hm S c V)) :
    (∀ x ∈ finitePhysicalCyclicSpace hm S c V, A x ∈ finitePhysicalCyclicSpace hm S c V) ∧
    (∀ x ∈ finitePhysicalCyclicSpace hm S c V, star A x ∈ finitePhysicalCyclicSpace hm S c V) :=
  projective_closedOrbit_reducing _ _ (finitePhysicalWeyl_mul hm S c V)
    (finitePhysicalWeyl_star_of_canonical hm S V c hσ) V.vacuum A hA

/-- Every actual finite-algebra observable preserves the original cyclic subspace. -/
theorem canonicalSourceAlgebra_invariant_cyclic
    (hσ : finiteSourceSymplecticMatrix hm S c = modeSymplecticForm)
    {A : H →L[ℂ] H} (hA : A ∈ canonicalSourceAlgebra V hm S)
    {x : H} (hx : x ∈ finitePhysicalCyclicSpace hm S c V) :
    A x ∈ finitePhysicalCyclicSpace hm S c V := by
  let : CompleteSpace (finitePhysicalCyclicSpace hm S c V) := by
    unfold finitePhysicalCyclicSpace closedCyclicSpan
    infer_instance
  rw [← generatedVNA_finitePhysicalWeyl hm S c V] at hA
  exact generatedVNA_invariant_of_reducing _ _
    (finitePhysicalCyclicSpace_reducing hm S V c hσ) hA hx

end VacuumBellSeparation
