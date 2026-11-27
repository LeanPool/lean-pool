/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Fock.StandardTensorTotality
public import LeanPool.VacuumBellSeparation.Fock.RealExponentialCoefficients
public import LeanPool.VacuumBellSeparation.Fock.WeylFockEquivalence

/-!
# Coherent totality from a real linear family

The closure of the actual real range need only contain a standard subspace.
Real rescaling extracts every tensor coefficient; continuity of each finite
multilinear form then extends its vanishing to the standard subspace. No
continuity of the label space or complex linearity of the label map is assumed.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Fock
open scoped InnerProductSpace

-- Named local caches of the existing restricted-submodule and completion instances.
/-- The real scalar action on a symmetric tensor sector, restricted from complex scalars. -/
local instance realLinearCoherentTotalitySymmetricTensorRealModule (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (n : ℕ) :
    Module ℝ (SymmetricTensorPower E n) :=
  Module.complexToReal (SymmetricTensorPower E n)

/-- Completeness of the symmetric tensor sector as a closed subspace. -/
local instance realLinearCoherentTotalitySymmetricTensorComplete (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (n : ℕ) :
    CompleteSpace (SymmetricTensorPower E n) :=
  (isClosed_symmetricTensorSubmodule E n).isComplete.completeSpace_coe

/-- Completeness of the Hilbert sum of the degrees of the Fock space. -/
local instance realLinearCoherentTotalitySymmetricFockComplete (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] : CompleteSpace (SymmetricFockSpace E) :=
  lp.completeSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

omit [CompleteSpace H] in
theorem fock_eq_zero_of_realLinear_exponential_orthogonal
    (L : E →ₗ[ℝ] H) (S : StandardSubspace H)
    (hS : ∀ v : S.toClosedSubmodule, (v : H) ∈ closure (Set.range L))
    (x : SymmetricFockSpace H)
    (hx : ∀ u : E, inner ℂ x (exponentialVector H (L u)) = 0) : x = 0 := by
  have hc (u : E) (n : ℕ) :
      inner ℂ (x n) (pureSymmetricTensor H n (L u)) = 0 := by
    apply inner_pureTensor_zero_of_real_exponential_zero H x (L u)
    intro t
    rw [← L.map_smul]
    exact hx (t • u)
  apply lp.ext
  funext n
  apply symmetricTensor_eq_zero_of_standard_diagonal S n
  intro v
  let M := symmetricTensorScalarForm H n (x n)
  have hcont : Continuous (fun y : H => M (fun _ => y)) :=
    M.cont.comp (continuous_pi fun _ => continuous_id)
  have hz : closure (Set.range L) ⊆ {y : H | M (fun _ => y) = 0} := by
    apply closure_minimal ?_ (isClosed_eq hcont continuous_const)
    rintro _ ⟨u, rfl⟩
    exact hc u n
  exact hz (hS v)

omit [CompleteSpace H] in
theorem fock_eq_zero_of_realLinear_coherent_orthogonal
    (L : E →ₗ[ℝ] H) (S : StandardSubspace H)
    (hS : ∀ v : S.toClosedSubmodule, (v : H) ∈ closure (Set.range L))
    (x : SymmetricFockSpace H)
    (hx : ∀ u : E, inner ℂ x (coherentVector H (L u)) = 0) : x = 0 := by
  apply fock_eq_zero_of_realLinear_exponential_orthogonal L S hS x
  intro u
  have h := hx u
  rw [coherentVector, inner_smul_right] at h
  exact (mul_eq_zero.mp h).resolve_left (Complex.exp_ne_zero _)

omit [CompleteSpace H] in
theorem realLinear_coherentVector_dense_span
    (L : E →ₗ[ℝ] H) (S : StandardSubspace H)
    (hS : ∀ v : S.toClosedSubmodule, (v : H) ∈ closure (Set.range L)) :
    (Submodule.span ℂ (Set.range fun u : E =>
      coherentVector H (L u))).topologicalClosure = ⊤ := by
  let K := Submodule.span ℂ (Set.range fun u : E => coherentVector H (L u))
  have horth : Kᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    apply fock_eq_zero_of_realLinear_coherent_orthogonal L S hS x
    intro u
    exact K.inner_left_of_mem_orthogonal (Submodule.subset_span ⟨u, rfl⟩) hx
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure, horth]

end VacuumBellSeparation.Fock
