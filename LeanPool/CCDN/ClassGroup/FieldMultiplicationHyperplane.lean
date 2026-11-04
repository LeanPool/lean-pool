/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs

/-! The algebraic nondegeneracy input for the uniform shape estimate of
a number-field lattice. Multiplication preserving a rational hyperplane
must be multiplication by a scalar. The proof uses linear functionals and
works over an arbitrary field extension. -/

@[expose] public section
namespace CCDN
noncomputable section

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

private theorem scalar_of_preserves_hyperplane (ℓ : K →ₗ[F] F) (hℓ : ℓ ≠ 0)
    (a : K) (ha : ∀ b : K, ℓ b = 0 → ℓ (a * b) = 0) :
    ∃ c : F, a = algebraMap F K c := by
  obtain ⟨z, hz⟩ : ∃ z : K, ℓ z ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓ (LinearMap.ext h)
  let u : K := (ℓ z)⁻¹ • z
  have hu : ℓ u = 1 := by simp [u, hz]
  let c : F := ℓ (a * u)
  have hp (t : K) : ℓ (a * t) = c * ℓ t := by
    have ht : ℓ (t - ℓ t • u) = 0 := by simp [hu]
    have h := ha (t - ℓ t • u) ht
    rw [mul_sub, mul_smul_comm, map_sub, map_smul] at h
    change ℓ (a * t) - ℓ t * c = 0 at h
    exact (sub_eq_zero.mp h).trans (mul_comm _ _)
  refine ⟨c, ?_⟩
  by_contra h
  have hzero (t : K) : ℓ ((a - algebraMap F K c) * t) = 0 := by
    rw [sub_mul, ← Algebra.smul_def, map_sub, map_smul, hp]
    simp
  have hh := hzero ((a - algebraMap F K c)⁻¹ * u)
  rw [mul_inv_cancel_left₀ (sub_ne_zero.mpr h), hu] at hh
  exact one_ne_zero hh

private theorem exists_kernel_multiplication_witness
    (ℓ : K →ₗ[F] F) (hℓ : ℓ ≠ 0)
    (a : K) (ha : a ∉ Set.range (algebraMap F K)) :
    ∃ b : K, ℓ b = 0 ∧ ℓ (a * b) ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨c, hc⟩ := scalar_of_preserves_hyperplane ℓ hℓ a h
  exact ha ⟨c, hc.symm⟩

/-- On the complement to the scalars inside a hyperplane containing one,
the multiplication pairing detected by the hyperplane functional is
nondegenerate. The second functional specifies that complement explicitly. -/
theorem multiplication_pairing_on_hyperplane_complement
    (ℓ μ : K →ₗ[F] F) (hℓ : ℓ ≠ 0) (hℓ1 : ℓ 1 = 0) (hμ1 : μ 1 = 1)
    (a : K) (ha0 : a ≠ 0) (hℓa : ℓ a = 0) (hμa : μ a = 0) :
    ∃ b : K, ℓ b = 0 ∧ μ b = 0 ∧ ℓ (a * b) ≠ 0 := by
  have ha : a ∉ Set.range (algebraMap F K) := by
    rintro ⟨c, hc⟩
    have h : c = 0 := by
      rw [← hc, Algebra.algebraMap_eq_smul_one, map_smul, hμ1, smul_eq_mul,
        mul_one] at hμa
      exact hμa
    exact ha0 (by rw [← hc, h, map_zero])
  obtain ⟨b, hb, hab⟩ := exists_kernel_multiplication_witness ℓ hℓ a ha
  refine ⟨b - μ b • (1 : K), ?_, ?_, ?_⟩
  · simp [hb, hℓ1]
  · simp [hμ1]
  · simpa only [mul_sub, mul_smul_comm, mul_one, map_sub, map_smul,
      hℓa, smul_zero, sub_zero] using hab

end
end CCDN
