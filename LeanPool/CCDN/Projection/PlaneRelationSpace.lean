/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-! At the degree of the irreducible image equation, the plane relation
space is one-dimensional. This supplies the specialized-kernel condition
for first-order deformation of a degree-preserving projection. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A multiple `g` of a nonzero polynomial `f` with total degree at most that of `f` is a scalar
multiple of `f`. -/
lemma eq_scalar_mul_of_dvd_of_totalDegree_le {K σ : Type*} [Field K]
    (f g : MvPolynomial σ K) (hf : f ≠ 0) (hdiv : f ∣ g)
    (hdeg : g.totalDegree ≤ f.totalDegree) : ∃ c : K, g = c • f := by
  by_cases hg : g = 0
  · exact ⟨0, by simp [hg]⟩
  obtain ⟨q, hq⟩ := hdiv
  have hq0 : q ≠ 0 := by intro hz; apply hg; rw [hq, hz, mul_zero]
  have hd := totalDegree_mul_of_isDomain hf hq0
  rw [← hq] at hd
  have hqd : q.totalDegree = 0 := by omega
  have hqC := totalDegree_eq_zero_iff_eq_C.mp hqd
  refine ⟨q.coeff 0, ?_⟩
  rw [hq, hqC, Algebra.smul_def]
  simpa using (mul_comm f (C (q.coeff 0)))

/-- Every relation no larger than the image equation is its scalar multiple. -/
theorem plane_projection_relation_space {K τ : Type*} [Field K]
    (I : Ideal (MvPolynomial τ K)) (a : Fin 2 → MvPolynomial τ K)
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0)
    (hker : ∀ g, aeval a g ∈ I ↔ f ∣ g)
    (g : MvPolynomial (Fin 2) K) (hg : g.totalDegree ≤ f.totalDegree)
    (hzero : aeval a g ∈ I) : ∃ c : K, g = c • f :=
  eq_scalar_mul_of_dvd_of_totalDegree_le f g hf ((hker g).mp hzero) hg

end
end CCDN
