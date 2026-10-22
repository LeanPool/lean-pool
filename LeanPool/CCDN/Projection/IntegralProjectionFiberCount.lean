/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.IdealZeroLocus
public import LeanPool.CCDN.Hilbert.LinearProjectionFiltration

/-! Rational-point fibers of an integral polynomial projection.
Evaluation on the quotient constructs the specialization homomorphisms. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A rational point of the fiber over `z` gives a specialization of the quotient algebra over
the parameter ring, sending each coordinate function to the corresponding coordinate. -/
theorem exists_projection_fiber_specialization {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (l : τ → MvPolynomial σ K)
    [Algebra (MvPolynomial τ K) (MvPolynomial σ K ⧸ I)]
    (hmap : algebraMap (MvPolynomial τ K) (MvPolynomial σ K ⧸ I) =
      (projectionCoordinateMap I l).toRingHom)
    (z : τ → K) (x : σ → K) (hzero : x ∈ idealZeroLocus I)
    (hproj : ∀ i, eval x (l i) = z i) :
    letI : Algebra (MvPolynomial τ K) K := (aeval z).toRingHom.toAlgebra
    ∃ ψ : (MvPolynomial σ K ⧸ I) →ₐ[MvPolynomial τ K] K,
      ∀ i, ψ (Ideal.Quotient.mk I (X i)) = x i := by
  let : Algebra (MvPolynomial τ K) K := (aeval z).toRingHom.toAlgebra
  let R := MvPolynomial τ K
  let A := MvPolynomial σ K ⧸ I
  let φ : A →ₐ[K] K := Ideal.Quotient.liftₐ I (aeval x) (fun f hf => hzero f hf)
  have hφ (f : MvPolynomial σ K) :
      φ (Ideal.Quotient.mk I f) = eval x f := by
    exact congrArg (fun g : MvPolynomial σ K →ₐ[K] K => g f)
      (Ideal.Quotient.liftₐ_comp I (aeval x) (fun f hf => hzero f hf))
  have hcomp : φ.comp (projectionCoordinateMap I l) = aeval z := by
    ext i
    simpa only [projectionCoordinateMap, AlgHom.comp_apply, aeval_X,
      Ideal.Quotient.mkₐ_eq_mk] using (hφ (l i)).trans (hproj i)
  let ψ : A →ₐ[R] K :=
    { φ.toRingHom with
      commutes' := fun r => by
        change φ (algebraMap R A r) = (aeval z) r
        rw [hmap]
        exact congrArg (fun f : R →ₐ[K] K => f r) hcomp }
  refine ⟨ψ, ?_⟩
  intro i
  change φ (Ideal.Quotient.mk I (X i)) = x i
  simpa only [eval_X] using hφ (X i)

end
end CCDN
