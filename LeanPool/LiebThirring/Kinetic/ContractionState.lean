/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.CurryingState
public import LeanPool.LiebThirring.Kinetic.ContractionTensor

/-!
# One-particle insertion, contraction and projection on `State`

Insert a fixed one-particle vector into coordinate `i`.

Contract coordinate `i` against the full spatial-and-spin one-particle vector.
-/

public section

open MeasureTheory
open scoped InnerProduct

namespace LiebThirring

private theorem adjoint_transport {E F H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (C : E ≃ₗᵢ[ℂ] F) (I : H →L[ℂ] F) :
    ((C.symm : F →L[ℂ] E).comp I).adjoint = I.adjoint.comp (C : E →L[ℂ] F) := by
  simp only [ContinuousLinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm,
    LinearIsometryEquiv.symm_symm]

/-- Insert a fixed one-particle vector into coordinate `i`. -/
@[expose] noncomputable def oneParticleInsertion {N q : ℕ} (i : Fin N)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position)) :
    RestState i q →L[ℂ] State N q :=
  (oneParticleCurryingLinearIsometryEquiv i).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (tensorInsertion (H := RestState i q) f)

/-- Contract coordinate `i` against the full spatial-and-spin one-particle vector. -/
@[expose] noncomputable def oneParticleContraction {N q : ℕ} (i : Fin N)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position)) :
    State N q →L[ℂ] RestState i q :=
  (tensorContraction (H := RestState i q) f).comp
    (oneParticleCurryingLinearIsometryEquiv i).toContinuousLinearEquiv.toContinuousLinearMap

/-- The concrete contraction is conjugate-linear in its one-particle vector. -/
theorem oneParticleContraction_smul {N q : ℕ} (i : Fin N)
    (a : ℂ) (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position)) :
    oneParticleContraction i (a • f) = star a • oneParticleContraction i f := by
  rw [oneParticleContraction, tensorContraction_smul, ContinuousLinearMap.smul_comp]
  rfl

/-- The concrete contraction is the adjoint of the concrete insertion. -/
theorem oneParticleInsertion_adjoint {N q : ℕ} (i : Fin N)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position)) :
    (oneParticleInsertion i f).adjoint = oneParticleContraction i f := by
  exact adjoint_transport (oneParticleCurryingLinearIsometryEquiv (q := q) i)
    (tensorInsertion (H := RestState i q) f)

/-- Exact norm of insertion on the state carrier. -/
theorem oneParticleInsertion_norm {N q : ℕ} (i : Fin N)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position)) (v : RestState i q) :
    ‖oneParticleInsertion i f v‖ = ‖f‖ * ‖v‖ := by
  change ‖(oneParticleCurryingLinearIsometryEquiv i).symm (tensorInsertion (H := RestState i q) f
    v)‖ = _
  rw [LinearIsometryEquiv.norm_map, tensorInsertion_norm]

/-- contraction contraction bound, with no antisymmetry or normalization assumption. -/
theorem oneParticleContraction_norm_le {N q : ℕ} (i : Fin N)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position)) (ψ : State N q) :
    ‖oneParticleContraction i f ψ‖ ≤ ‖f‖ * ‖ψ‖ := by
  change ‖tensorContraction (H := RestState i q) f (oneParticleCurryingLinearIsometryEquiv i ψ)‖ ≤ _
  calc
    _ ≤ ‖f‖ * ‖oneParticleCurryingLinearIsometryEquiv i ψ‖ :=
      tensorContraction_norm_le (H := RestState i q) f _
    _ = _ := by rw [LinearIsometryEquiv.norm_map]

/-- The zero one-particle vector contracts every state to zero. -/
theorem oneParticleContraction_zero {N q : ℕ} (i : Fin N) (ψ : State N q) :
    oneParticleContraction i 0 ψ = 0 := by
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa using oneParticleContraction_norm_le i 0 ψ) (norm_nonneg _)

/-- Currying the inserted state recovers the literal Hilbert-valued tensor. -/
theorem oneParticleCurrying_insertion {N q : ℕ} (i : Fin N)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position)) (v : RestState i q) :
    oneParticleCurrying i (oneParticleInsertion i f v) = tensorInsertion (H := RestState i q) f v
      := by
  change oneParticleCurryingLinearIsometryEquiv i
    ((oneParticleCurryingLinearIsometryEquiv i).symm (tensorInsertion (H := RestState i q) f v)) = _
  exact (oneParticleCurryingLinearIsometryEquiv i).apply_symm_apply _

/-- The inserted state has the prescribed product amplitudes on a.e. slices. -/
theorem oneParticleInsertion_ae {N q : ℕ} (i : Fin N)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position)) (v : RestState i q) :
    ∀ᵐ x : Position, ∀ s : Fin q, ∀ᵐ y : OtherConfiguration i,
      ∀ t : OtherSpinLabels i q,
        oneParticleInsertion i f v (insertParticle i x y) (insertSpin i s t) =
          f x s * v y t := by
  have hc := oneParticleCurrying_ae i (oneParticleInsertion i f v)
  rw [oneParticleCurrying_insertion] at hc
  filter_upwards [hc, tensorInsertion_apply_ae (H := RestState i q) f v] with x hx ht
  intro s
  have heq := hx s
  rw [ht s] at heq
  filter_upwards [heq, Lp.coeFn_smul (f x s) v] with y hy hs
  simp only [Pi.smul_apply] at hs
  intro t
  rw [← hy t, hs]
  rfl

/-- The rank-one lift obtained by inserting back after contraction.
It is an orthogonal projection when the inserted one-particle vector is unit. -/
@[expose] noncomputable def oneParticleProjection {N q : ℕ} (i : Fin N)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position)) :
    State N q →L[ℂ] State N q :=
  (oneParticleInsertion i f).comp (oneParticleContraction i f)

/-- Every lifted rank-one operator is self-adjoint. -/
theorem oneParticleProjection_adjoint {N q : ℕ} (i : Fin N)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position)) :
    (oneParticleProjection i f).adjoint = oneParticleProjection i f := by
  rw [oneParticleProjection, ← oneParticleInsertion_adjoint,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

/-- The symmetry identity needed by the finite projection sum estimate. -/
theorem oneParticleProjection_inner {N q : ℕ} (i : Fin N)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position)) (ψ φ : State N q) :
    inner ℂ (oneParticleProjection i f ψ) φ = inner ℂ ψ (oneParticleProjection i f φ) := by
  calc
    _ = inner ℂ ((oneParticleProjection i f).adjoint ψ) φ := by
      rw [oneParticleProjection_adjoint]
    _ = _ := ContinuousLinearMap.adjoint_inner_left (oneParticleProjection i f) φ ψ

/-- Contraction undoes insertion of a unit one-particle vector. -/
theorem oneParticleContraction_insertion {N q : ℕ} (i : Fin N)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position)) (hf : ‖f‖ = 1)
    (v : RestState i q) : oneParticleContraction i f (oneParticleInsertion i f v) = v := by
  have h : (oneParticleInsertion i f).adjoint.comp (oneParticleInsertion i f) = 1 :=
    (oneParticleInsertion i f).norm_map_iff_adjoint_comp_self.mp (fun w => by
      rw [oneParticleInsertion_norm, hf, one_mul])
  rw [oneParticleInsertion_adjoint] at h
  exact congrArg (fun T : RestState i q →L[ℂ] RestState i q => T v) h

/-- Inserting a unit vector after contraction is idempotent. -/
theorem oneParticleProjection_idempotent {N q : ℕ} (i : Fin N)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position)) (hf : ‖f‖ = 1)
    (ψ : State N q) : oneParticleProjection i f (oneParticleProjection i f ψ) =
      oneParticleProjection i f ψ := by
  change oneParticleInsertion i f
    (oneParticleContraction i f (oneParticleInsertion i f (oneParticleContraction i f ψ))) = _
  rw [oneParticleContraction_insertion i f hf]
  rfl

/-- Unit-vector projection and contraction have equal output norms. -/
theorem oneParticleProjection_norm {N q : ℕ} (i : Fin N)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position)) (hf : ‖f‖ = 1)
    (ψ : State N q) : ‖oneParticleProjection i f ψ‖ = ‖oneParticleContraction i f ψ‖ := by
  change ‖oneParticleInsertion i f (oneParticleContraction i f ψ)‖ = _
  rw [oneParticleInsertion_norm, hf, one_mul]

end LiebThirring

end
