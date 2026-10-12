/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.ContractionExchange
public import LeanPool.LiebThirring.Kinetic.PauliScaling
public import LeanPool.LiebThirring.Kinetic.PauliAbstract

/-!
# Conditional specialization of the projection argument to `State`

For unit one-particle vectors, the Pauli estimate follows from the two concrete lift relations
supplied as explicit hypotheses.

The complete occupation estimate conditional on the global contraction double-exchange identity.
Covariance, norm equality, and nonunit scaling are discharged by proved lemmas on the actual
`State` carrier.
-/

public section

open MeasureTheory

namespace LiebThirring

/-- For unit one-particle vectors, the Pauli estimate follows from the two
concrete lift relations supplied as explicit hypotheses. -/
theorem oneParticleContraction_pauli_unit_of_lift_relations {N q : ℕ}
    (i : Fin N) (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position))
    (hf : ‖f‖ = 1) (ψ : State N q) (hψ : antisymmetric ψ)
    (hdouble : ∀ k l : Fin N, k ≠ l → ∀ φ : State N q,
      oneParticleProjection k f (oneParticleProjection l f
        (simultaneousPermutation (Equiv.swap k l) φ)) =
      oneParticleProjection k f (oneParticleProjection l f φ))
    (hequal : ∀ j : Fin N, ‖oneParticleProjection j f ψ‖ =
      ‖oneParticleProjection i f ψ‖) :
    (N : ℝ) * ‖oneParticleContraction i f ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
  have hzero (k l : Fin N) (hkl : k ≠ l) :
      oneParticleProjection k f (oneParticleProjection l f ψ) = 0 := by
    have h := hdouble k l hkl ψ
    rw [simultaneousPermutation_swap_eq_neg ψ hψ k l hkl, map_neg, map_neg] at h
    have htwo : (2 : ℂ) • oneParticleProjection k f (oneParticleProjection l f ψ) = 0 := by
      rw [two_smul]
      calc
        _ = -oneParticleProjection k f (oneParticleProjection l f ψ) +
            oneParticleProjection k f (oneParticleProjection l f ψ) :=
          congrArg (fun v : State N q => v +
            oneParticleProjection k f (oneParticleProjection l f ψ)) h.symm
        _ = 0 := neg_add_cancel _
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  have h := card_mul_norm_sq_le_of_projection_relations
    (fun j : Fin N => oneParticleProjection j f) ψ
    (fun j x y => oneParticleProjection_inner j f x y)
    (fun j => oneParticleProjection_idempotent j f hf ψ) hzero i hequal
  simpa only [Fintype.card_fin, oneParticleProjection_norm i f hf ψ] using h

/-- The complete occupation estimate conditional on the global
contraction double-exchange identity. Covariance, norm equality, and nonunit scaling
are discharged by proved lemmas on the actual `State` carrier. -/
theorem oneParticleContraction_pauli_of_double_exchange {N q : ℕ}
    (i : Fin N) (ψ : State N q) (hψ : antisymmetric ψ)
    (hdouble : ∀ g : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position),
      ‖g‖ = 1 → ∀ k l : Fin N, k ≠ l → ∀ φ : State N q,
      oneParticleProjection k g (oneParticleProjection l g
        (simultaneousPermutation (Equiv.swap k l) φ)) =
      oneParticleProjection k g (oneParticleProjection l g φ))
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position)) :
    (N : ℝ) * ‖oneParticleContraction i f ψ‖ ^ 2 ≤ ‖f‖ ^ 2 * ‖ψ‖ ^ 2 := by
  apply oneParticleContraction_pauli_of_unit_bound i ψ _ f
  intro g hg
  exact oneParticleContraction_pauli_unit_of_lift_relations i g hg ψ hψ (hdouble g hg)
    (fun j => oneParticleProjection_norm_eq i j g hg ψ hψ)

end LiebThirring

end
