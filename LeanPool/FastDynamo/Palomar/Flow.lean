/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Palomar.Statement
public import LeanPool.FastDynamo.Dynamics.MainLagrangianClauses

/-!
# The velocity and the particle flow in the terms of the Challenge statement

The Challenge statement (`FastDynamo.Palomar.Statement`) works on `FastDynamoChallenge.T3 =
UnitAddTorus (Fin 3)` with values in `FastDynamoChallenge.R3 = EuclideanSpace ℝ (Fin 3)`.  These
are, by `abbrev`, the very types `Torus 3` and `R3` of the library, with the same instances, and
the quotient map `FastDynamoChallenge.toTorus` has the same body as `literalTorusPoint`.  So the
library's witness `mainLiteralVelocity` is a velocity in the Challenge's sense with no
identification.

* `exists_lipschitzWith_mainLiteralVelocity` — the velocity is Lipschitz.
* `isFlow_iff_isParticleFlow` — the Challenge's `IsFlow` (trajectories are images of integral
  curves, in mathlib's `IsIntegralCurve` sense, of the periodic lift `a ↦ u (a mod ℤ³)`) is the
  library's `IsParticleFlow`, for every velocity.
* `exists_isFlow_mainLiteralVelocity`, `isFlow_mainLiteralVelocity_eq` — the velocity has a
  flow, and every flow is `mainLiteralFlow`.
* `forall_isFlow_mainLiteralVelocity_continuous_coverEntropy` — every time map of every flow is
  continuous with `Dynamics.coverEntropy (Φ t) Set.univ = 0`.  The entropy is computed for the
  uniform structure of `UnitAddTorus (Fin 3)` (the product of the quotient uniformities), which
  is the uniform structure the library's `HasZeroTopologicalEntropy` is stated for on `Torus 3`.
-/

@[expose] public section

namespace FastDynamo

open FastDynamoChallenge

/-- The Challenge's quotient map `ℝ³ → 𝕋³` is the library's `literalTorusPoint`. -/
theorem toTorus_eq_literalTorusPoint : FastDynamoChallenge.toTorus = literalTorusPoint := rfl

/-- **The velocity of the theorem is Lipschitz**, in the Challenge's types. -/
theorem exists_lipschitzWith_mainLiteralVelocity :
    ∃ L, LipschitzWith L (mainLiteralVelocity : FastDynamoChallenge.T3 → FastDynamoChallenge.R3) :=
  ⟨_, lipschitzWith_mainLiteralVelocity⟩

/-- **The Challenge's flow predicate is the library's.**  `IsFlow u Φ` asks for integral curves
of the periodic lift `a ↦ u (toTorus a)` projecting to the trajectories; `IsParticleFlow u Φ` asks
for lifts `γ` of the trajectories with `γ' t = u (Φ t x)`.  Since `Φ t x = toTorus (γ t)`, the two
derivative conditions are the same. -/
theorem isFlow_iff_isParticleFlow (u : FastDynamoChallenge.T3 → FastDynamoChallenge.R3)
    (Φ : ℝ → FastDynamoChallenge.T3 → FastDynamoChallenge.T3) :
    FastDynamoChallenge.IsFlow u Φ ↔ IsParticleFlow u Φ := by
  constructor
  · intro h
    refine ⟨fun x ↦ (h x).1, fun x ↦ ?_⟩
    obtain ⟨γ, hγ, hΦ⟩ := (h x).2
    refine ⟨γ, hΦ, fun t ↦ ?_⟩
    rw [hΦ t]
    exact hγ t
  · intro h x
    refine ⟨h.initial x, ?_⟩
    obtain ⟨γ, hΦ, hγ⟩ := h.ode x
    refine ⟨γ, fun t ↦ ?_, hΦ⟩
    have := hγ t
    rw [hΦ t] at this
    exact this

/-- **The velocity of the theorem has a particle flow** in the Challenge's sense. -/
theorem exists_isFlow_mainLiteralVelocity :
    ∃ Φ, FastDynamoChallenge.IsFlow mainLiteralVelocity Φ := by
  obtain ⟨Φ, hΦ, -⟩ := existsUnique_isParticleFlow_mainLiteralVelocity
  exact ⟨Φ, (isFlow_iff_isParticleFlow _ _).2 hΦ⟩

/-- **Every flow of the velocity in the Challenge's sense is the library's flow**
`mainLiteralFlow`. -/
theorem isFlow_mainLiteralVelocity_eq {Φ : ℝ → FastDynamoChallenge.T3 → FastDynamoChallenge.T3}
    (hΦ : FastDynamoChallenge.IsFlow mainLiteralVelocity Φ) : Φ = mainLiteralFlow :=
  mainLiteralFlow_unique ((isFlow_iff_isParticleFlow _ _).1 hΦ)

/-- Every time map of `mainLiteralFlow` is continuous. -/
theorem continuous_mainLiteralFlow (t : ℝ) : Continuous (mainLiteralFlow t) :=
  ScaleFamily.TorusCellPlacement.continuous_literalFlow _ _ _ _ _ t

/-- **Zero entropy of the particle flow, in the Challenge's terms**: every time map of every flow
of the velocity is continuous and has `Dynamics.coverEntropy (Φ t) Set.univ = 0`. -/
theorem forall_isFlow_mainLiteralVelocity_continuous_coverEntropy :
    ∀ Φ, FastDynamoChallenge.IsFlow mainLiteralVelocity Φ → ∀ t,
      Continuous (Φ t) ∧ Dynamics.coverEntropy (Φ t) Set.univ = 0 := by
  intro Φ hΦ t
  rw [isFlow_mainLiteralVelocity_eq hΦ]
  exact ⟨continuous_mainLiteralFlow t, forall_hasZeroTopologicalEntropy_mainLiteralFlow t⟩

end FastDynamo
