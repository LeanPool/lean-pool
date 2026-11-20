/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.MainTheoremWitnesses

/-!
# The main theorem (spectral half)

This module proves the two final statements of the spectral half at the explicit
witnesses of `Global/MainTheoremWitnesses.lean`:

* `mainReducedTarget_holds`: the reduced-operator target of `Main.lean`; and
* `mainPhysicalConclusion_holds` (also named `main_theorem_spectral`): the
  spectral half of the paper's Theorem 1.2 (`thm:main`) stated in `Main.lean` — the
  theorem's "More precisely" clause and its real-datum clause.

Both are closed terms of the parameter chain: the velocity `mainVelocity` of
`eq:global-u`, the threshold `mainEps0 = δ₊/K₀²` and the growth floor `mainGrowthFloor = g_*`
of the two-component local seed.  No hypothesis remains; the per-diffusivity content is
`mainReducedClauses_holds`, i.e. `prop:global-spectral-transfer` followed by
`lem:axial-recovery`.

The clauses that are not part of `MainPhysicalConclusion` are
listed in the docstring of `Main.lean`.  The semigroup growth-rate clause is
proved separately (`gamma_ge_gamma0`, `FastDynamo/Dynamics/Assembly/MainGrowthRate.lean`)
and enters the strengthened statement of `FastDynamo/MainTheoremStrengthened.lean`,
together with `eq:main-thm-growth` for the semigroup orbit of the real datum and for every
solution of the curl-form equation with that datum, at the triple of the spectral clauses
(`MainSemigroupOrbitClauses`).  The two
dynamical clauses of Theorem 1.2 (its last sentence) are `MainTheoremDynamicalClauses`
of `FastDynamo/Dynamics/ParticleFlow.lean` and are proved by
`mainTheoremDynamical_holds` (`FastDynamo/Dynamics/MainLagrangianClauses.lean`); they are
projected there from the larger bundle `MainLagrangianClauses`, which is
`prop:particle-flow` and `cor:ideal-growth` at the same velocity.
-/

@[expose] public section
namespace FastDynamo

/-- The reduced-operator target holds: one nonzero real
divergence-free `W¹,∞` velocity and `ε₀, γ₀ > 0` such that every
`0 < ε ≤ ε₀` has a sector `K ≠ 0` and a reduced eigenpair with
`γ₀ ≤ Re λ`. -/
theorem mainReducedTarget_holds : MainReducedTarget :=
  ⟨mainVelocity, mainVelocity_isTransverseDivergenceFree, mainVelocity_ne_zero,
    mainEps0, mainGrowthFloor, mainEps0_pos, mainGrowthFloor_pos, mainReducedClauses_holds⟩

/-- The spectral half of the paper's Theorem 1.2 holds
(see `MainPhysicalConclusion` for the exact clauses). -/
theorem mainPhysicalConclusion_holds : MainPhysicalConclusion :=
  mainPhysicalConclusion_of_mainReducedTarget mainReducedTarget_holds

/-- Alias of `mainPhysicalConclusion_holds`, named after the spectral half of `thm:main`. -/
alias main_theorem_spectral := mainPhysicalConclusion_holds

end FastDynamo
