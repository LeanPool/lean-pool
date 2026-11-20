/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Finish.NegativeDiffusivity
public import LeanPool.FastDynamo.Dynamics.Assembly.FastDynamo
public import LeanPool.FastDynamo.Finish.MagneticScaleMain
public import LeanPool.FastDynamo.Finish.RealPartNotEigenmode
public import LeanPool.FastDynamo.Global.TorusBackgroundResolventHolomorphic
public import LeanPool.FastDynamo.Local.HorizontalSpectrumEigenvalue
public import LeanPool.FastDynamo.MainTheoremNormalized
public import LeanPool.FastDynamo.Dynamics.VanishingDiffusivity.Limit
public import LeanPool.FastDynamo.Dynamics.Assembly.SemigroupSpectralGrowth
public import LeanPool.FastDynamo.Palomar.Main

/-!
# A fast dynamo with zero topological entropy

Source: arxiv:2608.02586v3, url:https://github.com/lukasniebel/fast_dynamo_lean/tree/f2e17cdd0f814af1bd9c0a6ce10320b216ed4fe0
Authors: Lukas Niebel
Status: verified
Main declarations: `FastDynamo.challenge_statement`, `FastDynamo.main_theorem_strengthened`,
  `FastDynamo.tendstoUniformlyOn_resistiveEvolution_mainIdealGroup`
Tags: kinematic-dynamo, induction-equation, spectral-theory, topological-entropy
MSC: 35Q35, 76W05, 37B40
-/

/-!
# Fast dynamo: root module

This library formalises the paper *A fast dynamo with zero topological entropy*
(L. Niebel, arXiv:2608.02586v3): both halves of Theorem 1.2 (`thm:main`), the spectral one and
the dynamical one, together with the results around it — the axially independent case of
Lemma A.1 (`lem:semigroup-spectral-growth`), `prop:particle-flow`, `cor:ideal-growth` with the weak
form of the ideal induction equation, `cor:magnetic-scale` at the theorem's witnesses, and
the assertions of Remarks 1.4–1.7.  The release surface is:

* `FastDynamo.Main`: the statement `MainPhysicalConclusion` (the theorem's "More
  precisely" clause and its real-datum clause, without the semigroup growth-rate clause)
  and its reduction to the reduced-operator target `MainReducedTarget`.
* `FastDynamo.MainTheorem`: the proofs `mainPhysicalConclusion_holds`
  and `mainReducedTarget_holds`.
* `FastDynamo.MainTheoremStrengthened`: the stronger form the proof delivers,
  `main_theorem_strengthened` — explicit witnesses `mainVelocity`, `mainEps0`,
  `mainGrowthFloor` with `γ₀ = g_* ≥ (3/4)(448 − 4π²) ≥ 288`, the growth-floor eigenpair
  consequence of Proposition 7.1 at every admissible cell, the normalised velocity, the
  regularity of its chart-side and periodised representatives, the magnetic clauses on the
  literal `Torus 3`, the growth-rate clause `γ(u, ε) ≥ γ₀` for `0 < ε ≤ ε₀`, and
  `eq:main-thm-growth` for the semigroup orbit of the real datum and for every solution of the
  curl-form equation with that datum, at the triple of the spectral clauses.
* `FastDynamo.MainTheoremNormalized`: every clause of Theorem 1.2 for the normalised velocity
  of Remark 1.6, `mainTheoremNormalized_holds`.
* `FastDynamo.Finish.MagneticScaleMain`: `cor:magnetic-scale` at the witnesses of the theorem,
  `main_theorem_magnetic_scale`.
* `FastDynamo.Dynamics.Assembly.FastDynamo`: the definitions of dynamo, fast dynamo and slow
  dynamo of §1.1, and `isFastDynamo_mainVelocity`.
* `FastDynamo.Dynamics.Assembly.SemigroupSpectralGrowth`: the axially independent case of
  Lemma A.1 as one statement, `semigroupSpectralGrowth_holds`.
* `FastDynamo.Dynamics.MainLagrangianClauses`: the dynamical half at the same
  velocity — `mainTheoremDynamical_holds` for the theorem's own two clauses
  (its last sentence) and `mainTheoremLagrangian_holds` for the larger bundle
  `prop:particle-flow` + `cor:ideal-growth` it is projected from — hence Theorem 1.2
  in full, `mainTheoremComplete_holds`; the ideal solution group as the unique solution group
  of the ideal induction equation, `existsUnique_isIdealSolutionGroup_mainLiteralVelocity`;
  and the ideal–resistive gap `ideal_resistive_gap_holds` (the chain
  `γ_id(u) = 0 < γ₀ ≤ liminf_{ε ↓ 0} γ(u, ε)`, which joins the last clause of the theorem to
  `eq:main-growth-conclusion`; the paper states it as no single result).
* `FastDynamo.Dynamics.VanishingDiffusivity.Limit`: Remark 1.7,
  `tendstoUniformlyOn_resistiveEvolution_mainIdealGroup`, for each fixed divergence-free
  `L²` datum on bounded intervals of nonnegative time.

**Citations.**  Throughout this library the paper is cited by its LaTeX labels
(`thm:main`, `lem:axial-recovery`, `eq:main-thm-growth`, …), by the theorem numbers of the
paper (Theorem 1.2, Proposition 7.1, …) and by its section numbers (§1–§8, Appendix A).  The
Lean identifiers say `transverse` where the paper says "horizontal"; the correspondence is
recorded in `FastDynamo/Conventions.lean`.

The proof is assembled from the following layers (see `docs/MODULE_MAP.md`):

* `Conventions`, `Fourier/*`, `Analysis/*`: the torus, Fourier-graph Sobolev
  spaces, weak derivatives and Leibniz rules, periodic multipliers and cut-offs,
  whole-plane Fourier analysis, `H²` regularity, Rellich compactness, and the literal
  three-torus with its gradient, the mollifier `J_δ` and the Friedrichs commutator.
* `Operator/*`: domain operators, resolvents, Riesz projections, Fredholm and
  compactness theory, the resolvent set and spectrum of a partially defined operator,
  holomorphy of resolvents, the compact embedding `H² ↪ L²` of the product torus, the reduced,
  auxiliary and physical induction operators, the horizontal two-component operator of
  `lem:torus-sector-basic`, and the whole-plane local operator.
* `Local/*`: the two-component `L²`-witness variant of the local seed in Proposition 2.2
  (`prop:local-seed`): modified Bessel functions,
  the Ponomarenko dispersion function and its certified root on a segment, the piecewise
  Cartesian mode of `lem:jump-horizontal-mode` and its regularity, the horizontal form
  operator with its resolvent, its spectrum in the right half-plane (isolated eigenvalues)
  and local Riesz projection, the smoothed helical velocity, and the seed record
  `LocalSeedC2`.
* `Reduction/*`: the scaling identity `eq:scaling` of `lem:exact-renormalization`.
* `Global/*`: scale families, cell placement, the global velocity and its regularity
  (including its derivative at every point), the parameter choice, the background resolvent
  of `prop:background-resolvent` and its holomorphy, and the rescaled local resolvents of
  `cor:scaled-local-resolvents`, the torus charts and cut-offs, the two-summand parametrix and
  its error (`lem:parametrix-error`), the contour resolvent and the non-zero Riesz projection,
  the spectral transfer (`prop:global-spectral-transfer`), and the witnesses of the main
  theorem.
* `Finish/*`: the recovery of the axial component (`lem:axial-recovery`), divergence-free
  complex eigenmodes, the real datum and its exact `L²` norm law, the strong-solution
  certificate, the magnetic-length bounds and `cor:magnetic-scale`, the zero mean of the
  constructed fields (Remark 1.5, `rem:scope-intro`), Remark 1.4 on the real part of the
  mode, and the negative-diffusivity counterexample.
* `Dynamics/*` (Eulerian): the semigroup interface, uniqueness of forward strong
  solutions, the a priori energy bound and the energy identity `eq:energy-competition`, the
  Hille–Yosida generation theorem built from scratch in dissipative form, the product
  induction semigroup and its solenoidal restriction, and the growth rate `γ(u, ε)` with its
  floor and ceiling `γ₀ ≤ γ(u, ε) ≤ ‖∇⊥ u‖_∞` at the explicit witnesses; the growth bound of a
  semigroup as a limit (`Dynamics/GrowthBoundLimit.lean`) and its time rescaling; the
  generator of a semigroup, analytic semigroups, compactness and spectral mapping, the
  generator `L_{ε,u}` of the semigroup on `L²_σ`, and `γ(u, ε)` as a limit and as the
  spectral bound — the axially independent case of Lemma A.1
  (`lem:semigroup-spectral-growth`), stated as one structure in
  `Dynamics/Assembly/SemigroupSpectralGrowth.lean`; the dynamo definitions of §1.1.
* `Dynamics/Assembly/{NegativeSobolevResolvent,PhysicalInductionUniqueness,SemigroupOrbit}.lean`:
  "its solution" of `eq:main-thm-growth` — every forward strong solution of the curl-form
  equation with datum in `L²_σ` is the semigroup orbit, and the real datum's orbit is the
  explicit real curve and obeys the exact growth law, at the triple of the spectral clauses
  `MainPhysicalClausesAt` (`MainSemigroupOrbitClauses`).
* `Dynamics/ParticleFlow.lean`: the statement layer of the dynamical half —
  `IsParticleFlow`, `HasZeroTopologicalEntropy`, `IsIdealInductionGroup`,
  `MainLagrangianClauses` and `MainTheoremDynamicalClauses`.
* `Dynamics/IdealWeakForm.lean`, `Dynamics/IdealWeakFormRescaling.lean`: the weak form of the
  ideal induction equation — `IsIdealTestField`, `IsIdealWeakSolution`,
  `IsIdealSolutionGroup` — and its behaviour under time rescaling.
* `Dynamics/Flow/*` (Lagrangian): the particle flow in closed form.  The plane
  rotation and the radial shear bounds, the cell profiles and the single-cell flow
  map, the accumulating plane flow and its `ℤ²`-periodisation, the Lipschitz
  constants, the descent to `Torus 3` (`literalFlow`), the packing bound on `T³`
  and the Lipschitz-iterate entropy criterion, the derivative `DΦ_t` and its
  complexification, the variational equation `eq:flow-variational-equation`, measure
  preservation, the ODE itself (`isParticleFlow_literalFlow`) and its uniqueness by Grönwall
  on the lifts (`IsParticleFlow.unique`, `existsUnique_isParticleFlow_mainLiteralVelocity`);
  `eq:explicit-particle-flow` at torus level with the fixed points and the centre
  speed, and, in `Flow/LipschitzRate.lean`, the optimal Lipschitz constant `lipConst`
  with `lim_{|t| → ∞} |t|⁻¹ log Lip(Φ_t) = 0` (`prop:particle-flow`).
* `Dynamics/Ideal/*`: the ideal induction group.  Gradient orthogonality
  on the literal torus, the Cauchy transport operator `𝒯₀(t)` on `L²(T³;ℂ³)`,
  the truncated flows that make the solenoidal subspace invariant, strong
  continuity, the corestricted group `idealGroup` with
  `isIdealInductionGroup_idealGroup`; the velocity gradient and the stretching operator,
  the Cauchy orbits as weak solutions, the extension of the weak identity to Lipschitz test
  fields, and the uniqueness of weak solutions and of the solution group.
* `Dynamics/MainLagrangianClauses.lean`: the assembly — `MainLagrangianClauses` and
  `MainTheoremDynamicalClauses` at the constructed velocity, `MainTheoremLagrangian`,
  `MainTheoremDynamical`, `MainTheoremComplete`, the unique solution group and the
  ideal–resistive gap; `Dynamics/NormalizedLagrangianClauses.lean` the same for the
  normalised velocity.
* `Dynamics/VanishingDiffusivity/*`: Remark 1.7 — the bridge between the product picture of
  the resistive semigroup and the literal picture of the ideal group, the energy estimate
  against the mollified ideal orbit, and the limit `ε ↓ 0`.

* `Palomar/*`: Theorem 1.2 in the form of the Challenge statement (`Challenge.lean` at the
  root of the repository), which uses only mathlib notions and fourteen short definitions.
  `Palomar/Statement.lean` repeats those definitions character for character (namespace
  `FastDynamoChallenge`); the other modules identify them with the library's objects — Fourier
  coefficients, `L²_σ`, `H²`, the Fourier symbol of the induction operator, the induction
  semigroup, the particle flow, the ideal solution group — and `Palomar/Main.lean` proves the
  statement (`challenge_statement`).

`Check.lean` and `FastDynamo/AxiomAudit.lean` form the audited surface; the
release gate is `scripts/audit.sh`.
-/
