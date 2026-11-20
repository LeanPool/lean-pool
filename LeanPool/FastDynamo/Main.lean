/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Finish.RealSolution

/-!
# The main theorem: statement layer

This module states the spectral half of the paper's main theorem (Theorem 1.2, "A fast dynamo
with zero topological entropy", `thm:main`) at the level of the concrete objects of this
formalisation, and proves that it follows from a purely spectral statement about the reduced
axial induction operator.

## What is stated

`MainPhysicalConclusion` is the **spectral half** of Theorem 1.2 — the theorem's "More
precisely" and "Moreover, the real-valued datum" clauses — under the theorem's existentials:

* one real, divergence-free, nonzero `W¹,∞` velocity `u`, chosen before the diffusivity.  The
  Lean velocity lives on the horizontal torus and is read as an axially independent field
  (`TransverseRealW1Inf`); the theorem asks only for `u ∈ W^{1,∞}(T³; ℝ³)` with `Div u = 0`,
  and the axial independence and `u ≠ 0` are properties of the paper's construction
  (`lem:global-velocity`) that the Lean statement carries in addition;
* thresholds `ε₀ > 0` and a growth floor `γ₀ > 0` independent of `ε`;
* for every `0 < ε ≤ ε₀`, an axial Fourier index `K ≠ 0`, an eigenvalue `λ` with
  `γ₀ ≤ Re λ`, and a nonzero horizontal amplitude `b ∈ H²(T²; ℂ³)` such that the complex mode
  `V = e^{2πiKx₃} b` is an `H²` divergence-free eigenmode of the auxiliary and of the physical
  (curl-form) induction operator (`eq:main-spectral-conclusion`).  The three-torus is the
  product model `T² × T` (`ProductTorus3`), and the curl-form eigenvalue equation is an
  identity in `H⁻²`;
* the real datum `B_in = Re V` is nonzero, and the explicit real curve `B(t)` is a
  divergence-free strong solution of the induction equation with the exact norm law
  `‖B(t)‖ = e^{t Re λ} ‖B_in‖` (`eq:main-thm-growth`, which the paper states for `t ≥ 0`;
  the Lean clause holds at every real time) and the uniform lower bound
  `e^{t γ₀} ‖B_in‖ ≤ ‖B(t)‖` for `t ≥ 0`.  The `L²` norms are those of the product measure
  of the Haar probability measures on `T²` and `T`, which the measure-preserving
  identification `T² × T ≅ T³` carries to the paper's Lebesgue measure on `T³ = ℝ³/ℤ³`.

## What is not stated here

The theorem's growth-rate clause `γ(u, ε) ≥ γ₀` (the sentence before
`eq:main-growth-conclusion`, whose `liminf` form is that display) concerns the exponential
growth rate of the resistive semigroup `e^{t L_{ε,u}}` on `L²_σ(T³; ℂ³)`.  The Lean semigroup
is constructed in `FastDynamo/Dynamics/Assembly/` (Hille–Yosida generation of the semigroup
of the *auxiliary* induction operator on the product `L²` space, invariance of the solenoidal
subspace, transport to the literal three-torus); its growth bound is `gamma`, and the clause
is the theorem `gamma_ge_gamma0` of `FastDynamo/Dynamics/Assembly/MainGrowthRate.lean`.  It
is part of the strengthened statement `FastDynamo/MainTheoremStrengthened.lean` (fields
`growthRate`, `growthRate_le`), not of `MainPhysicalConclusion`, which is the purely spectral
statement layer.  The paper states the clause for `0 < ε ≤ ε₀`, and every Lean form here and
downstream uses the same interval.  The docstring of `gamma` records how it relates to the paper's
`γ(u, ε)`: it is the growth bound of the `C₀`-semigroup generated on `L²_σ` by `L_{ε,u}` with domain
`H² ∩ L²_σ`, a genuine limit, and equal to the spectral bound of `L_{ε,u}` (Lemma A.1,
`lem:semigroup-spectral-growth`, is `SemigroupSpectralGrowth`), on the product model `T² × T` with
an axially independent velocity.

The theorem's last sentence is its **dynamical** half, asserted for the same velocity field:
`h_top(Φ_t) = 0` for all `t ∈ ℝ`, and `lim_{t → ∞} t⁻¹ log ‖𝒯₀(t)‖_{L²_σ → L²_σ} = 0` for
the ideal induction solution group `𝒯₀`.  It is stated and proved outside
`MainPhysicalConclusion`:

* the predicate is `MainTheoremDynamicalClauses`
  (`FastDynamo/Dynamics/ParticleFlow.lean`), `MainTheoremDynamical` its
  instance at the constructed velocity, and `mainTheoremDynamical_holds`
  (`FastDynamo/Dynamics/MainLagrangianClauses.lean`) its proof;
* it is projected from the strictly larger bundle `MainLagrangianClauses` —
  `prop:particle-flow` and `cor:ideal-growth` together, including the Lipschitz bound
  `eq:linear-flow-lipschitz` and the two-sided per-datum bounds of `cor:ideal-growth`, which
  are not clauses of Theorem 1.2;
* the flow is the explicit one of `FastDynamo/Dynamics/Flow/*`, proved to be
  *the* particle flow of the velocity, the entropy clause goes through
  Mathlib's cover entropy (`FastDynamo/Analysis/EntropyCriterion.lean`), and
  the ideal group is the Cauchy transport operator of
  `FastDynamo/Dynamics/Ideal/*`;
* `MainTheoremComplete` joins the spectral half, the theorem's two dynamical
  clauses and the Lagrangian bundle (`FastDynamo/MainTheoremStrengthened.lean`).

The theorem says that "its solution" — the solution with initial datum `B_in` — obeys
`eq:main-thm-growth`.  The paper states no separate well-posedness theorem; its proof of
`thm:main` bounds `‖e^{t L_{ε,u}}‖` below by `‖B(t)‖ / ‖B_in‖`, so it reads the solution as
the orbit of `B_in` under the semigroup that `L_{ε,u}` generates on `L²_σ` (§1.1).
`MainPhysicalClauses` states that the explicit curve `B(t)` is a strong solution of the
curl-form equation in `H⁻²` at every real time.  The definite article is
`MainSemigroupOrbitClauses` (`FastDynamo/Dynamics/Assembly/SemigroupOrbit.lean`, asserted at
the theorem's witnesses as the field `semigroupOrbit` of `MainTheoremStrengthened`): `B_in`
lies in `L²_σ`, its orbit under `e^{t L_{ε,u}}` is the explicit real curve and obeys
`eq:main-thm-growth` for `t ≥ 0`, and every forward strong solution of the curl-form equation
with initial value `B_in` — an `H²`-valued curve differentiable in the Fourier model of `H⁻²`
within `[0, ∞)`, on the product torus — is that orbit, hence obeys the same law.  The same
predicate asserts `MainPhysicalClausesAt` at the triple `(K, λ, b)` of the orbit, so the
eigenmode, the real datum and its solution belong to one triple.  These clauses
cannot live in `MainPhysicalClauses`: this module is imported by the resolvent chain that
builds the semigroup, so naming the semigroup here would close an import cycle.  Uniqueness of
forward strong solutions with the same initial state is proved for the fixed-sector reduced
operator `reducedInductionOperator u ε K` (`FastDynamo/Dynamics/StrongSolutionUniqueness.lean`),
for the auxiliary product operator (`productInductionOperator_forwardStrongSolutionsUnique`,
`FastDynamo/Dynamics/Assembly/AxialSectorDomain.lean`) and for the curl-form product operator
of the clauses below (`productPhysicalInductionOperator_forwardStrongSolutionsUnique`,
`FastDynamo/Dynamics/Assembly/PhysicalInductionUniqueness.lean`).

## Reduction

`MainReducedTarget` is the reduced-operator statement that the global
construction has to deliver: for the fixed velocity and every small
diffusivity, an eigenpair of `reducedInductionOperator u ε K` with real part
at least `γ₀`.  `mainPhysicalConclusion_of_mainReducedTarget` shows that
this already implies every clause above, using the finish layer.

The per-diffusivity clauses are named separately (`MainReducedClauses`,
`MainPhysicalClauses`) so that the same clauses can be asserted for explicit
or normalised witnesses; the stronger forms the proof delivers are collected in
`FastDynamo/MainTheoremStrengthened.lean`.
-/

@[expose] public section
namespace FastDynamo

noncomputable section

/-- The per-diffusivity reduced clauses at a fixed velocity `u`, threshold
`eps0` and growth floor `gamma0`: for every `0 < ε ≤ ε₀` some nonzero axial
sector `K` carries an eigenpair of the reduced induction operator with
`γ₀ ≤ Re λ`.  Keeping the clauses separate from the outer existentials lets
the same predicate be asserted for explicit, normalised, or otherwise
strengthened witnesses. -/
def MainReducedClauses (u : TransverseRealW1Inf) (eps0 gamma0 : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → eps ≤ eps0 →
    ∃ (K : ℤ) (lambda : ℂ) (b : TransverseC3H2),
      K ≠ 0 ∧ gamma0 ≤ lambda.re ∧
      (reducedInductionOperator u eps K).IsEigenpair lambda b

/-- The reduced-operator target of the global construction: one nonzero real
divergence-free `W¹,∞` velocity and `ε₀, γ₀ > 0` such that for every
`0 < ε ≤ ε₀` some nonzero axial sector `K` carries an eigenpair of the reduced
induction operator with `γ₀ ≤ Re λ`.  The divergence-free property of `u`
is part of the existential because every downstream transfer theorem
consumes it. -/
def MainReducedTarget : Prop :=
  ∃ u : TransverseRealW1Inf,
    IsTransverseDivergenceFree u ∧ u ≠ 0 ∧
    ∃ eps0 gamma0 : ℝ, 0 < eps0 ∧ 0 < gamma0 ∧
      MainReducedClauses u eps0 gamma0

/-- The clauses of the paper's Theorem 1.2 for one diffusivity `eps` and one witness triple
`(K, lambda, b)` at a velocity `u` and growth floor `gamma0`, spelled out clause by clause.
`MainPhysicalClauses` asserts them for every `0 < ε ≤ ε₀` at some triple. -/
def MainPhysicalClausesAt (u : TransverseRealW1Inf) (gamma0 eps : ℝ) (K : ℤ) (lambda : ℂ)
    (b : TransverseC3H2) : Prop :=
  -- `K_ε ∈ ℤ \ {0}`, `Re λ_ε ≥ γ₀`, `0 ≠ b^ε ∈ H²(T²; ℂ³)`
  K ≠ 0 ∧ gamma0 ≤ lambda.re ∧ b ≠ 0 ∧
  -- the reduced eigenpair, kept as the reference datum
  (reducedInductionOperator u eps K).IsEigenpair lambda b ∧
  -- `V^ε = e^{2πiKx₃} b` is an `L²` eigenmode of the auxiliary operator
  (productInductionOperator u eps).IsEigenpair lambda (axialLiftH2 K b) ∧
  -- `V^ε` is divergence-free
  productDivergenceFromH2 (axialLiftH2 K b) = 0 ∧
  -- `L_{ε,u} V^ε = λ_ε V^ε` for the physical curl-form operator
  (productPhysicalInductionOperator u eps).IsEigenpair lambda
    (axialLiftH2 K b) ∧
  -- `B_in^ε = Re V^ε ≠ 0`
  realAxialInitialField K (transverseH2Embedding b) ≠ 0 ∧
  -- the real curve never vanishes
  (∀ t : ℝ,
    realAxialTrajectory K lambda (transverseH2Embedding b) t ≠ 0) ∧
  -- exact norm law `‖B^ε(t)‖ = e^{t Re λ_ε} ‖B_in^ε‖`, at every real time
  (∀ t : ℝ,
    ‖realAxialTrajectory K lambda (transverseH2Embedding b) t‖ =
      Real.exp (t * lambda.re) *
        ‖realAxialInitialField K (transverseH2Embedding b)‖) ∧
  -- growth lower bound with the `ε`-independent rate `γ₀`
  (∀ t : ℝ, 0 ≤ t →
    Real.exp (t * gamma0) *
        ‖realAxialInitialField K (transverseH2Embedding b)‖ ≤
      ‖realAxialTrajectory K lambda (transverseH2Embedding b) t‖) ∧
  -- the `H²` representative of the real field starts at `Re V^ε`
  realifiedEigenTrajectoryH2 lambda (axialLiftH2 K b) 0 =
    productRealPartH2 (axialLiftH2 K b) ∧
  -- the representative is real (conjugation-fixed) at every time
  (∀ t : ℝ,
    productConjH2 (realifiedEigenTrajectoryH2 lambda (axialLiftH2 K b) t) =
      realifiedEigenTrajectoryH2 lambda (axialLiftH2 K b) t) ∧
  -- and divergence-free at every time
  (∀ t : ℝ,
    productDivergenceFromH2
      (realifiedEigenTrajectoryH2 lambda (axialLiftH2 K b) t) = 0) ∧
  -- the `H²` representative is the explicit real `L²` curve
  (∀ t : ℝ,
    complexifyProductR3L2
        (realAxialTrajectory K lambda (transverseH2Embedding b) t) =
      productH2Embedding
        (realifiedEigenTrajectoryH2 lambda (axialLiftH2 K b) t)) ∧
  -- `B^ε(·)` is a strong solution of the physical induction equation
  (productPhysicalInductionOperator u eps).IsStrongSolution
    (realifiedEigenTrajectoryH2 lambda (axialLiftH2 K b))

/-- The per-diffusivity physical clauses of the paper's Theorem 1.2 at a fixed
velocity `u`, threshold `eps0` and growth floor `gamma0`: for every `0 < ε ≤ ε₀` some
`(K, λ, b)` satisfies `MainPhysicalClausesAt`.  See the module docstring for the reading of
each clause and for the growth-rate clause, which is stated separately. -/
def MainPhysicalClauses (u : TransverseRealW1Inf) (eps0 gamma0 : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → eps ≤ eps0 →
    ∃ (K : ℤ) (lambda : ℂ) (b : TransverseC3H2), MainPhysicalClausesAt u gamma0 eps K lambda b

/-- The spectral half of the paper's Theorem 1.2 in the paper's
quantifier order: one nonzero real divergence-free `W¹,∞` velocity and
`ε₀, γ₀ > 0` such that the physical clauses hold for every `0 < ε ≤ ε₀`. -/
def MainPhysicalConclusion : Prop :=
  ∃ u : TransverseRealW1Inf,
    IsTransverseDivergenceFree u ∧ u ≠ 0 ∧
    ∃ eps0 gamma0 : ℝ, 0 < eps0 ∧ 0 < gamma0 ∧
      MainPhysicalClauses u eps0 gamma0

/-- At a fixed divergence-free velocity and a positive growth floor, every physical clause for
one diffusivity follows from a reduced eigenpair of growth at least `γ₀` in a nonzero sector
through the finish layer (`realStrongModeCertificate_of_reducedEigenpair`). -/
theorem mainPhysicalClausesAt_of_reducedEigenpair
    {u : TransverseRealW1Inf} (hu : IsTransverseDivergenceFree u)
    {gamma0 : ℝ} (hgamma0 : 0 < gamma0) {eps : ℝ} (hpos : 0 < eps) {K : ℤ} (hK : K ≠ 0)
    {lambda : ℂ} {b : TransverseC3H2} (hgrowth : gamma0 ≤ lambda.re)
    (hpair : (reducedInductionOperator u eps K).IsEigenpair lambda b) :
    MainPhysicalClausesAt u gamma0 eps K lambda b := by
  have hb : b ≠ 0 := by
    intro hb
    exact hpair.1 (by rw [hb, map_zero])
  have cert : RealStrongModeCertificate u eps K lambda b gamma0 :=
    realStrongModeCertificate_of_reducedEigenpair
      u hu eps hpos.le K hK lambda (lt_of_lt_of_le hgamma0 hgrowth)
      b hpair gamma0 hgrowth
  exact ⟨hK, hgrowth, hb, hpair,
    cert.conditional.auxiliaryEigenpair,
    cert.conditional.divergence_eq_zero,
    cert.conditional.physicalEigenpair,
    cert.conditional.realInitial_ne_zero,
    cert.conditional.realTrajectory_ne_zero,
    cert.conditional.realTrajectory_norm,
    cert.conditional.realTrajectory_lower_bound,
    cert.initial_state,
    cert.state_fixed,
    cert.state_solenoidal,
    cert.real_field_embedding,
    cert.physical_strong_solution⟩

/-- At a fixed divergence-free velocity and a positive growth floor, every
physical clause follows from the reduced clauses through the finish layer. -/
theorem mainPhysicalClauses_of_mainReducedClauses
    {u : TransverseRealW1Inf} (hu : IsTransverseDivergenceFree u)
    {eps0 gamma0 : ℝ} (hgamma0 : 0 < gamma0)
    (hmode : MainReducedClauses u eps0 gamma0) :
    MainPhysicalClauses u eps0 gamma0 := by
  intro eps hpos hle
  obtain ⟨K, lambda, b, hK, hgrowth, hpair⟩ := hmode eps hpos hle
  exact ⟨K, lambda, b,
    mainPhysicalClausesAt_of_reducedEigenpair hu hgamma0 hpos hK hgrowth hpair⟩

/-- Every clause of the spectral half of Theorem 1.2 follows from the
reduced-operator target through the finish layer. -/
theorem mainPhysicalConclusion_of_mainReducedTarget
    (h : MainReducedTarget) : MainPhysicalConclusion := by
  obtain ⟨u, hu, hune, eps0, gamma0, heps0, hgamma0, hmode⟩ := h
  exact ⟨u, hu, hune, eps0, gamma0, heps0, hgamma0,
    mainPhysicalClauses_of_mainReducedClauses hu hgamma0 hmode⟩

end

end FastDynamo
