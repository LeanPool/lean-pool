/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.MainTheorem
public import LeanPool.FastDynamo.Global.GlobalSpectralTransferAllCells
public import LeanPool.FastDynamo.Operator.ReducedInductionScaling
public import LeanPool.FastDynamo.Global.TorusGlobalVelocityLipschitz
public import LeanPool.FastDynamo.Dynamics.Assembly.SemigroupOrbit
public import LeanPool.FastDynamo.Dynamics.ParticleFlow

/-!
# The main theorem, strengthened

`FastDynamo.MainTheorem` proves the spectral half of the paper's Theorem 1.2
(`thm:main`) in the theorem's own existential form.  This module collects the stronger forms
that the proof delivers, at the explicit witnesses of `Global/MainTheoremWitnesses`:

* **Explicit constants.**  The velocity `mainVelocity`, the threshold
  `mainEps0 = δ₊/K₀²` and the growth floor
  `mainGrowthFloor = g_* = Re(centre Γ) − radius Γ` (`eq:spectral-gap`) are closed terms, the
  physical clauses hold for them, and the growth floor has the explicit lower bound
  `(3/4)(448 − 4π²)` — three quarters of the paper's bound `(7/16)ϱ² − 4π²` on the real part
  of the seed eigenvalue (proof of `lem:jump-horizontal-mode`) at the formalisation's choice
  `ϱ = 32` — hence is at least `288`.  Theorem 1.2 itself names no value of `ε₀`
  or `γ₀`; the values are those the paper fixes in its construction, `ε₀ = δ₊/K₀²` in §3.2
  and `γ₀ = g_*` in the proof of `thm:main`.
* **Every admissible cell.**  `prop:global-spectral-transfer` (Proposition 7.1) is stated in
  the paper for every `0 < ε ≤ ε₀` and every `n` with `ε / ℓ_n² ∈ I`, while the proof of
  Theorem 1.2 uses one such `n(ε)`.  `MainEveryAdmissibleCellClauses` is that every-cell
  statement in eigenpair form: for every such `ε` and `n`, the sector `K_n` carries a growing
  eigenpair of the reduced and of the auxiliary operator.  It states the eigenvalue with
  `Re λ ≥ g_*` (the "In particular" of the proposition, lifted to three components), not the
  resolvent inclusion `Γ_τ ⊂ ρ(A_{ε,K_n})` or `Q_{ε,n} ≠ 0`.
* **Normalisation.**  The spectral half also holds for a velocity of `W^{1,∞}` norm at most
  one (Remark 1.6, the remark after `rem:scope-intro`), with the named witness
  `normalizedVelocity mainVelocity` and the thresholds `M⁻¹ ε₀`, `M⁻¹ γ₀` for
  `M = max (1, ‖mainVelocity‖)`, as in the remark.  The fields `normalized` and
  `normalizedWitness` carry the spectral clauses `MainPhysicalClauses`; every conclusion of
  Theorem 1.2 for the normalised velocity, with the remark's two identities, is
  `MainTheoremNormalized` (`FastDynamo/MainTheoremNormalized.lean`,
  `mainTheoremNormalized_holds`).
* **Qualitative regularity of the velocity.**  The chart-side representative
  of `mainVelocity` is differentiable everywhere, smooth away from the
  accumulation point, Lipschitz, has zero derivative at the accumulation
  point, and its derivative is discontinuous there, so the velocity is not
  `C¹` (§3.4, "Why the construction stops at Lipschitz regularity", and `rem:scope-intro`).
  All of this transfers to the `ℤ²`-periodisation of that representative,
  which is the pullback of the torus-side representative along the quotient
  map at *every* point of the plane and agrees with the chart-side
  representative on the fundamental box.  The torus-side representative
  represents the value of `mainVelocity` almost everywhere and is Lipschitz
  for the quotient metric of the torus, as is its axially independent
  extension to `Torus 3`.
* **The literal three-torus.**  The real magnetic trajectory, transported by
  the measure-preserving identification of the product model with
  `Torus 3 = Fin 3 → UnitAddCircle`, obeys the exact norm law and the growth
  lower bound entirely inside `L²(Torus 3; ℝ³)`, and its complexification is the orbit of
  the transported real datum under the induction semigroup `literalInductionSemigroup` on
  `L²_σ(Torus 3; ℂ³)`, at the same triple `(K, λ, b)` (`MainLiteralTorusClauses`).  The
  velocity is an axially independent function on `Torus 3`.

* **The growth-rate clause.**  The clause `γ(u, ε) ≥ γ₀` of Theorem 1.2 (whose `liminf` form
  is `eq:main-growth-conclusion`), where `γ(u, ε)` is the exponential growth rate
  `eq:semigroup-growth-rate` of the induction semigroup `e^{t L_{ε,u}}` on
  `L²_σ(T³; ℂ³)` (`FastDynamo/Dynamics/Assembly/MainGrowthRate.lean`: the semigroup generated
  on `L²_σ` by `L_{ε,u}` with domain `H² ∩ L²_σ`, constructed as the restriction of the
  Hille–Yosida semigroup of the auxiliary all-frequency induction operator and transported to
  the literal three-torus), together with the ceiling `γ(u, ε) ≤ ‖∇⊥u‖_∞`, so the growth rate
  is a finite number pinned between two explicit reals.  The field `growthRate` asserts the clause
  for `0 < ε ≤ ε₀`, the interval on which the paper states it.  The growth bound is the limit of
  `t⁻¹ log ‖e^{t L_{ε,u}}‖` and the spectral bound of `L_{ε,u}`; see the docstring of `gamma` and
  `SemigroupSpectralGrowth` (Lemma A.1, `lem:semigroup-spectral-growth`).

* **"Its solution" of `eq:main-thm-growth`.**  The field `semigroupOrbit`
  asserts `MainSemigroupOrbitClauses` (`FastDynamo/Dynamics/Assembly/SemigroupOrbit.lean`):
  at every `0 < ε ≤ ε₀` the real datum `B_in^ε = Re V^ε` lies in `L²_σ`, is non-zero,
  its orbit under the induction semigroup on `L²_σ` is the explicit real curve
  `B^ε(t)` and obeys `‖e^{tL}B_in^ε‖ = e^{t Re λ_ε}‖B_in^ε‖` for `t ≥ 0`, and every forward
  strong solution of the curl-form induction equation with initial value `B_in^ε` is that
  orbit and obeys the same law and the lower bound `e^{t γ₀}‖B_in^ε‖`.  At the same triple
  `(K_ε, λ_ε, b^ε)` every physical clause `MainPhysicalClausesAt` holds, so the eigenmode,
  the real datum and its solution belong to one triple; the field `physicalClauses` is the
  same content with the triple chosen separately.  The paper has no
  separate well-posedness theorem; the solution class (`H²`-valued curves differentiable in the
  Fourier model of `H⁻²` within `[0, ∞)`, on the product torus) is described in
  `FastDynamo/Dynamics/Assembly/SemigroupOrbit.lean`.

Everything is bundled in the `Prop`-valued structure `MainTheoremStrengthened`
and proved in `main_theorem_strengthened`.

The **dynamical half** of Theorem 1.2 is its last sentence: `h_top(Φ_t) = 0` for all
`t ∈ ℝ` and `lim_{t → ∞} t⁻¹ log ‖𝒯₀(t)‖_{L²_σ → L²_σ} = 0`.  Those two clauses
are `MainTheoremDynamicalClauses` (`FastDynamo/Dynamics/ParticleFlow.lean`), and
`MainTheoremDynamical` below is their instance at `mainLiteralVelocity`.  The larger bundle
they are projected from — `prop:particle-flow` and `cor:ideal-growth`, i.e. in addition the
Lipschitz bound `eq:linear-flow-lipschitz` and the two-sided per-datum bounds of
`cor:ideal-growth`, which the theorem itself does not state — is
`MainLagrangianClauses`, named `MainTheoremLagrangian` at that velocity.  `MainTheoremComplete`
carries all three: `strengthened`, `dynamical`, `lagrangian`.

**Conditional forms.**  `mainLiteralVelocity` is defined in this module, and the module
that proves the Lagrangian clauses imports it, so the conditionals
`mainTheoremComplete_of_lagrangian`, `ideal_resistive_gap` and
`ideal_resistive_gap_at_diffusivity` are stated here with that hypothesis.  It is
discharged in
`FastDynamo/Dynamics/MainLagrangianClauses.lean`, which imports this module and proves
`mainTheoremLagrangian_holds`, `mainTheoremDynamical_holds`, `mainTheoremComplete_holds`,
`ideal_resistive_gap_holds` and `ideal_resistive_gap_at_diffusivity_holds` — the same
statements with no hypothesis at all.  The proofs are the blueprint nodes
`prop:particle-flow` and `cor:ideal-growth` of `blueprint/src/chapters/particle.tex`,
realised in `FastDynamo/Dynamics/Flow/*` and `FastDynamo/Dynamics/Ideal/*`.

`ideal_resistive_gap` returns the chain `γ_id(u) = 0 < γ₀ ≤ liminf_{ε ↓ 0} γ(u, ε)`, with
`γ_id` the rate of the ideal *operator norm*; `ideal_resistive_gap_at_diffusivity` is its
sharper fixed-`ε` packaging.  The paper states this chain as no single result, but each
member is a statement of the paper: the left one is the last clause of `thm:main` and
`eq:zero-ideal-growth` of `cor:ideal-growth`, the middle one is `γ₀ > 0` of `thm:main`, and
the right one is `eq:main-growth-conclusion`.  Both are proved downstream, as
`ideal_resistive_gap_holds` and `ideal_resistive_gap_at_diffusivity_holds`.
-/

@[expose] public section
namespace FastDynamo

noncomputable section

open MeasureTheory
open HorizontalMode
open ScaleFamily.TorusCellPlacement.FullVelocityConcrete

/-! ## The seed's helical speeds -/

/-- The seed's angular speed is nonzero.  This is what makes the chart-side representative of
the velocity fail to be `C¹` at the accumulation point. -/
theorem seed_angularSpeed_ne_zero : globalSeedInterface.angularSpeed ≠ 0 :=
  globalSeedInterface_angularSpeed_ne_zero

/-! ## Representatives of the theorem's velocity -/

/-- The chart-side (Euclidean) representative of the theorem's velocity: the
paper's cell sum in the placement chart, at the seed's helical speeds and
the chain's axial shift. -/
def mainVelocityChartRepresentative : ℝ × ℝ → R3 :=
  parameterizedFullGlobalEuclideanRealSource globalSeedInterface.smoothingWidth
    mainParameterChoice.placement globalSeedInterface.angularSpeed
    globalSeedInterface.axialSpeed mainParameterChoice.tau

/-- The `ℤ²`-periodisation of the chart-side representative: the paper's
velocity repeated over the integer lattice.  It is the object that the
torus-side representative pulls back to at *every* point of the plane. -/
def mainVelocityPeriodizedRepresentative : ℝ × ℝ → R3 :=
  parameterizedFullGlobalPeriodizedRealSource globalSeedInterface.smoothingWidth
    mainParameterChoice.placement globalSeedInterface.angularSpeed
    globalSeedInterface.axialSpeed mainParameterChoice.tau

/-- The torus-side pointwise representative of the theorem's velocity. -/
def mainVelocityTorusRepresentative : TransverseTorus → R3 :=
  parameterizedFullGlobalRealTorusSource globalSeedInterface.smoothingWidth
    mainParameterChoice.placement globalSeedInterface.angularSpeed
    globalSeedInterface.axialSpeed mainParameterChoice.tau

/-- The value of the theorem's velocity is represented almost everywhere by the
torus-side pointwise representative. -/
theorem transverseW1InfValue_mainVelocity_ae :
    (transverseW1InfValue mainVelocity : TransverseTorus → R3) =ᵐ[transverseMeasure]
      mainVelocityTorusRepresentative :=
  transverseW1InfValue_parameterizedFullGlobalW1Inf_eq_realSource_ae
    globalSeedInterface.smoothingWidth mainParameterChoice.placement
    globalSeedInterface.angularSpeed globalSeedInterface.axialSpeed
    mainParameterChoice.tau mainParameterChoice.tau_nonneg

/-- **The identification at every point of the plane.**  Pulled back along the
quotient map, the torus-side representative is the periodised chart-side
representative — in particular at the accumulation point `p_∞ = (0, 1/2)`,
which the placement chart misses. -/
theorem mainVelocityTorusRepresentative_transverseTorusPoint_eq_periodized (x : ℝ × ℝ) :
    mainVelocityTorusRepresentative (transverseTorusPoint x) =
      mainVelocityPeriodizedRepresentative x :=
  parameterizedFullGlobalRealTorusSource_transverseTorusPoint
    globalSeedInterface.smoothingWidth mainParameterChoice.placement
    globalSeedInterface.angularSpeed globalSeedInterface.axialSpeed
    mainParameterChoice.tau x

/-- On the fundamental box `(0,1]²` the periodised representative is the
chart-side representative. -/
theorem mainVelocityPeriodizedRepresentative_eq_chart {x : ℝ × ℝ}
    (h1 : x.1 ∈ Set.Ioc (0 : ℝ) 1) (h2 : x.2 ∈ Set.Ioc (0 : ℝ) 1) :
    mainVelocityPeriodizedRepresentative x = mainVelocityChartRepresentative x :=
  parameterizedFullGlobalPeriodizedRealSource_eq_of_mem_Ioc
    globalSeedInterface.smoothingWidth mainParameterChoice.placement
    globalSeedInterface.angularSpeed globalSeedInterface.axialSpeed
    mainParameterChoice.tau h1 h2

/-- **The paper's regularity claims for the velocity**: the chart-side
representative is differentiable everywhere, smooth away from the accumulation
point, Lipschitz, has derivative zero at the accumulation point, and its
derivative is discontinuous there (so the velocity is not `C¹`). -/
theorem mainVelocityChartRepresentative_qualitative :
    GlobalVelocityQualitative mainVelocityChartRepresentative :=
  parameterizedFullGlobalEuclideanRealSource_qualitative
    globalSeedInterface.smoothingWidth mainParameterChoice.placement
    globalSeedInterface.angularSpeed globalSeedInterface.axialSpeed
    mainParameterChoice.tau mainParameterChoice.tau_nonneg
    seed_angularSpeed_ne_zero

/-- The explicit — but not claimed optimal — Lipschitz constant of the
chart-side representative. -/
def mainVelocityLipschitzBound : ℝ :=
  globalVelocityLipschitzBound globalSeedInterface.smoothingWidth
    mainParameterChoice.placement globalSeedInterface.angularSpeed
    globalSeedInterface.axialSpeed mainParameterChoice.tau

/-- The chart-side representative is Lipschitz with the explicit constant. -/
theorem lipschitzWith_mainVelocityChartRepresentative :
    LipschitzWith (Real.toNNReal mainVelocityLipschitzBound)
      mainVelocityChartRepresentative :=
  lipschitzWith_parameterizedFullGlobalEuclideanRealSource
    globalSeedInterface.smoothingWidth mainParameterChoice.placement
    globalSeedInterface.angularSpeed globalSeedInterface.axialSpeed
    mainParameterChoice.tau mainParameterChoice.tau_nonneg

/-- The torus-side representative is Lipschitz for the quotient metric of the
transverse torus, with twice the chart-side constant. -/
theorem lipschitzWith_mainVelocityTorusRepresentative :
    LipschitzWith (2 * Real.toNNReal mainVelocityLipschitzBound)
      mainVelocityTorusRepresentative :=
  lipschitzWith_parameterizedFullGlobalRealTorusSource
    globalSeedInterface.smoothingWidth mainParameterChoice.placement
    globalSeedInterface.angularSpeed globalSeedInterface.axialSpeed
    mainParameterChoice.tau mainParameterChoice.tau_nonneg

/-! ## Regularity of the periodised representative -/

/-- The periodised representative is Lipschitz with twice the chart-side
constant. -/
theorem lipschitzWith_mainVelocityPeriodizedRepresentative :
    LipschitzWith (2 * Real.toNNReal mainVelocityLipschitzBound)
      mainVelocityPeriodizedRepresentative :=
  lipschitzWith_parameterizedFullGlobalPeriodizedRealSource
    globalSeedInterface.smoothingWidth mainParameterChoice.placement
    globalSeedInterface.angularSpeed globalSeedInterface.axialSpeed
    mainParameterChoice.tau mainParameterChoice.tau_nonneg

/-- The periodised representative is differentiable at every point of the
plane. -/
theorem differentiable_mainVelocityPeriodizedRepresentative :
    Differentiable ℝ mainVelocityPeriodizedRepresentative :=
  differentiable_parameterizedFullGlobalPeriodizedRealSource
    globalSeedInterface.smoothingWidth mainParameterChoice.placement
    globalSeedInterface.angularSpeed globalSeedInterface.axialSpeed
    mainParameterChoice.tau mainParameterChoice.tau_nonneg

/-- The periodised representative is smooth of every order away from the
integer translates of the accumulation point. -/
theorem contDiffAt_mainVelocityPeriodizedRepresentative {x : ℝ × ℝ}
    (hx : ∀ k : ℤ × ℤ, x - ((k.1 : ℝ), (k.2 : ℝ)) ≠ accumulationPoint) :
    ContDiffAt ℝ (⊤ : ℕ∞) mainVelocityPeriodizedRepresentative x :=
  contDiffAt_parameterizedFullGlobalPeriodizedRealSource
    globalSeedInterface.smoothingWidth mainParameterChoice.placement
    globalSeedInterface.angularSpeed globalSeedInterface.axialSpeed
    mainParameterChoice.tau hx

/-- The derivative of the periodised representative vanishes at the
accumulation point (`Du = 0` on the accumulation circle). -/
theorem fderiv_mainVelocityPeriodizedRepresentative_accumulationPoint :
    fderiv ℝ mainVelocityPeriodizedRepresentative accumulationPoint = 0 :=
  fderiv_parameterizedFullGlobalPeriodizedRealSource_accumulationPoint
    globalSeedInterface.smoothingWidth mainParameterChoice.placement
    globalSeedInterface.angularSpeed globalSeedInterface.axialSpeed
    mainParameterChoice.tau mainParameterChoice.tau_nonneg

/-- **The velocity is not `C¹`,** read off the periodised representative: its
derivative is discontinuous at the accumulation point. -/
theorem not_continuousAt_fderiv_mainVelocityPeriodizedRepresentative :
    ¬ ContinuousAt (fderiv ℝ mainVelocityPeriodizedRepresentative) accumulationPoint :=
  not_continuousAt_fderiv_parameterizedFullGlobalPeriodizedRealSource
    globalSeedInterface.smoothingWidth mainParameterChoice.placement
    globalSeedInterface.angularSpeed globalSeedInterface.axialSpeed
    mainParameterChoice.tau mainParameterChoice.tau_nonneg
    seed_angularSpeed_ne_zero

/-! ## The semigroup orbit of the real datum -/

/-- **The real datum's semigroup orbit obeys `eq:main-thm-growth`** at the theorem's own
witnesses: `mainSemigroupOrbitClauses_of_mainReducedClauses`
(`FastDynamo/Dynamics/Assembly/SemigroupOrbit.lean`) at `mainVelocity`, `mainEps0`,
`mainGrowthFloor`, from the same reduced clauses `mainReducedClauses_holds` that supply
`mainPhysicalClauses_holds`. -/
theorem mainSemigroupOrbitClauses_holds :
    MainSemigroupOrbitClauses mainVelocity mainVelocity_isTransverseDivergenceFree
      mainEps0 mainGrowthFloor :=
  mainSemigroupOrbitClauses_of_mainReducedClauses mainVelocity
    mainVelocity_isTransverseDivergenceFree mainGrowthFloor_pos mainReducedClauses_holds

/-! ## The literal three-torus -/

/-- The theorem's velocity as an axially independent function on the literal
three-torus `Torus 3 = Fin 3 → UnitAddCircle`. -/
def mainLiteralVelocity : Torus 3 → R3 :=
  literalVelocity mainVelocityTorusRepresentative

/-- **The velocity is Lipschitz on the literal three-torus.** -/
theorem lipschitzWith_mainLiteralVelocity :
    LipschitzWith (2 * Real.toNNReal mainVelocityLipschitzBound) mainLiteralVelocity :=
  lipschitzWith_literalVelocity_parameterizedFullGlobalRealTorusSource
    globalSeedInterface.smoothingWidth mainParameterChoice.placement
    globalSeedInterface.angularSpeed globalSeedInterface.axialSpeed
    mainParameterChoice.tau mainParameterChoice.tau_nonneg

/-- The magnetic clauses of Theorem 1.2 on the literal three-torus: for every
`0 < ε ≤ ε₀` there are a sector `K ≠ 0`, an eigenvalue with `γ₀ ≤ Re λ`, a nonzero
amplitude `b` and a datum `B_in ∈ L²_σ(Torus 3; ℂ³)` such that

* the transported real trajectory `B(t)` in `L²(Torus 3; ℝ³)` obeys the exact norm law, never
  vanishes, and grows at least like `e^{t γ₀}`; every norm in these three clauses is the norm of
  `L²(Torus 3; ℝ³)`, the initial field appearing as the value of the trajectory at time zero;
* `B_in` is the complexification of `B(0)`;
* the orbit of `B_in` under the induction semigroup `literalInductionSemigroup` on
  `L²_σ(Torus 3; ℂ³)` — the semigroup whose growth bound is `gamma` — is the complexification
  of `B(t)` for every `t ≥ 0`.

The last clause makes `B(t)` the solution `e^{t L_{ε,u}} B_in` on the literal three-torus, at
the same triple `(K, λ, b)` as the norm law. -/
def MainLiteralTorusClauses : Prop :=
  ∀ (eps : ℝ) (heps : 0 < eps), eps ≤ mainEps0 →
    ∃ (K : ℤ) (lambda : ℂ) (b : TransverseC3H2) (Bin : literalSolenoidalSubspace),
      K ≠ 0 ∧ mainGrowthFloor ≤ lambda.re ∧ b ≠ 0 ∧
      (reducedInductionOperator mainVelocity eps K).IsEigenpair lambda b ∧
      (∀ t : ℝ,
        ‖literalRealTrajectory K lambda (transverseH2Embedding b) t‖ =
          Real.exp (t * lambda.re) *
            ‖literalRealTrajectory K lambda (transverseH2Embedding b) 0‖) ∧
      (∀ t : ℝ, literalRealTrajectory K lambda (transverseH2Embedding b) t ≠ 0) ∧
      (∀ t : ℝ, 0 ≤ t →
        Real.exp (t * mainGrowthFloor) *
            ‖literalRealTrajectory K lambda (transverseH2Embedding b) 0‖ ≤
          ‖literalRealTrajectory K lambda (transverseH2Embedding b) t‖) ∧
      (Bin : LiteralC3L2) =
        complexifyLiteralR3L2 (literalRealTrajectory K lambda (transverseH2Embedding b) 0) ∧
      (∀ t : ℝ, 0 ≤ t →
        ((literalInductionSemigroup mainVelocity mainVelocity_isTransverseDivergenceFree heps
            (Real.toNNReal t) Bin : literalSolenoidalSubspace) : LiteralC3L2) =
          complexifyLiteralR3L2 (literalRealTrajectory K lambda (transverseH2Embedding b) t))

/-- **The magnetic clauses hold on the literal three-torus.**  The triple and the datum are
those of `mainSemigroupOrbitClauses_holds`, transported by `solenoidalToLiteral`; the orbit
identity is the product-model one read through the transport, with
`toLiteralC3L2_complexifyProductR3L2` exchanging transport and complexification. -/
theorem mainLiteralTorusClauses_holds : MainLiteralTorusClauses := by
  intro eps hpos hle
  obtain ⟨K, lambda, b, Bin, hK, hfloor, hb, hpair, -, -, horbit, -, -, hphys⟩ :=
    mainSemigroupOrbitClauses_holds eps hpos hle
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hemb, -⟩ := hphys
  have hbL2 : transverseH2Embedding b ≠ 0 := by
    intro h
    exact hb (transverseH2Embedding_injective (by rw [h, map_zero]))
  have hlit : ∀ t : ℝ, 0 ≤ t →
      ((literalInductionSemigroup mainVelocity mainVelocity_isTransverseDivergenceFree hpos
          (Real.toNNReal t) (solenoidalToLiteral Bin) : literalSolenoidalSubspace) :
          LiteralC3L2) =
        complexifyLiteralR3L2 (literalRealTrajectory K lambda (transverseH2Embedding b) t) := by
    intro t ht
    rw [literalInductionSemigroup, StronglyContinuousSemigroup.congr_apply,
      LinearIsometryEquiv.symm_apply_apply, solenoidalToLiteral_apply]
    rw [show ((solenoidalInductionSemigroup mainVelocity mainVelocity_isTransverseDivergenceFree
        hpos).operator (Real.toNNReal t) Bin : ProductC3L2) = _ from horbit t ht,
      ← hemb t, toLiteralC3L2_complexifyProductR3L2]
    rfl
  refine ⟨K, lambda, b, solenoidalToLiteral Bin, hK, hfloor, hb, hpair, ?_, ?_, ?_, ?_, hlit⟩
  · intro t
    exact norm_literalRealTrajectory_eq_exp_mul_norm_zero K hK lambda
      (transverseH2Embedding b) t
  · intro t
    exact literalRealTrajectory_ne_zero K hK lambda hbL2 t
  · intro t ht
    exact literalRealTrajectory_norm_lower_bound_zero K hK lambda (transverseH2Embedding b)
      mainGrowthFloor t hfloor ht
  · have h0 := hlit 0 le_rfl
    rwa [Real.toNNReal_zero, StronglyContinuousSemigroup.apply_zero] at h0

/-! ## Proposition 7.1 at every admissible cell -/

/-- Proposition 7.1 (`prop:global-spectral-transfer`) in eigenpair form at every admissible
cell index of the parameter chain: whenever `ε / ℓ_n²` lies in the seed's diffusivity interval,
the sector `K_n` is nonzero and carries a growing eigenpair of the reduced and of the
auxiliary operator.  The paper's proposition also asserts `Γ_τ ⊂ ρ(A_{ε,K_n})`,
`Q_{ε,n} ≠ 0` and that the eigenvalue lies inside `Γ_τ`; this clause keeps only the
eigenvalue with real part at least `g_*`, lifted to three components. -/
def MainEveryAdmissibleCellClauses : Prop :=
  ∀ (eps : ℝ), 0 < eps → eps ≤ mainEps0 → ∀ n : ℕ,
    mainParameterChoice.scaleFamily.rescaledDiffusivity eps n ∈
        globalSeedInterface.parameters.interval →
      ((mainParameterChoice.scaleFamily.fourierIndex n : ℤ) ≠ 0) ∧
        ∃ (lambda : ℂ) (b : TransverseC3H2),
          mainGrowthFloor ≤ lambda.re ∧
            (reducedInductionOperator mainVelocity eps
              (mainParameterChoice.scaleFamily.fourierIndex n :
                ℤ)).IsEigenpair lambda b ∧
            (productInductionOperator mainVelocity eps).IsEigenpair lambda
              (axialLiftH2 (mainParameterChoice.scaleFamily.fourierIndex n : ℤ) b)

/-- **The every-cell eigenpair clauses hold.** -/
theorem mainEveryAdmissibleCellClauses_holds : MainEveryAdmissibleCellClauses :=
  fun _ hpos _ n hn ↦ exists_growing_eigenpair_of_admissible_index hpos n hn

/-! ## The named normalised witness -/

/-- **The paper's normalisation remark at a named witness.**  The velocity
`uNorm = mainVelocity / max (1, ‖mainVelocity‖)` lies in the closed unit ball of
`W^{1,∞}` and satisfies every physical clause with the rescaled thresholds
`M⁻¹ ε₀` and `M⁻¹ γ₀`, where `M⁻¹ = velocityNormalizer mainVelocity`. -/
theorem mainPhysicalClauses_normalizedVelocity :
    ‖normalizedVelocity mainVelocity‖ ≤ 1 ∧
      MainPhysicalClauses (normalizedVelocity mainVelocity)
        (velocityNormalizer mainVelocity * mainEps0)
        (velocityNormalizer mainVelocity * mainGrowthFloor) :=
  ⟨norm_normalizedVelocity_le_one mainVelocity,
    mainPhysicalClauses_of_mainReducedClauses
      (isTransverseDivergenceFree_normalizedVelocity mainVelocity_isTransverseDivergenceFree)
      (mul_pos (velocityNormalizer_pos mainVelocity) mainGrowthFloor_pos)
      (mainReducedClauses_smul (velocityNormalizer_pos mainVelocity) mainReducedClauses_holds)⟩

/-! ## The strengthened statement -/

/-- **The strengthened main theorem.**  Every clause of the spectral half of
the paper's Theorem 1.2 at the explicit witnesses, the growth-rate clause on the closed
interval `0 < ε ≤ ε₀` with its ceiling, `eq:main-thm-growth` for the semigroup orbit and for
every solution of the curl-form equation with the real datum,
together with the explicit formula and bounds for the constants, the every-cell form of
Proposition 7.1, the normalised form with a named witness, the qualitative
regularity of the velocity on the plane and on its periodisation, and the
transport to the literal three-torus. -/
structure MainTheoremStrengthened : Prop where
  /-- The velocity is divergence-free. -/
  velocity_isTransverseDivergenceFree : IsTransverseDivergenceFree mainVelocity
  /-- The velocity is nonzero. -/
  velocity_ne_zero : mainVelocity ≠ 0
  /-- The diffusivity threshold is positive. -/
  eps0_pos : 0 < mainEps0
  /-- The diffusivity threshold is `δ₊ / K₀²`, the paper's choice of `ε₀` in §3.2. -/
  eps0_eq :
    mainEps0 =
      globalSeedInterface.parameters.deltaPlus / (mainParameterChoice.baseIndex : ℝ) ^ 2
  /-- The growth floor is positive. -/
  growthFloor_pos : 0 < mainGrowthFloor
  /-- The growth floor is the minimum of `Re ζ` over the closed disc bounded by the seed's
  isolating circle, i.e. `Re(centre Γ) − radius Γ` (`eq:spectral-gap`). -/
  growthFloor_eq :
    mainGrowthFloor =
      globalSeedInterface.contour.center.re - globalSeedInterface.contour.radius
  /-- The growth floor retains three quarters of the certified real part `448 − (2π)²` of the
  seed eigenvalue `λ_* = κ² − N²` at `N = 2π`, `ϱ = 32`; numerically `γ₀ ≥ 288`. -/
  growthFloor_ge_three_quarters : 3 / 4 * (448 - (2 * Real.pi) ^ 2) ≤ mainGrowthFloor
  /-- The physical clauses of Theorem 1.2 at the explicit witnesses.  `semigroupOrbit`
  contains them at the triple of the semigroup orbit. -/
  physicalClauses : MainPhysicalClauses mainVelocity mainEps0 mainGrowthFloor
  /-- The growth-rate clause of `thm:main` (the per-diffusivity form of
  `eq:main-growth-conclusion`): for every `0 < ε ≤ ε₀`, the growth bound `γ(u, ε)` of the
  induction semigroup on `L²_σ(T³; ℂ³)` is at least the growth floor `γ₀`, on the interval
  on which the paper states the clause. -/
  growthRate : ∀ {ε : ℝ} (hpos : 0 < ε), ε ≤ mainEps0 →
    ((mainGrowthFloor : ℝ) : EReal) ≤
      gamma mainVelocity mainVelocity_isTransverseDivergenceFree hpos
  /-- **`eq:main-thm-growth` for "its solution"**: at every `0 < ε ≤ ε₀` the real datum
  `B_in^ε = Re V^ε` lies in `L²_σ`, is non-zero, and its orbit under the induction
  semigroup `e^{tL_{ε,u}}` on `L²_σ` — the semigroup generated by `L_{ε,u}` with domain
  `H² ∩ L²_σ`, whose growth bound is `γ(u, ε)` — is the explicit real curve
  `B^ε(t) = Re(e^{tλ_ε}V^ε)` and obeys `‖e^{tL}B_in^ε‖ = e^{t Re λ_ε} ‖B_in^ε‖` for `t ≥ 0`;
  every forward strong solution of the curl-form equation with initial value `B_in^ε` is that
  orbit, so obeys the same law and `‖B(t)‖ ≥ e^{t γ₀}‖B_in^ε‖` for `t ≥ 0`; and the same
  triple `(K_ε, λ_ε, b^ε)` satisfies `MainPhysicalClausesAt`, so the clauses of
  `physicalClauses` hold at the triple of the orbit.  This is the
  definite article in the theorem's "*its* solution"; the solution class is described in
  `FastDynamo/Dynamics/Assembly/SemigroupOrbit.lean`. -/
  semigroupOrbit :
    MainSemigroupOrbitClauses mainVelocity mainVelocity_isTransverseDivergenceFree
      mainEps0 mainGrowthFloor
  /-- The growth rate is bounded above: it is at most the stretching bound
  `‖∇⊥u‖_∞` at every positive diffusivity.  This gives `γ ≠ ⊤`; `γ ≠ ⊥` needs
  `growthRate`, which only fires for `ε ≤ ε₀`. -/
  growthRate_le : ∀ {ε : ℝ} (hpos : 0 < ε),
    gamma mainVelocity mainVelocity_isTransverseDivergenceFree hpos ≤
      ((‖transverseStretchingCoefficient mainVelocity‖ : ℝ) : EReal)
  /-- Proposition 7.1 in eigenpair form at every admissible cell index. -/
  everyAdmissibleCell : MainEveryAdmissibleCellClauses
  /-- The spectral half of the theorem also holds with a velocity of `W^{1,∞}` norm at most
  one; every clause for the normalised velocity is `MainTheoremNormalized`. -/
  normalized : MainPhysicalConclusionNormalized
  /-- The normalisation is realized by the named witness
  `normalizedVelocity mainVelocity` with the thresholds `M⁻¹ ε₀`, `M⁻¹ γ₀`. -/
  normalizedWitness :
    ‖normalizedVelocity mainVelocity‖ ≤ 1 ∧
      MainPhysicalClauses (normalizedVelocity mainVelocity)
        (velocityNormalizer mainVelocity * mainEps0)
        (velocityNormalizer mainVelocity * mainGrowthFloor)
  /-- The chart-side representative of the velocity has the paper's
  qualitative regularity. -/
  chartRepresentative_qualitative : GlobalVelocityQualitative mainVelocityChartRepresentative
  /-- The chart-side representative is Lipschitz with an explicit constant. -/
  chartRepresentative_lipschitz :
    LipschitzWith (Real.toNNReal mainVelocityLipschitzBound) mainVelocityChartRepresentative
  /-- The value of the velocity is the torus-side representative almost everywhere. -/
  value_ae_eq_torusRepresentative :
    (transverseW1InfValue mainVelocity : TransverseTorus → R3) =ᵐ[transverseMeasure]
      mainVelocityTorusRepresentative
  /-- The torus-side representative, pulled back along the quotient map, is the
  `ℤ²`-periodisation of the chart-side representative — at every point of the
  plane, the accumulation point included. -/
  torusRepresentative_eq_periodized : ∀ x : ℝ × ℝ,
    mainVelocityTorusRepresentative (transverseTorusPoint x) =
      mainVelocityPeriodizedRepresentative x
  /-- On the fundamental box the periodisation is the chart-side representative. -/
  periodized_eq_chart : ∀ x : ℝ × ℝ, x.1 ∈ Set.Ioc (0 : ℝ) 1 → x.2 ∈ Set.Ioc (0 : ℝ) 1 →
    mainVelocityPeriodizedRepresentative x = mainVelocityChartRepresentative x
  /-- The periodised representative is differentiable everywhere. -/
  periodized_differentiable : Differentiable ℝ mainVelocityPeriodizedRepresentative
  /-- The periodised representative is smooth away from the integer translates
  of the accumulation point. -/
  periodized_contDiffAt : ∀ x : ℝ × ℝ,
    (∀ k : ℤ × ℤ, x - ((k.1 : ℝ), (k.2 : ℝ)) ≠ accumulationPoint) →
      ContDiffAt ℝ (⊤ : ℕ∞) mainVelocityPeriodizedRepresentative x
  /-- The derivative of the periodised representative vanishes at the
  accumulation point. -/
  periodized_fderiv_accumulationPoint :
    fderiv ℝ mainVelocityPeriodizedRepresentative accumulationPoint = 0
  /-- The derivative of the velocity representative is discontinuous at the
  accumulation point of the torus, so the velocity is not `C¹`. -/
  periodized_not_continuousAt_fderiv :
    ¬ ContinuousAt (fderiv ℝ mainVelocityPeriodizedRepresentative) accumulationPoint
  /-- The periodised representative is Lipschitz. -/
  periodized_lipschitz :
    LipschitzWith (2 * Real.toNNReal mainVelocityLipschitzBound)
      mainVelocityPeriodizedRepresentative
  /-- The torus-side representative is Lipschitz for the quotient metric. -/
  torusRepresentative_lipschitz :
    LipschitzWith (2 * Real.toNNReal mainVelocityLipschitzBound) mainVelocityTorusRepresentative
  /-- The velocity on the literal three-torus is Lipschitz. -/
  literalVelocity_lipschitz :
    LipschitzWith (2 * Real.toNNReal mainVelocityLipschitzBound) mainLiteralVelocity
  /-- The magnetic clauses on the literal three-torus: the norm law of the transported real
  trajectory inside `L²(Torus 3; ℝ³)`, and the identification of its complexification with
  the orbit of the transported real datum under `literalInductionSemigroup`. -/
  literalTorus : MainLiteralTorusClauses

/-- **The strengthened main theorem.** -/
theorem main_theorem_strengthened : MainTheoremStrengthened where
  velocity_isTransverseDivergenceFree := mainVelocity_isTransverseDivergenceFree
  velocity_ne_zero := mainVelocity_ne_zero
  eps0_pos := mainEps0_pos
  eps0_eq := mainEps0_eq
  growthFloor_pos := mainGrowthFloor_pos
  growthFloor_eq := mainGrowthFloor_eq
  growthFloor_ge_three_quarters := mainGrowthFloor_ge_three_quarters
  physicalClauses := mainPhysicalClauses_holds
  growthRate := fun hpos hle ↦ gamma_ge_gamma0 hpos hle
  semigroupOrbit := mainSemigroupOrbitClauses_holds
  growthRate_le := fun hpos ↦ gamma_le_stretching _ _ hpos
  everyAdmissibleCell := mainEveryAdmissibleCellClauses_holds
  normalized := mainPhysicalConclusionNormalized_of_mainReducedTarget mainReducedTarget_holds
  normalizedWitness := mainPhysicalClauses_normalizedVelocity
  chartRepresentative_qualitative := mainVelocityChartRepresentative_qualitative
  chartRepresentative_lipschitz := lipschitzWith_mainVelocityChartRepresentative
  value_ae_eq_torusRepresentative := transverseW1InfValue_mainVelocity_ae
  torusRepresentative_eq_periodized :=
    mainVelocityTorusRepresentative_transverseTorusPoint_eq_periodized
  periodized_eq_chart := fun _ h1 h2 ↦ mainVelocityPeriodizedRepresentative_eq_chart h1 h2
  periodized_differentiable := differentiable_mainVelocityPeriodizedRepresentative
  periodized_contDiffAt := fun _ hx ↦ contDiffAt_mainVelocityPeriodizedRepresentative hx
  periodized_fderiv_accumulationPoint :=
    fderiv_mainVelocityPeriodizedRepresentative_accumulationPoint
  periodized_not_continuousAt_fderiv :=
    not_continuousAt_fderiv_mainVelocityPeriodizedRepresentative
  periodized_lipschitz := lipschitzWith_mainVelocityPeriodizedRepresentative
  torusRepresentative_lipschitz := lipschitzWith_mainVelocityTorusRepresentative
  literalVelocity_lipschitz := lipschitzWith_mainLiteralVelocity
  literalTorus := mainLiteralTorusClauses_holds

/-- The normalised form of the spectral half of Theorem 1.2 holds. -/
theorem mainPhysicalConclusionNormalized_holds : MainPhysicalConclusionNormalized :=
  main_theorem_strengthened.normalized

/-! ## The dynamical half of Theorem 1.2, stated -/

/-- **The Lagrangian bundle at the constructed velocity**: `prop:particle-flow` and
`cor:ideal-growth` together, at `mainLiteralVelocity`.  The velocity has a particle flow with
Lipschitz constants growing at most linearly in time (`eq:linear-flow-lipschitz`), every time
map has zero topological entropy (`prop:particle-flow`), and the ideal induction equation has
a unique, strongly continuous solution group on `L²_σ(T³; ℂ³)`, given by the Cauchy formula,
obeying the two-sided per-datum bounds of `cor:ideal-growth` and having exponential rate zero
on every non-zero datum (the last sentence of `cor:ideal-growth`).

This is *more* than the dynamical half of the theorem, which has only the entropy
clause and the operator-norm rate; that shorter statement is `MainTheoremDynamical` below,
and `MainLagrangianClauses.toMainTheoremDynamicalClauses` projects onto it.  The name follows
the blueprint node `prop:main-lagrangian`.

**Proved downstream, not here.**  `mainLiteralVelocity` is defined in this module and the
proof imports it, so the proof lives in `FastDynamo/Dynamics/MainLagrangianClauses.lean`:
`mainTheoremLagrangian_holds` is this proposition with no hypothesis, obtained from
`mainLagrangianClauses_literalVelocity` at the parameters of `mainParameterChoice`.  The flow is
`FastDynamo/Dynamics/Flow/*` and the ideal group `FastDynamo/Dynamics/Ideal/*`;
`FastDynamo/Dynamics/ParticleFlow.lean` states the clauses, with the weak form of the ideal
equation from `FastDynamo/Dynamics/IdealWeakForm.lean` (the fields `solutionGroup` and `unique`
of `IsIdealInductionGroup`).  The variational equation `eq:flow-variational-equation` is not a
clause of the bundle; it is proved for the constructed flow in
`FastDynamo/Dynamics/Flow/VariationalEquation.lean`.  The proofs are the blueprint nodes
`prop:particle-flow` and `cor:ideal-growth` of `blueprint/src/chapters/particle.tex`. -/
def MainTheoremLagrangian : Prop := MainLagrangianClauses mainLiteralVelocity

/-- **The dynamical half of Theorem 1.2 at the constructed velocity**
(`thm:main`, its last sentence):

```
  h_top(Φ_t) = 0   (t ∈ ℝ),        lim_{t → ∞} t⁻¹ log ‖𝒯₀(t)‖_{L²_σ → L²_σ} = 0 ,
```

for the particle flow `Φ` of `mainLiteralVelocity` and the ideal induction solution group
`𝒯₀` on `L²_σ(T³)`.  These two clauses are all the theorem asserts about the
dynamics: the Lipschitz bound and the two-sided per-datum bounds are `prop:particle-flow`
and `cor:ideal-growth`, outside the theorem, kept here as `MainTheoremLagrangian`.

**Proved downstream, not here** (the proof imports this module): `mainTheoremDynamical_holds`
(`FastDynamo/Dynamics/MainLagrangianClauses.lean`) is this proposition with no hypothesis,
obtained from `mainTheoremLagrangian_holds` by
`MainLagrangianClauses.toMainTheoremDynamicalClauses`. -/
def MainTheoremDynamical : Prop := MainTheoremDynamicalClauses mainLiteralVelocity

/-- **Theorem 1.2 in full** (`thm:main`):
the strengthened spectral, real-datum and growth-rate half, which `main_theorem_strengthened`
proves, together with the theorem's two dynamical clauses and — as a third
field, beyond what the theorem states — the Lagrangian bundle they are projected from.  Every
field is inhabited in `FastDynamo/Dynamics/MainLagrangianClauses.lean`, by
`mainTheoremComplete_holds`. -/
structure MainTheoremComplete : Prop where
  /-- The spectral half, `main_theorem_strengthened`. -/
  strengthened : MainTheoremStrengthened
  /-- The two dynamical clauses of the theorem (its last sentence), proved by
  `mainTheoremDynamical_holds`. -/
  dynamical : MainTheoremDynamical
  /-- `prop:particle-flow` and `cor:ideal-growth` at the same velocity — including the
  Lipschitz bound and the two-sided per-datum bounds, which are not clauses of the theorem —
  proved by `mainTheoremLagrangian_holds`. -/
  lagrangian : MainTheoremLagrangian

/-- Theorem 1.2 in full follows from the Lagrangian bundle alone: every other
clause of the theorem is proved in this module, and the theorem's own dynamical clauses are a
projection of the bundle (`MainLagrangianClauses.toMainTheoremDynamicalClauses`).  The
hypothesis is discharged in `FastDynamo/Dynamics/MainLagrangianClauses.lean`
(`mainTheoremComplete_holds`). -/
theorem mainTheoremComplete_of_lagrangian (h : MainTheoremLagrangian) :
    MainTheoremComplete :=
  ⟨main_theorem_strengthened, MainLagrangianClauses.toMainTheoremDynamicalClauses h, h⟩

/-- **The ideal–resistive gap**

```
  γ_id(u) = 0 < γ₀ ≤ liminf_{ε ↓ 0} γ(u, ε).
```

The paper states this chain as no single result, but every member is a statement of the
paper, and all three are returned here.

* The left-hand equality `γ_id(u) = 0` is `HasVanishingIdealOperatorGrowthRate
  mainLiteralVelocity`, the rate of the **operator norm** `‖𝒯₀(t)‖_{L²_σ→L²_σ}`.  It is the
  second dynamical clause of `thm:main` and `eq:zero-ideal-growth` of `cor:ideal-growth`.
  It is derived from the two-sided per-datum bounds of the Lagrangian hypothesis by
  `MainLagrangianClauses.hasVanishingIdealOperatorGrowthRate`, which is the last step of the
  paper's proof of `cor:ideal-growth`.  This is the only use this statement makes of the
  hypothesis.  The hypothesis is *not* an open assumption: it is discharged in
  `FastDynamo/Dynamics/MainLagrangianClauses.lean`, where `ideal_resistive_gap_holds` is this
  chain with no hypothesis at all.  It stays a hypothesis here only because this module
  defines `mainLiteralVelocity` and the proof imports it, so the proof cannot be imported here
  without a cycle.
* The middle inequality is `mainGrowthFloor_pos`, the constant `γ₀ > 0` of `thm:main`.
* The right-hand inequality is `eq:main-growth-conclusion`,
  `mainGrowthFloor_le_liminf_gammaOf`, taken along `𝓝[>] 0` of the total extension `gammaOf`
  of `γ(u, ·)`.

The sharper per-diffusivity form of the last member — `γ₀ ≤ γ(u, ε)` at *every* `0 < ε ≤ ε₀`,
not only in the limit — is `ideal_resistive_gap_at_diffusivity`. -/
theorem ideal_resistive_gap (h : MainTheoremLagrangian) :
    HasVanishingIdealOperatorGrowthRate mainLiteralVelocity ∧
      ((0 : ℝ) : EReal) < ((mainGrowthFloor : ℝ) : EReal) ∧
        ((mainGrowthFloor : ℝ) : EReal) ≤
          Filter.liminf (gammaOf mainVelocity mainVelocity_isTransverseDivergenceFree)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
  ⟨MainLagrangianClauses.hasVanishingIdealOperatorGrowthRate h,
    by exact_mod_cast mainGrowthFloor_pos, mainGrowthFloor_le_liminf_gammaOf⟩

/-- **The ideal–resistive gap at a fixed diffusivity**, the per-datum packaging: the ideal
rate of every non-zero datum vanishes (the last sentence of `cor:ideal-growth`), the growth
floor is positive, and `γ₀ ≤ γ(u, ε)` holds at the given `0 < ε ≤ ε₀` rather than only in
the limit `ε ↓ 0`; this third member is strictly stronger than the `liminf` of
`ideal_resistive_gap`. -/
theorem ideal_resistive_gap_at_diffusivity (h : MainTheoremLagrangian) {ε : ℝ} (hpos : 0 < ε)
    (hle : ε ≤ mainEps0) :
    HasVanishingIdealGrowthRate mainLiteralVelocity ∧
      ((0 : ℝ) : EReal) < ((mainGrowthFloor : ℝ) : EReal) ∧
        ((mainGrowthFloor : ℝ) : EReal) ≤
          gamma mainVelocity mainVelocity_isTransverseDivergenceFree hpos :=
  ⟨MainLagrangianClauses.hasVanishingIdealGrowthRate h,
    by exact_mod_cast mainGrowthFloor_pos, gamma_ge_gamma0 hpos hle⟩

end

end FastDynamo
