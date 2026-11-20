/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.LiteralThreeTorus
public import LeanPool.FastDynamo.Dynamics.Assembly.ProductSemigroup

/-!
# The paper's growth rate `γ(u, ε)` on `L²_σ(T³;ℂ³)`, and `γ ≥ γ₀`

`FastDynamo/Dynamics/Assembly/ProductSemigroup.lean` constructs the induction semigroup on the
solenoidal subspace of the *product* model
`ProductC3L2 = L²(T² × T¹; ℂ³)`; the paper's state space is `L²_σ(T³; ℂ³)` on the literal
three-torus.  The two are related by the surjective linear isometry
`toLiteralC3L2 : ProductC3L2 ≃ₗᵢ[ℂ] LiteralC3L2` of
`FastDynamo/Analysis/LiteralThreeTorus.lean`, which transports the solenoidal subspace, the
semigroup, and — because growth bounds are defined from operator norms alone — the growth rate
itself, exactly.

## Contents

* **The literal solenoidal subspace.**  `literalSolenoidalSubspace` is the image of
  `productSolenoidalSubspace` under the transport; it is closed, hence a Hilbert space
  (`isClosed_literalSolenoidalSubspace` and the `CompleteSpace` instance), which is what makes
  the operator norm `‖·‖_{L²_σ → L²_σ}` well typed.  `solenoidalToLiteral` is the induced
  surjective linear isometry between the two solenoidal subspaces.
* **The semigroup and the growth rate.**  `literalInductionSemigroup` is the transported
  semigroup, `gamma` its growth bound — the Lean value of the paper's `γ(u, ε)`.  Its
  ceiling is `gamma_le_stretching`.
* **The closing theorem.**  `gamma_ge_gamma0` is the growth-rate clause of `thm:main` (whose
  `liminf` form is `eq:main-growth-conclusion`): for every `0 < ε ≤ ε₀` the growth rate at the
  constructed velocity is at least `γ₀`, the interval on which the paper states the clause.  The
  route has the shape of the paper's own proof of `thm:main` — an exact exponential orbit law
  divided by the initial norm — read at the *complex* eigenmode `V^ε` where the paper reads it at
  the real datum `B_in^ε`; the two give the same inequality, `‖V^ε‖ ≠ 0` being part of
  `DomainOperator.IsEigenpair`.  The extra Lean-side obligation that the eigenfunction lie in the
  state space is discharged by the auxiliary solenoidality theorem of
  `FastDynamo/Finish/RealSolution.lean`, a result of the formalisation that the paper does not
  state.  The literal route at the real datum is `FastDynamo/Dynamics/Assembly/SemigroupOrbit.lean`.
  `mainGrowthFloor_le_gamma_le_stretching` packages both bounds, and `gamma_ne_bot`, `gamma_ne_top`
  record that `γ` is a real quantity rather than an infinity.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-! ## The solenoidal subspace of the literal three-torus -/

/-- `L²_σ(T³;ℂ³)`: the solenoidal subspace of the literal three-torus model, the image of
`productSolenoidalSubspace` under the isometric transport `toLiteralC3L2`.

So `L²_σ(T³)` is *defined here by isometric transport* from the Fourier-defined product
solenoidal subspace of `FastDynamo/Dynamics/Assembly/SolenoidalSubspace.lean`.  The paper
defines `L²_σ(T³)` directly as the divergence-free fields in `L²(T³;ℂ³)` (§1.1).  On the
literal model the subspace is characterised by the distributional divergence tested against
the characters `e_m`: `B ∈ literalSolenoidalSubspace` if and only if
`∑_{i<3} 2πi mᵢ ⟪e_m, Bᵢ⟫ = 0` for every `m ∈ ℤ³`
(`sum_inner_flatTorus3FourierBasis_eq_zero` and its converse
`mem_literalSolenoidalSubspace_of_sum_inner_eq_zero`, in `FastDynamo/Dynamics/Ideal/`), and its
fields are orthogonal to the gradient of every periodic function with `C¹` lift
(`inner_gradient_eq_zero_of_mem_literalSolenoidalSubspace`).  No single statement
`literalSolenoidalSubspace = {B : Div B = 0}` with `Div` defined on `Torus 3` is made. -/
def literalSolenoidalSubspace : Submodule ℂ LiteralC3L2 :=
  productSolenoidalSubspace.map (toLiteralC3L2 : ProductC3L2 →ₗ[ℂ] LiteralC3L2)

/-- The literal solenoidal subspace is closed: it is the preimage of the closed subspace
`productSolenoidalSubspace` under the continuous inverse transport. -/
theorem isClosed_literalSolenoidalSubspace :
    IsClosed (literalSolenoidalSubspace : Set LiteralC3L2) := by
  have hset : (literalSolenoidalSubspace : Set LiteralC3L2) =
      toLiteralC3L2.symm ⁻¹' (productSolenoidalSubspace : Set ProductC3L2) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨toLiteralC3L2.symm y, hy, by simp⟩
  rw [hset]
  exact isClosed_productSolenoidalSubspace.preimage toLiteralC3L2.symm.continuous

/-- The literal solenoidal subspace is a Hilbert space in its own right.  This is what makes
the operator norm `‖·‖_{L²_σ → L²_σ}` of the paper's growth rate well typed. -/
instance literalSolenoidalSubspaceCompleteSpace : CompleteSpace literalSolenoidalSubspace :=
  isClosed_literalSolenoidalSubspace.completeSpace_coe

/-- The isometric transport of the solenoidal subspace: `toLiteralC3L2` restricts to a
surjective linear isometry from `productSolenoidalSubspace` onto its image. -/
def solenoidalToLiteral : productSolenoidalSubspace ≃ₗᵢ[ℂ] literalSolenoidalSubspace :=
  LinearIsometryEquiv.submoduleMap productSolenoidalSubspace toLiteralC3L2

/-- The transport of the solenoidal subspace is the ambient transport, read through the two
inclusions.  This is definitional. -/
@[simp] theorem solenoidalToLiteral_apply (x : productSolenoidalSubspace) :
    (solenoidalToLiteral x : LiteralC3L2) = toLiteralC3L2 (x : ProductC3L2) :=
  rfl

/-! ## Non-vacuity of the state space -/

/--
**`L²_σ(T³;ℂ³)` is not the zero space.**  It contains a non-zero field.

This is what makes the ideal clauses of Theorem 1.2 non-vacuous.  Every clause of the dynamical
half — the Cauchy formula `IsIdealInductionGroup.cauchy`, the group laws, the strong continuity,
the two-sided per-datum bounds of `cor:ideal-growth` and the vanishing per-datum rate (its last
sentence) — is quantified over
`B : literalSolenoidalSubspace` and would hold verbatim on a trivial space, so the statement
below is the one that rules that reading out.

The witness is the spectral half's own: the unstable eigenfunction `V^ε = e^{2πiKx₃} b^ε` of
`gamma_ge_gamma0` is non-zero by the definition of `DomainOperator.IsEigenpair` (whose first field
is `A.embedding b ≠ 0`), lies in `productSolenoidalSubspace` by the auxiliary solenoidality
theorem `productH2Embedding_mem_productSolenoidalSubspace_of_isEigenpair`, and the transport
`toLiteralC3L2` is a linear isometry equivalence, hence injective.  The diffusivity is immaterial;
`mainEps0` is taken because `mainEps0_pos` and `le_rfl` discharge the two hypotheses of
`mainReducedClauses_holds` on the spot.
-/
theorem exists_ne_zero_literalSolenoidalSubspace : ∃ B : literalSolenoidalSubspace, B ≠ 0 := by
  obtain ⟨K, lam, b, -, hfloor, hpair⟩ := mainReducedClauses_holds mainEps0 mainEps0_pos le_rfl
  have hprod : (productInductionOperator mainVelocity mainEps0).IsEigenpair lam
      (axialLiftH2 K b) :=
    (productInductionEigenpair_axialLiftH2_iff_reduced mainVelocity mainEps0 K lam b).2 hpair
  have hre : 0 < lam.re := lt_of_lt_of_le mainGrowthFloor_pos hfloor
  have hmem : productH2Embedding (axialLiftH2 K b) ∈ productSolenoidalSubspace :=
    productH2Embedding_mem_productSolenoidalSubspace_of_isEigenpair mainVelocity
      mainVelocity_isTransverseDivergenceFree mainEps0_pos.le hre hprod
  refine ⟨⟨toLiteralC3L2 (productH2Embedding (axialLiftH2 K b)),
    ⟨productH2Embedding (axialLiftH2 K b), hmem, rfl⟩⟩, ?_⟩
  have hne : productH2Embedding (axialLiftH2 K b) ≠ 0 := hprod.1
  simpa [Submodule.mk_eq_zero, map_eq_zero_iff _ toLiteralC3L2.injective] using hne

/-- **The state space of the ideal clauses is non-trivial**, the instance form of
`exists_ne_zero_literalSolenoidalSubspace`.  With it, `B ≠ 0` in the clauses of
`MainLagrangianClauses` is a satisfiable hypothesis rather than an empty one. -/
instance literalSolenoidalSubspaceNontrivial : Nontrivial literalSolenoidalSubspace :=
  let ⟨B, hB⟩ := exists_ne_zero_literalSolenoidalSubspace
  ⟨B, 0, hB⟩

/-! ## The induction semigroup on `L²_σ(T³;ℂ³)` -/

section Transport

variable (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u) {ε : ℝ} (hε : 0 < ε)

/--
**The induction semigroup `e^{t L_{ε,u}}` on `L²_σ(T³;ℂ³)`.**  The solenoidal induction
semigroup of `FastDynamo/Dynamics/Assembly/ProductSemigroup.lean`, conjugated by the isometric
transport `solenoidalToLiteral` to the literal three-torus.

Conjugation by a surjective linear isometry changes no operator norm
(`StronglyContinuousSemigroup.norm_congr`), so this is a change of model and not a change of
quantity.
-/
def literalInductionSemigroup : StronglyContinuousSemigroup literalSolenoidalSubspace :=
  (solenoidalInductionSemigroup u hu hε).congr solenoidalToLiteral

/-- The transported semigroup obeys the same exponential bound
`‖S t‖ ≤ exp (‖∇⊥ u‖_∞ t)` as the untransported one. -/
theorem norm_literalInductionSemigroup_le (t : NNReal) :
    ‖(literalInductionSemigroup u hu hε).operator t‖ ≤
      Real.exp (‖transverseStretchingCoefficient u‖ * (t : ℝ)) :=
  ((solenoidalInductionSemigroup u hu hε).norm_congr solenoidalToLiteral t).trans_le
    (norm_solenoidalInductionSemigroup_le u hu hε t)

/-- The growth bound is an isometric invariant, so the transport to the literal three-torus
changes it by nothing at all.  This is `StronglyContinuousSemigroup.growthBound_congr`. -/
theorem growthBound_literalInductionSemigroup :
    (literalInductionSemigroup u hu hε).growthBound =
      (solenoidalInductionSemigroup u hu hε).growthBound :=
  (solenoidalInductionSemigroup u hu hε).growthBound_congr solenoidalToLiteral

/-! ## The growth rate -/

/--
**The paper's maximal growth rate** `γ(u, ε)` (`eq:semigroup-growth-rate`): the
exponential growth rate of `‖e^{t L_{ε,u}}‖_{L²_σ → L²_σ}`.

**Which semigroup.**  `literalInductionSemigroup u hu hε` is the isometric transport to the
literal three-torus of `solenoidalInductionSemigroup u hu hε`, and that semigroup is the
`C₀`-semigroup on `L²_σ` generated by the induction operator `L_{ε,u}` with domain `H² ∩ L²_σ`
(`FastDynamo/Dynamics/Assembly/SolenoidalGenerator.lean`): its generator is
`solenoidalInductionOperator u hu ε` (`generator_solenoidalInductionSemigroup`), whose value at
a divergence-free `H²` field `B`, embedded in `H⁻²`, is the curl form
`curl (u × B) + ε Δ B` of `eq:physical-generator`
(`productL2ToHMinus2_generator_solenoidalInductionSemigroup`), and every `C₀`-semigroup on
`L²_σ` with that generator is this one (`eq_solenoidalInductionSemigroup_of_generator_eq`,
`gamma_eq_growthBound_of_generator_eq`).  The semigroup is constructed as the restriction to
the invariant subspace `L²_σ` of the Hille–Yosida semigroup of the auxiliary operator
`productInductionOperator u ε` on the product `L²` space; the paper generates it directly on
`L²_σ` by perturbing `εΔ` (`lem:semigroup-spectral-growth`, Engel–Nagel III.2.10).

**A limit, and the spectral bound.**  `FastDynamo.StronglyContinuousSemigroup.growthBound` is
defined as the `limsup` in `EReal` of `t⁻¹ log ‖S t‖`; for `gamma` it is a limit and a real
number, as the paper asserts after `eq:semigroup-growth-rate`: `gamma_tendsto`
(`FastDynamo/Dynamics/Assembly/MainGrowthRateLimit.lean`) for the convergence in `[−∞, ∞)`,
and `gamma_eq_lim` (`FastDynamo/Dynamics/Assembly/InductionMeanConservation.lean`) for a real
limit `L` with `0 ≤ L ≤ ‖∇⊥ u‖_∞`.  It is the spectral bound,
`γ(u, ε) = sup {Re λ : λ ∈ σ(L_{ε,u})}` (`eq:growth-rate-spectral-bound`,
`gamma_eq_iSup_re_spectrum`), attained at an eigenvalue (`exists_eigenvalue_re_eq_gamma`); the
whole of `lem:semigroup-spectral-growth` is `SemigroupSpectralGrowth`
(`FastDynamo/Dynamics/Assembly/SemigroupSpectralGrowth.lean`).

**Model.**  The torus is the product model `T² × T`, transported isometrically to the literal
three-torus, and the velocity is axially independent (`TransverseRealW1Inf`); the literal
`L²_σ(T³)` is the transported product solenoidal subspace (`literalSolenoidalSubspace`).
Restricting to `L²_σ` matters: passing to an invariant subspace can strictly lower a growth
bound.
-/
def gamma : EReal := (literalInductionSemigroup u hu hε).growthBound

/--
**The ceiling.**  The growth rate never exceeds the `L^∞` norm of the transverse velocity
gradient, `γ(u, ε) ≤ ‖∇⊥ u‖_∞`, uniformly in the diffusivity.

The constant is the fixed-sector Hille–Yosida constant `M_u`, which the sector assembly carried
unchanged to the all-frequency operator; the two restrictions — to `L²_σ` and to the literal
model — can only decrease it, respectively leave it unchanged.
-/
theorem gamma_le_stretching :
    gamma u hu hε ≤ ((‖transverseStretchingCoefficient u‖ : ℝ) : EReal) :=
  (growthBound_literalInductionSemigroup u hu hε).trans_le
    (growthBound_solenoidalInductionSemigroup_le u hu hε)

/-- The growth rate is finite above: it is bounded by the real number `‖∇⊥ u‖_∞`. -/
theorem gamma_ne_top : gamma u hu hε ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top _) (gamma_le_stretching u hu hε)

end Transport

/-! ## The closing theorem -/

/--
**The growth-rate clause of `thm:main`** (whose `liminf` form is
`eq:main-growth-conclusion`).  At the explicitly constructed velocity
`mainVelocity`, for every diffusivity `0 < ε ≤ ε₀`, the paper's growth rate is at least
the `ε`-independent floor `γ₀`:

`γ(mainVelocity, ε) ≥ mainGrowthFloor`.

The paper states the clause for the same interval `0 < ε ≤ ε₀`, and it is what
`MainTheoremStrengthened.growthRate` and `ideal_resistive_gap_at_diffusivity` carry.

The proof has the shape of the paper's own proof of `thm:main` (an exact exponential orbit law
divided by the initial norm), read at the complex eigenmode rather than at the real datum:
`mainReducedClauses_holds` supplies, in a nonzero axial sector
`K`, a reduced eigenpair `(λ_ε, b^ε)` with `γ₀ ≤ Re λ_ε`;
`productInductionEigenpair_axialLiftH2_iff_reduced` promotes it to an eigenpair of the
all-frequency operator at the axial lift `V^ε = e^{2πiKx₃} b^ε`; `mainGrowthFloor_pos` makes
`Re λ_ε` positive, so `productH2Embedding_mem_productSolenoidalSubspace_of_isEigenpair` (the
auxiliary solenoidality theorem) puts `V^ε` inside the state space `L²_σ`; and
`re_le_growthBound_solenoidalInductionSemigroup_of_eigenpair` converts the eigenvalue into a
lower bound for the growth bound of the semigroup *on that subspace*, which
`growthBound_literalInductionSemigroup` identifies with `γ`.
-/
theorem gamma_ge_gamma0 {ε : ℝ} (hpos : 0 < ε) (hle : ε ≤ mainEps0) :
    ((mainGrowthFloor : ℝ) : EReal) ≤
      gamma mainVelocity mainVelocity_isTransverseDivergenceFree hpos := by
  obtain ⟨K, lam, b, -, hfloor, hpair⟩ := mainReducedClauses_holds ε hpos hle
  have hprod : (productInductionOperator mainVelocity ε).IsEigenpair lam (axialLiftH2 K b) :=
    (productInductionEigenpair_axialLiftH2_iff_reduced mainVelocity ε K lam b).2 hpair
  have hre : 0 < lam.re := lt_of_lt_of_le mainGrowthFloor_pos hfloor
  have hmem : productH2Embedding (axialLiftH2 K b) ∈ productSolenoidalSubspace :=
    productH2Embedding_mem_productSolenoidalSubspace_of_isEigenpair mainVelocity
      mainVelocity_isTransverseDivergenceFree hpos.le hre hprod
  refine le_trans (EReal.coe_le_coe_iff.2 hfloor) ?_
  calc (lam.re : EReal)
      ≤ (solenoidalInductionSemigroup mainVelocity
          mainVelocity_isTransverseDivergenceFree hpos).growthBound :=
        re_le_growthBound_solenoidalInductionSemigroup_of_eigenpair mainVelocity
          mainVelocity_isTransverseDivergenceFree hpos hprod hmem
    _ = gamma mainVelocity mainVelocity_isTransverseDivergenceFree hpos :=
        (growthBound_literalInductionSemigroup mainVelocity
          mainVelocity_isTransverseDivergenceFree hpos).symm

/--
**The sandwich.**  For every `0 < ε ≤ ε₀` the paper's growth rate at the constructed
velocity lies between the two explicit real constants of the main theorem,

`mainGrowthFloor ≤ γ(mainVelocity, ε) ≤ ‖∇⊥ mainVelocity‖_∞`.

The left inequality is `gamma_ge_gamma0`, the spectral half of Theorem 1.2 (`thm:main`) read
through the semigroup; the right one is `gamma_le_stretching`, the energy competition.
-/
theorem mainGrowthFloor_le_gamma_le_stretching {ε : ℝ} (hpos : 0 < ε) (hle : ε ≤ mainEps0) :
    ((mainGrowthFloor : ℝ) : EReal) ≤
        gamma mainVelocity mainVelocity_isTransverseDivergenceFree hpos ∧
      gamma mainVelocity mainVelocity_isTransverseDivergenceFree hpos ≤
        ((‖transverseStretchingCoefficient mainVelocity‖ : ℝ) : EReal) :=
  ⟨gamma_ge_gamma0 hpos hle,
    gamma_le_stretching mainVelocity mainVelocity_isTransverseDivergenceFree hpos⟩

/-! ## The growth rate as a total function of the diffusivity -/

/-- **The growth rate as a total function of `ε`.**  `gamma` carries the positivity proof
`0 < ε` as an argument, so it cannot be fed to a filter limit in `ε`.  This is the same
quantity, extended by `0` on `ε ≤ 0` so that it is a function `ℝ → EReal`; only its
values on `(0, ∞)` are ever read. -/
def gammaOf (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u) (ε : ℝ) : EReal :=
  if hε : 0 < ε then gamma u hu hε else 0

/-- On `(0, ∞)` the total extension is the paper's growth rate. -/
theorem gammaOf_eq_gamma (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u) {ε : ℝ}
    (hε : 0 < ε) : gammaOf u hu ε = gamma u hu hε :=
  dite_eq_left hε

/-- **`eq:main-growth-conclusion`**: "In particular, `liminf_{ε ↓ 0} γ(u, ε) ≥ γ₀`".  It is
the paper's own conclusion, weaker than the per-diffusivity bound `gamma_ge_gamma0` which holds
at every `0 < ε ≤ ε₀`, and is recorded because it is the form in which the paper defines a fast
dynamo (§1.1).  The `liminf` is taken along `𝓝[>] 0`, the filter of the paper's `ε ↓ 0`. -/
theorem mainGrowthFloor_le_liminf_gammaOf :
    ((mainGrowthFloor : ℝ) : EReal) ≤
      Filter.liminf (gammaOf mainVelocity mainVelocity_isTransverseDivergenceFree)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
  have hev : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ((mainGrowthFloor : ℝ) : EReal) ≤
        gammaOf mainVelocity mainVelocity_isTransverseDivergenceFree ε := by
    filter_upwards [Ioo_mem_nhdsGT mainEps0_pos] with ε hε
    rw [gammaOf_eq_gamma _ _ hε.1]
    exact gamma_ge_gamma0 hε.1 hε.2.le
  exact Filter.le_liminf_of_le (by isBoundedDefault) hev

/-- At the constructed velocity the growth rate is finite below as well: it is bounded from
below by the positive real number `mainGrowthFloor`.  With `gamma_ne_top` this pins `γ` to a
real value. -/
theorem gamma_ne_bot {ε : ℝ} (hpos : 0 < ε) (hle : ε ≤ mainEps0) :
    gamma mainVelocity mainVelocity_isTransverseDivergenceFree hpos ≠ ⊥ := by
  intro hbot
  have hfloor := gamma_ge_gamma0 hpos hle
  rw [hbot, le_bot_iff] at hfloor
  exact EReal.coe_ne_bot mainGrowthFloor hfloor

end

end FastDynamo
