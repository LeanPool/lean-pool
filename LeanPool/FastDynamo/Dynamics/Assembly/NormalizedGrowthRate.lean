/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.Assembly.MainGrowthRate
public import LeanPool.FastDynamo.Dynamics.Assembly.SemigroupOrbit
public import LeanPool.FastDynamo.Dynamics.SemigroupTimeRescaling
public import LeanPool.FastDynamo.Operator.ReducedInductionScaling

/-!
# The growth rate of the normalised velocity

Remark 1.6 of the paper (the remark after `rem:scope-intro`) normalises the velocity: with
`M = max {1, ‖u‖_{W^{1,∞}}}` and `uNorm = u / M`,

```
  L_{ε,uNorm} = M⁻¹ L_{Mε,u},        γ(uNorm, ε) = M⁻¹ γ(u, Mε),
```

so the growth-rate clause of `thm:main` holds for `uNorm` with the threshold `ε₀ / M` and the
floor `γ₀ / M`.  This module proves both identities for the Lean objects — the auxiliary
all-frequency action `productInductionAction` and the growth bound `gamma` of
`literalInductionSemigroup` — and the resulting clauses at the constructed velocity.

## Contents

* `productInductionAction_smul`: `A_{c ε, c u} = c · A_{ε, u}` for real `c`, and its
  normalised form `productInductionAction_normalizedVelocity`, the first display of the remark.
* `productInductionSemigroup_smul`, `solenoidalInductionSemigroup_smul`,
  `literalInductionSemigroup_smul`: for `c > 0` the induction semigroup of `c u` at diffusivity
  `c ε` is the semigroup of `u` at diffusivity `ε` run at time `c t`.  The time-rescaled
  semigroup realizes the operator `c A_{ε,u} = A_{cε,cu}`
  (`DomainOperatorSemigroupRealization.timeRescale`), and no other semigroup does
  (`productInductionSemigroup_unique`); the solenoidal subspace does not depend on the velocity,
  so the identity passes to the restriction and to its transport to the literal torus.
* `literalInductionSemigroup_normalizedVelocity` and `gamma_normalizedVelocity`: the
  semigroup of `uNorm` at `ε` is that of `u` at `M ε` run at time `M⁻¹ t`, and
  `γ(uNorm, ε) = M⁻¹ γ(u, M ε)`, the second display of the remark, from
  `StronglyContinuousSemigroup.growthBound_timeRescale`.
* `normalizedGrowthFloor_le_gamma`, `normalizedGrowthFloor_le_liminf_gammaOf`: the growth-rate
  clause of `thm:main` and `eq:main-growth-conclusion` for `normalizedVelocity mainVelocity`
  with `M⁻¹ ε₀` and `M⁻¹ γ₀`, deduced from `gamma_ge_gamma0` through the identity.
* `mainSemigroupOrbitClauses_normalizedVelocity`: `eq:main-thm-growth` for the semigroup orbit
  of the real datum and for every solution of the curl-form equation with that datum, at the
  normalised velocity.

The norm in `M` is the norm of `TransverseRealW1Inf`, `max(‖u‖_∞, ‖∂₁u‖_∞, ‖∂₂u‖_∞)`; the
paper does not fix a `W^{1,∞}` norm, and the identities hold for any `M > 0`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-! ## Homogeneity of the all-frequency action -/

/-- The transverse transport term `∑_{j<2} u_j ∂_j B` is homogeneous of degree one in the
velocity. -/
theorem productInductionTransverseTransport_smul (c : ℝ) (u : TransverseRealW1Inf) :
    productInductionTransverseTransport (c • u) =
      (c : ℂ) • productInductionTransverseTransport u := by
  rw [productInductionTransverseTransport, productInductionTransverseTransport,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [transverseW1InfComplexValueCoordLInf_smul, LinearIsometry.map_smul,
    ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_comp]

/-- The axial transport term `u₃ ∂₃ B` is homogeneous of degree one in the velocity. -/
theorem productInductionAxialTransport_smul (c : ℝ) (u : TransverseRealW1Inf) :
    productInductionAxialTransport (c • u) = (c : ℂ) • productInductionAxialTransport u := by
  rw [productInductionAxialTransport, productInductionAxialTransport,
    transverseW1InfComplexValueCoordLInf_smul, LinearIsometry.map_smul,
    ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_comp]

/-- The stretching term `∑_{j<2} B_j ∂_j u` is homogeneous of degree one in the velocity. -/
theorem productInductionStretching_smul (c : ℝ) (u : TransverseRealW1Inf) :
    productInductionStretching (c • u) = (c : ℂ) • productInductionStretching u := by
  rw [productInductionStretching, productInductionStretching, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [transverseW1InfComplexDerivLInf_smul, LinearIsometry.map_smul,
    ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_comp]

/-- The module identity `(a b) D − a T − a X + a S = a (b D − T − X + S)` behind
`productInductionAction_smul`, stated for an abstract module so that it is checked once. -/
theorem mul_smul_sub_sub_add {M : Type*} [AddCommGroup M] [Module ℂ M] (a b : ℂ)
    (D T X S : M) : (a * b) • D - a • T - a • X + a • S = a • (b • D - T - X + S) := by
  module

/-- **Homogeneity of the all-frequency induction action.**  For a real `c`, replacing the
velocity `u` by `c • u` and the diffusivity `ε` by `c ε` multiplies the action by `c`: the
diffusion term is linear in `ε`, the transport and stretching terms are `ℝ`-linear in `u`. -/
theorem productInductionAction_smul (c : ℝ) (u : TransverseRealW1Inf) (ε : ℝ) :
    productInductionAction (c • u) (c * ε) = (c : ℂ) • productInductionAction u ε := by
  have hscaled : productInductionAction (c • u) (c * ε) =
      ((c * ε : ℝ) : ℂ) • productInductionDiffusion -
        productInductionTransverseTransport (c • u) -
          productInductionAxialTransport (c • u) + productInductionStretching (c • u) :=
    rfl
  have hplain : productInductionAction u ε =
      (ε : ℂ) • productInductionDiffusion - productInductionTransverseTransport u -
        productInductionAxialTransport u + productInductionStretching u :=
    rfl
  rw [hscaled, hplain]
  simp only [productInductionTransverseTransport_smul, productInductionAxialTransport_smul,
    productInductionStretching_smul]
  rw [Complex.ofReal_mul]
  exact mul_smul_sub_sub_add (M := ProductC3H2 →L[ℂ] ProductC3L2) _ _ _ _ _ _

/-- `M⁻¹ (M ε) = ε` for the normalising factor `M⁻¹ = velocityNormalizer u`. -/
theorem velocityNormalizer_mul_max_mul (u : TransverseRealW1Inf) (ε : ℝ) :
    velocityNormalizer u * (max 1 ‖u‖ * ε) = ε := by
  have hM : max 1 ‖u‖ ≠ 0 := (max_one_norm_pos u).ne'
  rw [velocityNormalizer]
  field_simp

/-- **`L_{ε,uNorm} = M⁻¹ L_{Mε,u}`** (the first display of Remark 1.6), for the auxiliary
all-frequency action, with `uNorm = normalizedVelocity u`, `M = max 1 ‖u‖` and
`M⁻¹ = velocityNormalizer u`. -/
theorem productInductionAction_normalizedVelocity (u : TransverseRealW1Inf) (ε : ℝ) :
    productInductionAction (normalizedVelocity u) ε =
      (velocityNormalizer u : ℂ) • productInductionAction u (max 1 ‖u‖ * ε) := by
  rw [← productInductionAction_smul, velocityNormalizer_mul_max_mul]
  rfl

/-! ## The semigroup of the rescaled velocity -/

section Rescaling

variable (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u) {ε : ℝ} (hε : 0 < ε)
  {c : ℝ} (hc : 0 < c)

/-- **The all-frequency semigroup of `c u` at diffusivity `c ε` is that of `u` at
diffusivity `ε` run at time `c t`.**  The time-rescaled semigroup realizes the operator with
action `c A_{ε,u} = A_{cε,cu}` (`productInductionAction_smul`), and
`productInductionSemigroup_unique` says that only one semigroup realizes it. -/
theorem productInductionSemigroup_smul :
    productInductionSemigroup (c • u) (isTransverseDivergenceFree_smul c hu) (mul_pos hc hε) =
      (productInductionSemigroup u hu hε).timeRescale (Real.toNNReal c) :=
  (productInductionSemigroup_unique (c • u) (isTransverseDivergenceFree_smul c hu)
    (mul_pos hc hε)
    ((productInductionRealization u hu hε).timeRescale (Real.toNNReal c) rfl
      (by rw [Real.coe_toNNReal c hc.le]; exact productInductionAction_smul c u ε))).symm

/-- The identity `productInductionSemigroup_smul` on the solenoidal subspace, which does not
depend on the velocity: both sides are restrictions of the two sides of that identity. -/
theorem solenoidalInductionSemigroup_smul :
    solenoidalInductionSemigroup (c • u) (isTransverseDivergenceFree_smul c hu)
        (mul_pos hc hε) =
      (solenoidalInductionSemigroup u hu hε).timeRescale (Real.toNNReal c) := by
  ext t x : 3
  rw [solenoidalInductionSemigroup_apply, productInductionSemigroup_smul u hu hε hc]
  rfl

/-- **The induction semigroup on `L²_σ(T³; ℂ³)` of `c u` at diffusivity `c ε` is that of `u`
at diffusivity `ε` run at time `c t`**: the identity `solenoidalInductionSemigroup_smul`
transported to the literal three-torus. -/
theorem literalInductionSemigroup_smul :
    literalInductionSemigroup (c • u) (isTransverseDivergenceFree_smul c hu) (mul_pos hc hε) =
      (literalInductionSemigroup u hu hε).timeRescale (Real.toNNReal c) := by
  rw [literalInductionSemigroup, literalInductionSemigroup,
    solenoidalInductionSemigroup_smul u hu hε hc]
  rfl

end Rescaling

/-- **The semigroup of `uNorm` at diffusivity `ε` is the semigroup of `u` at diffusivity `M ε`
run at time `M⁻¹ t`** (Remark 1.6), on `L²_σ(T³; ℂ³)`, with `uNorm = normalizedVelocity u`,
`M = max 1 ‖u‖` and `M⁻¹ = velocityNormalizer u`: `literalInductionSemigroup_smul` at the
factor `M⁻¹` and the diffusivity `M ε`, whose product is `ε`. -/
theorem literalInductionSemigroup_normalizedVelocity (u : TransverseRealW1Inf)
    (hu : IsTransverseDivergenceFree u) {ε : ℝ} (hε : 0 < ε) :
    literalInductionSemigroup (normalizedVelocity u)
        (isTransverseDivergenceFree_normalizedVelocity hu) hε =
      (literalInductionSemigroup u hu (mul_pos (max_one_norm_pos u) hε)).timeRescale
        (Real.toNNReal (velocityNormalizer u)) := by
  rw [← literalInductionSemigroup_smul u hu (mul_pos (max_one_norm_pos u) hε)
    (velocityNormalizer_pos u)]
  have hdiff : ∀ (a : ℝ) (ha : 0 < a), a = ε →
      literalInductionSemigroup (normalizedVelocity u)
          (isTransverseDivergenceFree_normalizedVelocity hu) ha =
        literalInductionSemigroup (normalizedVelocity u)
          (isTransverseDivergenceFree_normalizedVelocity hu) hε := by
    rintro a ha rfl
    rfl
  exact (hdiff _ _ (velocityNormalizer_mul_max_mul u ε)).symm

/-- **`γ(uNorm, ε) = M⁻¹ γ(u, M ε)`** (the second display of Remark 1.6), for the growth bound of
the induction semigroup on `L²_σ(T³; ℂ³)`, with `uNorm = normalizedVelocity u`, `M = max 1 ‖u‖`
and `M⁻¹ = velocityNormalizer u`: the semigroup of `uNorm` is a time rescaling
(`literalInductionSemigroup_normalizedVelocity`), and time rescaling by `M⁻¹` multiplies the
growth bound by `M⁻¹` (`StronglyContinuousSemigroup.growthBound_timeRescale`). -/
theorem gamma_normalizedVelocity (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    {ε : ℝ} (hε : 0 < ε) :
    gamma (normalizedVelocity u) (isTransverseDivergenceFree_normalizedVelocity hu) hε =
      ((velocityNormalizer u : ℝ) : EReal) * gamma u hu (mul_pos (max_one_norm_pos u) hε) := by
  rw [gamma, literalInductionSemigroup_normalizedVelocity u hu hε,
    StronglyContinuousSemigroup.growthBound_timeRescale _
      (Real.toNNReal_pos.2 (velocityNormalizer_pos u)),
    Real.coe_toNNReal _ (velocityNormalizer_pos u).le]
  rfl

/-! ## The growth-rate clause for the normalised velocity -/

/-- **The growth-rate clause of `thm:main` for the normalised velocity** (Remark 1.6): for
every `0 < ε ≤ M⁻¹ ε₀`, the growth rate of `uNorm = normalizedVelocity mainVelocity` is at least
`M⁻¹ γ₀`.  By `gamma_normalizedVelocity`, `γ(uNorm, ε) = M⁻¹ γ(u, M ε)` with `M ε ≤ ε₀`, and
`gamma_ge_gamma0` bounds `γ(u, M ε)` below by `γ₀`.  As for `gamma_ge_gamma0`, the closed
interval is stronger than the open one of the paper. -/
theorem normalizedGrowthFloor_le_gamma {ε : ℝ} (hpos : 0 < ε)
    (hle : ε ≤ velocityNormalizer mainVelocity * mainEps0) :
    ((velocityNormalizer mainVelocity * mainGrowthFloor : ℝ) : EReal) ≤
      gamma (normalizedVelocity mainVelocity)
        (isTransverseDivergenceFree_normalizedVelocity mainVelocity_isTransverseDivergenceFree)
        hpos := by
  have hM := max_one_norm_pos mainVelocity
  have hle' : max 1 ‖mainVelocity‖ * ε ≤ mainEps0 := by
    have h := mul_le_mul_of_nonneg_left hle hM.le
    rwa [velocityNormalizer, ← mul_assoc, mul_one_div_cancel hM.ne', one_mul] at h
  rw [gamma_normalizedVelocity mainVelocity mainVelocity_isTransverseDivergenceFree hpos,
    EReal.coe_mul]
  exact mul_le_mul_of_nonneg_left (gamma_ge_gamma0 (mul_pos hM hpos) hle')
    (EReal.coe_nonneg.2 (velocityNormalizer_pos mainVelocity).le)

/-- **`eq:main-growth-conclusion` for the normalised velocity**:
`liminf_{ε ↓ 0} γ(uNorm, ε) ≥ M⁻¹ γ₀`, read along `𝓝[>] 0` of the total extension `gammaOf`. -/
theorem normalizedGrowthFloor_le_liminf_gammaOf :
    ((velocityNormalizer mainVelocity * mainGrowthFloor : ℝ) : EReal) ≤
      Filter.liminf
        (gammaOf (normalizedVelocity mainVelocity)
          (isTransverseDivergenceFree_normalizedVelocity mainVelocity_isTransverseDivergenceFree))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
  have hev : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ((velocityNormalizer mainVelocity * mainGrowthFloor : ℝ) : EReal) ≤
        gammaOf (normalizedVelocity mainVelocity)
          (isTransverseDivergenceFree_normalizedVelocity mainVelocity_isTransverseDivergenceFree)
          ε := by
    filter_upwards [Ioo_mem_nhdsGT (mul_pos (velocityNormalizer_pos mainVelocity) mainEps0_pos)]
      with ε hε
    rw [gammaOf_eq_gamma _ _ hε.1]
    exact normalizedGrowthFloor_le_gamma hε.1 hε.2.le
  exact Filter.le_liminf_of_le (by isBoundedDefault) hev

/-! ## The semigroup orbit of the real datum for the normalised velocity -/

/-- **`eq:main-thm-growth` for "its solution" at the normalised velocity**: the clauses
`MainSemigroupOrbitClauses` at `uNorm = normalizedVelocity mainVelocity` with the threshold
`M⁻¹ ε₀` and the floor `M⁻¹ γ₀` — the orbit, the uniqueness clause and the spectral clauses
`MainPhysicalClausesAt` at one triple — from the rescaled reduced clauses
`mainReducedClauses_smul`. -/
theorem mainSemigroupOrbitClauses_normalizedVelocity :
    MainSemigroupOrbitClauses (normalizedVelocity mainVelocity)
      (isTransverseDivergenceFree_normalizedVelocity mainVelocity_isTransverseDivergenceFree)
      (velocityNormalizer mainVelocity * mainEps0)
      (velocityNormalizer mainVelocity * mainGrowthFloor) :=
  mainSemigroupOrbitClauses_of_mainReducedClauses _ _
    (mul_pos (velocityNormalizer_pos mainVelocity) mainGrowthFloor_pos)
    (mainReducedClauses_smul (velocityNormalizer_pos mainVelocity) mainReducedClauses_holds)

end

end FastDynamo
