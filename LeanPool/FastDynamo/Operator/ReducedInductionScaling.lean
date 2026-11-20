/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Main

/-!
# Homogeneity of the reduced induction operator and the normalised velocity

Remark 1.6 of the paper (unlabelled; the normalisation of the velocity) rests on the joint
homogeneity of the induction action in the velocity and the diffusivity: replacing
`(u, ε)` by `(c u, c ε)` multiplies the whole action by `c`.  Writing
`M = max 1 ‖u‖_{W^{1,∞}}` and `uNorm = u / M` this gives `L_{ε, uNorm} = M⁻¹ L_{M ε, u}`,
so the conclusion of the main theorem transfers from `u` to the normalised
velocity `uNorm` with thresholds `ε₀ / M` and `γ₀ / M`, and one may always demand
`‖u‖ ≤ 1` in the statement.

## Contents

* `reducedInductionAction_smul`: the homogeneity
  `A_{c ε, c u, K} = c · A_{ε, u, K}` for a real scalar `c`.
* `reducedInductionOperator_isEigenpair_smul_iff`: for `c ≠ 0`, eigenpairs of
  the scaled operator at `c λ` are exactly the eigenpairs of the original
  operator at `λ`, with the same amplitude.
* `isTransverseDivergenceFree_smul`, `velocity_smul_ne_zero`: the two
  structural clauses survive a (nonzero) rescaling.
* `norm_normalizedVelocity_le_one`: the normalised velocity has `W^{1,∞}` norm
  at most `1`.
* `mainReducedClauses_smul`, `exists_normalized_mainReducedClauses`,
  `MainReducedTargetNormalized`, `MainPhysicalConclusionNormalized` and
  `mainPhysicalConclusionNormalized_of_mainReducedTarget`: the statement-layer
  consequences.

Nothing here changes the operators of `FastDynamo.Operator.FixedSector`; the
module only adds the scaling identities and the normalised statements.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-! ## Real scalars on the velocity coefficients

The velocity enters the reduced action only through the complexified
coefficient maps of `FastDynamo.Analysis.TransverseW1Inf`, which are
`ℝ`-linear into complex `L∞` spaces.  The lemmas below record their
homogeneity in the form needed downstream, with the real scalar already
promoted to a complex one. -/

/-- Scaling the velocity by a real `c` scales each complexified value
coordinate by `(c : ℂ)`. -/
theorem transverseW1InfComplexValueCoordLInf_smul
    (c : ℝ) (u : TransverseRealW1Inf) (i : Fin 3) :
    transverseW1InfComplexValueCoordLInf i (c • u) =
      (c : ℂ) • transverseW1InfComplexValueCoordLInf i u := by
  rw [map_smul]
  exact (Complex.coe_smul c _).symm

/-- Scaling the velocity by a real `c` scales each complexified weak derivative
by `(c : ℂ)`. -/
theorem transverseW1InfComplexDerivLInf_smul
    (c : ℝ) (u : TransverseRealW1Inf) (j : Fin 2) :
    transverseW1InfComplexDerivLInf j (c • u) =
      (c : ℂ) • transverseW1InfComplexDerivLInf j u := by
  rw [map_smul]
  exact (Complex.coe_smul c _).symm

/-- Scaling the velocity by a real `c` scales each complexified weak-derivative
coordinate by `(c : ℂ)`. -/
theorem transverseW1InfComplexDerivCoordLInf_smul
    (c : ℝ) (u : TransverseRealW1Inf) (j : Fin 2) (i : Fin 3) :
    transverseW1InfComplexDerivCoordLInf j i (c • u) =
      (c : ℂ) • transverseW1InfComplexDerivCoordLInf j i u := by
  rw [map_smul]
  exact (Complex.coe_smul c _).symm

/-! ## Homogeneity of the three velocity terms -/

/-- The transverse transport term `∑_{j<2} u_j ∂_j b` is homogeneous of degree
one in the velocity. -/
theorem reducedInductionTransport_smul (c : ℝ) (u : TransverseRealW1Inf) :
    reducedInductionTransport (c • u) = (c : ℂ) • reducedInductionTransport u := by
  rw [reducedInductionTransport, reducedInductionTransport, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [transverseW1InfComplexValueCoordLInf_smul, map_smul,
    ContinuousLinearMap.smul_comp]

/-- The axial transport term `(2π i K) u₃ b` is homogeneous of degree one in
the velocity. -/
theorem reducedInductionAxialTransport_smul
    (c : ℝ) (u : TransverseRealW1Inf) (K : ℤ) :
    reducedInductionAxialTransport (c • u) K =
      (c : ℂ) • reducedInductionAxialTransport u K := by
  rw [reducedInductionAxialTransport, reducedInductionAxialTransport,
    transverseW1InfComplexValueCoordLInf_smul, map_smul,
    ContinuousLinearMap.smul_comp]
  exact smul_comm (axialMultiplier K) (c : ℂ) _

/-- The stretching term `∑_{j<2} b_j ∂_j u` is homogeneous of degree one in the
velocity. -/
theorem reducedInductionStretching_smul (c : ℝ) (u : TransverseRealW1Inf) :
    reducedInductionStretching (c • u) = (c : ℂ) • reducedInductionStretching u := by
  rw [reducedInductionStretching, reducedInductionStretching, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [transverseW1InfComplexDerivLInf_smul, map_smul,
    ContinuousLinearMap.smul_comp]

/-! ## Joint homogeneity of the reduced action -/

/-- **Homogeneity of the reduced induction action.**  For every real scalar
`c`, replacing the velocity `u` by `c • u` and the diffusivity `ε` by `c * ε`
multiplies the whole reduced action by `(c : ℂ)`.  The diffusion term scales
because it is linear in `ε`, the three velocity terms because they are
`ℝ`-linear in `u`.  This is the paper's identity
`L_{ε, u/M} = M⁻¹ L_{M ε, u}` read with `c = 1 / M`. -/
theorem reducedInductionAction_smul
    (c : ℝ) (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) :
    reducedInductionAction (c • u) (c * ε) K =
      (c : ℂ) • reducedInductionAction u ε K := by
  rw [reducedInductionAction, reducedInductionAction,
    reducedInductionTransport_smul, reducedInductionAxialTransport_smul,
    reducedInductionStretching_smul, Complex.ofReal_mul, mul_smul]
  module

/-- Pointwise form of `reducedInductionAction_smul`. -/
theorem reducedInductionAction_smul_apply
    (c : ℝ) (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (b : TransverseC3H2) :
    reducedInductionAction (c • u) (c * ε) K b =
      (c : ℂ) • reducedInductionAction u ε K b := by
  rw [reducedInductionAction_smul]
  rfl

/-! ## Eigenpairs under the scaling -/

/-- An eigenpair of the reduced operator scales: if `b` is an eigenvector of
`A_{ε, u, K}` for `λ`, it is an eigenvector of `A_{c ε, c u, K}` for `c λ`.
No hypothesis on `c` is needed in this direction. -/
theorem reducedInductionOperator_isEigenpair_smul
    (c : ℝ) (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (lambda : ℂ)
    (b : TransverseC3H2)
    (h : (reducedInductionOperator u ε K).IsEigenpair lambda b) :
    (reducedInductionOperator (c • u) (c * ε) K).IsEigenpair ((c : ℂ) * lambda) b := by
  obtain ⟨hne, heq⟩ := h
  have heq' : reducedInductionAction u ε K b = lambda • transverseH2Embedding b := heq
  refine ⟨hne, ?_⟩
  change reducedInductionAction (c • u) (c * ε) K b =
    ((c : ℂ) * lambda) • transverseH2Embedding b
  rw [reducedInductionAction_smul_apply, heq', mul_smul]

/-- **Eigenpair scaling equivalence.**  For a nonzero real scalar `c`, the
eigenpairs of the rescaled reduced operator at `c λ` are exactly the
eigenpairs of the original operator at `λ`, with the *same* transverse
amplitude `b`. -/
theorem reducedInductionOperator_isEigenpair_smul_iff
    {c : ℝ} (hc : c ≠ 0) (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (lambda : ℂ)
    (b : TransverseC3H2) :
    (reducedInductionOperator (c • u) (c * ε) K).IsEigenpair ((c : ℂ) * lambda) b ↔
      (reducedInductionOperator u ε K).IsEigenpair lambda b := by
  refine ⟨fun h ↦ ?_, reducedInductionOperator_isEigenpair_smul c u ε K lambda b⟩
  obtain ⟨hne, heq⟩ := h
  have heq' : reducedInductionAction (c • u) (c * ε) K b =
      ((c : ℂ) * lambda) • transverseH2Embedding b := heq
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  refine ⟨hne, ?_⟩
  change reducedInductionAction u ε K b = lambda • transverseH2Embedding b
  refine smul_right_injective TransverseC3L2 hc' ?_
  change (c : ℂ) • reducedInductionAction u ε K b =
    (c : ℂ) • lambda • transverseH2Embedding b
  rw [← reducedInductionAction_smul_apply, ← mul_smul]
  exact heq'

/-! ## The structural clauses under the scaling -/

/-- Divergence-freeness is preserved by any real rescaling of the velocity: the
divergence is an `ℝ`-linear function of the stored weak derivatives. -/
theorem isTransverseDivergenceFree_smul (c : ℝ) {u : TransverseRealW1Inf}
    (hu : IsTransverseDivergenceFree u) : IsTransverseDivergenceFree (c • u) := by
  rw [IsTransverseDivergenceFree] at hu
  rw [IsTransverseDivergenceFree, transverseW1InfComplexDerivCoordLInf_smul,
    transverseW1InfComplexDerivCoordLInf_smul, ← smul_add, hu, smul_zero]

/-- A nonzero velocity stays nonzero after a nonzero rescaling. -/
theorem velocity_smul_ne_zero {c : ℝ} (hc : c ≠ 0) {u : TransverseRealW1Inf}
    (hu : u ≠ 0) : c • u ≠ 0 :=
  smul_ne_zero hc hu

/-! ## Norms on `TransverseRealW1Inf` -/

/-- The subspace norm on `TransverseRealW1Inf` is absolutely homogeneous. -/
theorem norm_smul_transverseRealW1Inf (c : ℝ) (u : TransverseRealW1Inf) :
    ‖c • u‖ = |c| * ‖u‖ := by
  rw [norm_smul, Real.norm_eq_abs]

/-! ## The normalised velocity -/

/-- The normalising factor `1 / max 1 ‖u‖` of the paper's normalisation
remark (Remark 1.6).  Using `max 1 ‖u‖` rather than `‖u‖` keeps the factor well defined and
positive even for `u = 0`. -/
def velocityNormalizer (u : TransverseRealW1Inf) : ℝ := 1 / max 1 ‖u‖

/-- The normalised velocity `uNorm = u / max (1, ‖u‖)`. -/
def normalizedVelocity (u : TransverseRealW1Inf) : TransverseRealW1Inf :=
  velocityNormalizer u • u

/-- The denominator of the normalising factor is at least `1`. -/
theorem one_le_max_one_norm (u : TransverseRealW1Inf) : (1 : ℝ) ≤ max 1 ‖u‖ :=
  le_max_left _ _

/-- The denominator of the normalising factor is positive. -/
theorem max_one_norm_pos (u : TransverseRealW1Inf) : (0 : ℝ) < max 1 ‖u‖ :=
  lt_of_lt_of_le zero_lt_one (one_le_max_one_norm u)

/-- The normalising factor is positive. -/
theorem velocityNormalizer_pos (u : TransverseRealW1Inf) : 0 < velocityNormalizer u :=
  div_pos zero_lt_one (max_one_norm_pos u)

/-- **The normalisation bound.**  Dividing a velocity by `max (1, ‖u‖)` puts it
in the closed unit ball of `W^{1,∞}`. -/
theorem norm_smul_max_one_norm_le_one (u : TransverseRealW1Inf) :
    ‖(1 / max 1 ‖u‖) • u‖ ≤ 1 := by
  rw [norm_smul_transverseRealW1Inf,
    abs_of_pos (div_pos zero_lt_one (max_one_norm_pos u)),
    div_mul_eq_mul_div, one_mul, div_le_one (max_one_norm_pos u)]
  exact le_max_right _ _

/-- The normalised velocity lies in the closed unit ball of `W^{1,∞}`. -/
theorem norm_normalizedVelocity_le_one (u : TransverseRealW1Inf) :
    ‖normalizedVelocity u‖ ≤ 1 :=
  norm_smul_max_one_norm_le_one u

/-- The normalised velocity is divergence-free whenever `u` is. -/
theorem isTransverseDivergenceFree_normalizedVelocity {u : TransverseRealW1Inf}
    (hu : IsTransverseDivergenceFree u) :
    IsTransverseDivergenceFree (normalizedVelocity u) :=
  isTransverseDivergenceFree_smul _ hu

/-- The normalised velocity is nonzero whenever `u` is. -/
theorem normalizedVelocity_ne_zero {u : TransverseRealW1Inf} (hu : u ≠ 0) :
    normalizedVelocity u ≠ 0 :=
  velocity_smul_ne_zero (velocityNormalizer_pos u).ne' hu

/-! ## Statement-layer consequences -/

/-- **Rescaling the reduced clauses.**  For `c > 0` the reduced clauses at
`(u, ε₀, γ₀)` imply the reduced clauses at `(c u, c ε₀, c γ₀)`: given
`0 < ε ≤ c ε₀`, apply the hypothesis at `ε / c ≤ ε₀` and scale the resulting
eigenpair by `c`; the growth floor scales because `Re (c λ) = c · Re λ`. -/
theorem mainReducedClauses_smul {c : ℝ} (hc : 0 < c) {u : TransverseRealW1Inf}
    {eps0 gamma0 : ℝ} (h : MainReducedClauses u eps0 gamma0) :
    MainReducedClauses (c • u) (c * eps0) (c * gamma0) := by
  intro eps hpos hle
  have hle' : eps / c ≤ eps0 := by
    rw [div_le_iff₀ hc, mul_comm]
    exact hle
  obtain ⟨K, lambda, b, hK, hgrowth, hpair⟩ := h (eps / c) (div_pos hpos hc) hle'
  refine ⟨K, (c : ℂ) * lambda, b, hK, ?_, ?_⟩
  · have hre : ((c : ℂ) * lambda).re = c * lambda.re := by
      simp [Complex.mul_re]
    rw [hre]
    exact mul_le_mul_of_nonneg_left hgrowth hc.le
  · have heps : c * (eps / c) = eps := by
      field_simp
    have hscaled :=
      reducedInductionOperator_isEigenpair_smul c u (eps / c) K lambda b hpair
    rwa [heps] at hscaled

/-- **Normalised reduced target.**  The reduced-operator target can always be
witnessed by a velocity in the closed unit ball of `W^{1,∞}`: replace `u` by
`u / max (1, ‖u‖)` and the thresholds by `ε₀ / max (1, ‖u‖)` and
`γ₀ / max (1, ‖u‖)`. -/
theorem exists_normalized_mainReducedClauses (h : MainReducedTarget) :
    ∃ u : TransverseRealW1Inf,
      IsTransverseDivergenceFree u ∧ u ≠ 0 ∧ ‖u‖ ≤ 1 ∧
      ∃ eps0 gamma0 : ℝ, 0 < eps0 ∧ 0 < gamma0 ∧
        MainReducedClauses u eps0 gamma0 := by
  obtain ⟨u, hu, hune, eps0, gamma0, heps0, hgamma0, hclauses⟩ := h
  exact ⟨normalizedVelocity u, isTransverseDivergenceFree_normalizedVelocity hu,
    normalizedVelocity_ne_zero hune, norm_normalizedVelocity_le_one u,
    velocityNormalizer u * eps0, velocityNormalizer u * gamma0,
    mul_pos (velocityNormalizer_pos u) heps0,
    mul_pos (velocityNormalizer_pos u) hgamma0,
    mainReducedClauses_smul (velocityNormalizer_pos u) hclauses⟩

/-- The reduced-operator target with the extra normalisation clause
`‖u‖ ≤ 1`. -/
def MainReducedTargetNormalized : Prop :=
  ∃ u : TransverseRealW1Inf,
    IsTransverseDivergenceFree u ∧ u ≠ 0 ∧ ‖u‖ ≤ 1 ∧
    ∃ eps0 gamma0 : ℝ, 0 < eps0 ∧ 0 < gamma0 ∧
      MainReducedClauses u eps0 gamma0

/-- The spectral half of Paper Theorem 1.2 with the extra normalisation
clause `‖u‖ ≤ 1` on the velocity. -/
def MainPhysicalConclusionNormalized : Prop :=
  ∃ u : TransverseRealW1Inf,
    IsTransverseDivergenceFree u ∧ u ≠ 0 ∧ ‖u‖ ≤ 1 ∧
    ∃ eps0 gamma0 : ℝ, 0 < eps0 ∧ 0 < gamma0 ∧
      MainPhysicalClauses u eps0 gamma0

/-- The normalised reduced target follows from the reduced target. -/
theorem mainReducedTargetNormalized_of_mainReducedTarget
    (h : MainReducedTarget) : MainReducedTargetNormalized :=
  exists_normalized_mainReducedClauses h

/-- Every physical clause of the main theorem follows from the normalised
reduced target, through the finish layer. -/
theorem mainPhysicalConclusionNormalized_of_mainReducedTargetNormalized
    (h : MainReducedTargetNormalized) : MainPhysicalConclusionNormalized := by
  obtain ⟨u, hu, hune, hnorm, eps0, gamma0, heps0, hgamma0, hclauses⟩ := h
  exact ⟨u, hu, hune, hnorm, eps0, gamma0, heps0, hgamma0,
    mainPhysicalClauses_of_mainReducedClauses hu hgamma0 hclauses⟩

/-- **The normalised main theorem.**  The reduced-operator target implies the
spectral half of Paper Theorem 1.2 with the additional requirement that
the velocity have `W^{1,∞}` norm at most `1`. -/
theorem mainPhysicalConclusionNormalized_of_mainReducedTarget
    (h : MainReducedTarget) : MainPhysicalConclusionNormalized :=
  mainPhysicalConclusionNormalized_of_mainReducedTargetNormalized
    (mainReducedTargetNormalized_of_mainReducedTarget h)

end

end FastDynamo
