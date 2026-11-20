/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.StrongSolutionUniqueness
public import LeanPool.FastDynamo.Operator.AdjointRealizationFromResolvent

/-!
# The formal adjoint of the reduced induction operator

For a real transverse `W^{1,∞}` velocity `u`, a diffusivity `ε` and an axial
frequency `K` the reduced induction action of `FastDynamo/Operator/FixedSector.lean`
is

`A b = ε Δ⊥ b − ε (2πK)² b − (u⊥·∇⊥) b − 2πi K u₃ b + (b·∇⊥) u`.

This module constructs the displayed formal adjoint

`A* b = ε Δ⊥ b − ε (2πK)² b + (u⊥·∇⊥) b + 2πi K u₃ b + (∇⊥u)ᵀ b`

on the same `H²` graph domain and with the same `L²` embedding, proves the
integration-by-parts identity `FormalAdjointPairing A A*` for a transversely
divergence-free velocity, and transports the half-plane numerical-range bound
of `FastDynamo/Dynamics/StrongSolutionUniqueness.lean` to `A*`.

Two devices keep the file short and draw every analytic input from results
proved elsewhere in the library.

* The transposed stretching matrix `(∇⊥u)ᵀ` is the pointwise adjoint
  `star (transverseStretchingCoefficient u)` of the literal stretching matrix
  of `FastDynamo/Global/TorusLocalCoreMeasurability.lean`, and the corresponding
  bilinear identity is the pointwise `ContinuousLinearMap.adjoint` identity
  integrated over the torus.  No new `W^{1,∞}` data is introduced, and the
  displayed matrix entries are `((∇⊥u)ᵀ b)(x) = Σ_{j<2} ⟪∂_j u(x), b(x)⟫ e_j`.
* The bilinear integration-by-parts identities for diffusion, transverse
  transport and axial transport are obtained from the *quadratic* identities
  proved in `FastDynamo/Global/ReducedInductionEnergyIdentity.lean`
  (`im_inner_reducedInductionDiffusion_eq_zero`,
  `re_inner_reducedInductionTransport_eq_zero`,
  `re_inner_reducedInductionAxialTransport_eq_zero`) by complex polarization.
  Over `ℂ` this loses nothing: a sesquilinear form vanishing on the diagonal
  vanishes identically.  In particular the divergence-freeness of `u` enters
  exactly where it enters the energy identity, through the weak Leibniz rule
  used by `re_inner_reducedInductionTransport_eq_zero`.

No maximality of the adjoint domain is asserted here: the output is precisely
the formal pairing consumed by
`DomainOperator.isAdjointRealization_of_formalAdjointPairing_of_surjective_pencil`,
whose surjectivity hypothesis is not addressed here; the maximal adjoint
realization is obtained in `Global/ReducedInductionHalfPlaneResolvent.lean` from a far
positive-real reference point.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

/-! ## Polarization of a sesquilinear pairing -/

/-- **Complex polarization.**  Let `S` and `T` be continuous linear maps from a
complex normed space into a complex inner-product space and let `r` be a scalar.
If the sesquilinear form `(b, c) ↦ ⟪S b, T c⟫ + r ⟪T b, S c⟫` vanishes on the
diagonal then it vanishes identically.

The two test vectors `b + c` and `b + i c` produce the sum and the difference of
the form and of its flip, whence both vanish. -/
private theorem inner_flip_pair_eq_zero_of_diagonal_eq_zero
    {D X : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
    [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (S T : D →L[ℂ] X) (r : ℂ)
    (hdiag : ∀ d : D, inner ℂ (S d) (T d) + r * inner ℂ (T d) (S d) = 0)
    (b c : D) :
    inner ℂ (S b) (T c) + r * inner ℂ (T b) (S c) = 0 := by
  have h1 := hdiag (b + c)
  have h2 := hdiag (b + Complex.I • c)
  have hb := hdiag b
  have hc := hdiag c
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, Complex.conj_I] at h1 h2
  have hsum : (inner ℂ (S b) (T c) + r * inner ℂ (T b) (S c)) +
      (inner ℂ (S c) (T b) + r * inner ℂ (T c) (S b)) = 0 := by
    linear_combination h1 - hb - hc
  have hI : Complex.I * ((inner ℂ (S b) (T c) + r * inner ℂ (T b) (S c)) -
      (inner ℂ (S c) (T b) + r * inner ℂ (T c) (S b))) = 0 := by
    linear_combination h2 - hb - hc +
      (inner ℂ (S c) (T c) + r * inner ℂ (T c) (S c)) * Complex.I_sq
  have hdiff := (mul_eq_zero.1 hI).resolve_left Complex.I_ne_zero
  linear_combination hsum / 2 + hdiff / 2

/-- A pairing whose quadratic form is purely imaginary is skew: the bilinear
identity `⟪T b, S c⟫ = -⟪S b, T c⟫` follows from `Re ⟪S d, T d⟫ = 0` alone. -/
theorem inner_flip_eq_neg_of_re_inner_eq_zero
    {D X : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
    [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (S T : D →L[ℂ] X)
    (h : ∀ d : D, (inner ℂ (S d) (T d)).re = 0) (b c : D) :
    inner ℂ (T b) (S c) = -inner ℂ (S b) (T c) := by
  have hdiag : ∀ d : D, inner ℂ (S d) (T d) + 1 * inner ℂ (T d) (S d) = 0 := by
    intro d
    rw [one_mul, ← inner_conj_symm (T d) (S d), Complex.add_conj, h d]
    simp
  have hpair := inner_flip_pair_eq_zero_of_diagonal_eq_zero S T 1 hdiag b c
  rw [one_mul] at hpair
  linear_combination hpair

/-- A pairing whose quadratic form is real is symmetric: the bilinear identity
`⟪T b, S c⟫ = ⟪S b, T c⟫` follows from `Im ⟪S d, T d⟫ = 0` alone. -/
theorem inner_flip_eq_of_im_inner_eq_zero
    {D X : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
    [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (S T : D →L[ℂ] X)
    (h : ∀ d : D, (inner ℂ (S d) (T d)).im = 0) (b c : D) :
    inner ℂ (T b) (S c) = inner ℂ (S b) (T c) := by
  have hdiag : ∀ d : D,
      inner ℂ (S d) (T d) + (-1 : ℂ) * inner ℂ (T d) (S d) = 0 := by
    intro d
    rw [neg_one_mul, ← inner_conj_symm (T d) (S d), ← sub_eq_add_neg,
      Complex.sub_conj, h d]
    simp
  have hpair :=
    inner_flip_pair_eq_zero_of_diagonal_eq_zero S T (-1 : ℂ) hdiag b c
  rw [neg_one_mul] at hpair
  linear_combination -hpair

/-! ## The transposed stretching coefficient -/

/-- Pointwise adjunction for an essentially bounded operator-valued multiplier on
the transverse torus: the `L²` adjoint of `operatorMulL2` is multiplication by the
pointwise adjoint symbol `star A`. -/
theorem inner_operatorMulTransverse_star
    (A : TransverseC3OperatorLInf) (f g : TransverseC3L2) :
    inner ℂ (operatorMulL2 transverseMeasure A f) g =
      inner ℂ f (operatorMulL2 transverseMeasure (star A) g) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [operatorMulL2_coe_ae transverseMeasure A f,
    operatorMulL2_coe_ae transverseMeasure (star A) g,
    Lp.coeFn_star A] with x hAf hAg hstar
  rw [hAf, hAg, hstar, Pi.star_apply, ContinuousLinearMap.star_eq_adjoint]
  exact (ContinuousLinearMap.adjoint_inner_right (A x) (f x) (g x)).symm

/-- The transposed stretching term `(∇⊥u)ᵀ b` on the reduced `H²` domain.  Its
coefficient is the pointwise adjoint of the literal transverse gradient
matrix `transverseStretchingCoefficient u`; no new velocity data is used. -/
def reducedInductionStretchingTranspose (u : TransverseRealW1Inf) :
    TransverseC3H2 →L[ℂ] TransverseC3L2 :=
  (operatorMulL2 transverseMeasure
    (star (transverseStretchingCoefficient u))).comp transverseH2Embedding

/-- Application form of the transposed stretching term: it is multiplication of
the `L²` value of `b` by the transposed gradient matrix. -/
theorem reducedInductionStretchingTranspose_apply
    (u : TransverseRealW1Inf) (b : TransverseC3H2) :
    reducedInductionStretchingTranspose u b =
      operatorMulL2 transverseMeasure
        (star (transverseStretchingCoefficient u))
        (transverseH2Embedding b) :=
  rfl

/-- Exact stretching pairing: the transposed stretching term is the formal
adjoint of the stretching term on the reduced `H²` domain. -/
theorem inner_reducedInductionStretching_flip
    (u : TransverseRealW1Inf) (b c : TransverseC3H2) :
    inner ℂ (reducedInductionStretching u b) (transverseH2Embedding c) =
      inner ℂ (transverseH2Embedding b)
        (reducedInductionStretchingTranspose u c) := by
  rw [← operatorMul_transverseStretchingCoefficient_eq,
    reducedInductionStretchingTranspose_apply]
  exact inner_operatorMulTransverse_star (transverseStretchingCoefficient u)
    (transverseH2Embedding b) (transverseH2Embedding c)

/-- The transposed stretching term has exactly the same real quadratic form as
the stretching term, because the two forms are complex conjugates. -/
theorem re_inner_reducedInductionStretchingTranspose_eq
    (u : TransverseRealW1Inf) (b : TransverseC3H2) :
    (inner ℂ (transverseH2Embedding b)
      (reducedInductionStretchingTranspose u b)).re =
      (inner ℂ (transverseH2Embedding b)
        (reducedInductionStretching u b)).re := by
  rw [← inner_reducedInductionStretching_flip u b b]
  exact inner_re_symm (𝕜 := ℂ) _ _

/-- Real part of the transposed stretching form obeys the same `L∞` bound as the
stretching form itself, with the *untransposed* coefficient norm. -/
theorem re_inner_reducedInductionStretchingTranspose_le
    (u : TransverseRealW1Inf) (b : TransverseC3H2) :
    (inner ℂ (transverseH2Embedding b)
      (reducedInductionStretchingTranspose u b)).re ≤
      ‖transverseStretchingCoefficient u‖ *
        ‖transverseH2Embedding b‖ ^ 2 := by
  rw [re_inner_reducedInductionStretchingTranspose_eq]
  exact re_inner_reducedInductionStretching_le u b

/-! ## Termwise formal pairings -/

/-- **Integration by parts for the reduced diffusion term.**  The shifted
transverse Laplacian `ε Δ⊥ − ε(2πK)²` is formally self-adjoint on the reduced
`H²` graph domain.  This is the polarization of the exact Fourier identity
`im_inner_reducedInductionDiffusion_eq_zero`, i.e. of the periodic
integration-by-parts formula for the transverse Laplacian. -/
theorem inner_reducedInductionDiffusion_flip
    (K : ℤ) (b c : TransverseC3H2) :
    inner ℂ (reducedInductionDiffusion K b) (transverseH2Embedding c) =
      inner ℂ (transverseH2Embedding b) (reducedInductionDiffusion K c) :=
  inner_flip_eq_of_im_inner_eq_zero (transverseH2Embedding (ι := Fin 3))
    (reducedInductionDiffusion K)
    (fun d ↦ im_inner_reducedInductionDiffusion_eq_zero K d) b c

/-- **Skewness of the transverse transport term.**  For a transversely
divergence-free real velocity the transport term `(u⊥·∇⊥)` changes sign under
formal adjunction.  This is the polarization of
`re_inner_reducedInductionTransport_eq_zero`, which is where the weak Leibniz
rule and the divergence-free hypothesis on `u` are used. -/
theorem inner_reducedInductionTransport_flip
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (b c : TransverseC3H2) :
    inner ℂ (reducedInductionTransport u b) (transverseH2Embedding c) =
      -inner ℂ (transverseH2Embedding b) (reducedInductionTransport u c) :=
  inner_flip_eq_neg_of_re_inner_eq_zero (transverseH2Embedding (ι := Fin 3))
    (reducedInductionTransport u)
    (fun d ↦ re_inner_reducedInductionTransport_eq_zero u hu 0 d) b c

/-- **Skewness of the axial transport term.**  The multiplier `2πiK u₃` is purely
imaginary with a real coefficient, so it changes sign under formal adjunction.
This is the polarization of
`re_inner_reducedInductionAxialTransport_eq_zero`; no divergence hypothesis is
needed. -/
theorem inner_reducedInductionAxialTransport_flip
    (u : TransverseRealW1Inf) (K : ℤ) (b c : TransverseC3H2) :
    inner ℂ (reducedInductionAxialTransport u K b) (transverseH2Embedding c) =
      -inner ℂ (transverseH2Embedding b)
        (reducedInductionAxialTransport u K c) :=
  inner_flip_eq_neg_of_re_inner_eq_zero (transverseH2Embedding (ι := Fin 3))
    (reducedInductionAxialTransport u K)
    (fun d ↦ re_inner_reducedInductionAxialTransport_eq_zero u K d) b c

/-! ## The displayed formal adjoint operator -/

/-- The displayed formal adjoint of the reduced induction action

`A* b = ε (Δ⊥ - (2πK)²) b + ∑_{j<2} u_j ∂_j b + (2π i K) u_3 b + (∇⊥u)ᵀ b`.

Diffusion is unchanged, both transport terms change sign, and the stretching
matrix is replaced by its pointwise transpose. -/
def reducedInductionAdjointAction (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) :
    TransverseC3H2 →L[ℂ] TransverseC3L2 :=
  (ε : ℂ) • reducedInductionDiffusion K + reducedInductionTransport u +
    reducedInductionAxialTransport u K + reducedInductionStretchingTranspose u

/-- The displayed formal adjoint operator: the same complete Fourier-graph
domain and the same `L²` embedding as `reducedInductionOperator`. -/
def reducedInductionAdjointOperator
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) :
    DomainOperator TransverseC3L2 TransverseC3H2 where
  embedding := transverseH2Embedding
  embedding_injective := transverseH2Embedding_injective
  op := reducedInductionAdjointAction u ε K

/-- The adjoint operator carries the same domain embedding as the forward
reduced induction operator. -/
@[simp] theorem reducedInductionAdjointOperator_embedding
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) :
    (reducedInductionAdjointOperator u ε K).embedding =
      transverseH2Embedding :=
  rfl

/-- The adjoint operator acts by the displayed formal adjoint action. -/
@[simp] theorem reducedInductionAdjointOperator_op
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) :
    (reducedInductionAdjointOperator u ε K).op =
      reducedInductionAdjointAction u ε K :=
  rfl

/-- **The complete integration-by-parts identity.**  For a transversely
divergence-free real velocity the displayed operator
`reducedInductionAdjointOperator u ε K` is a formal adjoint of
`reducedInductionOperator u ε K`:

`⟪A b, c⟫ = ⟪b, A* c⟫` for all `b, c` in the reduced `H²` domain.

This is a formal pairing only; no maximality of the adjoint domain is
asserted. -/
theorem reducedInductionOperator_formalAdjointPairing
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (ε : ℝ) (K : ℤ) :
    (reducedInductionOperator u ε K).FormalAdjointPairing
      (reducedInductionAdjointOperator u ε K) := by
  intro b c
  change inner ℂ (reducedInductionAction u ε K b) (transverseH2Embedding c) =
    inner ℂ (transverseH2Embedding b) (reducedInductionAdjointAction u ε K c)
  rw [reducedInductionAction, reducedInductionAdjointAction]
  simp only [add_apply, sub_apply, smul_apply, inner_add_left, inner_sub_left,
    inner_smul_left, inner_add_right, inner_smul_right, Complex.conj_ofReal]
  rw [inner_reducedInductionDiffusion_flip,
    inner_reducedInductionTransport_flip u hu,
    inner_reducedInductionAxialTransport_flip,
    inner_reducedInductionStretching_flip]
  ring

/-! ## Dissipativity of the adjoint -/

/-- Algebraic expansion of the adjoint quadratic form into diffusion, transverse
transport, axial transport and transposed stretching. -/
theorem inner_reducedInductionAdjointAction_eq
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (b : TransverseC3H2) :
    inner ℂ (transverseH2Embedding b)
        (reducedInductionAdjointAction u ε K b) =
      (ε : ℂ) * inner ℂ (transverseH2Embedding b)
        (reducedInductionDiffusion K b) +
      inner ℂ (transverseH2Embedding b) (reducedInductionTransport u b) +
      inner ℂ (transverseH2Embedding b)
        (reducedInductionAxialTransport u K b) +
      inner ℂ (transverseH2Embedding b)
        (reducedInductionStretchingTranspose u b) := by
  rw [reducedInductionAdjointAction]
  simp only [add_apply, smul_apply, inner_add_right, inner_smul_right]

/-- Literal real-part identity for the adjoint action.  Exactly as for the
forward action, both transport terms disappear and diffusion contributes the
nonpositive coercive term; only the transposed stretching survives. -/
theorem re_inner_reducedInductionAdjointAction_eq
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (ε : ℝ) (K : ℤ) (b : TransverseC3H2) :
    (inner ℂ (transverseH2Embedding b)
      (reducedInductionAdjointAction u ε K b)).re =
      -ε * (reducedTransverseGradientEnergy b +
        (2 * Real.pi * (K : ℝ)) ^ 2 *
          ‖transverseH2Embedding b‖ ^ 2) +
      (inner ℂ (transverseH2Embedding b)
        (reducedInductionStretchingTranspose u b)).re := by
  rw [inner_reducedInductionAdjointAction_eq, Complex.add_re, Complex.add_re,
    Complex.add_re, re_inner_reducedInductionTransport_eq_zero u hu K b,
    re_inner_reducedInductionAxialTransport_eq_zero u K b, Complex.mul_re,
    re_inner_reducedInductionDiffusion_eq,
    im_inner_reducedInductionDiffusion_eq_zero]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **Half-plane numerical range of the adjoint operator.**  For a transversely
divergence-free velocity and a nonnegative diffusivity the real part of the
adjoint energy pairing is bounded by `‖∇⊥ u‖_∞ ‖b‖²`, with the same constant
`M_u = ‖transverseStretchingCoefficient u‖` as for the forward operator and
uniformly in the axial index `K`.

This is the adjoint half of the Lumer–Phillips hypothesis: the transposed
stretching matrix has the same real quadratic form as the stretching matrix, so
no new coefficient norm is needed. -/
theorem re_inner_reducedInductionAdjointAction_le
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (ε : ℝ) (hε : 0 ≤ ε) (K : ℤ) (b : TransverseC3H2) :
    (inner ℂ (transverseH2Embedding b)
      (reducedInductionAdjointAction u ε K b)).re ≤
      ‖transverseStretchingCoefficient u‖ *
        ‖transverseH2Embedding b‖ ^ 2 := by
  have hreal := re_inner_reducedInductionAdjointAction_eq u hu ε K b
  have hstretch := re_inner_reducedInductionStretchingTranspose_le u b
  have haxial : (0 : ℝ) ≤ (2 * Real.pi * (K : ℝ)) ^ 2 := sq_nonneg _
  have hgrad := reducedTransverseGradientEnergy_nonneg b
  have hnorm : (0 : ℝ) ≤ ‖transverseH2Embedding b‖ ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hε hgrad, mul_nonneg (mul_nonneg hε haxial) hnorm]

/-- **Uniqueness of forward strong solutions of the adjoint equation.**  The
half-plane bound `re_inner_reducedInductionAdjointAction_le` feeds
`DomainOperator.forwardStrongSolutionsUnique_of_re_inner_le` with
`M = ‖transverseStretchingCoefficient u‖`, exactly as for the forward
operator. -/
theorem reducedInductionAdjointOperator_forwardStrongSolutionsUnique
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (ε : ℝ) (hε : 0 ≤ ε) (K : ℤ) :
    (reducedInductionAdjointOperator u ε K).ForwardStrongSolutionsUnique :=
  DomainOperator.forwardStrongSolutionsUnique_of_re_inner_le _
    ‖transverseStretchingCoefficient u‖
    (fun b ↦ re_inner_reducedInductionAdjointAction_le u hu ε hε K b)

end

end FastDynamo
