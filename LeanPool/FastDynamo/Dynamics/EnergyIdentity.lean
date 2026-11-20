/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.StrongSolutionUniqueness
public import LeanPool.FastDynamo.Finish.RealSolution
public import LeanPool.FastDynamo.Analysis.ProductTransportEnergy

/-!
# The energy identity of the induction equation

The paper states the competition between stretching and diffusion as the formal energy identity
`eq:energy-competition` (§1.1),

`½ d/dt ‖B(t)‖₂² = ∫_{T³} B·(B·∇)u dx − ε ‖∇B‖₂²`,

a consequence of `curl(u × B) = (B·∇)u − (u·∇)B` for divergence-free fields and of the skew
symmetry of transport.  This module proves it, for the induction operator
`productInductionOperator u ε` on the product torus `T² × T` with its complete Fourier-graph
domain `ProductC3H2` (`H²` fields), in two forms.

* The operator form `re_inner_productInductionAction_eq`: for a divergence-free transverse
  velocity `u`, every `ε` and every `B ∈ H²`,
  `Re ⟨B, A_{ε,u} B⟩ = Re ⟨B, (B·∇)u⟩ − ε ‖∇B‖₂²`
  with `‖∇B‖₂² = ∑_{j<2} ‖∂_j B‖₂² + ‖∂₃ B‖₂²` (`productGradientEnergy`).  The transport
  terms contribute nothing: the transverse one by the weak Leibniz rule and `Div u = 0`, the
  axial one because `u₃` does not depend on `x₃`.  The diffusion term is evaluated on the Fourier
  coefficients.
* The dynamical form `hasDerivAt_half_norm_sq_of_isStrongSolution` (and
  `hasDerivAt_half_norm_sq_of_isForwardStrongSolution` at positive times for forward strong
  solutions): along a strong solution of `productInductionOperator u ε` the function
  `t ↦ ½‖B(t)‖₂²` is differentiable with the derivative above.

The paper states the identity formally and for real-valued fields.  The Lean statements hold for
complex-valued `H²` fields, with the real part of the `L²` pairing in place of the real integral
`∫ B·(B·∇)u`; for a real-valued field `B` (a field fixed by the conjugation) the pairing is real
and equals that integral.  Neither form uses `Div B = 0`; off divergence-free fields the
auxiliary operator is not the curl form `ε ΔB + curl(u × B)`, so the paper's identity is the
case `Div B = 0`.  Along forward strong solutions of the curl form itself with divergence-free
datum the identity is `hasDerivAt_half_norm_sq_of_isForwardStrongSolution_physical`
(`FastDynamo/Dynamics/Assembly/PhysicalInductionUniqueness.lean`).
`realStrongSolution_hasDerivAt_half_norm_sq` instantiates the dynamical form at the real
solution `B^ε(t)` of Theorem 1.2 (`thm:main`), the realified eigenmode curve of
`FastDynamo/Finish/RealSolution.lean`.  The inner product is the Mathlib one, conjugate linear in
the first slot, whereas the paper takes it linear in the first; the real part of the pairing is
the same for both.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-! ## The gradient energy -/

/-- The gradient energy `‖∇B‖₂² = ∑_{j<2} ‖∂_j B‖₂² + ‖∂₃ B‖₂²` of an `H²` field on the product
torus, through its transverse and axial weak derivatives. -/
def productGradientEnergy (B : ProductC3H2) : ℝ :=
  ∑ j : Fin 2, ‖productTransverseDerivFromH2 j B‖ ^ 2 + ‖productAxialDerivFromH2 B‖ ^ 2

/-! ## Diffusion -/

/-- Summing the pointwise identity `⟨a_i, y_i⟩ = −(⟨x₁_i, x₁_i⟩ + ⟨x₂_i, x₂_i⟩ + ⟨x₃_i, x₃_i⟩)`
over the index gives the same identity for the inner products in `ℓ²`. -/
private theorem inner_lp_eq_neg_sum {ι : Type*} {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    (a y x₁ x₂ x₃ : lp E 2)
    (h : ∀ i, inner ℂ (a i) (y i) =
      -(inner ℂ (x₁ i) (x₁ i) + inner ℂ (x₂ i) (x₂ i) + inner ℂ (x₃ i) (x₃ i))) :
    inner ℂ a y = -(inner ℂ x₁ x₁ + inner ℂ x₂ x₂ + inner ℂ x₃ x₃) := by
  have s₁ := lp.summable_inner (𝕜 := ℂ) x₁ x₁
  have s₂ := lp.summable_inner (𝕜 := ℂ) x₂ x₂
  have s₃ := lp.summable_inner (𝕜 := ℂ) x₃ x₃
  rw [lp.inner_eq_tsum a y, lp.inner_eq_tsum x₁ x₁, lp.inner_eq_tsum x₂ x₂,
    lp.inner_eq_tsum x₃ x₃]
  simp_rw [h]
  rw [tsum_neg, (s₁.add s₂).tsum_add s₃, s₁.tsum_add s₂]

/-- Periodic integration by parts for scalar fields on the product torus, on the Fourier side:
if the Fourier coefficients of `g₁, g₂, g₃, h` are those of `f` times `2πi n₁`, `2πi n₂`, `2πi k`
and `−4π²(n₁² + n₂² + k²)`, then `⟨f, h⟩ = −(‖g₁‖² + ‖g₂‖² + ‖g₃‖²)` as inner products. -/
private theorem inner_scalar_eq_neg_derivatives
    (f g₁ g₂ g₃ h : ProductScalarL2)
    (hg₁ : ∀ k n, productScalarFourierAnalysisNested g₁ k n =
      (2 * Real.pi * Complex.I * (n 0 : ℂ)) * productScalarFourierAnalysisNested f k n)
    (hg₂ : ∀ k n, productScalarFourierAnalysisNested g₂ k n =
      (2 * Real.pi * Complex.I * (n 1 : ℂ)) * productScalarFourierAnalysisNested f k n)
    (hg₃ : ∀ k n, productScalarFourierAnalysisNested g₃ k n =
      (2 * Real.pi * Complex.I * (k : ℂ)) * productScalarFourierAnalysisNested f k n)
    (hh : ∀ k n, productScalarFourierAnalysisNested h k n =
      -(productFrequencyEnergy n k : ℂ) * productScalarFourierAnalysisNested f k n) :
    inner ℂ f h = -(inner ℂ g₁ g₁ + inner ℂ g₂ g₂ + inner ℂ g₃ g₃) := by
  rw [← productScalarFourierAnalysisNested.inner_map_map f h,
    ← productScalarFourierAnalysisNested.inner_map_map g₁ g₁,
    ← productScalarFourierAnalysisNested.inner_map_map g₂ g₂,
    ← productScalarFourierAnalysisNested.inner_map_map g₃ g₃]
  refine inner_lp_eq_neg_sum _ _ _ _ _ fun k ↦ ?_
  refine inner_lp_eq_neg_sum _ _ _ _ _ fun n ↦ ?_
  rw [hg₁, hg₂, hg₃, hh]
  simp only [RCLike.inner_apply, productFrequencyEnergy, Fin.sum_univ_two, map_mul,
    Complex.conj_ofReal, Complex.conj_I, map_intCast, map_ofNat]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Diffusion on the product torus.**  For `B ∈ H²`, `⟨B, ΔB⟩ = −‖∇B‖₂²`: periodic integration
by parts, proved coordinatewise from the Fourier coefficients of `B`, of its weak derivatives and
of its weak Laplacian. -/
theorem inner_productH2Embedding_laplacian_eq_neg_gradientEnergy (B : ProductC3H2) :
    inner ℂ (productH2Embedding B) (productLaplacianFromH2 B) =
      -(productGradientEnergy B : ℂ) := by
  have hcoord : ∀ i : Fin 3,
      inner ℂ (productCoordL2 i (productH2Embedding B))
          (productCoordL2 i (productLaplacianFromH2 B)) =
        -(inner ℂ (productCoordL2 i (productTransverseDerivFromH2 0 B))
            (productCoordL2 i (productTransverseDerivFromH2 0 B)) +
          inner ℂ (productCoordL2 i (productTransverseDerivFromH2 1 B))
            (productCoordL2 i (productTransverseDerivFromH2 1 B)) +
          inner ℂ (productCoordL2 i (productAxialDerivFromH2 B))
            (productCoordL2 i (productAxialDerivFromH2 B))) := by
    intro i
    refine inner_scalar_eq_neg_derivatives _ _ _ _ _ ?_ ?_ ?_ ?_ <;> intro k n <;>
      simp only [productScalarFourierAnalysisNested_coord_eq_productCoeffCLM,
        productCoeffCLM_productTransverseDerivFromH2, productCoeffCLM_productAxialDerivFromH2,
        productCoeffCLM_productLaplacianFromH2]
  rw [inner_productC3L2_eq_sum_coord, Finset.sum_congr rfl fun i _ ↦ hcoord i]
  simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib]
  rw [← inner_productC3L2_eq_sum_coord, ← inner_productC3L2_eq_sum_coord,
    ← inner_productC3L2_eq_sum_coord]
  simp only [inner_self_eq_norm_sq_to_K, productGradientEnergy, Fin.sum_univ_two]
  push_cast
  rfl

/-! ## Transport -/

/-- The axial `H¹` derivative of the scalar certificate of the `i`-th coordinate of an `H²` field
is the `i`-th coordinate of its axial weak derivative. -/
private theorem productScalarAxialDeriv_productH2CoordToScalarH1
    (B : ProductC3H2) (i : Fin 3) :
    productScalarAxialDerivFromH1 (productH2CoordToScalarH1 i B) =
      productCoordL2 i (productAxialDerivFromH2 B) := by
  apply productScalarFourierAnalysisNested.injective
  apply lp.ext
  funext k
  apply lp.ext
  funext n
  rw [productScalarFourierAnalysisNested_axialDerivFromH1,
    productScalarFourierAnalysisNested_coord_eq_productCoeffCLM,
    productCoeffCLM_productAxialDerivFromH2,
    ← productScalarFourierAnalysisNested_coord_eq_productCoeffCLM,
    ← productScalarH1Embedding_productH2CoordToScalarH1]

/-- **Transverse transport is skew.**  For a divergence-free transverse velocity, the transverse
transport term has no real quadratic pairing with an `H²` field on the product torus. -/
theorem re_inner_productInductionTransverseTransport_eq_zero
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u) (B : ProductC3H2) :
    (inner ℂ (productH2Embedding B) (productInductionTransverseTransport u B)).re = 0 := by
  have hcoord : ∀ i : Fin 3,
      (inner ℂ (productCoordL2 i (productH2Embedding B))
        (productCoordL2 i (productInductionTransverseTransport u B))).re = 0 := by
    intro i
    rw [productInductionTransverseTransport_apply]
    simp only [map_sum, inner_sum]
    simp_rw [productCoordL2_scalarVectorMulProduct]
    rw [← productScalarH1Embedding_productH2CoordToScalarH1 B i]
    simp_rw [← productScalarTransverseDeriv_productH2CoordToScalarH1 B i]
    simpa only [Fin.sum_univ_two, Complex.add_re,
      re_inner_productVelocityCoordMul_derivative_eq_flip] using
        re_sum_transverse_velocity_transport_eq_zero u hu (productH2CoordToScalarH1 i B)
  rw [inner_productC3L2_eq_sum_coord]
  simp only [Fin.sum_univ_three, Complex.add_re, hcoord, zero_add]

/-- **Axial transport is skew.**  The axial transport term `u₃ ∂₃ B` has no real quadratic pairing
with an `H²` field, because the real coefficient `u₃` does not depend on `x₃`. -/
theorem re_inner_productInductionAxialTransport_eq_zero
    (u : TransverseRealW1Inf) (B : ProductC3H2) :
    (inner ℂ (productH2Embedding B) (productInductionAxialTransport u B)).re = 0 := by
  have hcoord : ∀ i : Fin 3,
      (inner ℂ (productCoordL2 i (productH2Embedding B))
        (productCoordL2 i (productInductionAxialTransport u B))).re = 0 := by
    intro i
    rw [productInductionAxialTransport_apply, productCoordL2_scalarVectorMulProduct,
      ← productScalarH1Embedding_productH2CoordToScalarH1 B i,
      ← productScalarAxialDeriv_productH2CoordToScalarH1 B i,
      inner_productVelocityCoordMul_selfAdjoint u 2 _ _]
    refine (inner_re_symm (𝕜 := ℂ) _ _).trans ?_
    exact re_inner_axial_velocity_eq_zero u _
  rw [inner_productC3L2_eq_sum_coord]
  simp only [Fin.sum_univ_three, Complex.add_re, hcoord, zero_add]

/-! ## The energy identity -/

/-- **Energy identity for the induction operator** (`eq:energy-competition`, operator form).
For a divergence-free transverse velocity `u`, every `ε` and every field `B ∈ H²` on the product
torus,

`Re ⟨B, A_{ε,u} B⟩ = Re ⟨B, (B·∇)u⟩ − ε ‖∇B‖₂²`,

where `(B·∇)u` is `productInductionStretching u B`.  Both transport terms drop out because
`Div u = 0` and `u₃` is independent of `x₃`.  The identity holds for complex `H²` fields, with
the real part of the pairing; for real-valued `B` the pairing is the integral
`∫ B·(B·∇)u` of the paper. -/
theorem re_inner_productInductionAction_eq
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u) (ε : ℝ) (B : ProductC3H2) :
    (inner ℂ (productH2Embedding B) (productInductionAction u ε B)).re =
      (inner ℂ (productH2Embedding B) (productInductionStretching u B)).re -
        ε * productGradientEnergy B := by
  have hdiff : (inner ℂ (productH2Embedding B)
      (productInductionDiffusion B)).re = -productGradientEnergy B := by
    have h := inner_productH2Embedding_laplacian_eq_neg_gradientEnergy B
    rw [productInductionDiffusion, h]
    simp
  simp only [productInductionAction, add_apply, sub_apply,
    smul_apply, inner_add_right,
    inner_sub_right, inner_smul_right, Complex.add_re, Complex.sub_re,
    re_inner_productInductionTransverseTransport_eq_zero u hu,
    re_inner_productInductionAxialTransport_eq_zero u, Complex.re_ofReal_mul, hdiff]
  ring

/-- **The energy identity along forward strong solutions** (`eq:energy-competition`, dynamical
form).  Along a forward strong solution `B` of `productInductionOperator u ε` with `u`
divergence-free, at every positive time `t`, `s ↦ ½‖B(s)‖₂²` is differentiable at `t` with
derivative `Re ⟨B(t), (B(t)·∇)u⟩ − ε ‖∇B(t)‖₂²`. -/
theorem hasDerivAt_half_norm_sq_of_isForwardStrongSolution
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u) (ε : ℝ)
    {B : ℝ → ProductC3H2} (h : (productInductionOperator u ε).IsForwardStrongSolution B)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ ↦ (1 / 2 : ℝ) * ‖productH2Embedding (B s)‖ ^ 2)
      ((inner ℂ (productH2Embedding (B t)) (productInductionStretching u (B t))).re -
        ε * productGradientEnergy (B t)) t := by
  have h₁ := ((productInductionOperator u ε).hasDerivAt_norm_embedding_sq_of_isForwardStrongSolution
    h ht).const_mul (1 / 2 : ℝ)
  refine h₁.congr_deriv ?_
  rw [← re_inner_productInductionAction_eq u hu ε (B t)]
  change 1 / 2 * (2 * (inner ℂ (productH2Embedding (B t))
    (productInductionAction u ε (B t))).re) = _
  ring

/-- **The energy identity along strong solutions** (`eq:energy-competition`, dynamical form).
Along a strong solution `B` of `productInductionOperator u ε` with `u` divergence-free, the
function `t ↦ ½‖B(t)‖₂²` is differentiable at every real time with derivative
`Re ⟨B(t), (B(t)·∇)u⟩ − ε ‖∇B(t)‖₂²`.  The solution need not be divergence-free; for a real-valued
`B` the first term is `∫ B·(B·∇)u`. -/
theorem hasDerivAt_half_norm_sq_of_isStrongSolution
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u) (ε : ℝ)
    {B : ℝ → ProductC3H2} (h : (productInductionOperator u ε).IsStrongSolution B) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (1 / 2 : ℝ) * ‖productH2Embedding (B s)‖ ^ 2)
      ((inner ℂ (productH2Embedding (B t)) (productInductionStretching u (B t))).re -
        ε * productGradientEnergy (B t)) t := by
  have h₁ := ((productInductionOperator u ε).hasDerivAt_norm_embedding_sq_of_hasDerivAt_embedding
    (h t)).const_mul (1 / 2 : ℝ)
  refine h₁.congr_deriv ?_
  rw [← re_inner_productInductionAction_eq u hu ε (B t)]
  change 1 / 2 * (2 * (inner ℂ (productH2Embedding (B t))
    (productInductionAction u ε (B t))).re) = _
  ring

/-- **The energy identity for the real solution of Theorem 1.2.**  The real solution
`B^ε(t) = Re(e^{tλ}V)` of `thm:main`, the realified eigenmode curve
`realifiedEigenTrajectoryH2 λ V` built from an eigenpair `(λ, V)` of
`productInductionOperator u ε`, satisfies `eq:energy-competition` at every time: `t ↦ ½‖B^ε(t)‖₂²`
is differentiable with derivative `Re ⟨B^ε(t), (B^ε(t)·∇)u⟩ − ε ‖∇B^ε(t)‖₂²`, the first term being
the real integral `∫ B^ε·(B^ε·∇)u` because `B^ε(t)` is real-valued. -/
theorem realStrongSolution_hasDerivAt_half_norm_sq
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u) (ε : ℝ) (eigenvalue : ℂ)
    (V : ProductC3H2) (hEigen : (productInductionOperator u ε).IsEigenpair eigenvalue V)
    (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ (1 / 2 : ℝ) *
        ‖productH2Embedding (realifiedEigenTrajectoryH2 eigenvalue V s)‖ ^ 2)
      ((inner ℂ (productH2Embedding (realifiedEigenTrajectoryH2 eigenvalue V t))
          (productInductionStretching u (realifiedEigenTrajectoryH2 eigenvalue V t))).re -
        ε * productGradientEnergy (realifiedEigenTrajectoryH2 eigenvalue V t)) t :=
  hasDerivAt_half_norm_sq_of_isStrongSolution u hu ε
    (realifiedEigenTrajectoryH2_isStrongSolution u ε eigenvalue V hEigen) t

end

end FastDynamo
