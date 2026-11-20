/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.Assembly.AxialSectorDomain
public import LeanPool.FastDynamo.Dynamics.EnergyIdentity

/-!
# Sectorial estimates for the induction operator on the product torus

The induction operator `productInductionOperator u ε` of the paper (`eq:induction`, §1.1) on the
product torus `T² × T` is a sum of the diffusion `εΔ`, the transport term
`productInductionTransport u = (u·∇)`, and the stretching term `(B·∇)u`.  This module collects the
energy estimates that the analyticity of the semigroup of `lem:semigroup-spectral-growth`
(Appendix A) and the estimates in negative Sobolev norms use:

* the real part of the quadratic form with the gradient term retained,
  `Re ⟨B, A B⟩ ≤ ‖∇u‖ ‖B‖² − ε ‖∇B‖²`;
* the bound of the transport term by the gradient energy, `‖(u·∇)B‖ ≤ c ‖∇B‖`;
* the skewness of the transport term;
* the sector condition `|Im ⟨B, A B⟩| ≤ ω ‖B‖² − Re ⟨B, A B⟩` for `ε > 0`.

The paper does not state these estimates; they are the quantitative form of the energy competition
`eq:energy-competition`.  The inner product is the Mathlib one (conjugate linear in the first
slot), so the quadratic form is `inner ℂ (ι B) (A B)`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-- The transport part `(u·∇)B = ∑_{j<2} u_j ∂_j B + u₃ ∂₃ B` of the induction action on `H²`
fields of the product torus. -/
def productInductionTransport (u : TransverseRealW1Inf) : ProductC3H2 →L[ℂ] ProductC3L2 :=
  productInductionTransverseTransport u + productInductionAxialTransport u

/-- The induction action is the diffusion minus transport plus stretching. -/
theorem productInductionAction_eq_transport (u : TransverseRealW1Inf) (ε : ℝ)
    (B : ProductC3H2) :
    productInductionAction u ε B =
      (ε : ℂ) • productLaplacianFromH2 B - productInductionTransport u B +
        productInductionStretching u B := by
  simp only [productInductionAction, productInductionTransport, productInductionDiffusion,
    add_apply, sub_apply, smul_apply]
  abel

/-- The gradient energy is nonnegative. -/
theorem productGradientEnergy_nonneg (B : ProductC3H2) : 0 ≤ productGradientEnergy B := by
  unfold productGradientEnergy
  positivity

/-- The real part of the quadratic form of the stretching term is bounded by
`‖∇u‖ ‖B‖²` (with `‖∇u‖ = transverseStretchingCoefficient u`). -/
private theorem re_inner_productInductionStretching_le (u : TransverseRealW1Inf)
    (hu : IsTransverseDivergenceFree u) (B : ProductC3H2) :
    (inner ℂ (productH2Embedding B) (productInductionStretching u B)).re ≤
      ‖transverseStretchingCoefficient u‖ * ‖productH2Embedding B‖ ^ 2 := by
  have h := re_inner_productInductionAction_le u hu (le_refl (0 : ℝ)) B
  rwa [re_inner_productInductionAction_eq u hu 0 B, zero_mul, sub_zero] at h

/-- **The energy inequality with the gradient term.**  For a divergence-free transverse velocity,
`Re ⟨B, A_{ε,u} B⟩ ≤ ‖∇u‖ ‖B‖² − ε ‖∇B‖²` for every `B ∈ H²` and every `ε`; this is the
inequality form of `eq:energy-competition`. -/
theorem re_inner_productInductionAction_le_sub (u : TransverseRealW1Inf)
    (hu : IsTransverseDivergenceFree u) (ε : ℝ) (B : ProductC3H2) :
    (inner ℂ (productH2Embedding B) (productInductionAction u ε B)).re ≤
      ‖transverseStretchingCoefficient u‖ * ‖productH2Embedding B‖ ^ 2 -
        ε * productGradientEnergy B := by
  rw [re_inner_productInductionAction_eq u hu ε B]
  linarith [re_inner_productInductionStretching_le u hu B]

/-- **The transport term is controlled by the gradient energy**: `‖(u·∇)B‖ ≤ c ‖∇B‖` with
`c` depending on `u` only, because the velocity is bounded. -/
theorem exists_norm_productInductionTransport_le (u : TransverseRealW1Inf) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ B : ProductC3H2,
      ‖productInductionTransport u B‖ ≤ c * Real.sqrt (productGradientEnergy B) := by
  set f : Fin 2 → ProductC3L2 →L[ℂ] ProductC3L2 := fun j ↦
    scalarVectorMulProduct
      (pullTransverseScalarLInf (transverseW1InfComplexValueCoordLInf j.castSucc u)) with hf
  set g : ProductC3L2 →L[ℂ] ProductC3L2 :=
    scalarVectorMulProduct
      (pullTransverseScalarLInf (transverseW1InfComplexValueCoordLInf 2 u)) with hg
  refine ⟨∑ j : Fin 2, ‖f j‖ + ‖g‖, by positivity, fun B ↦ ?_⟩
  have hs : ∀ j : Fin 2, ‖productTransverseDerivFromH2 j B‖ ≤
      Real.sqrt (productGradientEnergy B) := by
    intro j
    refine Real.le_sqrt_of_sq_le ?_
    unfold productGradientEnergy
    have := Finset.single_le_sum (f := fun j : Fin 2 ↦ ‖productTransverseDerivFromH2 j B‖ ^ 2)
      (fun i _ ↦ by positivity) (Finset.mem_univ j)
    nlinarith [sq_nonneg ‖productAxialDerivFromH2 B‖]
  have ha : ‖productAxialDerivFromH2 B‖ ≤ Real.sqrt (productGradientEnergy B) := by
    refine Real.le_sqrt_of_sq_le ?_
    unfold productGradientEnergy
    nlinarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ (α := Fin 2)) ↦
      sq_nonneg ‖productTransverseDerivFromH2 j B‖)]
  have e : productInductionTransport u B =
      ∑ j : Fin 2, f j (productTransverseDerivFromH2 j B) + g (productAxialDerivFromH2 B) := by
    simp [productInductionTransport, productInductionTransverseTransport_apply,
      productInductionAxialTransport_apply, hf, hg]
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [add_mul, Finset.sum_mul]
  refine add_le_add (norm_sum_le _ _ |>.trans (Finset.sum_le_sum fun j _ ↦ ?_)) ?_
  · exact ((f j).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hs j) (norm_nonneg _))
  · exact (g.le_opNorm _).trans (mul_le_mul_of_nonneg_left ha (norm_nonneg _))

/-- **Skewness of the transport term.**  For divergence-free `u` the real part of the
sesquilinear pairing of `ι B` with `(u·∇) C` is minus that of `(u·∇) B` with `ι C`: the
polarisation of the vanishing of `Re ⟨B, (u·∇) B⟩`. -/
theorem re_inner_productInductionTransport_skew (u : TransverseRealW1Inf)
    (hu : IsTransverseDivergenceFree u) (B C : ProductC3H2) :
    (inner ℂ (productH2Embedding B) (productInductionTransport u C)).re =
      -(inner ℂ (productInductionTransport u B) (productH2Embedding C)).re := by
  have hq : ∀ X : ProductC3H2,
      (inner ℂ (productH2Embedding X) (productInductionTransport u X)).re = 0 := by
    intro X
    rw [productInductionTransport, add_apply, inner_add_right, Complex.add_re,
      re_inner_productInductionTransverseTransport_eq_zero u hu,
      re_inner_productInductionAxialTransport_eq_zero u, add_zero]
  have h := hq (B + C)
  simp only [map_add, inner_add_left, inner_add_right, Complex.add_re, hq B, hq C,
    zero_add] at h
  have := inner_re_symm (𝕜 := ℂ) (productH2Embedding C) (productInductionTransport u B)
  simp only [RCLike.re_to_complex] at this
  linarith

/-- The stretching term is bounded by the `L²` norm of the field. -/
theorem exists_norm_productInductionStretching_le (u : TransverseRealW1Inf) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ B : ProductC3H2,
      ‖productInductionStretching u B‖ ≤ c * ‖productH2Embedding B‖ := by
  refine ⟨∑ j : Fin 2, ‖vectorScalarMulProduct
    (pullTransverseVectorLInf (transverseW1InfComplexDerivLInf j u))‖ *
      ‖productCoordL2 j.castSucc‖, by positivity, fun B ↦ ?_⟩
  rw [productInductionStretching_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  rw [mul_assoc]
  gcongr
  exact ContinuousLinearMap.le_opNorm _ _

/-- Young's inequality in the form used for the sector estimate. -/
private theorem young_aux {ε c x s : ℝ} (hε : 0 < ε) :
    c * x * s ≤ ε * s ^ 2 + c ^ 2 / (4 * ε) * x ^ 2 := by
  rw [← sub_nonneg]
  have : ε * s ^ 2 + c ^ 2 / (4 * ε) * x ^ 2 - c * x * s = (2 * ε * s - c * x) ^ 2 / (4 * ε) := by
    field_simp
    ring
  rw [this]
  positivity

/-- The arithmetic of the sector estimate. -/
private theorem sector_arith {M d c ε x s G R a b : ℝ} (hε : 0 < ε) (hG : s ^ 2 = G)
    (hre : R ≤ M * x ^ 2 - ε * G) (hT : |a| ≤ c * x * s) (hS : |b| ≤ d * x ^ 2) :
    |-a + b| ≤ (M + d + c ^ 2 / (4 * ε)) * x ^ 2 - R := by
  have hy := young_aux (c := c) (x := x) (s := s) hε
  have h1 := abs_add_le (-a) b
  rw [abs_neg] at h1
  rw [← hG] at hre
  linarith

/-- **The sector condition.**  For a divergence-free transverse velocity and `ε > 0` there is
`ω` such that `|Im ⟨B, A_{ε,u} B⟩| ≤ ω ‖B‖² − Re ⟨B, A_{ε,u} B⟩` for all `B ∈ H²`: the imaginary
part comes from transport and stretching only and is absorbed by the gradient term
`ε ‖∇B‖²` through Young's inequality.  This is the numerical-range condition for analyticity of
the semigroup of `lem:semigroup-spectral-growth`. -/
theorem exists_productInduction_sectorial (u : TransverseRealW1Inf)
    (hu : IsTransverseDivergenceFree u) {ε : ℝ} (hε : 0 < ε) :
    ∃ ω : ℝ, ∀ B : ProductC3H2,
      |(inner ℂ (productH2Embedding B) (productInductionAction u ε B)).im| ≤
        ω * ‖productH2Embedding B‖ ^ 2 -
          (inner ℂ (productH2Embedding B) (productInductionAction u ε B)).re := by
  obtain ⟨c, hc0, hc⟩ := exists_norm_productInductionTransport_le u
  obtain ⟨d, hd0, hd⟩ := exists_norm_productInductionStretching_le u
  refine ⟨‖transverseStretchingCoefficient u‖ + d + c ^ 2 / (4 * ε), fun B ↦ ?_⟩
  have him : (inner ℂ (productH2Embedding B) (productInductionAction u ε B)).im =
      -(inner ℂ (productH2Embedding B) (productInductionTransport u B)).im +
        (inner ℂ (productH2Embedding B) (productInductionStretching u B)).im := by
    rw [productInductionAction_eq_transport, inner_add_right, inner_sub_right,
      inner_smul_right, inner_productH2Embedding_laplacian_eq_neg_gradientEnergy]
    simp
  have hT : |(inner ℂ (productH2Embedding B) (productInductionTransport u B)).im| ≤
      c * ‖productH2Embedding B‖ * Real.sqrt (productGradientEnergy B) := by
    refine (Complex.abs_im_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    calc ‖productH2Embedding B‖ * ‖productInductionTransport u B‖
        ≤ ‖productH2Embedding B‖ * (c * Real.sqrt (productGradientEnergy B)) := by
          gcongr; exact hc B
      _ = _ := by ring
  have hS : |(inner ℂ (productH2Embedding B) (productInductionStretching u B)).im| ≤
      d * ‖productH2Embedding B‖ ^ 2 := by
    refine (Complex.abs_im_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    calc ‖productH2Embedding B‖ * ‖productInductionStretching u B‖
        ≤ ‖productH2Embedding B‖ * (d * ‖productH2Embedding B‖) := by gcongr; exact hd B
      _ = _ := by ring
  rw [him]
  exact sector_arith hε (Real.sq_sqrt (productGradientEnergy_nonneg B))
    (re_inner_productInductionAction_le_sub u hu ε B) hT hS

end

end FastDynamo
