/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.LiteralFriedrichsCommutator
public import LeanPool.FastDynamo.Dynamics.Ideal.LipschitzTestFields
public import LeanPool.FastDynamo.Dynamics.Ideal.WeakSolution
public import LeanPool.FastDynamo.Dynamics.MainLagrangianClauses

/-!
# The mollifier between the product `H²` graph and the literal three-torus

Remark 1.7 of the paper states that the resistive semigroups `e^{tL_{ε,u}}` converge strongly,
locally uniformly in time, to the ideal solution group `𝒯₀(t)` as `ε → 0`.  The proof compares the
resistive orbit with the mollified ideal orbit `J_δ 𝒯₀(t)B` by an energy estimate.  The resistive
semigroup acts on the product torus `T² × T¹`, with generator defined on the Fourier-graph `H²`
domain `ProductC3H2`; the ideal group, the mollifier `J_δ` and the Friedrichs commutator live on
the literal three-torus `Torus 3`.  This module connects the two models.

## Contents

* `literalC3L2_ext_literalFourierCoeff`, `literalFourierCoeff_toLiteralC3L2`,
  `productCoeffCLM_toLiteralC3L2_symm` — the Fourier dictionary between the two models.
* `productMollifyH2 δ : ProductC3L2 →L[ℂ] ProductC3H2` — the mollifier with values in the product
  `H²` graph; `productH2Embedding_productMollifyH2` — its field is `J_δ f`, transported.
* `toLiteralC3L2_productInductionAction_productMollifyH2` — the induction action on `J_δ f`,
  transported: `ε ΔJ_δ f − ∑ⱼ uⱼ ∂ⱼJ_δ f + (J_δ f·∇)u`.  The transport term uses the stored value
  of the velocity, read through its continuous representative; the stretching term uses the
  stored derivatives, identified with the derivative of the literal velocity at every point
  (`literalFDeriv_literalVelocity_single_castSucc`).
* `hasDerivAt_literalMollify_mainIdealGroup` — `t ↦ J_δ 𝒯₀(t)B` is differentiable with derivative
  `J_δ (𝒯₀(t)B·∇)u − ∑ⱼ ∂ⱼJ_δ(uⱼ 𝒯₀(t)B)`.  The weak form of `IsIdealSolutionGroup`, tested with
  the characters `e_m eᵢ`, gives the Fourier coefficients of `𝒯₀(t)B` in integrated form
  (`literalFourierCoeff_idealGroup_sub`); `J_δ` and `∂ⱼJ_δ` are Fourier multipliers.
* `literalInductionSemigroup_apply_coe` — the resistive semigroup on `L²_σ(T³; ℂ³)` is the product
  semigroup, read through `toLiteralC3L2`.

The mollifier has no counterpart in the paper, which derives Remark 1.7 from the
Trotter–Kato theorem and the commutator lemma of DiPerna–Lions.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

/-! ## The Fourier dictionary between the two models -/

/-- A field on the literal three-torus is determined by its Fourier coefficients. -/
theorem literalC3L2_ext_literalFourierCoeff {X Y : LiteralC3L2}
    (h : ∀ m i, literalFourierCoeff X m i = literalFourierCoeff Y m i) : X = Y := by
  rw [← sum_literalSingleL2_literalCoordL2 X, ← sum_literalSingleL2_literalCoordL2 Y]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg _ ?_
  apply flatTorus3FourierBasis.repr.injective
  ext m
  simp only [HilbertBasis.repr_apply_apply]
  exact h m i

/-- The literal Fourier coefficients of a transported product field are its product Fourier
coefficients. -/
theorem literalFourierCoeff_toLiteralC3L2 (W : ProductC3L2) (m : Fin 3 → ℤ) (i : Fin 3) :
    literalFourierCoeff (toLiteralC3L2 W) m i =
      productCoeffCLM (fun j : Fin 2 ↦ m j.castSucc) (m (Fin.last 2)) i W :=
  (productCoeffCLM_eq_inner_flatTorus3FourierBasis i m W).symm

/-- The product Fourier coefficients of a field transported back from the literal three-torus. -/
theorem productCoeffCLM_toLiteralC3L2_symm (n : TransverseFrequency) (k : ℤ) (i : Fin 3)
    (X : LiteralC3L2) :
    productCoeffCLM n k i (toLiteralC3L2.symm X) =
      literalFourierCoeff X (Fin.snoc n k : Fin 3 → ℤ) i := by
  have h := literalFourierCoeff_toLiteralC3L2 (toLiteralC3L2.symm X)
    (Fin.snoc n k : Fin 3 → ℤ) i
  simp only [LinearIsometryEquiv.apply_symm_apply, Fin.snoc_castSucc, Fin.snoc_last] at h
  exact h.symm

/-! ## The mollifier with values in the product `H²` graph -/

/-- The symbol `σ_δ` of the mollifier has modulus at most one. -/
theorem norm_mollifierSymbol_le (δ : ℝ) (m : Fin 3 → ℤ) : ‖mollifierSymbol δ m‖ ≤ 1 := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq_of_le ?_
    (integral_abs_mollifierKernel_le δ))
  congr 1
  funext z
  rw [norm_mul, norm_translationPhase, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- A bound for the weighted symbol `(1 + 4π²|m|²) σ_δ(m)`, at least one. -/
def productMollifyBound (δ : ℝ) : ℝ :=
  1 + (2 * Real.pi) ^ 2 * |Classical.choose (exists_bound_sq_mul_mollifierSymbol δ)|

/-- The bound `productMollifyBound δ` is positive. -/
theorem productMollifyBound_pos (δ : ℝ) : 0 < productMollifyBound δ := by
  unfold productMollifyBound
  positivity

/-- The `H²` weight times the symbol of the mollifier at the product frequency `(n, k)`. -/
def productMollifySymbol (δ : ℝ) (n : TransverseFrequency) (k : ℤ) : ℂ :=
  (productH2Weight n k : ℂ) * mollifierSymbol δ (Fin.snoc n k : Fin 3 → ℤ)

/-- The weighted symbol is bounded by `productMollifyBound δ`. -/
theorem norm_productMollifySymbol_le (δ : ℝ) (n : TransverseFrequency) (k : ℤ) :
    ‖productMollifySymbol δ n k‖ ≤ productMollifyBound δ := by
  set m : Fin 3 → ℤ := Fin.snoc n k
  have hC := Classical.choose_spec (exists_bound_sq_mul_mollifierSymbol δ) m
  have hsum : (∑ j : Fin 3, ((m j : ℝ)) ^ 2) = (∑ j : Fin 2, ((n j : ℝ)) ^ 2) + (k : ℝ) ^ 2 := by
    simp only [m, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  rw [hsum] at hC
  have hw : 0 ≤ productH2Weight n k := (productH2Weight_pos n k).le
  rw [productMollifySymbol, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw, productH2Weight,
    productMollifyBound]
  have hσ := norm_mollifierSymbol_le δ m
  have hpi : 0 ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
  have hC' := hC.trans (le_abs_self _)
  nlinarith [norm_nonneg (mollifierSymbol δ m)]

/-- The normalised weighted symbol, of modulus at most one. -/
theorem norm_productMollifySymbol_div_le (δ : ℝ) (k : ℤ) (n : TransverseFrequency) :
    ‖productMollifySymbol δ n k / (productMollifyBound δ : ℂ)‖ ≤ 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (productMollifyBound_pos δ).le]
  exact div_le_one_of_le₀ (norm_productMollifySymbol_le δ n k) (productMollifyBound_pos δ).le

/-- The weighted Fourier coefficients `(1 + 4π²(|n|² + k²)) σ_δ(n, k) f̂ᵢ(n, k)` of the mollified
field. -/
def productMollifyCoeffs (δ : ℝ) : ProductC3L2 →L[ℂ] WeightedProductC3Coeffs :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin 3 ↦ ProductScalarFourierL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ (productMollifyBound δ : ℂ) •
      (nestedScalarMultiplier (fun k n ↦ productMollifySymbol δ n k / (productMollifyBound δ : ℂ))
        (norm_productMollifySymbol_div_le δ)).comp
      ((productScalarFourierAnalysisNested.toContinuousLinearEquiv :
        ProductScalarL2 →L[ℂ] ProductScalarFourierL2).comp (productCoordL2 i)))

/-- The entries of `productMollifyCoeffs δ f`. -/
theorem productMollifyCoeffs_apply (δ : ℝ) (f : ProductC3L2) (i : Fin 3) (k : ℤ)
    (n : TransverseFrequency) :
    productMollifyCoeffs δ f i k n = productMollifySymbol δ n k * productCoeffCLM n k i f := by
  have hB : (productMollifyBound δ : ℂ) ≠ 0 := by
    exact_mod_cast (productMollifyBound_pos δ).ne'
  change (productMollifyBound δ : ℂ) * (productMollifySymbol δ n k / (productMollifyBound δ : ℂ) *
    productScalarFourierAnalysisNested (productCoordL2 i f) k n) = _
  rw [productScalarFourierAnalysisNested_coord_eq_productCoeffCLM]
  field_simp

/-- The mollified field, transported to the product torus. -/
def productMollifyL2 (δ : ℝ) : ProductC3L2 →L[ℂ] ProductC3L2 :=
  (toLiteralC3L2.symm.toContinuousLinearEquiv : LiteralC3L2 →L[ℂ] ProductC3L2).comp
    ((literalMollify δ).comp
      (toLiteralC3L2.toContinuousLinearEquiv : ProductC3L2 →L[ℂ] LiteralC3L2))

/-- The product Fourier coefficients of the mollified field are those of the field, multiplied by
the symbol `σ_δ`. -/
theorem productCoeffCLM_productMollifyL2 (δ : ℝ) (f : ProductC3L2) (n : TransverseFrequency)
    (k : ℤ) (i : Fin 3) :
    productCoeffCLM n k i (productMollifyL2 δ f) =
      mollifierSymbol δ (Fin.snoc n k : Fin 3 → ℤ) * productCoeffCLM n k i f := by
  change productCoeffCLM n k i (toLiteralC3L2.symm (literalMollify δ (toLiteralC3L2 f))) = _
  rw [productCoeffCLM_toLiteralC3L2_symm, literalFourierCoeff,
    inner_flatTorus3FourierBasis_literalMollify, ← literalFourierCoeff,
    literalFourierCoeff_toLiteralC3L2]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- **The mollifier `J_δ` with values in the product `H²` graph**: the field
`J_δ f`, transported to the product torus, together with its weighted Fourier coefficients. -/
def productMollifyH2 (δ : ℝ) : ProductC3L2 →L[ℂ] ProductC3H2 :=
  ((productMollifyL2 δ).prod (productMollifyCoeffs δ)).codRestrict productH2Submodule
    fun f ↦ (mem_productH2Submodule_iff _ _).2 fun n k i ↦ by
      refine (productMollifyCoeffs_apply δ f i k n).trans ?_
      refine Eq.trans ?_ (congrArg _ (productCoeffCLM_productMollifyL2 δ f n k i)).symm
      rw [productMollifySymbol, mul_assoc]

/-- The field stored in `productMollifyH2 δ f` is `J_δ f`, transported to the product torus. -/
theorem productH2Embedding_productMollifyH2 (δ : ℝ) (f : ProductC3L2) :
    productH2Embedding (productMollifyH2 δ f) =
      toLiteralC3L2.symm (literalMollify δ (toLiteralC3L2 f)) :=
  rfl

/-! ## Derivatives of the mollified field -/

/-- A transverse derivative of the mollified field, transported to the literal three-torus, is
`∂ⱼ J_δ`. -/
theorem toLiteralC3L2_productTransverseDerivFromH2_productMollifyH2 (δ : ℝ) (j : Fin 2)
    (f : ProductC3L2) :
    toLiteralC3L2 (productTransverseDerivFromH2 j (productMollifyH2 δ f)) =
      literalMollifyDeriv δ j.castSucc (toLiteralC3L2 f) := by
  refine literalC3L2_ext_literalFourierCoeff fun m i ↦ ?_
  have hs : (Fin.snoc (fun j : Fin 2 ↦ m j.castSucc) (m (Fin.last 2)) : Fin 3 → ℤ) = m :=
    Fin.snoc_init_self m
  rw [literalFourierCoeff_toLiteralC3L2, productCoeffCLM_productTransverseDerivFromH2,
    productH2Embedding_productMollifyH2, productCoeffCLM_toLiteralC3L2_symm, hs,
    literalFourierCoeff, literalFourierCoeff, inner_flatTorus3FourierBasis_literalMollify,
    inner_flatTorus3FourierBasis_literalMollifyDeriv]
  ring

/-- The axial derivative of the mollified field, transported to the literal three-torus, is
`∂₃ J_δ`. -/
theorem toLiteralC3L2_productAxialDerivFromH2_productMollifyH2 (δ : ℝ) (f : ProductC3L2) :
    toLiteralC3L2 (productAxialDerivFromH2 (productMollifyH2 δ f)) =
      literalMollifyDeriv δ (Fin.last 2) (toLiteralC3L2 f) := by
  refine literalC3L2_ext_literalFourierCoeff fun m i ↦ ?_
  have hs : (Fin.snoc (fun j : Fin 2 ↦ m j.castSucc) (m (Fin.last 2)) : Fin 3 → ℤ) = m :=
    Fin.snoc_init_self m
  rw [literalFourierCoeff_toLiteralC3L2, productCoeffCLM_productAxialDerivFromH2,
    productH2Embedding_productMollifyH2, productCoeffCLM_toLiteralC3L2_symm, hs,
    literalFourierCoeff, literalFourierCoeff, inner_flatTorus3FourierBasis_literalMollify,
    inner_flatTorus3FourierBasis_literalMollifyDeriv]
  ring

/-! ## Almost-everywhere statements on the two models -/

/-- A property holding almost everywhere on the product torus holds almost everywhere on the
literal three-torus, read through the coordinate split. -/
theorem ae_literal_of_ae_product {q : ProductTorus3 → Prop} (hq : ∀ᵐ y ∂productMeasure, q y) :
    ∀ᵐ x : Torus 3, q (fun j : Fin 2 ↦ x j.castSucc, x (Fin.last 2)) := by
  have := (measurePreserving_productToLiteral.symm productToLiteral).quasiMeasurePreserving.ae hq
  simpa only [productToLiteral_symm_apply] using this

/-- A property holding almost everywhere on the transverse torus holds almost everywhere on the
literal three-torus, read on the two transverse coordinates. -/
theorem ae_literal_of_ae_transverse {q : TransverseTorus → Prop}
    (hq : ∀ᵐ y ∂transverseMeasure, q y) : ∀ᵐ x : Torus 3, q (fun j : Fin 2 ↦ x j.castSucc) :=
  ae_literal_of_ae_product (q := fun y ↦ q y.1)
    ((measurePreserving_fst (μ := transverseMeasure) (ν := axialMeasure)).quasiMeasurePreserving.ae
      hq)

/-! ## The velocity terms, transported to the literal three-torus -/

namespace ScaleFamily.TorusCellPlacement

open FullVelocityConcrete

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-- Multiplication by a component of the stored value of the velocity, transported to the
literal three-torus, is multiplication by the component of the literal velocity. -/
theorem toLiteralC3L2_scalarVectorMulProduct_value (htau : 0 ≤ tau) (j : Fin 3)
    (W : ProductC3L2) :
    toLiteralC3L2 (scalarVectorMulProduct (pullTransverseScalarLInf
        (transverseW1InfComplexValueCoordLInf j
          (parameterizedFullGlobalW1Inf h P angularSpeed axialSpeed tau htau))) W) =
      literalComponentMul
        (literalVelocity (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))
        (lipschitzWith_literalVelocity_parameterizedFullGlobalRealTorusSource
          h P angularSpeed axialSpeed tau htau).continuous j (toLiteralC3L2 W) := by
  set u := parameterizedFullGlobalW1Inf h P angularSpeed axialSpeed tau htau
  set c := pullTransverseScalarLInf (transverseW1InfComplexValueCoordLInf j u)
  refine Lp.ext ?_
  have hT := ae_literal_of_ae_transverse
    ((((EuclideanSpace.proj j : C3 →L[ℂ] ℂ).coeFn_compLpL (p := ∞)
      (transverseW1InfComplexValueLInf u)).and (transverseW1InfComplexValueLInf_coe_ae u)).and
      (transverseW1InfValue_parameterizedFullGlobalW1Inf_eq_realSource_ae
        h P angularSpeed axialSpeed tau htau))
  have hP := ae_literal_of_ae_product
    ((scalarVectorMulProduct_coe_ae c W).and (pullTransverseScalarLInf_coe_ae
      (transverseW1InfComplexValueCoordLInf j u)))
  filter_upwards [toLiteralC3L2_coe_ae (scalarVectorMulProduct c W), hP, hT,
    literalComponentMul_coe_ae _
      (lipschitzWith_literalVelocity_parameterizedFullGlobalRealTorusSource
        h P angularSpeed axialSpeed tau htau).continuous j (toLiteralC3L2 W),
    toLiteralC3L2_coe_ae W] with x h1 h2 h3 h4 h5
  rw [h1, h2.1, h2.2, h4, h5]
  congr 1
  change (EuclideanSpace.proj j : C3 →L[ℂ] ℂ).compLpL ∞ transverseMeasure
    (transverseW1InfComplexValueLInf u) _ = _
  have h32 : (transverseW1InfValue u : TransverseTorus → R3) (fun k ↦ x k.castSucc) =
      parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau
        (fun k ↦ x k.castSucc) := h3.2
  rw [h3.1.1, h3.1.2, h32]
  rfl

/-- The partial derivative of the literal velocity in a transverse direction is the stored
derivative of the velocity, at every point. -/
theorem literalFDeriv_literalVelocity_single_castSucc (htau : 0 ≤ tau) (x : Torus 3)
    (j : Fin 2) :
    literalFDeriv (literalVelocity
        (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) x
        (EuclideanSpace.single j.castSucc 1) =
      parameterizedHelicalGlobalRealTorusFirstDerivative h P angularSpeed axialSpeed j
          (fun k : Fin 2 ↦ x k.castSucc) +
        P.axialOffsetGlobalTorusDerivative tau j (fun k : Fin 2 ↦ x k.castSucc) := by
  set a : R3 := literalIocRepresentative x with ha
  have hxa : x = literalTorusPoint a := (literalTorusPoint_literalIocRepresentative x).symm
  have hd := (differentiable_parameterizedFullGlobalPeriodizedRealSource
    h P angularSpeed axialSpeed tau htau (flowPairProjection a)).hasFDerivAt.comp a
    flowPairProjection.hasFDerivAt
  have e : flowPairProjection (EuclideanSpace.single j.castSucc (1 : ℝ)) = pairBasis j := by
    fin_cases j <;> simp [pairBasis]
  have hpt : transverseTorusPoint (flowPairProjection a) =
      fun k : Fin 2 ↦ literalTorusPoint a k.castSucc := by
    funext k
    fin_cases k <;> simp [transverseTorusPoint, literalTorusPoint]
  rw [hxa, literalFDeriv_literalTorusPoint, literalVelocity_lift_eq h P angularSpeed axialSpeed tau,
    hd.fderiv, ContinuousLinearMap.comp_apply, e,
    fderiv_parameterizedFullGlobalPeriodizedRealSource_apply_pairBasis
      h P angularSpeed axialSpeed tau htau, hpt]

/-- The literal velocity does not depend on the axial coordinate. -/
theorem literalFDeriv_literalVelocity_single_last (htau : 0 ≤ tau) (x : Torus 3) :
    literalFDeriv (literalVelocity
        (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) x
        (EuclideanSpace.single (Fin.last 2) 1) = 0 := by
  set a : R3 := literalIocRepresentative x with ha
  have hxa : x = literalTorusPoint a := (literalTorusPoint_literalIocRepresentative x).symm
  have hd := (differentiable_parameterizedFullGlobalPeriodizedRealSource
    h P angularSpeed axialSpeed tau htau (flowPairProjection a)).hasFDerivAt.comp a
    flowPairProjection.hasFDerivAt
  have e : flowPairProjection (EuclideanSpace.single (Fin.last 2) (1 : ℝ)) = 0 := by
    simp [Fin.last]
  rw [hxa, literalFDeriv_literalTorusPoint, literalVelocity_lift_eq h P angularSpeed axialSpeed tau,
    hd.fderiv, ContinuousLinearMap.comp_apply, e, map_zero]

/-- **The stretching term, transported**: the product stretching `∑_{j<2} bⱼ ∂ⱼu`, built from
the stored derivatives of the velocity, is `literalStretchL2` of the literal velocity. -/
theorem toLiteralC3L2_stretching (htau : 0 ≤ tau) (W : ProductC3L2) :
    toLiteralC3L2 (∑ j : Fin 2, vectorScalarMulProduct (pullTransverseVectorLInf
        (transverseW1InfComplexDerivLInf j
          (parameterizedFullGlobalW1Inf h P angularSpeed axialSpeed tau htau)))
        (productCoordL2 j.castSucc W)) =
      literalStretchL2 (literalVelocity
        (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))
        (toLiteralC3L2 W) := by
  set u := parameterizedFullGlobalW1Inf h P angularSpeed axialSpeed tau htau
  set g : Fin 2 → ProductC3L2 := fun j ↦ vectorScalarMulProduct (pullTransverseVectorLInf
    (transverseW1InfComplexDerivLInf j u)) (productCoordL2 j.castSucc W)
  refine Lp.ext ?_
  have hc : ∀ j : Fin 2, (productCoordL2 j.castSucc W : ProductTorus3 → ℂ) =ᵐ[productMeasure]
      fun y ↦ (W : ProductTorus3 → C3) y j.castSucc := fun j ↦
    (EuclideanSpace.proj (𝕜 := ℂ) j.castSucc).coeFn_compLpL W
  have hg : ∀ j : Fin 2, (g j : ProductTorus3 → C3) =ᵐ[productMeasure]
      fun y ↦ (productCoordL2 j.castSucc W : ProductTorus3 → ℂ) y •
        (pullTransverseVectorLInf (transverseW1InfComplexDerivLInf j u) : ProductTorus3 → C3) y :=
    fun j ↦ vectorScalarMulProduct_coe_ae _ _
  have hpull : ∀ j : Fin 2,
      (pullTransverseVectorLInf (transverseW1InfComplexDerivLInf j u) : ProductTorus3 → C3)
        =ᵐ[productMeasure]
          fun y ↦ (transverseW1InfComplexDerivLInf j u : TransverseTorus → C3) y.1 :=
    fun j ↦ pullTransverseVectorLInf_coe_ae _
  have hP := ae_literal_of_ae_product ((Lp.coeFn_finsetSum Finset.univ g).and
    ((ae_all_iff.2 hg).and ((ae_all_iff.2 hpull).and (ae_all_iff.2 hc))))
  have hT := ae_literal_of_ae_transverse ((ae_all_iff.2 fun j ↦
    transverseW1InfComplexDerivLInf_coe_ae j u).and (ae_all_iff.2 fun j ↦
      transverseW1InfDeriv_parameterizedFullGlobalW1Inf_coe_ae
        h P angularSpeed axialSpeed tau htau j))
  filter_upwards [toLiteralC3L2_coe_ae (∑ j, g j), hP, hT,
    literalStretchL2_coe_ae h P angularSpeed axialSpeed tau htau (toLiteralC3L2 W),
    toLiteralC3L2_coe_ae W] with x h1 h2 h3 h4 h5
  rw [h1, h2.1, h4, literalStretch, h5, Finset.sum_apply]
  ext i
  rw [r3Complexify_apply]
  conv_rhs => rw [Fin.sum_univ_castSucc]
  rw [literalFDeriv_literalVelocity_single_last h P angularSpeed axialSpeed tau htau,
    PiLp.zero_apply, Complex.ofReal_zero, zero_mul, add_zero, WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [h2.2.1 j, h2.2.2.1 j, h3.1 j, h3.2 j, literalFDeriv_literalVelocity_single_castSucc
    h P angularSpeed axialSpeed tau htau]
  rw [h2.2.2.2 j, PiLp.smul_apply, complexifyR3_apply, smul_eq_mul, mul_comm]

end ScaleFamily.TorusCellPlacement

/-! ## Pairings with characters -/

/-- Pairing with the field `e eᵢ` reads the `i`-th component. -/
theorem inner_literalSingleL2 (i : Fin 3) (e : FlatTorus3ScalarL2) (X : LiteralC3L2) :
    inner ℂ (literalSingleL2 i e) X = inner ℂ e (literalCoordL2 i X) := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [literalSingleL2_coe_ae i e, literalCoordL2_coe_ae i X] with x h1 h2
  rw [h1, h2, inner_smul_left, EuclideanSpace.inner_single_left, map_one, one_mul,
    RCLike.inner_apply, mul_comm]

/-- Multiplication by a component of a real velocity is symmetric. -/
theorem inner_literalComponentMul (v : Torus 3 → R3) (hv : Continuous v) (j : Fin 3)
    (Y X : LiteralC3L2) :
    inner ℂ (literalComponentMul v hv j Y) X = inner ℂ Y (literalComponentMul v hv j X) := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [literalComponentMul_coe_ae v hv j Y, literalComponentMul_coe_ae v hv j X]
    with x h1 h2
  rw [h1, h2, inner_smul_left, inner_smul_right, Complex.conj_ofReal]

/-! ## The mollified ideal solution -/

namespace ScaleFamily.TorusCellPlacement

open FullVelocityConcrete

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-- **The Fourier coefficients of the ideal solution** satisfy the integrated equation
`B̂ᵢ(m)(s) − B̂ᵢ(m)(0) = ∫₀ˢ ((B·∇)u)^ᵢ(m) − ∑ⱼ 2πi mⱼ (uⱼB)^ᵢ(m)`: the weak form tested with
the character `e_m eᵢ`. -/
theorem literalFourierCoeff_idealGroup_sub (htau : 0 ≤ tau) (B : literalSolenoidalSubspace)
    (s : ℝ) (m : Fin 3 → ℤ) (i : Fin 3) :
    literalFourierCoeff (idealGroup h P angularSpeed axialSpeed tau s B) m i -
        literalFourierCoeff (idealGroup h P angularSpeed axialSpeed tau 0 B) m i =
      ∫ τ in (0 : ℝ)..s,
        (literalFourierCoeff (literalStretchL2 (literalVelocity
            (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))
            (idealGroup h P angularSpeed axialSpeed tau τ B)) m i -
          ∑ j : Fin 3, 2 * Real.pi * Complex.I * (m j : ℂ) *
            literalFourierCoeff (literalComponentMul (literalVelocity
              (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))
              (lipschitzWith_literalVelocity_parameterizedFullGlobalRealTorusSource
                h P angularSpeed axialSpeed tau htau).continuous j
              (idealGroup h P angularSpeed axialSpeed tau τ B)) m i) := by
  set v := literalVelocity (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)
  have hv := (lipschitzWith_literalVelocity_parameterizedFullGlobalRealTorusSource
    h P angularSpeed axialSpeed tau htau).continuous
  have hW := (isIdealSolutionGroup_idealGroup h P angularSpeed axialSpeed tau htau).weakSolution
    B |s|
  set c : (Fin 3 → ℤ) → Fin 3 → ℂ := fun _ i' ↦ if i' = i then 1 else 0
  set φ := literalTrigField {m} c
  have htrig : ∀ a : (Fin 3 → ℤ) → ℂ,
      literalTrigField {m} (fun m' i' ↦ a m' * c m' i') = a m • literalCharField m i := by
    intro a
    simp only [literalTrigField, Finset.sum_singleton, c, mul_ite, mul_one, mul_zero, ite_smul]
    rw [Finset.sum_eq_single i (fun b _ hb ↦ by
        rw [ite_eq_right hb]; exact zero_smul ℂ (literalCharField m b))
      (fun h ↦ absurd (Finset.mem_univ i) h), ite_eq_left rfl]
  have hφ : φ = literalCharField m i := by
    have h1 := htrig fun _ ↦ 1
    rw [one_smul] at h1
    rw [← h1]
    simp only [one_mul, φ]
  set e : LiteralC3L2 := literalSingleL2 i (flatTorus3FourierBasis m)
  have hφe : ∀ᵐ x ∂(volume : Measure (Torus 3)), φ x = (e : Torus 3 → C3) x := by
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure (Torus 3))
      (literalCharField m i)] with x hx
    rw [hφ, ← hx, toLp_literalCharField]
  set A : LiteralC3L2 := ∑ j : Fin 3, literalComponentMul v hv j
    ((2 * Real.pi * Complex.I * (m j : ℂ)) • e)
  have hadvA : literalAdvection v φ =ᵐ[volume] (A : Torus 3 → C3) := by
    filter_upwards [literalC3L2_coeFn_sum fun j ↦ literalComponentMul v hv j
        ((2 * Real.pi * Complex.I * (m j : ℂ)) • e),
      ae_all_iff.2 fun j ↦ literalComponentMul_coe_ae v hv j
        ((2 * Real.pi * Complex.I * (m j : ℂ)) • e),
      ae_all_iff.2 fun j ↦ Lp.coeFn_smul (2 * Real.pi * Complex.I * (m j : ℂ)) e, hφe]
      with x h1 h2 h3 h4
    rw [literalAdvection_literalTrigField, h1]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [h2 j, h3 j, Pi.smul_apply, ← h4]
    refine congrArg _ ((DFunLike.congr_fun (htrig fun m' ↦ 2 * Real.pi * Complex.I * (m' j : ℂ))
      x).trans ?_)
    rw [hφ]
    rfl
  have hmemφ : MemLp φ 2 (volume : Measure (Torus 3)) := (Lp.memLp e).ae_eq (hφe.mono
    fun x hx ↦ hx.symm)
  have hmemA : MemLp (literalAdvection v φ) 2 (volume : Measure (Torus 3)) :=
    (Lp.memLp A).ae_eq hadvA.symm
  have hF := idealWeakIdentity_of_isIdealTestField h P angularSpeed axialSpeed tau htau hW
    (isIdealTestField_literalTrigField _ _) hmemφ hmemA
    (⟨neg_nonpos.2 (abs_nonneg s), abs_nonneg s⟩ : (0 : ℝ) ∈ Set.Icc (-|s|) |s|)
    (⟨neg_abs_le s, le_abs_self s⟩ : s ∈ Set.Icc (-|s|) |s|)
  rw [MemLp.toLp_congr hmemφ (Lp.memLp e) hφe, MemLp.toLp_congr hmemA (Lp.memLp A) hadvA,
    Lp.toLp_coeFn, Lp.toLp_coeFn, IdealWeakIdentity] at hF
  have hcoeff : ∀ X : LiteralC3L2, inner ℂ e X = literalFourierCoeff X m i := fun X ↦
    inner_literalSingleL2 i _ X
  have hAX : ∀ X : LiteralC3L2, inner ℂ A X = -∑ j : Fin 3, 2 * Real.pi * Complex.I *
      (m j : ℂ) * literalFourierCoeff (literalComponentMul v hv j X) m i := by
    intro X
    rw [sum_inner, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hconj : (starRingEnd ℂ) (2 * Real.pi * Complex.I * (m j : ℂ)) =
        -(2 * Real.pi * Complex.I * (m j : ℂ)) := by
      simp [map_ofNat, Complex.conj_ofReal]
    rw [inner_literalComponentMul, inner_smul_left, hcoeff, hconj, neg_mul]
  simp only [hcoeff, hAX, ← sub_eq_add_neg] at hF
  exact hF

/-- **The mollified ideal solution is differentiable**:
`d/dt J_δ 𝒯₀(t)B = J_δ (𝒯₀(t)B·∇)u − ∑ⱼ ∂ⱼ J_δ (uⱼ 𝒯₀(t)B)`, at every time. -/
theorem hasDerivAt_literalMollify_idealGroup (htau : 0 ≤ tau) (δ : ℝ)
    (B : literalSolenoidalSubspace) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ literalMollify δ (idealGroup h P angularSpeed axialSpeed tau s B :
        LiteralC3L2))
      (literalMollify δ (literalStretchL2 (literalVelocity
          (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))
          (idealGroup h P angularSpeed axialSpeed tau t B)) -
        ∑ j : Fin 3, literalMollifyDeriv δ j (literalComponentMul (literalVelocity
          (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))
          (lipschitzWith_literalVelocity_parameterizedFullGlobalRealTorusSource
            h P angularSpeed axialSpeed tau htau).continuous j
          (idealGroup h P angularSpeed axialSpeed tau t B))) t := by
  set v := literalVelocity (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)
  set hv := (lipschitzWith_literalVelocity_parameterizedFullGlobalRealTorusSource
    h P angularSpeed axialSpeed tau htau).continuous
  set G : ℝ → LiteralC3L2 := fun s ↦ idealGroup h P angularSpeed axialSpeed tau s B
  have hG : Continuous G := by
    have : G = fun s ↦ idealTransport h P angularSpeed axialSpeed tau s B := by
      funext s
      exact idealGroup_coe h P angularSpeed axialSpeed tau htau s B
    rw [this]
    exact strongly_continuous_idealTransport h P angularSpeed axialSpeed tau htau B
  set F : ℝ → LiteralC3L2 := fun s ↦ literalMollify δ (literalStretchL2 v (G s)) -
    ∑ j : Fin 3, literalMollifyDeriv δ j (literalComponentMul v hv j (G s))
  have hF : Continuous F :=
    ((literalMollify δ).continuous.comp ((literalStretchL2 v).continuous.comp hG)).sub
      (continuous_finsetSum _ fun j _ ↦ (literalMollifyDeriv δ j).continuous.comp
        ((literalComponentMul v hv j).continuous.comp hG))
  have hint : ∀ s : ℝ, literalMollify δ (G s) =
      literalMollify δ (G 0) + ∫ τ in (0 : ℝ)..s, F τ := by
    intro s
    refine literalC3L2_ext_literalFourierCoeff fun m i ↦ ?_
    set ℓ : LiteralC3L2 →L[ℂ] ℂ := (innerSL ℂ (flatTorus3FourierBasis m)).comp (literalCoordL2 i)
    have hℓ : ∀ X, literalFourierCoeff X m i = ℓ X := fun X ↦ rfl
    have hJ : ∀ X, literalFourierCoeff (literalMollify δ X) m i =
        mollifierSymbol δ m * literalFourierCoeff X m i := fun X ↦
      inner_flatTorus3FourierBasis_literalMollify δ m i X
    have hFℓ : ∀ τ, literalFourierCoeff (F τ) m i = mollifierSymbol δ m *
        (literalFourierCoeff (literalStretchL2 v (G τ)) m i -
          ∑ j : Fin 3, 2 * Real.pi * Complex.I * (m j : ℂ) *
            literalFourierCoeff (literalComponentMul v hv j (G τ)) m i) := by
      intro τ
      simp only [F, literalFourierCoeff, map_sub, map_sum, inner_sub_right, inner_sum,
        inner_flatTorus3FourierBasis_literalMollify,
        inner_flatTorus3FourierBasis_literalMollifyDeriv, mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      ring
    have hsub : literalFourierCoeff (G s) m i - literalFourierCoeff (G 0) m i =
        ∫ τ in (0 : ℝ)..s, (literalFourierCoeff (literalStretchL2 v (G τ)) m i -
          ∑ j : Fin 3, 2 * Real.pi * Complex.I * (m j : ℂ) *
            literalFourierCoeff (literalComponentMul v hv j (G τ)) m i) :=
      literalFourierCoeff_idealGroup_sub h P angularSpeed axialSpeed tau htau B s m i
    rw [hℓ (_ + _), map_add, ← ContinuousLinearMap.intervalIntegral_comp_comm ℓ
      (hF.intervalIntegrable _ _)]
    simp only [← hℓ, hFℓ, intervalIntegral.integral_const_mul, hJ]
    rw [← hsub]
    ring
  rw [show (fun s ↦ literalMollify δ (G s)) = fun s ↦
      literalMollify δ (G 0) + ∫ τ in (0 : ℝ)..s, F τ from funext hint]
  exact ((hF.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add _

end ScaleFamily.TorusCellPlacement

open HorizontalMode ScaleFamily.TorusCellPlacement FullVelocityConcrete

/-! ## The induction action on mollified fields, at the velocity of the paper -/

/-- **The resistive induction action on a mollified field, transported to the literal
three-torus**: `A_ε J_δ f = ε Δ J_δ f − ∑ⱼ uⱼ ∂ⱼ J_δ f + (J_δ f · ∇)u`, at the velocity of the
paper. -/
theorem toLiteralC3L2_productInductionAction_productMollifyH2 (ε δ : ℝ) (f : ProductC3L2) :
    toLiteralC3L2 (productInductionAction mainVelocity ε (productMollifyH2 δ f)) =
      (ε : ℂ) • toLiteralC3L2 (productLaplacianFromH2 (productMollifyH2 δ f)) -
        (∑ j : Fin 3, literalComponentMul mainLiteralVelocity
            lipschitzWith_mainLiteralVelocity.continuous j
            (literalMollifyDeriv δ j (toLiteralC3L2 f))) +
        literalStretchL2 mainLiteralVelocity (literalMollify δ (toLiteralC3L2 f)) := by
  have hval : ∀ (j : Fin 3) (W : ProductC3L2),
      toLiteralC3L2 (scalarVectorMulProduct (pullTransverseScalarLInf
        (transverseW1InfComplexValueCoordLInf j mainVelocity)) W) =
      literalComponentMul mainLiteralVelocity lipschitzWith_mainLiteralVelocity.continuous j
        (toLiteralC3L2 W) := fun j W ↦
    toLiteralC3L2_scalarVectorMulProduct_value globalSeedInterface.smoothingWidth
      mainParameterChoice.placement globalSeedInterface.angularSpeed
      globalSeedInterface.axialSpeed mainParameterChoice.tau mainParameterChoice.tau_nonneg j W
  have hstr : ∀ W : ProductC3L2,
      toLiteralC3L2 (∑ j : Fin 2, vectorScalarMulProduct (pullTransverseVectorLInf
        (transverseW1InfComplexDerivLInf j mainVelocity)) (productCoordL2 j.castSucc W)) =
      literalStretchL2 mainLiteralVelocity (toLiteralC3L2 W) := fun W ↦
    toLiteralC3L2_stretching globalSeedInterface.smoothingWidth
      mainParameterChoice.placement globalSeedInterface.angularSpeed
      globalSeedInterface.axialSpeed mainParameterChoice.tau mainParameterChoice.tau_nonneg W
  have hemb : toLiteralC3L2 (productH2Embedding (productMollifyH2 δ f)) =
      literalMollify δ (toLiteralC3L2 f) := by
    rw [productH2Embedding_productMollifyH2, LinearIsometryEquiv.apply_symm_apply]
  rw [productInductionAction_apply, map_add, map_sub, map_sub, map_smul, map_sum]
  conv_rhs => rw [Fin.sum_univ_castSucc, ← sub_sub]
  congr 1
  · congr 1
    · congr 1
      refine Finset.sum_congr rfl fun j _ ↦ (hval _ _).trans ?_
      rw [toLiteralC3L2_productTransverseDerivFromH2_productMollifyH2]
    · refine (hval (Fin.last 2) _).trans ?_
      rw [toLiteralC3L2_productAxialDerivFromH2_productMollifyH2]
  · exact (hstr _).trans (by rw [hemb])

/-! ## The resistive semigroup on the literal three-torus -/

/-- The resistive semigroup on `L²_σ(T³; ℂ³)` is the product semigroup, read through the
transport `toLiteralC3L2`. -/
theorem literalInductionSemigroup_apply_coe {ε : ℝ} (hε : 0 < ε) (t : ℝ≥0)
    (B : literalSolenoidalSubspace) :
    ((literalInductionSemigroup mainVelocity mainVelocity_isTransverseDivergenceFree hε t B :
        literalSolenoidalSubspace) : LiteralC3L2) =
      toLiteralC3L2 (productInductionSemigroup mainVelocity mainVelocity_isTransverseDivergenceFree
        hε t (toLiteralC3L2.symm (B : LiteralC3L2))) :=
  rfl

/-- **The mollified ideal solution is differentiable** at the velocity of the paper:
`d/dt J_δ 𝒯₀(t)B = J_δ (𝒯₀(t)B·∇)u − ∑ⱼ ∂ⱼ J_δ (uⱼ 𝒯₀(t)B)`, at every time. -/
theorem hasDerivAt_literalMollify_mainIdealGroup (δ : ℝ) (B : literalSolenoidalSubspace)
    (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ literalMollify δ (mainIdealGroup s B : LiteralC3L2))
      (literalMollify δ (literalStretchL2 mainLiteralVelocity
          (mainIdealGroup t B)) -
        ∑ j : Fin 3, literalMollifyDeriv δ j (literalComponentMul mainLiteralVelocity
          lipschitzWith_mainLiteralVelocity.continuous j (mainIdealGroup t B))) t :=
  hasDerivAt_literalMollify_idealGroup globalSeedInterface.smoothingWidth
    mainParameterChoice.placement globalSeedInterface.angularSpeed
    globalSeedInterface.axialSpeed mainParameterChoice.tau mainParameterChoice.tau_nonneg δ B t

end

end FastDynamo
