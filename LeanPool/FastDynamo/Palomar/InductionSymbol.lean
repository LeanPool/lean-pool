/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Palomar.FourierDictionary
public import LeanPool.FastDynamo.Dynamics.Assembly.SolenoidalGenerator
public import LeanPool.FastDynamo.Global.MainTheoremWitnesses
public import LeanPool.FastDynamo.MainTheoremStrengthened

/-!
# The Fourier symbol of the induction operator

The library realises the curl form `L_{ε,u} B = curl (u × B) + ε ΔB` of the induction operator,
for `B` in the product `H²` graph `ProductC3H2`, as the element
`productPhysicalInductionAction u ε B` of its Fourier model `ProductC3HMinus2` of `H⁻²`, which
stores the coefficient of a distribution at the product frequency `(n, k)` divided by the weight
`productH2Weight n k = 1 + 4π²(|n|² + k²)`.  The Challenge statement writes the same operator
through mathlib's Fourier coefficients on `T3 = UnitAddTorus (Fin 3)`:

  `inductionRHS u ε B m i = 2πi ∑ⱼ mⱼ ((uᵢBⱼ)^(m) − (uⱼBᵢ)^(m)) − 4π² ε |m|² B̂ᵢ(m)`.

This module proves that the two agree.

## The dictionary

* Frequencies: the product frequency `(n, k)` (transverse `n : Fin 2 → ℤ`, axial `k : ℤ`) is the
  frequency `Fin.snoc n k : Fin 3 → ℤ` of `T3`; conversely `m` is `(fun j ↦ m j.castSucc, m 2)`.
* Fields: a product field `W` is read on `T3` as `toLiteralC3L2 W`; its product coefficient at
  `(n, k)` is the Challenge coefficient at `Fin.snoc n k` (`productCoeffCLM_eq_mFourierCoeff`).
* The velocity: `u : TransverseRealW1Inf` stores an essentially bounded value field; for any
  pointwise representative `v` of it, the velocity on `T3` is the axially independent field
  `literalVelocity v`.  The multiplication `productScalarMul` by the stored component `uₐ`,
  transported to `T3`, is multiplication by `literalVelocity v · a`
  (`toLiteralC3L2_scalarVectorMulProduct_velocityCoord_ae`).  Since `inductionRHS` reads the
  products `uₐ Bᵦ` only through their Fourier coefficients, the choice of representative is
  immaterial.
* The cross product: the library's `u × B` has the coordinates `u₁B₂ − u₂B₁`, `u₂B₀ − u₀B₂`,
  `u₀B₁ − u₁B₀`, and its distributional curl is computed coordinatewise; collecting the terms
  gives the divergence form `curl (u × B)ᵢ = ∑ⱼ ∂ⱼ(uᵢBⱼ − uⱼBᵢ)` of the Challenge.

## Contents

* `toLiteralC3L2_scalarVectorMulProduct_velocityCoord_ae`,
  `productCoeffCLM_productCrossWithVelocity_zero`, `…_one`, `…_two` — the products `uₐBᵦ` and
  the cross product.
* `productPhysicalInductionAction_apply` — **lemma P**: the entry of
  `productPhysicalInductionAction u ε B` at `(i, k, n)` is
  `inductionRHS (literalVelocity v) ε B_lit (Fin.snoc n k) i / productH2Weight n k`;
  `productH2Weight_mul_productPhysicalInductionAction_apply` is the same at a frequency
  `m : Fin 3 → ℤ` of `T3`, with the weight multiplied out.
* `inductionRHS_eq_of_productL2ToHMinus2_eq` — an identity of the curl form in `H⁻²`
  with the embedding of an `L²` field `D` is the Challenge identity
  `D̂ᵢ(m) = inductionRHS … m i`.
* `mainLiteralEigenmode_clauses` — the eigenmode of `mainPhysicalClauses_holds`, transported to
  `T3`: it lies in `L2σ`, is non-zero, its coefficients vanish off the axial frequency `K`, and
  it solves `inductionRHS mainLiteralVelocity ε V = λ V̂`.
* `mFourierCoeff_generator_solenoidalInductionSemigroup`,
  `exists_mem_generator_solenoidalInductionSemigroup_domain` — the generator of the library's
  induction semigroup on `L²_σ`, transported to `T3`, has the coefficients
  `inductionRHS (literalVelocity v) ε` of the transported field.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory FastDynamoChallenge UnitAddTorus

/-! ## The frequency dictionary -/

/-- The Challenge frequency `Fin.snoc n k` has transverse part `n`. -/
theorem snocFrequency_apply_zero (n : TransverseFrequency) (k : ℤ) :
    (Fin.snoc n k : Fin 3 → ℤ) 0 = n 0 :=
  Fin.snoc_castSucc (α := fun _ ↦ ℤ) (p := n) (x := k) (i := 0)

/-- The Challenge frequency `Fin.snoc n k` has transverse part `n`. -/
@[simp] theorem snocFrequency_apply_one (n : TransverseFrequency) (k : ℤ) :
    (Fin.snoc n k : Fin 3 → ℤ) 1 = n 1 :=
  Fin.snoc_castSucc (α := fun _ ↦ ℤ) (p := n) (x := k) (i := 1)

/-- The Challenge frequency `Fin.snoc n k` has axial part `k`. -/
@[simp] theorem snocFrequency_apply_two (n : TransverseFrequency) (k : ℤ) :
    (Fin.snoc n k : Fin 3 → ℤ) 2 = k :=
  Fin.snoc_last (α := fun _ ↦ ℤ) (p := n) (x := k)

/-- A frequency of `T3` is the `Fin.snoc` of its transverse and axial parts. -/
theorem snocFrequency_split (m : Fin 3 → ℤ) :
    (Fin.snoc (fun j : Fin 2 ↦ m j.castSucc) (m 2) : Fin 3 → ℤ) = m :=
  Fin.snoc_init_self m

/-! ## Multiplication by the velocity -/

/-- **Multiplication by a stored velocity component, transported.**  For `u` in the velocity
class and a pointwise representative `v` of its value field, multiplication by the `a`-th stored
component (`productVelocityCoord u a`), read on `T3`, is multiplication by the `a`-th component of
the axially independent velocity `literalVelocity v`. -/
theorem toLiteralC3L2_scalarVectorMulProduct_velocityCoord_ae (u : TransverseRealW1Inf)
    {v : TransverseTorus → R3}
    (hv : (transverseW1InfValue u : TransverseTorus → R3) =ᵐ[transverseMeasure] v)
    (a : Fin 3) (W : ProductC3L2) :
    (toLiteralC3L2 (scalarVectorMulProduct (productVelocityCoord u a) W) : T3 → C3)
      =ᵐ[volume] fun x ↦ ((literalVelocity v x a : ℝ) : ℂ) • (toLiteralC3L2 W : T3 → C3) x := by
  have hT := ae_literal_of_ae_transverse
    ((((EuclideanSpace.proj a : C3 →L[ℂ] ℂ).coeFn_compLpL (p := ⊤)
      (transverseW1InfComplexValueLInf u)).and (transverseW1InfComplexValueLInf_coe_ae u)).and
      hv)
  have hP := ae_literal_of_ae_product
    ((scalarVectorMulProduct_coe_ae (productVelocityCoord u a) W).and
      (pullTransverseScalarLInf_coe_ae (transverseW1InfComplexValueCoordLInf a u)))
  filter_upwards [toLiteralC3L2_coe_ae (scalarVectorMulProduct (productVelocityCoord u a) W),
    hP, hT, toLiteralC3L2_coe_ae W] with x h1 h2 h3 h5
  rw [h1, h2.1, productVelocityCoord, h2.2, h5]
  congr 1
  change (EuclideanSpace.proj a : C3 →L[ℂ] ℂ).compLpL ⊤ transverseMeasure
    (transverseW1InfComplexValueLInf u) _ = _
  rw [h3.1.1, h3.1.2, h3.2]
  rfl

/-- The product coefficient at `(n, k)` of the coordinate product `uₐ Bᵦ`
(`productVelocityTimesCoord u a b W`) is the Challenge coefficient at `Fin.snoc n k` of
`x ↦ uₐ(x) Bᵦ(x)` on `T3`. -/
theorem inner_productMonomialL2_productVelocityTimesCoord (u : TransverseRealW1Inf)
    {v : TransverseTorus → R3}
    (hv : (transverseW1InfValue u : TransverseTorus → R3) =ᵐ[transverseMeasure] v)
    (a b : Fin 3) (W : ProductC3L2) (n : TransverseFrequency) (k : ℤ) :
    inner ℂ (productMonomialL2 n k) (productVelocityTimesCoord u a b W) =
      mFourierCoeff (fun x ↦ ((literalVelocity v x a : ℝ) : ℂ) * (toLiteralC3L2 W : L2) x b)
        (Fin.snoc n k : Fin 3 → ℤ) := by
  have h : productVelocityTimesCoord u a b W =
      productCoordL2 b (scalarVectorMulProduct (productVelocityCoord u a) W) := by
    rw [productCoordL2_scalarVectorMulProduct]
    rfl
  have h2 : inner ℂ (productMonomialL2 n k) (productVelocityTimesCoord u a b W) =
      productCoeffCLM n k b (scalarVectorMulProduct (productVelocityCoord u a) W) := by
    rw [h]
    rfl
  rw [h2, productCoeffCLM_eq_mFourierCoeff]
  refine mFourierCoeff_congr_ae ?_ _
  filter_upwards [toLiteralC3L2_scalarVectorMulProduct_velocityCoord_ae u hv a W] with x hx
  rw [hx, PiLp.smul_apply, smul_eq_mul]

/-- The coordinate coefficient of `u × W`: the product coefficient at `(n, k)` of the first
coordinate `u₁W₂ − u₂W₁` of the cross product, as Challenge coefficients. -/
theorem productCoeffCLM_productCrossWithVelocity_zero (u : TransverseRealW1Inf)
    {v : TransverseTorus → R3}
    (hv : (transverseW1InfValue u : TransverseTorus → R3) =ᵐ[transverseMeasure] v)
    (W : ProductC3L2) (n : TransverseFrequency) (k : ℤ) :
    productCoeffCLM n k 0 (productCrossWithVelocity u W) =
      mFourierCoeff (fun x ↦ ((literalVelocity v x 1 : ℝ) : ℂ) * (toLiteralC3L2 W : L2) x 2)
          (Fin.snoc n k : Fin 3 → ℤ) -
        mFourierCoeff (fun x ↦ ((literalVelocity v x 2 : ℝ) : ℂ) * (toLiteralC3L2 W : L2) x 1)
          (Fin.snoc n k : Fin 3 → ℤ) := by
  change inner ℂ (productMonomialL2 n k) (productCoordL2 0 (productCrossWithVelocity u W)) = _
  rw [productCoordL2_productCrossWithVelocity_zero, inner_sub_right,
    inner_productMonomialL2_productVelocityTimesCoord u hv,
    inner_productMonomialL2_productVelocityTimesCoord u hv]

/-- The product coefficient at `(n, k)` of the second coordinate `u₂W₀ − u₀W₂` of the cross
product, as Challenge coefficients. -/
theorem productCoeffCLM_productCrossWithVelocity_one (u : TransverseRealW1Inf)
    {v : TransverseTorus → R3}
    (hv : (transverseW1InfValue u : TransverseTorus → R3) =ᵐ[transverseMeasure] v)
    (W : ProductC3L2) (n : TransverseFrequency) (k : ℤ) :
    productCoeffCLM n k 1 (productCrossWithVelocity u W) =
      mFourierCoeff (fun x ↦ ((literalVelocity v x 2 : ℝ) : ℂ) * (toLiteralC3L2 W : L2) x 0)
          (Fin.snoc n k : Fin 3 → ℤ) -
        mFourierCoeff (fun x ↦ ((literalVelocity v x 0 : ℝ) : ℂ) * (toLiteralC3L2 W : L2) x 2)
          (Fin.snoc n k : Fin 3 → ℤ) := by
  change inner ℂ (productMonomialL2 n k) (productCoordL2 1 (productCrossWithVelocity u W)) = _
  rw [productCoordL2_productCrossWithVelocity_one, inner_sub_right,
    inner_productMonomialL2_productVelocityTimesCoord u hv,
    inner_productMonomialL2_productVelocityTimesCoord u hv]

/-- The product coefficient at `(n, k)` of the third coordinate `u₀W₁ − u₁W₀` of the cross
product, as Challenge coefficients. -/
theorem productCoeffCLM_productCrossWithVelocity_two (u : TransverseRealW1Inf)
    {v : TransverseTorus → R3}
    (hv : (transverseW1InfValue u : TransverseTorus → R3) =ᵐ[transverseMeasure] v)
    (W : ProductC3L2) (n : TransverseFrequency) (k : ℤ) :
    productCoeffCLM n k 2 (productCrossWithVelocity u W) =
      mFourierCoeff (fun x ↦ ((literalVelocity v x 0 : ℝ) : ℂ) * (toLiteralC3L2 W : L2) x 1)
          (Fin.snoc n k : Fin 3 → ℤ) -
        mFourierCoeff (fun x ↦ ((literalVelocity v x 1 : ℝ) : ℂ) * (toLiteralC3L2 W : L2) x 0)
          (Fin.snoc n k : Fin 3 → ℤ) := by
  change inner ℂ (productMonomialL2 n k) (productCoordL2 2 (productCrossWithVelocity u W)) = _
  rw [productCoordL2_productCrossWithVelocity_two, inner_sub_right,
    inner_productMonomialL2_productVelocityTimesCoord u hv,
    inner_productMonomialL2_productVelocityTimesCoord u hv]

/-! ## Lemma P: the curl form in the Challenge's coefficients -/

/-- **Lemma P, the Fourier symbol of the curl-form induction operator.**  Let `u` be a velocity of
the library's class, `v` a pointwise representative of its value field, and `B` a field of the
product `H²` graph.  The entry at component `i` and product frequency `(n, k)` of the `H⁻²`
realisation `productPhysicalInductionAction u ε B` of `curl (u × B) + ε ΔB` is the Challenge's
`inductionRHS` of the axially independent velocity `literalVelocity v` and the transported field,
at the frequency `Fin.snoc n k`, divided by the `H⁻²` weight `1 + 4π²(|n|² + k²)`. -/
theorem productPhysicalInductionAction_apply (u : TransverseRealW1Inf)
    {v : TransverseTorus → R3}
    (hv : (transverseW1InfValue u : TransverseTorus → R3) =ᵐ[transverseMeasure] v)
    (ε : ℝ) (B : ProductC3H2) (i : Fin 3) (k : ℤ) (n : TransverseFrequency) :
    productPhysicalInductionAction u ε B i k n =
      inductionRHS (literalVelocity v) ε ⇑(toLiteralC3L2 (productH2Embedding B) : L2)
          (Fin.snoc n k : Fin 3 → ℤ) i / (productH2Weight n k : ℂ) := by
  have h1 : productPhysicalInductionAction u ε B i k n =
      (ε : ℂ) * productL2ToHMinus2 (productLaplacianFromH2 B) i k n +
        productWeakCurl (productCrossWithVelocity u (productH2Embedding B)) i k n := rfl
  have hw : (productH2Weight n k : ℂ) ≠ 0 := by exact_mod_cast (productH2Weight_pos n k).ne'
  rw [h1, productL2ToHMinus2_apply, productCoeffCLM_productLaplacianFromH2,
    productCoeffCLM_eq_mFourierCoeff]
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  · rw [productWeakCurl_apply_zero, productCoeffCLM_productCrossWithVelocity_two u hv,
      productCoeffCLM_productCrossWithVelocity_one u hv]
    simp only [inductionRHS, Fin.sum_univ_three, snocFrequency_apply_zero, snocFrequency_apply_one,
      snocFrequency_apply_two, productFrequencyEnergy, Fin.sum_univ_two]
    field_simp
    push_cast
    ring
  · rw [productWeakCurl_apply_one, productCoeffCLM_productCrossWithVelocity_zero u hv,
      productCoeffCLM_productCrossWithVelocity_two u hv]
    simp only [inductionRHS, Fin.sum_univ_three, snocFrequency_apply_zero, snocFrequency_apply_one,
      snocFrequency_apply_two, productFrequencyEnergy, Fin.sum_univ_two]
    field_simp
    push_cast
    ring
  · rw [productWeakCurl_apply_two, productCoeffCLM_productCrossWithVelocity_one u hv,
      productCoeffCLM_productCrossWithVelocity_zero u hv]
    simp only [inductionRHS, Fin.sum_univ_three, snocFrequency_apply_zero, snocFrequency_apply_one,
      snocFrequency_apply_two, productFrequencyEnergy, Fin.sum_univ_two]
    field_simp
    push_cast
    ring

/-- **Lemma P at a frequency of `T3`.**  For every `m : Fin 3 → ℤ`, the entry of the `H⁻²`
realisation of `curl (u × B) + ε ΔB` at component `i` and product frequency
`(fun j ↦ m j.castSucc, m 2)`, multiplied by the `H⁻²` weight, is `inductionRHS` of the
transported field at `m`. -/
theorem productH2Weight_mul_productPhysicalInductionAction_apply (u : TransverseRealW1Inf)
    {v : TransverseTorus → R3}
    (hv : (transverseW1InfValue u : TransverseTorus → R3) =ᵐ[transverseMeasure] v)
    (ε : ℝ) (B : ProductC3H2) (m : Fin 3 → ℤ) (i : Fin 3) :
    (productH2Weight (fun j : Fin 2 ↦ m j.castSucc) (m 2) : ℂ) *
        productPhysicalInductionAction u ε B i (m 2) (fun j : Fin 2 ↦ m j.castSucc) =
      inductionRHS (literalVelocity v) ε ⇑(toLiteralC3L2 (productH2Embedding B) : L2) m i := by
  have hw : (productH2Weight (fun j : Fin 2 ↦ m j.castSucc) (m 2) : ℂ) ≠ 0 := by
    exact_mod_cast (productH2Weight_pos _ _).ne'
  rw [productPhysicalInductionAction_apply u hv, snocFrequency_split, mul_div_cancel₀ _ hw]

/-- **The curl-form identity in `H⁻²`, read on `T3`.**  If the `H⁻²` embedding of an `L²` field
`D` is the curl form `curl (u × B) + ε ΔB` of an `H²` field `B`, then the Challenge coefficients
of the transported `D` are `inductionRHS (literalVelocity v) ε` of the transported `B`. -/
theorem inductionRHS_eq_of_productL2ToHMinus2_eq (u : TransverseRealW1Inf)
    {v : TransverseTorus → R3}
    (hv : (transverseW1InfValue u : TransverseTorus → R3) =ᵐ[transverseMeasure] v)
    {ε : ℝ} {B : ProductC3H2} {D : ProductC3L2}
    (h : productL2ToHMinus2 D = productPhysicalInductionAction u ε B) (m : Fin 3 → ℤ)
    (i : Fin 3) :
    mFourierCoeff (fun x ↦ (toLiteralC3L2 D : L2) x i) m =
      inductionRHS (literalVelocity v) ε ⇑(toLiteralC3L2 (productH2Embedding B) : L2) m i := by
  have hm := congrArg (fun a : ProductC3HMinus2 ↦ a i (m 2) (fun j : Fin 2 ↦ m j.castSucc)) h
  have hw : (productH2Weight (fun j : Fin 2 ↦ m j.castSucc) (m 2) : ℂ) ≠ 0 := by
    exact_mod_cast (productH2Weight_pos _ _).ne'
  simp only [productL2ToHMinus2_apply, productCoeffCLM_split_eq_mFourierCoeff] at hm
  rw [productPhysicalInductionAction_apply u hv, snocFrequency_split] at hm
  exact (div_left_inj₀ hw).1 hm

/-! ## The eigenmode of the main theorem -/

/-- **The library's eigenmode, read on `T3`.**  From the physical clauses
`MainPhysicalClausesAt u γ₀ ε K λ b` of a velocity `u` of the library's class (with `v` a pointwise
representative of its value field), the lifted mode `V = e^{2πiKx₃} b`, transported to `T3`, lies
in the Challenge's `L2σ`, is non-zero, has its Fourier coefficients on the axial frequency `K`, and
solves the Challenge's eigen-equation `inductionRHS (literalVelocity v) ε V = λ V̂`. -/
theorem literalEigenmode_of_mainPhysicalClausesAt (u : TransverseRealW1Inf)
    {v : TransverseTorus → R3}
    (hv : (transverseW1InfValue u : TransverseTorus → R3) =ᵐ[transverseMeasure] v)
    {γ₀ ε : ℝ} {K : ℤ} {lam : ℂ} {b : TransverseC3H2}
    (h : MainPhysicalClausesAt u γ₀ ε K lam b) :
    (toLiteralC3L2 (productH2Embedding (axialLiftH2 K b)) : L2) ∈ L2σ ∧
      (toLiteralC3L2 (productH2Embedding (axialLiftH2 K b)) : L2) ≠ 0 ∧
      (∀ (m : Fin 3 → ℤ) (i : Fin 3), m 2 ≠ K →
        mFourierCoeff (fun x ↦ (toLiteralC3L2 (productH2Embedding (axialLiftH2 K b)) : L2) x i)
          m = 0) ∧
      ∀ (m : Fin 3 → ℤ) (i : Fin 3),
        inductionRHS (literalVelocity v) ε
            ⇑(toLiteralC3L2 (productH2Embedding (axialLiftH2 K b)) : L2) m i =
          lam * mFourierCoeff
            (fun x ↦ (toLiteralC3L2 (productH2Embedding (axialLiftH2 K b)) : L2) x i) m := by
  obtain ⟨-, -, -, -, -, hdiv, hphys, -⟩ := h
  set V := axialLiftH2 K b
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mem_L2σ_iff]
    intro m
    have hs := (productDivergenceFromH2_eq_zero_iff V).1 hdiv (fun j : Fin 2 ↦ m j.castSucc) (m 2)
    simp only [productFrequencyDivergenceCoeff_apply, productCoeffCLM_split_eq_mFourierCoeff,
      Fin.sum_univ_two] at hs
    have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hsum : (2 * Real.pi * Complex.I : ℂ) *
        ∑ i, (m i : ℂ) * mFourierCoeff (fun x ↦ (toLiteralC3L2 (productH2Embedding V) : L2) x i)
          m = 0 := by
      rw [Fin.sum_univ_three]
      have e0 : (Fin.castSucc (0 : Fin 2) : Fin 3) = 0 := rfl
      have e1 : (Fin.castSucc (1 : Fin 2) : Fin 3) = 1 := rfl
      rw [e0, e1] at hs
      linear_combination hs
    exact (mul_eq_zero.1 hsum).resolve_left h2pi
  · intro h0
    apply hphys.1
    change productL2ToHMinus2 (productH2Embedding V) = 0
    rw [show productH2Embedding V = 0 from toLiteralC3L2.map_eq_zero_iff.1 h0, map_zero]
  · intro m i hm
    rw [← productCoeffCLM_split_eq_mFourierCoeff, productCoeffCLM_productH2Embedding_axialLiftH2]
    simp [hm]
  · intro m i
    have he : productL2ToHMinus2 (lam • productH2Embedding V) =
        productPhysicalInductionAction u ε V := by
      rw [map_smul]
      exact hphys.2.symm
    rw [← inductionRHS_eq_of_productL2ToHMinus2_eq u hv he m i, map_smul, mFourierCoeff_l2_smul]

/-- **The eigenmode clause at the main theorem's witnesses, on `T3`.**  For every
`0 < ε ≤ mainEps0` there are an axial frequency `K ≠ 0`, an eigenvalue `λ` with
`mainGrowthFloor ≤ Re λ` and an amplitude `b` such that the library's eigenmode
`V = e^{2πiKx₃} b`, transported to `T3`, is a non-zero element of `L2σ` whose Fourier coefficients
vanish off `m 2 = K` and which solves `inductionRHS mainLiteralVelocity ε V = λ V̂`.  The triple
is the one of `mainPhysicalClauses_holds`, whose remaining clauses are returned as well. -/
theorem mainLiteralEigenmode_clauses {ε : ℝ} (hε : 0 < ε) (hε₀ : ε ≤ mainEps0) :
    ∃ (K : ℤ) (lam : ℂ) (b : TransverseC3H2),
      MainPhysicalClausesAt mainVelocity mainGrowthFloor ε K lam b ∧
      K ≠ 0 ∧ mainGrowthFloor ≤ lam.re ∧
      (toLiteralC3L2 (productH2Embedding (axialLiftH2 K b)) : L2) ∈ L2σ ∧
      (toLiteralC3L2 (productH2Embedding (axialLiftH2 K b)) : L2) ≠ 0 ∧
      (∀ (m : Fin 3 → ℤ) (i : Fin 3), m 2 ≠ K →
        mFourierCoeff (fun x ↦ (toLiteralC3L2 (productH2Embedding (axialLiftH2 K b)) : L2) x i)
          m = 0) ∧
      ∀ (m : Fin 3 → ℤ) (i : Fin 3),
        inductionRHS mainLiteralVelocity ε
            ⇑(toLiteralC3L2 (productH2Embedding (axialLiftH2 K b)) : L2) m i =
          lam * mFourierCoeff
            (fun x ↦ (toLiteralC3L2 (productH2Embedding (axialLiftH2 K b)) : L2) x i) m := by
  obtain ⟨K, lam, b, h⟩ := mainPhysicalClauses_holds ε hε hε₀
  exact ⟨K, lam, b, h, h.1, h.2.1,
    literalEigenmode_of_mainPhysicalClausesAt mainVelocity transverseW1InfValue_mainVelocity_ae h⟩

/-! ## The generator of the induction semigroup -/

/-- **The generator of the library's induction semigroup, read on `T3`.**  For `x` in the domain
of the generator of `solenoidalInductionSemigroup` on `L²_σ` (an `H²` field, by
`mem_generator_solenoidalInductionSemigroup_domain_iff`), the Challenge coefficients of the value
of the generator at `x`, transported to `T3`, are `inductionRHS (literalVelocity v) ε` of the
transported `x`. -/
theorem mFourierCoeff_generator_solenoidalInductionSemigroup (u : TransverseRealW1Inf)
    (hu : IsTransverseDivergenceFree u) {ε : ℝ} (hε : 0 < ε) {v : TransverseTorus → R3}
    (hv : (transverseW1InfValue u : TransverseTorus → R3) =ᵐ[transverseMeasure] v)
    (x : (solenoidalInductionSemigroup u hu hε).generator.domain) (m : Fin 3 → ℤ) (i : Fin 3) :
    mFourierCoeff (fun y ↦ (toLiteralC3L2
        (((solenoidalInductionSemigroup u hu hε).generator x : productSolenoidalSubspace) :
          ProductC3L2) : L2) y i) m =
      inductionRHS (literalVelocity v) ε
        ⇑(toLiteralC3L2 ((x : productSolenoidalSubspace) : ProductC3L2) : L2) m i := by
  obtain ⟨B, hB⟩ := (mem_generator_solenoidalInductionSemigroup_domain_iff u hu hε x).1 x.2
  rw [← hB]
  exact inductionRHS_eq_of_productL2ToHMinus2_eq u hv
    (productL2ToHMinus2_generator_solenoidalInductionSemigroup u hu hε x B hB) m i

/-- **Divergence-free `H²` fields lie in the domain of the generator, with the Challenge's
coefficients.**  For a divergence-free field `B` of the product `H²` graph there is an element `x`
of the domain of the generator of `solenoidalInductionSemigroup` whose field is `B`, and the
Challenge coefficients of the value of the generator at `x`, transported to `T3`, are
`inductionRHS (literalVelocity v) ε` of the transported `B`. -/
theorem exists_mem_generator_solenoidalInductionSemigroup_domain (u : TransverseRealW1Inf)
    (hu : IsTransverseDivergenceFree u) {ε : ℝ} (hε : 0 < ε) {v : TransverseTorus → R3}
    (hv : (transverseW1InfValue u : TransverseTorus → R3) =ᵐ[transverseMeasure] v)
    (B : ProductC3H2) (hB : productDivergenceFromH2 B = 0) :
    ∃ x : (solenoidalInductionSemigroup u hu hε).generator.domain,
      ((x : productSolenoidalSubspace) : ProductC3L2) = productH2Embedding B ∧
      ∀ (m : Fin 3 → ℤ) (i : Fin 3),
        mFourierCoeff (fun y ↦ (toLiteralC3L2
            (((solenoidalInductionSemigroup u hu hε).generator x : productSolenoidalSubspace) :
              ProductC3L2) : L2) y i) m =
          inductionRHS (literalVelocity v) ε ⇑(toLiteralC3L2 (productH2Embedding B) : L2) m i := by
  let x₀ : productSolenoidalSubspace :=
    ⟨productH2Embedding B, (productH2Embedding_mem_productSolenoidalSubspace_iff B).2 hB⟩
  have hx₀ : x₀ ∈ (solenoidalInductionSemigroup u hu hε).generator.domain :=
    (mem_generator_solenoidalInductionSemigroup_domain_iff u hu hε x₀).2 ⟨B, rfl⟩
  exact ⟨⟨x₀, hx₀⟩, rfl, mFourierCoeff_generator_solenoidalInductionSemigroup u hu hε hv _⟩

/-- **The generator at the main theorem's velocity, read on `T3`.**  The case
`u = mainVelocity` of `mFourierCoeff_generator_solenoidalInductionSemigroup`, with the Challenge's
velocity `mainLiteralVelocity`. -/
theorem mFourierCoeff_generator_solenoidalInductionSemigroup_main {ε : ℝ} (hε : 0 < ε)
    (x : (solenoidalInductionSemigroup mainVelocity mainVelocity_isTransverseDivergenceFree
      hε).generator.domain) (m : Fin 3 → ℤ) (i : Fin 3) :
    mFourierCoeff (fun y ↦ (toLiteralC3L2
        (((solenoidalInductionSemigroup mainVelocity mainVelocity_isTransverseDivergenceFree
          hε).generator x : productSolenoidalSubspace) : ProductC3L2) : L2) y i) m =
      inductionRHS mainLiteralVelocity ε
        ⇑(toLiteralC3L2 ((x : productSolenoidalSubspace) : ProductC3L2) : L2) m i :=
  mFourierCoeff_generator_solenoidalInductionSemigroup mainVelocity
    mainVelocity_isTransverseDivergenceFree hε transverseW1InfValue_mainVelocity_ae x m i

/-- **Lemma P at the main theorem's velocity.**  The case `u = mainVelocity` of
`productH2Weight_mul_productPhysicalInductionAction_apply`, with the Challenge's velocity
`mainLiteralVelocity`. -/
theorem productH2Weight_mul_productPhysicalInductionAction_main_apply (ε : ℝ)
    (B : ProductC3H2) (m : Fin 3 → ℤ) (i : Fin 3) :
    (productH2Weight (fun j : Fin 2 ↦ m j.castSucc) (m 2) : ℂ) *
        productPhysicalInductionAction mainVelocity ε B i (m 2) (fun j : Fin 2 ↦ m j.castSucc) =
      inductionRHS mainLiteralVelocity ε ⇑(toLiteralC3L2 (productH2Embedding B) : L2) m i :=
  productH2Weight_mul_productPhysicalInductionAction_apply mainVelocity
    transverseW1InfValue_mainVelocity_ae ε B m i

end

end FastDynamo
