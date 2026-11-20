/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.RealCompatibility

/-!
# The real part of a complex magnetic eigenmode is not an eigenmode

Remark 1.4 of the paper (the unlabelled remark after `rem:subsequent-resolution`): if
`Im λ_ε ≠ 0`, the real part of the complex magnetic eigenmode `V^ε` is not itself a magnetic
eigenmode, since it is not an eigenfunction of `L_{ε,u}`.

`not_isEigenpair_productRealPartH2` proves this for the physical induction operator
`productPhysicalInductionOperator u ε` of the main theorem (`MainPhysicalClauses`) on the
product torus.  The argument uses only that the velocity is real, through the commutation of
the auxiliary induction action with conjugation, and that eigenmodes are divergence-free (the
paper's definition of a magnetic eigenmode), through the agreement of the auxiliary action with
the physical one on divergence-free fields.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-- The auxiliary action of a divergence-free eigenmode of the physical induction operator is
the eigenvalue times the field. -/
theorem productInductionAction_eq_smul_of_physicalEigenpair
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u) (ε : ℝ)
    {lam : ℂ} {V : ProductC3H2} (hdiv : productDivergenceFromH2 V = 0)
    (hV : (productPhysicalInductionOperator u ε).IsEigenpair lam V) :
    productInductionAction u ε V = lam • productH2Embedding V := by
  apply productL2ToHMinus2_injective
  rw [productInductionAction_toHMinus2_eq_physical u hu ε V hdiv, map_smul]
  exact hV.2

/-- Linear algebra behind the remark: from `λ x + λ' y = μ (x + y)` follows
`(λ - μ) x = (μ - λ') y`. -/
theorem sub_smul_eq_sub_smul_of_add_eq {M : Type*} [AddCommGroup M] [Module ℂ M]
    {lam lam' μ : ℂ} {x y : M} (h : lam • x + lam' • y = μ • (x + y)) :
    (lam - μ) • x = (μ - lam') • y := by
  rw [smul_add] at h
  rw [sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add, add_comm (μ • y)]
  exact h

/-- If `a x = b y` with `a ≠ 0`, then `x` is a scalar multiple of `y`. -/
theorem exists_eq_smul_of_smul_eq_smul {M : Type*} [AddCommGroup M] [Module ℂ M]
    {a b : ℂ} {x y : M} (ha : a ≠ 0) (h : a • x = b • y) : ∃ c : ℂ, x = c • y :=
  ⟨a⁻¹ * b, by rw [mul_smul, ← h, smul_smul, inv_mul_cancel₀ ha, one_smul]⟩

/-- The auxiliary action of the conjugate of a divergence-free eigenmode is the conjugate
eigenvalue times the conjugate field: the velocity is real. -/
theorem productInductionAction_productConjH2_of_eq_smul
    (u : TransverseRealW1Inf) (ε : ℝ) {lam : ℂ} {V : ProductC3H2}
    (hAV : productInductionAction u ε V = lam • productH2Embedding V) :
    productInductionAction u ε (productConjH2 V) =
      starRingEnd ℂ lam • productH2Embedding (productConjH2 V) := by
  rw [productInductionAction_productConjH2, hAV, productConjL2_smul,
    productH2Embedding_productConjH2]

/-- If the real part of `V` is an eigenvector with eigenvalue `μ` of the auxiliary action
and `V` one with eigenvalue `λ`, then `(λ - μ) V = (μ - conj λ) conj V` in `L²`. -/
theorem sub_smul_embedding_eq_of_realPart_eq_smul
    (u : TransverseRealW1Inf) (ε : ℝ) {lam μ : ℂ} {V : ProductC3H2}
    (hAV : productInductionAction u ε V = lam • productH2Embedding V)
    (hAR : productInductionAction u ε (productRealPartH2 V) =
      μ • productH2Embedding (productRealPartH2 V)) :
    (lam - μ) • productH2Embedding V =
      (μ - starRingEnd ℂ lam) • productH2Embedding (productConjH2 V) := by
  have hAC := productInductionAction_productConjH2_of_eq_smul u ε hAV
  have hRe : productRealPartH2 V = ((1 / 2 : ℝ) : ℂ) • (V + productConjH2 V) := rfl
  rw [hRe, map_smul, map_add, hAV, hAC, map_smul, map_add] at hAR
  have hc : ((1 / 2 : ℝ) : ℂ) ≠ 0 := by norm_num
  have h3 : lam • productH2Embedding V +
      starRingEnd ℂ lam • productH2Embedding (productConjH2 V) =
      μ • (productH2Embedding V + productH2Embedding (productConjH2 V)) := by
    apply smul_right_injective ProductC3L2 hc
    rw [smul_comm] at hAR
    exact hAR
  exact sub_smul_eq_sub_smul_of_add_eq h3

/-- The algebraic core of Remark 1.4: a field with `A V = λ V`, `Im λ ≠ 0`, whose real part
satisfies `A (Re V) = μ Re V`, vanishes. -/
theorem productH2Embedding_eq_zero_of_realPart_eq_smul
    (u : TransverseRealW1Inf) (ε : ℝ) {lam μ : ℂ} (hlam : lam.im ≠ 0) {V : ProductC3H2}
    (hAV : productInductionAction u ε V = lam • productH2Embedding V)
    (hAR : productInductionAction u ε (productRealPartH2 V) =
      μ • productH2Embedding (productRealPartH2 V)) :
    productH2Embedding V = 0 := by
  have hAC := productInductionAction_productConjH2_of_eq_smul u ε hAV
  have hmain := sub_smul_embedding_eq_of_realPart_eq_smul u ε hAV hAR
  have hconj : starRingEnd ℂ lam ≠ lam := by
    intro h
    apply hlam
    have him := congrArg Complex.im h
    simp only [Complex.conj_im] at him
    linarith
  by_cases hμ : lam = μ
  · subst hμ
    have hcoef : lam - starRingEnd ℂ lam ≠ 0 := sub_ne_zero.2 hconj.symm
    have h0 : (lam - lam) • productH2Embedding V = 0 := by simp
    have hCV : productH2Embedding (productConjH2 V) = 0 := by
      rcases smul_eq_zero.1 (hmain.symm.trans h0) with h | h
      · exact absurd h hcoef
      · exact h
    have hV0 : productH2Embedding V =
        productConjL2 (productH2Embedding (productConjH2 V)) :=
      calc productH2Embedding V
          = productH2Embedding (productConjH2 (productConjH2 V)) :=
            congrArg _ (productConjH2_involutive V).symm
        _ = _ := productH2Embedding_productConjH2 _
    rw [hV0, hCV]
    exact map_zero productConjL2
  · have hsub : lam - μ ≠ 0 := sub_ne_zero.2 hμ
    obtain ⟨c, hcL⟩ := exists_eq_smul_of_smul_eq_smul hsub hmain
    have hVc : V = c • productConjH2 V := by
      apply productH2Embedding_injective
      simpa only [map_smul] using hcL
    have h1 : productInductionAction u ε V =
        starRingEnd ℂ lam • productH2Embedding V :=
      calc productInductionAction u ε V =
          productInductionAction u ε (c • productConjH2 V) :=
            congrArg _ hVc
        _ = c • (starRingEnd ℂ lam • productH2Embedding (productConjH2 V)) :=
            (map_smul (productInductionAction u ε) c (productConjH2 V)).trans
              (congrArg (c • ·) hAC)
        _ = starRingEnd ℂ lam • productH2Embedding (c • productConjH2 V) :=
            (smul_comm c _ _).trans
              (congrArg _ (map_smul productH2Embedding c (productConjH2 V)).symm)
        _ = starRingEnd ℂ lam • productH2Embedding V :=
            congrArg _ (congrArg _ hVc.symm)
    rw [hAV, ← sub_eq_zero, ← sub_smul] at h1
    rcases smul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hconj
    · exact h

/-- **Remark 1.4 of the paper.**  Let the velocity be real and divergence-free, and let `V` be a
divergence-free eigenmode of the physical induction operator `L_{ε,u}` with eigenvalue `λ`,
`Im λ ≠ 0`.  Then the real part `Re V` is an eigenvector of `L_{ε,u}` for no eigenvalue. -/
theorem not_isEigenpair_productRealPartH2
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u) (ε : ℝ)
    {lam : ℂ} (hlam : lam.im ≠ 0) {V : ProductC3H2}
    (hdiv : productDivergenceFromH2 V = 0)
    (hV : (productPhysicalInductionOperator u ε).IsEigenpair lam V) (μ : ℂ) :
    ¬ (productPhysicalInductionOperator u ε).IsEigenpair μ (productRealPartH2 V) := by
  intro hR
  apply hV.1
  have h0 := productH2Embedding_eq_zero_of_realPart_eq_smul u ε hlam
    (productInductionAction_eq_smul_of_physicalEigenpair u hu ε hdiv hV)
    (productInductionAction_eq_smul_of_physicalEigenpair u hu ε
      (productRealPartH2_preserves_divergenceFree hdiv) hR)
  change productL2ToHMinus2 (productH2Embedding V) = 0
  rw [h0]
  exact map_zero productL2ToHMinus2

end

end FastDynamo
