/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Palomar.IdealGroup

/-!
# Uniqueness of the ideal solution group in the terms of the Challenge statement

The Challenge statement asks the orbits of an ideal solution group to satisfy the integrated
equation `B̂ᵢ(t)(m) − B̂ᵢ(s)(m) = ∫ₛᵗ inductionRHS u 0 B(τ) m i dτ` at every frequency, that is,
the weak form tested with the characters `e_m eᵢ` only.  The library's notion
(`IsIdealWeakSolution`) tests the advective form against every smooth periodic field.  This
module shows that for orbits in `L²_σ` the first implies the second, so that every solution group
in the sense of the Challenge is, after transport, a solution group in the sense of the library,
hence the library's `mainIdealGroup` (`existsUnique_isIdealSolutionGroup_mainLiteralVelocity`).

## The steps

* **Characters.**  The library's weak identity with the test pair
  `(e_m eᵢ, (u·∇)(e_m eᵢ) = ∑ⱼ uⱼ 2πi mⱼ e_m eᵢ)` is, for a field with values in `L²_σ`, the
  Challenge's identity at `(m, i)` (`idealWeakIdentity_charTestField_iff`): the pairings are the
  coefficients `Ŵᵢ(m)` and `−2πi ∑ⱼ mⱼ (uⱼWᵢ)^(m)`, and on `L²_σ` the stretching coefficient
  completes the latter to `inductionRHS u 0` (`mFourierCoeff_literalStretchL2_sub_eq_inductionRHS`).
* **Trigonometric fields.**  The weak identity with an `L²` test pair is conjugate-linear in the
  pair, so it holds for every trigonometric field `∑ c e_m eᵢ` with its advection
  (`idealWeakIdentity_literalTrigField_of_charTestField`).
* **Lipschitz and smooth fields.**  Fourier partial sums and the closedness of the weak identity
  (`IdealWeakIdentity.of_tendsto`) extend it to every field whose lift is Lipschitz and
  differentiable everywhere (`idealWeakIdentity_of_lipschitz_of_charTestField`, the argument of
  `IsIdealWeakSolution.weakIdentity_of_lipschitz` with the hypothesis on trigonometric fields in
  place of a weak solution), in particular to every smooth test field; this is
  `IsIdealWeakSolution` (`isIdealWeakSolution_of_charTestField`).
* **Uniqueness.**  `isIdealSolutionGroup_of_isIdealGroup`, `isIdealGroup_eq_challengeIdealGroup`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory FastDynamoChallenge UnitAddTorus Filter Topology HorizontalMode
open scoped ComplexConjugate NNReal

/-! ## Character test pairs -/

/-- The character field `e_n eₖ` as an element of `L2`. -/
def charTestField (n : Fin 3 → ℤ) (k : Fin 3) : L2 :=
  literalSingleL2 k (flatTorus3FourierBasis n)

/-- The advection `(u·∇)(e_n eₖ) = ∑ⱼ uⱼ 2πi nⱼ e_n eₖ` of the character field by the theorem's
velocity, as an element of `L2`. -/
def charAdvection (n : Fin 3 → ℤ) (k : Fin 3) : L2 :=
  ∑ j : Fin 3, literalComponentMul mainLiteralVelocity lipschitzWith_mainLiteralVelocity.continuous
    j ((2 * Real.pi * Complex.I * (n j : ℂ)) • charTestField n k)

/-- Pairing with the character field reads the Fourier coefficient. -/
theorem inner_charTestField (n : Fin 3 → ℤ) (k : Fin 3) (X : L2) :
    inner ℂ (charTestField n k) X = mFourierCoeff (fun x ↦ X x k) n := by
  rw [charTestField, inner_literalSingleL2, ← mFourierCoeff_coe_eq_inner,
    mFourierCoeff_literalCoordL2]

/-- Pairing with the advected character field: `−2πi ∑ⱼ nⱼ (uⱼXₖ)^(n)`. -/
theorem inner_charAdvection (n : Fin 3 → ℤ) (k : Fin 3) (X : L2) :
    inner ℂ (charAdvection n k) X = -∑ j : Fin 3, 2 * Real.pi * Complex.I * (n j : ℂ) *
      mFourierCoeff (fun x ↦ ((mainLiteralVelocity x j : ℝ) : ℂ) * X x k) n := by
  rw [charAdvection, sum_inner, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hconj : (starRingEnd ℂ) (2 * Real.pi * Complex.I * (n j : ℂ)) =
      -(2 * Real.pi * Complex.I * (n j : ℂ)) := by
    simp [map_ofNat, Complex.conj_ofReal]
  rw [inner_literalComponentMul, inner_smul_left, inner_charTestField,
    mFourierCoeff_literalComponentMul, hconj, neg_mul]

/-- Pairing with the advected character field, expanded over the velocity components. -/
theorem inner_charAdvection_eq_sum (n : Fin 3 → ℤ) (k : Fin 3) (Y : L2) :
    inner ℂ (charAdvection n k) Y = ∑ j : Fin 3,
      conj (2 * Real.pi * Complex.I * (n j : ℂ)) *
        inner ℂ (literalComponentMul mainLiteralVelocity
          lipschitzWith_mainLiteralVelocity.continuous j
          (literalSingleL2 k (flatTorus3FourierBasis n))) Y := by
  simp only [charAdvection, charTestField, sum_inner, map_smul, inner_smul_left]

/-- **The converse of the symbol identity.**  For a field `W : ℝ → L2` with values in `L²_σ`,
the library's weak identity with the character test pair `(e_n eₖ, (u·∇)(e_n eₖ))` is the
Challenge's integrated equation at `(n, k)`. -/
theorem idealWeakIdentity_charTestField_iff {W : ℝ → L2} (hW : ∀ τ, W τ ∈ L2σ) (s t : ℝ)
    (n : Fin 3 → ℤ) (k : Fin 3) :
    IdealWeakIdentity mainLiteralVelocity W s t (charTestField n k) (charAdvection n k) ↔
      mFourierCoeff (fun x ↦ W t x k) n - mFourierCoeff (fun x ↦ W s x k) n =
        ∫ τ in s..t, inductionRHS mainLiteralVelocity 0 (W τ : T3 → C3) n k := by
  have hint : ∀ τ, inner ℂ (charTestField n k) (literalStretchL2 mainLiteralVelocity (W τ)) +
      inner ℂ (charAdvection n k) (W τ) =
        inductionRHS mainLiteralVelocity 0 (W τ : T3 → C3) n k := by
    intro τ
    rw [inner_charTestField, inner_charAdvection, ← sub_eq_add_neg,
      mFourierCoeff_literalStretchL2_sub_eq_inductionRHS n k (hW τ)]
  rw [IdealWeakIdentity, inner_charTestField, inner_charTestField]
  simp only [hint]

/-! ## Trigonometric test fields -/

/-- **Trigonometric fields.**  If `W` satisfies the weak identity with every character test pair,
it satisfies it with every trigonometric field `∑ c e_m eᵢ` and its advection. -/
theorem idealWeakIdentity_literalTrigField_of_charTestField {W : ℝ → L2} {s t : ℝ}
    (hc : ContinuousOn W (Set.uIcc s t))
    (hchar : ∀ n k, IdealWeakIdentity mainLiteralVelocity W s t (charTestField n k)
      (charAdvection n k))
    (F : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → Fin 3 → ℂ) :
    IdealWeakIdentity mainLiteralVelocity W s t
      (ContinuousMap.toLp 2 (volume : Measure T3) ℂ (literalTrigField F c))
      (∑ j : Fin 3, literalComponentMul mainLiteralVelocity
        lipschitzWith_mainLiteralVelocity.continuous j
        (ContinuousMap.toLp 2 (volume : Measure T3) ℂ
          (literalTrigField F fun m i ↦ 2 * Real.pi * Complex.I * (m j : ℂ) * c m i))) := by
  set M : Fin 3 → L2 →L[ℂ] L2 := fun j ↦ literalComponentMul mainLiteralVelocity
    lipschitzWith_mainLiteralVelocity.continuous j
  set X : L2 := W t - W s - ∫ τ in s..t, literalStretchL2 mainLiteralVelocity (W τ)
  set Y : L2 := ∫ τ in s..t, W τ
  have hXY : ∀ φ ψ : L2, IdealWeakIdentity mainLiteralVelocity W s t φ ψ ↔
      inner ℂ φ X = inner ℂ ψ Y := by
    intro φ ψ
    rw [idealWeakIdentity_iff hc, inner_sub_right, inner_sub_right]
    constructor <;> intro h <;> linear_combination h
  have hchar' : ∀ (n : Fin 3 → ℤ) (k : Fin 3),
      inner ℂ (literalSingleL2 k (flatTorus3FourierBasis n)) X = ∑ j : Fin 3,
        conj (2 * Real.pi * Complex.I * (n j : ℂ)) *
          inner ℂ (M j (literalSingleL2 k (flatTorus3FourierBasis n))) Y := by
    intro n k
    have h := (hXY _ _).1 (hchar n k)
    rwa [inner_charAdvection_eq_sum, charTestField] at h
  rw [hXY, toLp_literalTrigField]
  simp only [toLp_literalTrigField, map_sum, map_smul, sum_inner, inner_smul_left, hchar',
    Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [map_mul]
  ring

/-! ## Lipschitz and smooth test fields -/

/-- **Lipschitz test fields.**  If `W` is continuous on `[s, t]` and satisfies the weak identity
with every character test pair, it satisfies the weak identity with the `L²` test pair
`(φ, (u·∇)φ)` for every field `φ` whose lift is Lipschitz and differentiable everywhere.  This is
the argument of `IsIdealWeakSolution.weakIdentity_of_lipschitz`, with the identity for
trigonometric fields (`idealWeakIdentity_literalTrigField_of_charTestField`) in place of a weak
solution. -/
theorem idealWeakIdentity_of_lipschitz_of_charTestField {W : ℝ → L2} {s t : ℝ}
    (hc : ContinuousOn W (Set.uIcc s t))
    (hchar : ∀ n k, IdealWeakIdentity mainLiteralVelocity W s t (charTestField n k)
      (charAdvection n k))
    {φ : T3 → C3} (hdiff : Differentiable ℝ fun a : R3 ↦ φ (literalTorusPoint a))
    {K : ℝ≥0} (hlip : LipschitzWith K fun a : R3 ↦ φ (literalTorusPoint a))
    (hφ : MemLp φ 2 volume) (hadv : MemLp (literalAdvection mainLiteralVelocity φ) 2 volume) :
    IdealWeakIdentity mainLiteralVelocity W s t (hφ.toLp φ) (hadv.toLp _) := by
  set u := mainLiteralVelocity
  set M : Fin 3 → L2 →L[ℂ] L2 := fun j ↦ literalComponentMul mainLiteralVelocity
    lipschitzWith_mainLiteralVelocity.continuous j
  have hM : ∀ (j : Fin 3) (X : L2), (M j X : T3 → C3) =ᵐ[volume]
      fun x ↦ ((u x j : ℝ) : ℂ) • (X : T3 → C3) x := fun j X ↦
    literalComponentMul_coe_ae _ _ j X
  -- the partial derivatives of `φ`
  have hD : ∀ j : Fin 3, MemLp (fun x ↦ fderiv ℝ (fun a : R3 ↦ φ (literalTorusPoint a))
      (literalIocRepresentative x) (EuclideanSpace.single j 1)) 2 (volume : Measure T3) := by
    intro j
    refine MemLp.of_bound ((measurable_fderiv_apply_const ℝ _ _).comp
      measurable_literalIocRepresentative).aestronglyMeasurable K
      (Eventually.of_forall fun x ↦ ?_)
    refine ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
    have hn : ‖(EuclideanSpace.single j (1 : ℝ) : R3)‖ = 1 := by simp
    rw [hn, mul_one]
    exact norm_fderiv_le_of_lipschitz ℝ hlip
  set D : Fin 3 → L2 := fun j ↦ (hD j).toLp _
  set Φ := hφ.toLp φ
  have hcoeff : ∀ j : Fin 3, (fun m i ↦ 2 * Real.pi * Complex.I * (m j : ℂ) *
      literalFourierCoeff Φ m i) = literalFourierCoeff (D j) := fun j ↦ by
    funext m i
    exact (literalFourierCoeff_fderiv hdiff hlip hφ j (hD j) m i).symm
  have hlimit : ∑ j : Fin 3, M j (D j) = hadv.toLp _ := by
    refine Lp.ext ?_
    filter_upwards [literalC3L2_coeFn_sum fun j ↦ M j (D j), ae_all_iff.2 fun j ↦ hM j (D j),
      ae_all_iff.2 fun j ↦ (show (D j : T3 → C3) =ᵐ[volume] _ from (hD j).coeFn_toLp),
      hadv.coeFn_toLp] with x h1 h2 h3 h4
    rw [h1, h4]
    simp_rw [h2, h3]
    conv_rhs => rw [literalAdvection, ← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (u x)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  rw [← hlimit]
  refine IdealWeakIdentity.of_tendsto hc (tendsto_toLp_literalTrigField Φ)
    (tendsto_finsetSum _ fun j _ ↦ ((M j).continuous.tendsto _).comp
      (tendsto_toLp_literalTrigField (D j)))
    (Eventually.of_forall fun F ↦ ?_)
  have h := idealWeakIdentity_literalTrigField_of_charTestField hc hchar F (literalFourierCoeff Φ)
  simp only [hcoeff] at h
  exact h

/-- **The library's weak form from the character identities.**  A field `W` continuous on
`[−T, T]` that satisfies the weak identity with every character test pair at all times of
`[−T, T]` is a weak solution of the ideal induction equation in the library's sense: the identity
holds against every smooth periodic test field. -/
theorem isIdealWeakSolution_of_charTestField {W : ℝ → L2} {T : ℝ}
    (hc : ContinuousOn W (Set.Icc (-T) T))
    (hchar : ∀ s ∈ Set.Icc (-T) T, ∀ t ∈ Set.Icc (-T) T, ∀ n k,
      IdealWeakIdentity mainLiteralVelocity W s t (charTestField n k) (charAdvection n k)) :
    IsIdealWeakSolution mainLiteralVelocity T W := by
  refine ⟨hc, fun φ hφt s hs t ht ↦ ?_⟩
  -- the test field is bounded, measurable, Lipschitz and differentiable
  have hcont : Continuous fun a : R3 ↦ φ (literalTorusPoint a) := hφt.continuous
  obtain ⟨C₀, hC₀⟩ := exists_norm_le_of_continuous_lift hcont
  have hφL : MemLp φ 2 volume :=
    MemLp.of_bound (measurable_of_continuous_lift
      hcont).aestronglyMeasurable C₀ (ae_of_all _ hC₀)
  have hadv : MemLp (literalAdvection mainLiteralVelocity φ) 2 volume := by
    obtain ⟨C, hC⟩ := ScaleFamily.TorusCellPlacement.exists_norm_literalAdvection_le
      globalSeedInterface.smoothingWidth mainParameterChoice.placement
      globalSeedInterface.angularSpeed globalSeedInterface.axialSpeed mainParameterChoice.tau
      mainParameterChoice.tau_nonneg hφt
    exact MemLp.of_bound (ScaleFamily.TorusCellPlacement.aestronglyMeasurable_literalAdvection
      globalSeedInterface.smoothingWidth mainParameterChoice.placement
      globalSeedInterface.angularSpeed globalSeedInterface.axialSpeed mainParameterChoice.tau
      mainParameterChoice.tau_nonneg hφt) C (ae_of_all _ hC)
  have hdiff : Differentiable ℝ fun a : R3 ↦ φ (literalTorusPoint a) := hφt.differentiable (by simp)
  obtain ⟨C, hC⟩ := exists_bound_comp_literalIocRepresentative (hφt.continuous_fderiv (by simp))
  have hC' : ∀ c : R3, ‖fderiv ℝ (fun c : R3 ↦ φ (literalTorusPoint c)) c‖ ≤ C := fun c ↦ by
    rw [fderiv_literalLift_congr φ
      (literalTorusPoint_literalIocRepresentative (literalTorusPoint c)).symm]
    exact hC _
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC' 0)
  have hlip : LipschitzWith (Real.toNNReal C) fun a : R3 ↦ φ (literalTorusPoint a) := by
    refine lipschitzWith_of_nnnorm_fderiv_le hdiff fun a ↦ ?_
    refine NNReal.coe_le_coe.1 ?_
    rw [coe_nnnorm, Real.coe_toNNReal _ hC0]
    exact hC' a
  have key := idealWeakIdentity_of_lipschitz_of_charTestField
    (hc.mono (Set.uIcc_subset_Icc hs ht)) (hchar s hs t ht) hdiff hlip hφL hadv
  -- back to the integral form
  have hpair : ∀ X : L2, inner ℂ (hφL.toLp φ) X = ∫ x, inner ℂ (φ x) ((X : T3 → C3) x) :=
    fun X ↦ (integral_inner_eq_inner_toLp hφL
      (Filter.EventuallyEq.refl _ _)).symm
  have hτ : ∀ τ : ℝ, (∫ x, (inner ℂ (φ x) (literalStretch mainLiteralVelocity
      (W τ : T3 → C3) x) + inner ℂ (literalAdvection mainLiteralVelocity φ x)
        ((W τ : T3 → C3) x))) =
      inner ℂ (hφL.toLp φ) (literalStretchL2 mainLiteralVelocity (W τ)) +
        inner ℂ (hadv.toLp _) (W τ) := by
    intro τ
    rw [L2.inner_def, L2.inner_def, ← integral_add (L2.integrable_inner _ _)
      (L2.integrable_inner _ _)]
    refine integral_congr_ae ?_
    filter_upwards [hφL.coeFn_toLp, hadv.coeFn_toLp, literalStretchL2_main_coe_ae (W τ)]
      with x h1 h2 h3
    rw [h1, h2, h3]
  rw [IdealWeakIdentity, hpair, hpair] at key
  simp_rw [hτ]
  exact key

/-! ## Uniqueness -/

/-- **Every solution group in the sense of the Challenge is one in the sense of the library.**
If `T'` satisfies `IsIdealGroup mainLiteralVelocity T'`, its transport to the library's state
space `literalSolenoidalSubspace` is a solution group of the library's ideal induction equation
(`IsIdealSolutionGroup`). -/
theorem isIdealSolutionGroup_of_isIdealGroup {T' : ℝ → L2σ →L[ℂ] L2σ}
    (hT' : IsIdealGroup mainLiteralVelocity T') :
    IsIdealSolutionGroup mainLiteralVelocity
      fun t ↦ (conjOp literalSolenoidalEquivL2σ).symm (T' t) where
  group_zero :=
    (congrArg (conjOp literalSolenoidalEquivL2σ).symm hT'.map_zero).trans (conjOp_symm_id _)
  group_add s t :=
    (congrArg (conjOp literalSolenoidalEquivL2σ).symm (hT'.map_add s t)).trans
      (conjOp_symm_comp _ _ _)
  weakSolution B T := by
    set B' : L2σ := literalSolenoidalEquivL2σ B
    have hcont : Continuous fun t ↦ ((T' t B' : L2σ) : L2) :=
      continuous_subtype_val.comp (hT'.continuous B')
    refine isIdealWeakSolution_of_charTestField (W := fun t ↦ ((T' t B' : L2σ) : L2))
      hcont.continuousOn fun s _ t _ n k ↦ ?_
    exact (idealWeakIdentity_charTestField_iff (fun τ ↦ (T' τ B').2) s t n k).2
      (hT'.weak B' n k s t)

/-- **I2, uniqueness.**  Every solution group of the ideal induction equation of the theorem's
velocity, in the sense of the Challenge statement, is `challengeIdealGroup`. -/
theorem isIdealGroup_eq_challengeIdealGroup {T' : ℝ → L2σ →L[ℂ] L2σ}
    (hT' : IsIdealGroup mainLiteralVelocity T') : T' = challengeIdealGroup := by
  obtain ⟨Φ, DΦ, hT, -⟩ := exists_isIdealInductionGroup_mainIdealGroup
  have h := hT.unique _ (isIdealSolutionGroup_of_isIdealGroup hT')
  funext t
  have ht := congrFun h t
  rw [challengeIdealGroup, ← ht, LinearIsometryEquiv.apply_symm_apply]

/-! ## The last clause of the Challenge statement -/

/-- **The ideal clause of the Challenge statement**: the ideal induction equation of the
theorem's velocity has a solution group on `L²_σ` in the sense of the Challenge, it has only one,
and its operator norm grows subexponentially, `t⁻¹ log ‖T t‖ → 0` as `t → ∞`. -/
theorem exists_unique_isIdealGroup_mainLiteralVelocity :
    ∃ T, FastDynamoChallenge.IsIdealGroup mainLiteralVelocity T ∧
      (∀ T', FastDynamoChallenge.IsIdealGroup mainLiteralVelocity T' → T' = T) ∧
      Tendsto (fun t : ℝ => t⁻¹ * Real.log ‖T t‖) atTop (𝓝 0) :=
  ⟨challengeIdealGroup, isIdealGroup_challengeIdealGroup,
    fun _ hT' ↦ isIdealGroup_eq_challengeIdealGroup hT',
    tendsto_inv_mul_log_norm_challengeIdealGroup⟩

end

end FastDynamo
