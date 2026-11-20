/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.Assembly.NegativeSobolevResolvent
public import LeanPool.FastDynamo.Dynamics.Assembly.ProductSemigroup

/-!
# Uniqueness of the solution of the induction equation in curl form

Theorem 1.2 of the paper (`thm:main`) speaks of *the* solution of the induction equation
`∂_t B = ε Δ B + curl(u × B)` with initial datum `B_in^ε`.  In the formalisation the curl-form
equation is the operator `productPhysicalInductionOperator u ε` on the product torus `T² × T`:
`H²` fields, values in the Fourier model of `H⁻²` (`FastDynamo/Operator/Compatibility.lean`).
A strong solution in the sense of `MainPhysicalClauses` is an `H²`-valued curve whose
`H⁻²` embedding is differentiable with derivative `ε ΔB + curl(u × B)`.  This module proves that
such solutions are unique for forward times, for every divergence-free transverse velocity and
every `ε > 0`, with no condition on the data
(`productPhysicalInductionOperator_forwardStrongSolutionsUnique`).  Hence the explicit curve
`B^ε(t)` of Theorem 1.2 is the solution with datum `B_in^ε`, and every forward strong solution
with divergence-free datum is the orbit of the induction semigroup
(`productH2Embedding_eq_productInductionSemigroup_of_isForwardStrongSolution`).  Along such a
solution the energy identity `eq:energy-competition` holds at every `t > 0`
(`hasDerivAt_half_norm_sq_of_isForwardStrongSolution_physical`).

The argument has three steps.

* The divergence of a forward strong solution satisfies, Fourier mode by Fourier mode, the
  heat equation `c' = −4π²ε|ξ|² c`, because the curl term has no divergence; so a solution with
  divergence-free datum stays divergence-free
  (`productDivergenceFromH2_eq_zero_of_isForwardStrongSolution`, for every `ε`).
* On divergence-free fields the curl form is the `H⁻²` embedding of the auxiliary action
  `productInductionAction u ε` (`productInductionAction_toHMinus2_eq_physical`).
* The resolvent `R(r)` of the auxiliary operator is bounded from the `H⁻²` norm
  (`exists_norm_stateResolvent_le_productL2ToHMinus2`), so for the difference `w` of two
  solutions, `R(r) w(t)` is an `L²` forward strong solution of the auxiliary operator with
  initial value `0`, hence `0` by the uniqueness for the auxiliary operator
  (`productInductionOperator_forwardStrongSolutionsUnique`); `R(r)` is injective.

The paper has no separate well-posedness statement: Theorem 1.2 asserts the norm law
`eq:main-thm-growth` for "its solution" and its proof writes that solution down.  The Lean
statement is uniqueness for forward times `t ≥ 0`, among `H²`-valued curves with one-sided
derivative at `t = 0` in the `H⁻²` model, on the product torus with an axially independent
velocity; it contains the class of `MainPhysicalClauses`, whose curve is a strong solution at
every real time.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-! ## The divergence on the `H⁻²` model -/

/-- The divergence at the Fourier mode `(n, k)` on the `H⁻²` coefficient model:
`F ↦ ∑_{j<2} 2πi n_j F_j(n,k) + 2πi k F_3(n,k)`. -/
def productHMinus2DivergenceFunctional (n : TransverseFrequency) (k : ℤ) :
    ProductC3HMinus2 →L[ℂ] ℂ :=
  (∑ j : Fin 2,
    (2 * Real.pi * Complex.I * (n j : ℂ)) • weightedProductCoeffCLM n k j.castSucc) +
  (2 * Real.pi * Complex.I * (k : ℂ)) • weightedProductCoeffCLM n k (2 : Fin 3)

/-- Evaluation of the modal divergence on the `H⁻²` model, with the three coordinates
displayed. -/
theorem productHMinus2DivergenceFunctional_apply (n : TransverseFrequency) (k : ℤ)
    (F : ProductC3HMinus2) :
    productHMinus2DivergenceFunctional n k F =
      (2 * Real.pi * Complex.I * (n 0 : ℂ)) * F 0 k n +
        (2 * Real.pi * Complex.I * (n 1 : ℂ)) * F 1 k n +
          (2 * Real.pi * Complex.I * (k : ℂ)) * F 2 k n := by
  simp [productHMinus2DivergenceFunctional, weightedProductCoeffCLM, Fin.sum_univ_two]
  rfl

/-- On `L²` fields the modal divergence on `H⁻²` is the solenoidality functional divided by
the order-two weight. -/
theorem productHMinus2DivergenceFunctional_productL2ToHMinus2 (n : TransverseFrequency) (k : ℤ)
    (V : ProductC3L2) :
    productHMinus2DivergenceFunctional n k (productL2ToHMinus2 V) =
      productSolenoidalFunctional n k V / (productH2Weight n k : ℂ) := by
  rw [productHMinus2DivergenceFunctional_apply, productSolenoidalFunctional_apply]
  simp only [productL2ToHMinus2_apply, Fin.sum_univ_two, Fin.castSucc_zero, Fin.castSucc_one]
  ring

/-- **The curl has no divergence**: the modal divergence of the distributional curl vanishes. -/
theorem productHMinus2DivergenceFunctional_productWeakCurl (n : TransverseFrequency) (k : ℤ)
    (W : ProductC3L2) :
    productHMinus2DivergenceFunctional n k (productWeakCurl W) = 0 := by
  rw [productHMinus2DivergenceFunctional_apply, productWeakCurl_apply_zero,
    productWeakCurl_apply_one, productWeakCurl_apply_two]
  ring

/-- The modal divergence of the curl-form induction action is `−ε 4π²|ξ|²` times the modal
divergence of the field: the divergence of `B` obeys the heat equation. -/
theorem productHMinus2DivergenceFunctional_productPhysicalInductionAction
    (u : TransverseRealW1Inf) (ε : ℝ) (n : TransverseFrequency) (k : ℤ) (B : ProductC3H2) :
    productHMinus2DivergenceFunctional n k (productPhysicalInductionAction u ε B) =
      -((ε * productFrequencyEnergy n k : ℝ) : ℂ) *
        productHMinus2DivergenceFunctional n k (productL2ToHMinus2 (productH2Embedding B)) := by
  simp only [productPhysicalInductionAction, add_apply,
    smul_apply, ContinuousLinearMap.comp_apply, map_add, map_smul,
    productHMinus2DivergenceFunctional_productWeakCurl, add_zero,
    productHMinus2DivergenceFunctional_productL2ToHMinus2, productSolenoidalFunctional_apply,
    productCoeffCLM_productLaplacianFromH2, Fin.sum_univ_two, smul_eq_mul]
  push_cast
  ring

/-! ## Solenoidality propagates -/

/-- **A strong solution of the curl form with divergence-free datum stays divergence-free.**
For every velocity `u` and every `ε`, if `w` is a forward strong solution of the curl-form
induction operator `productPhysicalInductionOperator u ε` and `div w(0) = 0`, then
`div w(t) = 0` for all `t ≥ 0`.  At every Fourier mode `(n, k)` the divergence solves
`c' = −4π²ε(|n|² + k²) c`, since the curl term has no divergence. -/
theorem productDivergenceFromH2_eq_zero_of_isForwardStrongSolution (u : TransverseRealW1Inf)
    (ε : ℝ) {w : ℝ → ProductC3H2}
    (hw : (productPhysicalInductionOperator u ε).IsForwardStrongSolution w)
    (hw0 : productDivergenceFromH2 (w 0) = 0) {t : ℝ} (ht : 0 ≤ t) :
    productDivergenceFromH2 (w t) = 0 := by
  rw [productDivergenceFromH2_eq_zero_iff] at hw0 ⊢
  intro n k
  set φ := productHMinus2DivergenceFunctional n k
  set lam : ℂ := -((ε * productFrequencyEnergy n k : ℝ) : ℂ)
  have hsol : (scalarOperator lam).IsForwardStrongSolution
      (fun s ↦ φ (productL2ToHMinus2 (productH2Embedding (w s)))) := by
    intro s hs
    have h := (φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt s (hw s hs)
    change HasDerivWithinAt (fun s ↦ φ (productL2ToHMinus2 (productH2Embedding (w s))))
      (φ (productPhysicalInductionAction u ε (w s))) (Set.Ici 0) s at h
    rw [productHMinus2DivergenceFunctional_productPhysicalInductionAction] at h
    exact h
  have hzero : (scalarOperator lam).IsForwardStrongSolution (fun _ ↦ (0 : ℂ)) := by
    intro s _
    simpa [scalarOperator] using hasDerivWithinAt_const s (Set.Ici (0 : ℝ)) (0 : ℂ)
  have hw0' : φ (productL2ToHMinus2 (productH2Embedding (w 0))) = 0 := by
    rw [productHMinus2DivergenceFunctional_productL2ToHMinus2,
      productSolenoidalFunctional_apply, hw0 n k, zero_div]
  have h := scalarOperator_forwardStrongSolutionsUnique lam _ _ hsol hzero hw0' t ht
  change φ (productL2ToHMinus2 (productH2Embedding (w t))) = 0 at h
  rw [productHMinus2DivergenceFunctional_productL2ToHMinus2, div_eq_zero_iff,
    productSolenoidalFunctional_apply] at h
  exact h.resolve_right (by exact_mod_cast (productH2Weight_pos n k).ne')

/-! ## Uniqueness -/

/-- **Uniqueness of strong solutions of the induction equation in curl form** (the solution of
Theorem 1.2, `thm:main`).  For a divergence-free transverse velocity `u` and `ε > 0`, two forward
strong solutions of the curl-form induction operator `productPhysicalInductionOperator u ε`
(`H²`-valued, differentiable in `H⁻²` from the right at `t = 0` and two-sidedly at `t > 0`) with
the same initial value agree for all `t ≥ 0`.  No divergence condition on the data is needed. -/
theorem productPhysicalInductionOperator_forwardStrongSolutionsUnique
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u) {ε : ℝ} (hε : 0 < ε) :
    (productPhysicalInductionOperator u ε).ForwardStrongSolutionsUnique := by
  intro w₁ w₂ h₁ h₂ h0 t ht
  have hw := (productPhysicalInductionOperator u ε).isForwardStrongSolution_sub h₁ h₂
  have hw0 : w₁ 0 - w₂ 0 = 0 :=
    sub_eq_zero.mpr ((productPhysicalInductionOperator u ε).embedding_injective h0)
  have hdiv : ∀ s, 0 ≤ s → productDivergenceFromH2 (w₁ s - w₂ s) = 0 := fun s hs ↦
    productDivergenceFromH2_eq_zero_of_isForwardStrongSolution u ε hw
      (by simp only [hw0, map_zero]) hs
  have hr : ‖transverseStretchingCoefficient u‖ < ‖transverseStretchingCoefficient u‖ + 1 :=
    lt_add_one _
  obtain ⟨C, hC⟩ := exists_norm_stateResolvent_le_productL2ToHMinus2 u hu hε hr
  generalize ‖transverseStretchingCoefficient u‖ + 1 = r at hr hC
  have hz : (r : ℂ) ∈ {z : ℂ | ‖transverseStretchingCoefficient u‖ < z.re} := by simpa using hr
  generalize productInductionHalfPlaneResolvent u hu hε = R at hC
  obtain ⟨v, hvdef⟩ : ∃ v : ℝ → ProductC3H2,
      v = fun s ↦ R.inv (r : ℂ) (productH2Embedding (w₁ s - w₂ s)) := ⟨_, rfl⟩
  have hv : (productInductionOperator u ε).IsForwardStrongSolution v := by
    intro s hs
    have hd : HasDerivWithinAt (fun τ ↦ productL2ToHMinus2 (productH2Embedding (w₁ τ - w₂ τ)))
        (productL2ToHMinus2 (productInductionAction u ε (w₁ s - w₂ s))) (Set.Ici 0) s := by
      rw [productInductionAction_toHMinus2_eq_physical u hu ε _ (hdiv s hs)]
      exact hw s hs
    have h := hasDerivWithinAt_comp_of_norm_le (R.stateResolvent (r : ℂ))
      productL2ToHMinus2 hC hd
    have hop := op_inv_embedding R hz (w₁ s - w₂ s)
    subst hvdef
    change HasDerivWithinAt
      (fun τ ↦ productH2Embedding (R.inv (r : ℂ) (productH2Embedding (w₁ τ - w₂ τ))))
      (productInductionAction u ε (R.inv (r : ℂ) (productH2Embedding (w₁ s - w₂ s))))
      (Set.Ici 0) s
    rw [show productInductionAction u ε (R.inv (r : ℂ) (productH2Embedding (w₁ s - w₂ s))) =
      R.stateResolvent (r : ℂ) (productInductionAction u ε (w₁ s - w₂ s)) from hop]
    exact h
  have hzero : (productInductionOperator u ε).IsForwardStrongSolution (fun _ ↦ 0) := by
    intro s _
    simp only [map_zero]
    exact hasDerivWithinAt_const _ _ _
  have hv0 : (productInductionOperator u ε).embedding (v 0) =
      (productInductionOperator u ε).embedding 0 := by
    simp only [hvdef, hw0, map_zero]
  have hvt := productInductionOperator_forwardStrongSolutionsUnique u hu hε.le v (fun _ ↦ 0)
    hv hzero hv0 t ht
  have hinv : R.inv (r : ℂ) (productH2Embedding (w₁ t - w₂ t)) = 0 := by
    have h' : productH2Embedding (v t) = productH2Embedding 0 := hvt
    rw [hvdef] at h'
    exact productH2Embedding_injective h'
  have hpen := DFunLike.congr_fun (R.right_inv _ hz) (productH2Embedding (w₁ t - w₂ t))
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hinv,
    map_zero] at hpen
  have hdiff : w₁ t - w₂ t = 0 :=
    productH2Embedding_injective (hpen.symm.trans (map_zero _).symm)
  exact congrArg (productPhysicalInductionOperator u ε).embedding (sub_eq_zero.mp hdiff)

variable (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u) {ε : ℝ} (hε : 0 < ε)

/-- **The semigroup orbit solves the curl-form equation.**  For a divergence-free `H²` datum
`B`, the domain-valued orbit of the induction semigroup is a forward strong solution of the
curl-form induction operator `productPhysicalInductionOperator u ε`. -/
theorem isForwardStrongSolution_productPhysicalInductionOperator_domainOrbit (B : ProductC3H2)
    (hB : productDivergenceFromH2 B = 0) :
    (productPhysicalInductionOperator u ε).IsForwardStrongSolution
      ((productInductionRealization u hu hε).domainOrbit B) := by
  intro t ht
  have hB' : productH2Embedding B ∈ productSolenoidalSubspace :=
    (mem_productSolenoidalSubspace_iff _).2 ((productDivergenceFromH2_eq_zero_iff _).1 hB)
  have h := (productL2ToHMinus2.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t
    ((productInductionRealization u hu hε).domainOrbit_isForwardStrongSolution B t ht)
  change HasDerivWithinAt
    (fun s ↦ productL2ToHMinus2 (productH2Embedding
      ((productInductionRealization u hu hε).domainOrbit B s)))
    (productPhysicalInductionAction u ε ((productInductionRealization u hu hε).domainOrbit B t))
    (Set.Ici 0) t
  rw [← productL2ToHMinus2_domainOrbit_eq_physical u hu hε B hB' ht]
  exact h

/-- **Every strong solution of the curl form with divergence-free datum is the semigroup
orbit.**  If `w` is a forward strong solution of `productPhysicalInductionOperator u ε` with
`div w(0) = 0`, then `w(t) = S(t) w(0)` in `L²` for all `t ≥ 0`, where `S` is the induction
semigroup `productInductionSemigroup u hu hε`. -/
theorem productH2Embedding_eq_productInductionSemigroup_of_isForwardStrongSolution
    {w : ℝ → ProductC3H2}
    (hw : (productPhysicalInductionOperator u ε).IsForwardStrongSolution w)
    (hw0 : productDivergenceFromH2 (w 0) = 0) {t : ℝ} (ht : 0 ≤ t) :
    productH2Embedding (w t) =
      productInductionSemigroup u hu hε (Real.toNNReal t) (productH2Embedding (w 0)) := by
  have h := productPhysicalInductionOperator_forwardStrongSolutionsUnique u hu hε w
    ((productInductionRealization u hu hε).domainOrbit (w 0)) hw
    (isForwardStrongSolution_productPhysicalInductionOperator_domainOrbit u hu hε (w 0) hw0)
    (by rw [(productInductionRealization u hu hε).domainOrbit_zero]) t ht
  have hS := (productInductionRealization u hu hε).semigroup_eq_embedding_domainOrbit (w 0) t ht
  change productInductionSemigroup u hu hε (Real.toNNReal t) (productH2Embedding (w 0)) =
    productH2Embedding _ at hS
  rw [hS]
  exact productL2ToHMinus2_injective h

include hu hε in
/-- **The energy identity along solutions of the curl form** (`eq:energy-competition`,
dynamical form, for the paper's operator `L_{ε,u} B = ε ΔB + curl(u × B)`).  If `w` is a
forward strong solution of `productPhysicalInductionOperator u ε` with `div w(0) = 0`, then at
every `t > 0` the function `s ↦ ½‖w(s)‖₂²` is differentiable with derivative
`Re ⟨w(t), (w(t)·∇)u⟩ − ε ‖∇w(t)‖₂²`.  The solution is the domain orbit of the induction
semigroup for `s ≥ 0` (`productPhysicalInductionOperator_forwardStrongSolutionsUnique`), which
is an `L²` forward strong solution of the auxiliary operator, so the identity is
`hasDerivAt_half_norm_sq_of_isForwardStrongSolution` for that orbit. -/
theorem hasDerivAt_half_norm_sq_of_isForwardStrongSolution_physical
    {w : ℝ → ProductC3H2}
    (hw : (productPhysicalInductionOperator u ε).IsForwardStrongSolution w)
    (hw0 : productDivergenceFromH2 (w 0) = 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ ↦ (1 / 2 : ℝ) * ‖productH2Embedding (w s)‖ ^ 2)
      ((inner ℂ (productH2Embedding (w t)) (productInductionStretching u (w t))).re -
        ε * productGradientEnergy (w t)) t := by
  set v := (productInductionRealization u hu hε).domainOrbit (w 0)
  have hv0 : v 0 = w 0 := (productInductionRealization u hu hε).domainOrbit_zero (w 0)
  have heq : ∀ s, 0 ≤ s → w s = v s := fun s hs ↦
    (productPhysicalInductionOperator u ε).embedding_injective
      (productPhysicalInductionOperator_forwardStrongSolutionsUnique u hu hε w v hw
        (isForwardStrongSolution_productPhysicalInductionOperator_domainOrbit u hu hε (w 0) hw0)
        (by rw [hv0]) s hs)
  have h := hasDerivAt_half_norm_sq_of_isForwardStrongSolution u hu ε
    ((productInductionRealization u hu hε).domainOrbit_isForwardStrongSolution (w 0)) ht
  rw [heq t ht.le]
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds ht] with s hs
  rw [heq s hs.le]

end

end FastDynamo
