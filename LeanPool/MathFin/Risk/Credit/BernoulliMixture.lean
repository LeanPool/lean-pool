/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Gaussian.NormalQuantile
public import Mathlib.Algebra.Order.Star.Real

/-!
# Bernoulli mixture models of portfolio credit risk

In a **Bernoulli mixture model** the default indicators of the obligors of a loan portfolio are
conditionally independent given a random default probability `Q ∈ [0, 1]`, the state of the
economy. We use the standard representation (McNeil–Frey–Embrechts 2015, §11.2): obligor `i`
defaults on the event `{Uᵢ ≤ Q}`, where the `Uᵢ` are independent and uniform on `(0, 1)` and
independent of `Q`. Given `Q = q`, each obligor defaults with probability `q`, independently of
the others. Dependence between defaults comes only from the common `Q`.

* **Joint default probabilities are moments of the mixing variable** (QRM Exercise Book,
  Ex. 11.11a). For every group `s` of obligors, `P(all of s default) = E[Q^|s|]`
  (`measureReal_iInter_default_eq_integral_pow`). The proof is Fubini on the joint law
  `law(Q) ⊗ Unif(0,1)^ι`: given `Q = q`, the group defaults with probability `q^|s|`.
* **Default correlation is nonnegative** (Ex. 11.4a, 11.11b). For two distinct obligors the
  covariance of the default indicators is `P(Dᵢ ∩ Dⱼ) − P(Dᵢ) P(Dⱼ) = E[Q²] − E[Q]² = Var(Q)`
  (`measureReal_inter_default_sub_mul`), which is never negative. So the default correlation
  `ρ_Y = (π₂ − π₁²)/(π₁ − π₁²)` equals `Var(Q)/(π₁(1 − π₁))` (`defaultCorrelation_eq`).
* **The one-factor Gaussian threshold model is a Bernoulli mixture** (Ex. 11.2d, 11.9, 11.17a).
  Obligor `i` defaults when its asset value `√ρ F + √(1 − ρ) εᵢ` falls below `Φ⁻¹(π)`, with `F`
  and the `εᵢ` independent standard normals. That event is `{Φ(εᵢ) ≤ p(F)}`, where
  `p(f) = Φ((Φ⁻¹(π) − √ρ f)/√(1 − ρ))` (`oneFactor_default_iff`). The `Φ(εᵢ)` are uniform by the
  probability integral transform, so the joint default probabilities are
  `πₖ = ∫ p(x)^k φ(x) dx` (`oneFactor_measureReal_iInter_default`). Each obligor defaults with
  probability exactly `π`, because the asset value is again standard normal
  (`oneFactor_measureReal_default`).

## Main definitions

* `oneFactorPD`: the conditional default probability `Φ((Φ⁻¹(π) − √ρ f) / √(1 − ρ))` of the
  one-factor Gaussian threshold model at default probability `π`, asset correlation `ρ` and
  factor value `f`.

## Main results

* `measureReal_iInter_default_eq_integral_pow`: `πₖ = E[Q^k]`.
* `measureReal_inter_default_sub_mul`: the default covariance is `Var(Q)`.
* `defaultCorrelation_eq`: `ρ_Y = Var(Q)/(π₁(1 − π₁))`, and `defaultCorrelation_nonneg`.
* `oneFactor_asset_le_iff`, `oneFactor_default_iff`: the threshold event is the mixture event.
* `oneFactor_bernoulliMixture`: the one-factor model satisfies the mixture hypotheses.
* `oneFactor_measureReal_iInter_default`: `πₖ = ∫ p(x)^k dN(0,1)(x)` in the Gaussian model.
* `oneFactor_measureReal_default`: each obligor defaults with probability `π`.
* `oneFactor_measureReal_inter_default_sub_mul`: the default covariance is `Var(p(F))`.

## References

* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Section 11.2
* [*QRM Exercise Book*][QRMExerciseBook], Ex. 11.11(a); Ex. 11.2(c), 11.9; Ex. 11.4(a), 11.11(b);
  Ex. 11.4(a), 11.9

## Tags

Bernoulli mixture model, portfolio credit risk, default correlation, one-factor Gaussian model,
conditionally independent defaults, joint default probability, Vasicek model, MSC 91G40, MSC 60E05,
JEL G32, JEL G33
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type*} [Fintype ι]

/-! ### Joint default probabilities of a Bernoulli mixture -/

omit [Fintype ι] in
/-- **Joint default probabilities of a Bernoulli mixture are moments of the mixing variable**
(QRM Exercise Book, Ex. 11.11a). Obligor `i` defaults when `Uᵢ ≤ Q`, where the `Uᵢ` are independent
uniforms on `(0, 1)`, independent of the mixing variable `Q ∈ [0, 1]`. Then every group `s` of
obligors defaults jointly with probability `E[Q^|s|]`. -/
theorem measureReal_iInter_default_eq_integral_pow [Finite ι] {Q : Ω → ℝ} {U : ι → Ω → ℝ}
    (hQ : AEMeasurable Q P) (hQ01 : ∀ᵐ ω ∂P, Q ω ∈ Icc 0 1)
    (hU : ∀ i, HasLaw (U i) (volume.restrict (Ioo 0 1)) P) (hUind : iIndepFun U P)
    (hQU : Q ⟂ᵢ[P] fun ω i ↦ U i ω) (s : Finset ι) :
    P.real (⋂ i ∈ s, {ω | U i ω ≤ Q ω}) = ∫ ω, Q ω ^ s.card ∂P := by
  cases nonempty_fintype ι
  classical
  have hUv : AEMeasurable (fun ω i ↦ U i ω) P :=
    .of_eval fun i ↦ (hU i).aemeasurable
  -- the joint law of `(Q, U)` is `law(Q) ⊗ Unif(0,1)^ι`
  have hlawU : P.map (fun ω i ↦ U i ω) = Measure.pi fun _ ↦ volume.restrict (Ioo (0 : ℝ) 1) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map fun i ↦ (hU i).aemeasurable).1 hUind]
    exact congrArg Measure.pi (funext fun i ↦ (hU i).map_eq)
  have hjoint := (indepFun_iff_map_prod_eq_prod_map_map hQ hUv).1 hQU
  -- the joint default event is a preimage under `(Q, U)`
  let S : Set (ℝ × (ι → ℝ)) := ⋂ i ∈ s, {p | p.2 i ≤ p.1}
  have hS : MeasurableSet S := .biInter s.countable_toSet fun i _ ↦
    measurableSet_le ((measurable_pi_apply i).comp measurable_snd) measurable_fst
  have hpre : ⋂ i ∈ s, {ω | U i ω ≤ Q ω} = (fun ω ↦ (Q ω, fun i ↦ U i ω)) ⁻¹' S := by
    ext ω; simp [S]
  -- given `Q = q ∈ [0, 1]`, the group defaults with probability `q ^ |s|`
  have hsec (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
      (Measure.pi fun _ : ι ↦ volume.restrict (Ioo (0 : ℝ) 1)) (Prod.mk q ⁻¹' S) =
        ENNReal.ofReal (q ^ s.card) := by
    have hbox : Prod.mk q ⁻¹' S = univ.pi fun i ↦ if i ∈ s then Iic q else univ := by
      ext v
      simp only [S, mem_preimage, mem_iInter, mem_ofPred_eq, mem_univ_pi]
      refine ⟨fun h i ↦ ?_, fun h i hi ↦ by simpa [hi] using h i⟩
      split_ifs with hi
      exacts [h i hi, mem_univ _]
    rw [hbox, Measure.pi_pi, ENNReal.ofReal_pow hq.1, ← Finset.prod_const,
      ← Fintype.prod_ite_mem s fun _ ↦ ENNReal.ofReal q]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    split_ifs
    · exact uniformIoo_Iic hq.1 hq.2
    · exact measure_univ
  have hint : Integrable (fun ω ↦ Q ω ^ s.card) P :=
    .of_bound (hQ.pow_const _).aestronglyMeasurable 1 <| hQ01.mono fun ω hω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hω.1 _)]
      exact pow_le_one₀ hω.1 hω.2
  rw [hpre, measureReal_def, ← Measure.map_apply_of_aemeasurable (hQ.prodMk hUv) hS, hjoint,
    hlawU, Measure.prod_apply hS,
        lintegral_map' (measurable_measure_prodMk_left hS).aemeasurable hQ,
    lintegral_congr_ae (hQ01.mono fun ω hω ↦ hsec (Q ω) hω),
    ← ofReal_integral_eq_lintegral_ofReal hint (hQ01.mono fun ω hω ↦ pow_nonneg hω.1 _),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae (hQ01.mono fun ω hω ↦ pow_nonneg hω.1 _))]

omit [Fintype ι] in
/-- **The default covariance of a Bernoulli mixture is the variance of the mixing variable**
(QRM Exercise Book, Ex. 11.4a): `P(Dᵢ ∩ Dⱼ) − P(Dᵢ) P(Dⱼ) = Var(Q)` for distinct obligors. -/
theorem measureReal_inter_default_sub_mul [Finite ι] {Q : Ω → ℝ} {U : ι → Ω → ℝ}
    (hQ : AEMeasurable Q P) (hQ01 : ∀ᵐ ω ∂P, Q ω ∈ Icc 0 1)
    (hU : ∀ i, HasLaw (U i) (volume.restrict (Ioo 0 1)) P) (hUind : iIndepFun U P)
    (hQU : Q ⟂ᵢ[P] fun ω i ↦ U i ω) {i j : ι} (hij : i ≠ j) :
    P.real ({ω | U i ω ≤ Q ω} ∩ {ω | U j ω ≤ Q ω}) -
        P.real {ω | U i ω ≤ Q ω} * P.real {ω | U j ω ≤ Q ω} = Var[Q; P] := by
  classical
  have hπ (k : ι) : P.real {ω | U k ω ≤ Q ω} = P[Q] := by
    simpa using measureReal_iInter_default_eq_integral_pow hQ hQ01 hU hUind hQU {k}
  have hπ₂ : P.real ({ω | U i ω ≤ Q ω} ∩ {ω | U j ω ≤ Q ω}) = P[Q ^ 2] := by
    simpa [Finset.card_pair hij, Pi.pow_apply] using
      measureReal_iInter_default_eq_integral_pow hQ hQ01 hU hUind hQU {i, j}
  have hQ2 : MemLp Q 2 P := .of_bound hQ.aestronglyMeasurable 1 <| hQ01.mono fun ω hω ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg hω.1]; exact hω.2
  rw [hπ₂, hπ, hπ, variance_eq_sub hQ2]
  ring

omit [Fintype ι] in
/-- **Default correlation in a Bernoulli mixture** (QRM Exercise Book, Ex. 11.11b): with
`π₁ = P(Dᵢ)` and `π₂ = P(Dᵢ ∩ Dⱼ)`, the correlation `(π₂ − π₁²)/(π₁ − π₁²)` of the default
indicators equals `Var(Q) / (E[Q](1 − E[Q]))`. -/
theorem defaultCorrelation_eq [Finite ι] {Q : Ω → ℝ} {U : ι → Ω → ℝ}
    (hQ : AEMeasurable Q P) (hQ01 : ∀ᵐ ω ∂P, Q ω ∈ Icc 0 1)
    (hU : ∀ i, HasLaw (U i) (volume.restrict (Ioo 0 1)) P) (hUind : iIndepFun U P)
    (hQU : Q ⟂ᵢ[P] fun ω i ↦ U i ω) {i j : ι} (hij : i ≠ j) :
    (P.real ({ω | U i ω ≤ Q ω} ∩ {ω | U j ω ≤ Q ω}) - P.real {ω | U i ω ≤ Q ω} ^ 2) /
        (P.real {ω | U i ω ≤ Q ω} - P.real {ω | U i ω ≤ Q ω} ^ 2) =
      Var[Q; P] / (P[Q] * (1 - P[Q])) := by
  classical
  have hπ (k : ι) : P.real {ω | U k ω ≤ Q ω} = P[Q] := by
    simpa using measureReal_iInter_default_eq_integral_pow hQ hQ01 hU hUind hQU {k}
  have hcov := measureReal_inter_default_sub_mul hQ hQ01 hU hUind hQU hij
  rw [hπ j, ← hπ i, ← sq] at hcov
  rw [hcov, hπ i]
  ring

omit [Fintype ι] in
/-- **Default correlation in a Bernoulli mixture is nonnegative** (QRM Exercise Book, Ex. 11.4a):
the covariance of two default indicators is a variance. -/
theorem defaultCorrelation_nonneg [Finite ι] {Q : Ω → ℝ} {U : ι → Ω → ℝ}
    (hQ : AEMeasurable Q P) (hQ01 : ∀ᵐ ω ∂P, Q ω ∈ Icc 0 1)
    (hU : ∀ i, HasLaw (U i) (volume.restrict (Ioo 0 1)) P) (hUind : iIndepFun U P)
    (hQU : Q ⟂ᵢ[P] fun ω i ↦ U i ω) {i j : ι} (hij : i ≠ j) :
    P.real {ω | U i ω ≤ Q ω} * P.real {ω | U j ω ≤ Q ω} ≤
      P.real ({ω | U i ω ≤ Q ω} ∩ {ω | U j ω ≤ Q ω}) := by
  have := measureReal_inter_default_sub_mul hQ hQ01 hU hUind hQU hij
  linarith [variance_nonneg Q P]

/-! ### The one-factor Gaussian threshold model -/

/-- The **conditional default probability** of the one-factor Gaussian threshold model with
default probability `π` and asset correlation `ρ`, given the systematic factor `F = f`:
`p(f) = Φ((Φ⁻¹(π) − √ρ f)/√(1 − ρ))`. -/
noncomputable def oneFactorPD (π ρ f : ℝ) : ℝ :=
  Phi ((PhiInv π - √ρ * f) / √(1 - ρ))

lemma measurable_oneFactorPD (π ρ : ℝ) : Measurable (oneFactorPD π ρ) :=
  continuous_Phi.measurable.comp (by fun_prop)

/-- The asset value `√ρ f + √(1 − ρ) e` falls below the threshold `Φ⁻¹(π)` exactly when the
idiosyncratic term `e` falls below the factor-dependent level `(Φ⁻¹(π) − √ρ f)/√(1 − ρ)`. -/
lemma oneFactor_asset_le_iff {π ρ : ℝ} (hρ : ρ < 1) (f e : ℝ) :
    √ρ * f + √(1 - ρ) * e ≤ PhiInv π ↔ e ≤ (PhiInv π - √ρ * f) / √(1 - ρ) := by
  rw [le_div_iff₀ (Real.sqrt_pos.2 (sub_pos.2 hρ))]
  constructor <;> intro <;> linarith

/-- **The threshold event is a mixture event.** The asset value `√ρ f + √(1 − ρ) e` falls below
the threshold `Φ⁻¹(π)` exactly when `Φ(e) ≤ p(f)`. -/
theorem oneFactor_default_iff {π ρ : ℝ} (hρ : ρ < 1) (f e : ℝ) :
    √ρ * f + √(1 - ρ) * e ≤ PhiInv π ↔ Phi e ≤ oneFactorPD π ρ f := by
  rw [oneFactor_asset_le_iff hρ, oneFactorPD, strictMono_Phi.le_iff_le]

omit [IsProbabilityMeasure P] [Fintype ι] in
/-- **The one-factor Gaussian threshold model is a Bernoulli mixture.** With `F` and the `εᵢ`
independent standard normals, the mixing variable `Q = p(F)` and the variables `Uᵢ = Φ(εᵢ)`
satisfy the hypotheses of the mixture theorems: `Q ∈ [0, 1]`, the `Uᵢ` are independent uniforms
on `(0, 1)` (the probability integral transform), and `Q` is independent of them. The threshold
events are the mixture events `{Uᵢ ≤ Q}` (`oneFactor_default_iff`). -/
theorem oneFactor_bernoulliMixture {π ρ : ℝ} {F : Ω → ℝ} {ε : ι → Ω → ℝ}
    (hF : HasLaw F (gaussianReal 0 1) P) (hε : ∀ i, HasLaw (ε i) (gaussianReal 0 1) P)
    (hεind : iIndepFun ε P) (hFε : F ⟂ᵢ[P] fun ω i ↦ ε i ω) :
    AEMeasurable (fun ω ↦ oneFactorPD π ρ (F ω)) P ∧
      (∀ᵐ ω ∂P, oneFactorPD π ρ (F ω) ∈ Icc 0 1) ∧
      (∀ i, HasLaw (fun ω ↦ Phi (ε i ω)) (volume.restrict (Ioo 0 1)) P) ∧
      iIndepFun (fun i ω ↦ Phi (ε i ω)) P ∧
      (fun ω ↦ oneFactorPD π ρ (F ω)) ⟂ᵢ[P] fun ω i ↦ Phi (ε i ω) := by
  have hPhi : Measurable Phi := continuous_Phi.measurable
  refine ⟨(measurable_oneFactorPD π ρ).comp_aemeasurable hF.aemeasurable,
    ae_of_all _ fun ω ↦ Ioo_subset_Icc_self (Phi_mem_Ioo _), fun i ↦ ?_,
    hεind.comp (fun _ ↦ Phi) fun _ ↦ hPhi,
    hFε.comp (measurable_oneFactorPD π ρ)
      (.of_eval fun i ↦ hPhi.comp (measurable_pi_apply i))⟩
  have h := hasLaw_cdf (hε i) (by rw [cdf_gaussianReal_zero_one]; exact continuous_Phi)
  simpa only [cdf_gaussianReal_zero_one] using h

omit [Fintype ι] in
/-- **Joint default probabilities in the one-factor Gaussian threshold model** (QRM Exercise Book,
Ex. 11.9). With `F` and the `εᵢ` independent standard normals, every group `s` of obligors
defaults jointly with probability `∫ p(x)^|s| dN(0,1)(x)`: the model is a Bernoulli mixture
(`oneFactor_bernoulliMixture`), so this is `measureReal_iInter_default_eq_integral_pow`. -/
theorem oneFactor_measureReal_iInter_default [Finite ι] {π ρ : ℝ} {F : Ω → ℝ} {ε : ι → Ω → ℝ}
    (hF : HasLaw F (gaussianReal 0 1) P) (hε : ∀ i, HasLaw (ε i) (gaussianReal 0 1) P)
    (hεind : iIndepFun ε P) (hFε : F ⟂ᵢ[P] fun ω i ↦ ε i ω) (hρ : ρ < 1) (s : Finset ι) :
    P.real (⋂ i ∈ s, {ω | √ρ * F ω + √(1 - ρ) * ε i ω ≤ PhiInv π}) =
      ∫ x, oneFactorPD π ρ x ^ s.card ∂gaussianReal 0 1 := by
  obtain ⟨hQ, hQ01, hU, hUind, hQU⟩ := oneFactor_bernoulliMixture (π := π) (ρ := ρ) hF hε hεind hFε
  simp_rw [oneFactor_default_iff hρ]
  rw [measureReal_iInter_default_eq_integral_pow hQ hQ01 hU hUind hQU s,
    ← hF.integral_comp (((measurable_oneFactorPD π ρ).pow_const _).aestronglyMeasurable)]
  rfl

omit [IsProbabilityMeasure P] in
/-- **Each obligor defaults with probability `π`** in the one-factor Gaussian threshold model: the
asset value `√ρ F + √(1 − ρ) ε` of independent standard normals is again standard normal, and it
falls below `Φ⁻¹(π)` with probability `Φ(Φ⁻¹(π)) = π`. -/
theorem oneFactor_measureReal_default {π ρ : ℝ} {F e : Ω → ℝ}
    (hF : HasLaw F (gaussianReal 0 1) P) (he : HasLaw e (gaussianReal 0 1) P) (hFe : F ⟂ᵢ[P] e)
    (hπ : π ∈ Ioo 0 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    P.real {ω | √ρ * F ω + √(1 - ρ) * e ω ≤ PhiInv π} = π := by
  have hsum := gaussianReal_add_gaussianReal_of_indepFun
    (hFe.comp (measurable_const_mul √ρ) (measurable_const_mul √(1 - ρ)))
    (gaussianReal_const_mul hF √ρ) (gaussianReal_const_mul he √(1 - ρ))
  have hvar : (.mk (√ρ ^ 2) (sq_nonneg _) * 1 + .mk (√(1 - ρ) ^ 2) (sq_nonneg _) * 1 : ℝ≥0)
      = 1 := by
    apply NNReal.coe_injective
    simp [Real.sq_sqrt hρ0, Real.sq_sqrt (sub_nonneg.2 hρ1)]
  rw [mul_zero, mul_zero, add_zero, hvar] at hsum
  have hlaw : HasLaw (fun ω ↦ √ρ * F ω + √(1 - ρ) * e ω) (gaussianReal 0 1) P :=
    ⟨(hF.aemeasurable.const_mul _).add (he.aemeasurable.const_mul _), by rw [← hsum]; rfl⟩
  rw [hlaw.measureReal_eq (p := (· ≤ PhiInv π)) measurableSet_Iic]
  change (gaussianReal 0 1).real (Iic (PhiInv π)) = π
  rw [← cdf_eq_real, cdf_gaussianReal_zero_one, Phi_PhiInv hπ]

omit [Fintype ι] in
/-- **The default covariance in the one-factor Gaussian threshold model is a variance**
(QRM Exercise Book, Ex. 11.4a in the Gaussian model). For distinct obligors,
`P(Dᵢ ∩ Dⱼ) − P(Dᵢ) P(Dⱼ) = Var(p(F))`, the variance of the conditional default probability: the
model is a Bernoulli mixture (`oneFactor_bernoulliMixture`), so this is
`measureReal_inter_default_sub_mul`. -/
theorem oneFactor_measureReal_inter_default_sub_mul [Finite ι] {π ρ : ℝ} {F : Ω → ℝ}
    {ε : ι → Ω → ℝ} (hF : HasLaw F (gaussianReal 0 1) P)
    (hε : ∀ i, HasLaw (ε i) (gaussianReal 0 1) P) (hεind : iIndepFun ε P)
    (hFε : F ⟂ᵢ[P] fun ω i ↦ ε i ω) (hρ : ρ < 1) {i j : ι} (hij : i ≠ j) :
    P.real ({ω | √ρ * F ω + √(1 - ρ) * ε i ω ≤ PhiInv π} ∩
          {ω | √ρ * F ω + √(1 - ρ) * ε j ω ≤ PhiInv π}) -
        P.real {ω | √ρ * F ω + √(1 - ρ) * ε i ω ≤ PhiInv π} *
          P.real {ω | √ρ * F ω + √(1 - ρ) * ε j ω ≤ PhiInv π} =
      Var[fun ω ↦ oneFactorPD π ρ (F ω); P] := by
  obtain ⟨hQ, hQ01, hU, hUind, hQU⟩ := oneFactor_bernoulliMixture (π := π) (ρ := ρ) hF hε hεind hFε
  simp_rw [oneFactor_default_iff hρ]
  exact measureReal_inter_default_sub_mul hQ hQ01 hU hUind hQU hij

end MathFin
