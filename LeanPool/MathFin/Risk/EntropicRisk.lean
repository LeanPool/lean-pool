/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Risk.LawInvariance
public import LeanPool.MathFin.Risk.UtilityDerivation
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Entropic risk: the certainty equivalent of exponential utility

The **entropic risk measure** of a loss `X` with risk aversion `γ > 0` is
`ρ_γ(X) = γ⁻¹ log E[exp (γ X)]`. It is the cash amount an agent with exponential utility
`u(x) = −exp (−γ x)` is indifferent to paying instead of bearing the loss: the position `−X` is
acceptable under `u` at wealth `0` exactly when `ρ_γ(X) ≤ 0` (`acceptableUnderUtility_exp_iff`).
This is the joint of the choice limb with the risk limb: the acceptance set of `UtilityDerivation`,
for the exponential utility, is the acceptance set of the entropic risk measure.

The entropic risk measure is the standard example of a **convex risk measure that is not coherent**
(`isConvexRiskMeasure_entropicRisk`, `not_isCoherentRiskMeasure_entropicRisk`): convexity is Hölder
(weighted AM-GM under the expectation), and positive homogeneity fails because `ρ_γ(c X)` is the
entropic risk at aversion `c γ`, not `c ρ_γ(X)`. It is law invariant
(`isLawInvariant_entropicRisk`).

The convexity and acceptance statements are made on a finite state space with a probability
measure, where every loss is integrable and `exp (γ X)` is too: on a general space `E[exp (γ X)]`
may be infinite, which Lean's Bochner integral reads as `0`, so convexity on all integrable
losses would be a statement about that junk value. The acceptance statement is made
against `acceptableUnderUtility`, which works on finite weights `p i = P {i}`.

## Main definitions

* `entropicRisk`: `ρ_γ(X) = γ⁻¹ log E[exp (γ X)]`.

## Main results

* `isConvexRiskMeasure_entropicRisk`: on a finite probability space, `ρ_γ` is a convex risk measure.
* `not_isCoherentRiskMeasure_entropicRisk`: it is not coherent: positive homogeneity fails on a
  fair coin.
* `acceptableUnderUtility_exp_iff`: the position `−L` is acceptable under exponential utility at
  wealth `0` iff `ρ_γ(L) ≤ 0`.
* `isLawInvariant_entropicRisk`: `ρ_γ` depends on the loss only through its law.

## References

* [H. Föllmer and A. Schied, *Convex measures of risk and trading constraints*][FollmerSchied2002]
* [H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete
  Time*][FollmerSchied], §4.9

## Tags

entropic risk, certainty equivalent, exponential utility, convex risk measure, acceptance set,
Hölder inequality, MSC 91G70, MSC 91B16, JEL G32, JEL D81
-/

@[expose] public section

namespace MathFin

open MeasureTheory Real

/-- The **entropic risk** of a loss `X` at risk aversion `γ`: `γ⁻¹ log E[exp (γ X)]`. -/
noncomputable def entropicRisk {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) (P : Measure Ω)
    (γ : ℝ) : ℝ :=
  γ⁻¹ * log (∫ ω, exp (γ * X ω) ∂P)

/-- **Entropic risk is law invariant**: `E[exp (γ X)]` is an integral against the law of `X`. -/
theorem isLawInvariant_entropicRisk {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (γ : ℝ) :
    IsLawInvariant P fun X ↦ entropicRisk X P γ := by
  have key {X : Ω → ℝ} (hX : AEMeasurable X P) :
      ∫ ω, exp (γ * X ω) ∂P = ∫ x, exp (γ * x) ∂(P.map X) :=
    (integral_map (f := fun x ↦ exp (γ * x)) hX
      (Continuous.aestronglyMeasurable (by fun_prop))).symm
  intro X Y hX hY h
  simp only [entropicRisk, key hX, key hY, h]

/-- The weighted AM-GM step of the Hölder inequality, normalised by `A` and `B`. -/
lemma rpow_mul_rpow_le {A B s t a b : ℝ} (hA : 0 < A) (hB : 0 < B) (hs : 0 < s) (ht : 0 < t)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    s ^ a * t ^ b ≤ A ^ a * B ^ b * (a * (s / A) + b * (t / B)) := by
  have h := Real.geom_mean_le_arith_mean2_weighted ha hb (div_pos hs hA).le (div_pos ht hB).le hab
  rw [Real.div_rpow hs.le hA.le, Real.div_rpow ht.le hB.le] at h
  have hA' := Real.rpow_pos_of_pos hA a
  have hB' := Real.rpow_pos_of_pos hB b
  calc s ^ a * t ^ b = A ^ a * B ^ b * (s ^ a / A ^ a * (t ^ b / B ^ b)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

section Finite

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {P : Measure ι} [IsProbabilityMeasure P] {γ : ℝ} {X Y : ι → ℝ}

omit [Fintype ι] in
lemma integral_exp_mul_pos (γ : ℝ) (X : ι → ℝ) [Finite ι] : 0 < ∫ ω, exp (γ * X ω) ∂P :=
  integral_exp_pos (f := fun ω ↦ γ * X ω) .of_finite

omit [Fintype ι] in
/-- Entropic risk is monotone. -/
theorem entropicRisk_mono [Finite ι] (hγ : 0 < γ) (h : X ≤ᵐ[P] Y) :
    entropicRisk X P γ ≤ entropicRisk Y P γ := by
  have := integral_mono_ae (μ := P) .of_finite .of_finite
    (h.mono fun ω hω ↦ Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hω hγ.le))
  exact mul_le_mul_of_nonneg_left (Real.log_le_log (integral_exp_mul_pos γ X) this)
    (inv_nonneg.2 hγ.le)

omit [Fintype ι] in
/-- Entropic risk is cash invariant: `ρ_γ(X + m) = ρ_γ(X) + m`. -/
theorem entropicRisk_add_const [Finite ι] (hγ : 0 < γ) (X : ι → ℝ) (m : ℝ) :
    entropicRisk (fun ω ↦ X ω + m) P γ = entropicRisk X P γ + m := by
  have e (ω : ι) : exp (γ * (X ω + m)) = exp (γ * m) * exp (γ * X ω) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [entropicRisk, e, integral_const_mul]
  rw [Real.log_mul (exp_pos _).ne' (integral_exp_mul_pos γ X).ne', Real.log_exp]
  field_simp
  ring

omit [Fintype ι] in
/-- Entropic risk is convex: Hölder's inequality `E[e^{γ(aX + bY)}] ≤ E[e^{γX}]^a E[e^{γY}]^b`
under the logarithm. -/
theorem entropicRisk_convex [Finite ι] (hγ : 0 < γ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (X Y : ι → ℝ) :
    entropicRisk (fun ω ↦ a * X ω + b * Y ω) P γ ≤
      a * entropicRisk X P γ + b * entropicRisk Y P γ := by
  have hA := integral_exp_mul_pos (P := P) γ X
  have hB := integral_exp_mul_pos (P := P) γ Y
  set A := ∫ ω, exp (γ * X ω) ∂P
  set B := ∫ ω, exp (γ * Y ω) ∂P
  have pt (ω : ι) : exp (γ * (a * X ω + b * Y ω)) ≤
      A ^ a * B ^ b * (a * (exp (γ * X ω) / A) + b * (exp (γ * Y ω) / B)) := by
    refine le_of_eq_of_le ?_ (rpow_mul_rpow_le hA hB (exp_pos (γ * X ω)) (exp_pos (γ * Y ω))
      ha hb hab)
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]; congr 1; ring
  have hint : ∫ ω, exp (γ * (a * X ω + b * Y ω)) ∂P ≤ A ^ a * B ^ b := by
    refine (integral_mono .of_finite .of_finite pt).trans_eq ?_
    rw [integral_const_mul, integral_add .of_finite .of_finite, integral_const_mul,
      integral_const_mul, integral_div, integral_div, div_self hA.ne', div_self hB.ne']
    rw [mul_one, mul_one, hab, mul_one]
  have hl := Real.log_le_log (integral_exp_mul_pos (P := P) γ (fun ω ↦ a * X ω + b * Y ω)) hint
  rw [Real.log_mul (Real.rpow_pos_of_pos hA a).ne' (Real.rpow_pos_of_pos hB b).ne',
    Real.log_rpow hA, Real.log_rpow hB] at hl
  calc entropicRisk (fun ω ↦ a * X ω + b * Y ω) P γ
      ≤ γ⁻¹ * (a * log A + b * log B) :=
        mul_le_mul_of_nonneg_left hl (inv_nonneg.2 hγ.le)
    _ = a * entropicRisk X P γ + b * entropicRisk Y P γ := by simp only [entropicRisk, A, B]; ring

omit [Fintype ι] in
/-- **Entropic risk is a convex risk measure** on a finite probability space. -/
theorem isConvexRiskMeasure_entropicRisk [Finite ι] (hγ : 0 < γ) :
    IsConvexRiskMeasure P fun X ↦ entropicRisk X P γ where
  mono _ _ _ _ h := entropicRisk_mono hγ h
  add_const _ _ m := entropicRisk_add_const hγ _ m
  convexOn := ⟨fun _ _ _ _ _ _ _ _ _ ↦ .of_finite, fun X _ Y _ _ _ ha hb hab ↦
    entropicRisk_convex hγ ha hb hab X Y⟩

/-- **Acceptance under exponential utility is entropic risk at most zero.** On a finite
probability space with the weights `p i = P {i}`, the position `−L` is acceptable under the
exponential utility `u(x) = −exp (−γ x)` at wealth `0` (`acceptableUnderUtility`) exactly when
the entropic risk `ρ_γ(L)` of the loss `L` is nonpositive. -/
theorem acceptableUnderUtility_exp_iff (hγ : 0 < γ) (L : ι → ℝ) :
    acceptableUnderUtility Finset.univ (fun i ↦ P.real {i}) (fun x ↦ -exp (-γ * x)) 0 (-L) ↔
      entropicRisk L P γ ≤ 0 := by
  have hE : ∫ ω, exp (γ * L ω) ∂P = ∑ i, P.real {i} * exp (γ * L i) := by
    rw [integral_fintype .of_finite]; simp only [smul_eq_mul]
  have hpos := integral_exp_mul_pos (P := P) γ L
  have e (i : ι) : P.real {i} * -exp (-γ * (0 + (-L) i)) = -(P.real {i} * exp (γ * L i)) := by
    rw [mul_neg]; congr 3; simp only [Pi.neg_apply, zero_add]; ring
  simp only [acceptableUnderUtility, expectedUtility]
  simp only [e, Finset.sum_neg_distrib, mul_zero, Real.exp_zero, ← hE, neg_le_neg_iff]
  simp only [entropicRisk]
  generalize ∫ ω, exp (γ * L ω) ∂P = I at hpos ⊢
  have hlog : log I ≤ 0 ↔ I ≤ 1 := by simpa using Real.log_le_log_iff hpos one_pos
  rw [← hlog]
  refine ⟨fun h ↦ mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hγ.le) h, fun h ↦ ?_⟩
  by_contra hc
  exact absurd h (not_le.2 (mul_pos (inv_pos.2 hγ) (not_le.1 hc)))

end Finite

/-- **Entropic risk is convex and not coherent.** On a fair coin, the entropic risk of the loss
`(2, 0)` is not twice that of `(1, 0)`: positive homogeneity fails for every `γ > 0`. -/
theorem not_isCoherentRiskMeasure_entropicRisk {γ : ℝ} (hγ : 0 < γ) :
    ∃ (P : Measure (Fin 2)) (_ : IsProbabilityMeasure P),
      ¬ IsCoherentRiskMeasure P fun X ↦ entropicRisk X P γ := by
  let p : PMF (Fin 2) := PMF.ofFintype (fun _ ↦ (2 : ENNReal)⁻¹) (by
    rw [Fin.sum_univ_two, ENNReal.inv_two_add_inv_two])
  refine ⟨p.toMeasure, inferInstance, fun h ↦ ?_⟩
  have hw (i : Fin 2) : (p.toMeasure).real {i} = 1 / 2 := by
    rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i)]
    simp [p]
  have key (a b : ℝ) : entropicRisk (![a, b] : Fin 2 → ℝ) p.toMeasure γ =
      γ⁻¹ * log ((exp (γ * a) + exp (γ * b)) / 2) := by
    rw [entropicRisk, integral_fintype .of_finite]
    simp only [Fin.sum_univ_two, hw, smul_eq_mul]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    congr 2; ring
  have h2 : entropicRisk (![2, 0] : Fin 2 → ℝ) p.toMeasure γ =
      2 * entropicRisk (![1, 0] : Fin 2 → ℝ) p.toMeasure γ := by
    have := h.const_mul (X := ![1, 0]) .of_finite (c := 2) (by norm_num)
    rw [show (fun ω ↦ 2 * (![1, 0] : Fin 2 → ℝ) ω) = ![2, 0] by
      ext i; fin_cases i <;> simp] at this
    exact this
  rw [key, key] at h2
  simp only [mul_zero, Real.exp_zero, mul_one] at h2
  have hu : exp (γ * 2) = exp γ * exp γ := by rw [← Real.exp_add]; ring_nf
  have hu1 : 1 < exp γ := by linarith [Real.add_one_lt_exp hγ.ne']
  rw [hu] at h2
  have h3 : log ((exp γ ^ 2 + 1) / 2) = 2 * log ((exp γ + 1) / 2) := by
    field_simp at h2; linarith
  have h4 := Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity))
    (h3.trans (by rw [Real.log_pow]; norm_num) : log ((exp γ ^ 2 + 1) / 2) =
      log (((exp γ + 1) / 2) ^ 2))
  nlinarith [mul_pos (sub_pos.2 hu1) (sub_pos.2 hu1)]

end MathFin
