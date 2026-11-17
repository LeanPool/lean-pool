/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.LocalSlope.Basic
public import LeanPool.KLS.FunctionalInequalities.Probability.Support.Affine

/-! # Local-slope Poincaré bounds

`Holds` uses the given coordinate law; `Intrinsic.optimalConstant` first takes the intrinsic law.
`Holds.memLp_two` shows that the square-integrability field of the test class is automatic under a
finite constant: truncation at levels `±k` and Fatou's lemma give `f ∈ L²` for every locally
Lipschitz `f` of finite local-slope energy.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FunctionalInequalities.Poincare.LocalSlope

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- A finite bound on all literature tests in the displayed coordinate space.
The extended variance is finite by `Energy.LocalSlope.Admissible.memLp_two`;
no real-valued infinite integral is used. -/
def Holds (ν : ProbabilityMeasure E) (C : NNReal) : Prop :=
  ∀ f : E → ℝ, Energy.LocalSlope.Admissible ν f →
    evariance f (ν : Measure E) ≤ (C : ENNReal) * Energy.LocalSlope.energy ν f

/-- The infimum of finite nonnegative Poincaré bounds for `Probability.intrinsicMeasure μ`.
Intrinsic coordinates remove redundant affine directions using an affine isometry; they do not
normalize the covariance. An empty set of finite bounds gives `⊤`. A zero-dimensional intrinsic
coordinate space has value zero, as proved below. -/
def Intrinsic.optimalConstant (μ : ProbabilityMeasure E) : ENNReal :=
  ⨅ C : {C : NNReal // Poincare.LocalSlope.Holds (Probability.intrinsicMeasure μ) C},
    (C.1 : ENNReal)

omit [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E]
  [SecondCountableTopology E] [FiniteDimensional ℝ E] in
/-- All tests on a zero-dimensional coordinate space have zero variance. -/
theorem holds_zero_of_subsingleton [Subsingleton E] (ν : ProbabilityMeasure E) :
    Holds ν 0 := by
  intro f _
  have hf : f = fun _ ↦ f 0 := funext fun y ↦ congrArg f (Subsingleton.elim y 0)
  rw [hf]
  simp [evariance]

section DegenerateConstants

omit [CompleteSpace E]
/-- The literature optimum includes the zero-dimensional case with value zero. -/
theorem Intrinsic.constant_eq_zero_of_subsingleton [Subsingleton E] (μ : ProbabilityMeasure E) :
    Poincare.LocalSlope.Intrinsic.optimalConstant μ = 0 := by
  apply le_antisymm ?_ bot_le
  exact
    iInf_le_of_le
      ⟨0, Poincare.LocalSlope.holds_zero_of_subsingleton (Probability.intrinsicMeasure μ)⟩
      (by simp)

/-- A zero-dimensional direction space gives literature optimum zero: every intrinsic test is
constant there. -/
theorem Intrinsic.constant_eq_zero_of_direction_subsingleton (μ : ProbabilityMeasure E)
    [Subsingleton (Probability.affineSupport μ).direction] :
    Poincare.LocalSlope.Intrinsic.optimalConstant μ = 0 := by
  apply le_antisymm ?_ bot_le
  exact
    iInf_le_of_le
      ⟨0, Poincare.LocalSlope.holds_zero_of_subsingleton (Probability.intrinsicMeasure μ)⟩
      (by simp)

/-- The zero-dimensional case stated through the direction submodule. -/
theorem Intrinsic.constant_eq_zero_of_direction_eq_bot (μ : ProbabilityMeasure E)
    (h : (Probability.affineSupport μ).direction = ⊥) :
    Poincare.LocalSlope.Intrinsic.optimalConstant μ = 0 := by
  have : Subsingleton (Probability.affineSupport μ).direction :=
    Submodule.subsingleton_iff_eq_bot.mpr h
  exact Intrinsic.constant_eq_zero_of_direction_subsingleton μ

end DegenerateConstants

section Truncation

open Filter

/-! ### Square integrability from a finite constant -/

/-- Truncation at `±k`, `k ≥ 0`, does not increase the absolute value. -/
private theorem abs_clamp_le {k : ℝ} (hk : 0 ≤ k) (t : ℝ) : |max (-k) (min k t)| ≤ |t| := by
  rw [abs_le]
  rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩ <;> constructor <;> simp only [max_def, min_def] <;>
      split_ifs <;>
    linarith

/-- Truncation at `±k`, `k ≥ 0`, is bounded by `k`. -/
private theorem abs_clamp_le_self {k : ℝ} (hk : 0 ≤ k) (t : ℝ) : |max (-k) (min k t)| ≤ k := by
  rw [abs_le]
  constructor <;> simp only [max_def, min_def] <;> split_ifs <;> linarith

/-- Truncation at `±k` fixes the values in `[-k, k]`. -/
private theorem clamp_eq {k t : ℝ} (ht : |t| ≤ k) : max (-k) (min k t) = t := by
  rw [abs_le] at ht
  rw [min_eq_right ht.2, max_eq_right ht.1]

/-- Truncation at `±k` is `1`-Lipschitz. -/
private theorem lipschitzWith_clamp (k : ℝ) :
    LipschitzWith 1 (fun t : ℝ ↦ max (-k) (min k t)) :=
  (LipschitzWith.id.const_min k).const_max (-k)

/-- `ENNReal.ofReal` is additive and homogeneous on the nonnegative expression `2y + 2z`. -/
private theorem ofReal_two_mul_add_two_mul {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    ENNReal.ofReal (2 * y + 2 * z) = 2 * ENNReal.ofReal y + 2 * ENNReal.ofReal z := by
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
/-- A finite local-slope Poincaré constant forces square integrability: every locally Lipschitz
`f` of finite local-slope energy lies in `L²(ν)`, although `L²` is a field of the test class.

The truncations `T_k f = max (-k) (min k f)` are bounded admissible tests with no larger slope,
so `Var_ν(T_k f) ≤ C · energy ν f = M` uniformly in `k`. On a sublevel set `{|f| ≤ a}` of
mass more than `1/2` the bound `m_k² ≤ 2 (T_k f - m_k)² + 2 a²` controls the means `m_k`, hence
`∫ (T_k f)²` is bounded, and Fatou's lemma passes the bound to `f`. Used for the unit-energy
gradient form of Letwin arXiv:2607.24164v1, Equation (1.1), which has no `L²` premise. -/
theorem Holds.memLp_two {ν : ProbabilityMeasure E} {C : NNReal} (hC : Holds ν C) {f : E → ℝ}
    (hf : LocallyLipschitz f) (he : Energy.LocalSlope.energy ν f ≠ ⊤) :
    MemLp f 2 (ν : Measure E) := by
  set μ : Measure E := (ν : Measure E)
  set T : ℕ → E → ℝ := fun k x ↦ max (-(k : ℝ)) (min (k : ℝ) (f x)) with hT
  have hfc : Continuous f := hf.continuous
  have hTc : ∀ k, Continuous (T k) := fun k ↦ continuous_const.max (continuous_const.min hfc)
  have hslope : ∀ k x, Energy.LocalSlope.apply (T k) x ≤ Energy.LocalSlope.apply f x := by
    intro k x
    refine Energy.LocalSlope.apply_le_of_dist_le one_pos fun y _ ↦ ?_
    simpa using (lipschitzWith_clamp (k : ℝ)).dist_le_mul (f y) (f x)
  have henergy : ∀ k, Energy.LocalSlope.energy ν (T k) ≤ Energy.LocalSlope.energy ν f :=
    fun k ↦ lintegral_mono fun x ↦ pow_le_pow_left' (hslope k x) 2
  have hadm : ∀ k, Energy.LocalSlope.Admissible ν (T k) := fun k ↦
    { locallyLipschitz := (lipschitzWith_clamp (k : ℝ)).locallyLipschitz.comp hf
      memLp_two := MemLp.of_bound (hTc k).aestronglyMeasurable (k : ℝ)
        (ae_of_all _ fun x ↦ by
          rw [Real.norm_eq_abs]; exact abs_clamp_le_self k.cast_nonneg _)
      finite_energy := ne_top_of_le_ne_top he (henergy k) }
  set M : ENNReal := (C : ENNReal) * Energy.LocalSlope.energy ν f
  have hM : M ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top he
  have hvar : ∀ k, evariance (T k) μ ≤ M := fun k ↦
    (hC (T k) (hadm k)).trans (mul_le_mul_right (henergy k) _)
  -- a sublevel set of `|f|` of mass more than one half
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (2⁻¹ : ENNReal) < μ {x | |f x| ≤ (a : ℝ)} := by
    have hmono : Monotone fun a : ℕ ↦ {x | |f x| ≤ (a : ℝ)} := fun a b hab x hx ↦
      show |f x| ≤ (b : ℝ) from le_trans hx (by exact_mod_cast hab)
    have hU : ⋃ a : ℕ, {x | |f x| ≤ (a : ℝ)} = Set.univ := by
      refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ?_
      obtain ⟨a, ha⟩ := exists_nat_ge |f x|
      exact ⟨a, ha⟩
    have ht := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hU, measure_univ] at ht
    exact ((tendsto_order.1 ht).1 _ ENNReal.one_half_lt_one).exists
  set A := {x | |f x| ≤ (a : ℝ)}
  have hAm : MeasurableSet A := measurableSet_le hfc.abs.measurable measurable_const
  set K : ENNReal := 2 * M + 2 * ENNReal.ofReal ((a : ℝ) ^ 2) with hK
  -- the means are bounded
  have hmean : ∀ k, ENNReal.ofReal ((μ[T k]) ^ 2) ≤ 2 * K := by
    intro k
    set m := μ[T k]
    have hpt : ∀ x, A.indicator (fun _ ↦ ENNReal.ofReal (m ^ 2)) x ≤
        2 * ENNReal.ofReal ((T k x - m) ^ 2) + 2 * ENNReal.ofReal ((a : ℝ) ^ 2) := by
      intro x
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx, ← ofReal_two_mul_add_two_mul (sq_nonneg _) (sq_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : |T k x| ≤ (a : ℝ) := (abs_clamp_le k.cast_nonneg _).trans hx
        have h2 : T k x ^ 2 ≤ (a : ℝ) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        nlinarith [sq_nonneg (2 * T k x - m)]
      · rw [Set.indicator_of_notMem hx]
        exact zero_le
    have hint := lintegral_mono (μ := μ) hpt
    rw [lintegral_indicator_const hAm, lintegral_add_right _ measurable_const,
      lintegral_const_mul _ ((hTc k).measurable.sub_const m |>.pow_const 2).ennreal_ofReal,
      lintegral_const, measure_univ, mul_one, ← evariance_eq_lintegral_ofReal] at hint
    have hle : ENNReal.ofReal (m ^ 2) * 2⁻¹ ≤ K :=
      calc ENNReal.ofReal (m ^ 2) * 2⁻¹ ≤ ENNReal.ofReal (m ^ 2) * μ A := by gcongr
        _ ≤ _ := hint
        _ ≤ K := add_le_add_left (mul_le_mul_right (hvar k) 2) _
    calc ENNReal.ofReal (m ^ 2) = ENNReal.ofReal (m ^ 2) * 2⁻¹ * 2 := by
          rw [mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]
      _ ≤ K * 2 := mul_le_mul_left hle 2
      _ = 2 * K := mul_comm _ _
  -- uniformly bounded second moments
  set B : ENNReal := 2 * M + 2 * (2 * K) with hB
  have hBne : B ≠ ⊤ := by
    simp only [hB, hK]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top hM,
      ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top hM,
          ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top⟩))⟩
  have hsecond : ∀ k, ∫⁻ x, ENNReal.ofReal (T k x ^ 2) ∂μ ≤ B := by
    intro k
    set m := μ[T k]
    have hpt : ∀ x, ENNReal.ofReal (T k x ^ 2) ≤
        2 * ENNReal.ofReal ((T k x - m) ^ 2) + 2 * ENNReal.ofReal (m ^ 2) := by
      intro x
      rw [← ofReal_two_mul_add_two_mul (sq_nonneg _) (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (T k x - 2 * m)])
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_add_right _ measurable_const,
      lintegral_const_mul _ ((hTc k).measurable.sub_const m |>.pow_const 2).ennreal_ofReal,
      lintegral_const, measure_univ, mul_one, ← evariance_eq_lintegral_ofReal]
    exact add_le_add (mul_le_mul_right (hvar k) 2) (mul_le_mul_right (hmean k) 2)
  -- Fatou
  have hlim : ∀ x, liminf (fun k ↦ ENNReal.ofReal (T k x ^ 2)) atTop =
      ENNReal.ofReal (f x ^ 2) := by
    intro x
    refine (tendsto_const_nhds.congr' ?_).liminf_eq
    filter_upwards [eventually_ge_atTop ⌈|f x|⌉₊] with k hk
    have hk' : |f x| ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
    simp only [hT, clamp_eq hk']
  have hfatou := lintegral_liminf_le (μ := μ) (u := atTop)
    (fun k ↦ ((hTc k).measurable.pow_const 2).ennreal_ofReal)
  simp only [hlim] at hfatou
  have hfin : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ < ⊤ :=
    (hfatou.trans (liminf_le_of_frequently_le' (Frequently.of_forall hsecond))).trans_lt
      hBne.lt_top
  exact (memLp_two_iff_integrable_sq hfc.aestronglyMeasurable).2
    ⟨(hfc.pow 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x ↦ sq_nonneg (f x))).2 hfin⟩

end Truncation

end FunctionalInequalities.Poincare.LocalSlope
