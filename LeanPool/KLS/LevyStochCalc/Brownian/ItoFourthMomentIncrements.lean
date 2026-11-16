/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0, with
-- source adaptations (deprecated names, proof-context visibility) listed in vendor/port.patch.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoAlgebra

/-!
# Moments of a Brownian increment and the partial sums of the elementary integral

The moments of a centred real Gaussian and of a Brownian increment: they scale with the standard
deviation, the odd ones vanish, and a random variable measurable before the increment factors out
of the integral against any power of it. On top of this the elementary integral of a simple
integrand is presented as the partial sums `SimplePredictable.partialSum` of its summands, with
their measurability, adaptedness and `Lᵖ` membership, and the variance budget
`SimplePredictable.varClock c k = ∑_{j < k} c_j² (τ_{j+1} − τ_j)` of a per-tile coefficient
bound `c`.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- The fourth moment of the standard real Gaussian distribution. -/
noncomputable def gaussianFourthMoment : ℝ :=
  ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 1)

theorem gaussianFourthMoment_nonneg : 0 ≤ gaussianFourthMoment :=
  integral_nonneg fun x => by positivity

/-- Every power of the identity is integrable for a real Gaussian distribution. -/
theorem integrable_pow_gaussianReal (m : ℕ) (hm : m ≠ 0) (μ' : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ m) (gaussianReal μ' v) := by
  have h : MemLp (id : ℝ → ℝ) (m : ℝ≥0∞) (gaussianReal μ' v) :=
    memLp_id_gaussianReal' _ (by simp)
  refine (h.integrable_norm_pow hm).mono (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp

/-- Powers of a centred real Gaussian scale with the standard deviation. -/
theorem integral_pow_gaussianReal_zero (v : ℝ≥0) (m : ℕ) :
    ∫ x : ℝ, x ^ m ∂(gaussianReal 0 v)
      = Real.sqrt v ^ m * ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1) := by
  have hsq : NNReal.mk (Real.sqrt v ^ 2) (sq_nonneg _) * 1 = v := by
    rw [mul_one]
    exact NNReal.eq (by simp [Real.sq_sqrt v.coe_nonneg])
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt v * x) = gaussianReal 0 v := by
    have h := gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := 1) (Real.sqrt v)
    rw [mul_zero, hsq] at h
    exact h
  conv_lhs => rw [← hmap]
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow]
  rw [integral_const_mul]

/-- The odd moments of the standard real Gaussian vanish. -/
theorem integral_pow_gaussianReal_odd (m : ℕ) (hm : Odd m) :
    ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1) = 0 := by
  have hmap : (gaussianReal (0 : ℝ) 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    simpa using gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)
  have h1 : ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1)
      = ∫ x : ℝ, (-x) ^ m ∂(gaussianReal 0 1) := by
    conv_lhs => rw [← hmap]
    rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [hm.neg_pow] at h1
  rw [integral_neg] at h1
  linarith

section Increments

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)

/-- The moments of a Brownian increment scale with the square root of its length. -/
theorem integral_increment_pow {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (m : ℕ) :
    ∫ ω, (W.W b ω - W.W a ω) ^ m ∂P
      = Real.sqrt (b - a) ^ m * ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1) := by
  have hmeas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  rw [← integral_map hmeas.aemeasurable
      (f := fun x : ℝ => x ^ m) (by fun_prop),
    W.increment_gaussian ha hab]
  exact integral_pow_gaussianReal_zero _ m

/-- Odd moments of a Brownian increment vanish. -/
theorem integral_increment_pow_odd {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {m : ℕ} (hm : Odd m) :
    ∫ ω, (W.W b ω - W.W a ω) ^ m ∂P = 0 := by
  rw [integral_increment_pow W ha hab m, integral_pow_gaussianReal_odd m hm, mul_zero]

/-- The second moment of a Brownian increment is its length. -/
theorem integral_increment_sq {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (W.W b ω - W.W a ω) ^ 2 ∂P = b - a := by
  rw [integral_increment_pow W ha hab 2,
    LevyStochCalc.Brownian.Martingale.gaussianReal_second_moment 1]
  rw [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ b - a)]
  norm_num

/-- The fourth moment of a Brownian increment is the square of its length, up to the fourth
moment of the standard Gaussian. -/
theorem integral_increment_pow_four {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (W.W b ω - W.W a ω) ^ 4 ∂P = (b - a) ^ 2 * gaussianFourthMoment := by
  rw [integral_increment_pow W ha hab 4]
  congr 1
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ b - a)]

/-- A random variable measurable before `a` is independent of every power of the increment
over `(a, b]`. -/
theorem integral_mul_increment_pow (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsBrownianFiltration W ℱ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {Y : Ω → ℝ}
    (hY : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) Y) (hYm : Measurable Y) (m : ℕ) :
    ∫ ω, Y ω * (W.W b ω - W.W a ω) ^ m ∂P
      = (∫ ω, Y ω ∂P) * ∫ ω, (W.W b ω - W.W a ω) ^ m ∂P := by
  have hΔ : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  have hindepσ := hℱ.indep ha hab
  have hYcomap : MeasurableSpace.comap Y inferInstance ≤ ℱ a := hY.measurable.comap_le
  have hIF : ProbabilityTheory.IndepFun Y (fun ω => W.W b ω - W.W a ω) P := by
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    rw [ProbabilityTheory.Indep_iff] at hindepσ
    exact hindepσ u v (hYcomap u hu) hv
  have hIF' : ProbabilityTheory.IndepFun Y (fun ω => (W.W b ω - W.W a ω) ^ m) P :=
    hIF.comp measurable_id (measurable_id.pow_const m)
  exact hIF'.integral_mul_eq_mul_integral hYm.aestronglyMeasurable
    (hΔ.pow_const m).aestronglyMeasurable

/-- A Brownian increment has moments of every order. -/
theorem memLp_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (fun ω => W.W b ω - W.W a ω) p P := by
  have hmeas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  have h := (memLp_map_measure_iff (g := (id : ℝ → ℝ)) (μ := P)
    (f := fun ω => W.W b ω - W.W a ω) (p := p)
    (by fun_prop) hmeas.aemeasurable).1
  rw [W.increment_gaussian ha hab] at h
  exact h (memLp_id_gaussianReal' p hp)

/-- A bounded random variable times a Brownian increment has moments of every order. -/
theorem memLp_mul_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (p : ℝ≥0∞) (hp : p ≠ ⊤)
    {Y : Ω → ℝ} (hYm : Measurable Y) {C : ℝ} (hC : ∀ ω, |Y ω| ≤ C) :
    MemLp (fun ω => Y ω * (W.W b ω - W.W a ω)) p P := by
  have hmeas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  refine MemLp.mono ((memLp_increment W ha hab p hp).const_mul C)
    (hYm.mul hmeas).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  have hC0 : 0 ≤ C := (abs_nonneg (Y ω)).trans (hC ω)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hC0]
  exact mul_le_mul_of_nonneg_right (hC ω) (abs_nonneg _)

end Increments

namespace SimplePredictable

variable {T : ℝ} (G : SimplePredictable Ω T)
  {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)

/-- The `i`-th summand of the elementary integral, indexed by a natural number. -/
noncomputable def term (i : ℕ) (ω : Ω) : ℝ :=
  if h : i < G.N then
    G.ξ ⟨i, h⟩ ω * (W.W (G.partition (⟨i, h⟩ : Fin G.N).succ) ω
      - W.W (G.partition (⟨i, h⟩ : Fin G.N).castSucc) ω)
  else 0

/-- The partial sums of the elementary integral. -/
noncomputable def partialSum (k : ℕ) (ω : Ω) : ℝ := ∑ i ∈ Finset.range k, G.term W i ω

theorem partialSum_zero (ω : Ω) : G.partialSum W 0 ω = 0 := by simp [partialSum]

theorem partialSum_succ (k : ℕ) (ω : Ω) :
    G.partialSum W (k + 1) ω = G.partialSum W k ω + G.term W k ω :=
  Finset.sum_range_succ _ _

theorem measurable_term (i : ℕ) : Measurable (G.term W i) := by
  unfold term
  split_ifs with h
  · exact (G.ξ_measurable _).mul ((W.measurable_eval _).sub (W.measurable_eval _))
  · exact measurable_const

theorem measurable_partialSum (k : ℕ) : Measurable (G.partialSum W k) :=
  Finset.measurable_sum _ fun i _ => G.measurable_term W i

theorem partialSum_card (ω : Ω) : G.partialSum W G.N ω = simpleIntegral W G T ω := by
  rw [simpleIntegral_eq_sum, partialSum, ← Fin.sum_univ_eq_sum_range
    (fun i => G.term W i ω) G.N]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [term, dite_eq_left i.isLt]

omit [MeasurableSpace Ω] in
/-- A finite sum of processes measurable for a sub-σ-algebra is measurable for it. -/
private theorem stronglyMeasurable_range_sum {m : MeasurableSpace Ω} {n : ℕ} {f : ℕ → Ω → ℝ}
    (h : ∀ i ∈ Finset.range n, @MeasureTheory.StronglyMeasurable Ω ℝ _ m (f i)) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _ m (fun ω => ∑ i ∈ Finset.range n, f i ω) :=
  @Finset.stronglyMeasurable_fun_sum Ω ℝ _ _ _ m _ _ _ h

theorem memLp_term {C : ℝ} (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)
    (p : ℝ≥0∞) (hp : p ≠ ⊤) (i : ℕ) : MemLp (G.term W i) p P := by
  by_cases h : i < G.N
  · have hterm : G.term W i = fun ω => G.ξ ⟨i, h⟩ ω
        * (W.W (G.partition (⟨i, h⟩ : Fin G.N).succ) ω
          - W.W (G.partition (⟨i, h⟩ : Fin G.N).castSucc) ω) := by
      funext ω; rw [term, dite_eq_left h]
    rw [hterm]
    exact memLp_mul_increment W (G.partition_nonneg _)
      (G.partition_strictMono Fin.castSucc_lt_succ) p hp (G.ξ_measurable _) (hC ⟨i, h⟩)
  · have hterm : G.term W i = fun _ => (0 : ℝ) := by funext ω; rw [term, dite_eq_right h]
    rw [hterm]; exact memLp_const 0

theorem memLp_partialSum {C : ℝ} (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)
    (p : ℝ≥0∞) (hp : p ≠ ⊤) (k : ℕ) : MemLp (G.partialSum W k) p P :=
  memLp_finsetSum _ fun i _ => G.memLp_term W hC p hp i

theorem stronglyMeasurable_partialSum (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsBrownianFiltration W ℱ)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    {k : ℕ} (hk : k ≤ G.N) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition ⟨k, by omega⟩)) (G.partialSum W k) := by
  refine stronglyMeasurable_range_sum fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hiN : i < G.N := lt_of_lt_of_le hi hk
  have hterm : G.term W i = fun ω => G.ξ ⟨i, hiN⟩ ω
      * (W.W (G.partition (⟨i, hiN⟩ : Fin G.N).succ) ω
        - W.W (G.partition (⟨i, hiN⟩ : Fin G.N).castSucc) ω) := by
    funext ω; rw [term, dite_eq_left hiN]
  rw [hterm]
  have hle1 : G.partition (⟨i, hiN⟩ : Fin G.N).castSucc
      ≤ G.partition (⟨k, by omega⟩ : Fin (G.N + 1)) :=
    G.partition_strictMono.monotone (by rw [Fin.le_def]; simp [Fin.castSucc]; omega)
  have hle2 : G.partition (⟨i, hiN⟩ : Fin G.N).succ
      ≤ G.partition (⟨k, by omega⟩ : Fin (G.N + 1)) :=
    G.partition_strictMono.monotone (by rw [Fin.le_def]; simp [Fin.succ]; omega)
  exact ((h_adapt ⟨i, hiN⟩).mono (ℱ.mono hle1)).mul
    (((hℱ.measurable _).stronglyMeasurable.mono (ℱ.mono hle2)).sub
      ((hℱ.measurable _).stronglyMeasurable.mono (ℱ.mono hle1)))

/-- The variance budget of the first `k` tiles for a per-tile coefficient bound `c`:
`∑_{j < k} c_j² (τ_{j+1} − τ_j)`. -/
noncomputable def varClock (c : Fin G.N → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, if h : j < G.N then
    c ⟨j, h⟩ ^ 2 * (G.partition (⟨j, h⟩ : Fin G.N).succ
      - G.partition (⟨j, h⟩ : Fin G.N).castSucc) else 0

theorem varClock_zero (c : Fin G.N → ℝ) : G.varClock c 0 = 0 := by simp [varClock]

theorem varClock_succ (c : Fin G.N → ℝ) {k : ℕ} (hk : k < G.N) :
    G.varClock c (k + 1) = G.varClock c k
      + c ⟨k, hk⟩ ^ 2 * (G.partition (⟨k, hk⟩ : Fin G.N).succ
        - G.partition (⟨k, hk⟩ : Fin G.N).castSucc) := by
  unfold varClock
  rw [Finset.sum_range_succ, dite_eq_left hk]

theorem varClock_nonneg (c : Fin G.N → ℝ) (k : ℕ) : 0 ≤ G.varClock c k := by
  unfold varClock
  refine Finset.sum_nonneg fun j _ => ?_
  by_cases h : j < G.N
  · rw [dite_eq_left h]
    exact mul_nonneg (sq_nonneg _)
      (sub_nonneg.mpr (G.partition_strictMono Fin.castSucc_lt_succ).le)
  · rw [dite_eq_right h]

theorem varClock_mono (c : Fin G.N → ℝ) {k l : ℕ} (h : k ≤ l) :
    G.varClock c k ≤ G.varClock c l := by
  unfold varClock
  have hsub : Finset.range k ⊆ Finset.range l := by
    intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => ?_
  by_cases hj : j < G.N
  · rw [dite_eq_left hj]
    exact mul_nonneg (sq_nonneg _)
      (sub_nonneg.mpr (G.partition_strictMono Fin.castSucc_lt_succ).le)
  · rw [dite_eq_right hj]

end SimplePredictable

end LevyStochCalc.Brownian.Ito
