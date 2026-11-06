/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Probability.TotalVariation


/-!
# Couplings and Poisson laws in total variation

General total-variation facts used by the source (inventory item B15, source lines 1693–1696,
2115–2120 and 2392–2398), all in the paper's probability convention `paperTVDist`:

* the coupling bound `d_TV(L(X), L(Y)) ≤ P(X ≠ Y)` and its monotone form
  `d_TV(L(X), L(Y)) ≤ E[Y - X]` for `ℕ`-valued `X ≤ Y`;
* `d_TV(Po(a), Po(b)) ≤ 1 - exp (-|a - b|) ≤ |a - b|`;
* continuity of the Poisson law in its parameter, and the replacement of the Poisson
  parameter along a sequence when the parameters are asymptotically equal;
* the Poisson zero-mass bound `|P(N = 0) - exp (-a)| ≤ d_TV(L(N), Po(a))`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace PoissonDeclumping

section Coupling

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Coupling bound.** Two random variables on the same probability space have laws whose
normalized total variation distance is at most the probability that they differ. The
disagreement event need not be measurable; `Measure.real` is then its outer measure. -/
theorem paperTVDist_map_le_measureReal_ne (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → α} (hX : Measurable X) (hY : Measurable Y) :
    paperTVDist (P.map X) (P.map Y) ≤ P.real {ω | X ω ≠ Y ω} := by
  rw [paperTVDist_le_iff]
  intro s hs
  rw [map_measureReal_apply hX hs, map_measureReal_apply hY hs]
  have h1 : X ⁻¹' s ⊆ Y ⁻¹' s ∪ {ω | X ω ≠ Y ω} := by
    intro ω hω
    by_cases h : X ω = Y ω
    · left
      simp only [mem_preimage] at hω ⊢
      rwa [← h]
    · exact Or.inr h
  have h2 : Y ⁻¹' s ⊆ X ⁻¹' s ∪ {ω | X ω ≠ Y ω} := by
    intro ω hω
    by_cases h : X ω = Y ω
    · left
      simp only [mem_preimage] at hω ⊢
      rwa [h]
    · exact Or.inr h
  have e1 := (measureReal_mono (μ := P) h1).trans (measureReal_union_le _ _)
  have e2 := (measureReal_mono (μ := P) h2).trans (measureReal_union_le _ _)
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- **Monotone coupling bound.** If `X ≤ Y` almost surely are `ℕ`-valued random variables and
`Y - X` is integrable, then `d_TV(L(X), L(Y)) ≤ E[Y - X]`. This is the mechanism used for the
truncation in Lemma `lem:truncate`(i), source lines 1692–1693. -/
theorem paperTVDist_map_le_integral_sub (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℕ} (hX : Measurable X) (hY : Measurable Y) (hXY : ∀ᵐ ω ∂P, X ω ≤ Y ω)
    (hint : Integrable (fun ω => (Y ω : ℝ) - X ω) P) :
    paperTVDist (P.map X) (P.map Y) ≤ ∫ ω, ((Y ω : ℝ) - X ω) ∂P := by
  refine (paperTVDist_map_le_measureReal_ne P hX hY).trans ?_
  have hmeas : MeasurableSet {ω | X ω ≠ Y ω} :=
    (measurableSet_eq_fun hX hY).compl
  rw [← integral_indicator_one hmeas]
  refine integral_mono_ae ((integrable_const (1 : ℝ)).indicator hmeas) hint ?_
  filter_upwards [hXY] with ω hω
  by_cases h : X ω = Y ω
  · rw [indicator_of_notMem (by simpa using h)]
    simp [h]
  · rw [indicator_of_mem (by simpa using h)]
    have : X ω + 1 ≤ Y ω := by omega
    have : ((X ω : ℝ) + 1) ≤ Y ω := by exact_mod_cast this
    simp only [Pi.one_apply]
    linarith

end Coupling

section Poisson

/-- The Poisson law with rate zero is the Dirac mass at zero. -/
theorem poissonMeasure_zero : poissonMeasure 0 = Measure.dirac 0 := by
  rw [Measure.ext_iff_singleton]
  intro a
  rcases a with _ | a
  · simp [poissonMeasure_singleton]
  · simp [poissonMeasure_singleton]

/-- `d_TV(Po(a), Po(b)) ≤ 1 - exp (-(b - a))` for `a ≤ b`, via the coupling `X` versus
`X + Y` with independent `X ~ Po(a)` and `Y ~ Po(b - a)`. -/
theorem paperTVDist_poissonMeasure_le_one_sub_exp_of_le {a b : ℝ≥0} (hab : a ≤ b) :
    paperTVDist (poissonMeasure a) (poissonMeasure b) ≤ 1 - Real.exp (-((b : ℝ) - a)) := by
  set P : Measure (ℕ × ℕ) := (poissonMeasure a).prod (poissonMeasure (b - a)) with hP
  have hX : P.map Prod.fst = poissonMeasure a := by simp [hP]
  have hY : P.map (fun x : ℕ × ℕ => x.1 + x.2) = poissonMeasure b := by
    have h := poissonMeasure_conv_poissonMeasure a (b - a)
    rw [add_tsub_cancel_of_le hab] at h
    rw [← h]
    rfl
  have hset : {x : ℕ × ℕ | x.1 ≠ x.1 + x.2} = univ ×ˢ {0}ᶜ := by
    ext x
    simp only [ne_eq, mem_prod, mem_univ, mem_compl_iff, mem_singleton_iff, true_and]
    change ¬x.1 = x.1 + x.2 ↔ ¬x.2 = 0
    omega
  have hcoup := paperTVDist_map_le_measureReal_ne P (X := Prod.fst)
    (Y := fun x : ℕ × ℕ => x.1 + x.2) measurable_fst (by fun_prop)
  rw [hX, hY, hset, measureReal_prod_prod, probReal_univ, one_mul,
    probReal_compl_eq_one_sub (measurableSet_singleton 0), poissonMeasure_real_singleton,
    NNReal.coe_sub hab] at hcoup
  simpa using hcoup

/-- `d_TV(Po(a), Po(b)) ≤ 1 - exp (-|a - b|)`. -/
theorem paperTVDist_poissonMeasure_le_one_sub_exp (a b : ℝ≥0) :
    paperTVDist (poissonMeasure a) (poissonMeasure b) ≤ 1 - Real.exp (-|(a : ℝ) - b|) := by
  rcases le_total a b with hab | hab
  · have h : |(a : ℝ) - b| = b - a := by
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hab))]
    rw [h]
    exact paperTVDist_poissonMeasure_le_one_sub_exp_of_le hab
  · have h : |(a : ℝ) - b| = a - b := abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hab))
    rw [h, paperTVDist_comm]
    exact paperTVDist_poissonMeasure_le_one_sub_exp_of_le hab

/-- **Poisson laws in total variation.** `d_TV(Po(a), Po(b)) ≤ |a - b|`, as used at source
lines 1695 and 2115. -/
theorem paperTVDist_poissonMeasure_le_abs_sub (a b : ℝ≥0) :
    paperTVDist (poissonMeasure a) (poissonMeasure b) ≤ |(a : ℝ) - b| := by
  refine (paperTVDist_poissonMeasure_le_one_sub_exp a b).trans ?_
  have := Real.add_one_le_exp (-|(a : ℝ) - b|)
  linarith

/-- If the Poisson parameters are asymptotically equal, the Poisson laws merge in total
variation. -/
theorem tendsto_paperTVDist_poissonMeasure {ι : Type*} {l : Filter ι} {a b : ι → ℝ≥0}
    (h : Tendsto (fun i => (a i : ℝ) - b i) l (𝓝 0)) :
    Tendsto (fun i => paperTVDist (poissonMeasure (a i)) (poissonMeasure (b i))) l (𝓝 0) := by
  have habs : Tendsto (fun i => |(a i : ℝ) - b i|) l (𝓝 0) := by
    simpa using h.abs
  exact squeeze_zero (fun _ => paperTVDist_nonneg _ _)
    (fun i => paperTVDist_poissonMeasure_le_abs_sub (a i) (b i)) habs

/-- Convergence of the Poisson parameter implies convergence of the Poisson laws in total
variation. -/
theorem tendsto_paperTVDist_poissonMeasure_of_tendsto {ι : Type*} {l : Filter ι}
    {a : ι → ℝ≥0} {b : ℝ≥0} (h : Tendsto a l (𝓝 b)) :
    Tendsto (fun i => paperTVDist (poissonMeasure (a i)) (poissonMeasure b)) l (𝓝 0) := by
  apply tendsto_paperTVDist_poissonMeasure (b := fun _ => b)
  have h' : Tendsto (fun i => (a i : ℝ)) l (𝓝 (b : ℝ)) := NNReal.tendsto_coe.mpr h
  simpa using h'.sub_const (b : ℝ)

/-- Continuity of the Poisson law in its parameter, for normalized total variation. -/
theorem tendsto_paperTVDist_poissonMeasure_nhds (b : ℝ≥0) :
    Tendsto (fun a => paperTVDist (poissonMeasure a) (poissonMeasure b)) (𝓝 b) (𝓝 0) :=
  tendsto_paperTVDist_poissonMeasure_of_tendsto (a := id) tendsto_id

/-- Triangle inequality along a filter: total-variation convergence passes through an
intermediate family of finite measures. -/
theorem tendsto_paperTVDist_trans {β ι : Type*} [MeasurableSpace β] {l : Filter ι}
    {μ ν ξ : ι → Measure β} [∀ i, IsFiniteMeasure (ν i)]
    (h₁ : Tendsto (fun i => paperTVDist (μ i) (ν i)) l (𝓝 0))
    (h₂ : Tendsto (fun i => paperTVDist (ν i) (ξ i)) l (𝓝 0)) :
    Tendsto (fun i => paperTVDist (μ i) (ξ i)) l (𝓝 0) := by
  have h := h₁.add h₂
  rw [add_zero] at h
  exact squeeze_zero (fun _ => paperTVDist_nonneg _ _)
    (fun i => paperTVDist_triangle (μ i) (ν i) (ξ i)) h

/-- Replacing the Poisson parameter: if `d_TV(L_n, Po(a_n)) → 0` and `a_n - b_n → 0`, then
`d_TV(L_n, Po(b_n)) → 0` (source lines 2112–2119). -/
theorem tendsto_paperTVDist_poissonMeasure_congr {ι : Type*} {l : Filter ι}
    (L : ι → Measure ℕ) {a b : ι → ℝ≥0}
    (hL : Tendsto (fun i => paperTVDist (L i) (poissonMeasure (a i))) l (𝓝 0))
    (hab : Tendsto (fun i => (a i : ℝ) - b i) l (𝓝 0)) :
    Tendsto (fun i => paperTVDist (L i) (poissonMeasure (b i))) l (𝓝 0) :=
  tendsto_paperTVDist_trans hL (tendsto_paperTVDist_poissonMeasure hab)

/-- The Poisson zero mass is controlled by total variation:
`|μ{0} - exp (-a)| ≤ d_TV(μ, Po(a))` (source lines 2392–2397). -/
theorem abs_measureReal_zero_sub_exp_le_paperTVDist (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (a : ℝ≥0) : |μ.real {0} - Real.exp (-(a : ℝ))| ≤ paperTVDist μ (poissonMeasure a) := by
  have h := abs_sub_measureReal_le_paperTVDist μ (poissonMeasure a) (measurableSet_singleton 0)
  simpa [poissonMeasure_real_singleton] using h

end Poisson

end PoissonDeclumping
