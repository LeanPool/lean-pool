/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-27 by the KLS formalization project: update deprecated aliases and
-- proof-local bindings for warning-free Lean v4.33.0 builds; see vendor/port.patch.

-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0, with
-- source adaptations (deprecated names, proof-context visibility) listed in vendor/port.patch.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoProcessVersion
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoQuadVarSum
public import LeanPool.KLS.LevyStochCalc.Brownian.AugmentedFiltration

/-!
# Existence of a continuous adapted version of an Itô process

The Itô integral has an a.e.-continuous modification by Kolmogorov–Chentsov. Zeroing its paths
on a null set makes them continuous everywhere, and the resulting process stays adapted exactly
when the filtration contains the null sets — the usual conditions. Adding a measurable initial
value and the drift's (Lipschitz, hence continuous) window integral gives an `IsItoVersion`.

## Main statements

* `LevyStochCalc.Brownian.Ito.measurable_of_ae_eq_of_null_mem` — a σ-algebra of the filtration
  containing the null sets does not distinguish a.e.-equal functions.
* `LevyStochCalc.Brownian.Ito.dyadicApprox` — the dyadic approximation from below, whose values
  lie in a countable set.
* `LevyStochCalc.Brownian.Ito.exists_continuousAdapted_modification` — the Itô integral has a
  continuous adapted modification.
* `LevyStochCalc.Brownian.Ito.exists_isItoVersion` — a continuous adapted version exists.
* `LevyStochCalc.Brownian.Ito.exists_isItoVersion_aug` — the same over the augmented
  filtration, with no side conditions.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- If a sub-σ-algebra of a filtration contains every `μ`-null set, a function a.e.-equal to a
measurable function for it is itself measurable for it. -/
theorem measurable_of_ae_eq_of_null_mem {μ : Measure Ω}
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (u : ℝ)
    (hnull : ∀ s : Set Ω, (∃ N, MeasurableSet N ∧ μ N = 0 ∧ s ⊆ N) → MeasurableSet[ℱ u] s)
    {f g : Ω → ℝ} (hg : Measurable[ℱ u] g) (hfg : f =ᵐ[μ] g) : Measurable[ℱ u] f := by
  obtain ⟨N, hNsub, hNmeas, hNzero⟩ :=
    MeasureTheory.exists_measurable_superset_of_null (MeasureTheory.ae_iff.mp hfg)
  have hNm : MeasurableSet[ℱ u] N := hnull N ⟨N, hNmeas, hNzero, Set.Subset.rfl⟩
  intro A hA
  have hset : f ⁻¹' A = (g ⁻¹' A \ N) ∪ (f ⁻¹' A ∩ N) := by
    ext ω
    by_cases hω : ω ∈ N
    · simp [hω]
    · have hfgω : f ω = g ω := by
        by_contra hne
        exact hω (hNsub hne)
      simp [hω, hfgω]
  rw [hset]
  exact MeasurableSet.union (MeasurableSet.diff (hg hA) hNm)
    (hnull _ ⟨N, hNmeas, hNzero, Set.inter_subset_right⟩)

/-- A measurable null set outside which an almost-everywhere property holds. -/
theorem exists_measurable_null_of_ae {μ : Measure Ω} {p : Ω → Prop} (h : ∀ᵐ ω ∂μ, p ω) :
    ∃ N : Set Ω, MeasurableSet N ∧ μ N = 0 ∧ ∀ ω, ω ∉ N → p ω := by
  obtain ⟨N, hsub, hmeas, hzero⟩ :=
    MeasureTheory.exists_measurable_superset_of_null (MeasureTheory.ae_iff.mp h)
  exact ⟨N, hmeas, hzero, fun ω hω => by_contra fun hp => hω (hsub hp)⟩

/-- The `n`-th dyadic approximation from below of a nonnegative real. -/
noncomputable def dyadicApprox (n : ℕ) (u : ℝ) : ℝ := (⌊u * 2 ^ n⌋₊ : ℝ) / 2 ^ n

theorem dyadicApprox_nonneg (n : ℕ) (u : ℝ) : 0 ≤ dyadicApprox n u := by
  unfold dyadicApprox
  positivity

theorem dyadicApprox_le {u : ℝ} (hu : 0 ≤ u) (n : ℕ) : dyadicApprox n u ≤ u := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [dyadicApprox, div_le_iff₀ h2]
  exact Nat.floor_le (by positivity)

theorem sub_dyadicApprox_lt (u : ℝ) (n : ℕ) : u - dyadicApprox n u < 1 / 2 ^ n := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hfl := Nat.lt_floor_add_one (u * 2 ^ n)
  rw [dyadicApprox, sub_lt_iff_lt_add,
    show (1 : ℝ) / 2 ^ n + (⌊u * 2 ^ n⌋₊ : ℝ) / 2 ^ n
      = ((⌊u * 2 ^ n⌋₊ : ℝ) + 1) / 2 ^ n by ring, lt_div_iff₀ h2]
  linarith

theorem tendsto_dyadicApprox {u : ℝ} (hu : 0 ≤ u) :
    Filter.Tendsto (fun n : ℕ => dyadicApprox n u) Filter.atTop (nhds u) := by
  have hlo : ∀ n : ℕ, u - 1 / 2 ^ n ≤ dyadicApprox n u := fun n => by
    have := sub_dyadicApprox_lt u n
    linarith
  have hhi : ∀ n : ℕ, dyadicApprox n u ≤ u := dyadicApprox_le hu
  have hpow : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) Filter.atTop (nhds 0) := by
    simpa using tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)
  have hsub : Filter.Tendsto (fun n : ℕ => u - 1 / 2 ^ n) Filter.atTop (nhds u) := by
    simpa using (tendsto_const_nhds (x := u) (f := Filter.atTop (α := ℕ))).sub hpow
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hsub tendsto_const_nhds hlo hhi

theorem dyadicApprox_eq (n : ℕ) (u : ℝ) :
    dyadicApprox n u = ((⌊u * 2 ^ n⌋₊ : ℕ) : ℝ) / 2 ^ n := rfl


section Exists

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hℱ hC0 hCH in
/-- **A continuous adapted modification of the Itô integral exists** when the filtration is
constant before time `0` and contains the measurable null sets. -/
theorem exists_continuousAdapted_modification
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) :
    ∃ Y : ℝ → Ω → ℝ, (∀ ω : Ω, Continuous fun t => Y t ω)
      ∧ (∀ u : ℝ, Measurable[ℱ u] (Y u))
      ∧ ∀ t : ℝ, 0 ≤ t → Y t =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ H hm hp hq t := by
  classical
  obtain ⟨Y, hYcont, hYmod⟩ :=
    exists_continuous_modification_stochasticIntegralBrownian W ℱ hℱ H hm hp hq hC0 hCH
  obtain ⟨N₁, hN₁meas, hN₁zero, hN₁cont⟩ := exists_measurable_null_of_ae hYcont
  -- the modification agrees with the integral at every nonnegative dyadic time
  have hdnn : ∀ p : ℕ × ℕ, (0 : ℝ) ≤ ((p.1 : ℝ) / 2 ^ p.2) := fun p => by positivity
  choose Nd hNdmeas hNdzero hNdout using fun p : ℕ × ℕ =>
    exists_measurable_null_of_ae (hYmod ((p.1 : ℝ) / 2 ^ p.2) (hdnn p))
  set N : Set Ω := N₁ ∪ ⋃ p : ℕ × ℕ, Nd p with hNdef
  have hNmeas : MeasurableSet N :=
    hN₁meas.union (MeasurableSet.iUnion fun p => hNdmeas p)
  have hNzero : P N = 0 :=
    MeasureTheory.measure_union_null hN₁zero
      (MeasureTheory.measure_iUnion_null fun p => hNdzero p)
  have hNcont : ∀ ω : Ω, ω ∉ N → Continuous fun t => Y t ω := fun ω hω =>
    hN₁cont ω fun h => hω (Or.inl h)
  have hNdyad : ∀ (p : ℕ × ℕ) (ω : Ω), ω ∉ N →
      Y ((p.1 : ℝ) / 2 ^ p.2) ω
        = stochasticIntegralBrownian W ℱ hℱ H hm hp hq ((p.1 : ℝ) / 2 ^ p.2) ω :=
    fun p ω hω => hNdout p ω fun h => hω (Or.inr (Set.mem_iUnion.mpr ⟨p, h⟩))
  -- `ℱ t` contains `ℱ 0` at every time, hence contains `N`
  have hle0 : ∀ t : ℝ, ℱ 0 ≤ ℱ t := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · exact ℱ.mono ht
    · exact hℱ0 t ht.le
  have hNm : ∀ t : ℝ, MeasurableSet[ℱ t] N := fun t =>
    hle0 t N (hnull N hNmeas hNzero)
  -- the truncated modification is adapted, as a pointwise limit along dyadic times
  have hYind : ∀ u : ℝ, 0 ≤ u →
      Measurable[ℱ u] fun ω => if ω ∈ N then (0 : ℝ) else Y u ω := by
    intro u hu
    have hstep : ∀ n : ℕ, Measurable[ℱ u] fun ω => if ω ∈ N then (0 : ℝ)
        else stochasticIntegralBrownian W ℱ hℱ H hm hp hq (dyadicApprox n u) ω := by
      intro n
      have hSI : Measurable[ℱ u]
          (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (dyadicApprox n u)) := by
        have h1 := (stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq
          (dyadicApprox n u)).measurable
        exact fun A hA => ℱ.mono (dyadicApprox_le hu n) _ (h1 hA)
      exact Measurable.ite (hNm u) measurable_const hSI
    have hlim : Filter.Tendsto (fun (n : ℕ) (ω : Ω) => if ω ∈ N then (0 : ℝ)
          else stochasticIntegralBrownian W ℱ hℱ H hm hp hq (dyadicApprox n u) ω)
        Filter.atTop (nhds fun ω => if ω ∈ N then (0 : ℝ) else Y u ω) := by
      rw [tendsto_pi_nhds]
      intro ω
      by_cases hω : ω ∈ N
      · simp only [hω, ite_true]
        exact tendsto_const_nhds
      · simp only [hω, ite_false]
        have heq : (fun n : ℕ => stochasticIntegralBrownian W ℱ hℱ H hm hp hq
            (dyadicApprox n u) ω) = fun n => Y (dyadicApprox n u) ω := by
          funext n
          exact (hNdyad (⌊u * 2 ^ n⌋₊, n) ω hω).symm
        rw [heq]
        exact Filter.Tendsto.comp ((hNcont ω hω).continuousAt (x := u))
          (tendsto_dyadicApprox hu)
    let : MeasurableSpace Ω := ℱ u
    exact measurable_of_tendsto_metrizable hstep hlim
  refine ⟨fun t ω => if ω ∈ N then 0 else Y (max t 0) ω, ?_, ?_, ?_⟩
  · intro ω
    by_cases hω : ω ∈ N
    · simpa [hω] using continuous_const
    · simp only [hω, ite_false]
      exact (hNcont ω hω).comp (continuous_id.max continuous_const)
  · intro u
    rcases le_or_gt 0 u with hu | hu
    · simp only [max_eq_left hu]
      exact hYind u hu
    · simp only [max_eq_right hu.le]
      exact fun A hA => hle0 u _ (hYind 0 le_rfl hA)
  · intro t ht
    filter_upwards [hYmod t ht,
      MeasureTheory.compl_mem_ae_iff.mpr hNzero] with ω hω hωN
    rw [ite_eq_right hωN, max_eq_left ht]
    exact hω

include hℱ hC0 hCH in
/-- **A continuous adapted version of an Itô process exists** when the filtration is constant
before time `0` and contains the measurable null sets. -/
theorem exists_isItoVersion
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {X₀ : Ω → ℝ} (hX₀ : Measurable[ℱ 0] X₀)
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    (hbp : Probability.ProgressivelyMeasurable ℱ bdrift)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B) :
    ∃ X : ℝ → Ω → ℝ, IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X := by
  obtain ⟨Y, hYcont, hYadapt, hYmod⟩ :=
    exists_continuousAdapted_modification W ℱ hℱ H hm hp hq hC0 hCH hℱ0 hnull
  have hle0 : ∀ t : ℝ, ℱ 0 ≤ ℱ t := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · exact ℱ.mono ht
    · exact hℱ0 t ht.le
  refine ⟨fun t ω => X₀ ω + (∫ s in Set.Icc (0 : ℝ) t, bdrift ω s ∂volume) + Y t ω, ?_, ?_, ?_⟩
  · exact fun ω => (continuous_const.add
      (continuous_setIntegral_Icc (Measurable.of_uncurry_left hbm) hB0 (hB ω))).add (hYcont ω)
  · intro t
    refine Measurable.stronglyMeasurable (Measurable.add (Measurable.add ?_ ?_) (hYadapt t))
    · exact fun A hA => hle0 t _ (hX₀ hA)
    · exact ((hbp.stronglyMeasurable_setIntegral measurableSet_Icc
        Set.Icc_subset_Iic_self volume).mono le_rfl).measurable
  · intro t ht
    filter_upwards [hYmod t ht] with ω hω
    rw [hω]
    rfl

include hC0 hCH in
/-- **A continuous adapted version exists over the augmented filtration**, with no side
conditions on the filtration: freezing `ℱ` before time `0` and augmenting by the null sets
gives a Brownian filtration satisfying the usual conditions. -/
theorem exists_isItoVersion_aug
    (Hp : Probability.ProgressivelyMeasurable (augFiltration ℱ P) H)
    (Hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X₀ : Ω → ℝ} (hX₀ : Measurable[ℱ 0] X₀)
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    (hbp : Probability.ProgressivelyMeasurable (augFiltration ℱ P) bdrift)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B) :
    ∃ X : ℝ → Ω → ℝ, IsItoVersion W (augFiltration ℱ P)
      (isBrownianFiltration_augFiltration hℱ) H hm Hp Hq X₀ bdrift X :=
  exists_isItoVersion W (augFiltration ℱ P) (isBrownianFiltration_augFiltration hℱ) H hm Hp Hq
    hC0 hCH (fun _ ht => le_of_eq (augFiltration_of_nonpos ℱ P ht).symm)
    (fun _ hs h0 => measurableSet_augFiltration_of_null ℱ P hs h0)
    (fun _ hA => le_augFiltration ℱ P 0 _ (hX₀ hA)) bdrift hbm hbp hB0 hB


end Exists

end LevyStochCalc.Brownian.Ito
