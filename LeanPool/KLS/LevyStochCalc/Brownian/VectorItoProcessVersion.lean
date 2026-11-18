/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.VectorItoProcess

/-!
# Continuous adapted versions of a vector Itô process

The Itô integral is defined time by time, so the vector process `t ↦ X_t` it produces has no path
regularity built in. `IsVectorItoVersion` names a continuous adapted `Fin n → ℝ`-valued process
agreeing with the vector Itô process at each time; such a version has jointly measurable paths, so
it can be composed with a continuous function and fed back into a time integral or an Itô integral.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion` — a continuous adapted version of a vector Itô
  process.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.measurable_uncurry` — its joint measurability.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.progressivelyMeasurable_comp` — a continuous
  function of it is progressively measurable.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.sub_ae` — a coordinate increment splits into a
  drift part and the martingale part.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_sub_le`,
  `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_sq_sub_le` and their norm forms — the
  increment moments carried over from `vectorItoProcess`.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section VectorVersion

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

/-- A continuous adapted `Fin n → ℝ`-valued process agreeing at each nonnegative time with the
vector Itô process `X₀ + ∫ b ds + ∑ₖ ∫ H^{·,k} dWᵏ`. -/
structure IsVectorItoVersion (X₀ : Ω → Fin n → ℝ) (bdrift : Fin n → Ω → ℝ → ℝ)
    (X : ℝ → Ω → Fin n → ℝ) : Prop where
  /-- every path is continuous -/
  continuous_path : ∀ ω : Ω, Continuous fun t => X t ω
  /-- the process is adapted -/
  adapted : ∀ t : ℝ, @MeasureTheory.StronglyMeasurable Ω (Fin n → ℝ) _ (ℱ t) (X t)
  /-- at each nonnegative time it agrees almost surely with the vector Itô process -/
  ae_eq : ∀ t : ℝ, 0 ≤ t → X t =ᵐ[P] vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift t

variable {W ℱ hcoord H hHm hHp hHs} {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ}
  {X : ℝ → Ω → Fin n → ℝ}

/-- A version's time slices are measurable. -/
theorem IsVectorItoVersion.measurable
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) (t : ℝ) :
    Measurable (X t) := ((h.adapted t).mono (ℱ.le t)).measurable

/-- A version's coordinates are measurable. -/
theorem IsVectorItoVersion.measurable_coord
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) (t : ℝ) (m : Fin n) :
    Measurable fun ω => X t ω m := (measurable_pi_apply m).comp (h.measurable t)

/-- A version's paths are jointly measurable in the sample point and the time. -/
theorem IsVectorItoVersion.measurable_uncurry
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) :
    Measurable (Function.uncurry fun ω s => X s ω) := by
  have hjoint : Measurable (Function.uncurry X) :=
    measurable_uncurry_of_continuous_of_measurable h.continuous_path h.measurable
  exact hjoint.comp measurable_swap

/-- A continuous function of a version is progressively measurable. -/
theorem IsVectorItoVersion.progressivelyMeasurable_comp
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) {φ : (Fin n → ℝ) → ℝ}
    (hφ : Continuous φ) : Probability.ProgressivelyMeasurable ℱ fun ω s => φ (X s ω) := by
  refine Probability.ProgressivelyMeasurable.of_isStronglyProgressive ?_
  refine MeasureTheory.StronglyAdapted.isStronglyProgressive_of_continuous
    (fun t => hφ.comp_stronglyMeasurable (h.adapted t)) fun ω => ?_
  exact hφ.comp (h.continuous_path ω)

/-- A measurable function of a version is jointly measurable. -/
theorem IsVectorItoVersion.measurable_uncurry_comp
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) {φ : (Fin n → ℝ) → ℝ}
    (hφ : Measurable φ) : Measurable (Function.uncurry fun ω s => φ (X s ω)) :=
  hφ.comp h.measurable_uncurry

/-- A version agrees with the vector Itô process at every time of a countable family,
simultaneously. -/
theorem IsVectorItoVersion.ae_eq_all
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) (t : ℕ → ℝ)
    (ht : ∀ i, 0 ≤ t i) :
    ∀ᵐ ω ∂P, ∀ i : ℕ, X (t i) ω = vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (t i) ω :=
  MeasureTheory.ae_all_iff.mpr fun i => h.ae_eq (t i) (ht i)

/-- The increment of a coordinate of a version splits into the drift's window integral and the
martingale part's increment. -/
theorem IsVectorItoVersion.sub_ae (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ}
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) (m : Fin n) :
    ∀ᵐ ω ∂P, X v ω m - X u ω m
      = (∫ s in Set.Ioc u v, bdrift m ω s ∂volume)
        + (vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
          - vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω) := by
  filter_upwards [h.ae_eq v (hu.trans huv), h.ae_eq u hu] with ω hv hu'
  rw [congrFun hv m, congrFun hu' m]
  exact vectorItoProcess_sub W ℱ hcoord H hHm hHp hHs X₀ bdrift hbm hB hu huv m ω

section Moments

variable {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)

include hC0 hCH in
/-- The first absolute moment of a coordinate of a version's increment. -/
theorem IsVectorItoVersion.integral_abs_sub_le
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) (m : Fin n) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) :
    Integrable (fun ω => |X v ω m - X u ω m|) P
      ∧ ∫ ω, |X v ω m - X u ω m| ∂P ≤ B * (v - u) + (d : ℝ) * (C * Real.sqrt (v - u)) := by
  rcases eq_or_lt_of_le huv with rfl | hlt
  · exact ⟨by simp, by simp⟩
  · obtain ⟨hint, hle⟩ := integral_abs_vectorItoProcess_sub_le W ℱ hcoord H hHm hHp hHs hC0 hCH
      X₀ bdrift hbm hB0 hB m hu hlt
    have hae : (fun ω => |X v ω m - X u ω m|)
        =ᵐ[P] fun ω => |vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω m
          - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω m| := by
      filter_upwards [h.ae_eq v (hu.trans huv), h.ae_eq u hu] with ω hv hu'
      rw [congrFun hv m, congrFun hu' m]
    exact ⟨hint.congr hae.symm, by rw [MeasureTheory.integral_congr_ae hae]; exact hle⟩

include hC0 hCH in
/-- The second moment of a coordinate of a version's increment. -/
theorem IsVectorItoVersion.integral_sq_sub_le
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) (m : Fin n) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) :
    Integrable (fun ω => (X v ω m - X u ω m) ^ 2) P
      ∧ ∫ ω, (X v ω m - X u ω m) ^ 2 ∂P
        ≤ 2 * (B * (v - u)) ^ 2 + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (v - u))) := by
  rcases eq_or_lt_of_le huv with rfl | hlt
  · exact ⟨by simp, by simp⟩
  · obtain ⟨hint, hle⟩ := integral_sq_vectorItoProcess_sub_le W ℱ hcoord H hHm hHp hHs hC0 hCH
      X₀ bdrift hbm hB0 hB m hu hlt
    have hae : (fun ω => (X v ω m - X u ω m) ^ 2)
        =ᵐ[P] fun ω => (vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω m
          - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω m) ^ 2 := by
      filter_upwards [h.ae_eq v (hu.trans huv), h.ae_eq u hu] with ω hv hu'
      rw [congrFun hv m, congrFun hu' m]
    exact ⟨hint.congr hae.symm, by rw [MeasureTheory.integral_congr_ae hae]; exact hle⟩

include hC0 hCH in
/-- The first moment of the norm of a version's increment. -/
theorem IsVectorItoVersion.integral_norm_sub_le
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) :
    Integrable (fun ω => ‖X v ω - X u ω‖) P
      ∧ ∫ ω, ‖X v ω - X u ω‖ ∂P
        ≤ (n : ℝ) * (B * (v - u) + (d : ℝ) * (C * Real.sqrt (v - u))) := by
  rcases eq_or_lt_of_le huv with rfl | hlt
  · exact ⟨by simp, by simp⟩
  · obtain ⟨hint, hle⟩ := integral_norm_vectorItoProcess_sub_le W ℱ hcoord H hHm hHp hHs hC0 hCH
      X₀ bdrift hbm hB0 hB hu hlt
    have hae : (fun ω => ‖X v ω - X u ω‖)
        =ᵐ[P] fun ω => ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
          - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω‖ := by
      filter_upwards [h.ae_eq v (hu.trans huv), h.ae_eq u hu] with ω hv hu'
      rw [hv, hu']
    exact ⟨hint.congr hae.symm, by rw [MeasureTheory.integral_congr_ae hae]; exact hle⟩

include hC0 hCH in
/-- The second moment of the norm of a version's increment. -/
theorem IsVectorItoVersion.integral_sq_norm_sub_le
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) :
    Integrable (fun ω => ‖X v ω - X u ω‖ ^ 2) P
      ∧ ∫ ω, ‖X v ω - X u ω‖ ^ 2 ∂P
        ≤ (n : ℝ) * (2 * (B * (v - u)) ^ 2 + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (v - u)))) := by
  rcases eq_or_lt_of_le huv with rfl | hlt
  · exact ⟨by simp, by simp⟩
  · obtain ⟨hint, hle⟩ := integral_sq_norm_vectorItoProcess_sub_le W ℱ hcoord H hHm hHp hHs
      hC0 hCH X₀ bdrift hbm hB0 hB hu hlt
    have hae : (fun ω => ‖X v ω - X u ω‖ ^ 2)
        =ᵐ[P] fun ω => ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
          - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω‖ ^ 2 := by
      filter_upwards [h.ae_eq v (hu.trans huv), h.ae_eq u hu] with ω hv hu'
      rw [hv, hu']
    exact ⟨hint.congr hae.symm, by rw [MeasureTheory.integral_congr_ae hae]; exact hle⟩

include hC0 hCH in
/-- The cube of the norm of a version's increment is integrable. -/
theorem IsVectorItoVersion.integrable_norm_sub_pow_three
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) :
    Integrable (fun ω => ‖X v ω - X u ω‖ ^ 3) P := by
  rcases eq_or_lt_of_le huv with rfl | hlt
  · simp
  · have hint := integrable_norm_vectorItoProcess_sub_pow_three W ℱ hcoord H hHm hHp hHs hC0 hCH
      X₀ bdrift hbm hB0 hB hu hlt
    have hae : (fun ω => ‖X v ω - X u ω‖ ^ 3)
        =ᵐ[P] fun ω => ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
          - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω‖ ^ 3 := by
      filter_upwards [h.ae_eq v (hu.trans huv), h.ae_eq u hu] with ω hv hu'
      rw [hv, hu']
    exact hint.congr hae.symm

end Moments

end VectorVersion

end LevyStochCalc.Brownian.Ito
