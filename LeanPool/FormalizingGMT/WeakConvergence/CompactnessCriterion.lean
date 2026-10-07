/-
Copyright (c) 2026 FormalizingGMT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalizingGMT contributors
-/
module


public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import LeanPool.FormalizingGMT.WeakConvergence.Basic

/-!
# Weak compactness for Radon measures

This file formalizes Evans--Gariepy, Revised Edition, Theorem 1.41: locally uniformly bounded
sequences of Radon measures on Euclidean space are vaguely sequentially compact.
-/

@[expose] public section

open scoped CompactlySupported ENNReal NNReal
open Filter Function Set Topology

noncomputable section

namespace MeasureTheory

private theorem exists_exhaustion_bounds_cutoffs {n : ℕ}
    (μ : ℕ → Measure (EuclideanSpace ℝ (Fin n)))
    (hμ : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      ∃ C : ℝ≥0, ∀ k, μ k K ≤ C) :
    ∃ (K : CompactExhaustion (EuclideanSpace ℝ (Fin n))) (B : ℕ → ℝ≥0)
        (cutoff : ℕ → C_c(EuclideanSpace ℝ (Fin n), ℝ≥0)),
      (∀ m k, μ k (K (m + 1)) ≤ B m) ∧
      (∀ m, Set.EqOn (cutoff m) 1 (K m)) ∧
      (∀ m, tsupport (cutoff m) ⊆ interior (K (m + 1))) ∧
      (∀ m x, cutoff m x ≤ 1) := by
  classical
  let K : CompactExhaustion (EuclideanSpace ℝ (Fin n)) := default
  choose B hB using fun m ↦ hμ (K (m + 1)) (K.isCompact (m + 1))
  have hcut (m : ℕ) :
      ∃ f : C(EuclideanSpace ℝ (Fin n), ℝ), Set.EqOn f 1 (K m) ∧
        IsCompact (tsupport f) ∧ tsupport f ⊆ interior (K (m + 1)) ∧
        ∀ x, f x ∈ Set.Icc 0 1 :=
    exists_continuousMap_one_of_isCompact_subset_isOpen (K.isCompact m) isOpen_interior
      (K.subset_interior_succ m)
  choose f hf_one hf_compact hf_support hf_range using hcut
  let cutoff (m : ℕ) : C_c(EuclideanSpace ℝ (Fin n), ℝ≥0) :=
    (⟨f m, hf_compact m⟩ : C_c(EuclideanSpace ℝ (Fin n), ℝ)).nnrealPart
  refine ⟨K, B, cutoff, hB, ?_, ?_, ?_⟩
  · intro m x hx
    change (f m x).toNNReal = 1
    rw [hf_one m hx]
    norm_num
  · intro m
    apply (closure_mono ?_).trans (hf_support m)
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx ⊢
    intro hfx
    apply hx
    change (f m x).toNNReal = 0
    rw [hfx]
    norm_num
  · intro m x
    simp only [cutoff, CompactlySupportedContinuousMap.nnrealPart_apply]
    exact Real.toNNReal_le_iff_le_coe.mpr (hf_range m x).2

section Weight

variable {X : Type*} [TopologicalSpace X]

private def geometricWeight (m : ℕ) : ℝ≥0 := (2⁻¹ : ℝ≥0) ^ (m + 1)

private def weightCoefficient (B : ℕ → ℝ≥0) (m : ℕ) : ℝ≥0 :=
  geometricWeight m / (B m + 1)

private def weightFunction (B : ℕ → ℝ≥0) (cutoff : ℕ → C_c(X, ℝ≥0))
    (x : X) : ℝ≥0 :=
  ∑' m, weightCoefficient B m * cutoff m x

private lemma summable_geometricWeight : Summable geometricWeight := by
  change Summable fun m : ℕ ↦ (2⁻¹ : ℝ≥0) ^ (m + 1)
  exact NNReal.summable_nat_add (fun m : ℕ ↦ (2⁻¹ : ℝ≥0) ^ m)
    (NNReal.summable_geometric (by norm_num)) 1

private lemma weightCoefficient_pos (B : ℕ → ℝ≥0) (m : ℕ) :
    0 < weightCoefficient B m := by
  simp only [weightCoefficient, geometricWeight]
  positivity

private lemma weightCoefficient_le_geometricWeight (B : ℕ → ℝ≥0) (m : ℕ) :
    weightCoefficient B m ≤ geometricWeight m := by
  exact div_le_self (by positivity) (by simp)

private lemma weightCoefficient_mul_bound_le (B : ℕ → ℝ≥0) (m : ℕ) :
    weightCoefficient B m * B m ≤ geometricWeight m := by
  calc
    weightCoefficient B m * B m ≤ weightCoefficient B m * (B m + 1) := by
      gcongr
      simp
    _ = geometricWeight m := by simp [weightCoefficient]

private lemma tsum_geometricWeight_eq_one : ∑' m, geometricWeight m = 1 := by
  simp only [geometricWeight, pow_succ']
  rw [NNReal.tsum_mul_left, NNReal.tsum_geometric (by norm_num)]
  apply NNReal.eq
  norm_num

private lemma geometricWeight_add (i N : ℕ) :
    geometricWeight (i + N) = (2⁻¹ : ℝ≥0) ^ N * geometricWeight i := by
  simp only [geometricWeight]
  rw [show i + N + 1 = N + (i + 1) by omega, pow_add]

private lemma tsum_geometricWeight_add (N : ℕ) :
    ∑' i, geometricWeight (i + N) = (2⁻¹ : ℝ≥0) ^ N := by
  simp_rw [geometricWeight_add]
  rw [NNReal.tsum_mul_left, tsum_geometricWeight_eq_one, mul_one]

private def natEquivIci (N : ℕ) : ℕ ≃ {m : ℕ // N ≤ m} where
  toFun i := ⟨i + N, by omega⟩
  invFun m := m - N
  left_inv i := by simp
  right_inv m := by
    apply Subtype.ext
    exact Nat.sub_add_cancel m.property

private lemma summable_weightTerms (B : ℕ → ℝ≥0) (cutoff : ℕ → C_c(X, ℝ≥0))
    (hcutoff : ∀ m x, cutoff m x ≤ 1) (x : X) :
    Summable fun m ↦ weightCoefficient B m * cutoff m x := by
  rw [← NNReal.summable_coe]
  apply Summable.of_nonneg_of_le
  · intro m
    positivity
  · intro m
    exact_mod_cast calc
      weightCoefficient B m * cutoff m x ≤ geometricWeight m * 1 :=
        mul_le_mul (weightCoefficient_le_geometricWeight B m) (hcutoff m x)
          (by positivity) (by positivity)
      _ = geometricWeight m := mul_one _
  · exact NNReal.summable_coe.mpr summable_geometricWeight

private lemma continuous_weightFunction (B : ℕ → ℝ≥0)
    (cutoff : ℕ → C_c(X, ℝ≥0)) (hcutoff : ∀ m x, cutoff m x ≤ 1) :
    Continuous (weightFunction B cutoff) := by
  rw [NNReal.isEmbedding_coe.continuous_iff]
  change Continuous fun x ↦ ((weightFunction B cutoff x : ℝ≥0) : ℝ)
  simp only [weightFunction, NNReal.coe_tsum]
  apply continuous_tsum
  · intro m
    fun_prop
  · exact NNReal.summable_coe.mpr summable_geometricWeight
  · intro m x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact_mod_cast calc
      weightCoefficient B m * cutoff m x ≤ geometricWeight m * 1 :=
        mul_le_mul (weightCoefficient_le_geometricWeight B m) (hcutoff m x)
          (by positivity) (by positivity)
      _ = geometricWeight m := mul_one _

private lemma weightFunction_pos (B : ℕ → ℝ≥0) (cutoff : ℕ → C_c(X, ℝ≥0))
    (hcutoff : ∀ m x, cutoff m x ≤ 1) (hcover : ∀ x, ∃ m, 1 ≤ cutoff m x)
    (x : X) :
    0 < weightFunction B cutoff x := by
  obtain ⟨m, hm⟩ := hcover x
  apply (mul_pos (weightCoefficient_pos B m) (lt_of_lt_of_le zero_lt_one hm)).trans_le
  exact (summable_weightTerms B cutoff hcutoff x).le_tsum m fun _ _ ↦ by positivity

private lemma cutoff_eq_zero_of_not_mem (K : CompactExhaustion X)
    (cutoff : ℕ → C_c(X, ℝ≥0))
    (hcutoff_support : ∀ m, tsupport (cutoff m) ⊆ K (m + 1)) {m : ℕ} {x : X}
    (hx : x ∉ K (m + 1)) :
    cutoff m x = 0 := by
  by_contra hne
  apply hx
  exact hcutoff_support m
    (subset_closure (show x ∈ Function.support (cutoff m) by simpa))

variable [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]

private lemma lintegral_cutoff_le (μ : ℕ → Measure X) (K : CompactExhaustion X)
    (B : ℕ → ℝ≥0) (cutoff : ℕ → C_c(X, ℝ≥0))
    (hB : ∀ m k, μ k (K (m + 1)) ≤ B m)
    (hcutoff_support : ∀ m, tsupport (cutoff m) ⊆ K (m + 1))
    (hcutoff : ∀ m x, cutoff m x ≤ 1) (m k : ℕ) :
    ∫⁻ x, (cutoff m x : ℝ≥0∞) ∂μ k ≤ B m := by
  calc
    ∫⁻ x, (cutoff m x : ℝ≥0∞) ∂μ k
      ≤ ∫⁻ x, (K (m + 1)).indicator (fun _ ↦ 1) x ∂μ k := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ K (m + 1)
        · simpa [hx] using ENNReal.coe_le_coe.mpr (hcutoff m x)
        · simp [hx, cutoff_eq_zero_of_not_mem K cutoff hcutoff_support hx]
    _ = μ k (K (m + 1)) :=
      lintegral_indicator_one (K.isCompact (m + 1)).measurableSet
    _ ≤ B m := hB m k

private lemma weighted_univ_le_one (μ : ℕ → Measure X) (K : CompactExhaustion X)
    (B : ℕ → ℝ≥0) (cutoff : ℕ → C_c(X, ℝ≥0))
    (hB : ∀ m k, μ k (K (m + 1)) ≤ B m)
    (hcutoff_support : ∀ m, tsupport (cutoff m) ⊆ K (m + 1))
    (hcutoff : ∀ m x, cutoff m x ≤ 1) (k : ℕ) :
    (μ k).withDensity (fun x ↦ (weightFunction B cutoff x : ℝ≥0∞)) univ ≤ 1 := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hw_coe : (fun x ↦ (weightFunction B cutoff x : ℝ≥0∞)) =
      fun x ↦ ∑' m, ((weightCoefficient B m * cutoff m x : ℝ≥0) : ℝ≥0∞) := by
    funext x
    rw [weightFunction, ENNReal.coe_tsum (summable_weightTerms B cutoff hcutoff x)]
  rw [hw_coe, lintegral_tsum]
  · calc
      ∑' m, ∫⁻ x, (weightCoefficient B m * cutoff m x : ℝ≥0) ∂μ k
        ≤ ∑' m, (geometricWeight m : ℝ≥0∞) := ENNReal.tsum_le_tsum fun m ↦ by
          change (∫⁻ x, (weightCoefficient B m : ℝ≥0∞) *
            (cutoff m x : ℝ≥0∞) ∂μ k) ≤ (geometricWeight m : ℝ≥0∞)
          rw [lintegral_const_mul]
          · calc
              (weightCoefficient B m : ℝ≥0∞) *
                  ∫⁻ x, (cutoff m x : ℝ≥0∞) ∂μ k
                ≤ (weightCoefficient B m : ℝ≥0∞) * B m := by
                  gcongr
                  exact lintegral_cutoff_le μ K B cutoff hB hcutoff_support hcutoff m k
              _ ≤ (geometricWeight m : ℝ≥0∞) := by
                exact_mod_cast weightCoefficient_mul_bound_le B m
          · fun_prop
      _ = 1 := by
        rw [← ENNReal.coe_tsum summable_geometricWeight, tsum_geometricWeight_eq_one]
        simp
  · intro m
    fun_prop

private lemma weighted_compl_le_geometric (μ : ℕ → Measure X)
    (K : CompactExhaustion X) (B : ℕ → ℝ≥0)
    (cutoff : ℕ → C_c(X, ℝ≥0))
    (hB : ∀ m k, μ k (K (m + 1)) ≤ B m)
    (hcutoff_support : ∀ m, tsupport (cutoff m) ⊆ K (m + 1))
    (hcutoff : ∀ m x, cutoff m x ≤ 1) (N k : ℕ) :
    (μ k).withDensity (fun x ↦ (weightFunction B cutoff x : ℝ≥0∞)) (K N)ᶜ
      ≤ ((2⁻¹ : ℝ≥0) ^ N : ℝ≥0∞) := by
  rw [withDensity_apply _ (K.isCompact N).measurableSet.compl]
  have hw_coe : (fun x ↦ (weightFunction B cutoff x : ℝ≥0∞)) =
      fun x ↦ ∑' m, ((weightCoefficient B m * cutoff m x : ℝ≥0) : ℝ≥0∞) := by
    funext x
    rw [weightFunction, ENNReal.coe_tsum (summable_weightTerms B cutoff hcutoff x)]
  rw [hw_coe, lintegral_tsum]
  · calc
      ∑' m, ∫⁻ x in (K N)ᶜ,
          ((weightCoefficient B m * cutoff m x : ℝ≥0) : ℝ≥0∞) ∂μ k
        ≤ ∑' m, if N ≤ m then (geometricWeight m : ℝ≥0∞) else 0 :=
          ENNReal.tsum_le_tsum fun m ↦ by
            split_ifs with hm
            · calc
                (∫⁻ x in (K N)ᶜ,
                    ((weightCoefficient B m * cutoff m x : ℝ≥0) : ℝ≥0∞) ∂μ k)
                  ≤ ∫⁻ x,
                      ((weightCoefficient B m * cutoff m x : ℝ≥0) : ℝ≥0∞) ∂μ k :=
                    setLIntegral_le_lintegral _ _
                _ = (weightCoefficient B m : ℝ≥0∞) *
                    ∫⁻ x, (cutoff m x : ℝ≥0∞) ∂μ k := by
                      change (∫⁻ x, (weightCoefficient B m : ℝ≥0∞) *
                        (cutoff m x : ℝ≥0∞) ∂μ k) = _
                      rw [lintegral_const_mul]
                      fun_prop
                _ ≤ (weightCoefficient B m : ℝ≥0∞) * B m := by
                  gcongr
                  exact lintegral_cutoff_le μ K B cutoff hB hcutoff_support hcutoff m k
                _ ≤ (geometricWeight m : ℝ≥0∞) := by
                  exact_mod_cast weightCoefficient_mul_bound_le B m
            · apply le_of_eq
              apply setLIntegral_eq_zero (K.isCompact N).measurableSet.compl
              intro x hx
              have hx' : x ∉ K (m + 1) := by
                intro hxm
                exact hx (K.subset (by omega) hxm)
              simp [cutoff_eq_zero_of_not_mem K cutoff hcutoff_support hx']
      _ = ∑' m, ({m : ℕ | N ≤ m}.indicator
          (fun i ↦ (geometricWeight i : ℝ≥0∞))) m := by
        apply tsum_congr
        intro m
        simp [Set.indicator]
      _ = ∑' m : {m : ℕ // N ≤ m}, (geometricWeight m : ℝ≥0∞) :=
        (tsum_subtype {m : ℕ | N ≤ m}
          (fun m ↦ (geometricWeight m : ℝ≥0∞))).symm
      _ = ∑' i, (geometricWeight (i + N) : ℝ≥0∞) := by
        simpa [natEquivIci] using
          ((natEquivIci N).tsum_eq
            (fun m : {m : ℕ // N ≤ m} ↦ (geometricWeight m : ℝ≥0∞))).symm
      _ = ((2⁻¹ : ℝ≥0) ^ N : ℝ≥0∞) := by
        rw [← ENNReal.coe_tsum
          (NNReal.summable_nat_add geometricWeight summable_geometricWeight N)]
        simpa only [ENNReal.coe_pow] using
          congrArg (fun x : ℝ≥0 ↦ (x : ℝ≥0∞)) (tsum_geometricWeight_add N)
  · intro m
    fun_prop

end Weight

private theorem exists_tendsto_subseq_of_mass_le_of_compl_le
    {E : Type*} [PseudoMetricSpace E] [T2Space E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.SeparableSpace E] [Nonempty E]
    (ν : ℕ → FiniteMeasure E) (K : ℕ → Set E) (u : ℕ → ℝ≥0)
    (hmass : ∀ k, (ν k).mass ≤ 1)
    (hK : ∀ n, IsCompact (K n)) (hK_mono : Monotone K)
    (hu : Tendsto u atTop (𝓝 0))
    (htail : ∀ k n, ν k (K n)ᶜ ≤ u n) :
    ∃ (φ : ℕ → ℕ) (νlim : FiniteMeasure E),
      StrictMono φ ∧ Tendsto (ν ∘ φ) atTop (𝓝 νlim) := by
  obtain ⟨M, hM, ψ, hψ, hmass_lim⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ≥0) 1)).tendsto_subseq
      (fun k ↦ ⟨by positivity, hmass k⟩)
  simp only [mem_Icc] at hM
  rcases eq_or_ne M 0 with rfl | hM_ne
  · refine ⟨ψ, 0, hψ, ?_⟩
    simpa [Function.comp_def] using
      (FiniteMeasure.tendsto_zero_of_tendsto_zero_mass hmass_lim)
  · have hM_pos : 0 < M := pos_iff_ne_zero.mpr hM_ne
    let c : ℝ≥0 := M / 2
    have hc_pos : 0 < c := by simp [c, hM_pos]
    have hc_lt : c < M := by
      simpa [c] using half_lt_self hM_pos
    have hevent : ∀ᶠ j in atTop, c < (ν (ψ j)).mass :=
      (tendsto_order.1 hmass_lim).1 c hc_lt
    rw [eventually_atTop] at hevent
    obtain ⟨N, hN⟩ := hevent
    let ν' : ℕ → FiniteMeasure E := fun j ↦ ν (ψ (j + N))
    have hmass_lower (j : ℕ) : c ≤ (ν' j).mass :=
      (hN (j + N) (by omega)).le
    have hν'_ne (j : ℕ) : ν' j ≠ 0 := by
      rw [← FiniteMeasure.mass_nonzero_iff]
      exact (hc_pos.trans_le (hmass_lower j)).ne'
    let u' : ℕ → ℝ≥0 := fun n ↦ u n / c
    have hu' : Tendsto u' atTop (𝓝 0) := by
      simpa [u', div_eq_mul_inv] using hu.mul_const c⁻¹
    have htail_normalize (j n : ℕ) : (ν' j).normalize (K n)ᶜ ≤ u' n := by
      rw [(ν' j).normalize_eq_of_nonzero (hν'_ne j)]
      calc
        (ν' j).mass⁻¹ * ν' j (K n)ᶜ
          ≤ c⁻¹ * u n := mul_le_mul
            ((inv_le_inv₀ (hc_pos.trans_le (hmass_lower j)) hc_pos).2 (hmass_lower j))
            (htail (ψ (j + N)) n) (by positivity) (by positivity)
        _ = u' n := by simp [u', div_eq_mul_inv, mul_comm]
    have hcompact :
        IsCompact {ρ : ProbabilityMeasure E | ∀ n, ρ (K n)ᶜ ≤ u' n} :=
      isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le hu' hK
        (Or.inr hK_mono)
    obtain ⟨ρ, hρ, θ, hθ, hρ_lim⟩ :=
      hcompact.tendsto_subseq (fun j ↦ htail_normalize j)
    let φ : ℕ → ℕ := fun i ↦ ψ (θ i + N)
    have hφ : StrictMono φ := by
      apply hψ.comp
      intro i j hij
      exact Nat.add_lt_add_right (hθ hij) N
    let νlim : FiniteMeasure E := M • ρ.toFiniteMeasure
    have hmass_final :
        Tendsto (fun i ↦ (ν (φ i)).mass) atTop (𝓝 M) := by
      exact (hmass_lim.comp (tendsto_add_atTop_nat N)).comp hθ.tendsto_atTop
    have hρ_finite :
        Tendsto (fun i ↦ ((ν' (θ i)).normalize).toFiniteMeasure) atTop
          (𝓝 ρ.toFiniteMeasure) :=
      (ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds atTop).mp hρ_lim
    have hsmul :
        Tendsto
          (fun i ↦ (ν (φ i)).mass • ((ν' (θ i)).normalize).toFiniteMeasure)
          atTop (𝓝 νlim) := by
      simpa [νlim] using hmass_final.smul hρ_finite
    refine ⟨φ, νlim, hφ, ?_⟩
    have hseq (i : ℕ) :
        (ν (φ i)).mass • ((ν' (θ i)).normalize).toFiniteMeasure = ν (φ i) := by
      change (ν (ψ (θ i + N))).mass •
          (ν (ψ (θ i + N))).normalize.toFiniteMeasure = ν (ψ (θ i + N))
      exact (ν (ψ (θ i + N))).self_eq_mass_smul_normalize.symm
    change Tendsto (fun i ↦ ν (φ i)) atTop (𝓝 νlim)
    exact hsmul.congr' (Eventually.of_forall hseq)

private theorem inverse_density_transfer
    {X : Type*} [PseudoMetricSpace X] [LocallyCompactSpace X] [SigmaCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : ℕ → Measure X) (w : X → ℝ≥0) (hw : Continuous w)
    (hw_pos : ∀ x, 0 < w x) (ν : ℕ → FiniteMeasure X)
    (hν : ∀ k, (ν k : Measure X) = (μ k).withDensity fun x ↦ (w x : ℝ≥0∞))
    (φ : ℕ → ℕ) (νlim : FiniteMeasure X)
    (hlim : Tendsto (ν ∘ φ) atTop (𝓝 νlim)) :
    let μlim := (νlim : Measure X).withDensity fun x ↦ ((w x)⁻¹ : ℝ≥0)
    IsLocallyFiniteMeasure μlim ∧ μlim.Regular ∧
      ∀ f : C_c(X, ℝ),
        Tendsto (fun j ↦ ∫ x, f x ∂μ (φ j)) atTop
          (𝓝 (∫ x, f x ∂μlim)) := by
  let winv : X → ℝ≥0 := fun x ↦ (w x)⁻¹
  have hwinv : Continuous winv := hw.inv₀ fun x ↦ (hw_pos x).ne'
  let μlim := (νlim : Measure X).withDensity fun x ↦ (winv x : ℝ≥0∞)
  have hμlim_local : IsLocallyFiniteMeasure μlim := by
    dsimp only [μlim]
    exact IsLocallyFiniteMeasure.withDensity_coe hwinv
  have hμlim_regular : μlim.Regular := by
    let _ := hμlim_local
    infer_instance
  have hrecover :
      μlim.withDensity (fun x ↦ (w x : ℝ≥0∞)) = (νlim : Measure X) := by
    have hinv_ne_zero : ∀ᵐ x ∂(νlim : Measure X), (winv x : ℝ≥0∞) ≠ 0 :=
      .of_forall fun x ↦ ENNReal.coe_ne_zero.mpr (inv_ne_zero (hw_pos x).ne')
    have hinv_ne_top : ∀ᵐ x ∂(νlim : Measure X), (winv x : ℝ≥0∞) ≠ ∞ :=
      .of_forall fun _ ↦ ENNReal.coe_ne_top
    have hsame := withDensity_inv_same
      (μ := (νlim : Measure X)) (f := fun x ↦ (winv x : ℝ≥0∞))
      (ENNReal.continuous_coe.comp hwinv).measurable hinv_ne_zero hinv_ne_top
    rw [show (fun x ↦ ((winv x : ℝ≥0∞))⁻¹) =
        (fun x ↦ (w x : ℝ≥0∞)) by
      funext x
      simp [winv, ENNReal.coe_inv (hw_pos x).ne']] at hsame
    exact hsame
  refine ⟨hμlim_local, hμlim_regular, ?_⟩
  intro f
  let winvC : C(X, ℝ≥0) := ⟨winv, hwinv⟩
  let g : C_c(X, ℝ) := winvC • f
  have hsource (k : ℕ) :
      ∫ x, g x ∂(ν k : Measure X) = ∫ x, f x ∂μ k := by
    rw [hν k, integral_withDensity_eq_integral_smul hw.measurable]
    congr 1
    funext x
    simp [g, winvC, winv, (hw_pos x).ne']
  have htarget :
      ∫ x, g x ∂(νlim : Measure X) = ∫ x, f x ∂μlim := by
    rw [← hrecover, integral_withDensity_eq_integral_smul hw.measurable]
    congr 1
    funext x
    simp [g, winvC, winv, (hw_pos x).ne']
  have hg := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hlim)
    g.toBoundedContinuousFunction
  simpa only [Function.comp_apply,
    CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply, hsource, htarget] using hg

private theorem exists_vaguelyConvergent_subseq_of_compact_bounded_aux
    {n : ℕ} (μ : ℕ → Measure (EuclideanSpace ℝ (Fin n)))
    (hμ : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      ∃ C : ℝ≥0, ∀ k, μ k K ≤ C) :
    ∃ (φ : ℕ → ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))),
      StrictMono φ ∧ IsLocallyFiniteMeasure ν ∧ ν.Regular ∧
        ∀ f : C_c(EuclideanSpace ℝ (Fin n), ℝ),
          Tendsto (fun j ↦ ∫ x, f x ∂μ (φ j)) atTop
            (𝓝 (∫ x, f x ∂ν)) := by
  obtain ⟨K, B, cutoff, hB, hcutoff_one, hcutoff_support, hcutoff_le⟩ :=
    exists_exhaustion_bounds_cutoffs μ hμ
  let w : EuclideanSpace ℝ (Fin n) → ℝ≥0 := weightFunction B cutoff
  have hw : Continuous w := continuous_weightFunction B cutoff hcutoff_le
  have hw_pos : ∀ x, 0 < w x := by
    intro x
    apply weightFunction_pos B cutoff hcutoff_le (x := x)
    intro y
    obtain ⟨m, hm⟩ := K.exists_mem y
    exact ⟨m, (hcutoff_one m hm).ge⟩
  have hcutoff_support' : ∀ m, tsupport (cutoff m) ⊆ K (m + 1) :=
    fun m ↦ (hcutoff_support m).trans interior_subset
  let weighted (k : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
    (μ k).withDensity fun x ↦ (w x : ℝ≥0∞)
  have hweighted_one (k : ℕ) : weighted k univ ≤ 1 := by
    exact weighted_univ_le_one μ K B cutoff hB hcutoff_support' hcutoff_le k
  let νm (k : ℕ) : FiniteMeasure (EuclideanSpace ℝ (Fin n)) :=
    ⟨weighted k, ⟨(hweighted_one k).trans_lt (by simp)⟩⟩
  have hνm (k : ℕ) :
      (νm k : Measure (EuclideanSpace ℝ (Fin n))) =
        (μ k).withDensity fun x ↦ (w x : ℝ≥0∞) := rfl
  have hmass (k : ℕ) : (νm k).mass ≤ 1 := by
    rw [← ENNReal.coe_le_coe, FiniteMeasure.ennreal_mass]
    exact hweighted_one k
  let u : ℕ → ℝ≥0 := fun N ↦ (2⁻¹ : ℝ≥0) ^ N
  have hu : Tendsto u atTop (𝓝 0) :=
    NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have htail (k N : ℕ) : νm k (K N)ᶜ ≤ u N := by
    rw [← ENNReal.coe_le_coe, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact weighted_compl_le_geometric μ K B cutoff hB hcutoff_support'
      hcutoff_le N k
  obtain ⟨φ, νlim, hφ, hνlim⟩ :=
    exists_tendsto_subseq_of_mass_le_of_compl_le
      νm K u hmass (fun N ↦ K.isCompact N) (fun _ _ h ↦ K.subset h) hu htail
  let ν : Measure (EuclideanSpace ℝ (Fin n)) :=
    (νlim : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      fun x ↦ ((w x)⁻¹ : ℝ≥0)
  refine ⟨φ, ν, hφ, ?_⟩
  exact inverse_density_transfer μ w hw hw_pos νm hνm φ νlim hνlim

/-- **Evans--Gariepy, Revised Edition, Theorem 1.41 (p. 66).**

A sequence of Radon measures on Euclidean space that is uniformly bounded on each compact set has
a subsequence converging weakly (i.e. vaguely) to a Radon measure. -/
theorem exists_vaguelyConvergent_subseq_of_compact_bounded
    {n : ℕ} (μ : ℕ → Measure (EuclideanSpace ℝ (Fin n)))
    (hμ : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      ∃ C : ℝ≥0, ∀ k, μ k K ≤ C) :
    ∃ (φ : ℕ → ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))),
      StrictMono φ ∧ ν.Regular ∧
        Measure.WeaklyConverges (fun j ↦ μ (φ j)) ν := by
  obtain ⟨φ, ν, hφ, -, hν_regular, hν⟩ :=
    exists_vaguelyConvergent_subseq_of_compact_bounded_aux μ hμ
  exact ⟨φ, ν, hφ, hν_regular, hν⟩

end MeasureTheory
