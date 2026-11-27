/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Sobolev.Mollify
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Sobolev's embedding in the plane: `W^{1,2}_loc ⊂ L^q_loc` for every `q < ∞`

* `HarmonicAnalysis.memLp_of_hasWeakFDerivOn_univ`: a compactly supported `g ∈ L² (ℂ)` with a weak
  derivative `Dg ∈ L² (ℂ)` is in `L^q (ℂ)` for every `q < ∞`.
* `HarmonicAnalysis.MemLpLoc.of_hasWeakFDerivOn`: `f ∈ W^{1,2}_loc (Ω)` is in `L^q_loc (Ω)` for
  every `q < ∞`.

Two auxiliary results, also used for the Beltrami equation:

* `HarmonicAnalysis.exists_contDiff_tsupport_subset_eventuallyEq_one`: a smooth cut-off with
  compact support in an open `Ω`, equal to `1` on a neighbourhood of a given compact `K ⊆ Ω`.
* `HarmonicAnalysis.MemLpLoc.memLp_smulRight_of_tsupport_subset`: `Dη ⊗ f ∈ L^p` for
  `f ∈ L^p_loc (Ω)` and such a cut-off `η`; with
  `HarmonicAnalysis.MemLpLoc.memLp_smul_of_tsupport_subset`, the weak derivative
  `η Df + Dη ⊗ f` of `η f` is in `L^p` for `f ∈ W^{1,p}_loc (Ω)`.

## Proof

The Gagliardo–Nirenberg–Sobolev inequality of Mathlib (`eLpNorm_le_eLpNorm_fderiv_of_eq`), for
compactly supported `C¹` functions: `‖u‖_q ≤ C ‖Du‖_s` for `1 ≤ s < 2` and `q = 2s / (2 − s)`,
with `C` independent of `u`. Let `g` be compactly supported with weak derivative `Dg ∈ L²`, and
`q ≥ 2`. Multiplying `Dg` by a smooth cut-off `χ` equal to `1` near `tsupport g` gives another weak
derivative of `g` (the Leibniz rule `HarmonicAnalysis.HasWeakFDerivOn.smul_of_tsupport_subset`, as
`χ g = g` and `Dχ ⊗ g = 0`), which has compact support and is therefore in `L^s` (Hölder). The
mollifications `g_n = ρ_n ⋆ g` are smooth with compact support, with `D g_n = ρ_n ⋆ (χ Dg)`
(`HarmonicAnalysis.hasFDerivAt_convolution_of_hasWeakFDerivOn`), so
`‖g_n‖_q ≤ C ‖ρ_n ⋆ (χ Dg)‖_s ≤ C ‖χ Dg‖_s` (`HarmonicAnalysis.eLpNorm_convolution_le`); and
`g_n → g` in `L²`, hence almost everywhere along a subsequence
(`HarmonicAnalysis.tendsto_eLpNorm_convolution_sub`). Fatou's lemma gives
`‖g‖_q ≤ liminf ‖g_n‖_q ≤ C ‖χ Dg‖_s < ∞`. A general `q < ∞` follows from `max q 2` by Hölder's
inequality on the compact support of `g`. For `f ∈ W^{1,2}_loc (Ω)` and a compact `K ⊆ Ω`, apply
this to `g = η f`, with `η ∈ C_c^∞ (Ω)` equal to `1` on `K`
(`HarmonicAnalysis.HasWeakFDerivOn.smul_of_tsupport_subset`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff Convolution

namespace HarmonicAnalysis

/-- **A smooth cut-off**: for a compact `K` in an open set `Ω` of a finite-dimensional real normed
space, a smooth real `η` with compact support in `Ω`, equal to `1` on a neighbourhood of `K`. -/
theorem exists_contDiff_tsupport_subset_eventuallyEq_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {K Ω : Set E} (hK : IsCompact K) (hΩ : IsOpen Ω)
    (hKΩ : K ⊆ Ω) :
    ∃ η : E → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ Ω ∧
      ∀ x ∈ K, η =ᶠ[𝓝 x] 1 := by
  obtain ⟨L₁, hL₁, hKL₁, hL₁Ω⟩ := exists_compact_between hK hΩ hKΩ
  obtain ⟨L₂, hL₂, hL₁L₂, hL₂Ω⟩ := exists_compact_between hL₁ hΩ hL₁Ω
  obtain ⟨η, hη, -, hηs, hη1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) isOpen_interior hL₁.isClosed hL₁L₂
  have hts : tsupport η ⊆ L₂ := by
    rw [tsupport, hηs]
    exact closure_minimal interior_subset hL₂.isClosed
  refine ⟨η, hη, hL₂.of_isClosed_subset (isClosed_tsupport η) hts, hts.trans hL₂Ω,
    fun x hx => ?_⟩
  filter_upwards [mem_interior_iff_mem_nhds.1 (hKL₁ hx)] with y hy
  exact (hη1 y).1 hy

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `Dη ⊗ f`, `v ↦ (∂_v η) f`, is in `L^p` for `f ∈ L^p_loc (Ω)` and a `C¹` real `η` with
compact support in `Ω`. -/
theorem MemLpLoc.memLp_smulRight_of_tsupport_subset {Ω : Set E} {f : E → F} {p : ℝ≥0∞}
    (h : MemLpLoc f p Ω) {η : E → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω) :
    MemLp (fun x => (fderiv ℝ η x).smulRight (f x)) p volume := by
  have hDη : Continuous (fderiv ℝ η) := hη.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := hDη.bounded_above_of_compact_support (hηc.fderiv (𝕜 := ℝ))
  have hfK := h _ hηΩ hηc
  have heq : (tsupport η).indicator (fun x => (fderiv ℝ η x).smulRight (f x)) =
      fun x => (fderiv ℝ η x).smulRight (f x) := by
    refine Set.indicator_eq_self.2 fun x hx => ?_
    by_contra hxη
    apply hx
    simp [fderiv_of_notMem_tsupport ℝ hxη]
  rw [← heq, memLp_indicator_iff_restrict
    (isClosed_tsupport η).measurableSet.nullMeasurableSet]
  refine hfK.of_le_mul (c := C) ?_ (ae_of_all _ fun x => ?_)
  · exact (ContinuousLinearMap.smulRightL ℝ E F).continuous₂.comp_aestronglyMeasurable₂
      hDη.aestronglyMeasurable hfK.aestronglyMeasurable
  · rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

end General

/-- **Sobolev's embedding for `q ≥ 2`**, the main step of
`HarmonicAnalysis.memLp_of_hasWeakFDerivOn_univ`: the Gagliardo–Nirenberg–Sobolev inequality for
the mollifications of `g` and Fatou's lemma. -/
private theorem memLp_nnreal_of_hasWeakFDerivOn_univ {g : ℂ → ℂ} {Dg : ℂ → ℂ →L[ℝ] ℂ}
    (hgc : HasCompactSupport g) (hg : MemLp g 2 volume) (hDg : MemLp Dg 2 volume)
    (h : HasWeakFDerivOn Set.univ g Dg) {q : ℝ≥0} (hq : 2 ≤ q) : MemLp g q volume := by
  -- a derivative with compact support: `χ Dg`, with `χ = 1` near `tsupport g`
  obtain ⟨χ, hχ, hχc, -, hχ1⟩ := exists_contDiff_tsupport_subset_eventuallyEq_one
    hgc.isCompact isOpen_univ (Set.subset_univ _)
  have hgl : LocallyIntegrable g volume := hg.locallyIntegrable one_le_two
  have hDgloc : MemLpLoc Dg 2 Set.univ := fun K _ _ => hDg.restrict K
  set G : ℂ → ℂ →L[ℝ] ℂ := fun x => χ x • Dg x
  have hW : HasWeakFDerivOn Set.univ g G := by
    have hW₀ := h.smul_of_tsupport_subset (hgl.locallyIntegrableOn _)
      ((hDg.locallyIntegrable one_le_two).locallyIntegrableOn _) hχ hχc (Set.subset_univ _)
    have e₁ : (fun x => χ x • g x) = g := by
      ext x
      by_cases hx : x ∈ tsupport g
      · simp [(hχ1 x hx).eq_of_nhds]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    have e₂ : (fun x => χ x • Dg x + (fderiv ℝ χ x).smulRight (g x)) = G := by
      ext x : 1
      by_cases hx : x ∈ tsupport g
      · have : fderiv ℝ χ x = 0 := by
          rw [(hχ1 x hx).fderiv_eq]
          exact fderiv_const_apply _
        simp [G, this]
      · simp [G, image_eq_zero_of_notMem_tsupport hx]
    rwa [e₁, e₂] at hW₀
  have hG2 : MemLp G 2 volume := hDgloc.memLp_smul_of_tsupport_subset hχ.continuous hχc
    (Set.subset_univ _)
  have hGl : LocallyIntegrable G volume := hG2.locallyIntegrable one_le_two
  -- the exponent `s = 2q / (q + 2) ∈ [1, 2)` with `1 / q = 1 / s − 1 / 2`
  set s : ℝ≥0 := (q⁻¹ + 2⁻¹)⁻¹
  have hs1 : 1 ≤ s := by
    rw [← NNReal.coe_le_coe]
    simp only [s, NNReal.coe_inv, NNReal.coe_add, NNReal.coe_one, NNReal.coe_ofNat]
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    rw [one_le_inv₀ (by positivity)]
    calc (q : ℝ)⁻¹ + 2⁻¹ ≤ 2⁻¹ + 2⁻¹ := by gcongr
      _ = 1 := by norm_num
  have hs2 : (s : ℝ≥0∞) ≤ 2 := by
    have : s ≤ 2 := by
      rw [← NNReal.coe_le_coe]
      simp only [s, NNReal.coe_inv, NNReal.coe_add, NNReal.coe_ofNat]
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      have : 0 ≤ (q : ℝ)⁻¹ := by positivity
      linarith
    exact_mod_cast this
  have hqs : ((q : ℝ))⁻¹ = (s : ℝ)⁻¹ - (Module.finrank ℝ ℂ : ℝ)⁻¹ := by
    simp [s, Complex.finrank_real_complex]
  have hGs : MemLp G s volume :=
    hG2.mono_exponent_of_measure_support_ne_top (s := tsupport χ)
      (fun x hx => by simp [G, image_eq_zero_of_notMem_tsupport hx]) hχc.measure_lt_top.ne hs2
  -- the mollifications
  let φ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨1 / ((n : ℝ) + 2), 1 / ((n : ℝ) + 1), by positivity,
      one_div_lt_one_div_of_lt (by positivity) (by linarith)⟩
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set u : ℕ → ℂ → ℂ := fun n => (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] g
  have hu : ∀ n, ContDiff ℝ 1 (u n) := fun n =>
    (φ n).hasCompactSupport_normed.contDiff_convolution_left _
      ((φ n).contDiff_normed.of_le (by exact_mod_cast le_top)) hgl
  have huc : ∀ n, HasCompactSupport (u n) := fun n =>
    (φ n).hasCompactSupport_normed.convolution _ hgc
  have hDu : ∀ n, fderiv ℝ (u n) = (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] G :=
    fun n => funext fun x =>
      (hasFDerivAt_convolution_of_hasWeakFDerivOn (φ n) hgl hGl hW x).fderiv
  set C : ℝ≥0 := SNormLESNormFDerivOfEqConst ℂ (volume : Measure ℂ) s
  have hbound : ∀ n, eLpNorm (u n) q volume ≤ C * eLpNorm G s volume := fun n =>
    calc eLpNorm (u n) q volume ≤ C * eLpNorm (fderiv ℝ (u n)) s volume :=
          eLpNorm_le_eLpNorm_fderiv_of_eq volume (hu n) (huc n) hs1
            (by simp [Complex.finrank_real_complex]) hqs
      _ ≤ C * eLpNorm G s volume := by
          rw [hDu n]
          gcongr
          exact eLpNorm_convolution_le (φ n) (by exact_mod_cast hs1) hGs.aestronglyMeasurable
  -- `u n → g` in `L²`, hence almost everywhere along a subsequence; Fatou's lemma
  have hlim := tendsto_eLpNorm_convolution_sub hφ one_le_two ENNReal.ofNat_ne_top hg
  obtain ⟨ns, -, hns⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero hlim).exists_seq_tendsto_ae
  calc eLpNorm g q volume ≤ atTop.liminf fun n => eLpNorm (u (ns n)) q volume :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => (hu (ns n)).continuous.aestronglyMeasurable) g
          hg.aestronglyMeasurable hns
    _ ≤ C * eLpNorm G s volume :=
        liminf_le_of_frequently_le' (Frequently.of_forall fun n => hbound (ns n))
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hGs.eLpNorm_lt_top

/-- A compactly supported `g ∈ L² (ℂ)` with a weak derivative `Dg ∈ L² (ℂ)` on the whole plane is
in `L^q (ℂ)` for every `q < ∞`. -/
theorem memLp_of_hasWeakFDerivOn_univ {g : ℂ → ℂ} {Dg : ℂ → ℂ →L[ℝ] ℂ}
    (hgc : HasCompactSupport g) (hg : MemLp g 2 volume) (hDg : MemLp Dg 2 volume)
    (h : HasWeakFDerivOn Set.univ g Dg) {q : ℝ≥0∞} (hq : q ≠ ⊤) : MemLp g q volume := by
  have H := memLp_nnreal_of_hasWeakFDerivOn_univ hgc hg hDg h (le_max_right q.toNNReal 2)
  refine H.mono_exponent_of_measure_support_ne_top (s := tsupport g)
    (fun x hx => image_eq_zero_of_notMem_tsupport hx) hgc.measure_lt_top.ne ?_
  calc q = (q.toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal hq).symm
    _ ≤ _ := by exact_mod_cast le_max_left q.toNNReal 2

/-- **Sobolev's embedding in the plane**: `W^{1,2}_loc (Ω) ⊂ L^q_loc (Ω)` for every `q < ∞`. -/
theorem MemLpLoc.of_hasWeakFDerivOn {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ}
    {Df : ℂ → ℂ →L[ℝ] ℂ} (hf : MemLpLoc f 2 Ω) (hDf : MemLpLoc Df 2 Ω)
    (h : HasWeakFDerivOn Ω f Df) {q : ℝ≥0∞} (hq : q ≠ ⊤) : MemLpLoc f q Ω := by
  intro K hKΩ hK
  obtain ⟨η, hη, hηc, hηΩ, hη1⟩ := exists_contDiff_tsupport_subset_eventuallyEq_one hK hΩ hKΩ
  have hW := h.smul_of_tsupport_subset (hf.locallyIntegrableOn hΩ one_le_two)
    (hDf.locallyIntegrableOn hΩ one_le_two) hη hηc hηΩ
  have hgq := memLp_of_hasWeakFDerivOn_univ (hηc.smul_right (f' := f))
    (hf.memLp_smul_of_tsupport_subset hη.continuous hηc hηΩ)
    ((hDf.memLp_smul_of_tsupport_subset hη.continuous hηc hηΩ).add
      (hf.memLp_smulRight_of_tsupport_subset (hη.of_le (by exact_mod_cast le_top)) hηc hηΩ))
    hW hq
  refine (memLp_congr_ae ?_).1 (hgq.restrict K)
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  simp [(hη1 x hx).eq_of_nhds]

end HarmonicAnalysis
