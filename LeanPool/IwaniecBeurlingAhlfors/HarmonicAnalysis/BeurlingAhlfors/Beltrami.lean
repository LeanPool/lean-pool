/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.BeurlingAhlfors.L2
public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Sobolev.Embedding
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Higher integrability of solutions of the Beltrami equation, from the `L^p` norm of `𝓑`

`HarmonicAnalysis.memLpLoc_of_beltrami`: let `Ω ⊆ ℂ` be open, `0 ≤ k < 1` and `2 ≤ p < ∞` with
`k ‖𝓑‖_p < 1`. If `f ∈ W^{1,2}_loc (Ω)` and `|∂_zbar f| ≤ k |∂f|` almost everywhere in `Ω` (`f` is
`K`-quasiregular, `K = (1 + k) / (1 − k)`), then `Df ∈ L^p_loc (Ω)`.

This is T. Iwaniec's argument (*Extremal inequalities in Sobolev spaces and quasiconformal
mappings*, Z. Anal. Anwendungen 1 (1982); as presented in K. Astala, T. Iwaniec and G. Martin,
*Elliptic partial differential equations and quasiconformal mappings in the plane*, Princeton
University Press, 2009, Chapters 13–14). Neither source was read; the argument is the standard
one, as follows.

## Proof

Let `K ⊆ Ω` be compact and `η ∈ C_c^∞ (Ω)` equal to `1` on a neighbourhood of `K`
(`HarmonicAnalysis.exists_contDiff_tsupport_subset_eventuallyEq_one`). Let `μ = ∂_zbar f / ∂f` on
`tsupport η` where `|∂_zbar f| ≤ k |∂f|` (with `0 / 0 = 0`) and `μ = 0` elsewhere, computed from a
strongly measurable version of `Df` on `tsupport η`, so that `μ` is measurable, `|μ| ≤ k`
everywhere and `∂_zbar f = μ ∂f` almost everywhere on `tsupport η`.

1. `g = η f` is a compactly supported `W^{1,2}` function on the plane, with
   `∂_zbar g = η ∂_zbar f + f ∂_zbar η` and `∂g = η ∂f + f ∂η`
   (`HarmonicAnalysis.HasWeakFDerivOn.smul_of_tsupport_subset`). So `∂_zbar g − μ ∂g = h` with
   `h = f (∂_zbar η − μ ∂η)`, and `h ∈ L² ∩ L^p`, since `f ∈ L^q_loc (Ω)` for every `q < ∞`
   (`HarmonicAnalysis.MemLpLoc.of_hasWeakFDerivOn`) and `∂_zbar η − μ ∂η` is bounded and vanishes
   off
   `tsupport η`.
2. `∂g = 𝓑 (∂_zbar g)` (`HarmonicAnalysis.beurlingL2_dzbar`), so `ω = ∂_zbar g ∈ L²` solves
   `ω = h + T ω`, with `T u = μ 𝓑 u`, a bounded operator on `L²` (`μ` acts through Mathlib's
   Hölder multiplication `ContinuousLinearMap.holderL`).
3. `‖T‖ ≤ k < 1` on `L²` (`HarmonicAnalysis.norm_beurlingL2_le`). Iterating `ω = h + T ω`,
   `ω − Σ_{n < N} Tⁿ h = T^N ω`, of `L²` norm at most `k^N ‖ω‖₂ → 0`: the partial sums of the
   Neumann series converge to `ω` in `L²`. On `L² ∩ L^p`, `‖T u‖_p ≤ k ‖𝓑‖_p ‖u‖_p`
   (`HarmonicAnalysis.eLpNorm_beurlingL2_le`), so `‖Σ_{n < N} Tⁿ h‖_p ≤ ‖h‖_p / (1 − k ‖𝓑‖_p)`.
   A subsequence of the partial sums converges almost everywhere to `ω`, and Fatou's lemma gives
   `‖ω‖_p ≤ ‖h‖_p / (1 − k ‖𝓑‖_p) < ∞`.
4. So `∂_zbar g ∈ L^p` and `∂g = 𝓑 (∂_zbar g) ∈ L^p`, hence `Dg ∈ L^p`
   (`HarmonicAnalysis.norm_le_dzPart_add_dzbarPart`), and `Df = Dg` on `K`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HarmonicAnalysis

/-- `∂ (A + B) = ∂A + ∂B`. -/
private theorem bel_dzPart_add (A B : ℂ →L[ℝ] ℂ) : dzPart (A + B) = dzPart A + dzPart B := by
  simp only [dzPart, add_apply]
  ring

/-- `∂_zbar (A + B) = ∂_zbar A + ∂_zbar B`. -/
private theorem bel_dzbarPart_add (A B : ℂ →L[ℝ] ℂ) :
    dzbarPart (A + B) = dzbarPart A + dzbarPart B := by
  simp only [dzbarPart, add_apply]
  ring

/-- `∂ (c A) = c ∂A` for real `c`. -/
private theorem bel_dzPart_smul (c : ℝ) (A : ℂ →L[ℝ] ℂ) : dzPart (c • A) = c * dzPart A := by
  simp only [dzPart, smul_apply, Complex.real_smul]
  ring

/-- `∂_zbar (c A) = c ∂_zbar A` for real `c`. -/
private theorem bel_dzbarPart_smul (c : ℝ) (A : ℂ →L[ℝ] ℂ) :
    dzbarPart (c • A) = c * dzbarPart A := by
  simp only [dzbarPart, smul_apply, Complex.real_smul]
  ring

/-- `∂ (L ⊗ w) = w ∂ (L ⊗ 1)` for a real linear form `L`. -/
private theorem bel_dzPart_smulRight (L : ℂ →L[ℝ] ℝ) (w : ℂ) :
    dzPart (L.smulRight w) = w * dzPart (L.smulRight 1) := by
  simp only [dzPart, ContinuousLinearMap.smulRight_apply, Complex.real_smul, mul_one]
  ring

/-- `∂_zbar (L ⊗ w) = w ∂_zbar (L ⊗ 1)` for a real linear form `L`. -/
private theorem bel_dzbarPart_smulRight (L : ℂ →L[ℝ] ℝ) (w : ℂ) :
    dzbarPart (L.smulRight w) = w * dzbarPart (L.smulRight 1) := by
  simp only [dzbarPart, ContinuousLinearMap.smulRight_apply, Complex.real_smul, mul_one]
  ring

/-- `f c ∈ L^q` for `f ∈ L^q_loc (Ω)` and a bounded measurable `c` vanishing off a compact
`T ⊆ Ω`. -/
private theorem bel_memLp_mul {Ω T : Set ℂ} {f c : ℂ → ℂ} {q : ℝ≥0∞} (hf : MemLpLoc f q Ω)
    (hT : IsCompact T) (hTΩ : T ⊆ Ω) (hc : AEStronglyMeasurable c volume) {C : ℝ}
    (hcC : ∀ z, ‖c z‖ ≤ C) (hcT : ∀ z ∉ T, c z = 0) :
    MemLp (fun z => f z * c z) q volume := by
  have heq : T.indicator (fun z => f z * c z) = fun z => f z * c z :=
    Set.indicator_eq_self.2 fun z hz => by
      by_contra hzT
      exact hz (by simp [hcT z hzT])
  have hfT := hf T hTΩ hT
  rw [← heq, memLp_indicator_iff_restrict hT.measurableSet.nullMeasurableSet]
  refine hfT.of_le_mul (c := C) (hfT.aestronglyMeasurable.mul hc.restrict)
    (ae_of_all _ fun z => ?_)
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hcC z) (norm_nonneg _)

/-- **The Neumann series in `L² ∩ L^p`**: if `ω = h + μ 𝓑 ω` in `L²`, with `μ` measurable,
`|μ| ≤ k < 1` and `k ‖𝓑‖_p < 1`, and `h ∈ L^p`, then `ω ∈ L^p`. -/
private theorem bel_memLp_of_eq {k p : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) (hp : 1 ≤ p)
    (hfin : beurlingPowNorm 1 p ≠ ⊤) (hkp : k * (beurlingPowNorm 1 p).toReal < 1)
    {μ : ℂ → ℂ} (hμm : AEStronglyMeasurable μ volume) (hμk : ∀ z, ‖μ z‖ ≤ k)
    {ω h : Lp ℂ 2 (volume : Measure ℂ)} (hh : MemLp h (ENNReal.ofReal p) volume)
    (hω : ω =ᵐ[volume] fun z => h z + μ z * beurlingL2 ω z) :
    MemLp ω (ENNReal.ofReal p) volume := by
  set P := ENNReal.ofReal p
  set Bp := beurlingPowNorm 1 p
  have hP1 : 1 ≤ P := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  -- the operator `T u = μ · 𝓑 u` on `L²`
  have hμt : MemLp μ ∞ volume := memLp_top_of_bound hμm k (ae_of_all _ hμk)
  set T : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
    (((ContinuousLinearMap.mul ℂ ℂ).holderL volume 2 ∞ 2).flip (hμt.toLp μ)).comp beurlingL2
  have hT : ∀ u, T u =ᵐ[volume] fun z => beurlingL2 u z * μ z := by
    intro u
    filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) (beurlingL2 u)
      (hμt.toLp μ), hμt.coeFn_toLp] with z hz1 hz2
    simp only [T, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.holderL_apply_apply]
    rw [hz1, hz2]
    rfl
  have hTn : ∀ u, ‖T u‖ ≤ k * ‖u‖ := by
    intro u
    calc ‖T u‖ ≤ k * ‖beurlingL2 u‖ := Lp.norm_le_mul_norm_of_ae_le_mul (by
          filter_upwards [hT u] with z hz
          rw [hz, norm_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hμk z) (norm_nonneg _))
      _ ≤ k * ‖u‖ := by
          gcongr
          calc ‖beurlingL2 u‖ ≤ ‖beurlingL2‖ * ‖u‖ := beurlingL2.le_opNorm u
            _ ≤ 1 * ‖u‖ := by gcongr; exact norm_beurlingL2_le
            _ = ‖u‖ := one_mul _
  have hTpow : ∀ n u, ‖(T ^ n) u‖ ≤ k ^ n * ‖u‖ := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih =>
      intro u
      rw [pow_succ', mul_apply_eq_comp]
      calc ‖T ((T ^ n) u)‖ ≤ k * ‖(T ^ n) u‖ := hTn _
        _ ≤ k * (k ^ n * ‖u‖) := by gcongr; exact ih u
        _ = k ^ (n + 1) * ‖u‖ := by ring
  -- `T` on `L² ∩ L^p`
  have hTP : ∀ u : Lp ℂ 2 (volume : Measure ℂ), MemLp u P volume →
      eLpNorm (T u) P volume ≤ ENNReal.ofReal k * Bp * eLpNorm u P volume := by
    intro u hu
    calc eLpNorm (T u) P volume = eLpNorm (fun z => beurlingL2 u z * μ z) P volume :=
          eLpNorm_congr_ae (hT u)
      _ ≤ ENNReal.ofReal k * eLpNorm (beurlingL2 u) P volume :=
          eLpNorm_le_mul_eLpNorm_of_ae_le_mul ((Lp.aestronglyMeasurable _).mul hμm)
            (ae_of_all _ fun z => by
              rw [Pi.mul_apply, norm_mul, mul_comm]
              exact mul_le_mul_of_nonneg_right (hμk z) (norm_nonneg _)) P
      _ ≤ ENNReal.ofReal k * (Bp * eLpNorm u P volume) := by
          gcongr
          exact eLpNorm_beurlingL2_le hp u hu
      _ = ENNReal.ofReal k * Bp * eLpNorm u P volume := (mul_assoc _ _ _).symm
  set r := ENNReal.ofReal k * Bp
  have hr : r < 1 :=
    calc r = ENNReal.ofReal (k * Bp.toReal) := by
          rw [ENNReal.ofReal_mul hk, ENNReal.ofReal_toReal hfin]
      _ < 1 := ENNReal.ofReal_lt_one.2 hkp
  set H := eLpNorm h P volume
  have hTPn : ∀ n, eLpNorm ((T ^ n) h) P volume ≤ r ^ n * H := by
    intro n
    induction n with
    | zero => simp [H]
    | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp]
      have hmem : MemLp ((T ^ n) h) P volume :=
        ih.trans_lt (ENNReal.mul_lt_top (ENNReal.pow_lt_top (hr.trans ENNReal.one_lt_top)) hh)
      calc eLpNorm (T ((T ^ n) h)) P volume ≤ r * eLpNorm ((T ^ n) h) P volume := hTP _ hmem
        _ ≤ r * (r ^ n * H) := by gcongr
        _ = r ^ (n + 1) * H := by ring
  -- the partial sums of the Neumann series
  set S : ℕ → Lp ℂ 2 (volume : Measure ℂ) := fun N => ∑ n ∈ Finset.range N, (T ^ n) h
  have hSP : ∀ N, eLpNorm (S N) P volume ≤ (∑ n ∈ Finset.range N, r ^ n) * H := by
    intro N
    induction N with
    | zero =>
      simp only [S, Finset.range_zero, Finset.sum_empty, zero_mul, nonpos_iff_eq_zero]
      rw [eLpNorm_congr_ae (Lp.coeFn_zero _ _ _)]
      exact eLpNorm_zero
    | succ N ih =>
      simp only [S, Finset.sum_range_succ] at ih ⊢
      calc eLpNorm (⇑(∑ n ∈ Finset.range N, (T ^ n) h + (T ^ N) h)) P volume
          = eLpNorm (⇑(∑ n ∈ Finset.range N, (T ^ n) h) + ⇑((T ^ N) h)) P volume :=
            eLpNorm_congr_ae (Lp.coeFn_add _ _)
        _ ≤ eLpNorm (⇑(∑ n ∈ Finset.range N, (T ^ n) h)) P volume +
            eLpNorm ((T ^ N) h) P volume :=
            eLpNorm_add_le hP1
        _ ≤ (∑ n ∈ Finset.range N, r ^ n) * H + r ^ N * H := add_le_add ih (hTPn N)
        _ = (∑ n ∈ Finset.range N, r ^ n + r ^ N) * H := (add_mul _ _ _).symm
  have hSP' : ∀ N, eLpNorm (S N) P volume ≤ (1 - r)⁻¹ * H := fun N =>
    (hSP N).trans (by
      gcongr
      rw [← ENNReal.tsum_geometric]
      exact sum_le_tsum _)
  -- the partial sums converge to `ω` in `L²`
  have hfix : ω - h = T ω := by
    refine sub_eq_iff_eq_add'.2 (Lp.ext ?_)
    filter_upwards [hω, Lp.coeFn_add h (T ω), hT ω] with z h1 h2 h3
    rw [h1, h2, Pi.add_apply, h3, mul_comm]
  have hrem : ∀ N, ω - S N = (T ^ N) ω := by
    intro N
    induction N with
    | zero => simp [S]
    | succ N ih =>
      simp only [S, Finset.sum_range_succ] at ih ⊢
      rw [← sub_sub, ih, ← map_sub, hfix, pow_succ, mul_apply_eq_comp]
  have hconv : Tendsto S atTop (𝓝 ω) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun N => norm_nonneg _) (g := fun N => k ^ N * ‖ω‖) (fun N => ?_) ?_
    · rw [norm_sub_rev, hrem]
      exact hTpow N ω
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hk hk1).mul_const ‖ω‖
  -- Fatou's lemma along an almost everywhere convergent subsequence
  obtain ⟨ns, -, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hconv).exists_seq_tendsto_ae
  calc eLpNorm ω P volume ≤ atTop.liminf fun n => eLpNorm (S (ns n)) P volume :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => Lp.aestronglyMeasurable _) _
          (Lp.aestronglyMeasurable ω) hns
    _ ≤ (1 - r)⁻¹ * H := liminf_le_of_frequently_le' (Frequently.of_forall fun n => hSP' _)
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (tsub_pos_of_lt hr)) hh

/-- **Iwaniec (1982)**: if `k ‖𝓑‖_p < 1`, `0 ≤ k < 1`, `2 ≤ p`, then every
`f ∈ W^{1,2}_loc (Ω)` with `|∂_zbar f| ≤ k |∂f|` almost everywhere in the open set `Ω` has
`Df ∈ L^p_loc (Ω)`. -/
theorem memLpLoc_of_beltrami {Ω : Set ℂ} (hΩ : IsOpen Ω) {k p : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hp : 2 ≤ p) (hfin : beurlingPowNorm 1 p ≠ ⊤) (hkp : k * (beurlingPowNorm 1 p).toReal < 1)
    {f : ℂ → ℂ} {Df : ℂ → ℂ →L[ℝ] ℂ} (hf : MemLpLoc f 2 Ω) (hDf : MemLpLoc Df 2 Ω)
    (h : HasWeakFDerivOn Ω f Df)
    (hbel : ∀ᵐ z ∂(volume.restrict Ω), ‖dzbarPart (Df z)‖ ≤ k * ‖dzPart (Df z)‖) :
    MemLpLoc Df (ENNReal.ofReal p) Ω := by
  set P := ENNReal.ofReal p
  have hp1 : 1 ≤ p := by linarith
  intro K hKΩ hK
  -- the cut-off `η`, `g = η f` and its weak derivative `Dg`
  obtain ⟨η, hη, hηc, hηΩ, hη1⟩ := exists_contDiff_tsupport_subset_eventuallyEq_one hK hΩ hKΩ
  set T := tsupport η
  have hTc : IsCompact T := hηc
  have hTm : MeasurableSet T := (isClosed_tsupport η).measurableSet
  set g : ℂ → ℂ := fun x => η x • f x
  set Dg : ℂ → ℂ →L[ℝ] ℂ := fun x => η x • Df x + (fderiv ℝ η x).smulRight (f x)
  have hW : HasWeakFDerivOn Set.univ g Dg := h.smul_of_tsupport_subset
    (hf.locallyIntegrableOn hΩ one_le_two) (hDf.locallyIntegrableOn hΩ one_le_two) hη hηc hηΩ
  have hgc : HasCompactSupport g := hηc.smul_right
  have hg2 : MemLp g 2 volume := hf.memLp_smul_of_tsupport_subset hη.continuous hηc hηΩ
  have hη1' : ContDiff ℝ 1 η := hη.of_le (by exact_mod_cast le_top)
  have hDg2 : MemLp Dg 2 volume :=
    (hDf.memLp_smul_of_tsupport_subset hη.continuous hηc hηΩ).add
      (hf.memLp_smulRight_of_tsupport_subset hη1' hηc hηΩ)
  have hfP : MemLpLoc f P Ω := hf.of_hasWeakFDerivOn hΩ hDf h ENNReal.ofReal_ne_top
  -- the Beltrami coefficient `μ`, from a strongly measurable version `D'` of `Df` on `T`
  obtain ⟨D', hD'm, hD'eq⟩ : AEStronglyMeasurable Df (volume.restrict T) :=
    (hDf T hηΩ hTc).aestronglyMeasurable
  have hA : Measurable fun z => dzPart (D' z) :=
    (continuous_dzPart.comp_stronglyMeasurable hD'm).measurable
  have hB : Measurable fun z => dzbarPart (D' z) :=
    (continuous_dzbarPart.comp_stronglyMeasurable hD'm).measurable
  set μ : ℂ → ℂ := T.indicator fun z =>
    if ‖dzbarPart (D' z)‖ ≤ k * ‖dzPart (D' z)‖ then dzbarPart (D' z) / dzPart (D' z) else 0
  have hμm : Measurable μ :=
    (Measurable.ite (measurableSet_le hB.norm (hA.norm.const_mul k)) (hB.div hA)
      measurable_const).indicator hTm
  have hμk : ∀ z, ‖μ z‖ ≤ k := by
    intro z
    simp only [μ, Set.indicator]
    split_ifs with h1 h2
    · rw [norm_div]
      rcases eq_or_ne (dzPart (D' z)) 0 with h0 | h0
      · simp [h0, hk]
      · rw [div_le_iff₀ (norm_pos_iff.2 h0)]
        exact h2
    · simpa using hk
    · simpa using hk
  have hμbel : ∀ᵐ z ∂(volume.restrict T), dzbarPart (Df z) = μ z * dzPart (Df z) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hηΩ hbel, hD'eq,
      ae_restrict_mem hTm] with z hz hzD hzT
    rw [hzD] at hz ⊢
    simp only [μ, Set.indicator_of_mem hzT, hz, ite_true]
    rcases eq_or_ne (dzPart (D' z)) 0 with h0 | h0
    · rw [h0, norm_zero, mul_zero] at hz
      simp [h0, norm_le_zero_iff.1 hz]
    · rw [div_mul_cancel₀ _ h0]
  -- `h = f (∂_zbar η − μ ∂η) ∈ L² ∩ L^p`
  set dη : ℂ → ℂ := fun z => dzPart ((fderiv ℝ η z).smulRight (1 : ℂ))
  set dbη : ℂ → ℂ := fun z => dzbarPart ((fderiv ℝ η z).smulRight (1 : ℂ))
  set c : ℂ → ℂ := fun z => dbη z - μ z * dη z
  set hh : ℂ → ℂ := fun z => f z * c z
  have hDη : Continuous (fderiv ℝ η) := hη1'.continuous_fderiv one_ne_zero
  have hDη1 : Continuous fun z => (fderiv ℝ η z).smulRight (1 : ℂ) :=
    ((ContinuousLinearMap.smulRightL ℝ ℂ ℂ).continuous.comp hDη).clm_apply continuous_const
  obtain ⟨Cη, hCη⟩ := hDη.bounded_above_of_compact_support (hηc.fderiv (𝕜 := ℝ))
  have hcm : AEStronglyMeasurable c volume :=
    ((continuous_dzbarPart.comp hDη1).aestronglyMeasurable).sub
      (hμm.aestronglyMeasurable.mul (continuous_dzPart.comp hDη1).aestronglyMeasurable)
  have hcC : ∀ z, ‖c z‖ ≤ (1 + k) * Cη := by
    intro z
    have h1 : ‖(fderiv ℝ η z).smulRight (1 : ℂ)‖ ≤ Cη := by
      rw [ContinuousLinearMap.norm_smulRight_apply, norm_one, mul_one]
      exact hCη z
    have h2 : ‖dbη z‖ ≤ Cη := (norm_dzbarPart_le _).trans h1
    have h3 : ‖dη z‖ ≤ Cη := (norm_dzPart_le _).trans h1
    calc ‖c z‖ ≤ ‖dbη z‖ + ‖μ z‖ * ‖dη z‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ Cη + k * Cη := by gcongr; exact hμk z
      _ = (1 + k) * Cη := by ring
  have hcT : ∀ z ∉ T, c z = 0 := by
    intro z hz
    simp [c, dη, dbη, fderiv_of_notMem_tsupport ℝ hz, dzPart, dzbarPart]
  have hh2 : MemLp hh 2 volume := bel_memLp_mul hf hTc hηΩ hcm hcC hcT
  have hhP : MemLp hh P volume := bel_memLp_mul hfP hTc hηΩ hcm hcC hcT
  -- `∂_zbar g = h + μ ∂g`
  have heq : ∀ᵐ z ∂volume, dzbarPart (Dg z) = hh z + μ z * dzPart (Dg z) := by
    refine ae_of_ae_restrict_of_ae_restrict_compl T ?_ ?_
    · filter_upwards [hμbel] with z hz
      simp only [Dg, hh, c, dη, dbη, bel_dzPart_add, bel_dzbarPart_add, bel_dzPart_smul,
        bel_dzbarPart_smul]
      rw [bel_dzPart_smulRight _ (f z), bel_dzbarPart_smulRight _ (f z)]
      linear_combination (η z : ℂ) * hz
    · rw [ae_restrict_iff' hTm.compl]
      refine ae_of_all _ fun z hz => ?_
      have h0 : fderiv ℝ η z = 0 := fderiv_of_notMem_tsupport ℝ hz
      have h1 : η z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [Dg, hh, c, dη, dbη, h0, h1, dzPart, dzbarPart]
  -- the Neumann series: `∂_zbar g ∈ L^p`
  set ω : Lp ℂ 2 (volume : Measure ℂ) := (memLp_dzbarPart hDg2).toLp _
  have hBω : beurlingL2 ω =ᵐ[volume] fun z => dzPart (Dg z) := beurlingL2_dzbar hgc hg2 hDg2 hW
  have hωP : MemLp ω P volume := by
    refine bel_memLp_of_eq hk hk1 hp1 hfin hkp hμm.aestronglyMeasurable hμk
      (h := hh2.toLp hh) ((memLp_congr_ae hh2.coeFn_toLp).2 hhP) ?_
    filter_upwards [(memLp_dzbarPart hDg2).coeFn_toLp, hh2.coeFn_toLp, heq, hBω] with
      z h1 h2 h3 h4
    rw [h1, h2, h4]
    exact h3
  -- `∂g = 𝓑 (∂_zbar g) ∈ L^p`, hence `Dg ∈ L^p`
  have hdbar : MemLp (fun z => dzbarPart (Dg z)) P volume :=
    (memLp_congr_ae (memLp_dzbarPart hDg2).coeFn_toLp).1 hωP
  have hdz : MemLp (fun z => dzPart (Dg z)) P volume := by
    refine (memLp_congr_ae hBω).1 ?_
    exact (eLpNorm_beurlingL2_le hp1 ω hωP).trans_lt (ENNReal.mul_lt_top hfin.lt_top hωP)
  have hDgP : MemLp Dg P volume := by
    refine (hdz.norm.add hdbar.norm).of_le hDg2.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    rw [Pi.add_apply, Real.norm_of_nonneg (by positivity)]
    exact norm_le_dzPart_add_dzbarPart (Dg z)
  -- `Df = Dg` on `K`
  refine (memLp_congr_ae ?_).1 (hDgP.restrict K)
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  have h0 : fderiv ℝ η z = 0 := by
    rw [(hη1 z hz).fderiv_eq]
    exact fderiv_const_apply _
  simp [Dg, h0, (hη1 z hz).eq_of_nhds]

end HarmonicAnalysis
