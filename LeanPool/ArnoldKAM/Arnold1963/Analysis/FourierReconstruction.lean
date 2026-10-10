/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Analysis.ShiftedFourier
public import LeanPool.ArnoldKAM.Arnold1963.Analysis.TailConstant

/-!
Reconstruction of the original analytic phase function and bounds for its Fourier remainder.
-/

@[expose] public section
noncomputable section
open Complex
open scoped NNReal
namespace KamProject.Arnold1963

theorem angleScale_normalize {n : ℕ} (q : ComplexSpace n) :
    angleScale n (complexShift (fun j => (q j).im / (2 * Real.pi))
      (fun j => (q j).re / (2 * Real.pi))) = q := by
  have hT : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  ext j
  simp [complexShift]
  field_simp
  exact re_add_im (q j)

theorem imagPart_shift_zero {n : ℕ} (y t : RealSpace n) :
    imagPart (angleScale n (complexShift y 0)) =
      imagPart (angleScale n (complexShift y t)) := by
  ext j
  simp [imagPart, complexShift, mul_im]

namespace AnalyticPhaseFunction
variable {n : ℕ} {G : Set (ComplexSpace n)} {ρ : ℝ≥0}

theorem hasSum_fourier_on_strip (f : AnalyticPhaseFunction n G ρ) {p : ComplexSpace n}
    (hp : p ∈ G) {σ : ℝ≥0} (hσρ : σ < ρ) {q : ComplexSpace n}
    (hq : q ∈ angleStrip n σ) :
    HasSum (fun k => f.fourierCoeff p k * fourierMonomial k q) (f.toFun (p, q)) := by
  let y : RealSpace n := fun j => (q j).im / (2 * Real.pi)
  let t : RealSpace n := fun j => (q j).re / (2 * Real.pi)
  have he : angleScale n (complexShift y t) = q := angleScale_normalize q
  have hy : ∀ j, |y j| ≤ normalizedWidth ρ := by
    intro j
    dsimp [y, normalizedWidth]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    exact div_le_div_of_nonneg_right
      (((mem_angleStrip_iff _ _).mp hq j).trans (show (σ : ℝ) ≤ ρ from hσρ.le))
      (by positivity)
  have hd : (0 : ℝ) < (ρ : ℝ) - σ := sub_pos.mpr (show (σ : ℝ) < ρ from hσρ)
  have hw : ‖imagPart (angleScale n (complexShift y 0))‖ ≤
      (ρ : ℝ) - ((ρ : ℝ) - σ) := by
    rw [imagPart_shift_zero y t, he]
    simpa [angleStrip] using hq
  simpa only [he] using f.hasSum_fourier_shifted hp y hy hd hw t

theorem tsum_fourierTerms_apply (f : AnalyticPhaseFunction n G ρ) {p : ComplexSpace n}
    (hp : p ∈ G) {σ : ℝ≥0} (hσρ : σ < ρ) (q : angleStrip n σ) :
    (∑' k, fourierTermOnStrip (f.fourierCoeff p) σ k) q = f.toFun (p, q) := by
  have hsum := summable_fourierTerms_of_decay (f.norm_le_iff.mp le_rfl).nonneg
    (sub_pos.mpr (show (σ : ℝ) < ρ from hσρ))
    (show (σ : ℝ) ≤ (ρ : ℝ) - ((ρ : ℝ) - σ) by linarith)
    (f.norm_fourierCoeff_le_exp hp)
  have hs := (BoundedContinuousFunction.evalCLM ℂ q).hasSum hsum.hasSum
  exact hs.unique (f.hasSum_fourier_on_strip hp hσρ q.property)

theorem norm_sub_fourierTruncation_le (f : AnalyticPhaseFunction n G ρ)
    {p : ComplexSpace n} (hp : p ∈ G) (hn : 0 < n)
    {δ γ N : ℝ} {σ : ℝ≥0} (hδ : 0 < δ) (hsmall : δ ≤ 1 / 12)
    (hγ : 0 ≤ γ) (hσ : (σ : ℝ) ≤ (ρ : ℝ) - (δ + γ))
    {q : ComplexSpace n} (hq : q ∈ angleStrip n σ) :
    ‖f.toFun (p, q) - fourierTruncation (f.fourierCoeff p) N q‖ ≤
      (((2 * n : ℝ) / Real.exp 1) ^ n * f.uniformNorm / δ ^ (n + 1)) *
        Real.exp (-N * γ) := by
  have hσρ : σ < ρ := by exact_mod_cast (show (σ : ℝ) < ρ by linarith)
  have hb := norm_fourierSeries_tail_le_arnoldConstant (N := N) hn
    (f.norm_le_iff.mp le_rfl).nonneg hδ hsmall hγ hσ (f.norm_fourierCoeff_le_exp hp)
  have he := BoundedContinuousFunction.norm_coe_le_norm
    ((∑' k, fourierTermOnStrip (f.fourierCoeff p) σ k) -
      ∑ k ∈ fourierModes n N, fourierTermOnStrip (f.fourierCoeff p) σ k) ⟨q, hq⟩
  apply le_trans _ hb
  rw [BoundedContinuousFunction.sub_apply, f.tsum_fourierTerms_apply hp hσρ,
    BoundedContinuousFunction.sum_apply] at he
  exact he

/-- The difference between a phase function and its finite Fourier truncation. -/
def fourierRemainder (f : AnalyticPhaseFunction n G ρ) (N : ℝ)
    (z : ComplexPhaseSpace n) : ℂ :=
  f.toFun z - fourierTruncation (f.fourierCoeff z.1) N z.2

theorem normBoundOn_fourierRemainder (f : AnalyticPhaseFunction n G ρ) (hn : 0 < n)
    {δ γ N : ℝ} {σ : ℝ≥0} (hδ : 0 < δ) (hsmall : δ ≤ 1 / 12)
    (hγ : 0 ≤ γ) (hσ : (σ : ℝ) ≤ (ρ : ℝ) - (δ + γ)) :
    NormBoundOn (f.fourierRemainder N) (phaseDomain G σ)
      ((((2 * n : ℝ) / Real.exp 1) ^ n * f.uniformNorm / δ ^ (n + 1)) *
        Real.exp (-N * γ)) := by
  refine ⟨?_, fun z hz => f.norm_sub_fourierTruncation_le hz.1 hn hδ hsmall hγ hσ hz.2⟩
  have hM := (f.norm_le_iff.mp le_rfl).nonneg
  positivity

end AnalyticPhaseFunction
end KamProject.Arnold1963
