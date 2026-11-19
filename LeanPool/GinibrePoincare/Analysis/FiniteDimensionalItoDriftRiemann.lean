/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FiniteDimensionalItoDriftRiemann.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoDriftVariation

/-!
# Finite dimensional Ito drift riemann

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `itoTestDerivativeDriftRiemann_tendsto`, `itoContinuousScalarRiemann_tendsto`,
`itoContinuousScalarRiemann_fin_tendsto`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Genuine continuous-operator Volterra Riemann sums converge; the operator
coefficient needs only continuity, as occurs for Df along a Brownian path. -/
theorem itoContinuousOperatorDriftRiemann_tendsto (A : ℝ → E →L[ℝ] ℝ) (b : ℝ → E)
    (T : ℝ) (hT : 0 ≤ T) (hA : ContinuousOn A (Icc 0 T))
    (hb : ContinuousOn b (Icc 0 T)) :
    Tendsto (fun n => ∑ i ∈ Finset.range (n+1),
      A (ginibreUniformTime T n i)
        (∫ s in ginibreUniformTime T n i..ginibreUniformTime T n (i+1), b s))
      atTop (𝓝 (∫ s in (0 : ℝ)..T, A s (b s))) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hb
  have hM0 : 0 ≤ M := (norm_nonneg (b 0)).trans (hM 0 ⟨le_rfl, hT⟩)
  have hUC := isCompact_Icc.uniformContinuousOn_of_continuous hA
  have hAb : ContinuousOn (fun s => A s (b s)) (Icc 0 T) := hA.clm_apply hb
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε/(M*T+1)
  have hden : 0 < M*T+1 := by nlinarith
  have hη : 0 < η := div_pos hε hden
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp hUC η hη
  have hmesh : Tendsto (fun n : ℕ => T/((n : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul T
  filter_upwards [hmesh.eventually (gt_mem_nhds hδ)] with n hn
  let τ := ginibreUniformTime T n
  have hmono : Monotone τ := ginibreUniformTime_mono T hT n
  have hτ (i : ℕ) (hi : i ≤ n+1) : τ i ∈ Icc 0 T := by
    constructor
    · simpa [τ] using hmono (Nat.zero_le i)
    · simpa [τ] using hmono hi
  have hsub (i : ℕ) (hi : i < n+1) : Icc (τ i) (τ (i+1)) ⊆ Icc 0 T := by
    intro s hs
    exact ⟨(hτ i hi.le).1.trans hs.1, hs.2.trans (hτ _ (Nat.succ_le_of_lt hi)).2⟩
  have hbi (i : ℕ) (hi : i < n+1) : IntervalIntegrable b volume (τ i) (τ (i+1)) :=
    (hb.mono (hsub i hi)).intervalIntegrable_of_Icc (hmono (Nat.le_succ i))
  have hai (i : ℕ) (hi : i < n+1) : IntervalIntegrable (fun s => A s (b s)) volume (τ i) (τ (i+1))
      :=
    (hAb.mono (hsub i hi)).intervalIntegrable_of_Icc (hmono (Nat.le_succ i))
  have he (i : ℕ) (hi : i < n+1) :
      ‖A (τ i) (∫ s in τ i..τ (i+1), b s) - ∫ s in τ i..τ (i+1), A s (b s)‖ ≤
        η*M*(τ (i+1)-τ i) := by
    have hci : IntervalIntegrable (fun s => A (τ i) (b s)) volume (τ i) (τ (i+1)) :=
      (continuous_const.continuousOn.clm_apply (hb.mono (hsub i hi))).intervalIntegrable_of_Icc
        (hmono (Nat.le_succ i))
    rw [← (A (τ i)).intervalIntegral_comp_comm (hbi i hi),
      ← intervalIntegral.integral_sub hci (hai i hi)]
    have hh : ∀ s ∈ uIoc (τ i) (τ (i+1)), ‖A (τ i) (b s)-A s (b s)‖ ≤ η*M := by
      intro s hs
      rw [uIoc_of_le (hmono (Nat.le_succ i))] at hs
      have hsK := hsub i hi (Ioc_subset_Icc_self hs)
      have hdist : dist (τ i) s < δ := by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs.1.le)]
        have hstep : τ (i+1)-τ i = T/((n : ℝ)+1) := ginibreUniformTime_increment T n i
        linarith [hs.2]
      have hnorm : ‖A (τ i)-A s‖ ≤ η := by
        simpa only [dist_eq_norm] using (hclose _ (hτ i hi.le) s hsK hdist).le
      have hop := (A (τ i)-A s).le_opNorm (b s)
      simp only [sub_apply] at hop
      exact hop.trans (mul_le_mul hnorm (hM s hsK) (norm_nonneg _) hη.le)
    have hh' := intervalIntegral.norm_integral_le_of_norm_le_const hh
    simpa only [abs_of_nonneg (sub_nonneg.mpr (hmono (Nat.le_succ i)))] using hh'
  have hint := intervalIntegral.sum_integral_adjacent_intervals hai
  simp only [τ, ginibreUniformTime_zero, ginibreUniformTime_end] at hint
  rw [dist_eq_norm, ← hint, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), ‖A (τ i) (∫ s in τ i..τ (i+1), b s)-
        ∫ s in τ i..τ (i+1), A s (b s)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n+1), η*M*(τ (i+1)-τ i) :=
      Finset.sum_le_sum (fun i hi => he i (Finset.mem_range.mp hi))
    _ = η*M*T := by
      simp only [τ, ginibreUniformTime_increment, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      have hne : (n : ℝ)+1 ≠ 0 := by positivity
      field_simp
    _ < ε := by
      change (ε/(M*T+1))*M*T < ε
      calc
        _ = (ε*M*T)/(M*T+1) := by ring
        _ < ε := (div_lt_iff₀ hden).mpr (by nlinarith)

/-- The genuine drift part of the discrete chain rule for a locally C² test
along an actual continuous path converges to its actual time integral. -/
theorem itoTestDerivativeDriftRiemann_tendsto (f : E → ℝ) (U : Set E)
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (z b : ℝ → E)
    (T : ℝ) (hT : 0 ≤ T) (hz : ContinuousOn z (Icc 0 T))
    (hzU : ∀ t ∈ Icc 0 T, z t ∈ U) (hb : ContinuousOn b (Icc 0 T)) :
    Tendsto (fun n => ∑ i ∈ Finset.range (n+1),
      fderiv ℝ f (z (ginibreUniformTime T n i))
        (∫ s in ginibreUniformTime T n i..ginibreUniformTime T n (i+1), b s))
      atTop (𝓝 (∫ s in (0 : ℝ)..T, fderiv ℝ f (z s) (b s))) := by
  exact itoContinuousOperatorDriftRiemann_tendsto (fun s => fderiv ℝ f (z s)) b T hT
    ((hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).comp hz hzU) hb

/-- The same actual drift limit at the stochastic library's nonnegative sampling times. -/
theorem itoContinuousOperatorDriftRiemann_fin_tendsto (A : ℝ → E →L[ℝ] ℝ) (b : ℝ → E)
    (T : ℝ≥0) (hA : ContinuousOn A (Icc (0 : ℝ) T))
    (hb : ContinuousOn b (Icc (0 : ℝ) T)) :
    Tendsto (fun n => ∑ i : Fin (n+1),
      A (ginibreUniformBrownianTime T n i)
        (∫ s in (ginibreUniformBrownianTime T n i : ℝ)..
          (ginibreUniformBrownianTime T n (i.val+1) : ℝ), b s))
      atTop (𝓝 (∫ s in (0 : ℝ)..T, A s (b s))) := by
  have he (n : ℕ) : (∑ i : Fin (n+1),
      A (ginibreUniformBrownianTime T n i)
        (∫ s in (ginibreUniformBrownianTime T n i : ℝ)..
          (ginibreUniformBrownianTime T n (i.val+1) : ℝ), b s)) =
      ∑ i ∈ Finset.range (n+1), A (ginibreUniformTime T n i)
        (∫ s in ginibreUniformTime T n i..ginibreUniformTime T n (i+1), b s) := by
    simp only [ginibreUniformBrownianTime_coe]
    exact Fin.sum_univ_eq_sum_range (fun i => A (ginibreUniformTime T n i)
      (∫ s in ginibreUniformTime T n i..ginibreUniformTime T n (i+1), b s)) (n+1)
  simp only [he]
  exact itoContinuousOperatorDriftRiemann_tendsto A b T T.coe_nonneg hA hb

/-- Actual scalar uniform Riemann sums for a merely continuous coefficient. -/
theorem itoContinuousScalarRiemann_tendsto (w : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hw : ContinuousOn w (Icc 0 T)) :
    Tendsto (fun n => ∑ i ∈ Finset.range (n+1), w (ginibreUniformTime T n i)*
      (T/((n : ℝ)+1))) atTop (𝓝 (∫ s in (0 : ℝ)..T, w s)) := by
  have h := itoContinuousOperatorDriftRiemann_tendsto
    (fun s => w s • (ContinuousLinearMap.id ℝ ℝ)) (fun _ => (1 : ℝ)) T hT
    (hw.smul continuous_const.continuousOn) continuous_const.continuousOn
  simpa only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one,
    intervalIntegral.integral_const, ginibreUniformTime_increment] using h

/-- The scalar continuous Riemann limit in the actual Brownian partition indexing. -/
theorem itoContinuousScalarRiemann_fin_tendsto (w : ℝ → ℝ) (T : ℝ≥0)
    (hw : ContinuousOn w (Icc (0 : ℝ) T)) :
    Tendsto (fun n => ∑ i : Fin (n+1), w (ginibreUniformBrownianTime T n i)*
      ((T : ℝ)/((n : ℝ)+1))) atTop (𝓝 (∫ s in (0 : ℝ)..T, w s)) := by
  have h := itoContinuousOperatorDriftRiemann_fin_tendsto
    (fun s => w s • (ContinuousLinearMap.id ℝ ℝ)) (fun _ => (1 : ℝ)) T
    (hw.smul continuous_const.continuousOn) continuous_const.continuousOn
  simpa only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one,
    intervalIntegral.integral_const, ginibreUniformBrownianTime_coe,
    ginibreUniformTime_increment] using h

end
end GinibrePoincare
