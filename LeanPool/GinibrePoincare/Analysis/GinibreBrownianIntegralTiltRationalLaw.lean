/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralTiltRationalLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGirsanovRationalStates

/-!
# Ginibre Brownian integral tilt rational law

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianVectorExponentialIntegralDensity_rational_states_hasLaw`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Under the actual terminal exponential likelihood, the full corrected
vector path has the genuine original Brownian joint law on every rational
subdivision of that same terminal horizon. -/
theorem brownianVectorExponentialIntegralDensity_rational_states_hasLaw
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (F : ι → ℝ≥0 → Ω → ℝ)
    (hF : ∀ i t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F i t))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t ω, (∑ i, (F i t ω) ^ 2) ≤ C ^ 2)
    (T : ℝ≥0)
    (hc : ∀ i, ∀ᵐ ω ∂P, ContinuousOn (fun s => F i s ω) (Set.Icc 0 T))
    (hs : ∀ i n, AEStronglyMeasurable (brownianUniformLeftSum (B i) (F i) T (n + 1)) P)
    (I : ι → Ω → ℝ)
    (hI : ∀ i, TendstoInMeasure P
      (fun n => brownianUniformLeftSum (B i) (F i) T (n + 1)) atTop (I i))
    (q : ℕ) (hq : 0 < q) :
    HasLaw (fun ω (p : Fin (q+1)) i => B i (T*(p.val : ℝ≥0)/(q : ℝ≥0)) ω-B i 0 ω-
      ∫ s in (0 : ℝ)..(T*(p.val : ℝ≥0)/(q : ℝ≥0) : ℝ≥0), F i (Real.toNNReal s) ω)
      (P.map (fun ω (p : Fin (q+1)) i => B i (T*(p.val : ℝ≥0)/(q : ℝ≥0)) ω-B i 0 ω))
      (P.withDensity (fun ω => ENNReal.ofReal (brownianVectorExponentialIntegralDensity F T I ω)))
          := by
  classical
  let τ := fun n => itoUniformNNTime T (q*(n+1))
  let h := fun n k ω i => F i (τ n k) ω
  let D := fun n => brownianPredictableVectorGaussianDensity B (h n) (τ n) (q*(n+1))
  let X := fun n ω (p : Fin (q+1)) i => brownianGirsanovCorrectedPrefix B (h n) (τ n) i
      (p.val*(n+1)) ω
  let Y := fun ω (p : Fin (q+1)) i => B i (T*(p.val : ℝ≥0)/(q : ℝ≥0)) ω-B i 0 ω
  let x := fun ω (p : Fin (q+1)) i => Y ω p i-
    ∫ s in (0 : ℝ)..(T*(p.val : ℝ≥0)/(q : ℝ≥0) : ℝ≥0), F i (Real.toNNReal s) ω
  have hh (n k : ℕ) : @Measurable Ω (ι→ℝ)
      (ginibreBrownianAugmentedFiltration B P hB (τ n k)) _ (h n k) := by
    let : MeasurableSpace Ω := ginibreBrownianAugmentedFiltration B P hB (τ n k)
    exact Measurable.of_eval (fun i => hF i _)
  have hzero (n : ℕ) : τ n 0=0 := by
    change (itoUniformTime T (q*(n+1)) 0).toNNReal=0
    simp only [itoUniformTime, Nat.cast_zero, mul_zero, zero_div, Real.toNNReal_zero]
  have hdm (n : ℕ) : Measurable (D n) :=
    (brownianPredictableVectorGaussianDensity_measurable_at B P hB (h n) (τ n)
      (itoUniformNNTime_mono _ _) (hh n) _).mono
      ((ginibreBrownianAugmentedFiltration B P hB).le _) le_rfl
  have hdp (n : ℕ) : 0≤ᵐ[P] D n := Eventually.of_forall fun ω =>
    (brownianPredictableVectorGaussianDensity_pos B _ _ _ ω).le
  have hdli (n : ℕ) : (∫⁻ ω, ENNReal.ofReal (D n ω) ∂P)=1 :=
    brownianPredictableVectorGaussianDensity_lintegral B P hB hind (h n) (τ n)
      (itoUniformNNTime_mono _ _) (hh n) _
  have hdi (n : ℕ) : Integrable (D n) P :=
    ⟨(hdm n).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (hdp n)).mpr (by rw [hdli]; simp)⟩
  have hdn (n : ℕ) : (∫ ω, D n ω ∂P)=1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (hdp n) (hdm n).aestronglyMeasurable, hdli]
    simp
  have hxmeas (n : ℕ) : Measurable (X n) := by
    apply Measurable.of_eval
    intro p
    apply Measurable.of_eval
    intro i
    exact (brownianGirsanovCorrectedPrefix_measurable_at B P hB (h n) (τ n)
      (itoUniformNNTime_mono _ _) (hh n) i _).mono
      ((ginibreBrownianAugmentedFiltration B P hB).le _) le_rfl
  have hYm : Measurable Y := by
    apply Measurable.of_eval
    intro p
    apply Measurable.of_eval
    intro i
    exact ((ginibreBrownian_augmented_coordinate_measurable_at B P hB _ _ le_rfl i).mono
      ((ginibreBrownianAugmentedFiltration B P hB).le _) le_rfl).sub
      ((ginibreBrownian_augmented_coordinate_measurable_at B P hB 0 0 le_rfl i).mono
        ((ginibreBrownianAugmentedFiltration B P hB).le _) le_rfl)
  have hae : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (x ω)) := by
    have hcAll := ae_all_iff.mpr hc
    filter_upwards [hcAll] with ω hω
    apply tendsto_pi_nhds.mpr
    intro p
    apply tendsto_pi_nhds.mpr
    intro i
    by_cases hp : p.val=0
    · have ht0 : T*(p.val : ℝ≥0)/(q : ℝ≥0)=0 := by simp [hp]
      have hX0 (n : ℕ) : X n ω p i=0 := by simp [X, hp, brownianGirsanovCorrectedPrefix]
      have hx0 : x ω p i=0 := by
        dsimp only [x, Y]
        rw [ht0]
        simp
      simp_rw [hX0, hx0]
      exact tendsto_const_nhds
    · have hp' : 0<p.val := Nat.pos_of_ne_zero hp
      have ht : T*(p.val : ℝ≥0)/(q : ℝ≥0)≤T := by
        rw [mul_div_assoc]
        apply (mul_le_mul_of_nonneg_left ((div_le_one (by positivity : (0 : ℝ≥0)<q)).mpr ?_) (show
            (0 : ℝ≥0)≤T from bot_le)).trans_eq
          (mul_one T)
        exact_mod_cast Nat.le_of_lt_succ p.isLt
      have hc' := (hω i).mono (Set.Icc_subset_Icc le_rfl ht)
      have hri := brownianRationalPrefix_drift_tendsto T p.val q hp' hq (fun s => F i s ω) hc'
      have heq (n : ℕ) : X n ω p i = Y ω p i-
          ∑ k ∈ Finset.range (p.val*(n+1)), F i (itoUniformNNTime T (q*(n+1)) k) ω*
            ((T : ℝ)/(q*(n+1) : ℕ)) := by
        dsimp only [X]
        rw [brownianGirsanovCorrectedPrefix_eq, hzero n]
        dsimp only [h, τ, Y]
        rw [brownianUniformNNTime_rational_endpoint T p.val q (n+1) hq (Nat.succ_pos n)]
        simp_rw [itoUniformNNTime_increment_sub_coe]
      simpa only [heq, x] using tendsto_const_nhds.sub hri
  have hxl := tendstoInMeasure_of_tendsto_ae (fun n => (hxmeas n).aestronglyMeasurable) hae
  have hx := hxl.aemeasurable (fun n => (hxmeas n).aemeasurable)
  let μ := P.map Y
  let : IsProbabilityMeasure μ := (by infer_instance)
  have hd := brownianVectorExponentialIntegralDensity_normalized B P hB hind F hF C hC hb T hc hs I
      hI
  have hDeq (n : ℕ) : D n = brownianVectorExponentialUniformSum B F T
      (brownianRationalRefinementIndex q n) := by
    have he := brownianPredictableVectorGaussianDensity_uniform_eq B F T
        (brownianRationalRefinementIndex q n)
    simpa only [brownianRationalRefinementIndex_succ q n hq, D, h, τ] using he
  apply actualVaryingDensity_constantLaw_limit P D _ hdi hd.1 hdp hd.2.1 hdn hd.2.2.1
    (by simpa only [Function.comp_def,← hDeq] using hd.2.2.2.comp
          (brownianRationalRefinementIndex_tendsto q hq))
    X x (fun n => (hxmeas n).aemeasurable) hx hxl μ
  intro n
  have hl := brownianGirsanovRationalGrid_states_identDistrib B P hB hind (h n) T q (n+1)
    hq (Nat.succ_pos n) (hh n)
  exact ⟨hl.aemeasurable_fst, hl.map_eq⟩

end
end GinibrePoincare
