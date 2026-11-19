/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianInteractionTilt.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianInteractionEnergy
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralExponentialNatural
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticContinuousLocalIdentity

/-! The actual OU-to-original Brownian drift tilt and its compact bounds. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BigOperators
namespace GinibrePoincare
noncomputable section

/-- The interaction drift `-(√(2α/n²) / 2) * ∂ᵢ W z` along the real coordinate direction `i`,
where `W = ginibreInteractionPotential n`. -/
def ginibreInteractionBrownianTilt (n : ℕ) (α : ℝ)
    (z : Configuration n) (i : Fin n × Fin 2) : ℝ :=
  -(Real.sqrt (2*α/(n : ℝ)^2)/2)*
    fderiv ℝ (ginibreInteractionPotential n) z (ginibreCoordinateDirection i)

theorem ginibreInteractionBrownianTilt_measurable (n : ℕ) (α : ℝ)
    (i : Fin n × Fin 2) : Measurable (fun z => ginibreInteractionBrownianTilt n α z i) :=
  measurable_const.mul (measurable_fderiv_apply_const ℝ (ginibreInteractionPotential n) _)

theorem ginibreInteractionBrownianTilt_continuousOn (n : ℕ) (α : ℝ)
    (i : Fin n × Fin 2) :
    ContinuousOn (fun z => ginibreInteractionBrownianTilt n α z i) {z | CollisionFree z} := by
  have hv : ContDiffOn ℝ 2 (ginibreInteractionPotential n) {z | CollisionFree z} :=
    fun z hz => ((ginibreInteractionPotential_contDiffAt n z hz).of_le
      (by exact WithTop.coe_le_coe.mpr (show (2 : ENat) ≤ ⊤ from le_top))).contDiffWithinAt
  exact continuousOn_const.mul ((hv.continuousOn_fderiv_of_isOpen (isOpen_collisionFree n) (by
      norm_num)).clm_apply continuousOn_const)

theorem ginibreInteractionBrownianTilt_compact_bound (n : ℕ) (α : ℝ)
    (K : Set (Configuration n)) (hK : IsCompact K) (hCF : ∀ z ∈ K, CollisionFree z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, (∑ i, (ginibreInteractionBrownianTilt n α z i)^2) ≤ C^2 := by
  have hc : ContinuousOn (fun z => ∑ i, (ginibreInteractionBrownianTilt n α z i)^2) K :=
    continuousOn_finsetSum _ (fun i _ => ((ginibreInteractionBrownianTilt_continuousOn n α i).mono
        hCF).pow 2)
  obtain ⟨R, hR, hb⟩ := (hK.image_of_continuousOn hc).isBounded.exists_pos_norm_le
  refine ⟨R+1, by linarith,?_⟩
  intro z hz
  have hh := hb _ (mem_image_of_mem _ hz)
  rw [Real.norm_eq_abs] at hh
  have hs := (le_abs_self (∑ i, (ginibreInteractionBrownianTilt n α z i)^2)).trans hh
  nlinarith [sq_nonneg R]

theorem ginibreInteractionBrownianTilt_noise_drift (n : ℕ) (α : ℝ) (hα : 0 ≤ α)
    (z : Configuration n) (i : Fin n × Fin 2) :
    Real.sqrt (2*α/(n : ℝ)^2)*ginibreInteractionBrownianTilt n α z i =
      -(α/(n : ℝ)^2)*fderiv ℝ (ginibreInteractionPotential n) z (ginibreCoordinateDirection i) := by
  unfold ginibreInteractionBrownianTilt
  have hs : (Real.sqrt (2*α/(n : ℝ)^2))^2 = 2*α/(n : ℝ)^2 :=
    Real.sq_sqrt (div_nonneg (by linarith) (sq_nonneg _))
  calc
    _ = -((Real.sqrt (2*α/(n : ℝ)^2))^2/2)*
      fderiv ℝ (ginibreInteractionPotential n) z (ginibreCoordinateDirection i) := by ring
    _ = _ := by rw [hs]; ring

theorem ginibreInteractionBrownianTilt_energy (n : ℕ) (α : ℝ) (hα : 0 ≤ α)
    (z : Configuration n) :
    (∑ i, (ginibreInteractionBrownianTilt n α z i)^2) =
      (α/(2*(n : ℝ)^2))*ginibreInteractionGradientNormSq n z := by
  unfold ginibreInteractionBrownianTilt ginibreInteractionGradientNormSq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, ginibreCoordinateDirection,
    ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hs : (Real.sqrt (2*α/(n : ℝ)^2))^2 = 2*α/(n : ℝ)^2 :=
    Real.sq_sqrt (div_nonneg (by linarith) (sq_nonneg _))
  simp only [mul_pow, neg_sq, div_pow, hs, ite_true]
  ring

/-- The actual interaction drift tilt has genuine normalized coordinate
exponential integrals on every compact collision-free adapted path. -/
theorem ginibreInteractionBrownianTilt_exponential_exists {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0)
    (Y : ℝ≥0 → Ω → Configuration n)
    (hY : StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB
        i).toIsPreBrownianReal)) Y)
    (hYC : ∀ ω, Continuous (fun t => Y t ω))
    (K : Set (Configuration n)) (hK : IsCompact K) (hCF : ∀ z ∈ K, CollisionFree z)
    (hRange : ∀ t ω, Y t ω ∈ K) (T : ℝ≥0) :
    ∃ M : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ,
      (∀ i, Martingale (M i) (ginibreBrownianAugmentedFiltration B P
        (fun i => (hB i).toIsPreBrownianReal)) P ∧
        (∀ ω, Continuous (fun t => M i t ω)) ∧ (∀ t, MemLp (M i t) 2 P) ∧
        M i 0 =ᵐ[P] (fun _ => 0) ∧
        ∀ t ≤ T, TendstoInMeasure P
          (fun k => brownianUniformLeftSum (B i)
            (fun r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) t (k+1)) atTop (M i t)) ∧
      Integrable (brownianVectorExponentialIntegralDensity
        (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (fun i => M i T)) P ∧
      (∫ ω, brownianVectorExponentialIntegralDensity
        (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (fun i => M i T) ω ∂P)=1 := by
  obtain ⟨C, hC, hb⟩ := ginibreInteractionBrownianTilt_compact_bound n α K hK hCF
  have hF (i : Fin n × Fin 2) (r : ℝ≥0) :
      @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P
        (fun i => (hB i).toIsPreBrownianReal) r) _
        (fun ω => ginibreInteractionBrownianTilt n α (Y r ω) i) :=
    (ginibreInteractionBrownianTilt_measurable n α i).comp (hY r).measurable
  have hc (i : Fin n × Fin 2) : ∀ᵐ ω ∂P,
      ContinuousOn (fun r => ginibreInteractionBrownianTilt n α (Y r ω) i) (Icc 0 T) :=
    ae_of_all P (fun ω => ((ginibreInteractionBrownianTilt_continuousOn n α i).comp_continuous
      (hYC ω) (fun r => hCF _ (hRange r ω))).continuousOn)
  obtain ⟨M, hM, hDi, hD1, hLimit⟩ := brownianBoundedVector_exponential_integral_exists_normalized
    B P hB hind (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i)
      hF C hC (fun r ω => hb _ (hRange r ω)) T hc
  exact ⟨M, hM, hDi, hD1⟩

theorem ginibreInteractionBrownianTilt_leftSums {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ)
    (Y : ℝ≥0 → Ω → Configuration n) (T : ℝ≥0) (k : ℕ) (ω : Ω) :
    (∑ i, brownianUniformLeftSum (B i)
      (fun r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (k+1) ω) =
    -(ginibreConfigurationBrownianGradientSum n B α Y (ginibreInteractionPotential n) T k ω)/2 := by
  rw [ginibreConfigurationBrownianGradientSum_eq]
  unfold brownianUniformLeftSum ginibreInteractionBrownianTilt
  have hc (a : ℝ) : -(Real.sqrt (2*α/(n : ℝ)^2)*a)/2 =
      -(Real.sqrt (2*α/(n : ℝ)^2)/2)*a := by ring
  rw [hc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only
  ring

theorem ginibreInteractionBrownianTilt_integrals_eq_gradient {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0)
    (Y : ℝ≥0 → Ω → Configuration n)
    (hY : StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB
        i).toIsPreBrownianReal)) Y)
    (K : Set (Configuration n)) (hK : IsCompact K) (hCF : ∀ z ∈ K, CollisionFree z)
    (hRange : ∀ t ω, Y t ω ∈ K) (T : ℝ≥0)
    (J : ℝ≥0 → Ω → ℝ) (hJC : ∀ ω, Continuous (fun t => J t ω))
    (hJ : ∀ t ≤ T, TendstoInMeasure P
      (ginibreConfigurationBrownianGradientSum n B α Y (ginibreInteractionPotential n) t) atTop (J
          t))
    (M : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (hMC : ∀ i ω, Continuous (fun t => M i t ω))
    (hM : ∀ i t, t ≤ T → TendstoInMeasure P
      (fun k => brownianUniformLeftSum (B i)
        (fun r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) t (k + 1)) atTop (M i t)) :
    ∀ᵐ ω ∂P, ∀ t ≤ T, (∑ i, M i t ω) = -J t ω/2 := by
  classical
  obtain ⟨C, hC, hb⟩ := ginibreInteractionBrownianTilt_compact_bound n α K hK hCF
  let F := fun (i : Fin n × Fin 2) r ω => ginibreInteractionBrownianTilt n α (Y r ω) i
  have hF (i : Fin n × Fin 2) (r : ℝ≥0) :
      @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P
        (fun i => (hB i).toIsPreBrownianReal) r) _ (F i r) :=
    (ginibreInteractionBrownianTilt_measurable n α i).comp (hY r).measurable
  have hFi (i : Fin n × Fin 2) (r : ℝ≥0) : MemLp (F i r) 2 P := by
    apply MemLp.of_bound (((hF i r).mono ((ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal)).le r) le_rfl).aestronglyMeasurable) C
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs]
    apply abs_le_of_sq_le_sq _ hC
    exact (Finset.single_le_sum (fun j _ => sq_nonneg (F j r ω)) (Finset.mem_univ i)).trans
      (hb _ (hRange r ω))
  have hFixed (t : ℝ≥0) : ∀ᵐ ω ∂P, t ≤ T → (∑ i, M i t ω) = -J t ω/2 := by
    by_cases ht : t ≤ T
    · have hs (i : Fin n × Fin 2) (k : ℕ) :=
        (brownianUniformLeftSum_memLp_two B P (fun i => (hB i).toIsPreBrownianReal)
          hind i (F i) (hF i) (hFi i) t (k+1)).aestronglyMeasurable
      have hsum := itoTendstoInMeasure_finset_sum P Finset.univ
        (fun i k => brownianUniformLeftSum (B i) (F i) t (k+1)) (fun i => M i t)
        hs (fun i => hM i t ht)
      have hg := ginibre_tendstoInMeasure_const_mul P
        (ginibreConfigurationBrownianGradientSum n B α Y (ginibreInteractionPotential n) t)
        (J t) (-(1/2 : ℝ)) (hJ t ht)
      have hh : TendstoInMeasure P
          (fun k ω => ∑ i, brownianUniformLeftSum (B i) (F i) t (k+1) ω) atTop
          (fun ω => -J t ω/2) := by
        convert hg using 1
        · funext k ω
          rw [ginibreInteractionBrownianTilt_leftSums]
          ring
        · funext ω; ring
      filter_upwards [tendstoInMeasure_ae_unique hsum hh] with ω hω
      exact fun _ => hω
    · exact ae_of_all P (fun ω h => False.elim (ht h))
  exact ginibre_ae_continuous_identity_until P (fun t ω => ∑ i, M i t ω)
    (fun t ω => -J t ω/2) (fun _ => T)
    (ae_of_all P (fun ω => continuous_finsetSum _ (fun i _ => hMC i ω)))
    (ae_of_all P (fun ω => (hJC ω).neg.div_const 2)) hFixed

end
end GinibrePoincare
