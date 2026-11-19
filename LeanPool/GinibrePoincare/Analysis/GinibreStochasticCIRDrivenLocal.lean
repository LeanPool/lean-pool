/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCIRDrivenLocal.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCIRFullNoiseSums
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticRadialBrownian
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticContinuousFieldIntegral
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticIntegralUntilIdentity
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticWeightedSumMemLp
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralSubstitutionNatural

/-! # Substitution of the radial Brownian driver

Write `X` for the Hamiltonian-stopped configuration, `a` for its CIR amplitude,
and `u` for the unit radial direction of the maximal configuration. The given
`β` is identified by convergence in measure of the original coordinate sums
against `u`; this theorem turns that identification into an integral against
`β` with integrand `a`.

The proof constructs `J` from the bounded coordinate field `a * u`. A second
martingale `N` comes from the localized radius Itô formula. Before the stopping
time their approximating sums coincide, so continuity and uniqueness of limits
identify `J` and `N` there. The bounded substitution theorem then gives
mean-square convergence of sums against `β`; square integrability converts
this to convergence in measure. Finally the Itô identity for `N` transfers to
`J`. Hamiltonian localization supplies the deterministic amplitude bound. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianMaximalProcess_local_CIR_Brownian_integral
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (he : ‖e‖ = 1)
    (β : ℝ≥0 → Ω → ℝ) (hβL : ∀ t, MemLp (β t) 2 P)
    (hβLim : ∀ t, TendstoInMeasure P (fun k ω => ∑ i,
      brownianUniformLeftSum (B i) (fun s ω =>
        ginibreRecenteredRadialDirection n e (ginibreBrownianMaximalProcess n α z B s ω) i)
        t (k + 1) ω) atTop (β t))
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0) :
    let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
    let a := fun t ω => Real.sqrt ((8*(α : ℝ)/(n : ℝ))*pairwiseRadius (X t ω))
    ∃ J : ℝ≥0 → Ω → ℝ,
      Martingale J (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P
          ∧
      (∀ ω, Continuous (fun t => J t ω)) ∧ (∀ t, MemLp (J t) 2 P) ∧ J 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ t ≤ T, Tendsto (fun k => ∫ ω,
        (brownianUniformLeftSum β a t (k+1) ω-J t ω)^2 ∂P) atTop (𝓝 0)) ∧
      (∀ t ≤ T, TendstoInMeasure P (fun k => brownianUniformLeftSum β a t (k+1)) atTop (J t)) ∧
      (∀ᵐ ω ∂P, ∀ t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω,
        pairwiseRadius (X t ω)-pairwiseRadius z = J t ω+
          ∫ s in (0 : ℝ)..t, (4*(α : ℝ)/(n : ℝ))*
            ((recenteredGammaShape n : ℝ)-pairwiseRadius (X s.toNNReal ω))) := by
  classical
  let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
  let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
  let a := fun t ω => Real.sqrt ((8*(α : ℝ)/(n : ℝ))*pairwiseRadius (X t ω))
  let u := fun t ω => ginibreRecenteredRadialDirection n e (ginibreBrownianMaximalProcess n α z B t
      ω)
  obtain ⟨hu, hunit, huc⟩ := ginibreBrownianMaximalProcess_radialDirection_properties hn α z hz B P
      hB hind e he
  obtain ⟨ha, hac, C, hC, hbound⟩ :=
      ginibreBrownianHamiltonianStoppedProcess_CIR_amplitude_properties
    (by omega) α z hz B P hB R hR T
  have hui (i : Fin n × Fin 2) (t : ℝ≥0) : @Measurable Ω ℝ (F t) _ (fun ω => u t ω i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin n × Fin 2 => ℝ) i).measurable.comp (hu t)
  have hub (i : Fin n × Fin 2) (t : ℝ≥0) (ω : Ω) : ‖u t ω i‖ ≤ 1 := by
    exact (PiLp.norm_apply_le (u t ω) i).trans_eq (hunit t ω)
  -- Construct the coordinate-field integral with the full-process direction.
  let A := fun i t ω => a t ω*u t ω i
  have hA (i : Fin n × Fin 2) (t : ℝ≥0) : @Measurable Ω ℝ (F t) _ (A i t) :=
    (ha t).measurable.mul (hui i t)
  have hAb (i : Fin n × Fin 2) (t : ℝ≥0) (ω : Ω) : ‖A i t ω‖ ≤ C := by
    rw [show A i t ω=a t ω*u t ω i from rfl, norm_mul]
    exact (mul_le_mul_of_nonneg_right (hbound t ω) (norm_nonneg _)).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hub i t ω) hC.le)
  have hAc (i : Fin n × Fin 2) : ∀ᵐ ω ∂P, ContinuousOn (fun t => A i t ω) (Icc 0 T) := by
    filter_upwards [huc] with ω hω
    exact ((hac ω).mul ((PiLp.continuous_apply 2 (fun _ : Fin n × Fin 2 => ℝ) i).comp
        hω)).continuousOn
  obtain ⟨J, hJM, hJC, hJL, hJ0, hJS⟩ := ginibreBoundedField_continuous_integral_exists
    B P hB hind A hA T hAc C hC.le hAb
  obtain ⟨N, hNM, hNC, hNL, hN0, hNS, hNIto⟩ :=
      ginibreBrownianMaximalProcess_local_CIR_integral_exists
    hn α z hz B P hB hind R hR T e
  -- Before the stop, both continuous integrals have identical approximating sums.
  have hEq : ∀ᵐ ω ∂P, ∀ t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω,
      J t ω=N t ω := by
    apply ginibreContinuous_probability_limits_eq_until P
      (fun t k ω => ∑ i, brownianUniformLeftSum (B i) (A i) t (k+1) ω)
      (fun t k ω => ∑ i, brownianUniformLeftSum (B i)
        (fun s ω => a s ω*ginibreRecenteredRadialDirection n e (X s ω) i) t (k+1) ω)
      J N (Eventually.of_forall hJC) (Eventually.of_forall hNC) T
      (ginibreBrownianHamiltonianBoundedStop n α z B R T)
      (fun ω => ginibreDrivenHamiltonianBoundedStop_le n α _ z R T) hJS hNS
    intro t ht k ω hts
    have hCF (s : ℝ≥0) (ω : Ω) : CollisionFree (X s ω) :=
      (ginibreBrownianHamiltonianStoppedProcess_range (by omega) α z hz B R hR T s ω).1
    rw [← ginibreConfigurationBrownianGradientSum_radius hn B α α.coe_nonneg X hCF e t k ω]
    exact (ginibreConfigurationBrownianGradientSum_radius_full_direction hn α α.coe_nonneg z hz B R
        hR T e t k ω hts).symm
  -- Substitute the radial driver and retain the stronger mean-square limit.
  have hMS (t : ℝ≥0) (ht : t ≤ T) : Tendsto (fun k => ∫ ω,
      (brownianUniformLeftSum β a t (k+1) ω-J t ω)^2 ∂P) atTop (𝓝 0) :=
    brownianUnitIntegral_bounded_substitution_of_horizon_limits B P hB hind u hu hunit huc a
      (fun r => (ha r).measurable) C hC.le hbound t
      (Eventually.of_forall (fun ω => (hac ω).continuousOn)) β hβL hβLim (J t) (hJS t ht)
  have hAL (t : ℝ≥0) : AEStronglyMeasurable (a t) P :=
    ((ha t).mono (F.le t)).aestronglyMeasurable
  refine ⟨J, hJM, hJC, hJL, hJ0, hMS, ?_, ?_⟩
  · intro t ht
    apply ginibre_tendstoInMeasure_of_meanSquare P _ _ _ (hMS t ht)
    intro k
    exact ((ginibreWeightedUniformLeftSum_memLp P β a hβL hAL C hbound t (k+1)).sub (hJL
        t)).integrable_sq
  · filter_upwards [hEq, hNIto] with ω hω hIto
    intro t ht
    rw [hω t ht]
    exact hIto t ht
end
end GinibrePoincare
