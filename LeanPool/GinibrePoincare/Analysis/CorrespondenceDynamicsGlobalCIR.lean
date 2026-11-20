/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceDynamicsGlobalCIR.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDynamicsLocalization
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticFullTwoRadiusRealization
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterCIRUnrestrictedRealization
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCIRRealization
/-!
# Correspondence dynamics global CIR

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `correspondence_ginibre_global_independent_CIR_equations`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

/-- The global CIR stochastic integral, identified by the actual radius and
its drift. The theorem below proves that ordinary Brownian left sums converge
to it; this is not a definition of the integral by an unverified SDE. -/
def correspondenceCIRIntegral {Ω : Type*} {n : ℕ} (α : ℝ≥0)
    (z : Configuration n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (D : Configuration n → ℝ) (η : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  D (ginibreBrownianMaximalProcess n α z B t ω)-D z-
    ∫ s in (0 : ℝ)..t, (4*(α : ℝ)/(n : ℝ)) *
      (η-D (ginibreBrownianMaximalProcess n α z B s.toNNReal ω))

/-- Actual exhausting Hamiltonian stopping times globalize the stochastic
integral and its CIR identity. Local integral facts are only arguments of this
reusable localization lemma; concrete instantiations discharge them internally. -/
theorem correspondence_global_CIR_integral_of_local
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (D : Configuration n → ℝ) (η : ℝ) (β : ℝ≥0 → Ω → ℝ)
    (hloc : ∀ (R : ℝ), ginibreHamiltonian n z ≤ R → ∀ (T : ℝ≥0),
      ∃ J : ℝ≥0 → Ω → ℝ,
        (∀ t ≤ T, TendstoInMeasure P (fun j => brownianUniformLeftSum β
          (fun s ω => Real.sqrt ((8 * (α : ℝ) / (n : ℝ)) *
            D (ginibreBrownianHamiltonianStoppedProcess n α z B R T s ω))) t (j + 1))
          atTop (J t)) ∧
        (∀ᵐ ω ∂P, ∀ t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω,
          D (ginibreBrownianHamiltonianStoppedProcess n α z B R T t ω) - D z = J t ω +
            ∫ s in (0 : ℝ)..t, (4 * (α : ℝ) / (n : ℝ)) *
              (η - D (ginibreBrownianHamiltonianStoppedProcess n α z B R T s.toNNReal ω))))
    (t : ℝ≥0) :
    TendstoInMeasure P (fun j => brownianUniformLeftSum β
      (fun s ω => Real.sqrt ((8*(α : ℝ)/(n : ℝ))*
        D (ginibreBrownianMaximalProcess n α z B s ω))) t (j+1))
      atTop (correspondenceCIRIntegral α z B D η t) := by
  classical
  let τ := fun k : ℕ => ginibreBrownianHamiltonianBoundedStop n α z B
    (ginibreHamiltonian n z+k) k
  let E := fun k : ℕ => {ω | t ≤ τ k ω}
  have hbad : Tendsto (fun k => P.real (E k)ᶜ) atTop (𝓝 0) :=
    correspondence_measure_compl_of_ae_exhaustion P E
      (fun k => ginibreBrownianHamiltonianBoundedStop_survival_measurable hn α z hz B P hB
        _ (le_add_of_nonneg_right (Nat.cast_nonneg k)) k t)
      ((ginibreBrownianHamiltonianBoundedStop_exhausts_ae hn α z hz B P hB hind).mono
        (fun ω hω => hω t))
  apply correspondence_tendstoInMeasure_of_exhaustion P E _ _ hbad
  intro k
  by_cases ht : t ≤ (k : ℝ≥0)
  · obtain ⟨J, hp, hi⟩ := hloc _ (le_add_of_nonneg_right (Nat.cast_nonneg k)) k
    have hX (ω : Ω) (hω : ω ∈ E k) (s : ℝ≥0) (hs : s ≤ t) :
        ginibreBrownianHamiltonianStoppedProcess n α z B (ginibreHamiltonian n z+k) k s ω =
          ginibreBrownianMaximalProcess n α z B s ω := by
      change ginibreBrownianMaximalProcess n α z B (min s (τ k ω)) ω = _
      rw [min_eq_left (hs.trans hω)]
    have heq : (E k).indicator (J t) =ᵐ[P]
        (E k).indicator (correspondenceCIRIntegral α z B D η t) := by
      filter_upwards [hi] with ω hω
      by_cases he : ω ∈ E k
      · simp only [indicator_of_mem he]
        have hh := hω t he
        rw [hX ω he t le_rfl] at hh
        have hiEq : (∫ s in (0 : ℝ)..t, (4*(α : ℝ)/(n : ℝ))*
            (η-D (ginibreBrownianHamiltonianStoppedProcess n α z B
              (ginibreHamiltonian n z+k) k s.toNNReal ω))) =
            ∫ s in (0 : ℝ)..t, (4*(α : ℝ)/(n : ℝ))*
              (η-D (ginibreBrownianMaximalProcess n α z B s.toNNReal ω)) := by
          apply intervalIntegral.integral_congr
          intro s hs
          have hs' : s ≤ (t : ℝ) := (by simpa [uIcc_of_le t.coe_nonneg] using hs : s ∈ Icc 0 (t :
                                          ℝ)).2
          dsimp only
          rw [hX ω he s.toNNReal ((Real.toNNReal_le_toNNReal hs').trans_eq (Real.toNNReal_coe (r :=
              t)))]
        rw [hiEq] at hh
        dsimp [correspondenceCIRIntegral]
        linarith
      · simp only [indicator_of_notMem he]
    have hleft (j : ℕ) :
        (E k).indicator (fun ω => brownianUniformLeftSum β
          (fun s ω => Real.sqrt ((8*(α : ℝ)/(n : ℝ))*
            D (ginibreBrownianHamiltonianStoppedProcess n α z B (ginibreHamiltonian n z+k) k s ω)))
                t (j+1) ω) =
        (E k).indicator (fun ω => brownianUniformLeftSum β
          (fun s ω => Real.sqrt ((8*(α : ℝ)/(n : ℝ))*
            D (ginibreBrownianMaximalProcess n α z B s ω))) t (j+1) ω) := by
      funext ω
      by_cases he : ω ∈ E k
      · simp only [indicator_of_mem he, brownianUniformLeftSum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hX ω he _ (itoUniformNNTime_le_end t (j+1) i (by omega)
          (Finset.mem_range.mp hi).le)]
      · simp only [indicator_of_notMem he]
    exact (ginibre_tendstoInMeasure_indicator P (E k) _ _ (hp t ht)).congr
      (fun j => Eventually.of_forall (fun ω => congrFun (hleft j) ω)) heq
  · have hE : E k = ∅ := by
      ext ω
      simp only [E, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro hω
      apply ht
      exact hω.trans (ginibreDrivenHamiltonianBoundedStop_le n α _ z _ k)
    simp only [hE, indicator_empty]
    intro ε hε
    simp [not_le.mpr hε]

/-- The two original Ginibre radii satisfy their CIR equations on the full
unrestricted time axis. Both Brownian drivers are independent; both stochastic
integrals are identified by convergence in probability of Brownian left sums
with the actual, unstopped amplitudes. -/
theorem correspondence_ginibre_global_independent_CIR_integrals
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0) (hα : 0 < α)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∃ βS βR : ℝ≥0 → Ω → ℝ,
      IsBrownianReal βS P ∧ IsBrownianReal βR P ∧
      IndepFun (fun ω t => βS t ω) (fun ω t => βR t ω) P ∧
      (∀ t, TendstoInMeasure P (fun j => brownianUniformLeftSum βS
        (fun s ω => Real.sqrt ((8*(α : ℝ)/(n : ℝ))*ginibreCenterSquared n
          (ginibreBrownianMaximalProcess n α z B s ω))) t (j+1))
        atTop (correspondenceCIRIntegral α z B (ginibreCenterSquared n) 1 t)) ∧
      (∀ t, TendstoInMeasure P (fun j => brownianUniformLeftSum βR
        (fun s ω => Real.sqrt ((8*(α : ℝ)/(n : ℝ))*pairwiseRadius
          (ginibreBrownianMaximalProcess n α z B s ω))) t (j+1))
        atTop (correspondenceCIRIntegral α z B pairwiseRadius (recenteredGammaShape n) t)) := by
  classical
  let i₀ : Fin n × Fin 2 := (⟨0, by omega⟩, 0)
  let e : EuclideanSpace ℝ (Fin n × Fin 2) := EuclideanSpace.single i₀ 1
  have he : ‖e‖=1 := by simp [e, PiLp.norm_single]
  obtain ⟨βS, hβS, hβSM, hβSL, hβS0, hβSLim, hβSShift, hβSFresh⟩ :=
    ginibreBrownianMaximalProcess_center_unrestricted_Brownian_exists hn α hα z hz B P hB hind
  obtain ⟨βR, hβR, hβRM, hβRL, hβR0, hβRLim, hβRShift, hβRFresh⟩ :=
    ginibreBrownianMaximalProcess_radial_Brownian_exists hn α z hz B P hB hind
  refine ⟨βS, βR, hβS, hβR,?_,?_,?_⟩
  · exact ginibreBrownian_unrestricted_center_radial_drivers_independent hn α hα z hz
      B P hB hind e e βS βR hβS.cont hβS0 hβSShift hβR.cont hβRLim
  · apply correspondence_global_CIR_integral_of_local (by omega) α z hz B P hB hind
    intro R hR T
    have hc := if hcenter : ginibreCenterSquared n z=0 then
      ginibreBrownianMaximalProcess_zero_center_CIR_Brownian_integral hn α hα z hz hcenter
        B P hB hind e he βS hβSM hβSL hβSLim R hR T else
      ginibreBrownianMaximalProcess_local_center_CIR_Brownian_integral hn α z hz
        (lt_of_le_of_ne (ginibreCenterSquared_nonneg n z) (Ne.symm hcenter))
        B P hB hind e he βS hβSL hβSLim R hR T
    obtain ⟨J, hJM, hJC, hJL, hJ0, hJMS, hJP, hJI⟩ := hc
    exact ⟨J, hJP, hJI⟩
  · apply correspondence_global_CIR_integral_of_local (by omega) α z hz B P hB hind
    intro R hR T
    obtain ⟨J, hJM, hJC, hJL, hJ0, hJMS, hJP, hJI⟩ :=
      ginibreBrownianMaximalProcess_local_CIR_Brownian_integral hn α z hz B P hB hind
        e he βR hβRL hβRLim R hR T
    exact ⟨J, hJP, hJI⟩

/-- Literal global CIR equations and independent Brownian driving noises,
with both stochastic integrals verified by unstopped Brownian left sums. -/
theorem correspondence_ginibre_global_independent_CIR_equations
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0) (hα : 0 < α)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∃ βS βR JS JR : ℝ≥0 → Ω → ℝ,
      IsBrownianReal βS P ∧ IsBrownianReal βR P ∧
      IndepFun (fun ω t => βS t ω) (fun ω t => βR t ω) P ∧
      (∀ t, TendstoInMeasure P (fun j => brownianUniformLeftSum βS
        (fun s ω => Real.sqrt ((8*(α : ℝ)/(n : ℝ))*ginibreCenterSquared n
          (ginibreBrownianMaximalProcess n α z B s ω))) t (j+1)) atTop (JS t)) ∧
      (∀ t, TendstoInMeasure P (fun j => brownianUniformLeftSum βR
        (fun s ω => Real.sqrt ((8*(α : ℝ)/(n : ℝ))*pairwiseRadius
          (ginibreBrownianMaximalProcess n α z B s ω))) t (j+1)) atTop (JR t)) ∧
      (∀ ω t, ginibreCenterSquared n (ginibreBrownianMaximalProcess n α z B t ω)-
        ginibreCenterSquared n z = JS t ω+
          ∫ s in (0 : ℝ)..t, (4*(α : ℝ)/(n : ℝ))*
            (1-ginibreCenterSquared n (ginibreBrownianMaximalProcess n α z B s.toNNReal ω))) ∧
      (∀ ω t, pairwiseRadius (ginibreBrownianMaximalProcess n α z B t ω)-pairwiseRadius z =
        JR t ω+∫ s in (0 : ℝ)..t, (4*(α : ℝ)/(n : ℝ))*
          ((recenteredGammaShape n : ℝ)-pairwiseRadius
            (ginibreBrownianMaximalProcess n α z B s.toNNReal ω))) := by
  obtain ⟨βS, βR, hS, hR, hi, hSI, hRI⟩ :=
    correspondence_ginibre_global_independent_CIR_integrals hn α hα z hz B P hB hind
  refine ⟨βS, βR, correspondenceCIRIntegral α z B (ginibreCenterSquared n) 1,
    correspondenceCIRIntegral α z B pairwiseRadius (recenteredGammaShape n),
    hS, hR, hi, hSI, hRI,?_,?_⟩ <;> intro ω t <;> unfold correspondenceCIRIntegral <;> ring

end
end GinibrePoincare
