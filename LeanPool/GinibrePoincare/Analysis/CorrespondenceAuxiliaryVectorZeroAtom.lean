/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryVectorZeroAtom.lean.
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

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryGinibreVectorMeasure
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroup

/-!
# Correspondence auxiliary vector zero atom

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreResolventVectorSpectralMeasure_zero_atom`.
-/

@[expose] public section
open MeasureTheory Filter Set
open scoped Topology CompactlySupported NNReal
namespace GinibrePoincare
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A positive contraction resolvent with dense range has no zero atom in any
actual vector spectral measure. Strong continuity of its internally constructed
CFC evolution supplies the approximation to the zero spectral indicator. -/
theorem vectorSpectralMeasure_zero_atom (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hSpec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) (hDense : DenseRange R) (u : H) :
    vectorSpectralMeasure R hR u {r : spectrum ℝ R | r.val = 0} = 0 := by
  let K := {r : spectrum ℝ R | r.val = 0}
  let μ := vectorSpectralMeasure R hR u
  have hbound (t : ℝ≥0) (ht : 0 < t) :
      μ K ≤ ENNReal.ofReal ((inner ℂ u (u-resolventCfcEvolution R t u)).re) := by
    let f : ℝ → ℝ := fun r => 1-resolventEvolutionMultiplier (t : ℝ) r
    have hf : Continuous f := continuous_const.sub (resolventEvolutionMultiplier_continuous _)
    let φ : C_c(spectrum ℝ R, ℝ) :=
      ⟨⟨fun r => f r.val, hf.comp continuous_subtype_val⟩,
        HasCompactSupport.of_compactSpace _⟩
    have hφ : ∀ r : spectrum ℝ R, 0 ≤ φ r := by
      intro r
      exact sub_nonneg.mpr (resolventEvolutionMultiplier_mem_unit_interval
        t.coe_nonneg (hSpec r.property)).2
    have hK : IsCompact K := (isClosed_eq continuous_subtype_val continuous_const).isCompact
    have hφK : ∀ r ∈ K, φ r = 1 := by
      intro r hr
      change 1-resolventEvolutionMultiplier (t : ℝ) r.val = 1
      change r.val = 0 at hr
      rw [hr, resolventEvolutionMultiplier_nonpositive (by exact_mod_cast ht) le_rfl, sub_zero]
    have hb := RealRMK.rieszMeasure_le_of_eq_one
      (vectorSpectralPositiveFunctional R hR u) hφ hK hφK
    have hcfc : (cfcHom hR) φ.toContinuousMap = 1-resolventCfcEvolution R t := by
      have hc : cfc f R = (cfcHom hR) φ.toContinuousMap :=
        cfc_apply f R hR hf.continuousOn
      rw [← hc]
      unfold f resolventCfcEvolution
      rw [cfc_sub _ _ R continuous_const.continuousOn
        (resolventEvolutionMultiplier_continuous _).continuousOn]
      change cfc (1 : ℝ → ℝ) R - _ = _
      rw [cfc_one ℝ R hR]
    change μ K ≤ ENNReal.ofReal
      ((inner ℂ u (((cfcHom hR) φ.toContinuousMap) u)).re) at hb
    rw [hcfc] at hb
    simpa only [sub_apply, one_apply_eq_self] using hb
  let t : ℕ → ℝ≥0 := fun m => 1 / ((m : ℝ≥0)+1)
  have ht : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have he : Tendsto (fun m => resolventCfcEvolution R (t m) u) atTop (𝓝 u) := by
    have hh := (continuous_resolventCfcEvolution R hR hSpec hDense u).tendsto 0 |>.comp ht
    simpa only [resolventCfcEvolution_zero R hR, one_apply_eq_self, Function.comp_def] using hh
  have hy : Tendsto (fun m => (inner ℂ u (u-resolventCfcEvolution R (t m) u)).re)
      atTop (𝓝 0) := by
    have h : Continuous (fun v : H => inner ℂ u (u-v)) :=
      continuous_const.inner (continuous_const.sub continuous_id)
    have hh := (Complex.continuous_re.comp h).tendsto u |>.comp he
    simpa [Function.comp_def] using hh
  have hlim : Tendsto (fun m => ENNReal.ofReal
      ((inner ℂ u (u-resolventCfcEvolution R (t m) u)).re)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.tendsto 0
        |>.comp hy
  have hz : μ K ≤ 0 := ge_of_tendsto' hlim (fun m => hbound (t m) (by dsimp [t]; positivity))
  exact le_antisymm hz bot_le

/-- The concrete Ginibre vector resolvent measure has no spectral atom at zero. -/
theorem ginibreResolventVectorSpectralMeasure_zero_atom (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) : ginibreResolventVectorSpectralMeasure n hn u {0} = 0 := by
  unfold ginibreResolventVectorSpectralMeasure
  rw [Measure.map_apply measurable_subtype_coe (measurableSet_singleton 0)]
  exact vectorSpectralMeasure_zero_atom _ (ginibreFullComplexResolvent_isSelfAdjoint n hn)
    (ginibreFullComplexResolvent_spectrum n hn) (ginibreFullComplexResolvent_denseRange n hn) u

end
end GinibrePoincare
