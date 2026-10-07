/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedLerayLimitPairing
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# The flux of the forced momentum pairing on a space-time set

In `lem:forced-equicontinuity` the increment of a spatial pairing of a forced
regularized solution is the space-time integral of the momentum flux against
the test field, with the pressure term. On any space-time set this integral
is bounded, by Hölder's inequality, through the `L²` norms of the transport
velocity, the velocity, the gradient and the force, the `L^{3/2}` norm of the
pressure, and the measure of the set, with the supremum bounds of the test
field, of its derivatives and of its divergence as coefficients.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The extended norm of a real number bounded by `M` is bounded by
`ENNReal.ofReal M`. -/
private theorem forcedLerayLimit_enorm_le_ofReal {x M : ℝ} (h : |x| ≤ M) :
    ‖x‖ₑ ≤ ENNReal.ofReal M := by
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal h

/-- Hölder's inequality `∫ φ ψ ≤ ‖φ‖_p ‖ψ‖_q` for extended nonnegative
functions on a restricted measure, with conjugate exponents. -/
private theorem forcedLerayLimit_lintegral_mul_le {S : Set ParabolicPoint} {p q : ℝ}
    (hpq : p.HolderConjugate q) {φ ψ : ParabolicPoint → ℝ≥0∞}
    (hφ : AEMeasurable φ (volume.restrict S)) (hψ : AEMeasurable ψ (volume.restrict S)) :
    ∫⁻ z in S, φ z * ψ z ≤
      (∫⁻ z in S, φ z ^ p) ^ (1 / p) * (∫⁻ z in S, ψ z ^ q) ^ (1 / q) :=
  ENNReal.lintegral_mul_le_Lp_mul_Lq _ hpq hφ hψ

/-- The lower integral of `‖g‖` over a set is at most the `L^p` quantity times
the measure of the set to the power `1 - 1/p`. -/
private theorem forcedLerayLimit_lintegral_enorm_le {S : Set ParabolicPoint} {p q : ℝ}
    (hpq : p.HolderConjugate q) {g : ParabolicPoint → ℝ}
    (hg : AEMeasurable g (volume.restrict S)) :
    ∫⁻ z in S, ‖g z‖ₑ ≤ (∫⁻ z in S, ‖g z‖ₑ ^ p) ^ (1 / p) * volume S ^ (1 / q) := by
  have h := forcedLerayLimit_lintegral_mul_le hpq hg.enorm
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [mul_one, ENNReal.one_rpow, setLIntegral_const, one_mul] at h
  convert h using 2

/-- `lem:forced-equicontinuity`, the flux bound: on a set `S` the lower
integral of the flux density with the pressure term is bounded through the
`L²` norms of the transport velocity, velocity, gradient and force, the
`L^{3/2}` norm of the pressure and the measure of `S`. -/
theorem forcedLerayLimit_flux_lintegral_le {S : Set ParabolicPoint}
    {U J f : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {P : ParabolicPoint → ℝ} {wc : Fin 3 → Vec3 → ℝ} {M0 M1 M2 : ℝ}
    (hM0 : ∀ i x, |wc i x| ≤ M0) (hM1 : ∀ i j x, |spatialDeriv (wc i) j x| ≤ M1)
    (hM2 : ∀ x, |∑ i : Fin 3, spatialDeriv (wc i) i x| ≤ M2)
    (hU : AEMeasurable U (volume.restrict S)) (hJ : AEMeasurable J (volume.restrict S))
    (hD : AEMeasurable D (volume.restrict S)) (hf : AEMeasurable f (volume.restrict S))
    (hP : AEMeasurable P (volume.restrict S)) :
    ∫⁻ z in S, ‖forcedHopfPairingFlux J U f D wc z +
        P z * ∑ i : Fin 3, spatialDeriv (wc i) i z.1‖ₑ ≤
      ENNReal.ofReal M1 * ∑ i : Fin 3, ∑ j : Fin 3,
          (∫⁻ z in S, ‖J z j‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
            (∫⁻ z in S, ‖U z i‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) +
        ENNReal.ofReal M1 * ∑ i : Fin 3, ∑ j : Fin 3,
          (∫⁻ z in S, ‖D z i j‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * volume S ^ (1 / 2 : ℝ) +
        ENNReal.ofReal M0 * ∑ i : Fin 3,
          (∫⁻ z in S, ‖f z i‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * volume S ^ (1 / 2 : ℝ) +
        ENNReal.ofReal M2 *
          ((∫⁻ z in S, ‖P z‖ₑ ^ (3 / 2 : ℝ)) ^ (1 / (3 / 2 : ℝ)) * volume S ^ (1 / 3 : ℝ)) := by
  have h22 : (2 : ℝ).HolderConjugate 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  have h323 : (3 / 2 : ℝ).HolderConjugate 3 := ⟨by norm_num, by norm_num, by norm_num⟩
  let μ := (volume : Measure ParabolicPoint).restrict S
  have hUi (i : Fin 3) : AEMeasurable (fun z => U z i) μ := hU.eval i
  have hJj (j : Fin 3) : AEMeasurable (fun z => J z j) μ := hJ.eval j
  have hDij (i j : Fin 3) : AEMeasurable (fun z => D z i j) μ := (hD.eval i).eval j
  have hfi (i : Fin 3) : AEMeasurable (fun z => f z i) μ := hf.eval i
  let g1 : ParabolicPoint → ℝ≥0∞ := fun z =>
    ∑ i : Fin 3, ∑ j : Fin 3, ‖J z j‖ₑ * ‖U z i‖ₑ
  let g2 : ParabolicPoint → ℝ≥0∞ := fun z => ∑ i : Fin 3, ∑ j : Fin 3, ‖D z i j‖ₑ
  let g3 : ParabolicPoint → ℝ≥0∞ := fun z => ∑ i : Fin 3, ‖f z i‖ₑ
  have hg1 : AEMeasurable g1 μ := Finset.aemeasurable_fun_sum _ fun i _ =>
    Finset.aemeasurable_fun_sum _ fun j _ => (hJj j).enorm.mul (hUi i).enorm
  have hg2 : AEMeasurable g2 μ := Finset.aemeasurable_fun_sum _ fun i _ =>
    Finset.aemeasurable_fun_sum _ fun j _ => (hDij i j).enorm
  have hg3 : AEMeasurable g3 μ := Finset.aemeasurable_fun_sum _ fun i _ => (hfi i).enorm
  have hpoint : ∀ z, ‖forcedHopfPairingFlux J U f D wc z +
      P z * ∑ i : Fin 3, spatialDeriv (wc i) i z.1‖ₑ ≤
      ENNReal.ofReal M1 * g1 z + ENNReal.ofReal M1 * g2 z + ENNReal.ofReal M0 * g3 z +
        ENNReal.ofReal M2 * ‖P z‖ₑ := by
    intro z
    unfold forcedHopfPairingFlux
    refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (enorm_add_le _ _).trans (add_le_add ((enorm_sub_le).trans (add_le_add ?_ ?_)) ?_)
      · refine (enorm_sum_le _ _).trans ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun i _ => (enorm_sum_le _ _).trans ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun j _ => ?_
        rw [enorm_mul, enorm_mul, mul_comm (ENNReal.ofReal M1)]
        exact mul_le_mul' le_rfl (forcedLerayLimit_enorm_le_ofReal (hM1 i j z.1))
      · refine (enorm_sum_le _ _).trans ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun i _ => (enorm_sum_le _ _).trans ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun j _ => ?_
        rw [enorm_mul, mul_comm (ENNReal.ofReal M1)]
        exact mul_le_mul' le_rfl (forcedLerayLimit_enorm_le_ofReal (hM1 i j z.1))
      · refine (enorm_sum_le _ _).trans ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun i _ => ?_
        rw [enorm_mul, mul_comm (ENNReal.ofReal M0)]
        exact mul_le_mul' le_rfl (forcedLerayLimit_enorm_le_ofReal (hM0 i z.1))
    · rw [enorm_mul, mul_comm (ENNReal.ofReal M2)]
      exact mul_le_mul' le_rfl (forcedLerayLimit_enorm_le_ofReal (hM2 z.1))
  refine (lintegral_mono hpoint).trans ?_
  have hA : AEMeasurable (fun z => ENNReal.ofReal M1 * g1 z + ENNReal.ofReal M1 * g2 z +
      ENNReal.ofReal M0 * g3 z) μ :=
    ((hg1.const_mul _).add (hg2.const_mul _)).add (hg3.const_mul _)
  have hB : AEMeasurable (fun z => ENNReal.ofReal M1 * g1 z + ENNReal.ofReal M1 * g2 z) μ :=
    (hg1.const_mul _).add (hg2.const_mul _)
  have hC : AEMeasurable (fun z => ENNReal.ofReal M1 * g1 z) μ := hg1.const_mul _
  rw [lintegral_add_left' hA, lintegral_add_left' hB, lintegral_add_left' hC,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp only [g1, g2, g3]
  have hJU (i j : Fin 3) : AEMeasurable (fun z => ‖J z j‖ₑ * ‖U z i‖ₑ) μ :=
    (hJj j).enorm.mul (hUi i).enorm
  refine add_le_add (add_le_add (add_le_add (mul_le_mul' le_rfl ?_) (mul_le_mul' le_rfl ?_))
    (mul_le_mul' le_rfl ?_)) (mul_le_mul' le_rfl ?_)
  · rw [lintegral_finsetSum' _ fun i _ => Finset.aemeasurable_fun_sum _ fun j _ => hJU i j]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [lintegral_finsetSum' _ fun j _ => hJU i j]
    refine Finset.sum_le_sum fun j _ => ?_
    exact forcedLerayLimit_lintegral_mul_le h22 (hJj j).enorm (hUi i).enorm
  · rw [lintegral_finsetSum' _ fun i _ => Finset.aemeasurable_fun_sum _ fun j _ =>
      (hDij i j).enorm]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [lintegral_finsetSum' _ fun j _ => (hDij i j).enorm]
    refine Finset.sum_le_sum fun j _ => ?_
    exact forcedLerayLimit_lintegral_enorm_le h22 (hDij i j)
  · rw [lintegral_finsetSum' _ fun i _ => (hfi i).enorm]
    refine Finset.sum_le_sum fun i _ => ?_
    exact forcedLerayLimit_lintegral_enorm_le h22 (hfi i)
  · exact forcedLerayLimit_lintegral_enorm_le h323 hP

end CKN.Leray

end
