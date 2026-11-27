/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.FaithfulDensityPurification
public import LeanPool.VacuumBellSeparation.Bell.ClosedCyclicSpan
public import LeanPool.VacuumBellSeparation.Bell.HilbertAmplificationCommutant
public import LeanPool.VacuumBellSeparation.Bell.OscillatorWeylCommutant

/-!
# Cyclicity of the actual faithful oscillator purification

The closed Weyl orbit is reducing. The genuine oscillator irreducibility
theorem puts every amplified rank-one operator in the amplified Weyl double
commutant. Those rank-one operators recover every single-coordinate vector;
their actual finite-sum net converges to every Hilbert direct-sum vector.
No representation-equivalence or cyclicity hypothesis is used.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian ContinuousLinearMap
open scoped InnerProductSpace ENNReal Topology

variable {n : ℕ}

theorem amplifiedWeyl_closedOrbit_invariant (ι : Type*)
    (v : lp (fun _ : ι => MultiModeOscillatorSpace n) 2) (z : MultiModePhaseSpace n)
    {x : lp (fun _ : ι => MultiModeOscillatorSpace n) 2}
    (hx : x ∈ closedCyclicSpan (fun w => hilbertAmplification ι (multiOscillatorWeyl w) v)) :
    hilbertAmplification ι (multiOscillatorWeyl z) x ∈
      closedCyclicSpan (fun w => hilbertAmplification ι (multiOscillatorWeyl w) v) := by
  apply closedCyclicSpan_invariant _ _ ?_ hx
  intro w
  have he : hilbertAmplification ι (multiOscillatorWeyl z)
      (hilbertAmplification ι (multiOscillatorWeyl w) v) =
        weylPhase (id : MultiModePhaseSpace n → MultiModePhaseSpace n) z w •
          hilbertAmplification ι (multiOscillatorWeyl (z + w)) v := by
    apply lp.ext
    funext i
    simpa only [hilbertAmplification_apply, smul_apply, lp.coeFn_smul, Pi.smul_apply,
      mul_apply_eq_comp] using
        congrArg (fun A : MultiModeOscillatorSpace n →L[ℂ] MultiModeOscillatorSpace n => A (v i))
          (multiOscillatorWeyl_mul z w)
  rw [he]
  exact (closedCyclicSpan _).smul_mem _ (mem_closedCyclicSpan _ (z + w))

theorem amplifiedWeyl_closedOrbit_reducing (ι : Type*)
    (v : lp (fun _ : ι => MultiModeOscillatorSpace n) 2)
    (A : lp (fun _ : ι => MultiModeOscillatorSpace n) 2 →L[ℂ]
      lp (fun _ : ι => MultiModeOscillatorSpace n) 2)
    (hA : A ∈ hilbertAmplification ι '' Set.range (multiOscillatorWeyl (m := n))) :
    (∀ x ∈ closedCyclicSpan (fun w => hilbertAmplification ι (multiOscillatorWeyl w) v),
      A x ∈ closedCyclicSpan (fun w => hilbertAmplification ι (multiOscillatorWeyl w) v)) ∧
    (∀ x ∈ closedCyclicSpan (fun w => hilbertAmplification ι (multiOscillatorWeyl w) v),
      star A x ∈ closedCyclicSpan (fun w => hilbertAmplification ι (multiOscillatorWeyl w) v)) := by
  obtain ⟨_, ⟨z, rfl⟩, rfl⟩ := hA
  refine ⟨fun x hx => amplifiedWeyl_closedOrbit_invariant ι v z hx, ?_⟩
  intro x hx
  rw [← hilbertAmplification_star, ContinuousLinearMap.star_eq_adjoint,
    multiOscillatorWeyl_adjoint]
  exact amplifiedWeyl_closedOrbit_invariant ι v (-z) hx

/-- Every amplified bounded operator preserves the actual closed Weyl orbit. -/
theorem amplification_apply_mem_closedWeylOrbit (ι : Type*)
    (v : lp (fun _ : ι => MultiModeOscillatorSpace n) 2)
    (A : MultiModeOscillatorSpace n →L[ℂ] MultiModeOscillatorSpace n) :
    hilbertAmplification ι A v ∈
      closedCyclicSpan (fun w => hilbertAmplification ι (multiOscillatorWeyl w) v) := by
  let : CompleteSpace
      (closedCyclicSpan (fun w => hilbertAmplification ι (multiOscillatorWeyl w) v)) := by
    unfold closedCyclicSpan
    infer_instance
  have hv : v ∈ closedCyclicSpan
      (fun w => hilbertAmplification ι (multiOscillatorWeyl w) v) := by
    have h := mem_closedCyclicSpan
      (fun w => hilbertAmplification ι (multiOscillatorWeyl w) v) 0
    have h1 : hilbertAmplification ι (1 : MultiModeOscillatorSpace n →L[ℂ]
        MultiModeOscillatorSpace n) = 1 := (hilbertAmplificationHom ι).map_one
    simpa only [multiOscillatorWeyl_zero, h1, one_apply_eq_self] using h
  have hA : A ∈ generatedVNA (Set.range (multiOscillatorWeyl (m := n))) := by
    rw [generatedVNA_oscillatorWeyl_eq_top]
    trivial
  exact generatedVNA_invariant_of_reducing _ _ (amplifiedWeyl_closedOrbit_reducing ι v)
    (hilbertAmplification_mem_generatedVNA ι _ hA) hv

/-- The actual faithful density purification is cyclic for the amplified Weyl
family on the full infinite-dimensional direct sum, including zero modes. -/
theorem faithfulDensityPurification_weyl_cyclic
    {ρ : MultiModeOscillatorSpace n →L[ℂ] MultiModeOscillatorSpace n}
    (hρ : IsFaithfulDensity ρ) :
    closedCyclicSpan (fun z => hilbertAmplification (operatorEigenIndex ρ)
      (multiOscillatorWeyl z) (faithfulDensityPurification hρ)) = ⊤ := by
  classical
  let K := closedCyclicSpan (fun z => hilbertAmplification (operatorEigenIndex ρ)
    (multiOscillatorWeyl z) (faithfulDensityPurification hρ))
  have hs (i : operatorEigenIndex ρ) (x : MultiModeOscillatorSpace n) : lp.single 2 i x ∈ K := by
    have h := amplification_apply_mem_closedWeylOrbit (operatorEigenIndex ρ)
      (faithfulDensityPurification hρ)
      (InnerProductSpace.rankOne ℂ x (positiveTraceClassEigenbasis hρ.isPositiveTraceClass i))
    rw [amplification_rankOne_faithfulDensityPurification] at h
    have hc : (Real.sqrt i.1.re : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (faithfulDensity_eigenvalue_pos hρ i)).ne'
    have hi := K.smul_mem ((Real.sqrt i.1.re : ℂ)⁻¹) h
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hi
  apply top_unique
  intro x hx
  exact (Submodule.span ℂ (Set.range (fun z => hilbertAmplification (operatorEigenIndex ρ)
    (multiOscillatorWeyl z) (faithfulDensityPurification
      hρ)))).isClosed_topologicalClosure.mem_of_tendsto
      (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x)
      (Filter.Eventually.of_forall fun s => K.sum_mem fun i hi => hs i (x i))

end VacuumBellSeparation
