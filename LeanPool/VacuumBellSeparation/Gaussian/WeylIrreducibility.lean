/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.WeylCoherentInversion

/-!
# Irreducibility of the actual finite-mode oscillator Weyl representation

The actual Bochner Gaussian orbit integral is the vacuum rank-one
projection. A nonzero closed invariant subspace therefore contains the
vacuum and all coherent vectors. This proves irreducibility and cyclicity
of every nonzero vector without assuming CCR uniqueness.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory ContinuousLinearMap InnerProductSpace
open scoped ComplexConjugate

theorem integral_mem_closed_complex_submodule {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (K : Submodule ℂ E) (hK : IsClosed (K : Set E)) {μ : Measure X} {f : X → E}
    (hf : Integrable f μ) (hmem : ∀ᵐ x ∂μ, f x ∈ K) : (∫ x, f x ∂μ) ∈ K := by
  rw [← hK.submodule_topologicalClosure_eq, ← K.orthogonal_orthogonal_eq_closure]
  apply (Kᗮ.mem_orthogonal _).mpr
  intro y hy
  rw [← integral_inner hf]
  apply integral_eq_zero_of_ae
  exact hmem.mono fun x hx => K.inner_left_of_mem_orthogonal hx hy

theorem exists_inner_multiCoherentVector_ne_zero {m : ℕ}
    {x : MultiModeOscillatorSpace m} (hx : x ≠ 0) :
    ∃ z : MultiModePhaseSpace m, inner ℂ (multiCoherentVector z) x ≠ 0 := by
  by_contra h
  push Not at h
  apply hx
  apply (innerSL_inj (𝕜 := ℂ)).mp
  apply continuousLinearMap_eq_of_dense_span (multiCoherentVector (m := m))
    (multiCoherentVector_dense_span m)
  intro z
  simpa only [innerSL_apply_apply, inner_zero_left, inner_conj_symm, map_zero,
    zero_apply] using
    congrArg conj (h z)

theorem weylVacuumIntegral_mem_of_invariant {m : ℕ}
    (K : Submodule ℂ (MultiModeOscillatorSpace m)) (hK : IsClosed (K : Set
      (MultiModeOscillatorSpace m)))
    (hW : ∀ z : MultiModePhaseSpace m, ∀ x ∈ K, multiOscillatorWeyl z x ∈ K)
    {x : MultiModeOscillatorSpace m} (hx : x ∈ K) : weylVacuumIntegral m x ∈ K := by
  rw [weylVacuumIntegral_apply]
  apply integral_mem_closed_complex_submodule K hK (integrable_weylVacuumOrbit x)
  exact Filter.Eventually.of_forall fun z => K.smul_mem _ (hW _ _ hx)

/-- Every nonzero closed subspace invariant under all actual oscillator
Weyl operators is the full Hilbert space. -/
theorem closed_weyl_invariant_eq_top {m : ℕ}
    (K : Submodule ℂ (MultiModeOscillatorSpace m)) (hK : IsClosed (K : Set
      (MultiModeOscillatorSpace m)))
    (hW : ∀ z : MultiModePhaseSpace m, ∀ x ∈ K, multiOscillatorWeyl z x ∈ K)
    {x : MultiModeOscillatorSpace m} (hx : x ∈ K) (hx₀ : x ≠ 0) : K = ⊤ := by
  obtain ⟨z, hz⟩ := exists_inner_multiCoherentVector_ne_zero hx₀
  let v := multiExponentialVector (0 : Fin m → ℂ)
  let y := multiOscillatorWeyl (-z) x
  have hy : y ∈ K := hW (-z) x hx
  have hinner : inner ℂ v y = inner ℂ (multiCoherentVector z) x := by
    dsimp only [y]
    rw [← multiOscillatorWeyl_adjoint z, adjoint_inner_right]
    dsimp only [v]
    rw [multiOscillatorWeyl_exponential_zero]
  have hp : (Real.pi : ℂ) ^ m ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hc : (Real.pi : ℂ) ^ m * inner ℂ v y ≠ 0 :=
    mul_ne_zero hp (by rwa [hinner])
  have havg := weylVacuumIntegral_mem_of_invariant K hK hW hy
  rw [weylVacuumIntegral_eq_rankOne, smul_apply, rankOne_apply, smul_smul] at havg
  change ((Real.pi : ℂ) ^ m * inner ℂ v y) • v ∈ K at havg
  have hv : v ∈ K := by
    have h := K.smul_mem (((Real.pi : ℂ) ^ m * inner ℂ v y)⁻¹) havg
    simpa only [inv_smul_smul₀ hc] using h
  have hspan : Submodule.span ℂ (Set.range (multiCoherentVector (m := m))) ≤ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    rw [← multiOscillatorWeyl_exponential_zero w]
    exact hW w v hv
  have hclosure := (Submodule.span ℂ (Set.range (multiCoherentVector
    (m := m)))).topologicalClosure_minimal
    hspan hK
  rw [multiCoherentVector_dense_span] at hclosure
  exact top_unique hclosure

/-- Every nonzero vector is genuinely cyclic for the full finite-mode
oscillator Weyl family. This supplies surjectivity for later constructed
intertwiners. -/
theorem multiOscillatorWeyl_orbit_dense_span {m : ℕ}
    {x : MultiModeOscillatorSpace m} (hx : x ≠ 0) :
    (Submodule.span ℂ (Set.range (fun z : MultiModePhaseSpace m =>
      multiOscillatorWeyl z x))).topologicalClosure = ⊤ := by
  let K := Submodule.span ℂ (Set.range (fun z : MultiModePhaseSpace m => multiOscillatorWeyl z x))
  have hW (z : MultiModePhaseSpace m) : ∀ y ∈ K, multiOscillatorWeyl z y ∈ K := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      rcases hy with ⟨w, rfl⟩
      rw [← mul_apply_eq_comp, multiOscillatorWeyl_mul, smul_apply]
      exact K.smul_mem _ (Submodule.subset_span ⟨z + w, rfl⟩)
    | zero => simpa only [map_zero] using K.zero_mem
    | add a b ha hb iha ihb => simpa only [map_add] using K.add_mem iha ihb
    | smul a y hy ih => simpa only [map_smul] using K.smul_mem a ih
  have hWclosure (z : MultiModePhaseSpace m) :
      ∀ y ∈ K.topologicalClosure, multiOscillatorWeyl z y ∈ K.topologicalClosure := by
    have hmap : K.map (multiOscillatorWeyl z).toLinearMap ≤ K := by
      rintro _ ⟨y, hy, rfl⟩
      exact hW z y hy
    have hcl := (K.topologicalClosure_map (multiOscillatorWeyl z)).trans
      (Submodule.topologicalClosure_mono hmap)
    intro y hy
    exact hcl ⟨y, hy, rfl⟩
  have hxK : x ∈ K := by
    have h : multiOscillatorWeyl (0 : MultiModePhaseSpace m) x ∈ K :=
      Submodule.subset_span ⟨0, rfl⟩
    simpa only [multiOscillatorWeyl_zero, one_apply_eq_self] using h
  exact closed_weyl_invariant_eq_top K.topologicalClosure K.isClosed_topologicalClosure
    hWclosure (K.le_topologicalClosure hxK) hx

end VacuumBellSeparation.Gaussian
