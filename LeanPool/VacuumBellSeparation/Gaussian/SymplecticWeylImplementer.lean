/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.WeylGaussianProjection

/-!
# Constructed unitary implementation of finite real symplectic relabelings

Preservation of the actual imaginary inner form implies bijectivity in
finite dimension. The Gaussian projection supplies a concrete normalized
vacuum. Its relabeled Weyl orbit has the actual coherent kernel and dense
span. The RKHS quotient and completion therefore construct a surjective
complex linear isometry, and its coherent action proves the Weyl
intertwining identity. No CCR uniqueness or implementer is a premise.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ComplexConjugate

variable {m : ℕ}

theorem PreservesWeylForm.injective
    {T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m} (hT : PreservesWeylForm T) :
    Function.Injective T := by
  have hker (x : MultiModePhaseSpace m) (hx : T x = 0) : x = 0 := by
    have hi := hT x (Complex.I • x)
    rw [hx, inner_zero_left, Complex.zero_im, inner_smul_right,
      inner_self_eq_norm_sq_to_K] at hi
    have hn : ‖x‖ ^ 2 = 0 := by
      simpa only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.mul_im,
        Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add] using hi.symm
    exact norm_eq_zero.mp (eq_zero_of_pow_eq_zero hn)
  intro x y hxy
  apply sub_eq_zero.mp
  apply hker
  rw [map_sub, hxy, sub_self]

theorem PreservesWeylForm.surjective
    {T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m} (hT : PreservesWeylForm T) :
    Function.Surjective T :=
  LinearMap.injective_iff_surjective.mp hT.injective

/-- Relabeled coherent vector obtained from `multiOscillatorWeyl`. -/
def relabeledCoherentVector
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m) (z : MultiModePhaseSpace m) :
    MultiModeOscillatorSpace m := multiOscillatorWeyl (T z) (relabeledGaussianVacuum T)

theorem weylPhase_vacuumWeight_eq_kernel (z w : MultiModePhaseSpace m) :
    weylPhase (id : MultiModePhaseSpace m → MultiModePhaseSpace m) (-z) w *
        phaseSpaceVacuumWeight (-z + w) =
      weylKernel (id : MultiModePhaseSpace m → MultiModePhaseSpace m) z w := by
  simp only [weylPhase, phaseSpaceVacuumWeight, weylKernel, id_eq,
    ← Complex.exp_add, norm_add_sq (𝕜 := ℂ), norm_neg, inner_neg_left]
  congr 1
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im,
      Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      RCLike.re_to_complex, map_neg] <;> ring

theorem inner_relabeledCoherentVector
    {T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m} (hT : PreservesWeylForm T)
    (z w : MultiModePhaseSpace m) :
    inner ℂ (relabeledCoherentVector T z) (relabeledCoherentVector T w) =
      weylKernel (id : MultiModePhaseSpace m → MultiModePhaseSpace m) z w := by
  rw [relabeledCoherentVector, relabeledCoherentVector,
    ← adjoint_inner_right, multiOscillatorWeyl_adjoint, ← map_neg,
    ← mul_apply_eq_comp, multiOscillatorWeyl_mul, weylPhase_relabel hT,
    ← map_add, smul_apply, inner_smul_right,
    relabeledGaussianVacuum_characteristic hT, weylPhase_vacuumWeight_eq_kernel]

theorem relabeledCoherentVector_dense_span
    {T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m} (hT : PreservesWeylForm T) :
    (Submodule.span ℂ (Set.range (relabeledCoherentVector T))).topologicalClosure = ⊤ := by
  have hv : relabeledGaussianVacuum T ≠ 0 := by
    intro h
    have hn := norm_relabeledGaussianVacuum T
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have hr : Set.range (relabeledCoherentVector T) =
      Set.range (fun z : MultiModePhaseSpace m => multiOscillatorWeyl z
        (relabeledGaussianVacuum T)) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨T z, rfl⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨w, hw⟩ := hT.surjective z
      exact ⟨w, by simp only [relabeledCoherentVector, hw]⟩
  rw [hr]
  exact multiOscillatorWeyl_orbit_dense_span hv

/-- Linear map for the symplectic coherent realization₀, of type `MultiModePhaseSpace m →
MultiModePhaseSpace m)) →ₗ[ℂ] MultiModeOscillatorSpace m`. -/
def symplecticCoherentRealization₀
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m) :
    RKHS.H₀ (weylRKHSKernel (id : MultiModePhaseSpace m → MultiModePhaseSpace m)) →ₗ[ℂ]
      MultiModeOscillatorSpace m :=
  Finsupp.linearCombination ℂ
    (fun p : MultiModePhaseSpace m × ℂ => p.2 • relabeledCoherentVector T p.1)

@[simp] theorem symplecticCoherentRealization₀_single
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m)
    (z : MultiModePhaseSpace m) (v a : ℂ) :
    symplecticCoherentRealization₀ T (Finsupp.single (z, v) a) =
      a • (v • relabeledCoherentVector T z) := by simp [symplecticCoherentRealization₀]

theorem inner_symplecticCoherentRealization₀
    {T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m} (hT : PreservesWeylForm T)
    (f g : RKHS.H₀ (weylRKHSKernel (id : MultiModePhaseSpace m → MultiModePhaseSpace m))) :
    inner ℂ (symplecticCoherentRealization₀ T f) (symplecticCoherentRealization₀ T g) =
      inner ℂ f g := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, inner_zero_left]
  | add f₁ f₂ h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]
  | single p a =>
    induction g using Finsupp.induction_linear with
    | zero => simp only [map_zero, inner_zero_right]
    | add g₁ g₂ h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]
    | single q b =>
      obtain ⟨z, v⟩ := p
      obtain ⟨w, u⟩ := q
      rw [symplecticCoherentRealization₀_single, symplecticCoherentRealization₀_single,
        inner_H₀_single]
      simp only [inner_smul_left, inner_smul_right, inner_relabeledCoherentVector hT]
      ring

/-- Linear isometry for the symplectic coherent realization iso₀, of type `MultiModePhaseSpace m →
MultiModePhaseSpace m)) →ₗᵢ[ℂ] MultiModeOscillatorSpace m`. -/
def symplecticCoherentRealizationIso₀
    {T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m} (hT : PreservesWeylForm T) :
    RKHS.H₀ (weylRKHSKernel (id : MultiModePhaseSpace m → MultiModePhaseSpace m)) →ₗᵢ[ℂ]
      MultiModeOscillatorSpace m :=
  (symplecticCoherentRealization₀ T).isometryOfInner (inner_symplecticCoherentRealization₀ hT)

/-- Linear isometry for the symplectic coherent realization, of type `MultiModePhaseSpace m →
MultiModePhaseSpace m) →ₗᵢ[ℂ] MultiModeOscillatorSpace m`. -/
def symplecticCoherentRealization
    {T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m} (hT : PreservesWeylForm T) :
    WeylSpace (id : MultiModePhaseSpace m → MultiModePhaseSpace m) →ₗᵢ[ℂ]
      MultiModeOscillatorSpace m := (symplecticCoherentRealizationIso₀ hT).fromCompletion

theorem symplecticCoherentRealization_weylVec
    {T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m} (hT : PreservesWeylForm T)
    (z : MultiModePhaseSpace m) :
    symplecticCoherentRealization hT (weylVec (id : MultiModePhaseSpace m
      → MultiModePhaseSpace m) z) =
      relabeledCoherentVector T z := by
  rw [weylVec_def, symplecticCoherentRealization, LinearIsometry.fromCompletion_apply_coe]
  change symplecticCoherentRealization₀ T (Finsupp.single (z, 1) 1) = relabeledCoherentVector T z
  simp

theorem symplecticCoherentRealization_surjective
    {T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m} (hT : PreservesWeylForm T) :
    Function.Surjective (symplecticCoherentRealization hT) := by
  have hclosed : IsClosed (Set.range (symplecticCoherentRealization hT)) :=
    (symplecticCoherentRealization hT).isometry.isClosedEmbedding.isClosed_range
  have hspan : Submodule.span ℂ (Set.range (relabeledCoherentVector T)) ≤
      (symplecticCoherentRealization hT).toLinearMap.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    exact ⟨weylVec (id : MultiModePhaseSpace m → MultiModePhaseSpace m) z,
      symplecticCoherentRealization_weylVec hT z⟩
  have hclosure := (Submodule.span ℂ (Set.range (relabeledCoherentVector
    T))).topologicalClosure_minimal
    hspan hclosed
  rw [relabeledCoherentVector_dense_span hT] at hclosure
  exact LinearMap.range_eq_top.mp (top_unique hclosure)

/-- A constructed unitary implementing an arbitrary finite real
symplectic label map. Its phase is fixed by the normalized projected vacuum. -/
def symplecticWeylImplementer
    {T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m} (hT : PreservesWeylForm T) :
    MultiModeOscillatorSpace m ≃ₗᵢ[ℂ] MultiModeOscillatorSpace m :=
  (multiWeylCoherentEquiv m).symm.trans
    (LinearIsometryEquiv.ofSurjective (symplecticCoherentRealization hT)
      (symplecticCoherentRealization_surjective hT))

theorem symplecticWeylImplementer_coherent
    {T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m} (hT : PreservesWeylForm T)
    (z : MultiModePhaseSpace m) :
    symplecticWeylImplementer hT (multiCoherentVector z) = relabeledCoherentVector T z := by
  rw [← multiWeylCoherentEquiv_weylVec z]
  change symplecticCoherentRealization hT
    ((multiWeylCoherentEquiv m).symm
      (multiWeylCoherentEquiv m (weylVec (id : MultiModePhaseSpace m
        → MultiModePhaseSpace m) z))) = _
  rw [LinearIsometryEquiv.symm_apply_apply, symplecticCoherentRealization_weylVec]

theorem symplecticWeylImplementer_weyl_apply
    {T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m} (hT : PreservesWeylForm T)
    (z : MultiModePhaseSpace m) (x : MultiModeOscillatorSpace m) :
    symplecticWeylImplementer hT (multiOscillatorWeyl z x) =
      multiOscillatorWeyl (T z) (symplecticWeylImplementer hT x) := by
  let U := (symplecticWeylImplementer hT).toLinearIsometry.toContinuousLinearMap
  have he : U.comp (multiOscillatorWeyl z) = (multiOscillatorWeyl (T z)).comp U := by
    apply continuousLinearMap_eq_of_dense_span (multiCoherentVector (m := m))
      (multiCoherentVector_dense_span m)
    intro w
    change symplecticWeylImplementer hT (multiOscillatorWeyl z (multiCoherentVector w)) =
      multiOscillatorWeyl (T z) (symplecticWeylImplementer hT (multiCoherentVector w))
    rw [multiOscillatorWeyl_coherentVector, map_smul, symplecticWeylImplementer_coherent,
      symplecticWeylImplementer_coherent, relabeledCoherentVector, relabeledCoherentVector,
      ← mul_apply_eq_comp, multiOscillatorWeyl_mul, weylPhase_relabel hT,
      ← map_add, smul_apply]
  exact congrArg (fun A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m => A x) he

/-- The actual conjugation identity on the fixed full oscillator Hilbert
space, with no implementer supplied as an assumption. -/
theorem symplecticWeylImplementer_conj_weyl
    {T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m} (hT : PreservesWeylForm T)
    (z : MultiModePhaseSpace m) :
    (symplecticWeylImplementer hT).conjStarAlgEquiv (multiOscillatorWeyl z) =
      multiOscillatorWeyl (T z) := by
  ext x
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    symplecticWeylImplementer_weyl_apply, LinearIsometryEquiv.apply_symm_apply]

end VacuumBellSeparation.Gaussian
