/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.GaugeFamilyTransfer

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.JointAEEqTransfer

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set

noncomputable section

/-- Finite affine Dirichlet gradients depend only on the a.e. coefficient
family. -/
theorem finiteAffineSolution_grad_ae_of_aeeq
    {d : ℕ} [NeZero d]
    {a b : Book.Ch02.TriadicCoeffFamily d}
    (hab : Book.Ch02.TriadicCoeffFamily.AEEq a b)
    (m : ℤ) (e : Vec d) :
    (finiteAffineSolution a m e).toH1.grad
      =ᵐ[volumeMeasureOn
        (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))]
      (finiteAffineSolution b m e).toH1.grad := by
  have hb := finiteAffineSolution_isAffineDirichletSolution b m e
  have hbAsA : IsAffineDirichletSolution
      (a.coeffOn (originCube d m)).toCoeffField
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)) e
      (finiteAffineSolution b m e).toH1 := by
    exact ⟨IsAHarmonicGradient.of_ae_eq_coeff
      (hab (originCube d m)).symm hb.1, hb.2⟩
  exact finiteAffineSolution_grad_ae_eq_of_isAffineDirichletSolution
    a m e (finiteAffineSolution b m e).toH1 hbAsA

/-- The zero-trace correction gradients inherit the preceding a.e.
invariance after cancelling the common affine boundary slope. -/
theorem finiteAffineCorrection_grad_ae_of_aeeq
    {d : ℕ} [NeZero d]
    {a b : Book.Ch02.TriadicCoeffFamily d}
    (hab : Book.Ch02.TriadicCoeffFamily.AEEq a b)
    (m : ℤ) (e : Vec d) :
    (finiteAffineCorrection a m e).toH1Function.grad
      =ᵐ[volumeMeasureOn
        (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))]
      (finiteAffineCorrection b m e).toH1Function.grad := by
  filter_upwards [finiteAffineSolution_grad_ae_of_aeeq hab m e]
    with x hx
  have hcancel :
      e + (finiteAffineCorrection a m e).toH1Function.grad x =
        e + (finiteAffineCorrection b m e).toH1Function.grad x := by
    simpa only [finiteAffineSolution_toH1, H1Function.add_grad,
      finiteAffineBoundaryH1_grad] using hx
  exact add_left_cancel hcancel

/-- The Hilbert-vector class of a finite correction gradient is a.e.
invariant in the coefficient family. -/
theorem finiteAffineCorrectionLocalSequence_gradient_eq_of_aeeq
    {d : ℕ} [NeZero d]
    {a b : Book.Ch02.TriadicCoeffFamily d}
    (hab : Book.Ch02.TriadicCoeffFamily.AEEq a b)
    (e : Vec d) (q : ℕ) :
    (finiteAffineCorrectionLocalSequence a e q).gradToHilbertVectorL2 =
      (finiteAffineCorrectionLocalSequence b e q).gradToHilbertVectorL2 := by
  apply Lp.ext
  filter_upwards [
    (finiteAffineCorrectionLocalSequence a e q).coeFn_gradToHilbertVectorL2,
    (finiteAffineCorrectionLocalSequence b e q).coeFn_gradToHilbertVectorL2,
    finiteAffineCorrection_grad_ae_of_aeeq hab (q : ℤ) e]
      with x ha hb hgrad
  rw [ha, hb]
  exact congrArg HilbertVec.ofVec hgrad

/-- The gradient component of every normalized local pair is invariant under
a.e. replacement of the coefficient family. -/
theorem normalizedLocalPair_gradient_eq_of_aeeq
    {d : ℕ} [NeZero d]
    {a b : Book.Ch02.TriadicCoeffFamily d}
    (hab : Book.Ch02.TriadicCoeffFamily.AEEq a b)
    (e : Vec d) (n k : ℕ) :
    (normalizedLocalPair (finiteAffineCorrectionLocalSequence a e) n k).2 =
      (normalizedLocalPair (finiteAffineCorrectionLocalSequence b e) n k).2 := by
  rw [normalizedLocalPair_gradient_eq, normalizedLocalPair_gradient_eq,
    finiteAffineCorrectionLocalSequence_gradient_eq_of_aeeq hab]

/-- Two joint finite-corrector limits for a.e.-equal families have identical
projective gradient components.  No equality of value representatives or of
the bundled families is asserted. -/
theorem jointGradientComponent_eq_of_aeeq
    {d : ℕ} [NeZero d]
    {a b : Book.Ch02.TriadicCoeffFamily d}
    (hab : Book.Ch02.TriadicCoeffFamily.AEEq a b)
    (PhiA PhiB : Vec d → NormalizedLocalH1Carrier d)
    (hA : IsFiniteAffineCorrectionJointLocalEquation a PhiA)
    (hB : IsFiniteAffineCorrectionJointLocalEquation b PhiB)
    (e : Vec d) (n : ℕ) :
    (PhiA e).gradientComponent n = (PhiB e).gradientComponent n := by
  have hlimA := (hA.1 e n).snd_nhds
  have hlimB := (hB.1 e n).snd_nhds
  have hseq :
      (fun k ↦
        (normalizedLocalPair
          (finiteAffineCorrectionLocalSequence a e) n k).2) =
      (fun k ↦
        (normalizedLocalPair
          (finiteAffineCorrectionLocalSequence b e) n k).2) := by
    funext k
    exact normalizedLocalPair_gradient_eq_of_aeeq hab e n k
  rw [hseq] at hlimA
  exact tendsto_nhds_unique hlimA hlimB

private theorem ae_eq_volume_of_localGradientCubes
    {d : ℕ} {E : Type*} {f g : Vec d → E}
    (h : ∀ q : ℕ, f =ᵐ[volumeMeasureOn (localGradientCube d q)] g) :
    f =ᵐ[volume] g := by
  have hall : ∀ᵐ x ∂volume, ∀ q : ℕ,
      x ∈ localGradientCube d q → f x = g x := by
    apply ae_all_iff.2
    intro q
    exact (ae_restrict_iff'
      (isOpen_openCubeSet (originCube d (q : ℤ))).measurableSet).mp (h q)
  filter_upwards [hall] with x hx
  have hxUnion : x ∈ ⋃ q, localGradientCube d q := by
    rw [iUnion_localGradientCube]
    trivial
  obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hxUnion
  exact hx q hxq

/-- Canonical global gradient representatives of a.e.-equal coefficient
families agree almost everywhere. -/
theorem jointGlobalGradient_ae_of_aeeq
    {d : ℕ} [NeZero d]
    {a b : Book.Ch02.TriadicCoeffFamily d}
    (hab : Book.Ch02.TriadicCoeffFamily.AEEq a b)
    (PhiA PhiB : Vec d → NormalizedLocalH1Carrier d)
    (hA : IsFiniteAffineCorrectionJointLocalEquation a PhiA)
    (hB : IsFiniteAffineCorrectionJointLocalEquation b PhiB)
    (e : Vec d) :
    (PhiA e).globalGradientRepresentative =ᵐ[volume]
      (PhiB e).globalGradientRepresentative := by
  apply ae_eq_volume_of_localGradientCubes
  intro n
  have hcomp := jointGradientComponent_eq_of_aeeq
    hab PhiA PhiB hA hB e n
  exact ((PhiA e).globalGradientRepresentative_ae_eq_component n).trans
    (by simpa only [hcomp] using
      ((PhiB e).globalGradientRepresentative_ae_eq_component n).symm)

end

end HighContrast
end HCPolySupport
