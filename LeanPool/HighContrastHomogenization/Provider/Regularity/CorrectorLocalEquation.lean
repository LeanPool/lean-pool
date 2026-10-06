/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorJointLimit
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteCubeSolutionRestriction
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.Representatives
public import LeanPool.HighContrastHomogenization.Support.PDE.HarmonicHilbert

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorLocalEquation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Local equations for the joint corrector limit

On each fixed centered cube, the finite affine solutions form a sequence in
the closed Hilbert space of coefficient-harmonic gradients.  The normalized
local limit therefore has a coefficient-harmonic affine-plus-corrector
representative on that cube.  The Cauchy premise remains explicit here.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

/-- The local affine-plus-corrector `H¹` representative selected by the joint
projective limit. -/
@[expose]
noncomputable def finiteAffineCorrectionJointLocalH1 {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    (e : Vec d) (n : ℕ) : H1Function (localGradientCube d n) :=
  (show H1Function (localGradientCube d n) from by
    simp only [localGradientCube]
    exact finiteAffineBoundaryH1 (n : ℤ) e) +
    (finiteAffineCorrectionJointLocalLimit a hCauchy e).localH1Function n

/-- The gradient class of the local full solution is the constant affine
gradient plus the stored corrector-gradient component. -/
@[simp] theorem finiteAffineCorrectionJointLocalH1_gradToHilbertVectorL2
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    (e : Vec d) (n : ℕ) :
    (finiteAffineCorrectionJointLocalH1 a hCauchy e n).gradToHilbertVectorL2 =
      (show LocalGradientL2 d n from by
        simp only [LocalGradientL2, localGradientCube]
        exact (finiteAffineBoundaryH1 (n : ℤ) e).gradToHilbertVectorL2) +
        (finiteAffineCorrectionJointLocalLimit a hCauchy e).gradientComponent n := by
  rw [finiteAffineCorrectionJointLocalH1,
    H1Function.gradToHilbertVectorL2_add,
    NormalizedLocalH1Carrier.localH1Function_gradToHilbertVectorL2]
  rfl

@[expose]
public noncomputable def finiteAffineNormalizedLocalFullH1
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (n k : ℕ) : H1Function (localGradientCube d n) :=
  (show H1Function (localGradientCube d n) from by
    simp only [localGradientCube]
    exact finiteAffineBoundaryH1 (n : ℤ) e) +
    normalizedLocalH1 (finiteAffineCorrectionLocalSequence a e) n k

private theorem finiteAffineNormalizedLocalFullH1_grad_eq
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (n k : ℕ) :
    (finiteAffineNormalizedLocalFullH1 a e n k).grad =
      (finiteCubeSolutionRestriction a
        (show (n : ℤ) ≤ ((n + k : ℕ) : ℤ) by omega)
        (finiteAffineCubeSolution a ((n + k : ℕ) : ℤ) e)).toH1.grad := by
  funext x
  rw [finiteCubeSolutionRestriction_grad]
  change (finiteAffineNormalizedLocalFullH1 a e n k).grad x =
    (finiteAffineSolution a ((n + k : ℕ) : ℤ) e).toH1.grad x
  rw [finiteAffineSolution_toH1]
  change
    (finiteAffineBoundaryH1 (n : ℤ) e).grad x +
        (normalizedLocalH1
          (finiteAffineCorrectionLocalSequence a e) n k).grad x =
      (finiteAffineBoundaryH1 ((n + k : ℕ) : ℤ) e).grad x +
        (finiteAffineCorrection a
          ((n + k : ℕ) : ℤ) e).toH1Function.grad x
  rw [finiteAffineBoundaryH1_grad, finiteAffineBoundaryH1_grad]
  change e +
      (normalizeOnUnitCube
        (finiteAffineCorrectionLocalSequence a e (n + k))).grad x =
    e + (finiteAffineCorrectionLocalSequence a e (n + k)).grad x
  rw [normalizeOnUnitCube_grad]

@[expose]
public noncomputable def finiteAffineNormalizedLocalCubeSolution
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (n k : ℕ) :
    Book.Ch03.CubeSolution (originCube d (n : ℤ)) a where
  toH1 := finiteAffineNormalizedLocalFullH1 a e n k
  isHarmonic := by
    rw [finiteAffineNormalizedLocalFullH1_grad_eq]
    exact
      (finiteCubeSolutionRestriction a
        (show (n : ℤ) ≤ ((n + k : ℕ) : ℤ) by omega)
        (finiteAffineCubeSolution a ((n + k : ℕ) : ℤ) e)).isHarmonic

private theorem finiteAffineNormalizedLocalFullH1_tendsto
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    (e : Vec d) (n : ℕ) :
    _root_.Filter.Tendsto
      (fun k =>
        (finiteAffineNormalizedLocalFullH1 a e n k).gradToHilbertVectorL2)
      _root_.Filter.atTop
      (nhds
        (finiteAffineCorrectionJointLocalH1 a hCauchy e n).gradToHilbertVectorL2) := by
  let g0 : LocalGradientL2 d n :=
    (show H1Function (localGradientCube d n) from by
      simp only [localGradientCube]
      exact finiteAffineBoundaryH1 (n : ℤ) e).gradToHilbertVectorL2
  have hlimit :
      _root_.Filter.Tendsto
        (fun k =>
          (normalizedLocalPair
            (finiteAffineCorrectionLocalSequence a e) n k).2)
        _root_.Filter.atTop
        (nhds
          ((finiteAffineCorrectionJointLocalLimit a hCauchy e).gradientComponent n)) :=
    (finiteAffineCorrectionJointLocalLimit_isLimit a hCauchy e n).snd_nhds
  have hsum :
      _root_.Filter.Tendsto
        (fun k =>
          g0 +
            (normalizedLocalPair
              (finiteAffineCorrectionLocalSequence a e) n k).2)
        _root_.Filter.atTop
        (nhds
          (g0 +
            (finiteAffineCorrectionJointLocalLimit a hCauchy e).gradientComponent n)) :=
    tendsto_const_nhds.add hlimit
  have hsource :
      (fun k =>
        (finiteAffineNormalizedLocalFullH1 a e n k).gradToHilbertVectorL2) =
        fun k =>
          g0 +
            (normalizedLocalPair
              (finiteAffineCorrectionLocalSequence a e) n k).2 := by
    funext k
    rw [finiteAffineNormalizedLocalFullH1,
      H1Function.gradToHilbertVectorL2_add]
    rfl
  have htarget :
      (finiteAffineCorrectionJointLocalH1 a hCauchy e n).gradToHilbertVectorL2 =
        g0 +
          (finiteAffineCorrectionJointLocalLimit a hCauchy e).gradientComponent n := by
    rw [finiteAffineCorrectionJointLocalH1_gradToHilbertVectorL2]
    rfl
  rw [hsource, htarget]
  exact hsum

private theorem isAHarmonicGradient_of_grad_mem_closedSubmodule
    {d : ℕ} {U : Set (Vec d)} {b : CoeffField d} {lam Lam : ℝ}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U b) (u : H1Function U)
    (hmem : u.gradToHilbertVectorL2 ∈
      AHarmonicGradientHilbert.closedSubmodule
        (PotentialSolenoidalL2Data.ofSubmoduleClosures U) hEll) :
    IsAHarmonicGradient b U u.grad := by
  let z : AHarmonicGradientHilbert.Space
      (PotentialSolenoidalL2Data.ofSubmoduleClosures U) hEll :=
    ⟨u.gradToHilbertVectorL2, hmem⟩
  have hvectorL2 :
      AHarmonicGradientHilbert.vectorField z = u.gradToVectorL2 := by
    simpa [H1Function.gradToHilbertVectorL2,
      H1Function.gradToVectorL2] using!
        (hilbertVectorL2ToVectorL2_toHilbertVectorL2
          (U := U) u.grad_memVectorL2)
  have hvector :
      AHarmonicGradientHilbert.vectorField z
        =ᵐ[volumeMeasureOn U] u.grad := by
    rw [hvectorL2]
    exact u.coeFn_gradToVectorL2
  refine ⟨u.isPotentialOn, ?_⟩
  have hsol :=
    AHarmonicGradientHilbert.isSolenoidalOn_matVecMul_vectorField z
  intro phi
  calc
    ∫ x in U, vecDot (matVecMul (b x) (u.grad x))
          (phi.toH1Function.grad x) ∂volume =
        ∫ x in U,
          vecDot
            (matVecMul (b x) (AHarmonicGradientHilbert.vectorField z x))
            (phi.toH1Function.grad x) ∂volume := by
              refine integral_congr_ae ?_
              exact hvector.symm.mono fun x hx =>
                congrArg
                  (fun g : Vec d =>
                    vecDot (matVecMul (b x) g) (phi.toH1Function.grad x)) hx
    _ = 0 := hsol phi

/-- On every fixed cube, the local affine-plus-corrector representative has
the public compatible coefficient as its harmonic coefficient. -/
theorem finiteAffineCorrectionJointLocalH1_isHarmonic
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    (e : Vec d) (n : ℕ) :
    IsAHarmonicGradient
      (a.coeffOn (originCube d (n : ℤ))).toCoeffField
      (localGradientCube d n)
      (finiteAffineCorrectionJointLocalH1 a hCauchy e n).grad := by
  let U : Book.Ch02.Domain d :=
    Book.Ch02.cubeDomain (originCube d (n : ℤ))
  let b : Book.Ch02.CoeffOn U :=
    Internal.Ch02.BookCh02.pointwiseCoeffOn U
      (a.coeffOn (originCube d (n : ℤ)))
  let hEll :=
    Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn U
      (a.coeffOn (originCube d (n : ℤ)))
  let M : PotentialSolenoidalL2Data (localGradientCube d n) :=
    PotentialSolenoidalL2Data.ofSubmoduleClosures (localGradientCube d n)
  have hmemApprox : ∀ k : ℕ,
      (finiteAffineNormalizedLocalFullH1 a e n k).gradToHilbertVectorL2 ∈
        AHarmonicGradientHilbert.closedSubmodule M hEll := by
    intro k
    let uPublic := finiteAffineNormalizedLocalCubeSolution a e n k
    have hAE : Book.Ch02.CoeffOn.AEEq b
        (a.coeffOn (originCube d (n : ℤ))) := by
      simpa only [U, b] using
        Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq U
          (a.coeffOn (originCube d (n : ℤ)))
    let uPointwise : Book.Ch02.Solution U b :=
      Book.Ch02.Solution.ofAEEq hAE.symm uPublic
    let z := AHarmonicGradientHilbert.ofAHarmonicFunction M hEll uPointwise
    exact z.2
  have hmem :
      (finiteAffineCorrectionJointLocalH1 a hCauchy e n).gradToHilbertVectorL2 ∈
        AHarmonicGradientHilbert.closedSubmodule M hEll :=
    (AHarmonicGradientHilbert.closedSubmodule M hEll).isClosed.mem_of_tendsto
      (finiteAffineNormalizedLocalFullH1_tendsto a hCauchy e n)
      (_root_.Filter.Eventually.of_forall hmemApprox)
  have hpointwise :
      IsAHarmonicGradient b.toCoeffField (localGradientCube d n)
        (finiteAffineCorrectionJointLocalH1 a hCauchy e n).grad :=
    isAHarmonicGradient_of_grad_mem_closedSubmodule hEll _ hmem
  have hAE :
      b.toCoeffField =ᵐ[volumeMeasureOn (localGradientCube d n)]
        (a.coeffOn (originCube d (n : ℤ))).toCoeffField := by
    simpa only [U, b, localGradientCube, Book.Ch02.cubeDomain_coe] using!
      Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq U
        (a.coeffOn (originCube d (n : ℤ)))
  exact IsAHarmonicGradient.of_ae_eq_coeff hAE hpointwise

/-- The fixed-cube affine-plus-corrector limit as the homogeneous cube
solution carrier. -/
@[expose]
noncomputable def finiteAffineCorrectionJointLocalCubeSolution
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    (e : Vec d) (n : ℕ) :
    Book.Ch03.CubeSolution (originCube d (n : ℤ)) a where
  toH1 := finiteAffineCorrectionJointLocalH1 a hCauchy e n
  isHarmonic := finiteAffineCorrectionJointLocalH1_isHarmonic
    a hCauchy e n

/-- The local cube-solution wrapper retains the selected `H¹` representative
definitionally. -/
@[simp] theorem finiteAffineCorrectionJointLocalCubeSolution_toH1
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    (e : Vec d) (n : ℕ) :
    (finiteAffineCorrectionJointLocalCubeSolution a hCauchy e n).toH1 =
      finiteAffineCorrectionJointLocalH1 a hCauchy e n :=
  rfl

end

end HighContrast
end HCPolySupport
