/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1CoefficientEnergySeminorm
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineRegularityJointAssembly
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineVaryingSlopeLimit

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1FiniteCorrectorLimitBridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Fixed-cube finite-corrector limit bridge

This file consumes the joint local-limit field of the available regularity
assembly and exposes the exact full-gradient convergence needed by the
coefficient-energy telescope.
-/

namespace HCPolySupport
namespace HighContrast

open Filter MeasureTheory

noncomputable section

/-- The finite affine full-gradient class on the fixed inner cube. -/
@[expose]
noncomputable def finiteAffineInnerGradientClass
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (q k : ℕ) : LocalGradientL2 d q :=
  Eq.mp (by simp only [LocalGradientL2, localGradientCube, Book.Ch02.cubeDomain_coe]; rfl)
    (finiteAffineSolutionInnerH1 a (q : ℤ)
      ((q + k : ℕ) : ℤ) (by omega) e).gradToHilbertVectorL2

/-- The finite affine full gradients converge on every fixed cube to the
full gradient of any joint local-limit family. -/
theorem finiteAffineSolutionInnerGradient_tendsto_of_jointLocalEquation
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (Phi : Vec d → NormalizedLocalH1Carrier d)
    (hPhi : IsFiniteAffineCorrectionJointLocalEquation a Phi)
    (e : Vec d) (q : ℕ) :
    Tendsto
      (fun k ↦ finiteAffineInnerGradientClass a e q k)
      atTop
      (nhds ((show LocalGradientL2 d q from
          constantGradientOnOriginCube e (q : ℤ)) +
        (Phi e).gradientComponent q)) := by
  have hlimit := (hPhi.1 e q).snd_nhds
  exact (tendsto_const_nhds.add hlimit).congr'
    (Filter.Eventually.of_forall fun k ↦
      by
        dsimp only
        have hcast : finiteAffineInnerGradientClass a e q k =
            (finiteAffineSolutionInnerH1 a (q : ℤ)
              ((q + k : ℕ) : ℤ) (by omega) e).gradToHilbertVectorL2 := rfl
        rw [hcast]
        exact finiteAffineFullGradientClass_eq_innerH1Gradient a e q k)

/-- A uniform coefficient-energy tail for the finite full gradients passes
to the joint local-limit full gradient. -/
theorem sqrt_jointLocalGradient_sub_finiteAffine_le_of_uniform_tail
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (Phi : Vec d → NormalizedLocalH1Carrier d)
    (hPhi : IsFiniteAffineCorrectionJointLocalEquation a Phi)
    (e : Vec d) (q k : ℕ) (B : ℝ)
    (htail : ∀ m : ℕ, k ≤ m →
      Real.sqrt (normalizedLocalSymmetricEnergy
        (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
          (originCube d (q : ℤ)) a)
        (finiteAffineInnerGradientClass a e q m -
          finiteAffineInnerGradientClass a e q k)) ≤ B) :
    Real.sqrt (normalizedLocalSymmetricEnergy
      (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
        (originCube d (q : ℤ)) a)
      (((show LocalGradientL2 d q from
            constantGradientOnOriginCube e (q : ℤ)) +
          (Phi e).gradientComponent q) -
        finiteAffineInnerGradientClass a e q k)) ≤ B := by
  exact sqrt_normalizedLocalSymmetricEnergy_limit_sub_le_of_uniform_tail
    (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
      (originCube d (q : ℤ)) a)
    (fun m ↦ finiteAffineInnerGradientClass a e q m)
    ((show LocalGradientL2 d q from
        constantGradientOnOriginCube e (q : ℤ)) +
      (Phi e).gradientComponent q)
    B
    (finiteAffineSolutionInnerGradient_tendsto_of_jointLocalEquation
      a Phi hPhi e q)
    k htail

end

end HighContrast
end HCPolySupport
