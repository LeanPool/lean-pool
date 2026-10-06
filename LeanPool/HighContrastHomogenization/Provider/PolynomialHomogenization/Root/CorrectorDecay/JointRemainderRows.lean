/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.LawFreeCoarsePoincare
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteCubeSolutionRestriction

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.JointRemainderRows

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set

noncomputable section

private theorem cubeSolution_weakFluxIntegrable
    {d : ℕ} {Q : TriadicCube d} {a : Book.Ch02.TriadicCoeffFamily d}
    (u : Book.Ch03.CubeSolution Q a) :
    weakFluxIntegrable (Book.Ch02.cubeDomain Q : Set (Vec d))
      (a.coeffOn Q).toCoeffField u := by
  intro phi
  exact integrableOn_vecDot_of_memVectorL2
    (Book.Ch02.Solution.flux_memVectorL2 u)
    phi.toH1Function.grad_memVectorL2

@[expose]
noncomputable def jointAffineCubeSolution
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (Phi : Vec d → NormalizedLocalH1Carrier d)
    (hPhi : IsFiniteAffineCorrectionJointLocalEquation a Phi)
    (e : Vec d) (q : ℕ) :
    Book.Ch03.CubeSolution (originCube d (q : ℤ)) a :=
  let phiLocal : H1Function
      (Book.Ch02.cubeDomain (originCube d (q : ℤ)) : Set (Vec d)) := by
    simpa only [localGradientCube, Book.Ch02.cubeDomain_coe] using
      (Phi e).localH1Function q
  { toH1 := finiteAffineBoundaryH1 (q : ℤ) e + phiLocal
    isHarmonic := by
      simpa only [phiLocal, localGradientCube, Book.Ch02.cubeDomain_coe] using!
        hPhi.2 e q }

@[expose]
noncomputable def finiteAffineInnerCubeSolution
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (q m : ℕ) (hqm : q ≤ m) :
    Book.Ch03.CubeSolution (originCube d (q : ℤ)) a :=
  finiteCubeSolutionRestriction a (by exact_mod_cast hqm)
    (finiteAffineCubeSolution a (m : ℤ) e)

@[expose]
noncomputable def jointFiniteRemainderCubeSolution
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (Phi : Vec d → NormalizedLocalH1Carrier d)
    (hPhi : IsFiniteAffineCorrectionJointLocalEquation a Phi)
    (e : Vec d) (q m : ℕ) (hqm : q ≤ m) :
    Book.Ch03.CubeSolution (originCube d (q : ℤ)) a :=
  AHarmonicFunction.subOfIntegrable
    (jointAffineCubeSolution a Phi hPhi e q)
    (finiteAffineInnerCubeSolution a e q m hqm)
    (cubeSolution_weakFluxIntegrable
      (jointAffineCubeSolution a Phi hPhi e q))
    (cubeSolution_weakFluxIntegrable
      (finiteAffineInnerCubeSolution a e q m hqm))

theorem jointFiniteRemainder_grad
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (Phi : Vec d → NormalizedLocalH1Carrier d)
    (hPhi : IsFiniteAffineCorrectionJointLocalEquation a Phi)
    (e : Vec d) (q m : ℕ) (hqm : q ≤ m) :
    (jointFiniteRemainderCubeSolution a Phi hPhi e q m hqm).toH1.grad =
      fun x ↦
        e + ((Phi e).localH1Function q).grad x -
        (finiteAffineSolution a (m : ℤ) e).toH1.grad x := by
  unfold jointFiniteRemainderCubeSolution
  rw [AHarmonicFunction.grad_subOfIntegrable]
  funext x
  rw [Pi.sub_apply]
  simp only [jointAffineCubeSolution,
    finiteAffineInnerCubeSolution, H1Function.add_grad,
    finiteAffineBoundaryH1_grad, finiteCubeSolutionRestriction_grad,
    finiteAffineCubeSolution]
  rfl

theorem jointFiniteRemainder_energy_eq
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (Phi : Vec d → NormalizedLocalH1Carrier d)
    (hPhi : IsFiniteAffineCorrectionJointLocalEquation a Phi)
    (e : Vec d) (q m : ℕ) (hqm : q ≤ m) :
    Book.Ch03.h1EnergyNormOnCube (originCube d (q : ℤ)) a
        (jointFiniteRemainderCubeSolution
          a Phi hPhi e q m hqm).toH1 =
      Real.sqrt (normalizedLocalSymmetricEnergy
        (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
          (originCube d (q : ℤ)) a)
        (((show LocalGradientL2 d q from
              constantGradientOnOriginCube e (q : ℤ)) +
            (Phi e).gradientComponent q) -
          finiteAffineInnerGradientClass a e q (m - q))) := by
  have hclass :
      ((show LocalGradientL2 d q from
            constantGradientOnOriginCube e (q : ℤ)) +
          (Phi e).gradientComponent q) -
        finiteAffineInnerGradientClass a e q (m - q) =
      (jointFiniteRemainderCubeSolution
        a Phi hPhi e q m hqm).toH1.gradToHilbertVectorL2 := by
    rw [← NormalizedLocalH1Carrier.localH1Function_gradToHilbertVectorL2]
    have hfiniteClass :
        finiteAffineInnerGradientClass a e q (m - q) =
          (finiteAffineSolutionInnerH1 a (q : ℤ) (m : ℤ)
            (by exact_mod_cast hqm) e).gradToHilbertVectorL2 := by
      have hcast : finiteAffineInnerGradientClass a e q (m - q) =
          (finiteAffineSolutionInnerH1 a (q : ℤ)
            ((q + (m - q) : ℕ) : ℤ) (by omega) e).gradToHilbertVectorL2 := rfl
      rw [hcast]
      simp only [Nat.add_sub_of_le hqm]
      rfl
    rw [hfiniteClass]
    let z := jointFiniteRemainderCubeSolution a Phi hPhi e q m hqm
    let w : H1Function (localGradientCube d q) :=
      Eq.mp (by simp only [localGradientCube, Book.Ch02.cubeDomain_coe]) z.toH1
    have hwgrad : w.grad = z.toH1.grad := rfl
    let c : LocalGradientL2 d q := constantGradientOnOriginCube e (q : ℤ)
    let p : LocalGradientL2 d q :=
      ((Phi e).localH1Function q).gradToHilbertVectorL2
    let f : LocalGradientL2 d q :=
      (finiteAffineSolutionInnerH1 a (q : ℤ) (m : ℤ)
        (by exact_mod_cast hqm) e).gradToHilbertVectorL2
    apply Lp.ext
    filter_upwards
        [coeFn_toHilbertVectorL2OfVecField
            (memVectorL2_const e),
          (Phi e).localH1Function q |>.coeFn_gradToHilbertVectorL2,
          (finiteAffineSolutionInnerH1 a (q : ℤ) (m : ℤ)
            (by exact_mod_cast hqm) e).coeFn_gradToHilbertVectorL2,
          w.coeFn_gradToHilbertVectorL2,
          Lp.coeFn_add c p,
          Lp.coeFn_sub (c + p) f]
      with x hc hp hf hw hadd hsub
    have hsub' : (c + p - f) x = (c + p) x - f x := hsub
    have hadd' : (c + p) x = c x + p x := hadd
    rw [hsub', hadd']
    show _ = w.gradToHilbertVectorL2 x
    rw [hw, hwgrad, jointFiniteRemainder_grad]
    have hc' : c x = hilbertifyVecField (fun _ : Vec d ↦ e) x := hc
    have hf' : f x = hilbertifyVecField
        (finiteAffineSolutionInnerH1 a (q : ℤ) (m : ℤ)
          (by exact_mod_cast hqm) e).grad x := hf
    rw [hc', hp, hf']
    simp only [finiteAffineSolutionInnerH1_grad]
    simp [hilbertifyVecField]
  rw [hclass]
  symm
  let wOuter : H1Function (openCubeSet (originCube d (q : ℤ))) :=
    Eq.mp (by simp only [Book.Ch02.cubeDomain_coe])
      (jointFiniteRemainderCubeSolution a Phi hPhi e q m hqm).toH1
  change Real.sqrt (normalizedLocalSymmetricEnergy _
    wOuter.gradToHilbertVectorL2) = _
  rw [Root.sqrt_normalizedEnergy_grad_eq_weightedGradNorm_toReal]
  rw [weightedGradNorm_congr_coeff_ae_on _
    (Book.Ch03.publicCoeffField_ae_eq_openCubeSet
      (originCube d (q : ℤ)) a)]
  have houterGrad : wOuter.grad =
      (jointFiniteRemainderCubeSolution a Phi hPhi e q m hqm).toH1.grad := rfl
  rw [houterGrad, weightedGradNorm_eq_ofReal_h1EnergyNormOnCube]
  rw [ENNReal.toReal_ofReal]
  unfold Book.Ch03.h1EnergyNormOnCube
  exact Real.sqrt_nonneg _

/-- The harmonic difference between the joint exact-gauge corrector and a
finite affine corrector has both printed-order rows controlled by its
coefficient energy, with a law-free multiplier. -/
theorem exists_jointFiniteRemainderRowsConstant
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d)
        (Phi : Vec d → NormalizedLocalH1Carrier d)
        (hPhi : IsFiniteAffineCorrectionJointLocalEquation a Phi),
        ∀ (e : Vec d) (q m : ℕ) (hqm : q ≤ m) (B : ℝ),
          scalarIdentityWeakError a s (q : ℤ) ≤ 1 →
          Book.Ch03.h1EnergyNormOnCube (originCube d (q : ℤ)) a
              (jointFiniteRemainderCubeSolution
                a Phi hPhi e q m hqm).toH1 ≤ B →
          cubeScaleNormalizedDualNegativeBesovVectorNormTwo
              (originCube d (q : ℤ)) s
              (jointFiniteRemainderCubeSolution
                a Phi hPhi e q m hqm).toH1.grad ≤ C * B ∧
          cubeScaleNormalizedDualNegativeBesovVectorNormTwo
              (originCube d (q : ℤ)) s
              (fun x ↦ matVecMul
                (Book.Ch03.publicCoeffField (originCube d (q : ℤ)) a x)
                ((jointFiniteRemainderCubeSolution
                  a Phi hPhi e q m hqm).toH1.grad x)) ≤ C * B := by
  obtain ⟨C, hC, hrows⟩ := exists_lawFreeCoarsePoincareRowsConstant
    d s hs
  refine ⟨C, hC, ?_⟩
  intro a Phi hPhi e q m hqm B hweak henergy
  have hraw := hrows a (q : ℤ)
    (jointFiniteRemainderCubeSolution a Phi hPhi e q m hqm) hweak
  constructor
  · exact hraw.1.trans (mul_le_mul_of_nonneg_left henergy hC.le)
  · exact hraw.2.trans (mul_le_mul_of_nonneg_left henergy hC.le)

end

end HighContrast
end HCPolySupport
