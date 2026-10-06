/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.PhysicalLiouvilleGauge
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.LiouvillePrivateThresholdFixedFamily
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1EquivariantPullbackEliminator
public import LeanPool.HighContrastHomogenization.Provider.Sharp.CoarseBlockOrder

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.PhysicalLiouvilleDoubleInclusion

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Physical Liouville double inclusion

The scalar normalized classification is transported through the exact
normalized-root gauge while retaining the same physical corrector family.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set _root_.Filter

noncomputable section

variable {d : ℕ}

private theorem normalizedRoot_transpose_eq
    [NeZero d]
    {m : Mat d} (hm : m.PosDef) :
    matTranspose (Selection.normalizedRoot m) = Selection.normalizedRoot m := by
  have hq := normalizedRoot_posDef_of_posDef hm
  simpa only [matTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using!
    hq.isHermitian

private theorem vecDot_matVecMul_of_symm
    {R : Mat d} (hR : matTranspose R = R) (y w : Vec d) :
    vecDot y (matVecMul R w) = vecDot (matVecMul R y) w := by
  have h := vecDot_matVecMul_transpose y w R
  rwa [hR] at h

private theorem linear_quasiMeasurePreserving
    (L : Mat d) (hL : IsUnit L.det) :
    Measure.QuasiMeasurePreserving (matVecMul L) volume volume := by
  refine ⟨(continuous_matVecMul L).measurable, ?_⟩
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi
    (M := L) hL.ne_zero
  change Measure.map (Matrix.toLin' L) volume ≪ volume
  rw [hmap]
  exact Measure.smul_absolutelyContinuous

private theorem eventuallyEq_of_comp_matVecMul
    {L : Mat d} (hL : IsUnit L.det) {f g : Vec d → ℝ}
    (h : (fun y ↦ f (matVecMul L y)) =ᵐ[volume]
      fun y ↦ g (matVecMul L y)) :
    f =ᵐ[volume] g := by
  let hLinv : IsUnit (L⁻¹).det := Matrix.isUnit_nonsing_inv_det L hL
  have hpull := (linear_quasiMeasurePreserving L⁻¹ hLinv).tendsto_ae h
  filter_upwards [hpull] with x hx
  change f (matVecMul L (matVecMul L⁻¹ x)) =
    g (matVecMul L (matVecMul L⁻¹ x)) at hx
  simpa only [matVecMul_mul, Matrix.mul_nonsing_inv L hL,
    matVecMul_one] using hx

/-- A canonical physical corrector family satisfies the full two-sided
Liouville classification on every certified sample. -/
theorem CanonicalPullbackCorrectorFamily.physicalLiouvilleDoubleInclusion
    [NeZero d]
    {GoodScale : Mat d → CoeffSpace d → ℝ → Prop}
    {abar : Mat d}
    {Phi : Vec d → CoeffSpace d → Vec d → ℝ}
    {gradPhi : Vec d → CoeffSpace d → Vec d → Vec d}
    (hfamily : CanonicalPullbackCorrectorFamily
      GoodScale abar Phi gradPhi)
    (a : CoeffSpace d) (x : ℝ) (hgood : GoodScale abar a x) :
    ∀ theta : ℝ, theta ∈ Set.Ioo (0 : ℝ) 1 →
      (∀ (v : Vec d → ℝ) (Dv : Vec d → Vec d),
        MemLiouvilleClass (fun y ↦ a.1 y) theta v Dv →
        ∃ (e : Vec d) (c : ℝ),
          v =ᵐ[volume] fun y ↦ vecDot e y + Phi e a y + c) ∧
      ∀ (e : Vec d) (c : ℝ),
        MemLiouvilleClass (fun y ↦ a.1 y) theta
          (fun y ↦ vecDot e y + Phi e a y + c)
          (fun y ↦ e + gradPhi e a y) := by
  intro theta htheta
  obtain ⟨hS, s, tolerance, aRef, delay, hCauchy, hs, hsLt,
      haRef, htail, hPhi, hpullback⟩ :=
    hfamily.normalizedJoint a x hgood
  let L : Mat d := Selection.normalizedRoot (symmPart abar)
  let hL : IsUnit L.det := (Matrix.isUnit_iff_isUnit_det _).mp
    (normalizedRoot_posDef_of_posDef hS).isUnit
  let normalized := normalizedCenteredCoeff a abar hS
  let pulled := affinePullbackCoeffSpace L hL normalized
  let b : CoeffField d := (⇑pulled.1 : CoeffField d)
  have hb : IsAELocallyUniformlyElliptic b := pulled.2
  have hpulledAffine :
      (⇑pulled.1 : CoeffField d) =ᵐ[volume]
        affineCoefficient L hL ⇑normalized.1 := by
    simpa only [pulled] using affinePullbackCoeffSpace_ae L hL normalized
  have haffineB : affineCoefficient L hL ⇑normalized.1 =ᵐ[volume] b :=
    hpulledAffine.symm
  have hcoeff : ∀ q : ℕ,
      Book.Ch03.publicCoeffField (originCube d (q : ℤ)) aRef
        =ᵐ[volumeMeasureOn (localGradientCube d q)] b := by
    intro q
    have hpublic := Book.Ch03.publicCoeffField_ae_eq_openCubeSet
      (originCube d (q : ℤ)) aRef
    have hlocalAffine :
        (aRef.coeffOn (originCube d (q : ℤ))).toCoeffField
          =ᵐ[volumeMeasureOn (localGradientCube d q)]
            affineCoefficient L hL ⇑normalized.1 := by
      exact _root_.Filter.Eventually.of_forall fun y ↦ by
        simpa only [L, hL, normalized] using
          congrFun (haRef (originCube d (q : ℤ))) y
    have hpublic' : Book.Ch03.publicCoeffField
        (originCube d (q : ℤ)) aRef
          =ᵐ[volumeMeasureOn (localGradientCube d q)]
            (aRef.coeffOn (originCube d (q : ℤ))).toCoeffField := by
      simpa only [localGradientCube] using hpublic
    exact hpublic'.trans
      (hlocalAffine.trans (ae_restrict_of_ae haffineB))
  have href :=
    scalarIdentityGoodTail_liouvilleDoubleInclusion_fixedFamily_after_restart
      d s hs hsLt hb aRef tolerance
      (((Quenched.triadicCeilingIndex x + delay : ℕ) : ℤ))
      htail hcoeff hCauchy hPhi theta htheta
  have hLT : matTranspose L = L := by
    simpa only [L] using normalizedRoot_transpose_eq hS
  have htransport : ∀ (v : Vec d → ℝ) (Dv : Vec d → Vec d),
      MemLiouvilleClass (fun y ↦ a.1 y) theta v Dv ↔
        MemLiouvilleClass b theta
          (fun y ↦ v (matVecMul L y))
          (fun y ↦ matVecMul (matTranspose L) (Dv (matVecMul L y))) := by
    intro v Dv
    simpa only [L, hL, normalized] using
      memLiouvilleClass_physical_normalizedPullback_iff
        a abar hS hb haffineB v Dv
  constructor
  · intro v Dv hv
    obtain ⟨eRef, cRef, hvRef⟩ := (href.1 ((htransport v Dv).mp hv))
    let e : Vec d := matVecMul L⁻¹ eRef
    have hLe : matVecMul L e = eRef := by
      simp only [e, matVecMul_mul, Matrix.mul_nonsing_inv L hL, matVecMul_one]
    obtain ⟨cPhi, hPhiValue⟩ := (hpullback e).1
    have hpulledValue :
        (fun y ↦ v (matVecMul L y)) =ᵐ[volume]
          fun y ↦ (vecDot e (matVecMul L y) +
            Phi e a (matVecMul L y) + (cRef - cPhi)) := by
      filter_upwards [hvRef, hPhiValue] with y hyv hyPhi
      rw [hyv, hyPhi, hLe]
      have hdot : vecDot e (matVecMul L y) = vecDot eRef y := by
        rw [vecDot_matVecMul_of_symm hLT, hLe]
      rw [hdot]
      ring
    exact ⟨e, cRef - cPhi,
      eventuallyEq_of_comp_matVecMul hL hpulledValue⟩
  · intro e c
    obtain ⟨cPhi, hPhiValue⟩ := (hpullback e).1
    have hRef := href.2 (matVecMul L e) (c + cPhi)
    let vPull : Vec d → ℝ := fun y ↦
      vecDot e (matVecMul L y) + Phi e a (matVecMul L y) + c
    let DPull : Vec d → Vec d := fun y ↦
      matVecMul (matTranspose L) (e + gradPhi e a (matVecMul L y))
    have hvalue :
        (fun y ↦ vecDot (matVecMul L e) y +
          (finiteAffineCorrectionJointLocalLimit aRef hCauchy
            (matVecMul L e)).globalValueRepresentative y + (c + cPhi))
          =ᵐ[volume] vPull := by
      filter_upwards [hPhiValue] with y hyPhi
      dsimp only [vPull]
      rw [hyPhi]
      have hdot : vecDot e (matVecMul L y) = vecDot (matVecMul L e) y :=
        vecDot_matVecMul_of_symm hLT e y
      rw [hdot]
      ring
    have hgrad :
        (fun y ↦ matVecMul L e +
          (finiteAffineCorrectionJointLocalLimit aRef hCauchy
            (matVecMul L e)).globalGradientRepresentative y)
          =ᵐ[volume] DPull := by
      have hp := (hpullback e).2.symm
      filter_upwards [hp] with y hy
      dsimp only [DPull]
      rw [hLT]
      exact hy
    have hPull : MemLiouvilleClass b theta vPull DPull :=
      (memLiouvilleClass_congr_representatives hvalue hgrad).mp hRef
    exact (htransport
      (fun y ↦ vecDot e y + Phi e a y + c)
      (fun y ↦ e + gradPhi e a y)).mpr (by
        simpa only [vPull, DPull] using hPull)

end

end Root
end HighContrast
end HCPolySupport
