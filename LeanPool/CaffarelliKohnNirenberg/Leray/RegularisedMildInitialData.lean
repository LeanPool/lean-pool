/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedInitialData
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierCoordinateL2Bridge
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildJSpace
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMollifierAllDerivatives
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.H1.Basic

/-!
# Regularised Mild Initial Data

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The mollified initial datum in the real `L²` carrier belongs to the
closed solenoidal subspace used by `lem:reg-local-mild`. -/
theorem regUniformMollifiedInitial_mildJData
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : CKN.IsInJ a) :
    RegularizedMildJData
      (realVectorL2OfCoordinateFunction
        (regUniformMollifiedInitial ρ ε hε a)
        (regMollifiedInitial_isInJ ρ ε hε ha).1) := by
  let field := regUniformMollifiedInitial ρ ε hε a
  let hfield : MemLp field (2 : ℝ≥0∞) volume :=
    (regMollifiedInitial_isInJ ρ ε hε ha).1
  let b : RealVectorL2 := realVectorL2OfCoordinateFunction field hfield
  change CKN.IsInJ (realVectorL2Representative b)
  have hJ : CKN.IsInJ field := regMollifiedInitial_isInJ ρ ε hε ha
  have hrep : realVectorL2Representative b =ᵐ[volume] field :=
    realVectorL2OfCoordinateFunction_rep field hfield
  rcases hJ with ⟨hmem, aSeq, hsm, hcompact, hdiv, hlimit⟩
  refine ⟨(memLp_congr_ae hrep).2 hmem, aSeq, hsm, hcompact, hdiv, ?_⟩
  have herror (n : ℕ) :
      eLpNorm (fun x => aSeq n x - realVectorL2Representative b x)
          (2 : ℝ≥0∞) volume =
        eLpNorm (fun x => aSeq n x - field x) (2 : ℝ≥0∞) volume := by
    apply eLpNorm_congr_ae
    filter_upwards [hrep] with x hx
    simp [hx]
  exact hlimit.congr' (Filter.Eventually.of_forall fun n => (herror n).symm)

/-- The mollified initial velocity is smooth in space, as used in
`thm:regularised`. -/
theorem regUniformMollifiedInitial_contDiff
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : CKN.IsInJ a) :
    ContDiff ℝ (⊤ : ℕ∞) (regUniformMollifiedInitial ρ ε hε a) := by
  let f := regUniformSpatialField a
  have hinput : MemLp f (2 : ℝ≥0∞) volume := by
    have hcoord : MemLp
        (fun x : L2Vec3 => a (WithLp.ofLp x)) (2 : ℝ≥0∞) volume :=
      ha.1.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin 3))
    exact hcoord.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  have hloc : LocallyIntegrable f volume := hinput.locallyIntegrable (by norm_num)
  have hkernelSmooth : ContDiff ℝ (⊤ : ℕ∞) (regMollifierKernel ρ ε hε) := by
    have hscale : ContDiff ℝ (⊤ : ℕ∞) (fun y : L2Vec3 => ε⁻¹ • y) := by
      fun_prop
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun y : L2Vec3 => (ε ^ 3)⁻¹ * ρ.rho (ε⁻¹ • y))
    exact contDiff_const.mul (ρ.smooth.comp hscale)
  have hkernelCompact : HasCompactSupport (regMollifierKernel ρ ε hε) := by
    unfold regMollifierKernel
    have hscaleNe : ε⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hε)
    have hcomp := ρ.compact.comp_homeomorph
      (Homeomorph.smulOfNeZero ε⁻¹ hscaleNe)
    exact hcomp.mul_left
  have hconv : ContDiff ℝ (⊤ : ℕ∞)
      (MeasureTheory.convolution (regMollifierKernel ρ ε hε) f
        allDerivativeScalarVectorAction volume) :=
    hkernelCompact.contDiff_convolution_left
      (L := allDerivativeScalarVectorAction) hkernelSmooth hloc
  have hto : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => WithLp.toLp 2 x) := by
    fun_prop
  let e : L2Vec3 ≃L[ℝ] Vec3 := PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 3 => ℝ)
  have hcoordinate : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 =>
      e (MeasureTheory.convolution (regMollifierKernel ρ ε hε) f
        allDerivativeScalarVectorAction volume (WithLp.toLp 2 x))) := by
    exact e.toContinuousLinearMap.contDiff.comp (hconv.comp hto)
  change ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 =>
    e (regMollifyVector ρ ε hε f (WithLp.toLp 2 x)))
  exact hcoordinate

end CKN.Leray

end
