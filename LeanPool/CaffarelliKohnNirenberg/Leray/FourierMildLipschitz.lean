/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildNonlinearity

/-!
# Difference bounds for the regularized quadratic term

These estimates supply the contraction constant in `lem:reg-local-mild`.
-/

public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

@[expose]
def mildScalarVectorActionLinear : ℝ →ₗ[ℝ] L2Vec3 →ₗ[ℝ] L2Vec3 :=
  LinearMap.mk₂ ℝ (fun c x => c • x)
    (by intro c d x; exact add_smul c d x)
    (by intro c d x; exact mul_smul c d x)
    (by intro c x y; exact smul_add c x y)
    (by intro c d x; exact (smul_comm c d x).symm)

@[expose]
def mildScalarVectorAction : ℝ →L[ℝ] L2Vec3 →L[ℝ] L2Vec3 :=
  mildScalarVectorActionLinear.mkContinuous₂ 1 (by
    intro c x
    change ‖c • x‖ ≤ 1 * ‖c‖ * ‖x‖
    simpa [one_mul] using (norm_smul_le c x))

@[expose]
def mildTensorOuterLinear : L2Vec3 →ₗ[ℝ] L2Vec3 →ₗ[ℝ] RealTensor3 :=
  LinearMap.mk₂ ℝ regularizedTensorOuter
    (by
      intro v w u
      apply PiLp.ext
      intro i
      apply PiLp.ext
      intro j
      simp [regularizedTensorOuter, add_mul])
    (by
      intro c v u
      apply PiLp.ext
      intro i
      apply PiLp.ext
      intro j
      simp only [regularizedTensorOuter, PiLp.smul_apply]
      ring)
    (by
      intro v u w
      apply PiLp.ext
      intro i
      apply PiLp.ext
      intro j
      simp [regularizedTensorOuter, mul_add])
    (by
      intro c v u
      apply PiLp.ext
      intro i
      apply PiLp.ext
      intro j
      simp only [regularizedTensorOuter, PiLp.smul_apply, smul_eq_mul]
      ring)

@[expose]
def mildTensorOuterCLM : L2Vec3 →L[ℝ] L2Vec3 →L[ℝ] RealTensor3 :=
  mildTensorOuterLinear.mkContinuous₂ 1 (by
    intro v u
    change ‖regularizedTensorOuter v u‖ ≤ 1 * ‖v‖ * ‖u‖
    rw [regularizedTensorOuter_norm]
    calc
      ‖v‖ * ‖u‖ ≤ 1 * ‖v‖ * ‖u‖ := by simp)

private theorem regMollifyVector_neg
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {f : L2Vec3 → L2Vec3} :
    regMollifyVector ρ ε hε (-f) = -regMollifyVector ρ ε hε f := by
  change MeasureTheory.convolution (regMollifierKernel ρ ε hε) (-f)
      mildScalarVectorAction volume = _
  funext x
  change (∫ y, mildScalarVectorAction (regMollifierKernel ρ ε hε y)
      ((-f) (x - y))) = -∫ y, mildScalarVectorAction
        (regMollifierKernel ρ ε hε y) (f (x - y))
  have hfun : (fun y => mildScalarVectorAction (regMollifierKernel ρ ε hε y)
      ((-f) (x - y))) = fun y => -(mildScalarVectorAction
        (regMollifierKernel ρ ε hε y) (f (x - y))) := by
    funext y
    simp [mildScalarVectorAction, mildScalarVectorActionLinear]
  rw [hfun, integral_neg]

private theorem regMollifyVector_sub
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {f g : L2Vec3 → L2Vec3} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    regMollifyVector ρ ε hε (f - g) =
      regMollifyVector ρ ε hε f - regMollifyVector ρ ε hε g := by
  have hneg := regMollifyVector_neg ρ ε hε (f := g)
  have hadd := regMollifyVector_add ρ ε hε hf hg.neg
  calc
    regMollifyVector ρ ε hε (f - g) =
        regMollifyVector ρ ε hε (f + -g) := by rfl
    _ = regMollifyVector ρ ε hε f + regMollifyVector ρ ε hε (-g) := hadd
    _ = regMollifyVector ρ ε hε f - regMollifyVector ρ ε hε g := by rw [hneg]; rfl

private theorem regMollifyVector_congr_ae
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {f g : L2Vec3 → L2Vec3} (hfg : f =ᵐ[volume] g) :
    regMollifyVector ρ ε hε f = regMollifyVector ρ ε hε g := by
  change MeasureTheory.convolution (regMollifierKernel ρ ε hε) f
      mildScalarVectorAction volume =
    MeasureTheory.convolution (regMollifierKernel ρ ε hε) g
      mildScalarVectorAction volume
  exact MeasureTheory.convolution_congr (L := mildScalarVectorAction)
    (Filter.Eventually.of_forall fun _ => rfl) hfg

private theorem regularizedTensorOuter_sub_identity (a b c d : L2Vec3) :
    regularizedTensorOuter a b - regularizedTensorOuter c d =
      regularizedTensorOuter (a - c) b + regularizedTensorOuter c (b - d) := by
  apply PiLp.ext
  intro i
  apply PiLp.ext
  intro j
  simp only [regularizedTensorOuter, PiLp.sub_apply, PiLp.add_apply]
  ring

/-- The scale-dependent `L²` to `L∞` constant of convolution by the
regularizing kernel. It is used in the quadratic estimate for `eq:reg-mild`. -/
@[expose]
def regularizedMildMollifierConstant (ρ : RegMollifierProfile) (ε : ℝ) : ℝ :=
  ENNReal.toReal (ENNReal.ofReal (ε ^ (-(3 / 2 : ℝ))) * eLpNorm ρ.rho 2 volume)

private theorem regularizedMildMollifierConstant_nonneg
    (ρ : RegMollifierProfile) (ε : ℝ) :
    0 ≤ regularizedMildMollifierConstant ρ ε := by
  exact ENNReal.toReal_nonneg

private theorem regMollifyVector_norm_le_scaled
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {f : L2Vec3 → L2Vec3} (hf : MemLp f 2 volume) (x : L2Vec3) :
    ‖regMollifyVector ρ ε hε f x‖ ≤
      regularizedMildMollifierConstant ρ ε * ‖hf.toLp f‖ := by
  have hpoint := regMollifyVector_pointwise_enorm_le_scaled ρ ε hε hf x
  have hfinite : eLpNorm f 2 volume ≠ ∞ := hf.eLpNorm_ne_top
  have hrepnorm : eLpNorm (hf.toLp f) 2 volume = eLpNorm f 2 volume :=
    eLpNorm_congr_ae hf.coeFn_toLp
  have hprofile : eLpNorm ρ.rho 2 volume ≠ ∞ := by
    exact (ρ.smooth.continuous.memLp_of_hasCompactSupport ρ.compact).eLpNorm_ne_top
  have hfiniteCoef :
      ENNReal.ofReal (ε ^ (-(3 / 2 : ℝ))) * eLpNorm ρ.rho 2 volume * eLpNorm f 2 volume ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hprofile) hfinite
  have hreal : ‖regMollifyVector ρ ε hε f x‖ ≤
      ENNReal.toReal (ENNReal.ofReal (ε ^ (-(3 / 2 : ℝ))) * eLpNorm ρ.rho 2 volume) *
        ‖hf.toLp f‖ := by
    have htoReal := ENNReal.toReal_mono hfiniteCoef hpoint
    simpa [← ofReal_norm, ENNReal.toReal_mul, hprofile, hfinite, hrepnorm, Lp.norm_def,
      ENNReal.toReal_ofReal (le_of_lt (Real.rpow_pos_of_pos hε _))] using htoReal
  simpa [regularizedMildMollifierConstant] using hreal

@[expose]
def mildTensorProductField (f g : L2Vec3 → L2Vec3) : L2Vec3 → RealTensor3 :=
  fun x => regularizedTensorOuter (f x) (g x)

private theorem mildTensorProductField_aestronglyMeasurable
    {f g : L2Vec3 → L2Vec3} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (mildTensorProductField f g) volume := by
  exact (mildTensorOuterCLM.continuous₂.comp_aestronglyMeasurable
    (hf.prodMk hg)).congr (Filter.Eventually.of_forall fun _ => rfl)

private theorem mildTensorProductField_memLp
    {f g : L2Vec3 → L2Vec3} (hf : AEStronglyMeasurable f volume)
    (hg : MemLp g 2 volume) (c : ℝ)
    (hbound : ∀ x, ‖f x‖ ≤ c) :
    MemLp (mildTensorProductField f g) 2 volume := by
  apply hg.of_le_mul (c := c) (mildTensorProductField_aestronglyMeasurable
    hf hg.aestronglyMeasurable)
  filter_upwards [] with x
  rw [mildTensorProductField, regularizedTensorOuter_norm]
  calc
    ‖f x‖ * ‖g x‖ ≤ c * ‖g x‖ :=
      mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)
    _ = c * ‖g x‖ := rfl

private theorem mildTensorProductLp_norm_le
    {f g : L2Vec3 → L2Vec3} (hf : AEStronglyMeasurable f volume)
    (hg : MemLp g 2 volume) (c : ℝ)
    (hbound : ∀ x, ‖f x‖ ≤ c) :
    ‖(mildTensorProductField_memLp hf hg c hbound).toLp
        (mildTensorProductField f g)‖ ≤ c * ‖hg.toLp g‖ := by
  have hpoint : ∀ᵐ x ∂volume,
      ‖(mildTensorProductField_memLp hf hg c hbound).toLp
        (mildTensorProductField f g) x‖ ≤ c * ‖hg.toLp g x‖ := by
    filter_upwards [
      (mildTensorProductField_memLp hf hg c hbound).coeFn_toLp,
      hg.coeFn_toLp] with x hx hgx
    rw [hx, mildTensorProductField, regularizedTensorOuter_norm, ← hgx]
    exact mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)
  exact Lp.norm_le_mul_norm_of_ae_le_mul hpoint

private theorem regMollifyVector_norm_le_l2
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : RealVectorL2) (x : L2Vec3) :
    ‖regMollifyVector ρ ε hε u x‖ ≤
      regularizedMildMollifierConstant ρ ε * ‖u‖ := by
  let hu := Lp.memLp u
  have hrep : hu.toLp u = u := by
    apply Lp.ext
    exact hu.coeFn_toLp
  simpa [hrep] using regMollifyVector_norm_le_scaled ρ ε hε hu x

private theorem regMollifyVector_sub_norm_le_l2
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u v : RealVectorL2) (x : L2Vec3) :
    ‖regMollifyVector ρ ε hε (u - v) x‖ ≤
      regularizedMildMollifierConstant ρ ε * ‖u - v‖ := by
  let hu := Lp.memLp u
  let hv := Lp.memLp v
  let hud := hu.sub hv
  have hrep : hud.toLp (fun x => u x - v x) = u - v := by
    change hud.toLp ((fun x => u x) - (fun x => v x)) = u - v
    calc
      hud.toLp ((fun x => u x) - (fun x => v x)) = hu.toLp u - hv.toLp v :=
        MemLp.toLp_sub hu hv
      _ = u - v := by rw [Lp.toLp_coeFn u hu, Lp.toLp_coeFn v hv]
  calc
    ‖regMollifyVector ρ ε hε (u - v) x‖ ≤
        regularizedMildMollifierConstant ρ ε *
          ‖hud.toLp (fun y => u y - v y)‖ :=
      regMollifyVector_norm_le_scaled ρ ε hε hud x
    _ = regularizedMildMollifierConstant ρ ε * ‖u - v‖ := by rw [hrep]

/-- The regularized quadratic tensor is locally Lipschitz from velocity `L²`
to tensor `L²`, with the constant used in `lem:reg-local-mild`. -/
theorem regularizedMildTensor_sub_norm_le (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) (u v : RealVectorL2) :
    ‖regularizedMildTensor ρ ε hε u - regularizedMildTensor ρ ε hε v‖ ≤
      regularizedMildMollifierConstant ρ ε * (‖u‖ + ‖v‖) * ‖u - v‖ := by
  let c := regularizedMildMollifierConstant ρ ε
  let du : L2Vec3 → L2Vec3 := fun x => u x - v x
  have hu : MemLp (fun x : L2Vec3 => u x) 2 volume := Lp.memLp u
  have hv : MemLp (fun x : L2Vec3 => v x) 2 volume := Lp.memLp v
  have hdu : MemLp du 2 volume := by
    change MemLp ((fun x : L2Vec3 => u x) - (fun x => v x)) 2 volume
    exact hu.sub hv
  have hc : 0 ≤ c := regularizedMildMollifierConstant_nonneg ρ ε
  have hJduMeas : AEStronglyMeasurable
      (regMollifyVector ρ ε hε du) volume :=
    regMollifyVector_aestronglyMeasurable ρ ε hε hdu
  have hJvMeas : AEStronglyMeasurable
      (regMollifyVector ρ ε hε v) volume :=
    regMollifyVector_aestronglyMeasurable ρ ε hε hv
  have hJduBound : ∀ x, ‖regMollifyVector ρ ε hε du x‖ ≤ c * ‖u - v‖ := by
    intro x
    have hduLp : hdu.toLp du = u - v := by
      change hdu.toLp ((fun x : L2Vec3 => u x) - (fun x => v x)) = u - v
      calc
        hdu.toLp ((fun x : L2Vec3 => u x) - (fun x => v x)) =
            hu.toLp u - hv.toLp v := MemLp.toLp_sub hu hv
        _ = u - v := by rw [Lp.toLp_coeFn u hu, Lp.toLp_coeFn v hv]
    calc
      ‖regMollifyVector ρ ε hε du x‖ ≤
          regularizedMildMollifierConstant ρ ε * ‖hdu.toLp du‖ :=
        regMollifyVector_norm_le_scaled ρ ε hε hdu x
      _ = c * ‖u - v‖ := by rw [hduLp]
  have hJvBound : ∀ x, ‖regMollifyVector ρ ε hε v x‖ ≤ c * ‖v‖ := by
    intro x
    simpa [c] using regMollifyVector_norm_le_l2 ρ ε hε v x
  let T₁field := mildTensorProductField (regMollifyVector ρ ε hε du) u
  let T₂field := mildTensorProductField (regMollifyVector ρ ε hε v) du
  have hT₁ : MemLp T₁field 2 volume := by
    exact mildTensorProductField_memLp hJduMeas hu (c * ‖u - v‖) hJduBound
  have hT₂ : MemLp T₂field 2 volume := by
    exact mildTensorProductField_memLp hJvMeas hdu (c * ‖v‖) hJvBound
  let T₁ : RealTensorL2 := hT₁.toLp T₁field
  let T₂ : RealTensorL2 := hT₂.toLp T₂field
  have hT₁bound : ‖T₁‖ ≤ c * ‖u - v‖ * ‖u‖ := by
    simpa [T₁, T₁field] using
      mildTensorProductLp_norm_le hJduMeas hu (c * ‖u - v‖) hJduBound
  have hT₂bound : ‖T₂‖ ≤ c * ‖v‖ * ‖u - v‖ := by
    calc
      ‖T₂‖ ≤ c * ‖v‖ * ‖hdu.toLp du‖ := by
        simpa [T₂, T₂field, du] using
          mildTensorProductLp_norm_le hJvMeas hdu (c * ‖v‖) hJvBound
      _ = c * ‖v‖ * ‖u - v‖ := by
        have hduLp : hdu.toLp du = u - v := by
          change hdu.toLp ((fun x : L2Vec3 => u x) - (fun x => v x)) = u - v
          calc
            hdu.toLp ((fun x : L2Vec3 => u x) - (fun x => v x)) =
                hu.toLp u - hv.toLp v := MemLp.toLp_sub hu hv
            _ = u - v := by rw [Lp.toLp_coeFn u hu, Lp.toLp_coeFn v hv]
        rw [hduLp]
  have hregU : (regularizedMildTensor ρ ε hε u : RealTensorL2) =ᵐ[volume]
      regularizedMildTensorField ρ ε hε u := by
    simp only [regularizedMildTensor]
    exact MemLp.coeFn_toLp _
  have hregV : (regularizedMildTensor ρ ε hε v : RealTensorL2) =ᵐ[volume]
      regularizedMildTensorField ρ ε hε v := by
    simp only [regularizedMildTensor]
    exact MemLp.coeFn_toLp _
  have hdecomp :
      regularizedMildTensor ρ ε hε u - regularizedMildTensor ρ ε hε v = T₁ + T₂ := by
    apply Lp.ext
    filter_upwards [
      hregU, hregV, hT₁.coeFn_toLp, hT₂.coeFn_toLp,
      Lp.coeFn_sub (regularizedMildTensor ρ ε hε u)
        (regularizedMildTensor ρ ε hε v), Lp.coeFn_add T₁ T₂]
      with x huRep hvRep hT₁Rep hT₂Rep hsub hadd
    calc
      (regularizedMildTensor ρ ε hε u - regularizedMildTensor ρ ε hε v) x =
          (regularizedMildTensor ρ ε hε u x -
            regularizedMildTensor ρ ε hε v x) := hsub
      _ = regularizedMildTensorField ρ ε hε u x -
          regularizedMildTensorField ρ ε hε v x := by rw [huRep, hvRep]
      _ = T₁field x + T₂field x := by
        rw [regularizedMildTensorField, regularizedMildTensorField,
          regularizedTensorOuter_sub_identity]
        have hJsubx : regMollifyVector ρ ε hε du x =
            regMollifyVector ρ ε hε u x - regMollifyVector ρ ε hε v x := by
          have hduAE : du =ᵐ[volume]
              ((fun y => u y) - fun y => v y) := by
            filter_upwards [] with y
            rfl
          have hconvDu := regMollifyVector_congr_ae ρ ε hε hduAE
          have hJsub := regMollifyVector_sub ρ ε hε hu hv
          calc
            regMollifyVector ρ ε hε du x =
                regMollifyVector ρ ε hε ((fun y => u y) - fun y => v y) x :=
              congrFun hconvDu x
            _ = regMollifyVector ρ ε hε u x - regMollifyVector ρ ε hε v x := by
              simpa only [Pi.sub_apply] using congrFun hJsub x
        rw [← hJsubx]
        simp [T₁field, T₂field, mildTensorProductField, du]
      _ = (T₁ x + T₂ x) := by rw [hT₁Rep, hT₂Rep]
      _ = (T₁ + T₂) x := hadd.symm
  rw [hdecomp]
  calc
    ‖T₁ + T₂‖ ≤ ‖T₁‖ + ‖T₂‖ := norm_add_le _ _
    _ ≤ c * ‖u - v‖ * ‖u‖ + c * ‖v‖ * ‖u - v‖ :=
      add_le_add hT₁bound hT₂bound
    _ = c * (‖u‖ + ‖v‖) * ‖u - v‖ := by ring

end CKN.Leray

end
