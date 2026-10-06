/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.HeatPDE
public import LeanPool.CaffarelliKohnNirenberg.Foundation.GagliardoNirenberg
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.H1.Basic
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SpatialDerivSupport
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Heat Entropy

The squared regularized magnitude used in `lem:pv-heat-critical`.
-/

public section

open CKN

open MeasureTheory Filter
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The squared regularized magnitude used in `lem:pv-heat-critical`. -/
@[expose] def heatRegSq (η : ℝ) (v : Vec3) : ℝ :=
  (∑ i : Fin 3, v i ^ 2) + η ^ 2

/-- The coordinate dot product used by the entropy derivatives in
`lem:pv-heat-critical`. -/
@[expose] def heatRegDot (v w : Vec3) : ℝ :=
  ∑ i : Fin 3, v i * w i

/-- The regularized squared magnitude is differentiable, as used in the
entropy chain rules for `lem:pv-heat-critical`. -/
theorem heatRegSq_differentiableAt (η : ℝ) (v : Vec3) :
    DifferentiableAt ℝ (heatRegSq η) v := by
  unfold heatRegSq
  fun_prop

private theorem heatRegSq_fderiv (η : ℝ) (v w : Vec3) :
    fderiv ℝ (heatRegSq η) v w = 2 * heatRegDot v w := by
  unfold heatRegSq heatRegDot
  rw [fderiv_add_const, fderiv_fun_sum]
  · have hcoord (i : Fin 3) :
    fderiv ℝ (fun z : Vec3 => z i ^ 2) v w = 2 * v i * w i := by
      change fderiv ℝ ((fun z : Vec3 => z i) ^ 2) v w = _
      rw [fderiv_pow 2 (differentiableAt_apply i v)]
      rw [fderiv_apply (by fun_prop : DifferentiableAt ℝ (fun z : Vec3 => z) v) i]
      have hId : fderiv ℝ (fun z : Vec3 => z) v =
          ContinuousLinearMap.id ℝ Vec3 := by
        change fderiv ℝ id v = ContinuousLinearMap.id ℝ Vec3
        exact fderiv_id
      rw [hId]
      rw [ContinuousLinearMap.comp_id]
      change (2 • v i ^ (2 - 1)) * w i = 2 * v i * w i
      norm_num
    rw [_root_.sum_apply]
    simp_rw [hcoord]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · intro i hi
    fun_prop

/-- Positive regularization makes the squared magnitude strictly positive in
`lem:pv-heat-critical`. -/
theorem heatRegSq_pos {η : ℝ} (hη : 0 < η) (v : Vec3) :
    0 < heatRegSq η v := by
  unfold heatRegSq
  positivity

private theorem heatRegSq_rpow_fderiv {η p : ℝ} (hη : 0 < η)
    (v w : Vec3) :
    fderiv ℝ (fun z : Vec3 => heatRegSq η z ^ p) v w =
      p * heatRegSq η v ^ (p - 1) * (2 * heatRegDot v w) := by
  have hq : HasFDerivAt (heatRegSq η)
      (fderiv ℝ (heatRegSq η) v) v :=
    (heatRegSq_differentiableAt η v).hasFDerivAt
  have hpow : HasFDerivAt (fun z : Vec3 => heatRegSq η z ^ p)
      ((p * heatRegSq η v ^ (p - 1)) • fderiv ℝ (heatRegSq η) v) v :=
    hq.rpow_const (Or.inl (ne_of_gt (heatRegSq_pos hη v)))
  have hderiv := hpow.fderiv
  have hw := congrArg (fun D : Vec3 →L[ℝ] ℝ => D w) hderiv
  simpa [heatRegSq_fderiv] using hw

/-- A smooth regularization of `|v|^(3/2)` used in `lem:pv-heat-critical`. -/
@[expose] def heatRegG (η : ℝ) (v : Vec3) : ℝ :=
  heatRegSq η v ^ (3 / 4 : ℝ) - η ^ (3 / 2 : ℝ)

/-- The regularized `|v|v` entropy test used in `lem:pv-heat-critical`. -/
@[expose] def heatRegTest (η : ℝ) (v : Vec3) : Vec3 :=
  fun i => (heatRegSq η v ^ (1 / 2 : ℝ) - η) * v i

/-- The nonnegative convex potential paired with `heatRegTest`. -/
@[expose] def heatRegEnergy (η : ℝ) (v : Vec3) : ℝ :=
  (1 / 3 : ℝ) * heatRegSq η v ^ (3 / 2 : ℝ) -
    (η / 2) * heatRegSq η v + η ^ 3 / 6

/-- The regularized critical profile is smooth for positive regularization,
as used in `lem:pv-heat-critical`. -/
theorem heatRegG_contDiff {η : ℝ} (hη : 0 < η) :
    ContDiff ℝ (⊤ : ℕ∞) (heatRegG η) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (heatRegSq η) := by
    unfold heatRegSq
    fun_prop
  have hpow (p : ℝ) :
      ContDiff ℝ (⊤ : ℕ∞) (fun v : Vec3 => heatRegSq η v ^ p) :=
    hq.rpow_const_of_ne (p := p) fun v => ne_of_gt (heatRegSq_pos hη v)
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun v : Vec3 => heatRegSq η v ^ (3 / 4 : ℝ) - η ^ (3 / 2 : ℝ))
  exact (hpow (3 / 4 : ℝ)).sub contDiff_const

/-- The regularized entropy test is smooth in the vector variable. -/
theorem heatRegTest_contDiff {η : ℝ} (hη : 0 < η) :
    ContDiff ℝ (⊤ : ℕ∞) (heatRegTest η) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (heatRegSq η) := by
    unfold heatRegSq
    fun_prop
  have hroot : ContDiff ℝ (⊤ : ℕ∞)
      (fun v : Vec3 => heatRegSq η v ^ (1 / 2 : ℝ)) :=
    hq.rpow_const_of_ne (p := (1 / 2 : ℝ)) fun v =>
      ne_of_gt (heatRegSq_pos hη v)
  rw [contDiff_pi]
  intro i
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun v : Vec3 =>
      (heatRegSq η v ^ (1 / 2 : ℝ) - η) * v i)
  exact (hroot.sub contDiff_const).mul (contDiff_apply ℝ ℝ i)

/-- The regularized entropy potential is smooth in the vector variable, as used
in the energy argument for `lem:pv-heat-critical`. -/
theorem heatRegEnergy_contDiff {η : ℝ} (hη : 0 < η) :
    ContDiff ℝ (⊤ : ℕ∞) (heatRegEnergy η) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (heatRegSq η) := by
    unfold heatRegSq
    fun_prop
  have hthree : ContDiff ℝ (⊤ : ℕ∞)
      (fun v : Vec3 => heatRegSq η v ^ (3 / 2 : ℝ)) :=
    hq.rpow_const_of_ne (p := (3 / 2 : ℝ)) fun v =>
      ne_of_gt (heatRegSq_pos hη v)
  unfold heatRegEnergy
  exact ((contDiff_const.mul hthree).sub
    (contDiff_const.mul hq)).add contDiff_const

private theorem heatCoordinate_fderiv (i : Fin 3) (v w : Vec3) :
    fderiv ℝ (fun z : Vec3 => z i) v w = w i := by
  rw [fderiv_apply (by fun_prop : DifferentiableAt ℝ (fun z : Vec3 => z) v) i]
  have hId : fderiv ℝ (fun z : Vec3 => z) v =
      ContinuousLinearMap.id ℝ Vec3 := by
    change fderiv ℝ id v = ContinuousLinearMap.id ℝ Vec3
    exact fderiv_id
  rw [hId, ContinuousLinearMap.comp_id]
  rfl

/-- The derivative of the regularized entropy test. -/
theorem heatRegTest_fderiv {η : ℝ} (hη : 0 < η)
    (v w : Vec3) (i : Fin 3) :
    fderiv ℝ (fun z : Vec3 => heatRegTest η z i) v w =
      (heatRegSq η v ^ (1 / 2 : ℝ) - η) * w i +
        heatRegSq η v ^ (-(1 / 2 : ℝ)) * heatRegDot v w * v i := by
  unfold heatRegTest
  have hfactorDiff : DifferentiableAt ℝ
      (fun z : Vec3 => heatRegSq η z ^ (1 / 2 : ℝ)) v :=
    (heatRegSq_differentiableAt η v).rpow_const
      (Or.inl (ne_of_gt (heatRegSq_pos hη v)))
  have hfactorDeriv : fderiv ℝ
      (fun z : Vec3 => heatRegSq η z ^ (1 / 2 : ℝ) - η) v w =
        heatRegSq η v ^ (-(1 / 2 : ℝ)) * heatRegDot v w := by
    rw [fderiv_sub_const, heatRegSq_rpow_fderiv (p := (1 / 2 : ℝ)) hη]
    have hexp : (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) := by norm_num
    rw [hexp]
    ring
  rw [fderiv_fun_mul (hfactorDiff.sub_const η)
    (differentiableAt_apply i v)]
  have hleft := heatCoordinate_fderiv i v w
  have hright : fderiv ℝ (fun z : Vec3 =>
      heatRegSq η z ^ (1 / 2 : ℝ) - η) v w =
        heatRegSq η v ^ (-(1 / 2 : ℝ)) * heatRegDot v w := hfactorDeriv
  simp only [add_apply, smul_apply,
    smul_eq_mul]
  rw [hleft, hright]
  ring

/-- The regularized energy derivative pairs with the regularized test, as used
in `lem:pv-heat-critical`. -/
theorem heatRegEnergy_fderiv {η : ℝ} (hη : 0 < η)
    (v w : Vec3) :
    fderiv ℝ (heatRegEnergy η) v w =
      (heatRegSq η v ^ (1 / 2 : ℝ) - η) * heatRegDot v w := by
  unfold heatRegEnergy
  have hqdiff := heatRegSq_differentiableAt η v
  have hhalf : DifferentiableAt ℝ
      (fun z : Vec3 => heatRegSq η z ^ (1 / 2 : ℝ)) v :=
    hqdiff.rpow_const (Or.inl (ne_of_gt (heatRegSq_pos hη v)))
  have hthree : DifferentiableAt ℝ
      (fun z : Vec3 => heatRegSq η z ^ (3 / 2 : ℝ)) v :=
    hqdiff.rpow_const (Or.inl (ne_of_gt (heatRegSq_pos hη v)))
  have hleft : DifferentiableAt ℝ
      (fun z : Vec3 => (1 / 3 : ℝ) * heatRegSq η z ^ (3 / 2 : ℝ)) v :=
    hthree.const_mul _
  have hright : DifferentiableAt ℝ
      (fun z : Vec3 => (η / 2) * heatRegSq η z) v :=
    hqdiff.const_mul _
  change fderiv ℝ (fun z : Vec3 =>
      ((1 / 3 : ℝ) * heatRegSq η z ^ (3 / 2 : ℝ) -
        (η / 2) * heatRegSq η z) + η ^ 3 / 6) v w = _
  rw [fderiv_add_const]
  change fderiv ℝ
      ((fun z : Vec3 => (1 / 3 : ℝ) * heatRegSq η z ^ (3 / 2 : ℝ)) -
        (fun z : Vec3 => (η / 2) * heatRegSq η z)) v w = _
  rw [fderiv_sub hleft hright]
  rw [fderiv_const_mul hthree]
  rw [fderiv_const_mul hqdiff]
  simp only [sub_apply, smul_apply, smul_eq_mul]
  rw [heatRegSq_rpow_fderiv (p := (3 / 2 : ℝ)) hη,
    heatRegSq_fderiv]
  have hexp : (3 / 2 : ℝ) - 1 = (1 / 2 : ℝ) := by norm_num
  rw [hexp]
  ring

/-- The regularized critical profile's vector derivative, used in the spatial
chain rule for `lem:pv-heat-critical`. -/
theorem heatRegG_fderiv {η : ℝ} (hη : 0 < η) (v w : Vec3) :
    fderiv ℝ (heatRegG η) v w =
      (3 / 2 : ℝ) * heatRegSq η v ^ (-(1 / 4 : ℝ)) * heatRegDot v w := by
  unfold heatRegG
  rw [fderiv_sub_const, heatRegSq_rpow_fderiv (p := (3 / 4 : ℝ)) hη]
  have hexp : (3 / 4 : ℝ) - 1 = -(1 / 4 : ℝ) := by norm_num
  rw [hexp]
  ring

/-- The regularized critical profile is differentiable for positive
regularization in `lem:pv-heat-critical`. -/
theorem heatRegG_differentiableAt {η : ℝ} (hη : 0 < η)
    (v : Vec3) : DifferentiableAt ℝ (heatRegG η) v := by
  unfold heatRegG
  exact ((heatRegSq_differentiableAt η v).rpow_const
    (Or.inl (ne_of_gt (heatRegSq_pos hη v)))).sub_const _

/-- The spatial derivative of the regularized critical profile along a smooth
vector field, used in the dissipation estimate for `lem:pv-heat-critical`. -/
theorem heatRegG_comp_fderiv {η : ℝ} (hη : 0 < η)
    {h : Vec3 → Vec3} {x v : Vec3} (hh : DifferentiableAt ℝ h x) :
    fderiv ℝ (fun y => heatRegG η (h y)) x v =
      (3 / 2 : ℝ) * heatRegSq η (h x) ^ (-(1 / 4 : ℝ)) *
        heatRegDot (h x) (fderiv ℝ h x v) := by
  change fderiv ℝ (heatRegG η ∘ h) x v = _
  have houter := (heatRegG_differentiableAt hη (h x)).hasFDerivAt
  have hcomp := houter.comp x hh.hasFDerivAt
  have hv := congrArg (fun D : Vec3 →L[ℝ] ℝ => D v) hcomp.fderiv
  calc
    fderiv ℝ (heatRegG η ∘ h) x v =
        (fderiv ℝ (heatRegG η) (h x) ∘SL fderiv ℝ h x) v := hv
    _ = fderiv ℝ (heatRegG η) (h x) (fderiv ℝ h x v) := rfl
    _ = (3 / 2 : ℝ) * heatRegSq η (h x) ^ (-(1 / 4 : ℝ)) *
          heatRegDot (h x) (fderiv ℝ h x v) := by
            rw [heatRegG_fderiv hη]

/-- The regularized test pairs with the vector derivative of its energy in
`lem:pv-heat-critical`. -/
theorem heatRegTest_pairing {η : ℝ} (v w : Vec3) :
    ∑ i : Fin 3, heatRegTest η v i * w i =
      (heatRegSq η v ^ (1 / 2 : ℝ) - η) * heatRegDot v w := by
  unfold heatRegTest heatRegDot
  calc
    ∑ i : Fin 3, (heatRegSq η v ^ (1 / 2 : ℝ) - η) * v i * w i =
        ∑ i : Fin 3, (heatRegSq η v ^ (1 / 2 : ℝ) - η) * (v i * w i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = (heatRegSq η v ^ (1 / 2 : ℝ) - η) * ∑ i : Fin 3, v i * w i := by
          rw [Finset.mul_sum]

private theorem heatRegDot_sq_le (v w : Vec3) :
    heatRegDot v w ^ 2 ≤
      (∑ i : Fin 3, v i ^ 2) * (∑ i : Fin 3, w i ^ 2) := by
  simpa [heatRegDot] using
    (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
      (fun i => v i) (fun i => w i))

/-- The entropy test derivative has a nonnegative quadratic dissipation. -/
theorem heatRegTest_dissipation_identity {η : ℝ} (hη : 0 < η)
    (v w : Vec3) :
    ∑ i : Fin 3, fderiv ℝ (fun z : Vec3 => heatRegTest η z i) v w * w i =
      (heatRegSq η v ^ (1 / 2 : ℝ) - η) * ∑ i : Fin 3, w i ^ 2 +
        heatRegSq η v ^ (-(1 / 2 : ℝ)) * (heatRegDot v w) ^ 2 := by
  calc
    ∑ i : Fin 3, fderiv ℝ (fun z : Vec3 => heatRegTest η z i) v w * w i =
        ∑ i : Fin 3,
          ((heatRegSq η v ^ (1 / 2 : ℝ) - η) * w i ^ 2 +
            heatRegSq η v ^ (-(1 / 2 : ℝ)) * heatRegDot v w * (v i * w i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [heatRegTest_fderiv hη]
              ring
    _ = (heatRegSq η v ^ (1 / 2 : ℝ) - η) *
          ∑ i : Fin 3, w i ^ 2 +
          heatRegSq η v ^ (-(1 / 2 : ℝ)) * heatRegDot v w *
            ∑ i : Fin 3, v i * w i := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = (heatRegSq η v ^ (1 / 2 : ℝ) - η) * ∑ i : Fin 3, w i ^ 2 +
          heatRegSq η v ^ (-(1 / 2 : ℝ)) * (heatRegDot v w) ^ 2 := by
              rw [heatRegDot]
              ring

/-- The entropy dissipation controls the regularized weighted gradient. -/
theorem heatRegTest_dissipation_lower {η : ℝ} (hη : 0 < η)
    (v w : Vec3) :
    (heatRegSq η v ^ (1 / 2 : ℝ) - η) * ∑ i : Fin 3, w i ^ 2 ≤
      ∑ i : Fin 3,
        fderiv ℝ (fun z : Vec3 => heatRegTest η z i) v w * w i := by
  rw [heatRegTest_dissipation_identity hη]
  exact le_add_of_nonneg_right
    (mul_nonneg (Real.rpow_nonneg
      (le_of_lt (heatRegSq_pos hη v)) _) (sq_nonneg _))

/-- The regularized Euclidean root is at least its positive offset. -/
theorem heatReg_root_ge_eta {η : ℝ} (hη : 0 < η) (v : Vec3) :
    η ≤ heatRegSq η v ^ (1 / 2 : ℝ) := by
  have hR : 0 ≤ ∑ i : Fin 3, v i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg (v i)
  have hηq : η ^ 2 ≤ heatRegSq η v := by
    unfold heatRegSq
    nlinarith only [hR]
  have hsqrt := Real.sqrt_le_sqrt hηq
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hη] at hsqrt
  rw [Real.sqrt_eq_rpow (heatRegSq η v)] at hsqrt
  exact hsqrt

private theorem heatReg_rpow_half_sq {η : ℝ} (hη : 0 < η) (v : Vec3) :
    (heatRegSq η v ^ (1 / 2 : ℝ)) ^ 2 = heatRegSq η v := by
  rw [← Real.sqrt_eq_rpow (heatRegSq η v)]
  exact Real.sq_sqrt (le_of_lt (heatRegSq_pos hη v))

/-- A nonnegative factorization of the regularized entropy potential. -/
theorem heatRegEnergy_factor {η : ℝ} (hη : 0 < η)
    (v : Vec3) :
    heatRegEnergy η v =
      (heatRegSq η v ^ (1 / 2 : ℝ) - η) ^ 2 *
        (2 * heatRegSq η v ^ (1 / 2 : ℝ) + η) / 6 := by
  let r : ℝ := heatRegSq η v ^ (1 / 2 : ℝ)
  have hr : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos (heatRegSq_pos hη v) _
  have hrsq : r ^ 2 = heatRegSq η v := by
    dsimp [r]
    exact heatReg_rpow_half_sq hη v
  have hthree : heatRegSq η v ^ (3 / 2 : ℝ) = r ^ 3 := by
    change heatRegSq η v ^ (3 / 2 : ℝ) =
      (heatRegSq η v ^ (1 / 2 : ℝ)) ^ (3 : ℕ)
    rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) * 3 by norm_num,
      ← Real.rpow_natCast, ← Real.rpow_mul
        (le_of_lt (heatRegSq_pos hη v))]
    congr 1
  change heatRegEnergy η v =
    (heatRegSq η v ^ (1 / 2 : ℝ) - η) ^ 2 *
      (2 * heatRegSq η v ^ (1 / 2 : ℝ) + η) / 6
  unfold heatRegEnergy
  rw [hthree]
  have hrval : heatRegSq η v ^ (1 / 2 : ℝ) = r := rfl
  rw [hrval, ← hrsq]
  ring

/-- The regularized entropy potential is nonnegative. -/
theorem heatRegEnergy_nonneg {η : ℝ} (hη : 0 < η)
    (v : Vec3) : 0 ≤ heatRegEnergy η v := by
  rw [heatRegEnergy_factor hη]
  have hroot : 0 ≤ heatRegSq η v ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (le_of_lt (heatRegSq_pos hη v)) _
  have hsum : 0 ≤ 2 * heatRegSq η v ^ (1 / 2 : ℝ) + η :=
    add_nonneg (mul_nonneg (by norm_num) hroot) hη.le
  exact div_nonneg (mul_nonneg (sq_nonneg _) hsum) (by norm_num)

/-- The square of the regularized `|v|^(3/2)` is controlled by its entropy. -/
theorem heatRegG_sq_le_energy {η : ℝ} (hη : 0 < η)
    (v : Vec3) : (heatRegG η v) ^ 2 ≤ 27 * heatRegEnergy η v := by
  let r : ℝ := heatRegSq η v ^ (1 / 2 : ℝ)
  let a : ℝ := Real.sqrt r
  let c : ℝ := Real.sqrt η
  have hr : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos (heatRegSq_pos hη v) _
  have ha : 0 < a := Real.sqrt_pos.2 hr
  have hc : 0 < c := Real.sqrt_pos.2 hη
  have hηr : η ≤ r := by
    dsimp [r]
    exact heatReg_root_ge_eta hη v
  have hac : c ≤ a := by
    apply Real.sqrt_le_sqrt
    exact hηr
  have ha2 : a ^ 2 = r := Real.sq_sqrt hr.le
  have hc2 : c ^ 2 = η := Real.sq_sqrt hη.le
  have hrpow : r ^ (3 / 2 : ℝ) = a ^ 3 := by
    change r ^ (3 / 2 : ℝ) = (Real.sqrt r) ^ (3 : ℕ)
    rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) * 3 by norm_num,
      ← Real.rpow_natCast, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hr.le]
    congr 1
  have hηpow : η ^ (3 / 2 : ℝ) = c ^ 3 := by
    change η ^ (3 / 2 : ℝ) = (Real.sqrt η) ^ (3 : ℕ)
    rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) * 3 by norm_num,
      ← Real.rpow_natCast, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hη.le]
    congr 1
  have hqpow : heatRegSq η v ^ (3 / 4 : ℝ) = r ^ (3 / 2 : ℝ) := by
    change heatRegSq η v ^ (3 / 4 : ℝ) =
      (heatRegSq η v ^ (1 / 2 : ℝ)) ^ (3 / 2 : ℝ)
    rw [show (3 / 4 : ℝ) = (1 / 2 : ℝ) * (3 / 2 : ℝ) by norm_num,
      ← Real.rpow_mul (le_of_lt (heatRegSq_pos hη v))]
  have hdiff : heatRegSq η v ^ (3 / 4 : ℝ) - η ^ (3 / 2 : ℝ) =
      (a - c) * (a ^ 2 + a * c + c ^ 2) := by
    rw [hqpow, hrpow, hηpow]
    ring
  have hfactor : r - η = (a - c) * (a + c) := by
    rw [← ha2, ← hc2]
    ring
  have hpoly : a ^ 2 + a * c + c ^ 2 ≤ 3 * a ^ 2 := by
    have hacmul : a * c ≤ a ^ 2 := by
      calc
        a * c ≤ a * a := mul_le_mul_of_nonneg_left hac ha.le
        _ = a ^ 2 := by ring
    have hc2le : c ^ 2 ≤ a ^ 2 :=
      (sq_le_sq₀ hc.le ha.le).2 hac
    nlinarith only [hacmul, hc2le]
  have hpolyNonneg : 0 ≤ a ^ 2 + a * c + c ^ 2 := by positivity
  have hsumNonneg : 0 ≤ a + c := by positivity
  have hpolySq : (a ^ 2 + a * c + c ^ 2) ^ 2 ≤ (3 * a ^ 2) ^ 2 :=
    pow_le_pow_left₀ hpolyNonneg hpoly 2
  have hsumSq : a ^ 2 ≤ (a + c) ^ 2 := by
    exact (sq_le_sq₀ ha.le (add_nonneg ha.le hc.le)).2
      (le_add_of_nonneg_right hc.le)
  have hbase : (3 * a ^ 2) ^ 2 ≤ 9 * a ^ 2 * (a + c) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hsumSq (by positivity : 0 ≤ 9 * a ^ 2)
    calc
      (3 * a ^ 2) ^ 2 = 9 * a ^ 2 * a ^ 2 := by ring
      _ ≤ 9 * a ^ 2 * (a + c) ^ 2 := hmul
  have hpolySq' : (a ^ 2 + a * c + c ^ 2) ^ 2 ≤
      9 * a ^ 2 * (a + c) ^ 2 := hpolySq.trans hbase
  have hcore :
      (a - c) ^ 2 * (a ^ 2 + a * c + c ^ 2) ^ 2 ≤
        9 * r * (r - η) ^ 2 := by
    calc
      (a - c) ^ 2 * (a ^ 2 + a * c + c ^ 2) ^ 2 ≤
          (a - c) ^ 2 * (9 * a ^ 2 * (a + c) ^ 2) :=
            mul_le_mul_of_nonneg_left hpolySq' (sq_nonneg _)
      _ = 9 * r * (r - η) ^ 2 := by rw [hfactor, ← ha2]; ring
  have htwor : 2 * r ≤ 2 * r + η := by linarith only [hη]
  have hE : 9 * r * (r - η) ^ 2 ≤
      27 * ((r - η) ^ 2 * (2 * r + η) / 6) := by
    calc
      9 * r * (r - η) ^ 2 = (9 / 2 : ℝ) * (2 * r) * (r - η) ^ 2 := by ring
      _ ≤ (9 / 2 : ℝ) * (2 * r + η) * (r - η) ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htwor (by norm_num)) (sq_nonneg _)
      _ = 27 * ((r - η) ^ 2 * (2 * r + η) / 6) := by ring
  calc
    (heatRegG η v) ^ 2 =
        (a - c) ^ 2 * (a ^ 2 + a * c + c ^ 2) ^ 2 := by
          rw [heatRegG, hdiff]
          ring
    _ ≤ 9 * r * (r - η) ^ 2 := hcore
    _ ≤ 27 * ((r - η) ^ 2 * (2 * r + η) / 6) := hE
    _ = 27 * heatRegEnergy η v := by
      rw [heatRegEnergy_factor hη]

/-- The negative half power is the reciprocal square root used in the entropy
derivative estimates for `lem:pv-heat-critical`. -/
theorem heatReg_inv_rpow_half {η : ℝ} (hη : 0 < η) (v : Vec3) :
    heatRegSq η v ^ (-(1 / 2 : ℝ)) =
      (heatRegSq η v ^ (1 / 2 : ℝ))⁻¹ := by
  rw [Real.rpow_neg (le_of_lt (heatRegSq_pos hη v))]

private theorem heatReg_weight_bound {η : ℝ} (hη : 0 < η) (v : Vec3) :
    heatRegSq η v ^ (-(1 / 2 : ℝ)) *
      (∑ i : Fin 3, v i ^ 2) ≤
        2 * (heatRegSq η v ^ (1 / 2 : ℝ) - η) := by
  let R : ℝ := ∑ i : Fin 3, v i ^ 2
  let r : ℝ := heatRegSq η v ^ (1 / 2 : ℝ)
  have hR : 0 ≤ R := by
    dsimp [R]
    exact Finset.sum_nonneg fun i _ => sq_nonneg (v i)
  have hrpos : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos (heatRegSq_pos hη v) _
  have hrη : η ≤ r := by
    simpa [r] using heatReg_root_ge_eta hη v
  have hrsq : r ^ 2 = heatRegSq η v := by
    dsimp [r]
    exact heatReg_rpow_half_sq hη v
  have hRform : R = (r - η) * (r + η) := by
    have hq : heatRegSq η v = R + η ^ 2 := by
      simp [heatRegSq, R, add_comm]
    rw [hq] at hrsq
    dsimp [R]
    nlinarith only [hrsq]
  calc
    heatRegSq η v ^ (-(1 / 2 : ℝ)) * R = R / r := by
      rw [heatReg_inv_rpow_half hη v]
      dsimp [r]
      ring
    _ = ((r - η) * (r + η)) / r := by rw [hRform]
    _ ≤ (2 * (r - η) * r) / r := by
      apply div_le_div_of_nonneg_right ?_ (le_of_lt hrpos)
      have hsum : r + η ≤ 2 * r := by nlinarith only [hrη]
      calc
        (r - η) * (r + η) ≤ (r - η) * (2 * r) :=
          mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hrη)
        _ = 2 * (r - η) * r := by ring
    _ = 2 * (r - η) := by
      field_simp [hrpos.ne']

/-- The gradient of the regularized `|v|^(3/2)` is controlled by entropy dissipation. -/
theorem heatReg_gradient_bound {η : ℝ} (hη : 0 < η)
    (v w : Vec3) :
    (fderiv ℝ (heatRegG η) v w) ^ 2 ≤
      (9 / 2 : ℝ) * (heatRegSq η v ^ (1 / 2 : ℝ) - η) *
        ∑ i : Fin 3, w i ^ 2 := by
  let q : ℝ := heatRegSq η v
  let d : ℝ := heatRegDot v w
  let W : ℝ := ∑ i : Fin 3, w i ^ 2
  have hqpos : 0 < q := by dsimp [q]; exact heatRegSq_pos hη v
  have hW : 0 ≤ W := by
    dsimp [W]
    exact Finset.sum_nonneg fun i _ => sq_nonneg (w i)
  have hd : d ^ 2 ≤ (∑ i : Fin 3, v i ^ 2) * W := by
    simpa [d, W] using heatRegDot_sq_le v w
  have hrpow : (q ^ (-(1 / 4 : ℝ))) ^ 2 = q ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hqpos.le]
    norm_num
  rw [heatRegG_fderiv hη]
  calc
    ((3 / 2 : ℝ) * q ^ (-(1 / 4 : ℝ)) * d) ^ 2 =
        (9 / 4 : ℝ) * q ^ (-(1 / 2 : ℝ)) * d ^ 2 := by
          have hm : ((3 / 2 : ℝ) * q ^ (-(1 / 4 : ℝ)) * d) ^ 2 =
              (3 / 2 : ℝ) ^ 2 * (q ^ (-(1 / 4 : ℝ))) ^ 2 * d ^ 2 := by ring
          rw [hm, hrpow]
          norm_num
    _ ≤ (9 / 4 : ℝ) *
        (2 * (heatRegSq η v ^ (1 / 2 : ℝ) - η) * W) := by
          have hcore : q ^ (-(1 / 2 : ℝ)) * d ^ 2 ≤
              2 * (heatRegSq η v ^ (1 / 2 : ℝ) - η) * W := by
            calc
              q ^ (-(1 / 2 : ℝ)) * d ^ 2 ≤
                  q ^ (-(1 / 2 : ℝ)) *
                    ((∑ i : Fin 3, v i ^ 2) * W) :=
                      mul_le_mul_of_nonneg_left hd (by positivity)
              _ = (q ^ (-(1 / 2 : ℝ)) *
                    (∑ i : Fin 3, v i ^ 2)) * W := by ring
              _ ≤ 2 * (heatRegSq η v ^ (1 / 2 : ℝ) - η) * W := by
                    exact mul_le_mul_of_nonneg_right
                      (heatReg_weight_bound hη v) hW
          calc
            (9 / 4 : ℝ) * q ^ (-(1 / 2 : ℝ)) * d ^ 2 =
                (9 / 4 : ℝ) * (q ^ (-(1 / 2 : ℝ)) * d ^ 2) := by ring
            _ ≤ (9 / 4 : ℝ) *
                (2 * (heatRegSq η v ^ (1 / 2 : ℝ) - η) * W) :=
                  mul_le_mul_of_nonneg_left hcore
                    (show 0 ≤ (9 / 4 : ℝ) by norm_num)
    _ = (9 / 2 : ℝ) *
        (heatRegSq η v ^ (1 / 2 : ℝ) - η) * W := by ring

/-- A quadratic bound on the regularized entropy for bounded vector fields. -/
theorem heatRegEnergy_le_mul_sum_sq {η M : ℝ} (hη : 0 < η)
    (hM : 0 ≤ M) (v : Vec3) (hv : vec3EuclideanNorm v ≤ M) :
    heatRegEnergy η v ≤ ((3 * η + 2 * M) / 6) *
      ∑ i : Fin 3, v i ^ 2 := by
  let q : ℝ := ∑ i : Fin 3, v i ^ 2
  let r : ℝ := heatRegSq η v ^ (1 / 2 : ℝ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos (heatRegSq_pos hη v) _
  have hrη : η ≤ r := by
    simpa [r] using heatReg_root_ge_eta hη v
  have hrsq : r ^ 2 = q + η ^ 2 := by
    dsimp [r, q]
    rw [heatReg_rpow_half_sq hη v]
    simp [heatRegSq, add_comm]
  have hqM : q ≤ M ^ 2 := by
    have hvSq := pow_le_pow_left₀ (vec3EuclideanNorm_nonneg v) hv 2
    unfold vec3EuclideanNorm at hvSq
    rw [Real.sq_sqrt hq] at hvSq
    exact hvSq
  have hrM : r ≤ η + M := by
    apply (sq_le_sq₀ hr.le (add_nonneg hη.le hM)).1
    calc
      r ^ 2 = q + η ^ 2 := hrsq
      _ = η ^ 2 + q := by ring
      _ ≤ η ^ 2 + M ^ 2 := add_le_add_right hqM (η ^ 2)
      _ = M ^ 2 + η ^ 2 := by ring
      _ ≤ (η + M) ^ 2 := by
        nlinarith only [hη, hM, mul_nonneg hη.le hM]
  have hd : 0 ≤ r - η := sub_nonneg.mpr hrη
  have hfactor : q = (r - η) * (r + η) := by
    rw [show q = r ^ 2 - η ^ 2 by nlinarith only [hrsq]]
    ring
  have hdSq : (r - η) ^ 2 ≤ q := by
    have hrle : r - η ≤ r + η := by linarith only [hη]
    calc
      (r - η) ^ 2 = (r - η) * (r - η) := by ring
      _ ≤ (r - η) * (r + η) :=
        mul_le_mul_of_nonneg_left hrle hd
      _ = q := hfactor.symm
  have hcoeff : 0 ≤ 2 * r + η := by positivity
  have hcoeff' : 2 * r + η ≤ 3 * η + 2 * M := by
    nlinarith only [hrM]
  rw [heatRegEnergy_factor hη]
  calc
    (r - η) ^ 2 * (2 * r + η) / 6 ≤
        q * (2 * r + η) / 6 := by
          apply div_le_div_of_nonneg_right ?_ (by norm_num : (0 : ℝ) ≤ 6)
          exact mul_le_mul_of_nonneg_right hdSq hcoeff
    _ ≤ q * (3 * η + 2 * M) / 6 := by
          apply div_le_div_of_nonneg_right ?_ (by norm_num : (0 : ℝ) ≤ 6)
          exact mul_le_mul_of_nonneg_left hcoeff' hq
    _ = ((3 * η + 2 * M) / 6) * q := by ring
    _ = ((3 * η + 2 * M) / 6) * ∑ i : Fin 3, v i ^ 2 := by rfl

/-- The regularized root increment is bounded by the Euclidean vector norm. -/
theorem heatReg_root_sub_eta_le_norm {η : ℝ} (hη : 0 < η)
    (v : Vec3) :
    heatRegSq η v ^ (1 / 2 : ℝ) - η ≤ vec3EuclideanNorm v := by
  let q : ℝ := ∑ i : Fin 3, v i ^ 2
  let r : ℝ := heatRegSq η v ^ (1 / 2 : ℝ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos (heatRegSq_pos hη v) _
  have hrη : η ≤ r := by simpa [r] using heatReg_root_ge_eta hη v
  have hrsq : r ^ 2 = q + η ^ 2 := by
    dsimp [r, q]
    rw [heatReg_rpow_half_sq hη v]
    simp [heatRegSq, add_comm]
  have hd : 0 ≤ r - η := sub_nonneg.mpr hrη
  have hfactor : q = (r - η) * (r + η) := by
    rw [show q = r ^ 2 - η ^ 2 by nlinarith only [hrsq]]
    ring
  have hdSq : (r - η) ^ 2 ≤ q := by
    have hrle : r - η ≤ r + η := by linarith only [hη]
    calc
      (r - η) ^ 2 = (r - η) * (r - η) := by ring
      _ ≤ (r - η) * (r + η) :=
        mul_le_mul_of_nonneg_left hrle hd
      _ = q := hfactor.symm
  have hdsqrt : r - η ≤ Real.sqrt q := by
    have hsq : (r - η) ^ 2 ≤ (Real.sqrt q) ^ 2 := by
      rw [Real.sq_sqrt hq]
      exact hdSq
    nlinarith only [hsq, hd, Real.sqrt_nonneg q]
  have hout : r - η ≤ vec3EuclideanNorm v := by
    simpa [vec3EuclideanNorm, q] using hdsqrt
  simpa [r] using hout

/-- Each regularized entropy-test component is bounded by the squared vector norm. -/
theorem heatRegTest_abs_le_norm_sq {η : ℝ} (hη : 0 < η) (v : Vec3)
    (i : Fin 3) : |heatRegTest η v i| ≤ vec3EuclideanNorm v ^ 2 := by
  rw [heatRegTest, abs_mul,
    abs_of_nonneg (sub_nonneg.mpr (heatReg_root_ge_eta hη v))]
  calc
    _ ≤ vec3EuclideanNorm v * |v i| :=
      mul_le_mul_of_nonneg_right (heatReg_root_sub_eta_le_norm hη v)
        (abs_nonneg _)
    _ ≤ vec3EuclideanNorm v ^ 2 := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left (abs_apply_le_vec3EuclideanNorm v i)
        (vec3EuclideanNorm_nonneg v)

end ESS

end
