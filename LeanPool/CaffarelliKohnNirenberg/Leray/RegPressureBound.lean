/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureSpaceTimeLp
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Space-time pressure bounds for the regularized tensor

The Riesz pressure operator transfers the `L^{5/3}` tensor estimate to
pressure. On a finite time slab, interpolation between the tensor `L¹` and
`L^{5/3}` estimates gives the `L^{3/2}` pressure bound.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The regularized transport tensor in space-time coordinates, used by
`def:riesz-pressure`. -/
@[expose]
def regPressureSpaceTimeTensor (J U : Vec3 × ℝ → Vec3) :
    Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j z => J z i * U z j

private theorem regPressure_product_tensor_memLp_fiveThirds
    {J U : Vec3 × ℝ → Vec3}
    (hJ : ∀ i, MemLp (fun z => J z i) (ENNReal.ofReal (10 / 3 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    (hU : ∀ j, MemLp (fun z => U z j) (ENNReal.ofReal (10 / 3 : ℝ))
      (volume : Measure (Vec3 × ℝ))) :
    ∀ i j, MemLp (regPressureSpaceTimeTensor J U i j)
      (ENNReal.ofReal (5 / 3 : ℝ)) (volume : Measure (Vec3 × ℝ)) := by
  have : ENNReal.HolderTriple (ENNReal.ofReal (10 / 3 : ℝ))
      (ENNReal.ofReal (10 / 3 : ℝ)) (ENNReal.ofReal (5 / 3 : ℝ)) := by
    have h : (10 / 3 : ℝ).HolderTriple (10 / 3 : ℝ) (5 / 3 : ℝ) :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    exact h.ennrealOfReal
  intro i j
  change MemLp (fun z : Vec3 × ℝ => J z i * U z j)
    (ENNReal.ofReal (5 / 3 : ℝ)) (volume : Measure (Vec3 × ℝ))
  exact (hJ i).mul (hU j)

/-- The global tensor `L^{5/3}` estimate follows from the two velocity
`L^{10/3}` bounds in `lem:reg-ten-thirds`. -/
theorem regPressure_regularized_fiveThirds_bound
    (J U : Vec3 × ℝ → Vec3)
    (hJ : ∀ i, MemLp (fun z => J z i) (ENNReal.ofReal (10 / 3 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    (hU : ∀ j, MemLp (fun z => U z j) (ENNReal.ofReal (10 / 3 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    (BJ BU : ℝ) (hBJ : 0 ≤ BJ) (hBU : 0 ≤ BU)
    (hJbound : ∀ i,
      eLpNorm (fun z => J z i) (ENNReal.ofReal (10 / 3 : ℝ))
        (volume : Measure (Vec3 × ℝ)) ≤ ENNReal.ofReal BJ)
    (hUbound : ∀ j,
      eLpNorm (fun z => U z j) (ENNReal.ofReal (10 / 3 : ℝ))
        (volume : Measure (Vec3 × ℝ)) ≤ ENNReal.ofReal BU) :
    ∃ hF : ∀ i j, MemLp (regPressureSpaceTimeTensor J U i j)
        (ENNReal.ofReal (5 / 3 : ℝ)) (volume : Measure (Vec3 × ℝ)),
      ‖rieszPressureSpaceTimeClass (5 / 3 : ℝ) (by norm_num)
        (rieszPressureSpaceTimeTensorToLp (5 / 3 : ℝ) (by norm_num)
          (regPressureSpaceTimeTensor J U) hF)‖ ≤
        9 * rieszPressureOperatorBound (5 / 3 : ℝ) (by norm_num) * (BJ * BU) := by
  let F := regPressureSpaceTimeTensor J U
  let hF := regPressure_product_tensor_memLp_fiveThirds hJ hU
  have hFbound (i j : Fin 3) :
      eLpNorm (F i j) (ENNReal.ofReal (5 / 3 : ℝ))
        (volume : Measure (Vec3 × ℝ)) ≤ ENNReal.ofReal (BJ * BU) := by
    have : ENNReal.HolderTriple (ENNReal.ofReal (10 / 3 : ℝ))
        (ENNReal.ofReal (10 / 3 : ℝ)) (ENNReal.ofReal (5 / 3 : ℝ)) := by
      have h : (10 / 3 : ℝ).HolderTriple (10 / 3 : ℝ) (5 / 3 : ℝ) :=
        ⟨by norm_num, by norm_num, by norm_num⟩
      exact h.ennrealOfReal
    have hHolder := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
      (p := ENNReal.ofReal (10 / 3 : ℝ))
      (q := ENNReal.ofReal (10 / 3 : ℝ))
      (r := ENNReal.ofReal (5 / 3 : ℝ))
      (fun a b : ℝ => a * b) 1 continuous_mul
      (hJ i).aestronglyMeasurable (hU j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        simp [Real.norm_eq_abs])
    calc
      eLpNorm (F i j) (ENNReal.ofReal (5 / 3 : ℝ))
          (volume : Measure (Vec3 × ℝ)) ≤
        eLpNorm (fun z => J z i) (ENNReal.ofReal (10 / 3 : ℝ))
          (volume : Measure (Vec3 × ℝ)) *
        eLpNorm (fun z => U z j) (ENNReal.ofReal (10 / 3 : ℝ))
          (volume : Measure (Vec3 × ℝ)) := by
        change eLpNorm (fun z => J z i * U z j) (ENNReal.ofReal (5 / 3 : ℝ))
          (volume : Measure (Vec3 × ℝ)) ≤ _
        simpa [ENNReal.smul_def, one_mul] using hHolder
      _ ≤ ENNReal.ofReal BJ * ENNReal.ofReal BU :=
        mul_le_mul (hJbound i) (hUbound j) (by positivity) (by positivity)
      _ = ENNReal.ofReal (BJ * BU) := by
        rw [← ENNReal.ofReal_mul hBJ]
  refine ⟨hF, ?_⟩
  let r : ℝ := 5 / 3
  let hr : 1 < r := by norm_num [r]
  let G := rieszPressureSpaceTimeTensorToLp r hr F hF
  have hRiesz : ‖rieszPressureSpaceTimeClass r hr G‖ ≤
      rieszPressureOperatorBound r hr *
        ∑ i : Fin 3, ∑ j : Fin 3, ‖G i j‖ := by
    simpa [G] using rieszPressureSpaceTimeClass_norm_le r hr
      (rieszPressureSpaceTimeTensorToLp r hr F hF)
  have hComponent (i j : Fin 3) : ‖G i j‖ ≤ BJ * BU := by
    have : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    change ‖(hF i j).toLp (F i j)‖ ≤ BJ * BU
    rw [Lp.norm_toLp]
    calc
      ENNReal.toReal (eLpNorm (F i j) (ENNReal.ofReal (5 / 3 : ℝ))
          (volume : Measure (Vec3 × ℝ))) ≤ ENNReal.toReal (ENNReal.ofReal (BJ * BU)) :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hFbound i j)
      _ = BJ * BU := ENNReal.toReal_ofReal (mul_nonneg hBJ hBU)
  have hOp : 0 ≤ rieszPressureOperatorBound r hr := by
    exact le_trans (norm_nonneg _) <|
      rieszPressureSpaceTimeComponent_norm_le r hr (0 : Fin 3) (0 : Fin 3)
  change ‖rieszPressureSpaceTimeClass r hr G‖ ≤
    9 * rieszPressureOperatorBound r hr * (BJ * BU)
  calc
    ‖rieszPressureSpaceTimeClass r hr G‖ ≤
        rieszPressureOperatorBound r hr *
          ∑ i : Fin 3, ∑ j : Fin 3, ‖G i j‖ := hRiesz
    _ ≤ rieszPressureOperatorBound r hr *
          ∑ i : Fin 3, ∑ j : Fin 3, BJ * BU := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact hComponent i j
      · exact hOp
    _ = 9 * rieszPressureOperatorBound r hr * (BJ * BU) := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

private theorem regPressure_interpolate_one_fiveThirds
    {α : Type} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hF1 : MemLp f (ENNReal.ofReal (1 : ℝ)) μ)
    (hF53 : MemLp f (ENNReal.ofReal (5 / 3 : ℝ)) μ)
    (B1 B53 : ℝ) (hB1 : 0 ≤ B1) (hB53 : 0 ≤ B53)
    (hBound1 : eLpNorm f (ENNReal.ofReal (1 : ℝ)) μ ≤ ENNReal.ofReal B1)
    (hBound53 : eLpNorm f (ENNReal.ofReal (5 / 3 : ℝ)) μ ≤ ENNReal.ofReal B53) :
    MemLp f (ENNReal.ofReal (3 / 2 : ℝ)) μ ∧
      eLpNorm f (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤
        ENNReal.ofReal (B1 ^ (1 / 6 : ℝ) * B53 ^ (5 / 6 : ℝ)) := by
  let g : α → ℝ := fun x => ‖f x‖ ^ (1 / 6 : ℝ)
  let k : α → ℝ := fun x => ‖f x‖ ^ (5 / 6 : ℝ)
  have hG : MemLp g (ENNReal.ofReal (6 : ℝ)) μ := by
    have hRpow := hF1.norm_rpow_div (ENNReal.ofReal (1 / 6 : ℝ))
    have hExponent : ENNReal.ofReal (1 : ℝ) /
        ENNReal.ofReal (1 / 6 : ℝ) = ENNReal.ofReal (6 : ℝ) := by
      rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < (1 / 6 : ℝ))]
      norm_num
    rw [hExponent] at hRpow
    simpa [g] using hRpow
  have hH : MemLp k (ENNReal.ofReal (2 : ℝ)) μ := by
    have hRpow := hF53.norm_rpow_div (ENNReal.ofReal (5 / 6 : ℝ))
    have hExponent : ENNReal.ofReal (5 / 3 : ℝ) /
        ENNReal.ofReal (5 / 6 : ℝ) = ENNReal.ofReal (2 : ℝ) := by
      rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < (5 / 6 : ℝ))]
      norm_num
    rw [hExponent] at hRpow
    simpa [k, ENNReal.toReal_ofReal (by norm_num : 0 ≤ (5 / 6 : ℝ)),
      Real.norm_eq_abs] using hRpow
  have : ENNReal.HolderTriple (ENNReal.ofReal (6 : ℝ))
      (ENNReal.ofReal (2 : ℝ)) (ENNReal.ofReal (3 / 2 : ℝ)) := by
    have h : (6 : ℝ).HolderTriple 2 (3 / 2 : ℝ) :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    exact h.ennrealOfReal
  have hProduct : MemLp (fun x => g x * k x)
      (ENNReal.ofReal (3 / 2 : ℝ)) μ := hG.mul hH
  have hProductEq : (fun x => g x * k x) = fun x => ‖f x‖ := by
    funext x
    by_cases hx : ‖f x‖ = 0
    · have hfx : f x = 0 := norm_eq_zero.mp hx
      simp [g, k, hfx]
    · change ‖f x‖ ^ (1 / 6 : ℝ) * ‖f x‖ ^ (5 / 6 : ℝ) = ‖f x‖
      rw [← Real.rpow_add (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx))]
      norm_num
  have hNormMem : MemLp (fun x => ‖f x‖)
      (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    exact (memLp_congr_ae (Filter.Eventually.of_forall fun x => congrFun hProductEq x)).1
      hProduct
  have hF32 : MemLp f (ENNReal.ofReal (3 / 2 : ℝ)) μ :=
    (memLp_norm_iff hF1.aestronglyMeasurable).1 hNormMem
  have hHolder := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
    (p := ENNReal.ofReal (6 : ℝ)) (q := ENNReal.ofReal (2 : ℝ))
    (r := ENNReal.ofReal (3 / 2 : ℝ)) (b := fun a b : ℝ => a * b)
    (c := (1 : NNReal)) (hb := continuous_mul)
    (hf := hG.aestronglyMeasurable) (hg := hH.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => by
      have hgx : 0 ≤ g x := Real.rpow_nonneg (norm_nonneg (f x)) _
      have hkx : 0 ≤ k x := Real.rpow_nonneg (norm_nonneg (f x)) _
      simp [Real.norm_eq_abs, abs_of_nonneg hgx, abs_of_nonneg hkx])
  have hHolder' : eLpNorm (fun x => g x * k x)
      (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤
      eLpNorm g (ENNReal.ofReal (6 : ℝ)) μ *
        eLpNorm k (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hHolder
  have hGnorm : eLpNorm g (ENNReal.ofReal (6 : ℝ)) μ =
      eLpNorm f (ENNReal.ofReal (1 : ℝ)) μ ^ (1 / 6 : ℝ) := by
    have hraw := eLpNorm_norm_rpow f hF1.aestronglyMeasurable
      (q := (1 / 6 : ℝ)) (by norm_num) (p := ENNReal.ofReal (6 : ℝ))
    have hExponent : ENNReal.ofReal (6 : ℝ) * ENNReal.ofReal (1 / 6 : ℝ) =
        ENNReal.ofReal (1 : ℝ) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6)]
      norm_num
    rw [hExponent] at hraw
    simpa [g] using hraw
  have hHnorm : eLpNorm k (ENNReal.ofReal (2 : ℝ)) μ =
      eLpNorm f (ENNReal.ofReal (5 / 3 : ℝ)) μ ^ (5 / 6 : ℝ) := by
    have hraw := eLpNorm_norm_rpow f hF53.aestronglyMeasurable
      (q := (5 / 6 : ℝ)) (by norm_num) (p := ENNReal.ofReal (2 : ℝ))
    have hExponent : ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal (5 / 6 : ℝ) =
        ENNReal.ofReal (5 / 3 : ℝ) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [hExponent] at hraw
    simpa [k] using hraw
  have hGbound : eLpNorm g (ENNReal.ofReal (6 : ℝ)) μ ≤
      ENNReal.ofReal (B1 ^ (1 / 6 : ℝ)) := by
    rw [hGnorm]
    calc
      eLpNorm f (ENNReal.ofReal (1 : ℝ)) μ ^ (1 / 6 : ℝ) ≤
          ENNReal.ofReal B1 ^ (1 / 6 : ℝ) :=
        ENNReal.rpow_le_rpow hBound1 (by norm_num)
      _ = ENNReal.ofReal (B1 ^ (1 / 6 : ℝ)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hB1 (by norm_num)]
  have hHbound : eLpNorm k (ENNReal.ofReal (2 : ℝ)) μ ≤
      ENNReal.ofReal (B53 ^ (5 / 6 : ℝ)) := by
    rw [hHnorm]
    calc
      eLpNorm f (ENNReal.ofReal (5 / 3 : ℝ)) μ ^ (5 / 6 : ℝ) ≤
          ENNReal.ofReal B53 ^ (5 / 6 : ℝ) :=
        ENNReal.rpow_le_rpow hBound53 (by norm_num)
      _ = ENNReal.ofReal (B53 ^ (5 / 6 : ℝ)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hB53 (by norm_num)]
  constructor
  · exact hF32
  · calc
      eLpNorm f (ENNReal.ofReal (3 / 2 : ℝ)) μ =
          eLpNorm (fun x => ‖f x‖) (ENNReal.ofReal (3 / 2 : ℝ)) μ :=
        (eLpNorm_norm f hF32.aestronglyMeasurable).symm
      _ = eLpNorm (fun x => g x * k x) (ENNReal.ofReal (3 / 2 : ℝ)) μ :=
        eLpNorm_congr_ae (Filter.Eventually.of_forall fun x => (congrFun hProductEq x).symm)
      _ ≤ eLpNorm g (ENNReal.ofReal (6 : ℝ)) μ *
            eLpNorm k (ENNReal.ofReal (2 : ℝ)) μ := hHolder'
      _ ≤ ENNReal.ofReal (B1 ^ (1 / 6 : ℝ)) *
            ENNReal.ofReal (B53 ^ (5 / 6 : ℝ)) :=
        mul_le_mul hGbound hHbound (by positivity) (by positivity)
      _ = ENNReal.ofReal (B1 ^ (1 / 6 : ℝ) * B53 ^ (5 / 6 : ℝ)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]

/-- The global `L^{5/3}` pressure class is bounded by the componentwise
`L^{5/3}` size of the regularized tensor, as in `lem:reg-pressure-bound`. -/
theorem regPressure_spaceTime_fiveThirds_norm_bound
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (5 / 3 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    (M : ℝ) (hM : 0 ≤ M)
    (hFbound : ∀ i j,
      eLpNorm (F i j) (ENNReal.ofReal (5 / 3 : ℝ))
        (volume : Measure (Vec3 × ℝ)) ≤ ENNReal.ofReal M) :
    ‖rieszPressureSpaceTimeClass (5 / 3 : ℝ) (by norm_num)
      (rieszPressureSpaceTimeTensorToLp (5 / 3 : ℝ) (by norm_num) F hF)‖ ≤
      9 * rieszPressureOperatorBound (5 / 3 : ℝ) (by norm_num) * M := by
  let r : ℝ := 5 / 3
  let hr : 1 < r := by norm_num [r]
  let G := rieszPressureSpaceTimeTensorToLp r hr F hF
  have hRiesz : ‖rieszPressureSpaceTimeClass r hr G‖ ≤
      rieszPressureOperatorBound r hr *
        ∑ i : Fin 3, ∑ j : Fin 3, ‖G i j‖ := by
    simpa [G] using rieszPressureSpaceTimeClass_norm_le r hr
      (rieszPressureSpaceTimeTensorToLp r hr F hF)
  have hComponent (i j : Fin 3) : ‖G i j‖ ≤ M := by
    have : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    change ‖(hF i j).toLp (F i j)‖ ≤ M
    rw [Lp.norm_toLp]
    calc
      ENNReal.toReal (eLpNorm (F i j) (ENNReal.ofReal (5 / 3 : ℝ))
          (volume : Measure (Vec3 × ℝ))) ≤ ENNReal.toReal (ENNReal.ofReal M) :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hFbound i j)
      _ = M := ENNReal.toReal_ofReal hM
  have hOp : 0 ≤ rieszPressureOperatorBound r hr := by
    have h := rieszPressureSpaceTimeComponent_norm_le r hr (0 : Fin 3) (0 : Fin 3)
    exact le_trans (norm_nonneg _) h
  change ‖rieszPressureSpaceTimeClass r hr G‖ ≤
    9 * rieszPressureOperatorBound r hr * M
  calc
    ‖rieszPressureSpaceTimeClass r hr G‖ ≤
        rieszPressureOperatorBound r hr *
          ∑ i : Fin 3, ∑ j : Fin 3, ‖G i j‖ := hRiesz
    _ ≤ rieszPressureOperatorBound r hr *
          ∑ i : Fin 3, ∑ j : Fin 3, M := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact hComponent i j
      · exact hOp
    _ = 9 * rieszPressureOperatorBound r hr * M := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

/-- On a finite slab, interpolation of the tensor `L¹` and `L^{5/3}` bounds
gives the `L^{3/2}` pressure estimate in `lem:reg-pressure-bound`. The tensor
is the one in the (R4) pressure formula, restricted to that slab. -/
theorem regPressure_spaceTime_threeHalves_norm_bound
    (T A M : ℝ) (hT : 0 ≤ T) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF1 : ∀ i j, MemLp (F i j) (ENNReal.ofReal (1 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    (hF53 : ∀ i j, MemLp (F i j) (ENNReal.ofReal (5 / 3 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    (hF1bound : ∀ i j,
      eLpNorm (F i j) (ENNReal.ofReal (1 : ℝ))
        (volume : Measure (Vec3 × ℝ)) ≤ ENNReal.ofReal (T * A))
    (hF53bound : ∀ i j,
      eLpNorm (F i j) (ENNReal.ofReal (5 / 3 : ℝ))
        (volume : Measure (Vec3 × ℝ)) ≤ ENNReal.ofReal M) :
    ∃ hF32 : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume : Measure (Vec3 × ℝ)),
      ‖rieszPressureSpaceTimeClass (3 / 2 : ℝ) (by norm_num)
        (rieszPressureSpaceTimeTensorToLp (3 / 2 : ℝ) (by norm_num) F hF32)‖ ≤
        9 * rieszPressureOperatorBound (3 / 2 : ℝ) (by norm_num) *
          ((T * A) ^ (1 / 6 : ℝ) * M ^ (5 / 6 : ℝ)) := by
  let r : ℝ := 3 / 2
  let hr : 1 < r := by norm_num [r]
  let hF32 : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) := fun i j =>
    (regPressure_interpolate_one_fiveThirds (hF1 i j) (hF53 i j)
      (T * A) M (mul_nonneg hT hA) hM (hF1bound i j) (hF53bound i j)).1
  refine ⟨hF32, ?_⟩
  let G := rieszPressureSpaceTimeTensorToLp r hr F hF32
  have hInterpolate (i j : Fin 3) :
      eLpNorm (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume : Measure (Vec3 × ℝ)) ≤
        ENNReal.ofReal ((T * A) ^ (1 / 6 : ℝ) * M ^ (5 / 6 : ℝ)) :=
    (regPressure_interpolate_one_fiveThirds (hF1 i j) (hF53 i j)
      (T * A) M (mul_nonneg hT hA) hM (hF1bound i j) (hF53bound i j)).2
  have hRiesz : ‖rieszPressureSpaceTimeClass r hr G‖ ≤
      rieszPressureOperatorBound r hr *
        ∑ i : Fin 3, ∑ j : Fin 3, ‖G i j‖ := by
    simpa [G] using rieszPressureSpaceTimeClass_norm_le r hr
      (rieszPressureSpaceTimeTensorToLp r hr F hF32)
  have hComponent (i j : Fin 3) : ‖G i j‖ ≤
      (T * A) ^ (1 / 6 : ℝ) * M ^ (5 / 6 : ℝ) := by
    have : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    change ‖(hF32 i j).toLp (F i j)‖ ≤
      (T * A) ^ (1 / 6 : ℝ) * M ^ (5 / 6 : ℝ)
    rw [Lp.norm_toLp]
    calc
      ENNReal.toReal (eLpNorm (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume : Measure (Vec3 × ℝ))) ≤
          ENNReal.toReal (ENNReal.ofReal
            ((T * A) ^ (1 / 6 : ℝ) * M ^ (5 / 6 : ℝ))) :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hInterpolate i j)
      _ = (T * A) ^ (1 / 6 : ℝ) * M ^ (5 / 6 : ℝ) :=
        ENNReal.toReal_ofReal (mul_nonneg
          (Real.rpow_nonneg (mul_nonneg hT hA) _) (Real.rpow_nonneg hM _))
  have hOp : 0 ≤ rieszPressureOperatorBound r hr := by
    exact le_trans (norm_nonneg _) <|
      rieszPressureSpaceTimeComponent_norm_le r hr (0 : Fin 3) (0 : Fin 3)
  change ‖rieszPressureSpaceTimeClass r hr G‖ ≤
    9 * rieszPressureOperatorBound r hr *
      ((T * A) ^ (1 / 6 : ℝ) * M ^ (5 / 6 : ℝ))
  calc
    ‖rieszPressureSpaceTimeClass r hr G‖ ≤
        rieszPressureOperatorBound r hr *
          ∑ i : Fin 3, ∑ j : Fin 3, ‖G i j‖ := hRiesz
    _ ≤ rieszPressureOperatorBound r hr *
          ∑ i : Fin 3, ∑ j : Fin 3,
            (T * A) ^ (1 / 6 : ℝ) * M ^ (5 / 6 : ℝ) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact hComponent i j
      · exact hOp
    _ = 9 * rieszPressureOperatorBound r hr *
          ((T * A) ^ (1 / 6 : ℝ) * M ^ (5 / 6 : ℝ)) := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

end CKN.Leray

end
