/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball
public import LeanPool.CaffarelliKohnNirenberg.Foundation.HomogeneousSobolev
public import LeanPool.CaffarelliKohnNirenberg.Foundation.VectorPotential
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpace
public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# JSpace Fourier

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology SchwartzMap FourierTransform LineDeriv
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

@[expose]
def extensionDotLinear : Vec3 →ₗ[ℝ] Vec3 →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ i : Fin 3, x i * y i)
    (by intro x y z; simp [Finset.sum_add_distrib, add_mul])
    (by
      intro c x y
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring)
    (by intro x y z; simp [Finset.sum_add_distrib, mul_add])
    (by
      intro c x y
      simp only [Pi.smul_apply, smul_eq_mul]
      calc
        (∑ i : Fin 3, x i * (c * y i)) =
            ∑ i : Fin 3, c * (x i * y i) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = c * ∑ i : Fin 3, x i * y i := (Finset.mul_sum _ _ _).symm)

@[expose]
def extensionDotContinuous : Vec3 →L[ℝ] Vec3 →L[ℝ] ℝ :=
  extensionDotLinear.mkContinuous₂ 3 (by
    intro x y
    calc
      ‖∑ i : Fin 3, x i * y i‖ ≤ ∑ i : Fin 3, ‖x i * y i‖ := norm_sum_le _ _
      _ = ∑ i : Fin 3, ‖x i‖ * ‖y i‖ := by simp [norm_mul]
      _ ≤ ∑ i : Fin 3, ‖x‖ * ‖y‖ := by
        apply Finset.sum_le_sum
        intro i _hi
        exact mul_le_mul (norm_le_pi_norm x i) (norm_le_pi_norm y i)
          (norm_nonneg _) (norm_nonneg _)
      _ = 3 * ‖x‖ * ‖y‖ := by simp [Finset.sum_const, nsmul_eq_mul]; ring)

@[expose]
def schwartzGradient (ψ : 𝓢(Vec3, ℝ)) : Vec3 → Vec3 :=
  fun x i => spatialDeriv ψ i x

private theorem schwartzGradient_memLp (ψ : 𝓢(Vec3, ℝ)) :
    MemLp (schwartzGradient ψ) (2 : ℝ≥0∞) volume := by
  apply MemLp.of_eval
  intro i
  have h := (∂_{basisVec i} ψ).memLp (2 : ℝ≥0∞) volume
  have heq : (fun x : Vec3 => schwartzGradient ψ x i) =
      fun x => (∂_{basisVec i} ψ) x := by
    funext x
    simp [schwartzGradient, spatialDeriv, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [heq]
  exact h

@[expose]
def cutoffSchwartzGradient (ψ : 𝓢(Vec3, ℝ)) (n : ℕ) : Vec3 → Vec3 :=
  fun x i => spatialDeriv
    (fun y => CKN.canonicalBallCutoff 0 ((n + 1 : ℕ) : ℝ)
      (2 * ((n + 1 : ℕ) : ℝ)) y * ψ y) i x

private theorem cutoffSchwartzGradient_memLp (ψ : 𝓢(Vec3, ℝ)) (n : ℕ) :
    MemLp (cutoffSchwartzGradient ψ n) (2 : ℝ≥0∞) volume := by
  apply MemLp.of_eval
  intro i
  have hpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have houter : ((n + 1 : ℕ) : ℝ) < 2 * ((n + 1 : ℕ) : ℝ) := by
    nlinarith only [hpos]
  have hη : ContDiff ℝ (⊤ : ℕ∞) (CKN.canonicalBallCutoff 0
        ((n + 1 : ℕ) : ℝ) (2 * ((n + 1 : ℕ) : ℝ)) : Vec3 → ℝ) := by
    exact CKN.canonicalBallCutoff_smooth 0 hpos.le houter
  have hprod : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => CKN.canonicalBallCutoff 0 ((n + 1 : ℕ) : ℝ)
        (2 * ((n + 1 : ℕ) : ℝ)) y * ψ y) := hη.mul (ψ.smooth ⊤)
  have hscalarCont : Continuous (fun x : Vec3 => cutoffSchwartzGradient ψ n x i) := by
    exact CKN.contDiff_spatialDeriv_smooth hprod i |>.continuous
  have hηc : HasCompactSupport (CKN.canonicalBallCutoff (d := 3) (0 : Vec3)
        ((n + 1 : ℕ) : ℝ) (2 * ((n + 1 : ℕ) : ℝ))) := by
    exact CKN.canonicalBallCutoff_hasCompactSupport (x₀ := (0 : Vec3)) hpos.le houter
  have hprodCompact : HasCompactSupport (fun y : Vec3 =>
      CKN.canonicalBallCutoff 0 ((n + 1 : ℕ) : ℝ)
        (2 * ((n + 1 : ℕ) : ℝ)) y * ψ y) := hηc.mul_right
  have hscalarCompact : HasCompactSupport (fun x => cutoffSchwartzGradient ψ n x i) := by
    change HasCompactSupport (fun x =>
      (fderiv ℝ (fun y : Vec3 => CKN.canonicalBallCutoff 0
        ((n + 1 : ℕ) : ℝ) (2 * ((n + 1 : ℕ) : ℝ)) y * ψ y) x)
          (basisVec i))
    exact hprodCompact.fderiv_apply (𝕜 := ℝ) (basisVec i)
  exact hscalarCont.memLp_of_hasCompactSupport hscalarCompact

@[expose]
def extensionPairing (a : Lp (α := Vec3) Vec3 (2 : ℝ≥0∞) volume) :
    Lp (α := Vec3) Vec3 (2 : ℝ≥0∞) volume →L[ℝ] ℝ :=
  (extensionDotContinuous.lpPairing volume (2 : ℝ≥0∞) (2 : ℝ≥0∞)) a

private theorem extensionPairing_eq_integral
    (a u : Lp (α := Vec3) Vec3 (2 : ℝ≥0∞) volume) :
    extensionPairing a u =
      ∫ x : Vec3, ∑ i : Fin 3, a x i * u x i := by
  rw [extensionPairing, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [extensionDotContinuous, extensionDotLinear]

/-- The weak divergence identity extends from compact tests to every real
Schwartz test. -/
theorem isWeakDivFreeL2_schwartz {a : Vec3 → Vec3}
    (ha : IsWeakDivFreeL2 a) (ψ : 𝓢(Vec3, ℝ)) :
    ∫ x : Vec3, ∑ i : Fin 3, a x i * spatialDeriv ψ i x = 0 := by
  let r : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)
  let R : ℕ → ℝ := fun n => 2 * r n
  let η : ℕ → Vec3 → ℝ := fun n => CKN.canonicalBallCutoff 0 (r n) (R n)
  let ψn : ℕ → Vec3 → ℝ := fun n x => η n x * ψ x
  let grad : Vec3 → Vec3 := schwartzGradient ψ
  let gradN : ℕ → Vec3 → Vec3 := cutoffSchwartzGradient ψ
  let aLp : Lp (α := Vec3) Vec3 (2 : ℝ≥0∞) volume := ha.1.toLp a
  let gradLp : Lp (α := Vec3) Vec3 (2 : ℝ≥0∞) volume :=
    (schwartzGradient_memLp ψ).toLp grad
  let gradNLp : ℕ → Lp (α := Vec3) Vec3 (2 : ℝ≥0∞) volume :=
    fun n => (cutoffSchwartzGradient_memLp ψ n).toLp (gradN n)
  have hr (n : ℕ) : 0 ≤ r n := by dsimp [r]; positivity
  have hrR (n : ℕ) : r n < R n := by
    dsimp [R]
    linarith only [show 0 < r n by dsimp [r]; positivity]
  have hgradNPoint (n : ℕ) (i : Fin 3) (x : Vec3) :
      gradN n x i = η n x * grad x i + spatialDeriv (η n) i x * ψ x := by
    have hη : ContDiff ℝ (⊤ : ℕ∞) (η n) :=
      CKN.canonicalBallCutoff_smooth 0 (hr n) (hrR n)
    have hηd := hη.differentiable (by simp) x
    have hψd := (ψ.smooth ⊤).differentiable (by simp) x
    have h := CKN.spatialDeriv_mul hηd hψd i (x := x)
    change spatialDeriv (fun y => η n y * ψ y) i x = _
    rw [h]
    rw [show spatialDeriv ψ i x = grad x i by rfl]
    ring
  have hgradη (n : ℕ) (x : Vec3) (i : Fin 3) :
      |spatialDeriv (η n) i x| ≤ 32 / r n := by
    have h := CKN.canonicalBallCutoff_gradient_bound (x₀ := 0) (hr n) (hrR n) x
    have h' : CKN.vecEuclideanNorm (CKN.classicalGradient (η n) x) ≤ 32 / (R n - r n) := by
      simpa [η, R] using h
    have hcoord := CKN.abs_apply_le_vecEuclideanNorm (CKN.classicalGradient (η n) x) i
    have hsp : CKN.spatialDeriv (η n) i x = CKN.classicalGradient (η n) x i := by
      rfl
    rw [hsp]
    calc
      |CKN.classicalGradient (η n) x i| ≤
          CKN.vecEuclideanNorm (CKN.classicalGradient (η n) x) := hcoord
      _ ≤ 32 / (R n - r n) := h'
      _ = 32 / r n := by dsimp [R]; ring
  have hcoordErr (n : ℕ) (i : Fin 3) (x : Vec3) :
      |gradN n x i - grad x i| ≤
        ‖((CKN.euclideanBall (0 : Vec3) (r n))ᶜ.indicator grad) x‖ +
          (32 / r n) * |ψ x| := by
    rw [hgradNPoint]
    by_cases hx : x ∈ CKN.euclideanBall 0 (r n)
    · have hηone : η n x = 1 := by
        exact CKN.canonicalBallCutoff_eq_one_on_inner (hr n) (hrR n) hx
      rw [hηone]
      simp only [one_mul]
      have heq : grad x i + spatialDeriv (η n) i x * ψ x - grad x i =
          spatialDeriv (η n) i x * ψ x := by ring
      rw [heq, abs_mul]
      exact (mul_le_mul_of_nonneg_right (hgradη n x i) (abs_nonneg (ψ x))).trans
        (le_add_of_nonneg_left (norm_nonneg _))
    · have hηle : η n x ≤ 1 := CKN.canonicalBallCutoff_le_one 0 (r n) (R n) x
      have hηnonneg : 0 ≤ η n x := CKN.canonicalBallCutoff_nonneg 0 (r n) (R n) x
      have hfactor : |η n x - 1| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith only [hηnonneg, hηle]
      have hxsmall : x ∉ CKN.euclideanBall (0 : Vec3) (r n) := hx
      have htail : ((CKN.euclideanBall (0 : Vec3) (r n))ᶜ.indicator grad) x = grad x := by
        rw [Set.indicator_of_mem hxsmall]
      have hgradcoord : |grad x i| ≤ ‖grad x‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (grad x) i
      have htailcoord : |grad x i| ≤
          ‖((CKN.euclideanBall (0 : Vec3) (r n))ᶜ.indicator grad) x‖ := by
        rw [htail]
        exact hgradcoord
      calc
        |η n x * grad x i + spatialDeriv (η n) i x * ψ x - grad x i| =
            |(η n x - 1) * grad x i + spatialDeriv (η n) i x * ψ x| := by
              congr 1
              ring
        _ ≤ |(η n x - 1) * grad x i| +
              |spatialDeriv (η n) i x * ψ x| := abs_add_le _ _
        _ = |η n x - 1| * |grad x i| +
              |spatialDeriv (η n) i x| * |ψ x| := by rw [abs_mul, abs_mul]
        _ ≤ ‖((CKN.euclideanBall (0 : Vec3) (r n))ᶜ.indicator grad) x‖ +
              (32 / r n) * |ψ x| := by
          calc
            _ ≤ |grad x i| + (32 / r n) * |ψ x| := by
              gcongr
              · exact mul_le_of_le_one_left (abs_nonneg _) hfactor
              · exact hgradη n x i
            _ ≤ _ := by simpa [add_comm] using
              add_le_add_right htailcoord ((32 / r n) * |ψ x|)
  have htailTendsto : Tendsto
      (fun n : ℕ => eLpNorm
        ((CKN.euclideanBall (0 : Vec3) (r n))ᶜ.indicator grad)
        (2 : ℝ≥0∞) volume) atTop (nhds 0) := by
    have h := eLpNorm_indicator_compl_euclideanBall_tendsto_zero
      (schwartzGradient_memLp ψ)
    have hcomp := h.comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def, r, Nat.cast_add, Nat.cast_one] using hcomp
  have hfactorRealTendsto : Tendsto (fun n : ℕ => |(32 : ℝ) / r n|)
      atTop (nhds 0) := by
    have hr : Tendsto r atTop atTop := by
      have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop
      have h := hnat.comp (tendsto_add_atTop_nat (1 : ℕ))
      simpa [Function.comp_def, Nat.cast_add, Nat.cast_one, r] using h
    have hreal : Tendsto (fun n : ℕ => 32 / r n) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (32 : ℝ)) atTop (nhds 32)).div_atTop hr
    exact hreal.congr' (Filter.Eventually.of_forall fun n =>
      (abs_of_nonneg (by positivity : 0 ≤ (32 : ℝ) / r n)).symm)
  have hfactorTendsto : Tendsto (fun n : ℕ => ‖(32 : ℝ) / r n‖ₑ)
      atTop (nhds 0) := by
    simpa only [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal hfactorRealTendsto
  have hmajorMemLp (n : ℕ) :
      MemLp (fun x : Vec3 => ‖((CKN.euclideanBall (0 : Vec3) (r n))ᶜ.indicator grad) x‖ +
        (32 / r n) * |ψ x|) (2 : ℝ≥0∞) volume := by
    exact ((schwartzGradient_memLp ψ).indicator (CKN.measurableSet_euclideanBall 0 (r n)).compl).norm.add
      ((ψ.memLp (2 : ℝ≥0∞) volume).norm.const_mul _)
  have hψabs : eLpNorm (fun x : Vec3 => |ψ x|) 2 volume =
      eLpNorm ψ 2 volume := by
    have habs : (fun x : Vec3 => |ψ x|) = fun x => ‖ψ x‖ := by
      funext x
      simp only [Real.norm_eq_abs]
    rw [habs]
    exact eLpNorm_norm ψ (ψ.memLp (2 : ℝ≥0∞) volume).aestronglyMeasurable
  have hmajorBound (n : ℕ) :
      eLpNorm (fun x : Vec3 => ‖((CKN.euclideanBall (0 : Vec3) (r n))ᶜ.indicator grad) x‖ +
        (32 / r n) * |ψ x|) (2 : ℝ≥0∞) volume ≤
        eLpNorm ((CKN.euclideanBall (0 : Vec3) (r n))ᶜ.indicator grad)
          (2 : ℝ≥0∞) volume + ‖(32 : ℝ) / r n‖ₑ * eLpNorm ψ 2 volume := by
    calc
      _ ≤ eLpNorm (fun x => ‖((CKN.euclideanBall (0 : Vec3) (r n))ᶜ.indicator grad) x‖)
            2 volume + eLpNorm (fun x => (32 / r n) * |ψ x|) 2 volume := by
          exact eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      _ = _ := by
        have hscale : (fun x : Vec3 => (32 / r n) * |ψ x|) =
            (32 / r n) • fun x => |ψ x| := by
          funext x
          simp [smul_eq_mul]
        have htailLp : MemLp ((CKN.euclideanBall (0 : Vec3) (r n))ᶜ.indicator grad)
            (2 : ℝ≥0∞) volume :=
          (schwartzGradient_memLp ψ).indicator
            (CKN.measurableSet_euclideanBall 0 (r n)).compl
        rw [eLpNorm_norm _ htailLp.aestronglyMeasurable]
        rw [hscale, eLpNorm_const_smul, hψabs]
  have hmajorTendsto : Tendsto
      (fun n : ℕ => eLpNorm (fun x : Vec3 =>
        ‖((CKN.euclideanBall (0 : Vec3) (r n))ᶜ.indicator grad) x‖ +
          (32 / r n) * |ψ x|) (2 : ℝ≥0∞) volume) atTop (nhds 0) := by
    have hψfinite : eLpNorm ψ (2 : ℝ≥0∞) volume ≠ ∞ :=
      (ψ.memLp (2 : ℝ≥0∞) volume).eLpNorm_ne_top
    have hprod : Tendsto
        (fun n : ℕ => ‖(32 : ℝ) / r n‖ₑ * eLpNorm ψ 2 volume)
        atTop (nhds 0) :=
      by simpa using ENNReal.Tendsto.mul_const hfactorTendsto (Or.inr hψfinite)
    have hsum := htailTendsto.add hprod
    have hnonneg : ∀ᶠ n : ℕ in atTop, (0 : ℝ≥0∞) + 0 ≤ eLpNorm
        (fun x : Vec3 => ‖((CKN.euclideanBall (0 : Vec3) (r n))ᶜ.indicator grad) x‖ +
          (32 / r n) * |ψ x|) 2 volume := by
      filter_upwards [] with n
      simp
    simpa only [zero_add] using tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hsum hnonneg
      (Filter.Eventually.of_forall hmajorBound)
  have herrorBound (n : ℕ) :
      eLpNorm (gradN n - grad) (2 : ℝ≥0∞) volume ≤
        (3 : ℝ≥0∞) * eLpNorm (fun x : Vec3 =>
          ‖((CKN.euclideanBall (0 : Vec3) (r n))ᶜ.indicator grad) x‖ +
            (32 / r n) * |ψ x|) 2 volume := by
    let base : Vec3 → ℝ := fun x =>
      ‖((CKN.euclideanBall (0 : Vec3) (r n))ᶜ.indicator grad) x‖ +
        (32 / r n) * |ψ x|
    let major : Vec3 → ℝ := fun x => 3 * base x
    have hbaseLp : MemLp base (2 : ℝ≥0∞) volume := hmajorMemLp n
    have hmajorLp : MemLp major (2 : ℝ≥0∞) volume := by
      simpa [major, base] using hbaseLp.const_mul (3 : ℝ)
    have hmeas : AEStronglyMeasurable (gradN n - grad) volume := by
      exact (cutoffSchwartzGradient_memLp ψ n).aestronglyMeasurable.sub
        (schwartzGradient_memLp ψ).aestronglyMeasurable
    have hpoint (x : Vec3) : ‖gradN n x - grad x‖ ≤ ‖major x‖ := by
      have hbaseNonneg : 0 ≤ base x := by
        change 0 ≤ ‖((CKN.euclideanBall (0 : Vec3) (r n))ᶜ.indicator grad) x‖ +
          (32 / r n) * |ψ x|
        exact add_nonneg (norm_nonneg _) (mul_nonneg
          (div_nonneg (by norm_num) (hr n)) (abs_nonneg _))
      have hmajorNonneg : 0 ≤ major x := by
        change 0 ≤ 3 * base x
        exact mul_nonneg (by norm_num) hbaseNonneg
      rw [Real.norm_eq_abs, abs_of_nonneg hmajorNonneg]
      apply (pi_norm_le_iff_of_nonneg hmajorNonneg).2
      intro i
      calc
        |(gradN n x - grad x) i| ≤ base x := hcoordErr n i x
        _ ≤ major x := by
          dsimp [major]
          nlinarith only [hbaseNonneg]
    have hmono : eLpNorm (gradN n - grad) 2 volume ≤ eLpNorm major 2 volume :=
      eLpNorm_mono hmeas hpoint
    have hmajorEq : major = (3 : ℝ) • base := by
      funext x
      simp [major, base, smul_eq_mul]
    calc
      _ ≤ eLpNorm major 2 volume := hmono
      _ = ‖(3 : ℝ)‖ₑ * eLpNorm base 2 volume := by
        rw [hmajorEq, eLpNorm_const_smul]
      _ = (3 : ℝ≥0∞) * eLpNorm
          (fun x : Vec3 => ‖((CKN.euclideanBall (0 : Vec3) (r n))ᶜ.indicator grad) x‖ +
            (32 / r n) * |ψ x|) 2 volume := by
        simp only [Real.enorm_eq_ofReal_abs, abs_of_pos (by norm_num : 0 < (3 : ℝ)),
          ENNReal.ofReal_ofNat]
        rfl
  have herrorTendsto : Tendsto
      (fun n : ℕ => eLpNorm (gradN n - grad) (2 : ℝ≥0∞) volume)
      atTop (nhds 0) := by
    have hmajor := ENNReal.Tendsto.const_mul hmajorTendsto
      (Or.inr (by norm_num : (3 : ℝ≥0∞) ≠ ∞))
    have hnonneg : ∀ᶠ n : ℕ in atTop,
        (3 : ℝ≥0∞) * 0 ≤ eLpNorm (gradN n - grad) (2 : ℝ≥0∞) volume :=
      Filter.Eventually.of_forall fun _ => by simp
    simpa using tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor
      hnonneg (Filter.Eventually.of_forall herrorBound)
  have hgradLimit : Tendsto gradNLp atTop (nhds gradLp) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' gradN
      (fun n => cutoffSchwartzGradient_memLp ψ n) grad (schwartzGradient_memLp ψ)).2
      herrorTendsto
  let P := extensionPairing aLp
  have hPLimit : Tendsto (fun n => P (gradNLp n)) atTop (nhds (P gradLp)) :=
    (P.continuous.tendsto gradLp).comp hgradLimit
  have hPzero (n : ℕ) : P (gradNLp n) = 0 := by
    rw [extensionPairing_eq_integral]
    let ψtest : WeakTestFunction (Set.univ : Set Vec3) :=
      ⟨ψn n,
        (CKN.canonicalBallCutoff_smooth 0 (hr n) (hrR n)).mul (ψ.smooth ⊤),
        (CKN.canonicalBallCutoff_hasCompactSupport (hr n) (hrR n)).mul_right,
        Set.subset_univ _⟩
    have htest := ha.2 ψtest
    have hgradEq (x : Vec3) : cutoffSchwartzGradient ψ n x =
        fun i => ψtest.partialDeriv i x := by
      funext i
      rfl
    calc
      ∫ x : Vec3, ∑ i : Fin 3, aLp x i * gradNLp n x i =
          ∫ x : Vec3, ∑ i : Fin 3, a x i * ψtest.partialDeriv i x := by
            apply integral_congr_ae
            filter_upwards [ha.1.coeFn_toLp, (cutoffSchwartzGradient_memLp ψ n).coeFn_toLp] with x ha' hg'
            rw [ha', hg', hgradEq x]
      _ = 0 := htest
  have hPconstant : (fun n : ℕ => P (gradNLp n)) = fun _ => (0 : ℝ) :=
    funext hPzero
  rw [hPconstant] at hPLimit
  have hPvalue : P gradLp = 0 := tendsto_nhds_unique hPLimit tendsto_const_nhds
  rw [extensionPairing_eq_integral] at hPvalue
  apply (integral_congr_ae ?_).trans hPvalue
  filter_upwards [ha.1.coeFn_toLp, (schwartzGradient_memLp ψ).coeFn_toLp] with x ha' hg'
  rw [ha', hg']
  rfl

end CKN

end
