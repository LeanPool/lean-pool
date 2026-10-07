/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.H1
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Setting.ExtSobolevBallSupported

/-!
# Sobolev Global L6

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic

namespace CKN

noncomputable section

/-- The global homogeneous Sobolev inequality, with one absolute constant
chosen before the function. -/
theorem sobolev_L6_global :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ g : H1Function (Set.univ : Set Vec3),
        lpNormOn 6 Set.univ g.toFun ≤ C * weakGradientLpNormOn 2 Set.univ g.grad := by
  let C : ℝ≥0∞ := localSobolevConstant
  have hCtop : C ≠ ∞ := by
    dsimp [C]
    unfold localSobolevConstant
    finiteness
  refine ⟨C, hCtop, ?_⟩
  intro g
  let A : ℝ≥0∞ := lpNormOn 2 Set.univ g.toFun
  let G : ℝ≥0∞ := weakGradientLpNormOn 2 Set.univ g.grad
  let radius : ℕ → ℝ := fun n => (n : ℝ) + 1
  let ball : ℕ → Set Vec3 := fun n => euclideanBall (0 : Vec3) (radius n)
  let truncation : ℕ → Vec3 → ℝ := fun n => (ball n).indicator g.toFun
  let error : ℕ → ℝ≥0∞ := fun n =>
    (Real.toNNReal (32 / radius n) : ℝ≥0∞)
  have hfun : MemLp g.toFun 2 volume := by
    simpa [MemL2On, MemLpOn, volumeOn] using g.memL2
  have hgradFun (i : Fin 3) : MemLp (fun x => g.grad x i) 2 volume := by
    simpa [MemL2On, MemLpOn, volumeOn] using g.grad_memL2 i
  have hgrad : MemLp g.grad 2 volume := (memLp_pi_iff).2 hgradFun
  have hAtop : A ≠ ∞ := by
    dsimp [A, lpNormOn]
    simpa [Measure.restrict_univ] using hfun.eLpNorm_ne_top
  have hGtop : G ≠ ∞ := by
    dsimp [G, weakGradientLpNormOn]
    simpa [Measure.restrict_univ] using hgrad.eLpNorm_ne_top
  have hballOpen (n : ℕ) : IsOpen (ball n) := by
    dsimp [ball]
    exact isOpen_euclideanBall 0 (radius n)
  have hballMeas (n : ℕ) : MeasurableSet (ball n) := (hballOpen n).measurableSet
  have hballPos (n : ℕ) : 0 < radius n := by
    dsimp [radius]
    positivity
  have htruncMem (n : ℕ) : MemLp (truncation n) 2 volume := by
    exact hfun.indicator (hballMeas n)
  have htruncMeas (n : ℕ) : AEStronglyMeasurable (truncation n) volume :=
    (htruncMem n).aestronglyMeasurable
  have hfunMeas : AEStronglyMeasurable g.toFun volume := hfun.aestronglyMeasurable
  have hpointwise : ∀ x : Vec3,
      Tendsto (fun n => truncation n x) atTop (𝓝 (g.toFun x)) := by
    intro x
    obtain ⟨N, hN⟩ := exists_nat_gt (vecEuclideanNorm x)
    have hmem : ∀ᶠ n : ℕ in atTop, x ∈ ball n := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hNcast : vecEuclideanNorm x < (N : ℝ) := hN
      have hncast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hnorm : vecEuclideanNorm x < radius n := by
        dsimp [radius]
        exact hNcast.trans_le (hncast.trans (le_add_of_nonneg_right zero_le_one))
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (hballPos n)).2
      simpa using hnorm
    have heq : (fun n => truncation n x) =ᶠ[atTop] (fun _ => g.toFun x) := by
      filter_upwards [hmem] with n hn
      simp [truncation, hn]
    exact tendsto_const_nhds.congr' heq.symm
  have hFatou : lpNormOn 6 Set.univ g.toFun ≤
      atTop.liminf (fun n => eLpNorm (truncation n) 6 volume) := by
    simpa [lpNormOn] using
      (Lp.eLpNorm_lim_le_liminf_eLpNorm htruncMeas g.toFun hfunMeas
        (Filter.Eventually.of_forall hpointwise))
  have hlocal (n : ℕ) :
      lpNormOn 6 (ball n) g.toFun ≤
        C * (weakGradientLpNormOn 2 (euclideanBall (0 : Vec3) (2 * radius n)) g.grad +
          error n * lpNormOn 2 (euclideanBall (0 : Vec3) (2 * radius n)) g.toFun) := by
    have houterOpen : IsOpen (euclideanBall (0 : Vec3) (2 * radius n)) :=
      isOpen_euclideanBall 0 (2 * radius n)
    have hlocal' := h1SobolevBall (x₀ := (0 : Vec3)) (r := radius n) (hballPos n)
      (g.restrict houterOpen (Set.subset_univ _))
    simpa [C, ball, radius, error, lpNormOn, weakGradientLpNormOn,
      H1Function.restrict_toFun, H1Function.restrict_grad] using hlocal'
  have htruncBound (n : ℕ) :
      eLpNorm (truncation n) 6 volume ≤ C * (G + error n * A) := by
    rw [show truncation n = (ball n).indicator g.toFun by rfl,
      eLpNorm_indicator_eq_eLpNorm_restrict (hballMeas n)]
    calc
      lpNormOn 6 (ball n) g.toFun ≤
          C * (weakGradientLpNormOn 2 (euclideanBall (0 : Vec3) (2 * radius n)) g.grad +
            error n * lpNormOn 2 (euclideanBall (0 : Vec3) (2 * radius n)) g.toFun) := hlocal n
      _ ≤ C * (G + error n * A) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add
        · simpa [G, weakGradientLpNormOn] using
            (eLpNorm_restrict_le g.grad 2 volume
              (euclideanBall (0 : Vec3) (2 * radius n)))
        · exact mul_le_mul_of_nonneg_left
            (by simpa [A, lpNormOn] using
              (eLpNorm_restrict_le g.toFun 2 volume
                (euclideanBall (0 : Vec3) (2 * radius n)))) (by positivity)
  have hsucc : Tendsto Nat.succ atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ => Nat.le_succ n) tendsto_id
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_inv_nat_nhds_zero.comp hsucc
    convert h using 1
    funext n
    simp [Nat.cast_succ]
  have herrorEq (n : ℕ) : error n =
      (32 : ℝ≥0∞) * ((n : ℝ≥0∞) + 1)⁻¹ := by
    dsimp [error, radius]
    change ENNReal.ofReal (32 / ((n : ℝ) + 1)) = _
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    rw [div_eq_mul_inv]
    norm_num [ENNReal.ofReal_natCast]
  have herrorTendsto : Tendsto error atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul hinv
      (Or.inr (by norm_num : (32 : ℝ≥0∞) ≠ ∞))
    have heq : error = fun n : ℕ => (32 : ℝ≥0∞) * ((n : ℝ≥0∞) + 1)⁻¹ :=
      funext herrorEq
    rw [heq]
    simpa using h
  have herrorATendsto : Tendsto (fun n => error n * A) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const herrorTendsto (Or.inr hAtop)
  have hfinal : lpNormOn 6 Set.univ g.toFun ≤ C * G := by
    apply ENNReal.le_of_forall_pos_le_add
    intro δ hδ htop
    have hdenTop : C + 1 ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hCtop, ENNReal.one_ne_top⟩
    have hδtop : (δ : ℝ≥0∞) / (C + 1) ≠ ∞ :=
      ENNReal.div_ne_top (by finiteness) (by positivity)
    have hδpos : 0 < (δ : ℝ≥0∞) / (C + 1) :=
      ENNReal.div_pos (by exact_mod_cast hδ.ne') (by finiteness)
    have hsmall : ∀ᶠ n : ℕ in atTop,
        error n * A ≤ (δ : ℝ≥0∞) / (C + 1) :=
      (ENNReal.tendsto_nhds_zero.1 herrorATendsto _ hδpos)
    have hlim : atTop.liminf (fun n => eLpNorm (truncation n) 6 volume) ≤
        C * (G + (δ : ℝ≥0∞) / (C + 1)) := by
      apply liminf_le_of_frequently_le'
      have hevent : ∀ᶠ n : ℕ in atTop,
          eLpNorm (truncation n) 6 volume ≤
            C * (G + (δ : ℝ≥0∞) / (C + 1)) := by
        filter_upwards [hsmall] with n hn
        exact (htruncBound n).trans (mul_le_mul_of_nonneg_left
          (by simpa only [add_comm] using (add_le_add_right hn G)) (by positivity))
      exact hevent.frequently
    refine hFatou.trans (hlim.trans ?_)
    calc
      C * (G + (δ : ℝ≥0∞) / (C + 1)) =
          C * G + C * ((δ : ℝ≥0∞) / (C + 1)) := by rw [mul_add]
      _ ≤ C * G + δ := by
        apply add_le_add_right
        calc
          C * ((δ : ℝ≥0∞) / (C + 1)) ≤
              (C + 1) * ((δ : ℝ≥0∞) / (C + 1)) := by
            exact mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right (by norm_num)) (by positivity)
          _ = δ := ENNReal.mul_div_cancel (by positivity) (by finiteness)
  exact hfinal

/-- The inhomogeneous whole-space consequence, with the same absolute
constant as the homogeneous inequality. -/
theorem sobolev_L6_global_inhomogeneous :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ g : H1Function (Set.univ : Set Vec3),
        lpNormOn 6 Set.univ g.toFun ≤
          C * (weakGradientLpNormOn 2 Set.univ g.grad + lpNormOn 2 Set.univ g.toFun) := by
  obtain ⟨C, hC, hglobal⟩ := sobolev_L6_global
  refine ⟨C, hC, fun g => ?_⟩
  exact (hglobal g).trans (mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_right (by positivity)) (by positivity))

/-- The scale-explicit spatial Sobolev estimate holds for almost every member
of a time-indexed family of `H¹` functions on a ball. -/
theorem sobolev_L6_ball_slices
    {x₀ : Vec3} {r : ℝ} (hr : 0 < r) {J : Set ℝ}
    (u : ℝ → H1Function (euclideanBall x₀ r)) :
    ∀ᵐ t ∂(volume.restrict J),
      lpNormOn 6 (euclideanBall x₀ r) (u t).toFun ≤
        ENNReal.ofReal sobolevPoincareFaithfulC5 *
          (weakGradientLpNormOn 2 (euclideanBall x₀ r) (u t).grad +
            (ENNReal.ofReal r)⁻¹ * lpNormOn 2 (euclideanBall x₀ r) (u t).toFun) := by
  filter_upwards [] with t
  exact extSobolevBall_everyBall hr (u t)

end

end CKN
