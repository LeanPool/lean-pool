/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropSpatialIBP
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# A uniform bound for the regularized pairing derivative

After the spatial integrations by parts, the time derivative of the pairing
of a regularized velocity with a fixed smooth solenoidal test involves only
the velocity and the transport velocity, without derivatives. Their `L²`
bounds therefore control it uniformly, as in the proof of
`lem:reg-equicontinuity`.
-/

public section

open MeasureTheory
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The elementary estimate `|∫ f g| ≤ (∫ f² + ∫ g²) / 2`. -/
theorem lerayHopfLimit_abs_integral_mul_le_half_sq
    {f g : Vec3 → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun x => f x * g x) ∧
      |∫ x, f x * g x| ≤ ((∫ x, f x ^ 2) + ∫ x, g x ^ 2) / 2 := by
  have hf2 := hf.integrable_sq
  have hg2 := hg.integrable_sq
  have hsum : Integrable (fun x => (f x ^ 2 + g x ^ 2) / 2) :=
    (hf2.add hg2).div_const 2
  have hpt : ∀ x, |f x * g x| ≤ (f x ^ 2 + g x ^ 2) / 2 := by
    intro x
    rw [abs_le]
    constructor <;> nlinarith only [sq_nonneg (f x - g x), sq_nonneg (f x + g x)]
  have hint : Integrable (fun x => f x * g x) := by
    refine hsum.mono (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hpt x).trans (le_abs_self _)
  refine ⟨hint, ?_⟩
  calc |∫ x, f x * g x| ≤ ∫ x, |f x * g x| := abs_integral_le_integral_abs
    _ ≤ ∫ x, (f x ^ 2 + g x ^ 2) / 2 :=
        integral_mono hint.abs hsum hpt
    _ = ((∫ x, f x ^ 2) + ∫ x, g x ^ 2) / 2 := by
        rw [integral_div, integral_add hf2 hg2]

/-- A continuous compactly supported field is square integrable. -/
theorem lerayHopfLimit_memLp_two_of_compact
    {c : Vec3 → ℝ} (hc : Continuous c) (hcc : HasCompactSupport c) :
    MemLp c 2 volume :=
  hc.memLp_of_hasCompactSupport hcc

/-- The pairing derivative after the spatial integrations by parts is bounded
by a constant depending only on the test and on the `L²` bounds of the
velocity and the transport velocity. -/
theorem lerayHopfLimit_pairing_rhs_bound
    (w : Fin 3 → Vec3 → ℝ)
    (hw : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (w i)) (hwc : ∀ i, HasCompactSupport (w i))
    (B : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f J : Fin 3 → Vec3 → ℝ,
      (∀ i, MemLp (f i) 2 volume) → (∀ j, MemLp (J j) 2 volume) →
      (∀ i, ∫ x, f i x ^ 2 ≤ B ^ 2) → (∀ j, ∫ x, J j x ^ 2 ≤ B ^ 2) →
      |∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
        (f i x * spatialDeriv (spatialDeriv (w i) j) j x +
          f i x * J j x * spatialDeriv (w i) j x)| ≤ K := by
  have hdw : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv (w i) j) :=
    fun i j => contDiff_spatialDeriv_smooth (hw i) j
  have hdwc : ∀ i j, HasCompactSupport (spatialDeriv (w i) j) := by
    intro i j
    change HasCompactSupport (fun x => (fderiv ℝ (w i) x) (basisVec j))
    exact (hwc i).fderiv_apply (𝕜 := ℝ) (basisVec j)
  have hddw : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv (spatialDeriv (w i) j) j) :=
    fun i j => contDiff_spatialDeriv_smooth (hdw i j) j
  have hddwc : ∀ i j, HasCompactSupport (spatialDeriv (spatialDeriv (w i) j) j) := by
    intro i j
    change HasCompactSupport
      (fun x => (fderiv ℝ (spatialDeriv (w i) j) x) (basisVec j))
    exact (hdwc i j).fderiv_apply (𝕜 := ℝ) (basisVec j)
  have hbound : ∀ i j, ∃ C : ℝ, ∀ x, ‖spatialDeriv (w i) j x‖ ≤ C := fun i j =>
    (hdw i j).continuous.bounded_above_of_compact_support (hdwc i j)
  choose C hC using hbound
  let M : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, |C i j|
  have hM : ∀ i j x, |spatialDeriv (w i) j x| ≤ M := by
    intro i j x
    calc |spatialDeriv (w i) j x| ≤ |C i j| := (hC i j x).trans (le_abs_self _)
      _ ≤ ∑ j' : Fin 3, |C i j'| :=
          Finset.single_le_sum (f := fun j' => |C i j'|)
            (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      _ ≤ M := Finset.single_le_sum (f := fun i' => ∑ j' : Fin 3, |C i' j'|)
            (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
            (Finset.mem_univ i)
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  let c : Fin 3 → Fin 3 → ℝ := fun i j =>
    ∫ x, spatialDeriv (spatialDeriv (w i) j) j x ^ 2
  have hc0 : ∀ i j, 0 ≤ c i j := fun i j =>
    integral_nonneg (fun x => sq_nonneg _)
  refine ⟨∑ i : Fin 3, ∑ j : Fin 3, ((B ^ 2 + c i j) / 2 + M * B ^ 2), ?_, ?_⟩
  · exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by
      have := hc0 i j
      positivity))
  intro f J hf hJ hfB hJB
  have hddwL : ∀ i j, MemLp (spatialDeriv (spatialDeriv (w i) j) j) 2 volume :=
    fun i j => lerayHopfLimit_memLp_two_of_compact (hddw i j).continuous (hddwc i j)
  have hterm1 : ∀ i j, Integrable
      (fun x => f i x * spatialDeriv (spatialDeriv (w i) j) j x) ∧
      |∫ x, f i x * spatialDeriv (spatialDeriv (w i) j) j x| ≤ (B ^ 2 + c i j) / 2 := by
    intro i j
    obtain ⟨hint, hle⟩ := lerayHopfLimit_abs_integral_mul_le_half_sq (hf i) (hddwL i j)
    refine ⟨hint, hle.trans ?_⟩
    have := hfB i
    linarith only [this]
  have hfJ : ∀ i j, Integrable (fun x => f i x * J j x) ∧
      (∫ x, |f i x * J j x|) ≤ B ^ 2 := by
    intro i j
    obtain ⟨hint, _⟩ := lerayHopfLimit_abs_integral_mul_le_half_sq (hf i) (hJ j)
    have habs := lerayHopfLimit_abs_integral_mul_le_half_sq (hf i).norm (hJ j).norm
    refine ⟨hint, ?_⟩
    have heq : (fun x => |f i x * J j x|) = fun x => ‖f i x‖ * ‖J j x‖ := by
      funext x
      rw [abs_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    rw [heq]
    refine (le_abs_self _).trans (habs.2.trans ?_)
    simp only [Real.norm_eq_abs, sq_abs]
    linarith only [hfB i, hJB j]
  have hterm2 : ∀ i j, Integrable
      (fun x => f i x * J j x * spatialDeriv (w i) j x) ∧
      |∫ x, f i x * J j x * spatialDeriv (w i) j x| ≤ M * B ^ 2 := by
    intro i j
    obtain ⟨hint, hle⟩ := hfJ i j
    have hmeas : AEStronglyMeasurable
        (fun x => f i x * J j x * spatialDeriv (w i) j x) volume :=
      hint.aestronglyMeasurable.mul (hdw i j).continuous.aestronglyMeasurable
    have hdom : ∀ x, ‖f i x * J j x * spatialDeriv (w i) j x‖ ≤ M * |f i x * J j x| := by
      intro x
      rw [Real.norm_eq_abs, abs_mul]
      have := hM i j x
      have h0 := abs_nonneg (f i x * J j x)
      nlinarith only [this, h0]
    have hint2 : Integrable (fun x => f i x * J j x * spatialDeriv (w i) j x) :=
      (hint.abs.const_mul M).mono hmeas (Filter.Eventually.of_forall (fun x =>
        (hdom x).trans (le_of_eq (by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hM0 (abs_nonneg _))]))))
    refine ⟨hint2, ?_⟩
    calc |∫ x, f i x * J j x * spatialDeriv (w i) j x|
        ≤ ∫ x, M * |f i x * J j x| := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_of_norm_le (hint.abs.const_mul M)
            (Filter.Eventually.of_forall hdom)
      _ = M * ∫ x, |f i x * J j x| := integral_const_mul _ _
      _ ≤ M * B ^ 2 := by
          exact mul_le_mul_of_nonneg_left hle hM0
  have hpair : ∀ i j, Integrable (fun x =>
      f i x * spatialDeriv (spatialDeriv (w i) j) j x +
        f i x * J j x * spatialDeriv (w i) j x) := fun i j =>
    (hterm1 i j).1.add (hterm2 i j).1
  have hrow : ∀ i, Integrable (fun x => ∑ j : Fin 3,
      (f i x * spatialDeriv (spatialDeriv (w i) j) j x +
        f i x * J j x * spatialDeriv (w i) j x)) := fun i =>
    integrable_finsetSum _ (fun j _ => hpair i j)
  rw [integral_finsetSum _ (fun i _ => hrow i)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [integral_finsetSum _ (fun j _ => hpair i j)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
  rw [integral_add (hterm1 i j).1 (hterm2 i j).1]
  exact (abs_add_le _ _).trans (add_le_add (hterm1 i j).2 (hterm2 i j).2)

end CKN.Leray

end
