/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.TaylorTwoVector

/-!
# The second-order Taylor bound against a modulus of continuity

A Lipschitz second derivative is more than the Taylor bound needs: the remainder is controlled by
the oscillation of the second derivative on the segment alone, which is what a merely continuous
second derivative supplies. The affine form `A + K‖z − w‖` of the oscillation bound covers a
Lipschitz second derivative (`A = 0`) and a merely uniformly continuous one (`K` chosen from the
modulus at scale `A`) in one statement.

## Main statements

* `LevyStochCalc.abs_sub_taylor_two_le_modulus_normed` — the bound by the oscillation on the
  segment.
* `LevyStochCalc.abs_sub_taylor_two_le_affine` — the bound `A‖y − x‖² + K‖y − x‖³` under an
  affine oscillation bound.
* `LevyStochCalc.abs_taylorRemainderNormed_le_affine` — its telescoped form along a sequence.
-/

@[expose] public section

namespace LevyStochCalc

/-- **First-order Taylor against an oscillation bound.** -/
theorem abs_sub_taylor_one_le_modulus {f f' : ℝ → ℝ} {M : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) {x y : ℝ}
    (hM : ∀ w ∈ Set.uIcc x y, |f' w - f' x| ≤ M) :
    |f y - f x - f' x * (y - x)| ≤ M * |y - x| := by
  have hconv : Convex ℝ (Set.uIcc x y) := convex_uIcc x y
  have hg : ∀ w ∈ Set.uIcc x y, HasDerivWithinAt (fun z => f z - f x - f' x * (z - x))
      (f' w - f' x) (Set.uIcc x y) w := by
    intro w _
    have hA : HasDerivAt (fun z : ℝ => f z - f x) (f' w) w := (hf w).sub_const (f x)
    have hB : HasDerivAt (fun z : ℝ => z - x) (1 : ℝ) w := (hasDerivAt_id w).sub_const x
    have hC : HasDerivAt (fun z : ℝ => f' x * (z - x)) (f' x * 1) w := hB.const_mul (f' x)
    have h1 : HasDerivAt (fun z : ℝ => f z - f x - f' x * (z - x)) (f' w - f' x * 1) w :=
      hA.sub hC
    rw [mul_one] at h1
    exact h1.hasDerivWithinAt
  have hbound : ∀ w ∈ Set.uIcc x y, ‖f' w - f' x‖ ≤ M := by
    intro w hw
    rw [Real.norm_eq_abs]
    exact hM w hw
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg hbound hconv
    Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [Real.norm_eq_abs] using hmain

/-- **Second-order Taylor against an oscillation bound.** -/
theorem abs_sub_taylor_two_le_modulus {f f' f'' : ℝ → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    {x y : ℝ} (hM : ∀ w ∈ Set.uIcc x y, |f'' w - f'' x| ≤ M) :
    |f y - f x - f' x * (y - x) - f'' x * (y - x) ^ 2 / 2| ≤ M * |y - x| ^ 2 := by
  have hconv : Convex ℝ (Set.uIcc x y) := convex_uIcc x y
  have hstep1 : ∀ w ∈ Set.uIcc x y, |f' w - f' x - f'' x * (w - x)| ≤ M * |y - x| := by
    intro w hw
    have hsub : Set.uIcc x w ⊆ Set.uIcc x y := Set.uIcc_subset_uIcc Set.left_mem_uIcc hw
    have hloc := abs_sub_taylor_one_le_modulus (f := f') (f' := f'') hf'
      (x := x) (y := w) (fun u hu => hM u (hsub hu))
    exact hloc.trans (mul_le_mul_of_nonneg_left (abs_sub_le_of_mem_uIcc hw) hM0)
  have hF : ∀ w ∈ Set.uIcc x y, HasDerivWithinAt
      (fun z => f z - f x - f' x * (z - x) - f'' x * (z - x) ^ 2 / 2)
      (f' w - f' x - f'' x * (w - x)) (Set.uIcc x y) w := by
    intro w _
    have hA : HasDerivAt (fun z : ℝ => f z - f x) (f' w) w := (hf w).sub_const (f x)
    have hB : HasDerivAt (fun z : ℝ => z - x) (1 : ℝ) w := (hasDerivAt_id w).sub_const x
    have hC : HasDerivAt (fun z : ℝ => f' x * (z - x)) (f' x * 1) w := hB.const_mul (f' x)
    have hD : HasDerivAt (fun z : ℝ => (z - x) ^ 2) (2 * (w - x)) w := by
      have h : HasDerivAt (fun z : ℝ => (z - x) * (z - x)) (1 * (w - x) + (w - x) * 1) w :=
        hB.mul hB
      have hfun : (fun z : ℝ => (z - x) * (z - x)) = fun z : ℝ => (z - x) ^ 2 := by
        funext z; ring
      rw [hfun] at h
      convert h using 1
      ring
    have hE : HasDerivAt (fun z : ℝ => f'' x * (z - x) ^ 2 / 2)
        (f'' x * (2 * (w - x)) / 2) w := (hD.const_mul (f'' x)).div_const 2
    have h1 := (hA.sub hC).sub hE
    have heq : f' w - f' x * 1 - f'' x * (2 * (w - x)) / 2
        = f' w - f' x - f'' x * (w - x) := by ring
    rw [heq] at h1
    exact h1.hasDerivWithinAt
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hF
    (fun w hw => by rw [Real.norm_eq_abs]; exact hstep1 w hw) hconv
    Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [Real.norm_eq_abs] at hmain
  have h0 : f x - f x - f' x * (x - x) - f'' x * (x - x) ^ 2 / 2 = 0 := by ring
  rw [h0, sub_zero] at hmain
  calc |f y - f x - f' x * (y - x) - f'' x * (y - x) ^ 2 / 2|
      ≤ M * |y - x| * |y - x| := hmain
    _ = M * |y - x| ^ 2 := by ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Second-order Taylor on a normed space against an oscillation bound.** The remainder is
controlled by the oscillation of the second derivative on the segment joining the two points. -/
theorem abs_sub_taylor_two_le_modulus_normed {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z) {x y : E}
    (hM : ∀ z ∈ segment ℝ x y, ‖f'' z - f'' x‖ ≤ M) :
    |f y - f x - f' x (y - x) - f'' x (y - x) (y - x) / 2| ≤ M * ‖y - x‖ ^ 2 := by
  set v : E := y - x with hv
  have hseg : ∀ t : ℝ, HasDerivAt (fun r : ℝ => x + r • v) v t := fun t => by
    have h := ((hasDerivAt_id t).smul_const v).const_add x
    simpa using h
  have hg : ∀ t : ℝ, HasDerivAt (fun r : ℝ => f (x + r • v)) (f' (x + t • v) v) t := fun t =>
    (hf (x + t • v)).comp_hasDerivAt t (hseg t)
  have hg' : ∀ t : ℝ,
      HasDerivAt (fun r : ℝ => f' (x + r • v) v) (f'' (x + t • v) v v) t := fun t => by
    have hap : HasFDerivAt (fun z : E => f' z v)
        ((ContinuousLinearMap.apply ℝ ℝ v).comp (f'' (x + t • v))) (x + t • v) :=
      (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp _ (hf' (x + t • v))
    exact hap.comp_hasDerivAt t (hseg t)
  have hosc : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
      |f'' (x + u • v) v v - f'' (x + (0 : ℝ) • v) v v| ≤ M * ‖v‖ ^ 2 := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    have hmem : x + u • v ∈ segment ℝ x y := by
      rw [segment_eq_image' ℝ x y]
      exact ⟨u, hu, rfl⟩
    have hsub : f'' (x + u • v) v v - f'' (x + (0 : ℝ) • v) v v
        = (f'' (x + u • v) - f'' x) v v := by simp
    have hbd : ‖(f'' (x + u • v) - f'' x) v v‖
        ≤ ‖f'' (x + u • v) - f'' x‖ * ‖v‖ * ‖v‖ :=
      ContinuousLinearMap.le_opNorm₂ _ v v
    calc |f'' (x + u • v) v v - f'' (x + (0 : ℝ) • v) v v|
        = ‖(f'' (x + u • v) - f'' x) v v‖ := by rw [hsub]; exact (Real.norm_eq_abs _).symm
      _ ≤ ‖f'' (x + u • v) - f'' x‖ * ‖v‖ * ‖v‖ := hbd
      _ ≤ M * ‖v‖ * ‖v‖ := by gcongr; exact hM _ hmem
      _ = M * ‖v‖ ^ 2 := by ring
  have hmain := abs_sub_taylor_two_le_modulus (f := fun r : ℝ => f (x + r • v))
    (f' := fun r : ℝ => f' (x + r • v) v) (f'' := fun r : ℝ => f'' (x + r • v) v v)
    (M := M * ‖v‖ ^ 2) (by positivity) hg hg' (x := 0) (y := 1) hosc
  simpa [hv] using hmain

/-- **Second-order Taylor against an affine modulus.** If the second derivative satisfies
`‖f'' z − f'' w‖ ≤ A + K‖z − w‖`, the second-order Taylor remainder is at most
`A‖y − x‖² + K‖y − x‖³`. -/
theorem abs_sub_taylor_two_le_affine {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hf'' : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖) (x y : E) :
    |f y - f x - f' x (y - x) - f'' x (y - x) (y - x) / 2|
      ≤ A * ‖y - x‖ ^ 2 + K * ‖y - x‖ ^ 3 := by
  have hM0 : (0 : ℝ) ≤ A + K * ‖y - x‖ := by positivity
  have hM : ∀ z ∈ segment ℝ x y, ‖f'' z - f'' x‖ ≤ A + K * ‖y - x‖ := by
    intro z hz
    rw [segment_eq_image' ℝ x y] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    have hnorm : ‖x + θ • (y - x) - x‖ = θ * ‖y - x‖ := by
      have hsub : x + θ • (y - x) - x = θ • (y - x) := by module
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
    refine (hf'' _ x).trans ?_
    rw [hnorm]
    have : K * (θ * ‖y - x‖) ≤ K * ‖y - x‖ := by
      refine mul_le_mul_of_nonneg_left ?_ hK0
      nlinarith [norm_nonneg (y - x), hθ.1, hθ.2]
    linarith
  have hmain := abs_sub_taylor_two_le_modulus_normed hM0 hf hf' hM
  refine hmain.trans (le_of_eq ?_)
  ring

/-- **Telescoped second-order Taylor expansion against an affine modulus.** -/
theorem abs_taylorRemainderNormed_le_affine {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hf'' : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖) (x : ℕ → E) (m : ℕ) :
    |taylorRemainderNormed f f' f'' x m|
      ≤ A * ∑ i ∈ Finset.range m, ‖x (i + 1) - x i‖ ^ 2
        + K * ∑ i ∈ Finset.range m, ‖x (i + 1) - x i‖ ^ 3 := by
  unfold taylorRemainderNormed
  have htel : f (x m) - f (x 0) = ∑ i ∈ Finset.range m, (f (x (i + 1)) - f (x i)) :=
    (Finset.sum_range_sub (fun i => f (x i)) m).symm
  rw [htel, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have heq : f (x (i + 1)) - f (x i)
      - (f' (x i) (x (i + 1) - x i) + f'' (x i) (x (i + 1) - x i) (x (i + 1) - x i) / 2)
      = f (x (i + 1)) - f (x i) - f' (x i) (x (i + 1) - x i)
        - f'' (x i) (x (i + 1) - x i) (x (i + 1) - x i) / 2 := by ring
  rw [heq]
  exact abs_sub_taylor_two_le_affine hA0 hK0 hf hf' hf'' (x i) (x (i + 1))

end LevyStochCalc
