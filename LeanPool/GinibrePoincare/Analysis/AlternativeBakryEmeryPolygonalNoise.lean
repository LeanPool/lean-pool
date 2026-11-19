/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryPolygonalNoise.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGaussianNoiseLSI
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Actual finite Gaussian coordinates for polygonal Langevin noise.
Each coordinate has variance one; its increment has variance `h`, before
multiplication by the Langevin diffusion amplitude `sqrt 2`. -/

@[expose] public section

open scoped BigOperators Topology
namespace GinibrePoincare
noncomputable section

variable {ι : Type*}

/-- The normalised ramp of the `j`-th time step of length `h`: `min (max (t - j h) 0) h / √h`,
rising linearly from `0` to `√h` on `[j h, (j + 1) h]`. -/
def bakryEmeryPolygonalRamp (h : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  min (max (t - (j : ℝ)*h) 0) h / Real.sqrt h

/-- The polygonal noise path `t ↦ (∑ j < m, ramp_j(t) * x (j, i))_i` linearly interpolating the
`m` step increments `x (j, ·)` on a grid of step `h`. -/
def bakryEmeryPolygonalNoise (m : ℕ) (h : ℝ)
    (x : (Fin m × ι) → ℝ) (t : ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => ∑ j : Fin m, bakryEmeryPolygonalRamp h j.val t * x (j, i))

theorem bakryEmeryPolygonalRamp_continuous (h : ℝ) (j : ℕ) :
    Continuous (bakryEmeryPolygonalRamp h j) := by
  unfold bakryEmeryPolygonalRamp
  fun_prop

theorem bakryEmeryPolygonalNoise_continuous (m : ℕ) (h : ℝ)
    (x : (Fin m × ι) → ℝ) : Continuous (bakryEmeryPolygonalNoise m h x) := by
  classical
  unfold bakryEmeryPolygonalNoise
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  exact continuous_finsetSum _ (fun j _ =>
    (bakryEmeryPolygonalRamp_continuous h j.val).mul continuous_const)

theorem bakryEmeryPolygonalNoise_zero (m : ℕ) (h : ℝ) (hh : 0 ≤ h)
    (x : (Fin m × ι) → ℝ) : bakryEmeryPolygonalNoise m h x 0 = 0 := by
  classical
  unfold bakryEmeryPolygonalNoise bakryEmeryPolygonalRamp
  have h0 (j : Fin m) : max (0 - (j.val : ℝ)*h) 0 = 0 :=
    max_eq_right (by
      have hp : 0 ≤ (j.val : ℝ)*h := by positivity
      linarith)
  simp only [h0, min_eq_left hh, zero_div, zero_mul, Finset.sum_const_zero]
  rfl

theorem bakryEmeryPolygonalRamp_on_interval (h : ℝ) (_ : 0 ≤ h)
    (j : ℕ) (t : ℝ) (ht : (j : ℝ) * h ≤ t) (ht' : t ≤ (j + 1 : ℕ) * h) :
    bakryEmeryPolygonalRamp h j t = (t-(j : ℝ)*h)/Real.sqrt h := by
  unfold bakryEmeryPolygonalRamp
  rw [max_eq_left (by linarith), min_eq_left]
  push_cast at ht'
  nlinarith

theorem bakryEmeryPolygonalRamp_before (h : ℝ) (hh : 0 ≤ h)
    (j : ℕ) (t : ℝ) (ht : t ≤ (j : ℝ) * h) :
    bakryEmeryPolygonalRamp h j t = 0 := by
  unfold bakryEmeryPolygonalRamp
  rw [max_eq_right (by linarith), min_eq_left hh]
  simp

theorem bakryEmeryPolygonalRamp_after (h : ℝ) (hh : 0 < h)
    (j : ℕ) (t : ℝ) (ht : (j + 1 : ℕ) * h ≤ t) :
    bakryEmeryPolygonalRamp h j t = Real.sqrt h := by
  unfold bakryEmeryPolygonalRamp
  push_cast at ht
  rw [max_eq_left (by nlinarith), min_eq_right (by nlinarith)]
  apply (div_eq_iff (Real.sqrt_ne_zero'.mpr hh)).mpr
  exact (Real.mul_self_sqrt hh.le).symm

theorem bakryEmeryPolygonalRamp_hasDerivAt (h : ℝ) (hh : 0 < h)
    (j : ℕ) (t : ℝ) (ht : t ∈ Set.Ioo ((j : ℝ) * h) ((j + 1 : ℕ) * h)) :
    HasDerivAt (bakryEmeryPolygonalRamp h j) (1 / Real.sqrt h) t := by
  have heq : bakryEmeryPolygonalRamp h j =ᶠ[nhds t]
      (fun s => (s-(j : ℝ)*h)/Real.sqrt h) := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioo ht] with s hs
    exact bakryEmeryPolygonalRamp_on_interval h hh.le j s hs.1.le hs.2.le
  exact (((hasDerivAt_id t).sub_const ((j : ℝ)*h)).div_const (Real.sqrt h)).congr_of_eventuallyEq
      heq

theorem bakryEmeryPolygonalRamp_hasDerivAt_on_other_interval
    (h : ℝ) (hh : 0 < h) (j k : ℕ) (hjk : j ≠ k)
    (t : ℝ) (ht : t ∈ Set.Ioo ((k : ℝ) * h) ((k + 1 : ℕ) * h)) :
    HasDerivAt (bakryEmeryPolygonalRamp h j) 0 t := by
  rcases lt_or_gt_of_ne hjk with hlt | hgt
  · have heq : bakryEmeryPolygonalRamp h j =ᶠ[nhds t] (fun _ => Real.sqrt h) := by
      filter_upwards [IsOpen.mem_nhds isOpen_Ioo ht] with z hz
      apply bakryEmeryPolygonalRamp_after h hh
      have hj : (j+1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hlt
      push_cast
      have hz0 := hz.1
      nlinarith [mul_le_mul_of_nonneg_right hj hh.le]
    exact (hasDerivAt_const t (Real.sqrt h)).congr_of_eventuallyEq heq
  · have heq : bakryEmeryPolygonalRamp h j =ᶠ[nhds t] (fun _ => 0) := by
      filter_upwards [IsOpen.mem_nhds isOpen_Ioo ht] with z hz
      apply bakryEmeryPolygonalRamp_before h hh.le
      have hj : (k+1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hgt
      push_cast at hz
      have hz1 := hz.2
      nlinarith [mul_le_mul_of_nonneg_right hj hh.le]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq heq

/-- Euclidean space over a finite index type has continuous scalar multiplication. -/
scoped instance euclideanSpace_continuousSMul_of_finite [Finite ι] :
    ContinuousSMul ℝ (EuclideanSpace ℝ ι) := by
  have := Fintype.ofFinite ι
  infer_instance

/-- The literal polygon has the desired constant velocity on each open grid interval. -/
theorem bakryEmeryPolygonalNoise_hasDerivAt [Finite ι] (m : ℕ) (h : ℝ) (hh : 0 < h)
    (x : (Fin m × ι) → ℝ) (k : Fin m) (t : ℝ)
    (ht : t ∈ Set.Ioo ((k.val : ℝ) * h) ((k.val + 1 : ℕ) * h)) :
    HasDerivAt (bakryEmeryPolygonalNoise m h x)
      (WithLp.toLp 2 (fun i => x (k, i) / Real.sqrt h)) t := by
  classical
  have := Fintype.ofFinite ι
  have hg : HasDerivAt
      (fun s => fun i => ∑ j : Fin m, bakryEmeryPolygonalRamp h j.val s * x (j, i))
      (fun i => x (k, i)/Real.sqrt h) t := by
    apply hasDerivAt_pi.mpr
    intro i
    have hd (j : Fin m) : HasDerivAt
        (fun s => bakryEmeryPolygonalRamp h j.val s * x (j, i))
        (if j = k then x (k, i)/Real.sqrt h else 0) t := by
      by_cases hj : j = k
      · subst j
        simpa [mul_comm, div_eq_mul_inv] using
          (bakryEmeryPolygonalRamp_hasDerivAt h hh k.val t ht).mul_const (x (k, i))
      · have hjv : j.val ≠ k.val := fun he => hj (Fin.ext he)
        simpa [hj] using
          (bakryEmeryPolygonalRamp_hasDerivAt_on_other_interval h hh j.val k.val hjv t
            ht).mul_const (x (j, i))
    simpa using (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hd j))
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.hasFDerivAt.comp_hasDerivAt t hg)

/-- Joint continuity of the actual finite-noise encoding, for subsequent
measurable flow selection and Brownian approximation. -/
theorem bakryEmeryPolygonalNoise_joint_continuous (m : ℕ) (h : ℝ) :
    Continuous (fun p : (((Fin m × ι) → ℝ) × ℝ) =>
      bakryEmeryPolygonalNoise m h p.1 p.2) := by
  classical
  unfold bakryEmeryPolygonalNoise
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  apply continuous_finsetSum
  intro j _
  exact ((bakryEmeryPolygonalRamp_continuous h j.val).comp continuous_snd).mul
    ((continuous_apply (j, i)).comp continuous_fst)

end
end GinibrePoincare
