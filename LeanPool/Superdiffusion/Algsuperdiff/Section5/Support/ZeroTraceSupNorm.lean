/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.HolderCalculus
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.ComparatorUniformBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.ZeroTraceBoundary

/-!
# ZeroTraceSupNorm

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The supremum norm of a function vanishing on the boundary of a cube

A function on `y + □_n` that extends continuously to the closed cube and
vanishes on its boundary is bounded by its own `1/2`-Hölder seminorm:

```text
  ‖w‖_{L^∞(y+□_n)} ≤ (3^n / 2)^{1/2} [w]_{C^{0,1/2}(y+□_n)} .
```

The proof is the one-line geometric argument.  The ambient norm of
`Vec d = Fin d → ℝ` is the supremum norm, so `y + □_n` is the ball of radius
`3^n/2` around `y`; every point `x` of it lies on a radius whose endpoint `z₀`
is a boundary point at distance `3^n/2 - ‖x - y‖ ≤ 3^n/2`, the segment from `x`
to `z₀` stays inside the cube, and the Hölder bound along that segment passes to
the endpoint by continuity, where the value is zero.

Since `(3^n/2)^{1/2} ≤ 3^{n/2}`, the bound is also stated with the constant
`3^{n/2}` in which the localized estimates of Section 5 are written.

For a Sobolev function the boundary hypothesis is the zero-trace property, and
no regularity beyond it is needed: `Section5/Support/ZeroTraceBoundary.lean`
shows that a representative of an `H¹₀` function takes arbitrarily small values
arbitrarily close to the boundary, which is exactly what the geometric argument
consumes at the endpoint of the radius.

## References

* ABK26, the localized estimates of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The cube of the supremum norm is a ball -/

/-- **`y + □_n` is the ball of radius `3^n/2` around `y`**, because the ambient
norm of `Vec d` is the supremum norm. -/
theorem cubeSetAt_eq_ball (y : Vec d) (n : ℤ) :
    cubeSetAt y n = Metric.ball y ((1 / 2 : ℝ) * (3 : ℝ) ^ n) := by
  have hA : (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by positivity
  ext x
  rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hA, mem_cubeSetAt_iff_forall_coord]
  refine forall_congr' fun i => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_lt]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith only [h1], h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith only [h1], h2⟩

theorem closure_cubeSetAt (y : Vec d) (n : ℤ) :
    closure (cubeSetAt y n) = Metric.closedBall y ((1 / 2 : ℝ) * (3 : ℝ) ^ n) := by
  have hA : (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by positivity
  rw [cubeSetAt_eq_ball, closure_ball y hA.ne']

theorem frontier_cubeSetAt (y : Vec d) (n : ℤ) :
    frontier (cubeSetAt y n) = Metric.sphere y ((1 / 2 : ℝ) * (3 : ℝ) ^ n) := by
  have hA : (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by positivity
  rw [cubeSetAt_eq_ball, frontier_ball y hA.ne']

theorem mem_closure_cubeSetAt_iff {y : Vec d} {n : ℤ} {x : Vec d} :
    x ∈ closure (cubeSetAt y n) ↔ ‖x - y‖ ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
  rw [closure_cubeSetAt, Metric.mem_closedBall, dist_eq_norm]

theorem mem_frontier_cubeSetAt_iff {y : Vec d} {n : ℤ} {x : Vec d} :
    x ∈ frontier (cubeSetAt y n) ↔ ‖x - y‖ = (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
  rw [frontier_cubeSetAt, Metric.mem_sphere, dist_eq_norm]

theorem mem_cubeSetAt_iff_norm_sub_lt {y : Vec d} {n : ℤ} {x : Vec d} :
    x ∈ cubeSetAt y n ↔ ‖x - y‖ < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
  rw [cubeSetAt_eq_ball, Metric.mem_ball, dist_eq_norm]

/-! ## 2. A radius through a point of the cube -/

/-- In dimension at least one there is a vector of norm one. -/
private theorem exists_norm_eq_one (hd : 0 < d) : ∃ u : Vec d, ‖u‖ = 1 := by
  refine ⟨basisVec (⟨0, hd⟩ : Fin d), le_antisymm ?_ ?_⟩
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    by_cases hj : j = ⟨0, hd⟩ <;> simp [basisVec, hj]
  · have h := norm_le_pi_norm (basisVec (⟨0, hd⟩ : Fin d)) ⟨0, hd⟩
    simpa only [basisVec, Pi.single_eq_same, norm_one] using h

/-- Every point of `ℝ^d` is the centre `y` displaced by its distance to `y`
along a vector of norm one. -/
private theorem exists_norm_eq_one_sub_eq (hd : 0 < d) (x y : Vec d) :
    ∃ u : Vec d, ‖u‖ = 1 ∧ x - y = ‖x - y‖ • u := by
  rcases eq_or_ne x y with rfl | hxy
  · obtain ⟨u, hu⟩ := exists_norm_eq_one hd
    exact ⟨u, hu, by simp⟩
  · have hne : ‖x - y‖ ≠ 0 := by
      rw [norm_ne_zero_iff]
      exact sub_ne_zero.2 hxy
    refine ⟨‖x - y‖⁻¹ • (x - y), ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hne]
    · rw [smul_inv_smul₀ hne]

/-! ## 3. The bound for a function vanishing on the boundary -/

/-- The sharp constant `(3^n/2)^{1/2}` is dominated by the constant `3^{n/2}` in
which the localized estimates of Section 5 are written. -/
private theorem rpow_half_cube_le_rpow_three_half (n : ℤ) :
    ((1 / 2 : ℝ) * (3 : ℝ) ^ n) ^ (1 / 2 : ℝ) ≤ Real.rpow 3 ((n : ℝ) / 2) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hstep : ((1 / 2 : ℝ) * (3 : ℝ) ^ n) ^ (1 / 2 : ℝ) ≤ ((3 : ℝ) ^ n) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith only [h3]) (by norm_num)
  refine hstep.trans (le_of_eq ?_)
  rw [← Real.rpow_intCast 3 n, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-! ## 4. A function vanishing outside the closed cube -/

theorem closure_cubeSetAt_subset_cubeSetAt_succ (y : Vec d) (n : ℤ) :
    closure (cubeSetAt y n) ⊆ cubeSetAt y (n + 1) := by
  intro x hx
  rw [mem_closure_cubeSetAt_iff] at hx
  rw [mem_cubeSetAt_iff_norm_sub_lt]
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hsucc : (3 : ℝ) ^ (n + 1) = 3 * (3 : ℝ) ^ n := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  rw [hsucc]
  linarith only [hx, h3]

/-! ## 5. The zero-trace Sobolev function -/

private theorem sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have hcross : 0 ≤ Real.sqrt a * Real.sqrt b :=
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  have hsq : (Real.sqrt a + Real.sqrt b) ^ 2 = a + 2 * (Real.sqrt a * Real.sqrt b) + b := by
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
    ring
  have hle : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    rw [hsq]
    linarith only [hcross]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq (by positivity)

/-- The pointwise bound behind the zero-trace form: the value at `x` is compared
with the values of the representative at points of the cube arbitrarily close to
the boundary point on the radius through `x`, where they are arbitrarily
small. -/
private theorem abs_le_of_zeroTrace (hd : 0 < d) {y : Vec d} {n : ℤ}
    (w : H10Function (cubeSetAt y n)) {v : Vec d → ℝ}
    (hv : v =ᵐ[volume.restrict (cubeSetAt y n)] w.toH1Function.toFun)
    {K : ℝ} (hK : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) K v)
    {x : Vec d} (hx : x ∈ cubeSetAt y n) :
    |v x| ≤ ((1 / 2 : ℝ) * (3 : ℝ) ^ n) ^ (1 / 2 : ℝ) * K := by
  have hA : (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by positivity
  obtain ⟨u, hu, hxu⟩ := exists_norm_eq_one_sub_eq hd x y
  -- the boundary point on the radius through `x`
  have hz₀ : y + ((1 / 2 : ℝ) * (3 : ℝ) ^ n) • u ∈ frontier (cubeSetAt y n) := by
    rw [mem_frontier_cubeSetAt_iff, add_sub_cancel_left, norm_smul, hu, mul_one,
      Real.norm_eq_abs, abs_of_pos hA]
  have hxz : x - (y + ((1 / 2 : ℝ) * (3 : ℝ) ^ n) • u)
      = (‖x - y‖ - (1 / 2 : ℝ) * (3 : ℝ) ^ n) • u := by
    have h1 : x - (y + ((1 / 2 : ℝ) * (3 : ℝ) ^ n) • u)
        = (x - y) - ((1 / 2 : ℝ) * (3 : ℝ) ^ n) • u := by abel
    rw [h1, sub_smul, ← hxu]
  have hxzle : ‖x - (y + ((1 / 2 : ℝ) * (3 : ℝ) ^ n) • u)‖ ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
    have hlt : ‖x - y‖ < (1 / 2 : ℝ) * (3 : ℝ) ^ n := mem_cubeSetAt_iff_norm_sub_lt.1 hx
    rw [hxz, norm_smul, hu, mul_one, Real.norm_eq_abs,
      abs_of_nonpos (by linarith only [hlt])]
    linarith only [norm_nonneg (x - y)]
  -- the Hölder constant is nonnegative
  have hhalf : y + (((1 / 2 : ℝ) * (3 : ℝ) ^ n) / 2) • u ∈ cubeSetAt y n := by
    rw [mem_cubeSetAt_iff_norm_sub_lt, add_sub_cancel_left, norm_smul, hu, mul_one,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith only [hA]
  have hne : y ≠ y + (((1 / 2 : ℝ) * (3 : ℝ) ^ n) / 2) • u := by
    intro hzero
    have hnorm : ‖(y + (((1 / 2 : ℝ) * (3 : ℝ) ^ n) / 2) • u) - y‖ = 0 := by
      rw [← hzero, sub_self, norm_zero]
    rw [add_sub_cancel_left, norm_smul, hu, mul_one, Real.norm_eq_abs,
      abs_of_pos (by positivity)] at hnorm
    linarith only [hnorm, hA]
  have hK0 : 0 ≤ K := hK.nonneg (mem_cubeSetAt_self y n) hhalf hne
  -- the value at `x` is bounded by the constant plus an arbitrarily small error
  rw [← Real.sqrt_eq_rpow]
  refine le_of_forall_pos_le_add fun eps heps => ?_
  set delta : ℝ := min ((eps / (2 * (K + 1))) ^ 2) (eps / 2) with hdeltadef
  have hdelta0 : 0 < delta := by
    rw [hdeltadef]
    exact lt_min (by positivity) (by linarith only [heps])
  obtain ⟨x', hx', hx'dist, hx'small⟩ :=
    exists_mem_cubeSetAt_abs_lt_of_mem_frontier w hv hz₀ hdelta0 hdelta0
  have hxx' : ‖x - x'‖ ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n + delta := by
    have htri : ‖x - x'‖ ≤ ‖x - (y + ((1 / 2 : ℝ) * (3 : ℝ) ^ n) • u)‖ +
        ‖(y + ((1 / 2 : ℝ) * (3 : ℝ) ^ n) • u) - x'‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have hrev : ‖(y + ((1 / 2 : ℝ) * (3 : ℝ) ^ n) • u) - x'‖ = ‖x' - (y +
        ((1 / 2 : ℝ) * (3 : ℝ) ^ n) • u)‖ := norm_sub_rev _ _
    linarith only [htri, hrev, hxzle, hx'dist]
  have hholder : |v x - v x'| ≤ K * ‖x - x'‖ ^ (1 / 2 : ℝ) := by
    have h := hK x hx x' hx'
    rwa [Real.norm_eq_abs] at h
  have hsqrtle : ‖x - x'‖ ^ (1 / 2 : ℝ) ≤
      Real.sqrt ((1 / 2 : ℝ) * (3 : ℝ) ^ n) + Real.sqrt delta := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.sqrt_le_sqrt hxx').trans (sqrt_add_le_sqrt_add_sqrt hA.le hdelta0.le)
  have hstep : K * ‖x - x'‖ ^ (1 / 2 : ℝ) ≤
      K * (Real.sqrt ((1 / 2 : ℝ) * (3 : ℝ) ^ n) + Real.sqrt delta) :=
    mul_le_mul_of_nonneg_left hsqrtle hK0
  -- the error terms are below `eps`
  have hsqrtdelta : Real.sqrt delta ≤ eps / (2 * (K + 1)) := by
    have hmono : Real.sqrt delta ≤ Real.sqrt ((eps / (2 * (K + 1))) ^ 2) :=
      Real.sqrt_le_sqrt (by rw [hdeltadef]; exact min_le_left _ _)
    rwa [Real.sqrt_sq (by positivity)] at hmono
  have hKdelta : K * Real.sqrt delta ≤ eps / 2 := by
    have h1 : K * Real.sqrt delta ≤ K * (eps / (2 * (K + 1))) :=
      mul_le_mul_of_nonneg_left hsqrtdelta hK0
    have hKp : (0 : ℝ) < K + 1 := by linarith only [hK0]
    have h2 : K * (eps / (2 * (K + 1))) ≤ eps / 2 := by
      have hrw : K * (eps / (2 * (K + 1))) = K / (K + 1) * (eps / 2) := by
        field_simp
      have hfrac : K / (K + 1) ≤ 1 := by
        rw [div_le_one hKp]
        linarith only [hK0]
      calc K * (eps / (2 * (K + 1))) = K / (K + 1) * (eps / 2) := hrw
        _ ≤ 1 * (eps / 2) := mul_le_mul_of_nonneg_right hfrac (by linarith only [heps])
        _ = eps / 2 := one_mul _
    linarith only [h1, h2]
  have hdeltale : delta ≤ eps / 2 := by
    rw [hdeltadef]
    exact min_le_right _ _
  have hfinal : |v x| ≤ |v x - v x'| + |v x'| := by
    have hsplit : |v x| - |v x'| ≤ |v x - v x'| := abs_sub_abs_le_abs_sub _ _
    linarith only [hsplit]
  have hmulrw : K * (Real.sqrt ((1 / 2 : ℝ) * (3 : ℝ) ^ n) + Real.sqrt delta)
      = Real.sqrt ((1 / 2 : ℝ) * (3 : ℝ) ^ n) * K + K * Real.sqrt delta := by ring
  linarith only [hfinal, hholder, hstep, hmulrw, hKdelta, hdeltale, hx'small]

/-- **The continuous representative of a zero-trace Sobolev function is bounded
on `y + □_n` by its own `1/2`-Hölder seminorm**, with the sharp constant
`(3^n/2)^{1/2}`, the square root of the largest distance from a point of the
cube to the boundary along a radius.

No regularity beyond membership in `H¹₀` is assumed: the boundary values of the
representative are read off from the translation estimate for the zero
extension. -/
theorem supNormOn_le_of_zeroTrace (hd : 0 < d) {y : Vec d} {n : ℤ}
    {v : H1Function (cubeSetAt y n)}
    (hw : ∃ w : H10Function (cubeSetAt y n), ∀ x, v.toFun x = w.toH1Function.toFun x)
    {vRep : Vec d → ℝ} (hrep : IsCubeRepresentative y n v vRep) :
    supNormOn (cubeSetAt y n) vRep ≤
      ENNReal.ofReal (((1 / 2 : ℝ) * (3 : ℝ) ^ n) ^ (1 / 2 : ℝ)) *
        holderSeminormOn (cubeSetAt y n) (1 / 2) vRep := by
  obtain ⟨w, hwf⟩ := hw
  have hvae : vRep =ᵐ[volume.restrict (cubeSetAt y n)] w.toH1Function.toFun := by
    filter_upwards [hrep.1] with x hx
    rw [hx, hwf x]
  have hApos : (0 : ℝ) < ((1 / 2 : ℝ) * (3 : ℝ) ^ n) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hne : ENNReal.ofReal (((1 / 2 : ℝ) * (3 : ℝ) ^ n) ^ (1 / 2 : ℝ)) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hApos
  rcases eq_or_lt_of_le (le_top (a := holderSeminormOn (cubeSetAt y n) (1 / 2) vRep)) with
    htop | hlt
  · rw [htop, ENNReal.mul_top hne]
    exact le_top
  · set K : ℝ := (holderSeminormOn (cubeSetAt y n) (1 / 2) vRep).toReal with hKdef
    have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
    have hKeq : holderSeminormOn (cubeSetAt y n) (1 / 2) vRep = ENNReal.ofReal K := by
      rw [hKdef, ENNReal.ofReal_toReal hlt.ne]
    have hKbd : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) K vRep :=
      (holderSeminormOn_le_ofReal_iff hK0).1 (le_of_eq hKeq)
    rw [hKeq, ← ENNReal.ofReal_mul hApos.le]
    refine (supNormOn_le_ofReal_iff (mul_nonneg hApos.le hK0)).2 fun x hx => ?_
    rw [Real.norm_eq_abs]
    exact abs_le_of_zeroTrace hd w hvae hKbd hx

/-- The same bound with the constant `3^{n/2}` in which the localized estimates
of Section 5 are written. -/
theorem supNormOn_le_rpow_mul_holderSeminormOn_of_zeroTrace (hd : 0 < d) {y : Vec d} {n : ℤ}
    {v : H1Function (cubeSetAt y n)}
    (hw : ∃ w : H10Function (cubeSetAt y n), ∀ x, v.toFun x = w.toH1Function.toFun x)
    {vRep : Vec d → ℝ} (hrep : IsCubeRepresentative y n v vRep) :
    supNormOn (cubeSetAt y n) vRep ≤
      ENNReal.ofReal (Real.rpow 3 ((n : ℝ) / 2)) *
        holderSeminormOn (cubeSetAt y n) (1 / 2) vRep :=
  (supNormOn_le_of_zeroTrace hd hw hrep).trans
    (mul_le_mul' (ENNReal.ofReal_le_ofReal (rpow_half_cube_le_rpow_three_half n)) le_rfl)

end

end Algsuperdiff.Section5.Support
