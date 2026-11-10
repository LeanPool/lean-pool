/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Disks.OmegaExpansion

import LeanPool.HyperellipticCurves.ForMathlib.AdicComplete
import LeanPool.HyperellipticCurves.ForMathlib.PowerSeries

/-!
# The infinity-disk expansion of a differential

For the infinity disk (parametrized by `z = t = x^g/y`) the coordinate `u(z) = 1/x` is the
contraction fixed point of `u = z²·F(u)` with `F = reverse f` (`ChabautyColeman.infSeries`),
built over the `X`-adically complete ring `O⟦z⟧` (`ChabautyColeman.exists_infSeries`); its
reduction has order `2` (`ChabautyColeman.order_map_infSeries`), the double zero of `u = 1/x`
that the infinity-chart order computations rest on. Since the
coordinates `x = 1/u`, `y = 1/(u^g z)` have poles at `z = 0`, the expansion of `ω = h(x) dx/y` is
a Laurent computation; multiplying through by `u` collapses it to the power-series identity
`u(z) · w_D(z) = -z · h*(u(z)) · u'(z)`
(`ChabautyColeman.infSeries_mul_omegaExpansionInf`), where `h*(u) = u^{g-1} h(1/u)` is
`reflect (g-1) h` evaluated at `u`. Explicitly `w_D(z) = -2·h*(u(z))·(1 - z²·F'(u))⁻¹`
(`ChabautyColeman.omegaExpansionInf`), pole-free because `1 - z²·F'(u)` is a unit.

The convergence uses the general algebraic tools `IsPrecomplete.exists_limit` and
`IsHausdorff.eq_zero_of_forall_mem_pow`, stated for an arbitrary `I`-adically complete
ring (they generalize the maximal-ideal versions in `HyperellipticCurves/Series/HenselRoot.lean`).

Blueprint node: `lem:omega-expansion` (infinity chart), `def:disk-antider`.
-/

@[expose] public section

open PowerSeries IsLocalRing Polynomial Submodule

namespace ChabautyColeman

/-! ### The infinity coordinate series -/

variable {O : Type*} [CommRing O]

/-- The `X`-adic contraction step: the Newton iterates `w` of `u = X²·F(u)` (`F = reverse f`,
`w 0 = 0`) have consecutive differences of ever-higher `X`-order, `w(k+1) - w k ∈ (X)^(k+1)`. -/
private theorem step_mem_pow {f : O[X]} (hf : f.Monic) (w : ℕ → O⟦X⟧) (hw0 : w 0 = 0)
    (hws : ∀ n, w (n + 1) = PowerSeries.X ^ 2 * aeval (w n) f.reverse) (k : ℕ) :
    w (k + 1) - w k ∈ (Ideal.span {(PowerSeries.X : O⟦X⟧)}) ^ (k + 1) := by
  set I : Ideal (O⟦X⟧) := Ideal.span {(PowerSeries.X : O⟦X⟧)}
  have hX2 : (PowerSeries.X : O⟦X⟧) ^ 2 ∈ I ^ 2 :=
    Ideal.pow_mem_pow (Ideal.mem_span_singleton.mpr dvd_rfl) 2
  induction k with
  | zero =>
    rw [hws, hw0, sub_zero, aeval_def, eval₂_at_zero, coeff_zero_reverse, hf.leadingCoeff,
      map_one, mul_one]
    exact Ideal.pow_le_pow_right (by lia) hX2
  | succ k ih =>
    rw [hws k, hws (k + 1), ← mul_sub]
    obtain ⟨q, hq⟩ : w (k + 1) - w k ∣ aeval (w (k + 1)) f.reverse - aeval (w k) f.reverse := by
      rw [aeval_def, aeval_def, ← eval_map, ← eval_map]; exact sub_dvd_eval_sub _ _ _
    rw [hq]
    have hm : PowerSeries.X ^ 2 * ((w (k + 1) - w k) * q) ∈ I ^ 2 * I ^ (k + 1) :=
      Ideal.mul_mem_mul hX2 (Ideal.mul_mem_right q _ ih)
    rw [← pow_add] at hm
    exact Ideal.pow_le_pow_right (by lia) hm

/-- Existence of the infinity coordinate series `u(z) ∈ O⟦z⟧` with `u = z²·F(u)`
(`F = reverse f`) and `u ≡ 0 mod z`, as the contraction fixed point (each step multiplies by
`z²`, raising the `z`-order). No completeness of `O` is needed. -/
theorem exists_infSeries {f : O[X]} (hf : f.Monic) :
    ∃ u : O⟦X⟧, u = PowerSeries.X ^ 2 * aeval u f.reverse ∧
      u ∈ Ideal.span {(PowerSeries.X : O⟦X⟧)} := by
  set F := f.reverse
  set I : Ideal (O⟦X⟧) := Ideal.span {(PowerSeries.X : O⟦X⟧)}
  set w : ℕ → O⟦X⟧ := fun n ↦ Nat.rec 0 (fun _ wn ↦ PowerSeries.X ^ 2 * aeval wn F) n
  have hw0 : w 0 = 0 := rfl
  have hws : ∀ n, w (n + 1) = PowerSeries.X ^ 2 * aeval (w n) F := fun _ ↦ rfl
  have hX2 : (PowerSeries.X : O⟦X⟧) ^ 2 ∈ I ^ 2 :=
    Ideal.pow_mem_pow (Ideal.mem_span_singleton.mpr dvd_rfl) 2
  have hdvd : ∀ a b : O⟦X⟧, a - b ∣ aeval a F - aeval b F := fun a b ↦ by
    rw [aeval_def, aeval_def, ← eval_map, ← eval_map]; exact sub_dvd_eval_sub a b _
  obtain ⟨u, hu0, hun⟩ := IsPrecomplete.exists_limit w (step_mem_pow hf w hw0 hws)
  refine ⟨u, ?_, by simpa [hw0] using hu0⟩
  rw [← sub_eq_zero]
  apply IsHausdorff.eq_zero_of_forall_mem_pow (I := I)
  intro n
  have key : u - PowerSeries.X ^ 2 * aeval u F
      = (u - w (n + 1)) + PowerSeries.X ^ 2 * (aeval (w n) F - aeval u F) := by
    rw [hws]; ring
  rw [key]
  refine add_mem (Ideal.pow_le_pow_right (by lia) (hun (n + 1))) ?_
  obtain ⟨q, hq⟩ := hdvd (w n) u
  rw [hq, ← mul_assoc]
  have hwnu : w n - u ∈ I ^ n := (Ideal.neg_mem_iff _).mp (by simpa using hun n)
  have hm : PowerSeries.X ^ 2 * (w n - u) * q ∈ I ^ 2 * I ^ n :=
    Ideal.mul_mem_right q _ (Ideal.mul_mem_mul hX2 hwnu)
  rw [← pow_add] at hm
  exact Ideal.pow_le_pow_right (by lia) hm

/-- The infinity-disk coordinate series `u(z) = 1/x`, root of `u = z²·F(u)` (`F = reverse f`). -/
noncomputable def infSeries {f : O[X]} (hf : f.Monic) : O⟦X⟧ := (exists_infSeries hf).choose

theorem infSeries_eq {f : O[X]} (hf : f.Monic) :
    infSeries hf = PowerSeries.X ^ 2 * aeval (infSeries hf) f.reverse :=
  (exists_infSeries hf).choose_spec.1

@[simp] theorem constantCoeff_infSeries {f : O[X]} (hf : f.Monic) :
    constantCoeff (infSeries hf) = 0 :=
  PowerSeries.X_dvd_iff.mp (Ideal.mem_span_singleton.mp (exists_infSeries hf).choose_spec.2)

/-- The denominator series `D = 1 - z²·F'(u)` is a unit (constant coefficient `1`). -/
theorem isUnit_infDenom {f : O[X]} (hf : f.Monic) :
    IsUnit (1 - PowerSeries.X ^ 2 * aeval (infSeries hf) f.reverse.derivative) := by
  rw [isUnit_iff_constantCoeff, map_sub, map_one, map_mul, map_pow, PowerSeries.constantCoeff_X,
    zero_pow (by norm_num), zero_mul, sub_zero]
  exact isUnit_one

/-- Chain rule: differentiating `u = z²·F(u)` gives `u'·(1 - z²·F'(u)) = 2z·F(u)`. -/
theorem derivative_infSeries_mul {f : O[X]} (hf : f.Monic) :
    PowerSeries.derivative (infSeries hf)
        * (1 - PowerSeries.X ^ 2 * aeval (infSeries hf) f.reverse.derivative)
      = 2 * PowerSeries.X * aeval (infSeries hf) f.reverse := by
  set u := infSeries hf with hu
  have hd : PowerSeries.derivative u
      = 2 * PowerSeries.X * aeval u f.reverse
        + PowerSeries.X ^ 2 * (aeval u f.reverse.derivative * PowerSeries.derivative u) := by
    conv_lhs => rw [hu, infSeries_eq hf, ← hu]
    rw [Derivation.leibniz, Derivation.comp_aeval_eq, PowerSeries.derivative_pow,
      PowerSeries.derivative_X,
      smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  linear_combination hd

section

variable [IsLocalRing O]

/-- The reduced infinity coordinate series `u(z)` has order `2`: `u = z²·F(u)` with `F(0) = 1`
(leading coefficient of the monic `f`). -/
theorem order_map_infSeries {f : O[X]} (hf : f.Monic) :
    ((infSeries hf).map (residue O)).order = 2 := by
  set ρ := residue O
  have heq : (infSeries hf).map ρ
      = PowerSeries.X ^ 2 * aeval ((infSeries hf).map ρ) (f.reverse.map ρ) := by
    nth_rw 1 [infSeries_eq hf]
    rw [map_mul, map_pow, PowerSeries.map_X, PowerSeries.map_aeval]
  have hcc : constantCoeff (aeval ((infSeries hf).map ρ) (f.reverse.map ρ)) = 1 := by
    rw [PowerSeries.constantCoeff_aeval, PowerSeries.constantCoeff_map, constantCoeff_infSeries,
      map_zero,
      eval_map, eval₂_at_zero, coeff_zero_reverse, hf.leadingCoeff, map_one]
  rw [heq, order_mul, order_pow, order_X,
    PowerSeries.order_eq_zero_of_constantCoeff_ne_zero (by rw [hcc]; exact one_ne_zero), add_zero]
  rfl

end

/-! ### The infinity-disk expansion -/

/-- The expansion of `ω = h(x) dx/y` on the infinity disk: the Laurent computation collapses to
`w_D(z) = -2·h*(u(z))·(1 - z²·F'(u))⁻¹`, where `h*(u) = u^{g-1} h(1/u)` (`= reflect (g-1) h`
evaluated at `u`). Pole-free; the order at lowest degree is `2(g-1) - 2·deg h`. -/
noncomputable def omegaExpansionInf (h : O[X]) {f : O[X]} (hf : f.Monic) : O⟦X⟧ :=
  -2 * aeval (infSeries hf) (reflect (genus f - 1) h)
    * Ring.inverse (1 - PowerSeries.X ^ 2 * aeval (infSeries hf) f.reverse.derivative)

/-- Differential form: `u(z) · w_D(z) = -z · h*(u(z)) · u'(z)`, i.e. `w_D dz = h(x) dx/y` cleared
of the pole at `z = 0` by multiplying with `u`. -/
theorem infSeries_mul_omegaExpansionInf (h : O[X]) {f : O[X]} (hf : f.Monic) :
    infSeries hf * omegaExpansionInf h hf
      = -PowerSeries.X * aeval (infSeries hf) (reflect (genus f - 1) h)
          * PowerSeries.derivative (infSeries hf) := by
  rw [omegaExpansionInf]
  set u := infSeries hf
  set D := 1 - PowerSeries.X ^ 2 * aeval u f.reverse.derivative
  set hs := aeval u (reflect (genus f - 1) h)
  set aF := aeval u f.reverse
  set du := PowerSeries.derivative u
  have hDinv : D * Ring.inverse D = 1 := Ring.mul_inverse_cancel D (isUnit_infDenom hf)
  have hchain : du * D = 2 * PowerSeries.X * aF := derivative_infSeries_mul hf
  have hueq : u = PowerSeries.X ^ 2 * aF := infSeries_eq hf
  have hcancel : D * (u * (-2 * hs * Ring.inverse D)) = D * (-PowerSeries.X * hs * du) := by
    linear_combination (-2 * hs * u) * hDinv + (PowerSeries.X * hs) * hchain + (-2 * hs) * hueq
  exact (isUnit_infDenom hf).mul_right_injective hcancel

/-! ### The infinity-disk antiderivative -/

variable {K : Type*} [Field K] [Algebra O K]

/-- The antiderivative `G^ω_D` of the infinity-disk expansion of `ω = h(x) dx/y`, over the
fraction field, with `G(0) = 0`. -/
noncomputable def diskAntiderivInf (h : O[X]) {f : O[X]} (hf : f.Monic) : K⟦X⟧ :=
  antideriv ((omegaExpansionInf h hf).map (algebraMap O K))

@[simp] theorem constantCoeff_diskAntiderivInf (h : O[X]) {f : O[X]} (hf : f.Monic) :
    constantCoeff (diskAntiderivInf (K := K) h hf) = 0 :=
  constantCoeff_antideriv _

end ChabautyColeman
