/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.HolderGauge

/-!
# HolderCalculus

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Calculus of the supremum norm and the Hölder seminorm

This file retains two explicit two-point estimates: interpolation of a Hölder
bound between a supremum bound and a Lipschitz bound,

  ```text
    [F]_{C^{0,1/2}(U)} ≤ ( 2 ‖F‖_{L^∞(U)} · L )^{1/2} ,
  ```

and the Leibniz estimate for a scalar multiple in explicit
`HolderSeminormBoundOn` form.

## References

* ABK26, the localized estimates of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport
open Algsuperdiff.Section4.Support
open scoped ENNReal NNReal

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E]

/-! ## 2. Interpolation between the supremum norm and a Lipschitz bound -/

/-- **Interpolation of the `1/2`-Hölder seminorm.**  A field bounded by `S` on
`U` and Lipschitz there with constant `L` has `1/2`-Hölder seminorm at most
`(2 S L)^{1/2}`: the two bounds `‖F x - F z‖ ≤ 2S` and `‖F x - F z‖ ≤ L‖x - z‖`
multiply, and the square root of their product is the stated bound.

No sign hypothesis is needed: at two distinct points of `U` the two hypotheses
force `0 ≤ S` and `0 ≤ L`, and at a single point both sides vanish. -/
theorem holderSeminormBoundOn_half_of_supNorm_of_lipschitz {U : Set (Vec d)} {S L : ℝ}
    {F : Vec d → E} (hS : ∀ x ∈ U, ‖F x‖ ≤ S) (hL : HolderSeminormBoundOn U 1 L F) :
    HolderSeminormBoundOn U (1 / 2) (Real.sqrt (2 * S * L)) F := by
  intro x hx z hz
  rcases eq_or_ne x z with rfl | hne
  · simp
  · have ht : (0 : ℝ) < ‖x - z‖ := by
      rw [norm_pos_iff]
      exact sub_ne_zero.2 hne
    have hS0 : 0 ≤ S := le_trans (norm_nonneg _) (hS x hx)
    have hLt : ‖F x - F z‖ ≤ L * ‖x - z‖ := by
      have h := hL x hx z hz
      rwa [Real.rpow_one] at h
    have hL0 : 0 ≤ L := by
      by_contra hcon
      push Not at hcon
      have hneg : L * ‖x - z‖ < 0 := mul_neg_of_neg_of_pos hcon ht
      linarith only [hneg, hLt, norm_nonneg (F x - F z)]
    have h2S : ‖F x - F z‖ ≤ 2 * S := by
      refine le_trans (norm_sub_le _ _) ?_
      linarith only [hS x hx, hS z hz]
    have hsq : ‖F x - F z‖ ^ 2 ≤ (2 * S * L) * ‖x - z‖ := by
      have h := mul_le_mul h2S hLt (norm_nonneg _) (by linarith only [hS0])
      calc ‖F x - F z‖ ^ 2 = ‖F x - F z‖ * ‖F x - F z‖ := sq _
        _ ≤ (2 * S) * (L * ‖x - z‖) := h
        _ = (2 * S * L) * ‖x - z‖ := by ring
    calc ‖F x - F z‖ = Real.sqrt (‖F x - F z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((2 * S * L) * ‖x - z‖) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (2 * S * L) * Real.sqrt ‖x - z‖ :=
          Real.sqrt_mul (by positivity) _
      _ = Real.sqrt (2 * S * L) * ‖x - z‖ ^ (1 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow ‖x - z‖]

/-! ## 3. The Leibniz rule -/

variable [NormedSpace ℝ E]

/-- **The Leibniz rule in explicit two-point form.**  With a Hölder constant and
a supremum bound for each factor, the product obeys the Hölder bound with
constant `Kf · SG + Sf · KG`. -/
theorem holderSeminormBoundOn_smul {U : Set (Vec d)} {alpha Kf Sf KG SG : ℝ}
    {f : Vec d → ℝ} {G : Vec d → E} (hKf0 : 0 ≤ Kf) (hSf0 : 0 ≤ Sf)
    (hKf : HolderSeminormBoundOn U alpha Kf f) (hSf : ∀ x ∈ U, ‖f x‖ ≤ Sf)
    (hKG : HolderSeminormBoundOn U alpha KG G) (hSG : ∀ x ∈ U, ‖G x‖ ≤ SG) :
    HolderSeminormBoundOn U alpha (Kf * SG + Sf * KG) (fun x => f x • G x) := by
  intro x hx z hz
  have hpow : (0 : ℝ) ≤ ‖x - z‖ ^ alpha := Real.rpow_nonneg (norm_nonneg _) alpha
  have hsplit : f x • G x - f z • G z = (f x - f z) • G z + f x • (G x - G z) := by
    rw [sub_smul, smul_sub]
    abel
  have h1 : ‖f x - f z‖ * ‖G z‖ ≤ (Kf * ‖x - z‖ ^ alpha) * SG :=
    mul_le_mul (hKf x hx z hz) (hSG z hz) (norm_nonneg _) (by positivity)
  have h2 : ‖f x‖ * ‖G x - G z‖ ≤ Sf * (KG * ‖x - z‖ ^ alpha) :=
    mul_le_mul (hSf x hx) (hKG x hx z hz) (norm_nonneg _) hSf0
  calc ‖f x • G x - f z • G z‖
      ≤ ‖f x - f z‖ * ‖G z‖ + ‖f x‖ * ‖G x - G z‖ := by
        rw [hsplit]
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_smul, norm_smul]
    _ ≤ (Kf * ‖x - z‖ ^ alpha) * SG + Sf * (KG * ‖x - z‖ ^ alpha) := add_le_add h1 h2
    _ = (Kf * SG + Sf * KG) * ‖x - z‖ ^ alpha := by ring

end Algsuperdiff.Section5.Support
