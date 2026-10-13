/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Dirichlet

/-!
# CubeSchauderData

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Cube Schauder, data layer

Nothing here is an elliptic estimate.  Every declaration is a proved local
helper; no source node is claimed, realized, or closed by this module.

## Main results

* `norm_sub_le_of_mem_openCubeSet_originCube` — the sup-norm diameter of `□_m`
  is `3^m`.
* `holderSeminormBoundOn_lower_exponent` — on a set of diameter `≤ D`,
  a `C^{0,α}` bound implies a `C^{0,β}` bound for `β ≤ α`, at the constant
  `K · D^{α-β}`.  This is the `s ≤ 1/2` leg of the frozen gauge.
* `holderSeminormBoundOn_nonneg_openCubeSet` — on the open cube in dimension
  `d ≥ 1` a Hölder bound forces its constant to be nonnegative.
* `memVectorL2_of_holderSeminormBoundOn` — a `C^{0,α}` vector field on `□_m` is
  in `L²(□_m)`, which is what CoarseGraining's Dirichlet existence theorem
  consumes.

## References

* ABK26, (the asserted Schauder input).
* `Algsuperdiff/Frozen/External/CubeSchauder.lean` (the frozen statement).
-/

namespace Algsuperdiff.Section4.Provider.Schauder

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section4.Support

variable {d : ℕ}

/-! ## 1. Sup-norm geometry of the open origin cube -/

/-- The origin is in every open origin cube. -/
theorem zero_mem_openCubeSet_originCube (m : ℤ) :
    (0 : Vec d) ∈ openCubeSet (originCube d m) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  refine mem_openCubeSet_originCube_iff.2 fun i => ⟨?_, ?_⟩ <;>
    simp only [Pi.zero_apply] <;> linarith only [h3]

/-- **The sup-norm diameter of `□_m` is `3^m`.** -/
theorem norm_sub_le_of_mem_openCubeSet_originCube {m : ℤ} {x y : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hy : y ∈ openCubeSet (originCube d m)) :
    ‖x - y‖ ≤ (3 : ℝ) ^ m := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  refine (pi_norm_le_iff_of_nonneg h3.le).2 fun i => ?_
  have hxi := (mem_openCubeSet_originCube_iff.mp hx) i
  have hyi := (mem_openCubeSet_originCube_iff.mp hy) i
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_le]
  exact ⟨by linarith only [hxi.1, hyi.2], by linarith only [hxi.2, hyi.1]⟩

/-- The constant quarter point lies in `□_m`.  Together with the origin it is
the two-point witness forcing Hölder constants on the cube to be nonnegative. -/
theorem quarterPoint_mem_openCubeSet_originCube (m : ℤ) :
    (fun _ : Fin d => (3 : ℝ) ^ m / 4) ∈ openCubeSet (originCube d m) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  refine mem_openCubeSet_originCube_iff.2 fun _ => ?_
  show (-(1 / 2 : ℝ)) * (3 : ℝ) ^ m < (3 : ℝ) ^ m / 4 ∧
    (3 : ℝ) ^ m / 4 < (1 / 2 : ℝ) * (3 : ℝ) ^ m
  exact ⟨by linarith only [h3], by linarith only [h3]⟩

/-! ## 2. The `rpow` dictionary for the triadic scale factor -/

/-- `(3^m)^t = 3^{t·m}` — the passage between the integer power of the scale
factor and the real power spelled in the frozen gauge. -/
theorem zpow_three_rpow (m : ℤ) (t : ℝ) :
    ((3 : ℝ) ^ m) ^ t = Real.rpow 3 (t * (m : ℝ)) := by
  rw [← Real.rpow_intCast (3 : ℝ) m, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    mul_comm]
  rfl

theorem rpow_three_pos (t : ℝ) : (0 : ℝ) < Real.rpow 3 t :=
  Real.rpow_pos_of_pos (by norm_num) t

/-! ## 3. Elementary algebra of the Hölder carrier -/

section Algebra

variable {E : Type*} [NormedAddCommGroup E]

/-- Hölder bounds add. -/
theorem holderSeminormBoundOn_add {U : Set (Vec d)} {alpha K L : ℝ} {f g : Vec d → E}
    (hf : HolderSeminormBoundOn U alpha K f) (hg : HolderSeminormBoundOn U alpha L g) :
    HolderSeminormBoundOn U alpha (K + L) (fun x => f x + g x) := by
  intro x hx y hy
  have hsplit : (f x + g x) - (f y + g y) = (f x - f y) + (g x - g y) := by abel
  have h1 : ‖(f x + g x) - (f y + g y)‖ ≤ ‖f x - f y‖ + ‖g x - g y‖ := by
    rw [hsplit]; exact norm_add_le _ _
  have h2 := hf x hx y hy
  have h3 := hg x hx y hy
  have h4 : (K + L) * ‖x - y‖ ^ alpha
      = K * ‖x - y‖ ^ alpha + L * ‖x - y‖ ^ alpha := by ring
  rw [h4]
  linarith only [h1, h2, h3]

variable [NormedSpace ℝ E]

/-- Hölder bounds scale by a nonnegative scalar. -/
theorem holderSeminormBoundOn_smul_nonneg {U : Set (Vec d)} {alpha K c : ℝ} {f : Vec d → E}
    (hf : HolderSeminormBoundOn U alpha K f) (hc : 0 ≤ c) :
    HolderSeminormBoundOn U alpha (c * K) (fun x => c • f x) := by
  intro x hx y hy
  have hsub : c • f x - c • f y = c • (f x - f y) := by rw [smul_sub]
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf x hx y hy) hc

end Algebra

/-! ## 4. Lowering the Hölder exponent on a bounded set -/

section Exponent

variable {E : Type*} [NormedAddCommGroup E]

/-- **Exponent lowering.**  On a set of diameter at most `D`, a `C^{0,α}` bound
with nonnegative constant `K` gives a `C^{0,β}` bound at `K · D^{α-β}` whenever
`0 < β ≤ α`.  (`0 < D` is only used through `D^{α-β} ≥ t^{α-β}`.) -/
theorem holderSeminormBoundOn_lower_exponent {U : Set (Vec d)} {alpha beta K D : ℝ}
    {f : Vec d → E} (hf : HolderSeminormBoundOn U alpha K f) (hK : 0 ≤ K)
    (hbeta : 0 < beta) (hle : beta ≤ alpha)
    (hdiam : ∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ D) :
    HolderSeminormBoundOn U beta (K * D ^ (alpha - beta)) f := by
  intro x hx y hy
  have ht0 : (0 : ℝ) ≤ ‖x - y‖ := norm_nonneg _
  have htD : ‖x - y‖ ≤ D := hdiam x hx y hy
  have hdiff : (0 : ℝ) ≤ alpha - beta := by linarith only [hle]
  have hkey : K * ‖x - y‖ ^ alpha ≤ K * D ^ (alpha - beta) * ‖x - y‖ ^ beta := by
    rcases eq_or_lt_of_le ht0 with h | h
    · have halpha : (0 : ℝ) < alpha := lt_of_lt_of_le hbeta hle
      rw [← h, Real.zero_rpow (ne_of_gt halpha), Real.zero_rpow (ne_of_gt hbeta)]
      simp
    · have hsplit : ‖x - y‖ ^ beta * ‖x - y‖ ^ (alpha - beta) = ‖x - y‖ ^ alpha := by
        rw [← Real.rpow_add h]
        congr 1
        ring
      have hmono : ‖x - y‖ ^ (alpha - beta) ≤ D ^ (alpha - beta) :=
        Real.rpow_le_rpow ht0 htD hdiff
      calc K * ‖x - y‖ ^ alpha
          = K * ‖x - y‖ ^ (alpha - beta) * ‖x - y‖ ^ beta := by rw [← hsplit]; ring
        _ ≤ K * D ^ (alpha - beta) * ‖x - y‖ ^ beta :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hmono hK) (Real.rpow_nonneg ht0 beta)
  exact le_trans (hf x hx y hy) hkey

/-- Exponent lowering on the open origin cube, with the scale factor spelled as
in the frozen gauge. -/
theorem holderSeminormBoundOn_lower_exponent_originCube {m : ℤ} {beta K : ℝ}
    {f : Vec d → E}
    (hf : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K f)
    (hK : 0 ≤ K) (hbeta : 0 < beta) (hle : beta ≤ 1 / 2) :
    HolderSeminormBoundOn (openCubeSet (originCube d m)) beta
      (K * Real.rpow 3 ((1 / 2 - beta) * (m : ℝ))) f := by
  have h := holderSeminormBoundOn_lower_exponent hf hK hbeta hle
    (fun x hx y hy => norm_sub_le_of_mem_openCubeSet_originCube hx hy)
  rwa [zpow_three_rpow] at h

end Exponent

/-! ## 5. Continuity, boundedness and `L²` membership -/

section L2

/-- A Hölder-continuous field is continuous on the domain of the bound. -/
theorem continuousOn_of_holderSeminormBoundOn {U : Set (Vec d)} {alpha K : ℝ}
    {f : Vec d → Vec d} (hK : 0 ≤ K) (halpha : 0 < alpha)
    (hf : HolderSeminormBoundOn U alpha K f) : ContinuousOn f U := by
  rw [Metric.continuousOn_iff]
  intro b _hb eps heps
  have hK1 : (0 : ℝ) < K + 1 := by linarith only [hK]
  have hq : (0 : ℝ) < eps / (K + 1) := div_pos heps hK1
  refine ⟨(eps / (K + 1)) ^ alpha⁻¹, Real.rpow_pos_of_pos hq _, fun a ha hab => ?_⟩
  have hdist : dist a b = ‖a - b‖ := dist_eq_norm a b
  have hstep : ‖a - b‖ ^ alpha < ((eps / (K + 1)) ^ alpha⁻¹) ^ alpha := by
    refine Real.rpow_lt_rpow (norm_nonneg _) ?_ halpha
    rwa [hdist] at hab
  have hpow : ((eps / (K + 1)) ^ alpha⁻¹) ^ alpha = eps / (K + 1) := by
    rw [← Real.rpow_mul hq.le, inv_mul_cancel₀ (ne_of_gt halpha), Real.rpow_one]
  have hmul : K * ‖a - b‖ ^ alpha ≤ K * (eps / (K + 1)) := by
    rw [← hpow]
    exact mul_le_mul_of_nonneg_left hstep.le hK
  have hlt : K * (eps / (K + 1)) < eps := by
    have hid : K * (eps / (K + 1)) = (K / (K + 1)) * eps := by field_simp
    have hfrac : K / (K + 1) < 1 := (div_lt_one hK1).2 (by linarith only [])
    rw [hid]
    calc (K / (K + 1)) * eps < 1 * eps := by
          exact mul_lt_mul_of_pos_right hfrac heps
      _ = eps := one_mul eps
  have hbd := hf a ha b _hb
  rw [dist_eq_norm]
  linarith only [hbd, hmul, hlt]

/-- A Hölder-continuous field on `□_m` is bounded there by its value at the
origin plus `K · 3^{αm}`. -/
theorem norm_le_of_holderSeminormBoundOn_originCube {m : ℤ} {alpha K : ℝ}
    {f : Vec d → Vec d} (hK : 0 ≤ K) (halpha : 0 ≤ alpha)
    (hf : HolderSeminormBoundOn (openCubeSet (originCube d m)) alpha K f)
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d m)) :
    ‖f x‖ ≤ ‖f 0‖ + K * ((3 : ℝ) ^ m) ^ alpha := by
  have h0 : (0 : Vec d) ∈ openCubeSet (originCube d m) := zero_mem_openCubeSet_originCube m
  have hbd := hf x hx 0 h0
  have hdiam : ‖x - (0 : Vec d)‖ ≤ (3 : ℝ) ^ m :=
    norm_sub_le_of_mem_openCubeSet_originCube hx h0
  have hmono : ‖x - (0 : Vec d)‖ ^ alpha ≤ ((3 : ℝ) ^ m) ^ alpha :=
    Real.rpow_le_rpow (norm_nonneg _) hdiam halpha
  have hmul : K * ‖x - (0 : Vec d)‖ ^ alpha ≤ K * ((3 : ℝ) ^ m) ^ alpha :=
    mul_le_mul_of_nonneg_left hmono hK
  have htri : ‖f x‖ ≤ ‖f x - f 0‖ + ‖f 0‖ := by
    have := norm_add_le (f x - f 0) (f 0)
    simpa using this
  linarith only [hbd, hmul, htri]

/-- **A Hölder-continuous vector field on `□_m` is square integrable there.** This
is the hypothesis CoarseGraining's Dirichlet existence theorem consumes. -/
theorem memVectorL2_of_holderSeminormBoundOn {m : ℤ} {alpha K : ℝ}
    {f : Vec d → Vec d} (hK : 0 ≤ K) (halpha : 0 < alpha)
    (hf : HolderSeminormBoundOn (openCubeSet (originCube d m)) alpha K f) :
    MemVectorL2 (openCubeSet (originCube d m)) f := by
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d m))) :=
    (isOpenBoundedConvexDomain_openCubeSet (originCube d m)).isFiniteMeasure_restrict_volume
  have hmeas : AEStronglyMeasurable f (volumeMeasureOn (openCubeSet (originCube d m))) :=
    (continuousOn_of_holderSeminormBoundOn hK halpha hf).aestronglyMeasurable
      (measurableSet_openCubeSet (originCube d m))
  refine MemLp.of_bound hmeas (‖f 0‖ + K * ((3 : ℝ) ^ m) ^ alpha) ?_
  refine (ae_restrict_iff' (measurableSet_openCubeSet (originCube d m))).2 ?_
  exact Filter.Eventually.of_forall fun x hx =>
    norm_le_of_holderSeminormBoundOn_originCube hK halpha.le hf hx

end L2

/-! ## 6. Nonnegativity of the constants on the cube -/

/-- On the open origin cube in dimension `d ≥ 1`, a Hölder bound forces its
constant to be nonnegative: the origin and the quarter point on the first axis
are two distinct points of the cube. -/
theorem holderSeminormBoundOn_nonneg_openCubeSet {E : Type*} [NormedAddCommGroup E]
    {m : ℤ} {alpha K : ℝ} {f : Vec d → E} (hd : 0 < d)
    (hf : HolderSeminormBoundOn (openCubeSet (originCube d m)) alpha K f) :
    0 ≤ K := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hi : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨i⟩ := hi
  refine hf.nonneg (quarterPoint_mem_openCubeSet_originCube m)
    (zero_mem_openCubeSet_originCube m) ?_
  intro hcontra
  have hval : (3 : ℝ) ^ m / 4 = 0 := by simpa using congrFun hcontra i
  linarith only [h3, hval]

end Algsuperdiff.Section4.Provider.Schauder
