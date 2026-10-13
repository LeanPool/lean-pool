/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepCompetitor
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepTriangle

/-!
# OneStepAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The triangle assembly: the deterministic one-step contraction

This module proves the **third display** of the proof of
`l.excess.decay.good.scales`,

```text
  E(u,U_k) ≤ C 3^{-k/2} E(u,U_0) + C 3^{(d/2+1)k} 3^{-n} ‖u-v‖_{L²(U_2)}
              + C 3^{(n-k)/2} [∇h]_{C^{0,1/2}(U_0)} 1_{bd} ,
```

as one pathwise, real-valued, coefficient-free theorem
(`excessDecay_oneStep_triangle_of_schauder`) on the truncated window family
`U_j = (x+□_{n-j}) ∩ □_m`.

## The single remaining input: the Schauder obligation

The theorem takes the Schauder conclusion as an explicit,
disclosingly named hypothesis:

```text
  hschauder :  K  ≤  Csch · (3^{-n})^{1/2} · E(v, U_2)  +  Kh
```

where `K` is the `C^{0,1/2}` seminorm bound of `∇v` on `U_3` and `Kh` is the
boundary-datum leg `C [∇h]_{C^{0,1/2}(U_2)} 1_{bd}`.  Nothing else in this
module is assumed: the harmonicity of `v` is *not* used, and every other leg is
proved.

## The three legs, and where each constant comes from

* `taylorContractionConst d · Csch · windowRatioConst d 2 · (3^{-k})^{1/2}` on
  `E(u,U_0)` — the printed^{-k/2}`.  `taylorContractionConst` is the
  affine-competitor constant of `OneStepCompetitor`, `windowRatioConst d 2` the
  excess quasi-monotonicity `E(u,U_2) ≤ κ E(u,U_0)` of `OneStepWindows`.
* `triangleRemainderConst d Csch k · 3^{-n}` on `‖u-v‖_{L²(U_2)}`, with
  `triangleRemainderConst d Csch k = 81 · taylorContractionConst d · Csch
  + 9 · 3^k · √((3^k)^d)`.  Since `√((3^k)^d) = 3^{kd/2}`, this is the
    printed^{(1+d/2)k}` exactly (the `81` and `9` are the aspect-`1/9` slacks
    of the two truncated normalizers, which the printed proof does not
    display).
* `taylorContractionConst d · (3^{n-k})^{1/2}` on `Kh` — the printed `C 3^{(n-k)/2}
  [∇h]_{C^{0,1/2}}`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. Two small `3`-power identities -/

private theorem three_zpow_rpow_half_mul (a b : ℤ) :
    ((3 : ℝ) ^ a) ^ (1 / 2 : ℝ) * ((3 : ℝ) ^ b) ^ (1 / 2 : ℝ)
      = ((3 : ℝ) ^ (a + b)) ^ (1 / 2 : ℝ) := by
  rw [← Real.mul_rpow (zpow_pos (by norm_num) a).le (zpow_pos (by norm_num) b).le,
    ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]

private theorem three_zpow_rpow_half_le_one {k : ℕ} :
    ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) ≤ 1 := by
  refine Real.rpow_le_one (zpow_pos (by norm_num) _).le ?_ (by norm_num)
  calc (3 : ℝ) ^ (-(k : ℤ)) ≤ (3 : ℝ) ^ (0 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ = 1 := zpow_zero 3

/-! ## 2. Restriction of the gradient carrier

`HasGradientOn.mono_set` now lives with its carrier in
`Algsuperdiff/Section4/Support/ClassicalGradient.lean`; the duplicate copy that
used to sit here was deleted with the `AffineSplitLift` re-point. -/

/-! ## 3. The assembled constant -/

/-- The remainder constant of the assembly: `81 C_taylor Csch + 9·3^k·√((3^k)^d)`,
i.e. the printed `C 3^{(1+d/2)k}`. -/
def triangleRemainderConst (d : ℕ) (Csch : ℝ) (k : ℕ) : ℝ :=
  81 * taylorContractionConst d * Csch
    + 9 * (3 : ℝ) ^ (k : ℤ) * Real.sqrt (((3 : ℝ) ^ (k : ℤ)) ^ d)

theorem triangleRemainderConst_nonneg (d : ℕ) {Csch : ℝ} (hCsch : 0 ≤ Csch) (k : ℕ) :
    0 ≤ triangleRemainderConst d Csch k := by
  have h1 : 0 ≤ 81 * taylorContractionConst d * Csch :=
    mul_nonneg (mul_nonneg (by norm_num) (taylorContractionConst_nonneg d)) hCsch
  have h2 : 0 ≤ 9 * (3 : ℝ) ^ (k : ℤ) * Real.sqrt (((3 : ℝ) ^ (k : ℤ)) ^ d) := by positivity
  rw [triangleRemainderConst]
  linarith only [h1, h2]

/-! ## 4. The assembly -/

/-- **The triangle assembly, deterministic form.**

Given the affine competitor's `C^{1,1/2}` data on `U_3`, the Schauder
bound `hschauder` on its gradient-Hölder constant, and *nothing else*, the excess
of `u` on `U_k` contracts:

```text
  E(u,U_k) ≤ C_t Csch κ (3^{-k})^{1/2} E(u,U_0)
              + (81 C_t Csch + 9·3^k √((3^k)^d)) · 3^{-n} ‖u-v‖_{L²(U_2)}
              + C_t (3^{n-k})^{1/2} Kh .
```
-/
theorem excessDecay_oneStep_triangle_of_schauder (hd : d ≠ 0) {m n : ℤ} {k : ℕ}
    (hk : 3 ≤ k) {x : Vec d} (hx : x ∈ openCubeSet (originCube d m)) (hnm : n - 1 ≤ m)
    {u v : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedWindow x m n)))
    (hv : MemLp v 2 (volume.restrict (truncatedWindow x m n)))
    {Gv : Vec d → Vec d} {K Kh Csch : ℝ} (hK : 0 ≤ K) (hCsch : 0 ≤ Csch)
    (hint : ∀ i, IntegrableOn (fun p => Gv p i) (truncatedWindow x m (n - 3)) volume)
    (hgrad : HasGradientOn (truncatedWindow x m (n - 3)) v Gv)
    (hhol : HolderSeminormBoundOn (truncatedWindow x m (n - 3)) (1 / 2 : ℝ) K Gv)
    (hschauder : K ≤ Csch * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
        * affineExcess (truncatedWindow x m (n - 2)) v + Kh) :
    affineExcess (truncatedWindow x m (n - (k : ℤ))) u
      ≤ taylorContractionConst d * Csch * windowRatioConst d 2
            * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
            * affineExcess (truncatedWindow x m n) u
        + triangleRemainderConst d Csch k
            * ((3 : ℝ) ^ (-n)
              * normalizedL2On (truncatedWindow x m (n - 2)) (fun y => u y - v y))
        + taylorContractionConst d * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ) * Kh := by
  have hne : (3 : ℝ) ≠ 0 := by norm_num
  have hCt : 0 ≤ taylorContractionConst d := taylorContractionConst_nonneg d
  have hkappa : 0 ≤ windowRatioConst d 2 := windowRatioConst_nonneg d 2
  -- window nondegeneracy at the four scales in play
  have hmk : n - (k : ℤ) - 1 ≤ m := by omega
  have hm3 : n - 3 - 1 ≤ m := by omega
  have hm2 : n - 2 - 1 ≤ m := by omega
  have hm0 : n - 1 ≤ m := hnm
  -- window inclusions and the restricted `MemLp` slots
  have hsub_k3 : truncatedWindow x m (n - (k : ℤ)) ⊆ truncatedWindow x m (n - 3) :=
    truncatedWindow_mono x m (by omega)
  have hsub_32 : truncatedWindow x m (n - 3) ⊆ truncatedWindow x m (n - 2) :=
    truncatedWindow_mono x m (by omega)
  have hsub_20 : truncatedWindow x m (n - 2) ⊆ truncatedWindow x m n :=
    truncatedWindow_mono x m (by omega)
  have huk : MemLp u 2 (volume.restrict (truncatedWindow x m (n - (k : ℤ)))) :=
    memLp_restrict_of_subset (hsub_k3.trans (hsub_32.trans hsub_20)) hu
  have hvk : MemLp v 2 (volume.restrict (truncatedWindow x m (n - (k : ℤ)))) :=
    memLp_restrict_of_subset (hsub_k3.trans (hsub_32.trans hsub_20)) hv
  have hu2 : MemLp u 2 (volume.restrict (truncatedWindow x m (n - 2))) :=
    memLp_restrict_of_subset hsub_20 hu
  have hv2 : MemLp v 2 (volume.restrict (truncatedWindow x m (n - 2))) :=
    memLp_restrict_of_subset hsub_20 hv
  -- (1) the triangle step on `U_k`
  have h1 := affineExcess_sub_le_truncatedWindow hd hx hmk huk hvk
  -- (2) the affine (Taylor) competitor on `U_k`
  have h2 := affineExcess_le_taylor hd hx hmk hK hvk
    (fun i => (hint i).mono_set hsub_k3) (hgrad.mono_set hsub_k3) (hhol.mono_set hsub_k3)
  -- (4) the triangle step on `U_2`, with `u` and `v` interchanged
  have h4 := affineExcess_sub_le_truncatedWindow hd hx hm2 hv2 hu2
  rw [normalizedL2On_sub_comm] at h4
  -- (5) quasi-monotonicity `E(u,U_2) ≤ κ E(u,U_0)`
  have h5 : affineExcess (truncatedWindow x m (n - 2)) u
      ≤ windowRatioConst d 2 * affineExcess (truncatedWindow x m n) u := by
    have h := affineExcess_truncatedWindow_le (l := n) x hx hm2 hm0 (by omega) hu
    rwa [show n - (n - 2) = (2 : ℤ) by ring] at h
  -- (6) the `L²` window transfer
  have h6 : normalizedL2On (truncatedWindow x m (n - (k : ℤ))) (fun y => u y - v y)
      ≤ Real.sqrt (((3 : ℝ) ^ (k : ℤ)) ^ d)
        * normalizedL2On (truncatedWindow x m (n - 2)) (fun y => u y - v y) := by
    have h := normalizedL2On_truncatedWindow_le (l := n - 2) (k := n - (k : ℤ)) hx hmk hm2
      (by omega) (f := fun y => u y - v y) (hu2.sub hv2)
    rwa [show n - 2 - (n - (k : ℤ)) + 2 = (k : ℤ) by ring] at h
  -- the two `3`-power rewrites
  have hpow_k : (3 : ℝ) ^ (-(n - (k : ℤ))) = (3 : ℝ) ^ (k : ℤ) * (3 : ℝ) ^ (-n) := by
    rw [show -(n - (k : ℤ)) = (k : ℤ) + -n by ring, zpow_add₀ hne]
  have hpow_2 : (3 : ℝ) ^ (-(n - 2)) = 9 * (3 : ℝ) ^ (-n) := by
    rw [show -(n - 2) = (2 : ℤ) + -n by ring, zpow_add₀ hne]
    norm_num
  have hQ : ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ)
      = ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) := by
    rw [three_zpow_rpow_half_mul, show -n + (n - (k : ℤ)) = -(k : ℤ) by ring]
  rw [hpow_k] at h1
  rw [hpow_2] at h4
  -- assemble
  set S2 := normalizedL2On (truncatedWindow x m (n - 2)) (fun y => u y - v y) with hS2
  set E0 := affineExcess (truncatedWindow x m n) u with hE0
  set R := Real.sqrt (((3 : ℝ) ^ (k : ℤ)) ^ d) with hR
  set T := ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ) with hT
  set Q := ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) with hQdef
  have hS2nn : 0 ≤ S2 := normalizedL2On_nonneg _ _
  have hTnn : (0 : ℝ) ≤ T := Real.rpow_nonneg (zpow_pos (by norm_num) _).le _
  have h3npos : (0 : ℝ) < (3 : ℝ) ^ (-n) := zpow_pos (by norm_num) _
  -- the `K`-leg, expanded through `hschauder`
  have hKT : taylorContractionConst d * K * T
      ≤ taylorContractionConst d * Csch * Q
          * affineExcess (truncatedWindow x m (n - 2)) v
        + taylorContractionConst d * T * Kh := by
    have hstep : taylorContractionConst d * T * K
        ≤ taylorContractionConst d * T
          * (Csch * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
            * affineExcess (truncatedWindow x m (n - 2)) v + Kh) :=
      mul_le_mul_of_nonneg_left hschauder (mul_nonneg hCt hTnn)
    have hexp : taylorContractionConst d * T
        * (Csch * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
          * affineExcess (truncatedWindow x m (n - 2)) v + Kh)
        = taylorContractionConst d * Csch
            * (((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) * T)
            * affineExcess (truncatedWindow x m (n - 2)) v
          + taylorContractionConst d * T * Kh := by ring
    rw [hexp, hQ] at hstep
    linarith only [hstep]
  -- the competitor excess on `U_2`, folded into and `S2`
  have hEv2 : affineExcess (truncatedWindow x m (n - 2)) v
      ≤ windowRatioConst d 2 * E0 + 81 * ((3 : ℝ) ^ (-n) * S2) := by
    linarith only [h4, h5]
  have hcoef : (0 : ℝ) ≤ taylorContractionConst d * Csch * Q :=
    mul_nonneg (mul_nonneg hCt hCsch) (Real.rpow_nonneg (zpow_pos (by norm_num) _).le _)
  have hfold : taylorContractionConst d * Csch * Q
        * affineExcess (truncatedWindow x m (n - 2)) v
      ≤ taylorContractionConst d * Csch * windowRatioConst d 2 * Q * E0
        + 81 * taylorContractionConst d * Csch * Q * ((3 : ℝ) ^ (-n) * S2) := by
    have h := mul_le_mul_of_nonneg_left hEv2 hcoef
    linarith only [h]
  -- discard the `Q ≤ 1` factor on the remainder leg
  have hQnn : (0 : ℝ) ≤ 81 * taylorContractionConst d * Csch * ((3 : ℝ) ^ (-n) * S2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCt) hCsch)
      (mul_nonneg h3npos.le hS2nn)
  have hdrop : 81 * taylorContractionConst d * Csch * Q * ((3 : ℝ) ^ (-n) * S2)
      ≤ 81 * taylorContractionConst d * Csch * ((3 : ℝ) ^ (-n) * S2) := by
    calc 81 * taylorContractionConst d * Csch * Q * ((3 : ℝ) ^ (-n) * S2)
        = (81 * taylorContractionConst d * Csch * ((3 : ℝ) ^ (-n) * S2)) * Q := by ring
      _ ≤ (81 * taylorContractionConst d * Csch * ((3 : ℝ) ^ (-n) * S2)) * 1 :=
          mul_le_mul_of_nonneg_left three_zpow_rpow_half_le_one hQnn
      _ = 81 * taylorContractionConst d * Csch * ((3 : ℝ) ^ (-n) * S2) := by ring
  -- the raw `‖u-v‖` leg on `U_k`
  have hraw : 9 * ((3 : ℝ) ^ (k : ℤ) * (3 : ℝ) ^ (-n))
        * normalizedL2On (truncatedWindow x m (n - (k : ℤ))) (fun y => u y - v y)
      ≤ 9 * (3 : ℝ) ^ (k : ℤ) * R * ((3 : ℝ) ^ (-n) * S2) := by
    have hc : (0 : ℝ) ≤ 9 * ((3 : ℝ) ^ (k : ℤ) * (3 : ℝ) ^ (-n)) := by positivity
    have h := mul_le_mul_of_nonneg_left h6 hc
    linarith only [h]
  rw [triangleRemainderConst]
  linarith only [h1, h2, hKT, hfold, hdrop, hraw]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
