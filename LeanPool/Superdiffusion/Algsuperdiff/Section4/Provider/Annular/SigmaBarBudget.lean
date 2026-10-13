/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.IncrementOscillation
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.ShellGaugeBudget

/-!
# SigmaBarBudget

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `σ` slots of Step 2, at the honest `𝒢₁` amplitude

ABK26, Section 4.1, `p.mathcalE.annular.decomp` Step 2.
`UglyLatticeChain.exists_uglyJEstimate_lattice_cube` carries five `σ`-shaped
inputs:

* `hkap0`, `hkap` — the normalization `γ κ² = c⋆`;
* `hsigmlow` — `½ κ 3^{γm} ≤ σ_m`;
* `hsignlow` — `¼ κ 3^{γn} ≤ σ_{n−2}`  (the relaxed constant);
* `hratio`  — `σ_m^{−1} σ_{n−2} ≤ C_r`;

together with the gauge input `hshell`.  This module discharges **all** of them
from the Section 3 induction state and from `ShellGaugeBudget`, at the honest
clause-(i) amplitude

```
T' = √c⋆ γ^{−1/2}    (so  T' = κ  exactly).
```

## The `hsignlow` constant, stated honestly

The frozen `Frozen.Section3.inductionState` gives
`σ_k² ≥ ¼ max(c⋆ γ^{−1} 3^{2γk}, ν²)`, hence at `k = n − 2`

```
σ_{n−2} ≥ ½ κ 3^{γ(n−2)} = 3^{−2γ} · ( ½ κ 3^{γn} ) ,
```

which is short of the printed `½ κ 3^{γn}` by exactly the factor `3^{2γ}` (`≤
3^{1/16} ≈ 1.072` on the printed window `8γ ≤ s ≤ 1/4`).  The ugly chain's
`hsignlow` binder was relaxed to `¼` for exactly this reason, and
`SignLowDischarge` discharges it outright from
`sigmaBar_lower_of_inductionState` below.
`inv_sigmaBar_sub_two_le_of_inductionState` is the inverse form of the same
fact, and it is what the `hshell` producer here consumes.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Section3
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Provider.BadEvents

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the amplitude is the chain's `κ` -/

private theorem three_rpow_mono₂ {x y : ℝ} (h : x ≤ y) : (3 : ℝ) ^ x ≤ (3 : ℝ) ^ y :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h

/-- `3^{1/2} ≤ 2`, the only numeric fact the `3^{2γ}` index shift costs. -/
private theorem three_rpow_half_le_two : (3 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 := by
  refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by norm_num) ?_
  have hsq : ((3 : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = 3 := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ ((1 : ℝ) / 2)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [hsq]
  norm_num

/-- The honest clause-(i) `𝒢₁` amplitude `T' = √c⋆ γ^{−1/2}` is positive. -/
theorem annularEventAmplitude_pos (M : ABKModel d) :
    (0 : ℝ) < Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹ := by
  have hc : (0 : ℝ) < Real.sqrt (Disorder.cstar M) :=
    Real.sqrt_pos.2 (Disorder.cstar_characterization M).1
  have hg : (0 : ℝ) < Real.sqrt M.gamma := Real.sqrt_pos.2 M.shellPrefix.gamma_pos
  exact mul_pos hc (inv_pos.2 hg)

/-- **The chain's `hkap` slot at the honest amplitude**: `γ T'² = c⋆`.  The `𝒢₁`
threshold of the printed clause-(i) event *is* the `κ` of
`e.ugly.estimate.for.J`; no rescaling intervenes. -/
theorem gamma_mul_annularEventAmplitude_sq (M : ABKModel d) :
    M.gamma * (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) ^ 2
      = Disorder.cstar M := by
  have hg : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hgne : M.gamma ≠ 0 := ne_of_gt hg
  rw [annularEventAmplitude_sq M]
  field_simp

/-! ## Part B -- the `σ` readings of the induction state -/

/-- **The `hsigmlow` slot.**  The lower branch of `e.shom.h.bounds`, at the
honest amplitude, at any scale below the landmark. -/
theorem sigmaBar_lower_of_inductionState (M : ABKModel d) {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}} (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E)
    {k : ℤ} (hk : k ≤ m0) :
    1 / 2 * ((Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹)
        * (3 : ℝ) ^ (M.gamma * (k : ℝ)))
      ≤ (Annealed.sigmaBar M k : ℝ) := by
  have h := sqrt_cstar_mul_inv_sqrt_gamma_mul_rpow_le_two_mul_sigmaBar M hS hk
  linarith only [h]

/-- **What the state gives at the shifted index `n − 2`.**  The inverse form of
`sigmaBar_lower_of_inductionState` at `k = n − 2`, with the exponent moved from
`3^{γ(n−2)}` to `3^{γn}` at the honest cost `3^{2γ} ≤ 2`.

This is the inverse form of the chain's (relaxed) `hsignlow` binder: the
printed statement would give the constant `2` where this gives `4`. -/
theorem inv_sigmaBar_sub_two_le_of_inductionState (M : ABKModel d) {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}} (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E)
    {n : ℤ} (hn : n - 2 ≤ m0) :
    ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹
      ≤ 4 * ((Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹)⁻¹
          * (3 : ℝ) ^ (-(M.gamma * (n : ℝ)))) := by
  have hkap0 := annularEventAmplitude_pos M
  have hg14 : M.gamma ≤ 1 / 4 := M.shellPrefix.gamma_le_quarter
  have hP0 : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (((n - 2 : ℤ)) : ℝ)) := by positivity
  have hlow := sigmaBar_lower_of_inductionState M hS hn
  have hstep := inv_le_two_mul_inv hkap0 hP0 hlow
  refine hstep.trans ?_
  have hinvP : ((3 : ℝ) ^ (M.gamma * (((n - 2 : ℤ)) : ℝ)))⁻¹
      = (3 : ℝ) ^ (2 * M.gamma) * (3 : ℝ) ^ (-(M.gamma * (n : ℝ))) := by
    rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  have h2g : (3 : ℝ) ^ (2 * M.gamma) ≤ 2 :=
    le_trans (three_rpow_mono₂ (by linarith only [hg14])) three_rpow_half_le_two
  have hE0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(M.gamma * (n : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hkinv0 : (0 : ℝ) ≤ (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹)⁻¹ :=
    (inv_pos.2 hkap0).le
  rw [hinvP]
  have hstep1 := mul_le_mul_of_nonneg_right h2g hE0
  have hstep2 := mul_le_mul_of_nonneg_left hstep1 hkinv0
  linarith only [hstep2]

/-- **The `hratio` slot at the constant `4`.**  Both branches of
`e.shom.h.bounds` at the two indices, with the `max` monotone in the scale. -/
theorem sigmaBar_ratio_le_four (M : ABKModel d) {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}} (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E)
    {m n : ℤ} (hnm : n - 2 ≤ m) (hm : m ≤ m0) :
    ((Annealed.sigmaBar M m : ℝ))⁻¹ * (Annealed.sigmaBar M (n - 2) : ℝ) ≤ 4 := by
  have hg0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hsm : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hlow := (hS.1 m hm).1
  have hup := (hS.1 (n - 2) (le_trans hnm hm)).2
  have hexp : (3 : ℝ) ^ (2 * M.gamma * (((n - 2 : ℤ)) : ℝ))
      ≤ (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
    refine three_rpow_mono₂ ?_
    have hc : ((n - 2 : ℤ) : ℝ) ≤ ((m : ℤ) : ℝ) := by exact_mod_cast hnm
    exact mul_le_mul_of_nonneg_left hc (by linarith only [hg0])
  have hcs0 : (0 : ℝ) ≤ Disorder.cstar M * M.gamma⁻¹ :=
    mul_nonneg (Disorder.cstar_characterization M).1.le (inv_nonneg.2 hg0.le)
  have hmax : max (Disorder.cstar M * M.gamma⁻¹ *
        (3 : ℝ) ^ (2 * M.gamma * (((n - 2 : ℤ)) : ℝ))) (M.nu ^ 2)
      ≤ max (Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))
          (M.nu ^ 2) :=
    max_le_max (mul_le_mul_of_nonneg_left hexp hcs0) le_rfl
  have hsq : (Annealed.sigmaBar M (n - 2) : ℝ) ^ 2
      ≤ (4 * (Annealed.sigmaBar M m : ℝ)) ^ 2 := by
    have hexpand : (4 * (Annealed.sigmaBar M m : ℝ)) ^ 2
        = 16 * (Annealed.sigmaBar M m : ℝ) ^ 2 := by ring
    rw [hexpand]
    linarith only [hup, hlow, hmax]
  have hle : (Annealed.sigmaBar M (n - 2) : ℝ) ≤ 4 * (Annealed.sigmaBar M m : ℝ) :=
    le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by linarith only [hsm]) hsq
  have hinv0 : (0 : ℝ) ≤ ((Annealed.sigmaBar M m : ℝ))⁻¹ := (inv_pos.2 hsm).le
  have hmne : (Annealed.sigmaBar M m : ℝ) ≠ 0 := ne_of_gt hsm
  calc ((Annealed.sigmaBar M m : ℝ))⁻¹ * (Annealed.sigmaBar M (n - 2) : ℝ)
      ≤ ((Annealed.sigmaBar M m : ℝ))⁻¹ * (4 * (Annealed.sigmaBar M m : ℝ)) :=
        mul_le_mul_of_nonneg_left hle hinv0
    _ = 4 := by field_simp

/-! ## Part C -- the `hshell` slot, at the explicit constant `196` -/

/-- **The `hshell` slot of `e.ugly.estimate.for.J`, discharged**.  On the honest
clause-(i) event `𝒢₁(m; s, √c⋆ γ^{−1/2})`, for every `L ≥ m` and every
scale-`n` lattice point `z` of `□_m`,

```
σ_{n−2}^{−1} · 3^{2n} ‖∇(k_L − k_{n−2})‖_{W^{1,∞}(z+□_n)} ≤ 196 · 3^{s(m−n)/4} .
```

`A_sh = 196` is an **absolute numeral**: no `s`, no `γ`, no `c⋆`, no dimension.
Two exact cancellations make this possible — the `𝒢₁` amplitude `T'` equals the
chain's `κ` (`gamma_mul_annularEventAmplitude_sq`), and the gauge weight
`3^{γn}` is exactly the one the `σ_{n−2}` lower bound produces.  The
composition is `4 · 49`: the `4` is `inv_sigmaBar_sub_two_le_of_inductionState`
(the `2` times the `3^{2γ} ≤ 2` index shift), the `49` is
`ShellGaugeBudget.shellGauge_le_of_eventG1`. -/
theorem shellBudget_of_eventG1_of_inductionState (M : ABKModel d) {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}} (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E)
    (m : ℤ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {omega : Cutoff.CutoffSample d}
    (homega : omega ∈ Support.eventG1 M m s
      (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
    {n L : ℤ} (hnm : n ≤ m) (hmL : m ≤ L) (hn2 : n - 2 ≤ m0)
    {v : Fin d → ℤ} (hv : v ∈ Support.latticeCubeSet d n m) :
    ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹ *
        ((3 : ℝ) ^ (2 * (n : ℝ)) *
          Support.shellW1InfGradNorm n
            (ShellField.translate (Support.triadicLatticePoint n v)
              (Provider.Stream.shellIncrement omega.1 (n - 2) L)))
      ≤ 196 * (3 : ℝ) ^ (s / 4 * ((m : ℝ) - (n : ℝ))) := by
  have hkap0 := annularEventAmplitude_pos M
  have hcast : ((m : ℝ) - (n : ℝ)) = ((m - n : ℤ) : ℝ) := by push_cast; ring
  rw [hcast]
  have hq0 : (0 : ℝ) ≤ ((m - n : ℤ) : ℝ) := by
    have : (0 : ℤ) ≤ m - n := by omega
    exact_mod_cast this
  have hG := shellGauge_le_of_eventG1 M m hs0 hs1 hkap0.le homega hnm hmL hv
  have h2n : (3 : ℝ) ^ (2 * (n : ℝ))
      = (3 : ℝ) ^ (M.gamma * (n : ℝ)) * (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hgpos : (0 : ℝ) ≤ (3 : ℝ) ^ (M.gamma * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hW0 : (0 : ℝ) ≤ Support.shellW1InfGradNorm n
      (ShellField.translate (Support.triadicLatticePoint n v)
        (Provider.Stream.shellIncrement omega.1 (n - 2) L)) :=
    Support.shellW1InfGradNorm_nonneg n _
  have hc0 : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * (n : ℝ)) *
      Support.shellW1InfGradNorm n
        (ShellField.translate (Support.triadicLatticePoint n v)
          (Provider.Stream.shellIncrement omega.1 (n - 2) L)) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hW0
  have hbound1 : (3 : ℝ) ^ (2 * (n : ℝ)) *
      Support.shellW1InfGradNorm n
        (ShellField.translate (Support.triadicLatticePoint n v)
          (Provider.Stream.shellIncrement omega.1 (n - 2) L))
      ≤ (3 : ℝ) ^ (M.gamma * (n : ℝ)) *
          (49 * (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹)
            * (3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ))) := by
    rw [h2n, mul_assoc]
    exact mul_le_mul_of_nonneg_left hG hgpos
  have hinv := inv_sigmaBar_sub_two_le_of_inductionState M hS (n := n) hn2
  have hb0 : (0 : ℝ) ≤ 4 * ((Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹)⁻¹
      * (3 : ℝ) ^ (-(M.gamma * (n : ℝ)))) := by
    have h1 : (0 : ℝ) ≤ (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹)⁻¹ :=
      (inv_pos.2 hkap0).le
    have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(M.gamma * (n : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    positivity
  have hmul := mul_le_mul hinv hbound1 hc0 hb0
  refine hmul.trans ?_
  have hkk : (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹)⁻¹
      * (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) = 1 :=
    inv_mul_cancel₀ (ne_of_gt hkap0)
  have hee : (3 : ℝ) ^ (-(M.gamma * (n : ℝ))) * (3 : ℝ) ^ (M.gamma * (n : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      show -(M.gamma * (n : ℝ)) + M.gamma * (n : ℝ) = 0 from by ring, Real.rpow_zero]
  have hval : (4 * ((Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹)⁻¹
        * (3 : ℝ) ^ (-(M.gamma * (n : ℝ)))))
      * ((3 : ℝ) ^ (M.gamma * (n : ℝ)) *
        (49 * (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹)
          * (3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ))))
      = 196 * (((Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹)⁻¹
          * (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
        * (((3 : ℝ) ^ (-(M.gamma * (n : ℝ))) * (3 : ℝ) ^ (M.gamma * (n : ℝ)))
          * (3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ)))) := by ring
  rw [hval, hkk, hee]
  have hmono : (3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ))
      ≤ (3 : ℝ) ^ (s / 4 * ((m - n : ℤ) : ℝ)) := by
    refine three_rpow_mono₂ ?_
    exact mul_le_mul_of_nonneg_right (by linarith only [hs0]) hq0
  calc (196 : ℝ) * (1 * (1 * (3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ))))
      = 196 * (3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ)) := by ring
    _ ≤ 196 * (3 : ℝ) ^ (s / 4 * ((m - n : ℤ) : ℝ)) := by linarith only [hmono]

end

end Algsuperdiff.Section4.Provider.Annular
