/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSixHolderExponent

/-!
# StepSevenCaccVolume

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 7c, the volume factor

## The target

ABK26 `t.regularity` Step 7c, the sentence

> Since `(z + □_n) ∩ □_m ⊆ U_{n'-2}`, passing to the smaller set costs a volume
> factor `3^{(d/2)(n'-n)} ≤ 3^{(d/2)(|𝓑|+6)}`.  By
> `e.bad.scale.proportion.bound`, this is at most `C 3^{(1/4)(1-α)(m-n)}`.

Two independent halves, both proved here unconditionally.

### Half one — what "costs a volume factor" means

The manuscript asserts the factor by inspection.  The decomposition it hides:
the factor is the square root of the ratio
of the two *volumes*, and the ratio is bounded by combining

* the **inclusion** `(z + □_{n+1}) ∩ □_m ⊆ U_{n'-2}` (the step's own stated
  hypothesis, coming from the selection and the window geometry), and
* the **volume lower bound** `3^{dn} ≤ |(z + □_{n+1}) ∩ □_m|` against the upper
  bound `|U_{n'-2}| ≤ |□_{n'}| = 3^{dn'}`.

`normalizedSqrt_le_volumeRatio_mul` is that decomposition at the level of the
volume-normalized `L²` masses: for `S ⊆ T` with `0 < |S|`,

```text
  ( |S|⁻¹ ∫_S f )^{1/2}  ≤  ( |T| / |S| )^{1/2} · ( |T|⁻¹ ∫_T f )^{1/2} ,
```

which is an identity plus monotonicity of the integral, no analysis.  It is
stated on the *scalars* `IS ≤ IT` and `volS, volT` so that it composes with any
rendering of the two masses (: the ABK26 field is `𝐚_L = ν I + 𝐤` with `𝐤`
antisymmetric, so `ν^{1/2}‖∇u‖_{L²}` IS the symmetric coefficient energy — the
left-hand side of `e.gradient.with.shom` is a coefficient-energy mass and the
comparison above is exactly what it needs).

### Half two — the budget arithmetic

`stepSevenVolumeExponent_le_of_gap` is the tex's second sentence, in full:

```text
  (d/2)(n'-n) ≤ (d/2)(|𝓑| + G)                        (the selection's gap)
              ≤ (d/2)·δ·((m-n) + 1) + (d/2)G          (e.bad.scale.proportion.bound)
              ≤ (d/2)·C₁⁻¹(1-α)((m-n) + 1) + (d/2)G   (δ ≤ C₁⁻¹(1-α))
              ≤ (1/4)(1-α)(m-n) + 1/4 + (d/2)G        (C₁ ≥ 2d+2, and 1-α ≤ 1)
```

At `G = 6` — the printed gap `max{n'-n, m-m'} ≤ |𝓑| + 6` — the constant is
`3^{3d + 1/4}`.  strengthened the lower gap to the sharp `n'-n ≤ |𝓑| + 3`, and
at `G = 3` the constant improves to `3^{3d/2 + 1/4}`.  Both are delivered.

## References

* ABK26, `t.regularity` Step 7c.
* ABK26, `e.bad.scale.proportion.bound`.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

noncomputable section

/-! ## 1. Half one — the volume-ratio cost of passing to a smaller set -/

/-- ** (b), the scalar core.**  If the mass `IS` carried by the smaller set is at
most the mass `IT` carried by the larger one, then the *volume-normalized*
square roots compare at the cost of the square root of the volume ratio:

```text
  √(IS / volS)  ≤  √(volT / volS) · √(IT / volT) .
```

No hypothesis beyond positivity of the two volumes and monotonicity of the
mass. -/
theorem normalizedSqrt_le_volumeRatio_mul {IS IT volS volT : ℝ}
    (hvolS : 0 < volS) (hvolT : 0 < volT) (hmono : IS ≤ IT) :
    Real.sqrt (IS / volS) ≤ Real.sqrt (volT / volS) * Real.sqrt (IT / volT) := by
  have hratio : (0 : ℝ) ≤ volT / volS := le_of_lt (div_pos hvolT hvolS)
  have hprod : volT / volS * (IT / volT) = IT / volS := by
    field_simp
  have hstep : IS / volS ≤ IT / volS := by gcongr
  calc Real.sqrt (IS / volS) ≤ Real.sqrt (IT / volS) := Real.sqrt_le_sqrt hstep
    _ = Real.sqrt (volT / volS * (IT / volT)) := by rw [hprod]
    _ = Real.sqrt (volT / volS) * Real.sqrt (IT / volT) := Real.sqrt_mul hratio _

/-- **The volume ratio at the two triadic scales.**  With `3^{dn} ≤ |S|` (the
tex-implicit lower bound on the truncated window `(z + □_{n+1}) ∩ □_m`) and
`|T| ≤ 3^{dn'}` (the trivial upper bound on `U_{n'-2} ⊆ z + □_{n'}`), the
square root of the volume ratio is the printed factor `3^{(d/2)(n'-n)}`. -/
theorem sqrt_volumeRatio_le_rpow_three (d : ℕ) {volS volT : ℝ} {n n' : ℤ}
    (hvolSpos : 0 < volS)
    (hvolS : Real.rpow (3 : ℝ) ((d : ℝ) * (n : ℝ)) ≤ volS)
    (hvolT : volT ≤ Real.rpow (3 : ℝ) ((d : ℝ) * (n' : ℝ))) :
    Real.sqrt (volT / volS) ≤ Real.rpow (3 : ℝ) (((d : ℝ) / 2) * ((n' : ℝ) - (n : ℝ))) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hY : (0 : ℝ) < Real.rpow (3 : ℝ) (((d : ℝ) / 2) * ((n' : ℝ) - (n : ℝ))) :=
    Real.rpow_pos_of_pos h3 _
  have hgap : (0 : ℝ) < Real.rpow (3 : ℝ) ((d : ℝ) * ((n' : ℝ) - (n : ℝ))) :=
    Real.rpow_pos_of_pos h3 _
  have hsplit : Real.rpow (3 : ℝ) ((d : ℝ) * ((n' : ℝ) - (n : ℝ))) *
      Real.rpow (3 : ℝ) ((d : ℝ) * (n : ℝ)) =
      Real.rpow (3 : ℝ) ((d : ℝ) * (n' : ℝ)) := by
    have h := Real.rpow_add h3 ((d : ℝ) * ((n' : ℝ) - (n : ℝ))) ((d : ℝ) * (n : ℝ))
    have hexp : (d : ℝ) * ((n' : ℝ) - (n : ℝ)) + (d : ℝ) * (n : ℝ) =
        (d : ℝ) * (n' : ℝ) := by ring
    rw [hexp] at h
    exact h.symm
  have hratio : volT / volS ≤ Real.rpow (3 : ℝ) ((d : ℝ) * ((n' : ℝ) - (n : ℝ))) := by
    rw [div_le_iff₀ hvolSpos]
    have hstep : Real.rpow (3 : ℝ) ((d : ℝ) * ((n' : ℝ) - (n : ℝ))) *
        Real.rpow (3 : ℝ) ((d : ℝ) * (n : ℝ)) ≤
        Real.rpow (3 : ℝ) ((d : ℝ) * ((n' : ℝ) - (n : ℝ))) * volS :=
      mul_le_mul_of_nonneg_left hvolS hgap.le
    linarith only [hvolT, hstep, hsplit.ge, hsplit.le]
  have hsq : Real.rpow (3 : ℝ) (((d : ℝ) / 2) * ((n' : ℝ) - (n : ℝ))) *
      Real.rpow (3 : ℝ) (((d : ℝ) / 2) * ((n' : ℝ) - (n : ℝ))) =
      Real.rpow (3 : ℝ) ((d : ℝ) * ((n' : ℝ) - (n : ℝ))) := by
    have h := Real.rpow_add h3 (((d : ℝ) / 2) * ((n' : ℝ) - (n : ℝ)))
      (((d : ℝ) / 2) * ((n' : ℝ) - (n : ℝ)))
    have hexp : ((d : ℝ) / 2) * ((n' : ℝ) - (n : ℝ)) +
        ((d : ℝ) / 2) * ((n' : ℝ) - (n : ℝ)) = (d : ℝ) * ((n' : ℝ) - (n : ℝ)) := by ring
    rw [hexp] at h
    exact h.symm
  calc Real.sqrt (volT / volS)
      ≤ Real.sqrt (Real.rpow (3 : ℝ) ((d : ℝ) * ((n' : ℝ) - (n : ℝ)))) :=
        Real.sqrt_le_sqrt hratio
    _ = Real.sqrt (Real.rpow (3 : ℝ) (((d : ℝ) / 2) * ((n' : ℝ) - (n : ℝ))) *
          Real.rpow (3 : ℝ) (((d : ℝ) / 2) * ((n' : ℝ) - (n : ℝ)))) := by rw [hsq]
    _ = Real.rpow (3 : ℝ) (((d : ℝ) / 2) * ((n' : ℝ) - (n : ℝ))) :=
        Real.sqrt_mul_self hY.le

/-! ## 2. Half two — the budget arithmetic -/

/-- `(d/2)·C₁⁻¹ ≤ 1/4`'s floor `C₁ ≥ 2d + 2`.  This is the *only* place the
`C₁`-largeness of the volume factor is used, and it is the `+2` (not the naive
`C₁ ≥ 2d`) that makes it go through with room to spare. -/
theorem half_dim_mul_inv_le_quarter (d : ℕ) {C1 : ℝ} (hC1 : 2 * (d : ℝ) + 2 ≤ C1) :
    (d : ℝ) / 2 * C1⁻¹ ≤ 1 / 4 := by
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hC1pos : (0 : ℝ) < C1 := by linarith only [hC1, hd]
  rw [mul_inv_le_iff₀ hC1pos]
  linarith only [hC1, hd]

/-- **The volume exponent, bounded by the budget** (second sentence).

At a gap `n' - n ≤ |𝓑| + G`, the budget `|𝓑| ≤ δ((m-n)+1)`, the parameter
choice `δ ≤ C₁⁻¹(1-α)`'s floor `C₁ ≥ 2d + 2`:

```text
  (d/2)(n' - n)  ≤  (d/2)·G  +  1/4  +  (1/4)(1-α)(m-n) .
```

The `+1/4` is the budget's own `+1` (`δ((m-n)+1)` rather than `δ(m-n)`)
weighted by `(1/4)(1-α) ≤ 1/4`. -/
theorem stepSevenVolumeExponent_le_of_gap (d : ℕ) {C1 alpha delta : ℝ} {B : ℕ}
    {n m n' : ℤ} {G : ℤ}
    (hC1 : 2 * (d : ℝ) + 2 ≤ C1) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hnm : n ≤ m) (hdelta : delta ≤ C1⁻¹ * (1 - alpha))
    (hgap : n' - n ≤ (B : ℤ) + G)
    (hbudget : (B : ℝ) ≤ delta * (((m - n).toNat : ℝ) + 1)) :
    ((d : ℝ) / 2) * ((n' : ℝ) - (n : ℝ)) ≤
      ((d : ℝ) / 2) * (G : ℝ) + 1 / 4 + 1 / 4 * stepSixExponent alpha n m := by
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hd2 : (0 : ℝ) ≤ (d : ℝ) / 2 := by linarith only [hd]
  have hC1pos : (0 : ℝ) < C1 := by linarith only [hC1, hd]
  have hA0 : (0 : ℝ) ≤ 1 - alpha := by linarith only [halpha1]
  have hA1 : (1 : ℝ) - alpha ≤ 1 := by linarith only [halpha0]
  -- the window length, as a real
  have hT : ((m - n).toNat : ℝ) = (m : ℝ) - (n : ℝ) := by
    have h : ((m - n).toNat : ℤ) = m - n := Int.toNat_of_nonneg (by omega)
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h
  have hT0 : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
    have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    linarith only [this]
  -- the selection gap, as a real
  have hgapR : (n' : ℝ) - (n : ℝ) ≤ (B : ℝ) + (G : ℝ) := by
    have h : ((n' - n : ℤ) : ℝ) ≤ (((B : ℤ) + G : ℤ) : ℝ) := by exact_mod_cast hgap
    push_cast at h
    linarith only [h]
  -- the budget, transported through `δ ≤ C₁⁻¹(1-α)`
  have hTp : (0 : ℝ) ≤ ((m : ℝ) - (n : ℝ)) + 1 := by linarith only [hT0]
  have hb1 : (B : ℝ) ≤ delta * (((m : ℝ) - (n : ℝ)) + 1) := by
    rw [hT] at hbudget; exact hbudget
  have hb2 : delta * (((m : ℝ) - (n : ℝ)) + 1) ≤
      C1⁻¹ * (1 - alpha) * (((m : ℝ) - (n : ℝ)) + 1) :=
    mul_le_mul_of_nonneg_right hdelta hTp
  have hb3 : ((d : ℝ) / 2) * (B : ℝ) ≤
      ((d : ℝ) / 2) * (C1⁻¹ * (1 - alpha) * (((m : ℝ) - (n : ℝ)) + 1)) :=
    mul_le_mul_of_nonneg_left (le_trans hb1 hb2) hd2
  -- `(d/2)·C₁⁻¹ ≤ 1/4`
  have hq := half_dim_mul_inv_le_quarter d hC1
  have hAT : (0 : ℝ) ≤ (1 - alpha) * (((m : ℝ) - (n : ℝ)) + 1) := mul_nonneg hA0 hTp
  have hb4 : ((d : ℝ) / 2) * (C1⁻¹ * (1 - alpha) * (((m : ℝ) - (n : ℝ)) + 1)) ≤
      1 / 4 * ((1 - alpha) * (((m : ℝ) - (n : ℝ)) + 1)) := by
    have h := mul_le_mul_of_nonneg_right hq hAT
    calc ((d : ℝ) / 2) * (C1⁻¹ * (1 - alpha) * (((m : ℝ) - (n : ℝ)) + 1))
        = ((d : ℝ) / 2 * C1⁻¹) * ((1 - alpha) * (((m : ℝ) - (n : ℝ)) + 1)) := by ring
      _ ≤ 1 / 4 * ((1 - alpha) * (((m : ℝ) - (n : ℝ)) + 1)) := h
  -- the `+1` of the budget costs `(1/4)(1-α) ≤ 1/4`
  have hb5 : 1 / 4 * ((1 - alpha) * (((m : ℝ) - (n : ℝ)) + 1)) ≤
      1 / 4 + 1 / 4 * ((1 - alpha) * ((m : ℝ) - (n : ℝ))) := by
    have h : (1 : ℝ) / 4 * (1 - alpha) ≤ 1 / 4 := by linarith only [hA1]
    have hexp : 1 / 4 * ((1 - alpha) * (((m : ℝ) - (n : ℝ)) + 1)) =
        1 / 4 * ((1 - alpha) * ((m : ℝ) - (n : ℝ))) + 1 / 4 * (1 - alpha) := by ring
    linarith only [h, hexp.ge, hexp.le]
  -- assemble
  have hgapmul : ((d : ℝ) / 2) * ((n' : ℝ) - (n : ℝ)) ≤
      ((d : ℝ) / 2) * ((B : ℝ) + (G : ℝ)) := mul_le_mul_of_nonneg_left hgapR hd2
  have hexpand : ((d : ℝ) / 2) * ((B : ℝ) + (G : ℝ)) =
      ((d : ℝ) / 2) * (B : ℝ) + ((d : ℝ) / 2) * (G : ℝ) := by ring
  rw [stepSixExponent]
  linarith only [hgapmul, hexpand.ge, hexpand.le, hb3, hb4, hb5]

/-- **The volume factor itself**, at the printed gap `n' - n ≤ |𝓑| + 6`:
`3^{(d/2)(n'-n)} ≤ 3^{3d + 1/4} · 3^{(1/4)(1-α)(m-n)}`, i.e. the
tex's `C 3^{(1/4)(1-α)(m-n)}` with the constant `C = C(d) = 3^{3d + 1/4}` made
explicit. -/
theorem three_rpow_stepSevenVolume_le (d : ℕ) {C1 alpha delta : ℝ} {B : ℕ}
    {n m n' : ℤ}
    (hC1 : 2 * (d : ℝ) + 2 ≤ C1) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hnm : n ≤ m) (hdelta : delta ≤ C1⁻¹ * (1 - alpha))
    (hgap : n' - n ≤ (B : ℤ) + 6)
    (hbudget : (B : ℝ) ≤ delta * (((m - n).toNat : ℝ) + 1)) :
    Real.rpow (3 : ℝ) (((d : ℝ) / 2) * ((n' : ℝ) - (n : ℝ))) ≤
      Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) *
        Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) := by
  have h := stepSevenVolumeExponent_le_of_gap d (G := 6) hC1 halpha0
    halpha1 hnm hdelta hgap hbudget
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hcast : (((6 : ℤ) : ℝ)) = (6 : ℝ) := by norm_num
  rw [hcast] at h
  calc Real.rpow (3 : ℝ) (((d : ℝ) / 2) * ((n' : ℝ) - (n : ℝ)))
      ≤ Real.rpow (3 : ℝ) ((3 * (d : ℝ) + 1 / 4) +
          1 / 4 * stepSixExponent alpha n m) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [h])
    _ = _ := Real.rpow_add h3 _ _

end

end Algsuperdiff.Section4.Provider.Regularity
