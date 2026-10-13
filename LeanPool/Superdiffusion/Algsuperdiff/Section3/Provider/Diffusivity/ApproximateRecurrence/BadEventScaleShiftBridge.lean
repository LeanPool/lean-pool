/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.GoodLocalEventAtBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.ShellDerivativeControl

/-!
# BadEventScaleShiftBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The scale-shift bridge from the frozen bad-event estimate to the dimension floor

`Algsuperdiff.Frozen.Section3.bad_event_estimate` publishes only `1 ≤ Ccg` about
its existential witness, while the Section 3.4 good half needs
`(d : ℝ) ^ 6 ≤ Ccg` at the **same** constant, and `goodLocalEvent` is not
monotone in that constant: its threshold

```
goodLocalThreshold M C m n = (1/2) * C⁻¹ * 3 ^ (-(1/2) * scaleGapPos m n) * sigmabar
```

is antitone in `C`, so the sensitivity clause tightens and the ellipticity
clause loosens as `C` grows.  An earlier disclosure in this cone concluded from
this that no transfer exists.  **That conclusion was wrong**, and this module
proves the transfer.

## The mechanism

The constant can be traded against the *cube scale*, because the oscillation
gauge is more strongly scale-weighted than the threshold.  At a common centre
(`cubeBasePoint (originCube d ell) = 0` for every `ell`),

```
cubeOscGauge (originCube d j) h
  = max (3 ^ (2 j) * ‖∇²h‖_{L∞(cu_j)}) (3 ^ j * ‖∇h‖_{L∞(cu_j)}) ,
```

so enlarging the cube from scale `m` to `mu` multiplies the *sup* upwards but the
*weights* by `3 ^ (-2 (mu - m))` resp. `3 ^ (-(mu - m))`, giving

* `cubeOscGauge_originCube_le_zpow_mul` (**L1**):
  `cubeOscGauge (originCube d m) h ≤ 3 ^ (m - mu) * cubeOscGauge (originCube d mu) h`,

whereas the threshold only gains `3 ^ ((mu - m)/2)`.  With `mu = m + 2k` the two
weights combine to an exact identity

* `goodLocalThreshold_scaleShift`:
  `3 ^ (m - (m + 2k)) * goodLocalThreshold M (2 C) (m + 2k) n
     = goodLocalThreshold M (2 * 3 ^ k * C) m n`,

whence the two clause inclusions

* `goodLocalSensitivity_scaleShift_subset_le`:
  `Sens (2 C, cu_{m+2k}, n) ⊆ Sens (2 * 3 ^ k * C, cu_m, n)`;
* `goodLocalEllipticity_const_mono`: `Ellip` only grows with the constant;

and their combination

* `goodLocalEvent_inter_subset_scaleShift_le`:
  `good (2C, cu_m, n) ∩ good (2C, cu_{m+2k}, n) ⊆ good (2 * 3 ^ k * C, cu_m, n)`.

## The dimension shift

`badEventScaleShiftExp d := 6 * d` is dimension-only and elementary: `d < 3 ^ d`
gives `(d : ℝ) ^ 6 ≤ 3 ^ (6 * d)`, which is all the floor `(d : ℝ) ^ 6 ≤ Cbase`
needs.  No logarithm and no ceiling occurs.

## Scope

This module proves the **geometric core** of the bridge, verified in Lean.  The
consuming step -- applying `Algsuperdiff.Frozen.Section3.bad_event_estimate`
twice at the same translate `triadicCubeShift R`, once at the cube scale
`R.scale` and once at `R.scale + 2 * badEventScaleShiftExp d`, and combining by
the union bound -- is proved in
`Provider.Diffusivity.ApproximateRecurrence.BadEventFrozenApplication`, which
is what the Section 3.4 bad-event leg consumes.

The clause inclusions are therefore stated in the **full regime `m ≤ n`**
(`goodLocalThreshold_scaleShift_le`, `goodLocalSensitivity_scaleShift_subset_le`,
`goodLocalEvent_inter_subset_scaleShift_le`), not only when the enlarged scale
`m + 2 k` still sits below `n`: the Section 3.4 grid is indexed by a free
recurrence multiplier and offers no headroom at its degenerate end, so the
consumer discharges the two frozen `n < m` gates on their own terms instead.
The exact threshold identity at the original gate `m + 2 k ≤ n` is kept as
`goodLocalThreshold_scaleShift`.

## References

* ABK26, `l.bad.event.lemma`; `e.good.local.events`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Stream

noncomputable section

variable {d : ℕ}

/-! ## The gauge at an origin cube -/

/-- The oscillation gauge at an origin cube, with its base point evaluated. -/
private theorem cubeOscGauge_originCube (ell : ℤ) (h : ShellField d) :
    cubeOscGauge (originCube d ell) h =
      max ((3 : ℝ) ^ (2 * ell) *
            localCubeSecondDerivNorm ell (ShellField.translate (0 : Vec d) h))
          ((3 : ℝ) ^ ell *
            localCubeDerivNorm ell (ShellField.translate (0 : Vec d) h)) := by
  have hb : cubeBasePoint (originCube d ell) = (0 : Vec d) := by
    funext i
    simp [cubeBasePoint, originCube]
  simp only [cubeOscGauge, hb]
  rfl

/-- **(L1) Cube-scale monotonicity of the oscillation gauge at a common centre.**
Enlarging the origin cube from scale `m` to `mu ≥ m` gains the factor
`3 ^ (m - mu) ≤ 1`: the sup can only grow, but the gauge weights `3 ^ (2 j)` and
`3 ^ j` grow strictly faster.  This is the lemma that makes the constant of
`e.good.local.events` tradeable against the cube scale. -/
theorem cubeOscGauge_originCube_le_zpow_mul {m mu : ℤ} (hle : m ≤ mu)
    (h : ShellField d) :
    cubeOscGauge (originCube d m) h ≤
      (3 : ℝ) ^ (m - mu) * cubeOscGauge (originCube d mu) h := by
  set g : ShellField d := ShellField.translate (0 : Vec d) h with hgdef
  have hpos : ∀ k : ℤ, (0 : ℝ) < (3 : ℝ) ^ k := fun k => zpow_pos (by norm_num) k
  have hsec := localCubeSecondDerivNorm_mono hle g
  have hfst := localCubeDerivNorm_mono hle g
  have hsec0 : 0 ≤ localCubeSecondDerivNorm mu g := localCubeSecondDerivNorm_nonneg mu g
  have hfst0 : 0 ≤ localCubeDerivNorm mu g := localCubeDerivNorm_nonneg mu g
  have hAmu : (3 : ℝ) ^ (2 * mu) * localCubeSecondDerivNorm mu g ≤
      cubeOscGauge (originCube d mu) h := by
    rw [cubeOscGauge_originCube]
    exact le_max_left _ _
  have hBmu : (3 : ℝ) ^ mu * localCubeDerivNorm mu g ≤
      cubeOscGauge (originCube d mu) h := by
    rw [cubeOscGauge_originCube]
    exact le_max_right _ _
  rw [cubeOscGauge_originCube]
  refine max_le ?_ ?_
  · have h1 : (3 : ℝ) ^ (2 * m) * localCubeSecondDerivNorm m g ≤
        (3 : ℝ) ^ (2 * m) * localCubeSecondDerivNorm mu g :=
      mul_le_mul_of_nonneg_left hsec (hpos _).le
    have hzp : (3 : ℝ) ^ (2 * m) ≤ (3 : ℝ) ^ (m - mu + 2 * mu) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : (3 : ℝ) ^ (2 * m) * localCubeSecondDerivNorm mu g ≤
        (3 : ℝ) ^ (m - mu + 2 * mu) * localCubeSecondDerivNorm mu g :=
      mul_le_mul_of_nonneg_right hzp hsec0
    have hsplit : (3 : ℝ) ^ (m - mu + 2 * mu) * localCubeSecondDerivNorm mu g =
        (3 : ℝ) ^ (m - mu) * ((3 : ℝ) ^ (2 * mu) * localCubeSecondDerivNorm mu g) := by
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      ring
    have h3 : (3 : ℝ) ^ (m - mu) * ((3 : ℝ) ^ (2 * mu) * localCubeSecondDerivNorm mu g) ≤
        (3 : ℝ) ^ (m - mu) * cubeOscGauge (originCube d mu) h :=
      mul_le_mul_of_nonneg_left hAmu (hpos _).le
    calc (3 : ℝ) ^ (2 * m) * localCubeSecondDerivNorm m g
        ≤ (3 : ℝ) ^ (2 * m) * localCubeSecondDerivNorm mu g := h1
      _ ≤ (3 : ℝ) ^ (m - mu + 2 * mu) * localCubeSecondDerivNorm mu g := h2
      _ = (3 : ℝ) ^ (m - mu) * ((3 : ℝ) ^ (2 * mu) * localCubeSecondDerivNorm mu g) := hsplit
      _ ≤ (3 : ℝ) ^ (m - mu) * cubeOscGauge (originCube d mu) h := h3
  · have h1 : (3 : ℝ) ^ m * localCubeDerivNorm m g ≤
        (3 : ℝ) ^ m * localCubeDerivNorm mu g :=
      mul_le_mul_of_nonneg_left hfst (hpos _).le
    have hsplit : (3 : ℝ) ^ m * localCubeDerivNorm mu g =
        (3 : ℝ) ^ (m - mu) * ((3 : ℝ) ^ mu * localCubeDerivNorm mu g) := by
      rw [show m = (m - mu) + mu by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      ring_nf
    have h3 : (3 : ℝ) ^ (m - mu) * ((3 : ℝ) ^ mu * localCubeDerivNorm mu g) ≤
        (3 : ℝ) ^ (m - mu) * cubeOscGauge (originCube d mu) h :=
      mul_le_mul_of_nonneg_left hBmu (hpos _).le
    calc (3 : ℝ) ^ m * localCubeDerivNorm m g
        ≤ (3 : ℝ) ^ m * localCubeDerivNorm mu g := h1
      _ = (3 : ℝ) ^ (m - mu) * ((3 : ℝ) ^ mu * localCubeDerivNorm mu g) := hsplit
      _ ≤ (3 : ℝ) ^ (m - mu) * cubeOscGauge (originCube d mu) h := h3

/-! ## The threshold identity and the two clause inclusions -/

/-- The exact threshold identity behind the scale shift: the cube-scale gain of
the gauge and the loss of the threshold combine to the constant `3 ^ k`. -/
theorem goodLocalThreshold_scaleShift (M : ABKModel d) {C : ℝ} (hC : 0 < C)
    (m n : ℤ) (k : ℕ) (hmn : m + 2 * (k : ℤ) ≤ n) :
    (3 : ℝ) ^ (m - (m + 2 * (k : ℤ))) *
        goodLocalThreshold M (2 * C) (m + 2 * (k : ℤ)) n =
      goodLocalThreshold M (2 * (3 : ℝ) ^ k * C) m n := by
  have hmn' : m ≤ n := by omega
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hgap1 : scaleGapPos (m + 2 * (k : ℤ)) n = (n : ℝ) - ((m + 2 * (k : ℤ) : ℤ) : ℝ) :=
    scaleGapPos_of_le hmn
  have hgap2 : scaleGapPos m n = (n : ℝ) - (m : ℝ) := scaleGapPos_of_le hmn'
  have hzp : (3 : ℝ) ^ (m - (m + 2 * (k : ℤ))) = (3 : ℝ) ^ (-(2 * (k : ℝ))) := by
    rw [show m - (m + 2 * (k : ℤ)) = -(2 * (k : ℤ)) by ring,
      ← Real.rpow_intCast 3 (-(2 * (k : ℤ)))]
    norm_num
  have hpk : (3 : ℝ) ^ k = (3 : ℝ) ^ ((k : ℝ)) := (Real.rpow_natCast 3 k).symm
  have hexp : (3 : ℝ) ^ (-(2 * (k : ℝ))) *
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((n : ℝ) - ((m + 2 * (k : ℤ) : ℤ) : ℝ))) =
      ((3 : ℝ) ^ ((k : ℝ)))⁻¹ *
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((n : ℝ) - (m : ℝ))) := by
    rw [← Real.rpow_neg (le_of_lt h3) ((k : ℝ)), ← Real.rpow_add h3, ← Real.rpow_add h3]
    congr 1
    push_cast
    ring
  have h3k : (0 : ℝ) < (3 : ℝ) ^ ((k : ℝ)) := Real.rpow_pos_of_pos h3 _
  rw [goodLocalThreshold, goodLocalThreshold, hgap1, hgap2, hzp, hpk]
  calc (3 : ℝ) ^ (-(2 * (k : ℝ))) *
        ((1 / 2 : ℝ) * (2 * C)⁻¹ *
          (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((n : ℝ) - ((m + 2 * (k : ℤ) : ℤ) : ℝ))) *
          ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)))
      = ((3 : ℝ) ^ (-(2 * (k : ℝ))) *
            (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((n : ℝ) - ((m + 2 * (k : ℤ) : ℤ) : ℝ)))) *
          ((1 / 2 : ℝ) * (2 * C)⁻¹ *
            ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))) := by ring
    _ = (((3 : ℝ) ^ ((k : ℝ)))⁻¹ *
            (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((n : ℝ) - (m : ℝ)))) *
          ((1 / 2 : ℝ) * (2 * C)⁻¹ *
            ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))) := by rw [hexp]
    _ = (1 / 2 : ℝ) * (2 * (3 : ℝ) ^ ((k : ℝ)) * C)⁻¹ *
          (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((n : ℝ) - (m : ℝ))) *
          ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)) := by
        field_simp

/-- **The threshold scale shift as an inequality, in the full regime `m ≤ n`.**

The exact identity of `goodLocalThreshold_scaleShift` needs the enlarged scale
`m + 2 k` to sit below the field scale `n`.  When it does not, the enlarged
threshold saturates at its own gap `0` while the original one keeps the factor
`3 ^ (-(1/2)(n - m))`, and the shifted comparison survives *as an inequality*
because `n - m ≤ 2 k` on that branch.  Only this inequality is used downstream,
so the bridge applies at every cube of the Section 3.4 grid, not only at those
with `2 k` scales of headroom. -/
theorem goodLocalThreshold_scaleShift_le (M : ABKModel d) {C : ℝ} (hC : 0 < C)
    (m n : ℤ) (k : ℕ) (hmn : m ≤ n) :
    (3 : ℝ) ^ (m - (m + 2 * (k : ℤ))) *
        goodLocalThreshold M (2 * C) (m + 2 * (k : ℤ)) n ≤
      goodLocalThreshold M (2 * (3 : ℝ) ^ k * C) m n := by
  rcases le_or_gt (m + 2 * (k : ℤ)) n with hle | hlt
  · exact le_of_eq (goodLocalThreshold_scaleShift M hC m n k hle)
  · have h3 : (0 : ℝ) < 3 := by norm_num
    have hCne : C ≠ 0 := ne_of_gt hC
    have hsig : (0 : ℝ) < ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)) :=
      (Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1)).2
    have hzp : (3 : ℝ) ^ (m - (m + 2 * (k : ℤ))) = (3 : ℝ) ^ (-(2 * (k : ℝ))) := by
      rw [show m - (m + 2 * (k : ℤ)) = -(2 * (k : ℤ)) by ring,
        ← Real.rpow_intCast 3 (-(2 * (k : ℤ)))]
      norm_num
    have hpk : (3 : ℝ) ^ k = (3 : ℝ) ^ ((k : ℝ)) := (Real.rpow_natCast 3 k).symm
    have h3k : (0 : ℝ) < (3 : ℝ) ^ ((k : ℝ)) := Real.rpow_pos_of_pos h3 _
    have h3kne : (3 : ℝ) ^ ((k : ℝ)) ≠ 0 := ne_of_gt h3k
    have hgap1 : scaleGapPos (m + 2 * (k : ℤ)) n = 0 := scaleGapPos_of_lt hlt
    have hgap2 : scaleGapPos m n = (n : ℝ) - (m : ℝ) := scaleGapPos_of_le hmn
    have hnm2 : (n : ℝ) ≤ (m : ℝ) + 2 * (k : ℝ) := by exact_mod_cast hlt.le
    have hkey : (3 : ℝ) ^ (-(2 * (k : ℝ))) ≤
        ((3 : ℝ) ^ ((k : ℝ)))⁻¹ *
          (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((n : ℝ) - (m : ℝ))) := by
      rw [← Real.rpow_neg (le_of_lt h3), ← Real.rpow_add h3]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      linarith
    have hA : (0 : ℝ) < (1 / 2 : ℝ) * (2 * C)⁻¹ *
        ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)) :=
      mul_pos (mul_pos (by norm_num) (inv_pos.2 (by linarith))) hsig
    rw [goodLocalThreshold, goodLocalThreshold, hgap1, hgap2, hzp, hpk]
    have hstep := mul_le_mul_of_nonneg_right hkey hA.le
    calc (3 : ℝ) ^ (-(2 * (k : ℝ))) *
          ((1 / 2 : ℝ) * (2 * C)⁻¹ * (3 : ℝ) ^ (-(1 / 2 : ℝ) * (0 : ℝ)) *
            ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)))
        = (3 : ℝ) ^ (-(2 * (k : ℝ))) *
            ((1 / 2 : ℝ) * (2 * C)⁻¹ *
              ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))) := by
          rw [mul_zero, Real.rpow_zero, mul_one]
      _ ≤ (((3 : ℝ) ^ ((k : ℝ)))⁻¹ *
            (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((n : ℝ) - (m : ℝ)))) *
              ((1 / 2 : ℝ) * (2 * C)⁻¹ *
                ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))) := hstep
      _ = (1 / 2 : ℝ) * (2 * (3 : ℝ) ^ ((k : ℝ)) * C)⁻¹ *
            (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((n : ℝ) - (m : ℝ))) *
            ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)) := by
          field_simp

/-- **The scale shift on the sensitivity clause.**  Membership at the *enlarged*
cube and the small constant implies membership at the *original* cube and the
constant multiplied by `3 ^ k`.  Stated in the full regime `m ≤ n`, through
`goodLocalThreshold_scaleShift_le`. -/
theorem goodLocalSensitivity_scaleShift_subset_le (M : ABKModel d) {C : ℝ} (hC : 0 < C)
    (m n : ℤ) (k : ℕ) (hmn : m ≤ n) :
    goodLocalSensitivity M (2 * C) (originCube d (m + 2 * (k : ℤ))) n ⊆
      goodLocalSensitivity M (2 * (3 : ℝ) ^ k * C) (originCube d m) n := by
  intro omega homega L hL
  have hle : m ≤ m + 2 * (k : ℤ) := by omega
  have hpow : (0 : ℝ) < (3 : ℝ) ^ (m - (m + 2 * (k : ℤ))) :=
    zpow_pos (by norm_num) _
  have hsens0 : (0 : ℝ) ≤ sensitivityConstMax d := (sensitivityConstMax_pos d).le
  have hgauge : cubeOscGauge (originCube d m) (shellIncrement omega.1 n L) ≤
      (3 : ℝ) ^ (m - (m + 2 * (k : ℤ))) *
        cubeOscGauge (originCube d (m + 2 * (k : ℤ))) (shellIncrement omega.1 n L) :=
    cubeOscGauge_originCube_le_zpow_mul hle _
  have h1 : sensitivityConstMax d *
        incrementOscGauge₂ (originCube d m) n L omega ≤
      (3 : ℝ) ^ (m - (m + 2 * (k : ℤ))) *
        (sensitivityConstMax d *
          incrementOscGauge₂ (originCube d (m + 2 * (k : ℤ))) n L omega) := by
    have hmul := mul_le_mul_of_nonneg_left hgauge hsens0
    calc sensitivityConstMax d * incrementOscGauge₂ (originCube d m) n L omega
        = sensitivityConstMax d *
            cubeOscGauge (originCube d m) (shellIncrement omega.1 n L) := rfl
      _ ≤ sensitivityConstMax d *
            ((3 : ℝ) ^ (m - (m + 2 * (k : ℤ))) *
              cubeOscGauge (originCube d (m + 2 * (k : ℤ)))
                (shellIncrement omega.1 n L)) := hmul
      _ = (3 : ℝ) ^ (m - (m + 2 * (k : ℤ))) *
            (sensitivityConstMax d *
              incrementOscGauge₂ (originCube d (m + 2 * (k : ℤ))) n L omega) := by
          simp only [incrementOscGauge₂]
          ring
  have h2 : (3 : ℝ) ^ (m - (m + 2 * (k : ℤ))) *
        (sensitivityConstMax d *
          incrementOscGauge₂ (originCube d (m + 2 * (k : ℤ))) n L omega) ≤
      (3 : ℝ) ^ (m - (m + 2 * (k : ℤ))) *
        goodLocalThreshold M (2 * C) (m + 2 * (k : ℤ)) n :=
    mul_le_mul_of_nonneg_left (homega L hL) hpow.le
  have h3 := goodLocalThreshold_scaleShift_le M hC m n k hmn
  show sensitivityConstMax d * incrementOscGauge₂ (originCube d m) n L omega ≤
    goodLocalThreshold M (2 * (3 : ℝ) ^ k * C) m n
  linarith [h1, h2, h3]

/-- The ellipticity clause only grows when the constant grows, because the
threshold it lower-bounds is antitone in the constant. -/
theorem goodLocalEllipticity_const_mono (M : ABKModel d) {C C' : ℝ} (hC : 0 < C)
    (hCC' : C ≤ C') (Q : TriadicCube d) (n : ℤ) :
    goodLocalEllipticity M C Q n ⊆ goodLocalEllipticity M C' Q n := by
  intro omega homega
  have hC' : (0 : ℝ) < C' := lt_of_lt_of_le hC hCC'
  have hinv : (C')⁻¹ ≤ C⁻¹ := by
    rw [inv_le_inv₀ hC' hC]
    exact hCC'
  have hpow : (0 : ℝ) < (3 : ℝ) ^ (-(1 / 2 : ℝ) * scaleGapPos Q.scale n) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hsig : (0 : ℝ) < ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)) :=
    (Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1)).2
  have hthr : goodLocalThreshold M C' Q.scale n ≤ goodLocalThreshold M C Q.scale n := by
    simp only [goodLocalThreshold]
    have h1 : (1 / 2 : ℝ) * (C')⁻¹ ≤ (1 / 2 : ℝ) * C⁻¹ := by linarith
    have hXS : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ) * scaleGapPos Q.scale n) *
        ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)) :=
      mul_nonneg hpow.le hsig.le
    calc (1 / 2 : ℝ) * (C')⁻¹ *
            (3 : ℝ) ^ (-(1 / 2 : ℝ) * scaleGapPos Q.scale n) *
            ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))
        = ((1 / 2 : ℝ) * (C')⁻¹) *
            ((3 : ℝ) ^ (-(1 / 2 : ℝ) * scaleGapPos Q.scale n) *
              ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))) := by ring
      _ ≤ ((1 / 2 : ℝ) * C⁻¹) *
            ((3 : ℝ) ^ (-(1 / 2 : ℝ) * scaleGapPos Q.scale n) *
              ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))) :=
          mul_le_mul_of_nonneg_right h1 hXS
      _ = (1 / 2 : ℝ) * C⁻¹ *
            (3 : ℝ) ^ (-(1 / 2 : ℝ) * scaleGapPos Q.scale n) *
            ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)) := by ring
  exact le_trans hthr homega

/-- **The scale-shift bridge at the level of the good local event.**  The two
frozen-reachable events at the small constant, one at the cube scale and one at
the enlarged scale, together imply the event at the enlarged constant.  Stated
in the full regime `m ≤ n`: no headroom between the enlarged scale and the field
scale is required. -/
theorem goodLocalEvent_inter_subset_scaleShift_le (M : ABKModel d) {C : ℝ} (hC : 0 < C)
    (m n : ℤ) (k : ℕ) (hmn : m ≤ n) :
    goodLocalEvent M (2 * C) (originCube d m) n ∩
        goodLocalEvent M (2 * C) (originCube d (m + 2 * (k : ℤ))) n ⊆
      goodLocalEvent M (2 * (3 : ℝ) ^ k * C) (originCube d m) n := by
  rintro omega ⟨h1, h2⟩
  have hk1 : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hmono : 2 * C ≤ 2 * (3 : ℝ) ^ k * C := by nlinarith
  exact ⟨goodLocalSensitivity_scaleShift_subset_le M hC m n k hmn h2.1,
    goodLocalEllipticity_const_mono M (by linarith) hmono _ _ h1.2⟩

/-! ## The dimension-only scale shift -/

/-- The dimension-only scale shift: `3 ^ (6 d)` clears the floor `(d : ℝ) ^ 6`
by the elementary `d < 3 ^ d`.  No logarithm and no ceiling occurs. -/
def badEventScaleShiftExp (d : ℕ) : ℕ := 6 * d

/-- `(d : ℝ) ^ 6 ≤ 3 ^ badEventScaleShiftExp d`. -/
theorem dim_pow_six_le_three_pow_scaleShiftExp (d : ℕ) :
    (d : ℝ) ^ 6 ≤ (3 : ℝ) ^ badEventScaleShiftExp d := by
  have hd : d < 3 ^ d := Nat.lt_pow_self (by norm_num)
  have hdR : (d : ℝ) ≤ ((3 ^ d : ℕ) : ℝ) := by exact_mod_cast hd.le
  have hcast : ((3 ^ d : ℕ) : ℝ) = (3 : ℝ) ^ d := by push_cast; ring
  rw [hcast] at hdR
  have h0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hstep : (d : ℝ) ^ 6 ≤ ((3 : ℝ) ^ d) ^ 6 := pow_le_pow_left₀ h0 hdR 6
  have hfin : ((3 : ℝ) ^ d) ^ 6 = (3 : ℝ) ^ badEventScaleShiftExp d := by
    rw [badEventScaleShiftExp, ← pow_mul]
    ring_nf
  linarith [hstep, hfin.le, hfin.ge]


end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
