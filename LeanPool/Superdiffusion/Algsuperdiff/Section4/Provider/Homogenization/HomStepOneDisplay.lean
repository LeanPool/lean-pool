/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepOneMoment

/-!
# HomStepOneDisplay

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5, Step 1: the printed display the `𝓔` estimate

## The target

The Step-1 conclusion, in the ADOPTED form of (fix 2):

```
𝔼[ EthmB(m)^p ]^{1/p}  ≤  C ( √p + √|log γ| ) √γ (log γ)²
```

for `p ∈ [1, C⁻¹ γ⁻¹ |log γ|⁻¹]`, in the `lintegral` normal form `∫⁻ EthmB^p ≤
(ofReal R)^p`.

The `√|log γ|` summand is NOT cosmetic: it is exactly the anchor's own
lower moment endpoint `q ≥ 2 d s'⁻¹`, which at the §4.5 exponents reads
`q ≥ 8 d |log γ|`.  The assembly below evaluates the anchor at
`q = max(4p, 8d|log γ|)` and `√q ≤ 2√p + √(8d)√|log γ|` is where the second
summand comes from.  The printed `√p` alone is unreachable below
`p ≈ d|log γ|`; this module states the reachable bound.

## The `Cgap`-explicit constant

The produced constant is `C₀ (1 + C_gap)`, LINEAR in the Step-3 gap constant
`C_gap` of `EthmB`'s second summand, with `C₀ = C₀(d, c⋆)` independent of it.
Keeping `C_gap` a free parameter rather than fixing it here is the honest
reading: the source's `C` in `C γ⁵` is pinned by Step 3, not by Step 1, and
(the Step-3 rescaling of the witness) then costs exactly one more factor,
absorbed by `lintegral_rpow_const_mul_le`.

## The conditional set (exactly one edge)

`hY` — the Markov/`Γ₁` moment `𝔼[(3^{(1-α)X_m(α)})^{2p}] ≤ 2^{2p}` of the
Theorem-C minimal-scale factor, transcribed as a named hypothesis at the single
exponent it is consumed at.  Theorem C is a declared dependency of the Step 1
(the moment bound).  NOTHING else is assumed.
-/

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

/-! ## 1. Elementary square-root facts -/

theorem sqrt_max_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (max a b) ≤ Real.sqrt a + Real.sqrt b := by
  have e : (Real.sqrt a + Real.sqrt b) ^ (2 : ℕ) =
      Real.sqrt a ^ (2 : ℕ) + 2 * (Real.sqrt a * Real.sqrt b) + Real.sqrt b ^ (2 : ℕ) := by
    ring
  rw [Real.sq_sqrt ha, Real.sq_sqrt hb] at e
  have hcross : (0 : ℝ) ≤ 2 * (Real.sqrt a * Real.sqrt b) := by positivity
  have hmax : max a b ≤ a + b := max_le (by linarith only [hb]) (by linarith only [ha])
  have hsum : max a b ≤ (Real.sqrt a + Real.sqrt b) ^ (2 : ℕ) := by
    linarith only [e, hcross, hmax]
  calc Real.sqrt (max a b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ (2 : ℕ)) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq (by positivity)

theorem sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num)]

theorem sqrt_le_one_of_le_one {x : ℝ} (h : x ≤ 1) : Real.sqrt x ≤ 1 := by
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_one] at this

/-! ## 2. The purely algebraic collapse -/

/-- **The Step-1 numeric collapse**, over abstract reals.

`W` is `√q`, `S` is `√p + √|log γ|`, `G` is `√γ`, `L` is `|log γ|`, `A` the
anchor's factor constant and `D = 2 + √(8d)` the `√max` loss.  Nothing
`γ`-dependent is hidden: every hypothesis is displayed. -/
theorem display_collapse {A D L S G W gam Cgap C0 : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hL : 4 ≤ L) (hS : 3 ≤ S) (hG : 0 ≤ G) (hW : 0 ≤ W)
    (hCgap : 0 ≤ Cgap)
    (hWDS : W ≤ D * S) (hSG : S * G ≤ 2) (hgam5 : gam ^ (5 : ℕ) ≤ G)
    (h1 : 2 * A * D * (1 + 2 * A * D) ≤ C0)
    (h2 : 1 + 4 * A ^ (2 : ℕ) * D ^ (2 : ℕ) ≤ C0) :
    L * (2 * (A * L * W * G * (1 + A * W * G))) +
        Cgap * gam ^ (5 : ℕ) * (1 + (A * L * W * G) ^ (2 : ℕ)) ≤
      C0 * (1 + Cgap) * S * G * L ^ (2 : ℕ) := by
  have hL0 : (0 : ℝ) ≤ L := by linarith only [hL]
  have hS0 : (0 : ℝ) ≤ S := by linarith only [hS]
  have hL2 : (16 : ℝ) ≤ L ^ (2 : ℕ) := by
    calc (16 : ℝ) = 4 ^ (2 : ℕ) := by norm_num
      _ ≤ L ^ (2 : ℕ) := pow_le_pow_left₀ (by norm_num) hL 2
  have hT0 : (0 : ℝ) ≤ L ^ (2 : ℕ) * S * G := by positivity
  /- `W G ≤ D (S G) ≤ 2 D` -/
  have hWG : W * G ≤ D * (S * G) := by
    have hstep : W * G ≤ (D * S) * G := mul_le_mul_of_nonneg_right hWDS hG
    calc W * G ≤ (D * S) * G := hstep
      _ = D * (S * G) := by ring
  have hWG2D : W * G ≤ 2 * D := by
    have hstep : D * (S * G) ≤ D * 2 := mul_le_mul_of_nonneg_left hSG hD
    calc W * G ≤ D * (S * G) := hWG
      _ ≤ D * 2 := hstep
      _ = 2 * D := by ring
  have hWG0 : (0 : ℝ) ≤ W * G := mul_nonneg hW hG
  /- ### the first summa -/
  have hbr : 1 + A * (W * G) ≤ 1 + 2 * A * D := by
    have h := mul_le_mul_of_nonneg_left hWG2D hA
    linarith only [h]
  have hbr0 : (0 : ℝ) ≤ 1 + A * (W * G) := by positivity
  have hfac0 : (0 : ℝ) ≤ 2 * A * L ^ (2 : ℕ) := by positivity
  have hlhs1 : 2 * A * L ^ (2 : ℕ) * (W * G) ≤ 2 * A * L ^ (2 : ℕ) * (D * (S * G)) :=
    mul_le_mul_of_nonneg_left hWG hfac0
  have hrhs0 : (0 : ℝ) ≤ 2 * A * L ^ (2 : ℕ) * (D * (S * G)) := by positivity
  have hterm1 : L * (2 * (A * L * W * G * (1 + A * W * G))) ≤ C0 * (L ^ (2 : ℕ) * S * G) := by
    have hstep : 2 * A * L ^ (2 : ℕ) * (W * G) * (1 + A * (W * G)) ≤
        2 * A * L ^ (2 : ℕ) * (D * (S * G)) * (1 + 2 * A * D) :=
      mul_le_mul hlhs1 hbr hbr0 hrhs0
    have he1 : L * (2 * (A * L * W * G * (1 + A * W * G))) =
        2 * A * L ^ (2 : ℕ) * (W * G) * (1 + A * (W * G)) := by ring
    have he2 : 2 * A * L ^ (2 : ℕ) * (D * (S * G)) * (1 + 2 * A * D) =
        (2 * A * D * (1 + 2 * A * D)) * (L ^ (2 : ℕ) * S * G) := by ring
    have hconst : (2 * A * D * (1 + 2 * A * D)) * (L ^ (2 : ℕ) * S * G) ≤
        C0 * (L ^ (2 : ℕ) * S * G) := mul_le_mul_of_nonneg_right h1 hT0
    rw [he1]
    calc 2 * A * L ^ (2 : ℕ) * (W * G) * (1 + A * (W * G))
        ≤ 2 * A * L ^ (2 : ℕ) * (D * (S * G)) * (1 + 2 * A * D) := hstep
      _ = (2 * A * D * (1 + 2 * A * D)) * (L ^ (2 : ℕ) * S * G) := he2
      _ ≤ C0 * (L ^ (2 : ℕ) * S * G) := hconst
  /- ### the second summa -/
  have hLS1 : (1 : ℝ) ≤ L ^ (2 : ℕ) * S := by
    have hmul : (1 : ℝ) * 1 ≤ L ^ (2 : ℕ) * S :=
      mul_le_mul (by linarith only [hL2]) (by linarith only [hS]) (by norm_num)
        (by linarith only [hL2])
    linarith only [hmul]
  have hGLS : G ≤ L ^ (2 : ℕ) * S * G := by
    have h := mul_le_mul_of_nonneg_right hLS1 hG
    linarith only [h]
  have hpieceA : Cgap * gam ^ (5 : ℕ) ≤ Cgap * (L ^ (2 : ℕ) * S * G) := by
    have hstep : Cgap * gam ^ (5 : ℕ) ≤ Cgap * G := mul_le_mul_of_nonneg_left hgam5 hCgap
    have hstep2 : Cgap * G ≤ Cgap * (L ^ (2 : ℕ) * S * G) :=
      mul_le_mul_of_nonneg_left hGLS hCgap
    linarith only [hstep, hstep2]
  have hWGsq : (W * G) ^ (2 : ℕ) ≤ (2 * D) ^ (2 : ℕ) := pow_le_pow_left₀ hWG0 hWG2D 2
  have hgamsq : gam ^ (5 : ℕ) * (W * G) ^ (2 : ℕ) ≤ G * (2 * D) ^ (2 : ℕ) :=
    mul_le_mul hgam5 hWGsq (by positivity) hG
  have hpieceB : Cgap * gam ^ (5 : ℕ) * (A * L * W * G) ^ (2 : ℕ) ≤
      (4 * A ^ (2 : ℕ) * D ^ (2 : ℕ) * Cgap) * (L ^ (2 : ℕ) * S * G) := by
    have he : Cgap * gam ^ (5 : ℕ) * (A * L * W * G) ^ (2 : ℕ) =
        (Cgap * (A ^ (2 : ℕ) * L ^ (2 : ℕ))) * (gam ^ (5 : ℕ) * (W * G) ^ (2 : ℕ)) := by
      ring
    have hnn : (0 : ℝ) ≤ Cgap * (A ^ (2 : ℕ) * L ^ (2 : ℕ)) := by positivity
    have hstep : (Cgap * (A ^ (2 : ℕ) * L ^ (2 : ℕ))) *
        (gam ^ (5 : ℕ) * (W * G) ^ (2 : ℕ)) ≤
        (Cgap * (A ^ (2 : ℕ) * L ^ (2 : ℕ))) * (G * (2 * D) ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hgamsq hnn
    have he2 : (Cgap * (A ^ (2 : ℕ) * L ^ (2 : ℕ))) * (G * (2 * D) ^ (2 : ℕ)) =
        (4 * A ^ (2 : ℕ) * D ^ (2 : ℕ) * Cgap) * (L ^ (2 : ℕ) * G) := by ring
    have hSstep : (4 * A ^ (2 : ℕ) * D ^ (2 : ℕ) * Cgap) * (L ^ (2 : ℕ) * G) ≤
        (4 * A ^ (2 : ℕ) * D ^ (2 : ℕ) * Cgap) * (L ^ (2 : ℕ) * S * G) := by
      have hfac : (0 : ℝ) ≤ 4 * A ^ (2 : ℕ) * D ^ (2 : ℕ) * Cgap := by positivity
      have hinner : L ^ (2 : ℕ) * G ≤ L ^ (2 : ℕ) * S * G := by
        have h1S : (1 : ℝ) ≤ S := by linarith only [hS]
        have hb : L ^ (2 : ℕ) * G * 1 ≤ L ^ (2 : ℕ) * G * S :=
          mul_le_mul_of_nonneg_left h1S (by positivity)
        calc L ^ (2 : ℕ) * G = L ^ (2 : ℕ) * G * 1 := by ring
          _ ≤ L ^ (2 : ℕ) * G * S := hb
          _ = L ^ (2 : ℕ) * S * G := by ring
      exact mul_le_mul_of_nonneg_left hinner hfac
    rw [he]
    calc (Cgap * (A ^ (2 : ℕ) * L ^ (2 : ℕ))) * (gam ^ (5 : ℕ) * (W * G) ^ (2 : ℕ))
        ≤ (Cgap * (A ^ (2 : ℕ) * L ^ (2 : ℕ))) * (G * (2 * D) ^ (2 : ℕ)) := hstep
      _ = (4 * A ^ (2 : ℕ) * D ^ (2 : ℕ) * Cgap) * (L ^ (2 : ℕ) * G) := he2
      _ ≤ (4 * A ^ (2 : ℕ) * D ^ (2 : ℕ) * Cgap) * (L ^ (2 : ℕ) * S * G) := hSstep
  have hterm2 : Cgap * gam ^ (5 : ℕ) * (1 + (A * L * W * G) ^ (2 : ℕ)) ≤
      (C0 * Cgap) * (L ^ (2 : ℕ) * S * G) := by
    have he : Cgap * gam ^ (5 : ℕ) * (1 + (A * L * W * G) ^ (2 : ℕ)) =
        Cgap * gam ^ (5 : ℕ) + Cgap * gam ^ (5 : ℕ) * (A * L * W * G) ^ (2 : ℕ) := by ring
    have hsum : Cgap * (L ^ (2 : ℕ) * S * G) +
        (4 * A ^ (2 : ℕ) * D ^ (2 : ℕ) * Cgap) * (L ^ (2 : ℕ) * S * G) ≤
        (C0 * Cgap) * (L ^ (2 : ℕ) * S * G) := by
      have hc : Cgap + 4 * A ^ (2 : ℕ) * D ^ (2 : ℕ) * Cgap ≤ C0 * Cgap := by
        have hstep := mul_le_mul_of_nonneg_right h2 hCgap
        linarith only [hstep]
      have hstep2 := mul_le_mul_of_nonneg_right hc hT0
      linarith only [hstep2]
    rw [he]
    linarith only [hpieceA, hpieceB, hsum]
  have hfinal : C0 * (L ^ (2 : ℕ) * S * G) + (C0 * Cgap) * (L ^ (2 : ℕ) * S * G) =
      C0 * (1 + Cgap) * S * G * L ^ (2 : ℕ) := by ring
  linarith only [hterm1, hterm2, hfinal]

end

end Algsuperdiff.Section4.Provider.Homogenization
