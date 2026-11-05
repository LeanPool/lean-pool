/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementLpLarge

/-!
# IncrementLpSquared

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `e.km.kn.Lp`: the squared `Γ₁` display

`Provider/Stream/IncrementLpLarge.lean` proves `e.kl.bounds.large` at the level
of the `L^p` **mass** and its unsquared `1/p`-th root (a `Γ₂` estimate).  The
printed `e.km.kn.Lp` (ABK26, in the form corrected) is neither of those: it is
the **squared** norm at `Γ₁`,

```
  || k_m - k_n ||^2_{Lbar^p(cu_l)}
      <= C(d) p A + O_{Gamma_1}( C(d) p A 3^{-(d/p)(l-m)} ) ,
      A := min{gamma^{-1}, m-n} 3^{2 gamma m} .
```

This module proves that squaring step on the restricted range `p ≥ 2`.  It is a
provider for the `p = 4` wave consumer, not the exact all-`p` source endpoint;
the frozen all-`p` export remains `draft_sorry`.

## The step

Write `mass` for the cube `L^p` mass and `H`, `T` for the proved head and tail
of `e.kl.bounds.large`, so that `mass ≤ H + T` pointwise and `T =
O_{Γ_{2/p}}(K)` with `K = streamIncrementLpGainScale`.  Since `norm =
mass^{1/p}` by definition,

```
  norm^2 = mass^{2/p} <= (H + T)^{2/p} <= H^{2/p} + T^{2/p} ,
```

the last inequality being subadditivity of `t ↦ t^{2/p}`, valid because `2/p ≤
1`; this is the **only** place `p ≥ 2` is used.  The proved
`isBigOWith_gammaSigma_two_rpow_inv` is the sibling at exponent `r = p`, which
proves at `Γ₂`; `isBigOWith_gammaSigma_one_rpow_two_div` below is the `Γ₁` one.
Both are instances of the same CoarseGraining power rule
(`Orlicz.isBigOWith_gammaSigma_rpow_iff_of_nonneg`, `e.powerofGammasigma`), so
no new CoarseGraining surface is needed.

The mass gain `3^{-(d/2)(l-m)}` becomes, under the `2/p`-th power, exactly the
printed spatial gain

```
  ( 3^{-(d/2)(l-m)} )^{2/p} = 3^{-(d/p)(l-m)} ,
```

which is `streamIncrementLpGainScale_rpow_two_div`.

## The head is a genuine `C(d) p A`; the tail constant is not

`streamIncrementLpMassHead_rpow_two_div` computes the squared head in closed
form:

```
  H^{2/p} = (gammaMomentConst 2 * streamPointScale M n m)^2 * p ,
```

and `streamPointScale_sq` evaluates the square of the pointwise amplitude,

```
  streamPointScale^2
    = (gammaTriangleConst 2 * d^2 * geometricConcentrationConst)^2
        * ( min{gamma^{-1}, m-n} * 3^{2 gamma m} ) .
```

So the resulting deterministic head is **literally** `C(d) p A` with `C(d) =
(gammaMomentConst 2 * gammaTriangleConst 2 * d^2 *
geometricConcentrationConst)^2`, a dimension-only constant: the head of the
corrected display, with its `p` explicit, has the dimension-only head shape
required by the exact all-`p` theorem.

**The tail constant is not.**  The `Γ₁` scale is `streamIncrementLpGainConst d
(2/p)^{2/p} * 3^{-(d/p)(l-m)} * (C(d) p A)`, and `streamIncrementLpGainConst`
carries CoarseGraining's colouring constant
`Book.Ch04.gammaSigmaDescendantsAtScaleConst d 0 (2/p)`, which grows like
`exp(Θ(p²))`; its corrected disclosure on `streamIncrementLpGainConst` is
inherited here.  At general `p` the tail prefactor is therefore **not** a
`C(d)`, and this module does **not** prove the exact all-`p` node.  At the
fixed `p = 4` of the wave consumer the prefactor is a genuine number
(`streamIncrementLpGainConst d 2⁻¹` at `d` fixed), and
`streamIncrementLpNormSq_head_tail_gain_four` is a proved `p = 4` consumer
instance.  It closes neither the frozen node nor any part of it.  A
`C(d)`-uniform tail constant at general `p` remains a separate obligation; the
exact all-`p` frozen theorem is still `draft_sorry`.

## What the Step-3 seam gets

ABK26's Step 3 of `p.bfA.multiscalebound` consumes the quantity `gamma * 3^{-2
gamma ell} * || k_L - k_{n-k-h_k} ||^2_{Lbar^4(cu)}` (inside the Step-3
display).  `streamIncrementLpNormSq_head_tail_gain_four` is exactly the `p = 4`
squared display it needs; the `gamma 3^{-2 gamma ell}` prefactor is the
consumer's, and applying it to the closed-form head `(gammaMomentConst 2 *
streamPointScale M n m)^2 * 4 = C(d) * 4 * min{gamma^{-1}, m-n} * 3^{2 gamma m}`
produces the printed `gamma hsep` first term at `ell = m`.  Nothing below
performs that instantiation.

## Main results

* `isBigOWith_gammaSigma_one_rpow_two_div` — the `Γ_{2/p} → Γ₁` power transfer
  (the `r = p/2` sibling of the proved `r = p` transfer to `Γ₂`).
* `rpow_two_div_le_add_rpow_two_div_of_le_add` — the deterministic half.
* `streamIncrementLpNorm_sq_eq_mass_rpow` — `norm^2 = mass^{2/p}`.
* `streamIncrementLpNormSq_head_tail_of_mass_head_tail` — the abstract
  head/tail packaging at `Γ₁`.
* `streamPointScale_sq` — the pointwise amplitude squared, in closed form: a
  dimension-only constant times `A = min{gamma^{-1}, m-n} 3^{2 gamma m}`.

## References

* ABK26, `e.km.kn.Lp`; `e.kl.bounds.large`; `e.kmn.bounds`;
  `e.powerofGammasigma`; `p.bfA.multiscalebound` Step 3.
* `Provider/Stream/IncrementLpLarge.lean` (the mass form and its unsquared
  root), `Provider/Stream/IncrementLp.lean` (the `Γ₂` transfer at exponent `p`
  and the mass/norm carriers), `Provider/Orlicz/ProductPower.lean` (the
  CoarseGraining power rule).
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The `Γ_{2/p} → Γ₁` power transfer -/

/-- **The `Γ` bookkeeping of the `2/p`-th power.**  A nonnegative
`O_{Γ_{2/p}}(K)` mass-level quantity has an `O_{Γ₁}(K^{2/p})` `2/p`-th power.

Every geometric gain carried by `K` has its exponent multiplied by `2/p`; at
the mass gain `3^{-(d/2)(l-m)}` this is the printed `3^{-(d/p)(l-m)}`. -/
theorem isBigOWith_gammaSigma_one_rpow_two_div {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] {T : Omega → ℝ} {p K : ℝ}
    (hp : 0 < p) (hK : 0 ≤ K) (hT_nonneg : ∀ omega, 0 ≤ T omega)
    (hT : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma (2 / p)) T K) :
    IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma 1)
      (fun omega => T omega ^ (2 / p)) (K ^ (2 / p)) := by
  have hsigma : (0 : ℝ) < 2 / p := by positivity
  have h := (Orlicz.isBigOWith_gammaSigma_rpow_iff_of_nonneg
    (μ := mu) (X := T) (K := K) (σ := 2 / p) (p := 2 / p)
    hsigma hK hT_nonneg).1 hT
  rwa [div_self (ne_of_gt hsigma)] at h

/-- **The deterministic half of the squaring step.**  For `p ≥ 2` the map `t ↦ t^{2/p}` is
subadditive, so a mass bound `mass ≤ H + T` becomes `mass^{2/p} ≤ H^{2/p} + T^{2/p}` with
**no** constant, keeping the deterministic head deterministic.  This is the only use of `2
≤ p`; the `1 ≤ p < 2` route carries a factor `2^{2/p-1}`. -/
theorem rpow_two_div_le_add_rpow_two_div_of_le_add {p H T z : ℝ} (hp : 2 ≤ p)
    (hH : 0 ≤ H) (hT : 0 ≤ T) (hz : 0 ≤ z) (hle : z ≤ H + T) :
    z ^ (2 / p) ≤ H ^ (2 / p) + T ^ (2 / p) := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hp
  have h0 : (0 : ℝ) ≤ 2 / p := by positivity
  have h1 : 2 / p ≤ 1 := (div_le_one hp0).2 hp
  calc z ^ (2 / p) ≤ (H + T) ^ (2 / p) := Real.rpow_le_rpow hz hle h0
    _ ≤ H ^ (2 / p) + T ^ (2 / p) := Real.rpow_add_le_add_rpow hH hT h0 h1

/-- The squared `L^p` norm of a stream increment is the `2/p`-th power of its
`L^p` mass.  This is definitional bookkeeping: `norm = mass^{1/p}`. -/
theorem streamIncrementLpNorm_sq_eq_mass_rpow (p : ℝ) (l n m : ℤ)
    (omega : ShellSeq d) :
    streamIncrementLpNorm p l n m omega ^ 2 =
      streamIncrementLpMass p l n m omega ^ (2 / p) := by
  have hmass := streamIncrementLpMass_nonneg p l n m omega
  have hexp : p⁻¹ * ((2 : ℕ) : ℝ) = 2 / p := by
    have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    rw [hcast]
    ring
  rw [streamIncrementLpNorm,
    ← Real.rpow_natCast (streamIncrementLpMass p l n m omega ^ p⁻¹) 2,
    ← Real.rpow_mul hmass, hexp]

/-! ## The abstract head/tail packaging at `Γ₁` -/

/-- **The shape the squared display consumes.**

Whenever the cube `L^p` mass of a stream increment is dominated by a
*deterministic* head `H` plus a nonnegative tail `T` obeying a `Γ_{2/p}` bound
at scale `K`, the **squared** `L^p` norm is dominated by the deterministic head
`H^{2/p}` plus a tail obeying a `Γ₁` bound at scale `K^{2/p}`.

This is the `Γ₁` analogue of the proved
`streamIncrementLpNorm_head_tail_of_mass_head_tail`, and the exact interface
for `e.kl.bounds.large`: with `H = (C(d)p)^{p/2} A^{p/2}` and `K =
(C(d)p)^{p/2} A^{p/2} 3^{-(d/2)(l-m)}` the conclusion is the corrected
`e.km.kn.Lp`, namely `C(d) p A + O_{Γ₁}(C(d) p A 3^{-(d/p)(l-m)})`. -/
theorem streamIncrementLpNormSq_head_tail_of_mass_head_tail (M : ABKModel d) {p : ℝ}
    (hp : 2 ≤ p) (l n m : ℤ) {H K : ℝ} {T : ShellSeq d → ℝ}
    (hH : 0 ≤ H) (hK : 0 ≤ K) (hT_nonneg : ∀ omega, 0 ≤ T omega)
    (hmass : ∀ omega, streamIncrementLpMass p l n m omega ≤ H + T omega)
    (hT : IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma (2 / p)) T K) :
    (∀ omega : ShellSeq d, 0 ≤ T omega ^ (2 / p)) ∧
      (∀ omega : ShellSeq d,
        streamIncrementLpNorm p l n m omega ^ 2 ≤ H ^ (2 / p) + T omega ^ (2 / p)) ∧
      IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 1)
        (fun omega => T omega ^ (2 / p)) (K ^ (2 / p)) := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hp
  refine ⟨fun omega => Real.rpow_nonneg (hT_nonneg omega) _, fun omega => ?_, ?_⟩
  · rw [streamIncrementLpNorm_sq_eq_mass_rpow]
    exact rpow_two_div_le_add_rpow_two_div_of_le_add hp hH (hT_nonneg omega)
      (streamIncrementLpMass_nonneg p l n m omega) (hmass omega)
  · exact isBigOWith_gammaSigma_one_rpow_two_div hp0 hK hT_nonneg hT

/-! ## The squared head in closed form -/

private theorem sq_min_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min (Real.sqrt a) (Real.sqrt b) ^ 2 = min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (Real.sqrt_le_sqrt h), Real.sq_sqrt ha]
  · rw [min_eq_right h, min_eq_right (Real.sqrt_le_sqrt h), Real.sq_sqrt hb]

/-- **The pointwise amplitude, squared.**  The `Γ₂` amplitude of
`e.k.ell.upscales` squares to a dimension-only constant times the manuscript's
`A = min{gamma^{-1}, m-n} 3^{2 gamma m}`.  The two square roots of
`streamPointScale` recombine into the printed minimum. -/
theorem streamPointScale_sq (M : ABKModel d) {n m : ℤ} (hnm : n < m) :
    streamPointScale M n m ^ 2 =
      (IndependentSums.gammaTriangleConst 2 * (d : ℝ) ^ 2 *
          geometricConcentrationConst) ^ 2 *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) * (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ)))) := by
  have hgamma : (0 : ℝ) ≤ M.gamma⁻¹ := (inv_pos.2 M.shellPrefix.gamma_pos).le
  have hmn : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
    have hlt : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
    linarith
  have hmin := sq_min_sqrt hgamma hmn
  have h3 : ((3 : ℝ) ^ (M.gamma * (m : ℝ))) ^ 2 =
      (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ))) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (M.gamma * (m : ℝ))) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    ring
  calc streamPointScale M n m ^ 2
      = (IndependentSums.gammaTriangleConst 2 * (d : ℝ) ^ 2 *
            geometricConcentrationConst) ^ 2 *
          (min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) ^ 2 *
            ((3 : ℝ) ^ (M.gamma * (m : ℝ))) ^ 2) := by
        rw [streamPointScale]
        ring
    _ = (IndependentSums.gammaTriangleConst 2 * (d : ℝ) ^ 2 *
            geometricConcentrationConst) ^ 2 *
          (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
            (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ)))) := by
        rw [hmin, h3]

end

end Algsuperdiff.Section3.Provider.Stream
