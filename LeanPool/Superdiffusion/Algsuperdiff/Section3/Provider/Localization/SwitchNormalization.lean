/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Localization.ResponseTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Localization.ShomContinuity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.DoubledAdjointEllipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Shaking.LambdaShaking

/-!
# SwitchNormalization

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: the comparator switch `shom_m -> shom_{l-h}` of the localization lemma

The printed display is

```
J(z+cu_l, shom_m^{-1/2}e, shom_m^{1/2}e; a_m) 1_{Q(l,l-h,z)}
  <= shom_m^{-1} shom_{l-h} J(z+cu_l, shom_{l-h}^{-1/2}e, shom_{l-h}^{1/2}e; a_m)
     + 2 shom_m^{-1} shom_{l-h} (shom_m shom_{l-h}^{-1} - 1)^2 shom_{l-h}
         |s_{m,*}^{-1}(z+cu_l)| 1_{Q(l,l-h,z)}
  <= 2 J(z+cu_l, shom_{l-h}^{-1/2}e, shom_{l-h}^{1/2}e; a_m)
     + C min{cgamma^2 (m-l+h)^2, 3^{2 cgamma (m-l+h)}} + C E^4 cgamma^2 |log cgamma|^4 .
```

The **coefficient stays `a_m` on both sides**; only the comparator moves.

## The two corrections implemented

* **The remainder shape.**  The printed remainder is false for large gaps: since `u^2 <= 3^{2u}`
  for `u >= 0`, the printed `min{cgamma^2 Delta^2, 3^{2 cgamma Delta}}` is
  identically `cgamma^2 Delta^2`, whereas the step's own quoted input
  `e.switchtheshoms.betterer.again` carries an **un-cancelled** `3^{cgamma
  Delta}` and `e.shaking.lambda` squares it.  The corrected per-cube remainder,
  delivered by every statement below, is
  ```
  C min{cgamma^2 Delta^2, 1} 3^{2 cgamma Delta}
    + C E^4 cgamma^2 |log cgamma|^4 3^{2 cgamma Delta} ,   Delta = m - l + h .
  ```

* The **honest uniform constant** is delivered here: `2 rho` where `shom_{l-h}
  <= rho shom_m`, i.e. `4` at the manuscript's own `rho = 2` and `8` at the
  `rho = 4` that `l.shom.continuity`'s quarter comparison actually yields (the
  `rho = 4` window comes from the recurrence-stage continuity route, which is
  exactly the second conjunct of the proved
  `shom_continuity`).  The printed proof additionally needs, silently, a
  small-gap hypothesis `|shom_m shom_{l-h}^{-1} - 1| <= 1/3` for itsmanuscrip
  t-literal constant `2`.

## What is here

* `sigmaStarInv_quadForm_le_of_normSq_le_two` — the gate transported to the
  loading ball (the source of the honest factor `2` in every remainder).
* `responseJ_comparator_switch_le` — `e.shaking.lambda` at
  `lam = shom_m shom_{l-h}^{-1}`, `eps`-form, at free comparators.
* `responseJ_comparator_switch_of_gate` — the uniform regime `delta = 1`, the
  honest constant `2 rho`.
* `sigmaStarInv_gate_of_lambdaGate`, `sigmaStarInv_transpose_gate_of_lambdaGate`
  — the printed `lambda_{s,2}` gate carrier, primal and adjoint.
* `responseJ_shom_switch_of_defect` — the switch at the **corrected**
  remainder.
* `shom_switch` — the display at the running comparators `shom_m`,
  `shom_{l-h}`, consuming `l.shom.continuity`.
* `breakdownLeg{A,B}_le_of_switch` — the *interface* against the proved
  transport, at free leading constant `Kc`, deep bound `c0` and remainder
  `rem`.
* `breakdownLeg{A,B}_le_of_shom_switch` — **the actual composition**:
  `shom_switch` fed into that interface at `sigma := shom_m`, `sigmaDeep:=
  shom_n`.

## The loading carrier: `vecNormSq v <= 2`, not `|e| = 1`

Every statement below is proved for **every** `v` with `vecNormSq v <= 2`.  The
step is pointwise in the loading; only its additive `sigma_*^{-1}` remainder
doubles, which is why every remainder below carries the honest factor `2` in
front of the gate level `Cev` (the printed display, stated at `|e| = 1`,
carries `1`).

## The `lambda`-gate is a conditional input
 ABK26 justifies the last inequality by the chain

```
|s_{m,*}^{-1}(z+cu_l)| 1_Q <= lambda_{1/8,2}^{-1}(z+cu_l; a_m) 1_Q
                           <= 2 lambda_{1/8,2}^{-1}(z+cu_l; a_{l-h}) 1_Q
                           <= C shom_{l-h}^{-1} ,
```

whose middle step is `l.lambda.sensitivity` on the good event `Q(l,l-h,z)` and
whose last step is the ellipticity clause of `e.good.local.events`.  It enters
every statement below as a named hypothesis in exactly the shape those
producers deliver, namely the *clamped* form

```
hgate : shom_{l-h} * (lambdaSq (z+cu_l) (1/8) (.finite 2) a_m)^{-1} <= Cev
```

(the `hgate` binder of `sigmaStarInv_gate_of_lambdaGate`), or, one step more
primitive and carrier-free,

```
hgate : shom_{l-h} * matrixNorm (sigmaStarInvCoarse U A) <= Cev
```

(`responseJ_comparator_switch_of_gate`).  Nothing in this module asserts that
either holds.

So the gate above is exactly `shom_{l-h} lambda_{1/8,2}^{-1}(z+cu_l; a_m) <=
Cev`, the last line of the printed chain, in the repository's own spelling.

## The cross-unit remainder shape, and where the bridge lives

| | `shom_switch` (here) | `AggregationRemainder.switchRemainder` |
|---|---|---|
| min order | `min 1 (cgamma^2 Delta^2)` | `min (cgamma^2 (j+h)^2) 1` |
| rpow exponent | `3 ^ (2 * (cgamma * Delta))` | `3 ^ (2 * cgamma * (j+h))` |
| structure | distributed (two summands) | factored (one product) |
| index | `Delta = (m:R) - (n:R)`, `m n : Z` | `(j:R) + (h:R)`, `j h : N` |

The min order here follows the proved `shom_continuity` display
(`ShomContinuity.lean`); the sibling's follows the manuscript.  The two shapes
are **equal, not merely comparable** — the whole glue is `min_comm`, one `ring`
normalization of the rpow exponent, and `push_cast` for the `Z -> R` reindex at
`n := m - j - h`.  The assembly must **consume** it, not re-derive it.  Nothing
on this side of the seam is restated for it: `shom_switch`'s statement is
unchanged.

## The scale gate on `m0` (-bin statement change)

The landmark premise carried by every public below is `mStarStar M < m0`,
**not** the printed `m0 in (mstar, infty) cap Z`.  Nothing else moved: the
premise is forwarded verbatim to `Provider.Localization.shom_continuity`, no
proof step here consumes it, and no frozen statement changes --
`Algsuperdiff.Frozen.Section3. diffusivity_asymptotics` keeps the printed
`mStar M < m0` and reaches the weaker-gated chain a fortiori through
`Provider.Scales.mStarStar_le_mStar`.

## References

* ABK26: the switch display; the `lambda`-gate chain, quoted as a hypothesis
  here; `e.shaking.lambda`; `e.good.local.events`.
-/

namespace Algsuperdiff.Section3.Provider.Localization

-- `_root_` is load-bearing: `Algsuperdiff.Section3.Provider.Homogenization` is a
-- live sibling namespace, so a bare `open Homogenization` resolves to it once any
-- `Provider.Homogenization` module enters this file's import closure.
open _root_.HCPolySupport
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section24.Sensitivity.Provider.Shaking

noncomputable section

variable {d : ℕ}

/-! ## 1. Real-variable arithmetic for the corrected remainder

Three elementary facts, isolated so that no numeric tactic is ever run on a
`Real.rpow` or a `Real.log` atom. -/

/-- `min{1, a+b}^2 <= 2 min{1, a^2} + 2 b^2` for nonnegative `a, b`. -/
private theorem min_one_add_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min 1 (a + b) ^ 2 ≤ 2 * min 1 (a ^ 2) + 2 * b ^ 2 := by
  have hX0 : (0 : ℝ) ≤ min 1 (a + b) := le_min (by norm_num) (by linarith)
  have hX1 : min 1 (a + b) ≤ 1 := min_le_left _ _
  have hXab : min 1 (a + b) ≤ a + b := min_le_right _ _
  have hsq1 : min 1 (a + b) ^ 2 ≤ (a + b) ^ 2 := pow_le_pow_left₀ hX0 hXab 2
  have hsq2 : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  rcases le_or_gt (a ^ 2) 1 with h | h
  · rw [min_eq_right h]
    linarith
  · rw [min_eq_left h.le]
    nlinarith [hX0, hX1, sq_nonneg b]

/-- `3^t * 3^t = 3^{2t}` at real exponents. -/
private theorem rpow_three_double (t : ℝ) :
    (3 : ℝ) ^ t * (3 : ℝ) ^ t = (3 : ℝ) ^ (2 * t) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-- **The squared `shom`-defect, in the corrected shape.**  A nonnegative
quantity bounded by `C min{1, a+b} 3^t` has square bounded by

```
2 C^2 min{1, a^2} 3^{2t} + 2 C^2 b^2 3^{2t} ,
```

which at `a = cgamma Delta`, `b = E^2 cgamma |log cgamma|^2`, `t = cgamma
Delta` is exactly the remainder. -/
private theorem sq_defect_le_corrected {C a b t K : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hK0 : 0 ≤ K)
    (hK : K ≤ C * min 1 (a + b) * (3 : ℝ) ^ t) :
    K ^ 2 ≤ 2 * C ^ 2 * min 1 (a ^ 2) * (3 : ℝ) ^ (2 * t)
      + 2 * C ^ 2 * b ^ 2 * (3 : ℝ) ^ (2 * t) := by
  have ht0 : (0 : ℝ) < (3 : ℝ) ^ t := Real.rpow_pos_of_pos (by norm_num) t
  have hX0 : (0 : ℝ) ≤ min 1 (a + b) := le_min (by norm_num) (by linarith)
  have hrhs0 : 0 ≤ C * min 1 (a + b) * (3 : ℝ) ^ t := by positivity
  have hsq : K ^ 2 ≤ (C * min 1 (a + b) * (3 : ℝ) ^ t) ^ 2 := by
    nlinarith [hK, hK0, hrhs0]
  have hexp : (C * min 1 (a + b) * (3 : ℝ) ^ t) ^ 2
      = C ^ 2 * min 1 (a + b) ^ 2 * ((3 : ℝ) ^ t * (3 : ℝ) ^ t) := by ring
  rw [hexp, rpow_three_double t] at hsq
  have hstep : C ^ 2 * min 1 (a + b) ^ 2 * (3 : ℝ) ^ (2 * t)
      ≤ C ^ 2 * (2 * min 1 (a ^ 2) + 2 * b ^ 2) * (3 : ℝ) ^ (2 * t) := by
    have h2 : (0 : ℝ) ≤ C ^ 2 * (3 : ℝ) ^ (2 * t) := by positivity
    nlinarith [min_one_add_sq_le ha hb, h2]
  nlinarith [hsq, hstep]

/-! ## 2. The `sigma_*^{-1}` quadratic form on the loading ball -/

/-- The coarse `sigma_*^{-1}` quadratic form is nonnegative.

The earlier route through `responseJ_nonneg` and
`responseJ_zero_q_eq_sigmaStarInvCoarse` was an independent re-derivation and
is withdrawn; the same one-line consumption is already used in-repo at
`sq_vecNormSq_le_vecDot_bCoarse_mul_vecDot_sigmaStarInvCoarse` in
`Provider/ErrorComparison/ToLambdasUpper.lean` and
`vecDot_sigmaCoarse_le_two_mul_add` in `EllipticityOrdered.lean`. -/
private theorem sigmaStarInv_quadForm_nonneg (U : Book.Ch02.Domain d)
    (A : Book.Ch02.CoeffOn U) (v : Vec d) :
    0 ≤ vecDot v (matVecMul (Book.Ch02.sigmaStarInvCoarse U A) v) := by
  simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using
    (Book.Ch02.sigmaStarInvCoarse_posDef U A).posSemidef.dotProduct_mulVec_nonneg v

/-- The quadratic form at a square-root-scaled loading:
`(sqrt c v) . M (sqrt c v) = c (v . M v)` for `c >= 0`. -/
private theorem quadForm_sqrt_smul (A : Mat d) {c : ℝ} (hc : 0 ≤ c) (v : Vec d) :
    vecDot (Real.sqrt c • v) (matVecMul A (Real.sqrt c • v))
      = c * vecDot v (matVecMul A v) := by
  rw [matVecMul_smul, vecDot_smul_left, vecDot_smul_right, ← mul_assoc,
    Real.mul_self_sqrt hc]

/-- A positive-semidefinite quadratic form is dominated by the operator norm:
`v . M v <= |M| |v|^2`.

The earlier `le_abs_self` detour through the `abs_` sibling is withdrawn; the
semidefiniteness hypothesis is free at the only call site, where `A` is
`sigmaStarInvCoarse`. -/
private theorem quadForm_le_matrixNorm_mul {A : Mat d} (hA : A.PosSemidef)
    (v : Vec d) :
    vecDot v (matVecMul A v) ≤ Book.Ch02.matrixNorm A * vecNormSq v := by
  rw [Book.Ch02.matrixNorm_eq_matrixOperatorNorm]
  exact Book.Ch02.vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq_of_posSemidef
    hA v

/-- **The gate, transported to the loading ball.**  If `sn |s_*^{-1}(U;A)|` is
clamped by `Cev`, then `sn` times the `s_*^{-1}` quadratic form at *every*
loading of squared length at most `2` is clamped by `2 Cev`.

The factor `2` is the entire cost of the `vecNormSq v <= 2` carrier that (ii)
makes binding; the printed display, stated at `|e| = 1`, carries `1` here. -/
theorem sigmaStarInv_quadForm_le_of_normSq_le_two (U : Book.Ch02.Domain d)
    (A : Book.Ch02.CoeffOn U) {sn Cev : ℝ} (hsn : 0 ≤ sn)
    (hgate : sn * Book.Ch02.matrixNorm (Book.Ch02.sigmaStarInvCoarse U A) ≤ Cev)
    {v : Vec d} (hv : vecNormSq v ≤ 2) :
    sn * vecDot v (matVecMul (Book.Ch02.sigmaStarInvCoarse U A) v) ≤ 2 * Cev := by
  have hnorm0 : (0 : ℝ) ≤ Book.Ch02.matrixNorm (Book.Ch02.sigmaStarInvCoarse U A) :=
    Book.Ch02.matrixNorm_nonneg _
  have hquad := quadForm_le_matrixNorm_mul
    (Book.Ch02.sigmaStarInvCoarse_posDef U A).posSemidef v
  have hball :
      Book.Ch02.matrixNorm (Book.Ch02.sigmaStarInvCoarse U A) * vecNormSq v ≤
        2 * Book.Ch02.matrixNorm (Book.Ch02.sigmaStarInvCoarse U A) := by
    nlinarith [hnorm0, hv]
  nlinarith [hquad, hball, hsn, hgate]

/-- The gate level is automatically nonnegative: it dominates a nonnegative
quantity. -/
private theorem gate_nonneg (U : Book.Ch02.Domain d) (A : Book.Ch02.CoeffOn U)
    {sn Cev : ℝ} (hsn : 0 ≤ sn)
    (hgate : sn * Book.Ch02.matrixNorm (Book.Ch02.sigmaStarInvCoarse U A) ≤ Cev) :
    0 ≤ Cev := by
  have hnorm0 : (0 : ℝ) ≤ Book.Ch02.matrixNorm (Book.Ch02.sigmaStarInvCoarse U A) :=
    Book.Ch02.matrixNorm_nonneg _
  nlinarith [hsn, hnorm0, hgate]

/-! ## 3. `e.shaking.lambda` at `lam = shom_m shom_{l-h}^{-1}`

The pure gauge algebra, at a bare `Domain`/`CoeffOn` pair so that the *same*
statement serves the primal leg and the transposed leg of the breakdown display.
The comparators are free positive scalars; no `shom`, no `nu`, no floor. -/

/-- **The comparator switch, `eps`-form.**  For positive comparators `sm`
(the working one, `shom_m`) and `sn` (the deep one, `shom_{l-h}`) and any Young
parameter `delta > 0`,

```
J(U, sm^{-1/2}v, sm^{1/2}v; A)
  <= (1+delta) (sn sm^{-1}) J(U, sn^{-1/2}v, sn^{1/2}v; A)
     + ((1+delta^{-1})/2) (sn sm^{-1}) (sm sn^{-1} - 1)^2 (sn (v . s_*^{-1} v)) .
```

This is `e.shaking.lambda` at `lam = sm sn^{-1}` and base loading `(sn^{-1/2}v,
sn^{1/2}v)`, in the pre-optimization form of the printed proof.  It is an
identity-level rearrangement of the proved
`Shaking.responseJ_shaking_lambda_normalizedLoading_epsilon`: nothing is
estimated, so the printed `J`-coefficient `lam^{-1}` is visibly the `delta ->
0` limit, and visibly unattainable. -/
theorem responseJ_comparator_switch_le (U : Book.Ch02.Domain d)
    (A : Book.Ch02.CoeffOn U) {sm sn delta : ℝ} (hsm : 0 < sm) (hsn : 0 < sn)
    (hdelta : 0 < delta) (v : Vec d) :
    Book.Ch02.responseJ U A ((Real.sqrt sm)⁻¹ • v) (Real.sqrt sm • v) ≤
      (1 + delta) * (sn * sm⁻¹) *
          Book.Ch02.responseJ U A ((Real.sqrt sn)⁻¹ • v) (Real.sqrt sn • v) +
        (1 + delta⁻¹) / 2 * (sn * sm⁻¹) * (sm * sn⁻¹ - 1) ^ 2 *
          (sn * vecDot v (matVecMul (Book.Ch02.sigmaStarInvCoarse U A) v)) := by
  have hmu : (0 : ℝ) < sm * sn⁻¹ := mul_pos hsm (inv_pos.mpr hsn)
  have hmusn : sm * sn⁻¹ * sn = sm := by field_simp
  have h := responseJ_shaking_lambda_normalizedLoading_epsilon U A
    (mu := sm * sn⁻¹) (sigma0 := sn) hmu hdelta v
  rw [hmusn, quadForm_sqrt_smul _ hsn.le] at h
  refine h.trans_eq ?_
  have hd : delta ≠ 0 := ne_of_gt hdelta
  have hm : sm ≠ 0 := ne_of_gt hsm
  have hn : sn ≠ 0 := ne_of_gt hsn
  field_simp
  ring

/-- **The comparator switch, uniform regime** (`delta = 1`), with the
`sigma_*^{-1}` remainder clamped by the disclosed gate.

```
J(U, sm^{-1/2}v, sm^{1/2}v; A)
  <= 2 rho J(U, sn^{-1/2}v, sn^{1/2}v; A) + 2 rho K^2 Cev
```

whenever `sn sm^{-1} <= rho`, `|sm sn^{-1} - 1| <= K` and
`sn |s_*^{-1}(U;A)| <= Cev`, for every `v` with `vecNormSq v <= 2`.

The printed `2` is *not* obtainable from `e.shaking.lambda` without a smallness
restriction on `|sm sn^{-1} - 1|`.

The two `2`s are different: on the `J`-term it is the Young factor `1 + delta`
at `delta = 1`; on the remainder it is the loading-ball factor of
`sigmaStarInv_quadForm_le_of_normSq_le_two` (the Young remainder coefficient
`(1 + delta^{-1})/2` is exactly `1` at `delta = 1`).

`hgate` is a **conditional A obligation**, not a source premise of this module:
it is the `lambda`-gate step, whose producers are
`Provider/BadEvents/GoodLocalEvents.lean` and
`Provider/BadEvents/LambdaTransfer.lean`. -/
theorem responseJ_comparator_switch_of_gate (U : Book.Ch02.Domain d)
    (A : Book.Ch02.CoeffOn U) {sm sn rho K Cev : ℝ} (hsm : 0 < sm) (hsn : 0 < sn)
    (hrho : sn * sm⁻¹ ≤ rho) (hK : |sm * sn⁻¹ - 1| ≤ K)
    (hgate : sn * Book.Ch02.matrixNorm (Book.Ch02.sigmaStarInvCoarse U A) ≤ Cev)
    {v : Vec d} (hv : vecNormSq v ≤ 2) :
    Book.Ch02.responseJ U A ((Real.sqrt sm)⁻¹ • v) (Real.sqrt sm • v) ≤
      2 * rho *
          Book.Ch02.responseJ U A ((Real.sqrt sn)⁻¹ • v) (Real.sqrt sn • v) +
        2 * rho * K ^ 2 * Cev := by
  have hcore := responseJ_comparator_switch_le U A hsm hsn zero_lt_one v
  have hr0 : (0 : ℝ) < sn * sm⁻¹ := mul_pos hsn (inv_pos.mpr hsm)
  have hrho0 : (0 : ℝ) ≤ rho := le_trans hr0.le hrho
  have hK0 : (0 : ℝ) ≤ K := le_trans (abs_nonneg _) hK
  have hKsq : (sm * sn⁻¹ - 1) ^ 2 ≤ K ^ 2 := by
    calc (sm * sn⁻¹ - 1) ^ 2 = |sm * sn⁻¹ - 1| ^ 2 := (sq_abs _).symm
      _ ≤ K ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hK 2
  have hJ0 : (0 : ℝ) ≤
      Book.Ch02.responseJ U A ((Real.sqrt sn)⁻¹ • v) (Real.sqrt sn • v) :=
    Book.Ch02.responseJ_nonneg _ _ _ _
  have hW0 : (0 : ℝ) ≤
      sn * vecDot v (matVecMul (Book.Ch02.sigmaStarInvCoarse U A) v) :=
    mul_nonneg hsn.le (sigmaStarInv_quadForm_nonneg U A v)
  have hW := sigmaStarInv_quadForm_le_of_normSq_le_two U A hsn.le hgate hv
  -- the `J`-leg
  have hleg : (1 + 1 : ℝ) * (sn * sm⁻¹) *
      Book.Ch02.responseJ U A ((Real.sqrt sn)⁻¹ • v) (Real.sqrt sn • v) ≤
      2 * rho *
        Book.Ch02.responseJ U A ((Real.sqrt sn)⁻¹ • v) (Real.sqrt sn • v) := by
    have : (1 + 1 : ℝ) * (sn * sm⁻¹) ≤ 2 * rho := by linarith
    exact mul_le_mul_of_nonneg_right this hJ0
  -- the remainder leg
  have hprod : (sn * sm⁻¹) * (sm * sn⁻¹ - 1) ^ 2 ≤ rho * K ^ 2 :=
    mul_le_mul hrho hKsq (sq_nonneg _) hrho0
  have hrem : (sn * sm⁻¹) * (sm * sn⁻¹ - 1) ^ 2 *
      (sn * vecDot v (matVecMul (Book.Ch02.sigmaStarInvCoarse U A) v)) ≤
      rho * K ^ 2 * (2 * Cev) :=
    mul_le_mul hprod hW hW0 (mul_nonneg hrho0 (sq_nonneg _))
  have hcoef : (1 + (1 : ℝ)⁻¹) / 2 = 1 := by norm_num
  rw [hcoef, one_mul] at hcore
  linarith [hcore, hleg, hrem]

/-! ## 4. The gate at the printed `lambda_{s,2}` carrier
 ABK26 clamps `|s_{m,*}^{-1}(z+cu_l)|` through `lambda_{1/8,2}^{-1}(z+cu_l;
 a_m)`.
The two bridges below convert a gate stated at that carrier into the matrix-norm
gate the switch consumes, on the primal and on the transposed representative.
The exponents `s, q` are free, so the `lambda`-gate step may discharge at the
printed `(1/8, 2)` or at any other admissible pair. -/

/-- **From the printed `lambda`-gate to the switch's gate**, primal leg.
CoarseGraining's one-cube ordering `e.ellipticities.monotone.ordered`
(`oneCube_sigmaStarInv_le_lambdaSq_finite_inv`) is exactly the printed step
`|s_{m,*}^{-1}(z+cu_l)| <= lambda_{s,2}^{-1}(z+cu_l; a_m)`. -/
theorem sigmaStarInv_gate_of_lambdaGate [NeZero d] (Q : TriadicCube d)
    (F : Book.Ch02.TriadicCoeffFamily d) {sn Cev s q : ℝ} (hsn : 0 ≤ sn)
    (hs : 0 < s) (hq : 1 ≤ q)
    (hgate : sn * (Book.Ch02.lambdaSq Q s (.finite q) F)⁻¹ ≤ Cev) :
    sn * Book.Ch02.matrixNorm
        (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q)) ≤
      Cev := by
  have hone := Book.Ch02.oneCube_sigmaStarInv_le_lambdaSq_finite_inv Q F hs hq
  have hrw : Book.Ch02.coarseSigmaStarInvMatrixNorm Q F =
      Book.Ch02.matrixNorm
        (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q)) := rfl
  rw [hrw] at hone
  exact le_trans (mul_le_mul_of_nonneg_left hone hsn) hgate

/-- **From the printed `lambda`-gate to the switch's gate**, adjoint leg.  Both
sides of the gate are adjoint-invariant: `sigma_*^{-1}(U; a^t) =
sigma_*^{-1}(U; a)` and `lambda_{s,q}(Q; a^t) = lambda_{s,q}(Q; a)` (proved
publics of `Provider/CoarseEllipticity/DoubledAdjointEllipticity.lean`), so the
*same* printed gate serves `breakdownLegB`. -/
theorem sigmaStarInv_transpose_gate_of_lambdaGate [NeZero d] (Q : TriadicCube d)
    (F : Book.Ch02.TriadicCoeffFamily d) {sn Cev s q : ℝ} (hsn : 0 ≤ sn)
    (hs : 0 < s) (hq : 1 ≤ q)
    (hgate : sn * (Book.Ch02.lambdaSq Q s (.finite q) F)⁻¹ ≤ Cev) :
    sn * Book.Ch02.matrixNorm
        (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q)
          (F.coeffOn Q).transpose) ≤ Cev := by
  rw [CoarseEllipticity.sigmaStarInvCoarse_transpose]
  exact sigmaStarInv_gate_of_lambdaGate Q F hsn hs hq hgate

/-! ## 5. The corrected remainder

Threading the squared `shom`-defect through the switch algebra of Section 3. -/

/-- **The per-cube switch at the corrected remainder.**

Given the `e.shom.m.vs.shom.n` defect display in its proved shape

```
|sm sn^{-1} - 1| <= Cd min{1, a + b} 3^t ,
```

the uniform switch at `rho = 4` (the `shom_continuity` ratio cap) yields, for
every `v` with `vecNormSq v <= 2`,

```
J(U, sm^{-1/2}v, sm^{1/2}v; A)
  <= 8 J(U, sn^{-1/2}v, sn^{1/2}v; A)
     + 16 Cd^2 Cev min{1, a^2} 3^{2t}
     + 16 Cd^2 Cev b^2 3^{2t} .
```

At `a = t = cgamma (m - l + h)` and `b = E^2 cgamma |log cgamma|^2` this is
**exactly** the corrected remainder: `C min{cgamma^2 Delta^2, 1} 3^{2 cgamma
Delta} +^4 cgamma^2 |log cgamma|^4 3^{2 cgamma Delta}`, with `b^2 = E^4
cgamma^2 |log cgamma|^4` and the `3^{2 cgamma Delta}` un-cancelled on both
summands.

Constant accounting, term by term:

* the remainder prefactor `16 = (rho = 4) * (2 from vecNormSq v <= 2) *
  (2 from the squared-defect split `min_one_add_sq_le`)`, the Young remainder
  coefficient `(1 + delta^{-1})/2` being exactly `1` at `delta = 1`.

Every constant is explicit; `Cd` is whatever the defect display supplies
(dimension-only, when that display is `shom_continuity`'s). -/
theorem responseJ_shom_switch_of_defect (U : Book.Ch02.Domain d)
    (A : Book.Ch02.CoeffOn U) {sm sn Cd a b t Cev : ℝ} (hsm : 0 < sm)
    (hsn : 0 < sn) (hrho : sn * sm⁻¹ ≤ 4) (hCd : 0 ≤ Cd) (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hdefect : |sm * sn⁻¹ - 1| ≤ Cd * min 1 (a + b) * (3 : ℝ) ^ t)
    (hgate : sn * Book.Ch02.matrixNorm (Book.Ch02.sigmaStarInvCoarse U A) ≤ Cev)
    {v : Vec d} (hv : vecNormSq v ≤ 2) :
    Book.Ch02.responseJ U A ((Real.sqrt sm)⁻¹ • v) (Real.sqrt sm • v) ≤
      8 * Book.Ch02.responseJ U A ((Real.sqrt sn)⁻¹ • v) (Real.sqrt sn • v) +
        16 * Cd ^ 2 * Cev * min 1 (a ^ 2) * (3 : ℝ) ^ (2 * t) +
        16 * Cd ^ 2 * Cev * b ^ 2 * (3 : ℝ) ^ (2 * t) := by
  have hCev0 : (0 : ℝ) ≤ Cev := gate_nonneg U A hsn.le hgate
  have hK0 : (0 : ℝ) ≤ Cd * min 1 (a + b) * (3 : ℝ) ^ t := by
    have hX0 : (0 : ℝ) ≤ min 1 (a + b) := le_min (by norm_num) (by linarith)
    have ht0 : (0 : ℝ) < (3 : ℝ) ^ t := Real.rpow_pos_of_pos (by norm_num) t
    positivity
  have hswitch := responseJ_comparator_switch_of_gate U A hsm hsn hrho hdefect
    hgate hv
  have hsq := sq_defect_le_corrected hCd ha hb hK0 (le_refl _)
  have hrem : 2 * (4 : ℝ) * (Cd * min 1 (a + b) * (3 : ℝ) ^ t) ^ 2 * Cev ≤
      16 * Cd ^ 2 * Cev * min 1 (a ^ 2) * (3 : ℝ) ^ (2 * t) +
        16 * Cd ^ 2 * Cev * b ^ 2 * (3 : ℝ) ^ (2 * t) := by
    nlinarith [hsq, hCev0]
  linarith [hswitch, hrem]

/-! ## 6. The `shom` instance: consuming `l.shom.continuity`

Of the three `shom` inputs the (i) consumer probe exhibited at `n := l - h`,
the switch step itself consumes exactly two: the second conjunct of the proved
`shom_continuity` (the ratio cap `4`, the honest reading of the printed
`shom_m^{-1} shom_{l-h} <= 2`) and the fifth (the `e.shom.m.vs.shom.n` defect
display).  The third — the fourth conjunct, the short-range cap `12` at `cgamma
(m-n) <= 1` — is **not** used here; it belongs to the `lambda`-gate step,
whose printed clamp runs through the good event's `shom_{l-h-1}` and must
return to `shom_{l-h}`. -/

/-- **The switch-normalization step at the running comparators**, at the
corrected remainder and the honest constant.

On the `l.shom.continuity` premise list, for every pair of scales `n <= m <= m0`
(the intended instance is `n := l - h`, so that `m - n = m - l + h = Delta`),
every domain/coefficient pair, every gate level `Cev` clamping the
`sigma_*^{-1}` size at the *deep* comparator, and **every** loading `v` with
`vecNormSq v <= 2`:

```
J(U, shom_m^{-1/2}v, shom_m^{1/2}v; A)
  <= 8 J(U, shom_n^{-1/2}v, shom_n^{1/2}v; A)
     + Cs Cev min{1, cgamma^2 (m-n)^2} 3^{2 cgamma (m-n)}
     + Cs Cev E^4 cgamma^2 |log cgamma|^4 3^{2 cgamma (m-n)} .
```

`hgate` is the `lambda`-gate conditional input; it is stated at the
*deep* comparator `shom_n` because that is the scale the printed clamp
`lambda_{1/8,2}^{-1}(z+cu_l; a_m) <= C shom_{l-h}^{-1}` produces.  Use
`sigmaStarInv_gate_of_lambdaGate` (or its adjoint twin) to feed it from the
printed `lambda_{1/8,2}` form. -/
theorem shom_switch (d : ℕ) :
    ∃ Cs : ℝ, 0 < Cs ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (E : {E : ℝ // 1 ≤ E}),
        mStarStar M < m0 →
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        Cs * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        ∀ m n : ℤ, n ≤ m → m ≤ m0 →
          ∀ (U : Book.Ch02.Domain d) (A : Book.Ch02.CoeffOn U) (Cev : ℝ),
            (Annealed.sigmaBar M n : ℝ) *
                Book.Ch02.matrixNorm (Book.Ch02.sigmaStarInvCoarse U A) ≤ Cev →
            ∀ v : Vec d, vecNormSq v ≤ 2 →
              Book.Ch02.responseJ U A
                  (Observable.inverseSqrtLoad (Annealed.sigmaBar M m) v)
                  (Observable.sqrtLoad (Annealed.sigmaBar M m) v) ≤
                8 * Book.Ch02.responseJ U A
                      (Observable.inverseSqrtLoad (Annealed.sigmaBar M n) v)
                      (Observable.sqrtLoad (Annealed.sigmaBar M n) v) +
                  Cs * Cev * min 1 (M.gamma ^ 2 * ((m : ℝ) - (n : ℝ)) ^ 2) *
                    (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))) +
                  Cs * Cev *
                      ((E : ℝ) ^ 4 * (M.gamma ^ 2 * |Real.log M.gamma| ^ 4)) *
                    (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))) := by
  obtain ⟨C, hC0, hcont⟩ := shom_continuity d
  refine ⟨max C (16 * C ^ 2), lt_of_lt_of_le hC0 (le_max_left _ _), ?_⟩
  intro M m0 E hm0 hstate hCE hgammaE m n hnm hm U A Cev hgate v hv
  have hcinv0 : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ :=
    (inv_pos.mpr (Disorder.cstar_characterization M).1).le
  have hCE' : C * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hcinv0) hCE
  obtain ⟨-, hratio, -, -, hdefect⟩ :=
    hcont M m0 E hm0 hstate hCE' hgammaE m n hnm hm
  have hsm : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hsn : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have ha : (0 : ℝ) ≤ M.gamma * ((m : ℝ) - (n : ℝ)) :=
    mul_nonneg hgamma0.le (by linarith)
  have hb : (0 : ℝ) ≤ (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2) := by
    have : (0 : ℝ) ≤ (E : ℝ) ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ M.gamma * |Real.log M.gamma| ^ 2 :=
      mul_nonneg hgamma0.le (sq_nonneg _)
    exact mul_nonneg this h2
  -- the defect display, with the reverse term dropped
  have hdef : |(Annealed.sigmaBar M m : ℝ) * ((Annealed.sigmaBar M n : ℝ))⁻¹ - 1| ≤
      C * min 1 (M.gamma * ((m : ℝ) - (n : ℝ)) +
          (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2)) *
        (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ))) := by
    have hrev : (0 : ℝ) ≤
        |(Annealed.sigmaBar M n : ℝ) * ((Annealed.sigmaBar M m : ℝ))⁻¹ - 1| :=
      abs_nonneg _
    linarith [hdefect, hrev]
  have hmain := responseJ_shom_switch_of_defect U A hsm hsn hratio hC0.le ha hb
    hdef hgate hv
  -- rewrite the loading spellings and absorb `16 C^2` into `Cs`
  have hload : Book.Ch02.responseJ U A
        (Observable.inverseSqrtLoad (Annealed.sigmaBar M m) v)
        (Observable.sqrtLoad (Annealed.sigmaBar M m) v) =
      Book.Ch02.responseJ U A
        ((Real.sqrt (Annealed.sigmaBar M m : ℝ))⁻¹ • v)
        (Real.sqrt (Annealed.sigmaBar M m : ℝ) • v) := rfl
  have hloadn : Book.Ch02.responseJ U A
        (Observable.inverseSqrtLoad (Annealed.sigmaBar M n) v)
        (Observable.sqrtLoad (Annealed.sigmaBar M n) v) =
      Book.Ch02.responseJ U A
        ((Real.sqrt (Annealed.sigmaBar M n : ℝ))⁻¹ • v)
        (Real.sqrt (Annealed.sigmaBar M n : ℝ) • v) := rfl
  rw [hload, hloadn]
  have hCev0 : (0 : ℝ) ≤ Cev := gate_nonneg U A hsn.le hgate
  have hpow0 : (0 : ℝ) <
      (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hmin0 : (0 : ℝ) ≤ min 1 (M.gamma ^ 2 * ((m : ℝ) - (n : ℝ)) ^ 2) :=
    le_min (by norm_num) (by positivity)
  have hCs : 16 * C ^ 2 ≤ max C (16 * C ^ 2) := le_max_right _ _
  have hidmin : (M.gamma * ((m : ℝ) - (n : ℝ))) ^ 2 =
      M.gamma ^ 2 * ((m : ℝ) - (n : ℝ)) ^ 2 := by ring
  have hidb : ((E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2)) ^ 2 =
      (E : ℝ) ^ 4 * (M.gamma ^ 2 * |Real.log M.gamma| ^ 4) := by ring
  rw [hidmin, hidb] at hmain
  have hterm1 : 16 * C ^ 2 * Cev *
        min 1 (M.gamma ^ 2 * ((m : ℝ) - (n : ℝ)) ^ 2) *
      (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))) ≤
      max C (16 * C ^ 2) * Cev *
          min 1 (M.gamma ^ 2 * ((m : ℝ) - (n : ℝ)) ^ 2) *
        (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))) := by
    have hfac : (0 : ℝ) ≤ Cev * min 1 (M.gamma ^ 2 * ((m : ℝ) - (n : ℝ)) ^ 2) *
        (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))) :=
      mul_nonneg (mul_nonneg hCev0 hmin0) hpow0.le
    nlinarith [hCs, hfac]
  have hterm2 : 16 * C ^ 2 * Cev *
        ((E : ℝ) ^ 4 * (M.gamma ^ 2 * |Real.log M.gamma| ^ 4)) *
      (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))) ≤
      max C (16 * C ^ 2) * Cev *
          ((E : ℝ) ^ 4 * (M.gamma ^ 2 * |Real.log M.gamma| ^ 4)) *
        (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))) := by
    have hb4 : (0 : ℝ) ≤ (E : ℝ) ^ 4 * (M.gamma ^ 2 * |Real.log M.gamma| ^ 4) := by
      positivity
    have hfac : (0 : ℝ) ≤ Cev *
        ((E : ℝ) ^ 4 * (M.gamma ^ 2 * |Real.log M.gamma| ^ 4)) *
        (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))) := by positivity
    nlinarith [hCs, hfac]
  linarith [hmain, hterm1, hterm2]

/-! ## 7. Discharging the transport's consumption interface

The switch is *pointwise inside* the response, so it is discharged inside the
hypothesis `h` of `breakdownLeg{A,B}_le_of_originCube_translate_bound` **at
`sigma:= Annealed.sigmaBar M m`** — instantiating `sigma:= shom_{l-h}` would
produce a leg at the wrong comparator for
`Breakdown.cutoffHomogenizationError_sq_ae_le_breakdown` ((i)). -/

/-- **The primal breakdown leg from the switch plus a deep-comparator bound.**

If, at the translated origin cube, the response at the *deep* comparator is
bounded by `c0` over the whole loading ball, and the switch moves the *working*
comparator onto it at leading constant `Kc` and additive remainder `rem`, then
`breakdownLegA` at the working comparator is bounded by `Kc c0 + rem`.

**`hdeep`'s producer (disclosure).**  `hdeep` is *not* produced anywhere in this
module, and unlike `hgate` it is not a subnode either: it is **the assembly's
own obligation**.  `hswitch`'s producer, by contrast, *is* in this file —
`shom_switch`, composed here as `breakdownLegA_le_of_shom_switch`. -/
theorem breakdownLegA_le_of_switch [NeZero d] (M : ABKModel d) (L : ℤ)
    (R : TriadicCube d) (omega : CutoffSample d)
    (sigma sigmaDeep : Observable.PositiveScalar) {Kc c0 rem : ℝ} (hKc : 0 ≤ Kc)
    (hc0 : 0 ≤ c0) (hrem : 0 ≤ rem)
    (hswitch : ∀ v : Vec d, vecNormSq v ≤ 2 →
      Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d R.scale))
          ((coefficientCutoffTriadicCoeffFamily M L
            (translateCutoffSample (triadicCubeShift R) omega)).coeffOn
              (originCube d R.scale))
          (Observable.inverseSqrtLoad sigma v) (Observable.sqrtLoad sigma v) ≤
        Kc * Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d R.scale))
              ((coefficientCutoffTriadicCoeffFamily M L
                (translateCutoffSample (triadicCubeShift R) omega)).coeffOn
                  (originCube d R.scale))
              (Observable.inverseSqrtLoad sigmaDeep v)
              (Observable.sqrtLoad sigmaDeep v) + rem)
    (hdeep : ∀ v : Vec d, vecNormSq v ≤ 2 →
      Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d R.scale))
          ((coefficientCutoffTriadicCoeffFamily M L
            (translateCutoffSample (triadicCubeShift R) omega)).coeffOn
              (originCube d R.scale))
          (Observable.inverseSqrtLoad sigmaDeep v)
          (Observable.sqrtLoad sigmaDeep v) ≤ c0) :
    breakdownLegA R (coefficientCutoffTriadicCoeffFamily M L omega)
        (Observable.isotropicComparatorMatrix sigma) ≤ Kc * c0 + rem := by
  refine breakdownLegA_le_of_originCube_translate_bound M L R omega sigma
    (by nlinarith [hKc, hc0, hrem]) ?_
  intro v hv
  exact le_trans (hswitch v hv)
    (by linarith [mul_le_mul_of_nonneg_left (hdeep v hv) hKc])

/-- The adjoint twin of `breakdownLegA_le_of_switch`; the transported
representative is the transpose, exactly as in
`breakdownLegB_le_of_originCube_translate_bound`.

`hswitch`'s producer is `shom_switch` itself, composed here as
`breakdownLegB_le_of_shom_switch`. -/
theorem breakdownLegB_le_of_switch [NeZero d] (M : ABKModel d) (L : ℤ)
    (R : TriadicCube d) (omega : CutoffSample d)
    (sigma sigmaDeep : Observable.PositiveScalar) {Kc c0 rem : ℝ} (hKc : 0 ≤ Kc)
    (hc0 : 0 ≤ c0) (hrem : 0 ≤ rem)
    (hswitch : ∀ v : Vec d, vecNormSq v ≤ 2 →
      Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d R.scale))
          ((coefficientCutoffTriadicCoeffFamily M L
            (translateCutoffSample (triadicCubeShift R) omega)).coeffOn
              (originCube d R.scale)).transpose
          (Observable.inverseSqrtLoad sigma v) (Observable.sqrtLoad sigma v) ≤
        Kc * Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d R.scale))
              ((coefficientCutoffTriadicCoeffFamily M L
                (translateCutoffSample (triadicCubeShift R) omega)).coeffOn
                  (originCube d R.scale)).transpose
              (Observable.inverseSqrtLoad sigmaDeep v)
              (Observable.sqrtLoad sigmaDeep v) + rem)
    (hdeep : ∀ v : Vec d, vecNormSq v ≤ 2 →
      Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d R.scale))
          ((coefficientCutoffTriadicCoeffFamily M L
            (translateCutoffSample (triadicCubeShift R) omega)).coeffOn
              (originCube d R.scale)).transpose
          (Observable.inverseSqrtLoad sigmaDeep v)
          (Observable.sqrtLoad sigmaDeep v) ≤ c0) :
    breakdownLegB R (coefficientCutoffTriadicCoeffFamily M L omega)
        (Observable.isotropicComparatorMatrix sigma) ≤ Kc * c0 + rem := by
  refine breakdownLegB_le_of_originCube_translate_bound M L R omega sigma
    (by nlinarith [hKc, hc0, hrem]) ?_
  intro v hv
  exact le_trans (hswitch v hv)
    (by linarith [mul_le_mul_of_nonneg_left (hdeep v hv) hKc])

/-! ### The composed endpoints

`shom_switch` emits the **left-associated** three-term `8 * J + A + B`, while
`breakdownLeg{A,B}_le_of_switch`'s `hswitch` demands the **two-term** `Kc * J +
rem`.  Over the reals those are equal but not syntactically so, and an `exact`
composition of the two headline endpoints of this module *fails* with a `Type
mismatch` (`8 * J + A + B` against `8 * J + (A + B)`).  The two theorems below
exhibit the composition once and for all, with the `linarith` bridge discharged
here rather than at every call site, at the development instantiation `sigma:=
shom_m`, `sigmaDeep:= shom_n` (i).  They are the actual content of the header's
claim that `breakdownLeg{A,B}_le_of_switch` is "the composition with the proved
transport".  No statement of `shom_switch` or of either leg lemma is changed. -/

/-- **The primal breakdown leg, straight from `shom_switch`.**

The full chain of this module in one statement: on the `l.shom.continuity`
premise list, for every pair of scales `n <= m <= m0`, every translated origin
cube of the breakdown display, every gate level `Cev` clamping the
`sigma_*^{-1}` size at the *deep* comparator `shom_n`, and every deep-response
bound `c0` over the loading ball `vecNormSq v <= 2`,

```
breakdownLegA R (a_L omega) (isotropic (shom_m))
  <= 8 c0
     + (Cs Cev min{1, cgamma^2 (m-n)^2} 3^{2 cgamma (m-n)}
        + Cs Cev E^4 cgamma^2 |log cgamma|^4 3^{2 cgamma (m-n)}) .
``` -/
theorem breakdownLegA_le_of_shom_switch (d : ℕ) [NeZero d] :
    ∃ Cs : ℝ, 0 < Cs ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (E : {E : ℝ // 1 ≤ E}),
        mStarStar M < m0 →
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        Cs * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        ∀ m n : ℤ, n ≤ m → m ≤ m0 →
          ∀ (L : ℤ) (R : TriadicCube d) (omega : CutoffSample d) (Cev c0 : ℝ),
            0 ≤ c0 →
            (Annealed.sigmaBar M n : ℝ) *
                Book.Ch02.matrixNorm (Book.Ch02.sigmaStarInvCoarse
                  (Book.Ch02.cubeDomain (originCube d R.scale))
                  ((coefficientCutoffTriadicCoeffFamily M L
                    (translateCutoffSample (triadicCubeShift R) omega)).coeffOn
                      (originCube d R.scale))) ≤ Cev →
            (∀ v : Vec d, vecNormSq v ≤ 2 →
              Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d R.scale))
                  ((coefficientCutoffTriadicCoeffFamily M L
                    (translateCutoffSample (triadicCubeShift R) omega)).coeffOn
                      (originCube d R.scale))
                  (Observable.inverseSqrtLoad (Annealed.sigmaBar M n) v)
                  (Observable.sqrtLoad (Annealed.sigmaBar M n) v) ≤ c0) →
            breakdownLegA R (coefficientCutoffTriadicCoeffFamily M L omega)
                (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) ≤
              8 * c0 +
                (Cs * Cev * min 1 (M.gamma ^ 2 * ((m : ℝ) - (n : ℝ)) ^ 2) *
                    (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))) +
                  Cs * Cev *
                      ((E : ℝ) ^ 4 * (M.gamma ^ 2 * |Real.log M.gamma| ^ 4)) *
                    (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ))))) := by
  obtain ⟨Cs, hCs0, hsw⟩ := shom_switch d
  refine ⟨Cs, hCs0, ?_⟩
  intro M m0 E hm0 hstate hCE hgammaE m n hnm hm L R omega Cev c0 hc0 hgate hdeep
  have hCev0 : (0 : ℝ) ≤ Cev :=
    gate_nonneg _ _ (Annealed.sigmaBar M n).2.le hgate
  have hpow0 : (0 : ℝ) <
      (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hmin0 : (0 : ℝ) ≤ min 1 (M.gamma ^ 2 * ((m : ℝ) - (n : ℝ)) ^ 2) :=
    le_min (by norm_num) (by positivity)
  have hE4 : (0 : ℝ) ≤ (E : ℝ) ^ 4 * (M.gamma ^ 2 * |Real.log M.gamma| ^ 4) := by
    positivity
  have hrem0 : (0 : ℝ) ≤
      Cs * Cev * min 1 (M.gamma ^ 2 * ((m : ℝ) - (n : ℝ)) ^ 2) *
          (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))) +
        Cs * Cev * ((E : ℝ) ^ 4 * (M.gamma ^ 2 * |Real.log M.gamma| ^ 4)) *
          (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))) := by
    have hA0 := mul_nonneg (mul_nonneg (mul_nonneg hCs0.le hCev0) hmin0) hpow0.le
    have hB0 := mul_nonneg (mul_nonneg (mul_nonneg hCs0.le hCev0) hE4) hpow0.le
    linarith
  refine breakdownLegA_le_of_switch M L R omega (Annealed.sigmaBar M m)
    (Annealed.sigmaBar M n) (by norm_num) hc0 hrem0 ?_ hdeep
  intro v hv
  have h := hsw M m0 E hm0 hstate hCE hgammaE m n hnm hm _ _ Cev hgate v hv
  linarith [h]

/-- **The adjoint breakdown leg, straight from `shom_switch`.**  The adjoint
twin of `breakdownLegA_le_of_shom_switch`; the gate is stated at the transposed
representative, which `sigmaStarInv_transpose_gate_of_lambdaGate` supplies from
the *same* printed `lambda`-gate by adjoint invariance. -/
theorem breakdownLegB_le_of_shom_switch (d : ℕ) [NeZero d] :
    ∃ Cs : ℝ, 0 < Cs ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (E : {E : ℝ // 1 ≤ E}),
        mStarStar M < m0 →
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        Cs * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        ∀ m n : ℤ, n ≤ m → m ≤ m0 →
          ∀ (L : ℤ) (R : TriadicCube d) (omega : CutoffSample d) (Cev c0 : ℝ),
            0 ≤ c0 →
            (Annealed.sigmaBar M n : ℝ) *
                Book.Ch02.matrixNorm (Book.Ch02.sigmaStarInvCoarse
                  (Book.Ch02.cubeDomain (originCube d R.scale))
                  ((coefficientCutoffTriadicCoeffFamily M L
                    (translateCutoffSample (triadicCubeShift R) omega)).coeffOn
                      (originCube d R.scale)).transpose) ≤ Cev →
            (∀ v : Vec d, vecNormSq v ≤ 2 →
              Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d R.scale))
                  ((coefficientCutoffTriadicCoeffFamily M L
                    (translateCutoffSample (triadicCubeShift R) omega)).coeffOn
                      (originCube d R.scale)).transpose
                  (Observable.inverseSqrtLoad (Annealed.sigmaBar M n) v)
                  (Observable.sqrtLoad (Annealed.sigmaBar M n) v) ≤ c0) →
            breakdownLegB R (coefficientCutoffTriadicCoeffFamily M L omega)
                (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) ≤
              8 * c0 +
                (Cs * Cev * min 1 (M.gamma ^ 2 * ((m : ℝ) - (n : ℝ)) ^ 2) *
                    (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))) +
                  Cs * Cev *
                      ((E : ℝ) ^ 4 * (M.gamma ^ 2 * |Real.log M.gamma| ^ 4)) *
                    (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ))))) := by
  obtain ⟨Cs, hCs0, hsw⟩ := shom_switch d
  refine ⟨Cs, hCs0, ?_⟩
  intro M m0 E hm0 hstate hCE hgammaE m n hnm hm L R omega Cev c0 hc0 hgate hdeep
  have hCev0 : (0 : ℝ) ≤ Cev :=
    gate_nonneg _ _ (Annealed.sigmaBar M n).2.le hgate
  have hpow0 : (0 : ℝ) <
      (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hmin0 : (0 : ℝ) ≤ min 1 (M.gamma ^ 2 * ((m : ℝ) - (n : ℝ)) ^ 2) :=
    le_min (by norm_num) (by positivity)
  have hE4 : (0 : ℝ) ≤ (E : ℝ) ^ 4 * (M.gamma ^ 2 * |Real.log M.gamma| ^ 4) := by
    positivity
  have hrem0 : (0 : ℝ) ≤
      Cs * Cev * min 1 (M.gamma ^ 2 * ((m : ℝ) - (n : ℝ)) ^ 2) *
          (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))) +
        Cs * Cev * ((E : ℝ) ^ 4 * (M.gamma ^ 2 * |Real.log M.gamma| ^ 4)) *
          (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))) := by
    have hA0 := mul_nonneg (mul_nonneg (mul_nonneg hCs0.le hCev0) hmin0) hpow0.le
    have hB0 := mul_nonneg (mul_nonneg (mul_nonneg hCs0.le hCev0) hE4) hpow0.le
    linarith
  refine breakdownLegB_le_of_switch M L R omega (Annealed.sigmaBar M m)
    (Annealed.sigmaBar M n) (by norm_num) hc0 hrem0 ?_ hdeep
  intro v hv
  have h := hsw M m0 E hm0 hstate hCE hgammaE m n hnm hm _ _ Cev hgate v hv
  linarith [h]

end

end Algsuperdiff.Section3.Provider.Localization
