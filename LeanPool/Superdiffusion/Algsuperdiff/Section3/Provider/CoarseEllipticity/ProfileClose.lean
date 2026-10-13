/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.LowerLegProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.PayloadSandwich
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Disorder.CstarUpperBound

/-!
# ProfileClose

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The collar and the constant pricing of `p.cg.ellipticity.bounds` at `q = 2`

`Provider/CoarseEllipticity/PayloadSandwich.lean` composes the two legs' payload
conjunctions out of `GridDomination`'s on-grid dominations and `BlockPayload`'s
per-scale block payload.  What its two producers deliver is a deterministic slot
`(ctop Cdet + Cdet) (mass rho^{-1})` and an exceptional amplitude
`foldedBlockPole d sigma A mass rho ctop p`, at the raw pole `rho = 2s`.  What
the frozen displays require is the *priced* form: the deterministic slot inside
`lowerEllipticityProfile Clow gamma s q` (lower) resp. inside `Cup` (upper), and
the exceptional amplitude below the frozen rare scale
`exp(-Clow^{-1} E^{-2} gamma^{-1})`.  This module is that pricing, and nothing
else: **every declaration below is an inequality between real numbers**, no
observable, no measure and no source step enters.

## The four items, and what each of them is

1. **The collar**, `rho = 2s -> 2s - gamma` (/ 6185 / 6212).
   `e.slstar.multiscale` normalizes by `3^{-gamma(m-n)}` on its left, so the
   lifted per-scale display carries `3^{gamma(k+1)}` on its right.  A
   `k`-dependent factor cannot sit in the consumers' `Cdet`;
   `BlockPayload.{forall_le_tsum_gridWeight_collar, le_tsum_gridWeight_collar}`
   absorbs it into the weight, which is exactly the passage from the pole `2s`
   to the pole `2s - gamma`.  §5 runs that absorption through the lower
   summation.  Its three-term twin is generic algebra, but the faithful upper
   source route applies the collar only to its two random lanes and keeps the
   deterministic slot at the raw pole, as Item 2 records.

2. **The deterministic slot.**  `detSlot_le_lowerEllipticityProfile` prices
   `(ctop Cdet + Cdet)(c_{s,2} (2s-gamma)^{-1})` into
   `lowerEllipticityProfile Clow gamma s (finite r)` on the printed branch
   `2 <= r`, through `c_{s,2} <= 4s`
   (`Book.Ch02.geometricDiscount_le_two_mul`, the bound behind
   `LambdaGridBridge.gridSumConst_two_le`) and
   `LowerLegProfile.lowerEllipticityProfile_finite_of_two_le`.  The output gate
   is `4 (ctop + 1) Cdet <= Clow`.

   **The *upper* leg's deterministic slot must not take the collar.**  On the
   frozen window `c_{s,2} (2s - gamma)^{-1}` is unbounded (at
   `s = gamma/2 + eps` it is `~
   gamma log 3 / (2 eps)` with `eps = exp(-C^{-1}E^{-2}gamma^{-1})`), so no
   dimension-only `Cup` majorizes it; and it need not, because the printed
   per-cube upper display has the deterministic `C` and carries
   `3^{gamma(m-n)}` only on the two random lanes.  `detSlot_le_upperConst`
   therefore prices the upper slot at the **uncollared** pole `(2s)^{-1}`,
   where `c_{s,2} (2s)^{-1} <= 2` is a genuine dimension-only bound --- which
   is exactly the slot `PayloadSandwich.threeTermSplit_cutoffUpperEllipticity`
   already produces.  The upper output gate is `2 (ctop + 1) Cdet <= Cup`.

3. **The exceptional amplitude, and the absorption gate.**  `foldedBlockPole_eq` puts the
   folded pole in closed form `Gamma_tri(sigma)^2 (mass (gridNetConst A)) (ctop rho^{-1} +
   p! (1+rho^{-1})^{p+1})`; `poleBracket_le` collapses the bracket against the window's
   own `2 eps <= 2s - gamma`; and `foldedBlockPole_le_of_gate` proves `foldedBlockPole <=
   eps`.

4. **The upper `Gamma_1` lane.**  `tsum_gridWeight_mul_foldedOrdinaryAmp_le`
   sums the folded ordinary amplitudes at the source's own degree
   (`e.bL.multiscale`'s per-cube `C gamma (m-n+1)` lifted by `e.maxy.bound`'s
   `(m-n+1)^{1/sigma}` at `sigma = 1`, i.e. degree `2`) against `gridWeight
   rho`, producing the pole order `3` --- the printed `(2s-gamma)^{-3}` of
   `e.cg.ellip.upper`, *not* an over-bound.  `hB1_le_frozenUpperOrdinary` then
   proves the frozen amplitude `Cup cstar^{-1} s gamma (2s-gamma)^{-3}`
   verbatim, using `c_{s,2} <= 4s` and `cstar <= 3/2`
   (`two_thirds_le_cstar_inv`).

## What is NOT proved here

Nothing analytic.  No per-cube block estimate (`p.bfA.multiscalebound`), no
`L`-uniformity, no base case, no observable and no measure occurs in any
statement of §1--§4 and §6; §5's two theorems are the model-free summations of
`LowerLeg` / `ScaleSummation` with the collar inserted, and they carry their
`hgrid` and `hsplit` binders exactly as those consumers do.  **No node is closed
by this module**, and no theorem below asserts that any leg's payload is
satisfiable.

## References

* ABK26, `p.cg.ellipticity.bounds`, statement (`e.cg.ellip.lower`,
  `e.cg.ellip.upper`); proof, with `e.cg.ellip.lower.pre`,
  `e.cg.ellip.upper.pre` and the absorption gate ("the assumption `2s - gamma >
  exp(-c E^{-2} gamma^{-1})` allows us to absorb the factors of `(2s - gamma)`
  into the exponential").
* ABK26, `p.bfA.multiscalebound`, `e.slstar.multiscale` label, `e.bL.multiscale`
  label; `l.maximums.Gamma.s` label.
* `Provider/CoarseEllipticity/{PayloadSandwich, BlockPayload, LowerLeg,
  LowerLegProfile, ScaleSummation, GridWeights, LambdaGridBridge}.lean` (the
  consumers whose slots are priced here).
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-! ## 1. Abstract-real cores

Every core of this module is stated over abstract reals: no `Real.exp` and no
`Real.rpow` occurs in §1, so no nonlinear arithmetic step ever meets a
transcendental. -/

/-- On `(0, 1]` the reciprocal is at least one. -/
theorem one_le_inv_of_le_one {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    1 ≤ eps⁻¹ := by
  have h := mul_le_mul_of_nonneg_right heps1 (inv_nonneg.2 heps.le)
  rwa [mul_inv_cancel₀ (ne_of_gt heps), one_mul] at h

/-- **The window collapse.**  If the rare scale `eps` sits at most halfway to the
pole parameter `rho` --- which on the frozen window is exactly
`2 exp(-C^{-1}E^{-2}gamma^{-1}) <= 2s - gamma` --- then the printed algebraic
pole `1 + rho^{-1}` is at most `2 eps^{-1}`. -/
theorem one_add_inv_le_two_mul_inv {eps rho : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hrho : 2 * eps ≤ rho) : 1 + rho⁻¹ ≤ 2 * eps⁻¹ := by
  have hrhopos : 0 < rho := lt_of_lt_of_le (by linarith) hrho
  have hinv1 : 1 ≤ eps⁻¹ := one_le_inv_of_le_one heps heps1
  have hkey : rho⁻¹ * (2 * eps) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hrho (inv_nonneg.2 hrhopos.le)
    rwa [inv_mul_cancel₀ (ne_of_gt hrhopos)] at h
  have h2 : rho⁻¹ * 2 ≤ eps⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hkey (inv_nonneg.2 heps.le)
    calc rho⁻¹ * 2 = rho⁻¹ * (2 * eps) * eps⁻¹ := by field_simp
      _ ≤ 1 * eps⁻¹ := h
      _ = eps⁻¹ := one_mul _
  linarith


/-- **The absorption step, abstractly.**  A nonnegative product `K A` bounded by
`eps^{n+1}` absorbs a pole of order `n` in `eps` and proves at `eps`.  This is
the whole arithmetic. -/
theorem mul_le_of_pow_inv_gate {K A P eps : ℝ} {n : ℕ}
    (hKA : 0 ≤ K * A) (heps : 0 < eps) (hP : P ≤ (eps⁻¹) ^ n)
    (hgate : K * A ≤ eps ^ (n + 1)) : K * A * P ≤ eps := by
  have hpow : (0 : ℝ) ≤ (eps⁻¹) ^ n := pow_nonneg (inv_nonneg.2 heps.le) n
  have hcancel : eps ^ (n + 1) * (eps⁻¹) ^ n = eps := by
    have hne : (eps : ℝ) ≠ 0 := ne_of_gt heps
    rw [inv_pow, pow_succ, mul_assoc, mul_comm eps ((eps ^ n)⁻¹), ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero n hne), one_mul]
  calc K * A * P ≤ K * A * (eps⁻¹) ^ n := mul_le_mul_of_nonneg_left hP hKA
    _ ≤ eps ^ (n + 1) * (eps⁻¹) ^ n := mul_le_mul_of_nonneg_right hgate hpow
    _ = eps := hcancel

/-! ## 2. The folded pole in closed form, and its gate -/

/-- The folded amplitude's head: at gap `1` the `e.maxy.bound` polynomial is
trivial. -/
theorem gridBlockAmp_zero (d : ℕ) (sigma A : ℝ) :
    gridBlockAmp d sigma A 0 = gridNetConst d sigma * A := by
  rw [gridBlockAmp]
  norm_num


/-- **The folded pole in closed form.**  `foldedBlockPole` factors as a
dimension-only head times the bracket `ctop rho^{-1} + p! (1+rho^{-1})^{p+1}`,
which is the only place the pole lives. -/
theorem foldedBlockPole_eq (d : ℕ) (sigma A mass rho ctop : ℝ) (p : ℕ) :
    foldedBlockPole d sigma A mass rho ctop p
      = gammaTriangleConst sigma ^ 2 * (mass * (gridNetConst d sigma * A)) *
          (ctop * rho⁻¹ + (Nat.factorial p : ℝ) * (1 + rho⁻¹) ^ (p + 1)) := by
  rw [foldedBlockPole, blockPoleConst, gridBlockAmp_zero]
  ring

/-- The bracket of `foldedBlockPole_eq`, collapsed against the window. -/
theorem poleBracket_le {rho eps ctop : ℝ} (p : ℕ)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hrho : 2 * eps ≤ rho) (hctop : 0 ≤ ctop) :
    ctop * rho⁻¹ + (Nat.factorial p : ℝ) * (1 + rho⁻¹) ^ (p + 1)
      ≤ 2 ^ (p + 1) * (ctop + (Nat.factorial p : ℝ)) * (eps⁻¹) ^ (p + 1) := by
  have hrhopos : 0 < rho := lt_of_lt_of_le (by linarith) hrho
  have hinv1 : 1 ≤ eps⁻¹ := one_le_inv_of_le_one heps heps1
  have hbase : 1 + rho⁻¹ ≤ 2 * eps⁻¹ := one_add_inv_le_two_mul_inv heps heps1 hrho
  have hbnn : (0 : ℝ) ≤ 1 + rho⁻¹ := by
    have := inv_nonneg.2 hrhopos.le
    linarith
  have hsplit : (2 * eps⁻¹) ^ (p + 1) = 2 ^ (p + 1) * (eps⁻¹) ^ (p + 1) := mul_pow _ _ _
  have hstep : (1 + rho⁻¹) ^ (p + 1) ≤ 2 ^ (p + 1) * (eps⁻¹) ^ (p + 1) := by
    rw [← hsplit]
    exact pow_le_pow_left₀ hbnn hbase (p + 1)
  have htail : rho⁻¹ ≤ 2 ^ (p + 1) * (eps⁻¹) ^ (p + 1) := by
    have h1 : (2 : ℝ) * eps⁻¹ ≤ (2 * eps⁻¹) ^ (p + 1) :=
      le_self_pow₀ (by linarith) (Nat.succ_ne_zero p)
    rw [hsplit] at h1
    linarith
  have hfac : (0 : ℝ) ≤ (Nat.factorial p : ℝ) := Nat.cast_nonneg _
  have hA : ctop * rho⁻¹ ≤ ctop * (2 ^ (p + 1) * (eps⁻¹) ^ (p + 1)) :=
    mul_le_mul_of_nonneg_left htail hctop
  have hB : (Nat.factorial p : ℝ) * (1 + rho⁻¹) ^ (p + 1)
      ≤ (Nat.factorial p : ℝ) * (2 ^ (p + 1) * (eps⁻¹) ^ (p + 1)) :=
    mul_le_mul_of_nonneg_left hstep hfac
  have hring : ctop * (2 ^ (p + 1) * (eps⁻¹) ^ (p + 1))
        + (Nat.factorial p : ℝ) * (2 ^ (p + 1) * (eps⁻¹) ^ (p + 1))
      = 2 ^ (p + 1) * (ctop + (Nat.factorial p : ℝ)) * (eps⁻¹) ^ (p + 1) := by ring
  linarith [hring.ge, hring.le]

/-- **The exceptional amplitude, priced below the rare scale.**

`hgate` is the *definition of the output constant*: it fixes how small the
per-cube amplitude `A` of `p.bfA.multiscalebound` must be against the leg's own
rare scale `eps`, and `gate_of_perCubeExponential` below discharges it from the
source's own `exp(-c E^{-2} gamma^{-1})` shape. -/
theorem foldedBlockPole_le_of_gate {d : ℕ} {sigma A mass rho ctop eps : ℝ} {p : ℕ}
    (hmass : 0 ≤ mass) (hA : 0 ≤ A) (hctop : 0 ≤ ctop)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hrho : 2 * eps ≤ rho)
    (hgate : gammaTriangleConst sigma ^ 2 * (mass * gridNetConst d sigma) *
        (2 ^ (p + 1) * (ctop + (Nat.factorial p : ℝ))) * A ≤ eps ^ (p + 2)) :
    foldedBlockPole d sigma A mass rho ctop p ≤ eps := by
  have hfac : (0 : ℝ) ≤ (Nat.factorial p : ℝ) := Nat.cast_nonneg _
  have h1 : (0 : ℝ) ≤ gammaTriangleConst sigma ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ mass * gridNetConst d sigma :=
    mul_nonneg hmass (gridNetConst_nonneg d sigma)
  have h3 : (0 : ℝ) ≤ 2 ^ (p + 1) * (ctop + (Nat.factorial p : ℝ)) :=
    mul_nonneg (by positivity) (by linarith)
  have hKA : (0 : ℝ) ≤ gammaTriangleConst sigma ^ 2 * (mass * gridNetConst d sigma) *
      (2 ^ (p + 1) * (ctop + (Nat.factorial p : ℝ))) * A :=
    mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) hA
  have hcoef : (0 : ℝ) ≤ gammaTriangleConst sigma ^ 2 *
      (mass * (gridNetConst d sigma * A)) :=
    mul_nonneg h1 (mul_nonneg hmass (mul_nonneg (gridNetConst_nonneg d sigma) hA))
  calc foldedBlockPole d sigma A mass rho ctop p
      = gammaTriangleConst sigma ^ 2 * (mass * (gridNetConst d sigma * A)) *
          (ctop * rho⁻¹ + (Nat.factorial p : ℝ) * (1 + rho⁻¹) ^ (p + 1)) :=
        foldedBlockPole_eq d sigma A mass rho ctop p
    _ ≤ gammaTriangleConst sigma ^ 2 * (mass * (gridNetConst d sigma * A)) *
          (2 ^ (p + 1) * (ctop + (Nat.factorial p : ℝ)) * (eps⁻¹) ^ (p + 1)) :=
        mul_le_mul_of_nonneg_left (poleBracket_le p heps heps1 hrho hctop) hcoef
    _ = gammaTriangleConst sigma ^ 2 * (mass * gridNetConst d sigma) *
          (2 ^ (p + 1) * (ctop + (Nat.factorial p : ℝ))) * A * (eps⁻¹) ^ (p + 1) := by
        ring
    _ ≤ eps := mul_le_of_pow_inv_gate hKA heps le_rfl hgate

/-- The same, with the window hypothesis in the frozen statement's own shape
`gamma/2 + eps <= s` (i.e. `hsWindow.1`) and the collar-absorbed pole
`rho = 2s - gamma`. -/
theorem foldedBlockPole_le_of_window {d : ℕ} {sigma A mass ctop gamma s eps : ℝ} {p : ℕ}
    (hmass : 0 ≤ mass) (hA : 0 ≤ A) (hctop : 0 ≤ ctop)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hwin : gamma / 2 + eps ≤ s)
    (hgate : gammaTriangleConst sigma ^ 2 * (mass * gridNetConst d sigma) *
        (2 ^ (p + 1) * (ctop + (Nat.factorial p : ℝ))) * A ≤ eps ^ (p + 2)) :
    foldedBlockPole d sigma A mass (2 * s - gamma) ctop p ≤ eps :=
  foldedBlockPole_le_of_gate hmass hA hctop heps heps1 (by linarith) hgate


/-- **The upper leg's exceptional amplitude at `p = 6`** --- the rounding integer
of the frozen index `(1-sigma)/3` (`frozenUpperIndex_inv_le_natSix`), so the
pole order is `p + 1 = 7`, an over-bound of the printed
`(2s-gamma)^{-(4+sigma)}`. -/
theorem foldedBlockPole_frozenUpper_le {d : ℕ} {sigma A mass ctop gamma s eps : ℝ}
    (hmass : 0 ≤ mass) (hA : 0 ≤ A) (hctop : 0 ≤ ctop)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hwin : gamma / 2 + eps ≤ s)
    (hgate : gammaTriangleConst sigma ^ 2 * (mass * gridNetConst d sigma) *
        (128 * (ctop + 720)) * A ≤ eps ^ 8) :
    foldedBlockPole d sigma A mass (2 * s - gamma) ctop 6 ≤ eps := by
  refine foldedBlockPole_le_of_window hmass hA hctop heps heps1 hwin ?_
  have hf : (2 : ℝ) ^ (6 + 1) * (ctop + (Nat.factorial 6 : ℝ)) = 128 * (ctop + 720) := by
    norm_num [Nat.factorial]
  rw [hf]
  exact hgate

/-! ## 3. The frozen rounding integers, and the absorption gate -/


/-- `p = 6` is admissible at the frozen upper index `(1-sigma)/3`. -/
theorem frozenUpperIndex_inv_le_natSix {sigma : ℝ} (h1 : sigma ≤ 1 / 2) :
    ((1 - sigma) / 3)⁻¹ ≤ ((6 : ℕ) : ℝ) := by
  simpa using frozenUpperIndex_inv_le h1


/-- The frozen rare scale is at most one, which is the `eps ≤ 1` binder of §2. -/
theorem exp_neg_frozen_le_one {Clow E gamma : ℝ} (hClow : 0 < Clow)
    (hgamma : 0 < gamma) :
    Real.exp (-(Clow⁻¹ * (E⁻¹) ^ 2 * gamma⁻¹)) ≤ 1 := by
  refine Real.exp_le_one_iff.2 ?_
  have h1 : (0 : ℝ) ≤ Clow⁻¹ := (inv_pos.2 hClow).le
  have h2 : (0 : ℝ) ≤ (E⁻¹) ^ 2 := sq_nonneg _
  have h3 : (0 : ℝ) ≤ gamma⁻¹ := (inv_pos.2 hgamma).le
  have h4 : (0 : ℝ) ≤ Clow⁻¹ * (E⁻¹) ^ 2 * gamma⁻¹ := mul_nonneg (mul_nonneg h1 h2) h3
  linarith





end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
