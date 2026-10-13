/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.PayloadSandwich
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.HsepReduction

/-!
# BfaPerCube

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `p.bfA.multiscalebound` per cube: the `sup_L`, and the Step-3 payload as an Orlicz split

ABK26 `p.bfA.multiscalebound` (statement) prints, for every `n <= m-1`
(`e.slstar.multiscale`),

```
  sup_{L in [m-1, infty) cap Z}  3^{-gamma(m-n)} shom_{m-1} |s^{-1}_{L,*}(cu_n)|
      <=  C + O_{Gamma_{(1-sigma)/2}}( exp(-c E^{-2} gamma^{-1}) ) .
```

This module provides the abstract supremum and Orlicz algebra used by a
faithful local producer; it does not itself discharge the source-level per-cube
estimate.

## The four sub-deltas, and what this module does with each

1. **The `s_{L,*}^{-1}` observable.**  The chain
   (`ConclusionRoot.abs_blockVecDot_coarseBlockMatrix_originCube_le_payload_ae`,
   the proved local branch at the concrete competitor) bounds the *scalar quadratic
   form* `|<(p,q), bfA_L(cu_m)(p,q)>|` at the framed loading, at the single cube
   `cu_m`.  The per-cube display needs the *operator norm*
   `|s^{-1}_{L,*}(z + cu_n)| = matrixNorm (sigmaStarInvCoarse ...)` at every
   descendant.  `BfaObservableNorm.lean` supplies the conditional
   quadratic-form-to-operator-norm implication.  Producing its pure-loading
   premise simultaneously in the loading and transporting the conclusion to
   each translated descendant remain open analytic work.
2. **The `hsep` tail conversion.**  This is available at the base case, in
   `HsepReduction.three_rpow_gamma_hsep_le_two_add_orlicz` (the replacement
   route; the printed middle expression is false).  What is *not* proved is the
   rest of the Step-3 right-hand side: the collar power `3^{2b hsep}`
   multiplying the improved exponential, and the sum of the two resulting lanes
   at one exponent.
3. **The `sup_{L >= m-1}`.**  Sections 1 and 3 prove the abstract carrier
   equivalence: once a faithful per-cube bound is available for every `L` with
   an `L`-free right-hand side, the canonical majorant is that right-hand side,
   and the `forall L` reading implies the printed `sSup` bound.  This algebra
   does not prove the per-cube source premise, so it closes no source node.
4. This module neither proves nor removes them.

## What is NOT proved here

* The Step-3 payoff at a descendant is only almost-everywhere and conditional,
  and its random separation scale is local: at `R` it is evaluated at
  `R.scale` on the translated sample.  `BfaLocalLane.lean` records that exact
  interface.  The former root/pathwise specialization in this file was
  rejected because it replaced that obligation by one root random variable
  and a pointwise `forall omega`; it has been removed.
* The final numerical comparison "`bfaLaneScale <= exp(-c E^{-2} gamma^{-1})`"
  is not performed here.  `ProfileConstants.lean` proves the sound elementary
  comparisons and now also instantiates the `_of_gates` local-grid lane from
  the frozen maximum and fifth-root bounds.  This file alone neither selects
  the final profile constants nor closes the remaining analytic payoff.
* The **collar**.  `e.slstar.multiscale` carries `3^{-gamma(m-n)}` on its L,
  while the proved payload carrier `cutoffSigmaStarInvBlockFamily` does not.
  At `n = m-1-k` the collar is `3^{gamma(k+1)}` on the right, i.e.
  `k`-dependent, and `BlockPayload`'s `Cdet` and `A` slots are scalars.  The
  only route is to absorb the collar into the exponent, `rho -> rho - gamma`,
  which is what the conditional arithmetic of `ProfileClose.lean` does
  (`foldedBlockPole_le_of_window`).
  `PayloadSandwich.blockGridSup_const_mul` gives that
  arithmetic the exact factorization it needs, but no theorem here supplies its
  analytic premise.

## References

* ABK26, `p.bfA.multiscalebound`; `e.slstar.multiscale`; `e.bL.multiscale`; Step
  3 and its conclusion (the deterministic conclusion, the `hsep` conversion, the
  `b_L` display).
* ABK26, `e.hsep.tails`, `e.indc.O.sigma`, `l.maximums.Gamma.s` /
  `e.maxy.bound`.
* `Provider/Multiscale/HsepReduction.lean` (sub-delta 2, proved at base),
  `Provider/Multiscale/ConclusionArithmetic.lean`
  (`three_rpow_le_two_add_indicator`),
  `Provider/Percolation/MinimalScaleSeparation.lean` (`hsep`, `e.hsep.tails`),
  `Provider/Multiscale/WaveOscillations.lean` (`measurableSet_lt_hsep`),
  `Provider/CoarseEllipticity/PayloadSandwich.lean` (the `hLunif` slot),
  `Provider/CoarseEllipticity/BlockPayload.lean` (the `hblock` / `hblockO`
  slots).
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.CoarseEllipticity

noncomputable section

variable {d : ℕ}

/-! ## 1. The printed `sup_{L in [m-1,infty) cap Z}`

`e.slstar.multiscale` prints a supremum over the cutoff ray on the L of an
`L`-free right-hand side.  The proved consumers instead take the `forall L`
form (`hLunif` plus `hblock`).  The two lemmas below prove that this is not a
weakening: the `forall L` form *implies* the printed `sSup` bound
(`raySup_le_of_forall`), and conversely the elements of the ray are dominated
by the `sSup` as soon as the ray is bounded above at all (`le_raySup`), which
the `forall L` form itself supplies.  Nothing anywhere in this file introduces
an unbounded supremum: Lean's `sSup` of an unbounded set is a junk value, and
the only direction used downstream is the one that needs no boundedness. -/


/-! ## 2. The two per-cube payload families -/


/-! ## 3. The `sup_L` collapse: `hLunif` and `hblock` from one `forall L` bound

`hLunif` asks for an `L`-free family `Xc` dominating the per-cube datum at every
cutoff index; `hblock` asks that same `Xc` to obey `|Xc| <= Cdet + U`.  The
source supplies both at once, because the right-hand side it prints is already
`L`-free: take `Xc` to BE that right-hand side.  `hblock` then becomes
`abs_of_nonneg` and the entire content is the `forall L` bound. -/


/-! ## 4. Measurability of the `hsep`-driven observables

Every lane below is a fixed function of the integer `hsep`, so a single
measurability statement covers all of them.
`Percolation.MinimalScaleSeparation` leaves this to the consumer  and
`WaveOscillations.measurableSet_lt_hsep` supplies the only input needed. -/

/-- `hsep` is a random variable.  (`WaveTermTranslation` carries the same
statement as a private helper; it is re-derived here rather than exported from
there, so that this module does not depend on the wave lane.) -/
theorem measurable_hsep (M : ABKModel d) (m : ℤ) (E b : ℝ) :
    Measurable (hsep M m E b) := by
  refine measurable_to_countable' fun k => ?_
  cases k with
  | zero =>
      have hset : hsep M m E b ⁻¹' {0} =
          {omega : CutoffSample d | 0 < hsep M m E b omega}ᶜ := by
        ext omega
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff,
          Set.mem_ofPred_eq]
        omega
      rw [hset]
      exact (measurableSet_lt_hsep M m E b 0).compl
  | succ j =>
      have hset : hsep M m E b ⁻¹' {j + 1} =
          {omega : CutoffSample d | j < hsep M m E b omega} ∩
            {omega : CutoffSample d | j + 1 < hsep M m E b omega}ᶜ := by
        ext omega
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
          Set.mem_compl_iff, Set.mem_ofPred_eq]
        omega
      rw [hset]
      exact (measurableSet_lt_hsep M m E b j).inter
        (measurableSet_lt_hsep M m E b (j + 1)).compl

/-- Any postcomposition of `hsep` is measurable: `ℕ` is countable. -/
theorem measurable_comp_hsep (M : ABKModel d) (m : ℤ) (E b : ℝ) (g : ℕ → ℝ) :
    Measurable fun omega : CutoffSample d => g (hsep M m E b omega) :=
  (measurable_of_countable g).comp (measurable_hsep M m E b)

/-! ## 5. The Step-3 payload as a constant plus one Orlicz lane

The Step-3 conclusion, in its replacement shape, is `Cpre * (3^{gamma hsep} (1 +
3^{2b hsep} eps))`.  Expanding, this is `Cpre * 3^{gamma hsep}  +  Cpre eps *
3^{(gamma+2b) hsep}`.  The first summand is the truncated prefactor, handled by
`HsepReduction`; the second is a pure power of `3^{hsep}`, handled by the
`e.powerofGammasigma` power rule.  The free indicator exponent is fixed so that
both lanes land at one exponent, and that exponent is the manuscript's
relabelled `sigma`. -/

/-- The power `p = (gamma + 2b)/b`: the exponent to which `e.hsep.tails` (which
controls `3^{b hsep}`) must be raised to control `3^{(gamma+2b) hsep}`. -/
def bfaPower (gam b : ℝ) : ℝ := (gam + 2 * b) / b

/-- The choice of `e.indc.O.sigma`'s free exponent, the unique one making the
two lanes coincide. -/
def bfaSigmaTwo (sigma gam b : ℝ) : ℝ := (1 - sigma) / (bfaPower gam b - 1)

/-- The common exponent of the two lanes, `tau = (1-sigma) b / (gamma + 2b)`. -/
def bfaTau (sigma gam b : ℝ) : ℝ := (1 - sigma) / bfaPower gam b


theorem one_lt_bfaPower {gam b : ℝ} (hgam : 0 < gam) (hb : 0 < b) :
    1 < bfaPower gam b := by
  rw [bfaPower, lt_div_iff₀ hb]
  linarith

/-- `p >= 2` always, so the relabelling genuinely weakens the exponent. -/
theorem two_le_bfaPower {gam b : ℝ} (hgam : 0 ≤ gam) (hb : 0 < b) :
    2 ≤ bfaPower gam b := by
  rw [bfaPower, le_div_iff₀ hb]
  linarith

theorem bfaPower_pos {gam b : ℝ} (hgam : 0 < gam) (hb : 0 < b) :
    0 < bfaPower gam b :=
  lt_trans zero_lt_one (one_lt_bfaPower hgam hb)

theorem bfaSigmaTwo_pos {sigma gam b : ℝ} (hsigma : sigma < 1) (hgam : 0 < gam)
    (hb : 0 < b) : 0 < bfaSigmaTwo sigma gam b := by
  rw [bfaSigmaTwo]
  exact div_pos (by linarith) (by linarith [one_lt_bfaPower hgam hb])

theorem bfaTau_pos {sigma gam b : ℝ} (hsigma : sigma < 1) (hgam : 0 < gam)
    (hb : 0 < b) : 0 < bfaTau sigma gam b :=
  div_pos (by linarith) (bfaPower_pos hgam hb)

/-- ** +: the two lanes coincide.**  With `sigma_2` chosen as `bfaSigmaTwo`,
`e.multGammasig`'s product exponent `(1-sigma) sigma_2/((1-sigma)+sigma_2)`
equals the power lane's `(1-sigma)/p`. -/
theorem prodSigma_bfaSigmaTwo_eq_bfaTau {sigma gam b : ℝ} (hsigma : sigma < 1)
    (hgam : 0 < gam) (hb : 0 < b) :
    (1 - sigma) * bfaSigmaTwo sigma gam b / ((1 - sigma) + bfaSigmaTwo sigma gam b)
      = bfaTau sigma gam b := by
  have hp1 : 1 < bfaPower gam b := one_lt_bfaPower hgam hb
  have hs : 0 < 1 - sigma := by linarith
  have hpm : bfaPower gam b - 1 ≠ 0 := by linarith
  have hp0 : bfaPower gam b ≠ 0 := by linarith
  rw [bfaSigmaTwo, bfaTau]
  field_simp
  rw [sub_add_cancel, div_self hp0]


/-- The truncated prefactor, `3^{gamma hsep} 1_{gamma hsep > 3^{-4}}`. -/
def slstarCollapseTerm (M : ABKModel d) (m : ℤ) (E b gam : ℝ)
    (omega : CutoffSample d) : ℝ :=
  (3 : ℝ) ^ (gam * (hsep M m E b omega : ℝ)) *
    (if (81 : ℝ)⁻¹ < gam * (hsep M m E b omega : ℝ) then (1 : ℝ) else 0)

/-- The collar power `3^{(gamma+2b) hsep}` carried by the improved
exponential. -/
def slstarPowerTerm (M : ABKModel d) (m : ℤ) (E b gam : ℝ)
    (omega : CutoffSample d) : ℝ :=
  (3 : ℝ) ^ ((gam + 2 * b) * (hsep M m E b omega : ℝ))

/-- The Orlicz lane of `e.slstar.multiscale`: the whole random part of the
Step-3 right-hand side. -/
def bfaLane (M : ABKModel d) (m : ℤ) (E b gam Cpre eps : ℝ)
    (omega : CutoffSample d) : ℝ :=
  Cpre * slstarCollapseTerm M m E b gam omega
    + Cpre * eps * slstarPowerTerm M m E b gam omega

theorem slstarCollapseTerm_nonneg (M : ABKModel d) (m : ℤ) (E b gam : ℝ)
    (omega : CutoffSample d) : 0 ≤ slstarCollapseTerm M m E b gam omega := by
  rw [slstarCollapseTerm]
  refine mul_nonneg (Real.rpow_nonneg (by norm_num) _) ?_
  by_cases h : (81 : ℝ)⁻¹ < gam * (hsep M m E b omega : ℝ)
  · rw [ite_eq_left h]; norm_num
  · rw [ite_eq_right h]

theorem slstarPowerTerm_nonneg (M : ABKModel d) (m : ℤ) (E b gam : ℝ)
    (omega : CutoffSample d) : 0 ≤ slstarPowerTerm M m E b gam omega :=
  Real.rpow_nonneg (by norm_num) _

theorem bfaLane_nonneg (M : ABKModel d) (m : ℤ) {E b gam Cpre eps : ℝ}
    (hCpre : 0 ≤ Cpre) (heps : 0 ≤ eps) (omega : CutoffSample d) :
    0 ≤ bfaLane M m E b gam Cpre eps omega :=
  add_nonneg (mul_nonneg hCpre (slstarCollapseTerm_nonneg M m E b gam omega))
    (mul_nonneg (mul_nonneg hCpre heps) (slstarPowerTerm_nonneg M m E b gam omega))

theorem measurable_bfaLane (M : ABKModel d) (m : ℤ) (E b gam Cpre eps : ℝ) :
    Measurable (bfaLane M m E b gam Cpre eps) := by
  have h1 : Measurable fun omega : CutoffSample d =>
      slstarCollapseTerm M m E b gam omega :=
    measurable_comp_hsep M m E b
      (fun j => (3 : ℝ) ^ (gam * (j : ℝ)) *
        (if (81 : ℝ)⁻¹ < gam * (j : ℝ) then (1 : ℝ) else 0))
  have h2 : Measurable fun omega : CutoffSample d =>
      slstarPowerTerm M m E b gam omega :=
    measurable_comp_hsep M m E b (fun j => (3 : ℝ) ^ ((gam + 2 * b) * (j : ℝ)))
  exact (h1.const_mul Cpre).add (h2.const_mul (Cpre * eps))

/-- **The Step-3 payload split into a constant and the lane** (the replacement
deterministic step, times the collar power). -/
theorem step3Payload_le_two_mul_add_bfaLane (M : ABKModel d) (m : ℤ)
    {E b gam Cpre eps : ℝ} (hgam : 0 ≤ gam) (hCpre : 0 ≤ Cpre)
    (omega : CutoffSample d) :
    Cpre * ((3 : ℝ) ^ (gam * (hsep M m E b omega : ℝ)) *
        (1 + (3 : ℝ) ^ (2 * b * (hsep M m E b omega : ℝ)) * eps))
      ≤ 2 * Cpre + bfaLane M m E b gam Cpre eps omega := by
  have hx : (0 : ℝ) ≤ gam * (hsep M m E b omega : ℝ) :=
    mul_nonneg hgam (Nat.cast_nonneg _)
  have hdet : (3 : ℝ) ^ (gam * (hsep M m E b omega : ℝ))
      ≤ 2 + slstarCollapseTerm M m E b gam omega := by
    have h := three_rpow_le_two_add_indicator hx
    rw [slstarCollapseTerm]
    by_cases hcase : (81 : ℝ)⁻¹ < gam * (hsep M m E b omega : ℝ)
    · rw [ite_eq_left hcase] at h ⊢
      linarith
    · rw [ite_eq_right hcase] at h ⊢
      linarith
  have hprod : (3 : ℝ) ^ (gam * (hsep M m E b omega : ℝ)) *
      (3 : ℝ) ^ (2 * b * (hsep M m E b omega : ℝ))
        = slstarPowerTerm M m E b gam omega := by
    rw [slstarPowerTerm, ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hexpand : Cpre * ((3 : ℝ) ^ (gam * (hsep M m E b omega : ℝ)) *
      (1 + (3 : ℝ) ^ (2 * b * (hsep M m E b omega : ℝ)) * eps))
      = Cpre * (3 : ℝ) ^ (gam * (hsep M m E b omega : ℝ))
        + Cpre * eps * ((3 : ℝ) ^ (gam * (hsep M m E b omega : ℝ)) *
            (3 : ℝ) ^ (2 * b * (hsep M m E b omega : ℝ))) := by ring
  rw [hexpand, hprod, bfaLane]
  have hmul := mul_le_mul_of_nonneg_left hdet hCpre
  linarith

/-- **The collar power at `Gamma_{(1-sigma)/p}`**'s power route: `e.hsep.tails`
controls `3^{b hsep}` at `Gamma_{1-sigma}` and amplitude `hsepAmplitude sigma
b`; raising to `p = (gamma+2b)/b` gives the collar power. -/
theorem isBigOWith_gammaSigma_slstarPowerTerm_of_gates (M : ABKModel d) {m : ℤ}
    {E sigma b gam : ℝ} (hd : 2 ≤ d) (hE : 1 ≤ E)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) ⟨E, hE⟩)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b) (hb1 : b ≤ 1 / 8)
    (hEexp : Real.exp (badClustersConst d / sigma) ≤ E)
    (hE4 : 4 ≤ E) (hunit : BadEvents.unitGate M) (hgamma20 : M.gamma ≤ 1 / 20)
    (hinvSq : E⁻¹ ^ 2 ≤ Algsuperdiff.Section3.Disorder.cstar M)
    (hEb : badClustersConst d / b ≤ E)
    (hgammaE : M.gamma ≤ E ^ (-5 : ℤ)) (hgam : 0 < gam) :
    IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma (bfaTau sigma gam b))
      (slstarPowerTerm M m E b gam)
      (hsepAmplitude sigma b ^ bfaPower gam b) := by
  have hp : 0 < bfaPower gam b := bfaPower_pos hgam hb0
  have hbase := isBigOWith_gammaSigma_three_rpow_hsep_of_gates M hd hE hS hsigma0
    hsigma hb0 hb1 hEexp hE4 hunit hgamma20 hinvSq hEb hgammaE
  have hnn : ∀ omega : CutoffSample d,
      (0 : ℝ) ≤ (3 : ℝ) ^ (b * (hsep M m E b omega : ℝ)) :=
    fun omega => Real.rpow_nonneg (by norm_num) _
  have hpow := (Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_rpow_iff_of_nonneg
    (μ := (cutoffSampleLaw M).toMeasure)
    (X := fun omega => (3 : ℝ) ^ (b * (hsep M m E b omega : ℝ)))
    (K := hsepAmplitude sigma b) (σ := 1 - sigma) (p := bfaPower gam b)
    hp (hsepAmplitude_pos sigma b).le hnn).1 hbase
  have hbne : b ≠ 0 := ne_of_gt hb0
  refine isBigOWith_gammaSigma_of_le (fun omega => le_of_eq ?_) hpow
  rw [slstarPowerTerm, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3), bfaPower]
  congr 1
  field_simp


/-- The explicit scale of the Orlicz lane: `e.multGammasig`'s constant times
`e.hsep.tails`' amplitude times `e.indc.O.sigma`'s `exp(-c gamma^{-1})`-sized
scale, plus `eps` times the collar power's amplitude, all through the two-term
`l.Gamma.sigma.triangle`. -/
def bfaLaneScale (sigma b gam Cpre eps : ℝ) : ℝ :=
  gammaTriangleConst (bfaTau sigma gam b) *
    (Cpre * (HCPolySupport.Book.Ch04.gammaProductConst (1 - sigma)
        (bfaSigmaTwo sigma gam b) * hsepAmplitude sigma b *
        truncationIndicatorScale b sigma (bfaSigmaTwo sigma gam b)
          (hsepAmplitude sigma b) ⌊(81 * gam)⁻¹⌋₊)
      + Cpre * eps * (hsepAmplitude sigma b ^ bfaPower gam b))

/-- The lane's scale is positive, as the consumers' `hA` slot requires. -/
theorem bfaLaneScale_pos {sigma b gam Cpre eps : ℝ} (hCpre : 0 < Cpre)
    (heps : 0 < eps) :
    0 < bfaLaneScale sigma b gam Cpre eps := by
  have hKpos : 0 < hsepAmplitude sigma b := hsepAmplitude_pos sigma b
  have hprodpos : 0 < HCPolySupport.Book.Ch04.gammaProductConst (1 - sigma)
      (bfaSigmaTwo sigma gam b) := Real.rpow_pos_of_pos (by norm_num) _
  rw [bfaLaneScale]
  refine mul_pos gammaTriangleConst_pos (add_pos ?_ ?_)
  · exact mul_pos hCpre (mul_pos (mul_pos hprodpos hKpos)
      (truncationIndicatorScale_pos hKpos _))
  · exact mul_pos (mul_pos hCpre heps) (Real.rpow_pos_of_pos hKpos _)

/-- **The Orlicz lane of `e.slstar.multiscale`, at one exponent and an explicit
scale.**  Both lanes are put at `bfaTau` --- the truncated prefactor by the
product rule at `sigma_2`, the collar power by the power rule --- and added by
the two-term `l.Gamma.sigma.triangle`.  By `bfaTau_eq_half_one_sub_bfaSigmaPrime`
this exponent is the printed `Gamma_{(1-sigma')/2}` at the relabelled `sigma'`. -/
theorem isBigOWith_gammaSigma_bfaLane_of_gates (M : ABKModel d) {m : ℤ}
    {E sigma b gam Cpre eps : ℝ} (hd : 2 ≤ d) (hE : 1 ≤ E)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) ⟨E, hE⟩)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b) (hb1 : b ≤ 1 / 8)
    (hEexp : Real.exp (badClustersConst d / sigma) ≤ E)
    (hE4 : 4 ≤ E) (hunit : BadEvents.unitGate M) (hgamma20 : M.gamma ≤ 1 / 20)
    (hinvSq : E⁻¹ ^ 2 ≤ Algsuperdiff.Section3.Disorder.cstar M)
    (hEb : badClustersConst d / b ≤ E)
    (hgammaE : M.gamma ≤ E ^ (-5 : ℤ)) (hgam : 0 < gam) (hgammab : gam ≤ b)
    (hCpre : 0 < Cpre) (heps : 0 < eps) :
    IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma (bfaTau sigma gam b))
      (bfaLane M m E b gam Cpre eps) (bfaLaneScale sigma b gam Cpre eps) := by
  have hs1 : sigma < 1 := by linarith
  have htau : 0 < bfaTau sigma gam b := bfaTau_pos hs1 hgam hb0
  have hsigma2 : 0 < bfaSigmaTwo sigma gam b := bfaSigmaTwo_pos hs1 hgam hb0
  have hcollapse := isBigOWith_gammaSigma_three_rpow_gamma_hsep_mul_indicator_of_gates M
    hd hE hS hsigma0 hsigma hsigma2 hb0 hb1 hEexp hE4 hunit hgamma20 hinvSq hEb
    hgammaE hgam hgammab
  rw [prodSigma_bfaSigmaTwo_eq_bfaTau hs1 hgam hb0] at hcollapse
  have hpower := isBigOWith_gammaSigma_slstarPowerTerm_of_gates M hd hE hS hsigma0
    hsigma hb0 hb1 hEexp hE4 hunit hgamma20 hinvSq hEb hgammaE hgam
  have hKpos : 0 < hsepAmplitude sigma b := hsepAmplitude_pos sigma b
  have h1 : IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma (bfaTau sigma gam b))
      (fun omega => Cpre * slstarCollapseTerm M m E b gam omega)
      (Cpre * (HCPolySupport.Book.Ch04.gammaProductConst (1 - sigma)
        (bfaSigmaTwo sigma gam b) * hsepAmplitude sigma b *
        truncationIndicatorScale b sigma (bfaSigmaTwo sigma gam b)
          (hsepAmplitude sigma b) ⌊(81 * gam)⁻¹⌋₊)) :=
    hcollapse.const_mul hCpre.le
  have h2 : IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma (bfaTau sigma gam b))
      (fun omega => Cpre * eps * slstarPowerTerm M m E b gam omega)
      (Cpre * eps * (hsepAmplitude sigma b ^ bfaPower gam b)) :=
    hpower.const_mul (mul_nonneg hCpre.le heps.le)
  have hprodpos : 0 < HCPolySupport.Book.Ch04.gammaProductConst (1 - sigma)
      (bfaSigmaTwo sigma gam b) := Real.rpow_pos_of_pos (by norm_num) _
  have hm1 : Measurable fun omega : CutoffSample d =>
      Cpre * slstarCollapseTerm M m E b gam omega :=
    (measurable_comp_hsep M m E b
      (fun j => (3 : ℝ) ^ (gam * (j : ℝ)) *
        (if (81 : ℝ)⁻¹ < gam * (j : ℝ) then (1 : ℝ) else 0))).const_mul Cpre
  have hm2 : Measurable fun omega : CutoffSample d =>
      Cpre * eps * slstarPowerTerm M m E b gam omega :=
    (measurable_comp_hsep M m E b
      (fun j => (3 : ℝ) ^ ((gam + 2 * b) * (j : ℝ)))).const_mul (Cpre * eps)
  exact isBigOWith_gammaSigma_add htau
    (fun omega => mul_nonneg hCpre.le (slstarCollapseTerm_nonneg M m E b gam omega))
    (fun omega => mul_nonneg (mul_nonneg hCpre.le heps.le)
      (slstarPowerTerm_nonneg M m E b gam omega))
    hm1 hm2
    (mul_pos hCpre (mul_pos (mul_pos hprodpos hKpos)
      (truncationIndicatorScale_pos hKpos _)))
    (mul_pos (mul_pos hCpre heps) (Real.rpow_pos_of_pos hKpos _))
    h1 h2


/-! ## 6. Generic composed-leg adapters

The following theorems conditionally adapt explicitly supplied
descendant-indexed estimates to the proved payload consumers.  They discharge
only the abstract majorant plumbing; they neither establish the source per-cube
estimate nor reduce O1/O2 to a root `hpay`.  The faithful local,
almost-everywhere shape needed to produce such data is recorded separately in
`BfaLocalLane.lean`. -/


end

end Algsuperdiff.Section3.Provider.Multiscale
