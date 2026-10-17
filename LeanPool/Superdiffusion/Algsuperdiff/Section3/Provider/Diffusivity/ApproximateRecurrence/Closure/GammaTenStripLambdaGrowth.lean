/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenStripMoment

/-!
# GammaTenStripLambdaGrowth

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The **growth rate in the localization scale** of the strip ellipticity moment

ABK26, Step 2 of `l.approximate.recurrence.formula`, `e.CG.bounds.2`.

## The gap this module fills

`Closure.GammaTenStripMoment.stripLambdaMoment M m Q` is finite at every cube
`Q`, and that module states plainly that no `Q`-independence is claimed: the
local control it integrates lives at the cover scale
`Cutoff.cubeOriginCoverScale Q`, and the lower-tail law makes its moments grow
with that scale.

The strip gate of `Closure.GammaTenStripAssembly` pays
`sqrt(d 3^{g-p}) sqrt(Cstrip)` with `p` growing **linearly** in the
localization scale `K` and `g` fixed, against a `Cstrip` that carries
`stripLambdaMoment M m (originCube d K)`.  Finiteness alone is therefore not
enough: the gate needs a *rate*.  This module supplies it, and the rate is
**polynomial**: degree eight in `K`, against a geometric `3^{-p}`.

## What is proved

* `closure_openCubeSet_originCube_subset`, `cubeOriginCoverScale_originCube_le`
  --- the canonical origin cover of `cu_K` sits at scale at most `K+1`.  The
  closure of an open origin cube is inside the closed cube one scale up, and
  minimality of `Nat.find` does the rest.
* `stripShellBudget` and `tsum_cutoffGammaMajorant_le` --- the summable
  lower-shell `Γ₂` budget of `Cutoff.HighMoments.cutoffGammaMajorant`, split as
  `(1 + |ell - m|)` times a factor free of the cube scale `ell`.  The split is
  the elementary majorant `sqrt(1 + max(ell - (m-r), 0)) <= (1+|ell-m|)(1+r)`
  against the geometric weight `3^{gamma(m-r)}`.
* `integral_one_add_cutoffLocalControl_pow_le` --- for `1 <= q <= 8`,
  `E[(1+u_ell)^q] <= 2^{q+1} S^8`, where `S = stripControlScale` is the
  `Γ₂` witness scale of `Cutoff.HighMoments.hasGammaMomentGrowthWith_cutoffLocalControl`
  capped below at one.  The only probabilistic input is that witness; the rest
  is `1+u <= 2 max(1,u)` and `max(1,u)^q <= 1 + u^q`.
* `stripLambdaMoment_le` --- the second moment of the Step-2 ellipticity weight
  at the envelope of `Q`, bounded by `stripLambdaGrowthConst M` times the eighth
  power of the witness scale at `cubeOriginCoverScale Q`.
* `stripLambdaMoment_originCube_le` --- **the module's target**:
  `stripLambdaMoment M m (cu_K) <= stripLambdaGrowthConst M
   (stripControlBase M m (1 + K))^8`, an explicit degree-eight polynomial in the
  localization scale `K` whose coefficients do not depend on `K`.
* `eventually_poly_le_geometric` --- the arithmetic the gate then uses: a fixed
  multiple of `(1+K)^8` is eventually below any fixed positive multiple of
  `3^K`.

## Binders

Everything below is **unconditional** in the model: no smallness of `cgamma`, no
`inductionState`, no regime, no direction normalization and no measurable
selection occurs.  `M.shellPrefix.gamma_pos` is the only model fact used, and it
is a field of `ABKModel`.

## Scope

Internal Provider infrastructure for the Step-2 boundary-strip gate.  There is
no `sorry`, no `admit`, no custom axiom and no `set_option maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2, `e.CG.bounds.2`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open Set
open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-! ## The cover scale of the localization cube -/

/-- The closure of an open origin cube is inside the open origin cube one scale
up.  Unconditional. -/
theorem closure_openCubeSet_originCube_subset (m : ℤ) :
    closure (openCubeSet (originCube d m)) ⊆ openCubeSet (originCube d (m + 1)) := by
  have h3 : (3 : ℝ) ^ m < (3 : ℝ) ^ (m + 1) :=
    zpow_lt_zpow_right₀ (by norm_num) (by omega)
  set C : Set (Vec d) :=
    Set.pi Set.univ fun _ : Fin d =>
      Set.Icc (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) ((1 / 2 : ℝ) * (3 : ℝ) ^ m) with hC
  have hCclosed : IsClosed C := isClosed_set_pi fun _ _ => isClosed_Icc
  have hsub : openCubeSet (originCube d m) ⊆ C := by
    intro x hx
    rw [mem_openCubeSet_originCube_iff] at hx
    intro i _
    exact ⟨(hx i).1.le, (hx i).2.le⟩
  refine (closure_minimal hsub hCclosed).trans ?_
  intro x hx
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hxi := hx i (Set.mem_univ i)
  rw [Set.mem_Icc] at hxi
  exact ⟨by linarith [hxi.1], by linarith [hxi.2]⟩

/-- The canonical origin cover of `cu_K` is at scale at most `K+1`.
Unconditional. -/
theorem cubeOriginCoverScale_originCube_le (K : ℕ) :
    cubeOriginCoverScale (originCube d (K : ℤ)) ≤ (K : ℤ) + 1 := by
  have h : cubeOriginCoverDepth (originCube d (K : ℤ)) ≤ K + 1 := by
    refine cubeOriginCoverDepth_le _ (K + 1) ?_
    have hcast : ((K + 1 : ℕ) : ℤ) = (K : ℤ) + 1 := by push_cast; ring
    rw [hcast]
    exact closure_openCubeSet_originCube_subset (d := d) (K : ℤ)
  unfold cubeOriginCoverScale
  exact_mod_cast h

/-- The canonical origin cover scale is nonnegative: it is a natural number.
Unconditional. -/
theorem cubeOriginCoverScale_nonneg (Q : TriadicCube d) :
    (0 : ℤ) ≤ cubeOriginCoverScale Q := Int.natCast_nonneg _

/-! ## Elementary real facts -/

/-- `Real.rpow` at base three, in the `^` spelling. -/
private theorem rpow_three_eq (x : ℝ) : Real.rpow 3 x = (3 : ℝ) ^ x := rfl

/-- Above one, the square root is below the argument.  A local copy of
`Closure.GammaTenGaugeScalarCap.sqrt_le_self_of_one_le`, which the present
module's own import closure does not reach. -/
private theorem sqrt_le_self_of_one_le' {t : ℝ} (h : 1 ≤ t) : Real.sqrt t ≤ t := by
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one h
  calc Real.sqrt t ≤ Real.sqrt (t * t) := Real.sqrt_le_sqrt (le_mul_of_one_le_left ht0 h)
    _ = t := Real.sqrt_mul_self ht0

/-- The geometric ratio of the lower-shell budget is below one. -/
private theorem rpow_neg_gamma_lt_one {gamma : ℝ} (hgamma : 0 < gamma) :
    (3 : ℝ) ^ (-gamma) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_iff_pos.2 hgamma)

/-- A geometric series with a linear weight is summable. -/
private theorem summable_one_add_mul_geometric {rho : ℝ} (h0 : 0 ≤ rho) (h1 : rho < 1) :
    Summable (fun r : ℕ => (1 + (r : ℝ)) * rho ^ r) := by
  have hgeo : Summable (fun r : ℕ => rho ^ r) := summable_geometric_of_lt_one h0 h1
  have hnorm : ‖rho‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg h0]
  have hpow : Summable (fun r : ℕ => (r : ℝ) ^ (1 : ℕ) * rho ^ r) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have hpow' : Summable (fun r : ℕ => (r : ℝ) * rho ^ r) := by
    simpa only [pow_one] using hpow
  refine (hgeo.add hpow').congr fun r => ?_
  ring

/-! ## The lower-shell budget, split off the cube scale -/

/-- **The cube-scale-free lower-shell budget.**  The `Γ₂` budget
`Cutoff.HighMoments.cutoffGammaMajorant` with its cube-scale factor replaced by
the linear majorant `1 + r`. -/
def stripShellBudget (d : ℕ) (gamma : ℝ) (m : ℤ) : ℝ :=
  ∑' r : ℕ, Real.exp 1 * gaussianMaximumDimConst d * (1 + (r : ℝ)) *
    Real.rpow 3 (gamma * ((m : ℝ) - (r : ℝ)))

theorem summable_stripShellBudgetTerm (d : ℕ) {gamma : ℝ} (hgamma : 0 < gamma) (m : ℤ) :
    Summable (fun r : ℕ => Real.exp 1 * gaussianMaximumDimConst d * (1 + (r : ℝ)) *
      Real.rpow 3 (gamma * ((m : ℝ) - (r : ℝ)))) := by
  have hs := summable_one_add_mul_geometric (rho := (3 : ℝ) ^ (-gamma))
    (Real.rpow_nonneg (by norm_num) _) (rpow_neg_gamma_lt_one hgamma)
  refine (hs.mul_left (Real.exp 1 * gaussianMaximumDimConst d *
    (3 : ℝ) ^ (gamma * (m : ℝ)))).congr fun r => ?_
  simp only [rpow_three_eq]
  have h1 : ((3 : ℝ) ^ (-gamma)) ^ r = (3 : ℝ) ^ (-gamma * (r : ℝ)) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-gamma)) r,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hsplit : (3 : ℝ) ^ (gamma * ((m : ℝ) - (r : ℝ))) =
      (3 : ℝ) ^ (gamma * (m : ℝ)) * ((3 : ℝ) ^ (-gamma)) ^ r := by
    rw [h1, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  rw [hsplit]
  ring

theorem stripShellBudget_nonneg (d : ℕ) (gamma : ℝ) (m : ℤ) :
    0 ≤ stripShellBudget d gamma m := by
  refine tsum_nonneg fun r => ?_
  have hG : (0 : ℝ) < gaussianMaximumDimConst d := gaussianMaximumDimConst_pos d
  have hr : (0 : ℝ) ≤ Real.rpow 3 (gamma * ((m : ℝ) - (r : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hpre : (0 : ℝ) ≤ Real.exp 1 * gaussianMaximumDimConst d * (1 + (r : ℝ)) := by
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    positivity
  exact mul_nonneg hpre hr

/-- **The `Γ₂` budget at cube scale `ell`, split.**  The cube scale enters only
through the linear factor `1 + |ell - m|`.

on `0 < gamma` alone. -/
theorem tsum_cutoffGammaMajorant_le (d : ℕ) {gamma : ℝ} (hgamma : 0 < gamma) (m ell : ℤ) :
    ∑' r : ℕ, cutoffGammaMajorant d gamma m ell r ≤
      (1 + |(ell : ℝ) - (m : ℝ)|) * stripShellBudget d gamma m := by
  have hG : (0 : ℝ) < gaussianMaximumDimConst d := gaussianMaximumDimConst_pos d
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hsum1 : Summable (cutoffGammaMajorant d gamma m ell) :=
    summable_cutoffGammaMajorant hgamma m ell
  have hsum2 := summable_stripShellBudgetTerm d hgamma m
  have hterm : ∀ r : ℕ, cutoffGammaMajorant d gamma m ell r ≤
      (1 + |(ell : ℝ) - (m : ℝ)|) *
        (Real.exp 1 * gaussianMaximumDimConst d * (1 + (r : ℝ)) *
          Real.rpow 3 (gamma * ((m : ℝ) - (r : ℝ)))) := by
    intro r
    set A : ℝ := |(ell : ℝ) - (m : ℝ)| with hAdef
    have hA : (0 : ℝ) ≤ A := abs_nonneg _
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have hP1 : (1 : ℝ) ≤ (1 + A) * (1 + (r : ℝ)) := by nlinarith
    have hmax : max ((ell : ℝ) - ((m : ℝ) - (r : ℝ))) 0 ≤ A + (r : ℝ) := by
      refine max_le ?_ (by linarith)
      have hle : (ell : ℝ) - (m : ℝ) ≤ A := le_abs_self _
      linarith
    have ht : 1 + max ((ell : ℝ) - ((m : ℝ) - (r : ℝ))) 0 ≤ (1 + A) * (1 + (r : ℝ)) := by
      nlinarith
    have hsq : Real.sqrt (1 + max ((ell : ℝ) - ((m : ℝ) - (r : ℝ))) 0) ≤
        (1 + A) * (1 + (r : ℝ)) :=
      le_trans (Real.sqrt_le_sqrt ht) (sqrt_le_self_of_one_le' hP1)
    have hrpow : (0 : ℝ) ≤ Real.rpow 3 (gamma * ((m : ℝ) - (r : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    have hstep : Real.sqrt (1 + max ((ell : ℝ) - ((m : ℝ) - (r : ℝ))) 0) *
        Real.rpow 3 (gamma * ((m : ℝ) - (r : ℝ))) ≤
          ((1 + A) * (1 + (r : ℝ))) * Real.rpow 3 (gamma * ((m : ℝ) - (r : ℝ))) :=
      mul_le_mul_of_nonneg_right hsq hrpow
    unfold cutoffGammaMajorant expectedCubeMajorant cubeMajorant
    calc Real.exp 1 * (gaussianMaximumDimConst d *
            (Real.sqrt (1 + max ((ell : ℝ) - ((m : ℝ) - (r : ℝ))) 0) *
              Real.rpow 3 (gamma * ((m : ℝ) - (r : ℝ)))))
        ≤ Real.exp 1 * (gaussianMaximumDimConst d *
            (((1 + A) * (1 + (r : ℝ))) *
              Real.rpow 3 (gamma * ((m : ℝ) - (r : ℝ))))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep hG.le) he.le
      _ = (1 + A) * (Real.exp 1 * gaussianMaximumDimConst d * (1 + (r : ℝ)) *
            Real.rpow 3 (gamma * ((m : ℝ) - (r : ℝ)))) := by ring
  calc ∑' r : ℕ, cutoffGammaMajorant d gamma m ell r
      ≤ ∑' r : ℕ, (1 + |(ell : ℝ) - (m : ℝ)|) *
          (Real.exp 1 * gaussianMaximumDimConst d * (1 + (r : ℝ)) *
            Real.rpow 3 (gamma * ((m : ℝ) - (r : ℝ)))) :=
        Summable.tsum_le_tsum hterm hsum1 (hsum2.mul_left _)
    _ = (1 + |(ell : ℝ) - (m : ℝ)|) * stripShellBudget d gamma m := by
        rw [tsum_mul_left]
        rfl

/-! ## The moments of the local control, quantitatively -/

/-- **The `Γ₂` witness scale of the cutoff local control, capped below at one.**
Three times the witness of
`Cutoff.HighMoments.hasGammaMomentGrowthWith_cutoffLocalControl`; the factor
three absorbs `sqrt q` for `q <= 9`, and the cap keeps the eighth power
monotone. -/
def stripControlScale (M : ABKModel d) (ell m : ℤ) : ℝ :=
  max 1 (3 * (IndependentSums.gammaMomentConst 2 *
    (IndependentSums.gammaTriangleConst 2 *
      ∑' r : ℕ, cutoffGammaMajorant d M.gamma m ell r)))

theorem one_le_stripControlScale (M : ABKModel d) (ell m : ℤ) :
    1 ≤ stripControlScale M ell m := le_max_left _ _

theorem stripControlScale_nonneg (M : ABKModel d) (ell m : ℤ) :
    0 ≤ stripControlScale M ell m :=
  le_trans zero_le_one (one_le_stripControlScale M ell m)

/-- The `q`-th moment of the local control is below the `q`-th power of the
capped witness scale, for `q <= 9`.  Unconditional. -/
theorem integral_cutoffLocalControl_pow_le (M : ABKModel d) (ell m : ℤ) {q : ℕ}
    (hq1 : 1 ≤ q) (hq9 : q ≤ 9) :
    ∫ omega, cutoffLocalControl ell m omega ^ q ∂(cutoffSampleLaw M).toMeasure ≤
      stripControlScale M ell m ^ q := by
  set Kell : ℝ := IndependentSums.gammaMomentConst 2 *
    (IndependentSums.gammaTriangleConst 2 *
      ∑' r : ℕ, cutoffGammaMajorant d M.gamma m ell r) with hKell
  have hKell0 : 0 ≤ Kell := by
    have h1 : (0 : ℝ) < IndependentSums.gammaMomentConst 2 :=
      IndependentSums.gammaMomentConst_pos (by norm_num)
    have h2 : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
      IndependentSums.gammaTriangleConst_pos
    have h3 : (0 : ℝ) ≤ ∑' r : ℕ, cutoffGammaMajorant d M.gamma m ell r :=
      tsum_nonneg fun r => (cutoffGammaMajorant_pos d M.gamma m ell r).le
    rw [hKell]
    positivity
  have hgrowth := hasGammaMomentGrowthWith_cutoffLocalControl M ell m
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  obtain ⟨-, hbd⟩ := hgrowth hq1R
  -- the exponent factor `q^{1/2}` is below three
  have hqle : ((q : ℝ)) ^ ((2 : ℝ)⁻¹) ≤ 3 := by
    have h9 : (q : ℝ) ≤ 9 := by exact_mod_cast hq9
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    have hmono : ((q : ℝ)) ^ ((2 : ℝ)⁻¹) ≤ (9 : ℝ) ^ ((2 : ℝ)⁻¹) :=
      Real.rpow_le_rpow hq0 h9 (by norm_num)
    have hval : (9 : ℝ) ^ ((2 : ℝ)⁻¹) = 3 := by
      have h1 : (9 : ℝ) ^ ((2 : ℝ)⁻¹) = Real.sqrt 9 := by
        rw [Real.sqrt_eq_rpow]
        norm_num
      rw [h1, show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
    rwa [hval] at hmono
  -- rewrite the two `rpow` sides as natural powers
  have habs : ∀ omega : CutoffSample d,
      |cutoffLocalControl ell m omega| ^ ((q : ℕ) : ℝ) =
        cutoffLocalControl ell m omega ^ q := by
    intro omega
    rw [abs_of_nonneg (cutoffLocalControl_nonneg ell m omega), Real.rpow_natCast]
  have hleft : ∫ omega, |cutoffLocalControl ell m omega| ^ ((q : ℕ) : ℝ)
      ∂(cutoffSampleLaw M).toMeasure =
      ∫ omega, cutoffLocalControl ell m omega ^ q ∂(cutoffSampleLaw M).toMeasure := by
    exact integral_congr_ae (Filter.Eventually.of_forall habs)
  have hright : (Kell * ((q : ℝ)) ^ ((2 : ℝ)⁻¹)) ^ ((q : ℕ) : ℝ) ≤
      stripControlScale M ell m ^ q := by
    have hb0 : (0 : ℝ) ≤ Kell * ((q : ℝ)) ^ ((2 : ℝ)⁻¹) :=
      mul_nonneg hKell0 (Real.rpow_nonneg (Nat.cast_nonneg q) _)
    have hb : Kell * ((q : ℝ)) ^ ((2 : ℝ)⁻¹) ≤ stripControlScale M ell m := by
      have h1 : Kell * ((q : ℝ)) ^ ((2 : ℝ)⁻¹) ≤ Kell * 3 :=
        mul_le_mul_of_nonneg_left hqle hKell0
      have h2 : Kell * 3 ≤ stripControlScale M ell m := by
        have := le_max_right (1 : ℝ) (3 * Kell)
        rw [stripControlScale, ← hKell]
        linarith [le_max_right (1 : ℝ) (3 * Kell)]
      linarith
    calc (Kell * ((q : ℝ)) ^ ((2 : ℝ)⁻¹)) ^ ((q : ℕ) : ℝ)
        ≤ (stripControlScale M ell m) ^ ((q : ℕ) : ℝ) :=
          Real.rpow_le_rpow hb0 hb (Nat.cast_nonneg q)
      _ = stripControlScale M ell m ^ q := Real.rpow_natCast _ q
  rw [← hleft]
  exact le_trans hbd hright

/-- **The shifted moment.**  For `1 <= q <= 8`,
`E[(1+u)^q] <= 2^{q+1} S^8`.  Unconditional. -/
theorem integral_one_add_cutoffLocalControl_pow_le (M : ABKModel d) (ell m : ℤ) {q : ℕ}
    (hq1 : 1 ≤ q) (hq8 : q ≤ 8) :
    ∫ omega, (1 + cutoffLocalControl ell m omega) ^ q ∂(cutoffSampleLaw M).toMeasure ≤
      2 ^ (q + 1) * stripControlScale M ell m ^ 8 := by
  have hS1 : 1 ≤ stripControlScale M ell m := one_le_stripControlScale M ell m
  have hS0 : 0 ≤ stripControlScale M ell m := stripControlScale_nonneg M ell m
  have hintU : Integrable (fun omega : CutoffSample d =>
      cutoffLocalControl ell m omega ^ q) (cutoffSampleLaw M).toMeasure :=
    integrable_cutoffLocalControl_pow M ell m q
  have hint1U : Integrable (fun omega : CutoffSample d =>
      (1 + cutoffLocalControl ell m omega) ^ q) (cutoffSampleLaw M).toMeasure :=
    integrable_one_add_cutoffLocalControl_pow M ell m q
  have hmaj : Integrable (fun omega : CutoffSample d =>
      2 ^ q * (1 + cutoffLocalControl ell m omega ^ q))
      (cutoffSampleLaw M).toMeasure :=
    ((integrable_const (1 : ℝ)).add hintU).const_mul _
  have hptw : ∀ omega : CutoffSample d,
      (1 + cutoffLocalControl ell m omega) ^ q ≤
        2 ^ q * (1 + cutoffLocalControl ell m omega ^ q) := by
    intro omega
    set u : ℝ := cutoffLocalControl ell m omega with hu
    have hu0 : 0 ≤ u := cutoffLocalControl_nonneg ell m omega
    rcases le_total u 1 with hle | hle
    · have h1 : (1 + u) ^ q ≤ (2 : ℝ) ^ q :=
        pow_le_pow_left₀ (by linarith) (by linarith) q
      have h2 : (0 : ℝ) ≤ u ^ q := pow_nonneg hu0 q
      have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ q := by positivity
      nlinarith
    · have h1 : (1 + u) ^ q ≤ (2 * u) ^ q :=
        pow_le_pow_left₀ (by linarith) (by linarith) q
      have h2 : (2 * u) ^ q = 2 ^ q * u ^ q := by rw [mul_pow]
      have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ q := by positivity
      nlinarith
  have hstep := integral_mono hint1U hmaj hptw
  have hval : ∫ omega, 2 ^ q * (1 + cutoffLocalControl ell m omega ^ q)
      ∂(cutoffSampleLaw M).toMeasure =
      2 ^ q * (1 + ∫ omega, cutoffLocalControl ell m omega ^ q
        ∂(cutoffSampleLaw M).toMeasure) := by
    rw [integral_const_mul, integral_add (integrable_const (1 : ℝ)) hintU]
    simp
  rw [hval] at hstep
  have hmom : ∫ omega, cutoffLocalControl ell m omega ^ q ∂(cutoffSampleLaw M).toMeasure ≤
      stripControlScale M ell m ^ q :=
    integral_cutoffLocalControl_pow_le M ell m hq1 (le_trans hq8 (by norm_num))
  have hpowle : stripControlScale M ell m ^ q ≤ stripControlScale M ell m ^ 8 :=
    pow_le_pow_right₀ hS1 hq8
  have hone : (1 : ℝ) ≤ stripControlScale M ell m ^ 8 := one_le_pow₀ hS1
  have h2q : (0 : ℝ) ≤ (2 : ℝ) ^ q := by positivity
  have hsum : (1 : ℝ) +
      ∫ omega, cutoffLocalControl ell m omega ^ q ∂(cutoffSampleLaw M).toMeasure ≤
        2 * stripControlScale M ell m ^ 8 := by linarith
  have hfin : (2 : ℝ) ^ q * ((1 : ℝ) +
      ∫ omega, cutoffLocalControl ell m omega ^ q ∂(cutoffSampleLaw M).toMeasure) ≤
      2 ^ (q + 1) * stripControlScale M ell m ^ 8 := by
    calc (2 : ℝ) ^ q * ((1 : ℝ) +
          ∫ omega, cutoffLocalControl ell m omega ^ q ∂(cutoffSampleLaw M).toMeasure)
        ≤ (2 : ℝ) ^ q * (2 * stripControlScale M ell m ^ 8) :=
          mul_le_mul_of_nonneg_left hsum h2q
      _ = 2 ^ (q + 1) * stripControlScale M ell m ^ 8 := by rw [pow_succ]; ring
  exact le_trans hstep hfin

/-! ## The growth of the strip ellipticity moment -/

/-- **The `K`-free coefficient of the strip moment's growth.**  A fixed
polynomial in the model's crude upper-ellipticity majorant and in `nu^{-1}`. -/
def stripLambdaGrowthConst (M : ABKModel d) : ℝ :=
  32 * cutoffUpperEllipticityMajorant M ^ 2 +
    (512 * M.nu⁻¹ * cutoffUpperEllipticityMajorant M ^ 3 +
      2048 * M.nu⁻¹ ^ 2 * cutoffUpperEllipticityMajorant M ^ 4)

theorem stripLambdaGrowthConst_nonneg (M : ABKModel d) :
    0 ≤ stripLambdaGrowthConst M := by
  have hK : (0 : ℝ) ≤ cutoffUpperEllipticityMajorant M :=
    cutoffUpperEllipticityMajorant_nonneg M
  have hnu : (0 : ℝ) < M.nu := M.nu_pos
  unfold stripLambdaGrowthConst
  positivity

/-- **The strip ellipticity moment, quantitatively.**  Unconditional. -/
theorem stripLambdaMoment_le (M : ABKModel d) (m : ℤ) (Q : TriadicCube d) :
    stripLambdaMoment M m Q ≤
      stripLambdaGrowthConst M *
        stripControlScale M (cubeOriginCoverScale Q) m ^ 8 := by
  set ell : ℤ := cubeOriginCoverScale Q with hell
  set Kmaj : ℝ := cutoffUpperEllipticityMajorant M with hKmaj
  have hKmaj0 : (0 : ℝ) ≤ Kmaj := cutoffUpperEllipticityMajorant_nonneg M
  have hnu : (0 : ℝ) < M.nu := M.nu_pos
  have h4 := integrable_one_add_cutoffLocalControl_pow M ell m 4
  have h6 := integrable_one_add_cutoffLocalControl_pow M ell m 6
  have h8 := integrable_one_add_cutoffLocalControl_pow M ell m 8
  have hEq : (fun omega : CutoffSample d => stripEllipticityWeight M m Q omega ^ 2) =
      fun omega : CutoffSample d =>
        Kmaj ^ 2 * (1 + cutoffLocalControl ell m omega) ^ 4 +
          (4 * M.nu⁻¹ * Kmaj ^ 3 * (1 + cutoffLocalControl ell m omega) ^ 6 +
            4 * M.nu⁻¹ ^ 2 * Kmaj ^ 4 * (1 + cutoffLocalControl ell m omega) ^ 8) := by
    funext omega
    unfold stripEllipticityWeight stripEllipticityEnvelope
    rw [hKmaj, hell]
    ring
  have hsplit : stripLambdaMoment M m Q =
      Kmaj ^ 2 * ∫ omega, (1 + cutoffLocalControl ell m omega) ^ 4
          ∂(cutoffSampleLaw M).toMeasure +
        (4 * M.nu⁻¹ * Kmaj ^ 3 * ∫ omega, (1 + cutoffLocalControl ell m omega) ^ 6
            ∂(cutoffSampleLaw M).toMeasure +
          4 * M.nu⁻¹ ^ 2 * Kmaj ^ 4 * ∫ omega, (1 + cutoffLocalControl ell m omega) ^ 8
            ∂(cutoffSampleLaw M).toMeasure) := by
    have hi4 : Integrable (fun omega : CutoffSample d =>
        Kmaj ^ 2 * (1 + cutoffLocalControl ell m omega) ^ 4)
        (cutoffSampleLaw M).toMeasure := h4.const_mul _
    have hi6 : Integrable (fun omega : CutoffSample d =>
        4 * M.nu⁻¹ * Kmaj ^ 3 * (1 + cutoffLocalControl ell m omega) ^ 6)
        (cutoffSampleLaw M).toMeasure := h6.const_mul _
    have hi8 : Integrable (fun omega : CutoffSample d =>
        4 * M.nu⁻¹ ^ 2 * Kmaj ^ 4 * (1 + cutoffLocalControl ell m omega) ^ 8)
        (cutoffSampleLaw M).toMeasure := h8.const_mul _
    have hi68 : Integrable (fun omega : CutoffSample d =>
        4 * M.nu⁻¹ * Kmaj ^ 3 * (1 + cutoffLocalControl ell m omega) ^ 6 +
          4 * M.nu⁻¹ ^ 2 * Kmaj ^ 4 * (1 + cutoffLocalControl ell m omega) ^ 8)
        (cutoffSampleLaw M).toMeasure := hi6.add hi8
    rw [stripLambdaMoment, hEq, integral_add hi4 hi68, integral_add hi6 hi8,
      integral_const_mul, integral_const_mul, integral_const_mul]
  set S : ℝ := stripControlScale M ell m with hS
  have hS0 : (0 : ℝ) ≤ S ^ 8 := by positivity
  have b4 := integral_one_add_cutoffLocalControl_pow_le M ell m
    (q := 4) (by norm_num) (by norm_num)
  have b6 := integral_one_add_cutoffLocalControl_pow_le M ell m
    (q := 6) (by norm_num) (by norm_num)
  have b8 := integral_one_add_cutoffLocalControl_pow_le M ell m
    (q := 8) (by norm_num) (by norm_num)
  have c4 : (0 : ℝ) ≤ Kmaj ^ 2 := by positivity
  have c6 : (0 : ℝ) ≤ 4 * M.nu⁻¹ * Kmaj ^ 3 := by positivity
  have c8 : (0 : ℝ) ≤ 4 * M.nu⁻¹ ^ 2 * Kmaj ^ 4 := by positivity
  have m4 := mul_le_mul_of_nonneg_left b4 c4
  have m6 := mul_le_mul_of_nonneg_left b6 c6
  have m8 := mul_le_mul_of_nonneg_left b8 c8
  rw [hsplit, stripLambdaGrowthConst, ← hKmaj]
  norm_num at m4 m6 m8 ⊢
  linarith

/-! ## The polynomial rate at the localization cube -/

/-- **The `K`-free base of the witness scale at the localization cube.** -/
def stripControlBase (M : ABKModel d) (m : ℤ) : ℝ :=
  (1 + 3 * (IndependentSums.gammaMomentConst 2 *
    (IndependentSums.gammaTriangleConst 2 * stripShellBudget d M.gamma m))) *
      (2 + |(m : ℝ)|)

theorem stripControlBase_nonneg (M : ABKModel d) (m : ℤ) :
    0 ≤ stripControlBase M m := by
  have h1 : (0 : ℝ) < IndependentSums.gammaMomentConst 2 :=
    IndependentSums.gammaMomentConst_pos (by norm_num)
  have h2 : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have h3 : (0 : ℝ) ≤ stripShellBudget d M.gamma m := stripShellBudget_nonneg d M.gamma m
  have h4 : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
  unfold stripControlBase
  positivity

/-- **The witness scale at the localization cube grows at most linearly.**
Unconditional. -/
theorem stripControlScale_originCube_le (M : ABKModel d) (m : ℤ) (K : ℕ) :
    stripControlScale M (cubeOriginCoverScale (originCube d (K : ℤ))) m ≤
      stripControlBase M m * (1 + (K : ℝ)) := by
  set ell : ℤ := cubeOriginCoverScale (originCube d (K : ℤ)) with hell
  have hgamma : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have h1 : (0 : ℝ) < IndependentSums.gammaMomentConst 2 :=
    IndependentSums.gammaMomentConst_pos (by norm_num)
  have h2 : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hB : (0 : ℝ) ≤ stripShellBudget d M.gamma m := stripShellBudget_nonneg d M.gamma m
  set a : ℝ := 3 * (IndependentSums.gammaMomentConst 2 *
    (IndependentSums.gammaTriangleConst 2 * stripShellBudget d M.gamma m)) with ha
  have ha0 : (0 : ℝ) ≤ a := by rw [ha]; positivity
  -- the cover scale is between zero and `K+1`
  have hlo : (0 : ℤ) ≤ ell := cubeOriginCoverScale_nonneg _
  have hhi : ell ≤ (K : ℤ) + 1 := cubeOriginCoverScale_originCube_le K
  have hloR : (0 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hlo
  have hhiR : (ell : ℝ) ≤ (K : ℝ) + 1 := by exact_mod_cast hhi
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have habs : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
  have hA0 : (0 : ℝ) ≤ |(ell : ℝ) - (m : ℝ)| := abs_nonneg _
  have hml : -|(m : ℝ)| ≤ (m : ℝ) := neg_abs_le _
  have hmu : (m : ℝ) ≤ |(m : ℝ)| := le_abs_self _
  -- the linear factor
  have hlin : 1 + |(ell : ℝ) - (m : ℝ)| ≤ (2 + |(m : ℝ)|) * (1 + (K : ℝ)) := by
    have hb : |(ell : ℝ) - (m : ℝ)| ≤ (K : ℝ) + 1 + |(m : ℝ)| := by
      rw [abs_le]
      constructor <;> linarith
    nlinarith
  have hlin1 : (1 : ℝ) ≤ 1 + |(ell : ℝ) - (m : ℝ)| := by linarith
  -- the budget split
  have hbud := tsum_cutoffGammaMajorant_le d hgamma m ell
  have hprod : 3 * (IndependentSums.gammaMomentConst 2 *
      (IndependentSums.gammaTriangleConst 2 *
        ∑' r : ℕ, cutoffGammaMajorant d M.gamma m ell r)) ≤
      a * (1 + |(ell : ℝ) - (m : ℝ)|) := by
    have hc : (0 : ℝ) ≤ 3 * (IndependentSums.gammaMomentConst 2 *
        IndependentSums.gammaTriangleConst 2) := by positivity
    have := mul_le_mul_of_nonneg_left hbud hc
    rw [ha]
    nlinarith [this]
  have hmax : stripControlScale M ell m ≤ (1 + a) * (1 + |(ell : ℝ) - (m : ℝ)|) := by
    rw [stripControlScale]
    refine max_le ?_ (le_trans hprod ?_)
    · nlinarith
    · nlinarith
  calc stripControlScale M ell m
      ≤ (1 + a) * (1 + |(ell : ℝ) - (m : ℝ)|) := hmax
    _ ≤ (1 + a) * ((2 + |(m : ℝ)|) * (1 + (K : ℝ))) := by
        exact mul_le_mul_of_nonneg_left hlin (by linarith)
    _ = stripControlBase M m * (1 + (K : ℝ)) := by
        rw [stripControlBase, ← ha]
        ring

/-- **The target: the strip ellipticity moment grows at most polynomially in the
localization scale.**  Degree eight, with `K`-free coefficients.
Unconditional. -/
theorem stripLambdaMoment_originCube_le (M : ABKModel d) (m : ℤ) (K : ℕ) :
    stripLambdaMoment M m (originCube d (K : ℤ)) ≤
      stripLambdaGrowthConst M * (stripControlBase M m * (1 + (K : ℝ))) ^ 8 := by
  refine le_trans (stripLambdaMoment_le M m (originCube d (K : ℤ))) ?_
  refine mul_le_mul_of_nonneg_left ?_ (stripLambdaGrowthConst_nonneg M)
  exact pow_le_pow_left₀
    (stripControlScale_nonneg M (cubeOriginCoverScale (originCube d (K : ℤ))) m)
    (stripControlScale_originCube_le M m K) 8

/-! ## Polynomial against geometric -/

/-- **The arithmetic the strip gate uses.**  A fixed multiple of `(1+K)^8` is
eventually below any fixed positive multiple of `3^K`.

on `0 < c` alone. -/
theorem eventually_poly_le_geometric (A : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ K : ℕ in Filter.atTop, A * (1 + (K : ℝ)) ^ 8 ≤ c * (3 : ℝ) ^ K := by
  have htend : Filter.Tendsto (fun K : ℕ => ((K : ℝ)) ^ (8 : ℕ) / (3 : ℝ) ^ K)
      Filter.atTop (nhds 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 8 (by norm_num)
  have hshift : Filter.Tendsto (fun K : ℕ => ((K : ℝ) + 1) ^ (8 : ℕ) / (3 : ℝ) ^ K)
      Filter.atTop (nhds 0) := by
    have hshift0 : Filter.Tendsto (fun K : ℕ => ((K : ℝ) + 1) ^ (8 : ℕ) / (3 : ℝ) ^ (K + 1))
        Filter.atTop (nhds 0) := by
      have := htend.comp (Filter.tendsto_add_atTop_nat 1)
      refine this.congr fun K => ?_
      simp [Function.comp]
    have hthree : Filter.Tendsto
        (fun K : ℕ => 3 * (((K : ℝ) + 1) ^ (8 : ℕ) / (3 : ℝ) ^ (K + 1)))
        Filter.atTop (nhds 0) := by
      simpa using hshift0.const_mul (3 : ℝ)
    refine hthree.congr fun K => ?_
    rw [pow_succ]
    field_simp
    ring
  have hA : ∀ᶠ K : ℕ in Filter.atTop,
      ((K : ℝ) + 1) ^ (8 : ℕ) / (3 : ℝ) ^ K < c / (|A| + 1) :=
    hshift.eventually_lt_const (by positivity)
  filter_upwards [hA] with K hK
  have h3 : (0 : ℝ) < (3 : ℝ) ^ K := by positivity
  have hA1 : (0 : ℝ) < |A| + 1 := by positivity
  have hstep : ((K : ℝ) + 1) ^ (8 : ℕ) * (|A| + 1) ≤ c * (3 : ℝ) ^ K := by
    have := (div_lt_div_iff₀ h3 hA1).1 hK
    linarith
  have hle : A ≤ |A| := le_abs_self A
  have hpow : (0 : ℝ) ≤ ((K : ℝ) + 1) ^ (8 : ℕ) := by positivity
  have hcomm : A * (1 + (K : ℝ)) ^ 8 ≤ ((K : ℝ) + 1) ^ (8 : ℕ) * (|A| + 1) := by
    have hrw : (1 + (K : ℝ)) ^ 8 = ((K : ℝ) + 1) ^ (8 : ℕ) := by ring
    rw [hrw]
    nlinarith
  linarith

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
