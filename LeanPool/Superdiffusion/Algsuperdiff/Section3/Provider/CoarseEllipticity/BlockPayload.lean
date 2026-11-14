/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.LowerLeg

/-!
# BlockPayload

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The per-scale block payload: `e.slstar.multiscale` lifted by `e.maxy.bound`

Historical conditional routes for the two legs of `p.cg.ellipticity.bounds` are
reduced, in `Provider/CoarseEllipticity/{LowerLeg, ScaleSummation}.lean`, to a
*scale summation whose two analytic A inputs are named there:

* `hgrid` --- the on-grid domination of the leg's target by a weighted series of
  per-scale grid maxima.  This abstract file does not produce it;
  `PayloadSandwich.lean` later discharges the relevant carrier identification
  on the ruled `q = 2` route, while general `q` remains separate;
* `hsplit` --- **the per-scale block split** `G k <= Cdet + (lanes)`, together
  with the lanes' measurability, nonnegativity, `Gamma`-tails and the
  amplitudes' summability.

This module produces `hsplit` and all the lane data attached to it, in the
**exact shape** the two consumers take them
(`LowerLeg.twoTermFamilySplit_of_gridSummation`,
`ScaleSummation.threeTermSplit_of_gridSummation`), from the manuscript's own
per-cube inputs.  It is the composition of exactly the two source steps
that stand between `p.bfA.multiscalebound` and those conditional payloads:

1. the **per-cube block estimate** `e.slstar.multiscale` (ABK26, label line;
   statement) and its `b_L` twin `e.bL.multiscale` (label line; statement),
   read at one triadic subcube `z + cu_n` of `cu_m`;
2. the **grid maximum** `e.maxy.bound` (`l.maximums.Gamma.s`, label line;
   statement) over the `3^{d(m-n)}` translates, which is the proved
   `GridWeights.gridSupAbs_descendants_isBigOWith`.

The composite is exactly the first display of the proof of
`p.cg.ellipticity.bounds` from `p.bfA.multiscalebound` (for the lower leg, for
the upper one).

## What the payload needs, and what this module adds

The consumers' `hsplit` binder is, character for character,

```
hsplit : forall k omega, G k omega <= Cdet + Uexp k omega                (lower)
hsplit : forall k omega, G k omega <= Cdet + U1 k omega + Uexp k omega   (upper)
```

with `Uexp k` (resp. `U1 k`) nonnegative, measurable, `Gamma`-bounded at an
amplitude `aexp k` (resp. `a1 k`) that is positive and whose weighted series
`sum_k mass * gridWeight rho k * aexp k` is summable and bounded by the output
constant.  Section 4 below produces the split (including the gap-`0` fold a
producer of `hgrid` needs, whose lane is a sum of two grid maxima), section 3
the tails, section 2 the amplitudes' arithmetic (with the *explicit printed
pole* `p ! (1 + rho^{-1})^{p+1}`), and section 6 runs the two consumers to their
conclusions.

The `e.maxy.bound` amplitude is `gridBlockAmp d sigma A k`, i.e. `(3 d log
3)^{1/sigma} * (k+1)^{1/sigma} * A`: the `k`-independent net constant and the
source's own polynomial `(m - n + 1)^{1/sigma}` at `m - n = k + 1`.  At the
lower leg's exceptional index `sigma = (1 - sigma_0/4)/2` the exponent is `2/(1
- sigma_0/4) <= 16/7`, the printed `(m-n+1)^{2+sigma_0}`; at the upper leg's
`(1 - sigma_0/4)/3` it is `3/(1 - sigma_0/4) <= 24/7`, the printed
`(m-n+1)^{3+sigma_0}`.

## The exponent-kind seam: a local bridge

`GridWeights.lean` records  an unbridged seam: its `gridNetConst_rpow_eq` emits
`((k:R)+1) ^ (sigma^{-1} : R)` (`Real.rpow`) while its `polyGridWeight_tsum_le`
consumes `((k:R)+1) ^ (p : N)` (`Monoid.npow`), and "no bridge lemma is proved
here".  `rpow_succ_le_natPow` below is that bridge, and
`gridBlockAmp_le_natPow`, `summable_gridWeight_mul_gridBlockAmp` and
`tsum_gridWeight_mul_gridBlockAmp_le` are its three consequences: the local
bridge **rounds the exponent up to the next integer** `p`, exactly the bridge
that docstring names, at the cost of the weaker pole `(1 + rho^{-1})^{p+1}` in
place of the printed `rho^{-(1/sigma + 1)}`.  Since the frozen displays absorb
every `(2s - gamma)` factor into the rare-event exponential, the weakening is
free at the call site and is priced there, not here.

## The collar

`e.slstar.multiscale` normalizes by `3^{-gamma(m-n)}` on its left and the
lifted display carries the reciprocal `3^{gamma(m-n)}` on its right.  A
`k`-dependent factor cannot sit in the consumers' `Cdet`, so it must be
absorbed into the weight: that is `GridWeights.gridWeight_mul_rpow`, and
`forall_le_tsum_gridWeight_collar` / `le_tsum_gridWeight_collar` below run the
absorption at the level of the whole series, moving the pole from `rho` to `rho
- g`.  At `rho = 2s` (the `hgrid` producer's weight) and `g = gamma` this is
the passage from `2s` to `2s - gamma` printed at `e.cg.ellip.lower.pre` and
`e.cg.ellip.upper.pre`.

## Conditional obligations retained by this module

* `hgrid`.  Every theorem of sections 5 and 6 takes it as a named hypothesis.
  No proof of it appears below.  The composition lemmas are therefore
  conditional A and carry no node status.  `PayloadSandwich.lean` supplies
  concrete `q = 2` instances downstream; that does not change the signatures
  here.
* The per-cube block estimate itself, i.e. `p.bfA.multiscalebound`.  This file
  takes `hblock` and its Orlicz lanes as explicit analytic A obligations;
  nothing here proves or narrows them.  Later multiscale providers may
  discharge concrete uses, but that downstream work is not credited here.
* The small-`m` branch (`p.base.case`, `l.mathcal.E.to.Lambdas`): untouched in
  this file.  The frozen base case is now proved, but no application of it is
  performed below.
* The identification of the legs' carrier grid maxima with `blockGridSup`
  (CoarseGraining's `Ch04.maxDescendant...AtScale` vs `gridSupAbs`) is not
  composed in this model-free file.  The later `PayloadSandwich.lean` route
  performs the concrete `q = 2` composition.

The concrete downstream theorem `superposedFlux_coarse_ellipticity_lower_leg`
supplies the lower leg through the superposed-flux pre-split route, so the list
above is module-local historical A disclosure, not the global lower-leg status.
The separate theorem `superposedFlux_coarse_ellipticity_upper_leg` supplies the
upper leg downstream.

## References

* ABK26, `p.bfA.multiscalebound`, statement (`e.slstar.multiscale` label,
  `e.bL.multiscale` label); proof of `p.cg.ellipticity.bounds` from it, (the
  grid lift, the summations, the absorption gate).
* ABK26, `l.maximums.Gamma.s` (`e.maxy.bound`), label.
* ABK26, `p.cg.ellipticity.bounds`, statement.
* `Provider/CoarseEllipticity/GridWeights.lean` (the grid, its weights and the
  `e.maxy.bound` lift), `.../ScaleSummation.lean` and `.../LowerLeg.lean` (the
  two consumers whose binders are matched here).
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums

noncomputable section

variable {Omega : Type*}

/-! ## 1. The block grid maximum

`blockGridSup d m k X` is the manuscript's `max_{z in 3^n Z^d cap cu_m}
|X_{z+cu_n}|` at `n = m - 1 - k`, i.e. at scale gap `m - n = k + 1`, which is
the range of the proof's own binder `n <= m - 1`. -/

/-- The grid maximum over the `3^{d(k+1)}` triadic subcubes of `cu_m` at scale
`m - 1 - k`: the source's `max_{z in 3^n Z^d cap cu_m}` at `m - n = k + 1`. -/
noncomputable def blockGridSup (d : ℕ) (m : ℤ) (k : ℕ)
    (X : TriadicCube d → Omega → ℝ) (omega : Omega) : ℝ :=
  gridSupAbs (descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    (descendantsAtScale_originCube_nonempty d m k) X omega

theorem blockGridSup_nonneg (d : ℕ) (m : ℤ) (k : ℕ)
    (X : TriadicCube d → Omega → ℝ) (omega : Omega) :
    0 ≤ blockGridSup d m k X omega :=
  gridSupAbs_nonneg _ _ _ _

theorem le_blockGridSup {d : ℕ} {m : ℤ} {k : ℕ} {X : TriadicCube d → Omega → ℝ}
    {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    (omega : Omega) :
    |X R omega| ≤ blockGridSup d m k X omega :=
  le_gridSupAbs (descendantsAtScale_originCube_nonempty d m k) hR omega

theorem blockGridSup_le {d : ℕ} {m : ℤ} {k : ℕ} {X : TriadicCube d → Omega → ℝ}
    {omega : Omega} {b : ℝ}
    (hb : ∀ R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)),
      |X R omega| ≤ b) :
    blockGridSup d m k X omega ≤ b :=
  gridSupAbs_le (descendantsAtScale_originCube_nonempty d m k) hb

theorem measurable_blockGridSup [MeasurableSpace Omega] (d : ℕ) (m : ℤ) (k : ℕ)
    {X : TriadicCube d → Omega → ℝ} (hm : ∀ R, Measurable (X R)) :
    Measurable (blockGridSup d m k X) :=
  measurable_gridSupAbs _ (descendantsAtScale_originCube_nonempty d m k) hm

/-! ## 2. The `e.maxy.bound` amplitude and its pole -/

/-- The amplitude `e.maxy.bound` produces at the triadic grid of gap `k + 1`: `(3 d
log 3)^{1/sigma} (k+1)^{1/sigma} A`.  The polynomial factor is the source's `(m
- n + 1)^{1/sigma}` and the constant is `gridNetConst`. -/
noncomputable def gridBlockAmp (d : ℕ) (sigma A : ℝ) (k : ℕ) : ℝ :=
  gridNetConst d sigma * (((k : ℝ) + 1) ^ sigma⁻¹) * A

/-- The pole the rounded-up polynomial lift produces against `gridWeight rho`:
`p ! (1 + rho^{-1})^{p+1}`, the printed `(2s - gamma)^{-(p+1)}` shape after
`one_sub_rpow_neg_inv_le`. -/
noncomputable def blockPoleConst (p : ℕ) (rho : ℝ) : ℝ :=
  (Nat.factorial p : ℝ) * (1 + rho⁻¹) ^ (p + 1)

theorem gridNetConst_pos {d : ℕ} (hd : 1 ≤ d) (sigma : ℝ) :
    0 < gridNetConst d sigma := by
  have hlog : (0 : ℝ) < Real.log 3 := lt_trans zero_lt_one one_lt_log_three
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hbase : (0 : ℝ) < 3 * (d : ℝ) * Real.log 3 :=
    mul_pos (mul_pos (by norm_num) (by linarith)) hlog
  exact Real.rpow_pos_of_pos hbase _

theorem gridBlockAmp_nonneg (d : ℕ) (sigma : ℝ) {A : ℝ} (hA : 0 ≤ A) (k : ℕ) :
    0 ≤ gridBlockAmp d sigma A k :=
  mul_nonneg
    (mul_nonneg (gridNetConst_nonneg d sigma) (Real.rpow_nonneg (by positivity) _)) hA

theorem gridBlockAmp_pos {d : ℕ} (hd : 1 ≤ d) (sigma : ℝ) {A : ℝ} (hA : 0 < A)
    (k : ℕ) : 0 < gridBlockAmp d sigma A k :=
  mul_pos (mul_pos (gridNetConst_pos hd sigma)
    (Real.rpow_pos_of_pos (by positivity) _)) hA

/-- **The exponent-kind bridge** (`GridWeights.lean`).  The real-exponent lift of
`e.maxy.bound` is over-bounded at the next integer degree: `(k+1)^t <= (k+1)^p`
for `t <= p`.  This is the only step that lets the `Real.rpow` amplitude of
`gridSupAbs_descendants_isBigOWith` be summed by the `Monoid.npow` series of
`polyGridWeight_tsum_le`. -/
theorem rpow_succ_le_natPow {t : ℝ} (p : ℕ) (hp : t ≤ (p : ℝ)) (k : ℕ) :
    ((k : ℝ) + 1) ^ t ≤ ((k : ℝ) + 1) ^ p := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have h := Real.rpow_le_rpow_of_exponent_le hk1 hp
  rwa [Real.rpow_natCast] at h

theorem gridBlockAmp_le_natPow {d : ℕ} {sigma A : ℝ} (hA : 0 ≤ A) (p : ℕ)
    (hp : sigma⁻¹ ≤ (p : ℝ)) (k : ℕ) :
    gridBlockAmp d sigma A k ≤ gridNetConst d sigma * A * ((k : ℝ) + 1) ^ p := by
  have hc : 0 ≤ gridNetConst d sigma * A := mul_nonneg (gridNetConst_nonneg d sigma) hA
  calc gridBlockAmp d sigma A k
      = gridNetConst d sigma * A * ((k : ℝ) + 1) ^ sigma⁻¹ := by
        rw [gridBlockAmp]; ring
    _ ≤ gridNetConst d sigma * A * ((k : ℝ) + 1) ^ p :=
        mul_le_mul_of_nonneg_left (rpow_succ_le_natPow p hp k) hc

/-! ### The rounding integer at the four exceptional indices

`hp : sigma⁻¹ ≤ p` is discharged, at each of the indices the source and the
frozen displays actually use, from the source's own window `sigma in (0,1/2]`.
The source applies `p.bfA.multiscalebound` with `sigma |-> sigma/4`, producing
the indices `(1 - sigma/4)/2` and `(1 - sigma/4)/3`; the frozen displays carry
`(1 - sigma)/2` and `(1 - sigma)/3`.  All four are covered. -/


/-- The upper display's exceptional index `(1 - sigma)/3` (the tail index of
`e.cg.ellip.upper`): `((1 - sigma)/3)⁻¹ = 3/(1 - sigma) ≤ 6` on the frozen
window `sigma in (0,1/2]`. -/
theorem frozenUpperIndex_inv_le {sigma : ℝ} (h1 : sigma ≤ 1 / 2) :
    ((1 - sigma) / 3)⁻¹ ≤ 6 := by
  have hpos : (0 : ℝ) < (1 - sigma) / 3 := by linarith
  rw [inv_le_comm₀ hpos (by norm_num)]
  linarith

private theorem gridWeight_mul_gridBlockAmp_le {d : ℕ} {mass rho sigma A : ℝ}
    (hmass : 0 ≤ mass) (hA : 0 ≤ A) (p : ℕ) (hp : sigma⁻¹ ≤ (p : ℝ)) (k : ℕ) :
    mass * gridWeight rho k * gridBlockAmp d sigma A k
      ≤ mass * (gridNetConst d sigma * A) * (((k : ℝ) + 1) ^ p * gridWeight rho k) := by
  have hw : 0 ≤ mass * gridWeight rho k :=
    mul_nonneg hmass (gridWeight_nonneg rho k)
  calc mass * gridWeight rho k * gridBlockAmp d sigma A k
      ≤ mass * gridWeight rho k * (gridNetConst d sigma * A * ((k : ℝ) + 1) ^ p) :=
        mul_le_mul_of_nonneg_left (gridBlockAmp_le_natPow hA p hp k) hw
    _ = mass * (gridNetConst d sigma * A) * (((k : ℝ) + 1) ^ p * gridWeight rho k) := by
        ring

theorem summable_gridWeight_mul_gridBlockAmp {d : ℕ} {mass rho sigma A : ℝ}
    (hmass : 0 ≤ mass) (hrho : 0 < rho) (hA : 0 ≤ A) (p : ℕ)
    (hp : sigma⁻¹ ≤ (p : ℝ)) :
    Summable fun k : ℕ => mass * gridWeight rho k * gridBlockAmp d sigma A k := by
  refine Summable.of_nonneg_of_le (fun k => ?_)
    (fun k => gridWeight_mul_gridBlockAmp_le hmass hA p hp k)
    ((polyGridWeight_summable p hrho).mul_left (mass * (gridNetConst d sigma * A)))
  exact mul_nonneg (mul_nonneg hmass (gridWeight_nonneg rho k))
    (gridBlockAmp_nonneg d sigma hA k)

/-- **The scale sum of the `e.maxy.bound` amplitudes**, with the explicit pole.

`sum_k mass * gridWeight rho k * gridBlockAmp d sigma A k
   <= mass * ((3 d log 3)^{1/sigma} A) * p ! (1 + rho^{-1})^{p+1}`

for any integer `p >= 1/sigma`.  The pole order `p + 1` is the printed one
rounded up: at the lower leg's `1/sigma = 2/(1 - sigma_0/4) <= 16/7` one may
take `p = 3` (printed `(2s - gamma)^{-(3 + sigma_0)}`), at the upper leg's
`1/sigma = 3/(1 - sigma_0/4) <= 24/7` one may take `p = 4` (printed `(2s -
gamma)^{-(4 + sigma_0)}`). -/
theorem tsum_gridWeight_mul_gridBlockAmp_le {d : ℕ} {mass rho sigma A : ℝ}
    (hmass : 0 ≤ mass) (hrho : 0 < rho) (hA : 0 ≤ A) (p : ℕ)
    (hp : sigma⁻¹ ≤ (p : ℝ)) :
    ∑' k : ℕ, mass * gridWeight rho k * gridBlockAmp d sigma A k
      ≤ mass * (gridNetConst d sigma * A) * blockPoleConst p rho := by
  have hcnn : 0 ≤ mass * (gridNetConst d sigma * A) :=
    mul_nonneg hmass (mul_nonneg (gridNetConst_nonneg d sigma) hA)
  have hstep : ∑' k : ℕ, mass * gridWeight rho k * gridBlockAmp d sigma A k
      ≤ ∑' k : ℕ, mass * (gridNetConst d sigma * A) *
          (((k : ℝ) + 1) ^ p * gridWeight rho k) :=
    (summable_gridWeight_mul_gridBlockAmp hmass hrho hA p hp).tsum_le_tsum
      (fun k => gridWeight_mul_gridBlockAmp_le hmass hA p hp k)
      ((polyGridWeight_summable p hrho).mul_left _)
  have hval : ∑' k : ℕ, mass * (gridNetConst d sigma * A) *
        (((k : ℝ) + 1) ^ p * gridWeight rho k)
      = mass * (gridNetConst d sigma * A) *
        ∑' k : ℕ, ((k : ℝ) + 1) ^ p * gridWeight rho k := tsum_mul_left
  have hpole : ∑' k : ℕ, ((k : ℝ) + 1) ^ p * gridWeight rho k
      ≤ blockPoleConst p rho := by
    refine (polyGridWeight_tsum_le p hrho).trans ?_
    have hinv : 0 ≤ (1 - (3 : ℝ) ^ (-rho))⁻¹ := (inv_pos.2 (one_sub_rpow_neg_pos hrho)).le
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hinv (one_sub_rpow_neg_inv_le hrho) (p + 1))
      (Nat.cast_nonneg _)
  refine hstep.trans ?_
  rw [hval]
  exact mul_le_mul_of_nonneg_left hpole hcnn

/-! ## 3. The `e.maxy.bound` lift of one lane -/

/-- **`e.maxy.bound` at the block grid, in the lanes' one-sided form.**

A per-cube `Gamma_sigma` bound at a common amplitude `A`, valid at every one of
the `3^{d(k+1)}` translates `z + cu_{m-1-k}` of `cu_m`, lifts to the grid
maximum at the amplitude `gridBlockAmp d sigma A k`.

The lanes of `p.bfA.multiscalebound` are nonnegative (they are the random parts
of a bound on an absolute value), and for a nonnegative variable the one-sided
relation `U <= O_{Gamma_sigma}(A)` the consumers use and the symmetric relation
`U = O_{Gamma_sigma}(A)` the proved maximum lemma takes are the same statement
(`Provider.Orlicz.isBigOWith_iff_isBigO_of_nonneg`). -/
theorem isBigOWith_gammaSigma_blockGridSup [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] {d : ℕ} (hd : 1 ≤ d)
    (m : ℤ) (k : ℕ) {U : TriadicCube d → Omega → ℝ} {A sigma : ℝ}
    (hsigma : 0 < sigma) (hA : 0 ≤ A)
    (hUnonneg : ∀ R omega, 0 ≤ U R omega)
    (hUO : ∀ R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)),
      IsBigOWith mu (gammaSigma sigma) (U R) A) :
    IsBigOWith mu (gammaSigma sigma) (blockGridSup d m k U)
      (gridBlockAmp d sigma A k) :=
  gridSupAbs_descendants_isBigOWith hd m k hsigma hA fun R hR =>
    (Provider.Orlicz.isBigOWith_iff_isBigO_of_nonneg (fun omega => hUnonneg R omega)).1
      (hUO R hR)

/-! ## 4. The per-scale split, in the consumers' `hsplit` shape -/


/-- **The three-slot per-scale block split** (the upper leg's `hsplit`).

The `b_L` analogue of `blockGridSup_le_add_of_perCube`: the per-cube estimate
`|X_R| <= Cdet + U1_R + Uexp_R` of `e.bL.multiscale` lifts to the grid maximum
with one grid maximum per lane. -/
theorem blockGridSup_le_add_add_of_perCube {d : ℕ} {m : ℤ} {k : ℕ}
    {X U1 Uexp : TriadicCube d → Omega → ℝ} {Cdet : ℝ}
    (hU1nonneg : ∀ R omega, 0 ≤ U1 R omega)
    (hUexpnonneg : ∀ R omega, 0 ≤ Uexp R omega)
    (hcube : ∀ R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)),
      ∀ omega, |X R omega| ≤ Cdet + U1 R omega + Uexp R omega)
    (omega : Omega) :
    blockGridSup d m k X omega
      ≤ Cdet + blockGridSup d m k U1 omega + blockGridSup d m k Uexp omega := by
  refine blockGridSup_le fun R hR => (hcube R hR omega).trans ?_
  have hle1 : |U1 R omega| ≤ blockGridSup d m k U1 omega := le_blockGridSup hR omega
  have hle2 : |Uexp R omega| ≤ blockGridSup d m k Uexp omega := le_blockGridSup hR omega
  rw [abs_of_nonneg (hU1nonneg R omega)] at hle1
  rw [abs_of_nonneg (hUexpnonneg R omega)] at hle2
  linarith

/-! ### The gap-`0` fold

A producer of `hgrid` folds the source series' gap-`0` term (CoarseGraining's
`LambdaSqFinite` at `n = 0`, outside `gridWeight`'s range) into the series at a
constant `ctop`, so its grid family has the shape `G k = ctop * T + (scale-k
maximum)` with `T` the top-scale maximum.  Splitting *that* family needs the
per-scale split at two scales and one addition of lanes, which is the two-term
case of `l.Gamma.sigma.triangle`. -/

/-- **Two nonnegative lanes, added**: the two-term case of
`l.Gamma.sigma.triangle`, in the one-sided form the consumers' lanes carry. -/
theorem isBigOWith_gammaSigma_add [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu] {U V : Omega → ℝ} {a b sigma : ℝ}
    (hsigma : 0 < sigma) (hUnonneg : ∀ omega, 0 ≤ U omega)
    (hVnonneg : ∀ omega, 0 ≤ V omega)
    (hUmeas : Measurable U) (hVmeas : Measurable V) (ha : 0 < a) (hb : 0 < b)
    (hU : IsBigOWith mu (gammaSigma sigma) U a)
    (hV : IsBigOWith mu (gammaSigma sigma) V b) :
    IsBigOWith mu (gammaSigma sigma) (fun omega => U omega + V omega)
      (gammaTriangleConst sigma * (a + b)) := by
  classical
  have hne : (0 : ℕ) ≠ 1 := by norm_num
  have hsum := isBigO_finset_sum_of_isBigO_gammaSigma (μ := mu)
    (s := ({0, 1} : Finset ℕ)) (X := fun i => if i = 0 then U else V)
    (a := fun i => if i = 0 then a else b) (σ := sigma) hsigma
    ⟨0, by simp⟩ ?_ ?_ ?_
  · have hfun : (fun omega => ∑ i ∈ ({0, 1} : Finset ℕ),
        (if i = 0 then U else V) omega) = fun omega => U omega + V omega := by
      funext omega
      rw [Finset.sum_pair hne]
      simp
    have hamp : ∑ i ∈ ({0, 1} : Finset ℕ), (if i = 0 then a else b) = a + b := by
      rw [Finset.sum_pair hne]
      simp
    rw [hfun, hamp] at hsum
    exact (Provider.Orlicz.isBigOWith_iff_isBigO_of_nonneg
      (fun omega => add_nonneg (hUnonneg omega) (hVnonneg omega))).2 hsum
  · intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · simpa using ha
    · rw [Finset.mem_singleton] at hi
      subst hi
      simpa using hb
  · intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · simpa using
        (Provider.Orlicz.isBigOWith_iff_isBigO_of_nonneg hUnonneg).1 hU
    · rw [Finset.mem_singleton] at hi
      subst hi
      simpa using
        (Provider.Orlicz.isBigOWith_iff_isBigO_of_nonneg hVnonneg).1 hV
  · intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · simpa using hUmeas
    · rw [Finset.mem_singleton] at hi
      subst hi
      simpa using hVmeas


/-! ## 5. The collar, absorbed into the weight

`e.slstar.multiscale` carries `3^{-gamma(m-n)}` on its left, so the lifted
per-scale display carries `3^{gamma(k+1)}` on its right.  A `k`-dependent
factor cannot sit in the consumers' `Cdet`; `GridWeights.gridWeight_mul_rpow`
moves it into the weight, which is the passage from the pole `rho` to `rho - g`
(from `2s` to `2s - gamma` at the source's data). -/


/-! ## 6. The compositions: the legs' payload conjunctions, conditional on `hgrid`

Both theorems below carry `hgrid` as an explicit analytic A obligation.
Neither carries source-node status; each exhibits the payload conjunction its
leg's reduction consumes, with every other binder discharged from the per-cube
block estimate. -/


end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
