/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffHomogenizationError
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.MultiscaleEstimate.BadEventMaxSplit

/-!
# BadEventSummed

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: the `l`-aggregation of the bad-event term (`e.local.bad.events.summed`)

This is a *provider endpoint only*.  It is not a source node, it creates and
modifies no frozen declaration, and it closes no source node, no instance of a
source node and no fraction of a source node.

## 1. The printed display, and what is delivered

```
    E^2_{s/4,infty,2}(cu_m; a_m, shom_m)
      . max_{l in (-infinity,m] cap Z} 3^{-s(m-l)/2}
          ( avsum_{z in 3^l Zd cap cu_m} 1_{not Q(l,l-h,z)} )^{s/d}
  <=  O_{Gamma_1}( C cstar^{-1} s^{-2} eps^{-C} cgamma )
    + O_{Gamma_{2/7}}( exp( -C^{-1} E^{-2} cgamma^{-1} ) ) .
```

`exists_badEventSummed_bound` (§5) is that display, at the multiscale root's
own binder set, with

* the left factor the Section 3 observable
  `Observable.cutoffHomogenizationError M m <s/4,_>` squared — the carrier in
  which `exists_crude_bound` states `e.mathcalE.crude.bound`;
* the printed `max_{l <= m}` as `⨆ j : ℕ` under the reindexing `j = m - l`, its
  weight written `3^{-(s/4).2.j}`, which is the *proved* spelling of `3^{-s
  j/2}` used by `BadEventMaxSplit` (the exponent slot of `Ch02.geometricWeight
  (s/4) 2`'s seam);
* the printed exponent `rho = s/d` (the printed `s/2d` is refuted there),
  inherited from `exists_badEvent_indicatorAverage_rpow_at_s_div_d`;

§6 then composes it with the proved max-first extraction and with the carrier
bridge, delivering the same estimate for the *post-step-1 middle expression* of
the printed derivation, in the almost-sure form admits.

## 2. The mechanism, in four lines

Write `W(omega)` for the printed maximum and `E^2(omega)` for the observable.

1. `W` is `[0,1]`-valued (`ciSup_three_rpow_mul_mem_Icc`): every weight is `<=
   1`, every averaged indicator is `<= 1`, every `rho`-power of a number in
   `[0,1]` is `<= 1`.
2. `W <= sum_j 3^{-s j/2}(avsum_z 1_{not Q})^{s/d}`
   (`ciSup_three_rpow_mul_le_tsum`) and the sum is
   `O_{Gamma_1}(gammaTriangleConst 1 . c_{s/2}^{-1} . A_bad)`
   (`isBigOWith_gammaOne_ciSup_three_rpow_mul`) — this is *the printed proof's
   own last step*, "summing over `l` instead of maxing".
3. `E^2 <= b + O_{Gamma_1}(A_1) + O_{Gamma_{2/7}}(A_2)` (`exists_crude_bound`,
   the proved `e.mathcalE.crude.bound`).
4. Hence, with `Y', Z' >= 0` the clamped witnesses of 3,

```
      E^2 . W  <=  (b + Y' + Z') . W  =  b.W + Y'.W + Z'.W
               <=  (b.W + Y') + Z'                     (because W <= 1) .
```

Only the D part `b` ever meets the `l`-sum; the two tail lanes meet the MAX,
which costs nothing.  No Orlicz product `e.multGammasig` is taken anywhere:
that route is index-refuted (`Gamma_{2/7} x Gamma_1 -> Gamma_{2/9}`, and `2/9 <
1/4`).

**Precisely what "unchanged" means here.**  The `Gamma_{2/7}` amplitude is
carried through V (`A_2` in and `A_2` out).  The `Gamma_1` amplitude is `(1 +
log 2)^{1^{-1}} . (b.K + A_1)`: the lane is merged with `b.W` by the two-event
union bound of `Provider.Multiscale.isBigOWith_gammaSigma_add`
(`ConclusionSeam3Closure.lean`), at the cost of the pure constant `1 + log 2 =
1.693...`, with NO power of `s`, no `d` and no `cstar`.

## 3. Where the printed `s^{-2}` comes from

Two independent factors `s^{-1}`, and they multiply only the deterministic
shift:

* `c_{s/2}^{-1} <= 20 s^{-1}` from the `l`-sum's total mass
  (`inv_geometricDiscount_quarter_two_le`, the `(s/4, 2)` instance of the
  upstream `Ch02.inv_geometricDiscount_le_five_inv`).

The deterministic shift itself is a pure constant on the printed window: the
proved `lowerEllipticityProfile_exponentTwo_quarter_le` gives `b = 8 Ccg + 8.
3^{cgamma}. lowerEllipticityProfile Ccg cgamma (s/4) 2 <= 8 Ccg + 16 Ccg.
3^{cgamma} / 3 <= 24 Ccg` at `cgamma <= 1`.  It is NOT bounded inside the
delivered statement: the explicit expression is kept, which is strictly
stronger and is what the crude bound itself carries.

The crude bound's own `Gamma_1` amplitude
`8 (Ccg cstar^{-1} (s/4) cgamma (2(s/4) - cgamma)^{-3})` is carried verbatim;
on the printed window `8 cgamma <= s` it is `<= C cstar^{-1} cgamma s^{-2}`,
matching the print, and that bound is not re-proved here.

Finally `3^{5h} <= eps^{-C}` — the printed absorption at `h := C |log eps|` —
is the consumer's, not this file's; the delivered amplitude carries `3^{5h}`
explicitly.

## The scale gate on `m`

The landmark premise carried by both endpoints below is `mStarStar M < m`,
**not** the printed `m0 in (mstar, infty) cap Z` that it inherits through
`exists_crude_bound` from `l.shom.continuity`.  Nothing else moved: the premise
is forwarded verbatim to the producers consumed here, no proof step here
consumes it, and no frozen statement changes.

## 4. Hypotheses

The premises are the printed ones: `inductionState M (m-1) E` (the multiscale
root's own state, as `exists_crude_bound` and
`exists_badEvent_indicatorAverage_rpow_at_s_div_d` carry it); the landmark gate
`mStarStar M < m`, inherited verbatim from `exists_crude_bound` and forwarded,
never consumed here; the four `E`-gates and `cgamma <= (E^{-1})^{10}` of
`e.param.conditions.in.main`; the bad-event producer's own slice
`epsilon in Ioc 0 (1/2)`, `(h:ℝ) <= H |log epsilon| + 1`,
`cstar^{-1} epsilon^{-C} <= E`; and the printed window `8 cgamma <= s <= 1` of
`l.localization.mathcalE`.  The measurability hypotheses of the abstract
engines are discharged at the concrete carrier by
`measurable_badEventAverage_rpow` and `Measurable.iSup`.

Two binders are not literally printed: `1 <= h`, and the per-lane nonemptiness
of `F` (the printed grid `3^{m-j} Zd cap cu_m` contains `0`, so this is free at
the intended instantiation).

**On `1 <= h`.**  The printed window is `h in N_0 cap [0, cgamma^{-1}]`, which
admits `h = 0`; this file needs `h >= 1`, and the reason is structural, not
technical.  The lane `j = 0` of the maximum carries the bad event
`Q(m, m-h, z)`, whose producer needs the induction state at the coarse scale
`m - h <= m - 1`; at `h = 0` that is the state at scale `m`, i.e. the
multiscale root's own conclusion, which would be circular.  It costs the
consumer nothing: at the intended instantiation
`h := waveCutoff C0 eps = ceil(C0 |log eps|)`, the bound
`1 <= ceil(C0 |log eps|)` follows from `0 < C0` and `eps in Ioc 0 (1/2)` alone,
since `eps <= 1/2` forces `|log eps| >= log 2 > 0` and `Nat.one_le_ceil_iff`
then gives the ceiling `>= 1` (`one_le_waveCutoff`).  Nothing in this file
discharges the binder; it is stated rather than hidden.

## 5. What this file does NOT deliver

* **Step 1** of the printed derivation, the per-scale pre-ceiling
  `avsum_z max_e J^{d/s} 1_{not Q} <= (max_z max_e J)(avsum_z 1_{not Q})^{s/d}`,
  is `BadEventPreCeiling`'s.  The left side of §6's endpoints is the
  post-step-1 middle expression of the print verbatim — the same left side
  `BadEventMaxSplit` carries.
* **The grid instantiation** `F j := 3^{m-j} Zd cap cu_m`: `F` stays free; only
  per-lane nonemptiness is used, and no cardinality of `F` enters anywhere.
* **`3^{5h} <= eps^{-C}` and the window `cgamma h <= 1`.**
* **The single extraction of the bad-event constant.**  The good-event level
  delivered here is `2 . Cbad`, and `Cbad` is the first component of
  `exists_badEventSup_isBigOWith_gammaOne`, i.e. the `Ccg` of
  `Frozen.bad_event_estimate`.  It is a *different* constant from
  `exists_crude_bound`'s `Ccg` (`Frozen.coarse_ellipticity_bounds`), and the
  two are kept apart in every statement of this file:
  `exists_badEventSummed_bound` binds `Ccg` and `Cbad` separately and never
  conflates them.  There is nothing to match against the induction state:
  `Algsuperdiff.Frozen.Section3.inductionState` carries no good-event constant
  at all (it is two `sigmaBar` bracketings plus a `Gamma_2`/`Gamma_{1/2}`
  two-term display for `cutoffHomogenizationError`), and `goodLocalEventAt`
  occurs nowhere outside the four `MultiscaleEstimate` files.  The seam is
  therefore an assembly obligation, not a statement one: the assembly must
  extract the bad-event existential once and thread that same `Cbad` into the
  localization fourth term and into this endpoint.
* **Measurability of the raw `l`-sum.**  The per-scale response
  `Ch02.maxDescendantNormalizedBlockResponseAtScale` at the *raw* cutoff
  coefficient family is not known measurable here (only its representative is),
  so the §6 endpoints are stated as an almost-sure domination by a named
  measurable witness pair rather than as `Probability.IsTwoTermBigOWith` at
  that left side, whose carrier demands `Measurable X`.  §6's display, whose
  left side is the *observable* and hence measurable, carries the genuine
  `IsTwoTermBigOWith`.

## 6. References

* ABK26: `e.mathcalE.crude.bound`, `e.badevent.indicator.propagate`,
  `e.multGammasig`, `l.Gamma.sigma.triangle`.
-/

namespace Algsuperdiff.Section3.Provider.MultiscaleEstimate

-- The `_root_` prefixes below are deliberate.  With the umbrella
-- `import Algsuperdiff.Section3` in place of the two imports above, a bare
-- `open Homogenization` lets the sibling namespace
-- `Algsuperdiff.Section3.Provider.Homogenization` shadow the root one and
-- `Vec` and `originCube` become unknown identifiers.  The prefixes keep the
-- file robust against that.
open _root_.MeasureTheory
open _root_.HCPolySupport
open _root_.HCPolySupport.Book
open _root_.HCPolySupport.IndependentSums

noncomputable section

variable {d : ℕ}

/-! ## 1. The ceiling composition, abstract -/

section Ceiling

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The ceiling composition at a general `[0,1]`-valued factor**, with the
deterministic shift priced through the factor's own smallness.

```
    X <= b + O_{Gamma_{s1}}(A1) + O_{Gamma_{s2}}(A2) ,   0 <= V <= 1 ,
    V <= O_{Gamma_{s1}}(K)
  =>  X . V  <=  O_{Gamma_{s1}}( (1 + log 2)^{s1^{-1}} . (b K + A1) )
                 + O_{Gamma_{s2}}( A2 ) .
```

Three facts and no more: `V >= 0` moves the domination inside the product; `V
<= 1` lets the two clamped witnesses pass through unchanged (`Y'.V <= Y'`),
which is the mechanism and the reason no Orlicz product is taken; and the deterministic part
becomes `b.V`, which is `Gamma_{s1}` at `b K` — this is what removes the
constant term `b` from the right-hand side, turning the crude bound's `C +
Gamma_1 + Gamma_{2/7}` into the printed `Gamma_1 + Gamma_{2/7}` of
`e.local.bad.events.summed`.

The witnesses are named: the output pair is `(b.V + max 0 Y, max 0 Z)`, the
clamps being the free `Provider.Tail.isBigOWith_max_zero` (the two-term
witnesses are only known measurable and dominating, never nonnegative).

The merge of the two `Gamma_{s1}` lanes is
`Provider.Multiscale.isBigOWith_gammaSigma_add`
(`Multiscale/ConclusionSeam3Closure.lean`), the two-event union bound at `(1 +
log 2)^{s1^{-1}}`: it needs `0 < s1` and the two displays, and NOTHING else —
no nonnegativity, no measurability.  The `gammaTriangleConst s1` merges
(`Orlicz/TwoTermCalculus.lean`, `TailSqrt.lean`,
`CoarseEllipticity/BlockPayload.lean`) would cost `16384` here instead of
`1.693...`; see the module header's §7.

This is NOT `ceiling_product` (`BadEventIngredients.lean`), which is single-`l`
(one scalar weight, one `Finset`) and which keeps the deterministic shift `b`
rather than pricing `b.V`; see the module header's twin census. -/
theorem isTwoTermBigOWith_mul_ceiling [IsFiniteMeasure μ]
    {X V : Ω → ℝ} {b K A₁ A₂ sigma₁ sigma₂ : ℝ}
    (hsigma₁ : 0 < sigma₁) (hb : 0 ≤ b) (hK : 0 ≤ K)
    (hVmeas : Measurable V) (hV : ∀ omega, V omega ∈ Set.Icc (0 : ℝ) 1)
    (hVtail : IsBigOWith μ (gammaSigma sigma₁) V K)
    (hX : Probability.IsDeterministicShiftTwoTermOneSidedOrlicz μ
      (gammaSigma sigma₁) (gammaSigma sigma₂) X b A₁ A₂) :
    Probability.IsTwoTermBigOWith μ (gammaSigma sigma₁) (gammaSigma sigma₂)
      (fun omega => X omega * V omega)
      ((1 + Real.log 2) ^ sigma₁⁻¹ * (b * K + A₁)) A₂ := by
  obtain ⟨Y, Z, hΨ₁, hΨ₂, hA₁, hA₂, hXm, hYm, hZm, hdom, hYt, hZt⟩ :=
    Probability.deterministicShiftTwoTermOneSidedOrlicz_iff_exists.1 hX
  have hY't : IsBigOWith μ (gammaSigma sigma₁) (fun omega => max 0 (Y omega)) A₁ :=
    Provider.Tail.isBigOWith_max_zero hA₁ hYt
  have hZ't : IsBigOWith μ (gammaSigma sigma₂) (fun omega => max 0 (Z omega)) A₂ :=
    Provider.Tail.isBigOWith_max_zero hA₂ hZt
  have hbV : IsBigOWith μ (gammaSigma sigma₁) (fun omega => b * V omega) (b * K) :=
    hVtail.const_mul hb
  have hsum : IsBigOWith μ (gammaSigma sigma₁)
      (fun omega => b * V omega + max 0 (Y omega))
      ((1 + Real.log 2) ^ sigma₁⁻¹ * (b * K + A₁)) :=
    Provider.Multiscale.isBigOWith_gammaSigma_add hsigma₁ hbV hY't
  have hlog2 : (0 : ℝ) < 1 + Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  have hpos : 0 < (1 + Real.log 2) ^ sigma₁⁻¹ * (b * K + A₁) :=
    mul_pos (Real.rpow_pos_of_pos hlog2 _) (by nlinarith [mul_nonneg hb hK])
  have hdom' : ∀ omega, X omega * V omega ≤
      (b * V omega + max 0 (Y omega)) + max 0 (Z omega) := by
    intro omega
    obtain ⟨hV0, hV1⟩ := Set.mem_Icc.1 (hV omega)
    have hle : X omega ≤ b + max 0 (Y omega) + max 0 (Z omega) := by
      have hd := hdom omega
      have hY := le_max_right 0 (Y omega)
      have hZ := le_max_right 0 (Z omega)
      linarith
    have hYZ : 0 ≤ max 0 (Y omega) + max 0 (Z omega) := by
      have hY := le_max_left (0 : ℝ) (Y omega)
      have hZ := le_max_left (0 : ℝ) (Z omega)
      linarith
    linarith [mul_le_mul_of_nonneg_right hle hV0,
      mul_le_mul_of_nonneg_left hV1 hYZ]
  exact ⟨fun omega => b * V omega + max 0 (Y omega), fun omega => max 0 (Z omega),
    hΨ₁, hΨ₂, hpos, hA₂, hXm.mul hVmeas,
    (measurable_const.mul hVmeas).add (measurable_const.max hYm),
    measurable_const.max hZm, hdom', hsum, hZ't⟩

end Ceiling

/-! ## 2. The weighted maximum, scalar layer -/

/-- The half-weight series, at the `(s/2, 1)` spelling of the proved upstream
`Ch05.Section52` geometry lemmas. -/
private theorem three_rpow_quarter_two_eq_half_one {s : ℝ} (j : ℕ) :
    Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) =
      Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) := by
  congr 1
  ring

/-- **The half-weight lies in `[0,1]`.**  `3^{-(s/4).2.j} = 3^{-s j/2} in [0,1]`
for `s >= 0` and every depth `j`: the first half of the pointwise ceiling.  The
upper bound is the proved in-closure `Provider.Percolation.three_rpow_le_one`
(`Percolation/Numerics.lean`), consumed rather than re-derived. -/
theorem three_rpow_quarter_two_mem_Icc {s : ℝ} (hs : 0 ≤ s) (j : ℕ) :
    Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  exact Set.mem_Icc.2 ⟨Real.rpow_nonneg (by norm_num) _,
    Provider.Percolation.three_rpow_le_one (by nlinarith)⟩

/-- **The weighted lane family is bounded above by `1`**, hence its supremum exists
as a genuine supremum (Lean's `⨆` is junk off `BddAbove`).  It is consumed
twice in this file: as the `hbdd` of `ciSup_three_rpow_mul_mem_Icc` (§2) and as
the `BddAbove` slot of the `le_ciSup` in §6. -/
theorem bddAbove_range_three_rpow_mul {s : ℝ} (hs : 0 ≤ s) {g : ℕ → ℝ}
    (hg : ∀ j, g j ∈ Set.Icc (0 : ℝ) 1) :
    BddAbove (Set.range fun j : ℕ => Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) * g j) := by
  refine ⟨1, ?_⟩
  rintro x ⟨j, rfl⟩
  obtain ⟨hw0, hw1⟩ := Set.mem_Icc.1 (three_rpow_quarter_two_mem_Icc hs j)
  obtain ⟨hg0, hg1⟩ := Set.mem_Icc.1 (hg j)
  nlinarith

/-- **The `[0,1]` ceiling of the printed `max_l`.**  For `[0,1]`-valued lanes the
weighted supremum `⨆_j 3^{-s j/2} g j` again lies in `[0,1]`: the lower bound
because lane `0` is nonnegative and the family is bounded above, the upper
bound lane-by-lane.  This is the hypothesis `hV` of §1's engine at the
development carrier, i.e. exactly what makes the two tail lanes cost nothing. -/
theorem ciSup_three_rpow_mul_mem_Icc {s : ℝ} (hs : 0 ≤ s) {g : ℕ → ℝ}
    (hg : ∀ j, g j ∈ Set.Icc (0 : ℝ) 1) :
    (⨆ j : ℕ, Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) * g j) ∈ Set.Icc (0 : ℝ) 1 := by
  have hbdd := bddAbove_range_three_rpow_mul hs hg
  refine Set.mem_Icc.2 ⟨?_, ?_⟩
  · refine le_ciSup_of_le hbdd 0 ?_
    obtain ⟨hw0, -⟩ := Set.mem_Icc.1 (three_rpow_quarter_two_mem_Icc hs 0)
    obtain ⟨hg0, -⟩ := Set.mem_Icc.1 (hg 0)
    exact mul_nonneg hw0 hg0
  · refine ciSup_le fun j => ?_
    obtain ⟨hw0, hw1⟩ := Set.mem_Icc.1 (three_rpow_quarter_two_mem_Icc hs j)
    obtain ⟨hg0, hg1⟩ := Set.mem_Icc.1 (hg j)
    nlinarith

/-- **The half-weight series sums to `c_{s/2}^{-1}`.**
`sum_j 3^{-s j/2} = (1 - 3^{-s/2})^{-1} = (Ch02.geometricDiscount (s/4) 2)^{-1}`,
the total mass of the printed `l`-sum.  Consumed from the upstream
`Ch05.Section52.tsum_rpow_three_neg_mul_nat_eq_inv_geometricDiscount`
(in this file's own import closure, measured), so no twelfth in-repo
`tsum_geometric_of_lt_one` call site is added; the only bridging is the
exponent identity `-(s/4).2.j = -(s/2).j`. -/
theorem tsum_three_rpow_quarter_two {s : ℝ} (hs : 0 < s) :
    ∑' j : ℕ, Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) =
      (Ch02.geometricDiscount (s / 4) 2)⁻¹ := by
  have hdisc : Ch02.geometricDiscount (s / 4) 2 = Ch02.geometricDiscount (s / 2) 1 := by
    change 1 - Real.rpow (3 : ℝ) (-(s / 4) * 2) = 1 - Real.rpow (3 : ℝ) (-(s / 2) * 1)
    congr 2
    ring
  rw [tsum_congr fun j : ℕ => three_rpow_quarter_two_eq_half_one (s := s) j, hdisc]
  exact Ch05.Section52.tsum_rpow_three_neg_mul_nat_eq_inv_geometricDiscount
    (gap := s / 2) (by linarith)

/-- **`c_{s/2}^{-1} <= 20 s^{-1}` on the printed window.**  The `(s/4, 2)` instance
of the upstream `Ch02.inv_geometricDiscount_le_five_inv`
(`DiscountBounds.lean`).  This is the S of the two factors `s^{-1}` behind
the printed `s^{-2}` (the first is the averaged-indicator display's `rho^{-1} =
d/s`), and it is the one the print produces by "summing over `l` instead of
maxing". -/
theorem inv_geometricDiscount_quarter_two_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    (Ch02.geometricDiscount (s / 4) 2)⁻¹ ≤ 20 * s⁻¹ := by
  have h := Ch02.inv_geometricDiscount_le_five_inv (s := s / 4) (p := 2)
    (by linarith) (by linarith) (by norm_num)
  have heq : (5 : ℝ) * (s / 4)⁻¹ = 20 * s⁻¹ := by
    field_simp
    norm_num
  linarith [heq ▸ h]

/-- **Summability of the weighted `[0,1]` lane family**, by comparison with the raw
geometric series, whose summability is the upstream
`Ch05.Section52.summable_rpow_three_neg_mul_nat`. -/
theorem summable_three_rpow_mul {s : ℝ} (hs : 0 < s) {g : ℕ → ℝ}
    (hg : ∀ j, g j ∈ Set.Icc (0 : ℝ) 1) :
    Summable fun j : ℕ => Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) * g j := by
  have hmaj : Summable fun j : ℕ => Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) :=
    (Ch05.Section52.summable_rpow_three_neg_mul_nat (gap := s / 2) (by linarith)).congr
      fun j => (three_rpow_quarter_two_eq_half_one (s := s) j).symm
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hmaj
  · obtain ⟨hw0, -⟩ := Set.mem_Icc.1 (three_rpow_quarter_two_mem_Icc hs.le j)
    obtain ⟨hg0, -⟩ := Set.mem_Icc.1 (hg j)
    exact mul_nonneg hw0 hg0
  · obtain ⟨-, hg1⟩ := Set.mem_Icc.1 (hg j)
    obtain ⟨hw0, -⟩ := Set.mem_Icc.1 (three_rpow_quarter_two_mem_Icc hs.le j)
    exact mul_le_of_le_one_right hw0 hg1

/-- **The printed `max` is dominated by the printed `sum`** — the last step of
the printed proof ("summing over `l` instead of maxing").
Every lane is nonnegative and the family is summable, so each lane is at most
the total, hence so is their supremum.  This is the ONLY place the `l`-sum is
used, and in §5 it is applied to the deterministic lane alone. -/
theorem ciSup_three_rpow_mul_le_tsum {s : ℝ} (hs : 0 < s) {g : ℕ → ℝ}
    (hg : ∀ j, g j ∈ Set.Icc (0 : ℝ) 1) :
    (⨆ j : ℕ, Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) * g j) ≤
      ∑' j : ℕ, Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) * g j := by
  have hsummable := summable_three_rpow_mul hs hg
  refine ciSup_le fun j => ?_
  refine hsummable.le_tsum j fun i _ => ?_
  obtain ⟨hw0, -⟩ := Set.mem_Icc.1 (three_rpow_quarter_two_mem_Icc hs.le i)
  obtain ⟨hg0, -⟩ := Set.mem_Icc.1 (hg i)
  exact mul_nonneg hw0 hg0

/-! ## 3. The `l`-aggregation engine -/

section Aggregation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The `l`-aggregation.**  If every lane obeys the SAME `Gamma_1` display at
amplitude `A` — which is what the printed averaged-indicator display gives,
since its amplitude does not depend on `l` — then the printed maximum obeys

```
    max_j 3^{-s j/2} G_j  <=  O_{Gamma_1}( gammaTriangleConst 1 . B ) ,
    B >= c_{s/2}^{-1} . A .
```

Route: weight each lane (`IsBigOWith.const_mul`), sum by the countable
`Gamma_1` triangle at nonnegative amplitudes
(`Provider.Orlicz.isBigOWith_gammaSigma_tsum_of_nonneg_amplitude_of_tsum_le`),
evaluate the amplitude series in closed form, then dominate the maximum by the
sum (`IsBigOWith.of_le`). -/
theorem isBigOWith_gammaOne_ciSup_three_rpow_mul [IsFiniteMeasure μ]
    {G : ℕ → Ω → ℝ} {s A B : ℝ} (hs : 0 < s) (hA : 0 ≤ A)
    (hG : ∀ j omega, G j omega ∈ Set.Icc (0 : ℝ) 1)
    (hGmeas : ∀ j, Measurable (G j))
    (hGt : ∀ j, IsBigOWith μ (gammaSigma 1) (G j) A)
    (hB : (Ch02.geometricDiscount (s / 4) 2)⁻¹ * A ≤ B) :
    IsBigOWith μ (gammaSigma 1)
      (fun omega => ⨆ j : ℕ, Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) * G j omega)
      (gammaTriangleConst 1 * B) := by
  have hwnonneg : ∀ j : ℕ, (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) :=
    fun j => (Set.mem_Icc.1 (three_rpow_quarter_two_mem_Icc hs.le j)).1
  have hlane : ∀ j : ℕ, IsBigOWith μ (gammaSigma 1)
      (fun omega => Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) * G j omega)
      (Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) * A) :=
    fun j => (hGt j).const_mul (hwnonneg j)
  have hasummable : Summable fun j : ℕ =>
      Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) * A :=
    ((Ch05.Section52.summable_rpow_three_neg_mul_nat (gap := s / 2)
      (by linarith)).congr
        fun j => (three_rpow_quarter_two_eq_half_one (s := s) j).symm).mul_right A
  have hamp : (∑' j : ℕ, Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) * A) ≤ B := by
    rw [tsum_mul_right, tsum_three_rpow_quarter_two hs]
    exact hB
  have htsum : IsBigOWith μ (gammaSigma 1)
      (fun omega => ∑' j : ℕ, Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) * G j omega)
      (gammaTriangleConst 1 * B) :=
    Provider.Orlicz.isBigOWith_gammaSigma_tsum_of_nonneg_amplitude_of_tsum_le
      one_pos
      (fun j omega => mul_nonneg (hwnonneg j) (Set.mem_Icc.1 (hG j omega)).1)
      (fun j => measurable_const.mul (hGmeas j))
      (fun j => mul_nonneg (hwnonneg j) hA)
      hasummable hlane hamp
  exact htsum.of_le fun omega =>
    ciSup_three_rpow_mul_le_tsum hs (fun j => hG j omega)

/-- **Measurability of the weighted maximum**, from `Measurable.iSup` over the
countable lane family (no `BddAbove` hypothesis is needed for measurability).
It is the `hVmeas` slot of §1's engine. -/
theorem measurable_ciSup_three_rpow_mul {G : ℕ → Ω → ℝ} {s : ℝ}
    (hGmeas : ∀ j, Measurable (G j)) :
    Measurable fun omega =>
      ⨆ j : ℕ, Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) * G j omega :=
  Measurable.iSup fun j => measurable_const.mul (hGmeas j)

end Aggregation

/-! ## 4. The bad-event maximum at the development carrier -/

/-- Measurability of the bad event's complement.  One-line restatement of the
file-scoped `private` `measurableSet_compl_goodLocalEventAt`
(`BadEventIngredients.lean`), from the same two proved publics
(`Cutoff.measurable_translateCutoffSample`,
`Provider.BadEvents.measurableSet_goodLocalEvent`); disclosed as a twin in the
module header because the original cannot be consumed across files. -/
private theorem measurableSet_compl_goodLocalEventAt' (M : ABKModel d) (Cbad : ℝ)
    (l n : ℤ) (z : Vec d) :
    MeasurableSet
      (Algsuperdiff.Frozen.Section3.goodLocalEventAt M Cbad l n z)ᶜ :=
  (((Cutoff.measurable_translateCutoffSample z)
    (Provider.BadEvents.measurableSet_goodLocalEvent M Cbad (originCube d l) n))).compl

/-- The unweighted `rho`-th power of an indicator average lies in `[0,1]`: the `w =
1` instance of the proved `weightedIndicatorAverage_rpow_mem_Icc`
(`BadEventCeiling.lean`), D from it rather than re-proved. -/
private theorem indicatorAverage_rpow_mem_Icc' {iota Omega : Type*} (F : Finset iota)
    (B : iota → Set Omega) {rho : ℝ} (hrho : 0 ≤ rho) (omega : Omega) :
    ((F.card : ℝ)⁻¹ * ∑ z ∈ F, (B z).indicator (fun _ => (1 : ℝ)) omega) ^ rho ∈
      Set.Icc (0 : ℝ) 1 := by
  have h := weightedIndicatorAverage_rpow_mem_Icc F B (w := 1)
    zero_le_one le_rfl hrho omega
  rwa [one_mul] at h

/-- Measurability of one bad-event lane, `omega |-> (avsum_z 1_{not Q})^rho`.
The same three-step composition that `ceiling_product` performs inline
(`BadEventIngredients.lean`), restated because that proof exports nothing. -/
private theorem measurable_badEventAverage_rpow (M : ABKModel d) (Cbad : ℝ)
    (l n : ℤ) (F : Finset (Vec d)) {rho : ℝ} (hrho : 0 ≤ rho) :
    Measurable fun omega : Cutoff.CutoffSample d =>
      (((F.card : ℝ)⁻¹ * ∑ z ∈ F,
        (Algsuperdiff.Frozen.Section3.goodLocalEventAt M Cbad l n z)ᶜ.indicator
          (fun _ => (1 : ℝ)) omega)) ^ rho :=
  (Real.continuous_rpow_const hrho).measurable.comp
    ((Finset.measurable_sum F fun z _ =>
      measurable_const.indicator (measurableSet_compl_goodLocalEventAt' M Cbad l n z)).const_mul
        ((F.card : ℝ)⁻¹))

/-- **The `l`-aggregation of the bad-event factor at the development carrier.**

```
    max_{l <= m} 3^{-s(m-l)/2} ( avsum_{z in F} 1_{not Q(l,l-h,z)} )^{s/d}
      <=  O_{Gamma_1}( gammaTriangleConst 1 . 20 s^{-1}
              . 16 d s^{-1} ( c^{-1} cstar^{-1} 3^{5h} cgamma
                              + exp(-c E^{-2} cgamma^{-1}) ) ) .
```

Every lane is the proved per-lane display
`exists_badEvent_indicatorAverage_rpow_at_s_div_d` read at `l := m - j`, whose
amplitude is independent of `l`; the aggregation engine of §3 then pays the `l`-sum
once, at the total mass `c_{s/2}^{-1} <= 20 s^{-1}`.

Binders beyond the two producers': `1 <= h` (module header §4 — the `j = 0`
lane's bad event needs the state one scale below `m`) and per-lane nonemptiness
of the free grid family `F`. -/
theorem exists_badEventSup_isBigOWith_gammaOne (d : ℕ) :
    ∃ Ccg c : ℝ, 1 ≤ Ccg ∧ 0 < c ∧
      ∀ H : ℝ, 0 ≤ H → ∃ C : ℝ, 1 ≤ C ∧
        ∀ (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E}) (epsilon : ℝ) (h : ℕ),
          Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
          epsilon ∈ Set.Ioc 0 (1 / 2) →
          (h : ℝ) ≤ H * |Real.log epsilon| + 1 →
          (Disorder.cstar M)⁻¹ * epsilon ^ (-C) ≤ (E : ℝ) →
          M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
          1 ≤ h →
          ∀ s : ℝ, 0 < s → s ≤ 1 →
          ∀ F : ℕ → Finset (Vec d), (∀ j : ℕ, (F j).Nonempty) →
            IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 1)
              (fun omega => ⨆ j : ℕ, Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) *
                (((F j).card : ℝ)⁻¹ * ∑ z ∈ F j,
                  (Algsuperdiff.Frozen.Section3.goodLocalEventAt M (2 * Ccg)
                    (m - (j : ℤ)) (m - (j : ℤ) - (h : ℤ)) z)ᶜ.indicator
                      (fun _ => (1 : ℝ)) omega) ^ (s / (d : ℝ)))
              (gammaTriangleConst 1 *
                (20 * s⁻¹ *
                  (16 * (d : ℝ) * s⁻¹ *
                    (c⁻¹ * (Disorder.cstar M)⁻¹ * (3 : ℝ) ^ (5 * (h : ℝ)) * M.gamma +
                      Real.exp (-(c * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)))))) := by
  obtain ⟨Ccg, c, hCcg, hc, hbad⟩ := exists_badEvent_indicatorAverage_rpow_at_s_div_d d
  refine ⟨Ccg, c, hCcg, hc, ?_⟩
  intro H hH
  obtain ⟨C, hC, hbadC⟩ := hbad H hH
  refine ⟨C, hC, ?_⟩
  intro M m E epsilon h hS heps hh hscale hgammaE hh1 s hs hs1 F hF
  have hcstar : 0 < Disorder.cstar M := Provider.Orlicz.cstar_pos M
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hrho : (0 : ℝ) ≤ s / (d : ℝ) := by positivity
  have hA0 : (0 : ℝ) ≤ 16 * (d : ℝ) * s⁻¹ *
      (c⁻¹ * (Disorder.cstar M)⁻¹ * (3 : ℝ) ^ (5 * (h : ℝ)) * M.gamma +
        Real.exp (-(c * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) := by
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (5 * (h : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have hexp : (0 : ℝ) < Real.exp (-(c * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) := Real.exp_pos _
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hcinv : (0 : ℝ) < c⁻¹ := inv_pos.2 hc
    have hcsinv : (0 : ℝ) < (Disorder.cstar M)⁻¹ := inv_pos.2 hcstar
    have hsinv : (0 : ℝ) < s⁻¹ := inv_pos.2 hs
    positivity
  refine isBigOWith_gammaOne_ciSup_three_rpow_mul hs hA0
    (fun j omega => indicatorAverage_rpow_mem_Icc' (F j) _ hrho omega)
    (fun j => measurable_badEventAverage_rpow M (2 * Ccg) (m - (j : ℤ))
      (m - (j : ℤ) - (h : ℤ)) (F j) hrho)
    (fun j => ?_) ?_
  · exact hbadC M m E epsilon h (m - (j : ℤ)) hS heps hh hscale hgammaE
      (by omega) s hs hs1 (F j) (hF j)
  · exact mul_le_mul_of_nonneg_right (inv_geometricDiscount_quarter_two_le hs hs1) hA0

/-! ## 5. `e.local.bad.events.summed` -/

/-- **`e.local.bad.events.summed`**, at the
multiscale root's own binder set:

```
    E^2_{s/4,infty,2}(cu_m; a_m, shom_m)
      . max_{l <= m} 3^{-s(m-l)/2}( avsum_{z in F} 1_{not Q(l,l-h,z)} )^{s/d}
  <=  O_{Gamma_1}( C(d) cstar^{-1} s^{-2} ( 3^{5h} cgamma
                                            + exp(-c E^{-2} cgamma^{-1}) ) )
    + O_{Gamma_{2/7}}( C exp( -Ccg^{-1} E^{-2} cgamma^{-1} ) ) ,
```

with both amplitudes written out in full rather than absorbed into a `C`.  The
left factor is the Section 3 observable, the maximum is the `⨆ j : ℕ` of the
reindexing `j = m - l`, and there is NO deterministic term on the right — that
is the whole point of §1's engine, and the reason the bad factor's own
`Gamma_1` smallness is needed.

The three ingredient displays enter exactly once each: `exists_crude_bound`
(display 1) as the two-term input, the per-lane averaged-indicator display
(display 3, at `rho = s/d`) through the `l`-aggregation, and the `[0,1]`
ceiling (`BadEventCeiling`) as the pointwise bound on the maximum.  Display 2
(`e.badevent.indicator.propagate`) is NOT on this path: the proved display 3 is
an independent consumer of the same per-site probability input.

Amplitude reading (module header §3): `8 Ccg + 8. 3^{cgamma}.
lowerEllipticityProfile.` is the crude bound's deterministic shift, a pure
constant `<= 24 Ccg` on the window; it is the ONLY factor that meets the
`l`-sum's `20 s^{-1}`.  The consumer still owes `3^{5h} <= eps^{-C}` at `h:=
ceil(C|log eps|)`. -/
theorem exists_badEventSummed_bound (d : ℕ) :
    ∃ Ccg Cshom Cbad c : ℝ, 0 < Ccg ∧ 0 < Cshom ∧ 1 ≤ Cbad ∧ 0 < c ∧
      ∀ H : ℝ, 0 ≤ H → ∃ C : ℝ, 1 ≤ C ∧
        ∀ (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E}) (epsilon : ℝ) (h : ℕ),
          Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
          mStarStar M < m →
          max (Real.exp (Ccg / (1 / 7))) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
          Cshom * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
          (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
          M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
          epsilon ∈ Set.Ioc 0 (1 / 2) →
          (h : ℝ) ≤ H * |Real.log epsilon| + 1 →
          (Disorder.cstar M)⁻¹ * epsilon ^ (-C) ≤ (E : ℝ) →
          1 ≤ h →
          ∀ s : ℝ, ∀ hs8 : 8 * M.gamma ≤ s, s ≤ 1 →
          ∀ F : ℕ → Finset (Vec d), (∀ j : ℕ, (F j).Nonempty) →
            Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
              (gammaSigma 1) (gammaSigma (2 / 7))
              (fun omega =>
                Observable.cutoffHomogenizationError M m
                    ⟨s / 4,
                      quarter_pos_of_eight_gamma_le M.shellPrefix.gamma_pos hs8⟩
                    omega ^ 2 *
                  ⨆ j : ℕ, Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) *
                    (((F j).card : ℝ)⁻¹ * ∑ z ∈ F j,
                      (Algsuperdiff.Frozen.Section3.goodLocalEventAt M (2 * Cbad)
                        (m - (j : ℤ)) (m - (j : ℤ) - (h : ℤ)) z)ᶜ.indicator
                          (fun _ => (1 : ℝ)) omega) ^ (s / (d : ℝ)))
              ((1 + Real.log 2) ^ (1 : ℝ)⁻¹ *
                ((8 * Ccg +
                    8 * (3 : ℝ) ^ M.gamma *
                      lowerEllipticityProfile Ccg M.gamma (s / 4)
                        Provider.Tail.exponentTwo) *
                    (gammaTriangleConst 1 *
                      (20 * s⁻¹ *
                        (16 * (d : ℝ) * s⁻¹ *
                          (c⁻¹ * (Disorder.cstar M)⁻¹ * (3 : ℝ) ^ (5 * (h : ℝ)) *
                              M.gamma +
                            Real.exp (-(c * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)))))) +
                  8 * (Ccg * (Disorder.cstar M)⁻¹ * (s / 4) * M.gamma *
                    (2 * (s / 4) - M.gamma)⁻¹ ^ 3)))
              ((1 + Real.log 2) ^ ((2 : ℝ) / 7)⁻¹ *
                (8 * Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) +
                  8 * (3 : ℝ) ^ M.gamma *
                    Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)))) := by
  obtain ⟨Ccg, Cshom, hCcg, hCshom, hcrude⟩ := exists_crude_bound d
  obtain ⟨Cbad, c, hCbad, hc, hsup⟩ := exists_badEventSup_isBigOWith_gammaOne d
  refine ⟨Ccg, Cshom, Cbad, c, hCcg, hCshom, hCbad, hc, ?_⟩
  intro H hH
  obtain ⟨C, hC, hsupC⟩ := hsup H hH
  refine ⟨C, hC, ?_⟩
  intro M m E epsilon h hS hmStar hE hEshom hEgamma hgammaE heps hh hscale hh1 s hs8 hs1 F hF
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hcstar : 0 < Disorder.cstar M := Provider.Orlicz.cstar_pos M
  have hs : (0 : ℝ) < s := by linarith
  have hrho : (0 : ℝ) ≤ s / (d : ℝ) := by positivity
  have hcrudeM := hcrude M m E hS hmStar hE hEshom hEgamma hgammaE s hs8 hs1
  have hsupM := hsupC M m E epsilon h hS heps hh hscale hgammaE hh1 s hs hs1 F hF
  have hb0 : (0 : ℝ) ≤ 8 * Ccg +
      8 * (3 : ℝ) ^ M.gamma *
        lowerEllipticityProfile Ccg M.gamma (s / 4) Provider.Tail.exponentTwo := by
    rw [Provider.Tail.lowerEllipticityProfile_exponentTwo]
    have hden : (0 : ℝ) < 2 * (s / 4) - M.gamma := by linarith
    have h3 : (0 : ℝ) < (3 : ℝ) ^ M.gamma := Real.rpow_pos_of_pos (by norm_num) _
    have hprof : (0 : ℝ) ≤ Ccg * (s / 4) * (2 * (s / 4) - M.gamma)⁻¹ := by positivity
    nlinarith [hCcg.le, h3.le]
  have hK0 : (0 : ℝ) ≤ gammaTriangleConst 1 *
      (20 * s⁻¹ *
        (16 * (d : ℝ) * s⁻¹ *
          (c⁻¹ * (Disorder.cstar M)⁻¹ * (3 : ℝ) ^ (5 * (h : ℝ)) * M.gamma +
            Real.exp (-(c * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))))) := by
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (5 * (h : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have hexp : (0 : ℝ) < Real.exp (-(c * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) := Real.exp_pos _
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hcinv : (0 : ℝ) < c⁻¹ := inv_pos.2 hc
    have hcsinv : (0 : ℝ) < (Disorder.cstar M)⁻¹ := inv_pos.2 hcstar
    have hsinv : (0 : ℝ) < s⁻¹ := inv_pos.2 hs
    have hgt : (0 : ℝ) < gammaTriangleConst 1 := gammaTriangleConst_pos
    positivity
  exact isTwoTermBigOWith_mul_ceiling one_pos hb0 hK0
    (measurable_ciSup_three_rpow_mul (s := s)
      (fun j => measurable_badEventAverage_rpow M (2 * Cbad) (m - (j : ℤ))
        (m - (j : ℤ) - (h : ℤ)) (F j) hrho))
    (fun omega => ciSup_three_rpow_mul_mem_Icc hs.le
      (fun j => indicatorAverage_rpow_mem_Icc' (F j) _ hrho omega))
    hsupM hcrudeM

/-! ## 6. The carrier bridge and the composed endpoint -/

/-- ```
    for a.e. omega:   E_{s,infty,2}(cu_m; a_m, shom_m)(omega)^2
      =  Ch02.HomogenizationErrorOnCube (cu_m) s infinity (finite 2)
           (a_m(omega)) (shom_m . Id) ^ 2 .
```

**Disclosure (the obligation's premise is withdrawn).**  The unsquared push is
NOT missing from this repository: it is the proved
`Observable.cutoffHomogenizationError_ae_eq_homogenizationErrorOnCube`
(`Observable/CutoffHomogenizationError.lean`), which already has eight in-repo
consumers (module header §8).  What follows is only its squared restatement,
at the `NeZero d` spelling `Provider.Orlicz.neZero_of_model M` that this
file's composition uses; it is a two-line consequence and is delivered as a
public only because the fourth term consumes the square. -/
theorem ae_sq_cutoffHomogenizationError_eq_homogenizationErrorOnCube_sq
    (M : ABKModel d) (m : ℤ) (s : {s : ℝ // 0 < s}) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Observable.cutoffHomogenizationError M m s omega ^ 2 =
        (@Ch02.HomogenizationErrorOnCube d (originCube d m) (s : ℝ) Ch02.MultiscaleExponent.infinity
          (Ch02.MultiscaleExponent.finite 2)
          (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega)
          (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m))) ^ 2 := by
  filter_upwards [Observable.cutoffHomogenizationError_ae_eq_homogenizationErrorOnCube
    M m s] with omega homega
  rw [homega]

end

end Algsuperdiff.Section3.Provider.MultiscaleEstimate
