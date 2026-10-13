/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.InitialJLBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.CombineIntegerDownscale
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.StarredFluctuationIntegrable
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.AmplitudeBridge

/-!
# FiniteRecurrence

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `(e.J.bound.by.indyhyp)` in its A.4 finite-corridor form

This module is a Provider helper and makes no source-node status claim.

## What is carried here

Items `(I-2)` and `(I-3)` of the depgraph record for the node
`p.combine.corrected`, the finite good-event Besov step:

* `(I-2)` the two substitutions into the proved Step-1 display
  `exists_integral_cutoffResponseJ_le_initialJLBoundDisplay`
  (`InitialJLBound.lean`): the printed mean gap by the proved Step-2
  display
  `coefficientCutoffLaw_sq_abs_annealedSigmaStarInvScalarAtScale_sub_le`
  (`CombineIntegerDownscale.lean`), and the two variance blocks by the
  proved unconditional corridor bound
  `exists_coefficientCutoff_finiteCorridor_starInverseVariance_withS_bound'`
  (`StarredFluctuationIntegrable.lean`);
* `(I-3)` the resulting finite recurrence, delivered twice: at integer scales
  (`exists_integral_cutoffResponseJ_le_finiteCorridorIndyhypDisplay`) and in
  the `A.4` reindexing `t = n - L` on `ℕ`
  (`exists_finiteRecurrence_integral_cutoffResponseJ`), the second in exactly
  the input shape of the proved weighted-mean iteration
  `finiteCorridor_weightedDefect_iteration`
  (`FiniteCorridorIteration.lean`), whose `hrec` binder it is.

## The delivered displays

At `delta_1 := 10^9 E^2 gamma` the integer-scale public delivers

`E[J(cu_m, sigmabar_L^{-1/2} e, sigmabar_L^{1/2} e; a_L)]`
`  <= A delta_1 (delta_1 + 3^{-(m-L)})`
`     + C sum_{n=L}^m 3^{-(m-n)} (E[J(cu_n)] - E[J(cu_m)])`,

which is the printed `e.J.bound.by.indyhyp` with the printed bi-infinite defect
sum `sum_{n=-infty}^m` replaced by the printed finite corridor `sum_{n=L}^m` of
`e.initial.JL.bound`.  That replacement is exactly what `A.4` prescribes: every
scale used lies in `[L, m]`, so the iteration never invokes a mean below the
infrared cutoff, for which `e.iter.init` supplies no estimate.

The `ℕ`-reindexed public sets `F t := E[J(cu_{L+t}, ...)]` and delivers

`F t <= A delta_1 (delta_1 + 3^{-t}) + C sum_{k=1}^{t} 3^{-k} (F (t-k) - F t)`,
`    for every t > j_0`,

which is the `A.4` display verbatim.  Both `A` and `C` and the separation `j_0`
are selected before the model, the cutoff `L` and the unit direction `e`, as
`A.4` requires.

## Shape match against `A.4`, with every constant disclosed

Write `C_1`, `C_bad` for the two constants of the proved Step-1 display,
`C_var` for the constant of the proved corridor variance bound (all three
existential, all at least `1`), and `sigmabar_L` for the running coarse-grained
diffusivity.

1. **The defect coefficient** is `C := C_1`, the Step-1 display's own constant.
   The gate binder `C 3^{-(3/4)(m-L)} <= 1/4` is therefore byte-identical to the
   proved one.
2. **The forcing amplitude** is `A := 3 C_1 C_var + 7 C_1 + C_bad`, assembled as:
   * `3 C_1 C_var` from the two variance blocks.  The proved corridor bound
     gives `sigmabar_L^2 var[sigma_{L,*}^{-1}(cu_n)] +
     var[sigma_{L,*}^{-1}kappa_L(cu_n)]` `  <= 2 C_var delta (delta +
     3^{-d(n-L)})` at every corridor scale `n`, where `delta` is the lane's
     two-term amplitude (see 4 below).  Summing against the printed weight
     `3^{-(m-n)}` uses the two corridor sums `sum_{n=L}^m 3^{-(m-n)} <= 3/2`
     and `sum_{n=L}^m 3^{-(m-n)} 3^{-d(n-L)} <= (3/2) 3^{-(m-L)}`.  The second
     needs `2 <= d`; that is `M.shellPrefix.dimension`, a field of the standing
     model, **not** an added hypothesis.  The product of the two `3/2`s with
     the `2` of the proved bound is the `3`.
   * `6 C_1` from the mean gap.  The proved Step-2 display gives
     `|sigmabar_{L,*}^{-1}(cu_m) - sigmabar_{L,*}^{-1}(cu_n)|^2` `  <= 4
     sigmabar_L^{-2} delta_1^2`, so the display's `sigmabar_L^2` weighting
     cancels the `sigmabar_L^{-2}` and leaves `4 delta_1^2` at every corridor
     scale; the corridor weight then contributes the `3/2`, giving `6
     delta_1^2`.
   * `C_1 + C_bad` from the collapse of the Step-1 display's two amplitude
     terms `C_1 delta_1^2 + C_bad (10^9 E^2 gamma)^2`.  Per `A.3` and `A.4`,
     which both **set** `delta_1 := 10^9 E^2 gamma`, the delivered statements
     are instantiated at that value, so the two terms are terms in one
     amplitude.  This is the adjudication recorded `(I-1)`.
   * finally `delta_1^2 <= delta_1 (delta_1 + 3^{-(m-L)})` absorbs the three
     pure-square blocks into the `A.4` forcing shape.
3. **The rate.**  The lag weights are the printed `3^{-k}` and the forcing
   decay is the printed `3^{-t}`; both are the single parameter `r = 1/3` of
   the proved iteration engine, which is the only admissible value there (its
   `hr3` caps `r` at `1/3`, and the printed lag weights force `r >= 1/3`).
4. **The two-term amplitude, absorbed.**  The proved corridor variance bound
   carries the lane's `delta = E^2 gamma + exp(-2 E^{-3} gamma^{-1})`, strictly
   larger than the printed `delta_1`-scale amplitude; this is the caveat
   recorded on that display `(B)`.  It is absorbed here, unconditionally under
   the proposition's own regime `gamma <= E^{-10}` and `1 <= E`, by
   `twoTermAmplitude_le_amplitude` below: `exp(-2 E^{-3} gamma^{-1}) <= E^2
   gamma`, hence `delta <= 2 E^2 gamma`, hence `delta <= 2 * 10^{-9} delta_1 <=
   delta_1`.  The elementary input is `exp(-x) <= 4/x^2` for `x > 0`.
5. The delivered `Chom` is their maximum.  Both places it is consumed are
   monotone in the right direction: the gate `gamma <= Chom^{-1} E^{-2}
   epsilon` is *stronger* for a larger `Chom`, and so is the corridor
   separation `L <= m - Chom |log epsilon|` since `|log epsilon| >= 0`.
   Nothing is weakened by the composition.

## Source premises, standing data, typing data, and no conditional input

Every caller-supplied mathematical proposition of the two publics is a threaded
premise of one of the three proved displays.  **There is no conditional A
input**: the module's conditional-A count is zero.

* `hEfloor`, `hregime` --- the `A.3` induction regime, verbatim from the Step-1
  display;
* `hLower` --- the frozen preceding-error clause, verbatim from the Step-1
  display and from the corridor variance bound (the two carry byte-identical
  binders);
* `hepsilon`, `hgate` --- the printed smallness window and gate, at the composed
  `Chom` (see 5 above);
* `hsep` (`L <= m - 2`) --- inherited verbatim from the Step-1 display, whose
  own disclosure pins the single excluded cutoff `L = m - 1` to (v);
* `hsepvar` (`L <= m - Chom |log epsilon|`) --- the corridor-separation premise
  of the proved corridor variance bound.  In the `ℕ`-reindexed public this
  reads `Chom |log epsilon| <= t`, i.e. the recurrence is delivered above an
  `epsilon`-dependent depth.  `A.4` asks for a dimension-only `j_0(d)`; the
  delivered `j_0` *is* dimension-only, but the separation binder rides
  alongside it.  This is a threaded premise of a proved display, not an
  addition, and it is the consumer's to discharge together with `A.4`'s choice
  of `k_1`;
* `hgateC` --- the printed gate `C 3^{-(1-s)(m-L)} <= 1/4` at the `s = 1/4`
  endpoint, verbatim from the Step-1 display.  In the `ℕ`-reindexed public it
  is discharged internally from `j_0 < t`;
* `he` --- `e.pq.normed` in the Step-1 display's form `|e| = 1`.

The amplitude-bridge conclusion (`A.3`'s `X_R` step) --- the shape `10^9 E^2
gamma in Ioc 0 (1/2)` together with the diagonal fourth-moment bound at every
cutoff `<= m - 1` --- is **not** a binder of either public.  Its producer, item
`(I-1)`, is the proved `AmplitudeBridge.lean`'s
`amplitude_mem_Ioc_and_lintegral_pow_four_le`; that module is imported above
and the conclusion is *consumed*, by the bare application
`amplitude_mem_Ioc_and_lintegral_pow_four_le M hChom10 hEfloor hregime hLower
hepsilon hgate hs`, every premise of which is either a binder of the publics
below or the internal `10^9 <= Chom` and `hs`.  The regularity index `hs: 0 <
1/4`, which selects the exponent `s = 1/4`, is likewise not a binder: it is
proof-irrelevant typing data and is produced internally by `norm_num`.  Nothing
beyond the bullets above is caller-supplied.

Standing data: `M : ABKModel d` (whence `2 <= d` and `0 < gamma`).  Typing data:
`d`, `[NeZero d]`, `m`, `L`, `t`, `e`, `E`, `epsilon`.

## The horizon and the `epsilon`-dependent depth, adjudicated

The recurrence is delivered at one observation scale at a time, with the
preceding-error clause taken at that observation scale, exactly as the proved
Step-1 display requires and exactly as `A.3` prescribes ("fix `M`, assume
`S(M-1,E)`").  Two consequences, both adjudicated and both costless:

1. **The horizon.**  The proved iteration engine's `hrec` binder ranges over
   *all* `t : ℕ`, while a consumer holding the clause at one top scale `m` gets
   the recurrence only for `L + t <= m`.  This costs nothing: the
   zero-truncation `G t := if t <= T then F t else 0` satisfies all three
   engine binders, since beyond `T` the recurrence degenerates to `0 <=
   nonneg`.  Every downstream consumption (; the cutoff-union completion) lies
   inside that horizon.
2. **The `epsilon`-dependent depth** carried by `hsepvar`/`hsept` is absorbed
   *consumer-side*, by a shift performed with the sharp geometric prefix
   `sum_{k > j} r^k <= (3/2) r^{j+1}` and the engine applied at `j_0 = 0`, with
   `A' := A + (3/2) r`; then `K = finiteCorridorAmplitude A' r 0 = 2 (A' + 2
   K_0)` is dimension-only, and the budget `k_1 <= C(d) |log epsilon|`
   survives.  **Do NOT instead pass `j_0' := max j_0 ceil(Chom |log epsilon|)`
   to the engine.**  `finiteCorridorAmplitude A r j_0 = 2 (A + 2 K_0 + j_0 r)`
   is *linear* in `j_0`, so that route makes `K ~ |log epsilon|` and hence
   demands `gamma <~ epsilon / (|log epsilon| E^2)`, contradicting `A.4`'s
   manuscript smallness condition `gamma <= C(d)^{-1} E^{-2} epsilon`.

The engine's other two binders, `hFnonneg` and the crude initialization
`hcrude` (`e.iter.init`), are separate producers and are not supplied here.

## References

* ABK26, Section 3.5: `p.combine.under.S`, its Step 5, and the proof of
  `p.homogenization.step`.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open Algsuperdiff.Section3

/-! ### The corridor geometric quintet, factored through one reindex -/

/-- `3^{-k}` at a natural exponent is the natural power `(1/3)^k`. -/
private theorem rpow_three_neg_natCast (k : ℕ) : (3 : ℝ) ^ (-(k : ℝ)) = (1 / 3 : ℝ) ^ k := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast, ← inv_pow]
  norm_num

/-- The printed corridor weight `3^{-(m-n)}` as a natural power of `1/3`. -/
private theorem rpow_three_neg_sub_eq_pow {m n : ℤ} (hnm : n ≤ m) :
    (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) = (1 / 3 : ℝ) ^ ((m - n).toNat) := by
  have hcast : ((m - n : ℤ) : ℝ) = (((m - n).toNat : ℕ) : ℝ) := by
    have h0 : (0 : ℤ) ≤ m - n := by omega
    exact_mod_cast (Int.toNat_of_nonneg h0).symm
  rw [hcast]
  exact rpow_three_neg_natCast _

/-- The reindexing `n ↦ m - n` of the printed integer corridor `[L, m]` onto the
lag range `{0, …, m - L}`.  This is the `A.4` change of variable `t = n - L`, in
the equivalent lag form. -/
private theorem sum_Icc_reindex {L m : ℤ} (hLm : L ≤ m) (w : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc L m, w ((m - n).toNat) =
      ∑ k ∈ Finset.range ((m - L).toNat + 1), w k := by
  refine Finset.sum_nbij' (fun n : ℤ => (m - n).toNat) (fun k : ℕ => m - (k : ℤ))
    ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_range]
    omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Icc]
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    show m - (((m - n).toNat : ℕ) : ℤ) = n
    omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    show ((m - (m - (k : ℤ))).toNat) = k
    omega
  · intro n _
    rfl

/-- The lag convolution of the printed weight `(1/3)^k` with a decay of ratio at
most `1/9`.  The gap between the two ratios is what makes the convolution
geometric at the printed rate rather than merely summable. -/
private theorem sum_range_geom_conv_le {b : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ 1 / 9) (t : ℕ) :
    ∑ k ∈ Finset.range (t + 1), (1 / 3 : ℝ) ^ k * b ^ (t - k) ≤
      3 / 2 * (1 / 3 : ℝ) ^ t := by
  have hstep : ∀ k ∈ Finset.range (t + 1),
      (1 / 3 : ℝ) ^ k * b ^ (t - k) ≤ (1 / 3 : ℝ) ^ t * (1 / 3 : ℝ) ^ (t - k) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have hbk : b ^ (t - k) ≤ (1 / 9 : ℝ) ^ (t - k) := pow_le_pow_left₀ hb0 hb _
    have hid : (1 / 3 : ℝ) ^ k * (1 / 9 : ℝ) ^ (t - k) =
        (1 / 3 : ℝ) ^ t * (1 / 3 : ℝ) ^ (t - k) := by
      have h9 : (1 / 9 : ℝ) = (1 / 3 : ℝ) ^ 2 := by norm_num
      rw [h9, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      omega
    calc (1 / 3 : ℝ) ^ k * b ^ (t - k)
        ≤ (1 / 3 : ℝ) ^ k * (1 / 9 : ℝ) ^ (t - k) :=
          mul_le_mul_of_nonneg_left hbk (by positivity)
      _ = _ := hid
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum]
  have hrefl : ∑ k ∈ Finset.range (t + 1), (1 / 3 : ℝ) ^ (t - k) =
      ∑ k ∈ Finset.range (t + 1), (1 / 3 : ℝ) ^ k := by
    simpa using Finset.sum_range_reflect (fun k => (1 / 3 : ℝ) ^ k) (t + 1)
  rw [hrefl]
  have hgeom := Algsuperdiff.Section3.Provider.Stream.sum_range_geom_third_le (t + 1)
  have hpos : (0 : ℝ) ≤ (1 / 3 : ℝ) ^ t := by positivity
  calc (1 / 3 : ℝ) ^ t * ∑ k ∈ Finset.range (t + 1), (1 / 3 : ℝ) ^ k
      ≤ (1 / 3 : ℝ) ^ t * (3 / 2) := mul_le_mul_of_nonneg_left hgeom hpos
    _ = 3 / 2 * (1 / 3 : ℝ) ^ t := by ring

/-- The printed corridor weight sums to at most `3/2`. -/
private theorem sum_Icc_weight_le {L m : ℤ} (hLm : L ≤ m) :
    ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) ≤ 3 / 2 := by
  refine le_trans (le_of_eq ?_)
    (Algsuperdiff.Section3.Provider.Stream.sum_range_geom_third_le ((m - L).toNat + 1))
  refine Eq.trans ?_ (sum_Icc_reindex hLm (fun k : ℕ => (1 / 3 : ℝ) ^ k))
  refine Finset.sum_congr rfl fun n hn => ?_
  simp only [Finset.mem_Icc] at hn
  show (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) = (1 / 3 : ℝ) ^ ((m - n).toNat)
  exact rpow_three_neg_sub_eq_pow hn.2

/-- The printed corridor weight convolved with a decay of ratio at most `1/9`
along the corridor.  This is the corridor half of the `A.4` forcing decay. -/
private theorem sum_Icc_weight_mul_decay_le {L m : ℤ} (hLm : L ≤ m) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : b ≤ 1 / 9) :
    ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) * b ^ ((n - L).toNat) ≤
      3 / 2 * (1 / 3 : ℝ) ^ ((m - L).toNat) := by
  refine le_trans (le_of_eq ?_) (sum_range_geom_conv_le hb0 hb ((m - L).toNat))
  refine Eq.trans ?_
    (sum_Icc_reindex hLm (fun k : ℕ => (1 / 3 : ℝ) ^ k * b ^ ((m - L).toNat - k)))
  refine Finset.sum_congr rfl fun n hn => ?_
  simp only [Finset.mem_Icc] at hn
  have hexp : (n - L).toNat = (m - L).toNat - (m - n).toNat := by omega
  change (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) * b ^ ((n - L).toNat) =
    (1 / 3 : ℝ) ^ ((m - n).toNat) * b ^ ((m - L).toNat - (m - n).toNat)
  rw [rpow_three_neg_sub_eq_pow hn.2, hexp]

/-- **The `A.4` reindexing of the printed defect sum**, `t = n - L`.  The scale
`n = m` contributes nothing, so the printed corridor sum over `[L, m]` is the
lag sum over `1 ≤ k ≤ m - L` in which every predecessor `t - k` lies in
`[0, t]`. -/
private theorem sum_Icc_weight_defect_eq {L m : ℤ} (hLm : L ≤ m) (g : ℤ → ℝ) :
    ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) * (g n - g m) =
      ∑ k ∈ Finset.Icc 1 ((m - L).toNat), (1 / 3 : ℝ) ^ k *
        (g (L + (((m - L).toNat - k : ℕ) : ℤ)) - g m) := by
  have hre := Eq.trans (?_ : ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) * (g n - g m)
        = ∑ n ∈ Finset.Icc L m,
          (fun k : ℕ => (1 / 3 : ℝ) ^ k *
            (g (L + (((m - L).toNat - k : ℕ) : ℤ)) - g m)) ((m - n).toNat))
    (sum_Icc_reindex hLm
      (fun k : ℕ => (1 / 3 : ℝ) ^ k * (g (L + (((m - L).toNat - k : ℕ) : ℤ)) - g m)))
  · rw [hre]
    have hsplit : Finset.range ((m - L).toNat + 1) = insert 0 (Finset.Icc 1 ((m - L).toNat)) := by
      ext k
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    have hnot : (0 : ℕ) ∉ Finset.Icc 1 ((m - L).toNat) := by simp
    rw [hsplit, Finset.sum_insert hnot]
    have hzero : (1 / 3 : ℝ) ^ (0 : ℕ) *
        (g (L + (((m - L).toNat - 0 : ℕ) : ℤ)) - g m) = 0 := by
      have hLt : L + (((m - L).toNat - 0 : ℕ) : ℤ) = m := by omega
      rw [hLt]
      ring
    rw [hzero, zero_add]
  · refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_Icc] at hn
    have hidx : L + (((m - L).toNat - (m - n).toNat : ℕ) : ℤ) = n := by omega
    change (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) * (g n - g m) =
      (1 / 3 : ℝ) ^ ((m - n).toNat) *
        (g (L + (((m - L).toNat - (m - n).toNat : ℕ) : ℤ)) - g m)
    rw [rpow_three_neg_sub_eq_pow hn.2, hidx]

/-! ### The two-term amplitude absorption -/

/-- The elementary exponential bound `exp(-x) ≤ 4/x²` for `x > 0`. -/
private theorem exp_neg_le_four_div_sq {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ 4 / x ^ 2 := by
  have hhalf : x / 2 ≤ Real.exp (x / 2) := by
    have h := Real.add_one_le_exp (x / 2)
    linarith
  have hnn : (0 : ℝ) ≤ x / 2 := by linarith
  have hexp : Real.exp (x / 2) * Real.exp (x / 2) = Real.exp x := by
    rw [← Real.exp_add]; congr 1; ring
  have hmul : x / 2 * (x / 2) ≤ Real.exp (x / 2) * Real.exp (x / 2) :=
    mul_le_mul hhalf hhalf hnn (Real.exp_pos _).le
  rw [hexp] at hmul
  have key : x ^ 2 / 4 ≤ Real.exp x := by
    calc
      x ^ 2 / 4 = x / 2 * (x / 2) := by ring
      _ ≤ Real.exp x := hmul
  have hx2 : (0 : ℝ) < x ^ 2 := by positivity
  have hinv : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]; simp
  rw [le_div_iff₀ hx2]
  have key' : x ^ 2 ≤ 4 * Real.exp x := by linarith only [key]
  calc
    Real.exp (-x) * x ^ 2 ≤ Real.exp (-x) * (4 * Real.exp x) :=
      mul_le_mul_of_nonneg_left key' (Real.exp_pos _).le
    _ = 4 * (Real.exp (-x) * Real.exp x) := by ring
    _ = 4 := by rw [hinv, mul_one]

/-- **The lane's two-term amplitude is below the printed one.**  Under the
proposition's own induction regime `gamma ≤ E^{-10}` with `1 ≤ E`, the
amplitude `delta = E² gamma + exp(-2 E^{-3} gamma^{-1})` carried by the proved
corridor variance bound satisfies `delta ≤ 2 E² gamma ≤ 10^9 E² gamma =
delta_1`.  The disclosed absorption constant is `2 * 10^{-9}`. -/
private theorem twoTermAmplitude_le_amplitude {E gamma : ℝ} (hE : 1 ≤ E) (hgamma : 0 < gamma)
    (hregime : gamma ≤ (E⁻¹) ^ 10) :
    E ^ 2 * gamma + Real.exp (-(2 * (E⁻¹) ^ 3 * gamma⁻¹)) ≤ 10 ^ 9 * E ^ 2 * gamma := by
  have hEpos : (0 : ℝ) < E := lt_of_lt_of_le zero_lt_one hE
  have hEne : (E : ℝ) ≠ 0 := ne_of_gt hEpos
  have hgne : gamma ≠ 0 := ne_of_gt hgamma
  have hxpos : (0 : ℝ) < 2 * (E⁻¹) ^ 3 * gamma⁻¹ := by positivity
  have hexp := exp_neg_le_four_div_sq hxpos
  have hE6 : (1 : ℝ) ≤ E ^ 6 := by simpa using pow_le_pow_left₀ zero_le_one hE 6
  have hE4 : E ^ 4 * gamma ≤ 1 := by
    have h1 : E ^ 4 * gamma ≤ E ^ 4 * (E⁻¹) ^ 10 :=
      mul_le_mul_of_nonneg_left hregime (by positivity)
    have h2 : E ^ 4 * (E⁻¹) ^ 10 = (E ^ 6)⁻¹ := by field_simp
    have hupos : (0 : ℝ) < (E ^ 6)⁻¹ := by positivity
    have hid : E ^ 6 * (E ^ 6)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    have h3 : (E ^ 6)⁻¹ ≤ 1 := by
      nlinarith only [mul_nonneg (by linarith only [hE6] : (0 : ℝ) ≤ E ^ 6 - 1)
        hupos.le, hid]
    linarith only [h1, h2, h3]
  have hPnn : (0 : ℝ) ≤ E ^ 2 * gamma * (2 * (E⁻¹) ^ 3 * gamma⁻¹) ^ 2 := by positivity
  have hid : E ^ 2 * gamma * (2 * (E⁻¹) ^ 3 * gamma⁻¹) ^ 2 * (E ^ 4 * gamma) = 4 := by
    field_simp
    ring
  have hkey : 4 / (2 * (E⁻¹) ^ 3 * gamma⁻¹) ^ 2 ≤ E ^ 2 * gamma := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 * (E⁻¹) ^ 3 * gamma⁻¹) ^ 2)]
    nlinarith only [mul_nonneg hPnn
      (by linarith only [hE4] : (0 : ℝ) ≤ 1 - E ^ 4 * gamma), hid]
  have hEg : (0 : ℝ) < E ^ 2 * gamma := by positivity
  linarith only [hexp, hkey, hEg]

/-! ### The two assembly steps, as abstract real arithmetic -/

/-- **The corridor assembly of the `A.4` forcing.**  `W` is the printed corridor
weight sum, `T` its convolution with the corridor decay, `delta` the lane's
two-term amplitude and `d1` the printed `delta_1`.  This is where the two
corridor sums, the `2` of the proved corridor variance bound and the amplitude
absorption combine into the coefficient `3 Cvar`. -/
private theorem corridor_forcing_le {Cvar delta d1 P W T : ℝ}
    (hCvar : 0 ≤ Cvar) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ d1) (hP : 0 ≤ P)
    (hW : W ≤ 3 / 2) (hT : T ≤ 3 / 2 * P) :
    (2 * Cvar * delta * delta + 4 * d1 ^ 2) * W + 2 * Cvar * delta * T ≤
      3 * Cvar * d1 * (d1 + P) + 6 * d1 ^ 2 := by
  have hd1 : (0 : ℝ) ≤ d1 := le_trans hdelta0 hdelta
  have hdd : (0 : ℝ) ≤ 2 * Cvar * delta * delta :=
    mul_nonneg (mul_nonneg (by linarith) hdelta0) hdelta0
  have hc1 : (0 : ℝ) ≤ 2 * Cvar * delta * delta + 4 * d1 ^ 2 := by
    have := sq_nonneg d1
    linarith
  have hc2 : (0 : ℝ) ≤ 2 * Cvar * delta := mul_nonneg (by linarith) hdelta0
  have h1 : (2 * Cvar * delta * delta + 4 * d1 ^ 2) * W ≤
      (2 * Cvar * delta * delta + 4 * d1 ^ 2) * (3 / 2) := mul_le_mul_of_nonneg_left hW hc1
  have h2 : 2 * Cvar * delta * T ≤ 2 * Cvar * delta * (3 / 2 * P) :=
    mul_le_mul_of_nonneg_left hT hc2
  have hsq : delta * delta ≤ d1 * d1 := mul_le_mul hdelta hdelta hdelta0 hd1
  have h3 : (0 : ℝ) ≤ Cvar * (d1 * d1 - delta * delta) := mul_nonneg hCvar (by linarith)
  have h4 : (0 : ℝ) ≤ Cvar * ((d1 - delta) * P) :=
    mul_nonneg hCvar (mul_nonneg (by linarith) hP)
  calc
    (2 * Cvar * delta * delta + 4 * d1 ^ 2) * W + 2 * Cvar * delta * T
        ≤ (2 * Cvar * delta * delta + 4 * d1 ^ 2) * (3 / 2) +
            2 * Cvar * delta * (3 / 2 * P) := add_le_add h1 h2
    _ ≤ 3 * Cvar * d1 * (d1 + P) + 6 * d1 ^ 2 := by
      nlinarith only [hsq, h3, h4]

/-- **The final absorption of the three pure-square blocks** of the Step-1
display into the `A.4` forcing shape `A d1 (d1 + P)`, using `d1 P ≥ 0`. -/
private theorem square_blocks_absorb {C1 Cbad Cvar d1 P Jm D A1 A2 : ℝ}
    (hC1 : 0 ≤ C1) (hCbad : 0 ≤ Cbad) (hd1 : 0 ≤ d1) (hP : 0 ≤ P)
    (hdisp : Jm ≤ C1 * D + C1 * A1 + C1 * A2 + C1 * d1 ^ 2 + Cbad * d1 ^ 2)
    (hkey : A1 + A2 ≤ 3 * Cvar * d1 * (d1 + P) + 6 * d1 ^ 2) :
    Jm ≤ (3 * C1 * Cvar + 7 * C1 + Cbad) * d1 * (d1 + P) + C1 * D := by
  have h1 : C1 * (A1 + A2) ≤ C1 * (3 * Cvar * d1 * (d1 + P) + 6 * d1 ^ 2) :=
    mul_le_mul_of_nonneg_left hkey hC1
  have h2 : (0 : ℝ) ≤ (7 * C1 + Cbad) * (d1 * P) :=
    mul_nonneg (by linarith) (mul_nonneg hd1 hP)
  nlinarith only [hdisp, h1, h2]

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ### `(e.J.bound.by.indyhyp)` at integer scales -/

private theorem cutoffResponse_integral_recurrence :
    ∀ (d : ℕ) [NeZero d] (Cvar : ℝ),
      (1 : ℝ) ≤ Cvar →
        ∀ (M : ABKModel d) (m : ℤ) (E : { E : ℝ // (1 : ℝ) ≤ E }) (L : ℤ),
          (∀ n ∈ Finset.Icc L m,
              (↑(Annealed.sigmaBar M L) : ℝ) ^ (2 : ℕ) *
                  (annealedSigmaStarInvScalarAtScale M L m - annealedSigmaStarInvScalarAtScale M L n) ^ (2 : ℕ) ≤
                (4 : ℝ) * ((10 : ℝ) ^ (9 : ℕ) * (↑E : ℝ) ^ (2 : ℕ) * M.gamma) ^ (2 : ℕ)) →
            (∀ n ∈ Finset.Icc L m,
                (↑(Annealed.sigmaBar M L) : ℝ) ^ (2 : ℕ) * starInverseVarianceAtScale M L n +
                    starInverseKappaVarianceAtScale M L n ≤
                  (2 : ℝ) * Cvar *
                      ((↑E : ℝ) ^ (2 : ℕ) * M.gamma + Real.exp (-((2 : ℝ) * (↑E : ℝ)⁻¹ ^ (3 : ℕ) * M.gamma⁻¹))) *
                    ((↑E : ℝ) ^ (2 : ℕ) * M.gamma + Real.exp (-((2 : ℝ) * (↑E : ℝ)⁻¹ ^ (3 : ℕ) * M.gamma⁻¹)) +
                      ((3 : ℝ) ^ (-(↑d : ℝ))) ^ (n - L).toNat)) →
              ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-(↑(m - n) : ℝ)) ≤ (3 / 2 : ℝ) →
                ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-(↑(m - n) : ℝ)) * ((3 : ℝ) ^ (-(↑d : ℝ))) ^ (n - L).toNat ≤
                    (3 / 2 : ℝ) * (1 / 3 : ℝ) ^ (m - L).toNat →
                  (0 : ℝ) ≤ (1 / 3 : ℝ) ^ (m - L).toNat →
                    (0 : ℝ) ≤ (↑E : ℝ) ^ (2 : ℕ) * M.gamma + Real.exp (-((2 : ℝ) * (↑E : ℝ)⁻¹ ^ (3 : ℕ) * M.gamma⁻¹)) →
                      (↑E : ℝ) ^ (2 : ℕ) * M.gamma + Real.exp (-((2 : ℝ) * (↑E : ℝ)⁻¹ ^ (3 : ℕ) * M.gamma⁻¹)) ≤
                          (10 : ℝ) ^ (9 : ℕ) * (↑E : ℝ) ^ (2 : ℕ) * M.gamma →
                        (↑(Annealed.sigmaBar M L) : ℝ) ^ (2 : ℕ) *
                              ∑ n ∈ Finset.Icc L m,
                                (3 : ℝ) ^ (-(↑(m - n) : ℝ)) *
                                  (starInverseVarianceAtScale M L n +
                                    (annealedSigmaStarInvScalarAtScale M L m - annealedSigmaStarInvScalarAtScale M L n) ^
                                      (2 : ℕ)) +
                            ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-(↑(m - n) : ℝ)) * starInverseKappaVarianceAtScale M L n ≤
                          (3 : ℝ) * Cvar * ((10 : ℝ) ^ (9 : ℕ) * (↑E : ℝ) ^ (2 : ℕ) * M.gamma) *
                              ((10 : ℝ) ^ (9 : ℕ) * (↑E : ℝ) ^ (2 : ℕ) * M.gamma + (1 / 3 : ℝ) ^ (m - L).toNat) +
                            (6 : ℝ) * ((10 : ℝ) ^ (9 : ℕ) * (↑E : ℝ) ^ (2 : ℕ) * M.gamma) ^ (2 : ℕ) := by
  intro d _ Cvar _ M m E L hgapn hvarn hWsum hConv hpowNn hdeltaNn hdeltaLe
  have hexpand : (Annealed.sigmaBar M L : ℝ) ^ 2 *
        (∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
          (starInverseVarianceAtScale M L n +
            (annealedSigmaStarInvScalarAtScale M L m -
              annealedSigmaStarInvScalarAtScale M L n) ^ 2)) +
      (∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
        starInverseKappaVarianceAtScale M L n) =
      ∑ n ∈ Finset.Icc L m,
        ((3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
            ((Annealed.sigmaBar M L : ℝ) ^ 2 * starInverseVarianceAtScale M L n +
              starInverseKappaVarianceAtScale M L n) +
          (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
            ((Annealed.sigmaBar M L : ℝ) ^ 2 *
              (annealedSigmaStarInvScalarAtScale M L m -
                annealedSigmaStarInvScalarAtScale M L n) ^ 2)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hexpand]
  have hterm : ∀ n ∈ Finset.Icc L m,
      (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
            ((Annealed.sigmaBar M L : ℝ) ^ 2 * starInverseVarianceAtScale M L n +
              starInverseKappaVarianceAtScale M L n) +
          (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
            ((Annealed.sigmaBar M L : ℝ) ^ 2 *
              (annealedSigmaStarInvScalarAtScale M L m -
                annealedSigmaStarInvScalarAtScale M L n) ^ 2) ≤
        (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
            (2 * Cvar *
              ((E : ℝ) ^ 2 * M.gamma + Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) *
              (((E : ℝ) ^ 2 * M.gamma +
                  Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) +
                ((3 : ℝ) ^ (-(d : ℝ))) ^ ((n - L).toNat))) +
          (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) * (4 * (10 ^ 9 * (E : ℝ) ^ 2 * M.gamma) ^ 2) := by
    intro n hn
    have hw : (0 : ℝ) ≤ (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    exact add_le_add (mul_le_mul_of_nonneg_left (hvarn n hn) hw)
      (mul_le_mul_of_nonneg_left (hgapn n hn) hw)
  refine (Finset.sum_le_sum hterm).trans ?_
  have hsplit : ∑ n ∈ Finset.Icc L m,
      ((3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
            (2 * Cvar *
              ((E : ℝ) ^ 2 * M.gamma + Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) *
              (((E : ℝ) ^ 2 * M.gamma +
                  Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) +
                ((3 : ℝ) ^ (-(d : ℝ))) ^ ((n - L).toNat))) +
          (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) * (4 * (10 ^ 9 * (E : ℝ) ^ 2 * M.gamma) ^ 2)) =
      (2 * Cvar *
            ((E : ℝ) ^ 2 * M.gamma + Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) *
            ((E : ℝ) ^ 2 * M.gamma + Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) +
          4 * (10 ^ 9 * (E : ℝ) ^ 2 * M.gamma) ^ 2) *
            (∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ))) +
        (2 * Cvar *
            ((E : ℝ) ^ 2 * M.gamma + Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))) *
          (∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
            ((3 : ℝ) ^ (-(d : ℝ))) ^ ((n - L).toNat)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hsplit]
  exact corridor_forcing_le (by linarith) hdeltaNn hdeltaLe hpowNn hWsum hConv

/-- At `delta_1 := 10^9 E^2 gamma` the delivered display is

`E[J(cu_m, sigmabar_L^{-1/2} e, sigmabar_L^{1/2} e; a_L)]`
`  <= A delta_1 (delta_1 + 3^{-(m-L)})`
`     + C sum_{n=L}^m 3^{-(m-n)} (E[J(cu_n)] - E[J(cu_m)])`,

i.e. the printed display with its bi-infinite defect sum replaced by the finite
corridor of `e.initial.JL.bound`.  `A` and `C` are selected before the model,
the cutoff and the direction.  Every constant is disclosed in the module
docstring; there is no conditional A input, the amplitude bridge being imported
and consumed rather than assumed.

This is a local Provider theorem and makes no source-node status claim. -/
theorem exists_integral_cutoffResponseJ_le_finiteCorridorIndyhypDisplay (d : ℕ) [NeZero d] :
    ∃ Chom A C : ℝ, (10 : ℝ) ^ 9 ≤ Chom ∧ 64 ≤ Chom ∧ 0 ≤ A ∧ 1 ≤ C ∧
      ∀ (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E}),
        15 * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        (∀ k : ℤ, k ≤ m - 1 →
          ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
            Probability.IsTwoTermBigOWith
              (Cutoff.cutoffSampleLaw M).toMeasure
              (IndependentSums.gammaSigma 2) (IndependentSums.gammaSigma (1 / 2))
              (Observable.cutoffHomogenizationError M k
                ⟨s,
                  (mul_pos (by norm_num : (0 : ℝ) < 8)
                    M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
              ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
              ((s⁻¹) ^ 2 *
                Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))) →
        ∀ epsilon : ℝ, epsilon ∈ Set.Ioc 0 (1 / 2) →
          M.gamma ≤ Chom⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon →
          ∀ L : ℤ, L ≤ m - 2 →
            (L : ℝ) ≤ (m : ℝ) - Chom * |Real.log epsilon| →
            C * (3 : ℝ) ^ (-(3 / 4 : ℝ) * ((m - L : ℤ) : ℝ)) ≤ 1 / 4 →
            ∀ e : Vec d, Ch02.vecNorm e = 1 →
              ∫ omega, Observable.cutoffResponseJ M m L e omega
                  ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
                A * (10 ^ 9 * (E : ℝ) ^ 2 * M.gamma) *
                    ((10 ^ 9 * (E : ℝ) ^ 2 * M.gamma) +
                      (3 : ℝ) ^ (-((m - L : ℤ) : ℝ))) +
                  C * ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
                    ((∫ omega, Observable.cutoffResponseJ M n L e omega
                        ∂(Cutoff.cutoffSampleLaw M).toMeasure) -
                      ∫ omega, Observable.cutoffResponseJ M m L e omega
                        ∂(Cutoff.cutoffSampleLaw M).toMeasure) := by
  obtain ⟨Chom1, C1, Cbad, hChom1, hC1, hCbad, hdisplay⟩ :=
    exists_integral_cutoffResponseJ_le_initialJLBoundDisplay d
  obtain ⟨Chom2, Cvar, hChom2, _hChom2shift, hCvar, hvarbound⟩ :=
    exists_coefficientCutoff_finiteCorridor_starInverseVariance_withS_bound' (d := d)
  have hCh1le : Chom1 ≤ max (max Chom1 Chom2) ((10 : ℝ) ^ 9) :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hCh2le : Chom2 ≤ max (max Chom1 Chom2) ((10 : ℝ) ^ 9) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hChom1pos : (0 : ℝ) < Chom1 := by linarith
  have hChompos : (0 : ℝ) < max (max Chom1 Chom2) ((10 : ℝ) ^ 9) :=
    lt_of_lt_of_le hChom1pos hCh1le
  refine ⟨max (max Chom1 Chom2) ((10 : ℝ) ^ 9), 3 * C1 * Cvar + 7 * C1 + Cbad, C1,
    le_max_right _ _, le_trans hChom1 hCh1le, by positivity, hC1, ?_⟩
  intro M m E hEfloor hregime hLower epsilon hepsilon hgate L hsep hsepvar hgateC e he
  have hs : (0 : ℝ) < 1 / 4 := by norm_num
  obtain ⟨hdelta1mem, hmomentAll⟩ :=
    amplitude_mem_Ioc_and_lintegral_pow_four_le M (le_max_right _ _) hEfloor hregime hLower
      hepsilon hgate hs
  have hmoment := hmomentAll L (by omega)
  have hd2 : 2 ≤ d := M.shellPrefix.dimension
  have hLm : L ≤ m := by omega
  have hgammaPos : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hEone : (1 : ℝ) ≤ (E : ℝ) := E.property
  have hdelta1pos : (0 : ℝ) < 10 ^ 9 * (E : ℝ) ^ 2 * M.gamma := by
    have : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le zero_lt_one hEone
    positivity
  -- the composed smallness constant dominates both proved ones
  have hgate1 : M.gamma ≤ Chom1⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon := by
    have hinv : (max (max Chom1 Chom2) ((10 : ℝ) ^ 9))⁻¹ ≤ Chom1⁻¹ := by
      rw [inv_le_inv₀ hChompos hChom1pos]
      exact hCh1le
    have hpos : (0 : ℝ) ≤ ((E : ℝ)⁻¹) ^ 2 * epsilon := by
      have := hepsilon.1
      positivity
    have hstep : (max (max Chom1 Chom2) ((10 : ℝ) ^ 9))⁻¹ * (((E : ℝ)⁻¹) ^ 2 * epsilon) ≤
        Chom1⁻¹ * (((E : ℝ)⁻¹) ^ 2 * epsilon) := mul_le_mul_of_nonneg_right hinv hpos
    linarith [hgate, hstep]
  have hgate2 : M.gamma ≤ Chom2⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon := by
    have hChom2pos : (0 : ℝ) < Chom2 := by linarith
    have hinv : (max (max Chom1 Chom2) ((10 : ℝ) ^ 9))⁻¹ ≤ Chom2⁻¹ := by
      rw [inv_le_inv₀ hChompos hChom2pos]
      exact hCh2le
    have hpos : (0 : ℝ) ≤ ((E : ℝ)⁻¹) ^ 2 * epsilon := by
      have := hepsilon.1
      positivity
    have hstep : (max (max Chom1 Chom2) ((10 : ℝ) ^ 9))⁻¹ * (((E : ℝ)⁻¹) ^ 2 * epsilon) ≤
        Chom2⁻¹ * (((E : ℝ)⁻¹) ^ 2 * epsilon) := mul_le_mul_of_nonneg_right hinv hpos
    linarith [hgate, hstep]
  have hsep2 : (L : ℝ) ≤ (m : ℝ) - Chom2 * |Real.log epsilon| := by
    have hstep : Chom2 * |Real.log epsilon| ≤
        max (max Chom1 Chom2) ((10 : ℝ) ^ 9) * |Real.log epsilon| :=
      mul_le_mul_of_nonneg_right hCh2le (abs_nonneg _)
    linarith [hsepvar, hstep]
  -- the proved Step-1 display, at the bridge's amplitude
  have hdisp := hdisplay M m E hEfloor hregime hLower epsilon hepsilon hgate1 L hsep hgateC e he
    (1 / 4) hs (10 ^ 9 * (E : ℝ) ^ 2 * M.gamma) hdelta1mem hmoment
  -- the loading identities of `e.pq.normed`
  have hsigpos : (0 : ℝ) < (Annealed.sigmaBar M L : ℝ) := (Annealed.sigmaBar M L).property
  have hevs : vecNormSq e = 1 := by
    rw [← Ch02.vecNorm_sq_eq_vecNormSq, he]; norm_num
  have hpq : Observable.sqrtLoad (Annealed.sigmaBar M L) e =
      (Annealed.sigmaBar M L : ℝ) • Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e := by
    rw [Observable.sqrtLoad, Observable.inverseSqrtLoad, smul_smul]
    congr 1
    field_simp
    exact Real.sq_sqrt hsigpos.le
  have hqnorm : vecNormSq (Observable.sqrtLoad (Annealed.sigmaBar M L) e) =
      (Annealed.sigmaBar M L : ℝ) := by
    rw [Observable.sqrtLoad, vecNormSq_smul, Real.sq_sqrt hsigpos.le, hevs, mul_one]
  -- (I-2), first substitution: the Step-2 mean gap
  have hgapn : ∀ n ∈ Finset.Icc L m,
      (Annealed.sigmaBar M L : ℝ) ^ 2 *
          (annealedSigmaStarInvScalarAtScale M L m -
            annealedSigmaStarInvScalarAtScale M L n) ^ 2 ≤
        4 * (10 ^ 9 * (E : ℝ) ^ 2 * M.gamma) ^ 2 := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have hbase := coefficientCutoffLaw_sq_abs_annealedSigmaStarInvScalarAtScale_sub_le
      M hn.1 hn.2 hs hdelta1mem hmoment hpq hqnorm
    rw [sq_abs] at hbase
    have hcancel : (Annealed.sigmaBar M L : ℝ) ^ 2 *
        (4 * ((Annealed.sigmaBar M L : ℝ))⁻¹ ^ 2 * (10 ^ 9 * (E : ℝ) ^ 2 * M.gamma) ^ 2) =
          4 * (10 ^ 9 * (E : ℝ) ^ 2 * M.gamma) ^ 2 := by
      field_simp
    calc (Annealed.sigmaBar M L : ℝ) ^ 2 *
          (annealedSigmaStarInvScalarAtScale M L m -
            annealedSigmaStarInvScalarAtScale M L n) ^ 2
        ≤ (Annealed.sigmaBar M L : ℝ) ^ 2 *
            (4 * ((Annealed.sigmaBar M L : ℝ))⁻¹ ^ 2 *
              (10 ^ 9 * (E : ℝ) ^ 2 * M.gamma) ^ 2) :=
          mul_le_mul_of_nonneg_left hbase (sq_nonneg _)
      _ = _ := hcancel
  -- (I-2), second substitution: the corridor variance bound
  have hdecayEq : ∀ j : ℕ,
      Real.rpow 3 (-(d : ℝ) * ((j : ℕ) : ℝ)) = ((3 : ℝ) ^ (-(d : ℝ))) ^ j := by
    intro j
    have hrfl : Real.rpow 3 (-(d : ℝ) * ((j : ℕ) : ℝ)) =
        (3 : ℝ) ^ (-(d : ℝ) * ((j : ℕ) : ℝ)) := rfl
    rw [hrfl, ← Real.rpow_natCast ((3 : ℝ) ^ (-(d : ℝ))) j,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hvarn : ∀ n ∈ Finset.Icc L m,
      (Annealed.sigmaBar M L : ℝ) ^ 2 * starInverseVarianceAtScale M L n +
          starInverseKappaVarianceAtScale M L n ≤
        2 * Cvar *
          ((E : ℝ) ^ 2 * M.gamma + Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) *
          (((E : ℝ) ^ 2 * M.gamma + Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) +
            ((3 : ℝ) ^ (-(d : ℝ))) ^ ((n - L).toNat)) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have hb := hvarbound M m E hLower epsilon hepsilon hgate2 L hsep2 n
      (Set.mem_Icc.mpr ⟨hn.1, hn.2⟩)
    rwa [hdecayEq ((n - L).toNat)] at hb
  -- the two corridor sums
  have hb0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(d : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hb9 : (3 : ℝ) ^ (-(d : ℝ)) ≤ 1 / 9 := by
    have hdle : -(d : ℝ) ≤ -(2 : ℝ) := by
      have hcast : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
      linarith
    have hval : (3 : ℝ) ^ (-(2 : ℝ)) = 1 / 9 := by
      rw [show (-(2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      norm_num
    rw [← hval]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hdle
  have hWsum : ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) ≤ 3 / 2 :=
    sum_Icc_weight_le hLm
  have hConv : ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
      ((3 : ℝ) ^ (-(d : ℝ))) ^ ((n - L).toNat) ≤
      3 / 2 * (1 / 3 : ℝ) ^ ((m - L).toNat) := sum_Icc_weight_mul_decay_le hLm hb0 hb9
  have hpowNn : (0 : ℝ) ≤ (1 / 3 : ℝ) ^ ((m - L).toNat) := by positivity
  -- the amplitude absorption
  have hdeltaNn : (0 : ℝ) ≤
      (E : ℝ) ^ 2 * M.gamma + Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) := by
    have : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le zero_lt_one hEone
    positivity
  have hdeltaLe : (E : ℝ) ^ 2 * M.gamma + Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) ≤
      10 ^ 9 * (E : ℝ) ^ 2 * M.gamma :=
    twoTermAmplitude_le_amplitude hEone hgammaPos hregime
  -- the assembled corridor bound on the variance-and-gap part
  have hkey := @cutoffResponse_integral_recurrence (d) (by infer_instance) (Cvar) (hCvar) (M) (m)
    (E) (L) (hgapn) (hvarn) (hWsum) (hConv) (hpowNn) (hdeltaNn) (hdeltaLe)
  -- the final absorption of the three pure-square blocks into the `A.4` forcing
  have hforce : (3 : ℝ) ^ (-((m - L : ℤ) : ℝ)) = (1 / 3 : ℝ) ^ ((m - L).toNat) :=
    rpow_three_neg_sub_eq_pow hLm
  rw [hforce]
  exact square_blocks_absorb (by linarith) (by linarith) hdelta1pos.le hpowNn hdisp hkey

/-! ### `(e.J.bound.by.indyhyp)` in the `A.4` reindexing `t = n - L` -/

/-- With `F t := E[J(cu_{L+t}, sigmabar_L^{-1/2} e, sigmabar_L^{1/2} e; a_L)]` and
`delta_1 := 10^9 E^2 gamma`,

`F t <= A delta_1 (delta_1 + 3^{-t}) + C sum_{k=1}^{t} 3^{-k} (F (t-k) - F t)`

for every `t > j_0`, with `A`, `C` and the dimension-only separation `j_0`
selected before the model, the cutoff `L` and the unit direction `e`.  Every
predecessor `t - k` lies in `[0, t]`, so no scale below the infrared cutoff is
used: that is exactly what `A.4` prescribes.

This is the input shape of `exists_finiteCorridor_weightedDefect_decay` at
`r = 1/3`.  The engine's `hFnonneg` and `hcrude` binders are separate producers
and are not supplied here; so is the clause at every observation scale, which the
`hLower` binder below is taken at, and which bounds the reach of the delivered
recurrence by the induction state's top scale.  The module docstring adjudicates
both that horizon and the `epsilon`-dependent depth: the first is free by
zero-truncation, the second is absorbed by a consumer-side shift with the engine
applied at `j_0 = 0` --- and *not* by enlarging the engine's own `j_0`.

This is a local Provider theorem and makes no source-node status claim. -/
theorem exists_finiteRecurrence_integral_cutoffResponseJ (d : ℕ) [NeZero d] :
    ∃ (Chom A C : ℝ) (j₀ : ℕ), (10 : ℝ) ^ 9 ≤ Chom ∧ 64 ≤ Chom ∧ 0 ≤ A ∧ 0 ≤ C ∧
      ∀ (M : ABKModel d) (E : {E : ℝ // 1 ≤ E}),
        15 * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        ∀ epsilon : ℝ, epsilon ∈ Set.Ioc 0 (1 / 2) →
          M.gamma ≤ Chom⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon →
          ∀ (L : ℤ) (e : Vec d), Ch02.vecNorm e = 1 →
            ∀ t : ℕ, j₀ < t → Chom * |Real.log epsilon| ≤ (t : ℝ) →
              (∀ k : ℤ, k ≤ (L + (t : ℤ)) - 1 →
                ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
                  Probability.IsTwoTermBigOWith
                    (Cutoff.cutoffSampleLaw M).toMeasure
                    (IndependentSums.gammaSigma 2) (IndependentSums.gammaSigma (1 / 2))
                    (Observable.cutoffHomogenizationError M k
                      ⟨s,
                        (mul_pos (by norm_num : (0 : ℝ) < 8)
                          M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
                    ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
                    ((s⁻¹) ^ 2 *
                      Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))) →
                ∫ omega, Observable.cutoffResponseJ M (L + (t : ℤ)) L e omega
                    ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
                  A * (10 ^ 9 * (E : ℝ) ^ 2 * M.gamma) *
                      ((10 ^ 9 * (E : ℝ) ^ 2 * M.gamma) + (1 / 3 : ℝ) ^ t) +
                    C * ∑ k ∈ Finset.Icc 1 t, (1 / 3 : ℝ) ^ k *
                      ((∫ omega, Observable.cutoffResponseJ M (L + ((t - k : ℕ) : ℤ)) L e omega
                          ∂(Cutoff.cutoffSampleLaw M).toMeasure) -
                        ∫ omega, Observable.cutoffResponseJ M (L + (t : ℤ)) L e omega
                          ∂(Cutoff.cutoffSampleLaw M).toMeasure) := by
  obtain ⟨Chom, A, C, hChom10, hChom64, hA, hC, hmain⟩ :=
    exists_integral_cutoffResponseJ_le_finiteCorridorIndyhypDisplay d
  -- the dimension-only separation: it fixes the printed gate at `s = 1/4`
  have hrho0 : (0 : ℝ) < (3 : ℝ) ^ (-(3 / 4 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hrho1 : (3 : ℝ) ^ (-(3 / 4 : ℝ)) < 1 := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 3)
      (by norm_num : (-(3 / 4 : ℝ)) < 0)
    simpa using h
  have hCpos : (0 : ℝ) < C := by linarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (by positivity : (0 : ℝ) < 1 / (4 * C)) hrho1
  refine ⟨Chom, A, C, max 2 N, hChom10, hChom64, hA, hCpos.le, ?_⟩
  intro M E hEfloor hregime epsilon hepsilon hgate L e he t ht hsept hLower
  have ht2 : 2 < t := lt_of_le_of_lt (le_max_left 2 N) ht
  have htN : N ≤ t := le_of_lt (lt_of_le_of_lt (le_max_right 2 N) ht)
  -- the printed gate at the delivered constant
  have hgateC : C * (3 : ℝ) ^ (-(3 / 4 : ℝ) * (((L + (t : ℤ)) - L : ℤ) : ℝ)) ≤ 1 / 4 := by
    have hcast : (((L + (t : ℤ)) - L : ℤ) : ℝ) = ((t : ℕ) : ℝ) := by
      push_cast
      ring
    have hpow : (3 : ℝ) ^ (-(3 / 4 : ℝ) * ((t : ℕ) : ℝ)) = ((3 : ℝ) ^ (-(3 / 4 : ℝ))) ^ t := by
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(3 / 4 : ℝ))) t,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    have hmono : ((3 : ℝ) ^ (-(3 / 4 : ℝ))) ^ t ≤ ((3 : ℝ) ^ (-(3 / 4 : ℝ))) ^ N :=
      pow_le_pow_of_le_one hrho0.le hrho1.le htN
    have hlt : ((3 : ℝ) ^ (-(3 / 4 : ℝ))) ^ t < 1 / (4 * C) := lt_of_le_of_lt hmono hN
    rw [hcast, hpow]
    have hstep : C * ((3 : ℝ) ^ (-(3 / 4 : ℝ))) ^ t < C * (1 / (4 * C)) :=
      (mul_lt_mul_of_pos_left hlt hCpos)
    have hval : C * (1 / (4 * C)) = 1 / 4 := by field_simp
    linarith [hstep, hval]
  have hsep : L ≤ (L + (t : ℤ)) - 2 := by omega
  have hsepvar : (L : ℝ) ≤ ((L + (t : ℤ) : ℤ) : ℝ) - Chom * |Real.log epsilon| := by
    have hcast : ((L + (t : ℤ) : ℤ) : ℝ) = (L : ℝ) + ((t : ℕ) : ℝ) := by push_cast; ring
    rw [hcast]
    linarith [hsept]
  have hmainInst := hmain M (L + (t : ℤ)) E hEfloor hregime hLower epsilon hepsilon hgate L
    hsep hsepvar hgateC e he
  have hLm : L ≤ L + (t : ℤ) := by omega
  have htoNat : ((L + (t : ℤ)) - L).toNat = t := by omega
  have hforce : (3 : ℝ) ^ (-(((L + (t : ℤ)) - L : ℤ) : ℝ)) = (1 / 3 : ℝ) ^ t := by
    rw [rpow_three_neg_sub_eq_pow hLm, htoNat]
  have hdefect : ∑ n ∈ Finset.Icc L (L + (t : ℤ)),
      (3 : ℝ) ^ (-(((L + (t : ℤ)) - n : ℤ) : ℝ)) *
        ((∫ omega, Observable.cutoffResponseJ M n L e omega
            ∂(Cutoff.cutoffSampleLaw M).toMeasure) -
          ∫ omega, Observable.cutoffResponseJ M (L + (t : ℤ)) L e omega
            ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∑ k ∈ Finset.Icc 1 t, (1 / 3 : ℝ) ^ k *
        ((∫ omega, Observable.cutoffResponseJ M (L + ((t - k : ℕ) : ℤ)) L e omega
            ∂(Cutoff.cutoffSampleLaw M).toMeasure) -
          ∫ omega, Observable.cutoffResponseJ M (L + (t : ℤ)) L e omega
            ∂(Cutoff.cutoffSampleLaw M).toMeasure) := by
    have hgen := sum_Icc_weight_defect_eq hLm
      (fun n : ℤ => ∫ omega, Observable.cutoffResponseJ M n L e omega
        ∂(Cutoff.cutoffSampleLaw M).toMeasure)
    rw [htoNat] at hgen
    exact hgen
  rw [hforce, hdefect] at hmainInst
  exact hmainInst

end

end Algsuperdiff.Section3.Provider.Homogenization
