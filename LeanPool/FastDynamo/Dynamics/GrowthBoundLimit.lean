/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.GrowthBound
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# The growth bound of a `C₀`-semigroup is a limit

The paper defines the maximal growth rate of the induction equation as a *limit*,

```
  γ(u, ε) := lim_{t → ∞} t⁻¹ · log ‖e^{t L_{ε,u}}‖_{L²_σ → L²_σ}
```

(`eq:semigroup-growth-rate`), which exists "because the logarithm of the semigroup norm is
subadditive and every `C₀`-semigroup is locally bounded in time" (the sentence after
`eq:semigroup-growth-rate`, citing Engel–Nagel Proposition IV.2.2).
`FastDynamo.StronglyContinuousSemigroup.growthBound` is the `EReal`-valued `limsup` of the
same function.  This module proves, for every `C₀`-semigroup on a complex Banach space, that the
`limsup` is a limit and equals the infimum over positive times:

```
  t⁻¹ log ‖S t‖ → growthBound S = inf_{t > 0} t⁻¹ log ‖S t‖   (t → ∞, in [−∞, ∞)).
```

The function is `growthExponent`, the integrand of `growthBound`: it takes the value `⊥` at
the times where `S t = 0` (where `log 0 = −∞` mathematically) and `t⁻¹ log ‖S t‖` elsewhere.
The limit is `⊥` exactly when there is no exponential minorant `e^{ω t} ≤ ‖S t‖`, which covers
the nilpotent semigroups but also semigroups whose norm decays faster than every exponential
without vanishing.

## The argument

It is Engel–Nagel's.  Fix `s > 0` and put `n = ⌊t / s⌋`.  The semigroup law and
`ContinuousLinearMap.opNorm_comp_le` give `‖S t‖ ≤ ‖S (t - n s)‖ ‖S s‖ⁿ ≤ K ‖S s‖ⁿ`, where
`K` bounds `‖S r‖` on `0 ≤ r ≤ s` (`exists_norm_operator_le`, from strong continuity on the
compact interval and Banach–Steinhaus, which is where completeness of `X` enters).  Taking
logarithms, `t⁻¹ log ‖S t‖ ≤ t⁻¹ log K + (n / t) log ‖S s‖`, whose right side tends to
`s⁻¹ log ‖S s‖`; if `S s = 0` then `S t = 0` for `t ≥ s`.  Hence the `limsup` is at most every
value `s⁻¹ log ‖S s‖`, so at most their infimum, which is trivially at most the `liminf`.

## Contents

* `growthExponent`, the integrand of `growthBound`.
* `growthBound_eq_iInf` and `tendsto_growthExponent`: the general theorem.
* `growthBound_ne_bot_iff`: the limit is finite exactly when there is an exponential minorant.
* `exists_growthBound_eq_and_tendsto`: where the limit is finite, the real-valued form of the
  paper's definition.

The application to the paper's `γ(u, ε)` is
`FastDynamo/Dynamics/Assembly/MainGrowthRateLimit.lean`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter Topology

universe u

namespace StronglyContinuousSemigroup

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]

/--
The finite-time growth exponent `t ↦ t⁻¹ log ‖S t‖` in `EReal`, with the value `⊥` at the times
where the operator norm vanishes: exactly the function whose `limsup` along `atTop` is
`FastDynamo.StronglyContinuousSemigroup.growthBound` (by definition), and whose limit
is the paper's growth rate (`eq:semigroup-growth-rate`).  Nonnegative time is parametrised by
`Real.toNNReal`, as in `growthBound`.
-/
def growthExponent (S : StronglyContinuousSemigroup X) (t : ℝ) : EReal :=
  if ‖S.operator (Real.toNNReal t)‖ = 0 then ⊥
  else ((t⁻¹ * Real.log ‖S.operator (Real.toNNReal t)‖ : ℝ) : EReal)

/-- The growth exponent never takes the value `⊤`. -/
theorem growthExponent_ne_top (S : StronglyContinuousSemigroup X) (t : ℝ) :
    S.growthExponent t ≠ ⊤ := by
  unfold growthExponent
  split_ifs
  · exact bot_ne_top
  · exact EReal.coe_ne_top _

/-- **Submultiplicativity along multiples**: `‖S (n s)‖ ≤ ‖S s‖ⁿ`, by the semigroup law and
`ContinuousLinearMap.opNorm_comp_le`; the case `n = 0` is `‖id‖ ≤ 1`. -/
theorem norm_operator_nsmul_le (S : StronglyContinuousSemigroup X) (s : NNReal) :
    ∀ n : ℕ, ‖S.operator (n • s)‖ ≤ ‖S.operator s‖ ^ n
  | 0 => by
    rw [zero_smul, pow_zero, S.operator_zero']
    exact ContinuousLinearMap.norm_id_le
  | n + 1 => by
    rw [succ_nsmul, S.operator_add', pow_succ]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (S.norm_operator_nsmul_le s n) (norm_nonneg _))

/-- **Local boundedness.**  On a Banach space the operator norm of a `C₀`-semigroup is bounded
on every compact time interval `[0, T]`: each orbit is continuous, hence bounded, on the compact
interval, and Banach–Steinhaus turns the pointwise bounds into a bound on the norms. -/
theorem exists_norm_operator_le [CompleteSpace X] (S : StronglyContinuousSemigroup X)
    (T : NNReal) : ∃ K : ℝ, 0 < K ∧ ∀ r : NNReal, r ≤ T → ‖S.operator r‖ ≤ K := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun r : Set.Icc (0 : NNReal) T ↦ S.operator r)
    fun x ↦ by
      obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : NNReal)) (b := T)).exists_bound_of_continuousOn
        (S.strong_continuous' x).continuousOn
      exact ⟨C, fun r ↦ hC r r.2⟩
  exact ⟨max C 1, lt_max_of_lt_right one_pos,
    fun r hr ↦ (hC ⟨r, zero_le, hr⟩).trans (le_max_left _ _)⟩

/-- **The `limsup` is at most every finite-time exponent.**  For every `s > 0`,
`limsup_{t → ∞} t⁻¹ log ‖S t‖ ≤ s⁻¹ log ‖S s‖`: this is the continuous-parameter Fekete
argument, with `t = ⌊t / s⌋ s + r`, `0 ≤ r < s`, and the local bound on `‖S r‖`. -/
theorem limsup_growthExponent_le [CompleteSpace X] (S : StronglyContinuousSemigroup X)
    {s : ℝ} (hs : 0 < s) : limsup S.growthExponent atTop ≤ S.growthExponent s := by
  obtain ⟨K, hK, hKb⟩ := S.exists_norm_operator_le (Real.toNNReal s)
  have hbound : ∀ t : ℝ, 0 ≤ t → ‖S.operator (Real.toNNReal t)‖ ≤
      K * ‖S.operator (Real.toNNReal s)‖ ^ ⌊t / s⌋₊ := by
    intro t ht
    have hns : (⌊t / s⌋₊ : ℝ) * s ≤ t := by
      have h := Nat.floor_le (div_nonneg ht hs.le)
      rwa [le_div_iff₀ hs] at h
    have hlt : t < (⌊t / s⌋₊ : ℝ) * s + s := by
      have h := Nat.lt_floor_add_one (t / s)
      rw [div_lt_iff₀ hs] at h
      linarith
    have hsplit : Real.toNNReal t =
        Real.toNNReal (t - ⌊t / s⌋₊ * s) + ⌊t / s⌋₊ • Real.toNNReal s := by
      apply NNReal.coe_injective
      rw [NNReal.coe_add, NNReal.coe_nsmul, Real.coe_toNNReal _ ht,
        Real.coe_toNNReal _ (by linarith), Real.coe_toNNReal _ hs.le, nsmul_eq_mul]
      ring
    rw [hsplit, S.operator_add']
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul ?_
      (S.norm_operator_nsmul_le _ _) (norm_nonneg _) hK.le)
    exact hKb _ (Real.toNNReal_le_toNNReal (by linarith))
  by_cases hs0 : ‖S.operator (Real.toNNReal s)‖ = 0
  · refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [eventually_ge_atTop s] with t ht
    have hn : ⌊t / s⌋₊ ≠ 0 := Nat.one_le_iff_ne_zero.1
      (Nat.le_floor (by rw [Nat.cast_one, one_le_div hs]; exact ht))
    have ht0 : ‖S.operator (Real.toNNReal t)‖ = 0 := by
      refine le_antisymm ?_ (norm_nonneg _)
      simpa [hs0, zero_pow hn] using hbound t (hs.le.trans ht)
    simp only [growthExponent, ite_eq_left ht0, ite_eq_left hs0, le_refl]
  · have hc : 0 < ‖S.operator (Real.toNNReal s)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hs0)
    set c := ‖S.operator (Real.toNNReal s)‖ with hc_def
    have hdiv : Tendsto (fun t : ℝ ↦ (⌊t / s⌋₊ : ℝ) / t) atTop (𝓝 s⁻¹) := by
      have h := (tendsto_nat_floor_div_atTop (R := ℝ)).comp
        (tendsto_id.atTop_div_const hs)
      have h' := h.mul_const s⁻¹
      rw [one_mul] at h'
      refine h'.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      simp only [Function.comp_apply, id]
      field_simp
    have hlim : Tendsto (fun t : ℝ ↦ t⁻¹ * (Real.log K + ⌊t / s⌋₊ * Real.log c)) atTop
        (𝓝 (s⁻¹ * Real.log c)) := by
      have h := (tendsto_inv_atTop_zero.mul_const (Real.log K)).add (hdiv.mul_const (Real.log c))
      rw [zero_mul, zero_add] at h
      refine h.congr fun t ↦ ?_
      ring
    have hmaj : ∀ᶠ t : ℝ in atTop, S.growthExponent t ≤
        ((t⁻¹ * (Real.log K + ⌊t / s⌋₊ * Real.log c) : ℝ) : EReal) := by
      filter_upwards [eventually_gt_atTop 0] with t ht
      unfold growthExponent
      split_ifs with ht0
      · exact bot_le
      rw [EReal.coe_le_coe_iff]
      refine mul_le_mul_of_nonneg_left ?_ (inv_pos.mpr ht).le
      have hlog := Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm ht0))
        (hbound t ht.le)
      rwa [Real.log_mul hK.ne' (pow_ne_zero _ hc.ne'), Real.log_pow] at hlog
    calc limsup S.growthExponent atTop
        ≤ limsup (fun t : ℝ ↦ ((t⁻¹ * (Real.log K + ⌊t / s⌋₊ * Real.log c) : ℝ) : EReal))
          atTop := limsup_le_limsup hmaj
      _ = ((s⁻¹ * Real.log c : ℝ) : EReal) := (EReal.tendsto_coe.2 hlim).limsup_eq
      _ = S.growthExponent s := by rw [growthExponent, ite_eq_right hs0]

/-- The infimum of the finite-time exponents over positive times lies between the `limsup` and
the `liminf` of the growth exponent: above the `limsup` by `limsup_growthExponent_le`, below
the `liminf` because every exponent at a positive time is at least the infimum. -/
theorem limsup_le_iInf_le_liminf [CompleteSpace X] (S : StronglyContinuousSemigroup X) :
    limsup S.growthExponent atTop ≤ ⨅ (t : ℝ) (_ : 0 < t), S.growthExponent t ∧
      ⨅ (t : ℝ) (_ : 0 < t), S.growthExponent t ≤ liminf S.growthExponent atTop :=
  ⟨le_iInf₂ fun _ ht ↦ S.limsup_growthExponent_le ht,
    le_liminf_of_le (by isBoundedDefault)
      ((eventually_gt_atTop 0).mono fun t ht ↦ iInf₂_le t ht)⟩

/--
**The growth bound is the infimum of the finite-time exponents** (Engel–Nagel Proposition
IV.2.2): for every `C₀`-semigroup on a complex Banach space,

```
  growthBound S = inf_{t > 0} t⁻¹ log ‖S t‖,
```

with `t⁻¹ log ‖S t‖` read as `⊥` where `S t = 0` (`growthExponent`).
-/
theorem growthBound_eq_iInf [CompleteSpace X] (S : StronglyContinuousSemigroup X) :
    S.growthBound = ⨅ (t : ℝ) (_ : 0 < t), S.growthExponent t :=
  le_antisymm (S.limsup_le_iInf_le_liminf).1
    ((S.limsup_le_iInf_le_liminf).2.trans liminf_le_limsup)

/--
**The limit defining the paper's growth rate exists, for every `C₀`-semigroup**
(`eq:semigroup-growth-rate` and the sentence after it; Engel–Nagel Proposition IV.2.2).  On a
complex Banach space the finite-time growth exponent `t ↦ t⁻¹ log ‖S t‖` converges in
`EReal = [−∞, ∞]` as `t → ∞`, and its limit is `growthBound S`, the `limsup` of the same
function; by `growthBound_eq_iInf` the limit is also `inf_{t > 0} t⁻¹ log ‖S t‖`.

The paper's sentence speaks of `log ‖e^{tL}‖`, which is `−∞` where the operator vanishes;
`growthExponent` takes the value `⊥` there, so the statement is the paper's one with the limit
read in `[−∞, ∞)` (it is never `⊤`, by `growthExponent_ne_top`).
-/
theorem tendsto_growthExponent [CompleteSpace X] (S : StronglyContinuousSemigroup X) :
    Tendsto S.growthExponent atTop (𝓝 S.growthBound) := by
  rw [S.growthBound_eq_iInf]
  exact tendsto_of_le_liminf_of_limsup_le (S.limsup_le_iInf_le_liminf).2
    (S.limsup_le_iInf_le_liminf).1

/-- The growth bound is never `⊤`: it is at most the finite-time exponent at time `1`. -/
theorem growthBound_ne_top [CompleteSpace X] (S : StronglyContinuousSemigroup X) :
    S.growthBound ≠ ⊤ :=
  ne_top_of_le_ne_top (S.growthExponent_ne_top 1)
    (S.growthBound_eq_iInf ▸ iInf₂_le 1 one_pos)

/--
**When the growth bound is finite.**  `growthBound S ≠ ⊥` exactly when `‖S t‖` has an
exponential minorant `e^{ω t} ≤ ‖S t‖` at all positive times.  In particular a finite growth
bound forces `S t ≠ 0` for every `t`; the converse fails (a `C₀`-semigroup can have norm
`e^{-t²/2}`, which never vanishes but has growth bound `−∞`).
-/
theorem growthBound_ne_bot_iff [CompleteSpace X] (S : StronglyContinuousSemigroup X) :
    S.growthBound ≠ ⊥ ↔
      ∃ ω : ℝ, ∀ t : NNReal, 0 < t → Real.exp (ω * t) ≤ ‖S.operator t‖ := by
  constructor
  · intro hbot
    refine ⟨S.growthBound.toReal, fun t ht ↦ ?_⟩
    have ht' : (0 : ℝ) < t := ht
    have hle : S.growthBound ≤ S.growthExponent t := S.growthBound_eq_iInf ▸ iInf₂_le _ ht'
    rw [EReal.coe_toReal S.growthBound_ne_top hbot |>.symm] at hle
    unfold growthExponent at hle
    rw [Real.toNNReal_coe] at hle
    split_ifs at hle with ht0
    · exact absurd (le_bot_iff.1 hle) (EReal.coe_ne_bot _)
    rw [EReal.coe_le_coe_iff, le_inv_mul_iff₀ ht'] at hle
    rw [mul_comm]
    exact (Real.le_log_iff_exp_le (lt_of_le_of_ne (norm_nonneg _) (Ne.symm ht0))).1 hle
  · rintro ⟨ω, hω⟩ hbot
    have h := S.le_growthBound_of_norm_ge (ω := ω) <| by
      filter_upwards [eventually_gt_atTop 0] with t ht
      have h := hω (Real.toNNReal t) (Real.toNNReal_pos.2 ht)
      rwa [Real.coe_toNNReal _ ht.le] at h
    rw [hbot, le_bot_iff] at h
    exact EReal.coe_ne_bot ω h

/--
**The real-valued form, where the limit is finite.**  If `growthBound S ≠ ⊥`, the operator
norm never vanishes at positive times and the real function `t ↦ t⁻¹ log ‖S t‖` converges to
the real number `L` with `growthBound S = L` — the paper's definition
(`eq:semigroup-growth-rate`) read verbatim in `ℝ`.
-/
theorem exists_growthBound_eq_and_tendsto [CompleteSpace X] (S : StronglyContinuousSemigroup X)
    (hbot : S.growthBound ≠ ⊥) :
    ∃ L : ℝ, S.growthBound = (L : EReal) ∧
      Tendsto (fun t : ℝ ↦ t⁻¹ * Real.log ‖S.operator (Real.toNNReal t)‖) atTop (𝓝 L) := by
  refine ⟨S.growthBound.toReal, (EReal.coe_toReal S.growthBound_ne_top hbot).symm, ?_⟩
  have h := S.tendsto_growthExponent
  rw [← EReal.coe_toReal S.growthBound_ne_top hbot] at h
  refine EReal.tendsto_coe.1 (h.congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hle : S.growthBound ≤ S.growthExponent t := S.growthBound_eq_iInf ▸ iInf₂_le t ht
  unfold growthExponent at hle ⊢
  split_ifs at hle ⊢ with ht0
  · exact absurd (le_bot_iff.1 hle) hbot
  · rfl

end StronglyContinuousSemigroup

end

end FastDynamo
