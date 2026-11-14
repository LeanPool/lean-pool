/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.DisplacementScale
public import Mathlib.Data.Int.Log

/-!
# ConfinementScale

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The widened scale and the confinement scale

The superdiffusive displacement bounds are stated at a random confinement scale
`m_t`, built from the displacement scales `S_k` of the tail bound in two steps.
First the scales are widened,

`S_n = sup_{k ≥ n} S_k 3^{-2(k-n)}`,

which is what makes the tail bound available at every scale above `n` and not
only at `n` itself.  Then the confinement scale is the smallest integer above
the logarithm of `K (1 + S_n) |log γ|^{1/2} R(t)`:

`m_t = inf {n ∈ ℤ : n ≥ ⌈log₃ (K (1 + S_n) |log γ|^{1/2} R(t))⌉}`.

Two points of the reading.  The widened scale is `ℝ≥0∞`-valued: the supremum is
over an infinite family and can be infinite, and the value `⊤` is the honest one
there — no truncation and no fallback.  The infimum is an infimum of a set of
integers, which the source takes without comment; it is attained as soon as the
set is nonempty, because the set is bounded below by `log₃` of the deterministic
factor, and that is the content of `exists_isConfinementScale`.  A scale at which
the widened scale is infinite is never in the set, so the definition needs no
side condition.

## Main definitions

* `widenedScale S n` — the widened scale `S_n`, in `ℝ≥0∞`.
* `confinementSet Stilde L` — the set the confinement scale is the infimum of.
* `IsConfinementScale Stilde L m` — `m` is that infimum, attained.

## References

* ABK26, the superdiffusive displacement bounds of Section 5.4.
-/

namespace Algsuperdiff.Section5.Support

open scoped ENNReal

noncomputable section

/-! ## 1. The widened scale -/

/-- **The widened scale** `S_n = sup_{k ≥ n} S_k 3^{-2(k-n)}`.  The supremum is
taken in `ℝ≥0∞`, where an unbounded family has the value `⊤`. -/
def widenedScale (S : ℤ → ℝ) (n : ℤ) : ℝ≥0∞ :=
  ⨆ k : {k : ℤ // n ≤ k}, ENNReal.ofReal (S k * (3 : ℝ) ^ (-2 * ((k : ℤ) - n)))

/-- The supremum over the scales `k ≥ n`, reindexed by `k = n + j` with `j : ℕ`.
This is the countable form used for measurability and for the moments. -/
theorem widenedScale_eq_iSup_nat (S : ℤ → ℝ) (n : ℤ) :
    widenedScale S n = ⨆ j : ℕ, ENNReal.ofReal (S (n + j) * (3 : ℝ) ^ (-2 * (j : ℤ))) := by
  refine le_antisymm (iSup_le fun k => ?_) (iSup_le fun j => ?_)
  · refine le_iSup_of_le ((k : ℤ) - n).toNat ?_
    have hk : (((((k : ℤ) - n).toNat : ℕ) : ℤ)) = (k : ℤ) - n := Int.toNat_of_nonneg (by omega)
    rw [hk]
    simp only [add_sub_cancel]
    exact le_rfl
  · exact le_iSup_of_le ⟨n + j, by omega⟩ (by simp)

/-! ## 2. The confinement scale -/

/-- **The set the confinement scale is the infimum of**: the scales `n` with
`L (1 + S_n) ≤ 3^n`, where `L` is the deterministic factor
`K |log γ|^{1/2} R(t)`. -/
def confinementSet (Stilde : ℤ → ℝ≥0∞) (L : ℝ) : Set ℤ :=
  {n : ℤ | ENNReal.ofReal L * (1 + Stilde n) ≤ ENNReal.ofReal ((3 : ℝ) ^ n)}

/-- **The set is bounded below**, by the integer logarithm of the deterministic
factor: the widened scale is nonnegative, so every admissible scale already
satisfies `L ≤ 3^n`. -/
theorem int_log_le_of_mem_confinementSet {Stilde : ℤ → ℝ≥0∞} {L : ℝ} (hL : 0 < L) {n : ℤ}
    (hn : n ∈ confinementSet Stilde L) : Int.log 3 L ≤ n := by
  have hpos : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hstep : ENNReal.ofReal L ≤ ENNReal.ofReal ((3 : ℝ) ^ n) := by
    refine le_trans ?_ hn
    calc ENNReal.ofReal L = ENNReal.ofReal L * 1 := (mul_one _).symm
      _ ≤ ENNReal.ofReal L * (1 + Stilde n) := by
          gcongr
          exact le_self_add
  have hreal : L ≤ (3 : ℝ) ^ n := (ENNReal.ofReal_le_ofReal_iff hpos.le).mp hstep
  have hlog : (3 : ℝ) ^ Int.log 3 L ≤ (3 : ℝ) ^ n := by
    refine le_trans ?_ hreal
    simpa using Int.zpow_log_le_self (b := 3) (r := L) (by norm_num) hL
  exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp hlog

/-- **The confinement scale**: the least admissible scale, that is, the attained
infimum of `confinementSet`. -/
def IsConfinementScale (Stilde : ℤ → ℝ≥0∞) (L : ℝ) (m : ℤ) : Prop :=
  IsLeast (confinementSet Stilde L) m

/-- **The infimum is attained.**  The set of admissible scales is bounded below
by `log₃ L`, so as soon as it is nonempty it has a least element. -/
theorem exists_isConfinementScale {Stilde : ℤ → ℝ≥0∞} {L : ℝ} (hL : 0 < L)
    (hne : (confinementSet Stilde L).Nonempty) :
    ∃ m : ℤ, IsConfinementScale Stilde L m := by
  obtain ⟨lb, hlb, hmin⟩ :=
    Int.exists_least_of_bdd (P := fun n => n ∈ confinementSet Stilde L)
      ⟨Int.log 3 L, fun z hz => int_log_le_of_mem_confinementSet hL hz⟩
      (by obtain ⟨n, hn⟩ := hne; exact ⟨n, hn⟩)
  exact ⟨lb, hlb, fun z hz => hmin z hz⟩

/-- There is only one confinement scale. -/
theorem isConfinementScale_unique {Stilde : ℤ → ℝ≥0∞} {L : ℝ} {m m' : ℤ}
    (hm : IsConfinementScale Stilde L m) (hm' : IsConfinementScale Stilde L m') : m = m' :=
  hm.unique hm'

/-- **The confinement scale is above the intrinsic scale.**  Any real below the
deterministic factor — in the source, `R(t)`, which is `L` divided by
`K |log γ|^{1/2} ≥ 1` — is below `3^{m_t}`. -/
theorem le_three_zpow_of_isConfinementScale' {Stilde : ℤ → ℝ≥0∞} {L Rt : ℝ} {m : ℤ}
    (hRt : Rt ≤ L) (hm : IsConfinementScale Stilde L m) :
    Rt ≤ (3 : ℝ) ^ m := by
  have hpos : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hstep : ENNReal.ofReal L ≤ ENNReal.ofReal ((3 : ℝ) ^ m) := by
    refine le_trans ?_ hm.1
    calc ENNReal.ofReal L = ENNReal.ofReal L * 1 := (mul_one _).symm
      _ ≤ ENNReal.ofReal L * (1 + Stilde m) := by
          gcongr
          exact le_self_add
  exact hRt.trans ((ENNReal.ofReal_le_ofReal_iff hpos.le).mp hstep)

end

end Algsuperdiff.Section5.Support
