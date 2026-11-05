/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.AssemblyFeed
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.EventBudgets
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.DisplaySlots

/-!
# EventReading

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Reading the good events `𝒢₁` and `𝒢₂` back into real estimates

`Support.eventG1` and `Support.eventG2` (ABK26, `d.good.event.for.lambda`) are
stated in `[0,∞]`, with no convergence side condition.  Every consumer inside
the proof of `p.mathcalE.annular.decomp` needs the *real* readings: a finite
sum, a bound on it, and -- the point of working in `[0,∞]` in the first place
-- the **summability** that keeps Lean's junk value `0` out of the real
`tsum`s.

This module supplies exactly those readings, each with the event membership as
its only substantive hypothesis.

## Part A -- the `[0,∞]`-to-real transport

`summable_of_ofReal_tsum_ne_top` and `tsum_le_of_ofReal_tsum_le`: a nonnegative
real family whose `ENNReal.ofReal` sum is finite is summable, and its sum obeys the same
bound.  `ennreal_tsum_annFam_eq` identifies the `ℤ × ℤ` sum of the guarded
annular family `Resum.annFam` with the iterated subtype sum in which the events
are written, which is what turns a `𝒢₂` membership into the `hsumE` binder of
`ClauseOne.clauseOne_bound`.

## Part B -- the `𝒢₁` readings

* the **first** component gives `Summable` for the `k ≥ m` shell tail, the bound
  `Σ ≤ T`, and hence `gradTailSq M m ω ≤ T²` -- the `G₁ᵃ` bracket that A2b's
  frontier item (d) recorded as missing;
* the **second** component gives the summability and the bound `≤ T²` for the
  single shell sum at the *event's own* weight `3^{−(s/4)v}`, at the A5b-pinned
  family `DisplaySlots.shellBlockLatticeReal`.  The two consequences the
  assembly needs are the `hAsum` binder (at the display weight `3^{−(s/2)v}`,
  which is smaller) and the **partial-sum budget** `Σ_{v<q+2} A(m−v)² ≤
  3^{s/4} T² 3^{(s/4)q}` feeding `AssemblyFeed.summable_annFam_grad` and
  `AssemblyFeed.summable_annFam_l2`.

-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the `[0,infinity]`-to-real transport -/

/-- A nonnegative real family whose `ENNReal.ofReal` sum is finite is summable. -/
theorem summable_of_ofReal_tsum_ne_top {iota : Type*} {f : iota → ℝ}
    (hf0 : ∀ i, 0 ≤ f i) (hfin : (∑' i, ENNReal.ofReal (f i)) ≠ ⊤) :
    Summable f :=
  (ENNReal.summable_toReal hfin).congr fun i => ENNReal.toReal_ofReal (hf0 i)

/-- The real reading of an `[0,infinity]`-valued bound on a nonnegative real
family: the sum obeys the same bound (and is not the junk value). -/
theorem tsum_le_of_ofReal_tsum_le {iota : Type*} {f : iota → ℝ} {T : ℝ}
    (hf0 : ∀ i, 0 ≤ f i) (hT : 0 ≤ T)
    (hle : (∑' i, ENNReal.ofReal (f i)) ≤ ENNReal.ofReal T) :
    ∑' i, f i ≤ T := by
  have hsum : Summable f :=
    summable_of_ofReal_tsum_ne_top hf0 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle)
  rw [← ENNReal.ofReal_tsum_of_nonneg hf0 hsum] at hle
  exact (ENNReal.ofReal_le_ofReal_iff hT).mp hle

private theorem ennreal_tsum_if_le (b : ℤ) (g : ℤ → ℝ≥0∞) :
    (∑' n : ℤ, (if n ≤ b then g n else 0)) = ∑' n : {n : ℤ // n ≤ b}, g n.1 := by
  classical
  have hinj : Function.Injective (fun n : {n : ℤ // n ≤ b} => n.1) :=
    Subtype.val_injective
  have hsupp : Function.support (fun n : ℤ => if n ≤ b then g n else 0)
      ⊆ Set.range (fun n : {n : ℤ // n ≤ b} => n.1) := by
    intro n hn
    by_cases h : n ≤ b
    · exact ⟨⟨n, h⟩, rfl⟩
    · exact absurd (ite_eq_right h) hn
  have hbij := hinj.tsum_eq hsupp
  have hcong : (∑' n : {n : ℤ // n ≤ b}, (if n.1 ≤ b then g n.1 else 0))
      = ∑' n : {n : ℤ // n ≤ b}, g n.1 :=
    tsum_congr fun n => ite_eq_left n.2
  rw [← hbij, hcong]

/-- **The guarded annular family as the iterated subtype sum.**  The `ℤ × ℤ`
sum of `ENNReal.ofReal ∘ Resum.annFam` is the iterated `Σ_{j ≤ m} Σ_{n ≤ j−1}` in which
`𝒢₂` is written. -/
theorem ennreal_tsum_annFam_eq (m : ℤ) (h : ℤ → ℤ → ℝ) :
    (∑' p : ℤ × ℤ, ENNReal.ofReal (annFam m h p))
      = ∑' j : {j : ℤ // j ≤ m}, ∑' n : {n : ℤ // n ≤ j.1 - 1},
          ENNReal.ofReal (h j.1 n.1) := by
  classical
  rw [ENNReal.tsum_prod' (f := fun p : ℤ × ℤ => ENNReal.ofReal (annFam m h p))]
  have hinner : ∀ j : ℤ,
      (∑' n : ℤ, ENNReal.ofReal (annFam m h (j, n)))
        = if j ≤ m then (∑' n : {n : ℤ // n ≤ j - 1}, ENNReal.ofReal (h j n.1))
          else 0 := by
    intro j
    by_cases hj : j ≤ m
    · rw [ite_eq_left hj, ← ennreal_tsum_if_le (j - 1) (fun n => ENNReal.ofReal (h j n))]
      refine tsum_congr fun n => ?_
      rw [annFam_apply]
      by_cases hn : n ≤ j - 1
      · rw [ite_eq_left (⟨hj, hn⟩ : j ≤ m ∧ n ≤ j - 1), ite_eq_left hn]
      · rw [ite_eq_right (fun hc : j ≤ m ∧ n ≤ j - 1 => hn hc.2), ite_eq_right hn,
          ENNReal.ofReal_zero]
    · rw [ite_eq_right hj]
      have hz : ∀ n : ℤ, ENNReal.ofReal (annFam m h (j, n)) = 0 := by
        intro n
        rw [annFam_apply, ite_eq_right (fun hc : j ≤ m ∧ n ≤ j - 1 => hj hc.1),
          ENNReal.ofReal_zero]
      rw [tsum_congr hz, tsum_zero]
  rw [tsum_congr hinner]
  exact ennreal_tsum_if_le m
    (fun j => ∑' n : {n : ℤ // n ≤ j - 1}, ENNReal.ofReal (h j n.1))

/-- The `[0,infinity]` finiteness criterion for the guarded annular family. -/
theorem summable_annFam_of_ennreal_ne_top {m : ℤ} {h : ℤ → ℤ → ℝ}
    (hh0 : ∀ j n, 0 ≤ h j n)
    (hfin : (∑' j : {j : ℤ // j ≤ m}, ∑' n : {n : ℤ // n ≤ j.1 - 1},
      ENNReal.ofReal (h j.1 n.1)) ≠ ⊤) :
    Summable (annFam m h) := by
  refine summable_of_ofReal_tsum_ne_top (annFam_nonneg hh0) ?_
  rw [ennreal_tsum_annFam_eq]
  exact hfin

/-! ## Part B -- the two `𝒢₁` readings -/

/-- The `k >= m` shell-tail family of the `G_1^a` content. -/
def gradTailFam (M : ABKModel d) (m : ℤ) (omega : Cutoff.CutoffSample d)
    (k : {k : ℤ // m ≤ k}) : ℝ :=
  (3 : ℝ) ^ ((2 - M.gamma) * (m : ℝ)) * Support.shellW1InfGradNorm m (omega.1 k.1)

private theorem gradTailFam_nonneg (M : ABKModel d) (m : ℤ)
    (omega : Cutoff.CutoffSample d) (k : {k : ℤ // m ≤ k}) :
    0 ≤ gradTailFam M m omega k :=
  mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (Support.shellW1InfGradNorm_nonneg m (omega.1 k.1))

/-- **The `𝒢₁ᵃ` reading, summability half.**  On `𝒢₁` the `k ≥ m` shell tail is
a genuine convergent series, so the real `tsum` inside `gradTailSq` is not the
junk value. -/
theorem summable_gradTail_of_eventG1 (M : ABKModel d) (m : ℤ) {s T : ℝ}
    {omega : Cutoff.CutoffSample d} (homega : omega ∈ Support.eventG1 M m s T) :
    Summable (fun k : {k : ℤ // m ≤ k} =>
      (3 : ℝ) ^ ((2 - M.gamma) * (m : ℝ))
        * Support.shellW1InfGradNorm m (omega.1 k.1)) :=
  summable_of_ofReal_tsum_ne_top (gradTailFam_nonneg M m omega)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top homega.1)

/-- **The `𝒢₁ᵃ` reading, value half.** -/
theorem tsum_gradTail_le_of_eventG1 (M : ABKModel d) (m : ℤ) {s T : ℝ} (hT : 0 ≤ T)
    {omega : Cutoff.CutoffSample d} (homega : omega ∈ Support.eventG1 M m s T) :
    (∑' k : {k : ℤ // m ≤ k},
        (3 : ℝ) ^ ((2 - M.gamma) * (m : ℝ))
          * Support.shellW1InfGradNorm m (omega.1 k.1)) ≤ T :=
  tsum_le_of_ofReal_tsum_le (gradTailFam_nonneg M m omega) hT homega.1

/-! ### The `𝒢₁ᵇ` reading at the pinned shell family -/

private theorem quarter_weight_eq (m : ℤ) (s : ℝ) (v : ℕ) :
    (3 : ℝ) ^ (-(1 / 4 : ℝ) * s * ((m - (m - (v : ℤ)) : ℤ) : ℝ))
      = (3 : ℝ) ^ (-(s / 4) * (v : ℝ)) := by
  congr 1
  push_cast
  ring

private theorem shellQuarterFam_nonneg (M : ABKModel d) (m : ℤ) (s : ℝ)
    (omega : Cutoff.CutoffSample d) (v : ℕ) :
    0 ≤ (3 : ℝ) ^ (-(s / 4) * (v : ℝ)) * shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2 :=
  mul_nonneg (Real.rpow_nonneg (by norm_num) _) (sq_nonneg _)

/-- The single shell sum at the event's own weight is dominated, term by term
and slot by slot, by the second component of `𝒢₁`. -/
private theorem ofReal_shellQuarter_tsum_le (M : ABKModel d) (m : ℤ) (s : ℝ)
    (omega : Cutoff.CutoffSample d) :
    (∑' v : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(s / 4) * (v : ℝ))
        * shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2))
      ≤ ∑' n : {n : ℤ // n ≤ m},
          ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 4 : ℝ) * s * ((m - n.1 : ℤ) : ℝ)))
            * ∑ k ∈ Finset.Icc (n.1 - 1) m, shellBlockLatticeAtom M m omega k ^ 2 := by
  classical
  have hinj : Function.Injective
      (fun v : ℕ => (⟨m - (v : ℤ), by omega⟩ : {n : ℤ // n ≤ m})) := by
    intro v w hvw
    have hval : m - (v : ℤ) = m - (w : ℤ) := congrArg Subtype.val hvw
    omega
  have hterm : ∀ v : ℕ,
      ENNReal.ofReal ((3 : ℝ) ^ (-(s / 4) * (v : ℝ))
          * shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2)
        ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 4 : ℝ) * s
              * ((m - (m - (v : ℤ)) : ℤ) : ℝ)))
            * ∑ k ∈ Finset.Icc (m - (v : ℤ) - 1) m,
                shellBlockLatticeAtom M m omega k ^ 2 := by
    intro v
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _), quarter_weight_eq]
    refine mul_le_mul_right
      (le_trans (ofReal_shellBlockLatticeReal_sq_le M m omega (by omega)) ?_) _
    exact Finset.single_le_sum
      (f := fun k => shellBlockLatticeAtom M m omega k ^ 2) (fun _i _hi => zero_le)
      (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  calc (∑' v : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(s / 4) * (v : ℝ))
          * shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2))
      ≤ ∑' v : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 4 : ℝ) * s
            * ((m - (m - (v : ℤ)) : ℤ) : ℝ)))
          * ∑ k ∈ Finset.Icc (m - (v : ℤ) - 1) m,
              shellBlockLatticeAtom M m omega k ^ 2 := ENNReal.tsum_le_tsum hterm
    _ ≤ ∑' n : {n : ℤ // n ≤ m},
          ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 4 : ℝ) * s * ((m - n.1 : ℤ) : ℝ)))
            * ∑ k ∈ Finset.Icc (n.1 - 1) m, shellBlockLatticeAtom M m omega k ^ 2 :=
        ENNReal.tsum_comp_le_tsum_of_injective hinj (fun n : {n : ℤ // n ≤ m} =>
          ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 4 : ℝ) * s * ((m - n.1 : ℤ) : ℝ)))
            * ∑ k ∈ Finset.Icc (n.1 - 1) m, shellBlockLatticeAtom M m omega k ^ 2)

/-- **The `𝒢₁ᵇ` reading, summability half**, at the A5b-pinned shell family. -/
theorem summable_shellQuarter_of_eventG1 (M : ABKModel d) (m : ℤ) {s T : ℝ}
    {omega : Cutoff.CutoffSample d} (homega : omega ∈ Support.eventG1 M m s T) :
    Summable (fun v : ℕ => (3 : ℝ) ^ (-(s / 4) * (v : ℝ))
      * shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2) :=
  summable_of_ofReal_tsum_ne_top (shellQuarterFam_nonneg M m s omega)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((ofReal_shellQuarter_tsum_le M m s omega).trans homega.2))

/-- **The `𝒢₁ᵇ` reading, value half.** -/
theorem tsum_shellQuarter_le_of_eventG1 (M : ABKModel d) (m : ℤ) {s T : ℝ}
    (hT : 0 ≤ T) {omega : Cutoff.CutoffSample d}
    (homega : omega ∈ Support.eventG1 M m s T) :
    (∑' v : ℕ, (3 : ℝ) ^ (-(s / 4) * (v : ℝ))
        * shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2) ≤ T ^ 2 :=
  tsum_le_of_ofReal_tsum_le (shellQuarterFam_nonneg M m s omega) (sq_nonneg T)
    (((ofReal_shellQuarter_tsum_le M m s omega).trans homega.2).trans
      (le_of_eq (by rw [ENNReal.ofReal_pow hT])))

/-- **The `hAsum` binder of `ClauseOne.clauseOne_bound`**, at the A5b-pinned
family: the display weight `3^{−(s/2)v}` is below the event weight
`3^{−(s/4)v}`. -/
theorem summable_shellBlockLatticeReal_of_eventG1 (M : ABKModel d) (m : ℤ)
    {s T : ℝ} (hs0 : 0 ≤ s) {omega : Cutoff.CutoffSample d}
    (homega : omega ∈ Support.eventG1 M m s T) :
    Summable (fun v : ℕ => (3 : ℝ) ^ (-(s / 2) * (v : ℝ))
      * shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2) := by
  refine Summable.of_nonneg_of_le
    (fun v => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (sq_nonneg _)) ?_
    (summable_shellQuarter_of_eventG1 M m homega)
  intro v
  have hv : (0 : ℝ) ≤ (v : ℝ) := Nat.cast_nonneg v
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hstep : (0 : ℝ) ≤ (s / 4) * (v : ℝ) := by positivity
  have hstep2 : (0 : ℝ) ≤ (s / 4) * (v : ℝ) := hstep
  have hkey : -(s / 2) * (v : ℝ) = -(s / 4) * (v : ℝ) - (s / 4) * (v : ℝ) := by ring
  linarith only [hkey, hstep2]

/-- **The partial-sum budget** feeding `AssemblyFeed.summable_annFam_grad` and
`AssemblyFeed.summable_annFam_l2`: the head block of the shell family is at most
`3^{s/4} T²` times the honest weight `3^{(s/4)(m−n)}`. -/
theorem shellPartialSum_le_of_eventG1 (M : ABKModel d) (m : ℤ) {s T : ℝ}
    (hs0 : 0 ≤ s) (hT : 0 ≤ T) {omega : Cutoff.CutoffSample d}
    (homega : omega ∈ Support.eventG1 M m s T) (n : ℤ) (hnm : n ≤ m) :
    ∑ v ∈ Finset.range ((m - n).toNat + 2),
        shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2
      ≤ ((3 : ℝ) ^ (s / 4) * T ^ 2) * (3 : ℝ) ^ (s / 4 * ((m - n : ℤ) : ℝ)) := by
  classical
  set N : ℕ := (m - n).toNat + 2 with hN
  have hcast : (((m - n).toNat : ℕ) : ℝ) = ((m - n : ℤ) : ℝ) := by
    have hz : ((m - n).toNat : ℤ) = m - n := Int.toNat_of_nonneg (by omega)
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hz
  have hsum := summable_shellQuarter_of_eventG1 M m (s := s) (T := T) homega
  have hbound := tsum_shellQuarter_le_of_eventG1 M m (s := s) (T := T) hT homega
  -- each block entry is the weighted entry times the weight's inverse
  have hterm : ∀ v ∈ Finset.range N,
      shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2
        ≤ (3 : ℝ) ^ (s / 4 * (((m - n : ℤ) : ℝ) + 1))
          * ((3 : ℝ) ^ (-(s / 4) * (v : ℝ))
              * shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2) := by
    intro v hv
    rw [Finset.mem_range, hN] at hv
    have hvle : (v : ℝ) ≤ ((m - n : ℤ) : ℝ) + 1 := by
      have : (v : ℝ) ≤ (((m - n).toNat : ℕ) : ℝ) + 1 := by
        have hvn : v ≤ (m - n).toNat + 1 := by omega
        exact_mod_cast hvn
      rw [hcast] at this
      exact this
    have hmono : (3 : ℝ) ^ (s / 4 * (v : ℝ))
        ≤ (3 : ℝ) ^ (s / 4 * (((m - n : ℤ) : ℝ) + 1)) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      exact mul_le_mul_of_nonneg_left hvle (by positivity)
    have hcancel : (3 : ℝ) ^ (s / 4 * (v : ℝ)) * (3 : ℝ) ^ (-(s / 4) * (v : ℝ)) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      norm_num
    calc shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2
        = (3 : ℝ) ^ (s / 4 * (v : ℝ))
            * ((3 : ℝ) ^ (-(s / 4) * (v : ℝ))
              * shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2) := by
          rw [← mul_assoc, hcancel, one_mul]
      _ ≤ (3 : ℝ) ^ (s / 4 * (((m - n : ℤ) : ℝ) + 1))
            * ((3 : ℝ) ^ (-(s / 4) * (v : ℝ))
              * shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2) :=
          mul_le_mul_of_nonneg_right hmono (shellQuarterFam_nonneg M m s omega v)
  have hstep : ∑ v ∈ Finset.range N,
      shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2
      ≤ (3 : ℝ) ^ (s / 4 * (((m - n : ℤ) : ℝ) + 1))
        * ∑ v ∈ Finset.range N, ((3 : ℝ) ^ (-(s / 4) * (v : ℝ))
            * shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hpartial : ∑ v ∈ Finset.range N, ((3 : ℝ) ^ (-(s / 4) * (v : ℝ))
      * shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2)
      ≤ ∑' v : ℕ, (3 : ℝ) ^ (-(s / 4) * (v : ℝ))
          * shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2 :=
    hsum.sum_le_tsum _ (fun v _ => shellQuarterFam_nonneg M m s omega v)
  have hcoef0 : (0 : ℝ) ≤ (3 : ℝ) ^ (s / 4 * (((m - n : ℤ) : ℝ) + 1)) :=
    Real.rpow_nonneg (by norm_num) _
  have hcombine : ∑ v ∈ Finset.range N,
      shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2
      ≤ (3 : ℝ) ^ (s / 4 * (((m - n : ℤ) : ℝ) + 1)) * T ^ 2 :=
    le_trans hstep (mul_le_mul_of_nonneg_left (le_trans hpartial hbound) hcoef0)
  refine le_trans hcombine (le_of_eq ?_)
  have hsplit : (3 : ℝ) ^ (s / 4 * (((m - n : ℤ) : ℝ) + 1))
      = (3 : ℝ) ^ (s / 4) * (3 : ℝ) ^ (s / 4 * ((m - n : ℤ) : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  rw [hsplit]
  ring

/-! ## Part D -- the two budget-family summabilities at the pinned carriers -/

/-- **The `hsumG` binder at the A2b head-block gradient family.**  Composition of
`EventBudgets.annularGradBlock_le` (the `hcsGn` slot at `Kgn = 81`) with the
`𝒢₁` partial-sum budget. -/
theorem summable_annFam_annularGradBlock_of_eventG1 (M : ABKModel d) (m : ℤ)
    {s T : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (hT : 0 ≤ T)
    {omega : Cutoff.CutoffSample d} (homega : omega ∈ Support.eventG1 M m s T) :
    Summable (annFam m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ)))
      * annularGradBlock M m omega j n)) :=
  summable_annFam_grad (Kgn := 81) (Ksh := (3 : ℝ) ^ (s / 4) * T ^ 2)
    (A := shellBlockLatticeReal M m omega) hs0 hs1 (by norm_num) (by positivity)
    (annularGradBlock_nonneg M m omega)
    (fun j n hj hn => annularGradBlock_le M m omega j n hj hn)
    (fun n hn => shellPartialSum_le_of_eventG1 M m hs0.le hT homega n hn)

/-- **The `hsumL` binder at the A2b head-block value family.**  Composition of
`EventBudgets.annularL2Block_le` (the `hcsL2` slot at `Kl2 = 1`) with the same
budget; the extra `3^{2γ(m−n)}` is absorbed by `8γ ≤ s`. -/
theorem summable_annFam_annularL2Block_of_eventG1 (M : ABKModel d) (m : ℤ)
    {s T : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (hsg : 8 * M.gamma ≤ s) (hT : 0 ≤ T)
    {omega : Cutoff.CutoffSample d} (homega : omega ∈ Support.eventG1 M m s T) :
    Summable (annFam m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ)))
      * annularL2Block M m omega j n)) :=
  summable_annFam_l2 (gamma := M.gamma) (Kl2 := 1) (Ksh := (3 : ℝ) ^ (s / 4) * T ^ 2)
    (A := shellBlockLatticeReal M m omega) hs0 hs1 hsg (by norm_num) (by positivity)
    (annularL2Block_nonneg M m omega)
    (fun j n hj hn => annularL2Block_le M m omega j n hj hn)
    (fun n hn => shellPartialSum_le_of_eventG1 M m hs0.le hT homega n hn)

end

end Algsuperdiff.Section4.Provider.Annular
