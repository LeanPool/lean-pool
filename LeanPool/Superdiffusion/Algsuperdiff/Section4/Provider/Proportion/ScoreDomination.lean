/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.Ycal

/-!
# ScoreDomination

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The deterministic domination of the `𝒢₀` score by the `𝒴` row sum

ABK26, §4.1, `l.good.scales.ratio.lambda`, score domination:

```
sup_{k ≤ m} 3^{−¼γ(m−k)} max_{z ∈ 3^{k−2}ℤ^d ∩ (□_m∖□_k)} ( … )_+
   ≤  γ⁴ Σ_{n ≤ m} 3^{−¼γ(m−n)} 𝒴_n .
```

Everything here is **pointwise in `ω` and unconditional**: the whole chain is
run in `ℝ≥0∞`, where the `k`-series inside `𝒴_n` and the `n`-row sum both
always exist.

The normalization `γ^{-4}` is NOT carried by `𝒴` here; it is a lane prefactor
and appears only in the downstream threshold.  Consequently the display below
has no `γ⁴` on the right: the inequality is between the score and the
*un-normalized* row sum.

## Main results

* `exists_mem_latticeAnnulusSet` — the annulus decomposition of the shell
  `□_m ∖ □_k` at a fixed lattice spacing (the union bound).
* `eventG0_score_le_YcalRowE` — the display, pointwise and unconditional.
* `one_lt_YcalRowE_of_notMem_eventG0` — its consumption: off `𝒢₀(m)` the row
  sum exceeds `1`.

## Scope

Provider material: proved local helpers, pointwise in `ω`.

## References

* ABK26, `l.good.scales.ratio.lambda`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The annulus decomposition of a shell -/

private theorem exists_annulus_index_aux (d : ℕ) (j k : ℤ) (v : Fin d → ℤ) :
    ∀ t : ℕ,
      Support.triadicLatticePoint j v ∈ openCubeSet (originCube d (k + (t : ℤ))) →
      Support.triadicLatticePoint j v ∉ openCubeSet (originCube d k) →
      ∃ n : ℤ, k + 1 ≤ n ∧ n ≤ k + (t : ℤ) ∧
        Support.triadicLatticePoint j v ∈
          openCubeSet (originCube d n) \ openCubeSet (originCube d (n - 1)) := by
  intro t
  induction t with
  | zero =>
      intro hin hout
      exact absurd (by simpa only [Nat.cast_zero, add_zero] using hin) hout
  | succ t ih =>
      intro hin hout
      by_cases hprev :
          Support.triadicLatticePoint j v ∈ openCubeSet (originCube d (k + (t : ℤ)))
      · obtain ⟨n, h1, h2, h3⟩ := ih hprev hout
        exact ⟨n, h1, by push_cast; omega, h3⟩
      · refine ⟨k + (t : ℤ) + 1, by omega, by push_cast; omega, ⟨?_, ?_⟩⟩
        · have hrw : k + ((t : ℤ) + 1) = k + (t : ℤ) + 1 := by ring
          have hin' : Support.triadicLatticePoint j v ∈
              openCubeSet (originCube d (k + ((t + 1 : ℕ) : ℤ))) := hin
          rw [show ((t + 1 : ℕ) : ℤ) = (t : ℤ) + 1 by push_cast; ring, hrw] at hin'
          exact hin'
        · have hrw : k + (t : ℤ) + 1 - 1 = k + (t : ℤ) := by ring
          rw [hrw]
          exact hprev

/-- **The annulus decomposition of a shell at a fixed lattice spacing** ("by
union bounds").  Every lattice point of `□_m ∖ □_k` lies in exactly one triadic
annulus `□_n ∖ □_{n−1}` with `k + 1 ≤ n ≤ m`. -/
theorem exists_mem_latticeAnnulusSet (d : ℕ) {j k m : ℤ} (hkm : k ≤ m)
    {v : Fin d → ℤ} (hv : v ∈ Support.latticeAnnulusSet d j m k) :
    ∃ n ∈ Finset.Icc (k + 1) m, v ∈ Support.latticeAnnulusSet d j n (n - 1) := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ, m = k + (t : ℤ) := ⟨(m - k).toNat, by omega⟩
  have hin : Support.triadicLatticePoint j v ∈ openCubeSet (originCube d (k + (t : ℤ))) := by
    rw [← ht]; exact hv.1
  obtain ⟨n, h1, h2, h3⟩ := exists_annulus_index_aux d j k v t hin hv.2
  exact ⟨n, Finset.mem_Icc.2 ⟨h1, by omega⟩, h3⟩

/-! ## 2. Two small `ℝ≥0∞` / weight identities -/

private theorem ofReal_max_zero (x : ℝ) : ENNReal.ofReal (max x 0) = ENNReal.ofReal x := by
  rcases le_or_gt 0 x with hx | hx
  · rw [max_eq_left hx]
  · rw [max_eq_right hx.le, ENNReal.ofReal_zero, ENNReal.ofReal_eq_zero.2 hx.le]

theorem weightThird_add (sprime : ℝ) (a b : ℕ) :
    weightThird sprime (a + b) = weightThird sprime a * weightThird sprime b := by
  rw [weightThird, weightThird, weightThird, pow_add]

/-- The `𝒢₀` weight is the geometric weight at rate `s' = γ/4`. -/
theorem rpow_weight_eq_weightThird (M : ABKModel d) {m k : ℤ} (hk : k ≤ m) :
    Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * M.gamma * ((m - k : ℤ) : ℝ))
      = weightThird (M.gamma / 4) (m - k).toNat := by
  rw [weightThird_eq]
  have hz : (((m - k).toNat : ℕ) : ℤ) = m - k := Int.toNat_of_nonneg (by omega)
  have hr : (((m - k).toNat : ℕ) : ℝ) = ((m - k : ℤ) : ℝ) := by exact_mod_cast hz
  rw [hr]
  congr 1
  ring

/-! ## 3. The row sum -/

/-- Total: no summability side condition. -/
def YcalRowE (M : ABKModel d) (Ccg sprime : ℝ) (m : ℤ)
    (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  ∑' n : ℤ,
    (if n ≤ m then
      ENNReal.ofReal (weightThird sprime (m - n).toNat) * YcalE M Ccg sprime n omega
    else 0)

/-! ## 4. The domination -/

/-- **The inner union bound**: the lattice maximum over the shell `□_m ∖ □_k` is at
most the sum of the annulus maxima. -/
theorem iSup_shell_le_sum_annMax (M : ABKModel d) (Ccg : ℝ) {m k : ℤ} (hk : k ≤ m - 1)
    (omega : Cutoff.CutoffSample d) :
    (⨆ v : ↥(Support.latticeAnnulusSet d (k - 2) m k),
        ENNReal.ofReal
          ((Annealed.sigmaBar M (k - 3) : ℝ) *
            Support.lambdaAnnulusAtom M k (Support.triadicLatticePoint (k - 2) v.1) omega
              - Ccg))
      ≤ ∑ n ∈ Finset.Icc (k + 1) m, ENNReal.ofReal (annMax M Ccg n k omega) := by
  refine iSup_le fun v => ?_
  obtain ⟨n, hn, hvn⟩ := exists_mem_latticeAnnulusSet d (j := k - 2) (by omega) v.2
  have hnk : k + 1 ≤ n := (Finset.mem_Icc.1 hn).1
  have hmemF : v.1 ∈ latticeAnnulusFinset d (k - 2) n (n - 1) :=
    (mem_latticeAnnulusFinset_iff (by omega)).2 hvn
  have hbracket : ENNReal.ofReal
      ((Annealed.sigmaBar M (k - 3) : ℝ) *
        Support.lambdaAnnulusAtom M k (Support.triadicLatticePoint (k - 2) v.1) omega - Ccg)
      = ENNReal.ofReal
          (Localize.cgExcess M Ccg (k - 2)
            (Support.triadicLatticePoint (k - 2) v.1) omega) := by
    rw [Localize.cgExcess_sub_two, ofReal_max_zero]
  have hle : Localize.cgExcess M Ccg (k - 2)
      (Support.triadicLatticePoint (k - 2) v.1) omega ≤ annMax M Ccg n k omega :=
    le_fmax (S := latticeAnnulusFinset d (k - 2) n (n - 1))
      (f := fun w : Fin d → ℤ =>
        Localize.cgExcess M Ccg (k - 2) (Support.triadicLatticePoint (k - 2) w) omega)
      hmemF
  rw [hbracket]
  refine le_trans (ENNReal.ofReal_le_ofReal hle) ?_
  exact Finset.single_le_sum (f := fun n => ENNReal.ofReal (annMax M Ccg n k omega))
    (fun _ _ => zero_le) hn

/-- **The score-domination display, pointwise and unconditional.**

The supremum defining `𝒢₀(m)` is at most the `𝒴` row sum at rate `s' = γ/4`.
The manuscript's `γ⁴` is absent because `𝒴` is not normalized here; the two
statements differ by that lane prefactor alone. -/
theorem eventG0_score_le_YcalRowE (M : ABKModel d) (Ccg : ℝ) (m : ℤ)
    (omega : Cutoff.CutoffSample d) :
    (⨆ k : {k : ℤ // k ≤ m - 1},
        ENNReal.ofReal
            (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * M.gamma * ((m - k.1 : ℤ) : ℝ))) *
          ⨆ v : ↥(Support.latticeAnnulusSet d (k.1 - 2) m k.1),
            ENNReal.ofReal
              ((Annealed.sigmaBar M (k.1 - 3) : ℝ) *
                  Support.lambdaAnnulusAtom M k.1
                    (Support.triadicLatticePoint (k.1 - 2) v.1) omega -
                Ccg))
      ≤ YcalRowE M Ccg (M.gamma / 4) m omega := by
  classical
  refine iSup_le fun k => ?_
  have hk : k.1 ≤ m - 1 := k.2
  have hweight : Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * M.gamma * ((m - k.1 : ℤ) : ℝ))
      = weightThird (M.gamma / 4) (m - k.1).toNat :=
    rpow_weight_eq_weightThird M (by omega)
  rw [hweight]
  -- step 1: the inner union bound
  refine le_trans (mul_le_mul_right (iSup_shell_le_sum_annMax M Ccg hk omega) _) ?_
  rw [Finset.mul_sum]
  -- step 2: split the weight and fold each term into `𝒴_n`
  have hterm : ∀ n ∈ Finset.Icc (k.1 + 1) m,
      ENNReal.ofReal (weightThird (M.gamma / 4) (m - k.1).toNat) *
          ENNReal.ofReal (annMax M Ccg n k.1 omega)
        ≤ ENNReal.ofReal (weightThird (M.gamma / 4) (m - n).toNat) *
            YcalE M Ccg (M.gamma / 4) n omega := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
    have hsplitNat : (m - k.1).toNat = (m - n).toNat + (n - k.1).toNat := by omega
    have hsplit : weightThird (M.gamma / 4) (m - k.1).toNat
        = weightThird (M.gamma / 4) (m - n).toNat * weightThird (M.gamma / 4) (n - k.1).toNat := by
      rw [hsplitNat, weightThird_add]
    rw [hsplit, ENNReal.ofReal_mul (weightThird_pos _).le, mul_assoc]
    refine mul_le_mul_right ?_ _
    rw [← ENNReal.ofReal_mul (weightThird_pos _).le]
    have hidx : n - (((n - k.1).toNat : ℕ) : ℤ) = k.1 := by omega
    have hbase := le_YcalE M Ccg (M.gamma / 4) n omega (n - k.1).toNat
    rw [hidx] at hbase
    exact hbase
  refine le_trans (Finset.sum_le_sum hterm) ?_
  -- step 3: the finite sum is below the total row sum
  have hrw : ∀ n ∈ Finset.Icc (k.1 + 1) m,
      ENNReal.ofReal (weightThird (M.gamma / 4) (m - n).toNat) *
          YcalE M Ccg (M.gamma / 4) n omega
        = (if n ≤ m then
            ENNReal.ofReal (weightThird (M.gamma / 4) (m - n).toNat) *
              YcalE M Ccg (M.gamma / 4) n omega
          else 0) := by
    intro n hn
    rw [ite_eq_left (Finset.mem_Icc.1 hn).2]
  rw [Finset.sum_congr rfl hrw]
  exact ENNReal.sum_le_tsum _

/-- **The consumption of the display.**  Off `𝒢₀(m)` the `𝒴` row sum exceeds the
threshold `1` of the good event.  This is the deterministic half of the
Appendix-D reduction. -/
theorem one_lt_YcalRowE_of_notMem_eventG0 (M : ABKModel d) (Ccg : ℝ) (m : ℤ)
    {omega : Cutoff.CutoffSample d} (homega : omega ∉ Support.eventG0 M Ccg m) :
    1 < YcalRowE M Ccg (M.gamma / 4) m omega := by
  have hgt : ¬ ((⨆ k : {k : ℤ // k ≤ m - 1},
      ENNReal.ofReal
          (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * M.gamma * ((m - k.1 : ℤ) : ℝ))) *
        ⨆ v : ↥(Support.latticeAnnulusSet d (k.1 - 2) m k.1),
          ENNReal.ofReal
            ((Annealed.sigmaBar M (k.1 - 3) : ℝ) *
                Support.lambdaAnnulusAtom M k.1
                  (Support.triadicLatticePoint (k.1 - 2) v.1) omega -
              Ccg)) ≤ 1) := homega
  exact lt_of_lt_of_le (not_le.1 hgt) (eventG0_score_le_YcalRowE M Ccg m omega)

end

end Algsuperdiff.Section4.Provider.Proportion
