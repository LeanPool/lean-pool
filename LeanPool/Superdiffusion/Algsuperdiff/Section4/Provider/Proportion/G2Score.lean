/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.Ycal

/-!
# G2Score

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `𝒢₂` score layer: the squared annular maximum, the atom `X_j`, and the
# exact interchange identity

ABK26, §4.1, the proof of `l.ratio.of.good.scales.for.mathcal.E`, Steps 1, 2 and
4.

The `𝒢₂` lane is structurally the cleanest of the three: where the `𝒢₀`
reduction is a chain of inequalities, the `𝒢₂` reduction is an **equality**:

```
s Σ_{j ≤ m} Σ_{n ≤ j−1} 3^{−¼s(m−n)} max_{z ∈ 3ⁿℤ^d ∩ (□_j∖□_{j−1})} 𝓔_{s,2,2}(z+□_n;·)²
  = K₂^{−1} s ε² Y_m ,        Y_m = Σ_{j ≤ m} 3^{−¼s(m−j)} X_j ,
```

whose entire content is the exponent split `3^{−¼s(m−n)} =
3^{−¼s(m−j)}·3^{−¼s(j−n)}` (`annularWeight_split`).  Everything below is proved
as an *identity* of `ℝ≥0∞`, so no convergence, no `a.s.` qualifier and no null
set enters: the convergence caveat that the printed `Y_m` identity leaves
implicit is therefore never needed.

## Main definitions

* `annularWeight` — the `ℝ≥0∞` weight `3^{−¼sk}` of the `𝒢₂` displays.
* `errorAtomSq` — the per-cube atom `𝓔_{s,2,2}(z+□_n; 𝐚_{n−2}, σ_{n−2})²`,
  rendered by translating the *sample*, at the public measurable `(2,2)`
  observable of `Support.ErrorRepresentative22`.
* `errorAnnMax` — the `0`-floored lattice maximum of Step 1's left side, over the
  `Finset` enumeration of `3^nℤ^d ∩ (□_j∖□_{j−1})`.
* `errorAnnSup` — the same maximum in the `ℝ≥0∞` supremum shape the frozen
  `Support.eventG2` uses; `errorAnnSup_eq_ofReal_errorAnnMax` identifies the two.
* `XcalE` — the atom `X_j`, **without** the manuscript's lane
  prefactor `K₂ε^{−2}`: the normalizer is a free parameter of the downstream
  threshold, not a rescaling of the score field.
* `XrowE` — the one-sided row sum `Σ_{j ≤ m} 3^{−¼s(m−j)} X_j`.

## Main results

* `annularWeight_split` — the exponent split; the whole content of the identity.
* `inner_eq_annularWeight_mul_XcalE` — **the identity**, an equality of `ℝ≥0∞`.
* `eventG2_eq_row` — the frozen `𝒢₂` event *is* `{s·XrowE ≤ ε²}`, exactly.

## Deviations from the printed text

* The summand reads the field at the *inner* scale `n` (`𝓔_{s,2,2}(z+□_n;
  𝐚_{n−2}, σ_{n−2})`), a per-inner-scale truncation.  This is the proved
  `Support.annularErrorObservable` at index `n`, so the convention is the
  manuscript's.
* `K₂ε^{−2}` is a lane prefactor, kept explicit.
* The row `XrowE` is the manuscript's one-sided row; the reconciliation with
  Appendix D's two-sided row is downstream and is an inequality in the
  manuscript's favour (the `j > m` rows are nonnegative).
* The `𝒢₂` observable is the measurable representative, choice-dependent
  on a null set; the manuscript's literal event is recovered a.e. through
  `Support.annularErrorAtom_ae_eq_annularErrorObservable`.  Nothing in this file
  depends on the choice: every statement is an identity between two expressions
  in the same observable.

## Scope

Provider material: proved local helpers.

## References

* ABK26, `l.ratio.of.good.scales.for.mathcal.E`; `d.good.event.for.lambda`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The geometric weight of the `𝒢₂` lane -/

/-- **The `𝒢₂` weight `3^{−¼sk}`, in `ℝ≥0∞`.**  Written exactly as the frozen
`Support.eventG2` writes it, so the identifications below are definitional on the
weight. -/
def annularWeight (s : ℝ) (k : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * s * ((k : ℤ) : ℝ)))

private theorem rpow_three_nonneg (x : ℝ) : (0 : ℝ) ≤ Real.rpow (3 : ℝ) x :=
  Real.rpow_nonneg (by norm_num) x

private theorem rpow_three_add (y z : ℝ) :
    Real.rpow (3 : ℝ) (y + z) = Real.rpow (3 : ℝ) y * Real.rpow (3 : ℝ) z :=
  Real.rpow_add (by norm_num) y z

/-- **The exponent split.**  `3^{−¼s(m−n)} = 3^{−¼s(m−j)}·3^{−¼s(j−n)}`: the single
computation behind's "by interchanging summation". -/
theorem annularWeight_split (s : ℝ) (m j n : ℤ) :
    annularWeight s (m - n) = annularWeight s (m - j) * annularWeight s (j - n) := by
  have hsplit : Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * s * ((m - n : ℤ) : ℝ))
      = Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * s * ((m - j : ℤ) : ℝ)) *
        Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * s * ((j - n : ℤ) : ℝ)) := by
    rw [← rpow_three_add]
    congr 1
    push_cast
    ring
  rw [annularWeight, annularWeight, annularWeight, hsplit,
    ENNReal.ofReal_mul (rpow_three_nonneg _)]

/-- The weight at a nonnegative offset is the `𝒢₀` lane's `weightThird` at rate
`¼s`; this is what lets the `ℕ`-indexed series apparatus of `SeriesTail` be
reused verbatim. -/
theorem annularWeight_eq_weightThird {s : ℝ} {k : ℤ} (hk : 0 ≤ k) :
    annularWeight s k = ENNReal.ofReal (weightThird (s / 4) k.toNat) := by
  rw [annularWeight, weightThird_eq]
  congr 2
  have hz : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk
  have hr : ((k.toNat : ℕ) : ℝ) = ((k : ℤ) : ℝ) := by exact_mod_cast hz
  rw [hr]
  ring

/-! ## 2. The squared per-cube atom and its lattice maximum -/

/-- **The `𝒢₂` per-cube atom** `𝓔_{s,2,2}(z+□_n; 𝐚_{n−2}, σ_{n−2})²`, rendered by
translating the sample, at the measurable `(2,2)` observable. -/
def errorAtomSq (M : ABKModel d) (n : ℤ) (s : {s : ℝ // 0 < s}) (z : Vec d)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  Support.annularErrorObservable M n s (Cutoff.translateCutoffSample z omega) ^ 2

theorem errorAtomSq_nonneg (M : ABKModel d) (n : ℤ) (s : {s : ℝ // 0 < s})
    (z : Vec d) (omega : Cutoff.CutoffSample d) : 0 ≤ errorAtomSq M n s z omega :=
  sq_nonneg _

theorem measurable_errorAtomSq (M : ABKModel d) (n : ℤ) (s : {s : ℝ // 0 < s})
    (z : Vec d) : Measurable (errorAtomSq M n s z) :=
  (((Support.measurable_annularErrorObservable M n s).comp
    (Cutoff.measurable_translateCutoffSample z)).pow_const 2)

/-- **The left side of Step 1**: `max_{z ∈ 3^nℤ^d ∩ (□_j∖□_{j−1})} 𝓔_{s,2,2}(z+□_n;
𝐚_{n−2}, σ_{n−2})²`, `0`-floored so that it is total (the annulus enumeration
may be empty). -/
def errorAnnMax (M : ABKModel d) (s : {s : ℝ // 0 < s}) (j n : ℤ)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  fmax (latticeAnnulusFinset d n j (j - 1))
    (fun v => errorAtomSq M n s (Support.triadicLatticePoint n v) omega)

theorem errorAnnMax_nonneg (M : ABKModel d) (s : {s : ℝ // 0 < s}) (j n : ℤ)
    (omega : Cutoff.CutoffSample d) : 0 ≤ errorAnnMax M s j n omega :=
  fmax_nonneg _ _

theorem measurable_errorAnnMax (M : ABKModel d) (s : {s : ℝ // 0 < s}) (j n : ℤ) :
    Measurable (errorAnnMax M s j n) :=
  measurable_fmax _ fun v => measurable_errorAtomSq M n s (Support.triadicLatticePoint n v)

/-- **The same maximum in the `ℝ≥0∞` supremum shape of the frozen event.** -/
def errorAnnSup (M : ABKModel d) (s : {s : ℝ // 0 < s}) (j n : ℤ)
    (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  ⨆ v : ↥(Support.latticeAnnulusSet d n j (j - 1)),
    ENNReal.ofReal (errorAtomSq M n s (Support.triadicLatticePoint n v.1) omega)

/-! ### The `Finset` maximum and the set supremum agree -/

variable {iota : Type*}

/-- A nonempty `Finset` attains its `0`-floored maximum at a member, provided the
values there are nonnegative. -/
theorem exists_mem_eq_fmax {S : Finset iota} {f : iota → ℝ} (hS : S.Nonempty)
    (hf : ∀ i ∈ S, 0 ≤ f i) : ∃ i ∈ S, fmax S f = f i := by
  classical
  obtain ⟨i, hi, hsup⟩ :=
    Finset.exists_mem_eq_sup (α := NNReal) S hS (fun i => (f i).toNNReal)
  refine ⟨i, hi, ?_⟩
  rw [fmax, hsup]
  exact Real.coe_toNNReal (f i) (hf i hi)

/-- **The two renderings of the lattice maximum coincide.**  The `Finset`
enumeration `latticeAnnulusFinset` and the proved set `latticeAnnulusSet` have
the same members at `n ≤ j`, and all entries are squares, hence nonnegative, so
the `0`-floor is not felt. -/
theorem errorAnnSup_eq_ofReal_errorAnnMax (M : ABKModel d) (s : {s : ℝ // 0 < s})
    {j n : ℤ} (hn : n ≤ j) (omega : Cutoff.CutoffSample d) :
    errorAnnSup M s j n omega = ENNReal.ofReal (errorAnnMax M s j n omega) := by
  classical
  refine le_antisymm (iSup_le fun v => ?_) ?_
  · refine ENNReal.ofReal_le_ofReal ?_
    exact le_fmax (S := latticeAnnulusFinset d n j (j - 1))
      (f := fun w : Fin d → ℤ => errorAtomSq M n s (Support.triadicLatticePoint n w) omega)
      ((mem_latticeAnnulusFinset_iff (d := d) hn).2 v.2)
  · rcases Finset.eq_empty_or_nonempty (latticeAnnulusFinset d n j (j - 1)) with hE | hE
    · rw [errorAnnMax, hE, fmax_empty, ENNReal.ofReal_zero]
      exact zero_le
    · obtain ⟨v, hv, hveq⟩ :=
        exists_mem_eq_fmax (f := fun w : Fin d → ℤ =>
          errorAtomSq M n s (Support.triadicLatticePoint n w) omega) hE
          (fun w _ => errorAtomSq_nonneg M n s _ omega)
      rw [errorAnnMax, hveq]
      exact le_iSup_of_le
        ⟨v, (mem_latticeAnnulusFinset_iff (d := d) hn).1 hv⟩ le_rfl

/-! ## 3. The atom `X_j` and the row sum -/

/-- **The atom `X_j`**, formed in `ℝ≥0∞` and WITHOUT the manuscript's lane
prefactor `K₂ε^{−2}`: `Σ_{n ≤ j−1} 3^{−¼s(j−n)} max_{z ∈ 3^nℤ^d ∩
(□_j∖□_{j−1})} 𝓔_{s,2,2}(z+□_n;·)²`. -/
def XcalE (M : ABKModel d) (s : {s : ℝ // 0 < s}) (j : ℤ)
    (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  ∑' n : {n : ℤ // n ≤ j - 1},
    annularWeight (s : ℝ) (j - n.1) * errorAnnSup M s j n.1 omega

/-- **The one-sided row sum `Y_m`**, before the `K₂ε^{−2}` normalization. -/
def XrowE (M : ABKModel d) (s : {s : ℝ // 0 < s}) (m : ℤ)
    (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  ∑' j : {j : ℤ // j ≤ m}, annularWeight (s : ℝ) (m - j.1) * XcalE M s j omega

/-! ### The `ℕ`-enumeration of the inner scales -/

/-- The inner scales `n ≤ j − 1` enumerated by the offset `j − n − 1 ∈ ℕ`. -/
def innerScaleEquiv (j : ℤ) : ℕ ≃ {n : ℤ // n ≤ j - 1} where
  toFun i := ⟨j - 1 - (i : ℤ), by omega⟩
  invFun n := (j - 1 - n.1).toNat
  left_inv i := by
    show (j - 1 - (j - 1 - (i : ℤ))).toNat = i
    omega
  right_inv n := by
    refine Subtype.ext ?_
    show j - 1 - (((j - 1 - n.1).toNat : ℕ) : ℤ) = n.1
    have hn := n.2
    omega

/-- **The atom is the `SeriesTail` weighted series** at the `𝒢₀` lane's weight
`weightThird (¼s)` shifted by one (the inner offset `j − n` starts at `1`).  This
is the bridge that lets the countable generalized triangle inequality
`isBigOWith_wsum` and the moment engine be reused verbatim on the `𝒢₂` lane. -/
theorem XcalE_eq_wsumE (M : ABKModel d) (s : {s : ℝ // 0 < s}) (j : ℤ)
    (omega : Cutoff.CutoffSample d) :
    XcalE M s j omega =
      wsumE (fun i => errorAnnMax M s j (j - 1 - (i : ℤ)))
        (fun i => weightThird ((s : ℝ) / 4) (i + 1)) omega := by
  rw [XcalE, ← (innerScaleEquiv j).tsum_eq
      (fun n : {n : ℤ // n ≤ j - 1} =>
        annularWeight (s : ℝ) (j - n.1) * errorAnnSup M s j n.1 omega),
    wsumE]
  refine tsum_congr fun i => ?_
  have hsub : j - (j - 1 - (i : ℤ)) = (i : ℤ) + 1 := by ring
  have hnle : j - 1 - (i : ℤ) ≤ j := by omega
  have htn : ((i : ℤ) + 1).toNat = i + 1 := by omega
  show annularWeight (s : ℝ) (j - (j - 1 - (i : ℤ))) *
      errorAnnSup M s j (j - 1 - (i : ℤ)) omega = _
  rw [hsub, annularWeight_eq_weightThird (by omega : (0 : ℤ) ≤ (i : ℤ) + 1), htn,
    errorAnnSup_eq_ofReal_errorAnnMax M s hnle omega,
    ← ENNReal.ofReal_mul (weightThird_pos _).le]

/-! ## 4. The identity -/

/-- **The identity.**  For every row index `m` and every annulus index `j`, the inner block
of the `𝒢₂` display is *exactly* the discounted atom.  This is an equality of
`ℝ≥0∞`: nothing is dropped, no convergence is used, and the entire content is
`annularWeight_split`. -/
theorem inner_eq_annularWeight_mul_XcalE (M : ABKModel d) (s : {s : ℝ // 0 < s})
    (m j : ℤ) (omega : Cutoff.CutoffSample d) :
    (∑' n : {n : ℤ // n ≤ j - 1},
        annularWeight (s : ℝ) (m - n.1) * errorAnnSup M s j n.1 omega)
      = annularWeight (s : ℝ) (m - j) * XcalE M s j omega := by
  rw [XcalE, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [annularWeight_split (s : ℝ) m j n.1, mul_assoc]

/-! ## 5. The frozen event, in row-sum form -/

/-- **The frozen `𝒢₂` event IS `{s·XrowE ≤ ε²}`.**  A set equality, obtained by
applying the identity inside the outer sum. -/
theorem eventG2_eq_row (M : ABKModel d) (m : ℤ) (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    Support.eventG2 M m s ep =
      {omega | ENNReal.ofReal (s : ℝ) * XrowE M s m omega ≤ ENNReal.ofReal (ep ^ 2)} := by
  ext omega
  have hkey :
      (∑' j : {j : ℤ // j ≤ m}, ∑' n : {n : ℤ // n ≤ j.1 - 1},
          ENNReal.ofReal
              (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * (s : ℝ) * ((m - n.1 : ℤ) : ℝ))) *
            ⨆ v : ↥(Support.latticeAnnulusSet d n.1 j.1 (j.1 - 1)),
              ENNReal.ofReal
                (Support.annularErrorObservable M n.1 s
                  (Cutoff.translateCutoffSample (Support.triadicLatticePoint n.1 v.1)
                    omega) ^ 2))
        = XrowE M s m omega := by
    rw [XrowE]
    exact tsum_congr fun j => inner_eq_annularWeight_mul_XcalE M s m j.1 omega
  rw [Support.mem_eventG2_iff]
  simp only [Set.mem_ofPred_eq]
  rw [hkey]

/-- The complement of the frozen `𝒢₂` event, in row form. -/
theorem notMem_eventG2_iff (M : ABKModel d) (m : ℤ) (s : {s : ℝ // 0 < s}) (ep : ℝ)
    (omega : Cutoff.CutoffSample d) :
    omega ∉ Support.eventG2 M m s ep ↔
      ENNReal.ofReal (ep ^ 2) < ENNReal.ofReal (s : ℝ) * XrowE M s m omega := by
  rw [eventG2_eq_row]
  exact not_le (a := ENNReal.ofReal (s : ℝ) * XrowE M s m omega)
    (b := ENNReal.ofReal (ep ^ 2))

end

end Algsuperdiff.Section4.Provider.Proportion
