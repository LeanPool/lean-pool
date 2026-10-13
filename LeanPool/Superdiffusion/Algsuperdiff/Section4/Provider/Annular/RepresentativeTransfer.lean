/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.ClauseOne
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.ErrorRepresentative22

/-!
# RepresentativeTransfer

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The representative/literal transfer of the clause-(i) display

ABK26, Section 4.1.  `ClauseOne` proves the four-term estimate **pointwise in
`omega`, at a fixed cutoff level `L`, for the literal carriers**
`Support.fluxCorrectedError` and real-valued right-hand families.  The Section
4.1 display is stated **almost surely, at the representative observables, over
the supremum in `L`, in `[0, infinity]`**.  This module performs that transfer.

Three separate moves are involved and each is isolated below.

1. **Literal to representative** (`indicator_observableSqSup_le`).  The proved
   `Support.ae_forall_fluxCorrectedError_eq_representative` gives a single
   probability-one event on which the literal error and its measurable
   representative agree simultaneously for every `L >= m` (the index set is
   countable).  On that event the `[0,infinity]`-valued supremum
   `fluxCorrectedErrorObservableSqSup` is bounded by any uniform-in-`L` bound
   for the literal, and the indicator of the good event only lowers it.
2. **Real to `[0,infinity]`** (`ofReal_tsum_le`,
   `ofReal_annDouble_le_ennDouble`).  This is what lets the display be stated
   without convergence side conditions.
3. **The lattice maxima** (`hE2dom`, `hG1bdom` slots).  The real right-hand families
   of `ClauseOne` are upper bounds for the per-cube atoms; the display carries
   the honest `[0,infinity]`-valued suprema over the lattice index sets.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Section3
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the transport helpers -/

/-- `ofReal` under-approximates an infinite sum of nonnegative reals, with **no**
summability hypothesis: a non-summable real sum is `0` by convention. -/
theorem ofReal_tsum_le {iota : Type*} {f : iota → ℝ} (hf : ∀ i, 0 ≤ f i) :
    ENNReal.ofReal (∑' i, f i) ≤ ∑' i, ENNReal.ofReal (f i) := by
  by_cases hs : Summable f
  · exact le_of_eq (ENNReal.ofReal_tsum_of_nonneg hf hs)
  · rw [tsum_eq_zero_of_not_summable hs, ENNReal.ofReal_zero]
    exact zero_le

/-- `ofReal` commutes with a guarded value. -/
theorem ofReal_ite_zero (P : Prop) [Decidable P] (a : ℝ) :
    ENNReal.ofReal (if P then a else 0) = if P then ENNReal.ofReal a else 0 := by
  split_ifs
  · rfl
  · exact ENNReal.ofReal_zero

/-- The `[0,infinity]`-valued sum over `{j : j <= b}` as a guarded sum over `Z`. -/
theorem ennreal_tsum_guard (b : ℤ) (g : ℤ → ℝ≥0∞) :
    ∑' j : {j : ℤ // j ≤ b}, g j.1 = ∑' j : ℤ, (if j ≤ b then g j else 0) := by
  classical
  have h1 : ∑' j : {j : ℤ // j ≤ b}, g j.1
      = ∑' j : ℤ, Set.indicator {j : ℤ | j ≤ b} g j := tsum_subtype {j : ℤ | j ≤ b} g
  rw [h1]
  refine tsum_congr fun j => ?_
  by_cases hj : j ≤ b
  · rw [Set.indicator_of_mem (show j ∈ {j : ℤ | j ≤ b} from hj), ite_eq_left hj]
  · rw [Set.indicator_of_notMem (show j ∉ {j : ℤ | j ≤ b} from hj), ite_eq_right hj]

/-- **The annular double sum, transported to `[0,infinity]`.**  A nonnegative
real annular double sum is dominated by the corresponding iterated
`[0,infinity]`-valued sum over the two subtypes, given a termwise domination on
the annular region.  No summability enters. -/
theorem ofReal_annDouble_le_ennDouble {m : ℤ} {h : ℤ → ℤ → ℝ} {H : ℤ → ℤ → ℝ≥0∞}
    (hh0 : ∀ j n, 0 ≤ h j n)
    (hdom : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 → ENNReal.ofReal (h j n) ≤ H j n) :
    ENNReal.ofReal (annDouble m h)
      ≤ ∑' j : {j : ℤ // j ≤ m}, ∑' n : {n : ℤ // n ≤ j.1 - 1}, H j.1 n.1 := by
  classical
  have hinner0 : ∀ j : ℤ,
      (0 : ℝ) ≤ ∑' n : ℤ, (if n ≤ j - 1 then h j n else 0) := by
    intro j
    refine tsum_nonneg fun n => ?_
    split_ifs
    · exact hh0 j n
    · exact le_rfl
  have hstep0 : ∀ j : ℤ,
      (0 : ℝ) ≤ (if j ≤ m then ∑' n : ℤ, (if n ≤ j - 1 then h j n else 0) else 0) := by
    intro j
    split_ifs
    · exact hinner0 j
    · exact le_rfl
  have hRHS : ∑' j : {j : ℤ // j ≤ m}, ∑' n : {n : ℤ // n ≤ j.1 - 1}, H j.1 n.1
      = ∑' j : ℤ, (if j ≤ m then ∑' n : {n : ℤ // n ≤ j - 1}, H j n.1 else 0) :=
    ennreal_tsum_guard m (fun j => ∑' n : {n : ℤ // n ≤ j - 1}, H j n.1)
  rw [annDouble_def, hRHS]
  refine le_trans (ofReal_tsum_le hstep0) (ENNReal.tsum_le_tsum fun j => ?_)
  by_cases hj : j ≤ m
  · rw [ofReal_ite_zero, ite_eq_left hj, ite_eq_left hj,
      ennreal_tsum_guard (j - 1) (fun n => H j n)]
    refine le_trans (ofReal_tsum_le (fun n => ?_)) (ENNReal.tsum_le_tsum fun n => ?_)
    · split_ifs
      · exact hh0 j n
      · exact le_rfl
    · rw [ofReal_ite_zero]
      by_cases hn : n ≤ j - 1
      · rw [ite_eq_left hn, ite_eq_left hn]
        exact hdom j n hj hn
      · rw [ite_eq_right hn, ite_eq_right hn]
  · rw [ofReal_ite_zero, ite_eq_right hj, ite_eq_right hj]

/-! ## Part B -- the four right-hand terms at the representative observables -/

/-- The first right-hand term of clause (i): the annular double sum of the
`[0,infinity]`-valued lattice maxima of the squared `(2,2)` error atoms. -/
def clauseOneTermOne (M : ABKModel d) (m : ℤ) (s : {s : ℝ // 0 < s})
    (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  ∑' j : {j : ℤ // j ≤ m}, ∑' n : {n : ℤ // n ≤ j.1 - 1},
    ENNReal.ofReal ((3 : ℝ) ^ (-(s : ℝ) * ((m - n.1 : ℤ) : ℝ))) *
      ⨆ v : ↥(Support.latticeAnnulusSet d n.1 j.1 (j.1 - 1)),
        ENNReal.ofReal (Support.annularErrorObservable M n.1 s
          (Cutoff.translateCutoffSample (Support.triadicLatticePoint n.1 v.1)
            omega) ^ 2)

def clauseOneTermThree (M : ABKModel d) (m : ℤ)
    (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  (∑' k : {k : ℤ // m ≤ k},
    ENNReal.ofReal ((3 : ℝ) ^ ((2 - M.gamma) * (m : ℝ))
      * Support.shellW1InfGradNorm m (omega.1 k.1))) ^ (2 : ℕ)

/-- The fourth right-hand term of clause (i): the `W^{2,infinity}` block sum. -/
def clauseOneTermFour (M : ABKModel d) (m : ℤ) (s : {s : ℝ // 0 < s})
    (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  ∑' n : {n : ℤ // n ≤ m},
    ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 2 : ℝ) * (s : ℝ) * ((m - n.1 : ℤ) : ℝ))) *
      ∑ k ∈ Finset.Icc (n.1 - 1) m,
        (ENNReal.ofReal ((3 : ℝ) ^ ((2 - M.gamma) * (k : ℝ))) *
          ⨆ v : ↥(Support.latticeCubeSet d k m),
            ENNReal.ofReal (Support.shellW2InfNormAt
              (Support.triadicLatticePoint k v.1) k (omega.1 k))) ^ (2 : ℕ)

/-! ## Part C -- the two provable dominations -/

/-- **The first term, from the atom-level slot.**  The real annular double sum of
`ClauseOne` is dominated by `clauseOneTermOne` as soon as each real atom family
value is dominated by the `[0,infinity]`-valued lattice supremum -- the only
genuinely missing direction, since a real supremum over a lattice index set has
no proved existence lemma. -/
theorem ofReal_annDouble_le_clauseOneTermOne (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) (omega : Cutoff.CutoffSample d) {E2 : ℤ → ℤ → ℝ}
    (hE0 : ∀ j n, 0 ≤ E2 j n)
    (hE2dom : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      ENNReal.ofReal (E2 j n)
        ≤ ⨆ v : ↥(Support.latticeAnnulusSet d n j (j - 1)),
            ENNReal.ofReal (Support.annularErrorObservable M n s
              (Cutoff.translateCutoffSample (Support.triadicLatticePoint n v.1)
                omega) ^ 2)) :
    ENNReal.ofReal
        (annDouble m
          (fun j n => (3 : ℝ) ^ (-((s : ℝ) * ((m - n : ℤ) : ℝ))) * E2 j n))
      ≤ clauseOneTermOne M m s omega := by
  refine ofReal_annDouble_le_ennDouble
    (h := fun j n => (3 : ℝ) ^ (-((s : ℝ) * ((m - n : ℤ) : ℝ))) * E2 j n)
    (H := fun j n => ENNReal.ofReal ((3 : ℝ) ^ (-(s : ℝ) * ((m - n : ℤ) : ℝ))) *
      ⨆ v : ↥(Support.latticeAnnulusSet d n j (j - 1)),
        ENNReal.ofReal (Support.annularErrorObservable M n s
          (Cutoff.translateCutoffSample (Support.triadicLatticePoint n v.1)
            omega) ^ 2))
    (fun j n => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hE0 j n))
    (fun j n hj hn => ?_)
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
    show -((s : ℝ) * ((m - n : ℤ) : ℝ)) = -(s : ℝ) * ((m - n : ℤ) : ℝ) from by ring]
  exact mul_le_mul_right (hE2dom j n hj hn) _

/-- **The third term, unconditionally.**  `ClauseOne`'s `gradTailSq` is the
square of a real `l^1` tail; `clauseOneTermThree` is the square of the same tail
formed in `[0,infinity]`, and `ofReal` under-approximates it with no summability
hypothesis. -/
theorem ofReal_gradTailSq_le_clauseOneTermThree (M : ABKModel d) (m : ℤ)
    (omega : Cutoff.CutoffSample d) :
    ENNReal.ofReal (gradTailSq M m omega) ≤ clauseOneTermThree M m omega := by
  have hnn : ∀ k : {k : ℤ // m ≤ k}, (0 : ℝ)
      ≤ (3 : ℝ) ^ ((2 - M.gamma) * (m : ℝ))
          * Support.shellW1InfGradNorm m (omega.1 k.1) :=
    fun k => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Support.shellW1InfGradNorm_nonneg _ _)
  have hsum0 : (0 : ℝ) ≤ ∑' k : {k : ℤ // m ≤ k},
      (3 : ℝ) ^ ((2 - M.gamma) * (m : ℝ))
        * Support.shellW1InfGradNorm m (omega.1 k.1) := tsum_nonneg hnn
  have htail := ofReal_tsum_le hnn
  show ENNReal.ofReal ((∑' k : {k : ℤ // m ≤ k},
      (3 : ℝ) ^ ((2 - M.gamma) * (m : ℝ))
        * Support.shellW1InfGradNorm m (omega.1 k.1)) ^ (2 : ℕ))
    ≤ (∑' k : {k : ℤ // m ≤ k},
        ENNReal.ofReal ((3 : ℝ) ^ ((2 - M.gamma) * (m : ℝ))
          * Support.shellW1InfGradNorm m (omega.1 k.1))) ^ (2 : ℕ)
  rw [ENNReal.ofReal_pow hsum0, pow_two, pow_two]
  exact mul_le_mul' htail htail

/-! ## Part D -- the literal-to-representative transfer of the left-hand side -/

/-- **The left-hand side, transferred.**  A uniform-in-`L` bound for the literal
squared flux-corrected error on the good event bounds the indicator of the
`[0,infinity]`-valued representative supremum, on the probability-one event where
literal and representative agree for every `L >= m`. -/
theorem indicator_observableSqSup_le [NeZero d] (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) {Event : Set (Cutoff.CutoffSample d)}
    {omega : Cutoff.CutoffSample d} {B : ℝ≥0∞}
    (hall : ∀ L : {L : ℤ // m ≤ L},
      Support.fluxCorrectedError M L.1 m (s : ℝ) omega
        = Support.fluxCorrectedErrorRepresentative M L.1 m s omega)
    (hb : omega ∈ Event → ∀ L : ℤ, m ≤ L →
      ENNReal.ofReal (Support.fluxCorrectedError M L m (s : ℝ) omega ^ 2) ≤ B) :
    Set.indicator Event (Support.fluxCorrectedErrorObservableSqSup M m s) omega
      ≤ B := by
  classical
  by_cases hmem : omega ∈ Event
  · rw [Set.indicator_of_mem hmem]
    show (⨆ L : {L : ℤ // m ≤ L},
        ENNReal.ofReal
          (Support.fluxCorrectedErrorRepresentative M L.1 m s omega ^ 2)) ≤ B
    refine iSup_le fun L => ?_
    exact le_of_eq_of_le
      (congrArg (fun x : ℝ => ENNReal.ofReal (x ^ 2)) (hall L)).symm
      (hb hmem L.1 L.2)
  · rw [Set.indicator_of_notMem hmem]
    exact zero_le

/-! ## Part E -- the assembled representative display -/

/-- **The clause-(i) display at the representative observables, almost surely.**

The pointwise literal chain of `ClauseOne` (hypothesis `hbound`, which
`clauseOne_bound` produces at each `L`) is transported to the
`[0,infinity]`-valued, almost-sure, representative-side display carried by the
Section 4.1 statement.

Named slots, with their recorded gaps:

* `hbound` -- the pointwise chain; every input of `clauseOne_bound`;
* `hE2dom` -- domination of the real `(2,2)`-atom family by the `[0,infinity]`-valued
  lattice-annulus supremum;
* `hG1bdom` -- domination of `ClauseOne`'s single shell sum by the display's
  `n`-then-`k` double block sum. -/
theorem clauseOne_representative_display [NeZero d] (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) (Event : Set (Cutoff.CutoffSample d)) {C : ℝ}
    {E2 : Cutoff.CutoffSample d → ℤ → ℤ → ℝ} {A : Cutoff.CutoffSample d → ℤ → ℝ}
    (hC0 : 0 ≤ C)
    (hE0 : ∀ omega j n, 0 ≤ E2 omega j n)
    (hbound : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∈ Event → ∀ L : ℤ, m ≤ L →
        IsClauseOneBound (Support.fluxCorrectedError M L m (s : ℝ) omega ^ 2)
          (annDouble m (fun j n =>
            (3 : ℝ) ^ (-((s : ℝ) * ((m - n : ℤ) : ℝ))) * E2 omega j n))
          (M.gamma ^ 2 * |Real.log M.gamma| ^ 4) (gradTailSq M m omega)
          (∑' v : ℕ, (3 : ℝ) ^ (-((s : ℝ) / 2) * (v : ℝ)) * A omega (m - (v : ℤ)) ^ 2)
          (s : ℝ) (Disorder.cstar M) M.gamma C)
    (hE2dom : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
        ENNReal.ofReal (E2 omega j n)
          ≤ ⨆ v : ↥(Support.latticeAnnulusSet d n j (j - 1)),
              ENNReal.ofReal (Support.annularErrorObservable M n s
                (Cutoff.translateCutoffSample
                  (Support.triadicLatticePoint n v.1) omega) ^ 2))
    (hG1bdom : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ENNReal.ofReal
          (∑' v : ℕ, (3 : ℝ) ^ (-((s : ℝ) / 2) * (v : ℝ)) * A omega (m - (v : ℤ)) ^ 2)
        ≤ clauseOneTermFour M m s omega) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Set.indicator Event (Support.fluxCorrectedErrorObservableSqSup M m s) omega
        ≤ ENNReal.ofReal (C * (s : ℝ)) * clauseOneTermOne M m s omega
          + ENNReal.ofReal (C * ((s : ℝ)⁻¹ ^ (3 : ℕ))
              * ((Disorder.cstar M)⁻¹ ^ (4 : ℕ)) * M.gamma ^ 2
              * |Real.log M.gamma| ^ 4)
          + ENNReal.ofReal (C * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹
              * M.gamma) * clauseOneTermThree M m omega
          + ENNReal.ofReal (C * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹
              * M.gamma) * clauseOneTermFour M m s omega := by
  have hgam0 : (0 : ℝ) ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcsinv : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ := inv_nonneg.2 hcs0.le
  filter_upwards [hbound, hE2dom, hG1bdom,
    Support.ae_forall_fluxCorrectedError_eq_representative M m s]
    with omega hb hdom1 hdom4 hall
  refine indicator_observableSqSup_le M m s hall ?_
  intro hmem L hL
  -- abbreviations for the four right-hand contents
  set G2 : ℝ := annDouble m (fun j n =>
    (3 : ℝ) ^ (-((s : ℝ) * ((m - n : ℤ) : ℝ))) * E2 omega j n) with hG2def
  set G1b : ℝ :=
    ∑' v : ℕ, (3 : ℝ) ^ (-((s : ℝ) / 2) * (v : ℝ)) * A omega (m - (v : ℤ)) ^ 2
    with hG1bdef
  have hG20 : (0 : ℝ) ≤ G2 := by
    rw [hG2def]
    exact annDouble_nonneg fun j n =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hE0 omega j n)
  have hG1b0 : (0 : ℝ) ≤ G1b := by
    rw [hG1bdef]
    exact tsum_nonneg fun v =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (sq_nonneg _)
  have hG1a0 : (0 : ℝ) ≤ gradTailSq M m omega := gradTailSq_nonneg M m omega
  have hRem0 : (0 : ℝ) ≤ M.gamma ^ 2 * |Real.log M.gamma| ^ 4 := by positivity
  have hc1 : (0 : ℝ) ≤ C * (s : ℝ) := mul_nonneg hC0 s.2.le
  have hc2 : (0 : ℝ) ≤ C * ((s : ℝ)⁻¹ ^ (3 : ℕ)) * ((Disorder.cstar M)⁻¹ ^ (4 : ℕ)) := by
    have hs0 : (0 : ℝ) ≤ (s : ℝ)⁻¹ := inv_nonneg.2 s.2.le
    positivity
  have hc3 : (0 : ℝ) ≤ C * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma := by
    have hs0 : (0 : ℝ) ≤ (s : ℝ)⁻¹ := inv_nonneg.2 s.2.le
    positivity
  -- the four real terms
  have hT1 : (0 : ℝ) ≤ C * (s : ℝ) * G2 := mul_nonneg hc1 hG20
  have hT2 : (0 : ℝ) ≤ C * ((s : ℝ)⁻¹ ^ (3 : ℕ)) * ((Disorder.cstar M)⁻¹ ^ (4 : ℕ))
      * (M.gamma ^ 2 * |Real.log M.gamma| ^ 4) := mul_nonneg hc2 hRem0
  have hT3 : (0 : ℝ) ≤ C * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma
      * gradTailSq M m omega := mul_nonneg hc3 hG1a0
  have hT4 : (0 : ℝ) ≤ C * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma
      * G1b := mul_nonneg hc3 hG1b0
  have hreal := hb hmem L hL
  unfold IsClauseOneBound at hreal
  refine le_trans (ENNReal.ofReal_le_ofReal hreal) ?_
  rw [ENNReal.ofReal_add (by linarith only [hT1, hT2, hT3]) hT4,
    ENNReal.ofReal_add (by linarith only [hT1, hT2]) hT3,
    ENNReal.ofReal_add hT1 hT2]
  refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
  · rw [ENNReal.ofReal_mul hc1]
    refine mul_le_mul_right ?_ _
    rw [hG2def]
    exact ofReal_annDouble_le_clauseOneTermOne M m s omega (hE0 omega) hdom1
  · refine le_of_eq (congrArg ENNReal.ofReal ?_)
    ring
  · rw [ENNReal.ofReal_mul hc3]
    exact mul_le_mul_right (ofReal_gradTailSq_le_clauseOneTermThree M m omega) _
  · rw [ENNReal.ofReal_mul hc3]
    refine mul_le_mul_right ?_ _
    rw [hG1bdef]
    exact hdom4

end

end Algsuperdiff.Section4.Provider.Annular
