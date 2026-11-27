/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageWeights
public import LeanPool.KLRandomness.StageCandidate
public import LeanPool.KLRandomness.PoolAdviceComputable
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Computable rational support wagers at a finite horizon

The analytic support sum is evaluated on a finite answer transcript. Its
executable form uses the candidate's Boolean mask and the actual finite pool
list, so no support-membership oracle is supplied to the stage algorithm.
The rational signed wagers are exactly those of the normalized strategies.
-/

@[expose] public section

namespace Klr.StageFiniteWager

open MeasureTheory RationalComputability
open scoped BigOperators

/-- The signed rational wager underlying the actual normalized strategy. -/
noncomputable def normalizedWager (s : BettingStrategy) : List Bool → ℚ :=
  (CapitalApproximation.ofComputable s.capital s.computable_capital).reserve.normalizedFraction

theorem computable_normalizedWager (s : BettingStrategy) : Computable (normalizedWager s) := by
  let R := (CapitalApproximation.ofComputable s.capital s.computable_capital).reserve
  have hv : Computable R.variation :=
    Computable.fst.comp (Computable.snd.comp R.computable_normalizationAccount)
  exact (primrec_rat_div.to_comp.comp R.computable_wager
    (primrec_rat_mul.to_comp.comp (Computable.const 2)
      (primrec_rat_add.to_comp.comp (Computable.const 1) hv))).of_eq fun _ => rfl

theorem cast_normalizedWager (s : BettingStrategy) (v : List Bool) :
    (normalizedWager s v : ℝ) = s.normalize.capital.wager v :=
  (ReservedRationalCapital.normalizedCapital_wager _ v).symm

theorem normalizedWager_abs_le_half (s : BettingStrategy) (v : List Bool) :
    |(normalizedWager s v : ℝ)| ≤ 1 / 2 := by
  rw [cast_normalizedWager]
  exact s.normalize_wager_abs_le_half v

/-- Total absolute wager placed inside a support while reading a finite
answer transcript. The summation uses only proper prefixes of that transcript. -/
def truncated (π : ScanRule) (h : List Bool → ℚ) (S : Finset ℕ) (v : List Bool) : ℚ :=
  ∑ t ∈ Finset.range v.length, if π.query (v.take t) ∈ S then |h (v.take t)| else 0

theorem truncated_nonneg (π : ScanRule) (h : List Bool → ℚ) (S : Finset ℕ) (v : List Bool) :
    0 ≤ truncated π h S v :=
  Finset.sum_nonneg fun t _ => by split_ifs <;> positivity

theorem cast_truncated_nonneg (π : ScanRule) (h : List Bool → ℚ)
    (S : Finset ℕ) (v : List Bool) : 0 ≤ (truncated π h S v : ℝ) :=
  Rat.cast_nonneg.mpr (truncated_nonneg π h S v)

/-- Exact agreement with the actual wagers on the first `V` adaptive queries. -/
theorem cast_truncated_transcript (π : ScanRule) (h : List Bool → ℚ)
    (S : Finset ℕ) (X : Cantor) (V : ℕ) :
    (truncated π h S (π.transcript X V) : ℝ) =
      ∑ t ∈ Finset.range V,
        if π.query (π.transcript X t) ∈ S then |(h (π.transcript X t) : ℝ)| else 0 := by
  unfold truncated
  push_cast
  rw [π.length_transcript]
  apply Finset.sum_congr rfl
  intro t ht
  rw [π.transcript_take X (Finset.mem_range.mp ht).le]
  split_ifs <;> simp

/-- The real finite-horizon objective is measurable on actual inputs. -/
theorem measurable_truncated (π : ScanRule) (h : List Bool → ℚ) (S : Finset ℕ) (V : ℕ) :
    Measurable (fun X => (truncated π h S (π.transcript X V) : ℝ)) :=
  DropEvents.measurable_transcript_eval π V (fun v => (truncated π h S v : ℝ))

theorem truncated_transcript_le_half_horizon (π : ScanRule) (h : List Bool → ℚ)
    (S : Finset ℕ) (X : Cantor) (V : ℕ)
    (hh : ∀ v, |(h v : ℝ)| ≤ 1 / 2) :
    (truncated π h S (π.transcript X V) : ℝ) ≤ (V : ℝ) / 2 := by
  rw [cast_truncated_transcript]
  calc
    _ ≤ ∑ _t ∈ Finset.range V, (1 / 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro t _
      split_ifs
      · exact hh _
      · norm_num
    _ = _ := by simp [div_eq_mul_inv]

/-- Truncation is bounded by the all-time support total used in candidate selection. -/
theorem truncated_transcript_le_supportWager (π : ScanRule) (h : List Bool → ℚ)
    (S : Finset ℕ) (X : Cantor) (V : ℕ) :
    (truncated π h S (π.transcript X V) : ℝ) ≤
      StageWeights.supportWager π (fun v => (h v : ℝ)) S X := by
  rw [cast_truncated_transcript]
  exact StageWeights.partial_supportWager_le π (fun v => (h v : ℝ)) S X V

/-- The finite rational objective dominates the actual early forced wagers. -/
theorem earlyWager_le_truncated (B : ℕ → AffineBlock) (π : ScanRule)
    (h : List Bool → ℚ) (V : ℕ → ℕ) (j : ℕ) (X : Cantor) :
    EarlyLateWagers.earlyWager B π (fun v => (h v : ℝ)) V j X ≤
      (truncated π h (B j).support (π.transcript X (V j)) : ℝ) := by
  rw [cast_truncated_transcript]
  exact StageWeights.earlyWager_le_partial_supportWager B π (fun v => (h v : ℝ)) V j X

/-- Executable form with an arbitrary Boolean support test. -/
def truncatedWith (q : List Bool → ℕ) (h : List Bool → ℚ)
    (selected : ℕ → Bool) (v : List Bool) : ℚ :=
  ((List.range v.length).map
    (fun t => if selected (q (v.take t)) then |h (v.take t)| else 0)).sum

theorem truncatedWith_eq_truncated (π : ScanRule) (h : List Bool → ℚ)
    (selected : ℕ → Bool) (S : Finset ℕ)
    (hs : ∀ a, selected a = true ↔ a ∈ S) (v : List Bool) :
    truncatedWith π.query h selected v = truncated π h S v := by
  rw [truncatedWith, ← List.sum_toFinset _ (List.nodup_range (n := v.length))]
  simp only [List.toFinset_range, truncated, hs]

/-- All finite parameters may vary computably, including the support test
and the wager function. No global effective enumeration of all scans is assumed. -/
theorem computable_truncatedWith {α : Type*} [Primcodable α]
    {q : α → List Bool → ℕ} {h : α → List Bool → ℚ}
    {selected : α → ℕ → Bool} {v : α → List Bool}
    (hq : Computable₂ q) (hh : Computable₂ h) (hs : Computable₂ selected)
    (hv : Computable v) :
    Computable (fun a => truncatedWith (q a) (h a) (selected a) (v a)) := by
  have hp : Computable (fun p : α × ℕ => (v p.1).take p.2) :=
    Primrec.list_take.to_comp.comp Computable.snd (hv.comp Computable.fst)
  have hg : Computable (fun p : α × ℕ => selected p.1 (q p.1 ((v p.1).take p.2))) :=
    hs.comp Computable.fst (hq.comp Computable.fst hp)
  have hw : Computable (fun p : α × ℕ => |h p.1 ((v p.1).take p.2)|) :=
    PoolAdvice.computable_rat_abs.comp (hh.comp Computable.fst hp)
  exact (PoolAdvice.computable_list_sum
    (l := fun a => List.range (v a).length)
    (f := fun a t => _root_.cond (selected a (q a ((v a).take t))) |h a ((v a).take t)| 0)
    (Primrec.list_range.to_comp.comp (Computable.list_length.comp hv))
    (Computable.cond hg hw (Computable.const (0 : ℚ)))).of_eq fun _ => by
      simp only [truncatedWith, Bool.cond_eq_ite]

/-- Decide whether an actual input position lies in the candidate support,
using only the finite pool and the executable Boolean mask. -/
def selected (G : List ℕ) (a : SparseListSearch.Entry) (n : ℕ) : Bool :=
  (List.range G.length).any
    (fun j => a.1.getD j false && decide (G.getD j 0 = n))

theorem selected_eq_true (G : List ℕ) (a : SparseListSearch.Entry) (n : ℕ) :
    selected G a n = true ↔
      n ∈ (SparseListWeights.support G.length a).image G.get := by
  rw [selected, List.any_eq_true]
  constructor
  · rintro ⟨j, hj, h⟩
    have hj' := List.mem_range.mp hj
    simp only [Bool.and_eq_true] at h
    obtain ⟨hm, hn⟩ := h
    refine Finset.mem_image.mpr ⟨⟨j, hj'⟩, ?_, ?_⟩
    · exact (SparseListCode.mem_maskSet G.length a.1 ⟨j, hj'⟩).mpr hm
    · exact (List.getD_eq_get G 0 ⟨j, hj'⟩).symm.trans (of_decide_eq_true hn)
  · intro hn
    obtain ⟨j, hj, hjn⟩ := Finset.mem_image.mp hn
    refine ⟨j.val, List.mem_range.mpr j.isLt, ?_⟩
    simp only [Bool.and_eq_true]
    constructor
    · exact (SparseListCode.mem_maskSet G.length a.1 j).mp hj
    · apply decide_eq_true_eq.mpr
      exact (List.getD_eq_get G 0 j).trans hjn

theorem computable_selected {α : Type*} [Primcodable α]
    {G : α → List ℕ} {a : α → SparseListSearch.Entry} {n : α → ℕ}
    (hG : Computable G) (ha : Computable a) (hn : Computable n) :
    Computable (fun p => selected (G p) (a p) (n p)) := by
  have hm := (Primrec.list_getD false).to_comp.comp
    (Computable.fst.comp (ha.comp Computable.fst)) Computable.snd
  have hg := (Primrec.list_getD 0).to_comp.comp (hG.comp Computable.fst) Computable.snd
  have he := Primrec.eq.decide.to_comp.comp hg (hn.comp Computable.fst)
  exact SparseSearch.computable_list_any
    (Primrec.list_range.to_comp.comp (Computable.list_length.comp hG))
    (Primrec.and.to_comp.comp hm he)

/-- The finite rational cost evaluated directly from the actual pool and candidate code. -/
def truncatedCandidate (π : ScanRule) (h : List Bool → ℚ)
    (G : List ℕ) (a : SparseListSearch.Entry) (v : List Bool) : ℚ :=
  truncatedWith π.query h (selected G a) v

theorem truncatedCandidate_eq_truncated (π : ScanRule) (h : List Bool → ℚ)
    (G : List ℕ) (a : SparseListSearch.Entry) (v : List Bool) :
    truncatedCandidate π h G a v =
      truncated π h ((SparseListWeights.support G.length a).image G.get) v :=
  truncatedWith_eq_truncated π h (selected G a) _ (selected_eq_true G a) v

theorem computable_truncatedCandidate (π : ScanRule) (h : List Bool → ℚ)
    (hh : Computable h) {α : Type*} [Primcodable α]
    {G : α → List ℕ} {a : α → SparseListSearch.Entry} {v : α → List Bool}
    (hG : Computable G) (ha : Computable a) (hv : Computable v) :
    Computable (fun p => truncatedCandidate π h (G p) (a p) (v p)) :=
  computable_truncatedWith (π.computable_query.comp Computable.snd)
    (hh.comp Computable.snd)
    (computable_selected (hG.comp Computable.fst) (ha.comp Computable.fst) Computable.snd)
    hv

/-- The executable candidate evaluation is exactly the finite cost on its
embedded affine block, independently of the block's syndrome. -/
theorem truncatedCandidate_eq_block (π : ScanRule) (h : List Bool → ℚ)
    (G : List ℕ) (hG : G.Nodup) {m r : ℕ} (a : SparseListSearch.Entry)
    (ha : SparseListSearch.GoodEntry G.length m r a) (y : Fin r → ZMod 2)
    (v : List Bool) :
    truncatedCandidate π h G a v =
      truncated π h (StageCandidate.block G.get hG.injective_get a ha y).support v :=
  truncatedCandidate_eq_truncated π h G a v

/-- The actual normalized rational wager needs no extra effectivity premise. -/
theorem computable_normalized_truncatedCandidate (s : BettingStrategy)
    {α : Type*} [Primcodable α]
    {G : α → List ℕ} {a : α → SparseListSearch.Entry} {v : α → List Bool}
    (hG : Computable G) (ha : Computable a) (hv : Computable v) :
    Computable (fun p =>
      truncatedCandidate s.normalize.scan (normalizedWager s) (G p) (a p) (v p)) :=
  computable_truncatedCandidate s.normalize.scan (normalizedWager s)
    (computable_normalizedWager s) hG ha hv

end Klr.StageFiniteWager
