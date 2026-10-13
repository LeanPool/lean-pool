/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.MarkovProcess.MarkovProcess.Path.RelativeHitting
public import LeanPool.Superdiffusion.Algsuperdiff.Process.Trajectory.ExitTimeChaining

/-!
# HitExitChaining

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Chaining a hit with the subsequent exit

This module builds one restart step from two successive events: first hit a member of a
countable family of closed sets, then exit the corresponding open enlargement.  Entrance into a
closed set `D` is represented by the exit time from the open complement `Dᶜ`.  This closedness is
essential: entrance times of general open sets need not be stopping times for the raw canonical
filtration, and a continuous path first entering an open set need only land in its closure.

Accordingly, the union of the small sets is assumed closed and the enlarged sets `V' i` are
open; each individual `V i` need only be measurable, the intended use being closed sets with
`V i ⊆ V' i`.  Closedness of the union is deliberately a separate hypothesis; it does not follow
for an arbitrary infinite family.  At a finite hitting time the path lies in the selected `V i`
itself, not merely its closure.  Reaching a cemetery point outside an enlargement counts as an
exit.

Public declarations:

* `ContinuousPath.hitTime`;
* `ContinuousPath.familyIndex`;
* `ContinuousPath.hitExitTime`;
* `ContinuousPath.measurable_familyIndex`;
* `ContinuousPath.familyIndex_mem_of_mem_iUnion`;
* `ContinuousPath.coordinate_hitTime_mem`;
* `ContinuousPath.isStoppingTime_hitExitTime`;
* `ContinuousPath.visited_before_iterated_subset`;
* `ContinuousPath.iteratedStoppingTime_hitExit_le_exitTime_of_visits`;
* `IsConservative.lintegral_exp_neg_exitTime_le_rho_pow_hitExit_of_cover`;
* `IsConservative.lintegral_exp_neg_exitTime_le_rho_pow_hitExit`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

open MarkovProcess

namespace Algsuperdiff.Process

noncomputable section

namespace ContinuousPath

open MarkovProcess.ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]

/-- The first entrance time into `D`, represented as the exit time from its complement. -/
def hitTime (D : Set alpha) (omega : ContinuousPath alpha) : ℝ≥0∞ :=
  exitTime Dᶜ omega

open Classical in
/-- The least member of a countable family containing `a`, with value zero off the union. -/
def familyIndex (V : ℕ → Set alpha) (a : alpha) : ℕ :=
  if h : ∃ i, a ∈ V i then Nat.find h else 0

/-- First hit the closed family, then exit the open enlargement selected at the hitting state. -/
def hitExitTime (V V' : ℕ → Set alpha) (omega : ContinuousPath alpha) : ℝ≥0∞ :=
  let T := (hitTime (⋃ i, V i) omega).untopD 0
  hitTime (⋃ i, V i) omega + exitTime (V' (familyIndex V (omega T))) (shift T omega)

variable [MeasurableSpace alpha]

omit [PseudoMetricSpace alpha] in
/-- The least-index selector of a measurable countable family is measurable. -/
theorem measurable_familyIndex (V : ℕ → Set alpha) (hV : ∀ i, MeasurableSet (V i)) :
    Measurable (familyIndex V) := by
  classical
  let p : alpha → ℕ → Prop := fun a i ↦ a ∈ V i ∨ (a ∉ ⋃ j, V j ∧ i = 0)
  have hp : ∀ a, ∃ i, p a i := by
    intro a
    by_cases ha : a ∈ ⋃ i, V i
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
      exact ⟨i, Or.inl hi⟩
    · exact ⟨0, Or.inr ⟨ha, rfl⟩⟩
  have hpMeas : ∀ i, MeasurableSet {a | p a i} := by
    intro i
    change MeasurableSet (V i ∪ ((⋃ j, V j)ᶜ ∩ {a : alpha | i = 0}))
    exact (hV i).union ((MeasurableSet.iUnion hV).compl.inter (MeasurableSet.const _))
  have hfind : Measurable (fun a ↦ Nat.find (hp a)) := measurable_find hp hpMeas
  have heq : familyIndex V = fun a ↦ Nat.find (hp a) := by
    funext a
    rw [familyIndex]
    by_cases ha : ∃ i, a ∈ V i
    · rw [dite_eq_left ha]
      have haUnion : a ∈ ⋃ i, V i := by simpa only [Set.mem_iUnion] using ha
      apply Nat.find_congr'
      intro i
      simp only [p, haUnion, not_true_eq_false, false_and, or_false]
    · rw [dite_eq_right ha]
      symm
      apply (Nat.find_eq_zero (hp a)).mpr
      exact Or.inr ⟨by simpa only [Set.mem_iUnion, not_exists] using ha, rfl⟩
  rw [heq]
  exact hfind

omit [PseudoMetricSpace alpha] [MeasurableSpace alpha] in
/-- A point in the union belongs to the family member selected by `familyIndex`. -/
theorem familyIndex_mem_of_mem_iUnion (V : ℕ → Set alpha) {a : alpha}
    (ha : a ∈ ⋃ i, V i) : a ∈ V (familyIndex V a) := by
  classical
  have hex : ∃ i, a ∈ V i := by simpa only [Set.mem_iUnion] using ha
  rw [familyIndex, dite_eq_left hex]
  exact Nat.find_spec hex

omit [MeasurableSpace alpha] in
/-- At a finite entrance time into a closed set, the path lies in that set. -/
theorem coordinate_hitTime_mem (D : Set alpha) (hD : IsClosed D) (omega : ContinuousPath alpha)
    (hfin : hitTime D omega ≠ ⊤) : omega ((hitTime D omega).untopD 0) ∈ D := by
  by_cases h0 : omega 0 ∈ D
  · have hle : hitTime D omega ≤ 0 :=
      exitTime_le_of_notMem Dᶜ omega 0 (by simpa only [Set.mem_compl_iff, not_not] using h0)
    have hzero : hitTime D omega = 0 := le_antisymm hle bot_le
    rw [hzero]
    exact h0
  · have hfront : omega ((hitTime D omega).untopD 0) ∈ frontier Dᶜ := by
      exact coordinate_exitTime_mem_frontier Dᶜ hD.isOpen_compl omega
        (by simpa only [Set.mem_compl_iff] using h0)
        hfin
    rw [frontier_compl] at hfront
    exact hD.frontier_subset hfront

omit [MeasurableSpace alpha] in
private theorem hitTime_add_exitTime_shift_le_iff_hitsSetBetween
    (T : ContinuousPath alpha → ℝ≥0∞) (U : Set alpha) (hU : IsOpen U)
    (omega : ContinuousPath alpha) (t : NNReal) :
    T omega + exitTime U (shift ((T omega).untopD 0) omega) ≤ (t : ℝ≥0∞) ↔
      T omega ≤ (t : ℝ≥0∞) ∧ omega ∈ hitsSetBetween T t Uᶜ := by
  constructor
  · intro hsum
    have hTt : T omega ≤ (t : ℝ≥0∞) :=
      (le_add_right (le_refl (T omega))).trans hsum
    refine ⟨hTt, ?_⟩
    have hTne : T omega ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hTt
    lift T omega to NNReal using hTne with a ha
    have hat : a ≤ t := WithTop.coe_le_coe.mp hTt
    have hsum' : (a : ℝ≥0∞) + exitTime U (shift a omega) ≤ (t : ℝ≥0∞) := hsum
    have hexit : exitTime U (shift a omega) ≤ ((t - a : NNReal) : ℝ≥0∞) := by
      rw [ENNReal.coe_sub]
      exact ENNReal.le_sub_of_add_le_left WithTop.coe_ne_top hsum'
    obtain ⟨q, hq⟩ := (exitTime_le_iff_mem_hitsSetBy U hU (t - a) (shift a omega)).mp hexit
    refine ⟨a + q, ?_, ?_, ?_⟩
    · simpa only [ha, ENNReal.coe_add] using
        (show (a : ℝ≥0∞) ≤ ((a + q : NNReal) : ℝ≥0∞) from
          WithTop.coe_le_coe.mpr le_self_add)
    · calc
        a + q ≤ a + (t - a) := add_le_add le_rfl q.property
        _ = t := add_tsub_cancel_of_le hat
    · simpa only [Set.mem_compl_iff, shift_apply] using hq
  · rintro ⟨hTt, s, hTs, hst, hsU⟩
    have hTne : T omega ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hTt
    lift T omega to NNReal using hTne with a ha
    have has : a ≤ s := WithTop.coe_le_coe.mp hTs
    have hbad : shift a omega (s - a) ∉ U := by
      rw [shift_apply, add_tsub_cancel_of_le has]
      simpa only [Set.mem_compl_iff] using hsU
    have hexit : exitTime U (shift a omega) ≤ ((s - a : NNReal) : ℝ≥0∞) :=
      exitTime_le_of_notMem U (shift a omega) (s - a) hbad
    change (a : ℝ≥0∞) + exitTime U (shift a omega) ≤ (t : ℝ≥0∞)
    calc
      (a : ℝ≥0∞) + exitTime U (shift a omega) ≤
          (a : ℝ≥0∞) + ((s - a : NNReal) : ℝ≥0∞) := add_le_add le_rfl hexit
      _ = (s : ℝ≥0∞) := by rw [← ENNReal.coe_add, add_tsub_cancel_of_le has]
      _ ≤ (t : ℝ≥0∞) := WithTop.coe_le_coe.mpr hst

variable [SecondCountableTopology alpha] [BorelSpace alpha]

/-- The composite hit-then-exit rule is a stopping time when the hit sets are measurable with a
closed union and each enlargement is open. -/
theorem isStoppingTime_hitExitTime
    (V V' : ℕ → Set alpha) (hVmeasurable : ∀ i, MeasurableSet (V i))
    (hDclosed : IsClosed (⋃ i, V i)) (hV'open : ∀ i, IsOpen (V' i)) :
    IsStoppingTime (canonicalFiltration (alpha := alpha)) (hitExitTime V V') := by
  let D : Set alpha := ⋃ i, V i
  let T : ContinuousPath alpha → ℝ≥0∞ := hitTime D
  let idx : ContinuousPath alpha → ℕ :=
    fun omega ↦ familyIndex V (omega ((T omega).untopD 0))
  have hT : IsStoppingTime (canonicalFiltration (alpha := alpha)) T := by
    simpa only [T, hitTime] using! isStoppingTime_exitTime Dᶜ hDclosed.isOpen_compl
  have hIdx : Measurable[hT.measurableSpace] idx :=
    (measurable_familyIndex V hVmeasurable).comp
      (measurable_eval_untopD_stoppingTime_stopped T hT)
  intro t
  have hevent : {omega : ContinuousPath alpha | hitExitTime V V' omega ≤ (t : ℝ≥0∞)} =
      ⋃ i : ℕ, ({omega | idx omega = i} ∩ {omega | T omega ≤ (t : ℝ≥0∞)}) ∩
        hitsSetBetween T t (V' i)ᶜ := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    change
      T omega + exitTime (V' (idx omega)) (shift ((T omega).untopD 0) omega) ≤
          (t : ℝ≥0∞) ↔ _
    constructor
    · intro h
      obtain ⟨hTt, hhit⟩ :=
        (hitTime_add_exitTime_shift_le_iff_hitsSetBetween T (V' (idx omega))
          (hV'open (idx omega)) omega t).mp h
      exact ⟨idx omega, ⟨rfl, hTt⟩, hhit⟩
    · rintro ⟨i, ⟨hidx, hTt⟩, hhit⟩
      rw [hidx]
      exact (hitTime_add_exitTime_shift_le_iff_hitsSetBetween T (V' i) (hV'open i)
        omega t).mpr ⟨hTt, hhit⟩
  have hright : MeasurableSet[canonicalFiltration (alpha := alpha) t]
      (⋃ i : ℕ, ({omega | idx omega = i} ∩ {omega | T omega ≤ (t : ℝ≥0∞)}) ∩
        hitsSetBetween T t (V' i)ᶜ) := by
    refine MeasurableSet.iUnion fun i ↦ MeasurableSet.inter ?_ ?_
    · have hi : MeasurableSet[hT.measurableSpace] {omega | idx omega = i} :=
        hIdx (measurableSet_singleton i)
      exact hi.2 t
    · exact measurableSet_hitsSetBetween T hT t (V' i)ᶜ (hV'open i).isClosed_compl
  exact hevent ▸ hright

end ContinuousPath

namespace ContinuousPath

open MarkovProcess.ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]

private theorem visited_before_hitExitTime_subset (V V' : ℕ → Set alpha)
    (omega : ContinuousPath alpha) :
    {j | ∃ t : NNReal, (t : ℝ≥0∞) < hitExitTime V V' omega ∧ omega t ∈ V j} ⊆
      {j | (V j ∩ V' (familyIndex V
        (omega ((hitTime (⋃ i, V i) omega).untopD 0)))).Nonempty} := by
  intro j hj
  obtain ⟨t, ht, hjV⟩ := hj
  let D : Set alpha := ⋃ i, V i
  let T : ContinuousPath alpha → ℝ≥0∞ := hitTime D
  let idx : ℕ := familyIndex V (omega ((T omega).untopD 0))
  have hjD : omega t ∈ D := by
    exact Set.mem_iUnion.mpr ⟨j, hjV⟩
  have hTt : T omega ≤ (t : ℝ≥0∞) :=
    exitTime_le_of_notMem Dᶜ omega t (by
      simpa only [Set.mem_compl_iff, not_not] using hjD)
  have hTne : T omega ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hTt
  lift T omega to NNReal using hTne with a ha
  have hUntopA : (a : ℝ≥0∞).untopD 0 = a := rfl
  have hat : a ≤ t := WithTop.coe_le_coe.mp hTt
  have ht' : (t : ℝ≥0∞) <
      (a : ℝ≥0∞) + exitTime (V' idx) (shift a omega) := by
    have ht' := ht
    change (t : ℝ≥0∞) < T omega +
      exitTime (V' idx) (shift ((T omega).untopD 0) omega) at ht'
    rw [← ha, hUntopA] at ht'
    exact ht'
  have hremain : ((t - a : NNReal) : ℝ≥0∞) <
      exitTime (V' idx) (shift a omega) := by
    by_contra hnot
    have hle : exitTime (V' idx) (shift a omega) ≤
        ((t - a : NNReal) : ℝ≥0∞) := le_of_not_gt hnot
    have hsum : (a : ℝ≥0∞) + exitTime (V' idx) (shift a omega) ≤
        (t : ℝ≥0∞) := by
      calc
        (a : ℝ≥0∞) + exitTime (V' idx) (shift a omega) ≤
            (a : ℝ≥0∞) + ((t - a : NNReal) : ℝ≥0∞) := add_le_add le_rfl hle
        _ = (t : ℝ≥0∞) := by
          rw [← ENNReal.coe_add, add_tsub_cancel_of_le hat]
    exact (not_le_of_gt ht') hsum
  have hstay : shift a omega (t - a) ∈ V' idx :=
    mem_of_lt_exitTime (V' idx) (shift a omega) (t - a) hremain
  rw [shift_apply, add_tsub_cancel_of_le hat] at hstay
  exact ⟨omega t, hjV, by simpa only [D, T, idx] using hstay⟩

/-- The hit sets visited before the first `k` composite cycles fit in a finite set of at most
`k * K` indices when each selected enlargement meets at most `K` hit sets. -/
theorem visited_before_iterated_subset (V V' : ℕ → Set alpha) (K : ℕ)
    (hoverlap : ∀ i, ∃ s : Finset ℕ,
      s.card ≤ K ∧ ∀ j, (V j ∩ V' i).Nonempty → j ∈ s)
    (k : ℕ) (omega : ContinuousPath alpha) :
    ∃ s : Finset ℕ, s.card ≤ k * K ∧ ∀ j,
      (∃ t : NNReal,
        (t : ℝ≥0∞) < iteratedStoppingTime (hitExitTime V V') k omega ∧ omega t ∈ V j) →
          j ∈ s := by
  induction k generalizing omega with
  | zero =>
      refine ⟨∅, by simp only [Finset.card_empty, zero_mul, le_refl], fun j hj ↦ ?_⟩
      obtain ⟨t, ht, _⟩ := hj
      simp only [iteratedStoppingTime] at ht
      exact (not_lt_of_ge bot_le ht).elim
  | succ k ih =>
      obtain ⟨sold, hcardOld, hold⟩ := ih omega
      by_cases htop : iteratedStoppingTime (hitExitTime V V') k omega = ⊤
      · refine ⟨sold, hcardOld.trans ?_, fun j hj ↦ hold j ?_⟩
        · exact Nat.mul_le_mul_right K (Nat.le_add_right k 1)
        · obtain ⟨t, ht, hjV⟩ := hj
          exact ⟨t, by rw [htop]; exact WithTop.coe_lt_top t, hjV⟩
      · lift iteratedStoppingTime (hitExitTime V V') k omega to NNReal using htop with a ha
        let eta : ContinuousPath alpha := shift a omega
        let T : ContinuousPath alpha → ℝ≥0∞ := hitTime (⋃ i, V i)
        let idx : ℕ := familyIndex V (eta ((T eta).untopD 0))
        obtain ⟨snew, hcardNew, hnew⟩ := hoverlap idx
        refine ⟨sold ∪ snew, ?_, fun j hj ↦ ?_⟩
        · calc
            (sold ∪ snew).card ≤ sold.card + snew.card := Finset.card_union_le _ _
            _ ≤ k * K + K := Nat.add_le_add hcardOld hcardNew
            _ = (k + 1) * K := by rw [Nat.add_mul, one_mul]
        · obtain ⟨t, ht, hjV⟩ := hj
          by_cases htold : (t : ℝ≥0∞) <
              iteratedStoppingTime (hitExitTime V V') k omega
          · have htold' : (t : ℝ≥0∞) < (a : ℝ≥0∞) := by
              rw [ha]
              exact htold
            exact Finset.mem_union_left snew (hold j ⟨t, htold', hjV⟩)
          · have hlea : (a : ℝ≥0∞) ≤ (t : ℝ≥0∞) := by
              rw [ha]
              exact le_of_not_gt htold
            have hat : a ≤ t := WithTop.coe_le_coe.mp hlea
            have hUntopA : (a : ℝ≥0∞).untopD 0 = a := rfl
            have ht' : (t : ℝ≥0∞) <
                (a : ℝ≥0∞) + hitExitTime V V' eta := by
              have ht' := ht
              rw [iteratedStoppingTime_succ', ← ha, hUntopA] at ht'
              exact ht'
            have hremain : ((t - a : NNReal) : ℝ≥0∞) < hitExitTime V V' eta := by
              by_contra hnot
              have hle : hitExitTime V V' eta ≤ ((t - a : NNReal) : ℝ≥0∞) :=
                le_of_not_gt hnot
              have hsum : (a : ℝ≥0∞) + hitExitTime V V' eta ≤ (t : ℝ≥0∞) := by
                calc
                  (a : ℝ≥0∞) + hitExitTime V V' eta ≤
                      (a : ℝ≥0∞) + ((t - a : NNReal) : ℝ≥0∞) := add_le_add le_rfl hle
                  _ = (t : ℝ≥0∞) := by
                    rw [← ENNReal.coe_add, add_tsub_cancel_of_le hat]
              exact (not_le_of_gt ht') hsum
            have hjShift : eta (t - a) ∈ V j := by
              dsimp only [eta]
              rw [shift_apply, add_tsub_cancel_of_le hat]
              exact hjV
            have hover : (V j ∩ V' idx).Nonempty := by
              exact visited_before_hitExitTime_subset V V' eta
                ⟨t - a, hremain, hjShift⟩
            exact Finset.mem_union_right sold (hnew j hover)

/-- If a path visits more distinct hit sets than `N` overlap blocks can contain before
leaving `U`, then its first `N` hit-then-exit cycles finish before that exit. -/
theorem iteratedStoppingTime_hitExit_le_exitTime_of_visits
    (V V' : ℕ → Set alpha) (U : Set alpha)
    (omega : ContinuousPath alpha) (K D N : ℕ)
    (hoverlap : ∀ i, ∃ s : Finset ℕ,
      s.card ≤ K ∧ ∀ j, (V j ∩ V' i).Nonempty → j ∈ s)
    (hvisits : ∃ s : Finset ℕ, D ≤ s.card ∧ ∀ i ∈ s,
      ∃ t : NNReal, (t : ℝ≥0∞) < exitTime U omega ∧ omega t ∈ V i)
    (hcount : N * K < D) :
    iteratedStoppingTime (hitExitTime V V') N omega ≤ exitTime U omega := by
  by_contra hnot
  have hexitLt : exitTime U omega <
      iteratedStoppingTime (hitExitTime V V') N omega := lt_of_not_ge hnot
  obtain ⟨svisit, hDcard, hsvisit⟩ := hvisits
  obtain ⟨scover, hcoverCard, hscover⟩ :=
    visited_before_iterated_subset V V' K hoverlap N omega
  have hsubset : svisit ⊆ scover := by
    intro i hi
    obtain ⟨t, ht, hiV⟩ := hsvisit i hi
    exact hscover i ⟨t, ht.trans hexitLt, hiV⟩
  have hcontra : D ≤ N * K :=
    hDcard.trans ((Finset.card_le_card hsubset).trans hcoverCard)
  exact (Nat.not_le_of_lt hcount) hcontra

end ContinuousPath

namespace SubMarkovKernelSemigroup

open MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- A one-step discounted exit bound on every hitting set controls the composite hit-then-exit
rule from every starting point. -/
theorem IsFellerKernelSemigroup.lintegral_discountedStoppingWeight_hitExitTime_le
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (V V' : ℕ → Set alpha) (hVmeasurable : ∀ i, MeasurableSet (V i))
    (hDclosed : IsClosed (⋃ i, V i)) (hV'open : ∀ i, IsOpen (V' i))
    (lam : ℝ) (hlam : 0 ≤ lam) (rho : ℝ≥0∞)
    (hone : ∀ i, ∀ z ∈ V i,
      ∫⁻ eta, ContinuousPath.discountedStoppingWeight lam
          (ContinuousPath.exitTime (V' i)) eta
        ∂(IsConservative.continuousProcess P hP z) ≤ rho)
    (y : alpha) :
    ∫⁻ omega, ContinuousPath.discountedStoppingWeight lam
        (ContinuousPath.hitExitTime V V') omega
      ∂(IsConservative.continuousProcess P hP y) ≤ rho := by
  let Q : Kernel alpha (ContinuousPath alpha) := IsConservative.continuousProcess P hP
  let D : Set alpha := ⋃ i, V i
  let T : ContinuousPath alpha → ℝ≥0∞ := ContinuousPath.hitTime D
  let idx : ContinuousPath alpha → ℕ := fun omega ↦
    ContinuousPath.familyIndex V (omega ((T omega).untopD 0))
  let S : Set (ContinuousPath alpha) := {omega | T omega < ⊤}
  let Y : ContinuousPath alpha → ContinuousPath alpha := fun omega ↦
    ContinuousPath.shift ((T omega).untopD 0) omega
  let G : ℕ → ContinuousPath alpha → ℝ≥0∞ := fun i ↦
    ContinuousPath.discountedStoppingWeight lam (ContinuousPath.exitTime (V' i))
  let W : ℕ → ContinuousPath alpha → ℝ≥0∞ := fun i ↦
    {omega | idx omega = i}.indicator (fun _ ↦ 1)
  have hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha)) T := by
    simpa only [T, ContinuousPath.hitTime] using!
      ContinuousPath.isStoppingTime_exitTime Dᶜ hDclosed.isOpen_compl
  have hS : MeasurableSet[hT.measurableSpace] S :=
    StoppingTime.measurableSet_stoppingTime_lt_top hT
  have hY : Measurable Y :=
    ContinuousPath.measurable_shift_untopD_stoppingTime T hT
  have hIdx : Measurable[hT.measurableSpace] idx :=
    (ContinuousPath.measurable_familyIndex V hVmeasurable).comp
      (ContinuousPath.measurable_eval_untopD_stoppingTime_stopped T hT)
  have hG : ∀ i, Measurable (G i) := by
    intro i
    exact ContinuousPath.measurable_discountedStoppingWeight
      (ContinuousPath.exitTime (V' i))
      (ContinuousPath.isStoppingTime_exitTime (V' i) (hV'open i)) lam
  have hW : ∀ i, Measurable[hT.measurableSpace] (W i) := by
    intro i
    exact measurable_const.indicator (hIdx (measurableSet_singleton i))
  have hWGlobal : ∀ i, Measurable (W i) := fun i ↦
    (hW i).mono hT.measurableSpace_le le_rfl
  have hRestart : ∀ i,
      (∫⁻ omega, W i omega * S.indicator (fun omega ↦ G i (Y omega)) omega ∂Q y) =
        ∫⁻ omega, W i omega * S.indicator
          (fun omega ↦ ∫⁻ eta, G i eta ∂Q (omega ((T omega).untopD 0))) omega ∂Q y := by
    intro i
    apply StoppingTime.lintegral_mul_indicator_of_restrict_map
      (mu := Q y)
      (kappa := Kernel.comap Q (fun omega ↦ omega ((T omega).untopD 0))
        (ContinuousPath.measurable_eval_untopD_stoppingTime T hT))
      (Y := Y) (m := hT.measurableSpace) (S := S) (F := G i) (W := W i)
    · exact hY
    · exact hT.measurableSpace_le
    · exact hS
    · intro A hA
      exact hFeller.continuousProcess_restrict_map_shift_stoppingTime_lt_top
        P hP hK y T hT A hA
    · exact hG i
    · exact hW i
  have hPiece : ∀ i,
      (∫⁻ omega, W i omega * S.indicator (fun omega ↦ G i (Y omega)) omega ∂Q y) ≤
        ∫⁻ omega, W i omega * S.indicator (fun _ ↦ rho) omega ∂Q y := by
    intro i
    rw [hRestart i]
    refine lintegral_mono fun omega ↦ ?_
    by_cases hs : omega ∈ S
    swap
    · simp only [Set.indicator_of_notMem hs, mul_zero, le_refl]
    simp only [Set.indicator_of_mem hs]
    by_cases hi : idx omega = i
    swap
    · have hiNotMem : omega ∉ {eta | idx eta = i} := by
        simpa only [Set.mem_ofPred_eq] using hi
      dsimp only [W]
      rw [Set.indicator_of_notMem hiNotMem, zero_mul]
      exact zero_le
    have hiMem : omega ∈ {eta | idx eta = i} := hi
    dsimp only [W]
    rw [Set.indicator_of_mem hiMem, one_mul]
    have hstateD : omega ((T omega).untopD 0) ∈ D :=
      ContinuousPath.coordinate_hitTime_mem D hDclosed omega (ne_of_lt hs)
    have hstateV : omega ((T omega).untopD 0) ∈ V i := by
      have hselected := ContinuousPath.familyIndex_mem_of_mem_iUnion V hstateD
      simpa only [idx, hi] using hselected
    simpa only [one_mul] using
      hone i (omega ((T omega).untopD 0)) hstateV
  have hSummandMeas : ∀ i, AEMeasurable
      (fun omega ↦ W i omega * S.indicator (fun omega ↦ G i (Y omega)) omega) (Q y) := by
    intro i
    exact ((hWGlobal i).mul ((hG i).comp hY |>.indicator
      (hT.measurableSpace_le S hS))).aemeasurable
  have hMainPoint : ∀ omega,
      ContinuousPath.discountedStoppingWeight lam
          (ContinuousPath.hitExitTime V V') omega ≤
        ∑' i, W i omega * S.indicator (fun omega ↦ G i (Y omega)) omega := by
    intro omega
    have hsum : (∑' i, W i omega * S.indicator (fun omega ↦ G i (Y omega)) omega) =
        S.indicator (fun omega ↦ G (idx omega) (Y omega)) omega := by
      by_cases hs : omega ∈ S
      · simp only [Set.indicator_of_mem hs]
        rw [tsum_eq_single (idx omega)]
        · have hmem : omega ∈ {eta | idx eta = idx omega} := rfl
          dsimp only [W]
          rw [Set.indicator_of_mem hmem, one_mul]
        · intro i hi
          have hnot : omega ∉ {eta | idx eta = i} := by
            simpa only [Set.mem_ofPred_eq] using Ne.symm hi
          dsimp only [W]
          rw [Set.indicator_of_notMem hnot, zero_mul]
      · simp only [Set.indicator_of_notMem hs, mul_zero, tsum_zero]
    rw [hsum]
    by_cases hTfinite : omega ∈ S
    swap
    · rw [Set.indicator_of_notMem hTfinite]
      have hnot : ¬T omega < ⊤ := by
        simpa only [S, Set.mem_ofPred_eq] using hTfinite
      have hTtop : T omega = ⊤ := top_unique (not_lt.mp hnot)
      have hsumTop : ContinuousPath.hitExitTime V V' omega = ⊤ := by
        change T omega +
          ContinuousPath.exitTime (V' (idx omega)) (Y omega) = ⊤
        rw [hTtop, top_add]
      rw [ContinuousPath.discountedStoppingWeight]
      have hnotMem : omega ∉
          {eta | ContinuousPath.hitExitTime V V' eta < ⊤} := by
        simp only [Set.mem_ofPred_eq, hsumTop, lt_self_iff_false, not_false_eq_true]
      rw [Set.indicator_of_notMem hnotMem]
    rw [Set.indicator_of_mem hTfinite]
    let R : ℝ≥0∞ := ContinuousPath.exitTime (V' (idx omega)) (Y omega)
    by_cases hRfinite : R = ⊤
    · have hsumTop : ContinuousPath.hitExitTime V V' omega = ⊤ := by
        change T omega + R = ⊤
        rw [hRfinite, add_top]
      rw [ContinuousPath.discountedStoppingWeight]
      have hnotMem : omega ∉
          {eta | ContinuousPath.hitExitTime V V' eta < ⊤} := by
        simp only [Set.mem_ofPred_eq, hsumTop, lt_self_iff_false, not_false_eq_true]
      rw [Set.indicator_of_notMem hnotMem]
      exact zero_le
    · have hTne : T omega ≠ ⊤ := ne_of_lt hTfinite
      have hsumFinite : T omega + R ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hTne, hRfinite⟩
      have hsigma : ContinuousPath.hitExitTime V V' omega = T omega + R := rfl
      have hmemSigma : omega ∈ {eta | ContinuousPath.hitExitTime V V' eta < ⊤} := by
        simpa only [hsigma, lt_top_iff_ne_top]
      have hmemR : Y omega ∈
          {eta | ContinuousPath.exitTime (V' (idx omega)) eta < ⊤} := by
        simpa only [R, lt_top_iff_ne_top]
      rw [ContinuousPath.discountedStoppingWeight, Set.indicator_of_mem hmemSigma]
      change ENNReal.ofReal
          (Real.exp (-lam * (ContinuousPath.hitExitTime V V' omega).toReal)) ≤
            G (idx omega) (Y omega)
      dsimp only [G]
      rw [ContinuousPath.discountedStoppingWeight, Set.indicator_of_mem hmemR, hsigma]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hreal : R.toReal ≤ (T omega + R).toReal :=
        ENNReal.toReal_mono hsumFinite (le_add_left le_rfl)
      exact mul_le_mul_of_nonpos_left hreal (neg_nonpos.mpr hlam)
  calc
    (∫⁻ omega, ContinuousPath.discountedStoppingWeight lam
        (ContinuousPath.hitExitTime V V') omega ∂Q y) ≤
        ∫⁻ omega, ∑' i, W i omega * S.indicator (fun omega ↦ G i (Y omega)) omega ∂Q y :=
      lintegral_mono hMainPoint
    _ = ∑' i, ∫⁻ omega, W i omega * S.indicator
        (fun omega ↦ G i (Y omega)) omega ∂Q y := lintegral_tsum hSummandMeas
    _ ≤ ∑' i, ∫⁻ omega, W i omega * S.indicator (fun _ ↦ rho) omega ∂Q y :=
      ENNReal.tsum_le_tsum hPiece
    _ = ∫⁻ omega, ∑' i, W i omega * S.indicator (fun _ ↦ rho) omega ∂Q y := by
      rw [lintegral_tsum]
      intro i
      exact ((hWGlobal i).mul (measurable_const.indicator
        (hT.measurableSpace_le S hS))).aemeasurable
    _ = ∫⁻ omega, S.indicator (fun _ ↦ rho) omega ∂Q y := by
      apply lintegral_congr
      intro omega
      by_cases hs : omega ∈ S
      · simp only [Set.indicator_of_mem hs]
        rw [tsum_eq_single (idx omega)]
        · have hmem : omega ∈ {eta | idx eta = idx omega} := rfl
          dsimp only [W]
          rw [Set.indicator_of_mem hmem, one_mul]
        · intro i hi
          have hnot : omega ∉ {eta | idx eta = i} := by
            simpa only [Set.mem_ofPred_eq] using Ne.symm hi
          dsimp only [W]
          rw [Set.indicator_of_notMem hnot, zero_mul]
      · simp only [Set.indicator_of_notMem hs, mul_zero, tsum_zero]
    _ ≤ rho * (Q y) S := lintegral_indicator_const_le S rho
    _ ≤ rho * 1 := by
      exact mul_le_mul_right ((measure_mono (Set.subset_univ S)).trans_eq measure_univ) rho
    _ = rho := mul_one rho

/-- The general exit-time chaining estimate specialized to the composite hit-then-exit rule.
The geometric comparison with the terminal exit time is supplied directly, guarded by
`exitTime U omega < ⊤`: paths that never leave `U` are unconstrained. -/
theorem IsConservative.lintegral_exp_neg_exitTime_le_rho_pow_hitExit_of_cover
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (V V' : ℕ → Set alpha) (hVmeasurable : ∀ i, MeasurableSet (V i))
    (hDclosed : IsClosed (⋃ i, V i)) (hV'open : ∀ i, IsOpen (V' i))
    (U : Set alpha) (lam : ℝ) (hlam : 0 < lam) (rho : ℝ≥0∞) (hrho : rho ≠ ⊤)
    (hone : ∀ i, ∀ z ∈ V i,
      ∫⁻ eta, ContinuousPath.discountedStoppingWeight lam
          (ContinuousPath.exitTime (V' i)) eta
        ∂(IsConservative.continuousProcess P hP z) ≤ rho)
    (N : ℕ) (x : alpha)
    (hcover : ∀ᵐ omega ∂(IsConservative.continuousProcess P hP x),
      ContinuousPath.exitTime U omega < ⊤ →
        ContinuousPath.iteratedStoppingTime (ContinuousPath.hitExitTime V V') N omega ≤
          ContinuousPath.exitTime U omega) :
    ∫⁻ omega, ContinuousPath.discountedStoppingWeight lam
        (ContinuousPath.exitTime U) omega
      ∂(IsConservative.continuousProcess P hP x) ≤ rho ^ N := by
  have hsigma : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (ContinuousPath.hitExitTime V V') :=
    ContinuousPath.isStoppingTime_hitExitTime V V' hVmeasurable hDclosed hV'open
  have hsmall : ∀ y ∈ Set.univ,
      ∫⁻ omega, ContinuousPath.discountedStoppingWeight lam
          (ContinuousPath.hitExitTime V V') omega
        ∂(IsConservative.continuousProcess P hP y) ≤ rho := by
    intro y _
    exact IsFellerKernelSemigroup.lintegral_discountedStoppingWeight_hitExitTime_le P hP hFeller hK V V'
      hVmeasurable hDclosed hV'open lam hlam.le rho hone y
  exact IsConservative.lintegral_exp_neg_exitTime_le_rho_pow P hP hFeller hK Set.univ U lam hlam
    (ContinuousPath.hitExitTime V V') hsigma rho hrho hsmall
    (fun _ _ _ ↦ Set.mem_univ _) N x (Set.mem_univ x) hcover

/-- **Composite hit-then-exit chaining bound.** If each selected enlargement meets at most `K`
hit sets and almost every path visits at least `D` explicitly listed hit sets strictly before
leaving `U`, then `N * K < D` turns the one-cycle estimate into a `rho ^ N` terminal-exit
estimate.

The visits premise is guarded by `exitTime U omega < ⊤`, so it asks nothing of paths that never
leave `U`.  Because almost every path starts at `x`, a starting point outside `U` leaves at time
`0`; no visit time is then strictly earlier, the guarded premise forces `D = 0`, and `hcount`
fails.  The conclusion is therefore vacuous unless `x ∈ U`. -/
theorem IsConservative.lintegral_exp_neg_exitTime_le_rho_pow_hitExit
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (V V' : ℕ → Set alpha) (hVmeasurable : ∀ i, MeasurableSet (V i))
    (hDclosed : IsClosed (⋃ i, V i)) (hV'open : ∀ i, IsOpen (V' i))
    (U : Set alpha)
    (lam : ℝ) (hlam : 0 < lam) (rho : ℝ≥0∞) (hrho : rho ≠ ⊤)
    (hone : ∀ i, ∀ z ∈ V i,
      ∫⁻ eta, ContinuousPath.discountedStoppingWeight lam
          (ContinuousPath.exitTime (V' i)) eta
        ∂(IsConservative.continuousProcess P hP z) ≤ rho)
    (K D N : ℕ) (x : alpha)
    (hoverlap : ∀ i, ∃ s : Finset ℕ,
      s.card ≤ K ∧ ∀ j, (V j ∩ V' i).Nonempty → j ∈ s)
    (hvisits : ∀ᵐ omega ∂(IsConservative.continuousProcess P hP x),
      ContinuousPath.exitTime U omega < ⊤ →
        ∃ s : Finset ℕ, D ≤ s.card ∧ ∀ i ∈ s,
          ∃ t : NNReal, (t : ℝ≥0∞) < ContinuousPath.exitTime U omega ∧ omega t ∈ V i)
    (hcount : N * K < D) :
    ∫⁻ omega, ContinuousPath.discountedStoppingWeight lam
        (ContinuousPath.exitTime U) omega
      ∂(IsConservative.continuousProcess P hP x) ≤ rho ^ N := by
  apply IsConservative.lintegral_exp_neg_exitTime_le_rho_pow_hitExit_of_cover P hP hFeller hK V V'
    hVmeasurable hDclosed hV'open U lam hlam rho hrho hone N x
  filter_upwards [hvisits] with omega hvisitsOmega
  intro hexit
  exact ContinuousPath.iteratedStoppingTime_hitExit_le_exitTime_of_visits V V' U omega K D N
    hoverlap (hvisitsOmega hexit) hcount

end SubMarkovKernelSemigroup

end

end Algsuperdiff.Process
