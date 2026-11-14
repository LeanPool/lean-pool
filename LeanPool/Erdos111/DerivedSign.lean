/-
Copyright (c) 2026 Jacob Parish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Parish
-/

module

public import LeanPool.Erdos111.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Derived signs of infinite traces (Lemma D)

Let `ν` satisfy `J` over `M`, and let `y ∉ M` have infinitely many neighbours in `M`.
Enumerate infinitely many of them as `a 0, a 1, …`. Stars from `y` to finite sets of
neighbours are patterns over `M`, so the expected minority count of the signs on any
finite set of neighbours is at most `C`. Hence almost surely one sign occurs only finitely
often along `a`; the other is the derived sign `s`, a measurable function of the
coordinates `a n`. For every finite set `B` of neighbours, the stars on `B` together with
`a 0, …, a (L - 1)` cost at least the disagreements with `s` on `B` once the derived sign
has recurred often enough along `a`, so monotone convergence in `L` bounds
`∑ u ∈ B, ν (σ u ≠ s)` by `C`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace Erdos111

variable {V : Type*}

open Classical in
/-- A star from `y` to the vertices of `D`, with `y ∉ D`, has extension cost equal to the
number of vertices of `D` carrying some sign `c`, the sign chosen for `y`. -/
theorem exists_extCost_star_eq {y : V} {D : Finset V} (hyD : y ∉ D) (τ : V → Bool) :
    ∃ c : Bool, extCost {y} (D.image fun b => s(y, b)) τ =
      (D.filter fun b => τ b = c).card := by
  obtain ⟨η, hη⟩ := exists_extCost_eq {y} (D.image fun b => s(y, b)) τ
  refine ⟨η y, hη.symm.trans ?_⟩
  unfold monoCount
  rw [Finset.filter_image, Finset.card_image_of_injective _ fun b b' h => Sym2.congr_right.1 h]
  congr 1
  refine Finset.filter_congr fun b hb => ?_
  have hby : b ≠ y := fun h => hyD (h ▸ hb)
  simp [mono, Finset.piecewise_eq_of_notMem _ _ _ (Finset.notMem_singleton.2 hby), eq_comm]

open Classical in
/-- A star from `y ∉ M` to finitely many of its neighbours in `M` is a pattern over `M`. -/
theorem isOver_star {G : SimpleGraph V} {M : Set V} {y : V} (hy : y ∉ M) {D : Finset V}
    (hD : ↑D ⊆ {u | G.Adj y u ∧ u ∈ M}) :
    (⟨D, {y}, D.image fun b => s(y, b)⟩ : Pattern V).IsOver G M where
  roots_subset u hu := (hD hu).2
  new_not_mem v hv := by
    rw [Finset.mem_singleton.1 hv]
    exact hy
  edges_subset e he := by
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 he
    exact (hD hb).1
  edges_meet e he := by
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 he
    exact ⟨y, Sym2.mem_mk_left y b, Finset.mem_singleton_self y⟩
  edges_inside e he v hv := by
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 he
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact Or.inr (Finset.mem_singleton_self v)
    · exact Or.inl hb

open Classical in
/-- An infinite set of naturals meets some initial segment in at least `K` elements. -/
theorem exists_le_card_filter_range {p : ℕ → Prop} [DecidablePred p] (h : {n | p n}.Infinite)
    (K : ℕ) : ∃ L, K ≤ ((Finset.range L).filter p).card := by
  obtain ⟨t, ht, rfl⟩ := h.exists_subset_card_eq K
  refine ⟨t.sup id + 1, Finset.card_le_card fun n hn => Finset.mem_filter.2 ⟨?_, ht hn⟩⟩
  exact Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))

open Classical in
/-- The count of a property along an initial segment is monotone in its length. -/
theorem card_filter_range_mono (p : ℕ → Prop) [DecidablePred p] {L L' : ℕ} (h : L ≤ L') :
    ((Finset.range L).filter p).card ≤ ((Finset.range L').filter p).card :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.2 h))

open Classical in
/-- The number of indices with a measurable property is a measurable function. -/
theorem measurable_card_filter {ι : Type*} (B : Finset ι) (p : ι → (V → Bool) → Prop)
    [∀ i ω, Decidable (p i ω)] (hp : ∀ i, MeasurableSet {ω | p i ω}) :
    Measurable fun ω => (((B.filter fun i => p i ω).card : ℕ) : ℝ≥0∞) := by
  have : (fun ω => (((B.filter fun i => p i ω).card : ℕ) : ℝ≥0∞)) =
      fun ω => ∑ i ∈ B, Set.indicator {ω | p i ω} 1 ω := by
    funext ω
    rw [Finset.card_filter]
    push_cast
    simp [Set.indicator_apply]
  rw [this]
  exact Finset.measurable_sum _ fun i _ => measurable_const.indicator (hp i)

open Classical in
/-- The expected number of indices with a measurable property is the sum of their
probabilities. -/
theorem lintegral_card_filter {ι : Type*} (ν : Measure (V → Bool)) (B : Finset ι)
    (p : ι → (V → Bool) → Prop) [∀ i ω, Decidable (p i ω)]
    (hp : ∀ i, MeasurableSet {ω | p i ω}) :
    ∫⁻ ω, (((B.filter fun i => p i ω).card : ℕ) : ℝ≥0∞) ∂ν = ∑ i ∈ B, ν {ω | p i ω} := by
  have : (fun ω => (((B.filter fun i => p i ω).card : ℕ) : ℝ≥0∞)) =
      fun ω => ∑ i ∈ B, Set.indicator {ω | p i ω} 1 ω := by
    funext ω
    rw [Finset.card_filter]
    push_cast
    simp [Set.indicator_apply]
  rw [this, lintegral_finsetSum B (f := fun i => Set.indicator {ω | p i ω} 1)
    fun i _ => measurable_const.indicator (hp i)]
  exact Finset.sum_congr rfl fun i _ => lintegral_indicator_one (hp i)

open Classical in
/-- Lemma D: a vertex with infinitely many neighbours in `M` has a derived sign `s`,
determined by the signs along an enumeration `a` of some of those neighbours, from which
almost surely only finitely many signs along `a` differ, and whose expected disagreement
with the signs of the neighbours sums to at most `C`. -/
theorem exists_derivedSign {G : SimpleGraph V} {C : ℝ≥0} {M : Set V}
    {ν : Measure (V → Bool)} (hν : Rooted G C M ν)
    {y : V} (hy : y ∉ M) (hT : {u | G.Adj y u ∧ u ∈ M}.Infinite) :
    ∃ (s : (V → Bool) → Bool) (a : ℕ → V),
      Function.Injective a ∧ (∀ n, G.Adj y (a n) ∧ a n ∈ M) ∧
      DependsOn s (Set.range a) ∧ Measurable s ∧
      (∀ᵐ ω ∂ν, {n | ω (a n) ≠ s ω}.Finite) ∧
      ∀ B : Finset V, ↑B ⊆ {u | G.Adj y u ∧ u ∈ M} →
        ∑ u ∈ B, ν {ω | ω u ≠ s ω} ≤ C := by
  classical
  set T := {u | G.Adj y u ∧ u ∈ M}
  -- An enumeration `a` of infinitely many neighbours in `M`.
  set a : ℕ → V := fun n => (hT.natEmbedding T n : V)
  have ha_inj : Function.Injective a :=
    Subtype.val_injective.comp (hT.natEmbedding T).injective
  have haT : ∀ n, a n ∈ T := fun n => (hT.natEmbedding T n).2
  have hyD : ∀ D : Finset V, ↑D ⊆ T → y ∉ D := fun D hD hyD => hy (hD hyD).2
  -- The derived sign: whether the sign `true` occurs infinitely often along `a`.
  set s : (V → Bool) → Bool := fun ω => decide {n | ω (a n) = true}.Infinite with hsdef
  have hs_meas : Measurable s := by
    refine measurable_to_bool ?_
    have : s ⁻¹' {true} = ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n), {ω | ω (a n) = true} := by
      ext ω
      simp [hsdef, ← Nat.frequently_atTop_iff_infinite, Filter.frequently_atTop]
    rw [this]
    exact MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n => MeasurableSet.iUnion
      fun _ => measurableSet_eq_fun (measurable_pi_apply (a n)) measurable_const
  have hs_dep : DependsOn s (Set.range a) := by
    intro ω ω' h
    have : ∀ n, ω (a n) = ω' (a n) := fun n => h (a n) ⟨n, rfl⟩
    simp only [hsdef, this]
  -- The derived sign occurs infinitely often along `a`.
  have hs_inf : ∀ ω, {n | ω (a n) = s ω}.Infinite := by
    intro ω
    by_cases h : {n | ω (a n) = true}.Infinite
    · simp [hsdef, h]
    · have : {n | ω (a n) = s ω} = {n | ω (a n) = true}ᶜ := by
        ext n
        simp [hsdef, h]
      rw [this]
      exact (Set.not_infinite.1 h).infinite_compl
  have hmeas_eq : ∀ (u : V) (c : (V → Bool) → Bool), Measurable c →
      MeasurableSet {ω : V → Bool | ω u = c ω} :=
    fun u c hc => measurableSet_eq_fun (measurable_pi_apply u) hc
  -- Stars from `y` cost at most `C` in expectation.
  have hstar : ∀ D : Finset V, ↑D ⊆ T →
      ∫⁻ ω, (extCost {y} (D.image fun b => s(y, b)) ω : ℝ≥0∞) ∂ν ≤ C := by
    intro D hD
    simpa using hν _ (isOver_star hy hD)
  have hcard_img : ∀ (L : ℕ) (ω : V → Bool) (c : Bool),
      (((Finset.range L).image a).filter fun u => ω u = c).card =
        ((Finset.range L).filter fun n => ω (a n) = c).card := by
    intro L ω c
    rw [Finset.filter_image, Finset.card_image_of_injective _ ha_inj]
  have himg_T : ∀ L, ↑((Finset.range L).image a) ⊆ T := by
    intro L u hu
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hu
    exact haT n
  refine ⟨s, a, ha_inj, haT, hs_dep, hs_meas, ?_, ?_⟩
  · -- The minority count along `a 0, …, a (L - 1)`.
    set f : ℕ → (V → Bool) → ℝ≥0∞ := fun L ω =>
      min (((Finset.range L).filter fun n => ω (a n) = true).card : ℝ≥0∞)
        (((Finset.range L).filter fun n => ω (a n) = false).card : ℝ≥0∞)
    have hf_meas : ∀ L, Measurable (f L) := fun L =>
      (measurable_card_filter _ (fun n ω => ω (a n) = true)
        fun n => hmeas_eq _ _ measurable_const).min
      (measurable_card_filter _ (fun n ω => ω (a n) = false)
        fun n => hmeas_eq _ _ measurable_const)
    have hf_mono : Monotone f := fun L L' h ω =>
      min_le_min (Nat.cast_le.2 (card_filter_range_mono _ h))
        (Nat.cast_le.2 (card_filter_range_mono _ h))
    have hf_le : ∀ L ω, f L ω ≤
        extCost {y} (((Finset.range L).image a).image fun b => s(y, b)) ω := by
      intro L ω
      obtain ⟨c, hc⟩ := exists_extCost_star_eq (hyD _ (himg_T L)) ω
      rw [hc, hcard_img]
      cases c
      · exact min_le_right _ _
      · exact min_le_left _ _
    have hF : ∫⁻ ω, ⨆ L, f L ω ∂ν ≤ C := by
      rw [lintegral_iSup hf_meas hf_mono]
      exact iSup_le fun L => (lintegral_mono (hf_le L)).trans (hstar _ (himg_T L))
    filter_upwards [ae_lt_top (Measurable.iSup hf_meas)
      (hF.trans_lt ENNReal.coe_lt_top).ne] with ω hω
    by_contra hinf
    obtain ⟨K, hK⟩ := ENNReal.exists_nat_gt hω.ne
    have hboth : ∀ c, {n | ω (a n) = c}.Infinite := by
      intro c
      by_cases hc : c = s ω
      · rw [hc]
        exact hs_inf ω
      · have : {n | ω (a n) = c} = {n | ω (a n) ≠ s ω} := by
          ext n
          simp only [Set.mem_ofPred_eq, Bool.eq_not_iff.2 hc, Bool.eq_not_iff]
        rw [this]
        exact hinf
    obtain ⟨L₁, hL₁⟩ := exists_le_card_filter_range (hboth true) K
    obtain ⟨L₂, hL₂⟩ := exists_le_card_filter_range (hboth false) K
    refine (hK.trans_le (le_iSup_of_le (max L₁ L₂) ?_)).false
    exact le_min
      (Nat.cast_le.2 (hL₁.trans (card_filter_range_mono _ (le_max_left _ _))))
      (Nat.cast_le.2 (hL₂.trans (card_filter_range_mono _ (le_max_right _ _))))
  · intro B hB
    -- The disagreement count on `B`, capped by the agreement count along `a`.
    set h : ℕ → (V → Bool) → ℝ≥0∞ := fun L ω =>
      min ((B.filter fun u => ω u ≠ s ω).card : ℝ≥0∞)
        (((Finset.range L).filter fun n => ω (a n) = s ω).card : ℝ≥0∞)
    have hh_meas : ∀ L, Measurable (h L) := fun L =>
      (measurable_card_filter _ (fun u ω => ω u ≠ s ω)
        fun u => (hmeas_eq _ _ hs_meas).compl).min
      (measurable_card_filter _ (fun n ω => ω (a n) = s ω)
        fun n => hmeas_eq _ _ hs_meas)
    have hh_mono : Monotone h := fun L L' hLL' ω =>
      min_le_min le_rfl (Nat.cast_le.2 (card_filter_range_mono _ hLL'))
    have hDT : ∀ L, ↑(B ∪ (Finset.range L).image a) ⊆ T := by
      intro L
      rw [Finset.coe_union]
      exact Set.union_subset hB (himg_T L)
    have hh_le : ∀ L ω, h L ω ≤
        extCost {y} ((B ∪ (Finset.range L).image a).image fun b => s(y, b)) ω := by
      intro L ω
      obtain ⟨c, hc⟩ := exists_extCost_star_eq (hyD _ (hDT L)) ω
      rw [hc]
      by_cases hcs : c = s ω
      · refine (min_le_right _ _).trans (Nat.cast_le.2 ?_)
        rw [hcs, ← hcard_img]
        exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.subset_union_right)
      · refine (min_le_left _ _).trans (Nat.cast_le.2 ?_)
        have : (B.filter fun u => ω u ≠ s ω) = B.filter fun u => ω u = c := by
          refine Finset.filter_congr fun u _ => ?_
          rw [Bool.eq_not_iff.2 hcs, Bool.eq_not_iff]
        rw [this]
        exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.subset_union_left)
    calc ∑ u ∈ B, ν {ω | ω u ≠ s ω}
        = ∫⁻ ω, ((B.filter fun u => ω u ≠ s ω).card : ℝ≥0∞) ∂ν :=
          (lintegral_card_filter ν B (fun u ω => ω u ≠ s ω)
            fun u => (hmeas_eq _ _ hs_meas).compl).symm
      _ ≤ ∫⁻ ω, ⨆ L, h L ω ∂ν := by
          refine lintegral_mono fun ω => ?_
          obtain ⟨L, hL⟩ := exists_le_card_filter_range (hs_inf ω)
            (B.filter fun u => ω u ≠ s ω).card
          exact le_iSup_of_le L (le_min le_rfl (Nat.cast_le.2 hL))
      _ = ⨆ L, ∫⁻ ω, h L ω ∂ν := lintegral_iSup hh_meas hh_mono
      _ ≤ C := iSup_le fun L => (lintegral_mono (hh_le L)).trans (hstar _ (hDT L))

end Erdos111
