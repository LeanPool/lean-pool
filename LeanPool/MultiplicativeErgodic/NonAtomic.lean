/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-!
# Small positive-measure sets in non-atomic measures

Mathlib's `NullSingletonClass` only records that singletons are null; it does *not* record the
classically stronger "no atoms" property (every positive-measure set has a positive-measure
proper subset) -- see the `TODO` note in
`Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass`, which states explicitly that the
stronger property implies `NullSingletonClass` but not conversely, in general measurable spaces.

For the "Lebesgue probability space" setting of `ProofMet.Rokhlin` (i.e. a standard Borel space),
the two notions do coincide, and this file proves the fact we actually need: every positive-measure
measurable set contains a measurable subset of arbitrarily small positive measure. This is the
first building block towards `ProofMet.rokhlin_lemma`.

The proof goes via a measurable embedding into `ℝ` (`MeasureTheory.embeddingReal`, available for
any `StandardBorelSpace`), where the key fact is proved directly from continuity of measures from
above/below: if every positive-measure subset of `T ⊆ ℝ` were null-or-full, the cumulative function
`t ↦ κ (T ∩ Iic t)` would jump directly from `0` to `κ T` at its unique jump point `t₀`, forcing
`κ (T ∩ {t₀}) = κ T > 0` and contradicting non-atomicity of singletons.
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Set Filter Topology

namespace ProofMet

section Real

variable {κ : Measure ℝ} [IsFiniteMeasure κ] [MeasureTheory.NullSingletonClass κ]

/-- If every positive-measure subset of `T` were null-or-full, the cumulative function
`t ↦ κ (T ∩ Iic t)` could only take the values `0` and `κ T`. This lemma packages the
contradiction that results: the jump point of that function would carry an atom of mass `κ T`. -/
private theorem not_forall_eq_zero_or_eq
    {T : Set ℝ} (hT : MeasurableSet T) (hTpos : 0 < κ T)
    (h : ∀ V ⊆ T, MeasurableSet V → κ V = 0 ∨ κ V = κ T) : False := by
  have hA_mem : ∀ t : ℝ, κ (T ∩ Iic t) = 0 ∨ κ (T ∩ Iic t) = κ T := fun t =>
    h _ inter_subset_left (hT.inter measurableSet_Iic)
  have hA_mono : Monotone (fun t : ℝ => κ (T ∩ Iic t)) := fun s t hst =>
    measure_mono (inter_subset_inter_right T (Iic_subset_Iic.2 hst))
  -- The cumulative function tends to `0` at `-∞` and to `κ T` at `+∞`.
  have hA_atBot : Tendsto (fun n : ℕ => κ (T ∩ Iic (-(n : ℝ)))) atTop (𝓝 0) := by
    have hanti : Antitone (fun n : ℕ => T ∩ Iic (-(n : ℝ))) := fun m n hmn =>
      inter_subset_inter_right T (Iic_subset_Iic.2 (neg_le_neg (Nat.cast_le.2 hmn)))
    have hiInter : (⋂ n : ℕ, T ∩ Iic (-(n : ℝ))) = ∅ := by
      ext x
      simp only [mem_iInter, mem_inter_iff, mem_Iic, mem_empty_iff_false, iff_false]
      intro hx
      obtain ⟨n, hn⟩ := exists_nat_gt (-x)
      exact absurd (hx n).2 (by linarith)
    have hlim := tendsto_measure_iInter_atTop
      (s := fun n : ℕ => T ∩ Iic (-(n : ℝ)))
      (fun n => (hT.inter measurableSet_Iic).nullMeasurableSet)
      hanti ⟨0, (measure_lt_top κ _).ne⟩
    rw [hiInter, measure_empty] at hlim
    exact hlim
  have hA_atTop : Tendsto (fun n : ℕ => κ (T ∩ Iic (n : ℝ))) atTop (𝓝 (κ T)) := by
    have hmono : Monotone (fun n : ℕ => T ∩ Iic (n : ℝ)) := fun m n hmn =>
      inter_subset_inter_right T (Iic_subset_Iic.2 (Nat.cast_le.2 hmn))
    have hiUnion : (⋃ n : ℕ, T ∩ Iic (n : ℝ)) = T := by
      ext x
      simp only [mem_iUnion, mem_inter_iff, mem_Iic]
      constructor
      · rintro ⟨n, hx, -⟩; exact hx
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_gt x
        exact ⟨n, hx, hn.le⟩
    have hlim := tendsto_measure_iUnion_atTop (μ := κ) (s := fun n : ℕ => T ∩ Iic (n : ℝ)) hmono
    rw [hiUnion] at hlim
    exact hlim
  -- So eventually the value is exactly `0` (resp. `κ T`).
  obtain ⟨N, hAN⟩ : ∃ N : ℕ, κ (T ∩ Iic (-(N : ℝ))) = 0 := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ n : ℕ, κ (T ∩ Iic (-(n : ℝ))) = κ T := fun n => (hA_mem _).resolve_left (hcon n)
    have hconst : Tendsto (fun n : ℕ => κ (T ∩ Iic (-(n : ℝ)))) atTop (𝓝 (κ T)) := by
      exact (tendsto_congr hall).2 tendsto_const_nhds
    exact hTpos.ne' (tendsto_nhds_unique hA_atBot hconst).symm
  obtain ⟨M, hAM⟩ : ∃ M : ℕ, κ (T ∩ Iic (M : ℝ)) = κ T := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ n : ℕ, κ (T ∩ Iic (n : ℝ)) = 0 := fun n => (hA_mem _).resolve_right (hcon n)
    have hconst : Tendsto (fun n : ℕ => κ (T ∩ Iic (n : ℝ))) atTop (𝓝 0) := by
      exact (tendsto_congr hall).2 tendsto_const_nhds
    exact hTpos.ne' (tendsto_nhds_unique hA_atTop hconst)
  -- The set of `t` with cumulative value `κ T` is nonempty and bounded below.
  set S : Set ℝ := {t : ℝ | κ (T ∩ Iic t) = κ T} with hS_def
  have hS_ne : S.Nonempty := ⟨(M : ℝ), hAM⟩
  have hS_bdd : BddBelow S := by
    refine ⟨-(N : ℝ), fun t ht => ?_⟩
    by_contra hcon
    push Not at hcon
    have hle : κ (T ∩ Iic t) ≤ κ (T ∩ Iic (-(N : ℝ))) := hA_mono hcon.le
    rw [hAN] at hle
    have ht' : κ (T ∩ Iic t) = κ T := ht
    rw [ht'] at hle
    exact absurd hle (not_le.2 hTpos)
  set t₀ : ℝ := sInf S with ht₀_def
  have hS_upper : ∀ t ∈ S, ∀ t' : ℝ, t ≤ t' → t' ∈ S := by
    intro t ht t' ht'
    rcases hA_mem t' with h0 | hfull
    · exfalso
      have hle : κ (T ∩ Iic t) ≤ κ (T ∩ Iic t') := hA_mono ht'
      have ht'' : κ (T ∩ Iic t) = κ T := ht
      rw [ht'', h0] at hle
      exact absurd hle (not_le.2 hTpos)
    · exact hfull
  have hgt_mem : ∀ t : ℝ, t₀ < t → t ∈ S := by
    intro t ht
    obtain ⟨s, hsS, hs_lt⟩ := exists_lt_of_csInf_lt hS_ne (ht₀_def ▸ ht : sInf S < t)
    exact hS_upper s hsS t hs_lt.le
  -- Right continuity forces `t₀` itself into `S`.
  have ht₀_mem : t₀ ∈ S := by
    have hanti : Antitone (fun n : ℕ => T ∩ Iic (t₀ + (1 : ℝ) / (n + 1))) := fun m n hmn =>
      inter_subset_inter_right T (Iic_subset_Iic.2 (by
        have : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity)
            (by exact_mod_cast Nat.add_le_add_right hmn 1)
        linarith))
    have hiInter : (⋂ n : ℕ, T ∩ Iic (t₀ + (1 : ℝ) / (n + 1))) = T ∩ Iic t₀ := by
      ext x
      simp only [mem_iInter, mem_inter_iff, mem_Iic]
      constructor
      · intro hx
        refine ⟨(hx 0).1, ?_⟩
        by_contra hcon
        push Not at hcon
        have hxpos : 0 < x - t₀ := by linarith
        obtain ⟨n, hn⟩ := exists_nat_gt (1 / (x - t₀))
        rw [div_lt_iff₀ hxpos] at hn
        have hthis := (hx n).2
        have hy : x - t₀ ≤ 1 / ((n : ℝ) + 1) := by linarith
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)] at hy
        have hexp : (x - t₀) * ((n : ℝ) + 1) = (x - t₀) * (n : ℝ) + (x - t₀) := by ring
        nlinarith [hn, hy, hexp, hxpos]
      · intro hx n
        refine ⟨hx.1, ?_⟩
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith [hx.2]
    have hlim := tendsto_measure_iInter_atTop
      (s := fun n : ℕ => T ∩ Iic (t₀ + (1 : ℝ) / (n + 1)))
      (fun n => (hT.inter measurableSet_Iic).nullMeasurableSet)
      hanti ⟨0, (measure_lt_top κ _).ne⟩
    rw [hiInter] at hlim
    have hconst : Tendsto (fun n : ℕ => κ (T ∩ Iic (t₀ + (1 : ℝ) / (n + 1)))) atTop (𝓝 (κ T)) := by
      have hall : ∀ n : ℕ, κ (T ∩ Iic (t₀ + (1 : ℝ) / (n + 1))) = κ T := fun n =>
        hgt_mem _ (by
          have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          linarith)
      exact (tendsto_congr hall).2 tendsto_const_nhds
    exact tendsto_nhds_unique hlim hconst
  -- Everything strictly below `t₀` contributes nothing.
  have hnull_below : κ (T ∩ Iio t₀) = 0 := by
    have hmono : Monotone (fun n : ℕ => T ∩ Iic (t₀ - (1 : ℝ) / (n + 1))) := fun m n hmn =>
      inter_subset_inter_right T (Iic_subset_Iic.2 (by
        have : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity)
            (by exact_mod_cast Nat.add_le_add_right hmn 1)
        linarith))
    have hiUnion : (⋃ n : ℕ, T ∩ Iic (t₀ - (1 : ℝ) / (n + 1))) = T ∩ Iio t₀ := by
      ext x
      simp only [mem_iUnion, mem_inter_iff, mem_Iic, mem_Iio]
      constructor
      · rintro ⟨n, hx, hle⟩
        refine ⟨hx, ?_⟩
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      · rintro ⟨hx, hlt⟩
        have hxpos : 0 < t₀ - x := by linarith
        obtain ⟨n, hn⟩ := exists_nat_gt (1 / (t₀ - x))
        rw [div_lt_iff₀ hxpos] at hn
        refine ⟨n, hx, ?_⟩
        have hkey : (1 : ℝ) / ((n : ℝ) + 1) ≤ t₀ - x := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
          nlinarith
        linarith
    have hlim := tendsto_measure_iUnion_atTop (μ := κ)
      (s := fun n : ℕ => T ∩ Iic (t₀ - (1 : ℝ) / (n + 1))) hmono
    rw [hiUnion] at hlim
    have hconst : Tendsto (fun n : ℕ => κ (T ∩ Iic (t₀ - (1 : ℝ) / (n + 1)))) atTop (𝓝 0) := by
      have hnotmem : ∀ n : ℕ, t₀ - (1 : ℝ) / (n + 1) ∉ S := by
        intro n hmem
        have hle := csInf_le hS_bdd hmem
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        rw [← ht₀_def] at hle
        linarith
      have hall : ∀ n : ℕ, κ (T ∩ Iic (t₀ - (1 : ℝ) / (n + 1))) = 0 := fun n =>
        (hA_mem _).resolve_right (hnotmem n)
      exact (tendsto_congr hall).2 tendsto_const_nhds
    exact tendsto_nhds_unique hlim hconst
  -- Combine: `T ∩ {t₀}` carries all of `T`'s mass, contradicting `NullSingletonClass`.
  have hsplit : T ∩ Iic t₀ = (T ∩ Iio t₀) ∪ (T ∩ {t₀}) := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_union, mem_Iio, mem_singleton_iff]
    constructor
    · rintro ⟨hx, hle⟩
      rcases eq_or_lt_of_le hle with heq | hlt
      · exact Or.inr ⟨hx, heq⟩
      · exact Or.inl ⟨hx, hlt⟩
    · rintro (⟨hx, hlt⟩ | ⟨hx, heq⟩)
      · exact ⟨hx, hlt.le⟩
      · exact ⟨hx, heq.le⟩
  have hdisj : Disjoint (T ∩ Iio t₀) (T ∩ ({t₀} : Set ℝ)) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx1⟩ ⟨-, hx2⟩
    simp only [mem_Iio] at hx1
    simp only [mem_singleton_iff] at hx2
    exact absurd hx2 hx1.ne
  have hmeasT₀ : κ (T ∩ {t₀}) = κ T := by
    have hunion := measure_union (μ := κ) hdisj (hT.inter (measurableSet_singleton t₀))
    rw [← hsplit, hnull_below, zero_add] at hunion
    exact (ht₀_mem.symm.trans hunion).symm
  have hle : κ (T ∩ {t₀}) ≤ κ {t₀} := measure_mono inter_subset_right
  rw [measure_singleton, hmeasT₀] at hle
  exact absurd hle (not_le.2 hTpos)

/-- On the real line, a finite `NullSingletonClass` measure gives every positive-measure
measurable set a measurable, proper, positive-measure subset. -/
theorem exists_ssubset_measure_pos_lt
    {T : Set ℝ} (hT : MeasurableSet T) (hTpos : 0 < κ T) :
    ∃ V ⊆ T, MeasurableSet V ∧ 0 < κ V ∧ κ V < κ T := by
  by_contra hcon
  push Not at hcon
  exact not_forall_eq_zero_or_eq hT hTpos (fun V hVT hV => by
    rcases eq_or_lt_of_le (measure_mono hVT : κ V ≤ κ T) with heq | hlt
    · exact Or.inr heq
    · rcases eq_zero_or_pos (κ V) with h0 | hpos
      · exact Or.inl h0
      · exact absurd (hcon V hVT hV hpos) (not_le.2 hlt))

end Real

end ProofMet

end MultiplicativeErgodic
