/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal

public import LeanPool.MultiplicativeErgodic.Kingman
public import LeanPool.MultiplicativeErgodic.NonAtomic

/-!
# Nonatomic splitting and disjoint orbit translates
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter

open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Non-atomic splitting on `Ω`** (transport of `ProofMet.exists_ssubset_measure_pos_lt` from
`ℝ`). Every positive-measure set has a measurable subset of strictly smaller positive measure.
Proof: push `μ` forward along the measurable embedding `embeddingReal Ω`, apply the `ℝ`-version,
and pull the witness back. -/
theorem exists_ssubset_measure_pos_lt_omega [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {P : Set Ω} (hP : MeasurableSet P) (hPpos : 0 < μ P) :
    ∃ V ⊆ P, MeasurableSet V ∧ 0 < μ V ∧ μ V < μ P := by
  set e := embeddingReal Ω with he_def
  have he : MeasurableEmbedding e := measurableEmbedding_embeddingReal Ω
  set κ : Measure ℝ := μ.map e with hκ_def
  have : IsProbabilityMeasure κ :=
    by dsimp [κ]; infer_instance
  have : NullSingletonClass κ := by
    refine ⟨fun r => ?_⟩
    rw [hκ_def, Measure.map_apply he.measurable (measurableSet_singleton r)]
    apply Set.Subsingleton.measure_zero
    intro a ha b hb
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha hb
    exact he.injective (ha.trans hb.symm)
  have hTmeas : MeasurableSet (e '' P) := he.measurableSet_image.2 hP
  have hκT : κ (e '' P) = μ P := by
    rw [hκ_def, Measure.map_apply he.measurable hTmeas, Set.preimage_image_eq P he.injective]
  have hTpos : 0 < κ (e '' P) := by rw [hκT]; exact hPpos
  obtain ⟨W, hWT, hWmeas, hWpos, hWlt⟩ := ProofMet.exists_ssubset_measure_pos_lt hTmeas hTpos
  have hμW : μ (e ⁻¹' W) = κ W := by rw [hκ_def, Measure.map_apply he.measurable hWmeas]
  refine ⟨e ⁻¹' W, ?_, he.measurable hWmeas, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hyP, hey⟩ := hWT hx
    rwa [← he.injective hey]
  · rw [hμW]; exact hWpos
  · rw [hμW, ← hκT]; exact hWlt

/-- From non-atomicity: a positive-measure set contains, for every `m`, a family of `m` pairwise
disjoint positive-measure subsets, together with a positive-measure "remainder" `R` disjoint from
all of them. Proved by induction on `m`, peeling off one strictly-smaller positive piece from `R`
at each step via `exists_ssubset_measure_pos_lt_omega`. Only the finitely many indices `< m` are
guaranteed positive; the rest are `∅`. -/
theorem exists_disjoint_pos_family [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {P : Set Ω} (hP : MeasurableSet P) (hPpos : 0 < μ P) (m : ℕ) :
    ∃ (F : ℕ → Set Ω) (R : Set Ω), (∀ i, MeasurableSet (F i)) ∧ (∀ i, F i ⊆ P) ∧
      (∀ i j, i ≠ j → Disjoint (F i) (F j)) ∧ (∀ i, i < m → 0 < μ (F i)) ∧
      (∀ i, m ≤ i → F i = ∅) ∧
      MeasurableSet R ∧ R ⊆ P ∧ 0 < μ R ∧ (∀ i, Disjoint (F i) R) := by
  induction m with
  | zero =>
    exact ⟨fun _ => ∅, P, fun _ => MeasurableSet.empty, fun _ => Set.empty_subset _,
      fun _ _ _ => disjoint_bot_left, fun i hi => absurd hi (Nat.not_lt_zero i),
      fun _ _ => rfl, hP, subset_rfl, hPpos, fun _ => disjoint_bot_left⟩
  | succ m ih =>
    obtain ⟨F, R, hFmeas, hFsub, hFdisj, hFpos, hFempty, hRmeas, hRsub, hRpos, hFR⟩ := ih
    obtain ⟨V, hVR, hVmeas, hVpos, hVlt⟩ := exists_ssubset_measure_pos_lt_omega μ hRmeas hRpos
    have hRVpos : 0 < μ (R \ V) := by
      rw [measure_sdiff hVR hVmeas.nullMeasurableSet (measure_ne_top μ V)]
      exact tsub_pos_of_lt hVlt
    refine ⟨Function.update F m V, R \ V, ?_, ?_, ?_, ?_, ?_, hRmeas.diff hVmeas,
      Set.sdiff_subset.trans hRsub, hRVpos, ?_⟩
    · intro i
      rcases eq_or_ne i m with rfl | h
      · rw [Function.update_self]; exact hVmeas
      · rw [Function.update_of_ne h]; exact hFmeas i
    · intro i
      rcases eq_or_ne i m with rfl | h
      · rw [Function.update_self]; exact hVR.trans hRsub
      · rw [Function.update_of_ne h]; exact hFsub i
    · intro i j hij
      rcases eq_or_ne i m with rfl | hi
      · rw [Function.update_self, Function.update_of_ne (Ne.symm hij)]
        exact Disjoint.symm ((hFR j).mono_right hVR)
      · rcases eq_or_ne j m with rfl | hj
        · rw [Function.update_of_ne hi, Function.update_self]
          exact (hFR i).mono_right hVR
        · rw [Function.update_of_ne hi, Function.update_of_ne hj]; exact hFdisj i j hij
    · intro i hi
      rcases eq_or_ne i m with rfl | h
      · rw [Function.update_self]; exact hVpos
      · rw [Function.update_of_ne h]; exact hFpos i (by omega)
    · intro i hi
      rw [Function.update_of_ne (by omega : i ≠ m)]; exact hFempty i (by omega)
    · intro i
      rcases eq_or_ne i m with rfl | h
      · rw [Function.update_self]; exact Set.disjoint_left.mpr (fun a haV haRV => haRV.2 haV)
      · rw [Function.update_of_ne h]; exact (hFR i).mono_right Set.sdiff_subset

/-- **Non-periodicity (Rudolph's standing hypothesis), proved from ergodicity + non-atomicity.**
For every period `N ≥ 1`, the set of `N`-periodic points is null.

Proof. Write `P = {x | σ^[N] x = x}` and suppose `μ P > 0`. For any positive-measure `F ⊆ P`,
the union `U = ⋃_{i < N} σ^i F` of the `N` iterates is `σ`-invariant (`σ` cyclically permutes
each finite orbit segment `{y, …, σ^{N-1}y}` with `y ∈ P`), hence has measure `0` or `1` by
ergodicity; being `≥ μ F > 0` it has measure `1`, so `1 = μ U ≤ N · μ F`, i.e. every positive
subset of `P` has measure `≥ 1/N`. But non-atomicity supplies `N+1` *disjoint* positive-measure
subsets of `P`; each has measure `≥ 1/N`, so their disjoint union has measure `≥ (N+1)/N > 1`,
contradicting `μ ≤ 1`. -/
theorem periodic_null [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (σ : Ω ≃ᵐ Ω) (hσ : Ergodic (⇑σ) μ) {N : ℕ} (hN : 1 ≤ N) :
    μ {x | σ^[N] x = x} = 0 := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hσiter : Measurable (⇑σ)^[M + 1] := σ.measurable.iterate (M + 1)
  have hPmeas : MeasurableSet {x | (⇑σ)^[M + 1] x = x} := measurableSet_eq_fun hσiter measurable_id
  by_contra hPne
  have hPpos : 0 < μ {x | (⇑σ)^[M + 1] x = x} :=
    lt_of_le_of_ne bot_le (Ne.symm hPne)
  have hmp : MeasurePreserving (⇑σ) μ μ := hσ.toMeasurePreserving
  have hmpsymm : MeasurePreserving (⇑σ.symm) μ μ := hmp.symm σ
  have hemb : ∀ i, MeasurableEmbedding (⇑σ)^[i] := by
    intro i
    induction i with
    | zero => rw [Function.iterate_zero]; exact MeasurableEmbedding.id
    | succ k ihk => rw [Function.iterate_succ]; exact ihk.comp σ.measurableEmbedding
  -- Measure of a set is preserved under the (bijective, measure-preserving) iterate `σ^[i]`.
  have himg : ∀ (i : ℕ) (S : Set Ω), MeasurableSet S → μ ((⇑σ)^[i] '' S) = μ S := by
    intro i S hS
    have hL : Function.LeftInverse (⇑σ.symm) (⇑σ) := σ.symm_apply_apply
    have hR : Function.RightInverse (⇑σ.symm) (⇑σ) := σ.apply_symm_apply
    have hinv : (⇑σ)^[i] '' S = (⇑σ.symm)^[i] ⁻¹' S :=
      congrFun (Set.image_eq_preimage_of_inverse (hL.iterate i) (hR.iterate i)) S
    rw [hinv]; exact (hmpsymm.iterate i).measure_preimage hS.nullMeasurableSet
  -- Ergodic lower bound: every positive-measure subset of the periodic set has measure `≥ 1/N`.
  have key : ∀ F : Set Ω, MeasurableSet F → F ⊆ {x | (⇑σ)^[M + 1] x = x} → 0 < μ F →
      (1 : ℝ≥0∞) ≤ ((M + 1 : ℕ) : ℝ≥0∞) * μ F := by
    intro F hFmeas hFsub hFpos
    have hUmeas : MeasurableSet (⋃ i ∈ Finset.range (M + 1), (⇑σ)^[i] '' F) :=
      Finset.measurableSet_biUnion _ (fun i _ => (hemb i).measurableSet_image.2 hFmeas)
    have hUinv : (⇑σ) ⁻¹' (⋃ i ∈ Finset.range (M + 1), (⇑σ)^[i] '' F)
        = ⋃ i ∈ Finset.range (M + 1), (⇑σ)^[i] '' F := by
      ext x
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image, Finset.mem_range, exists_prop]
      constructor
      · rintro ⟨i, hi, y, hyF, hxy⟩
        rcases Nat.eq_zero_or_pos i with rfl | hipos
        · simp only [Function.iterate_zero, id_eq] at hxy
          refine ⟨M, by omega, y, hyF, ?_⟩
          have hyP : (⇑σ)^[M + 1] y = y := hFsub hyF
          have hcalc : σ ((⇑σ)^[M] y) = σ x := by
            rw [← Function.iterate_succ_apply' (⇑σ) M y, hyP, hxy]
          exact σ.injective hcalc
        · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
          refine ⟨k, by omega, y, hyF, ?_⟩
          rw [Function.iterate_succ_apply'] at hxy
          exact σ.injective hxy
      · rintro ⟨i, hi, y, hyF, hxy⟩
        by_cases hlast : i + 1 = M + 1
        · refine ⟨0, by omega, y, hyF, ?_⟩
          have hyP : (⇑σ)^[M + 1] y = y := hFsub hyF
          -- goal: `(⇑σ)^[0] y = ⇑σ x`, i.e. `y = ⇑σ x`; `hxy : (⇑σ)^[i] y = ⇑σ x`.
          -- Capturing `iterate_succ_apply'` into an annotated `show` forces the exponent to appear
          -- as the literal `i + 1`, so the subsequent `rw [hlast]` fires (the previous attempt let
          -- the lemma produce `Nat.succ i`, which `rw [show i + 1 = M + 1 ..]` failed to match).
          simp only [Function.iterate_zero, id_eq]
          rw [← hxy,
            show ⇑σ ((⇑σ)^[i] y) = (⇑σ)^[i + 1] y from (Function.iterate_succ_apply' (⇑σ) i y).symm,
            show i + 1 = M + 1 from hlast]
          exact hyP.symm
        · refine ⟨i + 1, by omega, y, hyF, ?_⟩
          rw [Function.iterate_succ_apply', hxy]
    have hUmu : μ (⋃ i ∈ Finset.range (M + 1), (⇑σ)^[i] '' F)
        ≤ ((M + 1 : ℕ) : ℝ≥0∞) * μ F := by
      calc μ (⋃ i ∈ Finset.range (M + 1), (⇑σ)^[i] '' F)
            ≤ ∑ i ∈ Finset.range (M + 1), μ ((⇑σ)^[i] '' F) := measure_biUnion_finset_le _ _
        _ = ∑ _i ∈ Finset.range (M + 1), μ F := Finset.sum_congr rfl (fun i _ => himg i F hFmeas)
        _ = ((M + 1 : ℕ) : ℝ≥0∞) * μ F := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hUzo := hσ.toPreErgodic.prob_eq_zero_or_one hUmeas.nullMeasurableSet (by rw [hUinv])
    have hFU : μ F ≤ μ (⋃ i ∈ Finset.range (M + 1), (⇑σ)^[i] '' F) := by
      refine measure_mono (fun z hz => ?_)
      exact Set.mem_iUnion₂.mpr ⟨0, Finset.mem_range.mpr (by omega), by simpa using hz⟩
    have hU1 : μ (⋃ i ∈ Finset.range (M + 1), (⇑σ)^[i] '' F) = 1 := by
      rcases hUzo with h | h
      · rw [h] at hFU; exact absurd (le_antisymm hFU bot_le) hFpos.ne'
      · exact h
    rw [← hU1]; exact hUmu
  -- Non-atomicity supplies `M+2` disjoint positive-measure subsets; contradiction.
  obtain ⟨F, _R, hFmeas, hFsub, hFdisj, hFpos, _, _, _, _, _⟩ :=
    exists_disjoint_pos_family μ hPmeas hPpos (M + 2)
  have hdisj' : (↑(Finset.range (M + 2)) : Set ℕ).PairwiseDisjoint F :=
    fun i _ j _ hij => hFdisj i j hij
  have hsum_le : ∑ i ∈ Finset.range (M + 2), μ (F i) ≤ 1 := by
    rw [← measure_biUnion_finset hdisj' (fun i _ => hFmeas i)]
    calc μ (⋃ i ∈ Finset.range (M + 2), F i)
          ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hlow : ((M + 2 : ℕ) : ℝ≥0∞)
      ≤ ((M + 1 : ℕ) : ℝ≥0∞) * ∑ i ∈ Finset.range (M + 2), μ (F i) := by
    rw [Finset.mul_sum]
    calc ((M + 2 : ℕ) : ℝ≥0∞) = ∑ _i ∈ Finset.range (M + 2), (1 : ℝ≥0∞) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      _ ≤ ∑ i ∈ Finset.range (M + 2), ((M + 1 : ℕ) : ℝ≥0∞) * μ (F i) :=
            Finset.sum_le_sum (fun i hi =>
              key (F i) (hFmeas i) (hFsub i) (hFpos i (Finset.mem_range.mp hi)))
  have hcontra : ((M + 2 : ℕ) : ℝ≥0∞) ≤ ((M + 1 : ℕ) : ℝ≥0∞) :=
    calc ((M + 2 : ℕ) : ℝ≥0∞)
          ≤ ((M + 1 : ℕ) : ℝ≥0∞) * ∑ i ∈ Finset.range (M + 2), μ (F i) := hlow
      _ ≤ ((M + 1 : ℕ) : ℝ≥0∞) * 1 := by gcongr
      _ = ((M + 1 : ℕ) : ℝ≥0∞) := mul_one _
  have : (M + 2 : ℕ) ≤ (M + 1 : ℕ) := by exact_mod_cast hcontra
  omega

/-- Shared machinery for `exists_subset_disjoint_iterates` and its symmetric
form `exists_subset_disjoint_iterates_symm`: from a positive-measure `A` and ergodicity, produce
a positive-measure `B ⊆ A` whose first `K` forward shifts are each disjoint from `B` itself,
`Disjoint B (σ^[d] '' B)` for `d = 1, …, K`. Proof: a single-shift-disjointification step
(`periodic_null` + separating a positive fraction of `A₀` across a cut of a real embedding),
iterated over `d = 1, …, K`, shrinking the subset each step so earlier disjointness is
inherited. -/
private lemma disjoint_forward_shifts [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] (σ : Ω ≃ᵐ Ω) (hσ : Ergodic (⇑σ) μ)
    (K : ℕ) {A : Set Ω} (hA : MeasurableSet A) (hApos : 0 < μ A) :
    ∃ B, B ⊆ A ∧ MeasurableSet B ∧ 0 < μ B ∧
      ∀ d : ℕ, 1 ≤ d → d ≤ K → Disjoint B ((⇑σ)^[d] '' B) := by
  classical
  -- **Single-shift lemma.** For every period `d ≥ 1`, any positive-measure set has a
  -- positive-measure subset disjoint from its own `σ^[d]`-image. Proof: `σ^[d] x ≠ x` a.e.
  -- (`periodic_null`); via the measurable embedding `e = embeddingReal` into `ℝ` and a rational
  -- separating `q`, a positive fraction of `A₀` is sent from `{e < q}` into `{e ≥ q}` (or the
  -- reverse), and that piece is disjoint from its image.
  have shift : ∀ (d : ℕ), 1 ≤ d → ∀ (A₀ : Set Ω), MeasurableSet A₀ → 0 < μ A₀ →
      ∃ B, B ⊆ A₀ ∧ MeasurableSet B ∧ 0 < μ B ∧ Disjoint B ((⇑σ)^[d] '' B) := by
    intro d hd A₀ hA₀ hA₀pos
    set φ : Ω → Ω := (⇑σ)^[d] with hφdef
    have hφmeas : Measurable φ := σ.measurable.iterate d
    have hfix : μ {x | φ x = x} = 0 := periodic_null μ σ hσ hd
    set e : Ω → ℝ := embeddingReal Ω with hedef
    have he : MeasurableEmbedding e := measurableEmbedding_embeddingReal Ω
    have hSqmeas : ∀ q : ℚ, MeasurableSet {x : Ω | e x < (q : ℝ)} :=
      fun q => he.measurable measurableSet_Iio
    have hφpreimeas : ∀ q : ℚ, MeasurableSet {x : Ω | e (φ x) < (q : ℝ)} :=
      fun q => (he.measurable.comp hφmeas) measurableSet_Iio
    set U : ℚ → Set Ω :=
      fun q => A₀ ∩ {x | e x < (q : ℝ)} ∩ {x | ¬ (e (φ x) < (q : ℝ))} with hUdef
    set V : ℚ → Set Ω :=
      fun q => A₀ ∩ {x | ¬ (e x < (q : ℝ))} ∩ {x | e (φ x) < (q : ℝ)} with hVdef
    have hUmeas : ∀ q, MeasurableSet (U q) :=
      fun q => (hA₀.inter (hSqmeas q)).inter (hφpreimeas q).compl
    have hVmeas : ∀ q, MeasurableSet (V q) :=
      fun q => (hA₀.inter (hSqmeas q).compl).inter (hφpreimeas q)
    set WW : ℚ → Set Ω := fun q => U q ∪ V q with hWWdef
    have hcover : A₀ ⊆ (⋃ q, WW q) ∪ {x | φ x = x} := by
      intro x hx
      by_cases hfixx : φ x = x
      · exact Or.inr hfixx
      · refine Or.inl (Set.mem_iUnion.mpr ?_)
        have hne : e x ≠ e (φ x) := fun h => hfixx (he.injective h.symm)
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
          exact ⟨q, Or.inl ⟨⟨hx, hq1⟩, not_lt.mpr (le_of_lt hq2)⟩⟩
        · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hgt
          exact ⟨q, Or.inr ⟨⟨hx, not_lt.mpr (le_of_lt hq2)⟩, hq1⟩⟩
    have hexists : ∃ q, 0 < μ (U q) ∨ 0 < μ (V q) := by
      by_contra hcon
      have hall : ∀ q, μ (WW q) = 0 := by
        intro q
        have h1 : μ (U q) = 0 := by
          by_contra h; exact hcon ⟨q, Or.inl (lt_of_le_of_ne bot_le (Ne.symm h))⟩
        have h2 : μ (V q) = 0 := by
          by_contra h; exact hcon ⟨q, Or.inr (lt_of_le_of_ne bot_le (Ne.symm h))⟩
        have hle : μ (WW q) ≤ μ (U q) + μ (V q) := measure_union_le _ _
        rw [h1, h2, add_zero] at hle
        exact le_antisymm hle bot_le
      have hUnull : μ (⋃ q, WW q) = 0 := measure_iUnion_null hall
      have hle : μ A₀ ≤ 0 :=
        calc μ A₀ ≤ μ ((⋃ q, WW q) ∪ {x | φ x = x}) := measure_mono hcover
          _ ≤ μ (⋃ q, WW q) + μ {x | φ x = x} := measure_union_le _ _
          _ = 0 := by rw [hUnull, hfix, add_zero]
      exact absurd (le_antisymm hle bot_le) hA₀pos.ne'
    obtain ⟨q, hq⟩ := hexists
    rcases hq with hq | hq
    · refine ⟨U q, fun x hx => hx.1.1, hUmeas q, hq, ?_⟩
      rw [Set.disjoint_left]
      rintro w hwB ⟨x, hxB, rfl⟩
      exact hxB.2 hwB.1.2
    · refine ⟨V q, fun x hx => hx.1.1, hVmeas q, hq, ?_⟩
      rw [Set.disjoint_left]
      rintro w hwB ⟨x, hxB, rfl⟩
      exact hwB.1.2 hxB.2
  -- Iterate `shift` over the shifts `d = 1, …, K'`, shrinking the subset each step.
  have main : ∀ K' : ℕ, ∃ B, B ⊆ A ∧ MeasurableSet B ∧ 0 < μ B ∧
      ∀ d : ℕ, 1 ≤ d → d ≤ K' → Disjoint B ((⇑σ)^[d] '' B) := by
    intro K'
    induction K' with
    | zero =>
        refine ⟨A, subset_rfl, hA, hApos, ?_⟩
        intro d hd1 hd0
        exact absurd hd0 (by omega)
    | succ K' ih =>
        obtain ⟨B, hBA, hBmeas, hBpos, hBdisj⟩ := ih
        obtain ⟨C, hCB, hCmeas, hCpos, hCdisj⟩ := shift (K' + 1) (by omega) B hBmeas hBpos
        refine ⟨C, hCB.trans hBA, hCmeas, hCpos, ?_⟩
        intro d hd1 hdK
        rcases Nat.lt_or_ge d (K' + 1) with hlt | hge
        · have hdK' : d ≤ K' := by omega
          exact (hBdisj d hd1 hdK').mono hCB (Set.image_mono hCB)
        · have hdeq : d = K' + 1 := by omega
          rw [hdeq]; exact hCdisj
  exact main K

/-- **Rudolph's disjoint-translates lemma**, built on `periodic_null` via ergodicity.
Any positive-measure set
`A` has a positive-measure measurable subset `A'` whose one-sided forward translates
`A', σA', …, σ^{N-1}A'` are pairwise disjoint, for any `N`.

Rudolph proves this by contrapositive: if no such `A'` existed, a maximality argument (take a
sequence of subsets approaching the supremum of achievable disjoint-translate measure, use
continuity of measure along the union) forces `A` to be `σ^{N₀}`-invariant a.e. for some
`N₀ < N`, and then a refining-partition-tree argument turns that into "a.e. point of `A` is
`σ^{N₀}`-periodic" -- impossible for ergodic `σ` on a non-atomic space (`periodic_null`).

This is the entry point that consumes `periodic_null`.
The covering and assembly steps below cite only its
*statement*. -/
theorem exists_subset_disjoint_iterates [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] (σ : Ω ≃ᵐ Ω) (hσ : Ergodic (⇑σ) μ)
    (N : ℕ) {A : Set Ω} (hA : MeasurableSet A) (hApos : 0 < μ A) :
    ∃ A' ⊆ A, MeasurableSet A' ∧ 0 < μ A' ∧
      ∀ i < N, ∀ k < N, i ≠ k → Disjoint ((⇑σ)^[i] '' A') ((⇑σ)^[k] '' A') := by
  classical
  obtain ⟨B, hBA, hBmeas, hBpos, hBdisj⟩ := disjoint_forward_shifts μ σ hσ (N - 1) hA hApos
  -- Two translates `σ^[i]B`, `σ^[k]B` are disjoint iff `B ∩ σ^[k-i]B = ∅` (apply the bijection
  -- `σ^[-i]`, i.e. `zIter σ (-i)`). As `i, k` range over `{0,…,N-1}`, `|k-i|` ranges over
  -- `1,…,N-1`, exactly the shifts `disjoint_forward_shifts` already handles.
  set g : Equiv.Perm Ω := σ.toEquiv with hgdef
  have hcoeg : (⇑g : Ω → Ω) = ⇑σ := rfl
  have hcoeginv : (⇑(g⁻¹) : Ω → Ω) = ⇑σ.symm := rfl
  have hzeq : ∀ n : ℤ, zIter σ n = ⇑(g ^ n) := by
    intro n
    cases n with
    | ofNat m =>
        change (fun ω => (⇑σ)^[m] ω) = ⇑(g ^ (Int.ofNat m))
        rw [show (Int.ofNat m : ℤ) = (m : ℤ) from rfl, zpow_natCast, Equiv.Perm.coe_pow, hcoeg]
    | negSucc m =>
        change (fun ω => (⇑σ.symm)^[m + 1] ω) = ⇑(g ^ (Int.negSucc m))
        rw [zpow_negSucc, ← inv_pow, Equiv.Perm.coe_pow, hcoeginv]
  have hzcomp : ∀ (a b : ℤ) (x : Ω), zIter σ a (zIter σ b x) = zIter σ (a + b) x := by
    intro a b x
    rw [hzeq a, hzeq b, hzeq (a + b), ← Equiv.Perm.mul_apply, ← zpow_add]
  have hzzero : ∀ x : Ω, zIter σ (0 : ℤ) x = x := by
    intro x; rw [hzeq (0 : ℤ), zpow_zero]; rfl
  have hznat : ∀ (n : ℕ) (x : Ω), zIter σ (n : ℤ) x = (⇑σ)^[n] x := by
    intro n x
    rw [hzeq, zpow_natCast, Equiv.Perm.coe_pow, hcoeg]
  refine ⟨B, hBA, hBmeas, hBpos, ?_⟩
  intro i hi k hk hik
  rw [Set.disjoint_left]
  rintro w ⟨x, hxB, hxw⟩ ⟨y, hyB, hyw⟩
  have hxy : zIter σ (i : ℤ) x = zIter σ (k : ℤ) y := by rw [hznat, hznat, hxw, hyw]
  have h1 : zIter σ (-(i : ℤ)) (zIter σ (i : ℤ) x) = x := by
    rw [hzcomp, show (-(i : ℤ) + i : ℤ) = 0 from by ring]; exact hzzero x
  have h2 : zIter σ (-(i : ℤ)) (zIter σ (k : ℤ) y) = zIter σ ((k : ℤ) - i) y := by
    rw [hzcomp, show (-(i : ℤ) + k : ℤ) = (k : ℤ) - i from by ring]
  have hkey : x = zIter σ ((k : ℤ) - i) y :=
    calc x = zIter σ (-(i : ℤ)) (zIter σ (i : ℤ) x) := h1.symm
      _ = zIter σ (-(i : ℤ)) (zIter σ (k : ℤ) y) := by rw [hxy]
      _ = zIter σ ((k : ℤ) - i) y := h2
  set d : ℤ := (k : ℤ) - i with hd
  have hd0 : d ≠ 0 := by omega
  rcases lt_or_gt_of_ne hd0 with hdlt | hdgt
  · -- `d < 0`, i.e. `k < i`: then `x = σ^[(-d).toNat] y`, contradicting
    -- `Disjoint B (σ^[(-d)] '' B)`.
    set n : ℕ := (-d).toNat with hndef
    have hn1 : 1 ≤ n := by omega
    have hn2 : n ≤ N - 1 := by omega
    have hdn : (n : ℤ) = -d := by rw [hndef]; exact Int.toNat_of_nonneg (by omega)
    have hyx : zIter σ (-d) x = y :=
      calc zIter σ (-d) x = zIter σ (-d) (zIter σ d y) := by rw [hkey]
        _ = zIter σ (-d + d) y := by rw [hzcomp]
        _ = zIter σ 0 y := by rw [show (-d + d : ℤ) = 0 from by ring]
        _ = y := hzzero y
    have hyeq : (⇑σ)^[n] x = y := by rw [← hznat n x, hdn]; exact hyx
    exact Set.disjoint_left.mp (hBdisj n hn1 hn2) hyB ⟨x, hxB, hyeq⟩
  · -- `d > 0`, i.e. `i < k`: then `y = σ^[d.toNat] x`, contradicting `Disjoint B (σ^[d] '' B)`.
    set n : ℕ := d.toNat with hndef
    have hn1 : 1 ≤ n := by omega
    have hn2 : n ≤ N - 1 := by omega
    have hdn : (n : ℤ) = d := by rw [hndef]; exact Int.toNat_of_nonneg (by omega)
    have hxeq : (⇑σ)^[n] y = x := by rw [← hznat n y, hdn]; exact hkey.symm
    exact Set.disjoint_left.mp (hBdisj n hn1 hn2) hxB ⟨y, hyB, hxeq⟩

/-- **Symmetric corollary** of `exists_subset_disjoint_iterates`, in the shape
`vitali_cover_third`'s covering argument uses internally: `2N+1` translates `zIter σ i '' A'`
for `i ∈ {-N,…,N}` pairwise disjoint, for any window radius `N`, rather than Rudolph's `N`
one-sided translates. Built from the same `disjoint_forward_shifts` machinery at `K = 2N`
(differences `k - i` for `i, k ∈ {-N,…,N}` range over `{-2N,…,2N}`, exactly the shifts it
handles), not derived from `exists_subset_disjoint_iterates` itself: shifting that lemma's
witness by `σ^{-N}` to recenter it would break the required `A' ⊆ A`, since `A` need not be
`σ`-invariant. -/
theorem exists_subset_disjoint_iterates_symm [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] (σ : Ω ≃ᵐ Ω) (hσ : Ergodic (⇑σ) μ)
    (N : ℕ) {A : Set Ω} (hA : MeasurableSet A) (hApos : 0 < μ A) :
    ∃ A' ⊆ A, MeasurableSet A' ∧ 0 < μ A' ∧
      ∀ i ∈ Set.Icc (-(N : ℤ)) N, ∀ k ∈ Set.Icc (-(N : ℤ)) N, i ≠ k →
        Disjoint (zIter σ i '' A') (zIter σ k '' A') := by
  classical
  obtain ⟨B, hBA, hBmeas, hBpos, hBdisj⟩ := disjoint_forward_shifts μ σ hσ (2 * N) hA hApos
  set g : Equiv.Perm Ω := σ.toEquiv with hgdef
  have hcoeg : (⇑g : Ω → Ω) = ⇑σ := rfl
  have hcoeginv : (⇑(g⁻¹) : Ω → Ω) = ⇑σ.symm := rfl
  have hzeq : ∀ n : ℤ, zIter σ n = ⇑(g ^ n) := by
    intro n
    cases n with
    | ofNat m =>
        change (fun ω => (⇑σ)^[m] ω) = ⇑(g ^ (Int.ofNat m))
        rw [show (Int.ofNat m : ℤ) = (m : ℤ) from rfl, zpow_natCast, Equiv.Perm.coe_pow, hcoeg]
    | negSucc m =>
        change (fun ω => (⇑σ.symm)^[m + 1] ω) = ⇑(g ^ (Int.negSucc m))
        rw [zpow_negSucc, ← inv_pow, Equiv.Perm.coe_pow, hcoeginv]
  have hzcomp : ∀ (a b : ℤ) (x : Ω), zIter σ a (zIter σ b x) = zIter σ (a + b) x := by
    intro a b x
    rw [hzeq a, hzeq b, hzeq (a + b), ← Equiv.Perm.mul_apply, ← zpow_add]
  have hzzero : ∀ x : Ω, zIter σ (0 : ℤ) x = x := by
    intro x; rw [hzeq (0 : ℤ), zpow_zero]; rfl
  have hznat : ∀ (n : ℕ) (x : Ω), zIter σ (n : ℤ) x = (⇑σ)^[n] x := by
    intro n x
    rw [hzeq, zpow_natCast, Equiv.Perm.coe_pow, hcoeg]
  refine ⟨B, hBA, hBmeas, hBpos, ?_⟩
  intro i hi k hk hik
  obtain ⟨hi1, hi2⟩ := Set.mem_Icc.mp hi
  obtain ⟨hk1, hk2⟩ := Set.mem_Icc.mp hk
  rw [Set.disjoint_left]
  rintro w ⟨x, hxB, hxw⟩ ⟨y, hyB, hyw⟩
  have hxy : zIter σ i x = zIter σ k y := by rw [hxw, hyw]
  have h1 : zIter σ (-i) (zIter σ i x) = x := by
    rw [hzcomp, show (-i + i : ℤ) = 0 from by omega]; exact hzzero x
  have h2 : zIter σ (-i) (zIter σ k y) = zIter σ (k - i) y := by
    rw [hzcomp, show (-i + k : ℤ) = k - i from by omega]
  have hkey : x = zIter σ (k - i) y :=
    calc x = zIter σ (-i) (zIter σ i x) := h1.symm
      _ = zIter σ (-i) (zIter σ k y) := by rw [hxy]
      _ = zIter σ (k - i) y := h2
  set d : ℤ := k - i with hd
  have hd0 : d ≠ 0 := by omega
  rcases lt_or_gt_of_ne hd0 with hdlt | hdgt
  · -- `d < 0`: then `y = σ^[(-d).toNat] x`, contradicting `Disjoint B (σ^[(-d)] '' B)`.
    set n : ℕ := (-d).toNat with hndef
    have hn1 : 1 ≤ n := by omega
    have hn2 : n ≤ 2 * N := by omega
    have hdn : (n : ℤ) = -d := by rw [hndef]; exact Int.toNat_of_nonneg (by omega)
    have hyx : zIter σ (-d) x = y :=
      calc zIter σ (-d) x = zIter σ (-d) (zIter σ d y) := by rw [hkey]
        _ = zIter σ (-d + d) y := by rw [hzcomp]
        _ = zIter σ 0 y := by rw [show (-d + d : ℤ) = 0 from by omega]
        _ = y := hzzero y
    have hyeq : (⇑σ)^[n] x = y := by rw [← hznat n x, hdn]; exact hyx
    exact Set.disjoint_left.mp (hBdisj n hn1 hn2) hyB ⟨x, hxB, hyeq⟩
  · -- `d > 0`: then `x = σ^[d.toNat] y`, contradicting `Disjoint B (σ^[d] '' B)`.
    set n : ℕ := d.toNat with hndef
    have hn1 : 1 ≤ n := by omega
    have hn2 : n ≤ 2 * N := by omega
    have hdn : (n : ℤ) = d := by rw [hndef]; exact Int.toNat_of_nonneg (by omega)
    have hxeq : (⇑σ)^[n] y = x := by rw [← hznat n y, hdn]; exact hkey.symm
    exact Set.disjoint_left.mp (hBdisj n hn1 hn2) hxB ⟨y, hyB, hxeq⟩

/-! ### Infrastructure for `vitali_cover_third`.

The two-sided iteration `zIter σ` is the `ℤ`-action of `σ` by measure-preserving bijections.
These lemmas package that action (group law, measurability, measure-preservation, image
measure) and the elementary window-counting bound that the covering argument needs. They are
proved in full and are independent of the greedy construction. -/

/-- `zIter σ` is the `ℤ`-power of `σ` in the permutation group `Ω ≃ Ω`. -/
lemma zIter_eq_zpow (σ : Ω ≃ᵐ Ω) (t : ℤ) : zIter σ t = ⇑(σ.toEquiv ^ t) := by
  cases t with
  | ofNat n =>
    ext ω
    rw [show (Int.ofNat n : ℤ) = (n : ℤ) from rfl, zpow_natCast, Equiv.Perm.coe_pow]
    rfl
  | negSucc n =>
    ext ω
    rw [zpow_negSucc, ← inv_pow, Equiv.Perm.coe_pow]
    rfl

/-- Group law for the two-sided iteration: `zIter σ (a + b) = zIter σ a ∘ zIter σ b`. -/
lemma zIter_add (σ : Ω ≃ᵐ Ω) (a b : ℤ) (ω : Ω) :
    zIter σ (a + b) ω = zIter σ a (zIter σ b ω) := by
  rw [zIter_eq_zpow, zIter_eq_zpow, zIter_eq_zpow, zpow_add]
  rfl

/-- `zIter σ 0` is the identity. -/
lemma zIter_zero_apply (σ : Ω ≃ᵐ Ω) (ω : Ω) : zIter σ 0 ω = ω := by
  rw [zIter_eq_zpow, zpow_zero]; rfl

/-- Each translate `zIter σ t` is measurable. -/
lemma measurable_zIter (σ : Ω ≃ᵐ Ω) (t : ℤ) : Measurable (zIter σ t) := by
  cases t with
  | ofNat n => exact σ.measurable.iterate n
  | negSucc n => exact σ.symm.measurable.iterate (n + 1)

/-- Under an ergodic (hence measure-preserving) `σ`, each translate `zIter σ t` preserves `μ`. -/
lemma measurePreserving_zIter {μ : Measure Ω} (σ : Ω ≃ᵐ Ω)
    (hσ : Ergodic (⇑σ) μ) (t : ℤ) : MeasurePreserving (zIter σ t) μ μ := by
  cases t with
  | ofNat n => exact hσ.toMeasurePreserving.iterate n
  | negSucc n => exact (MeasurePreserving.symm σ hσ.toMeasurePreserving).iterate (n + 1)

/-- Each translate preserves the measure of a set (`μ (zIter σ t '' s) = μ s`), because
`zIter σ t` is a measure-preserving bijection with inverse `zIter σ (-t)`. -/
lemma measure_zIter_image {μ : Measure Ω} (σ : Ω ≃ᵐ Ω) (hσ : Ergodic (⇑σ) μ)
    (t : ℤ) {s : Set Ω} (hs : MeasurableSet s) : μ (zIter σ t '' s) = μ s := by
  have hinv : zIter σ t '' s = zIter σ (-t) ⁻¹' s := by
    have h := Set.image_eq_preimage_of_inverse (f := zIter σ t) (g := zIter σ (-t))
      (fun ω => by rw [← zIter_add]; simp [zIter_zero_apply])
      (fun ω => by rw [← zIter_add]; simp [zIter_zero_apply])
    exact congrFun h s
  rw [hinv]
  exact (measurePreserving_zIter σ hσ (-t)).measure_preimage hs.nullMeasurableSet

/-- **Window-counting bound.** The union of the `2r+1` translates of a measurable set `S`
over the symmetric index window `Icc (-r) r` has measure at most `(2r+1) · μ S`. This is the
elementary "length of the window" estimate that produces the factor in the Vitali bound. -/
lemma measure_iUnion_zIter_window_le {μ : Measure Ω} (σ : Ω ≃ᵐ Ω)
    (hσ : Ergodic (⇑σ) μ) (r : ℕ) {S : Set Ω} (hS : MeasurableSet S) :
    μ (⋃ t ∈ Set.Icc (-(r : ℤ)) r, zIter σ t '' S) ≤ (2 * r + 1) * μ S := by
  have hbi : (⋃ t ∈ Set.Icc (-(r : ℤ)) r, zIter σ t '' S)
      = ⋃ t ∈ (Finset.Icc (-(r : ℤ)) r), zIter σ t '' S := by
    apply Set.iUnion_congr; intro t; simp only [Set.mem_Icc, Finset.mem_Icc]
  rw [hbi]
  refine le_trans (measure_biUnion_finset_le _ _) (le_of_eq ?_)
  have hcard : (Finset.Icc (-(r : ℤ)) r).card = 2 * r + 1 := by
    rw [Int.card_Icc]; omega
  calc ∑ t ∈ Finset.Icc (-(r : ℤ)) r, μ (zIter σ t '' S)
      = ∑ _t ∈ Finset.Icc (-(r : ℤ)) r, μ S := by
        apply Finset.sum_congr rfl; intro t _; exact measure_zIter_image σ hσ t hS
    _ = (Finset.Icc (-(r : ℤ)) r).card • μ S := by rw [Finset.sum_const]
    _ = (2 * r + 1) * μ S := by rw [hcard, nsmul_eq_mul]; push_cast; ring

/-- Each translate `zIter σ t '' s` of a measurable set is measurable (`zIter σ t` is a
measurable bijection with measurable inverse `zIter σ (-t)`, so the image is the preimage
under the inverse). -/
lemma measurableSet_zIter_image (σ : Ω ≃ᵐ Ω) (t : ℤ) {s : Set Ω}
    (hs : MeasurableSet s) : MeasurableSet (zIter σ t '' s) := by
  have hinv : zIter σ t '' s = zIter σ (-t) ⁻¹' s := by
    have h := Set.image_eq_preimage_of_inverse (f := zIter σ t) (g := zIter σ (-t))
      (fun ω => by rw [← zIter_add]; simp [zIter_zero_apply])
      (fun ω => by rw [← zIter_add]; simp [zIter_zero_apply])
    exact congrFun h s
  rw [hinv]; exact (measurable_zIter σ (-t)) hs

/-- **Window-counting equality (disjoint case).** When the `2r+1` translates of `S` over the
symmetric window `Icc (-r) r` are pairwise disjoint, their union has measure *exactly*
`(2r+1) · μ S`. This is the equality companion of `measure_iUnion_zIter_window_le`, and is what
turns the greedy construction's per-level disjointness into the exact `Σ (2r+1) μ A'_r` term in
the factor-3 bound of `vitali_cover_third`. -/
lemma measure_iUnion_zIter_window_eq {μ : Measure Ω} (σ : Ω ≃ᵐ Ω)
    (hσ : Ergodic (⇑σ) μ) (r : ℕ) {S : Set Ω} (hS : MeasurableSet S)
    (hdisj : ∀ i ∈ Set.Icc (-(r : ℤ)) r, ∀ k ∈ Set.Icc (-(r : ℤ)) r, i ≠ k →
        Disjoint (zIter σ i '' S) (zIter σ k '' S)) :
    μ (⋃ t ∈ Set.Icc (-(r : ℤ)) r, zIter σ t '' S) = (2 * r + 1) * μ S := by
  have hbi : (⋃ t ∈ Set.Icc (-(r : ℤ)) r, zIter σ t '' S)
      = ⋃ t ∈ (Finset.Icc (-(r : ℤ)) r), zIter σ t '' S := by
    apply Set.iUnion_congr; intro t; simp only [Set.mem_Icc, Finset.mem_Icc]
  rw [hbi]
  have hpd : (↑(Finset.Icc (-(r : ℤ)) r) : Set ℤ).PairwiseDisjoint
      (fun t => zIter σ t '' S) := by
    intro i hi k hk hik
    simp only [Finset.coe_Icc, Set.mem_Icc] at hi hk
    exact hdisj i (Set.mem_Icc.mpr hi) k (Set.mem_Icc.mpr hk) hik
  rw [measure_biUnion_finset hpd (fun t _ => measurableSet_zIter_image σ t hS)]
  have hcard : (Finset.Icc (-(r : ℤ)) r).card = 2 * r + 1 := by rw [Int.card_Icc]; omega
  calc ∑ t ∈ Finset.Icc (-(r : ℤ)) r, μ (zIter σ t '' S)
      = ∑ _t ∈ Finset.Icc (-(r : ℤ)) r, μ S :=
        Finset.sum_congr rfl (fun t _ => measure_zIter_image σ hσ t hS)
    _ = (Finset.Icc (-(r : ℤ)) r).card • μ S := by rw [Finset.sum_const]
    _ = (2 * r + 1) * μ S := by rw [hcard, nsmul_eq_mul]; push_cast; ring


end MultiplicativeErgodic
