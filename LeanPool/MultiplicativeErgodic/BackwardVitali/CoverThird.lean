/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.BackwardVitali.Basic

/-!
# A measurable one-third Vitali covering theorem
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter

open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Infrastructure for the greedy construction in `vitali_cover_third`.

`DisjWin σ r A'` packages "the `2r+1` two-sided translates of `A'` (window radius `r`) are
pairwise disjoint" — the property selected pieces must have at each level of the construction. -/

/-- The `2r+1` two-sided translates of `A'` under `zIter σ`, indexed by `Set.Icc (-r) r`, are
pairwise disjoint. -/
private def DisjWin (σ : Ω ≃ᵐ Ω) (r : ℕ) (A' : Set Ω) : Prop :=
  ∀ i ∈ Set.Icc (-(r : ℤ)) r, ∀ k ∈ Set.Icc (-(r : ℤ)) r, i ≠ k →
    Disjoint (zIter σ i '' A') (zIter σ k '' A')

private lemma disjWin_empty (σ : Ω ≃ᵐ Ω) (r : ℕ) : DisjWin σ r (∅ : Set Ω) := by
  intro i _ k _ _
  simp

private lemma disjWin_mono (σ : Ω ≃ᵐ Ω) {r : ℕ} {A B : Set Ω} (h : A ⊆ B)
    (hB : DisjWin σ r B) : DisjWin σ r A := by
  intro i hi k hk hik
  exact (hB i hi k hk hik).mono (Set.image_mono h) (Set.image_mono h)

/-- An increasing union of `DisjWin`-sets is again a `DisjWin`-set: any collision witness lives
in finitely (two) many stages of the chain, so is captured at the later of the two. -/
private lemma disjWin_iUnion_of_monotone (σ : Ω ≃ᵐ Ω) {r : ℕ} {f : ℕ → Set Ω}
    (hf : Monotone f) (hDisj : ∀ n, DisjWin σ r (f n)) : DisjWin σ r (⋃ n, f n) := by
  intro i hi k hk hik
  rw [Set.disjoint_left]
  rintro z ⟨a, ha, rfl⟩ ⟨b, hb, hzb⟩
  simp only [Set.mem_iUnion] at ha hb
  obtain ⟨na, hna⟩ := ha
  obtain ⟨nb, hnb⟩ := hb
  have hAN : a ∈ f (max na nb) := hf (le_max_left na nb) hna
  have hBN : b ∈ f (max na nb) := hf (le_max_right na nb) hnb
  exact Set.disjoint_left.mp (hDisj (max na nb) i hi k hk hik) ⟨a, hAN, rfl⟩ ⟨b, hBN, hzb⟩

/-- **Measure-maximal (saturated) selection at a fixed window radius.** For any set
`S`, there is `A' ⊆ S`, measurable, with `DisjWin σ r A'`, which is *measure-saturated*: any
further valid extension `A''` (measurable, `⊆ S`, `DisjWin σ r A''`, `A' ⊆ A''`) adds nothing,
`μ (A'' \ A') = 0`.

**Method (not the axiom of choice).** Build an increasing sequence `Aseq n` by, at each step,
choosing an extension within `1/(n+1)` of the supremum of achievable measure *among extensions of
the current set* (this supremum exists in the complete lattice `ℝ≥0∞`; `lt_sSup_iff` extracts an
approximating witness). The union `C = ⋃ n, Aseq n` is then shown saturated by a squeeze: any
valid `A'' ⊇ C` is in particular a valid extension of every `Aseq n`, so `μ A'' ≤ (that level's
sup) ≤ μ (Aseq (n+1)) + 1/(n+1)`; letting `n → ∞` gives `μ A'' ≤ μ C`, and `C ⊆ A''` gives the
reverse, forcing `μ (A'' \ C) = 0`. -/
private lemma exists_saturated (μ : Measure Ω) [IsProbabilityMeasure μ] (σ : Ω ≃ᵐ Ω)
    (r : ℕ) {S : Set Ω} :
    ∃ A', A' ⊆ S ∧ MeasurableSet A' ∧ DisjWin σ r A' ∧
      ∀ A'', A' ⊆ A'' → A'' ⊆ S → MeasurableSet A'' → DisjWin σ r A'' → μ (A'' \ A') = 0 := by
  classical
  set P : Set Ω → Prop := fun A => A ⊆ S ∧ MeasurableSet A ∧ DisjWin σ r A with hPdef
  have hPempty : P ∅ := ⟨Set.empty_subset _, MeasurableSet.empty, disjWin_empty σ r⟩
  -- One-step improvement: extend `A` towards the supremum achievable among its extensions.
  have step : ∀ (A : Set Ω), P A → ∀ (n : ℕ),
      ∃ A', A ⊆ A' ∧ P A' ∧
        sSup ((fun A'' => μ A'') '' {A'' | A ⊆ A'' ∧ P A''}) ≤ μ A' + ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro A hA n
    set T : Set (Set Ω) := {A'' | A ⊆ A'' ∧ P A''} with hTdef
    set m : ℝ≥0∞ := sSup ((fun A'' => μ A'') '' T) with hmdef
    have hAT : A ∈ T := ⟨subset_rfl, hA⟩
    have hbound : ∀ x ∈ (fun A'' => μ A'') '' T, x ≤ μ S := by
      rintro x ⟨A'', ⟨_, hA''sub, _, _⟩, rfl⟩
      exact measure_mono hA''sub
    have hmle1 : m ≤ 1 := by
      rw [hmdef]
      exact le_trans (sSup_le hbound) (prob_le_one)
    have hmtop : m ≠ ⊤ := (lt_of_le_of_lt hmle1 (by norm_num : (1 : ℝ≥0∞) < ⊤)).ne
    by_cases hm0 : m = 0
    · exact ⟨A, subset_rfl, hA, by rw [hm0]; exact bot_le⟩
    · have hεne : ((n : ℝ≥0∞) + 1)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (by finiteness)
      have hlt : m - ((n : ℝ≥0∞) + 1)⁻¹ < m := ENNReal.sub_lt_self hmtop hm0 hεne
      obtain ⟨x, hxmem, hxlt⟩ := lt_sSup_iff.mp hlt
      obtain ⟨A', hA'T, hA'eq⟩ := hxmem
      refine ⟨A', hA'T.1, hA'T.2, ?_⟩
      have hA'eq' : μ A' = x := hA'eq
      rw [← hA'eq'] at hxlt
      exact (ENNReal.lt_add_of_sub_lt_right (Or.inl hmtop) hxlt).le
  -- Build the increasing sequence via the one-step improvement, `n`-indexed.
  set step' : Set Ω → ℕ → Set Ω := fun A n => if h : P A then (step A h n).choose else A
    with hstep'def
  set Aseq : ℕ → Set Ω := fun n => Nat.rec (∅ : Set Ω) (fun k ih => step' ih k) n with hAseqdef
  have hAseq0 : Aseq 0 = ∅ := rfl
  have hAseqsucc : ∀ n, Aseq (n + 1) = step' (Aseq n) n := fun _ => rfl
  have hAseqP : ∀ n, P (Aseq n) := by
    intro n
    induction n with
    | zero => rw [hAseq0]; exact hPempty
    | succ k ih =>
        rw [hAseqsucc k, hstep'def]
        simp only [dite_eq_left ih]
        exact (step (Aseq k) ih k).choose_spec.2.1
  have hAseqsub : ∀ n, Aseq n ⊆ Aseq (n + 1) := by
    intro n
    rw [hAseqsucc n, hstep'def]
    simp only [dite_eq_left (hAseqP n)]
    exact (step (Aseq n) (hAseqP n) n).choose_spec.1
  have hAseqbound : ∀ n, sSup ((fun A'' => μ A'') '' {A'' | Aseq n ⊆ A'' ∧ P A''})
      ≤ μ (Aseq (n + 1)) + ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    rw [hAseqsucc n, hstep'def]
    simp only [dite_eq_left (hAseqP n)]
    exact (step (Aseq n) (hAseqP n) n).choose_spec.2.2
  have hAseqmono : Monotone Aseq := monotone_nat_of_le_succ hAseqsub
  set C : Set Ω := ⋃ n, Aseq n with hCdef
  have hCsub : C ⊆ S := Set.iUnion_subset (fun n => (hAseqP n).1)
  have hCmeas : MeasurableSet C := MeasurableSet.iUnion (fun n => (hAseqP n).2.1)
  have hCdisj : DisjWin σ r C := disjWin_iUnion_of_monotone σ hAseqmono (fun n => (hAseqP n).2.2)
  refine ⟨C, hCsub, hCmeas, hCdisj, ?_⟩
  intro A'' hCA'' hA''sub hA''meas hA''disj
  have htendsto : Tendsto (fun n => μ (Aseq (n + 1)) + ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 (μ C)) := by
    have h1 : Tendsto (fun n => μ (Aseq (n + 1))) atTop (𝓝 (μ C)) := by
      have hbase := tendsto_measure_iUnion_atTop (μ := μ) hAseqmono
      rw [← hCdef] at hbase
      exact hbase.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
      have hshift := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      have hEq : (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹)
          = (fun n : ℕ => (n : ℝ≥0∞)⁻¹) ∘ (fun a => a + 1) := by
        funext n; simp [Function.comp]
      rw [hEq]
      exact hshift
    simpa using h1.add h2
  have hle : ∀ n, μ A'' ≤ μ (Aseq (n + 1)) + ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    have hAsub : Aseq n ⊆ A'' := (Set.subset_iUnion Aseq n).trans (hCdef ▸ hCA'')
    have hmemT : A'' ∈ {A'' | Aseq n ⊆ A'' ∧ P A''} :=
      ⟨hAsub, hA''sub, hA''meas, hA''disj⟩
    have hlesup : μ A'' ≤ sSup ((fun A'' => μ A'') '' {A'' | Aseq n ⊆ A'' ∧ P A''}) :=
      le_sSup ⟨A'', hmemT, rfl⟩
    exact hlesup.trans (hAseqbound n)
  have hle_final : μ A'' ≤ μ C := ge_of_tendsto' htendsto hle
  have hge_final : μ C ≤ μ A'' := measure_mono hCA''
  have heq : μ A'' = μ C := le_antisymm hle_final hge_final
  rw [measure_sdiff hCA'' hCmeas.nullMeasurableSet (measure_ne_top μ C), heq, tsub_self]

/-- If `A'` and `B'` each have pairwise-disjoint radius-`r` translate families, and every
translate of `A'` is disjoint from every translate of `B'` (not just at matching indices), then
so does their union. Used to combine a saturated piece with a newly-found compatible piece. -/
private lemma disjWin_union_of_disjoint_window (σ : Ω ≃ᵐ Ω) (r : ℕ) {A' B' : Set Ω}
    (hA' : DisjWin σ r A') (hB' : DisjWin σ r B')
    (hmeet : ∀ i ∈ Set.Icc (-(r : ℤ)) r, ∀ k ∈ Set.Icc (-(r : ℤ)) r,
        Disjoint (zIter σ i '' A') (zIter σ k '' B')) :
    DisjWin σ r (A' ∪ B') := by
  intro i hi k hk hik
  rw [Set.image_union, Set.image_union]
  refine Set.disjoint_union_left.mpr ⟨Set.disjoint_union_right.mpr ⟨?_, ?_⟩,
    Set.disjoint_union_right.mpr ⟨?_, ?_⟩⟩
  · exact hA' i hi k hk hik
  · exact hmeet i hi k hk
  · exact (hmeet k hk i hi).symm
  · exact hB' i hi k hk hik

/-- The set whose radius-`r` window avoids `W` is measurable. Used both in the saturation
dichotomy and for the per-level candidates in `vitali_cover_third`. -/
private lemma measurableSet_disjoint_window (σ : Ω ≃ᵐ Ω) (r : ℕ) {S W : Set Ω}
    (hS : MeasurableSet S) (hW : MeasurableSet W) :
    MeasurableSet {x ∈ S | Disjoint ((fun t => zIter σ t x) '' Set.Icc (-(r : ℤ)) r) W} := by
  have heq : {x ∈ S | Disjoint ((fun t => zIter σ t x) '' Set.Icc (-(r : ℤ)) r) W}
      = S \ ⋃ t ∈ Set.Icc (-(r : ℤ)) r, zIter σ t ⁻¹' W := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_iUnion, Set.mem_preimage,
      Set.disjoint_left, Set.mem_image, not_exists]
    constructor
    · rintro ⟨hxS, hdisj⟩
      exact ⟨hxS, fun t ht hxt => hdisj ⟨t, ht, rfl⟩ hxt⟩
    · rintro ⟨hxS, hnot⟩
      refine ⟨hxS, ?_⟩
      rintro z ⟨t, ht, rfl⟩ hzW
      exact hnot t ht hzW
  rw [heq]
  exact hS.diff (MeasurableSet.biUnion ((Set.finite_Icc _ _).countable)
    (fun t _ => (measurable_zIter σ t) hW))

/-- The collective window over a symmetric index range of a measurable set is measurable. -/
private lemma measurableSet_windowUnion (σ : Ω ≃ᵐ Ω) (r : ℕ) {S : Set Ω} (hS : MeasurableSet S) :
    MeasurableSet (⋃ k ∈ Set.Icc (-(r : ℤ)) r, zIter σ k '' S) :=
  MeasurableSet.biUnion ((Set.finite_Icc _ _).countable)
    (fun k _ => measurableSet_zIter_image σ k hS)

/-- **Vitali dichotomy at a fixed window radius.** For measurable `S`, there is a saturated
`A' ⊆ S` (as in `exists_saturated`) such that *almost every* `x ∈ S` has its radius-`r` window
meeting the collective radius-`r` window of `A'`. This is the key non-covering-but-meeting fact
that drives the classical Vitali `3r` argument: if it failed on a positive-measure set `B`,
`exists_subset_disjoint_iterates_symm` would produce a positive-measure `B' ⊆ B` compatible with
`A'` (its windows entirely avoid `A'`'s window, by definition of `B`), so `A' ∪ B'` would be a
strictly better valid piece, contradicting saturation of `A'`. -/
private lemma exists_saturated_dichotomy [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] (σ : Ω ≃ᵐ Ω) (hσ : Ergodic (⇑σ) μ)
    (r : ℕ) {S : Set Ω} (hS : MeasurableSet S) :
    ∃ A', A' ⊆ S ∧ MeasurableSet A' ∧ DisjWin σ r A' ∧
      μ {x ∈ S | Disjoint ((fun t => zIter σ t x) '' Set.Icc (-(r : ℤ)) r)
            (⋃ k ∈ Set.Icc (-(r : ℤ)) r, zIter σ k '' A')} = 0 := by
  obtain ⟨A', hA'S, hA'meas, hA'disj, hA'sat⟩ := exists_saturated μ σ r
  refine ⟨A', hA'S, hA'meas, hA'disj, ?_⟩
  set W : Set Ω := ⋃ k ∈ Set.Icc (-(r : ℤ)) r, zIter σ k '' A' with hWdef
  have hWmeas : MeasurableSet W := measurableSet_windowUnion σ r hA'meas
  set B : Set Ω := {x ∈ S | Disjoint ((fun t => zIter σ t x) '' Set.Icc (-(r : ℤ)) r) W}
  have hBmeas : MeasurableSet B := measurableSet_disjoint_window σ r hS hWmeas
  by_contra hBne
  have hBpos : 0 < μ B := pos_iff_ne_zero.mpr hBne
  obtain ⟨B', hB'B, hB'meas, hB'pos, hB'disj⟩ :=
    exists_subset_disjoint_iterates_symm μ σ hσ r hBmeas hBpos
  have hmeet : ∀ i ∈ Set.Icc (-(r : ℤ)) r, ∀ k ∈ Set.Icc (-(r : ℤ)) r,
      Disjoint (zIter σ i '' A') (zIter σ k '' B') := by
    intro i hi k hk
    refine Set.disjoint_left.mpr ?_
    rintro z ⟨a, ha, hza⟩ ⟨b, hb, hzb⟩
    have hbB : b ∈ B := hB'B hb
    have hzWin : z ∈ (fun t => zIter σ t b) '' Set.Icc (-(r : ℤ)) r := ⟨k, hk, hzb⟩
    have hzW : z ∈ W := by rw [hWdef]; exact Set.mem_biUnion hi ⟨a, ha, hza⟩
    exact (Set.disjoint_left.mp hbB.2 hzWin) hzW
  have hUnionDisj : DisjWin σ r (A' ∪ B') :=
    disjWin_union_of_disjoint_window σ r hA'disj hB'disj hmeet
  have hUnionSub : A' ∪ B' ⊆ S := Set.union_subset hA'S (hB'B.trans (fun x hx => hx.1))
  have hUnionMeas : MeasurableSet (A' ∪ B') := hA'meas.union hB'meas
  have hB'notA' : Disjoint B' A' := by
    refine Set.disjoint_left.mpr ?_
    intro x hxB' hxA'
    have hxB : x ∈ B := hB'B hxB'
    have hxWin : x ∈ (fun t => zIter σ t x) '' Set.Icc (-(r : ℤ)) r :=
      ⟨0, by simp, zIter_zero_apply σ x⟩
    have hxW : x ∈ W := by
      rw [hWdef]; exact Set.mem_biUnion (by simp) ⟨x, hxA', zIter_zero_apply σ x⟩
    exact (Set.disjoint_left.mp hxB.2 hxWin) hxW
  have hB'sub : B' ⊆ (A' ∪ B') \ A' := Set.subset_sdiff.mpr ⟨Set.subset_union_right, hB'notA'⟩
  have hle0 : μ B' ≤ μ ((A' ∪ B') \ A') := measure_mono hB'sub
  have h0 : μ ((A' ∪ B') \ A') = 0 :=
    hA'sat (A' ∪ B') Set.subset_union_left hUnionSub hUnionMeas hUnionDisj
  rw [h0] at hle0
  exact absurd (le_antisymm hle0 bot_le) hB'pos.ne'

/-- If `DisjWin σ r A'` holds, distinct points of `A'` have disjoint radius-`r` windows: two
translates `zIter σ t₁ x`, `zIter σ t₂ y` colliding either force `t₁ = t₂` (hence `x = y` by
injectivity of `zIter σ t₁`, contradicting distinctness) or witness a `DisjWin` failure. -/
private lemma disjWin_pairwise (σ : Ω ≃ᵐ Ω) {r : ℕ} {A' : Set Ω} (hdisj : DisjWin σ r A') :
    A'.PairwiseDisjoint (fun x => (fun t => zIter σ t x) '' Set.Icc (-(r : ℤ)) r) := by
  intro x hx y hy hxy
  change Disjoint ((fun t => zIter σ t x) '' Set.Icc (-(r : ℤ)) r)
    ((fun t => zIter σ t y) '' Set.Icc (-(r : ℤ)) r)
  rw [Set.disjoint_left]
  rintro z ⟨t1, ht1, hz1⟩ ⟨t2, ht2, hz2⟩
  by_cases heqt : t1 = t2
  · subst heqt
    have hxy' : zIter σ t1 x = zIter σ t1 y := hz1.trans hz2.symm
    have hinj : Function.Injective (zIter σ t1) := by
      rw [zIter_eq_zpow]; exact (σ.toEquiv ^ t1).injective
    exact hxy (hinj hxy')
  · exact Set.disjoint_left.mp (hdisj t1 ht1 t2 ht2 heqt) ⟨x, hx, hz1⟩ ⟨y, hy, hz2⟩

private abbrev orbitWindow (σ : Ω ≃ᵐ Ω) (r : ℕ) (x : Ω) : Set Ω :=
  (fun t => zIter σ t x) '' Set.Icc (-(r : ℤ)) r

private abbrev collectiveOrbitWindow (σ : Ω ≃ᵐ Ω) (r : ℕ) (S : Set Ω) : Set Ω :=
  ⋃ t ∈ Set.Icc (-(r : ℤ)) r, zIter σ t '' S

private abbrev SaturatedWindowSelection (μ : Measure Ω) (σ : Ω ≃ᵐ Ω)
    (radius : ℕ → ℕ) (level Sel Piece : ℕ → Set Ω) : Prop :=
  ∀ k,
    Piece k ⊆ {x ∈ level k | Disjoint (orbitWindow σ (radius k) x) (Sel k)} ∧
    DisjWin σ (radius k) (Piece k) ∧
    μ {x ∈ {x ∈ level k | Disjoint (orbitWindow σ (radius k) x) (Sel k)} |
      Disjoint (orbitWindow σ (radius k) x)
        (collectiveOrbitWindow σ (radius k) (Piece k))} = 0

private abbrev coveredWindowCenters (σ : Ω ≃ᵐ Ω) (A : Set Ω) (w : Ω → ℕ)
    (B : ℕ) (Piece : ℕ → Set Ω) : Set Ω :=
  {x ∈ A | ∃ k ≤ B, w x ≤ B - k ∧
    orbitWindow σ (w x) x ⊆ collectiveOrbitWindow σ (3 * (B - k) + 1) (Piece k)}

/-- Construct measurable, saturated pieces while excluding all earlier selected windows. -/
private theorem exists_saturated_window_ladder [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (σ : Ω ≃ᵐ Ω) (hσ : Ergodic (⇑σ) μ) (radius : ℕ → ℕ)
    (level : ℕ → Set Ω) (hlevelmeas : ∀ k, MeasurableSet (level k)) :
    ∃ Sel Piece : ℕ → Set Ω,
      Sel 0 = ∅ ∧
      (∀ k, Sel (k + 1) = Sel k ∪ collectiveOrbitWindow σ (radius k) (Piece k)) ∧
      (∀ k, MeasurableSet (Sel k) ∧ MeasurableSet (Piece k)) ∧
      SaturatedWindowSelection μ σ radius level Sel Piece := by
  classical
  let window := orbitWindow σ
  let windowUnion := collectiveOrbitWindow σ
  set pieceOf : ℕ → Set Ω → Set Ω := fun k ih =>
    if h : MeasurableSet {x ∈ level k | Disjoint (window (radius k) x) ih} then
      (exists_saturated_dichotomy μ σ hσ (radius k) h).choose
    else (∅ : Set Ω) with hpieceOfdef
  -- The accumulated selected window, built by `Nat.rec` (mirrors `Aseq`/`step'` in
  -- `exists_saturated`'s own proof).
  set Sel : ℕ → Set Ω := fun k => Nat.rec (∅ : Set Ω)
      (fun k ih => ih ∪ windowUnion (radius k) (pieceOf k ih)) k with hSeldef
  set Piece : ℕ → Set Ω := fun k => pieceOf k (Sel k) with hPiecedef
  have hSel0 : Sel 0 = ∅ := rfl
  have hSelsucc : ∀ k, Sel (k + 1) = Sel k ∪ windowUnion (radius k) (pieceOf k (Sel k)) :=
    fun _ => rfl
  have hPiecek : ∀ k, Piece k = pieceOf k (Sel k) := fun _ => rfl
  have hSelsucc' : ∀ k, Sel (k + 1) = Sel k ∪ windowUnion (radius k) (Piece k) := by
    intro k; rw [hPiecek k]
  -- Measurability of `Sel` and `Piece`, by simultaneous induction (the `dite_eq_left` branch of
  -- `pieceOf` always fires, since `Sel k` is always measurable).
  have hMeas : ∀ k, MeasurableSet (Sel k) ∧ MeasurableSet (Piece k) := by
    intro k
    induction k with
    | zero =>
        have hSel0meas : MeasurableSet (Sel 0) := by rw [hSel0]; exact MeasurableSet.empty
        refine ⟨hSel0meas, ?_⟩
        have hcond : MeasurableSet {x ∈ level 0 | Disjoint (window (radius 0) x) (Sel 0)} :=
          measurableSet_disjoint_window σ (radius 0) (hlevelmeas 0) hSel0meas
        rw [hPiecek 0, hpieceOfdef]
        simp only [dite_eq_left hcond]
        exact (exists_saturated_dichotomy μ σ hσ (radius 0) hcond).choose_spec.2.1
    | succ k ih =>
        obtain ⟨ihSel, ihPiece⟩ := ih
        have hSelk1meas : MeasurableSet (Sel (k + 1)) := by
          rw [hSelsucc' k]
          exact ihSel.union (measurableSet_windowUnion σ (radius k) ihPiece)
        refine ⟨hSelk1meas, ?_⟩
        have hcond : MeasurableSet
            {x ∈ level (k + 1) | Disjoint (window (radius (k + 1)) x) (Sel (k + 1))} :=
          measurableSet_disjoint_window σ (radius (k + 1)) (hlevelmeas (k + 1)) hSelk1meas
        rw [hPiecek (k + 1), hpieceOfdef]
        simp only [dite_eq_left hcond]
        exact (exists_saturated_dichotomy μ σ hσ (radius (k + 1)) hcond).choose_spec.2.1
  -- Full spec of `Piece k`: subset of the "not yet touching `Sel k`" candidate set, `DisjWin`,
  -- and the Vitali-dichotomy null-exceptional-set fact.
  have hPieceSpec : ∀ k,
      Piece k ⊆ {x ∈ level k | Disjoint (window (radius k) x) (Sel k)} ∧
      DisjWin σ (radius k) (Piece k) ∧
      μ {x ∈ {x ∈ level k | Disjoint (window (radius k) x) (Sel k)} |
          Disjoint (window (radius k) x) (windowUnion (radius k) (Piece k))} = 0 := by
    intro k
    have hcond : MeasurableSet {x ∈ level k | Disjoint (window (radius k) x) (Sel k)} :=
      measurableSet_disjoint_window σ (radius k) (hlevelmeas k) (hMeas k).1
    rw [hPiecek k, hpieceOfdef]
    simp only [dite_eq_left hcond]
    obtain ⟨hsub, _hmeas, hdisj, hnull⟩ :=
      (exists_saturated_dichotomy μ σ hσ (radius k) hcond).choose_spec
    exact ⟨hsub, hdisj, hnull⟩
  exact ⟨Sel, Piece, hSel0, hSelsucc', hMeas, hPieceSpec⟩

/-- Saturation covers almost every center by a selected window of at least its radius. -/
private theorem saturated_window_ladder_coverage (μ : Measure Ω)
    (σ : Ω ≃ᵐ Ω) (A : Set Ω) (w : Ω → ℕ) (B : ℕ) (hwB : ∀ x, w x ≤ B)
    (Sel Piece : ℕ → Set Ω) (hSel0 : Sel 0 = ∅)
    (hSelsucc' : ∀ k, Sel (k + 1) = Sel k ∪
      collectiveOrbitWindow σ (B - k) (Piece k))
    (hPieceSpec : SaturatedWindowSelection μ σ (fun k => B - k)
      (fun k => A ∩ w ⁻¹' {B - k}) Sel Piece) :
    (∀ k, k ≤ B → μ ((A ∩ w ⁻¹' {B - k}) \ coveredWindowCenters σ A w B Piece) = 0) ∧
      μ (A \ coveredWindowCenters σ A w B Piece) = 0 := by
  classical
  let window : ℕ → Ω → Set Ω := fun r x =>
    (fun t => zIter σ t x) '' Set.Icc (-(r : ℤ)) r
  let windowUnion : ℕ → Set Ω → Set Ω := fun r S =>
    ⋃ k ∈ Set.Icc (-(r : ℤ)) r, zIter σ k '' S
  have hWUdef : windowUnion = fun (r : ℕ) S =>
      ⋃ k ∈ Set.Icc (-(r : ℤ)) r, zIter σ k '' S := rfl
  let radius : ℕ → ℕ := fun k => B - k
  have hradiusdef : radius = fun k => B - k := rfl
  let level : ℕ → Set Ω := fun k => A ∩ w ⁻¹' {radius k}
  have hzcomp : ∀ (a b : ℤ) (y : Ω), zIter σ a (zIter σ b y) = zIter σ (a + b) y :=
    fun a b y => (zIter_add σ a b y).symm
  have hzcancel : ∀ (a : ℤ) (y : Ω), zIter σ (-a) (zIter σ a y) = y := by
    intro a y
    rw [hzcomp (-a) a y, show (-a + a : ℤ) = 0 from by ring, zIter_zero_apply]
  have hOffset : ∀ (s u : ℕ) (x : Ω) (P : Set Ω), s ≤ u →
      ¬ Disjoint (window s x) (windowUnion u P) →
      window s x ⊆ windowUnion (3 * u + 1) P := by
    intro s u x P hsu hnd
    rw [Set.not_disjoint_iff] at hnd
    obtain ⟨z, hz1, hz2⟩ := hnd
    obtain ⟨t1, ht1, hzt1⟩ := hz1
    dsimp only at hzt1
    rw [hWUdef] at hz2
    simp only [Set.mem_iUnion, Set.mem_image] at hz2
    obtain ⟨t2, ht2, p, hp, hzt2⟩ := hz2
    have hx_eq : x = zIter σ (t2 - t1) p := by
      have h1 : zIter σ (-t1) (zIter σ t1 x) = x := hzcancel t1 x
      rw [hzt1] at h1
      rw [← h1, ← hzt2, hzcomp]
      congr 1
      ring
    intro τ hτ
    obtain ⟨τ', hτ', hτeq⟩ := hτ
    dsimp only at hτeq
    have hmem : zIter σ (τ' + (t2 - t1)) p ∈ windowUnion (3 * u + 1) P := by
      rw [hWUdef]
      simp only [Set.mem_iUnion, Set.mem_image]
      refine ⟨τ' + (t2 - t1), ?_, p, hp, rfl⟩
      simp only [Set.mem_Icc] at ht1 ht2 hτ' ⊢
      omega
    rw [← hτeq, hx_eq, hzcomp]
    exact hmem
  have hSelMeetsSome : ∀ k, ∀ {r : ℕ} {x : Ω}, ¬ Disjoint (window r x) (Sel k) →
      ∃ k' < k, ¬ Disjoint (window r x) (windowUnion (radius k') (Piece k')) := by
    intro k
    induction k with
    | zero =>
        intro r x hnd
        exact absurd (by rw [hSel0]; exact disjoint_bot_right) hnd
    | succ k ih =>
        intro r x hnd
        rw [hSelsucc' k] at hnd
        by_cases hcase : Disjoint (window r x) (Sel k)
        · refine ⟨k, Nat.lt_succ_self k, ?_⟩
          intro hd
          exact hnd (Set.disjoint_union_right.mpr ⟨hcase, hd⟩)
        · obtain ⟨k', hk', hmeet⟩ := ih hcase
          exact ⟨k', hk'.trans (Nat.lt_succ_self k), hmeet⟩
  -- **The "Good" set**: points of `A` whose own window sits inside a `3·radius k + 1`-scaled
  -- window of some level-`k` selected piece, at radius no smaller than their own. (Indexed
  -- directly by the step `k`, not by the radius `u = radius k`, so no reflection/reindexing is
  -- needed later when this is matched up against the `k`-indexed `A'`.)
  set Good : Set Ω := {x ∈ A | ∃ k ≤ B, w x ≤ radius k ∧
      window (w x) x ⊆ windowUnion (3 * radius k + 1) (Piece k)} with hGooddef
  -- **Level coverage.** Each level, minus `Good`, is null: points not touching `Sel k` are
  -- covered by `exists_saturated_dichotomy`'s exceptional null set (tag `u = radius k`); points
  -- touching `Sel k` touch some strictly earlier (larger-radius) piece (tag `u = radius k' > `
  -- their own radius), via `hSelMeetsSome` and the `3r`-offset computation `hOffset`.
  have hLevelNull : ∀ k, k ≤ B → μ (level k \ Good) = 0 := by
    intro k hk
    set Sk : Set Ω := {x ∈ level k | Disjoint (window (radius k) x) (Sel k)} with hSkdef
    have hpart1 : level k \ Sk ⊆ Good := by
      rintro x ⟨hxlevel, hxnotSk⟩
      have hxA : x ∈ A := hxlevel.1
      have hwx : w x = radius k := hxlevel.2
      have hnd : ¬ Disjoint (window (radius k) x) (Sel k) := by
        intro hd; exact hxnotSk ⟨hxlevel, hd⟩
      rw [← hwx] at hnd
      obtain ⟨k', hk'lt, hmeet⟩ := hSelMeetsSome k hnd
      have hu_ge : w x ≤ radius k' := by rw [hwx]; simp only [hradiusdef]; omega
      have hcontain : window (w x) x ⊆ windowUnion (3 * radius k' + 1) (Piece k') :=
        hOffset (w x) (radius k') x (Piece k') hu_ge hmeet
      exact ⟨hxA, k', by omega, hu_ge, hcontain⟩
    have hpart2 : Sk \ Good ⊆
        {x ∈ Sk | Disjoint (window (radius k) x) (windowUnion (radius k) (Piece k))} := by
      rintro x ⟨hxSk, hxnotGood⟩
      refine ⟨hxSk, ?_⟩
      by_contra hd
      apply hxnotGood
      have hxlevel : x ∈ level k := hxSk.1
      have hwx : w x = radius k := hxlevel.2
      have hcontain : window (w x) x ⊆ windowUnion (3 * radius k + 1) (Piece k) := by
        rw [hwx]; exact hOffset (radius k) (radius k) x (Piece k) le_rfl hd
      exact ⟨hxlevel.1, k, hk, le_of_eq hwx, hcontain⟩
    have hexcep0 : μ {x ∈ Sk | Disjoint (window (radius k) x) (windowUnion (radius k) (Piece k))}
        = 0 := (hPieceSpec k).2.2
    have hdecomp : level k \ Good ⊆ Sk \ Good := by
      rintro x ⟨hxlevel, hxnotGood⟩
      refine ⟨?_, hxnotGood⟩
      by_contra hxnotSk
      exact hxnotGood (hpart1 ⟨hxlevel, hxnotSk⟩)
    have hchain : μ (level k \ Good) ≤ 0 :=
      calc μ (level k \ Good) ≤ μ (Sk \ Good) := measure_mono hdecomp
        _ ≤ μ {x ∈ Sk | Disjoint (window (radius k) x) (windowUnion (radius k) (Piece k))} :=
            measure_mono hpart2
        _ = 0 := hexcep0
    exact le_antisymm hchain bot_le
  -- **Coverage induction.** After processing `k` levels (radii `B, …, B-k+1`), everything with
  -- `w x + k > B` (i.e. already-processed radii) is covered by `Good` up to a null set.
  have hCoverage : ∀ k, k ≤ B + 1 → μ ({x ∈ A | B < w x + k} \ Good) = 0 := by
    intro k
    induction k with
    | zero =>
        intro _
        have hempty : {x ∈ A | B < w x + 0} = (∅ : Set Ω) := by
          ext x
          simp only [Set.mem_ofPred_eq, add_zero, Set.mem_empty_iff_false, iff_false, not_and]
          intro _
          exact not_lt.mpr (hwB x)
        rw [hempty]
        simp
    | succ k ih =>
        intro hk1
        have hkleB : k ≤ B := by omega
        have ihk : μ ({x ∈ A | B < w x + k} \ Good) = 0 := ih (by omega)
        have hsplit : {x ∈ A | B < w x + (k + 1)} \ Good
            ⊆ ({x ∈ A | B < w x + k} \ Good) ∪ (level k \ Good) := by
          rintro x ⟨⟨hxA, hxlt⟩, hxnotGood⟩
          by_cases hcase : B < w x + k
          · exact Or.inl ⟨⟨hxA, hcase⟩, hxnotGood⟩
          · have hwx : w x = radius k := by simp only [hradiusdef]; omega
            exact Or.inr ⟨⟨hxA, hwx⟩, hxnotGood⟩
        have hchain : μ ({x ∈ A | B < w x + (k + 1)} \ Good) ≤ 0 :=
          calc μ ({x ∈ A | B < w x + (k + 1)} \ Good)
              ≤ μ (({x ∈ A | B < w x + k} \ Good) ∪ (level k \ Good)) := measure_mono hsplit
            _ ≤ μ ({x ∈ A | B < w x + k} \ Good) + μ (level k \ Good) := measure_union_le _ _
            _ = 0 := by rw [ihk, hLevelNull k hkleB]; simp
        exact le_antisymm hchain bot_le
  have hAGoodNull : μ (A \ Good) = 0 := by
    have hAeq : {x ∈ A | B < w x + (B + 1)} = A := by
      ext x
      simp only [Set.mem_ofPred_eq, and_iff_left_iff_imp]
      intro _; omega
    have := hCoverage (B + 1) le_rfl
    rwa [hAeq] at this
  exact ⟨hLevelNull, hAGoodNull⟩

/-- **Rudolph's one-third covering lemma** (one-dimensional Vitali covering step, uses
`exists_subset_disjoint_iterates_symm`). For a *bounded* measurable window-radius function `w`
(finitely many values, since `w ω ≤ B`) on a measurable set `A`, there is a subset `A' ⊆ A` on
which the symmetric windows `I_ω = {zIter σ t ω : |t| ≤ w ω}` are pairwise disjoint and recover
at least a third of the region covered by *all* the windows over `A`.

**Method** (the classical one-dimensional Vitali `3r`-covering lemma, transported to orbit
segments). Partition `A` into the finitely many level sets `A_r = {ω ∈ A : w ω = r}`,
`r = 0, …, B`, and process them from the *longest* window (`r = B`) down to the shortest. At
level `r`, among the part of `A_r` *not already within window-distance of a previously selected
(longer-window) piece*, greedily select — via `exists_subset_disjoint_iterates_symm` with `N = r`
and the a.e.-maximal-measure limiting argument (approach the supremum of achievable
disjoint-translate measure) — a piece `A'_r` whose `2r+1`
translates are pairwise disjoint. Set `A' = ⋃_r A'_r`.

**The factor 3 and a subtlety versus Rudolph.** Rudolph's one-third covering lemma bounds `μ A ≤ 3
μ(⋃_{A'} I)`
(his final display, p. 40), i.e. the left-hand union is over the *centres* `A`. The statement
here is stronger: the left-hand union `⋃_{ω ∈ A} I_ω` is over the whole *windowed* region, and
must still be `≤ 3 μ(⋃_{A'} I)`. Rudolph's construction removes, at each level `u`, the
`3n(u)`-fold expanded window of `A'_u` (index range `[i(u)-n(u), j(u)+n(u)]`); a centre `ω`
sitting in the removed-but-not-covered shell can have its own window `I_ω` protrude to distance
`≈ 4 r_u`, which would only give a factor `4` for the windowed region. The fix (which does not
change the statement, only the construction) is to remove instead exactly the set of centres
whose window *meets* an already-selected window — removal radius `r_ω + r_u` rather than a fixed
`3 r_u + 1`. Then the classical Vitali dichotomy holds for every centre `ω ∈ A_r`: either `ω`'s
own maximal piece was selectable (so `I_ω` meets `I(A'_r)`, `r' = r`), or `I_ω` meets some
selected `I(A'_u)` with `r_u ≥ r`; in both cases `I_ω ⊆ ⋃_{|s| ≤ 3 r_u + 1} zIter σ s '' A'_u`
(a `3r`-scaled window). Summing the counting bound `measure_iUnion_zIter_window_le` over levels
then gives `μ(⋃_{ω ∈ A} I_ω) ≤ Σ_u (6 r_u + 3) μ A'_u = 3 Σ_u (2 r_u + 1) μ A'_u
= 3 μ(⋃_{A'} I)`, the last equality because the selected windows are pairwise disjoint.

The measure bookkeeping uses the `zIter` group law, measure preservation, image measures and
window counts. The greedy construction uses two selection lemmas:
* `exists_saturated` — the single-level *measure-maximal disjoint-window selection*, via the
  "approach the achievable supremum" `ℕ`-indexed limiting sequence (not the axiom of choice;
  the sequence is built with `lt_sSup_iff`/`ENNReal.sub_lt_self` and the limit taken with
  `tendsto_measure_iUnion_atTop`). This is exactly Rudolph's `𝒜_1`/`A'_1` maximality argument
  (his parenthetical "the sequence is constructed to approach the maximal available measure"),
  made fully explicit and radius-generic (works at any single fixed `r`, for any candidate set
  `S`, not just a whole level).
* `exists_saturated_dichotomy` — the classical Vitali dichotomy built on top of it: given `S`,
  produces a saturated `A' ⊆ S` such that *a.e.* `x ∈ S` has its radius-`r` window meeting the
  collective window of `A'` (if a positive-measure set of `x` failed this, extract a
  positive-measure disjoint-compatible piece via `exists_subset_disjoint_iterates_symm` and merge it
  into `A'` via `disjWin_union_of_disjoint_window`, contradicting saturation).

The construction assembles these selections by descending radius, followed by the final
counting estimate:
1. Run the construction `B + 1` times, once per level, in *descending* radius order: at step
   `k = 0, …, B` (radius `r = B - k`), apply `exists_saturated_dichotomy` to
   `S_k = (A ∩ w⁻¹{r}) ∩ {x | Disjoint (window_r x) (Sel k)}`, where `Sel k` is the union so far
   of the selected windows from strictly larger radii (`Sel 0 = ∅`,
   `Sel (k+1) = Sel k ∪ window_r (Piece k)`). Build `Piece : ℕ → Set Ω` and `Sel : ℕ → Set Ω`
   simultaneously via a non-dependent `Nat.rec` + `Classical.choose` (mirroring the `step'`/
   `Aseq` pattern inside `exists_saturated`'s proof: guard with `if h : MeasurableSet (S_of …)
   then (exists_saturated_dichotomy … h).choose else ∅`, then prove `MeasurableSet (Sel k)` for
   all `k` by a separate induction so the `dite_eq_left` branch always fires). Measurability of each
   `S_k` needs the "Disjoint window" set to be measurable, which is the same argument already
   supplied by `measurableSet_disjoint_window`, also used in `exists_saturated_dichotomy`.
2. **Coverage induction.** Prove by induction on `k = 0, …, B + 1`:
   `μ ({x ∈ A | w x ≥ B - k + 1} \ Good) = 0`, where `Good` is the *fixed* (`k`-independent) set
   `{x ∈ A | ∃ u ≤ B, w x ≤ u ∧ window_{w x} x ⊆ ⋃_{|s| ≤ 3u+1} zIter σ s '' Piece (B - u)}`.
   Base case `k = 0` is vacuous (`w x ≤ B` always). Inductive step splits
   `{w x ≥ B-k} = {w x ≥ B-k+1} ∪ (A ∩ w⁻¹{B-k})`: the first part is covered by the IH (`Sel k
   ⊆ Sel (k+1)` monotonicity — meeting a subset implies meeting the superset); the level part
   splits again into `S_k` (where `exists_saturated_dichotomy`'s null-set gives a.e. `x` meets
   `window (Piece k)`, tag `u = B - k = w x`, tight) and its complement in the level (already
   meets `Sel k` from a *strictly larger*, already-processed radius, tag `u >` that radius). In
   both cases `u ≥ w x` **by construction** (radius-descending processing order), which is what
   licenses the pointwise bound `window_{w x} x ⊆ ⋃_{|s|≤3u+1} zIter σ s '' Piece (B-u)` (from
   `w x ≤ u`, an offset computation identical to the one already done in
   `exists_saturated_dichotomy`'s `hmeet`, just with `2·(w x) + u ≤ 3u`). At `k = B+1` this gives
   `μ (A \ Good) = 0`, i.e. conclusion (ii) up to a null set.
3. **Disjointness (i).** Within a level, `DisjWin r (Piece k)` (from step 1) gives pointwise
   window-disjointness for distinct points of `Piece k` (two translates at indices `i ≠ k`
   colliding would witness a `DisjWin` failure — same argument as `disjWin_union_of_disjoint_window`
   /`hB'notA'` above). Across levels, `Piece k ⊆ S_k` forces `window (Piece k) ∩ Sel k = ∅`
   (pointwise, same computation as `exists_saturated_dichotomy`'s `hB'notA'`), so `Sel` is
   genuinely a *disjoint* union of the per-level windows, giving cross-level disjointness too.
4. **Arithmetic.** Let `A' = ⋃_k Piece k`. From (ii), `μ (⋃_{ω∈A} I_ω) ≤ μ (⋃_{u≤B} ⋃_{|s|≤3u+1}
   zIter σ s '' Piece (B-u)) ≤ Σ_{u≤B} (6u+3) μ (Piece (B-u))` (`measure_iUnion_zIter_window_le`
   + finite subadditivity over `Finset.range (B+1)`) `= 3 Σ_{u≤B} (2u+1) μ (Piece (B-u)) = 3
   Σ_{u≤B} μ (window_u (Piece (B-u)))` (`measure_iUnion_zIter_window_eq`, exact since each level
   is individually `DisjWin`) `= 3 μ (⋃_{ω∈A'} I_ω)` (cross-level disjointness from step 3 turns
   the sum of the disjoint per-level window-unions into the measure of their union). -/
theorem vitali_cover_third [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] (σ : Ω ≃ᵐ Ω) (hσ : Ergodic (⇑σ) μ)
    {A : Set Ω} (hA : MeasurableSet A) (w : Ω → ℕ) (hw : Measurable w)
    (B : ℕ) (hwB : ∀ ω, w ω ≤ B) :
    ∃ A' ⊆ A, MeasurableSet A' ∧
      (A'.PairwiseDisjoint fun ω => (fun t => zIter σ t ω) '' Set.Icc (-(w ω : ℤ)) (w ω)) ∧
      μ (⋃ ω ∈ A, (fun t => zIter σ t ω) '' Set.Icc (-(w ω : ℤ)) (w ω)) ≤
        3 * μ (⋃ ω ∈ A', (fun t => zIter σ t ω) '' Set.Icc (-(w ω : ℤ)) (w ω)) := by
  classical
  -- Window of radius `r` centred at `x`, and the collective window of radius `r` over a set `S`.
  set window : ℕ → Ω → Set Ω := fun r x => (fun t => zIter σ t x) '' Set.Icc (-(r : ℤ)) r
    with hwindowdef
  set windowUnion : ℕ → Set Ω → Set Ω := fun r S => ⋃ k ∈ Set.Icc (-(r : ℤ)) r, zIter σ k '' S
    with hWUdef
  -- Radius processed at step `k` (descending from `B`), and the level of `A` at that radius.
  set radius : ℕ → ℕ := fun k => B - k with hradiusdef
  set level : ℕ → Set Ω := fun k => A ∩ w ⁻¹' {radius k} with hleveldef
  have hlevelmeas : ∀ k, MeasurableSet (level k) :=
    fun k => hA.inter (hw (measurableSet_singleton _))
  -- The per-level selection, as a function of the "already selected" window `ih`.
  obtain ⟨Sel, Piece, hSel0, hSelsucc', hMeas, hPieceSpec⟩ :=
    exists_saturated_window_ladder μ σ hσ radius level hlevelmeas
  -- `zIter` group-law helpers (composition and cancellation).
  -- The collective window over a set is the union of the individual windows of its points.
  have hWU_eq_windows : ∀ (r : ℕ) (S : Set Ω), windowUnion r S = ⋃ x ∈ S, window r x := by
    intro r S
    ext z
    simp only [hWUdef, hwindowdef, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨k, hk, x, hx, hz⟩
      exact ⟨x, hx, k, hk, hz⟩
    · rintro ⟨x, hx, k, hk, hz⟩
      exact ⟨k, hk, x, hx, hz⟩
  -- **The `3r`-offset computation.** If a radius-`s` window meets a radius-`u` collective window
  -- (`s ≤ u`), the whole radius-`s` window sits inside the `3u+1`-scaled collective window.
  -- `Sel` is monotone (each step only adds to it).
  have hSelstep : ∀ k, Sel k ⊆ Sel (k + 1) := by
    intro k; rw [hSelsucc' k]; exact Set.subset_union_left
  have hSelMono : Monotone Sel := monotone_nat_of_le_succ hSelstep
  -- Meeting `Sel k` means meeting some earlier level's collective window.
  set Good : Set Ω := {x ∈ A | ∃ k ≤ B, w x ≤ radius k ∧
      window (w x) x ⊆ windowUnion (3 * radius k + 1) (Piece k)} with hGooddef
  obtain ⟨hLevelNull, hAGoodNull⟩ :=
    saturated_window_ladder_coverage μ σ A w B hwB Sel Piece hSel0 hSelsucc' hPieceSpec
  -- `Piece k`'s collective window is disjoint from `Sel k` (by construction: `Piece k` was
  -- selected from the "not yet touching `Sel k`" candidate set), hence from every earlier
  -- level's collective window too — giving cross-level disjointness.
  have hPieceDisjointSel : ∀ k, Disjoint (windowUnion (radius k) (Piece k)) (Sel k) := by
    intro k
    rw [hWU_eq_windows, Set.disjoint_iUnion₂_left]
    intro x hx
    exact ((hPieceSpec k).1 hx).2
  have hWUCrossDisjointLt : ∀ k k', k < k' →
      Disjoint (windowUnion (radius k) (Piece k)) (windowUnion (radius k') (Piece k')) := by
    intro k k' hkk'
    have hsub1 : windowUnion (radius k) (Piece k) ⊆ Sel (k + 1) := by
      rw [hSelsucc' k]; exact Set.subset_union_right
    have hle : k + 1 ≤ k' := by omega
    have hsub2 : Sel (k + 1) ⊆ Sel k' := hSelMono hle
    exact ((hPieceDisjointSel k').mono_right (hsub1.trans hsub2)).symm
  have hWUCrossDisjoint : ∀ k k', k ≠ k' →
      Disjoint (windowUnion (radius k) (Piece k)) (windowUnion (radius k') (Piece k')) := by
    intro k k' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hWUCrossDisjointLt k k' h
    · exact (hWUCrossDisjointLt k' k h).symm
  -- **`A'` and its disjointness.**
  set A' : Set Ω := ⋃ k ∈ Finset.range (B + 1), Piece k with hA'def
  have hA'sub : A' ⊆ A := by
    rw [hA'def]
    refine Set.iUnion₂_subset (fun k _ => ?_)
    intro x hx
    exact ((hPieceSpec k).1 hx).1.1
  have hA'meas : MeasurableSet A' := by
    rw [hA'def]
    exact Finset.measurableSet_biUnion _ (fun k _ => (hMeas k).2)
  have hA'disjoint : A'.PairwiseDisjoint (fun ω => window (w ω) ω) := by
    rw [hA'def]
    intro x hx y hy hxy
    change Disjoint (window (w x) x) (window (w y) y)
    simp only [Set.mem_iUnion, Finset.mem_range] at hx hy
    obtain ⟨k, _, hxk⟩ := hx
    obtain ⟨k', _, hyk'⟩ := hy
    by_cases hkk' : k = k'
    · subst hkk'
      have hwx : w x = radius k := ((hPieceSpec k).1 hxk).1.2
      have hwy : w y = radius k := ((hPieceSpec k).1 hyk').1.2
      have hdisj : Disjoint (window (radius k) x) (window (radius k) y) :=
        disjWin_pairwise σ (hPieceSpec k).2.1 hxk hyk' hxy
      rw [hwx, hwy]
      exact hdisj
    · have hwx : w x = radius k := ((hPieceSpec k).1 hxk).1.2
      have hwy : w y = radius k' := ((hPieceSpec k').1 hyk').1.2
      have hsub1 : window (w x) x ⊆ windowUnion (radius k) (Piece k) := by
        rw [hwx, hWU_eq_windows]; exact Set.subset_biUnion_of_mem hxk
      have hsub2 : window (w y) y ⊆ windowUnion (radius k') (Piece k') := by
        rw [hwy, hWU_eq_windows]; exact Set.subset_biUnion_of_mem hyk'
      exact (hWUCrossDisjoint k k' hkk').mono hsub1 hsub2
  refine ⟨A', hA'sub, hA'meas, hA'disjoint, ?_⟩
  -- `windowUnion` is monotone in its set argument.
  have hWUmono : ∀ (r : ℕ) {S T : Set Ω}, S ⊆ T → windowUnion r S ⊆ windowUnion r T := by
    intro r S T hST
    rw [hWUdef]
    exact Set.iUnion₂_mono (fun t _ => Set.image_mono hST)
  -- Every windowed centre `ω ∈ A` either lies in `Good` (its window sits in a `3r+1`-scaled
  -- selected window) or is in `level k \ Good` for the level `k` matching its own radius.
  have hBigSubset : (⋃ ω ∈ A, window (w ω) ω) ⊆
      (⋃ k ∈ Finset.range (B + 1), windowUnion (radius k) (level k \ Good)) ∪
      (⋃ k ∈ Finset.range (B + 1), windowUnion (3 * radius k + 1) (Piece k)) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨ω, hωA, hz⟩ := hz
    by_cases hg : ω ∈ Good
    · obtain ⟨k, hkB, _hwk, hcontain⟩ := hg.2
      refine Or.inr ?_
      simp only [Set.mem_iUnion, Finset.mem_range]
      exact ⟨k, by omega, hcontain hz⟩
    · have hle : w ω ≤ B := hwB ω
      set k : ℕ := B - w ω with hkdef
      have hweq : w ω = radius k := by simp only [hradiusdef, hkdef]; omega
      have hωlevel : ω ∈ level k := ⟨hωA, hweq⟩
      have hωin : ω ∈ level k \ Good := ⟨hωlevel, hg⟩
      have hzmem : z ∈ window (radius k) ω := by rw [← hweq]; exact hz
      refine Or.inl ?_
      simp only [Set.mem_iUnion, Finset.mem_range]
      refine ⟨k, by omega, ?_⟩
      rw [hWU_eq_windows]
      exact Set.mem_biUnion hωin hzmem
  -- The "not yet Good" leftover part of the split has measure zero.
  have hfirst0 : μ (⋃ k ∈ Finset.range (B + 1), windowUnion (radius k) (level k \ Good)) = 0 := by
    have hterms0 : ∀ k ∈ Finset.range (B + 1),
        μ (windowUnion (radius k) (level k \ Good)) = 0 := by
      intro k hk
      simp only [Finset.mem_range] at hk
      have hkB : k ≤ B := by omega
      obtain ⟨N, hsubN, hNmeas, hNnull⟩ := exists_measurable_superset_of_null (hLevelNull k hkB)
      have hsub : windowUnion (radius k) (level k \ Good) ⊆ windowUnion (radius k) N :=
        hWUmono (radius k) hsubN
      have hb : μ (windowUnion (radius k) N) ≤ (2 * radius k + 1) * μ N :=
        measure_iUnion_zIter_window_le σ hσ.toMeasurePreserving (radius k) hNmeas
      rw [hNnull, mul_zero] at hb
      exact le_antisymm ((measure_mono hsub).trans hb) bot_le
    have hchain0 : μ (⋃ k ∈ Finset.range (B + 1), windowUnion (radius k) (level k \ Good)) ≤ 0 :=
      calc μ (⋃ k ∈ Finset.range (B + 1), windowUnion (radius k) (level k \ Good))
          ≤ ∑ k ∈ Finset.range (B + 1), μ (windowUnion (radius k) (level k \ Good)) :=
            measure_biUnion_finset_le _ _
        _ = 0 := Finset.sum_eq_zero hterms0
    exact le_antisymm hchain0 bot_le
  -- The Good-witness union reindexes into `A'`'s window union.
  have hFinalEq : (⋃ k ∈ Finset.range (B + 1), windowUnion (radius k) (Piece k))
      = ⋃ ω ∈ A', window (w ω) ω := by
    ext z
    simp only [Set.mem_iUnion, hA'def]
    constructor
    · rintro ⟨k, hk, hz⟩
      rw [hWU_eq_windows] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨x, hxPiece, hzx⟩ := hz
      have hwx : w x = radius k := ((hPieceSpec k).1 hxPiece).1.2
      exact ⟨x, ⟨k, hk, hxPiece⟩, by rwa [hwx]⟩
    · rintro ⟨x, ⟨k, hk, hxPiece⟩, hz⟩
      have hwx : w x = radius k := ((hPieceSpec k).1 hxPiece).1.2
      refine ⟨k, hk, ?_⟩
      rw [hWU_eq_windows]
      simp only [Set.mem_iUnion]
      exact ⟨x, hxPiece, by rwa [← hwx]⟩
  -- Assemble the final bound.
  have hchain : μ (⋃ k ∈ Finset.range (B + 1), windowUnion (3 * radius k + 1) (Piece k))
      ≤ 3 * μ (⋃ ω ∈ A', window (w ω) ω) :=
    calc μ (⋃ k ∈ Finset.range (B + 1), windowUnion (3 * radius k + 1) (Piece k))
        ≤ ∑ k ∈ Finset.range (B + 1), μ (windowUnion (3 * radius k + 1) (Piece k)) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ Finset.range (B + 1), (2 * ((3 * radius k + 1 : ℕ) : ℝ≥0∞) + 1) * μ (Piece k) :=
          Finset.sum_le_sum (fun k _ =>
            measure_iUnion_zIter_window_le σ hσ.toMeasurePreserving (3 * radius k + 1) (hMeas k).2)
      _ = ∑ k ∈ Finset.range (B + 1), 3 * ((2 * radius k + 1) * μ (Piece k)) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          push_cast
          ring
      _ = ∑ k ∈ Finset.range (B + 1), 3 * μ (windowUnion (radius k) (Piece k)) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          congr 1
          exact (measure_iUnion_zIter_window_eq σ hσ.toMeasurePreserving (radius k)
            (hMeas k).2 (hPieceSpec k).2.1).symm
      _ = 3 * ∑ k ∈ Finset.range (B + 1), μ (windowUnion (radius k) (Piece k)) := by
          rw [Finset.mul_sum]
      _ = 3 * μ (⋃ k ∈ Finset.range (B + 1), windowUnion (radius k) (Piece k)) := by
          congr 1
          rw [measure_biUnion_finset (fun k _ k' _ hkk' => hWUCrossDisjoint k k' hkk')
            (fun k _ => measurableSet_windowUnion σ (radius k) (hMeas k).2)]
      _ = 3 * μ (⋃ ω ∈ A', window (w ω) ω) := by rw [hFinalEq]
  calc μ (⋃ ω ∈ A, window (w ω) ω)
      ≤ μ ((⋃ k ∈ Finset.range (B + 1), windowUnion (radius k) (level k \ Good)) ∪
          (⋃ k ∈ Finset.range (B + 1), windowUnion (3 * radius k + 1) (Piece k))) :=
        measure_mono hBigSubset
    _ ≤ μ (⋃ k ∈ Finset.range (B + 1), windowUnion (radius k) (level k \ Good)) +
          μ (⋃ k ∈ Finset.range (B + 1), windowUnion (3 * radius k + 1) (Piece k)) :=
        measure_union_le _ _
    _ = μ (⋃ k ∈ Finset.range (B + 1), windowUnion (3 * radius k + 1) (Piece k)) := by
        rw [hfirst0, zero_add]
    _ ≤ 3 * μ (⋃ ω ∈ A', window (w ω) ω) := hchain




end MultiplicativeErgodic
