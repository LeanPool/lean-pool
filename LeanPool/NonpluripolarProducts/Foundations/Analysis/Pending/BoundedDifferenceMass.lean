/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalSlotComparison

/-!
# Mass monotonicity for bounded differences: the abstract comparison argument

Let `μ c` be a family of finite measures on `M`, indexed by admissible potentials
`c` (in applications: the global mixed measure with `c` in a block of slots and
fixed bounded potentials elsewhere). Assume

* locality of maxima: `μ(max a c) = μ(a)` on `{c < a}`;
* pole sets are null, and every bounded `c` has the same total mass `V`;
* scaling: `μ((1 - ε) c - K) ≥ (1 - ε)^N μ(c)` for bounded `c`.

If `a ≤ b ≤ a + t`, then `μ(a)(M) ≤ μ(b)(M)` (`mass_le_of_le_add`).

Proof. The first two assumptions give the comparison principle
`μ(d){c < d} ≤ μ(c){c ≤ d}` for bounded `c`, `d`. Put `aₖ = max(a, -k)`,
`bₖ = max(b, -k)` and `d = (1 - ε) bₖ - ε k + 1`. Then `{b ≤ -k} ⊆ {aₖ < d}` and
`{aₖ ≤ d} ⊆ {a ≤ -k + (t + 1)/ε}`, so
`(1 - ε)^N μ(bₖ){b ≤ -k} ≤ μ(aₖ){a ≤ -k + (t+1)/ε}`. Locality of the truncation on
`{-k < a}` and the common mass `V` turn this into
`(1 - ε)^N (V - μ(b){-k < b}) ≤ V - μ(a){-k < a} + μ(a){a ≤ -k + (t+1)/ε}`.
Let `k → ∞` (pole sets are null), then `ε → 0`.
-/

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.BoundedDifferenceMass

open FirstPass FirstPass.GlobalPotentialPatches FirstPass.PositiveClasses
open MixedNonPluripolar GlobalNonPluripolar BoundedGlobalProduct GlobalSlotStokes
open GlobalMaxLocality UniformBoundedGlobalMass GlobalSlotComparison

noncomputable section

theorem ereal_trunc_lt_of_le {α β : EReal} {k ε : ℝ} (hab : α ≤ β)
    (hβ : β ≤ ((-k : ℝ) : EReal)) :
    max α ((-k : ℝ) : EReal) <
      (((1 - ε) * (max β ((-k : ℝ) : EReal)).toReal - (ε * k - 1) : ℝ) : EReal) := by
  rw [max_eq_right hβ, max_eq_right (hab.trans hβ), EReal.toReal_coe, EReal.coe_lt_coe_iff]
  linarith

theorem ereal_le_of_trunc_le {α β : EReal} {k ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t)
    (hab : α ≤ β) (hba : β ≤ α + (t : EReal)) (hβtop : β ≠ ⊤)
    (h : max α ((-k : ℝ) : EReal) ≤
      (((1 - ε) * (max β ((-k : ℝ) : EReal)).toReal - (ε * k - 1) : ℝ) : EReal)) :
    α ≤ ((-k + (t + 1) / ε : ℝ) : EReal) := by
  have hL : 0 ≤ (t + 1) / ε := div_nonneg (by linarith) hε.le
  by_cases hβ : β ≤ ((-k : ℝ) : EReal)
  · exact hab.trans (hβ.trans (EReal.coe_le_coe_iff.mpr (by linarith)))
  push Not at hβ
  have hβbot : β ≠ ⊥ := ne_bot_of_gt hβ
  have hαbot : α ≠ ⊥ := by
    rintro rfl
    exact hβbot (le_bot_iff.mp hba)
  have hαtop : α ≠ ⊤ := ne_top_of_le_ne_top hβtop hab
  lift β to ℝ using ⟨hβtop, hβbot⟩
  lift α to ℝ using ⟨hαtop, hαbot⟩
  rw [max_eq_left hβ.le, EReal.toReal_coe] at h
  have h1 : α ≤ (1 - ε) * β - (ε * k - 1) :=
    EReal.coe_le_coe_iff.mp ((le_max_left _ _).trans h)
  have h2 : β ≤ α + t := by exact_mod_cast hba
  have h3 : α ≤ β := by exact_mod_cast hab
  have h4 : β + k ≤ (t + 1) / ε := by
    rw [le_div_iff₀ hε]
    nlinarith
  exact EReal.coe_le_coe_iff.mpr (by linarith)

/-- Continuity from below of the strict superlevel sets, the pole set being null. -/
theorem tendsto_measure_superlevel {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {a : X → EReal} (hpole : μ {p | a p = ⊥} = 0) :
    Tendsto (fun k : ℕ => μ {p | ((-(k : ℝ) : ℝ) : EReal) < a p}) atTop
      (𝓝 (μ univ)) := by
  have hmono : Monotone (fun k : ℕ => {p | ((-(k : ℝ) : ℝ) : EReal) < a p}) := by
    intro k l hkl p hp
    exact lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr (by simp [hkl])) hp
  have hU : (⋃ k : ℕ, {p | ((-(k : ℝ) : ℝ) : EReal) < a p}) = univ \ {p | a p = ⊥} := by
    ext p
    simp only [mem_iUnion, mem_ofPred_eq, Set.mem_sdiff, mem_univ, true_and]
    constructor
    · rintro ⟨k, hk⟩ h
      rw [h] at hk
      exact not_lt_bot hk
    · intro h
      induction hp : a p using EReal.rec with
      | bot => exact absurd hp h
      | top => exact ⟨0, by simp⟩
      | coe r =>
        obtain ⟨k, hk⟩ := exists_nat_gt (-r)
        exact ⟨k, EReal.coe_lt_coe_iff.mpr (by linarith)⟩
  have h := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rwa [hU, measure_sdiff_null hpole] at h

/-- Continuity from above of the sublevel sets of a finite measure, the pole set
being null. -/
theorem tendsto_measure_sublevel {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] {a : X → EReal}
    (ha : Measurable a) (hpole : μ {p | a p = ⊥} = 0) (L : ℝ) :
    Tendsto (fun k : ℕ => μ {p | a p ≤ ((-(k : ℝ) + L : ℝ) : EReal)}) atTop (𝓝 0) := by
  have hanti : Antitone (fun k : ℕ => {p | a p ≤ ((-(k : ℝ) + L : ℝ) : EReal)}) := by
    intro k l hkl p hp
    have : (k : ℝ) ≤ l := by exact_mod_cast hkl
    exact hp.trans (EReal.coe_le_coe_iff.mpr (by linarith))
  have hI : (⋂ k : ℕ, {p | a p ≤ ((-(k : ℝ) + L : ℝ) : EReal)}) ⊆ {p | a p = ⊥} := by
    intro p hp
    simp only [mem_iInter, mem_ofPred_eq] at hp ⊢
    induction hq : a p using EReal.rec with
    | bot => rfl
    | top => exact absurd (hq ▸ hp 0) (by simp)
    | coe r =>
      obtain ⟨k, hk⟩ := exists_nat_gt (L - r)
      have := hq ▸ hp k
      exact absurd (EReal.coe_le_coe_iff.mp this) (by linarith)
  have h := tendsto_measure_iInter_atTop (μ := μ)
    (fun k => (measurableSet_le ha measurable_const).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rwa [measure_mono_null hI hpole] at h

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  {θ : Fin n → ClosedRealOneOneForm n M}

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem thetaPlurisubharmonic_update {x : Fin n → M → EReal} {i₀ : Fin n} {a c : M → EReal}
    (hxa : ∀ i, ThetaPlurisubharmonic (θ i).val (Function.update x i₀ a i))
    (hc : ThetaPlurisubharmonic (θ i₀).val c) :
    ∀ i, ThetaPlurisubharmonic (θ i).val (Function.update x i₀ c i) := by
  intro i
  by_cases h : i = i₀
  · subst h; simpa using hc
  · simpa [Function.update_of_ne h] using hxa i

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] in
theorem isBoundedPotential_max {u v : M → EReal} (hu : IsBoundedPotential u)
    (hv : IsBoundedPotential v) : IsBoundedPotential (fun p => max (u p) (v p)) := by
  obtain ⟨a₁, b₁, h₁⟩ := hu
  obtain ⟨a₂, b₂, h₂⟩ := hv
  refine ⟨a₁, max b₁ b₂, fun p => ⟨(h₁ p).1.trans (le_max_left _ _), max_le ?_ ?_⟩⟩
  · exact (h₁ p).2.trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
  · exact (h₂ p).2.trans (EReal.coe_le_coe_iff.mpr (le_max_right _ _))

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] in
theorem isBoundedPotential_coe {f : M → ℝ} {Q : ℝ} (hf : ∀ p, |f p| ≤ Q) :
    IsBoundedPotential (fun p => ((f p : ℝ) : EReal)) :=
  ⟨-Q, Q, fun p => ⟨EReal.coe_le_coe_iff.mpr (neg_le_of_abs_le (hf p)),
    EReal.coe_le_coe_iff.mpr (le_of_abs_le (hf p))⟩⟩

variable [Nonempty M]

omit [TopologicalSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] in
/-- **Mass monotonicity for a bounded difference, for an abstract family.**
`μ c hc` is a family of finite measures indexed by admissible potentials `c`, local
under maxima, null on poles, of common total mass `V` on bounded potentials, and
scaling by at least `(1 - ε)^N` under `c ↦ (1 - ε) c - K`. Then `a ≤ b ≤ a + t`
implies `μ a (M) ≤ μ b (M)`. -/
theorem mass_le_of_le_add (P : (M → EReal) → Prop) (μ : ∀ c : M → EReal, P c → Measure M)
    (hmeas : ∀ c, P c → Measurable c) (hfin : ∀ c (hc : P c) S, μ c hc S < ⊤)
    (hpole : ∀ c (hc : P c), μ c hc {p | c p = ⊥} = 0)
    (hconstP : ∀ r : ℝ, P (fun _ => (r : EReal)))
    (htr : ∀ c, P c → ∀ r : ℝ, P (fun p => max (c p) (r : EReal)))
    (htrb : ∀ c, P c → ∀ r : ℝ, IsBoundedPotential (fun p => max (c p) (r : EReal)))
    (hmax : ∀ c d, P c → P d → P (fun p => max (c p) (d p)))
    (hloc : ∀ a c (ha : P a) (_hc : P c) (hm : P (fun p => max (a p) (c p))),
      (μ _ hm).restrict {p | c p < a p} = (μ a ha).restrict {p | c p < a p})
    (V : ℝ≥0∞) (hV : ∀ c (hc : P c), IsBoundedPotential c → μ c hc univ = V) (N : ℕ)
    (hscale : ∀ c (hc : P c), IsBoundedPotential c →
      ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ K : ℝ,
      ∃ hd : P (fun p => (((1 - ε) * (c p).toReal - K : ℝ) : EReal)),
        ∀ S, ENNReal.ofReal ((1 - ε) ^ N) * μ c hc S ≤ μ _ hd S)
    {a b : M → EReal} {t : ℝ} (ht : 0 ≤ t) (ha : P a) (hb : P b)
    (hab : ∀ p, a p ≤ b p) (hba : ∀ p, b p ≤ a p + (t : EReal)) :
    μ a ha univ ≤ μ b hb univ := by
  classical
  have hcongr : ∀ c c' (h : c = c') (hc : P c) (hc' : P c'), μ c hc = μ c' hc' := by
    intro c c' h hc hc'; subst h; rfl
  set μa := μ a ha with hμa
  set μb := μ b hb with hμb
  have := (⟨hfin a ha univ⟩ : IsFiniteMeasure μa)
  have := (⟨hfin b hb univ⟩ : IsFiniteMeasure μb)
  have hapole : μa {p | a p = ⊥} = 0 := hpole a ha
  have hbpole : μb {p | b p = ⊥} = 0 := hpole b hb
  -- truncations
  let tr (c : M → EReal) (k : ℕ) : M → EReal :=
    fun p => max (c p) ((-(k : ℝ) : ℝ) : EReal)
  have hV0 : V < ⊤ := by
    rw [← hV (tr a 0) (htr a ha _) (htrb a ha _)]
    exact hfin _ _ _
  -- the comparison principle
  have hcomp : ∀ c d (hc : P c) (hd : P d) (hm : P (fun p => max (c p) (d p))),
      μ _ hm univ = μ c hc univ → μ d hd {p | c p < d p} ≤ μ c hc {p | c p ≤ d p} := by
    intro c d hc hd hm hmass
    have hm1 : MeasurableSet {p | c p < d p} := measurableSet_lt (hmeas c hc) (hmeas d hd)
    have hm2 : MeasurableSet {p | d p < c p} := measurableSet_lt (hmeas d hd) (hmeas c hc)
    have hm' := hmax d c hd hc
    have e1 : μ _ hm {p | c p < d p} = μ d hd {p | c p < d p} := by
      have h := hloc d c hd hc hm'
      rw [hcongr _ _ (funext fun p => max_comm (d p) (c p)) hm' hm] at h
      simpa [Measure.restrict_apply MeasurableSet.univ] using
        congrArg (fun ν : Measure M => ν univ) h
    have e2 : μ _ hm {p | d p < c p} = μ c hc {p | d p < c p} := by
      have h := hloc c d hc hd hm
      simpa [Measure.restrict_apply MeasurableSet.univ] using
        congrArg (fun ν : Measure M => ν univ) h
    have hdisj : Disjoint {p | c p < d p} {p | d p < c p} :=
      disjoint_left.mpr fun p (h1 : c p < d p) (h2 : d p < c p) => lt_asymm h1 h2
    have hle : μ d hd {p | c p < d p} + μ c hc {p | d p < c p} ≤
        μ c hc {p | c p ≤ d p} + μ c hc {p | d p < c p} := by
      calc μ d hd {p | c p < d p} + μ c hc {p | d p < c p}
          = μ _ hm ({p | c p < d p} ∪ {p | d p < c p}) := by
            rw [measure_union hdisj hm2, e1, e2]
        _ ≤ μ _ hm univ := measure_mono (subset_univ _)
        _ = μ c hc univ := hmass
        _ = μ c hc {p | c p ≤ d p} + μ c hc {p | d p < c p} := by
            rw [← measure_union _ hm2, ← ofPred_or]
            · congr 1; ext p; simp [le_or_gt]
            · exact disjoint_left.mpr fun p (h1 : c p ≤ d p) (h2 : d p < c p) => not_lt.mpr h1 h2
    exact (ENNReal.add_le_add_iff_right (hfin c hc _).ne).mp hle
  -- locality of the truncation on `{-k < c}`
  have hloc' (c : M → EReal) (hc : P c) (k : ℕ) (S : Set M)
      (hS : S ⊆ {p | ((-(k : ℝ) : ℝ) : EReal) < c p}) :
      μ (tr c k) (htr c hc _) S = μ c hc S := by
    have h := hloc c (fun _ => ((-(k : ℝ) : ℝ) : EReal)) hc
      (hconstP _) (htr c hc _)
    have h2 := congrArg (fun ν : Measure M => ν S) h
    rwa [Measure.restrict_eq_self _ hS, Measure.restrict_eq_self _ hS] at h2
  -- the estimate at fixed `ε` and `k`
  have key : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ k : ℕ,
      (1 - ε) ^ N * (V.toReal - (μb {p | ((-(k : ℝ) : ℝ) : EReal) < b p}).toReal) ≤
        V.toReal - (μa {p | ((-(k : ℝ) : ℝ) : EReal) < a p}).toReal +
          (μa {p | a p ≤ ((-(k : ℝ) + (t + 1) / ε : ℝ) : EReal)}).toReal := by
    intro ε hε0 hε1 k
    have hxak := htr a ha (-(k : ℝ))
    have hxbk := htr b hb (-(k : ℝ))
    set μak := μ (tr a k) hxak
    set μbk := μ (tr b k) hxbk
    obtain ⟨hxd, hsc⟩ := hscale (tr b k) hxbk (htrb b hb _) ε hε0 hε1 (ε * k - 1)
    set d : M → EReal := fun p => (((1 - ε) * (tr b k p).toReal - (ε * k - 1) : ℝ) : EReal)
      with hd
    have hxm := hmax (tr a k) d hxak hxd
    have hdb : IsBoundedPotential d := by
      obtain ⟨Q, hQ⟩ := IsBoundedPotential.exists_abs_toReal_le (htrb b hb (-(k : ℝ)))
      refine isBoundedPotential_coe (Q := |1 - ε| * Q + |ε * k - 1|) fun p => ?_
      calc |(1 - ε) * (tr b k p).toReal - (ε * k - 1)|
          ≤ |(1 - ε) * (tr b k p).toReal| + |ε * k - 1| := abs_sub _ _
        _ ≤ |1 - ε| * Q + |ε * k - 1| := by
          rw [abs_mul]; gcongr; exact hQ p
    have hmass : μ _ hxm univ = μak univ := by
      rw [hV _ hxm (isBoundedPotential_max (htrb a ha _) hdb), hV _ hxak (htrb a ha _)]
    have hcomp' := hcomp _ _ hxak hxd hxm hmass
    set A := {p | b p ≤ ((-(k : ℝ) : ℝ) : EReal)} with hA
    set D := {p | a p ≤ ((-(k : ℝ) + (t + 1) / ε : ℝ) : EReal)} with hD
    have hAsub : A ⊆ {p | tr a k p < d p} := fun p hp =>
      ereal_trunc_lt_of_le (ε := ε) (hab p) hp
    have hCsub : {p | tr a k p ≤ d p} ⊆ D := fun p hp =>
      ereal_le_of_trunc_le hε0 ht (hab p) (hba p)
        (fun h => IsBoundedPotential.ne_top (htrb b hb (-(k : ℝ))) p
          (show max (b p) _ = ⊤ by rw [h]; exact max_eq_left le_top)) hp
    have hAm : MeasurableSet A := measurableSet_le (hmeas b hb) measurable_const
    have hSam : MeasurableSet {p | a p ≤ ((-(k : ℝ) : ℝ) : EReal)} :=
      measurableSet_le (hmeas a ha) measurable_const
    have E1 : ENNReal.ofReal ((1 - ε) ^ N) * μbk A ≤ μak D :=
      (hsc A).trans ((measure_mono hAsub).trans (hcomp'.trans (measure_mono hCsub)))
    have hAc : Aᶜ = {p | ((-(k : ℝ) : ℝ) : EReal) < b p} := by ext p; simp [hA]
    have E2 : μbk A + μb {p | ((-(k : ℝ) : ℝ) : EReal) < b p} = V := by
      rw [← hloc' b hb k _ subset_rfl, ← hAc, measure_add_measure_compl hAm]
      exact hV _ hxbk (htrb b hb _)
    have E3 : μak {p | a p ≤ ((-(k : ℝ) : ℝ) : EReal)} +
        μa {p | ((-(k : ℝ) : ℝ) : EReal) < a p} = V := by
      have hc : {p | a p ≤ ((-(k : ℝ) : ℝ) : EReal)}ᶜ =
          {p | ((-(k : ℝ) : ℝ) : EReal) < a p} := by
        ext p; simp
      rw [← hloc' a ha k _ subset_rfl, ← hc, measure_add_measure_compl hSam]
      exact hV _ hxak (htrb a ha _)
    have E4 : μak D ≤ μak {p | a p ≤ ((-(k : ℝ) : ℝ) : EReal)} + μa D :=
      calc μak D = μak (D ∩ {p | a p ≤ ((-(k : ℝ) : ℝ) : EReal)}) +
            μak (D \ {p | a p ≤ ((-(k : ℝ) : ℝ) : EReal)}) :=
          (measure_inter_add_sdiff D hSam).symm
        _ ≤ μak {p | a p ≤ ((-(k : ℝ) : ℝ) : EReal)} + μa D := by
          refine add_le_add (measure_mono inter_subset_right) ?_
          rw [hloc' a ha k (D \ {p | a p ≤ ((-(k : ℝ) : ℝ) : EReal)}) (fun p hp =>
            show ((-(k : ℝ) : ℝ) : EReal) < a p from not_le.mp hp.2)]
          exact measure_mono sdiff_subset
    -- real conversion
    have hfin' (ν : Measure M) (S : Set M) (h : ν S ≤ V) : ν S ≠ ⊤ := (h.trans_lt hV0).ne
    have hbkA : μbk A ≤ V := E2 ▸ le_self_add
    have hbS : μb {p | ((-(k : ℝ) : ℝ) : EReal) < b p} ≤ V := E2 ▸ le_add_self
    have hak0 : μak {p | a p ≤ ((-(k : ℝ) : ℝ) : EReal)} ≤ V := E3 ▸ le_self_add
    have haS : μa {p | ((-(k : ℝ) : ℝ) : EReal) < a p} ≤ V := E3 ▸ le_add_self
    have hE2 := congrArg ENNReal.toReal E2
    have hE3 := congrArg ENNReal.toReal E3
    rw [ENNReal.toReal_add (hfin' _ _ hbkA) (hfin' _ _ hbS)] at hE2
    rw [ENNReal.toReal_add (hfin' _ _ hak0) (hfin' _ _ haS)] at hE3
    have hE1 := ENNReal.toReal_mono (hfin _ hxak D).ne E1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (by linarith) N)] at hE1
    have hE4 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin' _ _ hak0,
      (hfin a ha D).ne⟩) E4
    rw [ENNReal.toReal_add (hfin' _ _ hak0) (hfin a ha D).ne] at hE4
    have h1 : V.toReal - (μb {p | ((-(k : ℝ) : ℝ) : EReal) < b p}).toReal =
        (μbk A).toReal := by
      linarith
    rw [h1]
    linarith
  -- `k → ∞`, then `ε → 0`
  have hma := ENNReal.tendsto_toReal (measure_ne_top μa univ) |>.comp
    (tendsto_measure_superlevel μa hapole)
  have hmb := ENNReal.tendsto_toReal (measure_ne_top μb univ) |>.comp
    (tendsto_measure_superlevel μb hbpole)
  have hlim : ∀ ε : ℝ, 0 < ε → ε < 1 →
      (1 - ε) ^ N * (V.toReal - (μb univ).toReal) ≤ V.toReal - (μa univ).toReal := by
    intro ε hε0 hε1
    have hea := ENNReal.tendsto_toReal ENNReal.zero_ne_top |>.comp
      (tendsto_measure_sublevel μa (hmeas a ha) hapole ((t + 1) / ε))
    have hL := ((tendsto_const_nhds (x := V.toReal)).sub hmb).const_mul ((1 - ε) ^ N)
    have hR := ((tendsto_const_nhds (x := V.toReal)).sub hma).add hea
    simpa using le_of_tendsto_of_tendsto' hL hR (key ε hε0 hε1)
  have hfinal : V.toReal - (μb univ).toReal ≤ V.toReal - (μa univ).toReal := by
    have hT : Tendsto (fun ε : ℝ => (1 - ε) ^ N * (V.toReal - (μb univ).toReal)) (𝓝[>] 0)
        (𝓝 (V.toReal - (μb univ).toReal)) := by
      have := (((continuous_const.sub continuous_id).pow N).mul continuous_const).tendsto
        (0 : ℝ) (f := fun ε : ℝ => (1 - ε) ^ N * (V.toReal - (μb univ).toReal))
      simpa using this.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hT ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact hlim ε hε.1 hε.2
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp (by linarith)

end

end SGPT.Foundations.Analysis.Pending.BoundedDifferenceMass
