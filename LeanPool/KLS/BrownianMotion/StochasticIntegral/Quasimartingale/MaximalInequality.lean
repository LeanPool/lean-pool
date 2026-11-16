/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohit Manokaran, Rémy Degenne
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: Lean/Mathlib v4.35.0 replacements
-- of deprecated names (identifier-only); see vendor/port.patch.
module

public import LeanPool.KLS.BrownianMotion.Auxiliary.Filtration
public import LeanPool.KLS.BrownianMotion.Auxiliary.Upcrossing
public import LeanPool.KLS.BrownianMotion.StochasticIntegral.Quasimartingale.Basic

/-! # Maximal inequality for real quasimartingales -/

@[expose] public section

open MeasureTheory Finset Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory.SimpleProcess

namespace ProbabilityTheory

variable {ι Ω : Type*} [LinearOrder ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → ℝ} {τ σ : Ω → WithTop ι} {i : ι}

section Bridge

/-- The monotone enumeration of a finite set of times, extended by the constant `t` at indices
beyond `#F`. -/
@[grind]
noncomputable def finIdx (F : Finset ι) (t : ι) : ℕ → ι := fun k ↦
  if h : k < #F then (F.orderIsoOfFin rfl ⟨k, h⟩ : ι) else t

variable {F : Finset ι} {t : ι} {k l : ℕ}

lemma finIdx_mem (h : k < #F) : finIdx F t k ∈ F := by grind

lemma finIdx_eq_of_card_le (h : #F ≤ k) : finIdx F t k = t := by grind

lemma finIdx_le (hF : ∀ s ∈ F, s ≤ t) (k : ℕ) : finIdx F t k ≤ t := by grind

lemma finIdx_lt_of_lt (hkl : k < l) (hl : l < #F) : finIdx F t k < finIdx F t l := by
  rw [finIdx, finIdx, dite_eq_left (hkl.trans hl), dite_eq_left hl]
  exact mod_cast (F.orderIsoOfFin rfl).strictMono (mod_cast hkl)

lemma finIdx_lt_finIdx_iff (hk : k < #F) (hl : l < #F) :
    finIdx F t k < finIdx F t l ↔ k < l := by
  rw [finIdx, finIdx, dite_eq_left hk, dite_eq_left hl, Subtype.coe_lt_coe, OrderIso.lt_iff_lt, Fin.mk_lt_mk]

@[gcongr]
lemma finIdx_monotone (hF : ∀ s ∈ F, s ≤ t) : Monotone (finIdx F t) := by
  intro k l hkl
  rcases eq_or_lt_of_le hkl with rfl | hkl
  · exact le_rfl
  rcases lt_or_ge l #F with h | h
  · exact (finIdx_lt_of_lt hkl h).le
  · grind

lemma exists_finIdx_eq {s : ι} (hs : s ∈ F) : ∃ k, k < #F ∧ finIdx F t k = s := by
  obtain ⟨k, hk⟩ := (F.orderIsoOfFin rfl).surjective ⟨s, hs⟩
  exact ⟨k, k.2, by rw [finIdx, dite_eq_left k.2, Fin.eta, hk]⟩

lemma finIdx_zero_eq_bot [OrderBot ι] (hbot : ⊥ ∈ F) : finIdx F t 0 = ⊥ := by
  have hcard : 0 < #F := card_pos.2 ⟨⊥, hbot⟩
  obtain ⟨k, hk, hkeq⟩ := exists_finIdx_eq (t := t) hbot
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact hkeq
  · exact le_bot_iff.1 (hkeq ▸ (finIdx_lt_of_lt hkpos hk).le)

/-- Construct an elementary predictable set from a sequence of times and a sequence of measurable
functions. -/
@[simps]
noncomputable
def elemPredSetOfSeq [OrderBot ι] {idx : ℕ → ι} (hidx : Monotone idx) {W : ℕ → Ω → ℝ} (n : ℕ)
    (hWmeas : ∀ k, k < n → Measurable[𝓕 (idx k)] (W k)) :
    ElementaryPredictableSet 𝓕 :=
  letI K : Finset ℕ := {k ∈ range n | idx k < idx (k + 1)}
  { setBot := ∅
    I := K.image fun k ↦ (idx k, idx (k + 1))
    set := fun p ↦ if h : ∃ k ∈ K, (idx k, idx (k + 1)) = p then W h.choose ⁻¹' {1} else ∅
    le_of_mem_I := by grind
    measurableSet_setBot := @MeasurableSet.empty _ (𝓕 ⊥)
    measurableSet_set p hp := by
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hp
      have hex : ∃ k' ∈ K, (idx k', idx (k' + 1)) = (idx k, idx (k + 1)) := ⟨k, hk, rfl⟩
      simp only [dite_eq_left hex]
      obtain ⟨hcK, hceq⟩ := hex.choose_spec
      have h1 : idx hex.choose = idx k := (Prod.ext_iff.1 hceq).1
      have hKmem {k} (hk : k ∈ K) : k < n ∧ idx k < idx (k + 1) := by simpa [K] using hk
      have h2 : MeasurableSet[𝓕 (idx hex.choose)] (W hex.choose ⁻¹' {1}) :=
        hWmeas _ (hKmem hcK).1 (measurableSet_singleton 1)
      rwa [h1] at h2
    pairwiseDisjoint p hp q hq hpq := by
      simp only [coe_image, Set.mem_image, mem_coe] at hp hq
      obtain ⟨k, hk, rfl⟩ := hp
      obtain ⟨l, hl, rfl⟩ := hq
      have hkl : k ≠ l := fun h ↦ hpq (by rw [h])
      have hIoc : Disjoint (Set.Ioc (idx k) (idx (k + 1))) (Set.Ioc (idx l) (idx (l + 1))) := by
        rcases lt_or_gt_of_ne hkl with h | h
        · exact Set.Ioc_disjoint_Ioc_of_le (hidx (Nat.succ_le_of_lt h))
        · exact (Set.Ioc_disjoint_Ioc_of_le (hidx (Nat.succ_le_of_lt h))).symm
      exact Set.disjoint_left.2 fun x hx hx' ↦
        Set.disjoint_left.1 hIoc hx.1 hx'.1 }

lemma integral_elemPredSetOfSeq [OrderBot ι] {t : ι} (n : ℕ) {idx : ℕ → ι}
    (hidx : Monotone idx) (hidxt : ∀ k, idx k ≤ t) {W : ℕ → Ω → ℝ}
    (hW01 : ∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1)
    (hWmeas : ∀ k, k < n → Measurable[𝓕 (idx k)] (W k)) (ω : Ω) :
    ((elemPredSetOfSeq hidx n hWmeas).indicator (1 : ℝ) ● X) t ω =
      ∑ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω) := by
  let K : Finset ℕ := {k ∈ range n | idx k < idx (k + 1)}
  have hKmem : ∀ {k}, k ∈ K → k < n ∧ idx k < idx (k + 1) := by
    intro k hk
    simpa [K] using hk
  have hinj : Set.InjOn (fun k ↦ (idx k, idx (k + 1))) K := by
    intro k hk l hl hkl
    simp only [Prod.mk.injEq] at hkl
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd ((hidx (Nat.succ_le_of_lt h)).trans_eq hkl.1.symm) (hKmem hk).2.not_ge
    · exact absurd ((hidx (Nat.succ_le_of_lt h)).trans_eq hkl.1) (hKmem hl).2.not_ge
  rw [ElementaryPredictableSet.integral_indicator_apply]
  simp only [elemPredSetOfSeq_I, elemPredSetOfSeq_set]
  simp only [mem_filter, mem_range, ContinuousLinearMap.mul_apply', one_mul]
  rw [sum_image fun k hk l hl h ↦ hinj hk hl h]
  simp only [mem_filter, mem_range, Prod.mk.injEq]
  refine (sum_congr rfl fun k hk ↦ ?_).trans (sum_subset (filter_subset _ _) fun k hk hkK ↦ ?_)
  · -- per-term equality on K
    have h : ∃ k_1 ∈ {k ∈ range n | idx k < idx (k + 1)},
      (idx k_1, idx (k_1 + 1)) = (idx k, idx (k + 1)) := ⟨k, hk, rfl⟩
    rw [dite_eq_left h]
    suffices (W h.choose ⁻¹' {1}).indicator
        (fun ω ↦ stoppedProcess X (fun x ↦ ↑t) (idx (k + 1)) ω -
          stoppedProcess X (fun x ↦ ↑t) (idx k) ω) ω =
        W k ω * (X (idx (k + 1)) ω - X (idx k) ω) by
      convert this <;> simp
    have hchoose : h.choose = k := hinj h.choose_spec.1 hk h.choose_spec.2
    have hst : ∀ j, stoppedProcess X (fun _ ↦ (t : WithTop ι)) (idx j) ω = X (idx j) ω :=
      fun j ↦ stoppedProcess_eq_of_le (mod_cast hidxt j)
    simp only [hchoose]
    rcases hW01 k (hKmem hk).1 ω with h0 | h1
    · simp [h0]
    · simp [h1, hst, -stoppedProcess_of_eq_coe]
  · -- terms outside K vanish
    have hno : ¬ idx k < idx (k + 1) := fun h ↦ hkK (by simp [K, mem_range.1 hk, h])
    have heq : idx (k + 1) = idx k :=
      le_antisymm (not_lt.1 hno) (hidx k.le_succ)
    rw [heq, sub_self, mul_zero]

end Bridge

/-! ### Upcrossing and alternation bounds along finite time sets -/

section UpcrossingBound

variable {a b : ℝ} {t : ι} {F : Finset ι} {m : ℕ}

/-- An elementary predictable set representing upcrossings within a given interval. -/
noncomputable
def upcrossingWithinPredSet [OrderBot ι] (a b : ℝ) (F : Finset ι) (hF : ∀ s ∈ F, s ≤ t)
    (hX : StronglyAdapted 𝓕 X) :
    ElementaryPredictableSet 𝓕 :=
  letI f : ℕ → Ω → ℝ := fun k ω ↦ X (finIdx F t k) ω
  haveI hadapt : StronglyAdapted (𝓕.indexComap (finIdx_monotone hF)) f :=
    fun j ↦ hX (finIdx F t j)
  elemPredSetOfSeq (W := upcrossingStrat a b f #F) (finIdx_monotone hF) #F
    fun k _ ↦ (hadapt.upcrossingStrat k).measurable

lemma mul_upcrossingsBefore_le_integral_add_posPart [OrderBot ι]
    (hX : StronglyAdapted 𝓕 X) (hab : a < b) (hF : ∀ s ∈ F, s ≤ t) (ω : Ω) :
    letI f : ℕ → Ω → ℝ := fun k ω ↦ X (finIdx F t k) ω
    haveI hadapt : StronglyAdapted (𝓕.indexComap (finIdx_monotone hF)) f :=
      fun j ↦ hX (finIdx F t j)
    letI S := elemPredSetOfSeq (W := upcrossingStrat a b f #F) (finIdx_monotone hF) #F fun k _ ↦
      (hadapt.upcrossingStrat k).measurable
    (b - a) * (upcrossingsBefore a b f #F ω : ℝ)
      ≤ (S.indicator (1 : ℝ) ● X) t ω + (a - X t ω)⁺ := by
  let f : ℕ → Ω → ℝ := fun k ω ↦ X (finIdx F t k) ω
  have hadapt : StronglyAdapted (𝓕.indexComap (finIdx_monotone hF)) f :=
    fun j ↦ hX (finIdx F t j)
  let S := elemPredSetOfSeq (W := upcrossingStrat a b f #F) (finIdx_monotone hF) #F fun k hk ↦
    (hadapt.upcrossingStrat k).measurable
  rw [integral_elemPredSetOfSeq (𝓕 := 𝓕) (X := X) #F (finIdx_monotone hF) (finIdx_le hF)
    (W := upcrossingStrat a b f #F) (fun k _ ω ↦ upcrossingStrat_eq_zero_or_one a b f #F k ω)
    (fun k _ ↦ (hadapt.upcrossingStrat k).measurable) ω]
  have h1 := mul_upcrossingsBefore_le_sum_add_posPart (f := f) (N := #F) (ω := ω) hab
  have hfn : f #F ω = X t ω := by unfold f; rw [finIdx_eq_of_card_le le_rfl]
  rwa [hfn] at h1

/-- Expectation bound on the number of upcrossings along a finite set of times `F ⊆ Iic t`,
from the boundedness of elementary stochastic integrals at time `t`. -/
lemma mul_integral_upcrossingsBefore_finIdx_le [OrderBot ι] [IsFiniteMeasure μ]
    (hX : Adapted 𝓕 X) (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator 1 ● X) t] ≤ C)
    (hab : a < b) (hF : ∀ s ∈ F, s ≤ t) :
    (b - a) * ∫ ω, (upcrossingsBefore a b (fun k ↦ X (finIdx F t k)) #F ω : ℝ) ∂μ
      ≤ C + ∫ ω, (a - X t ω)⁺ ∂μ := by
  let f : ℕ → Ω → ℝ := fun k ω ↦ X (finIdx F t k) ω
  have hadapt : StronglyAdapted (𝓕.indexComap (finIdx_monotone hF)) f :=
    Adapted.stronglyAdapted <| fun j ↦ hX (finIdx F t j)
  let S := elemPredSetOfSeq (W := upcrossingStrat a b f #F) (finIdx_monotone hF) #F fun k hk ↦
    (hadapt.upcrossingStrat k).measurable
  have hintS : Integrable ((S.indicator (1 : ℝ) ● X) t) μ :=
    ElementaryPredictableSet.integrable_integral_real hXint S 1 t
  have hintmax : Integrable (fun ω ↦ (a - X t ω)⁺) μ :=
    (((integrable_const a).sub (hXint t))).pos_part
  have hintcount : Integrable (fun ω ↦ (upcrossingsBefore a b f #F ω : ℝ)) μ :=
    hadapt.integrable_upcrossingsBefore hab
  calc (b - a) * ∫ ω, (upcrossingsBefore a b f #F ω : ℝ) ∂μ
  _ = ∫ ω, (b - a) * (upcrossingsBefore a b f #F ω : ℝ) ∂μ := (integral_const_mul _ _).symm
  _ ≤ ∫ ω, ((S.indicator (1 : ℝ) ● X) t ω + (a - X t ω)⁺) ∂μ :=
    integral_mono (hintcount.const_mul _) (hintS.add hintmax)
      (mul_upcrossingsBefore_le_integral_add_posPart hX.stronglyAdapted hab hF)
  _ = μ[(S.indicator (1 : ℝ) ● X) t] + ∫ ω, (a - X t ω)⁺ ∂μ := integral_add hintS hintmax
  _ ≤ C + ∫ ω, (a - X t ω)⁺ ∂μ := by gcongr; exact hC S

variable (X) in
/-- The event that `X` makes `m` alternations from at most `a` to at least `b` at
increasing times inside the finite time set `F`. The levels are non-strict (`X ≤ a`, `b ≤ X`) to
match the `Set.Iic a` / `Set.Ici b` hitting conditions of `MeasureTheory.upcrossingsBefore`; with
this convention `altSet` coincides with the event of at least `m` upcrossings (see
`altSet_eq_upcrossingsBefore`). -/
def altSet (F : Finset ι) (a b : ℝ) (m : ℕ) : Set Ω :=
  {ω | ∃ c : ℕ → ι, (∀ i, i + 1 < 2 * m → c i < c (i + 1)) ∧ (∀ i < 2 * m, c i ∈ F)
    ∧ (∀ i < m, X (c (2 * i)) ω ≤ a) ∧ (∀ i < m, b ≤ X (c (2 * i + 1)) ω)}

lemma altSet_mono {F G : Finset ι} (h : F ⊆ G) : altSet X F a b m ⊆ altSet X G a b m :=
  fun _ ⟨c, hc1, hc2, hca, hcb⟩ ↦ ⟨c, hc1, fun i hi ↦ h (hc2 i hi), hca, hcb⟩

lemma altSet_mono' {a' b' : ℝ} (hab : a ≤ a') (hba : b' ≤ b) :
    altSet X F a b m ⊆ altSet X F a' b' m :=
  fun _ ⟨c, hc1, hc2, hca, hcb⟩ ↦ ⟨c, hc1, hc2, by grind⟩

/-- `altSet X F a b m` is exactly the event of at least `m` upcrossings of `[a, b]` by the
monotone enumeration `finIdx F t` of `F`. -/
lemma altSet_eq_upcrossingsBefore (hab : a < b) :
    altSet X F a b m = {ω | m ≤ upcrossingsBefore a b (fun k ↦ X (finIdx F t k)) #F ω} := by
  refine subset_antisymm ?_ ?_
  · rintro ω ⟨c, hc1, hc2, hca, hcb⟩
    have hex : ∀ i, i < 2 * m → ∃ k, k < #F ∧ finIdx F t k = c i :=
      fun i hi ↦ exists_finIdx_eq (hc2 i hi)
    let c' : ℕ → ℕ := fun i ↦ if hi : i < 2 * m then (hex i hi).choose else 0
    have hc'spec : ∀ i (hi : i < 2 * m), c' i < #F ∧ finIdx F t (c' i) = c i := by grind
    refine le_upcrossingsBefore_of_alternating hab (c := c') ?_ (by grind) ?_ ?_
    · intro i hi
      obtain ⟨hlt1, heq1⟩ := hc'spec i (by lia)
      obtain ⟨hlt2, heq2⟩ := hc'spec (i + 1) hi
      rw [← finIdx_lt_finIdx_iff (t := t) hlt1 hlt2, heq1, heq2]
      exact hc1 i hi
    · intro i hi
      obtain ⟨_, heq⟩ := hc'spec (2 * i) (by lia)
      simp only [heq]
      exact hca i hi
    · intro i hi
      obtain ⟨_, heq⟩ := hc'spec (2 * i + 1) (by lia)
      simp only [heq]
      exact hcb i hi
  · intro ω hω
    obtain ⟨c, hmono, hcN, ha, hb⟩ := exists_alternating_of_le_upcrossingsBefore hab hω
    exact ⟨fun i ↦ finIdx F t (c i), fun i hi ↦ finIdx_lt_of_lt (hmono i hi) (hcN (i + 1) hi),
      fun i hi ↦ finIdx_mem (hcN i hi), fun i hi ↦ ha i hi, fun i hi ↦ hb i hi⟩

/-- Quantitative alternation bound: the probability of `m` alternations along any finite
`F ⊆ Iic t` is at most `K / m` with `K` independent of `F` and `m`. -/
lemma measureReal_altSet_le [OrderBot ι] [IsFiniteMeasure μ]
    (hX : Adapted 𝓕 X) (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C)
    (hab : a < b) (hm : 0 < m) (hF : ∀ s ∈ F, s ≤ t) :
    μ.real (altSet X F a b m) ≤ (C + ∫ ω, (a - X t ω)⁺ ∂μ) / (b - a) / m := by
  let f : ℕ → Ω → ℝ := fun k ω ↦ X (finIdx F t k) ω
  have hadapt : StronglyAdapted (𝓕.indexComap (finIdx_monotone hF)) f :=
    Adapted.stronglyAdapted <| fun j ↦ hX (finIdx F t j)
  rw [altSet_eq_upcrossingsBefore (t := t) hab, div_div, le_div_iff₀ (by positivity)]
  calc μ.real {ω | m ≤ upcrossingsBefore a b f #F ω} * ((b - a) * m)
  _ = μ.real {ω | (m : ℝ) ≤ (upcrossingsBefore a b f #F ω : ℝ)} * ((b - a) * m) := by norm_cast
  _ = (b - a) * ((m : ℝ) * μ.real {ω | (m : ℝ) ≤ (upcrossingsBefore a b f #F ω : ℝ)}) := by ring
  _ ≤ (b - a) * ∫ ω, (upcrossingsBefore a b f #F ω : ℝ) ∂μ := by
    gcongr
    exact mul_meas_ge_le_integral_of_nonneg
      (ae_of_all _ fun ω ↦ by positivity) (hadapt.integrable_upcrossingsBefore hab) m
  _ ≤ C + ∫ ω, (a - X t ω)⁺ ∂μ :=
    mul_integral_upcrossingsBefore_finIdx_le (μ := μ) hX hXint hC hab hF

/-- The set of outcomes where there are infinitely many alternations of `X` from below `a`
to above `b` at times in a set `T` below `t`. -/
def infiniteAlt (T : Set ι) (t : ι) (X : ι → Ω → ℝ) (a b : ℝ) : Set Ω :=
  ⋂ m : ℕ, ⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}, altSet X F a b m

lemma infiniteAlt_mono' {T : Set ι} {a' b' : ℝ} (h : a ≤ a') (h' : b' ≤ b) :
    infiniteAlt T t X a b ⊆ infiniteAlt T t X a' b' := by
  unfold infiniteAlt
  gcongr
  exact altSet_mono' h h'

lemma infiniteAlt_mono'' {T : Set ι} {s t : ι} (h : s ≤ t) :
    infiniteAlt T s X a b ⊆ infiniteAlt T t X a b := by
  unfold infiniteAlt
  gcongr with F
  refine Set.iUnion_mono' ?_
  intro hF
  simp only [Set.subset_inter_iff, Set.mem_ofPred_eq] at hF
  simp only [subset_refl, Set.subset_inter_iff, Set.mem_ofPred_eq, exists_prop, and_true]
  refine ⟨hF.1, hF.2.trans ?_⟩
  grind

end UpcrossingBound

/-! ### Selection of alternating tuples from frequent oscillation -/

section Selection

variable [TopologicalSpace ι] [OrderTopology ι]

variable {T : Set ι} {x d : ι} {a b : ℝ} {ω : Ω}

lemma Ioo_inter_mem_nhdsWithin_inter_Ioi (hxd : x < d) : Set.Ioo x d ∩ T ∈ 𝓝[T ∩ Set.Ioi x] x := by
  simp only [inter_mem_iff]
  constructor
  · rw [mem_nhdsWithin_iff_eventually]
    filter_upwards [eventually_lt_nhds hxd] with s hs
    grind
  · exact mem_nhdsWithin_self_inter

lemma Ioo_inter_mem_nhdsWithin_inter_Iio (hxd : d < x) : Set.Ioo d x ∩ T ∈ 𝓝[T ∩ Set.Iio x] x := by
  simp only [inter_mem_iff]
  constructor
  · rw [mem_nhdsWithin_iff_eventually]
    filter_upwards [eventually_gt_nhds hxd] with s hs
    grind
  · exact mem_nhdsWithin_self_inter

lemma exists_finset_altSet_of_frequently_right (hxd : x < d)
    (hfa : ∃ᶠ s in 𝓝[T ∩ Set.Ioi x] x, X s ω < a)
    (hfb : ∃ᶠ s in 𝓝[T ∩ Set.Ioi x] x, b < X s ω) (m : ℕ) :
    ∃ F : Finset ι, ↑F ⊆ T ∩ Set.Ioo x d ∧ ω ∈ altSet X F a b m := by
  -- descending selection: even picks above `b`, odd picks below `a`
  have hsel k : ∃ c : ℕ → ι, (∀ i, i + 1 < k → c (i + 1) < c i)
      ∧ (∀ i < k, c i ∈ T ∩ Set.Ioo x d)
      ∧ (∀ i < k, if Even i then b < X (c i) ω else X (c i) ω < a) := by
    induction k with
    | zero => exact ⟨fun _ ↦ d, by lia, by lia, by lia⟩
    | succ k ih =>
      obtain ⟨c, hdesc, hmem, hval⟩ := ih
      -- previous lower endpoint
      set u : ι := if hk : 0 < k then c (k - 1) else d with hu
      have hxu : x < u := by grind
      have hud : u ≤ d := by grind
      have hU : Set.Ioo x u ∩ T ∈ 𝓝[T ∩ Set.Ioi x] x := Ioo_inter_mem_nhdsWithin_inter_Ioi hxu
      have hpick : ∃ s, s ∈ Set.Ioo x u ∩ T
          ∧ if Even k then b < X s ω else X s ω < a := by
        by_cases hk : Even k
        · simp only [ite_eq_left hk]
          obtain ⟨s, hs1, hs2⟩ := (hfb.and_eventually (Filter.eventually_of_mem hU
            (fun s hs ↦ hs))).exists
          exact ⟨s, hs2, hs1⟩
        · simp only [ite_eq_right hk]
          obtain ⟨s, hs1, hs2⟩ := (hfa.and_eventually (Filter.eventually_of_mem hU
            (fun s hs ↦ hs))).exists
          exact ⟨s, hs2, hs1⟩
      obtain ⟨s, ⟨hsIoo, hsT⟩, hsval⟩ := hpick
      exact ⟨Function.update c k s, by grind⟩
  obtain ⟨c, hdesc, hmem, hval⟩ := hsel (2 * m)
  -- reverse the order
  set ca : ℕ → ι := fun j ↦ c (2 * m - 1 - j) with hca
  exact ⟨(range (2 * m)).image ca, by grind, ca, by grind⟩

lemma mem_infiniteAlt_of_frequently_right (hxd : x < d)
    (hfa : ∃ᶠ s in 𝓝[T ∩ Set.Ioi x] x, X s ω < a)
    (hfb : ∃ᶠ s in 𝓝[T ∩ Set.Ioi x] x, b < X s ω) :
    ω ∈ infiniteAlt T d X a b := by
  simp only [infiniteAlt, Set.mem_iInter, Set.mem_iUnion, Set.mem_ofPred_eq]
  intro m
  obtain ⟨F, hFmem, hFalt⟩ := exists_finset_altSet_of_frequently_right hxd hfa hfb m
  refine ⟨F, ?_, hFalt⟩
  simp only [Set.subset_inter_iff] at hFmem ⊢
  refine ⟨hFmem.1, hFmem.2.trans ?_⟩
  grind

lemma exists_finset_altSet_of_frequently_left
    (hfa : ∃ᶠ s in 𝓝[T ∩ Set.Iio x] x, X s ω < a)
    (hfb : ∃ᶠ s in 𝓝[T ∩ Set.Iio x] x, b < X s ω) (m : ℕ) :
    ∃ F : Finset ι, ↑F ⊆ T ∩ Set.Iio x ∧ ω ∈ altSet X F a b m := by
  -- ascending selection: even picks below `a`, odd picks above `b`
  have hsel k : ∃ c : ℕ → ι, (∀ i, i + 1 < k → c i < c (i + 1))
      ∧ (∀ i < k, c i ∈ T ∩ Set.Iio x)
      ∧ (∀ i < k, if Even i then X (c i) ω < a else b < X (c i) ω) := by
    induction k with
    | zero => exact ⟨fun _ ↦ x, by lia, by lia, by lia⟩
    | succ k ih =>
      obtain ⟨c, hasc, hmem, hval⟩ := ih
      have hU : (if 0 < k then Set.Ioo (c (k - 1)) x else Set.Iio x) ∩ T
          ∈ 𝓝[T ∩ Set.Iio x] x := by
        split_ifs with hk
        · exact Ioo_inter_mem_nhdsWithin_inter_Iio (hmem (k - 1) (by lia)).2
        · rw [Set.inter_comm]
          exact self_mem_nhdsWithin
      have hpick : ∃ s, s ∈ (if 0 < k then Set.Ioo (c (k - 1)) x else Set.Iio x) ∩ T
          ∧ if Even k then X s ω < a else b < X s ω := by
        by_cases hk : Even k
        · simp only [ite_eq_left hk]
          obtain ⟨s, hs1, hs2⟩ := (hfa.and_eventually (Filter.eventually_of_mem hU
            (fun s hs ↦ hs))).exists
          exact ⟨s, hs2, hs1⟩
        · simp only [ite_eq_right hk]
          obtain ⟨s, hs1, hs2⟩ := (hfb.and_eventually (Filter.eventually_of_mem hU
            (fun s hs ↦ hs))).exists
          exact ⟨s, hs2, hs1⟩
      obtain ⟨s, ⟨hsIoo, hsT⟩, hsval⟩ := hpick
      have hsx : s < x := by grind
      refine ⟨Function.update c k s, ?_, by grind⟩
      intro i hi
      rcases Nat.lt_or_ge (i + 1) k with h | h
      · grind
      · have hik : i + 1 = k := by lia
        rw [hik, Function.update_self, Function.update_of_ne (by lia)]
        have hci : c i = c (k - 1) := by congr 1; lia
        grind
  obtain ⟨c, hasc, hmem, hval⟩ := hsel (2 * m)
  exact ⟨(range (2 * m)).image c, by grind, c, hasc, by grind⟩

lemma mem_infiniteAlt_of_frequently_left (hxd : x ≤ d)
    (hfa : ∃ᶠ s in 𝓝[T ∩ Set.Iio x] x, X s ω < a)
    (hfb : ∃ᶠ s in 𝓝[T ∩ Set.Iio x] x, b < X s ω) :
    ω ∈ infiniteAlt T d X a b := by
  simp only [infiniteAlt, Set.mem_iInter, Set.mem_iUnion, Set.mem_ofPred_eq]
  intro m
  obtain ⟨F, hFmem, hFalt⟩ := exists_finset_altSet_of_frequently_left hfa hfb m
  refine ⟨F, ?_, hFalt⟩
  simp only [Set.subset_inter_iff] at hFmem ⊢
  refine ⟨hFmem.1, hFmem.2.trans ?_⟩
  grind

end Selection

/-! ### Maximal inequality along finite time sets -/

section Maximal

variable {t : ι} {F : Finset ι} {lam : ℝ}

-- todo name
lemma sum_indicator_mul_sub_eq_stopped'' (f : ℕ → Ω → ℝ) (s : Set ℝ) (n : ℕ) (ω : Ω) :
    ∑ k ∈ range n, {ω' | ∀ j ≤ k, f j ω' ∉ s}.indicator 1 ω * (f (k + 1) ω - f k ω)
      = f (hittingBtwn f s 0 n ω) ω - f 0 ω := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    by_cases hhit : ∃ j ∈ Set.Icc 0 n, f j ω ∈ s
    · -- already hit by time `n`: the hitting time stabilizes and the last weight vanishes
      have hstab : hittingBtwn f s 0 n ω = hittingBtwn f s 0 (n + 1) ω :=
        hittingBtwn_eq_hittingBtwn_of_exists (Nat.le_succ n) hhit
      obtain ⟨j, hj, hjs⟩ := hhit
      rw [Set.indicator_of_notMem]
      · grind
      · simp only [Set.mem_ofPred_eq, not_forall, not_not]
        exact ⟨j, hj.2, hjs⟩
    · rw [hittingBtwn, ite_eq_right hhit]
      have h2 : hittingBtwn f s 0 (n + 1) ω = n + 1 := by
        refine le_antisymm (hittingBtwn_le ω) (not_lt.1 fun hlt ↦ ?_)
        obtain ⟨j, hj, hjs⟩ := (hittingBtwn_lt_iff (n + 1) le_rfl).1 hlt
        grind
      rw [h2, Set.indicator_of_mem (by simpa using hhit)]
      simp

/-- Discrete stopped telescoping identity: weighting the increments of `f` by the indicator of
"not yet above `lam`" telescopes to the value at the first time `f` exceeds `lam`. -/
lemma sum_indicator_mul_sub_eq_stopped (f : ℕ → Ω → ℝ) (lam : ℝ) (n : ℕ) (ω : Ω) :
    ∑ k ∈ range n, {ω' | ∀ j ≤ k, f j ω' ≤ lam}.indicator 1 ω * (f (k + 1) ω - f k ω)
      = f (hittingBtwn f (Set.Ioi lam) 0 n ω) ω - f 0 ω := by
  convert sum_indicator_mul_sub_eq_stopped'' f (Set.Ioi lam) n ω
  simp

omit [LinearOrder ι] in
/-- Integrability of bounded-weight increment sums. -/
lemma integrable_sum_weight_increments {g : ι → Ω → ℝ} (hgint : ∀ s, Integrable (g s) μ)
    {n : ℕ} {idx : ℕ → ι} {W : ℕ → Ω → ℝ}
    (hWmeas : ∀ k, k < n → AEStronglyMeasurable (W k) μ)
    (hWb : ∀ k, k < n → ∀ ω, ‖W k ω‖ ≤ 1) :
    Integrable (fun ω ↦ ∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω)) μ :=
  integrable_finsetSum _ fun k hk ↦ Integrable.bdd_mul ((hgint _).sub (hgint _))
    (hWmeas k (mem_range.1 hk)) (ae_of_all _ (hWb k (mem_range.1 hk)))

/-- Two-sided expectation bound for adapted `{0,1}`-weighted increment sums of `X`, from the
boundedness of elementary stochastic integrals at time `t`. The lower bound uses the
complementary weights `1 - W`. -/
lemma integral_sum_weight_increments_mem_Icc [OrderBot ι]
    (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C)
    {n : ℕ} {idx : ℕ → ι} (hidx : Monotone idx) (hidxt : ∀ k, idx k ≤ t)
    {W : ℕ → Ω → ℝ} (hW01 : ∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1)
    (hWmeas : ∀ k, k < n → Measurable[𝓕 (idx k)] (W k)) :
    ∫ ω, (∑ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ
        ∈ Set.Icc (-(C + ∫ ω, |X (idx n) ω - X (idx 0) ω| ∂μ)) C := by
  have hb01 : ∀ (V : ℕ → Ω → ℝ), (∀ k, k < n → ∀ ω, V k ω = 0 ∨ V k ω = 1) →
      ∀ k, k < n → ∀ ω, ‖V k ω‖ ≤ 1 := by
    intro V hV k hk ω
    rcases hV k hk ω with h | h <;> simp [h]
  have hupper : ∀ (V : ℕ → Ω → ℝ), (∀ k, k < n → ∀ ω, V k ω = 0 ∨ V k ω = 1) →
      (∀ k, k < n → Measurable[𝓕 (idx k)] (V k)) →
      ∫ ω, (∑ k ∈ range n, V k ω * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ ≤ C := by
    intro V hV01 hVmeas
    let S := elemPredSetOfSeq hidx n hVmeas
    have hS := integral_elemPredSetOfSeq (𝓕 := 𝓕) (X := X) n hidx hidxt (W := V) hV01 hVmeas
    rw [← funext_iff] at hS
    rw [← hS]
    exact hC S
  constructor
  · -- lower bound via the complementary weights
    have hW1 : ∀ k, k < n → ∀ ω, (1 - W k ω) = 0 ∨ (1 - W k ω) = 1 := by grind
    have hW1meas : ∀ k, k < n → Measurable[𝓕 (idx k)] (fun ω ↦ 1 - W k ω) :=
      fun k hk ↦ (measurable_const.sub (hWmeas k hk))
    have hco := hupper (fun k ω ↦ 1 - W k ω) hW1 hW1meas
    have hsplit : ∀ ω, (∑ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω))
        = (X (idx n) ω - X (idx 0) ω)
          - ∑ k ∈ range n, (1 - W k ω) * (X (idx (k + 1)) ω - X (idx k) ω) := by
      intro ω
      have htel : ∑ k ∈ range n, (X (idx (k + 1)) ω - X (idx k) ω)
          = X (idx n) ω - X (idx 0) ω := sum_range_sub (fun k ↦ X (idx k) ω) n
      rw [← htel, ← sum_sub_distrib]
      grind
    have hint1 : Integrable
        (fun ω ↦ ∑ k ∈ range n, (1 - W k ω) * (X (idx (k + 1)) ω - X (idx k) ω)) μ :=
      integrable_sum_weight_increments hXint
        (fun k hk ↦ ((hW1meas k hk).mono (𝓕.le _) le_rfl).aestronglyMeasurable)
        (hb01 _ hW1)
    have hintsub : Integrable (fun ω ↦ X (idx n) ω - X (idx 0) ω) μ :=
      (hXint _).sub (hXint _)
    have hI : ∫ ω, (∑ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ
        = (∫ ω, (X (idx n) ω - X (idx 0) ω) ∂μ)
          - ∫ ω, (∑ k ∈ range n, (1 - W k ω) * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ := by
      rw [integral_congr_ae (μ := μ) (ae_of_all _ hsplit), integral_sub hintsub hint1]
    have hT : -(∫ ω, |X (idx n) ω - X (idx 0) ω| ∂μ)
        ≤ ∫ ω, (X (idx n) ω - X (idx 0) ω) ∂μ := by
      rw [neg_le]
      calc -∫ ω, (X (idx n) ω - X (idx 0) ω) ∂μ
          ≤ |∫ ω, (X (idx n) ω - X (idx 0) ω) ∂μ| := neg_le_abs _
        _ ≤ ∫ ω, |X (idx n) ω - X (idx 0) ω| ∂μ := abs_integral_le_integral_abs
    rw [hI]
    linarith [hco]
  · exact hupper W hW01 hWmeas

/-- One-sided maximal inequality along a finite skeleton for an adapted, integrable process `g`
whose adapted `{0,1}`-weighted increment sums along `idx` have expectation at most `K`. -/
lemma mul_measureReal_exists_lt_le [IsFiniteMeasure μ]
    {g : ι → Ω → ℝ} (hg : StronglyAdapted 𝓕 g) (hgint : ∀ s, Integrable (g s) μ)
    {n : ℕ} {idx : ℕ → ι} (hidx : Monotone idx) {K : ℝ}
    (hK : ∀ W : ℕ → Ω → ℝ, (∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1) →
      (∀ k, k < n → Measurable[𝓕 (idx k)] (W k)) →
      ∫ ω, (∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω)) ∂μ ≤ K) :
    lam * μ.real {ω | ∃ k ≤ n, lam < g (idx k) ω}
      ≤ K + ∫ ω, |g (idx 0) ω| ∂μ + ∫ ω, |g (idx n) ω| ∂μ := by
  set f : ℕ → Ω → ℝ := fun k ω ↦ g (idx k) ω with hf
  set W : ℕ → Ω → ℝ := fun k ↦ {ω' | ∀ j ≤ k, f j ω' ≤ lam}.indicator 1 with hW
  have hW01 : ∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1 := by
    intro k _ ω
    by_cases h : ω ∈ {ω' | ∀ j ≤ k, f j ω' ≤ lam}
    · exact Or.inr (by rw [hW]; simp [Set.indicator_of_mem h])
    · exact Or.inl (by rw [hW]; simp [Set.indicator_of_notMem h])
  have hWmeas : ∀ k, k < n → Measurable[𝓕 (idx k)] (W k) := by
    intro k _
    have hset : MeasurableSet[𝓕 (idx k)] {ω' | ∀ j ≤ k, f j ω' ≤ lam} := by
      have : {ω' | ∀ j ≤ k, f j ω' ≤ lam} = ⋂ j ∈ Iic k, f j ⁻¹' Set.Iic lam := by
        ext ω'
        simp [Set.mem_iInter]
      rw [this]
      refine MeasurableSet.biInter (Iic k).countable_toSet fun j hj ↦ ?_
      have hj' : j ≤ k := mem_Iic.1 hj
      exact (𝓕.mono (hidx hj')) _ ((hg (idx j)).measurable measurableSet_Iic)
    exact (measurable_const.indicator hset)
  have hWb : ∀ k, k < n → ∀ ω, ‖W k ω‖ ≤ 1 := by
    intro k hk ω
    rcases hW01 k hk ω with h | h <;> simp [h]
  -- the stopped value
  set tau : Ω → ℕ := fun ω ↦ hittingBtwn f (Set.Ioi lam) 0 n ω with htau
  set ftau : Ω → ℝ := fun ω ↦ f (tau ω) ω with hftau
  have htel : ∀ ω, ftau ω = f 0 ω
      + ∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω) := by
    intro ω
    rw [hftau, htau]
    have hterm k : W k ω * (g (idx (k + 1)) ω - g (idx k) ω)
        = ({ω' | ∀ j ≤ k, f j ω' ≤ lam}.indicator 1 ω : ℝ) * (f (k + 1) ω - f k ω) := rfl
    simp_rw [hterm]
    rw [sum_indicator_mul_sub_eq_stopped f lam n ω]
    ring
  have hint_sum : Integrable
      (fun ω ↦ ∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω)) μ :=
    integrable_sum_weight_increments hgint
      (fun k hk ↦ ((hWmeas k hk).mono (𝓕.le _) le_rfl).aestronglyMeasurable) hWb
  have hint_ftau : Integrable ftau μ := by
    have : ftau = fun ω ↦ f 0 ω
        + ∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω) := funext htel
    rw [this]
    exact (hgint _).add hint_sum
  -- the event
  set H : Set Ω := {ω | ∃ k ≤ n, lam < g (idx k) ω} with hH
  have hHmeas : MeasurableSet H := by
    have : H = ⋃ k ∈ Iic n, (g (idx k)) ⁻¹' Set.Ioi lam := by ext; simp [hH]
    rw [this]
    exact MeasurableSet.biUnion (Iic n).countable_toSet fun k _ ↦
      (𝓕.le _) _ ((hg (idx k)).measurable measurableSet_Ioi)
  -- on `H`, the stopped value exceeds `lam`
  have hHval : ∀ ω ∈ H, lam < ftau ω := by
    intro ω hω
    obtain ⟨k, hk, hkval⟩ := hω
    have hexists : ∃ j ∈ Set.Icc 0 n, f j ω ∈ Set.Ioi lam := ⟨k, ⟨Nat.zero_le k, hk⟩, hkval⟩
    exact hittingBtwn_mem_set hexists
  -- off `H`, the stopped value is the terminal value
  have hHcval : ∀ ω ∉ H, ftau ω = f n ω := by
    intro ω hω
    have hno : ∀ j, j ≤ n → f j ω ≤ lam := by
      intro j hj
      by_contra hlt
      exact hω ⟨j, hj, not_le.1 hlt⟩
    have h1 : tau ω = n := by
      refine le_antisymm (hittingBtwn_le ω) (not_lt.1 fun hlt ↦ ?_)
      obtain ⟨j, hj, hjs⟩ := (hittingBtwn_lt_iff n le_rfl).1 hlt
      exact absurd hjs (not_lt.2 (hno j hj.2.le))
    change f (tau ω) ω = f n ω
    rw [h1]
  -- assemble
  have hsplit : ∫ ω, ftau ω ∂μ = (∫ ω in H, ftau ω ∂μ) + ∫ ω in Hᶜ, ftau ω ∂μ :=
    (integral_add_compl hHmeas hint_ftau).symm
  have hlower : lam * μ.real H ≤ ∫ ω in H, ftau ω ∂μ := by
    calc lam * μ.real H = ∫ _ in H, lam ∂μ := by rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ ω in H, ftau ω ∂μ := by
          refine setIntegral_mono_on (integrable_const lam).integrableOn
            hint_ftau.integrableOn hHmeas fun ω hω ↦ (hHval ω hω).le
  have hcompl : -(∫ ω, |g (idx n) ω| ∂μ) ≤ ∫ ω in Hᶜ, ftau ω ∂μ := by
    have heq : ∫ ω in Hᶜ, ftau ω ∂μ = ∫ ω in Hᶜ, f n ω ∂μ :=
      setIntegral_congr_fun hHmeas.compl fun ω hω ↦ hHcval ω hω
    rw [heq, neg_le]
    calc -∫ ω in Hᶜ, f n ω ∂μ ≤ |∫ ω in Hᶜ, f n ω ∂μ| := neg_le_abs _
      _ ≤ ∫ ω in Hᶜ, |f n ω| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ ω, |g (idx n) ω| ∂μ :=
          setIntegral_le_integral (hgint _).abs (ae_of_all _ fun ω ↦ abs_nonneg _)
  have htotal : ∫ ω, ftau ω ∂μ ≤ K + ∫ ω, |g (idx 0) ω| ∂μ := by
    have : ∫ ω, ftau ω ∂μ = (∫ ω, f 0 ω ∂μ)
        + ∫ ω, (∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω)) ∂μ := by
      rw [← integral_add (hgint _) hint_sum]
      exact integral_congr_ae (ae_of_all _ htel)
    rw [this]
    have h0 : ∫ ω, f 0 ω ∂μ ≤ ∫ ω, |g (idx 0) ω| ∂μ :=
      integral_mono (hgint _) (hgint _).abs fun ω ↦ le_abs_self _
    have hsum := hK W hW01 hWmeas
    linarith
  linarith [hsplit, hlower, hcompl, htotal]

/-- **Maximal inequality**: the probability that `|X|` exceeds `lam` somewhere on a finite set
`F ⊆ Iic t` is at most `K / lam`, with `K` independent of `F`. -/
theorem measureReal_exists_abs_lt_le [OrderBot ι] [IsFiniteMeasure μ]
    (hX : StronglyAdapted 𝓕 X) (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C)
    (hlam : 0 < lam) (hF : ∀ s ∈ F, s ≤ t) :
    μ.real {ω | ∃ s ∈ F, lam < |X s ω|}
      ≤ 2 * (C + ∫ ω, |X t ω - X ⊥ ω| ∂μ + ∫ ω, |X ⊥ ω| ∂μ + ∫ ω, |X t ω| ∂μ) / lam := by
  set G : Finset ι := insert ⊥ F with hG
  have hGF : F ⊆ G := subset_insert _ _
  have hGle : ∀ s ∈ G, s ≤ t := by simp [G]; grind
  set n : ℕ := G.card with hn
  set idx : ℕ → ι := finIdx G t with hidx
  have hmono : Monotone idx := finIdx_monotone hGle
  have hidx0 : idx 0 = ⊥ := finIdx_zero_eq_bot (mem_insert_self _ _)
  have hidxn : idx n = t := finIdx_eq_of_card_le hn.ge
  -- two-sided expectation bound for adapted 0/1 weights along `idx`
  have hbdd : ∀ W : ℕ → Ω → ℝ, (∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1) →
      (∀ k, k < n → Measurable[𝓕 (idx k)] (W k)) →
      ∫ ω, (∑ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ
        ∈ Set.Icc (-(C + ∫ ω, |X (idx n) ω - X (idx 0) ω| ∂μ)) C :=
    fun W hW01 hWmeas ↦ integral_sum_weight_increments_mem_Icc (t := t) hXint hC hmono
      (finIdx_le hGle) hW01 hWmeas
  -- apply the one-sided maximal inequality to `X`
  have hpos := mul_measureReal_exists_lt_le (lam := lam) hX hXint (n := n) hmono (K := C)
    (fun W hW01 hWmeas ↦ (hbdd W hW01 hWmeas).2)
  -- and to `-X`
  have hnegX : StronglyAdapted 𝓕 (fun s ω ↦ -X s ω) := fun s ↦ (hX s).neg
  have hnegint : ∀ s, Integrable ((fun s ω ↦ -X s ω) s) μ := fun s ↦ (hXint s).neg
  have hneg := mul_measureReal_exists_lt_le (lam := lam) hnegX hnegint (n := n) hmono
    (K := C + ∫ ω, |X (idx n) ω - X (idx 0) ω| ∂μ)
    (fun W hW01 hWmeas ↦ by
      have h1 := (hbdd W hW01 hWmeas).1
      have h2 : ∫ ω, (∑ k ∈ range n, W k ω * (-X (idx (k + 1)) ω - -X (idx k) ω)) ∂μ
          = -∫ ω, (∑ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ := by
        rw [← integral_neg]
        congr 1 with ω
        rw [← sum_neg_distrib]
        grind
      rw [h2]
      linarith)
  -- combine the two events
  have hsub : {ω | ∃ s ∈ F, lam < |X s ω|}
      ⊆ {ω | ∃ k ≤ n, lam < X (idx k) ω} ∪ {ω | ∃ k ≤ n, lam < -X (idx k) ω} := by
    rintro ω ⟨s, hs, habs⟩
    obtain ⟨k, hk, hkeq⟩ := exists_finIdx_eq (t := t) (hGF hs)
    grind
  have habs u : ∫ ω, |(fun s ω ↦ -X s ω) u ω| ∂μ = ∫ ω, |X u ω| ∂μ := by simp
  rw [hidx0, hidxn] at hpos hneg
  rw [habs ⊥, habs t] at hneg
  have hunion : μ.real {ω | ∃ s ∈ F, lam < |X s ω|}
      ≤ μ.real {ω | ∃ k ≤ n, lam < X (idx k) ω} + μ.real {ω | ∃ k ≤ n, lam < -X (idx k) ω} :=
    (measureReal_mono hsub).trans (measureReal_union_le _ _)
  have hI : (0 : ℝ) ≤ ∫ ω, |X t ω - X ⊥ ω| ∂μ := integral_nonneg fun ω ↦ abs_nonneg _
  rw [le_div_iff₀ hlam]
  have hmul : lam * μ.real {ω | ∃ s ∈ F, lam < |X s ω|}
      ≤ lam * (μ.real {ω | ∃ k ≤ n, lam < X (idx k) ω}
        + μ.real {ω | ∃ k ≤ n, lam < -X (idx k) ω}) :=
    mul_le_mul_of_nonneg_left hunion hlam.le
  rw [mul_add] at hmul
  nlinarith [hpos, hneg, hmul]

end Maximal

/-! ## Maximal inequality for countable sets -/

section CountableEvents

variable {T : Set ι} {t : ι} {a b lam : ℝ} {m : ℕ}

omit [LinearOrder ι] in
lemma countable_setOf_finset_coe_subset (hT : T.Countable) :
    {F : Finset ι | ↑F ⊆ T}.Countable := by
  have h1 : {F : Finset ι | ↑F ⊆ T}
      ⊆ (fun F : Finset ι ↦ (F : Set ι)) ⁻¹' {u : Set ι | u.Finite ∧ u ⊆ T} :=
    fun F hF ↦ ⟨F.finite_toSet, hF⟩
  exact ((Set.countable_ofPred_finite_subset hT).preimage coe_injective).mono h1

variable [OrderBot ι]

/-- The union of the alternation events over all finite subsets of a countable set of times
below `t` has measure at most `K / ((b - a) * m)`. -/
lemma measure_biUnion_altSet_le [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ)
    (hab : a < b) (hm : 0 < m) (hT : T.Countable) (t : ι) :
    μ (⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}, altSet X F a b m)
      ≤ ENNReal.ofReal ((variationBound X 𝓕 μ t + ∫ ω, (a - X t ω)⁺ ∂μ) / (b - a) / m) := by
  have hcnt : {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}.Countable :=
    countable_setOf_finset_coe_subset (hT.mono Set.inter_subset_left)
  have hdir : DirectedOn (Function.onFun (· ⊆ ·) fun F : Finset ι ↦ altSet X F a b m)
      {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t} :=
    fun F₁ h₁ F₂ h₂ ↦ ⟨F₁ ∪ F₂, by grind, altSet_mono subset_union_left,
      altSet_mono subset_union_right⟩
  rw [measure_biUnion_eq_iSup hcnt hdir]
  refine iSup₂_le fun F hF ↦ ?_
  have hF' : ∀ s ∈ F, s ≤ t := fun s hs ↦ (hF hs).2
  calc μ (altSet X F a b m)
  _ = ENNReal.ofReal (μ.real (altSet X F a b m)) :=
    (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
  _ ≤ _ := ENNReal.ofReal_le_ofReal (measureReal_altSet_le (μ := μ) hX.adapted hX.integrable
        (hX.integral_indicator_le_variationBound t) hab hm hF')

/-- Almost surely, there is no infinite family of alternations of `X` from below `a` to above `b`
at times in a countable set `T` below `t`. -/
lemma measure_infiniteAlt [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ) (hab : a < b) (hT : T.Countable) :
    μ (infiniteAlt T t X a b) = 0 := by
  suffices μ (⋂ m : ℕ, ⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}, altSet X F a b (m + 1)) = 0 by
    refine measure_mono_null ?_ this
    intro ω
    simp only [infiniteAlt, Set.subset_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion,
      exists_prop]
    exact fun h i ↦ h (i + 1)
  refine le_antisymm ?_ zero_le
  have hbound : ∀ m : ℕ,
      μ (⋂ m : ℕ, ⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}, altSet X F a b (m + 1))
        ≤ ENNReal.ofReal ((variationBound X 𝓕 μ t + ∫ ω, (a - X t ω)⁺ ∂μ) / (b - a) / (m + 1)) := by
    intro m
    refine (measure_mono (Set.iInter_subset _ m)).trans ?_
    have := measure_biUnion_altSet_le (μ := μ) hX hab (Nat.succ_pos m) hT t
    simpa using this
  have hlim : Tendsto (fun m : ℕ ↦
      ENNReal.ofReal ((variationBound X 𝓕 μ t + ∫ ω, (a - X t ω)⁺ ∂μ) / (b - a) / (m + 1)))
        atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine (ENNReal.continuous_ofReal.tendsto 0).comp ?_
    have h1 : Tendsto (fun n : ℕ ↦ ((variationBound X 𝓕 μ t + ∫ ω, (a - X t ω)⁺ ∂μ) / (b - a)) / n)
        atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
    have h2 := h1.comp (tendsto_add_atTop_nat 1)
    refine h2.congr fun m ↦ ?_
    simp [Function.comp, div_div]
  exact ge_of_tendsto' hlim hbound

lemma measure_all_infiniteAlt'' [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ) (T : Set ι) (hT : T.Countable) :
    ∀ᵐ ω ∂μ, ∀ q r, q < r → ω ∉ infiniteAlt T t X q r := by
  suffices ∀ᵐ ω ∂μ, ∀ (q r : ℚ), q < r → ω ∉ infiniteAlt T t X q r by
    filter_upwards [this] with ω hω q r hqr
    obtain ⟨q', r', hqq', hq'r', hr'r⟩ : ∃ q' r' : ℚ, q < q' ∧ q' < r' ∧ r' < r := by
      obtain ⟨r', hqr', hr'r⟩ := exists_rat_btwn hqr
      obtain ⟨q', hqq', hq'r'⟩ := exists_rat_btwn hqr'
      exact ⟨q', r', hqq', mod_cast hq'r', hr'r⟩
    exact fun h_mem ↦ hω q' r' hq'r' (infiniteAlt_mono' hqq'.le hr'r.le h_mem)
  simp_rw [ae_all_iff]
  intro q r hqr
  exact compl_mem_ae_iff.2 (measure_infiniteAlt hX (mod_cast hqr) hT)

lemma measure_all_infiniteAlt [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ)
    {T T' : Set ι} (hT : T.Countable) (hT' : T'.Countable) :
    ∀ᵐ ω ∂μ, ∀ d ∈ T', ∀ q r, q < r → ω ∉ infiniteAlt T d X q r := by
  rw [ae_ball_iff hT']
  exact fun t _ ↦ measure_all_infiniteAlt'' hX T hT

lemma measure_all_infiniteAlt' [IsFiniteMeasure μ] [(atTop : Filter ι).IsCountablyGenerated]
    (hX : IsRealQuasimartingale 𝓕 X μ)
    (T : Set ι) (hT : T.Countable) :
    ∀ᵐ ω ∂μ, ∀ d, ∀ q r, q < r → ω ∉ infiniteAlt T d X q r := by
  obtain ⟨u, hu⟩ := exists_seq_monotone_tendsto_atTop_atTop ι
  suffices ∀ᵐ ω ∂μ, ∀ n, ∀ q r, q < r → ω ∉ infiniteAlt T (u n) X q r by
    filter_upwards [this] with ω hω d q r hqr
    obtain ⟨n, hn⟩ : ∃ n, d ≤ u n := (hu.2.eventually_ge_atTop d).exists
    specialize hω n q r hqr
    exact fun h_mem ↦ hω (infiniteAlt_mono'' hn h_mem)
  rw [ae_all_iff]
  exact fun n ↦ measure_all_infiniteAlt'' hX T hT

lemma measure_exists_abs_gt_le [IsFiniteMeasure μ] {ε : ℝ}
    (hX : IsRealQuasimartingale 𝓕 X μ) (hε : 0 < ε) (hT : T.Countable) :
    μ {ω | ∃ s ∈ T ∩ Set.Iic t, ε < |X s ω|}
      ≤ ENNReal.ofReal (2 * (variationBound X 𝓕 μ t + ∫ ω, |X t ω - X ⊥ ω| ∂μ + ∫ ω, |X ⊥ ω| ∂μ
          + ∫ ω, |X t ω| ∂μ) / ε) := by
  have : {ω | ∃ s ∈ T ∩ Set.Iic t, ε < |X s ω|} =
      ⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}, {ω | ∃ s ∈ F, ε < |X s ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.subset_inter_iff, Set.mem_iUnion, exists_prop]
    refine ⟨fun ⟨s, hsT, hs⟩ ↦ ?_, fun ⟨F, hF, ⟨s, hsT, hs⟩⟩ ↦ ?_⟩
    · exact ⟨{s}, by grind, by grind⟩
    · exact ⟨s, by grind, by grind⟩
  rw [this]
  have hcnt : {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}.Countable :=
    countable_setOf_finset_coe_subset (hT.mono Set.inter_subset_left)
  have hdir : DirectedOn (Function.onFun (· ⊆ ·) fun F : Finset ι ↦ {ω | ∃ s ∈ F, ε < |X s ω|})
      {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t} :=
    fun F₁ h₁ F₂ h₂ ↦ ⟨F₁ ∪ F₂, by grind, by grind, by grind⟩
  rw [measure_biUnion_eq_iSup hcnt hdir]
  refine iSup₂_le fun F hF ↦ ?_
  have hF' : ∀ s ∈ F, s ≤ t := fun s hs ↦ (hF hs).2
  calc μ {ω | ∃ s ∈ F, ε < |X s ω|}
      = ENNReal.ofReal (μ.real {ω | ∃ s ∈ F, ε < |X s ω|}) :=
        (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal
        (measureReal_exists_abs_lt_le (μ := μ) hX.stronglyAdapted hX.integrable
          (hX.integral_indicator_le_variationBound t) hε hF')

lemma ae_exists_bound'' [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    (hT : T.Countable) (t : ι) :
    ∀ᵐ ω ∂μ, ∃ M : ℕ, ∀ s' ∈ T ∩ Set.Iic t, |X s' ω| ≤ M + 1 := by
  rw [ae_iff]
  push Not
  have : {a | ∀ (M : ℕ), ∃ s' ∈ T ∩ Set.Iic t, ↑M + 1 < |X s' a|}
      = ⋂ M : ℕ, {a | ∃ s' ∈ T ∩ Set.Iic t, (M + 1 : ℝ) < |X s' a|} := by ext; simp
  rw [this]
  refine le_antisymm ?_ zero_le
  have hbound (M : ℕ) :
      μ (⋂ M : ℕ, {ω | ∃ s ∈ T ∩ Set.Iic t, (M + 1 : ℝ) < |X s ω|})
        ≤ ENNReal.ofReal (2 * (variationBound X 𝓕 μ t + ∫ ω, |X t ω - X ⊥ ω| ∂μ + ∫ ω, |X ⊥ ω| ∂μ
            + ∫ ω, |X t ω| ∂μ) / (M + 1)) := by
    refine (measure_mono (Set.iInter_subset _ M)).trans ?_
    exact measure_exists_abs_gt_le hX (by positivity) hT
  have hlim : Tendsto (fun M : ℕ ↦
      ENNReal.ofReal (2 * (variationBound X 𝓕 μ t + ∫ ω, |X t ω - X ⊥ ω| ∂μ + ∫ ω, |X ⊥ ω| ∂μ
        + ∫ ω, |X t ω| ∂μ) / (M + 1))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine (ENNReal.continuous_ofReal.tendsto 0).comp ?_
    have h1 : Tendsto (fun n : ℕ ↦ (2 * (variationBound X 𝓕 μ t +
        ∫ ω, |X t ω - X ⊥ ω| ∂μ + ∫ ω, |X ⊥ ω| ∂μ + ∫ ω, |X t ω| ∂μ)) / n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have h2 := h1.comp (tendsto_add_atTop_nat 1)
    refine h2.congr fun M ↦ ?_
    simp
  exact ge_of_tendsto' hlim hbound

lemma ae_exists_bound [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    (hT : T.Countable) {T' : Set ι} (hT' : T'.Countable) :
    ∀ᵐ ω ∂μ, ∀ d ∈ T', ∃ M : ℕ, ∀ s' ∈ T ∩ Set.Iic d, |X s' ω| ≤ M + 1 := by
  rw [ae_ball_iff hT']
  intro d hdT
  exact ae_exists_bound'' hX hT d

lemma ae_exists_bound' [IsFiniteMeasure μ] [(atTop : Filter ι).IsCountablyGenerated]
    (hX : IsRealQuasimartingale 𝓕 X μ) (hT : T.Countable) :
    ∀ᵐ ω ∂μ, ∀ d, ∃ M : ℕ, ∀ s ∈ T ∩ Set.Iic d, |X s ω| ≤ M + 1 := by
  obtain ⟨u, hu⟩ := exists_seq_monotone_tendsto_atTop_atTop ι
  suffices ∀ᵐ ω ∂μ, ∀ n, ∃ M : ℕ, ∀ s ∈ T ∩ Set.Iic (u n), |X s ω| ≤ M + 1 by
    filter_upwards [this] with ω hω d
    obtain ⟨n, hn⟩ : ∃ n, d ≤ u n := (hu.2.eventually_ge_atTop d).exists
    obtain ⟨M, hM⟩ := hω n
    exact ⟨M, fun s hsT ↦ hM s (by grind)⟩
  rw [ae_all_iff]
  exact fun n ↦ ae_exists_bound'' hX hT (u n)

end CountableEvents

end ProbabilityTheory
