/-
Copyright (c) 2026 FormalizingGMT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalizingGMT contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Tactic

/- Necessary basic definitions -/
public import LeanPool.FormalizingGMT.RadonMeasures.Basic
public import LeanPool.FormalizingGMT.Densities.Basic
public import LeanPool.FormalizingGMT.RadonMeasures.HausdorffMeasure
public import LeanPool.FormalizingGMT.Covering.VariantVitali

/-!
# Technical lemmas for density bounds inside a set

This file contains the definitions and technical lemmas used in the proofs of the main results
of `FormalizingGMT/Densities/HausdorffUpperDensityInside.lean`:

* **Part I** (lower density bound, used by `hausdorffContentInfty_upperDensity_ge_ae_mem` and
  `hausdorffMeasure_upperDensity_ge_ae_mem`): the Hausdorff contents packaged as outer measures
  (`hausdorffContentOuter`, `hausdorffContentInftyOuter`), the sets `coverSet s E δ τ`, the
  vanishing of `H^s` on them, and the passage from a small upper density to membership in some
  `coverSet`.
* **Part II** (upper density bound, used by
  `hausdorffMeasure_upperDensity_le_one_ae_mem`, all in the namespace `HausdorffDensity`):
  the super-level sets `superlevelSet s E t`, the ball family
  `ballFamily`, the outer approximation coming from the Radon property, the covering estimate at
  each scale (`exists_cover_le`) and the nullity of the super-level sets (`superlevelSet_null`).

All balls occurring here are *closed* metric balls.
-/

@[expose] public section

/-! # Part I: the lower density bound -/

open scoped BigOperators Real Nat Pointwise ENNReal
open MeasureTheory MeasureTheory.OuterMeasure Set Filter Topology

noncomputable section

/-- If `a ≤ c * a` with `c < 1` and `a ≠ ∞`, then `a = 0`.  (Used in both Part I and Part II.) -/
lemma eq_zero_of_le_mul_self {a c : ℝ≥0∞} (hc : c < 1) (ha : a ≠ ⊤) (h : a ≤ c * a) : a = 0 := by
  by_contra h0
  have h1 : a * c < a * 1 := ENNReal.mul_lt_mul_right h0 ha hc
  rw [mul_one, mul_comm] at h1
  exact absurd (h.trans_lt h1) (lt_irrefl a)

/-! ## The Hausdorff contents as outer measures

Both Hausdorff contents defined in `HausdorffMeasure.lean` are outer measures; we record this by
identifying them with `MeasureTheory.OuterMeasure.mkMetric'.pre` and
`MeasureTheory.OuterMeasure.boundedBy` respectively.  This gives us monotonicity and countable
subadditivity for free. -/

section Contents

variable {X : Type*} [EMetricSpace X]

/-- The `δ`-restricted Hausdorff content, packaged as an outer measure. -/
noncomputable def hausdorffContentOuter (s : ℝ) (δ : ℝ≥0∞) : OuterMeasure X :=
  OuterMeasure.mkMetric'.pre (fun t => (Metric.ediam t) ^ s) δ

/-- The unrestricted Hausdorff content `H^s_∞`, packaged as an outer measure. -/
noncomputable def hausdorffContentInftyOuter (s : ℝ) : OuterMeasure X :=
  OuterMeasure.boundedBy (fun t => (Metric.ediam t) ^ s)

/-- `hausdorffContentOuter` computes the `δ`-restricted Hausdorff content. -/
lemma hausdorffContentOuter_apply (s : ℝ) (δ : ℝ≥0∞) (E : Set X) :
    hausdorffContentOuter s δ E = hausdorffContent s δ E := by
  rw [hausdorffContentOuter, mkMetric'.pre, boundedBy_apply, hausdorffContent]
  refine le_antisymm ?_ ?_
  · refine le_iInf fun t => le_iInf fun hcov => le_iInf fun hd => ?_
    refine le_trans (iInf₂_le t hcov) (le_of_eq ?_)
    refine tsum_congr fun n => ?_
    rw [MeasureTheory.extend_eq (fun (u : Set X) (_ : Metric.ediam u ≤ δ) => (Metric.ediam u) ^ s)
      (hd n)]
  · refine le_iInf fun t => le_iInf fun hcov => ?_
    by_cases hd : ∀ i, Metric.ediam (t i) ≤ δ
    · refine le_trans (iInf₂_le t hcov) ?_
      refine le_trans (iInf_le _ hd) (le_of_eq ?_)
      refine tsum_congr fun n => ?_
      rw [MeasureTheory.extend_eq (fun (u : Set X) (_ : Metric.ediam u ≤ δ) => (Metric.ediam u) ^ s)
        (hd n)]
    · push Not at hd
      obtain ⟨i, hi⟩ := hd
      have hi' : ¬ (Metric.ediam (t i) ≤ δ) := not_le.mpr hi
      have hne : (t i).Nonempty := by
        rcases Set.eq_empty_or_nonempty (t i) with h | h
        · exact absurd (h ▸ (by simp : Metric.ediam (∅ : Set X) ≤ δ)) hi'
        · exact h
      have hterm : (⨆ (_ : (t i).Nonempty), MeasureTheory.extend
          (fun (u : Set X) (_ : Metric.ediam u ≤ δ) => (Metric.ediam u) ^ s) (t i)) = ⊤ := by
        rw [iSup_pos hne, MeasureTheory.extend_eq_top
          (fun (u : Set X) (_ : Metric.ediam u ≤ δ) => (Metric.ediam u) ^ s) hi']
      have hle := ENNReal.le_tsum (f := fun n => ⨆ (_ : (t n).Nonempty), MeasureTheory.extend
          (fun (u : Set X) (_ : Metric.ediam u ≤ δ) => (Metric.ediam u) ^ s) (t n)) i
      rw [hterm, top_le_iff] at hle
      rw [hle]
      exact le_top

/-- `hausdorffContentInftyOuter` computes the unrestricted Hausdorff content. -/
lemma hausdorffContentInftyOuter_apply (s : ℝ) (E : Set X) :
    hausdorffContentInftyOuter s E = hausdorffContentInfty s E := by
  rw [hausdorffContentInftyOuter, boundedBy_apply, hausdorffContentInfty]

/-- Monotonicity of the `δ`-restricted Hausdorff content. -/
lemma hausdorffContent_mono {s : ℝ} {δ : ℝ≥0∞} {A B : Set X} (h : A ⊆ B) :
    hausdorffContent s δ A ≤ hausdorffContent s δ B := by
  rw [← hausdorffContentOuter_apply, ← hausdorffContentOuter_apply]
  exact measure_mono h

/-- Monotonicity of the unrestricted Hausdorff content. -/
lemma hausdorffContentInfty_mono {s : ℝ} {A B : Set X} (h : A ⊆ B) :
    hausdorffContentInfty s A ≤ hausdorffContentInfty s B := by
  rw [← hausdorffContentInftyOuter_apply, ← hausdorffContentInftyOuter_apply]
  exact measure_mono h

/-- Countable subadditivity of the `δ`-restricted Hausdorff content. -/
lemma hausdorffContent_iUnion_le {s : ℝ} {δ : ℝ≥0∞} (A : ℕ → Set X) :
    hausdorffContent s δ (⋃ i, A i) ≤ ∑' i, hausdorffContent s δ (A i) := by
  simp only [← hausdorffContentOuter_apply]
  exact measure_iUnion_le A

/-- The `δ`-restricted Hausdorff content of the empty set vanishes. -/
lemma hausdorffContent_empty (s : ℝ) (δ : ℝ≥0∞) :
    hausdorffContent s δ (∅ : Set X) = 0 := by
  rw [hausdorffContent]
  refine le_antisymm ?_ (zero_le)
  refine le_trans (iInf₂_le (fun _ => (∅ : Set X)) (by simp)) ?_
  exact le_trans (iInf_le _ (by simp)) (by simp)

/-- The `δ`-restricted Hausdorff content is antitone in `δ`. -/
lemma hausdorffContent_antitone {s : ℝ} {δ δ' : ℝ≥0∞} (h : δ ≤ δ') (A : Set X) :
    hausdorffContent s δ' A ≤ hausdorffContent s δ A := by
  rw [hausdorffContent, hausdorffContent]
  refine le_iInf fun t => le_iInf fun hcov => le_iInf fun hd => ?_
  exact le_trans (iInf₂_le t hcov) (iInf_le _ (fun i => (hd i).trans h))

/-- For a positive exponent, a set of vanishing diameter has vanishing Hausdorff content. -/
lemma hausdorffContentInfty_eq_zero_of_ediam_eq_zero {s : ℝ} (hs : 0 < s) {A : Set X}
    (hA : Metric.ediam A = 0) : hausdorffContentInfty s A = 0 := by
  refine le_antisymm ?_ (zero_le)
  rw [hausdorffContentInfty]
  refine le_trans (iInf₂_le (fun _ => A) (Set.subset_iUnion (fun _ : ℕ => A) 0)) ?_
  simp [hA, ENNReal.zero_rpow_of_pos hs]

end Contents

/-! ## The sets `E(δ, τ)` -/

section CoverSet

variable {X : Type*} [EMetricSpace X]

/-- `coverSet s E δ τ` is the set `E(δ, τ)` of Evans–Gariepy: the set of points `x ∈ E` such that
`H^s_δ(C ∩ E) ≤ τ (diam C)^s` whenever `C ⊆ X` contains `x` and has `diam C ≤ δ`. -/
def coverSet (s : ℝ) (E : Set X) (δ τ : ℝ≥0∞) : Set X :=
  {x | x ∈ E ∧ ∀ C : Set X, x ∈ C → Metric.ediam C ≤ δ →
    hausdorffContent s δ (C ∩ E) ≤ τ * (Metric.ediam C) ^ s}

lemma cover_set_subset (s : ℝ) (E : Set X) (δ τ : ℝ≥0∞) : coverSet s E δ τ ⊆ E :=
  fun _ hx => hx.1

/-- `E(δ, τ)` is monotone in `τ`. -/
lemma cover_set_mono_tau (s : ℝ) (E : Set X) (δ : ℝ≥0∞) {τ τ' : ℝ≥0∞} (h : τ ≤ τ') :
    coverSet s E δ τ ⊆ coverSet s E δ τ' :=
  fun _ hx => ⟨hx.1, fun C hC hCd => (hx.2 C hC hCd).trans (by gcongr)⟩

/-- Equation (0.5): if `0 < δ ≤ δ'` then `E(δ', 1 - δ') ⊆ E(δ, 1 - δ)`.

Note that the two sets are defined through *different* Hausdorff contents, `H^s_δ` and `H^s_{δ'}`.
They agree on the relevant sets `C ∩ E`, whose diameter is at most `δ ≤ δ'`, by the stabilisation
lemma `hausdorffContent_eq_hausdorffContentInfty_of_ediam_le`. -/
lemma cover_set_mono_delta {s : ℝ} (hs : 0 ≤ s) (E : Set X) {δ δ' : ℝ≥0∞}
    (hδ : 0 < δ) (hδδ' : δ ≤ δ') :
    coverSet s E δ' (1 - δ') ⊆ coverSet s E δ (1 - δ) := by
  rintro x ⟨hxE, hx⟩
  refine ⟨hxE, fun C hxC hCd => ?_⟩
  have hCE : Metric.ediam (C ∩ E) ≤ δ := le_trans (Metric.ediam_mono Set.inter_subset_left) hCd
  have h1 : hausdorffContent s δ (C ∩ E) = hausdorffContentInfty s (C ∩ E) :=
    hausdorffContent_eq_hausdorffContentInfty_of_ediam_le hs hδ hCE
  have h2 : hausdorffContent s δ' (C ∩ E) = hausdorffContentInfty s (C ∩ E) :=
    hausdorffContent_eq_hausdorffContentInfty_of_ediam_le hs (lt_of_lt_of_le hδ hδδ')
      (hCE.trans hδδ')
  rw [h1, ← h2]
  refine (hx C hxC (hCd.trans hδδ')).trans ?_
  gcongr

/-- **Lemma 0.1 (covering estimate for `E(δ, τ)`).** General form: no nonemptiness assumption on
the pieces of the cover is needed. -/
lemma hausdorffContent_cover_set_le_tsum {s : ℝ} (E : Set X) {δ τ : ℝ≥0∞}
    (C : ℕ → Set X) (h_cover : coverSet s E δ τ ⊆ ⋃ i, C i)
    (h_diam : ∀ i, Metric.ediam (C i) ≤ δ) :
    hausdorffContent s δ (coverSet s E δ τ) ≤ τ * ∑' i, (Metric.ediam (C i)) ^ s := by
  set A := coverSet s E δ τ
  have h1 : A ⊆ ⋃ i, (C i ∩ A) := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (h_cover hx)
    exact Set.mem_iUnion.mpr ⟨i, hi, hx⟩
  have hterm : ∀ i, hausdorffContent s δ (C i ∩ A) ≤ τ * (Metric.ediam (C i)) ^ s := by
    intro i
    rcases Set.eq_empty_or_nonempty (C i ∩ A) with h | ⟨x, hxC, hxA⟩
    · rw [h, hausdorffContent_empty]
      exact zero_le
    · exact le_trans (hausdorffContent_mono
        (Set.inter_subset_inter_right _ (cover_set_subset s E δ τ))) (hxA.2 (C i) hxC (h_diam i))
  calc hausdorffContent s δ A ≤ hausdorffContent s δ (⋃ i, C i ∩ A) := hausdorffContent_mono h1
    _ ≤ ∑' i, hausdorffContent s δ (C i ∩ A) := hausdorffContent_iUnion_le _
    _ ≤ ∑' i, τ * (Metric.ediam (C i)) ^ s := ENNReal.tsum_le_tsum hterm
    _ = τ * ∑' i, (Metric.ediam (C i)) ^ s := ENNReal.tsum_mul_left

/-- **Lemma 0.2 (contraction).** `H^s_δ(E(δ,τ)) ≤ τ · H^s_δ(E(δ,τ))`. -/
lemma hausdorffContent_cover_set_contraction {s : ℝ} (hs : 0 < s) (E : Set X) {δ τ : ℝ≥0∞}
    (hτ : τ ≠ 0) (hτ' : τ ≠ ⊤) :
    hausdorffContent s δ (coverSet s E δ τ)
      ≤ τ * hausdorffContent s δ (coverSet s E δ τ) := by
  rw [mul_comm, ← ENNReal.div_le_iff_le_mul (Or.inl hτ) (Or.inl hτ'), hausdorffContent]
  refine le_iInf fun t => le_iInf fun hcov => le_iInf fun hd => ?_
  rw [ENNReal.div_le_iff_le_mul (Or.inl hτ) (Or.inl hτ'), mul_comm]
  refine (hausdorffContent_cover_set_le_tsum E t hcov hd).trans (le_of_eq ?_)
  congr 1
  exact tsum_congr fun i => (hausdorffContent_summand_eq hs _).symm

end CoverSet

/-! ## Vanishing of `H^s(E(δ, τ))` -/

section Vanishing

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Lemma 0.3 (vanishing `H^s_δ`).** If `H^s(E) < ∞` then `H^s_δ(E(δ,τ)) = 0`. -/
lemma hausdorffContent_cover_set_eq_zero {s : ℝ} (hs : 0 < s) (E : Set X) {δ τ : ℝ≥0∞}
    (hδ : 0 < δ) (hτ : τ ≠ 0) (hτ1 : τ < 1) (hE : μH[s] E ≠ ⊤) :
    hausdorffContent s δ (coverSet s E δ τ) = 0 :=
  eq_zero_of_le_mul_self hτ1
    (ne_top_of_le_ne_top hE ((hausdorffContent_mono (cover_set_subset s E δ τ)).trans
      (hausdorffContent_le_hausdorffMeasure hδ E)))
    (hausdorffContent_cover_set_contraction hs E hτ (ne_top_of_lt hτ1))

omit [MeasurableSpace X] [BorelSpace X] in
/-- If the `δ`-restricted content of `A` vanishes for one `δ`, it vanishes for every `δ' > 0`.

(The positivity of `δ'` is essential: `H^s_0` only admits covers by singletons, so it may well be
infinite for a set of vanishing `s`-dimensional Hausdorff measure.) -/
lemma hausdorffContent_eq_zero_of_hausdorffContent_eq_zero {s : ℝ} (hs : 0 < s) {δ δ' : ℝ≥0∞}
    (hδ' : 0 < δ') {A : Set X} (h : hausdorffContent s δ A = 0) :
    hausdorffContent s δ' A = 0 := by
  rcases le_or_gt δ δ' with hle | hlt
  · exact le_antisymm (le_trans (hausdorffContent_antitone hle A) h.le) (zero_le)
  by_contra hne
  have hpos : 0 < hausdorffContent s δ' A := pos_iff_ne_zero.mpr hne
  have hδ'top : δ' ≠ ⊤ := (hlt.trans_le le_top).ne
  set η := min (hausdorffContent s δ' A) (δ' ^ s) with hη
  have hηpos : 0 < η := lt_min hpos (ENNReal.rpow_pos hδ' hδ'top)
  have hlt2 : hausdorffContent s δ A < η := h ▸ hηpos
  rw [hausdorffContent] at hlt2
  obtain ⟨t, ht⟩ := iInf_lt_iff.mp hlt2
  obtain ⟨hcov, ht2⟩ := iInf_lt_iff.mp ht
  obtain ⟨hd, ht3⟩ := iInf_lt_iff.mp ht2
  have hd' : ∀ i, Metric.ediam (t i) ≤ δ' := by
    intro i
    rcases Set.eq_empty_or_nonempty (t i) with he | hne'
    · simp [he]
    · have h1 : (Metric.ediam (t i)) ^ s
          ≤ ∑' n, ⨆ (_ : (t n).Nonempty), (Metric.ediam (t n)) ^ s := by
        refine le_trans (le_of_eq ?_) (ENNReal.le_tsum i)
        rw [iSup_pos hne']
      have h2 : (Metric.ediam (t i)) ^ s < δ' ^ s :=
        lt_of_le_of_lt h1 (ht3.trans_le (min_le_right _ _))
      exact le_of_lt ((ENNReal.rpow_lt_rpow_iff hs).mp h2)
  have hle2 : hausdorffContent s δ' A
      ≤ ∑' n, ⨆ (_ : (t n).Nonempty), (Metric.ediam (t n)) ^ s := by
    rw [hausdorffContent]
    exact le_trans (iInf₂_le t hcov) (iInf_le _ hd')
  exact absurd (lt_of_le_of_lt hle2 (ht3.trans_le (min_le_left _ _))) (lt_irrefl _)

/-- If some `δ`-restricted content of `A` vanishes, then so does the Hausdorff measure of `A`. -/
lemma hausdorffMeasure_eq_zero_of_hausdorffContent_eq_zero {s : ℝ} (hs : 0 < s) {δ : ℝ≥0∞}
    {A : Set X} (h : hausdorffContent s δ A = 0) : μH[s] A = 0 := by
  refine le_antisymm ?_ (zero_le)
  rw [MeasureTheory.Measure.hausdorffMeasure_apply]
  refine iSup_le fun r => iSup_le fun hr => ?_
  exact le_of_eq (hausdorffContent_eq_zero_of_hausdorffContent_eq_zero hs hr h)

/-- **Lemma 0.4.** `H^s(E(δ,τ)) = 0` for every `δ > 0` and `0 < τ < 1`. -/
lemma hausdorffMeasure_cover_set_eq_zero {s : ℝ} (hs : 0 < s) (E : Set X) {δ τ : ℝ≥0∞}
    (hδ : 0 < δ) (hτ : τ ≠ 0) (hτ1 : τ < 1) (hE : μH[s] E ≠ ⊤) :
    μH[s] (coverSet s E δ τ) = 0 :=
  hausdorffMeasure_eq_zero_of_hausdorffContent_eq_zero hs
    (hausdorffContent_cover_set_eq_zero hs E hδ hτ hτ1 hE)

/-- Step (g): `H^s (⋃ k, E(1/k, 1 - 1/k)) = 0`. -/
lemma hausdorffMeasure_iUnion_cover_set_eq_zero {s : ℝ} (hs : 0 < s) (E : Set X)
    (hE : μH[s] E ≠ ⊤) :
    μH[s] (⋃ k : ℕ+, coverSet s E ((k : ℝ≥0∞))⁻¹ (1 - ((k : ℝ≥0∞))⁻¹)) = 0 := by
  refine measure_iUnion_null fun k => ?_
  have hktop : ((k : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hδpos : (0 : ℝ≥0∞) < ((k : ℕ) : ℝ≥0∞)⁻¹ := ENNReal.inv_pos.mpr hktop
  rcases eq_or_lt_of_le (show (1 : ℕ) ≤ (k : ℕ) from k.property) with hk1 | hk1
  · -- `k = 1`, so `τ = 0`; use monotonicity in `τ` and the already known case `τ = 1/2`.
    have hkeq : ((k : ℕ) : ℝ≥0∞) = 1 := by rw [← hk1]; simp
    rw [hkeq]
    simp only [inv_one, tsub_self]
    refine measure_mono_null
      (cover_set_mono_tau s E 1 (show (0 : ℝ≥0∞) ≤ 1 / 2 from zero_le)) ?_
    exact hausdorffMeasure_cover_set_eq_zero hs E one_pos (by norm_num) (by norm_num) hE
  · have h1k : (1 : ℝ≥0∞) < ((k : ℕ) : ℝ≥0∞) := by
      exact_mod_cast (by exact_mod_cast hk1 : (1 : ℕ) < (k : ℕ))
    have hτ0 : (1 : ℝ≥0∞) - ((k : ℕ) : ℝ≥0∞)⁻¹ ≠ 0 :=
      (tsub_pos_iff_lt.mpr (ENNReal.inv_lt_one.mpr h1k)).ne'
    have hτ1 : (1 : ℝ≥0∞) - ((k : ℕ) : ℝ≥0∞)⁻¹ < 1 :=
      ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hδpos.ne'
    exact hausdorffMeasure_cover_set_eq_zero hs E hδpos hτ0 hτ1 hE

omit [MeasurableSpace X] [BorelSpace X] in
/-- At the exponent `s = 0`, the unrestricted content of a nonempty set is at least `1`. -/
lemma one_le_hausdorffContentInfty_zero {A : Set X} (hA : A.Nonempty) :
    1 ≤ hausdorffContentInfty 0 A := by
  rw [hausdorffContentInfty]
  refine le_iInf fun t => le_iInf fun hcov => ?_
  obtain ⟨y, hy⟩ := hA
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hy)
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum i)
  rw [iSup_pos ⟨y, hi⟩, ENNReal.rpow_zero]

end Vanishing

/-! ## From a small upper density to membership in some `E(δ, τ)` -/

section Density

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
/-- The `s`-dimensional density ratio of `H^s_∞` restricted to `E`, written out explicitly. -/
lemma dimensional_density_ratio_contentInfty (s : ℝ) (E : Set X) (x : X) {r : ℝ} (hr : 0 ≤ r) :
    dimensionalDensityRatio (OuterMeasure.restrict E (hausdorffContentInftyOuter s)) s x r
      = hausdorffContentInfty s (Metric.closedBall x r ∩ E) / ENNReal.ofReal ((2 * r) ^ s) := by
  rw [dimensional_density_ratio_closedBall _ _ _ hr, OuterMeasure.restrict_apply,
    hausdorffContentInftyOuter_apply]

/-- The density ratio of the restricted Hausdorff measure is `H^s(B(x,r) ∩ E) / (2r)^s`. -/
lemma density_ratio_apply (s : ℝ) (E : Set X) (x : X) {r : ℝ} (hr : 0 ≤ r) :
    dimensionalDensityRatio ((μH[s]).restrict E).toOuterMeasure s x r
      = μH[s] (Metric.closedBall x r ∩ E) / ENNReal.ofReal ((2 * r) ^ s) := by
  rw [dimensional_density_ratio_closedBall _ _ _ hr, Measure.toOuterMeasure_apply,
    Measure.restrict_apply Metric.isClosed_closedBall.measurableSet]

omit [MeasurableSpace X] [BorelSpace X] in
/-- **Lemma 0.5 (from small density to small density ratio).** -/
lemma exists_delta_of_upper_density_lt {s : ℝ} (E : Set X) (x : X)
    (hx : dimensionalUpperDensity (OuterMeasure.restrict E (hausdorffContentInftyOuter s)) s x
      < ENNReal.ofReal (1 / 2 ^ s)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ r : ℝ, 0 < r → r ≤ δ →
      hausdorffContentInfty s (Metric.closedBall x r ∩ E) / ENNReal.ofReal ((2 * r) ^ s)
        < ENNReal.ofReal ((1 - δ) / 2 ^ s) := by
  obtain ⟨b, hb0, hb1, hb2⟩ := ENNReal.lt_iff_exists_real_btwn.mp hx
  have h2s : (0 : ℝ) < 2 ^ s := Real.rpow_pos_of_pos two_pos s
  have hblt : b < 1 / 2 ^ s := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hb2
  have hb2s : b * 2 ^ s < 1 := by
    rw [lt_div_iff₀ h2s] at hblt; linarith
  set δ₀ : ℝ := 1 - b * 2 ^ s with hδ₀
  have hδ₀pos : 0 < δ₀ := by simp only [hδ₀]; linarith
  have hδ₀le : δ₀ ≤ 1 := by
    simp only [hδ₀]
    nlinarith
  have hbeq : b = (1 - δ₀) / 2 ^ s := by
    rw [hδ₀]; field_simp; ring
  have hev := eventually_lt_of_upper_density_lt (μ := OuterMeasure.restrict E
    (hausdorffContentInftyOuter s)) s x _ hb1
  rw [Filter.eventually_iff, mem_nhdsGT_iff_exists_Ioc_subset] at hev
  obtain ⟨u, hu, hsub⟩ := hev
  have hu0 : (0 : ℝ) < u := hu
  refine ⟨min δ₀ u, lt_min hδ₀pos hu0, (min_le_left _ _).trans hδ₀le, ?_⟩
  intro r hr0 hrle
  have hrmem : r ∈ Set.Ioc (0 : ℝ) u := ⟨hr0, hrle.trans (min_le_right _ _)⟩
  have hlt := hsub hrmem
  simp only [Set.mem_ofPred_eq, dimensional_density_ratio_contentInfty _ _ _ hr0.le] at hlt
  refine hlt.trans_le (ENNReal.ofReal_le_ofReal ?_)
  rw [hbeq]
  gcongr
  linarith [min_le_left δ₀ u]

omit [MeasurableSpace X] [BorelSpace X] in
/-- **Lemma 0.6.**  The hypothesis `x ∈ E` occurs in the statement in the source (`x ∈ E ∩ C`);
the proof only uses `x ∈ C`.  The bound `δ ≤ 1` is implicit in the source: for `δ > 1` the
hypothesis on the density ratios cannot be satisfied. -/
lemma hausdorffContentInfty_inter_le {s : ℝ} (hs : 0 < s) (E : Set X) (x : X) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {C : Set X} (hxC : x ∈ C)
    (hC : Metric.ediam C ≤ ENNReal.ofReal δ)
    (hdens : ∀ r : ℝ, 0 < r → r ≤ δ →
      hausdorffContentInfty s (Metric.closedBall x r ∩ E) / ENNReal.ofReal ((2 * r) ^ s)
        < ENNReal.ofReal ((1 - δ) / 2 ^ s)) :
    hausdorffContentInfty s (C ∩ E) ≤ ENNReal.ofReal (1 - δ) * (Metric.ediam C) ^ s := by
  rcases eq_or_lt_of_le (zero_le : (0 : ENNReal) ≤ Metric.ediam C) with h0 | hpos
  · have hz : Metric.ediam (C ∩ E) = 0 :=
      le_antisymm (h0 ▸ Metric.ediam_mono Set.inter_subset_left) bot_le
    rw [hausdorffContentInfty_eq_zero_of_ediam_eq_zero hs hz]
    exact bot_le
  · have hdtop : Metric.ediam C ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hC
    set d := (Metric.ediam C).toReal with hd
    have hd0 : 0 < d := ENNReal.toReal_pos hpos.ne' hdtop
    have hdeq : ENNReal.ofReal d = Metric.ediam C := ENNReal.ofReal_toReal hdtop
    have hdδ : d ≤ δ := by
      have h := (ENNReal.toReal_le_toReal hdtop ENNReal.ofReal_ne_top).mpr hC
      rwa [ENNReal.toReal_ofReal hδ.le] at h
    have hsub : C ∩ E ⊆ Metric.closedBall x d ∩ E := by
      rintro y ⟨hyC, hyE⟩
      refine ⟨?_, hyE⟩
      have h1 : edist y x ≤ Metric.ediam C := Metric.edist_le_ediam_of_mem hyC hxC
      rw [Metric.mem_closedBall]
      have h2 := (ENNReal.toReal_le_toReal (edist_ne_top y x) hdtop).mpr h1
      rwa [edist_dist, ENNReal.toReal_ofReal dist_nonneg] at h2
    have hb := hdens d hd0 hdδ
    have h2d : (0 : ℝ) < (2 * d) ^ s := Real.rpow_pos_of_pos (by linarith) s
    have h2s : (0 : ℝ) < 2 ^ s := Real.rpow_pos_of_pos two_pos s
    rw [ENNReal.div_lt_iff
      (Or.inl (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact h2d))
      (Or.inl ENNReal.ofReal_ne_top)] at hb
    refine le_trans (hausdorffContentInfty_mono hsub) (le_of_lt (hb.trans_le (le_of_eq ?_)))
    rw [← ENNReal.ofReal_mul (div_nonneg (by linarith) h2s.le)]
    rw [show (1 - δ) / 2 ^ s * (2 * d) ^ s = (1 - δ) * d ^ s by
      rw [Real.mul_rpow (by norm_num) hd0.le]
      field_simp]
    rw [ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_rpow_of_pos hd0, hdeq]

omit [MeasurableSpace X] [BorelSpace X] in
/-- Steps (j), (k): `x ∈ E(δ, 1 - δ)`.  Step (j) is the bound of Lemma 0.6 for the `δ`-restricted
content, obtained from `hausdorffContentInfty_inter_le` and
`hausdorffContent_le_hausdorffContentInfty`. -/
lemma mem_cover_set_of_density_lt {s : ℝ} (hs : 0 < s) (E : Set X) (x : X) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hxE : x ∈ E)
    (hdens : ∀ r : ℝ, 0 < r → r ≤ δ →
      hausdorffContentInfty s (Metric.closedBall x r ∩ E) / ENNReal.ofReal ((2 * r) ^ s)
        < ENNReal.ofReal ((1 - δ) / 2 ^ s)) :
    x ∈ coverSet s E (ENNReal.ofReal δ) (1 - ENNReal.ofReal δ) := by
  refine ⟨hxE, fun C hxC hCd => ?_⟩
  have h := le_trans (hausdorffContent_le_hausdorffContentInfty hs.le
      (le_trans (Metric.ediam_mono Set.inter_subset_left) hCd))
    (hausdorffContentInfty_inter_le hs E x hδ hδ1 hxC hCd hdens)
  rwa [show (1 : ℝ≥0∞) - ENNReal.ofReal δ = ENNReal.ofReal (1 - δ) by
    rw [ENNReal.ofReal_sub _ hδ.le, ENNReal.ofReal_one]]

omit [MeasurableSpace X] [BorelSpace X] in
/-- Step (l): a point of `E` with small upper density lies in one of the sets `E(1/k, 1 - 1/k)`. -/
lemma mem_iUnion_cover_set_of_upper_density_lt {s : ℝ} (hs : 0 < s) (E : Set X) (x : X)
    (hxE : x ∈ E)
    (hx : dimensionalUpperDensity (OuterMeasure.restrict E (hausdorffContentInftyOuter s)) s x
      < ENNReal.ofReal (1 / 2 ^ s)) :
    x ∈ ⋃ k : ℕ+, coverSet s E ((k : ℝ≥0∞))⁻¹ (1 - ((k : ℝ≥0∞))⁻¹) := by
  obtain ⟨δ, hδ, hδ1, hdens⟩ := exists_delta_of_upper_density_lt E x hx
  have hmem : x ∈ coverSet s E (ENNReal.ofReal δ) (1 - ENNReal.ofReal δ) :=
    mem_cover_set_of_density_lt hs E x hδ hδ1 hxE hdens
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  obtain ⟨k, hkval⟩ : ∃ k : ℕ+, ((k : ℕ) : ℝ) = (n : ℝ) + 1 :=
    ⟨⟨n + 1, Nat.succ_pos n⟩, by
      change ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1
      push_cast; ring⟩
  have hkpos : (0 : ℝ) < ((k : ℕ) : ℝ) := by rw [hkval]; positivity
  have hkle : (((k : ℕ) : ℝ≥0∞))⁻¹ ≤ ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hkpos]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hkval, inv_eq_one_div]
    exact hn.le
  have hkinvpos : (0 : ℝ≥0∞) < (((k : ℕ) : ℝ≥0∞))⁻¹ :=
    ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _)
  exact Set.mem_iUnion.mpr ⟨k, cover_set_mono_delta hs.le E hkinvpos hkle hmem⟩

end Density

end

/-! # Part II: the upper density bound

The proof follows the classical argument:

* `superlevelSet s E t` is the set `B_t` of points of `E` at which the upper density exceeds `t`;
* the restricted measure `H^s ⌞ E` is regular (`HausdorffRestrict.toRadonOuterMeasure`), so
  `B_t` can be approximated from outside by an open set `U`;
* the family `ballFamily` of closed balls contained in `U`, of radius `< δ`, on which the density
  exceeds `t`, is a fine cover of `B_t`, and the variant of Vitali's covering theorem
  (`vitali_variant_classical`) produces a countable disjoint subfamily whose `5`-fold enlargement
  (outside of any finite subfamily) still covers `B_t`;
* this yields covers of `B_t` of arbitrarily small mesh whose gauge sums are at most
  `t⁻¹ (H^s(B_t) + ε) + 5^s t⁻¹ ε`, whence `H^s(B_t) ≤ t⁻¹ H^s(B_t)` and so `H^s(B_t) = 0` for
  every `t > 1`;
* the exceptional set of the theorem is the countable union of the sets `B_{1 + 1/n}`.
-/

open scoped BigOperators Real Nat Pointwise ENNReal NNReal
open MeasureTheory MeasureTheory.OuterMeasure Metric Set Filter Topology

namespace HausdorffDensity

noncomputable section

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/-! ## Preliminaries on the Hausdorff measure and on closed balls -/

omit [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
/-- A closed ball of radius `r` has diameter at most `2r`. -/
lemma ediam_closedBall_le (x : X) (r : ℝ) :
    Metric.ediam (Metric.closedBall x r) ≤ ENNReal.ofReal (2 * r) := by
  refine Metric.ediam_le_of_forall_dist_le ?_
  intro y hy z hz
  have hy' := Metric.mem_closedBall.mp hy
  have hz' := Metric.mem_closedBall.mp hz
  calc dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
    _ ≤ r + r := by rw [dist_comm x z]; linarith
    _ = 2 * r := by ring

/-! ## The sets `B_t` and the ball family `F` -/

/-- **(a)** The super-level set of the upper `s`-density of `H^s ⌞ E`:
`B_t = {x ∈ E | limsup_{r → 0} H^s(B(x,r) ∩ E) / (2r)^s > t}`. -/
def superlevelSet (s : ℝ) (E : Set X) (t : ℝ≥0∞) : Set X :=
  {x ∈ E | t < dimensionalUpperDensity ((μH[s]).restrict E).toOuterMeasure s x}

/-- **(f)** The family of closed balls `B(x,r) ⊆ U` with `0 < r < δ` on which the `s`-density
of `E` exceeds `t`; a ball is encoded by the pair `(x, r)` of its centre and radius. -/
def ballFamily (s : ℝ) (E U : Set X) (δ : ℝ) (t : ℝ≥0∞) : Set (X × ℝ) :=
  {a : X × ℝ | Metric.closedBall a.1 a.2 ⊆ U ∧ 0 < a.2 ∧ a.2 < δ ∧
    t * ENNReal.ofReal ((2 * a.2) ^ s) < μH[s] (E ∩ Metric.closedBall a.1 a.2)}

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma superlevelSet_subset (s : ℝ) (E : Set X) (t : ℝ≥0∞) : superlevelSet s E t ⊆ E :=
  fun _ hx => hx.1

/-! ## (b)–(e): outer approximation coming from the Radon property -/

/-- **(b), (c), (d), (e).** Since the restricted measure `H^s ⌞ E` is regular, any subset `A` of `E`
is approximated from outside by open sets: for every `ε > 0` there is an open `U ⊇ A` with
`H^s(U ∩ E) < H^s(A) + ε`. -/
lemma exists_open_superset_measure_lt {s : ℝ} (hs : 0 ≤ s) {E : Set X}
    (hEmeas : MeasurableSet[(OuterMeasure.mkMetric (X := X) (fun r => r ^ s)).caratheodory] E)
    (hEfin : μH[s] E ≠ ⊤) (A : Set X) (hAE : A ⊆ E) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ μH[s] (U ∩ E) < μH[s] A + ε := by
  -- The restriction of the Hausdorff measure to `E` is regular.
  have _ : ((μH[s] : Measure X).restrict E).Regular := by
    have hborel : ‹MeasurableSpace X› = borel X := BorelSpace.measurable_eq
    subst hborel
    exact HausdorffRestrict.toRadonOuterMeasure s hs E hEmeas (lt_top_iff_ne_top.2 hEfin)
  set m : Measure X := (μH[s] : Measure X).restrict E with hm
  have hmA : m A ≤ μH[s] A := Measure.restrict_apply_le _ _
  have hAfin : μH[s] A ≠ ⊤ := ne_top_of_le_ne_top hEfin (measure_mono hAE)
  obtain ⟨U, hAU, hUopen, hUlt⟩ := exists_isOpen_lt_of_lt (μ := m) A (μH[s] A + ε)
    (lt_of_le_of_lt hmA (ENNReal.lt_add_right hAfin hε))
  refine ⟨U, hUopen, hAU, ?_⟩
  calc μH[s] (U ∩ E) = m U := by
        rw [hm, Measure.restrict_apply hUopen.measurableSet]
    _ < μH[s] A + ε := hUlt

/-! ## Fineness of the ball family -/

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- The family `F` of balls is a *fine* cover of `B_t`: through every point of `B_t` there are
balls of `F` of arbitrarily small radius centred at that point. -/
lemma fine_ballFamily {s : ℝ} {E U : Set X} (hU : IsOpen U) {t : ℝ≥0∞} {δ : ℝ} (hδ : 0 < δ)
    (hBU : superlevelSet s E t ⊆ U) (x : X) (hx : x ∈ superlevelSet s E t) {η : ℝ} (hη : 0 < η) :
    ∃ a ∈ ballFamily s E U δ t, a.2 ≤ η ∧ a.1 = x := by
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.mp hU x (hBU hx)
  have hfreq : ∃ᶠ r in 𝓝[>] (0 : ℝ),
      t < dimensionalDensityRatio ((μH[s]).restrict E).toOuterMeasure s x r :=
    frequently_gt_of_upper_density_gt s x t hx.2
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Set.Ioo 0 (min (min η δ) (r₀ / 2)) :=
    Ioo_mem_nhdsGT (by positivity)
  obtain ⟨r, hr1, hr2⟩ := (hfreq.and_eventually hev).exists
  have hrpos : 0 < r := hr2.1
  have hrη : r ≤ η := le_trans (le_of_lt hr2.2) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hrδ : r < δ := lt_of_lt_of_le hr2.2 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hrr₀ : r < r₀ := lt_of_lt_of_le hr2.2 (le_trans (min_le_right _ _) (by linarith))
  refine ⟨(x, r), ⟨?_, hrpos, hrδ, ?_⟩, hrη, rfl⟩
  · exact (Metric.closedBall_subset_ball hrr₀).trans hball
  · rw [density_ratio_apply _ _ _ hrpos.le] at hr1
    have hpos : (0 : ℝ) < (2 * r) ^ s := Real.rpow_pos_of_pos (by linarith) s
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by simpa using hpos))
      (Or.inl ENNReal.ofReal_ne_top)] at hr1
    simpa [Set.inter_comm] using hr1

/-! ## Choosing a finite subfamily carrying almost all of the mass -/

/-- Tails of a convergent sum in `ℝ≥0∞` are eventually small. -/
lemma exists_finset_tsum_compl_le {ι : Type*} (f : ι → ℝ≥0∞) (hf : ∑' i, f i ≠ ⊤)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ W : Finset ι, ∑' i : ((W : Set ι)ᶜ : Set ι), f i ≤ ε := by
  by_cases hle : ∑' i, f i ≤ ε
  · refine ⟨∅, le_trans ?_ hle⟩
    have := ENNReal.sum_add_tsum_compl (s := (∅ : Finset ι)) (f := f)
    simp only [Finset.sum_empty, zero_add] at this
    exact le_of_eq this
  · push Not at hle
    have hsub : ∑' i, f i - ε < ∑' i, f i := ENNReal.sub_lt_self hf (by
      intro h; rw [h] at hle; exact absurd hle (by simp)) hε
    rw [ENNReal.tsum_eq_iSup_sum] at hsub
    obtain ⟨W, hW⟩ := lt_iSup_iff.mp hsub
    rw [← ENNReal.tsum_eq_iSup_sum] at hW
    refine ⟨W, ?_⟩
    have hsplit := ENNReal.sum_add_tsum_compl (s := W) (f := f)
    have hWfin : ∑ i ∈ W, f i ≠ ⊤ := by
      refine ne_top_of_le_ne_top hf ?_
      rw [← hsplit]; exact le_self_add
    have h1 : ∑' i, f i < ∑ i ∈ W, f i + ε :=
      (ENNReal.sub_lt_iff_lt_right (ne_top_of_lt hle) hle.le).mp hW
    rw [← hsplit] at h1
    exact le_of_lt ((ENNReal.add_lt_add_iff_left hWfin).mp h1)

/-! ## (g)–(j): the covering estimate at scale `δ` -/

/-- **(g), (h), (i), (j).** For every `δ > 0` and `ε > 0` there is a countable cover of `B_t` by
sets of diameter at most `10 δ` whose gauge sum is at most
`t⁻¹ (H^s(B_t) + ε) + 5^s t⁻¹ ε`.

The cover is produced by applying the variant of Vitali's covering theorem
(`vitali_variant_classical`) to the fine family `ballFamily s E U δ t`, where `U` is an open set
containing `B_t` with `H^s(U ∩ E) < H^s(B_t) + ε`: one keeps the balls of a large finite
subfamily and the `5`-fold enlargements of the remaining ones. -/
lemma exists_cover_le {s : ℝ} (hs : 0 ≤ s) {E : Set X}
    (hEmeas : MeasurableSet[(OuterMeasure.mkMetric (X := X) (fun r => r ^ s)).caratheodory] E)
    (hEfin : μH[s] E ≠ ⊤) {t : ℝ≥0∞} (ht0 : t ≠ 0) (httop : t ≠ ⊤)
    {δ : ℝ} (hδ : 0 < δ) {ε : ℝ≥0∞} (hε0 : ε ≠ 0) :
    ∃ (u : Set (X × ℝ)) (C : X × ℝ → Set X), u.Countable ∧
      (∀ b ∈ u, Metric.ediam (C b) ≤ ENNReal.ofReal (10 * δ)) ∧
      superlevelSet s E t ⊆ ⋃ b ∈ u, C b ∧
      ∑' b : u, Metric.ediam (C ↑b) ^ s
        ≤ t⁻¹ * (μH[s] (superlevelSet s E t) + ε) + ENNReal.ofReal (5 ^ s) * t⁻¹ * ε := by
  classical
  set A := superlevelSet s E t with hA
  -- **(b)–(e)** an open set `U ⊇ B_t` with `H^s(U ∩ E) < H^s(B_t) + ε`
  obtain ⟨U, hUopen, hAU, hUlt⟩ :=
    exists_open_superset_measure_lt hs hEmeas hEfin A (superlevelSet_subset s E t) hε0
  set T := ballFamily s E U δ t with hT
  -- **(g)** the variant of Vitali's covering theorem applied to the fine family `T`
  have hfine : ∀ x ∈ A, ∀ η > (0 : ℝ), ∃ a ∈ T, a.2 ≤ η ∧ a.1 = x :=
    fun x hx η hη => fine_ballFamily hUopen hδ hAU x hx hη
  have hrad : ∃ R, ∀ a ∈ T, a.2 ≤ R := ⟨δ, fun _ ha => le_of_lt ha.2.2.1⟩
  have hpos : ∀ a ∈ T, 0 < a.2 := fun _ ha => ha.2.1
  obtain ⟨u, hut, hucount, hudisj, hucov⟩ :=
    vitali_variant_classical (X := A) T Prod.fst Prod.snd hfine hrad hpos
  have _ : Countable ↥u := hucount.to_subtype
  -- the mass of `E` inside each selected ball
  set f : X × ℝ → ℝ≥0∞ := fun b => μH[s] (E ∩ Metric.closedBall b.1 b.2) with hf
  set nu : Measure X := (μH[s]).restrict E with hnu
  have hnuball : ∀ b : X × ℝ, nu (Metric.closedBall b.1 b.2) = f b := fun b => by
    rw [hnu, Measure.restrict_apply Metric.isClosed_closedBall.measurableSet, hf, Set.inter_comm]
  have hdisj' : Pairwise (Function.onFun Disjoint
      fun b : ↥u => Metric.closedBall (b : X × ℝ).1 (b : X × ℝ).2) :=
    fun b₁ b₂ hne => hudisj b₁.2 b₂.2 (fun h => hne (Subtype.ext h))
  -- **(i)** the total mass of the selected balls is finite, so a finite subfamily carries all
  -- but `ε` of it
  have htsum_le : ∑' b : ↥u, f ↑b ≤ μH[s] E := by
    have h1 : ∑' b : ↥u, f ↑b
        = nu (⋃ b : ↥u, Metric.closedBall (b : X × ℝ).1 (b : X × ℝ).2) := by
      rw [measure_iUnion hdisj' (fun _ => Metric.isClosed_closedBall.measurableSet)]
      exact tsum_congr fun b => (hnuball ↑b).symm
    rw [h1]
    calc nu (⋃ b : ↥u, Metric.closedBall (b : X × ℝ).1 (b : X × ℝ).2) ≤ nu Set.univ :=
          measure_mono (Set.subset_univ _)
      _ = μH[s] E := by rw [hnu, Measure.restrict_apply_univ]
  have htsum_fin : ∑' b : ↥u, f ↑b ≠ ⊤ := ne_top_of_le_ne_top hEfin htsum_le
  obtain ⟨W, hW⟩ := exists_finset_tsum_compl_le (fun b : ↥u => f ↑b) htsum_fin hε0
  set w : Finset (X × ℝ) := W.image Subtype.val with hw
  have hmemw : ∀ b : ↥u, ((↑b : X × ℝ) ∈ w) ↔ b ∈ W := by
    intro b
    rw [hw]
    constructor
    · intro h
      obtain ⟨c, hc, hcb⟩ := Finset.mem_image.mp h
      exact (Subtype.ext hcb : c = b) ▸ hc
    · intro h; exact Finset.mem_image.mpr ⟨b, h, rfl⟩
  have hwu : (w : Set (X × ℝ)) ⊆ u := by
    intro a ha
    rw [hw, Finset.coe_image] at ha
    obtain ⟨b, -, rfl⟩ := ha
    exact b.2
  have hwT : (w : Set (X × ℝ)) ⊆ T := hwu.trans hut
  -- the cover: the balls of the finite subfamily, and the `5`-fold enlargements of the others
  set C : X × ℝ → Set X := fun b =>
    if b ∈ w then Metric.closedBall b.1 b.2 else Metric.closedBall b.1 (5 * b.2) with hC
  have hballU : ∀ b ∈ u, Metric.closedBall (b : X × ℝ).1 (b : X × ℝ).2 ⊆ U :=
    fun b hb => (hut hb).1
  refine ⟨u, C, hucount, ?_, ?_, ?_⟩
  · -- diameters are at most `10 δ`
    intro b hb
    have hb2 : b.2 < δ := (hut hb).2.2.1
    have hb2pos : 0 < b.2 := (hut hb).2.1
    by_cases hbw : b ∈ w
    · rw [hC]
      simp only [ite_eq_left hbw]
      exact le_trans (ediam_closedBall_le _ _) (ENNReal.ofReal_le_ofReal (by linarith))
    · rw [hC]
      simp only [ite_eq_right hbw]
      refine le_trans (ediam_closedBall_le _ _) (ENNReal.ofReal_le_ofReal (by linarith))
  · -- the cover property, from the conclusion of Vitali's theorem
    intro x hx
    by_cases hcase : ∃ a ∈ w, x ∈ Metric.closedBall a.1 a.2
    · obtain ⟨a, haw, hxa⟩ := hcase
      refine Set.mem_biUnion (hwu haw) ?_
      rw [hC]; simpa only [ite_eq_left haw] using hxa
    · push Not at hcase
      have hxdiff : x ∈ A \ ⋃ a ∈ w, Metric.closedBall a.1 a.2 := by
        refine ⟨hx, ?_⟩
        simpa using hcase
      obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.mp (hucov w hwT hxdiff)
      have hbw : b ∉ w := fun h => hb.2 (Finset.mem_coe.mpr h)
      refine Set.mem_biUnion hb.1 ?_
      rw [hC]; simpa only [ite_eq_right hbw] using hxb
  · -- **(h)** the gauge sum estimate
    have hbound : ∀ b : ↥u, Metric.ediam (C ↑b) ^ s ≤
        (if (↑b : X × ℝ) ∈ w then t⁻¹ * f ↑b
          else ENNReal.ofReal (5 ^ s) * (t⁻¹ * f ↑b)) := by
      intro b
      have hbT : (↑b : X × ℝ) ∈ T := hut b.2
      have hb2 : 0 < (↑b : X × ℝ).2 := hbT.2.1
      have hkey : ENNReal.ofReal ((2 * (↑b : X × ℝ).2) ^ s) ≤ t⁻¹ * f ↑b := by
        calc ENNReal.ofReal ((2 * (↑b : X × ℝ).2) ^ s)
            = t⁻¹ * (t * ENNReal.ofReal ((2 * (↑b : X × ℝ).2) ^ s)) := by
              rw [← mul_assoc, ENNReal.inv_mul_cancel ht0 httop, one_mul]
          _ ≤ t⁻¹ * f ↑b := by gcongr; exact hbT.2.2.2.le
      by_cases hbw : (↑b : X × ℝ) ∈ w
      · rw [hC]
        simp only [ite_eq_left hbw]
        refine le_trans ?_ hkey
        calc Metric.ediam (Metric.closedBall (↑b : X × ℝ).1 (↑b : X × ℝ).2) ^ s
            ≤ ENNReal.ofReal (2 * (↑b : X × ℝ).2) ^ s :=
              ENNReal.rpow_le_rpow (ediam_closedBall_le _ _) hs
          _ = ENNReal.ofReal ((2 * (↑b : X × ℝ).2) ^ s) :=
              ENNReal.ofReal_rpow_of_nonneg (by positivity) hs
      · rw [hC]
        simp only [ite_eq_right hbw]
        have h10 : (2 : ℝ) * (5 * (↑b : X × ℝ).2) = 5 * (2 * (↑b : X × ℝ).2) := by ring
        calc Metric.ediam (Metric.closedBall (↑b : X × ℝ).1 (5 * (↑b : X × ℝ).2)) ^ s
            ≤ ENNReal.ofReal (2 * (5 * (↑b : X × ℝ).2)) ^ s :=
              ENNReal.rpow_le_rpow (ediam_closedBall_le _ _) hs
          _ = ENNReal.ofReal ((5 * (2 * (↑b : X × ℝ).2)) ^ s) := by
              rw [h10, ENNReal.ofReal_rpow_of_nonneg (by positivity) hs]
          _ = ENNReal.ofReal (5 ^ s) * ENNReal.ofReal ((2 * (↑b : X × ℝ).2) ^ s) := by
              rw [Real.mul_rpow (by norm_num) (by positivity),
                ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) s)]
          _ ≤ ENNReal.ofReal (5 ^ s) * (t⁻¹ * f ↑b) := by gcongr
    have hfinite : ∑ b ∈ W, (if (↑b : X × ℝ) ∈ w then t⁻¹ * f ↑b
        else ENNReal.ofReal (5 ^ s) * (t⁻¹ * f ↑b)) ≤ t⁻¹ * μH[s] (U ∩ E) := by
      have h1 : ∑ b ∈ W, (if (↑b : X × ℝ) ∈ w then t⁻¹ * f ↑b
          else ENNReal.ofReal (5 ^ s) * (t⁻¹ * f ↑b)) = t⁻¹ * ∑ b ∈ W, f ↑b := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b hb => ?_
        rw [ite_eq_left ((hmemw b).mpr hb)]
      rw [h1]
      have h2 : ∑ b ∈ W, f ↑b
          = nu (⋃ b ∈ W, Metric.closedBall (b : X × ℝ).1 (b : X × ℝ).2) := by
        rw [measure_biUnion_finset (fun b₁ hb₁ b₂ hb₂ hne => hdisj' hne)
          (fun _ _ => Metric.isClosed_closedBall.measurableSet)]
        exact Finset.sum_congr rfl fun b _ => (hnuball ↑b).symm
      rw [h2]
      have h3 : nu (⋃ b ∈ W, Metric.closedBall (b : X × ℝ).1 (b : X × ℝ).2) ≤ μH[s] (U ∩ E) := by
        have hsub : (⋃ b ∈ W, Metric.closedBall (b : X × ℝ).1 (b : X × ℝ).2) ⊆ U :=
          Set.iUnion₂_subset fun b _ => hballU _ b.2
        calc nu (⋃ b ∈ W, Metric.closedBall (b : X × ℝ).1 (b : X × ℝ).2)
            ≤ nu U := measure_mono hsub
          _ = μH[s] (U ∩ E) := by rw [hnu, Measure.restrict_apply hUopen.measurableSet]
      gcongr
    have htail : ∑' b : ((W : Set ↥u)ᶜ : Set ↥u),
        (if ((b : ↥u) : X × ℝ) ∈ w then t⁻¹ * f ↑(b : ↥u)
          else ENNReal.ofReal (5 ^ s) * (t⁻¹ * f ↑(b : ↥u)))
        ≤ ENNReal.ofReal (5 ^ s) * t⁻¹ * ε := by
      have h1 : ∀ b : ((W : Set ↥u)ᶜ : Set ↥u),
          (if ((b : ↥u) : X × ℝ) ∈ w then t⁻¹ * f ↑(b : ↥u)
            else ENNReal.ofReal (5 ^ s) * (t⁻¹ * f ↑(b : ↥u)))
          = ENNReal.ofReal (5 ^ s) * t⁻¹ * f ↑(b : ↥u) := by
        intro b
        have hb : ((b : ↥u) : X × ℝ) ∉ w := fun h => b.2 ((hmemw _).mp h)
        rw [ite_eq_right hb, mul_assoc]
      rw [tsum_congr h1, ENNReal.tsum_mul_left]
      gcongr
    calc ∑' b : ↥u, Metric.ediam (C ↑b) ^ s
        ≤ ∑' b : ↥u, (if (↑b : X × ℝ) ∈ w then t⁻¹ * f ↑b
            else ENNReal.ofReal (5 ^ s) * (t⁻¹ * f ↑b)) := ENNReal.tsum_le_tsum hbound
      _ = ∑ b ∈ W, (if (↑b : X × ℝ) ∈ w then t⁻¹ * f ↑b
              else ENNReal.ofReal (5 ^ s) * (t⁻¹ * f ↑b))
            + ∑' b : ((W : Set ↥u)ᶜ : Set ↥u),
              (if ((b : ↥u) : X × ℝ) ∈ w then t⁻¹ * f ↑(b : ↥u)
                else ENNReal.ofReal (5 ^ s) * (t⁻¹ * f ↑(b : ↥u))) :=
          (ENNReal.sum_add_tsum_compl W _).symm
      _ ≤ t⁻¹ * μH[s] (U ∩ E) + ENNReal.ofReal (5 ^ s) * t⁻¹ * ε := add_le_add hfinite htail
      _ ≤ t⁻¹ * (μH[s] A + ε) + ENNReal.ofReal (5 ^ s) * t⁻¹ * ε := by gcongr

/-! ## (k), (l): the super-level sets are null -/

/-- **(k), (l).** For every `t > 1` the set `B_t` is `H^s`-null. -/
theorem superlevelSet_null {s : ℝ} (hs : 0 ≤ s) {E : Set X}
    (hEmeas : MeasurableSet[(OuterMeasure.mkMetric (X := X) (fun r => r ^ s)).caratheodory] E)
    (hEfin : μH[s] E ≠ ⊤) {t : ℝ≥0∞} (ht : 1 < t) (httop : t ≠ ⊤) :
    μH[s] (superlevelSet s E t) = 0 := by
  set A := superlevelSet s E t with hA
  have hAE : A ⊆ E := superlevelSet_subset s E t
  have hAfin : μH[s] A ≠ ⊤ := ne_top_of_le_ne_top hEfin (measure_mono hAE)
  have ht0 : t ≠ 0 := (zero_lt_one.trans ht).ne'
  have htinv : t⁻¹ < 1 := ENNReal.inv_lt_one.mpr ht
  have htinv_top : t⁻¹ ≠ ⊤ := (lt_of_lt_of_le htinv le_top).ne
  -- **(j)** For every `ε > 0`, `H^s(B_t) ≤ t⁻¹ (H^s(B_t) + ε) + 5^s t⁻¹ ε`; this comes from the
  -- covers of mesh `10/(n+1)` produced by `exists_cover_le`.
  have key : ∀ ε : ℝ≥0∞, ε ≠ 0 →
      μH[s] A ≤ t⁻¹ * (μH[s] A + ε) + ENNReal.ofReal (5 ^ s) * t⁻¹ * ε := by
    intro ε hε0
    choose u C hcount hdiam hcov hsum using
      fun n : ℕ => exists_cover_le hs hEmeas hEfin ht0 httop
        (δ := 1 / (n + 1 : ℝ)) (by positivity) hε0
    have _ : ∀ n : ℕ, Countable ↥(u n) := fun n => (hcount n).to_subtype
    have htend : Tendsto (fun n : ℕ => ENNReal.ofReal (10 * (1 / (n + 1 : ℝ)))) atTop (𝓝 0) := by
      have h : Tendsto (fun n : ℕ => 10 * (1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (10 : ℝ)
      simpa using ENNReal.tendsto_ofReal h
    have hle := MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum (X := X) s A
      (fun n : ℕ => ENNReal.ofReal (10 * (1 / (n + 1 : ℝ)))) htend
      (fun n (i : ↥(u n)) => C n ↑i)
      (Eventually.of_forall (fun n i => hdiam n ↑i i.2))
      (Eventually.of_forall (fun n => by
        have h := hcov n
        rwa [Set.biUnion_eq_iUnion] at h))
    refine le_trans hle ?_
    refine le_trans (Filter.liminf_le_liminf (Eventually.of_forall (fun n => hsum n))) ?_
    simp [← hA]
  -- **(k)** Letting `ε → 0` gives `H^s(B_t) ≤ t⁻¹ H^s(B_t)`.
  have h2 : μH[s] A ≤ t⁻¹ * μH[s] A := by
    set K : ℝ≥0∞ := t⁻¹ + ENNReal.ofReal (5 ^ s) * t⁻¹ with hK
    have hKtop : K ≠ ⊤ := by
      rw [hK]
      exact ENNReal.add_ne_top.mpr ⟨htinv_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top htinv_top⟩
    refine ENNReal.le_of_forall_pos_le_add ?_
    intro e he _
    set ee : ℝ≥0∞ := (e : ℝ≥0∞) / (K + 1) with hee
    have hK1 : K + 1 ≠ 0 := by positivity
    have hK1top : K + 1 ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hKtop, ENNReal.one_ne_top⟩
    have hee0 : ee ≠ 0 := by
      rw [hee]
      exact (ENNReal.div_ne_zero).mpr ⟨by exact_mod_cast he.ne', hK1top⟩
    have hkey := key ee hee0
    have hexp : t⁻¹ * (μH[s] A + ee) + ENNReal.ofReal (5 ^ s) * t⁻¹ * ee
        = t⁻¹ * μH[s] A + K * ee := by rw [hK]; ring
    rw [hexp] at hkey
    refine hkey.trans ?_
    have hfin : K * ee ≤ (e : ℝ≥0∞) :=
      calc K * ee ≤ (K + 1) * ee := by gcongr; exact le_self_add
        _ = (e : ℝ≥0∞) := by
            rw [hee]
            exact ENNReal.mul_div_cancel' (fun h => absurd h hK1) (fun h => absurd h hK1top)
    gcongr
  -- **(l)** Since `H^s(B_t) < ∞` and `t⁻¹ < 1`, this forces `H^s(B_t) = 0`.
  exact eq_zero_of_le_mul_self htinv hAfin h2

/-! ## (m): an auxiliary estimate for the main theorem -/

omit [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
/-- Every extended real number `> 1` exceeds `1 + 1/(n+1)` for some `n`. -/
lemma exists_nat_one_add_inv_lt {d : ℝ≥0∞} (hd : 1 < d) :
    ∃ n : ℕ, 1 + ((n : ℝ≥0∞) + 1)⁻¹ < d := by
  rcases eq_or_ne d ⊤ with rfl | hdtop
  · exact ⟨0, by norm_num⟩
  · have h1 : d - 1 ≠ 0 := by
      simp only [ne_eq, tsub_eq_zero_iff_le, not_le]
      exact hd
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt h1
    refine ⟨n, ?_⟩
    have h2 : ((n : ℝ≥0∞) + 1)⁻¹ ≤ (n : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.mpr le_self_add
    calc 1 + ((n : ℝ≥0∞) + 1)⁻¹ ≤ 1 + (n : ℝ≥0∞)⁻¹ := by gcongr
      _ < 1 + (d - 1) := ENNReal.add_lt_add_left ENNReal.one_ne_top hn
      _ = d := add_tsub_cancel_of_le hd.le

end

end HausdorffDensity
