/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MixedTruncationMaxLocality
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorSlotSmul
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PshConvexCone

/-!
# Positive linearity of mixed truncation limits in one slot

For PSH tuples that differ only in slot `i₀`, the mixed non-pluripolar
truncation-limit measure is positively linear in that slot:
`μ(s a + r b) = s μ(a) + r μ(b)` for `s, r > 0`, provided the `a`-measure does
not charge the poles of `b` and vice versa. These pole hypotheses cannot be
dropped: if `b ≡ ⊥` on an open set, the left side vanishes there while
`μ(a)` need not.

When `a` and `b` are bounded below by `t`, all three truncations at a level
below `(s + r) t` and `t` are the functions themselves, the common strict loci
agree, and bounded slot additivity and homogeneity of Bedford–Taylor limits give
the identity level by level (`mixedTruncationLimitMeasure_update_add_smul_of_le`).
In general, `s max(a,-m) + r max(b,-m)` is the maximum of `s a + r b` with a PSH
obstacle lying strictly below it where `a, b > -m`, so plurifine max-locality
transfers the bounded identity to `{a > -m, b > -m}` minus the poles of the other
slots. These sets exhaust `Ω` up to sets that the pole hypotheses and the pole
set vanishing make null for all three measures.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.MixedNonPluripolar

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
open FirstPass.MixedNonPluripolar
open MixedMongeAmpere

variable {n : ℕ}

/-- Multiplication by a nonnegative real distributes over `max` in `EReal`. -/
theorem ereal_coe_mul_max {s : ℝ} (hs : 0 ≤ s) (x y : EReal) :
    (s : EReal) * max x y = max ((s : EReal) * x) ((s : EReal) * y) :=
  Monotone.map_max (fun _ _ h => mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.mpr hs))

/-- A positive combination of two truncations is the maximum of the untruncated
combination and three competitors. Valid for all extended reals. -/
theorem mul_max_add_mul_max_eq {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) (x y κ : EReal) :
    (s : EReal) * max x κ + (r : EReal) * max y κ =
      max ((s : EReal) * x + (r : EReal) * y)
        (max (max ((s : EReal) * x + (r : EReal) * κ) ((s : EReal) * κ + (r : EReal) * y))
          ((s : EReal) * κ + (r : EReal) * κ)) := by
  rw [ereal_coe_mul_max hs, ereal_coe_mul_max hr, ← max_add_add_right, ← max_add_add_left,
    ← max_add_add_left]
  simp only [max_assoc]

/-- Where both entries exceed `t` and are finite, the competitors lie strictly below
the untruncated combination. -/
theorem max_competitors_lt {s r : ℝ} (hs : 0 < s) (hr : 0 < r) {x y : EReal} (t : ℝ)
    (hx : (t : EReal) < x) (hy : (t : EReal) < y) (hxt : x ≠ ⊤) (hyt : y ≠ ⊤) :
    max (max ((s : EReal) * x + (r : EReal) * t) ((s : EReal) * t + (r : EReal) * y))
      ((s : EReal) * t + (r : EReal) * t) < (s : EReal) * x + (r : EReal) * y := by
  lift x to ℝ using ⟨hxt, ne_bot_of_gt hx⟩
  lift y to ℝ using ⟨hyt, ne_bot_of_gt hy⟩
  rw [EReal.coe_lt_coe_iff] at hx hy
  norm_cast
  refine max_lt (max_lt ?_ ?_) ?_ <;> exact EReal.coe_lt_coe_iff.mpr (by nlinarith)

/-- Every extended real other than `⊥` exceeds some `-m`. -/
theorem exists_nat_neg_lt {x : EReal} (hx : x ≠ ⊥) :
    ∃ m : ℕ, ((-(m : ℝ) : ℝ) : EReal) < x := by
  obtain ⟨q, _, hq⟩ := EReal.exists_between_coe_real (bot_lt_iff_ne_bot.mpr hx)
  obtain ⟨m, hm⟩ := exists_nat_gt (-q)
  exact ⟨m, (EReal.coe_lt_coe_iff.mpr (by linarith)).trans hq⟩

/-- Replacing slot `i₀` of a PSH tuple by a PSH function gives a PSH tuple. -/
theorem plurisubharmonicOn_update {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → EReal} (i₀ : Fin n) {f g : ComplexModel n → EReal}
    (hg : ∀ i, PlurisubharmonicOn (Function.update u i₀ g i) Ω)
    (hf : PlurisubharmonicOn f Ω) : ∀ i, PlurisubharmonicOn (Function.update u i₀ f i) Ω := by
  intro i
  by_cases hi : i = i₀
  · subst hi; simpa using hf
  · simpa [Function.update_of_ne hi] using hg i

/-- **Max-locality in one slot.** Taking the maximum of slot `i₀` with a PSH obstacle
`g` does not change the truncation-limit measure where `g < f` and the other slots
are finite. -/
theorem mixedTruncationLimitMeasure_update_restrict_max {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → EReal} (i₀ : Fin n) {f g : ComplexModel n → EReal}
    (hf : ∀ i, PlurisubharmonicOn (Function.update u i₀ f i) Ω) (hg : PlurisubharmonicOn g Ω)
    (hfg : ∀ i, PlurisubharmonicOn (Function.update u i₀ (fun z => max (f z) (g z)) i) Ω) :
    (mixedTruncationLimitMeasure Ω (Function.update u i₀ fun z => max (f z) (g z)) hfg).restrict
        {z | z ∈ Ω ∧ g z < f z ∧ ∀ j, j ≠ i₀ → ⊥ < u j z} =
      (mixedTruncationLimitMeasure Ω (Function.update u i₀ f) hf).restrict
        {z | z ∈ Ω ∧ g z < f z ∧ ∀ j, j ≠ i₀ → ⊥ < u j z} := by
  classical
  set w : Fin n → ComplexModel n → EReal := Function.update (fun _ _ => ⊥) i₀ g with hw_def
  have hbot : PlurisubharmonicOn (fun _ : ComplexModel n => (⊥ : EReal)) Ω :=
    fun z _ => plurisubharmonicAt_const (⊥ : EReal) (by simp) z
  have hw : ∀ i, PlurisubharmonicOn (w i) Ω := by
    intro i
    by_cases hi : i = i₀
    · subst hi; simpa [hw_def] using hg
    · simpa [hw_def, Function.update_of_ne hi] using hbot
  have hmax : ∀ i, PlurisubharmonicOn (fun z => max (Function.update u i₀ f i z) (w i z)) Ω :=
    fun i => (hf i).max (hw i)
  have heq : (fun i z => max (Function.update u i₀ f i z) (w i z)) =
      Function.update u i₀ (fun z => max (f z) (g z)) := by
    funext i z
    by_cases hi : i = i₀
    · subst hi; simp [hw_def]
    · simp [hw_def, Function.update_of_ne hi]
  have hset : {z | z ∈ Ω ∧ ∀ i, w i z < Function.update u i₀ f i z} =
      {z | z ∈ Ω ∧ g z < f z ∧ ∀ j, j ≠ i₀ → ⊥ < u j z} := by
    ext z
    simp only [mem_ofPred_eq]
    refine and_congr_right fun _ => ⟨fun h => ⟨by simpa [hw_def] using h i₀,
      fun j hj => by simpa [hw_def, Function.update_of_ne hj] using h j⟩, fun h i => ?_⟩
    by_cases hi : i = i₀
    · subst hi; simpa [hw_def] using h.1
    · simpa [hw_def, Function.update_of_ne hi] using h.2 i hi
  have h := mixedTruncationLimitMeasure_restrict_max_eq hf hw hmax
  rw [hset, mixedTruncationLimitMeasure_congr hmax hfg
    (fun i z _ => congrFun (congrFun heq i) z)] at h
  exact h

/-- **Slot linearity for slots bounded below.** If `a` and `b` are bounded below by a
real constant everywhere, the truncation-limit measure is positively linear in slot
`i₀`; no pole hypothesis is needed. -/
theorem mixedTruncationLimitMeasure_update_add_smul_of_le {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → EReal} (i₀ : Fin n) {a b : ComplexModel n → EReal}
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (t : ℝ)
    (hat : ∀ z, (t : EReal) ≤ a z) (hbt : ∀ z, (t : EReal) ≤ b z)
    (hc : ∀ i, PlurisubharmonicOn
      (Function.update u i₀ (fun z => (s : EReal) * a z + (r : EReal) * b z) i) Ω)
    (ha : ∀ i, PlurisubharmonicOn (Function.update u i₀ a i) Ω)
    (hb : ∀ i, PlurisubharmonicOn (Function.update u i₀ b i) Ω) :
    mixedTruncationLimitMeasure Ω
        (Function.update u i₀ (fun z => (s : EReal) * a z + (r : EReal) * b z)) hc =
      ENNReal.ofReal s • mixedTruncationLimitMeasure Ω (Function.update u i₀ a) ha +
        ENNReal.ofReal r • mixedTruncationLimitMeasure Ω (Function.update u i₀ b) hb := by
  classical
  set c : ComplexModel n → EReal := fun z => (s : EReal) * a z + (r : EReal) * b z with hc_def
  have haf : PlurisubharmonicOn a Ω := by simpa using ha i₀
  have hbf : PlurisubharmonicOn b Ω := by simpa using hb i₀
  have hct : ∀ z, (((s + r) * t : ℝ) : EReal) ≤ c z := by
    intro z
    have h1 : ((s * t : ℝ) : EReal) ≤ (s : EReal) * a z := by
      rw [EReal.coe_mul]; exact mul_le_mul_of_nonneg_left (hat z) (EReal.coe_nonneg.mpr hs.le)
    have h2 : ((r * t : ℝ) : EReal) ≤ (r : EReal) * b z := by
      rw [EReal.coe_mul]; exact mul_le_mul_of_nonneg_left (hbt z) (EReal.coe_nonneg.mpr hr.le)
    calc (((s + r) * t : ℝ) : EReal) = ((s * t : ℝ) : EReal) + ((r * t : ℝ) : EReal) := by
          rw [← EReal.coe_add]; ring_nf
      _ ≤ _ := add_le_add h1 h2
  obtain ⟨K, hK⟩ := exists_nat_gt (max (-t) (-((s + r) * t)))
  set S : ℕ → Set (ComplexModel n) :=
    fun k => {z | z ∈ Ω ∧ ∀ j, j ≠ i₀ → ((-(k : ℝ) : ℝ) : EReal) < u j z} with hS
  have hlocus (f : ComplexModel n → EReal) (τ : ℝ) (hf : ∀ z, (τ : EReal) ≤ f z)
      (hτ : -(K : ℝ) < τ) (k : ℕ) (hk : K ≤ k) :
      commonStrictLocus Ω (Function.update u i₀ f) k = S k := by
    have hkτ : ((-(k : ℝ) : ℝ) : EReal) < (τ : EReal) := by
      have : (K : ℝ) ≤ k := Nat.cast_le.mpr hk
      exact EReal.coe_lt_coe_iff.mpr (by linarith)
    ext z
    simp only [commonStrictLocus, hS, mem_ofPred_eq]
    refine and_congr_right fun _ => ⟨fun h j hj => by simpa [Function.update_of_ne hj] using h j,
      fun h i => ?_⟩
    by_cases hi : i = i₀
    · subst hi; simpa using hkτ.trans_le (hf z)
    · simpa [Function.update_of_ne hi] using h i hi
  have hreal (f : ComplexModel n → EReal) (τ : ℝ) (hf : ∀ z, (τ : EReal) ≤ f z)
      (hτ : -(K : ℝ) < τ) (k : ℕ) (hk : K ≤ k) :
      ∀ i, EqOn (mixedTruncationReal (Function.update u i₀ f) k i)
        (Function.update (mixedTruncationReal u k) i₀ (fun z => (f z).toReal) i) Ω := by
    have hkτ : ((-(k : ℝ) : ℝ) : EReal) ≤ (τ : EReal) := by
      have : (K : ℝ) ≤ k := Nat.cast_le.mpr hk
      exact EReal.coe_le_coe_iff.mpr (by linarith)
    intro i z _
    by_cases hi : i = i₀
    · subst hi
      simp only [mixedTruncationReal, truncationReal, truncation, Function.update_self]
      rw [max_eq_left (hkτ.trans (hf z))]
    · simp [mixedTruncationReal, Function.update_of_ne hi]
  have hτa : -(K : ℝ) < t := by
    have := (le_max_left _ _).trans_lt hK; linarith
  have hτc : -(K : ℝ) < (s + r) * t := by
    have := (le_max_right _ _).trans_lt hK; linarith
  have hcreal : ∀ z ∈ Ω, (c z).toReal = s * (a z).toReal + r * (b z).toReal := by
    intro z hz
    obtain ⟨x, hx⟩ : ∃ x : ℝ, a z = x :=
      ⟨_, (EReal.coe_toReal (haf z hz).ne_top (ne_bot_of_le_ne_bot (EReal.coe_ne_bot t)
        (hat z))).symm⟩
    obtain ⟨y, hy⟩ : ∃ y : ℝ, b z = y :=
      ⟨_, (EReal.coe_toReal (hbf z hz).ne_top (ne_bot_of_le_ne_bot (EReal.coe_ne_bot t)
        (hbt z))).symm⟩
    simp only [hc_def, hx, hy, ← EReal.coe_mul, ← EReal.coe_add, EReal.toReal_coe]
  have hlevel (k : ℕ) (hk : K ≤ k) :
      mixedTruncationMeasure Ω (Function.update u i₀ c) hc k =
        ENNReal.ofReal s • mixedTruncationMeasure Ω (Function.update u i₀ a) ha k +
          ENNReal.ofReal r • mixedTruncationMeasure Ω (Function.update u i₀ b) hb k := by
    set v := mixedTruncationReal u k with hv
    have hbt' (w : Fin n → ComplexModel n → EReal) (hw : ∀ i, PlurisubharmonicOn (w i) Ω) :=
      BedfordTaylor.IsLocalMixedBedfordTaylorMeasure.isBTLimit
        (canonicalMixedBedfordTaylorMeasure_spec Ω _ (mixedTruncationReal_isLocallyBounded hw k))
    have hμc := ((hbt' _ hc).congr (hreal c _ hct hτc k hk)).congr (v :=
      Function.update v i₀ (fun z => (fun z => s * (a z).toReal) z + (fun z => r * (b z).toReal)
        z))
      (fun i z hz => by
        by_cases hi : i = i₀
        · subst hi; simpa using hcreal z hz
        · simp [Function.update_of_ne hi, hv])
    have hμa := (hbt' _ ha).congr (hreal a _ hat hτa k hk)
    have hμb := (hbt' _ hb).congr (hreal b _ hbt (by linarith) k hk)
    have hadd := BedfordTaylor.IsBTLimit.add_slot i₀ hμc
      (hμa.const_mul_slot i₀ hs.le) (hμb.const_mul_slot i₀ hr.le)
    unfold mixedTruncationMeasure
    rw [hlocus c _ hct hτc k hk, hlocus a _ hat hτa k hk, hlocus b _ hbt hτa k hk, hadd,
      Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul]
  have hrestr (f : ComplexModel n → EReal) (hf : ∀ i, PlurisubharmonicOn (Function.update u i₀ f
    i) Ω)
      (τ : ℝ) (hfτ : ∀ z, (τ : EReal) ≤ f z) (hτ : -(K : ℝ) < τ) (k : ℕ) (hk : K ≤ k) :
      (mixedTruncationLimitMeasure Ω (Function.update u i₀ f) hf).restrict (S k) =
        mixedTruncationMeasure Ω (Function.update u i₀ f) hf k := by
    rw [← hlocus f τ hfτ hτ k hk, mixedTruncationLimitMeasure_restrict_commonStrictLocus]
  have hpole (f : ComplexModel n → EReal) :
      componentPoleSet (Function.update u i₀ c) ⊆ componentPoleSet (Function.update u i₀ f) := by
    rintro z ⟨i, hi⟩
    by_cases h : i = i₀
    · subst h
      rw [Function.update_self] at hi
      have := hct z
      rw [hi, le_bot_iff] at this
      exact absurd this (EReal.coe_ne_bot _)
    · exact ⟨i, by simpa [Function.update_of_ne h] using hi⟩
  symm
  refine mixedTruncationLimitMeasure_unique hc ?_ ?_ ?_
  · rw [add_apply, smul_apply, smul_apply,
      mixedTruncationLimitMeasure_compl, mixedTruncationLimitMeasure_compl, smul_zero, smul_zero,
      add_zero]
  · rw [add_apply, smul_apply, smul_apply,
      measure_mono_null (hpole a) (mixedTruncationLimitMeasure_poleSet ha),
      measure_mono_null (hpole b) (mixedTruncationLimitMeasure_poleSet hb), smul_zero, smul_zero,
      add_zero]
  · intro k
    have hkk' : k ≤ max k K := le_max_left _ _
    have hK' : K ≤ max k K := le_max_right _ _
    rw [← Measure.restrict_restrict_of_subset (commonStrictLocus_mono Ω _ hkk'),
      hlocus c _ hct hτc _ hK', Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul,
      hrestr a ha _ hat hτa _ hK', hrestr b hb _ hbt hτa _ hK', ← hlevel _ hK',
      mixedTruncationMeasure_restrict hc hkk']

/-- **One-slot positive linearity of mixed truncation limits.** The pole hypotheses
`hpa`, `hpb` (each measure does not charge the poles of the other slot function)
are necessary. -/
theorem mixedTruncationLimitMeasure_update_add_smul {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → EReal} (i₀ : Fin n) {a b : ComplexModel n → EReal}
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (hc : ∀ i, PlurisubharmonicOn
      (Function.update u i₀ (fun z => (s : EReal) * a z + (r : EReal) * b z) i) Ω)
    (ha : ∀ i, PlurisubharmonicOn (Function.update u i₀ a i) Ω)
    (hb : ∀ i, PlurisubharmonicOn (Function.update u i₀ b i) Ω)
    (hpa : mixedTruncationLimitMeasure Ω (Function.update u i₀ b) hb {z | a z = ⊥} = 0)
    (hpb : mixedTruncationLimitMeasure Ω (Function.update u i₀ a) ha {z | b z = ⊥} = 0) :
    mixedTruncationLimitMeasure Ω
        (Function.update u i₀ (fun z => (s : EReal) * a z + (r : EReal) * b z)) hc =
      ENNReal.ofReal s • mixedTruncationLimitMeasure Ω (Function.update u i₀ a) ha +
        ENNReal.ofReal r • mixedTruncationLimitMeasure Ω (Function.update u i₀ b) hb := by
  classical
  set c : ComplexModel n → EReal := fun z => (s : EReal) * a z + (r : EReal) * b z with hc_def
  have haf : PlurisubharmonicOn a Ω := by simpa using ha i₀
  have hbf : PlurisubharmonicOn b Ω := by simpa using hb i₀
  have hcf : PlurisubharmonicOn c Ω := by simpa using hc i₀
  have hconst (e : EReal) (he : e ≠ ⊤) : PlurisubharmonicOn (fun _ : ComplexModel n => e) Ω :=
    fun z _ => plurisubharmonicAt_const e he z
  set E : ℕ → Set (ComplexModel n) := fun m => {z | z ∈ Ω ∧
    ((-(m : ℝ) : ℝ) : EReal) < a z ∧ ((-(m : ℝ) : ℝ) : EReal) < b z ∧
      ∀ j, j ≠ i₀ → ⊥ < u j z} with hE
  set ν := ENNReal.ofReal s • mixedTruncationLimitMeasure Ω (Function.update u i₀ a) ha +
    ENNReal.ofReal r • mixedTruncationLimitMeasure Ω (Function.update u i₀ b) hb with hν
  have hloc (m : ℕ) : (mixedTruncationLimitMeasure Ω (Function.update u i₀ c) hc).restrict (E m) =
      ν.restrict (E m) := by
    set t : ℝ := -(m : ℝ) with ht
    have htT : (t : EReal) ≠ ⊤ := EReal.coe_ne_top _
    have hmulT (p : ℝ) : (p : EReal) * (t : EReal) ≠ ⊤ := by
      rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
    set A : ComplexModel n → EReal := fun z => max (a z) (t : EReal) with hA_def
    set B : ComplexModel n → EReal := fun z => max (b z) (t : EReal) with hB_def
    set W : ComplexModel n → EReal := fun z =>
      max (max ((s : EReal) * a z + (r : EReal) * t) ((s : EReal) * t + (r : EReal) * b z))
        ((s : EReal) * t + (r : EReal) * t) with hW_def
    have hAf : PlurisubharmonicOn A Ω := haf.max (hconst _ htT)
    have hBf : PlurisubharmonicOn B Ω := hbf.max (hconst _ htT)
    have hsumT : (s : EReal) * t + (r : EReal) * t ≠ ⊤ := by
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]; exact EReal.coe_ne_top _
    have hWf : PlurisubharmonicOn W Ω :=
      (((haf.const_mul hs).add (hconst _ (hmulT r))).max
        ((hconst _ (hmulT s)).add (hbf.const_mul hr))).max
        (hconst _ hsumT)
    have hA := plurisubharmonicOn_update i₀ ha hAf
    have hB := plurisubharmonicOn_update i₀ hb hBf
    have hT := plurisubharmonicOn_update i₀ hc ((hAf.const_mul hs).add (hBf.const_mul hr))
    have hbdd := mixedTruncationLimitMeasure_update_add_smul_of_le i₀ hs hr t
      (fun z => le_max_right _ _) (fun z => le_max_right _ _) hT hA hB
    have hEA : (mixedTruncationLimitMeasure Ω (Function.update u i₀ A) hA).restrict (E m) =
        (mixedTruncationLimitMeasure Ω (Function.update u i₀ a) ha).restrict (E m) := by
      have h := mixedTruncationLimitMeasure_update_restrict_max i₀ ha (hconst _ htT) hA
      have hsub : E m ⊆ {z | z ∈ Ω ∧ (t : EReal) < a z ∧ ∀ j, j ≠ i₀ → ⊥ < u j z} :=
        fun z hz => ⟨hz.1, hz.2.1, hz.2.2.2⟩
      rw [← Measure.restrict_restrict_of_subset hsub, h, Measure.restrict_restrict_of_subset hsub]
    have hEB : (mixedTruncationLimitMeasure Ω (Function.update u i₀ B) hB).restrict (E m) =
        (mixedTruncationLimitMeasure Ω (Function.update u i₀ b) hb).restrict (E m) := by
      have h := mixedTruncationLimitMeasure_update_restrict_max i₀ hb (hconst _ htT) hB
      have hsub : E m ⊆ {z | z ∈ Ω ∧ (t : EReal) < b z ∧ ∀ j, j ≠ i₀ → ⊥ < u j z} :=
        fun z hz => ⟨hz.1, hz.2.2.1, hz.2.2.2⟩
      rw [← Measure.restrict_restrict_of_subset hsub, h, Measure.restrict_restrict_of_subset hsub]
    have hmaxW := plurisubharmonicOn_update i₀ hc (hcf.max hWf)
    have hET : (mixedTruncationLimitMeasure Ω
        (Function.update u i₀ (fun z => (s : EReal) * A z + (r : EReal) * B z)) hT).restrict
          (E m) = (mixedTruncationLimitMeasure Ω (Function.update u i₀ c) hc).restrict (E m) := by
      have hcongr := mixedTruncationLimitMeasure_congr hT hmaxW (fun i z _ => by
        by_cases hi : i = i₀
        · subst hi
          simp only [Function.update_self, hA_def, hB_def, hW_def, hc_def]
          exact mul_max_add_mul_max_eq hs.le hr.le _ _ _
        · simp [Function.update_of_ne hi])
      have h := mixedTruncationLimitMeasure_update_restrict_max i₀ hc hWf hmaxW
      have hsub : E m ⊆ {z | z ∈ Ω ∧ W z < c z ∧ ∀ j, j ≠ i₀ → ⊥ < u j z} :=
        fun z hz => ⟨hz.1, max_competitors_lt hs hr t hz.2.1 hz.2.2.1 (haf z hz.1).ne_top
          (hbf z hz.1).ne_top, hz.2.2.2⟩
      rw [hcongr, ← Measure.restrict_restrict_of_subset hsub, h,
        Measure.restrict_restrict_of_subset hsub]
    rw [← hET, hbdd, Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul, hEA, hEB,
      hν, Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul]
  have hmem : ∀ z ∈ Ω, (∀ j, j ≠ i₀ → u j z ≠ ⊥) → a z ≠ ⊥ → b z ≠ ⊥ → z ∈ ⋃ m, E m := by
    intro z hz hu ha' hb'
    obtain ⟨m₁, hm₁⟩ := exists_nat_neg_lt ha'
    obtain ⟨m₂, hm₂⟩ := exists_nat_neg_lt hb'
    have h₁ : (((-((m₁ + m₂ : ℕ) : ℝ)) : ℝ) : EReal) ≤ ((-(m₁ : ℝ) : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.mpr (by push_cast; linarith [(Nat.cast_nonneg m₂ : (0 : ℝ) ≤ m₂)])
    have h₂ : (((-((m₁ + m₂ : ℕ) : ℝ)) : ℝ) : EReal) ≤ ((-(m₂ : ℝ) : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.mpr (by push_cast; linarith [(Nat.cast_nonneg m₁ : (0 : ℝ) ≤ m₁)])
    exact mem_iUnion.mpr ⟨m₁ + m₂, hz, h₁.trans_lt hm₁, h₂.trans_lt hm₂,
      fun j hj => bot_lt_iff_ne_bot.mpr (hu j hj)⟩
  have hcompl (μ : Measure (ComplexModel n)) (X Y : Set (ComplexModel n))
      (hX : μ X = 0) (hY : μ Y = 0) (hΩ : μ (Ω : Set (ComplexModel n))ᶜ = 0)
      (hXY : ∀ z ∈ Ω, z ∉ X → z ∉ Y → z ∈ ⋃ m, E m) : μ.restrict (⋃ m, E m) = μ := by
    refine Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr ?_)
    refine measure_mono_null (fun z hz => ?_) (measure_union_null (measure_union_null hΩ hX) hY)
    by_contra hcon
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
    exact hz (hXY z hcon.1.1 hcon.1.2 hcon.2)
  have hpoleU (f : ComplexModel n → EReal) (z : ComplexModel n)
      (hz : z ∉ componentPoleSet (Function.update u i₀ f)) :
      (∀ j, j ≠ i₀ → u j z ≠ ⊥) ∧ f z ≠ ⊥ :=
    ⟨fun j hj h => hz ⟨j, by simpa [Function.update_of_ne hj] using h⟩,
      fun h => hz ⟨i₀, by simpa using h⟩⟩
  have hcμ := hcompl _ (componentPoleSet (Function.update u i₀ c)) ∅
    (mixedTruncationLimitMeasure_poleSet hc) measure_empty (mixedTruncationLimitMeasure_compl hc)
    (fun z hz hX _ => by
      obtain ⟨hu, hcz⟩ := hpoleU c z hX
      refine hmem z hz hu (fun h => hcz ?_) (fun h => hcz ?_)
      · simp [hc_def, h, EReal.mul_bot_of_pos (EReal.coe_pos.mpr hs)]
      · simp [hc_def, h, EReal.mul_bot_of_pos (EReal.coe_pos.mpr hr)])
  have haμ := hcompl _ (componentPoleSet (Function.update u i₀ a)) {z | b z = ⊥}
    (mixedTruncationLimitMeasure_poleSet ha) hpb (mixedTruncationLimitMeasure_compl ha)
    (fun z hz hX hY => (hpoleU a z hX).elim fun hu haz => hmem z hz hu haz hY)
  have hbμ := hcompl _ (componentPoleSet (Function.update u i₀ b)) {z | a z = ⊥}
    (mixedTruncationLimitMeasure_poleSet hb) hpa (mixedTruncationLimitMeasure_compl hb)
    (fun z hz hX hY => (hpoleU b z hX).elim fun hu hbz => hmem z hz hu hY hbz)
  have key := Measure.restrict_iUnion_congr.mpr hloc
  rw [hcμ, hν, Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul, haμ,
    hbμ] at key
  exact key

end SGPT.Foundations.Analysis.Pending.MixedNonPluripolar
