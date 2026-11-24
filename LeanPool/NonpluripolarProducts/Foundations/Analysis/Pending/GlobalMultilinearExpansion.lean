/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalDiagonalScaling

/-!
# Multilinear expansion of diagonal global mixed measures

For a nonempty finite family of closed real `(1,1)`-forms `α i` with raw `α i`-PSH
nondegenerate quasi-PSH potentials `f i`, and positive weights `w i`, the positive
combination `∑ w i f i` is `(∑ w i • α i)`-PSH, and the diagonal global mixed
measure of the combination expands as
`∑_{g : Fin n → T} (∏ j, w (g j)) • μ(α ∘ g, f ∘ g)`.

The proof applies one-slot positive linearity (`Pending.GlobalSlotLinear`) one
summand at a time in a single slot, and then one slot at a time. The pole set of
the combination is contained in the union of the pole sets of the `f i`, hence is
null for every global mixed measure.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.GlobalMultilinearExpansion

open FirstPass FirstPass.PositiveClasses
open GlobalNonPluripolar GlobalDiagonalScaling

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {ι : Type*} [DecidableEq ι]

/-- The positive combination of forms. -/
def sumForm (T : Finset ι) (w : ι → ℝ) (α : ι → ClosedRealOneOneForm n M) :
    ClosedRealOneOneForm n M :=
  ∑ i ∈ T, w i • α i

/-- The positive combination of potentials. -/
def sumPot (T : Finset ι) (w : ι → ℝ) (f : ι → M → EReal) : M → EReal :=
  fun p => ∑ i ∈ T, ((w i : ℝ) : EReal) * f i p

theorem ereal_half_add_half {c : ℝ} (hc : 0 < c) (x : EReal) :
    ((c / 2 : ℝ) : EReal) * x + ((c / 2 : ℝ) : EReal) * x = (c : EReal) * x := by
  have hc2 : 0 < c / 2 := half_pos hc
  induction x using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos hc2, EReal.coe_mul_bot_of_pos hc]
  | top => simp [EReal.coe_mul_top_of_pos hc2, EReal.coe_mul_top_of_pos hc]
  | coe x =>
    simp only [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_eq_coe_iff]
    ring

omit [DecidableEq ι] in
theorem sumForm_singleton (w : ι → ℝ) (α : ι → ClosedRealOneOneForm n M) (a : ι) :
    sumForm {a} w α = w a • α a := by
  simp [sumForm]

omit [TopologicalSpace M] [DecidableEq ι] in
theorem sumPot_singleton (w : ι → ℝ) (f : ι → M → EReal) (a : ι) :
    sumPot {a} w f = fun p => ((w a : ℝ) : EReal) * f a p := by
  funext p
  simp [sumPot]

omit [DecidableEq ι] in
theorem sumForm_cons (w : ι → ℝ) (α : ι → ClosedRealOneOneForm n M) {a : ι} {s : Finset ι}
    (ha : a ∉ s) : sumForm (Finset.cons a s ha) w α = w a • α a + (1 : ℝ) • sumForm s w α := by
  rw [sumForm, sumForm, Finset.sum_cons, one_smul]

omit [TopologicalSpace M] [DecidableEq ι] in
theorem sumPot_cons (w : ι → ℝ) (f : ι → M → EReal) {a : ι} {s : Finset ι} (ha : a ∉ s) :
    sumPot (Finset.cons a s ha) w f =
      fun p => ((w a : ℝ) : EReal) * f a p + ((1 : ℝ) : EReal) * sumPot s w f p := by
  funext p
  simp only [sumPot, Finset.sum_cons, EReal.coe_one, one_mul]

theorem thetaPlurisubharmonic_smul {γ : ClosedRealOneOneForm n M} {g : M → EReal} {c : ℝ}
    (hc : 0 < c) (hg : ThetaPlurisubharmonic γ.val g) :
    ThetaPlurisubharmonic (c • γ).val (fun p => (c : EReal) * g p) := by
  have h := thetaPlurisubharmonic_add_smul (half_pos hc) (half_pos hc) hg hg
  have eθ : (c / 2) • γ + (c / 2) • γ = c • γ := by rw [← add_smul, add_halves]
  have eg : (fun p => ((c / 2 : ℝ) : EReal) * g p + ((c / 2 : ℝ) : EReal) * g p) =
      fun p => (c : EReal) * g p := funext fun p => ereal_half_add_half hc (g p)
  rwa [eθ, eg] at h

omit [DecidableEq ι] in
/-- **Positive combinations of theta-PSH potentials.** -/
theorem thetaPlurisubharmonic_sumPot {T : Finset ι} (hT : T.Nonempty) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) {α : ι → ClosedRealOneOneForm n M} {f : ι → M → EReal}
    (hf : ∀ i, ThetaPlurisubharmonic (α i).val (f i)) :
    ThetaPlurisubharmonic (sumForm T w α).val (sumPot T w f) := by
  induction hT using Finset.Nonempty.cons_induction with
  | singleton a =>
    rw [sumForm_singleton, sumPot_singleton]
    exact thetaPlurisubharmonic_smul (hw a) (hf a)
  | cons a s ha hs ih =>
    rw [sumForm_cons, sumPot_cons]
    exact thetaPlurisubharmonic_add_smul (hw a) one_pos (hf a) ih

omit [TopologicalSpace M] [DecidableEq ι] in
/-- A pole of a positive combination is a pole of one of its terms. -/
theorem exists_eq_bot_of_sumPot_eq_bot {T : Finset ι} {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    {f : ι → M → EReal} {p : M} (h : sumPot T w f p = ⊥) : ∃ i ∈ T, f i p = ⊥ := by
  induction T using Finset.cons_induction with
  | empty => simp [sumPot] at h
  | cons a s ha ih =>
    have h' : ((w a : ℝ) : EReal) * f a p + sumPot s w f p = ⊥ := by
      simp only [sumPot, Finset.sum_cons] at h
      exact h
    rcases EReal.add_eq_bot_iff.mp h' with h1 | h1
    · refine ⟨a, Finset.mem_cons_self a s, ?_⟩
      induction hfa : f a p using EReal.rec with
      | bot => rfl
      | top => rw [hfa, EReal.coe_mul_top_of_pos (hw a)] at h1; exact absurd h1 (by simp)
      | coe x => rw [hfa, ← EReal.coe_mul] at h1; exact absurd h1 (EReal.coe_ne_bot _)
    · obtain ⟨i, hi, hfi⟩ := ih h1
      exact ⟨i, Finset.mem_cons.mpr (Or.inr hi), hfi⟩

omit [TopologicalSpace M] [DecidableEq ι] in
theorem sumPot_poles_subset {T : Finset ι} {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    {f : ι → M → EReal} : {p | sumPot T w f p = ⊥} ⊆ ⋃ i ∈ T, {p | f i p = ⊥} := by
  intro p hp
  obtain ⟨i, hi, hfi⟩ := exists_eq_bot_of_sumPot_eq_bot hw hp
  exact Set.mem_biUnion (x := i) hi hfi

/-- Update one slot of a tuple that is theta-PSH away from that slot. -/
theorem update_thetaPlurisubharmonic {F : Fin n → ClosedRealOneOneForm n M}
    {P : Fin n → M → EReal} {j : Fin n}
    (hFP : ∀ k, k ≠ j → ThetaPlurisubharmonic (F k).val (P k))
    {γ : ClosedRealOneOneForm n M} {g : M → EReal} (hg : ThetaPlurisubharmonic γ.val g) :
    ∀ k, ThetaPlurisubharmonic (Function.update F j γ k).val (Function.update P j g k) := by
  intro k
  by_cases hk : k = j
  · subst hk
    simpa only [Function.update_self] using hg
  · simpa only [Function.update_of_ne hk] using hFP k hk

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [DecidableEq ι] in
/-- **Poles of positive combinations are globally null.** -/
theorem globalMixedMeasure_sumPot_pole_null {θ : Fin n → ClosedRealOneOneForm n M}
    {u : Fin n → M → EReal} (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    {T : Finset ι} {w : ι → ℝ} (hw : ∀ i, 0 < w i) {f : ι → M → EReal}
    (hq : ∀ i, IsGlobalQuasiPshPotential (n := n) (f i)) :
    globalMixedMeasure θ u hu {p | sumPot T w f p = ⊥} = 0 :=
  measure_mono_null (sumPot_poles_subset hw)
    ((measure_biUnion_null_iff T.countable_toSet).mpr fun i _ =>
      globalMixedMeasure_pole_null_of_quasiPsh hu (hq i))

/-- One-slot positive homogeneity. -/
theorem globalMixedMeasure_update_smul (j : Fin n) {F : Fin n → ClosedRealOneOneForm n M}
    {P : Fin n → M → EReal} (hFP : ∀ k, k ≠ j → ThetaPlurisubharmonic (F k).val (P k))
    {c : ℝ} (hc : 0 < c) {γ : ClosedRealOneOneForm n M} {g : M → EReal}
    (hg : ThetaPlurisubharmonic γ.val g) (hgq : IsGlobalQuasiPshPotential (n := n) g) :
    globalMixedMeasure (Function.update F j (c • γ))
        (Function.update P j (fun p => (c : EReal) * g p))
        (update_thetaPlurisubharmonic hFP (thetaPlurisubharmonic_smul hc hg)) =
      ENNReal.ofReal c • globalMixedMeasure (Function.update F j γ) (Function.update P j g)
        (update_thetaPlurisubharmonic hFP hg) := by
  have hc2 : 0 < c / 2 := half_pos hc
  have hθ : Function.update F j (c • γ) j = (c / 2) • γ + (c / 2) • γ := by
    rw [Function.update_self, ← add_smul, add_halves]
  have eg : (fun p => ((c / 2 : ℝ) : EReal) * g p + ((c / 2 : ℝ) : EReal) * g p) =
      fun p => (c : EReal) * g p := funext fun p => ereal_half_add_half hc (g p)
  have hcomb : ∀ k, ThetaPlurisubharmonic (Function.update F j (c • γ) k).val
      (Function.update P j (fun p => ((c / 2 : ℝ) : EReal) * g p +
        ((c / 2 : ℝ) : EReal) * g p) k) := by
    rw [eg]; exact update_thetaPlurisubharmonic hFP (thetaPlurisubharmonic_smul hc hg)
  have eF : Function.update (Function.update F j (c • γ)) j γ = Function.update F j γ :=
    Function.update_idem _ _ _
  have ha : ∀ k, ThetaPlurisubharmonic
      (Function.update (Function.update F j (c • γ)) j γ k).val (Function.update P j g k) := by
    rw [eF]; exact update_thetaPlurisubharmonic hFP hg
  have hpole := globalMixedMeasure_pole_null_of_quasiPsh ha hgq
  have hlin := GlobalSlotLinear.globalMixedMeasure_update_add_smul j hc2 hc2 hθ hcomb ha ha
    hpole hpole
  rw [globalMixedMeasure_congr rfl (congrArg (Function.update P j) eg.symm) _ hcomb, hlin,
    ← add_smul, ← ENNReal.ofReal_add hc2.le hc2.le, add_halves]
  exact congrArg _ (globalMixedMeasure_congr eF rfl _ _)

omit [DecidableEq ι] in
/-- **One-slot finite positive linearity.** -/
theorem globalMixedMeasure_update_sum (j : Fin n) {F : Fin n → ClosedRealOneOneForm n M}
    {P : Fin n → M → EReal} (hFP : ∀ k, k ≠ j → ThetaPlurisubharmonic (F k).val (P k))
    {T : Finset ι} (hT : T.Nonempty) {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    {α : ι → ClosedRealOneOneForm n M} {f : ι → M → EReal}
    (hf : ∀ i, ThetaPlurisubharmonic (α i).val (f i))
    (hq : ∀ i, IsGlobalQuasiPshPotential (n := n) (f i)) :
    globalMixedMeasure (Function.update F j (sumForm T w α)) (Function.update P j (sumPot T w f))
        (update_thetaPlurisubharmonic hFP (thetaPlurisubharmonic_sumPot hT hw hf)) =
      ∑ i ∈ T, ENNReal.ofReal (w i) •
        globalMixedMeasure (Function.update F j (α i)) (Function.update P j (f i))
          (update_thetaPlurisubharmonic hFP (hf i)) := by
  induction hT using Finset.Nonempty.cons_induction with
  | singleton a =>
    rw [Finset.sum_singleton,
      globalMixedMeasure_congr (congrArg (Function.update F j) (sumForm_singleton w α a))
        (congrArg (Function.update P j) (sumPot_singleton w f a)) _
        (update_thetaPlurisubharmonic hFP (thetaPlurisubharmonic_smul (hw a) (hf a)))]
    exact globalMixedMeasure_update_smul j hFP (hw a) (hf a) (hq a)
  | cons a s ha hs ih =>
    set θ := Function.update F j (sumForm (Finset.cons a s ha) w α) with hθdef
    have hθ : θ j = w a • α a + (1 : ℝ) • sumForm s w α := by
      rw [hθdef, Function.update_self, sumForm_cons]
    have hcomb : ∀ k, ThetaPlurisubharmonic (θ k).val
        (Function.update P j (fun p => ((w a : ℝ) : EReal) * f a p +
          ((1 : ℝ) : EReal) * sumPot s w f p) k) := by
      rw [← sumPot_cons w f ha]
      exact update_thetaPlurisubharmonic hFP (thetaPlurisubharmonic_sumPot
        (Finset.cons_nonempty ha) hw hf)
    have eA : Function.update θ j (α a) = Function.update F j (α a) := Function.update_idem _ _ _
    have eB : Function.update θ j (sumForm s w α) = Function.update F j (sumForm s w α) :=
      Function.update_idem _ _ _
    have hA : ∀ k, ThetaPlurisubharmonic (Function.update θ j (α a) k).val
        (Function.update P j (f a) k) := by
      rw [eA]; exact update_thetaPlurisubharmonic hFP (hf a)
    have hB : ∀ k, ThetaPlurisubharmonic (Function.update θ j (sumForm s w α) k).val
        (Function.update P j (sumPot s w f) k) := by
      rw [eB]; exact update_thetaPlurisubharmonic hFP (thetaPlurisubharmonic_sumPot hs hw hf)
    have hlin := GlobalSlotLinear.globalMixedMeasure_update_add_smul j (hw a) one_pos hθ hcomb
      hA hB (globalMixedMeasure_pole_null_of_quasiPsh hB (hq a))
      (globalMixedMeasure_sumPot_pole_null hA hw hq)
    rw [globalMixedMeasure_congr rfl (congrArg (Function.update P j) (sumPot_cons w f ha)) _
      hcomb, hlin, ENNReal.ofReal_one, one_smul, Finset.sum_cons,
      globalMixedMeasure_congr eA rfl hA (update_thetaPlurisubharmonic hFP (hf a)),
      globalMixedMeasure_congr eB rfl hB
        (update_thetaPlurisubharmonic hFP (thetaPlurisubharmonic_sumPot hs hw hf)), ih]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [DecidableEq ι] in
/-- Reindexing a sum over a box with a singleton factor in slot `k`, expanded in that
slot. -/
theorem sum_piFinset_update_sum {β : Type*} [AddCommMonoid β] (A : Fin n → Finset ι)
    (k : Fin n) {i₀ : ι} (hA : A k = {i₀}) (T : Finset ι) (G : (Fin n → ι) → β) :
    ∑ g ∈ Fintype.piFinset A, ∑ i ∈ T, G (Function.update g k i) =
      ∑ g ∈ Fintype.piFinset (Function.update A k T), G g := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun q => Function.update q.1 k q.2)
    (fun g => (Function.update g k i₀, g k)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨g, i⟩ hq
    rw [Finset.mem_product, Fintype.mem_piFinset] at hq
    rw [Fintype.mem_piFinset]
    intro k'
    by_cases hk : k' = k
    · subst hk; simpa using hq.2
    · simpa [Function.update_of_ne hk] using hq.1 k'
  · intro g hg
    rw [Fintype.mem_piFinset] at hg
    rw [Finset.mem_product, Fintype.mem_piFinset]
    refine ⟨fun k' => ?_, by simpa using hg k⟩
    by_cases hk : k' = k
    · subst hk; simp [hA]
    · simpa [Function.update_of_ne hk] using hg k'
  · rintro ⟨g, i⟩ hq
    rw [Finset.mem_product, Fintype.mem_piFinset] at hq
    have hgk : g k = i₀ := by simpa [hA] using hq.1 k
    simp only [Function.update_idem, Function.update_self, Prod.mk.injEq, and_true]
    rw [← hgk, Function.update_eq_self]
  · intro g _
    simp
  · intro q _
    rfl

/-- The tuple whose first `m` slots follow `g` through `a`, the others being `s`. -/
def slotTuple {β : Type*} (m : ℕ) (g : Fin n → ι) (a : ι → β) (s : β) : Fin n → β :=
  fun k => if (k : ℕ) < m then a (g k) else s

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [DecidableEq ι] in
theorem slotTuple_self {β : Type*} {m : ℕ} (hm : m < n) (g : Fin n → ι) (a : ι → β) (s : β) :
    Function.update (slotTuple m g a s) ⟨m, hm⟩ s = slotTuple m g a s :=
  Function.update_eq_self_iff.mpr (by simp [slotTuple])

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [DecidableEq ι] in
theorem update_slotTuple {β : Type*} {m : ℕ} (hm : m < n) (g : Fin n → ι) (a : ι → β)
    (s : β) (i : ι) :
    Function.update (slotTuple m g a s) ⟨m, hm⟩ (a i) =
      slotTuple (m + 1) (Function.update g ⟨m, hm⟩ i) a s := by
  funext k
  by_cases hk : k = ⟨m, hm⟩
  · subst hk; simp [slotTuple]
  · have hk' : (k : ℕ) ≠ m := fun h => hk (Fin.ext h)
    rw [Function.update_of_ne hk]
    simp only [slotTuple, Function.update_of_ne hk]
    split_ifs <;> first | rfl | omega

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [DecidableEq ι] in
theorem slotTuple_thetaPlurisubharmonic (m : ℕ) (g : Fin n → ι) {T : Finset ι}
    (hT : T.Nonempty) {w : ι → ℝ} (hw : ∀ i, 0 < w i) {α : ι → ClosedRealOneOneForm n M}
    {f : ι → M → EReal} (hf : ∀ i, ThetaPlurisubharmonic (α i).val (f i)) :
    ∀ k, ThetaPlurisubharmonic (slotTuple m g α (sumForm T w α) k).val
      (slotTuple m g f (sumPot T w f) k) := by
  intro k
  by_cases hk : (k : ℕ) < m
  · simpa only [slotTuple, hk, ite_true] using hf (g k)
  · simpa only [slotTuple, hk, ite_false] using thetaPlurisubharmonic_sumPot hT hw hf

omit [DecidableEq ι] in
/-- **Multilinear expansion of the diagonal global mixed measure.** -/
theorem globalMixedMeasure_diagonal_sumPot {T : Finset ι} (hT : T.Nonempty) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) {α : ι → ClosedRealOneOneForm n M} {f : ι → M → EReal}
    (hf : ∀ i, ThetaPlurisubharmonic (α i).val (f i))
    (hq : ∀ i, IsGlobalQuasiPshPotential (n := n) (f i)) :
    globalMixedMeasure (fun _ => sumForm T w α) (fun _ => sumPot T w f)
        (fun _ => thetaPlurisubharmonic_sumPot hT hw hf) =
      ∑ g ∈ Fintype.piFinset (fun _ : Fin n => T),
        ENNReal.ofReal (∏ j, w (g j)) •
          globalMixedMeasure (fun j => α (g j)) (fun j => f (g j)) (fun j => hf (g j)) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hT
  let A : ℕ → Fin n → Finset ι := fun m k => if (k : ℕ) < m then T else {i₀}
  let c : ℕ → (Fin n → ι) → Fin n → ℝ := fun m g k => if (k : ℕ) < m then w (g k) else 1
  have hc0 : ∀ m g, 0 ≤ ∏ k, c m g k := fun m g =>
    Finset.prod_nonneg fun k _ => by
      simp only [c]; split_ifs
      · exact (hw _).le
      · exact zero_le_one
  have claim : ∀ m, m ≤ n →
      globalMixedMeasure (fun _ => sumForm T w α) (fun _ => sumPot T w f)
          (fun _ => thetaPlurisubharmonic_sumPot ⟨i₀, hi₀⟩ hw hf) =
        ∑ g ∈ Fintype.piFinset (A m), ENNReal.ofReal (∏ k, c m g k) •
          globalMixedMeasure (slotTuple m g α (sumForm T w α)) (slotTuple m g f (sumPot T w f))
            (slotTuple_thetaPlurisubharmonic m g ⟨i₀, hi₀⟩ hw hf) := by
    intro m
    induction m with
    | zero =>
      intro _
      have hA : A 0 = fun _ => ({i₀} : Finset ι) := by funext k; simp [A]
      rw [hA, Fintype.piFinset_singleton (fun _ : Fin n => i₀), Finset.sum_singleton]
      have hc : ∏ k, c 0 (fun _ => i₀) k = 1 := by simp [c]
      rw [hc, ENNReal.ofReal_one, one_smul]
      exact globalMixedMeasure_congr (by funext k; simp [slotTuple])
        (by funext k; simp [slotTuple]) _ _
    | succ m ih =>
      intro hm
      have hmn : m < n := hm
      set k : Fin n := ⟨m, hmn⟩ with hkdef
      rw [ih (Nat.le_of_succ_le hm)]
      have hAk : A m k = {i₀} := by simp [A, k]
      have hA1 : A (m + 1) = Function.update (A m) k T := by
        funext k'
        by_cases hk : k' = k
        · subst hk; simp [A, k]
        · have hk' : (k' : ℕ) ≠ m := fun h => hk (Fin.ext h)
          rw [Function.update_of_ne hk]
          simp only [A]
          split_ifs <;> first | rfl | omega
      rw [hA1, ← sum_piFinset_update_sum (A m) k hAk T]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [Fintype.mem_piFinset] at hg
      have hgk : g k = i₀ := by simpa [hAk] using hg k
      have hFP : ∀ k', k' ≠ k → ThetaPlurisubharmonic
          (slotTuple m g α (sumForm T w α) k').val (slotTuple m g f (sumPot T w f) k') :=
        fun k' _ => slotTuple_thetaPlurisubharmonic m g ⟨i₀, hi₀⟩ hw hf k'
      have hexp := globalMixedMeasure_update_sum k hFP ⟨i₀, hi₀⟩ hw hf hq
      rw [← globalMixedMeasure_congr (slotTuple_self hmn g α _) (slotTuple_self hmn g f _)
        (update_thetaPlurisubharmonic hFP (thetaPlurisubharmonic_sumPot ⟨i₀, hi₀⟩ hw hf))
        (slotTuple_thetaPlurisubharmonic m g ⟨i₀, hi₀⟩ hw hf), hexp, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← ENNReal.ofReal_mul (hc0 m g)]
      have hprod : (∏ k', c m g k') * w i = ∏ k', c (m + 1) (Function.update g k i) k' := by
        have e1 : c m g = Function.update (c m g) k 1 :=
          (Function.update_eq_self_iff.mpr (by simp [c, k])).symm
        have e2 : c (m + 1) (Function.update g k i) = Function.update (c m g) k (w i) := by
          funext k'
          by_cases hk : k' = k
          · subst hk; simp [c, k]
          · have hk' : (k' : ℕ) ≠ m := fun h => hk (Fin.ext h)
            rw [Function.update_of_ne hk]
            simp only [c, Function.update_of_ne hk]
            split_ifs <;> first | rfl | omega
        rw [e2, Finset.prod_update_of_mem (Finset.mem_univ k)]
        conv_lhs => rw [e1, Finset.prod_update_of_mem (Finset.mem_univ k)]
        ring
      rw [hprod]
      exact congrArg _ (globalMixedMeasure_congr (update_slotTuple hmn g α _ i)
        (update_slotTuple hmn g f _ i) _ _)
  rw [claim n le_rfl]
  have hAn : A n = fun _ => T := by funext k; simp [A, k.isLt]
  rw [hAn]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hcn : ∏ k, c n g k = ∏ j, w (g j) := by simp [c]
  rw [hcn]
  exact congrArg _ (globalMixedMeasure_congr (by funext k; simp [slotTuple])
    (by funext k; simp [slotTuple]) _ _)

end

end SGPT.Foundations.Analysis.Pending.GlobalMultilinearExpansion
