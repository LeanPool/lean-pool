/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.ProbabilisticMethod.BernoulliWeights
public import Mathlib.Analysis.SpecialFunctions.Exp

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Lovász Local Lemma for finite probabilities

Let `E i`, `i ∈ I`, be bad events in a finite probability space. The Local Lemma says that if each
event is unlikely and depends on few others, then with positive probability none of them occurs.
The lemma is proved here in its asymmetric, lopsided form, where "`E i` is independent of the
events outside `Γ i`" is replaced by the weaker inequality
`P(E i ∧ none of E j, j ∈ S) ≤ P(E i) P(none of E j, j ∈ S)` for `S` disjoint from `Γ i`.

The probability space is any finite sample set `Ω` with weights `w ≥ 0` of total `1`
(`Finset.weightProb`), so non-identically distributed coordinates and arbitrary finite laws are
covered; the `p`-biased cube is the case `Ω = U.powerset`, `w = U.bernoulliWeight p`. The proof
is the usual strong induction on the conditioning set, in a division-free form that never
conditions on an event of probability zero.

## Main definitions

* `Finset.weightProb Ω w P`: the probability `∑ a ∈ Ω with P a, w a`.
* `Finset.LopsidedWeights`, `Finset.Lopsided`: the lopsided dependence hypothesis, for finite
  weights and for the `p`-biased cube.

## Main statements

* `Finset.prod_one_sub_le_weightProb_forall_not`: **the Lovász Local Lemma** (asymmetric,
  lopsided form) for finite weights. If `P(E i) ≤ x i ∏ j ∈ Γ i, (1 - x j)` for `0 ≤ x i ≤ 1`,
  then the probability that no `E i` occurs is at least `∏ i ∈ I, (1 - x i)`.
* `Finset.exists_mem_forall_not_of_weight_lll`: hence some sample point avoids every `E i` when
  all `x i < 1`.
* `Finset.prod_one_sub_le_bernoulliProb_forall_not`, `Finset.exists_forall_not_of_lll`: the same
  on the `p`-biased cube.
* `Finset.lopsided_of_dependsOnCoords`: events determined by coordinate sets `T i` satisfy the
  lopsided hypothesis with `Γ i` the events whose coordinate sets meet `T i`.
* `Finset.exists_forall_not_of_symmetric_lll`: **the symmetric Local Lemma**. If every event has
  probability at most `q`, each meets at most `d` others, and `e q (d + 1) ≤ 1`, some subset
  avoids every event.

## References

* [P. Erdős, L. Lovász, *Problems and results on 3-chromatic hypergraphs and some related
  questions*][ErdosLovasz1975]
* [P. Erdős, J. Spencer, *Lopsided Lovász local lemma and Latin transversals*][ErdosSpencer1991]
* [N. Alon, J. H. Spencer, *The probabilistic method*][AlonSpencer2016]
-/

@[expose] public section

open Finset Real

namespace Finset

variable {α ι : Type*} [DecidableEq α] {U : Finset α} {p : ℝ}

section Basic

variable (U p)

/-- Splitting an event along another: `P(P) = P(P ∧ Q) + P(P ∧ ¬Q)`. -/
theorem bernoulliProb_eq_add (P Q : Finset α → Prop) [DecidablePred P] [DecidablePred Q] :
    U.bernoulliProb p P =
      U.bernoulliProb p (fun A => P A ∧ Q A) + U.bernoulliProb p (fun A => P A ∧ ¬Q A) := by
  unfold bernoulliProb
  rw [← sum_filter_add_sum_filter_not (U.powerset.filter P) Q, filter_filter, filter_filter]

variable {U p}

/-- A weaker event is at least as likely. -/
theorem bernoulliProb_mono (h0 : 0 ≤ p) (h1 : p ≤ 1) {P Q : Finset α → Prop} [DecidablePred P]
    [DecidablePred Q] (h : ∀ A, P A → Q A) : U.bernoulliProb p P ≤ U.bernoulliProb p Q :=
  sum_le_sum_of_subset_of_nonneg (monotone_filter_right _ fun A _ => h A) fun A _ _ =>
    bernoulliWeight_nonneg h0 h1 A

/-- The sure event has probability `1`. -/
@[simp] theorem bernoulliProb_true : U.bernoulliProb p (fun _ => True) = 1 := by
  rw [bernoulliProb, filter_true_of_mem fun _ _ => trivial, sum_bernoulliWeight]

end Basic

/-! ### Finite weights -/

section Weights

variable {β : Type*}

/-- The probability `∑ a ∈ Ω with P a, w a` of the event `P` under the weights `w` on the finite
sample set `Ω`. It is a probability when `w` is nonnegative on `Ω` with total `1`; for the
`p`-biased cube, `U.bernoulliProb p P` is `U.powerset.weightProb (U.bernoulliWeight p) P`. -/
noncomputable def weightProb (Ω : Finset β) (w : β → ℝ) (P : β → Prop) [DecidablePred P] : ℝ :=
  ∑ a ∈ Ω with P a, w a

variable {Ω : Finset β} {w : β → ℝ}

/-- For nonnegative weights, probabilities are nonnegative. -/
theorem weightProb_nonneg (hw0 : ∀ a ∈ Ω, 0 ≤ w a) (P : β → Prop) [DecidablePred P] :
    0 ≤ Ω.weightProb w P :=
  sum_nonneg fun a ha => hw0 a (mem_filter.mp ha).1

/-- For nonnegative weights, a weaker event is at least as likely. -/
theorem weightProb_mono (hw0 : ∀ a ∈ Ω, 0 ≤ w a) {P Q : β → Prop} [DecidablePred P]
    [DecidablePred Q] (h : ∀ a, P a → Q a) : Ω.weightProb w P ≤ Ω.weightProb w Q :=
  sum_le_sum_of_subset_of_nonneg (monotone_filter_right _ fun a _ => h a) fun a ha _ =>
    hw0 a (mem_filter.mp ha).1

/-- Splitting an event along another: `P(P) = P(P ∧ Q) + P(P ∧ ¬Q)`. -/
theorem weightProb_eq_add (Ω : Finset β) (w : β → ℝ) (P Q : β → Prop) [DecidablePred P]
    [DecidablePred Q] :
    Ω.weightProb w P =
      Ω.weightProb w (fun a => P a ∧ Q a) + Ω.weightProb w (fun a => P a ∧ ¬Q a) := by
  unfold weightProb
  rw [← sum_filter_add_sum_filter_not (Ω.filter P) Q, filter_filter, filter_filter]

end Weights

variable {β : Type*} (E : ι → β → Prop) [∀ i, DecidablePred (E i)]

/-- No event `E j`, `j ∈ S`, occurs. -/
def Avoids (S : Finset ι) (a : β) : Prop := ∀ j ∈ S, ¬E j a

/-- Avoiding finitely many decidable events is decidable. -/
instance (S : Finset ι) : DecidablePred (Avoids E S) := fun _ =>
  inferInstanceAs (Decidable (∀ j ∈ S, _))

omit [∀ i, DecidablePred (E i)] in
/-- Avoiding `insert i S` is avoiding `E i` and avoiding `S`. -/
theorem avoids_insert [DecidableEq ι] {i : ι} {S : Finset ι} {a : β} :
    Avoids E (insert i S) a ↔ ¬E i a ∧ Avoids E S a := by
  simp [Avoids]

variable {E}

/-- The lopsided dependence hypothesis for the weights `w` on `Ω`: `E i` is "negatively
correlated" with the event that no `E j`, `j ∈ S`, occurs, whenever `S` avoids `Γ i` and `i`. -/
def LopsidedWeights (Ω : Finset β) (w : β → ℝ) (I : Finset ι) (E : ι → β → Prop)
    [∀ i, DecidablePred (E i)] (Γ : ι → Finset ι) : Prop :=
  ∀ i ∈ I, ∀ S ⊆ I, Disjoint S (Γ i) → i ∉ S →
    Ω.weightProb w (fun a => E i a ∧ Avoids E S a) ≤
      Ω.weightProb w (E i) * Ω.weightProb w (Avoids E S)

/-- The lopsided dependence hypothesis on the `p`-biased cube: `LopsidedWeights` for the weights
`U.bernoulliWeight p` on `U.powerset`. -/
def Lopsided (U : Finset α) (p : ℝ) (I : Finset ι) (E : ι → Finset α → Prop)
    [∀ i, DecidablePred (E i)] (Γ : ι → Finset ι) : Prop :=
  ∀ i ∈ I, ∀ S ⊆ I, Disjoint S (Γ i) → i ∉ S →
    U.bernoulliProb p (fun A => E i A ∧ Avoids E S A) ≤
      U.bernoulliProb p (E i) * U.bernoulliProb p (Avoids E S)

/-- A product of factors in `[0, 1]` is at most `1`. -/
private theorem prod_le_one_of_mem_Icc {s : Finset ι} {f : ι → ℝ} (h0 : ∀ i ∈ s, 0 ≤ f i)
    (h1 : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha]
    have hs0 : 0 ≤ ∏ i ∈ s, f i := prod_nonneg fun i hi => h0 i (mem_insert_of_mem hi)
    have hs1 := ih (fun i hi => h0 i (mem_insert_of_mem hi)) fun i hi => h1 i (mem_insert_of_mem hi)
    nlinarith [h0 a (mem_insert_self a s), h1 a (mem_insert_self a s)]

/-- A product of factors in `[0, 1]` over a superset is smaller. -/
private theorem prod_le_prod_of_superset_of_le_one {s t : Finset ι} (hst : s ⊆ t) (f : ι → ℝ)
    (h0 : ∀ i ∈ t, 0 ≤ f i) (h1 : ∀ i ∈ t, f i ≤ 1) : ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i := by
  classical
  rw [← prod_sdiff hst]
  refine mul_le_of_le_one_left (prod_nonneg fun i hi => h0 i (hst hi)) ?_
  exact prod_le_one_of_mem_Icc (fun i hi => h0 i (mem_sdiff.mp hi).1)
    fun i hi => h1 i (mem_sdiff.mp hi).1

section Weights

variable {Ω : Finset β} {w : β → ℝ}

/-- Adding `i` to the avoided set costs the probability that `E i` occurs while `S` is avoided. -/
private theorem weightProb_avoids_insert [DecidableEq ι] (i : ι) (S : Finset ι) :
    Ω.weightProb w (Avoids E (insert i S)) =
      Ω.weightProb w (Avoids E S) - Ω.weightProb w (fun a => E i a ∧ Avoids E S a) := by
  have := weightProb_eq_add Ω w (Avoids E S) (E i)
  have heq : Ω.weightProb w (Avoids E (insert i S)) =
      Ω.weightProb w (fun a => Avoids E S a ∧ ¬E i a) := by
    unfold weightProb
    congr 1
    ext a
    simp [avoids_insert, and_comm]
  have heq2 : Ω.weightProb w (fun a => E i a ∧ Avoids E S a) =
      Ω.weightProb w (fun a => Avoids E S a ∧ E i a) := by
    unfold weightProb
    congr 1
    ext a
    simp [and_comm]
  linarith

/-- The conditional bound at the heart of the Local Lemma, by strong induction on `#S`:
`P(E i ∧ no E j, j ∈ S) ≤ x i P(no E j, j ∈ S)` for `S ⊆ I` not containing `i`. -/
private theorem weightProb_and_avoids_le (hw0 : ∀ a ∈ Ω, 0 ≤ w a) {I : Finset ι}
    {Γ : ι → Finset ι} (hL : LopsidedWeights Ω w I E Γ) {x : ι → ℝ} (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i ≤ 1) (hp : ∀ i ∈ I, Ω.weightProb w (E i) ≤ x i * ∏ j ∈ Γ i, (1 - x j))
    (n : ℕ) : ∀ S ⊆ I, #S = n → ∀ i ∈ I, i ∉ S →
      Ω.weightProb w (fun a => E i a ∧ Avoids E S a) ≤ x i * Ω.weightProb w (Avoids E S) := by
  classical
  set μ := Ω.weightProb w
  have hμ0 : ∀ (P : β → Prop) [DecidablePred P], 0 ≤ Ω.weightProb w P :=
    fun P _ => weightProb_nonneg hw0 P
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hS hn i hi hiS
    -- adding an index to a smaller set keeps a fraction `1 - x j`
    have step : ∀ T ⊆ I, #T < n → ∀ j ∈ I, j ∉ T →
        (1 - x j) * μ (Avoids E T) ≤ μ (Avoids E (insert j T)) := by
      intro T hT hTn j hj hjT
      have hs : μ (Avoids E (insert j T)) =
          μ (Avoids E T) - μ (fun a => E j a ∧ Avoids E T a) := weightProb_avoids_insert j T
      rw [hs]
      have := ih _ hTn T hT rfl j hj hjT
      nlinarith
    set S₂ := S.filter (· ∉ Γ i)
    set S₁ := S.filter (· ∈ Γ i)
    have hS₂ : S₂ ⊆ S := filter_subset _ _
    -- avoiding `S` costs at most the product over `S₁`
    have hgrow : ∀ T ⊆ S₁, (∏ j ∈ T, (1 - x j)) * μ (Avoids E S₂) ≤ μ (Avoids E (S₂ ∪ T)) := by
      intro T hT
      induction T using Finset.induction_on with
      | empty => simp
      | insert j T hjT ihT =>
        have hT' := (insert_subset_iff.mp hT).2
        have hj := (insert_subset_iff.mp hT).1
        have hjS : j ∈ S := (mem_filter.mp hj).1
        have hjS₂ : j ∉ S₂ := fun h => (mem_filter.mp h).2 (mem_filter.mp hj).2
        have hsub : S₂ ∪ T ⊆ S.erase j := fun y hy => by
          rcases mem_union.mp hy with hy | hy
          · exact mem_erase.mpr ⟨fun h => hjS₂ (h ▸ hy), hS₂ hy⟩
          · exact mem_erase.mpr ⟨fun h => hjT (h ▸ hy), (mem_filter.mp (hT' hy)).1⟩
        have hlt : #(S₂ ∪ T) < n := by
          rw [← hn]
          exact (card_le_card hsub).trans_lt (card_erase_lt_of_mem hjS)
        have := step (S₂ ∪ T) (hsub.trans ((erase_subset _ _).trans hS)) hlt j (hS hjS)
          fun h => (mem_union.mp h).elim hjS₂ hjT
        rw [prod_insert hjT, union_insert]
        calc (1 - x j) * (∏ k ∈ T, (1 - x k)) * μ (Avoids E S₂)
            = (1 - x j) * ((∏ k ∈ T, (1 - x k)) * μ (Avoids E S₂)) := by ring
          _ ≤ (1 - x j) * μ (Avoids E (S₂ ∪ T)) :=
              mul_le_mul_of_nonneg_left (ihT hT') (by linarith [hx1 j])
          _ ≤ _ := this
    have hS12 : S₂ ∪ S₁ = S := by
      ext j
      simp only [S₂, S₁, mem_union, mem_filter]
      tauto
    have hgrowS := hgrow S₁ Subset.rfl
    rw [hS12] at hgrowS
    have hprod : ∏ j ∈ Γ i, (1 - x j) ≤ ∏ j ∈ S₁, (1 - x j) := by
      refine prod_le_prod_of_superset_of_le_one (fun j hj => (mem_filter.mp hj).2) _
        (fun j _ => ?_)
        (fun j _ => ?_)
      · linarith [hx1 j]
      · linarith [hx0 j]
    calc μ (fun a => E i a ∧ Avoids E S a)
        ≤ μ (fun a => E i a ∧ Avoids E S₂ a) := weightProb_mono hw0 fun a ha =>
          ⟨ha.1, fun j hj => ha.2 j (hS₂ hj)⟩
      _ ≤ μ (E i) * μ (Avoids E S₂) := hL i hi S₂ (hS₂.trans hS)
          (disjoint_left.mpr fun j hj hjΓ => (mem_filter.mp hj).2 hjΓ)
          fun h => hiS (hS₂ h)
      _ ≤ x i * (∏ j ∈ Γ i, (1 - x j)) * μ (Avoids E S₂) :=
          mul_le_mul_of_nonneg_right (hp i hi) (hμ0 _)
      _ ≤ x i * (∏ j ∈ S₁, (1 - x j)) * μ (Avoids E S₂) := by
          gcongr
          · exact hμ0 _
          · exact hx0 i
      _ = x i * ((∏ j ∈ S₁, (1 - x j)) * μ (Avoids E S₂)) := by ring
      _ ≤ x i * μ (Avoids E S) := mul_le_mul_of_nonneg_left hgrowS (hx0 i)

/-- **The Lovász Local Lemma** (asymmetric, lopsided form) for any finite probability: weights
`w ≥ 0` on a finite sample set `Ω` with total `1`. Under the lopsided hypothesis, if
`P(E i) ≤ x i ∏ j ∈ Γ i, (1 - x j)` with `0 ≤ x ≤ 1`, then no `E i` occurs with probability at
least `∏ i ∈ I, (1 - x i)`. -/
theorem prod_one_sub_le_weightProb_forall_not (hw0 : ∀ a ∈ Ω, 0 ≤ w a)
    (hw1 : ∑ a ∈ Ω, w a = 1) {I : Finset ι} {Γ : ι → Finset ι} (hL : LopsidedWeights Ω w I E Γ)
    {x : ι → ℝ} (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1)
    (hp : ∀ i ∈ I, Ω.weightProb w (E i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∏ i ∈ I, (1 - x i) ≤ Ω.weightProb w (Avoids E I) := by
  classical
  -- multiply up over `I`
  have hall : ∀ T ⊆ I, ∏ i ∈ T, (1 - x i) ≤ Ω.weightProb w (Avoids E T) := by
    intro T hT
    induction T using Finset.induction_on with
    | empty =>
      rw [prod_empty]
      refine le_of_eq ?_
      unfold weightProb
      rw [filter_true_of_mem fun a _ j hj => absurd hj (notMem_empty j), hw1]
    | insert j T hjT ihT =>
      have hT' := (insert_subset_iff.mp hT).2
      have hj := (insert_subset_iff.mp hT).1
      rw [prod_insert hjT, weightProb_avoids_insert]
      have := weightProb_and_avoids_le hw0 hL hx0 hx1 hp _ T hT' rfl j hj hjT
      have h1j : 0 ≤ 1 - x j := by linarith [hx1 j]
      nlinarith [ihT hT', mul_le_mul_of_nonneg_left (ihT hT') h1j]
  exact hall I Subset.rfl

/-- **The Local Lemma for finite weights, existence form.** Under its hypotheses with all
`x i < 1`, some sample point of `Ω` avoids every `E i`. -/
theorem exists_mem_forall_not_of_weight_lll (hw0 : ∀ a ∈ Ω, 0 ≤ w a)
    (hw1 : ∑ a ∈ Ω, w a = 1) {I : Finset ι} {Γ : ι → Finset ι} (hL : LopsidedWeights Ω w I E Γ)
    {x : ι → ℝ} (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hp : ∀ i ∈ I, Ω.weightProb w (E i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∃ a ∈ Ω, ∀ i ∈ I, ¬E i a := by
  have hpos : 0 < Ω.weightProb w (Avoids E I) :=
    (prod_pos fun i _ => by linarith [hx1 i]).trans_le
      (prod_one_sub_le_weightProb_forall_not hw0 hw1 hL hx0 (fun i => (hx1 i).le) hp)
  obtain ⟨a, ha, -⟩ := exists_ne_zero_of_sum_ne_zero hpos.ne'
  exact ⟨a, (mem_filter.mp ha).1, (mem_filter.mp ha).2⟩

end Weights

variable {E : ι → Finset α → Prop} [∀ i, DecidablePred (E i)]

/-- **The Lovász Local Lemma** on the `p`-biased cube (asymmetric, lopsided form): the case
`Ω = U.powerset`, `w = U.bernoulliWeight p` of `prod_one_sub_le_weightProb_forall_not`. -/
theorem prod_one_sub_le_bernoulliProb_forall_not (h0 : 0 ≤ p) (h1 : p ≤ 1) {I : Finset ι}
    {Γ : ι → Finset ι} (hL : Lopsided U p I E Γ) {x : ι → ℝ} (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i ≤ 1)
    (hp : ∀ i ∈ I, U.bernoulliProb p (E i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∏ i ∈ I, (1 - x i) ≤ U.bernoulliProb p (Avoids E I) :=
  prod_one_sub_le_weightProb_forall_not (Ω := U.powerset) (w := U.bernoulliWeight p)
    (fun A _ => bernoulliWeight_nonneg h0 h1 A) (sum_bernoulliWeight U p) hL hx0 hx1 hp

/-- **The Local Lemma, existence form.** Under its hypotheses with all `x i < 1`, some `A ⊆ U`
avoids every `E i`. -/
theorem exists_forall_not_of_lll (h0 : 0 ≤ p) (h1 : p ≤ 1) {I : Finset ι} {Γ : ι → Finset ι}
    (hL : Lopsided U p I E Γ) {x : ι → ℝ} (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hp : ∀ i ∈ I, U.bernoulliProb p (E i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∃ A ∈ U.powerset, ∀ i ∈ I, ¬E i A :=
  exists_mem_forall_not_of_weight_lll (Ω := U.powerset) (w := U.bernoulliWeight p)
    (fun A _ => bernoulliWeight_nonneg h0 h1 A) (sum_bernoulliWeight U p) hL hx0 hx1 hp

/-- **Independence gives the lopsided hypothesis.** If each `E i` depends only on the coordinates
`T i ⊆ U`, the hypothesis holds (with equality) for `Γ i` the indices `j ≠ i` with `T j` meeting
`T i`. -/
theorem lopsided_of_dependsOnCoords [DecidableEq ι] {I : Finset ι} {T : ι → Finset α}
    (hT : ∀ i ∈ I, T i ⊆ U)
    (hE : ∀ i ∈ I, DependsOnCoords (E i) (T i)) :
    Lopsided U p I E fun i => I.filter fun j => j ≠ i ∧ ¬Disjoint (T i) (T j) := by
  intro i hi S hS hSΓ hiS
  refine (bernoulliProb_and (hT i hi) (biUnion_subset.mpr fun j hj => hT j (hS hj))
    ?_ (hE i hi) ?_).le
  · refine (disjoint_biUnion_right _ _ _).mpr fun j hj => ?_
    by_contra hij
    exact disjoint_left.mp hSΓ hj (mem_filter.mpr ⟨hS hj, fun h => hiS (h ▸ hj), hij⟩)
  · intro A B hAB
    refine forall₂_congr fun j hj => not_congr (hE j (hS hj) A B ?_)
    have hsub : T j ⊆ S.biUnion T := subset_biUnion_of_mem T hj
    rw [← inter_eq_right.mpr hsub, ← inter_assoc, ← inter_assoc, hAB]

/-- **The symmetric Local Lemma.** If each `E i` depends only on coordinates `T i ⊆ U`, has
probability at most `q`, and its coordinate set meets those of at most `d` other events, and if
`e q (d + 1) ≤ 1`, then some `A ⊆ U` avoids every `E i`. -/
theorem exists_forall_not_of_symmetric_lll [DecidableEq ι] (h0 : 0 ≤ p) (h1 : p ≤ 1) {I : Finset ι}
    {T : ι → Finset α} (hT : ∀ i ∈ I, T i ⊆ U) (hE : ∀ i ∈ I, DependsOnCoords (E i) (T i)) {q : ℝ}
    {d : ℕ} (hq : ∀ i ∈ I, U.bernoulliProb p (E i) ≤ q)
    (hd : ∀ i ∈ I, #(I.filter fun j => j ≠ i ∧ ¬Disjoint (T i) (T j)) ≤ d)
    (hqd : exp 1 * q * (d + 1) ≤ 1) :
    ∃ A ∈ U.powerset, ∀ i ∈ I, ¬E i A := by
  have hd1 : (0 : ℝ) < d + 1 := by positivity
  have he1 : (1 : ℝ) < exp 1 := by
    have := add_one_le_exp (1 : ℝ)
    linarith
  rcases I.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · exact ⟨∅, empty_mem_powerset _, by simp⟩
  have hq0 : 0 ≤ q := (bernoulliProb_nonneg h0 h1 _).trans (hq i₀ hi₀)
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · -- no dependencies: take `x i = q`
    have hq1 : q < 1 := by
      have : exp 1 * q ≤ 1 := by simpa using hqd
      nlinarith
    refine exists_forall_not_of_lll h0 h1 (lopsided_of_dependsOnCoords hT hE) (x := fun _ => q)
      (fun _ => hq0) (fun _ => hq1) fun i hi => ?_
    rw [card_eq_zero.mp (Nat.le_zero.mp (hd i hi)), prod_empty, mul_one]
    exact hq i hi
  have hd1' : (1 : ℝ) < d + 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
    linarith
  refine exists_forall_not_of_lll h0 h1 (lopsided_of_dependsOnCoords hT hE)
    (x := fun _ => 1 / (d + 1))
    (fun _ => by positivity) (fun _ => by rw [div_lt_one hd1]; exact hd1') fun i hi => ?_
  rw [prod_const]
  have hbase : 0 ≤ 1 - 1 / ((d : ℝ) + 1) := by
    rw [sub_nonneg, div_le_one hd1]; linarith
  have hbase1 : 1 - 1 / ((d : ℝ) + 1) ≤ 1 := by
    have : 0 ≤ 1 / ((d : ℝ) + 1) := by positivity
    linarith
  have hpow : (1 - 1 / ((d : ℝ) + 1)) ^ d ≤ (1 - 1 / ((d : ℝ) + 1)) ^ #(I.filter fun j =>
      j ≠ i ∧ ¬Disjoint (T i) (T j)) := pow_le_pow_of_le_one hbase hbase1 (hd i hi)
  -- `(1 - 1/(d+1))^d ≥ e⁻¹`
  have he : (exp 1)⁻¹ ≤ (1 - 1 / ((d : ℝ) + 1)) ^ d := by
    have hinv := one_add_inv_pow_le_exp (n := d)
    have hdpos' : (0 : ℝ) < d := by exact_mod_cast hdpos
    have heq : 1 - 1 / ((d : ℝ) + 1) = (1 + (d : ℝ)⁻¹)⁻¹ := by
      field_simp
      ring
    rw [heq, inv_pow]
    exact inv_anti₀ (by positivity) hinv
  have hqle : q ≤ (exp 1)⁻¹ * (1 / (d + 1)) := by
    rw [inv_mul_eq_div, div_div, le_div_iff₀ (by positivity)]
    linarith
  calc U.bernoulliProb p (E i) ≤ q := hq i hi
    _ ≤ (exp 1)⁻¹ * (1 / (d + 1)) := hqle
    _ ≤ (1 - 1 / ((d : ℝ) + 1)) ^ d * (1 / (d + 1)) :=
        mul_le_mul_of_nonneg_right he (by positivity)
    _ ≤ (1 - 1 / ((d : ℝ) + 1)) ^ #(I.filter fun j => j ≠ i ∧ ¬Disjoint (T i) (T j)) *
          (1 / (d + 1)) := mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = _ := mul_comm _ _

end Finset
