/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.StableMatching.Basic
public import LeanPool.StableMatching.Auxiliary
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Data.Fintype.EquivFin

/-!
# The deferred acceptance algorithm

We define the men-proposing deferred acceptance algorithm of Gale and Shapley in rounds. The
state of the algorithm is the set of women who have rejected each man. In each round every man
proposes to his best acceptable woman who has not rejected him (`Market.proposal`), every woman
holds her best acceptable proposer (`Market.held`) and rejects the others (`Market.step`).
`Market.deferredAcceptance` runs `|M| · |W| + 1` rounds from no rejection and returns each
man's final proposal.

Main results:

* `Market.step_rej_of_le`: the rejection sets only grow, so the iteration is constant after at
  most `|M| · |W|` rounds;
* `Market.isStable_daMatching` and `Market.exists_isStable_man_eq_deferredAcceptance`: the final
  proposals are the men's side of a stable matching, in which each woman is matched to the man
  she holds (A. E. Roth, *Deferred acceptance algorithms: history, theory, practice, and open
  questions*, Internat. J. Game Theory 36 (2008), Theorem 1; D. Gale, L. S. Shapley, *College
  admissions and the stability of marriage*, Amer. Math. Monthly 69 (1962), Theorem 1);
* `Market.exists_isStable`: every finite marriage market has a stable matching.

The key invariant (`Market.rankW_held_lt_of_mem_rej`) is that a woman who has rejected a man
holds, at every later round, someone (possibly nobody) she strictly prefers to him.
-/

@[expose] public section

noncomputable section

namespace LeanPool.StableMatching

variable {M W : Type*}

namespace Market

variable (P : Market M W)

section Proposal

variable [Fintype W] [DecidableEq W]

/-- The proposal of man `m` when the women in `R` have rejected him: his best acceptable woman
outside `R`, if any. -/
def proposal (m : M) (R : Finset W) : Option W :=
  List.argmin (fun w ↦ P.rankM m (some w))
    (Finset.univ.filter fun w ↦ w ∉ R ∧ P.rankM m (some w) < P.rankM m none).toList

variable {P}

/-! ### Proposals -/

theorem proposal_eq_some_iff {m : M} {R : Finset W} {w : W} :
    P.proposal m R = some w ↔ (w ∉ R ∧ P.rankM m (some w) < P.rankM m none) ∧
      ∀ w', w' ∉ R ∧ P.rankM m (some w') < P.rankM m none →
        P.rankM m (some w) ≤ P.rankM m (some w') :=
  argmin_filter_eq_some_iff _ ((P.rankM_injective m).comp (Option.some_injective W))

theorem proposal_eq_none_iff {m : M} {R : Finset W} :
    P.proposal m R = none ↔ ∀ w, ¬ (w ∉ R ∧ P.rankM m (some w) < P.rankM m none) :=
  argmin_filter_eq_none_iff _

theorem not_mem_of_proposal_eq_some {m : M} {R : Finset W} {w : W}
    (h : P.proposal m R = some w) : w ∉ R :=
  (proposal_eq_some_iff.1 h).1.1

theorem rankM_lt_none_of_proposal_eq_some {m : M} {R : Finset W} {w : W}
    (h : P.proposal m R = some w) : P.rankM m (some w) < P.rankM m none :=
  (proposal_eq_some_iff.1 h).1.2

theorem rankM_proposal_le_none (m : M) (R : Finset W) :
    P.rankM m (P.proposal m R) ≤ P.rankM m none := by
  cases h : P.proposal m R with
  | none => exact le_rfl
  | some w => exact (rankM_lt_none_of_proposal_eq_some h).le

/-- A man's proposal is at least as good as any acceptable woman who has not rejected him. -/
theorem rankM_proposal_le {m : M} {R : Finset W} {w : W} (hw : w ∉ R)
    (hacc : P.rankM m (some w) ≤ P.rankM m none) :
    P.rankM m (P.proposal m R) ≤ P.rankM m (some w) := by
  cases h : P.proposal m R with
  | none => exact absurd ⟨hw, rankM_some_lt_none hacc⟩ (proposal_eq_none_iff.1 h w)
  | some w' => exact (proposal_eq_some_iff.1 h).2 w ⟨hw, rankM_some_lt_none hacc⟩

/-- More rejections give a proposal that is no better. -/
theorem rankM_proposal_mono {m : M} {R R' : Finset W} (h : R ⊆ R') :
    P.rankM m (P.proposal m R) ≤ P.rankM m (P.proposal m R') := by
  cases h' : P.proposal m R' with
  | none => exact rankM_proposal_le_none m R
  | some w =>
    exact rankM_proposal_le (fun hw ↦ not_mem_of_proposal_eq_some h' (h hw))
      (rankM_lt_none_of_proposal_eq_some h').le

/-- A man keeps proposing to a woman as long as she has not rejected him. -/
theorem proposal_eq_of_subset {m : M} {R R' : Finset W} {w : W} (h : R ⊆ R')
    (hw : P.proposal m R = some w) (hw' : w ∉ R') : P.proposal m R' = some w := by
  have h1 : P.rankM m (P.proposal m R') ≤ P.rankM m (some w) :=
    rankM_proposal_le hw' (rankM_lt_none_of_proposal_eq_some hw).le
  have h2 := rankM_proposal_mono (P := P) (m := m) h
  rw [hw] at h2
  exact P.rankM_injective m (le_antisymm h1 h2)

end Proposal

section Held

variable [Fintype M] [DecidableEq W]

/-- The man woman `w` holds among the proposals `props`: her best acceptable proposer, if
any. -/
def held (props : M → Option W) (w : W) : Option M :=
  List.argmin (fun m ↦ P.rankW w (some m))
    (Finset.univ.filter fun m ↦ props m = some w ∧ P.rankW w (some m) < P.rankW w none).toList

variable {P}

/-! ### Held men -/

theorem held_eq_some_iff {props : M → Option W} {w : W} {m : M} :
    P.held props w = some m ↔ (props m = some w ∧ P.rankW w (some m) < P.rankW w none) ∧
      ∀ m', props m' = some w ∧ P.rankW w (some m') < P.rankW w none →
        P.rankW w (some m) ≤ P.rankW w (some m') :=
  argmin_filter_eq_some_iff _ ((P.rankW_injective w).comp (Option.some_injective M))

theorem held_eq_none_iff {props : M → Option W} {w : W} :
    P.held props w = none ↔ ∀ m, ¬ (props m = some w ∧ P.rankW w (some m) < P.rankW w none) :=
  argmin_filter_eq_none_iff _

theorem eq_some_of_held_eq_some {props : M → Option W} {w : W} {m : M}
    (h : P.held props w = some m) : props m = some w :=
  (held_eq_some_iff.1 h).1.1

theorem rankW_lt_none_of_held_eq_some {props : M → Option W} {w : W} {m : M}
    (h : P.held props w = some m) : P.rankW w (some m) < P.rankW w none :=
  (held_eq_some_iff.1 h).1.2

theorem rankW_held_le_none (props : M → Option W) (w : W) :
    P.rankW w (P.held props w) ≤ P.rankW w none := by
  cases h : P.held props w with
  | none => exact le_rfl
  | some m => exact (rankW_lt_none_of_held_eq_some h).le

/-- A woman holds a man at least as good as any acceptable proposer. -/
theorem rankW_held_le {props : M → Option W} {w : W} {m : M} (hm : props m = some w)
    (hacc : P.rankW w (some m) ≤ P.rankW w none) :
    P.rankW w (P.held props w) ≤ P.rankW w (some m) := by
  cases h : P.held props w with
  | none => exact absurd ⟨hm, rankW_some_lt_none hacc⟩ (held_eq_none_iff.1 h m)
  | some m' => exact (held_eq_some_iff.1 h).2 m ⟨hm, rankW_some_lt_none hacc⟩

end Held

variable [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

/-- One round of deferred acceptance: every man proposes, every woman holds her best acceptable
proposer, and each rejected proposal is added to the proposer's rejections. -/
def step (R : M → Finset W) : M → Finset W := fun m ↦
  match P.proposal m (R m) with
  | none => R m
  | some w =>
    if P.held (fun m' ↦ P.proposal m' (R m')) w = some m then R m else insert w (R m)

/-- The men-proposing **deferred acceptance** algorithm: `|M| · |W| + 1` rounds from no
rejection, then each man's final proposal. -/
def deferredAcceptance : M → Option W :=
  let R := P.step^[Fintype.card M * Fintype.card W + 1] fun _ ↦ ∅
  fun m ↦ P.proposal m (R m)

/-- The proposals of all men when the women in `R m` have rejected `m`. -/
def proposals (R : M → Finset W) : M → Option W := fun m ↦ P.proposal m (R m)

/-- The rejection sets after `k` rounds of deferred acceptance. -/
def rej (k : ℕ) : M → Finset W := P.step^[k] fun _ ↦ ∅

/-- The rejection sets at the end of deferred acceptance. -/
def finalRej : M → Finset W := P.rej (Fintype.card M * Fintype.card W + 1)

variable {P}

/-! ### One round -/

theorem step_eq_proposals (R : M → Finset W) (m : M) : P.step R m =
    match P.proposal m (R m) with
    | none => R m
    | some w => if P.held (P.proposals R) w = some m then R m else insert w (R m) := rfl

theorem mem_step_iff {R : M → Finset W} {m : M} {w : W} :
    w ∈ P.step R m ↔ w ∈ R m ∨ (P.proposal m (R m) = some w ∧ P.held (P.proposals R) w ≠ some m) :=
  by
  rw [step_eq_proposals]
  cases h : P.proposal m (R m) with
  | none => simp
  | some w' =>
    simp only [Option.some.injEq]
    split_ifs with hh
    · constructor
      · exact Or.inl
      · rintro (h' | ⟨rfl, h'⟩)
        · exact h'
        · exact absurd hh h'
    · rw [Finset.mem_insert]
      constructor
      · rintro (rfl | h')
        · exact Or.inr ⟨rfl, hh⟩
        · exact Or.inl h'
      · rintro (h' | ⟨rfl, -⟩)
        · exact Or.inr h'
        · exact Or.inl rfl

theorem subset_step (R : M → Finset W) (m : M) : R m ⊆ P.step R m :=
  fun _ hw ↦ mem_step_iff.2 (Or.inl hw)

/-- A man held by a woman is not rejected in this round. -/
theorem step_eq_of_held {R : M → Finset W} {w : W} {m : M}
    (h : P.held (P.proposals R) w = some m) : P.step R m = R m := by
  ext w'
  rw [mem_step_iff]
  refine ⟨?_, Or.inl⟩
  rintro (h' | ⟨h1, h2⟩)
  · exact h'
  · have h3 : P.proposals R m = some w := eq_some_of_held_eq_some h
    change P.proposal m (R m) = some w at h3
    rw [h3, Option.some.injEq] at h1
    subst h1
    exact absurd h h2

/-- A man held by a woman proposes to her again in the next round. -/
theorem proposal_step_of_held {R : M → Finset W} {w : W} {m : M}
    (h : P.held (P.proposals R) w = some m) : P.proposal m (P.step R m) = some w := by
  rw [step_eq_of_held h]
  exact (eq_some_of_held_eq_some h : P.proposals R m = some w)

/-- The man a woman holds only gets better from one round to the next. -/
theorem rankW_held_step_le (R : M → Finset W) (w : W) :
    P.rankW w (P.held (P.proposals (P.step R)) w) ≤ P.rankW w (P.held (P.proposals R) w) := by
  cases h : P.held (P.proposals R) w with
  | none => exact rankW_held_le_none _ w
  | some m => exact rankW_held_le (proposal_step_of_held h) (rankW_lt_none_of_held_eq_some h).le

/-- The fixed points of a round are the states in which every woman holds each of her
proposers. -/
theorem step_eq_self_iff {R : M → Finset W} :
    P.step R = R ↔ ∀ m w, P.proposal m (R m) = some w → P.held (P.proposals R) w = some m := by
  constructor
  · intro h m w hw
    by_contra hne
    have hmem : w ∈ P.step R m := mem_step_iff.2 (Or.inr ⟨hw, hne⟩)
    rw [h] at hmem
    exact not_mem_of_proposal_eq_some hw hmem
  · intro h
    funext m
    ext w
    rw [mem_step_iff]
    refine ⟨?_, Or.inl⟩
    rintro (h' | ⟨h1, h2⟩)
    · exact h'
    · exact absurd (h m w h1) h2

/-! ### The rounds -/

@[simp] theorem rej_zero (m : M) : P.rej 0 m = ∅ := rfl

theorem rej_succ (k : ℕ) : P.rej (k + 1) = P.step (P.rej k) :=
  Function.iterate_succ_apply' _ _ _

theorem rej_mono {k j : ℕ} (h : k ≤ j) (m : M) : P.rej k m ⊆ P.rej j m := by
  induction j, h using Nat.le_induction with
  | base => exact subset_rfl
  | succ j _ ih => exact ih.trans (by rw [rej_succ]; exact subset_step _ m)

theorem rej_add_of_step_eq {k : ℕ} (h : P.step (P.rej k) = P.rej k) (i : ℕ) :
    P.rej (k + i) = P.rej k := by
  induction i with
  | zero => rfl
  | succ i ih => rw [← add_assoc, rej_succ, ih, h]

theorem rej_eq_of_step_eq {k j : ℕ} (h : P.step (P.rej k) = P.rej k) (hkj : k ≤ j) :
    P.rej j = P.rej k := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hkj
  exact rej_add_of_step_eq h i

omit [DecidableEq M] [DecidableEq W] in
theorem sum_card_le (R : M → Finset W) :
    ∑ m, (R m).card ≤ Fintype.card M * Fintype.card W := by
  calc ∑ m, (R m).card ≤ ∑ _m : M, Fintype.card W :=
        Finset.sum_le_sum fun m _ ↦ Finset.card_le_univ (R m)
    _ = Fintype.card M * Fintype.card W := by simp

/-- A round that changes the state adds a rejection. -/
theorem sum_card_lt_step {R : M → Finset W} (h : P.step R ≠ R) :
    ∑ m, (R m).card < ∑ m, (P.step R m).card := by
  obtain ⟨m, hm⟩ := Function.ne_iff.1 h
  refine Finset.sum_lt_sum (fun m _ ↦ Finset.card_le_card (subset_step R m))
    ⟨m, Finset.mem_univ m, Finset.card_lt_card ?_⟩
  exact Finset.ssubset_iff_subset_ne.2 ⟨subset_step R m, Ne.symm hm⟩

theorem le_sum_card_rej (k : ℕ) (h : ∀ j < k, P.step (P.rej j) ≠ P.rej j) :
    k ≤ ∑ m, (P.rej k m).card := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have h1 := ih fun j hj ↦ h j (Nat.lt_succ_of_lt hj)
    have h2 := sum_card_lt_step (h k (Nat.lt_succ_self k))
    rw [rej_succ]
    omega

/-- **Termination.** After `|M| · |W|` rounds, a round changes nothing. -/
theorem step_rej_card_mul_card :
    P.step (P.rej (Fintype.card M * Fintype.card W)) = P.rej (Fintype.card M * Fintype.card W) := by
  by_contra h
  have hne : ∀ j < Fintype.card M * Fintype.card W + 1, P.step (P.rej j) ≠ P.rej j := by
    intro j hj hfix
    refine h ?_
    rw [rej_eq_of_step_eq hfix (Nat.lt_succ_iff.1 hj)]
    exact hfix
  have h1 := le_sum_card_rej _ hne
  have h2 := sum_card_le (P.rej (Fintype.card M * Fintype.card W + 1))
  omega

/-- After `|M| · |W|` rounds the iteration is constant. -/
theorem rej_eq_of_le {k : ℕ} (hk : Fintype.card M * Fintype.card W ≤ k) :
    P.rej k = P.rej (Fintype.card M * Fintype.card W) :=
  rej_eq_of_step_eq step_rej_card_mul_card hk

theorem step_rej_of_le {k : ℕ} (hk : Fintype.card M * Fintype.card W ≤ k) :
    P.step (P.rej k) = P.rej k := by
  rw [rej_eq_of_le hk]
  exact step_rej_card_mul_card

theorem step_finalRej : P.step P.finalRej = P.finalRej :=
  step_rej_of_le (Nat.le_succ _)

theorem finalRej_eq_of_le {k : ℕ} (hk : Fintype.card M * Fintype.card W ≤ k) :
    P.rej k = P.finalRej := by
  rw [finalRej, rej_eq_of_le hk, rej_eq_of_le (Nat.le_succ _)]

theorem rej_subset_finalRej (k : ℕ) (m : M) : P.rej k m ⊆ P.finalRej m := by
  rw [← finalRej_eq_of_le (le_max_right k (Fintype.card M * Fintype.card W))]
  exact rej_mono (le_max_left _ _) m

theorem deferredAcceptance_eq (m : M) :
    P.deferredAcceptance m = P.proposal m (P.finalRej m) := rfl

/-! ### The invariant and stability -/

/-- **The invariant of deferred acceptance.** A woman who has rejected a man holds someone
(possibly nobody) she strictly prefers to him. -/
theorem rankW_held_lt_of_mem_rej {k : ℕ} {m : M} {w : W} (hw : w ∈ P.rej k m) :
    P.rankW w (P.held (P.proposals (P.rej k)) w) < P.rankW w (some m) := by
  induction k with
  | zero => simp at hw
  | succ k ih =>
    rw [rej_succ] at hw ⊢
    refine lt_of_le_of_lt (rankW_held_step_le _ w) ?_
    rcases mem_step_iff.1 hw with h | ⟨h1, h2⟩
    · exact ih h
    · by_cases hacc : P.rankW w (some m) ≤ P.rankW w none
      · exact P.rankW_lt_of_le_of_ne (rankW_held_le h1 hacc) h2
      · exact lt_of_le_of_lt (rankW_held_le_none _ w) (not_le.1 hacc)

/-- The matching read off a fixed point of a round: each man is matched to the woman he
proposes to, who holds him. -/
def matchingOfStepEq (R : M → Finset W) (h : P.step R = R) : M ≃. W where
  toFun := P.proposals R
  invFun := P.held (P.proposals R)
  inv m w := ⟨eq_some_of_held_eq_some, fun h' ↦ step_eq_self_iff.1 h m w h'⟩

theorem isStable_matchingOfStepEq {R : M → Finset W} (h : P.step R = R)
    (hR : ∀ m w, w ∈ R m → P.rankW w (P.held (P.proposals R) w) < P.rankW w (some m)) :
    P.IsStable (P.matchingOfStepEq R h) := by
  refine ⟨⟨fun m ↦ rankM_proposal_le_none m (R m), fun w ↦ rankW_held_le_none _ w⟩, ?_⟩
  rintro m w ⟨hm, hw⟩
  change P.rankM m (some w) < P.rankM m (P.proposal m (R m)) at hm
  change P.rankW w (some m) < P.rankW w (P.held (P.proposals R) w) at hw
  by_cases hwR : w ∈ R m
  · exact absurd (hR m w hwR) (not_lt.2 hw.le)
  · have hacc := (lt_of_lt_of_le hm (rankM_proposal_le_none m (R m))).le
    exact absurd (rankM_proposal_le hwR hacc) (not_le.2 hm)

variable (P) in
/-- The outcome of deferred acceptance as a matching: each man is matched to his final
proposal, and each woman to the man she holds at the end. -/
def daMatching : M ≃. W := P.matchingOfStepEq P.finalRej P.step_finalRej

theorem daMatching_apply (m : M) : P.daMatching m = P.deferredAcceptance m := rfl

theorem coe_daMatching : ⇑P.daMatching = P.deferredAcceptance := rfl

theorem daMatching_symm_apply (w : W) :
    P.daMatching.symm w = P.held (P.proposals P.finalRej) w := rfl

variable (P) in
/-- The outcome of deferred acceptance is stable. -/
theorem isStable_daMatching : P.IsStable P.daMatching :=
  isStable_matchingOfStepEq P.step_finalRej fun _ _ hw ↦ rankW_held_lt_of_mem_rej hw

variable (P) in
/-- **Gale–Shapley.** Deferred acceptance returns the men's side of a stable matching. -/
theorem exists_isStable_man_eq_deferredAcceptance :
    ∃ μ : M ≃. W, ⇑μ = P.deferredAcceptance ∧ P.IsStable μ :=
  ⟨P.daMatching, rfl, P.isStable_daMatching⟩

end Market

/-- **Gale–Shapley.** Every finite marriage market has a stable matching. This is a corollary
of the deferred acceptance theorem; `Galvin.exists_isStable` is the pool's other, independent
existence proof, by induction, for a model in which acceptability is a single relation and
matchings are relations. -/
theorem Market.exists_isStable [Finite M] [Finite W] (P : Market M W) :
    ∃ μ : M ≃. W, P.IsStable μ := by
  classical
  have := Fintype.ofFinite M
  have := Fintype.ofFinite W
  exact ⟨P.daMatching, P.isStable_daMatching⟩

end LeanPool.StableMatching
