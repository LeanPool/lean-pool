/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Basic.PEquiv
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Monotone.Defs

/-!
# Marriage markets, matchings and stability

A marriage market on finite sets of men `M` and women `W` with strict preferences is given by
injective rank functions: each man ranks `Option W` and each woman ranks `Option M`, where
`none` stands for staying single; a smaller rank is better and a partner ranked after `none` is
unacceptable. A matching is a Mathlib partial equivalence `μ : M ≃. W`. We define individual
rationality, blocking pairs and stability (the marriage model of A. E. Roth, *Deferred acceptance
algorithms: history, theory, practice, and open questions*, Internat. J. Game Theory 36 (2008),
§1), and prove:

* `Market.isStable_swap_iff`: `μ` is stable for a market exactly when `μ.symm` is stable for
  its role swap, in which the women are the proposing side;
* `Market.isStable_comp_iff`: stability only depends on the order of the ranks, not on their
  values;
* `Market.IsStable.not_paretoImproves`: a stable matching is Pareto efficient;
* the change `Market.updateMan`, `Market.updateWoman` of one agent's stated preferences
  (Roth 2008, §2.1).
-/

@[expose] public section

namespace LeanPool.StableMatching

/-- A **marriage market** with strict preferences: each man ranks the women and staying single
(`none`), each woman ranks the men and `none`, by injective rank functions; a smaller rank is
better, and a partner ranked after `none` is unacceptable. -/
structure Market (M W : Type*) where
  /-- The rank a man gives to a woman, or to staying single. -/
  rankM : M → Option W → ℕ
  /-- The rank a woman gives to a man, or to staying single. -/
  rankW : W → Option M → ℕ
  /-- Men's preferences are strict. -/
  rankM_injective : ∀ m, Function.Injective (rankM m)
  /-- Women's preferences are strict. -/
  rankW_injective : ∀ w, Function.Injective (rankW w)

variable {M W : Type*}

namespace Market

variable (P : Market M W)

/-- A matching is **individually rational** when nobody is matched to an unacceptable
partner. -/
def IsIndividuallyRational (μ : M ≃. W) : Prop :=
  (∀ m, P.rankM m (μ m) ≤ P.rankM m none) ∧ ∀ w, P.rankW w (μ.symm w) ≤ P.rankW w none

/-- The pair `(m, w)` **blocks** `μ` when each prefers the other to the partner `μ` gives
them. -/
def Blocks (μ : M ≃. W) (m : M) (w : W) : Prop :=
  P.rankM m (some w) < P.rankM m (μ m) ∧ P.rankW w (some m) < P.rankW w (μ.symm w)

/-- A matching is **stable** when it is individually rational and no pair blocks it. -/
def IsStable (μ : M ≃. W) : Prop :=
  P.IsIndividuallyRational μ ∧ ∀ m w, ¬ P.Blocks μ m w

variable {P}

theorem rankM_eq_iff {m : M} {a b : Option W} : P.rankM m a = P.rankM m b ↔ a = b :=
  (P.rankM_injective m).eq_iff

theorem rankW_eq_iff {w : W} {a b : Option M} : P.rankW w a = P.rankW w b ↔ a = b :=
  (P.rankW_injective w).eq_iff

/-- A woman a man ranks no worse than being single, he ranks strictly better. -/
theorem rankM_some_lt_none {m : M} {w : W} (h : P.rankM m (some w) ≤ P.rankM m none) :
    P.rankM m (some w) < P.rankM m none :=
  lt_of_le_of_ne h fun h' ↦ Option.some_ne_none w (P.rankM_injective m h')

/-- A man a woman ranks no worse than being single, she ranks strictly better. -/
theorem rankW_some_lt_none {w : W} {m : M} (h : P.rankW w (some m) ≤ P.rankW w none) :
    P.rankW w (some m) < P.rankW w none :=
  lt_of_le_of_ne h fun h' ↦ Option.some_ne_none m (P.rankW_injective w h')

/-- A strict inequality from a weak one between ranks of different options. -/
theorem rankM_lt_of_le_of_ne {m : M} {a b : Option W} (h : P.rankM m a ≤ P.rankM m b)
    (hne : a ≠ b) : P.rankM m a < P.rankM m b :=
  lt_of_le_of_ne h fun h' ↦ hne (P.rankM_injective m h')

/-- A strict inequality from a weak one between ranks of different options. -/
theorem rankW_lt_of_le_of_ne {w : W} {a b : Option M} (h : P.rankW w a ≤ P.rankW w b)
    (hne : a ≠ b) : P.rankW w a < P.rankW w b :=
  lt_of_le_of_ne h fun h' ↦ hne (P.rankW_injective w h')

/-- An option a man ranks strictly better than being single is a woman. -/
theorem eq_some_of_rankM_lt_none {m : M} {a : Option W} (h : P.rankM m a < P.rankM m none) :
    ∃ w, a = some w := by
  cases a with
  | none => exact absurd h (lt_irrefl _)
  | some w => exact ⟨w, rfl⟩

/-- An option a woman ranks strictly better than being single is a man. -/
theorem eq_some_of_rankW_lt_none {w : W} {a : Option M} (h : P.rankW w a < P.rankW w none) :
    ∃ m, a = some m := by
  cases a with
  | none => exact absurd h (lt_irrefl _)
  | some m => exact ⟨m, rfl⟩

/-- At a stable matching, a woman whom a man strictly prefers to his partner is matched to a
man she strictly prefers to him. -/
theorem IsStable.rankW_lt {μ : M ≃. W} (hμ : P.IsStable μ) {m : M} {w : W}
    (h : P.rankM m (some w) < P.rankM m (μ m)) :
    P.rankW w (μ.symm w) < P.rankW w (some m) := by
  have h1 : P.rankW w (μ.symm w) ≤ P.rankW w (some m) :=
    not_lt.1 fun h' ↦ hμ.2 m w ⟨h, h'⟩
  refine P.rankW_lt_of_le_of_ne h1 fun h2 ↦ ?_
  rw [PEquiv.eq_some_iff] at h2
  rw [h2] at h
  exact lt_irrefl _ h

/-- At a stable matching, a man whom a woman strictly prefers to her partner is matched to a
woman he strictly prefers to her. -/
theorem IsStable.rankM_lt {μ : M ≃. W} (hμ : P.IsStable μ) {m : M} {w : W}
    (h : P.rankW w (some m) < P.rankW w (μ.symm w)) :
    P.rankM m (μ m) < P.rankM m (some w) := by
  have h1 : P.rankM m (μ m) ≤ P.rankM m (some w) :=
    not_lt.1 fun h' ↦ hμ.2 m w ⟨h', h⟩
  refine P.rankM_lt_of_le_of_ne h1 fun h2 ↦ ?_
  rw [← PEquiv.eq_some_iff] at h2
  rw [h2] at h
  exact lt_irrefl _ h

/-! ### Pareto efficiency -/

variable (P) in
/-- The matching `ν` **Pareto improves** on `μ` when every agent likes `ν` at least as well as
`μ` and some agent strictly prefers `ν`. -/
def ParetoImproves (ν μ : M ≃. W) : Prop :=
  (∀ m, P.rankM m (ν m) ≤ P.rankM m (μ m)) ∧ (∀ w, P.rankW w (ν.symm w) ≤ P.rankW w (μ.symm w)) ∧
    ((∃ m, P.rankM m (ν m) < P.rankM m (μ m)) ∨ ∃ w, P.rankW w (ν.symm w) < P.rankW w (μ.symm w))

/-- **A stable matching is Pareto efficient**: no matching makes every agent at least as well
off and some agent strictly better off (Roth 2008, §1). -/
theorem IsStable.not_paretoImproves {μ : M ≃. W} (hμ : P.IsStable μ) (ν : M ≃. W) :
    ¬ P.ParetoImproves ν μ := by
  rintro ⟨hM, hW, ⟨m, hm⟩ | ⟨w, hw⟩⟩
  · obtain ⟨w, hw⟩ := eq_some_of_rankM_lt_none (lt_of_lt_of_le hm (hμ.1.1 m))
    rw [hw] at hm
    have h1 := hμ.rankW_lt hm
    have h2 := hW w
    rw [(PEquiv.eq_some_iff ν).2 hw] at h2
    exact absurd (lt_of_le_of_lt h2 h1) (lt_irrefl _)
  · obtain ⟨m, hm⟩ := eq_some_of_rankW_lt_none (lt_of_lt_of_le hw (hμ.1.2 w))
    rw [hm] at hw
    have h1 := hμ.rankM_lt hw
    have h2 := hM m
    rw [(PEquiv.eq_some_iff ν).1 hm] at h2
    exact absurd (lt_of_le_of_lt h2 h1) (lt_irrefl _)

/-! ### Role swap -/

variable (P) in
/-- The **role swap** of a market: the women become the men and conversely. -/
def swap : Market W M where
  rankM := P.rankW
  rankW := P.rankM
  rankM_injective := P.rankW_injective
  rankW_injective := P.rankM_injective

@[simp] theorem swap_rankM : P.swap.rankM = P.rankW := rfl

@[simp] theorem swap_rankW : P.swap.rankW = P.rankM := rfl

@[simp] theorem swap_swap : P.swap.swap = P := rfl

theorem isIndividuallyRational_swap_iff {μ : M ≃. W} :
    P.swap.IsIndividuallyRational μ.symm ↔ P.IsIndividuallyRational μ := by
  simp [IsIndividuallyRational, and_comm]

theorem blocks_swap_iff {μ : M ≃. W} {m : M} {w : W} :
    P.swap.Blocks μ.symm w m ↔ P.Blocks μ m w := by
  simp [Blocks, and_comm]

/-- `μ` is stable for a market exactly when `μ.symm` is stable for its role swap. -/
theorem isStable_swap_iff {μ : M ≃. W} : P.swap.IsStable μ.symm ↔ P.IsStable μ := by
  rw [IsStable, IsStable, isIndividuallyRational_swap_iff]
  simp only [blocks_swap_iff]
  exact and_congr_right fun _ ↦ forall_comm

/-! ### Recomposing the ranks with strictly monotone maps -/

variable (P) in
/-- The market whose rank functions are those of `P` composed with strictly monotone maps of
`ℕ`, one for each agent. -/
def comp (f : M → ℕ → ℕ) (g : W → ℕ → ℕ) (hf : ∀ m, StrictMono (f m))
    (hg : ∀ w, StrictMono (g w)) : Market M W where
  rankM m := f m ∘ P.rankM m
  rankW w := g w ∘ P.rankW w
  rankM_injective m := (hf m).injective.comp (P.rankM_injective m)
  rankW_injective w := (hg w).injective.comp (P.rankW_injective w)

/-- **Stability is ordinal**: it is unchanged when every rank function is composed with a
strictly monotone map of `ℕ`. -/
theorem isStable_comp_iff {f : M → ℕ → ℕ} {g : W → ℕ → ℕ} (hf : ∀ m, StrictMono (f m))
    (hg : ∀ w, StrictMono (g w)) {μ : M ≃. W} :
    (P.comp f g hf hg).IsStable μ ↔ P.IsStable μ := by
  simp only [IsStable, IsIndividuallyRational, Blocks, comp, Function.comp_apply,
    (hf _).le_iff_le, (hg _).le_iff_le, (hf _).lt_iff_lt, (hg _).lt_iff_lt]

/-! ### Changing one agent's stated preferences -/

variable (P) in
/-- The market in which man `m` states the strict preferences `r` instead of his own. -/
def updateMan [DecidableEq M] (m : M) (r : Option W → ℕ) (hr : Function.Injective r) :
    Market M W where
  rankM := Function.update P.rankM m r
  rankW := P.rankW
  rankM_injective m' := by
    by_cases h : m' = m
    · subst h
      simpa using hr
    · simpa [Function.update_of_ne h] using P.rankM_injective m'
  rankW_injective := P.rankW_injective

variable (P) in
/-- The market in which woman `w` states the strict preferences `r` instead of her own. -/
def updateWoman [DecidableEq W] (w : W) (r : Option M → ℕ) (hr : Function.Injective r) :
    Market M W where
  rankM := P.rankM
  rankW := Function.update P.rankW w r
  rankM_injective := P.rankM_injective
  rankW_injective w' := by
    by_cases h : w' = w
    · subst h
      simpa using hr
    · simpa [Function.update_of_ne h] using P.rankW_injective w'

section UpdateMan

variable [DecidableEq M]

@[simp] theorem updateMan_rankW (m : M) (r : Option W → ℕ) (hr : Function.Injective r) :
    (P.updateMan m r hr).rankW = P.rankW := rfl

@[simp] theorem updateMan_rankM_self (m : M) (r : Option W → ℕ) (hr : Function.Injective r) :
    (P.updateMan m r hr).rankM m = r := by
  simp [updateMan]

theorem updateMan_rankM_of_ne {m m' : M} (h : m' ≠ m) (r : Option W → ℕ)
    (hr : Function.Injective r) : (P.updateMan m r hr).rankM m' = P.rankM m' := by
  simp [updateMan, Function.update_of_ne h]

/-- Stating one's own preferences changes nothing. -/
@[simp] theorem updateMan_self (m : M) : P.updateMan m (P.rankM m) (P.rankM_injective m) = P := by
  cases P
  simp [updateMan]

/-- A man's change of stated preferences is a woman's change in the role swap. -/
theorem swap_updateMan (m : M) (r : Option W → ℕ) (hr : Function.Injective r) :
    (P.updateMan m r hr).swap = P.swap.updateWoman m r hr := rfl

end UpdateMan

section UpdateWoman

variable [DecidableEq W]

@[simp] theorem updateWoman_rankM (w : W) (r : Option M → ℕ) (hr : Function.Injective r) :
    (P.updateWoman w r hr).rankM = P.rankM := rfl

@[simp] theorem updateWoman_rankW_self (w : W) (r : Option M → ℕ) (hr : Function.Injective r) :
    (P.updateWoman w r hr).rankW w = r := by
  simp [updateWoman]

theorem updateWoman_rankW_of_ne {w w' : W} (h : w' ≠ w) (r : Option M → ℕ)
    (hr : Function.Injective r) : (P.updateWoman w r hr).rankW w' = P.rankW w' := by
  simp [updateWoman, Function.update_of_ne h]

/-- Stating one's own preferences changes nothing. -/
@[simp] theorem updateWoman_self (w : W) :
    P.updateWoman w (P.rankW w) (P.rankW_injective w) = P := by
  cases P
  simp [updateWoman]

end UpdateWoman

end Market

end LeanPool.StableMatching
