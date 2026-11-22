/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.StableMatching.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Basic.Countable.Basic
public import Mathlib.Data.Fintype.EquivFin

/-!
# Roth's impossibility theorem

`not_exists_truthful_stable_mechanism`: with at least two men and two women, no mechanism that
returns a stable matching for every market makes truth-telling a dominant strategy for every
agent (A. E. Roth, *The economics of matching: stability and incentives*, Math. Oper. Res. 7
(1982), Theorem 3; A. E. Roth, *Deferred acceptance algorithms: history, theory, practice, and
open questions*, Internat. J. Game Theory 36 (2008), Theorem 6).

The proof embeds Roth's 2 × 2 example in the given sets of agents: men `m₁: w₁ > w₂`,
`m₂: w₂ > w₁`, women `w₁: m₂ > m₁`, `w₂: m₁ > m₂`, everyone acceptable to them, and every other
agent accepting nobody. If the mechanism does not give `w₁` her first choice `m₂`, then `w₁`
gets him by declaring `m₁` unacceptable, since `(m₁, w₂), (m₂, w₁)` is then the only stable
matching (`symm_eq_some_of_isStable`); otherwise `m₂` gets `w₂` instead of `w₁` by declaring
`w₁` unacceptable, which is the same situation in the role swap.
-/

@[expose] public section

namespace LeanPool.StableMatching

variable {α : Type*} [DecidableEq α]

/-- The rank function preferring `a`, then `b`, then staying single, then everyone else, in the
order given by `e`. -/
def rankTwo (e : α → ℕ) (a b : α) : Option α → ℕ
  | none => 2
  | some x => if x = a then 0 else if x = b then 1 else e x + 3

/-- The rank function preferring `a`, then staying single, then `b`, then everyone else, in the
order given by `e`. -/
def rankOne (e : α → ℕ) (a b : α) : Option α → ℕ
  | none => 1
  | some x => if x = a then 0 else if x = b then 2 else e x + 3

/-- The rank function preferring staying single to everyone, ordered by `e`. -/
def rankZero (e : α → ℕ) : Option α → ℕ
  | none => 0
  | some x => e x + 1

variable {e : α → ℕ} {a b : α}

theorem rankTwo_injective (he : Function.Injective e) (hab : a ≠ b) :
    Function.Injective (rankTwo e a b) := by
  rintro (_ | x) (_ | y) h <;> simp only [rankTwo] at h
  · rfl
  · split_ifs at h <;> omega
  · split_ifs at h <;> omega
  · congr 1
    split_ifs at h <;>
      first | (subst_vars; rfl) | omega | exact he (by omega)

theorem rankOne_injective (he : Function.Injective e) (hab : a ≠ b) :
    Function.Injective (rankOne e a b) := by
  rintro (_ | x) (_ | y) h <;> simp only [rankOne] at h
  · rfl
  · split_ifs at h <;> omega
  · split_ifs at h <;> omega
  · congr 1
    split_ifs at h <;>
      first | (subst_vars; rfl) | omega | exact he (by omega)

omit [DecidableEq α] in
theorem rankZero_injective (he : Function.Injective e) : Function.Injective (rankZero e) := by
  rintro (_ | x) (_ | y) h <;> simp only [rankZero] at h
  · rfl
  · omega
  · omega
  · exact congrArg some (he (by omega))

@[simp] theorem rankTwo_none : rankTwo e a b none = 2 := rfl

@[simp] theorem rankTwo_some_left : rankTwo e a b (some a) = 0 := by simp [rankTwo]

theorem rankTwo_some_right (hab : a ≠ b) : rankTwo e a b (some b) = 1 := by
  simp [rankTwo, hab.symm]

theorem rankTwo_eq_zero_iff {o : Option α} : rankTwo e a b o = 0 ↔ o = some a := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rankTwo_some_left⟩
  rcases o with _ | x
  · simp at h
  · simp only [rankTwo] at h
    split_ifs at h with h1
    exact h1 ▸ rfl

theorem rankTwo_le_one_iff {o : Option α} : rankTwo e a b o ≤ 1 ↔ o = some a ∨ o = some b := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases o with _ | x
    · simp at h
    · simp only [rankTwo] at h
      split_ifs at h with h1 h2
      · exact Or.inl (h1 ▸ rfl)
      · exact Or.inr (h2 ▸ rfl)
      · omega
  · rintro (rfl | rfl)
    · simp
    · simp only [rankTwo]
      split_ifs <;> omega

theorem rankTwo_le_two_iff {o : Option α} :
    rankTwo e a b o ≤ 2 ↔ o = some a ∨ o = some b ∨ o = none := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases o with _ | x
    · exact Or.inr (Or.inr rfl)
    · simp only [rankTwo] at h
      split_ifs at h with h1 h2
      · exact Or.inl (h1 ▸ rfl)
      · exact Or.inr (Or.inl (h2 ▸ rfl))
      · omega
  · rintro (rfl | rfl | rfl)
    · simp
    · simp only [rankTwo]
      split_ifs <;> omega
    · simp

@[simp] theorem rankOne_none : rankOne e a b none = 1 := rfl

@[simp] theorem rankOne_some_left : rankOne e a b (some a) = 0 := by simp [rankOne]

theorem rankOne_le_one_iff {o : Option α} : rankOne e a b o ≤ 1 ↔ o = some a ∨ o = none := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases o with _ | x
    · exact Or.inr rfl
    · simp only [rankOne] at h
      split_ifs at h with h1 h2
      · exact Or.inl (h1 ▸ rfl)
      · omega
      · omega
  · rintro (rfl | rfl) <;> simp

namespace Market

variable {X Y : Type*} [DecidableEq X] [DecidableEq Y]

/-- **Roth's example after a misreport.** In a market with men `x₁: y₁ > y₂`, `x₂: y₂ > y₁` and
women `y₁: x₂ > ∅ > x₁`, `y₂: x₁ > x₂`, every stable matching matches `y₁` with `x₂`. -/
theorem symm_eq_some_of_isStable {Q : Market X Y} {eX : X → ℕ} {eY : Y → ℕ} {x₁ x₂ : X}
    {y₁ y₂ : Y} (hx : x₁ ≠ x₂) (hy : y₁ ≠ y₂) (hx₁ : Q.rankM x₁ = rankTwo eY y₁ y₂)
    (hx₂ : Q.rankM x₂ = rankTwo eY y₂ y₁) (hy₁ : Q.rankW y₁ = rankOne eX x₂ x₁)
    (hy₂ : Q.rankW y₂ = rankTwo eX x₁ x₂) {ν : X ≃. Y} (hν : Q.IsStable ν) :
    ν.symm y₁ = some x₂ := by
  by_contra hne
  have h1 : ν.symm y₁ = none := by
    have := hν.1.2 y₁
    rw [hy₁, rankOne_none, rankOne_le_one_iff] at this
    exact this.resolve_left hne
  have h2 : ν x₂ = some y₂ := by
    have hnb := hν.2 x₂ y₁
    simp only [Blocks, h1, hx₂, hy₁, rankOne_some_left, rankOne_none, rankTwo_some_right hy.symm,
      Nat.lt_one_iff, and_true, not_lt] at hnb
    rcases rankTwo_le_one_iff.1 hnb with h | h
    · exact h
    · exact absurd ((PEquiv.eq_some_iff ν).2 h) hne
  have h3 : ν x₁ = none := by
    have := hν.1.1 x₁
    rw [hx₁, rankTwo_none, rankTwo_le_two_iff] at this
    rcases this with h | h | h
    · rw [(PEquiv.eq_some_iff ν).2 h] at h1
      exact absurd h1 (Option.some_ne_none _)
    · exact absurd (ν.inj h h2) hx
    · exact h
  refine hν.2 x₁ y₂ ⟨?_, ?_⟩
  · rw [h3, hx₁, rankTwo_none, rankTwo_some_right hy]
    omega
  · rw [(PEquiv.eq_some_iff ν).2 h2, hy₂, rankTwo_some_left, rankTwo_some_right hx]
    omega

end Market

open Market in
/-- **Roth's impossibility theorem.** With at least two men and two women, no mechanism that
returns a stable matching for every market makes truth-telling a dominant strategy for every
agent. -/
theorem not_exists_truthful_stable_mechanism {M W : Type*} [Fintype M] [Fintype W]
    [DecidableEq M] [DecidableEq W] (hM : 2 ≤ Fintype.card M) (hW : 2 ≤ Fintype.card W) :
    ¬ ∃ h : Market M W → (M ≃. W), (∀ P : Market M W, P.IsStable (h P)) ∧
      (∀ (P : Market M W) (m : M) (r : Option W → ℕ) (hr : Function.Injective r),
        P.rankM m (h P m) ≤ P.rankM m (h (P.updateMan m r hr) m)) ∧
      ∀ (P : Market M W) (w : W) (r : Option M → ℕ) (hr : Function.Injective r),
        P.rankW w ((h P).symm w) ≤ P.rankW w ((h (P.updateWoman w r hr)).symm w) := by
  rintro ⟨h, hstab, hman, hwoman⟩
  obtain ⟨m₁, m₂, hm⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card M)
  obtain ⟨w₁, w₂, hw⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card W)
  obtain ⟨eM, heM⟩ := Countable.exists_injective_nat M
  obtain ⟨eW, heW⟩ := Countable.exists_injective_nat W
  let P : Market M W :=
    { rankM := fun m ↦
        if m = m₁ then rankTwo eW w₁ w₂ else if m = m₂ then rankTwo eW w₂ w₁ else rankZero eW
      rankW := fun w ↦
        if w = w₁ then rankTwo eM m₂ m₁ else if w = w₂ then rankTwo eM m₁ m₂ else rankZero eM
      rankM_injective := fun m ↦ by
        split_ifs
        exacts [rankTwo_injective heW hw, rankTwo_injective heW hw.symm, rankZero_injective heW]
      rankW_injective := fun w ↦ by
        split_ifs
        exacts [rankTwo_injective heM hm.symm, rankTwo_injective heM hm, rankZero_injective heM] }
  have hP₁ : P.rankM m₁ = rankTwo eW w₁ w₂ := by simp [P]
  have hP₂ : P.rankM m₂ = rankTwo eW w₂ w₁ := by simp [P, hm.symm]
  have hQ₁ : P.rankW w₁ = rankTwo eM m₂ m₁ := by simp [P]
  have hQ₂ : P.rankW w₂ = rankTwo eM m₁ m₂ := by simp [P, hw.symm]
  by_cases hc : (h P).symm w₁ = some m₂
  · -- `m₂` declares `w₁` unacceptable
    have hr := rankOne_injective heW hw.symm
    set P₂ := P.updateMan m₂ (rankOne eW w₂ w₁) hr
    have key : (h P₂).symm.symm m₂ = some w₂ :=
      symm_eq_some_of_isStable (Q := P₂.swap) (eX := eW) (eY := eM) (x₁ := w₁) (x₂ := w₂)
        (y₁ := m₂) (y₂ := m₁) hw hm.symm (by simpa [P₂] using hQ₁) (by simpa [P₂] using hQ₂)
        (by simp [P₂]) (by simpa [P₂, updateMan_rankM_of_ne hm] using hP₁)
        (isStable_swap_iff.2 (hstab P₂))
    have := hman P m₂ (rankOne eW w₂ w₁) hr
    rw [PEquiv.symm_symm] at key
    rw [(PEquiv.eq_some_iff _).1 hc, key, hP₂, rankTwo_some_left, rankTwo_some_right hw.symm]
      at this
    omega
  · -- `w₁` declares `m₁` unacceptable
    have hr := rankOne_injective heM hm.symm
    set P₁ := P.updateWoman w₁ (rankOne eM m₂ m₁) hr
    have key : (h P₁).symm w₁ = some m₂ :=
      symm_eq_some_of_isStable (Q := P₁) (eX := eM) (eY := eW) hm hw (by simpa [P₁] using hP₁)
        (by simpa [P₁] using hP₂) (by simp [P₁])
        (by simpa [P₁, updateWoman_rankW_of_ne hw.symm] using hQ₂) (hstab P₁)
    have := hwoman P w₁ (rankOne eM m₂ m₁) hr
    rw [key, hQ₁, rankTwo_some_left, Nat.le_zero, rankTwo_eq_zero_iff] at this
    exact hc this

end LeanPool.StableMatching
