/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.Defs
public import Mathlib.Data.EReal.Basic
import Mathlib.Order.Hom.WithTopBot

/-!
# Integer control trajectories and the Bellman principle

Kovač and Tang, §3.1–3.3. Numerators and denominators are kept unreduced.
The stopping condition includes both inequalities in the definition of a
terminal decomposition, even for an empty control list.
-/

@[expose] public section

namespace Egyptian.Control

/-- A rational remainder with its last chosen denominator. -/
structure State where
  /-- The numerator of the current remainder. -/
  p : ℕ
  /-- The denominator of the current remainder. -/
  q : ℕ
  /-- The preceding denominator, or zero at the initial state. -/
  last : ℕ
  deriving DecidableEq, Repr

/-- The state represents a positive rational remainder. -/
def Valid (s : State) : Prop := 0 < s.p ∧ 0 < s.q

/-- The reciprocal of the last denominator exceeds the remainder when it is defined. -/
def Interior (s : State) : Prop := s.last * s.p < s.q

/-- Clear denominators after subtracting the reciprocal of the chosen control. -/
def step (s : State) (x : ℕ) : State :=
  ⟨s.p * x - s.q, s.q * x, x⟩

/-- The next denominator satisfies the order convention and leaves a positive remainder. -/
def Legal (σ : Convention) (s : State) (x : ℕ) : Prop :=
  s.q < s.p * x ∧ 2 ≤ x ∧ σ.rel s.last x

/-- Apply a finite list of denominators as successive controls. -/
def finish : State → List ℕ → State
  | s, [] => s
  | s, x :: xs => finish (step s x) xs

/-- Every denominator in the list is legal at its corresponding intermediate state. -/
def Controls (σ : Convention) : State → List ℕ → Prop
  | _, [] => True
  | s, x :: xs => Legal σ s x ∧ Controls σ (step s x) xs

/-- The remainder is a unit fraction with a denominator larger than the last control. -/
def CanStop (s : State) (T : ℕ) : Prop :=
  2 ≤ T ∧ s.last < T ∧ s.q = s.p * T

/-- A legal control list ending at a state with the specified unit tail. -/
def Terminal (σ : Convention) (s : State) (xs : List ℕ) (T : ℕ) : Prop :=
  Controls σ s xs ∧ CanStop (finish s xs) T

theorem step_valid {σ s x} (hv : Valid s) (h : Legal σ s x) : Valid (step s x) :=
  ⟨Nat.sub_pos_of_lt h.1, Nat.mul_pos hv.2 (by have := h.2.1; omega : 0 < x)⟩

theorem step_fraction {σ s x} (hv : Valid s) (h : Legal σ s x) :
    ((step s x).p : ℚ) / (step s x).q = (s.p : ℚ) / s.q - unit x := by
  have hp : s.q ≤ s.p * x := h.1.le
  have hq : (s.q : ℚ) ≠ 0 := by exact_mod_cast hv.2.ne'
  have hx : (x : ℚ) ≠ 0 := by exact_mod_cast (show 0 < x by have := h.2.1; omega).ne'
  simp only [step, unit, Nat.cast_sub hp, Nat.cast_mul]
  field_simp

theorem finish_valid {σ} {s : State} {xs : List ℕ} (hv : Valid s)
    (hc : Controls σ s xs) : Valid (finish s xs) := by
  induction xs generalizing s with
  | nil => exact hv
  | cons x xs ih => exact ih (step_valid hv hc.1) hc.2

theorem finish_fraction {σ s xs} (hv : Valid s) (hc : Controls σ s xs) :
    ((finish s xs).p : ℚ) / (finish s xs).q = (s.p : ℚ) / s.q - recipSum xs := by
  induction xs generalizing s with
  | nil => simp [finish, recipSum]
  | cons x xs ih =>
    rw [finish, ih (step_valid hv hc.1) hc.2, step_fraction hv hc.1]
    simp [recipSum]
    ring

theorem terminal_identity {σ s xs T} (hv : Valid s) (ht : Terminal σ s xs T) :
    (s.p : ℚ) / s.q = recipSum xs + unit T := by
  have h := finish_fraction hv ht.1
  have hv' := finish_valid hv ht.1
  have hp : ((finish s xs).p : ℚ) ≠ 0 := by exact_mod_cast hv'.1.ne'
  have hT : (T : ℚ) ≠ 0 := by exact_mod_cast (show 0 < T by have := ht.2.1; omega).ne'
  rw [ht.2.2.2, Nat.cast_mul] at h
  have hrem : ((finish s xs).p : ℚ) / ((finish s xs).p * T) = unit T := by
    unfold unit
    field_simp
  rw [hrem] at h
  linarith

/-- Going to the least denominator strictly larger than q/p decreases the
cleared numerator at every nonunit remainder. -/
theorem greedy_step {s : State} (hv : Valid s) (hi : Interior s)
    (hsmall : s.p ≤ s.q) (hn : ¬s.p ∣ s.q) (σ : Convention) :
    let x := s.q / s.p + 1
    Legal σ s x ∧ (step s x).p < s.p ∧ Interior (step s x) ∧
      (step s x).p ≤ (step s x).q := by
  let x := s.q / s.p + 1
  have hdecomp := Nat.div_add_mod s.q s.p
  have hrem : 0 < s.q % s.p := Nat.pos_of_ne_zero (fun h => hn (Nat.dvd_of_mod_eq_zero h))
  have hrem' := Nat.mod_lt s.q hv.1
  have hx : 2 ≤ x := by
    have := Nat.div_pos hsmall hv.1
    dsimp [x]
    omega
  have hxP : s.p * x = s.p * (s.q / s.p) + s.p := by simp [x, Nat.mul_add]
  have hlarge : s.q < s.p * x := by omega
  have hdrop : s.p * x - s.q < s.p := by omega
  have hlast : s.last < x := by
    unfold Interior at hi
    by_contra! hh
    exact (not_le_of_gt hlarge) ((Nat.mul_le_mul_left s.p hh).trans
      ((Nat.mul_comm s.p s.last) ▸ hi.le))
  have hord : σ.rel s.last x := by cases σ <;> first | exact hlast.le | exact hlast
  have hlast' : Interior (step s x) := by
    change x * (s.p * x - s.q) < s.q * x
    rw [Nat.mul_comm]
    exact Nat.mul_lt_mul_of_pos_right (hdrop.trans_le hsmall) (by omega)
  refine ⟨⟨hlarge, hx, hord⟩, hdrop, hlast', ?_⟩
  change s.p * x - s.q ≤ s.q * x
  exact hdrop.le.trans (hsmall.trans (Nat.le_mul_of_pos_right _ (by omega)))

/-- Every admitted state with p ≤ q has a terminal decomposition under either
denominator convention. At reciprocal 1 the legal continuation is [2,3] to 6. -/
theorem terminal_exists_small (σ : Convention) (s : State) (hv : Valid s)
    (hi : Interior s) (hsmall : s.p ≤ s.q) : ∃ xs T, Terminal σ s xs T := by
  by_cases hd : s.p ∣ s.q
  · obtain ⟨T, hT⟩ := hd
    have hlast : s.last < T := by
      have h := hi
      unfold Interior at h
      rw [hT, Nat.mul_comm s.p T] at h
      exact Nat.lt_of_mul_lt_mul_right h
    by_cases htwo : 2 ≤ T
    · exact ⟨[], T, trivial, htwo, hlast, hT⟩
    · have hone : T = 1 := by omega
      have hlast0 : s.last = 0 := by omega
      have hpq : s.q = s.p := by simpa [hone] using hT
      have ha : σ.rel 0 2 := by cases σ <;> norm_num [Convention.rel]
      have hb : σ.rel 2 3 := by cases σ <;> norm_num [Convention.rel]
      refine ⟨[2, 3], 6, ?_⟩
      simp only [Terminal, Controls, Legal, finish, step, CanStop, hpq, hlast0]
      have hp := hv.1
      exact ⟨⟨⟨by omega, by decide, ha⟩, ⟨by omega, by decide, hb⟩, trivial⟩,
        by decide, by decide, by omega⟩
  · let x := s.q / s.p + 1
    obtain ⟨hlegal, hdrop, hi', hsmall'⟩ := greedy_step hv hi hsmall hd σ
    obtain ⟨xs, T, hcs, hterm⟩ :=
      terminal_exists_small σ (step s x) (step_valid hv hlegal) hi' hsmall'
    exact ⟨x :: xs, T, ⟨hlegal, hcs⟩, hterm⟩
termination_by s.p

/-- The discounted value of a fixed control string with terminal denominator T. -/
noncomputable def reward (H : ℕ → ℝ) (xs : List ℕ) (T : ℕ) : EReal :=
  (((1 / 2 : ℝ) ^ xs.length * H T : ℝ) : EReal)

/-- The Bellman function is defined on all states. The supremum of the empty
set in the extended reals is minus infinity. -/
noncomputable def value (σ : Convention) (H : ℕ → ℝ) (s : State) : EReal :=
  ⨆ (xs : List ℕ) (T : ℕ) (_ : Terminal σ s xs T), reward H xs T

/-- The supremum of the undiscounted rewards for admissible stops at the current state. -/
noncomputable def obstacle (H : ℕ → ℝ) (s : State) : EReal :=
  ⨆ (T : ℕ) (_ : CanStop s T), ((H T : ℝ) : EReal)

/-- The order automorphism of the extended reals that divides finite values by two. -/
noncomputable def discount : EReal ≃o EReal :=
  ((OrderIso.mulLeft₀ (1/2 : ℝ) (by norm_num)).withTopCongr).withBotCongr

theorem reward_cons (H : ℕ → ℝ) (x : ℕ) (xs : List ℕ) (T : ℕ) :
    reward H (x :: xs) T = discount (reward H xs T) := by
  apply congrArg Real.toEReal
  change ((1/2 : ℝ) ^ (xs.length + 1) * H T : ℝ) = (1/2) * ((1/2)^xs.length * H T)
  ring

theorem reward_le_value {H σ s xs T} (ht : Terminal σ s xs T) :
    reward H xs T ≤ value σ H s :=
  le_iSup_of_le xs (le_iSup_of_le T (le_iSup_of_le ht le_rfl))

/-- Formula (B2), with the obstacle defined using the legal terminal denominators. -/
theorem optimality (σ : Convention) (H : ℕ → ℝ) (s : State) :
    value σ H s = max (obstacle H s)
      (⨆ (x : ℕ) (_ : Legal σ s x), discount (value σ H (step s x))) := by
  apply le_antisymm
  · refine iSup_le fun xs => iSup_le fun T => iSup_le fun ht => ?_
    cases xs with
    | nil =>
      apply le_trans _ (le_max_left _ _)
      unfold obstacle
      apply le_iSup_of_le T
      apply le_iSup_of_le ht.2
      simp [reward]
    | cons x xs =>
      rw [reward_cons]
      apply le_trans _ (le_max_right _ _)
      apply le_iSup_of_le x
      apply le_iSup_of_le ht.1.1
      exact discount.monotone (reward_le_value ⟨ht.1.2, ht.2⟩)
  · refine max_le (iSup_le fun T => iSup_le fun hT => ?_)
      (iSup_le fun x => iSup_le fun hx => ?_)
    · simpa [reward] using (reward_le_value (H := H) (xs := []) (σ := σ) ⟨trivial, hT⟩)
    · unfold value
      simp only [OrderIso.map_iSup]
      refine iSup_le fun xs => iSup_le fun T => iSup_le fun ht => ?_
      rw [← reward_cons H x]
      exact reward_le_value ⟨⟨hx, ht.1⟩, ht.2⟩

/-- Formula (B3), proved by induction along an arbitrary finite control string. -/
theorem least_supersolution (σ : Convention) (H : ℕ → ℝ) (F : State → EReal)
    (stopBound : ∀ s T, CanStop s T → (H T : EReal) ≤ F s)
    (stepBound : ∀ s x, Legal σ s x → discount (F (step s x)) ≤ F s)
    (s : State) : value σ H s ≤ F s := by
  refine iSup_le fun xs => iSup_le fun T => iSup_le fun ht => ?_
  induction xs generalizing s with
  | nil => simpa [reward] using stopBound s T ht.2
  | cons x xs ih =>
    rw [reward_cons]
    exact (discount.monotone (ih (step s x) ⟨ht.1.2, ht.2⟩)).trans (stepBound s x ht.1.1)

end Egyptian.Control
