/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/FiniteInjury.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.CodingForcing
public import Mathlib.Data.Finset.Filter

/-!
# Finite Injury
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.FiniteInjury

def accept (done : Finset ℕ) (proposal : Option ℕ) : Option ℕ :=
  proposal.bind (fun t => if t ∈ done then none else some t)

def update (done : Finset ℕ) (action : Option ℕ) : Finset ℕ :=
  match action with
  | none => done
  | some t => insert t (done.filter (fun i => i < t))

def state (proposal : ℕ → Finset ℕ → Option ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | s+1 => update (state proposal s) (accept (state proposal s) (proposal s (state proposal s)))

def action (proposal : ℕ → Finset ℕ → Option ℕ) (s : ℕ) : Option ℕ :=
  accept (state proposal s) (proposal s (state proposal s))

theorem state_succ (proposal : ℕ → Finset ℕ → Option ℕ) (s : ℕ) :
    state proposal (s+1) = update (state proposal s) (action proposal s) := rfl

theorem action_not_done {proposal : ℕ → Finset ℕ → Option ℕ} {s t : ℕ}
    (h : action proposal s = some t) : t ∉ state proposal s := by
  unfold action accept at h
  cases hp : proposal s (state proposal s) with
  | none => simp [hp] at h
  | some i =>
    simp only [hp, Option.bind_some] at h
    split at h
    · simp at h
    · rename_i hi
      have he := Option.some.inj h
      exact he ▸ hi

theorem done_after_action {proposal : ℕ → Finset ℕ → Option ℕ} {s t : ℕ}
    (h : action proposal s = some t) : t ∈ state proposal (s+1) := by
  simp [state_succ, h, update]

theorem done_persists {proposal : ℕ → Finset ℕ → Option ℕ} {s t : ℕ}
    (h : t ∈ state proposal s)
    (hsmall : ∀ i < t, action proposal s ≠ some i) : t ∈ state proposal (s+1) := by
  rw [state_succ]
  cases ha : action proposal s with
  | none => simpa [ha, update] using h
  | some i =>
    have hle : t ≤ i := by
      by_contra hn
      exact hsmall i (by omega) ha
    simp only [update, Finset.mem_insert, Finset.mem_filter]
    rcases eq_or_lt_of_le hle with he | he
    · exact Or.inl he
    · exact Or.inr ⟨h, he⟩

theorem done_persists_from {proposal : ℕ → Finset ℕ → Option ℕ} {S t : ℕ}
    (h : t ∈ state proposal S)
    (hsmall : ∀ s, S ≤ s → ∀ i < t, action proposal s ≠ some i) :
    ∀ s, S ≤ s → t ∈ state proposal s := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => exact h
  | succ s hs ih => exact done_persists ih (hsmall s hs)

theorem finite_injury (proposal : ℕ → Finset ℕ → Option ℕ) (t : ℕ) :
    ∃ S, ∀ s, S ≤ s → ∀ i < t, action proposal s ≠ some i := by
  induction t with
  | zero => exact ⟨0, fun _ _ _ hi => by omega⟩
  | succ t ih =>
    obtain ⟨S, hS⟩ := ih
    by_cases hact : ∃ s, S ≤ s ∧ action proposal s = some t
    · obtain ⟨s, hs, ha⟩ := hact
      have hdone := done_after_action ha
      have hpersist := done_persists_from hdone
        (fun u hu => hS u (hs.trans (Nat.le_succ s |>.trans hu)))
      refine ⟨s+1, ?_⟩
      intro u hu i hi he
      by_cases hit : i = t
      · subst i
        exact action_not_done he (hpersist u hu)
      · exact hS u (hs.trans (Nat.le_succ s |>.trans hu)) i (by omega) he
    · refine ⟨S, ?_⟩
      intro s hs i hi he
      by_cases hit : i = t
      · exact hact ⟨s, hs, hit ▸ he⟩
      · exact hS s hs i (by omega) he

open CodingForcing

def atLevel (p : Condition) (t : ℕ) : Condition :=
  ⟨p.left, p.right, p.sameLength, t⟩

theorem level_mono {A : ℕ → Oracle} {p q : Condition} {t k : ℕ}
    (h : Extends A (atLevel p t) (atLevel q t)) (hk : k ≤ t) :
    Extends A (atLevel p k) (atLevel q k) := by
  refine ⟨h.1, h.2.1, le_rfl, ?_⟩
  intro m hm hlen
  exact h.2.2.2 m ⟨hm.1, hm.2.1.trans_le hk, hm.2.2⟩ hlen

theorem eventual_level_chain (A : ℕ → Oracle)
    (proposal : ℕ → Finset ℕ → Option ℕ) (p : ℕ → Condition)
    (hstep : ∀ s k, k ≤ s →
      (∀ t, action proposal s = some t → k ≤ t) →
      Extends A (atLevel (p s) k) (atLevel (p (s + 1)) k)) (k : ℕ) :
    ∃ S, ∀ s, S ≤ s → ∀ u, s ≤ u →
      Extends A (atLevel (p s) k) (atLevel (p u) k) := by
  obtain ⟨S, hS⟩ := finite_injury proposal k
  refine ⟨max S k, ?_⟩
  intro s hs u hu
  induction u, hu using Nat.le_induction with
  | base => exact extends_refl A _
  | succ u hu ih =>
    apply extends_trans ih
    apply hstep u k ((le_max_right S k).trans (hs.trans hu))
    intro t ht
    by_contra hn
    exact hS u ((le_max_left S k).trans (hs.trans hu)) t (by omega) ht

end TuringRigidity.FiniteInjury

end OAI
