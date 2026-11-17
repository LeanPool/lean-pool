/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/FiniteInjurySchedule.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.FiniteInjury

/-!
# Finite Injury Schedule
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.FiniteInjurySchedule
open FiniteInjury

theorem exists_missing (seen : Finset ℕ) : ∃ t, t ∉ seen := by
  refine ⟨seen.sup id + 1,?_⟩
  intro h
  have hh : seen.sup id + 1 ≤ seen.sup id := Finset.le_sup (f := id) h
  omega

/-- The least priority not yet present in the visited set. -/
noncomputable def visit (seen : Finset ℕ) : ℕ := Nat.find (exists_missing seen)

theorem visit_missing (seen : Finset ℕ) : visit seen ∉ seen := Nat.find_spec (exists_missing seen)

theorem before_visit (seen : Finset ℕ) {t : ℕ} (h : t < visit seen) : t ∈ seen := by
  have hh := Nat.find_min (exists_missing seen) h
  simpa using hh

/-- After an action, forget visits to priorities strictly above the acting priority. -/
def reset (seen : Finset ℕ) (a : Option ℕ) : Finset ℕ := match a with
  | none => seen
  | some t => seen.filter (fun i => i ≤ t)

/-- The visited-priority sets under the least-unvisited scheduling rule and injury resets. -/
noncomputable def seen (proposal : ℕ → Finset ℕ → Option ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | s+1 => reset (insert (visit (seen proposal s)) (seen proposal s)) (action proposal s)

/-- The least unvisited priority scheduled at the given stage. -/
noncomputable def scheduled (proposal : ℕ → Finset ℕ → Option ℕ) (s : ℕ) : ℕ :=
  visit (seen proposal s)

theorem reset_preserves {S : Finset ℕ} {a : Option ℕ} {t : ℕ}
    (h : t ∈ S) (ha : ∀ i < t, a ≠ some i) : t ∈ reset S a := by
  cases he : a with
  | none => exact h
  | some i =>
    have hti : t ≤ i := by
      by_contra hn
      exact ha i (by omega) he
    exact Finset.mem_filter.mpr ⟨h,hti⟩

theorem seen_persists {proposal : ℕ → Finset ℕ → Option ℕ} {s t : ℕ}
    (h : t ∈ seen proposal s) (ha : ∀ i < t, action proposal s ≠ some i) :
    t ∈ seen proposal (s+1) :=
  reset_preserves (Finset.mem_insert_of_mem h) ha

theorem visit_recorded {proposal : ℕ → Finset ℕ → Option ℕ} {s : ℕ}
    (ha : ∀ i < scheduled proposal s, action proposal s ≠ some i) :
    scheduled proposal s ∈ seen proposal (s+1) :=
  reset_preserves (Finset.mem_insert_self _ _) ha

theorem fill_prefix {proposal : ℕ → Finset ℕ → Option ℕ} {S t : ℕ}
    (hS : ∀ s, S ≤ s → ∀ i < t, action proposal s ≠ some i) :
    ∀ n, n ≤ t+1 → ∀ j < n, j ∈ seen proposal (S+n) := by
  intro n
  induction n with
  | zero => intro hn j hj; omega
  | succ n ih =>
    intro hn j hj
    have hn' : n ≤ t+1 := by omega
    have hjt : j ≤ t := by omega
    have ha : ∀ i < j, action proposal (S+n) ≠ some i :=
      fun i hi => hS (S+n) (Nat.le_add_right _ _) i (hi.trans_le hjt)
    by_cases hmem : j ∈ seen proposal (S+n)
    · exact seen_persists hmem ha
    · have hjn : j = n := by
        by_contra hne
        exact hmem (ih hn' j (by omega))
      have hvis : scheduled proposal (S+n) = j := by
        apply Nat.le_antisymm
        · exact Nat.find_min' (exists_missing _) hmem
        · by_contra hlt
          have hvlt : visit (seen proposal (S+n)) < n := by
            change ¬ j ≤ scheduled proposal (S+n) at hlt
            dsimp only [scheduled] at hlt
            omega
          exact visit_missing _ (ih hn' _ hvlt)
      have hv := visit_recorded (proposal := proposal) (s := S+n) (by simpa [hvis] using ha)
      simpa [hvis,Nat.add_assoc] using hv

theorem eventually_seen (proposal : ℕ → Finset ℕ → Option ℕ) (t : ℕ) :
    ∃ S, ∀ s, S ≤ s → t ∈ seen proposal s := by
  obtain ⟨S,hS⟩ := finite_injury proposal t
  have ht := fill_prefix hS (t+1) le_rfl t (Nat.lt_succ_self t)
  refine ⟨S+(t+1),fun s hs => ?_⟩
  induction s,hs using Nat.le_induction with
  | base => exact ht
  | succ s hs ih => exact seen_persists ih (hS s ((Nat.le_add_right S (t+1)).trans hs))

theorem seen_witness {proposal : ℕ → Finset ℕ → Option ℕ} {s t : ℕ}
    (h : t ∈ seen proposal s) : ∃ v, v < s ∧ scheduled proposal v = t ∧
      ∀ u, v ≤ u → u < s → ∀ i < t, action proposal u ≠ some i := by
  induction s with
  | zero => simp [seen] at h
  | succ s ih =>
    have hmem : t ∈ insert (scheduled proposal s) (seen proposal s) := by
      cases ha : action proposal s with
      | none => simpa [seen,ha,reset,scheduled] using h
      | some i => exact (Finset.mem_filter.mp (show t ∈ (insert (scheduled proposal s)
          (seen proposal s)).filter (fun j => j ≤ i) by simpa [seen,ha,reset,scheduled] using h)).1
    have hsafe : ∀ i < t, action proposal s ≠ some i := by
      intro i hi he
      have hh : t ≤ i := (Finset.mem_filter.mp (show t ∈ (insert (scheduled proposal s)
          (seen proposal s)).filter (fun j => j ≤ i) by simpa [seen,he,reset,scheduled] using h)).2
      omega
    rcases Finset.mem_insert.mp hmem with he | hm
    · refine ⟨s,Nat.lt_succ_self s,he.symm,fun u hu hus i hi => ?_⟩
      have hue : u = s := by omega
      exact hue ▸ hsafe i hi
    · obtain ⟨v,hv,he,hkeep⟩ := ih hm
      refine ⟨v,hv.trans (Nat.lt_succ_self s),he,fun u hu hus i hi => ?_⟩
      by_cases hue : u = s
      · exact hue ▸ hsafe i hi
      · exact hkeep u hu (by omega) i hi

theorem surviving_visit (proposal : ℕ → Finset ℕ → Option ℕ) (t : ℕ) :
    ∃ v, scheduled proposal v = t ∧
      ∀ u, v ≤ u → ∀ i < t, action proposal u ≠ some i := by
  obtain ⟨S,hS⟩ := finite_injury proposal t
  have ht := fill_prefix hS (t+1) le_rfl t (Nat.lt_succ_self t)
  obtain ⟨v,hv,he,hkeep⟩ := seen_witness ht
  refine ⟨v,he,fun u hu i hi => ?_⟩
  by_cases hus : u < S+(t+1)
  · exact hkeep u hu hus i hi
  · exact hS u (by omega) i hi

end TuringRigidity.FiniteInjurySchedule

end OAI
