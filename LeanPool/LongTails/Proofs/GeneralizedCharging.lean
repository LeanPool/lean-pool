/-
Copyright (c) 2026 LongTails contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Tyurin, QuocViet Pham, Valentin Khrulkov, Ivan Oseledets
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.List.Nodup
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
Adapted from k3nfalt/longtails, commit 269cbc764dd36851fd0b64f2f950f329ee127de4.
Modified for Lean Pool: module visibility, namespace isolation, and current Mathlib.
-/

@[expose] public section

namespace LongTails.OracleTemplate.GeneralizedAccelerated

/-- An active block and earlier blocks used to count curvature updates. -/
structure ChargingState where
  /-- Start index and count of the active charging block. -/
  active : ℕ × ℕ
  /-- Completed charging blocks, in reverse chronological order. -/
  past : List (ℕ × ℕ)

/-- Partition the iteration history into blocks starting at upward curvature changes. -/
def charging (up : ℕ → Bool) : ℕ → ChargingState
  | 0 => ⟨(0, 0), []⟩
  | n + 1 =>
    let s := charging up n
    if up (n + 1) then ⟨(n + 1, 1), s.active :: s.past⟩
    else ⟨(s.active.1, s.active.2 + 1), s.past⟩

/-- The exponentially weighted inverse-curvature mass of a block. -/
noncomputable def chargeValue (w : ℕ → ℝ) (b : ℕ × ℕ) : ℝ :=
  2 ^ b.2 * w b.1

/-- The sum of the active and completed block charges. -/
noncomputable def chargeTotal (w : ℕ → ℝ) (s : ChargingState) : ℝ :=
  chargeValue w s.active + (s.past.map (chargeValue w)).sum

/-- The inverse-curvature mass accumulated at downward curvature changes. -/
noncomputable def downMass (up : ℕ → Bool) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), if up i then 0 else w i

lemma charging_mass_succ (up : ℕ → Bool) (w : ℕ → ℝ) (n : ℕ) :
    downMass up w (n + 1) = downMass up w n + (if up (n + 1) then 0 else w (n + 1)) := by
  exact Finset.sum_range_succ _ _

lemma charging_up {up : ℕ → Bool} (w : ℕ → ℝ) {n : ℕ} (h : up (n + 1) = true) :
    chargeValue w (charging up (n + 1)).active = 2 * w (n + 1) ∧
    chargeTotal w (charging up (n + 1)) = chargeTotal w (charging up n) + 2 * w (n + 1) := by
  simp [charging, h, chargeValue, chargeTotal]
  ring

lemma charging_down {up : ℕ → Bool} (w : ℕ → ℝ) {n : ℕ} (h : up (n + 1) = false) :
    chargeValue w (charging up (n + 1)).active = 2 * chargeValue w (charging up n).active ∧
    chargeTotal w (charging up (n + 1)) =
      chargeTotal w (charging up n) + chargeValue w (charging up n).active := by
  simp only [charging, h, Bool.false_eq_true, ↓reduceIte, chargeValue, pow_succ,
    chargeTotal]
  constructor <;> ring

lemma charging_potential {up : ℕ → Bool} {w : ℕ → ℝ}
    (hfirst : up 0 = false) (hw : ∀ n, 0 ≤ w n)
    (hnext : ∀ n, w (n + 1) = if up n then w n / 4 else 4 * w n) (n : ℕ) :
    chargeValue w (charging up n).active ≤ 16 * w n ∧
    (up n = true → chargeValue w (charging up n).active = 2 * w n) ∧
    chargeTotal w (charging up n) + (8 / 3) * w (n + 1) ≤ 16 * downMass up w n := by
  induction n with
  | zero =>
    have hn := hnext 0
    simp only [hfirst, Bool.false_eq_true, ↓reduceIte] at hn
    simp only [charging, chargeValue, pow_zero, one_mul, chargeTotal,
      List.map_nil, List.sum_nil, add_zero, downMass, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, hfirst, Bool.false_eq_true, ↓reduceIte,
      false_implies, true_and]
    constructor <;> nlinarith [hw 0]
  | succ n ih =>
    have hm := charging_mass_succ up w n
    have hn := hnext (n + 1)
    cases hu : up (n + 1) with
    | true =>
      obtain ⟨ha, hs⟩ := charging_up w hu
      simp only [hu, ↓reduceIte, add_zero] at hm hn
      refine ⟨?_, fun _ => ha, ?_⟩
      · rw [ha]
        nlinarith [hw (n + 1)]
      · rw [hs, hn, hm]
        linarith [ih.2.2]
    | false =>
      obtain ⟨ha, hs⟩ := charging_down w hu
      simp only [hu, Bool.false_eq_true, ↓reduceIte] at hm hn
      have hlast : chargeValue w (charging up n).active ≤ 8 * w (n + 1) := by
        have hp := hnext n
        cases hpup : up n with
        | false =>
          simp only [hpup, Bool.false_eq_true, ↓reduceIte] at hp
          nlinarith [ih.1, hw n]
        | true =>
          simp only [hpup, ↓reduceIte] at hp
          rw [ih.2.1 hpup]
          linarith
      refine ⟨?_, by simp [], ?_⟩
      · rw [ha]
        linarith
      · rw [hs, hn, hm]
        linarith [ih.2.2]

lemma charging_total_le {up : ℕ → Bool} {w : ℕ → ℝ}
    (hfirst : up 0 = false) (hw : ∀ n, 0 ≤ w n)
    (hnext : ∀ n, w (n + 1) = if up n then w n / 4 else 4 * w n) (n : ℕ) :
    chargeTotal w (charging up n) ≤ 16 * downMass up w n := by
  have h := (charging_potential hfirst hw hnext n).2.2
  nlinarith [hw (n + 1)]

/-- The active block followed by all completed blocks. -/
def chargingEntries (s : ChargingState) : List (ℕ × ℕ) := s.active :: s.past

lemma charging_indices (up : ℕ → Bool) (n : ℕ) :
    (charging up n).active.1 ≤ n ∧
    (∀ b ∈ (charging up n).past, b.1 < (charging up n).active.1) ∧
    (chargingEntries (charging up n)).Pairwise (fun a b => b.1 < a.1) ∧
    (∀ b ∈ chargingEntries (charging up n), b.1 = 0 ∨ up b.1 = true) := by
  induction n with
  | zero => simp [charging, chargingEntries]
  | succ n ih =>
    cases hu : up (n + 1) with
    | false =>
      simp only [charging, hu, Bool.false_eq_true, ↓reduceIte, chargingEntries,
        List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at ih ⊢
      exact ⟨by omega, ih.2.1, ⟨ih.2.2.1.1, ih.2.2.1.2⟩,
        ih.2.2.2.1, ih.2.2.2.2⟩
    | true =>
      have hb : ∀ b ∈ chargingEntries (charging up n), b.1 < n + 1 := by
        intro b h
        rcases List.mem_cons.mp h with h | h
        · subst b; omega
        · have ht := ih.2.1 b h; omega
      change _ ∧ _ ∧ _ ∧ _
      simp only [charging, hu, ↓reduceIte, chargingEntries]
      refine ⟨le_rfl, hb, List.pairwise_cons.mpr ⟨hb, ih.2.2.1⟩, ?_⟩
      intro b h
      rcases List.mem_cons.mp h with h | h
      · subst b; exact Or.inr hu
      · exact ih.2.2.2 b h

lemma charging_index_le (up : ℕ → Bool) (n : ℕ) (b : ℕ × ℕ)
    (hb : b ∈ chargingEntries (charging up n)) : b.1 ≤ n := by
  have h := charging_indices up n
  rcases List.mem_cons.mp hb with hb | hb
  · subst b; exact h.1
  · exact (h.2.1 b hb).le.trans h.1

/-- The total charge from blocks whose start precedes a given iteration. -/
noncomputable def chargePrefix (w : ℕ → ℝ) (s : ChargingState) (t : ℕ) : ℝ :=
  (((chargingEntries s).filter (fun b => b.1 < t)).map (chargeValue w)).sum

lemma charging_prefix_bound {up : ℕ → Bool} {w B : ℕ → ℝ}
    (hB0 : 0 ≤ B 0) (hB : Monotone B) (htotal : ∀ n, chargeTotal w (charging up n) ≤ B n) (n : ℕ) :
    ∀ b ∈ chargingEntries (charging up n), chargePrefix w (charging up n) b.1 ≤ B b.1 := by
  induction n with
  | zero =>
    intro b hb
    simp only [charging, chargingEntries, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst b
    simpa [chargePrefix, charging, chargingEntries] using hB0
  | succ n ih =>
    intro b hb
    cases hu : up (n + 1) with
    | true =>
      have he : chargingEntries (charging up (n + 1)) =
          (n + 1, 1) :: chargingEntries (charging up n) := by
        simp [charging, hu, chargingEntries]
      rw [he] at hb
      rcases List.mem_cons.mp hb with hb | hb
      · subst b
        have hfilter : (chargingEntries (charging up n)).filter
            (fun b => b.1 < n + 1) = chargingEntries (charging up n) := by
          apply List.filter_eq_self.mpr
          intro b hb
          simpa using Nat.lt_succ_of_le (charging_index_le up n b hb)
        have hp : chargePrefix w (charging up (n + 1)) (n + 1) =
            chargeTotal w (charging up n) := by
          unfold chargePrefix
          rw [he]
          simp only [List.filter_cons, lt_self_iff_false, decide_false,
            Bool.false_eq_true, ↓reduceIte]
          rw [hfilter]
          rfl
        rw [hp]
        exact (htotal n).trans (hB (Nat.le_succ n))
      · have ht : ¬n + 1 < b.1 := by
          have hi := charging_index_le up n b hb
          omega
        have hp : chargePrefix w (charging up (n + 1)) b.1 =
            chargePrefix w (charging up n) b.1 := by
          simp [chargePrefix, he, ht]
        rw [hp]
        exact ih b hb
    | false =>
      have hi := charging_indices up n
      have he : chargingEntries (charging up (n + 1)) =
          ((charging up n).active.1, (charging up n).active.2 + 1) ::
            (charging up n).past := by
        simp [charging, hu, chargingEntries]
      rw [he] at hb
      have hle : b.1 ≤ (charging up n).active.1 := by
        rcases List.mem_cons.mp hb with hb | hb
        · subst b; exact le_rfl
        · exact (hi.2.1 b hb).le
      have hp : chargePrefix w (charging up (n + 1)) b.1 =
          chargePrefix w (charging up n) b.1 := by
        unfold chargePrefix
        rw [he]
        simp [chargingEntries, not_lt_of_ge hle]
      rw [hp]
      rcases List.mem_cons.mp hb with hb | hb
      · subst b
        exact ih (charging up n).active List.mem_cons_self
      · exact ih b (List.mem_cons_of_mem _ hb)

lemma charging_count (up : ℕ → Bool) (n : ℕ) :
    (charging up n).active.2 + ((charging up n).past.map Prod.snd).sum = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases hu : up (n + 1) <;>
      simp [charging, hu, List.map_cons, List.sum_cons] <;> omega

lemma charging_nodup (up : ℕ → Bool) (n : ℕ) :
    (chargingEntries (charging up n)).Nodup := by
  have h := (charging_indices up n).2.2.1
  exact h.imp (fun {a b} hab he => by subst b; exact (Nat.lt_irrefl _ hab))

lemma charging_unique_index (up : ℕ → Bool) (n : ℕ) :
    Set.InjOn Prod.fst {b | b ∈ chargingEntries (charging up n)} := by
  have h : ((chargingEntries (charging up n)).map Prod.fst).Pairwise
      (fun a b => b < a) := List.pairwise_map.mpr (charging_indices up n).2.2.1
  have hn : ((chargingEntries (charging up n)).map Prod.fst).Nodup :=
    h.imp (fun {a b} hab => Ne.symm (Nat.ne_of_lt hab))
  exact (List.nodup_map_iff_inj_on (charging_nodup up n)).mp hn

/-- The finite set of active and completed charging blocks. -/
def chargingSet (up : ℕ → Bool) (n : ℕ) : Finset (ℕ × ℕ) :=
  (chargingEntries (charging up n)).toFinset

lemma charging_sum (up : ℕ → Bool) (n : ℕ) (w : ℕ → ℝ) :
    (∑ b ∈ chargingSet up n, chargeValue w b) = chargeTotal w (charging up n) := by
  rw [chargingSet, List.sum_toFinset _ (charging_nodup up n)]
  rfl

lemma charging_sum_count (up : ℕ → Bool) (n : ℕ) :
    (∑ b ∈ chargingSet up n, b.2) = n := by
  rw [chargingSet, List.sum_toFinset _ (charging_nodup up n)]
  exact charging_count up n

lemma charging_sum_prefix (up : ℕ → Bool) (n : ℕ) (w : ℕ → ℝ) (t : ℕ) :
    (∑ b ∈ (chargingSet up n).filter (fun b => b.1 < t), chargeValue w b) =
      chargePrefix w (charging up n) t := by
  have h := List.sum_toFinset (chargeValue w)
    ((charging_nodup up n).filter (fun b => decide (b.1 < t)))
  simpa only [List.toFinset_filter, decide_eq_true_eq, chargingSet, chargePrefix] using h

end LongTails.OracleTemplate.GeneralizedAccelerated
