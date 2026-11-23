/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.Entrance
public import LeanPool.Egyptian.BellmanScore
public import LeanPool.Egyptian.BranchCutoff

/-!
# Passing from proper to improper rational targets

Cut each terminal decomposition at the first entrance. Optimize its suffix,
then optimize over the finitely many entrance blocks whose length can compete
with a fixed witness. The final clause records finiteness of the entrance
blocks of *all* optimal decompositions, including ties.
-/

@[expose] public section

namespace Egyptian.Control

/-- The form of the proper-state majorant and attainment used at the
first entrance. It includes both conventions and the actual optimizer. -/
def ProperWinners (σ : Convention) : Prop :=
  ∀ s : State, Valid s → Interior s → s.p ≤ s.q →
    ∃ xs T, Wins σ s xs T ∧
      score xs T ≤ Payoff.value (inverseRemainder s) + Real.log (2 * (s.p : ℝ))

theorem improper_winners (σ : Convention) (s : State) (hv : Valid s) (hbig : s.q < s.p)
    (hex : ∃ xs T, Terminal σ s xs T) (proper : ProperWinners σ) :
    (∃ xs T, Wins σ s xs T) ∧
    Set.Finite {b : List ℕ | Entrance σ s b ∧ ∃ ys T, Wins σ s (b ++ ys) T} := by
  classical
  let S := {b : List ℕ | Entrance σ s b}
  have suffix (b : List ℕ) (hb : b ∈ S) : ∃ p : List ℕ × ℕ,
      Wins σ (finish s b) p.1 p.2 ∧
      score p.1 p.2 ≤ Payoff.value (inverseRemainder (finish s b)) +
        Real.log (2 * ((finish s b).p : ℝ)) := by
    change Entrance σ s b at hb
    obtain ⟨ys,T,ht,hle⟩ := proper _ (finish_valid hv hb.controls)
      hb.end_inside.1 hb.end_small.le
    exact ⟨(ys,T),ht,hle⟩
  let p (b : List ℕ) : List ℕ × ℕ := if h : b ∈ S then (suffix b h).choose else ([],0)
  have spec (b : List ℕ) (hb : b ∈ S) :
      Wins σ (finish s b) (p b).1 (p b).2 ∧
      score (p b).1 (p b).2 ≤ Payoff.value (inverseRemainder (finish s b)) +
        Real.log (2 * ((finish s b).p : ℝ)) := by
    simpa [p, hb] using (suffix b hb).choose_spec
  let w b := score (b ++ (p b).1) (p b).2
  have leg (b : List ℕ) (hb : b ∈ S) : Terminal σ s (b ++ (p b).1) (p b).2 :=
    (terminal_append ..).mpr ⟨Entrance.controls hb,(spec b hb).1.1⟩
  have upper (b : List ℕ) (hb : b ∈ S) :
      w b ≤ BranchCutoff.entranceUpper s.q b.length := by
    change Entrance σ s b at hb
    have v := finish_valid hv hb.controls
    have env := Payoff.entrance_envelope (r := b.length)
      v.1 hb.end_small.le hv.2 (by exact_mod_cast hb.denominator_product_bound hbig)
    change score (b ++ (p b).1) (p b).2 ≤ _
    rw [score_append]
    exact (div_le_div_of_nonneg_right (spec b hb).2 (by positivity)).trans env
  obtain ⟨xs0,T0,ht0⟩ := hex
  obtain ⟨a,_,_,ha,_⟩ := split_first_entrance ht0 hv (improper_nonempty ht0 hbig)
  have alegal := leg a ha
  have hTa := alegal.2.1
  have hp : 1 < ((p a).2 : ℝ) := by exact_mod_cast hTa
  have hvpos := (Real.log_pos hp).trans_le (Payoff.log_le_value hp.le)
  have hgap : 0 < w a := div_pos hvpos (by positivity)
  have cut := BranchCutoff.cutoff_of_tendsto S List.length w
    (BranchCutoff.entranceUpper s.q) a upper (BranchCutoff.entrance_limit s.q) hgap
  obtain ⟨b,hb,hmaximum,hfinite⟩ := BranchCutoff.finite_and_attained
    S List.length w a ha (finite_short_entrances σ s hbig) cut
  have dominate (b' ys : List ℕ) (T : ℕ) (he : b' ∈ S)
      (ht : Terminal σ (finish s b') ys T) :
      score (b' ++ ys) T ≤ w b' := by
    dsimp [w]
    rw [score_append, score_append]
    exact div_le_div_of_nonneg_right ((spec b' he).1.2 _ _ ht) (by positivity)
  have win : Wins σ s (b ++ (p b).1) (p b).2 := by
    refine ⟨leg b hb, ?_⟩
    intro xs T ht
    obtain ⟨b',ys,rfl,he,ht'⟩ := split_first_entrance ht hv (improper_nonempty ht hbig)
    exact (dominate _ _ _ he ht').trans (hmaximum b' he)
  refine ⟨⟨_,_,win⟩, hfinite.subset ?_⟩
  rintro b' ⟨he,ys,T,hw⟩
  refine ⟨he,le_antisymm (hmaximum _ he) ?_⟩
  exact (hw.2 _ _ win.1).trans (dominate _ _ _ he ((terminal_append ..).mp hw.1).2)

end Egyptian.Control
