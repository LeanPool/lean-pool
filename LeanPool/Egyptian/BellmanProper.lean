/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.BellmanScore
public import LeanPool.Egyptian.PayoffControl
public import LeanPool.Egyptian.BranchCutoff

/-!
# Attainment and the finite set of maximizing first descents

Kovač and Tang, §3.3. We stop each competing trajectory at its first fall
below the initial numerator. Strong induction supplies an optimal suffix.
The envelope log(2p) is an explicit majorant of the paper's constants Γₚ.
-/

@[expose] public section

namespace Egyptian.Control

theorem noFall_score {σ s xs T} (hv : Valid s) (hs : s.p ≤ s.q)
    (ht : Terminal σ s xs T) (hn : NoFall s xs) :
    score xs T ≤ Payoff.value (inverseRemainder s) := by
  have hn' := noFall_bound hv hs ht.1 hn
  rw [inverse_of_stop (finish_valid hv ht.1) ht.2.2.2] at hn'
  have h1 : (1 : ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by have := ht.2.1; omega)
  have h2 := one_le_inverse hv hs
  have h := Payoff.value_strictMonoOn.monotoneOn h1 (Payoff.one_le_orbit h2 _) hn'
  rw [Payoff.value_orbit h2] at h
  exact (div_le_iff₀ (by positivity)).2 (by linarith)

theorem unit_winner_eq {σ s xs T} (hv : Valid s) (hi : Interior s) (hs : s.p ≤ s.q)
    (hd : s.p ∣ s.q) (hw : Wins σ s xs T) :
    score xs T = Payoff.value (inverseRemainder s) := by
  obtain ⟨ys,U,ht,he⟩ := unit_reward σ hv hi hd
  rw [← score_as_mul] at he
  exact le_antisymm (noFall_score hv hs hw.1 (noFall_unit hv hd hw.1.1))
    (he ▸ hw.2 ys U ht)

/-- All maximizing nonunit trajectories start in a finite family of first
falls, and the suffix of each such trajectory also maximizes. -/
def FiniteWinningFalls (σ : Convention) (s : State) : Prop :=
  ∃ F : Set (List ℕ), F.Finite ∧ (∀ b ∈ F, FallBlock σ s b) ∧
    ∀ xs T, Wins σ s xs T → ∃ b ∈ F, ∃ ys, xs = b ++ ys ∧ Wins σ (finish s b) ys T

private theorem fall_majorant {σ s b} (hv : Valid s) (hs : s.p ≤ s.q)
    (hb : FallBlock σ s b) :
    (Payoff.value (inverseRemainder (finish s b)) + Real.log (2 * (finish s b).p)) /
        (2:ℝ)^b.length ≤ Payoff.value (inverseRemainder s) + Real.log (4*s.p)/2^b.length ∧
    Payoff.value (inverseRemainder s) + Real.log (4*s.p)/2^b.length ≤
      Payoff.value (inverseRemainder s) + Real.log (2*s.p) := by
  have hve := finish_valid hv hb.1
  have hp : (1:ℝ) ≤ s.p := by exact_mod_cast hv.1
  have hd : (1:ℝ) ≤ (finish s b).p := by exact_mod_cast hve.1
  have hr := List.length_pos_iff.mpr (fall_ne_nil hb)
  exact Payoff.fall_envelope (one_le_inverse hv hs)
    (one_le_inverse hve (finish_small s b hs)) hp hd hr
    (firstFall_bound hv hs hb.1 hb.2.2 hb.2.1)

private theorem proper_aux (σ : Convention) (s : State) (hv : Valid s)
    (hi : Interior s) (hs : s.p ≤ s.q) :
    ∃ xs T, Wins σ s xs T ∧ score xs T ≤
      Payoff.value (inverseRemainder s) + Real.log (2*(s.p : ℝ)) ∧
      (¬s.p ∣ s.q → FiniteWinningFalls σ s) := by
  classical
  by_cases hd : s.p ∣ s.q
  · obtain ⟨ys,U,ht,he⟩ := unit_reward σ hv hi hd
    rw [← score_as_mul] at he
    have hp : (1:ℝ) ≤ s.p := by exact_mod_cast hv.1
    exact ⟨ys,U,⟨ht,fun zs V hz => (noFall_score hv hs hz (noFall_unit hv hd hz.1)).trans he.ge⟩,
      he ▸ le_add_of_nonneg_right (Real.log_nonneg (by linarith)),fun hn => (hn hd).elim⟩
  · let B := {b : List ℕ // FallBlock σ s b}
    have successors (b : B) := proper_aux σ (finish s b.val) (finish_valid hv b.prop.1)
      (fall_interior hs b.prop) (finish_small s b.val hs)
    choose suffix den hwin henv hmore using successors
    let f (b : B) := score (b.val ++ suffix b) (den b)
    let H := Payoff.value (inverseRemainder s)
    let bound (n : ℕ) := H + Real.log (4*s.p)/(2:ℝ)^n
    have fBound (b : B) : f b ≤ bound b.val.length := by
      change score (b.val ++ suffix b) (den b) ≤ bound b.val.length
      rw [score_append]
      exact (div_le_div_of_nonneg_right (henv b) (by positivity)).trans
        (fall_majorant hv hs b.prop).1
    have fTerminal (b : B) : Terminal σ s (b.val ++ suffix b) (den b) :=
      (terminal_append ..).mpr ⟨b.prop.1,(hwin b).1⟩
    have splitScore (xs : List ℕ) (T : ℕ) (ht : Terminal σ s xs T) :
        score xs T ≤ H ∨ ∃ b : B, ∃ ys, xs = b.val ++ ys ∧ score xs T ≤ f b := by
      obtain hn | ⟨b,ys,rfl,hb⟩ := split_at_fall ht.1
      · exact Or.inl (noFall_score hv hs ht hn)
      · right
        let i : B := ⟨b,hb⟩
        obtain ⟨_,ht'⟩ := (terminal_append ..).mp ht
        refine ⟨i,ys,rfl,?_⟩
        change score (b ++ ys) T ≤ score (b ++ suffix i) (den i)
        rw [score_append, score_append]
        exact div_le_div_of_nonneg_right ((hwin i).2 ys T ht') (by positivity)
    obtain ⟨ys,U,ht,_,hstrict⟩ := greedy_reward σ s hv hi hs
    have hgain : H < score ys U := (score_as_mul ys U) ▸ hstrict hd
    obtain small | ⟨a,_,_,ha⟩ := splitScore ys U ht
    · exact (not_le_of_gt hgain small).elim
    have gap : H < f a := hgain.trans_le ha
    have finiteShort (M : ℕ) : Set.Finite {b : B | b ∈ Set.univ ∧ b.val.length < M} := by
      apply ((finite_short_falls σ s M).preimage (f := Subtype.val)
        Subtype.val_injective.injOn).subset
      intro b hb
      exact ⟨b.prop,hb.2.le⟩
    have lim : Filter.Tendsto bound Filter.atTop (nhds H) := by
      convert BranchCutoff.first_descent_limit H (Real.log (4*s.p)/2) using 1
      ext n
      dsimp [bound]
      ring
    have cut := BranchCutoff.cutoff_of_tendsto Set.univ (fun b : B => b.val.length) f
      bound a (fun b _ => fBound b) lim gap
    obtain ⟨best,_,hmax,hfinite⟩ := BranchCutoff.finite_and_attained Set.univ _ f a
      (Set.mem_univ a) finiteShort cut
    have globalMax (zs : List ℕ) (V : ℕ) (hz : Terminal σ s zs V) : score zs V ≤ f best := by
      obtain small | ⟨b,_,_,hb⟩ := splitScore zs V hz
      · exact small.trans (gap.le.trans (hmax a (Set.mem_univ _)))
      · exact hb.trans (hmax b (Set.mem_univ _))
    refine ⟨best.val ++ suffix best,den best,⟨fTerminal best,globalMax⟩,
      (fBound best).trans (fall_majorant hv hs best.prop).2,?_⟩
    intro _
    let F := {i : B | i ∈ Set.univ ∧ f i = f best}
    refine ⟨Subtype.val '' F, hfinite.image _, ?_, ?_⟩
    · rintro _ ⟨b,_,rfl⟩
      exact b.prop
    · intro xs T hw
      have eqv : score xs T = f best :=
        le_antisymm (globalMax _ _ hw.1) (hw.2 _ _ (fTerminal best))
      obtain small | ⟨b,zs,he,hbound⟩ := splitScore xs T hw.1
      · exact (not_le_of_gt ((gap.trans_le (hmax a (Set.mem_univ _))).trans_eq eqv.symm) small).elim
      · have hb : f b = f best :=
          le_antisymm (hmax b (Set.mem_univ _)) (eqv ▸ hbound)
        exact ⟨b.val,⟨b,⟨Set.mem_univ _,hb⟩,rfl⟩,zs,he,wins_suffix (he ▸ hw)⟩
termination_by s.p
decreasing_by exact b.prop.2.1

theorem proper_winner (σ : Convention) (s : State) (hv : Valid s)
    (hi : Interior s) (hs : s.p ≤ s.q) :
    ∃ xs T, Wins σ s xs T ∧
      score xs T ≤ Payoff.value (inverseRemainder s) + Real.log (2 * (s.p : ℝ)) := by
  obtain ⟨xs, T, hw, hb, _⟩ := proper_aux σ s hv hi hs
  exact ⟨xs, T, hw, hb⟩

theorem proper_max_falls (σ : Convention) (s : State) (hv : Valid s) (hi : Interior s)
    (hs : s.p ≤ s.q) (hd : ¬s.p ∣ s.q) : FiniteWinningFalls σ s := by
  obtain ⟨_,_,_,_,hf⟩ := proper_aux σ s hv hi hs
  exact hf hd

end Egyptian.Control
