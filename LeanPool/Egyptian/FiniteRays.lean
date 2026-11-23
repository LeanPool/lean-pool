/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.WinningRays
public import LeanPool.Egyptian.BellmanProper
public import LeanPool.Egyptian.GlobalAttainment

/-! Finiteness of maximizing rays, by strong induction on the cleared
numerator for proper states and then by finite entrance blocks for all
remaining states (Kovač–Tang, §4). -/

public section

namespace Egyptian.Control

theorem finite_winningRays_proper (s : State) (hv : Valid s) (hi : Interior s)
    (hs : s.p ≤ s.q) : (winningRays s).Finite := by
  by_cases hd : s.p ∣ s.q
  · exact finite_rays_unit hv hd (fun _ _ hw => unit_winner_eq hv hi hs hd hw)
  · obtain ⟨F, hF, hfall, hcover⟩ := proper_max_falls .weak s hv hi hs hd
    apply finite_rays_of_branches hF _ hcover
    intro b hb
    have h := hfall b hb
    exact finite_winningRays_proper (finish s b) (finish_valid hv h.1)
      (fall_interior hs h) (finish_small s b hs)
termination_by s.p
decreasing_by exact h.2.1

theorem finite_winningRays (s : State) (hv : Valid s) (hi : Interior s) :
    (winningRays s).Finite := by
  by_cases hs : s.p ≤ s.q
  · exact finite_winningRays_proper s hv hi hs
  have hbig := Nat.lt_of_not_ge hs
  have proper : ProperWinners .weak := by
    intro t ht hti hts
    obtain ⟨xs,T,hterm,hbest,hupper⟩ := proper_winner .weak t ht hti hts
    exact ⟨xs,T,⟨hterm,hbest⟩,hupper⟩
  by_cases hex : ∃ xs T, Terminal .weak s xs T
  · have hF := (improper_winners .weak s hv hbig hex proper).2
    apply finite_rays_of_branches hF
    · intro b hb
      have h : Entrance .weak s b := hb.1
      exact finite_winningRays_proper _ (finish_valid hv h.controls)
        h.end_inside.1 h.end_small.le
    · intro xs T hw
      obtain ⟨b,ys,rfl,he,_⟩ := split_first_entrance hw.1 hv (improper_nonempty hw.1 hbig)
      exact ⟨b,⟨he,ys,T,hw⟩,ys,rfl,wins_suffix hw⟩
  · apply Set.finite_empty.subset
    rintro a ⟨xs,T,hw,_⟩
    exact (hex ⟨xs,T,hw.1⟩).elim

end Egyptian.Control
