/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.PresFinish


/-!
# M5: path copy steps

A copy step writes one level of the new chunks' paths (`copyS`). The state with the copy
completed (`finS`) does not change, so the invariant carries over; only the job's position
advances.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-- The job after copy step `l`. -/
def copyNext (P : Params) (j : Job) (l : Nat) : Job :=
  { j with pc := if l < P.H then .copy (l + 1) else .walk none }

/-- The state after copy step `l`, as the code computes it. -/
def copyC (s : Core) (j : Job) (l : Nat) : Core :=
  let v := (s.path.getX j.x).getX l
  let s1 := { s with path := s.path.setX j.y ((s.path.getX j.y).setX l v) }
  let s2 := { s1 with path := s1.path.setX j.z ((s1.path.getX j.z).setX l v) }
  let V := s2.nodes.getX v
  let s3 := if V.first == j.x then
    { s2 with nodes := s2.nodes.modify v fun n => { n with first := j.y } } else s2
  if V.last == j.x then
    { s3 with nodes := s3.nodes.modify v fun n => { n with last := j.z } } else s3

theorem ts_copyC (s : Core) (j : Job) (l : Nat) : ts (copyC s j l) = copyS (ts s) j l := by
  unfold copyC copyS
  by_cases h1 : (s.nodes.getX ((s.path.getX j.x).getX l)).first = j.x <;>
    by_cases h2 : (s.nodes.getX ((s.path.getX j.x).getX l)).last = j.x <;>
    simp [h1, h2, nd, pth, ts]

/-- **A copy step runs.** -/
theorem jobStep_copy {s : Core} {j : Job} {l : Nat} (hpc : j.pc = .copy l) :
    (jobStep j).run s = .ok (some (copyNext s.P j l)) (copyC s j l) := by
  unfold jobStep copyC copyNext
  rw [hpc]
  simp only [run_getP_bind, run_getPath_bind, run_setPathAt_bind, run_getN_bind]
  split_ifs <;> simp only [  run_pure, run_bind, run_modN, ] <;> first | rfl | (split_ifs <;> rfl)

/-- Timing depends on the job only through the lagging nodes, the sweeps owed, and funding. -/
theorem Timing.congr_job {s : TS} {cl : List Nat} {oj oj' : Option Job} (Ti : Timing s cl oj)
    (hp : pend s oj' = pend s oj) (hs : ∀ v, slack s oj' v = slack s oj v)
    (hf : ∀ v, funded s oj' v ↔ funded s oj v) : Timing s cl oj' := by
  refine ⟨fun v hv => ?_, Ti.wA, Ti.wB, Ti.wF, fun v hv => ?_, fun v hv => ?_, Ti.wD, Ti.big, Ti.chain, Ti.tw1⟩
  · rw [hp]; exact Ti.wts v hv
  · rw [hs]; exact Ti.wC v hv
  · have := Ti.wC' v hv
    by_cases h : funded s oj v
    · rw [ite_eq_left ((hf v).mpr h)]; rw [ite_eq_left h] at this; exact this
    · rw [ite_eq_right (fun h' => h ((hf v).mp h'))]; rw [ite_eq_right h] at this; exact this

theorem copyRest_congr {j j' : Job} (hx : j'.x = j.x) (hy : j'.y = j.y) (hz : j'.z = j.z) (H : Nat) :
    ∀ k t l, H + 1 - l = k → copyRest j' H t l = copyRest j H t l := by
  intro k
  induction k with
  | zero => intro t l hk; unfold copyRest; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  | succ k ih =>
    intro t l hk
    unfold copyRest
    rw [ite_eq_left (by omega), ite_eq_left (by omega)]
    have : copyS t j' l = copyS t j l := by unfold copyS; rw [hx, hy, hz]
    rw [this]; exact ih _ _ (by omega)

theorem copyS_P (t : TS) (j : Job) (l : Nat) : (copyS t j l).P = t.P := by
  unfold copyS; dsimp only; split_ifs <;> rfl

theorem copyRest_P (j : Job) (H : Nat) : ∀ k t l, H + 1 - l = k → (copyRest j H t l).P = t.P := by
  intro k
  induction k with
  | zero => intro t l hk; unfold copyRest; rw [ite_eq_right (by omega)]
  | succ k ih =>
    intro t l hk; unfold copyRest; rw [ite_eq_left (by omega), ih _ _ (by omega), copyS_P]

theorem copyRest_step (j : Job) (H : Nat) (t : TS) (l : Nat) (hl : l ≤ H) :
    copyRest j H t l = copyRest j H (copyS t j l) (l + 1) := by
  conv_lhs => unfold copyRest
  rw [ite_eq_left hl]

/-- **A copy step keeps the invariant**: the completed state is unchanged. -/
theorem inv_copy {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat}
    {j : Job} {l : Nat} (hpc : j.pc = .copy l)
    (hI : InvJ (finS (ts s) (some j)) cl ord dr n0 (some j)) :
    InvJ (finS (ts (copyC s j l)) (some (copyNext s.P j l))) cl ord dr n0
      (some (copyNext s.P j l)) := by
  obtain ⟨hpos, hat⟩ := hI.job j rfl
  have hfin : finS (ts s) (some j) = copyRest j s.P.H (ts s) l := by
    simp only [finS]; rw [hpc]; rfl
  have hat' := hat
  simp only [JobAt, hpc] at hat'
  obtain ⟨hl1, hlH, hy, hz⟩ := hat'
  rw [hfin, copyRest_P j _ _ _ _ rfl] at hlH
  change l ≤ s.P.H at hlH
  -- the completed state is the same
  have hsame : finS (ts (copyC s j l)) (some (copyNext s.P j l)) = finS (ts s) (some j) := by
    rw [hfin, copyRest_step j _ _ l hlH, ts_copyC]
    simp only [finS, copyNext]
    have hP' : (copyS (ts s) j l).P = s.P := copyS_P _ _ _
    by_cases h : l < s.P.H
    · simp only [ite_eq_left h]
      rw [hP']
      exact copyRest_congr (j := j) (j' := { j with pc := .copy (l + 1) }) rfl rfl rfl s.P.H _ _ _ rfl
    · simp only [ite_eq_right h]
      unfold copyRest; rw [ite_eq_right (by omega)]
  rw [hsame]
  set t := finS (ts s) (some j)
  have hj : ∀ v, funded t (some (copyNext s.P j l)) v ↔ funded t (some j) v := fun v => Iff.rfl
  have hp : pend t (some (copyNext s.P j l)) = pend t (some j) := by
    by_cases h : l < s.P.H <;> simp [pend, wStart, copyNext, hpc, h]
  have hs : ∀ v, slack t (some (copyNext s.P j l)) v = slack t (some j) v := by
    intro v; by_cases h : l < s.P.H <;> simp [slack, curH, copyNext, hpc, h]
  refine ⟨hI.shape, hI.time.congr_job hp hs hj, hI.room, fun j' hj' => ?_, hI.cap, hI.len⟩
  cases hj'
  refine ⟨hpos, ?_⟩
  simp only [JobAt, copyNext]
  have htP : t.P = s.P := by rw [hfin, copyRest_P j _ _ _ _ rfl]; rfl
  by_cases h : l < s.P.H
  · simp only [ite_eq_left h]; rw [htP]; exact ⟨by omega, by omega, hy, hz⟩
  · simp only [ite_eq_right h]; exact ⟨hy, hz⟩

end OrderMaintenance.Proof.Top
