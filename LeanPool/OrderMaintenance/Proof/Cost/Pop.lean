/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.ResLoop


/-!
# The pop: queue, game and the rest

Popping chunk `c` takes it out of the queue; starting its split makes it splitting and adds two
overflow chunks. So the queue invariant holds again, and the game's new round starts by zeroing a
largest value.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- Starting a chunk split leaves the queue's fields alone. -/
theorem pqsame_split {s s2 : Core} {x : Nat} {job : Job}
    (hT : TopRel (linkChunkPair (push2 s) x s.C.size (s.C.size + 1)) s2) :
    PQSame s (markState s2 x s.C.size (s.C.size + 1) job) := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := hT.pq
  have hP := hT.rest.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [markState]
  · exact p4
  · exact p2
  · exact p3
  · exact p1
  · exact p5
  · exact p6
  · exact p8
  · exact p7
  · rw [hP]; rfl

/-- **The queue invariant after a pop and the split start.** -/
theorem pqc_pop {t t2 : Core} {c : Nat} {bl : Nat → List Nat} {nb : List Nat}
    (hQ : QRep t (cSz t) (inQC t) bl nb) (hc : inQC t c = true)
    (R : ResSpec (delSt t c) t2 c) (hS : PQSame (delSt t c) t2) : PQC t2 := by
  have hD := delSt_only t c
  have hdel := hQ.del hc
  have hCt : ∀ d, (delSt t c).C.getX d = t.C.getX d := fun d => by rw [hD.C]
  have hsz1 : (delSt t c).C.size = t.C.size := by rw [hD.C]
  have hcL : LiveC t c := by unfold inQC at hc; simp only [decide_eq_true_eq] at hc; exact hc.1
  have hP : t2.P = t.P := by rw [R.P, hD.P]
  refine ⟨_, _, hdel.congr hS (fun d => ?_) (fun d hd => ?_)⟩
  · unfold inQC
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self, R.xs.2.2.1]; simp
    · rw [Function.update_of_ne hdc]
      by_cases hd : d < t.C.size
      · have o := R.old d (by rw [hsz1]; exact hd) hdc
        simp only [cSt, cSz, hCt] at o
        simp only [LiveC, R.Csize, hsz1, cSt, cSz, o.1, o.2.2.1, hP]
        have : d < t.C.size + 2 := by omega
        simp [hd, this]
      · have hnL : ¬ LiveC t d := fun h => hd h.2
        by_cases hdn : d = t.C.size ∨ d = t.C.size + 1
        · have := (R.new d (by rw [hsz1]; exact hdn)).2.2.1
          simp [hnL, this]
        · have hnL' : ¬ LiveC t2 d := by
            simp only [LiveC, R.Csize, hsz1]; omega
          simp [hnL, hnL']
  · by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd; cases hd
    · rw [Function.update_of_ne hdc] at hd
      have hdL : LiveC t d := by unfold inQC at hd; simp only [decide_eq_true_eq] at hd; exact hd.1
      have o := R.old d (by rw [hsz1]; exact hdL.2) hdc
      simp only [cSz, hCt] at o
      exact o.1

/-- **The game after a pop and the split start**: the popped value is zeroed, nothing grows. -/
theorem gval_pop {t t2 : Core} {c : Nat} (R : ResSpec (delSt t c) t2 c) (d : Nat) :
    gval t2 d ≤ if d = c then 0 else gval t d := by
  have hD := delSt_only t c
  have hCt : ∀ d, (delSt t c).C.getX d = t.C.getX d := fun d => by rw [hD.C]
  have hsz1 : (delSt t c).C.size = t.C.size := by rw [hD.C]
  have hP : t2.P = t.P := by rw [R.P, hD.P]
  unfold gval
  by_cases hdc : d = c
  · subst hdc; rw [ite_eq_left rfl, R.xs.2.2.1]; simp
  · rw [ite_eq_right hdc]
    by_cases hd : d < t.C.size
    · have o := R.old d (by rw [hsz1]; exact hd) hdc
      simp only [cSt, cSz, hCt] at o
      simp only [LiveC, R.Csize, hsz1, cSt, cSz, o.1, o.2.2.1, hP]
      have : d < t.C.size + 2 := by omega
      simp [hd, this]
    · by_cases hdn : d = t.C.size ∨ d = t.C.size + 1
      · have := (R.new d (by rw [hsz1]; exact hdn)).2.2.1
        simp [this]
      · have hnL' : ¬ LiveC t2 d := by
          simp only [LiveC, R.Csize, hsz1]; omega
        simp [hnL']

/-- A queued chunk has the largest game value. -/
theorem gval_max {t : Core} {c : Nat} (hc : inQC t c = true)
    (hmax : ∀ d, inQC t d = true → cSz t d ≤ cSz t c) (d : Nat) : gval t d ≤ gval t c := by
  unfold inQC at hc; simp only [decide_eq_true_eq] at hc
  have hcv : gval t c = cSz t c - t.P.theta := by unfold gval; rw [ite_eq_left ⟨hc.1, hc.2.1⟩]
  rw [hcv]
  unfold gval
  split
  · next hd =>
    by_cases h : t.P.theta < cSz t d
    · have := hmax d (by unfold inQC; simp [hd.1, hd.2, h]); omega
    · omega
  · exact Nat.zero_le _

end OrderMaintenance.Proof
