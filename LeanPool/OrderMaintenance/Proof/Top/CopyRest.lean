/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.RunIns


/-!
# M5: the completed path copy

The views of `copyRest j H t l`: chunks `y`, `z` of job `j` carry `x`'s path on levels `l..H`, and
the range pointers of the nodes on that part of `x`'s path move to `y` (first) and `z` (last).
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
section
variable (j : Job) (H : Nat)

/-- `u` is on `x`'s path at a level from `l` to `H`. -/
def cpHit (t : TS) (l u : Nat) : Bool := (List.range' l (H + 1 - l)).any fun i => u == pth t j.x i

theorem cpHit_iff (t : TS) (l u : Nat) :
    cpHit j H t l u = true ↔ ∃ i, l ≤ i ∧ i ≤ H ∧ u = pth t j.x i := by
  unfold cpHit
  simp only [List.any_eq_true, List.mem_range'_1, beq_iff_eq]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩, h3⟩; exact ⟨i, h1, by omega, h3⟩
  · rintro ⟨i, h1, h2, h3⟩; exact ⟨i, ⟨h1, by omega⟩, h3⟩

/-- The first pointer after the copy from level `l`. -/
def cpFirst (t : TS) (l u : Nat) : Nat :=
  if cpHit j H t l u = true ∧ (nd t u).first = j.x then j.y else (nd t u).first
def cpLast (t : TS) (l u : Nat) : Nat :=
  if cpHit j H t l u = true ∧ (nd t u).last = j.x then j.z else (nd t u).last

/-- The copy's hypotheses: three distinct chunks, distinct path nodes, room in the new paths. -/
structure CopyOK (t : TS) (l : Nat) : Prop where
  yz : j.y ≠ j.z
  xy : j.x ≠ j.y
  xz : j.x ≠ j.z
  dist : ∀ i i', l ≤ i → i ≤ H → l ≤ i' → i' ≤ H → pth t j.x i = pth t j.x i' → i = i'
  sy : H < (t.path.getX j.y).size
  sz : H < (t.path.getX j.z).size

end

theorem copyS_views (t : TS) (j : Job) (l : Nat) (hyz : j.y ≠ j.z) (hxy : j.x ≠ j.y)
    (hxz : j.x ≠ j.z) (hv : pth t j.x l < t.nodes.size) :
    (copyS t j l).P = t.P ∧ (copyS t j l).cin = t.cin ∧ (copyS t j l).lpar = t.lpar ∧
      (copyS t j l).tag = t.tag ∧ (copyS t j l).nodes.size = t.nodes.size ∧
      (∀ c, c ≠ j.y → c ≠ j.z → (copyS t j l).path.getX c = t.path.getX c) ∧
      ((copyS t j l).path.getX j.y = (t.path.getX j.y).setX l (pth t j.x l)) ∧
      ((copyS t j l).path.getX j.z = (t.path.getX j.z).setX l (pth t j.x l)) ∧
      (∀ u, nd (copyS t j l) u = { nd t u with
        first := if u = pth t j.x l ∧ (nd t u).first = j.x then j.y else (nd t u).first,
        last := if u = pth t j.x l ∧ (nd t u).last = j.x then j.z else (nd t u).last }) := by
  unfold copyS
  simp only
  refine ⟨by split_ifs <;> rfl, by split_ifs <;> rfl, by split_ifs <;> rfl, by split_ifs <;> rfl,
    by split_ifs <;> simp, fun c hy hz => ?_, ?_, ?_, fun u => ?_⟩
  · split_ifs <;> simp [Array.getX_setX, hy, hz]
  · split_ifs <;> simp [Array.getX_setX, hyz]
  · split_ifs <;> simp [Array.getX_setX, Ne.symm hyz]
  · by_cases hu : u = pth t j.x l
    · subst hu
      have hv' : ¬ t.nodes.size ≤ pth t j.x l := Nat.not_le.mpr hv
      by_cases h1 : (nd t (pth t j.x l)).first = j.x <;> by_cases h2 : (nd t (pth t j.x l)).last = j.x <;>
        simp only [nd] at h1 h2 <;> simp [h1, h2, nd, Array.getX_modify,  hv]
    · simp only [hu, false_and, ite_false]
      split_ifs <;> simp [nd, Array.getX_modify, Ne.symm hu]

theorem cpHit_succ (j : Job) (H : Nat) (t : TS) (l u : Nat) (hl : l ≤ H) :
    cpHit j H t l u = true ↔ (u = pth t j.x l ∨ cpHit j H t (l + 1) u = true) := by
  rw [cpHit_iff, cpHit_iff]
  constructor
  · rintro ⟨i, h1, h2, h3⟩
    by_cases hi : i = l
    · left; rw [h3, hi]
    · right; exact ⟨i, by omega, h2, h3⟩
  · rintro (h | ⟨i, h1, h2, h3⟩)
    · exact ⟨l, le_rfl, hl, h⟩
    · exact ⟨i, by omega, h2, h3⟩

/-- **The completed copy.** -/
theorem copyRest_views (j : Job) (H : Nat) :
    ∀ k t l, H + 1 - l = k → CopyOK j H t l → (∀ i, l ≤ i → i ≤ H → pth t j.x i < t.nodes.size) →
      (copyRest j H t l).P = t.P ∧ (copyRest j H t l).cin = t.cin ∧
      (copyRest j H t l).lpar = t.lpar ∧ (copyRest j H t l).tag = t.tag ∧
      (copyRest j H t l).nodes.size = t.nodes.size ∧
      (∀ c, c ≠ j.y → c ≠ j.z → (copyRest j H t l).path.getX c = t.path.getX c) ∧
      (∀ i, ((copyRest j H t l).path.getX j.y).getX i =
        if l ≤ i ∧ i ≤ H then pth t j.x i else (t.path.getX j.y).getX i) ∧
      (∀ i, ((copyRest j H t l).path.getX j.z).getX i =
        if l ≤ i ∧ i ≤ H then pth t j.x i else (t.path.getX j.z).getX i) ∧
      ((copyRest j H t l).path.getX j.y).size = (t.path.getX j.y).size ∧
      ((copyRest j H t l).path.getX j.z).size = (t.path.getX j.z).size ∧
      (∀ u, nd (copyRest j H t l) u = { nd t u with first := cpFirst j H t l u, last := cpLast j H t l u }) := by
  intro k
  induction k with
  | zero =>
    intro t l hk hok hv
    unfold copyRest; rw [ite_eq_right (by omega)]
    have hh : ∀ u, cpHit j H t l u = false := fun u => by
      by_contra hc; simp only [Bool.not_eq_false] at hc
      obtain ⟨i, h1, h2, -⟩ := (cpHit_iff j H t l u).mp hc; omega
    refine ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, fun i => ?_, fun i => ?_, rfl, rfl, fun u => ?_⟩
    · rw [ite_eq_right (by omega)]
    · rw [ite_eq_right (by omega)]
    · simp only [cpFirst, cpLast, hh, Bool.false_eq_true, false_and, ite_false]
  | succ k ih =>
    intro t l hk hok hv
    have hl : l ≤ H := by omega
    rw [copyRest_step j H t l hl]
    have hvl := hv l le_rfl hl
    obtain ⟨cP, cC, cL, cT, cS, cO, cY, cZ, cN⟩ := copyS_views t j l hok.yz hok.xy hok.xz hvl
    have hpx : ∀ i, pth (copyS t j l) j.x i = pth t j.x i := fun i => by
      unfold pth; rw [cO j.x hok.xy hok.xz]
    have hsy : ((copyS t j l).path.getX j.y).size = (t.path.getX j.y).size := by
      rw [cY, Array.size_setX, ite_eq_left (by have := hok.sy; omega)]
    have hsz : ((copyS t j l).path.getX j.z).size = (t.path.getX j.z).size := by
      rw [cZ, Array.size_setX, ite_eq_left (by have := hok.sz; omega)]
    have hok' : CopyOK j H (copyS t j l) (l + 1) :=
      ⟨hok.yz, hok.xy, hok.xz, fun i i' h1 h2 h3 h4 e => hok.dist i i' (by omega) h2 (by omega) h4
        (by rw [← hpx, ← hpx]; exact e), by rw [hsy]; exact hok.sy, by rw [hsz]; exact hok.sz⟩
    obtain ⟨iP, iC, iL, iT, iS, iO, iY, iZ, iSy, iSz, iN⟩ := ih (copyS t j l) (l + 1) (by omega) hok'
      (fun i h1 h2 => by rw [hpx, cS]; exact hv i (by omega) h2)
    refine ⟨iP.trans cP, iC.trans cC, iL.trans cL, iT.trans cT, iS.trans cS,
      fun c hy hz => (iO c hy hz).trans (cO c hy hz), fun i => ?_, fun i => ?_, iSy.trans hsy,
      iSz.trans hsz, fun u => ?_⟩
    · rw [iY, hpx, cY, Array.getX_setX]
      by_cases hi : i = l
      · subst hi; simp [hl]
      · by_cases h2 : l + 1 ≤ i ∧ i ≤ H
        · rw [ite_eq_left h2, ite_eq_left ⟨by omega, h2.2⟩]
        · rw [ite_eq_right h2, ite_eq_right hi, ite_eq_right (by omega)]
    · rw [iZ, hpx, cZ, Array.getX_setX]
      by_cases hi : i = l
      · subst hi; simp [hl]
      · by_cases h2 : l + 1 ≤ i ∧ i ≤ H
        · rw [ite_eq_left h2, ite_eq_left ⟨by omega, h2.2⟩]
        · rw [ite_eq_right h2, ite_eq_right hi, ite_eq_right (by omega)]
    · have hF : ∀ w, (nd (copyS t j l) w).first =
          if w = pth t j.x l ∧ (nd t w).first = j.x then j.y else (nd t w).first := fun w => by rw [cN]
      have hL : ∀ w, (nd (copyS t j l) w).last =
          if w = pth t j.x l ∧ (nd t w).last = j.x then j.z else (nd t w).last := fun w => by rw [cN]
      rw [iN, cN]
      have hhit : ∀ w, cpHit j H (copyS t j l) (l + 1) w = cpHit j H t (l + 1) w := fun w => by
        unfold cpHit; simp only [hpx]
      unfold cpFirst cpLast
      rw [hhit, hF, hL]
      by_cases hu : u = pth t j.x l
      · have hn : cpHit j H t (l + 1) u = false := by
          by_contra hc; simp only [Bool.not_eq_false] at hc
          obtain ⟨i, h1, h2, h3⟩ := (cpHit_iff j H t (l + 1) u).mp hc
          have := hok.dist l i le_rfl hl (by omega) h2 (hu ▸ h3); omega
        have hh : cpHit j H t l u = true := (cpHit_succ j H t l u hl).mpr (Or.inl hu)
        simp only [hn, hh, Bool.false_eq_true, false_and, ite_false, true_and]
        subst hu
        simp
      · have hh : cpHit j H t l u = cpHit j H t (l + 1) u := by
          cases h : cpHit j H t (l + 1) u
          · by_contra hc; simp only [Bool.not_eq_false] at hc
            rcases (cpHit_succ j H t l u hl).mp hc with h' | h'
            · exact hu h'
            · rw [h] at h'; simp at h'
          · exact (cpHit_succ j H t l u hl).mpr (Or.inr h)
        simp only [hu, false_and, ite_false, hh]

end OrderMaintenance.Proof.Top
