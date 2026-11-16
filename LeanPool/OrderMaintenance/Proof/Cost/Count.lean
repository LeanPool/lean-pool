/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.TopIface


/-!
# The chunk count (`docs/PROOF.md` §4.4)

Every pop takes a quiet chunk above `θ` out of the quiet set. It became quiet at a size `e c ≤
c_max`, so at least `θ + 1 − c_max` insertions went into it since. Hence the pops, and with them
the chunks (`|C| = 2 + 2·pops`), are bounded by the element count over `θ + 1 − c_max`.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- The quiet chunks. -/
def quietSet (s : Core) : Finset Nat :=
  (Finset.range s.C.size).filter fun c => LiveC s c ∧ cSt s c = .quiet

theorem mem_quietSet {s : Core} {c : Nat} : c ∈ quietSet s ↔ LiveC s c ∧ cSt s c = .quiet := by
  unfold quietSet; simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨h.1.2, h⟩⟩

/-- **The chunk-count invariant**, with ghost sizes `e` at which quiet chunks became quiet. -/
structure CountInv (s : Core) (e : Nat → Nat) (pops : Nat) : Prop where
  size : s.C.size = 2 + 2 * pops
  bound : pops * (s.P.theta + 1 - cmax s.P) + ∑ c ∈ quietSet s, (cSz s c - e c) ≤ s.count
  e_le : ∀ c, LiveC s c → cSt s c = .quiet → e c ≤ cmax s.P

theorem CountInv.chunks {s : Core} {e : Nat → Nat} {pops : Nat} (h : CountInv s e pops)
    (hθ : cmax s.P + 1 ≤ s.P.theta + 1) :
    s.C.size ≤ 2 + 2 * (s.count / (s.P.theta + 1 - cmax s.P)) := by
  have h1 := h.bound
  have h2 : pops * (s.P.theta + 1 - cmax s.P) ≤ s.count := by omega
  have h3 : pops ≤ s.count / (s.P.theta + 1 - cmax s.P) :=
    (Nat.le_div_iff_mul_le (by omega)).mpr h2
  rw [h.size]; omega

/-- Steps that keep the quiet chunks, their sizes and the element count. -/
theorem CountInv.frame {s s' : Core} {e : Nat → Nat} {pops : Nat} (h : CountInv s e pops)
    (Q : QSame s s') (hcnt : s'.count = s.count) : CountInv s' e pops := by
  have hLC : ∀ c, LiveC s' c ↔ LiveC s c := fun c => by simp only [LiveC, Q.Csize]
  have hQ : quietSet s' = quietSet s := by
    ext c; rw [mem_quietSet, mem_quietSet, hLC]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, (Q.q c h1).mp h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, (Q.q c h1).mpr h2⟩
  refine ⟨by rw [Q.Csize]; exact h.size, ?_, fun c hc hq => ?_⟩
  · rw [hQ, hcnt, Q.P]
    have : ∑ c ∈ quietSet s, (cSz s' c - e c) = ∑ c ∈ quietSet s, (cSz s c - e c) :=
      Finset.sum_congr rfl fun c hc => by
        rw [mem_quietSet] at hc; rw [Q.sz c hc.1 hc.2]
    rw [this]; exact h.bound
  · rw [hLC] at hc; rw [Q.P]; exact h.e_le c hc ((Q.q c hc).mp hq)

/-- An insertion: one more element, and at most one more in the quiet sizes. -/
theorem CountInv.ins {s s' : Core} {e : Nat → Nat} {pops g : Nat} (h : CountInv s e pops)
    (S : InsSpec s s' g) (hcnt : s'.count = s.count + 1) : CountInv s' e pops := by
  have hLC : ∀ c, LiveC s' c ↔ LiveC s c := fun c => by simp only [LiveC, S.Csize]
  have hQ : quietSet s' = quietSet s := by
    ext c; rw [mem_quietSet, mem_quietSet, hLC, S.cst]
  refine ⟨by rw [S.Csize]; exact h.size, ?_, fun c hc hq => ?_⟩
  · rw [hQ, hcnt, S.P]
    have hle : ∑ c ∈ quietSet s, (cSz s' c - e c) ≤
        ∑ c ∈ quietSet s, ((cSz s c - e c) + if c = gC s g then 1 else 0) :=
      Finset.sum_le_sum fun c _ => by rw [S.csz]; split <;> omega
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq'] at hle
    have h1 := h.bound
    split at hle <;> omega
  · rw [hLC] at hc; rw [S.cst] at hq; rw [S.P]; exact h.e_le c hc hq

/-- A chunk removal: the siblings become quiet, with their sizes (at most `c_max`) as `e`. -/
theorem CountInv.remove {s : Core} {e : Nat → Nat} {pops x : Nat} (h : CountInv s e pops)
    (hx : x < s.C.size) (hl : cLl s x < s.C.size) (hr : cRr s x < s.C.size)
    (hlx : cLl s x ≠ x) (hrx : cRr s x ≠ x)
    (hls : cSt s (cLl s x) = .overflow) (hrs : cSt s (cRr s x) = .overflow)
    (hszl : cSz s (cLl s x) ≤ cmax s.P) (hszr : cSz s (cRr s x) ≤ cmax s.P) :
    CountInv (cremoveState s x)
      (fun c => if c = cLl s x ∨ c = cRr s x then cSz s c else e c) pops := by
  have hC' := cremoveState_C hx hl hr hlx hrx
  have hsz : ∀ c, cSz (cremoveState s x) c = cSz s c := by
    intro c; simp only [cSz, hC']; split_ifs <;> rfl
  have hst : ∀ c, cSt (cremoveState s x) c = if c = x then .dead
      else if c = cLl s x ∨ c = cRr s x then .quiet else cSt s c := by
    intro c; simp only [cSt, hC']; split_ifs <;> simp [deadC, quietC]
  have hLC : ∀ c, LiveC (cremoveState s x) c ↔ LiveC s c := by
    intro c; simp [LiveC, cremoveState]
  have hP : (cremoveState s x).P = s.P := rfl
  have hcnt : (cremoveState s x).count = s.count := rfl
  have hsub : quietSet (cremoveState s x) ⊆ quietSet s ∪ {cLl s x, cRr s x} := by
    intro c hc
    rw [mem_quietSet, hLC, hst] at hc
    rw [Finset.mem_union, mem_quietSet, Finset.mem_insert, Finset.mem_singleton]
    by_cases h1 : c = x
    · rw [ite_eq_left h1] at hc; cases hc.2
    · rw [ite_eq_right h1] at hc
      by_cases h2 : c = cLl s x ∨ c = cRr s x
      · right; exact h2
      · rw [ite_eq_right h2] at hc; left; exact hc
  refine ⟨by simp [cremoveState, h.size], ?_, fun c hc hq => ?_⟩
  · rw [hcnt, hP]
    have h1 := h.bound
    set f := fun c => cSz s c - if c = cLl s x ∨ c = cRr s x then cSz s c else e c with hf
    have e1 : ∑ c ∈ quietSet (cremoveState s x),
        (cSz (cremoveState s x) c - if c = cLl s x ∨ c = cRr s x then cSz s c else e c) =
        ∑ c ∈ quietSet (cremoveState s x), f c := by
      refine Finset.sum_congr rfl fun c _ => ?_; rw [hsz]
    have e2 : ∑ c ∈ quietSet (cremoveState s x), f c ≤ ∑ c ∈ quietSet s ∪ {cLl s x, cRr s x}, f c :=
      Finset.sum_le_sum_of_subset hsub
    have e3 := Finset.sum_union_inter (s₁ := quietSet s) (s₂ := {cLl s x, cRr s x}) (f := f)
    have e4 : ∑ c ∈ quietSet s, f c = ∑ c ∈ quietSet s, (cSz s c - e c) := by
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [mem_quietSet] at hc
      have : ¬ (c = cLl s x ∨ c = cRr s x) := by
        rintro (rfl | rfl)
        · rw [hls] at hc; exact absurd hc.2 (by simp)
        · rw [hrs] at hc; exact absurd hc.2 (by simp)
      simp only [hf, ite_eq_right this]
    have e5 : ∑ c ∈ ({cLl s x, cRr s x} : Finset Nat), f c = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      rw [Finset.mem_insert, Finset.mem_singleton] at hc
      simp only [hf, ite_eq_left hc]; simp
    rw [e1]
    omega
  · rw [hLC] at hc; rw [hst] at hq
    by_cases h1 : c = x
    · rw [ite_eq_left h1] at hq; cases hq
    · rw [ite_eq_right h1] at hq
      rw [hP]
      by_cases h2 : c = cLl s x ∨ c = cRr s x
      · simp only [ite_eq_left h2]
        rcases h2 with rfl | rfl
        · exact hszl
        · exact hszr
      · simp only [ite_eq_right h2]; rw [ite_eq_right h2] at hq; exact h.e_le c hc hq

/-- **A pop**: the popped chunk (above `θ`) leaves the quiet set, and two chunks are added. -/
theorem CountInv.pop {s s' : Core} {e : Nat → Nat} {pops x : Nat} (h : CountInv s e pops)
    (R : ResSpec s s' x) (hxL : LiveC s x) (hxq : cSt s x = .quiet) (hθ : s.P.theta < cSz s x)
    (hcnt : s'.count = s.count) : CountInv s' e (pops + 1) := by
  have hQ : quietSet s' = (quietSet s).erase x := by
    ext c
    rw [mem_quietSet, Finset.mem_erase, mem_quietSet]
    simp only [LiveC, R.Csize]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases hcx : c = x
      · rw [hcx, R.xs.2.2.1] at h3; cases h3
      · by_cases hn : c < s.C.size
        · rw [(R.old c hn hcx).2.2.1] at h3; exact ⟨hcx, ⟨h1, hn⟩, h3⟩
        · rw [(R.new c (by omega)).2.2.1] at h3; cases h3
    · rintro ⟨hcx, ⟨h1, hn⟩, h3⟩
      exact ⟨⟨h1, by omega⟩, by rw [(R.old c hn hcx).2.2.1]; exact h3⟩
  have hxQ : x ∈ quietSet s := mem_quietSet.mpr ⟨hxL, hxq⟩
  refine ⟨by rw [R.Csize, h.size]; ring, ?_, fun c hc hq => ?_⟩
  · rw [hQ, hcnt, R.P]
    have h1 := h.bound
    have he := h.e_le x hxL hxq
    have hsplit := Finset.add_sum_erase (quietSet s) (fun c => cSz s c - e c) hxQ
    have heq : ∑ c ∈ (quietSet s).erase x, (cSz s' c - e c) =
        ∑ c ∈ (quietSet s).erase x, (cSz s c - e c) := by
      refine Finset.sum_congr rfl fun c hc => ?_
      obtain ⟨hcx, hc⟩ := Finset.mem_erase.mp hc
      rw [(R.old c (mem_quietSet.mp hc).1.2 hcx).1]
    rw [heq, Nat.add_mul, Nat.one_mul]
    omega
  · have hc' : LiveC s c ∨ c = s.C.size ∨ c = s.C.size + 1 := by
      simp only [LiveC, R.Csize] at hc ⊢; omega
    rw [R.P]
    rcases hc' with hc' | hn
    · have hcx : c ≠ x := by rintro rfl; rw [R.xs.2.2.1] at hq; cases hq
      rw [(R.old c hc'.2 hcx).2.2.1] at hq
      exact h.e_le c hc' hq
    · rw [(R.new c hn).2.2.1] at hq; cases hq

end OrderMaintenance.Proof
