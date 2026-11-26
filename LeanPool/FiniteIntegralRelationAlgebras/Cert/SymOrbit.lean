/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Orbit
public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Sym

/-!
# Counting with symmetry reduction

The symmetries of a `Problem` act on the assignments of its high variables by permuting bits, and
leaves are constant on orbits. Hence the sum of all leaves is a weighted sum over orbit minima
(`Problem.fixCountL_of_orbits`), certified in segments (`OrbitSeg`).
-/

@[expose] public section

namespace RACert

theorem OrbitSeg.cast {t : ℕ} {perms : List (List ℕ × List ℕ)} {F : ℕ → ℕ}
    {lo hi M W M' W' : ℕ} (h : OrbitSeg t perms F lo hi M W) (hM : Nat.beq M M' = true)
    (hW : Nat.beq W W' = true) : OrbitSeg t perms F lo hi M' W' := by
  rw [← Nat.eq_of_beq_eq_true hM, ← Nat.eq_of_beq_eq_true hW]
  exact h

/-- The weighted sum of the values of `F` at the orbit minima `(α, orbit size)` of `seg`. -/
def SegSum (F : ℕ → ℕ) (seg : List (ℕ × ℕ)) (W : ℕ) : Prop :=
  (seg.map fun e => e.2 * F e.1).sum = W

theorem SegSum.append {F : ℕ → ℕ} {s₁ s₂ : List (ℕ × ℕ)} {W₁ W₂ : ℕ} (h₁ : SegSum F s₁ W₁)
    (h₂ : SegSum F s₂ W₂) : SegSum F (s₁ ++ s₂) (W₁ + W₂) := by
  unfold SegSum at *
  rw [List.map_append, List.sum_append, h₁, h₂]

/-- The form used by generated certificates: one check of the orbit minima of a file, whose
weighted sum is assembled from the sums of its parts. -/
theorem OrbitSeg.of_checkSum {t : ℕ} {perms : List (List ℕ × List ℕ)} {F : ℕ → ℕ} {lo hi : ℕ}
    {seg : List (ℕ × ℕ)} {M W W' : ℕ} (h : checkSeg t perms lo hi seg = true)
    (hM : Nat.beq (seg.map Prod.snd).sum M = true) (hs : SegSum F seg W')
    (hW : Nat.beq W' W = true) : OrbitSeg t perms F lo hi M W :=
  OrbitSeg.of_check h (Nat.eq_of_beq_eq_true hM) (hs.trans (Nat.eq_of_beq_eq_true hW))

namespace Problem

variable {P : Problem}

/-- Leaves are invariant under the action of a symmetry on the high variables. -/
theorem leaf_actBits (hcheck : P.check = true) (hrows : P.checkRows = true) {b : ℕ}
    (hb : b ≤ P.V) {S : Sym} {e : List ℕ × List ℕ} (hS : P.checkSym b S e = true)
    (he : checkBitPerm (P.V - b) e.1 e.2 = true) {α : ℕ} (hα : α < 2 ^ (P.V - b)) :
    P.leaf b (actBits (P.V - b) e.1 α) = P.leaf b α := by
  obtain ⟨F, htop⟩ := checkSym_spec hS
  refine F.leaf_eq hcheck hrows hb hα (actBits_lt he α) ?_ ?_
  · intro j hjb hjV
    have hi : j - b < P.V - b := by omega
    have h3 := (htop (j - b) hi).2
    rw [show b + (j - b) = j by omega] at h3
    rw [testBit_actBits he, show nth 0 e.2 (j - b) = nth 0 S.vq j - b by omega]
    simp [hi]
  · intro j hjb hjV
    have hπV := F.π_lt j hjV
    have hπb : b ≤ nth 0 S.vp j := by
      have := F.low j hjV
      omega
    have hi : nth 0 S.vp j - b < P.V - b := by omega
    have h3 := (htop (nth 0 S.vp j - b) hi).2
    rw [show b + (nth 0 S.vp j - b) = nth 0 S.vp j by omega, F.ρπ j hjV] at h3
    rw [testBit_actBits he, show nth 0 e.2 (nth 0 S.vp j - b) = j - b by omega]
    simp [hi]

/-- A checked orbit sum gives the count whenever the leaf evaluator is invariant. -/
theorem fixCountL_of_invariantLeaves (hcheck : P.check = true) (hrows : P.checkRows = true)
    {b t hi : ℕ} (hb : Nat.ble b P.V = true) (ht : Nat.beq t (P.V - b) = true)
    (hhi : Nat.beq hi (2 ^ t) = true) {perms : List (List ℕ × List ℕ)}
    {gens : List (ℕ × List ℕ)} {inv : List ℕ}
    (hgrp : checkBitGroup t perms gens inv = true)
    (hinv : ∀ e ∈ perms, ∀ α < 2 ^ t, P.leaf b (actBits t e.1 α) = P.leaf b α)
    {W : ℕ} (hseg : OrbitSeg t perms (P.leaf b) 0 hi hi W) : fixCountL P.s P.n P.perm = W := by
  obtain rfl := Nat.eq_of_beq_eq_true ht
  obtain rfl := Nat.eq_of_beq_eq_true hhi
  rw [fixCountL_eq_sumLeaves hcheck hrows (Nat.le_of_ble_eq_true hb), sumLeaves_eq_sum]
  simp only [Nat.zero_add]
  exact OrbitSeg.sum_eq hgrp hinv hseg

/-- **Count with symmetry reduction.** The number of invariant lawful cycle sets is the weighted
sum of the leaves over the orbit minima of the assignments of the high variables. -/
theorem fixCountL_of_orbits (hcheck : P.check = true) (hrows : P.checkRows = true) {b t hi : ℕ}
    (hb : Nat.ble b P.V = true) (ht : Nat.beq t (P.V - b) = true)
    (hhi : Nat.beq hi (2 ^ t) = true) {syms : List Sym} {perms : List (List ℕ × List ℕ)}
    {gens : List (ℕ × List ℕ)} {inv : List ℕ} (hsyms : P.checkSyms b syms perms = true)
    (hgrp : checkBitGroup t perms gens inv = true) {W : ℕ}
    (hseg : OrbitSeg t perms (P.leaf b) 0 hi hi W) : fixCountL P.s P.n P.perm = W := by
  refine fixCountL_of_invariantLeaves hcheck hrows hb ht hhi hgrp (fun e he α hα => ?_) hseg
  obtain rfl := Nat.eq_of_beq_eq_true ht
  obtain ⟨S, hS⟩ := checkSyms_spec hsyms e he
  have hbp : checkBitPerm (P.V - b) e.1 e.2 = true := by
    simp only [checkBitGroup, Bool.and_eq_true] at hgrp
    exact List.all_eq_true.mp hgrp.1 e he
  exact leaf_actBits hcheck hrows (Nat.le_of_ble_eq_true hb) hS hbp hα

end Problem

end RACert
