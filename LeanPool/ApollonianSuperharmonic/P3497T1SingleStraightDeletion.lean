/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3475T1BoundarySubdivision
public import LeanPool.ApollonianSuperharmonic.P3497T1StrictCornerSplice

-- [TABLET NODE: P3497T1SingleStraightDeletion]

/-!
# P3497T1SingleStraightDeletion

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace StraightDeletionConstruction

private noncomputable abbrev M (n : Nat) := n + 4

private noncomputable abbrev L (n : Nat) := n + 3

private noncomputable abbrev rot (n : Nat) (i : Fin ((n + 1) + 3)) : Fin (M n) → Fin (M n) := by
  classical
  let M := n + 4
  dsimp only [StraightDeletionConstruction.M] at *
  change (Fin M → Fin M)
  exact fun h => i + h

private noncomputable abbrev sig (n : Nat) : Fin (L n) → Fin (M n) := by
  classical
  let M := n + 4
  let L := n + 3
  dsimp only [StraightDeletionConstruction.M, StraightDeletionConstruction.L] at *
  change (Fin L → Fin M)
  exact fun k =>
    ⟨if k.val = 0 then 0 else k.val + 1, by split_ifs <;> omega⟩

private theorem hM (n : Nat) : 4 ≤ (M n) := by
  classical
  let M := n + 4
  dsimp only [StraightDeletionConstruction.M] at *
  change (4 ≤ M)
  dsimp [M]; omega

private theorem hM1 (n : Nat) : 1 < (M n) := by
  classical
  let M := n + 4
  have hM : 4 ≤ M := hM n
  dsimp only [StraightDeletionConstruction.M] at *
  change (1 < M)
  omega

private theorem hM2 (n : Nat) : 2 < (M n) := by
  classical
  let M := n + 4
  have hM : 4 ≤ M := hM n
  dsimp only [StraightDeletionConstruction.M] at *
  change (2 < M)
  omega

private theorem hM3 (n : Nat) : 3 < (M n) := by
  classical
  let M := n + 4
  have hM : 4 ≤ M := hM n
  dsimp only [StraightDeletionConstruction.M] at *
  change (3 < M)
  omega

private theorem hL1 (n : Nat) : 1 < (L n) := by
  classical
  let M := n + 4
  let L := n + 3
  have hM : 4 ≤ M := hM n
  dsimp only [StraightDeletionConstruction.L] at *
  change (1 < L)
  dsimp [L]; omega

private theorem hLM (n : Nat) : (L n) + 1 = (M n) := by
  rfl

private theorem hrot (n : Nat) (i : Fin ((n + 1) + 3)) : Function.Injective (rot n i) := by
  classical
  let M := n + 4
  let rot : Fin M → Fin M := fun h => i + h
  change (Function.Injective rot)
  intro a b hab
  apply Fin.ext
  have hv := congrArg Fin.val hab
  simp only [rot, Fin.val_add_eq_ite] at hv
  simp only [M] at hv
  have hi := i.isLt
  have hla := a.isLt
  have hlb := b.isLt
  simp only [M] at hi hla hlb
  by_cases ha : n + 4 ≤ i.val + a.val <;>
    by_cases hb : n + 4 ≤ i.val + b.val <;> simp_all <;> omega

private theorem hsig (n : Nat) : Function.Injective (sig n) := by
  classical
  let M := n + 4
  let L := n + 3
  let sig : Fin L → Fin M := fun k =>
    ⟨if k.val = 0 then 0 else k.val + 1, by split_ifs <;> omega⟩
  change (Function.Injective sig)
  intro a b hab
  apply Fin.ext
  have hv := congrArg Fin.val hab
  simp only [sig] at hv
  split_ifs at hv <;> omega

private theorem hrotSucc (n : Nat) (i : Fin ((n + 1) + 3)) (h : Fin (M n)) : (rot n i) (h + 1) =
    (rot n i) h + 1 := by
  classical
  let M := n + 4
  let rot : Fin M → Fin M := fun h => i + h
  dsimp only [StraightDeletionConstruction.M] at *
  change (rot (h + 1) = rot h + 1)
  apply Fin.ext
  change (i.val + (h.val + 1) % M) % M =
    ((i.val + h.val) % M + 1) % M
  calc
    (i.val + (h.val + 1) % M) % M =
        ((h.val + 1) % M + i.val) % M := by rw [Nat.add_comm]
    _ = (h.val + 1 + i.val) % M := Nat.mod_add_mod (h.val + 1) M i.val
    _ = (i.val + h.val + 1) % M := by congr 1; omega
    _ = ((i.val + h.val) % M + 1) % M := (Nat.mod_add_mod (i.val + h.val) M 1).symm

private theorem hsigSucc (n : Nat) (k : Fin (L n)) (hk : k.val ≠ 0) :
      (sig n) (k + 1) = (sig n) k + 1 := by
  classical
  let M := n + 4
  let L := n + 3
  let sig : Fin L → Fin M := fun k =>
    ⟨if k.val = 0 then 0 else k.val + 1, by split_ifs <;> omega⟩
  have hM1 : 1 < M := hM1 n
  have hL1 : 1 < L := hL1 n
  have hLM : L + 1 = M := hLM n
  dsimp only [StraightDeletionConstruction.L] at *
  change (sig (k + 1) = sig k + 1)
  apply Fin.ext
  have hpos : 0 < k.val := Nat.pos_of_ne_zero hk
  have hk0 : k ≠ 0 := by
    intro h
    apply hk
    exact congrArg Fin.val h
  by_cases hlast : k.val + 1 = L
  · simp [sig, Fin.val_add_eq_ite, hlast,
      hk0, hLM, Nat.mod_eq_of_lt hM1, Nat.mod_eq_of_lt hL1]
  · have hklt : k.val < L := k.isLt
    have hnext : k.val + 1 < L := by omega
    have hbound : k.val + 2 < M := by omega
    have hcond1 : ¬ L ≤ k.val + 1 := by omega
    have hcond2 : ¬ M ≤ k.val + 1 + 1 := by omega
    simp [sig, Fin.val_add_eq_ite, hk,
      hk0, Nat.mod_eq_of_lt hM1,
      Nat.mod_eq_of_lt hL1, hcond1, hcond2]

private noncomputable abbrev r (n : Nat) (p : P3381T1PolygonBoundary (n + 1)) (i : Fin ((n + 1)
    + 3)) : Fin (M n) → Real × Real := by
  classical
  let M := n + 4
  let rot : Fin M → Fin M := fun h => i + h
  dsimp only [StraightDeletionConstruction.M] at *
  change (Fin M → Real × Real)
  exact fun h => p.vertex (rot h)

private theorem hr (n : Nat) (p : P3381T1PolygonBoundary (n + 1)) (i : Fin ((n + 1) + 3)) :
    Function.Injective (r n p i) := by
  classical
  let M := n + 4
  let rot : Fin M → Fin M := fun h => i + h
  have hrot : Function.Injective rot := hrot n i
  let r : Fin M → Real × Real := fun h => p.vertex (rot h)
  change (Function.Injective r)
  intro a b hab
  exact hrot (p.injective hab)

private theorem ha (n : Nat) (p : P3381T1PolygonBoundary (n + 1)) (i : Fin ((n + 1) + 3)) : (r
    n p i) 0 ≠ (r n p i) 1 := by
  classical
  let M := n + 4
  let rot : Fin M → Fin M := fun h => i + h
  have hM1 : 1 < M := hM1 n
  let r : Fin M → Real × Real := fun h => p.vertex (rot h)
  have hr : Function.Injective r := hr n p i
  change (r 0 ≠ r 1)
  intro h
  have h01 : (0 : Fin M) = 1 := hr h
  have hv := congrArg Fin.val h01
  simp [Nat.mod_eq_of_lt hM1] at hv

private theorem hbc (n : Nat) (p : P3381T1PolygonBoundary (n + 1)) (i : Fin ((n + 1) + 3)) : (r
    n p i) 1 ≠ (r n p i) 2 := by
  classical
  let M := n + 4
  let rot : Fin M → Fin M := fun h => i + h
  have hM1 : 1 < M := hM1 n
  have hM2 : 2 < M := hM2 n
  let r : Fin M → Real × Real := fun h => p.vertex (rot h)
  have hr : Function.Injective r := hr n p i
  change (r 1 ≠ r 2)
  intro h
  have h12 : (1 : Fin M) = 2 := hr h
  have hv := congrArg Fin.val h12
  simp [Nat.mod_eq_of_lt hM1, Nat.mod_eq_of_lt hM2] at hv

private theorem hac (n : Nat) (p : P3381T1PolygonBoundary (n + 1)) (i : Fin ((n + 1) + 3)) : (r
    n p i) 0 ≠ (r n p i) 2 := by
  classical
  let M := n + 4
  let rot : Fin M → Fin M := fun h => i + h
  have hM2 : 2 < M := hM2 n
  let r : Fin M → Real × Real := fun h => p.vertex (rot h)
  have hr : Function.Injective r := hr n p i
  change (r 0 ≠ r 2)
  intro h
  have h02 : (0 : Fin M) = 2 := hr h
  have hv := congrArg Fin.val h02
  simp [Nat.mod_eq_of_lt hM2] at hv

private theorem hdet' (n : Nat) (p : P3381T1PolygonBoundary (n + 1)) (i : Fin ((n + 1) + 3))
    (hdet : P3381T1TriangleDeterminant (fun j : Fin 3 => p.vertex (i + ⟨j.val,
    Nat.lt_of_lt_of_le j.isLt (Nat.le_add_left 3 (n + 1))⟩)) = 0) : P3381T1TriangleDeterminant
    ![(r n p i) 0, (r n p i) 1, (r n p i) 2] = 0 := by
  classical
  let M := n + 4
  let rot : Fin M → Fin M := fun h => i + h
  have hM : 4 ≤ M := hM n
  let r : Fin M → Real × Real := fun h => p.vertex (rot h)
  change (P3381T1TriangleDeterminant ![r 0, r 1, r 2] = 0)
  have heq : (fun j : Fin 3 => r ⟨j.val, by omega⟩) =
      (fun j => p.vertex (i + ⟨j.val, Nat.lt_of_lt_of_le j.isLt
        (Nat.le_add_left 3 (n + 1))⟩)) := by
    funext j
    fin_cases j <;> simp [r, rot]
  have hvec : ![r 0, r 1, r 2] = (fun j : Fin 3 => r ⟨j.val, by omega⟩) := by
    funext j
    fin_cases j
    · rfl
    · rfl
    · exact congrArg r (Fin.ext rfl)
  rw [hvec, heq]
  exact hdet

private theorem hint (n : Nat) (p : P3381T1PolygonBoundary (n + 1)) (i : Fin ((n + 1) + 3)) :
    segment Real ((r n p i) 0) ((r n p i) 1) ∩ segment Real ((r n p i) 1) ((r n p i) 2) =
        Set.singleton ((r n p i) 1) := by
  classical
  let M := n + 4
  let rot : Fin M → Fin M := fun h => i + h
  have hM : 4 ≤ M := hM n
  have hrot : Function.Injective rot := hrot n i
  let r : Fin M → Real × Real := fun h => p.vertex (rot h)
  have ha : r 0 ≠ r 1 := ha n p i
  have hbc : r 1 ≠ r 2 := hbc n p i
  have hac : r 0 ≠ r 2 := hac n p i
  change (segment Real (r 0) (r 1) ∩ segment Real (r 1) (r 2) = {r 1})
  have hidx : rot (0 : Fin M) ≠ rot 1 := by
    intro h
    have hv := congrArg Fin.val (hrot h)
    norm_num at hv
    omega
  have he := p.edge_intersection (rot 0) (rot 1) (by
    exact hidx)
  have hstep : rot 1 + 1 = rot 2 := by
    apply Fin.ext
    change ((i.val + 1) % M + 1) % M = (i.val + 2) % M
    simp []
  have hp01 : p.vertex i ≠ p.vertex (i + 1) := by simpa [r, rot] using ha
  have hp12 : p.vertex (i + 1) ≠ p.vertex (i + 2) := by
    simpa [r, rot, hstep] using hbc
  have hp02 : p.vertex i ≠ p.vertex (i + 2) := by
    simpa [r, rot, hstep] using hac
  have he' : segment Real (p.vertex i) (p.vertex (i + 1)) ∩
      segment Real (p.vertex (i + 1)) (p.vertex (i + 2)) =
      {x | (x = p.vertex i ∨ x = p.vertex (i + 1)) ∧
        (x = p.vertex (i + 1) ∨ x = p.vertex (i + 2))} := by
    simpa [r, rot, hstep] using he
  have hfinal : segment Real (p.vertex i) (p.vertex (i + 1)) ∩
      segment Real (p.vertex (i + 1)) (p.vertex (i + 2)) =
      {p.vertex (i + 1)} := by
    rw [he']
    ext x
    constructor
    · rintro ⟨hleft, hright⟩
      rcases hleft with hleft | hleft
      · rcases hright with hright | hright
        · exact False.elim (hp01 (hleft.symm.trans hright))
        · exact False.elim (hp02 (hleft.symm.trans hright))
      · rcases hright with hright | hright
        · exact hleft
        · exact False.elim (hp12 (hleft.symm.trans hright))
    · intro hx
      subst x
      exact ⟨Or.inr rfl, Or.inl rfl⟩
  simpa [r, rot, hstep] using hfinal

private theorem oldInt (n : Nat) (p : P3381T1PolygonBoundary (n + 1)) (i : Fin ((n + 1) + 3))
    (a b : Fin (M n)) (hab : a ≠ b) :
      segment Real ((r n p i) a) ((r n p i) (a + 1)) ∩ segment Real ((r n p i) b) ((r n p i) (b +
          1)) =
        {x | (x = (r n p i) a ∨ x = (r n p i) (a + 1)) ∧ (x = (r n p i) b ∨ x = (r n p i) (b +
            1))} := by
  classical
  let M := n + 4
  let rot : Fin M → Fin M := fun h => i + h
  have hrot : Function.Injective rot := hrot n i
  have hrotSucc (h : Fin M) : rot (h + 1) = rot h + 1 := hrotSucc n i h
  let r : Fin M → Real × Real := fun h => p.vertex (rot h)
  change (segment Real (r a) (r (a + 1)) ∩ segment Real (r b) (r (b + 1)) =
        {x | (x = r a ∨ x = r (a + 1)) ∧ (x = r b ∨ x = r (b + 1))})
  have he := p.edge_intersection (rot a) (rot b) (fun h => hab (hrot h))
  simpa [r, hrotSucc] using he

private theorem rEq (n : Nat) (p : P3381T1PolygonBoundary (n + 1)) (i : Fin ((n + 1) + 3)) (a b
    : Fin (M n)) : (r n p i) a = (r n p i) b ↔ a = b := by
  classical
  let M := n + 4
  let rot : Fin M → Fin M := fun h => i + h
  let r : Fin M → Real × Real := fun h => p.vertex (rot h)
  have hr : Function.Injective r := hr n p i
  change (r a = r b ↔ a = b)
  exact ⟨fun h => hr h, fun h => congrArg r h⟩

private theorem sig0 (n : Nat) : (sig n) (0 : Fin (L n)) = 0 := by
  classical
  let M := n + 4
  let L := n + 3
  let sig : Fin L → Fin M := fun k =>
    ⟨if k.val = 0 then 0 else k.val + 1, by split_ifs <;> omega⟩
  change (sig (0 : Fin L) = 0)
  apply Fin.ext; simp [sig]

private theorem hval1L (n : Nat) : (1 : Fin (L n)).val = 1 := by
  classical
  let L := n + 3
  have hL1 : 1 < L := hL1 n
  change ((1 : Fin L).val = 1)
  simp [Nat.mod_eq_of_lt hL1]

private theorem hval2M (n : Nat) : (2 : Fin (M n)).val = 2 := by
  classical
  let M := n + 4
  have hM2 : 2 < M := hM2 n
  change ((2 : Fin M).val = 2)
  simp [Nat.mod_eq_of_lt hM2]

private theorem hmod1M (n : Nat) : 1 % (M n) = 1 := by
  classical
  let M := n + 4
  have hM1 : 1 < M := hM1 n
  dsimp only [StraightDeletionConstruction.M] at *
  change (1 % M = 1)
  exact Nat.mod_eq_of_lt hM1

private theorem hmod2M (n : Nat) : 2 % (M n) = 2 := by
  classical
  let M := n + 4
  have hM2 : 2 < M := hM2 n
  dsimp only [StraightDeletionConstruction.M] at *
  change (2 % M = 2)
  exact Nat.mod_eq_of_lt hM2

private theorem hmod3M (n : Nat) : 3 % (M n) = 3 := by
  classical
  let M := n + 4
  have hM3 : 3 < M := hM3 n
  dsimp only [StraightDeletionConstruction.M] at *
  change (3 % M = 3)
  exact Nat.mod_eq_of_lt hM3

private theorem new01 (n : Nat) : (0 : Fin (L n)) + 1 = 1 := by
  classical
  let L := n + 3
  have hL1 : 1 < L := hL1 n
  dsimp only [StraightDeletionConstruction.L] at *
  change ((0 : Fin L) + 1 = 1)
  apply Fin.ext
  simp [Nat.mod_eq_of_lt hL1]

private theorem sig1 (n : Nat) : (sig n) (1 : Fin (L n)) = 2 := by
  classical
  let M := n + 4
  let L := n + 3
  let sig : Fin L → Fin M := fun k =>
    ⟨if k.val = 0 then 0 else k.val + 1, by split_ifs <;> omega⟩
  have hval1L : (1 : Fin L).val = 1 := hval1L n
  have hval2M : (2 : Fin M).val = 2 := hval2M n
  change (sig (1 : Fin L) = 2)
  apply Fin.ext
  change (if (1 : Fin L).val = 0 then 0 else (1 : Fin L).val + 1) =
    (2 : Fin M).val
  rw [hval1L, hval2M]
  norm_num

private theorem old01 (n : Nat) : (0 : Fin (M n)) + 1 = 1 := by
  classical
  let M := n + 4
  have hmod1M : 1 % M = 1 := hmod1M n
  dsimp only [StraightDeletionConstruction.M] at *
  change ((0 : Fin M) + 1 = 1)
  apply Fin.ext
  simp [hmod1M]

private theorem old12 (n : Nat) : (1 : Fin (M n)) + 1 = 2 := by
  classical
  let M := n + 4
  have hM : 4 ≤ M := hM n
  have hmod1M : 1 % M = 1 := hmod1M n
  have hmod2M : 2 % M = 2 := hmod2M n
  dsimp only [StraightDeletionConstruction.M] at *
  change ((1 : Fin M) + 1 = 2)
  apply Fin.ext
  simp [Fin.val_add_eq_ite, hmod1M, hmod2M]
  omega

private theorem old23 (n : Nat) : (2 : Fin (M n)) + 1 = 3 := by
  classical
  let M := n + 4
  have hM : 4 ≤ M := hM n
  have hmod1M : 1 % M = 1 := hmod1M n
  have hmod2M : 2 % M = 2 := hmod2M n
  have hmod3M : 3 % M = 3 := hmod3M n
  dsimp only [StraightDeletionConstruction.M] at *
  change ((2 : Fin M) + 1 = 3)
  apply Fin.ext
  simp [Fin.val_add_eq_ite, hmod1M, hmod2M, hmod3M]
  omega

private theorem qedge0 (n : Nat) (p : P3381T1PolygonBoundary (n + 1)) (i : Fin ((n + 1) + 3)) :
    segment Real ((r n p i) ((sig n) 0)) ((r n p i) ((sig n) (0 + 1))) =
      segment Real ((r n p i) 0) ((r n p i) 2) := by
  classical
  let M := n + 4
  let L := n + 3
  let rot : Fin M → Fin M := fun h => i + h
  let sig : Fin L → Fin M := fun k =>
    ⟨if k.val = 0 then 0 else k.val + 1, by split_ifs <;> omega⟩
  let r : Fin M → Real × Real := fun h => p.vertex (rot h)
  have sig0 : sig (0 : Fin L) = 0 := sig0 n
  have sig1 : sig (1 : Fin L) = 2 := sig1 n
  change (segment Real (r (sig 0)) (r (sig (0 + 1))) =
      segment Real (r 0) (r 2))
  simp [sig0, sig1]

private theorem qedgePos (n : Nat) (p : P3381T1PolygonBoundary (n + 1)) (i : Fin ((n + 1) + 3))
    (k : Fin (L n)) (hk : k.val ≠ 0) :
      segment Real ((r n p i) ((sig n) k)) ((r n p i) ((sig n) (k + 1))) =
        segment Real ((r n p i) ((sig n) k)) ((r n p i) ((sig n) k + 1)) := by
  classical
  let M := n + 4
  let L := n + 3
  let rot : Fin M → Fin M := fun h => i + h
  let sig : Fin L → Fin M := fun k =>
    ⟨if k.val = 0 then 0 else k.val + 1, by split_ifs <;> omega⟩
  have hsigSucc (k : Fin L) (hk : k.val ≠ 0) :
      sig (k + 1) = sig k + 1 := hsigSucc n k hk
  let r : Fin M → Real × Real := fun h => p.vertex (rot h)
  dsimp only [StraightDeletionConstruction.L] at *
  change (segment Real (r (sig k)) (r (sig (k + 1))) =
        segment Real (r (sig k)) (r (sig k + 1)))
  rw [hsigSucc k hk]

private noncomputable abbrev invrot (n : Nat) (i : Fin ((n + 1) + 3)) : Fin (M n) → Fin (M n) := by
  classical
  let M := n + 4
  dsimp only [StraightDeletionConstruction.M] at *
  change (Fin M → Fin M)
  exact fun j =>
    if h : j.val < i.val then ⟨j.val + M - i.val, by omega⟩
    else ⟨j.val - i.val, by omega⟩

private theorem hinvrot (n : Nat) (i : Fin ((n + 1) + 3)) (j : Fin (M n)) : (rot n i) ((invrot n
    i) j) = j := by
  classical
  let M := n + 4
  let rot : Fin M → Fin M := fun h => i + h
  have hM : 4 ≤ M := hM n
  let invrot : Fin M → Fin M := fun j =>
    if h : j.val < i.val then ⟨j.val + M - i.val, by omega⟩
    else ⟨j.val - i.val, by omega⟩
  dsimp only [StraightDeletionConstruction.M] at *
  change (rot (invrot j) = j)
  apply Fin.ext
  unfold rot invrot
  split_ifs with hji
  · simp only [Fin.val_add_eq_ite]
    split_ifs <;> omega
  · simp only [Fin.val_add_eq_ite]
    split_ifs <;> omega

private theorem hinvrotRot (n : Nat) (i : Fin ((n + 1) + 3)) (j : Fin (M n)) : (invrot n i) ((rot
    n i) j) = j := by
  classical
  let M := n + 4
  let rot : Fin M → Fin M := fun h => i + h
  have hrot : Function.Injective rot := hrot n i
  let invrot : Fin M → Fin M := fun j =>
    if h : j.val < i.val then ⟨j.val + M - i.val, by omega⟩
    else ⟨j.val - i.val, by omega⟩
  have hinvrot (j : Fin M) : rot (invrot j) = j := hinvrot n i j
  dsimp only [StraightDeletionConstruction.M] at *
  change (invrot (rot j) = j)
  apply hrot
  simpa using hinvrot (rot j)

private noncomputable abbrev col (n : Nat) : Fin (M n) → Fin (L n) := by
  classical
  let M := n + 4
  let L := n + 3
  have hM : 4 ≤ M := hM n
  dsimp only [StraightDeletionConstruction.M, StraightDeletionConstruction.L] at *
  change (Fin M → Fin L)
  exact fun j =>
    ⟨if j.val ≤ 1 then 0 else j.val - 1, by split_ifs <;> omega⟩

private theorem colSurv (n : Nat) (k : Fin (L n)) : (col n) ((sig n) k) = k := by
  classical
  let M := n + 4
  let L := n + 3
  let sig : Fin L → Fin M := fun k =>
    ⟨if k.val = 0 then 0 else k.val + 1, by split_ifs <;> omega⟩
  have hM : 4 ≤ M := hM n
  let col : Fin M → Fin L := fun j =>
    ⟨if j.val ≤ 1 then 0 else j.val - 1, by split_ifs <;> omega⟩
  dsimp only [StraightDeletionConstruction.L] at *
  change (col (sig k) = k)
  apply Fin.ext
  simp only [col, sig]
  split_ifs at * <;> omega

private theorem sigCol (n : Nat) (h : Fin (M n)) (hh : 2 ≤ h.val) : (sig n) ((col n) h) = h := by
  classical
  let M := n + 4
  let L := n + 3
  let sig : Fin L → Fin M := fun k =>
    ⟨if k.val = 0 then 0 else k.val + 1, by split_ifs <;> omega⟩
  have hM : 4 ≤ M := hM n
  let col : Fin M → Fin L := fun j =>
    ⟨if j.val ≤ 1 then 0 else j.val - 1, by split_ifs <;> omega⟩
  dsimp only [StraightDeletionConstruction.M] at *
  change (sig (col h) = h)
  apply Fin.ext
  simp only [sig, col]
  split_ifs <;> omega

private theorem colZero (n : Nat) : (col n) (0 : Fin (M n)) = 0 := by
  classical
  let M := n + 4
  let L := n + 3
  have hM : 4 ≤ M := hM n
  let col : Fin M → Fin L := fun j =>
    ⟨if j.val ≤ 1 then 0 else j.val - 1, by split_ifs <;> omega⟩
  change (col (0 : Fin M) = 0)
  apply Fin.ext; simp [col]

private theorem colOne (n : Nat) : (col n) (1 : Fin (M n)) = 0 := by
  classical
  let M := n + 4
  let L := n + 3
  have hM : 4 ≤ M := hM n
  have hM1 : 1 < M := hM1 n
  let col : Fin M → Fin L := fun j =>
    ⟨if j.val ≤ 1 then 0 else j.val - 1, by split_ifs <;> omega⟩
  change (col (1 : Fin M) = 0)
  apply Fin.ext
  change (if 1 % M ≤ 1 then 0 else 1 % M - 1) = 0
  rw [Nat.mod_eq_of_lt hM1]
  rfl

private theorem colTwo (n : Nat) : (col n) (2 : Fin (M n)) = 1 := by
  classical
  let M := n + 4
  let L := n + 3
  have hM : 4 ≤ M := hM n
  have hL1 : 1 < L := hL1 n
  have hmod2M : 2 % M = 2 := hmod2M n
  let col : Fin M → Fin L := fun j =>
    ⟨if j.val ≤ 1 then 0 else j.val - 1, by split_ifs <;> omega⟩
  change (col (2 : Fin M) = 1)
  apply Fin.ext
  simp [col, hmod2M, Nat.mod_eq_of_lt hL1]

private theorem colSucc (n : Nat) (h : Fin (M n)) (hh : 2 ≤ h.val) :
      (col n) (h + 1) = (col n) h + 1 := by
  classical
  let M := n + 4
  let L := n + 3
  have hM : 4 ≤ M := hM n
  let col : Fin M → Fin L := fun j =>
    ⟨if j.val ≤ 1 then 0 else j.val - 1, by split_ifs <;> omega⟩
  dsimp only [StraightDeletionConstruction.M] at *
  change (col (h + 1) = col h + 1)
  apply Fin.ext
  simp only [col, Fin.val_add_eq_ite, Fin.val_one, M, L]
  split_ifs <;> simp_all only [ite_true, ite_false] <;>
    split_ifs <;> omega

private theorem invSucc (n : Nat) (i : Fin ((n + 1) + 3)) (j : Fin (M n)) : (invrot n i) (j + 1)
    = (invrot n i) j + 1 := by
  classical
  let M := n + 4
  let rot : Fin M → Fin M := fun h => i + h
  have hrot : Function.Injective rot := hrot n i
  have hrotSucc (h : Fin M) : rot (h + 1) = rot h + 1 := hrotSucc n i h
  let invrot : Fin M → Fin M := fun j =>
    if h : j.val < i.val then ⟨j.val + M - i.val, by omega⟩
    else ⟨j.val - i.val, by omega⟩
  have hinvrot (j : Fin M) : rot (invrot j) = j := hinvrot n i j
  dsimp only [StraightDeletionConstruction.M] at *
  change (invrot (j + 1) = invrot j + 1)
  apply hrot
  rw [hrotSucc, hinvrot, hinvrot]

private theorem firstInt (n : Nat) (p : P3381T1PolygonBoundary (n + 1)) (i : Fin ((n + 1) + 3))
    (hunion : segment Real ((r n p i) 0) ((r n p i) 1) ∪ segment Real ((r n p i) 1) ((r n p i) 2)
    = segment Real ((r n p i) 0) ((r n p i) 2)) (c : Fin (L n)) (hc : c.val ≠ 0) :
      segment Real ((r n p i) ((sig n) 0)) ((r n p i) ((sig n) (0 + 1))) ∩
          segment Real ((r n p i) ((sig n) c)) ((r n p i) ((sig n) (c + 1))) =
        {x | (x = (r n p i) ((sig n) 0) ∨ x = (r n p i) ((sig n) (0 + 1))) ∧
          (x = (r n p i) ((sig n) c) ∨ x = (r n p i) ((sig n) (c + 1)))} := by
  classical
  let M := n + 4
  let L := n + 3
  let rot : Fin M → Fin M := fun h => i + h
  let sig : Fin L → Fin M := fun k =>
    ⟨if k.val = 0 then 0 else k.val + 1, by split_ifs <;> omega⟩
  have hM : 4 ≤ M := hM n
  have hM1 : 1 < M := hM1 n
  have hsigSucc (k : Fin L) (hk : k.val ≠ 0) :
      sig (k + 1) = sig k + 1 := hsigSucc n k hk
  let r : Fin M → Real × Real := fun h => p.vertex (rot h)
  have ha : r 0 ≠ r 1 := ha n p i
  have hbc : r 1 ≠ r 2 := hbc n p i
  have hac : r 0 ≠ r 2 := hac n p i
  have oldInt (a b : Fin M) (hab : a ≠ b) :
      segment Real (r a) (r (a + 1)) ∩ segment Real (r b) (r (b + 1)) =
        {x | (x = r a ∨ x = r (a + 1)) ∧ (x = r b ∨ x = r (b + 1))} := oldInt n p i a b hab
  have rEq (a b : Fin M) : r a = r b ↔ a = b := rEq n p i a b
  have sig0 : sig (0 : Fin L) = 0 := sig0 n
  have hval2M : (2 : Fin M).val = 2 := hval2M n
  have hmod1M : 1 % M = 1 := hmod1M n
  have hmod2M : 2 % M = 2 := hmod2M n
  have hmod3M : 3 % M = 3 := hmod3M n
  have new01 : (0 : Fin L) + 1 = 1 := new01 n
  have sig1 : sig (1 : Fin L) = 2 := sig1 n
  have old01 : (0 : Fin M) + 1 = 1 := old01 n
  have old12 : (1 : Fin M) + 1 = 2 := old12 n
  have old23 : (2 : Fin M) + 1 = 3 := old23 n
  have qedge0 : segment Real (r (sig 0)) (r (sig (0 + 1))) =
      segment Real (r 0) (r 2) := qedge0 n p i
  have qedgePos (k : Fin L) (hk : k.val ≠ 0) :
      segment Real (r (sig k)) (r (sig (k + 1))) =
        segment Real (r (sig k)) (r (sig k + 1)) := qedgePos n p i k hk
  dsimp only [StraightDeletionConstruction.L] at *
  change segment Real (r 0) (r 1) ∪ segment Real (r 1) (r 2) =
    segment Real (r 0) (r 2) at hunion
  change (segment Real (r (sig 0)) (r (sig (0 + 1))) ∩
          segment Real (r (sig c)) (r (sig (c + 1))) =
        {x | (x = r (sig 0) ∨ x = r (sig (0 + 1))) ∧
          (x = r (sig c) ∨ x = r (sig (c + 1)))})
  let h := sig c
  have hhval : h.val = c.val + 1 := by simp [h, sig, hc]
  have hlow : 2 ≤ h.val := by omega
  have hneq0 : h ≠ 0 := by
    intro he
    have hv : h.val = 0 := by simpa using congrArg Fin.val he
    omega
  have hneq1 : h ≠ 1 := by
    intro he
    have hv : h.val = 1 := by
      simpa [Nat.mod_eq_of_lt hM1] using congrArg Fin.val he
    omega
  have hnextne : h + 1 ≠ 1 := by
    intro he
    apply hneq0
    apply add_right_cancel (b := (1 : Fin M))
    simpa only [zero_add] using he
  have hr1h : r 1 ≠ r h := fun he => hneq1 ((rEq h 1).mp he.symm)
  have hr1next : r 1 ≠ r (h + 1) := fun he => hnextne ((rEq (h + 1) 1).mp he.symm)
  have h0 := oldInt 0 h hneq0.symm
  have h1 := oldInt 1 h hneq1.symm
  simp only [old01] at h0
  simp only [old12] at h1
  rw [qedge0, qedgePos c hc]
  simp only [new01, sig0, sig1, hsigSucc c hc]
  change segment Real (r 0) (r 2) ∩ segment Real (r h) (r (h + 1)) =
    {x | (x = r 0 ∨ x = r 2) ∧ (x = r h ∨ x = r (h + 1))}
  rw [← hunion, Set.union_inter_distrib_right, h0, h1]
  ext x
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  by_cases hx : x = r 1
  · subst x
    simp [ha.symm, hbc, hr1h, hr1next]
  · simp only [hx, or_false, false_or, or_and_right]

private noncomputable abbrev q (n : Nat) (p : P3381T1PolygonBoundary (n + 1)) (i : Fin ((n + 1)
    + 3)) (hunion : segment Real ((r n p i) 0) ((r n p i) 1) ∪ segment Real ((r n p i) 1) ((r n p
    i) 2) = segment Real ((r n p i) 0) ((r n p i) 2)) : P3381T1PolygonBoundary n := by
  classical
  let M := n + 4
  let L := n + 3
  let rot : Fin M → Fin M := fun h => i + h
  let sig : Fin L → Fin M := fun k =>
    ⟨if k.val = 0 then 0 else k.val + 1, by split_ifs <;> omega⟩
  have hrot : Function.Injective rot := hrot n i
  have hsig : Function.Injective sig := hsig n
  have hsigSucc (k : Fin L) (hk : k.val ≠ 0) :
      sig (k + 1) = sig k + 1 := hsigSucc n k hk
  let r : Fin M → Real × Real := fun h => p.vertex (rot h)
  have ha : r 0 ≠ r 1 := ha n p i
  have oldInt (a b : Fin M) (hab : a ≠ b) :
      segment Real (r a) (r (a + 1)) ∩ segment Real (r b) (r (b + 1)) =
        {x | (x = r a ∨ x = r (a + 1)) ∧ (x = r b ∨ x = r (b + 1))} := oldInt n p i a b hab
  have firstInt (c : Fin L) (hc : c.val ≠ 0) :
      segment Real (r (sig 0)) (r (sig (0 + 1))) ∩
          segment Real (r (sig c)) (r (sig (c + 1))) =
        {x | (x = r (sig 0) ∨ x = r (sig (0 + 1))) ∧
          (x = r (sig c) ∨ x = r (sig (c + 1)))} := firstInt n p i hunion c hc
  exact {
    vertex := fun k => r (sig k)
    rational := fun k => p.rational (rot (sig k))
    injective := fun a b h => hsig (hrot (p.injective h))
    edge_intersection := by
      intro a b hab
      by_cases ha0 : a.val = 0
      · have ha : a = 0 := Fin.ext ha0
        subst a
        have hb : b.val ≠ 0 := by
          intro h
          apply hab
          exact Fin.ext h.symm
        exact firstInt b hb
      · by_cases hb0 : b.val = 0
        · have hb : b = 0 := Fin.ext hb0
          subst b
          have ha : a.val ≠ 0 := by
            intro h
            apply hab
            exact Fin.ext h
          have hf := firstInt a ha
          rw [Set.inter_comm]
          rw [hf]
          ext x
          constructor
          · rintro ⟨hleft, hright⟩
            exact ⟨hright, hleft⟩
          · rintro ⟨hleft, hright⟩
            exact ⟨hright, hleft⟩
        · have ha : a.val ≠ 0 := ha0
          have hb : b.val ≠ 0 := hb0
          have hab' : sig a ≠ sig b := fun h => hab (hsig h)
          simpa [hsigSucc a ha, hsigSucc b hb] using oldInt (sig a) (sig b) hab'
  }

private noncomputable def boundarySubdivision {n : Nat} (p : P3381T1PolygonBoundary (n + 1))
    (i : Fin ((n + 1) + 3))
    (hdet : P3381T1TriangleDeterminant (fun j : Fin 3 =>
      p.vertex (i + ⟨j.val, Nat.lt_of_lt_of_le j.isLt
        (Nat.le_add_left 3 (n + 1))⟩)) = 0)
    (t : Real) (ht0 : 0 < t) (ht1 : t < 1)
    (hsplice : r n p i 1 = (1 - t) • r n p i 0 + t • r n p i 2)
    (hunion : segment Real (r n p i 0) (r n p i 1) ∪
      segment Real (r n p i 1) (r n p i 2) = segment Real (r n p i 0) (r n p i 2)) :
    P3475T1BoundarySubdivision (q n p i hunion) p := by
-- BODY
  classical
  let M := n + 4
  let L := n + 3
  let rot : Fin M → Fin M := fun h => i + h
  let sig : Fin L → Fin M := fun k =>
    ⟨if k.val = 0 then 0 else k.val + 1, by split_ifs <;> omega⟩
  have hM : 4 ≤ M := StraightDeletionConstruction.hM n
  have hM1 : 1 < M := StraightDeletionConstruction.hM1 n
  have hM2 : 2 < M := StraightDeletionConstruction.hM2 n
  have hM3 : 3 < M := StraightDeletionConstruction.hM3 n
  have hL1 : 1 < L := StraightDeletionConstruction.hL1 n
  have hLM : L + 1 = M := StraightDeletionConstruction.hLM n
  have hrot : Function.Injective rot := StraightDeletionConstruction.hrot n i
  have hsig : Function.Injective sig := StraightDeletionConstruction.hsig n
  have hrotSucc (h : Fin M) : rot (h + 1) = rot h + 1 := StraightDeletionConstruction.hrotSucc n i h
  have hsigSucc (k : Fin L) (hk : k.val ≠ 0) :
      sig (k + 1) = sig k + 1 := StraightDeletionConstruction.hsigSucc n k hk
  let r : Fin M → Real × Real := fun h => p.vertex (rot h)
  have hr : Function.Injective r := StraightDeletionConstruction.hr n p i
  have ha : r 0 ≠ r 1 := StraightDeletionConstruction.ha n p i
  have hbc : r 1 ≠ r 2 := StraightDeletionConstruction.hbc n p i
  have hac : r 0 ≠ r 2 := StraightDeletionConstruction.hac n p i
  have hdet' : P3381T1TriangleDeterminant ![r 0, r 1, r 2] = 0 :=
      StraightDeletionConstruction.hdet' n p i hdet
  have hint : segment Real (r 0) (r 1) ∩ segment Real (r 1) (r 2) = {r 1} :=
      StraightDeletionConstruction.hint n p i
  have oldInt (a b : Fin M) (hab : a ≠ b) :
      segment Real (r a) (r (a + 1)) ∩ segment Real (r b) (r (b + 1)) =
        {x | (x = r a ∨ x = r (a + 1)) ∧ (x = r b ∨ x = r (b + 1))} :=
            StraightDeletionConstruction.oldInt n p i a b hab
  have rEq (a b : Fin M) : r a = r b ↔ a = b := StraightDeletionConstruction.rEq n p i a b
  have sig0 : sig (0 : Fin L) = 0 := StraightDeletionConstruction.sig0 n
  have hval1L : (1 : Fin L).val = 1 := StraightDeletionConstruction.hval1L n
  have hval2M : (2 : Fin M).val = 2 := StraightDeletionConstruction.hval2M n
  have hmod1M : 1 % M = 1 := StraightDeletionConstruction.hmod1M n
  have hmod2M : 2 % M = 2 := StraightDeletionConstruction.hmod2M n
  have hmod3M : 3 % M = 3 := StraightDeletionConstruction.hmod3M n
  have new01 : (0 : Fin L) + 1 = 1 := StraightDeletionConstruction.new01 n
  have sig1 : sig (1 : Fin L) = 2 := StraightDeletionConstruction.sig1 n
  have old01 : (0 : Fin M) + 1 = 1 := StraightDeletionConstruction.old01 n
  have old12 : (1 : Fin M) + 1 = 2 := StraightDeletionConstruction.old12 n
  have old23 : (2 : Fin M) + 1 = 3 := StraightDeletionConstruction.old23 n
  have qedge0 : segment Real (r (sig 0)) (r (sig (0 + 1))) =
      segment Real (r 0) (r 2) := StraightDeletionConstruction.qedge0 n p i
  have qedgePos (k : Fin L) (hk : k.val ≠ 0) :
      segment Real (r (sig k)) (r (sig (k + 1))) =
        segment Real (r (sig k)) (r (sig k + 1)) := StraightDeletionConstruction.qedgePos n p i k hk
  let invrot : Fin M → Fin M := fun j =>
    if h : j.val < i.val then ⟨j.val + M - i.val, by omega⟩
    else ⟨j.val - i.val, by omega⟩
  have hinvrot (j : Fin M) : rot (invrot j) = j := StraightDeletionConstruction.hinvrot n i j
  have hinvrotRot (j : Fin M) : invrot (rot j) = j := StraightDeletionConstruction.hinvrotRot n i j
  let col : Fin M → Fin L := fun j =>
    ⟨if j.val ≤ 1 then 0 else j.val - 1, by split_ifs <;> omega⟩
  have colSurv (k : Fin L) : col (sig k) = k := StraightDeletionConstruction.colSurv n k
  have sigCol (h : Fin M) (hh : 2 ≤ h.val) : sig (col h) = h :=
      StraightDeletionConstruction.sigCol n h hh
  have colZero : col (0 : Fin M) = 0 := StraightDeletionConstruction.colZero n
  have colOne : col (1 : Fin M) = 0 := StraightDeletionConstruction.colOne n
  have colTwo : col (2 : Fin M) = 1 := StraightDeletionConstruction.colTwo n
  have colSucc (h : Fin M) (hh : 2 ≤ h.val) :
      col (h + 1) = col h + 1 := StraightDeletionConstruction.colSucc n h hh
  have invSucc (j : Fin M) : invrot (j + 1) = invrot j + 1 :=
      StraightDeletionConstruction.invSucc n i j
  have firstInt (c : Fin L) (hc : c.val ≠ 0) :
      segment Real (r (sig 0)) (r (sig (0 + 1))) ∩
          segment Real (r (sig c)) (r (sig (c + 1))) =
        {x | (x = r (sig 0) ∨ x = r (sig (0 + 1))) ∧
          (x = r (sig c) ∨ x = r (sig (c + 1)))} := StraightDeletionConstruction.firstInt n p i
              hunion c hc
  let q : P3381T1PolygonBoundary n := StraightDeletionConstruction.q n p i hunion
  change r 1 = (1 - t) • r 0 + t • r 2 at hsplice
  change segment Real (r 0) (r 1) ∪ segment Real (r 1) (r 2) =
    segment Real (r 0) (r 2) at hunion
  have qvertex (k : Fin L) : q.vertex k = r (sig k) := by rfl
  let start : Fin L → Fin M := fun k => rot (sig k)
  let edge : Fin M → Fin L := fun j => col (invrot j)
  let parameter : Fin M → Real := fun j => if invrot j = 1 then t else 0
  have hstart : Function.Injective start := by
    intro a b hab
    exact hsig (hrot hab)
  have hsigne1 (k : Fin L) : sig k ≠ 1 := by
    intro he
    have hv := congrArg Fin.val he
    have hk := k.isLt
    have hv1 : (1 : Fin M).val = 1 := by simp [Nat.mod_eq_of_lt hM1]
    rw [hv1] at hv
    simp only [sig] at hv
    split_ifs at hv; omega
  refine ⟨start, hstart, edge, parameter, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : invrot j = 1 <;> simp [parameter, hj, ht0.le]
  · intro j
    by_cases hj : invrot j = 1 <;> simp [parameter, hj, ht1]
  · intro k
    change col (invrot (rot (sig k))) = k
    rw [hinvrotRot, colSurv]
  · intro k
    change (if invrot (rot (sig k)) = 1 then t else 0) = 0
    rw [hinvrotRot]
    simp [hsigne1]
  · intro j
    let h := invrot j
    have hj : rot h = j := hinvrot j
    have hpj : p.vertex j = r h := by
      simpa [r] using congrArg p.vertex hj.symm
    change p.vertex j =
      (1 - parameter j) • q.vertex (col h) +
        parameter j • q.vertex (col h + 1)
    by_cases hzero : h.val = 0
    · have heq : h = 0 := Fin.ext hzero
      have hzero' : invrot j = 0 := by simpa [h] using heq
      rw [hpj]
      simp [parameter, hzero', colZero, qvertex, sig0, heq]
    · by_cases hone : h.val = 1
      · have heq : h = 1 := Fin.ext hone
        have hone' : invrot j = 1 := by simpa [h] using heq
        rw [hpj, heq, hsplice]
        simp [parameter, hone', colOne, qvertex, sig0, sig1]
      · have hlarge : 2 ≤ h.val := by omega
        have hnotone : h ≠ 1 := by
          intro he
          apply hone
          exact congrArg Fin.val he
        have hnotone' : invrot j ≠ 1 := by simpa [h] using hnotone
        rw [hpj]
        have hcoll := sigCol h hlarge
        simp [parameter, hnotone', qvertex, hcoll]
  · intro j
    let h := invrot j
    have hj : rot h = j := hinvrot j
    have hnext : invrot (j + 1) = h + 1 := by
      dsimp [h]
      exact invSucc j
    by_cases hzero : h.val = 0
    · have heq : h = 0 := Fin.ext hzero
      have hzero' : invrot j = 0 := by simpa [h] using heq
      have hnextval : h + 1 = 1 := by simp [heq]
      have hparam0 : parameter j = 0 := by simp [parameter, hzero']
      have hnextparam : parameter (j + 1) = t := by
        simp [parameter, hnext, hnextval]
      left
      constructor
      · change col (invrot (j + 1)) = col (invrot j)
        rw [hnext, heq, hzero']
        simp [old01, colOne, colZero]
      · rw [hparam0, hnextparam]
        exact ht0
    · by_cases hone : h.val = 1
      · have heq : h = 1 := Fin.ext hone
        have hone' : invrot j = 1 := by simpa [h] using heq
        have hnextval : h + 1 = 2 := by simpa [heq] using old12
        have hparamj : parameter j = t := by simp [parameter, hone']
        have hnextne : h + 1 ≠ 1 := by
          intro he
          have h21 : (2 : Fin M) = 1 := hnextval.symm.trans he
          have hv := congrArg Fin.val h21
          norm_num [hmod1M, hmod2M] at hv
        have hnextparam : parameter (j + 1) = 0 := by
          simp [parameter, hnext, hnextne]
        right
        constructor
        · change col (invrot (j + 1)) = col (invrot j) + 1
          rw [hnext, heq, hone']
          simp [old12, colTwo, colOne, new01]
        · exact hnextparam
      · have hlarge : 2 ≤ h.val := by omega
        have hnotone' : invrot j ≠ 1 := by
          intro he
          apply hone
          exact congrArg Fin.val (by simpa [h] using he)
        have hnextne : h + 1 ≠ 1 := by
          intro he
          have hv := congrArg Fin.val he
          have hv1 : (1 : Fin M).val = 1 := by
            simp [Nat.mod_eq_of_lt hM1]
          rw [hv1] at hv
          simp only [Fin.val_add_eq_ite] at hv
          split_ifs at hv <;> omega
        have hparamj : parameter j = 0 := by simp [parameter, hnotone']
        have hnextparam : parameter (j + 1) = 0 := by
          simp [parameter, hnext, hnextne]
        right
        constructor
        · change col (invrot (j + 1)) = col (invrot j) + 1
          rw [hnext]
          exact colSucc h hlarge
        · exact hnextparam
  · apply Set.ext
    intro x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨j, hx⟩
      let h := invrot j
      have hj : rot h = j := hinvrot j
      have hseg : segment Real (p.vertex j) (p.vertex (j + 1)) =
          segment Real (r h) (r (h + 1)) := by
        rw [← hj, ← hrotSucc]
      rw [hseg] at hx
      by_cases hz : h.val = 0
      · have hh : h = 0 := Fin.ext hz
        have hhseg : segment Real (r h) (r (h + 1)) =
            segment Real (r 0) (r (0 + 1)) := by simp [hh]
        rw [hhseg] at hx
        apply Set.mem_iUnion.mpr
        refine ⟨0, ?_⟩
        change x ∈ segment Real (r (sig 0)) (r (sig (0 + 1)))
        rw [qedge0, ← hunion]
        simpa [hh] using Or.inl hx
      · by_cases hone : h.val = 1
        · have hh : h = 1 := Fin.ext hone
          have hhseg : segment Real (r h) (r (h + 1)) =
              segment Real (r 1) (r (1 + 1)) := by simp [hh]
          rw [hhseg] at hx
          apply Set.mem_iUnion.mpr
          refine ⟨0, ?_⟩
          change x ∈ segment Real (r (sig 0)) (r (sig (0 + 1)))
          rw [qedge0, ← hunion]
          simpa [hh, old12] using Or.inr hx
        · have hlarge : 2 ≤ h.val := by omega
          let k := col h
          have hk : sig k = h := sigCol h hlarge
          have hk0 : k ≠ 0 := by
            intro he
            have hs0 : sig k = 0 := by simpa [he] using sig0
            have htmp := congrArg Fin.val (hk.symm.trans hs0)
            have hzero : h.val = 0 := by simpa using htmp
            omega
          apply Set.mem_iUnion.mpr
          refine ⟨k, ?_⟩
          change x ∈ segment Real (r (sig k)) (r (sig (k + 1)))
          have hk0val : k.val ≠ 0 := by
            intro hv
            apply hk0
            exact Fin.ext hv
          rw [qedgePos k hk0val, hk]
          exact hx
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨k, hx⟩
      by_cases hk0 : k.val = 0
      · have hk : k = 0 := Fin.ext hk0
        subst k
        change x ∈ segment Real (r (sig 0)) (r (sig (0 + 1))) at hx
        rw [qedge0, ← hunion] at hx
        rcases hx with hx | hx
        · apply Set.mem_iUnion.mpr
          refine ⟨rot 0, ?_⟩
          have hseg : segment Real (p.vertex (rot 0)) (p.vertex (rot 0 + 1)) =
              segment Real (r 0) (r (0 + 1)) := by
            rw [← hrotSucc 0]
          rw [hseg]
          exact hx
        · apply Set.mem_iUnion.mpr
          refine ⟨rot 1, ?_⟩
          have hseg : segment Real (p.vertex (rot 1)) (p.vertex (rot 1 + 1)) =
              segment Real (r 1) (r (1 + 1)) := by
            rw [← hrotSucc 1]
          rw [hseg]
          exact hx
      · have hlarge : 2 ≤ (sig k).val := by
          have hkpos : k.val > 0 := Nat.pos_of_ne_zero hk0
          have hkpos' : k.val ≠ 0 := by omega
          simp only [sig, ite_eq_right hkpos']
          omega
        have hk : sig (col (sig k)) = sig k := sigCol (sig k) hlarge
        apply Set.mem_iUnion.mpr
        refine ⟨rot (sig k), ?_⟩
        have hseg : segment Real (p.vertex (rot (sig k)))
            (p.vertex (rot (sig k) + 1)) =
            segment Real (r (sig k)) (r (sig k + 1)) := by
          rw [← hrotSucc (sig k)]
        rw [hseg]
        change x ∈ segment Real (r (sig k)) (r (sig (k + 1))) at hx
        rw [qedgePos k hk0] at hx
        exact hx


end StraightDeletionConstruction

theorem P3497T1SingleStraightDeletion {n : Nat}
    (p : P3381T1PolygonBoundary (n + 1))
    (i : Fin ((n + 1) + 3))
    (hdet : P3381T1TriangleDeterminant (fun j : Fin 3 =>
      p.vertex (i + ⟨j.val, Nat.lt_of_lt_of_le j.isLt
        (Nat.le_add_left 3 (n + 1))⟩)) = 0) :
    ∃ q : P3381T1PolygonBoundary n,
      (∀ k : Fin (n + 3), q.vertex k =
        p.vertex (i + ⟨if k.val = 0 then 0 else k.val + 1, by
          split_ifs <;> omega⟩)) ∧
      Nonempty (P3475T1BoundarySubdivision q p) := by
  classical
  let r := StraightDeletionConstruction.r n p i
  obtain ⟨t, ht0, ht1, hsplice, hunion⟩ :=
    P3497T1StrictCornerSplice (r 0) (r 1) (r 2)
      (StraightDeletionConstruction.hac n p i) (StraightDeletionConstruction.ha n p i)
      (StraightDeletionConstruction.hbc n p i) (StraightDeletionConstruction.hdet' n p i hdet)
      (StraightDeletionConstruction.hint n p i)
  refine ⟨StraightDeletionConstruction.q n p i hunion, ?_,
    ⟨StraightDeletionConstruction.boundarySubdivision p i hdet t ht0 ht1 hsplice hunion⟩⟩
  intro k
  rfl

end ApollonianSuperharmonic

end
