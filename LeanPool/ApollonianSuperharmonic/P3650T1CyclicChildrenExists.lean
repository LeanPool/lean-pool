/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3650T1CyclicChildren

-- [TABLET NODE: P3650T1CyclicChildrenExists]

/-!
# P3650T1CyclicChildrenExists

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace CyclicChildrenConstruction

private noncomputable abbrev N (n : Nat) := n + 3

private theorem hN (n : Nat) : 3 ≤ (N n) := by
  classical
  let N := n + 3
  dsimp only [CyclicChildrenConstruction.N] at *
  change (3 ≤ N)
  dsimp [N]; omega

private theorem hNpos (n : Nat) : 0 < (N n) := by
  classical
  let N := n + 3
  have hN : 3 ≤ N := hN n
  dsimp only [CyclicChildrenConstruction.N] at *
  change (0 < N)
  omega

private noncomputable abbrev rot (n : Nat) (a : Fin (n + 3)) : Fin (N n) → Fin (N n) := by
  classical
  let N := n + 3
  dsimp only [CyclicChildrenConstruction.N] at *
  change (Fin N → Fin N)
  exact fun i => a + i

private theorem hrot_inj (n : Nat) (a : Fin (n + 3)) : Function.Injective (rot n a) := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  change (Function.Injective rot)
  intro i j hij
  apply Fin.ext
  have hv := congrArg Fin.val hij
  simp only [rot, Fin.val_add_eq_ite] at hv
  by_cases hi : N ≤ a.val + i.val <;>
    by_cases hj : N ≤ a.val + j.val <;> simp_all [N] <;> omega

private noncomputable abbrev k (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) : Nat := by
  classical
  let N := n + 3
  exact (b.val + N - a.val) % N

private theorem hklt (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) : (k n a b) < (N n) := by
  classical
  let N := n + 3
  have hNpos : 0 < N := hNpos n
  let k : Nat := (b.val + N - a.val) % N
  dsimp only [CyclicChildrenConstruction.N, CyclicChildrenConstruction.k] at *
  change (k < N)
  dsimp [k]; exact Nat.mod_lt _ hNpos

private theorem hrotzero (n : Nat) (a : Fin (n + 3)) : (rot n a) (0 : Fin (N n)) = a := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  dsimp only [CyclicChildrenConstruction.N] at *
  change (rot (0 : Fin N) = a)
  apply Fin.ext
  simp [rot, N]

private theorem hkv (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) : (k n a b) = if a.val ≤ b.val
    then b.val - a.val else b.val + (N n) - a.val := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hrotzero : rot (0 : Fin N) = a := hrotzero n a
  dsimp only [CyclicChildrenConstruction.N, CyclicChildrenConstruction.k] at *
  change (k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val)
  dsimp [k]
  split_ifs with habv
  · have hsub : b.val + N - a.val = N + (b.val - a.val) := by omega
    rw [hsub, Nat.add_mod]
    simp only [Nat.mod_self, zero_add]
    simp [Nat.mod_eq_of_lt (show b.val - a.val < N by omega)]
  · have hsub : b.val + N - a.val = b.val + (N - a.val) := by omega
    rw [hsub]
    exact Nat.mod_eq_of_lt (show b.val + (N - a.val) < N by omega)

private theorem hrotk (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) : (rot n a) ⟨(k n a b), (hklt
    n a b)⟩ = b := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hrotzero : rot (0 : Fin N) = a := hrotzero n a
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  dsimp only [CyclicChildrenConstruction.k] at *
  change (rot ⟨k, hklt⟩ = b)
  apply Fin.ext
  simp only [rot, Fin.val_add_eq_ite]
  rw [hkv]
  split_ifs <;> omega

private theorem hkpos (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) : 0 < (k n a b)
    := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  have hrot_inj : Function.Injective rot := hrot_inj n a
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hrotzero : rot (0 : Fin N) = a := hrotzero n a
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hrotk : rot ⟨k, hklt⟩ = b := hrotk n a b
  dsimp only [CyclicChildrenConstruction.k] at *
  change (0 < k)
  by_contra h
  have hkz : k = 0 := by omega
  have : (⟨k, hklt⟩ : Fin N) = 0 := by apply Fin.ext; simp [hkz]
  have heq := hrot_inj (show rot ⟨k, hklt⟩ = rot 0 by rw [this])
  have : a = b := by rw [← hrotzero, ← hrotk, heq]
  exact hab this

private theorem hkne1 (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hnext : b ≠ a + 1) : (k n a
    b) ≠ 1 := by
  classical
  let N := n + 3
  have hN : 3 ≤ N := hN n
  let rot : Fin N → Fin N := fun i => a + i
  have hrot_inj : Function.Injective rot := hrot_inj n a
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hrotk : rot ⟨k, hklt⟩ = b := hrotk n a b
  dsimp only [CyclicChildrenConstruction.k] at *
  change (k ≠ 1)
  intro he
  have hidx : (⟨k, hklt⟩ : Fin N) = 1 := by
    apply Fin.ext
    simp [he, Nat.mod_eq_of_lt (show 1 < N by omega)]
  have heq := hrot_inj (show rot ⟨k, hklt⟩ = rot 1 by rw [hidx])
  apply hnext
  calc
    b = rot 1 := hrotk.symm.trans (congrArg rot hidx)
    _ = a + 1 := rfl

private theorem hkle (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hprev : a ≠ b + 1) : (k n a
    b) + 2 ≤ (N n) := by
  classical
  let N := n + 3
  have hN : 3 ≤ N := hN n
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hrotzero : rot (0 : Fin N) = a := hrotzero n a
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hrotk : rot ⟨k, hklt⟩ = b := hrotk n a b
  dsimp only [CyclicChildrenConstruction.N, CyclicChildrenConstruction.k] at *
  change (k + 2 ≤ N)
  by_contra h
  have hbad : k = N - 1 := by omega
  let last : Fin N := ⟨N - 1, by omega⟩
  have hrlast : (rot last).val = if a.val = 0 then N - 1 else a.val - 1 := by
    by_cases ha0 : a.val = 0
    · simp [rot, last, Fin.val_add_eq_ite, ha0,
        ]
      omega
    · have hap : 0 < a.val := by omega
      simp only [rot, last, Fin.val_add_eq_ite]
      split_ifs <;> omega
  have hlast : (rot last) + 1 = a := by
    apply Fin.ext
    rw [Fin.val_add_eq_ite, hrlast]
    by_cases ha0 : a.val = 0
    · rw [ite_eq_left ha0]
      have hNm1 : N - 1 + 1 = N := by omega
      have hone : 1 % N = 1 := Nat.mod_eq_of_lt (by omega : 1 < N)
      simp [hNm1, hone, ha0]
    · rw [ite_eq_right ha0]
      have hsum : a.val - 1 + 1 = a.val := by omega
      have hone : 1 % N = 1 := Nat.mod_eq_of_lt (by omega : 1 < N)
      simp [hsum, hone]
      omega
  have hidx : (⟨k, hklt⟩ : Fin N) = last := by apply Fin.ext; simp [last, hbad]
  have hb : b = rot last := hrotk.symm.trans (congrArg rot hidx)
  have heq : a = b + 1 := by
    calc
      a = rot last + 1 := hlast.symm
      _ = b + 1 := (congrArg (fun x : Fin N => x + 1) hb).symm
  exact (hprev heq).elim

private theorem hk_bounds (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext : b
    ≠ a + 1) (hprev : a ≠ b + 1) : 2 ≤ (k n a b) ∧ (k n a b) ≤ (N n) - 2 := by
  classical
  let N := n + 3
  have hN : 3 ≤ N := hN n
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkpos : 0 < k := hkpos n a b hab
  have hkne1 : k ≠ 1 := hkne1 n a b hnext
  have hkle : k + 2 ≤ N := hkle n a b hprev
  dsimp only [CyclicChildrenConstruction.N, CyclicChildrenConstruction.k] at *
  change (2 ≤ k ∧ k ≤ N - 2)
  omega

private theorem hrot_val (n : Nat) (a : Fin (n + 3)) (i : Fin (N n)) : ((rot n
    a) i).val = (a.val + i.val) % (N n) := by
  rfl

private noncomputable abbrev root (n : Nat) : List (Fin (N n)) := by
  classical
  let N := n + 3
  dsimp only [CyclicChildrenConstruction.N] at *
  change (List (Fin N))
  exact List.ofFn (fun i : Fin N => i)

private theorem hrootlen (n : Nat) : (root n).length = (N n) := by
  classical
  let N := n + 3
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  dsimp only [CyclicChildrenConstruction.N] at *
  change (root.length = N)
  simp [root, N]

private theorem hrot_list (n : Nat) (a : Fin (n + 3)) : (root n).rotate a.val =
    List.ofFn (rot n a) := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  have hrot_val (i : Fin N) : (rot i).val = (a.val + i.val) % N := hrot_val n a i
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  change (root.rotate a.val = List.ofFn rot)
  apply List.ext_getElem
  · simp [root]
  · intro j hj₁ hj₂
    rw [List.getElem_rotate]
    simp only [root, List.getElem_ofFn, List.length_ofFn]
    apply Fin.ext
    rw [hrot_val, Nat.add_comm j a.val]

private noncomputable abbrev l (n : Nat) (a : Fin (n + 3)) : List (Fin (N n)) := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  dsimp only [CyclicChildrenConstruction.N] at *
  change (List (Fin N))
  exact List.ofFn rot

private noncomputable abbrev u (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) : List (Fin (N n))
    := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  let l : List (Fin N) := List.ofFn rot
  dsimp only [CyclicChildrenConstruction.N] at *
  change (List (Fin N))
  exact (l.drop 1).take (k - 1)

private noncomputable abbrev v (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) : List (Fin (N n))
    := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  let l : List (Fin N) := List.ofFn rot
  dsimp only [CyclicChildrenConstruction.N] at *
  change (List (Fin N))
  exact l.drop (k + 1)

private theorem hlu (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hprev : a ≠ b + 1) : (u n a
    b).length = (k n a b) - 1 := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let l : List (Fin N) := List.ofFn rot
  let u : List (Fin N) := (l.drop 1).take (k - 1)
  dsimp only [CyclicChildrenConstruction.k] at *
  change (u.length = k - 1)
  simp [u, l, List.length_take]
  omega

private theorem hlv (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hprev : a ≠ b + 1) : (v n a
    b).length = (N n) - ((k n a b) + 1) := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let l : List (Fin N) := List.ofFn rot
  let v : List (Fin N) := l.drop (k + 1)
  dsimp only [CyclicChildrenConstruction.N, CyclicChildrenConstruction.k] at *
  change (v.length = N - (k + 1))
  simp [v, l, List.length_drop]
  omega

private theorem hget_l (n : Nat) (a : Fin (n + 3)) (j : Nat) (hj : j < (N n)) :
      (l n a)[j]'(by simpa only [l, id_eq, List.length_ofFn] using hj) = (rot n a) ⟨j, hj⟩ := by
  change (List.ofFn (rot n a))[j]'(by simpa only [List.length_ofFn] using hj) = _
  rw [List.getElem_ofFn]

private theorem hparent_order (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext
    : b ≠ a + 1) (hprev : a ≠ b + 1) : (root n).rotate a.val = a :: ((u n a b) ++ b :: (v n a b))
    := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hrotzero : rot (0 : Fin N) = a := hrotzero n a
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hrotk : rot ⟨k, hklt⟩ = b := hrotk n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  have hk_bounds : 2 ≤ k ∧ k ≤ N - 2 := hk_bounds n a b hab hnext hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  have hrot_list : root.rotate a.val = List.ofFn rot := hrot_list n a
  let l : List (Fin N) := List.ofFn rot
  let u : List (Fin N) := (l.drop 1).take (k - 1)
  let v : List (Fin N) := l.drop (k + 1)
  have hlu : u.length = k - 1 := hlu n a b hprev
  have hlv : v.length = N - (k + 1) := hlv n a b hprev
  have hget_l (j : Nat) (hj : j < N) :
      l[j]'(by simp [l]; omega) = rot ⟨j, hj⟩ := hget_l n a j hj
  change (root.rotate a.val = a :: (u ++ b :: v))
  rw [hrot_list]
  apply List.ext_getElem
  · simp only [List.length_ofFn]
    simp only [List.length_cons, List.length_append]
    rw [hlu, hlv]
    omega
  · intro j hj₁ hj₂
    cases j with
    | zero => simp [hrotzero]
    | succ j =>
      by_cases hjk : j + 1 = k
      · have hju : j = u.length := by rw [hlu]; omega
        subst j
        simp only [List.getElem_cons_succ]
        rw [List.getElem_append_right (as := u) (bs := b :: v) (by omega)]
        simp only [Nat.sub_self]
        simp only [List.getElem_cons_zero]
        have hpos : u.length + 1 = k := by rw [hlu]; omega
        have hget := hget_l k hklt
        have hh : l[k] = b := hget.trans hrotk
        simpa only [l, hpos] using hh
      · by_cases hju : j < u.length
        · simp only [List.getElem_cons_succ]
          rw [List.getElem_append_left hju]
          simp only [u, List.getElem_take, List.getElem_drop]
          simp [l, Nat.add_comm]
        · have hjtail : u.length < j := by rw [hlu]; omega
          simp only [List.getElem_cons_succ]
          have hj' : j < (u ++ b :: v).length := by simpa using hj₂
          rw [List.getElem_append_right (as := u) (bs := b :: v)
            hjtail.le (h₂ := hj')]
          let t := j - u.length - 1
          have hsub : j - u.length = t + 1 := by dsimp [t]; omega
          simp only [hsub, List.getElem_cons_succ]
          simp only [v, List.getElem_drop]
          rw [List.getElem_ofFn]
          have hjN : j + 1 < N := by
            dsimp [N]
            simp only [List.length_ofFn] at hj₁
            omega
          have hbnd : k + 1 + (j - u.length - 1) < N := by
            rw [hlu]
            omega
          have hidx := hget_l (k + 1 + (j - u.length - 1)) hbnd
          rw [hidx]
          apply congrArg rot
          apply Fin.ext
          simp only []
          rw [hlu]
          omega

private noncomputable abbrev leftN (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) := (k n a b) - 2

private noncomputable abbrev rightN (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) := (N n) - (k n
    a b) - 2

private theorem hleftLen (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠
    a + 1) (hprev : a ≠ b + 1) : (leftN n a b) + 3 = (k n a b) + 1 := by
  classical
  let N := n + 3
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hk_bounds : 2 ≤ k ∧ k ≤ N - 2 := hk_bounds n a b hab hnext hprev
  let leftN := k - 2
  dsimp only [CyclicChildrenConstruction.k, CyclicChildrenConstruction.leftN] at *
  change (leftN + 3 = k + 1)
  dsimp [leftN]; omega

private theorem hrightLen (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext : b
    ≠ a + 1) (hprev : a ≠ b + 1) : (rightN n a b) + 3 = (N n) - (k n a b) + 1 := by
  classical
  let N := n + 3
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  let rightN := N - k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  dsimp only [CyclicChildrenConstruction.N, CyclicChildrenConstruction.k,
      CyclicChildrenConstruction.rightN] at *
  change (rightN + 3 = N - k + 1)
  dsimp [rightN]; omega

private theorem hleftLt (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠
    a + 1) (hprev : a ≠ b + 1) : (leftN n a b) < n := by
  classical
  let N := n + 3
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  dsimp only [CyclicChildrenConstruction.leftN] at *
  change (leftN < n)
  dsimp [leftN, N]; omega

private theorem hrightLt (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠
    a + 1) (hprev : a ≠ b + 1) : (rightN n a b) < n := by
  classical
  let N := n + 3
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  have hk_bounds : 2 ≤ k ∧ k ≤ N - 2 := hk_bounds n a b hab hnext hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  let rightN := N - k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  dsimp only [CyclicChildrenConstruction.rightN] at *
  change (rightN < n)
  dsimp [rightN, N]; omega

private noncomputable abbrev il (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b)
    (hnext : b ≠ a + 1) (hprev : a ≠ b + 1) : Fin ((leftN n a b) + 3) → Fin (N n) := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  dsimp only [CyclicChildrenConstruction.N, CyclicChildrenConstruction.leftN] at *
  change (Fin (leftN + 3) → Fin N)
  exact fun i => rot ⟨i.val, by rw [hleftLen] at i; omega⟩

private noncomputable abbrev posR (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) : Fin ((rightN n
    a b) + 3) → Nat := by
  classical
  let N := n + 3
  let k : Nat := (b.val + N - a.val) % N
  let rightN := N - k - 2
  dsimp only [CyclicChildrenConstruction.rightN] at *
  change (Fin (rightN + 3) → Nat)
  exact fun i =>
    if i.val = N - k then 0 else k + i.val

private theorem hposRlt (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠
    a + 1) (hprev : a ≠ b + 1) (i : Fin ((rightN n a b) + 3)) : (posR n a b) i < (N n) := by
  classical
  let N := n + 3
  have hNpos : 0 < N := hNpos n
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  let rightN := N - k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  have hrightLen : rightN + 3 = N - k + 1 := hrightLen n a b hab hnext hprev
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  dsimp only [CyclicChildrenConstruction.N, CyclicChildrenConstruction.rightN] at *
  change (posR i < N)
  have hi : i.val < N - k + 1 := by rw [← hrightLen]; exact i.isLt
  dsimp [posR]
  split_ifs <;> omega

private noncomputable abbrev ir (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b)
    (hnext : b ≠ a + 1) (hprev : a ≠ b + 1) : Fin ((rightN n a b) + 3) → Fin (N n) := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  let rightN := N - k - 2
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  have hposRlt (i : Fin (rightN + 3)) : posR i < N := hposRlt n a b hab hnext hprev i
  dsimp only [CyclicChildrenConstruction.N, CyclicChildrenConstruction.rightN] at *
  change (Fin (rightN + 3) → Fin N)
  exact fun i => rot ⟨posR i, hposRlt i⟩

private theorem hleft_inj (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext : b
    ≠ a + 1) (hprev : a ≠ b + 1) : Function.Injective (il n a b hab hnext hprev) := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  have hrot_inj : Function.Injective rot := hrot_inj n a
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  let il : Fin (leftN + 3) → Fin N := fun i => rot ⟨i.val, by rw [hleftLen] at i; omega⟩
  change (Function.Injective il)
  intro i j hij
  have heq := hrot_inj hij
  apply Fin.ext
  have h := congrArg Fin.val heq
  dsimp [il] at h
  exact h

private theorem hright_inj (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext : b
    ≠ a + 1) (hprev : a ≠ b + 1) : Function.Injective (ir n a b hab hnext hprev) := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  have hrot_inj : Function.Injective rot := hrot_inj n a
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hk_bounds : 2 ≤ k ∧ k ≤ N - 2 := hk_bounds n a b hab hnext hprev
  let leftN := k - 2
  let rightN := N - k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  have hrightLen : rightN + 3 = N - k + 1 := hrightLen n a b hab hnext hprev
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  have hposRlt (i : Fin (rightN + 3)) : posR i < N := hposRlt n a b hab hnext hprev i
  let ir : Fin (rightN + 3) → Fin N := fun i => rot ⟨posR i, hposRlt i⟩
  change (Function.Injective ir)
  intro i j hij
  have heq := hrot_inj hij
  have hval : posR i = posR j := congrArg Fin.val heq
  apply Fin.ext
  have hi_lt : i.val < N - k + 1 := by
    calc i.val < rightN + 3 := i.isLt
      _ = N - k + 1 := hrightLen
  have hj_lt : j.val < N - k + 1 := by
    calc j.val < rightN + 3 := j.isLt
      _ = N - k + 1 := hrightLen
  have hi : i.val ≤ N - k := by omega
  have hj : j.val ≤ N - k := by omega
  dsimp [posR] at hval
  split_ifs at hval <;> omega

private theorem hleft_order (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext :
    b ≠ a + 1) (hprev : a ≠ b + 1) : List.ofFn (il n a b hab hnext hprev) = a :: ((u n a b) ++
    [b]) := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hrotzero : rot (0 : Fin N) = a := hrotzero n a
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hrotk : rot ⟨k, hklt⟩ = b := hrotk n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  have hk_bounds : 2 ≤ k ∧ k ≤ N - 2 := hk_bounds n a b hab hnext hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let l : List (Fin N) := List.ofFn rot
  let u : List (Fin N) := (l.drop 1).take (k - 1)
  have hlu : u.length = k - 1 := hlu n a b hprev
  have hget_l (j : Nat) (hj : j < N) :
      l[j]'(by simp [l]; omega) = rot ⟨j, hj⟩ := hget_l n a j hj
  let leftN := k - 2
  let rightN := N - k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  have hrightLen : rightN + 3 = N - k + 1 := hrightLen n a b hab hnext hprev
  have hrightLt : rightN < n := hrightLt n a b hab hnext hprev
  let il : Fin (leftN + 3) → Fin N := fun i => rot ⟨i.val, by rw [hleftLen] at i; omega⟩
  change (List.ofFn il = a :: (u ++ [b]))
  apply List.ext_getElem
  · simp only [List.length_ofFn]
    rw [hleftLen]
    simp [hlu]
    omega
  · intro j hj₁ hj₂
    cases j with
    | zero =>
      simp [il, hrotzero]
    | succ j =>
      by_cases hjk : j + 1 = k
      · have hlast : j = u.length := by rw [hlu]; omega
        have hpos : j + 1 = k := hjk
        simp only [List.getElem_cons_succ]
        rw [List.getElem_append_right (as := u) (bs := [b]) (by omega)]
        simp only [hlast, Nat.sub_self, List.getElem_cons_zero]
        have hkbound : k < leftN + 3 := by rw [hleftLen]; omega
        have hget := List.getElem_ofFn (f := il) (i := k)
          (by simpa only [List.length_ofFn] using hkbound)
        have hilk : il ⟨k, hkbound⟩ = b := by
          change rot ⟨k, hklt⟩ = b
          exact hrotk
        have hpos2 : u.length + 1 = k := by rw [← hlast]; exact hjk
        simpa only [hpos2] using hget.trans hilk
      · have hjlt : j + 1 < k := by simp only [List.length_ofFn, hleftLen] at hj₁; omega
        have hju : j < u.length := by rw [hlu]; omega
        simp only [List.getElem_cons_succ]
        rw [List.getElem_append_left hju]
        have hleftElem : (List.ofFn il)[j + 1]'(by simpa only [List.length_ofFn] using hj₁) =
            rot ⟨j + 1, by omega⟩ := by
          rw [List.getElem_ofFn]
        have hrightElem : u[j]'hju = rot ⟨j + 1, by omega⟩ := by
          change ((l.drop 1).take (k - 1))[j] = _
          simp only [List.getElem_take, List.getElem_drop]
          have hg := hget_l (j + 1) (by omega)
          simpa [Nat.add_comm] using hg
        exact hleftElem.trans hrightElem.symm

private theorem hright_order (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext :
    b ≠ a + 1) (hprev : a ≠ b + 1) : List.ofFn (ir n a b hab hnext hprev) = b :: ((v n a b) ++
    [a]) := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hrotzero : rot (0 : Fin N) = a := hrotzero n a
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hrotk : rot ⟨k, hklt⟩ = b := hrotk n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  have hk_bounds : 2 ≤ k ∧ k ≤ N - 2 := hk_bounds n a b hab hnext hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let l : List (Fin N) := List.ofFn rot
  let v : List (Fin N) := l.drop (k + 1)
  have hlv : v.length = N - (k + 1) := hlv n a b hprev
  have hget_l (j : Nat) (hj : j < N) :
      l[j]'(by simp [l]; omega) = rot ⟨j, hj⟩ := hget_l n a j hj
  let leftN := k - 2
  let rightN := N - k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  have hrightLen : rightN + 3 = N - k + 1 := hrightLen n a b hab hnext hprev
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  have hposRlt (i : Fin (rightN + 3)) : posR i < N := hposRlt n a b hab hnext hprev i
  let ir : Fin (rightN + 3) → Fin N := fun i => rot ⟨posR i, hposRlt i⟩
  change (List.ofFn ir = b :: (v ++ [a]))
  apply List.ext_getElem
  · simp only [List.length_ofFn]
    rw [hrightLen]
    simp [hlv]
    omega
  · intro j hj₁ hj₂
    cases j with
    | zero =>
      have hz : ¬ (0 : Nat) = N - k := by omega
      simp [ir, posR, hz, hrotk]
    | succ j =>
      by_cases hjend : j + 1 = N - k
      · have hlast : j = v.length := by rw [hlv]; omega
        simp only [List.getElem_cons_succ]
        rw [List.getElem_append_right (as := v) (bs := [a]) (by omega)]
        simp only [hlast, Nat.sub_self, List.getElem_cons_zero]
        have hpos : v.length + 1 = N - k := by rw [hlv]; omega
        have hbound : N - k < rightN + 3 := by rw [hrightLen]; omega
        have hget := List.getElem_ofFn (f := ir) (i := N - k)
          (by simpa only [List.length_ofFn] using hbound)
        have hirlast : ir ⟨N - k, hbound⟩ = a := by
          change rot ⟨posR ⟨N - k, hbound⟩, hposRlt _⟩ = a
          simp? [posR]
          exact hrotzero
        simpa only [hpos] using hget.trans hirlast
      · have hjlt : j + 1 < N - k := by
          simp only [List.length_ofFn, hrightLen] at hj₁
          omega
        have hjv : j < v.length := by rw [hlv]; omega
        simp only [List.getElem_cons_succ]
        rw [List.getElem_append_left hjv]
        have hleftElem : (List.ofFn ir)[j + 1] =
            rot ⟨k + (j + 1), by omega⟩ := by
          rw [List.getElem_ofFn]
          simp [ir, posR, Nat.ne_of_lt hjlt]
        have hrightElem : v[j]'hjv = rot ⟨k + (j + 1), by omega⟩ := by
          change (l.drop (k + 1))[j] = _
          rw [List.getElem_drop]
          have hg := hget_l (k + 1 + j) (by omega)
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hg
        exact hleftElem.trans hrightElem.symm

private theorem hAil (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠ a +
    1) (hprev : a ≠ b + 1) : (il n a b hab hnext hprev) 0 = a := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hrotzero : rot (0 : Fin N) = a := hrotzero n a
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  let il : Fin (leftN + 3) → Fin N := fun i => rot ⟨i.val, by rw [hleftLen] at i; omega⟩
  change (il 0 = a)
  simp [il, hrotzero]

private theorem hik (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠ a +
    1) (hprev : a ≠ b + 1) : (k n a b) < (leftN n a b) + 3 := by
  classical
  let N := n + 3
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  dsimp only [CyclicChildrenConstruction.k, CyclicChildrenConstruction.leftN] at *
  change (k < leftN + 3)
  rw [hleftLen]; omega

private noncomputable abbrev ik (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b)
    (hnext : b ≠ a + 1) (hprev : a ≠ b + 1) : Fin ((leftN n a b) + 3) := by
  classical
  let N := n + 3
  let k : Nat := (b.val + N - a.val) % N
  let leftN := k - 2
  have hik : k < leftN + 3 := hik n a b hab hnext hprev
  dsimp only [CyclicChildrenConstruction.leftN] at *
  change (Fin (leftN + 3))
  exact ⟨k, hik⟩

private theorem hBil (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠ a +
    1) (hprev : a ≠ b + 1) : (il n a b hab hnext hprev) (ik n a b hab hnext hprev) = b := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hrotk : rot ⟨k, hklt⟩ = b := hrotk n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  let il : Fin (leftN + 3) → Fin N := fun i => rot ⟨i.val, by rw [hleftLen] at i; omega⟩
  have hik : k < leftN + 3 := hik n a b hab hnext hprev
  let ik : Fin (leftN + 3) := ⟨k, hik⟩
  change (il ik = b)
  change rot ⟨k, hklt⟩ = b
  exact hrotk

private theorem hBir (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠ a +
    1) (hprev : a ≠ b + 1) : (ir n a b hab hnext hprev) 0 = b := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hrotk : rot ⟨k, hklt⟩ = b := hrotk n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  let rightN := N - k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  have hrightLen : rightN + 3 = N - k + 1 := hrightLen n a b hab hnext hprev
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  have hposRlt (i : Fin (rightN + 3)) : posR i < N := hposRlt n a b hab hnext hprev i
  let ir : Fin (rightN + 3) → Fin N := fun i => rot ⟨posR i, hposRlt i⟩
  have hik : k < leftN + 3 := hik n a b hab hnext hprev
  change (ir 0 = b)
  have hz : ¬ (0 : Nat) = N - k := by omega
  simp [ir, posR, hz, hrotk]

private theorem hlastRlt (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠
    a + 1) (hprev : a ≠ b + 1) : (N n) - (k n a b) < (rightN n a b) + 3 := by
  classical
  let N := n + 3
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  let rightN := N - k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  have hrightLen : rightN + 3 = N - k + 1 := hrightLen n a b hab hnext hprev
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  have hposRlt (i : Fin (rightN + 3)) : posR i < N := hposRlt n a b hab hnext hprev i
  have hik : k < leftN + 3 := hik n a b hab hnext hprev
  dsimp only [CyclicChildrenConstruction.N, CyclicChildrenConstruction.k,
      CyclicChildrenConstruction.rightN] at *
  change (N - k < rightN + 3)
  rw [hrightLen]; omega

private noncomputable abbrev lastR (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b)
    (hnext : b ≠ a + 1) (hprev : a ≠ b + 1) : Fin ((rightN n a b) + 3) := by
  classical
  let N := n + 3
  let k : Nat := (b.val + N - a.val) % N
  let rightN := N - k - 2
  have hlastRlt : N - k < rightN + 3 := hlastRlt n a b hab hnext hprev
  dsimp only [CyclicChildrenConstruction.rightN] at *
  change (Fin (rightN + 3))
  exact ⟨N - k, hlastRlt⟩

private theorem hAir (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠ a +
    1) (hprev : a ≠ b + 1) : (ir n a b hab hnext hprev) (lastR n a b hab hnext hprev) = a := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hrotzero : rot (0 : Fin N) = a := hrotzero n a
  let rightN := N - k - 2
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  have hposRlt (i : Fin (rightN + 3)) : posR i < N := hposRlt n a b hab hnext hprev i
  let ir : Fin (rightN + 3) → Fin N := fun i => rot ⟨posR i, hposRlt i⟩
  have hlastRlt : N - k < rightN + 3 := hlastRlt n a b hab hnext hprev
  let lastR : Fin (rightN + 3) := ⟨N - k, hlastRlt⟩
  change (ir lastR = a)
  change rot ⟨posR lastR, hposRlt lastR⟩ = a
  simp [lastR, posR, hrotzero]

private theorem hcommon (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠
    a + 1) (hprev : a ≠ b + 1) : Set.range (il n a b hab hnext hprev) ∩ Set.range (ir n a b hab
    hnext hprev) = {a, b} := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  have hrot_inj : Function.Injective rot := hrot_inj n a
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  let rightN := N - k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  have hrightLen : rightN + 3 = N - k + 1 := hrightLen n a b hab hnext hprev
  let il : Fin (leftN + 3) → Fin N := fun i => rot ⟨i.val, by rw [hleftLen] at i; omega⟩
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  have hposRlt (i : Fin (rightN + 3)) : posR i < N := hposRlt n a b hab hnext hprev i
  let ir : Fin (rightN + 3) → Fin N := fun i => rot ⟨posR i, hposRlt i⟩
  have hAil : il 0 = a := hAil n a b hab hnext hprev
  have hik : k < leftN + 3 := hik n a b hab hnext hprev
  let ik : Fin (leftN + 3) := ⟨k, hik⟩
  have hBil : il ik = b := hBil n a b hab hnext hprev
  have hBir : ir 0 = b := hBir n a b hab hnext hprev
  have hlastRlt : N - k < rightN + 3 := hlastRlt n a b hab hnext hprev
  let lastR : Fin (rightN + 3) := ⟨N - k, hlastRlt⟩
  have hAir : ir lastR = a := hAir n a b hab hnext hprev
  change (Set.range il ∩ Set.range ir = {a, b})
  apply Set.ext
  intro x
  constructor
  · intro hx
    rcases hx.1 with ⟨i, hxi⟩
    rcases hx.2 with ⟨j, hxj⟩
    have hEq : ir j = il i := hxj.trans hxi.symm
    have hiN : i.val < N := by
      have hi' : i.val < k + 1 := by simpa only [hleftLen] using i.isLt
      omega
    have hpos : (⟨i.val, hiN⟩ : Fin N) =
        ⟨posR j, hposRlt j⟩ := by
      apply hrot_inj
      simpa [il, ir] using hEq.symm
    have hv : i.val = posR j := congrArg Fin.val hpos
    have hi : i.val ≤ k := by
      have hbound : i.val < k + 1 := by simpa only [hleftLen] using i.isLt
      omega
    have hj : j.val ≤ N - k := by
      have hbound : j.val < N - k + 1 := by simpa only [hrightLen] using j.isLt
      omega
    by_cases hend : j.val = N - k
    · have hzero : posR j = 0 := by simp [posR, hend]
      have hizero : i.val = 0 := by omega
      have hi0 : i = 0 := Fin.ext hizero
      apply Or.inl
      calc
        x = il i := hxi.symm
        _ = il 0 := by rw [hi0]
        _ = a := hAil
    · have hposr : posR j = k + j.val := by simp [posR, hend]
      have hjeq : j.val = 0 := by omega
      have hival : i.val = k := by omega
      have hiK : i = ik := Fin.ext hival
      apply Or.inr
      calc
        x = il i := hxi.symm
        _ = il ik := by rw [hiK]
        _ = b := hBil
  · intro hx
    rcases hx with hxa | hxb
    · subst x
      exact ⟨⟨0, hAil⟩, ⟨lastR, hAir⟩⟩
    · subst x
      exact ⟨⟨ik, hBil⟩, ⟨0, hBir⟩⟩

private theorem hopen_old_disjoint (n : Nat) (p : P3381T1PolygonBoundary n) (a : Fin (n + 3))
    (b : Fin (n + 3)) (hclear : Disjoint (openSegment Real (p.vertex a) (p.vertex b))
    (P3544T1BoundaryCarrier p)) (x : Real × Real) (hx :
      x ∈ openSegment Real (p.vertex a) (p.vertex b)) (j : Fin (N n)) :
      x ∉ segment Real (p.vertex j) (p.vertex (j + 1)) := by
  classical
  let N := n + 3
  dsimp only [CyclicChildrenConstruction.N] at *
  intro hxj
  have hxC : x ∈ P3544T1BoundaryCarrier p := by
    simp? [P3544T1BoundaryCarrier]
    exact ⟨j, hxj⟩
  exact (Set.disjoint_left.mp hclear) hx hxC

private theorem hvertex_side (n : Nat) (p : P3381T1PolygonBoundary n) (e j : Fin (N n)) (hmem :
      p.vertex e ∈ segment Real (p.vertex j) (p.vertex (j + 1))) :
      e = j ∨ e = j + 1 := by
  classical
  let N := n + 3
  dsimp only [CyclicChildrenConstruction.N] at *
  by_cases heq : e = j
  · exact Or.inl heq
  · by_cases heq' : e = j + 1
    · exact Or.inr heq'
    · have hedge := p.edge_intersection e j heq
      have hpt : p.vertex e ∈ segment Real (p.vertex e) (p.vertex (e + 1)) :=
        left_mem_segment Real _ _
      have hpair : p.vertex e ∈
          segment Real (p.vertex e) (p.vertex (e + 1)) ∩
            segment Real (p.vertex j) (p.vertex (j + 1)) := ⟨hpt, hmem⟩
      rw [hedge] at hpair
      rcases hpair with ⟨_, hends⟩
      rcases hends with h | h
      · exact Or.inl (p.injective h)
      · exact Or.inr (p.injective h)

private theorem hchord_old (n : Nat) (p : P3381T1PolygonBoundary n) (a : Fin (n + 3)) (b : Fin
    (n + 3)) (hclear : Disjoint (openSegment Real (p.vertex a) (p.vertex b))
    (P3544T1BoundaryCarrier p)) (x : Real × Real) (j : Fin (N n)) :
      x ∈ segment Real (p.vertex a) (p.vertex b) ∩
        segment Real (p.vertex j) (p.vertex (j + 1)) ↔
      (x = p.vertex a ∨ x = p.vertex b) ∧
        (x = p.vertex j ∨ x = p.vertex (j + 1)) := by
  classical
  let N := n + 3
  have hopen_old_disjoint (x : Real × Real) (hx :
      x ∈ openSegment Real (p.vertex a) (p.vertex b)) (j : Fin N) :
      x ∉ segment Real (p.vertex j) (p.vertex (j + 1)) := hopen_old_disjoint n p a b hclear x hx j
  have hvertex_side (e j : Fin N) (hmem :
      p.vertex e ∈ segment Real (p.vertex j) (p.vertex (j + 1))) :
      e = j ∨ e = j + 1 := hvertex_side n p e j hmem
  dsimp only [CyclicChildrenConstruction.N] at *
  constructor
  · rintro ⟨hxchord, hxold⟩
    rw [← insert_endpoints_openSegment Real (p.vertex a) (p.vertex b)] at hxchord
    simp only [Set.mem_insert_iff] at hxchord
    rcases hxchord with hxa | hxb | hopen
    · subst x
      rcases hvertex_side a j hxold with h | h
      · exact ⟨Or.inl rfl, Or.inl (congrArg p.vertex h)⟩
      · exact ⟨Or.inl rfl, Or.inr (congrArg p.vertex h)⟩
    · subst x
      rcases hvertex_side b j hxold with h | h
      · exact ⟨Or.inr rfl, Or.inl (congrArg p.vertex h)⟩
      · exact ⟨Or.inr rfl, Or.inr (congrArg p.vertex h)⟩
    · exact False.elim ((hopen_old_disjoint x hopen j) hxold)
  · rintro ⟨hchord, hold⟩
    constructor
    · rcases hchord with hxa | hxb
      · rw [hxa]
        exact left_mem_segment Real _ _
      · rw [hxb]
        exact right_mem_segment Real _ _
    · rcases hold with hxj | hxj1
      · rw [hxj]
        exact left_mem_segment Real _ _
      · rw [hxj1]
        exact right_mem_segment Real _ _

private theorem hrot_succ (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext : b
    ≠ a + 1) (hprev : a ≠ b + 1) (i : Fin (N n)) : (rot n a) (i + 1) = (rot n a) i + 1 := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  let rightN := N - k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  have hposRlt (i : Fin (rightN + 3)) : posR i < N := hposRlt n a b hab hnext hprev i
  have hik : k < leftN + 3 := hik n a b hab hnext hprev
  have hlastRlt : N - k < rightN + 3 := hlastRlt n a b hab hnext hprev
  dsimp only [CyclicChildrenConstruction.N] at *
  change (rot (i + 1) = rot i + 1)
  apply Fin.ext
  change (a.val + (i.val + 1) % N) % N =
    ((a.val + i.val) % N + 1) % N
  calc
    (a.val + (i.val + 1) % N) % N =
        ((i.val + 1) % N + a.val) % N := by rw [Nat.add_comm]
    _ = (i.val + 1 + a.val) % N := Nat.mod_add_mod (i.val + 1) N a.val
    _ = (a.val + i.val + 1) % N := by congr 1; omega
    _ = ((a.val + i.val) % N + 1) % N :=
      (Nat.mod_add_mod (a.val + i.val) N 1).symm

private theorem hleftLen_gt (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext :
    b ≠ a + 1) (hprev : a ≠ b + 1) : 1 < (leftN n a b) + 3 := by
  classical
  let N := n + 3
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  have hk_bounds : 2 ≤ k ∧ k ≤ N - 2 := hk_bounds n a b hab hnext hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  let rightN := N - k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  have hposRlt (i : Fin (rightN + 3)) : posR i < N := hposRlt n a b hab hnext hprev i
  have hik : k < leftN + 3 := hik n a b hab hnext hprev
  have hlastRlt : N - k < rightN + 3 := hlastRlt n a b hab hnext hprev
  dsimp only [CyclicChildrenConstruction.leftN] at *
  change (1 < leftN + 3)
  rw [hleftLen]; omega

private theorem hrightLen_gt (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext :
    b ≠ a + 1) (hprev : a ≠ b + 1) : 1 < (rightN n a b) + 3 := by
  classical
  let N := n + 3
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  let rightN := N - k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  have hrightLen : rightN + 3 = N - k + 1 := hrightLen n a b hab hnext hprev
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  have hposRlt (i : Fin (rightN + 3)) : posR i < N := hposRlt n a b hab hnext hprev i
  have hik : k < leftN + 3 := hik n a b hab hnext hprev
  have hlastRlt : N - k < rightN + 3 := hlastRlt n a b hab hnext hprev
  dsimp only [CyclicChildrenConstruction.rightN] at *
  change (1 < rightN + 3)
  rw [hrightLen]; omega

private theorem hleft_succ (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext : b
    ≠ a + 1) (hprev : a ≠ b + 1) (i : Fin ((leftN n a b) + 3)) (hi : i.val < (k n a b)) :
      (il n a b hab hnext hprev) (i + 1) = (il n a b hab hnext hprev) i + 1 := by
  classical
  let N := n + 3
  have hN : 3 ≤ N := hN n
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  let rightN := N - k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  let il : Fin (leftN + 3) → Fin N := fun i => rot ⟨i.val, by rw [hleftLen] at i; omega⟩
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  have hposRlt (i : Fin (rightN + 3)) : posR i < N := hposRlt n a b hab hnext hprev i
  have hik : k < leftN + 3 := hik n a b hab hnext hprev
  have hlastRlt : N - k < rightN + 3 := hlastRlt n a b hab hnext hprev
  have hrot_succ (i : Fin N) : rot (i + 1) = rot i + 1 := hrot_succ n a b hab hnext hprev i
  have hleftLen_gt : 1 < leftN + 3 := hleftLen_gt n a b hab hnext hprev
  dsimp only [CyclicChildrenConstruction.k, CyclicChildrenConstruction.leftN] at *
  change (il (i + 1) = il i + 1)
  have hbound : i.val + 1 < leftN + 3 := by
    calc i.val + 1 < k + 1 := Nat.succ_lt_succ hi
      _ = leftN + 3 := hleftLen.symm
  have hone : (1 : Fin (leftN + 3)).val = 1 := by
    simp [Nat.mod_eq_of_lt hleftLen_gt]
  have hval : (i + 1).val = i.val + 1 := by
    change (i.val + (1 : Fin (leftN + 3)).val) % (leftN + 3) = i.val + 1
    rw [hone, Nat.mod_eq_of_lt hbound]
  have hparentidx : (⟨i.val, by omega⟩ : Fin N) + 1 = ⟨i.val + 1, by omega⟩ := by
    apply Fin.ext
    simp [Fin.val_add_eq_ite, Nat.mod_eq_of_lt (by omega : 1 < N),
      Nat.not_le.mpr (by omega : i.val + 1 < N)]
  calc
    il (i + 1) = rot ⟨i.val + 1, by
        calc i.val + 1 < k + 1 := Nat.succ_lt_succ hi
          _ ≤ N := by rw [← hleftLen]; omega⟩ := by
      dsimp [il]
      congr 1
      exact Fin.ext hval
    _ = rot ((⟨i.val, by omega⟩ : Fin N) + 1) := by rw [hparentidx]
    _ = rot ⟨i.val, by omega⟩ + 1 := hrot_succ ⟨i.val, by omega⟩
    _ = il i + 1 := rfl

private theorem hright_succ (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext :
    b ≠ a + 1) (hprev : a ≠ b + 1) (i : Fin ((rightN n a b) + 3)) (hi : i.val < (N n) - (k n a b)) :
      (ir n a b hab hnext hprev) (i + 1) = (ir n a b hab hnext hprev) i + 1 := by
  classical
  let N := n + 3
  have hN : 3 ≤ N := hN n
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  let rightN := N - k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  have hrightLen : rightN + 3 = N - k + 1 := hrightLen n a b hab hnext hprev
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  have hposRlt (i : Fin (rightN + 3)) : posR i < N := hposRlt n a b hab hnext hprev i
  let ir : Fin (rightN + 3) → Fin N := fun i => rot ⟨posR i, hposRlt i⟩
  have hik : k < leftN + 3 := hik n a b hab hnext hprev
  have hlastRlt : N - k < rightN + 3 := hlastRlt n a b hab hnext hprev
  have hrot_succ (i : Fin N) : rot (i + 1) = rot i + 1 := hrot_succ n a b hab hnext hprev i
  have hrightLen_gt : 1 < rightN + 3 := hrightLen_gt n a b hab hnext hprev
  dsimp only [CyclicChildrenConstruction.N, CyclicChildrenConstruction.k,
      CyclicChildrenConstruction.rightN] at *
  change (ir (i + 1) = ir i + 1)
  have hbound : i.val + 1 < rightN + 3 := by
    calc i.val + 1 < N - k + 1 := Nat.succ_lt_succ hi
      _ = rightN + 3 := hrightLen.symm
  have hone : (1 : Fin (rightN + 3)).val = 1 := by
    simp [Nat.mod_eq_of_lt hrightLen_gt]
  have hval : (i + 1).val = i.val + 1 := by
    change (i.val + (1 : Fin (rightN + 3)).val) % (rightN + 3) = i.val + 1
    rw [hone, Nat.mod_eq_of_lt hbound]
  by_cases hend : i.val + 1 = N - k
  · have hpnext : posR (i + 1) = 0 := by simp [posR, hval, hend]
    have hpar : (⟨k + i.val, by omega⟩ : Fin N) + 1 = 0 := by
      apply Fin.ext
      have hsum : k + i.val + 1 = N := by omega
      have honeN : (1 : Fin N).val = 1 := by
        simp [Nat.mod_eq_of_lt (by omega : 1 < N)]
      rw [Fin.val_add_eq_ite, honeN]
      rw [ite_eq_left (show N ≤ k + i.val + 1 by omega)]
      simp [hsum]
    calc
      ir (i + 1) = rot 0 := by simp [ir, hpnext]
      _ = rot ((⟨k + i.val, by omega⟩ : Fin N) + 1) := by rw [hpar]
      _ = rot ⟨k + i.val, by omega⟩ + 1 := hrot_succ _
      _ = ir i + 1 := by
        have hpi : posR i = k + i.val := by simp [posR]; omega
        simp [ir, hpi]
  · have hpnext : posR (i + 1) = k + i.val + 1 := by
      simp only [posR, hval, ite_eq_right hend]
      exact (Nat.add_assoc k i.val 1).symm
    have hpi : posR i = k + i.val := by
      have hne : i.val ≠ N - k := by omega
      simp [posR, hne]
    have hparentidx : (⟨k + i.val, by omega⟩ : Fin N) + 1 =
        ⟨k + i.val + 1, by omega⟩ := by
      apply Fin.ext
      simp [Fin.val_add_eq_ite, Nat.mod_eq_of_lt (by omega : 1 < N),
        Nat.not_le.mpr (by omega : k + i.val + 1 < N)]
    calc
      ir (i + 1) = rot ⟨k + i.val + 1, by omega⟩ := by
        simp only [ir, hpnext]
      _ = rot ((⟨k + i.val, by omega⟩ : Fin N) + 1) := by rw [hparentidx]
      _ = rot ⟨k + i.val, by omega⟩ + 1 := hrot_succ _
      _ = ir i + 1 := by simp [ir, hpi]

private theorem hleft_wrap (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext : b
    ≠ a + 1) (hprev : a ≠ b + 1) : (ik n a b hab hnext hprev) + 1 = 0 := by
  classical
  let N := n + 3
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  have hk_bounds : 2 ≤ k ∧ k ≤ N - 2 := hk_bounds n a b hab hnext hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  let rightN := N - k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  have hposRlt (i : Fin (rightN + 3)) : posR i < N := hposRlt n a b hab hnext hprev i
  have hik : k < leftN + 3 := hik n a b hab hnext hprev
  let ik : Fin (leftN + 3) := ⟨k, hik⟩
  have hlastRlt : N - k < rightN + 3 := hlastRlt n a b hab hnext hprev
  change (ik + 1 = 0)
  apply Fin.ext
  simp [ik, Fin.val_add_eq_ite, hleftLen,
    Nat.mod_eq_of_lt (by omega : 1 < k + 1)]

private theorem hright_wrap (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext :
    b ≠ a + 1) (hprev : a ≠ b + 1) : (lastR n a b hab hnext hprev) + 1 = 0 := by
  classical
  let N := n + 3
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  let rightN := N - k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  have hrightLen : rightN + 3 = N - k + 1 := hrightLen n a b hab hnext hprev
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  have hposRlt (i : Fin (rightN + 3)) : posR i < N := hposRlt n a b hab hnext hprev i
  have hik : k < leftN + 3 := hik n a b hab hnext hprev
  have hlastRlt : N - k < rightN + 3 := hlastRlt n a b hab hnext hprev
  let lastR : Fin (rightN + 3) := ⟨N - k, hlastRlt⟩
  change (lastR + 1 = 0)
  apply Fin.ext
  simp [lastR, Fin.val_add_eq_ite, hrightLen,
    Nat.mod_eq_of_lt (by omega : 1 < N - k + 1)]

private theorem hleft_ord_edge (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext
    : b ≠ a + 1) (hprev : a ≠ b + 1) (i : Fin ((leftN n a b) + 3)) (hi : i.val < (k n a b)) :
      (il n a b hab hnext hprev) (i + 1) = (il n a b hab hnext hprev) i + 1 := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  let il : Fin (leftN + 3) → Fin N := fun i => rot ⟨i.val, by rw [hleftLen] at i; omega⟩
  have hleft_succ (i : Fin (leftN + 3)) (hi : i.val < k) :
      il (i + 1) = il i + 1 := hleft_succ n a b hab hnext hprev i hi
  dsimp only [CyclicChildrenConstruction.k, CyclicChildrenConstruction.leftN] at *
  change (il (i + 1) = il i + 1)
  exact hleft_succ i hi

private theorem hright_ord_edge (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b)
    (hnext : b ≠ a + 1) (hprev : a ≠ b + 1) (i : Fin ((rightN n a b) + 3)) (hi : i.val < (N n) -
    (k n a b)) :
      (ir n a b hab hnext hprev) (i + 1) = (ir n a b hab hnext hprev) i + 1 := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  let rightN := N - k - 2
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  have hposRlt (i : Fin (rightN + 3)) : posR i < N := hposRlt n a b hab hnext hprev i
  let ir : Fin (rightN + 3) → Fin N := fun i => rot ⟨posR i, hposRlt i⟩
  have hright_succ (i : Fin (rightN + 3)) (hi : i.val < N - k) :
      ir (i + 1) = ir i + 1 := hright_succ n a b hab hnext hprev i hi
  dsimp only [CyclicChildrenConstruction.N, CyclicChildrenConstruction.k,
      CyclicChildrenConstruction.rightN] at *
  change (ir (i + 1) = ir i + 1)
  exact hright_succ i hi

private theorem hleft_last_edge (n : Nat) (p : P3381T1PolygonBoundary n) (a : Fin (n + 3)) (b :
    Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠ a + 1) (hprev : a ≠ b + 1) :
      segment Real (p.vertex ((il n a b hab hnext hprev) (ik n a b hab hnext hprev))) (p.vertex
          ((il n a b hab hnext hprev) ((ik n a b hab hnext hprev) + 1))) =
        segment Real (p.vertex a) (p.vertex b) := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  let il : Fin (leftN + 3) → Fin N := fun i => rot ⟨i.val, by rw [hleftLen] at i; omega⟩
  have hAil : il 0 = a := hAil n a b hab hnext hprev
  have hik : k < leftN + 3 := hik n a b hab hnext hprev
  let ik : Fin (leftN + 3) := ⟨k, hik⟩
  have hBil : il ik = b := hBil n a b hab hnext hprev
  have hleft_wrap : ik + 1 = 0 := hleft_wrap n a b hab hnext hprev
  change (segment Real (p.vertex (il ik)) (p.vertex (il (ik + 1))) =
        segment Real (p.vertex a) (p.vertex b))
  rw [hleft_wrap, hBil, hAil]
  exact segment_symm Real _ _

private theorem hright_last_edge (n : Nat) (p : P3381T1PolygonBoundary n) (a : Fin (n + 3)) (b
    : Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠ a + 1) (hprev : a ≠ b + 1) :
      segment Real (p.vertex ((ir n a b hab hnext hprev) (lastR n a b hab hnext hprev)))
          (p.vertex ((ir n a b hab hnext hprev) ((lastR n a b hab hnext hprev) + 1))) =
        segment Real (p.vertex a) (p.vertex b) := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  let rightN := N - k - 2
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  have hposRlt (i : Fin (rightN + 3)) : posR i < N := hposRlt n a b hab hnext hprev i
  let ir : Fin (rightN + 3) → Fin N := fun i => rot ⟨posR i, hposRlt i⟩
  have hBir : ir 0 = b := hBir n a b hab hnext hprev
  have hlastRlt : N - k < rightN + 3 := hlastRlt n a b hab hnext hprev
  let lastR : Fin (rightN + 3) := ⟨N - k, hlastRlt⟩
  have hAir : ir lastR = a := hAir n a b hab hnext hprev
  have hright_wrap : lastR + 1 = 0 := hright_wrap n a b hab hnext hprev
  change (segment Real (p.vertex (ir lastR)) (p.vertex (ir (lastR + 1))) =
        segment Real (p.vertex a) (p.vertex b))
  rw [hright_wrap, hAir, hBir]

private theorem hleft_nonlast (n : Nat) (p : P3381T1PolygonBoundary n) (a : Fin (n + 3)) (b :
    Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠ a + 1) (hprev : a ≠ b + 1) (i : Fin ((leftN n a b) +
    3)) (hi : i.val < (k n a b)) :
      segment Real (p.vertex ((il n a b hab hnext hprev) i)) (p.vertex ((il n a b hab hnext
          hprev) (i + 1))) =
        segment Real (p.vertex ((il n a b hab hnext hprev) i)) (p.vertex ((il n a b hab hnext
            hprev) i + 1)) := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  let il : Fin (leftN + 3) → Fin N := fun i => rot ⟨i.val, by rw [hleftLen] at i; omega⟩
  have hleft_succ (i : Fin (leftN + 3)) (hi : i.val < k) :
      il (i + 1) = il i + 1 := hleft_succ n a b hab hnext hprev i hi
  dsimp only [CyclicChildrenConstruction.k, CyclicChildrenConstruction.leftN] at *
  change (segment Real (p.vertex (il i)) (p.vertex (il (i + 1))) =
        segment Real (p.vertex (il i)) (p.vertex (il i + 1)))
  rw [hleft_succ i hi]

private theorem hright_nonlast (n : Nat) (p : P3381T1PolygonBoundary n) (a : Fin (n + 3)) (b :
    Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠ a + 1) (hprev : a ≠ b + 1) (i : Fin ((rightN n a b) +
    3)) (hi : i.val < (N n) - (k n a b)) :
      segment Real (p.vertex ((ir n a b hab hnext hprev) i)) (p.vertex ((ir n a b hab hnext
          hprev) (i + 1))) =
        segment Real (p.vertex ((ir n a b hab hnext hprev) i)) (p.vertex ((ir n a b hab hnext
            hprev) i + 1)) := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  let rightN := N - k - 2
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  have hposRlt (i : Fin (rightN + 3)) : posR i < N := hposRlt n a b hab hnext hprev i
  let ir : Fin (rightN + 3) → Fin N := fun i => rot ⟨posR i, hposRlt i⟩
  have hright_succ (i : Fin (rightN + 3)) (hi : i.val < N - k) :
      ir (i + 1) = ir i + 1 := hright_succ n a b hab hnext hprev i hi
  dsimp only [CyclicChildrenConstruction.N, CyclicChildrenConstruction.k,
      CyclicChildrenConstruction.rightN] at *
  change (segment Real (p.vertex (ir i)) (p.vertex (ir (i + 1))) =
        segment Real (p.vertex (ir i)) (p.vertex (ir i + 1)))
  rw [hright_succ i hi]

private theorem hleft_old_old (n : Nat) (p : P3381T1PolygonBoundary n) (a : Fin (n + 3)) (b :
    Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠ a + 1) (hprev : a ≠ b + 1) (i j : Fin ((leftN n a b)
    + 3)) (hi : i.val < (k n a b))
      (hj : j.val < (k n a b)) (hij : i ≠ j) :
      segment Real (p.vertex ((il n a b hab hnext hprev) i)) (p.vertex ((il n a b hab hnext
          hprev) (i + 1))) ∩
          segment Real (p.vertex ((il n a b hab hnext hprev) j)) (p.vertex ((il n a b hab hnext
              hprev) (j + 1))) =
        {x | (x = p.vertex ((il n a b hab hnext hprev) i) ∨ x = p.vertex ((il n a b hab hnext
            hprev) (i + 1))) ∧
          (x = p.vertex ((il n a b hab hnext hprev) j) ∨ x = p.vertex ((il n a b hab hnext hprev)
              (j + 1)))} := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  let il : Fin (leftN + 3) → Fin N := fun i => rot ⟨i.val, by rw [hleftLen] at i; omega⟩
  have hleft_inj : Function.Injective il := hleft_inj n a b hab hnext hprev
  have hleft_succ (i : Fin (leftN + 3)) (hi : i.val < k) :
      il (i + 1) = il i + 1 := hleft_succ n a b hab hnext hprev i hi
  dsimp only [CyclicChildrenConstruction.k, CyclicChildrenConstruction.leftN] at *
  change (segment Real (p.vertex (il i)) (p.vertex (il (i + 1))) ∩
          segment Real (p.vertex (il j)) (p.vertex (il (j + 1))) =
        {x | (x = p.vertex (il i) ∨ x = p.vertex (il (i + 1))) ∧
          (x = p.vertex (il j) ∨ x = p.vertex (il (j + 1)))})
  have hq : il i ≠ il j := by
    intro he
    exact hij (hleft_inj he)
  have hp := p.edge_intersection (il i) (il j) hq
  rw [← hleft_succ i hi, ← hleft_succ j hj] at hp
  exact hp

private theorem hright_old_old (n : Nat) (p : P3381T1PolygonBoundary n) (a : Fin (n + 3)) (b :
    Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠ a + 1) (hprev : a ≠ b + 1) (i j : Fin ((rightN n a b)
    + 3)) (hi : i.val < (N n) - (k n a b))
      (hj : j.val < (N n) - (k n a b)) (hij : i ≠ j) :
      segment Real (p.vertex ((ir n a b hab hnext hprev) i)) (p.vertex ((ir n a b hab hnext
          hprev) (i + 1))) ∩
          segment Real (p.vertex ((ir n a b hab hnext hprev) j)) (p.vertex ((ir n a b hab hnext
              hprev) (j + 1))) =
        {x | (x = p.vertex ((ir n a b hab hnext hprev) i) ∨ x = p.vertex ((ir n a b hab hnext
            hprev) (i + 1))) ∧
          (x = p.vertex ((ir n a b hab hnext hprev) j) ∨ x = p.vertex ((ir n a b hab hnext hprev)
              (j + 1)))} := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  let rightN := N - k - 2
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  have hposRlt (i : Fin (rightN + 3)) : posR i < N := hposRlt n a b hab hnext hprev i
  let ir : Fin (rightN + 3) → Fin N := fun i => rot ⟨posR i, hposRlt i⟩
  have hright_inj : Function.Injective ir := hright_inj n a b hab hnext hprev
  have hright_succ (i : Fin (rightN + 3)) (hi : i.val < N - k) :
      ir (i + 1) = ir i + 1 := hright_succ n a b hab hnext hprev i hi
  dsimp only [CyclicChildrenConstruction.N, CyclicChildrenConstruction.k,
      CyclicChildrenConstruction.rightN] at *
  change (segment Real (p.vertex (ir i)) (p.vertex (ir (i + 1))) ∩
          segment Real (p.vertex (ir j)) (p.vertex (ir (j + 1))) =
        {x | (x = p.vertex (ir i) ∨ x = p.vertex (ir (i + 1))) ∧
          (x = p.vertex (ir j) ∨ x = p.vertex (ir (j + 1)))})
  have hq : ir i ≠ ir j := by
    intro he
    exact hij (hright_inj he)
  have hp := p.edge_intersection (ir i) (ir j) hq
  rw [← hright_succ i hi, ← hright_succ j hj] at hp
  exact hp

private theorem hleft_old_last (n : Nat) (p : P3381T1PolygonBoundary n) (a : Fin (n + 3)) (b :
    Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠ a + 1) (hprev : a ≠ b + 1) (hclear : Disjoint
    (openSegment Real (p.vertex a) (p.vertex b)) (P3544T1BoundaryCarrier p)) (i : Fin ((leftN n
    a b) + 3)) (hi : i.val < (k n a b)) :
      segment Real (p.vertex ((il n a b hab hnext hprev) i)) (p.vertex ((il n a b hab hnext
          hprev) (i + 1))) ∩
          segment Real (p.vertex ((il n a b hab hnext hprev) (ik n a b hab hnext hprev)))
              (p.vertex ((il n a b hab hnext hprev) ((ik n a b hab hnext hprev) + 1))) =
        {x | (x = p.vertex ((il n a b hab hnext hprev) i) ∨ x = p.vertex ((il n a b hab hnext
            hprev) (i + 1))) ∧
          (x = p.vertex ((il n a b hab hnext hprev) (ik n a b hab hnext hprev)) ∨ x = p.vertex
              ((il n a b hab hnext hprev) ((ik n a b hab hnext hprev) + 1)))} := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  let il : Fin (leftN + 3) → Fin N := fun i => rot ⟨i.val, by rw [hleftLen] at i; omega⟩
  have hAil : il 0 = a := hAil n a b hab hnext hprev
  have hik : k < leftN + 3 := hik n a b hab hnext hprev
  let ik : Fin (leftN + 3) := ⟨k, hik⟩
  have hBil : il ik = b := hBil n a b hab hnext hprev
  have hchord_old (x : Real × Real) (j : Fin N) :
      x ∈ segment Real (p.vertex a) (p.vertex b) ∩
        segment Real (p.vertex j) (p.vertex (j + 1)) ↔
      (x = p.vertex a ∨ x = p.vertex b) ∧
        (x = p.vertex j ∨ x = p.vertex (j + 1)) := hchord_old n p a b hclear x j
  have hleft_succ (i : Fin (leftN + 3)) (hi : i.val < k) :
      il (i + 1) = il i + 1 := hleft_succ n a b hab hnext hprev i hi
  have hleft_wrap : ik + 1 = 0 := hleft_wrap n a b hab hnext hprev
  have hleft_last_edge :
      segment Real (p.vertex (il ik)) (p.vertex (il (ik + 1))) =
        segment Real (p.vertex a) (p.vertex b) := hleft_last_edge n p a b hab hnext hprev
  have hleft_nonlast (i : Fin (leftN + 3)) (hi : i.val < k) :
      segment Real (p.vertex (il i)) (p.vertex (il (i + 1))) =
        segment Real (p.vertex (il i)) (p.vertex (il i + 1)) := hleft_nonlast n p a b hab hnext
            hprev i hi
  dsimp only [CyclicChildrenConstruction.k, CyclicChildrenConstruction.leftN] at *
  change (segment Real (p.vertex (il i)) (p.vertex (il (i + 1))) ∩
          segment Real (p.vertex (il ik)) (p.vertex (il (ik + 1))) =
        {x | (x = p.vertex (il i) ∨ x = p.vertex (il (i + 1))) ∧
          (x = p.vertex (il ik) ∨ x = p.vertex (il (ik + 1)))})
  rw [hleft_nonlast i hi, hleft_last_edge]
  ext x
  have hh := hchord_old x (il i)
  rw [Set.mem_inter_iff] at hh
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  simpa only [hleft_succ i hi, hleft_wrap, hBil, hAil, and_comm, or_comm] using hh

private theorem hright_old_last (n : Nat) (p : P3381T1PolygonBoundary n) (a : Fin (n + 3)) (b :
    Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠ a + 1) (hprev : a ≠ b + 1) (hclear : Disjoint
    (openSegment Real (p.vertex a) (p.vertex b)) (P3544T1BoundaryCarrier p)) (i : Fin ((rightN
    n a b) + 3)) (hi : i.val < (N n) - (k n a b)) :
      segment Real (p.vertex ((ir n a b hab hnext hprev) i)) (p.vertex ((ir n a b hab hnext
          hprev) (i + 1))) ∩
          segment Real (p.vertex ((ir n a b hab hnext hprev) (lastR n a b hab hnext hprev)))
              (p.vertex ((ir n a b hab hnext hprev) ((lastR n a b hab hnext hprev) + 1))) =
        {x | (x = p.vertex ((ir n a b hab hnext hprev) i) ∨ x = p.vertex ((ir n a b hab hnext
            hprev) (i + 1))) ∧
          (x = p.vertex ((ir n a b hab hnext hprev) (lastR n a b hab hnext hprev)) ∨ x = p.vertex
              ((ir n a b hab hnext hprev) ((lastR n a b hab hnext hprev) + 1)))} := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  let rightN := N - k - 2
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  have hposRlt (i : Fin (rightN + 3)) : posR i < N := hposRlt n a b hab hnext hprev i
  let ir : Fin (rightN + 3) → Fin N := fun i => rot ⟨posR i, hposRlt i⟩
  have hBir : ir 0 = b := hBir n a b hab hnext hprev
  have hlastRlt : N - k < rightN + 3 := hlastRlt n a b hab hnext hprev
  let lastR : Fin (rightN + 3) := ⟨N - k, hlastRlt⟩
  have hAir : ir lastR = a := hAir n a b hab hnext hprev
  have hchord_old (x : Real × Real) (j : Fin N) :
      x ∈ segment Real (p.vertex a) (p.vertex b) ∩
        segment Real (p.vertex j) (p.vertex (j + 1)) ↔
      (x = p.vertex a ∨ x = p.vertex b) ∧
        (x = p.vertex j ∨ x = p.vertex (j + 1)) := hchord_old n p a b hclear x j
  have hright_succ (i : Fin (rightN + 3)) (hi : i.val < N - k) :
      ir (i + 1) = ir i + 1 := hright_succ n a b hab hnext hprev i hi
  have hright_wrap : lastR + 1 = 0 := hright_wrap n a b hab hnext hprev
  have hright_last_edge :
      segment Real (p.vertex (ir lastR)) (p.vertex (ir (lastR + 1))) =
        segment Real (p.vertex a) (p.vertex b) := hright_last_edge n p a b hab hnext hprev
  have hright_nonlast (i : Fin (rightN + 3)) (hi : i.val < N - k) :
      segment Real (p.vertex (ir i)) (p.vertex (ir (i + 1))) =
        segment Real (p.vertex (ir i)) (p.vertex (ir i + 1)) := hright_nonlast n p a b hab hnext
            hprev i hi
  dsimp only [CyclicChildrenConstruction.N, CyclicChildrenConstruction.k,
      CyclicChildrenConstruction.rightN] at *
  change (segment Real (p.vertex (ir i)) (p.vertex (ir (i + 1))) ∩
          segment Real (p.vertex (ir lastR)) (p.vertex (ir (lastR + 1))) =
        {x | (x = p.vertex (ir i) ∨ x = p.vertex (ir (i + 1))) ∧
          (x = p.vertex (ir lastR) ∨ x = p.vertex (ir (lastR + 1)))})
  rw [hright_nonlast i hi, hright_last_edge]
  ext x
  have hh := hchord_old x (ir i)
  rw [Set.mem_inter_iff] at hh
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  simpa only [hright_succ i hi, hright_wrap, hAir, hBir, and_comm] using hh

private theorem hleft_last_old (n : Nat) (p : P3381T1PolygonBoundary n) (a : Fin (n + 3)) (b :
    Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠ a + 1) (hprev : a ≠ b + 1) (hclear : Disjoint
    (openSegment Real (p.vertex a) (p.vertex b)) (P3544T1BoundaryCarrier p)) (i : Fin ((leftN n
    a b) + 3)) (hi : i.val < (k n a b)) :
      segment Real (p.vertex ((il n a b hab hnext hprev) (ik n a b hab hnext hprev))) (p.vertex
          ((il n a b hab hnext hprev) ((ik n a b hab hnext hprev) + 1))) ∩
          segment Real (p.vertex ((il n a b hab hnext hprev) i)) (p.vertex ((il n a b hab hnext
              hprev) (i + 1))) =
        {x | (x = p.vertex ((il n a b hab hnext hprev) (ik n a b hab hnext hprev)) ∨ x = p.vertex
            ((il n a b hab hnext hprev) ((ik n a b hab hnext hprev) + 1))) ∧
          (x = p.vertex ((il n a b hab hnext hprev) i) ∨ x = p.vertex ((il n a b hab hnext hprev)
              (i + 1)))} := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  let il : Fin (leftN + 3) → Fin N := fun i => rot ⟨i.val, by rw [hleftLen] at i; omega⟩
  have hik : k < leftN + 3 := hik n a b hab hnext hprev
  let ik : Fin (leftN + 3) := ⟨k, hik⟩
  have hleft_old_last (i : Fin (leftN + 3)) (hi : i.val < k) :
      segment Real (p.vertex (il i)) (p.vertex (il (i + 1))) ∩
          segment Real (p.vertex (il ik)) (p.vertex (il (ik + 1))) =
        {x | (x = p.vertex (il i) ∨ x = p.vertex (il (i + 1))) ∧
          (x = p.vertex (il ik) ∨ x = p.vertex (il (ik + 1)))} := hleft_old_last n p a b hab
              hnext hprev hclear i hi
  dsimp only [CyclicChildrenConstruction.k, CyclicChildrenConstruction.leftN] at *
  change (segment Real (p.vertex (il ik)) (p.vertex (il (ik + 1))) ∩
          segment Real (p.vertex (il i)) (p.vertex (il (i + 1))) =
        {x | (x = p.vertex (il ik) ∨ x = p.vertex (il (ik + 1))) ∧
          (x = p.vertex (il i) ∨ x = p.vertex (il (i + 1)))})
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  have hh := congrArg (fun s : Set (Real × Real) => x ∈ s) (hleft_old_last i hi)
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hh
  constructor
  · rintro ⟨hdiag, hold⟩
    rcases hh.mp ⟨hold, hdiag⟩ with ⟨eold, ediag⟩
    exact ⟨ediag, eold⟩
  · rintro ⟨ediag, eold⟩
    rcases hh.mpr ⟨eold, ediag⟩ with ⟨hold, hdiag⟩
    exact ⟨hdiag, hold⟩

private theorem hright_last_old (n : Nat) (p : P3381T1PolygonBoundary n) (a : Fin (n + 3)) (b :
    Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠ a + 1) (hprev : a ≠ b + 1) (hclear : Disjoint
    (openSegment Real (p.vertex a) (p.vertex b)) (P3544T1BoundaryCarrier p)) (i : Fin ((rightN
    n a b) + 3)) (hi : i.val < (N n) - (k n a b)) :
      segment Real (p.vertex ((ir n a b hab hnext hprev) (lastR n a b hab hnext hprev)))
          (p.vertex ((ir n a b hab hnext hprev) ((lastR n a b hab hnext hprev) + 1))) ∩
          segment Real (p.vertex ((ir n a b hab hnext hprev) i)) (p.vertex ((ir n a b hab hnext
              hprev) (i + 1))) =
        {x | (x = p.vertex ((ir n a b hab hnext hprev) (lastR n a b hab hnext hprev)) ∨ x =
            p.vertex ((ir n a b hab hnext hprev) ((lastR n a b hab hnext hprev) + 1))) ∧
          (x = p.vertex ((ir n a b hab hnext hprev) i) ∨ x = p.vertex ((ir n a b hab hnext hprev)
              (i + 1)))} := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  let rightN := N - k - 2
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  have hposRlt (i : Fin (rightN + 3)) : posR i < N := hposRlt n a b hab hnext hprev i
  let ir : Fin (rightN + 3) → Fin N := fun i => rot ⟨posR i, hposRlt i⟩
  have hlastRlt : N - k < rightN + 3 := hlastRlt n a b hab hnext hprev
  let lastR : Fin (rightN + 3) := ⟨N - k, hlastRlt⟩
  have hright_old_last (i : Fin (rightN + 3)) (hi : i.val < N - k) :
      segment Real (p.vertex (ir i)) (p.vertex (ir (i + 1))) ∩
          segment Real (p.vertex (ir lastR)) (p.vertex (ir (lastR + 1))) =
        {x | (x = p.vertex (ir i) ∨ x = p.vertex (ir (i + 1))) ∧
          (x = p.vertex (ir lastR) ∨ x = p.vertex (ir (lastR + 1)))} := hright_old_last n p a b
              hab hnext hprev hclear i hi
  dsimp only [CyclicChildrenConstruction.N, CyclicChildrenConstruction.k,
      CyclicChildrenConstruction.rightN] at *
  change (segment Real (p.vertex (ir lastR)) (p.vertex (ir (lastR + 1))) ∩
          segment Real (p.vertex (ir i)) (p.vertex (ir (i + 1))) =
        {x | (x = p.vertex (ir lastR) ∨ x = p.vertex (ir (lastR + 1))) ∧
          (x = p.vertex (ir i) ∨ x = p.vertex (ir (i + 1)))})
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  have hh := congrArg (fun s : Set (Real × Real) => x ∈ s) (hright_old_last i hi)
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hh
  constructor
  · rintro ⟨hdiag, hold⟩
    rcases hh.mp ⟨hold, hdiag⟩ with ⟨eold, ediag⟩
    exact ⟨ediag, eold⟩
  · rintro ⟨ediag, eold⟩
    rcases hh.mpr ⟨eold, ediag⟩ with ⟨hold, hdiag⟩
    exact ⟨hdiag, hold⟩

private noncomputable abbrev leftPoly (n : Nat) (p : P3381T1PolygonBoundary n) (a : Fin (n +
    3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠ a + 1) (hprev : a ≠ b + 1) (hclear :
    Disjoint (openSegment Real (p.vertex a) (p.vertex b)) (P3544T1BoundaryCarrier p)) :
    P3381T1PolygonBoundary (leftN n a b) := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  let rightN := N - k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  let il : Fin (leftN + 3) → Fin N := fun i => rot ⟨i.val, by rw [hleftLen] at i; omega⟩
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  have hposRlt (i : Fin (rightN + 3)) : posR i < N := hposRlt n a b hab hnext hprev i
  have hleft_inj : Function.Injective il := hleft_inj n a b hab hnext hprev
  have hik : k < leftN + 3 := hik n a b hab hnext hprev
  let ik : Fin (leftN + 3) := ⟨k, hik⟩
  have hlastRlt : N - k < rightN + 3 := hlastRlt n a b hab hnext hprev
  have hleft_old_old (i j : Fin (leftN + 3)) (hi : i.val < k)
      (hj : j.val < k) (hij : i ≠ j) :
      segment Real (p.vertex (il i)) (p.vertex (il (i + 1))) ∩
          segment Real (p.vertex (il j)) (p.vertex (il (j + 1))) =
        {x | (x = p.vertex (il i) ∨ x = p.vertex (il (i + 1))) ∧
          (x = p.vertex (il j) ∨ x = p.vertex (il (j + 1)))} := hleft_old_old n p a b hab hnext
              hprev i j hi hj hij
  have hleft_old_last (i : Fin (leftN + 3)) (hi : i.val < k) :
      segment Real (p.vertex (il i)) (p.vertex (il (i + 1))) ∩
          segment Real (p.vertex (il ik)) (p.vertex (il (ik + 1))) =
        {x | (x = p.vertex (il i) ∨ x = p.vertex (il (i + 1))) ∧
          (x = p.vertex (il ik) ∨ x = p.vertex (il (ik + 1)))} := hleft_old_last n p a b hab
              hnext hprev hclear i hi
  have hleft_last_old (i : Fin (leftN + 3)) (hi : i.val < k) :
      segment Real (p.vertex (il ik)) (p.vertex (il (ik + 1))) ∩
          segment Real (p.vertex (il i)) (p.vertex (il (i + 1))) =
        {x | (x = p.vertex (il ik) ∨ x = p.vertex (il (ik + 1))) ∧
          (x = p.vertex (il i) ∨ x = p.vertex (il (i + 1)))} := hleft_last_old n p a b hab hnext
              hprev hclear i hi
  dsimp only [CyclicChildrenConstruction.leftN] at *
  change (P3381T1PolygonBoundary leftN)
  exact {
    vertex := fun i => p.vertex (il i)
    rational := fun i => p.rational (il i)
    injective := p.injective.comp hleft_inj
    edge_intersection := by
      intro i j hij
      have hi' : i.val < leftN + 3 := i.isLt
      have hj' : j.val < leftN + 3 := j.isLt
      by_cases hi : i.val = k
      · have hik' : i = ik := Fin.ext hi
        subst i
        by_cases hj : j.val = k
        · have hjk' : j = ik := Fin.ext hj
          subst j
          exact (hij rfl).elim
        · have hjlt : j.val < k := by
            have hb : j.val < k + 1 := by calc j.val < leftN + 3 := j.isLt
              _ = k + 1 := hleftLen
            omega
          exact hleft_last_old j hjlt
      · have hilt : i.val < k := by
          have hb : i.val < k + 1 := by calc i.val < leftN + 3 := i.isLt
            _ = k + 1 := hleftLen
          omega
        by_cases hj : j.val = k
        · have hjk' : j = ik := Fin.ext hj
          subst j
          exact hleft_old_last i hilt
        · have hjlt : j.val < k := by
            have hb : j.val < k + 1 := by calc j.val < leftN + 3 := j.isLt
              _ = k + 1 := hleftLen
            omega
          exact hleft_old_old i j hilt hjlt hij
  }

private noncomputable abbrev rightPoly (n : Nat) (p : P3381T1PolygonBoundary n) (a : Fin (n +
    3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠ a + 1) (hprev : a ≠ b + 1) (hclear :
    Disjoint (openSegment Real (p.vertex a) (p.vertex b)) (P3544T1BoundaryCarrier p)) :
    P3381T1PolygonBoundary (rightN n a b) := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  let rightN := N - k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  have hrightLen : rightN + 3 = N - k + 1 := hrightLen n a b hab hnext hprev
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  have hposRlt (i : Fin (rightN + 3)) : posR i < N := hposRlt n a b hab hnext hprev i
  let ir : Fin (rightN + 3) → Fin N := fun i => rot ⟨posR i, hposRlt i⟩
  have hright_inj : Function.Injective ir := hright_inj n a b hab hnext hprev
  have hik : k < leftN + 3 := hik n a b hab hnext hprev
  have hlastRlt : N - k < rightN + 3 := hlastRlt n a b hab hnext hprev
  let lastR : Fin (rightN + 3) := ⟨N - k, hlastRlt⟩
  have hright_old_old (i j : Fin (rightN + 3)) (hi : i.val < N - k)
      (hj : j.val < N - k) (hij : i ≠ j) :
      segment Real (p.vertex (ir i)) (p.vertex (ir (i + 1))) ∩
          segment Real (p.vertex (ir j)) (p.vertex (ir (j + 1))) =
        {x | (x = p.vertex (ir i) ∨ x = p.vertex (ir (i + 1))) ∧
          (x = p.vertex (ir j) ∨ x = p.vertex (ir (j + 1)))} := hright_old_old n p a b hab hnext
              hprev i j hi hj hij
  have hright_old_last (i : Fin (rightN + 3)) (hi : i.val < N - k) :
      segment Real (p.vertex (ir i)) (p.vertex (ir (i + 1))) ∩
          segment Real (p.vertex (ir lastR)) (p.vertex (ir (lastR + 1))) =
        {x | (x = p.vertex (ir i) ∨ x = p.vertex (ir (i + 1))) ∧
          (x = p.vertex (ir lastR) ∨ x = p.vertex (ir (lastR + 1)))} := hright_old_last n p a b
              hab hnext hprev hclear i hi
  have hright_last_old (i : Fin (rightN + 3)) (hi : i.val < N - k) :
      segment Real (p.vertex (ir lastR)) (p.vertex (ir (lastR + 1))) ∩
          segment Real (p.vertex (ir i)) (p.vertex (ir (i + 1))) =
        {x | (x = p.vertex (ir lastR) ∨ x = p.vertex (ir (lastR + 1))) ∧
          (x = p.vertex (ir i) ∨ x = p.vertex (ir (i + 1)))} := hright_last_old n p a b hab hnext
              hprev hclear i hi
  dsimp only [CyclicChildrenConstruction.rightN] at *
  change (P3381T1PolygonBoundary rightN)
  exact {
    vertex := fun i => p.vertex (ir i)
    rational := fun i => p.rational (ir i)
    injective := p.injective.comp hright_inj
    edge_intersection := by
      intro i j hij
      have hi' : i.val < rightN + 3 := i.isLt
      have hj' : j.val < rightN + 3 := j.isLt
      by_cases hi : i.val = N - k
      · have hilast' : i = lastR := Fin.ext hi
        subst i
        by_cases hj : j.val = N - k
        · have hjlast' : j = lastR := Fin.ext hj
          subst j
          exact (hij rfl).elim
        · have hjlt : j.val < N - k := by
            have hb : j.val < N - k + 1 := by calc j.val < rightN + 3 := j.isLt
              _ = N - k + 1 := hrightLen
            omega
          exact hright_last_old j hjlt
      · have hilt : i.val < N - k := by
          have hb : i.val < N - k + 1 := by calc i.val < rightN + 3 := i.isLt
            _ = N - k + 1 := hrightLen
          omega
        by_cases hj : j.val = N - k
        · have hjlast' : j = lastR := Fin.ext hj
          subst j
          exact hright_old_last i hilt
        · have hjlt : j.val < N - k := by
            have hb : j.val < N - k + 1 := by calc j.val < rightN + 3 := j.isLt
              _ = N - k + 1 := hrightLen
            omega
          exact hright_old_old i j hilt hjlt hij
  }

private theorem hrotsurj (n : Nat) (a : Fin (n + 3)) : Function.Surjective (rot n a) := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  have hrot_inj : Function.Injective rot := hrot_inj n a
  change (Function.Surjective rot)
  exact Finite.injective_iff_surjective.mp hrot_inj

private theorem hparent_mem (n : Nat) (p : P3381T1PolygonBoundary n) (x : Real × Real) :
      x ∈ P3544T1BoundaryCarrier p ↔
        ∃ j : Fin (N n), x ∈ segment Real (p.vertex j) (p.vertex (j + 1)) := by
  classical
  let N := n + 3
  dsimp only [CyclicChildrenConstruction.N] at *
  change (x ∈ P3544T1BoundaryCarrier p ↔
        ∃ j : Fin N, x ∈ segment Real (p.vertex j) (p.vertex (j + 1)))
  change x ∈ (⋃ j : Fin N, segment Real (p.vertex j) (p.vertex (j + 1))) ↔ _
  simp only [Set.mem_iUnion]

private theorem hleft_mem (n : Nat) (p : P3381T1PolygonBoundary n) (a : Fin (n + 3)) (b : Fin
    (n + 3)) (hab : a ≠ b) (hnext : b ≠ a + 1) (hprev : a ≠ b + 1) (hclear : Disjoint
    (openSegment Real (p.vertex a) (p.vertex b)) (P3544T1BoundaryCarrier p)) (x : Real × Real) :
      x ∈ P3544T1BoundaryCarrier (leftPoly n p a b hab hnext hprev hclear) ↔
        ∃ i : Fin ((leftN n a b) + 3),
          x ∈ segment Real (p.vertex ((il n a b hab hnext hprev) i)) (p.vertex ((il n a b hab
              hnext hprev) (i + 1))) := by
  simp only [P3544T1BoundaryCarrier, Set.mem_iUnion, leftPoly, il, id_eq]

private theorem hright_mem (n : Nat) (p : P3381T1PolygonBoundary n) (a : Fin (n + 3)) (b : Fin
    (n + 3)) (hab : a ≠ b) (hnext : b ≠ a + 1) (hprev : a ≠ b + 1) (hclear : Disjoint
    (openSegment Real (p.vertex a) (p.vertex b)) (P3544T1BoundaryCarrier p)) (x : Real × Real) :
      x ∈ P3544T1BoundaryCarrier (rightPoly n p a b hab hnext hprev hclear) ↔
        ∃ i : Fin ((rightN n a b) + 3),
          x ∈ segment Real (p.vertex ((ir n a b hab hnext hprev) i)) (p.vertex ((ir n a b hab
              hnext hprev) (i + 1))) := by
  simp only [P3544T1BoundaryCarrier, Set.mem_iUnion, rightPoly, ir, id_eq]

private theorem hcarrier_union (n : Nat) (p : P3381T1PolygonBoundary n) (a : Fin (n + 3)) (b :
    Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠ a + 1) (hprev : a ≠ b + 1) (hclear : Disjoint
    (openSegment Real (p.vertex a) (p.vertex b)) (P3544T1BoundaryCarrier p)) :
      P3544T1BoundaryCarrier (leftPoly n p a b hab hnext hprev hclear) ∪
          P3544T1BoundaryCarrier (rightPoly n p a b hab hnext hprev hclear) =
        P3544T1BoundaryCarrier p ∪ segment Real (p.vertex a) (p.vertex b) := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  let rightN := N - k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  have hrightLen : rightN + 3 = N - k + 1 := hrightLen n a b hab hnext hprev
  let il : Fin (leftN + 3) → Fin N := fun i => rot ⟨i.val, by rw [hleftLen] at i; omega⟩
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  have hposRlt (i : Fin (rightN + 3)) : posR i < N := hposRlt n a b hab hnext hprev i
  let ir : Fin (rightN + 3) → Fin N := fun i => rot ⟨posR i, hposRlt i⟩
  have hleft_inj : Function.Injective il := hleft_inj n a b hab hnext hprev
  have hright_inj : Function.Injective ir := hright_inj n a b hab hnext hprev
  have hik : k < leftN + 3 := hik n a b hab hnext hprev
  let ik : Fin (leftN + 3) := ⟨k, hik⟩
  have hlastRlt : N - k < rightN + 3 := hlastRlt n a b hab hnext hprev
  let lastR : Fin (rightN + 3) := ⟨N - k, hlastRlt⟩
  have hleft_succ (i : Fin (leftN + 3)) (hi : i.val < k) :
      il (i + 1) = il i + 1 := hleft_succ n a b hab hnext hprev i hi
  have hright_succ (i : Fin (rightN + 3)) (hi : i.val < N - k) :
      ir (i + 1) = ir i + 1 := hright_succ n a b hab hnext hprev i hi
  have hleft_last_edge :
      segment Real (p.vertex (il ik)) (p.vertex (il (ik + 1))) =
        segment Real (p.vertex a) (p.vertex b) := hleft_last_edge n p a b hab hnext hprev
  have hright_last_edge :
      segment Real (p.vertex (ir lastR)) (p.vertex (ir (lastR + 1))) =
        segment Real (p.vertex a) (p.vertex b) := hright_last_edge n p a b hab hnext hprev
  have hleft_nonlast (i : Fin (leftN + 3)) (hi : i.val < k) :
      segment Real (p.vertex (il i)) (p.vertex (il (i + 1))) =
        segment Real (p.vertex (il i)) (p.vertex (il i + 1)) := hleft_nonlast n p a b hab hnext
            hprev i hi
  have hright_nonlast (i : Fin (rightN + 3)) (hi : i.val < N - k) :
      segment Real (p.vertex (ir i)) (p.vertex (ir (i + 1))) =
        segment Real (p.vertex (ir i)) (p.vertex (ir i + 1)) := hright_nonlast n p a b hab hnext
            hprev i hi
  have hleft_old_old (i j : Fin (leftN + 3)) (hi : i.val < k)
      (hj : j.val < k) (hij : i ≠ j) :
      segment Real (p.vertex (il i)) (p.vertex (il (i + 1))) ∩
          segment Real (p.vertex (il j)) (p.vertex (il (j + 1))) =
        {x | (x = p.vertex (il i) ∨ x = p.vertex (il (i + 1))) ∧
          (x = p.vertex (il j) ∨ x = p.vertex (il (j + 1)))} := hleft_old_old n p a b hab hnext
              hprev i j hi hj hij
  have hright_old_old (i j : Fin (rightN + 3)) (hi : i.val < N - k)
      (hj : j.val < N - k) (hij : i ≠ j) :
      segment Real (p.vertex (ir i)) (p.vertex (ir (i + 1))) ∩
          segment Real (p.vertex (ir j)) (p.vertex (ir (j + 1))) =
        {x | (x = p.vertex (ir i) ∨ x = p.vertex (ir (i + 1))) ∧
          (x = p.vertex (ir j) ∨ x = p.vertex (ir (j + 1)))} := hright_old_old n p a b hab hnext
              hprev i j hi hj hij
  have hleft_old_last (i : Fin (leftN + 3)) (hi : i.val < k) :
      segment Real (p.vertex (il i)) (p.vertex (il (i + 1))) ∩
          segment Real (p.vertex (il ik)) (p.vertex (il (ik + 1))) =
        {x | (x = p.vertex (il i) ∨ x = p.vertex (il (i + 1))) ∧
          (x = p.vertex (il ik) ∨ x = p.vertex (il (ik + 1)))} := hleft_old_last n p a b hab
              hnext hprev hclear i hi
  have hright_old_last (i : Fin (rightN + 3)) (hi : i.val < N - k) :
      segment Real (p.vertex (ir i)) (p.vertex (ir (i + 1))) ∩
          segment Real (p.vertex (ir lastR)) (p.vertex (ir (lastR + 1))) =
        {x | (x = p.vertex (ir i) ∨ x = p.vertex (ir (i + 1))) ∧
          (x = p.vertex (ir lastR) ∨ x = p.vertex (ir (lastR + 1)))} := hright_old_last n p a b
              hab hnext hprev hclear i hi
  have hleft_last_old (i : Fin (leftN + 3)) (hi : i.val < k) :
      segment Real (p.vertex (il ik)) (p.vertex (il (ik + 1))) ∩
          segment Real (p.vertex (il i)) (p.vertex (il (i + 1))) =
        {x | (x = p.vertex (il ik) ∨ x = p.vertex (il (ik + 1))) ∧
          (x = p.vertex (il i) ∨ x = p.vertex (il (i + 1)))} := hleft_last_old n p a b hab hnext
              hprev hclear i hi
  have hright_last_old (i : Fin (rightN + 3)) (hi : i.val < N - k) :
      segment Real (p.vertex (ir lastR)) (p.vertex (ir (lastR + 1))) ∩
          segment Real (p.vertex (ir i)) (p.vertex (ir (i + 1))) =
        {x | (x = p.vertex (ir lastR) ∨ x = p.vertex (ir (lastR + 1))) ∧
          (x = p.vertex (ir i) ∨ x = p.vertex (ir (i + 1)))} := hright_last_old n p a b hab hnext
              hprev hclear i hi
  let leftPoly : P3381T1PolygonBoundary leftN := CyclicChildrenConstruction.leftPoly n p a b
      hab hnext hprev hclear
  let rightPoly : P3381T1PolygonBoundary rightN := CyclicChildrenConstruction.rightPoly n p a b
      hab hnext hprev hclear
  have hrotsurj : Function.Surjective rot := hrotsurj n a
  have hparent_mem (x : Real × Real) :
      x ∈ P3544T1BoundaryCarrier p ↔
        ∃ j : Fin N, x ∈ segment Real (p.vertex j) (p.vertex (j + 1)) := hparent_mem n p x
  have hleft_mem (x : Real × Real) :
      x ∈ P3544T1BoundaryCarrier leftPoly ↔
        ∃ i : Fin (leftN + 3),
          x ∈ segment Real (p.vertex (il i)) (p.vertex (il (i + 1))) := hleft_mem n p a b hab
              hnext hprev hclear x
  have hright_mem (x : Real × Real) :
      x ∈ P3544T1BoundaryCarrier rightPoly ↔
        ∃ i : Fin (rightN + 3),
          x ∈ segment Real (p.vertex (ir i)) (p.vertex (ir (i + 1))) := hright_mem n p a b hab
              hnext hprev hclear x
  change (P3544T1BoundaryCarrier leftPoly ∪ P3544T1BoundaryCarrier rightPoly =
        P3544T1BoundaryCarrier p ∪ segment Real (p.vertex a) (p.vertex b))
  ext x
  constructor
  · intro hx
    rcases hx with hx | hx
    · obtain ⟨i, hxi⟩ := hleft_mem x |>.mp hx
      by_cases hi : i.val = k
      · have hiK : i = ik := Fin.ext hi
        subst i
        apply Or.inr
        rw [← hleft_last_edge]
        exact hxi
      · have hilt : i.val < k := by
          have hb : i.val < k + 1 := by calc i.val < leftN + 3 := i.isLt
            _ = k + 1 := hleftLen
          omega
        have hxi' := hxi
        rw [hleft_nonlast i hilt] at hxi'
        apply Or.inl
        exact (hparent_mem x).mpr ⟨il i, hxi'⟩
    · obtain ⟨i, hxi⟩ := hright_mem x |>.mp hx
      by_cases hi : i.val = N - k
      · have hiK : i = lastR := Fin.ext hi
        subst i
        apply Or.inr
        rw [← hright_last_edge]
        exact hxi
      · have hilt : i.val < N - k := by
          have hb : i.val < N - k + 1 := by calc i.val < rightN + 3 := i.isLt
            _ = N - k + 1 := hrightLen
          omega
        have hxi' := hxi
        rw [hright_nonlast i hilt] at hxi'
        apply Or.inl
        exact (hparent_mem x).mpr ⟨ir i, hxi'⟩
  · rintro (hx | hx)
    · obtain ⟨j, hj⟩ := (hparent_mem x).mp hx
      obtain ⟨t, ht⟩ := hrotsurj j
      by_cases htleft : t.val < k
      · let i : Fin (leftN + 3) := ⟨t.val, by rw [hleftLen]; omega⟩
        have hil : il i = j := by
          dsimp [il, i]
          rw [← ht]
        have hilnext : il (i + 1) = j + 1 := by
          rw [hleft_succ i htleft, hil]
        have hxi : x ∈ segment Real (p.vertex (il i)) (p.vertex (il (i + 1))) := by
          simpa only [hil, hilnext] using hj
        exact Or.inl ((hleft_mem x).mpr ⟨i, hxi⟩)
      · have htge : k ≤ t.val := by omega
        have hti : t.val - k < N - k := by omega
        let i : Fin (rightN + 3) := ⟨t.val - k, by rw [hrightLen]; omega⟩
        have hir : ir i = j := by
          have hpos : posR ⟨t.val - k, by rw [hrightLen]; omega⟩ = t.val := by
            simp only [posR]
            split_ifs with h
            · omega
            · omega
          calc
            ir i = rot t := by
              dsimp [ir]
              congr 1
              apply Fin.ext
              exact hpos
            _ = j := ht
        have hirnext : ir (i + 1) = j + 1 := by
          rw [hright_succ i hti, hir]
        have hxi : x ∈ segment Real (p.vertex (ir i)) (p.vertex (ir (i + 1))) := by
          simpa only [hir, hirnext] using hj
        exact Or.inr ((hright_mem x).mpr ⟨i, hxi⟩)
    · have hxiL : x ∈ segment Real (p.vertex (il ik)) (p.vertex (il (ik + 1))) := by
        rw [hleft_last_edge]
        exact hx
      have hxiR : x ∈ segment Real (p.vertex (ir lastR)) (p.vertex (ir (lastR + 1))) := by
        rw [hright_last_edge]
        exact hx
      exact Or.inl ((hleft_mem x).mpr ⟨ik, hxiL⟩)

private theorem hcommon_index (n : Nat) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext
    : b ≠ a + 1) (hprev : a ≠ b + 1) (s t : Fin (N n)) (hs : s ∈ Set.range (il n a b hab hnext
    hprev))
      (ht : t ∈ Set.range (ir n a b hab hnext hprev)) (hst : s = t) : s = a ∨ s = b := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  let rightN := N - k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  let il : Fin (leftN + 3) → Fin N := fun i => rot ⟨i.val, by rw [hleftLen] at i; omega⟩
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  have hposRlt (i : Fin (rightN + 3)) : posR i < N := hposRlt n a b hab hnext hprev i
  let ir : Fin (rightN + 3) → Fin N := fun i => rot ⟨posR i, hposRlt i⟩
  have hcommon : Set.range il ∩ Set.range ir = {a, b} := hcommon n a b hab hnext hprev
  dsimp only [CyclicChildrenConstruction.N] at *
  have hm : s ∈ Set.range il ∩ Set.range ir := by
    refine ⟨hs, ?_⟩
    rcases ht with ⟨j, hj⟩
    exact ⟨j, hj.trans hst.symm⟩
  have habmem : s ∈ ({a, b} : Set (Fin N)) := by
    rw [← hcommon]
    exact hm
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using habmem

private theorem hpoint_chord (n : Nat) (p : P3381T1PolygonBoundary n) (a : Fin (n + 3)) (b :
    Fin (n + 3)) (x : Real × Real) (s : Fin (N n))
      (hxs : x = p.vertex s) (hs : s = a ∨ s = b) :
      x ∈ segment Real (p.vertex a) (p.vertex b) := by
  classical
  let N := n + 3
  dsimp only [CyclicChildrenConstruction.N] at *
  rcases hs with h | h
  · rw [hxs, h]
    exact left_mem_segment Real _ _
  · rw [hxs, h]
    exact right_mem_segment Real _ _

private theorem hcarrier_intersection (n : Nat) (p : P3381T1PolygonBoundary n) (a : Fin (n +
    3)) (b : Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠ a + 1) (hprev : a ≠ b + 1) (hclear :
    Disjoint (openSegment Real (p.vertex a) (p.vertex b)) (P3544T1BoundaryCarrier p)) :
      P3544T1BoundaryCarrier (leftPoly n p a b hab hnext hprev hclear) ∩
          P3544T1BoundaryCarrier (rightPoly n p a b hab hnext hprev hclear) =
        segment Real (p.vertex a) (p.vertex b) := by
  classical
  let N := n + 3
  let rot : Fin N → Fin N := fun i => a + i
  let k : Nat := (b.val + N - a.val) % N
  have hklt : k < N := hklt n a b
  have hkv : k = if a.val ≤ b.val then b.val - a.val else b.val + N - a.val := hkv n a b
  have hkle : k + 2 ≤ N := hkle n a b hprev
  let root : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hrootlen : root.length = N := hrootlen n
  let leftN := k - 2
  let rightN := N - k - 2
  have hleftLen : leftN + 3 = k + 1 := hleftLen n a b hab hnext hprev
  have hrightLen : rightN + 3 = N - k + 1 := hrightLen n a b hab hnext hprev
  let il : Fin (leftN + 3) → Fin N := fun i => rot ⟨i.val, by rw [hleftLen] at i; omega⟩
  let posR : Fin (rightN + 3) → Nat := fun i =>
    if i.val = N - k then 0 else k + i.val
  have hposRlt (i : Fin (rightN + 3)) : posR i < N := hposRlt n a b hab hnext hprev i
  let ir : Fin (rightN + 3) → Fin N := fun i => rot ⟨posR i, hposRlt i⟩
  have hleft_inj : Function.Injective il := hleft_inj n a b hab hnext hprev
  have hright_inj : Function.Injective ir := hright_inj n a b hab hnext hprev
  have hAil : il 0 = a := hAil n a b hab hnext hprev
  have hik : k < leftN + 3 := hik n a b hab hnext hprev
  let ik : Fin (leftN + 3) := ⟨k, hik⟩
  have hBil : il ik = b := hBil n a b hab hnext hprev
  have hlastRlt : N - k < rightN + 3 := hlastRlt n a b hab hnext hprev
  let lastR : Fin (rightN + 3) := ⟨N - k, hlastRlt⟩
  have hAir : ir lastR = a := hAir n a b hab hnext hprev
  have hcommon : Set.range il ∩ Set.range ir = {a, b} := hcommon n a b hab hnext hprev
  have hleft_succ (i : Fin (leftN + 3)) (hi : i.val < k) :
      il (i + 1) = il i + 1 := hleft_succ n a b hab hnext hprev i hi
  have hright_succ (i : Fin (rightN + 3)) (hi : i.val < N - k) :
      ir (i + 1) = ir i + 1 := hright_succ n a b hab hnext hprev i hi
  have hleft_last_edge :
      segment Real (p.vertex (il ik)) (p.vertex (il (ik + 1))) =
        segment Real (p.vertex a) (p.vertex b) := hleft_last_edge n p a b hab hnext hprev
  have hright_last_edge :
      segment Real (p.vertex (ir lastR)) (p.vertex (ir (lastR + 1))) =
        segment Real (p.vertex a) (p.vertex b) := hright_last_edge n p a b hab hnext hprev
  have hleft_nonlast (i : Fin (leftN + 3)) (hi : i.val < k) :
      segment Real (p.vertex (il i)) (p.vertex (il (i + 1))) =
        segment Real (p.vertex (il i)) (p.vertex (il i + 1)) := hleft_nonlast n p a b hab hnext
            hprev i hi
  have hright_nonlast (i : Fin (rightN + 3)) (hi : i.val < N - k) :
      segment Real (p.vertex (ir i)) (p.vertex (ir (i + 1))) =
        segment Real (p.vertex (ir i)) (p.vertex (ir i + 1)) := hright_nonlast n p a b hab hnext
            hprev i hi
  have hleft_old_old (i j : Fin (leftN + 3)) (hi : i.val < k)
      (hj : j.val < k) (hij : i ≠ j) :
      segment Real (p.vertex (il i)) (p.vertex (il (i + 1))) ∩
          segment Real (p.vertex (il j)) (p.vertex (il (j + 1))) =
        {x | (x = p.vertex (il i) ∨ x = p.vertex (il (i + 1))) ∧
          (x = p.vertex (il j) ∨ x = p.vertex (il (j + 1)))} := hleft_old_old n p a b hab hnext
              hprev i j hi hj hij
  have hright_old_old (i j : Fin (rightN + 3)) (hi : i.val < N - k)
      (hj : j.val < N - k) (hij : i ≠ j) :
      segment Real (p.vertex (ir i)) (p.vertex (ir (i + 1))) ∩
          segment Real (p.vertex (ir j)) (p.vertex (ir (j + 1))) =
        {x | (x = p.vertex (ir i) ∨ x = p.vertex (ir (i + 1))) ∧
          (x = p.vertex (ir j) ∨ x = p.vertex (ir (j + 1)))} := hright_old_old n p a b hab hnext
              hprev i j hi hj hij
  have hleft_old_last (i : Fin (leftN + 3)) (hi : i.val < k) :
      segment Real (p.vertex (il i)) (p.vertex (il (i + 1))) ∩
          segment Real (p.vertex (il ik)) (p.vertex (il (ik + 1))) =
        {x | (x = p.vertex (il i) ∨ x = p.vertex (il (i + 1))) ∧
          (x = p.vertex (il ik) ∨ x = p.vertex (il (ik + 1)))} := hleft_old_last n p a b hab
              hnext hprev hclear i hi
  have hright_old_last (i : Fin (rightN + 3)) (hi : i.val < N - k) :
      segment Real (p.vertex (ir i)) (p.vertex (ir (i + 1))) ∩
          segment Real (p.vertex (ir lastR)) (p.vertex (ir (lastR + 1))) =
        {x | (x = p.vertex (ir i) ∨ x = p.vertex (ir (i + 1))) ∧
          (x = p.vertex (ir lastR) ∨ x = p.vertex (ir (lastR + 1)))} := hright_old_last n p a b
              hab hnext hprev hclear i hi
  have hleft_last_old (i : Fin (leftN + 3)) (hi : i.val < k) :
      segment Real (p.vertex (il ik)) (p.vertex (il (ik + 1))) ∩
          segment Real (p.vertex (il i)) (p.vertex (il (i + 1))) =
        {x | (x = p.vertex (il ik) ∨ x = p.vertex (il (ik + 1))) ∧
          (x = p.vertex (il i) ∨ x = p.vertex (il (i + 1)))} := hleft_last_old n p a b hab hnext
              hprev hclear i hi
  have hright_last_old (i : Fin (rightN + 3)) (hi : i.val < N - k) :
      segment Real (p.vertex (ir lastR)) (p.vertex (ir (lastR + 1))) ∩
          segment Real (p.vertex (ir i)) (p.vertex (ir (i + 1))) =
        {x | (x = p.vertex (ir lastR) ∨ x = p.vertex (ir (lastR + 1))) ∧
          (x = p.vertex (ir i) ∨ x = p.vertex (ir (i + 1)))} := hright_last_old n p a b hab hnext
              hprev hclear i hi
  let leftPoly : P3381T1PolygonBoundary leftN := CyclicChildrenConstruction.leftPoly n p a b
      hab hnext hprev hclear
  let rightPoly : P3381T1PolygonBoundary rightN := CyclicChildrenConstruction.rightPoly n p a b
      hab hnext hprev hclear
  have hleft_mem (x : Real × Real) :
      x ∈ P3544T1BoundaryCarrier leftPoly ↔
        ∃ i : Fin (leftN + 3),
          x ∈ segment Real (p.vertex (il i)) (p.vertex (il (i + 1))) := hleft_mem n p a b hab
              hnext hprev hclear x
  have hright_mem (x : Real × Real) :
      x ∈ P3544T1BoundaryCarrier rightPoly ↔
        ∃ i : Fin (rightN + 3),
          x ∈ segment Real (p.vertex (ir i)) (p.vertex (ir (i + 1))) := hright_mem n p a b hab
              hnext hprev hclear x
  have hcommon_index (s t : Fin N) (hs : s ∈ Set.range il)
      (ht : t ∈ Set.range ir) (hst : s = t) : s = a ∨ s = b := hcommon_index n a b hab hnext
          hprev s t hs ht hst
  have hpoint_chord (x : Real × Real) (s : Fin N)
      (hxs : x = p.vertex s) (hs : s = a ∨ s = b) :
      x ∈ segment Real (p.vertex a) (p.vertex b) := hpoint_chord n p a b x s hxs hs
  change (P3544T1BoundaryCarrier leftPoly ∩ P3544T1BoundaryCarrier rightPoly =
        segment Real (p.vertex a) (p.vertex b))
  ext x
  constructor
  · rintro ⟨hxL, hxR⟩
    obtain ⟨i, hxi⟩ := (hleft_mem x).mp hxL
    obtain ⟨j, hxj⟩ := (hright_mem x).mp hxR
    by_cases hi : i.val = k
    · have hiK : i = ik := Fin.ext hi
      subst i
      rw [hleft_last_edge] at hxi
      exact hxi
    · have hilt : i.val < k := by
        have hb : i.val < k + 1 := by calc i.val < leftN + 3 := i.isLt
          _ = k + 1 := hleftLen
        omega
      by_cases hj : j.val = N - k
      · have hjK : j = lastR := Fin.ext hj
        subst j
        rw [hright_last_edge] at hxj
        exact hxj
      · have hjlt : j.val < N - k := by
          have hb : j.val < N - k + 1 := by calc j.val < rightN + 3 := j.isLt
            _ = N - k + 1 := hrightLen
          omega
        have hxi' := hxi
        have hxj' := hxj
        rw [hleft_nonlast i hilt] at hxi'
        rw [hright_nonlast j hjlt] at hxj'
        have hqne : il i ≠ ir j := by
          intro hq
          have hm : il i ∈ Set.range il ∩ Set.range ir := by
            exact ⟨⟨i, rfl⟩, ⟨j, hq.symm⟩⟩
          have habmem : il i ∈ ({a, b} : Set (Fin N)) := by
            rw [← hcommon]
            exact hm
          have habidx : il i = a ∨ il i = b := by
            simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using habmem
          rcases habidx with hia | hib
          · have hi0 : i = 0 := hleft_inj (hia.trans hAil.symm)
            have hjlast : j = lastR := hright_inj (by
              calc
                ir j = il i := hq.symm
                _ = a := hia
                _ = ir lastR := hAir.symm)
            have : j.val = N - k := congrArg Fin.val hjlast
            omega
          · have hik' : i = ik := hleft_inj (hib.trans hBil.symm)
            have : i.val = k := congrArg Fin.val hik'
            omega
        have hp := p.edge_intersection (il i) (ir j) hqne
        have hboth : x ∈ segment Real (p.vertex (il i)) (p.vertex (il i + 1)) ∩
            segment Real (p.vertex (ir j)) (p.vertex (ir j + 1)) := ⟨hxi', hxj'⟩
        rw [hp] at hboth
        rcases hboth with ⟨hleftEnd, hrightEnd⟩
        rcases hleftEnd with hL | hL
        · rcases hrightEnd with hR | hR
          · have hst : il i = ir j := p.injective (hL.symm.trans hR)
            have habidx := hcommon_index (il i) (ir j) ⟨i, rfl⟩ ⟨j, rfl⟩ hst
            exact hpoint_chord x (il i) hL habidx
          · have hR' : x = p.vertex (ir (j + 1)) := by
              simpa only [← hright_succ j hjlt] using hR
            have hst : il i = ir (j + 1) := p.injective (hL.symm.trans hR')
            have hri : ir (j + 1) ∈ Set.range ir := ⟨j + 1, rfl⟩
            have habidx := hcommon_index (il i) (ir (j + 1)) ⟨i, rfl⟩ hri hst
            exact hpoint_chord x (il i) hL habidx
        · rcases hrightEnd with hR | hR
          · have hL' : x = p.vertex (il (i + 1)) := by
              simpa only [← hleft_succ i hilt] using hL
            have hst : il (i + 1) = ir j := p.injective (hL'.symm.trans hR)
            have hli : il (i + 1) ∈ Set.range il := ⟨i + 1, rfl⟩
            have habidx := hcommon_index (il (i + 1)) (ir j) hli ⟨j, rfl⟩ hst
            exact hpoint_chord x (il (i + 1)) hL' habidx
          · have hL' : x = p.vertex (il (i + 1)) := by
              simpa only [← hleft_succ i hilt] using hL
            have hR' : x = p.vertex (ir (j + 1)) := by
              simpa only [← hright_succ j hjlt] using hR
            have hst : il (i + 1) = ir (j + 1) := p.injective (hL'.symm.trans hR')
            have hli : il (i + 1) ∈ Set.range il := ⟨i + 1, rfl⟩
            have hri : ir (j + 1) ∈ Set.range ir := ⟨j + 1, rfl⟩
            have habidx := hcommon_index (il (i + 1)) (ir (j + 1)) hli hri hst
            exact hpoint_chord x (il (i + 1)) hL' habidx
  · intro hx
    have hxiL : x ∈ segment Real (p.vertex (il ik)) (p.vertex (il (ik + 1))) := by
      rw [hleft_last_edge]
      exact hx
    have hxiR : x ∈ segment Real (p.vertex (ir lastR)) (p.vertex (ir (lastR + 1))) := by
      rw [hright_last_edge]
      exact hx
    exact ⟨(hleft_mem x).mpr ⟨ik, hxiL⟩,
      (hright_mem x).mpr ⟨lastR, hxiR⟩⟩

end CyclicChildrenConstruction

theorem P3650T1CyclicChildrenExists {n : Nat} (p : P3381T1PolygonBoundary n)
    (a b : Fin (n + 3)) (hab : a ≠ b) (hnext : b ≠ a + 1)
    (hprev : a ≠ b + 1)
    (hclear : Disjoint (openSegment Real (p.vertex a) (p.vertex b))
      (P3544T1BoundaryCarrier p)) :
    Nonempty (P3650T1CyclicChildren p a b) := by
  classical
  have hk_bounds := CyclicChildrenConstruction.hk_bounds n a b hab hnext hprev
  refine ⟨{
    left_n := (CyclicChildrenConstruction.leftN n a b)
    right_n := (CyclicChildrenConstruction.rightN n a b)
    left_lt := (CyclicChildrenConstruction.hleftLt n a b hab hnext hprev)
    right_lt := (CyclicChildrenConstruction.hrightLt n a b hab hnext hprev)
    left := (CyclicChildrenConstruction.leftPoly n p a b hab hnext hprev hclear)
    right := (CyclicChildrenConstruction.rightPoly n p a b hab hnext hprev hclear)
    il := (CyclicChildrenConstruction.il n a b hab hnext hprev)
    ir := (CyclicChildrenConstruction.ir n a b hab hnext hprev)
    il_injective := (CyclicChildrenConstruction.hleft_inj n a b hab hnext hprev)
    ir_injective := (CyclicChildrenConstruction.hright_inj n a b hab hnext hprev)
    left_vertex := rfl
    right_vertex := rfl
    u := (CyclicChildrenConstruction.u n a b)
    v := (CyclicChildrenConstruction.v n a b)
    hu := by rw [(CyclicChildrenConstruction.hlu n a b hprev)]; omega
    hv := by rw [(CyclicChildrenConstruction.hlv n a b hprev)]; omega
    rotation := a.val
    parent_order := (CyclicChildrenConstruction.hparent_order n a b hab hnext hprev)
    left_order := (CyclicChildrenConstruction.hleft_order n a b hab hnext hprev)
    right_order := (CyclicChildrenConstruction.hright_order n a b hab hnext hprev)
    common_indices := (CyclicChildrenConstruction.hcommon n a b hab hnext hprev)
    carrier_union := (CyclicChildrenConstruction.hcarrier_union n p a b hab hnext hprev hclear)
    carrier_intersection := (CyclicChildrenConstruction.hcarrier_intersection n p a b hab hnext
        hprev hclear)
  }⟩

end ApollonianSuperharmonic

end
