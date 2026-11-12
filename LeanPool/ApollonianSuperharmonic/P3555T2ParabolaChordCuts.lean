/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.Linarith

public import Mathlib.Analysis.Convex.Join
public import LeanPool.ApollonianSuperharmonic.P3381T1TriangleDeterminant

-- [TABLET NODE: P3555T2ParabolaChordCuts]

/-!
# P3555T2ParabolaChordCuts

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ParabolaChordLemmas

private theorem hL :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))), ((a :: (u ++ b :: v)).Nodup) → (
    let L := a :: (u ++ b :: v)
    L.Nodup) := by
  classical
  intro n a b u v hboundary L
  exact hboundary

private theorem haNotTail :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    (L.Nodup) → (a ∉ u ++ b :: v) := by
  classical
  intro n a b u v L hL
  exact (List.nodup_cons.mp hL).1

private theorem htailNodup :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    (L.Nodup) → ((u ++ b :: v).Nodup) := by
  classical
  intro n a b u v L hL
  exact (List.nodup_cons.mp hL).2

private theorem hne :
    ∀ (n : Nat), (Fin (n + 3) → Real × Real) → (∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u :
        List (Fin (n + 3))), ∀ (v : List (Fin (n + 3))), ((a :: (u ++ b :: v)).Nodup) → ((∃ k :
        Nat, (a :: (u ++ b :: v)).Sublist ((List.ofFn (fun i : Fin (n + 3) => i)).rotate k)) → (
    let L := a :: (u ++ b :: v)
    (L.Nodup) → ((a ∉ u ++ b :: v) → (((u ++ b :: v).Nodup) → (a ≠ b)))))) := by
  classical
  intro n q a b u v hboundary hcyclic L hL haNotTail htailNodup hab
  subst b
  apply haNotTail
  simp

private theorem hparts :
    ∀ (n : Nat), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v : List (Fin (n + 3))), ((u
        ++ b :: v).Nodup) → (u.Nodup ∧ (b :: v).Nodup ∧ ∀ a ∈ u, ∀ b_1 ∈ b :: v, a ≠ b_1) := by
  classical
  intro n b u v htailNodup
  exact List.nodup_append.mp htailNodup

private theorem huNodup :
    ∀ (n : Nat), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v : List (Fin (n + 3))),
        (u.Nodup ∧ (b :: v).Nodup ∧ ∀ a ∈ u, ∀ b_1 ∈ b :: v, a ≠ b_1) → (u.Nodup) := by
  classical
  intro n b u v hparts
  exact hparts.1

private theorem hbNotU :
    ∀ (n : Nat), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v : List (Fin (n + 3))),
        (u.Nodup ∧ (b :: v).Nodup ∧ ∀ a ∈ u, ∀ b_1 ∈ b :: v, a ≠ b_1) → (b ∉ u) := by
  classical
  intro n b u v hparts hb
  exact hparts.2.2 b hb b (by simp) rfl

private theorem hvNodup :
    ∀ (n : Nat), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v : List (Fin (n + 3))),
        (u.Nodup ∧ (b :: v).Nodup ∧ ∀ a ∈ u, ∀ b_1 ∈ b :: v, a ≠ b_1) → (v.Nodup) := by
  classical
  intro n b u v hparts
  have := List.nodup_cons.mp hparts.2.1
  exact this.2

private theorem hbNotV :
    ∀ (n : Nat), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v : List (Fin (n + 3))),
        (u.Nodup ∧ (b :: v).Nodup ∧ ∀ a ∈ u, ∀ b_1 ∈ b :: v, a ≠ b_1) → (b ∉ v) := by
  classical
  intro n b u v hparts
  exact (List.nodup_cons.mp hparts.2.1).1

private theorem haNotU :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))), (a ∉ u ++ b :: v) → (a ∉ u) := by
  classical
  intro n a b u v haNotTail ha
  apply haNotTail
  exact List.mem_append_left _ ha

private theorem haNotV :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))), (a ∉ u ++ b :: v) → (a ∉ v) := by
  classical
  intro n a b u v haNotTail ha
  apply haNotTail
  exact List.mem_append_right _ (List.mem_cons_of_mem _ ha)

private theorem huvDisjoint :
    ∀ (n : Nat), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v : List (Fin (n + 3))),
        (u.Nodup ∧ (b :: v).Nodup ∧ ∀ a ∈ u, ∀ b_1 ∈ b :: v, a ≠ b_1) → (∀ i, i ∈ u → i ∈ v →
        False) := by
  classical
  intro n b u v hparts i hiU hiV
  have hcross := hparts.2.2 i hiU i (List.mem_cons_of_mem _ hiV)
  exact hcross rfl

private theorem hANodup :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))),
    let A := a :: (u ++ [b])
    (a ≠ b) → ((u.Nodup) → ((b ∉ u) → ((a ∉ u) → (A.Nodup)))) := by
  classical
  intro n a b u A hne huNodup hbNotU haNotU
  apply List.nodup_cons.mpr
  constructor
  · intro ha
    rcases List.mem_append.mp ha with hau | hab
    · exact haNotU hau
    · exact hne (List.mem_singleton.mp hab)
  · apply List.nodup_append.mpr
    exact ⟨huNodup, by simp, by
      intro x hx y hy hxy
      simp only [List.mem_singleton] at hy
      have hxb : x = b := hxy.trans hy
      exact hbNotU (hxb ▸ hx)⟩

private theorem hBNodup :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (v : List (Fin (n + 3))),
    let B := b :: (v ++ [a])
    (a ≠ b) → ((v.Nodup) → ((b ∉ v) → ((a ∉ v) → (B.Nodup)))) := by
  classical
  intro n a b v B hne hvNodup hbNotV haNotV
  apply List.nodup_cons.mpr
  constructor
  · intro hb
    rcases List.mem_append.mp hb with hbv | hba
    · exact hbNotV hbv
    · exact hne.symm (List.mem_singleton.mp hba)
  · apply List.nodup_append.mpr
    exact ⟨hvNodup, by simp, by
      intro x hx y hy hxy
      simp only [List.mem_singleton] at hy
      have hxa : x = a := hxy.trans hy
      exact haNotV (hxa ▸ hx)⟩

private theorem hnil :
    ∀ (n : Nat), ∀ (xs : List (Fin (n + 3))), ([] : List (Fin (n + 3))).Sublist xs := by
  classical
  intro n xs
  induction xs with
  | nil => exact List.Sublist.slnil
  | cons x xs ih => exact List.Sublist.cons x ih

private theorem hnilv :
    ∀ (n : Nat), ∀ (v : List (Fin (n + 3))), (∀ (xs : List (Fin (n + 3))), ([] : List (Fin (n +
        3))).Sublist xs) → ([].Sublist v) := by
  classical
  intro n v hnil
  exact hnil v

private theorem hbSub :
    ∀ (n : Nat), ∀ (b : Fin (n + 3)), ∀ (v : List (Fin (n + 3))), ([].Sublist v) → (([b] : List
        (Fin (n + 3))).Sublist (b :: v)) := by
  classical
  intro n b v hnilv
  exact List.Sublist.cons_cons b hnilv

private theorem hAtail :
    ∀ (n : Nat), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v : List (Fin (n + 3))),
        (([b] : List (Fin (n + 3))).Sublist (b :: v)) → ((u ++ [b]).Sublist (u ++ b :: v)) := by
  classical
  intro n b u v hbSub
  exact List.Sublist.append (List.Sublist.refl u) hbSub

private theorem hAsubL :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    let A := a :: (u ++ [b])
    ((u ++ [b]).Sublist (u ++ b :: v)) → (A.Sublist L) := by
  classical
  intro n a b u v L A hAtail
  exact List.Sublist.cons_cons a hAtail

private theorem hrootlen :
    ∀ (n : Nat),
    let root := List.ofFn (fun i : Fin (n + 3) => i)
    root.length = n + 3 := by
  classical
  intro n root
  simp [root]

private theorem hRval :
    ∀ (n : Nat), ∀ (k : ℕ),
    let root := List.ofFn (fun i : Fin (n + 3) => i)
    let R := root.rotate k
    (root.length = n + 3) → (∀ (j : Fin R.length), (R.get j).val = (j.val + k) % (n + 3)) := by
  classical
  intro n k root R hrootlen j
  rw [List.get_rotate]
  rw [List.get_ofFn]
  simp only [Fin.val_cast, hrootlen]

private theorem hrankDiff :
    ∀ (n : Nat), (List (Fin (n + 3))) → (∀ (m : Nat), ∀ (k : Nat), ∀ (p : Nat), ∀ (s : Nat), (0 <
        m) → ((p < m) → ((s < m) → ((p ≤ s) → ((((s+k)%m+m-((p+k)%m))%m) = s-p))))) := by
  classical
  intro n v m k p s hm hp hs hps
  let x := (p + k) % m
  let d := s-p
  have hx : x < m := Nat.mod_lt _ hm
  have hd : d < m := by omega
  have hy : (s + k) % m = (x + d) % m := by
    rw [show s + k = (p + k) + (s-p) by omega, Nat.add_mod,
      Nat.mod_eq_of_lt hd]
  rw [hy]
  dsimp [d]
  by_cases hwrap : x + (s-p) < m
  · rw [Nat.mod_eq_of_lt hwrap,
      show x + (s-p) + m - x = m + (s-p) by omega, Nat.add_mod]
    simp only [Nat.mod_self, zero_add, dvd_refl, Nat.mod_mod_of_dvd]
    exact Nat.mod_eq_of_lt hd
  · have hwrap' : m ≤ x + (s-p) := by omega
    have hmod : (x + (s-p)) % m = x + (s-p) - m := by
      rw [Nat.mod_eq_sub_mod hwrap',
        Nat.mod_eq_of_lt (by omega : x + (s-p) - m < m)]
    rw [hmod, show x + (s-p) - m + m - x = s-p by omega, Nat.mod_eq_of_lt hd]

private theorem hsourceA :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    (⟨0, by simp [L]⟩ : Fin L.length).val <
      (⟨u.length+1, by simp [L]⟩ : Fin L.length).val := by
  classical
  intro n a b u v L
  simp

private theorem hsourceB :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))), (0 < v.length) → (
    let L := a :: (u ++ b :: v)
    u.length+1 < L.length) := by
  classical
  intro n a b u v hv L
  simp only [L, List.length_cons, List.length_append]
  omega

private theorem haAtRoot :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    ∀ (k : ℕ),
    let root := List.ofFn (fun i : Fin (n + 3) => i)
    let R := root.rotate k
    ∀ (emb : Fin (a :: (u ++ b :: v)).length ↪o Fin ((List.ofFn fun (i : Fin (n + (3 : ℕ))) =>
        i).rotate k).length), (∀ (ix : Fin (a :: (u ++ b :: v)).length), (a :: (u ++ b :: v)).get
        ix = ((List.ofFn fun (i : Fin (n + (3 : ℕ))) => i).rotate k).get ((emb : Fin (a :: (u ++
        b :: v)).length → Fin ((List.ofFn fun (i : Fin (n + (3 : ℕ))) => i).rotate k).length)
        ix)) → (
    let ia : Fin L.length := ⟨0, by simp [L]⟩
    R.get (emb ia) = a) := by
  classical
  intro n a b u v L k root R emb hemb ia
  have h := hemb ia
  calc
    R.get (emb ia) = L.get ia := h.symm
    _ = a := by simp [L, ia]

private theorem hbAtRoot :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    ∀ (k : ℕ),
    let root := List.ofFn (fun i : Fin (n + 3) => i)
    let R := root.rotate k
    ∀ (emb : Fin (a :: (u ++ b :: v)).length ↪o Fin ((List.ofFn fun (i : Fin (n + (3 : ℕ))) =>
        i).rotate k).length), (∀ (ix : Fin (a :: (u ++ b :: v)).length), (a :: (u ++ b :: v)).get
        ix = ((List.ofFn fun (i : Fin (n + (3 : ℕ))) => i).rotate k).get ((emb : Fin (a :: (u ++
        b :: v)).length → Fin ((List.ofFn fun (i : Fin (n + (3 : ℕ))) => i).rotate k).length)
        ix)) → (∀ (hsourceB : u.length+1 < L.length),
    let ib : Fin L.length := ⟨u.length+1, hsourceB⟩
    R.get (emb ib) = b) := by
  classical
  intro n a b u v L k root R emb hemb hsourceB ib
  have h := hemb ib
  calc
    R.get (emb ib) = L.get ib := h.symm
    _ = b := by simp [L, ib]

private theorem hrootOrder :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    ∀ (k : ℕ), ∀ (emb : Fin (a :: (u ++ b :: v)).length ↪o Fin ((List.ofFn fun (i : Fin (n + (3 :
        ℕ))) => i).rotate k).length), ((⟨0, by simp [L]⟩ : Fin L.length).val < (⟨u.length+1, by
        simp [L]⟩ : Fin L.length).val) → (∀ (hsourceB : u.length+1 < L.length),
    let ia : Fin L.length := ⟨0, by simp [L]⟩
    let ib : Fin L.length := ⟨u.length+1, hsourceB⟩
    (emb ia).val < (emb ib).val) := by
  classical
  intro n a b u v L k emb hsourceA hsourceB ia ib
  exact emb.lt_iff_lt.mpr hsourceA

private theorem hBVsubDrop :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    ∀ (k : ℕ),
    let root := List.ofFn (fun i : Fin (n + 3) => i)
    let R := root.rotate k
    ∀ (emb : Fin (a :: (u ++ b :: v)).length ↪o Fin ((List.ofFn fun (i : Fin (n + (3 : ℕ))) =>
        i).rotate k).length), (∀ (ix : Fin (a :: (u ++ b :: v)).length), (a :: (u ++ b :: v)).get
        ix = ((List.ofFn fun (i : Fin (n + (3 : ℕ))) => i).rotate k).get ((emb : Fin (a :: (u ++
        b :: v)).length → Fin ((List.ofFn fun (i : Fin (n + (3 : ℕ))) => i).rotate k).length)
        ix)) → (∀ (hsourceB : u.length+1 < L.length),
    let ib : Fin L.length := ⟨u.length+1, hsourceB⟩
    (b :: v).Sublist (R.drop (emb ib).val)) := by
  classical
  intro n a b u v L k root R emb hemb hsourceB ib
  apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
  let src (p : Fin (b :: v).length) : Fin L.length :=
    ⟨ib.val + p.val, by
      have hLen : ib.val + (b :: v).length = L.length := by
        simp only [ib, L, List.length_cons, List.length_append]
        omega
      exact (Nat.add_lt_add_left p.isLt ib.val).trans_eq hLen⟩
  let f (p : Fin (b :: v).length) : Fin (R.drop (emb ib).val).length :=
    ⟨(emb (src p)).val - (emb ib).val, by
      have hs : ib ≤ src p := by
        apply Fin.le_iff_val_le_val.mpr
        change ib.val ≤ ib.val + p.val
        exact Nat.le_add_right _ _
      have hm : (emb ib).val ≤ (emb (src p)).val :=
        Fin.le_iff_val_le_val.mp (emb.monotone hs)
      have ht : (emb (src p)).val < R.length := (emb (src p)).isLt
      simp only [List.length_drop]
      omega⟩
  have hf : StrictMono f := by
    intro p q hpq
    apply Fin.lt_def.mpr
    have hpq' : (src p).val < (src q).val := by
      change ib.val + p.val < ib.val + q.val
      exact Nat.add_lt_add_left (Fin.lt_def.mp hpq) _
    have he : (emb (src p)).val < (emb (src q)).val :=
      Fin.lt_def.mp (emb.strictMono hpq')
    have hpLower : (emb ib).val ≤ (emb (src p)).val := by
      apply Fin.le_iff_val_le_val.mp (emb.monotone _)
      apply Fin.le_iff_val_le_val.mpr
      change ib.val ≤ ib.val+p.val
      exact Nat.le_add_right _ _
    have hqLower : (emb ib).val ≤ (emb (src q)).val := by
      apply Fin.le_iff_val_le_val.mp (emb.monotone _)
      apply Fin.le_iff_val_le_val.mpr
      change ib.val ≤ ib.val+q.val
      exact Nat.le_add_right _ _
    simp only [f]
    omega
  refine ⟨OrderEmbedding.ofStrictMono f hf, ?_⟩
  intro p
  have hsrc : (b :: v).get p = L.get (src p) := by
    refine Fin.cases ?_ ?_ p
    · simp [L, ib, src]
    · intro j
      have hix : (src (Fin.succ j)).val = u.length + (j.val+1) + 1 := by
        simp [src, ib]
        omega
      have htail : L.get ⟨u.length+(j.val+1)+1, by
          simp only [L, List.length_cons, List.length_append, List.length_cons]
          omega⟩ = v.get j := by
        rw [List.get_eq_getElem, List.get_eq_getElem]
        change (a :: (u ++ b :: v))[(u.length+(j.val+1))+1] = v[j.val]
        rw [List.getElem_cons_succ]
        rw [List.getElem_append_right (by omega)]
        simp [List.getElem_cons_succ]
      calc
        (b :: v).get (Fin.succ j) = v.get j := by rfl
        _ = L.get ⟨u.length+(j.val+1)+1, by
            simp only [L, List.length_cons, List.length_append, List.length_cons]
            omega⟩ := htail.symm
        _ = L.get (src (Fin.succ j)) := by
          congr 1
          exact Fin.ext hix.symm
  calc
    (b :: v).get p = L.get (src p) := hsrc
    _ = R.get (emb (src p)) := hemb (src p)
    _ = (R.drop (emb ib).val).get (f p) := by
      change R[(emb (src p)).val] = (R.drop (emb ib).val)[(f p).val]
      rw [List.getElem_drop]
      have hm : (emb ib).val ≤ (emb (src p)).val := by
        exact Fin.le_iff_val_le_val.mp (emb.monotone (Fin.le_iff_val_le_val.mpr
          (by change ib.val ≤ ib.val+p.val; exact Nat.le_add_right _ _)))
      have heq : (emb ib).val + (f p).val = (emb (src p)).val := by
        simp only [f]
        exact Nat.add_sub_of_le hm
      simp only [heq]

private theorem hAsingleTake :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    ∀ (k : ℕ),
    let root := List.ofFn (fun i : Fin (n + 3) => i)
    let R := root.rotate k
    ∀ (emb : Fin (a :: (u ++ b :: v)).length ↪o Fin ((List.ofFn fun (i : Fin (n + (3 : ℕ))) =>
        i).rotate k).length), ∀ (hsourceB : u.length+1 < L.length),
    let ia : Fin L.length := ⟨0, by simp [L]⟩
    let ib : Fin L.length := ⟨u.length+1, hsourceB⟩
    (R.get (emb ia) = a) → (((emb ia).val < (emb ib).val) → (([a] : List (Fin (n+3))).Sublist
        (R.take (emb ib).val))) := by
  classical
  intro n a b u v L k root R emb hsourceB ia ib haAtRoot hrootOrder
  let ip : Fin (R.take (emb ib).val).length := ⟨(emb ia).val, by
    rw [List.length_take]
    apply Nat.lt_min.mpr
    exact ⟨Fin.lt_def.mp hrootOrder, (emb ia).isLt⟩⟩
  apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
  let f : Fin 1 → Fin (R.take (emb ib).val).length := fun _ => ip
  have hf : StrictMono f := by
    intro x y hxy
    have : x.val < y.val := Fin.lt_def.mp hxy
    have : False := by omega
    exact this.elim
  refine ⟨OrderEmbedding.ofStrictMono f hf, ?_⟩
  intro ix
  have hx : ix = 0 := Fin.eq_zero ix
  rw [hx]
  change a = (R.take (emb ib).val).get ip
  rw [List.get_eq_getElem, List.getElem_take]
  change a = R.get (emb ia)
  exact haAtRoot.symm

private theorem hBsubAtB :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    let B := b :: (v ++ [a])
    ∀ (k : ℕ),
    let root := List.ofFn (fun i : Fin (n + 3) => i)
    let R := root.rotate k
    ∀ (emb : Fin (a :: (u ++ b :: v)).length ↪o Fin ((List.ofFn fun (i : Fin (n + (3 : ℕ))) =>
        i).rotate k).length), ∀ (hsourceB : u.length+1 < L.length),
    let ib : Fin L.length := ⟨u.length+1, hsourceB⟩
    ((b :: v).Sublist (R.drop (emb ib).val)) → ((([a] : List (Fin (n+3))).Sublist (R.take (emb
        ib).val)) → (B.Sublist (R.rotate (emb ib).val))) := by
  classical
  intro n a b u v L B k root R emb hsourceB ib hBVsubDrop hAsingleTake
  have hconcat : B.Sublist (R.drop (emb ib).val ++ R.take (emb ib).val) := by
    change (b :: v ++ [a]).Sublist _
    exact List.Sublist.append hBVsubDrop hAsingleTake
  rw [List.rotate_eq_drop_append_take (by exact (emb ib).isLt.le)]
  exact hconcat

private theorem hBsubRoot :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    let B := b :: (v ++ [a])
    ∀ (k : ℕ),
    let root := List.ofFn (fun i : Fin (n + 3) => i)
    let R := root.rotate k
    ∀ (emb : Fin (a :: (u ++ b :: v)).length ↪o Fin ((List.ofFn fun (i : Fin (n + (3 : ℕ))) =>
        i).rotate k).length), ∀ (hsourceB : u.length+1 < L.length),
    let ib : Fin L.length := ⟨u.length+1, hsourceB⟩
    (B.Sublist (R.rotate (emb ib).val)) → (∃ k : Nat, B.Sublist (root.rotate k)) := by
  classical
  intro n a b u v L B k root R emb hsourceB ib hBsubAtB
  refine ⟨k + (emb ib).val, ?_⟩
  simpa [R, root, List.rotate_rotate] using hBsubAtB

private theorem hvalA :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    ∀ (k : ℕ),
    let root := List.ofFn (fun i : Fin (n + 3) => i)
    let R := root.rotate k
    ∀ (emb : Fin (a :: (u ++ b :: v)).length ↪o Fin ((List.ofFn fun (i : Fin (n + (3 : ℕ))) =>
        i).rotate k).length), (∀ (j : Fin R.length), (R.get j).val = (j.val + k) % (n + 3)) → (
    let ia : Fin L.length := ⟨0, by simp [L]⟩
    (R.get (emb ia) = a) → (a.val = ((emb ia).val + k) % (n + 3))) := by
  classical
  intro n a b u v L k root R emb hRval ia haAtRoot
  rw [← haAtRoot]
  exact hRval (emb ia)

private theorem hvalB :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    ∀ (k : ℕ),
    let root := List.ofFn (fun i : Fin (n + 3) => i)
    let R := root.rotate k
    ∀ (emb : Fin (a :: (u ++ b :: v)).length ↪o Fin ((List.ofFn fun (i : Fin (n + (3 : ℕ))) =>
        i).rotate k).length), (∀ (j : Fin R.length), (R.get j).val = (j.val + k) % (n + 3)) → (∀
            (hsourceB : u.length+1 < L.length),
    let ib : Fin L.length := ⟨u.length+1, hsourceB⟩
    (R.get (emb ib) = b) → (b.val = ((emb ib).val + k) % (n + 3))) := by
  classical
  intro n a b u v L k root R emb hRval hsourceB ib hbAtRoot
  calc
    b.val = (R.get (emb ib)).val := congrArg Fin.val hbAtRoot.symm
    _ = ((emb ib).val + k) % (n + 3) := hRval (emb ib)

private theorem hrankB :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    ∀ (k : ℕ), ∀ (emb : Fin (a :: (u ++ b :: v)).length ↪o Fin ((List.ofFn fun (i : Fin (n + (3 :
        ℕ))) => i).rotate k).length), (∀ (m : Nat), ∀ (k : Nat), ∀ (p : Nat), ∀ (s : Nat), (0 <
        m) → ((p < m) → ((s < m) → ((p ≤ s) → ((((s+k)%m+m-((p+k)%m))%m) = s-p))))) → (∀
            (hsourceB : u.length+1 < L.length),
    let ia : Fin L.length := ⟨0, by simp [L]⟩
    let ib : Fin L.length := ⟨u.length+1, hsourceB⟩
    ((emb ia).val < (emb ib).val) → ((a.val = ((emb ia).val + k) % (n + 3)) → ((b.val = ((emb
        ib).val + k) % (n + 3)) → (((b.val + (n+3) - a.val) % (n+3)) =
      (emb ib).val - (emb ia).val)))) := by
  classical
  intro n a b u v L k emb hrankDiff hsourceB ia ib hrootOrder hvalA hvalB
  calc
    ((b.val + (n+3) - a.val) % (n+3)) =
        (((emb ib).val + k) % (n+3) + (n+3) -
          ((emb ia).val + k) % (n+3)) % (n+3) := by rw [hvalB, hvalA]
    _ = (emb ib).val - (emb ia).val := by
      apply hrankDiff (n+3) k (emb ia).val (emb ib).val
      · omega
      · have h := (emb ia).isLt
        simp [] at h
        omega
      · have h := (emb ib).isLt
        simp [] at h
        omega
      · exact hrootOrder.le

private theorem hrankB' :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    ∀ (k : ℕ), ∀ (emb : Fin (a :: (u ++ b :: v)).length ↪o Fin ((List.ofFn fun (i : Fin (n + (3 :
        ℕ))) => i).rotate k).length), ∀ (hsourceB : u.length+1 < L.length),
    let ia : Fin L.length := ⟨0, by simp [L]⟩
    let ib : Fin L.length := ⟨u.length+1, hsourceB⟩
    (((b.val + (n+3) - a.val) % (n+3)) = (emb ib).val - (emb ia).val) → (
    let rank := fun i : Fin (n+3) => (i.val + (n+3) - a.val) % (n+3)
    rank b = (emb ib).val - (emb ia).val) := by
  classical
  intro n a b u v L k emb hsourceB ia ib hrankB rank
  simpa [rank] using hrankB

private theorem hrankAt :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    ∀ (k : ℕ),
    let root := List.ofFn (fun i : Fin (n + 3) => i)
    let R := root.rotate k
    ∀ (emb : Fin (a :: (u ++ b :: v)).length ↪o Fin ((List.ofFn fun (i : Fin (n + (3 : ℕ))) =>
        i).rotate k).length), (∀ (ix : Fin (a :: (u ++ b :: v)).length), (a :: (u ++ b :: v)).get
        ix = ((List.ofFn fun (i : Fin (n + (3 : ℕ))) => i).rotate k).get ((emb : Fin (a :: (u ++
        b :: v)).length → Fin ((List.ofFn fun (i : Fin (n + (3 : ℕ))) => i).rotate k).length)
        ix)) → ((∀ (j : Fin R.length), (R.get j).val = (j.val + k) % (n + 3)) → ((∀ (m : Nat), ∀
            (k : Nat), ∀ (p : Nat), ∀ (s : Nat), (0 < m) → ((p < m) → ((s < m) → ((p ≤ s) →
        ((((s+k)%m+m-((p+k)%m))%m) = s-p))))) → ((u.length+1 < L.length) → (
    let ia : Fin L.length := ⟨0, by simp [L]⟩
    (a.val = ((emb ia).val + k) % (n + 3)) → (
    let rank := fun i : Fin (n+3) => (i.val + (n+3) - a.val) % (n+3)
    ∀ (p : Fin L.length), (ia ≤ p) → (∀ (i : Fin (n+3)), (L.get p = i) → (rank i = (emb p).val -
        (emb ia).val))))))) := by
  classical
  intro n a b u v L k root R emb hemb hRval hrankDiff hsourceB ia hvalA rank p hp i hpi
  have hvalI : i.val = ((emb p).val + k) % (n+3) := by
    calc
      i.val = (R.get (emb p)).val := (congrArg Fin.val ((hemb p).symm.trans hpi)).symm
      _ = ((emb p).val+k)%(n+3) := hRval (emb p)
  calc
    rank i = (((emb p).val+k)%(n+3)+(n+3)-((emb ia).val+k)%(n+3))%(n+3) := by
      dsimp [rank]
      rw [hvalI, hvalA]
    _ = (emb p).val-(emb ia).val := by
      apply hrankDiff (n+3) k (emb ia).val (emb p).val
      · omega
      · have h := (emb ia).isLt
        simp [] at h
        omega
      · have h := (emb p).isLt
        simp [] at h
        omega
      · exact emb.monotone hp

private theorem hrankU :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))), (0 < v.length) → (
    let L := a :: (u ++ b :: v)
    ∀ (k : ℕ), ∀ (emb : Fin (a :: (u ++ b :: v)).length ↪o Fin ((List.ofFn fun (i : Fin (n + (3 :
        ℕ))) => i).rotate k).length), ∀ (hsourceB : u.length+1 < L.length),
    let ia : Fin L.length := ⟨0, by simp [L]⟩
    let ib : Fin L.length := ⟨u.length+1, hsourceB⟩
    ((emb ia).val < (emb ib).val) → (
    let rank := fun i : Fin (n+3) => (i.val + (n+3) - a.val) % (n+3)
    (rank b = (emb ib).val - (emb ia).val) → ((∀ (p : Fin L.length), (ia ≤ p) → (∀ (i : Fin
        (n+3)), (L.get p = i) → (rank i = (emb p).val - (emb ia).val))) → (∀ (i : Fin (n+3)), (i
        ∈ u) → (0 < rank i ∧ rank i < rank b))))) := by
  classical
  intro n a b u v hv L k emb hsourceB ia ib hrootOrder rank hrankB' hrankAt i hi
  obtain ⟨j, hj, hji⟩ := List.getElem_of_mem hi
  have hpBound : j+1 < L.length := by simp [L]; omega
  let p : Fin L.length := ⟨j+1, hpBound⟩
  have hpi : L.get p = i := by
    rw [List.get_eq_getElem]
    change (a :: (u ++ b :: v))[j+1] = i
    rw [List.getElem_cons_succ, List.getElem_append_left hj, hji]
  have hpos : ia < p := by
    apply Fin.lt_def.mpr
    simp [ia, p]
  have hposB : p < ib := by
    apply Fin.lt_def.mpr
    simp [ib, p]
    omega
  have hr := hrankAt p hpos.le i hpi
  constructor
  · rw [hr]
    have he : (emb ia).val < (emb p).val := emb.lt_iff_lt.mpr hpos
    omega
  · rw [hr, hrankB']
    have he1 : (emb ia).val < (emb p).val := emb.lt_iff_lt.mpr hpos
    have he2 : (emb p).val < (emb ib).val := emb.lt_iff_lt.mpr hposB
    omega

private theorem hrankV :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    ∀ (k : ℕ), ∀ (emb : Fin (a :: (u ++ b :: v)).length ↪o Fin ((List.ofFn fun (i : Fin (n + (3 :
        ℕ))) => i).rotate k).length), ∀ (hsourceB : u.length+1 < L.length),
    let ia : Fin L.length := ⟨0, by simp [L]⟩
    let ib : Fin L.length := ⟨u.length+1, hsourceB⟩
    ((emb ia).val < (emb ib).val) → (
    let rank := fun i : Fin (n+3) => (i.val + (n+3) - a.val) % (n+3)
    (rank b = (emb ib).val - (emb ia).val) → ((∀ (p : Fin L.length), (ia ≤ p) → (∀ (i : Fin
        (n+3)), (L.get p = i) → (rank i = (emb p).val - (emb ia).val))) → (∀ (i : Fin (n+3)), (i
        ∈ v) → (rank b < rank i)))) := by
  classical
  intro n a b u v L k emb hsourceB ia ib hrootOrder rank hrankB' hrankAt i hi
  obtain ⟨j, hj, hji⟩ := List.getElem_of_mem hi
  have hpBound : u.length+1+j+1 < L.length := by simp [L]; omega
  let p : Fin L.length := ⟨u.length+1+j+1, hpBound⟩
  have hpi : L.get p = i := by
    rw [List.get_eq_getElem]
    change (a :: (u ++ b :: v))[u.length+1+j+1] = i
    rw [List.getElem_cons_succ]
    rw [List.getElem_append_right (by omega)]
    have hidx : u.length+1+j-u.length = j+1 := by omega
    simpa [hidx] using hji
  have hposB : ib < p := by
    apply Fin.lt_def.mpr
    dsimp [ib, p]
    omega
  have hiaB : ia ≤ ib := by
    apply Fin.le_iff_val_le_val.mpr
    simp [ia, ib]
  have hr := hrankAt p (hiaB.trans hposB.le) i hpi
  rw [hr, hrankB']
  have he1 : (emb ia).val < (emb ib).val := hrootOrder
  have he2 : (emb ib).val < (emb p).val := emb.lt_iff_lt.mpr hposB
  omega

private theorem hrankFormula :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    ∀ (k : ℕ),
    let root := List.ofFn (fun i : Fin (n + 3) => i)
    let R := root.rotate k
    ∀ (emb : Fin (a :: (u ++ b :: v)).length ↪o Fin ((List.ofFn fun (i : Fin (n + (3 : ℕ))) =>
        i).rotate k).length), (u.length+1 < L.length) → (
    let ia : Fin L.length := ⟨0, by simp [L]⟩
    (R.get (emb ia) = a) → ((a.val = ((emb ia).val + k) % (n + 3)) → (
    let rank := fun i : Fin (n+3) => (i.val + (n+3) - a.val) % (n+3)
    ∀ (i : Fin (n+3)), rank i =
      if a.val ≤ i.val then i.val-a.val else n+3-a.val+i.val))) := by
  classical
  intro n a b u v L k root R emb hsourceB ia haAtRoot hvalA rank i
  by_cases h : a.val ≤ i.val
  · have heq : i.val+(n+3)-a.val = (n+3)+(i.val-a.val) := by omega
    simp [rank, h, heq, Nat.mod_eq_of_lt (by omega : i.val-a.val < n+3)]
  · have heq : i.val+(n+3)-a.val = n+3-a.val+i.val := by omega
    simp [rank, h, heq, Nat.mod_eq_of_lt (by omega : n+3-a.val+i.val < n+3)]

private theorem hrankHi :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)),
    let rank := fun i : Fin (n+3) => (i.val + (n+3) - a.val) % (n+3)
    (∀ (i : Fin (n+3)), rank i = if a.val ≤ i.val then i.val-a.val else n+3-a.val+i.val) → (∀ (i
        : Fin (n+3)), (a.val ≤ i.val) → (rank i = i.val-a.val)) := by
  classical
  intro n a rank hrankFormula i h
  rw [hrankFormula i, ite_eq_left h]

private theorem hrankLo :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)),
    let rank := fun i : Fin (n+3) => (i.val + (n+3) - a.val) % (n+3)
    (∀ (i : Fin (n+3)), rank i = if a.val ≤ i.val then i.val-a.val else n+3-a.val+i.val) → (∀ (i
        : Fin (n+3)), (¬ a.val ≤ i.val) → (rank i = n+3-a.val+i.val)) := by
  classical
  intro n a rank hrankFormula i h
  rw [hrankFormula i, ite_eq_right h]

private theorem hAsubRoot :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    let A := a :: (u ++ [b])
    (A.Sublist L) → (∀ (k : ℕ), ((a :: (u ++ b :: v)).Sublist ((List.ofFn fun (i : Fin (n + (3 :
        ℕ))) => i).rotate k)) → (∃ k : Nat, A.Sublist
      ((List.ofFn (fun i : Fin (n + 3) => i)).rotate k))) := by
  classical
  intro n a b u v L A hAsubL k hLrot
  exact ⟨k, hAsubL.trans hLrot⟩

private theorem hdet :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), (∀ i, q i = ((i.val : Real), (i.val : Real) ^
        2)) → (∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)),
    let D := fun z => P3381T1TriangleDeterminant ![q a, q b, z]
    ∀ (c : Fin (n + 3)), D (q c) = ((b.val : Real) - a.val) *
        ((c.val : Real) - a.val) * ((c.val : Real) - b.val)) := by
  classical
  intro n q hq a b D c
  simp [D, P3381T1TriangleDeterminant, hq]
  ring

private theorem hDform :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), (∀ i, q i = ((i.val : Real), (i.val : Real) ^
        2)) → (∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)),
    let D := fun z => P3381T1TriangleDeterminant ![q a, q b, z]
    ∀ (z : Real × Real), D z = ((b.val : Real) - a.val) *
        (z.2 - ((a.val : Real)+(b.val : Real))*z.1 + a.val*b.val)) := by
  classical
  intro n q hq a b D z
  simp [D, P3381T1TriangleDeterminant, hq]
  ring

private theorem hTaConv :
    ∀ (n : Nat), ∀ (c : Fin (n+3)), Convex Real {z : Real × Real | 0 ≤ z.2 - 2*(c.val : Real)*z.1
        + (c.val : Real)^2} := by
  classical
  intro n c
  rw [convex_iff_div]
  intro x hx y hy r s hr hs hrs
  change 0 ≤ x.2 - 2*(c.val : Real)*x.1 + (c.val : Real)^2 at hx
  change 0 ≤ y.2 - 2*(c.val : Real)*y.1 + (c.val : Real)^2 at hy
  change 0 ≤ (((r/(r+s)) • x + (s/(r+s)) • y).2 -
    2*(c.val : Real)*((r/(r+s)) • x + (s/(r+s)) • y).1 + (c.val : Real)^2)
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
  have hw : r/(r+s)+s/(r+s)=1 := by rw [← add_div, div_self hrs.ne']
  have hlin : r/(r+s)*x.2+s/(r+s)*y.2 -
      2*(c.val : Real)*(r/(r+s)*x.1+s/(r+s)*y.1)+(c.val : Real)^2 =
      r/(r+s)*(x.2-2*(c.val : Real)*x.1+(c.val : Real)^2) +
        s/(r+s)*(y.2-2*(c.val : Real)*y.1+(c.val : Real)^2) := by
    calc
      _ = r/(r+s)*(x.2-2*(c.val : Real)*x.1+(c.val : Real)^2) +
          s/(r+s)*(y.2-2*(c.val : Real)*y.1+(c.val : Real)^2) +
          (c.val : Real)^2*(1-(r/(r+s)+s/(r+s))) := by ring
      _ = _ := by rw [hw]; ring
  rw [hlin]
  exact add_nonneg (mul_nonneg (div_nonneg hr hrs.le) hx)
    (mul_nonneg (div_nonneg hs hrs.le) hy)

private theorem hTaV :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), (∀ i, q i = ((i.val : Real), (i.val : Real) ^
        2)) → (∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v : List
        (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    q '' {i | i ∈ L} ⊆
      {z : Real × Real | 0 ≤ z.2 - 2*(a.val : Real)*z.1 + (a.val : Real)^2}) := by
  classical
  intro n q hq a b u v L
  rintro z ⟨i, hi, rfl⟩
  change 0 ≤ (q i).2 - 2*(a.val : Real)*(q i).1 + (a.val : Real)^2
  rw [hq i]
  have hsquare : 0 ≤ ((i.val : Real)-(a.val : Real))^2 := sq_nonneg _
  nlinarith [hsquare]

private theorem hTbV :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), (∀ i, q i = ((i.val : Real), (i.val : Real) ^
        2)) → (∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v : List
        (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    q '' {i | i ∈ L} ⊆
      {z : Real × Real | 0 ≤ z.2 - 2*(b.val : Real)*z.1 + (b.val : Real)^2}) := by
  classical
  intro n q hq a b u v L
  rintro z ⟨i, hi, rfl⟩
  change 0 ≤ (q i).2 - 2*(b.val : Real)*(q i).1 + (b.val : Real)^2
  rw [hq i]
  have hsquare : 0 ≤ ((i.val : Real)-(b.val : Real))^2 := sq_nonneg _
  nlinarith [hsquare]

private theorem hTaH :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀
        (u : List (Fin (n + 3))), ∀ (v : List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    let H := convexHull Real (q '' {i | i ∈ L})
    (∀ (c : Fin (n+3)), Convex Real {z : Real × Real | 0 ≤ z.2 - 2*(c.val : Real)*z.1 + (c.val :
        Real)^2}) → ((q '' {i | i ∈ L} ⊆ {z : Real × Real | 0 ≤ z.2 - 2*(a.val : Real)*z.1 +
        (a.val : Real)^2}) → (H ⊆ {z : Real × Real | 0 ≤ z.2 - 2*(a.val : Real)*z.1 + (a.val :
        Real)^2})) := by
  classical
  intro n q a b u v L H hTaConv hTaV
  exact convexHull_min hTaV (hTaConv a)

private theorem hTbH :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀
        (u : List (Fin (n + 3))), ∀ (v : List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    let H := convexHull Real (q '' {i | i ∈ L})
    (∀ (c : Fin (n+3)), Convex Real {z : Real × Real | 0 ≤ z.2 - 2*(c.val : Real)*z.1 + (c.val :
        Real)^2}) → ((q '' {i | i ∈ L} ⊆ {z : Real × Real | 0 ≤ z.2 - 2*(b.val : Real)*z.1 +
        (b.val : Real)^2}) → (H ⊆ {z : Real × Real | 0 ≤ z.2 - 2*(b.val : Real)*z.1 + (b.val :
        Real)^2})) := by
  classical
  intro n q a b u v L H hTaConv hTbV
  exact convexHull_min hTbV (hTaConv b)

private theorem haH :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀
        (u : List (Fin (n + 3))), ∀ (v : List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    let H := convexHull Real (q '' {i | i ∈ L})
    q a ∈ H := by
  classical
  intro n q a b u v L H
  exact subset_convexHull Real _ ⟨a, by simp [L]⟩

private theorem hbH :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀
        (u : List (Fin (n + 3))), ∀ (v : List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    let H := convexHull Real (q '' {i | i ∈ L})
    q b ∈ H := by
  classical
  intro n q a b u v L H
  exact subset_convexHull Real _ ⟨b, by simp [L]⟩

private theorem hsegH :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀
        (u : List (Fin (n + 3))), ∀ (v : List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    let H := convexHull Real (q '' {i | i ∈ L})
    (q a ∈ H) → ((q b ∈ H) → (segment Real (q a) (q b) ⊆ H)) := by
  classical
  intro n q a b u v L H haH hbH
  exact (convex_convexHull Real (q '' {i | i ∈ L})).segment_subset haH hbH

private theorem hneR :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), (a ≠ b) → ((b.val : Real)-(a.val :
        Real) ≠ 0) := by
  classical
  intro n a b hne he
  apply hne
  exact Fin.ext (by exact_mod_cast (sub_eq_zero.mp he).symm)

private theorem hFfromD :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)),
    let D := fun z => P3381T1TriangleDeterminant ![q a, q b, z]
    (∀ (z : Real × Real), D z = ((b.val : Real) - a.val) * (z.2 - ((a.val : Real)+(b.val :
        Real))*z.1 + a.val*b.val)) → (
    let F := fun z : Real × Real => z.2 -
      ((a.val : Real)+(b.val : Real))*z.1 + (a.val : Real)*(b.val : Real)
    ((b.val : Real)-(a.val : Real) ≠ 0) → (∀ (z : Real × Real), (D z = 0) → (F z = 0))) := by
  classical
  intro n q a b D hDform F hneR z hDz
  rw [hDform] at hDz
  dsimp [F]
  exact (mul_eq_zero.mp hDz).resolve_left hneR

private theorem hTaLine :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)),
    let F := fun z : Real × Real => z.2 -
      ((a.val : Real)+(b.val : Real))*z.1 + (a.val : Real)*(b.val : Real)
    ∀ (z : Real × Real), (F z = 0) → (z.2 - 2*(a.val : Real)*z.1 + (a.val : Real)^2 =
        ((b.val : Real)-(a.val : Real))*(z.1-(a.val : Real))) := by
  classical
  intro n a b F z hf
  dsimp [F] at hf
  nlinarith

private theorem hTbLine :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)),
    let F := fun z : Real × Real => z.2 -
      ((a.val : Real)+(b.val : Real))*z.1 + (a.val : Real)*(b.val : Real)
    ∀ (z : Real × Real), (F z = 0) → (z.2 - 2*(b.val : Real)*z.1 + (b.val : Real)^2 =
        ((a.val : Real)-(b.val : Real))*(z.1-(b.val : Real))) := by
  classical
  intro n a b F z hf
  dsimp [F] at hf
  nlinarith

private theorem chordMemberInc :
    ∀ (A : Real), ∀ (B : Real), ∀ (X : Real), ∀ (Y : Real), (A < B) → ((Y-(A+B)*X+A*B=0) → ((A ≤
        X) → ((X ≤ B) → ((X,Y) ∈ segment Real (A,A^2) (B,B^2))))) := by
  classical
  intro A B X Y hab hF hAX hXB
  rw [segment_eq_image_lineMap]
  rw [Set.mem_image]
  let t := (X-A)/(B-A)
  refine ⟨t, ?_, ?_⟩
  · constructor
    · dsimp [t]
      exact div_nonneg (sub_nonneg.mpr hAX) (sub_nonneg.mpr hab.le)
    · dsimp [t]
      rw [div_le_one (sub_pos.mpr hab)]
      linarith
  · rw [AffineMap.lineMap_apply_module]
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
    · dsimp [t]
      field_simp [ne_of_gt (sub_pos.mpr hab)]
      ring
    · dsimp [t]
      field_simp [ne_of_gt (sub_pos.mpr hab)]
      nlinarith [hF]

private theorem hsegD :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), (∀ i, q i = ((i.val : Real), (i.val : Real) ^
        2)) → (∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)),
    let D := fun z => P3381T1TriangleDeterminant ![q a, q b, z]
    (∀ (z : Real × Real), D z = ((b.val : Real) - a.val) * (z.2 - ((a.val : Real)+(b.val :
        Real))*z.1 + a.val*b.val)) → (segment Real (q a) (q b) ⊆ {z | D z = 0})) := by
  classical
  intro n q hq a b D hDform z hz
  rw [segment_eq_image_lineMap] at hz
  rw [Set.mem_image] at hz
  obtain ⟨t, ht, hzt⟩ := hz
  change D z = 0
  rw [← hzt, hDform, AffineMap.lineMap_apply_module]
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
  rw [hq a, hq b]
  simp only []
  ring

private theorem hzeroLine :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), (∀ i, q i = ((i.val : Real), (i.val : Real) ^
        2)) → (∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v : List
        (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    let H := convexHull Real (q '' {i | i ∈ L})
    (a ≠ b) → (
    let D := fun z => P3381T1TriangleDeterminant ![q a, q b, z]
    (H ⊆ {z : Real × Real | 0 ≤ z.2 - 2*(a.val : Real)*z.1 + (a.val : Real)^2}) → ((H ⊆ {z : Real
        × Real | 0 ≤ z.2 - 2*(b.val : Real)*z.1 + (b.val : Real)^2}) → ((segment Real (q a) (q b)
        ⊆ H) → (
    let F := fun z : Real × Real => z.2 -
      ((a.val : Real)+(b.val : Real))*z.1 + (a.val : Real)*(b.val : Real)
    (∀ (z : Real × Real), (D z = 0) → (F z = 0)) → ((∀ (z : Real × Real), (F z = 0) → (z.2 -
        2*(a.val : Real)*z.1 + (a.val : Real)^2 = ((b.val : Real)-(a.val : Real))*(z.1-(a.val :
        Real)))) → ((∀ (z : Real × Real), (F z = 0) → (z.2 - 2*(b.val : Real)*z.1 + (b.val :
        Real)^2 = ((a.val : Real)-(b.val : Real))*(z.1-(b.val : Real)))) → ((∀ (A : Real), ∀ (B :
            Real), ∀ (X : Real), ∀ (Y : Real), (A < B) → ((Y-(A+B)*X+A*B=0) → ((A ≤ X) → ((X ≤ B) →
        ((X,Y) ∈ segment Real (A,A^2) (B,B^2)))))) → ((segment Real (q a) (q b) ⊆ {z | D z = 0})
        → (H ∩ {z | D z = 0} = segment Real (q a) (q b))))))))))) := by
  classical
  intro n q hq a b u v L H hne D hTaH hTbH hsegH F hFfromD hTaLine hTbLine chordMemberInc hsegD
  ext z
  constructor
  · rintro ⟨hzH, hDz⟩
    have hf := hFfromD z hDz
    have hTa := hTaH hzH
    have hTb := hTbH hzH
    have hTa' : 0 ≤ z.2 - 2*(a.val : Real)*z.1 + (a.val : Real)^2 := hTa
    have hTb' : 0 ≤ z.2 - 2*(b.val : Real)*z.1 + (b.val : Real)^2 := hTb
    have hxy : (z.1,z.2) ∈ segment Real
        ((a.val : Real),(a.val : Real)^2) ((b.val : Real),(b.val : Real)^2) := by
      by_cases hab : a.val < b.val
      · have hAX : (a.val : Real) ≤ z.1 := by
          rw [hTaLine z hf] at hTa'
          have habR : (a.val : Real) < (b.val : Real) := by exact_mod_cast hab
          have hnonneg := (mul_nonneg_iff_of_pos_left (sub_pos.mpr habR)).mp hTa'
          linarith
        have hXB : z.1 ≤ (b.val : Real) := by
          rw [hTbLine z hf] at hTb'
          have habR : (a.val : Real) < (b.val : Real) := by exact_mod_cast hab
          have hpos : 0 < (b.val : Real)-(a.val : Real) := sub_pos.mpr habR
          have hnonneg : 0 ≤ ((b.val : Real)-(a.val : Real))*((b.val : Real)-z.1) := by
            rw [show ((b.val : Real)-(a.val : Real))*((b.val : Real)-z.1) =
              ((a.val : Real)-(b.val : Real))*(z.1-(b.val : Real)) by ring]
            exact hTb'
          have hx := (mul_nonneg_iff_of_pos_left hpos).mp hnonneg
          linarith
        exact chordMemberInc _ _ _ _ (by exact_mod_cast hab) hf hAX hXB
      · have hba : b.val < a.val := by
          rcases Nat.lt_trichotomy b.val a.val with hba | heq | hlt
          · exact hba
          · exact False.elim (hne (Fin.ext heq.symm))
          · exact (hab hlt).elim
        have hBX : (b.val : Real) ≤ z.1 := by
          rw [hTbLine z hf] at hTb'
          have hbaR : (b.val : Real) < (a.val : Real) := by exact_mod_cast hba
          have hnonneg := (mul_nonneg_iff_of_pos_left (sub_pos.mpr hbaR)).mp hTb'
          linarith
        have hXA : z.1 ≤ (a.val : Real) := by
          rw [hTaLine z hf] at hTa'
          have hbaR : (b.val : Real) < (a.val : Real) := by exact_mod_cast hba
          have hpos : 0 < (a.val : Real)-(b.val : Real) := sub_pos.mpr hbaR
          have hnonneg : 0 ≤ ((a.val : Real)-(b.val : Real))*((a.val : Real)-z.1) := by
            rw [show ((a.val : Real)-(b.val : Real))*((a.val : Real)-z.1) =
              ((b.val : Real)-(a.val : Real))*(z.1-(a.val : Real)) by ring]
            exact hTa'
          have hx := (mul_nonneg_iff_of_pos_left hpos).mp hnonneg
          linarith
        have hf' : z.2 - ((b.val : Real)+(a.val : Real))*z.1 +
            (b.val : Real)*(a.val : Real) = 0 := by
          rw [add_comm (b.val : Real) (a.val : Real), mul_comm (b.val : Real) (a.val : Real)]
          exact hf
        have hh := chordMemberInc (b.val : Real) (a.val : Real) z.1 z.2
          (by exact_mod_cast hba) hf' hBX hXA
        have hsym := segment_symm Real
          ((b.val : Real),(b.val : Real)^2) ((a.val : Real),(a.val : Real)^2)
        rw [hsym] at hh
        exact hh
    simpa only [hq a, hq b] using hxy
  · intro hz
    constructor
    · exact hsegH hz
    · exact hsegD hz

private theorem hBcyclic :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (v : List (Fin (n + 3))),
    let B := b :: (v ++ [a])
    let root := List.ofFn (fun i : Fin (n + 3) => i)
    (∃ k : Nat, B.Sublist (root.rotate k)) → (∃ k : Nat, B.Sublist
      ((List.ofFn (fun i : Fin (n+3) => i)).rotate k)) := by
  classical
  intro n a b v B root hBsubRoot
  simpa [root] using hBsubRoot

private theorem hDcombo :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)),
    let D := fun z => P3381T1TriangleDeterminant ![q a, q b, z]
    (∀ (z : Real × Real), D z = ((b.val : Real) - a.val) * (z.2 - ((a.val : Real)+(b.val :
        Real))*z.1 + a.val*b.val)) → (∀ (x : Real × Real), ∀ (y : Real × Real), ∀ (r : Real), ∀
            (s : Real), (r+s ≠ 0) → (D ((r/(r+s)) • x + (s/(r+s)) • y) =
        r/(r+s)*D x + s/(r+s)*D y)) := by
  classical
  intro n q a b D hDform x y r s hrs
  have hw : r/(r+s)+s/(r+s)=1 := by rw [← add_div, div_self hrs]
  calc
    D ((r/(r+s)) • x + (s/(r+s)) • y) =
        r/(r+s)*D x + s/(r+s)*D y +
          ((b.val : Real)-(a.val : Real))*(a.val : Real)*(b.val : Real)*
            (1-(r/(r+s)+s/(r+s))) := by
      rw [hDform, hDform x, hDform y]
      simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
      ring
    _ = r/(r+s)*D x + s/(r+s)*D y := by rw [hw]; ring

private theorem hDleConv :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)),
    let D := fun z => P3381T1TriangleDeterminant ![q a, q b, z]
    (∀ (x : Real × Real), ∀ (y : Real × Real), ∀ (r : Real), ∀ (s : Real), (r+s ≠ 0) → (D
        ((r/(r+s)) • x + (s/(r+s)) • y) = r/(r+s)*D x + s/(r+s)*D y)) → (Convex Real {z : Real ×
        Real | D z ≤ 0}) := by
  classical
  intro n q a b D hDcombo
  rw [convex_iff_div]
  intro x hx y hy r s hr hs hrs
  change D x ≤ 0 at hx
  change D y ≤ 0 at hy
  change D ((r/(r+s)) • x + (s/(r+s)) • y) ≤ 0
  rw [hDcombo x y r s hrs.ne']
  exact add_nonpos
    (mul_nonpos_of_nonneg_of_nonpos (div_nonneg hr hrs.le) hx)
    (mul_nonpos_of_nonneg_of_nonpos (div_nonneg hs hrs.le) hy)

private theorem hDgeConv :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)),
    let D := fun z => P3381T1TriangleDeterminant ![q a, q b, z]
    (∀ (x : Real × Real), ∀ (y : Real × Real), ∀ (r : Real), ∀ (s : Real), (r+s ≠ 0) → (D
        ((r/(r+s)) • x + (s/(r+s)) • y) = r/(r+s)*D x + s/(r+s)*D y)) → (Convex Real {z : Real ×
        Real | 0 ≤ D z}) := by
  classical
  intro n q a b D hDcombo
  rw [convex_iff_div]
  intro x hx y hy r s hr hs hrs
  change 0 ≤ D x at hx
  change 0 ≤ D y at hy
  change 0 ≤ D ((r/(r+s)) • x + (s/(r+s)) • y)
  rw [hDcombo x y r s hrs.ne']
  exact add_nonneg
    (mul_nonneg (div_nonneg hr hrs.le) hx)
    (mul_nonneg (div_nonneg hs hrs.le) hy)

private theorem hUneg :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀
        (u : List (Fin (n + 3))), (List (Fin (n + 3))) → ((a ≠ b) → (
    let rank := fun i : Fin (n+3) => (i.val + (n+3) - a.val) % (n+3)
    (∀ (i : Fin (n+3)), (i ∈ u) → (0 < rank i ∧ rank i < rank b)) → ((∀ (i : Fin (n+3)), (a.val ≤
        i.val) → (rank i = i.val-a.val)) → ((∀ (i : Fin (n+3)), (¬ a.val ≤ i.val) → (rank i =
        n+3-a.val+i.val)) → (
    let D := fun z => P3381T1TriangleDeterminant ![q a, q b, z]
    (∀ (c : Fin (n + 3)), D (q c) = ((b.val : Real) - a.val) * ((c.val : Real) - a.val) * ((c.val
        : Real) - b.val)) → (∀ i ∈ u, D (q i) < 0)))))) := by
  classical
  intro n q a b u v hne rank hrankU hrankHi hrankLo D hdet i hi
  have hru := hrankU i hi
  by_cases hab : a.val < b.val
  · have hrb := hrankHi b hab.le
    have hAi : a.val ≤ i.val := by
      by_contra h
      have hform := hrankLo i h
      omega
    have hia : a.val < i.val := by
      have hform := hrankHi i hAi
      omega
    have hib : i.val < b.val := by
      have hform := hrankHi i hAi
      omega
    have habR : (a.val : Real) < (b.val : Real) := by exact_mod_cast hab
    have hiaR : (a.val : Real) < (i.val : Real) := by exact_mod_cast hia
    have hibR : (i.val : Real) < (b.val : Real) := by exact_mod_cast hib
    have hcoeff : 0 < (b.val : Real)-(a.val : Real) := sub_pos.mpr habR
    have hleft : 0 < ((b.val : Real)-(a.val : Real)) * ((i.val : Real)-(a.val : Real)) :=
      mul_pos hcoeff (sub_pos.mpr hiaR)
    have hright : (i.val : Real)-(b.val : Real) < 0 := sub_neg.mpr hibR
    change D (q i) < 0
    rw [hdet i]
    exact mul_neg_of_pos_of_neg hleft hright
  · have hba : b.val < a.val := by
      rcases Nat.lt_trichotomy b.val a.val with hba | heq | hlt
      · exact hba
      · exact False.elim (hne (Fin.ext heq.symm))
      · exact (hab hlt).elim
    by_cases hAi : a.val ≤ i.val
    · have hform := hrankHi i hAi
      have hbform := hrankLo b (not_le_of_gt hba)
      have hia : a.val < i.val := by omega
      have hib : b.val < i.val := by omega
      have hbaR : (b.val : Real) < (a.val : Real) := by exact_mod_cast hba
      have hiaR : (a.val : Real) < (i.val : Real) := by exact_mod_cast hia
      have hibR : (b.val : Real) < (i.val : Real) := by exact_mod_cast hib
      have hcoeff : (b.val : Real)-(a.val : Real) < 0 := sub_neg.mpr hbaR
      have hleft : ((b.val : Real)-(a.val : Real)) * ((i.val : Real)-(a.val : Real)) < 0 :=
        mul_neg_of_neg_of_pos hcoeff (sub_pos.mpr hiaR)
      have hright : 0 < (i.val : Real)-(b.val : Real) := sub_pos.mpr hibR
      change D (q i) < 0
      rw [hdet i]
      exact mul_neg_of_neg_of_pos hleft hright
    · have hform := hrankLo i hAi
      have hbform := hrankLo b (not_le_of_gt hba)
      have hib : i.val < b.val := by omega
      have hbaR : (b.val : Real) < (a.val : Real) := by exact_mod_cast hba
      have hiaNat : i.val < a.val := by omega
      have hiaR : (i.val : Real) < (a.val : Real) := by exact_mod_cast hiaNat
      have hibR : (i.val : Real) < (b.val : Real) := by exact_mod_cast hib
      have hcoeff : (b.val : Real)-(a.val : Real) < 0 := sub_neg.mpr hbaR
      have hiaReal : (i.val : Real)-(a.val : Real) < 0 := sub_neg.mpr hiaR
      have hleft : 0 < ((b.val : Real)-(a.val : Real)) * ((i.val : Real)-(a.val : Real)) :=
        mul_pos_of_neg_of_neg hcoeff hiaReal
      have hright : (i.val : Real)-(b.val : Real) < 0 := sub_neg.mpr hibR
      change D (q i) < 0
      rw [hdet i]
      exact mul_neg_of_pos_of_neg hleft hright

private theorem hVpos :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀
        (v : List (Fin (n + 3))), (a ≠ b) → (
    let rank := fun i : Fin (n+3) => (i.val + (n+3) - a.val) % (n+3)
    (∀ (i : Fin (n+3)), (i ∈ v) → (rank b < rank i)) → ((∀ (i : Fin (n+3)), (a.val ≤ i.val) →
        (rank i = i.val-a.val)) → ((∀ (i : Fin (n+3)), (¬ a.val ≤ i.val) → (rank i =
        n+3-a.val+i.val)) → (
    let D := fun z => P3381T1TriangleDeterminant ![q a, q b, z]
    (∀ (c : Fin (n + 3)), D (q c) = ((b.val : Real) - a.val) * ((c.val : Real) - a.val) * ((c.val
        : Real) - b.val)) → (∀ i ∈ v, 0 < D (q i)))))) := by
  classical
  intro n q a b v hne rank hrankV hrankHi hrankLo D hdet i hi
  have hrv := hrankV i hi
  by_cases hab : a.val < b.val
  · by_cases hAi : a.val ≤ i.val
    · have hformI := hrankHi i hAi
      have hformB := hrankHi b hab.le
      have hib : b.val < i.val := by omega
      have habR : (a.val : Real) < (b.val : Real) := by exact_mod_cast hab
      have hiaR : (a.val : Real) < (i.val : Real) := by exact_mod_cast (by omega : a.val < i.val)
      have hibR : (b.val : Real) < (i.val : Real) := by exact_mod_cast hib
      have hcoeff : 0 < (b.val : Real)-(a.val : Real) := sub_pos.mpr habR
      have hleft : 0 < ((b.val : Real)-(a.val : Real))*((i.val : Real)-(a.val : Real)) :=
        mul_pos hcoeff (sub_pos.mpr hiaR)
      have hright : 0 < (i.val : Real)-(b.val : Real) := sub_pos.mpr hibR
      change D (q i) > 0
      rw [hdet i]
      exact mul_pos hleft hright
    · have hia : i.val < a.val := by omega
      have habR : (a.val : Real) < (b.val : Real) := by exact_mod_cast hab
      have hiaR : (i.val : Real) < (a.val : Real) := by exact_mod_cast hia
      have hibR : (i.val : Real) < (b.val : Real) := by exact_mod_cast (by omega : i.val < b.val)
      have hcoeff : 0 < (b.val : Real)-(a.val : Real) := sub_pos.mpr habR
      have hleft : 0 < ((i.val : Real)-(a.val : Real))*((i.val : Real)-(b.val : Real)) :=
        mul_pos_of_neg_of_neg (sub_neg.mpr hiaR) (sub_neg.mpr hibR)
      change D (q i) > 0
      rw [hdet i]
      rw [mul_assoc]
      exact mul_pos hcoeff hleft
  · have hba : b.val < a.val := by
      have hneval : a.val ≠ b.val := fun e => hne (Fin.ext e)
      omega
    have hAi : ¬ a.val ≤ i.val := by
      intro h
      have hformI := hrankHi i h
      have hformB := hrankLo b (not_le_of_gt hba)
      have hiBound : i.val < n+3 := i.isLt
      omega
    have hformI := hrankLo i hAi
    have hformB := hrankLo b (not_le_of_gt hba)
    have hib : b.val < i.val := by omega
    have hia : i.val < a.val := by omega
    have hbaR : (b.val : Real) < (a.val : Real) := by exact_mod_cast hba
    have hiaR : (i.val : Real) < (a.val : Real) := by exact_mod_cast hia
    have hibR : (b.val : Real) < (i.val : Real) := by exact_mod_cast hib
    have hleft : 0 < ((b.val : Real)-(a.val : Real))*((i.val : Real)-(a.val : Real)) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hbaR) (sub_neg.mpr hiaR)
    have hright : 0 < (i.val : Real)-(b.val : Real) := sub_pos.mpr hibR
    change D (q i) > 0
    rw [hdet i]
    exact mul_pos hleft hright

private theorem hAidx :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    let A := a :: (u ++ [b])
    (A.Sublist L) → ({i | i ∈ A} ⊆ {i | i ∈ L}) := by
  classical
  intro n a b u v L A hAsubL
  exact hAsubL.subset

private theorem hAinH :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀
        (u : List (Fin (n + 3))), ∀ (v : List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    let A := a :: (u ++ [b])
    let H := convexHull Real (q '' {i | i ∈ L})
    ({i | i ∈ A} ⊆ {i | i ∈ L}) → (q '' {i | i ∈ A} ⊆ H) := by
  classical
  intro n q a b u v L A H hAidx
  exact (Set.image_mono hAidx).trans (subset_convexHull Real _)

private theorem hAhalf :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀
        (u : List (Fin (n + 3))),
    let A := a :: (u ++ [b])
    let D := fun z => P3381T1TriangleDeterminant ![q a, q b, z]
    (∀ (c : Fin (n + 3)), D (q c) = ((b.val : Real) - a.val) * ((c.val : Real) - a.val) * ((c.val
        : Real) - b.val)) → ((∀ i ∈ u, D (q i) < 0) → (q '' {i | i ∈ A} ⊆ {z | D z ≤ 0})) := by
  classical
  intro n q a b u A D hdet hUneg
  rintro z ⟨i, hi, rfl⟩
  change D (q i) ≤ 0
  simp only [A, List.mem_cons, List.mem_append] at hi
  rcases hi with hia | hiu | hib | hnil
  · subst i
    rw [hdet a]
    simp
  · exact le_of_lt (hUneg i hiu)
  · subst i
    rw [hdet b]
    simp
  · simp at hnil

private theorem hAcut :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀
        (u : List (Fin (n + 3))), ∀ (v : List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    let A := a :: (u ++ [b])
    let H := convexHull Real (q '' {i | i ∈ L})
    let HA := convexHull Real (q '' {i | i ∈ A})
    let D := fun z => P3381T1TriangleDeterminant ![q a, q b, z]
    (Convex Real {z : Real × Real | D z ≤ 0}) → ((q '' {i | i ∈ A} ⊆ H) → ((q '' {i | i ∈ A} ⊆ {z
        | D z ≤ 0}) → (HA ⊆ H ∩ {z | D z ≤ 0}))) := by
  classical
  intro n q a b u v L A H HA D hDleConv hAinH hAhalf
  exact convexHull_min (Set.subset_inter hAinH hAhalf)
      (Convex.inter (convex_convexHull Real _) hDleConv)

private theorem hBidx :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    let B := b :: (v ++ [a])
    {i | i ∈ B} ⊆ {i | i ∈ L} := by
  classical
  intro n a b u v L B i hi
  simp only [B, List.mem_cons, List.mem_append] at hi
  rcases hi with hib | hiv | hia | hnil
  · subst i
    simp [L]
  · change i ∈ a :: (u ++ b :: v)
    simp only [List.mem_cons, List.mem_append]
    exact Or.inr (Or.inr (Or.inr hiv))
  · subst i
    simp [L]
  · simp at hnil

private theorem hBinH :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀
        (u : List (Fin (n + 3))), ∀ (v : List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    let B := b :: (v ++ [a])
    let H := convexHull Real (q '' {i | i ∈ L})
    ({i | i ∈ B} ⊆ {i | i ∈ L}) → (q '' {i | i ∈ B} ⊆ H) := by
  classical
  intro n q a b u v L B H hBidx
  exact (Set.image_mono hBidx).trans (subset_convexHull Real _)

private theorem hBhalf :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀
        (v : List (Fin (n + 3))),
    let B := b :: (v ++ [a])
    let D := fun z => P3381T1TriangleDeterminant ![q a, q b, z]
    (∀ (c : Fin (n + 3)), D (q c) = ((b.val : Real) - a.val) * ((c.val : Real) - a.val) * ((c.val
        : Real) - b.val)) → ((∀ i ∈ v, 0 < D (q i)) → (q '' {i | i ∈ B} ⊆ {z | 0 ≤ D z})) := by
  classical
  intro n q a b v B D hdet hVpos
  rintro z ⟨i, hi, rfl⟩
  change 0 ≤ D (q i)
  simp only [B, List.mem_cons, List.mem_append] at hi
  rcases hi with hib | hiv | hia | hnil
  · subst i
    rw [hdet b]
    simp
  · exact le_of_lt (hVpos i hiv)
  · subst i
    rw [hdet a]
    simp
  · simp at hnil

private theorem hBcut :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀
        (u : List (Fin (n + 3))), ∀ (v : List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    let B := b :: (v ++ [a])
    let H := convexHull Real (q '' {i | i ∈ L})
    let HB := convexHull Real (q '' {i | i ∈ B})
    let D := fun z => P3381T1TriangleDeterminant ![q a, q b, z]
    (Convex Real {z : Real × Real | 0 ≤ D z}) → ((q '' {i | i ∈ B} ⊆ H) → ((q '' {i | i ∈ B} ⊆ {z
        | 0 ≤ D z}) → (HB ⊆ H ∩ {z | 0 ≤ D z}))) := by
  classical
  intro n q a b u v L B H HB D hDgeConv hBinH hBhalf
  exact convexHull_min (Set.subset_inter hBinH hBhalf)
      (Convex.inter (convex_convexHull Real _) hDgeConv)

private theorem hIndexUnion :
    ∀ (n : Nat), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (u : List (Fin (n + 3))), ∀ (v :
        List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    let A := a :: (u ++ [b])
    let B := b :: (v ++ [a])
    {i | i ∈ L} = {i | i ∈ A} ∪ {i | i ∈ B} := by
  classical
  intro n a b u v L A B
  ext i
  simp only [Set.mem_union, L, A, B, List.mem_cons, List.mem_append,
    ]
  simp only [List.not_mem_nil, or_false]
  constructor
  · rintro (ha | hu | hb | hv)
    · exact Or.inl (Or.inl ha)
    · exact Or.inl (Or.inr (Or.inl hu))
    · exact Or.inl (Or.inr (Or.inr hb))
    · exact Or.inr (Or.inr (Or.inl hv))
  · rintro (hA | hB)
    · rcases hA with ha | hu | hb
      · exact Or.inl ha
      · exact Or.inr (Or.inl hu)
      · exact Or.inr (Or.inr (Or.inl hb))
    · rcases hB with hb | hv | ha
      · exact Or.inr (Or.inr (Or.inl hb))
      · exact Or.inr (Or.inr (Or.inr hv))
      · exact Or.inl ha

private theorem hImageUnion :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀
        (u : List (Fin (n + 3))), ∀ (v : List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    let A := a :: (u ++ [b])
    let B := b :: (v ++ [a])
    ({i | i ∈ L} = {i | i ∈ A} ∪ {i | i ∈ B}) → (q '' {i | i ∈ L} =
      (q '' {i | i ∈ A}) ∪ (q '' {i | i ∈ B})) := by
  classical
  intro n q a b u v L A B hIndexUnion
  rw [hIndexUnion, Set.image_union]

private theorem hSA :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀
        (u : List (Fin (n + 3))),
    let A := a :: (u ++ [b])
    (q '' {i | i ∈ A}).Nonempty := by
  classical
  intro n q a b u A
  exact ⟨q a, ⟨a, by simp [A], rfl⟩⟩

private theorem hSB :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀
        (v : List (Fin (n + 3))),
    let B := b :: (v ++ [a])
    (q '' {i | i ∈ B}).Nonempty := by
  classical
  intro n q a b v B
  exact ⟨q b, ⟨b, by simp [B], rfl⟩⟩

private theorem hHjoin :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀
        (u : List (Fin (n + 3))), ∀ (v : List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    let A := a :: (u ++ [b])
    let B := b :: (v ++ [a])
    let H := convexHull Real (q '' {i | i ∈ L})
    let HA := convexHull Real (q '' {i | i ∈ A})
    let HB := convexHull Real (q '' {i | i ∈ B})
    (q '' {i | i ∈ L} = (q '' {i | i ∈ A}) ∪ (q '' {i | i ∈ B})) → (((q '' {i | i ∈ A}).Nonempty)
        → (((q '' {i | i ∈ B}).Nonempty) → (H = convexJoin Real HA HB))) := by
  classical
  intro n q a b u v L A B H HA HB hImageUnion hSA hSB
  change convexHull Real (q '' {i | i ∈ L}) = _
  rw [hImageUnion]
  exact convexHull_union hSA hSB

private theorem hchordA :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀
        (u : List (Fin (n + 3))),
    let A := a :: (u ++ [b])
    let HA := convexHull Real (q '' {i | i ∈ A})
    segment Real (q a) (q b) ⊆ HA := by
  classical
  intro n q a b u A HA
  apply segment_subset_convexHull
  · exact ⟨a, by simp [A], rfl⟩
  · exact ⟨b, by simp [A], rfl⟩

private theorem hchordB :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀
        (v : List (Fin (n + 3))),
    let B := b :: (v ++ [a])
    let HB := convexHull Real (q '' {i | i ∈ B})
    segment Real (q a) (q b) ⊆ HB := by
  classical
  intro n q a b v B HB
  apply segment_subset_convexHull
  · exact ⟨a, by simp [B], rfl⟩
  · exact ⟨b, by simp [B], rfl⟩

private theorem negativeJoinCut :
    ∀ {S : Set (Real × Real)}, ∀ {T : Set (Real × Real)}, ∀ (D' : Real × Real → Real), (Convex
        Real S) → ((∀ x, x ∈ S → D' x ≤ 0) → ((∀ y, y ∈ T → 0 ≤ D' y) → ((∀ x y : Real × Real, ∀
        r s : Real, r + s ≠ 0 →
        D' ((r / (r + s)) • x + (s / (r + s)) • y) =
          r / (r + s) * D' x + s / (r + s) * D' y) → ((∀ w, w ∈ convexJoin Real S T → D' w = 0 →
              w ∈ S) → (convexJoin Real S T ∩ {z | D' z ≤ 0} ⊆ S))))) := by
  classical
  intro S T D' hS hneg hpos haff hzero
  rintro z ⟨hz, hDz⟩
  obtain ⟨x, hx, y, hy, hseg⟩ := mem_convexJoin.mp hz
  obtain ⟨r, s, hr, hs, hrs, rfl⟩ := hseg
  have hdx := hneg x hx
  have hdy := hpos y hy
  have hDz' : D' (r • x + s • y) = r * D' x + s * D' y := by
    have hh := haff x y r s (by rw [hrs]; norm_num)
    simpa only [hrs, div_one, one_smul] using hh
  by_cases hdyzero : D' y = 0
  · have hyS : y ∈ S := hzero y
      (mem_convexJoin.mpr ⟨x, hx, y, hy, right_mem_segment Real x y⟩) hdyzero
    exact hS hx hyS hr hs hrs
  have hdypos : 0 < D' y := lt_of_le_of_ne hdy (Ne.symm hdyzero)
  by_cases hdxzero : D' x = 0
  · have hszero : s = 0 := by
      by_contra hsne
      have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hsne)
      rw [hdxzero] at hDz'
      have hprod : 0 < s * D' y := mul_pos hspos hdypos
      change D' (r • x + s • y) ≤ 0 at hDz
      rw [hDz'] at hDz
      nlinarith
    have hrone : r = 1 := by linarith
    simpa [hszero, hrone] using hx
  have hdxneg : D' x < 0 := lt_of_le_of_ne hdx hdxzero
  let den := D' y - D' x
  have hden : 0 < den := sub_pos.mpr (lt_trans hdxneg hdypos)
  have hdenne : D' y - D' x ≠ 0 := ne_of_gt hden
  let alpha := D' y / den
  let beta := -D' x / den
  have halpha : 0 ≤ alpha := le_of_lt (div_pos hdypos hden)
  have hbeta : 0 < beta := div_pos (neg_pos.mpr hdxneg) hden
  have hsum : alpha + beta = 1 := by
    dsimp [alpha, beta, den]
    field_simp [hdenne]
    ring
  let w := alpha • x + beta • y
  have hwseg : w ∈ segment Real x y := ⟨alpha, beta, halpha, hbeta.le, hsum, rfl⟩
  have hwjoin : w ∈ convexJoin Real S T := mem_convexJoin.mpr ⟨x, hx, y, hy, hwseg⟩
  have hwzero : D' w = 0 := by
    have hh := haff x y alpha beta (by rw [hsum]; norm_num)
    rw [show D' w = alpha * D' x + beta * D' y by
      simpa only [hsum, div_one, one_smul] using hh]
    dsimp [alpha, beta, den]
    field_simp [hdenne]
    ring
  have hwS : w ∈ S := hzero w hwjoin hwzero
  have hs_le : s ≤ beta := by
    apply (le_div_iff₀ hden).mpr
    dsimp [den]
    have hmix : r * D' x + s * D' y ≤ 0 := by
      rw [← hDz']
      exact hDz
    have hmixEq : r * D' x + s * D' y =
        D' x + s * (D' y - D' x) := by
      calc
        _ = (r + s) * D' x + s * (D' y - D' x) := by ring
        _ = D' x + s * (D' y - D' x) := by rw [hrs]; ring
    nlinarith only [hmix, hmixEq]
  let c := s / beta
  have hc : 0 ≤ c := div_nonneg hs hbeta.le
  have hc_le : c ≤ 1 := (div_le_one hbeta).mpr hs_le
  have hc_beta : c * beta = s := div_mul_cancel₀ s (ne_of_gt hbeta)
  have hr_eq : r = 1 - s := by
    nlinarith only [hrs]
  have hc_alpha : (1 - c) + c * alpha = r := by
    have halpha' : alpha = 1 - beta := by
      linarith only [hsum]
    calc
      (1 - c) + c * alpha = (1 - c) + c * (1 - beta) := by rw [halpha']
      _ = 1 - c * beta := by
        rw [mul_sub]
        simp only [mul_one]
        rw [← add_sub_assoc, sub_add_cancel]
      _ = 1 - s := by rw [hc_beta]
      _ = r := hr_eq.symm
  have heq : (1 - c) • x + c • w = r • x + s • y := by
    dsimp [w]
    rw [smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul,
      hc_alpha, hc_beta]
  rw [← heq]
  exact hS hx hwS (sub_nonneg.mpr hc_le) hc (by ring)

private theorem hAeq :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀
        (u : List (Fin (n + 3))), ∀ (v : List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    let A := a :: (u ++ [b])
    let B := b :: (v ++ [a])
    let H := convexHull Real (q '' {i | i ∈ L})
    let HA := convexHull Real (q '' {i | i ∈ A})
    let HB := convexHull Real (q '' {i | i ∈ B})
    let D := fun z => P3381T1TriangleDeterminant ![q a, q b, z]
    (H ∩ {z | D z = 0} = segment Real (q a) (q b)) → ((∀ (x : Real × Real), ∀ (y : Real × Real),
        ∀ (r : Real), ∀ (s : Real), (r+s ≠ 0) → (D ((r/(r+s)) • x + (s/(r+s)) • y) = r/(r+s)*D x
        + s/(r+s)*D y)) → ((HA ⊆ H ∩ {z | D z ≤ 0}) → ((HB ⊆ H ∩ {z | 0 ≤ D z}) → ((H =
        convexJoin Real HA HB) → ((segment Real (q a) (q b) ⊆ HA) → ((∀ {S : Set (Real × Real)},
            ∀ {T : Set (Real × Real)}, ∀ (D' : Real × Real → Real), (Convex Real S) → ((∀ x, x ∈ S →
        D' x ≤ 0) → ((∀ y, y ∈ T → 0 ≤ D' y) → ((∀ x y : Real × Real, ∀ r s : Real, r + s ≠ 0 →
        D' ((r / (r + s)) • x + (s / (r + s)) • y) = r / (r + s) * D' x + s / (r + s) * D' y) →
        ((∀ w, w ∈ convexJoin Real S T → D' w = 0 → w ∈ S) → (convexJoin Real S T ∩ {z | D' z ≤
        0} ⊆ S)))))) → (HA = H ∩ {z | D z ≤ 0}))))))) := by
  classical
  intro n q a b u v L A B H HA HB D hzeroLine hDcombo hAcut hBcut hHjoin hchordA negativeJoinCut
  apply Set.Subset.antisymm hAcut
  intro z hz
  have hzjoin : z ∈ convexJoin Real HA HB := by rw [← hHjoin]; exact hz.1
  have hzeroA : ∀ w, w ∈ convexJoin Real HA HB → D w = 0 → w ∈ HA := by
    intro w hw hDw
    have hwH : w ∈ H := by rw [hHjoin]; exact hw
    have hwseg : w ∈ segment Real (q a) (q b) := by
      exact (Set.ext_iff.mp hzeroLine w).mp ⟨hwH, hDw⟩
    exact hchordA hwseg
  exact negativeJoinCut D (convex_convexHull Real _) (fun z hz => (hAcut hz).2)
    (fun z hz => (hBcut hz).2) hDcombo hzeroA ⟨hzjoin, hz.2⟩

private theorem hBeq :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀
        (u : List (Fin (n + 3))), ∀ (v : List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    let A := a :: (u ++ [b])
    let B := b :: (v ++ [a])
    let H := convexHull Real (q '' {i | i ∈ L})
    let HA := convexHull Real (q '' {i | i ∈ A})
    let HB := convexHull Real (q '' {i | i ∈ B})
    let D := fun z => P3381T1TriangleDeterminant ![q a, q b, z]
    (H ∩ {z | D z = 0} = segment Real (q a) (q b)) → ((∀ (x : Real × Real), ∀ (y : Real × Real),
        ∀ (r : Real), ∀ (s : Real), (r+s ≠ 0) → (D ((r/(r+s)) • x + (s/(r+s)) • y) = r/(r+s)*D x
        + s/(r+s)*D y)) → ((HA ⊆ H ∩ {z | D z ≤ 0}) → ((HB ⊆ H ∩ {z | 0 ≤ D z}) → ((H =
        convexJoin Real HA HB) → ((segment Real (q a) (q b) ⊆ HB) → ((∀ {S : Set (Real × Real)},
            ∀ {T : Set (Real × Real)}, ∀ (D' : Real × Real → Real), (Convex Real S) → ((∀ x, x ∈ S →
        D' x ≤ 0) → ((∀ y, y ∈ T → 0 ≤ D' y) → ((∀ x y : Real × Real, ∀ r s : Real, r + s ≠ 0 →
        D' ((r / (r + s)) • x + (s / (r + s)) • y) = r / (r + s) * D' x + s / (r + s) * D' y) →
        ((∀ w, w ∈ convexJoin Real S T → D' w = 0 → w ∈ S) → (convexJoin Real S T ∩ {z | D' z ≤
        0} ⊆ S)))))) → (HB = H ∩ {z | 0 ≤ D z}))))))) := by
  classical
  intro n q a b u v L A B H HA HB D hzeroLine hDcombo hAcut hBcut hHjoin hchordB negativeJoinCut
  apply Set.Subset.antisymm hBcut
  intro z hz
  have hzjoin : z ∈ convexJoin Real HB HA := by
    rw [convexJoin_comm, ← hHjoin]
    exact hz.1
  have hzeroB : ∀ w, w ∈ convexJoin Real HB HA → -D w = 0 → w ∈ HB := by
    intro w hw hDw
    have hw' : w ∈ convexJoin Real HA HB := by rw [convexJoin_comm]; exact hw
    have hwH : w ∈ H := by rw [hHjoin]; exact hw'
    have hwseg : w ∈ segment Real (q a) (q b) := by
      exact (Set.ext_iff.mp hzeroLine w).mp ⟨hwH, (neg_eq_zero.mp hDw)⟩
    exact hchordB hwseg
  have hcut := negativeJoinCut (fun z => -D z) (convex_convexHull Real _)
    (fun z hz => neg_nonpos.mpr ((hBcut hz).2))
    (fun z hz => neg_nonneg.mpr ((hAcut hz).2))
    (by intro x y r s hrs; rw [hDcombo x y r s hrs]; ring) hzeroB
  apply hcut ⟨hzjoin, ?_⟩
  change -D z ≤ 0
  exact neg_nonpos.mpr hz.2

private theorem hunion :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀
        (u : List (Fin (n + 3))), ∀ (v : List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    let A := a :: (u ++ [b])
    let B := b :: (v ++ [a])
    let H := convexHull Real (q '' {i | i ∈ L})
    let HA := convexHull Real (q '' {i | i ∈ A})
    let HB := convexHull Real (q '' {i | i ∈ B})
    let D := fun z => P3381T1TriangleDeterminant ![q a, q b, z]
    (HA = H ∩ {z | D z ≤ 0}) → ((HB = H ∩ {z | 0 ≤ D z}) → (HA ∪ HB = H)) := by
  classical
  intro n q a b u v L A B H HA HB D hAeq hBeq
  rw [hAeq, hBeq]
  ext z
  constructor
  · rintro (⟨hz, _⟩ | ⟨hz, _⟩)
    · exact hz
    · exact hz
  · intro hz
    by_cases h : D z ≤ 0
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, le_of_not_ge h⟩

private theorem hinter :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀
        (u : List (Fin (n + 3))), ∀ (v : List (Fin (n + 3))),
    let L := a :: (u ++ b :: v)
    let A := a :: (u ++ [b])
    let B := b :: (v ++ [a])
    let H := convexHull Real (q '' {i | i ∈ L})
    let HA := convexHull Real (q '' {i | i ∈ A})
    let HB := convexHull Real (q '' {i | i ∈ B})
    let D := fun z => P3381T1TriangleDeterminant ![q a, q b, z]
    (H ∩ {z | D z = 0} = segment Real (q a) (q b)) → ((HA = H ∩ {z | D z ≤ 0}) → ((HB = H ∩ {z |
        0 ≤ D z}) → (HA ∩ HB = segment Real (q a) (q b)))) := by
  classical
  intro n q a b u v L A B H HA HB D hzeroLine hAeq hBeq
  rw [hAeq, hBeq]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hz, hle⟩, ⟨_, hge⟩⟩
    have hzero : z ∈ H ∩ {w | D w = 0} := ⟨hz, le_antisymm hle hge⟩
    rw [hzeroLine] at hzero
    exact hzero
  · intro hz
    have hzero : z ∈ H ∩ {w | D w = 0} := by rw [hzeroLine]; exact hz
    exact ⟨⟨hzero.1, le_of_eq hzero.2⟩,
      ⟨hzero.1, le_of_eq hzero.2.symm⟩⟩

end ParabolaChordLemmas

theorem P3555T2ParabolaChordCuts {n : Nat}
    (q : Fin (n + 3) → Real × Real)
    (hq : ∀ i, q i = ((i.val : Real), (i.val : Real) ^ 2))
    (a b : Fin (n + 3)) (u v : List (Fin (n + 3)))
     (hv : 0 < v.length)
    (hboundary : (a :: (u ++ b :: v)).Nodup)
    (hcyclic : ∃ k : Nat, (a :: (u ++ b :: v)).Sublist
      ((List.ofFn (fun i : Fin (n + 3) => i)).rotate k)) :
    let L := a :: (u ++ b :: v)
    let A := a :: (u ++ [b])
    let B := b :: (v ++ [a])
    let H := convexHull Real (q '' {i | i ∈ L})
    let HA := convexHull Real (q '' {i | i ∈ A})
    let HB := convexHull Real (q '' {i | i ∈ B})
    let D := fun z => P3381T1TriangleDeterminant ![q a, q b, z]
    a ≠ b ∧ A.Nodup ∧ B.Nodup ∧
    (∃ k : Nat, A.Sublist ((List.ofFn (fun i : Fin (n + 3) => i)).rotate k)) ∧
    (∃ k : Nat, B.Sublist ((List.ofFn (fun i : Fin (n + 3) => i)).rotate k)) ∧
    ({i | i ∈ A} ∩ {i | i ∈ B} = {a, b}) ∧
    (∀ i ∈ u, D (q i) < 0) ∧ (∀ i ∈ v, 0 < D (q i)) ∧
    HA = H ∩ {z | D z ≤ 0} ∧ HB = H ∩ {z | 0 ≤ D z} ∧
    HA ∪ HB = H ∧ HA ∩ HB = segment Real (q a) (q b) := by
-- BODY
  classical
  let L := a :: (u ++ b :: v)
  let A := a :: (u ++ [b])
  let B := b :: (v ++ [a])
  let H := convexHull Real (q '' {i | i ∈ L})
  let HA := convexHull Real (q '' {i | i ∈ A})
  let HB := convexHull Real (q '' {i | i ∈ B})
  have hL : L.Nodup := ParabolaChordLemmas.hL n a b u v hboundary
  have haNotTail : a ∉ u ++ b :: v := ParabolaChordLemmas.haNotTail n a b u v hL
  have htailNodup : (u ++ b :: v).Nodup := ParabolaChordLemmas.htailNodup n a b u v hL
  have hne : a ≠ b := ParabolaChordLemmas.hne n q a b u v hboundary hcyclic hL haNotTail htailNodup
  have hparts := ParabolaChordLemmas.hparts n b u v htailNodup
  have huNodup : u.Nodup := ParabolaChordLemmas.huNodup n b u v hparts
  have hbNotU : b ∉ u := ParabolaChordLemmas.hbNotU n b u v hparts
  have hvNodup : v.Nodup := ParabolaChordLemmas.hvNodup n b u v hparts
  have hbNotV : b ∉ v := ParabolaChordLemmas.hbNotV n b u v hparts
  have haNotU : a ∉ u := ParabolaChordLemmas.haNotU n a b u v haNotTail
  have haNotV : a ∉ v := ParabolaChordLemmas.haNotV n a b u v haNotTail
  have huvDisjoint : ∀ i, i ∈ u → i ∈ v → False := ParabolaChordLemmas.huvDisjoint n b u v hparts
  have hANodup : A.Nodup := ParabolaChordLemmas.hANodup n a b u hne huNodup hbNotU haNotU
  have hBNodup : B.Nodup := ParabolaChordLemmas.hBNodup n a b v hne hvNodup hbNotV haNotV
  have hsets : {i | i ∈ A} ∩ {i | i ∈ B} = {a, b} := (show
      {i | i ∈ A} ∩ {i | i ∈ B} = {a, b}
    from by
      classical
      ext i
      simp [A, B, List.mem_cons, List.mem_append]; aesop)
  have hnil (xs : List (Fin (n + 3))) :
      ([] : List (Fin (n + 3))).Sublist xs := ParabolaChordLemmas.hnil n xs
  have hnilv := ParabolaChordLemmas.hnilv n v hnil
  have hbSub : ([b] : List (Fin (n + 3))).Sublist (b :: v) := ParabolaChordLemmas.hbSub n b v hnilv
  have hAtail : (u ++ [b]).Sublist (u ++ b :: v) := ParabolaChordLemmas.hAtail n b u v hbSub
  have hAsubL : A.Sublist L := ParabolaChordLemmas.hAsubL n a b u v hAtail
  obtain ⟨k, hLrot⟩ := hcyclic
  let root := List.ofFn (fun i : Fin (n + 3) => i)
  let R := root.rotate k
  have hrootlen : root.length = n + 3 := ParabolaChordLemmas.hrootlen n
  obtain ⟨emb, hemb⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hLrot
  have hRval (j : Fin R.length) : (R.get j).val = (j.val + k) % (n + 3) :=
      ParabolaChordLemmas.hRval n k hrootlen j
  have hrankDiff (m k p s : Nat) (hm : 0 < m) (hp : p < m) (hs : s < m)
      (hps : p ≤ s) : (((s+k)%m+m-((p+k)%m))%m) = s-p := ParabolaChordLemmas.hrankDiff n v m k p
          s hm hp hs hps
  have hsourceA : (⟨0, by simp [L]⟩ : Fin L.length).val <
      (⟨u.length+1, by simp [L]⟩ : Fin L.length).val := ParabolaChordLemmas.hsourceA n a b u v
  have hsourceB : u.length+1 < L.length := ParabolaChordLemmas.hsourceB n a b u v hv
  let ia : Fin L.length := ⟨0, by simp [L]⟩
  let ib : Fin L.length := ⟨u.length+1, hsourceB⟩
  have haAtRoot : R.get (emb ia) = a := ParabolaChordLemmas.haAtRoot n a b u v k emb hemb
  have hbAtRoot : R.get (emb ib) = b := ParabolaChordLemmas.hbAtRoot n a b u v k emb hemb hsourceB
  have hrootOrder : (emb ia).val < (emb ib).val := ParabolaChordLemmas.hrootOrder n a b u v k emb
      hsourceA hsourceB
  have hBVsubDrop : (b :: v).Sublist (R.drop (emb ib).val) := ParabolaChordLemmas.hBVsubDrop n a
      b u v k emb hemb hsourceB
  let ip : Fin (R.take (emb ib).val).length := ⟨(emb ia).val, by
    rw [List.length_take]
    apply Nat.lt_min.mpr
    exact ⟨Fin.lt_def.mp hrootOrder, (emb ia).isLt⟩⟩
  have hAsingleTake : ([a] : List (Fin (n+3))).Sublist (R.take (emb ib).val) :=
      ParabolaChordLemmas.hAsingleTake n a b u v k emb hsourceB haAtRoot hrootOrder
  have hBsubAtB : B.Sublist (R.rotate (emb ib).val) := ParabolaChordLemmas.hBsubAtB n a b u v k
      emb hsourceB hBVsubDrop hAsingleTake
  have hBsubRoot : ∃ k : Nat, B.Sublist (root.rotate k) := ParabolaChordLemmas.hBsubRoot n a b u
      v k emb hsourceB hBsubAtB
  have hvalA : a.val = ((emb ia).val + k) % (n + 3) := ParabolaChordLemmas.hvalA n a b u v k emb
      hRval haAtRoot
  have hvalB : b.val = ((emb ib).val + k) % (n + 3) := ParabolaChordLemmas.hvalB n a b u v k emb
      hRval hsourceB hbAtRoot
  have hrankB : ((b.val + (n+3) - a.val) % (n+3)) =
      (emb ib).val - (emb ia).val := ParabolaChordLemmas.hrankB n a b u v k emb hrankDiff
          hsourceB hrootOrder hvalA hvalB
  let rank := fun i : Fin (n+3) => (i.val + (n+3) - a.val) % (n+3)
  have hrankB' : rank b = (emb ib).val - (emb ia).val := ParabolaChordLemmas.hrankB' n a b u v k
      emb hsourceB hrankB
  have hrankAt (p : Fin L.length) (hp : ia ≤ p) (i : Fin (n+3))
      (hpi : L.get p = i) : rank i = (emb p).val - (emb ia).val := ParabolaChordLemmas.hrankAt n
          a b u v k emb hemb hRval hrankDiff hsourceB hvalA p hp i hpi
  have hrankU (i : Fin (n+3)) (hi : i ∈ u) : 0 < rank i ∧ rank i < rank b :=
      ParabolaChordLemmas.hrankU n a b u v hv k emb hsourceB hrootOrder hrankB' hrankAt i hi
  have hrankV (i : Fin (n+3)) (hi : i ∈ v) : rank b < rank i := ParabolaChordLemmas.hrankV n a b
      u v k emb hsourceB hrootOrder hrankB' hrankAt i hi
  have hrankFormula (i : Fin (n+3)) : rank i =
      if a.val ≤ i.val then i.val-a.val else n+3-a.val+i.val := ParabolaChordLemmas.hrankFormula
          n a b u v k emb hsourceB haAtRoot hvalA i
  have hrankHi (i : Fin (n+3)) (h : a.val ≤ i.val) : rank i = i.val-a.val :=
      ParabolaChordLemmas.hrankHi n a hrankFormula i h
  have hrankLo (i : Fin (n+3)) (h : ¬ a.val ≤ i.val) :
      rank i = n+3-a.val+i.val := ParabolaChordLemmas.hrankLo n a hrankFormula i h
  have hAsubRoot : ∃ k : Nat, A.Sublist
      ((List.ofFn (fun i : Fin (n + 3) => i)).rotate k) := ParabolaChordLemmas.hAsubRoot n a b u
          v hAsubL k hLrot
  let D := fun z => P3381T1TriangleDeterminant ![q a, q b, z]
  have hdet (c : Fin (n + 3)) :
      D (q c) = ((b.val : Real) - a.val) *
        ((c.val : Real) - a.val) * ((c.val : Real) - b.val) := ParabolaChordLemmas.hdet n q hq a b c
  have hDform (z : Real × Real) :
      D z = ((b.val : Real) - a.val) *
        (z.2 - ((a.val : Real)+(b.val : Real))*z.1 + a.val*b.val) := ParabolaChordLemmas.hDform n
            q hq a b z
  have hTaConv (c : Fin (n+3)) :
      Convex Real {z : Real × Real | 0 ≤ z.2 - 2*(c.val : Real)*z.1 + (c.val : Real)^2} :=
          ParabolaChordLemmas.hTaConv n c
  have hTaV : q '' {i | i ∈ L} ⊆
      {z : Real × Real | 0 ≤ z.2 - 2*(a.val : Real)*z.1 + (a.val : Real)^2} :=
          ParabolaChordLemmas.hTaV n q hq a b u v
  have hTbV : q '' {i | i ∈ L} ⊆
      {z : Real × Real | 0 ≤ z.2 - 2*(b.val : Real)*z.1 + (b.val : Real)^2} :=
          ParabolaChordLemmas.hTbV n q hq a b u v
  have hTaH : H ⊆ {z : Real × Real | 0 ≤ z.2 - 2*(a.val : Real)*z.1 + (a.val : Real)^2} :=
      ParabolaChordLemmas.hTaH n q a b u v hTaConv hTaV
  have hTbH : H ⊆ {z : Real × Real | 0 ≤ z.2 - 2*(b.val : Real)*z.1 + (b.val : Real)^2} :=
      ParabolaChordLemmas.hTbH n q a b u v hTaConv hTbV
  have haH : q a ∈ H := ParabolaChordLemmas.haH n q a b u v
  have hbH : q b ∈ H := ParabolaChordLemmas.hbH n q a b u v
  have hsegH : segment Real (q a) (q b) ⊆ H := ParabolaChordLemmas.hsegH n q a b u v haH hbH
  let F := fun z : Real × Real => z.2 -
    ((a.val : Real)+(b.val : Real))*z.1 + (a.val : Real)*(b.val : Real)
  have hneR : (b.val : Real)-(a.val : Real) ≠ 0 := ParabolaChordLemmas.hneR n a b hne
  have hFfromD (z : Real × Real) (hDz : D z = 0) : F z = 0 := ParabolaChordLemmas.hFfromD n q a b
      hDform hneR z hDz
  have hTaLine (z : Real × Real) (hf : F z = 0) :
      z.2 - 2*(a.val : Real)*z.1 + (a.val : Real)^2 =
        ((b.val : Real)-(a.val : Real))*(z.1-(a.val : Real)) := ParabolaChordLemmas.hTaLine n a b
            z hf
  have hTbLine (z : Real × Real) (hf : F z = 0) :
      z.2 - 2*(b.val : Real)*z.1 + (b.val : Real)^2 =
        ((a.val : Real)-(b.val : Real))*(z.1-(b.val : Real)) := ParabolaChordLemmas.hTbLine n a b
            z hf
  have chordMemberInc (A B X Y : Real) (hab : A < B)
      (hF : Y-(A+B)*X+A*B=0) (hAX : A ≤ X) (hXB : X ≤ B) :
      (X,Y) ∈ segment Real (A,A^2) (B,B^2) := ParabolaChordLemmas.chordMemberInc A B X Y hab hF
          hAX hXB
  have hsegD : segment Real (q a) (q b) ⊆ {z | D z = 0} := ParabolaChordLemmas.hsegD n q hq a b
      hDform
  have hzeroLine : H ∩ {z | D z = 0} = segment Real (q a) (q b) := ParabolaChordLemmas.hzeroLine
      n q hq a b u v hne hTaH hTbH hsegH hFfromD hTaLine hTbLine chordMemberInc hsegD
  have hBcyclic : ∃ k : Nat, B.Sublist
      ((List.ofFn (fun i : Fin (n+3) => i)).rotate k) := ParabolaChordLemmas.hBcyclic n a b v
          hBsubRoot
  have hDcombo (x y : Real × Real) (r s : Real) (hrs : r+s ≠ 0) :
      D ((r/(r+s)) • x + (s/(r+s)) • y) =
        r/(r+s)*D x + s/(r+s)*D y := ParabolaChordLemmas.hDcombo n q a b hDform x y r s hrs
  have hDleConv : Convex Real {z : Real × Real | D z ≤ 0} := ParabolaChordLemmas.hDleConv n q a b
      hDcombo
  have hDgeConv : Convex Real {z : Real × Real | 0 ≤ D z} := ParabolaChordLemmas.hDgeConv n q a b
      hDcombo
  clear hsegD hTaLine hTbLine hFfromD hneR
    chordMemberInc hTaConv hTaV hTbV hTaH hTbH haH hbH hsegH
  clear ip hAsingleTake hBsubAtB hBVsubDrop hrootOrder
  clear hrankB'
  clear hBsubRoot k hLrot root R hrootlen emb hemb hRval hrankDiff hsourceA hsourceB
    ia ib haAtRoot hbAtRoot hvalA hvalB hrankB hrankAt
  have hUneg : ∀ i ∈ u, D (q i) < 0 := ParabolaChordLemmas.hUneg n q a b u v hne hrankU hrankHi
      hrankLo hdet
  have hVpos : ∀ i ∈ v, 0 < D (q i) := ParabolaChordLemmas.hVpos n q a b v hne hrankV hrankHi
      hrankLo hdet
  clear rank hrankU hrankV hrankFormula hrankHi hrankLo
  have hAidx : {i | i ∈ A} ⊆ {i | i ∈ L} := ParabolaChordLemmas.hAidx n a b u v hAsubL
  have hAinH : q '' {i | i ∈ A} ⊆ H := ParabolaChordLemmas.hAinH n q a b u v hAidx
  have hAhalf : q '' {i | i ∈ A} ⊆ {z | D z ≤ 0} := ParabolaChordLemmas.hAhalf n q a b u hdet hUneg
  have hAcut : HA ⊆ H ∩ {z | D z ≤ 0} := ParabolaChordLemmas.hAcut n q a b u v hDleConv hAinH hAhalf
  have hBidx : {i | i ∈ B} ⊆ {i | i ∈ L} := ParabolaChordLemmas.hBidx n a b u v
  have hBinH : q '' {i | i ∈ B} ⊆ H := ParabolaChordLemmas.hBinH n q a b u v hBidx
  have hBhalf : q '' {i | i ∈ B} ⊆ {z | 0 ≤ D z} := ParabolaChordLemmas.hBhalf n q a b v hdet hVpos
  have hBcut : HB ⊆ H ∩ {z | 0 ≤ D z} := ParabolaChordLemmas.hBcut n q a b u v hDgeConv hBinH hBhalf
  clear hdet hAidx hAinH hAhalf hBidx hBinH hBhalf hDleConv hDgeConv
  clear hL haNotTail htailNodup hparts huNodup hbNotU hvNodup hbNotV haNotU haNotV huvDisjoint
  clear hnil hnilv hbSub hAtail hAsubL hboundary
  have hIndexUnion : {i | i ∈ L} = {i | i ∈ A} ∪ {i | i ∈ B} := ParabolaChordLemmas.hIndexUnion n
      a b u v
  have hImageUnion : q '' {i | i ∈ L} =
      (q '' {i | i ∈ A}) ∪ (q '' {i | i ∈ B}) := ParabolaChordLemmas.hImageUnion n q a b u v
          hIndexUnion
  have hSA : (q '' {i | i ∈ A}).Nonempty := ParabolaChordLemmas.hSA n q a b u
  have hSB : (q '' {i | i ∈ B}).Nonempty := ParabolaChordLemmas.hSB n q a b v
  have hHjoin : H = convexJoin Real HA HB := ParabolaChordLemmas.hHjoin n q a b u v hImageUnion
      hSA hSB
  have hchordA : segment Real (q a) (q b) ⊆ HA := ParabolaChordLemmas.hchordA n q a b u
  have hchordB : segment Real (q a) (q b) ⊆ HB := ParabolaChordLemmas.hchordB n q a b v
  have negativeJoinCut {S T : Set (Real × Real)} (D' : Real × Real → Real)
      (hS : Convex Real S)
      (hneg : ∀ x, x ∈ S → D' x ≤ 0)
      (hpos : ∀ y, y ∈ T → 0 ≤ D' y)
      (haff : ∀ x y : Real × Real, ∀ r s : Real, r + s ≠ 0 →
        D' ((r / (r + s)) • x + (s / (r + s)) • y) =
          r / (r + s) * D' x + s / (r + s) * D' y)
      (hzero : ∀ w, w ∈ convexJoin Real S T → D' w = 0 → w ∈ S) :
      convexJoin Real S T ∩ {z | D' z ≤ 0} ⊆ S := ParabolaChordLemmas.negativeJoinCut (S := S) (T
          := T) D' hS hneg hpos haff hzero
  have hAeq : HA = H ∩ {z | D z ≤ 0} := ParabolaChordLemmas.hAeq n q a b u v hzeroLine hDcombo
      hAcut hBcut hHjoin hchordA negativeJoinCut
  have hBeq : HB = H ∩ {z | 0 ≤ D z} := ParabolaChordLemmas.hBeq n q a b u v hzeroLine hDcombo
      hAcut hBcut hHjoin hchordB negativeJoinCut
  have hunion : HA ∪ HB = H := ParabolaChordLemmas.hunion n q a b u v hAeq hBeq
  have hinter : HA ∩ HB = segment Real (q a) (q b) := ParabolaChordLemmas.hinter n q a b u v
      hzeroLine hAeq hBeq
  exact ⟨hne, hANodup, hBNodup, hAsubRoot, hBcyclic, hsets,
    hUneg, hVpos, hAeq, hBeq, hunion, hinter⟩

end ApollonianSuperharmonic

end
