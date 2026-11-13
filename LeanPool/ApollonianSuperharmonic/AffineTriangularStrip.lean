/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Nodup
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

public import LeanPool.ApollonianSuperharmonic.TriangularStripSegment

-- [TABLET NODE: AffineTriangularStrip]

/-!
# AffineTriangularStrip

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace TriangularStripProof

private theorem rotHeight :
    let R : (Int × Int) ≃ (Int × Int) :=
      { toFun := fun z => (z.1 - z.2, z.1)
        invFun := fun z => (z.2, z.2 - z.1)
        left_inv := fun z => by ext <;> simp
        right_inv := fun z => by ext <;> simp }
    ∀ (x : (Int × Int)), ∀ (y : (Int × Int)), ∀ (z : (Int × Int)), TriangularSignedHeight (R x)
        (R y) (R z) = TriangularSignedHeight x y z := by
  classical
  intro R x y z
  simp only [TriangularSignedHeight, R, Equiv.coe_fn_mk]
  ring

private theorem rotMax :
    let R : (Int × Int) ≃ (Int × Int) :=
      { toFun := fun z => (z.1 - z.2, z.1)
        invFun := fun z => (z.2, z.2 - z.1)
        left_inv := fun z => by ext <;> simp
        right_inv := fun z => by ext <;> simp }
    ∀ (x : (Int × Int)), ∀ (y : (Int × Int)), TriangularMaxIncrement (R x) (R y) =
        TriangularMaxIncrement x y := by
  classical
  intro R x y
  have h₁ : y.1 - y.2 - (x.1 - x.2) = (y.1 - x.1) - (y.2 - x.2) := by ring
  have h₂ : (y.1 - x.1) - (y.2 - x.2) - (y.1 - x.1) = -(y.2 - x.2) := by ring
  simp only [TriangularMaxIncrement, R, Equiv.coe_fn_mk, h₁, h₂, abs_neg]
  simp only [max_comm, max_left_comm]

private theorem rotAdj :
    let R : (Int × Int) ≃ (Int × Int) :=
      { toFun := fun z => (z.1 - z.2, z.1)
        invFun := fun z => (z.2, z.2 - z.1)
        left_inv := fun z => by ext <;> simp
        right_inv := fun z => by ext <;> simp }
    ∀ (x : (Int × Int)), ∀ (y : (Int × Int)), TriangularLatticeAdjacent (R x) (R y) ↔
        TriangularLatticeAdjacent x y := by
  classical
  intro R x y
  simp only [TriangularLatticeAdjacent, R, Equiv.coe_fn_mk, Prod.sub_def, Prod.mk.injEq]
  omega

private theorem normOrder :
    ∀ (A : Int), ∀ (B : Int), (0 < A) → ((0 ≤ B) → ((B ≤ A) → (∃ e : Int ≃
        {z : (Int × Int) // 0 ≤ A * z.2 - B * z.1 ∧ A * z.2 - B * z.1 < A},
        ∀ m n : Int,
          TriangularLatticeAdjacent (e m).1 (e n).1 ↔ n = m + 1 ∨ m = n + 1))) := by
  classical
  intro A B hA hB hBA
  let c : Int → Int := fun r => (B * r + A - 1) / A
  have hc (r : Int) : 0 ≤ A * c r - B * r ∧ A * c r - B * r < A := by
    have h := Int.emod_nonneg (B * r + A - 1) (ne_of_gt hA)
    have h' := Int.emod_lt_of_pos (B * r + A - 1) hA
    have h'' := Int.emod_add_mul_ediv (B * r + A - 1) A
    dsimp [c]
    omega
  have hu (r s : Int) (hs : 0 ≤ A * s - B * r ∧ A * s - B * r < A) : s = c r := by
    have h := hc r
    have : -1 < s - c r ∧ s - c r < 1 := by
      constructor <;> nlinarith
    omega
  let e : Int ≃ {z : (Int × Int) // 0 ≤ A * z.2 - B * z.1 ∧ A * z.2 - B * z.1 < A} :=
    { toFun := fun r => ⟨(r, c r), hc r⟩
      invFun := fun z => z.1.1
      left_inv := fun _ => rfl
      right_inv := fun z => by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact (hu _ _ z.2).symm }
  refine ⟨e, ?_⟩
  intro m n
  change TriangularLatticeAdjacent (m, c m) (n, c n) ↔ _
  have hm := hc m
  have hn := hc n
  have next (r : Int) : c (r + 1) = c r ∨ c (r + 1) = c r + 1 := by
    have hr := hc r
    have hr' := hc (r + 1)
    have : -1 < c (r + 1) - c r ∧ c (r + 1) - c r < 2 := by
      constructor <;> nlinarith
    omega
  simp only [TriangularLatticeAdjacent, Prod.sub_def, Prod.mk.injEq]
  constructor
  · intro h
    rcases h with h | h | h | h | h | h <;> rcases h with ⟨h₁, h₂⟩
    all_goals
      first
      | omega
      | have he : n = m := by omega
        exfalso
        simp [he] at h₂
  · rintro (rfl | h)
    · rcases next m with h | h <;> omega
    · subst m
      rcases next n with h' | h' <;> omega

private theorem monotoneChain :
    ∀ (l : List Int), (l.Nodup) → ((l.IsChain (fun a b => b = a + 1 ∨ a = b + 1)) → (l.IsChain
        (fun a b => b = a + 1) ∨ l.IsChain (fun a b => a = b + 1))) := by
  classical
  intro l hn hc
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l =>
      have hn' := (List.nodup_cons.mp hn).2
      have hc' := (List.isChain_cons_cons.mp hc).2
      have hab := (List.isChain_cons_cons.mp hc).1
      cases l with
      | nil => simpa using hab
      | cons c l =>
        have hac : a ≠ c := by
          intro h
          exact (List.nodup_cons.mp hn).1 (by simp [h])
        rcases ih hn' hc' with hf | hb
        · have hbc := (List.isChain_cons_cons.mp hf).1
          left
          exact List.isChain_cons_cons.mpr ⟨by omega, hf⟩
        · have hbc := (List.isChain_cons_cons.mp hb).1
          right
          exact List.isChain_cons_cons.mpr ⟨by omega, hb⟩

private theorem forwardLast :
    ∀ (a : Int), ∀ (l : List Int), ((a :: l).IsChain (fun a b => b = a + 1)) → ((a :: l).getLast?
        = some (a + l.length)) := by
  classical
  intro a l hc
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    obtain ⟨rfl, hc⟩ := List.isChain_cons_cons.mp hc
    rw [List.getLast?_cons_cons, ih _ hc]
    congr 1
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

private theorem backwardLast :
    ∀ (a : Int), ∀ (l : List Int), ((a :: l).IsChain (fun a b => a = b + 1)) → ((a :: l).getLast?
        = some (a - l.length)) := by
  classical
  intro a l hc
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    obtain ⟨hab, hc⟩ := List.isChain_cons_cons.mp hc
    have he : b = a - 1 := by omega
    subst b
    simpa [List.getLast?_cons_cons, Nat.cast_add, sub_sub, add_comm] using ih (a - 1) hc

private theorem forwardUnique :
    ∀ (a : Int), ∀ (l : List Int), ∀ (k : List Int), ((a :: l).IsChain (fun a b => b = a + 1)) →
        (((a :: k).IsChain (fun a b => b = a + 1)) → ((l.length = k.length) → (l = k))) := by
  classical
  intro a l k hl hk hlen
  induction l generalizing a k with
  | nil => simpa using hlen.symm
  | cons b l ih =>
    cases k with
    | nil => simp at hlen
    | cons c k =>
      obtain ⟨rfl, hl⟩ := List.isChain_cons_cons.mp hl
      obtain ⟨rfl, hk⟩ := List.isChain_cons_cons.mp hk
      congr 1
      exact ih _ _ hl hk (by simpa using hlen)

private theorem backwardUnique :
    ∀ (a : Int), ∀ (l : List Int), ∀ (k : List Int), ((a :: l).IsChain (fun a b => a = b + 1)) →
        (((a :: k).IsChain (fun a b => a = b + 1)) → ((l.length = k.length) → (l = k))) := by
  classical
  intro a l k hl hk hlen
  induction l generalizing a k with
  | nil => simpa using hlen.symm
  | cons b l ih =>
    cases k with
    | nil => simp at hlen
    | cons c k =>
      obtain ⟨hab, hl⟩ := List.isChain_cons_cons.mp hl
      obtain ⟨hac, hk⟩ := List.isChain_cons_cons.mp hk
      have : c = b := by omega
      subst c
      congr 1
      exact ih _ _ hl hk (by simpa using hlen)

private theorem intUnique :
    (∀ (l : List Int), (l.Nodup) → ((l.IsChain (fun a b => b = a + 1 ∨ a = b + 1)) → (l.IsChain
        (fun a b => b = a + 1) ∨ l.IsChain (fun a b => a = b + 1)))) → ((∀ (a : Int), ∀ (l : List
        Int), ((a :: l).IsChain (fun a b => b = a + 1)) → ((a :: l).getLast? = some (a +
        l.length))) → ((∀ (a : Int), ∀ (l : List Int), ((a :: l).IsChain (fun a b => a = b + 1))
        → ((a :: l).getLast? = some (a - l.length))) → ((∀ (a : Int), ∀ (l : List Int), ∀ (k :
        List Int), ((a :: l).IsChain (fun a b => b = a + 1)) → (((a :: k).IsChain (fun a b => b =
        a + 1)) → ((l.length = k.length) → (l = k)))) → ((∀ (a : Int), ∀ (l : List Int), ∀ (k :
        List Int), ((a :: l).IsChain (fun a b => a = b + 1)) → (((a :: k).IsChain (fun a b => a =
        b + 1)) → ((l.length = k.length) → (l = k)))) → (∀ (a : Int), ∀ (b : Int), ∀ (l : List
        Int), ∀ (k : List Int), (l.head? = some a ∧ l.getLast? = some b ∧ l.Nodup ∧
        l.IsChain (fun a b => b = a + 1 ∨ a = b + 1)) → ((k.head? = some a ∧ k.getLast? = some b
            ∧ k.Nodup ∧
        k.IsChain (fun a b => b = a + 1 ∨ a = b + 1)) → (l = k))))))) := by
  classical
  intro monotoneChain forwardLast backwardLast forwardUnique backwardUnique a b l k hl hk
  cases l with
  | nil => simp at hl
  | cons a' l =>
    cases k with
    | nil => simp at hk
    | cons a'' k =>
      have ha : a' = a := by simpa using hl.1
      have ha' : a'' = a := by simpa using hk.1
      subst a'
      subst a''
      rcases monotoneChain _ hl.2.2.1 hl.2.2.2 with hf | hb <;>
        rcases monotoneChain _ hk.2.2.1 hk.2.2.2 with kf | kb
      · have hlast := forwardLast _ _ hf
        have klast := forwardLast _ _ kf
        have hlen : l.length = k.length := by
          rw [hl.2.1] at hlast
          rw [hk.2.1] at klast
          simp only [Option.some.injEq] at hlast klast
          omega
        exact congrArg (List.cons a) (forwardUnique _ _ _ hf kf hlen)
      · have hlast := forwardLast _ _ hf
        have klast := backwardLast _ _ kb
        rw [hl.2.1] at hlast
        rw [hk.2.1] at klast
        simp only [Option.some.injEq] at hlast klast
        have hl0 : l = [] := List.length_eq_zero_iff.mp (by omega)
        have hk0 : k = [] := List.length_eq_zero_iff.mp (by omega)
        simp [hl0, hk0]
      · have hlast := backwardLast _ _ hb
        have klast := forwardLast _ _ kf
        rw [hl.2.1] at hlast
        rw [hk.2.1] at klast
        simp only [Option.some.injEq] at hlast klast
        have hl0 : l = [] := List.length_eq_zero_iff.mp (by omega)
        have hk0 : k = [] := List.length_eq_zero_iff.mp (by omega)
        simp [hl0, hk0]
      · have hlast := backwardLast _ _ hb
        have klast := backwardLast _ _ kb
        have hlen : l.length = k.length := by
          rw [hl.2.1] at hlast
          rw [hk.2.1] at klast
          simp only [Option.some.injEq] at hlast klast
          omega
        exact congrArg (List.cons a) (backwardUnique _ _ _ hb kb hlen)

private theorem intExists :
    ∀ (a : Int), ∀ (b : Int), ∃ l : List Int,
      l.head? = some a ∧ l.getLast? = some b ∧ l.Nodup ∧
        l.IsChain (fun a b => b = a + 1 ∨ a = b + 1) := by
  classical
  intro a b
  have forward (a : Int) (d : Nat) : ∃ l : List Int,
      l.head? = some a ∧ l.getLast? = some (a + d) ∧ l.Nodup ∧
        l.IsChain (fun a b => b = a + 1) := by
    induction d generalizing a with
    | zero => exact ⟨[a], by simp⟩
    | succ d ih =>
      obtain ⟨l, hh, ht, hn, hc⟩ := ih (a + 1)
      have lower : ∀ z ∈ l, a + 1 ≤ z := by
        cases l with
        | nil => simp at hh
        | cons a' l =>
          have : a' = a + 1 := by simpa using hh
          subst a'
          exact hc.induction (fun z => a + 1 ≤ z) _
            (by intro x y hxy h; omega) (by simp)
      refine ⟨a :: l, by simp, ?_, ?_, ?_⟩
      · have hne : l ≠ [] := by intro he; simp [he] at hh
        rw [List.getLast?_cons_of_ne_nil hne, ht]
        congr 1
        simp only [Nat.cast_succ]
        ring
      · exact List.nodup_cons.mpr ⟨by intro h; have := lower a h; omega, hn⟩
      · exact hc.cons (by intro y hy; simpa [hh, eq_comm] using hy)
  by_cases hab : a ≤ b
  · have hd : a + ((b - a).toNat : Int) = b := by omega
    obtain ⟨l, hh, ht, hn, hc⟩ := forward a (b - a).toNat
    exact ⟨l, hh, hd ▸ ht, hn, hc.imp (by intro a b h; exact Or.inl h)⟩
  · have hd : b + ((a - b).toNat : Int) = a := by omega
    obtain ⟨l, hh, ht, hn, hc⟩ := forward b (a - b).toNat
    refine ⟨l.reverse, ?_, ?_, List.nodup_reverse.mpr hn, ?_⟩
    · rw [List.head?_reverse, ht, hd]
    · simpa using hh
    · apply List.isChain_reverse.mpr
      exact hc.imp (by intro a b h; exact Or.inr h)

private theorem normalizeStrip :
    let R : (Int × Int) ≃ (Int × Int) :=
      { toFun := fun z => (z.1 - z.2, z.1)
        invFun := fun z => (z.2, z.2 - z.1)
        left_inv := fun z => by ext <;> simp
        right_inv := fun z => by ext <;> simp }
    (∀ (x : (Int × Int)), ∀ (y : (Int × Int)), ∀ (z : (Int × Int)), TriangularSignedHeight (R x)
        (R y) (R z) = TriangularSignedHeight x y z) → ((∀ (x : (Int × Int)), ∀ (y : (Int × Int)),
        TriangularMaxIncrement (R x) (R y) = TriangularMaxIncrement x y) → ((∀ (x : (Int × Int)),
        ∀ (y : (Int × Int)), TriangularLatticeAdjacent (R x) (R y) ↔ TriangularLatticeAdjacent x
        y) → (∀ (x : (Int × Int)), ∀ (y : (Int × Int)), (x ≠ y) → (∃ e : (Int × Int) ≃ (Int ×
        Int), e x = (0, 0) ∧ 0 < (e y).1 ∧ 0 ≤ (e y).2 ∧ (e y).2 ≤ (e y).1 ∧
        (∀ z, TriangularSignedHeight (e x) (e y) (e z) = TriangularSignedHeight x y z) ∧
        TriangularMaxIncrement (e x) (e y) = TriangularMaxIncrement x y ∧
        (∀ z u, TriangularLatticeAdjacent (e z) (e u) ↔ TriangularLatticeAdjacent z u))))) := by
  classical
  intro R rotHeight rotMax rotAdj x y hxy
  let T : (Int × Int) ≃ (Int × Int) :=
    { toFun := fun z => z - x
      invFun := fun z => z + x
      left_inv := fun z => by simp
      right_inv := fun z => by simp }
  have htH (z : (Int × Int)) : TriangularSignedHeight (T x) (T y) (T z) =
      TriangularSignedHeight x y z := by
    simp [T, TriangularSignedHeight, Prod.sub_def]
  have htM : TriangularMaxIncrement (T x) (T y) = TriangularMaxIncrement x y := by
    simp [T, TriangularMaxIncrement, Prod.sub_def]
  have htAdj (z u : (Int × Int)) : TriangularLatticeAdjacent (T z) (T u) ↔
      TriangularLatticeAdjacent z u := by
    simp only [TriangularLatticeAdjacent, T, Equiv.coe_fn_mk]
    rw [sub_sub_sub_cancel_right]
  let E : Nat → (Int × Int) ≃ (Int × Int) := fun n => T.trans (R ^ n)
  have heH (n : Nat) (z : (Int × Int)) : TriangularSignedHeight (E n x) (E n y) (E n z) =
      TriangularSignedHeight x y z := by
    induction n with
    | zero => simpa [E] using htH z
    | succ n ih =>
      simpa [E, pow_succ', Equiv.Perm.mul_apply] using
        (rotHeight (E n x) (E n y) (E n z)).trans ih
  have heM (n : Nat) : TriangularMaxIncrement (E n x) (E n y) =
      TriangularMaxIncrement x y := by
    induction n with
    | zero => simpa [E] using htM
    | succ n ih =>
      simpa [E, pow_succ', Equiv.Perm.mul_apply] using
        (rotMax (E n x) (E n y)).trans ih
  have heAdj (n : Nat) (z u : (Int × Int)) : TriangularLatticeAdjacent (E n z) (E n u) ↔
      TriangularLatticeAdjacent z u := by
    induction n with
    | zero => simpa [E] using htAdj z u
    | succ n ih =>
      simpa [E, pow_succ', Equiv.Perm.mul_apply] using
        (rotAdj (E n z) (E n u)).trans ih
  have he0 (n : Nat) : E n x = (0, 0) := by
    induction n with
    | zero => ext <;> simp [E, T, Prod.sub_def]
    | succ n ih => simpa [E, pow_succ', Equiv.Perm.mul_apply, R] using congrArg R ih
  have hnonzero : y.1 - x.1 ≠ 0 ∨ y.2 - x.2 ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    apply hxy
    ext <;> omega
  have hex : ∃ n : Nat, 0 < (E n y).1 ∧ 0 ≤ (E n y).2 ∧ (E n y).2 ≤ (E n y).1 := by
    by_cases ha : 0 ≤ y.1 - x.1
    · by_cases hb : 0 ≤ y.2 - x.2
      · by_cases hba : y.2 - x.2 ≤ y.1 - x.1
        · refine ⟨0, ?_⟩
          simp [E, T]
          omega
        · refine ⟨5, ?_⟩
          norm_num [E, T, R, pow_succ, Equiv.Perm.mul_apply]
          omega
      · refine ⟨1, ?_⟩
        norm_num [E, T, R, pow_succ, Equiv.Perm.mul_apply]
        omega
    · by_cases hb : 0 ≤ y.2 - x.2
      · refine ⟨4, ?_⟩
        norm_num [E, T, R, pow_succ, Equiv.Perm.mul_apply]
        omega
      · by_cases hba : y.2 - x.2 ≤ y.1 - x.1
        · refine ⟨2, ?_⟩
          norm_num [E, T, R, pow_succ, Equiv.Perm.mul_apply]
          omega
        · refine ⟨3, ?_⟩
          norm_num [E, T, R, pow_succ, Equiv.Perm.mul_apply]
          omega
  obtain ⟨n, hn⟩ := hex
  exact ⟨E n, he0 n, hn.1, hn.2.1, hn.2.2, heH n, heM n, heAdj n⟩

private theorem stripOrder :
    (∀ (A : Int), ∀ (B : Int), (0 < A) → ((0 ≤ B) → ((B ≤ A) → (∃ e : Int ≃
        {z : (Int × Int) // 0 ≤ A * z.2 - B * z.1 ∧ A * z.2 - B * z.1 < A}, ∀ m n : Int,
        TriangularLatticeAdjacent (e m).1 (e n).1 ↔ n = m + 1 ∨ m = n + 1)))) → ((∀ (x : (Int ×
        Int)), ∀ (y : (Int × Int)), (x ≠ y) → (∃ e : (Int × Int) ≃ (Int × Int), e x = (0, 0) ∧ 0
        < (e y).1 ∧ 0 ≤ (e y).2 ∧ (e y).2 ≤ (e y).1 ∧ (∀ z, TriangularSignedHeight (e x) (e y) (e
        z) = TriangularSignedHeight x y z) ∧ TriangularMaxIncrement (e x) (e y) =
        TriangularMaxIncrement x y ∧ (∀ z u, TriangularLatticeAdjacent (e z) (e u) ↔
        TriangularLatticeAdjacent z u))) → (∀ (x : (Int × Int)), ∀ (y : (Int × Int)), (x ≠ y) →
        (0 < TriangularMaxIncrement x y ∧
        ∃ order : Int ≃ {z : (Int × Int) // TriangularBoundaryStrip x y z},
          ∀ m n : Int,
            TriangularLatticeAdjacent (order m).1 (order n).1 ↔ n = m + 1 ∨ m = n + 1))) := by
  classical
  intro normOrder normalizeStrip x y hxy
  obtain ⟨e, he0, hA, hB, hBA, heH, heM, heAdj⟩ := normalizeStrip x y hxy
  let A := (e y).1
  let B := (e y).2
  have hmax : TriangularMaxIncrement (e x) (e y) = A := by
    rw [he0]
    dsimp [TriangularMaxIncrement, A, B]
    rw [sub_zero, sub_zero, abs_of_nonneg hA.le, abs_of_nonneg hB,
      abs_of_nonneg (sub_nonneg.mpr hBA)]
    omega
  have hM : TriangularMaxIncrement x y = A := heM.symm.trans hmax
  have hstrip (z : (Int × Int)) : TriangularBoundaryStrip x y z ↔
      0 ≤ A * (e z).2 - B * (e z).1 ∧ A * (e z).2 - B * (e z).1 < A := by
    unfold TriangularBoundaryStrip
    rw [← heH z, he0, hM]
    simp [TriangularSignedHeight, A, B]
  obtain ⟨f, hf⟩ := normOrder A B hA hB hBA
  let t : {z : (Int × Int) // TriangularBoundaryStrip x y z} ≃
      {z : (Int × Int) // 0 ≤ A * z.2 - B * z.1 ∧ A * z.2 - B * z.1 < A} :=
    { toFun := fun z => ⟨e z.1, (hstrip z.1).mp z.2⟩
      invFun := fun z => ⟨e.symm z.1, (hstrip (e.symm z.1)).mpr (by simpa using z.2)⟩
      left_inv := fun z => by apply Subtype.ext; simp
      right_inv := fun z => by apply Subtype.ext; simp }
  refine ⟨by simpa [hM] using hA, f.trans t.symm, ?_⟩
  intro m n
  change TriangularLatticeAdjacent (e.symm (f m).1) (e.symm (f n).1) ↔ _
  rw [← heAdj]
  simpa using hf m n

private theorem crossing :
    ∀ (x : (Int × Int)), ∀ (y : (Int × Int)), ∀ (z : (Int × Int)), (0 ≤ TriangularSignedHeight x
        y z ∧
        ∃ u : (Int × Int), TriangularLatticeAdjacent z u ∧ TriangularSignedHeight x y u < 0) ↔
        TriangularBoundaryStrip x y z := by
  classical
  intro x y z
  let a := y.1 - x.1
  let b := y.2 - x.2
  have hbound : ∀ u, TriangularLatticeAdjacent z u →
      TriangularSignedHeight x y z - TriangularSignedHeight x y u ≤ TriangularMaxIncrement x y := by
    intro u hu
    simp only [TriangularLatticeAdjacent, Prod.sub_def, Prod.mk.injEq] at hu
    have ha : |a| ≤ TriangularMaxIncrement x y := le_max_left _ _
    have hb : |b| ≤ TriangularMaxIncrement x y := (le_max_left _ _).trans (le_max_right _ _)
    have hab : |a - b| ≤ TriangularMaxIncrement x y := (le_max_right _ _).trans (le_max_right _ _)
    have ha' := le_abs_self a
    have ha'' := neg_le_abs a
    have hb' := le_abs_self b
    have hb'' := neg_le_abs b
    have hab' := le_abs_self (a - b)
    have hab'' := neg_le_abs (a - b)
    dsimp [a, b] at *
    rcases hu with hu | hu | hu | hu | hu | hu <;>
      rcases hu with ⟨hu₁, hu₂⟩ <;> dsimp [TriangularSignedHeight] <;> nlinarith
  have hstep : ∃ d : (Int × Int),
      TriangularLatticeAdjacent (0, 0) d ∧
      a * d.2 - b * d.1 = -TriangularMaxIncrement x y := by
    have ha : |a| = a ∨ |a| = -a := abs_choice a
    have hb : |b| = b ∨ |b| = -b := abs_choice b
    have hab : |a - b| = a - b ∨ |a - b| = -(a - b) := abs_choice (a - b)
    change ∃ d : (Int × Int), TriangularLatticeAdjacent (0, 0) d ∧
      a * d.2 - b * d.1 = -max |a| (max |b| |a - b|)
    by_cases h₁ : max |b| |a - b| ≤ |a|
    · rw [max_eq_left h₁]
      rcases ha with ha | ha
      · refine ⟨(0, -1), ?_, ?_⟩ <;> simp [TriangularLatticeAdjacent, Prod.sub_def, ha]
      · refine ⟨(0, 1), ?_, ?_⟩ <;> simp [TriangularLatticeAdjacent, Prod.sub_def, ha]
    · rw [max_eq_right (le_of_not_ge h₁)]
      by_cases h₂ : |a - b| ≤ |b|
      · rw [max_eq_left h₂]
        rcases hb with hb | hb
        · refine ⟨(1, 0), ?_, ?_⟩ <;> simp [TriangularLatticeAdjacent, Prod.sub_def, hb]
        · refine ⟨(-1, 0), ?_, ?_⟩ <;> simp [TriangularLatticeAdjacent, Prod.sub_def, hb]
      · rw [max_eq_right (le_of_not_ge h₂)]
        rcases hab with hab | hab
        · refine ⟨(-1, -1), ?_, ?_⟩ <;> simp [TriangularLatticeAdjacent, Prod.sub_def, hab]; ring
        · refine ⟨(1, 1), ?_, ?_⟩ <;> simp [TriangularLatticeAdjacent, Prod.sub_def, hab]
  constructor
  · rintro ⟨hz, u, hu, hn⟩
    exact ⟨hz, by have := hbound u hu; omega⟩
  · rintro ⟨hz, hm⟩
    obtain ⟨d, hd, hh⟩ := hstep
    refine ⟨hz, z + d, ?_, ?_⟩
    · simpa [TriangularLatticeAdjacent, Prod.sub_def, Prod.add_def] using hd
    · have he : TriangularSignedHeight x y (z + d) =
          TriangularSignedHeight x y z + (a * d.2 - b * d.1) := by
        simp only [TriangularSignedHeight, Prod.add_def]
        dsimp [a, b]
        ring
      rw [he, hh]
      omega

private theorem stripSegment :
    (∀ (a : Int), ∀ (b : Int), ∀ (l : List Int), ∀ (k : List Int), (l.head? = some a ∧ l.getLast?
        = some b ∧ l.Nodup ∧ l.IsChain (fun a b => b = a + 1 ∨ a = b + 1)) → ((k.head? = some a ∧
        k.getLast? = some b ∧ k.Nodup ∧ k.IsChain (fun a b => b = a + 1 ∨ a = b + 1)) → (l = k)))
        → ((∀ (a : Int), ∀ (b : Int), ∃ l : List Int, l.head? = some a ∧ l.getLast? = some b ∧
        l.Nodup ∧ l.IsChain (fun a b => b = a + 1 ∨ a = b + 1)) → ((∀ (x : (Int × Int)), ∀ (y :
        (Int × Int)), (x ≠ y) → (0 < TriangularMaxIncrement x y ∧ ∃ order : Int ≃
        {z : (Int × Int) // TriangularBoundaryStrip x y z}, ∀ m n : Int,
        TriangularLatticeAdjacent (order m).1 (order n).1 ↔ n = m + 1 ∨ m = n + 1)) → (∀ (x :
        (Int × Int)), ∀ (y : (Int × Int)), ∃! path : List (Int × Int), TriangularStripSegment x y
        path))) := by
  classical
  intro intUnique intExists stripOrder x y
  classical
  by_cases hxy : x = y
  · exact ⟨[x], by simp [TriangularStripSegment, hxy],
      by intro path h; simpa [TriangularStripSegment, hxy] using h⟩
  obtain ⟨hM, order, hadj⟩ := stripOrder x y hxy
  let f : Int → (Int × Int) := fun n => (order n).1
  let g : (Int × Int) → Int := fun z => if hz : TriangularBoundaryStrip x y z then order.symm ⟨z,
      hz⟩ else 0
  have hx : TriangularBoundaryStrip x y x := by
    simpa [TriangularBoundaryStrip, TriangularSignedHeight] using hM
  have hy : TriangularBoundaryStrip x y y := by
    simpa [TriangularBoundaryStrip, TriangularSignedHeight, mul_comm] using hM
  have hfg (z : (Int × Int)) (hz : TriangularBoundaryStrip x y z) : f (g z) = z := by
    simp [f, g, hz]
  have hgf (n : Int) : g (f n) = n := by
    have hn : TriangularBoundaryStrip x y (f n) := (order n).2
    simp [g, hn, f]
  have hfi : Function.Injective f := fun m n h => by
    have := congrArg g h
    simpa only [hgf] using this
  have hfstrip (n : Int) : TriangularBoundaryStrip x y (f n) := (order n).2
  have hrecover (path : List (Int × Int)) (hs : ∀ z ∈ path, TriangularBoundaryStrip x y z) :
      (path.map g).map f = path := by
    rw [List.map_map]
    calc
      path.map (f ∘ g) = path.map id := List.map_congr_left (fun z hz => hfg z (hs z hz))
      _ = path := List.map_id path
  have hcoords (path : List (Int × Int)) (hp : TriangularStripSegment x y path) :
      (path.map g).head? = some (g x) ∧ (path.map g).getLast? = some (g y) ∧
        (path.map g).Nodup ∧
        (path.map g).IsChain (fun a b => b = a + 1 ∨ a = b + 1) := by
    simp only [TriangularStripSegment, ite_eq_right hxy] at hp
    refine ⟨by simp [hp.1], by simp [hp.2.1], ?_, ?_⟩
    · have hn : ((path.map g).map f).Nodup := by rw [hrecover path hp.2.2.2.1]; exact hp.2.2.1
      exact (List.nodup_map_iff hfi).mp hn
    · apply (List.isChain_map g).mpr
      apply hp.2.2.2.2.imp_of_mem_imp
      intro z u hz hu hzu
      apply (hadj (g z) (g u)).mp
      change TriangularLatticeAdjacent (f (g z)) (f (g u))
      rw [hfg z (hp.2.2.2.1 z hz), hfg u (hp.2.2.2.1 u hu)]
      exact hzu
  obtain ⟨l, hh, ht, hn, hc⟩ := intExists (g x) (g y)
  refine ⟨l.map f, ?_, ?_⟩
  · simp only [TriangularStripSegment, ite_eq_right hxy]
    refine ⟨?_, ?_, hn.map hfi, ?_, ?_⟩
    · simp [hh, hfg x hx]
    · simp [ht, hfg y hy]
    · intro z hz
      obtain ⟨n, _, rfl⟩ := List.mem_map.mp hz
      exact hfstrip n
    · exact (List.isChain_map f).mpr (hc.imp fun m n h => (hadj m n).mpr h)
  · intro path hp
    have hco := hcoords path hp
    have he : path.map g = l := intUnique _ _ _ _ hco ⟨hh, ht, hn, hc⟩
    have hp' := hp
    simp only [TriangularStripSegment, ite_eq_right hxy] at hp'
    rw [← hrecover path hp'.2.2.2.1, he]

end TriangularStripProof

theorem AffineTriangularStrip :
    (∀ x y : Int × Int,
      ∃! path : List (Int × Int), TriangularStripSegment x y path) ∧
    ∀ x y : Int × Int, x ≠ y →
      0 < TriangularMaxIncrement x y ∧
      (∀ z : Int × Int,
        (0 ≤ TriangularSignedHeight x y z ∧
          ∃ u : Int × Int,
            TriangularLatticeAdjacent z u ∧
            TriangularSignedHeight x y u < 0) ↔
        TriangularBoundaryStrip x y z) ∧
      ∃ order : Int ≃ {z : Int × Int // TriangularBoundaryStrip x y z},
        ∀ m n : Int,
          TriangularLatticeAdjacent (order m).1 (order n).1 ↔
            n = m + 1 ∨ m = n + 1 := by
-- BODY
  classical
  let R : (Int × Int) ≃ (Int × Int) :=
    { toFun := fun z => (z.1 - z.2, z.1)
      invFun := fun z => (z.2, z.2 - z.1)
      left_inv := fun z => by ext <;> simp
      right_inv := fun z => by ext <;> simp }
  have rotHeight (x y z : (Int × Int)) :
      TriangularSignedHeight (R x) (R y) (R z) = TriangularSignedHeight x y z :=
          TriangularStripProof.rotHeight x y z
  have rotMax (x y : (Int × Int)) :
      TriangularMaxIncrement (R x) (R y) = TriangularMaxIncrement x y :=
          TriangularStripProof.rotMax x y
  have rotAdj (x y : (Int × Int)) :
      TriangularLatticeAdjacent (R x) (R y) ↔ TriangularLatticeAdjacent x y :=
          TriangularStripProof.rotAdj x y
  have normOrder (A B : Int) (hA : 0 < A) (hB : 0 ≤ B) (hBA : B ≤ A) :
      ∃ e : Int ≃ {z : (Int × Int) // 0 ≤ A * z.2 - B * z.1 ∧ A * z.2 - B * z.1 < A},
        ∀ m n : Int,
          TriangularLatticeAdjacent (e m).1 (e n).1 ↔ n = m + 1 ∨ m = n + 1 :=
              TriangularStripProof.normOrder A B hA hB hBA
  have monotoneChain (l : List Int) (hn : l.Nodup)
      (hc : l.IsChain (fun a b => b = a + 1 ∨ a = b + 1)) :
      l.IsChain (fun a b => b = a + 1) ∨ l.IsChain (fun a b => a = b + 1) :=
          TriangularStripProof.monotoneChain l hn hc
  have forwardLast (a : Int) (l : List Int)
      (hc : (a :: l).IsChain (fun a b => b = a + 1)) :
      (a :: l).getLast? = some (a + l.length) := TriangularStripProof.forwardLast a l hc
  have backwardLast (a : Int) (l : List Int)
      (hc : (a :: l).IsChain (fun a b => a = b + 1)) :
      (a :: l).getLast? = some (a - l.length) := TriangularStripProof.backwardLast a l hc
  have forwardUnique (a : Int) (l k : List Int)
      (hl : (a :: l).IsChain (fun a b => b = a + 1))
      (hk : (a :: k).IsChain (fun a b => b = a + 1))
      (hlen : l.length = k.length) : l = k := TriangularStripProof.forwardUnique a l k hl hk hlen
  have backwardUnique (a : Int) (l k : List Int)
      (hl : (a :: l).IsChain (fun a b => a = b + 1))
      (hk : (a :: k).IsChain (fun a b => a = b + 1))
      (hlen : l.length = k.length) : l = k := TriangularStripProof.backwardUnique a l k hl hk hlen
  have intUnique (a b : Int) (l k : List Int)
      (hl : l.head? = some a ∧ l.getLast? = some b ∧ l.Nodup ∧
        l.IsChain (fun a b => b = a + 1 ∨ a = b + 1))
      (hk : k.head? = some a ∧ k.getLast? = some b ∧ k.Nodup ∧
        k.IsChain (fun a b => b = a + 1 ∨ a = b + 1)) : l = k := TriangularStripProof.intUnique
            monotoneChain forwardLast backwardLast forwardUnique backwardUnique a b l k hl hk
  have intExists (a b : Int) : ∃ l : List Int,
      l.head? = some a ∧ l.getLast? = some b ∧ l.Nodup ∧
        l.IsChain (fun a b => b = a + 1 ∨ a = b + 1) := TriangularStripProof.intExists a b
  have normalizeStrip (x y : (Int × Int)) (hxy : x ≠ y) :
      ∃ e : (Int × Int) ≃ (Int × Int), e x = (0, 0) ∧ 0 < (e y).1 ∧ 0 ≤ (e y).2 ∧ (e y).2 ≤ (e
          y).1 ∧
        (∀ z, TriangularSignedHeight (e x) (e y) (e z) = TriangularSignedHeight x y z) ∧
        TriangularMaxIncrement (e x) (e y) = TriangularMaxIncrement x y ∧
        (∀ z u, TriangularLatticeAdjacent (e z) (e u) ↔ TriangularLatticeAdjacent z u) :=
            TriangularStripProof.normalizeStrip rotHeight rotMax rotAdj x y hxy
  have stripOrder (x y : (Int × Int)) (hxy : x ≠ y) :
      0 < TriangularMaxIncrement x y ∧
        ∃ order : Int ≃ {z : (Int × Int) // TriangularBoundaryStrip x y z},
          ∀ m n : Int,
            TriangularLatticeAdjacent (order m).1 (order n).1 ↔ n = m + 1 ∨ m = n + 1 :=
                TriangularStripProof.stripOrder normOrder normalizeStrip x y hxy
  have crossing (x y z : (Int × Int)) :
      (0 ≤ TriangularSignedHeight x y z ∧
        ∃ u : (Int × Int), TriangularLatticeAdjacent z u ∧ TriangularSignedHeight x y u < 0) ↔
        TriangularBoundaryStrip x y z := TriangularStripProof.crossing x y z
  have stripSegment (x y : (Int × Int)) : ∃! path : List (Int × Int), TriangularStripSegment x y
      path := TriangularStripProof.stripSegment intUnique intExists stripOrder x y
  refine ⟨stripSegment, ?_⟩
  intro x y hxy
  obtain ⟨hM, horder⟩ := stripOrder x y hxy
  exact ⟨hM, crossing x y, horder⟩

end ApollonianSuperharmonic

end
