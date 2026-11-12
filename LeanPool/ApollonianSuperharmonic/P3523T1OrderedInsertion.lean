/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3523T1InsertionConstruction
public import LeanPool.ApollonianSuperharmonic.P3523T1SubdivisionExit

/-!
# P3523T1OrderedInsertion

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

open Fin.NatCast

-- [TABLET NODE: P3523T1OrderedInsertion]
namespace OrderedInsertionGeometry

private theorem hsameAt138 :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), (∀ (j : Fin (n + (3 : ℕ))), ∃ k < n + (3 :
        ℕ), s.edge (j + (↑(k + (1 : ℕ)) : Fin (n + (3 : ℕ)))) ≠ s.edge j) → (∀ (i : Fin (r + (3 :
        ℕ))), ∀ (ex : ∃ k < n + (3 : ℕ), s.edge (s.start i + (↑(k + (1 : ℕ)) : Fin (n + (3 :
        ℕ)))) ≠ s.edge (s.start i)),
    let k₀ := Nat.find ex
    let m := k₀ + 1
    (k₀ < n + 3) → (∀ (k : Nat), (k < m) → (s.edge (s.start i + (k : Fin (n + 3))) = i))) := by
  classical
  intro r n q p s hexit i ex k₀ m hk₀ k hk
  cases k with
  | zero => simpa using s.edge_start i
  | succ k =>
    have hmin := Nat.find_min ex (show k < k₀ by dsimp [m] at hk; omega)
    have hkn : k < n + 3 := by dsimp [m] at hk; omega
    have heq : s.edge (s.start i + ((k + 1 : Nat) : Fin (n + 3))) =
        s.edge (s.start i) := by
      by_contra hn
      exact hmin ⟨hkn, hn⟩
    simpa only [s.edge_start] using heq

private theorem hstartAt150 :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), (∀ (j : Fin (n + (3 : ℕ))), s.parameter j =
        (0 : ℝ) → j = s.start (s.edge j)) → ((∀ (j : Fin (n + (3 : ℕ))), ∃ k < n + (3 : ℕ),
        s.edge (j + (↑(k + (1 : ℕ)) : Fin (n + (3 : ℕ)))) ≠ s.edge j) → (∀ (i : Fin (r + (3 :
        ℕ))), ∀ (ex : ∃ k < n + (3 : ℕ), s.edge (s.start i + (↑(k + (1 : ℕ)) : Fin (n + (3 :
        ℕ)))) ≠ s.edge (s.start i)),
    let k₀ := Nat.find ex
    let m := k₀ + 1
    (s.edge (s.start i + (m : Fin (n + 3))) ≠ i) → ((∀ (k : Nat), (k < m) → (s.edge (s.start i +
        (k : Fin (n + 3))) = i)) → (s.start i + (m : Fin (n + 3)) = s.start (i + 1))))) := by
  classical
  intro r n q p s hzero hexit i ex k₀ m hlast hsame
  rcases s.successor (s.start i + (k₀ : Fin (n + 3))) with hs | hs
  · have heq : s.edge (s.start i + (m : Fin (n + 3))) = i := by
      simpa [m, Nat.cast_add, add_assoc, hsame k₀ (by dsimp [m]; omega)]
        using hs.1
    exact (hlast heq).elim
  · have heq : s.edge (s.start i + (m : Fin (n + 3))) = i + 1 := by
      simpa [m, Nat.cast_add, add_assoc, hsame k₀ (by dsimp [m]; omega)]
        using hs.1
    have hz : s.parameter (s.start i + (m : Fin (n + 3))) = 0 := by
      simpa [m, Nat.cast_add, add_assoc] using hs.2
    simpa only [heq] using hzero _ hz

private theorem hstepAt162 :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), (∀ (j : Fin (n + (3 : ℕ))), ∃ k < n + (3 :
        ℕ), s.edge (j + (↑(k + (1 : ℕ)) : Fin (n + (3 : ℕ)))) ≠ s.edge j) → (∀ (i : Fin (r + (3 :
        ℕ))), ∀ (ex : ∃ k < n + (3 : ℕ), s.edge (s.start i + (↑(k + (1 : ℕ)) : Fin (n + (3 :
        ℕ)))) ≠ s.edge (s.start i)),
    let k₀ := Nat.find ex
    let m := k₀ + 1
    (∀ (k : Nat), (k < m) → (s.edge (s.start i + (k : Fin (n + 3))) = i)) → (∀ (k : Nat), (k + 1
        < m) → (s.parameter (s.start i + (k : Fin (n + 3))) <
        s.parameter (s.start i + ((k + 1 : Nat) : Fin (n + 3)))))) := by
  classical
  intro r n q p s hexit i ex k₀ m hsame k hk
  rcases s.successor (s.start i + (k : Fin (n + 3))) with hs | hs
  · simpa [Nat.cast_add, add_assoc] using hs.2
  · have heq : i = i + 1 := by
      have hadv : s.edge (s.start i + ((k + 1 : Nat) : Fin (n + 3))) =
          s.edge (s.start i + (k : Fin (n + 3))) + 1 := by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hs.1
      rw [hsame k (by omega), hsame (k + 1) hk] at hadv
      exact hadv
    have hi := congrArg Fin.val heq
    change i.val = (i.val + 1) % (r + 3) at hi
    by_cases hlt : i.val + 1 < r + 3
    · rw [Nat.mod_eq_of_lt hlt] at hi
      omega
    · have hend : i.val + 1 = r + 3 := by omega
      rw [hend, Nat.mod_self] at hi
      omega

private theorem hstrict :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), (∀ (j : Fin (n + (3 : ℕ))), ∃ k < n + (3 :
        ℕ), s.edge (j + (↑(k + (1 : ℕ)) : Fin (n + (3 : ℕ)))) ≠ s.edge j) → (∀ (i : Fin (r + (3 :
        ℕ))), ∀ (ex : ∃ k < n + (3 : ℕ), s.edge (s.start i + (↑(k + (1 : ℕ)) : Fin (n + (3 :
        ℕ)))) ≠ s.edge (s.start i)),
    let k₀ := Nat.find ex
    let m := k₀ + 1
    (∀ (k : Nat), (k + 1 < m) → (s.parameter (s.start i + (k : Fin (n + 3))) < s.parameter
        (s.start i + ((k + 1 : Nat) : Fin (n + 3))))) → (∀ (l : Nat), l < m → ∀ k : Nat, k < l →
      s.parameter (s.start i + (k : Fin (n + 3))) <
        s.parameter (s.start i + (l : Fin (n + 3))))) := by
  classical
  intro r n q p s hexit i ex k₀ m hstep l
  induction l with
  | zero => intro _ k hk; omega
  | succ l ih =>
    intro hl k hkl
    have hsl := hstep l hl
    by_cases heq : k = l
    · simpa only [heq] using hsl
    · exact (ih (by omega) k (by omega)).trans hsl

private theorem affine :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ [NeZero (n + (3 : ℕ))],
    ∀ (j : Fin (n + (3 : ℕ))),
    let t₀ := s.parameter (j - 1)
    let t₁ := s.parameter j
    let u := (t₁ - t₀) / (1 - t₀)
    ((1 - u) * (1 - t₀) = 1 - t₁) → (((1 - u) * t₀ + u = t₁) → (∀ (A : Real × Real), ∀ (B : Real
        × Real), (1 - t₁) • A + t₁ • B =
        (1 - u) • ((1 - t₀) • A + t₀ • B) + u • B)) := by
  classical
  intro r n q p s this j t₀ t₁ u hc₀ hc₁ A B
  calc
    (1 - t₁) • A + t₁ • B =
        ((1 - u) * (1 - t₀)) • A + ((1 - u) * t₀ + u) • B := by
          rw [hc₀, hc₁]
    _ = (1 - u) • ((1 - t₀) • A + t₀ • B) + u • B := by
        rw [add_smul, smul_add, smul_smul, smul_smul]
        simp [add_assoc]

private theorem filterPrev :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), (P3475T1BoundarySubdivision q
        p) → (∀ (X : Set (Real × Real)), ∀ (K : Set (Real × Real)), (P3475T1TriangleTree q X K)
        → ((Fin (n + (3 : ℕ))) → (∀ {α : Type}, ∀ (l : List α), ∀ (p : α → Bool), ∀ (k : Nat), ∀
            (h : Nat), (l.Nodup) → (∀ (hk : k < l.length), (0 < k) → (∀ (hlen : h < (l.filter
        p).length), (p (l.get ⟨k - 1, by omega⟩) = true) → (((l.filter p).get ⟨h, hlen⟩ = l.get
        ⟨k, hk⟩) → (l.get ⟨k - 1, by omega⟩ ∈ (l.filter p).take h))))))) := by
  classical
  intro r n q s X K t j α l p k h hn hk hpos hlen hp hcur
  induction l generalizing k h with
  | nil => simp at hk
  | cons a l ih =>
    cases k with
    | zero => omega
    | succ k =>
      have hk' : k < l.length := by simpa using hk
      cases hp0 : p a with
      | false =>
        by_cases hkz : k = 0
        · subst k
          simp [hp0] at hp
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkz
          have hk'' : k + 1 < l.length := by simpa using hk'
          have hlen' : h < (l.filter p).length := by simpa [hp0] using hlen
          have hcur' : (l.filter p).get ⟨h, hlen'⟩ = l.get ⟨k + 1, hk''⟩ := by
            simpa [hp0] using hcur
          have hprev := ih (k := k + 1) (h := h) (hn := hn.of_cons) (hk := hk'')
            (hpos := by omega) (hlen := hlen') (hp := by simpa using hp) (hcur := hcur')
          simpa [hp0] using hprev
      | true =>
        cases h with
        | zero =>
          have heq : a = l.get ⟨k, hk'⟩ := by simpa [hp0] using hcur
          have hmem : l.get ⟨k, hk'⟩ ∈ l := List.get_mem l ⟨k, hk'⟩
          exact False.elim (hn.notMem (heq ▸ hmem))
        | succ h =>
          by_cases hkz : k = 0
          · subst k
            simp [hp0]
          · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkz
            have hk'' : k + 1 < l.length := by simpa using hk'
            have hlen' : h < (l.filter p).length := by simpa [hp0] using hlen
            have hcur' : (l.filter p).get ⟨h, hlen'⟩ = l.get ⟨k + 1, hk''⟩ := by
              simpa [hp0] using hcur
            have hprev := ih (k := k + 1) (h := h) (hn := hn.of_cons) (hk := hk'')
              (hpos := by omega) (hlen := hlen') (hp := by simpa using hp) (hcur := hcur')
            simpa [hp0] using Or.inr hprev

private theorem fold_not_mem :
    ∀ (n : Nat), ∀ (l : List (Fin (n + 3) × Fin (n + 3) × Fin (n + 3))), ∀ (A : Finset (Fin (n +
        3))), ∀ (x : Fin (n + 3)), (x ∉ A) → ((∀ a ∈ l, a.2.1 ≠ x) → (x ∉ l.foldl (fun vs e =>
        insert e.2.1 vs) A)) := by
  classical
  intro n l A x hx hall
  induction l generalizing A with
  | nil => simpa
  | cons a l ih =>
      have hhead : a.2.1 ≠ x := hall a (by simp)
      apply ih
      · simpa [Finset.mem_insert, hhead.symm] using hx
      · intro b hb
        exact hall b (by simp [hb])

private theorem fold_insert_mem :
    ∀ (n : Nat), ∀ (l : List (Fin (n + 3) × Fin (n + 3) × Fin (n + 3))), ∀ (A : Finset (Fin (n +
        3))), ∀ (x : Fin (n + 3)), (x ∈ A ∨ x ∈ l.map (fun e => e.2.1)) → (x ∈ l.foldl (fun vs e
        => insert e.2.1 vs) A) := by
  classical
  intro n l A x hx
  induction l generalizing A with
  | nil =>
      rcases hx with hxA | hxFalse
      · simpa using hxA
      · simp at hxFalse
  | cons a l ih =>
      simp only [List.map_cons, List.mem_cons] at hx
      simp only [List.foldl_cons]
      rcases hx with hxA | hx
      · apply ih (A := insert a.2.1 A)
        exact Or.inl (Finset.mem_insert.mpr (Or.inr hxA))
      · rcases hx with hxa | hx
        · subst x
          apply ih (A := insert a.2.1 A)
          exact Or.inl (Finset.mem_insert.mpr (Or.inl rfl))
        · apply ih (A := insert a.2.1 A)
          exact Or.inr hx

private theorem keepBoundaryAt383 :
    ∀ (n : Nat),
    let boundaryStep := fun
        (es : Finset (Finset (Fin (n + 3))))
        (e : Fin (n + 3) × Fin (n + 3) × Fin (n + 3)) =>
          insert {e.1, e.2.1}
            (insert {e.2.1, e.2.2} (es.erase {e.1, e.2.2}))
    ∀ (l : List (Fin (n + 3) × Fin (n + 3) × Fin (n + 3))), ∀ (A : Finset (Finset (Fin (n +
        3)))), ∀ (P : Finset (Fin (n + 3))), (P ∈ A ∨ ∃ e ∈ l,
        P = {e.1, e.2.1} ∨ P = {e.2.1, e.2.2}) → ((∀ e ∈ l, P ≠ {e.1, e.2.2}) → (P ∈ l.foldl
            boundaryStep A)) := by
  classical
  intro n boundaryStep l A P hseed hno
  induction l generalizing A with
  | nil =>
      rcases hseed with hA | ⟨e, he, _⟩
      · simpa using hA
      · simp at he
  | cons a l ih =>
      simp only [List.foldl_cons]
      rcases hseed with hA | ⟨e, he, hedge⟩
      · apply ih (A := boundaryStep A a)
        · left
          change P ∈ insert {a.1, a.2.1}
            (insert {a.2.1, a.2.2} (A.erase {a.1, a.2.2}))
          simp only [Finset.mem_insert, Finset.mem_erase]
          exact Or.inr (Or.inr ⟨hno a (by simp), hA⟩)
        · intro b hb
          exact hno b (by simp [hb])
      · rcases List.mem_cons.mp he with heq | heTail
        · subst e
          apply ih (A := boundaryStep A a)
          · left
            rcases hedge with h1 | h2
            · simp [boundaryStep, h1]
            · simp [boundaryStep, h2]
          · intro b hb
            exact hno b (by simp [hb])
        · apply ih (A := boundaryStep A a)
          · right
            exact ⟨e, heTail, hedge⟩
          · intro b hb
            exact hno b (by simp [hb])

private theorem prevTupleMem :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K), ∀ (h : ℕ), ∀ (hh : h <
        (P3523T1InsertionConstruction s t).steps.length), ∀ [NeZero (n + (3 : ℕ))],
    let c := P3523T1InsertionConstruction s t
    let e := c.steps.get ⟨h, hh⟩
    ∀ (j : Fin (n + (3 : ℕ))), ((j - (1 : Fin (n + (3 : ℕ))), j, s.start (s.edge j + (1 : Fin (r
        + (3 : ℕ))))) = e) → (∀ (k : Fin (n + (3 : ℕ))), ∀ (hk : s.start (0 : Fin (r + (3 : ℕ)))
        + k = j), (s.parameter j ≠ 0) → (((j - 1) + 1 = j) → (((List.ofFn fun k : Fin (n + 3) =>
        s.start 0 + k).Nodup) → ((∀ {α : Type}, ∀ (l : List α), ∀ (p : α → Bool), ∀ (k : Nat), ∀
            (h : Nat), (l.Nodup) → (∀ (hk : k < l.length), (0 < k) → (∀ (hlen : h < (l.filter
        p).length), (p (l.get ⟨k - 1, by omega⟩) = true) → (((l.filter p).get ⟨h, hlen⟩ = l.get
        ⟨k, hk⟩) → (l.get ⟨k - 1, by omega⟩ ∈ (l.filter p).take h))))) → (
    (s.parameter (j - 1) ≠ 0) → (((j - 1) - 1, j - 1, s.start (s.edge (j - 1) + 1)) ∈
        c.steps.take h)))))) := by
  classical
  intro r n q p s X K t h hh this c e j heq k hk hparam hp hrawNodup filterPrev hzprev
  let raw := List.ofFn (fun k : Fin (n + 3) => s.start 0 + k)
  let pred := fun z : Fin (n + 3) => decide (s.parameter z ≠ 0)
  let kp : Fin (n + 3) := ⟨k.val - 1, by omega⟩
  have hrawLen : raw.length = n + 3 := by simp [raw]
  have hkpos : 0 < k.val := by
    by_contra hnot
    have hkval : k.val = 0 := by omega
    have hkz : k = 0 := Fin.ext hkval
    subst k
    have hjstart : j = s.start 0 := by simpa using hk.symm
    exact hparam (by rw [hjstart]; exact s.parameter_start 0)
  have hkprev : kp + 1 = k := by
    apply Fin.ext
    rw [Fin.val_add_eq_of_add_lt (by simp [kp]; omega)]
    simp [kp]
    omega
  have hprevLabel : s.start 0 + kp = j - 1 := by
    apply add_right_cancel
    calc
      (s.start 0 + kp) + 1 = s.start 0 + (kp + 1) := by simp [add_assoc]
      _ = s.start 0 + k := by rw [hkprev]
      _ = j := hk
      _ = (j - 1) + 1 := hp.symm
  have hrawPrev : raw.get ⟨k.val - 1, by
      rw [hrawLen]
      exact lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩ = j - 1 := by
    have hcast : Fin.cast hrawLen ⟨k.val - 1, by
        rw [hrawLen]
        exact lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩ = kp := by
      apply Fin.ext
      rfl
    change (List.ofFn (fun i : Fin (n + 3) => s.start 0 + i)).get
      ⟨k.val - 1, by
          rw [hrawLen]
          exact lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩ = j - 1
    rw [List.get_ofFn, hcast]
    exact hprevLabel
  have hrawCur : raw.get ⟨k.val, by rw [hrawLen]; exact k.isLt⟩ = j := by
    have hcast : Fin.cast hrawLen ⟨k.val, by rw [hrawLen]; exact k.isLt⟩ = k := by
      apply Fin.ext
      rfl
    change (List.ofFn (fun i : Fin (n + 3) => s.start 0 + i)).get
      ⟨k.val, by rw [hrawLen]; exact k.isLt⟩ = j
    rw [List.get_ofFn, hcast]
    exact hk
  have hfilterLen : h < (List.filter pred raw).length := by
    simpa [c, P3523T1InsertionConstruction, raw, pred] using hh
  have hfilterCur : (List.filter pred raw).get ⟨h, hfilterLen⟩ = j := by
    have hget : (j - 1, j, s.start (s.edge j + 1)) = c.steps.get ⟨h, hh⟩ := by
      simpa only [e] using heq
    have hm := congrArg
      (fun z : Fin (n + 3) × Fin (n + 3) × Fin (n + 3) => z.2.1) hget.symm
    simpa [c, P3523T1InsertionConstruction, raw, pred] using hm
  have hpred : pred (raw.get ⟨k.val - 1,
      by
          rw [hrawLen]
          exact lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩) = true := by
    rw [hrawPrev]
    simp [pred, hzprev]
  have hfilteredPrev := filterPrev raw pred k.val h hrawNodup
    (by rw [hrawLen]; exact k.isLt) hkpos hfilterLen hpred
    (hfilterCur.trans hrawCur.symm)
  have hfilteredPrev' : j - 1 ∈ (List.filter pred raw).take h := by
    rw [← hrawPrev]
    exact hfilteredPrev
  have : ((j - 1) - 1, j - 1, s.start (s.edge (j - 1) + 1)) ∈
      (List.map (fun z => (z - 1, z, s.start (s.edge z + 1)))
        (List.filter pred raw)).take h := by
    rw [← List.map_take]
    exact List.mem_map.mpr ⟨j - 1, hfilteredPrev', rfl⟩
  simpa [c, P3523T1InsertionConstruction, raw, pred] using this

private theorem pairCasesAt487 :
    ∀ (n : Nat), ∀ {a : Fin (n + 3)}, ∀ {b : Fin (n + 3)}, ∀ {c : Fin (n + 3)}, ∀
        {d : Fin (n + 3)}, (a ≠ b) → ((({a, b} : Finset (Fin (n + 3))) = {c, d}) → ((a = c ∧ b =
        d) ∨ (a = d ∧ b = c))) := by
  classical
  intro n a b c d hab h
  have hac : a = c ∨ a = d := by
    have ha : a ∈ ({c, d} : Finset (Fin (n + 3))) := by
      rw [← h]
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using ha
  rcases hac with hac | had
  · have hb : b = c ∨ b = d := by
      have hb' : b ∈ ({c, d} : Finset (Fin (n + 3))) := by
        rw [← h]
        simp
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hb'
    rcases hb with hbc | hbd
    · exact False.elim (hab (hac.trans hbc.symm))
    · exact Or.inl ⟨hac, hbd⟩
  · have hb : b = c ∨ b = d := by
      have hb' : b ∈ ({c, d} : Finset (Fin (n + 3))) := by
        rw [← h]
        simp
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hb'
    rcases hb with hbc | hbd
    · exact Or.inr ⟨had, hbc⟩
    · exact False.elim (hab (had.trans hbd.symm))

private theorem hrawPrevAt546 :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), (P3475T1TriangleTree q X K) → ((ℕ) → (∀ [NeZero (n + (3 : ℕ))],
    ∀ (j : Fin (n + (3 : ℕ))), ∀ (k : Fin (n + (3 : ℕ))), ((j - 1) + 1 = j) → (
    let raw := List.ofFn (fun k : Fin (n + 3) => s.start 0 + k)
    let kp : Fin (n + 3) := ⟨k.val - 1, by omega⟩
    ∀ (hrawLen : raw.length = n + 3), (s.start 0 + kp = j - 1) → (raw.get ⟨k.val - 1, by
      rw [hrawLen]
      exact lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩ = j - 1)))) := by
  classical
  intro r n q p s X K t h this j k hp raw kp hrawLen hprevLabel
  have hcast : Fin.cast hrawLen ⟨k.val - 1, by
      rw [hrawLen]
      exact lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩ = kp := by
    apply Fin.ext
    rfl
  change (List.ofFn (fun i : Fin (n + 3) => s.start 0 + i)).get
    ⟨k.val - 1, by
        rw [hrawLen]
        exact lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩ = j - 1
  rw [List.get_ofFn, hcast]
  exact hprevLabel

private theorem hrawCurAt556 :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (j : Fin (n + (3 : ℕ))), ∀ (k : Fin (n +
        (3 : ℕ))), (s.start (0 : Fin (r + (3 : ℕ))) + k = j) → (
    let raw := List.ofFn (fun k : Fin (n + 3) => s.start 0 + k)
    ∀ (hrawLen : raw.length = n + 3), raw.get ⟨k.val, by
      rw [hrawLen]
      exact k.isLt⟩ = j) := by
  classical
  intro r n q p s j k hk raw hrawLen
  have hcast : Fin.cast hrawLen ⟨k.val, by rw [hrawLen]; exact k.isLt⟩ = k := by
    apply Fin.ext
    rfl
  change (List.ofFn (fun i : Fin (n + 3) => s.start 0 + i)).get
    ⟨k.val, by rw [hrawLen]; exact k.isLt⟩ = j
  rw [List.get_ofFn, hcast]
  exact hk

private theorem hprefix :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K), ∀ (h : ℕ), ∀ (hh : h <
        (P3523T1InsertionConstruction s t).steps.length), ∀ [NeZero (n + (3 : ℕ))],
    let c := P3523T1InsertionConstruction s t
    let e := c.steps.get ⟨h, hh⟩
    ∀ (j : Fin (n + (3 : ℕ))), ((j - (1 : Fin (n + (3 : ℕ))), j, s.start (s.edge j + (1 : Fin (r
        + (3 : ℕ))))) = e) → ((Fin (n + (3 : ℕ))) → ((c.steps.Nodup) → (∀ a ∈ c.steps.take h,
        a.2.1 ≠ j))) := by
  classical
  intro r n q p s X K t h hh this c e j heq k hstepsNodup a ha haj
  rcases List.mem_take_iff_getElem.mp ha with ⟨i, hi, haeq⟩
  have hi' : i < h := by omega
  have hiSteps : i < c.steps.length := lt_trans hi' hh
  have haSteps := List.getElem_mem hiSteps
  rcases List.mem_map.mp haSteps with ⟨j', hj', htuple⟩
  have hjEq : j' = j := by
    have hm := congrArg (fun z : Fin (n + 3) × Fin (n + 3) × Fin (n + 3) => z.2.1)
      (htuple.trans haeq)
    simpa using hm.trans haj
  have hget : c.steps[i] = c.steps[h] := by
    calc
      c.steps[i] = a := haeq
      _ = (j' - 1, j', s.start (s.edge j' + 1)) := (htuple.trans haeq).symm
      _ = (j - 1, j, s.start (s.edge j + 1)) := by rw [hjEq]
      _ = e := heq
      _ = c.steps[h] := rfl
  have hidx := hstepsNodup.getElem_inj_iff.mp hget
  omega

private theorem hno :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K), ∀ (h : ℕ), ∀ (hh : h <
        (P3523T1InsertionConstruction s t).steps.length), ∀ [NeZero (n + (3 : ℕ))],
    let c := P3523T1InsertionConstruction s t
    let e := c.steps.get ⟨h, hh⟩
    ∀ (j : Fin (n + (3 : ℕ))), ((j - (1 : Fin (n + (3 : ℕ))), j, s.start (s.edge j + (1 : Fin (r
        + (3 : ℕ))))) = e) → ((Fin (n + (3 : ℕ))) → (((j - 1) + 1 = j) → ((s.edge (j - 1) =
        s.edge j) → ((j - 1 ≠ s.start (s.edge j + 1)) → ((c.steps.Nodup) → ((∀ {α : Type}, ∀ (l :
            List α), (l.Nodup) → (∀ (m : Nat), ∀ (hm : m < l.length), l.get ⟨m, hm⟩ ∉ l.take m)) →
        ((∀ {a : Fin (n + 3)}, ∀ {b : Fin (n + 3)}, ∀ {c : Fin (n + 3)}, ∀ {d : Fin (n + 3)}, (a
        ≠ b) → ((({a, b} : Finset (Fin (n + 3))) = {c, d}) → ((a = c ∧ b = d) ∨ (a = d ∧ b =
        c)))) → (
    let P : Finset (Fin (n + 3)) := {j - 1, s.start (s.edge j + 1)}
    ∀ z ∈ c.steps.take h, P ≠ {z.1, z.2.2})))))))) := by
  classical
  intro r n q p s X K t h hh this c e j heq k hp hsame hne hstepsNodup getNotTake pairCases P z
      hz hpair
  have hzsteps : z ∈ c.steps := List.mem_of_mem_take hz
  rcases List.mem_map.mp hzsteps with ⟨w, hw, hztuple⟩
  have hwfilter := List.mem_filter.mp hw
  rcases List.mem_ofFn.mp hwfilter.1 with ⟨v, hv⟩
  have hparamw : s.parameter w ≠ 0 := of_decide_eq_true hwfilter.2
  have hpw : (w - 1) + 1 = w := by simp
  have hsw := s.successor (w - 1)
  rw [hpw] at hsw
  have hsamew : s.edge (w - 1) = s.edge w := by
    rcases hsw with h | h
    · exact h.1.symm
    · exact False.elim (hparamw h.2)
  have hneW : w - 1 ≠ s.start (s.edge w + 1) := by
    intro heqW
    have hed := congrArg s.edge heqW
    rw [hsamew, s.edge_start] at hed
    have hone : (1 : Fin (r + 3)) = 0 := add_left_cancel
      (show s.edge w + 1 = s.edge w + 0 by simp at hed)
    have hvone := congrArg Fin.val hone
    norm_num at hvone
  have horient := pairCases hne hpair
  rcases horient with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · have hwj : w = j := by
      calc
        w = (w - 1) + 1 := hpw.symm
        _ = (j - 1) + 1 := by
          have hwleft : z.1 = w - 1 := congrArg Prod.fst hztuple.symm
          rw [← hwleft, hleft]
        _ = j := hp
    have hztuple' : z = (j - 1, j, s.start (s.edge j + 1)) := by
      calc
        z = (w - 1, w, s.start (s.edge w + 1)) := hztuple.symm
        _ = (j - 1, j, s.start (s.edge j + 1)) := by rw [hwj]
    have hget : z = c.steps.get ⟨h, hh⟩ := by
      calc
        z = (j - 1, j, s.start (s.edge j + 1)) := hztuple'
        _ = e := heq
        _ = c.steps.get ⟨h, hh⟩ := rfl
    have hmem : c.steps.get ⟨h, hh⟩ ∈ c.steps.take h := hget ▸ hz
    exact getNotTake c.steps hstepsNodup h hh hmem
  · have hwprev : w = s.start (s.edge j + 1) + 1 := by
      calc
        w = (w - 1) + 1 := hpw.symm
        _ = s.start (s.edge j + 1) + 1 := by
          have hwleft : z.1 = w - 1 := congrArg Prod.fst hztuple.symm
          rw [← hwleft, hright]
    let b := s.start (s.edge j + 1)
    have hparamb : s.parameter b = 0 := s.parameter_start (s.edge j + 1)
    have hsb := s.successor b
    have hbnext : s.edge b = s.edge j + 1 := s.edge_start _
    have hsameb : s.edge (b + 1) = s.edge b := by
      rcases hsb with hsameb | hadv
      · exact hsameb.1
      · exact False.elim (hparamw (by rw [hwprev]; exact hadv.2))
    have hstartEq : s.start (s.edge (b + 1) + 1) = j - 1 := by
      calc
        s.start (s.edge (b + 1) + 1) = z.2.2 := by
          calc
            _ = s.start (s.edge w + 1) := by simp [b, hwprev]
            _ = z.2.2 := congrArg Prod.snd (congrArg Prod.snd hztuple)
        _ = j - 1 := hleft.symm
    have hcontr := congrArg s.edge hstartEq
    rw [s.edge_start] at hcontr
    have heqEdge : s.edge (b + 1) + 1 = s.edge j := by
      simpa [hsame] using hcontr
    rw [hsameb, hbnext] at heqEdge
    have htwo : s.edge j + 2 = s.edge j := by
      calc
        s.edge j + 2 = (s.edge j + 1) + 1 := by
          rw [show (2 : Fin (r + 3)) = 1 + 1 by norm_num]
          simp [add_assoc]
        _ = s.edge j := heqEdge
    have htwoFin : (2 : Fin (r + 3)) = 0 := by
      exact add_left_cancel (show s.edge j + 2 = s.edge j + 0 by simpa using htwo)
    have hvtwo := congrArg Fin.val htwoFin
    change 2 % (r + 3) = 0 at hvtwo
    rw [Nat.mod_eq_of_lt (by omega : 2 < r + 3)] at hvtwo
    omega

private theorem hseed :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K), (∀ (j : Fin (n + (3 : ℕ))), s.parameter j
        = (0 : ℝ) → j = s.start (s.edge j)) → (∀ (h : ℕ), ∀ [NeZero (n + (3 : ℕ))],
    let c := P3523T1InsertionConstruction s t
    ∀ (j : Fin (n + (3 : ℕ))), (s.edge (j - 1) = s.edge j) → (((s.parameter (j - 1) ≠ 0) → (((j -
        1) - 1, j - 1, s.start (s.edge (j - 1) + 1)) ∈ c.steps.take h)) → (
    let P : Finset (Fin (n + 3)) := {j - 1, s.start (s.edge j + 1)}
    P ∈ (Finset.univ.image fun i : Fin (r + 3) =>
      ({s.start i, s.start (i + 1)} : Finset (Fin (n + 3)))) ∨
      ∃ z ∈ c.steps.take h,
        P = {z.1, z.2.1} ∨ P = {z.2.1, z.2.2}))) := by
  classical
  intro r n q p s X K t hzero h this c j hsame prevTupleMem P
  by_cases hzprev : s.parameter (j - 1) = 0
  · left
    apply Finset.mem_image.mpr
    refine ⟨s.edge j, Finset.mem_univ _, ?_⟩
    have hstart := hzero (j - 1) hzprev
    simp only [P]
    rw [hstart, hsame]
  · right
    have hprev := prevTupleMem hzprev
    refine ⟨((j - 1) - 1, j - 1, s.start (s.edge (j - 1) + 1)), hprev, Or.inr ?_⟩
    simp only [P, hsame]

private theorem hvertices :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K), (∀ (j : Fin (n + (3 : ℕ))), s.parameter j
        = (0 : ℝ) → j = s.start (s.edge j)) → ((P3523T1InsertionConstruction s t).vertices
      (P3523T1InsertionConstruction s t).steps.length = Finset.univ) := by
  classical
  intro r n q p s X K t hzero
  classical
    let c := P3523T1InsertionConstruction s t
    have hinj : Function.Injective (fun k : Fin (n + 3) => s.start 0 + k) := by
      intro a b hab
      exact add_left_cancel hab
    have himage : Finset.univ.image (fun k : Fin (n + 3) => s.start 0 + k) =
        (Finset.univ : Finset (Fin (n + 3))) := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_of_injective _ hinj]
      simp
    have fold_mem (l : List (Fin (n + 3) × Fin (n + 3) × Fin (n + 3)))
        (A : Finset (Fin (n + 3))) (x : Fin (n + 3))
        (hx : x ∈ A ∨ x ∈ l.map (fun e => e.2.1)) :
        x ∈ l.foldl (fun vs e => insert e.2.1 vs) A := by
      induction l generalizing A with
      | nil => simpa using hx.elim id (by simp)
      | cons a l ih =>
          simp only [List.map_cons, List.mem_cons] at hx
          simp only [List.foldl_cons]
          rcases hx with hxA | hx
          · apply ih (A := insert a.2.1 A)
            exact Or.inl (Finset.mem_insert.mpr (Or.inr hxA))
          · rcases hx with hxa | hx
            · subst x
              apply ih (A := insert a.2.1 A)
              exact Or.inl (Finset.mem_insert.mpr (Or.inl rfl))
            · apply ih (A := insert a.2.1 A)
              exact Or.inr hx
    change (c.steps.take c.steps.length).foldl
      (fun vs e => insert e.2.1 vs) (Finset.univ.image s.start) = Finset.univ
    simp only [List.take_length]
    ext x
    constructor
    · intro _
      simp
    · intro _
      by_cases hz : s.parameter x = 0
      · have hxstart := hzero x hz
        rw [hxstart]
        apply fold_mem
        left
        exact Finset.mem_image.mpr ⟨s.edge x, Finset.mem_univ _, rfl⟩
      · apply fold_mem
        right
        change x ∈ (List.map (fun j => (j - 1, j, s.start (s.edge j + 1)))
          (List.filter (fun j => decide (s.parameter j ≠ 0))
            (List.ofFn fun k : Fin (n + 3) => s.start 0 + k))).map
              (fun e => e.2.1)
        have hximg : x ∈ Finset.univ.image (fun k : Fin (n + 3) => s.start 0 + k) := by
          rw [himage]
          exact Finset.mem_univ x
        obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hximg
        have hxsource : x ∈ List.ofFn (fun k : Fin (n + 3) => s.start 0 + k) :=
          List.mem_ofFn.mpr ⟨k, hk⟩
        have hxfilter : x ∈ List.filter (fun j => decide (s.parameter j ≠ 0))
            (List.ofFn fun k : Fin (n + 3) => s.start 0 + k) :=
          List.mem_filter.mpr ⟨hxsource, by simp [hz]⟩
        simpa [List.map_map] using hxfilter

private theorem pairCasesAt830 :
    ∀ (n : Nat), ∀ {a : Fin (n + 3)}, ∀ {b : Fin (n + 3)}, ∀ {c : Fin (n + 3)}, ∀
        {d : Fin (n + 3)}, (a ≠ b) → ((({a, b} : Finset (Fin (n + 3))) = {c, d}) → ((a = c ∧ b =
        d) ∨ (a = d ∧ b = c))) := by
  classical
  intro n a b c d hab h
  have hac : a = c ∨ a = d := by
    have ha : a ∈ ({c, d} : Finset (Fin (n + 3))) := by
      rw [← h]
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using ha
  rcases hac with hac | had
  · have hb : b = c ∨ b = d := by
      have hb' : b ∈ ({c, d} : Finset (Fin (n + 3))) := by
        rw [← h]
        simp
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hb'
    rcases hb with hbc | hbd
    · exact False.elim (hab (hac.trans hbc.symm))
    · exact Or.inl ⟨hac, hbd⟩
  · have hb : b = c ∨ b = d := by
      have hb' : b ∈ ({c, d} : Finset (Fin (n + 3))) := by
        rw [← h]
        simp
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hb'
    rcases hb with hbc | hbd
    · exact Or.inr ⟨had, hbc⟩
    · exact False.elim (hab (had.trans hbd.symm))

private theorem boundaryEdgeInj :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), (∀ {a : Fin (n + 3)}, ∀ {b : Fin (n + 3)},
            ∀ {c : Fin (n + 3)}, ∀ {d : Fin (n + 3)}, (a ≠ b) → ((({a, b} : Finset (Fin (n + 3))) =
        {c, d}) → ((a = c ∧ b = d) ∨ (a = d ∧ b = c)))) → ((∀ (i : Fin (r + 3)), i ≠ i + 1) →
        (Function.Injective
      (fun i : Fin (r + 3) =>
        ({s.start i, s.start (i + 1)} : Finset (Fin (n + 3)))))) := by
  classical
  intro r n q p s pairCases adjacentNe i j hij
  have hends := pairCases (by
    intro h
    exact adjacentNe i (s.start_injective (by simpa using h))) hij
  rcases hends with ⟨hleft, _⟩ | ⟨hleft, hright⟩
  · exact s.start_injective hleft
  · have hij' : i = j + 1 := s.start_injective hleft
    have hji' : i + 1 = j := s.start_injective hright
    have htwo : i + 2 = i := by
      calc
        i + 2 = (i + 1) + 1 := by
          rw [show (2 : Fin (r + 3)) = 1 + 1 by norm_num]
          simp [add_assoc]
        _ = j + 1 := by rw [hji']
        _ = i := by rw [hij']
    have htwoFin : (2 : Fin (r + 3)) = 0 :=
      add_left_cancel (show i + 2 = i + 0 by simpa using htwo)
    have hv := congrArg Fin.val htwoFin
    change 2 % (r + 3) = 0 at hv
    rw [Nat.mod_eq_of_lt (by omega : 2 < r + 3)] at hv
    omega

private theorem boundaryCardUpdate :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), (P3475T1BoundarySubdivision q p) → (∀ (B : Finset (Finset (Fin (n + 3)))), ∀ (V :
            Finset (Fin (n + 3))), ∀ (a : Fin (n + 3)), ∀ (d : Fin (n + 3)), ∀ (b : Fin (n + 3)), (a
        ≠ b) → ((a ∈ V) → ((b ∈ V) → ((d ∉ V) → ((∀ P ∈ B, ∀ x ∈ P, x ∈ V) → (({a, b} ∈ B) →
        ((insert {a, d} (insert {d, b} (B.erase {a, b}))).card = B.card + 1))))))) := by
  classical
  intro r n q p s B V a d b hab ha hb hd hend herase
  have had : a ≠ d := by
    intro h
    exact hd (h ▸ ha)
  have hbd : b ≠ d := by
    intro h
    exact hd (h ▸ hb)
  have hnewA : ({a, d} : Finset (Fin (n + 3))) ∉ B := by
    intro hmem
    have hdmem : d ∈ ({a, d} : Finset (Fin (n + 3))) := by simp
    exact hd (hend _ hmem d hdmem)
  have hnewB : ({d, b} : Finset (Fin (n + 3))) ∉ B := by
    intro hmem
    have hdmem : d ∈ ({d, b} : Finset (Fin (n + 3))) := by simp
    exact hd (hend _ hmem d hdmem)
  have hnewNe : ({a, d} : Finset (Fin (n + 3))) ≠ {d, b} := by
    intro heq
    have hamem : a ∈ ({d, b} : Finset (Fin (n + 3))) := by
      rw [← heq]
      simp
    rcases Finset.mem_insert.mp hamem with had' | hab'
    · exact had had'
    · exact hab (Finset.mem_singleton.mp hab')
  have hnewBErase : ({d, b} : Finset (Fin (n + 3))) ∉ B.erase {a, b} := by
    intro hmem
    exact hnewB (Finset.mem_erase.mp hmem).2
  have hnewAnot : ({a, d} : Finset (Fin (n + 3))) ∉
      insert {d, b} (B.erase {a, b}) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with hnew | hmem
    · exact hnewNe hnew
    · exact hnewA (Finset.mem_erase.mp hmem).2
  rw [Finset.card_insert_of_notMem hnewAnot,
    Finset.card_insert_of_notMem hnewBErase,
    Finset.card_erase_of_mem herase]
  have hcardpos : 0 < B.card := Finset.card_pos.mpr ⟨{a, b}, herase⟩
  have hcardpos' : 1 ≤ B.card := hcardpos
  omega

private theorem hstate :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K), ((∀ h : Nat, ∀ hh : h <
        (P3523T1InsertionConstruction s t).steps.length,
    let e := (P3523T1InsertionConstruction s t).steps.get ⟨h, hh⟩
    e.1 ≠ e.2.2 ∧ e.1 ∈ (P3523T1InsertionConstruction s t).vertices h ∧
    e.2.2 ∈ (P3523T1InsertionConstruction s t).vertices h ∧
    e.2.1 ∉ (P3523T1InsertionConstruction s t).vertices h ∧
    {e.1, e.2.2} ∈ (P3523T1InsertionConstruction s t).boundary h ∧
    ∃ u : Real, 0 < u ∧ u < 1 ∧
      p.vertex e.2.1 = (1 - u) • p.vertex e.1 + u • p.vertex e.2.2 ∧
      P3523T1InterpolatedTarget s t e.2.1 =
        (1 - u) • P3523T1InterpolatedTarget s t e.1 +
          u • P3523T1InterpolatedTarget s t e.2.2)) → (
    let c := P3523T1InsertionConstruction s t
    let initialBoundary := Finset.univ.image (fun i : Fin (r + 3) =>
      ({s.start i, s.start (i + 1)} : Finset (Fin (n + 3))))
    let initialVertices := Finset.univ.image s.start
    (initialBoundary.card = initialVertices.card) → ((∀ (B : Finset (Finset (Fin (n + 3)))), ∀ (V
        : Finset (Fin (n + 3))), ∀ (a : Fin (n + 3)), ∀ (d : Fin (n + 3)), ∀ (b : Fin (n + 3)),
        (a ≠ b) → ((a ∈ V) → ((b ∈ V) → ((d ∉ V) → ((∀ P ∈ B, ∀ x ∈ P, x ∈ V) → (({a, b} ∈ B) →
        ((insert {a, d} (insert {d, b} (B.erase {a, b}))).card = B.card + 1))))))) → (∀ h : Nat,
        h ≤ c.steps.length →
      (∀ P ∈ c.boundary h, ∀ x ∈ P, x ∈ c.vertices h) ∧
        (c.boundary h).card = (c.vertices h).card))) := by
  classical
  intro r n q p s X K t hvalid c initialBoundary initialVertices hinitCard boundaryCardUpdate
  let boundaryStep := fun
      (es : Finset (Finset (Fin (n + 3))))
      (e : Fin (n + 3) × Fin (n + 3) × Fin (n + 3)) =>
        insert {e.1, e.2.1}
          (insert {e.2.1, e.2.2} (es.erase {e.1, e.2.2}))
  intro h
  induction h with
  | zero =>
      intro _
      constructor
      · simp [c, P3523T1InsertionConstruction]
      · simpa [c, P3523T1InsertionConstruction, initialBoundary,
          initialVertices] using hinitCard
  | succ h ih =>
      intro hle
      have hh : h < c.steps.length := by omega
      have hprev := ih (by omega)
      have hentry := hvalid h hh
      rcases hentry with ⟨hab, ha, hb, hd, herase, _⟩
      have hboundaryRec : c.boundary (h + 1) =
          boundaryStep (c.boundary h) c.steps[h] := by
        change (c.steps.take (h + 1)).foldl
          (fun es e => insert {e.1, e.2.1}
            (insert {e.2.1, e.2.2} (es.erase {e.1, e.2.2}))) initialBoundary = _
        rw [List.take_succ_eq_append_getElem hh]
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
        rfl
      have hverticesRec : c.vertices (h + 1) =
          insert c.steps[h].2.1 (c.vertices h) := by
        change (c.steps.take (h + 1)).foldl
          (fun vs e => insert e.2.1 vs) initialVertices = _
        rw [List.take_succ_eq_append_getElem hh]
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
        rfl
      have hupdateCard :
          (c.boundary (h + 1)).card = (c.boundary h).card + 1 := by
        rw [hboundaryRec]
        exact boundaryCardUpdate (c.boundary h) (c.vertices h)
          (c.steps[h].1) (c.steps[h].2.1) (c.steps[h].2.2)
          (by simpa using hab) (by simpa using ha) (by simpa using hb)
          (by simpa using hd) hprev.1 (by simpa using herase)
      have hupdateVertices :
          (c.vertices (h + 1)).card = (c.vertices h).card + 1 := by
        rw [hverticesRec]
        have hfresh : c.steps[h].2.1 ∉ c.vertices h := by simpa using hd
        exact Finset.card_insert_of_notMem hfresh
      constructor
      · intro P hP x hx
        rw [hboundaryRec] at hP
        rw [hverticesRec]
        simp only [boundaryStep, Finset.mem_insert] at hP
        rcases hP with hA | hP
        · subst P
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with hx | hx
          · subst x
            exact Finset.mem_insert.mpr (Or.inr ha)
          · subst x
            exact Finset.mem_insert.mpr (Or.inl rfl)
        · rcases hP with hB | hP
          · subst P
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with hx | hx
            · subst x
              exact Finset.mem_insert.mpr (Or.inl rfl)
            · subst x
              exact Finset.mem_insert.mpr (Or.inr hb)
          · have hold : P ∈ c.boundary h := (Finset.mem_erase.mp hP).2
            exact Finset.mem_insert.mpr (Or.inr (hprev.1 P hold x hx))
      · rw [hupdateCard, hupdateVertices, hprev.2]

private theorem targetPairInj :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), (P3475T1BoundarySubdivision q p) → (∀ (X : Set (Real × Real)), ∀ (K : Set (Real ×
        Real)), (P3475T1TriangleTree q X K) → ((∀ {a : Fin (n + 3)}, ∀ {b : Fin (n + 3)}, ∀
            {c : Fin (n + 3)}, ∀ {d : Fin (n + 3)}, (a ≠ b) → ((({a, b} : Finset (Fin (n + 3))) =
            {c,
        d}) → ((a = c ∧ b = d) ∨ (a = d ∧ b = c)))) → ((∀ (i : Fin (n + 3)), i ≠ i + 1) →
        (Function.Injective
      (fun i : Fin (n + 3) => ({i, i + 1} : Finset (Fin (n + 3)))))))) := by
  classical
  intro r n q p s X K t pairCases targetAdjNe i j hij
  have hcases := pairCases (targetAdjNe i) hij
  rcases hcases with ⟨hij, _⟩ | ⟨hij, hji⟩
  · exact hij
  · have htwo : i + 2 = i := by
      calc
        i + 2 = (i + 1) + 1 := by
          rw [show (2 : Fin (n + 3)) = 1 + 1 by norm_num]
          simp [add_assoc]
        _ = j + 1 := by rw [hji]
        _ = i := by rw [hij]
    have htwoFin : (2 : Fin (n + 3)) = 0 :=
      add_left_cancel (show i + 2 = i + 0 by simpa using htwo)
    have hv := congrArg Fin.val htwoFin
    change 2 % (n + 3) = 0 at hv
    rw [Nat.mod_eq_of_lt (by omega : 2 < n + 3)] at hv
    omega

private theorem keepBoundaryAt1047 :
    ∀ (n : Nat),
    let boundaryStep := fun
        (es : Finset (Finset (Fin (n + 3))))
        (e : Fin (n + 3) × Fin (n + 3) × Fin (n + 3)) =>
          insert {e.1, e.2.1}
            (insert {e.2.1, e.2.2} (es.erase {e.1, e.2.2}))
    ∀ (l : List (Fin (n + 3) × Fin (n + 3) × Fin (n + 3))), ∀ (A : Finset (Finset (Fin (n +
        3)))), ∀ (P : Finset (Fin (n + 3))), (P ∈ A ∨ ∃ e ∈ l,
        P = {e.1, e.2.1} ∨ P = {e.2.1, e.2.2}) → ((∀ e ∈ l, P ≠ {e.1, e.2.2}) → (P ∈ l.foldl
            boundaryStep A)) := by
  classical
  intro n boundaryStep l A P hseed hno
  induction l generalizing A with
  | nil =>
      rcases hseed with hA | ⟨e, he, _⟩
      · simpa using hA
      · simp at he
  | cons a l ih =>
      simp only [List.foldl_cons]
      rcases hseed with hA | ⟨e, he, hedge⟩
      · apply ih (A := boundaryStep A a)
        · left
          change P ∈ insert {a.1, a.2.1}
            (insert {a.2.1, a.2.2} (A.erase {a.1, a.2.2}))
          simp only [Finset.mem_insert, Finset.mem_erase]
          exact Or.inr (Or.inr ⟨hno a (by simp), hA⟩)
        · intro b hb
          exact hno b (by simp [hb])
      · rcases List.mem_cons.mp he with heq | heTail
        · subst e
          apply ih (A := boundaryStep A a)
          · left
            rcases hedge with h1 | h2
            · simp [boundaryStep, h1]
            · simp [boundaryStep, h2]
          · intro b hb
            exact hno b (by simp [hb])
        · apply ih (A := boundaryStep A a)
          · right
            exact ⟨e, heTail, hedge⟩
          · intro b hb
            exact hno b (by simp [hb])

private theorem memStep :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
    let c := P3523T1InsertionConstruction s t
    (Finset.univ.image (fun k : Fin (n + 3) => s.start 0 + k) = (Finset.univ : Finset (Fin (n +
        3)))) → (∀ (j : Fin (n + 3)), (s.parameter j ≠ 0) → ((j - 1, j, s.start (s.edge j + 1)) ∈
        c.steps)) := by
  classical
  intro r n q p s X K t c hshiftImage j hj
  change (j - 1, j, s.start (s.edge j + 1)) ∈
    (List.map (fun z => (z - 1, z, s.start (s.edge z + 1)))
    (List.filter (fun z => decide (s.parameter z ≠ 0))
      (List.ofFn fun k : Fin (n + 3) => s.start 0 + k)))
  apply List.mem_map.mpr
  refine ⟨j, ?_, rfl⟩
  apply List.mem_filter.mpr
  constructor
  · obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (by
      rw [hshiftImage]
      exact Finset.mem_univ j)
    exact List.mem_ofFn.mpr ⟨k, hk⟩
  · simp [hj]

private theorem noErase :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
    let c := P3523T1InsertionConstruction s t
    (∀ {a : Fin (n + 3)}, ∀ {b : Fin (n + 3)}, ∀ {c : Fin (n + 3)}, ∀ {d : Fin (n + 3)}, (a ≠ b)
        → ((({a, b} : Finset (Fin (n + 3))) = {c, d}) → ((a = c ∧ b = d) ∨ (a = d ∧ b = c)))) →
        ((∀ (i : Fin (n + 3)), i ≠ i + 1) → (∀ (x : Fin (n + 3)), ∀ e ∈ c.steps, ({x, x + 1} :
        Finset (Fin (n + 3))) ≠ {e.1, e.2.2})) := by
  classical
  intro r n q p s X K t c pairCases targetAdjNe x e he hpair
  change e ∈ List.map (fun z => (z - 1, z, s.start (s.edge z + 1)))
    (List.filter (fun z => decide (s.parameter z ≠ 0))
      (List.ofFn fun k : Fin (n + 3) => s.start 0 + k)) at he
  rcases List.mem_map.mp he with ⟨w, hw, htuple⟩
  have hwf := List.mem_filter.mp hw
  have hparamw : s.parameter w ≠ 0 := of_decide_eq_true hwf.2
  have hpw : (w - 1) + 1 = w := by simp
  have hsPrev := s.successor (w - 1)
  rw [hpw] at hsPrev
  have hsamew : s.edge (w - 1) = s.edge w := by
    rcases hsPrev with h | h
    · exact h.1.symm
    · exact False.elim (hparamw h.2)
  have hwleft : e.1 = w - 1 := congrArg Prod.fst htuple.symm
  have hwend : e.2.2 = s.start (s.edge w + 1) :=
    (congrArg Prod.snd (congrArg Prod.snd htuple)).symm
  have hcases := pairCases (targetAdjNe x) hpair
  rcases hcases with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · have hwx : w = x + 1 := by
      calc
        w = (w - 1) + 1 := hpw.symm
        _ = x + 1 := by rw [← hwleft, hleft]
    have hstart : w = s.start (s.edge w + 1) := by
      calc
        w = x + 1 := hwx
        _ = e.2.2 := hright
        _ = s.start (s.edge w + 1) := hwend
    have hz : s.parameter w = 0 := by
      rw [hstart]
      exact s.parameter_start _
    exact hparamw hz
  · have hwx : w = x + 2 := by
      calc
        w = (w - 1) + 1 := hpw.symm
        _ = (x + 1) + 1 := by rw [← hwleft, hright]
        _ = x + 2 := by
          rw [show (2 : Fin (n + 3)) = 1 + 1 by norm_num]
          simp [add_assoc]
    have hxstart : x = s.start (s.edge w + 1) := by
      calc
        x = e.2.2 := hleft
        _ = s.start (s.edge w + 1) := hwend
    have hedgeX : s.edge x = s.edge w + 1 := by
      rw [hxstart]
      exact s.edge_start _
    have hEdgeW : s.edge w = s.edge (x + 1) := by
      calc
        s.edge w = s.edge (w - 1) := hsamew.symm
        _ = s.edge (x + 1) := by rw [← hwleft, hright]
    rcases s.successor x with hsX | haX
    · have hzeroOne : (1 : Fin (r + 3)) = 0 := by
        have hEq : s.edge x = s.edge x + 1 := by
          calc
            s.edge x = s.edge w + 1 := hedgeX
            _ = s.edge (x + 1) + 1 := by rw [hEdgeW]
            _ = s.edge x + 1 := by rw [hsX.1]
        exact add_left_cancel
          (show s.edge x + 1 = s.edge x + 0 by simpa using hEq.symm)
      have hv := congrArg Fin.val hzeroOne
      norm_num at hv
    · have hzeroTwo : (2 : Fin (r + 3)) = 0 := by
        have hEq : s.edge x = s.edge x + 2 := by
          calc
            s.edge x = s.edge w + 1 := hedgeX
            _ = s.edge (x + 1) + 1 := by rw [hEdgeW]
            _ = s.edge x + 2 := by
              rw [haX.1, show (2 : Fin (r + 3)) = 1 + 1 by norm_num]
              simp [add_assoc]
        exact add_left_cancel
          (show s.edge x + 2 = s.edge x + 0 by simpa using hEq.symm)
      have hv := congrArg Fin.val hzeroTwo
      change 2 % (r + 3) = 0 at hv
      rw [Nat.mod_eq_of_lt (by omega : 2 < r + 3)] at hv
      omega

private theorem cycleSeed :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K), (∀ (j : Fin (n + (3 : ℕ))), s.parameter j
        = (0 : ℝ) → j = s.start (s.edge j)) → (
    let c := P3523T1InsertionConstruction s t
    let initialBoundary := Finset.univ.image (fun i : Fin (r + 3) =>
      ({s.start i, s.start (i + 1)} : Finset (Fin (n + 3))))
    (∀ {a : Fin (n + 3)}, ∀ {b : Fin (n + 3)}, ∀ {c : Fin (n + 3)}, ∀ {d : Fin (n + 3)}, (a = c)
        → ((b = d) → (({a, b} : Finset (Fin (n + 3))) = {c, d}))) → ((∀ (j : Fin (n + 3)),
            (s.parameter j ≠ 0) → ((j - 1, j, s.start (s.edge j + 1)) ∈ c.steps)) → (∀ (x : Fin (n +
        3)), ({x, x + 1} : Finset (Fin (n + 3))) ∈ initialBoundary ∨
        ∃ e ∈ c.steps,
          ({x, x + 1} : Finset (Fin (n + 3))) = {e.1, e.2.1} ∨
            ({x, x + 1} : Finset (Fin (n + 3))) = {e.2.1, e.2.2}))) := by
  classical
  intro r n q p s X K t hzero c initialBoundary pairEq memStep x
  by_cases hyzero : s.parameter (x + 1) = 0
  · by_cases hxzero : s.parameter x = 0
    · left
      have hxstart := hzero x hxzero
      have hystart := hzero (x + 1) hyzero
      have hsx := s.successor x
      have hadv : s.edge (x + 1) = s.edge x + 1 := by
        rcases hsx with hs | ha
        · have hlt := hs.2
          rw [hyzero] at hlt
          have hnonneg := s.parameter_nonneg x
          linarith
        · exact ha.1
      apply Finset.mem_image.mpr
      refine ⟨s.edge x, Finset.mem_univ _, ?_⟩
      have hright : x + 1 = s.start (s.edge x + 1) := by
        rw [hadv] at hystart
        exact hystart
      exact pairEq hxstart.symm hright.symm
    · right
      have hstep := memStep x hxzero
      refine ⟨(x - 1, x, s.start (s.edge x + 1)), hstep, Or.inr ?_⟩
      have hystart := hzero (x + 1) hyzero
      have hsx := s.successor x
      have hadv : s.edge (x + 1) = s.edge x + 1 := by
        rcases hsx with hs | ha
        · have hlt := hs.2
          rw [hyzero] at hlt
          have hnonneg := s.parameter_nonneg x
          linarith
        · exact ha.1
      have hright : x + 1 = s.start (s.edge x + 1) := by
        rw [hadv] at hystart
        exact hystart
      exact pairEq rfl hright
  · right
    have hstep := memStep (x + 1) hyzero
    refine ⟨(x + 1 - 1, x + 1, s.start (s.edge (x + 1) + 1)), hstep, Or.inl ?_⟩
    have hpred : x + 1 - 1 = x := by simp
    exact pairEq hpred.symm rfl

private theorem htargetSubset :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
    let c := P3523T1InsertionConstruction s t
    let initialBoundary := Finset.univ.image (fun i : Fin (r + 3) =>
      ({s.start i, s.start (i + 1)} : Finset (Fin (n + 3))))
    let targetBoundary := Finset.univ.image (fun j : Fin (n + 3) =>
      ({j, j + 1} : Finset (Fin (n + 3))))
    let boundaryStep := fun
        (es : Finset (Finset (Fin (n + 3))))
        (e : Fin (n + 3) × Fin (n + 3) × Fin (n + 3)) =>
          insert {e.1, e.2.1}
            (insert {e.2.1, e.2.2} (es.erase {e.1, e.2.2}))
    (∀ (l : List (Fin (n + 3) × Fin (n + 3) × Fin (n + 3))), ∀ (A : Finset (Finset (Fin (n +
        3)))), ∀ (P : Finset (Fin (n + 3))), (P ∈ A ∨ ∃ e ∈ l, P = {e.1, e.2.1} ∨ P = {e.2.1,
        e.2.2}) → ((∀ e ∈ l, P ≠ {e.1, e.2.2}) → (P ∈ l.foldl boundaryStep A))) → ((∀ (x : Fin (n
        + 3)), ∀ e ∈ c.steps, ({x, x + 1} : Finset (Fin (n + 3))) ≠ {e.1, e.2.2}) → ((∀ (x : Fin
        (n + 3)), ({x, x + 1} : Finset (Fin (n + 3))) ∈ initialBoundary ∨ ∃ e ∈ c.steps, ({x,
        x + 1} : Finset (Fin (n + 3))) = {e.1, e.2.1} ∨ ({x, x + 1} : Finset (Fin (n + 3))) =
        {e.2.1, e.2.2}) → (targetBoundary ⊆ c.boundary c.steps.length))) := by
  classical
  intro r n q p s X K t c initialBoundary targetBoundary boundaryStep keepBoundary noErase
      cycleSeed P hP
  rcases Finset.mem_image.mp hP with ⟨x, -, rfl⟩
  have hkeep := keepBoundary c.steps initialBoundary {x, x + 1}
    (cycleSeed x) (noErase x)
  change {x, x + 1} ∈
    (c.steps.take c.steps.length).foldl
      (fun es e => insert {e.1, e.2.1}
        (insert {e.2.1, e.2.2} (es.erase {e.1, e.2.2}))) initialBoundary
  rw [List.take_length]
  exact hkeep

end OrderedInsertionGeometry

namespace OrderedInsertionDetails

private theorem hsameAt1300 :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ [NeZero (n + (3 : ℕ))],
    ∀ (j : Fin (n + (3 : ℕ))), (s.parameter j ≠ 0) → ((s.edge j = s.edge (j - (1 : Fin (n + (3 :
        ℕ)))) ∧ s.parameter (j - (1 : Fin (n + (3 : ℕ)))) < s.parameter j ∨ s.edge j = s.edge (j
        - (1 : Fin (n + (3 : ℕ)))) + (1 : Fin (r + (3 : ℕ))) ∧ s.parameter j = (0 : ℝ)) → (s.edge
        (j - 1) = s.edge j)) := by
  classical
  intro r n q p s this j hparam hs
  rcases hs with h | h
  · exact h.1.symm
  · exact False.elim (hparam h.2)

private theorem hnext :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (j : Fin (n + (3 : ℕ))), s.edge j ≠
        s.edge j + 1 := by
  classical
  intro r n q p s j h
  have hone : (1 : Fin (r + 3)) = 0 :=
    add_left_cancel (show s.edge j + 1 = s.edge j + 0 by simp at h)
  have hv := congrArg Fin.val hone
  norm_num at hv

private theorem hne :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ [NeZero (n + (3 : ℕ))],
    ∀ (j : Fin (n + (3 : ℕ))), (s.edge (j - 1) = s.edge j) → ((s.edge j ≠ s.edge j + 1) → (j - 1
        ≠ s.start (s.edge j + 1))) := by
  classical
  intro r n q p s this j hsame hnext h
  have hed := congrArg s.edge h
  rw [hsame, s.edge_start] at hed
  exact hnext hed

private theorem hlt :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ [NeZero (n + (3 : ℕ))],
    ∀ (j : Fin (n + (3 : ℕ))), (s.parameter j ≠ 0) → ((s.edge j = s.edge (j - (1 : Fin (n + (3 :
        ℕ)))) ∧ s.parameter (j - (1 : Fin (n + (3 : ℕ)))) < s.parameter j ∨ s.edge j = s.edge (j
        - (1 : Fin (n + (3 : ℕ)))) + (1 : Fin (r + (3 : ℕ))) ∧ s.parameter j = (0 : ℝ)) →
        (s.parameter (j - 1) < s.parameter j)) := by
  classical
  intro r n q p s this j hparam hs
  rcases hs with h | h
  · exact h.2
  · exact False.elim (hparam h.2)

private theorem hu :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ [NeZero (n + (3 : ℕ))],
    ∀ (j : Fin (n + (3 : ℕ))), (s.parameter (j - 1) < s.parameter j) → (
    let t₀ := s.parameter (j - 1)
    let t₁ := s.parameter j
    let u := (t₁ - t₀) / (1 - t₀)
    (t₀ < 1) → ((t₁ < 1) → (0 < u ∧ u < 1))) := by
  classical
  intro r n q p s this j hlt t₀ t₁ u ht₀one ht₁one
  dsimp [u]
  constructor
  · exact div_pos (sub_pos.mpr hlt) (sub_pos.mpr ht₀one)
  · rw [div_lt_one (sub_pos.mpr ht₀one)]
    linarith

private theorem hc₀ :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ [NeZero (n + (3 : ℕ))],
    ∀ (j : Fin (n + (3 : ℕ))),
    let t₀ := s.parameter (j - 1)
    let t₁ := s.parameter j
    let u := (t₁ - t₀) / (1 - t₀)
    (1 - t₀ ≠ 0) → ((1 - u) * (1 - t₀) = 1 - t₁) := by
  classical
  intro r n q p s this j t₀ t₁ u hden
  dsimp [u]
  field_simp [hden]
  ring

private theorem hc₁ :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ [NeZero (n + (3 : ℕ))],
    ∀ (j : Fin (n + (3 : ℕ))),
    let t₀ := s.parameter (j - 1)
    let t₁ := s.parameter j
    let u := (t₁ - t₀) / (1 - t₀)
    (1 - t₀ ≠ 0) → ((1 - u) * t₀ + u = t₁) := by
  classical
  intro r n q p s this j t₀ t₁ u hden
  dsimp [u]
  field_simp [hden]
  ring

private theorem retain :
    ∀ (n : Nat), ∀ (l : List (Fin (n + 3) × Fin (n + 3) × Fin (n + 3))), ∀ (A : Finset (Fin (n +
        3))), ∀ (x : Fin (n + 3)), (x ∈ A) → (x ∈ l.foldl (fun vs e => insert e.2.1 vs) A) := by
  classical
  intro n l A x hx
  induction l generalizing A with
  | nil => simpa
  | cons a l ih =>
      simpa only [List.foldl_cons] using
        ih (insert a.2.1 A) (Finset.mem_insert.mpr (Or.inr hx))

private theorem hrawNodup :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), (List.ofFn fun k : Fin (n + 3) => s.start 0
        + k).Nodup := by
  classical
  intro r n q p s
  apply List.nodup_ofFn.mpr
  intro a b hab
  exact add_left_cancel hab

private theorem htupleInj :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ [NeZero (n + (3 : ℕ))],
    Function.Injective
      (fun j : Fin (n + 3) => (j - 1, j, s.start (s.edge j + 1))) := by
  classical
  intro r n q p s this a b hab
  exact congrArg (fun e : Fin (n + 3) × Fin (n + 3) × Fin (n + 3) => e.2.1) hab

private theorem hstepsNodup :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K), ∀ [NeZero (n + (3 : ℕ))],
    let c := P3523T1InsertionConstruction s t
    ((List.filter (fun j => decide (s.parameter j ≠ 0)) (List.ofFn fun k : Fin (n + 3) => s.start
        0 + k)).Nodup) → ((Function.Injective (fun j : Fin (n + 3) => (j - 1, j, s.start (s.edge
        j + 1)))) → (c.steps.Nodup)) := by
  classical
  intro r n q p s X K t this c hfilterNodup htupleInj
  change (List.map (fun j => (j - 1, j, s.start (s.edge j + 1)))
    (List.filter (fun j => decide (s.parameter j ≠ 0))
      (List.ofFn fun k : Fin (n + 3) => s.start 0 + k))).Nodup
  exact hfilterNodup.map htupleInj

private theorem getNotTake :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), (P3475T1BoundarySubdivision q p) → (∀ (X : Set (Real × Real)), ∀ (K : Set (Real ×
        Real)), (P3475T1TriangleTree q X K) → ((ℕ) → ((Fin (n + (3 : ℕ))) → ((Fin (n + (3 :
        ℕ))) → (∀ {α : Type}, ∀ (l : List α), (l.Nodup) → (∀ (m : Nat), ∀ (hm : m < l.length),
        l.get ⟨m, hm⟩ ∉ l.take m)))))) := by
  classical
  intro r n q p s X K t h j k α l hn m hm hmem
  rcases List.mem_take_iff_getElem.mp hmem with ⟨i, hi, heq⟩
  have hi' : i < m := by omega
  have hiList : i < l.length := lt_trans hi' hm
  have heq' : l[i] = l[m] := by simpa using heq
  have hidx := hn.getElem_inj_iff.mp heq'
  omega

private theorem hkpos :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K), ∀ (h : ℕ), ∀ [NeZero (n + (3 : ℕ))],
    ∀ (j : Fin (n + (3 : ℕ))), ∀ (k : Fin (n + (3 : ℕ))), ∀ (hk : s.start (0 : Fin (r + (3 : ℕ)))
        + k = j), ∀ (hparam : s.parameter j ≠ 0), ∀ (hp : (j - 1) + 1 = j), (∀ {α : Type}, ∀ (l :
            List α), ∀ (p : α → Bool), ∀ (k : Nat), ∀ (h : Nat), ∀ (hn : l.Nodup), ∀ (hk : k <
        l.length), ∀ (hpos : 0 < k), ∀ (hlen : h < (l.filter p).length), (p (l.get ⟨k - 1,
        by omega⟩) = true) → (((l.filter p).get ⟨h, hlen⟩ = l.get ⟨k, hk⟩) → (l.get ⟨k - 1,
        by omega⟩ ∈ (l.filter p).take h))) → (0 < k.val) := by
  classical
  intro r n q p s X K t h this j k hk hparam hp filterPrev
  by_contra hnot
  have hkval : k.val = 0 := by omega
  have hkz : k = 0 := Fin.ext hkval
  subst k
  have hjstart : j = s.start 0 := by simpa using hk.symm
  exact hparam (by rw [hjstart]; exact s.parameter_start 0)

private theorem hkprev :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K), ∀ (h : ℕ), ∀ [NeZero (n + (3 : ℕ))],
    ∀ (j : Fin (n + (3 : ℕ))), ∀ (k : Fin (n + (3 : ℕ))), ∀ (hp : (j - 1) + 1 = j),
    let raw := List.ofFn (fun k : Fin (n + 3) => s.start 0 + k)
    let kp : Fin (n + 3) := ⟨k.val - 1, by omega⟩
    (raw.length = n + 3) → ((0 < k.val) → (kp + 1 = k)) := by
  classical
  intro r n q p s X K t h this j k hp raw kp hrawLen hkpos
  apply Fin.ext
  rw [Fin.val_add_eq_of_add_lt (by simp [kp]; omega)]
  simp [kp]
  omega

private theorem hprevLabel :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K), ∀ (h : ℕ), ∀ [NeZero (n + (3 : ℕ))],
    ∀ (j : Fin (n + (3 : ℕ))), ∀ (k : Fin (n + (3 : ℕ))), ∀ (hk : s.start (0 : Fin (r + (3 : ℕ)))
        + k = j), ∀ (hp : (j - 1) + 1 = j),
    let kp : Fin (n + 3) := ⟨k.val - 1, by omega⟩
    (kp + 1 = k) → (s.start 0 + kp = j - 1) := by
  classical
  intro r n q p s X K t h this j k hk hp kp hkprev
  apply add_right_cancel
  calc
    (s.start 0 + kp) + 1 = s.start 0 + (kp + 1) := by simp [add_assoc]
    _ = s.start 0 + k := by rw [hkprev]
    _ = j := hk
    _ = (j - 1) + 1 := hp.symm

private theorem hfilterCur :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K), ∀ (h : ℕ), ∀ (hh : h <
        (P3523T1InsertionConstruction s t).steps.length), ∀ [NeZero (n + (3 : ℕ))],
    let c := P3523T1InsertionConstruction s t
    let e := c.steps.get ⟨h, hh⟩
    ∀ (j : Fin (n + (3 : ℕ))), ((j - (1 : Fin (n + (3 : ℕ))), j, s.start (s.edge j + (1 : Fin (r
        + (3 : ℕ))))) = e) → (
    let raw := List.ofFn (fun k : Fin (n + 3) => s.start 0 + k)
    let pred := fun z : Fin (n + 3) => decide (s.parameter z ≠ 0)
    ∀ (hfilterLen : h < (List.filter pred raw).length), (List.filter pred raw).get ⟨h,
        hfilterLen⟩ = j) := by
  classical
  intro r n q p s X K t h hh this c e j heq raw pred hfilterLen
  have hget : (j - 1, j, s.start (s.edge j + 1)) =
      c.steps.get ⟨h, hh⟩ := by simpa only [e] using heq
  have hm := congrArg
    (fun z : Fin (n + 3) × Fin (n + 3) × Fin (n + 3) => z.2.1) hget.symm
  simpa [c, P3523T1InsertionConstruction, raw, pred] using hm

private theorem hpred :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ [NeZero (n + (3 : ℕ))],
    ∀ (j : Fin (n + (3 : ℕ))), ∀ (k : Fin (n + (3 : ℕ))), let raw := List.ofFn (fun k : Fin (n +
        3) => s.start 0 + k)
    let pred := fun z : Fin (n + 3) => decide (s.parameter z ≠ 0)
    (¬s.parameter (j - (1 : Fin (n + (3 : ℕ)))) = (0 : ℝ)) → (∀ (hrawLen : raw.length =
        n + 3), (raw.get ⟨k.val - 1, by
      rw [hrawLen]
      exact lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩ = j - 1) → (pred (raw.get ⟨k.val - 1,
      by
          rw [hrawLen]
          exact lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩) = true)) := by
  classical
  intro r n q p s this j k raw pred hzprev hrawLen hrawPrev
  rw [hrawPrev]
  simp [pred, hzprev]

private theorem hfilteredPrev' :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (h : ℕ), ∀ [NeZero (n + (3 : ℕ))],
    ∀ (j : Fin (n + (3 : ℕ))), ∀ (k : Fin (n + (3 : ℕ))),
    let raw := List.ofFn (fun k : Fin (n + 3) => s.start 0 + k)
    let pred := fun z : Fin (n + 3) => decide (s.parameter z ≠ 0)
    ∀ (hrawLen : raw.length = n + 3), (raw.get ⟨k.val - 1, by
      rw [hrawLen]
      exact lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩ = j - 1) → ((raw.get ⟨(↑k : ℕ) - (1 : ℕ),
          by rw [hrawLen]; exact lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩
          ∈ List.take h (List.filter pred raw)) → (j - 1 ∈ (List.filter pred raw).take h)) := by
  classical
  intro r n q p s h this j k raw pred hrawLen hrawPrev hfilteredPrev
  rw [← hrawPrev]
  exact hfilteredPrev

private theorem htuplePrev :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K), ∀ (h : ℕ), ∀ [NeZero (n + (3 : ℕ))],
    let c := P3523T1InsertionConstruction s t
    ∀ (j : Fin (n + (3 : ℕ))),
    let raw := List.ofFn (fun k : Fin (n + 3) => s.start 0 + k)
    let pred := fun z : Fin (n + 3) => decide (s.parameter z ≠ 0)
    (j - 1 ∈ (List.filter pred raw).take h) → (((j - 1) - 1, j - 1, s.start (s.edge (j - 1) + 1))
        ∈ c.steps.take h) := by
  classical
  intro r n q p s X K t h this c j raw pred hfilteredPrev'
  change ((j - 1) - 1, j - 1, s.start (s.edge (j - 1) + 1)) ∈
    (List.map (fun z => (z - 1, z, s.start (s.edge z + 1)))
      (List.filter pred raw)).take h
  rw [← List.map_take]
  exact List.mem_map.mpr ⟨j - 1, hfilteredPrev', rfl⟩

private theorem hxinit :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (j : Fin (n + (3 : ℕ))), (s.parameter j ≠
        0) → (j ∉ Finset.univ.image s.start) := by
  classical
  intro r n q p s j hparam hx
  rcases Finset.mem_image.mp hx with ⟨i, _, hi⟩
  apply hparam
  rw [← hi]
  exact s.parameter_start i

private theorem hboundary :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K), (∀ (j : Fin (n + (3 : ℕ))), s.parameter j
        = (0 : ℝ) → j = s.start (s.edge j)) → (((∀ h : Nat, ∀ hh : h <
        (P3523T1InsertionConstruction s t).steps.length,
    let e := (P3523T1InsertionConstruction s t).steps.get ⟨h, hh⟩
    e.1 ≠ e.2.2 ∧ e.1 ∈ (P3523T1InsertionConstruction s t).vertices h ∧
    e.2.2 ∈ (P3523T1InsertionConstruction s t).vertices h ∧
    e.2.1 ∉ (P3523T1InsertionConstruction s t).vertices h ∧
    {e.1, e.2.2} ∈ (P3523T1InsertionConstruction s t).boundary h ∧
    ∃ u : Real, 0 < u ∧ u < 1 ∧
      p.vertex e.2.1 = (1 - u) • p.vertex e.1 + u • p.vertex e.2.2 ∧
      P3523T1InterpolatedTarget s t e.2.1 =
        (1 - u) • P3523T1InterpolatedTarget s t e.1 +
          u • P3523T1InterpolatedTarget s t e.2.2)) → (((P3523T1InsertionConstruction s
              t).vertices (P3523T1InsertionConstruction s t).steps.length = Finset.univ) →
              ((P3523T1InsertionConstruction s t).boundary
      (P3523T1InsertionConstruction s t).steps.length =
        Finset.univ.image (fun j : Fin (n + 3) => ({j, j + 1} : Finset _))))) := by
  classical
  intro r n q p s X K t hzero hvalid hvertices
  classical
  let c := P3523T1InsertionConstruction s t
  let initialBoundary := Finset.univ.image (fun i : Fin (r + 3) =>
    ({s.start i, s.start (i + 1)} : Finset (Fin (n + 3))))
  let initialVertices := Finset.univ.image s.start
  let targetBoundary := Finset.univ.image (fun j : Fin (n + 3) =>
    ({j, j + 1} : Finset (Fin (n + 3))))
  let boundaryStep := fun
      (es : Finset (Finset (Fin (n + 3))))
      (e : Fin (n + 3) × Fin (n + 3) × Fin (n + 3)) =>
        insert {e.1, e.2.1}
          (insert {e.2.1, e.2.2} (es.erase {e.1, e.2.2}))
  have pairCases {a b c d : Fin (n + 3)} (hab : a ≠ b)
      (h : ({a, b} : Finset (Fin (n + 3))) = {c, d}) :
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := OrderedInsertionGeometry.pairCasesAt830 n (a := a)
          (b := b) (c := c) (d := d) hab h
  have adjacentNe (i : Fin (r + 3)) : i ≠ i + 1 := by
    intro heq
    have hone : (1 : Fin (r + 3)) = 0 :=
      add_left_cancel (show i + 1 = i + 0 by simp at heq)
    have hv := congrArg Fin.val hone
    norm_num at hv
  have boundaryEdgeInj : Function.Injective
      (fun i : Fin (r + 3) =>
        ({s.start i, s.start (i + 1)} : Finset (Fin (n + 3)))) :=
            OrderedInsertionGeometry.boundaryEdgeInj r n q p s pairCases adjacentNe
  have hinitCard : initialBoundary.card = initialVertices.card := by
    dsimp [initialBoundary, initialVertices]
    rw [Finset.card_image_of_injective _ boundaryEdgeInj,
      Finset.card_image_of_injective _ s.start_injective]
  have hinitEndpoints : ∀ P ∈ initialBoundary, ∀ x ∈ P, x ∈ initialVertices := by
    intro P hP x hx
    rcases Finset.mem_image.mp hP with ⟨i, -, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · subst x
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    · subst x
      exact Finset.mem_image.mpr ⟨i + 1, Finset.mem_univ _, rfl⟩
  have pairEq {a b c d : Fin (n + 3)} (hac : a = c) (hbd : b = d) :
      ({a, b} : Finset (Fin (n + 3))) = {c, d} := by
    ext z
    simp [hac, hbd]
  have boundaryCardUpdate
      (B : Finset (Finset (Fin (n + 3))))
      (V : Finset (Fin (n + 3))) (a d b : Fin (n + 3))
      (hab : a ≠ b) (ha : a ∈ V) (hb : b ∈ V) (hd : d ∉ V)
      (hend : ∀ P ∈ B, ∀ x ∈ P, x ∈ V)
      (herase : {a, b} ∈ B) :
      (insert {a, d} (insert {d, b} (B.erase {a, b}))).card = B.card + 1 :=
          OrderedInsertionGeometry.boundaryCardUpdate r n q p s B V a d b hab ha hb hd hend
          herase
  have hstate : ∀ h : Nat, h ≤ c.steps.length →
      (∀ P ∈ c.boundary h, ∀ x ∈ P, x ∈ c.vertices h) ∧
        (c.boundary h).card = (c.vertices h).card := OrderedInsertionGeometry.hstate r n q p
            s X K t hvalid hinitCard boundaryCardUpdate
  have hfinalState := hstate c.steps.length (by omega)
  have hboundaryCard : (c.boundary c.steps.length).card = n + 3 := by
    rw [hfinalState.2, hvertices]
    simp
  have targetAdjNe (i : Fin (n + 3)) : i ≠ i + 1 := by
    intro heq
    have hone : (1 : Fin (n + 3)) = 0 :=
      add_left_cancel (show i + 1 = i + 0 by simp at heq)
    have hv := congrArg Fin.val hone
    norm_num at hv
  have targetPairInj : Function.Injective
      (fun i : Fin (n + 3) => ({i, i + 1} : Finset (Fin (n + 3)))) :=
          OrderedInsertionGeometry.targetPairInj r n q p s X K t pairCases targetAdjNe
  have htargetCard : targetBoundary.card = n + 3 := by
    dsimp [targetBoundary]
    rw [Finset.card_image_of_injective _ targetPairInj]
    simp
  have keepBoundary
      (l : List (Fin (n + 3) × Fin (n + 3) × Fin (n + 3)))
      (A : Finset (Finset (Fin (n + 3)))) (P : Finset (Fin (n + 3)))
      (hseed : P ∈ A ∨ ∃ e ∈ l,
        P = {e.1, e.2.1} ∨ P = {e.2.1, e.2.2})
      (hno : ∀ e ∈ l, P ≠ {e.1, e.2.2}) :
      P ∈ l.foldl boundaryStep A := OrderedInsertionGeometry.keepBoundaryAt1047 n l A P hseed
          hno
  have hinjShift : Function.Injective (fun k : Fin (n + 3) => s.start 0 + k) := by
    intro a b hab
    exact add_left_cancel hab
  have hshiftImage : Finset.univ.image (fun k : Fin (n + 3) => s.start 0 + k) =
      (Finset.univ : Finset (Fin (n + 3))) := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injective _ hinjShift]
    simp
  have memStep (j : Fin (n + 3)) (hj : s.parameter j ≠ 0) :
      (j - 1, j, s.start (s.edge j + 1)) ∈ c.steps := OrderedInsertionGeometry.memStep r n q
          p s X K t hshiftImage j hj
  have offsetNe (a : Fin (r + 3)) (k : Nat) (hk : k < r + 3)
      (hkpos : 0 < k) : a + (k : Fin (r + 3)) ≠ a := by
    intro heq
    have hkfin : (k : Fin (r + 3)) = 0 :=
      add_left_cancel (show a + (k : Fin (r + 3)) = a + 0 by simpa using heq)
    have hv := congrArg Fin.val hkfin
    change k % (r + 3) = 0 at hv
    rw [Nat.mod_eq_of_lt hk] at hv
    omega
  have noErase (x : Fin (n + 3)) :
      ∀ e ∈ c.steps, ({x, x + 1} : Finset (Fin (n + 3))) ≠ {e.1, e.2.2} :=
          OrderedInsertionGeometry.noErase r n q p s X K t pairCases targetAdjNe x
  have cycleSeed (x : Fin (n + 3)) :
      ({x, x + 1} : Finset (Fin (n + 3))) ∈ initialBoundary ∨
        ∃ e ∈ c.steps,
          ({x, x + 1} : Finset (Fin (n + 3))) = {e.1, e.2.1} ∨
            ({x, x + 1} : Finset (Fin (n + 3))) = {e.2.1, e.2.2} :=
                OrderedInsertionGeometry.cycleSeed r n q p s X K t hzero pairEq memStep x
  have htargetSubset : targetBoundary ⊆ c.boundary c.steps.length :=
      OrderedInsertionGeometry.htargetSubset r n q p s X K t keepBoundary noErase cycleSeed
  change c.boundary c.steps.length = targetBoundary
  exact (Finset.eq_of_subset_of_card_le htargetSubset (by
    rw [hboundaryCard, htargetCard])).symm

end OrderedInsertionDetails

theorem P3523T1OrderedInsertion {r n : Nat}
    (q : P3381T1PolygonBoundary r) (p : P3381T1PolygonBoundary n)
    (s : P3475T1BoundarySubdivision q p)
    (X K : Set (Real × Real)) (t : P3475T1TriangleTree q X K) :
    let c := P3523T1InsertionConstruction s t
    (∀ i : Fin (r + 3), ∃ m : Nat, 0 < m ∧ m ≤ n + 3 ∧
      s.start i + (m : Fin (n + 3)) = s.start (i + 1) ∧
      (∀ k : Nat, k < m → s.edge (s.start i + (k : Fin (n + 3))) = i) ∧
      (∀ k l : Nat, k < l → l < m →
        s.parameter (s.start i + (k : Fin (n + 3))) <
          s.parameter (s.start i + (l : Fin (n + 3))))) ∧
    (∀ h : Nat, ∀ hh : h < c.steps.length,
      let e := c.steps.get ⟨h, hh⟩
      e.1 ≠ e.2.2 ∧ e.1 ∈ c.vertices h ∧ e.2.2 ∈ c.vertices h ∧
      e.2.1 ∉ c.vertices h ∧ {e.1, e.2.2} ∈ c.boundary h ∧
      ∃ u : Real, 0 < u ∧ u < 1 ∧
        p.vertex e.2.1 = (1 - u) • p.vertex e.1 + u • p.vertex e.2.2 ∧
        P3523T1InterpolatedTarget s t e.2.1 =
          (1 - u) • P3523T1InterpolatedTarget s t e.1 +
            u • P3523T1InterpolatedTarget s t e.2.2) ∧
    c.vertices c.steps.length = Finset.univ ∧
    c.boundary c.steps.length =
      Finset.univ.image (fun j : Fin (n + 3) => ({j, j + 1} : Finset _)) := by
-- BODY
  obtain ⟨hzero, hexit⟩ := P3523T1SubdivisionExit q p s
  dsimp only
  constructor
  · intro i
    let ex := hexit (s.start i)
    let k₀ := Nat.find ex
    let m := k₀ + 1
    have hk₀ : k₀ < n + 3 := (Nat.find_spec ex).1
    have hm : m ≤ n + 3 := by dsimp [m]; omega
    have hlast : s.edge (s.start i + (m : Fin (n + 3))) ≠ i := by
      simpa only [m, k₀, s.edge_start] using (Nat.find_spec ex).2
    have hsame (k : Nat) (hk : k < m) := OrderedInsertionGeometry.hsameAt138 r n q p
            s hexit i ex hk₀ k hk
    have hstart := OrderedInsertionGeometry.hstartAt150 r n q p s hzero hexit i ex hlast hsame
    have hstep (k : Nat) (hk : k + 1 < m) := OrderedInsertionGeometry.hstepAt162 r n q p s hexit
        i ex hsame k hk
    exact ⟨m, by dsimp [m]; omega, hm, hstart, hsame,
      fun k l hkl hl => OrderedInsertionGeometry.hstrict r n q p s hexit i ex hstep l hl k hkl⟩
  · have hvalid : (∀ h : Nat, ∀ hh : h < (P3523T1InsertionConstruction s t).steps.length,
      let e := (P3523T1InsertionConstruction s t).steps.get ⟨h, hh⟩
      e.1 ≠ e.2.2 ∧ e.1 ∈ (P3523T1InsertionConstruction s t).vertices h ∧
      e.2.2 ∈ (P3523T1InsertionConstruction s t).vertices h ∧
      e.2.1 ∉ (P3523T1InsertionConstruction s t).vertices h ∧
      {e.1, e.2.2} ∈ (P3523T1InsertionConstruction s t).boundary h ∧
      ∃ u : Real, 0 < u ∧ u < 1 ∧
        p.vertex e.2.1 = (1 - u) • p.vertex e.1 + u • p.vertex e.2.2 ∧
        P3523T1InterpolatedTarget s t e.2.1 =
          (1 - u) • P3523T1InterpolatedTarget s t e.1 +
            u • P3523T1InterpolatedTarget s t e.2.2) := by
      intro h hh
      let : NeZero (n + 3) := ⟨by omega⟩
      let c := P3523T1InsertionConstruction s t
      let e := c.steps.get ⟨h, hh⟩
      have hem : e ∈ c.steps := List.get_mem c.steps ⟨h, hh⟩
      simp only [c, P3523T1InsertionConstruction] at e hem
      rcases List.mem_map.mp hem with ⟨j, hj, heq⟩
      have hjfilter := List.mem_filter.mp hj
      rcases List.mem_ofFn.mp hjfilter.1 with ⟨k, hk⟩
      have hparam : s.parameter j ≠ 0 := of_decide_eq_true hjfilter.2
      have hp : (j - 1) + 1 = j := by simp
      have hs := s.successor (j - 1)
      rw [hp] at hs
      have hsame := OrderedInsertionDetails.hsameAt1300 r n q p s j
          hparam hs
      have hnext := OrderedInsertionDetails.hnext r n q p s j
      have hne := OrderedInsertionDetails.hne r n q p s j hsame
          hnext
      have hlt := OrderedInsertionDetails.hlt r n q p s j
          hparam hs
      let t₀ := s.parameter (j - 1)
      let t₁ := s.parameter j
      let u := (t₁ - t₀) / (1 - t₀)
      have ht₀one : t₀ < 1 := s.parameter_lt_one _
      have ht₁one : t₁ < 1 := s.parameter_lt_one _
      have hden : 1 - t₀ ≠ 0 := ne_of_gt (sub_pos.mpr ht₀one)
      have hu := OrderedInsertionDetails.hu r n q p s j hlt ht₀one ht₁one
      have hc₀ := OrderedInsertionDetails.hc₀ r n q p s j hden
      have hc₁ := OrderedInsertionDetails.hc₁ r n q p s j hden
      have affine (A B : Real × Real) := OrderedInsertionGeometry.affine r n q p
                s j hc₀ hc₁ A B
      have retain (l : List (Fin (n + 3) × Fin (n + 3) × Fin (n + 3)))
          (A : Finset (Fin (n + 3))) (x : Fin (n + 3)) (hx : x ∈ A) :=
              OrderedInsertionDetails.retain n l A x hx
      have hrawNodup := OrderedInsertionDetails.hrawNodup r n q p s
      have hfilterNodup :
          (List.filter (fun j => decide (s.parameter j ≠ 0))
            (List.ofFn fun k : Fin (n + 3) => s.start 0 + k)).Nodup :=
        hrawNodup.filter _
      have htupleInj := OrderedInsertionDetails.htupleInj r n q p s
      have hstepsNodup := OrderedInsertionDetails.hstepsNodup r n q p s X K t
          hfilterNodup htupleInj
      have filterPrev {α : Type} (l : List α) (p : α → Bool) (k h : Nat)
          (hn : l.Nodup) (hk : k < l.length) (hpos : 0 < k)
          (hlen : h < (l.filter p).length)
          (hp : p (l.get ⟨k - 1, by omega⟩) = true)
          (hcur : (l.filter p).get ⟨h, hlen⟩ = l.get ⟨k, hk⟩) :=
              OrderedInsertionGeometry.filterPrev r
              n q s X K t j (α := α) l p k h hn hk hpos hlen hp hcur
      have getNotTake {α : Type} (l : List α) (hn : l.Nodup) (m : Nat)
          (hm : m < l.length) := OrderedInsertionDetails.getNotTake r
              n q p s X K t h j k (α := α) l hn m hm
      have fold_not_mem (l : List (Fin (n + 3) × Fin (n + 3) × Fin (n + 3)))
          (A : Finset (Fin (n + 3))) (x : Fin (n + 3)) (hx : x ∉ A)
          (hall : ∀ a ∈ l, a.2.1 ≠ x) := OrderedInsertionGeometry.fold_not_mem n
              l A x hx hall
      have fold_insert_mem (l : List (Fin (n + 3) × Fin (n + 3) × Fin (n + 3)))
          (A : Finset (Fin (n + 3))) (x : Fin (n + 3))
          (hx : x ∈ A ∨ x ∈ l.map (fun e => e.2.1)) := OrderedInsertionGeometry.fold_insert_mem
              n l A x hx
      let boundaryStep := fun
          (es : Finset (Finset (Fin (n + 3))))
          (e : Fin (n + 3) × Fin (n + 3) × Fin (n + 3)) =>
            insert {e.1, e.2.1}
              (insert {e.2.1, e.2.2} (es.erase {e.1, e.2.2}))
      have keepBoundary (l : List (Fin (n + 3) × Fin (n + 3) × Fin (n + 3)))
          (A : Finset (Finset (Fin (n + 3)))) (P : Finset (Fin (n + 3)))
          (hseed : P ∈ A ∨ ∃ e ∈ l,
            P = {e.1, e.2.1} ∨ P = {e.2.1, e.2.2})
          (hno : ∀ e ∈ l, P ≠ {e.1, e.2.2}) := OrderedInsertionGeometry.keepBoundaryAt383 n l A P
              hseed hno
      let raw := List.ofFn (fun k : Fin (n + 3) => s.start 0 + k)
      let pred := fun z : Fin (n + 3) => decide (s.parameter z ≠ 0)
      have prevTupleMem (hzprev : s.parameter (j - 1) ≠ 0) :=
          OrderedInsertionGeometry.prevTupleMem r n q p s X K t h hh j heq k hk hparam hp
              hrawNodup filterPrev hzprev
      have pairCases {a b c d : Fin (n + 3)} (hab : a ≠ b)
          (h : ({a, b} : Finset (Fin (n + 3))) = {c, d}) :=
              OrderedInsertionGeometry.pairCasesAt487 n (a := a)
              (b := b) (c := c) (d := d) hab h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · change e.1 ≠ e.2.2
        rw [← heq]
        exact hne
      · by_cases hzprev : s.parameter (j - 1) = 0
        · change e.1 ∈ (c.steps.take h).foldl
            (fun vs e => insert e.2.1 vs) (Finset.univ.image s.start)
          rw [← heq]
          rw [hzero (j - 1) hzprev, hsame]
          apply retain
          exact Finset.mem_image.mpr ⟨s.edge j, Finset.mem_univ _, rfl⟩
        · let raw := List.ofFn (fun k : Fin (n + 3) => s.start 0 + k)
          let pred := fun z : Fin (n + 3) => decide (s.parameter z ≠ 0)
          let kp : Fin (n + 3) := ⟨k.val - 1, by omega⟩
          have hrawLen : raw.length = n + 3 := by simp [raw]
          have hkpos := OrderedInsertionDetails.hkpos r n q p s X K t h j k hk hparam
              hp filterPrev
          have hkprev := OrderedInsertionDetails.hkprev r n q p s X K t h j k hp
              hrawLen hkpos
          have hprevLabel := OrderedInsertionDetails.hprevLabel r n q p
              s X K t h j k hk hp hkprev
          have hrawPrev := OrderedInsertionGeometry.hrawPrevAt546 r n q p s X K t h j k hp
              hrawLen hprevLabel
          have hrawCur := OrderedInsertionGeometry.hrawCurAt556 r n q p s j k hk hrawLen
          have hfilterLen : h < (List.filter pred raw).length := by
            simpa [c, P3523T1InsertionConstruction, raw, pred] using hh
          have hfilterCur := OrderedInsertionDetails.hfilterCur r n q p s X K t h hh j heq
              hfilterLen
          have hpred := OrderedInsertionDetails.hpred r n q p s j k hzprev hrawLen hrawPrev
          have hfilteredPrev := filterPrev raw pred k.val h hrawNodup
            (by rw [hrawLen]; exact k.isLt) hkpos hfilterLen hpred
              (hfilterCur.trans hrawCur.symm)
          have hfilteredPrev' := OrderedInsertionDetails.hfilteredPrev' r n q p s h j k hrawLen
              hrawPrev hfilteredPrev
          have htuplePrev := OrderedInsertionDetails.htuplePrev r n q p s X K t h j hfilteredPrev'
          have hlabel : j - 1 ∈ (c.steps.take h).map (fun z => z.2.1) :=
            List.mem_map.mpr ⟨_, htuplePrev, rfl⟩
          change e.1 ∈ (c.steps.take h).foldl
            (fun vs e => insert e.2.1 vs) (Finset.univ.image s.start)
          rw [← heq]
          exact fold_insert_mem _ _ _ (Or.inr hlabel)
      · have hbinit : s.start (s.edge j + 1) ∈ Finset.univ.image s.start := by
          exact Finset.mem_image.mpr ⟨s.edge j + 1, Finset.mem_univ _, rfl⟩
        change e.2.2 ∈ (c.steps.take h).foldl
          (fun vs e => insert e.2.1 vs) (Finset.univ.image s.start)
        rw [← heq]
        exact retain _ _ _ hbinit
      · have hxinit := OrderedInsertionDetails.hxinit r n q p s j
          hparam
        have hprefix := OrderedInsertionGeometry.hprefix r n q
            p s X K t h hh j heq k hstepsNodup
        change e.2.1 ∉ (c.steps.take h).foldl
          (fun vs e => insert e.2.1 vs) (Finset.univ.image s.start)
        rw [← heq]
        exact fold_not_mem _ _ _ hxinit hprefix
      · change {e.1, e.2.2} ∈ (c.steps.take h).foldl boundaryStep
          (Finset.univ.image fun i : Fin (r + 3) =>
            ({s.start i, s.start (i + 1)} : Finset (Fin (n + 3))))
        rw [← heq]
        let P : Finset (Fin (n + 3)) := {j - 1, s.start (s.edge j + 1)}
        have hno := OrderedInsertionGeometry.hno r n q p
            s X K t h hh j heq k hp hsame hne hstepsNodup getNotTake pairCases
        have hseed := OrderedInsertionGeometry.hseed r n q p s X
                  K t hzero h j hsame prevTupleMem
        have hmem := keepBoundary (c.steps.take h)
          (Finset.univ.image fun i : Fin (r + 3) =>
            ({s.start i, s.start (i + 1)} : Finset (Fin (n + 3)))) P hseed hno
        simpa [P, c, P3523T1InsertionConstruction, boundaryStep] using hmem
      · refine ⟨u, hu.1, hu.2, ?_, ?_⟩
        · change p.vertex e.2.1 = (1 - u) • p.vertex e.1 + u • p.vertex e.2.2
          rw [← heq]
          rw [s.vertex_formula j, s.vertex_formula (j - 1),
            s.vertex_formula (s.start (s.edge j + 1))]
          rw [hsame, s.edge_start, s.parameter_start]
          simp only [sub_zero, one_smul, zero_smul]
          rw [add_zero]
          exact affine (q.vertex (s.edge j)) (q.vertex (s.edge j + 1))
        · change P3523T1InterpolatedTarget s t e.2.1 =
            (1 - u) • P3523T1InterpolatedTarget s t e.1 +
              u • P3523T1InterpolatedTarget s t e.2.2
          rw [← heq]
          simp only [P3523T1InterpolatedTarget]
          rw [hsame, s.edge_start, s.parameter_start]
          simp only [sub_zero, one_smul, zero_smul]
          rw [add_zero]
          exact affine (t.target (s.edge j)) (t.target (s.edge j + 1))
    have hvertices := OrderedInsertionGeometry.hvertices r n q p s X K t hzero
    have hboundary := OrderedInsertionDetails.hboundary r n q p s X K t hzero hvalid hvertices
    exact ⟨hvalid, hvertices, hboundary⟩

end ApollonianSuperharmonic

end
