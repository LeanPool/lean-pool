/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Correct.ChunkSplit


/-!
# The reservation process preserves INV-S (Lemma 3.2: reservation and top tag writes)

`splitChunkStart x` links two new, empty chunks `y`, `z` right before and after `x`, then
`insertAround` gives them tags under guards against their chunk-list neighbours. Between the
linking and the tag writes INV-S does not hold (the new chunks still have tag 0), so the proof
follows the computation: the read-only preparation leaves the state unchanged, the two guarded
writes put `ty`, `tz` strictly between their neighbours' tags, and the rest only touches the
top structure.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Frames for `insertAround`'s parts -/

/-- The state relation asserting literal equality of the two cores. -/
def Unchanged (s s' : Core) : Prop := s' = s

instance : IsPre Unchanged where
  refl _ := rfl
  trans _ _ _ h1 h2 := h2.trans h1

theorem pres_roomNextTo_un (t e : Nat) (b : Bool) : Pres Unchanged (roomNextTo t e b) := by
  unfold roomNextTo; pres [pres_getP, pres_getN _]

theorem pres_insertAroundPrep (x : Nat) : Pres Unchanged (insertAroundPrep x) := by
  unfold insertAroundPrep
  pres [pres_getPath _, pres_getN _, pres_getC _, pres_getLpar _, pres_roomNextTo_un _ _ _]

theorem pres_insertAroundFinish (x y z : Nat) (tabs ly lz : List Nat) (lp : Nat) :
    Pres Same (insertAroundFinish x y z tabs ly lz lp) := by
  unfold insertAroundFinish joinChunk
  pres [pres_getP, pres_insertAroundIn _ _ _ _, pres_setPath _ _, pres_setInTables _ _ _,
    pres_setLpar _ _, pres_modN _ _]

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Linking two chunks around `x` -/

section linkc
variable {s : Core} {x y z : Nat}

/-- The hypotheses under which `linkChunkPair` does what it should. -/
structure LinkCOK (s : Core) (x y z : Nat) : Prop where
  szx : x < s.C.size
  szy : y < s.C.size
  szz : z < s.C.size
  szp : cP s x ≠ NIL → cP s x < s.C.size
  szn : cN s x ≠ NIL → cN s x < s.C.size
  d1 : y ≠ z
  d2 : y ≠ x
  d3 : z ≠ x
  d4 : cP s x ≠ y
  d5 : cP s x ≠ z
  d6 : cN s x ≠ y
  d7 : cN s x ≠ z
  d8 : cP s x ≠ x
  d9 : cN s x ≠ x
  d10 : cP s x ≠ NIL → cP s x ≠ cN s x

theorem LinkCOK.cN' (h : LinkCOK s x y z) (w : Nat) :
    cN (linkChunkPair s x y z) w =
      if w = x then z else if w = y then x else if w = z then cN s x
      else if w = cP s x ∧ cP s x ≠ NIL then y else cN s w := by
  obtain ⟨szx, szy, szz, szp, szn, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := h
  simp only [cN, cP] at *
  generalize hp : (s.C.getX x).prev = p at *
  generalize hn : (s.C.getX x).next = n at *
  simp only [linkChunkPair, hp, hn, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, apply_ite (f := Chunk.next)]
  have e1 := Ne.symm d1; have e2 := Ne.symm d2; have e3 := Ne.symm d3; have e4 := Ne.symm d4
  have e5 := Ne.symm d5; have e6 := Ne.symm d6; have e7 := Ne.symm d7; have e8 := Ne.symm d8
  have e9 := Ne.symm d9
  by_cases hwx : w = x
  · simp [hwx, szx,       ]
  · have hwx' := Ne.symm hwx
    by_cases hwy : w = y
    · simp [hwy, szy,  d2, e1, e2, d4, d6, ]
    · have hwy' := Ne.symm hwy
      by_cases hwz : w = z
      · simp [hwz, szz,  d3, e1, e3,  d7, ]
      · have hwz' := Ne.symm hwz
        by_cases hp0 : p = NIL
        · simp [hwx, hwx', hwy, hwy', hwz, hwz', hp0]
        · by_cases hwp : w = p
          · subst hwp
            have := d10 hp0
            simp [hwx, hwy, hwz, hwx',  hwz', hp0, szp hp0,  Ne.symm this]
          · simp [hwx, hwx', hwy, hwy', hwz, hwz', hp0, hwp, Ne.symm hwp]

theorem LinkCOK.cP' (h : LinkCOK s x y z) (w : Nat) :
    cP (linkChunkPair s x y z) w =
      if w = x then y else if w = y then cP s x else if w = z then x
      else if w = cN s x ∧ cN s x ≠ NIL then z else cP s w := by
  obtain ⟨szx, szy, szz, szp, szn, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := h
  simp only [cN, cP] at *
  generalize hp : (s.C.getX x).prev = p at *
  generalize hn : (s.C.getX x).next = n at *
  simp only [linkChunkPair, hp, hn, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, apply_ite (f := Chunk.prev)]
  have e1 := Ne.symm d1; have e2 := Ne.symm d2; have e3 := Ne.symm d3; have e4 := Ne.symm d4
  have e5 := Ne.symm d5; have e6 := Ne.symm d6; have e7 := Ne.symm d7; have e8 := Ne.symm d8
  have e9 := Ne.symm d9
  by_cases hwx : w = x
  · simp [hwx, szx,       ]
  · have hwx' := Ne.symm hwx
    by_cases hwy : w = y
    · simp [hwy, szy,  d2, e1, e2, d4, d6, ]
    · have hwy' := Ne.symm hwy
      by_cases hwz : w = z
      · simp [hwz, szz,  d3, e1, e3,  d7, ]
      · have hwz' := Ne.symm hwz
        by_cases hn0 : n = NIL
        · simp [hwx, hwx', hwy, hwy', hwz, hwz', hn0]
        · by_cases hwn : w = n
          · subst hwn
            simp [hwx, hwy, hwz, hwx',   hn0, szn hn0]
          · simp [hwx, hwx', hwy, hwy', hwz, hwz', hn0, hwn, Ne.symm hwn]

theorem linkChunkPair_cF (w : Nat) : cF (linkChunkPair s x y z) w = cF s w := by
  simp only [linkChunkPair, cF, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, apply_ite (f := Chunk.first)]
  split_ifs <;> rfl

theorem linkChunkPair_cLs (w : Nat) : cLs (linkChunkPair s x y z) w = cLs s w := by
  simp only [linkChunkPair, cLs, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, apply_ite (f := Chunk.last)]
  split_ifs <;> rfl

theorem linkChunkPair_cT (w : Nat) : cT (linkChunkPair s x y z) w = cT s w := by
  simp only [linkChunkPair, cT, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, apply_ite (f := Chunk.tag)]
  split_ifs <;> rfl

theorem linkChunkPair_rest :
    (linkChunkPair s x y z).E = s.E ∧ (linkChunkPair s x y z).Gs = s.Gs ∧
      (linkChunkPair s x y z).freeG = s.freeG ∧ (linkChunkPair s x y z).head = s.head ∧
      (linkChunkPair s x y z).tail = s.tail ∧ (linkChunkPair s x y z).firstGroup = s.firstGroup ∧
      (linkChunkPair s x y z).C.size = s.C.size ∧
      (linkChunkPair s x y z).firstChunk = (if cP s x ≠ NIL then s.firstChunk else y) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [linkChunkPair, Array.size_modify', Array.size_ite]; split_ifs <;> rfl
  · simp only [linkChunkPair, cP, bne_iff_ne, ne_eq]

end linkc

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- A tag write. -/
def withTag (s : Core) (c t : Nat) : Core :=
  { s with C := s.C.modify c fun C => { C with tag := t } }

/-- The state after allocating two chunks. -/
def push2 (s : Core) : Core := { s with C := (s.C.push {}).push {} }

theorem guardedSetTag_run (c t : Nat) (s : Core) :
    ((guardedSetTag c t).run s = .ok () (withTag s c t) ∧ TagOK s c t) ∨
      ∃ msg, (guardedSetTag c t).run s = .error (.guard msg) s := by
  unfold guardedSetTag modC
  rw [run_bind]
  rcases guardTag_run c t s with ⟨hr, hg⟩ | ⟨msg, hr⟩
  · rw [hr]; left; exact ⟨rfl, hg⟩
  · rw [hr]; right; exact ⟨msg, rfl⟩

/-- The abstract nesting after splitting chunk `x` into `y, x, z` (`y`, `z` empty). -/
def Abs.splitChunk (A : Abs) (x y z : Nat) : Abs where
  chunks := A.chunks.replace1 x [y, x, z]
  grps := fun c => if c = y ∨ c = z then [] else A.grps c
  elts := A.elts

/-- Total reads after allocating the two fresh chunks. -/
theorem push2_getX (s : Core) (w : Nat) :
    (push2 s).C.getX w =
      if w = s.C.size ∨ w = s.C.size + 1 then {} else s.C.getX w := by
  simp only [push2, Array.getX_push, Array.size_push]
  by_cases h1 : w = s.C.size + 1
  · simp [h1]
  · by_cases h2 : w = s.C.size
    · simp [h2]
    · simp [h1, h2]

/-- Two guarded tag writes preserve every other field of each chunk. -/
theorem withTag_pair_getX (s : Core) (y ty tz : Nat) (hbound : y + 1 < s.C.size) (w : Nat) :
    (withTag (withTag s y ty) (y + 1) tz).C.getX w =
      { s.C.getX w with
        tag := if w = y + 1 then tz else if w = y then ty else (s.C.getX w).tag } := by
  have hybound : y < s.C.size := by omega
  simp only [withTag, Array.getX_modify, Array.size_modify']
  by_cases h1 : w = y + 1
  · subst h1; simp [hbound]
  · by_cases h2 : w = y
    · subst h2; simp [hybound]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem Abs.splitChunk_glist {A : Abs} {x y z : Nat} (hx : x ∈ A.chunks) (hnd : A.chunks.Nodup)
    (hy : y ∉ A.chunks) (hz : z ∉ A.chunks) (_hxy : x ≠ y) (_hxz : x ≠ z) :
    (A.splitChunk x y z).glist = A.glist := by
  obtain ⟨c1, c2, hcsplit⟩ := List.mem_iff_append.mp hx
  have hnd' := hnd
  rw [hcsplit] at hnd'
  have hx1' : x ∉ c1 := fun h => (List.nodup_append.mp hnd').2.2 x h x (by simp) rfl
  have hgo : ∀ c ∈ A.chunks, (A.splitChunk x y z).grps c = A.grps c := by
    intro c hc
    have h1 : c ≠ y := fun e => hy (e ▸ hc)
    have h2 : c ≠ z := fun e => hz (e ▸ hc)
    simp only [Abs.splitChunk, h1, h2, or_self, ite_false]
  have hgy : (A.splitChunk x y z).grps y = [] := by simp [Abs.splitChunk]
  have hgz : (A.splitChunk x y z).grps z = [] := by simp [Abs.splitChunk]
  unfold Abs.glist
  have hch : (A.splitChunk x y z).chunks = c1 ++ y :: x :: z :: c2 := by
    simp [Abs.splitChunk, hcsplit, replace1_mid hx1']
  rw [hch, hcsplit, List.flatMap_append, List.flatMap_append, List.flatMap_cons,
    List.flatMap_cons, List.flatMap_cons, List.flatMap_cons, hgy, hgz, hgo x hx]
  have e1 : c1.flatMap (A.splitChunk x y z).grps = c1.flatMap A.grps :=
    List.flatMap_congr fun c hc => hgo c (by rw [hcsplit]; simp [hc])
  have e2 : c2.flatMap (A.splitChunk x y z).grps = c2.flatMap A.grps :=
    List.flatMap_congr fun c hc => hgo c (by rw [hcsplit]; simp [hc])
  rw [e1, e2]; simp


/-- Linking two fresh chunks preserves the doubly linked chunk list. -/
private theorem splitChunk_llist {s s1 t : Core} {A : Abs} {x y p n : Nat}
    {c1 c2 : List Nat} (hLbase : LList (cN s) (cP s) s.firstChunk A.chunks)
    (hcsplit : A.chunks = c1 ++ x :: c2)
    (hch' : (A.splitChunk x y (y + 1)).chunks = c1 ++ y :: x :: (y + 1) :: c2)
    (hyA : y ∉ A.chunks) (hzA : y + 1 ∉ A.chunks) (hypos : 1 ≤ y) (hxs : x < y)
    (hpdef : cP s x = p) (hndef : cN s x = n)
    (hfc : t.firstChunk = if p ≠ NIL then s.firstChunk else y)
    (hN : ∀ w, cN t w = if w = x then y + 1 else if w = y then x
      else if w = y + 1 then n else if w = p ∧ p ≠ NIL then y else cN s1 w)
    (hP : ∀ w, cP t w = if w = x then y else if w = y then p
      else if w = y + 1 then x else if w = n ∧ n ≠ NIL then y + 1 else cP s1 w)
    (cN1 : ∀ w, w ≠ y → w ≠ y + 1 → cN s1 w = cN s w)
    (cP1 : ∀ w, w ≠ y → w ≠ y + 1 → cP s1 w = cP s w) :
    LList (cN t) (cP t) t.firstChunk (A.splitChunk x y (y + 1)).chunks := by
  have hnil := hLbase.nonil
  rw [hch']
  have hL := hLbase
  rw [hcsplit] at hL
  have := LList.insert_around (nxt' := cN t) (prv' := cP t) hL
    (by rw [← hcsplit]; exact hyA) (by rw [← hcsplit]; exact hzA) (by omega)
    (by unfold NIL; omega) (by unfold NIL; omega) (fun w hw => ?_) (fun w hw => ?_)
  · rw [hpdef] at this
    rw [hfc]
    by_cases hp0 : p = NIL
    · rw [ite_eq_left hp0] at this; rw [ite_eq_right (not_not.mpr hp0)]; exact this
    · rw [ite_eq_right hp0] at this; rw [ite_eq_left hp0]; exact this
  · rw [hN, hpdef, hndef]
    have hw0 : w ≠ NIL := fun e => by
      rw [e] at hw; rcases mem_around_iff.mp hw with h | h | h
      · unfold NIL at h; omega
      · unfold NIL at h; omega
      · exact hnil (hcsplit ▸ h)
    by_cases h1 : w = y; · simp [h1, show y ≠ x by omega]
    by_cases h2 : w = x; · simp [h2, show x ≠ y by omega]
    by_cases h3 : w = y + 1; · simp [h3, show y + 1 ≠ x by omega]
    by_cases h4 : w = p
    · subst h4; simp [h1, h2, h3, hw0]
    · simp only [h1, h2, h3, h4, ite_false, false_and]
      exact cN1 w h1 h3
  · rw [hP, hpdef, hndef]
    have hw0 : w ≠ NIL := fun e => by
      rw [e] at hw; rcases mem_around_iff.mp hw with h | h | h
      · unfold NIL at h; omega
      · unfold NIL at h; omega
      · exact hnil (hcsplit ▸ h)
    by_cases h1 : w = y; · simp [h1, show y ≠ x by omega]
    by_cases h2 : w = x; · simp [h2, show x ≠ y by omega]
    by_cases h3 : w = y + 1; · simp [h3, show y + 1 ≠ x by omega]
    by_cases h4 : w = n
    · subst h4; simp [h1, h2, h3, hw0]
    · simp only [h1, h2, h3, h4, ite_false, false_and]
      exact cP1 w h1 h3

/-- The two guarded tags fit into the old strictly increasing chunk order. -/
private theorem splitChunk_tags {s s1 s2 s3 t : Core} {A : Abs} {x y p n ty tz : Nat}
    {c1 c2 : List Nat} (hI : INV s A) (hx : x ∈ A.chunks)
    (hcsplit : A.chunks = c1 ++ x :: c2)
    (hch' : (A.splitChunk x y (y + 1)).chunks = c1 ++ y :: x :: (y + 1) :: c2)
    (hyA : y ∉ A.chunks) (hzA : y + 1 ∉ A.chunks)
    (hxs : x < y) (hx1 : 1 ≤ x) (hpy : p < y) (hny : n < y)
    (hpdef : cP s x = p) (hndef : cN s x = n)
    (hs2 : s2 = linkChunkPair s1 x y (y + 1)) (hs3 : s3 = withTag s2 y ty)
    (h1C : ∀ w, s1.C.getX w = if w = y ∨ w = y + 1 then {} else s.C.getX w)
    (cN2 : ∀ w, cN s2 w = if w = x then y + 1 else if w = y then x
      else if w = y + 1 then n else if w = p ∧ p ≠ NIL then y else cN s1 w)
    (cP2 : ∀ w, cP s2 w = if w = x then y else if w = y then p
      else if w = y + 1 then x else if w = n ∧ n ≠ NIL then y + 1 else cP s1 w)
    (cT4 : ∀ w, cT t w = if w = y + 1 then tz else if w = y then ty
      else if w = y ∨ w = y + 1 then 0 else cT s w)
    (hy : TagOK s2 y ty) (hz : TagOK s3 (y + 1) tz) :
    ((A.splitChunk x y (y + 1)).chunks.map (cT t)).IsChain (· < ·) := by
  have hnil := hI.cList.nonil
  have hcnd' := hI.cList.nodup
  rw [hcsplit] at hcnd'
  rw [hch']
  have hs := hI.cSorted
  rw [hcsplit] at hs
  refine isChain_around hs (fun w hw => ?_) ?_ ?_ ?_ ?_
  · have hwA : w ∈ A.chunks := hcsplit ▸ hw
    have h1 : w ≠ y := fun e => hyA (e ▸ hwA)
    have h2 : w ≠ y + 1 := fun e => hzA (e ▸ hwA)
    rw [cT4, ite_eq_right h2, ite_eq_right h1, ite_eq_right (by omega)]
  · intro w hw
    rw [cT4, ite_eq_right (by omega), ite_eq_left rfl]
    -- `w` is `x`'s predecessor
    have hwp : w = p := by
      rw [← hpdef, hI.cList.prev x hx, hcsplit, predOf_mid hcnd']
      rcases c1.eq_nil_or_concat with h | ⟨c1', a, rfl⟩
      · subst h; simp at hw
      · simp at hw; simp [hw]
    have hp0 : p ≠ NIL := fun e => hnil (by
      rw [hcsplit, ← e, ← hwp]
      simp [List.mem_of_getLast? hw])
    have := hy.1 (by rw [cP2]; simp [show y ≠ x by omega, hp0])
    rw [cP2] at this
    simp only [show y ≠ x by omega, ite_false, ite_true] at this
    rw [hwp]
    have hpne : p ≠ y ∧ p ≠ y + 1 := ⟨by omega, by omega⟩
    rw [show cT s2 p = cT s p by
      rw [hs2, linkChunkPair_cT]; simp only [cT, h1C, hpne.1, hpne.2, or_self, ite_false]] at this
    exact this
  · have c1 : cT t y = ty := by rw [cT4]; simp []
    rw [c1]
    have := hy.2 (by
      rw [cN2]
      simp only [show y ≠ x by omega, ↓reduceIte, ne_eq]
      unfold NIL
      omega)
    rw [cN2] at this
    simp only [show y ≠ x by omega, ite_false, ite_true] at this
    rw [show cT s2 x = cT s x by
      rw [hs2, linkChunkPair_cT]; simp only [cT, h1C, show x ≠ y by omega,
        show x ≠ y + 1 by omega, or_self, ite_false]] at this
    exact this
  · have c1 : cT t (y + 1) = tz := by rw [cT4]; simp
    rw [c1]
    have := hz.1 (by
      simp only [hs3, withTag, cP, Array.getX_modify, show y ≠ y + 1 by omega, false_and,
        ite_false]
      change cP s2 (y + 1) ≠ NIL
      rw [cP2]; simp only [show y + 1 ≠ x by omega, ↓reduceIte,
          Nat.succ_ne_self,  ne_eq]; unfold NIL; omega)
    have hzp : cP s3 (y + 1) = x := by
      simp only [hs3, withTag, cP, Array.getX_modify, show y ≠ y + 1 by omega, false_and,
        ite_false]
      change cP s2 (y + 1) = x
      rw [cP2]; simp only [show y + 1 ≠ x by omega, ↓reduceIte,
          Nat.succ_ne_self]
    rw [hzp] at this
    rw [show cT s3 x = cT s x by
      simp only [hs3, withTag, cT, Array.getX_modify, show y ≠ x by omega, false_and, ite_false]
      change cT s2 x = cT s x
      rw [hs2, linkChunkPair_cT]; simp only [cT, h1C, show x ≠ y by omega,
        show x ≠ y + 1 by omega, or_self, ite_false]] at this
    exact this
  · intro w hw
    rw [cT4, ite_eq_left rfl]
    have hwn : w = n := by
      rw [← hndef, hI.cList.next x hx, hcsplit, succOf_mid hcnd']
      cases c2 with
      | nil => simp at hw
      | cons a t => simp at hw; simp [hw]
    have hwA : w ∈ A.chunks := by rw [hcsplit]; cases c2 with
      | nil => simp at hw
      | cons a t => simp at hw; simp [hw]
    have hn0 : n ≠ NIL := fun e => hnil (by rw [← e, ← hwn]; exact hwA)
    have hzn : cN s3 (y + 1) = n := by
      simp only [hs3, withTag, cN, Array.getX_modify, show y ≠ y + 1 by omega, false_and,
        ite_false]
      change cN s2 (y + 1) = n
      rw [cN2]; simp only [show y + 1 ≠ x by omega, ↓reduceIte,
          Nat.succ_ne_self]
    have := hz.2 (by rw [hzn]; exact hn0)
    rw [hzn] at this
    rw [hwn]
    have hny' : n ≠ y ∧ n ≠ y + 1 := ⟨by omega, by omega⟩
    rw [show cT s3 n = cT s n by
      simp only [hs3, withTag, cT, Array.getX_modify, Ne.symm hny'.1, false_and, ite_false]
      change cT s2 n = cT s n
      rw [hs2, linkChunkPair_cT]; simp only [cT, h1C, hny'.1, hny'.2, or_self, ite_false]] at this
    exact this

/-- **Linking two new chunks around `x` and tagging them (under their guards) preserves INV-S.** -/
theorem inv_splitChunk {s : Core} {A : Abs} (hI : INV s A) {x ty tz : Nat}
    (hx : x ∈ A.chunks)
    (hy : TagOK (linkChunkPair (push2 s) x s.C.size (s.C.size + 1)) s.C.size ty)
    (hz : TagOK (withTag (linkChunkPair (push2 s) x s.C.size (s.C.size + 1)) s.C.size ty)
      (s.C.size + 1) tz) :
    INV (withTag (withTag (linkChunkPair (push2 s) x s.C.size (s.C.size + 1)) s.C.size ty)
      (s.C.size + 1) tz) (A.splitChunk x s.C.size (s.C.size + 1)) := by
  generalize hydef : s.C.size = y at hy hz ⊢
  have hxs : x < y := hydef ▸ ((hI.cAlloc x).mp hx).2
  have hx1 : 1 ≤ x := ((hI.cAlloc x).mp hx).1
  set s1 := push2 s with hs1
  set s2 := linkChunkPair s1 x y (y + 1) with hs2
  set s3 := withTag s2 y ty with hs3
  set s4 := withTag s3 (y + 1) tz with hs4
  -- `push2`
  have h1C : ∀ w, s1.C.getX w = if w = y ∨ w = y + 1 then {} else s.C.getX w := by
    intro w
    simpa only [hydef] using push2_getX s w
  have h1sz : s1.C.size = y + 2 := by simp [hs1, push2, hydef]
  have hnil := hI.cList.nonil
  have hcnd := hI.cList.nodup
  generalize hpdef : cP s x = p
  generalize hndef : cN s x = n
  have hpm : p = NIL ∨ p ∈ A.chunks := by
    rw [← hpdef, hI.cList.prev x hx]
    exact (predOf_mem_or (l := A.chunks) (x := x)).elim Or.inr Or.inl
  have hnm : n = NIL ∨ n ∈ A.chunks := by
    rw [← hndef, hI.cList.next x hx]
    exact (succOf_mem_or (l := A.chunks) (x := x)).elim Or.inr Or.inl
  have hmem_lt : ∀ c ∈ A.chunks, c < y := fun c hc => hydef ▸ ((hI.cAlloc c).mp hc).2
  have hp1 : cP s1 x = p := by
    simp only [cP, h1C, show x ≠ y by omega,
      show x ≠ y + 1 by omega]
    simp [hpdef]
  have hn1 : cN s1 x = n := by
    simp only [cN, h1C, show x ≠ y by omega,
      show x ≠ y + 1 by omega]
    simp [hndef]
  have hlt : ∀ c, c = NIL ∨ c ∈ A.chunks → c < y := by
    intro c hc; rcases hc with h | h
    · rw [h]; unfold NIL; omega
    · exact hmem_lt c h
  have hpy : p < y := hlt p hpm
  have hny : n < y := hlt n hnm
  have hpx : p ≠ x := by
    rw [← hpdef, hI.cList.prev x hx]
    exact predOf_ne_self hcnd x (by unfold NIL; omega)
  have hnx : n ≠ x := by
    rw [← hndef, hI.cList.next x hx]
    exact succOf_ne_self hcnd x (by unfold NIL; omega)
  have hpn : p ≠ NIL → p ≠ n := by
    intro h0; rw [← hpdef, ← hndef, hI.cList.prev x hx, hI.cList.next x hx]
    exact predOf_ne_succOf hcnd hx (by rw [← hI.cList.prev x hx, hpdef]; exact h0)
  have hLink : LinkCOK s1 x y (y + 1) := by
    refine ⟨by omega, by omega, by omega, fun h => by rw [hp1] at h ⊢; omega,
      fun h => by rw [hn1] at h ⊢; omega, by omega, by omega, by omega,
      by rw [hp1]; omega, by rw [hp1]; omega, by rw [hn1]; omega, by rw [hn1]; omega,
      by rw [hp1]; exact hpx, by rw [hn1]; exact hnx, fun h => by rw [hp1, hn1] at *; exact hpn h⟩
  obtain ⟨rE, rG, rF, rH, rT, rFG, rCs, rFC⟩ :=
    linkChunkPair_rest (s := s1) (x := x) (y := y) (z := y + 1)
  -- accessors of `s4`
  have hC4 : ∀ w, s4.C.getX w = { s2.C.getX w with
      tag := if w = y + 1 then tz else if w = y then ty else (s2.C.getX w).tag } := by
    intro w
    exact withTag_pair_getX s2 y ty tz (by rw [hs2, rCs, h1sz]; omega) w
  have cN4 : ∀ w, cN s4 w = cN s2 w := by intro w; simp only [cN, hC4]
  have cP4 : ∀ w, cP s4 w = cP s2 w := by intro w; simp only [cP, hC4]
  have cF4 : ∀ w, cF s4 w = cF s2 w := by intro w; simp only [cF, hC4]
  have cLs4 : ∀ w, cLs s4 w = cLs s2 w := by intro w; simp only [cLs, hC4]
  have cT4 : ∀ w, cT s4 w = if w = y + 1 then tz else if w = y then ty
      else (if w = y ∨ w = y + 1 then 0 else cT s w) := by
    intro w; simp only [cT, hC4]
    rw [show (s2.C.getX w).tag = cT s2 w from rfl, hs2, linkChunkPair_cT]
    simp only [cT, h1C]
    by_cases h1 : w = y + 1; · simp [h1]
    by_cases h2 : w = y; · simp [h2]
    simp [h1, h2]
  have cN2 := hLink.cN'
  have cP2 := hLink.cP'
  rw [hp1, hn1] at cN2 cP2
  have cN1 : ∀ w, w ≠ y → w ≠ y + 1 → cN s1 w = cN s w := by
    intro w h1 h2; simp only [cN, h1C, h1, h2, false_or, ite_false]
  have cP1 : ∀ w, w ≠ y → w ≠ y + 1 → cP s1 w = cP s w := by
    intro w h1 h2; simp only [cP, h1C, h1, h2, false_or, ite_false]
  have cF1 : ∀ w, cF s1 w = if w = y ∨ w = y + 1 then NIL else cF s w := by
    intro w; simp only [cF, h1C]; split <;> rfl
  have cLs1 : ∀ w, cLs s1 w = if w = y ∨ w = y + 1 then NIL else cLs s w := by
    intro w; simp only [cLs, h1C]; split <;> rfl
  have hE4 : s4.E = s.E := rE
  have hG4 : s4.Gs = s.Gs := rG
  have hT4 : s4.tail = s.tail := rT
  have hH4 : s4.head = s.head := rH
  have hF4 : s4.freeG = s.freeG := rF
  have hFG4 : s4.firstGroup = s.firstGroup := rFG
  have hCs4 : s4.C.size = y + 2 := by
    rw [hs4, hs3]; simp only [withTag, Array.size_modify']; rw [hs2, rCs, h1sz]
  -- the abstract nesting
  obtain ⟨c1, c2, hcsplit⟩ := List.mem_iff_append.mp hx
  have hcnd' := hcnd
  rw [hcsplit] at hcnd'
  have hx1' : x ∉ c1 := fun h => (List.nodup_append.mp hcnd').2.2 x h x (by simp) rfl
  have hch' : (A.splitChunk x y (y + 1)).chunks = c1 ++ y :: x :: (y + 1) :: c2 := by
    simp [Abs.splitChunk, hcsplit, replace1_mid hx1']
  have hyA : y ∉ A.chunks := fun h => absurd (hmem_lt y h) (by omega)
  have hzA : y + 1 ∉ A.chunks := fun h => absurd (hmem_lt (y + 1) h) (by omega)
  have hmem' : ∀ c, c ∈ (A.splitChunk x y (y + 1)).chunks ↔ c = y ∨ c = y + 1 ∨ c ∈ A.chunks := by
    intro c; rw [hch', hcsplit]; exact mem_around_iff
  have hgl' : (A.splitChunk x y (y + 1)).glist = A.glist :=
    Abs.splitChunk_glist hx hcnd hyA hzA (by omega) (by omega)
  have hel' : (A.splitChunk x y (y + 1)).elist = A.elist := by
    unfold Abs.elist; rw [hgl']; rfl
  refine
    { eList := ?_, eAlloc := ?_, tail := ?_, gList := ?_, gAlloc := ?_, gPos := ?_, gAlive := ?_,
      gOut := ?_, free := ?_, freeNodup := ?_, cList := ?_, cAlloc := ?_, cOut := ?_,
      gEnds := ?_, cEnds := ?_, grp := ?_, chk := ?_, eSorted := ?_, gSorted := ?_,
      cSorted := ?_ }
  · have e1 : eN s4 = eN s := by funext e; simp [eN, hE4]
    have e2 : eP s4 = eP s := by funext e; simp [eP, hE4]
    rw [hel', e1, e2, hH4]; exact hI.eList
  · rw [hel', hE4]; exact hI.eAlloc
  · rw [hel', hT4]; exact hI.tail
  · have e1 : gN s4 = gN s := by funext g; simp [gN, hG4]
    have e2 : gP s4 = gP s := by funext g; simp [gP, hG4]
    rw [hgl', e1, e2, hFG4]; exact hI.gList
  · rw [hgl', hG4]; exact hI.gAlloc
  · rw [hG4]; exact hI.gPos
  · intro g h1 h2; rw [hgl']; rw [hG4] at h2; simp only [gA, hG4]; exact hI.gAlive g h1 h2
  · intro g hg; rw [hgl'] at hg; simp only [gN, gP, hG4]; exact hI.gOut g hg
  · rw [hgl', hF4, hG4]; exact hI.free
  · rw [hF4]; exact hI.freeNodup
  · apply splitChunk_llist hI.cList hcsplit hch' hyA hzA (by omega) hxs hpdef hndef
      (s1 := s1)
    · change (linkChunkPair s1 x y (y + 1)).firstChunk = _
      rw [rFC, hp1]
      rfl
    · intro w; rw [cN4, cN2]
    · intro w; rw [cP4, cP2]
    · exact cN1
    · exact cP1
  · intro c
    rw [hmem', hCs4, hI.cAlloc c, hydef]
    constructor
    · rintro (rfl | rfl | ⟨h1, h2⟩) <;> omega
    · rintro ⟨h1, h2⟩
      by_cases ha : c = y; · exact Or.inl ha
      by_cases hb : c = y + 1; · exact Or.inr (Or.inl hb)
      exact Or.inr (Or.inr ⟨h1, by omega⟩)
  · intro c hc
    rw [hmem'] at hc
    push Not at hc
    obtain ⟨h1, h2, h3⟩ := hc
    have hcp : ¬ (c = p ∧ p ≠ NIL) := fun ⟨e, hp0⟩ => h3 (by
      exact hpm.elim (fun hp => False.elim (hp0 hp)) (fun hm => e ▸ hm))
    have hcn : ¬ (c = n ∧ n ≠ NIL) := fun ⟨e, hn0⟩ => h3 (by
      exact hnm.elim (fun hn => False.elim (hn0 hn)) (fun hm => e ▸ hm))
    have hcx : c ≠ x := fun e => h3 (e ▸ hx)
    rw [cN4, cP4, cF4, cN2, cP2, hs2, linkChunkPair_cF, cF1]
    simp only [hcx, h1, h2, hcp, hcn, ite_false, or_self]
    rw [cN1 c h1 h2, cP1 c h1 h2]
    exact hI.cOut c h3
  · intro g hg; rw [hgl'] at hg; simp only [gF, gLs, hG4]; exact hI.gEnds g hg
  · intro c hc
    rw [hmem'] at hc
    rw [cF4, cLs4, hs2, linkChunkPair_cF, linkChunkPair_cLs, cF1, cLs1]
    simp only [Abs.splitChunk]
    rcases hc with rfl | rfl | hc
    · simp [Ends]
    · simp [Ends]
    · have h1 : c ≠ y := fun e => hyA (e ▸ hc)
      have h2 : c ≠ y + 1 := fun e => hzA (e ▸ hc)
      simp only [h1, h2, or_self, ite_false]
      exact hI.cEnds c hc
  · intro g hg e he; rw [hgl'] at hg; simp only [eG, hE4]; exact hI.grp g hg e he
  · intro c hc g hg
    rw [hmem'] at hc
    simp only [Abs.splitChunk] at hg
    rcases hc with rfl | rfl | hc
    · simp at hg
    · simp at hg
    · have h1 : c ≠ y := fun e => hyA (e ▸ hc)
      have h2 : c ≠ y + 1 := fun e => hzA (e ▸ hc)
      simp only [h1, h2, or_self, ite_false] at hg
      simp only [gC, hG4]; exact hI.chk c hc g hg
  · intro g hg; rw [hgl'] at hg
    have : eL s4 = eL s := by funext e; simp [eL, hE4]
    rw [this]; exact hI.eSorted g hg
  · intro c hc
    rw [hmem'] at hc
    have : gL s4 = gL s := by funext g; simp [gL, hG4]
    rw [this]
    simp only [Abs.splitChunk]
    rcases hc with rfl | rfl | hc
    · simp
    · simp
    · have h1 : c ≠ y := fun e => hyA (e ▸ hc)
      have h2 : c ≠ y + 1 := fun e => hzA (e ▸ hc)
      simp only [h1, h2, or_self, ite_false]
      exact hI.gSorted c hc
  · exact splitChunk_tags hI hx hcsplit hch' hyA hzA hxs hx1 hpy hny hpdef hndef
      hs2 hs3 h1C cN2 cP2 cT4 hy hz

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem run_newChunk_bind {β : Type} (k : Nat → CM β) (s : Core) :
    (newChunk >>= k).run s = (k s.C.size).run { s with C := s.C.push {} } := rfl

theorem pres_markSplit (x y z : Nat) (job : Job) : Pres Same (markSplit x y z job) := by
  unfold markSplit modC; pres <;> same

theorem Same.eframe {s s' : Core} (h : Same s s') : EFrame s s' := h.1.eframe


theorem withTag_eframe (s : Core) (c t : Nat) : EFrame s (withTag s c t) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl⟩

theorem good_splitChunkStart (x : Nat) : Good (splitChunkStart x) := by
  intro s A hI
  unfold splitChunkStart
  simp only [run_get_bind, run_require_bind]
  by_cases hv : (x != NIL && decide (x < s.C.size)) = true
  swap
  · rw [ite_eq_right hv]; exact EFrame.refl s
  rw [ite_eq_left hv]
  simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at hv
  have hx : x ∈ A.chunks := (hI.cAlloc x).mpr ⟨by have := hv.1; unfold NIL at this; omega, hv.2⟩
  simp only [run_newChunk_bind, run_modify_bind, Array.size_push]
  have hps : ({ ({ s with C := s.C.push {} } : Core) with C := (s.C.push {}).push {} } : Core) =
      push2 s := rfl
  rw [hps]
  -- E and the other element fields are untouched up to the linked state
  have hE2 : EFrame s (linkChunkPair (push2 s) x s.C.size (s.C.size + 1)) :=
    ⟨by simp [linkChunkPair,
      push2], fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl⟩
  have hInv := fun ty tz => inv_splitChunk (ty := ty) (tz := tz) hI hx
  generalize hs2 : linkChunkPair (push2 s) x s.C.size (s.C.size + 1) = s2 at hE2 hInv
  rw [run_bind]
  unfold insertAround
  rw [run_bind]
  have hprep := pres_insertAroundPrep x s2
  rcases hpr : (insertAroundPrep x).run s2 with ⟨⟨ty, tz, tabs, ly, lz, lp⟩, s2'⟩ | ⟨e, s2'⟩
  · rw [hpr] at hprep
    simp only [Unchanged] at hprep
    subst hprep
    simp only
    rw [run_bind]
    rcases guardedSetTag_run s.C.size ty s2' with ⟨hr1, hg1⟩ | ⟨msg, hr1⟩
    · rw [hr1]
      simp only
      rw [run_bind]
      rcases guardedSetTag_run (s.C.size + 1) tz (withTag s2' s.C.size ty) with
        ⟨hr2, hg2⟩ | ⟨msg, hr2⟩
      · rw [hr2]
        simp only
        have hI4 := hInv ty tz hg1 hg2
        have hfin := pres_insertAroundFinish x s.C.size (s.C.size + 1) tabs ly lz lp
          (withTag (withTag s2' s.C.size ty) (s.C.size + 1) tz)
        rcases hf : (insertAroundFinish x s.C.size (s.C.size + 1) tabs ly lz lp).run
            (withTag (withTag s2' s.C.size ty) (s.C.size + 1) tz) with ⟨job, s5⟩ | ⟨e, s5⟩
        · rw [hf] at hfin
          simp only
          have hm := pres_markSplit x s.C.size (s.C.size + 1) job s5
          rcases hmr : (markSplit x s.C.size (s.C.size + 1) job).run s5 with ⟨u, s6⟩ | ⟨e, s6⟩
          · rw [hmr] at hm
            have h46 : Same (withTag (withTag s2' s.C.size ty) (s.C.size + 1) tz) s6 :=
              IsPre.trans _ _ _ hfin hm
            refine ⟨hE2.trans (EFrame.trans ((withTag_eframe _ _ _).trans
              (withTag_eframe _ _ _)) h46.eframe), _, hI4.of_sameLinks h46.1 h46.2, ?_⟩
            have hlt : ∀ c ∈ A.chunks, c < s.C.size := fun c hc => ((hI.cAlloc c).mp hc).2
            unfold Abs.elist
            rw [Abs.splitChunk_glist hx hI.cList.nodup (fun h => by have := hlt _ h; omega)
              (fun h => by have := hlt _ h; omega) (by have := hlt x hx; omega)
              (by have := hlt x hx; omega)]
            rfl
          · rw [hmr] at hm
            cases e with
            | guard _ =>
              exact hE2.trans (EFrame.trans ((withTag_eframe _ _ _).trans (withTag_eframe _ _ _))
                (IsPre.trans _ _ _ hfin hm : Same _ _).eframe)
            | bug _ => exact hm
        · rw [hf] at hfin
          cases e with
          | guard _ =>
            exact hE2.trans (EFrame.trans ((withTag_eframe _ _ _).trans (withTag_eframe _ _ _))
              hfin.eframe)
          | bug _ => exact hfin
      · rw [hr2]
        exact hE2.trans (withTag_eframe _ _ _)
    · rw [hr1]; exact hE2
  · rw [hpr] at hprep
    cases e with
    | guard _ => simp only [Unchanged] at hprep; subst hprep; exact hE2
    | bug _ => exact hprep

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem good_setResJob (r : Option Job) :
    Good (modify fun s => { s with resJob := r } : CM PUnit) :=
  Good.of_pres (Pres.same_safe (Pres.modify (by same)))

theorem good_reservation (k : Nat) : Good (reservation k) := by
  unfold reservation
  good [Good.of_pres pres_pqEmpty, Good.of_pres pres_pqPopMax.same_safe, good_splitChunkStart _,
    Good.of_pres (pres_jobStep _), good_setResJob _]

/-- **Lemma 3.2 for the background work of one insertion.** -/
theorem good_background (y : Nat) : Good (background y) := by
  unfold background
  good [Good.of_pres pres_getP, Good.of_pres (pres_getE _), Good.of_pres (pres_getG _),
    Good.of_pres (pres_chunkSize _ _).same_safe, good_startGroupSplit _, good_driveGroup _,
    good_driveChunk _, good_reservation _]

end OrderMaintenance.Proof
