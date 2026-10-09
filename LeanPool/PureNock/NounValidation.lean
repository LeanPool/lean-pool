/-
Copyright (c) 2026 Pure Nock formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pure Nock formalization contributors
-/

module

public import LeanPool.PureNock.Tree
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Ring.Nat

/-!
# Structural noun validation

`Lem:decomp`, `Algorithm:Valid_Noun`, and `Thm:Noun_Validation`
(`main.tex:1206–1270`) over Nat-labelled nouns.
-/

@[expose] public section

namespace Nock

/-! ### `Lem:decomp` (`main.tex:1210–1213`) -/

namespace Noun

-- main.tex:1210–1213
/-- **`Lem:decomp`** (`main.tex:1210–1213`).
    ∃! λ_L, λ_R ∈ ℕ₊ s.t. λ = λ_L + λ_R, n_L ∈ N^{λ_L}(F), n_R ∈ N^{λ_R}(F)
    ⇔ n = cons(n_L,n_R), n ∈ N^λ(F).
    (Lean ∃ also includes `n = cons(n_L,n_R)` per CORRESPONDENCE note 3.) -/
theorem decomp (n nL nR : Noun) (lam : ℕ) :
    (∃! p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ lam = p.1 + p.2 ∧
        nL.leaves = p.1 ∧ nR.leaves = p.2 ∧ n = Noun.cell nL nR)
      ↔ (n = Noun.cell nL nR ∧ n.leaves = lam) := by
  constructor
  · rintro ⟨p, ⟨_, _, hsum, hL, hR, hcons⟩, _⟩
    refine ⟨hcons, ?_⟩
    subst hcons
    simp only [Noun.leaves]
    omega
  · rintro ⟨hcons, hlen⟩
    refine ⟨(nL.leaves, nR.leaves),
      ⟨nL.one_le_leaves, nR.one_le_leaves, ?_, rfl, rfl, hcons⟩, ?_⟩
    · subst hcons; simp only [Noun.leaves] at hlen; omega
    · rintro q ⟨_, _, _, hqL, hqR, _⟩
      exact Prod.ext_iff.mpr ⟨hqL.symm, hqR.symm⟩

/-- The structural core of `Lem:decomp`: the children of a `cons` are unique — `cons` is
    injective, so the decomposition `n = cons(nL,nR)` is well-defined (main.tex:1208). -/
theorem cons_children_unique {l r l' r' : Noun} (h : Noun.cell l r = Noun.cell l' r') :
    l = l' ∧ r = r' := by
  injection h with h₁ h₂; exact ⟨h₁, h₂⟩

end Noun

/-! ### `Algorithm:Valid_Noun` (`main.tex:1244–1260`) -/

/-- A transcript entry `(n, n_L?/n_R?)` — the paper's `t_i = (n, n_L, n_R)`. -/
abbrev Transcript := List (Noun × Option (Noun × Noun))

/-- **`Algorithm:Valid_Noun`** (`main.tex:1244–1260`), one step of `CheckValidNoun`:
    parse `(n,n_L,n_R) ← t_i`; if `n ∉ mset` Reject; erase `n`; if atom require
    `n_L,n_R = ⊥` else require `n = cons(n_L,n_R)` and push `{n_L,n_R}`. `none` = Reject. -/
def stepMset (m : Multiset Noun) (n : Noun) (ch : Option (Noun × Noun)) :
    Option (Multiset Noun) :=
  match n, ch with
  | Noun.atom k, none => if Noun.atom k ∈ m then some (m.erase (Noun.atom k)) else none
  | Noun.cell a b, some (a', b') =>
      if Noun.cell a b ∈ m ∧ a = a' ∧ b = b' then
        some (a ::ₘ b ::ₘ m.erase (Noun.cell a b)) else none
  | _, _ => none

/-- Run the whole transcript, threading the multiset; `none` on any `Reject`. -/
def runMset : Multiset Noun → Transcript → Option (Multiset Noun)
  | m, [] => some m
  | m, (n, ch) :: ts =>
      match stepMset m n ch with
      | some m' => runMset m' ts
      | none => none

theorem runMset_cons {m m' : Multiset Noun} {n : Noun} {ch : Option (Noun × Noun)}
    {ts : Transcript} (h : stepMset m n ch = some m') :
    runMset m ((n, ch) :: ts) = runMset m' ts := by
  simp only [runMset, h]

/-- Accept / Reject, the output of `CheckValidNoun`. -/
inductive Result where
  | accept : Result
  | reject : Result
deriving DecidableEq, Repr

/-- **`Algorithm:Valid_Noun`** (`main.tex:1244–1260`).
    `CheckValidNoun(n₀;T)`: init `mset = {n₀}`; while `mset ≠ ∅` process `t_i` as in
    `stepMset`; if `mset = ∅` return Accept else Reject. -/
def checkValidNoun (n₀ : Noun) (T : Transcript) : Result :=
  match runMset {n₀} T with
  | some m => if m = 0 then Result.accept else Result.reject
  | none => Result.reject

theorem checkValidNoun_accept_iff (n₀ : Noun) (T : Transcript) :
    checkValidNoun n₀ T = Result.accept ↔ runMset {n₀} T = some 0 := by
  unfold checkValidNoun
  cases hr : runMset {n₀} T with
  | none => simp
  | some m =>
      by_cases hz : m = 0
      · subst hz; simp
      · simp [hz]

/-! ### Total node count of the multiset, and its decrease under each step -/

/-- Total node count across a multiset of nouns (`Σ size`). -/
def msize (m : Multiset Noun) : ℕ := (m.map Noun.size).sum

@[simp] theorem msize_zero : msize (0 : Multiset Noun) = 0 := by simp [msize]

@[simp] theorem msize_cons (a : Noun) (m : Multiset Noun) :
    msize (a ::ₘ m) = a.size + msize m := by
  simp [msize]

theorem msize_singleton (a : Noun) : msize ({a} : Multiset Noun) = a.size := by
  simp [msize]

theorem msize_erase {n : Noun} {m : Multiset Noun} (h : n ∈ m) :
    msize m = n.size + msize (m.erase n) := by
  conv_lhs => rw [← Multiset.cons_erase h]
  rw [msize_cons]

/-- Each successful step of the walk removes exactly one node from the total (`Lem:pbt_size`
    bookkeeping): a leaf pops `1` node; a cell pops `1 + |l| + |r|` and pushes `|l| + |r|`. -/
theorem step_msize {m m' : Multiset Noun} {n : Noun} {ch : Option (Noun × Noun)}
    (h : stepMset m n ch = some m') : msize m = msize m' + 1 := by
  cases n with
  | atom k =>
      cases ch with
      | none =>
          simp only [stepMset] at h
          split at h
          · rename_i hmem
            simp only [Option.some.injEq] at h
            subst h
            rw [msize_erase hmem]; simp only [Noun.size]; omega
          · simp at h
      | some c => simp only [stepMset] at h; simp at h
  | cell a b =>
      cases ch with
      | none => simp only [stepMset] at h; simp at h
      | some c =>
          obtain ⟨a', b'⟩ := c
          simp only [stepMset] at h
          split at h
          · rename_i hcond
            obtain ⟨hmem, -, -⟩ := hcond
            simp only [Option.some.injEq] at h
            subst h
            rw [msize_erase hmem]
            simp only [msize_cons, Noun.size]
            omega
          · simp at h

/-- An accepting run consumes a transcript of length exactly `msize m` (the total node count
    of the initial multiset).  This is the necessity half of `Thm:Noun_Validation`. -/
theorem run_length : ∀ {m : Multiset Noun} {T : Transcript},
    runMset m T = some 0 → T.length = msize m := by
  intro m T
  induction T generalizing m with
  | nil =>
      intro h
      simp only [runMset, Option.some.injEq] at h
      subst h; simp
  | cons t ts ih =>
      intro h
      obtain ⟨n, ch⟩ := t
      simp only [runMset] at h
      cases hstep : stepMset m n ch with
      | none => rw [hstep] at h; simp at h
      | some m' =>
          rw [hstep] at h
          have hlen := ih h
          have hms := step_msize hstep
          simp only [List.length_cons]
          omega

/-! ### The canonical accepting transcript (a preorder DFS walk) -/

/-- The canonical validity transcript of a noun: a preorder DFS walk.  A cell is decomposed
    (checking `cons`) before its subtrees are validated; an atom is a single no-children step. -/
def transcript : Noun → Transcript
  | Noun.atom k => [(Noun.atom k, none)]
  | Noun.cell l r => (Noun.cell l r, some (l, r)) :: (transcript l ++ transcript r)

@[simp] theorem transcript_length (n : Noun) : (transcript n).length = n.size := by
  induction n with
  | atom k => rfl
  | cell l r ihl ihr =>
      simp only [transcript, List.length_cons, List.length_append, ihl, ihr, Noun.size]
      omega

/-- Processing `transcript n` off the front of a multiset containing `n` validates `n` and
    removes exactly `n`, leaving the rest of the walk untouched.  (Order-independence of the
    walk, main.tex:1266: we use preorder.) -/
theorem run_transcript : ∀ (n : Noun) (m : Multiset Noun) (rest : Transcript),
    runMset (n ::ₘ m) (transcript n ++ rest) = runMset m rest := by
  intro n
  induction n with
  | atom k =>
      intro m rest
      rw [show transcript (Noun.atom k) ++ rest = (Noun.atom k, none) :: rest from rfl]
      have hstep : stepMset (Noun.atom k ::ₘ m) (Noun.atom k) none = some m := by
        simp [stepMset, Multiset.erase_cons_head]
      rw [runMset_cons hstep]
  | cell l r ihl ihr =>
      intro m rest
      rw [show transcript (Noun.cell l r) ++ rest
          = (Noun.cell l r, some (l, r)) :: (transcript l ++ transcript r ++ rest) from rfl]
      have hstep : stepMset (Noun.cell l r ::ₘ m) (Noun.cell l r) (some (l, r))
          = some (l ::ₘ r ::ₘ m) := by
        simp [stepMset, Multiset.erase_cons_head]
      rw [runMset_cons hstep, List.append_assoc,
        ihl (r ::ₘ m) (transcript r ++ rest), ihr m rest]

/-- The canonical transcript accepts. -/
theorem run_transcript_accept (n : Noun) : runMset {n} (transcript n) = some 0 := by
  have h := run_transcript n 0 []
  rw [List.append_nil] at h
  rw [show ({n} : Multiset Noun) = n ::ₘ 0 from rfl, h]
  rfl

/-! ### `Thm:Noun_Validation` (`main.tex:1268–1269`) -/

-- main.tex:1268–1269
/-- **`Thm:Noun_Validation`** (`main.tex:1268–1269`).
    n ∈ N^λ(F) ⇔ ∃ T. CheckValidNoun(n;T)=Accept ∧ |T|=2λ−1 -/
theorem Noun_Validation (n : Noun) (lam : ℕ) :
    n.leaves = lam ↔
      ∃ T : Transcript, checkValidNoun n T = Result.accept ∧ T.length = 2 * lam - 1 := by
  constructor
  · intro hlen
    refine ⟨transcript n, ?_, ?_⟩
    · rw [checkValidNoun_accept_iff]; exact run_transcript_accept n
    · rw [transcript_length]
      have := n.size_add_one
      omega
  · rintro ⟨T, hacc, hlenT⟩
    rw [checkValidNoun_accept_iff] at hacc
    have hlenrun := run_length hacc
    rw [msize_singleton] at hlenrun
    have hsz := n.size_add_one
    have hpos := n.one_le_leaves
    omega

end Nock
