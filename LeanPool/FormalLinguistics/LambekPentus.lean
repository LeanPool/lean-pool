/-
Copyright (c) 2026 bocchitherock888-ux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: bocchitherock888-ux
-/

module

public import LeanPool.FormalLinguistics.LambekCut
public import LeanPool.FormalLinguistics.LambekInterpolation
public import LeanPool.FormalLinguistics.LambekFreeGroup
public import LeanPool.FormalLinguistics.LambekThin

/-!
  Pentus's theorem (1993): every Lambek grammar generates a context-free language, and
  the resulting characterisation of Lambek languages (Chomsky's conjecture).

  The proof follows Pentus's argument as presented by Kanazawa (2018, Section 4):
  thin sequents, interpolation, the free-group interpretation and Pentus's lemma about
  free groups give a "binary reduction" of every derivable sequent whose types have
  bounded size; the context-free grammar has the types of bounded size as nonterminals
  and the derivable sequents with at most two antecedent types as rules.
-/

@[expose] public section

namespace FormalLinguistics

namespace LPentus

/-! ### Primitive types of a type -/

/-- The list of primitive types occurring in a type (with repetitions). -/
def prims {P : Type} : LType P → List P
  | LType.prim p => [p]
  | LType.over A B => prims A ++ prims B
  | LType.under B A => prims B ++ prims A
  | LType.mul A B => prims A ++ prims B

theorem size_map {P Q : Type} (f : P → Q) (A : LType P) : (A.map f).size = A.size := by
  induction A with
  | prim p => rfl
  | over A B ihA ihB => simp [LType.map, LType.size, ihA, ihB]
  | under B A ihB ihA => simp [LType.map, LType.size, ihA, ihB]
  | mul A B ihA ihB => simp [LType.map, LType.size, ihA, ihB]

theorem prims_map {P Q : Type} (f : P → Q) (A : LType P) :
    prims (A.map f) = (prims A).map f := by
  induction A with
  | prim p => rfl
  | over A B ihA ihB => simp [LType.map, prims, ihA, ihB]
  | under B A ihB ihA => simp [LType.map, prims, ihA, ihB]
  | mul A B ihA ihB => simp [LType.map, prims, ihA, ihB]

theorem size_pos {P : Type} (A : LType P) : 1 ≤ A.size := by
  induction A with
  | prim p => simp [LType.size]
  | over A B ihA ihB => simp only [LType.size]; omega
  | under B A ihB ihA => simp only [LType.size]; omega
  | mul A B ihA ihB => simp only [LType.size]; omega

theorem mem_prims_of_occ {P : Type} [DecidableEq P] (p : P) (A : LType P) :
    A.occ p ≠ 0 → p ∈ prims A := by
  induction A with
  | prim q =>
    intro h
    simp only [LType.occ] at h
    by_cases hq : q = p
    · subst hq; simp [prims]
    · simp [hq] at h
  | over A B ihA ihB =>
    intro h; simp only [LType.occ] at h; simp only [prims, List.mem_append]
    by_cases hA : A.occ p = 0
    · exact Or.inr (ihB (by omega))
    · exact Or.inl (ihA hA)
  | under B A ihB ihA =>
    intro h; simp only [LType.occ] at h; simp only [prims, List.mem_append]
    by_cases hB : B.occ p = 0
    · exact Or.inr (ihA (by omega))
    · exact Or.inl (ihB hB)
  | mul A B ihA ihB =>
    intro h; simp only [LType.occ] at h; simp only [prims, List.mem_append]
    by_cases hA : A.occ p = 0
    · exact Or.inr (ihB (by omega))
    · exact Or.inl (ihA hA)

theorem exists_of_occList {P : Type} [DecidableEq P] (p : P) (Δ : List (LType P)) :
    occList p Δ ≠ 0 → ∃ X ∈ Δ, p ∈ prims X := by
  induction Δ with
  | nil => intro h; exact absurd rfl h
  | cons A Δ ih =>
    intro h
    rw [LInterp.occList_cons] at h
    by_cases hA : A.occ p = 0
    · obtain ⟨X, hX, hp⟩ := ih (by omega)
      exact ⟨X, List.mem_cons_of_mem _ hX, hp⟩
    · exact ⟨A, List.mem_cons_self, mem_prims_of_occ p A hA⟩

theorem occ_of_mem_prims {P : Type} [DecidableEq P] (p : P) (A : LType P) :
    p ∈ prims A → A.occ p ≠ 0 := by
  induction A with
  | prim q =>
    intro h
    simp [prims] at h
    subst h; simp [LType.occ]
  | over A B ihA ihB =>
    intro h; simp only [LType.occ]; simp only [prims, List.mem_append] at h
    rcases h with h | h
    · have := ihA h; omega
    · have := ihB h; omega
  | under B A ihB ihA =>
    intro h; simp only [LType.occ]; simp only [prims, List.mem_append] at h
    rcases h with h | h
    · have := ihB h; omega
    · have := ihA h; omega
  | mul A B ihA ihB =>
    intro h; simp only [LType.occ]; simp only [prims, List.mem_append] at h
    rcases h with h | h
    · have := ihA h; omega
    · have := ihB h; omega

/-- Primitives of an interpolant, transported along a renaming. -/
theorem transfer {P Q : Type} [DecidableEq Q] (f : Q → P) {E : LType Q} {Δ : List (LType Q)}
    (h : ∀ q, E.occ q ≤ occList q Δ) :
    ∀ p ∈ prims (E.map f), ∃ X ∈ Δ.map (LType.map f), p ∈ prims X := by
  intro p hp
  rw [prims_map, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  have h1 := occ_of_mem_prims q E hq
  have h2 : occList q Δ ≠ 0 := by have := h q; omega
  obtain ⟨X, hX, hqX⟩ := exists_of_occList q Δ h2
  refine ⟨X.map f, List.mem_map_of_mem hX, ?_⟩
  rw [prims_map]
  exact List.mem_map_of_mem hqX

theorem split_last {α β : Type} (f : α → β) (z : β) :
    ∀ (xs : List α) (l r : List β) (u v : β), xs.map f ++ [z] = l ++ u :: v :: r →
      (∃ xs1 a b xs2, xs = xs1 ++ [a, b] ++ xs2 ∧ u = f a ∧ v = f b) ∨
      (∃ xs1 a, xs = xs1 ++ [a] ∧ u = f a ∧ v = z) := by
  intro xs
  induction xs with
  | nil =>
    intro l r u v h
    cases l with
    | nil => simp at h
    | cons x l => simp at h
  | cons x xs ih =>
    intro l r u v h
    cases l with
    | nil =>
      simp at h
      obtain ⟨rfl, h⟩ := h
      cases xs with
      | nil =>
        simp at h
        right; exact ⟨[], x, by simp, rfl, h.1.symm⟩
      | cons y ys =>
        simp at h
        left; exact ⟨[], x, y, ys, by simp, rfl, h.1.symm⟩
    | cons l0 l' =>
      simp at h
      obtain ⟨_, h⟩ := h
      rcases ih l' r u v h with ⟨xs1, a, b, xs2, rfl, hu, hv⟩ | ⟨xs1, a, rfl, hu, hv⟩
      · left; exact ⟨x :: xs1, a, b, xs2, by simp, hu, hv⟩
      · right; exact ⟨x :: xs1, a, by simp, hu, hv⟩

/-- **Binary reduction step** (Kanazawa 2018, Lemma 5). -/
theorem step {P : Type} [DecidableEq P] (m : Nat) {Γ : List (LType P)} {C : LType P}
    (h : LDer0 Γ C) (hlen : 3 ≤ Γ.length) (hΓ : ∀ X ∈ Γ, X.size ≤ m) (hC : C.size ≤ m) :
    (∃ Γ₁ Γ₂ A B E, Γ = Γ₁ ++ [A, B] ++ Γ₂ ∧ E.size ≤ m ∧ LDer0 [A, B] E ∧
        LDer0 (Γ₁ ++ [E] ++ Γ₂) C ∧ ∀ p ∈ prims E, ∃ X ∈ [A, B], p ∈ prims X) ∨
    (∃ Γ₁ A E, Γ = Γ₁ ++ [A] ∧ Γ₁ ≠ [] ∧ E.size ≤ m ∧ LDer0 Γ₁ E ∧ LDer0 [E, A] C ∧
        ∀ p ∈ prims E, ∃ X ∈ Γ₁, p ∈ prims X) := by
  obtain ⟨Γ', C', h', hΓ', hC', hthin⟩ := h.exists_thin
  subst hΓ' hC'
  have hred0 : FGWord.reduce (interpList Γ' ++ FGWord.inv C'.interp) = [] :=
    FGWord.reduce_append_inv_eq_nil h'.interp_sound
  have hflat : (Γ'.map LType.interp ++ [FGWord.inv C'.interp]).flatten
      = interpList Γ' ++ FGWord.inv C'.interp := by simp [interpList]
  have hlen' : 2 ≤ (Γ'.map LType.interp ++ [FGWord.inv C'.interp]).length := by
    simp at hlen ⊢; omega
  obtain ⟨l, r, u, v, hus, hnorm⟩ :=
    FGWord.pentus_lemma _ hlen' (by rw [hflat]; exact hred0)
  have hfac : ∀ x ∈ Γ'.map LType.interp ++ [FGWord.inv C'.interp], FGWord.norm x ≤ m := by
    intro x hx
    rw [List.mem_append, List.mem_map, List.mem_singleton] at hx
    rcases hx with ⟨A', hA', rfl⟩ | rfl
    · have h1 := LType.norm_interp_le A'
      have h2 := hΓ (A'.map Prod.fst) (List.mem_map_of_mem hA')
      rw [size_map] at h2
      omega
    · rw [FGWord.norm_inv]
      have h1 := LType.norm_interp_le C'
      rw [size_map] at hC
      omega
  have hu := hfac u (by rw [hus]; simp)
  have hv := hfac v (by rw [hus]; simp)
  have huv : FGWord.norm (u ++ v) ≤ m := by
    have := Nat.max_le.2 ⟨hu, hv⟩
    omega
  rcases split_last LType.interp _ Γ' l r u v hus with
      ⟨Γ₁', A', B', Γ₂', rfl, rfl, rfl⟩ | ⟨Γ₁', A', rfl, rfl, rfl⟩
  · obtain ⟨E', hE1, hE2, hocc⟩ :=
      LDer0.interpolation (Γ := Γ₁') (Δ := [A', B']) (Θ := Γ₂') h' (by simp)
    have hocc1 : ∀ q, E'.occ q ≤ 1 := by
      intro q
      have h1 := hthin q
      have h2 := hocc q
      rw [LInterp.occList_append, LInterp.occList_append] at h1
      omega
    have hsz : E'.size ≤ m := by
      rw [← LType.norm_interp_eq_size E' hocc1, ← FGWord.norm_eq_of_reduce_eq hE1.interp_sound]
      have e : interpList [A', B'] = A'.interp ++ B'.interp := by simp [interpList]
      rw [e]; exact huv
    left
    refine ⟨Γ₁'.map (LType.map Prod.fst), Γ₂'.map (LType.map Prod.fst), A'.map Prod.fst,
      B'.map Prod.fst, E'.map Prod.fst, by simp, by rw [size_map]; exact hsz,
      by simpa using hE1.map Prod.fst, by simpa using hE2.map Prod.fst, ?_⟩
    have := transfer Prod.fst (fun q => (hocc q).1)
    simpa using this
  · have hne : Γ₁' ≠ [] := by
      intro h0; subst h0; simp at hlen
    obtain ⟨E', hE1, hE2, hocc⟩ :=
      LDer0.interpolation (Γ := []) (Δ := Γ₁') (Θ := [A']) (by simpa using h') hne
    have hocc1 : ∀ q, E'.occ q ≤ 1 := by
      intro q
      have h1 := hthin q
      have h2 := hocc q
      rw [LInterp.occList_append] at h1
      rw [LInterp.occList_nil] at h2
      omega
    have hsz : E'.size ≤ m := by
      rw [← LType.norm_interp_eq_size E' hocc1, ← FGWord.norm_eq_of_reduce_eq hE1.interp_sound]
      have e : interpList (Γ₁' ++ [A']) = interpList Γ₁' ++ A'.interp := by simp [interpList]
      rw [e, List.append_assoc] at hred0
      rw [FGWord.norm_eq_of_reduce_append_eq_nil hred0]
      exact huv
    right
    refine ⟨Γ₁'.map (LType.map Prod.fst), A'.map Prod.fst, E'.map Prod.fst, by simp,
      by simpa using hne, by rw [size_map]; exact hsz,
      by simpa using hE1.map Prod.fst, by simpa using hE2.map Prod.fst, ?_⟩
    exact transfer Prod.fst (fun q => (hocc q).1)

/-! ### Finitely many candidate types -/

/-- All types built from the primitives `ps` with at most `n` nested connectives. -/
def allTypes {P : Type} (ps : List P) : Nat → List (LType P)
  | 0 => ps.map LType.prim
  | n + 1 => allTypes ps n ++ (allTypes ps n).flatMap (fun X => (allTypes ps n).flatMap
      (fun Y => [LType.over X Y, LType.under X Y, LType.mul X Y]))

theorem allTypes_succ {P : Type} {ps : List P} {n : Nat} {A : LType P}
    (h : A ∈ allTypes ps n) : A ∈ allTypes ps (n + 1) := by
  simp only [allTypes, List.mem_append]; exact Or.inl h

theorem allTypes_prim {P : Type} {ps : List P} {p : P} (hp : p ∈ ps) :
    ∀ n, LType.prim p ∈ allTypes ps n := by
  intro n
  induction n with
  | zero => simp only [allTypes]; exact List.mem_map_of_mem hp
  | succ n ih => exact allTypes_succ ih

theorem allTypes_bin {P : Type} {ps : List P} {n : Nat} {X Y : LType P}
    (hX : X ∈ allTypes ps n) (hY : Y ∈ allTypes ps n) :
    LType.over X Y ∈ allTypes ps (n + 1) ∧ LType.under X Y ∈ allTypes ps (n + 1) ∧
      LType.mul X Y ∈ allTypes ps (n + 1) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [allTypes, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨X, hX, Y, hY, by simp⟩

theorem mem_allTypes {P : Type} (ps : List P) (A : LType P) :
    (∀ p ∈ prims A, p ∈ ps) → ∀ n, A.size ≤ n + 1 → A ∈ allTypes ps n := by
  induction A with
  | prim p =>
    intro h n _
    exact allTypes_prim (h p (by simp [prims])) n
  | over A B ihA ihB =>
    intro h n hn
    have h1 := size_pos A; have h2 := size_pos B
    simp only [LType.size] at hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    refine (allTypes_bin (ihA (fun p hp => h p (by simp [prims, hp])) k (by omega))
      (ihB (fun p hp => h p (by simp [prims, hp])) k (by omega))).1
  | under B A ihB ihA =>
    intro h n hn
    have h1 := size_pos A; have h2 := size_pos B
    simp only [LType.size] at hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    refine (allTypes_bin (ihB (fun p hp => h p (by simp [prims, hp])) k (by omega))
      (ihA (fun p hp => h p (by simp [prims, hp])) k (by omega))).2.1
  | mul A B ihA ihB =>
    intro h n hn
    have h1 := size_pos A; have h2 := size_pos B
    simp only [LType.size] at hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    refine (allTypes_bin (ihA (fun p hp => h p (by simp [prims, hp])) k (by omega))
      (ihB (fun p hp => h p (by simp [prims, hp])) k (by omega))).2.2

/-- The "good" types: bounded size, primitives among `ps`. -/
def Good {P : Type} (ps : List P) (m : Nat) (A : LType P) : Prop :=
  A.size ≤ m ∧ ∀ p ∈ prims A, p ∈ ps

theorem Good.mem {P : Type} {ps : List P} {m : Nat} {A : LType P} (h : Good ps m A) :
    A ∈ allTypes ps m :=
  mem_allTypes ps A h.2 m (by have := h.1; omega)

/-! ### The context-free grammar -/

/-- Admissible rules of the context-free grammar. -/
def RuleOK {P T : Type} (G : LambekGrammar P T) (r : LType P × List (Symbol (LType P) T)) :
    Prop :=
  (∃ a, r.2 = [Symbol.tm a] ∧ (a, r.1) ∈ G.lexicon) ∨
  (∃ A, r.2 = [Symbol.nt A] ∧ LDer0 [A] r.1) ∨
  (∃ A B, r.2 = [Symbol.nt A, Symbol.nt B] ∧ LDer0 [A, B] r.1)

open Classical in
/-- The context-free grammar whose nonterminals are types: lexical rules, and the derivable
    sequents with one or two antecedent types among the candidate types. -/
noncomputable def pentusCFG {P T : Type} (G : LambekGrammar P T) (ps : List P) (m : Nat) :
    CFG (LType P) T where
  start := LType.prim G.distinguished
  rules := (G.lexicon.map (fun (x : T × LType P) => (x.2, [Symbol.tm x.1])) ++
    (allTypes ps m).flatMap (fun A => (allTypes ps m).map (fun D => (D, [Symbol.nt A]))) ++
    (allTypes ps m).flatMap (fun A => (allTypes ps m).flatMap (fun B =>
      (allTypes ps m).map (fun D => (D, [Symbol.nt A, Symbol.nt B]))))).filter
    (fun r => decide (RuleOK G r))

theorem rule_ok {P T : Type} {G : LambekGrammar P T} {ps : List P} {m : Nat}
    {r : LType P × List (Symbol (LType P) T)} (h : r ∈ (pentusCFG G ps m).rules) :
    RuleOK G r := by
  simp only [pentusCFG, List.mem_filter, decide_eq_true_iff] at h
  exact h.2

theorem lex_rule {P T : Type} {G : LambekGrammar P T} {ps : List P} {m : Nat} {a : T}
    {A : LType P} (h : (a, A) ∈ G.lexicon) : (A, [Symbol.tm a]) ∈ (pentusCFG G ps m).rules := by
  simp only [pentusCFG, List.mem_filter, decide_eq_true_iff]
  refine ⟨?_, Or.inl ⟨a, rfl, h⟩⟩
  simp only [List.mem_append]
  exact Or.inl (Or.inl (List.mem_map.2 ⟨(a, A), h, rfl⟩))

theorem un_rule {P T : Type} {G : LambekGrammar P T} {ps : List P} {m : Nat}
    {A D : LType P} (hA : A ∈ allTypes ps m) (hD : D ∈ allTypes ps m) (h : LDer0 [A] D) :
    (D, [Symbol.nt A]) ∈ (pentusCFG G ps m).rules := by
  simp only [pentusCFG, List.mem_filter, decide_eq_true_iff]
  refine ⟨?_, Or.inr (Or.inl ⟨A, rfl, h⟩)⟩
  simp only [List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inl (Or.inr ⟨A, hA, D, hD, rfl⟩)

theorem bin_rule {P T : Type} {G : LambekGrammar P T} {ps : List P} {m : Nat}
    {A B D : LType P} (hA : A ∈ allTypes ps m) (hB : B ∈ allTypes ps m)
    (hD : D ∈ allTypes ps m) (h : LDer0 [A, B] D) :
    (D, [Symbol.nt A, Symbol.nt B]) ∈ (pentusCFG G ps m).rules := by
  simp only [pentusCFG, List.mem_filter, decide_eq_true_iff]
  refine ⟨?_, Or.inr (Or.inr ⟨A, B, rfl, h⟩)⟩
  simp only [List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inr ⟨A, hA, B, hB, D, hD, rfl⟩

/-! ### Soundness of the grammar -/

theorem lexAssign_append {P T : Type} {G : LambekGrammar P T} {w1 w2 : List T}
    {Γ1 Γ2 : List (LType P)} (h1 : G.LexAssign w1 Γ1) (h2 : G.LexAssign w2 Γ2) :
    G.LexAssign (w1 ++ w2) (Γ1 ++ Γ2) := by
  induction h1 with
  | nil => simpa using h2
  | cons ha _ ih => exact LambekGrammar.LexAssign.cons ha ih

/-- List-level companion of `CFG.YieldList` for the soundness proof. -/
inductive SY {P T : Type} (G : LambekGrammar P T) : List (Symbol (LType P) T) → List T → Prop
  | nil : SY G [] []
  | cons_tm {a : T} {rhs : List (Symbol (LType P) T)} {w : List T} :
      SY G rhs w → SY G (Symbol.tm a :: rhs) (a :: w)
  | cons_nt {D : LType P} {rhs : List (Symbol (LType P) T)} {w1 w2 : List T} :
      (∃ Γ, G.LexAssign w1 Γ ∧ LDer0 Γ D) → SY G rhs w2 → SY G (Symbol.nt D :: rhs) (w1 ++ w2)

mutual
  theorem sound {P T : Type} {G : LambekGrammar P T} {ps : List P} {m : Nat}
      {D : LType P} {w : List T} :
      CFG.Yield (pentusCFG G ps m) D w → ∃ Γ, G.LexAssign w Γ ∧ LDer0 Γ D
    | CFG.Yield.rule hr hyl_raw => by
      have hyl := sound_list hyl_raw
      rcases rule_ok hr with ⟨a, he, hlex⟩ | ⟨A, he, hd⟩ | ⟨A, B, he, hd⟩
      · simp only at he hlex
        subst he
        cases hyl with
        | cons_tm hnil =>
          cases hnil
          exact ⟨[D], LambekGrammar.LexAssign.cons hlex LambekGrammar.LexAssign.nil,
            LDer0.identity D⟩
      · simp only at he hd
        subst he
        cases hyl with
        | cons_nt h1 hnil =>
          cases hnil
          obtain ⟨Γ, hl, hg⟩ := h1
          refine ⟨Γ, by simpa using hl, ?_⟩
          have := LDer0.cut (Γ := []) (Δ := []) hg (by simpa using hd)
          simpa using this
      · simp only at he hd
        subst he
        cases hyl with
        | cons_nt h1 hrest =>
          cases hrest with
          | cons_nt h2 hnil =>
            cases hnil
            obtain ⟨Γ1, hl1, hg1⟩ := h1
            obtain ⟨Γ2, hl2, hg2⟩ := h2
            refine ⟨Γ1 ++ Γ2, by simpa using lexAssign_append hl1 hl2, ?_⟩
            have k1 := LDer0.cut (Γ := []) (Δ := [B]) hg1 (by simpa using hd)
            have k2 := LDer0.cut (Γ := Γ1) (Δ := []) hg2 (by simpa using k1)
            simpa using k2

  theorem sound_list {P T : Type} {G : LambekGrammar P T} {ps : List P} {m : Nat}
      {rhs : List (Symbol (LType P) T)} {w : List T} :
      CFG.YieldList (pentusCFG G ps m) rhs w → SY G rhs w
    | CFG.YieldList.nil => SY.nil
    | CFG.YieldList.cons_tm h => SY.cons_tm (sound_list h)
    | CFG.YieldList.cons_nt hy h => SY.cons_nt (sound hy) (sound_list h)
end

/-! ### Completeness of the grammar -/

theorem complete {P T : Type} [DecidableEq P] (G : LambekGrammar P T) (ps : List P) (m : Nat) :
    ∀ n (Γ : List (LType P)) (D : LType P), Γ.length ≤ n → (∀ X ∈ Γ, Good ps m X) →
      Good ps m D → LDer0 Γ D →
      CFG.Derives (pentusCFG G ps m) [Symbol.nt D] (Γ.map Symbol.nt) := by
  intro n
  induction n with
  | zero =>
    intro Γ D hlen _ _ hder
    have : Γ = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact absurd this hder.ne_nil
  | succ n ih =>
    intro Γ D hlen hg hD hder
    by_cases h3 : 3 ≤ Γ.length
    · rcases step m hder h3 (fun X hX => (hg X hX).1) hD.1 with
          ⟨Γ₁, Γ₂, A, B, E, rfl, hE, hAB, hrest, hpr⟩ | ⟨Γ₁, A, E, rfl, hne, hE, hΓ₁, hEA, hpr⟩
      · have hgA := hg A (by simp)
        have hgB := hg B (by simp)
        have hgE : Good ps m E := ⟨hE, fun p hp => by
          obtain ⟨X, hX, hpX⟩ := hpr p hp
          simp at hX
          rcases hX with rfl | rfl
          · exact hgA.2 p hpX
          · exact hgB.2 p hpX⟩
        have h1 := ih (Γ₁ ++ [E] ++ Γ₂) D (by simp at hlen ⊢; omega)
          (fun X hX => by
            simp only [List.mem_append, List.mem_singleton] at hX
            rcases hX with (hX | rfl) | hX
            · exact hg X (by simp [hX])
            · exact hgE
            · exact hg X (by simp [hX])) hD hrest
        have h2 : CFG.Step (pentusCFG G ps m)
            (Γ₁.map Symbol.nt ++ [Symbol.nt E] ++ Γ₂.map Symbol.nt)
            (Γ₁.map Symbol.nt ++ [Symbol.nt A, Symbol.nt B] ++ Γ₂.map Symbol.nt) :=
          CFG.Step.mk _ _ _ _ (bin_rule hgA.mem hgB.mem hgE.mem hAB)
        have h3 := CFG.Derives.tail (by simpa using h1) h2
        simpa using h3
      · have hgA := hg A (by simp)
        have hgE : Good ps m E := ⟨hE, fun p hp => by
          obtain ⟨X, hX, hpX⟩ := hpr p hp
          exact (hg X (by simp [hX])).2 p hpX⟩
        have h1 := ih Γ₁ E (by simp at hlen ⊢; omega)
          (fun X hX => hg X (by simp [hX])) hgE hΓ₁
        have h2 : CFG.Step (pentusCFG G ps m) [Symbol.nt D] [Symbol.nt E, Symbol.nt A] := by
          simpa using CFG.Step.mk [] [] _ _ (bin_rule hgE.mem hgA.mem hD.mem hEA)
        have h3 := CFG.Derives.append_right [Symbol.nt A] h1
        have h4 := CFG.Derives.trans (CFG.Derives.single h2) (by simpa using h3)
        simpa using h4
    · rcases Γ with _ | ⟨A, _ | ⟨B, _ | ⟨X, rest⟩⟩⟩
      · exact absurd rfl hder.ne_nil
      · have hgA := hg A (by simp)
        have h2 : CFG.Step (pentusCFG G ps m) [Symbol.nt D] [Symbol.nt A] := by
          simpa using CFG.Step.mk [] [] _ _ (un_rule hgA.mem hD.mem hder)
        simpa using CFG.Derives.single h2
      · have hgA := hg A (by simp)
        have hgB := hg B (by simp)
        have h2 : CFG.Step (pentusCFG G ps m) [Symbol.nt D] [Symbol.nt A, Symbol.nt B] := by
          simpa using CFG.Step.mk [] [] _ _ (bin_rule hgA.mem hgB.mem hD.mem hder)
        simpa using CFG.Derives.single h2
      · simp at h3

theorem lex_derives {P T : Type} {G : LambekGrammar P T} {ps : List P} {m : Nat}
    {w : List T} {Γ : List (LType P)} (h : G.LexAssign w Γ) :
    CFG.Derives (pentusCFG G ps m) (Γ.map Symbol.nt) (w.map Symbol.tm) := by
  induction h with
  | nil => exact CFG.Derives.refl _
  | @cons a A w Γ ha _ ih =>
    have h1 : CFG.Step (pentusCFG G ps m) [Symbol.nt A] [Symbol.tm a] := by
      simpa using CFG.Step.mk [] [] _ _ (lex_rule (ps := ps) (m := m) ha)
    have := CFG.Derives.append (CFG.Derives.single h1) ih
    simpa using this

theorem lexAssign_mem {P T : Type} {G : LambekGrammar P T} {w : List T}
    {Γ : List (LType P)} (h : G.LexAssign w Γ) : ∀ X ∈ Γ, ∃ a, (a, X) ∈ G.lexicon := by
  induction h with
  | nil => intro X hX; simp at hX
  | @cons a A w Γ ha _ ih =>
    intro X hX
    rcases List.mem_cons.1 hX with rfl | hX
    · exact ⟨a, ha⟩
    · exact ih X hX

theorem le_sum_of_mem {α : Type} (f : α → Nat) {l : List α} {x : α} (h : x ∈ l) :
    f x ≤ (l.map f).sum := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := ih h; simp; omega

end LPentus

/-- **Pentus's theorem.** Every Lambek grammar has a context-free grammar generating the
    same language. -/
theorem lambek_to_cfg {P T : Type} (G : LambekGrammar P T) :
    ∃ G' : CFG (LType P) T, ∀ w, G'.Lang w ↔ G.Lang w := by
  classical
  let ps : List P := G.distinguished :: G.lexicon.flatMap (fun x => LPentus.prims x.2)
  let m : Nat := (G.lexicon.map (fun x => x.2.size)).sum + 1
  have hlexgood : ∀ a A, (a, A) ∈ G.lexicon → LPentus.Good ps m A := by
    intro a A h
    refine ⟨?_, fun p hp => ?_⟩
    · have := LPentus.le_sum_of_mem (fun x : T × LType P => x.2.size) h
      simp only at this
      omega
    · exact List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨(a, A), h, hp⟩)
  have hsgood : LPentus.Good ps m (LType.prim G.distinguished) :=
    ⟨by simp [LType.size, m], fun p hp => by simp [LPentus.prims] at hp; simp [ps, hp]⟩
  refine ⟨LPentus.pentusCFG G ps m, fun w => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨Γ, hl, hd⟩ := LPentus.sound (CFG.lang_iff_yield.1 h)
    exact ⟨Γ, hl, LDer_iff_LDer0.2 hd⟩
  · obtain ⟨Γ, hl, hd⟩ := h
    have hd0 := LDer_iff_LDer0.1 hd
    have hg : ∀ X ∈ Γ, LPentus.Good ps m X := by
      intro X hX
      obtain ⟨a, ha⟩ := LPentus.lexAssign_mem hl X hX
      exact hlexgood a X ha
    have h1 := LPentus.complete G ps m Γ.length Γ _ (Nat.le_refl _) hg hsgood hd0
    exact CFG.Derives.trans h1 (LPentus.lex_derives hl)

/-- A language is a Lambek language if it is generated by some finite Lambek grammar. -/
def IsLambekLang {T : Type} (L : List T → Prop) : Prop :=
  ∃ (P : Type) (G : LambekGrammar P T), ∀ w, G.Lang w ↔ L w

/-- **Chomsky–Pentus theorem.** A language is generated by a Lambek grammar if and only if
    it is an ε-free context-free language. -/
theorem chomsky_pentus {T : Type} [DecidableEq T] (L : List T → Prop) :
    IsLambekLang L ↔
      ((∃ (N : Type) (_ : DecidableEq N) (G : CFG N T), ∀ w, G.Lang w ↔ L w) ∧ ¬ L []) := by
  constructor
  · rintro ⟨P, G, hG⟩
    obtain ⟨G', hG'⟩ := lambek_to_cfg G
    refine ⟨⟨LType P, fun a b => Classical.propDecidable (a = b), G', fun w => (hG' w).trans (hG w)⟩, ?_⟩
    intro h0
    obtain ⟨Γ, hl, hd⟩ := (hG []).2 h0
    cases hl
    exact (LDer_iff_LDer0.1 hd).ne_nil rfl
  · rintro ⟨⟨N, inst, G, hG⟩, hne⟩
    refine ⟨_, (cfgToABG G).toLambek, fun w => ?_⟩
    rw [cfg_to_lambek_equiv, hG]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      rintro rfl
      exact hne h

end FormalLinguistics
