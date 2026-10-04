/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NFStandard.Basic

/-! NF weak partition development: NFStandard.CylinderCompiler. -/


public section

namespace NFChoice.Foundation

namespace Formula

/-! `StratifiedByBelow cap ty p` is a stratification certificate with one global
normalization ceiling. In particular, the witness type chosen at every
quantifier is at most `cap`. This is the form needed by Hailperin's uniform
singleton normalization: every variable is raised exactly `cap - type` times,
and that convention is unchanged beneath binders.
-/


/-- Stratification by `ty`, with every bound-variable type globally capped. -/
@[expose]
def StratifiedByBelow (cap : Int) {n : Nat} (ty : Fin n → Int) : Formula n → Prop
  | .falsum => True
  | .equal x y => ty x = ty y
  | .mem x y => ty y = ty x + 1
  | .imp p q => StratifiedByBelow cap ty p ∧ StratifiedByBelow cap ty q
  | .all p => ∃ k : Int, k ≤ cap ∧ StratifiedByBelow cap (Fin.cases k ty) p

@[simp]
theorem stratifiedByBelow_falsum {cap : Int} {n : Nat} (ty : Fin n → Int) :
    StratifiedByBelow cap ty (.falsum : Formula n) :=
  trivial

@[simp]
theorem stratifiedByBelow_equal {cap : Int} {n : Nat} (ty : Fin n → Int) (x y : Fin n) :
    StratifiedByBelow cap ty (.equal x y) ↔ ty x = ty y :=
  Iff.rfl

@[simp]
theorem stratifiedByBelow_mem {cap : Int} {n : Nat} (ty : Fin n → Int) (x y : Fin n) :
    StratifiedByBelow cap ty (.mem x y) ↔ ty y = ty x + 1 :=
  Iff.rfl

@[simp]
theorem stratifiedByBelow_imp {cap : Int} {n : Nat} (ty : Fin n → Int) (p q : Formula n) :
    StratifiedByBelow cap ty (.imp p q) ↔
      StratifiedByBelow cap ty p ∧ StratifiedByBelow cap ty q :=
  Iff.rfl

@[simp]
theorem stratifiedByBelow_all {cap : Int} {n : Nat} (ty : Fin n → Int)
    (p : Formula (n + 1)) :
    StratifiedByBelow cap ty (.all p) ↔
      ∃ k : Int, k ≤ cap ∧ StratifiedByBelow cap (Fin.cases k ty) p :=
  Iff.rfl

/-- Increasing the normalization ceiling preserves a capped certificate. -/
theorem StratifiedByBelow.mono :
    ∀ {cap cap' : Int} {n : Nat} {ty : Fin n → Int} {p : Formula n},
      cap ≤ cap' → StratifiedByBelow cap ty p → StratifiedByBelow cap' ty p
  | _, _, _, _, .falsum, _, _ => trivial
  | _, _, _, _, .equal _ _, _, hp => hp
  | _, _, _, _, .mem _ _, _, hp => hp
  | _, _, _, _, .imp p q, hcap, hp =>
    ⟨StratifiedByBelow.mono hcap hp.1, StratifiedByBelow.mono hcap hp.2⟩
  | _, _, _, _, .all p, hcap, hp =>
    by
    rcases hp with ⟨k, hk, hp⟩
    exact ⟨k, hk.trans hcap, StratifiedByBelow.mono hcap hp⟩

/-- Forgetting the global ceiling recovers the ordinary certificate. -/
theorem StratifiedByBelow.toStratifiedBy :
    ∀ {cap : Int} {n : Nat} {ty : Fin n → Int} {p : Formula n},
      StratifiedByBelow cap ty p → StratifiedBy ty p
  | _, _, _, .falsum, _ => trivial
  | _, _, _, .equal _ _, hp => hp
  | _, _, _, .mem _ _, hp => hp
  | _, _, _, .imp p q, hp =>
    ⟨StratifiedByBelow.toStratifiedBy hp.1, StratifiedByBelow.toStratifiedBy hp.2⟩
  | _, _, _, .all p, hp => by
    rcases hp with ⟨k, _, hp⟩
    exact ⟨k, StratifiedByBelow.toStratifiedBy hp⟩

/-- A simple upper bound for every entry of a finite type context. -/
@[expose]
def contextCap : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, ty => max (ty 0) (contextCap n (fun i => ty i.succ))

theorem le_contextCap : ∀ {n : Nat} (ty : Fin n → Int) (i : Fin n), ty i ≤ contextCap n ty
  | 0, _, i => Fin.elim0 i
  | n + 1, ty, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact le_max_left _ _
    · exact (le_contextCap (fun q : Fin n => ty q.succ) j).trans (le_max_right _ _)

/-- Every ordinary finite stratification admits one cap valid at all binders. -/
theorem exists_stratifiedByBelow :
    ∀ {n : Nat} (ty : Fin n → Int) (p : Formula n),
      StratifiedBy ty p → ∃ cap : Int, (∀ i, ty i ≤ cap) ∧ StratifiedByBelow cap ty p
  | n, ty, .falsum, _ => ⟨contextCap n ty, le_contextCap ty, trivial⟩
  | n, ty, .equal i j, hp => ⟨contextCap n ty, le_contextCap ty, hp⟩
  | n, ty, .mem i j, hp => ⟨contextCap n ty, le_contextCap ty, hp⟩
  | n, ty, .imp p q, hp =>
    by
    rcases exists_stratifiedByBelow ty p hp.1 with ⟨capP, htyP, hpP⟩
    rcases exists_stratifiedByBelow ty q hp.2 with ⟨capQ, htyQ, hpQ⟩
    refine ⟨max capP capQ, ?_, ?_⟩
    · intro i
      exact (htyP i).trans (le_max_left _ _)
    · exact ⟨hpP.mono (le_max_left _ _), hpQ.mono (le_max_right _ _)⟩
  | n, ty, .all p, hp => by
    rcases hp with ⟨k, hp⟩
    rcases exists_stratifiedByBelow (Fin.cases k ty) p hp with ⟨cap, hbound, hp⟩
    refine ⟨cap, ?_, ⟨k, hbound 0, hp⟩⟩
    intro i
    exact hbound i.succ

/-- A selected global cap and capped certificate for a stratified formula. -/
structure CappedStratification {n : Nat} (p : Formula n) where
  /-- The `cap` component of the corresponding first-order structure. -/
  cap : Int
  /-- The `ty` component of the corresponding first-order structure. -/
  ty : Fin n → Int
  bounded : ∀ i, ty i ≤ cap
  certificate : StratifiedByBelow cap ty p

/-- Package a usual stratification as a globally capped one. -/
@[expose]
noncomputable def cappedStratification {n : Nat} (p : Formula n) (hp : Stratified p) :
    CappedStratification p := by
  let ty := Classical.choose hp
  have hty := Classical.choose_spec hp
  let cap := Classical.choose (exists_stratifiedByBelow ty p hty)
  have hcap := Classical.choose_spec (exists_stratifiedByBelow ty p hty)
  exact ⟨cap, ty, hcap.1, hcap.2⟩

end Formula

namespace NFStandard

open scoped Fol
open NFChoice.SemanticCore
open NFChoice.SemanticCore.Lowering

/-! `CylinderAlgebra` is the small, typed relation-algebra interface used by the
uniform Hailperin compiler. The cap is fixed for the whole formula, including
all bound variables. A concrete implementation therefore raises coordinate
`i` by `Int.toNat (cap - ty i)` singleton steps once and never has to rebase a
tail valuation when a quantifier is crossed.
-/


/-- Operations sufficient to compile globally capped stratified formulas. -/
structure CylinderAlgebra (S : Fol.Structure LNF) where
  /-- The code operation of this NF model presentation. -/
  code : {n : Nat} → Int → (Fin n → Int) → DVec S n → S
  /-- The empty operation of this NF model presentation. -/
  empty : Int → (n : Nat) → S
  /-- The compl operation of this NF model presentation. -/
  compl : Int → (n : Nat) → S → S
  /-- The inter operation of this NF model presentation. -/
  inter : Int → (n : Nat) → S → S → S
  /-- The eq Set operation of this NF model presentation. -/
  eqSet : {n : Nat} → Int → (ty : Fin n → Int) → (i j : Fin n) → S
  /-- The mem Set operation of this NF model presentation. -/
  memSet : {n : Nat} → Int → (ty : Fin n → Int) → (i j : Fin n) → S
  /-- The exists Set operation of this NF model presentation. -/
  existsSet : {n : Nat} → Int → (ty : Fin n → Int) → Int → S → S
  /-- The slice operation of this NF model presentation. -/
  slice : {n : Nat} → Int → (ty : Fin (n + 1) → Int) → S → DVec S n → S
  mem_empty :
    ∀ {n : Nat} (cap : Int) (ty : Fin n → Int) (_hcap : ∀ i, ty i ≤ cap) (xs : DVec S n),
      ¬Mem S (code cap ty xs) (empty cap n)
  mem_compl :
    ∀ {n : Nat} (cap : Int) (ty : Fin n → Int) (_hcap : ∀ i, ty i ≤ cap) (A : S)
      (xs : DVec S n), Mem S (code cap ty xs) (compl cap n A) ↔ ¬Mem S (code cap ty xs) A
  mem_inter :
    ∀ {n : Nat} (cap : Int) (ty : Fin n → Int) (_hcap : ∀ i, ty i ≤ cap) (A B : S)
      (xs : DVec S n),
      Mem S (code cap ty xs) (inter cap n A B) ↔
        Mem S (code cap ty xs) A ∧ Mem S (code cap ty xs) B
  mem_eqSet :
    ∀ {n : Nat} (cap : Int) (ty : Fin n → Int) (_hcap : ∀ i, ty i ≤ cap) (i j : Fin n)
      (_h : ty i = ty j) (xs : DVec S n),
      Mem S (code cap ty xs) (eqSet cap ty i j) ↔ lookup xs i = lookup xs j
  mem_memSet :
    ∀ {n : Nat} (cap : Int) (ty : Fin n → Int) (_hcap : ∀ i, ty i ≤ cap) (i j : Fin n)
      (_h : ty j = ty i + 1) (xs : DVec S n),
      Mem S (code cap ty xs) (memSet cap ty i j) ↔ Mem S (lookup xs i) (lookup xs j)
  mem_existsSet :
    ∀ {n : Nat} (cap : Int) (ty : Fin n → Int) (_hcap : ∀ i, ty i ≤ cap) (k : Int)
      (_hk : k ≤ cap) (A : S) (xs : DVec S n),
      Mem S (code cap ty xs) (existsSet cap ty k A) ↔
        ∃ a : S, Mem S (code cap (Fin.cases k ty) (DVec.cons a xs)) A
  mem_slice :
    ∀ {n : Nat} (cap : Int) (ty : Fin (n + 1) → Int) (_hcap : ∀ i, ty i ≤ cap) (A : S)
      (xs : DVec S n) (z : S),
      Mem S z (slice cap ty A xs) ↔ Mem S (code cap ty (DVec.cons z xs)) A

namespace CylinderAlgebra

variable {S : Fol.Structure LNF} (C : CylinderAlgebra S)

/-- Compile a formula using one global normalization cap. -/
@[expose]
noncomputable def compile :
    ∀ {n : Nat} (cap : Int) (ty : Fin n → Int) (p : Formula n),
      Formula.StratifiedByBelow cap ty p → S
  | n, cap, _, .falsum, _ => C.empty cap n
  | _, cap, ty, .equal i j, _ => C.eqSet cap ty i j
  | _, cap, ty, .mem i j, _ => C.memSet cap ty i j
  | n, cap, ty, .imp p q, h =>
    C.compl cap n
      (C.inter cap n (compile cap ty p h.1) (C.compl cap n (compile cap ty q h.2)))
  | n, cap, ty, .all p, h =>
    let k := Classical.choose h
    let hp := (Classical.choose_spec h).2
    C.compl cap n
      (C.existsSet cap ty k (C.compl cap (n + 1) (compile cap (Fin.cases k ty) p hp)))

/-- The compiler represents exactly the semantic truth set of its formula. -/
theorem mem_compile :
    ∀ {n : Nat} (cap : Int) (ty : Fin n → Int) (p : Formula n) (_hcap : ∀ i, ty i ≤ cap)
      (hp : Formula.StratifiedByBelow cap ty p) (xs : DVec S n),
      Mem S (C.code cap ty xs) (C.compile cap ty p hp) ↔ FormulaHolds S xs p
  | _, cap, ty, .falsum, hcap, _, xs =>
    by
    simp only [compile, FormulaHolds]
    exact iff_false_intro (C.mem_empty cap ty hcap xs)
  | _, cap, ty, .equal i j, hcap, hp, xs => by
    simpa [compile, FormulaHolds] using C.mem_eqSet cap ty hcap i j hp xs
  | _, cap, ty, .mem i j, hcap, hp, xs => by
    simpa [compile, FormulaHolds] using C.mem_memSet cap ty hcap i j hp xs
  | n, cap, ty, .imp p q, hcap, hp, xs =>
    by
    rw [compile, C.mem_compl cap ty hcap, C.mem_inter cap ty hcap,
      C.mem_compl cap ty hcap, mem_compile cap ty p hcap hp.1 xs,
      mem_compile cap ty q hcap hp.2 xs]
    simp only [FormulaHolds]
    tauto
  | n, cap, ty, .all p, hcap, hp, xs =>
    by
    have hk : Classical.choose hp ≤ cap := (Classical.choose_spec hp).1
    have hbody := (Classical.choose_spec hp).2
    have hcap' : ∀ i, Fin.cases (Classical.choose hp) ty i ≤ cap :=
      by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hk
      · exact hcap j
    rw [compile, C.mem_compl cap ty hcap,
      C.mem_existsSet cap ty hcap (Classical.choose hp) hk]
    simp only [not_exists, FormulaHolds]
    apply forall_congr'
    intro a
    rw [C.mem_compl cap (Fin.cases (Classical.choose hp) ty) hcap',
      mem_compile cap (Fin.cases (Classical.choose hp) ty) p hcap' hbody (DVec.cons a xs)]
    tauto

/-- Chosen comprehension object produced by the uniform compiler. -/
@[expose]
noncomputable def comprehensionSet {n : Nat} (p : Formula (n + 1))
    (hp : Formula.Stratified p) (xs : DVec S n) : S :=
  let cs := Formula.cappedStratification p hp
  C.slice cs.cap cs.ty (C.compile cs.cap cs.ty p cs.certificate) xs

/-- Every cylinder algebra validates the complete standard NF schema. -/
theorem mem_comprehensionSet {n : Nat} (p : Formula (n + 1)) (hp : Formula.Stratified p)
    (xs : DVec S n) (z : S) :
    Mem S z (C.comprehensionSet p hp xs) ↔ FormulaHolds S (DVec.cons z xs) p :=
  by
  let cs := Formula.cappedStratification p hp
  change Mem S z (C.slice cs.cap cs.ty (C.compile cs.cap cs.ty p cs.certificate) xs) ↔ _
  rw [C.mem_slice cs.cap cs.ty cs.bounded,
    C.mem_compile cs.cap cs.ty p cs.bounded cs.certificate (DVec.cons z xs)]

end CylinderAlgebra

end NFStandard

end NFChoice.Foundation
