/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Core.System
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.FinCases

/-!
# The interaction combinators

Lafont's system: three symbols and six rules. The names: `con` is Lafont's constructor
`γ`, `dup` his duplicator `δ`, and `era` his eraser `ε`.

Port order follows Lafont's Fig. 2. Annihilation of two `con` cells exchanges the auxiliary ports;
annihilation of two `dup` cells does not. This is Lafont's system, not the symmetric one in which
both annihilations are the same.

Contents, in the order of the file:

1. Symbols and cells: `Comb`, `sig`, `mkCon`, `mkDup`, `mkEra`.
2. Simplification lemmas on cells (`vars_mk…`, `bind_mk…`, `below_mk…`) and the induction
   principle `Comb.induction`.
3. The six rules: `ruleConCon`, `ruleDupDup`, `ruleEraEra`, `ruleEraBin` (used for `era`–`con` and
   for `era`–`dup`), `ruleConDup`, and the system `system`.
4. The system is well formed: the `rule…_linear`, `rule…_reduced` and `rule…_swap` lemmas, then
   `system_wellFormed`.
5. Nets of combinators and the six interactions: `CNet`, `Red`, `inst_eraBin`, `inst_conDup`,
   `step_con_con`, `step_dup_dup`, `step_era_era`, `step_era_con`, `step_era_dup`,
   `step_con_dup`.
6. Wire substitution at the auxiliary ports of a cell: `subst_mkCon`, `subst_mkDup`,
   `subst_var_self`, `wire_con_left`, `wire_con_right`, `wire_dup_left`, `wire_dup_right`.
-/

@[expose] public section

namespace INet

-- ============================================================================================
-- 1. Symbols and cells
-- ============================================================================================

/-- The three combinators. -/
inductive Comb : Type
  -- the constructor, Lafont's `γ`
  | con
  -- the duplicator, Lafont's `δ`
  | dup
  -- the eraser, Lafont's `ε`
  | era
  deriving DecidableEq

namespace Comb

/-- The signature of the combinators: `con` and `dup` have two auxiliary ports, `era` none. -/
def sig : Signature where
  Sym := Comb
  arity
    | con => 2
    | dup => 2
    | era => 0

-- the type of names
variable {ν : Type}

/-- A `con` cell with trees on its auxiliary ports (Lafont's `γ`). -/
def mkCon
    -- the trees on the left and on the right auxiliary port
    (a b : Term sig ν) :
    Term sig ν :=
  .app Comb.con ![a, b]

/-- A `dup` cell with trees on its auxiliary ports (Lafont's `δ`). -/
def mkDup
    -- the trees on the left and on the right auxiliary port
    (a b : Term sig ν) :
    Term sig ν :=
  .app Comb.dup ![a, b]

/-- An `era` cell (Lafont's `ε`). -/
def mkEra : Term sig ν :=
  .app Comb.era ![]

-- ============================================================================================
-- 2. Simplification lemmas on cells, and induction
-- ============================================================================================

-- the names of a `con` cell are those of its two subtrees
@[simp] theorem vars_mkCon (a b : Term sig ν) : (mkCon a b).vars = a.vars + b.vars := by
  simp [mkCon, sig, Fin.sum_univ_two]
-- the names of a `dup` cell are those of its two subtrees
@[simp] theorem vars_mkDup (a b : Term sig ν) : (mkDup a b).vars = a.vars + b.vars := by
  simp [mkDup, sig, Fin.sum_univ_two]
-- an `era` cell has no name
@[simp] theorem vars_mkEra : (mkEra : Term sig ν).vars = 0 := by
  simp [mkEra, sig]

-- plugging trees into the names of a `con` cell plugs them into its two subtrees
@[simp] theorem bind_mkCon {μ : Type} (f : ν → Term sig μ) (a b : Term sig ν) :
    (mkCon a b).bind f = mkCon (a.bind f) (b.bind f) := by
  change Term.app Comb.con (fun i => (![a, b] i).bind f) = Term.app Comb.con _
  congr 1; funext i; fin_cases i <;> rfl
-- plugging trees into the names of a `dup` cell plugs them into its two subtrees
@[simp] theorem bind_mkDup {μ : Type} (f : ν → Term sig μ) (a b : Term sig ν) :
    (mkDup a b).bind f = mkDup (a.bind f) (b.bind f) := by
  change Term.app Comb.dup (fun i => (![a, b] i).bind f) = Term.app Comb.dup _
  congr 1; funext i; fin_cases i <;> rfl
-- plugging trees into the names of an `era` cell changes nothing
@[simp] theorem bind_mkEra {μ : Type} (f : ν → Term sig μ) :
    (mkEra : Term sig ν).bind f = mkEra := by
  change Term.app (S := sig) Comb.era _ = Term.app (S := sig) Comb.era _
  congr 1; funext (i : Fin 0); exact i.elim0

-- a `con` cell is below `k` exactly when its two subtrees are
@[simp] theorem below_mkCon {k : ℕ} {a b : Term sig ℕ} :
    (mkCon a b).Below k ↔ a.Below k ∧ b.Below k := by
  simp [Term.Below, or_imp, forall_and]
-- a `dup` cell is below `k` exactly when its two subtrees are
@[simp] theorem below_mkDup {k : ℕ} {a b : Term sig ℕ} :
    (mkDup a b).Below k ↔ a.Below k ∧ b.Below k := by
  simp [Term.Below, or_imp, forall_and]
-- an `era` cell is below every bound
@[simp] theorem below_mkEra {k : ℕ} : (mkEra : Term sig ℕ).Below k := by simp [Term.Below]

/-- Induction on trees of combinators. -/
theorem induction
    -- the property to prove
    {P : Term sig ν → Prop}
    -- it holds for a leaf
    (var : ∀ x, P (.var x))
    -- it holds for an `era` cell
    (era : P mkEra)
    -- it holds for a `con` cell when it holds for its two subtrees
    (con : ∀ a b, P a → P b → P (mkCon a b))
    -- it holds for a `dup` cell when it holds for its two subtrees
    (dup : ∀ a b, P a → P b → P (mkDup a b)) :
    -- then it holds for every tree
    ∀ t, P t := by
  intro t
  induction t with
  | var x => exact var x
  | app α ts ih =>
    cases α with
    | con =>
      have : ts = ![ts (0 : Fin 2), ts (1 : Fin 2)] := by
        funext (i : Fin 2); fin_cases i <;> rfl
      rw [this]; exact con _ _ (ih (0 : Fin 2)) (ih (1 : Fin 2))
    | dup =>
      have : ts = ![ts (0 : Fin 2), ts (1 : Fin 2)] := by
        funext (i : Fin 2); fin_cases i <;> rfl
      rw [this]; exact dup _ _ (ih (0 : Fin 2)) (ih (1 : Fin 2))
    | era =>
      have : ts = ![] := by funext (i : Fin 0); exact i.elim0
      rw [this]; exact era

-- ============================================================================================
-- 3. The six rules
-- ============================================================================================

section Rules

-- The names of a right-hand side, for a first cell with `a` auxiliary ports, a second cell with
-- `b`, and `m` wires created by the rule.

/-- The `i`-th auxiliary port of the first cell. -/
def l {a b m : ℕ} (i : Fin a) : Term sig (Fin a ⊕ Fin b ⊕ Fin m) := .var (.inl i)
/-- The `i`-th auxiliary port of the second cell. -/
def r {a b m : ℕ} (i : Fin b) : Term sig (Fin a ⊕ Fin b ⊕ Fin m) := .var (.inr (.inl i))
/-- The `i`-th wire created by the rule. -/
def w {a b m : ℕ} (i : Fin m) : Term sig (Fin a ⊕ Fin b ⊕ Fin m) := .var (.inr (.inr i))

/-- `con`–`con` annihilation: the auxiliary ports are exchanged. -/
def ruleConCon : Rule sig 2 2 :=
  -- no new wire; left port to right port, right port to left port
  ⟨0, s(l 0, r 1) ::ₘ {s(l 1, r 0)}⟩

/-- `dup`–`dup` annihilation: the auxiliary ports are joined in order. -/
def ruleDupDup : Rule sig 2 2 :=
  -- no new wire; left port to left port, right port to right port
  ⟨0, s(l 0, r 0) ::ₘ {s(l 1, r 1)}⟩

/-- `era`–`era` annihilation: nothing is left. -/
def ruleEraEra : Rule sig 0 0 :=
  -- no new wire, and the empty net
  ⟨0, 0⟩

/-- `era`–`con` and `era`–`dup` commutation: an eraser on each auxiliary port. -/
def ruleEraBin : Rule sig 0 2 :=
  -- no new wire; one `era` on each auxiliary port of the second cell
  ⟨0, s(mkEra, r 0) ::ₘ {s(mkEra, r 1)}⟩

/-- `con`–`dup` commutation: each cell is copied and four wires are created. -/
def ruleConDup : Rule sig 2 2 :=
  -- four new wires; a `dup` on each auxiliary port of the `con`, a `con` on each auxiliary port
  -- of the `dup`; the wire `w 0` joins the left `dup` to the left `con`, `w 1` the left `dup` to
  -- the right `con`, `w 2` the right `dup` to the left `con`, `w 3` the right `dup` to the right
  -- `con`
  ⟨4, s(l 0, mkDup (w 0) (w 1)) ::ₘ s(l 1, mkDup (w 2) (w 3)) ::ₘ
    s(r 0, mkCon (w 0) (w 2)) ::ₘ {s(r 1, mkCon (w 1) (w 3))}⟩

end Rules

/-- Lafont's system of interaction combinators. -/
def system : System sig where
  rule
    -- the three annihilations
    | con, con => some ruleConCon
    | dup, dup => some ruleDupDup
    | era, era => some ruleEraEra
    -- the three commutations
    | era, con => some ruleEraBin
    | era, dup => some ruleEraBin
    | con, dup => some ruleConDup
    -- the same pairs in the other order have no rule of their own: an equation is unordered
    | _, _ => none

-- ============================================================================================
-- 4. The system is well formed
-- ============================================================================================

section WellFormed

-- Each rule is linear: every auxiliary port occurs once, every created wire twice.

theorem ruleConCon_linear : ruleConCon.Linear :=
  ⟨by decide, by decide, by decide⟩

theorem ruleDupDup_linear : ruleDupDup.Linear :=
  ⟨by decide, by decide, by decide⟩

theorem ruleEraEra_linear : ruleEraEra.Linear :=
  ⟨fun i => i.elim0, fun j => j.elim0, fun w => w.elim0⟩

theorem ruleEraBin_linear : ruleEraBin.Linear :=
  ⟨by decide, by decide, by decide⟩

theorem ruleConDup_linear : ruleConDup.Linear :=
  ⟨by decide, by decide, by decide⟩

-- Each rule is reduced: every equation has an auxiliary port on one side.

theorem ruleConCon_reduced : ruleConCon.Reduced := by
  intro e he
  unfold ruleConCon at he
  dsimp only at he
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inl 0, _, rfl, by simp⟩
  obtain rfl := Multiset.mem_singleton.1 he
  exact ⟨.inl 1, _, rfl, by simp⟩

theorem ruleDupDup_reduced : ruleDupDup.Reduced := by
  intro e he
  unfold ruleDupDup at he
  dsimp only at he
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inl 0, _, rfl, by simp⟩
  obtain rfl := Multiset.mem_singleton.1 he
  exact ⟨.inl 1, _, rfl, by simp⟩

theorem ruleEraEra_reduced : ruleEraEra.Reduced := by
  intro e he
  exact (Multiset.notMem_zero _ he).elim

theorem ruleEraBin_reduced : ruleEraBin.Reduced := by
  intro e he
  unfold ruleEraBin at he
  dsimp only at he
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inr (.inl 0), mkEra, Sym2.eq_swap, by simp⟩
  obtain rfl := Multiset.mem_singleton.1 he
  exact ⟨.inr (.inl 1), mkEra, Sym2.eq_swap, by simp⟩

theorem ruleConDup_reduced : ruleConDup.Reduced := by
  intro e he
  unfold ruleConDup at he
  dsimp only at he
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inl 0, _, rfl, by simp⟩
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inl 1, _, rfl, by simp⟩
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inr (.inl 0), _, rfl, by simp⟩
  obtain rfl := Multiset.mem_singleton.1 he
  exact ⟨.inr (.inl 1), _, rfl, by simp⟩

-- Each rule of a symbol with itself, read from the other cell, is the same net.

theorem ruleConCon_swap : ruleConCon.swap.net = ruleConCon.net := by
  change (s(Term.var (.inr (.inl 0)), Term.var (.inl 1)) ::ₘ
      {s(Term.var (.inr (.inl 1)), Term.var (.inl 0))} : Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 0)) =
    s(Term.var (.inl 0), Term.var (.inr (.inl 1))) ::ₘ
      {s(Term.var (.inl 1), Term.var (.inr (.inl 0)))}
  exact (congrArg₂ (fun x y => (x ::ₘ {y} : Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 0)))
    Sym2.eq_swap Sym2.eq_swap).trans (Multiset.pair_comm _ _)

theorem ruleDupDup_swap : ruleDupDup.swap.net = ruleDupDup.net := by
  change (s(Term.var (.inr (.inl 0)), Term.var (.inl 0)) ::ₘ
      {s(Term.var (.inr (.inl 1)), Term.var (.inl 1))} : Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 0)) =
    s(Term.var (.inl 0), Term.var (.inr (.inl 0))) ::ₘ
      {s(Term.var (.inl 1), Term.var (.inr (.inl 1)))}
  exact congrArg₂ (fun x y => (x ::ₘ {y} : Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 0)))
    Sym2.eq_swap Sym2.eq_swap

theorem ruleEraEra_swap : ruleEraEra.swap.net = ruleEraEra.net := by
  simp [Rule.swap, Net.bind, ruleEraEra]

/-- Lafont's combinators form an interaction system. -/
theorem system_wellFormed : system.WellFormed where
  linear := by
    intro α β r h
    cases α <;> cases β <;> cases h <;>
      first
        | exact ruleConCon_linear | exact ruleDupDup_linear | exact ruleEraEra_linear
        | exact ruleEraBin_linear | exact ruleConDup_linear
  reduced := by
    intro α β r h
    cases α <;> cases β <;> cases h <;>
      first
        | exact ruleConCon_reduced | exact ruleDupDup_reduced | exact ruleEraEra_reduced
        | exact ruleEraBin_reduced | exact ruleConDup_reduced
  unique := by
    intro α β hne h
    cases α <;> cases β <;> first | rfl | exact absurd rfl hne | cases h
  symm := by
    refine fun α r h => Rule.symm_of_equiv ?_
    revert α r h
    intro α r h
    cases α <;> cases h <;>
      first
        | exact Equiv.of_eq ruleConCon_swap | exact Equiv.of_eq ruleDupDup_swap
        | exact Equiv.of_eq ruleEraEra_swap

end WellFormed

-- ============================================================================================
-- 5. Nets of combinators and the six interactions
-- ============================================================================================

/-- Nets of combinators with natural-number names. -/
abbrev CNet := Net sig ℕ

/-- Reduction of nets of combinators. -/
abbrev Red : CNet → CNet → Prop := Steps system

section Steps

-- for this section: the trees on the auxiliary ports of the two cells, `a` and `b` for the first
-- cell, `c` and `d` for the second, and the rest of the net
variable (a b c d : Term sig ℕ) (Δ : CNet)

/-- The right-hand side of `era` against a binary cell: an `era` on each of `a` and `b`. -/
theorem inst_eraBin
    -- the names of the wires created by the rule: there is none
    (f : Fin 0 → ℕ) :
    ruleEraBin.inst (![] : Fin 0 → Term sig ℕ) ![a, b] f = s(mkEra, a) ::ₘ {s(mkEra, b)} := by
  simp [Rule.inst, Net.bind, ruleEraBin, r]

/-- The right-hand side of `con` against `dup`: a `dup` on each of `a` and `b`, a `con` on each of
`c` and `d`, and four wires between them. -/
theorem inst_conDup
    -- the names of the four wires created by the rule
    (f : Fin 4 → ℕ) :
    ruleConDup.inst ![a, b] ![c, d] f =
      s(a, mkDup (.var (f 0)) (.var (f 1))) ::ₘ s(b, mkDup (.var (f 2)) (.var (f 3))) ::ₘ
        s(c, mkCon (.var (f 0)) (.var (f 2))) ::ₘ {s(d, mkCon (.var (f 1)) (.var (f 3)))} := by
  simp [Rule.inst, Net.bind, ruleConDup, l, r, w]

/-- `con`–`con` annihilation: `a` is joined to `d` and `b` to `c` (the ports are exchanged). -/
theorem step_con_con :
    Step system (s(mkCon a b, mkCon c d) ::ₘ Δ) (s(a, d) ::ₘ s(b, c) ::ₘ Δ) := by
  have h : Step system (s(mkCon a b, mkCon c d) ::ₘ Δ) ((s(a, d) ::ₘ {s(b, c)} : CNet) + Δ) :=
    Step.mk (I := system) con con ruleConCon rfl ![a, b] ![c, d] Δ
      (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
  simpa using h

/-- `dup`–`dup` annihilation: `a` is joined to `c` and `b` to `d` (the ports are kept in order). -/
theorem step_dup_dup :
    Step system (s(mkDup a b, mkDup c d) ::ₘ Δ) (s(a, c) ::ₘ s(b, d) ::ₘ Δ) := by
  have h : Step system (s(mkDup a b, mkDup c d) ::ₘ Δ) ((s(a, c) ::ₘ {s(b, d)} : CNet) + Δ) :=
    Step.mk (I := system) dup dup ruleDupDup rfl ![a, b] ![c, d] Δ
      (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
  simpa using h

/-- `era`–`era` annihilation: nothing is left. -/
theorem step_era_era : Step system (s(mkEra, mkEra) ::ₘ Δ) Δ := by
  have h : Step system (s(mkEra, mkEra) ::ₘ Δ) ((0 : CNet) + Δ) :=
    Step.mk (I := system) era era ruleEraEra rfl ![] ![] Δ
      (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
  simpa using h

/-- `era`–`con` commutation: an `era` on each auxiliary port of the `con`. -/
theorem step_era_con :
    Step system (s(mkEra, mkCon a b) ::ₘ Δ) (s(mkEra, a) ::ₘ s(mkEra, b) ::ₘ Δ) := by
  have h : Step system (s(mkEra, mkCon a b) ::ₘ Δ)
      (ruleEraBin.inst (![] : Fin 0 → Term sig ℕ) ![a, b] (Fin.elim0 : Fin 0 → ℕ) + Δ) :=
    Step.mk (I := system) era con ruleEraBin rfl ![] ![a, b] Δ
      (Fin.elim0 : Fin 0 → ℕ) (fun (i : Fin 0) => i.elim0) (fun (i : Fin 0) => i.elim0)
  rw [inst_eraBin] at h
  simpa using h

/-- `era`–`dup` commutation: an `era` on each auxiliary port of the `dup`. -/
theorem step_era_dup :
    Step system (s(mkEra, mkDup a b) ::ₘ Δ) (s(mkEra, a) ::ₘ s(mkEra, b) ::ₘ Δ) := by
  have h : Step system (s(mkEra, mkDup a b) ::ₘ Δ)
      (ruleEraBin.inst (![] : Fin 0 → Term sig ℕ) ![a, b] (Fin.elim0 : Fin 0 → ℕ) + Δ) :=
    Step.mk (I := system) era dup ruleEraBin rfl ![] ![a, b] Δ
      (Fin.elim0 : Fin 0 → ℕ) (fun (i : Fin 0) => i.elim0) (fun (i : Fin 0) => i.elim0)
  rw [inst_eraBin] at h
  simpa using h

/-- `con`–`dup` commutation: a `dup` on each auxiliary port of the `con`, a `con` on each
auxiliary port of the `dup`, and four new wires `x`, `y`, `z`, `t` between them. -/
theorem step_con_dup
    -- the names of the four new wires: pairwise distinct,
    (x y z t : ℕ)
    (hnd : [x, y, z, t].Nodup)
    -- and not used in the net one starts from
    (hfresh : ∀ v ∈ [x, y, z, t], v ∉ Net.vars (s(mkCon a b, mkDup c d) ::ₘ Δ)) :
    Step system (s(mkCon a b, mkDup c d) ::ₘ Δ)
      -- a `dup` on `a` and a `dup` on `b`,
      (s(a, mkDup (.var x) (.var y)) ::ₘ s(b, mkDup (.var z) (.var t)) ::ₘ
        -- a `con` on `c` and a `con` on `d`, and the rest of the net
        s(c, mkCon (.var x) (.var z)) ::ₘ s(d, mkCon (.var y) (.var t)) ::ₘ Δ) := by
  have hinj : Function.Injective (![x, y, z, t] : Fin 4 → ℕ) := by
    intro i j h
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true] at hnd
    fin_cases i <;> fin_cases j <;> simp_all
  have hfr : ∀ i : Fin 4, (![x, y, z, t] : Fin 4 → ℕ) i ∉
      Net.vars (s(mkCon a b, mkDup c d) ::ₘ Δ) := by
    intro i
    fin_cases i
    · exact hfresh x (by simp)
    · exact hfresh y (by simp)
    · exact hfresh z (by simp)
    · exact hfresh t (by simp)
  have h : Step system (s(mkCon a b, mkDup c d) ::ₘ Δ)
      (ruleConDup.inst ![a, b] ![c, d] (![x, y, z, t] : Fin 4 → ℕ) + Δ) :=
    Step.mk (I := system) con dup ruleConDup rfl ![a, b] ![c, d] Δ ![x, y, z, t] hinj hfr
  rw [inst_conDup] at h
  simpa using h

end Steps

-- ============================================================================================
-- 6. Wire substitution at the auxiliary ports of a cell
-- ============================================================================================

section WireShapes

open Term

-- for this section: the wire `x`, the tree `t` on one of its ends, the tree `r` on the root of
-- the cell that holds its other end, the tree `c` on the other auxiliary port of that cell, and
-- the rest of the net
variable {x : ℕ} {t r c : Term sig ℕ} {Δ : CNet}

-- plugging a tree into a name of a `con` cell plugs it into its two subtrees
theorem subst_mkCon (a b : Term sig ℕ) (x : ℕ) (t : Term sig ℕ) :
    (mkCon a b).subst x t = mkCon (a.subst x t) (b.subst x t) := by simp [Term.subst]
-- plugging a tree into a name of a `dup` cell plugs it into its two subtrees
theorem subst_mkDup (a b : Term sig ℕ) (x : ℕ) (t : Term sig ℕ) :
    (mkDup a b).subst x t = mkDup (a.subst x t) (b.subst x t) := by simp [Term.subst]
-- plugging a tree into the leaf of that name gives the tree
theorem subst_var_self (x : ℕ) (t : Term sig ℕ) : (var x : Term sig ℕ).subst x t = t := by
  simp [Term.subst]

/-- A wire that ends on the left auxiliary port of a `con` cell: the tree on its other end is
plugged there. -/
theorem wire_con_left
    -- the net one starts from is linear: the wire, the cell, and the rest of the net
    (hlin : Net.Linear (s(var x, t) ::ₘ s(r, mkCon (var x) c) ::ₘ Δ)) :
    Wire (s(var x, t) ::ₘ s(r, mkCon (var x) c) ::ₘ Δ) (s(r, mkCon t c) ::ₘ Δ) := by
  have h := Wire.mk x t r (mkCon (var x) c) Δ hlin (by simp)
  have hx := hlin x
  simp only [Net.vars_cons, eqVars_mk, vars_var, vars_mkCon, Multiset.count_add,
    Multiset.count_singleton_self] at hx
  have hr : x ∉ r.vars := Multiset.count_eq_zero.1 (by omega)
  have hc : x ∉ c.vars := Multiset.count_eq_zero.1 (by omega)
  rwa [subst_mkCon, subst_var_self, subst_of_notMem hr, subst_of_notMem hc] at h

/-- A wire that ends on the right auxiliary port of a `con` cell: the tree on its other end is
plugged there. -/
theorem wire_con_right
    -- the net one starts from is linear: the wire, the cell, and the rest of the net
    (hlin : Net.Linear (s(var x, t) ::ₘ s(r, mkCon c (var x)) ::ₘ Δ)) :
    Wire (s(var x, t) ::ₘ s(r, mkCon c (var x)) ::ₘ Δ) (s(r, mkCon c t) ::ₘ Δ) := by
  have h := Wire.mk x t r (mkCon c (var x)) Δ hlin (by simp)
  have hx := hlin x
  simp only [Net.vars_cons, eqVars_mk, vars_var, vars_mkCon, Multiset.count_add,
    Multiset.count_singleton_self] at hx
  have hr : x ∉ r.vars := Multiset.count_eq_zero.1 (by omega)
  have hc : x ∉ c.vars := Multiset.count_eq_zero.1 (by omega)
  rwa [subst_mkCon, subst_var_self, subst_of_notMem hr, subst_of_notMem hc] at h

/-- A wire that ends on the left auxiliary port of a `dup` cell: the tree on its other end is
plugged there. -/
theorem wire_dup_left
    -- the net one starts from is linear: the wire, the cell, and the rest of the net
    (hlin : Net.Linear (s(var x, t) ::ₘ s(r, mkDup (var x) c) ::ₘ Δ)) :
    Wire (s(var x, t) ::ₘ s(r, mkDup (var x) c) ::ₘ Δ) (s(r, mkDup t c) ::ₘ Δ) := by
  have h := Wire.mk x t r (mkDup (var x) c) Δ hlin (by simp)
  have hx := hlin x
  simp only [Net.vars_cons, eqVars_mk, vars_var, vars_mkDup, Multiset.count_add,
    Multiset.count_singleton_self] at hx
  have hr : x ∉ r.vars := Multiset.count_eq_zero.1 (by omega)
  have hc : x ∉ c.vars := Multiset.count_eq_zero.1 (by omega)
  rwa [subst_mkDup, subst_var_self, subst_of_notMem hr, subst_of_notMem hc] at h

/-- A wire that ends on the right auxiliary port of a `dup` cell: the tree on its other end is
plugged there. -/
theorem wire_dup_right
    -- the net one starts from is linear: the wire, the cell, and the rest of the net
    (hlin : Net.Linear (s(var x, t) ::ₘ s(r, mkDup c (var x)) ::ₘ Δ)) :
    Wire (s(var x, t) ::ₘ s(r, mkDup c (var x)) ::ₘ Δ) (s(r, mkDup c t) ::ₘ Δ) := by
  have h := Wire.mk x t r (mkDup c (var x)) Δ hlin (by simp)
  have hx := hlin x
  simp only [Net.vars_cons, eqVars_mk, vars_var, vars_mkDup, Multiset.count_add,
    Multiset.count_singleton_self] at hx
  have hr : x ∉ r.vars := Multiset.count_eq_zero.1 (by omega)
  have hc : x ∉ c.vars := Multiset.count_eq_zero.1 (by omega)
  rwa [subst_mkDup, subst_var_self, subst_of_notMem hr, subst_of_notMem hc] at h

end WireShapes

end Comb

end INet
