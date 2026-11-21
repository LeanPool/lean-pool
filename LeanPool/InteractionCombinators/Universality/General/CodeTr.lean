/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.General.CodeGamma
public import LeanPool.InteractionCombinators.Universality.RecursionFree.RecursionFreeStrict
public import Mathlib.Data.Finset.Sort

/-!
# The principal net `[α]` of Fig. 10 and its strictness (pages 89–90)

Lafont 1997, Section 2.7, journal pages 88–89 (PDF 20–21), Fig. 10, top left: "a principal net
`[α_i]` can be defined for each symbol `α_i` as in Fig. 10". It is the cell of Fig. 6 (page 86),
the transpositor `T_{1,1}` carrying the menu `Γ_i` and the selector `S^i_m` on the multiplexor
`M_{n_i+2}`, whose first leaf is the package `!Γ`, the code of `Γ = Γ_1 & ⋯ & Γ_m` (the "genetic
code"), followed by the `n_i` ports and the loop `ℓ`.

**The names.** The ports of `α` are `0, …, n - 1`, the loop is `n`, the menu `Γ_α` takes the block
of names above `n + 1` (`codeCellMenu side α (n + 1)`), the menu `Γ` the next block
(`codeMenus side (codeMenuBase side α)`), and the code `!Γ` numbers its cut names from the end of
that block (`codeKey side α`). The cut names of `decomp` are distinct and above that bound, but not
consecutive. So the principal net is built by a general constructor `treePNet`: a tree whose names
`< n` occur once and whose other names occur twice is a principal net with `n` ports, its other
names numbered in increasing order as internal wires.

Contents, in the order of the file:

1. A tree as a principal net: `wireSet`, `wireNum` (the numbering of the internal names by rank)
   and `wireNum_strictMono`; `treeLeaf`, `treeName` and their lemmas; `treePNet`, a tree with
   ports `0, …, n - 1` and every other name twice, as a `PNet`; `treePNet_inst` (the instance
   with the ports and wires named back gives the tree), `treePNet_strict`, and `treePNet_hyps`
   (the hypotheses from `Ico 0 n + 2 • X`).
2. The tree of `[α]` for a given numbering `e : S.Sym ≃ Fin n` of the symbols (computable; page
   90: no order on the symbols is needed): `codeMenuBaseE`, `codeKeyE`, `codeTreeE`,
   `vars_codeTreeE`, `codeTreeE_hyps`; the principal net `codeNetE`, `codeNetE_inst`,
   `codeNetE_strict`, and the translation `codeTranslationE`.
3. The tree of `[α]` for the numbering `symEnum S`: `codeMenuBase`, `codeKey`, `codeTree`,
   `vars_codeTree`, `codeTree_hyps`.
4. Main result: the principal net `codeNet`, the translation `codeTranslation`, and
   `codeTranslation_strict`: the translation is strict (definition page 80), since the root of
   `[α]` is the root of `T_{1,1}`, a `dup` cell.
-/

@[expose] public section

namespace INet.Comb

open Term Translation

-- ============================================================================================
-- 1. A tree as a principal net
-- ============================================================================================

/-- The internal names of a tree with `n` ports: its names `≥ n`. -/
def wireSet
    -- the number of ports, and the tree
    (n : ℕ)
    (t : Term sig ℕ) :
    Finset ℕ :=
  t.vars.toFinset.filter (n ≤ ·)

/-- The numbering of the internal names of a tree with `n` ports (page 80): each name of
`wireSet n t` is sent to its rank, so the internal wires are numbered in increasing order. -/
def wireNum
    -- the number of ports, and the tree
    (n : ℕ)
    (t : Term sig ℕ) :
    wireSet n t ≃ Fin (wireSet n t).card :=
  ((wireSet n t).orderIsoOfFin rfl).symm.toEquiv

/-- **The numbering `wireNum` is increasing** (page 80): a smaller internal name gets a smaller
wire number. -/
theorem wireNum_strictMono
    -- the number of ports, and the tree
    (n : ℕ)
    (t : Term sig ℕ) :
    StrictMono (wireNum n t) :=
  ((wireSet n t).orderIsoOfFin rfl).symm.strictMono

/-- The inverse numbering is increasing too (page 80): wire `i` is the `i`-th internal name. -/
theorem wireNum_symm_strictMono
    -- the number of ports, and the tree
    (n : ℕ)
    (t : Term sig ℕ) :
    StrictMono (wireNum n t).symm :=
  ((wireSet n t).orderIsoOfFin rfl).strictMono

/-- The leaf of a name `x` of `t`: the port `x` if `x < n`, otherwise the internal wire numbered by
the rank of `x` among the internal names. (The eraser is never used for a name of `t`.) -/
def treeLeaf
    -- the number of ports, and the tree
    (n : ℕ)
    (t : Term sig ℕ)
    -- the name
    (x : ℕ) :
    Term sig (Fin n ⊕ Fin (wireSet n t).card) :=
  if h : x < n then var (.inl ⟨x, h⟩)
  else if h' : x ∈ wireSet n t then var (.inr ((wireNum n t) ⟨x, h'⟩))
  else mkEra

/-- The leaf of a name that occurs in `t`. -/
def treeName
    -- the number of ports, and the tree
    (n : ℕ)
    (t : Term sig ℕ)
    -- a name of the tree
    (x : {x // x ∈ t.vars}) :
    Fin n ⊕ Fin (wireSet n t).card :=
  if h : x.1 < n then .inl ⟨x.1, h⟩
  else .inr ((wireNum n t)
    ⟨x.1, Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 x.2, not_lt.1 h⟩⟩)

/-- Distinct names of `t` have distinct leaves (page 80). -/
theorem treeName_injective
    -- the number of ports, and the tree
    (n : ℕ)
    (t : Term sig ℕ) :
    Function.Injective (treeName n t) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  unfold treeName at h
  by_cases h1 : x < n <;> by_cases h2 : y < n
  · simp only [h1, h2, dite_true, Sum.inl.injEq, Fin.mk.injEq] at h
    exact Subtype.ext h
  · simp [h1, h2] at h
  · simp [h1, h2] at h
  · simp only [h1, h2, dite_false, Sum.inr.injEq] at h
    have := (wireNum n t).injective h
    exact Subtype.ext (by simpa using congrArg Subtype.val this)

/-- The leaf of a name `x` of `t` has the single name `treeName n t x` (page 80). -/
theorem vars_treeLeaf
    -- the number of ports, and the tree
    (n : ℕ)
    (t : Term sig ℕ)
    -- a name of the tree
    (x : ℕ)
    (hx : x ∈ t.vars) :
    (treeLeaf n t x).vars = {treeName n t ⟨x, hx⟩} := by
  unfold treeLeaf treeName
  by_cases h1 : x < n
  · simp [h1]
  · have h2 : x ∈ wireSet n t :=
      Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 hx, not_lt.1 h1⟩
    simp [h1, h2]

/-- The names of the tree of `treePNet`: each name `x` of `t` becomes its leaf, with
multiplicity. -/
theorem vars_bind_treeLeaf
    -- the number of ports, and the tree
    (n : ℕ)
    (t : Term sig ℕ) :
    (t.bind (treeLeaf n t)).vars = t.vars.attach.map (treeName n t) := by
  rw [vars_bind]
  conv_lhs => rw [← Multiset.attach_map_val t.vars]
  rw [Multiset.bind_map, ← Multiset.bind_singleton]
  exact Multiset.bind_congr fun x _ => vars_treeLeaf n t x.1 x.2

/-- **A tree as a principal net** (principal nets, page 80). A tree `t` whose names `0, …, n - 1`
occur once and whose names `≥ n` occur twice is a principal net with `n` auxiliary ports: the names
`< n` are the ports, the names `≥ n` the internal wires, numbered in increasing order. -/
def treePNet
    -- the number of ports
    (n : ℕ)
    -- the tree: each port once, every other name twice
    (t : Term sig ℕ)
    (hp : ∀ i < n, t.vars.count i = 1)
    (hw : ∀ x ∈ t.vars, n ≤ x → t.vars.count x = 2) :
    PNet sig n where
  internal := (wireSet n t).card
  tree := t.bind (treeLeaf n t)
  port_count i := by
    have hi : (i : ℕ) ∈ t.vars := Multiset.count_pos.1 (by rw [hp i i.isLt]; omega)
    have e : (Sum.inl i : Fin n ⊕ Fin (wireSet n t).card) = treeName n t ⟨i, hi⟩ := by
      simp [treeName, i.isLt]
    rw [vars_bind_treeLeaf, e, Multiset.count_map_eq_count' _ _ (treeName_injective n t),
      Multiset.count_attach]
    exact hp i i.isLt
  internal_count w := by
    have hx := Finset.mem_filter.1 ((wireNum n t).symm w).2
    have hxv : ((wireNum n t).symm w).1 ∈ t.vars := Multiset.mem_toFinset.1 hx.1
    have e : (Sum.inr w : Fin n ⊕ Fin (wireSet n t).card) =
        treeName n t ⟨((wireNum n t).symm w).1, hxv⟩ := by
      have hn : ¬ ((wireNum n t).symm w).1 < n := not_lt.2 hx.2
      simp only [treeName, hn, dite_false]
      exact congrArg Sum.inr ((wireNum n t).apply_symm_apply w).symm
    rw [vars_bind_treeLeaf, e, Multiset.count_map_eq_count' _ _ (treeName_injective n t),
      Multiset.count_attach]
    exact hw _ hxv hx.2

/-- **The principal net `treePNet` is the tree `t`** (page 80): its instance with the port `i`
named `i` and each internal wire named back by the numbering of `wireSet` is `t`. -/
theorem treePNet_inst
    -- the number of ports
    (n : ℕ)
    -- the tree: each port once, every other name twice
    (t : Term sig ℕ)
    (hp : ∀ i < n, t.vars.count i = 1)
    (hw : ∀ x ∈ t.vars, n ≤ x → t.vars.count x = 2) :
    -- the port `i` named `i`, the wire `w` named by the name of rank `w`: this is `t`
    (treePNet n t hp hw).inst (fun i => var (i : ℕ)) (fun w => ((wireNum n t).symm w).1) =
      t := by
  change (t.bind (treeLeaf n t)).bind (Sum.elim (fun i : Fin n => var (i : ℕ))
    fun w : Fin (wireSet n t).card => var ((wireNum n t).symm w).1) = t
  rw [Term.bind_bind]
  conv_rhs => rw [← Term.bind_var_self t]
  refine Term.bind_congr fun x hx => ?_
  unfold treeLeaf
  by_cases h1 : x < n
  · simp [h1]
  · have h2 : x ∈ wireSet n t :=
      Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 hx, not_lt.1 h1⟩
    simp [h1, h2]

/-- **A tree that is not a wire gives a strict principal net** (definition page 80). -/
theorem treePNet_strict
    -- the number of ports
    (n : ℕ)
    -- the tree: each port once, every other name twice, and not a wire
    (t : Term sig ℕ)
    (hp : ∀ i < n, t.vars.count i = 1)
    (hw : ∀ x ∈ t.vars, n ≤ x → t.vars.count x = 2)
    (ht : ∀ x, t ≠ var x) :
    (treePNet n t hp hw).Strict := by
  intro x hx
  change t.bind (treeLeaf n t) = var x at hx
  cases t with
  | var y => exact ht y rfl
  | app α ts =>
    rw [bind_app] at hx
    cases hx

/-- The hypotheses of `treePNet` (page 80) for a tree whose names are the ports `0, …, n - 1` once
and both ends of each name of a multiset `X` without repetition, above `n`. -/
theorem treePNet_hyps
    -- the number of ports, the tree and its internal names `X`
    {n : ℕ}
    {t : Term sig ℕ}
    {X : Multiset ℕ}
    -- the names of the tree: the ports once, the names of `X` twice
    (h : t.vars = Multiset.Ico 0 n + 2 • X)
    -- the names of `X` are distinct, and none is a port
    (hX : X.Nodup)
    (hXn : ∀ x ∈ X, n ≤ x) :
    -- each port occurs once
    (∀ i < n, t.vars.count i = 1) ∧
      -- and every other name of the tree twice
      (∀ x ∈ t.vars, n ≤ x → t.vars.count x = 2) := by
  refine ⟨fun i hi => ?_, fun x hx hn => ?_⟩
  · have hiX : i ∉ X := fun hm => by have := hXn i hm; omega
    rw [h, Multiset.count_add, Multiset.count_nsmul, Multiset.count_eq_zero.2 hiX, count_Ico]
    simp [hi]
  · have hxX : x ∈ X := by
      rw [h] at hx
      rcases Multiset.mem_add.1 hx with hx | hx
      · rw [Multiset.mem_Ico] at hx; omega
      · exact Multiset.mem_of_mem_nsmul hx
    rw [h, Multiset.count_add, Multiset.count_nsmul, Multiset.count_eq_one_of_mem hX hxX,
      count_Ico]
    split_ifs <;> omega

-- ============================================================================================
-- 2. The tree of `[α]` for a given numbering of the symbols
-- ============================================================================================

-- Fig. 10 numbers the symbols `α_0, …, α_{m-1}`; page 90 notes that no order on the symbols is
-- needed. Here the numbering is an argument `e : S.Sym ≃ Fin n`, so that the tree is computable;
-- the versions without `E` in section 3 take `e := symEnum S`.

/-- The names of the ports `0, …, n - 1`. -/
theorem sum_vars_ofFn_var
    -- the number of ports
    (n : ℕ) :
    ((List.ofFn fun j : Fin n => (var (j : ℕ) : Term sig ℕ)).map Term.vars).sum =
      Multiset.Ico 0 n := by
  rw [List.map_ofFn, List.sum_ofFn, ← map_val_univ]
  simp only [Function.comp_def, vars_var]
  rw [Finset.sum_eq_multiset_sum]
  have h := Multiset.sum_map_singleton (Finset.univ.val.map fun w : Fin n => (w : ℕ))
  rwa [Multiset.map_map] at h

-- the interaction system
variable {S : Signature}

section Enum

-- the numbering `e` of the `n` symbols, and the choice `side` of expanded sides
variable {n : ℕ} (e : S.Sym ≃ Fin n)
  (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

/-- The first name of the menu `Γ` in `[α]`, with the symbols numbered by `e`: after the ports
`0, …, k - 1`, the loop `k` and the block of the menu `Γ_α` (page 89), where `k = S.arity α`. -/
def codeMenuBaseE
    -- the symbol
    (α : S.Sym) :
    ℕ :=
  S.arity α + 1 + ∑ j, codeCellSizesE e side α j

/-- The first cut name of the code `!Γ` in `[α]`, with the symbols numbered by `e`: after the block
of the menu `Γ` (page 89). -/
def codeKeyE
    -- the symbol
    (α : S.Sym) :
    ℕ :=
  codeMenuBaseE e side α + ∑ i, codeMenuSizesE e side i

/-- **The tree of `[α]` of Fig. 10** (top left, page 89), with the `n` symbols numbered by
`e : S.Sym ≃ Fin n`: the transpositor `T_{1,1}` carrying the menu `Γ_α` (names from `k + 1`) and the
selector `S^{e α}_n` on the multiplexor `M_{k+2}`, whose leaves are, from left to right, the code
`!Γ` of `Γ = Γ_0 & ⋯ & Γ_{n-1}` (`Γ` named from `codeMenuBaseE`, the cut names of the code from
`codeKeyE`), the ports `0, …, k - 1`, and the loop `ℓ = k`. Here `k = S.arity α`; Fig. 10 writes
`m` for the number of symbols and `n_i` for the arity. -/
def codeTreeE
    -- the symbol
    (α : S.Sym) :
    Term sig ℕ :=
  cellSkel (menu (codeCellMenuE e side α (S.arity α + 1))) n (e α)
    (code (codeKeyE e side α) (menu (codeMenusE e side (codeMenuBaseE e side α))) ::
      List.ofFn fun j : Fin (S.arity α) => var (j : ℕ)) (S.arity α)

/-- **The names of `[α]` of Fig. 10** (page 89), for any numbering `e` of the symbols: the ports
`0, …, k - 1` once, and twice each the names of `[k, codeKeyE)` (the loop, the names of `Γ_α` and
those of `Γ`) and the cut names of the code `!Γ`, where `k = S.arity α`. -/
theorem vars_codeTreeE
    -- the symbol
    (α : S.Sym) :
    -- the ports once
    (codeTreeE e side α).vars = Multiset.Ico 0 (S.arity α) +
      -- and twice: the loop, the names of the menus, and the cut names of the code
      2 • (Multiset.Ico (S.arity α) (codeKeyE e side α) +
        (decomp (codeKeyE e side α)
          (menu (codeMenusE e side (codeMenuBaseE e side α)))).ports) := by
  have hB : S.arity α + 1 ≤ codeMenuBaseE e side α := Nat.le_add_right _ _
  have hK : codeMenuBaseE e side α ≤ codeKeyE e side α := Nat.le_add_right _ _
  have h1 : Multiset.Ico (S.arity α) (S.arity α + 1) = {S.arity α} :=
    (Multiset.Nodup.ext Multiset.nodup_Ico (Multiset.nodup_singleton _)).2 fun x => by
      simp only [Multiset.mem_Ico, Multiset.mem_singleton]; omega
  have hI : Multiset.Ico (S.arity α) (codeKeyE e side α) = {S.arity α} +
      Multiset.Ico (S.arity α + 1) (codeMenuBaseE e side α) +
      Multiset.Ico (codeMenuBaseE e side α) (codeKeyE e side α) := by
    rw [← h1, Multiset.Ico_add_Ico_eq_Ico (by omega) hB, Multiset.Ico_add_Ico_eq_Ico (by omega) hK]
  have e1 : (menu (codeCellMenuE e side α (S.arity α + 1))).vars =
      2 • Multiset.Ico (S.arity α + 1) (codeMenuBaseE e side α) :=
    vars_menu_codeCellMenuE e side α _
  have e2 : (menu (codeMenusE e side (codeMenuBaseE e side α))).vars =
      2 • Multiset.Ico (codeMenuBaseE e side α) (codeKeyE e side α) :=
    vars_menu_codeMenusE e side _
  rw [codeTreeE, vars_cellSkel, e1, List.map_cons, List.sum_cons, sum_vars_ofFn_var, vars_code,
    e2, hI]
  simp only [smul_add, two_nsmul]
  abel

/-- The names of `[α]` other than the ports are distinct and above the ports (page 89), for any
numbering `e` of the symbols. -/
theorem codeTreeE_wires
    -- the symbol
    (α : S.Sym) :
    -- the loop, the names of the menus and the cut names of the code are distinct
    (Multiset.Ico (S.arity α) (codeKeyE e side α) +
        (decomp (codeKeyE e side α)
          (menu (codeMenusE e side (codeMenuBaseE e side α)))).ports).Nodup ∧
      -- and none of them is a port
      ∀ x ∈ Multiset.Ico (S.arity α) (codeKeyE e side α) +
        (decomp (codeKeyE e side α) (menu (codeMenusE e side (codeMenuBaseE e side α)))).ports,
        S.arity α ≤ x := by
  obtain ⟨hnd, hr, -⟩ :=
    decomp_ports (menu (codeMenusE e side (codeMenuBaseE e side α))) (codeKeyE e side α)
  have hn : S.arity α ≤ codeKeyE e side α := by unfold codeKeyE codeMenuBaseE; omega
  refine ⟨Multiset.nodup_add.2 ⟨Multiset.nodup_Ico, hnd, Multiset.disjoint_left.2 fun hx hy => ?_⟩,
    fun x hx => ?_⟩
  · have := (hr _ hy).1
    rw [Multiset.mem_Ico] at hx
    omega
  · rcases Multiset.mem_add.1 hx with hx | hx
    · exact (Multiset.mem_Ico.1 hx).1
    · exact hn.trans (hr x hx).1

/-- The tree of `[α]` has the ports `0, …, n - 1` once and every other name twice (page 89), for any
numbering `e` of the symbols. -/
theorem codeTreeE_hyps
    -- the symbol
    (α : S.Sym) :
    -- each port occurs once
    (∀ i < S.arity α, (codeTreeE e side α).vars.count i = 1) ∧
      -- and every other name of the tree twice
      (∀ x ∈ (codeTreeE e side α).vars, S.arity α ≤ x → (codeTreeE e side α).vars.count x = 2) :=
  treePNet_hyps (vars_codeTreeE e side α) (codeTreeE_wires e side α).1 (codeTreeE_wires e side α).2

/-- The root of `[α]` is the `dup` cell of `T_{1,1}` (Fig. 10, page 89), for any numbering `e`. -/
theorem codeTreeE_eq_mkDup
    -- the symbol
    (α : S.Sym) :
    ∃ a b, codeTreeE e side α = mkDup a b :=
  exists_cellSkel_eq_mkDup _ _ _ _ _

/-- The tree of `[α]` is not a wire (page 89), for any numbering `e` of the symbols. -/
theorem codeTreeE_ne_var
    -- the symbol, and a name
    (α : S.Sym)
    (x : ℕ) :
    codeTreeE e side α ≠ var x := by
  obtain ⟨a, b, h⟩ := codeTreeE_eq_mkDup e side α
  rw [h]
  intro h'
  cases h'

/-- **The principal net `[α]` of Fig. 10** (top left, page 89; principal nets, page 80), with the
symbols numbered by `e`: the tree `codeTreeE e side α` with the ports `0, …, k - 1` and its other
names as internal wires, where `k = S.arity α`. -/
def codeNetE
    -- the symbol
    (α : S.Sym) :
    PNet sig (S.arity α) :=
  treePNet (S.arity α) (codeTreeE e side α) (codeTreeE_hyps e side α).1
    (codeTreeE_hyps e side α).2

/-- The principal net `[α]` is the tree of Fig. 10 (page 89), for any numbering `e` of the symbols:
its instance with the port `i` named `i` and the internal wires named back is
`codeTreeE e side α`. -/
theorem codeNetE_inst
    -- the symbol
    (α : S.Sym) :
    -- the port `i` named `i`, the wire `w` named by the name of rank `w`: this is the tree
    (codeNetE e side α).inst (fun i => var (i : ℕ))
      (fun w => ((wireNum (S.arity α) (codeTreeE e side α)).symm w).1) = codeTreeE e side α :=
  treePNet_inst _ _ _ _

/-- **`[α]` of Fig. 10 is strict** (definition page 80, Fig. 10 page 89), for any numbering `e`. -/
theorem codeNetE_strict
    -- the symbol
    (α : S.Sym) :
    (codeNetE e side α).Strict :=
  treePNet_strict _ _ _ _ (codeTreeE_ne_var e side α)

/-- **The translation of Fig. 10** (pages 89–90), with the symbols numbered by `e`: every symbol
`α` is translated into the principal net `codeNetE e side α`. -/
def codeTranslationE :
    Translation S sig :=
  ⟨codeNetE e side⟩

end Enum

-- ============================================================================================
-- 3. The tree of `[α]` for the numbering `symEnum S`
-- ============================================================================================

-- finitely many symbols, and the choice `side` of expanded sides
variable [Finite S.Sym] (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

/-- The first name of the menu `Γ` in `[α]`: after the ports `0, …, n - 1`, the loop `n` and the
block of the menu `Γ_α`. -/
noncomputable def codeMenuBase
    -- the symbol
    (α : S.Sym) :
    ℕ :=
  codeMenuBaseE (symEnum S) side α

/-- `codeMenuBase` unfolded. -/
theorem codeMenuBase_eq
    -- the symbol
    (α : S.Sym) :
    codeMenuBase side α = S.arity α + 1 + ∑ j, codeCellSizes side α j :=
  rfl

/-- The first cut name of the code `!Γ` in `[α]`: after the block of the menu `Γ`. -/
noncomputable def codeKey
    -- the symbol
    (α : S.Sym) :
    ℕ :=
  codeKeyE (symEnum S) side α

/-- `codeKey` unfolded. -/
theorem codeKey_eq
    -- the symbol
    (α : S.Sym) :
    codeKey side α = codeMenuBase side α + ∑ i, codeMenuSizes side i :=
  rfl

/-- **The tree of `[α]` of Fig. 10** (top left, page 89): the transpositor `T_{1,1}` carrying the
menu `Γ_α` (names from `n + 1`) and the selector `S^α_m` on the multiplexor `M_{n+2}`, whose leaves
are, from left to right, the code `!Γ` of `Γ = Γ_0 & ⋯ & Γ_{m-1}` (`Γ` named from `codeMenuBase`,
the cut names of the code from `codeKey`), the ports `0, …, n - 1`, and the loop `ℓ = n`. Here
`n = S.arity α`, `m` is the number of symbols, and `side` is any choice of expanded sides (page 90:
no order on the symbols is needed). It is `codeTreeE` with the symbols numbered by `symEnum`. -/
noncomputable def codeTree
    -- the symbol
    (α : S.Sym) :
    Term sig ℕ :=
  codeTreeE (symEnum S) side α

/-- `codeTree` unfolded: the tree of Fig. 10 (page 89). -/
theorem codeTree_eq
    -- the symbol
    (α : S.Sym) :
    -- the transpositor with the menu `Γ_α` and the selector of `α`, on the leaves
    codeTree side α =
      cellSkel (menu (codeCellMenu side α (S.arity α + 1))) (Nat.card S.Sym) (symEnum S α)
        -- the code `!Γ`, then the ports, then the loop
        (code (codeKey side α) (menu (codeMenus side (codeMenuBase side α))) ::
          List.ofFn fun j : Fin (S.arity α) => var (j : ℕ)) (S.arity α) :=
  rfl

/-- **The names of `[α]` of Fig. 10** (page 89): the ports `0, …, n - 1` once, and twice each the
names of `[n, codeKey)` (the loop, the names of `Γ_α` and those of `Γ`) and the cut names of the
code `!Γ`. -/
theorem vars_codeTree
    -- the symbol
    (α : S.Sym) :
    -- the ports once
    (codeTree side α).vars = Multiset.Ico 0 (S.arity α) +
      -- and twice: the loop, the names of the menus, and the cut names of the code
      2 • (Multiset.Ico (S.arity α) (codeKey side α) +
        (decomp (codeKey side α) (menu (codeMenus side (codeMenuBase side α)))).ports) :=
  vars_codeTreeE (symEnum S) side α

/-- The names of `[α]` other than the ports are distinct and above the ports (page 89). -/
theorem codeTree_wires
    -- the symbol
    (α : S.Sym) :
    -- the loop, the names of the menus and the cut names of the code are distinct
    (Multiset.Ico (S.arity α) (codeKey side α) +
        (decomp (codeKey side α) (menu (codeMenus side (codeMenuBase side α)))).ports).Nodup ∧
      -- and none of them is a port
      ∀ x ∈ Multiset.Ico (S.arity α) (codeKey side α) +
        (decomp (codeKey side α) (menu (codeMenus side (codeMenuBase side α)))).ports,
        S.arity α ≤ x :=
  codeTreeE_wires (symEnum S) side α

/-- The tree of `[α]` has the ports `0, …, n - 1` once and every other name twice (page 89). -/
theorem codeTree_hyps
    -- the symbol
    (α : S.Sym) :
    -- each port occurs once
    (∀ i < S.arity α, (codeTree side α).vars.count i = 1) ∧
      -- and every other name of the tree twice
      (∀ x ∈ (codeTree side α).vars, S.arity α ≤ x → (codeTree side α).vars.count x = 2) :=
  codeTreeE_hyps (symEnum S) side α

/-- The root of `[α]` is the `dup` cell of `T_{1,1}` (Fig. 10, page 89). -/
theorem codeTree_eq_mkDup
    -- the symbol
    (α : S.Sym) :
    ∃ a b, codeTree side α = mkDup a b :=
  codeTreeE_eq_mkDup (symEnum S) side α

/-- The tree of `[α]` is not a wire (page 89). -/
theorem codeTree_ne_var
    -- the symbol, and a name
    (α : S.Sym)
    (x : ℕ) :
    codeTree side α ≠ var x :=
  codeTreeE_ne_var (symEnum S) side α x

-- ============================================================================================
-- 4. Main result: the principal net `[α]` and the translation are strict
-- ============================================================================================

/-- **The principal net `[α]` of Fig. 10** (top left, page 89; principal nets, page 80): the tree
`codeTree side α` with the ports `0, …, n - 1` and its other names as internal wires. It is
`codeNetE` with the symbols numbered by `symEnum`. -/
noncomputable def codeNet
    -- the symbol
    (α : S.Sym) :
    PNet sig (S.arity α) :=
  codeNetE (symEnum S) side α

/-- `codeNet` unfolded: the tree of Fig. 10 as a principal net (page 89). -/
theorem codeNet_eq
    -- the symbol
    (α : S.Sym) :
    codeNet side α =
      treePNet (S.arity α) (codeTree side α) (codeTree_hyps side α).1 (codeTree_hyps side α).2 :=
  rfl

/-- **The translation of Fig. 10** (pages 89–90): every symbol `α` is translated into the principal
net `[α]`, built from the choice `side` of expanded sides. -/
noncomputable def codeTranslation :
    Translation S sig :=
  ⟨codeNet side⟩

/-- `codeTranslation` is `codeTranslationE` with the symbols numbered by `symEnum` (page 90). -/
theorem codeTranslation_eq_E :
    codeTranslation side = codeTranslationE (symEnum S) side :=
  rfl

/-- The principal net `[α]` is the tree of Fig. 10 (page 89): its instance with the port `i` named
`i` and the internal wires named back is `codeTree side α`. -/
theorem codeNet_inst
    -- the symbol
    (α : S.Sym) :
    -- the port `i` named `i`, the wire `w` named by the name of rank `w`: this is the tree
    (codeNet side α).inst (fun i => var (i : ℕ))
      (fun w => ((wireNum (S.arity α) (codeTree side α)).symm w).1) = codeTree side α :=
  codeNetE_inst (symEnum S) side α

/-- **`[α]` of Fig. 10 is strict** (definition page 80, Fig. 10 page 89): its principal port is the
root of `T_{1,1}`, a `dup` cell. -/
theorem codeNet_strict
    -- the symbol
    (α : S.Sym) :
    (codeNet side α).Strict :=
  codeNetE_strict (symEnum S) side α

/-- **The translation of Fig. 10 is strict** (Lafont 1997, definition page 80, Fig. 10 pages
89–90): no `[α]` is a wire. -/
theorem codeTranslation_strict :
    (codeTranslation side).Strict :=
  codeNet_strict side

end INet.Comb
