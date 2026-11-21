/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.General.CodeTr

/-!
# Two cells `[α]`, `[β]` of Fig. 10 plugged by their roots (pages 89–90)

Lafont 1997, Section 2.7, Fig. 10 (journal page 89, PDF page 21) and page 90: "The reader is
invited to complete the proof of Theorem 1 by working out the analogue of Fig. 7". This file does
the first rows of that analogue (Fig. 7, page 86, rows 1–2). The principal nets `[α]` and `[β]` of
Fig. 10, plugged by their roots, are two cells of Fig. 6 whose multiplexors carry the code `!Γ` as
first leaf. The transpositors `T_{1,1}` meet, each selector extracts one package of the other menu:
the selector of `[α]` takes `Γ_{α,β}` from the menu of `[β]` and the selector of `[β]` takes
`Γ_{β,α}` from the menu of `[α]`. Then the multiplexor of `[α]` meets the dual multiplexor of
`Γ_{α,β}`: the code `!Γ` meets the copier `C_p`, the ports of `[α]` meet the trees of `⟨φ_{α,β}⟩`,
and the loop meets the transpositor `T_σ`.

The results are stated first with the symbols numbered by any `e : S.Sym ≃ Fin n` (names ending in
`E`: `codeWiresE`, `inst_codeNetE_fresh`, `getElem_codeCellMenuE`, `codeCells_meetE`, …), then
for `e := symEnum S` under the old names.

Contents, in the order of the file:

1. Renaming the tree of a principal net: `codeRen`, the renaming of the names of a tree (the ports
   to the given names, every other name `x` to `K + x`); `codeRen_injOn`,
   `treePNet_inst_codeRen`.
2. For any numbering `e`, the wires of `[α]` and the menu `Γ_β`: `codeWiresE`,
   `inst_codeNetE_fresh` (the instance of `[α]` whose internal wires are named by `codeWiresE` is
   the tree of `[α]` renamed by `codeRen`), `codeWiresE_injective`, `le_codeWiresE`,
   `codeWiresE_lt`, `length_codeCellMenuE`, `getElem_codeCellMenuE` (the entry of the menu `Γ_β`
   at the number of `α` is `Γ_{α,β}`), `codeCellMenuE_isPackage`, `le_of_mem_codeCellMenuE`.
3. For any numbering `e`, the two cells meet: `codeTreeE_bind_codeRen`,
   `codeCellMenuE_bind_isPackage`, `codeCells_meetE` (Fig. 7, rows 1–2, for Fig. 10).
4. The same for the numbering `symEnum S`: `codeWires`, `inst_codeNet_fresh`,
   `codeWires_injective`, `le_codeWires`, `codeWires_lt`, `length_codeCellMenu`,
   `getElem_codeCellMenu`, `codeCellMenu_isPackage`, `le_of_mem_codeCellMenu`,
   `codeTree_bind_codeRen`, `codeCellMenu_bind_isPackage`.
5. Main result: `codeCells_meet`, the two cells meet (Fig. 7, rows 1–2, for Fig. 10).
6. Main result: `codeCells_meet_gamma`, the multiplexor of `[α]` against `Γ_{α,β}` (Fig. 7, row 3,
   for Fig. 10), with the auxiliary lemmas `zipWith_ofFn_ofFn` and `mux_muxStar_cons_ofFn`.
-/

@[expose] public section

namespace INet.Comb

open Term Translation

-- ============================================================================================
-- 1. Renaming the tree of a principal net
-- ============================================================================================

/-- The renaming of the names of a tree with `n` ports (page 80): the port `x < n` to `xs x`, every
other name `x` to `K + x`. -/
def codeRen
    -- the names on the `n` ports
    {n : ℕ}
    (xs : Fin n → ℕ)
    -- the shift of the other names, and the name renamed
    (K x : ℕ) :
    ℕ :=
  if h : x < n then xs ⟨x, h⟩ else K + x

/-- `codeRen` is injective on the names that are not ports. -/
theorem codeRen_injOn
    -- the renaming
    {n : ℕ}
    (xs : Fin n → ℕ)
    (K : ℕ)
    -- a set of names, none of which is a port
    (X : Set ℕ)
    (hX : ∀ x ∈ X, n ≤ x) :
    Set.InjOn (codeRen xs K) X := by
  intro x hx y hy h
  have h1 := hX x hx
  have h2 := hX y hy
  simp only [codeRen, show ¬ x < n by omega, show ¬ y < n by omega, dite_false] at h
  omega

/-- **The instance of `treePNet` with its wires shifted** (page 80): the instance of the principal
net of a tree `t` with the names `xs` on its ports and the internal wire of name `x` named `K + x`
is `t` renamed by `codeRen xs K`. -/
theorem treePNet_inst_codeRen
    -- the tree: the ports `0, …, n - 1` occur once, every other name twice
    (n : ℕ)
    (t : Term sig ℕ)
    (hp : ∀ i < n, t.vars.count i = 1)
    (hw : ∀ x ∈ t.vars, n ≤ x → t.vars.count x = 2)
    -- the names on the ports, and the shift of the internal wires
    (xs : Fin n → ℕ)
    (K : ℕ) :
    (treePNet n t hp hw).inst (fun i => var (xs i))
        (fun w => K + ((wireNum n t).symm w).1) =
      t.bind fun x => var (codeRen xs K x) := by
  change (t.bind (treeLeaf n t)).bind (Sum.elim (fun i : Fin n => var (xs i))
    fun w : Fin (wireSet n t).card => var (K + ((wireNum n t).symm w).1)) = _
  rw [Term.bind_bind]
  refine Term.bind_congr fun x hx => ?_
  unfold treeLeaf
  by_cases h1 : x < n
  · simp [h1, codeRen]
  · have h2 : x ∈ wireSet n t :=
      Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 hx, not_lt.1 h1⟩
    simp [h1, h2, codeRen]

-- the interaction system
variable {S : Signature}

section Enum

-- the numbering `e` of the `n` symbols, and the choice `side` of expanded sides
variable {n : ℕ} (e : S.Sym ≃ Fin n)
  (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

-- ============================================================================================
-- 2. For any numbering `e`: the wires of `[α]` and the menu `Γ_β`
-- ============================================================================================

/-- The names of the internal wires of `[α]`, shifted by `K` (page 89), for any numbering `e` of the
symbols. -/
def codeWiresE
    -- the symbol, and the shift
    (α : S.Sym)
    (K : ℕ) :
    Fin (codeNetE e side α).internal → ℕ :=
  fun w => K + ((wireNum (S.arity α) (codeTreeE e side α)).symm w).1

/-- **The instance of `[α]` of Fig. 10 with its wires shifted** (page 89): with the names `xs` on
its ports and its internal wires named by `codeWiresE`, `[α]` is its tree renamed by `codeRen`. -/
theorem inst_codeNetE_fresh
    -- the symbol, the names on its ports, and the shift of the internal wires
    (α : S.Sym)
    (xs : Fin (S.arity α) → ℕ)
    (K : ℕ) :
    (codeNetE e side α).inst (fun i => var (xs i)) (codeWiresE e side α K) =
      (codeTreeE e side α).bind fun x => var (codeRen xs K x) :=
  treePNet_inst_codeRen _ _ _ _ xs K

/-- The internal wires named by `codeWiresE` are distinct. -/
theorem codeWiresE_injective
    -- the symbol, and the shift
    (α : S.Sym)
    (K : ℕ) :
    Function.Injective (codeWiresE e side α K) := by
  intro a b h
  have h' : ((wireNum (S.arity α) (codeTreeE e side α)).symm a).1 =
      ((wireNum (S.arity α) (codeTreeE e side α)).symm b).1 := by
    simpa [codeWiresE] using h
  exact (wireNum (S.arity α) (codeTreeE e side α)).symm.injective (Subtype.ext h')

/-- The internal wires named by `codeWiresE` are at least `K`. -/
theorem le_codeWiresE
    -- the symbol, the shift, and an internal wire of `[α]`
    (α : S.Sym)
    (K : ℕ)
    (w : Fin (codeNetE e side α).internal) :
    K ≤ codeWiresE e side α K w :=
  Nat.le_add_right _ _

/-- The internal wires named by `codeWiresE` are below `K` plus a bound of the names of the tree. -/
theorem codeWiresE_lt
    -- the symbol, the shift, and an internal wire of `[α]`
    (α : S.Sym)
    (K : ℕ)
    (w : Fin (codeNetE e side α).internal) :
    codeWiresE e side α K w < K + ((codeTreeE e side α).vars.sup + 1) := by
  have hm := Finset.mem_filter.1 ((wireNum (S.arity α) (codeTreeE e side α)).symm w).2
  have := Multiset.le_sup (Multiset.mem_toFinset.1 hm.1)
  simp only [codeWiresE]
  omega

/-- The menu `Γ_β` of Fig. 10 has one package per symbol (page 89). -/
theorem length_codeCellMenuE
    -- the symbol, and the first name of the menu
    (β : S.Sym)
    (k₀ : ℕ) :
    (codeCellMenuE e side β k₀).length = n :=
  List.length_ofFn

/-- **The entry of `Γ_β` at the number of `α` is `Γ_{α,β}`** (Fig. 10, page 89): the package built
from the side of `α` against `β`, on its block of names. -/
theorem getElem_codeCellMenuE
    -- the two symbols, and the first name of the menu `Γ_β`
    (α β : S.Sym)
    (k₀ : ℕ)
    -- the number of `α` is an index of the menu
    (h : (e α : ℕ) < (codeCellMenuE e side β k₀).length) :
    (codeCellMenuE e side β k₀)[(e α : ℕ)]'h =
      codeGammaOpt n (fun γ => e γ) (side α β)
        (k₀ + off (codeCellSizesE e side β) (e α)) := by
  simp only [codeCellMenuE, List.getElem_ofFn, Fin.eta]
  congr 2 <;> exact e.symm_apply_apply α

/-- The packages of the menu `Γ_β` (page 89): each `Γ_{j,β}` is a package. -/
theorem codeCellMenuE_isPackage
    -- the symbol, and the first name of the menu
    (β : S.Sym)
    (k₀ : ℕ) :
    ∀ π ∈ codeCellMenuE e side β k₀, π.IsPackage := by
  intro π hπ
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hπ
  exact isPackage_of_vars_eq (vars_codeGammaOpt _ _ _ _)

/-- The names of the packages of the menu `Γ_β` are above `k₀`. -/
theorem le_of_mem_codeCellMenuE
    -- the symbol, and the first name of the menu
    (β : S.Sym)
    (k₀ : ℕ) :
    ∀ π ∈ codeCellMenuE e side β k₀, ∀ x ∈ π.vars, k₀ ≤ x := by
  intro π hπ x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hπ
  rw [vars_codeGammaOpt] at hx
  have := (Multiset.mem_Ico.1 (Multiset.mem_of_mem_nsmul hx)).1
  omega

-- ============================================================================================
-- 3. For any numbering `e`: the two cells meet
-- ============================================================================================

/-- The tree of `[α]` renamed by `codeRen` is the cell of Fig. 6 with the renamed menu `Γ_α`, the
renamed code `!Γ`, the ports `xs` and the loop `K + n` (page 89). -/
theorem codeTreeE_bind_codeRen
    -- the symbol, the names on its ports, and the shift of the internal wires
    (α : S.Sym)
    (xs : Fin (S.arity α) → ℕ)
    (K : ℕ) :
    -- the renamed tree of `[α]` is the cell of Fig. 6 with: the renamed menu `Γ_α`,
    (codeTreeE e side α).bind (fun x => var (codeRen xs K x)) =
      cellSkel (menu ((codeCellMenuE e side α (S.arity α + 1)).map
          (·.bind fun x => var (codeRen xs K x))))
        -- the selector of the number of `α` among `n`,
        n (e α)
        -- the leaves of the multiplexor: the renamed code `!Γ` and the ports `xs`,
        ((code (codeKeyE e side α) (menu (codeMenusE e side (codeMenuBaseE e side α)))).bind
            (fun x => var (codeRen xs K x)) ::
          List.ofFn fun j => var (xs j))
        -- and the loop
        (K + S.arity α) := by
  rw [codeTreeE, bind_cellSkel, menu, bind_mux, ← menu, List.map_cons, List.map_ofFn]
  have hn : codeRen xs K (S.arity α) = K + S.arity α := by simp [codeRen]
  rw [hn]
  congr 3
  funext j
  simp [codeRen]

/-- The packages of the renamed menu `Γ_α` of `[α]` are packages (page 89): `codeRen` is
injective above the ports. -/
theorem codeCellMenuE_bind_isPackage
    -- the symbol, the names on its ports, and the shift of the internal wires
    (α : S.Sym)
    (xs : Fin (S.arity α) → ℕ)
    (K : ℕ) :
    ∀ π ∈ (codeCellMenuE e side α (S.arity α + 1)).map (·.bind fun x => var (codeRen xs K x)),
      π.IsPackage := by
  intro π hπ
  obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hπ
  refine IsPackage.bind_var (codeCellMenuE_isPackage e side α _ ρ hρ) _
    (codeRen_injOn xs K _ fun x hx => ?_)
  have := le_of_mem_codeCellMenuE e side α _ ρ hρ x hx
  omega

/-- **Two cells `[α]`, `[β]` of Fig. 10 plugged by their roots meet** (Lafont 1997, Fig. 10,
pages 89–90; the analogue of Fig. 7, rows 1–2, page 86). With the names `xs`, `ys` on their ports,
any names `f`, `g` of their internal wires, in a context `Δ` with the whole net linear, the net
reduces up to wires to two equations: the multiplexor of `[α]`, whose leaves are its code `!Γ`, the
ports `xs` and a loop `ℓ`, against the package `Γ_{α,β}` of the menu of `[β]` (built from the side
of `α` against `β`); and the multiplexor of `[β]`, leaves its code, the ports `ys` and the same
loop `ℓ`, against the package `Γ_{β,α}` of the menu of `[α]`.

The renamings are explicit: the internal wires of `[α]` are first renamed above every name of the
net, by `codeRen xs K` (the name `x` of the tree of `[α]` becomes `K + x`), and those of `[β]`
above again, by `codeRen ys K'`. The loop is `ℓ = K + S.arity α`. The side `side` is any choice of
expanded sides, and the `n` symbols are numbered by any `e : S.Sym ≃ Fin n` (page 90: no order on
the symbols is needed). -/
theorem codeCells_meetE
    -- the two symbols, and the names on the ports of `[α]` and of `[β]`
    (α β : S.Sym)
    (xs : Fin (S.arity α) → ℕ)
    (ys : Fin (S.arity β) → ℕ)
    -- any names of the internal wires of `[α]` and of `[β]`
    (f : Fin (codeNetE e side α).internal → ℕ)
    (g : Fin (codeNetE e side β).internal → ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the net we start from is linear: `[α]` and `[β]` plugged by their roots, and `Δ`
    (hlin : Net.Linear (s((codeNetE e side α).inst (fun i => var (xs i)) f,
      (codeNetE e side β).inst (fun j => var (ys j)) g) ::ₘ Δ)) :
    -- there are shifts `K`, `K'` of the internal wires and a net `M` such that
    ∃ (K K' : ℕ) (M : CNet),
      -- the net reduces, up to wires, to `M`,
      StepsE system (s((codeNetE e side α).inst (fun i => var (xs i)) f,
        (codeNetE e side β).inst (fun j => var (ys j)) g) ::ₘ Δ) M ∧
      -- and `M` is the same graph as: the multiplexor of `[α]` (leaves: its renamed code `!Γ`,
      -- the ports `xs`, the loop `K + S.arity α`) against `Γ_{α,β}`, renamed as in `[β]`;
      Equiv M
        (s(mux ((code (codeKeyE e side α)
                  (menu (codeMenusE e side (codeMenuBaseE e side α)))).bind
                (fun x => var (codeRen xs K x)) ::
              List.ofFn (fun i => (var (xs i) : Term sig ℕ)) ++ [var (K + S.arity α)]),
            (codeGammaOpt n (fun γ => e γ) (side α β)
              (S.arity β + 1 + off (codeCellSizesE e side β) (e α))).bind
                (fun x => var (codeRen ys K' x))) ::ₘ
          -- the multiplexor of `[β]` (leaves: its renamed code, the ports `ys`, the same loop)
          -- against `Γ_{β,α}`, renamed as in `[α]`; and `Δ`
          s(mux ((code (codeKeyE e side β)
                  (menu (codeMenusE e side (codeMenuBaseE e side β)))).bind
                (fun x => var (codeRen ys K' x)) ::
              List.ofFn (fun j => (var (ys j) : Term sig ℕ)) ++ [var (K + S.arity α)]),
            (codeGammaOpt n (fun γ => e γ) (side β α)
              (S.arity α + 1 + off (codeCellSizesE e side α) (e β))).bind
                (fun x => var (codeRen xs K x))) ::ₘ Δ) := by
  set N : CNet := s((codeNetE e side α).inst (fun i => var (xs i)) f,
    (codeNetE e side β).inst (fun j => var (ys j)) g) ::ₘ Δ with hN
  obtain ⟨K, hK⟩ := Net.exists_below N
  -- rename the internal wires of `[α]` above every name of the net
  have E1 : Equiv N (s((codeNetE e side α).inst (fun i => var (xs i)) (codeWiresE e side α K),
      (codeNetE e side β).inst (fun j => var (ys j)) g) ::ₘ Δ) := by
    have L : Net.Linear (s((codeNetE e side β).inst (fun j => var (ys j)) g,
        (codeNetE e side α).inst (fun i => var (xs i)) f)
        ::ₘ Δ) := by
      rw [Sym2.eq_swap]
      exact hlin
    have E := PNet.equiv_inst_fresh (h := codeWiresE e side α K) L (codeWiresE_injective e side α K)
      (fun w hw => by
        have hw' : codeWiresE e side α K w ∈ Net.vars N := by
          rw [hN, Sym2.eq_swap]; exact hw
        have := hK _ hw'
        have := le_codeWiresE e side α K w
        omega)
    rw [Sym2.eq_swap (a := (codeNetE e side β).inst _ g),
      Sym2.eq_swap (a := (codeNetE e side β).inst _ g)] at E
    exact E
  have L1 := E1.linear hlin
  set N1 : CNet := s((codeNetE e side α).inst (fun i => var (xs i)) (codeWiresE e side α K),
      (codeNetE e side β).inst (fun j => var (ys j)) g) ::ₘ Δ with hN1
  obtain ⟨K', hK'⟩ := Net.exists_below N1
  -- rename the internal wires of `[β]` above every name of the new net
  have E2 : Equiv N1 (s((codeNetE e side α).inst (fun i => var (xs i)) (codeWiresE e side α K),
      (codeNetE e side β).inst (fun j => var (ys j)) (codeWiresE e side β K')) ::ₘ Δ) :=
    PNet.equiv_inst_fresh (h := codeWiresE e side β K') L1 (codeWiresE_injective e side β K')
      fun w hw => by
        have := hK' _ hw
        have := le_codeWiresE e side β K' w
        omega
  have hA := inst_codeNetE_fresh e side α xs K
  have hB := inst_codeNetE_fresh e side β ys K'
  rw [codeTreeE_bind_codeRen] at hA hB
  have L2 := E2.linear L1
  rw [hA, hB] at L2
  have hlen : ∀ (γ δ : S.Sym) (k : ℕ) (F : ℕ → ℕ),
      ((codeCellMenuE e side γ k).map (·.bind fun x => var (F x))).length = n := by
    intro γ δ k F; simp [length_codeCellMenuE]
  obtain ⟨M, hS, hE⟩ := cellSkel_cellSkel _ _ n (e α) (e β)
    (hlen α α _ _) (hlen β β _ _) (Fin.isLt _) (Fin.isLt _)
    (codeCellMenuE_bind_isPackage e side α xs K)
    (codeCellMenuE_bind_isPackage e side β ys K') _ _ _ _
    Δ L2
  rw [← hA, ← hB] at hS
  obtain ⟨M', hS', hE'⟩ := stepsE_of_equiv (E1.trans E2) hS
  refine ⟨K, K', M', hS', hE'.trans (hE.trans (Equiv.of_eq ?_))⟩
  simp only [List.getElem_map, getElem_codeCellMenuE, List.cons_append]

end Enum

-- ============================================================================================
-- 4. The same for the numbering `symEnum S`
-- ============================================================================================

-- finitely many symbols, numbered by `symEnum S`, and the choice `side` of expanded sides
variable [Finite S.Sym] (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

/-- The names of the internal wires of `[α]`, shifted by `K` (page 89). -/
noncomputable def codeWires
    -- the symbol, and the shift
    (α : S.Sym)
    (K : ℕ) :
    Fin (codeNet side α).internal → ℕ :=
  codeWiresE (symEnum S) side α K

/-- **The instance of `[α]` of Fig. 10 with its wires shifted** (page 89): with the names `xs` on
its ports and its internal wires named by `codeWires`, `[α]` is its tree renamed by `codeRen`. -/
theorem inst_codeNet_fresh
    -- the symbol, the names on its ports, and the shift of the internal wires
    (α : S.Sym)
    (xs : Fin (S.arity α) → ℕ)
    (K : ℕ) :
    (codeNet side α).inst (fun i => var (xs i)) (codeWires side α K) =
      (codeTree side α).bind fun x => var (codeRen xs K x) :=
  inst_codeNetE_fresh (symEnum S) side α xs K

/-- The internal wires named by `codeWires` are distinct. -/
theorem codeWires_injective
    -- the symbol, and the shift
    (α : S.Sym)
    (K : ℕ) :
    Function.Injective (codeWires side α K) :=
  codeWiresE_injective (symEnum S) side α K

/-- The internal wires named by `codeWires` are at least `K`. -/
theorem le_codeWires
    -- the symbol, the shift, and an internal wire of `[α]`
    (α : S.Sym)
    (K : ℕ)
    (w : Fin (codeNet side α).internal) :
    K ≤ codeWires side α K w :=
  le_codeWiresE (symEnum S) side α K w

/-- The internal wires named by `codeWires` are below `K` plus a bound of the names of the tree. -/
theorem codeWires_lt
    -- the symbol, the shift, and an internal wire of `[α]`
    (α : S.Sym)
    (K : ℕ)
    (w : Fin (codeNet side α).internal) :
    codeWires side α K w < K + ((codeTree side α).vars.sup + 1) :=
  codeWiresE_lt (symEnum S) side α K w

/-- The menu `Γ_β` of Fig. 10 has one package per symbol (page 89). -/
theorem length_codeCellMenu
    -- the symbol, and the first name of the menu
    (β : S.Sym)
    (k₀ : ℕ) :
    (codeCellMenu side β k₀).length = Nat.card S.Sym :=
  length_codeCellMenuE (symEnum S) side β k₀

/-- **The entry of `Γ_β` at the number of `α` is `Γ_{α,β}`** (Fig. 10, page 89): the package built
from the side of `α` against `β`, on its block of names. -/
theorem getElem_codeCellMenu
    -- the two symbols, and the first name of the menu `Γ_β`
    (α β : S.Sym)
    (k₀ : ℕ)
    -- the number of `α` is an index of the menu
    (h : (symEnum S α : ℕ) < (codeCellMenu side β k₀).length) :
    (codeCellMenu side β k₀)[(symEnum S α : ℕ)]'h =
      codeGammaOpt (Nat.card S.Sym) (fun γ => symEnum S γ) (side α β)
        (k₀ + off (codeCellSizes side β) (symEnum S α)) :=
  getElem_codeCellMenuE (symEnum S) side α β k₀ h

/-- The packages of the menu `Γ_β` (page 89): each `Γ_{j,β}` is a package. -/
theorem codeCellMenu_isPackage
    -- the symbol, and the first name of the menu
    (β : S.Sym)
    (k₀ : ℕ) :
    ∀ π ∈ codeCellMenu side β k₀, π.IsPackage :=
  codeCellMenuE_isPackage (symEnum S) side β k₀

/-- The names of the packages of the menu `Γ_β` are above `k₀`. -/
theorem le_of_mem_codeCellMenu
    -- the symbol, and the first name of the menu
    (β : S.Sym)
    (k₀ : ℕ) :
    ∀ π ∈ codeCellMenu side β k₀, ∀ x ∈ π.vars, k₀ ≤ x :=
  le_of_mem_codeCellMenuE (symEnum S) side β k₀

/-- The tree of `[α]` renamed by `codeRen` is the cell of Fig. 6 with the renamed menu `Γ_α`, the
renamed code `!Γ`, the ports `xs` and the loop `K + n` (page 89). -/
theorem codeTree_bind_codeRen
    -- the symbol, the names on its ports, and the shift of the internal wires
    (α : S.Sym)
    (xs : Fin (S.arity α) → ℕ)
    (K : ℕ) :
    -- the renamed tree of `[α]` is the cell of Fig. 6 with: the renamed menu `Γ_α`,
    (codeTree side α).bind (fun x => var (codeRen xs K x)) =
      cellSkel (menu ((codeCellMenu side α (S.arity α + 1)).map
          (·.bind fun x => var (codeRen xs K x))))
        -- the selector of the number of `α` among the symbols,
        (Nat.card S.Sym) (symEnum S α)
        -- the leaves of the multiplexor: the renamed code `!Γ` and the ports `xs`,
        ((code (codeKey side α) (menu (codeMenus side (codeMenuBase side α)))).bind
            (fun x => var (codeRen xs K x)) ::
          List.ofFn fun j => var (xs j))
        -- and the loop
        (K + S.arity α) :=
  codeTreeE_bind_codeRen (symEnum S) side α xs K

/-- The packages of the renamed menu `Γ_α` of `[α]` are packages (page 89): `codeRen` is
injective above the ports. -/
theorem codeCellMenu_bind_isPackage
    -- the symbol, the names on its ports, and the shift of the internal wires
    (α : S.Sym)
    (xs : Fin (S.arity α) → ℕ)
    (K : ℕ) :
    ∀ π ∈ (codeCellMenu side α (S.arity α + 1)).map (·.bind fun x => var (codeRen xs K x)),
      π.IsPackage :=
  codeCellMenuE_bind_isPackage (symEnum S) side α xs K

-- ============================================================================================
-- 5. Main result: the two cells meet
-- ============================================================================================

/-- **Two cells `[α]`, `[β]` of Fig. 10 plugged by their roots meet** (Lafont 1997, Fig. 10,
pages 89–90; the analogue of Fig. 7, rows 1–2, page 86). With the names `xs`, `ys` on their ports,
any names `f`, `g` of their internal wires, in a context `Δ` with the whole net linear, the net
reduces up to wires to two equations: the multiplexor of `[α]`, whose leaves are its code `!Γ`, the
ports `xs` and a loop `ℓ`, against the package `Γ_{α,β}` of the menu of `[β]` (built from the side
of `α` against `β`); and the multiplexor of `[β]`, leaves its code, the ports `ys` and the same
loop `ℓ`, against the package `Γ_{β,α}` of the menu of `[α]`.

The renamings are explicit: the internal wires of `[α]` are first renamed above every name of the
net, by `codeRen xs K` (the name `x` of the tree of `[α]` becomes `K + x`), and those of `[β]`
above again, by `codeRen ys K'`. The loop is `ℓ = K + n` with `n` the arity of `α`. The side
`side` is any choice of expanded sides. -/
theorem codeCells_meet
    -- the two symbols, and the names on the ports of `[α]` and of `[β]`
    (α β : S.Sym)
    (xs : Fin (S.arity α) → ℕ)
    (ys : Fin (S.arity β) → ℕ)
    -- any names of the internal wires of `[α]` and of `[β]`
    (f : Fin (codeNet side α).internal → ℕ)
    (g : Fin (codeNet side β).internal → ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the net we start from is linear: `[α]` and `[β]` plugged by their roots, and `Δ`
    (hlin : Net.Linear (s((codeNet side α).inst (fun i => var (xs i)) f,
      (codeNet side β).inst (fun j => var (ys j)) g) ::ₘ Δ)) :
    -- there are shifts `K`, `K'` of the internal wires and a net `M` such that
    ∃ (K K' : ℕ) (M : CNet),
      -- the net reduces, up to wires, to `M`,
      StepsE system (s((codeNet side α).inst (fun i => var (xs i)) f,
        (codeNet side β).inst (fun j => var (ys j)) g) ::ₘ Δ) M ∧
      -- and `M` is the same graph as: the multiplexor of `[α]` (leaves: its renamed code `!Γ`,
      -- the ports `xs`, the loop `K + S.arity α`) against `Γ_{α,β}`, renamed as in `[β]`;
      Equiv M
        (s(mux ((code (codeKey side α) (menu (codeMenus side (codeMenuBase side α)))).bind
                (fun x => var (codeRen xs K x)) ::
              List.ofFn (fun i => (var (xs i) : Term sig ℕ)) ++ [var (K + S.arity α)]),
            (codeGammaOpt (Nat.card S.Sym) (fun γ => symEnum S γ) (side α β)
              (S.arity β + 1 + off (codeCellSizes side β) (symEnum S α))).bind
                (fun x => var (codeRen ys K' x))) ::ₘ
          -- the multiplexor of `[β]` (leaves: its renamed code, the ports `ys`, the same loop)
          -- against `Γ_{β,α}`, renamed as in `[α]`; and `Δ`
          s(mux ((code (codeKey side β) (menu (codeMenus side (codeMenuBase side β)))).bind
                (fun x => var (codeRen ys K' x)) ::
              List.ofFn (fun j => (var (ys j) : Term sig ℕ)) ++ [var (K + S.arity α)]),
            (codeGammaOpt (Nat.card S.Sym) (fun γ => symEnum S γ) (side β α)
              (S.arity α + 1 + off (codeCellSizes side α) (symEnum S β))).bind
                (fun x => var (codeRen xs K x))) ::ₘ Δ) :=
  codeCells_meetE (symEnum S) side α β xs ys f g Δ hlin

-- ============================================================================================
-- 6. Main result: the multiplexor of `[α]` against `Γ_{α,β}`
-- ============================================================================================

/-- Pairing two lists of trees given by functions on `Fin n`. -/
theorem zipWith_ofFn_ofFn
    -- the two lists of `n` trees
    {n : ℕ}
    (ps qs : Fin n → Term sig ℕ) :
    List.zipWith (fun t u => s(t, u)) (List.ofFn ps) (List.ofFn qs) =
      List.ofFn fun i => s(ps i, qs i) := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp

/-- **`M_{n+2}` against `M*_{n+2}`, first leaf, `n` middle leaves and last leaf** (page 82): the
multiplexor with leaves `c`, `ps`, `t` against the dual multiplexor with leaves `C`, `qs`, `T`
joins `c` to `C`, each `ps i` to `qs i`, and `t` to `T`, in any context `Δ`. -/
theorem mux_muxStar_cons_ofFn
    -- the first and last leaves of the multiplexor (`c`, `t`) and of the dual one (`C`, `T`)
    {n : ℕ}
    (c C t T : Term sig ℕ)
    -- the `n` middle leaves of the multiplexor and of the dual one
    (ps qs : Fin n → Term sig ℕ)
    -- the rest of the net
    (Δ : CNet) :
    -- the multiplexor against the dual multiplexor reduces to
    Red (s(mux (c :: List.ofFn ps ++ [t]), muxStar (C :: List.ofFn qs ++ [T])) ::ₘ Δ)
      -- `c` against `C`, `t` against `T`, each `ps i` against `qs i`, and `Δ`
      (s(c, C) ::ₘ s(t, T) ::ₘ ((↑(List.ofFn fun i => s(ps i, qs i)) : CNet) + Δ)) := by
  refine (mux_muxStar _ _ Δ (by simp)).cast rfl ?_
  rw [List.cons_append, List.cons_append, List.zipWith_cons_cons,
    List.zipWith_append (by simp), zipWith_ofFn_ofFn]
  simp only [List.zipWith_cons_cons, List.zipWith_nil_right, ← Multiset.cons_coe,
    ← Multiset.coe_add, Multiset.cons_add]
  rw [Multiset.coe_nil, Multiset.add_cons, add_zero, Multiset.cons_add]

-- the interaction system, and the arity `a` and number `k` of middle ports of a side
variable {S : Signature} {a k : ℕ}

/-- **The multiplexor of `[α]` against `Γ_{α,β}`** (Fig. 10, page 89; the analogue of Fig. 7,
row 3, page 86). The multiplexor `M_{n+2}` of `[α]`, with leaves the code `c`, the ports `xs` and
the loop `ℓ`, against the package `Γ_{α,β}` of a side `φ` (renamed by any `ρ`), in any context
`Δ`, reduces by `mux_muxStar` to the code `c` against the copier `C_p` on the extra ports of the
cells of `⟨φ⟩`, each port `xs i` against the tree of `⟨φ⟩` at the port `i` of `α`, and the loop `ℓ`
against the transpositor `T_σ` on the trees of `⟨φ⟩` at the middle ports. -/
theorem codeCells_meet_gamma
    -- the number `m` of symbols, and their numbering `idx`
    (m : ℕ)
    (idx : S.Sym → ℕ)
    -- the side `φ`, and the involution `σ` of its middle ports
    (φ : Rule S a k)
    (σ : Equiv.Perm (Fin k))
    (hσ : Function.Involutive σ)
    -- the first name `k₀` of the package `Γ_{α,β}`, and its renaming `ρ`
    (k₀ : ℕ)
    (ρ : ℕ → ℕ)
    -- the leaves of the multiplexor: the code `c`, the ports `xs` and the loop `ℓ`
    (c : Term sig ℕ)
    (xs : Fin a → ℕ)
    (ℓ : ℕ)
    -- the rest of the net
    (Δ : CNet) :
    -- the multiplexor against the renamed package `Γ_{α,β}` reduces to
    Red (s(mux (c :: List.ofFn (fun i => (var (xs i) : Term sig ℕ)) ++ [var ℓ]),
        (codeGamma m idx φ σ hσ k₀).bind fun x => var (ρ x)) ::ₘ Δ)
      -- the code `c` against the copier `C_p` on the extra ports of the cells of `⟨φ⟩`,
      (s(c, (copier (codeGammaExtras m idx φ k₀)).bind fun x => var (ρ x)) ::ₘ
        -- the loop `ℓ` against the transpositor `T_σ` on the trees of `⟨φ⟩` at the middle ports,
        s(var ℓ, transpositorPerm σ hσ fun j => (codePort m idx φ k₀ (.inr j)).bind
          fun x => var (ρ x)) ::ₘ
        -- each port `xs i` against the tree of `⟨φ⟩` at the port `i` of `α`, and `Δ`
        ((↑(List.ofFn fun i => s(var (xs i), (codePort m idx φ k₀ (.inl i)).bind
          fun x => var (ρ x))) : CNet) + Δ)) := by
  rw [codeGamma, bind_muxStar, List.map_cons, List.map_append, List.map_ofFn, List.map_cons,
    List.map_nil, bind_transpositorPerm]
  exact mux_muxStar_cons_ofFn _ _ _ _ _ _ Δ

end INet.Comb
