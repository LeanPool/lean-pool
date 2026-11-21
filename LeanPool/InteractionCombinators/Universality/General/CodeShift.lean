/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.General.CodeTr

/-!
# Renaming the pieces of Fig. 10, and the cell `[β]` it extracts (pages 89–90)

Lafont 1997, Fig. 10 (journal page 89, PDF page 21) and the text of page 90.

The extraction of page 90 (`codeCell_code_codeMenus`) leaves, at a cell `⟨β⟩`, the tree of `[β]`
with a copy of the menu `Γ_β` and a copy of `!Γ`, renamed by some functions `g` and `g'`. The copy
of `!Γ` comes from another cell, whose names start elsewhere. This file shows that the result is an
instance of the principal net `[β]` of `codeTranslation` (`CodeTr.lean`), so that the
translation relation `TermTr` holds.

The versions with `E` number the symbols by any `e : S.Sym ≃ Fin n`; the versions without `E`
take `e := symEnum S`.

Contents, in the order of the file:

1. Auxiliary lemmas: shifting the pieces of Fig. 10. `bind_codeExtra`, `codeTerm_shift`,
   `codeExtras_shift`, `codeGamma_shift`, `codeGammaOpt_shift`: the pieces numbered from `k₀`
   are those numbered from `k₀'`, renamed by any `g` with `g (k₀ + i) = k₀' + i`.
2. Auxiliary lemmas for any numbering: shifting the menus. `menu_codeCellMenuE_shift`,
   `menu_codeMenusE_shift`.
3. Auxiliary lemmas: instances of a tree. `treePNet_inst_bind` (an instance of `treePNet` is the
   tree with the ports plugged and the other names renamed), `bind_cellSkel_of`.
4. Main result for any numbering: `codeNetE_inst_eq`, the tree left by the extraction is an
   instance of `[β]`.
5. Main results for the enumeration `symEnum S`: `menu_codeCellMenu_shift`,
   `menu_codeMenus_shift`, and `codeNet_inst_eq`, the tree left by the extraction is an instance
   of `[β]`.
-/

@[expose] public section

namespace INet.Comb

open Term Translation

-- the interaction system, an arity and a number of auxiliary ports
variable {S : Signature} {a k : ℕ}

-- ============================================================================================
-- 1. Auxiliary lemmas: shifting the pieces of Fig. 10
-- ============================================================================================

/-- Renaming goes through the tree on the extra port of `⟨α_i⟩` (page 89). -/
theorem bind_codeExtra
    -- the renaming
    (g : ℕ → ℕ)
    -- the data of the tree: the number of symbols, the symbol, the names, the first cut name
    (m i y u k₀ : ℕ)
    -- `g` sends `k₀ + 1` to the successor of the image of `k₀`
    (hg : g (k₀ + 1) = g k₀ + 1) :
    (codeExtra m i y u k₀).bind (fun x => var (g x))
      = codeExtra m i (g y) (g u) (g k₀) := by
  simp [codeExtra, copier, bind_autoMux, bind_muxStar, selector_eq_cellSel, bind_cellSel, hg]

-- the number of symbols, and the numbering of the symbols
variable (m : ℕ) (idx : S.Sym → ℕ)

/-- **Shifting `⟨t⟩`** (Fig. 10, page 89): renaming `⟨t⟩`, numbered from `b`, by a `g` that sends
`b + i` to `b' + i` gives `⟨t⟩` of the renamed tree, numbered from `b'`. -/
theorem codeTerm_shift
    -- the renaming
    (g : ℕ → ℕ)
    -- the tree
    (t : Term S ℕ) :
    -- for any first names `b` and `b'`, if `g` sends `b + i` to `b' + i`,
    ∀ (b b' : ℕ), (∀ i, g (b + i) = b' + i) →
      -- then the renamed `⟨t⟩` is `⟨t⟩` of the renamed tree, numbered from `b'`
      (codeTerm m idx b t).bind (fun x => var (g x))
        = codeTerm m idx b' (t.bind fun x => var (g x)) := by
  induction t with
  | var x => intro b b' _; rfl
  | app α ts ih =>
    intro b b' hg
    have h0 : g b = b' := by simpa using hg 0
    rw [codeTerm, bind_cellSkel, bind_app, codeTerm]
    simp only [bind_var, List.map_cons, List.map_ofFn, Function.comp_def, codeSize_bind_var, h0,
      hg 1, hg 2]
    congr 2
    exact List.ofFn_inj.2 (funext fun i =>
      ih i _ _ fun j => by rw [add_assoc, add_assoc, hg, add_assoc, add_assoc])

/-- **Shifting the trees on the extra ports of `⟨t⟩`** (Fig. 10, page 89). -/
theorem codeExtras_shift
    -- the renaming
    (g : ℕ → ℕ)
    -- the tree
    (t : Term S ℕ) :
    -- for any first names `b` and `b'`, if `g` sends `b + i` to `b' + i`,
    ∀ (b b' : ℕ), (∀ i, g (b + i) = b' + i) →
      -- then the renamed extra trees are those of the renamed tree, numbered from `b'`
      (codeExtras m idx b t).map (·.bind fun x => var (g x))
        = codeExtras m idx b' (t.bind fun x => var (g x)) := by
  induction t with
  | var x => intro b b' _; rfl
  | app α ts ih =>
    intro b b' hg
    rw [codeExtras, bind_app, codeExtras, List.map_cons, bind_codeExtra _ _ _ _ _ _
      (by rw [hg 3, show b + 3 + 1 = b + 4 by omega, hg 4]), hg 1, hg 2, hg 3, List.map_flatten,
      List.map_ofFn]
    simp only [Function.comp_def, codeSize_bind_var]
    congr 2
    exact List.ofFn_inj.2 (funext fun i =>
      ih i _ _ fun j => by rw [add_assoc, add_assoc, hg, add_assoc, add_assoc])

/-- **Shifting `Γ_{i,j}`** (Fig. 10, page 89): the package numbered from `k₀`, renamed by a `g`
that sends `k₀ + i` to `k₀' + i`, is the package numbered from `k₀'`. -/
theorem codeGamma_shift
    -- the rule, and the involution of its auxiliary ports
    (φ : Rule S a k)
    (σ : Equiv.Perm (Fin k))
    (hσ : Function.Involutive σ)
    -- the renaming, which sends `k₀ + i` to `k₀' + i`
    (g : ℕ → ℕ)
    (k₀ k₀' : ℕ)
    (hg : ∀ i, g (k₀ + i) = k₀' + i) :
    (codeGamma m idx φ σ hσ k₀).bind (fun x => var (g x))
      = codeGamma m idx φ σ hσ k₀' := by
  have hb : ∀ p i, g (codeBase φ k₀ p + i) = codeBase φ k₀' p + i := fun p i => by
    simp only [codeBase, add_assoc]; exact hg _
  have hp : ∀ p, (codePort m idx φ k₀ p).bind (fun x => var (g x)) = codePort m idx φ k₀' p :=
    fun p => by
      rw [codePort, codeTerm_shift m idx g _ _ _ (hb p), gammaTree_shift φ g k₀ k₀' hg]; rfl
  have hx : ∀ p, (codePortExtras m idx φ k₀ p).map (·.bind fun x => var (g x)) =
      codePortExtras m idx φ k₀' p := fun p => by
    rw [codePortExtras, codeExtras_shift m idx g _ _ _ (hb p), gammaTree_shift φ g k₀ k₀' hg]; rfl
  rw [codeGamma, bind_muxStar, List.map_cons, copier, bind_autoMux, codeGammaExtras,
    List.map_flatten, List.map_ofFn, List.map_append, List.map_ofFn, List.map_cons, List.map_nil,
    bind_transpositorPerm]
  simp only [Function.comp_def, hp, hx]
  rfl

/-- Shifting `codeGammaOpt` (page 89). -/
theorem codeGammaOpt_shift
    -- the expanded side, if any
    (o : Option (ExpSide S a))
    -- the renaming, which sends `k₀ + i` to `k₀' + i`
    (g : ℕ → ℕ)
    (k₀ k₀' : ℕ)
    (hg : ∀ i, g (k₀ + i) = k₀' + i) :
    (codeGammaOpt m idx o k₀).bind (fun x => var (g x))
      = codeGammaOpt m idx o k₀' := by
  cases o with
  | none => simp [codeGammaOpt]
  | some s => exact codeGamma_shift m idx s.φ s.σ s.involutive g k₀ k₀' hg

section Enum

-- the numbering `e` of the `n` symbols, and the expanded sides of the rules
variable {n : ℕ} (e : S.Sym ≃ Fin n)
  (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

-- ============================================================================================
-- 2. Auxiliary lemmas for any numbering: shifting the menus
-- ============================================================================================

/-- **Shifting the menu `Γ_β`** (Fig. 10, page 89), with the symbols numbered by any `e`: the menu
numbered from `k₀`, renamed by a `g` that sends `k₀ + i` to `k₀' + i`, is the menu numbered from
`k₀'`. -/
theorem menu_codeCellMenuE_shift
    -- the symbol
    (β : S.Sym)
    -- the renaming, which sends `k₀ + i` to `k₀' + i`
    (g : ℕ → ℕ)
    (k₀ k₀' : ℕ)
    (hg : ∀ i, g (k₀ + i) = k₀' + i) :
    (menu (codeCellMenuE e side β k₀)).bind (fun x => var (g x))
      = menu (codeCellMenuE e side β k₀') := by
  rw [menu, bind_mux, codeCellMenuE, codeCellMenuE, List.map_ofFn, menu]
  congr 2
  funext j
  exact codeGammaOpt_shift _ _ _ g _ _ fun i => by rw [add_assoc, hg, add_assoc]

/-- **Shifting the menu `Γ = Γ_0 & ⋯ & Γ_{m-1}`** (Fig. 10, page 89), with the symbols numbered by
any `e`. -/
theorem menu_codeMenusE_shift
    -- the renaming, which sends `k₀ + i` to `k₀' + i`
    (g : ℕ → ℕ)
    (k₀ k₀' : ℕ)
    (hg : ∀ i, g (k₀ + i) = k₀' + i) :
    (menu (codeMenusE e side k₀)).bind (fun x => var (g x))
      = menu (codeMenusE e side k₀') := by
  rw [menu, bind_mux, codeMenusE, codeMenusE, List.map_ofFn, menu]
  congr 2
  funext i
  exact menu_codeCellMenuE_shift e side _ g _ _ fun j => by rw [add_assoc, hg, add_assoc]

end Enum

-- ============================================================================================
-- 3. Auxiliary lemmas: instances of a tree
-- ============================================================================================

/-- **An instance of `treePNet`** (page 80): with the tree `args i` on the port `i` and the internal
wire of name `x` named `h x`, the instance is `t` with each port `i < n` replaced by `args i` and
every other name `x` by `h x`. -/
theorem treePNet_inst_bind
    -- the tree: the ports `i < n` occur once, the other names twice
    (n : ℕ)
    (t : Term sig ℕ)
    (hp : ∀ i < n, t.vars.count i = 1)
    (hw : ∀ x ∈ t.vars, n ≤ x → t.vars.count x = 2)
    -- the trees on the ports, and the names of the internal wires
    (args : Fin n → Term sig ℕ)
    (h : ℕ → ℕ) :
    (treePNet n t hp hw).inst args (fun w => h ((wireNum n t).symm w).1)
      = t.bind fun x => if hx : x < n then args ⟨x, hx⟩ else var (h x) := by
  change (t.bind (treeLeaf n t)).bind (Sum.elim args
    fun w : Fin (wireSet n t).card => var (h ((wireNum n t).symm w).1)) = _
  rw [Term.bind_bind]
  refine Term.bind_congr fun x hx => ?_
  unfold treeLeaf
  by_cases h1 : x < n
  · simp [h1]
  · have h2 : x ∈ wireSet n t :=
      Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 hx, not_lt.1 h1⟩
    simp [h1, h2]

/-- Plugging trees into the names of the cell `[αᵢ]` of Fig. 6 (page 86), when the loop is renamed
to a name. -/
theorem bind_cellSkel_of
    -- the trees plugged into the names
    (f : ℕ → Term sig ℕ)
    -- the cell: the menu, the number of symbols, the symbol, the trees on the ports
    (Γ : Term sig ℕ)
    (m i : ℕ)
    (ts : List (Term sig ℕ))
    -- the loop `ℓ`, sent by `f` to the name `ℓ'`
    (ℓ ℓ' : ℕ)
    (hℓ : f ℓ = var ℓ') :
    (cellSkel Γ m i ts ℓ).bind f
      = cellSkel (Γ.bind f) m i (ts.map (·.bind f)) ℓ' := by
  simp [cellSkel, bind_transpositor, bind_cellSel, bind_mux, hℓ]

section Enum

-- the numbering `e` of the `n` symbols, and the expanded sides of the rules
variable {n : ℕ} (e : S.Sym ≃ Fin n)
  (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

-- ============================================================================================
-- 4. Main result for any numbering: the extracted tree is an instance of `[β]`
-- ============================================================================================

/-- **The extracted tree is an instance of `[β]`** (Fig. 10, pages 89–90), with the `n` symbols
numbered by any `e : S.Sym ≃ Fin n`. The tree of `[β]` with a copy of the menu `Γ_β` (numbered from
any `B`, renamed by `g`), a copy of the code `!Γ` of `Γ = codeMenusE e side k₀` (cut names from `K`,
renamed by `g'`), the trees `args` on the ports and the loop `ℓ` is the principal net
`codeNetE e side β` with `args` on its ports and its internal wires named by some `F`. -/
theorem codeNetE_inst_eq
    -- the symbol of the cell
    (β : S.Sym)
    -- the first names: of the copy of `Γ_β`, of `Γ`, and the first cut name of `!Γ`
    (B k₀ K : ℕ)
    -- the renamings of the copy of `Γ_β` and of the copy of `!Γ`
    (g g' : ℕ → ℕ)
    -- the loop
    (ℓ : ℕ)
    -- the trees on the ports
    (args : Fin (S.arity β) → Term sig ℕ) :
    -- some naming `F` of the internal wires makes the instance of `[β]` with `args` on its ports
    ∃ F, (codeNetE e side β).inst args F
      -- equal to the cell `[β]` with the renamed `Γ_β`, the renamed `!Γ`, `args` and the loop
      = cellSkel ((menu (codeCellMenuE e side β B)).bind fun x => var (g x)) n
          (e β) (((code K (menu (codeMenusE e side k₀))).bind fun x => var (g' x)) ::
            List.ofFn args) ℓ := by
  set MB := codeMenuBaseE e side β
  set KB := codeKeyE e side β
  -- the shift of the menu `Γ_β` from `S.arity β + 1` to `B`, and that of `Γ` from `MB` to `k₀`
  set s₁ : ℕ → ℕ := fun x => B + (x - (S.arity β + 1))
  set s₂ : ℕ → ℕ := fun x => k₀ + (x - MB)
  set ρ : ℕ → ℕ := fun x => if x < KB then s₂ x else K + (x - KB)
  set h : ℕ → ℕ := fun x => if x = S.arity β then ℓ else if x < MB then g (s₁ x) else g' (ρ x)
  refine ⟨fun w => h ((wireNum (S.arity β) (codeTreeE e side β)).symm w).1, ?_⟩
  have hMB : S.arity β + 1 ≤ MB := Nat.le_add_right _ _
  have hKB : MB ≤ KB := Nat.le_add_right _ _
  have hΓv : ∀ x ∈ (menu (codeCellMenuE e side β (S.arity β + 1))).vars,
      S.arity β + 1 ≤ x ∧ x < MB := fun x hx => by
    rw [vars_menu_codeCellMenuE, Multiset.mem_nsmul_of_ne_zero (by omega), Multiset.mem_Ico] at hx
    exact hx
  have hGv : ∀ x ∈ (menu (codeMenusE e side MB)).vars, MB ≤ x ∧ x < KB := fun x hx => by
    rw [vars_menu_codeMenusE, Multiset.mem_nsmul_of_ne_zero (by omega), Multiset.mem_Ico] at hx
    exact hx
  have hCv : ∀ x ∈ (code KB (menu (codeMenusE e side MB))).vars, MB ≤ x := fun x hx => by
    rw [vars_code] at hx
    rcases Multiset.mem_add.1 hx with hx | hx
    · rcases Multiset.mem_add.1 hx with hx | hx
      · exact (hGv x hx).1
      · exact hKB.trans ((decomp_ports _ KB).2.1 x hx).1
    · exact hKB.trans ((decomp_ports _ KB).2.1 x hx).1
  -- the menu `Γ_β`
  have eΓ : (menu (codeCellMenuE e side β (S.arity β + 1))).bind (fun x => var (h x)) =
      (menu (codeCellMenuE e side β B)).bind fun x => var (g x) := by
    rw [← menu_codeCellMenuE_shift e side β s₁ (S.arity β + 1) B (fun i => by simp [s₁]),
      Term.bind_bind]
    refine Term.bind_congr fun x hx => ?_
    obtain ⟨h1, h2⟩ := hΓv x hx
    simp [h, show x ≠ S.arity β by omega, h2]
  -- the code `!Γ`
  have eC : (code KB (menu (codeMenusE e side MB))).bind (fun x => var (h x)) =
      (code K (menu (codeMenusE e side k₀))).bind fun x => var (g' x) := by
    have eρ : (menu (codeMenusE e side MB)).bind (fun x => var (s₂ x)) =
        (menu (codeMenusE e side MB)).bind (fun x => var (ρ x)) :=
      Term.bind_congr fun x hx => by simp [ρ, (hGv x hx).2]
    rw [← menu_codeMenusE_shift e side s₂ MB k₀ (fun i => by simp [s₂]), eρ,
      code_bind_var _ ρ KB K (fun i => by simp [ρ]), Term.bind_bind]
    refine Term.bind_congr fun x hx => ?_
    have := hCv x hx
    simp [h, show x ≠ S.arity β by omega, show ¬ x < MB by omega]
  refine (treePNet_inst_bind _ (codeTreeE e side β) _ _ args h).trans ?_
  rw [codeTreeE, bind_cellSkel_of _ _ _ _ _ _ ℓ (by simp [h])]
  have hΓ : (menu (codeCellMenuE e side β (S.arity β + 1))).bind
      (fun x => if hx : x < S.arity β then args ⟨x, hx⟩ else var (h x)) =
      (menu (codeCellMenuE e side β (S.arity β + 1))).bind (fun x => var (h x)) :=
    Term.bind_congr fun x hx => by simp [show ¬ x < S.arity β by have := (hΓv x hx).1; omega]
  have hC : (code KB (menu (codeMenusE e side MB))).bind
      (fun x => if hx : x < S.arity β then args ⟨x, hx⟩ else var (h x)) =
      (code KB (menu (codeMenusE e side MB))).bind (fun x => var (h x)) :=
    Term.bind_congr fun x hx => by simp [show ¬ x < S.arity β by have := hCv x hx; omega]
  have hA : (fun j : Fin (S.arity β) => (var (j : ℕ) : Term sig ℕ).bind
      (fun x => if hx : x < S.arity β then args ⟨x, hx⟩ else var (h x))) = args :=
    funext fun j => by simp [j.isLt]
  simp only [List.map_cons, List.map_ofFn, Function.comp_def, hΓ, eΓ, hA]
  exact congrArg (fun c => cellSkel _ _ _ (c :: List.ofFn args) ℓ) (hC.trans eC)

end Enum

-- ============================================================================================
-- 5. Main results for the enumeration `symEnum S`
-- ============================================================================================

-- finitely many symbols, and the expanded sides of the rules
variable [Finite S.Sym] (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

/-- **Shifting the menu `Γ_β`** (Fig. 10, page 89). -/
theorem menu_codeCellMenu_shift
    -- the symbol
    (β : S.Sym)
    -- the renaming, which sends `k₀ + i` to `k₀' + i`
    (g : ℕ → ℕ)
    (k₀ k₀' : ℕ)
    (hg : ∀ i, g (k₀ + i) = k₀' + i) :
    (menu (codeCellMenu side β k₀)).bind (fun x => var (g x))
      = menu (codeCellMenu side β k₀') :=
  menu_codeCellMenuE_shift (symEnum S) side β g k₀ k₀' hg

/-- **Shifting the menu `Γ = Γ_0 & ⋯ & Γ_{m-1}`** (Fig. 10, page 89). -/
theorem menu_codeMenus_shift
    -- the renaming, which sends `k₀ + i` to `k₀' + i`
    (g : ℕ → ℕ)
    (k₀ k₀' : ℕ)
    (hg : ∀ i, g (k₀ + i) = k₀' + i) :
    (menu (codeMenus side k₀)).bind (fun x => var (g x))
      = menu (codeMenus side k₀') :=
  menu_codeMenusE_shift (symEnum S) side g k₀ k₀' hg

/-- **The extracted tree is an instance of `[β]`** (Fig. 10, pages 89–90). The tree of `[β]` with
a copy of the menu `Γ_β` (numbered from any `B`, renamed by `g`), a copy of the code `!Γ` of
`Γ = codeMenus side k₀` (cut names from `K`, renamed by `g'`), the trees `args` on the ports and the
loop `ℓ` is the principal net `[β]` of `codeTranslation side` with `args` on its ports and its
internal wires named by some `F`. -/
theorem codeNet_inst_eq
    -- the symbol of the cell
    (β : S.Sym)
    -- the first names: of the copy of `Γ_β`, of `Γ`, and the first cut name of `!Γ`
    (B k₀ K : ℕ)
    -- the renamings of the copy of `Γ_β` and of the copy of `!Γ`
    (g g' : ℕ → ℕ)
    -- the loop
    (ℓ : ℕ)
    -- the trees on the ports
    (args : Fin (S.arity β) → Term sig ℕ) :
    -- some naming `F` of the internal wires makes the instance of `[β]` with `args` on its ports
    ∃ F, (codeNet side β).inst args F
      -- equal to the cell `[β]` with the renamed `Γ_β`, the renamed `!Γ`, `args` and the loop
      = cellSkel ((menu (codeCellMenu side β B)).bind fun x => var (g x)) (Nat.card S.Sym)
          (symEnum S β) (((code K (menu (codeMenus side k₀))).bind fun x => var (g' x)) ::
            List.ofFn args) ℓ :=
  codeNetE_inst_eq (symEnum S) side β B k₀ K g g' ℓ args

end INet.Comb
