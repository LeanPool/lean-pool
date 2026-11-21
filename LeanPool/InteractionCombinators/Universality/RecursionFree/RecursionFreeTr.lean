/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.RecursionFree.RecursionFreeSide
public import LeanPool.InteractionCombinators.Universality.RecursionFree.Gamma
public import LeanPool.InteractionCombinators.Universality.RecursionFree.CellSkeleton
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Lafont, "Interaction Combinators" (1997): the translation `[α]` of a recursion-free system

Page 86 (PDF page 18), Section 2.4, Fig. 6. The cell `α_j` is translated into the net of Fig. 6
(left): the transpositor `T_{1,1}` carrying the menu `Γ_{1,j} & … & Γ_{m,j}`, the selector
`S^j_m` on the multiplexor `M_{n_j+1}`, and the loop `ℓ`. The package `Γ_{i,j}` uses
translations of the cells of `φ_{i,j}`, which are smaller than `α_j`: "the translation is defined
by induction on the order".

Contents, in the order of the file:

1. Auxiliary lemmas: translations depend only on the symbols they meet. `size_bind_var`,
   `Translation.size_congr`, `trTerm_congr`, `mem_cells_gammaTree`, `gammaSize_eq`,
   `gammaSize_congr`, `gamma_congr`.
2. Definitions: the package of an optional side. `gammaOpt`, `gammaOptSize`, `vars_gammaOpt`.
3. Definitions: the tree of Fig. 6 as a principal net. `cellName` and its lemmas,
   `vars_cellSkel_ports`, `cellPNet` (the ports of `α` are the names `0, …, n - 1`, the loop `ℓ`
   is `n`, the packages take consecutive blocks above `n`), `cellPNet_congr`, `defaultPNet`.
4. Definitions: the cell `[α]` of Fig. 6. `symEnum`, `cellSizes`, `cellMenu`,
   `vars_menu_cellMenu`, `cellNet` (its packages built with a translation `Φ`), `cellNet_tree`,
   `cellNet_congr`.
5. Main results: the translation, by well-founded recursion on the rank. `lowerTr`,
   `System.RecursionFreeData.translation`, its fixpoint equation `translation_net`,
   `translation_net_of_rank_eq_zero`, `cells_side_of_rank_eq_zero`.
6. Example: the eraser of `systemNoConDup` (rank 0), `translation_noConDup_era`: its translation
   is `cellNet Φ D era` for every `Φ`.
-/

@[expose] public section

namespace INet

open Term

variable {S S' : Signature}

-- ============================================================================================
-- 1. Auxiliary lemmas: translations depend only on the symbols they meet
-- ============================================================================================

namespace Translation

/-- The size of the translation of a tree does not depend on the names of its leaves. -/
theorem size_bind_var
    -- the translation
    (Φ : Translation S S')
    -- the tree, and two renamings of its leaves
    {ν : Type}
    (t : Term S ν)
    (f g : ν → ℕ) :
    Φ.size (t.bind fun x => var (f x)) = Φ.size (t.bind fun x => var (g x)) := by
  induction t with
  | var x => rfl
  | app α ts ih => simp only [bind_app, size, ih]

/-- The size of the translation of a tree depends only on the translations of its cells. -/
theorem size_congr
    -- two translations
    {Φ Φ' : Translation S S'}
    -- the tree, on whose cells the two translations agree
    (t : Term S ℕ)
    (h : ∀ γ ∈ t.cells, Φ.net γ = Φ'.net γ) :
    Φ.size t = Φ'.size t := by
  induction t with
  | var x => rfl
  | app α ts ih =>
    simp only [cells_app, Multiset.mem_cons, Multiset.mem_sum, Finset.mem_univ, true_and] at h
    simp only [size, h α (Or.inl rfl), fun i => ih i fun γ hγ => h γ (Or.inr ⟨i, hγ⟩)]

/-- The translation of a tree depends only on the translations of its cells (pages 79–80). -/
theorem trTerm_congr
    -- two translations
    {Φ Φ' : Translation S S'}
    -- the tree, on whose cells the two translations agree
    (t : Term S ℕ)
    (h : ∀ γ ∈ t.cells, Φ.net γ = Φ'.net γ)
    -- the first name of the internal wires
    (k : ℕ) :
    Φ.trTerm k t = Φ'.trTerm k t := by
  induction t generalizing k with
  | var x => rfl
  | app α ts ih =>
    simp only [cells_app, Multiset.mem_cons, Multiset.mem_sum, Finset.mem_univ, true_and] at h
    have hs : ∀ j, Φ.size (ts j) = Φ'.size (ts j) := fun j =>
      size_congr _ fun γ hγ => h γ (Or.inr ⟨j, hγ⟩)
    have ih' : ∀ i k, Φ.trTerm k (ts i) = Φ'.trTerm k (ts i) := fun i k =>
      ih i (fun γ hγ => h γ (Or.inr ⟨i, hγ⟩)) k
    simp only [trTerm, hs, ih']
    rw [h α (Or.inl rfl)]

end Translation

namespace Comb

open Translation

variable {a k : ℕ}

/-- The cells of the tree of `φ` at a port are cells of `φ` (Fig. 6, page 86). -/
theorem mem_cells_gammaTree
    -- the side `φ`, the first name `k₀` and a port `p`
    {φ : Rule S a k}
    {k₀ : ℕ}
    {p : Fin a ⊕ Fin k}
    -- a cell of the tree of `φ` at `p`
    {γ : S.Sym}
    (hγ : γ ∈ (gammaTree φ k₀ p).cells) :
    γ ∈ φ.net.cells := by
  rw [gammaTree, cells_bind] at hγ
  simp only [cells_var, Multiset.bind_zero, add_zero] at hγ
  rcases φ.portTreeC_eq_or_mem p with h | h
  · rw [h] at hγ
    simp at hγ
  · exact Multiset.mem_bind.2 ⟨_, h, by rw [eqCells_mk]; simp [hγ]⟩

/-- The number of names of `Γ_{i,j}` does not depend on the first name `k₀`. -/
theorem gammaSize_eq
    -- the translation, the side `φ`, and the first name `k₀`
    (Φ : Translation S sig)
    (φ : Rule S a k)
    (k₀ : ℕ) :
    gammaSize Φ φ k₀ = gammaSize Φ φ 0 := by
  unfold gammaSize gammaSizes gammaTree
  congr 1
  exact Finset.sum_congr rfl fun q _ => size_bind_var Φ _ _ _

/-- The number of names of `Γ_{i,j}` depends only on the translations of the cells of `φ`. -/
theorem gammaSize_congr
    -- two translations, and a side `φ` on whose cells they agree
    {Φ Φ' : Translation S sig}
    {φ : Rule S a k}
    (h : ∀ γ ∈ φ.net.cells, Φ.net γ = Φ'.net γ)
    -- the first name
    (k₀ : ℕ) :
    gammaSize Φ φ k₀ = gammaSize Φ' φ k₀ := by
  unfold gammaSize gammaSizes
  congr 1
  exact Finset.sum_congr rfl fun q _ => size_congr _ fun γ hγ => h γ (mem_cells_gammaTree hγ)

/-- **`Γ_{i,j}` depends only on the translations of the cells of `φ_{i,j}`** (Fig. 6, page 86):
this is what makes the definition by induction on the order possible. -/
theorem gamma_congr
    -- two translations, and a side `φ`
    {Φ Φ' : Translation S sig}
    {φ : Rule S a k}
    -- the involution of the middle ports
    (σ : Equiv.Perm (Fin k))
    (hσ : Function.Involutive σ)
    -- the first name
    (k₀ : ℕ)
    -- the two translations agree on the cells of `φ`
    (h : ∀ γ ∈ φ.net.cells, Φ.net γ = Φ'.net γ) :
    gamma Φ φ σ hσ k₀ = gamma Φ' φ σ hσ k₀ := by
  have hs : gammaSizes Φ φ k₀ = gammaSizes Φ' φ k₀ := funext fun q =>
    size_congr _ fun γ hγ => h γ (mem_cells_gammaTree hγ)
  have hp : ∀ p, gammaPort Φ φ k₀ p = gammaPort Φ' φ k₀ p := fun p => by
    unfold gammaPort
    rw [hs]
    exact trTerm_congr _ (fun γ hγ => h γ (mem_cells_gammaTree hγ)) _
  unfold gamma
  simp only [hp]

-- ============================================================================================
-- 2. Definitions: the package of an optional side
-- ============================================================================================

/-- `Γ_{i,j}` for the side of `α_i` against `α_j`, numbered from `k₀`; an eraser when there is no
rule between them (Fig. 6, page 86). -/
noncomputable def gammaOpt
    -- the translation
    (Φ : Translation S sig) :
    -- the side, if any, and the first name `k₀`
    Option (ExpSide S a) → ℕ → Term sig ℕ
  | some s, k₀ => gamma Φ s.φ s.σ s.involutive k₀
  | none, _ => mkEra

/-- The number of names of `gammaOpt`. -/
noncomputable def gammaOptSize
    -- the translation
    (Φ : Translation S sig) :
    -- the side, if any
    Option (ExpSide S a) → ℕ
  | some s => gammaSize Φ s.φ 0
  | none => 0

/-- The names of `gammaOpt Φ o k₀` are both ends of each name of `[k₀, k₀ + gammaOptSize Φ o)`. -/
theorem vars_gammaOpt
    -- the translation, the side if any, and the first name
    (Φ : Translation S sig)
    (o : Option (ExpSide S a))
    (k₀ : ℕ) :
    (gammaOpt Φ o k₀).vars = 2 • Multiset.Ico k₀ (k₀ + gammaOptSize Φ o) := by
  cases o with
  | none => simp [gammaOpt, gammaOptSize]
  | some s =>
    rw [gammaOpt, gammaOptSize, vars_gamma Φ s.expanded s.linear, gammaSize_eq]

-- ============================================================================================
-- 3. Definitions: the tree of Fig. 6 as a principal net
-- ============================================================================================

/-- The name `x` of the tree of Fig. 6 as a leaf of a principal net with `n` ports and `I + 1`
internal wires: `x < n` is a port, `n ≤ x < n + I + 1` an internal wire. -/
def cellName
    -- the number of ports, and `I + 1` internal wires
    (n I : ℕ)
    -- the name
    (x : ℕ) :
    Fin n ⊕ Fin (I + 1) :=
  if h : x < n then .inl ⟨x, h⟩ else if h' : x - n < I + 1 then .inr ⟨x - n, h'⟩ else .inr 0

/-- The names `0, …, n - 1` of the ports. -/
theorem map_val_univ (n : ℕ) :
    (Finset.univ.val.map fun w : Fin n => (w : ℕ)) = Multiset.Ico 0 n := by
  simpa using map_add_univ 0 n

-- the names `0, …, n - 1` are read by `cellName` as the `n` ports
theorem map_cellName_ports
    -- the number of ports, and `I + 1` internal wires
    (n I : ℕ) :
    (Multiset.Ico 0 n).map (cellName n I) = Finset.univ.val.map Sum.inl := by
  rw [← map_val_univ, Multiset.map_map]
  refine Multiset.map_congr rfl fun w _ => ?_
  simp [cellName]

-- the names `n, …, n + I` are read by `cellName` as the `I + 1` internal wires
theorem map_cellName_Ico
    -- the number of ports, and `I + 1` internal wires
    (n I : ℕ) :
    (Multiset.Ico n (n + (I + 1))).map (cellName n I) = Finset.univ.val.map Sum.inr := by
  rw [← map_add_univ, Multiset.map_map]
  refine Multiset.map_congr rfl fun w _ => ?_
  have := w.isLt
  simp only [Function.comp_apply, cellName]
  rw [dite_eq_right_of_eq_false (eq_false (by omega)),
    dite_eq_left_of_eq_true (eq_true (by omega))]
  exact congrArg Sum.inr (Fin.ext (by simp))

/-- The names of the tree of Fig. 6 (left, page 86), with the ports `ts = 0, …, n - 1`, the loop
`ℓ = n`, and a menu `G` whose names are both ends of each name of `[n + 1, n + 1 + I)`. -/
theorem vars_cellSkel_ports
    -- the number of ports, the number `m` of symbols and the index `i` of the selector
    (n m i : ℕ)
    -- the menu, whose names are both ends of each name of `[n + 1, n + 1 + I)`
    (I : ℕ)
    (G : Term sig ℕ)
    (hG : G.vars = 2 • Multiset.Ico (n + 1) (n + 1 + I)) :
    -- the names are the ports once, and both ends of the loop `n` and of the names of the menu
    (cellSkel G m i (List.ofFn fun j : Fin n => var (j : ℕ)) n).vars
      = Multiset.Ico 0 n + 2 • Multiset.Ico n (n + (I + 1)) := by
  have hts : ((List.ofFn fun j : Fin n => (var (j : ℕ) : Term sig ℕ)).map Term.vars).sum =
      Multiset.Ico 0 n := by
    rw [List.map_ofFn, List.sum_ofFn, ← map_val_univ]
    simp only [Function.comp_def, vars_var]
    rw [Finset.sum_eq_multiset_sum]
    have h := Multiset.sum_map_singleton (Finset.univ.val.map fun w : Fin n => (w : ℕ))
    rwa [Multiset.map_map] at h
  have h1 : Multiset.Ico n (n + 1) = {n} :=
    (Multiset.Nodup.ext Multiset.nodup_Ico (Multiset.nodup_singleton n)).2 fun x => by
      simp only [Multiset.mem_Ico, Multiset.mem_singleton]; omega
  have hI : Multiset.Ico n (n + (I + 1)) = n ::ₘ Multiset.Ico (n + 1) (n + 1 + I) := by
    rw [← Multiset.Ico_add_Ico_eq_Ico (show n ≤ n + 1 by omega) (show n + 1 ≤ n + (I + 1) by omega),
      h1, Multiset.singleton_add, show n + (I + 1) = n + 1 + I by omega]
  rw [cellSkel, vars_transpositor]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, vars_cellSel,
    vars_mux, List.map_append, List.sum_append, hts, hG, hI, vars_var]
  rw [← Multiset.singleton_add]
  simp only [two_nsmul]
  abel

/-- **The tree of Fig. 6 as a principal net** (page 86). The tree `cellSkel (menu G) |G| i ts n`
with the ports `ts = 0, …, n - 1` and the loop `ℓ = n`, when the names of the menu are both ends
of each name of `[n + 1, n + 1 + I)`: the names `< n` become the ports, the names of
`[n, n + I + 1)` the internal wires. -/
def cellPNet
    -- the number of ports, and the number of names of the menu
    (n I : ℕ)
    -- the menu, and the index of the selector
    (G : List (Term sig ℕ))
    (i : ℕ)
    -- the names of the menu are both ends of each name of `[n + 1, n + 1 + I)`
    (hG : (menu G).vars = 2 • Multiset.Ico (n + 1) (n + 1 + I)) :
    PNet sig n where
  internal := I + 1
  tree := (cellSkel (menu G) G.length i (List.ofFn fun j : Fin n => var (j : ℕ)) n).bind
    fun x => var (cellName n I x)
  port_count j := by
    rw [vars_bind]
    simp only [vars_var, Multiset.bind_singleton]
    rw [vars_cellSkel_ports n _ _ I _ hG, Multiset.map_add, Multiset.map_nsmul,
      map_cellName_ports, map_cellName_Ico, Multiset.count_add, Multiset.count_nsmul,
      Multiset.count_map_eq_count' _ _ Sum.inl_injective,
      Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ_val _),
      Multiset.count_eq_zero.2 (by simp)]
  internal_count w := by
    rw [vars_bind]
    simp only [vars_var, Multiset.bind_singleton]
    rw [vars_cellSkel_ports n _ _ I _ hG, Multiset.map_add, Multiset.map_nsmul,
      map_cellName_ports, map_cellName_Ico, Multiset.count_add, Multiset.count_nsmul,
      Multiset.count_map_eq_count' _ _ Sum.inr_injective,
      Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ_val _),
      Multiset.count_eq_zero.2 (by simp)]

/-- `cellPNet` depends only on the size `I` and the menu `G`. -/
theorem cellPNet_congr
    -- the number of ports, two sizes, two menus, and the index of the selector
    {n I I' : ℕ}
    {G G' : List (Term sig ℕ)}
    {i : ℕ}
    -- the names of each menu
    {hG : (menu G).vars = 2 • Multiset.Ico (n + 1) (n + 1 + I)}
    {hG' : (menu G').vars = 2 • Multiset.Ico (n + 1) (n + 1 + I')}
    -- the sizes are equal, and the menus are equal
    (hI : I = I')
    (hGG : G = G') :
    cellPNet n I G i hG = cellPNet n I' G' i hG' := by
  subst hI hGG
  rfl

/-- A fixed principal net of arity `n` (an empty menu), put on the symbols that the recursion does
not see yet. -/
def defaultPNet (n : ℕ) : PNet sig n :=
  cellPNet n 0 [] 0 (by simp [menu, mux])

-- ============================================================================================
-- 4. Definitions: the cell `[α]` of Fig. 6
-- ============================================================================================

variable [Finite S.Sym] {I : System S}

/-- The numbering `α_0, …, α_{m-1}` of the alphabet (page 86). -/
noncomputable def symEnum
    -- a finite alphabet
    (S : Signature)
    [Finite S.Sym] :
    S.Sym ≃ Fin (Nat.card S.Sym) :=
  Finite.equivFin S.Sym

/-- The numbers of names of the packages `Γ_{i,α}` of the menu of `[α]`. -/
noncomputable def cellSizes
    -- the translation, the data of the recursion-free system, and the symbol `α`
    (Φ : Translation S sig)
    (D : I.RecursionFreeData)
    (α : S.Sym) :
    Fin (Nat.card S.Sym) → ℕ :=
  fun i => gammaOptSize Φ (D.side ((symEnum S).symm i) α)

/-- The menu `Γ_{0,α}, …, Γ_{m-1,α}` of `[α]` (Fig. 6, page 86): `Γ_{i,α}` is built from the side
of `α_i` against `α`, on the `i`-th block of names above `n + 1`, `n` the arity of `α`. -/
noncomputable def cellMenu
    -- the translation, the data of the recursion-free system, and the symbol `α`
    (Φ : Translation S sig)
    (D : I.RecursionFreeData)
    (α : S.Sym) :
    List (Term sig ℕ) :=
  List.ofFn fun i => gammaOpt Φ (D.side ((symEnum S).symm i) α)
    (S.arity α + 1 + off (cellSizes Φ D α) i)

/-- The names of the menu of `[α]` are both ends of each name of a block above `n + 1`. -/
theorem vars_menu_cellMenu
    -- the translation, the data of the recursion-free system, and the symbol `α`
    (Φ : Translation S sig)
    (D : I.RecursionFreeData)
    (α : S.Sym) :
    (menu (cellMenu Φ D α)).vars
      = 2 • Multiset.Ico (S.arity α + 1) (S.arity α + 1 + ∑ i, cellSizes Φ D α i) := by
  rw [menu, vars_mux, cellMenu, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_def, vars_gammaOpt]
  rw [← Finset.smul_sum]
  exact congrArg (2 • ·) (sum_Ico_off (cellSizes Φ D α) (S.arity α + 1))

/-- **The cell `[α]` of Fig. 6** (left, page 86), its packages `Γ_{i,α}` built with the
translation `Φ`: the transpositor `T_{1,1}` carrying the menu `Γ_{0,α} & … & Γ_{m-1,α}`, the
selector `S^{index α}_m` on the multiplexor `M_{n+1}` of the ports and the loop, and the loop. -/
noncomputable def cellNet
    -- the translation, the data of the recursion-free system, and the symbol `α`
    (Φ : Translation S sig)
    (D : I.RecursionFreeData)
    (α : S.Sym) :
    PNet sig (S.arity α) :=
  cellPNet (S.arity α) (∑ i, cellSizes Φ D α i) (cellMenu Φ D α) (symEnum S α)
    (vars_menu_cellMenu Φ D α)

/-- The tree of `cellNet` is the tree `cellSkel` of Fig. 6, its names read as ports and internal
wires (page 86). -/
theorem cellNet_tree
    -- the translation, the data of the recursion-free system, and the symbol `α`
    (Φ : Translation S sig)
    (D : I.RecursionFreeData)
    (α : S.Sym) :
    (cellNet Φ D α).tree
      = (cellSkel (menu (cellMenu Φ D α)) (Nat.card S.Sym) (symEnum S α)
          (List.ofFn fun j : Fin (S.arity α) => var (j : ℕ)) (S.arity α)).bind
          fun x => var (cellName (S.arity α) (∑ i, cellSizes Φ D α i) x) := by
  simp [cellNet, cellPNet, cellMenu]

/-- **`[α]` depends only on the translations of the symbols smaller than `α`** (Fig. 6, page 86):
the packages `Γ_{i,α}` use only translations of cells of `φ_{i,α}`, which are smaller than `α`
(`rank_side`, `gamma_congr`). -/
theorem cellNet_congr
    -- two translations, the data of the recursion-free system, and the symbol `α`
    {Φ Φ' : Translation S sig}
    {D : I.RecursionFreeData}
    {α : S.Sym}
    -- the two translations agree on the symbols of rank smaller than `α`
    (h : ∀ γ, D.rank γ < D.rank α → Φ.net γ = Φ'.net γ) :
    cellNet Φ D α = cellNet Φ' D α := by
  have hs : cellSizes Φ D α = cellSizes Φ' D α := funext fun i => by
    unfold cellSizes
    cases hsd : D.side ((symEnum S).symm i) α with
    | none => rfl
    | some s => exact gammaSize_congr (fun γ hγ => h γ (D.rank_side hsd γ hγ)) 0
  have hm : cellMenu Φ D α = cellMenu Φ' D α := by
    unfold cellMenu
    rw [hs]
    congr 1
    funext i
    cases hsd : D.side ((symEnum S).symm i) α with
    | none => rfl
    | some s => exact gamma_congr _ _ _ fun γ hγ => h γ (D.rank_side hsd γ hγ)
  exact cellPNet_congr (by rw [hs]) hm

-- ============================================================================================
-- 5. Main results: the translation, by induction on the order
-- ============================================================================================

/-- The translation seen by the call for `α`: the given principal nets on the symbols smaller
than `α`, `defaultPNet` on the others. -/
def _root_.INet.System.RecursionFreeData.lowerTr
    -- the data of the recursion-free system, and the symbol `α`
    (D : I.RecursionFreeData)
    (α : S.Sym)
    -- the principal nets already given to the symbols of smaller rank
    (rec : ∀ β, D.rank β < D.rank α → PNet sig (S.arity β)) :
    Translation S sig :=
  ⟨fun β => if h : D.rank β < D.rank α then rec β h else defaultPNet _⟩

/-- **The translation of a recursion-free system** (Lafont 1997, Fig. 6, page 86), "defined by
induction on the order": `[α]` is `cellNet` built with the translations of the symbols smaller
than `α`. -/
noncomputable def _root_.INet.System.RecursionFreeData.translation
    -- the data of the recursion-free system
    (D : I.RecursionFreeData) :
    Translation S sig :=
  ⟨(measure D.rank).wf.fix fun α rec => cellNet (D.lowerTr α rec) D α⟩

/-- **The fixpoint equation** (Fig. 6, page 86): the translation of `α` is the cell `[α]` whose
packages are built with the translation itself. -/
theorem _root_.INet.System.RecursionFreeData.translation_net
    -- the data of the recursion-free system, and the symbol `α`
    (D : I.RecursionFreeData)
    (α : S.Sym) :
    D.translation.net α = cellNet D.translation D α := by
  change (measure D.rank).wf.fix _ α = _
  rw [WellFounded.fix_eq]
  refine cellNet_congr fun γ hγ => ?_
  change (if h : D.rank γ < D.rank α then _ else _) = _
  rw [dite_eq_left_of_eq_true (eq_true hγ)]
  rfl

/-- For a symbol of rank `0`, the translation does not use any other translation (page 86): it is
`cellNet Φ D α` for every `Φ`. -/
theorem _root_.INet.System.RecursionFreeData.translation_net_of_rank_eq_zero
    -- the data of the recursion-free system, and a symbol `α` of rank `0`
    (D : I.RecursionFreeData)
    {α : S.Sym}
    (h0 : D.rank α = 0)
    -- any translation
    (Φ : Translation S sig) :
    D.translation.net α = cellNet Φ D α :=
  (D.translation_net α).trans (cellNet_congr fun γ hγ => absurd hγ (by omega))

omit [Finite S.Sym] in
/-- For a symbol of rank `0`, every side `φ_{i,α}` of its menu has no cell (page 86). -/
theorem _root_.INet.System.RecursionFreeData.cells_side_of_rank_eq_zero
    -- the data of the recursion-free system, a symbol `α` of rank `0`, and a symbol `β`
    (D : I.RecursionFreeData)
    {α β : S.Sym}
    (h0 : D.rank α = 0)
    -- the side `s` of `β` against `α`
    {s : ExpSide S (S.arity β)}
    (hs : D.side β α = some s) :
    s.φ.net.cells = 0 :=
  Multiset.eq_zero_of_forall_notMem fun γ hγ => absurd (D.rank_side hs γ hγ) (by omega)

-- ============================================================================================
-- 6. Example: the eraser of `systemNoConDup` (page 87)
-- ============================================================================================

-- the alphabet `con`, `dup`, `era` of the combinators is finite
instance : Finite sig.Sym :=
  Finite.of_surjective (fun i : Fin 3 => ![Comb.con, Comb.dup, Comb.era] i) (by
    intro c
    cases c
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩])

/-- **The translation of the eraser of `systemNoConDup`** (pages 86–87). The eraser has rank `0`,
so its translation is `cellNet Φ D era` for every translation `Φ`. Its menu has three packages,
one for each symbol: the side of `era` against `era` is the `φ` of the rule `era`–`era`, and the
side of `con` (resp. `dup`) against `era` is the `ψ` of the rule `era`–`con` (resp. `era`–`dup`),
since there is no rule `con`–`era`; none of these sides has a cell. -/
theorem translation_noConDup_era
    -- any translation
    (Φ : Translation sig sig) :
    -- the translation of `era` is `cellNet Φ D era`,
    recursionFreeDataNoConDup.translation.net Comb.era
        = cellNet Φ recursionFreeDataNoConDup Comb.era ∧
      -- the side of `era` against `era` is the `φ` of the rule `era`–`era`,
      recursionFreeDataNoConDup.rawSide Comb.era Comb.era
          = some (recursionFreeDataNoConDup.rawφ Comb.era Comb.era ruleEraEra rfl) ∧
      -- the side of `con` against `era` is the `ψ` of the rule `era`–`con`,
      recursionFreeDataNoConDup.rawSide Comb.con Comb.era
          = some (recursionFreeDataNoConDup.rawψ Comb.con Comb.era ruleEraBin rfl) ∧
      -- the side of `dup` against `era` is the `ψ` of the rule `era`–`dup`,
      recursionFreeDataNoConDup.rawSide Comb.dup Comb.era
          = some (recursionFreeDataNoConDup.rawψ Comb.dup Comb.era ruleEraBin rfl) ∧
      -- and no side against `era` has a cell
      ∀ β (s : ExpSide sig (sig.arity β)),
        recursionFreeDataNoConDup.side β Comb.era = some s → s.φ.net.cells = 0 :=
  ⟨recursionFreeDataNoConDup.translation_net_of_rank_eq_zero rfl Φ,
    recursionFreeDataNoConDup.rawSide_of_rule rfl,
    recursionFreeDataNoConDup.rawSide_of_rule_swap rfl rfl,
    recursionFreeDataNoConDup.rawSide_of_rule_swap rfl rfl,
    fun _ _ hs => recursionFreeDataNoConDup.cells_side_of_rank_eq_zero rfl hs⟩

end Comb

end INet
