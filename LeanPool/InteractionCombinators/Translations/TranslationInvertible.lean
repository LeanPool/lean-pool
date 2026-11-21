/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Translations.TranslationCompBasic

/-!
# An invertible translation renames the symbols and permutes the ports (page 81)

Lafont 1997, page 81, top: "If `Φ` is invertible, it is easy to see that each `Φ(α)` is
necessarily of the following form [a cell `α'` whose auxiliary ports are permuted by `σ`] where
`α'` is a symbol of `Σ'` and `σ` is a permutation. In other words, `Φ` is given by a renaming of
the symbols and a permutation of the auxiliary ports of each symbol."

The proof counts cells. The translation `Ψ(p)` of a principal net has, for each cell `β` of `p`,
the cells of `Ψ(β)` (`Translation.cells_trPNet_eq`). Since `Ψ(Φ(α))` and `Φ(Ψ(α'))` are single
cells, every `Φ(α)` and every `Ψ(α')` has at least one cell, and then exactly one. The internal
wires of `Ψ(Φ(α))` include those of `Φ(α)`, and the single cell `α` has none, so `Φ(α)` has none.

Contents, in the order of the file:

1. Auxiliary lemmas, counting the leaves and cells of a principal net: `PNet.vars_bind_cells`,
   `Term.eq_app_var_of_card_cells`, `card_eq_one_of_sum_map`.
2. Auxiliary lemmas, the cells of a translation: `Translation.cells_trTerm`,
   `Translation.cells_trPNet_eq`, `Translation.cells_id`, `Translation.sum_card_of_iso`.
3. An invertible translation sends each symbol to one cell: `Translation.Invertible.inverse`,
   `Translation.Invertible.card_cells`, `Translation.Invertible.internal_eq_zero` (`Φ(α)` has
   one cell and no internal wire), `Translation.Invertible.net_eq` (`Φ(α)` is a cell `α'` whose
   auxiliary port `j` is the port `ρ j` of the net, for a bijection `ρ`).
4. Main result, the renaming of the symbols is a bijection: `Translation.Invertible.sym`,
   `Translation.Invertible.net_eq_sym`, `Translation.Invertible.cells_net`,
   `Translation.Invertible.sym_sym`, `Translation.Invertible.symEquiv`,
   `Translation.Invertible.bijective_sym`, and `Translation.Invertible.exists_symEquiv`, the
   statement of page 81.
-/

@[expose] public section

namespace INet

open Term

-- ============================================================================================
-- 1. Auxiliary lemmas: counting the leaves and cells of a principal net
-- ============================================================================================

namespace PNet

variable {S : Signature} {n : ℕ}

/-- Plugging trees into the leaves of a principal net adds, for each auxiliary port, the cells of
the tree plugged into it, provided nothing with a cell is plugged into the internal wires: each
port occurs once (principal nets, page 80). -/
theorem vars_bind_cells
    -- the principal net
    {ν : Type}
    (p : PNet S n)
    -- the trees plugged into its leaves, without cells on the internal wires
    (g : Fin n ⊕ Fin p.internal → Term S ν)
    (hg : ∀ w, (g (.inr w)).cells = 0) :
    -- the cells of the plugged trees are those of the trees on the auxiliary ports
    (p.tree.vars.bind fun x => (g x).cells)
      = ∑ i, (g (.inl i)).cells := by
  classical
  have e : (p.tree.vars.bind fun x => (g x).cells) =
      ∑ x ∈ p.tree.vars.toFinset, p.tree.vars.count x • (g x).cells :=
    Finset.sum_multiset_map_count _ _
  rw [e, Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by
    rw [Multiset.count_eq_zero_of_notMem (by simpa using hx), zero_nsmul]),
    Fintype.sum_sum_type]
  simp [p.port_count, p.internal_count, hg]

end PNet

/-- A tree with exactly one cell is that cell with a leaf on each auxiliary port. -/
theorem Term.eq_app_var_of_card_cells
    -- a tree with one cell
    {S : Signature}
    {ν : Type}
    {t : Term S ν}
    (h : Multiset.card t.cells = 1) :
    -- it is a cell `α` with the leaf `x i` on its auxiliary port `i`
    ∃ (α : S.Sym) (x : Fin (S.arity α) → ν),
      t = app α fun i => var (x i) := by
  cases t with
  | var y => simp at h
  | app α ts =>
    rw [cells_app, Multiset.card_cons, Nat.add_eq_right, Multiset.card_eq_zero,
      Finset.sum_eq_zero_iff] at h
    have hv : ∀ i, ∃ y, ts i = var y := fun i => by
      have hi := h i (Finset.mem_univ _)
      cases hti : ts i with
      | var y => exact ⟨y, rfl⟩
      | app β us => rw [hti, cells_app] at hi; exact absurd hi (Multiset.cons_ne_zero)
    choose x hx using hv
    exact ⟨α, x, by rw [show ts = fun i => var (x i) from funext hx]⟩

/-- A multiset whose elements weigh at least `1` each and weigh `1` in total has one element. -/
theorem card_eq_one_of_sum_map
    -- the multiset
    {X : Type}
    {m : Multiset X}
    -- the weight: at least `1` on each element, `1` in total
    {f : X → ℕ}
    (hf : ∀ x, 1 ≤ f x)
    (hs : (m.map f).sum = 1) :
    Multiset.card m = 1 := by
  have hle : Multiset.card m ≤ 1 := by
    calc Multiset.card m = (m.map fun _ => 1).sum := by simp
      _ ≤ (m.map f).sum := Multiset.sum_map_le_sum_map _ _ fun x _ => hf x
      _ = 1 := hs
  have hne : Multiset.card m ≠ 0 := fun h0 => by
    rw [Multiset.card_eq_zero.1 h0] at hs
    simp at hs
  omega

namespace Translation

variable {S S' S'' : Signature}

-- ============================================================================================
-- 2. Auxiliary lemmas: the cells of a translation
-- ============================================================================================

/-- **The cells of a translated tree** (page 80): each cell `α` of the tree is replaced by the
cells of `Φ(α)`. -/
theorem cells_trTerm
    -- the translation
    (Φ : Translation S S')
    -- the first number used for the internal wires, and the tree
    (k : ℕ)
    (t : Term S ℕ) :
    (Φ.trTerm k t).cells
      = t.cells.bind fun α => (Φ.net α).tree.cells := by
  induction t generalizing k with
  | var x => rfl
  | app α ts ih =>
    change ((Φ.net α).tree.bind _).cells = _
    rw [cells_bind, PNet.vars_bind_cells _ _ (fun w => rfl)]
    simp only [Sum.elim_inl, ih, cells_app, Multiset.cons_bind, Multiset.sum_bind']

/-- **The cells of `Ψ(p)`** (page 80): each cell `β` of the principal net `p` is replaced by the
cells of `Ψ(β)`. -/
theorem cells_trPNet_eq
    -- the translation and the principal net
    {n : ℕ}
    (Ψ : Translation S' S'')
    (p : PNet S' n) :
    (Ψ.trPNet p).tree.cells
      = p.tree.cells.bind fun β => (Ψ.net β).tree.cells := by
  rw [cells_trPNet, cells_trTerm, PNet.cells_natTree]

/-- The cells of the single cell `α`, as a principal net: `α` alone. -/
theorem cells_id (α : S.Sym) : ((Translation.id S).net α).tree.cells = {α} := by
  simp [Translation.id, PNet.cell]

/-- If `Ψ(Φ(α))` is the single cell `α` (page 80), then the cells of `Φ(α)`, each weighed by the
number of cells of its translation by `Ψ`, weigh `1`. -/
theorem sum_card_of_iso
    -- two translations and a symbol `α`
    {Φ : Translation S S'}
    {Ψ : Translation S' S}
    {α : S.Sym}
    -- `Ψ(Φ(α))` is the single cell `α`
    (h : ((Ψ.comp Φ).net α).Iso ((Translation.id S).net α)) :
    -- the numbers of cells of `Ψ(β)`, for the cells `β` of `Φ(α)`, add up to `1`
    ((Φ.net α).tree.cells.map fun β => Multiset.card (Ψ.net β).tree.cells).sum = 1 := by
  have hc := congrArg Multiset.card h.cells_eq
  rw [cells_id] at hc
  change Multiset.card (Ψ.trPNet (Φ.net α)).tree.cells = _ at hc
  rw [cells_trPNet_eq, Multiset.card_bind] at hc
  simpa using hc

-- ============================================================================================
-- 3. An invertible translation sends each symbol to one cell
-- ============================================================================================

variable {Φ : Translation S S'}

/-- An inverse of an invertible translation is invertible, with inverse the translation
(page 80: the definition is symmetric). -/
theorem Invertible.inverse
    -- a translation `Ψ` back
    {Ψ : Translation S' S}
    -- `Ψ ∘ Φ` is the identity of `S`
    (h1 : ∀ α, ((Ψ.comp Φ).net α).Iso ((Translation.id S).net α))
    -- `Φ ∘ Ψ` is the identity of `S'`
    (h2 : ∀ α', ((Φ.comp Ψ).net α').Iso ((Translation.id S').net α')) :
    Ψ.Invertible :=
  ⟨Φ, h2, h1⟩

/-- **`Φ(α)` has exactly one cell** (page 81), when `Φ` is invertible. -/
theorem Invertible.card_cells
    -- `Φ` is invertible, and `α` is a symbol
    (h : Φ.Invertible)
    (α : S.Sym) :
    Multiset.card (Φ.net α).tree.cells = 1 := by
  obtain ⟨Ψ, h1, h2⟩ := h
  have hd : ∀ β, 1 ≤ Multiset.card (Ψ.net β).tree.cells := fun β => by
    have hs := sum_card_of_iso (h2 β)
    have : Multiset.card (Ψ.net β).tree.cells ≠ 0 := fun h0 => by
      rw [Multiset.card_eq_zero.1 h0] at hs
      simp at hs
    omega
  exact card_eq_one_of_sum_map hd (sum_card_of_iso (h1 α))

/-- **`Φ(α)` has no internal wire** (page 81), when `Φ` is invertible: the internal wires of
`Φ(α)` are internal wires of `Φ⁻¹(Φ(α))`, which is the single cell `α`. -/
theorem Invertible.internal_eq_zero
    -- `Φ` is invertible, and `α` is a symbol
    (h : Φ.Invertible)
    (α : S.Sym) :
    (Φ.net α).internal = 0 := by
  obtain ⟨Ψ, h1, -⟩ := h
  obtain ⟨e, -⟩ := h1 α
  have he : (Φ.net α).internal + Ψ.size (Φ.net α).natTree = 0 := Fin.equiv_iff_eq.1 ⟨e⟩
  omega

/-- **An invertible translation is a renaming and a permutation** (page 81, the figure at the
top): if `Φ` is invertible, then `Φ(α)` is a single cell `α'` of `S'` whose auxiliary ports are
plugged, without internal wire, into the auxiliary ports of the net in some order: the auxiliary
port `j` of `α'` is the port `ρ j` of `Φ(α)`, and `ρ` is a bijection. In the figure, `ρ` is the
permutation `σ` read from the ports of `α'` (below the box) to the ports of `Φ(α)` (above it). -/
theorem Invertible.net_eq
    -- `Φ` is invertible, and `α` is a symbol
    (h : Φ.Invertible)
    (α : S.Sym) :
    -- there are a symbol `α'` of `S'` and a bijection `ρ` of the auxiliary ports
    ∃ (α' : S'.Sym) (ρ : Fin (S'.arity α') ≃ Fin (S.arity α)),
      -- such that `Φ(α)` is the cell `α'` with the port `ρ j` of the net on its port `j`
      (Φ.net α).tree = Term.app α' (fun j => Term.var (Sum.inl (ρ j))) := by
  obtain ⟨α', x, hx⟩ := Term.eq_app_var_of_card_cells (h.card_cells α)
  have h0 := h.internal_eq_zero α
  have hl : ∀ j, ∃ i, x j = Sum.inl i := fun j => by
    rcases x j with i | w
    · exact ⟨i, rfl⟩
    · have := w.isLt
      omega
  choose ρ hρ using hl
  have hcount : ∀ i, (Finset.univ.filter fun j => i = ρ j).card = 1 := by
    intro i
    have hc := (Φ.net α).port_count i
    rw [hx] at hc
    simpa [Multiset.count_sum', hρ, Multiset.count_singleton, Finset.sum_boole] using hc
  have hbij : Function.Bijective ρ := by
    rw [Function.bijective_iff_existsUnique]
    intro i
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (hcount i)
    refine ⟨a, ?_, fun b hb => ?_⟩
    · have hm := Finset.mem_singleton_self a
      rw [← ha, Finset.mem_filter] at hm
      exact hm.2.symm
    · have hm : b ∈ ({a} : Finset _) := by
        rw [← ha, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hb.symm⟩
      exact Finset.mem_singleton.1 hm
  refine ⟨α', _root_.Equiv.ofBijective ρ hbij, ?_⟩
  rw [hx]
  simp [hρ]

-- ============================================================================================
-- 4. Main result: the renaming of the symbols is a bijection
-- ============================================================================================

/-- **The renaming of symbols** of an invertible translation (page 81): `h.sym α` is the symbol
`α'` of the single cell of `Φ(α)`. -/
noncomputable def Invertible.sym
    -- `Φ` is invertible, and `α` is a symbol
    (h : Φ.Invertible)
    (α : S.Sym) :
    S'.Sym :=
  (h.net_eq α).choose

/-- `Φ(α)` is the cell `h.sym α` with its auxiliary ports permuted (page 81). -/
theorem Invertible.net_eq_sym
    -- `Φ` is invertible, and `α` is a symbol
    (h : Φ.Invertible)
    (α : S.Sym) :
    -- there is a bijection `ρ` of the auxiliary ports
    ∃ ρ : Fin (S'.arity (h.sym α)) ≃ Fin (S.arity α),
      -- such that `Φ(α)` is the cell `h.sym α` with the port `ρ j` of the net on its port `j`
      (Φ.net α).tree = Term.app (h.sym α) (fun j => Term.var (Sum.inl (ρ j))) :=
  (h.net_eq α).choose_spec

/-- The cells of `Φ(α)`: the symbol `h.sym α` alone. -/
theorem Invertible.cells_net
    -- `Φ` is invertible, and `α` is a symbol
    (h : Φ.Invertible)
    (α : S.Sym) :
    (Φ.net α).tree.cells = {h.sym α} := by
  obtain ⟨ρ, hρ⟩ := h.net_eq_sym α
  rw [hρ]
  simp

/-- If `Ψ(Φ(α))` is the cell `α` and both translations are invertible, then renaming `α` by `Φ`,
then by `Ψ`, gives `α` back (page 81). -/
theorem Invertible.sym_sym
    -- `Φ` and a translation `Ψ` back are invertible
    {Ψ : Translation S' S}
    (hΦ : Φ.Invertible)
    (hΨ : Ψ.Invertible)
    -- `Ψ(Φ(α))` is the single cell `α`
    {α : S.Sym}
    (hα : ((Ψ.comp Φ).net α).Iso ((Translation.id S).net α)) :
    hΨ.sym (hΦ.sym α) = α := by
  have hc := hα.cells_eq
  rw [cells_id] at hc
  change (Ψ.trPNet (Φ.net α)).tree.cells = _ at hc
  rw [cells_trPNet_eq, hΦ.cells_net, Multiset.singleton_bind, hΨ.cells_net] at hc
  exact Multiset.singleton_inj.1 hc

/-- **The renaming of symbols is a bijection** (page 81, "`Φ` is given by a renaming of the
symbols"): its inverse is the renaming of the symbols of `Φ⁻¹`. -/
noncomputable def Invertible.symEquiv
    -- `Φ` is invertible
    (h : Φ.Invertible) :
    S.Sym ≃ S'.Sym :=
  have hΨ := Invertible.inverse h.choose_spec.1 h.choose_spec.2
  { toFun := h.sym
    invFun := hΨ.sym
    left_inv := fun α => Invertible.sym_sym h hΨ (h.choose_spec.1 α)
    right_inv := fun α' => Invertible.sym_sym hΨ h (h.choose_spec.2 α') }

/-- **The renaming of symbols is bijective** (page 81). -/
theorem Invertible.bijective_sym (h : Φ.Invertible) : Function.Bijective h.sym :=
  h.symEquiv.bijective

/-- **An invertible translation is a renaming of the symbols and a permutation of the auxiliary
ports of each symbol** (page 81, top): there is a bijection `e` from the symbols of `S` to those
of `S'` such that each `Φ(α)` is the single cell `e α`, its auxiliary port `j` plugged into the
port `ρ j` of the net, for a bijection `ρ`. -/
theorem Invertible.exists_symEquiv
    -- `Φ` is invertible
    (h : Φ.Invertible) :
    -- there is a bijection `e` from the symbols of `S` to those of `S'`
    ∃ e : S.Sym ≃ S'.Sym,
      -- such that each `Φ(α)` is the cell `e α`, up to a bijection `ρ` of the auxiliary ports
      ∀ α, ∃ ρ : Fin (S'.arity (e α)) ≃ Fin (S.arity α),
        (Φ.net α).tree = Term.app (e α) (fun j => Term.var (Sum.inl (ρ j))) :=
  ⟨h.symEquiv, h.net_eq_sym⟩

end Translation

end INet
