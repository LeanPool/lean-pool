/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Translations.TranslationCompAssoc
public import LeanPool.InteractionCombinators.Translations.TranslationInvertible

/-!
# Renamings plus permutations are the invertible translations (page 81)

Lafont 1997, page 81, top: if `Φ` is invertible, "each `Φ(α)` is necessarily of the following
form [a cell `α'` under a box `σ` on its auxiliary ports] where `α'` is a symbol of `Σ'` and `σ` is
a permutation. In other words, `Φ` is given by a renaming of the symbols and a permutation of the
auxiliary ports of each symbol."

`Translation.Invertible.exists_symEquiv` (`Translations/TranslationInvertible.lean`) proves that
an invertible translation has this form. This file gives the converse and the characterization.

The figure draws `σ` as a box with no arrow, so the paper fixes no direction for it; here, as in
`Invertible.net_eq`, it is read from the ports of `α'` to the ports of `Φ(α)`.

These results were first proved in `Checks/Translations/TranslationInvertibleReview.lean`.

Contents, in the order of the file:

1. Definitions: `PNet.permCell β σ`, the cell `β` with its auxiliary ports permuted by `σ`;
   `Translation.renPermTr e ρ`, a renaming of the symbols and a permutation of the ports;
   `renPermInv`, the permutations of its inverse.
2. Auxiliary lemmas: `permCell_eq_cell`, `trPNet_permCell`, `val_renPerm_symm_finCongr`;
   `Invertible.of_iso`, invertibility depends only on the nets `Φ(α)` up to `Iso`;
   `Invertible.iso_permCell`.
3. What `net_eq`, `sym` and `symEquiv` return: `net_eq_renPermTr`, `Invertible.sym_eq_of_tree`,
   `sym_renPermTr`, `Invertible.symEquiv_symm_eq`, `Invertible.sym_inverse_unique`,
   `symEquiv_renPermTr`. On a renaming plus permutation, `net_eq` returns the given permutation
   and `sym`, `symEquiv` the given renaming; `sym` depends only on `Φ`, and the inverse of
   `symEquiv` is the renaming of every inverse of `Φ`, not only of the inverse chosen in its
   definition.
4. Main results: `renPermTr_invertible`, every renaming plus permutation is invertible;
   `invertible_iff_renPermTr`, the invertible translations are exactly the renamings plus
   permutations, up to `Iso`.
-/

@[expose] public section

namespace INet

open Term

-- ============================================================================================
-- 1. Definitions
-- ============================================================================================

namespace PNet

variable {S : Signature}

/-- **A permuted cell** (page 81, the figure at the top): the cell `β` with its auxiliary ports
permuted by `σ`, its auxiliary port `j` being the port `σ j` of the net. It has no internal
wire. -/
def permCell
    -- the number of ports of the net
    {n : ℕ}
    -- the symbol of the cell, and the permutation of its auxiliary ports
    (β : S.Sym)
    (σ : Fin (S.arity β) ≃ Fin n) :
    PNet S n where
  internal := 0
  tree := .app β fun j => .var (.inl (σ j))
  port_count i := by
    rw [Term.vars_app, Multiset.count_sum']
    simp only [Term.vars_var, Multiset.count_singleton, Sum.inl.injEq]
    rw [← _root_.Equiv.sum_comp σ.symm]
    simp
  internal_count w := w.elim0

end PNet

namespace Translation

open PNet

variable {S S' S'' : Signature}

/-- **A renaming of the symbols and a permutation of the ports** (page 81): `α` is translated to
the cell `e α`, its auxiliary port `j` plugged into the port `ρ α j`. -/
def renPermTr
    -- the renaming of the symbols
    (e : S.Sym → S'.Sym)
    -- for each symbol `α`, the permutation from the auxiliary ports of `e α` to those of `α`
    (ρ : ∀ α, Fin (S'.arity (e α)) ≃ Fin (S.arity α)) :
    Translation S S' :=
  ⟨fun α => permCell (e α) (ρ α)⟩

/-- The permutations of the inverse of `renPermTr e ρ` (page 81): the port `j` of the cell
`e.symm α'` is the port `ρ⁻¹ j` of the net, read back in the arity of `α'`. -/
def renPermInv
    -- the renaming, a bijection of the symbols
    (e : S.Sym ≃ S'.Sym)
    -- the permutations of the ports
    (ρ : ∀ α, Fin (S'.arity (e α)) ≃ Fin (S.arity α))
    -- a symbol of the target
    (α' : S'.Sym) :
    Fin (S.arity (e.symm α')) ≃ Fin (S'.arity α') :=
  (ρ (e.symm α')).symm.trans (finCongr (congrArg S'.arity (e.apply_symm_apply α')))

end Translation

-- ============================================================================================
-- 2. Auxiliary lemmas
-- ============================================================================================

namespace PNet

variable {S : Signature}

/-- A permuted cell whose symbol is `α` and whose permutation keeps every port is the cell `α`
(page 81). -/
theorem permCell_eq_cell
    -- the symbol `β` of the permuted cell is `α`
    {α β : S.Sym}
    (hβ : β = α)
    -- the permutation keeps every port
    (σ : Fin (S.arity β) ≃ Fin (S.arity α))
    (hσ : ∀ j, (σ j : ℕ) = j) :
    permCell β σ = PNet.cell α := by
  subst hβ
  have : σ = _root_.Equiv.refl _ := _root_.Equiv.ext fun j => Fin.ext (hσ j)
  subst this
  rfl

end PNet

namespace Translation

open PNet

variable {S S' S'' : Signature}

/-- **The translation of a permuted cell by a renaming plus permutation** (pages 80-81): it is
the renamed cell, with the two permutations composed. -/
theorem trPNet_permCell
    -- the renaming plus permutation
    (e : S'.Sym → S''.Sym)
    (ρ : ∀ β, Fin (S''.arity (e β)) ≃ Fin (S'.arity β))
    -- the permuted cell
    {n : ℕ}
    (β : S'.Sym)
    (σ : Fin (S'.arity β) ≃ Fin n) :
    -- its translation is the same graph as the cell `e β`, permuted by `ρ β` then `σ`
    ((renPermTr e ρ).trPNet (permCell β σ)).Iso (permCell (e β) ((ρ β).trans σ)) := by
  have hs : (renPermTr e ρ).size (permCell β σ).natTree = 0 := by
    change 0 + ∑ i, (renPermTr e ρ).size (Term.var (σ i : ℕ)) = 0
    simp [Translation.size]
  have hm : (permCell (e β) ((ρ β).trans σ)).internal =
      0 + (renPermTr e ρ).size (permCell β σ).natTree := by
    rw [hs]
    rfl
  have hy := (renPermTr e ρ).trPNet_hyps (permCell β σ)
  exact PNet.iso_ofNat (permCell (e β) ((ρ β).trans σ)) (finCongr hm) hy.1 hy.2.1 hy.2.2 rfl

/-- The permutation of the inverse of a renaming plus permutation, applied after `ρ β`, keeps the
ports (page 81). -/
theorem val_renPerm_symm_finCongr
    -- the renaming plus permutation
    (e : S.Sym → S'.Sym)
    (ρ : ∀ α, Fin (S'.arity (e α)) ≃ Fin (S.arity α))
    -- two equal symbols, hence of equal arities after renaming
    {α β : S.Sym}
    (hβ : β = α)
    (h : S'.arity (e β) = S'.arity (e α))
    -- an auxiliary port of `β`
    (j : Fin (S.arity β)) :
    (ρ α (finCongr h ((ρ β).symm j)) : ℕ) = j := by
  subst hβ
  simp

/-- **Invertibility depends only on the graphs `Φ(α)`** (page 80): if `Φ` is invertible and
`Φ'(α)` is the same graph as `Φ(α)` for every `α`, then `Φ'` is invertible, with the same
inverse. -/
theorem Invertible.of_iso
    -- an invertible translation `Φ`, and a translation `Φ'`
    {Φ Φ' : Translation S S'}
    (h : Φ.Invertible)
    -- every `Φ'(α)` is the same graph as `Φ(α)`
    (hΦ : ∀ α, (Φ.net α).Iso (Φ'.net α)) :
    Φ'.Invertible := by
  obtain ⟨Ψ, h1, h2⟩ := h
  exact ⟨Ψ, fun α => ((comp_iso_right Ψ hΦ α).symm).trans (h1 α),
    fun α' => ((comp_iso_left Ψ hΦ α').symm).trans (h2 α')⟩

/-- An invertible translation sends `α` to the permuted cell of its root, up to the names of
internal wires (page 81): `Φ(α)` has no internal wire and is the cell `e α` with its port `j`
plugged into `ρ j`. -/
theorem Invertible.iso_permCell
    -- an invertible translation and a symbol `α`
    {Φ : Translation S S'}
    (h : Φ.Invertible)
    {α : S.Sym}
    -- the tree of `Φ(α)` is the cell `β`, its auxiliary port `j` plugged into the port `ρ j`
    {β : S'.Sym}
    (ρ : Fin (S'.arity β) ≃ Fin (S.arity α))
    (hρ : (Φ.net α).tree = Term.app β (fun j => Term.var (Sum.inl (ρ j)))) :
    (Φ.net α).Iso (permCell β ρ) := by
  refine ⟨finCongr (h.internal_eq_zero α), ?_⟩
  rw [hρ, Term.bind_app]
  rfl

-- ============================================================================================
-- 3. What `net_eq`, `sym` and `symEquiv` return
-- ============================================================================================

/-- **`net_eq` returns the given renaming and permutation** (page 81): if the tree of
`renPermTr e ρ` at `α` is the cell `α'` with its port `j` plugged into `ρ' j`, then `α' = e α` and
`ρ'` is `ρ α`. -/
theorem net_eq_renPermTr
    -- the renaming plus permutation
    (e : S.Sym → S'.Sym)
    (ρ : ∀ α, Fin (S'.arity (e α)) ≃ Fin (S.arity α))
    -- a symbol `α`, a symbol `α'` and a permutation `ρ'` of the ports of `α'`
    {α : S.Sym}
    {α' : S'.Sym}
    {ρ' : Fin (S'.arity α') ≃ Fin (S.arity α)}
    -- the tree of the translation of `α` is the cell `α'` permuted by `ρ'`
    (hρ : ((renPermTr e ρ).net α).tree = Term.app α' (fun j => Term.var (Sum.inl (ρ' j)))) :
    -- the symbol is `e α`
    α' = e α ∧
    -- and the permutation is `ρ α`
    HEq ρ' (ρ α) := by
  obtain ⟨h1, h2⟩ := Term.app.inj hρ
  subst h1
  refine ⟨rfl, heq_of_eq (_root_.Equiv.ext fun j => ?_)⟩
  have h3 := congrFun (eq_of_heq h2) j
  exact (Sum.inl_injective (Term.var.inj h3)).symm

/-- **`sym` depends only on `Φ`** (page 81): whatever proof of invertibility is used, `h.sym α` is
the root symbol of `Φ(α)`. -/
theorem Invertible.sym_eq_of_tree
    -- an invertible translation and a symbol `α`
    {Φ : Translation S S'}
    (h : Φ.Invertible)
    {α : S.Sym}
    -- the tree of `Φ(α)` has the root symbol `β`
    {β : S'.Sym}
    {ts : Fin (S'.arity β) → Term S' (Fin (S.arity α) ⊕ Fin (Φ.net α).internal)}
    (ht : (Φ.net α).tree = Term.app β ts) :
    h.sym α = β := by
  obtain ⟨ρ, hρ⟩ := h.net_eq_sym α
  rw [hρ] at ht
  exact (Term.app.inj ht).1

/-- The renaming of `renPermTr e ρ` is `e` (page 81). -/
theorem sym_renPermTr
    -- the renaming plus permutation
    (e : S.Sym → S'.Sym)
    (ρ : ∀ α, Fin (S'.arity (e α)) ≃ Fin (S.arity α))
    -- a proof that it is invertible
    (h : (renPermTr e ρ).Invertible)
    -- a symbol
    (α : S.Sym) :
    h.sym α = e α :=
  h.sym_eq_of_tree rfl

/-- **The inverse of `symEquiv` is the renaming of any inverse of `Φ`** (page 81), not only of
the inverse chosen by `symEquiv`. -/
theorem Invertible.symEquiv_symm_eq
    -- an invertible translation
    {Φ : Translation S S'}
    (h : Φ.Invertible)
    -- a translation `Ψ` inverse to `Φ` on both sides
    {Ψ : Translation S' S}
    (h1 : ∀ α, ((Ψ.comp Φ).net α).Iso ((Translation.id S).net α))
    (h2 : ∀ α', ((Φ.comp Ψ).net α').Iso ((Translation.id S').net α'))
    -- a symbol of the target
    (α' : S'.Sym) :
    h.symEquiv.symm α' = (Invertible.inverse h1 h2).sym α' := by
  rw [_root_.Equiv.symm_apply_eq]
  exact (Invertible.sym_sym (Invertible.inverse h1 h2) h (h2 α')).symm

/-- **Two inverses of `Φ` rename the symbols in the same way** (page 81). -/
theorem Invertible.sym_inverse_unique
    -- an invertible translation
    {Φ : Translation S S'}
    (h : Φ.Invertible)
    -- two translations `Ψ`, `Ψ'`, each inverse to `Φ` on both sides
    {Ψ Ψ' : Translation S' S}
    (h1 : ∀ α, ((Ψ.comp Φ).net α).Iso ((Translation.id S).net α))
    (h2 : ∀ α', ((Φ.comp Ψ).net α').Iso ((Translation.id S').net α'))
    (h1' : ∀ α, ((Ψ'.comp Φ).net α).Iso ((Translation.id S).net α))
    (h2' : ∀ α', ((Φ.comp Ψ').net α').Iso ((Translation.id S').net α')) :
    (Invertible.inverse h1 h2).sym = (Invertible.inverse h1' h2').sym :=
  funext fun α' => (h.symEquiv_symm_eq h1 h2 α').symm.trans (h.symEquiv_symm_eq h1' h2' α')

/-- `symEquiv` of a renaming plus permutation is the renaming (page 81). -/
theorem symEquiv_renPermTr
    -- the renaming plus permutation, the renaming a bijection
    (e : S.Sym ≃ S'.Sym)
    (ρ : ∀ α, Fin (S'.arity (e α)) ≃ Fin (S.arity α))
    -- a proof that it is invertible
    (h : (renPermTr e ρ).Invertible) :
    h.symEquiv = e :=
  _root_.Equiv.ext fun α => sym_renPermTr e ρ h α

-- ============================================================================================
-- 4. Main results: the invertible translations
-- ============================================================================================

/-- **Every renaming plus permutation is invertible** (page 81, the converse of
`Translation.Invertible.net_eq`): its inverse renames by `e⁻¹` and permutes by `ρ⁻¹`. -/
theorem renPermTr_invertible
    -- the renaming, a bijection of the symbols
    (e : S.Sym ≃ S'.Sym)
    -- for each symbol `α`, the permutation from the auxiliary ports of `e α` to those of `α`
    (ρ : ∀ α, Fin (S'.arity (e α)) ≃ Fin (S.arity α)) :
    (renPermTr e ρ).Invertible := by
  refine ⟨renPermTr e.symm (renPermInv e ρ), fun α => ?_, fun α' => ?_⟩
  · refine (trPNet_permCell _ _ _ _).trans ?_
    rw [permCell_eq_cell (e.symm_apply_apply α)]
    · exact PNet.Iso.refl _
    · intro j
      exact val_renPerm_symm_finCongr e ρ (e.symm_apply_apply α)
        (congrArg S'.arity (e.apply_symm_apply (e α))) j
  · refine (trPNet_permCell _ _ _ _).trans ?_
    rw [permCell_eq_cell (e.apply_symm_apply α')]
    · exact PNet.Iso.refl _
    · intro j
      simp [renPermInv]

/-- **The invertible translations are the renamings plus permutations** (page 81, top: "`Φ` is
given by a renaming of the symbols and a permutation of the auxiliary ports of each symbol"):
`Φ` is invertible if and only if there are a bijection `e` of the symbols and, for each `α`, a
bijection `ρ α` from the auxiliary ports of `e α` to those of `α`, such that every `Φ(α)` is the
same graph as the cell `e α` with its port `j` plugged into the port `ρ α j`. -/
theorem invertible_iff_renPermTr
    -- a translation
    (Φ : Translation S S') :
    -- `Φ` is invertible if and only if
    Φ.Invertible ↔
      -- there are a renaming `e` of the symbols and permutations `ρ` of the ports
      ∃ (e : S.Sym ≃ S'.Sym) (ρ : ∀ α, Fin (S'.arity (e α)) ≃ Fin (S.arity α)),
        -- such that every `Φ(α)` is the same graph as the permuted cell `e α`
        ∀ α, (Φ.net α).Iso ((renPermTr e ρ).net α) := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := h.exists_symEquiv
    choose ρ hρ using he
    exact ⟨e, ρ, fun α => h.iso_permCell (ρ α) (hρ α)⟩
  · rintro ⟨e, ρ, hΦ⟩
    exact (renPermTr_invertible e ρ).of_iso fun α => (hΦ α).symm

end Translation

end INet
