/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Translations.TranslationComp

/-!
# The tree of `Ψ(p)` over `ℕ` (page 80)

Lafont 1997, page 80: "a translation extends to nets in an obvious way".

* `PNet.natTree_ofNat`, `Translation.natTree_trPNet`, `Translation.termTr_trPNet`: the tree of
  `Ψ(p)` over `ℕ` is exactly `Ψ.trTerm` applied to the tree of `p` over `ℕ`, which is a
  translation of it in the sense of `TermTr`. So `trPNet` translates nets "in the obvious way".
* `PNet.Iso.cells_eq`, `Translation.cells_trPNet`: `Iso` keeps the cells.

Contents, in the order of the file:

1. Auxiliary lemmas on principal nets over `ℕ`: `PNet.natTree_ofNat` (a net built by `ofNat`
   read back over `ℕ` is its tree), `PNet.cells_bind_var`, `PNet.Iso.cells_eq`,
   `PNet.cells_natTree` (renaming, `Iso` and reading over `ℕ` keep the cells).
2. Main results: `Translation.natTree_trPNet` (the tree of `Ψ(p)` is `Ψ.trTerm` of the tree of
   `p`), `Translation.termTr_trPNet` (it is a translation of it in the sense of `TermTr`),
   `Translation.cells_trPNet` (its cells).
-/

@[expose] public section

namespace INet

open Term

-- ============================================================================================
-- 1. Auxiliary lemmas: principal nets over `ℕ`
-- ============================================================================================

namespace PNet

variable {S : Signature} {n : ℕ}

/-- **`ofNat` read back over `ℕ`** (principal nets, page 80): the tree over `ℕ` of `ofNat n m t`,
its port `i` named `i` and its internal wire `w` named `n + w`, is `t`. -/
theorem natTree_ofNat
    -- the number of ports and of internal wires
    (n m : ℕ)
    -- the tree: its names are below `n + m`, each port `i < n` occurs once, and each internal
    -- wire `n + w` occurs twice
    (t : Term S ℕ)
    (hb : ∀ x ∈ t.vars, x < n + m)
    (hp : ∀ i < n, t.vars.count i = 1)
    (hw : ∀ w < m, t.vars.count (n + w) = 2) :
    -- the principal net built from `t`, read back over `ℕ`, is `t`
    (ofNat n m t hb hp hw).natTree = t := by
  change (((t.toFin hb).bind fun x => var (finSumFinEquiv.symm x)).bind
    fun x => var (Sum.elim (fun i : Fin n => (i : ℕ)) (fun w : Fin m => n + (w : ℕ)) x)) = t
  rw [Term.bind_bind]
  conv_rhs => rw [← Term.bind_toFin t hb]
  refine Term.bind_congr fun x _ => ?_
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective x
  rw [_root_.Equiv.symm_apply_apply]
  cases y <;> simp

/-- Renaming the leaves of a tree keeps its cells. -/
theorem cells_bind_var
    -- the types of names, and the renaming
    {ν μ : Type}
    (g : ν → μ)
    -- the tree
    (t : Term S ν) :
    (t.bind fun x => var (g x)).cells = t.cells := by
  rw [cells_bind]
  simp

/-- **`Iso` keeps the cells** (page 80): principal nets that are the same graph have the same
cells. -/
theorem Iso.cells_eq
    -- two principal nets that are the same graph
    {p q : PNet S n}
    (h : p.Iso q) :
    p.tree.cells = q.tree.cells := by
  obtain ⟨e, he⟩ := h
  rw [← he, cells_bind_var]

/-- The tree over `ℕ` of a principal net has its cells. -/
theorem cells_natTree
    -- the principal net
    (p : PNet S n) :
    p.natTree.cells = p.tree.cells :=
  cells_bind_var _ _

end PNet

-- ============================================================================================
-- 2. Main results: the tree of `Ψ(p)`
-- ============================================================================================

namespace Translation

variable {S' S'' : Signature} {n : ℕ}

/-- **`Ψ(p)` is `Ψ` applied to the tree of `p`** (page 80, "a translation extends to nets in an
obvious way"): the tree over `ℕ` of `Ψ.trPNet p` is `Ψ.trTerm` of the tree over `ℕ` of `p`, the
internal wires of the new instances numbered from `n + p.internal`. -/
theorem natTree_trPNet
    -- the translation
    (Ψ : Translation S' S'')
    -- the principal net of arity `n`
    (p : PNet S' n) :
    -- the new internal wires are numbered from `n + p.internal`
    (Ψ.trPNet p).natTree = Ψ.trTerm (n + p.internal) p.natTree :=
  PNet.natTree_ofNat _ _ _ _ _ _

/-- **`Ψ(p)` is a translation of `p`** (page 80): the tree over `ℕ` of `Ψ.trPNet p` is a
translation, in the sense of `TermTr`, of the tree over `ℕ` of `p`. -/
theorem termTr_trPNet
    -- the translation
    (Ψ : Translation S' S'')
    -- the principal net of arity `n`
    (p : PNet S' n) :
    Ψ.TermTr p.natTree (Ψ.trPNet p).natTree := by
  rw [natTree_trPNet]
  exact Ψ.termTr_trTerm _ _

/-- The cells of `Ψ(p)` are those of `Ψ.trTerm` of the tree of `p` (page 80). -/
theorem cells_trPNet
    -- the translation
    (Ψ : Translation S' S'')
    -- the principal net of arity `n`
    (p : PNet S' n) :
    (Ψ.trPNet p).tree.cells = (Ψ.trTerm (n + p.internal) p.natTree).cells := by
  rw [← PNet.cells_natTree, natTree_trPNet]

end Translation

end INet
