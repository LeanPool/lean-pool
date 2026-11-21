/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.General.CodeCellsMeet
public import LeanPool.InteractionCombinators.Universality.General.CodeShift

/-!
# The packages `Γ_{α,β}`, `Γ_{β,α}` of Fig. 10 against their multiplexors (pages 89–90)

Lafont 1997, Section 2.7, Fig. 10 (journal page 89, PDF page 21) and page 90, where the analogue
of Fig. 7 (page 86) is left to the reader. This file does the last rows of that analogue, as
`mux_gamma_mux_gamma` (`Fig7End.lean`) does them for Fig. 7. After the two cells `[α]`, `[β]` have
met (`codeCells_meet`), the multiplexor `M_{a+2}` of `[α]` faces the package `Γ_{α,β}` and the
multiplexor `M_{b+2}` of `[β]` faces `Γ_{β,α}`, the two multiplexors sharing the loop `ℓ`. Each
multiplexor annihilates with the dual multiplexor of its package (`mux_muxStar`): the code `!Γ` of
each cell meets the copier `C_p` of the package, the ports of each cell meet the trees of `⟨φ⟩` on
its side, and the loop joins the two transpositors `T_σ`, which annihilate
(`transpositorPerm_transpositorPerm`): the middle port `l` of `⟨φ⟩` meets the middle port `σ l` of
`⟨ψ⟩`.

Contents, in the order of the file:

1. Auxiliary lemmas: the multiplexors against the packages.
   * `codeGamma_loop` — `M_{a+2}` with leaves `c`, `ts`, `ℓ` against `Γ_{α,β}`.
   * `codeGamma_meet` — the last rows of the analogue of Fig. 7, at the level of trees, in a
     context `Δ`.
   * `codeGammaOpt_bind_codeRen` — the package met by `[α]` in `codeCells_meet`, renamed, is a
     package `Γ_{α,β}` with a shifted base.
2. Main result for any numbering `e` of the symbols: `codeCells_meet_endE`.
3. Main result: `codeCells_meet_end`, the two cells `[α]`, `[β]` of Fig. 10 plugged by their
   roots, when the sides of `α` against `β` and of `β` against `α` have the same middle ports and
   involution: `codeCells_meet` followed by `codeGamma_meet`.
-/

@[expose] public section

namespace INet.Comb

open Term Translation

variable {S : Signature}

-- ============================================================================================
-- 1. Auxiliary lemmas: the multiplexors against the packages
-- ============================================================================================

/-- **`M_{a+2}` against `Γ_{α,β}`, with any trees on the ports** (Fig. 10, page 89; the analogue of
Fig. 7, row 3, page 86). The multiplexor with leaves `c`, the `a` trees `ts` and the loop `ℓ`
against the package `Γ_{α,β}` of a side `φ` reduces, in any context `Δ`, to `c` against the copier
`C_p`, the loop against the transpositor `T_σ` on the trees of `⟨φ⟩` at the middle ports, and each
`ts[p]` against the tree of `⟨φ⟩` at the port `p`. -/
theorem codeGamma_loop
    -- the number `m` of symbols and their numbering `idx`
    (m : ℕ)
    (idx : S.Sym → ℕ)
    -- the side `φ`, with `a` ports and `k` middle ports, and its involution `σ`
    {a k : ℕ}
    (φ : Rule S a k)
    (σ : Equiv.Perm (Fin k))
    (hσ : Function.Involutive σ)
    -- the base `k₀` of the names of the package
    (k₀ : ℕ)
    -- the leaves of the multiplexor: `c`, the `a` trees `ts`, the loop `ℓ`
    (c : Term sig ℕ)
    (ts : List (Term sig ℕ))
    (hts : ts.length = a)
    (ℓ : ℕ)
    -- the rest of the net
    (Δ : CNet) :
    -- the multiplexor against the package reduces to: `c` against the copier `C_p`, the loop
    -- against the transpositor `T_σ`, and each `ts[p]` against the tree of `⟨φ⟩` at the port `p`
    Red (s(mux (c :: ts ++ [var ℓ]), codeGamma m idx φ σ hσ k₀) ::ₘ Δ)
      (s(c, copier (codeGammaExtras m idx φ k₀))
        ::ₘ s(var ℓ, transpositorPerm σ hσ (fun j => codePort m idx φ k₀ (.inr j)))
        ::ₘ ((Finset.univ.val.map fun p : Fin a =>
              s(ts[(p : ℕ)]'(hts ▸ p.2), codePort m idx φ k₀ (.inl p)))
            + Δ)) := by
  have hlen : (c :: ts ++ [var ℓ]).length =
      (copier (codeGammaExtras m idx φ k₀) ::
        (List.ofFn (fun i => codePort m idx φ k₀ (.inl i)) ++
          [transpositorPerm σ hσ (fun j => codePort m idx φ k₀ (.inr j))])).length := by
    simp [hts]
  refine (mux_muxStar _ _ Δ hlen).cast rfl ?_
  rw [List.cons_append, List.zipWith_cons_cons, List.zipWith_append (by simp [hts]),
    ← Multiset.cons_coe, ← Multiset.coe_add, coe_zipWith_ofFn ts hts]
  simp only [List.zipWith_cons_cons, List.zipWith_nil_right, ← Multiset.cons_coe,
    Multiset.coe_nil]
  ms

/-- **The last rows of the analogue of Fig. 7 for Fig. 10** (Lafont 1997, pages 89–90; Fig. 7,
page 86). The multiplexor `M_{a+2}` with leaves `c`, `ts` and `ℓ` against the package `Γ_{α,β}` of
a side `φ`, and `M_{b+2}` with leaves `c'`, `us` and the same `ℓ` against the package `Γ_{β,α}` of a
side `ψ` with the same involution `σ` of the `k` middle ports, reduce up to wires to: `c` against
the copier `C_p` of `Γ_{α,β}`, `c'` against the copier of `Γ_{β,α}`, the tree `ts[p]` against the
tree of `⟨φ⟩` at its port `p`, the tree `us[q]` against the tree of `⟨ψ⟩` at its port `q`, and the
tree of `⟨φ⟩` at the middle port `l` against the tree of `⟨ψ⟩` at the middle port `σ l`.

No hypothesis on `φ` and `ψ` is needed beyond linearity of the whole net. -/
theorem codeGamma_meet
    -- the number `m` of symbols and their numbering `idx`
    (m : ℕ)
    (idx : S.Sym → ℕ)
    -- the two sides `φ`, `ψ`, with `a` and `b` ports, the same `k` middle ports and the same
    -- involution `σ`
    {a b k : ℕ}
    (φ : Rule S a k)
    (ψ : Rule S b k)
    (σ : Equiv.Perm (Fin k))
    (hσ : Function.Involutive σ)
    -- the bases `k₀`, `k₁` of the names of the two packages
    (k₀ k₁ : ℕ)
    -- the leaves of the two multiplexors: `c`, `ts` and `c'`, `us`, then the shared loop `ℓ`
    (c c' : Term sig ℕ)
    (ts us : List (Term sig ℕ))
    (hts : ts.length = a)
    (hus : us.length = b)
    (ℓ : ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the net we start from is linear
    (hlin : Net.Linear
      (s(mux (c :: ts ++ [var ℓ]), codeGamma m idx φ σ hσ k₀)
        ::ₘ s(mux (c' :: us ++ [var ℓ]), codeGamma m idx ψ σ hσ k₁)
        ::ₘ Δ)) :
    -- there is a net `M` such that
    ∃ M,
      -- the two multiplexors against their packages, beside `Δ`, reduce up to wires to `M`,
      StepsE system
        (s(mux (c :: ts ++ [var ℓ]), codeGamma m idx φ σ hσ k₀)
          ::ₘ s(mux (c' :: us ++ [var ℓ]), codeGamma m idx ψ σ hσ k₁)
          ::ₘ Δ)
        M ∧
      -- and `M` is the same graph as: `c` and `c'` against the copiers of the two packages,
      -- `ts[p]` against `⟨φ⟩` at `p`, `us[q]` against `⟨ψ⟩` at `q`, and `⟨φ⟩` at the middle
      -- port `l` against `⟨ψ⟩` at `σ l`, beside `Δ`
      Equiv M
        (s(c, copier (codeGammaExtras m idx φ k₀))
          ::ₘ s(c', copier (codeGammaExtras m idx ψ k₁))
          ::ₘ ((Finset.univ.val.map fun p : Fin a =>
                s(ts[(p : ℕ)]'(hts ▸ p.2), codePort m idx φ k₀ (.inl p)))
              + (Finset.univ.val.map fun q : Fin b =>
                s(us[(q : ℕ)]'(hus ▸ q.2), codePort m idx ψ k₁ (.inl q)))
              + (Finset.univ.val.map fun l : Fin k =>
                s(codePort m idx φ k₀ (.inr l), codePort m idx ψ k₁ (.inr (σ l))))
              + Δ)) := by
  set Tφ := transpositorPerm σ hσ (fun j => codePort m idx φ k₀ (.inr j)) with hTφ
  set Tψ := transpositorPerm σ hσ (fun j => codePort m idx ψ k₁ (.inr j)) with hTψ
  set Cφ := copier (codeGammaExtras m idx φ k₀) with hCφ
  set Cψ := copier (codeGammaExtras m idx ψ k₁) with hCψ
  set Xφ : CNet := Finset.univ.val.map fun p : Fin a =>
    s(ts[(p : ℕ)]'(hts ▸ p.2), codePort m idx φ k₀ (.inl p)) with hXφ
  set Xψ : CNet := Finset.univ.val.map fun q : Fin b =>
    s(us[(q : ℕ)]'(hus ▸ q.2), codePort m idx ψ k₁ (.inl q)) with hXψ
  set Y : CNet := Finset.univ.val.map fun l : Fin k =>
    s(codePort m idx φ k₀ (.inr l), codePort m idx ψ k₁ (.inr (σ l))) with hY
  -- the first multiplexor meets its dual
  have h1 := codeGamma_loop m idx φ σ hσ k₀ c ts hts ℓ
    (s(mux (c' :: us ++ [var ℓ]), codeGamma m idx ψ σ hσ k₁) ::ₘ Δ)
  -- the second multiplexor meets its dual
  have h2 := codeGamma_loop m idx ψ σ hσ k₁ c' us hus ℓ
    (s(c, Cφ) ::ₘ s(var ℓ, Tφ) ::ₘ (Xφ + Δ))
  set R : CNet := s(c, Cφ) ::ₘ s(c', Cψ) ::ₘ (Xφ + Xψ + Δ) with hR
  have h12 : Red (s(mux (c :: ts ++ [var ℓ]), codeGamma m idx φ σ hσ k₀) ::ₘ
      s(mux (c' :: us ++ [var ℓ]), codeGamma m idx ψ σ hσ k₁) ::ₘ Δ)
      (s(Tφ, var ℓ) ::ₘ s(var ℓ, Tψ) ::ₘ R) := by
    refine h1.trans (h2.cast (by rw [← hTφ, ← hXφ, ← hCφ]; ms) ?_)
    rw [← hTψ, ← hXψ, ← hCψ, hR, Sym2.eq_swap (a := Tφ)]
    ms
  have L2 : Net.Linear (s(Tφ, var ℓ) ::ₘ s(var ℓ, Tψ) ::ₘ R) :=
    h12.linear system_wellFormed.linear hlin
  -- the loop joins the two transpositors
  have E := equiv_contract Tφ Tψ ℓ R L2
  -- the transpositors annihilate
  have h3 := transpositorPerm_transpositorPerm σ hσ (fun j => codePort m idx φ k₀ (.inr j))
    (fun j => codePort m idx ψ k₁ (.inr j)) R
  obtain ⟨M, hS, hE⟩ := stepsE_of_equiv E h3.stepsE
  refine ⟨M, h12.stepsE.trans hS, hE.trans (Equiv.of_eq ?_)⟩
  rw [← hY, hR]
  ms

/-- The package `Γ_{α,β}` met by `[α]` in `codeCells_meet`, renamed by `codeRen ys K'`, is the
package `Γ_{α,β}` numbered from `K' + B` (page 89), when the side of `α` against `β` exists. -/
theorem codeGammaOpt_bind_codeRen
    -- the optional side `o`, equal to the side `φ`, with `a` ports and `k` middle ports, linear
    -- and expanded, with its involution `σ`
    {a n k : ℕ}
    (o : Option (ExpSide S a))
    (φ : Rule S a k)
    (σ : Equiv.Perm (Fin k))
    (hl : φ.Linear)
    (he : φ.Expanded)
    (hσ : Function.Involutive σ)
    (ho : o = some ⟨k, φ, σ, hl, he, hσ⟩)
    -- the number `m` of symbols and their numbering `idx`
    (m : ℕ)
    (idx : S.Sym → ℕ)
    -- the renaming `codeRen ys K'`, and the base `B` of the package, at least the number `n` of
    -- the names `ys`
    (ys : Fin n → ℕ)
    (K' B : ℕ)
    (hB : n ≤ B) :
    -- the renamed package is the package numbered from `K' + B`
    (codeGammaOpt m idx o B).bind (fun x => var (codeRen ys K' x))
      = codeGamma m idx φ σ hσ (K' + B) := by
  subst ho
  refine codeGamma_shift m idx φ σ hσ _ B (K' + B) fun i => ?_
  simp only [codeRen, show ¬ B + i < n by omega, dite_false]
  omega

-- ============================================================================================
-- 2. Main result for any numbering of the symbols
-- ============================================================================================

section Enum

-- the numbering `e` of the `n` symbols of the signature, and the expanded sides of the rules
variable {n : ℕ} (e : S.Sym ≃ Fin n)
  (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

/-- **Two cells `[α]`, `[β]` of Fig. 10 plugged by their roots, to the end, for any numbering `e`
of the symbols** (Lafont 1997, Fig. 10, pages 89–90; page 90: no order on the symbols is needed).
This is `codeCells_meet_end` with the `n` symbols numbered by any `e : S.Sym ≃ Fin n`: the cells
are `codeNetE e side α`, `codeNetE e side β`, and the menus, keys and sizes are the `E` versions.
Let the side of `α` against `β` be `φ` and the side of `β` against `α` be `ψ`, with the same `k`
middle ports and involution `σ`. The net reduces up to wires to: the renamed code `!Γ` of each
cell against the copier `C_p` of the package it meets, each port `xs p` (`ys q`) against the tree
of `⟨φ⟩` (`⟨ψ⟩`) at that port, and the tree of `⟨φ⟩` at the middle port `l` against the tree of
`⟨ψ⟩` at `σ l`. It composes `codeCells_meetE` with `codeGamma_meet`. -/
theorem codeCells_meet_endE
    -- the two symbols, the names on the ports of their cells, and the names of the internal
    -- wires of the cells
    (α β : S.Sym)
    (xs : Fin (S.arity α) → ℕ)
    (ys : Fin (S.arity β) → ℕ)
    (f : Fin (codeNetE e side α).internal → ℕ)
    (g : Fin (codeNetE e side β).internal → ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the side `φ` of `α` against `β` and the side `ψ` of `β` against `α`, with the same `k`
    -- middle ports and the same involution `σ`, both linear and expanded
    {k : ℕ}
    (φ : Rule S (S.arity α) k)
    (ψ : Rule S (S.arity β) k)
    (σ : Equiv.Perm (Fin k))
    (hσ : Function.Involutive σ)
    (hl : φ.Linear)
    (he : φ.Expanded)
    (hl' : ψ.Linear)
    (he' : ψ.Expanded)
    (hs : side α β = some ⟨k, φ, σ, hl, he, hσ⟩)
    (hs' : side β α = some ⟨k, ψ, σ, hl', he', hσ⟩)
    -- the net we start from is linear: the two cells plugged by their roots, beside `Δ`
    (hlin : Net.Linear
      (s((codeNetE e side α).inst (fun i => var (xs i)) f,
          (codeNetE e side β).inst (fun j => var (ys j)) g)
        ::ₘ Δ)) :
    -- there are bounds `K`, `K'` and a net `M` such that
    ∃ (K K' : ℕ) (M : CNet),
      -- the two cells plugged by their roots, beside `Δ`, reduce up to wires to `M`,
      StepsE system
        (s((codeNetE e side α).inst (fun i => var (xs i)) f,
            (codeNetE e side β).inst (fun j => var (ys j)) g)
          ::ₘ Δ)
        M ∧
      -- and `M` is the same graph as: the renamed code `!Γ` of `[α]` against the copier of
      -- `Γ_{α,β}`, the renamed code of `[β]` against the copier of `Γ_{β,α}`, each `xs p`
      -- against `⟨φ⟩` at `p`, each `ys q` against `⟨ψ⟩` at `q`, and `⟨φ⟩` at the middle port
      -- `l` against `⟨ψ⟩` at `σ l`, beside `Δ`
      Equiv M
        (s((code (codeKeyE e side α) (menu (codeMenusE e side (codeMenuBaseE e side α)))).bind
              (fun x => var (codeRen xs K x)),
            copier (codeGammaExtras n (fun γ => (e γ : ℕ)) φ
              (K' + (S.arity β + 1 + off (codeCellSizesE e side β) (e α)))))
          ::ₘ s((code (codeKeyE e side β) (menu (codeMenusE e side (codeMenuBaseE e side β)))).bind
              (fun x => var (codeRen ys K' x)),
            copier (codeGammaExtras n (fun γ => (e γ : ℕ)) ψ
              (K + (S.arity α + 1 + off (codeCellSizesE e side α) (e β)))))
          ::ₘ ((Finset.univ.val.map fun p : Fin (S.arity α) =>
                s(var (xs p), codePort n (fun γ => (e γ : ℕ)) φ
                  (K' + (S.arity β + 1 + off (codeCellSizesE e side β) (e α))) (.inl p)))
              + (Finset.univ.val.map fun q : Fin (S.arity β) =>
                s(var (ys q), codePort n (fun γ => (e γ : ℕ)) ψ
                  (K + (S.arity α + 1 + off (codeCellSizesE e side α) (e β))) (.inl q)))
              + (Finset.univ.val.map fun l : Fin k =>
                s(codePort n (fun γ => (e γ : ℕ)) φ
                    (K' + (S.arity β + 1 + off (codeCellSizesE e side β) (e α))) (.inr l),
                  codePort n (fun γ => (e γ : ℕ)) ψ
                    (K + (S.arity α + 1 + off (codeCellSizesE e side α) (e β)))
                    (.inr (σ l))))
              + Δ)) := by
  obtain ⟨K, K', M1, hS1, hE1⟩ := codeCells_meetE e side α β xs ys f g Δ hlin
  rw [codeGammaOpt_bind_codeRen _ φ σ hl he hσ hs _ _ ys K' _ (by omega),
    codeGammaOpt_bind_codeRen _ ψ σ hl' he' hσ hs' _ _ xs K _ (by omega)] at hE1
  have L1 := hE1.linear (hS1.linear system_wellFormed.linear hlin)
  obtain ⟨M2, hS2, hE2⟩ := codeGamma_meet n (fun γ => (e γ : ℕ)) φ ψ σ hσ _ _ _ _
    _ _ (List.length_ofFn) (List.length_ofFn) _ Δ L1
  obtain ⟨M3, hS3, hE3⟩ := stepsE_of_equiv hE1 hS2
  refine ⟨K, K', M3, hS1.trans hS3, hE3.trans (hE2.trans (Equiv.of_eq ?_))⟩
  simp only [List.getElem_ofFn]

end Enum

-- ============================================================================================
-- 3. Main result: the symbols numbered by `symEnum S`
-- ============================================================================================

-- a signature with finitely many symbols, and the expanded sides of the rules
variable [Finite S.Sym] (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

/-- **Two cells `[α]`, `[β]` of Fig. 10 plugged by their roots, to the end** (Lafont 1997, Fig. 10,
pages 89–90; the analogue of the whole of Fig. 7, page 86). Let the side of `α` against `β` be a
side `φ` and the side of `β` against `α` a side `ψ`, both with the same `k` middle ports and the
same involution `σ`. With the names `xs`, `ys` on the ports of `[α]`, `[β]`, any names of their
internal wires, in a context `Δ` with the whole net linear, the net reduces up to wires to:

* the code `!Γ` of `[α]` (renamed by `codeRen xs K`) against the copier `C_p` of `Γ_{α,β}`, and
  the code of `[β]` (renamed by `codeRen ys K'`) against the copier of `Γ_{β,α}`;
* each port `xs p` against the tree of `⟨φ⟩` at the port `p`, and each `ys q` against the tree of
  `⟨ψ⟩` at the port `q`;
* the tree of `⟨φ⟩` at the middle port `l` against the tree of `⟨ψ⟩` at the middle port `σ l`.

The package `Γ_{α,β}` is numbered from `K' + S.arity β + 1 + off (codeCellSizes side β) α`, its
place in the menu of `[β]` shifted by `K'`, and `Γ_{β,α}` likewise from `K + …`, the bounds `K`,
`K'` being those of `codeCells_meet`. It composes `codeCells_meet` with `codeGamma_meet`. -/
theorem codeCells_meet_end
    -- the two symbols, the names on the ports of their cells, and the names of the internal
    -- wires of the cells
    (α β : S.Sym)
    (xs : Fin (S.arity α) → ℕ)
    (ys : Fin (S.arity β) → ℕ)
    (f : Fin (codeNet side α).internal → ℕ)
    (g : Fin (codeNet side β).internal → ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the side `φ` of `α` against `β` and the side `ψ` of `β` against `α`, with the same `k`
    -- middle ports and the same involution `σ`, both linear and expanded
    {k : ℕ}
    (φ : Rule S (S.arity α) k)
    (ψ : Rule S (S.arity β) k)
    (σ : Equiv.Perm (Fin k))
    (hσ : Function.Involutive σ)
    (hl : φ.Linear)
    (he : φ.Expanded)
    (hl' : ψ.Linear)
    (he' : ψ.Expanded)
    (hs : side α β = some ⟨k, φ, σ, hl, he, hσ⟩)
    (hs' : side β α = some ⟨k, ψ, σ, hl', he', hσ⟩)
    -- the net we start from is linear: the two cells plugged by their roots, beside `Δ`
    (hlin : Net.Linear
      (s((codeNet side α).inst (fun i => var (xs i)) f,
          (codeNet side β).inst (fun j => var (ys j)) g)
        ::ₘ Δ)) :
    -- there are bounds `K`, `K'` and a net `M` such that
    ∃ (K K' : ℕ) (M : CNet),
      -- the two cells plugged by their roots, beside `Δ`, reduce up to wires to `M`,
      StepsE system
        (s((codeNet side α).inst (fun i => var (xs i)) f,
            (codeNet side β).inst (fun j => var (ys j)) g)
          ::ₘ Δ)
        M ∧
      -- and `M` is the same graph as: the renamed code `!Γ` of `[α]` against the copier of
      -- `Γ_{α,β}`, the renamed code of `[β]` against the copier of `Γ_{β,α}`, each `xs p`
      -- against `⟨φ⟩` at `p`, each `ys q` against `⟨ψ⟩` at `q`, and `⟨φ⟩` at the middle port
      -- `l` against `⟨ψ⟩` at `σ l`, beside `Δ`
      Equiv M
        (s((code (codeKey side α) (menu (codeMenus side (codeMenuBase side α)))).bind
              (fun x => var (codeRen xs K x)),
            copier (codeGammaExtras (Nat.card S.Sym) (fun γ => symEnum S γ) φ
              (K' + (S.arity β + 1 + off (codeCellSizes side β) (symEnum S α)))))
          ::ₘ s((code (codeKey side β) (menu (codeMenus side (codeMenuBase side β)))).bind
              (fun x => var (codeRen ys K' x)),
            copier (codeGammaExtras (Nat.card S.Sym) (fun γ => symEnum S γ) ψ
              (K + (S.arity α + 1 + off (codeCellSizes side α) (symEnum S β)))))
          ::ₘ ((Finset.univ.val.map fun p : Fin (S.arity α) =>
                s(var (xs p), codePort (Nat.card S.Sym) (fun γ => symEnum S γ) φ
                  (K' + (S.arity β + 1 + off (codeCellSizes side β) (symEnum S α))) (.inl p)))
              + (Finset.univ.val.map fun q : Fin (S.arity β) =>
                s(var (ys q), codePort (Nat.card S.Sym) (fun γ => symEnum S γ) ψ
                  (K + (S.arity α + 1 + off (codeCellSizes side α) (symEnum S β))) (.inl q)))
              + (Finset.univ.val.map fun l : Fin k =>
                s(codePort (Nat.card S.Sym) (fun γ => symEnum S γ) φ
                    (K' + (S.arity β + 1 + off (codeCellSizes side β) (symEnum S α))) (.inr l),
                  codePort (Nat.card S.Sym) (fun γ => symEnum S γ) ψ
                    (K + (S.arity α + 1 + off (codeCellSizes side α) (symEnum S β)))
                    (.inr (σ l))))
              + Δ)) :=
  codeCells_meet_endE (symEnum S) side α β xs ys f g Δ φ ψ σ hσ hl he hl' he' hs hs' hlin

end INet.Comb
