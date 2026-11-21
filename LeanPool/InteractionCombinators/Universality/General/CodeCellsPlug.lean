/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.General.CodeGammaMeet
public import LeanPool.InteractionCombinators.Universality.General.CodeGammaExtract
public import LeanPool.InteractionCombinators.Universality.RecursionFree.PlugTermTr

/-!
# Two cells `[α]`, `[β]` of Fig. 10 plugged by their roots reduce to the end of Fig. 7

Lafont 1997, Section 2.7, Fig. 10 (journal page 89, PDF page 21) and page 90, where the analogue
of Fig. 7 (pages 85–86) is "left to the reader". After the two cells have met and their
multiplexors have annihilated with the packages `Γ_{α,β}`, `Γ_{β,α}` (`codeCells_meet_end`), each
copier `C_p` makes the copies of `!Γ` that the cells of `⟨φ⟩` need, and `⟨φ⟩` becomes a
translation of the side `φ` (`codeGamma_extract`); the same for `ψ`. What is left is the net at the
end of Fig. 7, `plugTermTarget`, with translated trees.

The results are stated first with the symbols numbered by any `e : S.Sym ≃ Fin n` (names ending in
`E`), then for `e := symEnum S` under the names without `E`.

Contents, in the order of the file:

1. Auxiliary lemmas: rearranging the equations between the ports.
   * `ports_sum_form` — the equations left by `codeCells_meet_end` are in the form of
     `codeGamma_extract`.
   * `middle_reindex` — the middle equations with `σ` on one side are those with `σ` on the other,
     for an involutive `σ`.
2. Auxiliary lemmas for any numbering `e` of the symbols: `codeKeyE_bound`,
   `injOn_codeRen_codeE` — the code of `[α]` satisfies the hypotheses of `codeGamma_extractE`
   (the glue between `codeCells_meet_endE` and `codeGamma_extractE`, found by the review
   `CodeMeetReview.lean`).
3. Main result for any numbering: `codeCells_plugE` — the two cells plugged by their roots reduce
   to `plugTermTarget` of trees that are translations of the trees of `φ` and `ψ`.
4. Main result: `codeKey_bound`, `injOn_codeRen_code` and `codeCells_plug`, the same at
   `e := symEnum S`.
-/

@[expose] public section

namespace INet.Comb

open Term Translation

variable {S : Signature}

-- ============================================================================================
-- 1. Auxiliary lemmas: rearranging the equations between the ports
-- ============================================================================================

/-- **The ports left by `codeGamma_meet` are in the form of `codeGamma_extract`** (page 90): the
equations `ts p = F (.inl p)` and `F (.inr l) = G (σ l)` together are `∑ q, {s(P q, F q)}` with
the partner `P (.inl p) = ts p` and `P (.inr l) = G (σ l)`. -/
theorem ports_sum_form
    -- the number `a` of ports and `k` of middle wires
    {a k : ℕ}
    -- the trees on the ports and middle wires of one side
    (F : Fin a ⊕ Fin k → Term sig ℕ)
    -- the trees against the ports
    (ts : Fin a → Term sig ℕ)
    -- the trees of the other side on the middle wires, and the involution between them
    (G : Fin k → Term sig ℕ)
    (σ : Equiv.Perm (Fin k)) :
    -- the equations on the ports and on the middle wires form one sum over `Fin a ⊕ Fin k`
    (Finset.univ.val.map fun p : Fin a => s(ts p, F (.inl p))) +
        (Finset.univ.val.map fun l : Fin k => s(F (.inr l), G (σ l))) =
      ∑ q, {s(Sum.elim ts (fun l => G (σ l)) q, F q)} := by
  rw [Fintype.sum_sum_type, sum_singleton_univ, sum_singleton_univ]
  congr 1
  exact Multiset.map_congr rfl fun l _ => Sym2.eq_swap

/-- **The middle equations, with `σ` moved to the other side** (Fig. 7, page 86): for an
involutive `σ`, the equations `f l = g (σ l)` are the equations `g l = f (σ l)`. -/
theorem middle_reindex
    -- an involution of the `k` middle wires
    {k : ℕ}
    (σ : Equiv.Perm (Fin k))
    (hσ : Function.Involutive σ)
    -- the trees of the two sides on the middle wires
    (f g : Fin k → Term sig ℕ) :
    (Finset.univ.val.map fun l : Fin k => s(f l, g (σ l))) =
      Finset.univ.val.map fun l : Fin k => s(g l, f (σ l)) := by
  have e : (Finset.univ.val.map fun l : Fin k => s(f l, g (σ l))) =
      (Finset.univ.val.map σ).map fun l : Fin k => s(f l, g (σ l)) := by
    rw [Multiset.map_univ_val_equiv]
  rw [e, Multiset.map_map]
  congr 1
  funext l
  simp only [Function.comp_apply, hσ l]
  exact Sym2.eq_swap

section Enum

-- the numbering `e` of the `n` symbols, and the expanded sides of the rules
variable {n : ℕ} (e : S.Sym ≃ Fin n)
  (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

-- ============================================================================================
-- 2. Auxiliary lemmas for any numbering: the code of `[α]` fits `codeGamma_extractE`
-- ============================================================================================

/-- **The code of `[α]` satisfies the bound of `codeGamma_extractE`, for any numbering `e` of the
symbols** (page 89): with `B = codeMenuBaseE e side α`, the first cut name `codeKeyE e side α` of
`!Γ` is `B + ∑ codeMenuSizesE e side`. -/
theorem codeKeyE_bound
    -- a symbol
    (α : S.Sym) :
    codeMenuBaseE e side α + ∑ i, codeMenuSizesE e side i ≤ codeKeyE e side α :=
  le_rfl

/-- **The renaming of the code of `[α]` satisfies the hypothesis of `codeGamma_extractE`, for any
numbering `e` of the symbols** (page 89): the names of `!Γ` in `[α]` are above the ports, so
`codeRen xs K`, the renaming used by `codeCells_meetE`, is injective on them. -/
theorem injOn_codeRen_codeE
    -- a symbol
    (α : S.Sym)
    -- the names on the ports of `[α]`, and the shift of its other names
    (xs : Fin (S.arity α) → ℕ)
    (K : ℕ) :
    -- `codeRen xs K` is injective on the names of the code `!Γ` of `[α]`
    Set.InjOn (codeRen xs K)
      {x | x ∈ (code (codeKeyE e side α)
        (menu (codeMenusE e side (codeMenuBaseE e side α)))).vars} := by
  refine codeRen_injOn xs K _ fun x hx => ?_
  have hB : S.arity α + 1 ≤ codeMenuBaseE e side α := Nat.le_add_right _ _
  have hK : codeMenuBaseE e side α ≤ codeKeyE e side α := Nat.le_add_right _ _
  rw [Set.mem_ofPred_eq, vars_code] at hx
  rcases Multiset.mem_add.1 hx with hx | hx
  · rcases Multiset.mem_add.1 hx with hx | hx
    · rw [vars_menu_codeMenusE e side] at hx
      have := (Multiset.mem_Ico.1 (Multiset.mem_of_mem_nsmul hx)).1
      omega
    · have := ((decomp_ports _ _).2.1 x hx).1
      omega
  · have := ((decomp_ports _ _).2.1 x hx).1
    omega

-- ============================================================================================
-- 3. Main result for any numbering: two cells plugged by their roots
-- ============================================================================================

/-- **Two cells `[α]`, `[β]` of Fig. 10 plugged by their roots reduce to the end of Fig. 7 with
translated trees, for any numbering `e` of the symbols** (Lafont 1997, Fig. 10, pages 89–90, the
analogue of Fig. 7, pages 85–86, "left to the reader"; page 90: no order on the symbols is needed).
This is `codeCells_plug` with the `n` symbols numbered by any `e : S.Sym ≃ Fin n`. When the side
of `α` against `β` is `φ` and that of `β` against `α` is `ψ`, with
the same middle ports and involution `σ`, the cells `[α]` with ports `xs` and `[β]` with ports `ys`
plugged by their principal ports, in a linear net with any context `Δ`, reduce to a net `Equiv` to
`plugTermTarget σ tφ tψ xs ys` beside `Δ`, where each `tφ p` is a translation of the tree
`gammaTree φ k₀ p` and each `tψ q` of `gammaTree ψ k₁ q`, by `codeTranslationE e side`. -/
theorem codeCells_plugE
    -- the two symbols, and the names on the ports of their cells
    (α β : S.Sym)
    (xs : Fin (S.arity α) → ℕ)
    (ys : Fin (S.arity β) → ℕ)
    -- the names of the internal wires of the two cells
    (f : Fin (codeNetE e side α).internal → ℕ)
    (g : Fin (codeNetE e side β).internal → ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the expanded side `φ` of `α` against `β` and `ψ` of `β` against `α`, with `k` middle wires
    -- and the same involution `σ`
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
    -- the net we start from is linear: the two cells plugged by their roots, and `Δ`
    (hlin : Net.Linear (s((codeNetE e side α).inst (fun i => var (xs i)) f,
      (codeNetE e side β).inst (fun j => var (ys j)) g) ::ₘ Δ)) :
    -- there are numbers `k₀`, `k₁`, a net `M` and trees `tφ`, `tψ` such that
    ∃ (k₀ k₁ : ℕ) (M : CNet) (tφ : Fin (S.arity α) ⊕ Fin k → Term sig ℕ)
      (tψ : Fin (S.arity β) ⊕ Fin k → Term sig ℕ),
      -- the net reduces, up to wires, to `M`,
      StepsE system (s((codeNetE e side α).inst (fun i => var (xs i)) f,
        (codeNetE e side β).inst (fun j => var (ys j)) g) ::ₘ Δ) M ∧
      -- `M` is the same graph as the end of Fig. 7 with the trees `tφ`, `tψ`, beside `Δ`,
      Equiv M (plugTermTarget σ tφ tψ xs ys + Δ) ∧
      -- each `tφ p` is a translation of the tree `gammaTree φ k₀ p`,
      (∀ p, (codeTranslationE e side).TermTr (gammaTree φ k₀ p) (tφ p)) ∧
      -- and each `tψ q` of the tree `gammaTree ψ k₁ q`
      (∀ q, (codeTranslationE e side).TermTr (gammaTree ψ k₁ q) (tψ q)) := by
  obtain ⟨K, K', M1, hS1, hE1⟩ :=
    codeCells_meet_endE e side α β xs ys f g Δ φ ψ σ hσ hl he hl' he' hs hs' hlin
  set idx : S.Sym → ℕ := fun γ => (e γ : ℕ)
  set k₀ := K' + (S.arity β + 1 + off (codeCellSizesE e side β) (e α))
  set k₁ := K + (S.arity α + 1 + off (codeCellSizesE e side α) (e β))
  set Cα := (code (codeKeyE e side α)
    (menu (codeMenusE e side (codeMenuBaseE e side α)))).bind (fun x => var (codeRen xs K x))
  set Cβ := (code (codeKeyE e side β)
    (menu (codeMenusE e side (codeMenuBaseE e side β)))).bind (fun x => var (codeRen ys K' x))
  set Fφ := codePort n idx φ k₀
  set Fψ := codePort n idx ψ k₁
  set A := Finset.univ.val.map fun p : Fin (S.arity α) => s(var (xs p), Fφ (.inl p))
  set B := Finset.univ.val.map fun q : Fin (S.arity β) => s(var (ys q), Fψ (.inl q))
  set C := Finset.univ.val.map fun l : Fin k => s(Fφ (.inr l), Fψ (.inr (σ l)))
  set Pφ : Fin (S.arity α) ⊕ Fin k → Term sig ℕ :=
    Sum.elim (fun p => var (xs p)) (fun l => Fψ (.inr (σ l)))
  set Δ1 : CNet := s(copier (codeGammaExtras n idx ψ k₁), Cβ) ::ₘ (B + Δ)
  -- 1. the net of `codeCells_meet_end` in the form of `codeGamma_extract` for `φ`
  have e1 : s(Cα, copier (codeGammaExtras n idx φ k₀)) ::ₘ
      s(Cβ, copier (codeGammaExtras n idx ψ k₁)) ::ₘ (A + B + C + Δ) =
      s(copier (codeGammaExtras n idx φ k₀), Cα) ::ₘ ((∑ q, {s(Pφ q, Fφ q)}) + Δ1) := by
    rw [← ports_sum_form Fφ (fun p => var (xs p)) (fun l => Fψ (.inr l)) σ, Sym2.eq_swap,
      Sym2.eq_swap (a := Cβ)]
    simp only [Δ1, A, B, C]
    ms
  rw [e1] at hE1
  have L1 := hE1.linear (hS1.linear system_wellFormed.linear hlin)
  obtain ⟨M2, tφ, hS2, hE2, htφ⟩ := codeGamma_extractE e side φ k₀ (codeMenuBaseE e side α)
    (codeKeyE e side α) (codeKeyE_bound e side α) (codeRen xs K)
    (injOn_codeRen_codeE e side α xs K)
    Pφ Δ1 L1
  -- 2. the middle equations, now `tφ (.inr l) = Fψ (.inr (σ l))`, in the form for `ψ`
  set A' := Finset.univ.val.map fun p : Fin (S.arity α) => s(var (xs p), tφ (.inl p))
  set Pψ : Fin (S.arity β) ⊕ Fin k → Term sig ℕ :=
    Sum.elim (fun q => var (ys q)) (fun l => tφ (.inr (σ l)))
  have e2 : (∑ q, {s(Pφ q, tφ q)}) + Δ1 =
      s(copier (codeGammaExtras n idx ψ k₁), Cβ) ::ₘ ((∑ q, {s(Pψ q, Fψ q)}) + (A' + Δ)) := by
    have h1 : (∑ q, {s(Pφ q, tφ q)}) = A' +
        Finset.univ.val.map fun l : Fin k => s(tφ (.inr l), Fψ (.inr (σ l))) := by
      rw [Fintype.sum_sum_type, sum_singleton_univ, sum_singleton_univ]
      congr 1
      exact Multiset.map_congr rfl fun _ _ => Sym2.eq_swap
    have hm := middle_reindex σ hσ (fun l => tφ (.inr l)) (fun l => Fψ (.inr l))
    have hp := ports_sum_form Fψ (fun q => var (ys q)) (fun l => tφ (.inr l)) σ
    beta_reduce at hm hp
    rw [h1, hm, ← hp]
    simp only [Δ1, A', B]
    ms
  have L2 := hE2.linear (hS2.linear system_wellFormed.linear L1)
  rw [e2] at L2 hE2
  obtain ⟨M3, tψ, hS3, hE3, htψ⟩ := codeGamma_extractE e side ψ k₁ (codeMenuBaseE e side β)
    (codeKeyE e side β) (codeKeyE_bound e side β) (codeRen ys K')
    (injOn_codeRen_codeE e side β ys K')
    Pψ (A' + Δ) L2
  -- 3. back to `plugTermTarget`
  have e3 : (∑ q, {s(Pψ q, tψ q)}) + (A' + Δ) = plugTermTarget σ tφ tψ xs ys + Δ := by
    have h1 : (∑ q, {s(Pψ q, tψ q)}) =
        (Finset.univ.val.map fun q : Fin (S.arity β) => s(var (ys q), tψ (.inl q))) +
          Finset.univ.val.map fun l : Fin k => s(tψ (.inr l), tφ (.inr (σ l))) := by
      rw [Fintype.sum_sum_type, sum_singleton_univ, sum_singleton_univ]
      congr 1
      exact Multiset.map_congr rfl fun _ _ => Sym2.eq_swap
    have hm := middle_reindex σ hσ (fun l => tψ (.inr l)) (fun l => tφ (.inr l))
    beta_reduce at hm
    rw [h1, hm, plugTermTarget]
    simp only [A']
    ms
  rw [e3] at hE3
  obtain ⟨M4, hS4, hE4⟩ := stepsE_of_equiv hE2 hS3
  obtain ⟨M5, hS5, hE5⟩ := stepsE_of_equiv hE1 (hS2.trans hS4)
  exact ⟨k₀, k₁, M5, tφ, tψ, hS1.trans hS5, hE5.trans (hE4.trans hE3), htφ, htψ⟩

end Enum

-- ============================================================================================
-- 4. Main result: two cells plugged by their roots, symbols numbered by `symEnum S`
-- ============================================================================================

-- finitely many symbols, and the expanded sides of the rules
variable [Finite S.Sym] (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

/-- **The code of `[α]` satisfies the bound of `codeGamma_extract`** (page 89): with
`B = codeMenuBase side α`, the first cut name `codeKey side α` of `!Γ` is `B + ∑ codeMenuSizes`. -/
theorem codeKey_bound
    -- a symbol
    (α : S.Sym) :
    codeMenuBase side α + ∑ i, codeMenuSizes side i ≤ codeKey side α :=
  codeKeyE_bound (symEnum S) side α

/-- **The renaming of the code of `[α]` satisfies the hypothesis of `codeGamma_extract`**
(page 89): the names of `!Γ` in `[α]` are above the ports, so `codeRen xs K`, the renaming used by
`codeCells_meet`, is injective on them. -/
theorem injOn_codeRen_code
    -- a symbol
    (α : S.Sym)
    -- the names on the ports of `[α]`, and the shift of its other names
    (xs : Fin (S.arity α) → ℕ)
    (K : ℕ) :
    -- `codeRen xs K` is injective on the names of the code `!Γ` of `[α]`
    Set.InjOn (codeRen xs K)
      {x | x ∈ (code (codeKey side α) (menu (codeMenus side (codeMenuBase side α)))).vars} :=
  injOn_codeRen_codeE (symEnum S) side α xs K

/-- **Two cells `[α]`, `[β]` of Fig. 10 plugged by their roots reduce to the end of Fig. 7 with
translated trees** (Lafont 1997, Fig. 10, pages 89–90, the analogue of Fig. 7, pages 85–86, "left
to the reader"). When the side of `α` against `β` is `φ` and that of `β` against `α` is `ψ`, with
the same middle ports and involution `σ`, the cells `[α]` with ports `xs` and `[β]` with ports `ys`
plugged by their principal ports, in a linear net with any context `Δ`, reduce to a net `Equiv` to
`plugTermTarget σ tφ tψ xs ys` beside `Δ`, where each `tφ p` is a translation of the tree
`gammaTree φ k₀ p` and each `tψ q` of `gammaTree ψ k₁ q`, by `codeTranslation side`. -/
theorem codeCells_plug
    -- the two symbols, and the names on the ports of their cells
    (α β : S.Sym)
    (xs : Fin (S.arity α) → ℕ)
    (ys : Fin (S.arity β) → ℕ)
    -- the names of the internal wires of the two cells
    (f : Fin (codeNet side α).internal → ℕ)
    (g : Fin (codeNet side β).internal → ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the expanded side `φ` of `α` against `β` and `ψ` of `β` against `α`, with `k` middle wires
    -- and the same involution `σ`
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
    -- the net we start from is linear: the two cells plugged by their roots, and `Δ`
    (hlin : Net.Linear (s((codeNet side α).inst (fun i => var (xs i)) f,
      (codeNet side β).inst (fun j => var (ys j)) g) ::ₘ Δ)) :
    -- there are numbers `k₀`, `k₁`, a net `M` and trees `tφ`, `tψ` such that
    ∃ (k₀ k₁ : ℕ) (M : CNet) (tφ : Fin (S.arity α) ⊕ Fin k → Term sig ℕ)
      (tψ : Fin (S.arity β) ⊕ Fin k → Term sig ℕ),
      -- the net reduces, up to wires, to `M`,
      StepsE system (s((codeNet side α).inst (fun i => var (xs i)) f,
        (codeNet side β).inst (fun j => var (ys j)) g) ::ₘ Δ) M ∧
      -- `M` is the same graph as the end of Fig. 7 with the trees `tφ`, `tψ`, beside `Δ`,
      Equiv M (plugTermTarget σ tφ tψ xs ys + Δ) ∧
      -- each `tφ p` is a translation of the tree `gammaTree φ k₀ p`,
      (∀ p, (codeTranslation side).TermTr (gammaTree φ k₀ p) (tφ p)) ∧
      -- and each `tψ q` of the tree `gammaTree ψ k₁ q`
      (∀ q, (codeTranslation side).TermTr (gammaTree ψ k₁ q) (tψ q)) :=
  codeCells_plugE (symEnum S) side α β xs ys f g Δ φ ψ σ hσ hl he hl' he' hs hs' hlin

end INet.Comb
