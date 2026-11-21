/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Translations.TranslationCompBasic
public import LeanPool.InteractionCombinators.Text.NetTrWire

/-!
# Translating by a composite is composing the translations (page 80)

Lafont 1997, Section 1.7, journal page 80, last paragraph: "Composition of translations is defined
in the obvious way." `Translation.comp Ψ Φ` (`TranslationComp.lean`) translates `α` to `Ψ(Φ(α))`.
This file shows that it is the composite in the sense of the translations of trees and nets: a
translation by `Φ` followed by a translation by `Ψ` is a translation by `Ψ ∘ Φ`, with exactly the
same names, no renaming needed.

Contents, in the order of the file:

1. Auxiliary lemmas: `TermTr.eq_var_of_tr`, `TermTr.app_inv`, the translations of a wire and of
   a cell; `off_block_eq`, the blocks of names of `trTerm` for distinct subtrees are disjoint;
   `TermTr.bind_inv`, a translation by `Ψ` of `u.bind τ` is `(Ψ.trTerm k u).bind ρ`, where `ρ`
   sends the leaves of `u` to translations of their images and the new internal wires to wires.
2. Main results: `TermTr.comp`, `EqTr.comp`, `rel_eqTr_comp`, `NetTr.comp`, the translation by
   the composite, for trees, equations and nets.
-/

@[expose] public section

namespace INet

variable {S S' S'' : Signature}

open Term

namespace Translation

-- ============================================================================================
-- 1. Auxiliary lemmas: inverting a translation
-- ============================================================================================

/-- **The translation of a wire is that wire** (page 80): a translation only replaces cells. -/
theorem TermTr.eq_var_of_tr
    -- a translation `t` by `Ψ` of the wire `x`
    {Ψ : Translation S' S''}
    {x : ℕ}
    {t : Term S'' ℕ}
    (h : Ψ.TermTr (Term.var x) t) :
    t = Term.var x := by
  cases h
  rfl

/-- **The translation of a cell** (page 80): it is an instance of the principal net of its symbol,
whose arguments are translations of the subtrees. -/
theorem TermTr.app_inv
    -- the translation
    {Ψ : Translation S' S''}
    -- the cell `β` with its subtrees `vs`
    {β : S'.Sym}
    {vs : Fin (S'.arity β) → Term S' ℕ}
    -- a translation `t` of the cell
    {t : Term S'' ℕ}
    (h : Ψ.TermTr (Term.app β vs) t) :
    -- there are trees `ts` and names `f` for the internal wires of `Ψ(β)` such that
    ∃ (ts : Fin (S'.arity β) → Term S'' ℕ) (f : Fin (Ψ.net β).internal → ℕ),
      -- each `ts i` is a translation of the subtree `vs i`,
      (∀ i, Ψ.TermTr (vs i) (ts i)) ∧
      -- and `t` is the instance of `Ψ(β)` with `ts` on its ports and `f` on its wires
      t = (Ψ.net β).inst ts f := by
  cases h with
  | app _ _ ts f h => exact ⟨ts, f, h, rfl⟩

/-- The blocks of consecutive sizes laid end to end from `a` are disjoint (page 80): a name in the
blocks `i` and `j` forces `i = j`. -/
theorem off_block_eq
    -- the sizes of the `m` blocks, their start `a`, and a name `z`
    {m : ℕ}
    (s : Fin m → ℕ)
    (a z : ℕ)
    -- `z` lies in the block `i` and in the block `j`
    {i j : Fin m}
    (hi : a + off s i ≤ z ∧ z < a + off s i + s i)
    (hj : a + off s j ≤ z ∧ z < a + off s j + s j) :
    i = j := by
  by_contra hne
  have h := congrArg (Multiset.count z) (sum_Ico_off s a)
  rw [Multiset.count_sum', count_Ico] at h
  have h2 : (∑ l ∈ ({i, j} : Finset (Fin m)),
      (Multiset.Ico (a + off s l) (a + off s l + s l)).count z) ≤
      ∑ l, (Multiset.Ico (a + off s l) (a + off s l + s l)).count z :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Finset.sum_pair hne, count_Ico, count_Ico, h] at h2
  simp only [hi, hj, and_self, ↓reduceIte] at h2
  split_ifs at h2 <;> omega

/-- **Translating a tree with trees plugged into its leaves** (page 80). Let `u` be a tree whose
names are below `k`, and `τ` send every name occurring twice in `u` to a wire. A translation `t''`
by `Ψ` of `u.bind τ` is `(Ψ.trTerm k u).bind ρ`, the translation of `u` with its internal wires
numbered from `k`, for some `ρ` that sends each leaf `x` of `u` to a translation of `τ x` and each
new internal wire to a wire. -/
theorem TermTr.bind_inv
    -- the translation
    (Ψ : Translation S' S'')
    -- the trees `τ x` plugged into the leaves `x` of the tree `u`
    (τ : ℕ → Term S' ℕ)
    (u : Term S' ℕ) :
    -- for every bound `k` and every tree `t''`,
    ∀ (k : ℕ) (t'' : Term S'' ℕ),
      -- if the names of `u` are below `k`,
      (∀ x ∈ u.vars, x < k) →
      -- every name occurring twice in `u` is sent by `τ` to a wire,
      (∀ x, 2 ≤ u.vars.count x → ∃ y, τ x = Term.var y) →
      -- and `t''` is a translation by `Ψ` of `u` with `τ` plugged in,
      Ψ.TermTr (u.bind τ) t'' →
      -- then there is a substitution `ρ` such that
      ∃ ρ : ℕ → Term S'' ℕ,
        -- `ρ` sends each leaf `x` of `u` to a translation of `τ x`,
        (∀ x ∈ u.vars, Ψ.TermTr (τ x) (ρ x)) ∧
        -- `ρ` sends each new internal wire, from `k` on, to a wire,
        (∀ x, k ≤ x → x < k + Ψ.size u → ∃ y, ρ x = Term.var y) ∧
        -- and `t''` is the translation of `u` numbered from `k`, with `ρ` plugged in
        t'' = (Ψ.trTerm k u).bind ρ := by
  induction u with
  | var x =>
    intro k t'' _ _ h
    refine ⟨fun _ => t'', fun z hz => ?_, fun z h1 h2 => ?_, rfl⟩
    · rw [vars_var, Multiset.mem_singleton] at hz
      subst hz
      exact h
    · exact absurd h2 (by simp [size]; omega)
  | app β us ih =>
    intro k t'' hb hτ h
    classical
    obtain ⟨ts'', f'', hts, rfl⟩ := TermTr.app_inv
      (show Ψ.TermTr (Term.app β fun i => (us i).bind τ)
      t'' from h)
    let I := (Ψ.net β).internal
    let s : Fin (S'.arity β) → ℕ := fun j => Ψ.size (us j)
    let kk : Fin (S'.arity β) → ℕ := fun i => k + I + off s i
    have hcount : ∀ i x, (us i).vars.count x ≤ (Term.app β us).vars.count x := fun i x => by
      rw [vars_app, Multiset.count_sum']
      exact Finset.single_le_sum (f := fun l => (us l).vars.count x)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hsub : ∀ i x, x ∈ (us i).vars → x ∈ (Term.app β us).vars := fun i x hx =>
      Term.mem_vars_app i hx
    have hrec := fun i => ih i (kk i) (ts'' i) (fun x hx => (hb x (hsub i x hx)).trans_le
      (by simp only [kk]; omega)) (fun x hx => hτ x (hx.trans (hcount i x))) (hts i)
    choose ρs hρ1 hρ2 hρ3 using hrec
    let blk : Fin (S'.arity β) → ℕ → Prop := fun j x =>
      x ∈ (us j).vars ∨ (kk j ≤ x ∧ x < kk j + s j)
    let ρ : ℕ → Term S'' ℕ := fun x =>
      if hx : k ≤ x ∧ x < k + I then Term.var (f'' ⟨x - k, by omega⟩)
      else if hj : ∃ j, blk j x then ρs hj.choose x
      else Term.var x
    -- two blocks that share a name give it the same image
    have hagree : ∀ i j x, blk i x → blk j x → ρs j x = ρs i x := by
      intro i j x hi hj
      by_cases hij : i = j
      · subst hij; rfl
      rcases hi with hi | hi <;> rcases hj with hj | hj
      · have h2 : 2 ≤ (Term.app β us).vars.count x := by
          rw [vars_app, Multiset.count_sum']
          have := Finset.sum_le_sum_of_subset (f := fun l => (us l).vars.count x)
            (Finset.subset_univ ({i, j} : Finset (Fin (S'.arity β))))
          rw [Finset.sum_pair hij] at this
          have := Multiset.one_le_count_iff_mem.2 hi
          have := Multiset.one_le_count_iff_mem.2 hj
          omega
        obtain ⟨y, hy⟩ := hτ x h2
        have e1 := hρ1 i x hi
        have e2 := hρ1 j x hj
        rw [hy] at e1 e2
        rw [e1.eq_var_of_tr, e2.eq_var_of_tr]
      · have := hb x (hsub i x hi); simp only [kk] at hj; omega
      · have := hb x (hsub j x hj); simp only [kk] at hi; omega
      · exact absurd (off_block_eq s (k + I) x hi hj) hij
    have hblk : ∀ i x, x ∈ (Ψ.trTerm (kk i) (us i)).vars → blk i x := by
      intro i x hx
      rw [vars_trTerm, two_nsmul, Multiset.mem_add, Multiset.mem_add, or_self,
        Multiset.mem_Ico] at hx
      exact hx
    have hkey : ∀ i x, blk i x → ρ x = ρs i x := by
      intro i x hx
      have hn : ¬ (k ≤ x ∧ x < k + I) := by
        rintro ⟨h1, h2⟩
        rcases hx with hx | hx
        · have := hb x (hsub i x hx); omega
        · simp only [kk] at hx; omega
      have hj : ∃ j, blk j x := ⟨i, hx⟩
      simp only [ρ]
      rw [dite_eq_right_of_eq_false (eq_false hn), dite_eq_left_of_eq_true (eq_true hj)]
      exact hagree i _ x hx hj.choose_spec
    refine ⟨ρ, fun x hx => ?_, fun x h1 h2 => ?_, ?_⟩
    · obtain ⟨i, -, hi⟩ := Multiset.mem_sum.1 (show x ∈ ∑ i, (us i).vars from hx)
      rw [hkey i x (Or.inl hi)]
      exact hρ1 i x hi
    · by_cases hx : x < k + I
      · refine ⟨f'' ⟨x - k, by omega⟩, ?_⟩
        simp only [ρ]
        rw [dite_eq_left_of_eq_true (eq_true ⟨h1, hx⟩)]
      · have hsz : Ψ.size (Term.app β us) = I + ∑ i, s i := rfl
        have hm : x ∈ Multiset.Ico (k + I) (k + I + ∑ i, s i) :=
          Multiset.mem_Ico.2 ⟨by omega, by omega⟩
        rw [← sum_Ico_off] at hm
        obtain ⟨i, -, hi⟩ := Multiset.mem_sum.1 hm
        rw [Multiset.mem_Ico] at hi
        rw [hkey i x (Or.inr hi)]
        exact hρ2 i x hi.1 hi.2
    · change (Ψ.net β).inst ts'' f'' =
        ((Ψ.net β).inst (fun i => Ψ.trTerm (kk i) (us i)) (fun w => k + w)).bind ρ
      unfold PNet.inst
      rw [Term.bind_bind]
      refine Term.bind_congr fun x _ => ?_
      cases x with
      | inl i =>
        change ts'' i = (Ψ.trTerm (kk i) (us i)).bind ρ
        rw [hρ3 i]
        exact Term.bind_congr fun x hx => (hkey i x (hblk i x hx)).symm
      | inr w =>
        change Term.var (f'' w) = ρ (k + w)
        have hw : k ≤ k + (w : ℕ) ∧ k + (w : ℕ) < k + I := ⟨by omega, by have := w.isLt; omega⟩
        simp only [ρ]
        rw [dite_eq_left_of_eq_true (eq_true hw)]
        congr 2
        exact Fin.ext (by simp)

-- ============================================================================================
-- 2. Main results: translating by a composite
-- ============================================================================================

/-- **Translating by a composite is composing the translations, for trees** (page 80,
"composition of translations is defined in the obvious way"). If `t'` is a translation of `t` by
`Φ` and `t''` a translation of `t'` by `Ψ`, then `t''` is a translation of `t` by `Ψ ∘ Φ`, with
the same names: the internal wires of an instance of `Ψ(Φ(α))` are those of the instance of
`Φ(α)` and those of the instances of the `Ψ(β)` inside it. -/
theorem TermTr.comp
    -- the two translations, `Φ` first
    {Φ : Translation S S'}
    {Ψ : Translation S' S''}
    -- the trees
    {t : Term S ℕ}
    {t' : Term S' ℕ}
    {t'' : Term S'' ℕ}
    -- `t'` translates `t` by `Φ`, and `t''` translates `t'` by `Ψ`
    (h : Φ.TermTr t t')
    (h' : Ψ.TermTr t' t'') :
    (Ψ.comp Φ).TermTr t t'' := by
  induction h generalizing t'' with
  | var x =>
    rw [h'.eq_var_of_tr]
    exact .var x
  | app α ts ts' f hts ih =>
    classical
    let τ : ℕ → Term S' ℕ := fun x =>
      if hx : x < S.arity α then ts' ⟨x, hx⟩
      else if hw : x - S.arity α < (Φ.net α).internal then Term.var (f ⟨x - S.arity α, hw⟩)
      else Term.var x
    have hinst : (Φ.net α).inst ts' f = (Φ.net α).natTree.bind τ := by
      unfold PNet.inst PNet.natTree
      rw [Term.bind_bind]
      refine Term.bind_congr fun x _ => ?_
      cases x with
      | inl i => simp [τ, PNet.enc, i.isLt]
      | inr w => simp [τ, PNet.enc, w.isLt]
    rw [hinst] at h'
    have hport : ∀ i : Fin (S.arity α), (i : ℕ) ∈ (Φ.net α).natTree.vars := fun i => by
      have e := (Φ.net α).count_natTree_enc (.inl i)
      rw [(Φ.net α).port_count] at e
      exact Multiset.one_le_count_iff_mem.1 (le_of_eq e.symm)
    have hwire : ∀ w : Fin (Φ.net α).internal,
        S.arity α + (w : ℕ) ∈ (Φ.net α).natTree.vars := fun w => by
      have e := (Φ.net α).count_natTree_enc (.inr w)
      rw [(Φ.net α).internal_count] at e
      exact Multiset.one_le_count_iff_mem.1 (by
        change 1 ≤ (Φ.net α).natTree.vars.count ((Φ.net α).enc (.inr w)); omega)
    have hτ : ∀ x, 2 ≤ (Φ.net α).natTree.vars.count x → ∃ y, τ x = Term.var y := by
      intro x hx
      by_cases hxn : x < S.arity α
      · have e := (Φ.net α).count_natTree_enc (.inl ⟨x, hxn⟩)
        rw [(Φ.net α).port_count] at e
        have : (Φ.net α).natTree.vars.count x = 1 := e
        omega
      · simp only [τ, hxn, ↓reduceDIte]
        split_ifs
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
    obtain ⟨ρ, h1, h2, h3⟩ := TermTr.bind_inv Ψ τ (Φ.net α).natTree
      (S.arity α + (Φ.net α).internal) t'' (PNet.natTree_lt _) hτ h'
    have hvar : ∀ w : Fin ((Φ.net α).internal + Ψ.size (Φ.net α).natTree),
        ∃ y, ρ (S.arity α + w) = Term.var y := by
      intro w
      by_cases hw : (w : ℕ) < (Φ.net α).internal
      · refine ⟨f ⟨w, hw⟩, ?_⟩
        have e := h1 _ (hwire ⟨w, hw⟩)
        have hτw : τ (S.arity α + w) = Term.var (f ⟨w, hw⟩) := by simp [τ, hw]
        rw [hτw] at e
        exact e.eq_var_of_tr
      · exact h2 _ (by omega) (by have := w.isLt; omega)
    choose g hg using hvar
    have he : t'' = ((Ψ.comp Φ).net α).inst (fun i => ρ i) g := by
      rw [h3, ← natTree_trPNet]
      change _ = (Ψ.trPNet (Φ.net α)).tree.bind _
      unfold PNet.natTree
      rw [Term.bind_bind]
      refine Term.bind_congr fun x _ => ?_
      cases x with
      | inl i => rfl
      | inr w => exact hg w
    rw [he]
    refine TermTr.app α ts _ g fun i => ih i ?_
    have e := h1 _ (hport i)
    have hτi : τ i = ts' i := by simp [τ, i.isLt]
    rwa [hτi] at e

/-- **Translating by a composite is composing the translations, for equations** (page 80). -/
theorem EqTr.comp
    -- the two translations, `Φ` first
    {Φ : Translation S S'}
    {Ψ : Translation S' S''}
    -- the equations
    {e : Sym2 (Term S ℕ)}
    {e' : Sym2 (Term S' ℕ)}
    {e'' : Sym2 (Term S'' ℕ)}
    -- `e'` translates `e` by `Φ`, and `e''` translates `e'` by `Ψ`
    (h : Φ.EqTr e e')
    (h' : Ψ.EqTr e' e'') :
    (Ψ.comp Φ).EqTr e e'' := by
  obtain ⟨a, b, a', b', rfl, rfl, ha, hb⟩ := h
  obtain ⟨a'', b'', rfl, ha', hb'⟩ := EqTr.mk h'
  exact ⟨a, b, a'', b'', rfl, rfl, ha.comp ha', hb.comp hb'⟩

/-- Equation-wise translations compose (page 80). -/
theorem rel_eqTr_comp
    -- the two translations, `Φ` first
    {Φ : Translation S S'}
    {Ψ : Translation S' S''}
    -- the nets
    {N : Net S ℕ}
    {N' : Net S' ℕ}
    {N'' : Net S'' ℕ}
    -- `N'` translates `N` equation by equation by `Φ`, and `N''` translates `N'` by `Ψ`
    (h : Multiset.Rel Φ.EqTr N N')
    (h' : Multiset.Rel Ψ.EqTr N' N'') :
    Multiset.Rel (Ψ.comp Φ).EqTr N N'' := by
  induction h generalizing N'' with
  | zero =>
    rw [Multiset.rel_zero_left.1 h']
    exact Multiset.Rel.zero
  | cons he _ ih =>
    obtain ⟨e'', N₁, he', hN, rfl⟩ := Multiset.rel_cons_left.1 h'
    exact Multiset.Rel.cons (he.comp he') (ih hN)

/-- **Translating by a composite is composing the translations, for nets** (page 80,
"composition of translations is defined in the obvious way"). If `N'` is a translation of `N` by
`Φ` and `N''` a translation of `N'` by `Ψ`, then `N''` is a translation of `N` by `Ψ ∘ Φ`, with
the same names. -/
theorem NetTr.comp
    -- the two translations, `Φ` first
    {Φ : Translation S S'}
    {Ψ : Translation S' S''}
    -- the nets
    {N : Net S ℕ}
    {N' : Net S' ℕ}
    {N'' : Net S'' ℕ}
    -- `N'` translates `N` by `Φ`, and `N''` translates `N'` by `Ψ`
    (h : Φ.NetTr N N')
    (h' : Ψ.NetTr N' N'') :
    (Ψ.comp Φ).NetTr N N'' :=
  ⟨rel_eqTr_comp h.rel h'.rel, h'.linear⟩

end Translation

end INet
