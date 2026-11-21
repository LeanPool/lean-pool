/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.RecursionFree.PlugTr

/-!
# The end of Fig. 7 with any translated trees is a translation of the plugged rule (pages 85–86, 90)

Lafont 1997, Section 2.4, journal page 86 (end of Fig. 7), and page 90 for Fig. 10, where the same
argument is left to the reader. `netTr_plug_gamma` (`PlugTr.lean`) is stated for the trees
`gammaPort Φ φ k₀ p`, the translations of the trees of `φ` with their new wires numbered in one
fixed way. In Fig. 10 the trees reached after the copies of `!Γ` are extracted are translations
of the same trees with new wires named by the reduction (`codeGamma_extract`). Here the trees are
any translations.

Contents, in the order of the file:

1. Definition: `plugTermTarget σ tφ tψ xs ys`, the net at the end of Fig. 7 for any trees `tφ`,
   `tψ`.
2. Auxiliary lemma: `plugTarget_eq_plugTermTarget`, `plugTarget` is the case
   `tφ = gammaPort Φ φ k₀`, `tψ = gammaPort Φ ψ k₁`.
3. Main results: `netTr_plug_termTr`, **`plugTermTarget` is, up to wires, a translation of an
   instance of `Rule.plug φ ψ σ`**, as soon as `tφ p` translates `gammaTree φ k₀ p` and `tψ q`
   translates `gammaTree ψ k₁ q`; and `netTr_plug_gamma'`, `netTr_plug_gamma` again, from
   `netTr_plug_termTr`.
-/

@[expose] public section

namespace INet.Comb

open Term Translation ExpandedIso

variable {S : Signature}

-- ============================================================================================
-- 1. Definition
-- ============================================================================================

/-- **The net at the end of Fig. 7, for any trees** (Lafont 1997, page 86; page 90 for Fig. 10):
the name `xs p` against the tree `tφ (.inl p)`, the name `ys q` against `tψ (.inl q)`, and the
tree `tφ (.inr l)` at the middle port `l` against the tree `tψ (.inr (σ l))`. -/
noncomputable def plugTermTarget
    -- the numbers of ports of the two sides and of middle wires
    {a b k : ℕ}
    -- the permutation of the middle wires
    (σ : Equiv.Perm (Fin k))
    -- the trees of the two sides, on their free ports (`.inl`) and middle ports (`.inr`)
    (tφ : Fin a ⊕ Fin k → Term sig ℕ)
    (tψ : Fin b ⊕ Fin k → Term sig ℕ)
    -- the names of the free ports of the two sides
    (xs : Fin a → ℕ)
    (ys : Fin b → ℕ) :
    CNet :=
  -- the free ports of the first side,
  (Finset.univ.val.map fun p : Fin a => s(var (xs p), tφ (.inl p))) +
    -- the free ports of the second side,
    (Finset.univ.val.map fun q : Fin b => s(var (ys q), tψ (.inl q))) +
    -- and the middle port `l` of the first side against the port `σ l` of the second
    (Finset.univ.val.map fun l : Fin k => s(tφ (.inr l), tψ (.inr (σ l))))

-- ============================================================================================
-- 2. Auxiliary lemma: the net of `PlugTr.lean` is a case
-- ============================================================================================

/-- `plugTarget` (page 86) is `plugTermTarget` with the trees `gammaPort` of `[φ]` and `[ψ]`. -/
theorem plugTarget_eq_plugTermTarget
    -- the translation
    (Φ : Translation S sig)
    -- the two sides, with `k` middle wires, and the permutation of the middle wires
    {a b k : ℕ}
    (φ : Rule S a k)
    (ψ : Rule S b k)
    (σ : Equiv.Perm (Fin k))
    -- the offsets of the internal wires of the two sides
    (k₀ k₁ : ℕ)
    -- the names of the free ports
    (xs : Fin a → ℕ)
    (ys : Fin b → ℕ) :
    plugTarget Φ φ ψ σ k₀ k₁ xs ys =
      plugTermTarget σ (gammaPort Φ φ k₀) (gammaPort Φ ψ k₁) xs ys := rfl

-- ============================================================================================
-- 3. Main results: a translation of the plugged rule
-- ============================================================================================

/-- **The net at the end of Fig. 7, with any translated trees, is a translation of the plugged
rule** (Lafont 1997, page 86; the plugged rule, page 85; Fig. 10, page 90). For linear sides `φ`,
`ψ` in expanded form, any permutation `σ` of the middle wires and any trees `tφ p`, `tψ q` that are
translations of the trees `gammaTree φ k₀ p`, `gammaTree ψ k₁ q`, if `plugTermTarget` is linear
then it is, up to wires, a translation of an instance of `Rule.plug φ ψ σ` with the names `xs` on
the ports of `φ` and `ys` on those of `ψ`.

The internal wire `w` of `φ` is named `k₀ + w`, that of `ψ` is named `k₁ + w`, as in `gammaTree`;
the middle wire `l` gets a fresh name `B + l`, removed at the end (`equiv_contract_map`). -/
theorem netTr_plug_termTr
    -- the translation
    (Φ : Translation S sig)
    -- the two sides, with `k` middle wires, both linear and in expanded form
    {a b k : ℕ}
    {φ : Rule S a k}
    {ψ : Rule S b k}
    (hφe : φ.Expanded)
    (hφl : φ.Linear)
    (hψe : ψ.Expanded)
    (hψl : ψ.Linear)
    -- the permutation of the middle wires
    (σ : Equiv.Perm (Fin k))
    -- the offsets of the internal wires of the two sides
    (k₀ k₁ : ℕ)
    -- the trees, translations of the trees of the two sides
    (tφ : Fin a ⊕ Fin k → Term sig ℕ)
    (tψ : Fin b ⊕ Fin k → Term sig ℕ)
    (hφ : ∀ p, Φ.TermTr (gammaTree φ k₀ p) (tφ p))
    (hψ : ∀ q, Φ.TermTr (gammaTree ψ k₁ q) (tψ q))
    -- the names of the free ports
    (xs : Fin a → ℕ)
    (ys : Fin b → ℕ)
    -- the net at the end of Fig. 7 is linear
    (hlin : Net.Linear (plugTermTarget σ tφ tψ xs ys)) :
    -- there are names `h` of the internal wires of the plugged rule and a net `N'` such that
    ∃ (h : Fin (Rule.plug φ ψ σ).internal → ℕ) (N' : CNet),
      -- `N'` is a translation of the instance of the plugged rule with these names,
      Φ.NetTr ((Rule.plug φ ψ σ).inst (fun i => .var (xs i)) (fun j => .var (ys j)) h) N' ∧
      -- and `N'` is the same graph as the net at the end of Fig. 7
      Equiv N' (plugTermTarget σ tφ tψ xs ys) := by
  set B := (plugTermTarget σ tφ tψ xs ys).vars.sup + 1 with hB
  let h : Fin (k + φ.internal + ψ.internal) → ℕ := fun i =>
    if (i : ℕ) < k then B + i else if (i : ℕ) < k + φ.internal then k₀ + (i - k)
    else k₁ + (i - (k + φ.internal))
  let Mφ : Fin a ⊕ Fin k → ℕ := Sum.elim xs fun l => B + l
  let Mψ : Fin b ⊕ Fin k → ℕ := Sum.elim ys fun l => B + (σ.symm l : ℕ)
  let G : Fin a ⊕ Fin b ⊕ Fin (k + φ.internal + ψ.internal) → Term S ℕ :=
    Sum.elim (fun i => .var (xs i)) (Sum.elim (fun j => .var (ys j)) fun i => .var (h i))
  -- the instance, equation by equation
  have hinst : (Rule.plug φ ψ σ).inst (fun i => .var (xs i)) (fun j => .var (ys j)) h =
      (Finset.univ.val.map fun p => s(var (Mφ p), gammaTree φ k₀ p)) +
        (Finset.univ.val.map fun q => s(var (Mψ q), gammaTree ψ k₁ q)) := by
    change Net.bind G (φ.net.bind (fun x => var (Rule.plugL x)) +
      ψ.net.bind (fun x => var (Rule.plugR σ x))) = _
    rw [show ∀ A C : Net S (Fin a ⊕ Fin b ⊕ Fin (k + φ.internal + ψ.internal)),
        Net.bind G (A + C) = Net.bind G A + Net.bind G C from
        fun A C => Multiset.map_add _ _ _, Net.bind_bind, Net.bind_bind]
    congr 1
    · refine bind_expanded hφe hφl _ Mφ k₀ ?_ ?_
      · rintro (i | l)
        · rfl
        · simp [port, Rule.plugL, G, h, Mφ]
      · intro w
        simp only [Rule.plugL, Term.bind, G, Sum.elim_inr, h, Fin.val_castAdd, Fin.val_natAdd]
        split_ifs <;> first | omega | (congr 1; omega)
    · refine bind_expanded hψe hψl _ Mψ k₁ ?_ ?_
      · rintro (j | l)
        · rfl
        · simp [port, Rule.plugR, G, h, Mψ]
      · intro w
        simp only [Rule.plugR, Term.bind, G, Sum.elim_inr, h, Fin.val_natAdd]
        split_ifs <;> first | omega | (congr 1; omega)
  have hrel : Multiset.Rel Φ.EqTr
      ((Rule.plug φ ψ σ).inst (fun i => .var (xs i)) (fun j => .var (ys j)) h)
      ((Finset.univ.val.map fun p => s(var (Mφ p), tφ p)) +
        (Finset.univ.val.map fun q => s(var (Mψ q), tψ q))) := by
    rw [hinst]
    refine Multiset.Rel.add ?_ ?_
    · refine Multiset.rel_map.2 (Multiset.rel_refl_of_refl_on fun p _ => ?_)
      exact ⟨_, _, _, _, rfl, rfl, TermTr.var _, hφ p⟩
    · refine Multiset.rel_map.2 (Multiset.rel_refl_of_refl_on fun q _ => ?_)
      exact ⟨_, _, _, _, rfl, rfl, TermTr.var _, hψ q⟩
  -- the same net, arranged for the removal of the middle wires
  have hT : (Finset.univ.val.map fun p => s(var (Mφ p), tφ p)) +
      (Finset.univ.val.map fun q => s(var (Mψ q), tψ q)) =
      (Finset.univ.val.map fun l : Fin k => s(tφ (.inr l), var (B + (l : ℕ)))) +
        (Finset.univ.val.map fun l : Fin k => s(var (B + (l : ℕ)), tψ (.inr (σ l)))) +
        ((Finset.univ.val.map fun p : Fin a => s(var (xs p), tφ (.inl p))) +
          (Finset.univ.val.map fun q : Fin b => s(var (ys q), tψ (.inl q)))) := by
    have h1 : (Finset.univ.val.map fun p => s(var (Mφ p), tφ p)) =
        (Finset.univ.val.map fun p : Fin a => s(var (xs p), tφ (.inl p))) +
          Finset.univ.val.map fun l : Fin k => s(tφ (.inr l), var (B + (l : ℕ))) := by
      rw [map_univ_sum]
      congr 1
      exact Multiset.map_congr rfl fun l _ => Sym2.eq_swap
    have h2 : (Finset.univ.val.map fun q => s(var (Mψ q), tψ q)) =
        (Finset.univ.val.map fun q : Fin b => s(var (ys q), tψ (.inl q))) +
          Finset.univ.val.map fun l : Fin k => s(var (B + (l : ℕ)), tψ (.inr (σ l))) := by
      rw [map_univ_sum]
      congr 1
      conv_lhs => rw [← Multiset.map_univ_val_equiv σ]
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun l _ => ?_
      simp [Mψ]
    rw [h1, h2]
    ms
  -- linearity: the middle wires are fresh
  have hlin' : Net.Linear
      ((Finset.univ.val.map fun l : Fin k => s(tφ (.inr l), var (B + (l : ℕ)))) +
        (Finset.univ.val.map fun l : Fin k => s(var (B + (l : ℕ)), tψ (.inr (σ l)))) +
        ((Finset.univ.val.map fun p : Fin a => s(var (xs p), tφ (.inl p))) +
          (Finset.univ.val.map fun q : Fin b => s(var (ys q), tψ (.inl q))))) := by
    refine hlin.add_fresh (Finset.univ.val.map fun l : Fin k => B + (l : ℕ)) ?_ ?_ ?_
    · exact Finset.univ.nodup.map fun x y hxy => Fin.ext (by simpa using hxy)
    · intro x hx hmem
      obtain ⟨l, -, rfl⟩ := Multiset.mem_map.1 hx
      have := Multiset.le_sup hmem
      omega
    · simp only [plugTermTarget, Net.vars_add, vars_map_net, eqVars_mk, vars_var,
        Multiset.bind_add, Multiset.bind_singleton]
      abel
  have E := equiv_contract_map Finset.univ.val (fun l : Fin k => B + (l : ℕ))
    (fun l => tφ (.inr l)) (fun l => tψ (.inr (σ l))) _ hlin'
  refine ⟨h, _, ⟨hrel, hlin'.cast hT.symm⟩, (Equiv.of_eq hT).trans (E.trans (Equiv.of_eq ?_))⟩
  simp only [plugTermTarget]
  ms

/-- **`netTr_plug_gamma` from `netTr_plug_termTr`** (Lafont 1997, page 86): the trees `gammaPort`
of `[φ]` and `[ψ]` are translations of the trees of `φ` and `ψ` (`termTr_trTerm`), so the net
`plugTarget` at the end of Fig. 7 is, up to wires, a translation of an instance of the plugged
rule. -/
theorem netTr_plug_gamma'
    -- the translation
    (Φ : Translation S sig)
    -- the two sides, with `k` middle wires, both linear and in expanded form
    {a b k : ℕ}
    {φ : Rule S a k}
    {ψ : Rule S b k}
    (hφe : φ.Expanded)
    (hφl : φ.Linear)
    (hψe : ψ.Expanded)
    (hψl : ψ.Linear)
    -- the permutation of the middle wires
    (σ : Equiv.Perm (Fin k))
    -- the offsets of the internal wires of the two sides
    (k₀ k₁ : ℕ)
    -- the names of the free ports
    (xs : Fin a → ℕ)
    (ys : Fin b → ℕ)
    -- the net `plugTarget` at the end of Fig. 7 is linear
    (hlin : Net.Linear (plugTarget Φ φ ψ σ k₀ k₁ xs ys)) :
    -- there are names `h` of the internal wires of the plugged rule and a net `N'` such that
    ∃ (h : Fin (Rule.plug φ ψ σ).internal → ℕ) (N' : CNet),
      -- `N'` is a translation of the instance of the plugged rule with these names,
      Φ.NetTr ((Rule.plug φ ψ σ).inst (fun i => .var (xs i)) (fun j => .var (ys j)) h) N' ∧
      -- and `N'` is the same graph as `plugTarget`
      Equiv N' (plugTarget Φ φ ψ σ k₀ k₁ xs ys) := by
  rw [plugTarget_eq_plugTermTarget] at hlin ⊢
  exact netTr_plug_termTr Φ hφe hφl hψe hψl σ k₀ k₁ (gammaPort Φ φ k₀) (gammaPort Φ ψ k₁)
    (fun p => Φ.termTr_trTerm _ _) (fun q => Φ.termTr_trTerm _ _) xs ys hlin

end INet.Comb
