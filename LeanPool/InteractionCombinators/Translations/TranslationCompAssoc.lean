/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Translations.TranslationCompTr
public import LeanPool.InteractionCombinators.Universality.RecursionFree.DecompositionSymmLiteral
public import LeanPool.InteractionCombinators.Universality.RecursionFree.RecursionFreeFig7

/-!
# Composition of translations is associative and respects `Iso` (page 80)

Lafont 1997, Section 1.7, journal page 80, last paragraph: "Composition of translations is defined
in the obvious way." The principal nets are graphs, so the algebra of composition holds up to the
names of internal wires (`PNet.Iso`), symbol by symbol.

Contents, in the order of the file:

1. Auxiliary lemmas on principal nets: `PNet.mem_vars_tree`; `PNet.card_vars_tree`, a principal
   net with `n` ports and `m` internal wires has `n + 2 m` leaves;
   `PNet.iso_of_natTree_eq_bind`, if the tree over `ℕ` of `q` is that of `p` with its leaves
   renamed, the ports kept, then `p` and `q` are the same graph; and its converse
   `PNet.Iso.natTree_eq_bind`.
2. Auxiliary lemmas on translations of a tree: `TermTr.eq_bind_trTerm`, every translation of a
   tree is the canonical one, `trTerm`, with its leaves renamed and the names of the tree kept;
   `port_mem_natTree`; `iso_trPNet_of_termTr`, all translations of a principal net are the same
   graph; `TermTr.of_iso`, translations by symbol-wise `Iso` principal nets are the same.
3. Main results: `Translation.trPNet_iso`, `Translation.comp_iso_right`,
   `Translation.comp_iso_left`, composing respects `Iso` on both sides;
   `Translation.comp_assoc`, `(Θ ∘ Ψ) ∘ Φ = Θ ∘ (Ψ ∘ Φ)`; `Translation.Invertible.comp`, the
   composite of invertible translations is invertible.
-/

@[expose] public section

namespace INet

variable {S S' S'' S''' : Signature}

open Term

-- ============================================================================================
-- 1. Auxiliary lemmas: the leaves of a principal net
-- ============================================================================================

namespace PNet

variable {n : ℕ}

/-- Every port and every internal wire of a principal net occurs in its tree. -/
theorem mem_vars_tree
    -- the principal net
    (p : PNet S n)
    -- a port or an internal wire of it
    (x : Fin n ⊕ Fin p.internal) :
    x ∈ p.tree.vars := by
  rw [← Multiset.count_pos]
  cases x with
  | inl i => rw [p.port_count]; omega
  | inr w => rw [p.internal_count]; omega

/-- **The leaves of a principal net** (page 80): `n` ports, each once, and `m` internal wires,
each twice, so `n + 2 m` leaves. -/
theorem card_vars_tree
    -- the principal net, with `n` ports
    (p : PNet S n) :
    Multiset.card p.tree.vars = n + 2 * p.internal := by
  rw [← Multiset.sum_count_eq_card (s := Finset.univ) (fun a _ => Finset.mem_univ a),
    Fintype.sum_sum_type]
  simp only [p.port_count, p.internal_count, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  ring

/-- **Renaming the leaves of a principal net over `ℕ`** (page 80). If the tree over `ℕ` of `q` is
that of `p` with its names renamed by `g`, and `g` keeps the ports, then `p` and `q` are the same
graph: `g` is a bijection of the internal wires, since both nets have their leaves counted by
`card_vars_tree`. -/
theorem iso_of_natTree_eq_bind
    -- two principal nets with `n` ports
    {p q : PNet S n}
    -- a renaming of the names over `ℕ` that keeps the ports
    (g : ℕ → ℕ)
    (hg : ∀ i < n, g i = i)
    -- the tree over `ℕ` of `q` is that of `p` renamed by `g`
    (h : q.natTree = p.natTree.bind fun x => var (g x)) :
    -- then `p` and `q` are the same graph
    p.Iso q := by
  classical
  have hvq : q.natTree.vars = (p.tree.vars.map p.enc).map g := by
    rw [h, Term.vars_bind_var_map, vars_natTree]
  have hex : ∀ x, ∃ y, q.enc y = g (p.enc x) := by
    intro x
    have hm : g (p.enc x) ∈ q.natTree.vars := by
      rw [hvq]
      exact Multiset.mem_map_of_mem _ (Multiset.mem_map_of_mem _ (p.mem_vars_tree x))
    rw [vars_natTree, Multiset.mem_map] at hm
    obtain ⟨y, -, hy⟩ := hm
    exact ⟨y, hy⟩
  choose F hF using hex
  have htree : q.tree = p.tree.bind fun x => var (F x) := by
    apply Term.bind_var_injective q.enc_injective
    change q.natTree = _
    rw [h, natTree, Term.bind_bind, Term.bind_bind]
    exact Term.bind_congr fun x _ => by
      change var (g (p.enc x)) = var (q.enc (F x))
      rw [hF]
  have hFl : ∀ i, F (.inl i) = .inl i := fun i =>
    q.enc_injective (by rw [hF]; exact hg i i.isLt)
  have hsurj : Function.Surjective F := by
    intro y
    have hm := q.mem_vars_tree y
    rw [htree, Term.vars_bind_var_map, Multiset.mem_map] at hm
    obtain ⟨x, -, hx⟩ := hm
    exact ⟨x, hx⟩
  have hcard : q.internal = p.internal := by
    have e := congrArg Multiset.card (congrArg Term.vars htree)
    rw [Term.vars_bind_var_map, Multiset.card_map, card_vars_tree, card_vars_tree] at e
    omega
  have hbij : Function.Bijective F :=
    (Fintype.bijective_iff_surjective_and_card F).2 ⟨hsurj, by simp [hcard]⟩
  have hr : ∀ w, ∃ v, F (.inr w) = .inr v := by
    intro w
    rcases hw : F (.inr w) with i | v
    · rw [← hFl i] at hw
      exact absurd (hbij.1 hw) (by simp)
    · exact ⟨v, rfl⟩
  choose e he using hr
  have hinj : Function.Injective e := fun w v hwv =>
    Sum.inr_injective (hbij.1 (by rw [he, he, hwv]))
  have ebij : Function.Bijective e :=
    (Fintype.bijective_iff_injective_and_card e).2 ⟨hinj, by simp [hcard]⟩
  refine ⟨Equiv.ofBijective e ebij, ?_⟩
  rw [htree]
  exact Term.bind_congr fun x _ => by
    cases x with
    | inl i => rw [hFl]; rfl
    | inr w => rw [he]; rfl

/-- **`Iso` as a renaming over `ℕ`** (page 80): if `p` and `q` are the same graph, the tree over
`ℕ` of `q` is that of `p` renamed by a map that keeps the ports and every name from
`n + p.internal` on. -/
theorem Iso.natTree_eq_bind
    -- two principal nets with `n` ports that are the same graph
    {p q : PNet S n}
    (h : p.Iso q) :
    -- there is a renaming `g` of the names over `ℕ`
    ∃ g : ℕ → ℕ,
      -- that keeps the ports,
      (∀ i < n, g i = i) ∧
      -- keeps every name from `n + p.internal` on,
      (∀ x, n + p.internal ≤ x → g x = x) ∧
      -- the two nets have as many internal wires,
      p.internal = q.internal ∧
      -- and the tree over `ℕ` of `q` is that of `p` renamed by `g`
      q.natTree = p.natTree.bind fun x => var (g x) := by
  classical
  obtain ⟨e, he⟩ := h
  have hm : p.internal = q.internal := by simpa using Fintype.card_congr e
  let g : ℕ → ℕ := fun x =>
    if hx : n ≤ x ∧ x < n + p.internal then n + (e ⟨x - n, by omega⟩ : ℕ) else x
  have hout : ∀ x, ¬ (n ≤ x ∧ x < n + p.internal) → g x = x := fun x hx => by
    simp only [g]
    split_ifs
    rfl
  have hin : ∀ w : Fin p.internal, g (n + w) = n + e w := fun w => by
    simp only [g]
    split_ifs with hx
    · congr 3
      exact Fin.ext (by simp)
    · exact absurd ⟨by omega, by have := w.isLt; omega⟩ hx
  refine ⟨g, fun i hi => hout i (by omega), fun x hx => hout x (by omega), hm, ?_⟩
  rw [natTree, ← he, natTree, Term.bind_bind, Term.bind_bind]
  refine Term.bind_congr fun x _ => ?_
  cases x with
  | inl i =>
    change var (i : ℕ) = var (g i)
    rw [hout i (by omega)]
  | inr w =>
    change var (n + (e w : ℕ)) = var (g (n + w))
    rw [hin]

end PNet

-- ============================================================================================
-- 2. Auxiliary lemmas: every translation is the canonical one, renamed
-- ============================================================================================

namespace Translation

open PNet

variable {n : ℕ}

/-- **A translation is the canonical one, renamed** (page 80). If `u` is a translation by `Ψ` of a
tree `t` whose names are below `k`, then `u` is `Ψ.trTerm k t` with its leaves renamed by a map
that keeps the names of `t`. -/
theorem TermTr.eq_bind_trTerm
    -- the translation, a tree `t` and a tree `u`
    {Ψ : Translation S' S''}
    {t : Term S' ℕ}
    {u : Term S'' ℕ}
    -- a bound on the names of `t`
    (k : ℕ)
    (hb : ∀ x ∈ t.vars, x < k)
    -- `u` is a translation of `t` by `Ψ`
    (h : Ψ.TermTr t u) :
    -- there is a renaming `g`
    ∃ g : ℕ → ℕ,
      -- that keeps the names of `t`,
      (∀ x ∈ t.vars, g x = x) ∧
      -- and `u` is the canonical translation of `t` renamed by `g`
      u = (Ψ.trTerm k t).bind fun x => Term.var (g x) := by
  classical
  obtain ⟨ρ, h1, h2, h3⟩ := TermTr.bind_inv Ψ Term.var t k u hb (fun x _ => ⟨x, rfl⟩)
    (by rw [Term.bind_var_self]; exact h)
  have hv : ∀ x ∈ t.vars, ρ x = Term.var x := fun x hx => (h1 x hx).eq_var_of_tr
  let g : ℕ → ℕ := fun x => if hx : ∃ y, ρ x = Term.var y then hx.choose else x
  have hg : ∀ x, (∃ y, ρ x = Term.var y) → ρ x = Term.var (g x) := fun x hx => by
    simp only [g]; rw [dite_eq_left_of_eq_true (eq_true hx)]
    exact hx.choose_spec
  refine ⟨g, fun x hx => ?_, ?_⟩
  · have := hg x ⟨x, hv x hx⟩
    rw [hv x hx] at this
    exact (Term.var.inj this).symm
  · rw [h3]
    refine Term.bind_congr fun x hx => hg x ?_
    rw [vars_trTerm, two_nsmul, Multiset.mem_add, Multiset.mem_add, or_self,
      Multiset.mem_Ico] at hx
    rcases hx with hx | hx
    · exact ⟨x, hv x hx⟩
    · exact h2 x hx.1 hx.2

/-- The ports of a principal net are names of its tree over `ℕ`. -/
theorem port_mem_natTree
    -- the principal net
    (p : PNet S' n)
    -- a port
    (i : ℕ)
    (hi : i < n) :
    i ∈ p.natTree.vars := by
  rw [vars_natTree]
  exact Multiset.mem_map_of_mem p.enc (p.mem_vars_tree (.inl ⟨i, hi⟩))

/-- **Two translations of a principal net are the same graph** (page 80). If the tree over `ℕ` of
`q` is a translation by `Ψ` of that of `p`, then `q` is `Ψ(p)` up to the names of its internal
wires. -/
theorem iso_trPNet_of_termTr
    -- the translation
    (Ψ : Translation S' S'')
    -- a principal net and a principal net over the target signature
    (p : PNet S' n)
    (q : PNet S'' n)
    -- the tree over `ℕ` of `q` is a translation by `Ψ` of that of `p`
    (h : Ψ.TermTr p.natTree q.natTree) :
    -- then `Ψ(p)` and `q` are the same graph
    (Ψ.trPNet p).Iso q := by
  obtain ⟨g, hg, he⟩ := TermTr.eq_bind_trTerm (n + p.internal) p.natTree_lt h
  refine iso_of_natTree_eq_bind g (fun i hi => hg i (port_mem_natTree p i hi)) ?_
  rwa [natTree_trPNet]

/-- Translations by symbol-wise `Iso` principal nets are the same: an instance of `Ψ(β)` is an
instance of `Ψ'(β)`, its internal wires renamed through the bijection. -/
theorem TermTr.of_iso
    -- two translations that are the same graph on every symbol
    {Ψ Ψ' : Translation S' S''}
    (hΨ : ∀ β, (Ψ.net β).Iso (Ψ'.net β))
    -- a translation `u` of `t` by `Ψ`
    {t : Term S' ℕ}
    {u : Term S'' ℕ}
    (h : Ψ.TermTr t u) :
    -- is a translation of `t` by `Ψ'`
    Ψ'.TermTr t u := by
  induction h with
  | var x => exact .var x
  | app β ts ts' f _ ih =>
    obtain ⟨e, he⟩ := hΨ β
    have hinst : (Ψ.net β).inst ts' f = (Ψ'.net β).inst ts' fun w => f (e.symm w) := by
      rw [PNet.inst, PNet.inst, ← he, Term.bind_bind]
      exact Term.bind_congr fun x _ => by cases x <;> simp
    rw [hinst]
    exact TermTr.app β ts ts' _ ih

-- ============================================================================================
-- 3. Main results: composition respects `Iso`, is associative, keeps invertibility
-- ============================================================================================

/-- **Translating respects `Iso`** (page 80): the translations by `Ψ` of two principal nets that
are the same graph are the same graph. -/
theorem trPNet_iso
    -- the translation
    (Ψ : Translation S' S'')
    -- two principal nets that are the same graph
    {p q : PNet S' n}
    (h : p.Iso q) :
    -- their translations are the same graph
    (Ψ.trPNet p).Iso (Ψ.trPNet q) := by
  obtain ⟨g, hg, hk, hm, he⟩ := h.natTree_eq_bind
  refine iso_of_natTree_eq_bind g hg ?_
  rw [natTree_trPNet, natTree_trPNet, he,
    trTerm_shift Ψ g p.natTree (n + p.internal) (n + q.internal) fun i => by
      rw [hk _ (by omega)]; omega]

/-- **Composing respects `Iso` on the right** (page 80): if `Φ(α)` and `Φ'(α)` are the same graph
for every `α`, so are `(Ψ ∘ Φ)(α)` and `(Ψ ∘ Φ')(α)`. -/
theorem comp_iso_right
    -- the translation applied second
    (Ψ : Translation S' S'')
    -- two translations applied first, the same graph on every symbol
    {Φ Φ' : Translation S S'}
    (h : ∀ α, (Φ.net α).Iso (Φ'.net α))
    -- a symbol
    (α : S.Sym) :
    -- the two composites are the same graph on `α`
    ((Ψ.comp Φ).net α).Iso ((Ψ.comp Φ').net α) :=
  Ψ.trPNet_iso (h α)

/-- **Composing respects `Iso` on the left** (page 80): if `Ψ(β)` and `Ψ'(β)` are the same graph
for every `β`, so are `(Ψ ∘ Φ)(α)` and `(Ψ' ∘ Φ)(α)`. -/
theorem comp_iso_left
    -- two translations applied second
    {Ψ Ψ' : Translation S' S''}
    -- the translation applied first
    (Φ : Translation S S')
    -- the two translations applied second are the same graph on every symbol
    (h : ∀ β, (Ψ.net β).Iso (Ψ'.net β))
    -- a symbol
    (α : S.Sym) :
    -- the two composites are the same graph on `α`
    ((Ψ.comp Φ).net α).Iso ((Ψ'.comp Φ).net α) :=
  (iso_trPNet_of_termTr Ψ' (Φ.net α) (Ψ.trPNet (Φ.net α))
    (TermTr.of_iso h (termTr_trPNet Ψ (Φ.net α)))).symm

/-- **Composition is associative** (page 80): `((Θ ∘ Ψ) ∘ Φ)(α)` and `(Θ ∘ (Ψ ∘ Φ))(α)` are the
same graph. A translation by `Ψ` followed by a translation by `Θ` is a translation by `Θ ∘ Ψ`
(`TermTr.comp`), and all translations of a principal net are the same graph. -/
theorem comp_assoc
    -- the three translations, `Φ` applied first
    (Θ : Translation S'' S''')
    (Ψ : Translation S' S'')
    (Φ : Translation S S')
    -- a symbol
    (α : S.Sym) :
    -- the two ways of composing them are the same graph on `α`
    (((Θ.comp Ψ).comp Φ).net α).Iso ((Θ.comp (Ψ.comp Φ)).net α) :=
  iso_trPNet_of_termTr (Θ.comp Ψ) (Φ.net α) _
    (TermTr.comp (termTr_trPNet Ψ (Φ.net α)) (termTr_trPNet Θ (Ψ.trPNet (Φ.net α))))

/-- **The composite of invertible translations is invertible** (page 80), with inverse
`Φ⁻¹ ∘ Ψ⁻¹`: `(Φ⁻¹ ∘ Ψ⁻¹) ∘ (Ψ ∘ Φ) = Φ⁻¹ ∘ (Ψ⁻¹ ∘ Ψ) ∘ Φ = Φ⁻¹ ∘ Φ = id`, and symmetrically. -/
theorem Invertible.comp
    -- two invertible translations, `Φ` applied first
    {Φ : Translation S S'}
    {Ψ : Translation S' S''}
    (hΦ : Φ.Invertible)
    (hΨ : Ψ.Invertible) :
    -- their composite is invertible
    (Ψ.comp Φ).Invertible := by
  obtain ⟨Φi, hΦ1, hΦ2⟩ := hΦ
  obtain ⟨Ψi, hΨ1, hΨ2⟩ := hΨ
  -- `B ∘ (A ∘ C) = B ∘ C` when `A = id` up to `Iso`
  have cancel : ∀ {T₁ T₂ T₃ : Signature} (B : Translation T₂ T₃) (A : Translation T₂ T₂)
      (C : Translation T₁ T₂), (∀ β, (A.net β).Iso ((Translation.id T₂).net β)) →
      ∀ γ, (((B.comp A).comp C).net γ).Iso ((B.comp C).net γ) := by
    intro T₁ T₂ T₃ B A C hA γ
    have h1 : ∀ β, ((B.comp A).net β).Iso (B.net β) := fun β =>
      (comp_iso_right B hA β).trans (comp_id B β)
    exact comp_iso_left C h1 γ
  refine ⟨Φi.comp Ψi, fun α => ?_, fun α => ?_⟩
  · -- `(Φ⁻¹ ∘ Ψ⁻¹) ∘ (Ψ ∘ Φ) ≅ ((Φ⁻¹ ∘ Ψ⁻¹) ∘ Ψ) ∘ Φ ≅ (Φ⁻¹ ∘ (Ψ⁻¹ ∘ Ψ)) ∘ Φ ≅ Φ⁻¹ ∘ Φ`
    refine (comp_assoc (Φi.comp Ψi) Ψ Φ α).symm.trans ?_
    refine (comp_iso_left Φ (fun β => comp_assoc Φi Ψi Ψ β) α).trans ?_
    exact (cancel Φi (Ψi.comp Ψ) Φ hΨ1 α).trans (hΦ1 α)
  · refine (comp_assoc (Ψ.comp Φ) Φi Ψi α).symm.trans ?_
    refine (comp_iso_left Ψi (fun β => comp_assoc Ψ Φ Φi β) α).trans ?_
    exact (cancel Ψ (Φ.comp Φi) Ψi hΦ2 α).trans (hΨ2 α)

end Translation

end INet
