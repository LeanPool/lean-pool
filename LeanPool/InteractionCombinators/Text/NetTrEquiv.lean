/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Text.RenameMany
public import LeanPool.InteractionCombinators.Core.Translation
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas

/-!
# Two translations of a net are the same graph

Lafont 1997, Section 1.7, page 80: a translation of a net replaces every cell by an instance of the
principal net of its symbol. The internal wires of the instances get new names, and the choice of
these names does not matter: two translations of the same net are equivalent
(`Translation.NetTr.equiv`).

The proof pairs the two translations position by position. Where the first translation has the
name `x` and the second the name `y`, the paired net has the name `(x, y)`. A name of the source
net becomes a pair `(x, x)`, and an internal wire of an instance a pair `(f w, g w)` occurring
twice. Linearity of both translations makes each projection injective on the names of the paired
net, so the renaming that sends `x` to `y` is a renaming of the first translation into the second
that fixes its free ports (`Net.equiv_bind_var`).

Concrete checks on translations whose principal net has an internal wire are in
`NetTrEquivCheck.lean`.

Contents, in the order of the file:

1. Definitions: `Zip.proj`, the projection of a net of pairs of names, and `Zip.EvenOff`, every
   off-diagonal pair occurs an even number of times.
2. Auxiliary lemmas on nets of pairs: `Multiset.count_add_count_le_count_map`, `Zip.injOn` (a
   linear projection is injective on the names), `Zip.equiv` (the two projections are the same
   graph).
3. Auxiliary lemmas: pairing two translations. `Translation.TermTr.zip` (of a tree),
   `Translation.EqTr.zip` (of an equation), `Translation.rel_zip` (of a net).
4. Main result: `Translation.NetTr.equiv`, two translations of a net are the same graph.
-/

@[expose] public section

namespace INet

variable {S S' : Signature}

open Term

-- ============================================================================================
-- 1. Definitions
-- ============================================================================================

namespace Zip

/-- The projection of a net of pairs of names: every pair `p` replaced by `g p`. -/
abbrev proj
    -- the projection of a pair of names
    (g : ℕ × ℕ → ℕ)
    -- the net of pairs
    (Z : Net S (ℕ × ℕ)) :
    Net S ℕ :=
  Z.bind fun p => var (g p)

/-- Every pair of distinct names occurs an even number of times. -/
def EvenOff
    -- the names of a net of pairs
    (m : Multiset (ℕ × ℕ)) :
    Prop :=
  ∀ p : ℕ × ℕ, p.1 ≠ p.2 → Even (m.count p)

end Zip

-- ============================================================================================
-- 2. Auxiliary lemmas on nets of pairs
-- ============================================================================================

/-- In a multiset, two distinct elements with the same image together occur at most as often as
their common image in the image multiset. -/
theorem _root_.Multiset.count_add_count_le_count_map
    -- the types, with decidable equality
    {α β : Type}
    [DecidableEq α]
    [DecidableEq β]
    -- the map and the multiset
    (g : α → β)
    (s : Multiset α)
    -- two distinct elements with the same image
    {p q : α}
    (hpq : p ≠ q)
    (hg : g p = g q) :
    s.count p + s.count q ≤ (s.map g).count (g p) := by
  rw [Multiset.count_map, Multiset.count_eq_card_filter_eq, Multiset.count_eq_card_filter_eq,
    ← Multiset.card_add, Multiset.filter_add_filter]
  have h0 : s.filter (fun a => p = a ∧ q = a) = 0 :=
    Multiset.filter_eq_nil.2 fun a _ h => hpq (h.1.trans h.2.symm)
  rw [h0, add_zero]
  refine Multiset.card_le_card (Multiset.monotone_filter_right s fun a h => ?_)
  rcases h with rfl | rfl
  · rfl
  · exact hg

namespace Zip

/-- In a net of pairs where every off-diagonal pair occurs an even number of times, a projection
that is linear is injective on the names: two distinct pairs with the same image would give that
image three or four occurrences. -/
theorem injOn
    -- the net of pairs
    {Z : Net S (ℕ × ℕ)}
    -- a projection that sends each diagonal pair `(x, x)` to `x`
    {g : ℕ × ℕ → ℕ}
    (hg : ∀ x, g (x, x) = x)
    -- the projection of `Z` is linear
    (hlin : (proj g Z).Linear)
    -- every off-diagonal pair occurs an even number of times in `Z`
    (hev : EvenOff Z.vars) :
    Set.InjOn g {p | p ∈ Z.vars} := by
  intro p hp q hq hpq
  by_contra hne
  have c := Multiset.count_add_count_le_count_map g Z.vars hne hpq
  rw [← Net.vars_bind_var (S := S)] at c
  have hl : (Net.vars (Z.bind fun x => var (g x))).count (g p) ≤ 2 := hlin (g p)
  have hp1 := Multiset.one_le_count_iff_mem.2 (show p ∈ Z.vars from hp)
  have hq1 := Multiset.one_le_count_iff_mem.2 (show q ∈ Z.vars from hq)
  by_cases hp' : p.1 = p.2
  · by_cases hq' : q.1 = q.2
    · apply hne
      have e1 : g p = p.1 := by rw [← hg p.1]; congr 1; exact Prod.ext rfl hp'.symm
      have e2 : g q = q.1 := by rw [← hg q.1]; congr 1; exact Prod.ext rfl hq'.symm
      have h1 : p.1 = q.1 := e1.symm.trans (hpq.trans e2)
      exact Prod.ext h1 (hp'.symm.trans (h1.trans hq'))
    · obtain ⟨k, hk⟩ := hev q hq'
      omega
  · obtain ⟨k, hk⟩ := hev p hp'
    omega

/-- **Equivalence of the two projections of a net of pairs.** If both projections are linear and
every off-diagonal pair occurs an even number of times, the two projections are the same graph:
the second is a renaming of the first that keeps its names distinct and fixes its free ports. -/
theorem equiv
    -- the net of pairs, with both projections linear
    {Z : Net S (ℕ × ℕ)}
    (h₁ : (proj Prod.fst Z).Linear)
    (h₂ : (proj Prod.snd Z).Linear)
    -- every off-diagonal pair occurs an even number of times in `Z`
    (hev : EvenOff Z.vars) :
    Equiv (proj Prod.fst Z) (proj Prod.snd Z) := by
  classical
  have i₁ := injOn (fun _ => rfl) h₁ hev
  have i₂ := injOn (fun _ => rfl) h₂ hev
  let f : ℕ → ℕ := fun y => if h : ∃ p ∈ Z.vars, p.1 = y then (Classical.choose h).2 else y
  have hf : ∀ p ∈ Z.vars, f p.1 = p.2 := by
    intro p hp
    have h : ∃ q ∈ Z.vars, q.1 = p.1 := ⟨p, hp, rfl⟩
    have hc := Classical.choose_spec h
    change (if h : ∃ q ∈ Z.vars, q.1 = p.1 then (Classical.choose h).2 else p.1) = p.2
    rw [dite_eq_left_of_eq_true (eq_true h), i₁ hc.1 hp hc.2]
  have hv : (proj Prod.fst Z).vars = Z.vars.map Prod.fst := Net.vars_bind_var _ _
  have E := Net.equiv_bind_var h₁ f ?_ ?_
  · refine E.trans (Equiv.of_eq ?_)
    rw [Net.bind_bind]
    exact Net.bind_congr fun p hp => by simp [hf p hp]
  · intro y hy y' hy' heq
    have hy : y ∈ (proj Prod.fst Z).vars := hy
    have hy' : y' ∈ (proj Prod.fst Z).vars := hy'
    rw [hv] at hy hy'
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hy'
    rw [hf p hp, hf q hq] at heq
    rw [i₂ hp hq heq]
  · intro y hy
    have hym : y ∈ (proj Prod.fst Z).vars := Multiset.one_le_count_iff_mem.1 (by omega)
    rw [hv] at hym hy
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hym
    rw [Multiset.count_map_eq_count _ _ i₁ p hp] at hy
    rw [hf p hp]
    by_contra hne
    obtain ⟨k, hk⟩ := hev p (Ne.symm hne)
    omega

end Zip

-- ============================================================================================
-- 3. Auxiliary lemmas: pairing two translations
-- ============================================================================================

namespace Translation

variable {Φ : Translation S S'}

/-- **Two translations of a tree, paired.** If `t₁` and `t₂` are translations of the same tree,
there is a tree over pairs of names whose two projections are `t₁` and `t₂`, in which every
off-diagonal pair occurs an even number of times: the names of the source tree are paired with
themselves, and the internal wires of the instances (two ends each) with each other. (Lafont 1997,
Section 1.7, page 80.) -/
theorem TermTr.zip
    -- the source tree and two of its translations
    {t : Term S ℕ}
    {t₁ t₂ : Term S' ℕ}
    (h₁ : Φ.TermTr t t₁)
    (h₂ : Φ.TermTr t t₂) :
    -- there is a tree `z` over pairs of names such that
    ∃ z : Term S' (ℕ × ℕ),
      -- its first projection is `t₁`,
      z.bind (fun p => Term.var p.1) = t₁ ∧
      -- its second projection is `t₂`,
      z.bind (fun p => Term.var p.2) = t₂ ∧
      -- and every off-diagonal pair occurs in it an even number of times
      Zip.EvenOff z.vars := by
  induction h₁ generalizing t₂ with
  | var x =>
    cases h₂
    refine ⟨Term.var (x, x), rfl, rfl, fun p hp => ?_⟩
    have : p ≠ (x, x) := fun h => hp (by rw [h])
    simp [this]
  | app α ts ts' f h ih =>
    cases h₂ with
    | app _ _ ts₂ g hh =>
      choose zs hz₁ hz₂ hze using fun i => ih i (hh i)
      refine ⟨(Φ.net α).tree.bind (Sum.elim zs fun w => Term.var (f w, g w)), ?_, ?_, ?_⟩
      · rw [Term.bind_bind, PNet.inst]
        congr 1
        funext q
        cases q with
        | inl i => exact hz₁ i
        | inr w => rfl
      · rw [Term.bind_bind, PNet.inst]
        congr 1
        funext q
        cases q with
        | inl i => exact hz₂ i
        | inr w => rfl
      · intro p hp
        rw [Term.vars_bind, Multiset.count_bind_fintype, Fintype.sum_sum_type]
        simp only [(Φ.net α).port_count, (Φ.net α).internal_count, one_mul, Sum.elim_inl,
          Sum.elim_inr]
        refine Even.add (Finset.even_sum _ fun i _ => hze i p hp) ?_
        rw [← Finset.mul_sum]
        exact even_two_mul _

/-- Two translations of an equation, paired (Lafont 1997, Section 1.7, page 80). -/
theorem EqTr.zip
    -- the source equation and two of its translations
    {e : Sym2 (Term S ℕ)}
    {e₁ e₂ : Sym2 (Term S' ℕ)}
    (h₁ : Φ.EqTr e e₁)
    (h₂ : Φ.EqTr e e₂) :
    -- there is an equation `z` over pairs of names such that
    ∃ z : Sym2 (Term S' (ℕ × ℕ)),
      -- its first projection is `e₁`,
      z.map (Term.bind fun p => Term.var p.1) = e₁ ∧
      -- its second projection is `e₂`,
      z.map (Term.bind fun p => Term.var p.2) = e₂ ∧
      -- and every off-diagonal pair occurs in it an even number of times
      Zip.EvenOff (eqVars z) := by
  obtain ⟨a, b, a₁, b₁, rfl, rfl, ha₁, hb₁⟩ := h₁
  obtain ⟨c, d, c₂, d₂, he, rfl, hc₂, hd₂⟩ := h₂
  have key : ∀ {a b : Term S ℕ} {a₁ b₁ a₂ b₂ : Term S' ℕ}, Φ.TermTr a a₁ → Φ.TermTr b b₁ →
      Φ.TermTr a a₂ → Φ.TermTr b b₂ →
      ∃ z : Sym2 (Term S' (ℕ × ℕ)), z.map (Term.bind fun p => Term.var p.1) = s(a₁, b₁) ∧
        z.map (Term.bind fun p => Term.var p.2) = s(a₂, b₂) ∧ Zip.EvenOff (eqVars z) := by
    intro a b a₁ b₁ a₂ b₂ ha₁ hb₁ ha₂ hb₂
    obtain ⟨za, za₁, za₂, zae⟩ := TermTr.zip ha₁ ha₂
    obtain ⟨zb, zb₁, zb₂, zbe⟩ := TermTr.zip hb₁ hb₂
    refine ⟨s(za, zb), by simp [za₁, zb₁], by simp [za₂, zb₂], fun p hp => ?_⟩
    simp only [eqVars_mk, Multiset.count_add]
    exact (zae p hp).add (zbe p hp)
  rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact key ha₁ hb₁ hc₂ hd₂
  · obtain ⟨z, z₁, z₂, ze⟩ := key ha₁ hb₁ hd₂ hc₂
    exact ⟨z, z₁, z₂.trans Sym2.eq_swap, ze⟩

/-- Two translations of a net, paired equation by equation (Lafont 1997, Section 1.7,
page 80). -/
theorem rel_zip
    -- the source net and two nets related to it equation by equation by translation
    {N : Net S ℕ}
    {N₁ N₂ : Net S' ℕ}
    (h₁ : Multiset.Rel Φ.EqTr N N₁)
    (h₂ : Multiset.Rel Φ.EqTr N N₂) :
    -- there is a net `Z` over pairs of names such that
    ∃ Z : Net S' (ℕ × ℕ),
      -- its first projection is `N₁`,
      Zip.proj Prod.fst Z = N₁ ∧
      -- its second projection is `N₂`,
      Zip.proj Prod.snd Z = N₂ ∧
      -- and every off-diagonal pair occurs in it an even number of times
      Zip.EvenOff Z.vars := by
  induction N using Multiset.induction_on generalizing N₁ N₂ with
  | empty =>
    rw [Multiset.rel_zero_left] at h₁ h₂
    subst h₁ h₂
    exact ⟨0, rfl, rfl, fun p _ => by simp⟩
  | cons e N ih =>
    obtain ⟨e₁, N₁', he₁, hN₁, rfl⟩ := Multiset.rel_cons_left.1 h₁
    obtain ⟨e₂, N₂', he₂, hN₂, rfl⟩ := Multiset.rel_cons_left.1 h₂
    obtain ⟨z, z₁, z₂, ze⟩ := EqTr.zip he₁ he₂
    obtain ⟨Z, Z₁, Z₂, Ze⟩ := ih hN₁ hN₂
    refine ⟨z ::ₘ Z, ?_, ?_, fun p hp => ?_⟩
    · simp only [Zip.proj, Net.bind, Multiset.map_cons] at Z₁ ⊢
      rw [Z₁, ← z₁]
    · simp only [Zip.proj, Net.bind, Multiset.map_cons] at Z₂ ⊢
      rw [Z₂, ← z₂]
    · rw [Net.vars_cons, Multiset.count_add]
      exact (ze p hp).add (Ze p hp)

-- ============================================================================================
-- 4. Main result: two translations of a net are the same graph
-- ============================================================================================

/-- **Two translations of a net are the same graph.** If `N₁` and `N₂` are translations of the net
`N`, they differ only by the names of the internal wires of the instances, and `N₁` is equivalent
to `N₂`. (Lafont 1997, Section 1.7, page 80: the translation of a net is defined up to the names
of the new wires.) -/
theorem NetTr.equiv
    -- the translation
    {Φ : Translation S S'}
    -- the source net and two of its translations
    {N : Net S ℕ}
    {N₁ N₂ : Net S' ℕ}
    (h₁ : Φ.NetTr N N₁)
    (h₂ : Φ.NetTr N N₂) :
    Equiv N₁ N₂ := by
  obtain ⟨Z, rfl, rfl, hev⟩ := rel_zip h₁.rel h₂.rel
  exact Zip.equiv h₁.linear h₂.linear hev

end Translation

end INet
