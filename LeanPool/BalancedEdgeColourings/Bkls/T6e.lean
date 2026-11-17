/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.T6d
public import LeanPool.BalancedEdgeColourings.Bkls.TwoCol

/-!
# Theorem 6, part (e): the colour replacing `2` at a vertex, and the orientation of short pairs

The recoloured edges of colours `0, 1` use the colours `0, 1, 3` (`emb`); `Aset col01 x` is the
set they show at `x`. At a vertex `u` off the hexagons that has an edge of colour `2`, that edge may
have to change colour: `exists_kk` finds a colour `k u ∉ Aset u`, `k u ≠ 2`, such that replacing `2`
by `k u` does not make the colour set of `u` equal to that of a vertex with the same key and degree
and no colour `2` (at most `C(2, d)` such vertices, against `4 - d` candidates).

`Q u u'`: `u, u'` (off the hexagons) are joined by edges of colour `2` to opposite hexagon vertices.
`Q` and `Rel` are matchings, so a two-colouring `gb` separates both (`exists_gb`).
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.T6

open Finset SimpleGraph _root_.LeanPool.BalancedEdgeColourings.Bkls.Comp

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {c : Sym2 V → Fin 3} {κ : Type*} {key : V → κ}

/-- The colours `0, 1, 2` of `step_cor4` become `0, 1, 3`. -/
def emb (a : Fin 3) : Fin 4 := if a = 2 then 3 else a.castSucc

theorem emb_inj : Function.Injective emb := by decide

theorem emb_ne_two (a : Fin 3) : emb a ≠ 2 := by revert a; decide

theorem emb_mem (a : Fin 3) : emb a ∈ ({0, 1, 3} : Finset (Fin 4)) := by revert a; decide

variable (G c) in
/-- The colours shown at `x` by the recoloured edges of colours `0, 1`. -/
noncomputable def Aset (col01 : Sym2 V → Fin 3) (x : V) : Finset (Fin 4) :=
  (inc01 G c x).image (emb ∘ col01)

omit [DecidableEq V] in
theorem card_inc01_of_two (hc : ProperOn G c) {x : V} (h : (2 : Fin 3) ∈ Sc G c x) :
    #(inc01 G c x) + 1 = G.degree x := by
  classical
  obtain ⟨y, hy, hcy⟩ := exists_two h
  rw [← C4.card_inc, inc01, ← card_filter_add_card_filter_not (s := G.incidenceFinset x) (fun
      e => c e ≠ 2)]
  have : (G.incidenceFinset x).filter (fun e => ¬ c e ≠ 2) = {s(x, y)} := by
    ext e
    simp only [mem_filter, mem_singleton, not_not, C4.mem_inc]
    constructor
    · rintro ⟨⟨he, hxe⟩, hce⟩
      exact two_edge_unique hc he hxe hce hy (Sym2.mem_mk_left _ _) hcy
    · rintro rfl; exact ⟨⟨hy, Sym2.mem_mk_left _ _⟩, hcy⟩
  rw [this, card_singleton]

omit [DecidableEq V] in
theorem inc01_of_not_two {x : V} (h : (2 : Fin 3) ∉ Sc G c x) :
    inc01 G c x = G.incidenceFinset x := by
  classical
  apply filter_true_of_mem
  intro e he hce
  exact h (mem_image.2 ⟨e, he, hce⟩)

omit [DecidableEq V] in
theorem card_Aset {col01 : Sym2 V → Fin 3} {x : V}
    (hp : ∀ e e', e ∈ inc01 G c x → e' ∈ inc01 G c x → e ≠ e' → col01 e ≠ col01 e') :
    #(Aset G c col01 x) = #(inc01 G c x) := by
  classical
  apply card_image_of_injOn
  intro a ha b hb hab
  by_contra hne
  exact hp a b ha hb hne (emb_inj hab)

omit [DecidableEq V] in
theorem Aset_sub (col01 : Sym2 V → Fin 3) (x : V) : Aset G c col01 x ⊆ {0, 1, 3} := by
  classical
  intro y hy
  obtain ⟨e, -, rfl⟩ := mem_image.1 hy
  exact emb_mem _

omit [DecidableEq V] in
theorem two_notMem_Aset (col01 : Sym2 V → Fin 3) (x : V) : (2 : Fin 4) ∉ Aset G c col01 x := by
  classical
  exact fun h => by have := Aset_sub col01 x h; simp at this
section Hyp

variable (hc : ProperOn G c)
  (h1 : ∀ u v, key u = key v → u ≠ v → G.degree u = G.degree v → Sc G c u = Sc G c v →
    G.degree u = 3)
  (h2 : ∀ u v w, key u = key v → key v = key w → G.degree u = 3 → G.degree v = 3 →
    G.degree w = 3 → u = v ∨ v = w ∨ u = w)

include hc h1 in
omit [DecidableEq V] in
/-- **The replacement colour at one vertex.** -/
theorem exists_k {col01 : Sym2 V → Fin 3} {u : V}
    (hp : ∀ e e', e ∈ inc01 G c u → e' ∈ inc01 G c u → e ≠ e' → col01 e ≠ col01 e')
    (h2u : (2 : Fin 3) ∈ Sc G c u) :
    ∃ k : Fin 4, k ≠ 2 ∧ k ∉ Aset G c col01 u ∧ ∀ v, v ≠ u → key v = key u →
      G.degree v = G.degree u → (2 : Fin 3) ∉ Sc G c v →
      insert k (Aset G c col01 u) ≠ Aset G c col01 v := by
  classical
  have hd3 : G.degree u ≤ 3 := degree_le_three hc u
  have hcardA : #(Aset G c col01 u) + 1 = G.degree u := by
    rw [card_Aset hp, card_inc01_of_two hc h2u]
  have hK : #(({0, 1, 3} : Finset (Fin 4)) \ Aset G c col01 u) + #(Aset G c col01 u) = 3 :=
    card_sdiff_add_card_eq_card (Aset_sub col01 u)
  by_contra hall
  push Not at hall
  have hb : ∀ k ∈ ({0, 1, 3} : Finset (Fin 4)) \ Aset G c col01 u, ∃ v, v ≠ u ∧
      key v = key u ∧ G.degree v = G.degree u ∧ (2 : Fin 3) ∉ Sc G c v ∧
      insert k (Aset G c col01 u) = Aset G c col01 v := by
    intro k hk
    rw [mem_sdiff] at hk
    have hk2 : k ≠ 2 := by
      intro e; subst e; simp at hk
    exact hall k hk2 hk.2
  have : Nonempty V := ⟨u⟩
  choose! b hb using hb
  have hsub2 : ∀ v, (2 : Fin 3) ∉ Sc G c v → Sc G c v ⊆ univ.erase 2 := fun v h y hy =>
    mem_erase.2 ⟨fun e => h (by subst e; exact hy), mem_univ _⟩
  have hmaps : ∀ k ∈ ({0, 1, 3} : Finset (Fin 4)) \ Aset G c col01 u,
      Sc G c (b k) ∈ (univ.erase (2 : Fin 3)).powersetCard (G.degree u) := by
    intro k hk
    obtain ⟨-, -, hdeg, h2', -⟩ := hb k hk
    rw [mem_powersetCard]
    exact ⟨hsub2 _ h2', by rw [card_Sc hc, hdeg]⟩
  have hinj : Set.InjOn (fun k => Sc G c (b k))
      ↑(({0, 1, 3} : Finset (Fin 4)) \ Aset G c col01 u) := by
    intro k hk k' hk' e
    obtain ⟨-, hkey, hdeg, h2', hA⟩ := hb k hk
    obtain ⟨-, hkey', hdeg', -, hA'⟩ := hb k' hk'
    have hbb : b k = b k' := by
      by_contra hbb
      have h3 := h1 (b k) (b k') (hkey.trans hkey'.symm) hbb (hdeg.trans hdeg'.symm) e
      have hle : #(Sc G c (b k)) ≤ #(univ.erase (2 : Fin 3)) := card_le_card (hsub2 _ h2')
      have h2c : #(univ.erase (2 : Fin 3)) = 2 := by decide
      rw [card_Sc hc, h2c] at hle
      omega
    have heq : insert k (Aset G c col01 u) = insert k' (Aset G c col01 u) := by
      rw [hA, hA', hbb]
    have hkA := (mem_sdiff.1 hk).2
    have hm : k ∈ insert k' (Aset G c col01 u) := heq ▸ mem_insert_self _ _
    rcases mem_insert.1 hm with h | h
    · exact h
    · exact absurd h hkA
  have hle := card_le_card_of_injOn _ (fun k hk => hmaps k hk) hinj
  rw [card_powersetCard] at hle
  have h2c : #(univ.erase (2 : Fin 3)) = 2 := by decide
  rw [h2c] at hle
  have e1 : Nat.choose 2 1 = 2 := rfl
  have e2 : Nat.choose 2 2 = 1 := rfl
  have e3 : Nat.choose 2 3 = 0 := rfl
  rcases (show G.degree u = 1 ∨ G.degree u = 2 ∨ G.degree u = 3 by omega) with h | h | h <;>
    rw [h] at hle <;> omega

include hc h1 in
omit [DecidableEq V] in
/-- **The replacement colours.** -/
theorem exists_kk {col01 : Sym2 V → Fin 3}
    (hp : ∀ x, ¬ IsHex G c key x → ∀ e e', e ∈ inc01 G c x → e' ∈ inc01 G c x → e ≠ e' →
      col01 e ≠ col01 e') :
    ∃ kk : V → Fin 4, ∀ u, kk u ≠ 2 ∧ (¬ IsHex G c key u → (2 : Fin 3) ∈ Sc G c u →
      kk u ∉ Aset G c col01 u ∧ ∀ v, v ≠ u → key v = key u → G.degree v = G.degree u →
        (2 : Fin 3) ∉ Sc G c v → insert (kk u) (Aset G c col01 u) ≠ Aset G c col01 v) := by
  classical
  have : ∀ u, ∃ k : Fin 4, k ≠ 2 ∧ (¬ IsHex G c key u → (2 : Fin 3) ∈ Sc G c u →
      k ∉ Aset G c col01 u ∧ ∀ v, v ≠ u → key v = key u → G.degree v = G.degree u →
        (2 : Fin 3) ∉ Sc G c v → insert k (Aset G c col01 u) ≠ Aset G c col01 v) := by
    intro u
    by_cases h : ¬ IsHex G c key u ∧ (2 : Fin 3) ∈ Sc G c u
    · obtain ⟨k, a, b, d⟩ := exists_k hc h1 (hp u h.1) h.2
      exact ⟨k, a, fun _ _ => ⟨b, d⟩⟩
    · exact ⟨0, by decide, fun h' h'' => absurd ⟨h', h''⟩ h⟩
  choose kk hkk using this
  exact ⟨kk, hkk⟩
end Hyp

variable (G c key) in
/-- `u, u'` (off the hexagons) are joined by edges of colour `2` to opposite hexagon vertices. -/
def Q (u u' : V) : Prop :=
  ¬ IsHex G c key u ∧ ¬ IsHex G c key u' ∧ ∃ x x', Opp G c key x x' ∧ G.Adj x u ∧
    c s(x, u) = 2 ∧ G.Adj x' u' ∧ c s(x', u') = 2

omit [DecidableEq V] in
theorem Q.symm {u u' : V} (h : Q G c key u u') : Q G c key u' u := by
  classical
  obtain ⟨a, b, x, x', o, h1, h2, h3, h4⟩ := h
  exact ⟨b, a, x', x, o.symm, h3, h4, h1, h2⟩

omit [DecidableEq V] in
theorem Q_unique (hc : ProperOn G c)
    (h1 : ∀ u v, key u = key v → u ≠ v → G.degree u = G.degree v → Sc G c u = Sc G c v →
      G.degree u = 3)
    (h2 : ∀ u v w, key u = key v → key v = key w → G.degree u = 3 → G.degree v = 3 →
      G.degree w = 3 → u = v ∨ v = w ∨ u = w)
    {u v w : V} (hv : Q G c key u v) (hw : Q G c key u w) : v = w := by
  classical
  obtain ⟨-, -, x, x', o, ha, hca, hb, hcb⟩ := hv
  obtain ⟨-, -, y, y', o', ha', hca', hb', hcb'⟩ := hw
  have hxy : x = y := two_unique hc ha.symm (by rwa [Sym2.eq_swap]) ha'.symm
    (by rwa [Sym2.eq_swap])
  subst hxy
  have := opp_unique hc h1 h2 o o'
  subst this
  exact two_unique hc hb hcb hb' hcb'

omit [DecidableEq V] in
/-- **Orientation of the short pairs.** -/
theorem exists_gb (hc : ProperOn G c)
    (h1 : ∀ u v, key u = key v → u ≠ v → G.degree u = G.degree v → Sc G c u = Sc G c v →
      G.degree u = 3)
    (h2 : ∀ u v w, key u = key v → key v = key w → G.degree u = 3 → G.degree v = 3 →
      G.degree w = 3 → u = v ∨ v = w ∨ u = w) :
    ∃ gb : V → Bool, (∀ u v, u ≠ v → Q G c key u v → gb u ≠ gb v) ∧
      ∀ u v, u ≠ v → Rel G c key u v → gb u ≠ gb v := by
  classical
  exact Comp.two_matchings _ _ (fun _ _ h => h.symm) (fun _ _ _ => Q_unique hc h1 h2)
    (fun _ _ h => h.symm) (fun _ _ _ => rel_unique hc h1 h2)
end Bkls.T6

end LeanPool.BalancedEdgeColourings
