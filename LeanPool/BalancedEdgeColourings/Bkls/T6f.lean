/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.T6e

/-!
# Theorem 6, part (f): the colouring before the hexagons are fixed

`col2`: edges of colours `0, 1` get `emb ∘ col01`; edges of colour `2` between hexagon vertices get
`emb ∘ lg`; an edge of colour `2` from a hexagon to a vertex `u` off the hexagons gets `pc u`
(`kk u`
if `u` is in a short pair and `gb u = false`, else `2`); other edges of colour `2` keep `2`.

* `col2_proper`: proper at every vertex off the hexagons;
* `col2_sep`: vertices off the hexagons with the same key get different colour sets;
* `col2_pend`: the pendant edges at opposite hexagon vertices (not joined to each other) get
  different colours.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.T6

open Finset SimpleGraph _root_.LeanPool.BalancedEdgeColourings.Bkls.Comp

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {c : Sym2 V → Fin 3} {κ : Type*} {key : V → κ}

omit [DecidableEq V] in
theorem mem_inc01 {x : V} {e : Sym2 V} :
    e ∈ inc01 G c x ↔ e ∈ G.incidenceFinset x ∧ c e ≠ 2 := by
  classical
  unfold inc01; exact mem_filter
variable (G c key) in
/-- `u` is in a short pair and gives up the colour `2`. -/
def Changed (gb : V → Bool) (u : V) : Prop := (∃ u', Q G c key u u') ∧ gb u = false

variable (G c key) in
/-- The colour of the edge of colour `2` at `u`, when it goes to a hexagon. -/
noncomputable def pc (kk : V → Fin 4) (gb : V → Bool) (u : V) : Fin 4 := by
  classical exact if Changed G c key gb u then kk u else 2

variable (G c key) in
/-- The colouring before the hexagons are fixed. -/
noncomputable def col2 (col01 lg : Sym2 V → Fin 3) (kk : V → Fin 4) (gb : V → Bool)
    (e : Sym2 V) : Fin 4 := by
  classical
  exact if c e ≠ 2 then emb (col01 e)
    else if ∀ y ∈ e, IsHex G c key y then emb (lg e)
    else if h : ∃ u ∈ e, ¬ IsHex G c key u ∧ ∃ x ∈ e, IsHex G c key x then
      pc G c key kk gb h.choose
    else 2

variable {col01 lg : Sym2 V → Fin 3} {kk : V → Fin 4} {gb : V → Bool}

omit [DecidableEq V] in
theorem pc_of_changed {u : V} (h : Changed G c key gb u) : pc G c key kk gb u = kk u := by
  classical
  rw [pc, ite_eq_left h]

omit [DecidableEq V] in
theorem pc_of_not_changed {u : V} (h : ¬ Changed G c key gb u) : pc G c key kk gb u = 2 := by
  classical
  rw [pc, ite_eq_right h]
theorem col2_01 {e : Sym2 V} (h : c e ≠ 2) : col2 G c key col01 lg kk gb e = emb (col01 e) := by
  rw [col2, ite_eq_left h]

omit [DecidableEq V] in
theorem allhex {x y : V} (hx : IsHex G c key x) (hy : IsHex G c key y) :
    ∀ z ∈ s(x, y), IsHex G c key z := by
  classical
  intro z hz
  rcases Sym2.mem_iff.1 hz with rfl | rfl
  · exact hx
  · exact hy
theorem col2_hh {e : Sym2 V} (h : c e = 2) (hall : ∀ y ∈ e, IsHex G c key y) :
    col2 G c key col01 lg kk gb e = emb (lg e) := by
  rw [col2, ite_eq_right (not_not.2 h), ite_eq_left hall]

theorem col2_hu {x u : V} (hcx : c s(x, u) = 2) (hx : IsHex G c key x)
    (hu : ¬ IsHex G c key u) : col2 G c key col01 lg kk gb s(x, u) = pc G c key kk gb u := by
  have hn : ¬ ∀ y ∈ s(x, u), IsHex G c key y := fun h => hu (h u (Sym2.mem_mk_right _ _))
  have hex : ∃ w ∈ s(x, u), ¬ IsHex G c key w ∧ ∃ z ∈ s(x, u), IsHex G c key z :=
    ⟨u, Sym2.mem_mk_right _ _, hu, x, Sym2.mem_mk_left _ _, hx⟩
  rw [col2, ite_eq_right (not_not.2 hcx), ite_eq_right hn, dite_eq_left hex]
  congr 1
  obtain ⟨hm, hn', -⟩ := hex.choose_spec
  rcases Sym2.mem_iff.1 hm with h | h
  · exact absurd (by rw [h]; exact hx) hn'
  · exact h

theorem col2_uu {x y : V} (hcx : c s(x, y) = 2) (hx : ¬ IsHex G c key x)
    (hy : ¬ IsHex G c key y) : col2 G c key col01 lg kk gb s(x, y) = 2 := by
  have hn : ¬ ∀ z ∈ s(x, y), IsHex G c key z := fun h => hx (h x (Sym2.mem_mk_left _ _))
  have hnex : ¬ ∃ w ∈ s(x, y), ¬ IsHex G c key w ∧ ∃ z ∈ s(x, y), IsHex G c key z := by
    rintro ⟨-, -, -, z, hz, hzh⟩
    rcases Sym2.mem_iff.1 hz with rfl | rfl
    · exact hx hzh
    · exact hy hzh
  rw [col2, ite_eq_right (not_not.2 hcx), ite_eq_right hn, dite_eq_right hnex]

omit [DecidableEq V] in
theorem not_changed_of (hc : ProperOn G c) {u y : V} (hy : G.Adj u y) (hcy : c s(u, y) = 2)
    (hyh : ¬ IsHex G c key y) : ¬ Changed G c key gb u := by
  classical
  rintro ⟨⟨u', -, -, x, x', o, hxu, hcxu, -, -⟩, -⟩
  have : x = y := two_unique hc hxu.symm (by rwa [Sym2.eq_swap]) hy hcy
  exact hyh (this ▸ o.hex)
theorem col2_two_off (hc : ProperOn G c) {u y : V} (hu : ¬ IsHex G c key u) (hy : G.Adj u y)
    (hcy : c s(u, y) = 2) : col2 G c key col01 lg kk gb s(u, y) = pc G c key kk gb u := by
  by_cases hyh : IsHex G c key y
  · rw [Sym2.eq_swap]; exact col2_hu (by rwa [Sym2.eq_swap]) hyh hu
  · rw [col2_uu hcy hu hyh, pc_of_not_changed (not_changed_of hc hy hcy hyh)]

theorem col2_mixed (hc : ProperOn G c)
    (hkkA : ∀ u, ¬ IsHex G c key u → (2 : Fin 3) ∈ Sc G c u → kk u ∉ Aset G c col01 u)
    {x : V} {e e' : Sym2 V} (hx : ¬ IsHex G c key x) (he : e ∈ G.incidenceFinset x)
    (hce : c e = 2) (he' : e' ∈ inc01 G c x) :
    col2 G c key col01 lg kk gb e ≠ col2 G c key col01 lg kk gb e' := by
  rw [C4.mem_inc] at he
  obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.1 he.2
  have hy : G.Adj x y := by have := he.1; rwa [mem_edgeSet] at this
  rw [col2_two_off hc hx hy hce, col2_01 (mem_inc01.1 he').2]
  have hmem : emb (col01 e') ∈ Aset G c col01 x := mem_image.2 ⟨e', he', rfl⟩
  intro heq
  by_cases hch : Changed G c key gb x
  · rw [pc_of_changed hch] at heq
    have h2x : (2 : Fin 3) ∈ Sc G c x :=
      mem_image.2 ⟨s(x, y), (C4.mem_inc G).2 ⟨hy, Sym2.mem_mk_left _ _⟩, hce⟩
    exact hkkA x hx h2x (by rw [heq]; exact hmem)
  · rw [pc_of_not_changed hch] at heq
    exact emb_ne_two _ heq.symm

/-- **Proper off the hexagons.** -/
theorem col2_proper (hc : ProperOn G c)
    (hcol01 : ∀ x, ¬ IsHex G c key x → ∀ e e', e ∈ inc01 G c x → e' ∈ inc01 G c x → e ≠ e' →
      col01 e ≠ col01 e')
    (hkkA : ∀ u, ¬ IsHex G c key u → (2 : Fin 3) ∈ Sc G c u → kk u ∉ Aset G c col01 u)
    {x : V} (hx : ¬ IsHex G c key x) :
    ∀ e e', e ∈ G.incidenceFinset x → e' ∈ G.incidenceFinset x → e ≠ e' →
      col2 G c key col01 lg kk gb e ≠ col2 G c key col01 lg kk gb e' := by
  intro e e' he he' hne
  by_cases hce : c e = 2
  · by_cases hce' : c e' = 2
    · exact absurd (hce.trans hce'.symm) (hc x e e' he he' hne)
    · exact col2_mixed hc hkkA hx he hce (mem_inc01.2 ⟨he', hce'⟩)
  · by_cases hce' : c e' = 2
    · exact (col2_mixed hc hkkA hx he' hce' (mem_inc01.2 ⟨he, hce⟩)).symm
    · rw [col2_01 hce, col2_01 hce']
      exact fun h => hcol01 x hx e e' (mem_inc01.2 ⟨he, hce⟩) (mem_inc01.2 ⟨he', hce'⟩) hne
        (emb_inj h)

theorem Sc_col2 (hc : ProperOn G c) {x : V} (hx : ¬ IsHex G c key x) :
    Sc G (col2 G c key col01 lg kk gb) x = if (2 : Fin 3) ∈ Sc G c x then
      insert (pc G c key kk gb x) (Aset G c col01 x) else Aset G c col01 x := by
  have himg : (inc01 G c x).image (col2 G c key col01 lg kk gb) = Aset G c col01 x := by
    unfold Aset
    apply image_congr
    intro e he
    exact col2_01 (mem_inc01.1 (mem_coe.1 he)).2
  split_ifs with h2
  · obtain ⟨y, hy, hcy⟩ := exists_two h2
    have hinc : G.incidenceFinset x = insert s(x, y) (inc01 G c x) := by
      ext e
      rw [mem_insert, mem_inc01]
      constructor
      · intro he
        by_cases hce : c e = 2
        · left
          exact two_edge_unique hc ((C4.mem_inc G).1 he).1 ((C4.mem_inc G).1 he).2 hce hy
            (Sym2.mem_mk_left _ _) hcy
        · right; exact ⟨he, hce⟩
      · rintro (rfl | ⟨he, -⟩)
        · exact (C4.mem_inc G).2 ⟨hy, Sym2.mem_mk_left _ _⟩
        · exact he
    rw [Sc, hinc, image_insert, himg, col2_two_off hc hx hy hcy]
  · rw [Sc, ← inc01_of_not_two h2, himg]

omit [DecidableEq V] in
theorem card_Sc_at {n : ℕ} {f : Sym2 V → Fin n} {x : V}
    (hp : ∀ e e', e ∈ G.incidenceFinset x → e' ∈ G.incidenceFinset x → e ≠ e' → f e ≠ f e') :
    #(Sc G f x) = G.degree x := by
  classical
  unfold Sc
  rw [card_image_of_injOn, C4.card_inc]
  intro a ha b hb e
  by_contra hne
  exact hp a b ha hb hne e

omit [DecidableEq V] in
theorem Aset_ne_of
    (hrel : ∀ u v, Rel G c key u v → (inc01 G c u).image col01 ≠ (inc01 G c v).image col01)
    {u v : V} (hr : Rel G c key u v) : Aset G c col01 u ≠ Aset G c col01 v := by
  classical
  intro h
  apply hrel u v hr
  unfold Aset at h
  rw [← image_image, ← image_image] at h
  exact image_injective emb_inj h
theorem sep_two (hc : ProperOn G c)
    (hkkS : ∀ u, ¬ IsHex G c key u → (2 : Fin 3) ∈ Sc G c u → ∀ v, v ≠ u → key v = key u →
      G.degree v = G.degree u → (2 : Fin 3) ∉ Sc G c v →
      insert (kk u) (Aset G c col01 u) ≠ Aset G c col01 v)
    {u v : V} (hu : ¬ IsHex G c key u) (hv : ¬ IsHex G c key v) (huv : u ≠ v)
    (hk : key u = key v) (hd : G.degree u = G.degree v) (h2u : (2 : Fin 3) ∈ Sc G c u)
    (h2v : (2 : Fin 3) ∉ Sc G c v) :
    Sc G (col2 G c key col01 lg kk gb) u ≠ Sc G (col2 G c key col01 lg kk gb) v := by
  rw [Sc_col2 hc hu, Sc_col2 hc hv, ite_eq_left h2u, ite_eq_right h2v]
  by_cases hch : Changed G c key gb u
  · rw [pc_of_changed hch]; exact hkkS u hu h2u v (Ne.symm huv) hk.symm hd.symm h2v
  · rw [pc_of_not_changed hch]
    intro h
    exact two_notMem_Aset col01 v (by rw [← h]; exact mem_insert_self _ _)

/-- **Separation off the hexagons.** -/
theorem col2_sep (hc : ProperOn G c)
    (hcol01 : ∀ x, ¬ IsHex G c key x → ∀ e e', e ∈ inc01 G c x → e' ∈ inc01 G c x → e ≠ e' →
      col01 e ≠ col01 e')
    (hrel : ∀ u v, Rel G c key u v → (inc01 G c u).image col01 ≠ (inc01 G c v).image col01)
    (hkk2 : ∀ u, kk u ≠ 2)
    (hkkA : ∀ u, ¬ IsHex G c key u → (2 : Fin 3) ∈ Sc G c u → kk u ∉ Aset G c col01 u)
    (hkkS : ∀ u, ¬ IsHex G c key u → (2 : Fin 3) ∈ Sc G c u → ∀ v, v ≠ u → key v = key u →
      G.degree v = G.degree u → (2 : Fin 3) ∉ Sc G c v →
      insert (kk u) (Aset G c col01 u) ≠ Aset G c col01 v)
    (hgR : ∀ u v, u ≠ v → Rel G c key u v → gb u ≠ gb v)
    {u v : V} (hu : ¬ IsHex G c key u) (hv : ¬ IsHex G c key v) (huv : u ≠ v)
    (hk : key u = key v) :
    Sc G (col2 G c key col01 lg kk gb) u ≠ Sc G (col2 G c key col01 lg kk gb) v := by
  by_cases hd : G.degree u = G.degree v
  swap
  · intro h
    apply hd
    rw [← card_Sc_at (col2_proper hc hcol01 hkkA hu), ← card_Sc_at (col2_proper hc hcol01 hkkA hv),
      h]
  by_cases hs : ((2 : Fin 3) ∈ Sc G c u ↔ (2 : Fin 3) ∈ Sc G c v)
  · have hr : Rel G c key u v := ⟨huv, hk, hd, hs, hu, hv⟩
    have hA := Aset_ne_of hrel hr
    rw [Sc_col2 hc hu, Sc_col2 hc hv]
    by_cases h2u : (2 : Fin 3) ∈ Sc G c u
    · rw [ite_eq_left h2u, ite_eq_left (hs.1 h2u)]
      have hg := hgR u v huv hr
      by_cases hcu : Changed G c key gb u
      · have hcv : ¬ Changed G c key gb v := fun hcv => hg (hcu.2.trans hcv.2.symm)
        rw [pc_of_changed hcu, pc_of_not_changed hcv]
        intro h
        have : (2 : Fin 4) ∈ insert (kk u) (Aset G c col01 u) := by
          rw [h]; exact mem_insert_self _ _
        rcases mem_insert.1 this with h' | h'
        · exact hkk2 u h'.symm
        · exact two_notMem_Aset col01 u h'
      · by_cases hcv : Changed G c key gb v
        · rw [pc_of_not_changed hcu, pc_of_changed hcv]
          intro h
          have : (2 : Fin 4) ∈ insert (kk v) (Aset G c col01 v) := by
            rw [← h]; exact mem_insert_self _ _
          rcases mem_insert.1 this with h' | h'
          · exact hkk2 v h'.symm
          · exact two_notMem_Aset col01 v h'
        · rw [pc_of_not_changed hcu, pc_of_not_changed hcv]
          intro h
          apply hA
          have := congrArg (fun s => s.erase 2) h
          rwa [erase_insert (two_notMem_Aset col01 u), erase_insert (two_notMem_Aset col01 v)]
            at this
    · rw [ite_eq_right h2u, ite_eq_right (fun h => h2u (hs.2 h))]; exact hA
  · by_cases h2u : (2 : Fin 3) ∈ Sc G c u
    · have h2v : (2 : Fin 3) ∉ Sc G c v := fun h => hs ⟨fun _ => h, fun _ => h2u⟩
      exact sep_two hc hkkS hu hv huv hk hd h2u h2v
    · have h2v : (2 : Fin 3) ∈ Sc G c v := by
        by_contra h2v
        exact hs ⟨fun h => absurd h h2u, fun h => absurd h h2v⟩
      exact (sep_two hc hkkS hv hu (Ne.symm huv) hk.symm hd.symm h2v h2u).symm

section Pend

variable (hc : ProperOn G c)
  (h1 : ∀ u v, key u = key v → u ≠ v → G.degree u = G.degree v → Sc G c u = Sc G c v →
    G.degree u = 3)
  (h2 : ∀ u v w, key u = key v → key v = key w → G.degree u = 3 → G.degree v = 3 →
    G.degree w = 3 → u = v ∨ v = w ∨ u = w)

include hc h1 h2 in
theorem pend_mixed {x x' y y' : V} (o : Opp G c key x x') (hy : G.Adj x y) (hcy : c s(x, y) = 2)
    (hy' : G.Adj x' y') (hcy' : c s(x', y') = 2) (hyh : IsHex G c key y)
    (hy'h : ¬ IsHex G c key y') :
    col2 G c key col01 lg kk gb s(x, y) ≠ col2 G c key col01 lg kk gb s(x', y') := by
  rw [col2_hh hcy (allhex o.hex hyh), col2_hu hcy' o.symm.hex hy'h]
  have hnc : ¬ Changed G c key gb y' := by
    rintro ⟨⟨u', -, hu', z, z', oz, hzy, hczy, hz'u, hcz'u⟩, -⟩
    have hz : z = x' := two_unique hc hzy.symm (by rwa [Sym2.eq_swap]) hy'.symm
      (by rwa [Sym2.eq_swap])
    subst hz
    have hz' : z' = x := opp_unique hc h1 h2 oz o.symm
    subst hz'
    exact hu' (two_unique hc hy hcy hz'u hcz'u ▸ hyh)
  rw [pc_of_not_changed hnc]
  exact emb_ne_two _

include hc h1 h2 in
/-- **Pendant edges at opposite vertices.** -/
theorem col2_pend (hlg : ∀ e e', (LP G c key).Adj e e' → lg e ≠ lg e') (hkk2 : ∀ u, kk u ≠ 2)
    (hgQ : ∀ u v, u ≠ v → Q G c key u v → gb u ≠ gb v)
    {x x' y y' : V} (o : Opp G c key x x') (hna : ¬ G.Adj x x') (hy : G.Adj x y)
    (hcy : c s(x, y) = 2) (hy' : G.Adj x' y') (hcy' : c s(x', y') = 2) :
    col2 G c key col01 lg kk gb s(x, y) ≠ col2 G c key col01 lg kk gb s(x', y') := by
  by_cases hyh : IsHex G c key y <;> by_cases hy'h : IsHex G c key y'
  · rw [col2_hh hcy (allhex o.hex hyh), col2_hh hcy' (allhex o.symm.hex hy'h)]
    intro h
    refine hlg s(x, y) s(x', y') ⟨fun e => ?_, ⟨hy, hcy, allhex o.hex hyh⟩,
      ⟨hy', hcy', allhex o.symm.hex hy'h⟩, x, Sym2.mem_mk_left _ _, x', Sym2.mem_mk_left _ _, o⟩
      (emb_inj h)
    rcases Sym2.eq_iff.1 e with ⟨h1', -⟩ | ⟨-, h2'⟩
    · exact o.ne h1'
    · exact hna (h2' ▸ hy)
  · exact pend_mixed hc h1 h2 o hy hcy hy' hcy' hyh hy'h
  · exact (pend_mixed hc h1 h2 o.symm hy' hcy' hy hcy hy'h hyh).symm
  · have hQ : Q G c key y y' := ⟨hyh, hy'h, x, x', o, hy, hcy, hy', hcy'⟩
    have hne : y ≠ y' := by
      rintro rfl
      exact o.ne (two_unique hc hy.symm (by rwa [Sym2.eq_swap]) hy'.symm (by rwa [Sym2.eq_swap]))
    have hg := hgQ y y' hne hQ
    rw [col2_hu hcy o.hex hyh, col2_hu hcy' o.symm.hex hy'h]
    cases hgy : gb y <;> cases hgy' : gb y'
    · exact absurd (hgy.trans hgy'.symm) hg
    · have hc1 : Changed G c key gb y := ⟨⟨y', hQ⟩, hgy⟩
      have hc2 : ¬ Changed G c key gb y' := fun h => by
        rw [h.2] at hgy'
        exact absurd hgy' (by decide)
      rw [pc_of_changed hc1, pc_of_not_changed hc2]
      exact hkk2 y
    · have hc1 : ¬ Changed G c key gb y := fun h => by rw [h.2] at hgy; exact absurd hgy (by decide)
      have hc2 : Changed G c key gb y' := ⟨⟨y, hQ.symm⟩, hgy'⟩
      rw [pc_of_not_changed hc1, pc_of_changed hc2]
      exact (hkk2 y').symm
    · exact absurd (hgy.trans hgy'.symm) hg

end Pend

end Bkls.T6

end LeanPool.BalancedEdgeColourings
