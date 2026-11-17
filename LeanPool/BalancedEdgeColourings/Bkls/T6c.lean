/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.T6b

/-!
# Theorem 6, part (c): recolouring the edges of colours `0, 1` off the hexagons

`step_cor4`: the edges of colours `0, 1` at vertices off the bad hexagons can be recoloured with
three colours, properly, so that `Rel`-pairs see different sets of these colours (Corollary 4 on
`G2`, which has no bad hexagon).
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.T6

open Finset SimpleGraph LeanPool.BalancedEdgeColourings.Bkls.Comp

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {c : Sym2 V → Fin 3} {κ : Type*} {key : V → κ}

/-- The edges of colours `0, 1` at a vertex. -/
noncomputable def inc01 (G : SimpleGraph V) [DecidableRel G.Adj] (c : Sym2 V → Fin 3) (v : V) :
    Finset (Sym2 V) := (G.incidenceFinset v).filter fun e => c e ≠ 2

omit [DecidableEq V] in
theorem step_cor4 (hc : ProperOn G c)
    (h1 : ∀ u v, key u = key v → u ≠ v → G.degree u = G.degree v → Sc G c u = Sc G c v →
      G.degree u = 3)
    (h2 : ∀ u v w, key u = key v → key v = key w → G.degree u = 3 → G.degree v = 3 →
      G.degree w = 3 → u = v ∨ v = w ∨ u = w) :
    ∃ col : Sym2 V → Fin 3,
      (∀ v e e', ¬ IsHex G c key v → e ∈ inc01 G c v → e' ∈ inc01 G c v → e ≠ e' →
        col e ≠ col e') ∧
      ∀ u v, Rel G c key u v → (inc01 G c u).image col ≠ (inc01 G c v).image col := by
  classical
  let G2 : SimpleGraph V :=
    { Adj := fun u v => (G01 G c).Adj u v ∧ ¬ IsHex G c key u ∧ ¬ IsHex G c key v
      symm := ⟨fun u v h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
      loopless := ⟨fun v h => (G01 G c).loopless.irrefl v h.1⟩ }
  have hinc : ∀ u, ¬ IsHex G c key u → G2.incidenceFinset u = inc01 G c u := by
    intro u hu
    ext e
    rw [C4.mem_inc, inc01, mem_filter, C4.mem_inc]
    constructor
    · rintro ⟨he, hue⟩
      obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.1 hue
      rw [mem_edgeSet] at he ⊢
      exact ⟨⟨he.1.1, hue⟩, he.1.2⟩
    · rintro ⟨⟨he, hue⟩, hc2⟩
      obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.1 hue
      rw [mem_edgeSet] at he ⊢
      have h01 : (G01 G c).Adj u x := ⟨he, hc2⟩
      exact ⟨⟨h01, hu, nonhex_nbr hc hu h01⟩, hue⟩
  have hinc_hex : ∀ u, IsHex G c key u → G2.incidenceFinset u = ∅ := by
    intro u hu
    ext e
    rw [C4.mem_inc]
    simp only [notMem_empty, iff_false, not_and]
    intro he hue
    obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.1 hue
    exact he.2.1 hu
  have hdeg2 : ∀ v, G2.degree v ≤ 2 := fun v =>
    (degree_le_of_le (G := G2) (H := G01 G c) (fun a b h => h.1)).trans (degree_G01_le hc v)
  -- the two colours as `Fin 2`
  let χ : Sym2 V → Fin 2 := fun e => if c e = 0 then 0 else 1
  have hχ : ∀ v e e', e ∈ G2.incidenceFinset v → e' ∈ G2.incidenceFinset v → e ≠ e' →
      χ e ≠ χ e' := by
    intro v e e' he he' hne
    by_cases hv : IsHex G c key v
    · rw [hinc_hex v hv] at he; exact absurd he (notMem_empty _)
    rw [hinc v hv] at he he'
    obtain ⟨he1, he2⟩ := mem_filter.1 he
    obtain ⟨he1', he2'⟩ := mem_filter.1 he'
    have := hc v e e' he1 he1' hne
    simp only [χ]
    split_ifs <;> first | decide | omega
  -- the matching
  let m : V → Option V := fun u => if h : ∃ v, Rel G c key u v then some h.choose else none
  have hm_iff : ∀ u v, m u = some v ↔ Rel G c key u v := by
    intro u v
    constructor
    · intro h
      by_cases hex : ∃ v, Rel G c key u v
      · simp only [m, dite_eq_left hex, Option.some.injEq] at h
        rw [← h]; exact hex.choose_spec
      · simp [m, dite_eq_right hex] at h
    · intro h
      have hex : ∃ v, Rel G c key u v := ⟨v, h⟩
      simp only [m, dite_eq_left hex, Option.some.injEq]
      exact rel_unique hc h1 h2 hex.choose_spec h
  -- colour sets and `χ`-images
  have hSc : ∀ u, ¬ IsHex G c key u → ∀ y : Fin 3, y ≠ 2 →
      (y ∈ Sc G c u ↔ (if y = 0 then (0 : Fin 2) else 1) ∈ (G2.incidenceFinset u).image χ) := by
    intro u hu y hy
    rw [hinc u hu, Sc]
    simp only [mem_image, inc01, mem_filter]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, ⟨he, hy⟩, rfl⟩
    · rintro ⟨e, ⟨he, he2⟩, hχe⟩
      refine ⟨e, he, ?_⟩
      simp only [χ] at hχe
      split_ifs at hχe with h3 h4 h4 <;> omega
  obtain ⟨col, hcol1, hcol2⟩ := C4.cor4 (H := G2) hdeg2 χ hχ m
    (fun u v h => by
      have hr := (hm_iff u v).1 h
      refine ⟨(hm_iff v u).2 hr.symm, hr.1, fun hS => ?_⟩
      obtain ⟨huv, kv, dv, sv, hu, hv⟩ := hr
      have hS' : Sc G c u = Sc G c v := by
        ext y
        by_cases hy : y = 2
        · subst hy; exact sv
        · rw [hSc u hu y hy, hSc v hv y hy, hS]
      have h3 := h1 u v kv huv dv hS'
      -- three colours present: two of them are `0, 1`
      have hfull : Sc G c u = univ := eq_univ_of_card _ (by rw [card_Sc hc, h3]; rfl)
      rw [← card_incidenceFinset_eq_degree, hinc u hu]
      have : (inc01 G c u).image c = {0, 1} := by
        ext y
        simp only [mem_image, inc01, mem_filter, mem_insert, mem_singleton]
        constructor
        · rintro ⟨e, ⟨_, h2'⟩, rfl⟩; omega
        · intro hy
          have hy' : y ∈ Sc G c u := by rw [hfull]; exact mem_univ _
          obtain ⟨e, he, rfl⟩ := mem_image.1 hy'
          exact ⟨e, ⟨he, by omega⟩, rfl⟩
      rw [← card_image_of_injOn (f := c), this]
      · decide
      · intro a ha b hb e
        by_contra hne
        exact hc u a b (mem_filter.1 ha).1 (mem_filter.1 hb).1 hne e)
    (fun w hadj hinj hall => by
      have hr : ∀ k, Rel G c key (w k) (w (k + 3)) := fun k => (hm_iff _ _).1 (hall k)
      have hbad : BadHex G c key w :=
        ⟨hinj, fun k => (hadj k).1, fun k => ⟨(hr k).2.1, (hr k).2.2.1⟩⟩
      exact (hadj 0).2.1 ⟨w, hbad, 0, rfl⟩)
  refine ⟨col, fun v e e' hv he he' hne => ?_, fun u v h => ?_⟩
  · rw [← hinc v hv] at he he'
    exact hcol1 v e e' he he' hne
  · have := hcol2 u v ((hm_iff u v).2 h)
    rwa [hinc u h.2.2.2.2.1, hinc v h.2.2.2.2.2] at this
end Bkls.T6

end LeanPool.BalancedEdgeColourings
