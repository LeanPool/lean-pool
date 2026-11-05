/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.Cycle3
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Balister–Kostochka–Li–Schelp 2004, Lemma 3 (three colours)

The cycles are the orbits of a permutation `σ` of a finite set (edge `v` joins `v` and `σ v`, the
colour set of `v` is `{f (σ⁻¹ v), f v}`); `m` is a partial matching of the vertices, possibly across
cycles, joining no two adjacent vertices. If every cycle has length at least `3`, every odd cycle
has an unmatched vertex, and no cycle of length `6` has all its opposite vertices matched, then a
proper colouring with three colours separates the colour sets of matched vertices (`lemma3`).

The cycles are coloured one at a time with `Bkls.Cyc.cycle_colouring`: a partner on a cycle already
coloured restricts the vertex by its colour set, a partner on a later cycle imposes nothing yet.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.L3

open Finset Function

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The colour set of `v`: the colours of the edges `σ⁻¹ v → v` and `v → σ v`. -/
def S3 (σ : Equiv.Perm V) (f : V → Fin 3) (v : V) : Finset (Fin 3) := {f (σ.symm v), f v}

omit [DecidableEq V] [Fintype V] in
theorem isPeriodicPt_perm (σ : Equiv.Perm V) (v : V) : IsPeriodicPt σ (orderOf σ) v := by
  classical
  change (⇑σ)^[orderOf σ] v = v
  rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]
  rfl

omit [DecidableEq V] [Fintype V] in
theorem minimalPeriod_pos_perm [Finite V] (σ : Equiv.Perm V) (v : V) : 0 < minimalPeriod σ v := by
  classical
  let : Fintype V := Fintype.ofFinite V
  exact (isPeriodicPt_perm σ v).minimalPeriod_pos (orderOf_pos σ)

omit [DecidableEq V] [Fintype V] in
theorem iterate_mod (σ : Equiv.Perm V) (v : V) (n : ℕ) :
    (⇑σ)^[n % minimalPeriod σ v] v = (⇑σ)^[n] v := by
  classical
  exact (isPeriodicPt_minimalPeriod σ v).iterate_mod_apply n

omit [DecidableEq V] [Fintype V] in
/-- **Lemma 3 (three colours).** -/
theorem lemma3 [Finite V] (σ : Equiv.Perm V) (m : V → Option V)
    (hm : ∀ u v, m u = some v → m v = some u ∧ v ≠ u ∧ v ≠ σ u ∧ u ≠ σ v)
    (h3 : ∀ v, 3 ≤ minimalPeriod σ v)
    (hodd : ∀ v, Odd (minimalPeriod σ v) → ∃ k, m ((⇑σ)^[k] v) = none)
    (h6 : ∀ v, ¬ (minimalPeriod σ v = 6 ∧ ∀ k, m ((⇑σ)^[k] v) = some ((⇑σ)^[k + 3] v))) :
    ∃ f : V → Fin 3, (∀ v, f v ≠ f (σ v)) ∧ ∀ u v, m u = some v → S3 σ f u ≠ S3 σ f v := by
  classical
  let : Fintype V := Fintype.ofFinite V
  -- invariance of a set under `σ`
  let Inv : Finset V → Prop := fun D => ∀ v, v ∈ D ↔ σ v ∈ D
  let Good : Finset V → (V → Fin 3) → Prop := fun D f =>
    (∀ v ∈ D, f v ≠ f (σ v)) ∧ ∀ u v, u ∈ D → v ∈ D → m u = some v → S3 σ f u ≠ S3 σ f v
  have hiter : ∀ D, Inv D → ∀ v ∈ D, ∀ k, (⇑σ)^[k] v ∈ D := by
    intro D hD v hv k
    induction k with
    | zero => exact hv
    | succ k ih => rw [iterate_succ_apply']; exact (hD _).1 ih
  have hsymm : ∀ D, Inv D → ∀ v, v ∈ D ↔ σ.symm v ∈ D := fun D hD v => by
    rw [hD (σ.symm v), Equiv.apply_symm_apply]
  suffices key : ∀ n, ∀ D : Finset V, #D ≤ n → Inv D → ∃ f, Good D f by
    obtain ⟨f, hf1, hf2⟩ := key _ univ le_rfl (fun v => by simp)
    exact ⟨f, fun v => hf1 v (mem_univ _), fun u v h => hf2 u v (mem_univ _) (mem_univ _) h⟩
  intro n
  induction n with
  | zero =>
    intro D hD _
    have : D = ∅ := card_eq_zero.1 (by omega)
    subst this
    exact ⟨fun _ => 0, fun v hv => absurd hv (notMem_empty v),
      fun u v hu => absurd hu (notMem_empty u)⟩
  | succ n ih =>
    intro D hDc hD
    rcases D.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · exact ⟨fun _ => 0, fun v hv => absurd hv (notMem_empty v),
        fun u v hu => absurd hu (notMem_empty u)⟩
    -- the orbit of `v`
    set r := minimalPeriod σ v with hr
    have hr0 : 0 < r := minimalPeriod_pos_perm σ v
    have hr3 : 3 ≤ r := h3 v
    have : NeZero r := ⟨by omega⟩
    let ι : ZMod r → V := fun k => (⇑σ)^[k.val] v
    have hιsucc : ∀ k, σ (ι k) = ι (k + 1) := by
      intro k
      change σ ((⇑σ)^[k.val] v) = (⇑σ)^[(k + 1).val] v
      rw [← iterate_succ_apply' σ k.val v, ← iterate_mod σ v (k.val + 1), ← hr,
        Cyc.val_add_one' k]
    have hιpred : ∀ k, σ.symm (ι k) = ι (k - 1) := by
      intro k
      rw [Equiv.symm_apply_eq, hιsucc, sub_add_cancel]
    have hιinj : Injective ι := by
      intro a b h
      have := iterate_injOn_Iio_minimalPeriod (f := σ) (x := v) (ZMod.val_lt a) (ZMod.val_lt b) h
      exact ZMod.val_injective r this
    have hιnat : ∀ k : ℕ, (⇑σ)^[k] v = ι (k : ZMod r) := by
      intro k
      change (⇑σ)^[k] v = (⇑σ)^[((k : ℕ) : ZMod r).val] v
      rw [ZMod.val_natCast, hr, iterate_mod]
    set O := univ.image ι with hO
    have hmemO : ∀ u, u ∈ O ↔ ∃ k, ι k = u := fun u => by simp [hO]
    have hOinv : Inv O := by
      intro u
      rw [hmemO, hmemO]
      constructor
      · rintro ⟨k, rfl⟩; exact ⟨k + 1, (hιsucc k).symm⟩
      · rintro ⟨k, hk⟩
        refine ⟨k - 1, ?_⟩
        rw [← hιpred, hk, Equiv.symm_apply_apply]
    have hOD : O ⊆ D := by
      intro u hu
      obtain ⟨k, rfl⟩ := (hmemO u).1 hu
      exact hiter D hD v hv k.val
    -- the rest
    set D' := D \ O with hD'
    have hD'inv : Inv D' := by
      intro u
      simp only [hD', mem_sdiff]
      rw [hD u, hOinv u]
    have hD'c : #D' ≤ n := by
      have h1 : v ∈ O := (hmemO v).2 ⟨0, by simp [ι]⟩
      have := card_sdiff_add_card_eq_card hOD
      have h2 : 0 < #O := card_pos.2 ⟨v, h1⟩
      rw [hD']; omega
    obtain ⟨f, hf1, hf2⟩ := ih D' hD'c hD'inv
    -- the index of a vertex of the orbit
    let idx : V → ZMod r := fun u => if h : ∃ k, ι k = u then h.choose else 0
    have hidx : ∀ k, idx (ι k) = k := fun k => by
      have h : ∃ k', ι k' = ι k := ⟨k, rfl⟩
      simp only [idx, dite_eq_left h]
      exact hιinj h.choose_spec
    have hιidx : ∀ u ∈ O, ι (idx u) = u := fun u hu => by
      obtain ⟨k, rfl⟩ := (hmemO u).1 hu
      rw [hidx]
    -- the states of the orbit
    let st : ZMod r → Cyc.VState r := fun k =>
      match m (ι k) with
      | none => .free
      | some u => if u ∈ O then .int (idx u) else if u ∈ D' then .ext (S3 σ f u) else .free
    have hst_int : ∀ k j, st k = .int j → m (ι k) = some (ι j) := by
      intro k j h
      cases hmk : m (ι k) with
      | none => simp [st, hmk] at h
      | some u =>
        simp only [st, hmk] at h
        by_cases h1 : u ∈ O
        · rw [ite_eq_left h1] at h
          rw [← Cyc.VState.int.inj h, hιidx u h1]
        · rw [ite_eq_right h1] at h
          by_cases h2 : u ∈ D'
          · rw [ite_eq_left h2] at h; cases h
          · rw [ite_eq_right h2] at h; cases h
    have hst_ext : ∀ k F, st k = .ext F → ∃ u, m (ι k) = some u ∧ u ∈ D' ∧ F = S3 σ f u := by
      intro k F h
      cases hmk : m (ι k) with
      | none => simp [st, hmk] at h
      | some u =>
        simp only [st, hmk] at h
        by_cases h1 : u ∈ O
        · rw [ite_eq_left h1] at h; cases h
        · rw [ite_eq_right h1] at h
          by_cases h2 : u ∈ D'
          · rw [ite_eq_left h2] at h
            exact ⟨u, rfl, h2, (Cyc.VState.ext.inj h).symm⟩
          · rw [ite_eq_right h2] at h; cases h
    have hst_of : ∀ k u, m (ι k) = some u → u ∈ O → st k = .int (idx u) := by
      intro k u hu h1
      simp only [st, hu, ite_eq_left h1]
    have hst_of' : ∀ k u, m (ι k) = some u → u ∉ O → u ∈ D' → st k = .ext (S3 σ f u) := by
      intro k u hu h1 h2
      simp only [st, hu, ite_eq_right h1, ite_eq_left h2]
    -- apply the one-cycle lemma
    obtain ⟨g, hg1, hg2, hg3⟩ := Cyc.cycle_colouring r hr3 st
      (fun k F h => by
        obtain ⟨u, -, hu, rfl⟩ := hst_ext k F h
        have hne : f (σ.symm u) ≠ f u := by
          have := hf1 (σ.symm u) ((hsymm D' hD'inv u).1 hu)
          rwa [Equiv.apply_symm_apply] at this
        unfold S3
        exact card_pair hne)
      (fun k j h => by
        have hkj := hst_int k j h
        obtain ⟨h1, h2, h3', h4⟩ := hm _ _ hkj
        refine ⟨hst_of j (ι k) h1 ((hmemO _).2 ⟨k, rfl⟩) |>.trans (by rw [hidx]),
          fun e => h2 (by rw [e]), fun e => h3' (by rw [e, hιsucc]), fun e => h4 (by
            rw [e, hιsucc])⟩)
      (fun hodd' => by
        obtain ⟨k, hk⟩ := hodd v hodd'
        refine ⟨(k : ZMod r), ?_⟩
        simp only [st]
        rw [← hιnat k, hk])
      (fun ⟨h6r, hall⟩ => h6 v ⟨h6r, fun k => by
        have := hst_int _ _ (hall (k : ZMod r))
        rw [← hιnat k] at this
        rw [this, hιnat (k + 3)]
        push_cast
        rfl⟩)
    -- the extended colouring
    let f' : V → Fin 3 := fun w => if w ∈ O then g (idx w) else f w
    have hf'O : ∀ k, f' (ι k) = g k := fun k => by
      simp only [f', ite_eq_left ((hmemO _).2 ⟨k, rfl⟩), hidx]
    have hf'D : ∀ w, w ∉ O → f' w = f w := fun w hw => by simp only [f', ite_eq_right hw]
    have hSO : ∀ k, S3 σ f' (ι k) = Cyc.S g k := fun k => by
      unfold S3 Cyc.S
      rw [hιpred, hf'O, hf'O]
    have hSD : ∀ w, w ∈ D' → S3 σ f' w = S3 σ f w := fun w hw => by
      have h1 : w ∉ O := (mem_sdiff.1 hw).2
      have h2 : σ.symm w ∉ O := (mem_sdiff.1 ((hsymm D' hD'inv w).1 hw)).2
      unfold S3
      rw [hf'D w h1, hf'D _ h2]
    refine ⟨f', fun w hw => ?_, fun u w hu hw huw => ?_⟩
    · by_cases hwO : w ∈ O
      · obtain ⟨k, rfl⟩ := (hmemO w).1 hwO
        rw [hιsucc, hf'O, hf'O]
        exact hg1 k
      · have hwD' : w ∈ D' := mem_sdiff.2 ⟨hw, hwO⟩
        have hsw : σ w ∉ O := fun h => hwO ((hOinv w).2 h)
        rw [hf'D w hwO, hf'D _ hsw]
        exact hf1 w hwD'
    · by_cases huO : u ∈ O <;> by_cases hwO : w ∈ O
      · obtain ⟨k, rfl⟩ := (hmemO u).1 huO
        obtain ⟨j, rfl⟩ := (hmemO w).1 hwO
        rw [hSO, hSO]
        exact hg3 k j (by rw [hst_of k (ι j) huw hwO, hidx])
      · obtain ⟨k, rfl⟩ := (hmemO u).1 huO
        have hwD' : w ∈ D' := mem_sdiff.2 ⟨hw, hwO⟩
        rw [hSO, hSD w hwD']
        exact hg2 k _ (hst_of' k w huw hwO hwD')
      · obtain ⟨j, rfl⟩ := (hmemO w).1 hwO
        have huD' : u ∈ D' := mem_sdiff.2 ⟨hu, huO⟩
        have hwu := (hm _ _ huw).1
        rw [hSO, hSD u huD']
        exact fun e => hg2 j _ (hst_of' j u hwu huO huD') e.symm
      · have huD' : u ∈ D' := mem_sdiff.2 ⟨hu, huO⟩
        have hwD' : w ∈ D' := mem_sdiff.2 ⟨hw, hwO⟩
        rw [hSD u huD', hSD w hwD']
        exact hf2 u w huD' hwD' huw
end Bkls.L3

end LeanPool.BalancedEdgeColourings
