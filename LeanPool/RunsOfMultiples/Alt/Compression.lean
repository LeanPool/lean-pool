/-
Copyright (c) 2026 Jason Hoelscher-Obermaier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hoelscher-Obermaier, Claude Opus 5.5
-/
module

-- Adapted for Lean Pool: module visibility, imports, and proof organization.

public import LeanPool.RunsOfMultiples.Alt.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

/-!
# Chain compression (Lemma 1 and the abstract part of Lemma 2)

A *chain system* splits the positive integers into chains: every `n > 0` sits at position
`pos n` of the chain `key n`, and `elt k u` is the element at position `u` of chain `k`
(valid positions form an initial segment, elements increase along a chain).

`comp S` replaces the occupied positions of every chain by an initial segment of the same size.
We show `|comp S| = |S|`, that `comp` does not decrease any `|A S t|` provided the multiples
`j * elt k e` (`j ≤ t`) can be described by "shifted windows" in target chains (`Cons`), and
that `comp` strictly decreases the sum of the elements as soon as some chain has a gap.
-/

open Finset

@[expose] public section

namespace RunsOfMultiples

/-- A partition of the positive integers into increasing chains. -/
structure ChainSys (κ : Type) where
  /-- The chain containing a positive integer. -/
  key : ℕ → κ
  /-- The position of a positive integer in its chain. -/
  pos : ℕ → ℕ
  /-- The integer at a given chain and position. -/
  elt : κ → ℕ → ℕ
  /-- The positions belonging to a chain, forming an initial segment. -/
  vld : κ → ℕ → Prop
  elt_key_pos : ∀ n, 0 < n → elt (key n) (pos n) = n
  vld_key_pos : ∀ n, 0 < n → vld (key n) (pos n)
  key_elt : ∀ k u, vld k u → key (elt k u) = k
  pos_elt : ∀ k u, vld k u → pos (elt k u) = u
  elt_pos : ∀ k u, vld k u → 0 < elt k u
  vld_mono : ∀ k u v, vld k u → v ≤ u → vld k v
  elt_lt : ∀ k u v, vld k v → u < v → elt k u < elt k v

namespace ChainSys

variable {κ : Type} [DecidableEq κ] (C : ChainSys κ)

/-- Occupied positions of chain `k`. -/
def occ (S : Finset ℕ) (k : κ) : Finset ℕ := (S.filter (fun n => C.key n = k)).image C.pos

/-- Compression: every chain's occupied positions become an initial segment. -/
def comp (S : Finset ℕ) : Finset ℕ :=
  (S.image C.key).biUnion (fun k => (range (C.occ S k).card).image (C.elt k))

/-- The window condition describing `A S t` along chain `k`. -/
def Cons (t : ℕ) (k : κ) : Prop :=
  ∃ (ι : Type) (I : Finset ι) (tgt : ι → κ) (Lc : ι → ℕ),
    (∀ e, C.vld k e → ∀ i ∈ I, ∀ h ≤ Lc i, C.vld (tgt i) (e + h)) ∧
    ∀ S : Finset ℕ, (∀ n ∈ S, 0 < n) → ∀ e, C.vld k e →
      (C.elt k e ∈ A S t ↔ C.elt k e ∈ S ∧ ∀ i ∈ I, ∀ h ≤ Lc i, C.elt (tgt i) (e + h) ∈ S)

variable {C}

section basic

variable {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n)
include hS

lemma mem_occ_iff {k : κ} {u : ℕ} : u ∈ C.occ S k ↔ C.vld k u ∧ C.elt k u ∈ S := by
  unfold occ
  rw [mem_image]
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [mem_filter] at hn
    obtain ⟨hnS, rfl⟩ := hn
    exact ⟨C.vld_key_pos n (hS n hnS), by rw [C.elt_key_pos n (hS n hnS)]; exact hnS⟩
  · rintro ⟨hv, hmem⟩
    exact ⟨C.elt k u, mem_filter.2 ⟨hmem, C.key_elt k u hv⟩, C.pos_elt k u hv⟩

lemma vld_of_lt_card {k : κ} {u : ℕ} (hu : u < (C.occ S k).card) : C.vld k u := by
  have hne : (C.occ S k).Nonempty := card_pos.1 (by omega)
  have hM : (C.occ S k).max' hne ∈ C.occ S k := max'_mem _ _
  have hsub : C.occ S k ⊆ range ((C.occ S k).max' hne + 1) := fun x hx =>
    mem_range.2 (Nat.lt_succ_of_le (le_max' _ _ hx))
  have := card_le_card hsub
  rw [card_range] at this
  exact C.vld_mono k _ u ((mem_occ_iff hS).1 hM).1 (by omega)

lemma mem_comp_iff {n : ℕ} (hn : 0 < n) : n ∈ C.comp S ↔ C.pos n < (C.occ S (C.key n)).card := by
  unfold comp
  rw [mem_biUnion]
  constructor
  · rintro ⟨k, -, hk⟩
    rw [mem_image] at hk
    obtain ⟨u, hu, rfl⟩ := hk
    rw [mem_range] at hu
    have hv := vld_of_lt_card hS hu
    rw [C.key_elt k u hv, C.pos_elt k u hv]
    exact hu
  · intro h
    obtain ⟨u, hu⟩ : (C.occ S (C.key n)).Nonempty := card_pos.1 (by omega)
    unfold occ at hu
    rw [mem_image] at hu
    obtain ⟨m, hm, -⟩ := hu
    rw [mem_filter] at hm
    exact ⟨C.key n, mem_image.2 ⟨m, hm.1, hm.2⟩,
      mem_image.2 ⟨C.pos n, mem_range.2 h, C.elt_key_pos n hn⟩⟩

lemma comp_pos : ∀ n ∈ C.comp S, 0 < n := by
  intro n hn
  unfold comp at hn
  rw [mem_biUnion] at hn
  obtain ⟨k, -, hk⟩ := hn
  rw [mem_image] at hk
  obtain ⟨u, hu, rfl⟩ := hk
  exact C.elt_pos k u (vld_of_lt_card hS (mem_range.1 hu))

lemma occ_comp (k : κ) : C.occ (C.comp S) k = range (C.occ S k).card := by
  ext u
  rw [mem_occ_iff (comp_pos hS), mem_range]
  constructor
  · rintro ⟨hv, hmem⟩
    have := (mem_comp_iff hS (C.elt_pos k u hv)).1 hmem
    rwa [C.key_elt k u hv, C.pos_elt k u hv] at this
  · intro hu
    have hv := vld_of_lt_card hS hu
    refine ⟨hv, (mem_comp_iff hS (C.elt_pos k u hv)).2 ?_⟩
    rwa [C.key_elt k u hv, C.pos_elt k u hv]

/-- On a chain, `pos` is injective. -/
lemma pos_injOn (k : κ) : Set.InjOn C.pos ↑(S.filter (fun n => C.key n = k)) := by
  intro x hx y hy hxy
  simp only [coe_filter, Set.mem_ofPred_eq] at hx hy
  rw [← C.elt_key_pos x (hS x hx.1), ← C.elt_key_pos y (hS y hy.1), hx.2, hy.2, hxy]

lemma card_fibre (k : κ) : (S.filter (fun n => C.key n = k)).card = (C.occ S k).card :=
  (card_image_of_injOn (pos_injOn hS k)).symm

lemma key_mem_of_mem_comp {n : ℕ} (hn : n ∈ C.comp S) : C.key n ∈ S.image C.key := by
  have hn0 := comp_pos hS n hn
  have h := (mem_comp_iff hS hn0).1 hn
  obtain ⟨u, hu⟩ : (C.occ S (C.key n)).Nonempty := card_pos.1 (by omega)
  unfold occ at hu
  rw [mem_image] at hu
  obtain ⟨m, hm, -⟩ := hu
  rw [mem_filter] at hm
  exact mem_image.2 ⟨m, hm.1, hm.2⟩

/-- Compression preserves cardinality. -/
theorem card_comp : (C.comp S).card = S.card := by
  rw [card_eq_sum_card_fiberwise (f := C.key) (t := S.image C.key)
      (fun n hn => key_mem_of_mem_comp hS hn),
    card_eq_sum_card_fiberwise (f := C.key) (t := S.image C.key)
      (fun n hn => mem_image_of_mem _ hn)]
  refine sum_congr rfl fun k _ => ?_
  rw [card_fibre (comp_pos hS), card_fibre hS, occ_comp hS, card_range]

/-- The sum of a set, chain by chain. -/
lemma sum_eq_sum_occ : ∑ n ∈ S, n = ∑ k ∈ S.image C.key, ∑ u ∈ C.occ S k, C.elt k u := by
  rw [← sum_fiberwise_of_maps_to (g := C.key) (t := S.image C.key)
    (fun n hn => mem_image_of_mem _ hn)]
  refine sum_congr rfl fun k _ => ?_
  unfold occ
  rw [sum_image (pos_injOn hS k)]
  refine sum_congr rfl fun n hn => ?_
  rw [mem_filter] at hn
  rw [← hn.2, C.elt_key_pos n (hS n hn.1)]

end basic

/-- Sum over an initial segment is at most the sum over any set of the same size, for a
function increasing on an initial segment containing the set; strictly if the set is not the
initial segment. -/
lemma sum_range_le_sum (f : ℕ → ℕ) (P : ℕ → Prop)
    (hf : ∀ u v, P v → u < v → f u < f v) :
    ∀ (s : ℕ) (E : Finset ℕ), E.card = s → (∀ u ∈ E, P u) →
      ∑ u ∈ range s, f u ≤ ∑ u ∈ E, f u ∧ (E ≠ range s → ∑ u ∈ range s, f u < ∑ u ∈ E, f u) := by
  intro s
  induction s with
  | zero =>
    intro E hE _
    rw [card_eq_zero] at hE
    subst hE
    simp
  | succ s ih =>
    intro E hE hP'
    have hne : E.Nonempty := card_pos.1 (by omega)
    set M := E.max' hne with hMdef
    have hME : M ∈ E := max'_mem _ _
    have hcard : (E.erase M).card = s := by rw [card_erase_of_mem hME, hE]; rfl
    obtain ⟨ih1, ih2⟩ := ih (E.erase M) hcard (fun u hu => hP' u (mem_of_mem_erase hu))
    -- the maximum is at least `s`
    have hsM : s ≤ M := by
      have hsub : E ⊆ range (M + 1) := fun x hx =>
        mem_range.2 (Nat.lt_succ_of_le (le_max' _ _ hx))
      have := card_le_card hsub
      rw [card_range] at this
      omega
    have hfs : f s ≤ f M := by
      rcases Nat.lt_or_eq_of_le hsM with h | h
      · exact (hf s M (hP' M hME) h).le
      · rw [h]
    rw [sum_range_succ, ← add_sum_erase E f hME]
    refine ⟨by linarith, fun hneq => ?_⟩
    rcases Nat.lt_or_eq_of_le hsM with h | h
    · have := hf s M (hP' M hME) h
      linarith
    · -- `M = s`, so the rest must differ from `range s`
      have hrest : E.erase M ≠ range s := by
        intro hcontra
        apply hneq
        ext x
        rw [mem_range]
        constructor
        · intro hx
          by_cases hxM : x = M
          · omega
          · have : x ∈ E.erase M := mem_erase.2 ⟨hxM, hx⟩
            rw [hcontra, mem_range] at this
            omega
        · intro hx
          by_cases hxs : x = s
          · rw [hxs, h]; exact hME
          · have : x ∈ range s := mem_range.2 (by omega)
            rw [← hcontra] at this
            exact mem_of_mem_erase this
      have := ih2 hrest
      have hfsM : f s = f M := by rw [h]
      linarith

/-- Compression does not increase the sum, and strictly decreases it if some chain has a gap. -/
theorem sum_comp_le {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n) :
    ∑ n ∈ C.comp S, n ≤ ∑ n ∈ S, n ∧
      ((∃ k, C.occ S k ≠ range (C.occ S k).card) → ∑ n ∈ C.comp S, n < ∑ n ∈ S, n) := by
  have hkeys : (C.comp S).image C.key ⊆ S.image C.key := by
    intro k hk
    rw [mem_image] at hk
    obtain ⟨n, hn, rfl⟩ := hk
    exact key_mem_of_mem_comp hS hn
  have hcompsum : ∑ n ∈ C.comp S, n =
      ∑ k ∈ S.image C.key, ∑ u ∈ range (C.occ S k).card, C.elt k u := by
    rw [← sum_fiberwise_of_maps_to (g := C.key) (t := S.image C.key)
      (fun n hn => key_mem_of_mem_comp hS hn)]
    refine sum_congr rfl fun k _ => ?_
    rw [← occ_comp hS k]
    unfold occ
    rw [sum_image (pos_injOn (comp_pos hS) k)]
    refine sum_congr rfl fun n hn => ?_
    rw [mem_filter] at hn
    rw [← hn.2, C.elt_key_pos n (comp_pos hS n hn.1)]
  have hchain : ∀ k, ∑ u ∈ range (C.occ S k).card, C.elt k u ≤ ∑ u ∈ C.occ S k, C.elt k u ∧
      (C.occ S k ≠ range (C.occ S k).card →
        ∑ u ∈ range (C.occ S k).card, C.elt k u < ∑ u ∈ C.occ S k, C.elt k u) := fun k =>
    sum_range_le_sum (C.elt k) (C.vld k)
      (fun u v hv huv => C.elt_lt k u v hv huv) _ _ rfl
      (fun u hu => ((mem_occ_iff hS).1 hu).1)
  rw [hcompsum, sum_eq_sum_occ (C := C) hS]
  refine ⟨sum_le_sum fun k _ => (hchain k).1, ?_⟩
  rintro ⟨k, hk⟩
  have hkS : k ∈ S.image C.key := by
    by_contra hk'
    apply hk
    have : C.occ S k = ∅ := by
      unfold occ
      rw [image_eq_empty, filter_eq_empty_iff]
      intro n hn hnk
      exact hk' (mem_image.2 ⟨n, hn, hnk⟩)
    rw [this]
    rfl
  exact sum_lt_sum (fun k _ => (hchain k).1) ⟨k, hkS, (hchain k).2 hk⟩

/-- **Lemma 1 + compression**: if every chain satisfies the window condition for `t`,
compression does not decrease `|A S t|`. -/
theorem card_A_le_comp {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n) (t : ℕ) (hC : ∀ k, C.Cons t k) :
    (A S t).card ≤ (A (C.comp S) t).card := by
  have hS' := comp_pos (C := C) hS
  rw [card_eq_sum_card_fiberwise (f := C.key) (t := S.image C.key)
      (fun n hn => mem_image_of_mem _ (A_subset S t hn)),
    card_eq_sum_card_fiberwise (f := C.key) (t := S.image C.key)
      (fun n hn => key_mem_of_mem_comp hS (A_subset _ t hn))]
  refine sum_le_sum fun k _ => ?_
  obtain ⟨ι, I, tgt, Lc, hvld, hiff⟩ := hC k
  classical
  -- the valid starting positions along chain `k`
  let V : Finset ℕ → Finset ℕ := fun T => (C.occ T k).filter
    (fun e => ∀ i ∈ I, ∀ h ∈ range (Lc i + 1), e + h ∈ C.occ T (tgt i))
  -- the fibre of `A T t` over `k` is in bijection with `V T`
  have hfib : ∀ T : Finset ℕ, (∀ n ∈ T, 0 < n) →
      ((A T t).filter (fun n => C.key n = k)).card = (V T).card := by
    intro T hT
    have hsub : (A T t).filter (fun n => C.key n = k) ⊆ T.filter (fun n => C.key n = k) :=
      filter_subset_filter _ (A_subset T t)
    rw [← card_image_of_injOn (Set.InjOn.mono (by exact_mod_cast hsub) (pos_injOn hT k))]
    congr 1
    ext e
    simp only [mem_image, mem_filter, V, mem_range]
    constructor
    · rintro ⟨n, ⟨hnA, hnk⟩, rfl⟩
      have hn0 := hT n (A_subset T t hnA)
      have hv : C.vld k (C.pos n) := by rw [← hnk]; exact C.vld_key_pos n hn0
      have helt : C.elt k (C.pos n) = n := by rw [← hnk]; exact C.elt_key_pos n hn0
      have := (hiff T hT (C.pos n) hv).1 (by rw [helt]; exact hnA)
      refine ⟨(mem_occ_iff hT).2 ⟨hv, this.1⟩, fun i hi h hh => ?_⟩
      exact (mem_occ_iff hT).2 ⟨hvld _ hv i hi h (by omega), this.2 i hi h (by omega)⟩
    · rintro ⟨he, hcons⟩
      obtain ⟨hv, hmem⟩ := (mem_occ_iff hT).1 he
      refine ⟨C.elt k e, ⟨(hiff T hT e hv).2 ⟨hmem, fun i hi h hh => ?_⟩,
        C.key_elt k e hv⟩, C.pos_elt k e hv⟩
      exact ((mem_occ_iff hT).1 (hcons i hi h (by omega))).2
  rw [hfib S hS, hfib _ hS']
  -- Lemma 1: `|V S| + Lc i ≤ |occ S (tgt i)|`
  have hwin : ∀ i ∈ I, (V S).Nonempty → (V S).card + Lc i ≤ (C.occ S (tgt i)).card := by
    intro i hi hne
    set e₀ := (V S).max' hne
    have he₀ : e₀ ∈ V S := max'_mem _ _
    have hdisj : Disjoint (V S) ((Icc 1 (Lc i)).image (fun h => e₀ + h)) := by
      rw [disjoint_left]
      intro x hx hx'
      rw [mem_image] at hx'
      obtain ⟨h, hh, rfl⟩ := hx'
      rw [mem_Icc] at hh
      have := le_max' (V S) _ hx
      omega
    have hsub : V S ∪ (Icc 1 (Lc i)).image (fun h => e₀ + h) ⊆ C.occ S (tgt i) := by
      intro x hx
      rw [mem_union] at hx
      rcases hx with hx | hx
      · have := (mem_filter.1 hx).2 i hi 0 (mem_range.2 (Nat.succ_pos _))
        simpa using this
      · rw [mem_image] at hx
        obtain ⟨h, hh, rfl⟩ := hx
        rw [mem_Icc] at hh
        exact (mem_filter.1 he₀).2 i hi h (mem_range.2 (by omega))
    have := card_le_card hsub
    rw [card_union_of_disjoint hdisj, card_image_of_injective _ (add_right_injective e₀),
      Nat.card_Icc] at this
    omega
  -- after compression, the first `|V S|` positions are valid starts
  have hrange : range (V S).card ⊆ V (C.comp S) := by
    intro e he
    rw [mem_range] at he
    have hne : (V S).Nonempty := card_pos.1 (by omega)
    have hVocc : (V S).card ≤ (C.occ S k).card := card_le_card (filter_subset _ _)
    simp only [V, mem_filter, occ_comp hS, mem_range]
    refine ⟨by omega, fun i hi h hh => ?_⟩
    have := hwin i hi hne
    omega
  have := card_le_card hrange
  rwa [card_range] at this

end ChainSys

end RunsOfMultiples
