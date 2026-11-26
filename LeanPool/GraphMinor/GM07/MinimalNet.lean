/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs

/-!
# From a normal net to a minimal net

A minimal net (Graph Minors VII, Section 2, page 216) minimizes first a natural number and then
another, over all `G`-normal nets. So a `G`-normal net gives a minimal net
(`Net.exists_isMinimalFor`). Fibers of a net are finite (`Net.finite_fiber`), so the first of these
numbers counts what it should.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-- If there is a `G`-normal net, then there is a minimal net with respect to `G`. -/
theorem Net.exists_isMinimalFor {G : Drawing S} {N₀ : Net S} (h : N₀.IsNormalFor G) : ∃ N : Net S,
  N.IsMinimalFor G := by
  classical
  have h1 : ∃ n, ∃ N : Net S, N.IsNormalFor G ∧ N.bdVertexPreimageCard G = n := ⟨_, N₀, h, rfl⟩
  obtain ⟨N₁, hN₁, hc⟩ := Nat.find_spec h1
  have h2 : ∃ m, ∃ N : Net S, N.IsNormalFor G ∧ N.bdVertexPreimageCard G = Nat.find h1 ∧ N.r = m
    := ⟨_, N₁, hN₁, hc, rfl⟩
  obtain ⟨N, hN, hc', hr⟩ := Nat.find_spec h2
  refine ⟨N, hN, fun N' hN' => ?_, fun N' hN' hle => ?_⟩
  · rw [hc']
    exact Nat.find_min' h1 ⟨N', hN', rfl⟩
  · have hge : Nat.find h1 ≤ N'.bdVertexPreimageCard G := Nat.find_min' h1 ⟨N', hN', rfl⟩
    rw [hr]
    exact Nat.find_min' h2 ⟨N', hN', le_antisymm (hc' ▸ hle) hge, rfl⟩

theorem Net.mem_Ioo_of_ne {t : unitInterval} (h0 : t ≠ 0) (h1 : t ≠ 1) : t ∈ Ioo
  (0 : unitInterval) 1 :=
  ⟨unitInterval.pos_iff_ne_zero.mpr h0, unitInterval.lt_one_iff_ne_one.mpr h1⟩

/-- The ends of the arcs of a net. -/
def Net.ends (N : Net S) : Set N.D :=
  {z | ∃ i, z = N.f i 0 ∨ z = N.f i 1 ∨ z = N.g i 0 ∨ z = N.g i 1}

theorem Net.finite_ends (N : Net S) : N.ends.Finite := by
  have : N.ends = ⋃ i, {N.f i 0, N.f i 1, N.g i 0, N.g i 1} := by
    ext z
    simp [Net.ends]
  rw [this]
  exact finite_iUnion fun i => by simp

theorem Net.f_eq_iff (N : Net S) {i j : Fin N.r} {t t' : unitInterval} (ht : t ∈ Ioo
  (0 : unitInterval) 1) (h : N.f i t = N.f j t') : i = j ∧ t = t' := by
  by_cases hij : i = j
  · subst hij
    exact ⟨rfl, N.injective_f i h⟩
  · exact (N.internally_disjoint_ff i j hij t ht ⟨t', h.symm⟩).elim

theorem Net.g_eq_iff (N : Net S) {i j : Fin N.r} {t t' : unitInterval} (ht : t ∈ Ioo
  (0 : unitInterval) 1) (h : N.g i t = N.g j t') : i = j ∧ t = t' := by
  by_cases hij : i = j
  · subst hij
    exact ⟨rfl, N.injective_g i h⟩
  · exact (N.internally_disjoint_gg i j hij t ht ⟨t', h.symm⟩).elim

/-- A point inside an arc is not an end of any arc. -/
theorem Net.f_notMem_ends (N : Net S) {i : Fin N.r} {t : unitInterval} (ht : t ∈ Ioo
  (0 : unitInterval) 1) : N.f i t ∉ N.ends := by
  rintro ⟨j, h | h | h | h⟩
  · exact ht.1.ne' (N.f_eq_iff ht h).2
  · exact ht.2.ne (N.f_eq_iff ht h).2
  · exact N.internally_disjoint_fg i j t ht ⟨0, h.symm⟩
  · exact N.internally_disjoint_fg i j t ht ⟨1, h.symm⟩

theorem Net.g_notMem_ends (N : Net S) {i : Fin N.r} {t : unitInterval} (ht : t ∈ Ioo
  (0 : unitInterval) 1) : N.g i t ∉ N.ends := by
  rintro ⟨j, h | h | h | h⟩
  · exact N.internally_disjoint_gf i j t ht ⟨0, h.symm⟩
  · exact N.internally_disjoint_gf i j t ht ⟨1, h.symm⟩
  · exact ht.1.ne' (N.g_eq_iff ht h).2
  · exact ht.2.ne (N.g_eq_iff ht h).2

/-- A set closed under one pasting step in both directions is closed under `φ`-equality. -/
theorem Net.mem_of_eq (N : Net S) {C : Set N.D} (hC : ∀ i t, N.f i t ∈ C ↔ N.g i t ∈ C) {x y : N.D}
  (hxy : N.φ x = N.φ y) (hx : x ∈ C) : y ∈ C := by
  have h := (N.bd_eq_iff x y).mp hxy
  have key : ∀ a b, Relation.EqvGen (fun a b : N.D => ∃ (i : Fin N.r) (t : unitInterval), a
    = N.f i t ∧ b = N.g i t) a b → (a ∈ C ↔ b ∈ C) := by
    intro a b hab
    induction hab with
    | rel a b h =>
      obtain ⟨i, t, rfl, rfl⟩ := h
      exact hC i t
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ h1 h2 => exact h1.trans h2
  exact (key x y h).mp hx

/-- **Fibers of a net are finite.** Interior points have singleton fibers, a point inside an arc has
the class `{f i t, g i t}`, the ends form a finite set closed under pasting, and a point on no arc
is alone.
So `bdVertexPreimageCard` counts what it should. -/
theorem Net.finite_fiber (N : Net S) (z : S) : (N.φ ⁻¹' {z}).Finite := by
  classical
  by_cases hne : (N.φ ⁻¹' {z}).Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty.mp hne]
    exact finite_empty
  obtain ⟨x, hx⟩ := hne
  have hsub : ∀ C : Set N.D, C.Finite → (∀ i t, N.f i t ∈ C ↔ N.g i t ∈ C) → x ∈ C →
    (N.φ ⁻¹' {z}).Finite := fun C hf hC hxC =>
    hf.subset fun y hy => N.mem_of_eq hC (hx.trans hy.symm) hxC
  by_cases hE : x ∈ N.ends
  · refine hsub N.ends N.finite_ends (fun i t => ?_) hE
    by_cases h0 : t = 0
    · subst h0
      exact ⟨fun _ => ⟨i, .inr (.inr (.inl rfl))⟩, fun _ => ⟨i, .inl rfl⟩⟩
    by_cases h1 : t = 1
    · subst h1
      exact ⟨fun _ => ⟨i, .inr (.inr (.inr rfl))⟩, fun _ => ⟨i, .inr (.inl rfl)⟩⟩
    have ht := Net.mem_Ioo_of_ne h0 h1
    exact ⟨fun h => (N.f_notMem_ends ht h).elim, fun h => (N.g_notMem_ends ht h).elim⟩
  by_cases hA : ∃ i, ∃ t ∈ Ioo (0 : unitInterval) 1, x = N.f i t ∨ x = N.g i t
  · obtain ⟨i, t, ht, hxt⟩ := hA
    refine hsub {N.f i t, N.g i t} (by simp) (fun j t' => ?_) (by rcases hxt with h | h
      <;> simp [h])
    have hfg : ∀ a : unitInterval, N.f i t ≠ N.g j a := fun a h => N.internally_disjoint_fg i j t
      ht ⟨a, h.symm⟩
    have hgf : ∀ a : unitInterval, N.g i t ≠ N.f j a := fun a h => N.internally_disjoint_gf i j t
      ht ⟨a, h.symm⟩
    simp only [mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro (h | h)
      · obtain ⟨rfl, rfl⟩ := N.f_eq_iff ht h.symm
        exact .inr rfl
      · exact (hgf _ h.symm).elim
    · rintro (h | h)
      · exact (hfg _ h.symm).elim
      · obtain ⟨rfl, rfl⟩ := N.g_eq_iff ht h.symm
        exact .inl rfl
  · refine hsub {x} (finite_singleton x) (fun i t => ?_) rfl
    have hf : N.f i t ≠ x := fun h => by
      by_cases h0 : t = 0
      · exact hE ⟨i, .inl (by rw [← h, h0])⟩
      by_cases h1 : t = 1
      · exact hE ⟨i, .inr (.inl (by rw [← h, h1]))⟩
      exact hA ⟨i, t, Net.mem_Ioo_of_ne h0 h1, .inl h.symm⟩
    have hg : N.g i t ≠ x := fun h => by
      by_cases h0 : t = 0
      · exact hE ⟨i, .inr (.inr (.inl (by rw [← h, h0])))⟩
      by_cases h1 : t = 1
      · exact hE ⟨i, .inr (.inr (.inr (by rw [← h, h1])))⟩
      exact hA ⟨i, t, Net.mem_Ioo_of_ne h0 h1, .inr h.symm⟩
    simp [hf, hg]

end GraphMinor.GM07
