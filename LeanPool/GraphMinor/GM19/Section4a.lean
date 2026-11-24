/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Defs2
public import Mathlib.Data.Multiset.DershowitzManna

/-!
# Graph Minors XIX, (4.3) and (4.4)

We show that a well-quasi-order has no infinite strictly descending chain of sub-ideals (4.3), and
that a sequence of colour schemes cannot go on refining for ever (4.4).

The paper proves (4.4) with König's lemma on a tree of long sides. We use the same facts in a
shorter
form. A refinement replaces each long side by finitely many smaller ones, or leaves it alone. So the
multiset of quasi-orders of the long sides goes down in the Dershowitz–Manna order, unless nothing
changes, and then the third condition of a refinement makes the number of short sides go down.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Function Topology GraphMinor.Surface

universe u w

variable {α : Type w}

namespace QuasiOrder

/-- The relation `≼` is reflexive. -/
theorem IsSubIdeal.refl (Ω : QuasiOrder α) : Ω.IsSubIdeal Ω :=
  ⟨Subset.rfl, fun _ _ _x hx _ ↦ hx, fun _ _ _ _ ↦ Iff.rfl⟩

/-- The relation `≼` is transitive. -/
theorem IsSubIdeal.trans {Ω₁ Ω₂ Ω₃ : QuasiOrder α} (h₁ : Ω₁.IsSubIdeal Ω₂)
    (h₂ : Ω₂.IsSubIdeal Ω₃) : Ω₁.IsSubIdeal Ω₃ where
  E_subset := h₁.E_subset.trans h₂.E_subset
  downward_closed x' hx' x hx hle := by
    have hx'2 := h₁.E_subset hx'
    have hx2 := h₂.downward_closed x' hx'2 x hx hle
    exact h₁.downward_closed x' hx' x hx2 ((h₂.le_iff x hx2 x' hx'2).2 hle)
  le_iff x hx y hy := (h₁.le_iff x hx y hy).trans
    (h₂.le_iff x (h₁.E_subset hx) y (h₁.E_subset hy))

/-- **Graph Minors XIX, (4.3).** A well-quasi-order starts no infinite chain `Ω₁ ≻ Ω₂ ≻ ⋯`. The
paper omits the proof. Choose `x_i ∈ E(Ω_i) \ E(Ω_{i+1})`. Then `x_i ≤ x_j` for some `i < j`, and as
`E(Ω_{i+1})` is closed downward and contains `x_j`, it contains `x_i`, a contradiction. -/
theorem theorem_4_3_proof (Ω : ℕ → QuasiOrder α) (hwqo : (Ω 0).IsWQO)
    (hstrict : ∀ i, (Ω (i + 1)).IsStrictSubIdeal (Ω i)) : False := by
  have hsub : ∀ i k, (Ω (i + k)).IsSubIdeal (Ω i) := by
    intro i k
    induction k with
    | zero => exact IsSubIdeal.refl _
    | succ k ih => exact (hstrict (i + k)).1.trans ih
  have hex : ∀ i, ∃ x, x ∈ (Ω i).E ∧ x ∉ (Ω (i + 1)).E := by
    intro i
    by_contra hno
    push Not at hno
    exact (hstrict i).2 (Subset.antisymm (hstrict i).1.E_subset hno)
  choose x hx hx' using hex
  obtain ⟨i, j, hij, hle⟩ := hwqo x fun i ↦ by
    have := hsub 0 i
    rw [Nat.zero_add] at this
    exact this.E_subset (hx i)
  obtain ⟨k, rfl⟩ : ∃ k, j = i + 1 + k := ⟨j - (i + 1), by omega⟩
  have h0 : ∀ i, (Ω i).IsSubIdeal (Ω 0) := fun i ↦ by simpa using hsub 0 i
  have hxj : x (i + 1 + k) ∈ (Ω (i + 1)).E := (hsub (i + 1) k).E_subset (hx _)
  exact hx' i ((h0 (i + 1)).downward_closed _ hxj (x i) ((h0 i).E_subset (hx i)) hle)

/-- `Ω` with its relation cut down to `E(Ω)`, so that only this part of the relation matters. -/
def norm (Ω : QuasiOrder α) : QuasiOrder α where
  E := Ω.E
  le x y := x ∈ Ω.E ∧ y ∈ Ω.E ∧ Ω.le x y
  refl x hx := ⟨hx, hx, Ω.refl x hx⟩
  trans x hx y hy z hz h₁ h₂ := ⟨hx, hz, Ω.trans x hx y hy z hz h₁.2.2 h₂.2.2⟩

theorem norm_isWQO {Ω : QuasiOrder α} (h : Ω.IsWQO) : Ω.norm.IsWQO := fun f hf ↦ by
  obtain ⟨i, j, hij, hle⟩ := h f hf
  exact ⟨i, j, hij, hf i, hf j, hle⟩

theorem IsSubIdeal.norm {Ω' Ω : QuasiOrder α} (h : Ω'.IsSubIdeal Ω) : Ω'.norm.IsSubIdeal Ω.norm
  where
  E_subset := h.E_subset
  downward_closed x' hx' x hx hle := h.downward_closed x' hx' x hx hle.2.2
  le_iff x hx y hy := by
    constructor
    · exact fun hle ↦ ⟨h.E_subset hx, h.E_subset hy, (h.le_iff x hx y hy).1 hle.2.2⟩
    · exact fun hle ↦ ⟨hx, hy, (h.le_iff x hx y hy).2 hle.2.2⟩

/-- Two quasi-orders with the same element set, each a sub-ideal of the other's relation, agree
after
`norm`. -/
theorem IsSubIdeal.norm_eq {Ω' Ω : QuasiOrder α} (h : Ω'.IsSubIdeal Ω) (hE : Ω'.E = Ω.E) :
    Ω'.norm = Ω.norm := by
  have hle : (Ω'.norm).le = (Ω.norm).le := by
    funext x y
    apply propext
    constructor
    · exact fun hxy ↦ ⟨hE ▸ hxy.1, hE ▸ hxy.2.1, (h.le_iff x hxy.1 y hxy.2.1).1 hxy.2.2⟩
    · intro hxy
      have hx : x ∈ Ω'.E := hE ▸ hxy.1
      have hy : y ∈ Ω'.E := hE ▸ hxy.2.1
      exact ⟨hx, hy, (h.le_iff x hx y hy).2 hxy.2.2⟩
  have hE' : (Ω'.norm).E = (Ω.norm).E := hE
  cases hA : Ω'.norm
  cases hB : Ω.norm
  simp only [hA, hB] at hE' hle
  subst hE'
  subst hle
  rfl

end QuasiOrder

/-- The well-quasi-orders on `α`, ordered by `≼`. -/
def WQOKey (α : Type w) : Type w := {Ω : QuasiOrder α // Ω.IsWQO}

instance : Preorder (WQOKey α) where
  le a b := a.1.IsSubIdeal b.1
  le_refl a := QuasiOrder.IsSubIdeal.refl a.1
  le_trans _ _ _ h₁ h₂ := QuasiOrder.IsSubIdeal.trans h₁ h₂

theorem WQOKey.lt_iff {a b : WQOKey α} : a < b ↔ a.1.IsStrictSubIdeal b.1 := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, fun hE ↦ h₂ ⟨hE.ge, fun _ _ x hx _ ↦ hE ▸ hx, fun x hx y hy ↦ ?_⟩⟩
    exact (h₁.le_iff x (hE ▸ hx) y (hE ▸ hy)).symm
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, fun h ↦ h₂ (Subset.antisymm h₁.E_subset h.E_subset)⟩

instance : WellFoundedLT (WQOKey α) := by
  suffices h : WellFounded ((· < ·) : WQOKey α → WQOKey α → Prop) from ⟨h.apply⟩
  rw [RelEmbedding.wellFounded_iff_isEmpty]
  refine ⟨fun g ↦ ?_⟩
  exact QuasiOrder.theorem_4_3_proof (fun i ↦ (g i).1) (g 0).2 fun i ↦
    WQOKey.lt_iff.1 (g.map_rel_iff.2 (Nat.lt_succ_self i))

section Refinement



variable {S₁ S₂ : Type u} [TopologicalSpace S₁] [TopologicalSpace S₂]

open Classical in
theorem Frame.finite_longSides (Φ : Frame S₁) : Φ.longSides.Finite :=
  Φ.finite_sides.subset fun _ h ↦ h.1

open Classical in
/-- The element of `WQOKey α` of a long side. -/
noncomputable def ColourScheme.key (χ : ColourScheme S₁ α) (s : Set S₁) : WQOKey α :=
  if h : s ∈ χ.Φ.sides then ⟨(χ.ΩS s).norm, QuasiOrder.norm_isWQO (χ.isWQO_S s h)⟩
  else ⟨χ.Ω2.norm, QuasiOrder.norm_isWQO χ.isWQO_2⟩

open Classical in
theorem ColourScheme.key_of_mem (χ : ColourScheme S₁ α) {s : Set S₁} (h : s ∈ χ.Φ.sides) :
    (χ.key s).1 = (χ.ΩS s).norm := by
  simp [ColourScheme.key, h]

open Classical in
/-- The multiset of the quasi-orders of the long sides. -/
noncomputable def ColourScheme.longMultiset (χ : ColourScheme S₁ α) : Multiset (WQOKey α) :=
  ∑ s ∈ χ.Φ.finite_longSides.toFinset, {χ.key s}

open Classical in
/-- One refinement lowers the multiset of quasi-orders, or keeps it and lowers the number of short
sides. -/
theorem ColourScheme.IsRefinement.step {χ' : ColourScheme S₁ α} {χ : ColourScheme S₂ α}
    (h : χ'.IsRefinement χ) :
    Prod.Lex Multiset.IsDershowitzMannaLT (· < ·)
      (χ'.longMultiset, χ'.Φ.shortSides.ncard) (χ.longMultiset, χ.Φ.shortSides.ncard) := by
  obtain ⟨-, -, -, f, hmaps, hsub, hstrict, hthird⟩ := h
  set L' := χ'.Φ.finite_longSides.toFinset with hL'
  set L := χ.Φ.finite_longSides.toFinset with hL
  have memL' : ∀ {R}, R ∈ L' ↔ R ∈ χ'.Φ.longSides := by simp [hL']
  have memL : ∀ {s}, s ∈ L ↔ s ∈ χ.Φ.longSides := by simp [hL]
  let good : Set S₂ → Prop := fun s ↦ ∃ R ∈ L', f R = s ∧ (∀ R' ∈ L', f R' = s → R' = R) ∧
    (χ'.ΩS R).E = (χ.ΩS s).E
  have hkey : ∀ R ∈ L', (χ'.ΩS R).E = (χ.ΩS (f R)).E → χ'.key R = χ.key (f R) := by
    intro R hR hE
    have hR' := memL'.1 hR
    apply Subtype.ext
    rw [χ'.key_of_mem hR'.1, χ.key_of_mem (hmaps hR').1]
    exact (hsub R hR').norm_eq hE
  have hX : ∑ R ∈ L'.filter (fun R ↦ good (f R)), ({χ'.key R} : Multiset (WQOKey α)) =
      ∑ s ∈ L.filter good, {χ.key s} := by
    refine Finset.sum_bij (fun R _ ↦ f R) ?_ ?_ ?_ ?_
    · intro R hR
      obtain ⟨hR1, hg⟩ := Finset.mem_filter.1 hR
      exact Finset.mem_filter.2 ⟨memL.2 (hmaps (memL'.1 hR1)), hg⟩
    · intro R₁ h₁ R₂ h₂ he
      obtain ⟨hR1, R, -, hRf, huniq, -⟩ := Finset.mem_filter.1 h₁
      have hR2 := (Finset.mem_filter.1 h₂).1
      rw [huniq R₁ hR1 rfl, huniq R₂ hR2 he.symm]
    · intro s hs
      obtain ⟨-, R, hR, hRf, huniq, hE⟩ := Finset.mem_filter.1 hs
      subst hRf
      exact ⟨R, Finset.mem_filter.2 ⟨hR, R, hR, rfl, huniq, hE⟩, rfl⟩
    · intro R hR
      obtain ⟨hR1, R₀, hR₀, hRf, huniq, hE⟩ := Finset.mem_filter.1 hR
      obtain rfl := huniq R hR1 rfl
      rw [hkey _ hR₀ hE]
  have hM' : χ'.longMultiset = ∑ s ∈ L.filter good, {χ.key s} +
      ∑ R ∈ L'.filter (fun R ↦ ¬ good (f R)), {χ'.key R} := by
    rw [← hX, ColourScheme.longMultiset, Finset.sum_filter_add_sum_filter_not]
  have hM : χ.longMultiset = ∑ s ∈ L.filter good, {χ.key s} +
      ∑ s ∈ L.filter (fun s ↦ ¬ good s), {χ.key s} := by
    rw [ColourScheme.longMultiset, Finset.sum_filter_add_sum_filter_not]
  by_cases hB : (L.filter fun s ↦ ¬ good s) = ∅
  · have hall : ∀ s ∈ L, good s := by
      intro s hs
      by_contra hg
      have : s ∈ L.filter fun s ↦ ¬ good s := Finset.mem_filter.2 ⟨hs, hg⟩
      rw [hB] at this
      simp at this
    have hA : (L'.filter fun R ↦ ¬ good (f R)) = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      intro R hR
      simpa using hall _ (memL.2 (hmaps (memL'.1 hR)))
    have hEq : χ'.longMultiset = χ.longMultiset := by
      rw [hM', hM, hA, hB]
      simp
    rw [hEq]
    refine Prod.Lex.right _ (hthird fun s hs ↦ ?_)
    obtain ⟨R, hR, hRf, -, hE⟩ := hall s (memL.2 hs)
    exact ⟨R, memL'.1 hR, hRf, hE⟩
  · refine Prod.Lex.left _ _ ⟨_, _, _, ?_, hM', hM, ?_⟩
    · obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.2 hB
      intro h0
      have hmem : χ.key s ∈ ∑ s ∈ L.filter (fun s ↦ ¬ good s), ({χ.key s} : Multiset _) :=
        Multiset.mem_sum.2 ⟨s, hs, by simp⟩
      have h0' : ∑ s ∈ L.filter (fun s ↦ ¬ good s), ({χ.key s} : Multiset _) = 0 := h0
      rw [h0'] at hmem
      simp at hmem
    · intro y hy
      obtain ⟨R, hR, hyR⟩ := Multiset.mem_sum.1 hy
      obtain ⟨hR1, hg⟩ := Finset.mem_filter.1 hR
      rw [Multiset.mem_singleton] at hyR
      subst hyR
      have hR' := memL'.1 hR1
      have hfR : f R ∈ χ.Φ.longSides := hmaps hR'
      refine ⟨χ.key (f R), Multiset.mem_sum.2 ⟨f R, Finset.mem_filter.2 ⟨memL.2 hfR, hg⟩, by simp⟩,
        ?_⟩
      rw [WQOKey.lt_iff, χ'.key_of_mem hR'.1, χ.key_of_mem hfR.1]
      by_cases huniq : ∀ R' ∈ L', f R' = f R → R' = R
      · refine ⟨(hsub R hR').norm, fun hE ↦ hg ⟨R, hR1, rfl, huniq, hE⟩⟩
      · push Not at huniq
        obtain ⟨R', hR'1, hff, hne⟩ := huniq
        have := hstrict R hR' R' (memL'.1 hR'1) hne.symm hff.symm
        exact ⟨this.1.norm, this.2⟩

end Refinement

open Classical in
/-- **Graph Minors XIX, (4.4).** There is no sequence `χ_i` of colour schemes such that `χ_{i+1}` is
a
refinement of `χ_i` for all `i`. -/
theorem theorem_4_4_proof (S : ℕ → Type u) [∀ i, TopologicalSpace (S i)]
    (χ : ∀ i, ColourScheme (S i) α) (h : ∀ i, (χ (i + 1)).IsRefinement (χ i)) : False := by
  have hwf : WellFounded (Prod.Lex (Multiset.IsDershowitzMannaLT (α := WQOKey α)) (· < · : ℕ → ℕ
    → Prop)) :=
    WellFounded.prod_lex Multiset.wellFounded_isDershowitzMannaLT wellFounded_lt
  obtain ⟨_, ⟨i, rfl⟩, hmin⟩ := hwf.has_min
    (range fun i ↦ ((χ i).longMultiset, (χ i).Φ.shortSides.ncard)) ⟨_, ⟨0, rfl⟩⟩
  exact hmin _ ⟨i + 1, rfl⟩ (h i).step

end GraphMinor.GM19
