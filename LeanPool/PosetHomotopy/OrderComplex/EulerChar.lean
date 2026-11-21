/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.OrderComplex
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Euler characteristics of posets (roadmap 3.5)

The Euler characteristic of a preorder (`chainEulerChar`) is the alternating count
`Σ (-1) ^ (#σ + 1)` of its nonempty finite chains, the faces of its order complex. For a finite
partial order it is computed on finite subsets (`chainSum`), and three sign-reversing
involutions, adding or removing one vertex of a chain, compute it:

* `chainSum_eq_one_of_isLeast`: a finite poset with a least element has Euler characteristic `1`;
* `chainSum_erase_of_isLeast`: removing an element `x` such that the elements above `x` have a
  least one does not change the Euler characteristic (the combinatorial shadow of the removal
  of an up beat point, roadmap 1.3);
* `chainSum_eq_one_of_closure`: a finite poset with a closure operator whose closed elements have
  a least one has Euler characteristic `1`. This is the combinatorial form of Quillen's conical
  contractibility (roadmap 3.3, D. Quillen, « Homotopy properties of the poset of nontrivial
  p-subgroups of a group », Adv. Math. 28 (1978), 101–128, 1.5) used for Brown's theorem.

The identification of `chainEulerChar` with the Euler characteristic of the realization is Tau
Ceti's `AbstractSimplicialComplex.eulerChar_realization`, whose module does not build at the
pinned versions; it is not used here.
-/

@[expose] public section

open Finset

namespace LeanPool.PosetHomotopy

universe u

/-- **Roadmap 3.5.** The Euler characteristic of a preorder: the alternating count
`Σ (-1) ^ (#σ + 1)` of its nonempty finite chains. -/
noncomputable def chainEulerChar (T : Type u) [Preorder T] : ℤ :=
  ∑ᶠ σ : TauCeti.SetLike.Face (TauCeti.AbstractSimplicialComplex.orderComplex T),
    (-1 : ℤ) ^ (σ.1.card + 1)

section Toggle

variable {T : Type u}

/-- Adding or removing the vertex `m`. -/
def toggle [DecidableEq T] (m : T) (σ : Finset T) : Finset T :=
  if m ∈ σ then σ.erase m else insert m σ

theorem toggle_toggle [DecidableEq T] (m : T) (σ : Finset T) : toggle m (toggle m σ) = σ := by
  unfold toggle
  by_cases h : m ∈ σ
  · simp [h, Finset.insert_erase h]
  · simp [h, Finset.erase_insert h]

theorem mem_toggle_iff [DecidableEq T] (m : T) (σ : Finset T) :
    m ∈ toggle m σ ↔ m ∉ σ := by
  unfold toggle
  by_cases h : m ∈ σ <;> simp [h]

theorem sign_toggle [DecidableEq T] (m : T) (σ : Finset T) :
    (-1 : ℤ) ^ (σ.card + 1) + (-1) ^ ((toggle m σ).card + 1) = 0 := by
  unfold toggle
  split_ifs with h
  · rw [← Finset.card_erase_add_one h, pow_succ]; ring
  · rw [Finset.card_insert_of_notMem h, pow_succ]; ring

theorem toggle_ne [DecidableEq T] (m : T) (σ : Finset T) : toggle m σ ≠ σ := fun h => by
  have := mem_toggle_iff m σ
  rw [h] at this
  tauto

end Toggle

section Finite

variable {T : Type u} [PartialOrder T]

/-- A nonempty finite chain. -/
def IsChainFinset (σ : Finset T) : Prop := σ.Nonempty ∧ IsChain (· ≤ ·) (σ : Set T)

open Classical in
/-- The alternating count of the nonempty chains contained in a finite set. -/
noncomputable def chainSum (S : Finset T) : ℤ :=
  ∑ σ ∈ S.powerset with IsChainFinset σ, (-1 : ℤ) ^ (σ.card + 1)

/-- If every element of `σ` is comparable with `m`, toggling `m` keeps a chain. -/
theorem isChain_toggle [DecidableEq T] {m : T} {σ : Finset T}
    (hσ : IsChain (· ≤ ·) (σ : Set T)) (hm : ∀ y ∈ σ, y ≤ m ∨ m ≤ y) :
    IsChain (· ≤ ·) (toggle m σ : Set T) := by
  unfold toggle
  split_ifs
  · exact hσ.mono (by simp)
  · rw [Finset.coe_insert]
    exact hσ.insert fun y hy _ => (hm y hy).symm

/-- **Roadmap 3.5.** A finite poset with a least element has Euler characteristic `1`: toggling
the least element pairs off every chain but the singleton. -/
theorem chainSum_eq_one_of_isLeast {S : Finset T} {m : T} (hm : m ∈ S)
    (hle : ∀ z ∈ S, m ≤ z) : chainSum S = 1 := by
  classical
  unfold chainSum
  have hmem : ({m} : Finset T) ∈ S.powerset.filter IsChainFinset := by
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.singleton_subset_iff]
    exact ⟨hm, Finset.singleton_nonempty m, by simp⟩
  rw [← Finset.add_sum_erase _ _ hmem, Finset.card_singleton,
    show ((-1 : ℤ)) ^ (1 + 1) = 1 by norm_num, add_eq_left]
  refine Finset.sum_involution (fun σ _ => toggle m σ) (fun σ _ => sign_toggle m σ)
    (fun σ _ _ => toggle_ne m σ) (fun σ hσ => ?_) (fun σ _ => toggle_toggle m σ)
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_powerset] at hσ ⊢
  obtain ⟨hne, hS, hne', hch⟩ := hσ
  have hcmp : ∀ y ∈ σ, y ≤ m ∨ m ≤ y := fun y hy => Or.inr (hle y (hS hy))
  refine ⟨?_, ?_, ?_, isChain_toggle hch hcmp⟩
  · intro h
    unfold toggle at h
    split_ifs at h with hmσ
    · obtain ⟨y, hy⟩ := hne'
      by_cases hym : y = m
      · subst hym
        obtain ⟨z, hz, hzy⟩ : ∃ z ∈ σ, z ≠ y := by
          by_contra hc
          push Not at hc
          exact hne (Finset.eq_singleton_iff_unique_mem.2 ⟨hy, hc⟩)
        have : z ∈ σ.erase y := Finset.mem_erase.2 ⟨hzy, hz⟩
        rw [h] at this
        exact hzy (Finset.mem_singleton.1 this)
      · have : y ∈ σ.erase m := Finset.mem_erase.2 ⟨hym, hy⟩
        rw [h] at this
        exact hym (Finset.mem_singleton.1 this)
    · have : ∀ y ∈ σ, y = m := fun y hy => by
        have : y ∈ insert m σ := Finset.mem_insert_of_mem hy
        rw [h] at this
        exact Finset.mem_singleton.1 this
      obtain ⟨y, hy⟩ := hne'
      exact hmσ (this y hy ▸ hy)
  · unfold toggle
    split_ifs
    · exact (Finset.erase_subset _ _).trans hS
    · exact Finset.insert_subset hm hS
  · unfold toggle
    split_ifs with hmσ
    · obtain ⟨y, hy⟩ := hne'
      by_cases hym : y = m
      · subst hym
        obtain ⟨z, hz, hzy⟩ : ∃ z ∈ σ, z ≠ y := by
          by_contra hc
          push Not at hc
          exact hne (Finset.eq_singleton_iff_unique_mem.2 ⟨hy, hc⟩)
        exact ⟨z, Finset.mem_erase.2 ⟨hzy, hz⟩⟩
      · exact ⟨y, Finset.mem_erase.2 ⟨hym, hy⟩⟩
    · exact Finset.insert_nonempty _ _

/-- **Roadmap 3.5.** Removing an element `x` of `S` such that the elements of `S` above `x` have a
least element `m` does not change the Euler characteristic: toggling `m` pairs off the chains
through `x`. -/
theorem chainSum_erase_of_isLeast [DecidableEq T] {S : Finset T} {x m : T} (hm : m ∈ S)
    (hxm : x < m) (hle : ∀ y ∈ S, x < y → m ≤ y) : chainSum S = chainSum (S.erase x) := by
  classical
  unfold chainSum
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun σ => x ∈ σ)]
  have hzero : ∑ σ ∈ (S.powerset.filter IsChainFinset).filter (fun σ => x ∈ σ),
      (-1 : ℤ) ^ (σ.card + 1) = 0 := by
    refine Finset.sum_involution (fun σ _ => toggle m σ) (fun σ _ => sign_toggle m σ)
      (fun σ _ _ => toggle_ne m σ) (fun σ hσ => ?_) (fun σ _ => toggle_toggle m σ)
    simp only [Finset.mem_filter, Finset.mem_powerset] at hσ ⊢
    obtain ⟨⟨hS, -, hch⟩, hx⟩ := hσ
    have hxt : x ∈ toggle m σ := by
      unfold toggle
      split_ifs
      · exact Finset.mem_erase.2 ⟨hxm.ne, hx⟩
      · exact Finset.mem_insert_of_mem hx
    have hcmp : ∀ y ∈ σ, y ≤ m ∨ m ≤ y := by
      intro y hy
      rcases eq_or_ne y x with rfl | hyx
      · exact Or.inl hxm.le
      rcases hch.total (Finset.mem_coe.2 hy) (Finset.mem_coe.2 hx) with h | h
      · exact Or.inl (h.trans hxm.le)
      · exact Or.inr (hle y (hS hy) (lt_of_le_of_ne h (Ne.symm hyx)))
    refine ⟨⟨?_, ⟨x, hxt⟩, isChain_toggle hch hcmp⟩, hxt⟩
    unfold toggle
    split_ifs
    · exact (Finset.erase_subset _ _).trans hS
    · exact Finset.insert_subset hm hS
  rw [hzero, zero_add]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext σ
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun ⟨⟨h₁, h₂⟩, h₃⟩ => ⟨fun y hy => Finset.mem_erase.2 ⟨fun h => h₃ (h ▸ hy), h₁ hy⟩, h₂⟩,
    fun ⟨h₁, h₂⟩ => ⟨⟨h₁.trans (Finset.erase_subset _ _), h₂⟩,
      fun h => (Finset.mem_erase.1 (h₁ h)).1 rfl⟩⟩

/-- **Roadmap 3.5.** A finite poset `S` with a closure operator `φ` (monotone, inflationary,
idempotent) whose closed elements are all above a closed element `q` has Euler characteristic
`1`: the non-closed elements are removed one at a time, a maximal one first, and the closed
elements have the least element `q`. -/
theorem chainSum_eq_one_of_closure (S : Finset T) (φ : T → T) (hφS : ∀ z ∈ S, φ z ∈ S)
    (hφmono : ∀ a ∈ S, ∀ b ∈ S, a ≤ b → φ a ≤ φ b) (hφle : ∀ z ∈ S, z ≤ φ z)
    (hφφ : ∀ z ∈ S, φ (φ z) = φ z) {q : T} (hq : q ∈ S) (hqφ : φ q = q)
    (hqle : ∀ z ∈ S, q ≤ φ z) : chainSum S = 1 := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hall : ∀ z ∈ S, φ z = z
    · exact chainSum_eq_one_of_isLeast hq fun z hz => hall z hz ▸ hqle z hz
    · push Not at hall
      obtain ⟨x, hx, hmax⟩ := Finset.exists_maximal (s := S.filter fun z => φ z ≠ z)
        (let ⟨z, hz, hz'⟩ := hall; ⟨z, Finset.mem_filter.2 ⟨hz, hz'⟩⟩)
      obtain ⟨hxS, hxφ⟩ := Finset.mem_filter.1 hx
      have hxlt : x < φ x := lt_of_le_of_ne (hφle x hxS) (Ne.symm hxφ)
      have hclosed : ∀ y ∈ S, x < y → φ y = y := fun y hy hxy => by
        by_contra h
        exact hxy.not_ge (hmax (Finset.mem_filter.2 ⟨hy, h⟩) hxy.le)
      rw [chainSum_erase_of_isLeast (hφS x hxS) hxlt fun y hy hxy =>
        hclosed y hy hxy ▸ hφmono x hxS y hy hxy.le]
      have hqx : q ≠ x := fun h => hxφ (h ▸ hqφ)
      refine ih _ (Finset.erase_ssubset hxS) (fun z hz => ?_) (fun a ha b hb =>
        hφmono a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb))
        (fun z hz => hφle z (Finset.mem_of_mem_erase hz))
        (fun z hz => hφφ z (Finset.mem_of_mem_erase hz)) (Finset.mem_erase.2 ⟨hqx, hq⟩)
        (fun z hz => hqle z (Finset.mem_of_mem_erase hz))
      have hzS := Finset.mem_of_mem_erase hz
      refine Finset.mem_erase.2 ⟨fun h => hxφ ?_, hφS z hzS⟩
      rw [← h, hφφ z hzS]

theorem isChain_coe_iff {s : Finset T} :
    IsChain (· ≤ ·) (s : Set T) ↔ ∀ a ∈ s, ∀ b ∈ s, a ≤ b ∨ b ≤ a :=
  ⟨fun h _ ha _ hb => h.total ha hb, fun h a ha b hb _ => h a ha b hb⟩

/-- The Euler characteristic of a finite partial order is the alternating count of the chains
of its finite set of elements. -/
theorem chainEulerChar_eq_chainSum [Fintype T] :
    chainEulerChar T = chainSum (Finset.univ : Finset T) := by
  classical
  unfold chainEulerChar chainSum
  rw [finsum_eq_sum_of_fintype]
  rw [← Finset.sum_subtype
    (Finset.univ.filter fun σ : Finset T => σ ∈ TauCeti.AbstractSimplicialComplex.orderComplex T)
    (fun _ => by simp) (fun σ : Finset T => (-1 : ℤ) ^ (σ.card + 1))]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext σ
  simp [IsChainFinset, TauCeti.AbstractSimplicialComplex.mem_orderComplex_iff]

/-- The Euler characteristic of a subposet `{x // p x}` of a finite partial order is the
alternating count of the chains of `T` made of elements satisfying `p`. -/
theorem chainEulerChar_subtype [Fintype T] (p : T → Prop) [DecidablePred p] :
    chainEulerChar {x // p x} = chainSum (Finset.univ.filter p) := by
  classical
  rw [chainEulerChar_eq_chainSum]
  unfold chainSum
  refine Finset.sum_nbij' (fun σ => σ.map (Function.Embedding.subtype p))
    (fun σ => σ.subtype p) (fun σ hσ => ?_) (fun σ hσ => ?_) (fun σ _ => ?_) (fun σ hσ => ?_)
    (fun σ _ => by rw [Finset.card_map])
  · simp only [Finset.mem_filter, Finset.mem_powerset, IsChainFinset, isChain_coe_iff] at hσ ⊢
    refine ⟨fun x hx => ?_, hσ.2.1.map, fun a ha b hb => ?_⟩
    · obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hx
      simpa using y.2
    · obtain ⟨a', ha', rfl⟩ := Finset.mem_map.1 ha
      obtain ⟨b', hb', rfl⟩ := Finset.mem_map.1 hb
      exact hσ.2.2 a' ha' b' hb'
  · simp only [Finset.mem_filter, Finset.mem_powerset, IsChainFinset, isChain_coe_iff] at hσ ⊢
    have hp : ∀ x ∈ σ, p x := fun x hx => (Finset.mem_filter.1 (hσ.1 hx)).2
    refine ⟨Finset.subset_univ _, ?_, fun a ha b hb => ?_⟩
    · obtain ⟨x, hx⟩ := hσ.2.1
      exact ⟨⟨x, hp x hx⟩, Finset.mem_subtype.2 hx⟩
    · exact hσ.2.2 a (Finset.mem_subtype.1 ha) b (Finset.mem_subtype.1 hb)
  · ext x
    simpa [Finset.mem_subtype] using fun _ => x.2
  · simp only [Finset.mem_filter, Finset.mem_powerset] at hσ
    exact Finset.subtype_map_of_mem fun x hx => (Finset.mem_filter.1 (hσ.1 hx)).2

end Finite

end LeanPool.PosetHomotopy
