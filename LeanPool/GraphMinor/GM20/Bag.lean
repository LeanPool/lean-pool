/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Codes
import LeanPool.GraphMinor.GM04.Higman

/-!
# Bags of labelled edges

The proof of (4.10) of Graph Minors XX labels an edge of a condensation with a small patchwork, all
of
whose vertices are roots. For such a patchwork only the following matters: for each of the finitely
many codes of edges, the list of labels of the edges with that code. That data is a `Bag`. By
Higman's
lemma bags are well-quasi-ordered (`wqo_bag`), and two comparable bags give an injection of the
edges
which keeps codes and does not lower labels (`exists_edgeMap`).
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v}

/-- For each code, a list of labels. -/
def Bag (Ω : Type*) (k : ℕ) := EdgeCode k → List Ω

instance {Ω : Type*} [Preorder Ω] (k : ℕ) : Preorder (Bag Ω k) where
  le f g := ∀ c, List.SublistForall₂ (· ≤ ·) (f c) (g c)
  le_refl f c := refl_of (List.SublistForall₂ (· ≤ ·)) (f c)
  le_trans _ _ _ hfg hgh c := _root_.trans (hfg c) (hgh c)

/-- Bags are well-quasi-ordered, by Higman's lemma for each of the finitely many codes. -/
theorem wqo_bag {Ω : Type*} [Preorder Ω] (hΩ : WellQuasiOrderedLE Ω) (k : ℕ) :
    WellQuasiOrderedLE (Bag Ω k) := by
  have hU : (univ : Set Ω).PartiallyWellOrderedOn (· ≤ ·) := fun f ↦ hΩ.wqo fun i ↦ (f i).1
  have hL := hU.partiallyWellOrderedOn_sublistForall₂
  have hp : IsPreorder (List Ω) (List.SublistForall₂ (· ≤ ·)) := ⟨⟩
  have hl : WellQuasiOrdered (List.SublistForall₂ (· ≤ ·) : List Ω → List Ω → Prop) := by
    intro f
    obtain ⟨m, n, hmn, h⟩ := hL fun i ↦ ⟨f i, fun _ _ ↦ mem_univ _⟩
    exact ⟨m, n, hmn, h⟩
  exact ⟨WellQuasiOrdered.pi (r := fun _ : EdgeCode k ↦ List.SublistForall₂ (· ≤ ·)) fun _ ↦ hl⟩

/-- A sublist relation between duplicate-free lists gives an injection between them. -/
theorem exists_inj_of_sublistForall₂ {κ Ω : Type*} {r : Ω → Ω → Prop} {l₁ l₂ : List κ}
    {ℓ₁ ℓ₂ : κ → Ω} (hnd₁ : l₁.Nodup) (hnd₂ : l₂.Nodup)
    (h : List.SublistForall₂ (fun x y ↦ r (ℓ₁ x) (ℓ₂ y)) l₁ l₂) :
    ∃ g : κ → κ, (∀ x ∈ l₁, ∀ y ∈ l₁, g x = g y → x = y) ∧
      (∀ x ∈ l₁, g x ∈ l₂) ∧ (∀ x ∈ l₁, r (ℓ₁ x) (ℓ₂ (g x))) :=
  GM04.exists_inj_of_sublistForall₂ hnd₁ hnd₂ h

variable {Ω : Type*}

open Classical in
/-- The edges of `R` with code `c`, in some order. -/
noncomputable def edgesOfCode (k : ℕ) (R : Patchwork Ω α β) (c : EdgeCode k) : List β :=
  (R.G.edgeSet_finite.toFinset.filter fun e ↦ edgeCode k R.G.roots R e = c).toList

theorem mem_edgesOfCode {k : ℕ} {R : Patchwork Ω α β} {c : EdgeCode k} {e : β} :
    e ∈ edgesOfCode k R c ↔ e ∈ R.G.edgeSet ∧ edgeCode k R.G.roots R e = c := by
  classical
  simp [edgesOfCode]

/-- The bag of a patchwork. -/
noncomputable def bag (k : ℕ) (R : Patchwork Ω α β) : Bag Ω k :=
  fun c ↦ (edgesOfCode k R c).map R.φ

/-- Comparable bags give an injection of the edges that keeps codes and does not lower labels. -/
theorem exists_edgeMap [Preorder Ω] {k : ℕ} {R R' : Patchwork Ω α β} (h : bag k R ≤ bag k R') :
    ∃ g : β → β, InjOn g R.G.edgeSet ∧ MapsTo g R.G.edgeSet R'.G.edgeSet ∧
      ∀ f ∈ R.G.edgeSet, R.φ f ≤ R'.φ (g f) ∧
        edgeCode k R.G.roots R f = edgeCode k R'.G.roots R' (g f) := by
  classical
  have hc : ∀ c, _ := fun c ↦ by
    have hsub : List.SublistForall₂ (· ≤ ·) (bag k R c) (bag k R' c) := h c
    simp only [bag, List.sublistForall₂_map_left_iff, List.sublistForall₂_map_right_iff] at hsub
    exact exists_inj_of_sublistForall₂ (Finset.nodup_toList _) (Finset.nodup_toList _) hsub
  choose G hinj hmem hle using hc
  have hself : ∀ f ∈ R.G.edgeSet, f ∈ edgesOfCode k R (edgeCode k R.G.roots R f) := fun f hf ↦
    mem_edgesOfCode.mpr ⟨hf, rfl⟩
  have hcode : ∀ f ∈ R.G.edgeSet,
      edgeCode k R'.G.roots R' (G (edgeCode k R.G.roots R f) f) = edgeCode k R.G.roots R f :=
    fun f hf ↦ (mem_edgesOfCode.mp (hmem _ f (hself f hf))).2
  refine ⟨fun f ↦ G (edgeCode k R.G.roots R f) f, ?_, ?_, ?_⟩
  · intro f₁ h₁ f₂ h₂ heq
    have heq' : G (edgeCode k R.G.roots R f₁) f₁ = G (edgeCode k R.G.roots R f₂) f₂ := heq
    have hcc : edgeCode k R.G.roots R f₁ = edgeCode k R.G.roots R f₂ := by
      rw [← hcode f₁ h₁, ← hcode f₂ h₂, heq']
    rw [hcc] at heq'
    exact hinj _ f₁ (hcc ▸ hself f₁ h₁) f₂ (hself f₂ h₂) heq'
  · exact fun f hf ↦ (mem_edgesOfCode.mp (hmem _ f (hself f hf))).1
  · exact fun f hf ↦ ⟨hle _ f (hself f hf), (hcode f hf).symm⟩

end GraphMinor.GM20
