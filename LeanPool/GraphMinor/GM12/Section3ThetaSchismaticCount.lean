/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3BranchRelabel
public import LeanPool.GraphMinor.GM12.Section3ThetaClassification
import LeanPool.GraphMinor.GM12.Section3PuncturedCuffs
import LeanPool.GraphMinor.GM12.Section3PuncturedSurface

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# The vertex bound for a schismatic theta

Condition (iv) of XII (3.1), page 245, applies to every normal
schismatic theta. Its three pair circles surround distinct cuffs by
the proved classification. Index the opposite branches by those cuffs
and apply the three-branch bound. The branch permutation preserves
the union and hence the vertex count.
-/

public section

namespace GraphMinor.GM12

open Set Surface

universe u

private theorem injective_triple {ι : Type*} {i j k : ι}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : Function.Injective (![i, j, k]) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all

/-- Condition (iv) of XII (3.1) bounds every normal schismatic theta
when the prescribed deletion family is indexed by three elements. -/
theorem three_branch_vertex_count_gt_of_schismatic
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (Γ : Drawing S)
    (Δ : Fin 3 → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hUC : Γ.U ⊆ discComplement Δ) (N : ℕ)
    (hbound : IsSphere S → ∀ (P D : Fin 3 → Set S) (a b : S), a ≠ b →
      Γ.IsNormal (⋃ i, P i) → (∀ i, IsLineWithEnds (P i) a b) →
      (∀ i j, i ≠ j → P i ∩ P j = {a, b}) → (⋃ i, P i) ⊆ discComplement Δ →
      (∀ i, IsClosedDisc (D i) ∧
        discBd (D i) = ⋃ j : {j // j ≠ i}, P j.val ∧ Δ i ⊆ D i ∧ ¬ P i ⊆ D i) →
      N < (Γ.V ∩ ⋃ i, P i).ncard)
    {P Q R : Set (discComplement Δ)} {a b : discComplement Δ} (hab : a ≠ b)
    (hP : IsLineWithEnds P a b) (hQ : IsLineWithEnds Q a b) (hR : IsLineWithEnds R a b)
    (hPQ : P ∩ Q = {a, b}) (hPR : P ∩ R = {a, b}) (hQR : Q ∩ R = {a, b})
    (hX : GM07.IsSchismatic (P ∪ Q ∪ R))
    (hn : (drawingInSubspace Γ (discComplement Δ) hUC).IsNormal (P ∪ Q ∪ R)) :
    N < ((drawingInSubspace Γ (discComplement Δ) hUC).V ∩ (P ∪ Q ∪ R)).ncard := by
  let : ConnectedSpace (discComplement Δ) :=
    Subtype.connectedSpace (discComplement_isConnected hS Δ hΔ hdisj)
  have hsphere := (sphere_card_three_of_schismatic_theta hS Δ hΔ hdisj
    hab hP hQ hR hPQ hPR hQR hX).1
  obtain ⟨C₁, C₂, C₃, hs₁, hs₂, hs₃, h12, h13, h23⟩ :=
    surrounding_pairs_of_schismatic_theta (discComplement_isSurface hS Δ hΔ hdisj)
      (discComplement_cuffs_nonempty hS Δ hΔ hdisj) hab hP hQ hR hPQ hPR hQR hX
  have hc₁ := hs₁.1
  have hc₂ := hs₂.1
  have hc₃ := hs₃.1
  rw [discComplement_cuffs_eq hS Δ hΔ hdisj] at hc₁ hc₂ hc₃
  obtain ⟨i, rfl⟩ := hc₁
  obtain ⟨j, rfl⟩ := hc₂
  obtain ⟨k, rfl⟩ := hc₃
  have hij : i ≠ j := fun he => h12 (congrArg (fun l => Subtype.val ⁻¹' discBd (Δ l)) he)
  have hik : i ≠ k := fun he => h13 (congrArg (fun l => Subtype.val ⁻¹' discBd (Δ l)) he)
  have hjk : j ≠ k := fun he => h23 (congrArg (fun l => Subtype.val ⁻¹' discBd (Δ l)) he)
  let B : Fin 3 → Set (discComplement Δ) := ![P, Q, R]
  let f : Fin 3 → Fin 3 := ![k, j, i]
  have hfi : Function.Injective f := injective_triple hjk.symm hik.symm hij.symm
  let e : Fin 3 ≃ Fin 3 := Equiv.ofBijective f ⟨hfi, Finite.surjective_of_injective hfi⟩
  have hU : (⋃ l, B l) = P ∪ Q ∪ R := by
    ext x
    simp [B, Fin.exists_fin_succ, or_assoc]
  have hO₀ : (⋃ l : {l : Fin 3 // l ≠ 0}, B l.val) = Q ∪ R := by
    ext x
    simp [B, Fin.exists_fin_succ]
  have hO₁ : (⋃ l : {l : Fin 3 // l ≠ 1}, B l.val) = P ∪ R := by
    ext x
    simp [B, Fin.exists_fin_succ]
  have hO₂ : (⋃ l : {l : Fin 3 // l ≠ 2}, B l.val) = P ∪ Q := by
    ext x
    simp [B, Fin.exists_fin_succ]
  have hline : ∀ l, IsLineWithEnds (B l) a b := by
    intro l
    fin_cases l
    · exact hP
    · exact hQ
    · exact hR
  have hmeet : ∀ l m, l ≠ m → B l ∩ B m = {a, b} := by
    intro l m hlm
    fin_cases l <;> fin_cases m
    · exact (hlm rfl).elim
    · exact hPQ
    · exact hPR
    · exact (inter_comm Q P).trans hPQ
    · exact (hlm rfl).elim
    · exact hQR
    · exact (inter_comm R P).trans hPR
    · exact (inter_comm R Q).trans hQR
    · exact (hlm rfl).elim
  have hcircles : ∀ l, IsOArc (⋃ m : {m // m ≠ l}, B m.val) := by
    intro l
    fin_cases l
    · change IsOArc (⋃ m : {m : Fin 3 // m ≠ 0}, B m.val)
      rw [hO₀]
      exact isOArc_union_of_lines_inter_eq_ends hQ hR hQR
    · change IsOArc (⋃ m : {m : Fin 3 // m ≠ 1}, B m.val)
      rw [hO₁]
      exact isOArc_union_of_lines_inter_eq_ends hP hR hPR
    · change IsOArc (⋃ m : {m : Fin 3 // m ≠ 2}, B m.val)
      rw [hO₂]
      exact isOArc_union_of_lines_inter_eq_ends hP hQ hPQ
  have hs : ∀ l, GM07.SurroundsCuff (⋃ m : {m // m ≠ l}, B m.val)
      (Subtype.val ⁻¹' discBd (Δ (e l))) := by
    intro l
    fin_cases l
    · change GM07.SurroundsCuff (⋃ m : {m : Fin 3 // m ≠ 0}, B m.val)
        (Subtype.val ⁻¹' discBd (Δ k))
      rw [hO₀]
      exact hs₃
    · change GM07.SurroundsCuff (⋃ m : {m : Fin 3 // m ≠ 1}, B m.val)
        (Subtype.val ⁻¹' discBd (Δ j))
      rw [hO₁]
      exact hs₂
    · change GM07.SurroundsCuff (⋃ m : {m : Fin 3 // m ≠ 2}, B m.val)
        (Subtype.val ⁻¹' discBd (Δ i))
      rw [hO₂]
      exact hs₁
  have hnB : (drawingInSubspace Γ (discComplement Δ) hUC).IsNormal (⋃ l, B l) := by
    rwa [hU]
  have hnotB : ¬ GM07.IsNearPlanar (⋃ l, B l) := by rw [hU]; exact hX.2.1
  have hbig := three_branch_vertex_count_gt_relabelled hS hsphere Γ Δ hΔ hdisj hUC N hbound
    B hab hline hmeet hcircles e hs hnB hnotB
  rw [hU] at hbig
  exact hbig

end GraphMinor.GM12
