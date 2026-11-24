/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3CapOneDisc
public import LeanPool.GraphMinor.GM12.Section3PuncturedCuffs
public import LeanPool.GraphMinor.Surface.TopologyStatements
import LeanPool.GraphMinor.GM12.Section3CapTopology
import LeanPool.GraphMinor.Surface.Classification
import LeanPool.GraphMinor.Surface.ModelCriterion
import LeanPool.GraphMinor.Surface.PasteModel

/-!
# Model parameters of the punctured surface

The application of VII in XII (3.1), page 245, uses the surface obtained
by deleting the prescribed disc interiors. Its number of cuffs is the
number of discs. Filling a prescribed cuff preserves the handle and
cross-cap parameters and removes one cuff, by the surface pasting theorem.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- The last parameter of a model for Sigma-star is exactly the number
of deleted discs, as used in the application of VII for XII (3.1). -/
theorem discComplement_model_cuff_parameter
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    {a b c : ℕ} (e : discComplement Δ ≃ₜ SurfaceModel a b c) :
    c = Nat.card ι := by
  obtain ⟨ht, f, hf⟩ := presents_ew a b c
  let := ht
  exact (ncard_cuffs hf).symm.trans
    ((ncard_cuffs_congr e).symm.trans (discComplement_cuff_count hS Δ hΔ hdisj))

/-- Filling one prescribed disc preserves both genus parameters of a
model for Sigma-star. This implements one capping step in XII (3.1). -/
theorem discComplement_model_fill_one
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    {a b c : ℕ} (e : discComplement Δ ≃ₜ SurfaceModel a b c) (i : ι) :
    0 < c ∧ Nonempty
      (discComplement (fun k : {k // k ≠ i} => Δ k.val) ≃ₜ SurfaceModel a b (c - 1)) := by
  obtain ⟨j, hj, _⟩ := exists_cap_discComplement_cuff hS Δ hΔ hdisj i
  have hC := discComplement_isSurface hS Δ hΔ hdisj
  exact paste_model hC hj.cuff hj.isSurface
    (cappedCuff_isClosedEmbedding hC hj) hj.isClosedDisc
    hj.union_eq hj.inter_eq hj.discBd_eq e

/-- Filling all prescribed discs recovers the original surface with
unchanged handle and cross-cap parameters. This relates the model used
in VII to the fixed surface of XII (3.1). -/
theorem discComplement_model_fill_all
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    {a b c : ℕ} (e : discComplement Δ ≃ₜ SurfaceModel a b c) :
    Nonempty (S ≃ₜ SurfaceModel a b 0) := by
  classical
  induction hn : Nat.card ι using Nat.strong_induction_on generalizing ι c with
  | ind n ih =>
    cases isEmpty_or_nonempty ι with
    | inl hempty =>
      let := hempty
      have hc : c = 0 := by
        simpa using discComplement_model_cuff_parameter hS Δ hΔ hdisj e
      have hC : discComplement Δ = univ := by simp [discComplement]
      exact ⟨((Homeomorph.Set.univ S).symm.trans
        (Homeomorph.setCongr hC).symm).trans (hc ▸ e)⟩
    | inr hne =>
      obtain ⟨i⟩ := hne
      let := Fintype.ofFinite ι
      have hlt : Nat.card {k : ι // k ≠ i} < n := by
        rw [← hn, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        exact Fintype.card_lt_of_injective_of_notMem Subtype.val Subtype.val_injective
          (b := i) (by rintro ⟨x, hx⟩; exact x.property hx)
      obtain ⟨_, e'⟩ := discComplement_model_fill_one hS Δ hΔ hdisj e i
      exact ih _ hlt (fun k : {k : ι // k ≠ i} => Δ k.val)
        (fun k => hΔ k.val)
        (fun k l hkl => hdisj (fun he => hkl (Subtype.ext he))) e'.some rfl

/-- A model of the original closed surface fixes both genus parameters
for every placement of the deleted discs. Only the cuff count changes.
Thus the model in the application of VII for XII (3.1) can be chosen
independently of the drawing and of the placement of the discs. -/
theorem discComplement_model_of_closed_model
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    {a₀ b₀ : ℕ} (e₀ : S ≃ₜ SurfaceModel a₀ b₀ 0) :
    Nonempty (discComplement Δ ≃ₜ SurfaceModel a₀ b₀ (Nat.card ι)) := by
  have hC := discComplement_isSurface hS Δ hΔ hdisj
  have hconn := Subtype.connectedSpace (discComplement_isConnected hS Δ hΔ hdisj)
  obtain ⟨a, b, c, ⟨e⟩⟩ := classification _ hC hconn
  have hc := discComplement_model_cuff_parameter hS Δ hΔ hdisj e
  obtain ⟨eS⟩ := discComplement_model_fill_all hS Δ hΔ hdisj e
  obtain ⟨_, hgenus, hcross⟩ :=
    (modelCriterion.2 a b 0 a₀ b₀ 0).mp ⟨eS.symm.trans e₀⟩
  obtain ⟨eM⟩ := (modelCriterion.2 a b c a₀ b₀ (Nat.card ι)).mpr
    ⟨hc, hgenus, hcross⟩
  exact ⟨e.trans eM⟩

end GraphMinor.GM12
