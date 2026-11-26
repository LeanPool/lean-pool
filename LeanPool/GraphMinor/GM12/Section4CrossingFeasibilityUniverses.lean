/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4CrossingFeasibility
public import LeanPool.GraphMinor.GM12.Section4SmallSurfaceCopy
public import LeanPool.GraphMinor.GM12.Section4ContactPartitionImage

/-!
# Crossing feasibility in arbitrary surface universes

For XII (4.5), claim (1), page 253, perform the geometric
construction on a homeomorphic small surface. Carry each
prescribed disc and its boundary parametrization to that
surface, use the ordered crossing partition, then carry the
vertex discs and endpoints back. The homeomorphism preserves
all contact and opposite-pair equations. No size assumption
is added to the surface in the conclusion.
-/

public section

namespace GraphMinor.GM12

open Set Surface Graph

/-- The ordered-parameter form of XII (4.5), claim (1), page 253,
in arbitrary surface universes. The small-copy construction
retains all graph and disc witnesses without a size hypothesis. -/
theorem theorem_4_5_claim_1_ordered_univ {S : Type*} [TopologicalSpace S]
  [ConnectedSpace S]
    (hS : IsClosedSurface S) {p : ℕ} (hp : 4 ≤ p) :
    ∃ (W E : Type) (L : Graph W E) (κ : E × Bool → W) (t : ℕ) (σ : Fin t × Bool ≃ E),
      Finite W ∧ Finite E ∧ IsIsoMinor (GM16.completeGraph p) L ∧
      L.vertexSet = univ ∧ L.edgeSet = univ ∧
      (∀ e, L.IsLink e (κ (e, false)) (κ (e, true))) ∧
      (∀ e, κ (e, false) ≠ κ (e, true)) ∧ 2 ≤ t ∧
      (∀ w, ∃ i j, i ≠ j ∧ ∃ b c d e : Bool,
        κ (σ (i, b), c) = w ∧ κ (σ (j, d), e) = w) ∧
      ∀ (Δ : Fin t → Set S) (q : Fin t → Circle → S) (β : Fin t → Fin 4 → ℝ),
        (∀ i, IsClosedDisc (Δ i)) → Pairwise (fun i j => Disjoint (Δ i) (Δ j)) →
        (∀ i, Continuous (q i) ∧ Function.Injective (q i) ∧ range (q i) = discBd (Δ i)) →
        (∀ i, StrictMono (β i)) → (∀ i j, β i j ∈ Ico 0 1) →
        ∃ (ends : E × Bool → S) (B : W → Set S), Function.Injective ends ∧
          (∀ w, IsClosedDisc (B w)) ∧ Pairwise (fun w z => Disjoint (B w) (B z)) ∧
          (∀ w, B w ∩ (⋃ i, Δ i) = edgeEndClass ends κ w) ∧
          (∀ i, ({ends (σ (i, false), false), ends (σ (i, false), true)} : Set S) =
            {q i (ee (β i 0)), q i (ee (β i 2))}) ∧
          (∀ i, ({ends (σ (i, true), false), ends (σ (i, true), true)} : Set S) =
            {q i (ee (β i 1)), q i (ee (β i 3))}) := by
  classical
  obtain ⟨S₀, tS₀, ⟨e⟩, hS₀⟩ := exists_small_closed_surface_copy hS
  let : TopologicalSpace S₀ := tS₀
  let : T2Space S₀ := hS₀.2.1
  let : ConnectedSpace S₀ := e.surjective.connectedSpace e.continuous
  obtain ⟨W, E, L, κ, t, σ, hW, hE, hminor, hLV, hLE, hlink, hκne, ht, htwo, hmain⟩ :=
    theorem_4_5_claim_1_ordered hS₀ hp
  refine ⟨W, E, L, κ, t, σ, hW, hE, hminor, hLV, hLE, hlink, hκne, ht, htwo, ?_⟩
  intro Δ q β hΔ hΔΔ hq hβ hβ01
  let Δ₀ := fun i => e '' Δ i
  let q₀ := fun i => e ∘ q i
  have hΔ₀ : ∀ i, IsClosedDisc (Δ₀ i) := fun i =>
    ((hΔ i).image e.continuous.continuousOn e.symm.continuous.continuousOn
      (fun z _ => e.symm_apply_apply z)).1
  have hΔΔ₀ : Pairwise (fun i j => Disjoint (Δ₀ i) (Δ₀ j)) :=
    fun i j hij => (disjoint_image_iff e.injective).mpr (hΔΔ hij)
  have hq₀ : ∀ i, Continuous (q₀ i) ∧ Function.Injective (q₀ i) ∧ range (q₀ i) = discBd (Δ₀ i) :=
    fun i => boundary_param_image_homeomorph e (hΔ i) (q i) (hq i)
  obtain ⟨ends₀, B₀, hinj₀, hB₀, hBB₀, hcontact₀, h0, h1⟩ :=
    hmain Δ₀ q₀ β hΔ₀ hΔΔ₀ hq₀ hβ hβ01
  obtain ⟨hB, hBB, hcontact⟩ := contact_partition_image e.symm B₀ Δ₀ ends₀ κ hB₀ hBB₀ hcontact₀
  refine ⟨e.symm ∘ ends₀, (fun w => e.symm '' B₀ w), e.symm.injective.comp hinj₀,
    hB, hBB, ?_, ?_, ?_⟩
  · intro w
    simpa only [Δ₀, image_image, e.symm_apply_apply, image_id'] using hcontact w
  · intro i
    have h := congrArg (fun X : Set S₀ => e.symm '' X) (h0 i)
    simp only [image_pair] at h
    simpa only [q₀, Function.comp_apply, e.symm_apply_apply] using h
  · intro i
    have h := congrArg (fun X : Set S₀ => e.symm '' X) (h1 i)
    simp only [image_pair] at h
    simpa only [q₀, Function.comp_apply, e.symm_apply_apply] using h

end GraphMinor.GM12
