/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14q

/-!
# Graph Minors XIX, Section 14: arcs of a cuff, and marked drawings
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {S X : Type} [TopologicalSpace S] [TopologicalSpace X] [T2Space S] [T2Space X] {Θ : Set X}

/-- A surface with finitely many marked points on its boundary, two on each cuff, gives a drawing
with the same arcs, in each surface that holds it. -/
theorem exists_boundaryDrawing (hX : IsSurface X) {i : X → S} (hi : IsClosedEmbedding i) {N : Set
  X} (hN : N.Finite) (hsub : N ⊆ bd X)
    (h2 : ∀ C : cuffs X, ∃ p ∈ N ∩ C.1, ∃ q ∈ N ∩ C.1, p ≠ q) :
    ∃ K : Drawing S, K.U = i '' bd X ∧ K.V = i '' N ∧ arcComponentsIn (K.U \ K.V)
      = image i '' arcComponentsIn (bd X \ N) := by
  have himd : i '' bd X \ i '' N = i '' (bd X \ N) := (image_sdiff hi.injective _ _).symm
  have harc : arcComponentsIn (i '' (bd X \ N)) = image i '' arcComponentsIn (bd X \ N) := by
    ext C
    constructor
    · intro hC
      obtain ⟨c, hc, rfl⟩ := arcComponentsIn_image hi.isEmbedding hC
      exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact arcComponentsIn_image' hi.isEmbedding hc
  refine ⟨{
    U := i '' bd X
    V := i '' N
    V_subset_U := image_mono hsub
    isClosed_U := hi.isClosedMap _ (isClosed_bd X)
    finite_V := hN.image i
    finite_edges := ?_
    edge_cond := ?_ }, rfl, rfl, by simp only [himd, harc]⟩
  · simp only [himd, harc]
    exact (finite_arcComponentsIn_bd hX hN h2).image _
  · simp only [himd, harc]
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨C, a, b, hab, hub, rfl, hdis, ha, hb⟩ := exists_arc_of_mem hX (cuffPar hX) hN h2 hc
    have hL := isLine_arcOf (cuffPar hX C) hab hub
    have hne := (GM20.line_facts hL).1
    refine Or.inl ⟨i (cuffPoint (cuffPar hX C) a), i (cuffPoint (cuffPar hX C) b),
      hi.injective.ne hne, ?_, ?_⟩
    · rw [hi.closure_image_eq, ← image_inter hi.injective]
      have : closure (arcOf (cuffPar hX C) a b) ∩ N =
          ({cuffPoint (cuffPar hX C) a, cuffPoint (cuffPar hX C) b} : Set X) := by
        ext x
        constructor
        · rintro ⟨h₁, h₂⟩
          have ht : x ∈ tilde (arcOf (cuffPar hX C) a b) := ⟨h₁, fun h₃ ↦ disjoint_left.mp hdis h₃
            h₂⟩
          rwa [tilde_arcOf _ hab hub] at ht
        · rintro (rfl | rfl)
          · exact ⟨by rw [closure_arcOf _ hab]; exact ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩, ha⟩
          · exact ⟨by rw [closure_arcOf _ hab]; exact ⟨b, ⟨hab.le, le_rfl⟩, rfl⟩, hb⟩
      rw [this, image_pair]
    · rw [hi.closure_image_eq, closure_arcOf _ hab, image_image]
      exact GM11.isLine_of_injOn (hi.continuous.comp (continuous_cuffPoint _)) hab
        (hi.injective.comp_injOn (cuffPoint_injOn_Icc _ hub))

omit [T2Space X] in
/-- Two arcs of a cuff with no marked point on them and with the same first point are equal. -/
theorem arc_head_eq {f : Circle ≃ₜ Θ} {W : Set X} {a b a' b' : ℝ} (hab : a < b) (hab' : a' < b')
  (h₁ : arcOf f a b ∈ arcComponentsIn W) (h₂ : arcOf f a' b' ∈ arcComponentsIn W)
    (e : cuffPoint f a = cuffPoint f a') : arcOf f a b = arcOf f a' b' := by
  obtain ⟨m, hm⟩ := cuffPoint_eq f e
  have hs := arcOf_shift f a' b' m
  rw [← hs] at h₂ ⊢
  rw [← hm] at h₂ ⊢
  set c := b' + m * (2 * Real.pi)
  have hc : a < c := by simp only [c]; rw [hm]; linarith
  refine arcComp_eq_of_mem h₁ h₂ (x := cuffPoint f ((a + min b c) / 2)) ⟨_, ⟨?_, ?_⟩, rfl⟩ ⟨_,
    ⟨?_, ?_⟩, rfl⟩
  all_goals have := lt_min hab hc
  all_goals have h₃ := min_le_left b c
  all_goals have h₄ := min_le_right b c
  all_goals linarith

omit [T2Space X] in
/-- Two arcs of a cuff with no marked point on them and with the same last point are equal. -/
theorem arc_tail_eq {f : Circle ≃ₜ Θ} {W : Set X} {a b a' b' : ℝ} (hab : a < b) (hab' : a' < b')
  (h₁ : arcOf f a b ∈ arcComponentsIn W) (h₂ : arcOf f a' b' ∈ arcComponentsIn W)
    (e : cuffPoint f b = cuffPoint f b') : arcOf f a b = arcOf f a' b' := by
  obtain ⟨m, hm⟩ := cuffPoint_eq f e
  have hs := arcOf_shift f a' b' m
  rw [← hs] at h₂ ⊢
  rw [← hm] at h₂ ⊢
  set c := a' + m * (2 * Real.pi)
  have hc : c < b := by simp only [c]; rw [hm]; linarith
  refine arcComp_eq_of_mem h₁ h₂ (x := cuffPoint f ((b + max a c) / 2)) ⟨_, ⟨?_, ?_⟩, rfl⟩ ⟨_,
    ⟨?_, ?_⟩, rfl⟩
  all_goals have := max_lt hab hc
  all_goals have h₃ := le_max_left a c
  all_goals have h₄ := le_max_right a c
  all_goals linarith

/-- There are at most as many arcs as marked points. -/
theorem ncard_arcs_le (hX : IsSurface X) {N : Set X} (hN : N.Finite) (h2 : ∀ C : cuffs X, ∃ p ∈ N ∩
  C.1, ∃ q ∈ N ∩ C.1, p ≠ q) :
    (arcComponentsIn (bd X \ N)).ncard ≤ N.ncard := by
  classical
  rcases (arcComponentsIn (bd X \ N)).eq_empty_or_nonempty with he | ⟨c₀, hc₀⟩
  · rw [he]
    simp
  obtain ⟨x₀, -⟩ := hc₀.1
  have : Nonempty X := ⟨x₀⟩
  have hspec : ∀ c ∈ arcComponentsIn (bd X \ N), ∃ x : X, x ∈ N ∧ ∃ (C : cuffs X) (a b : ℝ), a < b
    ∧ c = arcOf (cuffPar hX C) a b ∧ cuffPoint (cuffPar hX C) a = x := fun c hc ↦ by
    obtain ⟨C, a, b, h₁, -, h₃, -, h₄, -⟩ := exists_arc_of_mem hX (cuffPar hX) hN h2 hc
    exact ⟨_, h₄, C, a, b, h₁, h₃, rfl⟩
  choose! g hg using hspec
  refine ncard_le_ncard_of_injOn g (fun c hc ↦ (hg c hc).1) (fun c hc c' hc' e ↦ ?_) hN
  obtain ⟨-, C, a, b, h₁, rfl, h₃⟩ := hg c hc
  obtain ⟨-, C', a', b', h₁', rfl, h₃'⟩ := hg _ hc'
  rw [← h₃, ← h₃'] at e
  obtain rfl : C = C' := by
    by_contra hne
    exact disjoint_left.mp (cuffs_disjoint' hne) (cuffPoint_mem _ _) (e.symm ▸ cuffPoint_mem _ _)
  exact arc_head_eq h₁ h₁' hc hc' e

end GraphMinor.GM19
