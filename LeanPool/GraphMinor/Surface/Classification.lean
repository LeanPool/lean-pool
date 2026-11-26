/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.ModelHomeo
public import LeanPool.GraphMinor.Surface.ModelWord
public import LeanPool.GraphMinor.Surface.OneWord
public import LeanPool.GraphMinor.Surface.SurfacePull
public import LeanPool.GraphMinor.Surface.WordIso

/-!
# Classification of surfaces

Each connected surface is homeomorphic to a model (`classification`). We cap the surface, dissect
the closed surface
around the cuffs, restrict the dissection to the surface, read off one word, bring the word to its
normal form
and compare with the word of the model. This is the proof of Seifert and Threlfall, *Lehrbuch der
Topologie*, Chapter 6,
with the dissection built by hand instead of quoting a triangulation.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

universe u

variable {S : Type u} [TopologicalSpace S]

theorem sUnion_cuffs : ⋃₀ cuffs S = bd S := by
  apply subset_antisymm
  · rintro x ⟨_, ⟨y, hy, rfl⟩, hx⟩
    exact connectedComponentIn_subset _ _ hx
  · intro x hx
    exact ⟨_, ⟨x, hx, rfl⟩, mem_connectedComponentIn hx⟩

theorem cuffs_disjoint {C C' : Set S} (hC : C ∈ cuffs S) (hC' : C' ∈ cuffs S)
  (hne : C ≠ C') : Disjoint C C' := by
  obtain ⟨x, hx, rfl⟩ := hC
  obtain ⟨y, hy, rfl⟩ := hC'
  rw [Set.disjoint_left]
  intro z h1 h2
  exact hne ((connectedComponentIn_eq h1).trans (connectedComponentIn_eq h2).symm)

variable [T2Space S]

/-- The cuffs of a surface as a graph. -/
theorem exists_cuff_graph (hS : IsSurface S) :
    ∃ (V : Set S) (E : Set (Set S)), IsGraph V E ∧ V ⊆ ⋃₀ E ∧ ⋃₀ E = bd S := by
  classical
  have hfin := (cuff_statement.{u} S hS).2.1
  have hO := (cuff_statement.{u} S hS).2.2
  have key : ∀ 𝓐 : Set (Set S), 𝓐.Finite → 𝓐 ⊆ cuffs S →
      ∃ (V : Set S) (E : Set (Set S)), IsGraph V E ∧ V ⊆ ⋃₀ E ∧ gr V E = ⋃₀ 𝓐 := by
    intro 𝓐 h𝓐
    induction 𝓐, h𝓐 using Set.Finite.induction_on with
    | empty =>
      intro _
      exact ⟨∅, ∅, isGraph_empty, by simp, by simp [gr]⟩
    | @insert C 𝓐 hC _ ih =>
      intro hsub
      obtain ⟨V, E, hg, hV, hgr⟩ := ih ((subset_insert _ _).trans hsub)
      have hCc : C ∈ cuffs S := hsub (mem_insert _ _)
      have hdisj : C \ gr V E = C := by
        rw [hgr]
        refine Disjoint.sdiff_eq_left (Set.disjoint_left.mpr ?_)
        rintro z hz ⟨C', hC', hz'⟩
        have hne : C ≠ C' := fun h => hC (h ▸ hC')
        exact Set.disjoint_left.mp (cuffs_disjoint hCc (hsub (mem_insert_of_mem _ hC')) hne) hz hz'
      have hconn : FinConn (C \ gr V E) := by
        rw [hdisj]
        exact ⟨{C}, finite_singleton _, fun J hJ => by
          rw [mem_singleton_iff.mp hJ]
          exact (hO C hCc).isPreconnected, sUnion_singleton _⟩
      obtain ⟨V', E', -, hg', hgr', hV'⟩ := hg.add_curve (hO C hCc) hconn
      refine ⟨V', E', hg', hV' hV, ?_⟩
      rw [hgr', hgr, sUnion_insert, union_comm]
  obtain ⟨V, E, hg, hV, hgr⟩ := key _ hfin subset_rfl
  refine ⟨V, E, hg, hV, ?_⟩
  rw [← sUnion_cuffs, ← hgr]
  exact (union_eq_right.mpr hV).symm

theorem TwoConn.sUnion_add {X : Type u} [TopologicalSpace X] {G : Set X} (hG : TwoConn G) {𝓐 : Set
  (Set X)} (h𝓐 : 𝓐.Finite)
    (hc : ∀ C ∈ 𝓐, TwoConn C) (hm : ∀ C ∈ 𝓐, ∃ x y, x ∈ G ∩ C ∧ y ∈ G ∩ C ∧ x ≠ y) : TwoConn
      (G ∪ ⋃₀ 𝓐) := by
  induction 𝓐, h𝓐 using Set.Finite.induction_on with
  | empty => simpa using hG
  | @insert C 𝓐 _ _ ih =>
    have h1 := ih (fun D hD => hc D (mem_insert_of_mem _ hD)) (fun D hD => hm D
      (mem_insert_of_mem _ hD))
    obtain ⟨x, y, hx, hy, hxy⟩ := hm C (mem_insert _ _)
    have h2 := h1.union (hc C (mem_insert _ _)) (x := x) (y := y) ⟨.inl hx.1, hx.2⟩ ⟨.inl hy.1,
      hy.2⟩ hxy
    have e : G ∪ ⋃₀ insert C 𝓐 = G ∪ ⋃₀ 𝓐 ∪ C := by
      rw [sUnion_insert, union_assoc, union_comm C]
    rwa [e]

/-- A dissection of each connected surface. -/
theorem exists_surface_dissection (hS : IsSurface S) [ConnectedSpace S] :
    ∃ (V : Set S) (E 𝓕 : Set (Set S)), IsDissection V E 𝓕 := by
  classical
  obtain ⟨hcpt, -, hman⟩ := id hS
  obtain ⟨T, _, j, K, hT, hj, hK, hu, hi, hconn⟩ := exists_capAll S hS
  have := hconn inferInstance
  have : T2Space T := hT.2.1
  have hfin := (cuff_statement.{u} S hS).2.1
  have hO := (cuff_statement.{u} S hS).2.2
  obtain ⟨V₀, E₀, hg, hV₀, hE₀⟩ := exists_cuff_graph hS
  have hgT := hg.map hj.isEmbedding
  have hsU : ⋃₀ ((fun e => j '' e) '' E₀) = j '' bd S := by
    rw [sUnion_image, ← image_iUnion₂, ← sUnion_eq_biUnion, hE₀]
  obtain ⟨ρ, hρ, hl⟩ := exists_inv_of_compactOn (isCompact_univ (X := S)) hj.continuous.continuousOn
    hj.injective.injOn
  have hOT : ∀ C ∈ cuffs S, IsOArc (j '' C) := fun C hC =>
    (hO C hC).image hj.continuous.continuousOn (hρ.mono (image_mono (subset_univ _)))
      (fun x _ => hl (mem_univ x))
  obtain ⟨V, E, 𝓕, -, hsub, hd⟩ := exists_dissection hT hgT (image_mono hV₀ |>.trans (by
      rintro _ ⟨y, ⟨e, he, hy⟩, rfl⟩
      exact ⟨_, ⟨e, he, rfl⟩, mem_image_of_mem j hy⟩)) (𝓒c := (fun C => j '' C) '' cuffs S)
        (hfin.image _)
    (by
      rintro _ ⟨C, hC, rfl⟩
      exact (hOT C hC).twoConn)
    (by
      rintro _ ⟨C, hC, rfl⟩
      exact (hOT C hC).exists_three)
    (by
      intro G hG hm
      rw [hsU, ← sUnion_cuffs, sUnion_eq_biUnion, image_iUnion₂, ← sUnion_image]
      exact hG.sUnion_add (hfin.image _) (by
        rintro _ ⟨C, hC, rfl⟩
        exact (hOT C hC).twoConn) hm)
  rw [hsU] at hsub
  exact ⟨_, _, _, pull_dissection hman hj hK hu hi hd hsub⟩

/-- **Classification of surfaces, first part.** -/
theorem classification : ClassificationStatement.{u} := by
  classical
  intro S _ hS hconn
  obtain ⟨hcpt, ht2, hman⟩ := id hS
  obtain ⟨V, E, 𝓕, hd⟩ := exists_surface_dissection hS
  have hne : 𝓕.Nonempty := by
    rw [nonempty_iff_ne_empty]
    rintro rfl
    obtain ⟨x⟩ : Nonempty S := inferInstance
    have := hd.cover
    simp at this
    exact (eq_empty_iff_forall_notMem.mp this.symm x (mem_univ _))
  obtain ⟨W, f, I, hW, h0, hf, hlen, hI, hcount⟩ := exists_family hman hd hne
  obtain ⟨w, g, hw, hG, hg⟩ := exists_one_word (X := S) _ I W f rfl hW h0 hf hlen hI hcount
  have toModel : ∀ (a b c : ℕ) (w' : List Letter), WEq.{u} w w' →
      PEq.{u} (modelW a b (2 * a + b + c)) (sW w') → ∃ a b c, Nonempty (S ≃ₜ SurfaceModel a b c)
        := by
    intro a b c w' h1 h2
    obtain ⟨g', hg'⟩ := ((show PEq.{u} (sW w) (sW w') from h1).trans h2.symm S).mp ⟨g, hg⟩
    exact ⟨a, b, c, model_homeo a b c hg'⟩
  have sphere : ∀ x : Letter, WEq.{u} w [x, linv x] → ∃ a b c, Nonempty (S ≃ₜ SurfaceModel a b c)
    := by
    intro x hx
    obtain ⟨w', hp, h3⟩ := exists_modelW_nf.{u} 0 0 0
    rcases h3 with ⟨-, h4⟩ | ⟨-, rfl⟩
    · exact absurd rfl h4
    · refine toModel 0 0 0 _ (hx.trans ?_) hp
      refine Iso.weq ⟨fun _ => 0, fun _ => x.2, ?_, ?_⟩
      · intro l hl l' hl' _
        have e1 : l.1 = x.1 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl <;> rfl
        have e2 : l'.1 = x.1 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
          rcases hl' with rfl | rfl <;> rfl
        rw [e1, e2]
      · obtain ⟨k, e⟩ := x
        cases e <;> simp [linv, segL]
  rcases exists_nf.{u} hw hG with ⟨a, b, c, w', hnf, hwe⟩ | ⟨x, hx⟩
  · obtain ⟨w'', hp, h3⟩ := exists_modelW_nf.{u} a b c
    rcases h3 with ⟨hnf', -⟩ | ⟨h0', rfl⟩
    · exact toModel a b c w'' (hwe.trans (nf_eq hnf hnf')) hp
    · obtain ⟨rfl, rfl, rfl⟩ : a = 0 ∧ b = 0 ∧ c = 0 := by omega
      obtain ⟨X, Y, Z, rfl, h1, h2, h3, -⟩ := hnf
      cases h1
      cases h2
      cases h3
      obtain ⟨g', hg'⟩ := ((show PEq.{u} (sW w) (sW ([] ++ [] ++ [])) from hwe) S).mp ⟨g, hg⟩
      obtain ⟨x⟩ : Nonempty S := inferInstance
      have h4 : x ∈ g' '' Dsk (sW ([] ++ [] ++ [])) := hg'.2.1 ▸ mem_univ x
      obtain ⟨y, hy, -⟩ := h4
      exact absurd (by
        simp [sW, nW, Function.update] ) hy.1
  · exact sphere x hx

end GraphMinor.Surface
