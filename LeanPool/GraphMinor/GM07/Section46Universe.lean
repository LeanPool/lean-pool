/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46Reduce
import LeanPool.GraphMinor.GM07.Section46WTransport
import LeanPool.GraphMinor.GM07.Section3
import LeanPool.GraphMinor.GM12.Section3HomeoWalks
import LeanPool.GraphMinor.GM19.Section4c
import LeanPool.GraphMinor.Surface.AddCrosscap

/-!
# The hypotheses of VII (4.6) along a homeomorphism

The proof of VII (4.6) takes place in a surface in `Type`. A surface in any
universe is homeomorphic to its model, so the hypotheses and the conclusion of
(4.6) move along that homeomorphism. Only hypothesis (ii) needs care, since it
speaks of all capped surfaces in the universe of the surface. There we lift a
capped surface to the larger universe with `ULift`.
-/

public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} {T : Type} [TopologicalSpace S] [TopologicalSpace T]

/-- A homeomorphism carries cuffs to cuffs. -/
theorem cuffs_image_homeo (e : S ≃ₜ T) : cuffs T = (fun C => e '' C) '' cuffs S := by
  ext C
  simp only [cuffs, componentsIn, mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← GM19.image_bd e] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨_, ⟨x, hx, rfl⟩, ?_⟩
    rw [← GM19.image_bd e]
    exact e.image_connectedComponentIn hx
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨e x, by rw [← GM19.image_bd e]; exact mem_image_of_mem e hx, ?_⟩
    rw [← GM19.image_bd e]
    exact (e.image_connectedComponentIn hx).symm

/-- The number `v(Σ, k)` depends only on the homeomorphism type. -/
theorem vSurface_eq_of_homeo (e : S ≃ₜ T) (k : ℕ) : vSurface S k = vSurface T k := by
  unfold vSurface
  congr 1
  ext v
  constructor
  · rintro ⟨a, b, c, ⟨f⟩, h⟩
    exact ⟨a, b, c, ⟨e.symm.trans f⟩, h⟩
  · rintro ⟨a, b, c, ⟨f⟩, h⟩
    exact ⟨a, b, c, ⟨e.trans f⟩, h⟩

private theorem isNormal_pull (e : S ≃ₜ T) {G : Drawing S} {B : Set T}
    (h : (mapDrawingHomeo e G).IsNormal B) : G.IsNormal (e.symm '' B) := by
  rintro x ⟨⟨y, hy, rfl⟩, hx⟩
  obtain ⟨z, hz, hzz⟩ := h ⟨hy, ⟨_, hx, by simp⟩⟩
  have : z = e.symm y := by
    rw [← hzz]
    simp
  exact this ▸ hz

private theorem ncard_pull (e : S ≃ₜ T) (G : Drawing S) (B : Set T) :
    (G.V ∩ e.symm '' B).ncard = ((mapDrawingHomeo e G).V ∩ B).ncard := by
  have : (mapDrawingHomeo e G).V ∩ B = e '' (G.V ∩ e.symm '' B) := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩
      exact ⟨x, ⟨hx, _, hy, by simp⟩, rfl⟩
    · rintro ⟨x, ⟨hx, y, hy, rfl⟩, rfl⟩
      exact ⟨⟨_, hx, rfl⟩, by simpa using hy⟩
  rw [this, ncard_image_of_injective _ e.injective]

theorem IsNullHomotopicOArc.image_homeo {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {F : Set X} (h : IsNullHomotopicOArc F) : IsNullHomotopicOArc (e '' F) := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.trans (e.image F), ?_⟩
  obtain ⟨c, -, ψ, -, h0, h1⟩ := hφ
  refine ⟨e c, mem_univ _, ⟨⟨fun p => e (ψ p), by fun_prop⟩, fun _ => mem_univ _, fun x => ?_,
    fun x => ?_⟩⟩
  · change e (ψ (x, 0)) = e (φ x).1
    rw [h0]
    rfl
  · change e (ψ (x, 1)) = e c
    rw [h1]
    rfl

/-- Hypothesis (i) of VII (4.6) along a homeomorphism. -/
theorem hi_map (e : S ≃ₜ T) {G : Drawing S} {v : ℕ}
    (hi : ∀ B : Set S, G.IsNormal B → IsIArc B → (G.V ∩ B).ncard ≤ v →
      ∃ C ∈ cuffs S, lineEnds B ⊆ C) :
    ∀ B : Set T, (mapDrawingHomeo e G).IsNormal B → IsIArc B →
      ((mapDrawingHomeo e G).V ∩ B).ncard ≤ v → ∃ C ∈ cuffs T, lineEnds B ⊆ C := by
  intro B hn hI hc
  obtain ⟨u₀, v₀, hu, hv, hl⟩ := hI
  have hsym : ∀ {x : T}, x ∈ bd T → e.symm x ∈ bd S := fun {x} hx => by
    rw [← GM19.image_bd e.symm]
    exact mem_image_of_mem _ hx
  have hmap : ∀ {a b : T}, IsLineWithEnds B a b → IsLineWithEnds (e.symm '' B) (e.symm a)
    (e.symm b) :=
    fun {a b} ⟨f, h0, h1⟩ => ⟨f.trans (e.symm.image B), by simp [h0], by simp [h1]⟩
  obtain ⟨C, hC, hsub⟩ := hi _ (isNormal_pull e hn) ⟨_, _, hsym hu, hsym hv, hmap hl⟩
    (by rw [ncard_pull]; exact hc)
  refine ⟨e '' C, by rw [cuffs_image_homeo e]; exact mem_image_of_mem _ hC, ?_⟩
  rintro x ⟨y, hy⟩
  exact ⟨e.symm x, hsub ⟨_, hmap hy⟩, by simp⟩

private theorem discBd_image_homeo {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (Δ : Set X) : discBd (e '' Δ) = e '' discBd Δ := by
  unfold discBd
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [← GM19.image_bd (e.image Δ)] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    exact ⟨x.1, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨e.image Δ x, by
      rw [← GM19.image_bd (e.image Δ)]
      exact mem_image_of_mem _ hx, rfl⟩

/-- The null-homotopy condition in a capped surface moves to the model. -/
private theorem capped_map (e : S ≃ₜ T) {C : Set S} {B : Set T}
    (h : IsNullHomotopicOArcInCappedCuff C (e.symm '' B)) :
    IsNullHomotopicOArcInCappedCuff (e '' C) B := by
  obtain ⟨hC, hB, hall⟩ := h
  have hC' : IsCuff (e '' C) := by
    change e '' C ∈ cuffs T
    rw [cuffs_image_homeo e]
    exact mem_image_of_mem _ hC
  refine ⟨hC', ?_, ?_⟩
  · have := isOArc_image e.isEmbedding hB
    rwa [image_image, show (fun x => e (e.symm x)) = id from funext (by simp), image_id] at this
  · intro S₀ _ j₀ D₀ hcap
    let u : S₀ ≃ₜ ULift.{u} S₀ := Homeomorph.ulift.symm
    have hcap' : IsCappedCuff C (ULift.{u} S₀) (fun x => u (j₀ (e x))) (u '' D₀) := by
      obtain ⟨-, hsurf, hemb, hdisc, hbd, hun, hin⟩ := hcap
      have himg : ∀ A : Set S, (fun x => u (j₀ (e x))) '' A = u '' (j₀ '' (e '' A)) := fun A => by
        simp only [image_image]
      have hrange : range (fun x => u (j₀ (e x))) = u '' range j₀ := by
        rw [← image_univ, himg, image_univ, e.range_coe, image_univ]
      refine ⟨hC, isSurface_of_homeo u hsurf, u.isEmbedding.comp (hemb.comp e.isEmbedding), ?_,
        ?_, ?_, ?_⟩
      · obtain ⟨φ⟩ := hdisc
        exact ⟨φ.trans (u.image D₀)⟩
      · rw [discBd_image_homeo, hbd, himg]
      · rw [hrange, ← image_union, hun, image_univ, u.range_coe]
      · rw [hrange, himg, ← image_inter u.injective, hin]
    have hnull := hall (ULift.{u} S₀) _ _ hcap'
    have := IsNullHomotopicOArc.image_homeo u.symm hnull
    convert this using 1
    ext y
    simp [image_image]

/-- Hypothesis (ii) of VII (4.6) along a homeomorphism. -/
theorem hii_map (e : S ≃ₜ T) {G : Drawing S} {v : ℕ}
    (hii : ∀ B : Set S, G.IsNormal B → IsOArc B → (G.V ∩ B).ncard ≤ v →
      IsNullHomotopicOArc B ∨
        ∃ C ∈ cuffs S, IsNullHomotopicOArcInCappedCuff C B ∧ G.V ∩ C ⊆ B) :
    ∀ B : Set T, (mapDrawingHomeo e G).IsNormal B → IsOArc B →
      ((mapDrawingHomeo e G).V ∩ B).ncard ≤ v →
      IsNullHomotopicOArc B ∨
        ∃ C ∈ cuffs T, IsNullHomotopicOArcInCappedCuff C B ∧ (mapDrawingHomeo e G).V ∩ C ⊆ B := by
  intro B hn hO hc
  rcases hii _ (isNormal_pull e hn) (isOArc_image e.symm.isEmbedding hO)
    (by rw [ncard_pull]; exact hc) with h | ⟨C, hC, hcap, hsub⟩
  · left
    have := IsNullHomotopicOArc.image_homeo e h
    rwa [image_image, show (fun x => e (e.symm x)) = id from funext (by simp), image_id] at this
  · refine .inr ⟨e '' C, by rw [cuffs_image_homeo e]; exact mem_image_of_mem _ hC,
      capped_map e hcap, ?_⟩
    rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    obtain rfl := e.injective hxy
    obtain ⟨b, hb, rfl⟩ := hsub ⟨hx, hy⟩
    simpa using hb

/-- Hypothesis (iii) of VII (4.6) along a homeomorphism. -/
theorem hiii_map (e : S ≃ₜ T) {G : Drawing S}
    (hiii : ∀ C ∈ cuffs S, 2 ≤ (G.V ∩ C).ncard) :
    ∀ C ∈ cuffs T, 2 ≤ ((mapDrawingHomeo e G).V ∩ C).ncard := by
  intro C hC
  rw [cuffs_image_homeo e] at hC
  obtain ⟨C₀, hC₀, rfl⟩ := hC
  change 2 ≤ (e '' G.V ∩ e '' C₀).ncard
  rw [← image_inter e.injective, ncard_image_of_injective _ e.injective]
  exact hiii C₀ hC₀

/-- Feasibility comes back along a homeomorphism. -/
theorem isGFeasible_of_map (e : S ≃ₜ T) {G H : Drawing S}
    (h : IsGFeasible (mapDrawingHomeo e G) (mapDrawingHomeo e H)) : IsGFeasible G H := by
  obtain ⟨X, hX, hhom, hsub⟩ := h
  have hhom' := ForestsHomoplastic.map_homeomorph e.symm hhom
  rw [GM12.mapDrawingHomeo_symm] at hhom'
  refine ⟨mapDrawingHomeo e.symm X, IsSurfaceForest.map_homeo e.symm hX, hhom', ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hsub.1 hx
    simpa using hy
  · intro f hf
    rw [GM12.mapDrawingHomeo_edges] at hf
    obtain ⟨g, hg, rfl⟩ := hf
    have := hsub.2 hg
    rw [GM12.mapDrawingHomeo_edges] at this
    obtain ⟨g₀, hg₀, rfl⟩ := this
    rwa [image_image, show (fun x => e.symm (e x)) = id from funext (by simp), image_id]

end GraphMinor.GM07
