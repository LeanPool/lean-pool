/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14y

/-!
# Graph Minors XIX, Section 14: the coloured painting `(Γ', φ')`
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 TangleDatum

universe w

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space S] [T2Space Shat] {α
  : Type w}
  {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace Slice

variable {T : Set S} {D : TangleDatum cap χ} (s : Slice T D)

/-- The drawing `K` of the fragment. -/
noncomputable def K : Drawing S := s.exists_K.choose

include s

theorem K_U : s.K.U = cutF (cap.emb ∘ s.f) s.𝒲 := s.exists_K.choose_spec.1

theorem K_V : s.K.V = Subtype.val '' s.Nb := s.exists_K.choose_spec.2.1

theorem fd : FrameData χ.Φ s.Q.Γ s.K (Subtype.val : ↥Tᶜ → S) := s.exists_K.choose_spec.2.2.1

theorem anchored : IsAnchored s.Q.Γ s.K := s.exists_K.choose_spec.2.2.2

theorem mem_pullV {x : ↥Tᶜ} : x ∈ pullV s.Q.Γ s.K Subtype.val ↔ x ∈ s.N := by
  constructor
  · rintro (h | h)
    · exact s.mem_QV.mp h
    · rw [s.K_V] at h
      obtain ⟨y, hy, e⟩ := h
      exact Subtype.ext e ▸ hy.1
  · intro h
    exact .inl (s.mem_QV.mpr h)

theorem bd_pullV : bd ↥Tᶜ \ pullV s.Q.Γ s.K Subtype.val = bd ↥Tᶜ \ s.Nb := by
  ext x
  simp only [mem_sdiff, s.mem_pullV, Nb, mem_inter_iff]
  tauto

theorem pullFrameV_eq : pullFrameV χ.Φ s.K (Subtype.val : ↥Tᶜ → S) = s.Nb := by
  ext x
  constructor
  · rintro (h | h)
    · exact absurd (s.bd_sub_T (χ.Φ.V_subset h)) x.2
    · rw [s.K_V] at h
      obtain ⟨y, hy, e⟩ := h
      exact Subtype.ext e ▸ hy
  · intro h
    exact .inr (by rw [s.K_V]; exact ⟨x, h, rfl⟩)

variable [Nonempty ↥Tᶜ]

omit s in
/-- The painting `Γ'`. -/
noncomputable def paint (s : Slice T D) (ε : Set ↥Tᶜ → Bool) : Painting ↥Tᶜ := s.fd.paint (flipOf ε)

theorem paint_V (ε : Set ↥Tᶜ → Bool) : (s.paint ε).V = s.N := by
  ext x
  exact s.mem_pullV

theorem arc_E (ε : Set ↥Tᶜ → Bool) {c : Set ↥Tᶜ} (hc : c ∈ arcComponentsIn (bd ↥Tᶜ \ s.Nb)) : c ∈
  (s.paint ε).E :=
  (s.fd.mem_paint_E _).mpr (.inl (by rw [s.bd_pullV]; exact hc))

theorem border_arc (ε : Set ↥Tᶜ → Bool) {e : Set ↥Tᶜ} (he : e ∈ (s.paint ε).E)
  (hb : Painting.IsBorder e) : e ∈ arcComponentsIn (bd ↥Tᶜ \ s.Nb) := by
  rw [← s.bd_pullV]
  exact s.fd.mem_arcs_of_border _ he hb

theorem γ_arc (ε : Set ↥Tᶜ → Bool) {c : Set ↥Tᶜ} (hc : c ∈ arcComponentsIn (bd ↥Tᶜ \ s.Nb)) :
  (s.paint ε).γ c = arcMarch s.isSurface (flipOf ε c) c := by
  have hp : c ∈ arcComponentsIn (bd ↥Tᶜ \ pullV s.Q.Γ s.K Subtype.val) := by
    rwa [s.bd_pullV]
  have hnl := s.fd.pull.notMem_liftPieces hp
  change pullγ s.Q.Γ Subtype.val _ c = _
  rw [pullγ_arc hnl]
  change arcMarch _ (flipOf ε (sideOf χ.Φ s.K Subtype.val c)) c = _
  have hs : c ∈ arcComponentsIn (bd ↥Tᶜ \ pullFrameV χ.Φ s.K Subtype.val) := by
    rwa [s.pullFrameV_eq]
  rw [FrameData.sideOf_eq hc.1 hs subset_rfl]

/-- The hypotheses on the frame. -/
structure IsCutFrame (Φ' : Frame ↥Tᶜ) (Z : Set ↥Tᶜ) (ε : Set ↥Tᶜ → Bool) : Prop where
  V_eq : Φ'.V = s.markN
  Z_eq : Z = s.markZ
  long_iff : ∀ c, Φ'.isLong c ↔ Disjoint c Z
  γ_eq : ∀ c, Φ'.γ c = arcMarch s.isSurface (flipOf ε c) c

theorem paint_fits {Φ' : Frame ↥Tᶜ} {Z : Set ↥Tᶜ} {ε : Set ↥Tᶜ → Bool} (h : s.IsCutFrame Φ' Z ε) :
  (s.paint ε).Fits Φ' := by
  have hS := χ.isSurface
  have := χ.connected
  have hX := s.isSurface
  have hsides : Φ'.sides = arcComponentsIn (bd ↥Tᶜ \ s.markN) := by
    simp only [Frame.sides, h.V_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [h.V_eq] at hx
    rw [s.paint_V]
    exact (s.markN_sub hx).1
  · rintro c ⟨hc, hl⟩
    rw [hsides] at hc
    have hnd : ¬ Disjoint c s.markZ := fun hd ↦ hl ((h.long_iff c).mpr (h.Z_eq ▸ hd))
    obtain ⟨z, hzc, hz⟩ := not_disjoint_iff.mp hnd
    obtain ⟨W, hz⟩ := mem_iUnion.mp hz
    obtain ⟨i, hi, rfl⟩ := mem_iUnion₂.mp hz
    obtain rfl : c = s.arc W i := arcComp_eq_of_mem hc (s.arc_side hi) hzc (s.zx_arc W i)
    exact s.arc_E ε (s.arc_mem W i)
  · intro e he hb c hc hes
    rw [hsides] at hc
    have ha := s.border_arc ε he hb
    rw [s.γ_arc ε ha, h.γ_eq]
    have hne : e.Nonempty := ha.1
    obtain ⟨x, hx⟩ := hne
    have hxb := (ha.2.1 hx).1
    obtain ⟨C, hC, hxC⟩ := sUnion_cuffs (S := ↥Tᶜ) ▸ hxb
    obtain ⟨C₁, a, b, -, -, rfl, -, -, -⟩ := exists_arc_of_mem hX (cuffPar hX) s.finite_markN
      s.two_marks hc
    have hCe : (C₁ : Set ↥Tᶜ) = C := by
      by_contra hne
      exact disjoint_left.mp (cuffs_disjoint C₁.2 hC hne) (arcOf_subset _ _ _ (hes hx)) hxC
    rw [flipOf_eq ε C₁.2 hc.1 (arcOf_subset _ _ _), flipOf_eq ε C₁.2 ha.1 (hes.trans
      (arcOf_subset _ _ _))]
    exact dirAgrees_arcs hX _ s.finite_markN s.two_marks s.finite_Nb s.two ha hc hes
  · exact s.fd.pull.isInternallyThreeConnected _ (fun _ hp ↦ (s.fd.nodup_arcMarch _
      s.fd.pull.finite_pullV s.fd.pull.two hp).1)
      (fun _ hp ↦ (s.fd.nodup_arcMarch _ s.fd.pull.finite_pullV s.fd.pull.two hp).2)
        s.Q.fits.internally_three_connected s.anchored
  · exact s.fd.pull.size_three_region hS _ (fun _ hp ↦ (s.fd.nodup_arcMarch _
      s.fd.pull.finite_pullV s.fd.pull.two hp).1)
      (fun _ hp ↦ (s.fd.nodup_arcMarch _ s.fd.pull.finite_pullV s.fd.pull.two hp).2)
        s.Q.fits.size_three_region s.anchored

end Slice

end GraphMinor.GM19
