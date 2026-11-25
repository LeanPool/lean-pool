/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14ag
public import Mathlib.Data.Set.Card.Arithmetic

import LeanPool.GraphMinor.GM07.Bridge

import LeanPool.GraphMinor.GM19.FeatureCount

import LeanPool.GraphMinor.GM19.FragmentOrient

/-!
# Graph Minors XIX, Section 14: the proof of (14.1)

The boundaries of the wheels, with the singular places of the rims marked, form a feature of bounded
size. By (5.2) there are finitely many of these up to homeomorphism. So the places of
all the paintings lie in finitely many sets of rows, and each of these is well-behaved.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 TangleDatum

universe w

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space S] [T2Space Shat] {α
  : Type w}
  {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace TangleDatum

variable (D : TangleDatum cap χ) {ω₀ : α} {𝒲 : Set (Set Shat)}

omit [T2Space S] in
/-- Each capping disc lies inside a wheel, since its pole does and no rim meets it. -/
theorem cover_compl (hc : D.IsWheelCover ω₀ 𝒲) : (⋃ W ∈ 𝒲, discInt W)ᶜ ⊆ cap.emb '' (bd S)ᶜ := by
  have hS := χ.isSurface
  have hT := cap.isClosedSurface
  have hman : ∀ x : Shat, IsManifoldPoint x := cap.isSurface.2.2
  have hin : ∀ Θ ∈ cuffs S, ∃ W ∈ 𝒲, closure (cap.cuffDisc Θ) ⊆ discInt W := by
    intro Θ hΘ
    obtain ⟨p, hp, hpd, -⟩ := D.rad.exists_pole hΘ
    obtain ⟨W, hW, hpW⟩ := hc.poles_covered p hp
    have hcl : closure (cap.cuffDisc Θ) = cap.cuffDisc Θ ∪ cap.emb '' Θ
      := cap.closure_cuffDisc hΘ
    have hoffr : ∀ {x}, x ∈ cap.cuffDisc Θ → x ∉ range cap.emb := fun {x} hx hr ↦ by
      have : x ∈ (range cap.emb)ᶜ := by
        rw [cap.compl_eq]
        exact mem_biUnion hΘ hx
      exact this hr
    have hoff : Disjoint (closure (cap.cuffDisc Θ)) (discBd W) := by
      refine disjoint_left.mpr fun x hx hxb ↦ ?_
      obtain ⟨y, hy, rfl⟩ := hc.bd_in_interior W hW hxb
      rw [hcl] at hx
      rcases hx with hx | ⟨y', hy', e⟩
      · exact hoffr hx ⟨y, rfl⟩
      · obtain rfl := cap.isEmbedding.injective e
        exact hy.2 (cuff_subset_bd ⟨Θ, hΘ⟩ hy')
    obtain ⟨H, ρ, hdisc⟩ := hc.all_wheels W hW
    have hWd : IsClosedDisc W := hdisc.is_disc
    have hpre : IsPreconnected (closure (cap.cuffDisc Θ)) := isPreconnected_of_isClosedDisc
      (cap.cuffDisc_closedDisc Θ hΘ)
    have hcW : IsClosed W := hWd.isClosed
    refine ⟨W, hW, hpre.subset_left_of_subset_union (hWd.isOpen_discInt hman) hcW.isOpen_compl
      (disjoint_left.mpr fun y hy hy' ↦ hy' (Surface.discInt_subset _ hy)) ?_ ⟨p, subset_closure
        hpd, hpW, ?_⟩⟩
    · intro y hy
      by_cases hyW : y ∈ W
      · exact .inl ⟨hyW, disjoint_left.mp hoff hy⟩
      · exact .inr hyW
    · exact disjoint_left.mp hoff (subset_closure hpd)
  intro y hy
  have key : ∀ Θ ∈ cuffs S, y ∉ closure (cap.cuffDisc Θ) := fun Θ hΘ hyc ↦ by
    obtain ⟨W, hW, hsub⟩ := hin Θ hΘ
    exact hy (mem_iUnion₂.mpr ⟨W, hW, hsub hyc⟩)
  by_cases hr : y ∈ range cap.emb
  · obtain ⟨x, rfl⟩ := hr
    refine ⟨x, fun hxb ↦ ?_, rfl⟩
    obtain ⟨Θ, hΘ, hxΘ⟩ := sUnion_cuffs (S := S) ▸ hxb
    refine key Θ hΘ ?_
    rw [cap.closure_cuffDisc hΘ]
    exact .inr ⟨x, hxΘ, rfl⟩
  · have : y ∈ (range cap.emb)ᶜ := hr
    rw [cap.compl_eq] at this
    obtain ⟨Θ, hΘ, hyΘ⟩ := mem_iUnion₂.mp this
    exact absurd (subset_closure hyΘ) (key Θ hΘ)

omit [T2Space S] in
/-- A wheel cover is a cut of `Σ`, from any homeomorphism of `Σ`. -/
theorem isCutData (hc : D.IsWheelCover ω₀ 𝒲) (f : S ≃ₜ S) : IsCutData (cap.emb ∘ f) 𝒲 := by
  have hS := χ.isSurface
  have : CompactSpace S := hS.1
  have hbd : (fun x ↦ f x) '' (bd S)ᶜ = (bd S)ᶜ := by
    rw [image_compl_eq f.bijective, image_bd f]
  have himg : (cap.emb ∘ f) '' (bd S)ᶜ = cap.emb '' (bd S)ᶜ := by
    rw [image_comp]
    exact congrArg (cap.emb '' ·) hbd
  have hdisc : ∀ W ∈ 𝒲, IsClosedDisc W := fun W hW ↦ by
    obtain ⟨H, ρ, h⟩ := hc.all_wheels W hW
    exact h.is_disc
  refine ⟨?_, hc.finite_wheels, hdisc, hc.pairwise_disjoint, fun W hW ↦ ?_, ?_⟩
  · exact (cap.isEmbedding.continuous.comp f.continuous).isClosedEmbedding
      (cap.isEmbedding.injective.comp f.injective)
  · rw [himg]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hc.bd_in_interior W hW hy
    exact ⟨x, hx.2, rfl⟩
  · rw [himg]
    exact D.cover_compl hc

end TangleDatum

namespace Slice

variable {T : Set S} {D : TangleDatum cap χ} (s : Slice T D)
include s

theorem ncard_hub_le (W : ↥s.𝒲) : (s.fr W).H.V.ncard ≤ 4 * (s.fr W).ρ + 4 := by
  rcases (s.fr W).hW.hub_cases with ⟨z, hV, -, -⟩ | ⟨hH, hle, -, -⟩
  · rw [hV, ncard_singleton]
    omega
  · obtain ⟨-, -, -, hcirc, -⟩ := id hH
    rw [IsCircuit.ncard_V hcirc.2]
    exact hle

theorem ncard_sing_le (W : ↥s.𝒲) : (s.sing W).ncard ≤ 4 * (s.fr W).ρ + 5 := by
  have hsub : s.sing W ⊆ insert ((s.fr W).R.k - 1) ((s.fr W).R.changes (s.fr W).sp) := by
    rintro i ⟨hi, h | h⟩
    · exact .inl (by omega)
    · exact .inr ⟨hi, h⟩
  have hfin : ((s.fr W).R.changes (s.fr W).sp).Finite := (finite_lt_nat _).subset fun _ h ↦ h.1
  have h₁ := ncard_le_ncard hsub (hfin.insert _)
  have h₂ := ncard_insert_le ((s.fr W).R.k - 1) ((s.fr W).R.changes (s.fr W).sp)
  have h₃ := (s.fr W).R.ncard_changes_le (s.fr W).hW (s.fr W).hbdS (s.fr W).hin (s.fr W).sp
  have h₄ := s.ncard_hub_le W
  omega

/-- The marked points of a rim. -/
theorem ncard_marks_le {b : ℕ} (hb : ∀ W, (s.fr W).ρ ≤ b) : (s.markN ∪ s.markZ).ncard ≤ 3 *
  (4 * b + 5) * s.𝒲.ncard := by
  classical
  have := s.finite_𝒲
  have := Fintype.ofFinite ↥s.𝒲
  let A : ↥s.𝒲 → Set ↥Tᶜ := fun W ↦ (s.vx W '' s.sing W) ∪ ((fun i ↦ s.vx W (i + 1)) '' s.sing W) ∪
    (s.zx W '' s.sing W)
  have hA : ∀ W, (A W).ncard ≤ 3 * (4 * b + 5) := fun W ↦ by
    have h₁ := ncard_image_le (f := s.vx W) (s.finite_sing W)
    have h₂ := ncard_image_le (f := fun i ↦ s.vx W (i + 1)) (s.finite_sing W)
    have h₃ := ncard_image_le (f := s.zx W) (s.finite_sing W)
    have h₄ := ncard_union_le ((s.vx W '' s.sing W) ∪ ((fun i ↦ s.vx W (i + 1)) '' s.sing W))
      (s.zx W '' s.sing W)
    have h₅ := ncard_union_le (s.vx W '' s.sing W) ((fun i ↦ s.vx W (i + 1)) '' s.sing W)
    have h₆ := s.ncard_sing_le W
    have h₇ := hb W
    change ((s.vx W '' s.sing W) ∪ ((fun i ↦ s.vx W (i + 1)) '' s.sing W) ∪
      (s.zx W '' s.sing W)).ncard ≤ _
    omega
  have hsub : s.markN ∪ s.markZ ⊆ ⋃ W, A W := by
    rintro x (hx | hx)
    · obtain ⟨W, hx⟩ := mem_iUnion.mp hx
      obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp hx
      rcases hx with rfl | hx
      · exact mem_iUnion.mpr ⟨W, .inl (.inl ⟨i, hi, rfl⟩)⟩
      · exact mem_iUnion.mpr ⟨W, .inl (.inr ⟨i, hi, (mem_singleton_iff.mp hx).symm⟩)⟩
    · obtain ⟨W, hx⟩ := mem_iUnion.mp hx
      obtain ⟨i, hi, rfl⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion.mpr ⟨W, .inr ⟨i, hi, rfl⟩⟩
  have hfinA : ∀ W, (A W).Finite := fun W ↦ (((s.finite_sing W).image _).union
    ((s.finite_sing W).image _)).union ((s.finite_sing W).image _)
  have h₁ := ncard_le_ncard hsub (finite_iUnion hfinA)
  have h₂ : (⋃ W, A W).ncard ≤ ∑ W, (A W).ncard := by
    simpa using ncard_iUnion_le_of_fintype A
  have h₃ : ∑ W, (A W).ncard ≤ ∑ _W : ↥s.𝒲, 3 * (4 * b + 5) := Finset.sum_le_sum fun W _ ↦ hA W
  have h₄ : ∑ _W : ↥s.𝒲, 3 * (4 * b + 5) = 3 * (4 * b + 5) * s.𝒲.ncard := by
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm,
      ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  omega

/-- **The feature.** -/
theorem exists_feature {b : ℕ} (hb : ∀ W, (s.fr W).ρ ≤ b) : ∃ K : Drawing S, IsFeature χ.Φ K ∧ K.U
  = cutF (cap.emb ∘ s.f) s.𝒲 ∧ K.V = Subtype.val '' (s.markN ∪ s.markZ) ∧
    K.V.ncard + K.E.ncard ≤ 2 * (3 * (4 * b + 5) * s.𝒲.ncard) := by
  classical
  have hX := s.isSurface
  have hfin : (s.markN ∪ s.markZ).Finite := s.finite_markN.union s.finite_markZ
  have hsub : s.markN ∪ s.markZ ⊆ bd ↥Tᶜ := union_subset (fun x hx ↦ (s.markN_sub hx).2)
    (fun x hx ↦ by
    obtain ⟨W, hx⟩ := mem_iUnion.mp hx
    obtain ⟨i, hi, rfl⟩ := mem_iUnion₂.mp hx
    exact s.cf_sub_bd W.2 (s.arc_cf W i (s.zx_arc W i)))
  have h2 : ∀ C : cuffs ↥Tᶜ, ∃ p ∈ (s.markN ∪ s.markZ) ∩ C.1, ∃ q ∈ (s.markN ∪ s.markZ) ∩ C.1, p ≠
    q := fun C ↦ by
    obtain ⟨p, hp, q, hq, hne⟩ := s.two_marks C
    exact ⟨p, ⟨.inl hp.1, hp.2⟩, q, ⟨.inl hq.1, hq.2⟩, hne⟩
  obtain ⟨K, hU, hV, hE⟩ := exists_boundaryDrawing hX s.isClosedEmbedding hfin hsub h2
  rw [s.image_bd] at hU
  have hoff : Disjoint K.U (bd S) := by
    refine disjoint_left.mpr fun x hx hxb ↦ ?_
    rw [hU, ← s.image_bd] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2 (s.bd_sub_T hxb)
  have hEsub : ∀ e ∈ K.E, e ⊆ K.U := fun e he ↦ he.2.1.trans sdiff_subset
  refine ⟨K, ⟨fun e he ↦ hoff.mono_left (hEsub e he), fun v hv ↦ ?_,
    fun c hc ↦ hoff.mono_right ?_⟩, hU, hV, ?_⟩
  · rw [hV] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    obtain ⟨R, hR, -, -, -, hxR, -⟩ := exists_two_arcs hX hfin h2 hx (hsub hx)
    have hEm : Subtype.val '' R ∈ K.E := by
      change _ ∈ arcComponentsIn (K.U \ K.V)
      rw [hE]
      exact mem_image_of_mem _ hR
    refine ⟨_, hEm, image_closure_subset_closure_image continuous_subtype_val
      (mem_image_of_mem _ hxR.1), ?_⟩
    rintro ⟨y, hy, e⟩
    exact hxR.2 (Subtype.ext e ▸ hy)
  · exact fun x hx ↦ (hc.1.2.1 hx).1
  · have h₁ : K.V.ncard ≤ (s.markN ∪ s.markZ).ncard := by
      rw [hV]
      exact ncard_image_le hfin
    have h₂ : K.E.ncard ≤ (arcComponentsIn (bd ↥Tᶜ \ (s.markN ∪ s.markZ))).ncard := by
      change (arcComponentsIn (K.U \ K.V)).ncard ≤ _
      rw [hE]
      exact ncard_image_le (finite_arcComponentsIn_bd hX hfin h2)
    have h₃ := ncard_arcs_le hX hfin h2
    have h₄ := s.ncard_marks_le hb
    omega

end Slice

/-- **Graph Minors XIX, (14.1).** -/
theorem theorem_14_1_proof : Theorem141Statement.{w} := by
  intro S Shat _ _ _ _ β _ cap χ hd 𝒮 hcl hS2 k ω₀ hk m n _ hn
  classical
  have hS := χ.isSurface
  let b := 2 * n * 5 ^ (2 * m)
  obtain ⟨𝓕, hf, h𝓕⟩ := GraphMinor.GM19.theorem_5_2_proof S hS χ.connected χ.Φ (2 * (3 *
    (4 * b + 5) * (m + numCuffs S)))
  have : Finite 𝓕 := hf
  refine ⟨⋃ K₀ : 𝓕, rowPlaces cap hd 𝒮 ω₀ K₀.1 b, IsWellBehavedPlaces.iUnion fun K₀ ↦
    rowPlaces_wellBehaved hd hcl hS2 hk K₀.1 b, ?_⟩
  intro D hm hfl
  obtain ⟨𝒲, hc, hnum, hrad⟩ := theorem_12_4_proof D hd hk hn hfl
  have ha : 4 ≤ 5 ^ (2 * m) * n := by
    have : 1 ≤ 5 ^ (2 * m) := Nat.one_le_pow _ _ (by norm_num)
    nlinarith
  have hbe : b = 2 * (5 ^ (2 * m) * n) := by simp only [b]; ring
  have hrep : 25 * (5 ^ (2 * m) * n) < D.rep := by
    have h₁ := hfl.1
    have h25 : 5 ^ (2 * m + 2) * n = 25 * (5 ^ (2 * m) * n) := by rw [pow_add]; ring
    omega
  have hex : ∀ W : ↥𝒲, ∃ fr : WheelFrame D W.1, fr.ρ = D.wheelRadius W.1 := fun W ↦ by
    have := hrad W.1 W.2
    exact exists_wheelFrame (hc.all_wheels W.1 W.2) (hc.bd_in_interior W.1 W.2)
      (hc.interior_vertex W.1 W.2) (by omega)
  choose fr hρ using hex
  have hb : ∀ W, (fr W).ρ ≤ b := fun W ↦ (hρ W).trans_le (hrad W.1 W.2)
  have hord : D.rep ≤ D.ord := (tangleRep_spec D.rad D.ord D.𝒯).1
  have hθ : 4 * n * 5 ^ (2 * m) + 3 = 2 * b + 3 := by simp only [b]; ring
  let s₀ : Slice (cutT (cap.emb ∘ Homeomorph.refl S) 𝒲) D := ⟨𝒲, fr, Homeomorph.refl S,
    IsFramePreservingHomeo.refl' _, D.isCutData hc _, rfl⟩
  obtain ⟨K, hF, hU, hV, hsize⟩ := s₀.exists_feature hb
  have hle : K.V.ncard + K.E.ncard ≤ 2 * (3 * (4 * b + 5) * (m + numCuffs S)) := hsize.trans (by
    gcongr)
  obtain ⟨K₀, hK₀, f, hfp, hfU, hfV⟩ := h𝓕 K hF hle
  have hcut := D.isCutData hc f
  let r : Row D ω₀ K₀ b :=
    { 𝒲 := 𝒲
      fr := fr
      f := f
      hf := hfp
      cut := hcut
      cov := hc.Z_covered
      hb := hb
      hU := by
        ext x
        have h₁ : f x ∈ K.U ↔ x ∈ K₀.U := by
          rw [← hfU]
          exact ⟨fun ⟨y, hy, e⟩ ↦ f.injective e ▸ hy, fun h ↦ ⟨x, h, rfl⟩⟩
        rw [← h₁, hU]
        rfl
      hV := by
        intro W i hi hs x hx
        have hsing : i ∈ s₀.sing W := ⟨hi, hs⟩
        have hfx : f x ∈ K.V := by
          rw [hV]
          rcases hx with h | h | h
          · have e : cap.emb (f x) = s₀.e (s₀.vx W i) := h.trans (s₀.e_vx W i).symm
            exact ⟨s₀.vx W i, .inl (mem_iUnion.mpr ⟨W, mem_iUnion₂.mpr ⟨_, hsing, .inl rfl⟩⟩),
              (cap.isEmbedding.injective e).symm⟩
          · have e : cap.emb (f x) = s₀.e (s₀.vx W (i + 1)) := h.trans (s₀.e_vx W (i + 1)).symm
            exact ⟨s₀.vx W (i + 1), .inl (mem_iUnion.mpr ⟨W, mem_iUnion₂.mpr ⟨_, hsing,
              .inr rfl⟩⟩), (cap.isEmbedding.injective e).symm⟩
          · have e : cap.emb (f x) = s₀.e (s₀.zx W i) := h.trans (s₀.e_zx W i).symm
            exact ⟨s₀.zx W i, .inr (mem_iUnion.mpr ⟨W, mem_iUnion₂.mpr ⟨_, hsing, rfl⟩⟩),
              (cap.isEmbedding.injective e).symm⟩
        rw [← hfV] at hfx
        obtain ⟨y, hy, e⟩ := hfx
        exact f.injective e ▸ hy }
  refine ⟨coverLoc 𝒲 hc.finite_wheels hc.pairwise_disjoint fr, ?_, mem_iUnion.mpr ⟨⟨K₀, hK₀⟩, D,
    hm, r, rfl⟩⟩
  refine coverLoc_isolates 𝒲 _ _ fr (by omega) (fun W ↦ ?_) ?_
  · have := hb W
    omega
  · omega

end GraphMinor.GM19
