/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
public import LeanPool.GraphMinor.Surface.DiscPolygon
import LeanPool.GraphMinor.GM07.Section2Base
import LeanPool.GraphMinor.GM07.Section2Euler
import LeanPool.GraphMinor.GM07.NetSwapBasic
import LeanPool.GraphMinor.Surface.InvarianceOfDomain
import LeanPool.GraphMinor.Surface.DiscArcs

/-!
# Sliding along a side of the net

The slide on page 227 of VII (4.6) moves points along a central edge. We
do it in `Δ`, where this edge is two sides: a homeomorphism of the
boundary circle which acts in the same way on both sides extends to the
closed disc. Since it respects the pasting along the edge, it comes down
to a homeomorphism of `Σ′`.
-/

public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

/-- A homeomorphism of the boundary of a closed disc extends to the disc. -/
theorem exists_disc_homeo_of_bd {D : Type} [TopologicalSpace D]
    (hD : IsClosedDisc (univ : Set D)) (B : bd D ≃ₜ bd D) :
    ∃ b : D ≃ₜ D, ∀ x : bd D, b x.1 = (B x).1 := by
  have hb : discBd (univ : Set D) = bd D := image_bd_homeomorph (Homeomorph.Set.univ D)
  obtain ⟨φ₀⟩ := hD.isOArc_discBd
  let C : discBd (univ : Set D) ≃ₜ bd D := Homeomorph.setCongr hb
  let φ₁ : Circle ≃ₜ discBd (univ : Set D) := (φ₀.trans C).trans (B.trans C.symm)
  obtain ⟨h₀, g₀, c₀, he₀⟩ := exists_chart_extending hD φ₀
  obtain ⟨h₁, g₁, c₁, he₁⟩ := exists_chart_extending hD φ₁
  have hm₀ : ∀ x : D, h₀ x ∈ Metric.closedBall (0 : ℂ) 1 := fun x => c₀.hm (mem_univ x)
  have hm₁ : ∀ x : D, h₁ x ∈ Metric.closedBall (0 : ℂ) 1 := fun x => c₁.hm (mem_univ x)
  have hc₀ : Continuous h₀ := continuousOn_univ.mp c₀.hc
  have hc₁ : Continuous h₁ := continuousOn_univ.mp c₁.hc
  let b : D ≃ₜ D :=
    { toFun := fun x => g₁ (h₀ x)
      invFun := fun x => g₀ (h₁ x)
      left_inv := fun x => by
        change g₀ (h₁ (g₁ (h₀ x))) = x
        rw [c₁.hg (hm₀ x), c₀.gh (mem_univ x)]
      right_inv := fun x => by
        change g₁ (h₀ (g₀ (h₁ x))) = x
        rw [c₀.hg (hm₁ x), c₁.gh (mem_univ x)]
      continuous_toFun := c₁.gc.comp_continuous hc₀ hm₀
      continuous_invFun := c₀.gc.comp_continuous hc₁ hm₁ }
  refine ⟨b, fun x => ?_⟩
  obtain ⟨z, hz⟩ : ∃ z, (C (φ₀ z)) = x := ⟨(φ₀.trans C).symm x, by simp⟩
  have ht : Circle.exp (Complex.arg z) = z := Circle.exp_arg z
  set t := Complex.arg z with htdef
  have h1 : g₀ (eC t) = x.1 := by
    rw [he₀, ht, ← hz]
    rfl
  have hball : eC t ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp [eC]
  have h2 : h₀ x.1 = eC t := by
    rw [← h1, c₀.hg hball]
  change g₁ (h₀ x.1) = (B x).1
  rw [h2, he₁, ht, ← hz]
  simp [φ₁]
  rfl

/-- The action of a slide of the side parameter on `Δ`. -/
private noncomputable def bdSlide {S : Type} [TopologicalSpace S] (N : Net S) (i : Fin N.r)
    (σ : unitInterval → unitInterval) (x : N.D) : N.D :=
  open Classical in
  if x ∈ range (N.f i) then N.f i (σ (Function.invFun (N.f i) x))
  else if x ∈ range (N.g i) then N.g i (σ (Function.invFun (N.g i) x)) else x

section

variable {S : Type} [TopologicalSpace S] (N : Net S) (i : Fin N.r)
  {σ : unitInterval → unitInterval}

private theorem bdSlide_f (r : unitInterval) : bdSlide N i σ (N.f i r) = N.f i (σ r) := by
  have h : N.f i r ∈ range (N.f i) := ⟨r, rfl⟩
  simp only [bdSlide, h, ite_true]
  rw [Function.leftInverse_invFun (N.injective_f i) r]

private theorem bdSlide_g (h0 : σ 0 = 0) (h1 : σ 1 = 1) (r : unitInterval) :
    bdSlide N i σ (N.g i r) = N.g i (σ r) := by
  by_cases h : N.g i r ∈ range (N.f i)
  · obtain ⟨r', hr'⟩ := h
    have hr'Ioo : r' ∉ Ioo (0 : unitInterval) 1 := fun hm =>
      N.internally_disjoint_fg i i r' hm ⟨r, hr'.symm⟩
    have hrIoo : r ∉ Ioo (0 : unitInterval) 1 := fun hm =>
      N.internally_disjoint_gf i i r hm ⟨r', hr'⟩
    have hσr : σ r = r := by
      rcases Net.unitInterval_eq_zero_or_one_or_mem_Ioo r with rfl | rfl | hm
      · exact h0
      · exact h1
      · exact (hrIoo hm).elim
    have hσr' : σ r' = r' := by
      rcases Net.unitInterval_eq_zero_or_one_or_mem_Ioo r' with rfl | rfl | hm
      · exact h0
      · exact h1
      · exact (hr'Ioo hm).elim
    rw [← hr', bdSlide_f, hσr', hσr, hr']
  · have hg : N.g i r ∈ range (N.g i) := ⟨r, rfl⟩
    simp only [bdSlide, h, hg, ite_true, ite_false]
    rw [Function.leftInverse_invFun (N.injective_g i) r]

private theorem bdSlide_off (h0 : σ 0 = 0) (h1 : σ 1 = 1) {x : N.D}
    (hf : x ∉ N.f i '' Ioo (0 : unitInterval) 1) (hg : x ∉ N.g i '' Ioo (0 : unitInterval) 1) :
    bdSlide N i σ x = x := by
  by_cases h : x ∈ range (N.f i)
  · obtain ⟨r, rfl⟩ := h
    have hσr : σ r = r := by
      rcases Net.unitInterval_eq_zero_or_one_or_mem_Ioo r with rfl | rfl | hm
      · exact h0
      · exact h1
      · exact (hf ⟨r, hm, rfl⟩).elim
    rw [bdSlide_f, hσr]
  · by_cases h' : x ∈ range (N.g i)
    · obtain ⟨r, rfl⟩ := h'
      have hσr : σ r = r := by
        rcases Net.unitInterval_eq_zero_or_one_or_mem_Ioo r with rfl | rfl | hm
        · exact h0
        · exact h1
        · exact (hg ⟨r, hm, rfl⟩).elim
      rw [bdSlide_g N i h0 h1, hσr]
    · simp only [bdSlide, h, h', ite_false]

end

/-- A slide of the side parameter, used on both sides of a pair, extends to the disc. -/
theorem Net.exists_disc_slide {S : Type} [TopologicalSpace S] (N : Net S) (i : Fin N.r)
    (σ : unitInterval ≃ₜ unitInterval) (h0 : σ 0 = 0) (h1 : σ 1 = 1) :
    ∃ b : N.D ≃ₜ N.D, (∀ r, b (N.f i r) = N.f i (σ r)) ∧ (∀ r, b (N.g i r) = N.g i (σ r)) ∧
      ∀ x ∈ bd N.D, x ∉ N.f i '' Ioo (0 : unitInterval) 1 →
        x ∉ N.g i '' Ioo (0 : unitInterval) 1 → b x = x := by
  classical
  have : CompactSpace N.D := N.isSurface_D.1
  have : T2Space N.D := N.isSurface_D.2.1
  have hbc : IsClosed (bd N.D) := isClosed_bd N.D
  have : CompactSpace (bd N.D) := isCompact_iff_compactSpace.mp hbc.isCompact
  have h0' : σ.symm 0 = 0 := by rw [← h0, σ.symm_apply_apply, h0]
  have h1' : σ.symm 1 = 1 := by rw [← h1, σ.symm_apply_apply, h1]
  have hfbd : ∀ r, N.f i r ∈ bd N.D := fun r => N.range_f_subset_bd i ⟨r, rfl⟩
  have hgbd : ∀ r, N.g i r ∈ bd N.D := fun r => N.range_g_subset_bd i ⟨r, rfl⟩
  have hmaps : ∀ τ : unitInterval → unitInterval, τ 0 = 0 → τ 1 = 1 → ∀ x ∈ bd N.D,
      bdSlide N i τ x ∈ bd N.D := by
    intro τ h h' x hx
    by_cases hf : x ∈ N.f i '' Ioo (0 : unitInterval) 1
    · obtain ⟨r, -, rfl⟩ := hf
      rw [bdSlide_f]
      exact hfbd _
    by_cases hg : x ∈ N.g i '' Ioo (0 : unitInterval) 1
    · obtain ⟨r, -, rfl⟩ := hg
      rw [bdSlide_g N i h h']
      exact hgbd _
    rw [bdSlide_off N i h h' hf hg]
    exact hx
  have hinv : ∀ τ τ' : unitInterval → unitInterval, τ 0 = 0 → τ 1 = 1 → τ' 0 = 0 → τ' 1 = 1 →
      (∀ r, τ' (τ r) = r) → ∀ x, bdSlide N i τ' (bdSlide N i τ x) = x := by
    intro τ τ' h h' k k' hl x
    by_cases hf : x ∈ range (N.f i)
    · obtain ⟨r, rfl⟩ := hf
      rw [bdSlide_f, bdSlide_f, hl]
    by_cases hg : x ∈ range (N.g i)
    · obtain ⟨r, rfl⟩ := hg
      rw [bdSlide_g N i h h', bdSlide_g N i k k', hl]
    have hf' : x ∉ N.f i '' Ioo (0 : unitInterval) 1 := fun ⟨r, _, hr⟩ => hf ⟨r, hr⟩
    have hg' : x ∉ N.g i '' Ioo (0 : unitInterval) 1 := fun ⟨r, _, hr⟩ => hg ⟨r, hr⟩
    rw [bdSlide_off N i h h' hf' hg', bdSlide_off N i k k' hf' hg']
  obtain ⟨U₁, hU₁, hU₁e⟩ := N.exists_isOpen_inter_bd_eq_image_Ioo_f i 0 1
  obtain ⟨U₂, hU₂, hU₂e⟩ := N.exists_isOpen_inter_bd_eq_image_Ioo_g i 0 1
  let P₃ : Set N.D := bd N.D ∩ U₁ᶜ ∩ U₂ᶜ
  have hP₃ : IsClosed P₃ := (hbc.inter hU₁.isClosed_compl).inter hU₂.isClosed_compl
  have hcont : ∀ A : Set N.D, IsClosed A → IsClosed (bd N.D ∩ bdSlide N i σ ⁻¹' A) := by
    intro A hA
    let c₁ : Set unitInterval := (fun r => N.f i (σ r)) ⁻¹' A
    let c₂ : Set unitInterval := (fun r => N.g i (σ r)) ⁻¹' A
    have hc₁ : IsClosed c₁ := hA.preimage ((N.f i).continuous.comp σ.continuous)
    have hc₂ : IsClosed c₂ := hA.preimage ((N.g i).continuous.comp σ.continuous)
    have heq : bd N.D ∩ bdSlide N i σ ⁻¹' A = N.f i '' c₁ ∪ N.g i '' c₂ ∪ (P₃ ∩ A) := by
      ext x
      constructor
      · rintro ⟨hx, hxA⟩
        by_cases hf : x ∈ range (N.f i)
        · obtain ⟨r, rfl⟩ := hf
          refine .inl (.inl ⟨r, ?_, rfl⟩)
          have : bdSlide N i σ (N.f i r) ∈ A := hxA
          rwa [bdSlide_f] at this
        by_cases hg : x ∈ range (N.g i)
        · obtain ⟨r, rfl⟩ := hg
          refine .inl (.inr ⟨r, ?_, rfl⟩)
          have : bdSlide N i σ (N.g i r) ∈ A := hxA
          rwa [bdSlide_g N i h0 h1] at this
        have hf' : x ∉ N.f i '' Ioo (0 : unitInterval) 1 := fun ⟨r, _, hr⟩ => hf ⟨r, hr⟩
        have hg' : x ∉ N.g i '' Ioo (0 : unitInterval) 1 := fun ⟨r, _, hr⟩ => hg ⟨r, hr⟩
        refine .inr ⟨⟨⟨hx, fun h => hf' (hU₁e ▸ ⟨h, hx⟩)⟩, fun h => hg' (hU₂e ▸ ⟨h, hx⟩)⟩, ?_⟩
        have : bdSlide N i σ x ∈ A := hxA
        rwa [bdSlide_off N i h0 h1 hf' hg'] at this
      · rintro ((⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨⟨⟨hx, h₁⟩, h₂⟩, hxA⟩)
        · refine ⟨hfbd r, ?_⟩
          change bdSlide N i σ (N.f i r) ∈ A
          rw [bdSlide_f]
          exact hr
        · refine ⟨hgbd r, ?_⟩
          change bdSlide N i σ (N.g i r) ∈ A
          rw [bdSlide_g N i h0 h1]
          exact hr
        · refine ⟨hx, ?_⟩
          change bdSlide N i σ x ∈ A
          rw [bdSlide_off N i h0 h1 (fun h => h₁ (hU₁e.symm.subset h).1)
            (fun h => h₂ (hU₂e.symm.subset h).1)]
          exact hxA
    rw [heq]
    exact ((hc₁.isCompact.image (N.f i).continuous).isClosed.union
      (hc₂.isCompact.image (N.g i).continuous).isClosed).union (hP₃.inter hA)
  let E : bd N.D ≃ bd N.D :=
    { toFun := fun x => ⟨bdSlide N i σ x.1, hmaps _ h0 h1 _ x.2⟩
      invFun := fun x => ⟨bdSlide N i σ.symm x.1, hmaps _ h0' h1' _ x.2⟩
      left_inv := fun x => Subtype.ext (hinv _ _ h0 h1 h0' h1' (fun r => σ.symm_apply_apply r) x.1)
      right_inv := fun x => Subtype.ext (hinv _ _ h0' h1' h0 h1 (fun r
        => σ.apply_symm_apply r) x.1) }
  have hEc : Continuous E := by
    rw [continuous_iff_isClosed]
    intro C hC
    obtain ⟨A, hA, rfl⟩ := isClosed_induced_iff.mp hC
    have hheq : E ⁻¹' (Subtype.val ⁻¹' A) = Subtype.val ⁻¹' (bd N.D ∩ bdSlide N i σ ⁻¹' A) := by
      ext x
      constructor
      · intro hx
        exact ⟨x.2, hx⟩
      · intro hx
        exact hx.2
    rw [hheq]
    exact (hcont A hA).preimage continuous_subtype_val
  obtain ⟨b, hb⟩ := exists_disc_homeo_of_bd N.isClosedDisc_D (hEc.homeoOfEquivCompactToT2 (f := E))
  refine ⟨b, fun r => ?_, fun r => ?_, fun x hx hf hg => ?_⟩
  · have := hb ⟨N.f i r, hfbd r⟩
    rw [this]
    exact bdSlide_f N i r
  · have := hb ⟨N.g i r, hgbd r⟩
    rw [this]
    exact bdSlide_g N i h0 h1 r
  · have := hb ⟨x, hx⟩
    rw [this]
    exact bdSlide_off N i h0 h1 hf hg

end GraphMinor.GM07
