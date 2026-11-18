/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Legendre.Basic
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Supporting affine plane at an interior point of the effective domain

For an extended-real potential with convex real epigraph, no value `-∞`, and `0` in the interior of
its effective
domain, a supporting affine function touching at `0` is produced by Hahn–Banach separation
(`exists_supporting_affine_at_zero`); it is not supplied as a premise.

Supporting infrastructure for Cordero-Erausquin–Klartag, Proposition 12.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.Analysis


section
-- Supporting affine planes.

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private theorem linear_eq_zero_of_local_nonpos (L : E →L[ℝ] ℝ)
    (h : ∀ᶠ x in nhds (0 : E), L x ≤ 0) : L = 0 := by
  by_contra hne
  have hex : ∃ x, L x ≠ 0 := by
    by_contra hx
    push Not at hx
    apply hne
    ext x
    change L x = (0 : ℝ)
    exact hx x
  obtain ⟨x, hx⟩ := hex
  have hw : ∃ w, 0 < L w := by
    rcases lt_or_gt_of_ne hx with hn | hp
    · refine ⟨-x, ?_⟩
      simpa only [map_neg] using neg_pos.mpr hn
    · exact ⟨x, hp⟩
  obtain ⟨w, hw⟩ := hw
  have ht : Filter.Tendsto (fun t : ℝ => t • w)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 : E)) := by
    have hc : Continuous (fun t : ℝ => t • w) := continuous_id.smul continuous_const
    have hd : Filter.Tendsto (fun t : ℝ => t • w)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ((0 : ℝ) • w)) :=
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa only [zero_smul] using hd
  have hh := ht.eventually h
  obtain ⟨t, htle, htpos⟩ := (hh.and self_mem_nhdsWithin).exists
  have hpos : 0 < L (t • w) := by
    rw [map_smul, smul_eq_mul]
    exact mul_pos htpos hw
  exact (not_lt_of_ge htle) hpos
/-- The source touching affine plane at0 is genuinely produced from convex
epigraph geometry and the original interior-domain hypothesis. -/
theorem exists_supporting_affine_at_zero [FiniteDimensional ℝ E] (f : E → EReal)
    (hf : ConvexPotential f) (h0 : (0 : E) ∈ interior {x | f x ≠ ⊤}) :
    ∃ a : E, ∀ x, ((inner ℝ a x + (f 0).toReal : ℝ) : EReal) ≤ f x := by
  let D : Set E := {x | f x ≠ ⊤}
  let K : Set E := interior D
  let F : E → ℝ := fun x => (f x).toReal
  let A : Set (E × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}
  have hfin0 : f 0 ≠ ⊤ := interior_subset h0
  have hcoe : ∀ x ∈ D, ((F x : ℝ) : EReal) = f x := by
    intro x hx
    exact EReal.coe_toReal hx (hf.1 x)
  have hreal := hf.convexOn_toReal
  have hK : IsOpen K := isOpen_interior
  have hKconv : Convex ℝ K := hreal.1.interior
  have hcont : ContinuousOn F K := (hreal.subset interior_subset hKconv).continuousOn hK
  have hcont0 : ContinuousAt F (0 : E) := hcont.continuousAt (hK.mem_nhds h0)
  have hAint : (interior A).Nonempty := by
    refine ⟨((0 : E), F 0 + 1), mem_interior_iff_mem_nhds.mpr ?_⟩
    have hd : ∀ᶠ p : E × ℝ in nhds ((0 : E), F 0 + 1), p.1 ∈ K :=
      (continuous_fst.tendsto _).eventually (hK.mem_nhds h0)
    have hF : ContinuousAt (fun p : E × ℝ => F p.1) ((0 : E), F 0 + 1) :=
      ContinuousAt.fst' hcont0
    have hT : ContinuousAt (fun p : E × ℝ => p.2) ((0 : E), F 0 + 1) := continuousAt_snd
    have ht : ∀ᶠ p : E × ℝ in nhds ((0 : E), F 0 + 1), F p.1 < p.2 :=
      ContinuousAt.eventually_lt hF hT (by simp)
    filter_upwards [hd, ht] with p hp hpt
    change f p.1 ≤ (p.2 : EReal)
    rw [← hcoe p.1 (interior_subset hp)]
    exact EReal.coe_le_coe_iff.mpr hpt.le
  have hboundary : ((0 : E), F 0) ∉ interior A := by
    intro hint
    have hpath :
      Filter.Tendsto (fun t : ℝ => ((0 : E), F 0 - t)) (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((0 : E), F 0)) := by
      have hc : Continuous (fun t : ℝ => ((0 : E), F 0 - t)) :=
        continuous_const.prodMk (continuous_const.sub continuous_id)
      have hd :
        Filter.Tendsto (fun t : ℝ => ((0 : E), F 0 - t)) (nhdsWithin 0 (Set.Ioi 0))
          (nhds ((0 : E), F 0 - 0)) :=
        (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa only [sub_zero] using hd
    have hm := hpath.eventually (mem_interior_iff_mem_nhds.mp hint)
    obtain ⟨t, htA, htpos⟩ := (hm.and self_mem_nhdsWithin).exists
    change f 0 ≤ ((F 0 - t : ℝ) : EReal) at htA
    rw [← hcoe 0 hfin0] at htA
    have hr := EReal.coe_le_coe_iff.mp htA
    linarith
  obtain ⟨S, hS, hsep⟩ := geometric_hahn_banach_of_nonempty_interior_point hf.2 hboundary hAint
  let L : E →L[ℝ] ℝ := S.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let q : ℝ := S ((0 : E), 1)
  have hrepr (x : E) (t : ℝ) : S (x, t) = L x + t * q := by
    have hp : (x, t) = (x, 0) + t • ((0 : E), (1 : ℝ)) := by ext <;> simp
    rw [hp, map_add, map_smul]
    rfl
  have hqle : q ≤ 0 := by
    have hm : ((0 : E), F 0 + 1) ∈ A := by
      change f 0 ≤ ((F 0 + 1 : ℝ) : EReal)
      rw [← hcoe 0 hfin0]
      exact EReal.coe_le_coe_iff.mpr (by linarith)
    have hs := hsep _ hm
    rw [hrepr, hrepr] at hs
    simp only [map_zero] at hs
    nlinarith
  have hqne : q ≠ 0 := by
    intro hq
    have hLL : ∀ x ∈ D, L x ≤ 0 := by
      intro x hx
      have hm : (x, F x) ∈ A := by
        change f x ≤ ((F x : ℝ) : EReal)
        rw [hcoe x hx]
      have hs := hsep _ hm
      rw [hrepr, hrepr, hq] at hs
      simpa only [map_zero, mul_zero, add_zero] using hs
    have hDom : ∀ᶠ x in nhds (0 : E), x ∈ D := mem_interior_iff_mem_nhds.mp h0
    have hLoc : ∀ᶠ x in nhds (0 : E), L x ≤ 0 := hDom.mono (fun x hx => hLL x hx)
    have hLzero := linear_eq_zero_of_local_nonpos L hLoc
    apply hS
    apply ContinuousLinearMap.ext
    intro p
    rcases p with ⟨x, t⟩
    rw [hrepr, hLzero, hq]
    simp
  have hqpos : 0 < -q := neg_pos.mpr (lt_of_le_of_ne hqle hqne)
  let T : E →L[ℝ] ℝ := (-q)⁻¹ • L
  let a : E := (InnerProductSpace.toDual ℝ E).symm T
  refine ⟨a, ?_⟩
  intro x
  by_cases hx : f x = ⊤
  · rw [hx]
    exact le_top
  have hm : (x, F x) ∈ A := by
    change f x ≤ ((F x : ℝ) : EReal)
    rw [hcoe x hx]
  have hs := hsep _ hm
  rw [hrepr, hrepr] at hs
  simp only [map_zero, zero_add] at hs
  have hdiv : L x / (-q) ≤ F x - F 0 := by
    apply (div_le_iff₀ hqpos).mpr
    nlinarith
  have ha : inner ℝ a x = L x / (-q) := by
    dsimp [a]
    rw [InnerProductSpace.toDual_symm_apply]
    simp only [T, smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [← hcoe x hx]
  apply EReal.coe_le_coe_iff.mpr
  rw [ha]
  change L x / (-q) + F 0 ≤ F x
  linarith

end

end FunctionalInequalities.Analysis
