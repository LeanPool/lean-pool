/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic.Continuity

/-!
# Connected-domain closure and separated branches

The closure argument only requires differentiability; derivatives need not
vary continuously and zero values are treated by open level sets.
-/

@[expose] public section

open Set Metric

namespace PlanarMidpoint

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {s : Set E} {f : E → F}

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- A nonempty open fiber of a continuous function on a preconnected set
is the whole domain. The fiber is open in the ambient space. -/
theorem is_const_of_isOpen_fiber (hs : IsPreconnected s)
    (hf : ContinuousOn f s) {c : F}
    (hopen : IsOpen (s ∩ f ⁻¹' {c}))
    (hne : ∃ y ∈ s, f y = c) : ∀ x ∈ s, f x = c := by
  obtain ⟨y, hy, hyc⟩ := hne
  intro x hx
  have h₂ := hf.comp_continuous continuous_subtype_val (fun x ↦ x.2)
  by_contra h₃
  obtain ⟨t, ht, ht'⟩ := (isClosed_singleton (x := c)).preimage h₂
  have ht'' : ∀ a ∈ s, a ∈ t ↔ f a ≠ c := by
    simpa [Set.ext_iff] using ht'
  obtain ⟨z, H₁, H₂, H₃⟩ := hs _ _ hopen ht
    (fun x h ↦ by simp [h, ht'', eq_or_ne])
    ⟨y, by simpa [hyc]⟩ ⟨x, by simp [ht'' _ hx, hx, h₃]⟩
  exact (ht'' _ H₁).mp H₃ H₂.2

/-- Derivative zero away from the zero fiber already forces constancy.
This needs no continuity of the derivative and makes no assertion about
passing derivatives across the boundary of the zero fiber. -/
theorem exists_is_const_of_fderiv_eq_zero_off_zero
    (hs : IsOpen s) (hconn : IsPreconnected s)
    (hf : DifferentiableOn ℝ f s)
    (hzero : ∀ x ∈ s, f x ≠ 0 → fderiv ℝ f x = 0) :
    ∃ c, ∀ x ∈ s, f x = c := by
  by_cases hn : ∃ y ∈ s, f y ≠ 0
  · obtain ⟨y, hy, hny⟩ := hn
    refine ⟨f y, is_const_of_isOpen_fiber hconn hf.continuousOn ?_ ⟨y, hy, rfl⟩⟩
    let u := s ∩ f ⁻¹' ({0}ᶜ : Set F)
    have hu : IsOpen u := hf.continuousOn.isOpen_inter_preimage hs isOpen_compl_singleton
    have hfu : DifferentiableOn ℝ f u := hf.mono inter_subset_left
    have hzu : u.EqOn (fderiv ℝ f) 0 := fun x hx ↦ hzero x hx.1 hx.2
    have hv := hu.isOpen_inter_preimage_of_fderiv_eq_zero hfu hzu {f y}
    have heq : u ∩ f ⁻¹' {f y} = s ∩ f ⁻¹' {f y} := by
      ext x
      simp only [u, mem_inter_iff, mem_preimage, mem_compl_iff, mem_singleton_iff]
      constructor
      · exact fun h ↦ ⟨h.1.1, h.2⟩
      · exact fun h ↦ ⟨⟨h.1, h.2 ▸ hny⟩, h.2⟩
    rwa [heq] at hv
  · refine ⟨0, fun x hx ↦ ?_⟩
    by_contra h
    exact hn ⟨x, hx, h⟩

/-- Two-stage closure for a differential rigidity argument. An attained
value in an open regular locus propagates through a clopen fiber. If the
regular locus is never attained, the exceptional-locus argument only needs
to prove vanishing at nonzero values. -/
theorem exists_is_const_of_regular_locus
    (hs : IsOpen s) (hconn : IsPreconnected s)
    (hf : DifferentiableOn ℝ f s)
    (G : Set F) (hG : IsOpen G)
    (hregular : ∀ x ∈ s, f x ∈ G → fderiv ℝ f x = 0)
    (hexceptional : (∀ x ∈ s, f x ∉ G) →
      ∀ x ∈ s, f x ≠ 0 → fderiv ℝ f x = 0) :
    ∃ c, ∀ x ∈ s, f x = c := by
  by_cases hn : ∃ y ∈ s, f y ∈ G
  · obtain ⟨y, hy, hGy⟩ := hn
    refine ⟨f y, is_const_of_isOpen_fiber hconn hf.continuousOn ?_ ⟨y, hy, rfl⟩⟩
    let u := s ∩ f ⁻¹' G
    have hu : IsOpen u := hf.continuousOn.isOpen_inter_preimage hs hG
    have hfu : DifferentiableOn ℝ f u := hf.mono inter_subset_left
    have hzu : u.EqOn (fderiv ℝ f) 0 := fun x hx ↦ hregular x hx.1 hx.2
    have hv := hu.isOpen_inter_preimage_of_fderiv_eq_zero hfu hzu {f y}
    have heq : u ∩ f ⁻¹' {f y} = s ∩ f ⁻¹' {f y} := by
      ext x
      simp only [u, mem_inter_iff, mem_preimage, mem_singleton_iff]
      constructor
      · exact fun h ↦ ⟨h.1.1, h.2⟩
      · exact fun h ↦ ⟨⟨h.1, h.2 ▸ hGy⟩, h.2⟩
    rwa [heq] at hv
  · apply exists_is_const_of_fderiv_eq_zero_off_zero hs hconn hf
    apply hexceptional
    intro x hx hGx
    exact hn ⟨x, hx, hGx⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Two separated continuous branches cannot switch arbitrarily close to a point.
The branch classification must hold throughout a neighborhood before this
lemma can be used to identify derivatives. -/
theorem eventually_eq_left_branch {g h : E → F} {x : E}
    (hf : ContinuousAt f x) (hh : ContinuousAt h x)
    (hsep : g x ≠ h x) (hfg : f x = g x)
    (hbranches : ∀ᶠ y in nhds x, f y = g y ∨ f y = h y) :
    f =ᶠ[nhds x] g := by
  have hne : f x ≠ h x := hfg ▸ hsep
  filter_upwards [(hf.ne_iff_eventually_ne hh).mp hne, hbranches] with y hy hcase
  exact hcase.resolve_right hy

/-- Local equality with a selected branch identifies the full Fréchet derivative. -/
theorem fderiv_eq_left_branch {g h : E → F} {x : E}
    (hf : ContinuousAt f x) (hh : ContinuousAt h x)
    (hsep : g x ≠ h x) (hfg : f x = g x)
    (hbranches : ∀ᶠ y in nhds x, f y = g y ∨ f y = h y) :
    fderiv ℝ f x = fderiv ℝ g x :=
  (eventually_eq_left_branch hf hh hsep hfg hbranches).fderiv_eq

end PlanarMidpoint
