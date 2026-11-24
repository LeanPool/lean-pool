/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ComplexAnalyticSubvarieties
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Topology of complex analytic subsets

Source: the standard facts about analytic sets used in Copy-4, `sec:gluing`
(`transcendental-nakamaye-copy4-20260911`): "a connected complex manifold is
irreducible"; Grauert--Remmert, *Coherent analytic sheaves*, Ch. 5 and 9;
blueprint `ana:irreducible-components`.

* `eqOn_zero_of_isOpen_convex`: the identity theorem for a holomorphic function
  on an open convex subset of a complex normed space, proved by restricting to
  complex lines and applying the one-variable identity theorem.
* `IsComplexAnalyticSubset.isClosed`: an analytic subset is closed.
* `IsComplexAnalyticSubset.isClosed_interior`: the interior of an analytic subset
  is closed.  At a point of the closure of the interior, the local generators
  vanish on a nonempty open subset of a coordinate ball, hence on the whole ball.
* `isComplexAnalyticallyIrreducible_univ_of_connectedSpace`: a connected complex
  manifold is analytically irreducible.  An analytic subset with nonempty
  interior is clopen-interior, hence everything; two closed sets with empty
  interior cannot cover the manifold.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

/-- **Identity theorem on a convex open set.** A holomorphic function on an
open convex set `W` which vanishes on a nonempty open subset of `W` vanishes on
all of `W`. -/
theorem eqOn_zero_of_isOpen_convex {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {W U : Set E} {f : E → ℂ} (hW : IsOpen W)
    (hWc : Convex ℝ W) (hf : DifferentiableOn ℂ f W) (hU : IsOpen U)
    (hUW : U ⊆ W) (hUne : U.Nonempty) (hfU : EqOn f 0 U) : EqOn f 0 W := by
  obtain ⟨u, hu⟩ := hUne
  intro z hz
  let L : ℂ → E := fun t => u + t • (z - u)
  have hLc : Continuous L := by fun_prop
  have hLd : Differentiable ℂ L := by fun_prop
  let D : Set ℂ := L ⁻¹' W
  have hD : IsOpen D := hW.preimage hLc
  have hDc : Convex ℝ D := by
    intro t ht s hs a b ha hb hab
    have h := hWc ht hs ha hb hab
    simp only [D, L, mem_preimage] at h ⊢
    convert h using 1
    obtain rfl : b = 1 - a := by linarith
    simp only [← Complex.coe_smul]
    push_cast
    module
  have hg : DifferentiableOn ℂ (f ∘ L) D :=
    hf.comp hLd.differentiableOn fun t ht => ht
  have h0 : (0 : ℂ) ∈ D := by simpa [D, L] using hUW hu
  have h1 : (1 : ℂ) ∈ D := by simpa [D, L] using hz
  have hev : f ∘ L =ᶠ[𝓝 0] 0 := by
    have hLU : ∀ᶠ t in 𝓝 (0 : ℂ), L t ∈ U :=
      hLc.continuousAt.preimage_mem_nhds (by simpa [L] using hU.mem_nhds hu)
    filter_upwards [hLU] with t ht
    exact hfU ht
  have := (DifferentiableOn.analyticOnNhd hg hD).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hDc.isPreconnected h0 hev h1
  simpa [L] using this

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- An analytic subset is closed. -/
theorem IsComplexAnalyticSubset.isClosed {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) : IsClosed A := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨p⟩ := hA x
  have hxs := mem_complexChartAt_source (n := n) x
  obtain ⟨i, hi⟩ : ∃ i, p.generator i ((complexChartAt (n := n) x).val x) ≠ 0 := by
    by_contra! h
    exact hx ((p.zeroLocus hxs p.center_mem_coordinateNeighborhood).mpr h)
  have hS : (complexChartAt (n := n) x).val.source ∩
      (complexChartAt (n := n) x).val ⁻¹' p.coordinateNeighborhood ∈ 𝓝 x :=
    ((complexChartAt (n := n) x).val.continuousOn.isOpen_inter_preimage
      (complexChartAt (n := n) x).val.open_source p.isOpen_coordinateNeighborhood).mem_nhds
      ⟨hxs, p.center_mem_coordinateNeighborhood⟩
  have hcont : ContinuousAt
      (fun y => p.generator i ((complexChartAt (n := n) x).val y)) x :=
    ((p.generator_holomorphic i).continuousOn.continuousAt
      (p.isOpen_coordinateNeighborhood.mem_nhds p.center_mem_coordinateNeighborhood)).comp
      ((complexChartAt (n := n) x).val.continuousAt hxs)
  filter_upwards [hS, hcont.eventually_ne hi] with y hy hy'
  exact fun hyA => hy' ((p.zeroLocus hy.1 hy.2).mp hyA i)

/-- The interior of an analytic subset is closed. -/
theorem IsComplexAnalyticSubset.isClosed_interior {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) : IsClosed (interior A) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨p⟩ := hA x
  set e := (complexChartAt (n := n) x).val with he
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp p.isOpen_coordinateNeighborhood (e x)
      p.center_mem_coordinateNeighborhood
  set S := e.source ∩ e ⁻¹' ball (e x) r with hSdef
  have hSo : IsOpen S := e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
  have hxS : x ∈ S := ⟨mem_complexChartAt_source (n := n) x, mem_ball_self hr⟩
  obtain ⟨y, hyS, hyint⟩ := mem_closure_iff.mp hx S hSo hxS
  have hUo : IsOpen (e '' (interior A ∩ S)) :=
    e.isOpen_image_of_subset_source (isOpen_interior.inter hSo) fun z hz => hz.2.1
  have hvanish : ∀ i, EqOn (p.generator i) 0 (ball (e x) r) := by
    intro i
    refine eqOn_zero_of_isOpen_convex isOpen_ball (convex_ball _ _)
      ((p.generator_holomorphic i).mono hball) hUo ?_ ⟨e y, y, ⟨hyint, hyS⟩, rfl⟩ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact hz.2.2
    · rintro _ ⟨z, hz, rfl⟩
      exact (p.zeroLocus hz.2.1 (hball hz.2.2)).mp (interior_subset hz.1) i
  have hSA : S ⊆ A := fun z hz =>
    (p.zeroLocus hz.1 (hball hz.2)).mpr fun i => hvanish i hz.2
  exact mem_interior_iff_mem_nhds.mpr (mem_of_superset (hSo.mem_nhds hxS) hSA)

/-- An analytic subset of a connected manifold with nonempty interior is the
whole manifold. -/
theorem IsComplexAnalyticSubset.eq_univ_of_interior_nonempty [ConnectedSpace M]
    {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    (hint : (interior A).Nonempty) : A = univ :=
  eq_univ_of_univ_subset
    ((IsClopen.eq_univ ⟨hA.isClosed_interior, isOpen_interior⟩ hint).symm.subset.trans
      interior_subset)

/-- **A connected complex manifold is analytically irreducible.** -/
theorem isComplexAnalyticallyIrreducible_univ_of_connectedSpace [ConnectedSpace M] :
    IsComplexAnalyticallyIrreducible (n := n) (univ : Set M) := by
  refine ⟨isComplexAnalyticSubset_univ, univ_nonempty, fun B C hB hC _ _ hBC => ?_⟩
  by_cases hBi : (interior B).Nonempty
  · exact Or.inl (hB.eq_univ_of_interior_nonempty hBi).symm
  by_cases hCi : (interior C).Nonempty
  · exact Or.inr (hC.eq_univ_of_interior_nonempty hCi).symm
  exfalso
  rw [not_nonempty_iff_eq_empty] at hBi hCi
  have hBC' := interior_union_isClosed_of_interior_empty hB.isClosed hCi
  rw [← hBC, interior_univ, hBi] at hBC'
  exact univ_nonempty.ne_empty hBC'

end

end SGPT.Foundations.Analysis.FirstPass
