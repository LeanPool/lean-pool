/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Integrability
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.Distribution.Support

/-!
# The causal heat kernel as a distribution

External Input `ext:heat-kernel` of `paper/ckn.tex` states that
`W₊(t,x) = 1_{t>0}(4πt)^{-3/2}e^{-|x|²/(4t)}` is locally integrable on
`ℝ³ × ℝ`, is supported in `{t ≥ 0}`, and satisfies `(∂_t - Δ)W₊ = δ_{(0,0)}`
in `𝒟'(ℝ³ × ℝ)`.  Writing that identity requires a distribution carrier for
`W₊`.  This file supplies it: the established local integrability of
`heatKernelPlus`, stated for the ordinary product topology on `Vec3 × ℝ` rather
than the parabolic one, the induced distribution, its action on every test
function, and its causal support.

The fundamental-solution identity itself is the content of the external input
and is not proved here.
-/

public section

open scoped BigOperators Distributions
open Set MeasureTheory

noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

/-- `heatKernelPlus` is locally integrable for the ordinary product topology on
`Vec3 × ℝ`.  The established statement is for the parabolic topology on
`ParabolicPoint`; the two topologies agree, and a distribution on `Vec3 × ℝ`
needs the product form. -/
theorem heatKernelPlus_locallyIntegrable_prod_volume :
    LocallyIntegrable (fun z : Vec3 × ℝ => heatKernelPlus z) volume := by
  intro z
  obtain ⟨U, hU, hint⟩ :=
    heatKernelPlus_locallyIntegrable (parabolicHomeomorph.symm z)
  refine ⟨parabolicHomeomorph '' U, ?_, ?_⟩
  · have h : parabolicHomeomorph '' U ∈
        Filter.map (⇑parabolicHomeomorph) (nhds (parabolicHomeomorph.symm z)) :=
      Filter.image_mem_map hU
    rwa [parabolicHomeomorph.map_nhds_eq, parabolicHomeomorph.apply_symm_apply] at h
  · have himg : parabolicHomeomorph '' U = U := by
      ext w
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact hp
      · intro hw
        exact ⟨w, hw, rfl⟩
    rw [himg]
    exact hint


/-- The causal heat kernel `W₊` of External Input `ext:heat-kernel`, read as a
distribution on all of `ℝ³ × ℝ`. -/
@[expose]
def heatKernelPlusDistribution :
    𝓓'((⊤ : TopologicalSpace.Opens (Vec3 × ℝ)), ℝ) :=
  Distribution.ofFun ⊤ (fun z : Vec3 × ℝ => heatKernelPlus z) volume ⊤

/-- The distribution of `W₊` acts on every test function by integration against
`W₊`; in particular it is not the zero map of the non-integrable branch. -/
theorem heatKernelPlusDistribution_apply
    (ψ : 𝓓((⊤ : TopologicalSpace.Opens (Vec3 × ℝ)), ℝ)) :
    heatKernelPlusDistribution ψ = ∫ z : Vec3 × ℝ, ψ z • heatKernelPlus z := by
  refine Distribution.ofFun_apply ?_
  exact heatKernelPlus_locallyIntegrable_prod_volume.locallyIntegrableOn _

/-- The distributional support of `W₊` lies in the closed half space `{t ≥ 0}`,
the causality clause of External Input `ext:heat-kernel`. -/
theorem heatKernelPlusDistribution_dsupport_subset :
    Distribution.dsupport heatKernelPlusDistribution ⊆ {z : Vec3 × ℝ | 0 ≤ z.2} := by
  apply Set.sInter_subset_of_mem
  refine ⟨?_, ?_⟩
  · intro ψ hψ
    rw [heatKernelPlusDistribution_apply]
    have hfun : (fun z : Vec3 × ℝ => ψ z • heatKernelPlus z) = fun _ => (0 : ℝ) := by
      funext z
      by_cases hz : (0 : ℝ) ≤ z.2
      · have hnot : z ∉ tsupport ψ := fun hmem => (hψ hmem) hz
        rw [image_eq_zero_of_notMem_tsupport hnot, zero_smul]
      · rw [heatKernelPlus_eq_zero_of_nonpos (le_of_lt (not_le.mp hz)), smul_zero]
    rw [hfun, integral_zero]
  · exact isClosed_le continuous_const continuous_snd

end CKN.Foundation.Heat
