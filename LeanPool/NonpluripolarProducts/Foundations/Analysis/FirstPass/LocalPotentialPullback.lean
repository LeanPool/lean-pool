/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.FormPullback
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HolomorphicDDC

/-!
# Pullback of actual smooth local potentials

The source domain records both chart conditions and the inverse image of the
target potential domain. The full two-form identity follows from normalized
ddC naturality and the constructed smooth-form pullback. No local dd-bar
existence theorem or positivity assumption is required.
-/

@[expose] public section

open Set
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback

open HolomorphicMaps

noncomputable section

variable {k n : ℕ} {V M : Type*}
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual open inverse image of a target potential domain in a chart pair. -/
def potentialDomain (f : V → M) (e : ComplexChart k V) (d : ComplexChart n M)
    (W : Set (ComplexModel n)) : Set (ComplexModel k) :=
  coordinateDomain f e d ∩ coordinateMap f e d ⁻¹' W

theorem potentialDomain_isOpen {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (e : ComplexChart k V) (d : ComplexChart n M)
    {W : Set (ComplexModel n)} (hW : IsOpen W) :
    IsOpen (potentialDomain f e d W) :=
  (coordinateMap_contDiffOn hf e d).continuousOn.isOpen_inter_preimage
    (coordinateDomain_isOpen hf e d) hW

theorem isSmoothLocalPotential_pullback {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    {θ : SmoothRealForm n M 2} (e : ComplexChart k V) {d : ComplexChart n M}
    {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ d W ρ) :
    IsSmoothLocalPotential (SmoothRealForm.pullback hf θ) e
      (potentialDomain f e d W) (ρ ∘ coordinateMap f e d) := by
  refine ⟨potentialDomain_isOpen hf e d hρ.1, fun _ hz => hz.1.1,
    hρ.2.2.1.comp_inter (coordinateMap_contDiffOn_real hf e d), ?_⟩
  intro z hz
  change smoothDDC (fun y => ρ (coordinateMap f e d y)) z = _
  rw [HolomorphicDDC.smoothDDC_comp (potentialDomain_isOpen hf e d hρ.1) hρ.1
    ((coordinateMap_contDiffOn hf e d).mono inter_subset_left) hρ.2.2.1
    (fun _ hy => hy.2) hz,
    hρ.2.2.2 hz.2, SmoothRealForm.pullback_coeff hf θ e d hz.1]

/-- Existing local potentials pull back at every point. This does not assert
that an arbitrary smooth form has local potentials. -/
theorem hasSmoothLocalPotentials_pullback {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    {θ : SmoothRealForm n M 2} (hθ : HasSmoothLocalPotentials θ) :
    HasSmoothLocalPotentials (SmoothRealForm.pullback hf θ) := by
  intro e z hz
  let d := complexChartAt (n := n) (f (e.val.symm z))
  have hzd : z ∈ coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
  obtain ⟨W, ρ, hzW, hρ⟩ :=
    hθ d (coordinateMap f e d z) (coordinateMap_mem_target hzd)
  exact ⟨potentialDomain f e d W, ρ ∘ coordinateMap f e d,
    ⟨hzd, hzW⟩, isSmoothLocalPotential_pullback hf e hρ⟩

end

end SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback
