/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryLocalDolbeaultIteration.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultConfiguration

/-!
# Correspondence auxiliary local Dolbeault iteration

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `smoothClosedForm_coordinate_iteration_on_polydisc`.
-/

@[expose] public section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section

theorem smooth_dbarComponent_contDiff {n : ℕ} (f : Configuration n → ℂ)
    (hf : ContDiff ℝ ∞ f) (j : Fin n) : ContDiff ℝ ∞ (fun p => dbarComponent f j p) :=
  finiteComplexDbar_contDiff f hf _ _

theorem smooth_dbarComponent_commute {n : ℕ} (f : Configuration n → ℂ)
    (hf : ContDiff ℝ ∞ f) (j k : Fin n) (p : Configuration n) :
    dbarComponent (fun q => dbarComponent f j q) k p =
      dbarComponent (fun q => dbarComponent f k q) j p :=
  finiteComplexDbar_commute f hf _ _ _ _ p

theorem smooth_dbarComponent_sub {n : ℕ} (f g : Configuration n → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (j : Fin n) (p : Configuration n) :
    dbarComponent (f-g) j p = dbarComponent f j p - dbarComponent g j p :=
  finiteComplexDbar_sub f g (hf.differentiable (by simp)) (hg.differentiable (by simp)) _ _ p

theorem smooth_dbarComponent_add {n : ℕ} (f g : Configuration n → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (j : Fin n) (p : Configuration n) :
    dbarComponent (f+g) j p = dbarComponent f j p + dbarComponent g j p := by
  simp only [dbarComponent, fderiv_add (hf.differentiable (by simp) p)
    (hg.differentiable (by simp) p), add_apply]
  ring

theorem dbarComponent_zero_of_eventuallyZero {n : ℕ} {f : Configuration n → ℂ}
    {p : Configuration n} (hf : f =ᶠ[𝓝 p] (fun _ => 0)) (j : Fin n) :
    dbarComponent f j p = 0 := by
  simp only [dbarComponent, hf.fderiv_eq (𝕜 := ℝ)]
  simp

/-- The cylinder set of configurations `p` with `p j ∈ V j` for every `j ∈ s`. -/
def dolbeaultCylinder {n : ℕ} (V : Fin n → Set ℂ) (s : Finset (Fin n)) : Set (Configuration n) :=
  {p | ∀ j ∈ s, p j ∈ V j}

theorem dolbeaultCylinder_isOpen {n : ℕ} (V : Fin n → Set ℂ)
    (hV : ∀ j, IsOpen (V j)) (s : Finset (Fin n)) : IsOpen (dolbeaultCylinder V s) := by
  have he : dolbeaultCylinder V s = ⋂ j ∈ s, (fun p : Configuration n => p j) ⁻¹' V j := by
    ext p
    simp [dolbeaultCylinder]
  rw [he]
  exact isOpen_biInter_finset (fun j _ => (hV j).preimage (continuous_apply j))

/-- The full smooth coordinate iteration. The source has no growth or
global integrability assumptions. This theorem is an intermediate smooth
case, rather than the locally L² distributional Dolbeault endpoint. -/
theorem smoothClosedForm_coordinate_iteration_on_polydisc {n : ℕ}
    (α : Fin n → Configuration n → ℂ) (hα : ∀ j, ContDiff ℝ ∞ (α j))
    (W : Fin n → Set ℂ) (hW : ∀ j, IsOpen (W j))
    (hclosed : ∀ j k p, p ∈ dolbeaultCylinder W Finset.univ →
      dbarComponent (α j) k p = dbarComponent (α k) j p)
    (V : Fin n → Set ℂ) (hV : ∀ j, IsOpen (V j))
    (χ : Fin n → ℂ → ℂ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j))
    (hc : ∀ j, HasCompactSupport (χ j)) (hχone : ∀ j z, z ∈ V j → χ j z = 1)
    (hχW : ∀ j, tsupport (χ j) ⊆ W j)
    (s : Finset (Fin n)) :
    ∃ u : Configuration n → ℂ, ContDiff ℝ ∞ u ∧
      ∀ p ∈ dolbeaultCylinder W Finset.univ ∩ dolbeaultCylinder V s,
        ∀ j ∈ s, dbarComponent u j p = α j p := by
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨fun _ => 0, contDiff_const, fun _ _ _ h => False.elim (Finset.notMem_empty _ h)⟩
  | @insert j s hjs ih =>
    obtain ⟨u, hu, hsol⟩ := ih
    let β : Fin n → Configuration n → ℂ := fun k => α k - fun p => dbarComponent u k p
    have hβ (k : Fin n) : ContDiff ℝ ∞ (β k) :=
      (hα k).sub (smooth_dbarComponent_contDiff u hu k)
    have hβclosed (k l : Fin n) (p : Configuration n)
        (hp : p ∈ dolbeaultCylinder W Finset.univ) :
        dbarComponent (β k) l p = dbarComponent (β l) k p := by
      rw [smooth_dbarComponent_sub _ _ (hα k) (smooth_dbarComponent_contDiff u hu k),
        smooth_dbarComponent_sub _ _ (hα l) (smooth_dbarComponent_contDiff u hu l),
        hclosed k l p hp, smooth_dbarComponent_commute u hu k l p]
    have hβzero (p : Configuration n)
        (hp : p ∈ dolbeaultCylinder W Finset.univ ∩ dolbeaultCylinder V s)
        (k : Fin n) (hks : k ∈ s) : β k p = 0 := by
      simp only [β, Pi.sub_apply]
      rw [hsol p hp k hks, sub_self]
    let v := configurationCauchyGreenPotential j (χ j) (β j)
    have hv : ContDiff ℝ ∞ v := configurationCauchyGreenPotential_contDiff j _ _
      (hχ j) (hc j) (hβ j)
    refine ⟨u+v, hu.add hv,?_⟩
    intro p hp k hk
    have hps : p ∈ dolbeaultCylinder W Finset.univ ∩ dolbeaultCylinder V s :=
      ⟨hp.1, fun l hl => hp.2 l (Finset.mem_insert_of_mem hl)⟩
    rw [smooth_dbarComponent_add u v hu hv]
    rcases Finset.mem_insert.mp hk with hkj | hks
    · subst k
      have hj := configurationCauchyGreenPotential_solves j (χ j) (β j) (hχ j) (hc j) (hβ j) p
      have hχp := hχone j (p j) (hp.2 j (Finset.mem_insert_self j s))
      rw [hχp, one_mul] at hj
      change dbarComponent u j p + dbarComponent v j p = α j p
      rw [hj]
      simp only [β, Pi.sub_apply]
      ring
    · have hkj : k ≠ j := by intro he; subst k; exact hjs hks
      have hCR (z : ℂ) (hz : z ∈ tsupport (χ j)) :
          dbarComponent (β j) k (dolbeaultReplaceCoordinate j (p, z)) = 0 := by
        let q := dolbeaultReplaceCoordinate j (p, z)
        have hq : q ∈ dolbeaultCylinder W Finset.univ ∩ dolbeaultCylinder V s := by
          constructor
          · intro l _
            by_cases hlj : l = j
            · subst l
              simpa [q, dolbeaultReplaceCoordinate_apply] using hχW j hz
            · simpa only [q, dolbeaultReplaceCoordinate_apply, ite_eq_right hlj] using
                hps.1 l (Finset.mem_univ l)
          · intro l hl
            have hlj : l ≠ j := by intro he; subst l; exact hjs hl
            simpa only [q, dolbeaultReplaceCoordinate_apply, ite_eq_right hlj] using hps.2 l hl
        have he : β k =ᶠ[𝓝 q] (fun _ => 0) := by
          filter_upwards [((dolbeaultCylinder_isOpen W hW Finset.univ).inter
            (dolbeaultCylinder_isOpen V hV s)).mem_nhds hq] with r hr
          exact hβzero r hr k hks
        rw [hβclosed j k q hq.1]
        exact dbarComponent_zero_of_eventuallyZero he j
      have hzero := configurationCauchyGreenPotential_preserves_CR_on_support j k hkj (χ j) (β j)
        (hχ j) (hc j) (hβ j) p hCR
      change dbarComponent u k p + dbarComponent v k p = α k p
      rw [hzero, add_zero, hsol p hps k hks]

end
end GinibrePoincare
