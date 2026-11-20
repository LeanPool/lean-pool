/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryLocalDolbeaultBoundaryIteration.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultBoundary

/-!
# Correspondence auxiliary local Dolbeault boundary iteration

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `smoothDolbeaultPrimitive_solves_and_residual`.
-/

@[expose] public section
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section

/-- The explicit local smooth homotopy uses only a finite sum of cutoff
Cauchy integrals and derivative-free boundary operators. -/
theorem smoothDolbeaultPrimitive_solves_and_residual {n : ℕ}
    (α : Fin n → Configuration n → ℂ) (hα : ∀ j, ContDiff ℝ ∞ (α j))
    (W V : Fin n → Set ℂ) (hW : ∀ j, IsOpen (W j)) (hV : ∀ j, IsOpen (V j))
    (hclosed : ∀ j k p, p ∈ dolbeaultCylinder W Finset.univ →
      dbarComponent (α j) k p = dbarComponent (α k) j p)
    (χ : Fin n → ℂ → ℂ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j))
    (hc : ∀ j, HasCompactSupport (χ j)) (hχone : ∀ j z, z ∈ V j → χ j z = 1)
    (hχW : ∀ j, tsupport (χ j) ⊆ W j) (l : List (Fin n)) (hl : l.Nodup) :
    ∀ p ∈ dolbeaultCylinder W Finset.univ ∩ dolbeaultCylinder V l.toFinset,
      (∀ k ∈ l, dbarComponent (smoothDolbeaultPrimitive χ α l) k p = α k p) ∧
      (∀ k ∉ l, α k p - dbarComponent (smoothDolbeaultPrimitive χ α l) k p =
        smoothDolbeaultBoundaryComposition χ l (α k) p) := by
  induction l with
  | nil =>
    intro p hp
    constructor
    · simp
    · intro k hk
      simp [smoothDolbeaultPrimitive, smoothDolbeaultBoundaryComposition, dbarComponent]
  | cons j l ih =>
    obtain ⟨hjl, hln⟩ := List.nodup_cons.mp hl
    have ih' := ih hln
    let u := smoothDolbeaultPrimitive χ α l
    have hu : ContDiff ℝ ∞ u := smoothDolbeaultPrimitive_contDiff χ hχ hc α hα l
    let β : Fin n → Configuration n → ℂ := fun k => α k - fun p => dbarComponent u k p
    have hβ (k : Fin n) : ContDiff ℝ ∞ (β k) :=
      (hα k).sub (smooth_dbarComponent_contDiff u hu k)
    have hβclosed (k t : Fin n) (p : Configuration n)
        (hp : p ∈ dolbeaultCylinder W Finset.univ) :
        dbarComponent (β k) t p = dbarComponent (β t) k p := by
      rw [smooth_dbarComponent_sub _ _ (hα k) (smooth_dbarComponent_contDiff u hu k),
        smooth_dbarComponent_sub _ _ (hα t) (smooth_dbarComponent_contDiff u hu t),
        hclosed k t p hp, smooth_dbarComponent_commute u hu k t p]
    have hβrep (p : Configuration n)
        (hp : p ∈ dolbeaultCylinder W Finset.univ ∩ dolbeaultCylinder V l.toFinset)
        (k : Fin n) (hk : k ∉ l) : β k p = smoothDolbeaultBoundaryComposition χ l (α k) p :=
      (ih' p hp).2 k hk
    have hβzero (p : Configuration n)
        (hp : p ∈ dolbeaultCylinder W Finset.univ ∩ dolbeaultCylinder V l.toFinset)
        (k : Fin n) (hk : k ∈ l) : β k p = 0 := by
      change α k p - dbarComponent u k p = 0
      rw [(ih' p hp).1 k hk, sub_self]
    let v := configurationCauchyGreenPotential j (χ j)
      (smoothDolbeaultBoundaryComposition χ l (α j))
    let vβ := configurationCauchyGreenPotential j (χ j) (β j)
    have hv : ContDiff ℝ ∞ v := configurationCauchyGreenPotential_contDiff j _ _
      (hχ j) (hc j) (smoothDolbeaultBoundaryComposition_contDiff χ hχ hc l _ (hα j))
    have hjfs : j ∉ l.toFinset := by simpa using hjl
    have hmatch (q : Configuration n)
        (hq : q ∈ dolbeaultCylinder W Finset.univ ∩ dolbeaultCylinder V l.toFinset) : v q = vβ q :=
            by
      apply (configurationCauchyGreenPotential_congr_on_support j (χ j) (β j) _ q ?_).symm
      intro z hz
      exact hβrep _ (dolbeaultCylinder_replace W V l.toFinset j hjfs q hq z (hχW j hz)) j hjl
    intro p hp
    have hps : p ∈ dolbeaultCylinder W Finset.univ ∩ dolbeaultCylinder V l.toFinset := by
      refine ⟨hp.1,?_⟩
      intro k hk
      exact hp.2 k (by simpa using List.mem_cons_of_mem j (List.mem_toFinset.mp hk))
    have he : v =ᶠ[𝓝 p] vβ := by
      filter_upwards [((dolbeaultCylinder_isOpen W hW Finset.univ).inter
        (dolbeaultCylinder_isOpen V hV l.toFinset)).mem_nhds hps] with q hq
      exact hmatch q hq
    have hdmatch (k : Fin n) : dbarComponent v k p = dbarComponent vβ k p :=
      finiteComplexDbar_congr_of_eventuallyEq he
    have hpj : p j ∈ V j := hp.2 j (by simp)
    have hχp := hχone j (p j) hpj
    constructor
    · intro k hk
      change dbarComponent (u+v) k p = _
      rw [smooth_dbarComponent_add u v hu hv, hdmatch]
      rcases List.mem_cons.mp hk with hkj | hkl
      · subst k
        have hd := configurationCauchyGreenPotential_solves j (χ j) (β j)
          (hχ j) (hc j) (hβ j) p
        rw [hχp, one_mul] at hd
        rw [hd]
        change dbarComponent u j p + (α j p - dbarComponent u j p) = α j p
        ring
      · have hkj : k ≠ j := by intro he; subst k; exact hjl hkl
        have hCR (z : ℂ) (hz : z ∈ tsupport (χ j)) :
            dbarComponent (β j) k (dolbeaultReplaceCoordinate j (p, z)) = 0 := by
          have hq := dolbeaultCylinder_replace W V l.toFinset j hjfs p hps z (hχW j hz)
          rw [hβclosed j k _ hq.1]
          have hzβ : β k =ᶠ[𝓝 (dolbeaultReplaceCoordinate j (p, z))] (fun _ => 0) := by
            filter_upwards [((dolbeaultCylinder_isOpen W hW Finset.univ).inter
              (dolbeaultCylinder_isOpen V hV l.toFinset)).mem_nhds hq] with q hqq
            exact hβzero q hqq k hkl
          exact dbarComponent_zero_of_eventuallyZero hzβ j
        have hzv := configurationCauchyGreenPotential_preserves_CR_on_support j k hkj
          (χ j) (β j) (hχ j) (hc j) (hβ j) p hCR
        rw [hzv, add_zero, (ih' p hps).1 k hkl]
    · intro k hk
      have hkj : k ≠ j := fun h => hk (by simp [h])
      have hkl : k ∉ l := fun h => hk (List.mem_cons_of_mem j h)
      have hd := configurationCauchyGreen_cutoff_residual j k hkj (χ j) (β j) (β k)
        (hχ j) (hc j) (hβ j) (hβ k) p (fun z hz =>
          hβclosed j k _ (dolbeaultCylinder_replace W V l.toFinset j hjfs p hps z (hχW j hz)).1)
      change dbarComponent vβ k p = χ j (p j) * β k p -
        configurationCauchyGreenBoundary j (χ j) (β k) p at hd
      have hbmatch : configurationCauchyGreenBoundary j (χ j) (β k) p =
          configurationCauchyGreenBoundary j (χ j)
            (smoothDolbeaultBoundaryComposition χ l (α k)) p := by
        apply configurationCauchyGreenPotential_congr_on_support
        intro z hz
        exact hβrep _ (dolbeaultCylinder_replace W V l.toFinset j hjfs p hps z
          (hχW j (planarDbar_tsupport_subset _ hz))) k hkl
      change α k p - dbarComponent (u+v) k p = _
      rw [smooth_dbarComponent_add u v hu hv, hdmatch, hd, hχp, one_mul, hbmatch]
      simp only [β, Pi.sub_apply, smoothDolbeaultBoundaryComposition]
      ring

end
end GinibrePoincare
