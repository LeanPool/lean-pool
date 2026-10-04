/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Embedding.GagliardoNirenberg


/-!
# Cutting a class off inside a boundary chart

Guo's Theorem III.2.2 finishes by covering the boundary with finitely many chart
neighbourhoods and gluing the local extensions with a partition of unity. Each piece of that
partition is a cutoff supported in one chart's ball, and the piece it cuts out has to reach the
whole region above that chart's graph, where the chart describes the domain only inside the
ball.

That is what this file supplies. A cutoff supported in `W` sends a weak gradient on `B ∩ W` to
a weak gradient on all of `B`, since a test function on `B` multiplied by the cutoff is a test
function on `B ∩ W`, and every integrand the identity names vanishes off `W` along with the
cutoff. `hasWeakGradOn_univ_mul_cutoff` is the case `W ⊆ B`, where the conclusion reaches the
whole space; here the cutoff straddles the boundary of `B`, which is what a boundary chart
does.

## Main declarations

* `EllipticPdes.Extension.integrableOn_of_vanishing_off`: integrability spreads from the part
  of a set inside a neighbourhood when the class vanishes outside it.
* `EllipticPdes.Extension.hasWeakGradOn_mul_cutoff_inter`: the weak gradient of a class cut off
  inside a neighbourhood, on the surrounding set.

## References

James Guo, *Partial Differential Equations* (Course Lecture Notes), Theorem III.2.2
(p. 20), proof step 3 (p. 21); L. C. Evans, *Partial Differential Equations* (2nd ed.),
§5.4 Theorem 1 (p. 253).
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Embedding (HasWeakGradOn partialD_mul integrableOn_mul_bounded)
open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- **Integrability from a neighbourhood the class vanishes outside.** A class integrable on the
part of a set inside `W` and vanishing off `W` is integrable on the whole set, the rest of it
contributing nothing. -/
theorem integrableOn_of_vanishing_off {B W : Set (EuclideanSpace ℝ (Fin d))}
    (hB : MeasurableSet B) (hW : MeasurableSet W) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : IntegrableOn f (B ∩ W) volume) (hoff : ∀ x, x ∉ W → f x = 0) :
    IntegrableOn f B volume := by
  have hdiff : IntegrableOn f (B \ W) volume := by
    refine (integrableOn_zero (μ := volume) (s := B \ W)).congr_fun ?_ (hB.diff hW)
    intro x hx
    exact (hoff x hx.2).symm
  exact Set.inter_union_sdiff B W ▸ hf.union hdiff

/-- **Weak gradient of a class cut off inside a neighbourhood.** If `u` has weak gradient `g` on
`B ∩ W` and `η` is smooth with `tsupport η ⊆ W`, then `η u` has weak gradient
`η gₖ + u ∂ₖη` on all of `B`. Testing against `φ` reduces to testing the hypothesis against
`η φ`, whose support sits inside `B ∩ W`, and both sides of the identity see only `W`, the
cutoff and its derivative vanishing off it. -/
theorem hasWeakGradOn_mul_cutoff_inter {B W : Set (EuclideanSpace ℝ (Fin d))}
    (hB : MeasurableSet B) {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hηc : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : tsupport η ⊆ W)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u (B ∩ W) volume) (hgi : ∀ k, IntegrableOn (g k) (B ∩ W) volume)
    (h : HasWeakGradOn (B ∩ W) u g) :
    HasWeakGradOn B (fun x => η x * u x)
      (fun k x => η x * g k x + partialD k η x * u x) := by
  intro φ hφc hφcs hφs k
  have hηd : Differentiable ℝ η := hηc.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφc.differentiable (by simp)
  have hηcont : Continuous η := hηc.continuous
  have hφcont : Continuous φ := hφc.continuous
  have hηpc : Continuous (partialD k η) :=
    (hηc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφpc : Continuous (partialD k φ) :=
    (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφpcs : HasCompactSupport (partialD k φ) :=
    hφcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  -- the cutoff and its derivative vanish off the neighbourhood
  have hoff : ∀ x, x ∉ W → η x = 0 ∧ partialD k η x = 0 := by
    intro x hx
    have hxs : x ∉ tsupport η := fun hc => hx (hηs hc)
    refine ⟨image_eq_zero_of_notMem_tsupport hxs, ?_⟩
    have hev : η =ᶠ[nhds x] fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hxs] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    rw [partialD, hev.fderiv_eq]
    simp
  -- the test function, pushed inside the neighbourhood
  have hψc : ContDiff ℝ (⊤ : ℕ∞) fun x => η x * φ x := hηc.mul hφc
  have hψcs : HasCompactSupport fun x => η x * φ x := hφcs.mul_left
  have hψs : tsupport (fun x => η x * φ x) ⊆ B ∩ W := by
    have hsupp : Function.support (fun x => η x * φ x)
        ⊆ Function.support η ∩ Function.support φ := by
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      constructor <;> intro hc <;> apply hx
      · rw [hc, zero_mul]
      · rw [hc, mul_zero]
    have hcl := (closure_mono hsupp).trans (closure_inter_subset_inter_closure _ _)
    exact fun x hx => ⟨hφs (hcl hx).2, hηs (hcl hx).1⟩
  have key := h _ hψc hψcs hψs k
  -- bounds and integrability of the pieces, each with a compactly supported factor
  have hbound : ∀ a b : EuclideanSpace ℝ (Fin d) → ℝ, Continuous a → Continuous b →
      HasCompactSupport b → ∃ C : ℝ, ∀ x, ‖a x * b x‖ ≤ C := by
    intro a b ha hb hbcs
    exact (hbcs.mul_left (f := a)).exists_bound_of_continuous (ha.mul hb)
  obtain ⟨C1, hC1⟩ := hbound η (partialD k φ) hηcont hφpc hφpcs
  obtain ⟨C2, hC2⟩ := hbound (partialD k η) φ hηpc hφcont hφcs
  obtain ⟨C3, hC3⟩ := hbound η φ hηcont hφcont hφcs
  have hi1 : IntegrableOn (fun x => u x * (η x * partialD k φ x)) (B ∩ W) volume :=
    integrableOn_mul_bounded hu (hηcont.mul hφpc) hC1
  have hi2 : IntegrableOn (fun x => u x * (partialD k η x * φ x)) (B ∩ W) volume :=
    integrableOn_mul_bounded hu (hηpc.mul hφcont) hC2
  have hi3 : IntegrableOn (fun x => g k x * (η x * φ x)) (B ∩ W) volume :=
    integrableOn_mul_bounded (hgi k) (hηcont.mul hφcont) hC3
  -- the product rule inside the test function, and the split it licenses
  have hsplit : ∫ x in B ∩ W, u x * partialD k (fun y => η y * φ y) x
      = (∫ x in B ∩ W, u x * (partialD k η x * φ x))
        + ∫ x in B ∩ W, u x * (η x * partialD k φ x) := by
    rw [← integral_add hi2 hi1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [partialD_mul k (hηd x) (hφd x)]
    ring
  rw [hsplit] at key
  -- both sides of the goal see only the neighbourhood
  have hLrestrict : ∫ x in B, η x * u x * partialD k φ x
      = ∫ x in B ∩ W, η x * u x * partialD k φ x := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hB Set.inter_subset_left ?_
    intro x hx
    rw [(hoff x fun hc => hx.2 ⟨hx.1, hc⟩).1, zero_mul, zero_mul]
  have hRrestrict : ∫ x in B, (η x * g k x + partialD k η x * u x) * φ x
      = ∫ x in B ∩ W, (η x * g k x + partialD k η x * u x) * φ x := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hB Set.inter_subset_left ?_
    intro x hx
    obtain ⟨h1, h2⟩ := hoff x fun hc => hx.2 ⟨hx.1, hc⟩
    rw [h1, h2, zero_mul, zero_mul, add_zero, zero_mul]
  have hgoalL : ∫ x in B ∩ W, η x * u x * partialD k φ x
      = ∫ x in B ∩ W, u x * (η x * partialD k φ x) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hgoalR : ∫ x in B ∩ W, (η x * g k x + partialD k η x * u x) * φ x
      = (∫ x in B ∩ W, g k x * (η x * φ x))
        + ∫ x in B ∩ W, u x * (partialD k η x * φ x) := by
    rw [← integral_add hi3 hi2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [hLrestrict, hRrestrict, hgoalL, hgoalR]
  linarith [key]

end EllipticPdes.Extension
