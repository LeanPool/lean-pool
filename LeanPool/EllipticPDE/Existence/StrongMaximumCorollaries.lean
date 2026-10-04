/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Existence.StrongMaximum


/-!
# Corollaries of Hopf's lemma and the strong maximum principle

The free-sign clauses of Hopf's lemma and of the strong maximum principle, in which the
zeroth-order coefficient has any sign and the extremal value is zero, follow from the
nonnegative clauses by replacing `c` with its positive part: on the set where the function is
nonpositive the change of coefficient lowers the operator. The avoidance principle, the
tangency corollary at a boundary point with an interior sphere, and uniqueness for the
Neumann problem up to a constant then follow.

## Main declarations

* `EllipticPdes.Classical.hopf_lemma_of_zero`: Hopf's lemma with `c` of any sign and
  `u x₀ = 0`.
* `EllipticPdes.Classical.strong_maximum_principle_of_zero`: the strong principle at a zero
  maximum with `c` of any sign.
* `EllipticPdes.Classical.avoidance_principle`: two ordered functions with ordered images
  either agree or are strictly ordered.
* `EllipticPdes.Classical.eq_of_eq_of_fderiv_eq`: tangency at a boundary point with an
  interior sphere forces equality.
* `EllipticPdes.Classical.neumann_unique`: uniqueness up to a constant for the Neumann problem.

## Operator convention

The non-divergence operator here is `L u = -∑ aᵢⱼ ∂ᵢⱼu + ∑ bᵢ ∂ᵢu + c u`.
All Guo results cited in this file are translated by negating the source operator:
Guo's operator is `-L`, with coefficients `a`, `-b`, `-c`. Thus his subsolution inequality
`(-L) u ≥ 0` becomes `L u ≤ 0`, and his potential condition `-c ≤ 0` becomes `c ≥ 0`.

## References

James Guo, *Partial Differential Equations* (Course Lecture Notes), Lemma XI.4.3,
Theorem XI.4.5, Corollaries XI.4.6, XI.4.7 and XI.4.8 (pp. 100–103).
-/

@[expose] public section

open Set Filter Topology Metric

noncomputable section

namespace EllipticPdes.Classical

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- The operator with the positive part of the zeroth-order coefficient is at most the operator
with the coefficient itself, on a nonpositive function. -/
theorem nondivOp_posPart_le (a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ) (c : EuclideanSpace ℝ (Fin d) → ℝ)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {x : EuclideanSpace ℝ (Fin d)} (hux : u x ≤ 0) :
    nondivOp a b (fun y => max (c y) 0) u x ≤ nondivOp a b c u x := by
  rw [nondivOp_congr_zeroth a b c (fun y => max (c y) 0) u x]
  have h1 : 0 ≤ max (c x) 0 - c x := by
    have := le_max_left (c x) 0
    linarith
  nlinarith [mul_nonneg h1 (neg_nonneg.mpr hux)]

/-- **Hopf's lemma at a zero boundary value** (Guo Lemma XI.4.3(iii)). With the zeroth-order
coefficient bounded in absolute value and of any sign, a subsolution strictly negative on the
ball, vanishing at a point `x₀` of the sphere and differentiable there, has positive derivative
at `x₀` in the outward radial direction. -/
theorem hopf_lemma_of_zero (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {θ A B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ U, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    {c : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ} (hc : ∀ x ∈ U, |c x| ≤ C)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsub : ∀ x ∈ U, nondivOp a b c u x ≤ 0)
    {x₀ y : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hr : 0 < r) (hball : ball y r ⊆ U)
    (hx₀ : dist x₀ y = r) (hlt : ∀ x ∈ U, u x < u x₀) (hu0 : u x₀ = 0)
    (hdiff : DifferentiableAt ℝ u x₀) :
    0 < fderiv ℝ u x₀ (x₀ - y) :=
  hopf_lemma hd hθ hsymm hell ha hb (c := fun x => max (c x) 0) (C := C)
    (fun x _ => le_max_right _ _)
    (fun x hx => max_le ((le_abs_self _).trans (hc x hx)) ((abs_nonneg _).trans (hc x hx)))
    hu huc
    (fun x hx => (nondivOp_posPart_le a b c (by linarith [hlt x hx])).trans (hsub x hx))
    hr hball hx₀ hlt (fun x _ => by rw [hu0, mul_zero]) hdiff

/-- **Strong maximum principle at a zero maximum** (Guo Theorem XI.4.5(iii)). With the
zeroth-order coefficient bounded in absolute value and of any sign, a subsolution on a connected
open set that attains the maximum zero at an interior point vanishes on the set. -/
theorem strong_maximum_principle_of_zero (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {θ A B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ U, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    {c : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ} (hc : ∀ x ∈ U, |c x| ≤ C)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hsub : ∀ x ∈ U, nondivOp a b c u x ≤ 0)
    {x₀ : EuclideanSpace ℝ (Fin d)} (hx₀ : x₀ ∈ U) (hmax : ∀ x ∈ U, u x ≤ u x₀)
    (hu0 : u x₀ = 0) : ∀ x ∈ U, u x = u x₀ :=
  strong_maximum_principle hd hU hUc hθ hsymm hell ha hb (c := fun x => max (c x) 0) (C := C)
    (fun x _ => le_max_right _ _)
    (fun x hx => max_le ((le_abs_self _).trans (hc x hx)) ((abs_nonneg _).trans (hc x hx)))
    hu (fun x hx => (nondivOp_posPart_le a b c (by linarith [hmax x hx])).trans (hsub x hx))
    hx₀ hmax (fun x _ => by rw [hu0, mul_zero])

/-- **Avoidance principle** (Guo Corollary XI.4.6). On a connected open set, with the
zeroth-order coefficient bounded in absolute value, two functions with `L u ≤ L v` and `u ≤ v`
either agree everywhere or satisfy `u < v` everywhere. -/
theorem avoidance_principle (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {θ A B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ U, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    {c : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ} (hc : ∀ x ∈ U, |c x| ≤ C)
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (hL : ∀ x ∈ U, nondivOp a b c u x ≤ nondivOp a b c v x) (hle : ∀ x ∈ U, u x ≤ v x) :
    (∀ x ∈ U, u x = v x) ∨ (∀ x ∈ U, u x < v x) := by
  by_cases h : ∃ x₀ ∈ U, u x₀ = v x₀
  · obtain ⟨x₀, hx₀, hx₀eq⟩ := h
    left
    have hw : ∀ x ∈ U, nondivOp a b c (fun y => u y - v y) x ≤ 0 := fun x hx => by
      rw [nondivOp_sub hU hu hv a b c hx]
      linarith [hL x hx]
    have hmax : ∀ x ∈ U, (fun y => u y - v y) x ≤ (fun y => u y - v y) x₀ := fun x hx => by
      linarith [hle x hx]
    have hcst := strong_maximum_principle_of_zero hd hU hUc hθ hsymm hell ha hb hc (hu.sub hv)
      hw hx₀ hmax (by linarith)
    intro x hx
    have := hcst x hx
    linarith
  · right
    intro x hx
    rcases lt_or_eq_of_le (hle x hx) with h1 | h1
    · exact h1
    · exact absurd ⟨x, hx, h1⟩ h

/-- **Tangency at a boundary point forces equality** (Guo Corollary XI.4.7, with the interior
sphere condition at the point in place of a `C²` boundary). On a connected open set, two
functions with `L u ≤ L v`, `u ≤ v` on the set, equal with equal derivatives at a point `x₀`
of the frontier that is on the sphere of a ball inside the set, agree on the set. -/
theorem eq_of_eq_of_fderiv_eq (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {θ A B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ U, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    {c : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ} (hc : ∀ x ∈ U, |c x| ≤ C)
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hL : ∀ x ∈ U, nondivOp a b c u x ≤ nondivOp a b c v x) (hle : ∀ x ∈ U, u x ≤ v x)
    {x₀ y : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hr : 0 < r) (hball : ball y r ⊆ U)
    (hx₀ : dist x₀ y = r) (heq : u x₀ = v x₀) (hfd : fderiv ℝ u x₀ = fderiv ℝ v x₀)
    (hud : DifferentiableAt ℝ u x₀) (hvd : DifferentiableAt ℝ v x₀) :
    ∀ x ∈ U, u x = v x := by
  rcases avoidance_principle hd hU hUc hθ hsymm hell ha hb hc hu hv hL hle with h | h
  · exact h
  · exfalso
    have hw : ∀ x ∈ U, nondivOp a b c (fun y => u y - v y) x ≤ 0 := fun x hx => by
      rw [nondivOp_sub hU hu hv a b c hx]
      linarith [hL x hx]
    have hlt : ∀ x ∈ U, (fun y => u y - v y) x < (fun y => u y - v y) x₀ := fun x hx => by
      linarith [h x hx]
    have hwd : DifferentiableAt ℝ (fun y => u y - v y) x₀ := hud.sub hvd
    have hhopf := hopf_lemma_of_zero hd hθ hsymm hell ha hb hc (hu.sub hv) (huc.sub hvc) hw hr
      hball hx₀ hlt (by linarith) hwd
    have hfw : fderiv ℝ (fun y => u y - v y) x₀ = 0 := by
      have := fderiv_sub hud hvd
      rw [hfd, sub_self] at this
      exact this
    rw [hfw] at hhopf
    simp at hhopf

/-- A function that is constant on an open set and continuous on its closure is constant on the
closure. -/
theorem eq_on_closure_of_eq_on {U : Set (EuclideanSpace ℝ (Fin d))}
    {w : EuclideanSpace ℝ (Fin d) → ℝ} (hwc : ContinuousOn w (closure U)) {M : ℝ}
    (h : ∀ x ∈ U, w x = M) : ∀ x ∈ closure U, w x = M := by
  have hcl : IsClosed (closure U ∩ w ⁻¹' {M}) :=
    hwc.preimage_isClosed_of_isClosed isClosed_closure isClosed_singleton
  have hsub : U ⊆ closure U ∩ w ⁻¹' {M} := fun x hx => ⟨subset_closure hx, h x hx⟩
  intro x hx
  exact ((hcl.closure_subset_iff.mpr hsub) hx).2

/-- A solution with nonnegative maximum over the closure and zero normal derivative along an
interior sphere at every frontier point is constant on the closure. -/
theorem eq_const_of_neumann_aux (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ A B C : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ U, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    (hc0 : ∀ x ∈ U, 0 ≤ c x) (hcC : ∀ x ∈ U, c x ≤ C)
    {w : EuclideanSpace ℝ (Fin d) → ℝ} (hw : ContDiffOn ℝ 2 w U)
    (hwc : ContinuousOn w (closure U)) (hsub : ∀ x ∈ U, nondivOp a b c w x ≤ 0)
    (hν : ∀ y ∈ frontier U, DifferentiableAt ℝ w y ∧ ∃ z r, 0 < r ∧ ball z r ⊆ U ∧
      dist y z = r ∧ fderiv ℝ w y (y - z) = 0)
    {p : EuclideanSpace ℝ (Fin d)} (hp : p ∈ closure U) (hpmax : ∀ x ∈ closure U, w x ≤ w p)
    (hp0 : 0 ≤ w p) : ∀ x ∈ closure U, w x = w p := by
  -- an interior maximum point gives constancy
  have hint : ∀ x₀ ∈ U, w x₀ = w p → ∀ x ∈ closure U, w x = w p := by
    intro x₀ hx₀ hx₀eq
    refine eq_on_closure_of_eq_on hwc fun x hx => ?_
    have := strong_maximum_principle hd hU hUc hθ hsymm hell ha hb hc0 hcC hw hsub hx₀
      (fun x hx => by rw [hx₀eq]; exact hpmax x (subset_closure hx))
      (fun x hx => by rw [hx₀eq]; exact mul_nonneg (hc0 x hx) hp0) x hx
    rw [this, hx₀eq]
  by_cases hpU : p ∈ U
  · exact hint p hpU rfl
  · have hpfr : p ∈ frontier U := by
      rw [hU.frontier_eq]
      exact ⟨hp, hpU⟩
    by_cases hex : ∃ x₀ ∈ U, w x₀ = w p
    · obtain ⟨x₀, hx₀, hx₀eq⟩ := hex
      exact hint x₀ hx₀ hx₀eq
    · exfalso
      have hlt : ∀ x ∈ U, w x < w p := fun x hx =>
        lt_of_le_of_ne (hpmax x (subset_closure hx)) fun h => hex ⟨x, hx, h⟩
      obtain ⟨hdiff, z, r, hr, hball, hdist, hfz⟩ := hν p hpfr
      have hhopf := hopf_lemma hd hθ hsymm hell ha hb hc0 hcC hw hwc hsub hr hball hdist hlt
        (fun x hx => mul_nonneg (hc0 x hx) hp0) hdiff
      rw [hfz] at hhopf
      exact lt_irrefl _ hhopf

/-- **Uniqueness for the Neumann problem** (Guo Corollary XI.4.8). On a bounded connected open
set with an interior sphere at every frontier point, with `c ≥ 0` bounded, two functions with
the same image under `L`, differentiable at every frontier point and with the same derivative
there along the radius of an interior sphere, differ by a constant on the closure. -/
theorem neumann_unique (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ A B C : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ U, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    (hc0 : ∀ x ∈ U, 0 ≤ c x) (hcC : ∀ x ∈ U, c x ≤ C)
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hL : ∀ x ∈ U, nondivOp a b c u x = nondivOp a b c v x)
    (hν : ∀ y ∈ frontier U, DifferentiableAt ℝ u y ∧ DifferentiableAt ℝ v y ∧
      ∃ z r, 0 < r ∧ ball z r ⊆ U ∧ dist y z = r ∧
        fderiv ℝ u y (y - z) = fderiv ℝ v y (y - z)) :
    ∃ M : ℝ, ∀ x ∈ closure U, u x = v x + M := by
  set w : EuclideanSpace ℝ (Fin d) → ℝ := fun y => u y - v y with hwdef
  have hw : ContDiffOn ℝ 2 w U := hu.sub hv
  have hwc : ContinuousOn w (closure U) := huc.sub hvc
  have hsol : ∀ x ∈ U, nondivOp a b c w x = 0 := fun x hx => by
    rw [hwdef, nondivOp_sub hU hu hv a b c hx, hL x hx, sub_self]
  have hwν : ∀ y ∈ frontier U, DifferentiableAt ℝ w y ∧ ∃ z r, 0 < r ∧ ball z r ⊆ U ∧
      dist y z = r ∧ fderiv ℝ w y (y - z) = 0 := by
    intro y hy
    obtain ⟨hud, hvd, z, r, hr, hball, hdist, hfd⟩ := hν y hy
    refine ⟨hud.sub hvd, z, r, hr, hball, hdist, ?_⟩
    have : fderiv ℝ w y = fderiv ℝ u y - fderiv ℝ v y := fderiv_sub hud hvd
    rw [this, _root_.sub_apply, hfd, sub_self]
  have hcl : IsCompact (closure U) := hUb.isCompact_closure
  have hclne : (closure U).Nonempty := hUne.closure
  obtain ⟨p, hp, hpmax⟩ := hcl.exists_isMaxOn hclne hwc
  obtain ⟨q, hq, hqmin⟩ := hcl.exists_isMinOn hclne hwc
  rcases le_or_gt 0 (w p) with hp0 | hp0
  · refine ⟨u p - v p, fun x hx => ?_⟩
    have := eq_const_of_neumann_aux hd hU hUc hθ hsymm hell ha hb hc0 hcC hw hwc
      (fun x hx => (hsol x hx).le) hwν hp (fun x hx => hpmax hx) hp0 x hx
    simp only [hwdef] at this
    linarith
  · -- the negative of `w` has nonnegative maximum at `q`
    have hnw : ContDiffOn ℝ 2 (fun y => -w y) U := hw.neg
    have hnwc : ContinuousOn (fun y => -w y) (closure U) := hwc.neg
    have hnsub : ∀ x ∈ U, nondivOp a b c (fun y => -w y) x ≤ 0 := fun x hx => by
      rw [nondivOp_neg hU hw a b c hx, hsol x hx, neg_zero]
    have hnν : ∀ y ∈ frontier U, DifferentiableAt ℝ (fun y => -w y) y ∧ ∃ z r, 0 < r ∧
        ball z r ⊆ U ∧ dist y z = r ∧ fderiv ℝ (fun y => -w y) y (y - z) = 0 := by
      intro y hy
      obtain ⟨hd', z, r, hr, hball, hdist, hfz⟩ := hwν y hy
      refine ⟨hd'.neg, z, r, hr, hball, hdist, ?_⟩
      have e : fderiv ℝ (fun y => -w y) y = -fderiv ℝ w y := fderiv_neg
      rw [e, _root_.neg_apply, hfz, neg_zero]
    have hqmax : ∀ x ∈ closure U, (fun y => -w y) x ≤ (fun y => -w y) q := fun x hx => by
      have h1 : w q ≤ w x := hqmin hx
      simp only
      linarith
    have hq0 : 0 ≤ (fun y => -w y) q := by
      have h1 : w q ≤ w p := hpmax hq
      simp only
      linarith
    refine ⟨u q - v q, fun x hx => ?_⟩
    have := eq_const_of_neumann_aux hd hU hUc hθ hsymm hell ha hb hc0 hcC hnw hnwc hnsub
      hnν hq hqmax hq0 x hx
    simp only [hwdef] at this
    linarith

/-- **Uniqueness for the Neumann problem with a nonzero zeroth-order coefficient** (Guo Remark
XI.4.9). When `c` is positive somewhere on the set, the constant is zero. -/
theorem neumann_unique_of_exists_pos (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ A B C : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ U, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    (hc0 : ∀ x ∈ U, 0 ≤ c x) (hcC : ∀ x ∈ U, c x ≤ C) (hcpos : ∃ x ∈ U, c x ≠ 0)
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hL : ∀ x ∈ U, nondivOp a b c u x = nondivOp a b c v x)
    (hν : ∀ y ∈ frontier U, DifferentiableAt ℝ u y ∧ DifferentiableAt ℝ v y ∧
      ∃ z r, 0 < r ∧ ball z r ⊆ U ∧ dist y z = r ∧
        fderiv ℝ u y (y - z) = fderiv ℝ v y (y - z)) :
    ∀ x ∈ closure U, u x = v x := by
  obtain ⟨M, hM⟩ := neumann_unique hd hU hUc hUb hUne hθ hsymm hell ha hb hc0 hcC hu hv huc hvc
    hL hν
  obtain ⟨x₁, hx₁, hc₁⟩ := hcpos
  -- on the set, `u - v` is the constant `M`, so `L` of it is `c M`
  have hwM : ∀ x ∈ U, (fun y => u y - v y) x = (fun _ => M) x := fun x hx => by
    simp only
    linarith [hM x (subset_closure hx)]
  have hL' : nondivOp a b c (fun y => u y - v y) x₁ = nondivOp a b c (fun _ => M) x₁ := by
    unfold nondivOp
    have hfd : ∀ i, ∀ x ∈ U, partialD i (fun y => u y - v y) x = partialD i (fun _ => M) x := by
      intro i x hx
      simp only [partialD]
      rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) hwM)]
    have hfd2 : ∀ i j, partialD i (partialD j (fun y => u y - v y)) x₁
        = partialD i (partialD j (fun _ => M)) x₁ := by
      intro i j
      have h := (Filter.eventuallyEq_of_mem (hU.mem_nhds hx₁) (hfd j)).fderiv_eq (𝕜 := ℝ)
      change fderiv ℝ (partialD j fun y => u y - v y) x₁ (e i)
        = fderiv ℝ (partialD j fun _ => M) x₁ (e i)
      rw [h]
    simp only [hfd2, hfd _ x₁ hx₁, hwM x₁ hx₁]
  rw [nondivOp_sub hU hu hv a b c hx₁, hL x₁ hx₁, sub_self, nondivOp_const] at hL'
  have hM0 : M = 0 := by
    rcases mul_eq_zero.mp hL'.symm with h | h
    · exact absurd h hc₁
    · exact h
  intro x hx
  have := hM x hx
  rw [hM0, add_zero] at this
  exact this

end EllipticPdes.Classical
