/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Legendre.Basic
public import Mathlib.Analysis.Normed.Affine.Convex

/-!
# Finite affine maxima below a Legendre transform

`affineMaximum s hs a y` is the maximum of the affine functions `y ↦ ⟪x, y⟫ - a x` over a nonempty
finite set `s`
(`continuous_affineMaximum`). Every open neighbourhood of `0` in a finite-dimensional space contains
such a set whose
convex hull has `0` in its interior, including in dimension zero
(`exists_finite_hull_neighborhood`), and then the
maximum grows at least linearly with a constant independent of intercepts bounded at the vertices
(`affineMaximum_coercive`). With intercepts `(ψ ·).toReal` at finite values it lies below `legendre
ψ`
(`affineMaximum_le_legendre`); convergence at the finitely many vertices gives one eventual uniform
lower bound for the
transforms of a sequence (`eventually_affineMaximum_sub_le_legendre`, Cordero-Erausquin–Klartag,
*Moment measures*,
arXiv:1304.0630v1, (60)).

This is the geometric part of the proof of Lemma 17, (56b); the integration step is in
`Probability/MomentMeasure/ConjugateMass.lean`.
-/

@[expose] public section

noncomputable section
open Filter Set
open scoped Topology

namespace FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A genuine finite maximum of the affine summands of a conjugate. -/
def affineMaximum (s : Finset E) (hs : s.Nonempty) (a : E → ℝ) (y : E) : ℝ :=
  s.sup' hs (fun x => inner ℝ x y - a x)

theorem continuous_affineMaximum (s : Finset E) (hs : s.Nonempty) (a : E → ℝ) :
    Continuous (affineMaximum s hs a) := by
  exact Continuous.finset_sup'_apply hs fun x _ =>
    (continuous_const.inner continuous_id).sub continuous_const

/-- A simplex in the original open neighborhood supplies a finite witness whose
convex hull still contains a neighborhood of zero, including dimension zero. -/
theorem exists_finite_hull_neighborhood [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsOpen K) (h0 : (0 : E) ∈ K) :
    ∃ (s : Finset E) (_hs : s.Nonempty), (↑s : Set E) ⊆ K ∧
      (0 : E) ∈ interior (convexHull ℝ (↑s : Set E)) := by
  classical
  obtain ⟨b, hb0, hbK⟩ := exists_mem_interior_convexHull_affineBasis (hK.mem_nhds h0)
  let s : Finset E := Finset.univ.image b
  have heq : (↑s : Set E) = range b := by simp [s]
  refine ⟨s, Finset.univ_nonempty.image b, ?_, ?_⟩
  · rw [heq]
    exact (subset_convexHull ℝ (range b)).trans hbK
  · rwa [heq]

/-- The geometric neighborhood produces a linear lower bound for the actual
finite affine maximum. The intercept bound is only at its finitely many vertices. -/
theorem affineMaximum_coercive [FiniteDimensional ℝ E]
    (s : Finset E) (hs : s.Nonempty)
    (h0 : (0 : E) ∈ interior (convexHull ℝ (↑s : Set E))) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : E → ℝ) (M : ℝ), (∀ x ∈ s, a x ≤ M) →
      ∀ y, c * ‖y‖ - M ≤ affineMaximum s hs a y := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp h0)
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro a M ha y
  let A := affineMaximum s hs a y
  have hvertices : (↑s : Set E) ⊆ {x | inner ℝ x y ≤ A + M} := by
    intro x hx
    change inner ℝ x y ≤ A + M
    have hmax := Finset.le_sup' (fun x => inner ℝ x y - a x) hx
    change inner ℝ x y - a x ≤ A at hmax
    have := ha x hx
    linarith
  have hhalf : Convex ℝ {x : E | inner ℝ x y ≤ A + M} := by
    intro x hx z hz α β hα hβ hsum
    simp only [mem_ofPred_eq, inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial]
    have hh := add_le_add (mul_le_mul_of_nonneg_left hx hα)
      (mul_le_mul_of_nonneg_left hz hβ)
    rw [← add_mul, hsum, one_mul] at hh
    exact hh
  have hhull := convexHull_min hvertices hhalf
  by_cases hy : y = 0
  · subst y
    have hz : (0 : E) ∈ convexHull ℝ (↑s : Set E) := interior_subset h0
    have hh := hhull hz
    simp only [mem_ofPred_eq, inner_zero_right] at hh
    simpa only [norm_zero, mul_zero, zero_sub] using (by linarith : -M ≤ A)
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  let z : E := (r / 2 / ‖y‖) • y
  have hz : z ∈ Metric.ball (0 : E) r := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos (half_pos hr) hn), div_mul_cancel₀ _ hn.ne']
    linarith
  have hh := hhull (hball hz)
  change inner ℝ z y ≤ A + M at hh
  have hinner : inner ℝ z y = (r / 2) * ‖y‖ := by
    dsimp [z]
    rw [inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [starRingEnd_apply, star_trivial]
    field_simp
  rw [hinner] at hh
  linarith

/-- CEK (60), for an arbitrary genuine finite set: pointwise convergence at
its vertices yields one eventual bound uniform over every dual point. -/
theorem eventually_affineMaximum_sub_le_legendre
    (φ : ℕ → E → EReal) (ψ : E → EReal) (s : Finset E) (hs : s.Nonempty)
    (hfin : ∀ x ∈ s, ψ x ≠ ⊤ ∧ ψ x ≠ ⊥)
    (hlim : ∀ x ∈ s, Tendsto (fun j => φ j x) atTop (𝓝 (ψ x)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ y : E,
      ((affineMaximum s hs (fun x => (ψ x).toReal) y - ε : ℝ) : EReal) ≤
        legendre (φ j) y := by
  have hupper : ∀ᶠ j in atTop, ∀ x ∈ s,
      φ j x ≤ ((ψ x).toReal + ε : ℝ) := by
    apply (eventually_all_finset s).mpr
    intro x hx
    have hc := EReal.coe_toReal (hfin x hx).1 (hfin x hx).2
    have hlt : ψ x < (((ψ x).toReal + ε : ℝ) : EReal) := by
      rw [← hc]
      exact EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right _ hε)
    exact ((hlim x hx).eventually (Iio_mem_nhds hlt)).mono fun _ h => h.le
  filter_upwards [hupper] with j hj
  intro y
  obtain ⟨x, hx, hmax⟩ := s.exists_mem_eq_sup' hs (fun x => inner ℝ x y - (ψ x).toReal)
  change ((s.sup' hs (fun x => inner ℝ x y - (ψ x).toReal) - ε : ℝ) : EReal) ≤ _
  rw [hmax]
  have hterm : ((inner ℝ x y - (ψ x).toReal - ε : ℝ) : EReal) ≤
      (inner ℝ x y : EReal) - φ j x := by
    have h := EReal.sub_le_sub (le_refl (inner ℝ x y : EReal)) (hj x hx)
    convert h using 1
    rw [← EReal.coe_sub]
    congr 1
    ring
  exact hterm.trans (le_iSup (fun z : E => (inner ℝ z y : EReal) - φ j z) x)

/-- Finite affine maxima are genuine lower bounds of the full conjugate. -/
theorem affineMaximum_le_legendre (ψ : E → EReal) (s : Finset E) (hs : s.Nonempty)
    (hfin : ∀ x ∈ s, ψ x ≠ ⊤ ∧ ψ x ≠ ⊥) (y : E) :
    (affineMaximum s hs (fun x => (ψ x).toReal) y : EReal) ≤ legendre ψ y := by
  obtain ⟨x, hx, heq⟩ := s.exists_mem_eq_sup' hs (fun x => inner ℝ x y - (ψ x).toReal)
  change ((s.sup' hs (fun x => inner ℝ x y - (ψ x).toReal) : ℝ) : EReal) ≤ _
  rw [heq, EReal.coe_sub, EReal.coe_toReal (hfin x hx).1 (hfin x hx).2]
  exact le_iSup (fun z : E => (inner ℝ z y : EReal) - ψ z) x

end FunctionalInequalities.Analysis
