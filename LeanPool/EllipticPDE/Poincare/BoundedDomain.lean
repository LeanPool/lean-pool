/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Poincare.BoxSlice


/-!
# Poincaré inequality on arbitrary bounded domains (chain step 5)

`BoxSlice.lean` discharges the per-direction slice bound when the domain IS the open
coordinate box. This file removes that restriction: any `Ω` contained in a box inherits
the slice bound, because a test function of `Ω` is a test function of the box
(`IsTestFn.mono`) and the box integrals restrict to `Ω` (the integrands vanish off
`tsupport φ ⊆ Ω`). Averaging (`poincare_testfn`) and density (`poincare_H01`) are already
domain-general, so the Poincaré inequality follows on every bounded domain
(`poincare_H01_of_bounded`), with the closed-form constant `L²/(2(n+1))` from any
bounding box of side `L`. This is the `p = q = 2` Friedrichs (Poincaré) inequality
for `H₀¹`; the limit passage from test functions to `H₀¹(Ω)` by density is the
density step `poincare_H01`, which is architectural here because `H₀¹` is defined
as the closure of the test-function graphs.
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace EllipticPdes.Poincare

open EllipticPdes.Sobolev

variable {n : ℕ}

/-- **Per-direction Poincaré bound for a subset of a box.** A test function of any
`Ω` inside the open box obeys the box slice bound with the integrals taken over `Ω`. -/
theorem slice_bound_of_subset_euclBox {a b : Fin (n + 1) → ℝ} (hab : ∀ k, a k ≤ b k)
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hsub : Ω ⊆ euclBox a b)
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (h : IsTestFn Ω φ) (i : Fin (n + 1)) :
    ∫ x in Ω, (φ x) ^ 2 ≤ (b i - a i) ^ 2 / 2 * ∫ x in Ω, (partialD i φ x) ^ 2 := by
  have hbox : IsTestFn (euclBox a b) φ := h.mono hsub
  -- Both box integrals restrict to `Ω`: the integrands vanish on `euclBox \ Ω`.
  have hφeq : ∫ x in euclBox a b, (φ x) ^ 2 = ∫ x in Ω, (φ x) ^ 2 :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (isOpen_euclBox a b).measurableSet hsub
      (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun hm => hx.2 (h.2.2 hm))]
        ring)
  have hdeq : ∫ x in euclBox a b, (partialD i φ x) ^ 2
      = ∫ x in Ω, (partialD i φ x) ^ 2 :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (isOpen_euclBox a b).measurableSet hsub
      (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport
          (fun hm => hx.2 (((tsupport_partialD_subset i φ).trans h.2.2) hm))]
        ring)
  calc ∫ x in Ω, (φ x) ^ 2
      = ∫ x in euclBox a b, (φ x) ^ 2 := hφeq.symm
    _ ≤ (b i - a i) ^ 2 / 2 * ∫ x in euclBox a b, (partialD i φ x) ^ 2 :=
        slice_bound_euclBox a b hab hbox i
    _ = (b i - a i) ^ 2 / 2 * ∫ x in Ω, (partialD i φ x) ^ 2 := by rw [hdeq]

/-- **Poincaré inequality on `H₀¹(Ω)` for `Ω` inside a box** with sides at most `L`:
`‖U₀‖² ≤ L²/(2(n+1)) · ∑ᵢ ‖Uᵢ‖²`. -/
theorem poincare_H01_of_subset_euclBox {a b : Fin (n + 1) → ℝ} (hab : ∀ k, a k ≤ b k)
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hsub : Ω ⊆ euclBox a b)
    {L : ℝ} (hL : ∀ i, b i - a i ≤ L)
    {U : H1amb Ω} (hU : U ∈ H01 Ω) :
    ‖U 0‖ ^ 2 ≤ L ^ 2 / (2 * (n + 1)) * ∑ i : Fin (n + 1), ‖U i.succ‖ ^ 2 := by
  have hL0 : 0 ≤ L := le_trans (sub_nonneg.mpr (hab 0)) (hL 0)
  have hslice : ∀ {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
      (h : IsTestFn Ω φ) (i : Fin (n + 1)),
      ∫ x in Ω, (φ x) ^ 2 ≤ L ^ 2 / 2 * ∫ x in Ω, (partialD i φ x) ^ 2 := by
    intro φ h i
    refine le_trans (slice_bound_of_subset_euclBox hab hsub h i)
      (mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun x => sq_nonneg _))
    have hside : (b i - a i) ^ 2 ≤ L ^ 2 := by
      have h1 : 0 ≤ b i - a i := sub_nonneg.mpr (hab i)
      nlinarith [hL i]
    linarith
  have h := poincare_H01 (Ω := Ω) _
    (fun {_φ} hφ => poincare_testfn (Nat.succ_pos n) (L ^ 2 / 2)
      (fun {_ψ} h' i => hslice h' i) hφ) hU
  refine le_trans h (le_of_eq ?_)
  rw [div_div]
  norm_cast

/-- The test-function instance, in the slice-constant form the coercivity layer
consumes. Derived FROM `poincare_H01_of_subset_euclBox` (test graphs lie in `H₀¹`). -/
theorem testfn_bound_of_subset_euclBox {a b : Fin (n + 1) → ℝ} (hab : ∀ k, a k ≤ b k)
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hsub : Ω ⊆ euclBox a b)
    {C : ℝ} (hC : ∀ i, (b i - a i) ^ 2 / 2 ≤ C)
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (h : IsTestFn Ω φ) :
    ‖(h.testGraph 0 : L2D Ω)‖ ^ 2
      ≤ C / (n + 1) * ∑ i : Fin (n + 1), ‖h.testGraph i.succ‖ ^ 2 := by
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
  have h2C : (0 : ℝ) ≤ 2 * C := by linarith
  have hL : ∀ i, b i - a i ≤ Real.sqrt (2 * C) := by
    intro i
    have h1 : 0 ≤ b i - a i := sub_nonneg.mpr (hab i)
    have h2 : (b i - a i) ^ 2 ≤ 2 * C := by linarith [hC i]
    calc b i - a i = Real.sqrt ((b i - a i) ^ 2) := (Real.sqrt_sq h1).symm
      _ ≤ Real.sqrt (2 * C) := Real.sqrt_le_sqrt h2
  have hmem : h.testGraph ∈ H01 Ω :=
    (Submodule.le_topologicalClosure _) (Submodule.subset_span ⟨φ, h, rfl⟩)
  have hp := poincare_H01_of_subset_euclBox hab hsub hL hmem
  rw [Real.sq_sqrt h2C] at hp
  refine le_trans hp (le_of_eq ?_)
  rw [mul_div_mul_left C ((n : ℝ) + 1) two_ne_zero]

/-- Every bounded set sits inside an open coordinate box with sides bounded by a
single `L` (derived from a bounding radius about the origin). -/
theorem exists_euclBox_superset {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩb : Bornology.IsBounded Ω) :
    ∃ (a b : Fin (n + 1) → ℝ) (L : ℝ), (∀ k, a k ≤ b k) ∧ Ω ⊆ euclBox a b
      ∧ ∀ i, b i - a i ≤ L := by
  obtain ⟨R, hR⟩ := hΩb.subset_closedBall 0
  set M : ℝ := max R 0 + 1
  have hM0 : 0 < M := by
    have : (0 : ℝ) ≤ max R 0 := le_max_right R 0
    linarith
  refine ⟨fun _ => -M, fun _ => M, 2 * M, fun k => by linarith, ?_, fun i => by linarith⟩
  intro x hx
  have hxR : ‖x‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hR hx
  intro k
  have habs : |x k| ≤ ‖x‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x k
  have hlt : |x k| < M := by
    have : R ≤ max R 0 := le_max_left R 0
    linarith [le_trans habs hxR]
  exact ⟨by simpa using (abs_lt.mp hlt).1, (abs_lt.mp hlt).2⟩

/-- **Poincaré inequality on `H₀¹` of an arbitrary bounded domain** (the
Friedrichs inequality, `p = q = 2`): some constant `C ≥ 0` controls the function part
by the gradient part, uniformly over `H₀¹(Ω)`.

Guo, *Partial Differential Equations* (JHU AS.110.631-632), Theorem III.4.6 states the
`W_0^{1,p}` form, `‖u‖_{L^q} ≤ C ‖Du‖_{L^p}` for `q ∈ [1, p*]`, and derives it from the
Gagliardo-Nirenberg-Sobolev inequality. This declaration is its `p = q = 2` case, proved
on a different route and consequently in every dimension: Guo's hypothesis `p ∈ [1, n)`
reads `n > 2` at `p = 2`, excluding `n = 1` and `n = 2`, because the GNS route needs a
finite Sobolev conjugate. The route here goes through the one-dimensional inequality and
Fubini, which asks nothing of the dimension, with the constant `L²/(2(n+1))`
in place of the sharp one. -/
theorem poincare_H01_of_bounded {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩb : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : H1amb Ω), U ∈ H01 Ω →
      ‖U 0‖ ^ 2 ≤ C * ∑ i : Fin (n + 1), ‖U i.succ‖ ^ 2 := by
  obtain ⟨a, b, L, hab, hsub, hL⟩ := exists_euclBox_superset hΩb
  have hL0 : 0 ≤ L := le_trans (sub_nonneg.mpr (hab 0)) (hL 0)
  exact ⟨L ^ 2 / (2 * (n + 1)), by positivity, fun U hU =>
    poincare_H01_of_subset_euclBox hab hsub hL hU⟩

/-- **Coercivity of the bilinear form of the Laplacian on a bounded domain**, with no abstract
Poincaré
hypothesis. `poincare_H01_of_bounded` names the constant, so the only input is boundedness of
`Ω`. This is the form of coercivity the direct method uses, where the domain is a ball and no
box structure is at hand. -/
theorem laplaceBilin_coercive_of_bounded {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩb : Bornology.IsBounded Ω) : IsCoercive (EllipticPdes.laplaceBilin Ω) := by
  obtain ⟨C, hC, hpoin⟩ := poincare_H01_of_bounded hΩb
  have hpos : (0 : ℝ) < C + 1 := by linarith
  refine ⟨1 / (C + 1), by positivity, fun U => ?_⟩
  set S : ℝ := ∑ i : Fin (n + 1), ‖(U : H1amb Ω) i.succ‖ ^ 2 with hS
  have hBUU : EllipticPdes.laplaceBilin Ω U U = S := EllipticPdes.laplaceBilin_self Ω U
  have hnorm : ‖U‖ ^ 2 = ‖(U : H1amb Ω) 0‖ ^ 2 + S := by
    rw [show ‖U‖ = ‖(U : H1amb Ω)‖ from rfl, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
  have hkey : ‖U‖ * ‖U‖ ≤ (C + 1) * S := by
    have h1 : ‖U‖ ^ 2 ≤ (C + 1) * S := by
      rw [hnorm]
      nlinarith [hpoin (U : H1amb Ω) U.2]
    nlinarith [h1]
  rw [hBUU, mul_assoc]
  calc 1 / (C + 1) * (‖U‖ * ‖U‖)
      ≤ 1 / (C + 1) * ((C + 1) * S) := mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = S := by rw [← mul_assoc, one_div_mul_cancel hpos.ne', one_mul]

end EllipticPdes.Poincare
