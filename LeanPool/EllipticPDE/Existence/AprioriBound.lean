/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Existence.ClassicalMaximum


/-!
# A priori bound from the maximum principle

For a subsolution of `L u = f` on a bounded open set lying in a slab of width `D` in a
coordinate direction, with `c ≥ 0`, the supremum of `u` is bounded by the supremum of its
positive part over the boundary plus `(e^{(B/θ + 1) D} - 1)` times the bound on `f` over `θ`.
The comparison function is `sup u⁺ + (F/θ)(e^{αD} - e^{α (x_{i₀} - m)})` at `α = B/θ + 1`,
whose image under `L` is at least `F`, so the comparison principle applies. A solution is
bounded in absolute value by the same expression with the boundary supremum of `|u|`.

## Main declarations

* `EllipticPdes.Classical.apriori_bound_sub`: the bound for a subsolution.
* `EllipticPdes.Classical.apriori_bound_abs`: the bound for a solution.

## Operator convention

The non-divergence operator here is `L u = -∑ aᵢⱼ ∂ᵢⱼu + ∑ bᵢ ∂ᵢu + c u`.
All Guo results cited in this file are translated by negating the source operator:
Guo's operator is `-L`, with coefficients `a`, `-b`, `-c`. Thus his subsolution inequality
`(-L) u ≥ 0` becomes `L u ≤ 0`, and his potential condition `-c ≤ 0` becomes `c ≥ 0`.

## References

James Guo, *Partial Differential Equations* (Course Lecture Notes), Theorem XI.5.1
(p. 103); D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second
Order*, Theorem 3.7 (p. 36).
-/

@[expose] public section

open Set Filter Topology Metric

noncomputable section

namespace EllipticPdes.Classical

variable {d : ℕ}

/-- The diagonal coefficient is at least the ellipticity constant. -/
theorem le_diag_of_ell {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {θ : ℝ}
    {z : EuclideanSpace ℝ (Fin d)}
    (hell : ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a z i j * ξ i * ξ j) (i₀ : Fin d) :
    θ ≤ a z i₀ i₀ := by
  classical
  have h := hell (Pi.single i₀ (1 : ℝ) : Fin d → ℝ)
  have hs1 : ∑ i, ((Pi.single i₀ (1 : ℝ) : Fin d → ℝ) i) ^ 2 = 1 := by
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro i _ hi
      simp [hi]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hs2 : ∑ i, ∑ j, a z i j * (Pi.single i₀ (1 : ℝ) : Fin d → ℝ) i
      * (Pi.single i₀ (1 : ℝ) : Fin d → ℝ) j = a z i₀ i₀ := by
    rw [Finset.sum_eq_single i₀]
    · rw [Finset.sum_eq_single i₀]
      · simp
      · intro j _ hj
        simp [hj]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · intro i _ hi
      simp [hi]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hs1, hs2, mul_one] at h
  exact h

/-- The coordinate map is continuous. -/
theorem continuous_coord (i₀ : Fin d) :
    Continuous fun x : EuclideanSpace ℝ (Fin d) => x i₀ :=
  (EuclideanSpace.proj i₀ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous

/-- A slab bound on an open set extends to its closure. -/
theorem slab_closure {U : Set (EuclideanSpace ℝ (Fin d))} {i₀ : Fin d} {m D : ℝ}
    (hslab : ∀ x ∈ U, m ≤ x i₀ ∧ x i₀ ≤ m + D) :
    ∀ x ∈ closure U, m ≤ x i₀ ∧ x i₀ ≤ m + D := by
  have hcl : IsClosed {x : EuclideanSpace ℝ (Fin d) | m ≤ x i₀ ∧ x i₀ ≤ m + D} :=
    (isClosed_le continuous_const (continuous_coord i₀)).inter
      (isClosed_le (continuous_coord i₀) continuous_const)
  intro x hx
  exact (hcl.closure_subset_iff.mpr fun y hy => hslab y hy) hx

/-- **Maximum-principle bound for a subsolution** (Guo Theorem XI.5.1(i), Gilbarg and Trudinger
Theorem 3.7). On a bounded open set inside the slab `m ≤ x_{i₀} ≤ m + D`, with `c ≥ 0`, a function
with `L u ≤ f` and `f ≤ F` is bounded by the maximum of its positive part over the boundary
plus `(e^{(B/θ + 1) D} - 1) F/θ`. -/
theorem apriori_bound_sub (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x)
    {i₀ : Fin d} {m D : ℝ} (hslab : ∀ x ∈ U, m ≤ x i₀ ∧ x i₀ ≤ m + D)
    {u f : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsub : ∀ x ∈ U, nondivOp a b c u x ≤ f x)
    {F : ℝ} (hF0 : 0 ≤ F) (hF : ∀ x ∈ U, f x ≤ F) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U,
      u x ≤ max (u y) 0 + (Real.exp ((B / θ + 1) * D) - 1) * (F / θ) := by
  classical
  obtain ⟨x₁, hx₁⟩ := hUne
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hb x₁ hx₁ (⟨0, hd⟩ : Fin d))
  have hD0 : 0 ≤ D := by linarith [hslab x₁ hx₁]
  -- the maximum of `u` over the frontier
  have hcl : IsCompact (closure U) := hUb.isCompact_closure
  have hfr : IsCompact (frontier U) :=
    hcl.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨y, hyfr, hymax⟩ := hfr.exists_isMaxOn (frontier_nonempty_of_isBounded hd hUb ⟨x₁, hx₁⟩)
    (huc.mono frontier_subset_closure)
  refine ⟨y, hyfr, ?_⟩
  set K : ℝ := max (u y) 0 with hK
  have hK0 : 0 ≤ K := le_max_right _ _
  -- the comparison function
  set α : ℝ := B / θ + 1 with hα
  have hα1 : 1 ≤ α := by
    have : 0 ≤ B / θ := div_nonneg hB0 hθ.le
    linarith
  have hα0 : 0 < α := by linarith
  set ε : ℝ := -(F / θ) * Real.exp (-α * m) with hε
  set c₀ : ℝ := K + F / θ * Real.exp (α * D) with hc₀
  set v : EuclideanSpace ℝ (Fin d) → ℝ := fun x => c₀ + ε * expFn α i₀ x with hv
  have hvx : ∀ x, v x = K + F / θ * (Real.exp (α * D) - Real.exp (α * (x i₀ - m))) := by
    intro x
    simp only [hv, hc₀, hε, expFn]
    rw [show α * (x i₀ - m) = -α * m + α * x i₀ by ring, Real.exp_add]
    ring
  have hvC : ContDiffOn ℝ 2 v U :=
    contDiffOn_const.add (contDiffOn_const.mul (contDiff_expFn α i₀).contDiffOn)
  have hvc : ContinuousOn v (closure U) :=
    continuousOn_const.add (continuousOn_const.mul (contDiff_expFn α i₀).continuous.continuousOn)
  have hF' : 0 ≤ F / θ := div_nonneg hF0 hθ.le
  -- `v` is nonnegative and at most `K + (e^{αD} - 1) F/θ` on the closure
  have hvbd : ∀ x ∈ closure U,
      0 ≤ v x ∧ v x ≤ K + (Real.exp (α * D) - 1) * (F / θ) := by
    intro x hx
    obtain ⟨h1, h2⟩ := slab_closure hslab x hx
    rw [hvx]
    have e1 : 1 ≤ Real.exp (α * (x i₀ - m)) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (mul_nonneg hα0.le (by linarith))
    have e2 : Real.exp (α * (x i₀ - m)) ≤ Real.exp (α * D) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hα0.le)
    constructor
    · nlinarith [mul_nonneg hF' (sub_nonneg.mpr e2)]
    · nlinarith [mul_nonneg hF' (sub_nonneg.mpr e1)]
  -- `L u ≤ L v` on the set
  have hL : ∀ x ∈ U, nondivOp a b c u x ≤ nondivOp a b c v x := by
    intro x hx
    obtain ⟨h1, _⟩ := hslab x hx
    rw [hv, nondivOp_add_smul hU contDiffOn_const (contDiff_expFn α i₀).contDiffOn a b c ε hx,
      nondivOp_const, nondivOp_expFn]
    have haa : θ ≤ a x i₀ i₀ := le_diag_of_ell (hell x hx) i₀
    have hbb : b x i₀ ≤ B := (abs_le.mp (hb x hx i₀)).2
    have hcx := hc x hx
    have hw : 1 ≤ Real.exp (-α * m) * expFn α i₀ x := by
      simp only [expFn]
      rw [← Real.exp_add, ← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hwpos : 0 < expFn α i₀ x := expFn_pos α i₀ x
    have hepos : 0 < Real.exp (-α * m) := Real.exp_pos _
    -- the principal and transport part of `L (e^{α(x - m)})` is at least `θ`
    have hprin : θ ≤ (a x i₀ i₀ * α ^ 2 - b x i₀ * α) * (Real.exp (-α * m) * expFn α i₀ x) := by
      have hθα : θ * α = B + θ := by
        rw [hα]
        field_simp
      have h3 : θ * α ≤ a x i₀ i₀ * α ^ 2 - b x i₀ * α := by
        have e1 : θ * α ^ 2 ≤ a x i₀ i₀ * α ^ 2 := mul_le_mul_of_nonneg_right haa (sq_nonneg α)
        have e2 : b x i₀ * α ≤ B * α := mul_le_mul_of_nonneg_right hbb hα0.le
        have e3 : θ * α ^ 2 - B * α = θ * α := by linear_combination α * hθα
        linarith
      have h4 : θ ≤ θ * α := by nlinarith
      have h5 : 0 ≤ a x i₀ i₀ * α ^ 2 - b x i₀ * α := by linarith
      calc θ ≤ θ * α := h4
        _ ≤ a x i₀ i₀ * α ^ 2 - b x i₀ * α := h3
        _ = (a x i₀ i₀ * α ^ 2 - b x i₀ * α) * 1 := (mul_one _).symm
        _ ≤ (a x i₀ i₀ * α ^ 2 - b x i₀ * α) * (Real.exp (-α * m) * expFn α i₀ x) :=
            mul_le_mul_of_nonneg_left hw h5
    -- the zeroth-order part is `c v ≥ 0`
    have hcv : 0 ≤ c x * v x := mul_nonneg hcx (hvbd x (subset_closure hx)).1
    have hvx' := hvx x
    simp only [hv] at hvx' hcv
    have key : c x * c₀ + ε * ((-(a x i₀ i₀ * α ^ 2) + b x i₀ * α + c x) * expFn α i₀ x)
        = F / θ * ((a x i₀ i₀ * α ^ 2 - b x i₀ * α) * (Real.exp (-α * m) * expFn α i₀ x))
          + c x * (c₀ + ε * expFn α i₀ x) := by
      simp only [hε]
      ring
    rw [key]
    have hFθ : F / θ * θ = F := div_mul_cancel₀ F hθ.ne'
    calc nondivOp a b c u x ≤ f x := hsub x hx
      _ ≤ F := hF x hx
      _ = F / θ * θ := hFθ.symm
      _ ≤ F / θ * ((a x i₀ i₀ * α ^ 2 - b x i₀ * α) * (Real.exp (-α * m) * expFn α i₀ x)) :=
          mul_le_mul_of_nonneg_left hprin hF'
      _ ≤ F / θ * ((a x i₀ i₀ * α ^ 2 - b x i₀ * α) * (Real.exp (-α * m) * expFn α i₀ x))
          + c x * (c₀ + ε * expFn α i₀ x) := by linarith
  -- `u ≤ v` on the frontier
  have hbd : ∀ x ∈ frontier U, u x ≤ v x := by
    intro x hx
    have h1 : u x ≤ u y := hymax hx
    have h2 : u y ≤ K := le_max_left _ _
    have h3 := (hvbd x (frontier_subset_closure hx))
    rw [hvx] at h3 ⊢
    have h4 : 0 ≤ F / θ * (Real.exp (α * D) - Real.exp (α * (x i₀ - m))) := by
      obtain ⟨_, hx2⟩ := slab_closure hslab x (frontier_subset_closure hx)
      exact mul_nonneg hF' (sub_nonneg.mpr (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (by linarith) hα0.le)))
    linarith
  intro x hx
  have := comparison_principle hd hU hUb ⟨x₁, hx₁⟩ hθ hsymm hell hb hc hu hvC huc hvc hL hbd x hx
  have hb2 := (hvbd x hx).2
  rw [hα] at hb2
  linarith

/-- **Maximum-principle bound for a solution** (Guo Theorem XI.5.1(ii), Gilbarg and Trudinger
Theorem 3.7). On a bounded open set inside the slab `m ≤ x_{i₀} ≤ m + D`, with `c ≥ 0`, a function
with `L u = f` and `|f| ≤ F` is bounded in absolute value by the maximum of `|u|` over the
boundary plus `(e^{(B/θ + 1) D} - 1) F/θ`. -/
theorem apriori_bound_abs (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x)
    {i₀ : Fin d} {m D : ℝ} (hslab : ∀ x ∈ U, m ≤ x i₀ ∧ x i₀ ≤ m + D)
    {u f : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsol : ∀ x ∈ U, nondivOp a b c u x = f x)
    {F : ℝ} (hF : ∀ x ∈ U, |f x| ≤ F) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U,
      |u x| ≤ |u y| + (Real.exp ((B / θ + 1) * D) - 1) * (F / θ) := by
  obtain ⟨x₁, hx₁⟩ := hUne
  have hF0 : 0 ≤ F := (abs_nonneg _).trans (hF x₁ hx₁)
  have hcl : IsCompact (closure U) := hUb.isCompact_closure
  have hfr : IsCompact (frontier U) :=
    hcl.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨y, hyfr, hymax⟩ := hfr.exists_isMaxOn (frontier_nonempty_of_isBounded hd hUb ⟨x₁, hx₁⟩)
    ((huc.mono frontier_subset_closure).abs)
  refine ⟨y, hyfr, fun x hx => ?_⟩
  obtain ⟨y₁, hy₁, h₁⟩ := apriori_bound_sub hd hU hUb ⟨x₁, hx₁⟩ hθ hsymm hell hb hc hslab hu huc
    (f := f) (fun x hx => (hsol x hx).le) hF0 (fun x hx => (le_abs_self _).trans (hF x hx))
  have hneg : ∀ x ∈ U, nondivOp a b c (fun y => -u y) x ≤ (fun y => -f y) x := fun x hx => by
    rw [nondivOp_neg hU hu a b c hx, hsol x hx]
  obtain ⟨y₂, hy₂, h₂⟩ := apriori_bound_sub hd hU hUb ⟨x₁, hx₁⟩ hθ hsymm hell hb hc hslab hu.neg
    huc.neg hneg hF0 (fun x hx => (neg_le_abs _).trans (hF x hx))
  have hy₁' : |u y₁| ≤ |u y| := hymax hy₁
  have hy₂' : |u y₂| ≤ |u y| := hymax hy₂
  have m₁ : max (u y₁) 0 ≤ |u y₁| := max_le (le_abs_self _) (abs_nonneg _)
  have m₂ : max (-u y₂) 0 ≤ |u y₂| := max_le (neg_le_abs _) (abs_nonneg _)
  have e₁ := h₁ x hx
  have e₂ := h₂ x hx
  rw [abs_le]
  constructor
  · linarith
  · linarith

end EllipticPdes.Classical
