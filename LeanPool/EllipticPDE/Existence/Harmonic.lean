/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Existence.StrongMaximum


/-!
# Maximum principles for subharmonic functions

The Laplacian is the non-divergence operator with the identity as coefficient matrix and no
lower-order terms, up to sign. The classical weak and strong maximum principles and the
uniqueness of the Dirichlet problem specialise to subharmonic, superharmonic and harmonic
functions, in the sense of the sum of the second coordinate partials.

## Main declarations

* `EllipticPdes.Classical.laplacianSum`: the sum of the second coordinate partials.
* `EllipticPdes.Classical.nondivOp_laplace`: the Laplacian as a non-divergence operator.
* `EllipticPdes.Classical.weak_maximum_principle_subharmonic`: the weak maximum principle.
* `EllipticPdes.Classical.strong_maximum_principle_subharmonic`: the strong maximum principle.
* `EllipticPdes.Classical.strong_minimum_principle_superharmonic`: the strong minimum principle.
* `EllipticPdes.Classical.harmonic_const_of_max`, `harmonic_const_of_min`: a harmonic function
  attaining its supremum or infimum in the interior is constant.
* `EllipticPdes.Classical.dirichlet_unique_harmonic`: uniqueness for the Dirichlet problem.

## References

James Guo, *Partial Differential Equations* (Course Lecture Notes), Lemma XI.1.5,
Corollary XI.1.6, Lemma XI.1.7 (p. 92) and Lemma XI.2.4 (p. 95).
-/

@[expose] public section

open Set Filter Topology Metric

noncomputable section

namespace EllipticPdes.Classical

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- The sum of the second coordinate partials. -/
def laplacianSum (u : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, partialD i (partialD i u) x

/-- The identity coefficient matrix. -/
def idCoeff (i j : Fin d) : ℝ := if i = j then 1 else 0

/-- The Laplacian is the negative of the non-divergence operator with the identity as
coefficient matrix and no lower-order terms. -/
theorem nondivOp_laplace (u : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    nondivOp (fun _ => idCoeff) (fun _ _ => 0) (fun _ => 0) u x = -laplacianSum u x := by
  classical
  unfold nondivOp laplacianSum idCoeff
  simp [ite_mul, Finset.sum_ite_eq]

/-- The identity matrix is symmetric. -/
theorem idCoeff_symm (i j : Fin d) : idCoeff i j = idCoeff j i := by
  unfold idCoeff
  by_cases h : i = j
  · subst h
    rfl
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

/-- The identity matrix is elliptic with constant one. -/
theorem idCoeff_ell (ξ : Fin d → ℝ) :
    1 * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, idCoeff i j * ξ i * ξ j := by
  classical
  unfold idCoeff
  simp [ite_mul, Finset.sum_ite_eq, sq]

/-- The identity matrix is bounded by one. -/
theorem idCoeff_bdd (i j : Fin d) : |idCoeff i j| ≤ 1 := by
  unfold idCoeff
  by_cases h : i = j
  · rw [ite_eq_left h, abs_one]
  · rw [ite_eq_right h, abs_zero]
    exact zero_le_one

/-- The Laplacian of a negative. -/
theorem laplacianSum_neg {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ U) : laplacianSum (fun y => -u y) x = -laplacianSum u x := by
  have h := nondivOp_neg hU hu (fun _ => idCoeff) (fun _ _ => 0) (fun _ => 0) hx
  rw [nondivOp_laplace, nondivOp_laplace] at h
  linarith

/-- **Weak maximum principle for subharmonic functions** (Guo Lemma XI.1.7). A function `C²`
on a bounded open set, continuous on its closure, with nonnegative Laplacian on the set, attains
its maximum over the closure on the boundary. -/
theorem weak_maximum_principle_subharmonic (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsub : ∀ x ∈ U, 0 ≤ laplacianSum u x) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, u x ≤ u y :=
  weak_maximum_principle hd hU hUb hUne (a := fun _ => idCoeff) (b := fun _ _ => 0) (B := 0) one_pos
    (fun _ _ => idCoeff_symm) (fun _ _ => idCoeff_ell) (fun _ _ _ => by simp) hu huc
    fun x hx => by
      rw [nondivOp_laplace]
      linarith [hsub x hx]

/-- **Strong maximum principle for subharmonic functions** (Guo Lemma XI.1.5). A function `C²`
on a connected open set with nonnegative Laplacian that attains its supremum over the set at an
interior point is constant. -/
theorem strong_maximum_principle_subharmonic (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hsub : ∀ x ∈ U, 0 ≤ laplacianSum u x)
    {x₀ : EuclideanSpace ℝ (Fin d)} (hx₀ : x₀ ∈ U) (hmax : ∀ x ∈ U, u x ≤ u x₀) :
    ∀ x ∈ U, u x = u x₀ :=
  strong_maximum_principle hd hU hUc (a := fun _ => idCoeff) (b := fun _ _ => 0) (c := fun _ => 0)
    (A := 1) (B := 0) (C := 0) one_pos (fun _ _ => idCoeff_symm) (fun _ _ => idCoeff_ell)
    (fun _ _ => idCoeff_bdd) (fun _ _ _ => by simp) (fun _ _ => le_rfl) (fun _ _ => le_rfl) hu
    (fun x hx => by
      rw [nondivOp_laplace]
      linarith [hsub x hx])
    hx₀ hmax fun _ _ => by simp

/-- **Strong minimum principle for superharmonic functions** (Guo Corollary XI.1.6). A function
`C²` on a connected open set with nonpositive Laplacian that attains its infimum over the set at
an interior point is constant. -/
theorem strong_minimum_principle_superharmonic (hd : 0 < d)
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) (hUc : IsPreconnected U)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hsup : ∀ x ∈ U, laplacianSum u x ≤ 0)
    {x₀ : EuclideanSpace ℝ (Fin d)} (hx₀ : x₀ ∈ U) (hmin : ∀ x ∈ U, u x₀ ≤ u x) :
    ∀ x ∈ U, u x = u x₀ := by
  have h := strong_maximum_principle_subharmonic hd hU hUc hu.neg
    (fun x hx => by
      rw [laplacianSum_neg hU hu hx]
      linarith [hsup x hx])
    hx₀ (fun x hx => by linarith [hmin x hx])
  intro x hx
  linarith [h x hx]

/-- **Harmonic functions attaining their supremum are constant** (Guo Corollary XI.1.6). -/
theorem harmonic_const_of_max (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hharm : ∀ x ∈ U, laplacianSum u x = 0)
    {x₀ : EuclideanSpace ℝ (Fin d)} (hx₀ : x₀ ∈ U) (hmax : ∀ x ∈ U, u x ≤ u x₀) :
    ∀ x ∈ U, u x = u x₀ :=
  strong_maximum_principle_subharmonic hd hU hUc hu (fun x hx => (hharm x hx).ge) hx₀ hmax

/-- **Harmonic functions attaining their infimum are constant** (Guo Corollary XI.1.6). -/
theorem harmonic_const_of_min (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hharm : ∀ x ∈ U, laplacianSum u x = 0)
    {x₀ : EuclideanSpace ℝ (Fin d)} (hx₀ : x₀ ∈ U) (hmin : ∀ x ∈ U, u x₀ ≤ u x) :
    ∀ x ∈ U, u x = u x₀ :=
  strong_minimum_principle_superharmonic hd hU hUc hu (fun x hx => (hharm x hx).le) hx₀ hmin

/-- **Uniqueness for the Dirichlet problem for the Laplacian** (Guo Lemma XI.2.4, the uniqueness
clause). Two functions `C²` on a bounded open set and continuous on its closure, with the same
Laplacian on the set and the same boundary values, agree on the closure. -/
theorem dirichlet_unique_harmonic (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hL : ∀ x ∈ U, laplacianSum u x = laplacianSum v x)
    (hbd : ∀ x ∈ frontier U, u x = v x) : ∀ x ∈ closure U, u x = v x :=
  dirichlet_unique hd hU hUb hUne (a := fun _ => idCoeff) (b := fun _ _ => 0) (c := fun _ => 0)
    (B := 0) one_pos (fun _ _ => idCoeff_symm) (fun _ _ => idCoeff_ell) (fun _ _ _ => by simp)
    (fun _ _ => le_rfl) hu hv huc hvc
    (fun x hx => by rw [nondivOp_laplace, nondivOp_laplace, hL x hx]) hbd

end EllipticPdes.Classical
