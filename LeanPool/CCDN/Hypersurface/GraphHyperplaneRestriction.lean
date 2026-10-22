/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Plane.SectionBounds
import LeanPool.CCDN.Determinant.PlaneMultiplicity
import LeanPool.CCDN.Plane.FullDegreeSectionIrreducibility
import Mathlib.Algebra.MvPolynomial.Funext

/-! A hyperplane written as x₀ = ∑ aᵢxᵢ. A full-degree
irreducible plane contained in that hyperplane certifies irreducibility
of the entire hyperplane restriction. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The restriction of a polynomial in the coordinates `x_none` and `x i` to the hyperplane
`x_none = ∑ a i * x i`, as a polynomial in the remaining coordinates `x i`. -/
def graphHyperplaneRestriction {K σ : Type*} [CommRing K] [Fintype σ]
    (a : σ → K) : MvPolynomial (Option σ) K →ₐ[K] MvPolynomial σ K :=
  aeval (fun i => Option.elim i (∑ j, C (a j) * X j) X)

/-- Restriction to a graph hyperplane does not increase the total degree. -/
lemma graphHyperplaneRestriction_totalDegree_le {K σ : Type*}
    [Field K] [Fintype σ] (a : σ → K) (f : MvPolynomial (Option σ) K) :
    (graphHyperplaneRestriction a f).totalDegree ≤ f.totalDegree := by
  apply linear_eval₂_totalDegree_le
  intro i
  cases i with
  | none =>
    apply totalDegree_finsetSum_le
    intro j _
    exact (totalDegree_mul _ _).trans (by simp)
  | some j => simp

/-- Evaluating the restriction of `f` to the hyperplane `x_none = ∑ a j * x j` at `x` is
evaluating `f` at the point of the hyperplane lying over `x`. -/
lemma graphHyperplaneRestriction_eval {K σ : Type*} [CommRing K] [Fintype σ]
    (a x : σ → K) (f : MvPolynomial (Option σ) K) :
    eval x (graphHyperplaneRestriction a f) =
      eval (fun i => Option.elim i (∑ j, a j * x j) x) f := by
  have he : (eval x).comp (graphHyperplaneRestriction a).toRingHom =
      eval (fun i => Option.elim i (∑ j, a j * x j) x) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [graphHyperplaneRestriction]
    · intro i
      cases i <;> simp [graphHyperplaneRestriction]
  exact RingHom.congr_fun he f

/-- Restriction to a graph hyperplane preserves homogeneity of degree `d`. -/
lemma graphHyperplaneRestriction_homogeneous {K σ : Type*}
    [CommRing K] [Fintype σ] (a : σ → K) {f : MvPolynomial (Option σ) K} {d : ℕ}
    (hf : f.IsHomogeneous d) : (graphHyperplaneRestriction a f).IsHomogeneous d := by
  let v : Option σ → MvPolynomial σ K :=
    fun i => Option.elim i (∑ j, C (a j) * X j) X
  have hv : ∀ i, (v i).IsHomogeneous 1 := by
    intro i
    cases i with
    | none =>
      exact IsHomogeneous.sum _ _ _ (fun j _ => (isHomogeneous_X K j).C_mul (a j))
    | some j => exact isHomogeneous_X K j
  simpa only [one_mul, v, graphHyperplaneRestriction] using hf.aeval v hv

/-- Restriction to the graph hyperplane commutes with applying a ring homomorphism `φ` to the
coefficients, the hyperplane coefficients `a` being mapped by `φ` as well. -/
lemma graphHyperplaneRestriction_map {K L σ : Type*}
    [CommRing K] [CommRing L] [Fintype σ]
    (φ : K →+* L) (a : σ → K) (f : MvPolynomial (Option σ) K) :
    map φ (graphHyperplaneRestriction a f) =
      graphHyperplaneRestriction (φ ∘ a) (map φ f) := by
  have he : (map φ).comp (graphHyperplaneRestriction a).toRingHom =
      (graphHyperplaneRestriction (φ ∘ a)).toRingHom.comp (map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [graphHyperplaneRestriction]
    · intro i
      cases i <;> simp [graphHyperplaneRestriction]
  exact RingHom.congr_fun he f

/-- Restriction to a graph hyperplane commutes with taking the homogeneous component of
degree `d`. -/
lemma graphHyperplaneRestriction_homogeneousComponent {K σ : Type*}
    [CommRing K] [Fintype σ] (a : σ → K)
    (f : MvPolynomial (Option σ) K) (d : ℕ) :
    graphHyperplaneRestriction a (homogeneousComponent d f) =
      homogeneousComponent d (graphHyperplaneRestriction a f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
    have hm := isHomogeneous_monomial c (rfl : m.degree = m.degree)
    rw [homogeneousComponent_of_mem hm,
      homogeneousComponent_of_mem (graphHyperplaneRestriction_homogeneous a hm)]
    split_ifs <;> simp
  | add f g hf hg => simp only [map_add, hf, hg]

private lemma planeSectionPolynomial_eval {K σ : Type*} [CommRing K]
    (f : MvPolynomial σ K) (v : PlaneParameters σ → K) (t : Fin 2 → K) :
    eval t (planeSectionPolynomial f v) =
      eval (fun i => v (i, 0) + v (i, 1) * t 0 + v (i, 2) * t 1) f := by
  rw [← bivariateEval_equiv, planeSectionPolynomial, AlgEquiv.apply_symm_apply]
  exact universalPlaneSection_eval f v (t 0) (t 1)

private lemma graphHyperplaneRestriction_planeSection {K σ : Type*}
    [Field K] [Infinite K] [Fintype σ]
    (a : σ → K) (v : PlaneParameters (Option σ) → K)
    (hv : ∀ j : Fin 3, v (none, j) = ∑ i, a i * v (some i, j))
    (f : MvPolynomial (Option σ) K) :
    planeSectionPolynomial (graphHyperplaneRestriction a f) (fun p => v (some p.1, p.2)) =
      planeSectionPolynomial f v := by
  apply MvPolynomial.funext
  intro t
  rw [planeSectionPolynomial_eval, graphHyperplaneRestriction_eval, planeSectionPolynomial_eval]
  apply congrArg (fun z : Option σ → K => eval z f)
  funext i
  cases i with
  | none => simp [hv, mul_add, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]
  | some i => rfl

/-- Full degree and irreducibility of a concrete contained plane force both
properties for the containing hyperplane. -/
theorem graphHyperplaneRestriction_irreducible_of_plane
    {K σ : Type*} [Field K] [Infinite K] [Fintype σ]
    (f : MvPolynomial (Option σ) K) (a : σ → K)
    (v : PlaneParameters (Option σ) → K)
    (hv : ∀ j : Fin 3, v (none, j) = ∑ i, a i * v (some i, j))
    (hir : Irreducible (universalPlaneSection f v))
    (hdegree : bivariateTotalDegree (universalPlaneSection f v) = f.totalDegree) :
    (graphHyperplaneRestriction a f).totalDegree = f.totalDegree ∧
      Irreducible (graphHyperplaneRestriction a f) := by
  let w : PlaneParameters σ → K := fun p => v (some p.1, p.2)
  have he := graphHyperplaneRestriction_planeSection a v hv f
  have hfull : (graphHyperplaneRestriction a f).totalDegree = f.totalDegree := by
    apply le_antisymm (graphHyperplaneRestriction_totalDegree_le a f)
    have hh := planeSectionPolynomial_totalDegree (graphHyperplaneRestriction a f) w
    rw [show w = (fun p => v (some p.1, p.2)) from rfl, he] at hh
    exact hdegree ▸ hh
  refine ⟨hfull, ?_⟩
  apply irreducible_of_full_degree_map (planeSectionPolynomialHom w)
    (fun g => planeSectionPolynomial_totalDegree g w)
  · change Irreducible (planeSectionPolynomial (graphHyperplaneRestriction a f) w)
    rw [show w = (fun p => v (some p.1, p.2)) from rfl, he]
    exact (MulEquiv.irreducible_iff (f := (bivariatePolynomialEquiv K).symm)).mpr hir
  · change (planeSectionPolynomial (graphHyperplaneRestriction a f) w).totalDegree =
      (graphHyperplaneRestriction a f).totalDegree
    rw [show w = (fun p => v (some p.1, p.2)) from rfl, he, hfull]
    exact hdegree

end
end CCDN
