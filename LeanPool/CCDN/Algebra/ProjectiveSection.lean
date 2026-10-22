/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.IdealZeroLocus
public import LeanPool.CCDN.Algebra.PolynomialPredicates
public import LeanPool.CCDN.Hilbert.HomogeneousHilbert
public import Mathlib.LinearAlgebra.Projectivization.Basic
import LeanPool.CCDN.Height.ProjectivePointSeparation
import LeanPool.CCDN.Height.ProjectiveZeroLocus
import LeanPool.CCDN.Hilbert.FilteredIntersection

/-! Proper homogeneous sections of projective curves. The degree is the
slope of the graded Hilbert function. Homogeneous interpolation and
injective multiplication in the coordinate domain prove the section bound. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
variable {K : Type*} [Field K]

instance homogeneousCoordinateSpace_finite {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (M : ℕ) :
    Module.Finite K (homogeneousCoordinateSpace I M) := by
  exact Module.Finite.of_fg
    ((homogeneousSubmodule_fg _ _ _).map (Ideal.Quotient.mkₐ K I).toLinearMap)

/-- The graded Hilbert function of `I`: the dimension of the degree-`M` part of the coordinate
ring `MvPolynomial (Fin (n + 1)) K ⧸ I`, that is, of the image of the homogeneous polynomials
of degree `M`. -/
def projectiveHilbertFunction {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (M : ℕ) : ℕ := Module.finrank K (homogeneousCoordinateSpace I M)

/-- The ideal `I` has projective curve degree `d`: the graded Hilbert function of
`MvPolynomial (Fin (n + 1)) K ⧸ I` eventually equals `d * M + c` for some constant `c`. For a
homogeneous prime ideal of a projective curve, `d` is the usual degree. -/
def HasProjectiveCurveDegree {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (d : ℕ) : Prop :=
  ∃ N : ℕ, ∃ c : ℤ, ∀ M : ℕ, N ≤ M →
    (projectiveHilbertFunction I M : ℤ) = (d : ℤ) * M + c

/-- A projective point belongs to the zero locus when every representative
annihilates the ideal. For homogeneous ideals this is the usual projective zero locus. -/
def projectiveIdealZeroLocus {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) K)) :
    Set (Projectivization K (Fin (n + 1) → K)) :=
  {x | ∀ (v : Fin (n + 1) → K) (hv : v ≠ 0),
    Projectivization.mk K v hv = x → v ∈ idealZeroLocus I}

/-- The chosen representative of a point of the projective zero locus of `I` lies in the affine
zero locus of `I`. -/
lemma projectiveIdealZeroLocus_rep {n : ℕ}
    {I : Ideal (MvPolynomial (Fin (n + 1)) K)} {x : Projectivization K (Fin (n + 1) → K)}
    (hx : x ∈ projectiveIdealZeroLocus I) :
    x.rep ∈ idealZeroLocus I :=
  hx x.rep x.rep_nonzero x.mk_rep

private lemma homogeneousCoordinateSpace_mul_mem {n M m : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    {f : MvPolynomial (Fin (n + 1)) K} (hf : f.IsHomogeneous m)
    {a : MvPolynomial (Fin (n + 1)) K ⧸ I}
    (ha : a ∈ homogeneousCoordinateSpace I M) :
    (Ideal.Quotient.mk I) f * a ∈ homogeneousCoordinateSpace I (m + M) := by
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp ha
  exact Submodule.mem_map.mpr ⟨f * g, hf.mul hg, by simp⟩

/-- Distinct points on a proper homogeneous section force a drop in the graded
Hilbert function at least as large as their number. -/
private theorem projective_section_hilbert_drop {n m M : ℕ} {ι : Type*}
    [Fintype ι]
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous m) (hfI : f ∉ I)
    (z : ι → Projectivization K (Fin (n + 1) → K)) (hz : Function.Injective z)
    (hzI : ∀ i, z i ∈ projectiveIdealZeroLocus I)
    (hzf : ∀ i, eval (z i).rep f = 0) (hM : Fintype.card ι - 1 ≤ m + M) :
    Fintype.card ι + projectiveHilbertFunction I M ≤ projectiveHilbertFunction I (m + M) := by
  classical
  let A := MvPolynomial (Fin (n + 1)) K ⧸ I
  let q := Ideal.Quotient.mkₐ K I
  let ψ : ι → A →ₐ[K] K := fun i =>
    Ideal.Quotient.liftₐ I (aeval (z i).rep) (by
      intro g hg
      simpa only [aeval_eq_eval] using projectiveIdealZeroLocus_rep (hzI i) g hg)
  have hψ (i : ι) (g : MvPolynomial (Fin (n + 1)) K) :
      ψ i (q g) = eval (z i).rep g := by
    rfl
  let φ : A →ₗ[K] (ι → K) := LinearMap.pi fun i => (ψ i).toLinearMap
  let V := homogeneousCoordinateSpace I (m + M)
  let W := homogeneousCoordinateSpace I M
  let U := W.map (LinearMap.mulLeft K (q f))
  have hUV : U ≤ V := by
    rintro a ha
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp ha
    exact homogeneousCoordinateSpace_mul_mem I hf hb
  have hUker : U ≤ φ.ker := by
    rintro a ha
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp ha
    apply LinearMap.mem_ker.mpr
    ext i
    change ψ i (q f * b) = 0
    rw [map_mul, hψ, hzf, zero_mul]
  have hf0 : q f ≠ 0 := by
    exact fun he => hfI (Ideal.Quotient.eq_zero_iff_mem.mp he)
  have hUdim : Module.finrank K U = projectiveHilbertFunction I M :=
    (Submodule.equivMapOfInjective (LinearMap.mulLeft K (q f))
      (fun a b h => mul_left_cancel₀ hf0 h) W).finrank_eq.symm
  obtain ⟨h, hhom, heval⟩ := exists_projective_point_separators_degree z hz hM
  have htop : V.map φ = ⊤ := by
    apply top_unique
    intro w _
    apply Submodule.mem_map.mpr
    refine ⟨∑ j, w j • q (h j), ?_, ?_⟩
    · apply Submodule.sum_mem
      intro j _
      apply Submodule.smul_mem
      exact Submodule.mem_map.mpr ⟨h j, hhom j, rfl⟩
    · ext i
      change ψ i (∑ j, w j • q (h j)) = w i
      simp [hψ, heval]
  have h := finrank_map_add_kernel_subspace_le φ V U hUV hUker
  rw [htop, finrank_top, Module.finrank_pi, hUdim] at h
  exact h

/-- A proper section of degree `m` meets a degree-`d` projective prime curve
in at most `dm` distinct points over the base field. -/
theorem projective_section_card_le_degree {n d m : ℕ} {ι : Type*}
    [Fintype ι]
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (hdegree : HasProjectiveCurveDegree I d)
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous m) (hfI : f ∉ I)
    (z : ι → Projectivization K (Fin (n + 1) → K)) (hz : Function.Injective z)
    (hzI : ∀ i, z i ∈ projectiveIdealZeroLocus I)
    (hzf : ∀ i, eval (z i).rep f = 0) :
    Fintype.card ι ≤ d * m := by
  classical
  obtain ⟨N, c, hN⟩ := hdegree
  let M := max N (Fintype.card ι)
  have hlow := projective_section_hilbert_drop I f hf hfI z hz hzI hzf
    (show Fintype.card ι - 1 ≤ m + M by dsimp [M]; omega)
  have h0 := hN M (le_max_left _ _)
  have h1 := hN (m + M) (by dsimp [M]; omega)
  have hlowZ : (Fintype.card ι : ℤ) + projectiveHilbertFunction I M ≤
      projectiveHilbertFunction I (m + M) := by exact_mod_cast hlow
  rw [h0, h1] at hlowZ
  push_cast at hlowZ
  have hcard : (Fintype.card ι : ℤ) ≤ (d : ℤ) * m := by linarith
  exact_mod_cast hcard

/-- A point of the zero locus of a homogeneous ideal stays in it after scaling. -/
lemma homogeneous_ideal_eval_smul
    {K σ : Type*} [Field K] (I : Ideal (MvPolynomial σ K))
    (hI : IsHomogeneousIdeal I)
    (v : σ → K) (hv : v ∈ idealZeroLocus I)
    (a : K) (f : MvPolynomial σ K) (hf : f ∈ I) :
    eval (a • v) f = 0 := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent f]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro N _
  rw [homogeneous_eval_smul (homogeneousComponent_isHomogeneous _ _),
    hv _ (hI f hf N), mul_zero]

end
end CCDN
