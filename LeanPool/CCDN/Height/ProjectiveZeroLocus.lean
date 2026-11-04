/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Height.ProjectivePrimitive
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Homogeneous zero loci on rational projective space and their integer
representatives. Membership is independent of the representative. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Evaluating a homogeneous polynomial of degree `d` at `a • v` multiplies its value at `v` by
`a ^ d`. -/
lemma homogeneous_eval_smul {K σ : Type*} [CommSemiring K]
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d)
    (a : K) (v : σ → K) :
    eval (a • v) f = a ^ d * eval v f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  simp only [map_sum, eval_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hd : m.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (mem_support_iff.mp hm)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finsupp.prod, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  change f.coeff m * (a ^ m.degree * _) = _
  rw [hd]
  ring

/-- Over a field, a homogeneous polynomial vanishes at `a • v`, for `a ≠ 0`, exactly when it
vanishes at `v`. -/
lemma homogeneous_eval_zero_iff_smul {K σ : Type*} [Field K]
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d)
    {a : K} (ha : a ≠ 0) (v : σ → K) :
    eval (a • v) f = 0 ↔ eval v f = 0 := by
  rw [homogeneous_eval_smul hf, mul_eq_zero]
  simp [pow_ne_zero _ ha]

/-- A homogeneous polynomial vanishes at one nonzero vector exactly when it vanishes at any other
nonzero vector spanning the same projective point. -/
lemma homogeneous_eval_zero_iff_projective_eq {K : Type*} [Field K] {n d : ℕ}
    {f : MvPolynomial (Fin (n + 1)) K} (hf : f.IsHomogeneous d)
    {v w : Fin (n + 1) → K} (hv : v ≠ 0) (hw : w ≠ 0)
    (he : Projectivization.mk K v hv = Projectivization.mk K w hw) :
    eval v f = 0 ↔ eval w f = 0 := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K v w hv hw).mp he
  rw [← ha]
  exact homogeneous_eval_zero_iff_smul hf a.ne_zero w

/-- The projective points whose chosen representative is a zero of `f`; for homogeneous `f`
this is the projective zero locus of `f`, independent of the representative. -/
def projectiveZeroLocus {K : Type*} [Field K] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) K) :
    Set (Projectivization K (Fin (n + 1) → K)) :=
  {x | eval x.rep f = 0}

/-- For homogeneous `f`, the projective point spanned by a nonzero vector `v` lies in the
projective zero locus of `f` exactly when `f` vanishes at `v`. -/
lemma mem_projectiveZeroLocus_mk {K : Type*} [Field K] {n d : ℕ}
    {f : MvPolynomial (Fin (n + 1)) K} (hf : f.IsHomogeneous d)
    (v : Fin (n + 1) → K) (hv : v ≠ 0) :
    Projectivization.mk K v hv ∈ projectiveZeroLocus f ↔ eval v f = 0 := by
  exact homogeneous_eval_zero_iff_projective_eq hf
    (Projectivization.mk K v hv).rep_nonzero hv
    (Projectivization.mk K v hv).mk_rep

/-- For homogeneous rational `f`, a rational projective point lies in the zero locus of `f` exactly
when `f` vanishes at its primitive integer representative. -/
lemma mem_projectiveZeroLocus_primitive {n d : ℕ}
    {f : MvPolynomial (Fin (n + 1)) ℚ} (hf : f.IsHomogeneous d)
    (x : ProjectivePoint n) :
    x ∈ projectiveZeroLocus f ↔ eval (rationalPoint (primitiveProjectiveRep x)) f = 0 := by
  have h := mem_projectiveZeroLocus_mk hf
    (rationalPoint (primitiveProjectiveRep x))
    (rationalPoint_ne_zero (primitiveProjectiveRep_ne_zero x))
  rwa [primitiveProjectiveRep_mk] at h

/-- For a homogeneous integer polynomial `f`, a rational projective point lies in the projective
zero locus of `f` (viewed over `ℚ`) exactly when `f` vanishes at the point's primitive integer
representative. -/
lemma mem_integer_projectiveZeroLocus {n d : ℕ}
    {f : MvPolynomial (Fin (n + 1)) ℤ} (hf : f.IsHomogeneous d)
    (x : ProjectivePoint n) :
    x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) f) ↔
      eval (primitiveProjectiveRep x) f = 0 := by
  rw [mem_projectiveZeroLocus_primitive (hf.map _)]
  change eval ((Int.castRingHom ℚ) ∘ primitiveProjectiveRep x)
    (map (Int.castRingHom ℚ) f) = 0 ↔ _
  rw [← map_eval]
  exact Int.cast_eq_zero

/-- Reduce a projective count to a finite family of bounded primitive
integer vectors representing distinct projective points. -/
theorem projective_zero_count_le_of_family_bound {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d)
    (B R : ℝ)
    (hbound : ∀ (t : ℕ) (z : Fin t → IntPoint (n + 1))
      (hz : ∀ i, z i ≠ 0),
      Function.Injective (fun i => Projectivization.mk ℚ (rationalPoint (z i))
        (rationalPoint_ne_zero (hz i))) →
      (∀ i, Finset.univ.gcd (z i) = 1) →
      (∀ i, eval (z i) f = 0) →
      (∀ i, InBox (z i) B) → (t : ℝ) ≤ R) :
    (projectiveCount (projectiveZeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤ R := by
  classical
  let S := projectivePoints (projectiveZeroLocus (map (Int.castRingHom ℚ) f)) B
  let e := (Fintype.equivFin S).symm
  let z : Fin (Fintype.card S) → IntPoint (n + 1) :=
    fun i => primitiveProjectiveRep (e i).val
  have hz (i) : z i ≠ 0 := primitiveProjectiveRep_ne_zero _
  have he (i) : Projectivization.mk ℚ (rationalPoint (z i))
      (rationalPoint_ne_zero (hz i)) = (e i).val := primitiveProjectiveRep_mk _
  have hinj : Function.Injective (fun i => Projectivization.mk ℚ (rationalPoint (z i))
      (rationalPoint_ne_zero (hz i))) := by
    simp_rw [he]
    exact Subtype.val_injective.comp e.injective
  have hprim (i) : Finset.univ.gcd (z i) = 1 := primitiveProjectiveRep_gcd _
  have hzero (i) : eval (z i) f = 0 :=
    (mem_integer_projectiveZeroLocus hf _).mp (mem_projectivePoints.mp (e i).property).2
  have hbox (i j) : |(z i j : ℝ)| ≤ B :=
    (primitiveProjectiveRep_bound _ j).trans (mem_projectivePoints.mp (e i).property).1
  have h := hbound _ z hz hinj hprim hzero hbox
  simpa only [Fintype.card_coe, S, projectiveCount] using h

end
end CCDN
