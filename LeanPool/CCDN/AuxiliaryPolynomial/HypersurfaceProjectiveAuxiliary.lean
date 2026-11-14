/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.AuxiliaryPolynomial.AbsoluteAuxiliary

/-! A single auxiliary polynomial for all rational points of bounded projective
height, with no finite-family hypothesis. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The rational points of height at most `B` on the zero locus of `f`, as a finite family
of bounded primitive integer zeros. A form vanishing on the family vanishes at every such
point. -/
lemma exists_bounded_projective_zero_family {n d : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : f.IsHomogeneous d) (B : ℝ) :
    ∃ (t : ℕ) (z : Fin t → IntPoint (n + 1)), (∀ i, Finset.univ.gcd (z i) = 1) ∧
      (∀ i, eval (z i) f = 0) ∧ (∀ i, InBox (z i) B) ∧
      ∀ {M : ℕ} (g : MvPolynomial (Fin (n + 1)) ℤ), g.IsHomogeneous M →
        (∀ i, eval (z i) g = 0) → ∀ x : ProjectivePoint n, x.mulHeight ≤ B →
          x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) f) →
          x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) g) := by
  classical
  let S := projectivePoints (projectiveZeroLocus (map (Int.castRingHom ℚ) f)) B
  let e := (Fintype.equivFin S).symm
  refine ⟨Fintype.card S, fun i => primitiveProjectiveRep (e i).val,
    fun i => primitiveProjectiveRep_gcd _,
    fun i => (mem_integer_projectiveZeroLocus hf _).mp (mem_projectivePoints.mp (e i).property).2,
    fun i j => (primitiveProjectiveRep_bound _ j).trans
      (mem_projectivePoints.mp (e i).property).1, ?_⟩
  intro M g hgh hgz x hxB hxf
  obtain ⟨i, hi⟩ := e.surjective ⟨x, mem_projectivePoints.mpr ⟨hxB, hxf⟩⟩
  have hh : eval (primitiveProjectiveRep (e i).val) g = 0 := hgz i
  rw [hi] at hh
  exact (mem_integer_projectiveZeroLocus hgh x).mpr hh

/-- The full projective-height formulation of the absolutely irreducible
case of CCDN Theorem 3.1.1. -/
theorem hypersurface_absolute_projective_auxiliary
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n d : ℕ}
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom K) f))
    {B : ℝ} (hB : 1 ≤ B) :
    ∃ (bad : Finset ℕ) (M : ℕ),
      (∀ p, p ∈ bad ↔ stepanovThreshold d < p ∧ HypersurfaceBadReduction f p) ∧
      (M : ℝ) ≤ hypersurfaceAuxiliaryDegreeBound n d B (primeSetFactor bad)
        (integerCoefficientHeight f) ∧
      ∃ g : MvPolynomial (Fin (n + 3)) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
        (∀ x : ProjectivePoint (n + 2), x.mulHeight ≤ B →
          x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) f) →
          x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) g)) ∧ ¬ f ∣ g := by
  obtain ⟨t, z, hprim, hzero, hbox, hlift⟩ := exists_bounded_projective_zero_family f hf B
  obtain ⟨bad, M, hbad, hdegree, g, hg0, hgh, hgz, hgnd⟩ :=
    hypersurface_absolute_auxiliary_degree f hf hd hir z hprim hzero hB hbox
  exact ⟨bad, M, hbad, hdegree, g, hg0, hgh, hlift g hgh hgz, hgnd⟩

end
end CCDN
