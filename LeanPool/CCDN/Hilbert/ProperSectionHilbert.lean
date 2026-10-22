/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.FilteredHilbertPolynomial
import LeanPool.CCDN.ForMathlib.Polynomial
import LeanPool.CCDN.Hilbert.PolynomialComparison

/-! Hilbert inequalities for a proper polynomial section of a prime
affine variety. Multiplication by the section is injective in the original
coordinate domain and is killed in the section quotient. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem proper_section_filtered_hilbert_drop
    {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (f : MvPolynomial σ K) (hf : f ∉ I) (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace (I ⊔ Ideal.span {f}) (f.totalDegree + N)) +
      Module.finrank K (filteredCoordinateSpace I N) ≤
        Module.finrank K (filteredCoordinateSpace I (f.totalDegree + N)) := by
  classical
  let := Fintype.ofFinite σ
  let J := I ⊔ Ideal.span {f}
  let A := MvPolynomial σ K ⧸ I
  let q := Ideal.Quotient.mkₐ K I
  let ψ : A →ₐ[K] MvPolynomial σ K ⧸ J :=
    Ideal.Quotient.liftₐ I (Ideal.Quotient.mkₐ K J) (by
      intro g hg
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ((show I ≤ J from le_sup_left) hg))
  have hψ (g : MvPolynomial σ K) :
      ψ (q g) = Ideal.Quotient.mk J g := rfl
  let V := filteredCoordinateSpace I (f.totalDegree + N)
  let W := filteredCoordinateSpace I N
  let U := W.map (LinearMap.mulLeft K (q f))
  have hUV : U ≤ V := by
    rintro x hx
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hb
    refine Submodule.mem_map.mpr ⟨f * g, ?_, by simp [q]⟩
    rw [mem_restrictTotalDegree] at hg ⊢
    exact (totalDegree_mul _ _).trans (Nat.add_le_add_left hg _)
  have hUker : U ≤ ψ.toLinearMap.ker := by
    rintro x hx
    obtain ⟨b, _, rfl⟩ := Submodule.mem_map.mp hx
    apply LinearMap.mem_ker.mpr
    change ψ (q f * b) = 0
    rw [map_mul, hψ, Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show Ideal.span {f} ≤ J from le_sup_right) (Ideal.subset_span (by simp))), zero_mul]
  have hf0 : q f ≠ 0 :=
    fun h => hf (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hUdim : Module.finrank K U = Module.finrank K W :=
    (Submodule.equivMapOfInjective (LinearMap.mulLeft K (q f))
      (fun a b h => mul_left_cancel₀ hf0 h) W).finrank_eq.symm
  have hmap : V.map ψ.toLinearMap =
      filteredCoordinateSpace J (f.totalDegree + N) := by
    ext x
    constructor
    · rintro ⟨a, ⟨g, hg, rfl⟩, rfl⟩
      exact Submodule.mem_map.mpr ⟨g, hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact Submodule.mem_map.mpr ⟨q g, Submodule.mem_map.mpr ⟨g, hg, rfl⟩, rfl⟩
  have h := finrank_map_add_kernel_subspace_le ψ.toLinearMap V U hUV hUker
  rw [hmap, hUdim] at h
  exact h

/-- The Hilbert polynomial of the section is bounded by the finite
difference of the original Hilbert polynomial, with the necessary shift. -/
theorem proper_section_hilbert_polynomial_difference
    {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (f : MvPolynomial σ K) (hf : f ∉ I) :
    ∃ M : ℕ, ∀ N ≥ M,
      ((filteredHilbertPolynomial (I ⊔ Ideal.span {f})).comp
        (Polynomial.X + Polynomial.C (f.totalDegree : ℚ))).eval (N : ℚ) ≤
      ((filteredHilbertPolynomial I).comp
        (Polynomial.X + Polynomial.C (f.totalDegree : ℚ)) -
          filteredHilbertPolynomial I).eval (N : ℚ) := by
  obtain ⟨M, hM⟩ := filteredHilbertPolynomial_spec I
  obtain ⟨L, hL⟩ := filteredHilbertPolynomial_spec (I ⊔ Ideal.span {f})
  refine ⟨max M L, fun N hN => ?_⟩
  have hMN : M ≤ N := (le_max_left _ _).trans hN
  have hLN : L ≤ f.totalDegree + N := by
    have := (le_max_right M L).trans hN
    omega
  simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_sub]
  rw [show (N : ℚ) + f.totalDegree = ((f.totalDegree + N : ℕ) : ℚ) by push_cast; ring,
    hM _ (by omega), hM _ hMN, hL _ hLN]
  have h := proper_section_filtered_hilbert_drop I f hf N
  have hQ : (Module.finrank K
      (filteredCoordinateSpace (I ⊔ Ideal.span {f}) (f.totalDegree + N)) : ℚ) +
      Module.finrank K (filteredCoordinateSpace I N) ≤
        Module.finrank K (filteredCoordinateSpace I (f.totalDegree + N)) := by
    exact_mod_cast h
  linarith

/-- Every proper polynomial section lowers the affine Hilbert
dimension by at least one. In the maximal remaining dimension its leading
coefficient is at most the expected intersection degree. -/
theorem proper_section_hilbert_dimension_leadingCoeff
    {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (m : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (f : MvPolynomial σ K) (hf : f ∉ I) (hfdeg : 0 < f.totalDegree)
    (hsection : I ⊔ Ideal.span {f} ≠ ⊤) :
    (filteredHilbertPolynomial (I ⊔ Ideal.span {f})).natDegree ≤ m ∧
      ((filteredHilbertPolynomial (I ⊔ Ideal.span {f})).natDegree = m →
        (filteredHilbertPolynomial (I ⊔ Ideal.span {f})).leadingCoeff ≤
          (filteredHilbertPolynomial I).leadingCoeff * (m + 1) * f.totalDegree) := by
  let P := (filteredHilbertPolynomial (I ⊔ Ideal.span {f})).comp
    (Polynomial.X + Polynomial.C (f.totalDegree : ℚ))
  let Q := (filteredHilbertPolynomial I).comp
    (Polynomial.X + Polynomial.C (f.totalDegree : ℚ)) - filteredHilbertPolynomial I
  have hPdeg : P.natDegree =
      (filteredHilbertPolynomial (I ⊔ Ideal.span {f})).natDegree :=
    Polynomial.natDegree_taylor _ _
  have hPlc : P.leadingCoeff =
      (filteredHilbertPolynomial (I ⊔ Ideal.span {f})).leadingCoeff :=
    Polynomial.leadingCoeff_taylor _ _
  have hPpos : 0 < P.leadingCoeff := by
    rw [hPlc]
    exact filteredHilbertPolynomial_leadingCoeff_pos _ hsection
  have hs : (f.totalDegree : ℚ) ≠ 0 := by exact_mod_cast hfdeg.ne'
  have hQdeg :=
    Polynomial.natDegree_comp_X_add_C_sub_self (filteredHilbertPolynomial I) hdim _ hs
  have hQlc :=
    Polynomial.leadingCoeff_comp_X_add_C_sub_self (filteredHilbertPolynomial I) hdim _ hs
  have hQpos : 0 < Q.leadingCoeff := by
    rw [show Q.leadingCoeff = _ from hQlc]
    exact mul_pos (mul_pos
      (filteredHilbertPolynomial_leadingCoeff_pos I (Ideal.IsPrime.ne_top ‹I.IsPrime›))
      (by positivity))
      (by exact_mod_cast hfdeg)
  have hle := proper_section_hilbert_polynomial_difference I f hf
  constructor
  · have h := polynomial_natDegree_le_of_eventual_nat_eval_le P Q hPpos hle
    simpa only [hPdeg, show Q.natDegree = m from hQdeg] using h
  · intro hdimsection
    have h := polynomial_leadingCoeff_le_of_eventual_nat_eval_le P Q hPpos hQpos
      (by rw [hPdeg, hdimsection]; exact hQdeg.symm) hle
    simpa only [hPlc, show Q.leadingCoeff = _ from hQlc] using h

end
end CCDN
