/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Noether.UniversalPlaneWitness
import LeanPool.CCDN.AuxiliaryPolynomial.ConstantLeadingBadReduction
import LeanPool.CCDN.Determinant.ClosedFormIntegerMinor
import LeanPool.CCDN.Determinant.PlaneMultiplicity
import LeanPool.CCDN.Determinant.UniversalPlaneMinor
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Noether.ClosedFormParameterDegree
import LeanPool.CCDN.Noether.ClosedFormScaling

/-! A nonzero polynomial of degree at most 2*d^3 detects all plane sections
that lose the full degree or fail geometric irreducibility. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The universal plane restriction of `f` has total degree at most the total degree of `f` in the
two plane coordinates. -/
lemma universalPlaneMap_planeDegree_le {K σ : Type*} [CommRing K]
    (f : MvPolynomial σ K) : (universalPlaneMap K σ f).totalDegree ≤ f.totalDegree := by
  change (eval₂Hom (C.comp (C : K →+* MvPolynomial (PlaneParameters σ) K))
    (fun i => C (X (i,0)) + C (X (i,1)) * X 0 + C (X (i,2)) * X 1) f).totalDegree ≤ _
  apply linear_eval₂_totalDegree_le
  intro i
  have hx (j : Fin 2) :
      (X j : MvPolynomial (Fin 2) (MvPolynomial (PlaneParameters σ) K)).totalDegree ≤ 1 := by
    simpa [X] using
      totalDegree_monomial_le (Finsupp.single j 1) (1 : MvPolynomial (PlaneParameters σ) K)
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · simp
    · exact (totalDegree_mul _ _).trans (by simpa using hx 0)
  · exact (totalDegree_mul _ _).trans (by simpa using hx 1)

/-- Every specialization of the plane parameters of the universal plane restriction of `f` has
total degree at most the total degree of `f`. -/
lemma universalPlanePolynomial_specialization_totalDegree {K L σ : Type*}
    [CommRing K] [CommRing L] (f : MvPolynomial σ K)
    (φ : MvPolynomial (PlaneParameters σ) K →+* L) :
    bivariateTotalDegree (bivariateMap φ (universalPlanePolynomial f)) ≤ f.totalDegree := by
  apply (bivariateTotalDegree_map_le φ _).trans
  simpa only [universalPlanePolynomial, bivariateTotalDegree, AlgEquiv.symm_apply_apply]
    using universalPlaneMap_planeDegree_le f

/-- The bad-plane witness: the universal outer leading coefficient of the plane restriction of
`f` times the closed-form minor with rows `rows` and columns `cols`. The leading-coefficient
factor detects all outer-degree drops. -/
def universalPlaneBadWitness {K σ : Type*} [CommRing K] (f : MvPolynomial σ K)
    (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree) :
    MvPolynomial (PlaneParameters σ) K :=
  universalPlaneLeading f *
    ((closedFormCoefficientMatrix f.totalDegree (universalPlanePolynomial f)).submatrix
      rows cols).det

private lemma universalPlaneBadWitness_degree {K σ : Type*} [CommRing K] (f : MvPolynomial σ K)
    (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree) :
    (universalPlaneBadWitness f rows cols).totalDegree ≤ 2 * f.totalDegree ^ 3 := by
  apply (totalDegree_mul _ _).trans
  have hl := universalPlanePolynomial_coefficient_degree f f.totalDegree 0
  have hm := closedForm_minor_parameterDegree _ _ _ _
    (universalPlanePolynomial_coefficient_degree f) rows cols
  change (universalPlaneLeading f).totalDegree ≤ f.totalDegree at hl
  calc
    _ ≤ f.totalDegree + (2 * f.totalDegree ^ 2 - 1) * f.totalDegree := Nat.add_le_add hl hm
    _ ≤ 2 * f.totalDegree ^ 3 := by
      by_cases h : f.totalDegree = 0
      · simp [h]
      · have h1 : 1 ≤ 2 * f.totalDegree ^ 2 := by
          have : 0 < f.totalDegree := Nat.pos_of_ne_zero h; nlinarith
        have he := Nat.sub_add_cancel h1
        nlinarith

/-- Nonvanishing certifies full degree and irreducibility over ANY target
field of characteristic zero or greater than d. In particular it applies in the
algebraic closure when detecting geometrically bad finite-field planes. -/
theorem universalPlaneBadWitness_good_specialization
    {K L σ : Type*} [CommRing K] [Field L]
    (f : MvPolynomial σ K) (hpos : 0 < f.totalDegree) (hchar : CharZeroOrGT L f.totalDegree)
    (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree)
    (φ : MvPolynomial (PlaneParameters σ) K →+* L)
    (hw : φ (universalPlaneBadWitness f rows cols) ≠ 0) :
    (bivariateMap φ (universalPlanePolynomial f)).natDegree = f.totalDegree ∧
      bivariateTotalDegree (bivariateMap φ (universalPlanePolynomial f)) = f.totalDegree ∧
      Irreducible (bivariateMap φ (universalPlanePolynomial f)) := by
  let g := bivariateMap φ (universalPlanePolynomial f)
  have hh := mul_ne_zero_iff.mp (show φ (universalPlaneLeading f) *
      φ (((closedFormCoefficientMatrix f.totalDegree (universalPlanePolynomial f)).submatrix
        rows cols).det) ≠ 0
      by simpa only [universalPlaneBadWitness, map_mul] using hw)
  have ht : bivariateTotalDegree g ≤ f.totalDegree :=
    universalPlanePolynomial_specialization_totalDegree f φ
  have hc : ((g.coeff f.totalDegree).coeff 0) ≠ 0 := by
    simpa only [g, bivariateMap_coeff, universalPlaneLeading] using hh.1
  have hd : g.natDegree = f.totalDegree := by
    apply le_antisymm ((bivariate_natDegree_le_totalDegree g).trans ht)
    apply Polynomial.le_natDegree_of_ne_zero
    intro hz
    exact hc (by rw [hz, Polynomial.coeff_zero])
  have he : bivariateTotalDegree g = f.totalDegree :=
    le_antisymm ht (hd ▸ bivariate_natDegree_le_totalDegree g)
  refine ⟨hd, he, ?_⟩
  by_contra hred
  have hl : g.leadingCoeff = Polynomial.C (φ (universalPlaneLeading f)) := by
    rw [bivariate_leadingCoeff_eq_constant g (by omega)]
    congr 1
    change (g.coeff g.natDegree).coeff 0 = _
    rw [hd]
    exact bivariateMap_coeff φ _ _ _
  have hr := closedForm_rank_drop_of_constant_leading f.totalDegree hpos hchar
    _ hh.1 g hl hred hd ht
  have hdet : ((closedFormCoefficientMatrix f.totalDegree g).submatrix rows cols).det ≠ 0 := by
    rw [← closedForm_minor_map]
    exact hh.2
  have hrank := Matrix.le_rank_of_det_submatrix_ne_zero _ rows cols hdet
  omega

/-- A concrete cubic-degree bad-section witness over the original field. -/
theorem exists_universalPlane_badWitness
    {K σ : Type*} [Field K] [Finite σ]
    (f : MvPolynomial (Option σ) K)
    (hf : Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpos : 0 < f.totalDegree) (hchar : CharZeroOrGT K (2 * f.totalDegree ^ 2)) :
    ∃ (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
      (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree),
      universalPlaneBadWitness f rows cols ≠ 0 ∧
      (universalPlaneBadWitness f rows cols).totalDegree ≤ 2 * f.totalDegree ^ 3 := by
  classical
  let := Fintype.ofFinite σ
  obtain ⟨rows, cols, hdet, _⟩ := exists_universalPlane_minor_degree f hf hpos hchar
  exact ⟨rows, cols,
    mul_ne_zero (universalPlaneLeading_ne_zero f hf hpos
      (hchar.mono (by nlinarith [Nat.le_mul_self f.totalDegree]))) hdet,
    universalPlaneBadWitness_degree f rows cols⟩

/-- A nonzero integer polynomial in the full parameter space,
constructed for every geometrically irreducible integer equation. -/
theorem exists_integer_universalPlane_badWitness
    {L σ : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Finite σ]
    (f : MvPolynomial (Option σ) ℤ)
    (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f))
    (hpos : 0 < f.totalDegree) :
    ∃ (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
      (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree),
      universalPlaneBadWitness f rows cols ≠ 0 ∧
      (universalPlaneBadWitness f rows cols).totalDegree ≤ 2 * f.totalDegree ^ 3 := by
  classical
  let := Fintype.ofFinite σ
  let φ : ℤ →+* L := Int.castRingHom L
  have ht : (MvPolynomial.map φ f).totalDegree = f.totalDegree :=
    totalDegree_map_of_injective (RingHom.injective_int _) f
  have hex := exists_universalPlane_minor (MvPolynomial.map φ f) hf (ht ▸ hpos)
    (.of_charZero _)
  rw [ht] at hex
  obtain ⟨rows, cols, hdet⟩ := hex
  have hm : ((closedFormCoefficientMatrix f.totalDegree
      (universalPlanePolynomial f)).submatrix rows cols).det ≠ 0 := by
    intro he
    rw [universalPlanePolynomial_map, ← closedForm_minor_map, he, map_zero] at hdet
    exact hdet rfl
  have hl : universalPlaneLeading f ≠ 0 := by
    have hn := universalPlaneLeading_ne_zero_of_irreducible (MvPolynomial.map φ f) hf
      (ht ▸ hpos) (.of_charZero _)
    have he : universalPlaneLeading (MvPolynomial.map φ f) =
        MvPolynomial.map φ (universalPlaneLeading f) := by
      simp only [universalPlaneLeading, ht, universalPlanePolynomial_map, bivariateMap_coeff]
    rw [he] at hn
    intro hz
    exact hn (by rw [hz, map_zero])
  exact ⟨rows, cols, mul_ne_zero hl hm, universalPlaneBadWitness_degree f rows cols⟩

end
end CCDN
