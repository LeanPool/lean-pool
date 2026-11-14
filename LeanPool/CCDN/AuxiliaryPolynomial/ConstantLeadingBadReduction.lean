/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Noether.BivariateTotalDegree
public import LeanPool.CCDN.Noether.ClosedFormHeight
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import LeanPool.CCDN.Determinant.ClosedFormIntegerMinor
import LeanPool.CCDN.Determinant.ClosedFormMinorCharge
import LeanPool.CCDN.ForMathlib.Matrix
import LeanPool.CCDN.Noether.ClosedFormScaling

/-! Bad reduction for integer bivariate equations with a nonzero constant
outer leading coefficient. A leading-coefficient factor in the witness also
covers degree-dropping reductions. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Real

/-- Full outer degree forces the outer leading coefficient to be constant. -/
lemma bivariate_leadingCoeff_eq_constant {R : Type*} [CommRing R]
    (f : R[X][X]) (htotal : bivariateTotalDegree f ≤ f.natDegree) :
    f.leadingCoeff = C (f.leadingCoeff.coeff 0) := by
  by_cases hc : f.leadingCoeff = 0
  · simp [hc]
  have hn : f.leadingCoeff.coeff f.leadingCoeff.natDegree ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hc
  have h := bivariateTotalDegree_coeff_le f f.natDegree f.leadingCoeff.natDegree hn
  have hz : f.leadingCoeff.natDegree = 0 := by omega
  exact eq_C_of_natDegree_eq_zero hz

private lemma bivariateMap_constant_leading {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R[X][X]) (a : R) (ha : φ a ≠ 0)
    (hl : f.leadingCoeff = C a) :
    (bivariateMap φ f).natDegree = f.natDegree ∧
      (bivariateMap φ f).leadingCoeff = C (φ a) := by
  have hn : (Polynomial.mapRingHom φ) f.leadingCoeff ≠ 0 := by
    simpa [hl] using ha
  constructor
  · exact natDegree_map_of_leadingCoeff_ne_zero (Polynomial.mapRingHom φ) hn
  · exact (leadingCoeff_map_of_leadingCoeff_ne_zero (Polynomial.mapRingHom φ) hn).trans
      (by simp [hl])

/-- Bad reduction includes both lost total degree and geometric reducibility. -/
def BivariateBadReduction (f : ℤ[X][X]) (d p : ℕ) : Prop :=
  ∃ hp : p.Prime, let _ : Fact p.Prime := ⟨hp⟩
    let fₚ := bivariateMap (Int.castRingHom (AlgebraicClosure (ZMod p))) f
    bivariateTotalDegree fₚ ≠ d ∨ ¬Irreducible fₚ

private lemma exists_constant_leading_integer_minor
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (d : ℕ) (f : ℤ[X][X]) (a : ℤ) (ha : a ≠ 0) (hl : f.leadingCoeff = C a)
    (hdeg : f.natDegree = d) (hir : Irreducible (bivariateMap (Int.castRingHom F) f)) :
    ∃ (r : Fin (2 * d ^ 2 - 1) → ℕ × ℕ)
      (c : Fin (2 * d ^ 2 - 1) → ClosedFormColumns d),
      Function.Injective r ∧ Function.Injective c ∧
      ((closedFormCoefficientMatrix d f).submatrix r c).det ≠ 0 := by
  have haF : (a : F) ≠ 0 := Int.cast_ne_zero.mpr ha
  obtain ⟨hdegF, hlF⟩ := bivariateMap_constant_leading (Int.castRingHom F) f a haF hl
  have hr := closedForm_rank_lower_of_constant_leading d (a : F) haF _ hlF hir (hdegF.trans hdeg)
  obtain ⟨r, c, hr, hc, hdet⟩ := Matrix.exists_det_submatrix_ne_zero_of_le_rank
    (closedFormCoefficientMatrix d (bivariateMap (Int.castRingHom F) f))
    (2 * d ^ 2 - 1) (by omega)
  refine ⟨r, c, hr, hc, ?_⟩
  intro hz
  apply hdet
  rw [← closedForm_minor_map, hz, map_zero]

/-- Every bad prime above the degree divides leading coefficient times minor.
Primes killing the leading coefficient are handled without a rank hypothesis. -/
private lemma constant_leading_bad_prime_dvd
    (d : ℕ) (hd : 0 < d) (f : ℤ[X][X]) (a : ℤ) (hl : f.leadingCoeff = C a)
    (hdeg : f.natDegree = d) (htotal : bivariateTotalDegree f ≤ d)
    (r : Fin (2 * d ^ 2 - 1) → ℕ × ℕ)
    (c : Fin (2 * d ^ 2 - 1) → ClosedFormColumns d)
    (p : ℕ) (hp : d < p) (hbad : BivariateBadReduction f d p) :
    (p : ℤ) ∣ a * ((closedFormCoefficientMatrix d f).submatrix r c).det := by
  by_cases hpa : (p : ℤ) ∣ a
  · exact dvd_mul_of_dvd_left hpa _
  obtain ⟨hpp, hbad⟩ := hbad
  let : Fact p.Prime := ⟨hpp⟩
  let K := AlgebraicClosure (ZMod p)
  let g := bivariateMap (Int.castRingHom K) f
  change bivariateTotalDegree g ≠ d ∨ ¬Irreducible g at hbad
  have haK : (a : K) ≠ 0 := by
    intro hz
    exact hpa ((CharP.intCast_eq_zero_iff K p a).mp hz)
  obtain ⟨hdegK, hlK⟩ := bivariateMap_constant_leading (Int.castRingHom K) f a haK hl
  have ht : bivariateTotalDegree g ≤ d := (bivariateTotalDegree_map_le _ f).trans htotal
  have he : bivariateTotalDegree g = d := by
    have hn := bivariate_natDegree_le_totalDegree g
    change g.natDegree = f.natDegree at hdegK
    omega
  have hred : ¬Irreducible g := hbad.resolve_left (not_ne_iff.mpr he)
  have hr := closedForm_rank_drop_of_constant_leading d hd (.of_charP hp) (a : K) haK g hlK hred
    (hdegK.trans hdeg) ht
  apply dvd_mul_of_dvd_right
  apply characteristic_dvd_closedForm_minor_of_rank_lt (K := K) p d (2 * d ^ 2 - 1) f r c
  dsimp only [g] at hr
  omega

/-- A full-outer-degree integer equation has a height-controlled positive
witness for every bad prime, including loss of degree. Integer monicity is
not required. -/
theorem exists_full_outer_bad_prime_witness
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (d : ℕ) (hd : 1 ≤ d) (f : ℤ[X][X]) (hdeg : f.natDegree = d)
    (htotal : bivariateTotalDegree f ≤ d)
    (hir : Irreducible (bivariateMap (Int.castRingHom F) f))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : BivariateCoefficientBound f H) :
    ∃ D : ℤ, 0 < D ∧
      Real.log D ≤ (27 * (d : ℝ) ^ 4) * (1 + 2 * Real.log H / (d : ℝ) ^ 2) ∧
      ∀ p : ℕ, d < p → BivariateBadReduction f d p → (p : ℤ) ∣ D := by
  have hf : f ≠ 0 := by
    intro hz
    apply hir.ne_zero
    rw [hz, map_zero]
  let a := f.leadingCoeff.coeff 0
  have hl : f.leadingCoeff = C a := bivariate_leadingCoeff_eq_constant f (hdeg ▸ htotal)
  have ha : a ≠ 0 := by
    intro hz
    apply (Polynomial.leadingCoeff_ne_zero.mpr hf)
    rw [hl, hz, map_zero]
  obtain ⟨r, c, _, _, hD⟩ := exists_constant_leading_integer_minor d f a ha hl hdeg hir
  let D := ((closedFormCoefficientMatrix d f).submatrix r c).det
  have hp : a * D ≠ 0 := mul_ne_zero ha hD
  refine ⟨|a * D|, abs_pos.mpr hp, ?_, ?_⟩
  · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hd0 : (0 : ℝ) < d := by linarith
    have haH : |(a : ℝ)| ≤ H := hcoeff f.natDegree 0
    have ha0 : (a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
    have hD0 : (D : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hD
    have hla := Real.log_le_log (abs_pos.mpr ha0) haH
    have hminor := closedForm_minor_log_height d (2 * d ^ 2 - 1) hd (by omega) f H hH hcoeff
      hdeg.le (fun i => (bivariate_coefficient_natDegree_le_totalDegree f i).trans htotal) r c hD
    change Real.log |(D : ℝ)| ≤ _ at hminor
    rw [Int.cast_abs, Int.cast_mul, abs_mul,
      Real.log_mul (abs_ne_zero.mpr ha0) (abs_ne_zero.mpr hD0)]
    have he : (27 * (d : ℝ) ^ 4) * (1 + 2 * Real.log H / (d : ℝ) ^ 2) =
        (27 * (d : ℝ) ^ 4) * (1 + Real.log H / (d : ℝ) ^ 2) +
          27 * (d : ℝ) ^ 2 * Real.log H := by field_simp; ring
    rw [he]
    have hlog : 0 ≤ Real.log H := Real.log_nonneg hH
    have hfac : 0 ≤ 27 * (d : ℝ) ^ 2 - 1 := by nlinarith
    nlinarith [mul_nonneg hfac hlog]
  · intro p hp hbad
    exact (dvd_abs _ _).mpr
      (constant_leading_bad_prime_dvd d (by omega) f a hl hdeg htotal r c p hp hbad)

end
end CCDN
