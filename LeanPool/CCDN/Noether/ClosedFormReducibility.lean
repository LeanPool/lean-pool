/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.CharZeroOrGT
public import LeanPool.CCDN.Noether.BivariateTotalDegree
import LeanPool.CCDN.ForMathlib.Polynomial
import LeanPool.CCDN.Noether.BivariateFactorForms
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
Reducibility forces a rank drop of the closed-form coefficient matrix for normalized monic
bivariate equations whose degrees up to `d` are nonzero in the base field, in particular below
the characteristic and in characteristic zero. The rank drop is first derived from coprime
factor decompositions, with coprimality imposed in the univariate fraction-field ring, where
factorization can supply it.
-/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

/-- A bounded extra solution outside the scalar gradient span forces rank drop. -/
private theorem closedForm_rank_drop_of_extra_form {F : Type*} [Field F]
    (d : ℕ) (hd : 0 < d) (f p q : F[X][X])
    (hf : bivariateTotalDegree f ≤ d) (hf' : f.derivative ≠ 0)
    (hp : InBivariateGrid d p) (hq : InBivariateGrid d q)
    (hclosed : closedFormOperator f (p, q) = 0)
    (hind : ∀ a : F, p ≠ C (C a) * f.derivative) :
    (closedFormCoefficientMatrix d f).rank + 2 ≤ 2 * d ^ 2 := by
  obtain ⟨hg₁, hg₂⟩ := bivariate_gradient_in_grid d hd f hf
  apply closedForm_rank_drop_of_two_forms d f
    (f.derivative, (bivariateCoefficientDerivative F) f) (p, q)
    hg₁ hg₂ hp hq (closedFormOperator_gradient f) hclosed
  · intro he
    exact hf' (congrArg Prod.fst he)
  · intro a ha
    apply hind a
    have he := congrArg Prod.fst ha
    change a • f.derivative = p at he
    simpa only [Algebra.smul_def, Polynomial.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply] using he.symm

/-- A nontrivial coprime product gives two independent bounded closed forms,
and hence the required matrix rank drop. -/
private theorem closedForm_rank_drop_of_coprime_factors
    {F : Type*} [Field F] (d : ℕ) (hd : 0 < d)
    (hchar : CharZeroOrGT F d)
    (g h : F[X][X]) (hg : Irreducible g) (hgm : g.Monic)
    (hh : h ≠ 0) (hhpos : 0 < h.natDegree)
    (hcop : IsCoprime (g.map (algebraMap F[X] (RatFunc F)))
      (h.map (algebraMap F[X] (RatFunc F))))
    (hdeg : (g * h).natDegree = d) (htotal : bivariateTotalDegree (g * h) ≤ d) :
    (closedFormCoefficientMatrix d (g * h)).rank + 2 ≤ 2 * d ^ 2 := by
  let φ := algebraMap F[X] (RatFunc F)
  have hinj := RatFunc.algebraMap_injective F
  have hgpos := hgm.natDegree_pos_of_not_isUnit hg.not_isUnit
  have hsum := natDegree_mul hg.ne_zero hh
  have hgnat : (g.map φ).natDegree = g.natDegree := natDegree_map_eq_of_injective hinj _
  have hhnat : (h.map φ).natDegree = h.natDegree := natDegree_map_eq_of_injective hinj _
  have hgR : Irreducible (g.map φ) := hgm.irreducible_iff_irreducible_map_fraction_map.mp hg
  have hgg : IsCoprime (g.map φ) (g.map φ).derivative :=
    (separable_iff_derivative_ne_zero hgR).mpr
      (derivative_ne_zero_of_natCast_natDegree_ne_zero (by
        rw [hgnat]
        simpa using (map_ne_zero (algebraMap F (RatFunc F))).mpr (hchar _ hgpos (by omega))))
  have hh' := derivative_ne_zero_of_natCast_natDegree_ne_zero (f := h.map φ) (by
    rw [hhnat]
    simpa using (map_ne_zero (algebraMap F (RatFunc F))).mpr (hchar _ hhpos (by omega)))
  have hgd : 0 < bivariateTotalDegree g := hgpos.trans_le (bivariate_natDegree_le_totalDegree g)
  obtain ⟨hpgrid, hqgrid⟩ := bivariate_factor_form_in_grid d g h hg.ne_zero hh hgd htotal
  apply closedForm_rank_drop_of_extra_form d hd (g * h)
    (h * g.derivative) (h * (bivariateCoefficientDerivative F) g) htotal
    (derivative_ne_zero_of_natCast_natDegree_ne_zero (by
      rw [hdeg]
      simpa using (map_ne_zero (algebraMap F (F[X]))).mpr (hchar d hd le_rfl))) hpgrid hqgrid
  · have he := bivariate_factor_closed_form g h
    change _ - _ - _ + _ = (0 : F[X][X])
    linear_combination he
  · intro a he
    apply factor_numerator_not_scalar_gradient (g.map φ) (h.map φ)
      (natDegree_pos_iff_degree_pos.mp (hgnat ▸ hgpos)) hcop hgg hh' (algebraMap F (RatFunc F) a)
    simpa only [Polynomial.map_mul, Polynomial.map_C, derivative_map, derivative_mul,
      Polynomial.map_add, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C, φ] using
      congrArg (Polynomial.map φ) he

/-- Repeated irreducible factors of every multiplicity at least two likewise
force rank drop; the whole equation need not be squarefree. -/
private theorem closedForm_rank_drop_of_repeated_factor
    {F : Type*} [Field F] (d k : ℕ) (hd : 0 < d)
    (hchar : CharZeroOrGT F d)
    (g h : F[X][X]) (hg : Irreducible g) (hgm : g.Monic) (hh : h ≠ 0)
    (hcop : IsCoprime (g.map (algebraMap F[X] (RatFunc F)))
      (h.map (algebraMap F[X] (RatFunc F))))
    (hdeg : (g ^ (k + 2) * h).natDegree = d)
    (htotal : bivariateTotalDegree (g ^ (k + 2) * h) ≤ d) :
    (closedFormCoefficientMatrix d (g ^ (k + 2) * h)).rank + 2 ≤ 2 * d ^ 2 := by
  let φ := algebraMap F[X] (RatFunc F)
  have hinj := RatFunc.algebraMap_injective F
  have hgpos := hgm.natDegree_pos_of_not_isUnit hg.not_isUnit
  have hfn : g ^ (k + 2) * h ≠ 0 := mul_ne_zero (pow_ne_zero _ hg.ne_zero) hh
  have hgdiv : g ∣ g ^ (k + 2) * h := dvd_mul_of_dvd_left (dvd_pow_self g (by omega)) h
  have hgle := natDegree_le_of_dvd hgdiv hfn
  have hgnat : (g.map φ).natDegree = g.natDegree := natDegree_map_eq_of_injective hinj _
  have hgR : Irreducible (g.map φ) := hgm.irreducible_iff_irreducible_map_fraction_map.mp hg
  have hgg : IsCoprime (g.map φ) (g.map φ).derivative :=
    (separable_iff_derivative_ne_zero hgR).mpr
      (derivative_ne_zero_of_natCast_natDegree_ne_zero (by
        rw [hgnat]
        simpa using (map_ne_zero (algebraMap F (RatFunc F))).mpr (hchar _ hgpos (by omega))))
  have hgd : 0 < bivariateTotalDegree g := hgpos.trans_le (bivariate_natDegree_le_totalDegree g)
  obtain ⟨hpgrid, hqgrid⟩ := bivariate_power_factor_form_in_grid d k g h hg.ne_zero hh hgd htotal
  apply closedForm_rank_drop_of_extra_form d hd (g ^ (k + 2) * h)
    (g ^ k * h * g.derivative) (g ^ k * h * (bivariateCoefficientDerivative F) g) htotal
    (derivative_ne_zero_of_natCast_natDegree_ne_zero (by
      rw [hdeg]
      simpa using (map_ne_zero (algebraMap F (F[X]))).mpr (hchar d hd le_rfl))) hpgrid hqgrid
  · have he := bivariate_power_factor_closed_form g h k
    change _ - _ - _ + _ = (0 : F[X][X])
    linear_combination he
  · intro a he
    apply power_factor_numerator_not_scalar_gradient (g.map φ) (h.map φ) k
      (natDegree_pos_iff_degree_pos.mp (hgnat ▸ hgpos)) hcop hgg (algebraMap F (RatFunc F) a)
    have hp : (g.map φ) ^ (k + 2) * h.map φ = (g ^ (k + 2) * h).map φ := by simp
    rw [hp, Polynomial.derivative_map (g ^ (k + 2) * h) φ]
    simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, derivative_map,
      RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C, φ] using congrArg (Polynomial.map φ) he

end
end CCDN

namespace CCDN
noncomputable section
open Polynomial

private lemma exists_monic_bivariate_irreducible_factor {F : Type*} [Field F]
    (f : F[X][X]) (hf : f.Monic) (hu : ¬IsUnit f) :
    ∃ g : F[X][X], Irreducible g ∧ g.Monic ∧ g ∣ f := by
  obtain ⟨r, hr, hrf⟩ := WfDvdMonoid.exists_irreducible_factor hu hf.ne_zero
  obtain ⟨s, hs⟩ := hrf
  have hl : r.leadingCoeff * s.leadingCoeff = 1 := by
    rw [← leadingCoeff_mul, ← hs]
    exact hf
  have hsU : IsUnit s.leadingCoeff :=
    ⟨⟨s.leadingCoeff, r.leadingCoeff, by rw [mul_comm, hl], hl⟩, rfl⟩
  have hC : IsUnit (C s.leadingCoeff) := hsU.map C
  have ha := associated_mul_unit_right r (C s.leadingCoeff) hC
  refine ⟨r * C s.leadingCoeff, ha.irreducible_iff.mp hr, ?_, ?_⟩
  · change (r * C s.leadingCoeff).leadingCoeff = 1
    rw [leadingCoeff_mul, leadingCoeff_C, hl]
  · exact ha.dvd_iff_dvd_left.mp ⟨s, hs⟩

/-- Extract one monic irreducible factor with its full multiplicity; the
remaining factor is monic and coprime after passage to the fraction field. -/
private lemma exists_monic_bivariate_primary_factor {F : Type*} [Field F]
    (f : F[X][X]) (hf : f.Monic) (hu : ¬IsUnit f) :
    ∃ (g h : F[X][X]) (m : ℕ), Irreducible g ∧ g.Monic ∧ h.Monic ∧
      0 < m ∧ f = g ^ m * h ∧
      IsCoprime (g.map (algebraMap F[X] (RatFunc F)))
        (h.map (algebraMap F[X] (RatFunc F))) := by
  obtain ⟨g, hg, hgm, hgf⟩ := exists_monic_bivariate_irreducible_factor f hf hu
  obtain ⟨m, h, hnd, he⟩ := WfDvdMonoid.max_power_factor hf.ne_zero hg
  have hm : 0 < m := by
    by_contra hn
    have hz : m = 0 := by omega
    simp only [hz, pow_zero, one_mul] at he
    exact hnd (he ▸ hgf)
  have hhm : h.Monic := (hgm.pow m).of_mul_monic_left (he ▸ hf)
  refine ⟨g, h, m, hg, hgm, hhm, hm, he, ?_⟩
  have hgR : Irreducible (g.map (algebraMap F[X] (RatFunc F))) :=
    hgm.irreducible_iff_irreducible_map_fraction_map.mp hg
  apply (hgR.isCoprime_or_dvd _).resolve_right
  intro hdiv
  exact hnd ((hgm.isPrimitive.dvd_iff_fraction_map_dvd_fraction_map (RatFunc F)).mpr hdiv)

/-- A reducible normalized equation of total degree at most d, with outer
degree d, in characteristic zero or larger than d, has coefficient-matrix kernel
dimension at least two. Both squarefree and repeated-factor cases are covered. -/
theorem closedForm_rank_drop_of_not_irreducible
    {F : Type*} [Field F] (d : ℕ) (hd : 0 < d)
    (hchar : CharZeroOrGT F d)
    (f : F[X][X]) (hf : f.Monic) (hred : ¬Irreducible f)
    (hdeg : f.natDegree = d) (htotal : bivariateTotalDegree f ≤ d) :
    (closedFormCoefficientMatrix d f).rank + 2 ≤ 2 * d ^ 2 := by
  have hfu : ¬IsUnit f := not_isUnit_of_natDegree_pos f (hdeg ▸ hd)
  obtain ⟨g, h, m, hg, hgm, hhm, hm, he, hcop⟩ :=
    exists_monic_bivariate_primary_factor f hf hfu
  by_cases hm1 : m = 1
  · have he' : f = g * h := by simpa only [hm1, pow_one] using he
    have hhu : ¬IsUnit h := by
      intro hhU
      apply hred
      rw [he']
      exact (associated_mul_unit_left g h hhU).irreducible_iff.mpr hg
    rw [he'] at hdeg htotal ⊢
    exact closedForm_rank_drop_of_coprime_factors d hd hchar g h hg hgm hhm.ne_zero
      (hhm.natDegree_pos_of_not_isUnit hhu) hcop hdeg htotal
  · have hm2 : m = (m - 2) + 2 := by omega
    rw [hm2] at he
    rw [he] at hdeg htotal ⊢
    exact closedForm_rank_drop_of_repeated_factor d (m - 2) hd hchar g h hg hgm
      hhm.ne_zero hcop hdeg htotal

end
end CCDN
