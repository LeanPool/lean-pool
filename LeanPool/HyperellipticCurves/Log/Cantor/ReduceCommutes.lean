/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Cantor.CantorPipeline
public import LeanPool.HyperellipticCurves.RedJ.Hom
public import LeanPool.HyperellipticCurves.RedJ.Stability

import LeanPool.HyperellipticCurves.ForMathlib.LocalRing
import LeanPool.HyperellipticCurves.ForMathlib.Polynomial
import Mathlib.Algebra.Polynomial.Lifts

/-!
# Reduction commutes with reduced representatives (blueprint `lem:reduce-commutes`)

`ChabautyColeman.red_reducedRep_eq`: if the reduction `redJ` of the class of a reduced
Mumford datum `(u, v)` over `K` is represented by a reduced datum `(u₀, v₀)` over the
residue field with `u₀` squarefree of full degree (good position), then `(u, v)` is
*integral* — it descends to `O[X]` — and reduces exactly to `(u₀, v₀)`.

Route: over the splitting field `L` of `u` the reduction is the class of the reduced ideal
of the base-changed datum (`ChabautyColeman.redJ_mk0_mumfordIdeal_of_splits`), and the split
Mumford ideal factors into point ideals (`ChabautyColeman.eq_of_mumfordIdeal_eq_prod_pointIdeal`:
the factorization determines the datum, by the norm identity `I·ι(I) = (u)`). Reducing
the factorization to the residue curve and matching it against `(u₀, v₀)`
(`ChabautyColeman.prod_pointIdeal_eq_reduced`: semi-reduce with
`exists_span_singleton_mul_mumfordIdeal`, count degrees with the norm identity, conclude
with uniqueness of reduced representatives), the full degree of `u₀` forces every point
to be integral with multiplicity one and distinct reductions
(`ChabautyColeman.red_reducedRep_points`). The datum is then integral because `u` is a
product of linear factors with integral roots and `v` is the CRT interpolant through the
integral points (the `x`-coordinates have distinct reductions, so their differences are
units), and the residue identifications follow by transport along the residue-field
equivalence of the integral closure.

The file's second exported result is `ChabautyColeman.redJ_mk0_mumford`: the reduction of the
class of an integral Mumford datum with squarefree reduced `u`-part is the class of the
reduced datum. Both are consumed by `LeanPool.HyperellipticCurves.Log.Ftau.ChartMem`.
-/

@[expose] public section

open Polynomial nonZeroDivisors

namespace ChabautyColeman

variable {F : Type*} [Field F] {g : F[X]}

variable [NeZero (2 : F)] [Fact (Squarefree g)]

/-- The conjugate product of a product of point ideals is the principal ideal of the
product of the linear factors — the norm computation shared by the factorization
lemmas. -/
private theorem prod_pointIdeal_mul_star {ι : Type*} (s : Finset ι) (x y : ι → F)
    (k : ι → ℕ) (hcurve : ∀ i ∈ s, y i ^ 2 = g.eval (x i)) :
    (∏ i ∈ s, pointIdeal g (x i) (y i) ^ k i)
      * (∏ i ∈ s, pointIdeal g (x i) (y i) ^ k i).map (starRingEnd (HypRing F g))
      = Ideal.span {algebraMap F[X] (HypRing F g) (∏ i ∈ s, (X - C (x i)) ^ k i)} := by
  classical
  have hsf : Squarefree g := Fact.out
  have h2 : (2 : F) ≠ 0 := NeZero.ne 2
  have hmapprod : Ideal.map (starRingEnd (HypRing F g))
      (∏ i ∈ s, pointIdeal g (x i) (y i) ^ k i)
      = ∏ i ∈ s, Ideal.map (starRingEnd (HypRing F g)) (pointIdeal g (x i) (y i) ^ k i) :=
    map_prod (Ideal.mapHom _) _ _
  rw [hmapprod, ← Finset.prod_mul_distrib, map_prod, ← Ideal.prod_span_singleton]
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  have hmappow : Ideal.map (starRingEnd (HypRing F g)) (pointIdeal g (x i) (y i) ^ k i)
      = ((pointIdeal g (x i) (y i)).map (starRingEnd (HypRing F g))) ^ k i :=
    map_pow (Ideal.mapHom _) _ _
  have hstar : (pointIdeal g (x i) (y i)).map (starRingEnd (HypRing F g))
      = pointIdeal g (x i) (-(y i)) := by
    rw [pointIdeal_eq_mumfordIdeal, pointIdeal_eq_mumfordIdeal, map_star_mumfordIdeal,
      C_neg]
  rw [hmappow, hstar, ← mul_pow, pointIdeal_mul_pointIdeal_neg g hsf h2 (hcurve i hi),
    Ideal.span_singleton_pow, ← map_pow]

variable [Fact (Odd g.natDegree)]

/-- **The point factorization of a Mumford ideal determines the datum**: if the Mumford
ideal of a monic datum `(u, v)` is a product of point ideals, then `u` is the product of
the corresponding linear factors and `v` interpolates the `y`-coordinates. -/
theorem eq_of_mumfordIdeal_eq_prod_pointIdeal {ι : Type*} {s : Finset ι} {x y : ι → F}
    {k : ι → ℕ} (hcurve : ∀ i ∈ s, y i ^ 2 = g.eval (x i))
    {u v : F[X]} (hu : u.Monic) (hdvd : u ∣ v ^ 2 - g)
    (hfac : mumfordIdeal g u v = ∏ i ∈ s, pointIdeal g (x i) (y i) ^ k i) :
    ∏ i ∈ s, (X - C (x i)) ^ k i = u ∧ ∀ i ∈ s, k i ≠ 0 → v.eval (x i) = y i := by
  classical
  have hsf : Squarefree g := Fact.out
  have h2 : (2 : F) ≠ 0 := NeZero.ne 2
  have hAmonic : (∏ i ∈ s, (X - C (x i)) ^ k i).Monic :=
    monic_prod_of_monic _ _ fun i _ ↦ (monic_X_sub_C _).pow _
  have hueq : ∏ i ∈ s, (X - C (x i)) ^ k i = u := by
    have h1 := prod_pointIdeal_mul_star s x y k hcurve
    rw [← hfac, mumfordIdeal_mul_map_star g hsf h2 hdvd] at h1
    obtain ⟨w, hw⟩ := Ideal.span_singleton_eq_span_singleton.mp h1.symm
    obtain ⟨e, hwe⟩ := (HypRing.isUnit_iff Fact.out).mp w.isUnit
    rw [hwe, HypRing.algebraMap_eq_C, ← map_mul] at hw
    have hAe : (∏ i ∈ s, (X - C (x i)) ^ k i) * C (e : F) = u :=
      QuadraticAlgebra.algebraMap_injective hw
    exact eq_of_monic_of_associated hAmonic hu
      ⟨(isUnit_C.mpr e.isUnit).unit, by rwa [IsUnit.unit_spec]⟩
  refine ⟨hueq, fun i hi hki ↦ ?_⟩
  have hP : mumfordIdeal g u v ≤ pointIdeal g (x i) (y i) := by
    rw [hfac, ← Finset.mul_prod_erase s _ hi]
    exact le_trans Ideal.mul_le_left (Ideal.pow_le_self hki)
  exact eval_eq_of_y_sub_mem_pointIdeal (hcurve i hi) (hP (y_sub_mem_mumfordIdeal g u v))

/-- **The Mumford ideal of a split datum with distinct roots is the product of its point
ideals** — the converse of `eq_of_mumfordIdeal_eq_prod_pointIdeal`. The containment in
each point ideal gives divisibility by the product of the (distinct maximal) point
ideals; the norm identity `I·ι(I) = (u)` on both sides forces the connecting factor to
be the unit ideal. -/
theorem mumfordIdeal_eq_prod_pointIdeal {ι : Type*} {s : Finset ι} {x y : ι → F}
    (hcurve : ∀ i ∈ s, y i ^ 2 = g.eval (x i))
    (hinj : ∀ i ∈ s, ∀ j ∈ s, x i = x j → i = j)
    {u v : F[X]} (hu : u = ∏ i ∈ s, (X - C (x i))) (hdvd : u ∣ v ^ 2 - g)
    (hvals : ∀ i ∈ s, v.eval (x i) = y i) :
    mumfordIdeal g u v = ∏ i ∈ s, pointIdeal g (x i) (y i) := by
  classical
  have hsf : Squarefree g := Fact.out
  have h2 : (2 : F) ≠ 0 := NeZero.ne 2
  -- the Mumford ideal is contained in each point ideal
  have hle : ∀ i ∈ s, mumfordIdeal g u v ≤ pointIdeal g (x i) (y i) := by
    intro i hi
    rw [mumfordIdeal_eq_span, pointIdeal_eq_ker (hcurve i hi)]
    refine Ideal.span_le.mpr ?_
    rintro z (rfl | rfl)
    · rw [SetLike.mem_coe, RingHom.mem_ker, evalHom_algebraMap, hu]
      refine eval_eq_zero_of_dvd_of_eval_eq_zero (Finset.dvd_prod_of_mem _ hi) ?_
      rw [eval_sub, eval_X, eval_C, sub_self]
    · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, evalHom_y, evalHom_algebraMap,
        sub_eq_zero]
      exact (hvals i hi).symm
  -- the product of the (distinct prime) point ideals divides the Mumford ideal
  have hpinj : ∀ i ∈ s, ∀ j ∈ s, pointIdeal g (x i) (y i) = pointIdeal g (x j) (y j)
      → i = j := fun i hi j hj h ↦
    hinj i hi j hj ((pointIdeal_eq_pointIdeal_iff (hcurve i hi)).mp h).1
  have hdvdprod : (∏ i ∈ s, pointIdeal g (x i) (y i)) ∣ mumfordIdeal g u v := by
    rw [show (∏ i ∈ s, pointIdeal g (x i) (y i))
        = ∏ P ∈ s.image fun i ↦ pointIdeal g (x i) (y i), P from
      (Finset.prod_image (f := fun P ↦ P) hpinj).symm]
    refine Finset.prod_primes_dvd _ ?_ ?_
    · intro P hP
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hP
      refine Ideal.prime_of_isPrime ?_ (pointIdeal_isMaximal (hcurve i hi)).isPrime
      exact pointIdeal_ne_bot g _ _
    · intro P hP
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hP
      exact Ideal.dvd_iff_le.mpr (hle i hi)
  obtain ⟨J, hJ⟩ := hdvdprod
  -- norms: both sides have conjugate product `(u)`, so the connecting factor is trivial
  have hu0 : u ≠ 0 := by
    rw [hu]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ X_sub_C_ne_zero _
  have hnormM : mumfordIdeal g u v * (mumfordIdeal g u v).map (starRingEnd (HypRing F g))
      = Ideal.span {algebraMap F[X] (HypRing F g) u} :=
    mumfordIdeal_mul_map_star g hsf h2 hdvd
  have hnormP : (∏ i ∈ s, pointIdeal g (x i) (y i))
      * (∏ i ∈ s, pointIdeal g (x i) (y i)).map (starRingEnd (HypRing F g))
      = Ideal.span {algebraMap F[X] (HypRing F g) u} := by
    have h := prod_pointIdeal_mul_star s x y (fun _ ↦ 1) hcurve
    simp only [pow_one] at h
    rwa [← hu] at h
  have hspan0 : Ideal.span {algebraMap F[X] (HypRing F g) u} ≠ 0 :=
    span_singleton_algebraMap_ne_zero g hu0
  have hJJ : J * J.map (starRingEnd (HypRing F g)) = 1 := by
    have h1 : Ideal.span {algebraMap F[X] (HypRing F g) u}
        = Ideal.span {algebraMap F[X] (HypRing F g) u}
          * (J * J.map (starRingEnd (HypRing F g))) := by
      calc Ideal.span {algebraMap F[X] (HypRing F g) u}
          = mumfordIdeal g u v
            * (mumfordIdeal g u v).map (starRingEnd (HypRing F g)) := hnormM.symm
        _ = (∏ i ∈ s, pointIdeal g (x i) (y i)) * J
            * (((∏ i ∈ s, pointIdeal g (x i) (y i)) * J).map
              (starRingEnd (HypRing F g))) := by rw [← hJ]
        _ = (∏ i ∈ s, pointIdeal g (x i) (y i))
            * ((∏ i ∈ s, pointIdeal g (x i) (y i)).map (starRingEnd (HypRing F g)))
            * (J * J.map (starRingEnd (HypRing F g))) := by
              rw [Ideal.map_mul]
              ring
        _ = Ideal.span {algebraMap F[X] (HypRing F g) u}
            * (J * J.map (starRingEnd (HypRing F g))) := by rw [hnormP]
    exact (mul_left_cancel₀ hspan0 ((mul_one _).trans h1)).symm
  rw [hJ, Ideal.isUnit_iff.mp (isUnit_iff_exists_inv.mpr ⟨_, hJJ⟩), Ideal.mul_top]

/-- **The norm identity determines the product of linear factors up to a scalar**: if the
product of point ideals is the semi-reduced datum `(c) · (u', v')`, then conjugating both
descriptions and comparing the two principal generators gives `∏ (X - C xᵢ)^kᵢ · e = c² u'`
for a unit `e` of `F`. -/
private theorem prod_X_sub_C_pow_mul_C_eq_of_span_mul {ι : Type*} (s : Finset ι) (x y : ι → F)
    (k : ι → ℕ) (hcurve : ∀ i ∈ s, y i ^ 2 = g.eval (x i)) {c u' v' : F[X]}
    (hdvd' : u' ∣ v' ^ 2 - g)
    (hDeq : (∏ i ∈ s, pointIdeal g (x i) (y i) ^ k i)
      = Ideal.span {algebraMap F[X] (HypRing F g) c} * mumfordIdeal g u' v') :
    ∃ e : Fˣ, (∏ i ∈ s, (X - C (x i)) ^ k i) * C (e : F) = c ^ 2 * u' := by
  set D := ∏ i ∈ s, pointIdeal g (x i) (y i) ^ k i
  have hcstar : (Ideal.span {algebraMap F[X] (HypRing F g) c}).map
      (starRingEnd (HypRing F g)) = Ideal.span {algebraMap F[X] (HypRing F g) c} := by
    have hstc : (starRingEnd (HypRing F g)) (algebraMap F[X] (HypRing F g) c)
        = algebraMap F[X] (HypRing F g) c := QuadraticAlgebra.star_algebraMap c
    rw [Ideal.map_span, Set.image_singleton, hstc]
  have hDstar' : D * D.map (starRingEnd (HypRing F g))
      = Ideal.span {algebraMap F[X] (HypRing F g) (c ^ 2 * u')} := by
    rw [hDeq, Ideal.map_mul, hcstar, map_star_mumfordIdeal]
    calc Ideal.span {algebraMap F[X] (HypRing F g) c} * mumfordIdeal g u' v'
        * (Ideal.span {algebraMap F[X] (HypRing F g) c} * mumfordIdeal g u' (-v'))
        = Ideal.span {algebraMap F[X] (HypRing F g) c}
          * Ideal.span {algebraMap F[X] (HypRing F g) c}
          * (mumfordIdeal g u' v' * mumfordIdeal g u' (-v')) := by ring
      _ = Ideal.span {algebraMap F[X] (HypRing F g) (c ^ 2 * u')} := by
        rw [← map_star_mumfordIdeal, mumfordIdeal_mul_map_star g Fact.out (NeZero.ne 2) hdvd',
          Ideal.span_singleton_mul_span_singleton,
          Ideal.span_singleton_mul_span_singleton, ← map_mul, ← map_mul, sq]
  obtain ⟨w, hw⟩ : Associated (algebraMap F[X] (HypRing F g) (∏ i ∈ s, (X - C (x i)) ^ k i))
      (algebraMap F[X] (HypRing F g) (c ^ 2 * u')) := by
    rw [← Ideal.span_singleton_eq_span_singleton, ← prod_pointIdeal_mul_star s x y k hcurve,
      hDstar']
  obtain ⟨e, hwe⟩ := (HypRing.isUnit_iff Fact.out).mp w.isUnit
  rw [hwe, HypRing.algebraMap_eq_C, ← map_mul] at hw
  exact ⟨e, QuadraticAlgebra.algebraMap_injective hw⟩

/-- **A product of point-ideal classes matched with a reduced Mumford class determines
the points**: if a product of `≤ deg u₀` point ideals represents the same class as a
reduced Mumford ideal `(u₀, v₀)`, then the `x`-coordinates with multiplicity form
exactly the root datum of `u₀`, and `v₀` interpolates the `y`-coordinates. Semi-reduce
the product (`exists_span_singleton_mul_mumfordIdeal`); the norm identity
`I · ι(I) = (u)` counts degrees and forces the connecting factor to be a unit, and
uniqueness of reduced representatives identifies the datum. -/
theorem prod_pointIdeal_eq_reduced {ι : Type*} {s : Finset ι} {x y : ι → F} {k : ι → ℕ}
    (hcurve : ∀ i ∈ s, y i ^ 2 = g.eval (x i))
    {u₀ v₀ : F[X]} (hu₀ : u₀.Monic) (hv₀ : v₀.degree < u₀.degree)
    (hg₀ : 2 * u₀.natDegree < g.natDegree) (hd₀ : u₀ ∣ v₀ ^ 2 - g)
    (hdeg : ∑ i ∈ s, k i ≤ u₀.natDegree)
    (hD0 : (∏ i ∈ s, pointIdeal g (x i) (y i) ^ k i) ≠ 0)
    (hmk : ClassGroup.mk0 ⟨∏ i ∈ s, pointIdeal g (x i) (y i) ^ k i,
        mem_nonZeroDivisors_of_ne_zero hD0⟩
      = ClassGroup.mk0 ⟨mumfordIdeal g u₀ v₀,
          mumfordIdeal_mem_nonZeroDivisors g hu₀.ne_zero v₀⟩) :
    ∏ i ∈ s, (X - C (x i)) ^ k i = u₀ ∧ ∀ i ∈ s, k i ≠ 0 → v₀.eval (x i) = y i := by
  classical
  have hsf : Squarefree g := Fact.out
  have h2 : (2 : F) ≠ 0 := NeZero.ne 2
  set D := ∏ i ∈ s, pointIdeal g (x i) (y i) ^ k i with hDdef
  -- semi-reduce the product of point ideals
  obtain ⟨c, u', v', hc0, hu'0, hdvd', hDeq⟩ :=
    exists_span_singleton_mul_mumfordIdeal g D (by rwa [← Submodule.zero_eq_bot])
  -- the conjugate product computes the norm two ways, up to a scalar
  obtain ⟨e, hAe⟩ := prod_X_sub_C_pow_mul_C_eq_of_span_mul s x y k hcurve hdvd' hDeq
  -- degree bookkeeping
  have hA0 : (∏ i ∈ s, (X - C (x i)) ^ k i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)
  have hAmonic : (∏ i ∈ s, (X - C (x i)) ^ k i).Monic :=
    monic_prod_of_monic _ _ fun i _ ↦ (monic_X_sub_C _).pow _
  have he0 : (e : F) ≠ 0 := e.ne_zero
  have hdegid : ∑ i ∈ s, k i = 2 * c.natDegree + u'.natDegree := by
    have h1 := congrArg natDegree hAe
    rw [natDegree_mul hA0 (fun h ↦ he0 (by rwa [← C_eq_zero])), natDegree_C, add_zero,
      natDegree_mul (pow_ne_zero 2 hc0) hu'0, natDegree_pow,
      natDegree_prod_X_sub_C_pow] at h1
    lia
  -- the class of the point product is the class of the semi-reduced datum
  have hM'0 : mumfordIdeal g u' v' ≠ 0 := mumfordIdeal_ne_zero g hu'0 v'
  have hcspan0 : Ideal.span {algebraMap F[X] (HypRing F g) c} ≠ 0 :=
    span_singleton_algebraMap_ne_zero g hc0
  have hmkD : ClassGroup.mk0 ⟨D, mem_nonZeroDivisors_of_ne_zero hD0⟩
      = ClassGroup.mk0 ⟨mumfordIdeal g u' v', mem_nonZeroDivisors_of_ne_zero hM'0⟩ :=
    (congrArg ClassGroup.mk0 (Subtype.ext hDeq)).trans
      (mk0_mul_left_of_isPrincipal (mem_nonZeroDivisors_of_ne_zero hcspan0)
        (mem_nonZeroDivisors_of_ne_zero hM'0) ⟨⟨_, rfl⟩⟩)
  -- normalize the semi-reduced datum
  set u'' := u' * C u'.leadingCoeff⁻¹ with hu''def
  set v'' := v' %ₘ u'' with hv''def
  have hu''m : u''.Monic := monic_mul_leadingCoeff_inv hu'0
  have hIdeq : mumfordIdeal g u'' v'' = mumfordIdeal g u' v' := by
    rw [hv''def, mumfordIdeal_modByMonic, hu''def]
    exact mumfordIdeal_mul_leadingCoeff_inv g hu'0
  have hu''dvd : u'' ∣ v' ^ 2 - g := (mul_leadingCoeff_inv_dvd_iff hu'0).mpr hdvd'
  have hdvd'' : u'' ∣ v'' ^ 2 - g := dvd_modByMonic_sq_sub_of_dvd g hu''dvd
  have hv''deg : v''.degree < u''.degree := degree_modByMonic_lt _ hu''m
  have hu''nat : u''.natDegree = u'.natDegree :=
    natDegree_eq_of_degree_eq (degree_mul_leadingCoeff_inv u' hu'0)
  have hg'' : 2 * u''.natDegree < g.natDegree := by lia
  have hcl : ClassGroup.mk0 ⟨mumfordIdeal g u'' v'',
        mumfordIdeal_mem_nonZeroDivisors g hu''m.ne_zero v''⟩
      = ClassGroup.mk0 ⟨mumfordIdeal g u₀ v₀,
          mumfordIdeal_mem_nonZeroDivisors g hu₀.ne_zero v₀⟩ :=
    ((congrArg ClassGroup.mk0 (Subtype.ext hIdeq)).trans hmkD.symm).trans hmk
  obtain ⟨hueq, hveq⟩ := mumfordIdeal_reduced_unique g hu''m hu₀ hv''deg hv₀ hg'' hg₀
    hdvd'' hd₀ hcl
  -- the connecting factor is a unit, and the product of linear factors is `u₀`
  have hu'nat : u'.natDegree = u₀.natDegree := by rw [← hu''nat, hueq]
  have hcnat : c.natDegree = 0 := by lia
  have hγ : c = C (c.coeff 0) := eq_C_of_natDegree_eq_zero hcnat
  have hγ0 : c.coeff 0 ≠ 0 := fun h ↦ hc0 (by rw [hγ, h, C_0])
  have hA2 : (∏ i ∈ s, (X - C (x i)) ^ k i)
      = C (c.coeff 0 ^ 2 * (e : F)⁻¹) * u' := by
    have h := hAe
    rw [hγ, ← C_pow] at h
    calc (∏ i ∈ s, (X - C (x i)) ^ k i)
        = (∏ i ∈ s, (X - C (x i)) ^ k i) * C (e : F) * C (e : F)⁻¹ := by
          rw [mul_assoc, ← C_mul, mul_inv_cancel₀ he0, C_1, mul_one]
      _ = C (c.coeff 0 ^ 2) * u' * C (e : F)⁻¹ := by rw [h]
      _ = C (c.coeff 0 ^ 2 * (e : F)⁻¹) * u' := by rw [C_mul]; ring
  have hAeq : (∏ i ∈ s, (X - C (x i)) ^ k i) = u₀ := by
    have hlcA := hAmonic.leadingCoeff
    rw [hA2, leadingCoeff_mul, leadingCoeff_C] at hlcA
    have hδ : c.coeff 0 ^ 2 * (e : F)⁻¹ = u'.leadingCoeff⁻¹ :=
      eq_inv_of_mul_eq_one_left hlcA
    rw [hA2, hδ, mul_comm, ← hu''def, hueq]
  refine ⟨hAeq, fun i hi hki ↦ ?_⟩
  -- the interpolation values, via the point-evaluation homomorphism
  have hP : D ≤ pointIdeal g (x i) (y i) := by
    rw [hDdef, ← Finset.mul_prod_erase s _ hi]
    exact le_trans Ideal.mul_le_left (Ideal.pow_le_self hki)
  have hprime := (pointIdeal_isMaximal (hcurve i hi)).isPrime
  rcases hprime.mul_le.mp (hDeq ▸ hP) with hcase | hcase
  · -- the connecting scalar cannot vanish at the point
    exfalso
    have hmem : algebraMap F[X] (HypRing F g) c ∈ pointIdeal g (x i) (y i) :=
      hcase (Ideal.subset_span rfl)
    rw [pointIdeal_eq_ker (hcurve i hi), RingHom.mem_ker, evalHom_algebraMap, hγ,
      eval_C] at hmem
    exact hγ0 hmem
  · -- the point lies on the semi-reduced datum
    have hymem : v'.eval (x i) = y i :=
      eval_eq_of_y_sub_mem_pointIdeal (hcurve i hi) (hcase (y_sub_mem_mumfordIdeal g u' v'))
    -- pass from `v'` to the reduced `v₀` using that `x i` is a root of `u₀`
    have hroot : u₀.eval (x i) = 0 := by
      rw [← hAeq]
      refine eval_eq_zero_of_dvd_of_eval_eq_zero
        (dvd_pow_self _ hki |>.trans (Finset.dvd_prod_of_mem _ hi)) ?_
      rw [eval_sub, eval_X, eval_C, sub_self]
    have hspec := modByMonic_add_div v' u''
    have := congrArg (Polynomial.eval (x i)) hspec
    rw [eval_add, eval_mul, ← hv''def, hveq, hueq, hroot, zero_mul, add_zero] at this
    rwa [this]

section Main

universe u

open Function IsLocalRing

/-- A polynomial over the fraction field `K` whose image in an extension `L` is defined over the
integral closure of `O` in `L` is already defined over `O`: its coefficients are integral over
`O`, hence in `O` because `O` is integrally closed. -/
theorem exists_map_eq_of_map_integralClosure {O K L : Type*} [CommRing O]
    [IsIntegrallyClosed O] [Field K] [Algebra O K] [IsFractionRing O K] [Field L] [Algebra K L]
    [Algebra O L] [IsScalarTower O K L] {q : K[X]} {qC : (integralClosure O L)[X]}
    (h : q.map (algebraMap K L) = qC.map (algebraMap (integralClosure O L) L)) :
    ∃ qO : O[X], qO.map (algebraMap O K) = q := by
  refine (Polynomial.mem_lifts q).mp ((Polynomial.lifts_iff_coeff_lifts q).mpr fun n ↦ ?_)
  refine IsIntegrallyClosed.isIntegral_iff.mp
    ((isIntegral_algHom_iff (IsScalarTower.toAlgHom O K L) (algebraMap K L).injective).mp ?_)
  have h1 : algebraMap K L (q.coeff n) = algebraMap (integralClosure O L) L (qC.coeff n) := by
    rw [← Polynomial.coeff_map, ← Polynomial.coeff_map, h]
  rw [show (IsScalarTower.toAlgHom O K L) (q.coeff n) = algebraMap K L (q.coeff n) from rfl, h1]
  exact IsIntegral.map (IsScalarTower.toAlgHom O (integralClosure O L) L)
    (integralClosure.isIntegral _)

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]
  {K : Type u} [Field K] [Algebra O K] [IsFractionRing O K] [CharZero K]
  [IsAlgClosed (ResidueField O)] {f : O[X]}

variable (f) in
/-- Reduction of a curve point stays on the reduced curve. -/
theorem redres_sq_curve (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] {x y : L}
    (hxy : y ^ 2 = ((f.map (algebraMap O K)).map (algebraMap K L)).eval x)
    (hx : IsIntegral O x) :
    redres O L y ^ 2 = (f.map (residue O)).eval (redres O L x) := by
  have hy : IsIntegral O y := isIntegral_of_curve f L hxy hx
  set t : integralClosure O L := ⟨x, hx⟩
  set s : integralClosure O L := ⟨y, hy⟩
  have hinj : Function.Injective (algebraMap (integralClosure O L) L) :=
    Subtype.coe_injective
  -- the curve identity descends to the integral closure
  have hcl : s ^ 2 = (f.map (algebraMap O (integralClosure O L))).eval t := by
    refine hinj ?_
    rwa [map_pow, ← eval_map_apply, ← map_algebraMap_integralClosure_eq f L]
  have hres : residue (integralClosure O L) s ^ 2
      = ((f.map (algebraMap O (integralClosure O L))).map
          (residue (integralClosure O L))).eval (residue (integralClosure O L) t) := by
    rw [eval_map_apply, ← map_pow]
    exact congrArg _ hcl
  have hrs : redres O L y = ((integralClosureResidueEquiv O L).symm :
      ResidueField (integralClosure O L) →+* ResidueField O)
      (residue (integralClosure O L) s) := redres_coe (t := s)
  have hrt : redres O L x = ((integralClosureResidueEquiv O L).symm :
      ResidueField (integralClosure O L) →+* ResidueField O)
      (residue (integralClosure O L) t) := redres_coe (t := t)
  rw [hrs, hrt, ← map_pow, hres, ← eval_map_apply, map_residue_integralClosure_eq]

variable [NeZero (2 : ResidueField O)]
  [Fact (Odd (f.map (algebraMap O K)).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O K)))]
  [Fact (Odd (f.map (residue O)).natDegree)] [Fact (Squarefree (f.map (residue O)))]

open nonZeroDivisors in
/-- **Reduction of the class of a split Mumford datum**: if `u` splits over the finite
extension `L/K`, the reduction of the class of `(u, v)` is the class of the reduced ideal of
the base-changed datum. -/
theorem redJ_mk0_mumfordIdeal_of_splits (hf : f.Monic) (hdeg : 0 < f.natDegree)
    {L : IntermediateField K (AlgebraicClosure K)} [FiniteDimensional K L] {u v : K[X]}
    (hu0 : u ≠ 0) (hdvd : u ∣ v ^ 2 - f.map (algebraMap O K))
    (hsplit : (u.map (algebraMap K L)).Splits) :
    redJ (ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O K)) u v,
        mumfordIdeal_mem_nonZeroDivisors _ hu0 v⟩)
      = ClassGroup.mk0 ⟨redIdealBar f L (mumfordIdeal
            ((f.map (algebraMap O K)).map (algebraMap K L)) (u.map (algebraMap K L))
            (v.map (algebraMap K L))),
          mem_nonZeroDivisors_of_ne_zero (redIdealBar_ne_zero f L _)⟩ := by
  have huL0 : u.map (algebraMap K L) ≠ 0 := by
    simpa [Polynomial.map_eq_zero_iff (algebraMap K L).injective] using hu0
  have hdvdL : u.map (algebraMap K L) ∣ (v.map (algebraMap K L)) ^ 2
      - (f.map (algebraMap O K)).map (algebraMap K L) := by
    have h := Polynomial.map_dvd (algebraMap K L) hdvd
    rwa [Polynomial.map_sub, Polynomial.map_pow] at h
  have hM0 : mumfordIdeal ((f.map (algebraMap O K)).map (algebraMap K L))
      (u.map (algebraMap K L)) (v.map (algebraMap K L)) ≠ 0 :=
    mumfordIdeal_ne_zero _ huL0 (v.map (algebraMap K L))
  refine IsRedJPair.redJ_eq hf hdeg ⟨L, ‹FiniteDimensional K L›,
    ⟨_, mem_nonZeroDivisors_of_ne_zero hM0⟩,
    splitSupported_mumfordIdeal huL0 hdvdL hsplit, ?_, rfl⟩
  rw [HypJac.map_mk0]
  congr 1
  ext : 1
  exact mumfordIdeal_map (f.map (algebraMap O K)) u v

open nonZeroDivisors in
/-- **Reduction commutes with reduced representatives, point stage**: the split Mumford
representative of a reduced datum whose reduction is represented by a squarefree
full-degree datum consists of distinct integral points with distinct reductions, matching
the roots of `u₀` and interpolated by `v₀`. -/
theorem red_reducedRep_points (hf : f.Monic) (hdeg : 0 < f.natDegree)
    {u v : K[X]} (hu : u.Monic)
    (hdvd : u ∣ v ^ 2 - f.map (algebraMap O K))
    {u₀ v₀ : (ResidueField O)[X]} (hu₀ : u₀.Monic) (hv₀ : v₀.degree < u₀.degree)
    (hg₀ : 2 * u₀.natDegree < (f.map (residue O)).natDegree)
    (hd₀ : u₀ ∣ v₀ ^ 2 - f.map (residue O)) (hsq₀ : Squarefree u₀)
    (hfull : u.natDegree ≤ u₀.natDegree)
    (hred : redJ (ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O K)) u v,
        mumfordIdeal_mem_nonZeroDivisors _ hu.ne_zero v⟩)
      = ClassGroup.mk0 ⟨mumfordIdeal (f.map (residue O)) u₀ v₀,
          mumfordIdeal_mem_nonZeroDivisors _ hu₀.ne_zero v₀⟩) :
    ∃ (L : IntermediateField K (AlgebraicClosure K)) (_ : FiniteDimensional K L)
      (t : Finset (L × L)),
      (∀ p ∈ t, p.2 ^ 2 = ((f.map (algebraMap O K)).map (algebraMap K L)).eval p.1)
      ∧ (∀ p ∈ t, IsIntegral O p.1)
      ∧ (∀ p ∈ t, ∀ q ∈ t, redres O L p.1 = redres O L q.1 → p = q)
      ∧ u.map (algebraMap K L) = ∏ p ∈ t, (X - C p.1)
      ∧ (∀ p ∈ t, (v.map (algebraMap K L)).eval p.1 = p.2)
      ∧ u₀ = ∏ p ∈ t, (X - C (redres O L p.1))
      ∧ (∀ p ∈ t, v₀.eval (redres O L p.1) = redres O L p.2) := by
  classical
  -- represent the class by the split Mumford ideal over the splitting field of `u`
  obtain ⟨L, hFD, hsplit⟩ := exists_intermediateField_splits_base u
  set fL := (f.map (algebraMap O K)).map (algebraMap K L)
  set uL := u.map (algebraMap K L) with huLdef
  set vL := v.map (algebraMap K L)
  have huL0 : uL ≠ 0 := by
    simpa [huLdef, Polynomial.map_eq_zero_iff (algebraMap K L).injective] using hu.ne_zero
  have huLm : uL.Monic := hu.map _
  have hdvdL : uL ∣ vL ^ 2 - fL := by
    have h := Polynomial.map_dvd (algebraMap K L) hdvd
    rwa [Polynomial.map_sub, Polynomial.map_pow] at h
  set M := mumfordIdeal fL uL vL
  have hM0 : M ≠ 0 := mumfordIdeal_ne_zero fL huL0 vL
  have hss : SplitSupported M := splitSupported_mumfordIdeal huL0 hdvdL hsplit
  rw [redJ_mk0_mumfordIdeal_of_splits hf hdeg hu.ne_zero hdvd hsplit] at hred
  -- factor the split ideal into point ideals
  obtain ⟨sF, hIeq, hne, hle⟩ := exists_finset_maxPowDividing hM0
  set kf : IsDedekindDomain.HeightOneSpectrum (HypRing L fL) → ℕ :=
    fun w ↦ (Associates.mk w.asIdeal).count (Associates.mk M).factors with hkfdef
  have hpt : ∀ w : {z // z ∈ sF}, ∃ xw yw, ∃ _ : yw ^ 2 = fL.eval xw,
      w.1.asIdeal = pointIdeal fL xw yw :=
    fun w ↦ hss w.1.asIdeal w.1.isPrime w.1.ne_bot (hle w.1 w.2)
  choose xL yL hcv hpv using hpt
  have hfacM : M = ∏ w ∈ sF.attach, pointIdeal fL (xL w) (yL w) ^ kf w.1 := by
    conv_lhs => rw [← hIeq, ← Finset.prod_attach sF fun w ↦ w.maxPowDividing M]
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing]
    simp only [hkfdef]
    rw [hpv w]
  have hk0 : ∀ w : {z // z ∈ sF}, kf w.1 ≠ 0 := fun w h0 ↦
    (Associates.count_ne_zero_iff_dvd hM0 w.1.irreducible).mpr
      (Ideal.dvd_iff_le.mpr (hle w.1 w.2)) h0
  clear_value kf
  -- the linear factors of `u` over `L` and the interpolation values
  obtain ⟨huprod, hvvals⟩ := eq_of_mumfordIdeal_eq_prod_pointIdeal
    (fun w _ ↦ hcv w) huLm hdvdL hfacM
  have hsumL : ∑ w ∈ sF.attach, kf w.1 = u.natDegree := by
    have h1 := congrArg natDegree huprod
    rwa [natDegree_prod_X_sub_C_pow, huLdef, hu.natDegree_map] at h1
  -- reduce the factorization to the residue curve
  set sInt := sF.attach.filter (fun w ↦ IsIntegral O (xL w)) with hsIntdef
  have hbar : redIdealBar f L M
      = ∏ w ∈ sInt, pointIdeal (f.map (residue O)) (redres O L (xL w))
          (redres O L (yL w)) ^ kf w.1 :=
    hfacM ▸ redIdealBar_prod_pointIdeal f L _ _ fun w _ ↦ hcv w
  -- match against the good-position datum over the residue field
  have hcurveR : ∀ w ∈ sInt, redres O L (yL w) ^ 2
      = (f.map (residue O)).eval (redres O L (xL w)) := fun w hw ↦
    redres_sq_curve f L (hcv w) (Finset.mem_filter.mp hw).2
  have hsumInt : ∑ w ∈ sInt, kf w.1 ≤ u₀.natDegree :=
    le_trans (le_trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
      hsumL.le) hfull
  have hD0' : (∏ w ∈ sInt, pointIdeal (f.map (residue O)) (redres O L (xL w))
      (redres O L (yL w)) ^ kf w.1) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w _ ↦ pow_ne_zero _
      (pointIdeal_ne_zero _ _ _)
  obtain ⟨hAred, hyred⟩ := prod_pointIdeal_eq_reduced hcurveR hu₀ hv₀ hg₀ hd₀ hsumInt hD0'
    (((congrArg ClassGroup.mk0 (Subtype.ext hbar)).symm).trans hred)
  -- all points are integral, with multiplicity one and distinct reductions
  have hsumred : ∑ w ∈ sInt, kf w.1 = u₀.natDegree := by
    have h1 := congrArg natDegree hAred
    rwa [natDegree_prod_X_sub_C_pow] at h1
  have hallint : ∀ w ∈ sF.attach, IsIntegral O (xL w) := by
    intro w₀ hw₀
    by_contra hnint
    have hlt2 : ∑ w ∈ sInt, kf w.1 < ∑ w ∈ sF.attach, kf w.1 := by
      refine Finset.sum_lt_sum_of_subset (Finset.filter_subset _ _) hw₀
        (fun hmem ↦ hnint (Finset.mem_filter.mp hmem).2)
        (Nat.pos_of_ne_zero (hk0 w₀)) fun _ _ _ ↦ Nat.zero_le _
    rw [hsumred, hsumL] at hlt2
    exact absurd hfull (Nat.not_le.mpr hlt2)
  have hsIntall : sInt = sF.attach := by
    rw [hsIntdef]
    exact Finset.filter_true_of_mem hallint
  rw [hsIntall] at hAred hyred hsumred
  -- multiplicity one and distinct reductions, from squarefreeness
  obtain ⟨hk1, hxinj'⟩ := eq_one_and_inj_of_squarefree_prod_X_sub_C_pow
    (fun w _ ↦ hk0 w) (hAred ▸ hsq₀)
  have hxinj (w w' : {z // z ∈ sF}) (heq : redres O L (xL w) = redres O L (xL w')) : w = w' :=
    hxinj' w (Finset.mem_attach _ _) w' (Finset.mem_attach _ _) heq
  -- package the points
  have hpinj : ∀ w ∈ sF.attach, ∀ w' ∈ sF.attach,
      (xL w, yL w) = (xL w', yL w') → w = w' := by
    intro w _ w' _ h
    have h1 : xL w = xL w' := congrArg Prod.fst h
    exact hxinj w w' (by rw [h1])
  refine ⟨L, hFD, sF.attach.image fun w ↦ (xL w, yL w), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hp
    exact hcv w
  · intro p hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    exact hallint w hw
  · intro p hp q hq hpq
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨w', -, rfl⟩ := Finset.mem_image.mp hq
    rw [hxinj w w' hpq]
  · rw [Finset.prod_image hpinj]
    rw [huLdef] at huprod
    rw [← huprod]
    exact (Finset.prod_congr rfl fun w hw ↦ by rw [hk1 w hw, pow_one]).symm
  · intro p hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    exact hvvals w hw (hk0 w)
  · rw [Finset.prod_image hpinj, ← hAred]
    exact (Finset.prod_congr rfl fun w hw ↦ by rw [hk1 w hw, pow_one]).symm
  · intro p hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    exact hyred w hw (hk0 w)

open nonZeroDivisors in
/-- **Reduction commutes with reduced representatives at good position** (blueprint
`lem:reduce-commutes`, core form): if the reduction of the class of a reduced Mumford
datum `(u, v)` over `K` is represented by a reduced datum `(u₀, v₀)` over the residue
field with `u₀` squarefree of full degree, then `(u, v)` is integral and reduces exactly
to `(u₀, v₀)`. -/
theorem red_reducedRep_eq (hf : f.Monic) (hdeg : 0 < f.natDegree)
    {u v : K[X]} (hu : u.Monic) (hv : v.degree < u.degree)
    (hdvd : u ∣ v ^ 2 - f.map (algebraMap O K))
    {u₀ v₀ : (ResidueField O)[X]} (hu₀ : u₀.Monic) (hv₀ : v₀.degree < u₀.degree)
    (hg₀ : 2 * u₀.natDegree < (f.map (residue O)).natDegree)
    (hd₀ : u₀ ∣ v₀ ^ 2 - f.map (residue O)) (hsq₀ : Squarefree u₀)
    (hfull : u.natDegree ≤ u₀.natDegree)
    (hred : redJ (ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O K)) u v,
        mumfordIdeal_mem_nonZeroDivisors _ hu.ne_zero v⟩)
      = ClassGroup.mk0 ⟨mumfordIdeal (f.map (residue O)) u₀ v₀,
          mumfordIdeal_mem_nonZeroDivisors _ hu₀.ne_zero v₀⟩) :
    ∃ uO vO : O[X], uO.map (algebraMap O K) = u ∧ vO.map (algebraMap O K) = v
      ∧ uO.map (residue O) = u₀ ∧ vO.map (residue O) = v₀ := by
  classical
  obtain ⟨L, hFD, t, hcv, hint, hinj, huprod, hvvals, hu₀prod, hv₀vals⟩ :=
    red_reducedRep_points hf hdeg hu hdvd hu₀ hv₀ hg₀ hd₀ hsq₀ hfull hred
  -- the points in the integral closure
  set xC : {p // p ∈ t} → integralClosure O L := fun p ↦ ⟨p.1.1, hint p.1 p.2⟩
  set yC : {p // p ∈ t} → integralClosure O L := fun p ↦
    ⟨p.1.2, isIntegral_of_curve f L (hcv p.1 p.2) (hint p.1 p.2)⟩
  set UC : (integralClosure O L)[X] := ∏ p ∈ t.attach, (X - C (xC p)) with hUCdef
  have hUCm : UC.Monic := monic_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _
  have hUCmap : UC.map (algebraMap (integralClosure O L) L) = u.map (algebraMap K L) := by
    rw [hUCdef, Polynomial.map_prod, huprod,
      ← Finset.prod_attach t fun p ↦ (X - C p.1 : (L : Type _)[X])]
    refine Finset.prod_congr rfl fun p _ ↦ ?_
    rw [Polynomial.map_sub, map_X, map_C]
    rfl
  -- the coefficients of `u` lift to `O`
  obtain ⟨uO, huO⟩ := exists_map_eq_of_map_integralClosure hUCmap.symm
  -- interpolate `v` integrally through the points
  have hresC : ∀ p q : {z // z ∈ t}, p ≠ q →
      residue (integralClosure O L) (xC p) ≠ residue (integralClosure O L) (xC q) := by
    intro p q hne heq
    refine hne (Subtype.ext (hinj p.1 p.2 q.1 q.2 ?_))
    have h1 : redres O L (p.1.1 : L) = (integralClosureResidueEquiv O L).symm
        (residue (integralClosure O L) (xC p)) := redres_coe (t := xC p)
    have h2 : redres O L (q.1.1 : L) = (integralClosureResidueEquiv O L).symm
        (residue (integralClosure O L) (xC q)) := redres_coe (t := xC q)
    rw [h1, h2, heq]
  obtain ⟨vC, hvCdeg, hvCeval⟩ := exists_degree_lt_eval_eq
    (fun p q hne ↦ isUnit_sub_of_residue_ne (hresC p q hne)) yC
  rw [← Finset.attach_eq_univ, ← hUCdef] at hvCdeg
  -- `v` agrees with the integral interpolant over `L`
  have hxLinj : ∀ p q : {z // z ∈ t}, (p.1.1 : L) = q.1.1 → p = q := fun p q h ↦
    Subtype.ext (hinj p.1 p.2 q.1 q.2 (by rw [h]))
  have htcard : t.card = u.natDegree := by
    rw [← hu.natDegree_map (algebraMap K L), huprod]
    simp
  have hvLeq : v.map (algebraMap K L) = vC.map (algebraMap (integralClosure O L) L) := by
    refine eq_of_degree_sub_lt_card_of_eval_eq (x := fun p : {z // z ∈ t} ↦ (p.1.1 : L))
      hxLinj (fun p ↦ ?_) ?_
    · have h3 := congrArg (algebraMap (integralClosure O L) L) (hvCeval p)
      rw [← eval_map_apply] at h3
      rw [hvvals p.1 p.2]
      exact h3.symm
    · rw [Fintype.card_coe, htcard]
      refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
      · exact degree_map_le.trans_lt (hv.trans_eq (degree_eq_natDegree hu.ne_zero))
      · refine degree_map_le.trans_lt ?_
        calc vC.degree < UC.degree := hvCdeg
          _ = (u.natDegree : WithBot ℕ) := by
            rw [← hUCm.degree_map (algebraMap (integralClosure O L) L), hUCmap,
              hu.degree_map, degree_eq_natDegree hu.ne_zero]
  obtain ⟨vO, hvO⟩ := exists_map_eq_of_map_integralClosure hvLeq
  -- transport the data to the integral closure, then to the residue field
  have huOC : uO.map (algebraMap O (integralClosure O L)) = UC := by
    refine Polynomial.map_injective (algebraMap (integralClosure O L) L)
      Subtype.coe_injective ?_
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq O (integralClosure O L) L,
      IsScalarTower.algebraMap_eq O K L, ← Polynomial.map_map, huO, hUCmap]
  have hvOL : vO.map (algebraMap O L) = v.map (algebraMap K L) := by
    rw [IsScalarTower.algebraMap_eq O K L, ← Polynomial.map_map, hvO]
  have huOres : uO.map (residue O) = u₀ := by
    rw [hu₀prod, ← Finset.prod_attach t fun p ↦ (X - C (redres O L p.1) : (ResidueField O)[X])]
    exact map_residue_eq_prod_of_map_integralClosure O L (x := xC) (huOC.trans hUCdef)
  have hu₀card : t.card = u₀.natDegree := by
    rw [hu₀prod]
    simp
  have hvOres : vO.map (residue O) = v₀ := by
    refine eq_of_degree_sub_lt_card_of_eval_eq
      (x := fun p : {z // z ∈ t} ↦ redres O L (p.1.1 : L))
      (fun p q h ↦ Subtype.ext (hinj p.1 p.2 q.1 q.2 h)) (fun p ↦ ?_) ?_
    · have h1 : (vO.map (residue O)).eval (redres O L (p.1.1 : L))
          = redres O L ((vO.map (algebraMap O L)).eval (p.1.1 : L)) :=
        eval_map_residue_redres O L vO (xC p)
      rw [h1, hvOL, hvvals p.1 p.2, hv₀vals p.1 p.2]
    · rw [Fintype.card_coe, hu₀card]
      refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
      · refine degree_map_le.trans_lt ?_
        have h1 : vO.degree = v.degree := by
          rw [← hvO]
          exact (Polynomial.degree_map_eq_of_injective
            (FaithfulSMul.algebraMap_injective O K) vO).symm
        rw [h1]
        refine hv.trans_le ?_
        rw [degree_eq_natDegree hu.ne_zero]
        exact_mod_cast hfull
      · exact hv₀.trans_eq (degree_eq_natDegree hu₀.ne_zero)
  exact ⟨uO, vO, huO, hvO, huOres, hvOres⟩

/-- **The reduction of the class of an integral Mumford datum is the class of the reduced
datum**, provided the reduced `u`-polynomial is squarefree: split `u` over `L` with
integral roots, factor the Mumford ideal into point ideals on both levels, and match the
reductions. -/
theorem redJ_mk0_mumford (hf : f.Monic) (hdeg : 0 < f.natDegree)
    {uO vO : O[X]} (hu : uO.Monic) (hdvd : uO ∣ vO ^ 2 - f)
    (hsq : Squarefree (uO.map (residue O))) :
    redJ (ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O K))
        (uO.map (algebraMap O K)) (vO.map (algebraMap O K)),
      mumfordIdeal_mem_nonZeroDivisors _ (hu.map (algebraMap O K)).ne_zero _⟩)
      = ClassGroup.mk0 ⟨mumfordIdeal (f.map (residue O)) (uO.map (residue O))
          (vO.map (residue O)),
        mumfordIdeal_mem_nonZeroDivisors _ (hu.map (residue O)).ne_zero _⟩ := by
  classical
  -- separability of `u`, lifted from squarefreeness of its reduction
  have hsepO : uO.Separable :=
    separable_of_map_residue hu (PerfectField.separable_iff_squarefree.mpr hsq)
  -- split `u` over `L`
  set uK := uO.map (algebraMap O K) with huKdef
  obtain ⟨L, hFD, hsplit⟩ := exists_intermediateField_splits_base uK
  set fL := (f.map (algebraMap O K)).map (algebraMap K L) with hfLdef
  set uL := uK.map (algebraMap K L) with huLdef
  set vL := (vO.map (algebraMap O K)).map (algebraMap K L) with hvLdef
  have huLm : uL.Monic := (hu.map _).map _
  have hsepL : uL.Separable := hsepO.map.map
  have hnodup : uL.roots.Nodup := Polynomial.nodup_roots hsepL
  set t : Finset L := uL.roots.toFinset with htdef
  have htval : t.val = uL.roots := by rw [htdef, Multiset.toFinset_val, hnodup.dedup]
  have huLprod : uL = ∏ x ∈ t, (X - C x) := by
    nth_rw 1 [hsplit.eq_prod_roots_of_monic huLm]
    rw [Finset.prod_eq_multiset_prod, htval]
  -- the roots are integral over `O`
  have huLO : uL = uO.map (algebraMap O L) := by
    rw [huLdef, huKdef, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hroot : ∀ x ∈ t, uL.eval x = 0 := fun x hx ↦
    isRoot_of_mem_roots (Multiset.mem_toFinset.mp hx)
  have hint : ∀ x ∈ t, IsIntegral O x := by
    intro x hx
    refine ⟨uO, hu, ?_⟩
    have h := hroot x hx
    rwa [huLO, eval_map] at h
  -- the curve values at the roots
  have hdvdL : uL ∣ vL ^ 2 - fL := by
    have h := Polynomial.map_dvd (algebraMap K L)
      (Polynomial.map_dvd (algebraMap O K) hdvd)
    rwa [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_pow,
      ← huKdef, ← hvLdef, ← hfLdef, ← huLdef] at h
  have hcv : ∀ x ∈ t, (vL.eval x) ^ 2 = fL.eval x := by
    intro x hx
    have h := eval_eq_zero_of_dvd_of_eval_eq_zero hdvdL (hroot x hx)
    rwa [eval_sub, eval_pow, sub_eq_zero] at h
  -- the split Mumford ideal factors into point ideals
  have hfacL : mumfordIdeal fL uL vL = ∏ x ∈ t, pointIdeal fL x (vL.eval x) :=
    mumfordIdeal_eq_prod_pointIdeal hcv (fun i _ j _ h ↦ h) huLprod hdvdL fun _ _ ↦ rfl
  -- reduce the factorization
  have hbar : redIdealBar f L (mumfordIdeal fL uL vL)
      = ∏ x ∈ t, pointIdeal (f.map (residue O)) (redres O L x)
          (redres O L (vL.eval x)) := by
    rw [hfacL, redIdealBar_prod f L _ _ fun x _ ↦ pointIdeal_ne_zero fL _ _]
    exact Finset.prod_congr rfl fun x hx ↦
      redIdealBar_pointIdeal f L (hcv x hx) (hint x hx)
  -- transport the factorization of `u` to the residue field
  set xC : {z // z ∈ t} → integralClosure O L := fun x ↦ ⟨x.1, hint x.1 x.2⟩
  set UC : (integralClosure O L)[X] := ∏ x ∈ t.attach, (X - C (xC x)) with hUCdef
  have hUCmap : UC.map (algebraMap (integralClosure O L) L) = uL := by
    rw [hUCdef, Polynomial.map_prod, huLprod,
      ← Finset.prod_attach t fun x ↦ (X - C x : L[X])]
    refine Finset.prod_congr rfl fun x _ ↦ ?_
    rw [Polynomial.map_sub, map_X, map_C]
    rfl
  have huOC : uO.map (algebraMap O (integralClosure O L)) = UC := by
    refine Polynomial.map_injective (algebraMap (integralClosure O L) L)
      Subtype.coe_injective ?_
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq O (integralClosure O L) L,
      hUCmap, huLO]
  have huOres : uO.map (residue O) = ∏ x ∈ t.attach, (X - C (redres O L (x.1 : L))) :=
    map_residue_eq_prod_of_map_integralClosure O L (x := xC) (huOC.trans hUCdef)
  have huOresattach : uO.map (residue O) = ∏ x ∈ t, (X - C (redres O L x)) := by
    rw [huOres, ← Finset.prod_attach t fun x ↦ (X - C (redres O L x) :
      (ResidueField O)[X])]
  -- distinct reductions, from squarefreeness of the reduced `u`
  have hrinj := separable_prod_X_sub_C_iff'.mp
    (huOresattach ▸ PerfectField.separable_iff_squarefree.mpr hsq)
  -- the reduced factorization is the reduced Mumford ideal
  have hdvdres : uO.map (residue O) ∣ (vO.map (residue O)) ^ 2 - f.map (residue O) := by
    have h := Polynomial.map_dvd (residue O) hdvd
    rwa [Polynomial.map_sub, Polynomial.map_pow] at h
  have hcurveres : ∀ x ∈ t, redres O L (vL.eval x) ^ 2
      = (f.map (residue O)).eval (redres O L x) := fun x hx ↦
    redres_sq_curve f L (hcv x hx) (hint x hx)
  have hvLO : vL = vO.map (algebraMap O L) := by
    rw [hvLdef, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hvals : ∀ x ∈ t, (vO.map (residue O)).eval (redres O L x)
      = redres O L (vL.eval x) := fun x hx ↦ by
    rw [hvLO]
    exact eval_map_residue_redres O L vO ⟨x, hint x hx⟩
  have hfacres : mumfordIdeal (f.map (residue O)) (uO.map (residue O))
      (vO.map (residue O))
      = ∏ x ∈ t, pointIdeal (f.map (residue O)) (redres O L x)
          (redres O L (vL.eval x)) :=
    mumfordIdeal_eq_prod_pointIdeal hcurveres hrinj huOresattach hdvdres hvals
  -- assemble the reduction pair
  rw [redJ_mk0_mumfordIdeal_of_splits hf hdeg (hu.map (algebraMap O K)).ne_zero
    (map_dvd_sq_sub (algebraMap O K) hdvd) hsplit]
  refine congrArg ClassGroup.mk0 (Subtype.ext ?_)
  change redIdealBar f L (mumfordIdeal fL uL vL)
    = mumfordIdeal (f.map (residue O)) (uO.map (residue O)) (vO.map (residue O))
  rw [hbar, hfacres]

end Main

end ChabautyColeman

end
