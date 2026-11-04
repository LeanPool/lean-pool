/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Analysis.PrimeCutoff
public import LeanPool.CCDN.AuxiliaryPolynomial.ConstantLeadingBadReduction
public import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceBadReduction
public import LeanPool.CCDN.Height.IntegerCoefficientHeight
public import LeanPool.CCDN.Plane.FiniteFieldConstants
import LeanPool.CCDN.AuxiliaryPolynomial.GeneralBadReduction
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Noether.ShearNormalization
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-! Finite bad-prime sets for plane equations, with coefficient-height
charge bounds and irreducible good reductions. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Real

/-- A multivariate polynomial over a field whose image under a field homomorphism is irreducible
is itself irreducible. -/
lemma mvPolynomial_irreducible_of_field_map
    {F K σ : Type*} [Field F] [Field K] (φ : F →+* K)
    (f : MvPolynomial σ F) (hf : Irreducible (MvPolynomial.map φ f)) : Irreducible f := by
  have hunit (q : MvPolynomial σ F) (hq : IsUnit (MvPolynomial.map φ q)) : IsUnit q := by
    obtain ⟨hc, hd⟩ := MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hq
    have he : (MvPolynomial.map φ q).totalDegree = q.totalDegree :=
      MvPolynomial.totalDegree_map_of_injective φ.injective q
    apply MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mpr
    refine ⟨isUnit_iff_ne_zero.mpr ?_, he ▸ hd⟩
    intro hz
    apply hc.ne_zero
    rw [MvPolynomial.coeff_map, hz, map_zero]
  refine ⟨fun h => hf.not_isUnit (h.map (MvPolynomial.map φ)), ?_⟩
  intro g h he
  have hh := hf.isUnit_or_isUnit (by rw [he, map_mul])
  exact hh.imp (hunit g) (hunit h)

/-- The total degree of the bivariate model `bivariatePolynomialEquiv R f` of a polynomial `f` in
two variables equals the total degree of `f`. -/
lemma bivariateTotalDegree_equiv {R : Type*} [CommRing R]
    (f : MvPolynomial (Fin 2) R) :
    bivariateTotalDegree (bivariatePolynomialEquiv R f) = f.totalDegree := by
  simp only [bivariateTotalDegree, AlgEquiv.symm_apply_apply]

/-- Bad reduction of the bivariate model of a plane equation is bad reduction of the
equation itself. -/
private lemma bivariateBadReduction_iff_hypersurfaceBadReduction (f : MvPolynomial (Fin 2) ℤ)
    (p : ℕ) :
    BivariateBadReduction (bivariatePolynomialEquiv ℤ f) f.totalDegree p ↔
      HypersurfaceBadReduction f p := by
  apply exists_congr
  intro hp
  let : Fact p.Prime := ⟨hp⟩
  let K := AlgebraicClosure (ZMod p)
  change bivariateTotalDegree (bivariateMap (Int.castRingHom K) (bivariatePolynomialEquiv ℤ f)) ≠
      f.totalDegree ∨
      ¬Irreducible (bivariateMap (Int.castRingHom K) (bivariatePolynomialEquiv ℤ f)) ↔
    (MvPolynomial.map (Int.castRingHom K) f).totalDegree ≠ f.totalDegree ∨
      ¬Irreducible (MvPolynomial.map (Int.castRingHom K) f)
  rw [bivariatePolynomialEquiv_map, bivariateTotalDegree_equiv,
    MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv K)]

/-- Good reduction implies the irreducibility over the prime field needed by the singular
determinant estimate. -/
lemma irreducible_reduction_of_not_hypersurfaceBadReduction {σ : Type*}
    (f : MvPolynomial σ ℤ) (p : ℕ) [Fact p.Prime]
    (hf : ¬HypersurfaceBadReduction f p) :
    Irreducible (MvPolynomial.map (Int.castRingHom (ZMod p)) f) := by
  have h := ((not_hypersurfaceBadReduction_iff f p).mp hf).2
  apply mvPolynomial_irreducible_of_field_map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
  have he : (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).comp (Int.castRingHom (ZMod p)) =
      Int.castRingHom (AlgebraicClosure (ZMod p)) := by ext; simp
  simpa only [MvPolynomial.map_map, he] using h

/-- The complete set of bad primes above `stepanovThreshold d` is finite and has the
required charge bound. Good reductions outside this set are
irreducible reductions, not an additional input. -/
theorem exists_plane_bad_prime_set
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (f : MvPolynomial (Fin 2) ℤ) (hd : 0 < f.totalDegree)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) f))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : CoefficientHeightLE f H) :
    ∃ B : Finset ℕ,
      (∀ p, p ∈ B ↔
        stepanovThreshold (f.totalDegree : ℝ) < (p : ℝ) ∧ HypersurfaceBadReduction f p) ∧
      (∑ p ∈ B, Real.log p / p) ≤
        Real.log (1 + Real.log H / (f.totalDegree : ℝ) ^ 2) +
          Real.log 7 + 2 * mertensError + 1 := by
  classical
  let q := bivariatePolynomialEquiv ℤ f
  have hqdeg : bivariateTotalDegree q = f.totalDegree := bivariateTotalDegree_equiv f
  have hqir : Irreducible (bivariateMap (Int.castRingHom F) q) := by
    rw [bivariatePolynomialEquiv_map, MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv F)]
    exact hir
  have hqcoeff : BivariateCoefficientBound q H := by
    intro i j
    rw [bivariatePolynomialEquiv_coeff]
    exact hcoeff _
  obtain ⟨D, hD, _, hdiv⟩ :=
    exists_plane_bad_prime_witness f.totalDegree hd q hqdeg hqir H hH hqcoeff
  let B := D.natAbs.primeFactors.filter
    (fun p : ℕ => stepanovThreshold (f.totalDegree : ℝ) < (p : ℝ) ∧ HypersurfaceBadReduction f p)
  have hd1 : (1 : ℝ) ≤ f.totalDegree := by exact_mod_cast hd
  have hcut : (f.totalDegree : ℝ) ≤ stepanovThreshold (f.totalDegree : ℝ) := by
    unfold stepanovThreshold
    nlinarith [sq_nonneg ((f.totalDegree : ℝ) ^ 2 - 1)]
  have hmem (p : ℕ) : p ∈ B ↔
      stepanovThreshold (f.totalDegree : ℝ) < (p : ℝ) ∧ HypersurfaceBadReduction f p := by
    constructor
    · exact fun h => (Finset.mem_filter.mp h).2
    · intro hp
      apply Finset.mem_filter.mpr
      refine ⟨?_, hp⟩
      apply Nat.mem_primeFactors.mpr
      refine ⟨hp.2.choose, ?_, Int.natAbs_ne_zero.mpr hD.ne'⟩
      have hz := hdiv p (by exact_mod_cast hcut.trans_lt hp.1)
        ((bivariateBadReduction_iff_hypersurfaceBadReduction f p).mpr hp.2)
      simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hz
  refine ⟨B, hmem, ?_⟩
  exact plane_geometric_bad_prime_charge f.totalDegree hd q hqdeg hqir H hH hqcoeff B
    (fun p hp => (bivariateBadReduction_iff_hypersurfaceBadReduction f p).mpr ((hmem p).mp hp).2)
    (fun p hp => ((hmem p).mp hp).1)

end
end CCDN
