/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.RedJ.ReductionIdeal
public import LeanPool.HyperellipticCurves.Specialization.FiberSum

/-!
# The reduction of an ideal of the coordinate ring to the residue curve

For an ideal `I` of the coordinate ring `A_K` over the fraction field of a DVR `O` with
algebraically closed residue field, `ChabautyColeman.redIdeal f I` is the ideal of the
residue curve attached to the divisor `∑_{P_bar} fiberCount(I)(P_bar)·P_bar` — the pointwise
reduction
of the divisor of `I`, with only rational points of the disks counted (which is the whole
divisor when the data of `I` splits over `K`).

Main properties: multiplicativity (`ChabautyColeman.redIdeal_mul`), the values on point
ideals (`ChabautyColeman.redIdeal_pointIdeal_of_redPoint_eq` — reduction of a point class is
the class of the reduced point), and, via `thm:spec` in fiber-count form, the reduction of a
split principal ideal is the principal ideal of the reduced function
(`ChabautyColeman.redIdeal_span`).

Together these constitute the local (single-field) content of `def:redJ`/`thm:redJ-hom`.
-/

@[expose] public section

open Polynomial IsLocalRing

namespace ChabautyColeman

/-- Two affine curve points with equal coordinates are equal. -/
theorem CurvePoint.affine_congr {K : Type*} [Field K] {g : K[X]} {x y x' y' : K}
    (hx : x = x') (hy : y = y') (h : y ^ 2 = g.eval x) (h' : y' ^ 2 = g.eval x') :
    CurvePoint.affine x y h = CurvePoint.affine x' y' h' := by
  subst hx hy; rfl

section RedIdeal

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
  (f : O[X])

/-- The reduction multiplicity function of an ideal `I ⊆ A_K`: at each affine point of the
residue curve, the total multiplicity of `I` over its residue disk. -/
noncomputable def redMult (I : Ideal (HypRing K (f.map (algebraMap O K))))
    (p : AffinePair (f.map (residue O))) : ℕ :=
  fiberCount f I (.affine p.1.1 p.1.2 p.2)

theorem redMult_apply (I : Ideal (HypRing K (f.map (algebraMap O K))))
    (p : AffinePair (f.map (residue O))) :
    redMult f I p = fiberCount f I (.affine p.1.1 p.1.2 p.2) :=
  rfl

/-- The reduction of an ideal `I ⊆ A_K` to the residue curve: the ideal of the divisor
`∑_{P_bar} redMult(I)(P_bar)·P_bar` on the residue curve. -/
noncomputable def redIdeal (I : Ideal (HypRing K (f.map (algebraMap O K)))) :
    Ideal (HypRing (ResidueField O) (f.map (residue O))) :=
  pointIdealProd (redMult f I)

variable {f}

theorem redIdeal_ne_zero [Fact (Odd (f.map (residue O)).natDegree)]
    (I : Ideal (HypRing K (f.map (algebraMap O K)))) : redIdeal f I ≠ 0 :=
  pointIdealProd_ne_zero _

variable [NeZero (2 : K)] [Fact (Odd (f.map (algebraMap O K)).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O K)))]

/-- The reduction multiplicity function of a nonzero ideal has finite support: each point in
the support singles out a rational point of its disk whose maximal ideal divides `I`. -/
theorem finite_support_redMult {I : Ideal (HypRing K (f.map (algebraMap O K)))} (hI : I ≠ 0) :
    (Function.support (redMult f I)).Finite := by
  classical
  have key : ∀ p : AffinePair (f.map (residue O)), redMult f I p ≠ 0 →
      ∃ (x y : K) (h : y ^ 2 = (f.map (algebraMap O K)).eval x),
        redPoint (.affine x y h) = .affine p.1.1 p.1.2 p.2 ∧
        pointIdeal (f.map (algebraMap O K)) x y ∣ I := by
    intro p hp
    rw [redMult, fiberCount] at hp
    have hex : ∃ P : ResidueDisk (K := K) (CurvePoint.affine p.1.1 p.1.2 p.2),
        (emultiplicity (pointIdeal (f.map (algebraMap O K)) P.1.xCoord P.1.yCoord)
          I).toNat ≠ 0 := by
      by_contra! hall
      exact hp (finsum_eq_zero_of_forall_eq_zero hall)
    obtain ⟨⟨P₀, hP₀⟩, hne⟩ := hex
    obtain ⟨x, y, h, rfl, -, -, -, -⟩ := exists_eq_affine_of_redPoint_eq_affine hP₀
    simp only [CurvePoint.xCoord_affine, CurvePoint.yCoord_affine] at hne
    refine ⟨x, y, h, hP₀, ?_⟩
    by_contra hnd
    exact hne (by rw [emultiplicity_eq_zero.mpr hnd]; rfl)
  choose χx χy χh hred hdvd using key
  refine Set.Finite.of_finite_image (f := fun p ↦
    if hp : redMult f I p ≠ 0 then pointIdeal (f.map (algebraMap O K)) (χx p hp) (χy p hp)
    else ⊤) ?_ ?_
  · refine Set.Finite.subset ((Ideal.finite_factors hI).image
      IsDedekindDomain.HeightOneSpectrum.asIdeal) ?_
    rintro J ⟨p, hp, rfl⟩
    have hp' : redMult f I p ≠ 0 := hp
    simp only [dite_eq_left hp']
    exact ⟨pointSpectrum (χh p hp'), hdvd p hp', rfl⟩
  · rintro p hp q hq hpq
    have hp' : redMult f I p ≠ 0 := hp
    have hq' : redMult f I q ≠ 0 := hq
    simp only [dite_eq_left hp', dite_eq_left hq'] at hpq
    obtain ⟨h1, h2⟩ := (pointIdeal_eq_pointIdeal_iff (χh p hp')).mp hpq
    have hpoint := CurvePoint.affine_congr h1 h2 (χh p hp') (χh q hq')
    have heq : (CurvePoint.affine p.1.1 p.1.2 p.2 :
        CurvePoint (ResidueField O) (f.map (residue O))) = .affine q.1.1 q.1.2 q.2 :=
      (hred p hp').symm.trans ((congrArg redPoint hpoint).trans (hred q hq'))
    simp only [CurvePoint.affine.injEq] at heq
    exact Subtype.ext (Prod.ext heq.1 heq.2)

/-- Reduction multiplicities are additive in the ideal. -/
theorem redMult_mul {I J : Ideal (HypRing K (f.map (algebraMap O K)))} (hI : I ≠ 0)
    (hJ : J ≠ 0) (p : AffinePair (f.map (residue O))) :
    redMult f (I * J) p = redMult f I p + redMult f J p :=
  fiberCount_mul p.2 hI hJ

/-- The reduction multiplicity of the maximal ideal of an integral point at its own
reduction is `1`. -/
theorem redMult_pointIdeal_of_redPoint_eq {x y : K}
    (hxy : y ^ 2 = (f.map (algebraMap O K)).eval x) {ab bb : ResidueField O}
    {hb : bb ^ 2 = (f.map (residue O)).eval ab}
    (hred : redPoint (.affine x y hxy) = .affine ab bb hb) :
    redMult f (pointIdeal (f.map (algebraMap O K)) x y) ⟨(ab, bb), hb⟩ = 1 :=
  fiberCount_pointIdeal_of_redPoint_eq hxy hred

/-- Reduction of ideals is multiplicative. -/
theorem redIdeal_mul {I J : Ideal (HypRing K (f.map (algebraMap O K)))} (hI : I ≠ 0)
    (hJ : J ≠ 0) : redIdeal f (I * J) = redIdeal f I * redIdeal f J := by
  rw [redIdeal, redIdeal, redIdeal, _root_.funext (redMult_mul hI hJ),
    pointIdealProd_add (finite_support_redMult hI) (finite_support_redMult hJ)]

/-- **Reduction of a point class is the class of the reduced point** (ideal level): the
reduction of the maximal ideal of an integral point is the maximal ideal of its reduction. -/
theorem redIdeal_pointIdeal_of_redPoint_eq {x y : K}
    (hxy : y ^ 2 = (f.map (algebraMap O K)).eval x) {ab bb : ResidueField O}
    {hb : bb ^ 2 = (f.map (residue O)).eval ab}
    (hred : redPoint (.affine x y hxy) = .affine ab bb hb) :
    redIdeal f (pointIdeal (f.map (algebraMap O K)) x y)
      = pointIdeal (f.map (residue O)) ab bb := by
  rw [redIdeal, pointIdealProd_eq_pow ⟨(ab, bb), hb⟩ ?_,
    redMult_pointIdeal_of_redPoint_eq hxy hred, pow_one]
  intro p hp
  refine fiberCount_pointIdeal_of_redPoint_ne hxy fun h ↦ hp ?_
  have heq := hred.symm.trans h
  simp only [CurvePoint.affine.injEq] at heq
  exact Subtype.ext (Prod.ext heq.1.symm heq.2.symm)

/-- A point reducing to `∞_bar` contributes trivially: the reduction of its maximal ideal is the
unit ideal. -/
theorem redIdeal_pointIdeal_of_redPoint_eq_infinity {x y : K}
    (hxy : y ^ 2 = (f.map (algebraMap O K)).eval x)
    (hred : redPoint (.affine x y hxy) = .infinity) :
    redIdeal f (pointIdeal (f.map (algebraMap O K)) x y) = ⊤ :=
  pointIdealProd_eq_top fun p ↦
    fiberCount_pointIdeal_of_redPoint_ne hxy (hred ▸ fun h ↦ by simp at h)

/-- The reduction of the unit ideal is the unit ideal. -/
theorem redIdeal_top :
    redIdeal f (⊤ : Ideal (HypRing K (f.map (algebraMap O K)))) = ⊤ :=
  pointIdealProd_eq_top fun p ↦ fiberCount_top p.2

/-- The reduction of `(x - a)` for non-integral `a` is the unit ideal. -/
theorem redIdeal_span_X_sub_C_of_not_isIntegral {a : K} (ha : ¬IsIntegral O a) :
    redIdeal f (Ideal.span {algebraMap K[X] (HypRing K (f.map (algebraMap O K))) (X - C a)}) =
      ⊤ :=
  pointIdealProd_eq_top fun p ↦ fiberCount_span_X_sub_C_of_not_isIntegral ha p.2

end RedIdeal

section Engine

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
  {f P Q : O[X]}
  [NeZero (2 : K)] [Fact (Odd (f.map (algebraMap O K)).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O K)))]
  [NeZero (2 : ResidueField O)] [Fact (Odd (f.map (residue O)).natDegree)]
  [Fact (Squarefree (f.map (residue O)))] [IsAlgClosed (ResidueField O)]

/-- **`thm:spec` at the level of reduced ideals**: the reduction of a split principal ideal
is the principal ideal of the reduced function. -/
theorem redIdeal_span (hf : f.Monic) (hdeg : 0 < f.natDegree) (h2 : IsUnit (2 : O))
    (hN : (P ^ 2 - f * Q ^ 2).map (residue O) ≠ 0)
    (hcop : IsCoprime (P.map (algebraMap O K)) (Q.map (algebraMap O K)))
    (hsq : ∀ (ω : O), f.eval ω = 0 → ∀ w : maximalIdeal O,
      ((P ^ 2 - f * Q ^ 2).map (algebraMap O K)).eval (algebraMap O K (ω + w.1)) = 0 →
        ∃ y ∈ maximalIdeal O, y ^ 2 = f.eval (ω + w.1))
    (hsplit : ((P ^ 2 - f * Q ^ 2).map (algebraMap O K)).Splits) :
    redIdeal f (Ideal.span {(⟨P.map (algebraMap O K), Q.map (algebraMap O K)⟩ :
        HypRing K (f.map (algebraMap O K)))})
      = Ideal.span {(⟨P.map (residue O), Q.map (residue O)⟩ :
          HypRing (ResidueField O) (f.map (residue O)))} := by
  have hzbar : (⟨P.map (residue O), Q.map (residue O)⟩ :
      HypRing (ResidueField O) (f.map (residue O))) ≠ 0 := by
    intro h0
    obtain ⟨hre, him⟩ := QuadraticAlgebra.mk_eq_zero.mp h0
    refine hN ?_
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_pow,
      hre, him]
    ring
  have hspan : redMult f (Ideal.span {(⟨P.map (algebraMap O K),
        Q.map (algebraMap O K)⟩ : HypRing K (f.map (algebraMap O K)))})
      = fun p : AffinePair (f.map (residue O)) ↦
        (emultiplicity (pointIdeal (f.map (residue O)) p.1.1 p.1.2)
          (Ideal.span {(⟨P.map (residue O), Q.map (residue O)⟩ :
            HypRing (ResidueField O) (f.map (residue O)))})).toNat :=
    _root_.funext fun p ↦ fiberCount_span hf hdeg h2 hN hcop hsq hsplit p.2
  rw [redIdeal, hspan, pointIdealProd_span hzbar]

end Engine

end ChabautyColeman

end
