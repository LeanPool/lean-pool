/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCenteringIdentity
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCenteringAdjointIdentity
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCenteringEstimate
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCenteringSmallness

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastCenteringCap

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The centering cap

The two centering pairings of the one-step hub, at the calibrated loads of
the response metric, are second order in the hatted contrast defect: the
closed Schur forms of the pairing identities are estimated by the generic
centering estimate, whose smallness clauses are supplied by the hatted
contrast of the annealed block alone.  The cap constant is `3d + 4`, half
the generic constant.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- **The centering cap.**  Both centering pairings at the calibrated loads
are bounded by `(3d + 4)·ε²` whenever `d·(hat − 1) ≤ ε ≤ 1`. -/
theorem centering_pairing_caps [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (U : Book.Ch02.Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    {S SStar K : Mat d} (hS : S.PosDef) (hStar : SStar.PosDef)
    (hE : toFullBlockMat (annealedBlock P (U : Set (Vec d))) =
      schurBlock S SStar K)
    {eps : ℝ} (hpos : 0 < eps) (heps1 : eps ≤ 1)
    (htr : (d : ℝ) * (schurHattedContrast S SStar - 1) ≤ eps)
    (e : Vec d) (he : e ⬝ᵥ e = 1) :
    (1 / 2 : ℝ) *
        |vecDot
          (fun i ↦ ∫ a, averageGradient U
            ((a.subSkew (Response.responseSkew K)
              (Response.is_skew_mat_response_skew K)).coeffOn U)
            (Response.centeredResponseOptimizer U
              (a.subSkew (Response.responseSkew K)
                (Response.is_skew_mat_response_skew K))
              (Response.centeredResponseLoadP S SStar K e)
              (Response.centeredResponseLoadQ S SStar K e)) i ∂P)
          (fun i ↦ ∫ a, averageFlux U
            ((a.subSkew (Response.responseSkew K)
              (Response.is_skew_mat_response_skew K)).coeffOn U)
            (Response.centeredResponseOptimizer U
              (a.subSkew (Response.responseSkew K)
                (Response.is_skew_mat_response_skew K))
              (Response.centeredResponseLoadP S SStar K e)
              (Response.centeredResponseLoadQ S SStar K e)) i ∂P)| ≤
      (3 * (d : ℝ) + 4) * eps ^ 2 ∧
    (1 / 2 : ℝ) *
        |vecDot
          (fun i ↦ ∫ a, averageGradient U
            ((a.subSkew (Response.responseSkew K)
              (Response.is_skew_mat_response_skew K)).transpose.coeffOn U)
            (Response.centeredAdjointOptimizer U
              (a.subSkew (Response.responseSkew K)
                (Response.is_skew_mat_response_skew K))
              (Response.centeredResponseLoadP S SStar K e)
              (Response.centeredResponseLoadQ S SStar K e)) i ∂P)
          (fun i ↦ ∫ a, averageFlux U
            ((a.subSkew (Response.responseSkew K)
              (Response.is_skew_mat_response_skew K)).transpose.coeffOn U)
            (Response.centeredAdjointOptimizer U
              (a.subSkew (Response.responseSkew K)
                (Response.is_skew_mat_response_skew K))
              (Response.centeredResponseLoadP S SStar K e)
              (Response.centeredResponseLoadQ S SStar K e)) i ∂P)| ≤
      (3 * (d : ℝ) + 4) * eps ^ 2 := by
  classical
  set ksym : Mat d := Response.responseSymmetric K with hksym
  set p : Vec d := Response.centeredResponseLoadP S SStar K e with hp
  set r : Vec d := Response.centeredResponseLoadQ S SStar K e with hr
  have hkherm : ksymᴴ = ksym := by
    rw [hksym]
    exact Response.responseSymmetric_isHermitian K
  have hStarInvHerm : (SStar⁻¹)ᴴ = SStar⁻¹ := hStar.inv.isHermitian
  -- the loads in the estimate's spelling
  have hloadP : p =
      matSqrt (matGeomMean (S + ksym * SStar⁻¹ * ksym) SStar)⁻¹ *ᵥ e := by
    rw [hp, hksym, Response.centeredResponseLoadP, Response.centeredResponseMetric,
      Response.centeredResponseBlock, Response.responseSymmetric_isHermitian]
  have hloadQ : r =
      matSqrt (matGeomMean (S + ksym * SStar⁻¹ * ksym) SStar) *ᵥ e := by
    rw [hr, hksym, Response.centeredResponseLoadQ, Response.centeredResponseMetric,
      Response.centeredResponseBlock, Response.responseSymmetric_isHermitian]
  -- the smallness pack
  obtain ⟨horder, hgapM, hskewM0, htrGap, htrSkew0⟩ :=
    centering_smallness_supply U hint hS hStar hE hpos htr
  have hskewM : ksym * SStar⁻¹ * ksym ≤ (eps ^ 2 / 4) • SStar := by
    rw [hksym]
    exact hskewM0
  have htrSkewk : Matrix.trace (ksym * SStar⁻¹ * ksym * SStar⁻¹) ≤
      (d : ℝ) * eps ^ 2 / 4 := by
    rw [hksym]
    exact htrSkew0
  -- the shared dot-product bridges
  have hgstar : (Response.responseSkew K)ᴴ = -Response.responseSkew K := by
    have hg := Response.is_skew_mat_response_skew K
    rwa [conjTranspose_eq_transpose']
  have hterm4 : ∀ w : Vec d,
      w ⬝ᵥ (SStar⁻¹ * K * SStar⁻¹) *ᵥ w =
        (SStar⁻¹ *ᵥ w) ⬝ᵥ ksym *ᵥ (SStar⁻¹ *ᵥ w) := by
    intro w
    have h1 : (SStar⁻¹ * K * SStar⁻¹) *ᵥ w =
        SStar⁻¹ *ᵥ (K *ᵥ (SStar⁻¹ *ᵥ w)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [h1, ← mulVec_dotProduct_symm hStarInvHerm]
    have hK : K = ksym + Response.responseSkew K := by
      rw [hksym]
      have h := Response.sub_responseSkew K
      rw [← h]
      abel
    rw [hK, Matrix.add_mulVec, dotProduct_add,
      Response.dotProduct_mulVec_of_skew hgstar, add_zero]
  have hterm5 : ∀ w : Vec d,
      ((SStar⁻¹ * S) *ᵥ p) ⬝ᵥ w = (S *ᵥ p) ⬝ᵥ (SStar⁻¹ *ᵥ w) := by
    intro w
    rw [← Matrix.mulVec_mulVec, mulVec_dotProduct_symm hStarInvHerm]
  -- the primal estimate
  have hest := centering_generic_estimate hS hStar hkherm
    (le_of_lt hpos) heps1 horder hgapM hskewM htrGap htrSkewk e he
  -- the adjoint estimate at the negated symmetric coordinate
  have hknegherm : (-ksym)ᴴ = -ksym := by
    rw [Matrix.conjTranspose_neg, hkherm]
  have hnegconj : -ksym * SStar⁻¹ * -ksym = ksym * SStar⁻¹ * ksym := by
    rw [Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  have hskewMneg : -ksym * SStar⁻¹ * -ksym ≤ (eps ^ 2 / 4) • SStar := by
    rw [hnegconj]
    exact hskewM
  have htrSkewneg : Matrix.trace (-ksym * SStar⁻¹ * -ksym * SStar⁻¹) ≤
      (d : ℝ) * eps ^ 2 / 4 := by
    rw [hnegconj]
    exact htrSkewk
  have hestA := centering_generic_estimate hS hStar hknegherm
    (le_of_lt hpos) heps1 horder hgapM hskewMneg htrGap htrSkewneg e he
  rw [hnegconj] at hestA
  have hslot : matSqrt (matGeomMean (S + ksym * SStar⁻¹ * ksym) SStar) *ᵥ e +
      -ksym *ᵥ (matSqrt (matGeomMean (S + ksym * SStar⁻¹ * ksym) SStar)⁻¹ *ᵥ
        e) =
      matSqrt (matGeomMean (S + ksym * SStar⁻¹ * ksym) SStar) *ᵥ e -
        ksym *ᵥ (matSqrt (matGeomMean (S + ksym * SStar⁻¹ * ksym) SStar)⁻¹ *ᵥ
          e) := by
    rw [Matrix.neg_mulVec, ← sub_eq_add_neg]
  rw [hslot] at hestA
  have hquadneg : ∀ x : Vec d, x ⬝ᵥ -ksym *ᵥ x = -(x ⬝ᵥ ksym *ᵥ x) :=
    fun x => by rw [Matrix.neg_mulVec, dotProduct_neg]
  rw [hquadneg, sub_neg_eq_add] at hestA
  -- the two closed forms
  have hid := centering_pairing_eq U hint hStar hE p r
  rw [← hksym] at hid
  set W : Vec d := r + ksym *ᵥ p with hW
  have hid2 := centering_adjoint_pairing_eq U hint hStar hE p r
  rw [← hksym] at hid2
  set W2 : Vec d := r - ksym *ᵥ p with hW2
  constructor
  · -- the primal cap
    rw [hid, hterm4 W, hterm5 W, hW, hloadP, hloadQ]
    linarith only [hest]
  · -- the adjoint cap
    rw [hid2, hterm4 W2, hterm5 W2, hW2, hloadP, hloadQ]
    linarith only [hestA]

/-- **The centering cap at the terminal adapted cell**: the instance of the
cap at `U := adaptedDomain hq t`, phrased on the adapted mean — exactly the
two centering clauses of the one-step hub's `hcaps` hypothesis, at
`Z := (3d + 4)·ε²`. -/
theorem centering_caps_at_terminal [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (hfin : HasFiniteAdaptedMean P q t)
    {S SStar K : Mat d} (hS : S.PosDef) (hStar : SStar.PosDef)
    (hform : toFullBlockMat (adaptedMean P q t) = schurBlock S SStar K)
    {eps : ℝ} (hpos : 0 < eps) (heps1 : eps ≤ 1)
    (htr : (d : ℝ) * (schurHattedContrast S SStar - 1) ≤ eps)
    (e : Vec d) (he : e ⬝ᵥ e = 1) :
    (1 / 2 : ℝ) *
        |vecDot
          (fun i ↦ ∫ a, averageGradient (Response.adaptedDomain hq t)
            ((a.subSkew (Response.responseSkew K)
              (Response.is_skew_mat_response_skew K)).coeffOn
                (Response.adaptedDomain hq t))
            (Response.centeredResponseOptimizer (Response.adaptedDomain hq t)
              (a.subSkew (Response.responseSkew K)
                (Response.is_skew_mat_response_skew K))
              (Response.centeredResponseLoadP S SStar K e)
              (Response.centeredResponseLoadQ S SStar K e)) i ∂P)
          (fun i ↦ ∫ a, averageFlux (Response.adaptedDomain hq t)
            ((a.subSkew (Response.responseSkew K)
              (Response.is_skew_mat_response_skew K)).coeffOn
                (Response.adaptedDomain hq t))
            (Response.centeredResponseOptimizer (Response.adaptedDomain hq t)
              (a.subSkew (Response.responseSkew K)
                (Response.is_skew_mat_response_skew K))
              (Response.centeredResponseLoadP S SStar K e)
              (Response.centeredResponseLoadQ S SStar K e)) i ∂P)| ≤
      (3 * (d : ℝ) + 4) * eps ^ 2 ∧
    (1 / 2 : ℝ) *
        |vecDot
          (fun i ↦ ∫ a, averageGradient (Response.adaptedDomain hq t)
            ((a.subSkew (Response.responseSkew K)
              (Response.is_skew_mat_response_skew K)).transpose.coeffOn
                (Response.adaptedDomain hq t))
            (Response.centeredAdjointOptimizer (Response.adaptedDomain hq t)
              (a.subSkew (Response.responseSkew K)
                (Response.is_skew_mat_response_skew K))
              (Response.centeredResponseLoadP S SStar K e)
              (Response.centeredResponseLoadQ S SStar K e)) i ∂P)
          (fun i ↦ ∫ a, averageFlux (Response.adaptedDomain hq t)
            ((a.subSkew (Response.responseSkew K)
              (Response.is_skew_mat_response_skew K)).transpose.coeffOn
                (Response.adaptedDomain hq t))
            (Response.centeredAdjointOptimizer (Response.adaptedDomain hq t)
              (a.subSkew (Response.responseSkew K)
                (Response.is_skew_mat_response_skew K))
              (Response.centeredResponseLoadP S SStar K e)
              (Response.centeredResponseLoadQ S SStar K e)) i ∂P)| ≤
      (3 * (d : ℝ) + 4) * eps ^ 2 := by
  have hint : HasIntegrableCoarseBlock P
      ((Response.adaptedDomain hq t : Domain d) : Set (Vec d)) := by
    simpa only [Response.adaptedDomain_carrier] using! hfin
  have hE : toFullBlockMat
      (annealedBlock P ((Response.adaptedDomain hq t : Domain d) : Set (Vec d))) =
      schurBlock S SStar K := by
    simpa only [adaptedMean, Response.adaptedDomain_carrier] using hform
  exact centering_pairing_caps (Response.adaptedDomain hq t) hint hS hStar hE
    hpos heps1 htr e he

end

end HCPolySupport.HighContrast.Quenched
