/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedPartitionAverage
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.MatrixExtraction
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.MagicIdentities.MuOrdering.EllipticWrappers

/-!
# High-contrast homogenization: Provider.Recurrence.AdaptedResponseSubadditivity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Subadditivity of the coarse block over a partition into convex cells

`e.fixed.geometry.parent.child` states `𝐀(U) ≤ Σ (|U_i| / |U|) 𝐀(U_i)` for a
disjoint partition of `U` up to a null set.  The mathematics behind it is one
line: the coarse block is the Hessian of the response functional `J(U; p, q)`,
which is a *supremum* over the `a`-harmonic competitors on `U`, and an
`a`-harmonic function on `U` restricts to an `a`-harmonic function on every open
subset; so each competitor for the parent is, cell by cell, a competitor for the
cell, and averaging its integrand over the partition gives the bound.

Two facts turn that line into a proof over cells that are not triadic cubes.
First, the identity reading the coarse block off the response functional,
`J(U; p, q) = ½ (-p, q) · 𝐀(U) (-p, q) - p · q`, holds over every bounded open
convex domain, not only over cubes: this is `responseJ_eq_blockQuadratic` below,
assembled from the canonical recovery data of the variational problem.  Second,
the affine term `- p · q` is the same on the parent and on every cell, and the
weights sum to one, so it cancels from the averaged inequality.

The subadditivity is proved here for an arbitrary finite family of bounded open
convex cells of one common volume, pairwise disjoint and covering the parent up
to a null set.  The aligned subdivision of an adapted cell is such a family.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Ellipticity of a pointwise representative on a measurable set -/

/-- A measurable field uniformly elliptic at every point of a measurable set is
elliptic on that set, in the sense the response functional consumes. -/
theorem isEllipticFieldOn_of_measurable {lam Lam : ℝ} {f : CoeffField d}
    (hf : Measurable f) {U : Set (Vec d)}
    (hell : ∀ x ∈ U, IsEllipticMatrix lam Lam (f x))
    (hU : MeasurableSet U) : IsEllipticFieldOn lam Lam U f := by
  classical
  refine ⟨?_, hell⟩
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  exact Measurable.ite hU
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hf)) measurable_const

/-! ## The response functional reads off the coarse block on any convex domain -/

/-- **The response functional is the coarse block quadratic form**, on every
bounded open convex domain.  This is the identity that frees
`e.fixed.geometry.parent.child` from the triadic cube. -/
theorem responseJ_eq_blockQuadratic [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {lam Lam : ℝ} {f : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U f) (hvol : 0 < (volume U).toReal) (p q : Vec d) :
    ResponseJ U p q f =
      1 / 2 * blockVecDot (-p, q) (blockMatVecMul (coarseBlockMatrix U f) (-p, q)) -
        vecDot p q := by
  have : IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  obtain ⟨R, _sigma0, compat, hA, _hSInv, hS, hK, hSigma, _hCanon⟩ :=
    Internal.Ch02.BookCh02.exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
      hU hEll hvol
  exact
    magic_identity_responseJ_block_quadratic_coarseBlockMatrix_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      R hU hEll hvol compat hA hS hK hSigma p q

/-! ## Competitor restriction -/

/-- **Subadditivity of the response functional.**  Every `a`-harmonic competitor
on the parent restricts to a competitor on each cell, so the average of its
integrand is bounded by the average of the cells' suprema. -/
theorem responseJ_le_sum_weight_of_aePartition {ι : Type*} {U : Set (Vec d)}
    {Z : Finset ι} {c : ι → Set (Vec d)} {f : CoeffField d} {lam Lam : ℝ}
    (hU : IsOpenBoundedConvexDomain U) (hEll : IsEllipticFieldOn lam Lam U f)
    (hc : ∀ i ∈ Z, IsOpenBoundedConvexDomain (c i)) (hsub : ∀ i ∈ Z, c i ⊆ U)
    (hdisj : (↑Z : Set ι).PairwiseDisjoint c)
    (hnull : volume (U \ ⋃ i ∈ (↑Z : Set ι), c i) = 0)
    (hcell0 : ∀ i ∈ Z, volume (c i) ≠ 0) (p q : Vec d) :
    ResponseJ U p q f ≤
      ∑ i ∈ Z, (volume (c i)).toReal / (volume U).toReal * ResponseJ (c i) p q f := by
  have : IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  refine csSup_le (responseJValueSet_nonempty U p q f) ?_
  rintro m ⟨u, rfl⟩
  have hint : IntegrableOn (scalarResponseIntegrand U f p q u) U volume :=
    scalarResponseIntegrand_integrableOn_of_isEllipticFieldOn hEll p q u
  rw [volumeAverage_eq_sum_weight_of_aePartition
    (fun i hi => (hc i hi).isOpen.measurableSet) hsub hdisj hnull hint hcell0
    hU.volume_lt_top.ne]
  refine Finset.sum_le_sum fun i hi => ?_
  have : IsFiniteMeasure (volumeMeasureOn (c i)) := by
    simpa [volumeMeasureOn] using (hc i hi).isFiniteMeasure_restrict_volume
  have hEllc : IsEllipticFieldOn lam Lam (c i) f :=
    IsEllipticFieldOn.mono hEll (hc i hi).isOpen.measurableSet (hsub i hi)
  have hvolc : (volume (c i)).toReal ≠ 0 :=
    (ENNReal.toReal_pos (hcell0 i hi)
      (measure_cell_ne_top_of_subset hU.volume_lt_top.ne (hsub i hi))).ne'
  have hcongr : scalarResponseIntegrand U f p q u =
      scalarResponseIntegrand (c i) f p q
        (u.restrictOfIsEllipticFieldOn hU.isOpen (hc i hi).isOpen (hsub i hi) hEllc) := rfl
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [hcongr]
  exact le_responseJ_of_mem_responseJValueSet_of_isEllipticFieldOn hEllc hvolc p q
    (responseJValueSet_mem (c i) p q f _)

/-! ## Subadditivity of the coarse block -/

/-- **Subadditivity of the coarse block over a partition into convex cells**, in
the quadratic form that defines the Loewner order.  This is the first display of
`e.fixed.geometry.parent.child`, with its printed weights `|U_i| / |U|`. -/
theorem blockQuadratic_le_sum_weight_of_aePartition [NeZero d] {ι : Type*}
    {U : Set (Vec d)} {Z : Finset ι} {c : ι → Set (Vec d)} {f : CoeffField d}
    {lam Lam : ℝ}
    (hU : IsOpenBoundedConvexDomain U) (hEll : IsEllipticFieldOn lam Lam U f)
    (hU0 : volume U ≠ 0)
    (hc : ∀ i ∈ Z, IsOpenBoundedConvexDomain (c i)) (hsub : ∀ i ∈ Z, c i ⊆ U)
    (hdisj : (↑Z : Set ι).PairwiseDisjoint c)
    (hnull : volume (U \ ⋃ i ∈ (↑Z : Set ι), c i) = 0)
    (hcell0 : ∀ i ∈ Z, volume (c i) ≠ 0) (X : BlockVec d) :
    1 / 2 * blockVecDot X (blockMatVecMul (coarseBlockMatrix U f) X) ≤
      ∑ i ∈ Z, (volume (c i)).toReal / (volume U).toReal *
        (1 / 2 * blockVecDot X (blockMatVecMul (coarseBlockMatrix (c i) f) X)) := by
  have hvol : 0 < (volume U).toReal := ENNReal.toReal_pos hU0 hU.volume_lt_top.ne
  set p : Vec d := -X.1 with hp
  set q : Vec d := X.2 with hq
  have hX : ((-p, q) : BlockVec d) = X := by
    rw [hp, hq, neg_neg]
  have hparent : 1 / 2 * blockVecDot X (blockMatVecMul (coarseBlockMatrix U f) X) =
      ResponseJ U p q f + vecDot p q := by
    rw [responseJ_eq_blockQuadratic hU hEll hvol p q, hX]
    ring
  have hcell : ∀ i ∈ Z,
      1 / 2 * blockVecDot X (blockMatVecMul (coarseBlockMatrix (c i) f) X) =
        ResponseJ (c i) p q f + vecDot p q := by
    intro i hi
    have hEllc : IsEllipticFieldOn lam Lam (c i) f :=
      IsEllipticFieldOn.mono hEll (hc i hi).isOpen.measurableSet (hsub i hi)
    have hvolc : 0 < (volume (c i)).toReal :=
      ENNReal.toReal_pos (hcell0 i hi)
        (measure_cell_ne_top_of_subset hU.volume_lt_top.ne (hsub i hi))
    rw [responseJ_eq_blockQuadratic (hc i hi) hEllc hvolc p q, hX]
    ring
  have hweight : ∑ i ∈ Z, (volume (c i)).toReal / (volume U).toReal = 1 :=
    sum_weight_eq_one_of_aePartition (fun i hi => (hc i hi).isOpen.measurableSet) hsub
      hdisj hnull hU0 hU.volume_lt_top.ne
  have hsum : ∑ i ∈ Z, (volume (c i)).toReal / (volume U).toReal *
        (1 / 2 * blockVecDot X (blockMatVecMul (coarseBlockMatrix (c i) f) X)) =
      (∑ i ∈ Z, (volume (c i)).toReal / (volume U).toReal * ResponseJ (c i) p q f) +
        vecDot p q := by
    have hdist : ∀ t : ℝ,
        ∑ i ∈ Z, (volume (c i)).toReal / (volume U).toReal *
            (ResponseJ (c i) p q f + t) =
          (∑ i ∈ Z, (volume (c i)).toReal / (volume U).toReal * ResponseJ (c i) p q f) +
            (∑ i ∈ Z, (volume (c i)).toReal / (volume U).toReal) * t := by
      intro t
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [Finset.sum_congr rfl fun i hi => by rw [hcell i hi], hdist, hweight, one_mul]
  have hJ := responseJ_le_sum_weight_of_aePartition hU hEll hc hsub hdisj hnull hcell0 p q
  rw [hparent, hsum]
  linarith only [hJ]

end

end Recurrence
end HighContrast
end HCPolySupport
