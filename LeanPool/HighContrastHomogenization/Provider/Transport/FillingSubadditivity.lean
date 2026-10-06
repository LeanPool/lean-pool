/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.EuclideanAmbient
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedResponseSubadditivity
public import LeanPool.HighContrastHomogenization.Provider.Sharp.CoarseBlockOrder
public import LeanPool.HighContrastHomogenization.Setup.SourceObjects

/-!
# High-contrast homogenization: Provider.Transport.FillingSubadditivity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Subadditivity of the coarse block over a sub-partition, with its residual

The moving finite exhaustion of `e.two.grid.whitney.average` reads
`e.fixed.geometry.parent.child` along a family that is *not* a partition: the
maximal `q`-filling of a target cell `W`, cut off at a finite scale `J`, is a
finite disjoint family of cells inside `W` whose union misses a residual `R_J` of
positive measure.  The partition lemmas of
`HCPoly.Provider.Recurrence.AdaptedPartitionAverage` therefore do not apply, and
the printed argument does not ask them to: it triangulates the residual, pays for
it, and lets `J → -∞`.

This file pays for the residual once and for all, without triangulating it.  Two
observations do the work.

*Finite additivity with a residual.*  The integral over `W` of any function
integrable there is the sum of the integrals over the selected cells plus the
integral over the residual, and the relative volumes `|c_i| / |W|` together with
`|R| / |W|` sum to one.  No null hypothesis and no infinite sum enters; this is
the split that subadditivity over a finite cross-grid exhaustion makes before the
triangulation.

*A uniform bound on the response integrand.*  On any measurable subset of `W`,
and uniformly over the `a`-harmonic competitors, the scalar response integrand of
the variational definition of the coarse block is at most
`λ^{-1}(Λ²|p|² + |q|²)`: ellipticity bounds the energy from below, the two
linear terms are absorbed by Young's
inequality, and no convexity or maximizer is involved.  This is
`scalarResponseIntegrand_le_plainUpperBound_of_isEllipticFieldOn` upstream; the
only thing added here is that it is used on the residual, where nothing else is
known.

Together they give the response functional of the parent below the weighted sum
of the responses of the selected cells plus the residual weight times one
constant, and hence the same for the block quadratic form: the leftover affine
term `-p·q` of `responseJ_eq_blockQuadratic`, which cancels exactly against a
full partition, survives here multiplied by the residual weight and is folded
into the same constant.  Because the residual weight is what the residual volume
of the Whitney selection drives to zero, the value of that constant
is irrelevant downstream, and the coefficient-space forms below record only that
one exists.
-/

namespace HCPolySupport
namespace HighContrast
namespace Transport

open MeasureTheory

noncomputable section

variable {d : ℕ}

section SubPartition

variable {ι : Type*} {U : Set (Vec d)} {Z : Finset ι} {c : ι → Set (Vec d)}

/-! ## Finite additivity with a residual -/

/-- The union of a finite family of measurable cells is measurable. -/
private theorem measurableSet_biUnion_coe (hmeas : ∀ i ∈ Z, MeasurableSet (c i)) :
    MeasurableSet (⋃ i ∈ (↑Z : Set ι), c i) := by
  classical
  rw [Finset.set_biUnion_coe]
  exact Z.measurableSet_biUnion hmeas

/-- **The volume of the parent is the sum of the volumes of the cells plus the
volume of the residual.**  The cells are disjoint and inside the parent, and the
residual is what the parent has left; no null hypothesis is used. -/
theorem measure_eq_sum_add_residual (hU : MeasurableSet U)
    (hmeas : ∀ i ∈ Z, MeasurableSet (c i)) (hsub : ∀ i ∈ Z, c i ⊆ U)
    (hdisj : (↑Z : Set ι).PairwiseDisjoint c) :
    volume U =
      (∑ i ∈ Z, volume (c i)) + volume (U \ ⋃ i ∈ (↑Z : Set ι), c i) := by
  classical
  have hVsub : (⋃ i ∈ (↑Z : Set ι), c i) ⊆ U :=
    Set.iUnion₂_subset fun i hi => hsub i (Finset.mem_coe.mp hi)
  have hVmeas : MeasurableSet (⋃ i ∈ (↑Z : Set ι), c i) := measurableSet_biUnion_coe hmeas
  have hbig : volume (⋃ i ∈ (↑Z : Set ι), c i) = ∑ i ∈ Z, volume (c i) := by
    rw [Finset.set_biUnion_coe]
    exact measure_biUnion_finset hdisj hmeas
  calc volume U = volume ((⋃ i ∈ (↑Z : Set ι), c i) ∪ (U \ ⋃ i ∈ (↑Z : Set ι), c i)) := by
        rw [Set.union_sdiff_cancel hVsub]
    _ = volume (⋃ i ∈ (↑Z : Set ι), c i) + volume (U \ ⋃ i ∈ (↑Z : Set ι), c i) :=
        measure_union disjoint_sdiff_self_right (hU.diff hVmeas)
    _ = (∑ i ∈ Z, volume (c i)) + volume (U \ ⋃ i ∈ (↑Z : Set ι), c i) := by rw [hbig]

/-- **The integral over the parent splits off the residual.**  This is the finite
additivity that subadditivity over a finite cross-grid exhaustion uses before its
triangulation. -/
theorem setIntegral_eq_sum_add_residual {g : Vec d → ℝ} (hU : MeasurableSet U)
    (hmeas : ∀ i ∈ Z, MeasurableSet (c i)) (hsub : ∀ i ∈ Z, c i ⊆ U)
    (hdisj : (↑Z : Set ι).PairwiseDisjoint c) (hint : IntegrableOn g U volume) :
    ∫ x in U, g x =
      (∑ i ∈ Z, ∫ x in c i, g x) + ∫ x in U \ ⋃ i ∈ (↑Z : Set ι), c i, g x := by
  classical
  have hVsub : (⋃ i ∈ (↑Z : Set ι), c i) ⊆ U :=
    Set.iUnion₂_subset fun i hi => hsub i (Finset.mem_coe.mp hi)
  have hVmeas : MeasurableSet (⋃ i ∈ (↑Z : Set ι), c i) := measurableSet_biUnion_coe hmeas
  have hbig : ∫ x in ⋃ i ∈ (↑Z : Set ι), c i, g x = ∑ i ∈ Z, ∫ x in c i, g x := by
    refine Recurrence.setIntegral_eq_sum_of_aePartition hmeas
      (fun i hi => Set.subset_biUnion_of_mem (u := c) (Finset.mem_coe.mpr hi)) hdisj ?_
      (hint.mono_set hVsub)
    rw [Set.sdiff_self, measure_empty]
  calc ∫ x in U, g x
      = ∫ x in (⋃ i ∈ (↑Z : Set ι), c i) ∪ (U \ ⋃ i ∈ (↑Z : Set ι), c i), g x := by
        rw [Set.union_sdiff_cancel hVsub]
    _ = (∫ x in ⋃ i ∈ (↑Z : Set ι), c i, g x) +
          ∫ x in U \ ⋃ i ∈ (↑Z : Set ι), c i, g x :=
        setIntegral_union disjoint_sdiff_self_right (hU.diff hVmeas)
          (hint.mono_set hVsub) (hint.mono_set Set.sdiff_subset)
    _ = (∑ i ∈ Z, ∫ x in c i, g x) + ∫ x in U \ ⋃ i ∈ (↑Z : Set ι), c i, g x := by rw [hbig]

/-- **The weights of a sub-partition, together with the residual weight, sum to
one.**  This is the printed normalization `Σ|V|/|W| + |R|/|W| = 1` of the split
exhaustion. -/
theorem sum_weight_add_residual_eq_one (hU : MeasurableSet U)
    (hmeas : ∀ i ∈ Z, MeasurableSet (c i)) (hsub : ∀ i ∈ Z, c i ⊆ U)
    (hdisj : (↑Z : Set ι).PairwiseDisjoint c)
    (hU0 : volume U ≠ 0) (hUtop : volume U ≠ ⊤) :
    (∑ i ∈ Z, (volume (c i)).toReal / (volume U).toReal) +
        (volume (U \ ⋃ i ∈ (↑Z : Set ι), c i)).toReal / (volume U).toReal = 1 := by
  have htoReal : (volume U).toReal =
      (∑ i ∈ Z, (volume (c i)).toReal) +
        (volume (U \ ⋃ i ∈ (↑Z : Set ι), c i)).toReal := by
    rw [measure_eq_sum_add_residual hU hmeas hsub hdisj,
      ENNReal.toReal_add
        (ENNReal.sum_ne_top.mpr fun i hi =>
          Recurrence.measure_cell_ne_top_of_subset hUtop (hsub i hi))
        (Recurrence.measure_cell_ne_top_of_subset hUtop Set.sdiff_subset),
      ENNReal.toReal_sum fun i hi => Recurrence.measure_cell_ne_top_of_subset hUtop (hsub i hi)]
  rw [← Finset.sum_div, ← add_div, ← htoReal,
    div_self (ENNReal.toReal_pos hU0 hUtop).ne']

/-! ## The response functional over a sub-partition -/

/-- **Subadditivity of the response functional over a sub-partition.**  Every
competitor on the parent restricts to a competitor on each selected cell, and on
the residual the integrand is below the uniform elliptic majorant
`λ^{-1}(Λ²|p|² + |q|²)`, which is all that is known there. -/
theorem responseJ_le_sum_weight_add_residual {f : CoeffField d} {lam Lam : ℝ}
    (hU : IsOpenBoundedConvexDomain U) (hEll : IsEllipticFieldOn lam Lam U f)
    (hU0 : volume U ≠ 0) (hc : ∀ i ∈ Z, IsOpenBoundedConvexDomain (c i))
    (hsub : ∀ i ∈ Z, c i ⊆ U) (hdisj : (↑Z : Set ι).PairwiseDisjoint c)
    (hcell0 : ∀ i ∈ Z, volume (c i) ≠ 0) (p q : Vec d) :
    ResponseJ U p q f ≤
      (∑ i ∈ Z, (volume (c i)).toReal / (volume U).toReal * ResponseJ (c i) p q f) +
        (volume (U \ ⋃ i ∈ (↑Z : Set ι), c i)).toReal / (volume U).toReal *
          (lam⁻¹ * (Lam ^ 2 * vecNormSq p + vecNormSq q)) := by
  have : IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  have hUmeas : MeasurableSet U := hU.isOpen.measurableSet
  have hUtop : volume U ≠ ⊤ := hU.volume_lt_top.ne
  have hmeas : ∀ i ∈ Z, MeasurableSet (c i) := fun i hi => (hc i hi).isOpen.measurableSet
  have hUpos : (0 : ℝ) < (volume U).toReal := ENNReal.toReal_pos hU0 hUtop
  have hRmeas : MeasurableSet (U \ ⋃ i ∈ (↑Z : Set ι), c i) :=
    hUmeas.diff (measurableSet_biUnion_coe hmeas)
  have hRtop : volume (U \ ⋃ i ∈ (↑Z : Set ι), c i) ≠ ⊤ :=
    Recurrence.measure_cell_ne_top_of_subset hUtop Set.sdiff_subset
  refine csSup_le (responseJValueSet_nonempty U p q f) ?_
  rintro m ⟨u, rfl⟩
  have hint : IntegrableOn (scalarResponseIntegrand U f p q u) U volume :=
    scalarResponseIntegrand_integrableOn_of_isEllipticFieldOn hEll p q u
  have hcellle : ∀ i ∈ Z, ∫ x in c i, scalarResponseIntegrand U f p q u x ≤
      (volume (c i)).toReal * ResponseJ (c i) p q f := by
    intro i hi
    have : IsFiniteMeasure (volumeMeasureOn (c i)) := by
      simpa [volumeMeasureOn] using (hc i hi).isFiniteMeasure_restrict_volume
    have hEllc : IsEllipticFieldOn lam Lam (c i) f :=
      IsEllipticFieldOn.mono hEll (hmeas i hi) (hsub i hi)
    have hpos : (0 : ℝ) < (volume (c i)).toReal :=
      ENNReal.toReal_pos (hcell0 i hi) (Recurrence.measure_cell_ne_top_of_subset hUtop (hsub i hi))
    have hcongr : scalarResponseIntegrand U f p q u =
        scalarResponseIntegrand (c i) f p q
          (u.restrictOfIsEllipticFieldOn hU.isOpen (hc i hi).isOpen (hsub i hi) hEllc) := rfl
    have hle : volumeAverage (c i) (scalarResponseIntegrand U f p q u) ≤
        ResponseJ (c i) p q f := by
      rw [hcongr]
      exact le_responseJ_of_mem_responseJValueSet_of_isEllipticFieldOn hEllc hpos.ne' p q
        (responseJValueSet_mem (c i) p q f _)
    rw [volumeAverage] at hle
    have := mul_le_mul_of_nonneg_left hle hpos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at this
  have hresle : ∫ x in U \ ⋃ i ∈ (↑Z : Set ι), c i, scalarResponseIntegrand U f p q u x ≤
      (volume (U \ ⋃ i ∈ (↑Z : Set ι), c i)).toReal *
        (lam⁻¹ * (Lam ^ 2 * vecNormSq p + vecNormSq q)) := by
    have hmono := setIntegral_mono_on (hint.mono_set Set.sdiff_subset)
      (integrableOn_const hRtop) hRmeas fun x hx =>
        scalarResponseIntegrand_le_plainUpperBound_of_isEllipticFieldOn hEll p q u x hx.1
    rwa [setIntegral_const, smul_eq_mul, measureReal_def] at hmono
  rw [volumeAverage]
  have hsplit := setIntegral_eq_sum_add_residual (g := scalarResponseIntegrand U f p q u)
    hUmeas hmeas hsub hdisj hint
  have hstep : (volume U).toReal⁻¹ * ∫ x in U, scalarResponseIntegrand U f p q u x ≤
      (volume U).toReal⁻¹ *
        ((∑ i ∈ Z, (volume (c i)).toReal * ResponseJ (c i) p q f) +
          (volume (U \ ⋃ i ∈ (↑Z : Set ι), c i)).toReal *
            (lam⁻¹ * (Lam ^ 2 * vecNormSq p + vecNormSq q))) := by
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hUpos.le)
    rw [hsplit]
    exact add_le_add (Finset.sum_le_sum hcellle) hresle
  refine hstep.trans_eq ?_
  rw [mul_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun _ _ => by ring
  · ring

/-! ## The block quadratic form over a sub-partition -/

/-- **Subadditivity of the coarse block over a sub-partition**, in the quadratic
form that defines the Loewner order.  This is the first display of
`e.fixed.geometry.parent.child` along a family that covers the parent only
partially: the deficit is charged to the residual weight, at one constant that
depends on the ellipticity of the field and on the doubled vector alone.

The affine term `-p·q` of `responseJ_eq_blockQuadratic` no longer cancels, the
cell weights summing to `1 - |R|/|W|` rather than to one; what it leaves is
exactly the residual weight times `-X_1·X_2`, which is why that term appears
inside the same bracket. -/
theorem blockQuadratic_le_sum_weight_add_residual [NeZero d] {f : CoeffField d}
    {lam Lam : ℝ} (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U f) (hU0 : volume U ≠ 0)
    (hc : ∀ i ∈ Z, IsOpenBoundedConvexDomain (c i)) (hsub : ∀ i ∈ Z, c i ⊆ U)
    (hdisj : (↑Z : Set ι).PairwiseDisjoint c) (hcell0 : ∀ i ∈ Z, volume (c i) ≠ 0)
    (X : BlockVec d) :
    1 / 2 * blockVecDot X (blockMatVecMul (coarseBlockMatrix U f) X) ≤
      (∑ i ∈ Z, (volume (c i)).toReal / (volume U).toReal *
          (1 / 2 * blockVecDot X (blockMatVecMul (coarseBlockMatrix (c i) f) X))) +
        (volume (U \ ⋃ i ∈ (↑Z : Set ι), c i)).toReal / (volume U).toReal *
          (lam⁻¹ * (Lam ^ 2 * vecNormSq X.1 + vecNormSq X.2) - vecDot X.1 X.2) := by
  have hUmeas : MeasurableSet U := hU.isOpen.measurableSet
  have hUtop : volume U ≠ ⊤ := hU.volume_lt_top.ne
  have hmeas : ∀ i ∈ Z, MeasurableSet (c i) := fun i hi => (hc i hi).isOpen.measurableSet
  have hvol : 0 < (volume U).toReal := ENNReal.toReal_pos hU0 hUtop
  have hX : ((-(-X.1), X.2) : BlockVec d) = X := by rw [neg_neg]
  have hparent : 1 / 2 * blockVecDot X (blockMatVecMul (coarseBlockMatrix U f) X) =
      ResponseJ U (-X.1) X.2 f + vecDot (-X.1) X.2 := by
    rw [Recurrence.responseJ_eq_blockQuadratic hU hEll hvol (-X.1) X.2, hX]
    ring
  have hcelleq : ∀ i ∈ Z,
      1 / 2 * blockVecDot X (blockMatVecMul (coarseBlockMatrix (c i) f) X) =
        ResponseJ (c i) (-X.1) X.2 f + vecDot (-X.1) X.2 := by
    intro i hi
    have hEllc : IsEllipticFieldOn lam Lam (c i) f :=
      IsEllipticFieldOn.mono hEll (hmeas i hi) (hsub i hi)
    have hvolc : 0 < (volume (c i)).toReal :=
      ENNReal.toReal_pos (hcell0 i hi) (Recurrence.measure_cell_ne_top_of_subset hUtop (hsub i hi))
    rw [Recurrence.responseJ_eq_blockQuadratic (hc i hi) hEllc hvolc (-X.1) X.2, hX]
    ring
  have hweight := sum_weight_add_residual_eq_one hUmeas hmeas hsub hdisj hU0 hUtop
  have hsum : ∑ i ∈ Z, (volume (c i)).toReal / (volume U).toReal *
        (1 / 2 * blockVecDot X (blockMatVecMul (coarseBlockMatrix (c i) f) X)) =
      (∑ i ∈ Z, (volume (c i)).toReal / (volume U).toReal * ResponseJ (c i) (-X.1) X.2 f) +
        (∑ i ∈ Z, (volume (c i)).toReal / (volume U).toReal) * vecDot (-X.1) X.2 := by
    rw [Finset.sum_congr rfl fun i hi => by rw [hcelleq i hi], Finset.sum_mul,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hWsum : ∑ i ∈ Z, (volume (c i)).toReal / (volume U).toReal =
      1 - (volume (U \ ⋃ i ∈ (↑Z : Set ι), c i)).toReal / (volume U).toReal := by
    linarith only [hweight]
  have hJ := responseJ_le_sum_weight_add_residual hU hEll hU0 hc hsub hdisj hcell0 (-X.1) X.2
  rw [vecNormSq_neg] at hJ
  rw [hparent, hsum, hWsum, vecDot_neg_left]
  linarith only [hJ]

end SubPartition

/-! ## The coefficient-space forms -/

section CoeffSpace

variable {ι : Type*} {U : Set (Vec d)} {Z : Finset ι} {c : ι → Set (Vec d)}

/-- **The coarse response is positive**, the first clause of
`e.two.grid.whitney.average`: its quadratic form is nonnegative at every
doubled vector, on every bounded open convex domain of positive volume. -/
theorem zero_le_blockQuadratic_coarseBlock [NeZero d] (hU : IsOpenBoundedConvexDomain U)
    (hU0 : volume U ≠ 0) (a : CoeffSpace d) (X : BlockVec d) :
    0 ≤ 1 / 2 * blockVecDot X (blockMatVecMul (coarseBlock U a) X) := by
  obtain ⟨lam, Lam, f, _, _, hfm, hfell, hae⟩ :=
    exists_pointwise_elliptic_representative a.2 hU.isBoundedDomain.isBounded
  have hvol : 0 < (volume U).toReal := ENNReal.toReal_pos hU0 hU.volume_lt_top.ne
  rw [coarseBlock_eq_of_ae_eq a hae,
    ← Sharp.mu_eq_half_blockQuadratic hU
      (Recurrence.isEllipticFieldOn_of_measurable hfm hfell hU.isOpen.measurableSet) hvol,
    ← Mu_congr_ae hae X]
  exact zero_le_Mu_coeffSpace U X a

end CoeffSpace

end

end Transport
end HighContrast
end HCPolySupport
