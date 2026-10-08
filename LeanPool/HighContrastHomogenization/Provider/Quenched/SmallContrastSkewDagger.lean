/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSkewLaw
public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewNormalization

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSkewDagger

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Coarse ellipticity under the constant-skew recentering

The last clause of the law-side API for the recentering of Section 2.5 of HC:
the frozen dagger assumption `e.coarse.ellipticity` survives the recentering,
with the reference block replaced by its shear congruence and the source field
composed with the inverse recentering.

The gauge, the growth witness and the exponent are untouched — the recentering
does not move the source at all, it only relabels which sample carries it.
The cell bound transports because the shear congruence preserves the doubled
Loewner order (`Response.skewBlockCongr_loewner_iff`) and commutes with scalar
dilation (`Response.blockScale_skewBlockCongr`).
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The standard aligned cube as a Chapter-2 domain. -/
@[expose]
public def standardCellDomain (d : ℕ) (k : ℤ) (w : Fin d → ℤ) :
    Book.Ch02.Domain d where
  carrier := standardCell d k w
  isDomain := by
    simpa [standardCell] using
      isOpenBoundedConvexDomain_openCubeSet
        (translateCube w (originCube d k))
  nonempty := Recurrence.standardCell_nonempty k w

@[simp] private theorem standardCellDomain_carrier (k : ℤ) (w : Fin d → ℤ) :
    ((standardCellDomain d k w : Book.Ch02.Domain d) : Set (Vec d)) =
      standardCell d k w := rfl

/-- Constant-skew covariance of the coarse response on a standard cell. -/
theorem coarseBlock_standardCell_subSkew (k : ℤ) (w : Fin d → ℤ)
    (a : CoeffSpace d) {g : Mat d} (hg : IsSkewMat g) :
    coarseBlock (standardCell d k w) (a.subSkew g hg) =
      Response.skewBlockCongr g (coarseBlock (standardCell d k w) a) := by
  simpa only [standardCellDomain_carrier] using
    Response.coarseBlock_subSkew (standardCellDomain d k w) a g hg

/-- The recentered source field: the original source read at the un-recentered
sample. -/
@[expose]
def recenteredSource (S : CoeffSpace d → ℝ) {g : Mat d} (hg : IsSkewMat g) :
    CoeffSpace d → ℝ :=
  fun a => S (a.subSkew (-g) (Response.isSkewMat_neg hg))

theorem recenteredSource_subSkew (S : CoeffSpace d → ℝ) {g : Mat d}
    (hg : IsSkewMat g) (a : CoeffSpace d) :
    recenteredSource S hg (a.subSkew g hg) = S a := by
  rw [recenteredSource, subSkew_neg_subSkew a hg]

/-- **Coarse ellipticity survives the recentering.**  The reference block picks
up the shear congruence; the gauge, growth witness and exponent are unchanged;
the source field is composed with the inverse recentering. -/
theorem coarseEllipticityDagger_recenteredLaw
    {P : Measure (CoeffSpace d)} {gexp : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ}
    {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P gexp E Ψ K S)
    {g : Mat d} (hg : IsSkewMat g) :
    HCPoly.Frozen.CoarseEllipticityDagger (recenteredLaw P hg) gexp
      (Response.skewBlockCongr g E) Ψ K (recenteredSource S hg) := by
  classical
  have hmeas : Measurable fun a : CoeffSpace d => a.subSkew g hg :=
    Selection.measurable_subSkew g hg
  have hmeasInv : Measurable fun a : CoeffSpace d =>
      a.subSkew (-g) (Response.isSkewMat_neg hg) :=
    Selection.measurable_subSkew (-g) (Response.isSkewMat_neg hg)
  have hSmeas : Measurable (recenteredSource S hg) :=
    hdag.source_measurable.comp hmeasInv
  refine
    { g_mem := hdag.g_mem
      refBlock_isSymm := Response.isSymmetricBlockMat_skewBlockCongr hdag.refBlock_isSymm
      refBlock_posDef := Response.blockPosDef_skewBlockCongr hdag.refBlock_posDef
      gauge_admissible := hdag.gauge_admissible
      one_lt_growthWitness := hdag.one_lt_growthWitness
      gauge_growth := hdag.gauge_growth
      source_measurable := hSmeas
      source_nonneg := fun a => hdag.source_nonneg _
      source_tail := ?_
      coarse_bound := ?_ }
  · -- the tail event is the preimage of the original tail event
    intro t ht
    have hset : IndependentSums.upperTailEvent (recenteredSource S hg) t =
        (fun a : CoeffSpace d => a.subSkew (-g) (Response.isSkewMat_neg hg)) ⁻¹'
          IndependentSums.upperTailEvent S t := rfl
    have hmeasSet : MeasurableSet
        (IndependentSums.upperTailEvent S t) :=
      measurableSet_lt measurable_const hdag.source_measurable
    have hpre : (fun a : CoeffSpace d => a.subSkew g hg) ⁻¹'
        ((fun a : CoeffSpace d => a.subSkew (-g) (Response.isSkewMat_neg hg)) ⁻¹'
          IndependentSums.upperTailEvent S t) =
        IndependentSums.upperTailEvent S t := by
      ext a
      simp only [Set.mem_preimage]
      rw [subSkew_neg_subSkew a hg]
    have happly : recenteredLaw P hg
        (IndependentSums.upperTailEvent (recenteredSource S hg) t) =
        P (IndependentSums.upperTailEvent S t) := by
      rw [hset, recenteredLaw, Measure.map_apply hmeas
        (hmeasInv hmeasSet), hpre]
    have hbase := hdag.source_tail t ht
    calc (recenteredLaw P hg).real
          (IndependentSums.upperTailEvent (recenteredSource S hg) t)
        = P.real (IndependentSums.upperTailEvent S t) := by
          simp only [MeasureTheory.measureReal_def, happly]
      _ ≤ (Ψ t)⁻¹ := hbase
  · -- the cell bound transports through the congruence
    have hembed : MeasurableEmbedding
        (fun a : CoeffSpace d => a.subSkew g hg) :=
      (subSkewEquiv hg).measurableEmbedding
    rw [recenteredLaw]
    refine hembed.ae_map_iff.2 ?_
    filter_upwards [hdag.coarse_bound] with a ha
    intro m hm k hk w hw
    have hS : recenteredSource S hg (a.subSkew g hg) = S a :=
      recenteredSource_subSkew S hg a
    rw [hS] at hm
    have hbase := ha m hm k hk w hw
    have hcong : coarseBlock (standardCell d k w) (a.subSkew g hg) =
        Response.skewBlockCongr g (coarseBlock (standardCell d k w) a) :=
      coarseBlock_standardCell_subSkew k w a hg
    rw [hcong, ← Response.blockScale_skewBlockCongr]
    exact (Response.skewBlockCongr_loewner_iff g _ _).mpr hbase

end

end HCPolySupport.HighContrast.Quenched
