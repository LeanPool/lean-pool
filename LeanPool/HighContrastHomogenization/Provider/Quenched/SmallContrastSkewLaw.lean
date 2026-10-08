/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSkewInvariants
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBootstrapIdentityGrid
public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewBlock
public import LeanPool.HighContrastHomogenization.Provider.Response.LocalizedOptimizerObservables

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSkewLaw

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The law-side skew-recentering invariance

The recentering of Section 2.5 of HC
is a transformation of the *coefficient field*, hence of the *law*: the
recentered law is the pushforward of `P` under `a ↦ a - g`, i.e. under
`CoeffSpace.subSkew`.  The paper uses it to assume,
without loss of generality, that a homogenized skew vanishes, on the ground
that the assumptions and the conclusions of the small-contrast argument are
invariant.

This file proves that invariance for the objects the small-contrast argument
actually carries:

* `annealedBlock` (and hence `adaptedMean`) is *covariant*: it acquires the
  shear congruence `skewBlockCongr g`;
* `IsStationaryLaw` is *invariant*;
* `adaptedHattedContrast` and `annealedContrast` are *invariant*, because both
  contrasts are skew-blind (`SmallContrastSkewInvariants`).

The recentering map is a measurable involution up to sign, so all integral
transports go through `integral_map_equiv`, which needs no measurability side
condition on the integrand.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The recentering map is a measurable equivalence -/

/-- Recentering by `-g` undoes recentering by `g`. -/
theorem subSkew_neg_subSkew (a : CoeffSpace d) {g : Mat d} (hg : IsSkewMat g) :
    (a.subSkew g hg).subSkew (-g) (Response.isSkewMat_neg hg) = a := by
  apply Subtype.ext
  apply MeasureTheory.AEEqFun.ext
  filter_upwards [CoeffSpace.subSkew_ae (a.subSkew g hg) (-g)
      (Response.isSkewMat_neg hg), CoeffSpace.subSkew_ae a g hg] with x h1 h2
  rw [h1, h2]
  abel

/-- **The recentering map as a measurable equivalence** of the coefficient
space. -/
@[expose]
def subSkewEquiv {g : Mat d} (hg : IsSkewMat g) : CoeffSpace d ≃ᵐ CoeffSpace d where
  toFun := fun a => a.subSkew g hg
  invFun := fun a => a.subSkew (-g) (Response.isSkewMat_neg hg)
  left_inv := fun a => subSkew_neg_subSkew a hg
  right_inv := by
    intro a
    simpa only [neg_neg] using
      subSkew_neg_subSkew a (Response.isSkewMat_neg hg)
  measurable_toFun := Selection.measurable_subSkew g hg
  measurable_invFun := Selection.measurable_subSkew (-g) (Response.isSkewMat_neg hg)

@[simp] theorem subSkewEquiv_apply {g : Mat d} (hg : IsSkewMat g)
    (a : CoeffSpace d) : subSkewEquiv hg a = a.subSkew g hg := rfl

/-- The recentered law: the pushforward of `P` under the recentering map. -/
@[expose]
def recenteredLaw (P : Measure (CoeffSpace d)) {g : Mat d} (hg : IsSkewMat g) :
    Measure (CoeffSpace d) :=
  Measure.map (fun a : CoeffSpace d => a.subSkew g hg) P

theorem recenteredLaw_eq_map (P : Measure (CoeffSpace d)) {g : Mat d}
    (hg : IsSkewMat g) :
    recenteredLaw P hg = Measure.map (subSkewEquiv hg) P := rfl

instance isProbabilityMeasure_recenteredLaw (P : Measure (CoeffSpace d))
    [IsProbabilityMeasure P] {g : Mat d} (hg : IsSkewMat g) :
    IsProbabilityMeasure (recenteredLaw P hg) := by
  rw [recenteredLaw]
  infer_instance

/-! ## Stationarity is invariant -/

/-- Recentering commutes with the integer translations. -/
theorem translateCoeff_subSkew (z : Fin d → ℤ) (a : CoeffSpace d)
    {g : Mat d} (hg : IsSkewMat g) :
    translateCoeff z (a.subSkew g hg) = (translateCoeff z a).subSkew g hg := by
  apply Subtype.ext
  apply MeasureTheory.AEEqFun.ext
  have hqmp := (measurePreserving_add_right (volume : Measure (Vec d))
      (Source.AKL.intTranslation z)).quasiMeasurePreserving
  filter_upwards [Source.AKL.translateField_ae z (a.subSkew g hg).1,
    hqmp.tendsto_ae (CoeffSpace.subSkew_ae a g hg),
    CoeffSpace.subSkew_ae (translateCoeff z a) g hg,
    Source.AKL.translateField_ae z a.1] with x h1 h2 h3 h4
  change ⇑(Source.AKL.translateField z (a.subSkew g hg).1) x = _
  rw [h1, h2, h3]
  change _ = ⇑(Source.AKL.translateField z a.1) x - g
  rw [h4]

/-- **Stationarity is invariant under the recentering.** -/
theorem isStationaryLaw_recenteredLaw {P : Measure (CoeffSpace d)}
    (hP : HCPoly.Frozen.IsStationaryLaw P) {g : Mat d} (hg : IsSkewMat g) :
    HCPoly.Frozen.IsStationaryLaw (recenteredLaw P hg) := by
  intro z
  have hcomm : translateCoeff z ∘ (fun a : CoeffSpace d => a.subSkew g hg) =
      (fun a : CoeffSpace d => a.subSkew g hg) ∘ translateCoeff z := by
    funext a
    exact translateCoeff_subSkew z a hg
  calc
    Measure.map (translateCoeff z) (recenteredLaw P hg) =
        Measure.map (translateCoeff z ∘ (fun a : CoeffSpace d => a.subSkew g hg))
          P := by
      rw [recenteredLaw, Measure.map_map (measurable_translateCoeff z)
        (Selection.measurable_subSkew g hg)]
    _ = Measure.map ((fun a : CoeffSpace d => a.subSkew g hg) ∘ translateCoeff z)
          P := by rw [hcomm]
    _ = Measure.map (fun a : CoeffSpace d => a.subSkew g hg)
          (Measure.map (translateCoeff z) P) := by
      rw [Measure.map_map (Selection.measurable_subSkew g hg)
        (measurable_translateCoeff z)]
    _ = recenteredLaw P hg := by rw [hP z, recenteredLaw]

/-! ## The annealed block is shear-covariant -/

/-- **The annealed block of the recentered law** is the shear congruence of the
annealed block: this is the law-level form of HC (2.65). -/
theorem annealedBlock_recenteredLaw {P : Measure (CoeffSpace d)}
    (U : Book.Ch02.Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    {g : Mat d} (hg : IsSkewMat g) :
    annealedBlock (recenteredLaw P hg) (U : Set (Vec d)) =
      Response.skewBlockCongr g (annealedBlock P (U : Set (Vec d))) := by
  classical
  have hFint : Integrable
      (fun a : CoeffSpace d =>
        toFullBlockMat (coarseBlock (U : Set (Vec d)) (a.subSkew g hg))) P := by
    have hbase := integrable_toFullBlockMat hint
    have h := integrable_mul_left_mul_right (μ := P)
      (fullBlockShear g)ᴴ (fullBlockShear g) hbase
    refine h.congr (Filter.Eventually.of_forall fun a => ?_)
    change (fullBlockShear g)ᴴ * toFullBlockMat (coarseBlock (U : Set (Vec d)) a) *
        fullBlockShear g =
      toFullBlockMat (coarseBlock (U : Set (Vec d)) (a.subSkew g hg))
    rw [Response.coarseBlock_subSkew U a g hg, Response.toFullBlockMat_skewBlockCongr]
  have hbridge := Response.integral_coarseBlock_subSkew (P := P) U hint g hg
  have hentry : ∀ α β : BlockCoord d,
      blockMatEntry
          (annealedBlock (recenteredLaw P hg) (U : Set (Vec d))) α β =
        blockMatEntry
          (Response.skewBlockCongr g (annealedBlock P (U : Set (Vec d)))) α β := by
    intro α β
    rw [blockMatEntry_annealedBlock, recenteredLaw_eq_map,
      MeasureTheory.integral_map_equiv (subSkewEquiv hg)
        (fun a => blockMatEntry (coarseBlock (U : Set (Vec d)) a) α β)]
    have hleft : ∀ a : CoeffSpace d,
        blockMatEntry (coarseBlock (U : Set (Vec d)) (subSkewEquiv hg a)) α β =
          toFullBlockMat
            (coarseBlock (U : Set (Vec d)) (a.subSkew g hg)) α β := by
      intro a
      rw [subSkewEquiv_apply, toFullBlockMat_eq_blockMatEntry]
    rw [integral_congr_ae (Filter.Eventually.of_forall hleft)]
    rw [← entry_integral hFint α β, hbridge, toFullBlockMat_eq_blockMatEntry]
  refine blockMat_ext ?_ ?_ ?_ ?_ <;> funext i j
  · exact hentry (Sum.inl i) (Sum.inl j)
  · exact hentry (Sum.inl i) (Sum.inr j)
  · exact hentry (Sum.inr i) (Sum.inl j)
  · exact hentry (Sum.inr i) (Sum.inr j)

/-- **The adapted mean of the recentered law.** -/
theorem adaptedMean_recenteredLaw {P : Measure (CoeffSpace d)} {q : Mat d}
    (hq : q.PosDef) (k : ℤ) (hint : HasFiniteAdaptedMean P q k)
    {g : Mat d} (hg : IsSkewMat g) :
    adaptedMean (recenteredLaw P hg) q k =
      Response.skewBlockCongr g (adaptedMean P q k) := by
  have h := annealedBlock_recenteredLaw (P := P) (Response.adaptedDomain hq k)
    (by rwa [Response.adaptedDomain_carrier]) hg
  rw [Response.adaptedDomain_carrier] at h
  rw [adaptedMean, adaptedMean, h]

/-! ## Both contrasts are invariant -/

/-- **The Euclidean annealed contrast is invariant under the recentering.** -/
theorem annealedContrast_recenteredLaw {P : Measure (CoeffSpace d)}
    (m : ℤ)
    (hint : HasFiniteAdaptedMean P (1 : Mat d) m)
    (hpd : BlockPosDef (annealedBlock P (centeredCube d m)))
    {g : Mat d} (hg : IsSkewMat g) :
    annealedContrast (recenteredLaw P hg) m = annealedContrast P m := by
  have hone : (1 : Mat d).PosDef := Matrix.PosDef.one
  have hmean : adaptedMean P (1 : Mat d) m = annealedBlock P (centeredCube d m) :=
    adaptedMean_one P m
  have hpd' : BlockPosDef (adaptedMean P (1 : Mat d) m) := by rwa [hmean]
  have hfull : (toFullBlockMat (adaptedMean P (1 : Mat d) m)).PosDef :=
    posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P _ m) hpd'
  obtain ⟨S, SStar, K, -, hStar, hform⟩ := exists_schurBlock hfull
  have hform' : toFullBlockMat (annealedBlock P (centeredCube d m)) =
      schurBlock S SStar K := by rwa [hmean] at hform
  have hmap := adaptedMean_recenteredLaw (P := P) hone m hint hg
  rw [adaptedMean_one (recenteredLaw P hg) m, adaptedMean_one P m] at hmap
  rw [annealedContrast, annealedContrast, hmap]
  exact blockContrast_skewBlockCongr hStar hform' hg

end

end HCPolySupport.HighContrast.Quenched
