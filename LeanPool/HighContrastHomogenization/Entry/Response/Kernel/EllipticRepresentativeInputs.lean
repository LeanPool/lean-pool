/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AffineSobolevPullback
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AnnealedBlockIdentity

/-!
# High-contrast homogenization: Entry.Response.Kernel.EllipticRepresentativeInputs

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Elliptic representatives and integrability inputs

For the recentred coefficients `a_- = respCoeffMinus F a` and `a_+ = respCoeffPlus F a`, this file
produces an almost-everywhere-equal representative that is pointwise elliptic on the response
cell, and uses it to obtain `MemLp` of the pulled-back flux consumed by the cutoff-pairing bound.
It then proves, at the carriers of the diagonal weak-norm estimate, the nonnegativity of the
averaged energy density and the integrability of the doubled optimizer field and its flux, for
both signs and on both the aligned subcells and the parent cell.  These are the elliptic and
integrability inputs of the response-transfer estimate `p.response.transfer`.
-/

section
/-!
## The elliptic input for the cutoff bound, and the pulled-back flux it feeds

`IsEllipticFieldOn lam Lam (adaptedCell q t) b` is a hypothesis that the cutoff bound
(`integral_abs_cutoffPairingOnCell_le_respWeak`,
`HCPoly/Entry/Response/Cutoff/ResponseTransferFromCutoffBound.lean`) does not carry and
would have to be given one, in order to reach
`MemLp flux 2 (normalizedCubeMeasure Q)` for the pulled-back flux -- the `hflux` slot of the
generic CG product bridge
`abs_cubeAverage_vecDot_centered_scalar_cutoff_le_scaledWeakNormProduct` in namespace
`Book.Ch05.Section53.JUpperBoundWeakNorms`.

**It does not have to be given one.**  For the two coefficients the cutoff bound actually
quantifies over,
`respCoeffMinus F a` and `respCoeffPlus F a` with `a : CoeffSpace d`, the datum is DERIVABLE from
`a`'s own qualitative local uniform ellipticity (`HCPoly/Setup/CoefficientSpace.lean`) together
with the invertibility of the grid, which the cutoff bound carries through its premise
`2 * d ≤ 3 ^ jStar`.  The derivation is
`Annealed.exists_elliptic_representative_adapted`
(`HCPoly/Entry/Annealed/AdaptedDomainLocality.lean`)
followed by `isEllipticFieldOn_sub_skew`/`isEllipticFieldOn_transpose_add_skew`; it is exactly the
derivation already performed inside `bddAbove_respWeakEnergySet_respCoeffMinus`
, lifted here to a reusable statement.

The shape is the a.e.-REPRESENTATIVE one -- ellipticity of some `f` with
`respCoeffMinus F a =ᵐ f` on the cell -- and not ellipticity of `respCoeffMinus F a` on the nose,
because a point of `CoeffSpace d` is an a.e. class and no representative of it is elliptic
pointwise.  This is the same shape as the `bddAbove_respWeakEnergySet` hypothesis
 and as
`CoeffSpace.exists_pointwise_coeffOn_family_aeeq`, and it is
enough for every `MemLp`/`Integrable` consumer, all of which are a.e. invariant.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The elliptic representative on an adapted cell, for both response coefficients -/

/-- **The elliptic input for the cutoff bound, minus sign.**  For every sample `a` the coefficient
`a_- = a - g` has, on the adapted cell, an a.e.-equal representative that is uniformly elliptic
there.  Nothing but invertibility of the grid is needed; the constants belong to the sample and
to the cell and enter no estimate, since the ellipticity is qualitative and local. -/
theorem exists_elliptic_representative_respCoeffMinus (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d) :
    ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) f ∧
        respCoeffMinus F a =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)] f := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq t 0 a
  rw [adaptedCellTranslate_zero] at hEll
  refine ⟨lam, 2 * Lam + 2 * ‖respg F‖ ^ 2 / lam, fun x => f x - respg F, hlam, ?_,
    isEllipticFieldOn_sub_skew hEll _ (respg_isSkew F), ?_⟩
  · have hn : (0:ℝ) ≤ 2 * ‖respg F‖ ^ 2 / lam := by positivity
    linarith only [hle, hn, hlam]
  · refine MeasureTheory.ae_restrict_of_ae ?_
    filter_upwards [hae] with x hx
    simp [respCoeffMinus, hx]

/-- **The elliptic input for the cutoff bound, plus sign.**  The transposed twin, for `a_+ = a^t +
g`. -/
theorem exists_elliptic_representative_respCoeffPlus (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d) :
    ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) f ∧
        respCoeffPlus F a =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)] f := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq t 0 a
  rw [adaptedCellTranslate_zero] at hEll
  refine ⟨lam, 2 * Lam + 2 * ‖respg F‖ ^ 2 / lam, fun x => matTranspose (f x) + respg F, hlam, ?_,
    isEllipticFieldOn_transpose_add_skew hEll _ (respg_isSkew F), ?_⟩
  · have hn : (0:ℝ) ≤ 2 * ‖respg F‖ ^ 2 / lam := by positivity
    linarith only [hle, hn, hlam]
  · refine MeasureTheory.ae_restrict_of_ae ?_
    filter_upwards [hae] with x hx
    simp [respCoeffPlus, hx]

/-- The same datum at the cutoff bound's own grid, from its own premises:
`2 * d ≤ 3 ^ jStar` and positive definiteness of the canonical metric. -/
theorem exists_elliptic_representative_respCell_respCoeffMinus {jStar : ℕ}
    (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    (a : CoeffSpace d) :
    ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (respCell jStar F t) f ∧
        respCoeffMinus F a =ᵐ[volumeMeasureOn (respCell jStar F t)] f :=
  exists_elliptic_representative_respCoeffMinus (respGrid jStar F)
    (Geometry.isUnit_roundedGrid hjStar hm) t F a

/-- The plus twin of the previous. -/
theorem exists_elliptic_representative_respCell_respCoeffPlus {jStar : ℕ}
    (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    (a : CoeffSpace d) :
    ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (respCell jStar F t) f ∧
        respCoeffPlus F a =ᵐ[volumeMeasureOn (respCell jStar F t)] f :=
  exists_elliptic_representative_respCoeffPlus (respGrid jStar F)
    (Geometry.isUnit_roundedGrid hjStar hm) t F a

/-! ## The pulled-back flux is `L²` for the normalized reference-cube measure -/

/-- **The flux slot of the pulled-back centred optimizer field.**  The field
`y ↦ q⁻¹ ((optimizerField b u (q y) − Y).2)` is square integrable for
the normalized measure of the reference cube — the `hflux` slot of the generic CG product bridge
`abs_cubeAverage_vecDot_centered_scalar_cutoff_le_scaledWeakNormProduct`
(`Book/Ch05/.../JUpperBoundWeakNorms/Product/Bridge.lean`), whose potential slot is
`respCenteredPullbackH1` (`AffineSobolevPullback.lean`).

The elliptic datum is taken in the a.e.-representative form produced by
`exists_elliptic_representative_respCoeffMinus`/`…Plus` above, so the cutoff bound needs no
ellipticity
hypothesis of its own. -/
theorem memLp_two_normalizedCubeMeasure_pullback_flux {q : Mat d} (hq : IsUnit q) (t : ℤ)
    {lam Lam : ℝ} {b f : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) f)
    (hbf : b =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)] f)
    (u : AHarmonicFunction b (HighContrast.adaptedCell q t)) (Y : BlockVec d) :
    MemLp (fun y => matVecMul q⁻¹ ((optimizerField b u (matVecMul q y) - Y).2)) 2
      (normalizedCubeMeasure (originCube d t)) := by
  classical
  have hconv : IsOpenBoundedConvexDomain (HighContrast.adaptedCell q t) :=
    adaptedCell_isOpenBoundedConvexDomain q hq t
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) := by
    simpa [volumeMeasureOn] using hconv.isFiniteMeasure_restrict_volume
  -- The flux of the ELLIPTIC REPRESENTATIVE is `L²` on the cell (CG, `CoefficientField.lean`).
  have hfluxf : MemVectorL2 (HighContrast.adaptedCell q t)
      (fun x => matVecMul (f x) (u.toH1.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1.grad_memVectorL2
  -- a.e. equality on the cell transfers it to the coefficient itself, and the constant `Y.2` is
  -- `L²` because the cell has finite measure.
  have hae : (fun x => matVecMul (f x) (u.toH1.grad x))
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
        fun x => matVecMul (b x) (u.toH1.grad x) := by
    filter_upwards [hbf] with x hx
    rw [hx]
  have hfluxb : MemVectorL2 (HighContrast.adaptedCell q t)
      (fun x => (optimizerField b u x - Y).2) :=
    ((memLp_congr_ae hae).mp hfluxf).sub (memLp_const Y.2)
  -- coordinatewise, then pull back along `x = q y` with the post-composition `q⁻¹`
  have hG : GradMemL2On (HighContrast.adaptedCell q t) (fun x => (optimizerField b u x - Y).2) :=
    fun i => (memLp_pi_iff.mp hfluxb) i
  have hpull : GradMemL2On (openCubeSet (originCube d t))
      (fun y => matVecMul q⁻¹ ((optimizerField b u (matVecMul q y) - Y).2)) :=
    gradMemL2On_matVecMul_comp_matVecMul (G := fun x => (optimizerField b u x - Y).2) hq q⁻¹
      (image_openCubeSet_originCube_eq_adaptedCell q t).subset hG
  exact MemLp.of_eval fun i => memL2On_openCubeSet_normalizedCubeMeasure (hpull i)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Pointwise ellipticity and integrability of the recentred field at the carriers

Every cell-average step of the diagonal weak-norm estimate moves a matrix through the cell
average of the doubled optimizer field `optimizerField b u = (∇v, b ∇v)`, so those steps ask
for two things about the recentred coefficient `b = respCoeffMinus F a` (or `b = respCoeffPlus
F a`): uniform ellipticity of `b` on the cell and integrability of both slots of the doubled
field.

Pointwise ellipticity is **not** derivable.  A point of `CoeffSpace d` is an a.e. class, while
`IsEllipticFieldOn lam Lam U b` requires `IsEllipticMatrix lam Lam (b x)` at every `x ∈ U`; an
arbitrary representative of the class may be modified on a null set and remain locally uniformly
elliptic almost everywhere, so only the a.e. shape `IsAEEllipticFieldOn lam Lam U b` is
available.  The tree carries the a.e.-representative datum for the two response coefficients,
`exists_elliptic_representative_respCoeffMinus` and `…Plus` (`EllipticRepresentativeInputs.lean`):
some
field `f` pointwise elliptic on the cell and equal to `b` there almost everywhere.

This file discharges the integrability side conditions through that representative.  Integrals
are a.e. invariant, so the representative suffices.  The flux slot `x ↦ b(x) ∇u(x)` is `L²`
because the representative's flux is `L²` (`memVectorL2_matVecMul_of_isEllipticFieldOn`) and the
two agree almost everywhere; the scalar energy density `∇u · b ∇u` is the `vecDot` pairing of
two `L²` fields (`integrableOn_vecDot_of_memVectorL2`); and it is nonnegative almost everywhere
because the representative is elliptic on the cell, so the `vecDot` against its lower bound is
a.e. nonnegative and `volumeAverage` inherits that sign.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## Transport of the flux and the energy density across the a.e. representative -/

omit [NeZero d] in
/-- **The flux slot is `L²` through the a.e. representative.**  If `b` agrees almost everywhere
on a set `U` with a field `f` pointwise elliptic on a subset `V ⊆ U`, then `x ↦ b(x) ∇u(x)` is
`L²` on `V` for any `AHarmonicFunction` of `b` on `U`: the representative's flux is `L²` there
and the two coincide a.e. on `V`. -/
theorem memVectorL2_optimizerField_flux_of_aeEq {U V : Set (Vec d)} (hVU : V ⊆ U)
    {b f : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam V f)
    (hbf : b =ᵐ[volumeMeasureOn U] f) (u : AHarmonicFunction b U) :
    MemVectorL2 V (fun x => matVecMul (b x) (u.toH1.grad x)) := by
  have hbfV : b =ᵐ[volumeMeasureOn V] f :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) hbf
  have hgradV : MemVectorL2 V u.toH1.grad :=
    (u.toH1.grad_memVectorL2).mono_measure (MeasureTheory.Measure.restrict_mono hVU le_rfl)
  have hfluxf : MemVectorL2 V (fun x => matVecMul (f x) (u.toH1.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hgradV
  have hae : (fun x => matVecMul (f x) (u.toH1.grad x)) =ᵐ[volumeMeasureOn V]
      (fun x => matVecMul (b x) (u.toH1.grad x)) := by
    filter_upwards [hbfV] with x hx
    rw [hx]
  exact (MeasureTheory.memLp_congr_ae hae).mp hfluxf

omit [NeZero d] in
/-- **The scalar energy density is integrable through the a.e. representative.**  If `b` agrees
almost everywhere on `U` with a field `f` pointwise elliptic on `U`, then
`x ↦ ∇u(x) · b(x) ∇u(x)` is integrable on `U`: the gradient is `L²` and the representative's
flux is `L²`, so their `vecDot` pairing is `L¹`, and the a.e. equality transports it to `b`. -/
theorem integrableOn_energyDensity_of_aeEq {U : Set (Vec d)} {b f : CoeffField d}
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U f) (hbf : b =ᵐ[volumeMeasureOn U] f)
    (u : AHarmonicFunction b U) :
    IntegrableOn (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2) U := by
  have hgrad : MemVectorL2 U u.toH1.grad := u.toH1.grad_memVectorL2
  have hfluxf : MemVectorL2 U (fun x => matVecMul (f x) (u.toH1.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hgrad
  have hae : (fun x => matVecMul (f x) (u.toH1.grad x)) =ᵐ[volumeMeasureOn U]
      (fun x => matVecMul (b x) (u.toH1.grad x)) := by
    filter_upwards [hbf] with x hx
    rw [hx]
  have hfluxb : MemVectorL2 U (fun x => matVecMul (b x) (u.toH1.grad x)) :=
    (MeasureTheory.memLp_congr_ae hae).mp hfluxf
  simpa [optimizerField] using integrableOn_vecDot_of_memVectorL2 hgrad hfluxb

omit [NeZero d] in
/-- **The averaged energy density is nonnegative through the a.e. representative.**  If `b`
agrees almost everywhere on a measurable set `U` with a field `f` pointwise elliptic on `U`
with lower constant `lam > 0`, then the volume average over `U` of
`x ↦ ∇u(x) · b(x) ∇u(x)` is nonnegative.  On the full-measure set where `b = f`, the integrand
is bounded below by `lam * ‖∇u(x)‖²`, hence nonnegative, and `integral_nonneg_of_ae` gives the
sign of the average. -/
theorem volumeAverage_energyDensity_nonneg_of_aeEq {U : Set (Vec d)}
    (hU : MeasurableSet U) {b f : CoeffField d} {lam Lam : ℝ} (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U f) (hbf : b =ᵐ[volumeMeasureOn U] f)
    (u : AHarmonicFunction b U) :
    0 ≤ volumeAverage U (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2) := by
  unfold volumeAverage
  refine mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) ?_
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards [hbf, MeasureTheory.ae_restrict_mem hU] with x hxb hxU
  simp only [optimizerField]
  rw [hxb]
  have hlow := (hEll.2 x hxU).2.2.1 (u.toH1.grad x)
  have hnn : 0 ≤ lam * vecNormSq (u.toH1.grad x) := mul_nonneg hlam.le (vecNormSq_nonneg _)
  exact le_trans hnn hlow

/-! ## The recentred coefficient `a_- = respCoeffMinus F a` -/

/-- **Integrability of both slots of the doubled optimizer field on a triadic subcell, for
`respCoeffMinus F a`.**  For an invertible grid `q`, generation `t` and depth `n`, both slots of
the doubled optimizer field of an arbitrary `AHarmonicFunction` attached to `respCoeffMinus F a`
on `HighContrast.adaptedCell q t` are integrable on every aligned depth-`n` subcell
`adaptedCellAtCenter q (t - n) w`.  The gradient slot needs no ellipticity; the flux slot uses the
a.e.-elliptic representative on the subcell. -/
theorem integrableOn_optimizerField_respCoeffMinus_box (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (HighContrast.adaptedCell q t))
    (n : ℕ) (w : Fin d → ℤ) (hw : w ∈ triadicIndexBox d n) (j : Fin d) :
    IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) u x).1 j)
        (adaptedCellAtCenter q (t - (n : ℤ)) w) ∧
      IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) u x).2 j)
        (adaptedCellAtCenter q (t - (n : ℤ)) w) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffMinus q hq t F a
  have hVU : adaptedCellAtCenter q (t - (n : ℤ)) w ⊆ HighContrast.adaptedCell q t :=
    adaptedCellAtCenter_subset_adaptedCell q t n hw
  have hVfin : volume (adaptedCellAtCenter q (t - (n : ℤ)) w) ≠ ⊤ :=
    Geometry.volume_adaptedCellAtCenter_ne_top q (t - (n : ℤ)) w
  have : IsFiniteMeasure (volumeMeasureOn (adaptedCellAtCenter q (t - (n : ℤ)) w)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_adaptedCellAtCenter q hq (t - (n : ℤ))
        w).isFiniteMeasure_restrict_volume
  have hVmeas : MeasurableSet (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w).measurableSet
  have hEllV : IsEllipticFieldOn lam Lam (adaptedCellAtCenter q (t - (n : ℤ)) w) f :=
    IsEllipticFieldOn.mono hEll hVmeas hVU
  have hflux : MemVectorL2 (adaptedCellAtCenter q (t - (n : ℤ)) w)
      (fun x => matVecMul ((respCoeffMinus F a) x) (u.toH1.grad x)) :=
    memVectorL2_optimizerField_flux_of_aeEq hVU hEllV hae u
  refine ⟨integrableOn_optimizerField_fst_pub hVU hVfin (respCoeffMinus F a) u j, ?_⟩
  have hmem : MemLp (fun x => (optimizerField (respCoeffMinus F a) u x).2 j) 2
      (volumeMeasureOn (adaptedCellAtCenter q (t - (n : ℤ)) w)) := by
    simpa [optimizerField] using (MeasureTheory.memLp_pi_iff.mp hflux) j
  exact MemLp.integrable (by norm_num) hmem

/-- **Integrability of the scalar energy density on the parent cell, for
`respCoeffMinus F a`.**  The energy density `x ↦ ∇u(x) · (respCoeffMinus F a)(x) ∇u(x)` of an
arbitrary `AHarmonicFunction` attached to `respCoeffMinus F a` on the adapted cell is integrable
there. -/
theorem integrableOn_energyDensity_respCoeffMinus (q : Mat d) (hq : IsUnit q)
    (t : ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (HighContrast.adaptedCell q t)) :
    IntegrableOn (fun x => vecDot (optimizerField (respCoeffMinus F a) u x).1
      (optimizerField (respCoeffMinus F a) u x).2) (HighContrast.adaptedCell q t) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffMinus q hq t F a
  exact integrableOn_energyDensity_of_aeEq hEll hae u

/-- **Nonnegativity of the averaged energy density, for `respCoeffMinus F a`.**  The volume
average over the adapted cell of the energy density of an arbitrary `AHarmonicFunction` attached
to `respCoeffMinus F a` is nonnegative. -/
theorem energyDensity_average_nonneg (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (HighContrast.adaptedCell q t)) :
    0 ≤ volumeAverage (HighContrast.adaptedCell q t)
      (fun x => vecDot (optimizerField (respCoeffMinus F a) u x).1
        (optimizerField (respCoeffMinus F a) u x).2) := by
  obtain ⟨lam, Lam, f, hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffMinus q hq t F a
  exact volumeAverage_energyDensity_nonneg_of_aeEq
    (adaptedCell_isOpenBoundedConvexDomain q hq t).isOpen.measurableSet hlam hEll hae u

/-! ## The transposed recentred coefficient `a_+ = respCoeffPlus F a` -/

/-- **Integrability of both slots of the doubled optimizer field on a triadic subcell, for
`respCoeffPlus F a`.**  The transposed twin of
`integrableOn_optimizerField_respCoeffMinus_box`. -/
theorem integrableOn_optimizerField_respCoeffPlus_box (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (HighContrast.adaptedCell q t))
    (n : ℕ) (w : Fin d → ℤ) (hw : w ∈ triadicIndexBox d n) (j : Fin d) :
    IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) u x).1 j)
        (adaptedCellAtCenter q (t - (n : ℤ)) w) ∧
      IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) u x).2 j)
        (adaptedCellAtCenter q (t - (n : ℤ)) w) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffPlus q hq t F a
  have hVU : adaptedCellAtCenter q (t - (n : ℤ)) w ⊆ HighContrast.adaptedCell q t :=
    adaptedCellAtCenter_subset_adaptedCell q t n hw
  have hVfin : volume (adaptedCellAtCenter q (t - (n : ℤ)) w) ≠ ⊤ :=
    Geometry.volume_adaptedCellAtCenter_ne_top q (t - (n : ℤ)) w
  have : IsFiniteMeasure (volumeMeasureOn (adaptedCellAtCenter q (t - (n : ℤ)) w)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_adaptedCellAtCenter q hq (t - (n : ℤ))
        w).isFiniteMeasure_restrict_volume
  have hVmeas : MeasurableSet (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w).measurableSet
  have hEllV : IsEllipticFieldOn lam Lam (adaptedCellAtCenter q (t - (n : ℤ)) w) f :=
    IsEllipticFieldOn.mono hEll hVmeas hVU
  have hflux : MemVectorL2 (adaptedCellAtCenter q (t - (n : ℤ)) w)
      (fun x => matVecMul ((respCoeffPlus F a) x) (u.toH1.grad x)) :=
    memVectorL2_optimizerField_flux_of_aeEq hVU hEllV hae u
  refine ⟨integrableOn_optimizerField_fst_pub hVU hVfin (respCoeffPlus F a) u j, ?_⟩
  have hmem : MemLp (fun x => (optimizerField (respCoeffPlus F a) u x).2 j) 2
      (volumeMeasureOn (adaptedCellAtCenter q (t - (n : ℤ)) w)) := by
    simpa [optimizerField] using (MeasureTheory.memLp_pi_iff.mp hflux) j
  exact MemLp.integrable (by norm_num) hmem

/-- **Integrability of the scalar energy density on the parent cell, for `respCoeffPlus F a`.**
The transposed twin of `integrableOn_energyDensity_respCoeffMinus`. -/
theorem integrableOn_energyDensity_respCoeffPlus (q : Mat d) (hq : IsUnit q)
    (t : ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (HighContrast.adaptedCell q t)) :
    IntegrableOn (fun x => vecDot (optimizerField (respCoeffPlus F a) u x).1
      (optimizerField (respCoeffPlus F a) u x).2) (HighContrast.adaptedCell q t) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffPlus q hq t F a
  exact integrableOn_energyDensity_of_aeEq hEll hae u

/-- **Nonnegativity of the averaged energy density, for `respCoeffPlus F a`.**  The transposed
twin of `energyDensity_average_nonneg`. -/
theorem energyDensity_average_nonneg_plus (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (HighContrast.adaptedCell q t)) :
    0 ≤ volumeAverage (HighContrast.adaptedCell q t)
      (fun x => vecDot (optimizerField (respCoeffPlus F a) u x).1
        (optimizerField (respCoeffPlus F a) u x).2) := by
  obtain ⟨lam, Lam, f, hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffPlus q hq t F a
  exact volumeAverage_energyDensity_nonneg_of_aeEq
    (adaptedCell_isOpenBoundedConvexDomain q hq t).isOpen.measurableSet hlam hEll hae u

end

end HCPolySupport.HighContrast.Multiscale
end
