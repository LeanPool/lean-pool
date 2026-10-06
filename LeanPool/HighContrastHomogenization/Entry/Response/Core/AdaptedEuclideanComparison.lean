/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.BridgeComparisons
public import LeanPool.HighContrastHomogenization.Geometry.ReferenceAspectRatio

/-!
# High-contrast homogenization: Entry.Response.Core.AdaptedEuclideanComparison

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Euclidean-versus-adapted annealed block comparison

This file proves the two Euclidean-versus-adapted grid comparisons of HC Lemma 2.15, the E1 and E2
kernels that `p.response.transfer` uses to normalize its source term. A capped Whitney-type
covering of a cube by maximal adapted cells gives a row-volume bound and a summable total mass;
the geometrically decaying rows below the cap are then controlled by the source bound and
recombined into an annealed-block comparison for the actual capped partition. Two elementary
Loewner-order lemmas — a forward form absorbing a scaled error into a bound, and a reverse form
subtracting one out to isolate a lower bound — turn this partition comparison into the E1
inequality `𝐀hom_{t+ℓ,Id} ≤ (1+C·𝔢(m)·3^{-ℓ})·𝐀hom_{t,q}` and the E2 inequality
`𝐀hom_{t+ℓ+r,q} ≤ 𝐀hom_{t+ℓ,Id} + C·𝔢(m)·3^{-r}·𝐀hom_{t,q}`.
-/

section
/-!
Plan for E1, then E2 (HC).

1. Establish identity-grid and integer-translation support, and integrate the
  source bound for standard cells at arbitrary locations. The bounded-window
  multiplier is used after translating an aligned ancestor into its window.
2. Apply standard Whitney subadditivity to obtain an annealed source estimate
  for every rounded adapted cell, without inserting an eccentricity factor:
  the inverse norm of the rounded grid is at most two.
3. Tile a Euclidean cube by maximal adapted cells capped at t. The cap has
  expectation adaptedMean q t by integer stationarity. Lower rows use step 2,
  with a direct relative inverse-norm bound of order e (the general gridRatio
  API raises distortion to power 2d and would lose the required dependence).
  Sum the geometric deficit series, then apply reference normalization.
  Antitonicity does not bound smaller means by the cap mean; only the cap
  uses stationarity, and every smaller row uses the source estimate.
4. Only after E1 closes, exchange grids for E2, cap at t+ell, and normalize
  the source error at t. Constants are chosen before every law and metric.

Every lemma is compiled under the package lock with warnings as errors.
No result from the response-transfer skeleton
`HCPoly.Entry.Multiscale.ResponseTransferSkeleton` is consumed.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter
  adaptedMean annealedBlock blockMatEntry_blockScale blockScale coarseBlock
  toFullBlockMat_eq_blockMatEntry)
open HCPolySupport.HighContrast (adaptedCell adaptedCellTranslate centeredCube standardCell
  standardCellCenter)
namespace HCPolySupport.HighContrast.Multiscale.Adapter

open MeasureTheory Geometry
open scoped Matrix.Norms.L2Operator

/-- The adapted cell of the identity grid at generation `j` is the centered cube of side
`3 ^ j`. -/
theorem identity_cell {d : ℕ} (j : ℤ) :
    adaptedCell (1 : Mat d) j = centeredCube d j := by
  have hid : matVecMul (1 : Mat d) = (fun v => v) :=
    funext fun v => by rw [matVecMul_eq_mulVec, Matrix.one_mulVec]
  simp [adaptedCell, hid]

/-- Any generation-`j` standard cell centered at `w` has a generation-`j` recentered copy,
centered at some `u`, that lies inside the generation-`J` centered cube for `j ≤ J`; the two
centers differ by an integer translation `v` at generation `J`. -/
theorem standard_recenter {d : ℕ} {j J : ℤ} (hj : j ≤ J) (w : Fin d → ℤ) :
    ∃ u v : Fin d → ℤ, standardCell d j u ⊆ centeredCube d J ∧
      standardCellCenter j w = standardCellCenter j u + standardCellCenter J v := by
  obtain ⟨v, hv⟩ := Source.exists_standardCell_ancestor hj w
  let n := (J - j).toNat
  have hn : j + (n : ℤ) = J := by
    dsimp [n]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  let u : Fin d → ℤ := fun i => w i - (3 : ℤ) ^ n * v i
  have hp : (3 : ℝ) ^ J = (3 : ℝ) ^ j * (3 : ℝ) ^ n := by
    rw [← hn, zpow_add₀ (by norm_num), zpow_natCast]
  have hc : standardCellCenter j w = standardCellCenter j u + standardCellCenter J v := by
    ext i
    simp only [standardCellCenter, u, Pi.add_apply, Int.cast_sub, Int.cast_mul,
      Int.cast_pow, Int.cast_ofNat, hp]
    ring
  refine ⟨u, v, ?_, hc⟩
  intro x hx
  have hxw : standardCellCenter J v + x ∈ standardCell d j w := by
    rw [Recurrence.mem_standardCell_iff] at hx ⊢
    intro i
    have hci := congrFun hc i
    simp only [standardCellCenter, Pi.add_apply] at hci ⊢
    constructor <;> linarith only [hci, (hx i).1, (hx i).2]
  have hparent := hv hxw
  rw [Recurrence.mem_standardCell_iff] at hparent
  rw [Recurrence.mem_centeredCube_iff]
  intro i
  have hi := hparent i
  simp only [standardCellCenter, Pi.add_apply] at hi
  constructor <;> linarith only [hi.1, hi.2]

/-- The rounded-grid analogue of `standard_recenter`: a generation-`j` adapted cell indexed by
`w`, `j ≤ J`, has a recentered index `u` whose cell lies inside the generation-`J` adapted cell,
and the annealed block over the two cells agrees, since integer translation of an adapted cell
does not change its annealed block under a stationary law. -/
theorem rounded_recenter {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P)
    (J : ℕ) (hJ : 2 * d ≤ 3 ^ J) (m : Mat d) (hm : m.PosDef)
    (j : ℤ) (hj : j ≤ (J : ℤ)) (w : Fin d → ℤ) :
    ∃ u : Fin d → ℤ,
      adaptedCellAtCenter (explicitRoundedGrid J m) j u ⊆ adaptedCell (explicitRoundedGrid J m) J ∧
      annealedBlock P (adaptedCellAtCenter (explicitRoundedGrid J m) j w) =
        annealedBlock P (adaptedCellAtCenter (explicitRoundedGrid J m) j u) := by
  obtain ⟨u, v, hu, hc⟩ := standard_recenter hj w
  refine ⟨u, ?_, ?_⟩
  · rw [adaptedCellAtCenter_eq_affine_standardCell, adaptedCell]
    exact Set.image_mono hu
  · obtain ⟨z, hz⟩ := Annealed.adaptedCellCenter_eq_intTranslation J m le_rfl v
    have hcent : adaptedCellCenter (explicitRoundedGrid J m) j w =
        adaptedCellCenter (explicitRoundedGrid J m) j u +
          HCPolySupport.Source.AKL.intTranslation z := by
      simp only [Recurrence.adaptedCellCenter_eq] at hz ⊢
      rw [hc, matVecMul_eq_mulVec, Matrix.mulVec_add]
      exact congrArg (fun x => matVecMul (explicitRoundedGrid J m) (standardCellCenter j u) + x) hz
    change annealedBlock P (adaptedCellTranslate _ j _) = _
    rw [hcent]
    exact Source.annealedBlock_adapted_add_intTranslation P hstat
      (explicitRoundedGrid J m) (isUnit_roundedGrid hJ hm) j
      (adaptedCellCenter (explicitRoundedGrid J m) j u) z

/-- Averaging a pointwise Loewner bound `coarseBlock U a ≤ c * X a * E` (a.e. in `a`, `X`
integrable) gives the corresponding bound on the annealed block, scaled by the expectation of
`X`. -/
theorem annealed_scale_bound {d : ℕ} {P : Measure (CoeffSpace d)}
    {U : Set (Vec d)} {X : CoeffSpace d → ℝ} {E : BlockMat d} (c : ℝ)
    (hU : HasIntegrableCoarseBlock P U) (hX : Integrable X P)
    (hb : ∀ᵐ a ∂P, BlockMatLoewnerLE (coarseBlock U a) (blockScale (c * X a) E)) :
    BlockMatLoewnerLE (annealedBlock P U) (blockScale (c * ∫ a, X a ∂P) E) := by
  have hi (α β : BlockCoord d) : Integrable
      (fun a => blockMatEntry (blockScale (c * X a) E) α β) P := by
    simpa only [blockMatEntry_blockScale] using (hX.const_mul c).mul_const (blockMatEntry E α β)
  have h := Analysis.blockMatLoewnerLE_integral hU hi hb
  have he : ofFullBlockMat (Matrix.of fun α β =>
      ∫ a, blockMatEntry (blockScale (c * X a) E) α β ∂P) =
      blockScale (c * ∫ a, X a ∂P) E := by
    rw [← ofFullBlockMat_toFullBlockMat (blockScale (c * ∫ a, X a ∂P) E)]
    congr 1
    ext α β
    simp only [Matrix.of_apply, toFullBlockMat_eq_blockMatEntry,
      blockMatEntry_blockScale, integral_mul_const, integral_const_mul]
  rw [he] at h
  simpa only [Matrix.of_apply, Annealed.fullBlock_integral_coarseBlock,
    ofFullBlockMat_toFullBlockMat] using! h

/-- The source bound for aligned cells has no eccentricity cost: the local
Whitney proof only uses the inverse-norm bound two. Recenter fine cells at J,
and use stationarity and monotonicity for coarser cells. -/
theorem aligned_source_bound (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc C : ℝ, 0 < Csrc ∧ 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (J : ℕ), 2 * d ≤ 3 ^ J →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (J : ℤ) →
          ∀ (m : Mat d), m.PosDef →
            adaptedCell (explicitRoundedGrid J m) J ⊆ centeredCube d (2 * (J : ℤ)) →
            ∀ (j : ℤ) (w : Fin d → ℤ),
              BlockMatLoewnerLE (annealedBlock P (adaptedCellAtCenter (explicitRoundedGrid J m)
                j w))
                (blockScale (C * (3 : ℝ) ^ (γ * max ((J : ℝ) - (j : ℝ)) 0)) E) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Csrc, C₀, hCsrc, _hC₀, hsource⟩ :=
    Source.source_multiplier_and_adapted_bound d hd γ hγ
  let D : ℝ := 12 * (d : ℝ) ^ ((3 : ℝ) / 2) / (1 - (3 : ℝ) ^ (-(1 - γ)))
  have hden : 0 < 1 - (3 : ℝ) ^ (-(1 - γ)) :=
    sub_pos.mpr (Annealed.bridge_fine_ratio_mem_Ico hγ.2).2
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨Csrc, 2 * D, hCsrc, by positivity, ?_⟩
  intro P hP E Ψ K S hstat hdag J hJ hsrc m hm hwindow
  obtain ⟨ell, X, _hell, _hX, hform, _hmin, hlp, _hi, _hmoment, hnorm, hpath⟩ :=
    hsource P E Ψ K S hstat hdag J hJ hsrc
  have hX0 (a) : 0 ≤ X a := by rw [hform]; positivity
  have hEX := Annealed.source_envelope_integral_le_two d hd γ hγ P X hX0 hlp hnorm
  have hQ : 1 ≤ ENNReal.ofReal (bigQ d γ : ℝ) := by
    apply ENNReal.one_le_ofReal.mpr
    exact_mod_cast (bigQ_two_le d γ hγ).trans' (by norm_num)
  have hlocal (j : ℤ) (y : Vec d)
      (hcell : adaptedCellTranslate (explicitRoundedGrid J m) j y ⊆ centeredCube d (2 * (J : ℤ))) :
      BlockMatLoewnerLE (annealedBlock P (adaptedCellTranslate (explicitRoundedGrid J m) j y))
        (blockScale (2 * D * (3 : ℝ) ^ (γ * max ((J : ℝ) - (j : ℝ)) 0)) E) := by
    have hint := Annealed.hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag
      J hJ m hm j y
    have hb : ∀ᵐ a ∂P, BlockMatLoewnerLE
        (coarseBlock (adaptedCellTranslate (explicitRoundedGrid J m) j y) a)
        (blockScale ((D * (3 : ℝ) ^ (γ * max ((J : ℝ) - (j : ℝ)) 0)) * X a) E) := by
      filter_upwards [hpath] with a ha
      simpa only [D, mul_assoc, mul_left_comm, mul_comm] using
        Source.adapted_bound_of_standard γ hγ E hdag.refBlock_posDef a J (X a) (hX0 a)
          ha.1 (inverseNormLE_roundedGrid hJ hm) j y hcell
    exact (annealed_scale_bound _ hint (hlp.integrable hQ) hb).trans
      (Source.blockScale_le_blockScale_of_pos hdag.refBlock_posDef (by
        have hD' : 0 ≤ D * (3 : ℝ) ^ (γ * max ((J : ℝ) - (j : ℝ)) 0) := by positivity
        calc
          D * (3 : ℝ) ^ (γ * max ((J : ℝ) - (j : ℝ)) 0) * (∫ a, X a ∂P)
              ≤ D * (3 : ℝ) ^ (γ * max ((J : ℝ) - (j : ℝ)) 0) * 2 :=
            mul_le_mul_of_nonneg_left hEX hD'
          _ = 2 * D * (3 : ℝ) ^ (γ * max ((J : ℝ) - (j : ℝ)) 0) := by ring))
  intro j w
  by_cases hj : j ≤ (J : ℤ)
  · obtain ⟨u, hu, he⟩ := rounded_recenter P hstat J hJ m hm j hj w
    rw [he]
    exact hlocal j (adaptedCellCenter (explicitRoundedGrid J m) j u) (hu.trans hwindow)
  · have hJj : (J : ℤ) ≤ j := le_of_lt (lt_of_not_ge hj)
    rw [Annealed.annealedBlock_adaptedCellAtCenter P hstat J hJ m hm j hJj w]
    have hmono := Annealed.adaptedMean_antitone d hd P γ E Ψ K S hstat hdag
      J hJ m hm J j le_rfl hJj
    have hb := hlocal J 0 (by simpa [adaptedCellTranslate] using hwindow)
    have hJR : (J : ℝ) ≤ (j : ℝ) := by exact_mod_cast hJj
    simpa [adaptedCellTranslate, adaptedMean, max_eq_right (sub_nonpos.mpr hJR)] using
      hmono.trans (by
        simpa [adaptedCellTranslate, adaptedMean, HighContrast.adaptedCell,
          HighContrast.centeredCube] using hb)

end HCPolySupport.HighContrast.Multiscale.Adapter
end

section
open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (adaptedCellCenter)
open HCPolySupport.HighContrast (adaptedCell adaptedCellTranslate standardCell)
namespace HCPolySupport.HighContrast.Multiscale.Adapter

open MeasureTheory Geometry
open scoped Matrix.Norms.L2Operator

/-- The capped Whitney row bound uses only the inverse norm of the relative
matrix. In particular its constant is linear in that norm. -/
theorem lower_row_volume {d : ℕ} [NeZero d] {q q' : Mat d} {K : ℝ}
    (hq : IsUnit q) (hq' : IsUnit q') (hK : 0 ≤ K)
    (hInv : InverseNormLE (q⁻¹ * q') K)
    (j cap r : ℤ) (hr : r < cap) (y : Vec d) :
    ∑ _z ∈ (finite_maximalAdaptedCellCenters_of_volume_ne_top hq
        (Transport.volume_adaptedCellTranslate_ne_top q' j y) cap r).toFinset,
      (volume (adaptedCell q r)).toReal / (volume (adaptedCellTranslate q' j y)).toReal ≤
        (6 * (d : ℝ) * K * Real.sqrt d) * (3 : ℝ) ^ ((r : ℝ) - (j : ℝ)) := by
  classical
  let V := adaptedCellTranslate (q⁻¹ * q') j (matVecMul q⁻¹ y)
  have hvol := volume_le_of_near_complement hK hInv
    (j := j) (y := matVecMul q⁻¹ y)
    (A := ⋃ w ∈ maximalCellIndices V cap r, standardCell d r w)
    (s := Real.sqrt d * (3 : ℝ) ^ (r + 1)) (by positivity)
    (by
      rintro x hx
      obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
      exact hw.subset hxw)
    (by
      rintro x hx
      obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
      exact exists_not_mem_of_mem_maximalCell hr hw hxw)
  have hc : 2 * (d : ℝ) * (K * (Real.sqrt d * (3 : ℝ) ^ (r + 1))) *
      (3 : ℝ) ^ (-j) = (6 * (d : ℝ) * K * Real.sqrt d) *
        (3 : ℝ) ^ ((r : ℝ) - (j : ℝ)) := by
    rw [← Int.cast_sub, Real.rpow_intCast, zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0),
      zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_neg, div_eq_mul_inv]
    ring
  rw [hc] at hvol
  have hsum := sum_relVolume_le_of_volume_le
    (volume_adaptedCellTranslate_pos hInv j (matVecMul q⁻¹ y)).ne'
    (Transport.volume_adaptedCellTranslate_ne_top (q⁻¹ * q') j (matVecMul q⁻¹ y))
    (by positivity : 0 ≤ (6 * (d : ℝ) * K * Real.sqrt d) *
      (3 : ℝ) ^ ((r : ℝ) - (j : ℝ))) hvol
  simp_rw [← adaptedCell_relVolume_eq_standard_preimage hq hq' j r y] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum ⊢
  have hcard :
      (finite_maximalAdaptedCellCenters_of_volume_ne_top hq
        (Transport.volume_adaptedCellTranslate_ne_top q' j y) cap r).toFinset.card =
      (finite_maximalCellIndices
        (Transport.volume_adaptedCellTranslate_ne_top (q⁻¹ * q') j (matVecMul q⁻¹ y)) cap
          r).toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card _
        (finite_maximalAdaptedCellCenters_of_volume_ne_top hq
          (Transport.volume_adaptedCellTranslate_ne_top q' j y) cap r),
      ← Set.ncard_eq_toFinset_card _
        (finite_maximalCellIndices
          (Transport.volume_adaptedCellTranslate_ne_top (q⁻¹ * q') j (matVecMul q⁻¹ y)) cap r),
      ncard_maximalAdaptedCellCenters_eq_preimage hq,
      preimage_matVecMul_adaptedCellTranslate_eq hq]
  rw [hcard]
  exact hsum

/-- A norm bound `‖q'⁻¹ * q‖ ≤ K` transfers to an `InverseNormLE` bound on `q⁻¹ * q'` itself, by
cancelling the two grids and applying the operator-norm inequality to the inverse product. -/
theorem relative_inverse_bound {d : ℕ} {q q' : Mat d} {K : ℝ}
    (hq : IsUnit q) (hq' : IsUnit q') (hK : ‖q'⁻¹ * q‖ ≤ K) :
    InverseNormLE (q⁻¹ * q') K := by
  intro v
  have hcancel : (q'⁻¹ * q) * (q⁻¹ * q') = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc q q⁻¹ q',
      Matrix.mul_nonsing_inv q ((Matrix.isUnit_iff_isUnit_det q).mp hq),
      Matrix.one_mul, Matrix.nonsing_inv_mul q' ((Matrix.isUnit_iff_isUnit_det q').mp hq')]
  have hb := vecNormSq_mulVec_le_opNorm (q'⁻¹ * q) (Matrix.mulVec (q⁻¹ * q') v)
  rw [Matrix.mulVec_mulVec, hcancel, Matrix.one_mulVec] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) hK 2) (vecNormSq_nonneg _))

/-- The volume-ratio weights of the maximal adapted `q`-cells tiling a `q'`-cell `W` are
summable and sum to one: the maximal cells are pairwise disjoint and their union covers `W` up
to a null set. -/
theorem maximal_mass {d : ℕ} [NeZero d]
    (q q' : Mat d) (hq : IsUnit q) (hq' : IsUnit q') (n cap : ℤ) (y : Vec d) :
    let W := adaptedCellTranslate q' n y
    let I := {p : ℤ × (Fin d → ℤ) // IsMaximalAdaptedCellIn W q cap p.1 p.2}
    let w := fun i : I => (volume (adaptedCellAtCenter q i.1.1 i.1.2)).toReal / (volume W).toReal
    Summable w ∧ (∑' i, w i) = 1 := by
  intro W I w
  let s := {p : ℤ × (Fin d → ℤ) | IsMaximalAdaptedCellIn W q cap p.1 p.2}
  have hsub : ∀ i ∈ s, adaptedCellAtCenter q i.1 i.2 ⊆ W := fun _ hi => hi.1.2
  have hdis := pairwiseDisjoint_maximalAdaptedCellPairs W q hq cap
  have hnull := volume_diff_iUnion_maximalAdaptedCells_of_isOpen hq
    (isOpen_adaptedCellTranslate hq' n y) cap
  have hWfin : volume W ≠ ⊤ := Transport.volume_adaptedCellTranslate_ne_top q' n y
  let : IsFiniteMeasure (volumeMeasureOn W) := ⟨by simpa [volumeMeasureOn] using hWfin.lt_top⟩
  have hmeas (i) (_hi : i ∈ s) : MeasurableSet (adaptedCellAtCenter q i.1 i.2) :=
    (isOpen_adaptedCellTranslate hq i.1 (adaptedCellCenter q i.1 i.2)).measurableSet
  have hw : Summable w := summable_volumeRatio (s := s) (W := W) (U := fun i =>
    adaptedCellAtCenter q i.1 i.2)
    hmeas hsub hdis
  have hW0 : (volume W).toReal ≠ 0 := by
    dsimp [W]
    rw [volume_adaptedCellTranslate_toReal]
    have hdq : q'.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det q').mp hq').ne_zero
    positivity
  exact ⟨hw, Source.tsum_volumeRatio_eq_one (Set.to_countable s)
    (W := W) (U := fun i => adaptedCellAtCenter q i.1 i.2) hW0 hmeas hsub hdis hnull⟩

end HCPolySupport.HighContrast.Multiscale.Adapter
end

section
open HCPolySupport.HighContrast (blockScale blockVecDot_blockMatVecMul_eq_sum)
namespace HCPolySupport.HighContrast.Multiscale.Adapter

open MeasureTheory

/-- If each fine row's weight below a cap is bounded by a geometrically decaying multiple `D *
3 ^ (t - n)` of a base scale, the row-weighted geometric sum over all indices below the cap is
summable and bounded by the total mass `D` times the geometric series constant, evaluated at the
cap. -/
theorem fine_weight_bound {ι : Type*} [Countable ι]
    (w : ι → ℝ) (r : ι → ℤ) (hw0 : ∀ i, 0 ≤ w i) (hw : Summable w)
    (cap n : ℤ) (D : ℝ) (hD : 0 ≤ D)
    (hrow : ∀ t < cap, (∑' i : {i // r i = t}, w i) ≤ D * (3 : ℝ) ^ ((t : ℝ) - n))
    (γ : ℝ) (hγ : γ < 1) :
    Summable (fun i : {i // r i < cap} => w i * (3 : ℝ) ^ (γ * ((cap : ℝ) - r i))) ∧
      (∑' i : {i // r i < cap}, w i * (3 : ℝ) ^ (γ * ((cap : ℝ) - r i))) ≤
        D / (1 - (3 : ℝ) ^ (-(1 - γ))) * (3 : ℝ) ^ (-((n : ℝ) - cap)) := by
  let L := {i // r i < cap}
  have hwL : Summable (fun i : L => w i) := hw.subtype _
  apply Annealed.bridge_fine_weighted_sum (fun i : L => w i) (fun i => r i)
    (fun i => hw0 i) hwL cap n (fun i => i.2) D hD _ γ hγ
  intro t
  by_cases ht : t < cap
  · let e : {i : L // r i = t} → {i // r i = t} := fun i => ⟨i.1.1, i.2⟩
    have he : Function.Injective e := by
      intro i k h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : {i // r i = t} => x.1) h
    exact (Summable.tsum_le_tsum_of_inj e he (fun i _ => hw0 i)
      (fun _ => le_rfl) (hwL.subtype _) (hw.subtype _)).trans (hrow t ht)
  · have : IsEmpty {i : L // r i = t} := ⟨fun i => ht (i.2 ▸ i.1.2)⟩
    simp only [tsum_empty]
    positivity

/-- A weighted finite sum `∑ w i * f i` splits by whether the row index reaches the cap: the
at-cap terms are bounded using the total mass `≤ 1` and the cap bound `a`, and the below-cap
terms are bounded using the geometric weighted-sum bound `T` from `fine_weight_bound`, together
giving `a + c * T * b`. -/
theorem finite_cap_sum {ι : Type*}
    (w : ι → ℝ) (r : ι → ℤ) (f : ι → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw : Summable w) (hmass : (∑' i, w i) ≤ 1)
    (cap : ℤ) (hr : ∀ i, r i ≤ cap) (γ a b c T : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hcap : ∀ i, r i = cap → f i ≤ a)
    (hlow : ∀ i, r i < cap → f i ≤ c * (3 : ℝ) ^ (γ * ((cap : ℝ) - r i)) * b)
    (hs : Summable (fun i : {i // r i < cap} => w i * (3 : ℝ) ^ (γ * ((cap : ℝ) - r i))))
    (ht : (∑' i : {i // r i < cap}, w i * (3 : ℝ) ^ (γ * ((cap : ℝ) - r i))) ≤ T)
    (F : Finset ι) :
    (∑ i ∈ F, w i * f i) ≤ a + c * T * b := by
  classical
  have htop : (∑ i ∈ F with ¬ r i < cap, w i * f i) ≤ a := by
    calc
      _ ≤ ∑ i ∈ F with ¬ r i < cap, w i * a := Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_left (hcap i (by have := (Finset.mem_filter.mp hi).2; have := hr i;
          omega)) (hw0 i))
      _ = (∑ i ∈ F with ¬ r i < cap, w i) * a := (Finset.sum_mul ..).symm
      _ ≤ 1 * a := mul_le_mul_of_nonneg_right
        ((hw.sum_le_tsum _ (fun i _ => hw0 i)).trans hmass) ha
      _ = a := one_mul a
  have htail : (∑ i ∈ F with r i < cap, w i * f i) ≤ c * T * b := by
    have hsum := hs.sum_le_tsum (F.subtype (fun i => r i < cap)) (fun i _ =>
      mul_nonneg (hw0 i) (Real.rpow_nonneg (by norm_num) _))
    rw [Finset.sum_subtype_eq_sum_filter
      (f := fun i => w i * (3 : ℝ) ^ (γ * ((cap : ℝ) - r i)))] at hsum
    calc
      _ ≤ ∑ i ∈ F with r i < cap, w i *
          (c * (3 : ℝ) ^ (γ * ((cap : ℝ) - r i)) * b) :=
        Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
          (hlow i (Finset.mem_filter.mp hi).2) (hw0 i))
      _ = c * (∑ i ∈ F with r i < cap, w i * (3 : ℝ) ^ (γ * ((cap : ℝ) - r i))) * b := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ c * T * b := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hsum.trans ht) hc) hb
  calc
    _ = (∑ i ∈ F with r i < cap, w i * f i) +
        (∑ i ∈ F with ¬ r i < cap, w i * f i) :=
      (Finset.sum_filter_add_sum_filter_not F (fun i => r i < cap) _).symm
    _ ≤ c * T * b + a := add_le_add htail htop
    _ = a + c * T * b := add_comm _ _

/-- The doubled quadratic form `v. (1/2) A v` is additive in the block matrix `A`. -/
theorem quadratic_add {d : ℕ} (M N : FullBlockMat d) (v : BlockVec d) :
    (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat (M + N)) v) =
      (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat M) v) +
      (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat N) v) := by
  simp only [blockVecDot_blockMatVecMul_eq_sum, blockMatEntry_ofFullBlockMat,
    Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

/-- The doubled quadratic form `v. (1/2) A v` is nonnegative when `A` is positive definite. -/
theorem quadratic_nonneg {d : ℕ} {A : BlockMat d}
    (hA : Book.Ch02.BlockPosDef A) (v : BlockVec d) :
    0 ≤ (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul A v) := by
  by_cases hv : v = 0
  · simp [hv, blockVecDot, vecDot]
  · exact mul_nonneg (by norm_num) (hA v hv).le

/-- The doubled quadratic form `v. (1/2) A v` scales linearly under scalar multiplication of
`A`. -/
theorem quadratic_smul {d : ℕ} (c : ℝ) (M : FullBlockMat d) (v : BlockVec d) :
    (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat (c • M)) v) =
      c * ((1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat M) v)) :=
  Source.quadratic_blockScale c (ofFullBlockMat M) v

/-- The block-matrix specialization of `finite_cap_sum`, via the quadratic form: a weighted sum
of blocks `B i`, each Loewner-bounded by `A` at the cap and by a geometrically decaying multiple
of `E` below the cap, is itself Loewner-bounded by `A + (c * T) • E`. -/
theorem finite_block_cap {d : ℕ} {ι : Type*}
    (w : ι → ℝ) (r : ι → ℤ) (B : ι → BlockMat d) (A E : BlockMat d)
    (hw0 : ∀ i, 0 ≤ w i) (hw : Summable w) (hmass : (∑' i, w i) ≤ 1)
    (cap : ℤ) (hr : ∀ i, r i ≤ cap) (γ c T : ℝ)
    (hA : Book.Ch02.BlockPosDef A) (hE : Book.Ch02.BlockPosDef E) (hc : 0 ≤ c)
    (hcap : ∀ i, r i = cap → BlockMatLoewnerLE (B i) A)
    (hlow : ∀ i, r i < cap →
      BlockMatLoewnerLE (B i) (blockScale (c * (3 : ℝ) ^ (γ * ((cap : ℝ) - r i))) E))
    (hs : Summable (fun i : {i // r i < cap} => w i * (3 : ℝ) ^ (γ * ((cap : ℝ) - r i))))
    (ht : (∑' i : {i // r i < cap}, w i * (3 : ℝ) ^ (γ * ((cap : ℝ) - r i))) ≤ T)
    (F : Finset ι) :
    BlockMatLoewnerLE (ofFullBlockMat (∑ i ∈ F, w i • toFullBlockMat (B i)))
      (ofFullBlockMat (toFullBlockMat A + (c * T) • toFullBlockMat E)) := by
  intro v
  rw [Annealed.bridge_quadratic_sum, quadratic_add, quadratic_smul]
  simp only [quadratic_smul, ofFullBlockMat_toFullBlockMat]
  exact finite_cap_sum w r
    (fun i => (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (B i) v))
    hw0 hw hmass cap hr γ _ _ c T (quadratic_nonneg hA v) (quadratic_nonneg hE v) hc
    (fun i hi => hcap i hi v)
    (fun i hi => by simpa only [Source.quadratic_blockScale] using hlow i hi v) hs ht F

end HCPolySupport.HighContrast.Multiscale.Adapter
end

section
open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter
  annealedBlock blockScale)
open HCPolySupport.HighContrast (adaptedCellTranslate)
namespace HCPolySupport.HighContrast.Multiscale.Adapter

open MeasureTheory Geometry
open scoped Matrix.Norms.L2Operator

/-- Annealed comparison from the actual capped maximal-cell partition.
The parent and every child are open affine cubes with integrable entries. -/
theorem partition_comparison {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (q q' : Mat d) (hq : IsUnit q) (hq' : IsUnit q')
    (K : ℝ) (hK : 0 ≤ K) (hInv : InverseNormLE (q⁻¹ * q') K)
    (n cap : ℤ) (y : Vec d) (γ : ℝ) (hγ : γ < 1)
    (A E : BlockMat d) (hA : Book.Ch02.BlockPosDef A) (hE : Book.Ch02.BlockPosDef E)
    (c : ℝ) (hc : 0 ≤ c)
    (hWint : HasIntegrableCoarseBlock P (adaptedCellTranslate q' n y))
    (hint : ∀ (r : ℤ) (w : Fin d → ℤ), HasIntegrableCoarseBlock P (adaptedCellAtCenter q r w))
    (hcap : ∀ w : Fin d → ℤ, BlockMatLoewnerLE (annealedBlock P (adaptedCellAtCenter q cap w)) A)
    (hlow : ∀ (r : ℤ), r < cap → ∀ w : Fin d → ℤ,
      BlockMatLoewnerLE (annealedBlock P (adaptedCellAtCenter q r w))
        (blockScale (c * (3 : ℝ) ^ (γ * ((cap : ℝ) - r))) E)) :
    BlockMatLoewnerLE (annealedBlock P (adaptedCellTranslate q' n y))
      (ofFullBlockMat (toFullBlockMat A +
        (c * ((6 * (d : ℝ) * K * Real.sqrt d) / (1 - (3 : ℝ) ^ (-(1 - γ)))) *
          (3 : ℝ) ^ (-((n : ℝ) - cap))) • toFullBlockMat E)) := by
  classical
  let W := adaptedCellTranslate q' n y
  let s := {p : ℤ × (Fin d → ℤ) | IsMaximalAdaptedCellIn W q cap p.1 p.2}
  let w (i : s) := (volume (adaptedCellAtCenter q i.1.1 i.1.2)).toReal / (volume W).toReal
  have hsub : ∀ i ∈ s, adaptedCellAtCenter q i.1 i.2 ⊆ W := fun _ hi => hi.1.2
  have hdis := pairwiseDisjoint_maximalAdaptedCellPairs W q hq cap
  have hnull := volume_diff_iUnion_maximalAdaptedCells_of_isOpen hq
    (isOpen_adaptedCellTranslate hq' n y) cap
  have hWfin : volume W ≠ ⊤ := Transport.volume_adaptedCellTranslate_ne_top q' n y
  have hw : Summable w := (maximal_mass q q' hq hq' n cap y).1
  have hw0 (i) : 0 ≤ w i := by dsimp [w]; positivity
  have hmass : (∑' i, w i) = 1 := (maximal_mass q q' hq hq' n cap y).2
  have hrow (r : ℤ) (hr : r < cap) :
      (∑' i : {i : s // i.1.1 = r}, w i) ≤
        (6 * (d : ℝ) * K * Real.sqrt d) * (3 : ℝ) ^ ((r : ℝ) - n) := by
    have hm := Annealed.bridge_maximal_row_mass W q hq cap r
      (finite_maximalAdaptedCellCenters_of_volume_ne_top hq hWfin cap r) (volume W).toReal
    exact hm.2.trans_le (lower_row_volume hq hq' hK hInv n cap r hr y)
  obtain ⟨hs, ht⟩ := fine_weight_bound w (fun i => i.1.1) hw0 hw cap n
    (6 * (d : ℝ) * K * Real.sqrt d) (by positivity) hrow γ hγ
  apply Annealed.bridge_annealed_partition_bound (Set.to_countable s) P q' hq' n y
    (fun _ => q) (fun _ _ => hq) (fun i => i.1) (fun i => adaptedCellCenter q i.1 i.2)
    _ hsub hdis hnull hWint (fun i _ => hint i.1 i.2)
  intro F
  have hb := finite_block_cap w (fun i => i.1.1)
    (fun i => annealedBlock P (adaptedCellAtCenter q i.1.1 i.1.2)) A E
    hw0 hw hmass.le cap (fun i => i.2.1.1) γ c _ hA hE hc
    (fun i hi => by simpa only [hi] using hcap i.1.2)
    (fun i hi => hlow i.1.1 hi i.1.2) hs ht F
  simpa only [mul_assoc] using! hb

end HCPolySupport.HighContrast.Multiscale.Adapter
end

section
open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter
  adaptedMean annealedBlock aspectRatio blockPosDef_annealedBlock blockScale)
open HCPolySupport.HighContrast (adaptedCell adaptedCellTranslate centeredCube)
namespace HCPolySupport.HighContrast.Multiscale.Adapter

open MeasureTheory Geometry
open scoped Matrix.Norms.L2Operator

/-- If `B ≤ A + c • E` and `E ≤ k • A`, then `B ≤ (1 + c * k) • A`: substituting the second
bound into the first and collecting the `A` terms. -/
theorem normalize_forward {d : ℕ} {A B E : BlockMat d} {c k : ℝ}
    (hc : 0 ≤ c)
    (hB : BlockMatLoewnerLE B (ofFullBlockMat (toFullBlockMat A + c • toFullBlockMat E)))
    (hE : BlockMatLoewnerLE E (blockScale k A)) :
    BlockMatLoewnerLE B (blockScale (1 + c * k) A) := by
  intro v
  have hb := hB v
  rw [quadratic_add, quadratic_smul] at hb
  simp only [ofFullBlockMat_toFullBlockMat] at hb
  have he := mul_le_mul_of_nonneg_left (hE v) hc
  rw [Source.quadratic_blockScale] at he ⊢
  linarith only [hb, he]

/-- E1, with the unused unit-range assumption omitted from this support export. -/
theorem forward_comparison (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc C : ℝ, 0 < Csrc ∧ 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (J : ℕ), 2 * d ≤ 3 ^ J →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (J : ℤ) →
          ∀ (m : Mat d), m.PosDef →
            ∀ t : ℤ, (J : ℤ) ≤ t →
              adaptedCell (explicitRoundedGrid J m) t ⊆ centeredCube d (2 * (J : ℤ)) →
              ∀ ℓ : ℕ, 1 ≤ ℓ →
                BlockMatLoewnerLE (adaptedMean P (1 : Mat d) (t + (ℓ : ℤ)))
                  (blockScale (1 + C * aspectRatio E * (‖m‖ * ‖m⁻¹‖) * (3 : ℝ) ^ (-(ℓ : ℝ)))
                    (adaptedMean P (explicitRoundedGrid J m) t)) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Cs, Ca, hCs, hCa, hsource⟩ := aligned_source_bound d hd γ hγ
  obtain ⟨Cn, Cb, hCn, hCb, hnorm⟩ := Annealed.adaptedMean_refBlock_normalization d hd γ hγ
  let D : ℝ := 1 - (3 : ℝ) ^ (-(1 - γ))
  have hD : 0 < D := sub_pos.mpr (Annealed.bridge_fine_ratio_mem_Ico hγ.2).2
  let C : ℝ := Ca * (12 * (d : ℝ) * Real.sqrt d / D) * Cb
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨max Cs Cn, C, lt_max_of_lt_left hCs, hC, ?_⟩
  intro P hP E Ψ K S hstat hdag J hJ hsrc m hm t hJt hwindow ℓ _hℓ
  have hlog : 0 ≤ Real.logb 3 (2 * K) :=
    Real.logb_nonneg (by norm_num) (by linarith only [hdag.one_lt_growthWitness])
  have hss := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left Cs Cn) hlog)).trans hsrc
  have hsn := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_right Cs Cn) hlog)).trans hsrc
  let q := explicitRoundedGrid J m
  have hq : IsUnit q := isUnit_roundedGrid hJ hm
  have hwinJ : adaptedCell q J ⊆ centeredCube d (2 * (J : ℤ)) :=
    (Set.image_mono (Window.centeredCube_mono hJt)).trans hwindow
  have hsrcAll := hsource P E Ψ K S hstat hdag J hJ hss m hm hwinJ
  have hint (r : ℤ) (w : Fin d → ℤ) : HasIntegrableCoarseBlock P (adaptedCellAtCenter q r w) :=
    Annealed.hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag J hJ m hm r
      (adaptedCellCenter q r w)
  have hintA : HasIntegrableCoarseBlock P (adaptedCell q t) := by
    simpa only [adaptedCellTranslate, zero_add, Set.image_id'] using
      Annealed.hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag J hJ m hm t 0
  have hA : Book.Ch02.BlockPosDef (adaptedMean P q t) :=
    blockPosDef_annealedBlock hintA (fun a => by
      simpa only [adaptedCellTranslate, zero_add, Set.image_id', HighContrast.adaptedCell,
        HighContrast.centeredCube] using
        Annealed.blockPosDef_coarseBlock_adapted q hq t 0 a)
  have hintW : HasIntegrableCoarseBlock P (adaptedCellTranslate (1 : Mat d) (t + ℓ) 0) := by
    simpa only [explicitRoundedGrid_one] using Annealed.hasIntegrableCoarseBlock_adapted d hd P
      γ E Ψ K S
      hstat hdag J hJ (1 : Mat d) (one_posDef d) (t + ℓ) 0
  have hInv : InverseNormLE (q⁻¹ * (1 : Mat d)) (2 * Real.sqrt (‖m‖ * ‖m⁻¹‖)) :=
    relative_inverse_bound hq isUnit_one (by
      simpa only [inv_one, Matrix.one_mul] using opNorm_roundedGrid_le hJ hm)
  have hcap (w : Fin d → ℤ) :
      BlockMatLoewnerLE (annealedBlock P (adaptedCellAtCenter q t w)) (adaptedMean P q t) := by
    rw [Annealed.annealedBlock_adaptedCellAtCenter P hstat J hJ m hm t hJt w]
    exact BlockMatLoewnerLE.refl _
  have hlow (r : ℤ) (hr : r < t) (w : Fin d → ℤ) :
      BlockMatLoewnerLE (annealedBlock P (adaptedCellAtCenter q r w))
        (blockScale (Ca * (3 : ℝ) ^ (γ * ((t : ℝ) - r))) E) := by
    apply (hsrcAll r w).trans
    apply Source.blockScale_le_blockScale_of_pos hdag.refBlock_posDef
    apply mul_le_mul_of_nonneg_left _ hCa.le
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply mul_le_mul_of_nonneg_left _ hγ.1
    apply max_le
    · exact sub_le_sub_right (by exact_mod_cast hJt) _
    · exact sub_nonneg.mpr (by exact_mod_cast hr.le)
  have hp := partition_comparison P q (1 : Mat d) hq isUnit_one
    (2 * Real.sqrt (‖m‖ * ‖m⁻¹‖)) (by positivity) hInv (t + ℓ) t 0 γ hγ.2
    (adaptedMean P q t) E hA hdag.refBlock_posDef Ca hCa.le hintW hint hcap hlow
  have hexp : -(((t + (ℓ : ℤ) : ℤ) : ℝ) - (t : ℝ)) = -(ℓ : ℝ) := by push_cast; ring
  simp only [hexp, adaptedCellTranslate, zero_add, Set.image_id'] at hp
  have hn := normalize_forward (by positivity : 0 ≤ Ca *
      ((6 * (d : ℝ) * (2 * Real.sqrt (‖m‖ * ‖m⁻¹‖)) * Real.sqrt d) / D) *
      (3 : ℝ) ^ (-(ℓ : ℝ))) hp
    (hnorm P E Ψ K S hstat hdag J hJ hsn m hm t hJt hwindow).2
  have heq : 1 + (Ca * ((6 * (d : ℝ) * (2 * Real.sqrt (‖m‖ * ‖m⁻¹‖)) * Real.sqrt d) / D) *
        (3 : ℝ) ^ (-(ℓ : ℝ))) * (Cb * aspectRatio E * Real.sqrt (‖m‖ * ‖m⁻¹‖)) =
      1 + C * aspectRatio E * (‖m‖ * ‖m⁻¹‖) * (3 : ℝ) ^ (-(ℓ : ℝ)) := by
    dsimp [C]
    calc
      _ = 1 + Ca * (12 * (d : ℝ) * Real.sqrt d / D) * Cb * aspectRatio E *
          (Real.sqrt (‖m‖ * ‖m⁻¹‖)) ^ 2 * (3 : ℝ) ^ (-(ℓ : ℝ)) := by ring
      _ = _ := by rw [Real.sq_sqrt (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [heq] at hn
  exact hn

end HCPolySupport.HighContrast.Multiscale.Adapter
end

section
open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter
  adaptedMean annealedBlock aspectRatio blockPosDef_annealedBlock blockScale blockSub)
open HCPolySupport.HighContrast (adaptedCell adaptedCellTranslate centeredCube)
namespace HCPolySupport.HighContrast.Multiscale.Adapter

open MeasureTheory Geometry
open scoped Matrix.Norms.L2Operator

/-- The reverse companion of `normalize_forward`: if `A` is positive definite, `B ≤ M + c • E`,
`E ≤ k • A`, and `c * k ≤ δ`, then `B - δ • A ≤ M`. -/
theorem normalize_reverse {d : ℕ} {A B M E : BlockMat d} {c k δ : ℝ}
    (hA : Book.Ch02.BlockPosDef A) (hc : 0 ≤ c) (hδ : c * k ≤ δ)
    (hB : BlockMatLoewnerLE B (ofFullBlockMat (toFullBlockMat M + c • toFullBlockMat E)))
    (hE : BlockMatLoewnerLE E (blockScale k A)) :
    BlockMatLoewnerLE (blockSub B (blockScale δ A)) M := by
  intro v
  have hb := hB v
  rw [quadratic_add, quadratic_smul] at hb
  simp only [ofFullBlockMat_toFullBlockMat] at hb
  have he := mul_le_mul_of_nonneg_left (hE v) hc
  rw [Source.quadratic_blockScale] at he
  have hδv := mul_le_mul_of_nonneg_right hδ (quadratic_nonneg hA v)
  have hsub := blockVecDot_blockMatVecMul_ofFullBlockMat_sub B (blockScale δ A) v
  change blockVecDot v (blockMatVecMul (blockSub B (blockScale δ A)) v) = _ at hsub
  rw [hsub, mul_sub, Source.quadratic_blockScale]
  linarith only [hb, he, hδv]

/-- E2 from the same capped partition, now with standard cells in the adapted
parent. The source normalization is still taken at the original generation t. -/
theorem reverse_comparison (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc C : ℝ, 0 < Csrc ∧ 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (J : ℕ), 2 * d ≤ 3 ^ J →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (J : ℤ) →
          ∀ (m : Mat d), m.PosDef →
            ∀ t : ℤ, (J : ℤ) ≤ t →
              adaptedCell (explicitRoundedGrid J m) t ⊆ centeredCube d (2 * (J : ℤ)) →
              ∀ ℓ r : ℕ, 1 ≤ ℓ → 1 ≤ r →
                BlockMatLoewnerLE
                  (blockSub (adaptedMean P (explicitRoundedGrid J m) (t + (ℓ : ℤ) + (r : ℤ)))
                    (blockScale (C * aspectRatio E * (‖m‖ * ‖m⁻¹‖) * (3 : ℝ) ^ (-(r : ℝ)))
                      (adaptedMean P (explicitRoundedGrid J m) t)))
                  (adaptedMean P (1 : Mat d) (t + (ℓ : ℤ))) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Cs, Ca, hCs, hCa, hsource⟩ := aligned_source_bound d hd γ hγ
  obtain ⟨Cn, Cb, hCn, hCb, hnorm⟩ := Annealed.adaptedMean_refBlock_normalization d hd γ hγ
  let D : ℝ := 1 - (3 : ℝ) ^ (-(1 - γ))
  have hD : 0 < D := sub_pos.mpr (Annealed.bridge_fine_ratio_mem_Ico hγ.2).2
  let C : ℝ := Ca * (12 * (d : ℝ) * Real.sqrt d / D) * Cb
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨max Cs Cn, C, lt_max_of_lt_left hCs, hC, ?_⟩
  intro P hP E Ψ K S hstat hdag J hJ hsrc m hm t hJt hwindow ℓ r _hℓ _hr
  have hlog : 0 ≤ Real.logb 3 (2 * K) :=
    Real.logb_nonneg (by norm_num) (by linarith only [hdag.one_lt_growthWitness])
  have hss := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left Cs Cn) hlog)).trans hsrc
  have hsn := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_right Cs Cn) hlog)).trans hsrc
  let q := explicitRoundedGrid J m
  have hq : IsUnit q := isUnit_roundedGrid hJ hm
  have hwin1 : adaptedCell (explicitRoundedGrid J (1 : Mat d)) J ⊆ centeredCube d (2 * (J : ℤ))
    := by
    rw [explicitRoundedGrid_one, identity_cell]
    exact Window.centeredCube_mono (by omega)
  have hsrcAll (j : ℤ) (w : Fin d → ℤ) :
      BlockMatLoewnerLE (annealedBlock P (adaptedCellAtCenter (1 : Mat d) j w))
        (blockScale (Ca * (3 : ℝ) ^ (γ * max ((J : ℝ) - (j : ℝ)) 0)) E) := by
    simpa only [explicitRoundedGrid_one] using
      hsource P E Ψ K S hstat hdag J hJ hss (1 : Mat d) (one_posDef d) hwin1 j w
  have hint (j : ℤ) (w : Fin d → ℤ) : HasIntegrableCoarseBlock P (adaptedCellAtCenter (1 : Mat
    d) j w) := by
    simpa only [explicitRoundedGrid_one] using!
      Annealed.hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag J hJ
        (1 : Mat d) (one_posDef d) j (adaptedCellCenter (1 : Mat d) j w)
  have hintM : HasIntegrableCoarseBlock P (adaptedCell (1 : Mat d) (t + ℓ)) := by
    simpa only [explicitRoundedGrid_one, adaptedCellTranslate, zero_add, Set.image_id'] using
      Annealed.hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag J hJ
        (1 : Mat d) (one_posDef d) (t + ℓ) 0
  have hM : Book.Ch02.BlockPosDef (adaptedMean P (1 : Mat d) (t + ℓ)) :=
    blockPosDef_annealedBlock hintM (fun a => by
      simpa only [adaptedCellTranslate, zero_add, Set.image_id', HighContrast.adaptedCell,
        HighContrast.centeredCube] using
        Annealed.blockPosDef_coarseBlock_adapted (1 : Mat d) isUnit_one (t + ℓ) 0 a)
  have hintA : HasIntegrableCoarseBlock P (adaptedCell q t) := by
    simpa only [adaptedCellTranslate, zero_add, Set.image_id'] using
      Annealed.hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag J hJ m hm t 0
  have hA : Book.Ch02.BlockPosDef (adaptedMean P q t) :=
    blockPosDef_annealedBlock hintA (fun a => by
      simpa only [adaptedCellTranslate, zero_add, Set.image_id', HighContrast.adaptedCell,
        HighContrast.centeredCube] using
        Annealed.blockPosDef_coarseBlock_adapted q hq t 0 a)
  have hintW : HasIntegrableCoarseBlock P (adaptedCellTranslate q (t + ℓ + r) 0) :=
    Annealed.hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag J hJ m hm (t + ℓ + r) 0
  have hInv : InverseNormLE ((1 : Mat d)⁻¹ * q) 2 :=
    relative_inverse_bound isUnit_one hq (by
      simpa only [Matrix.mul_one] using opNorm_roundedGrid_inv_le hJ hm)
  have hcap (w : Fin d → ℤ) :
      BlockMatLoewnerLE (annealedBlock P (adaptedCellAtCenter (1 : Mat d) (t + ℓ) w))
        (adaptedMean P (1 : Mat d) (t + ℓ)) := by
    have he := Annealed.annealedBlock_adaptedCellAtCenter P hstat J hJ (1 : Mat d) (one_posDef d)
      (t + ℓ) (by omega) w
    simp only [explicitRoundedGrid_one] at he
    rw [he]
    exact BlockMatLoewnerLE.refl _
  have hlow (j : ℤ) (hj : j < t + ℓ) (w : Fin d → ℤ) :
      BlockMatLoewnerLE (annealedBlock P (adaptedCellAtCenter (1 : Mat d) j w))
        (blockScale (Ca * (3 : ℝ) ^ (γ * (((t + (ℓ : ℤ) : ℤ) : ℝ) - j))) E) := by
    apply (hsrcAll j w).trans
    apply Source.blockScale_le_blockScale_of_pos hdag.refBlock_posDef
    apply mul_le_mul_of_nonneg_left _ hCa.le
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply mul_le_mul_of_nonneg_left _ hγ.1
    apply max_le
    · exact sub_le_sub_right (by exact_mod_cast (show (J : ℤ) ≤ t + ℓ by omega)) _
    · exact sub_nonneg.mpr (by exact_mod_cast hj.le)
  have hp := partition_comparison P (1 : Mat d) q isUnit_one hq 2 (by norm_num) hInv
    (t + ℓ + r) (t + ℓ) 0 γ hγ.2 (adaptedMean P (1 : Mat d) (t + ℓ)) E hM
    hdag.refBlock_posDef Ca hCa.le hintW hint hcap hlow
  have hexp : -(((t + (ℓ : ℤ) + (r : ℤ) : ℤ) : ℝ) - ((t + (ℓ : ℤ) : ℤ) : ℝ)) =
      -(r : ℝ) := by push_cast; ring
  simp only [hexp, adaptedCellTranslate, zero_add, Set.image_id'] at hp
  have hecc : Real.sqrt (‖m‖ * ‖m⁻¹‖) ≤ ‖m‖ * ‖m⁻¹‖ := by
    have he := Source.one_le_source_eccentricity hm
    have hsq := Real.sq_sqrt (mul_nonneg (norm_nonneg m) (norm_nonneg m⁻¹))
    calc
      Real.sqrt (‖m‖ * ‖m⁻¹‖) ≤ Real.sqrt (‖m‖ * ‖m⁻¹‖) ^ 2 := by
        rw [pow_two]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right he (Real.sqrt_nonneg _)
      _ = ‖m‖ * ‖m⁻¹‖ := hsq
  have hPi : 0 ≤ aspectRatio E :=
    (HCPolySupport.HighContrast.one_le_aspectRatio_of_coarseEllipticityDagger hdag).trans'
    zero_le_one
  have hδ : (Ca * ((6 * (d : ℝ) * 2 * Real.sqrt d) / D) * (3 : ℝ) ^ (-(r : ℝ))) *
      (Cb * aspectRatio E * Real.sqrt (‖m‖ * ‖m⁻¹‖)) ≤
      C * aspectRatio E * (‖m‖ * ‖m⁻¹‖) * (3 : ℝ) ^ (-(r : ℝ)) := by
    calc
      _ = C * aspectRatio E * Real.sqrt (‖m‖ * ‖m⁻¹‖) * (3 : ℝ) ^ (-(r : ℝ)) := by
        dsimp [C]
        ring
      _ ≤ _ := by gcongr
  exact normalize_reverse hA (by positivity) hδ hp
    (hnorm P E Ψ K S hstat hdag J hJ hsn m hm t hJt hwindow).2

end HCPolySupport.HighContrast.Multiscale.Adapter
end
