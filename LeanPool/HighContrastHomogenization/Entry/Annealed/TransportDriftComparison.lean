/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.TransportDriftAlgebra
public import LeanPool.HighContrastHomogenization.Entry.Annealed.BridgeComparisons
public import LeanPool.HighContrastHomogenization.Entry.Annealed.BridgeComparisonsOneSided
public import LeanPool.HighContrastHomogenization.Provider.Window.CellGeometry

/-!
# High-contrast homogenization: Entry.Annealed.TransportDriftComparison

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Transport drift comparison on two rounded grids

The deterministic drift estimates consumed by the two-grid transport.  The module proves the
scaling-composition law `blockScale a (blockScale b A) = blockScale (a * b) A` and a
cross-source comparison bounding the annealed mean of one rounded grid by a constant multiple
of the annealed mean of a second rounded grid.  It then removes the temporary source-scale cap
from the maximal-family partition comparison, assembles the complete Whitney drift comparison,
and deduces the printed determinant-drift estimate: on two positive definite geometries within
bounded projective distance, the drift of the transported geometry is bounded by the scaled
drift of the reference geometry plus the partition, source and terminal-decay terms.  These
estimates serve Proposition `p.two.grid.transport`.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter adaptedMean aspectRatio blockScale
  blockSub blockTrace blockVecDot_blockMatVecMul_eq_sum gridRatio normalizedBlock)
open HCPolySupport.HighContrast (adaptedCell adaptedCellTranslate centeredCube)
namespace HCPolySupport.HighContrast.Annealed
open MeasureTheory Geometry Multiscale Analysis
open scoped Matrix.Norms.L2Operator MatrixOrder Matrix
noncomputable section

/-- Twice a natural number cast to `ℝ` is nonnegative. -/
private lemma two_mul_natCast_nonneg (d : ℕ) : (0 : ℝ) ≤ 2 * (d : ℝ) :=
  mul_nonneg (by norm_num) (Nat.cast_nonneg d)

/-- A power of the base `3` with real exponent is nonnegative. -/
private lemma three_rpow_nonneg (x : ℝ) : (0 : ℝ) ≤ (3 : ℝ) ^ x :=
  Real.rpow_nonneg (by norm_num) x

/-- Scaling twice multiplies the real coefficients. -/
theorem transport_scale_scale {d : ℕ} (a b : ℝ) (A : BlockMat d) :
    blockScale a (blockScale b A) = blockScale (a * b) A := by
  have h : toFullBlockMat (blockScale a (blockScale b A)) = toFullBlockMat (blockScale (a * b)
    A) := by
    simp only [toFullBlockMat_blockScale, smul_smul]
  simpa only [ofFullBlockMat_toFullBlockMat] using congrArg ofFullBlockMat h

/-- Source normalization compares means on either rounded geometry, with a single outer constant. -/
theorem exists_transport_cross_source_mean (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc C : ℝ, 0 < Csrc ∧ 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ jStar : ℕ, 2 * d ≤ 3 ^ jStar → ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
        ∀ m mPlus : Mat d, m.PosDef → mPlus.PosDef →
        ∀ s j : ℤ, (jStar : ℤ) ≤ s → (jStar : ℤ) ≤ j →
          adaptedCell (explicitRoundedGrid jStar m) s ⊆ centeredCube d (2 * (jStar : ℤ)) →
          adaptedCell (explicitRoundedGrid jStar mPlus) j ⊆ centeredCube d (2 * (jStar : ℤ)) →
          BlockMatLoewnerLE (adaptedMean P (explicitRoundedGrid jStar mPlus) j)
            (blockScale (C * aspectRatio E * Real.sqrt (‖m‖ * ‖m⁻¹‖) *
              Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖)) (adaptedMean P (explicitRoundedGrid jStar m) s))
                := by
  obtain ⟨Cs, Cn, hCs, hCn, hnorm⟩ := adaptedMean_refBlock_normalization d hd γ hγ
  refine ⟨Cs, Cn ^ 2, hCs, pow_pos hCn _, ?_⟩
  intro P hP E Ψ K S hstat hdag jStar hj hsrc m mPlus hm hmPlus s j hs hjJ hsW hjW
  have hOld := (hnorm P E Ψ K S hstat hdag jStar hj hsrc m hm s hs hsW).2
  have hNew := (hnorm P E Ψ K S hstat hdag jStar hj hsrc mPlus hmPlus j hjJ hjW).1
  have h := hNew.trans (bridge_blockScale_mono (mul_nonneg hCn.le (Real.sqrt_nonneg _)) hOld)
  rw [transport_scale_scale] at h
  convert h using 1
  congr 1
  ring

/-- Removing the cap from a maximal-family row cannot increase its mass. -/
theorem transport_drift_subrow {d : ℕ} [NeZero d] (W : Set (Vec d)) (q : Mat d) (hq : IsUnit q)
    (cap r : ℤ)
    (hfin : (maximalAdaptedCellCenters W q cap r).Finite) :
    let I := {p : ℤ × (Fin d → ℤ) // IsMaximalAdaptedCellIn W q cap p.1 p.2}
    (∑' p : {p : {p : I // p.1.1 < cap} // p.1.1.1 = r},
      (volume (adaptedCellAtCenter q p.1.1.1.1 p.1.1.1.2)).toReal / (volume W).toReal) ≤
      ∑ _z ∈ hfin.toFinset, (volume (adaptedCell q r)).toReal / (volume W).toReal := by
  classical
  intro I
  let R := {p : I // p.1.1 = r}
  let S := {p : {p : I // p.1.1 < cap} // p.1.1.1 = r}
  let e : S → R := fun p => ⟨p.1.1, p.2⟩
  have he : Function.Injective e := by
    intro p v h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : R => x.1) h
  have hm := bridge_maximal_row_mass W q hq cap r hfin (volume W).toReal
  let w : R → ℝ := fun p => (volume (adaptedCellAtCenter q p.1.1.1 p.1.1.2)).toReal / (volume
    W).toReal
  have hw0 (p : R) : 0 ≤ w p := div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hsum : Summable w := hm.1
  have hle : (∑' p : S, w (e p)) ≤ ∑' p : R, w p :=
    Summable.tsum_le_tsum_of_inj e he (fun p _ => hw0 p) (fun _ => le_rfl)
      (hsum.comp_injective he) hsum
  exact hle.trans_eq hm.2


/-- Apply the accepted partition comparison to the actual forward Whitney family.
The temporary maximum in the summation cap isolates the source-scale endpoint. -/
theorem exists_transport_drift_partition_raw (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (K₀ : ℝ) (hK₀ : 1 ≤ K₀) :
    ∃ Csrc Cw Ct : ℝ, 0 < Csrc ∧ 0 < Cw ∧ 0 < Ct ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ jStar : ℕ, 2 * d ≤ 3 ^ jStar → ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
        ∀ m mPlus : Mat d, m.PosDef → mPlus.PosDef →
          gridRatio (explicitRoundedGrid jStar m) (explicitRoundedGrid jStar mPlus) ≤ K₀ →
        ∀ j terminal : ℤ, (jStar : ℤ) ≤ terminal → ∀ L : ℕ, 1 ≤ L →
          (jStar : ℤ) ≤ j - (L : ℤ) →
          adaptedCell (explicitRoundedGrid jStar mPlus) j ⊆ centeredCube d (2 * (jStar : ℤ)) →
          adaptedCell (explicitRoundedGrid jStar m) terminal ⊆ centeredCube d (2 * (jStar : ℤ)) →
          BlockMatLoewnerLE
            (blockSub (adaptedMean P (explicitRoundedGrid jStar mPlus) j)
              (adaptedMean P (explicitRoundedGrid jStar m) (j - (L : ℤ))))
            (ofFullBlockMat
              (Cw • (∑ r ∈ Finset.Icc (jStar : ℤ) (max (jStar : ℤ) (j - (L : ℤ) - 1)),
                (3 : ℝ) ^ ((r : ℝ) - j) • toFullBlockMat (adaptedMean P (explicitRoundedGrid
                  jStar m) r)) +
               (Ct * Cw * aspectRatio E * (Real.sqrt (‖m‖ * ‖m⁻¹‖)) ^ 2 *
                 (3 : ℝ) ^ (-((j : ℝ) - jStar))) • toFullBlockMat (adaptedMean P
                   (explicitRoundedGrid jStar m) terminal))) := by
  classical
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Cs, Ct, hCs, hCt, hcomp⟩ := bridge_partition_comparison d hd γ hγ
  obtain ⟨Cg, _hCg, hwhitney⟩ := Entry.two_grid_whitney d hd
  obtain ⟨Cw, hCw, hwhitney⟩ := hwhitney K₀ hK₀
  refine ⟨max Cs (Cg γ), Cw, Ct, hCs.trans_le (le_max_left _ _), hCw, hCt, ?_⟩
  intro P hP E Ψ K S hstat hdag jStar hj hsrc m mPlus hm hmPlus hratio j terminal htJ L hL hbJ hW hT
  let q := explicitRoundedGrid jStar m
  let qPlus := explicitRoundedGrid jStar mPlus
  let b := j - (L : ℤ)
  let W := adaptedCell qPlus j
  let I := {p : ℤ × (Fin d → ℤ) | IsMaximalAdaptedCellIn W q b p.1 p.2}
  have hq : IsUnit q := isUnit_roundedGrid hj hm
  have hlog : 0 ≤ Real.logb 3 (2 * K) := (Real.logb_pos (by norm_num)
    (by linarith only [hdag.one_lt_growthWitness] : (1 : ℝ) < 2 * K)).le
  have hsC := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left Cs (Cg γ)) hlog)).trans hsrc
  have hsG := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_right Cs (Cg γ)) hlog)).trans hsrc
  have hzero : (0 : Vec d) ∈ adaptedLatticeAtScale qPlus j := by
    refine ⟨0, ?_⟩
    simp only [adaptedCellCenter, Pi.zero_apply, Int.cast_zero]
    change (3 : ℝ) ^ j • matVecMul qPlus 0 = 0
    simp only [matVecMul_zero, smul_zero]
  obtain ⟨hfin, hsub, hdis, hnull, _hvol, _hcard, _hcount, hmass, hrow⟩ :=
    (hwhitney γ hγ K hdag.one_lt_growthWitness jStar hj hsG m mPlus hm hmPlus hratio j L hL).1 0
      hzero
  have _hcapmass := bridge_whitney_cap_mass_le_one (adaptedCellTranslate qPlus j 0) q hq b
    (Transport.volume_adaptedCellTranslate_ne_top _ _ _) hfin hmass
  simp only [adaptedCellTranslate, zero_add, Set.image_id'] at hfin hsub hdis hnull hrow
  have hraw := hcomp P E Ψ K S hstat hdag jStar hj hsC m m mPlus hm hm hmPlus
    (max (jStar : ℤ) (b - 1)) b j terminal (le_max_left _ _) hbJ htJ hW hT
    (ℤ × (Fin d → ℤ)) I (fun _ => q) (fun _ _ => hq) Prod.fst
    (fun p => adaptedCellCenter q p.1 p.2) (fun p => p.1 < b) Prod.fst Prod.snd
    (fun p hp => hsub p.1 p.2 hp) hdis hnull (fun _ _ _ => rfl)
    (fun p hp hpb => by
      have he : p.1 = b := by have := hp.1.1; omega
      change adaptedCellAtCenter q p.1 p.2 = adaptedCellAtCenter q b p.2
      rw [he])
    (fun p _ hpb => by omega) Cw hCw.le
  have hrows : ∀ r : ℤ, r ≤ max (jStar : ℤ) (b - 1) →
      (∑' p : {p : {p : I // p.1.1 < b} // p.1.1.1 = r},
        (volume (adaptedCellAtCenter q p.1.1.1.1 p.1.1.1.2)).toReal / (volume W).toReal) ≤
          Cw * (3 : ℝ) ^ ((r : ℝ) - j) := by
    intro r _hr
    by_cases hrb : r < b
    · exact (transport_drift_subrow W q hq b r (hfin r hrb.le)).trans (hrow r hrb)
    · let : IsEmpty {p : {p : I // p.1.1 < b} // p.1.1.1 = r} := ⟨fun p => by
        have hp := p.1.2; have he := p.2; omega⟩
      rw [tsum_empty]
      exact mul_nonneg hCw.le (Real.rpow_nonneg (by norm_num) _)
  simpa only [toFullBlockMat_blockScale, toFullBlockMat_ofFullBlockMat] using hraw hrows

/-- The temporary cap adds only the source-scale term, even at the first target generation. -/
theorem transport_drift_cap_sum (J b j : ℤ) (hJb : J ≤ b) (f : ℤ → ℝ) (hfJ : 0 ≤ f J) :
    (∑ r ∈ Finset.Icc J (max J (b - 1)), (3 : ℝ) ^ ((r : ℝ) - j) * f r) ≤
      (∑ r ∈ Finset.Icc J (b - 1), (3 : ℝ) ^ ((r : ℝ) - j) * f r) +
        (3 : ℝ) ^ (-((j : ℝ) - J)) * f J := by
  by_cases hb : b = J
  · subst b
    simp only [max_eq_left (by omega : J - 1 ≤ J), Finset.Icc_self, Finset.sum_singleton,
      Finset.Icc_eq_empty_of_lt (by omega : J - 1 < J), Finset.sum_empty, zero_add, neg_sub,
        le_refl]
  · rw [max_eq_right (by omega : J ≤ b - 1)]
    exact le_add_of_nonneg_right (mul_nonneg (three_rpow_nonneg _) hfJ)

private theorem transport_quadratic_add {d : ℕ} (M N : FullBlockMat d) (v : BlockVec d) :
    (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat (M + N)) v) =
      (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat M) v) +
        (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat N) v) := by
  simp only [blockVecDot_blockMatVecMul_eq_sum, blockMatEntry_ofFullBlockMat,
    Matrix.add_apply, add_mul, mul_add, Finset.sum_add_distrib]

private theorem transport_quadratic_smul {d : ℕ} (c : ℝ) (M : FullBlockMat d) (v : BlockVec d) :
    (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat (c • M)) v) =
      c * ((1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat M) v)) := by
  simpa only [toFullBlockMat_ofFullBlockMat] using! Source.quadratic_blockScale c
    (ofFullBlockMat M) v

private theorem transport_quadratic_nonneg {d : ℕ} (A : BlockMat d)
    (hA : (toFullBlockMat A).PosSemidef) (v : BlockVec d) :
    0 ≤ (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul A v) := by
  apply mul_nonneg (by norm_num)
  simpa only [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul, star_trivial] using
    hA.dotProduct_mulVec_nonneg (toFullBlockVec v)

/-- Remove the temporary source-scale cap and weaken only the scalar source decay. -/
theorem transport_drift_partition_enlarge {d : ℕ} (A : ℤ → BlockMat d) (H F : BlockMat d)
    (hAJ : ∀ r, (toFullBlockMat (A r)).PosSemidef) (hF : (toFullBlockMat F).PosSemidef)
    (J b j : ℤ) (hJb : J ≤ b) (hJj : J ≤ j)
    (Cw Cf M C D B γ : ℝ) (hCw : 0 ≤ Cw) (hCf : 0 ≤ Cf) (hM : 0 ≤ M)
    (hγ : 0 ≤ γ) (hcoeff : Cw * M + Cf ≤ D * B) (hCW : Cw ≤ C)
    (hsource : BlockMatLoewnerLE (A J) (blockScale M F))
    (hraw : BlockMatLoewnerLE (blockSub H (A b))
      (ofFullBlockMat (Cw • (∑ r ∈ Finset.Icc J (max J (b - 1)),
        (3 : ℝ) ^ ((r : ℝ) - j) • toFullBlockMat (A r)) +
        (Cf * (3 : ℝ) ^ (-((j : ℝ) - J))) • toFullBlockMat F))) :
    BlockMatLoewnerLE H
      (ofFullBlockMat (toFullBlockMat (A b) +
        C • (∑ r ∈ Finset.Icc J (b - 1), (3 : ℝ) ^ ((r : ℝ) - j) • toFullBlockMat (A r)) +
        (D * B * (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - J))) • toFullBlockMat F)) := by
  intro v
  let f := fun r => (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (A r) v)
  let z := (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul F v)
  have hz : 0 ≤ z := transport_quadratic_nonneg F hF v
  have hf (r : ℤ) : 0 ≤ f r := transport_quadratic_nonneg (A r) (hAJ r) v
  have hs : f J ≤ M * z := by simpa only [Source.quadratic_blockScale] using hsource v
  have hcap := transport_drift_cap_sum J b j hJb f (hf J)
  have hlow : (3 : ℝ) ^ (-((j : ℝ) - J)) ≤ (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - J)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hgap : 0 ≤ (j : ℝ) - J := by exact_mod_cast sub_nonneg.mpr hJj
    nlinarith only [mul_nonneg hγ hgap]
  have hcf0 : 0 ≤ Cw * M + Cf := add_nonneg (mul_nonneg hCw hM) hCf
  have hcf : (Cw * M + Cf) * (3 : ℝ) ^ (-((j : ℝ) - J)) ≤
      D * B * (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - J)) :=
    (mul_le_mul_of_nonneg_left hlow hcf0).trans (mul_le_mul_of_nonneg_right hcoeff
      (three_rpow_nonneg _))
  have hsum0 : 0 ≤ ∑ r ∈ Finset.Icc J (b - 1), (3 : ℝ) ^ ((r : ℝ) - j) * f r :=
    Finset.sum_nonneg (fun r _ => mul_nonneg (three_rpow_nonneg _) (hf r))
  have hr := hraw v
  have hsub : (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (blockSub H (A b)) v) =
      (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul H v) - f b := by
    rw [show blockSub H (A b) = ofFullBlockMat (toFullBlockMat H - toFullBlockMat (A b)) from rfl,
      blockVecDot_blockMatVecMul_ofFullBlockMat_sub]
    dsimp only [f]; ring
  rw [hsub, transport_quadratic_add, transport_quadratic_smul,
    transport_quadratic_smul, bridge_quadratic_sum] at hr
  simp only [transport_quadratic_smul, ofFullBlockMat_toFullBlockMat] at hr
  rw [transport_quadratic_add, transport_quadratic_add, ofFullBlockMat_toFullBlockMat,
    transport_quadratic_smul, transport_quadratic_smul, bridge_quadratic_sum]
  simp only [transport_quadratic_smul, ofFullBlockMat_toFullBlockMat]
  change _ ≤ f b + C * (∑ r ∈ Finset.Icc J (b - 1), (3 : ℝ) ^ ((r : ℝ) - j) * f r) +
    (D * B * (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - J))) * z
  change (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul H v) - f b ≤
    Cw * (∑ r ∈ Finset.Icc J (max J (b - 1)), (3 : ℝ) ^ ((r : ℝ) - j) * f r) +
      Cf * (3 : ℝ) ^ (-((j : ℝ) - J)) * z at hr
  have hc := mul_le_mul_of_nonneg_left hcap hCw
  have hs' := mul_le_mul_of_nonneg_left hs (mul_nonneg hCw (three_rpow_nonneg (-((j : ℝ) - J))))
  have hcf' := mul_le_mul_of_nonneg_right hcf hz
  have hcw' := mul_le_mul_of_nonneg_right hCW hsum0
  nlinarith only [hr, hc, hs', hcf', hcw']

/-- The complete Whitney drift comparison, including the empty boundary at j=jStar+L. -/
theorem exists_transport_whitney_drift_comparison (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (K₀ : ℝ) (hK₀ : 1 ≤ K₀) :
    ∃ Csrc C : ℝ, 0 < Csrc ∧ 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ jStar : ℕ, 2 * d ≤ 3 ^ jStar → ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
        ∀ m mPlus : Mat d, m.PosDef → mPlus.PosDef →
          gridRatio (explicitRoundedGrid jStar m) (explicitRoundedGrid jStar mPlus) ≤ K₀ →
        ∀ j terminal : ℤ, (jStar : ℤ) ≤ terminal → ∀ L : ℕ, 1 ≤ L →
          (jStar : ℤ) ≤ j - (L : ℤ) →
          adaptedCell (explicitRoundedGrid jStar mPlus) j ⊆ centeredCube d (2 * (jStar : ℤ)) →
          adaptedCell (explicitRoundedGrid jStar m) terminal ⊆ centeredCube d (2 * (jStar : ℤ)) →
          BlockMatLoewnerLE (adaptedMean P (explicitRoundedGrid jStar mPlus) j)
            (ofFullBlockMat
              (toFullBlockMat (adaptedMean P (explicitRoundedGrid jStar m) (j - (L : ℤ))) +
               (C * K₀) • (∑ r ∈ Finset.Icc (jStar : ℤ) (j - (L : ℤ) - 1),
                 (3 : ℝ) ^ ((r : ℝ) - j) • toFullBlockMat (adaptedMean P (explicitRoundedGrid
                   jStar m) r)) +
               (C * (1 + aspectRatio E * (Real.sqrt (‖m‖ * ‖m⁻¹‖) + Real.sqrt (‖mPlus‖ *
                 ‖mPlus⁻¹‖)) ^ 2) *
                 (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - jStar))) • toFullBlockMat (adaptedMean P
                   (explicitRoundedGrid jStar m) terminal))) := by
  classical
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Cs, Cw, Ct, hCs, hCw, hCt, hraw⟩ := exists_transport_drift_partition_raw d hd γ hγ K₀ hK₀
  obtain ⟨CnSrc, Cn, hCnSrc, hCn, hnorm⟩ := exists_transport_cross_source_mean d hd γ hγ
  let C := Cn + Cw * (Cn + Ct + 1) + 1
  have hC : 0 < C := by
    dsimp only [C]
    have hprod : 0 < Cw * (Cn + Ct + 1) := mul_pos hCw (by linarith only [hCn, hCt])
    linarith only [hCn, hprod]
  have hCwC : Cw ≤ C := by dsimp only [C]; nlinarith only [hCn, mul_pos hCw (add_pos hCn hCt)]
  have hCtC : Cw * (Cn + Ct) ≤ C := by dsimp only [C]; linarith only [hCn, hCw]
  refine ⟨max Cs CnSrc, C, hCs.trans_le (le_max_left _ _), hC, ?_⟩
  intro P hP E Ψ K S hstat hdag jStar hj hsrc m mPlus hm hmPlus hratio j terminal htJ L hL hbJ hW hT
  have hlog : 0 ≤ Real.logb 3 (2 * K) := (Real.logb_pos (by norm_num)
    (by linarith only [hdag.one_lt_growthWitness] : (1 : ℝ) < 2 * K)).le
  have hsR := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left Cs CnSrc) hlog)).trans hsrc
  have hsN := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_right Cs CnSrc) hlog)).trans hsrc
  let A := fun r => adaptedMean P (explicitRoundedGrid jStar m) r
  let F := A terminal
  let e := Real.sqrt (‖m‖ * ‖m⁻¹‖)
  let ePlus := Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖)
  let B := 1 + aspectRatio E * (e + ePlus) ^ 2
  have hPi : 0 ≤ aspectRatio E := (one_le_aspectRatio_of_coarseEllipticityDagger hdag).trans'
    (by norm_num)
  have he : 0 ≤ e := Real.sqrt_nonneg _
  have hePlus : 0 ≤ ePlus := Real.sqrt_nonneg _
  have hJB : adaptedCell (explicitRoundedGrid jStar m) (jStar : ℤ) ⊆ centeredCube d (2 * (jStar
    : ℤ)) :=
    (Set.image_mono (Window.centeredCube_mono htJ)).trans hT
  have hs := hnorm P E Ψ K S hstat hdag jStar hj hsN m m hm hm terminal (jStar : ℤ) htJ le_rfl
    hT hJB
  have hs' : BlockMatLoewnerLE (A jStar) (blockScale (Cn * aspectRatio E * e ^ 2) F) := by
    convert hs using 1
    congr 1
    dsimp only [e]; ring
  have hB : aspectRatio E * e ^ 2 ≤ B := by
    dsimp only [B]
    have hsq : e ^ 2 ≤ (e + ePlus) ^ 2 := by nlinarith only [he, hePlus, sq_nonneg ePlus]
    linarith only [mul_le_mul_of_nonneg_left hsq hPi]
  have hcoeff : Cw * (Cn * aspectRatio E * e ^ 2) + Ct * Cw * aspectRatio E * e ^ 2 ≤ C * B := by
    calc
      _ = (Cw * (Cn + Ct)) * (aspectRatio E * e ^ 2) := by ring
      _ ≤ C * (aspectRatio E * e ^ 2) := mul_le_mul_of_nonneg_right hCtC (mul_nonneg hPi
        (sq_nonneg e))
      _ ≤ C * B := mul_le_mul_of_nonneg_left hB hC.le
  exact transport_drift_partition_enlarge A (adaptedMean P (explicitRoundedGrid jStar mPlus) j) F
    (fun r => (adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm r).posSemidef)
    (adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm terminal).posSemidef
    jStar (j - (L : ℤ)) j hbJ (by omega)
    Cw (Ct * Cw * aspectRatio E * e ^ 2) (Cn * aspectRatio E * e ^ 2) (C * K₀) C B γ
    hCw.le (mul_nonneg (mul_nonneg (mul_nonneg hCt.le hCw.le) hPi) (sq_nonneg e))
      (mul_nonneg (mul_nonneg hCn.le hPi) (sq_nonneg e)) hγ.1 hcoeff
    (hCwC.trans (le_mul_of_one_le_right hC.le hK₀)) hs'
    (hraw P E Ψ K S hstat hdag jStar hj hsR m mPlus hm hmPlus hratio j terminal htJ L hL hbJ hW hT)

/-- Collect the geometric-series factors and absorb each scalar error coefficient. -/
private theorem transport_drift_absorption_constants (d : ℕ) (γ K₀ Cw Cn : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (hK₀ : 1 ≤ K₀) (hCw : 0 < Cw) (hCn : 0 < Cn) :
    let a := (1 - γ) / 8
    let Ga := 1 / (1 - (3 : ℝ) ^ (-a))
    let Gb := 1 / (1 - (3 : ℝ) ^ (-(1 - a)))
    let G₁ := 1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))
    let Cd := (8 / 3 : ℝ) * d
    let Ci := (8 / 3 : ℝ) * d * Cw * G₁
    let Cs := (8 / 3 : ℝ) * d * (Cw + Cn)
    let Co := (4 / 3 : ℝ) * (1 + (Cw * K₀) * Gb) * Ga
    let C := 1 + Cd + Ci + Cs + Co
    0 < a ∧ a < 1 ∧ a ≤ 1 - γ ∧ 0 ≤ Ga ∧ 0 ≤ Gb ∧ 0 ≤ G₁ ∧
      0 ≤ Cd ∧ 0 ≤ Ci ∧ 0 ≤ Cs ∧ 0 ≤ Co ∧ 0 < C ∧
      Cd ≤ C ∧ Ci ≤ C ∧ Cs ≤ C ∧ Co ≤ C := by
  let a := (1 - γ) / 8
  let Ga := 1 / (1 - (3 : ℝ) ^ (-a))
  let Gb := 1 / (1 - (3 : ℝ) ^ (-(1 - a)))
  let G₁ := 1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))
  let Cd := (8 / 3 : ℝ) * d
  let Ci := (8 / 3 : ℝ) * d * Cw * G₁
  let Cs := (8 / 3 : ℝ) * d * (Cw + Cn)
  let Co := (4 / 3 : ℝ) * (1 + (Cw * K₀) * Gb) * Ga
  let C := 1 + Cd + Ci + Cs + Co
  have ha : 0 < a := by dsimp only [a]; linarith only [hγ.2]
  have ha1 : a < 1 := by dsimp only [a]; linarith only [hγ.1]
  have hGa : 0 ≤ Ga := (one_div_pos.mpr (transport_geometric_Icc a ha 0 0).1).le
  have hGb : 0 ≤ Gb := (one_div_pos.mpr (transport_geometric_Icc (1 - a) (by linarith only
    [ha1]) 0 0).1).le
  have hG₁ : 0 ≤ G₁ := (one_div_pos.mpr (transport_geometric_Icc 1 (by norm_num) 0 0).1).le
  have hCd : 0 ≤ Cd := by dsimp only [Cd]; exact mul_nonneg (by norm_num) (Nat.cast_nonneg d)
  have hCi : 0 ≤ Ci := by
    dsimp only [Ci]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hCw.le) hG₁
  have hCs : 0 ≤ Cs := by
    dsimp only [Cs]
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) (add_nonneg hCw.le hCn.le)
  have hCo : 0 ≤ Co := by
    dsimp only [Co]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (add_nonneg zero_le_one (mul_nonneg (mul_nonneg hCw.le (zero_le_one.trans hK₀)) hGb))) hGa
  have hC : 0 < C := by dsimp only [C]; linarith only [hCd, hCi, hCs, hCo]
  have hCdC : Cd ≤ C := by dsimp only [C]; linarith only [hCi, hCs, hCo]
  have hCiC : Ci ≤ C := by dsimp only [C]; linarith only [hCd, hCs, hCo]
  have hCsC : Cs ≤ C := by dsimp only [C]; linarith only [hCd, hCi, hCo]
  have hCoC : Co ≤ C := by dsimp only [C]; linarith only [hCd, hCi, hCs]
  have hab : a ≤ 1 - γ := by dsimp only [a]; linarith only [hγ.2]
  exact ⟨ha, ha1, hab, hGa, hGb, hG₁, hCd, hCi, hCs, hCo, hC, hCdC, hCiC, hCsC, hCoC⟩

private theorem transport_drift_error_absorption (A C Co Cd Ci δ I D T U : ℝ)
    (hA : A ≤ Co * D + T + (Cd * δ + Ci * I))
    (hCoC : Co ≤ C) (hCdC : Cd ≤ C) (hCiC : Ci ≤ C)
    (hD : 0 ≤ D) (hδ : 0 ≤ δ) (hI : 0 ≤ I) (hTU : T ≤ U) :
    A ≤ C * (δ + I + D) + U := by
  calc
    _ ≤ Co * D + T + (Cd * δ + Ci * I) := hA
    _ ≤ C * D + U + (C * δ + C * I) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_right hCoC hD) hTU)
        (add_le_add (mul_le_mul_of_nonneg_right hCdC hδ)
          (mul_le_mul_of_nonneg_right hCiC hI))
    _ = _ := by ring

private theorem transport_cross_eccentricity_bound (Pi e ePlus : ℝ)
    (hPi : 0 ≤ Pi) (he : 0 ≤ e) (hp : 0 ≤ ePlus) :
    0 ≤ 1 + Pi * (e + ePlus) ^ 2 ∧ Pi * e * ePlus ≤ 1 + Pi * (e + ePlus) ^ 2 := by
  have hsq : e * ePlus ≤ (e + ePlus) ^ 2 := by
    nlinarith only [he, hp, sq_nonneg e, sq_nonneg ePlus]
  exact ⟨by positivity, by nlinarith only [mul_le_mul_of_nonneg_left hsq hPi]⟩

private theorem transport_source_growth_bound (Cs C B R : ℝ) (J : ℕ) (n : ℤ) (L : ℕ)
    (hn : (J : ℤ) ≤ n) (hCs : 0 ≤ Cs) (hCsC : Cs ≤ C) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    (Cs * B) * ((n : ℝ) + L - J) * R ≤ C * B * (1 + (n : ℝ) + L - J) * R := by
  have hnr : (J : ℝ) ≤ n := by exact_mod_cast hn
  have hu : 0 ≤ 1 + (n : ℝ) + L - J := by
    linarith only [hnr, (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  calc
    _ ≤ Cs * B * (1 + (n : ℝ) + L - J) * R := by gcongr; linarith only [hu]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCsC hB) hu) hR

/-- The complete printed determinant-drift estimate. The uniform errors use the
mass-one Abel identity; the source term retains its linear scale factor. -/
theorem exists_two_grid_drift_comparison (d : ℕ) (hd : 2 ≤ d)
    (K₀ : ℝ) (hK₀ : 1 ≤ K₀) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc C : ℝ, 0 < Csrc ∧ 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ jStar : ℕ, 2 * d ≤ 3 ^ jStar → ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
        ∀ m mPlus : Mat d, m.PosDef → mPlus.PosDef →
          gridRatio (explicitRoundedGrid jStar m) (explicitRoundedGrid jStar mPlus) ≤ K₀ →
        ∀ n : ℤ, (jStar : ℤ) ≤ n → ∀ L : ℕ, 1 ≤ L →
          adaptedCell (explicitRoundedGrid jStar m) (n + 2 * (L : ℤ)) ∪
            adaptedCell (explicitRoundedGrid jStar mPlus) (n + (L : ℤ)) ⊆ centeredCube d (2 *
              (jStar : ℤ)) →
        ∀ δ : ℝ, δ ∈ Set.Icc (0 : ℝ) (1 / 4) →
          BlockMatLoewnerLE (blockScale (1 - δ) (adaptedMean P (explicitRoundedGrid jStar m) (n
            + 2 * (L : ℤ))))
            (adaptedMean P (explicitRoundedGrid jStar mPlus) (n + (L : ℤ))) →
          BlockMatLoewnerLE (adaptedMean P (explicitRoundedGrid jStar mPlus) (n + (L : ℤ)))
            (blockScale (1 + δ) (adaptedMean P (explicitRoundedGrid jStar m) (n + 2 * (L : ℤ)))) →
          determinantDrift P γ (explicitRoundedGrid jStar mPlus) jStar (n + (L : ℤ)) ≤
            C * (δ + K₀ * (3 : ℝ) ^ (-(L : ℝ)) + (3 : ℝ) ^ ((1 - γ) / 4 * (L : ℝ)) *
              determinantDrift P γ (explicitRoundedGrid jStar m) jStar (n + 2 * (L : ℤ))) +
            C * (1 + aspectRatio E * (Real.sqrt (‖m‖ * ‖m⁻¹‖) + Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖))
              ^ 2) *
              (1 + (n : ℝ) + L - jStar) * (3 : ℝ) ^ (-((1 - γ) / 8) * ((n : ℝ) - jStar)) := by
  classical
  let : NeZero d := ⟨by omega⟩
  obtain ⟨CwSrc, Cw, hCwSrc, hCw, hwhitney⟩ := exists_transport_whitney_drift_comparison d hd γ
    hγ K₀ hK₀
  obtain ⟨CnSrc, Cn, hCnSrc, hCn, hsource⟩ := exists_transport_cross_source_mean d hd γ hγ
  let a := (1 - γ) / 8
  let Ga := 1 / (1 - (3 : ℝ) ^ (-a))
  let Gb := 1 / (1 - (3 : ℝ) ^ (-(1 - a)))
  let G₁ := 1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))
  let Cd := (8 / 3 : ℝ) * d
  let Ci := (8 / 3 : ℝ) * d * Cw * G₁
  let Cs := (8 / 3 : ℝ) * d * (Cw + Cn)
  let Co := (4 / 3 : ℝ) * (1 + (Cw * K₀) * Gb) * Ga
  let C := 1 + Cd + Ci + Cs + Co
  obtain ⟨ha, ha1, hab, hGa, hGb, hG₁, hCd, hCi, hCs, hCo, hC, hCdC, hCiC, hCsC, hCoC⟩ :=
    transport_drift_absorption_constants d γ K₀ Cw Cn hγ hK₀ hCw hCn
  refine ⟨max CwSrc CnSrc, C, hCwSrc.trans_le (le_max_left _ _), hC, ?_⟩
  intro P hP E Ψ K S hstat hdag jStar hj hsrc m mPlus hm hmPlus hratio n hn L hL hwindow δ hδ
    hlow hup
  have hlog : 0 ≤ Real.logb 3 (2 * K) := (Real.logb_pos (by norm_num)
    (by linarith only [hdag.one_lt_growthWitness] : (1 : ℝ) < 2 * K)).le
  have hsW := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left CwSrc CnSrc) hlog)).trans hsrc
  have hsN := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_right CwSrc CnSrc) hlog)).trans
    hsrc
  let q := explicitRoundedGrid jStar m
  let qPlus := explicitRoundedGrid jStar mPlus
  let t := n + (L : ℤ)
  let s := n + 2 * (L : ℤ)
  let F := adaptedMean P q s
  let H := adaptedMean P qPlus t
  let f := fun r => blockTrace (blockSub (relMean P q r s) (Book.Ch02.blockIdentity d))
  let g := fun j => blockTrace (blockSub (relMean P qPlus j t) (Book.Ch02.blockIdentity d))
  let B := 1 + aspectRatio E * (Real.sqrt (‖m‖ * ‖m⁻¹‖) + Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖)) ^ 2
  let R := (3 : ℝ) ^ (-a * ((n : ℝ) - jStar))
  let grow := (3 : ℝ) ^ (2 * a * (L : ℝ))
  let Dold := determinantDrift P γ q jStar s
  let Iold := (2 * (d : ℝ)) * (Cw * K₀) * G₁ * (3 : ℝ) ^ (-(L : ℝ))
  let Yold := (2 * (d : ℝ)) * (Cw + Cn) * B
  have hF : (toFullBlockMat F).PosDef := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj
    m hm s
  have hH : (toFullBlockMat H).PosDef := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj
    mPlus hmPlus t
  have hOld (r : ℤ) : (toFullBlockMat (adaptedMean P q r)).PosDef := adaptedMean_posDef d hd P γ
    E Ψ K S hstat hdag jStar hj m hm r
  have hNew (j : ℤ) : (toFullBlockMat (adaptedMean P qPlus j)).PosDef := adaptedMean_posDef d hd
    P γ E Ψ K S hstat hdag jStar hj mPlus hmPlus j
  have hf (r : ℤ) (hr : r ∈ Finset.Icc (jStar : ℤ) (s - 1)) : 0 ≤ f r :=
    transport_drift_trace_nonneg d hd P γ E Ψ K S hstat hdag jStar hj m hm r s
      (Finset.mem_Icc.mp hr).1
      (by have := (Finset.mem_Icc.mp hr).2; omega)
  have hDold : 0 ≤ Dold := bridge_determinantDrift_nonneg d hd P γ E Ψ K S hstat hdag jStar hj m
    hm s
  have hPi : 0 ≤ aspectRatio E := (one_le_aspectRatio_of_coarseEllipticityDagger hdag).trans'
    (by norm_num)
  obtain ⟨hB, hBcross⟩ :=
    transport_cross_eccentricity_bound (aspectRatio E) (Real.sqrt (‖m‖ * ‖m⁻¹‖))
      (Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖)) hPi (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hIold : 0 ≤ Iold := by
    dsimp only [Iold]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
      (mul_nonneg hCw.le (zero_le_one.trans hK₀))) hG₁) (three_rpow_nonneg _)
  have hYold : 0 ≤ Yold := by
    dsimp only [Yold]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
      (add_nonneg hCw.le hCn.le)) hB
  have htW : adaptedCell qPlus t ⊆ centeredCube d (2 * (jStar : ℤ)) := Set.Subset.trans
    Set.subset_union_right hwindow
  have hsW' : adaptedCell q s ⊆ centeredCube d (2 * (jStar : ℤ)) := Set.Subset.trans
    Set.subset_union_left hwindow
  have hjW (j : ℤ) (hjt : j ≤ t) : adaptedCell qPlus j ⊆ centeredCube d (2 * (jStar : ℤ)) :=
    (Set.image_mono (Window.centeredCube_mono hjt)).trans htW
  have hpoint (j : ℤ) (hj' : j ∈ Finset.Icc (jStar : ℤ) (t - 1)) :
      g j ≤ (4 / 3 : ℝ) * (if j < (jStar : ℤ) + L then 0 else f (j - (L : ℤ)) +
        (Cw * K₀) * ∑ r ∈ Finset.Icc (jStar : ℤ) (j - (L : ℤ) - 1), (3 : ℝ) ^ ((r : ℝ) - j) * f r) +
        (Cs * B) * (if j < (jStar : ℤ) + L then 1 else (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - jStar))) +
        (Cd * δ + Ci * K₀ * (3 : ℝ) ^ (-(L : ℝ))) := by
    let old := if j < (jStar : ℤ) + L then 0 else f (j - (L : ℤ)) +
      (Cw * K₀) * ∑ r ∈ Finset.Icc (jStar : ℤ) (j - (L : ℤ) - 1), (3 : ℝ) ^ ((r : ℝ) - j) * f r
    let src := if j < (jStar : ℤ) + L then 1 else (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - jStar))
    have ho0 : 0 ≤ old := by
      dsimp only [old]; split_ifs with he
      · exact le_rfl
      · have hjj := Finset.mem_Icc.mp hj'
        exact add_nonneg (hf _ (Finset.mem_Icc.mpr ⟨by omega, by dsimp only [s, t] at *; omega⟩))
          (mul_nonneg (mul_nonneg hCw.le (zero_le_one.trans hK₀)) (Finset.sum_nonneg fun r hr =>
            mul_nonneg (three_rpow_nonneg _)
            (hf r (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, by have := (Finset.mem_Icc.mp
              hr).2; dsimp only [s, t] at *; omega⟩))))
    have hz0 : 0 ≤ src := by
      dsimp only [src]; split_ifs with he
      · exact zero_le_one
      · exact three_rpow_nonneg _
    have ho : blockTrace (blockSub (normalizedBlock (adaptedMean P qPlus j) F)
      (Book.Ch02.blockIdentity d)) ≤
        old + Yold * src + Iold := by
      by_cases he : j < (jStar : ℤ) + L
      · have hsrc := hsource P E Ψ K S hstat hdag jStar hj hsN m mPlus hm hmPlus s j
          (by dsimp only [s]; omega) (Finset.mem_Icc.mp hj').1 hsW' (hjW j (by have :=
            (Finset.mem_Icc.mp hj').2; omega))
        have hb := transport_normalized_trace_scalar_bound (adaptedMean P qPlus j) F (hNew
          j).posSemidef hF
          (Cn * aspectRatio E * Real.sqrt (‖m‖ * ‖m⁻¹‖) * Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖))
          (mul_nonneg (mul_nonneg (mul_nonneg hCn.le hPi) (Real.sqrt_nonneg _))
            (Real.sqrt_nonneg _)) hsrc
        have hbc := mul_le_mul_of_nonneg_left hBcross (mul_nonneg (two_mul_natCast_nonneg d) hCn.le)
        dsimp only [old, src]; rw [ite_eq_left he, ite_eq_left he, mul_one, zero_add]
        have hbc' : (2 * (d : ℝ)) * Cn * B ≤ Yold := by
          dsimp only [Yold]
          nlinarith only [mul_nonneg (mul_nonneg (two_mul_natCast_nonneg d) hCw.le) hB]
        nlinarith only [hb, hbc, hbc', hIold]
      · have hlate := hwhitney P E Ψ K S hstat hdag jStar hj hsW m mPlus hm hmPlus hratio j s
          (by dsimp only [s]; omega) L hL (by omega) (hjW j (by have := (Finset.mem_Icc.mp
            hj').2; omega)) hsW'
        have ht := transport_drift_trace_comparison (fun r => adaptedMean P q r) (adaptedMean P
          qPlus j) F
          hOld (hNew j) hF (Finset.Icc (jStar : ℤ) (j - (L : ℤ) - 1)) (j - (L : ℤ))
          (fun r => (3 : ℝ) ^ ((r : ℝ) - j)) (fun _ => three_rpow_nonneg _)
          (Cw * K₀) (Cw * B * (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - jStar)))
          (mul_nonneg hCw.le (zero_le_one.trans hK₀)) (mul_nonneg (mul_nonneg hCw.le hB)
            (three_rpow_nonneg _)) hlate
        change _ ≤ f (j - (L : ℤ)) + (Cw * K₀) *
          (∑ r ∈ Finset.Icc (jStar : ℤ) (j - (L : ℤ) - 1), (3 : ℝ) ^ ((r : ℝ) - j) * f r) +
          (2 * (d : ℝ)) * (Cw * K₀) * (∑ r ∈ Finset.Icc (jStar : ℤ) (j - (L : ℤ) - 1), (3 : ℝ) ^
            ((r : ℝ) - j)) +
          (2 * (d : ℝ)) * (Cw * B * (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - jStar))) at ht
        have hi := mul_le_mul_of_nonneg_left (transport_drift_identity_row (jStar : ℤ) j L)
          (mul_nonneg (two_mul_natCast_nonneg d) (mul_nonneg hCw.le (zero_le_one.trans hK₀)))
        have hcs : (2 * (d : ℝ)) * Cw * B ≤ Yold := by
          dsimp only [Yold]
          nlinarith only [mul_nonneg (mul_nonneg (two_mul_natCast_nonneg d) hCn.le) hB]
        have hcs' := mul_le_mul_of_nonneg_right hcs (three_rpow_nonneg (-(1 - γ) * ((j : ℝ) -
          jStar)))
        dsimp only [old, src]; rw [ite_eq_right he, ite_eq_right he]
        dsimp only [Iold, G₁]
        linarith only [ht, hi, hcs']
    have hc := transport_trace_normalizer_comparison hF hH (hNew j).posSemidef hδ hlow hup
    have hδpos : 0 < 1 - δ := by linarith only [hδ.2]
    have hbound := hc.trans (add_le_add (mul_le_mul_of_nonneg_left ho (inv_nonneg.mpr hδpos.le))
      le_rfl)
    have hbounds := transport_delta_bounds d hδ
    have hU0 : 0 ≤ old + Yold * src + Iold := add_nonneg (add_nonneg ho0 (mul_nonneg hYold hz0))
      hIold
    have hlast := hbound.trans (add_le_add (mul_le_mul_of_nonneg_right hbounds.1 hU0) hbounds.2)
    change g j ≤ (4 / 3 : ℝ) * (old + Yold * src + Iold) + (8 / 3 : ℝ) * d * δ at hlast
    calc
      _ ≤ _ := hlast
      _ = _ := by dsimp only [Yold, Iold, Cs, Cd, Ci]; ring
  have hscalar := transport_drift_scalar_assembly a (1 - γ) ha ha1 hab (jStar : ℤ) n hn L hL f g hf
    (4 / 3) (Cw * K₀) (Cs * B) (Cd * δ + Ci * K₀ * (3 : ℝ) ^ (-(L : ℝ)))
    (by norm_num) (mul_nonneg hCw.le (zero_le_one.trans hK₀)) (mul_nonneg hCs hB) hpoint
  have hAbel := transport_determinantDrift_abel P γ qPlus jStar t (by dsimp only [t]; omega) hH
  have hAbelOld := transport_determinantDrift_abel P γ q jStar s (by dsimp only [s]; omega) hF
  have hsumOld := transport_abel_sum_bound a ha (jStar : ℤ) s (by dsimp only [s]; omega) f hf
    Dold hAbelOld.symm
  simp only [s, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] at hsumOld
  have hsc : determinantDrift P γ qPlus jStar t ≤
      (4 / 3 : ℝ) * grow * (1 + (Cw * K₀) * Gb) *
        (∑ r ∈ Finset.Icc (jStar : ℤ) (s - 1), (3 : ℝ) ^ (-a * ((n : ℝ) + 2 * L - r - 1)) * f r) +
        (Cs * B) * ((n : ℝ) + L - jStar) * R + (Cd * δ + Ci * K₀ * (3 : ℝ) ^ (-(L : ℝ))) := by
    rw [hAbel]
    simpa only [t, s, g, a, grow, Gb, R, div_eq_mul_inv, one_mul, Int.cast_add,
      Int.cast_natCast] using hscalar
  have hcoef : 0 ≤ (4 / 3 : ℝ) * grow * (1 + (Cw * K₀) * Gb) := by
    dsimp only [grow]
    exact mul_nonneg (mul_nonneg (by norm_num) (three_rpow_nonneg _))
      (add_nonneg zero_le_one (mul_nonneg (mul_nonneg hCw.le (zero_le_one.trans hK₀)) hGb))
  have hpay := hsc.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hsumOld hcoef)
    le_rfl) le_rfl)
  have hgrowD : 0 ≤ grow * Dold := mul_nonneg (by dsimp only [grow]; exact three_rpow_nonneg _)
    hDold
  have hsourceGrow : (Cs * B) * ((n : ℝ) + L - jStar) * R ≤
      C * B * (1 + (n : ℝ) + L - jStar) * R :=
    transport_source_growth_bound Cs C B R jStar n L hn hCs hCsC hB
      (by dsimp only [R]; exact three_rpow_nonneg _)
  have hfinal : determinantDrift P γ qPlus jStar t ≤
      C * (δ + K₀ * (3 : ℝ) ^ (-(L : ℝ)) + grow * Dold) +
        C * B * (1 + (n : ℝ) + L - jStar) * R := by
    have hpaid : determinantDrift P γ qPlus jStar t ≤
        Co * (grow * Dold) + (Cs * B) * ((n : ℝ) + L - jStar) * R +
          (Cd * δ + Ci * (K₀ * (3 : ℝ) ^ (-(L : ℝ)))) := by
      (convert hpay using 1; try rfl)
      show (4 / 3 : ℝ) * (1 + (Cw * K₀) * Gb) * (1 / (1 - (3 : ℝ) ^ (-a))) * (grow * Dold) +
          (Cs * B) * ((n : ℝ) + L - jStar) * R +
          (Cd * δ + Ci * (K₀ * (3 : ℝ) ^ (-(L : ℝ)))) = _
      ring
    exact transport_drift_error_absorption _ C Co Cd Ci δ _ _ _ _ hpaid hCoC hCdC hCiC
      hgrowD hδ.1 (mul_nonneg (zero_le_one.trans hK₀) (three_rpow_nonneg _)) hsourceGrow
  have heGrow : grow = (3 : ℝ) ^ ((1 - γ) / 4 * (L : ℝ)) := by
    dsimp only [grow, a]
    congr 1
    ring
  rw [heGrow] at hfinal
  exact hfinal


end
end HCPolySupport.HighContrast.Annealed
