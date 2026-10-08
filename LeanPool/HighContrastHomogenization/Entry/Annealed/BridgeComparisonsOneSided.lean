/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.BridgeComparisons

/-!
# High-contrast homogenization: Entry.Annealed.BridgeComparisonsOneSided

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The two one-sided Whitney comparisons

`p.successful.short.bridge`. Countable subadditivity uses response
quadratics on the open parent and its open cells. A single locally elliptic
representative serves the entire partition. The null remainder is never
an argument of `coarseBlock`.

The companion module `BridgeComparisons` holds the shared partition-comparison
machinery. Here the two comparisons themselves are proved: the forward
comparison bounds the Loewner difference of the new and old adapted means by the
old-grid quadratic sum together with a locally elliptic term, and the reverse
comparison is the matching bound in the opposite direction, with the packed new
cells at `n + L` and the old boundary rows running up to that cap. The cap-row
mass bound gives the summability of the boundary row masses on which the
countable subadditivity argument rests. The quadratic identities
`bridge_enlarge_quadratic_smul` and `bridge_enlarge_quadratic_add` record the
scaling and additivity of the response quadratic.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter adaptedMean aspectRatio blockScale
  blockSub blockVecDot_blockMatVecMul_eq_sum gridRatio)
open HCPolySupport.HighContrast (adaptedCell adaptedCellTranslate centeredCube)
namespace HCPolySupport.HighContrast.Annealed

open MeasureTheory Geometry Filter
open scoped Matrix.Norms.L2Operator
noncomputable section

/-- The forward cap row has mass at most one. Summability is obtained from
finite volume before the full mass identity is used. -/
theorem bridge_whitney_cap_mass_le_one {d : ℕ} [NeZero d]
    (W : Set (Vec d)) (q : Mat d) (hq : IsUnit q) (cap : ℤ) (hW : volume W ≠ ⊤)
    (hfin : ∀ r : ℤ, r ≤ cap → (maximalAdaptedCellCenters W q cap r).Finite)
    (hwt : (∑' r : {r : ℤ // r ≤ cap}, ∑ _z ∈ (hfin r.1 r.2).toFinset,
      (volume (adaptedCell q r.1)).toReal / (volume W).toReal) = 1) :
    (∑ _z ∈ (hfin cap le_rfl).toFinset,
      (volume (adaptedCell q cap)).toReal / (volume W).toReal) ≤ 1 := by
  have hs : Summable (fun r : {r : ℤ // r ≤ cap} =>
      ∑ _z ∈ (hfin r.1 r.2).toFinset,
        (volume (adaptedCell q r.1)).toReal / (volume W).toReal) := by
    simpa only [Finset.sum_div] using
      (hasSum_maximalAdaptedCell_row_volumes hq hW cap hfin).summable.div_const (volume W).toReal
  rw [← hwt]
  exact hs.le_tsum ⟨cap, le_rfl⟩ (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))

private theorem bridge_full_quadratic_nonneg {d : ℕ} {A : BlockMat d}
    (hA : (toFullBlockMat A).PosSemidef) (v : BlockVec d) :
    0 ≤ (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul A v) := by
  apply mul_nonneg (by norm_num)
  simpa only [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul, star_trivial] using
    hA.dotProduct_mulVec_nonneg (toFullBlockVec v)

/-- Local restatement of `bridge_quadratic_smul` from `BridgeComparisons`, kept private
to this file since the source lemma is itself file-private there. -/
private theorem bridge_enlarge_quadratic_smul {d : ℕ} (c : ℝ) (A : BlockMat d) (v : BlockVec d) :
    (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat (c • toFullBlockMat A)) v) =
      c * ((1 / 2 : ℝ) * blockVecDot v (blockMatVecMul A v)) :=
  Source.quadratic_blockScale c A v

/-- Local restatement of `bridge_quadratic_add` from `BridgeComparisons`, kept private
to this file since the source lemma is itself file-private there. -/
private theorem bridge_enlarge_quadratic_add {d : ℕ} (M N : FullBlockMat d) (v : BlockVec d) :
    (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat (M + N)) v) =
      (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat M) v) +
        (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat N) v) := by
  simp only [blockVecDot_blockMatVecMul_eq_sum, blockMatEntry_ofFullBlockMat,
    Matrix.add_apply, add_mul, mul_add, Finset.sum_add_distrib]

private theorem bridge_comparison_enlarge {d : ℕ} (A : ℤ → BlockMat d)
    (H Base T : BlockMat d) (hA : ∀ r, (toFullBlockMat (A r)).PosSemidef)
    (hT : (toFullBlockMat T).PosSemidef) (J cap j : ℤ) (hJj : J ≤ j)
    (Cw Ct C K₀ Pi a b γ : ℝ) (_hCw : 0 ≤ Cw) (_hCt : 0 ≤ Ct)
    (hC : 0 ≤ C) (hK₀ : 1 ≤ K₀) (hCwC : Cw ≤ C) (hCtC : Ct * Cw ≤ C)
    (hPi : 0 ≤ Pi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hγ : 0 ≤ γ)
    (h : BlockMatLoewnerLE (blockSub H Base)
      (ofFullBlockMat (toFullBlockMat (blockScale Cw (ofFullBlockMat
        (∑ r ∈ Finset.Icc J cap, (3 : ℝ) ^ ((r : ℝ) - j) • toFullBlockMat (A r)))) +
        toFullBlockMat (blockScale (Ct * Cw * Pi * a ^ 2 * (3 : ℝ) ^ (-((j : ℝ) - J))) T)))) :
    BlockMatLoewnerLE (blockSub H Base)
      (ofFullBlockMat (toFullBlockMat (blockScale (C * K₀) (ofFullBlockMat
        (∑ r ∈ Finset.Icc J cap, (3 : ℝ) ^ ((r : ℝ) - j) • toFullBlockMat (A r)))) +
        toFullBlockMat (blockScale (C * (1 + Pi * (a + b) ^ 2) *
          (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - J))) T))) := by
  have hc : Cw ≤ C * K₀ := hCwC.trans (le_mul_of_one_le_right hC hK₀)
  have ht : Ct * Cw * Pi * a ^ 2 * (3 : ℝ) ^ (-((j : ℝ) - J)) ≤
      C * (1 + Pi * (a + b) ^ 2) * (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - J)) := by
    calc
      _ = (Ct * Cw) * (Pi * a ^ 2 * (3 : ℝ) ^ (-((j : ℝ) - J))) := by ring
      _ ≤ C * (Pi * a ^ 2 * (3 : ℝ) ^ (-((j : ℝ) - J))) :=
        mul_le_mul_of_nonneg_right hCtC (by positivity)
      _ ≤ C * ((1 + Pi * (a + b) ^ 2) * (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - J))) :=
        mul_le_mul_of_nonneg_left (bridge_source_normalization_factor hPi ha hb
          (by exact_mod_cast sub_nonneg.mpr hJj) hγ) hC
      _ = _ := by ring
  intro v
  apply (h v).trans
  simp only [bridge_enlarge_quadratic_add, ofFullBlockMat_toFullBlockMat,
    Source.quadratic_blockScale]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right hc
    rw [bridge_quadratic_sum]
    exact Finset.sum_nonneg (fun r _ => by
      rw [bridge_enlarge_quadratic_smul]
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (bridge_full_quadratic_nonneg (hA r) v))
  · exact mul_le_mul_of_nonneg_right ht (bridge_full_quadratic_nonneg hT v)

private theorem bridge_forward_rows {d : ℕ}
    (W : Set (Vec d)) (q : Mat d) (hq : IsUnit q) (cap j : ℤ)
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hfin : ∀ t : ℤ, t ≤ cap → (maximalAdaptedCellCenters W q cap t).Finite)
    (hrow : ∀ (t : ℤ) (ht : t < cap),
      (∑ _z ∈ (hfin t ht.le).toFinset, (volume (adaptedCell q t)).toReal / (volume W).toReal) ≤
        Cw * (3 : ℝ) ^ ((t : ℝ) - j)) :
    let I := {p : ℤ × (Fin d → ℤ) // IsMaximalAdaptedCellIn W q cap p.1 p.2}
    ∀ (t : ℤ), t ≤ cap →
      (∑' i : {i : {i : I // i.1.1 < cap} // i.1.1.1 = t},
        (volume (adaptedCellAtCenter q i.1.1.1.1 i.1.1.1.2)).toReal / (volume W).toReal) ≤
        Cw * (3 : ℝ) ^ ((t : ℝ) - j) := by
  intro I t ht
  by_cases htn : t < cap
  · let e : {i : {i : I // i.1.1 < cap} // i.1.1.1 = t} ≃
        {i : I // i.1.1 = t} :=
      { toFun := fun i => ⟨i.1.1, i.2⟩
        invFun := fun i => ⟨⟨i.1, by rw [i.2]; exact htn⟩, i.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hr := (bridge_maximal_row_mass W q hq cap t (hfin t ht) (volume W).toReal).2
    have he := e.tsum_eq (fun i => (volume (adaptedCellAtCenter q i.1.1.1 i.1.1.2)).toReal /
      (volume W).toReal)
    change (∑' i : {i : {i : I // i.1.1 < cap} // i.1.1.1 = t},
      (volume (adaptedCellAtCenter q i.1.1.1.1 i.1.1.1.2)).toReal / (volume W).toReal) = _ at he
    rw [he, hr]
    exact hrow t htn
  · have he : t = cap := by omega
    have hempty : IsEmpty {i : {i : I // i.1.1 < cap} // i.1.1.1 = t} := ⟨fun i => by
      have hi := i.1.2
      have hit := i.2
      omega⟩
    simp only [tsum_empty]
    positivity

/-- The forward Whitney comparison, `e.bridge.upper.comparison`.
The old-grid sum ends at `n`; its parent is the new cell at `n+L`. -/
theorem bridge_upper_comparison (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (K₀ : ℝ) (hK₀ : 1 ≤ K₀) :
    ∃ Csrc C : ℝ, 0 < Csrc ∧ 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ jStar : ℕ, 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          ∀ (m mPlus : Mat d), m.PosDef → mPlus.PosDef →
            gridRatio (explicitRoundedGrid jStar m) (explicitRoundedGrid jStar mPlus) ≤ K₀ →
            ∀ (n : ℤ) (L : ℕ), (jStar : ℤ) ≤ n → 1 ≤ L →
              adaptedCell (explicitRoundedGrid jStar m) (n + 2 * (L : ℤ)) ∪
                  adaptedCell (explicitRoundedGrid jStar mPlus) (n + (L : ℤ)) ⊆
                centeredCube d (2 * (jStar : ℤ)) →
              BlockMatLoewnerLE
                (blockSub (adaptedMean P (explicitRoundedGrid jStar mPlus) (n + (L : ℤ)))
                  (adaptedMean P (explicitRoundedGrid jStar m) n))
                (ofFullBlockMat
                  (toFullBlockMat (blockScale (C * K₀) (ofFullBlockMat
                    (∑ r ∈ Finset.Icc (jStar : ℤ) n,
                      (3 : ℝ) ^ ((r : ℝ) - (n : ℝ) - (L : ℝ)) •
                        toFullBlockMat (adaptedMean P (explicitRoundedGrid jStar m) r)))) +
                    toFullBlockMat (blockScale
                      (C * (1 + aspectRatio E * (Real.sqrt (‖m‖ * ‖m⁻¹‖) +
                        Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖)) ^ 2) *
                        (3 : ℝ) ^ (-(1 - γ) * ((n : ℝ) + (L : ℝ) - jStar)))
                      (adaptedMean P (explicitRoundedGrid jStar m) (n + 2 * (L : ℤ)))))) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Cs, Ct, hCs, hCt, hcomp⟩ := bridge_partition_comparison d hd γ hγ
  obtain ⟨Cg, _hCg, hwhitney⟩ := Entry.two_grid_whitney d hd
  obtain ⟨Cw, hCw, hwhitney⟩ := hwhitney K₀ hK₀
  let C := Cw * (Ct + 1)
  have hC : 0 < C := mul_pos hCw (by positivity)
  have hCwC : Cw ≤ C := by dsimp [C]; nlinarith only [mul_pos hCw hCt]
  have hCtC : Ct * Cw ≤ C := by dsimp [C]; nlinarith only [hCw]
  refine ⟨max Cs (Cg γ), C, hCs.trans_le (le_max_left _ _), hC, ?_⟩
  intro P hP E Ψ K S hstat hdag jStar hj hsrc m mPlus hm hmPlus hratio n L hn hL hcontain
  classical
  let q := explicitRoundedGrid jStar m
  let qPlus := explicitRoundedGrid jStar mPlus
  let W := adaptedCell qPlus (n + (L : ℤ))
  let I := {p : ℤ × (Fin d → ℤ) | IsMaximalAdaptedCellIn W q n p.1 p.2}
  have hq : IsUnit q := isUnit_roundedGrid hj hm
  have hqPlus : IsUnit qPlus := isUnit_roundedGrid hj hmPlus
  have hlog : 0 ≤ Real.logb 3 (2 * K) := (Real.logb_pos (by norm_num)
    (by linarith only [hdag.one_lt_growthWitness] : (1 : ℝ) < 2 * K)).le
  have hsrcs := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left Cs (Cg γ)) hlog)).trans hsrc
  have hsrcg := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_right Cs (Cg γ)) hlog)).trans
    hsrc
  have hzero : (0 : Vec d) ∈ adaptedLatticeAtScale qPlus (n + (L : ℤ)) := by
    exact ⟨0, by
      simp only [adaptedCellCenter, Pi.zero_apply, Int.cast_zero]
      change (3 : ℝ) ^ (n + (L : ℤ)) • matVecMul qPlus 0 = 0
      simp only [matVecMul_zero, smul_zero]⟩
  have hg := (hwhitney γ hγ K hdag.one_lt_growthWitness jStar hj hsrcg
    m mPlus hm hmPlus hratio (n + (L : ℤ)) L hL).1 0 hzero
  obtain ⟨hfin, hsub, hdis, hnull, _hvol, _hcard, _hcount, hmass, hrow⟩ := hg
  have _hcapmass := bridge_whitney_cap_mass_le_one
    (adaptedCellTranslate qPlus (n + (L : ℤ)) 0) q hq (n + (L : ℤ) - (L : ℤ))
    (Transport.volume_adaptedCellTranslate_ne_top _ _ _) hfin hmass
  simp only [add_sub_cancel_right, adaptedCellTranslate, zero_add,
    Set.image_id'] at hfin hsub hdis hnull hrow
  have hforward := hcomp P E Ψ K S hstat hdag jStar hj hsrcs m m mPlus hm hm hmPlus
    n n (n + (L : ℤ)) (n + 2 * (L : ℤ)) hn hn (by omega)
    (Set.Subset.trans Set.subset_union_right hcontain)
    (Set.Subset.trans Set.subset_union_left hcontain)
    (ℤ × (Fin d → ℤ)) I (fun _ => q) (fun _ _ => hq) Prod.fst
    (fun p => adaptedCellCenter q p.1 p.2) (fun p => p.1 < n) Prod.fst Prod.snd
    (fun p hp => hsub p.1 p.2 hp) hdis hnull
    (fun _ _ _ => rfl)
    (fun p hp hpn => by
      have he : p.1 = n := by have hh := hp.1.1; omega
      change adaptedCellAtCenter q p.1 p.2 = adaptedCellAtCenter q n p.2
      rw [he])
    (fun _ hp _ => hp.1.1) Cw hCw.le
  have hrows := bridge_forward_rows W q hq n (n + (L : ℤ)) Cw hCw.le hfin hrow
  have hb := hforward hrows
  have h := bridge_comparison_enlarge (fun r => adaptedMean P q r)
    (adaptedMean P qPlus (n + (L : ℤ))) (adaptedMean P q n)
    (adaptedMean P q (n + 2 * (L : ℤ)))
    (fun r => (adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm r).posSemidef)
    (adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm _).posSemidef
    jStar n (n + (L : ℤ)) (by omega) Cw Ct C K₀ (aspectRatio E)
    (Real.sqrt (‖m‖ * ‖m⁻¹‖)) (Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖)) γ
    hCw.le hCt.le hC.le hK₀ hCwC hCtC (one_le_aspectRatio_of_coarseEllipticityDagger hdag
      |>.trans' (by norm_num))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hγ.1 hb
  simpa only [Int.cast_add, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat,
    sub_add_eq_sub_sub, q, qPlus] using h

/-- The reverse Whitney comparison, `e.bridge.lower.comparison`. The
packed new cells are at `n+L`; the old boundary rows include that cap. -/
theorem bridge_lower_comparison (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (K₀ : ℝ) (hK₀ : 1 ≤ K₀) :
    ∃ Csrc C : ℝ, 0 < Csrc ∧ 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ jStar : ℕ, 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          ∀ (m mPlus : Mat d), m.PosDef → mPlus.PosDef →
            gridRatio (explicitRoundedGrid jStar m) (explicitRoundedGrid jStar mPlus) ≤ K₀ →
            ∀ (n : ℤ) (L : ℕ), (jStar : ℤ) ≤ n → 1 ≤ L →
              adaptedCell (explicitRoundedGrid jStar m) (n + 2 * (L : ℤ)) ∪
                  adaptedCell (explicitRoundedGrid jStar mPlus) (n + (L : ℤ)) ⊆
                centeredCube d (2 * (jStar : ℤ)) →
              BlockMatLoewnerLE
                (blockSub (adaptedMean P (explicitRoundedGrid jStar m) (n + 2 * (L : ℤ)))
                  (adaptedMean P (explicitRoundedGrid jStar mPlus) (n + (L : ℤ))))
                (ofFullBlockMat
                  (toFullBlockMat (blockScale (C * K₀) (ofFullBlockMat
                    (∑ r ∈ Finset.Icc (jStar : ℤ) (n + (L : ℤ)),
                      (3 : ℝ) ^ ((r : ℝ) - (n : ℝ) - 2 * (L : ℝ)) •
                        toFullBlockMat (adaptedMean P (explicitRoundedGrid jStar m) r)))) +
                    toFullBlockMat (blockScale
                      (C * (1 + aspectRatio E * (Real.sqrt (‖m‖ * ‖m⁻¹‖) +
                        Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖)) ^ 2) *
                        (3 : ℝ) ^ (-(1 - γ) * ((n : ℝ) + 2 * (L : ℝ) - jStar)))
                      (adaptedMean P (explicitRoundedGrid jStar m) (n + 2 * (L : ℤ)))))) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Cs, Ct, hCs, hCt, hcomp⟩ := bridge_partition_comparison d hd γ hγ
  obtain ⟨Cg, _hCg, hwhitney⟩ := Entry.two_grid_whitney d hd
  obtain ⟨Cw, hCw, hwhitney⟩ := hwhitney K₀ hK₀
  let C := Cw * (Ct + 1)
  have hC : 0 < C := mul_pos hCw (by positivity)
  have hCwC : Cw ≤ C := by dsimp [C]; nlinarith only [mul_pos hCw hCt]
  have hCtC : Ct * Cw ≤ C := by dsimp [C]; nlinarith only [hCw]
  refine ⟨max Cs (Cg γ), C, hCs.trans_le (le_max_left _ _), hC, ?_⟩
  intro P hP E Ψ K S hstat hdag jStar hj hsrc m mPlus hm hmPlus hratio n L hn hL hcontain
  classical
  let q := explicitRoundedGrid jStar m
  let qPlus := explicitRoundedGrid jStar mPlus
  let cap := n + (L : ℤ)
  let W := adaptedCell q (n + 2 * (L : ℤ))
  let V := adaptedUncoveredPart W qPlus cap
  let O := {p : ℤ × (Fin d → ℤ) | IsMaximalAdaptedCellIn V q cap p.1 p.2}
  let ι := (Fin d → ℤ) ⊕ (ℤ × (Fin d → ℤ))
  let I : Set ι := {i | Sum.elim (fun w => adaptedCellAtCenter qPlus cap w ⊆ W) (fun p => p ∈ O) i}
  let qi : ι → Mat d := Sum.elim (fun _ => qPlus) (fun _ => q)
  let ji : ι → ℤ := Sum.elim (fun _ => cap) Prod.fst
  let yi : ι → Vec d := Sum.elim (adaptedCellCenter qPlus cap)
    (fun p => adaptedCellCenter q p.1 p.2)
  let U := fun i => adaptedCellTranslate (qi i) (ji i) (yi i)
  let old : ι → Prop := Sum.elim (fun _ => False) (fun _ => True)
  let r : ι → ℤ := Sum.elim (fun _ => cap) Prod.fst
  let z : ι → Fin d → ℤ := Sum.elim id Prod.snd
  have hq : IsUnit q := isUnit_roundedGrid hj hm
  have hqPlus : IsUnit qPlus := isUnit_roundedGrid hj hmPlus
  have hlog : 0 ≤ Real.logb 3 (2 * K) := (Real.logb_pos (by norm_num)
    (by linarith only [hdag.one_lt_growthWitness] : (1 : ℝ) < 2 * K)).le
  have hsrcs := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left Cs (Cg γ)) hlog)).trans hsrc
  have hsrcg := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_right Cs (Cg γ)) hlog)).trans
    hsrc
  have hzero : (0 : Vec d) ∈ adaptedLatticeAtScale q (n + 2 * (L : ℤ)) := by
    exact ⟨0, by
      simp only [adaptedCellCenter, Pi.zero_apply, Int.cast_zero]
      change (3 : ℝ) ^ (n + 2 * (L : ℤ)) • matVecMul q 0 = 0
      simp only [matVecMul_zero, smul_zero]⟩
  have hg := (hwhitney γ hγ K hdag.one_lt_growthWitness jStar hj hsrcg
    m mPlus hm hmPlus hratio (n + 2 * (L : ℤ)) L hL).2 0 hzero
  have hecap : n + 2 * (L : ℤ) - (L : ℤ) = cap := by dsimp [cap]; omega
  simp only [hecap, adaptedCellTranslate, zero_add, Set.image_id'] at hg
  obtain ⟨hfin, hsubO, hdisO, hnullO, hrowO⟩ := hg
  have hsub (i : ι) (hi : i ∈ I) : U i ⊆ W := by
    cases i with
    | inl w => exact hi
    | inr p => exact (hsubO p.1 p.2 hi).trans Set.sdiff_subset
  have hcross (w : Fin d → ℤ) (p : ℤ × (Fin d → ℤ))
      (hw : adaptedCellAtCenter qPlus cap w ⊆ W) (hp : p ∈ O) :
      Disjoint (adaptedCellAtCenter qPlus cap w) (adaptedCellAtCenter q p.1 p.2) := by
    apply Set.disjoint_left.mpr
    intro x hxw hxp
    exact (hp.1.2 hxp).2 (Set.mem_iUnion₂.mpr ⟨w, hw, hxw⟩)
  have hdis : I.PairwiseDisjoint U := by
    intro i hi k hk hne
    cases i with
    | inl w =>
      cases k with
      | inl v => exact adaptedCellAtCenter_disjoint_of_ne hqPlus cap (fun he => hne (congrArg
        Sum.inl he))
      | inr p => exact hcross w p hi hk
    | inr p =>
      cases k with
      | inl w => exact (hcross w p hk hi).symm
      | inr p' => exact hdisO hi hk (fun he => hne (congrArg Sum.inr he))
  have hUnion : (⋃ i ∈ I, U i) = adaptedCoveredPart W qPlus cap ∪
      ⋃ p ∈ O, adaptedCellAtCenter q p.1 p.2 := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
      cases i with
      | inl w => exact Or.inl (Set.mem_iUnion₂.mpr ⟨w, hi, hxi⟩)
      | inr p => exact Or.inr (Set.mem_iUnion₂.mpr ⟨p, hi, hxi⟩)
    · intro hx
      rcases hx with hx | hx
      · obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
        exact Set.mem_iUnion₂.mpr ⟨Sum.inl w, hw, hxw⟩
      · obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
        exact Set.mem_iUnion₂.mpr ⟨Sum.inr p, hp, hxp⟩
  have hnull : volume (W \ ⋃ i ∈ I, U i) = 0 := by rw [hUnion]; exact hnullO
  have hold (i : ι) (_hi : i ∈ I) (hoi : old i) : U i = adaptedCellAtCenter q (r i) (z i) := by
    cases i with
    | inl w => exact False.elim hoi
    | inr p => rfl
  have hbase (i : ι) (_hi : i ∈ I) (hoi : ¬old i) : U i = adaptedCellAtCenter qPlus cap (z i) := by
    cases i with
    | inl w => rfl
    | inr p => exact False.elim (hoi True.intro)
  have hcap (i : ι) (hi : i ∈ I) (hoi : old i) : r i ≤ cap := by
    cases i with
    | inl w => exact False.elim hoi
    | inr p => exact hi.1.1
  have hrows (t : ℤ) (ht : t ≤ cap) :
      (∑' i : {i : {i : I // old i} // r i.1 = t},
        (volume (U i.1.1)).toReal / (volume W).toReal) ≤
        Cw * (3 : ℝ) ^ ((t : ℝ) - ((n + 2 * (L : ℤ) : ℤ) : ℝ)) := by
    let F := {i : {i : I // old i} // r i.1 = t}
    have hid (i : F) : i.1.1.1 = Sum.inr (r i.1.1, z i.1.1) := by
      cases he : i.1.1.1 with
      | inl w => have hi := i.1.2; simp only [old, he, Sum.elim_inl] at hi
      | inr p => simp only [r, z, Sum.elim_inr, Prod.mk.eta]
    let e : F → {p : O // p.1.1 = t} := fun i =>
      ⟨⟨(r i.1.1, z i.1.1), by
        have hi := i.1.1.2
        rw [hid i] at hi
        exact hi⟩, i.2⟩
    have he : Function.Injective e := by
      intro i k h
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      rw [hid i, hid k]
      exact congrArg Sum.inr (congrArg (fun x : {p : O // p.1.1 = t} => x.1.1) h)
    have hweight (i : F) : (volume (U i.1.1)).toReal / (volume W).toReal =
        (volume (adaptedCellAtCenter q (e i).1.1.1 (e i).1.1.2)).toReal / (volume W).toReal := by
      rw [hold i.1.1 i.1.1.2 i.1.2]
    have hr := bridge_maximal_row_mass V q hq cap t (hfin t ht) (volume W).toReal
    have hs : Summable (fun i : F => (volume (U i.1.1)).toReal / (volume W).toReal) := by
      simp_rw [hweight]
      exact hr.1.comp_injective he
    have hb := Summable.tsum_le_tsum_of_inj e he (fun _ _ => by positivity)
      (fun i => (hweight i).le) hs hr.1
    exact hb.trans (hr.2 ▸ hrowO t ht)
  have hb := hcomp P E Ψ K S hstat hdag jStar hj hsrcs m mPlus m hm hmPlus hm
    cap cap (n + 2 * (L : ℤ)) (n + 2 * (L : ℤ)) (by dsimp [cap]; omega)
    (by dsimp [cap]; omega) (by omega)
    (Set.Subset.trans Set.subset_union_left hcontain)
    (Set.Subset.trans Set.subset_union_left hcontain) ι I qi
    (fun i _ => by cases i with | inl _ => exact hqPlus | inr _ => exact hq)
    ji yi old r z hsub hdis hnull hold hbase hcap Cw hCw.le hrows
  have h := bridge_comparison_enlarge (fun r => adaptedMean P q r)
    (adaptedMean P q (n + 2 * (L : ℤ))) (adaptedMean P qPlus cap)
    (adaptedMean P q (n + 2 * (L : ℤ)))
    (fun r => (adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm r).posSemidef)
    (adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm _).posSemidef
    jStar cap (n + 2 * (L : ℤ)) (by omega) Cw Ct C K₀ (aspectRatio E)
    (Real.sqrt (‖m‖ * ‖m⁻¹‖)) (Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖)) γ
    hCw.le hCt.le hC.le hK₀ hCwC hCtC (one_le_aspectRatio_of_coarseEllipticityDagger hdag
      |>.trans' (by norm_num))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hγ.1 hb
  simpa only [Int.cast_add, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat,
    sub_add_eq_sub_sub, q, qPlus, cap] using h

end
end HCPolySupport.HighContrast.Annealed
