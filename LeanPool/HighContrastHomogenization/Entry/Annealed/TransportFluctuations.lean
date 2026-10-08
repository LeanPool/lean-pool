/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.TransportMeans

/-!
# High-contrast homogenization: Entry.Annealed.TransportFluctuations

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Fluctuation bounds for the two-grid transport

The fluctuation and Whitney estimates consumed by the two-grid transport
`p.two.grid.transport`.  Stationarity pays only the number of scale-`k` parents for their
joint history maximum; the averaged lattice row and the two Whitney row shapes are bounded
as Schatten moments, with the operator-norm, weighted-moment and finite-row inequalities
that let a single nonnegative envelope dominate every old-history generation.  The old bulk
family, the boundary rows above `k` and the root of the weighted moment are then paid by the
profile, after canceling the exact parent-cardinality and dimension factors, so the whole
old-history contribution keeps the printed terminal decay.
-/
open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter adaptedMean
  blockPosDef_annealedBlock blockSub coarseBlock gridRatio matSqrt measurable_translateCoeff
  normalizedBlock translateCoeff)
open HCPolySupport.HighContrast (adaptedCell adaptedCellTranslate standardCellCenter)
namespace HCPolySupport.HighContrast.Annealed
open MeasureTheory Geometry Multiscale Analysis
open scoped Matrix.Norms.L2Operator MatrixOrder Matrix
noncomputable section

/-- Stationarity pays only the number of scale-k parents for their joint history
maximum. Every parent keeps the same translation across all child generations. -/
theorem transport_parent_history_max (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (γ : ℝ) (_hγ : γ ∈ Set.Ico (0 : ℝ) 1)
      (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K
      S) (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (k : ℤ) (hk : (jStar : ℤ) ≤ k) {ι : Type*} (Z : Finset ι) (hZ : Z.Nonempty)
    (p : ι → Fin d → ℤ) :
    let q := explicitRoundedGrid jStar m
    let H := fun a : CoeffSpace d => ⨆ j ∈ Set.Icc (jStar : ℤ) k,
      (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((k : ℝ) - j)) *
        ⨆ y ∈ adaptedLatticeAtScale q j ∩ adaptedCell q k,
          blockOpNorm (normalizedFluctuation P q j k y a) ^ bigQ d γ
    (∀ a, 0 ≤ H a) ∧ Integrable (fun a => ⨆ z ∈ (Z : Set ι), H (translateCoeff (p z) a)) P ∧
      (∫ a, ⨆ z ∈ (Z : Set ι), H (translateCoeff (p z) a) ∂P) ≤
        (Z.card : ℝ) * fluctuationHistory P γ q jStar k := by
  intro q H
  have hq := isUnit_roundedGrid hj hm
  obtain ⟨z, hz⟩ := (transport_history_centers q hq k k le_rfl).2
  have hH0 (a : CoeffSpace d) : 0 ≤ H a := (mul_nonneg (by positivity) (pow_nonneg (norm_nonneg
    _) _)).trans (transport_history_pointwise P γ q hq jStar k k ⟨hk, le_rfl⟩ z hz a)
  have hH : Integrable H P := (bridge_fluctuationHistory_integrable d hd P γ E Ψ K S hstat hdag
    jStar hj m hm k hk).1
  have hmem (z : ι) (_hz : z ∈ Z) : MemLp (fun a => H (translateCoeff (p z) a)) (ENNReal.ofReal
    1) P := by
    have hmp : MeasurePreserving (translateCoeff (p z)) P P := ⟨measurable_translateCoeff _,
      hstat _⟩
    simpa only [ENNReal.ofReal_one] using! (memLp_one_iff_integrable.mpr
      hH).comp_measurePreserving hmp
  have he (z : ι) : (∫ a, H (translateCoeff (p z) a) ∂P) = fluctuationHistory P γ q jStar k := by
    have hi := integral_map (μ := P) (φ := translateCoeff (p z))
      (measurable_translateCoeff _).aemeasurable
      (f := H) (by rw [hstat]; exact hH.aestronglyMeasurable)
    rw [hstat] at hi; exact hi.symm
  obtain ⟨hint, hbound⟩ := transport_target_max_moment (by norm_num : (0 : ℝ) < 1) Z hZ
    (fun z a => H (translateCoeff (p z) a)) (fun _ _ => ae_of_all P fun _ => hH0 _) hmem
  simp only [Real.rpow_one] at hint hbound
  refine ⟨hH0, hint, ?_⟩
  simp only [he, Finset.sum_const, nsmul_eq_mul] at hbound
  exact hbound
/-- Averaging at the even moment bigQ, with the actual terminal mean as R,
then transport from the self normalization. Both the row-average bound and log-det loss
are consumed; the row may be empty. -/
theorem exists_transport_averaged_fluctuation (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (S : CoeffSpace d → ℝ) (_hP : IsProbabilityMeasure P),
      IsStationaryLaw P → IsUnitRangeLaw P → CoarseEllipticityDagger P γ E Ψ K S →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
      ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
      ∀ (m : Mat d), m.PosDef → ∀ (r t : ℤ), (jStar : ℤ) ≤ r → r ≤ t →
      ∀ (Z : Finset (Vec d)), (Z : Set (Vec d)) ⊆ adaptedLatticeAtScale (explicitRoundedGrid
        jStar m) r →
      ∀ (v : ℝ), 0 ≤ v →
      lqSchattenNorm P (bigQ d γ : ℝ) (fun a => ofFullBlockMat
        (∑ z ∈ Z, v • toFullBlockMat (normalizedFluctuation P (explicitRoundedGrid jStar m) r t
          z a))) ≤
        ((bigQ d γ : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2)) * (Real.sqrt (Z.card : ℝ) * v) *
          Real.exp (detIncrement P (explicitRoundedGrid jStar m) r t) *
          lqSchattenNorm P (bigQ d γ : ℝ) (normalizedFluctuationSelf P (explicitRoundedGrid
            jStar m) r) := by
  obtain ⟨Cs, hCs, havg⟩ := exists_transport_lattice_row_average d hd γ hγ
  refine ⟨Cs, hCs, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag jStar hj hsrc m hm r t hjr hrt Z hZ v hv
  let := hP
  let : NeZero d := ⟨by omega⟩
  let q := explicitRoundedGrid jStar m
  have hQ : 1 ≤ (bigQ d γ : ℝ) := by exact_mod_cast bigQ_pos d γ hγ
  have hRs : IsSymmetricBlockMat (adaptedMean P q t) := isSymmetricBlockMat_annealedBlock P _
  have hRp : Book.Ch02.BlockPosDef (adaptedMean P q t) := by
    have hpos := blockPosDef_annealedBlock (hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S
      hstat hdag jStar hj m hm t 0)
      (fun a => blockPosDef_coarseBlock_adapted q (isUnit_roundedGrid hj hm) t 0 a)
    simpa only [adaptedCellTranslate_zero] using! hpos
  have ha := havg P E Ψ K S hP hstat hunit hdag (bigQ d γ) (bigQ_two_le d γ hγ)
    (bigQ_even d γ) jStar hj hsrc m hm r hjr Z hZ (adaptedMean P q t) hRs hRp v hv
  have hcoeff : ((Z.card : ℝ) * v) *
      ((bigQ d γ : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) / (Z.card : ℝ) ^ ((1 : ℝ) / 2)) =
      ((bigQ d γ : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2)) * (Real.sqrt (Z.card : ℝ) * v) := by
    rw [← Real.sqrt_eq_rpow]
    calc
      _ = ((bigQ d γ : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2)) * v *
          ((Z.card : ℝ) / Real.sqrt (Z.card : ℝ)) := by ring
      _ = _ := by rw [Real.div_sqrt]; ring
  rw [hcoeff] at ha
  have hmem : SchattenMemLp P (bigQ d γ : ℝ) (normalizedFluctuationSelf P q r) :=
    bridge_fluctuation_memLqSchatten d hd P γ E Ψ K S hstat hdag jStar hj m hm r r 0
  have hmem' : SchattenMemLp P (bigQ d γ : ℝ) (fun a => normalizedBlock
      (blockSub (coarseBlock (adaptedCell q r) a) (adaptedMean P q r)) (adaptedMean P q r)) := by
    change SchattenMemLp P (bigQ d γ : ℝ) (fun a => normalizedBlock
      (blockSub (coarseBlock (adaptedCellTranslate q r 0) a) (adaptedMean P q r))
        (adaptedMean P q r)) at hmem
    simpa only [adaptedCellTranslate_zero] using hmem
  have ht := lqSchattenNorm_normalizedBlock_transport_le d hd P γ E Ψ K S hstat hdag
    jStar hj m hm r (t - r).toNat hjr hQ
    (fun a => blockSub (coarseBlock (adaptedCell q r) a) (adaptedMean P q r)) hmem'
  have hgap : r + ((t - r).toNat : ℤ) = t := by omega
  rw [hgap] at ht
  change _ ≤ _ * lqSchattenNorm P (bigQ d γ : ℝ) (normalizedFluctuationSelf P q r)
  have hmineq := mul_le_mul_of_nonneg_left ht (show 0 ≤
      ((bigQ d γ : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2)) * (Real.sqrt (Z.card : ℝ) * v) by positivity)
  have hfinal := ha.trans hmineq
  have hself : (fun a => normalizedBlock
      (blockSub (coarseBlock (adaptedCell q r) a) (adaptedMean P q r)) (adaptedMean P q r)) =
      normalizedFluctuationSelf P q r := by
    funext a
    change _ = normalizedBlock (blockSub (coarseBlock (adaptedCellTranslate q r 0) a)
      (adaptedMean P q r)) (adaptedMean P q r)
    rw [adaptedCellTranslate_zero]
  rw [hself] at hfinal; exact hfinal.trans_eq (by ring)
/-- The Whitney two-grid bound supplies both square-sum coefficients and the actual
infinite mass identity. All constants are chosen before the grids and target. -/
theorem exists_transport_whitney_coefficients (d : ℕ) (hd : 2 ≤ d)
    (K₀ : ℝ) (hK₀ : 1 ≤ K₀) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧ ∃ C : ℝ, 0 < C ∧
      ∀ K : ℝ, 1 < K → ∀ jStar : ℕ, 2 * d ≤ 3 ^ jStar →
      ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
      ∀ m mPlus : Mat d, m.PosDef → mPlus.PosDef →
      gridRatio (explicitRoundedGrid jStar m) (explicitRoundedGrid jStar mPlus) ≤ K₀ →
      ∀ (j : ℤ) (ell : ℕ), 1 ≤ ell →
      ∀ y ∈ adaptedLatticeAtScale (explicitRoundedGrid jStar mPlus) j,
        let W := adaptedCellTranslate (explicitRoundedGrid jStar mPlus) j y
        let q := explicitRoundedGrid jStar m
        let cap := j - (ell : ℤ)
        ∃ hfin : ∀ r : ℤ, r ≤ cap → (maximalAdaptedCellCenters W q cap r).Finite,
          let v := fun r => (volume (adaptedCell q r)).toReal / (volume W).toReal
          (∑' r : {r : ℤ // r ≤ cap}, ∑ _z ∈ (hfin r.1 r.2).toFinset, v r.1) = 1 ∧
          (∑ _z ∈ (hfin cap le_rfl).toFinset, (v cap) ^ 2) ^ ((1 : ℝ) / 2) ≤
            C * (3 : ℝ) ^ (-(d : ℝ) / 2 * (ell : ℝ)) ∧
          ∀ (r : ℤ) (hr : r < cap),
            (∑ _z ∈ (hfin r hr.le).toFinset, (v r) ^ 2) ^ ((1 : ℝ) / 2) ≤
              C * (3 : ℝ) ^ (-((d : ℝ) + 1) / 2 * ((j : ℝ) - r)) ∧
            (∑ _z ∈ (hfin r hr.le).toFinset, v r) ≤ C * (3 : ℝ) ^ ((r : ℝ) - j) := by
  obtain ⟨Cs, hCs, hwhitney⟩ := Entry.two_grid_whitney d hd
  obtain ⟨C₀, hC₀, hdata⟩ := hwhitney K₀ hK₀
  let C := C₀ * Real.sqrt C₀ + C₀ + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hC1 : C₀ * Real.sqrt C₀ ≤ C := by dsimp only [C]; linarith only [hC₀]
  have hC2 : C₀ ≤ C := by
    have hp := mul_nonneg hC₀.le (Real.sqrt_nonneg C₀)
    dsimp only [C]; linarith only [hp]
  refine ⟨Cs γ, hCs γ hγ, C, hC, ?_⟩
  intro K hK jStar hj hsrc m mPlus hm hmPlus hratio j ell hell y hy W q cap
  obtain ⟨hfin, _hsub, _hdis, _hnull, hvol, hcap, hcount, hmass, hrow⟩ := (hdata γ hγ K hK jStar
    hj hsrc m mPlus hm hmPlus hratio j ell hell).1 y hy
  refine ⟨hfin, ?_⟩
  intro v
  have hvol' (r : ℤ) (hr : r ≤ cap) :
      v r ≤ C₀ * (3 : ℝ) ^ (-((d : ℝ) * ((j : ℝ) - r))) := by
    change (volume (adaptedCell q r)).toReal / (volume W).toReal ≤ _
    simpa only [neg_mul] using (hvol r hr)
  refine ⟨hmass, ?_, ?_⟩
  · have hb := transport_row_square_sum_bound (hfin cap le_rfl).toFinset
      (a := (d : ℝ) * ((j : ℝ) - cap)) hC₀.le
      (show 0 ≤ v cap by dsimp only [v]; positivity) hcap
      (hvol' cap le_rfl)
    have hexp : ((d : ℝ) * (ell : ℝ)) / 2 - (d : ℝ) * ((j : ℝ) - cap) =
        -(d : ℝ) / 2 * (ell : ℝ) := by
      dsimp only [cap]; simp only [Int.cast_sub, Int.cast_natCast]; ring
    rw [hexp] at hb; exact hb.trans (mul_le_mul_of_nonneg_right hC1 (by positivity))
  · intro r hr
    have hb := transport_row_square_sum_bound (hfin r hr.le).toFinset
      (a := (d : ℝ) * ((j : ℝ) - r)) hC₀.le
      (show 0 ≤ v r by dsimp only [v]; positivity) (hcount r hr) (hvol' r hr.le)
    have hexp : (((d : ℝ) - 1) * ((j : ℝ) - r)) / 2 - (d : ℝ) * ((j : ℝ) - r) =
        -((d : ℝ) + 1) / 2 * ((j : ℝ) - r) := by ring
    rw [hexp] at hb; exact ⟨hb.trans (mul_le_mul_of_nonneg_right hC1 (by positivity)),
      (hrow r hr).trans (mul_le_mul_of_nonneg_right hC2 (by positivity))⟩
/-- Operator-norm transport is pointwise, so it can be used before any random maximum. -/
theorem transport_opNorm_normalizer {d : ℕ} {A B : BlockMat d}
    (hA : (toFullBlockMat A).PosDef) (hB : (toFullBlockMat B).PosDef) (X : BlockMat d) :
    blockOpNorm (normalizedBlock X B) ≤
      blockOpNorm (normalizedBlock A B) * blockOpNorm (normalizedBlock X A) := by
  rw [blockOpNorm, normalizedBlock_transport_congr hA hB X,
    ← transportMatrix_sq_opNorm_eq_general hA hB]
  let T := bridgeMap A B
  have ht : ‖Tᵀ‖ = ‖T‖ := by change ‖star T‖ = ‖T‖; exact norm_star T
  calc
    _ ≤ ‖Tᵀ * toFullBlockMat (normalizedBlock X A)‖ * ‖T‖ := norm_mul_le _ _
    _ ≤ (‖Tᵀ‖ * ‖toFullBlockMat (normalizedBlock X A)‖) * ‖T‖ := mul_le_mul_of_nonneg_right
      (norm_mul_le _ _) (norm_nonneg _)
    _ = _ := by rw [ht]; change _ = _ * ‖toFullBlockMat (normalizedBlock X A)‖; ring
/-- A positive finite row mass multiplies the maximum of its entry norms.
Only the fixed dimension converts its final operator norm to Schatten norm. -/
theorem transport_finite_row_bound {ι : Type*} {d : ℕ} (Z : Finset ι)
    {N A : ℝ} (hN : 1 ≤ N) (w : ι → ℝ) (hw : ∀ z ∈ Z, 0 ≤ w z)
    (X : ι → BlockMat d) (hX : ∀ z ∈ Z, (toFullBlockMat (X z)).IsHermitian)
    (hbound : ∀ z ∈ Z, blockOpNorm (X z) ≤ A) :
    absSchattenNorm N (ofFullBlockMat (∑ z ∈ Z, w z • toFullBlockMat (X z))) ≤
      (2 * (d : ℝ)) ^ N⁻¹ * (∑ z ∈ Z, w z) * A := by
  have hs : (toFullBlockMat (ofFullBlockMat (∑ z ∈ Z, w z • toFullBlockMat (X z)))).IsHermitian
    := by
    rw [toFullBlockMat_ofFullBlockMat]
    change (∑ z ∈ Z, w z • toFullBlockMat (X z)).conjTranspose = _
    rw [Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro z hz; rw [Matrix.conjTranspose_smul, (hX z hz).eq]; rfl
  have hn : ‖∑ z ∈ Z, w z • toFullBlockMat (X z)‖ ≤ (∑ z ∈ Z, w z) * A := by
    calc
      _ ≤ ∑ z ∈ Z, ‖w z • toFullBlockMat (X z)‖ := norm_sum_le _ _
      _ ≤ ∑ z ∈ Z, w z * A := by
        apply Finset.sum_le_sum
        intro z hz; rw [norm_smul, Real.norm_of_nonneg (hw z hz)]; exact
          mul_le_mul_of_nonneg_left (hbound z hz) (hw z hz)
      _ = _ := (Finset.sum_mul _ _ _).symm
  have h := absSchattenNorm_le_dim_rpow_mul_blockOpNorm hs hN
  rw [blockOpNorm, toFullBlockMat_ofFullBlockMat] at h; exact h.trans
    ((mul_le_mul_of_nonneg_left hn (by positivity)).trans_eq (by ring))
/-- Removing a positive geometric moment weight gives its reciprocal root.
This is used on each child before taking the parent maximum. -/
theorem transport_weighted_moment_root (Q : ℕ) (hQ : 0 < Q) {x H b : ℝ} (hx : 0 ≤ x) (hH : 0 ≤ H)
    (h : (3 : ℝ) ^ (-(Q : ℝ) * b) * x ^ Q ≤ H) :
    x ≤ (3 : ℝ) ^ b * H ^ (Q : ℝ)⁻¹ := by
  have hQr : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hpow : ((3 : ℝ) ^ b * H ^ (Q : ℝ)⁻¹) ^ (Q : ℝ) = (3 : ℝ) ^ ((Q : ℝ) * b) * H := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_mul hH, inv_mul_cancel₀ hQr.ne', Real.rpow_one, mul_comm b (Q : ℝ)]
  apply (Real.rpow_le_rpow_iff hx (by positivity) hQr).mp
  rw [hpow, Real.rpow_natCast]
  have hmul := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) ((Q :
    ℝ) * b))
  rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    show (Q : ℝ) * b + -(Q : ℝ) * b = 0 by ring, Real.rpow_zero, one_mul] at hmul
  exact hmul
/-- A single random envelope controls all old-history generations in the new
target. Its moment pays only the finite family of scale-k parents. -/
theorem transport_old_history_envelope (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ)
      (K : ℝ)
    (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K
      S) (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (qPlus : Mat d) (k t : ℤ) (hk : (jStar : ℤ) ≤ k) (hkt : k ≤ t) (h : ℕ)
    (hcover : adaptedCell qPlus t ⊆ adaptedCell (explicitRoundedGrid jStar m) (t + h)) :
    ∃ X : CoeffSpace d → ℝ, (∀ a, 0 ≤ X a) ∧ MemLp X (ENNReal.ofReal (bigQ d γ : ℝ)) P ∧
      (∫ a, X a ^ bigQ d γ ∂P) ≤ (3 : ℝ) ^ (d * ((t - k).toNat + h)) *
        fluctuationHistory P γ (explicitRoundedGrid jStar m) jStar k ∧
      ∀ r ∈ Set.Icc (jStar : ℤ) k, ∀ w : Fin d → ℤ,
        adaptedCellCenter (explicitRoundedGrid jStar m) r w ∈ adaptedCell qPlus t →
        ∀ a : CoeffSpace d,
          blockOpNorm (normalizedFluctuation P (explicitRoundedGrid jStar m) r k
            (adaptedCellCenter (explicitRoundedGrid jStar m) r w) a) ≤
          (3 : ℝ) ^ (rhoMax d γ * ((k : ℝ) - r)) * X a := by
  have hγ := hdag.g_mem
  classical
  let q := explicitRoundedGrid jStar m
  have hq := isUnit_roundedGrid hj hm
  have hparent := transport_old_parent_family q qPlus hq k t hkt h hcover
  let Z := hparent.1.toFinset
  have hcard : (Z.card : ℝ) = (3 : ℝ) ^ (d * ((t - k).toNat + h)) := by
    have he := hparent.2.1
    rw [Set.ncard_eq_toFinset_card _ hparent.1] at he
    exact_mod_cast he
  have hZ : Z.Nonempty := Finset.card_pos.mp (by
    have hc : (0 : ℝ) < Z.card := by rw [hcard]; positivity
    exact_mod_cast hc)
  choose p hp using fun v : Fin d → ℤ => transport_parent_fluctuation_shift d jStar m k hk v
  let H := fun a : CoeffSpace d => ⨆ j ∈ Set.Icc (jStar : ℤ) k,
    (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((k : ℝ) - j)) *
      ⨆ y ∈ adaptedLatticeAtScale q j ∩ adaptedCell q k,
        blockOpNorm (normalizedFluctuation P q j k y a) ^ bigQ d γ
  let F := fun a => ⨆ v ∈ (Z : Set (Fin d → ℤ)), H (translateCoeff (p v) a)
  let X := fun a => F a ^ (bigQ d γ : ℝ)⁻¹
  have hdata := transport_parent_history_max d hd P γ hγ E Ψ K S hstat hdag jStar hj m hm k hk Z
    hZ p
  have hH0 (a : CoeffSpace d) : 0 ≤ H a := hdata.1 a
  have hle (v : Fin d → ℤ) (hv : v ∈ Z) (a : CoeffSpace d) : H (translateCoeff (p v) a) ≤ F a := by
    change _ ≤ ⨆ v ∈ (Z : Set (Fin d → ℤ)), H (translateCoeff (p v) a)
    rw [iSup_mem_finset_eq_finset_sup Z hZ _ (fun v _ => hH0 (translateCoeff (p v) a))]
    exact Finset.le_sup' (fun v : Fin d → ℤ => H (translateCoeff (p v) a)) hv
  have hF0 (a : CoeffSpace d) : 0 ≤ F a := by
    obtain ⟨v, hv⟩ := hZ
    exact (hH0 _).trans (hle v hv a)
  have hFmem : Integrable F P := hdata.2.1
  have hQ := bigQ_real_pos d γ hγ
  have hXmem : MemLp X (ENNReal.ofReal (bigQ d γ : ℝ)) P := (weightedMax_root_memLp hQ
    (ae_of_all P hF0) hFmem).1
  refine ⟨X, (fun a => Real.rpow_nonneg (hF0 a) _), hXmem, ?_, ?_⟩
  · have he (a) : X a ^ bigQ d γ = F a := by
      dsimp only [X]; rw [← Real.rpow_natCast]; exact Real.rpow_inv_rpow (hF0 a) hQ.ne'
    have hi : (∫ a, X a ^ bigQ d γ ∂P) = ∫ a, F a ∂P := integral_congr_ae (ae_of_all P he)
    rw [hi, ← hcard]; exact hdata.2.2
  · intro r hr w hw a
    obtain ⟨v, hv, hsub⟩ := hparent.2.2 r hr.2 w hw
    have hvZ : v ∈ Z := hparent.1.mem_toFinset.mpr hv
    have hown : adaptedCellCenter q r w ∈ adaptedCellAtCenter q r w := by
      rw [adaptedCellAtCenter_eq_affine_standardCell]; exact ⟨standardCellCenter r w,
        Recurrence.standardCellCenter_mem_standardCell r w,
        (Recurrence.adaptedCellCenter_eq q r w).symm⟩
    obtain ⟨z, hz, hshift⟩ := hp v P r k hr.2 w (hsub hown)
    have hb := (transport_history_pointwise P γ q hq jStar k r hr z hz (translateCoeff (p v)
      a)).trans (hle v hvZ a)
    rw [← hshift a] at hb; exact transport_weighted_moment_root (bigQ d γ) (bigQ_pos d γ hγ)
      (norm_nonneg _) (hF0 a) (by simpa only [mul_assoc] using hb)
/-- The old-history norm comparison after taking the Q-th power, including
the exact d-dimensional parent-count exponent. -/
theorem transport_old_history_moment_factor (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 :
  ℝ) 1) (M : BlockMat d) (hM : (toFullBlockMat M).IsHermitian)
    (hIM : BlockMatLoewnerLE (Book.Ch02.blockIdentity d) M)
    (n k : ℤ) (hnk : k ≤ n) (L : ℕ) :
    (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((n : ℝ) + L - k)) *
        (3 : ℝ) ^ ((d : ℝ) * ((n : ℝ) + L - k)) * blockOpNorm M ^ bigQ d γ ≤
      (3 : ℝ) ^ ((1 - γ) / 4 * (L : ℝ)) *
        (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) + 2 * L - k)) * (1 + meanPenalty (bigQ d γ) M) := by
  have hQ := bigQ_real_pos d γ hγ
  have hbase : 0 ≤ 1 + meanPenalty (bigQ d γ) M := add_nonneg zero_le_one (meanPenalty_nonneg
    (bigQ d γ) M ((toFullBlockMat_isHermitian_iff _).1 hM) hIM)
  have hroot : ((1 + meanPenalty (bigQ d γ) M) ^ (bigQ d γ : ℝ)⁻¹) ^ bigQ d γ =
      1 + meanPenalty (bigQ d γ) M := by
    rw [← Real.rpow_natCast]; exact Real.rpow_inv_rpow hbase hQ.ne'
  have he (x : ℝ) : ((3 : ℝ) ^ x) ^ bigQ d γ = (3 : ℝ) ^ (x * (bigQ d γ : ℝ)) :=
    (Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3) x (bigQ d γ)).symm
  have hpow := pow_le_pow_left₀ (mul_nonneg (by positivity) (norm_nonneg _))
    (transport_old_history_factor d hd γ hγ M hM hIM n k hnk L) (bigQ d γ)
  have hleft : (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((n : ℝ) + L - k)) *
      (3 : ℝ) ^ ((d : ℝ) * ((n : ℝ) + L - k)) =
      ((3 : ℝ) ^ (-(rhoMax d γ - (d : ℝ) / (bigQ d γ : ℝ)) * ((n : ℝ) + L - k))) ^ bigQ d γ := by
    rw [he, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    field_simp [hQ.ne']
    ring
  rw [hleft, ← mul_pow]
  apply hpow.trans_eq
  rw [mul_pow, mul_pow, hroot, he, he]
  have he1 : ((1 - γ) / (4 * (bigQ d γ : ℝ)) * (L : ℝ)) * (bigQ d γ : ℝ) =
      (1 - γ) / 4 * (L : ℝ) := by field_simp [hQ.ne']
  have he2 : (-(1 - γ) / (4 * (bigQ d γ : ℝ)) * ((n : ℝ) + 2 * L - k)) * (bigQ d γ : ℝ) =
      -((1 - γ) / 4) * ((n : ℝ) + 2 * L - k) := by field_simp [hQ.ne']
  rw [he1, he2]
/-- Above k, target counting and averaging leave precisely the old profile
weight. Nonnegative gamma and the positive bulk decay exponent pay the rest. -/
theorem transport_bulk_high_weight (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (n j : ℤ) (L ell : ℕ) (hjt : j ≤ n + (L : ℤ)) :
    (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((n : ℝ) + L - j)) *
        (3 : ℝ) ^ ((d : ℝ) * ((n : ℝ) + L - j)) *
        ((3 : ℝ) ^ (-(d : ℝ) / 2 * (ell : ℝ))) ^ bigQ d γ ≤
      (3 : ℝ) ^ ((1 - γ) / 4 * (L : ℝ)) *
        (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) + 2 * L - ((j : ℝ) - ell))) := by
  have hQ := bigQ_real_pos d γ hγ
  have hs : 0 ≤ (n : ℝ) + L - j := by exact_mod_cast sub_nonneg.mpr hjt
  have hga : 0 ≤ (bigQ d γ : ℝ) * γ * ((n : ℝ) + L - j) := mul_nonneg (mul_nonneg hQ.le hγ.1) hs
  have hel : 0 ≤ (bigQ d γ : ℝ) *
      ((d : ℝ) / 2 - (1 - γ) / (4 * (bigQ d γ : ℝ))) * (ell : ℝ) :=
    mul_nonneg (mul_nonneg hQ.le (fluctuation_decay_exponent_pos d hd γ hγ).le) (Nat.cast_nonneg _)
  rw [transport_target_count_weight d hd γ hγ,
    ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
  simp only [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have he : ((1 - γ) / 4 * (L : ℝ) - ((1 - γ) / 4) * ((n : ℝ) + 2 * L - ((j : ℝ) - ell))) -
      (-(bigQ d γ : ℝ) * (γ + (1 - γ) / (4 * (bigQ d γ : ℝ))) * ((n : ℝ) + L - j) +
        (-(d : ℝ) / 2 * (ell : ℝ)) * (bigQ d γ : ℝ)) =
      (bigQ d γ : ℝ) * γ * ((n : ℝ) + L - j) + (bigQ d γ : ℝ) *
        ((d : ℝ) / 2 - (1 - γ) / (4 * (bigQ d γ : ℝ))) * (ell : ℝ) := by
    field_simp [hQ.ne']
    ring
  linarith only [he, hga, hel]
/-- Boundary averaging preserves a summable coefficient in the separation
of the target and source generations, after the exact target-count loss. -/
theorem transport_boundary_high_weight (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (n j r : ℤ) (L : ℕ) (hjt : j ≤ n + (L : ℤ)) :
    let β := ((d : ℝ) + 1) / 2 - (1 - γ) / (4 * (bigQ d γ : ℝ))
    (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((n : ℝ) + L - j)) *
        (3 : ℝ) ^ ((d : ℝ) * ((n : ℝ) + L - j)) *
        ((3 : ℝ) ^ (-((d : ℝ) + 1) / 2 * ((j : ℝ) - r))) ^ bigQ d γ ≤
      (3 : ℝ) ^ ((1 - γ) / 4 * (L : ℝ)) *
        ((3 : ℝ) ^ (-β * ((j : ℝ) - r))) ^ bigQ d γ *
        (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) + 2 * L - r)) := by
  intro β
  have hQ := bigQ_real_pos d γ hγ
  have hs : 0 ≤ (n : ℝ) + L - j := by exact_mod_cast sub_nonneg.mpr hjt
  have hg : 0 ≤ (bigQ d γ : ℝ) * γ * ((n : ℝ) + L - j) := mul_nonneg (mul_nonneg hQ.le hγ.1) hs
  rw [transport_target_count_weight d hd γ hγ]
  simp only [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have he : ((1 - γ) / 4 * (L : ℝ) + (-β * ((j : ℝ) - r)) * (bigQ d γ : ℝ) -
      ((1 - γ) / 4) * ((n : ℝ) + 2 * L - r)) -
      (-(bigQ d γ : ℝ) * (γ + (1 - γ) / (4 * (bigQ d γ : ℝ))) * ((n : ℝ) + L - j) +
      (-((d : ℝ) + 1) / 2 * ((j : ℝ) - r)) * (bigQ d γ : ℝ)) =
      (bigQ d γ : ℝ) * γ * ((n : ℝ) + L - j) := by
    dsimp only [β]
    field_simp [hQ.ne']
    ring
  linarith only [he, hg]
/-- The mixed norm at the fixed natural moment has the printed Bochner moment.
Membership records that this is an integrable random moment. -/
theorem transport_lq_moment {d Q : ℕ} {P : Measure (CoeffSpace d)}
    (hQ : 0 < Q) (H : CoeffSpace d → BlockMat d) (hH : SchattenMemLp P (Q : ℝ) H) :
    lqSchattenNorm P (Q : ℝ) H ^ Q = ∫ a, absSchattenNorm (Q : ℝ) (H a) ^ Q ∂P := by
  have hQ1 : 1 ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQr : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hpos : 0 ≤ ∫ a, absSchattenNorm (Q : ℝ) (H a) ^ Q ∂P := by
    apply integral_nonneg_of_ae
    filter_upwards [hH.symmetric] with a ha
    exact pow_nonneg (absSchattenNorm_nonneg ((toFullBlockMat_isHermitian_iff _).2 ha) hQ1) Q
  simp only [lqSchattenNorm, Real.rpow_natCast]
  rw [← Real.rpow_natCast]; exact Real.rpow_inv_rpow hpos hQr.ne'
/-- The averaging estimate gives the actual row moment, for both Whitney row shapes. -/
theorem exists_transport_lattice_row_moment (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (S : CoeffSpace d → ℝ) (_hP : IsProbabilityMeasure P),
      IsStationaryLaw P → IsUnitRangeLaw P → CoarseEllipticityDagger P γ E Ψ K S →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
      ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
      ∀ (m : Mat d), m.PosDef → ∀ (r t : ℤ), (jStar : ℤ) ≤ r → r ≤ t →
      ∀ (Z : Finset (Vec d)), (Z : Set (Vec d)) ⊆ adaptedLatticeAtScale (explicitRoundedGrid
        jStar m) r →
      ∀ (v : ℝ), 0 ≤ v →
      ∀ A : ℝ, (∑ _z ∈ Z, v ^ 2) ^ ((1 : ℝ) / 2) ≤ A →
      (∫ a, absSchattenNorm (bigQ d γ : ℝ) (ofFullBlockMat
        (∑ z ∈ Z, v • toFullBlockMat (normalizedFluctuation P (explicitRoundedGrid jStar m) r t
          z a))) ^ bigQ d γ ∂P) ≤
        ((bigQ d γ : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) * A) ^ bigQ d γ *
          Real.exp ((bigQ d γ : ℝ) * detIncrement P (explicitRoundedGrid jStar m) r t) *
          ∫ a, absSchattenNorm (bigQ d γ : ℝ)
            (normalizedFluctuationSelf P (explicitRoundedGrid jStar m) r a) ^ bigQ d γ ∂P := by
  obtain ⟨Cs, hCs, havg⟩ := exists_transport_averaged_fluctuation d hd γ hγ
  refine ⟨Cs, hCs, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag jStar hj hsrc m hm r t hjr hrt Z hZ v hv A hA
  let := hP
  let q := explicitRoundedGrid jStar m
  let R := fun a => ofFullBlockMat (∑ z ∈ Z, v • toFullBlockMat (normalizedFluctuation P q r t z a))
  have hQ := bigQ_pos d γ hγ
  have hQ1 : 1 ≤ (bigQ d γ : ℝ) := by exact_mod_cast hQ
  have hR : SchattenMemLp P (bigQ d γ : ℝ) R := memLqSchatten_normalizedCentered_sum d hd P γ E
    Ψ K S hstat hdag jStar hj m hm r
      (adaptedMean P q t) (bigQ d γ) hQ1 Z (fun _ => v) id
  have hV : SchattenMemLp P (bigQ d γ : ℝ) (normalizedFluctuationSelf P q r) :=
    bridge_fluctuation_memLqSchatten d hd P γ E Ψ K S hstat hdag jStar hj m hm r r 0
  have hcoef : Real.sqrt (Z.card : ℝ) * v ≤ A := by
    simpa only [← Real.sqrt_eq_rpow, Finset.sum_const, nsmul_eq_mul,
      Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hv] using hA
  have hn : lqSchattenNorm P (bigQ d γ : ℝ) R ≤
      ((bigQ d γ : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) * A) *
        Real.exp (detIncrement P q r t) * lqSchattenNorm P (bigQ d γ : ℝ)
          (normalizedFluctuationSelf P q r) := by
    apply (havg P E Ψ K S hP hstat hunit hdag jStar hj hsrc m hm r t hjr hrt Z hZ v hv).trans
    apply mul_le_mul_of_nonneg_right _ (hV.lqSchattenNorm_eq_eLpNorm_toReal hQ1).2.1
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_left hcoef (by positivity)
  have hp := pow_le_pow_left₀ (hR.lqSchattenNorm_eq_eLpNorm_toReal hQ1).2.1 hn (bigQ d γ)
  rw [transport_lq_moment hQ R hR, mul_pow, mul_pow,
    transport_lq_moment hQ (normalizedFluctuationSelf P q r) hV, ← Real.exp_nat_mul] at hp
  exact hp
/-- The old-history half of the bulk family retains one common envelope
under the joint maximum. Its exact coefficient is recorded before absorption. -/
theorem transport_old_bulk_raw (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
      (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K
      S) (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (qPlus : Mat d) (k n : ℤ) (hk : (jStar : ℤ) ≤ k) (hkn : k ≤ n) (L h : ℕ) (hcover :
      adaptedCell qPlus (n + L) ⊆ adaptedCell (explicitRoundedGrid jStar m) (n + L + h))
    {ι : Type*} (I : Finset ι) (hI : I.Nonempty) (j : ι → ℤ) (Z : ι → Finset (Vec d)) (v : ι → ℝ)
    (hjgen : ∀ i ∈ I, j i - 1 ∈ Set.Icc (jStar : ℤ) k)
    (hZ : ∀ i ∈ I, (Z i : Set (Vec d)) ⊆
      adaptedLatticeAtScale (explicitRoundedGrid jStar m) (j i - 1) ∩ adaptedCell qPlus (n + L))
    (hv : ∀ i ∈ I, 0 ≤ v i) (hmass : ∀ i ∈ I, ∑ _z ∈ Z i, v i ≤ 1) :
    let q := explicitRoundedGrid jStar m
    let Q := bigQ d γ
    let M := relMean P q k (n + 2 * (L : ℤ))
    let B := (2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ * (3 : ℝ) ^ (rhoMax d γ) *
      (3 : ℝ) ^ (-rhoMax d γ * ((n : ℝ) + L - k)) * blockOpNorm M
    (∫ a, (⨆ i ∈ (I : Set ι), (3 : ℝ) ^ (-rhoMax d γ * ((n : ℝ) + L - j i)) *
      absSchattenNorm (Q : ℝ) (ofFullBlockMat (∑ z ∈ Z i, v i • toFullBlockMat
        (normalizedFluctuation P q (j i - 1) (n + 2 * (L : ℤ)) z a)))) ^ (Q : ℝ) ∂P) ≤
      B ^ Q * ((3 : ℝ) ^ (d * ((n + (L : ℤ) - k).toNat + h)) * fluctuationHistory P γ q jStar k)
        := by
  intro q Q M B
  classical
  have hQ : 0 < (Q : ℝ) := bigQ_real_pos d γ hγ
  have hQ1 : 1 ≤ (Q : ℝ) := by exact_mod_cast bigQ_pos d γ hγ
  have hkt : k ≤ n + (L : ℤ) := by omega
  obtain ⟨X, hX0, hXmem, hXmoment, hXbound⟩ := transport_old_history_envelope d hd P γ E Ψ K S
    hstat hdag jStar hj m hm qPlus k (n + (L : ℤ)) hk hkt h hcover
  let R := fun i a => ofFullBlockMat (∑ z ∈ Z i, v i • toFullBlockMat
    (normalizedFluctuation P q (j i - 1) (n + 2 * (L : ℤ)) z a))
  let w := fun i => (3 : ℝ) ^ (-rhoMax d γ * ((n : ℝ) + L - j i))
  let f := fun i a => w i * absSchattenNorm (Q : ℝ) (R i a)
  have hR (i : ι) : SchattenMemLp P (Q : ℝ) (R i) := memLqSchatten_normalizedCentered_sum d hd P
    γ E Ψ K S hstat hdag jStar hj m hm
      (j i - 1) (adaptedMean P q (n + 2 * (L : ℤ))) Q hQ1 (Z i) (fun _ => v i) id
  have hf0 (i : ι) (_hi : i ∈ I) : ∀ᵐ a ∂P, 0 ≤ f i a :=
    (hR i).symmetric.mono fun _ ha => mul_nonneg (by dsimp only [w]; positivity)
      (absSchattenNorm_nonneg ((toFullBlockMat_isHermitian_iff _).2 ha) hQ1)
  have hf (i : ι) (_hi : i ∈ I) : MemLp (f i) (ENNReal.ofReal (Q : ℝ)) P := ((hR
    i).memLp_absSchattenNorm hQ1).const_mul (w i)
  have hAk := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm k
  have hAt := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm (n + 2 * (L : ℤ))
  have hMn : 0 ≤ blockOpNorm M := norm_nonneg _
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hfield (i : ι) (hi : i ∈ I) : ∀ᵐ a ∂P, f i a ≤ B * X a := by
    have hentry (z : Vec d) : SchattenMemLp P (Q : ℝ)
        (normalizedFluctuation P q (j i - 1) (n + 2 * (L : ℤ)) z) :=
      bridge_fluctuation_memLqSchatten d hd P γ E Ψ K S hstat hdag jStar hj m hm
        (j i - 1) (n + 2 * (L : ℤ)) z
    filter_upwards [(Filter.eventually_all_finset (Z i)).mpr (fun z _ => (hentry z).symmetric)]
      with a ha
    have hbound (z : Vec d) (hz : z ∈ Z i) :
        blockOpNorm (normalizedFluctuation P q (j i - 1) (n + 2 * (L : ℤ)) z a) ≤
          blockOpNorm M * ((3 : ℝ) ^ (rhoMax d γ * ((k : ℝ) - (j i - 1 : ℤ))) * X a) := by
      obtain ⟨u, hu⟩ := (hZ i hi hz).1
      have hx := hXbound (j i - 1) (hjgen i hi) u (hu.symm ▸ (hZ i hi hz).2) a
      rw [hu] at hx
      have hn : blockOpNorm (normalizedFluctuation P q (j i - 1) (n + 2 * (L : ℤ)) z a) ≤
          blockOpNorm M * blockOpNorm (normalizedFluctuation P q (j i - 1) k z a) :=
        transport_opNorm_normalizer hAk hAt (blockSub (coarseBlock (adaptedCellTranslate q (j i
          - 1) z) a) (adaptedMean P q (j i - 1)))
      exact hn.trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
    have hb := transport_finite_row_bound (Z i) hQ1 (fun _ => v i) (fun _ _ => hv i hi)
      (fun z => normalizedFluctuation P q (j i - 1) (n + 2 * (L : ℤ)) z a)
      (fun z hz => (toFullBlockMat_isHermitian_iff _).2 (ha z hz)) hbound
    have hcoef : 0 ≤ blockOpNorm M * ((3 : ℝ) ^ (rhoMax d γ * ((k : ℝ) - (j i - 1 : ℤ))) * X a)
      := mul_nonneg (norm_nonneg _) (mul_nonneg (by positivity) (hX0 a))
    have hmassbound := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hmass i hi) hcoef)
      (show 0 ≤ (2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ by positivity)
    simp only [one_mul] at hmassbound
    have hrow : absSchattenNorm (Q : ℝ) (R i a) ≤ (2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ *
        (blockOpNorm M * ((3 : ℝ) ^ (rhoMax d γ * ((k : ℝ) - (j i - 1 : ℤ))) * X a)) :=
      hb.trans (by simpa only [mul_assoc] using hmassbound)
    have he : w i * (3 : ℝ) ^ (rhoMax d γ * ((k : ℝ) - (j i - 1 : ℤ))) =
        (3 : ℝ) ^ (rhoMax d γ) * (3 : ℝ) ^ (-rhoMax d γ * ((n : ℝ) + L - k)) := by
      dsimp only [w]; simp only [← Real.rpow_add (by norm_num : (0 : ℝ) < 3), Int.cast_sub,
        Int.cast_one]
      congr 1; ring
    calc
      _ ≤ w i * ((2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ *
          (blockOpNorm M * ((3 : ℝ) ^ (rhoMax d γ * ((k : ℝ) - (j i - 1 : ℤ))) * X a))) :=
        mul_le_mul_of_nonneg_left hrow (by positivity)
      _ = ((2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ * blockOpNorm M) *
          (w i * (3 : ℝ) ^ (rhoMax d γ * ((k : ℝ) - (j i - 1 : ℤ)))) * X a := by ring
      _ = B * X a := by rw [he]; dsimp only [B]; ring
  have hb := (transport_joint_envelope_moment hQ hB I hI f hf0 hf X (ae_of_all P hX0) hXmem
    hfield).2
  simp only [Real.rpow_natCast] at hb
  simpa only [Real.rpow_natCast] using
    hb.trans (mul_le_mul_of_nonneg_left hXmoment (pow_nonneg hB Q))
/-- Exact cancellation of the root dimension factor and parent cardinality
against the old-history weight. The enlargement contributes only 3^(d*h). -/
theorem transport_old_bulk_mass_factor (d Q : ℕ) (hQ : 0 < Q) (ρ : ℝ)
    (s : ℤ) (hs : 0 ≤ s) (h : ℕ) (x : ℝ) :
    ((2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ * (3 : ℝ) ^ ρ * (3 : ℝ) ^ (-ρ * (s : ℝ)) * x) ^ Q *
        (3 : ℝ) ^ (d * (s.toNat + h)) =
      (2 * (d : ℝ)) * (3 : ℝ) ^ ((Q : ℝ) * ρ + (d : ℝ) * h) *
        ((3 : ℝ) ^ (-(Q : ℝ) * ρ * (s : ℝ)) * (3 : ℝ) ^ ((d : ℝ) * s) * x ^ Q) := by
  have hQr : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hdroot : ((2 * (d : ℝ)) ^ (Q : ℝ)⁻¹) ^ Q = 2 * (d : ℝ) := by
    rw [← Real.rpow_natCast]; exact Real.rpow_inv_rpow (by positivity) hQr.ne'
  have hp (a : ℝ) : ((3 : ℝ) ^ a) ^ Q = (3 : ℝ) ^ (a * (Q : ℝ)) := (Real.rpow_mul_natCast (by
    norm_num : (0 : ℝ) ≤ 3) a Q).symm
  have hsR : (s.toNat : ℝ) = (s : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hs
  have hc : (3 : ℝ) ^ (d * (s.toNat + h)) = (3 : ℝ) ^ ((d : ℝ) * ((s : ℝ) + h)) := by
    rw [← Real.rpow_natCast]
    congr 1; simp only [Nat.cast_mul, Nat.cast_add, hsR]
  have he : (3 : ℝ) ^ (ρ * (Q : ℝ)) * (3 : ℝ) ^ ((-ρ * (s : ℝ)) * (Q : ℝ)) *
      (3 : ℝ) ^ ((d : ℝ) * ((s : ℝ) + h)) =
      (3 : ℝ) ^ ((Q : ℝ) * ρ + (d : ℝ) * h) *
        ((3 : ℝ) ^ (-(Q : ℝ) * ρ * (s : ℝ)) * (3 : ℝ) ^ ((d : ℝ) * s)) := by
    simp only [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1; ring
  rw [mul_pow, mul_pow, mul_pow, hdroot, hp, hp, hc]
  calc
    _ = (2 * (d : ℝ)) * ((3 : ℝ) ^ (ρ * (Q : ℝ)) *
        (3 : ℝ) ^ ((-ρ * (s : ℝ)) * (Q : ℝ)) * (3 : ℝ) ^ ((d : ℝ) * ((s : ℝ) + h))) * x ^ Q :=
          by ring
    _ = _ := by rw [he]; ring
/-- The powered old-history factor is paid by the first profile component.
The constant records the fixed enlargement of the parent family. -/
theorem transport_old_history_profile_payment (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ)
      (K : ℝ)
    (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K
      S) (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (k n : ℤ) (hk : (jStar : ℤ) ≤ k) (hkn : k ≤ n) (L h : ℕ) :
    let q := explicitRoundedGrid jStar m
    let Q := bigQ d γ
    let M := relMean P q k (n + 2 * (L : ℤ))
    let B := (2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ * (3 : ℝ) ^ (rhoMax d γ) *
      (3 : ℝ) ^ (-rhoMax d γ * ((n : ℝ) + L - k)) * blockOpNorm M
    B ^ Q * ((3 : ℝ) ^ (d * ((n + (L : ℤ) - k).toNat + h)) * fluctuationHistory P γ q jStar k) ≤
      ((2 * (d : ℝ)) * (3 : ℝ) ^ ((Q : ℝ) * rhoMax d γ + (d : ℝ) * h)) *
        (3 : ℝ) ^ ((1 - γ) / 4 * (L : ℝ)) * profile P γ q jStar k (n + 2 * (L : ℤ)) := by
  intro q Q M B
  have hγ := hdag.g_mem
  let C := (2 * (d : ℝ)) * (3 : ℝ) ^ ((Q : ℝ) * rhoMax d γ + (d : ℝ) * h)
  have hAk := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm k
  have hAt := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm (n + 2 * (L : ℤ))
  have hS := matSqrt_inv_posDef_full hAt
  have hSEq : (matSqrt (toFullBlockMat (adaptedMean P q (n + 2 * (L : ℤ))))⁻¹).conjTranspose =
      matSqrt (toFullBlockMat (adaptedMean P q (n + 2 * (L : ℤ))))⁻¹ := hS.isHermitian.eq
  have hMH : (toFullBlockMat M).IsHermitian := by
    change (toFullBlockMat (normalizedBlock (adaptedMean P q k)
      (adaptedMean P q (n + 2 * (L : ℤ))))).IsHermitian
    simpa only [normalizedBlock, toFullBlockMat_ofFullBlockMat, hSEq] using
      (hAk.posSemidef.conjTranspose_mul_mul_same
        (matSqrt (toFullBlockMat (adaptedMean P q (n + 2 * (L : ℤ))))⁻¹)).isHermitian
  have hIM := (adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag jStar hj m hm
    k (n + 2 * (L : ℤ)) hk (by omega)).1
  have hp := transport_old_history_moment_factor d hd γ hγ M hMH hIM n k hkn L
  have hpay := (transport_profile_components d hd P γ E Ψ K S hstat hdag jStar hj m hm
    k (n + 2 * (L : ℤ)) hk (by omega)).1
  simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] at hpay
  have hfluc := (bridge_fluctuationHistory_integrable d hd P γ E Ψ K S hstat hdag jStar hj m hm
    k hk).2
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have he := transport_old_bulk_mass_factor d Q (bigQ_pos d γ hγ) (rhoMax d γ) (n + (L : ℤ) - k)
    (by omega) h (blockOpNorm M)
  simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast] at he
  calc
    B ^ Q * ((3 : ℝ) ^ (d * ((n + (L : ℤ) - k).toNat + h)) * fluctuationHistory P γ q jStar k) =
      (B ^ Q * (3 : ℝ) ^ (d * ((n + (L : ℤ) - k).toNat + h))) *
        fluctuationHistory P γ q jStar k := by ring
    _ = (C * ((3 : ℝ) ^ (-(Q : ℝ) * rhoMax d γ * ((n : ℝ) + L - k)) *
        (3 : ℝ) ^ ((d : ℝ) * ((n : ℝ) + L - k)) * blockOpNorm M ^ Q)) *
        fluctuationHistory P γ q jStar k := by rw [he]
    _ ≤ (C * ((3 : ℝ) ^ ((1 - γ) / 4 * (L : ℝ)) *
        (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) + 2 * L - k)) * (1 + meanPenalty Q M))) *
        fluctuationHistory P γ q jStar k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC) hfluc
    _ = (C * (3 : ℝ) ^ ((1 - γ) / 4 * (L : ℝ))) *
        ((3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) + 2 * L - k)) *
          (1 + meanPenalty Q M) * fluctuationHistory P γ q jStar k) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpay (mul_nonneg hC (by positivity))
/-- The old bulk family is paid by the first summand of the actual profile. -/
theorem transport_old_bulk_profile_bound (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
      (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K
      S) (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (qPlus : Mat d) (k n : ℤ) (hk : (jStar : ℤ) ≤ k) (hkn : k ≤ n) (L h : ℕ) (hcover :
      adaptedCell qPlus (n + L) ⊆ adaptedCell (explicitRoundedGrid jStar m) (n + L + h))
    {ι : Type*} (I : Finset ι) (hI : I.Nonempty) (j : ι → ℤ) (Z : ι → Finset (Vec d)) (v : ι → ℝ)
    (hjgen : ∀ i ∈ I, j i - 1 ∈ Set.Icc (jStar : ℤ) k)
    (hZ : ∀ i ∈ I, (Z i : Set (Vec d)) ⊆
      adaptedLatticeAtScale (explicitRoundedGrid jStar m) (j i - 1) ∩ adaptedCell qPlus (n + L))
    (hv : ∀ i ∈ I, 0 ≤ v i) (hmass : ∀ i ∈ I, ∑ _z ∈ Z i, v i ≤ 1) :
    let q := explicitRoundedGrid jStar m
    let Q := bigQ d γ
    (∫ a, (⨆ i ∈ (I : Set ι), (3 : ℝ) ^ (-rhoMax d γ * ((n : ℝ) + L - j i)) *
      absSchattenNorm (Q : ℝ) (ofFullBlockMat (∑ z ∈ Z i, v i • toFullBlockMat
        (normalizedFluctuation P q (j i - 1) (n + 2 * (L : ℤ)) z a)))) ^ (Q : ℝ) ∂P) ≤
      ((2 * (d : ℝ)) * (3 : ℝ) ^ ((Q : ℝ) * rhoMax d γ + (d : ℝ) * h)) *
        (3 : ℝ) ^ ((1 - γ) / 4 * (L : ℝ)) * profile P γ q jStar k (n + 2 * (L : ℤ)) := by
  intro q Q
  exact (transport_old_bulk_raw d hd P γ hγ E Ψ K S hstat hdag jStar hj m hm qPlus k n hk hkn L h
    hcover I hI j Z v hjgen hZ hv hmass).trans
      (transport_old_history_profile_payment d hd P γ E Ψ K S hstat hdag jStar hj m hm k n hk
        hkn L h)
/-- The boundary rows above k are paid by the final profile sum. Weighted
convexity is applied before exchanging the target and source generations. -/
theorem exists_transport_high_boundary_profile (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (S : CoeffSpace d → ℝ) (_hP : IsProbabilityMeasure P),
      IsStationaryLaw P → IsUnitRangeLaw P → CoarseEllipticityDagger P γ E Ψ K S →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
      ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
      ∀ (m : Mat d), m.PosDef → ∀ (k n : ℤ), (jStar : ℤ) ≤ k → k ≤ n →
      ∀ (L : ℕ) (D : ℝ), 0 ≤ D →
      let q := explicitRoundedGrid jStar m
      let Q := bigQ d γ
      let β := ((d : ℝ) + 1) / 2 - (1 - γ) / (4 * (Q : ℝ))
      let M := 1 + 1 / (1 - (3 : ℝ) ^ (-β))
      ∀ (I : Finset (ℤ × (Fin d → ℤ))), I.Nonempty → ∀ (T : ℤ → Finset ℤ),
      ∀ (Z : ℤ × (Fin d → ℤ) → ℤ → Finset (Vec d)) (v : ℤ × (Fin d → ℤ) → ℤ → ℝ),
      (∀ j ∈ I.image Prod.fst, T j ⊆ Finset.Icc (k + 1) j) →
      (∀ i ∈ I, i.1 ≤ n + (L : ℤ)) →
      (∀ j ∈ I.image Prod.fst, ((I.filter (fun i => i.1 = j)).card : ℝ) ≤
        (3 : ℝ) ^ ((d : ℝ) * ((n : ℝ) + L - j))) →
      (∀ i ∈ I, ∀ r ∈ T i.1, (Z i r : Set (Vec d)) ⊆ adaptedLatticeAtScale q r) →
      (∀ i ∈ I, ∀ r ∈ T i.1, 0 ≤ v i r) →
      (∀ i ∈ I, ∀ r ∈ T i.1, (∑ _z ∈ Z i r, v i r ^ 2) ^ ((1 : ℝ) / 2) ≤
        D * (3 : ℝ) ^ (-((d : ℝ) + 1) / 2 * ((i.1 : ℝ) - r))) →
      (∫ a, (⨆ i ∈ (I : Set (ℤ × (Fin d → ℤ))),
        (3 : ℝ) ^ (-rhoMax d γ * ((n : ℝ) + L - i.1)) *
          ∑ r ∈ T i.1, absSchattenNorm (Q : ℝ) (ofFullBlockMat (∑ z ∈ Z i r, v i r •
            toFullBlockMat (normalizedFluctuation P q r (n + 2 * (L : ℤ)) z a)))) ^ (Q : ℝ) ∂P) ≤
        M ^ (Q + 1) * ((Q : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) * D) ^ Q *
          (3 : ℝ) ^ ((1 - γ) / 4 * (L : ℝ)) * profile P γ q jStar k (n + 2 * (L : ℤ)) := by
  classical
  obtain ⟨Cs, hCs, hrow⟩ := exists_transport_lattice_row_moment d hd γ hγ
  refine ⟨Cs, hCs, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag jStar hj hsrc m hm k n hk hkn L D hD
    q Q β M I hI T Z v hT hjt hcount hZ hv hcoef
  let := hP
  let t := n + 2 * (L : ℤ)
  let A := ((Q : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) * D) ^ Q
  let c := (3 : ℝ) ^ ((1 - γ) / 4 * (L : ℝ))
  let w := fun j : ℤ => (3 : ℝ) ^ (-rhoMax d γ * ((n : ℝ) + L - j))
  let θ := fun j r : ℤ => (3 : ℝ) ^ (-β * ((j : ℝ) - r))
  let b := fun j r : ℤ => (3 : ℝ) ^ (-((d : ℝ) + 1) / 2 * ((j : ℝ) - r))
  let R := fun i r a => ofFullBlockMat (∑ z ∈ Z i r, v i r •
    toFullBlockMat (normalizedFluctuation P q r t z a))
  let f := fun i a => w i.1 * ∑ r ∈ T i.1, absSchattenNorm (Q : ℝ) (R i r a)
  let V := fun r : ℤ => Real.exp ((Q : ℝ) * detIncrement P q r t) *
    ∫ a, absSchattenNorm (Q : ℝ) (normalizedFluctuationSelf P q r a) ^ Q ∂P
  let F := fun r : ℤ => (3 : ℝ) ^ (-((1 - γ) / 4) * ((t : ℝ) - r)) * V r
  let B := fun j : ℤ => ∑ r ∈ T j, (θ j r * (θ j r)⁻¹ ^ Q) * (b j r ^ Q * V r)
  have hQ := bigQ_pos d γ hγ
  have hQr := bigQ_real_pos d γ hγ
  have hQ1 : 1 ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hβ : 0 < β := transport_boundary_decay_pos d hd γ hγ
  have hgeo : 0 < 1 / (1 - (3 : ℝ) ^ (-β)) := one_div_pos.mpr (transport_geometric_Icc β hβ 0 0).1
  have hM : 1 ≤ M := by dsimp only [M]; linarith only [hgeo]
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hθ (j r) : 0 < θ j r := by dsimp only [θ]; positivity
  have himage : ∀ i ∈ I, i.1 ∈ I.image Prod.fst := fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hR (i r) : SchattenMemLp P (Q : ℝ) (R i r) := memLqSchatten_normalizedCentered_sum d hd P
    γ E Ψ K S hstat hdag jStar hj m hm
      r (adaptedMean P q t) Q hQ1 (Z i r) (fun _ => v i r) id
  have hR0 (i r) : ∀ᵐ a ∂P, 0 ≤ absSchattenNorm (Q : ℝ) (R i r a) :=
    (hR i r).symmetric.mono fun _ ha => absSchattenNorm_nonneg ((toFullBlockMat_isHermitian_iff
      _).2 ha) hQ1
  have hm0 (r) : 0 ≤ ∫ a, absSchattenNorm (Q : ℝ) (normalizedFluctuationSelf P q r a) ^ Q ∂P := by
    have hmem := bridge_fluctuation_memLqSchatten d hd P γ E Ψ K S hstat hdag jStar hj m hm r r 0
    apply integral_nonneg_of_ae
    filter_upwards [hmem.symmetric] with a ha
    exact pow_nonneg (absSchattenNorm_nonneg ((toFullBlockMat_isHermitian_iff _).2 ha) hQ1) Q
  have hV (r) : 0 ≤ V r := mul_nonneg (Real.exp_pos _).le (hm0 r)
  have hF (r) : 0 ≤ F r := mul_nonneg (by positivity) (hV r)
  have hB (j) : 0 ≤ B j := Finset.sum_nonneg fun r _ =>
    mul_nonneg (mul_nonneg (hθ j r).le (pow_nonneg (inv_nonneg.mpr (hθ j r).le) Q)) (mul_nonneg
      (by dsimp only [b]; positivity) (hV r))
  have hf0 (i) (_hi : i ∈ I) : ∀ᵐ a ∂P, 0 ≤ f i a := by
    filter_upwards [(Filter.eventually_all_finset (T i.1)).mpr (fun r _ => hR0 i r)] with a ha
    exact mul_nonneg (by dsimp only [w]; positivity) (Finset.sum_nonneg ha)
  have hf (i) (_hi : i ∈ I) : MemLp (f i) (ENNReal.ofReal (Q : ℝ)) P :=
    (memLp_finsetSum (T i.1) (fun r _ => (hR i r).memLp_absSchattenNorm hQ1)).const_mul (w i.1)
  have hmass (j) (hjmem : j ∈ I.image Prod.fst) : ∑ r ∈ T j, θ j r ≤ M := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (hT j hjmem) (fun _ _ _ => (hθ _ _).le)).trans
    exact (transport_geometric_Icc β hβ (k + 1) j).2.trans (by dsimp only [M]; linarith only [])
  have hmom (i) (hi : i ∈ I) : (∫ a, f i a ^ (Q : ℝ) ∂P) ≤ w i.1 ^ Q * (M ^ Q * A * B i.1) := by
    have hh := (transport_weighted_moment_sum Q hQ (T i.1) (θ i.1) (fun r _ => hθ i.1 r)
      (fun r a => absSchattenNorm (Q : ℝ) (R i r a)) (fun r _ => hR0 i r)
      (fun r _ => (hR i r).memLp_absSchattenNorm hQ1) hM (hmass i.1 (himage i hi))).2
    have hb (r) (hr : r ∈ T i.1) : (∫ a, absSchattenNorm (Q : ℝ) (R i r a) ^ Q ∂P) ≤ A * (b i.1
      r ^ Q * V r) := by
      have hrng := Finset.mem_Icc.mp (hT i.1 (himage i hi) hr)
      have hr_lower : (jStar : ℤ) ≤ r := by omega
      have hr_upper : r ≤ t := by
        dsimp only [t]
        have hi_upper := hjt i hi
        omega
      have hh := hrow P E Ψ K S hP hstat hunit hdag jStar hj hsrc m hm r t hr_lower hr_upper
        (Z i r) (hZ i hi r hr) (v i r) (hv i hi r hr) (D * b i.1 r)
        (hcoef i hi r hr)
      apply hh.trans_eq
      dsimp only [A, V]
      rw [show (Q : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) * (D * b i.1 r) =
        ((Q : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) * D) * b i.1 r by ring, mul_pow]
      ring
    have hpow : (f i) ^ (Q : ℝ) =
        fun a : CoeffSpace d => w i.1 ^ Q *
          (∑ r ∈ T i.1, absSchattenNorm (Q : ℝ) (R i r a)) ^ Q := by
      funext a
      simp only [Pi.pow_apply, f, Real.rpow_natCast, mul_pow]
    have hmoment : (∫ a, f i a ^ (Q : ℝ) ∂P) =
        w i.1 ^ Q * ∫ a,
          (∑ r ∈ T i.1, absSchattenNorm (Q : ℝ) (R i r a)) ^ Q ∂P := by
      calc
        _ = ∫ a, ((f i) ^ (Q : ℝ)) a ∂P := by simp only [Pi.pow_apply]
        _ = ∫ a, w i.1 ^ Q *
            (∑ r ∈ T i.1, absSchattenNorm (Q : ℝ) (R i r a)) ^ Q ∂P := by rw [hpow]
        _ = _ := integral_const_mul (w i.1 ^ Q)
          (fun a : CoeffSpace d => (∑ r ∈ T i.1, absSchattenNorm (Q : ℝ) (R i r a)) ^ Q)
    rw [hmoment]
    apply mul_le_mul_of_nonneg_left _ (by dsimp only [w]; positivity)
    apply hh.trans
    calc
      _ ≤ M ^ Q * ∑ r ∈ T i.1, (θ i.1 r * (θ i.1 r)⁻¹ ^ Q) * (A * (b i.1 r ^ Q * V r)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans hM) Q)
        exact Finset.sum_le_sum fun r hr => mul_le_mul_of_nonneg_left (hb r hr) (by positivity)
      _ = _ := by
        dsimp only [B]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
  have hscale (j) (hjmem : j ∈ I.image Prod.fst) :
      w j ^ Q * (3 : ℝ) ^ ((d : ℝ) * ((n : ℝ) + L - j)) * B j ≤ c * ∑ r ∈ T j, θ j r * F r := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hjmem
    dsimp only [B]; rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    have hb := transport_boundary_high_weight d hd γ hγ n i.1 r L (hjt i hi)
    have hw : w i.1 ^ Q = (3 : ℝ) ^ (-(Q : ℝ) * rhoMax d γ * ((n : ℝ) + L - i.1)) := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]; congr 1; ring
    have he : (θ i.1 r)⁻¹ ^ Q * θ i.1 r ^ Q = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ (hθ i.1 r).ne', one_pow]
    have hp := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (hV r)) (mul_nonneg (hθ
      i.1 r).le (pow_nonneg (inv_nonneg.mpr (hθ i.1 r).le) Q))
    calc
      _ = (θ i.1 r * (θ i.1 r)⁻¹ ^ Q) *
          (((3 : ℝ) ^ (-(Q : ℝ) * rhoMax d γ * ((n : ℝ) + L - i.1)) *
          (3 : ℝ) ^ ((d : ℝ) * ((n : ℝ) + L - i.1)) * b i.1 r ^ Q) * V r) := by rw [hw]; ring
      _ ≤ _ := hp
      _ = c * (θ i.1 r * F r) := by
        dsimp only [F, c]; simp only [t, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
          Int.cast_natCast]
        calc
          _ = (3 : ℝ) ^ ((1 - γ) / 4 * (L : ℝ)) * θ i.1 r *
              ((θ i.1 r)⁻¹ ^ Q * θ i.1 r ^ Q) *
              ((3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) + 2 * L - r)) * V r) := by ring
          _ = _ := by rw [he]; ring
  have hconv : (∑ j ∈ I.image Prod.fst, ∑ r ∈ T j, θ j r * F r) ≤
      M * ∑ r ∈ Finset.Icc (k + 1) t, F r := by
    have hh := transport_geometric_convolution β hβ (I.image Prod.fst) (Finset.Icc (k + 1) t)
      T (n + (L : ℤ)) (by
        intro j hjmem
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hjmem
        exact hjt i hi)
      (by
        intro j hjmem r hr
        have hrng := Finset.mem_Icc.mp (hT j hjmem hr)
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hjmem
        exact Finset.mem_Icc.mpr ⟨hrng.1, by have ht := hjt i hi; omega⟩)
      (fun j hjmem r hr => (Finset.mem_Icc.mp (hT j hjmem hr)).2) F (fun r _ => hF r)
    exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp only [M]; linarith only [])
      (Finset.sum_nonneg fun r _ => hF r))
  have hpay : (∑ r ∈ Finset.Icc (k + 1) t, F r) ≤ profile P γ q jStar k t := by
    simpa only [F, V, mul_assoc] using
      (transport_profile_components d hd P γ E Ψ K S hstat hdag jStar hj m hm k t hk (by
        omega)).2.2.2
  calc
    _ ≤ ∑ i ∈ I, ∫ a, f i a ^ (Q : ℝ) ∂P := (transport_target_max_moment hQr I hI f hf0 hf).2
    _ ≤ ∑ i ∈ I, w i.1 ^ Q * (M ^ Q * A * B i.1) := Finset.sum_le_sum hmom
    _ = ∑ j ∈ I.image Prod.fst, ((I.filter (fun i => i.1 = j)).card : ℝ) *
        (w j ^ Q * (M ^ Q * A * B j)) := by
      rw [← Finset.sum_fiberwise_of_maps_to himage (fun i : ℤ × (Fin d → ℤ) => w i.1 ^ Q * (M ^
        Q * A * B i.1))]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2]),
        Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ I.image Prod.fst, M ^ Q * A * (c * ∑ r ∈ T j, θ j r * F r) := by
      apply Finset.sum_le_sum
      intro j hjmem
      calc
        _ ≤ (3 : ℝ) ^ ((d : ℝ) * ((n : ℝ) + L - j)) * (w j ^ Q * (M ^ Q * A * B j)) :=
          mul_le_mul_of_nonneg_right (hcount j hjmem)
            (mul_nonneg (by dsimp only [w]; positivity) (mul_nonneg (by positivity) (hB j)))
        _ = (M ^ Q * A) * (w j ^ Q * (3 : ℝ) ^ ((d : ℝ) * ((n : ℝ) + L - j)) * B j) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hscale j hjmem) (by positivity)
    _ = M ^ Q * A * c * ∑ j ∈ I.image Prod.fst, ∑ r ∈ T j, θ j r * F r := by
      simp only [mul_assoc, ← Finset.mul_sum]
    _ ≤ M ^ Q * A * c * (M * ∑ r ∈ Finset.Icc (k + 1) t, F r) := mul_le_mul_of_nonneg_left hconv
      (by positivity)
    _ ≤ M ^ Q * A * c * (M * profile P γ q jStar k t) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hpay (zero_le_one.trans hM)) (by positivity)
    _ = _ := by rw [pow_succ]; ring

end
end HCPolySupport.HighContrast.Annealed
