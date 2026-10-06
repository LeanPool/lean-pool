/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.TransportProfile

/-!
# High-contrast homogenization: Entry.Annealed.TransportDrift

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Geometric drift weights for the two-grid transport

The drift estimates that the source and boundary corrections of the two-grid transport
`p.two.grid.transport` consume: the boundary mean loses only the quarter-`(1 - γ)` power in
the generation distance; the geometric convolutions of the fine source and of the comparison
error have bounded mass; the early and fine weight sums keep the printed terminal decay; and
the asymmetric profile bracket absorbs each source amplitude.  One nonnegative source field,
with `L^Q` norm and `Q`-th moment bounded independently of the law, the geometry and the
generation choices, dominates the actual Whitney rows; the bulk fluctuations and the
fluctuation history are reindexed as a single finite joint maximum over paired generations
and centres, and the centered and mean reductions of the Whitney estimate are discharged with
the source, positivity, series and moment guards.
-/
open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter adaptedMean aspectRatio
  aspectRatio_nonneg blockPosDef_annealedBlock blockScale blockSub coarseBlock gridRatio
  isSymmetricBlockMat_coarseBlockMatrix normalizedBlock)
open HCPolySupport.HighContrast (adaptedCell adaptedCellTranslate aspectRatio_nonneg
  centeredCube standardCellCenter)
namespace HCPolySupport.HighContrast.Annealed
open MeasureTheory Geometry Multiscale Analysis
open scoped Matrix.Norms.L2Operator MatrixOrder Matrix
noncomputable section

/-- The actual boundary mean sum has only the quarter-(1-gamma) loss in L. -/
theorem transport_boundary_mean_bound (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
      (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K
      S) (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (k n : ℤ) (hk : (jStar : ℤ) ≤ k) (hkn : k ≤ n) (L : ℕ) (hL : 1 ≤ L) :
    let q := explicitRoundedGrid jStar m
    let ell := fun j : ℤ => if j ≤ k + (L : ℤ) then 1 else L
    (∑ j ∈ Finset.Icc ((jStar : ℤ) + L) (n + L),
      (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) + L - 1 - j)) *
        ∑ r ∈ Finset.Icc (jStar : ℤ) (j - (ell j : ℤ) - 1),
          (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - r)) *
            meanPenalty (bigQ d γ) (relMean P q r (n + 2 * (L : ℤ)))) ≤
      ((1 / (1 - (3 : ℝ) ^ (-((3 : ℝ) / 4 * (1 - γ))))) *
        (2 + 1 / (1 - (3 : ℝ) ^ (-((1 - γ) / 4))))) *
          (3 : ℝ) ^ ((1 - γ) / 4 * (L : ℝ)) * profile P γ q jStar k (n + 2 * (L : ℤ)) := by
  intro q ell
  let t := n + 2 * (L : ℤ)
  let J := Finset.Icc ((jStar : ℤ) + L) (n + L)
  let U := Finset.Ico (jStar : ℤ) t
  let T := fun j : ℤ => Finset.Icc (jStar : ℤ) (j - (ell j : ℤ) - 1)
  let β := (3 : ℝ) / 4 * (1 - γ)
  let D := (3 : ℝ) ^ ((1 - γ) / 4 * (L : ℝ))
  let p := fun r : ℤ => meanPenalty (bigQ d γ) (relMean P q r t)
  let F := fun r : ℤ => (3 : ℝ) ^ (-((1 - γ) / 4) * ((t : ℝ) - 1 - r)) * p r
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hβ : 0 < β := by dsimp only [β]; linarith only [hγ.2]
  have hG : 0 < 1 / (1 - (3 : ℝ) ^ (-β)) := one_div_pos.mpr (transport_geometric_Icc β hβ 0 0).1
  have hF (r) (hr : r ∈ U) : 0 ≤ F r := mul_nonneg (by positivity)
    (adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag jStar hj m hm r t
      (Finset.mem_Ico.mp hr).1 (Finset.mem_Ico.mp hr).2.le).2.2.2.2.2
  have htj (j : ℤ) (r : ℤ) (hr : r ∈ T j) : r ≤ j := by
    have hh := (Finset.mem_Icc.mp hr).2
    omega
  have hTU (j : ℤ) (hjmem : j ∈ J) : T j ⊆ U := by
    intro r hr
    have hh := Finset.mem_Icc.mp hr
    have hjt := (Finset.mem_Icc.mp hjmem).2
    change r ∈ Finset.Ico (jStar : ℤ) t
    exact Finset.mem_Ico.mpr ⟨hh.1, by dsimp only [t]; omega⟩
  have hconv := transport_geometric_convolution β hβ J U T (n + (L : ℤ))
    (fun j hjmem => (Finset.mem_Icc.mp hjmem).2) hTU (fun j _ r hr => htj j r hr) F hF
  have he (j r : ℤ) : (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) + L - 1 - j)) *
      ((3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - r)) * p r) = D * ((3 : ℝ) ^ (-β * ((j : ℝ) - r)) * F r)
        := by
    have hh : (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) + L - 1 - j)) *
        (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - r)) = D *
          ((3 : ℝ) ^ (-β * ((j : ℝ) - r)) * (3 : ℝ) ^ (-((1 - γ) / 4) * ((t : ℝ) - 1 - r))) := by
      dsimp only [D, β, t]
      simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1; ring
    calc
      _ = ((3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) + L - 1 - j)) *
          (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - r))) * p r := by ring
      _ = _ := by rw [hh]; dsimp only [F]; ring
  have hpay : (∑ r ∈ U, F r) ≤
      (2 + 1 / (1 - (3 : ℝ) ^ (-((1 - γ) / 4)))) * profile P γ q jStar k t :=
    transport_meanHistory_to_profile d hd P γ E Ψ K S hstat hdag jStar hj m hm k t hk (by dsimp
      only [t]; omega)
  calc
    _ = D * ∑ j ∈ J, ∑ r ∈ T j, (3 : ℝ) ^ (-β * ((j : ℝ) - r)) * F r := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _; rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun r _ => he j r)
    _ ≤ D * ((1 / (1 - (3 : ℝ) ^ (-β))) * ∑ r ∈ U, F r) := mul_le_mul_of_nonneg_left hconv hD
    _ ≤ D * ((1 / (1 - (3 : ℝ) ^ (-β))) *
        ((2 + 1 / (1 - (3 : ℝ) ^ (-((1 - γ) / 4)))) * profile P γ q jStar k t)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpay hG.le) hD
    _ = _ := by ring
/-- A source convolution retains its terminal decay and has a geometric mass. -/
theorem transport_source_convolution (a b : ℝ) (hab : a < b)
    (J lo t : ℤ) (hlo : J ≤ lo) :
    (∑ j ∈ Finset.Icc lo t, (3 : ℝ) ^ (-a * ((t : ℝ) - j)) *
      (3 : ℝ) ^ (-b * ((j : ℝ) - J))) ≤
      (1 / (1 - (3 : ℝ) ^ (-(b - a)))) * (3 : ℝ) ^ (-a * ((t : ℝ) - J)) := by
  have he (j : ℤ) : (3 : ℝ) ^ (-a * ((t : ℝ) - j)) * (3 : ℝ) ^ (-b * ((j : ℝ) - J)) =
      (3 : ℝ) ^ (-(b - a) * ((j : ℝ) - J)) * (3 : ℝ) ^ (-a * ((t : ℝ) - J)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3), ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1; ring
  simp_rw [he]
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left hlo)
    (fun _ _ _ => by positivity)).trans (transport_geometric_forward (b - a) (sub_pos.mpr hab) J t)
/-- Both fine-source powers have the printed decay, including an empty target range. -/
theorem transport_fine_weight_sum (γ : ℝ) (hγ : γ < 1) (Q : ℕ) (hQ : 1 ≤ Q)
    (J n : ℤ) (L : ℕ) :
    (∑ j ∈ Finset.Icc (J + (L : ℤ)) (n + L),
      (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) + L - j)) *
        ((3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - J)) +
         (3 : ℝ) ^ (-(Q : ℝ) * (1 - γ) * ((j : ℝ) - J)))) ≤
      (2 / (1 - (3 : ℝ) ^ (-(3 * (1 - γ) / 4)))) *
        (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) + L - J)) := by
  have hq : 1 ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hp (j : ℤ) (hj : j ∈ Finset.Icc (J + (L : ℤ)) (n + L)) :
      (3 : ℝ) ^ (-(Q : ℝ) * (1 - γ) * ((j : ℝ) - J)) ≤
        (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - J)) := by
    have hjJ : (J : ℝ) ≤ j := by exact_mod_cast (show J ≤ j by have := (Finset.mem_Icc.mp hj).1;
      omega)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith only [mul_nonneg (sub_nonneg.mpr hq) (mul_nonneg (sub_pos.mpr hγ).le
      (sub_nonneg.mpr hjJ))]
  have hb := transport_source_convolution ((1 - γ) / 4) (1 - γ) (by linarith only [hγ])
    J (J + (L : ℤ)) (n + L) (by omega)
  have he : 1 - γ - (1 - γ) / 4 = 3 * (1 - γ) / 4 := by ring
  simp only [Int.cast_add, Int.cast_natCast, he] at hb
  calc
    _ ≤ ∑ j ∈ Finset.Icc (J + (L : ℤ)) (n + L),
        2 * ((3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) + L - j)) *
          (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - J))) := by
      apply Finset.sum_le_sum
      intro j hj
      have := mul_le_mul_of_nonneg_left (hp j hj) (by positivity :
        0 ≤ (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) + L - j)))
      nlinarith only [this]
    _ = 2 * ∑ j ∈ Finset.Icc (J + (L : ℤ)) (n + L),
        (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) + L - j)) *
          (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - J)) := (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * ((1 / (1 - (3 : ℝ) ^ (-(3 * (1 - γ) / 4)))) *
        (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) + L - J))) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring
/-- Early target generations start at J and pay decay in n−J. -/
theorem transport_early_weight_sum (a : ℝ) (ha : 0 < a) (J n : ℤ) (L : ℕ) :
    (∑ j ∈ Finset.Icc J (J + (L : ℤ) - 1),
      (3 : ℝ) ^ (-a * ((n : ℝ) + L - j))) ≤
      (1 / (1 - (3 : ℝ) ^ (-a))) * (3 : ℝ) ^ (-a * ((n : ℝ) - J)) := by
  have he (j : ℤ) : (3 : ℝ) ^ (-a * ((n : ℝ) + L - j)) =
      (3 : ℝ) ^ (-a * ((J + (L : ℤ) - 1 : ℤ) - j : ℝ)) *
        (3 : ℝ) ^ (-a * ((n : ℝ) - J + 1)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  simp_rw [he]
  rw [← Finset.sum_mul]
  have hG := transport_geometric_Icc a ha J (J + (L : ℤ) - 1)
  exact (mul_le_mul_of_nonneg_right hG.2 (by positivity)).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith only [ha]))
        (one_div_nonneg.mpr hG.1.le))
/-- The comparison error has bounded geometric mass. -/
theorem transport_comparison_error_sum (a : ℝ) (ha : 0 < a) (J t : ℤ)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    (∑ j ∈ Finset.Icc J t, (3 : ℝ) ^ (-a * ((t : ℝ) - j)) * δ) ≤
      (1 / (1 - (3 : ℝ) ^ (-a))) * δ := by
  rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (transport_geometric_Icc a ha J t).2 hδ
/-- The asymmetric profile bracket absorbs each of its source amplitudes. -/
theorem transport_profile_source_bracket {Pi K₀ e ePlus : ℝ} (hPi : 0 ≤ Pi)
    (hK₀ : 0 ≤ K₀) (he : 0 ≤ e) (hePlus : 0 ≤ ePlus) :
    1 ≤ 1 + Pi * (K₀ * e * ePlus + ePlus ^ 2) ∧
      Pi * K₀ * e * ePlus ≤ 1 + Pi * (K₀ * e * ePlus + ePlus ^ 2) ∧
      Pi * ePlus ^ 2 ≤ 1 + Pi * (K₀ * e * ePlus + ePlus ^ 2) := by
  have hmix : 0 ≤ Pi * K₀ * e * ePlus := by positivity
  have hnew : 0 ≤ Pi * ePlus ^ 2 := by positivity
  constructor
  · nlinarith only [hmix, hnew]
  constructor <;> nlinarith only [hmix, hnew]
/-- Applying the source theorem to the target itself gives the square of the
new-grid eccentricity. One X works for all target generations and centers. -/
theorem exists_transport_target_source (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc C : ℝ, 0 < Csrc ∧ 0 < C ∧
    ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
      (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
      IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ K S →
      ∀ jStar : ℕ, 2 * d ≤ 3 ^ jStar →
        ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
      ∃ X : CoeffSpace d → ℝ, (∀ a, 0 ≤ X a) ∧
        MemLp X (ENNReal.ofReal (bigQ d γ : ℝ)) P ∧
        eLpNorm X (ENNReal.ofReal (bigQ d γ : ℝ)) P ≤ ENNReal.ofReal 2 ∧
        Integrable X P ∧ (∫ a, X a ∂P ≤ 2) ∧
        ∀ᵐ a ∂P, ∀ mPlus : Mat d, mPlus.PosDef →
          ∀ s : ℤ, (jStar : ℤ) ≤ s →
            adaptedCell (explicitRoundedGrid jStar mPlus) s ⊆ centeredCube d (2 * (jStar : ℤ)) →
          ∀ j : ℤ, (jStar : ℤ) ≤ j → ∀ y : Vec d,
            adaptedCellTranslate (explicitRoundedGrid jStar mPlus) j y ⊆ centeredCube d (2 *
              (jStar : ℤ)) →
          BlockMatLoewnerLE
            (normalizedBlock (coarseBlock (adaptedCellTranslate (explicitRoundedGrid jStar
              mPlus) j y) a)
              (adaptedMean P (explicitRoundedGrid jStar mPlus) s))
            (blockScale (C * aspectRatio E * (Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖)) ^ 2 * X a)
              (Book.Ch02.blockIdentity d)) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Cs, Ca, hCs, hCa, hsource⟩ := Source.source_multiplier_and_adapted_bound d hd γ hγ
  obtain ⟨CnSrc, Cn, hCnSrc, hCn, hnormalize⟩ := bridge_normalize_source_tail d hd γ hγ
  refine ⟨max Cs CnSrc, Ca * Cn, hCs.trans_le (le_max_left _ _), mul_pos hCa hCn, ?_⟩
  intro P hP E Ψ K S hstat hdag jStar hj hsrc
  have hlog : 0 ≤ Real.logb 3 (2 * K) := (Real.logb_pos (by norm_num)
    (by linarith only [hdag.one_lt_growthWitness] : (1 : ℝ) < 2 * K)).le
  have hsS := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left Cs CnSrc) hlog)).trans hsrc
  have hsN := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_right Cs CnSrc) hlog)).trans hsrc
  obtain ⟨ell, X, _hell, _hXm, hform, _hgood, hX, _hXi, _hmoment, hnorm, hbound⟩ := hsource P E
    Ψ K S hstat hdag jStar hj hsS
  have hX0 (a) : 0 ≤ X a := by rw [hform]; positivity
  have hQ : 1 ≤ (bigQ d γ : ℝ) := by exact_mod_cast (bigQ_two_le d γ hγ).trans' (by norm_num)
  refine ⟨X, hX0, hX, hnorm, hX.integrable (ENNReal.one_le_ofReal.mpr hQ),
    source_envelope_integral_le_two d hd γ hγ P X hX0 hX hnorm, ?_⟩
  filter_upwards [hbound] with a ha
  intro mPlus hmPlus s hs hsW j hjJ y hyW
  have hjR : (jStar : ℝ) - j ≤ 0 := by exact_mod_cast sub_nonpos.mpr hjJ
  have hA : BlockMatLoewnerLE (coarseBlock (adaptedCellTranslate (explicitRoundedGrid jStar
    mPlus) j y) a)
      (blockScale (Ca * Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖) * X a) E) := by
    simpa only [max_eq_right hjR, mul_zero, Real.rpow_zero, mul_one] using ha.2 mPlus hmPlus j y hyW
  have hnormed := hnormalize P E Ψ K S hstat hdag jStar hj hsN mPlus hmPlus s hs hsW _ _
    (by have := hX0 a; positivity) hA
  have hR := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj mPlus hmPlus s
  have hM := posDef_toFullBlockMat (isSymmetricBlockMat_coarseBlockMatrix _ (⇑a.1))
    (blockPosDef_coarseBlock_adapted _ (isUnit_roundedGrid hj hmPlus) j y a)
  have hn := (transport_normalized_psd_bound hM.posSemidef hR
    (by have := hX0 a; have := aspectRatio_nonneg E; positivity) hnormed).2
  convert hn using 1
  congr 1; ring_nf
/-- The source L^Q bound gives its actual Bochner moment. -/
theorem transport_source_moment {α : Type*} [MeasurableSpace α] {P : Measure α} (Q : ℕ) (hQ : 0
  < Q) (X : α → ℝ) (hX0 : ∀ᵐ a ∂P, 0 ≤ X a) (hX : MemLp X (ENNReal.ofReal (Q : ℝ)) P) (M : ℝ)
  (hM : 0 ≤ M)
    (hnorm : eLpNorm X (ENNReal.ofReal (Q : ℝ)) P ≤ ENNReal.ofReal M) :
    (∫ a, X a ^ Q ∂P) ≤ M ^ Q := by
  have hQr : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hI : 0 ≤ ∫ a, X a ^ Q ∂P := integral_nonneg_of_ae (hX0.mono fun _ ha => pow_nonneg ha Q)
  have he := scalar_eLpNorm_toReal_eq_root hQr hX0 hX
  simp only [Real.rpow_natCast] at he
  have hr : (∫ a, X a ^ Q ∂P) ^ (Q : ℝ)⁻¹ ≤ M := by
    rw [← he]
    simpa only [ENNReal.toReal_ofReal hM] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg hI _) hr hQr.le
  rwa [← Real.rpow_mul hI, inv_mul_cancel₀ hQr.ne', Real.rpow_one, Real.rpow_natCast] at hp
/-- Two common source fields and their centering constants have a fixed moment. -/
theorem transport_source_sum_moment {α : Type*} [MeasurableSpace α] {P : Measure α}
    [IsProbabilityMeasure P] (Q : ℕ) (hQ : 0 < Q) (X Y : α → ℝ) (hX0 : ∀ᵐ a ∂P, 0 ≤ X a) (hY0 :
      ∀ᵐ a ∂P, 0 ≤ Y a) (hX : MemLp X (ENNReal.ofReal (Q : ℝ)) P) (hY : MemLp Y (ENNReal.ofReal
      (Q : ℝ)) P)
    (hXN : eLpNorm X (ENNReal.ofReal (Q : ℝ)) P ≤ ENNReal.ofReal 2)
    (hYN : eLpNorm Y (ENNReal.ofReal (Q : ℝ)) P ≤ ENNReal.ofReal 2) :
    (∫ a, (X a + Y a + 4) ^ Q ∂P) ≤ (3 : ℝ) ^ Q * (2 * 2 ^ Q + 4 ^ Q) := by
  let F : Fin 3 → α → ℝ := ![X, Y, fun _ => 4]
  have hF0 (i : Fin 3) : ∀ᵐ a ∂P, 0 ≤ F i a := by
    fin_cases i
    · exact hX0
    · exact hY0
    · exact ae_of_all P fun _ => by norm_num [F]
  have hF (i : Fin 3) : MemLp (F i) (ENNReal.ofReal (Q : ℝ)) P := by
    fin_cases i
    · exact hX
    · exact hY
    · exact memLp_const 4
  have hs := transport_weighted_moment_sum Q hQ Finset.univ (fun _ : Fin 3 => (1 : ℝ))
    (fun _ _ => by norm_num) F (fun i _ => hF0 i) (fun i _ => hF i) (M := 3) (by norm_num) (by
      norm_num)
  have hx := transport_source_moment Q hQ X hX0 hX 2 (by norm_num) hXN
  have hy := transport_source_moment Q hQ Y hY0 hY 2 (by norm_num) hYN
  have hb := hs.2
  simp only [Fin.sum_univ_succ, F, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero, inv_one, one_pow, one_mul, integral_const, probReal_univ, one_smul,
    ← add_assoc] at hb
  apply hb.trans (mul_le_mul_of_nonneg_left _ (by positivity))
  linarith only [hx, hy]
/-- Both early targets and fine Whitney tails pay a single common source
weight; raising that weight to Q gives exactly the printed profile decay. -/
theorem transport_source_max_weight (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (J n j : ℤ) (L : ℕ) (_hn : J ≤ n) (hj : j ∈ Set.Icc J (n + (L : ℤ))) :
    let b := ((1 - γ) / 4) / (bigQ d γ : ℝ)
    (j < J + (L : ℤ) → (3 : ℝ) ^ (-rhoMax d γ * ((n : ℝ) + L - j)) ≤
      (3 : ℝ) ^ (-b * ((n : ℝ) - J))) ∧
    (3 : ℝ) ^ (-rhoMax d γ * ((n : ℝ) + L - j)) *
        (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - J)) ≤ (3 : ℝ) ^ (-b * ((n : ℝ) - J)) ∧
    ((3 : ℝ) ^ (-b * ((n : ℝ) - J))) ^ bigQ d γ =
      (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) - J)) := by
  intro b
  have hQ := bigQ_real_pos d γ hγ
  have hQ1 : 1 ≤ (bigQ d γ : ℝ) := by exact_mod_cast bigQ_pos d γ hγ
  have ha : 0 < 1 - γ := sub_pos.mpr hγ.2
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hbr : b ≤ rhoMax d γ := by
    have he := rhoMax_sub_d_div_bigQ d hd γ hγ
    rw [← div_div] at he
    have hdQ : 0 ≤ (d : ℝ) / (bigQ d γ : ℝ) := div_nonneg (Nat.cast_nonneg d) hQ.le
    dsimp only [b]; linarith only [he, hγ.1, hdQ]
  have hba : b ≤ 1 - γ := by
    apply (div_le_iff₀ hQ).mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hQ1) (sub_pos.mpr hγ.2).le, hγ.2]
  have hj0 : 0 ≤ (j : ℝ) - J := by exact_mod_cast sub_nonneg.mpr hj.1
  have hjt : 0 ≤ (n : ℝ) + L - j := by exact_mod_cast sub_nonneg.mpr hj.2
  constructor
  · intro hearly
    have he : (n : ℝ) - J ≤ (n : ℝ) + L - j := by exact_mod_cast (show n - J ≤ n + (L : ℤ) - j
      by omega)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith only [mul_nonneg (sub_nonneg.mpr hbr) hjt, mul_le_mul_of_nonneg_left he hb]
  constructor
  · rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith only [mul_nonneg (sub_nonneg.mpr hbr) hjt, mul_nonneg (sub_nonneg.mpr hba) hj0,
      mul_nonneg hb (Nat.cast_nonneg L)]
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    dsimp only [b]
    field_simp [hQ.ne']
/-- The printed bulk fluctuation estimate for the actual Whitney rows.
The constant precedes the law, geometry and all generation choices. -/
theorem exists_transport_bulk_fluctuations (d : ℕ) (hd : 2 ≤ d)
    (K₀ : ℝ) (hK₀ : 1 ≤ K₀) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (S : CoeffSpace d → ℝ) (_hP : IsProbabilityMeasure P),
      IsStationaryLaw P → IsUnitRangeLaw P → CoarseEllipticityDagger P γ E Ψ K S →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
      ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
      ∀ m mPlus : Mat d, m.PosDef → mPlus.PosDef →
      gridRatio (explicitRoundedGrid jStar m) (explicitRoundedGrid jStar mPlus) ≤ K₀ →
      ∀ k n : ℤ, (jStar : ℤ) ≤ k → k ≤ n → ∀ L : ℕ, 1 ≤ L →
      let q := explicitRoundedGrid jStar m
      let qPlus := explicitRoundedGrid jStar mPlus
      let Q := bigQ d γ
      let ell := fun j : ℤ => if j ≤ k + (L : ℤ) then 1 else L
      let cap := fun j : ℤ => j - (ell j : ℤ)
      let W := fun p : ℤ × (Fin d → ℤ) => adaptedCellAtCenter qPlus p.1 p.2
      ∀ (I : Finset (ℤ × (Fin d → ℤ))),
        (∀ p ∈ I, p.1 ∈ Set.Icc ((jStar : ℤ) + L) (n + L)) →
        (∀ p ∈ I, standardCellCenter p.1 p.2 ∈ centeredCube d (n + L)) →
      ∃ hfin : ∀ p : ℤ × (Fin d → ℤ), ∀ r : ℤ, r ≤ cap p.1 →
          (maximalAdaptedCellCenters (W p) q (cap p.1) r).Finite,
        let Z := fun p => (hfin p (cap p.1) le_rfl).toFinset
        let v := fun p => (volume (adaptedCell q (cap p.1))).toReal / (volume (W p)).toReal
        (∫ a, (⨆ p ∈ (I : Set (ℤ × (Fin d → ℤ))),
          (3 : ℝ) ^ (-rhoMax d γ * ((n : ℝ) + L - p.1)) * absSchattenNorm (Q : ℝ)
            (ofFullBlockMat (∑ z ∈ Z p, v p • toFullBlockMat
              (normalizedFluctuation P q (cap p.1) (n + 2 * (L : ℤ)) z a)))) ^ (Q : ℝ) ∂P) ≤
          C * (3 : ℝ) ^ ((1 - γ) / 4 * (L : ℝ)) * profile P γ q jStar k (n + 2 * (L : ℤ)) := by
  classical
  obtain ⟨Cr, hCr, D, hD, hrows⟩ := exists_transport_whitney_rows d hd K₀ hK₀ γ hγ
  obtain ⟨Cb, hCb, hhigh⟩ := exists_transport_high_bulk_profile d hd γ hγ
  obtain ⟨h, hcover⟩ := exists_transport_parent_enlargement d hd K₀ hK₀
  let B := (2 * (d : ℝ)) * (3 : ℝ) ^ ((bigQ d γ : ℝ) * rhoMax d γ + (d : ℝ) * h)
  let A := ((bigQ d γ : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) * D) ^ bigQ d γ
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨max Cr Cb, hCr.trans_le (le_max_left _ _), B + 2 * A, by positivity, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag jStar hj hsrc m mPlus hm hmPlus hratio k n hk hkn L hL
    q qPlus Q ell cap W I hgen hcenter
  let := hP
  have hK := hdag.one_lt_growthWitness
  have hlog : 0 ≤ Real.logb 3 (2 * K) := (Real.logb_pos (by norm_num) (by linarith only [hK] :
    (1 : ℝ) < 2 * K)).le
  have hsR := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left Cr Cb) hlog)).trans hsrc
  have hsB := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_right Cr Cb) hlog)).trans hsrc
  obtain ⟨hfin, hdata⟩ := hrows K hK jStar hj hsR m mPlus hm hmPlus hratio k (n + (L : ℤ)) L hL
    I (fun p hp => (hgen p hp).2) hcenter
  refine ⟨hfin, ?_⟩
  intro Z v
  let c := (3 : ℝ) ^ ((1 - γ) / 4 * (L : ℝ))
  let F := fun p a => (3 : ℝ) ^ (-rhoMax d γ * ((n : ℝ) + L - p.1)) *
    absSchattenNorm (Q : ℝ) (ofFullBlockMat (∑ z ∈ Z p, v p • toFullBlockMat
      (normalizedFluctuation P q (cap p.1) (n + 2 * (L : ℤ)) z a)))
  let Il := I.filter (fun p => cap p.1 ≤ k)
  let Ih := I.filter (fun p => k < cap p.1)
  have hU : Il ∪ Ih = I := by
    ext p; simp only [Il, Ih, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (hp | hp) <;> exact hp.1
    · intro hp
      rcases le_or_gt (cap p.1) k with he | he
      · exact Or.inl ⟨hp, he⟩
      · exact Or.inr ⟨hp, he⟩
  have hP0 := bridge_profile_nonneg d hd P γ E Ψ K S hstat hdag jStar hj m hm k (n + 2 * (L :
    ℤ)) hk (by omega)
  have hQ : 0 < Q := bigQ_pos d γ hγ
  have hQ1 : 1 ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hmem (p) : SchattenMemLp P (Q : ℝ) (fun a => ofFullBlockMat (∑ z ∈ Z p, v p •
      toFullBlockMat (normalizedFluctuation P q (cap p.1) (n + 2 * (L : ℤ)) z a))) :=
    memLqSchatten_normalizedCentered_sum d hd P γ E Ψ K S hstat hdag jStar hj m hm
      (cap p.1) (adaptedMean P q (n + 2 * (L : ℤ))) Q hQ1 (Z p) (fun _ => v p) id
  have hF0 (p) : ∀ᵐ a ∂P, 0 ≤ F p a := (hmem p).symmetric.mono fun _ ha =>
    mul_nonneg (by positivity) (absSchattenNorm_nonneg ((toFullBlockMat_isHermitian_iff _).2 ha)
      hQ1)
  have hFmem (p) : MemLp (F p) (ENNReal.ofReal (Q : ℝ)) P := ((hmem p).memLp_absSchattenNorm
    hQ1).const_mul _
  have hZcap (p) (hp : p ∈ I) : (Z p : Set (Vec d)) ⊆
      adaptedLatticeAtScale q (cap p.1) ∩ adaptedCell qPlus (n + (L : ℤ)) := by
    have hh : (((if hr : cap p.1 ≤ cap p.1 then (hfin p (cap p.1) hr).toFinset else ∅) : Finset
      (Vec d)) : Set (Vec d)) ⊆
        adaptedLatticeAtScale q (cap p.1) ∩ adaptedCell qPlus (n + (L : ℤ)) := (hdata p hp).1
          (cap p.1) le_rfl
    simpa only [dite_eq_left le_rfl] using hh
  have hmasscap (p) (hp : p ∈ I) : ∑ _z ∈ Z p, v p ≤ 1 := by
    have hh : (∑ _z ∈ (if hr : cap p.1 ≤ cap p.1 then (hfin p (cap p.1) hr).toFinset else ∅), v
      p) ≤ 1 :=
      (hdata p hp).2.1
    simpa only [dite_eq_left le_rfl] using hh
  have hrootcap (p) (hp : p ∈ I) : (∑ _z ∈ Z p, v p ^ 2) ^ ((1 : ℝ) / 2) ≤
      D * (3 : ℝ) ^ (-(d : ℝ) / 2 * (ell p.1 : ℝ)) := by
    have hh : (∑ _z ∈ (if hr : cap p.1 ≤ cap p.1 then (hfin p (cap p.1) hr).toFinset else ∅), v
      p ^ 2) ^ ((1 : ℝ) / 2) ≤
        D * (3 : ℝ) ^ (-(d : ℝ) / 2 * (ell p.1 : ℝ)) := (hdata p hp).2.2.1
    simpa only [dite_eq_left le_rfl] using hh
  have hcaplo (p) (hp : p ∈ Il) : cap p.1 = p.1 - 1 := by
    have hh := (Finset.mem_filter.mp hp).2
    dsimp only [cap, ell] at hh ⊢
    split_ifs at hh ⊢ with he
    · rfl
    · omega
  have hl : (∫ a, (⨆ p ∈ (Il : Set (ℤ × (Fin d → ℤ))), F p a) ^ (Q : ℝ) ∂P) ≤
      B * c * profile P γ q jStar k (n + 2 * (L : ℤ)) := by
    by_cases hIl : Il.Nonempty
    · have hlgen (p) (hp : p ∈ Il) : p.1 - 1 ∈ Set.Icc (jStar : ℤ) k := by
        obtain ⟨hgl, hgu⟩ := hgen p (Finset.mem_filter.mp hp).1
        have hc := (Finset.mem_filter.mp hp).2
        rw [hcaplo p hp] at hc; exact ⟨by omega, hc⟩
      have hZl (p) (hp : p ∈ Il) : (Z p : Set (Vec d)) ⊆ adaptedLatticeAtScale q (p.1 - 1) ∩
        adaptedCell qPlus (n + L) := by
        simpa only [← hcaplo p hp] using hZcap p (Finset.mem_filter.mp hp).1
      have hmass (p) (hp : p ∈ Il) : ∑ _z ∈ Z p, v p ≤ 1 := by
        exact hmasscap p (Finset.mem_filter.mp hp).1
      have hb := transport_old_bulk_profile_bound d hd P γ hγ E Ψ K S hstat hdag jStar hj m hm qPlus
        k n hk hkn L h (hcover q qPlus (isUnit_roundedGrid hj hm) hratio (n + (L : ℤ)))
        Il hIl Prod.fst Z v hlgen hZl (fun p _ => by dsimp only [v]; positivity) hmass
      have he (a : CoeffSpace d) : (⨆ p ∈ (Il : Set (ℤ × (Fin d → ℤ))), F p a) =
          ⨆ p ∈ (Il : Set (ℤ × (Fin d → ℤ))),
            (3 : ℝ) ^ (-rhoMax d γ * ((n : ℝ) + L - p.1)) * absSchattenNorm (Q : ℝ)
              (ofFullBlockMat (∑ z ∈ Z p, v p • toFullBlockMat
                (normalizedFluctuation P q (p.1 - 1) (n + 2 * (L : ℤ)) z a))) := by
        apply iSup_congr
        intro p
        apply iSup_congr
        intro hp
        dsimp only [F]; rw [hcaplo p hp]
      have hie := integral_congr_ae (ae_of_all P (fun a => congrArg (fun x : ℝ => x ^ (Q : ℝ))
        (he a)))
      exact hie.le.trans hb
    · simpa [Finset.not_nonempty_iff_eq_empty.mp hIl, Real.rpow_natCast, zero_pow (Nat.ne_of_gt
      hQ)] using
        mul_nonneg (mul_nonneg hB.le hc) hP0
  have hh : (∫ a, (⨆ p ∈ (Ih : Set (ℤ × (Fin d → ℤ))), F p a) ^ (Q : ℝ) ∂P) ≤
      2 * A * c * profile P γ q jStar k (n + 2 * (L : ℤ)) := by
    by_cases hIh : Ih.Nonempty
    · apply hhigh P E Ψ K S hP hstat hunit hdag jStar hj hsB m hm k n hk hkn L D hD.le Ih hIh Z v
      · intro p hp
        have hh := (Finset.mem_filter.mp hp).2
        obtain ⟨hgl, hgu⟩ := hgen p (Finset.mem_filter.mp hp).1
        have hcapj : cap p.1 ≤ p.1 := by dsimp only [cap]; omega
        change cap p.1 ∈ Finset.Icc (k + 1) (n + 2 * (L : ℤ))
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · exact fun p hp => (hgen p (Finset.mem_filter.mp hp).1).2
      · intro j hjmem
        simpa only [Int.cast_add, Int.cast_natCast] using transport_target_fiber_card Ih (n + (L
          : ℤ))
          (fun p hp => (hgen p (Finset.mem_filter.mp hp).1).2)
          (fun p hp => hcenter p (Finset.mem_filter.mp hp).1) j hjmem
      · intro p hp z hz
        exact (hZcap p (Finset.mem_filter.mp hp).1 hz).1
      · exact fun p _ => by dsimp only [v]; positivity
      · intro p hp
        exact hrootcap p (Finset.mem_filter.mp hp).1
    · have hp : 0 ≤ (2 : ℝ) * A * c * profile P γ q jStar k (n + 2 * (L : ℤ)) := mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hA) hc) hP0
      simpa [Finset.not_nonempty_iff_eq_empty.mp hIh, Real.rpow_natCast, zero_pow (Nat.ne_of_gt
        hQ)] using hp
  have ht := transport_joint_union_moment Q hQ Il Ih F (fun p _ => hF0 p) (fun p _ => hFmem p)
  rw [hU] at ht; exact ht.trans ((add_le_add hl hh).trans_eq (by ring))
/-- The real fluctuation history is exactly one finite joint maximum over
paired target generations and integer centers, with its Q-th power outside. -/
theorem transport_fluctuation_history_reindex {d : ℕ} (P : Measure (CoeffSpace d))
    (γ : ℝ) (q : Mat d) (hq : IsUnit q) (jStar : ℕ) (t : ℤ) (ht : (jStar : ℤ) ≤ t) :
    ∃ I : Finset (ℤ × (Fin d → ℤ)), I.Nonempty ∧
      (∀ p, p ∈ I ↔ p.1 ∈ Set.Icc (jStar : ℤ) t ∧ standardCellCenter p.1 p.2 ∈ centeredCube d t) ∧
      fluctuationHistory P γ q jStar t =
        ∫ a, (⨆ p ∈ (I : Set (ℤ × (Fin d → ℤ))),
          (3 : ℝ) ^ (-rhoMax d γ * ((t : ℝ) - p.1)) *
            blockOpNorm (normalizedFluctuation P q p.1 t (adaptedCellCenter q p.1 p.2) a)) ^
              (bigQ d γ : ℝ) ∂P := by
  classical
  let Z := fun j : ℤ => if hj : j ≤ t then
    ((alignedCenterSet_finite_card d j (t - j).toNat).1).toFinset else ∅
  have hZ (j : ℤ) (hj : j ≤ t) (w : Fin d → ℤ) : w ∈ Z j ↔ standardCellCenter j w ∈ centeredCube
    d t := by
    have he : j + ((t - j).toNat : ℤ) = t := by omega
    simp only [Z, dite_eq_left hj, Set.Finite.mem_toFinset, he, Set.mem_ofPred_eq]
  let I := (Finset.Icc (jStar : ℤ) t).biUnion (fun j => (Z j).image (fun w => (j, w)))
  have hI (p : ℤ × (Fin d → ℤ)) : p ∈ I ↔ p.1 ∈ Set.Icc (jStar : ℤ) t ∧
      standardCellCenter p.1 p.2 ∈ centeredCube d t := by
    constructor
    · intro hp
      obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hpj
      cases he
      exact ⟨Finset.mem_Icc.mp hj, (hZ j (Finset.mem_Icc.mp hj).2 w).mp hw⟩
    · intro hp
      exact Finset.mem_biUnion.mpr ⟨p.1, Finset.mem_Icc.mpr hp.1,
        Finset.mem_image.mpr ⟨p.2, (hZ p.1 hp.1.2 p.2).mpr hp.2, Prod.eta p⟩⟩
  have hzero : standardCellCenter t (0 : Fin d → ℤ) ∈ centeredCube d t := by
    rw [Recurrence.mem_centeredCube_iff]
    intro i; simp only [HighContrast.standardCellCenter, Pi.zero_apply, Int.cast_zero, mul_zero]
    have hp : (0 : ℝ) < 3 ^ t := by positivity
    constructor <;> nlinarith only [hp]
  have hIne : I.Nonempty := ⟨(t, 0), (hI _).mpr ⟨⟨ht, le_rfl⟩, hzero⟩⟩
  refine ⟨I, hIne, hI, ?_⟩
  let Q := bigQ d γ
  let f := fun (p : ℤ × (Fin d → ℤ)) a => (3 : ℝ) ^ (-rhoMax d γ * ((t : ℝ) - p.1)) *
    blockOpNorm (normalizedFluctuation P q p.1 t (adaptedCellCenter q p.1 p.2) a)
  have hf0 (p a) : 0 ≤ f p a := mul_nonneg (by positivity) (norm_nonneg _)
  have hc (p) (hp : p ∈ I) : adaptedCellCenter q p.1 p.2 ∈ adaptedLatticeAtScale q p.1 ∩
    adaptedCell q t := ⟨⟨p.2, rfl⟩, ⟨standardCellCenter p.1 p.2, (hI p).mp hp |>.2,
      (Recurrence.adaptedCellCenter_eq q p.1 p.2).symm⟩⟩
  have hpow (p a) : f p a ^ (Q : ℝ) =
      (3 : ℝ) ^ (-(Q : ℝ) * rhoMax d γ * ((t : ℝ) - p.1)) *
        blockOpNorm (normalizedFluctuation P q p.1 t (adaptedCellCenter q p.1 p.2) a) ^ Q := by
    have hn : 0 ≤ blockOpNorm (normalizedFluctuation P q p.1 t (adaptedCellCenter q p.1 p.2) a)
      := norm_nonneg _
    dsimp only [f]
    rw [Real.mul_rpow (by positivity : 0 ≤ (3 : ℝ) ^ (-rhoMax d γ * ((t : ℝ) - p.1))) hn,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
    congr 2; ring
  unfold fluctuationHistory
  apply integral_congr_ae
  apply ae_of_all
  intro a
  have hinner (j : ℤ) (hj : j ∈ Set.Icc (jStar : ℤ) t) : ∃ z ∈ adaptedLatticeAtScale q j ∩
    adaptedCell q t,
      (⨆ y ∈ adaptedLatticeAtScale q j ∩ adaptedCell q t,
        blockOpNorm (normalizedFluctuation P q j t y a) ^ Q) =
          blockOpNorm (normalizedFluctuation P q j t z a) ^ Q := by
    obtain ⟨hfin, hne⟩ := transport_history_centers q hq j t hj.2
    have hfn := hfin.toFinset_nonempty.mpr hne
    obtain ⟨z, hz, he⟩ := Finset.exists_mem_eq_sup' hfn
      (fun z => blockOpNorm (normalizedFluctuation P q j t z a) ^ Q)
    refine ⟨z, hfin.mem_toFinset.mp hz, ?_⟩
    simpa only [Set.Finite.coe_toFinset] using!
      (iSup_mem_finset_eq_finset_sup hfin.toFinset hfn _ (fun _ _ => pow_nonneg (norm_nonneg _)
        Q)).trans he
  have hj0 (j) (hj : j ∈ Finset.Icc (jStar : ℤ) t) : 0 ≤
      (3 : ℝ) ^ (-(Q : ℝ) * rhoMax d γ * ((t : ℝ) - j)) *
        ⨆ y ∈ adaptedLatticeAtScale q j ∩ adaptedCell q t,
          blockOpNorm (normalizedFluctuation P q j t y a) ^ Q := by
    obtain ⟨z, _hz, he⟩ := hinner j (Finset.mem_Icc.mp hj)
    rw [he]; exact mul_nonneg (by positivity) (pow_nonneg (norm_nonneg _) Q)
  have hfmax : (⨆ p ∈ (I : Set (ℤ × (Fin d → ℤ))), f p a) = I.sup' hIne (fun p => f p a) :=
    iSup_mem_finset_eq_finset_sup I hIne _ (fun p _ => hf0 p a)
  change (⨆ j ∈ Set.Icc (jStar : ℤ) t, (3 : ℝ) ^ (-(Q : ℝ) * rhoMax d γ * ((t : ℝ) - j)) *
    ⨆ y ∈ adaptedLatticeAtScale q j ∩ adaptedCell q t, blockOpNorm (normalizedFluctuation P q j
      t y a) ^ Q) =
      (⨆ p ∈ (I : Set (ℤ × (Fin d → ℤ))), f p a) ^ (Q : ℝ)
  apply le_antisymm
  · rw [show Set.Icc (jStar : ℤ) t = (Finset.Icc (jStar : ℤ) t : Set ℤ) by ext; simp,
      iSup_mem_finset_eq_finset_sup _ (Finset.nonempty_Icc.mpr ht) _ hj0, hfmax]
    apply Finset.sup'_le
    intro j hj
    obtain ⟨z, hz, he⟩ := hinner j (Finset.mem_Icc.mp hj)
    obtain ⟨w, rfl⟩ := hz.1
    obtain ⟨x, hx, hxe⟩ := hz.2
    have hew : standardCellCenter j w ∈ centeredCube d t := by
      rw [Recurrence.adaptedCellCenter_eq] at hxe; exact (matVecMul_injective_of_isUnit q hq
        hxe) ▸ hx
    have hp : (j, w) ∈ I := (hI _).mpr ⟨Finset.mem_Icc.mp hj, hew⟩
    rw [he, ← hpow (j, w) a]
    exact Real.rpow_le_rpow (hf0 _ _) (Finset.le_sup' (fun p => f p a) hp) (Nat.cast_nonneg Q)
  · rw [hfmax]
    obtain ⟨p, hp, he⟩ := Finset.exists_mem_eq_sup' hIne (fun p => f p a)
    rw [he, hpow]; exact transport_history_pointwise P γ q hq jStar t p.1 ((hI p).mp hp).1 _ (hc
      p hp) a

private theorem transport_finite_whitney_mass {d : ℕ} (q : Mat d)
    (W : Set (Vec d)) (jStar : ℕ) (cap : ℤ)
    (hfin : ∀ r ≤ cap, (maximalAdaptedCellCenters W q cap r).Finite)
    (htotal : (∑' r : {r : ℤ // r ≤ cap}, ∑ _z ∈ (hfin r.1 r.2).toFinset,
      (volume (adaptedCell q r.1)).toReal / (volume W).toReal) = 1) :
    let Z := fun r => if hr : r ≤ cap then (hfin r hr).toFinset else ∅
    (∑ r ∈ Finset.Icc (jStar : ℤ) cap,
      ∑ _z ∈ Z r, (volume (adaptedCell q r)).toReal / (volume W).toReal) ≤ 1 := by
  classical
  intro Z
  change (∑' r : {r : ℤ // r ≤ cap}, ∑ _z ∈ (hfin r.1 r.2).toFinset,
    (volume (adaptedCell q r.1)).toReal / (volume W).toReal) = 1 at htotal
  have hs : Summable (fun r : {r : ℤ // r ≤ cap} =>
      ∑ _z ∈ (hfin r.1 r.2).toFinset, (volume (adaptedCell q r.1)).toReal / (volume W).toReal)
        := by
    by_contra hn
    rw [tsum_eq_zero_of_not_summable hn] at htotal; norm_num at htotal
  let U := (Finset.Icc (jStar : ℤ) cap).attach.image
    (fun r => (⟨r.1, (Finset.mem_Icc.mp r.2).2⟩ : {r : ℤ // r ≤ cap}))
  have hu := hs.sum_le_tsum U (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
  rw [htotal] at hu
  have he : Function.Injective (fun r : {r // r ∈ Finset.Icc (jStar : ℤ) cap} =>
      (⟨r.1, (Finset.mem_Icc.mp r.2).2⟩ : {r : ℤ // r ≤ cap})) := fun _ _ h => Subtype.ext
        (congrArg (fun x : {r : ℤ // r ≤ cap} => x.1) h)
  dsimp only [U] at hu
  rw [Finset.sum_image (fun _ _ _ _ h => he h)] at hu
  have hz (r) (hr : r ∈ Finset.Icc (jStar : ℤ) cap) : Z r = (hfin r (Finset.mem_Icc.mp
    hr).2).toFinset := dite_eq_left (Finset.mem_Icc.mp hr).2
  have heq : (∑ r ∈ (Finset.Icc (jStar : ℤ) cap).attach,
      ∑ _z ∈ (hfin r.1 (Finset.mem_Icc.mp r.2).2).toFinset,
        (volume (adaptedCell q r.1)).toReal / (volume W).toReal) =
      ∑ r ∈ Finset.Icc (jStar : ℤ) cap, ∑ _z ∈ Z r,
        (volume (adaptedCell q r)).toReal / (volume W).toReal := by
    calc
      _ = ∑ r ∈ (Finset.Icc (jStar : ℤ) cap).attach, ∑ _z ∈ Z r.1,
          (volume (adaptedCell q r.1)).toReal / (volume W).toReal :=
        Finset.sum_congr rfl fun r _ => by rw [hz r.1 r.2]
      _ = _ := Finset.sum_attach (Finset.Icc (jStar : ℤ) cap) (fun r : ℤ =>
        ∑ _z ∈ Z r, (volume (adaptedCell q r)).toReal / (volume W).toReal)
  exact heq ▸ hu

/-- The centered and mean reductions with every Whitney, source, positivity,
series and moment guard discharged. The same source X serves all targets. -/
theorem exists_transport_whitney_reduction (d : ℕ) (hd : 2 ≤ d)
    (K₀ : ℝ) (hK₀ : 1 ≤ K₀) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc Cf Cm : ℝ, 0 < Csrc ∧ 0 < Cf ∧ 0 < Cm ∧
    ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
      (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
      IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ K S →
      ∀ jStar : ℕ, 2 * d ≤ 3 ^ jStar →
        ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
      ∃ X : CoeffSpace d → ℝ, (∀ a, 0 ≤ X a) ∧
        MemLp X (ENNReal.ofReal (bigQ d γ : ℝ)) P ∧
        eLpNorm X (ENNReal.ofReal (bigQ d γ : ℝ)) P ≤ ENNReal.ofReal 2 ∧
        Integrable X P ∧ (∫ a, X a ∂P ≤ 2) ∧
      ∀ m mPlus : Mat d, m.PosDef → mPlus.PosDef →
        gridRatio (explicitRoundedGrid jStar m) (explicitRoundedGrid jStar mPlus) ≤ K₀ →
      ∀ oldEnd newEnd j : ℤ, j ≤ newEnd → ∀ ell : ℕ, 1 ≤ ell →
        (jStar : ℤ) ≤ j - (ell : ℤ) → j - (ell : ℤ) ≤ oldEnd →
        adaptedCell (explicitRoundedGrid jStar mPlus) newEnd ⊆ centeredCube d (2 * (jStar : ℤ)) →
      ∀ w : Fin d → ℤ, standardCellCenter j w ∈ centeredCube d newEnd →
      ∀ δ : ℝ, δ ∈ Set.Icc (0 : ℝ) (1 / 4) →
      let q := explicitRoundedGrid jStar m
      let qPlus := explicitRoundedGrid jStar mPlus
      let Q := bigQ d γ
      let cap := j - (ell : ℤ)
      let W := adaptedCellAtCenter qPlus j w
      let B := aspectRatio E * K₀ * Real.sqrt (‖m‖ * ‖m⁻¹‖) * Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖)
      let decay := (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - jStar))
      let F := adaptedMean P q oldEnd
      let H := adaptedMean P qPlus newEnd
      let I := {p : ℤ × (Fin d → ℤ) // IsMaximalAdaptedCellIn W q cap p.1 p.2}
      let f := fun (p : I) a => ((volume (adaptedCellAtCenter q p.1.1 p.1.2)).toReal / (volume
        W).toReal) •
        toFullBlockMat (coarseBlock (adaptedCellAtCenter q p.1.1 p.1.2) a)
      let G := fun a => normalizedBlock (ofFullBlockMat (∑' p, f p a)) H
      let MG := ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G a) α β ∂P)
      BlockMatLoewnerLE (blockScale (1 - δ) F) H → BlockMatLoewnerLE H (blockScale (1 + δ) F) →
      ∃ hfin : ∀ r ≤ cap, (maximalAdaptedCellCenters W q cap r).Finite,
        let Z := fun r => if hr : r ≤ cap then (hfin r hr).toFinset else ∅
        let V := fun r a => ofFullBlockMat (∑ z ∈ Z r,
          ((volume (adaptedCell q r)).toReal / (volume W).toReal) •
            toFullBlockMat (normalizedFluctuation P q r oldEnd z a))
        (∀ᵐ a ∂P, absSchattenNorm (Q : ℝ) (blockSub (G a) MG) ≤
          ((4 / 3 : ℝ) * (2 * (d : ℝ)) ^ (Q : ℝ)⁻¹) *
            (absSchattenNorm (Q : ℝ) (V cap a) +
              ∑ r ∈ Finset.Icc (jStar : ℤ) (cap - 1), absSchattenNorm (Q : ℝ) (V r a)) +
          ((2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ * (2 * (d : ℝ)) * Cf) * B * decay * (X a + 2)) ∧
        meanPenalty Q MG ≤ Cm * (meanPenalty Q (relMean P q cap oldEnd) +
          (∑ r ∈ Finset.Icc (jStar : ℤ) (cap - 1),
            (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - r)) * meanPenalty Q (relMean P q r oldEnd)) +
          δ + B ^ Q * (decay + decay ^ Q)) := by
  classical
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Cs, Ct, hCs, hCt, hsource⟩ := transport_fine_source_tail d hd γ hγ
  obtain ⟨Co, hCo, hordered⟩ := exists_transport_whitney_ordered_data d hd K₀ hK₀ γ hγ
  obtain ⟨CwSrc, _hCwSrc, hwhitney⟩ := Entry.two_grid_whitney d hd
  obtain ⟨Cw, hCw, hwhitney⟩ := hwhitney K₀ hK₀
  have hQ1 : 1 ≤ bigQ d γ := (bigQ_pos d γ hγ)
  obtain ⟨Cm, hCm, hmean⟩ := transport_whitney_mean_bound d hd γ hγ (bigQ d γ) hQ1
    (Ct * Cw) Cw (mul_pos hCt hCw).le hCw.le
  refine ⟨max Cs (max Co (CwSrc γ)), Ct * Cw, Cm, hCs.trans_le (le_max_left _ _), mul_pos hCt
    hCw, hCm, ?_⟩
  intro P hP E Ψ K S hstat hdag jStar hj hsrc
  have hlog : 0 ≤ Real.logb 3 (2 * K) := (Real.logb_pos (by norm_num)
    (by linarith only [hdag.one_lt_growthWitness] : (1 : ℝ) < 2 * K)).le
  have hsS := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left Cs (max Co (CwSrc γ)))
    hlog)).trans hsrc
  have hsO := (Int.ceil_mono (mul_le_mul_of_nonneg_right
    ((le_max_left Co (CwSrc γ)).trans (le_max_right Cs _)) hlog)).trans hsrc
  have hsW := (Int.ceil_mono (mul_le_mul_of_nonneg_right
    ((le_max_right Co (CwSrc γ)).trans (le_max_right Cs _)) hlog)).trans hsrc
  obtain ⟨X, hX0, hX, hnorm, hXi, hEX, hfine⟩ := hsource P E Ψ K S hstat hdag jStar hj hsS
  refine ⟨X, hX0, hX, hnorm, hXi, hEX, ?_⟩
  intro m mPlus hm hmPlus hratio oldEnd newEnd j hjt ell hell hJcap hcapold hwindow w hw δ hδ
    q qPlus Q cap W B decay F H I f G MG hlow hup
  have hq := isUnit_roundedGrid hj hm
  have hqPlus := isUnit_roundedGrid hj hmPlus
  have hjJ : (jStar : ℤ) ≤ j := by omega
  have hQ : 1 ≤ (Q : ℝ) := by exact_mod_cast hQ1
  have hB : 1 ≤ B := by
    have hPi := one_le_aspectRatio_of_coarseEllipticityDagger hdag
    have he := Source.one_le_source_eccentricity hm
    have hePlus := Source.one_le_source_eccentricity hmPlus
    dsimp only [B]
    calc
      (1 : ℝ) = 1 * 1 * 1 * 1 := by norm_num
      _ ≤ aspectRatio E * K₀ * Real.sqrt (‖m‖ * ‖m⁻¹‖) * Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖) := by
        gcongr
  have hW : W ⊆ centeredCube d (2 * (jStar : ℤ)) := by
    have he : j + ((newEnd - j).toNat : ℤ) = newEnd := by omega
    have hh := (aligned_adapted_partition qPlus hqPlus j (newEnd - j).toNat).1 w (by simpa only
      [he] using! hw)
    rw [he] at hh; exact hh.trans hwindow
  obtain ⟨hfin, hsub, hdis, _hnull, _hvol, _hcard, _hcount, htotal, hrow⟩ := (hwhitney γ hγ K
    hdag.one_lt_growthWitness jStar hj hsW m mPlus hm hmPlus hratio j ell hell).1
      (adaptedCellCenter qPlus j w) ⟨w, rfl⟩
  refine ⟨hfin, ?_⟩
  intro Z V
  let v := fun p : I => (volume (adaptedCellAtCenter q p.1.1 p.1.2)).toReal / (volume W).toReal
  let Ifine := {p : I // p.1.1 < (jStar : ℤ)}
  let M := fun a => ofFullBlockMat (∑' p : Ifine, f p.1 a)
  let T := fun a => normalizedBlock (M a) H
  have hv0 (p : I) : 0 ≤ v p := by dsimp only [v]; positivity
  have hWfin : volume W ≠ ⊤ := Transport.volume_adaptedCellTranslate_ne_top _ _ _
  let : IsFiniteMeasure (volumeMeasureOn W) := ⟨by simpa [volumeMeasureOn] using hWfin.lt_top⟩
  have hv : Summable v := summable_volumeRatio
    (U := fun p : ℤ × (Fin d → ℤ) => adaptedCellAtCenter q p.1 p.2)
    (W := W) (s := {p : ℤ × (Fin d → ℤ) | IsMaximalAdaptedCellIn W q cap p.1 p.2})
    (fun p _ => (isOpen_adaptedCellTranslate hq p.1 (adaptedCellCenter q p.1 p.2)).measurableSet)
    (fun p hp => hsub p.1 p.2 hp) hdis
  have hrowFine (r : ℤ) : (∑' p : {p : Ifine // p.1.1.1 = r}, v p.1.1) ≤
      Cw * (3 : ℝ) ^ ((r : ℝ) - j) := by
    by_cases hr : r < (jStar : ℤ)
    · let e : {p : Ifine // p.1.1.1 = r} → {p : I // p.1.1 = r} := fun p => ⟨p.1.1, p.2⟩
      have he : Function.Injective e := by
        intro p s h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun x : {p : I // p.1.1 = r} => x.1) h
      have hfs : Summable (fun p : {p : Ifine // p.1.1.1 = r} => v p.1.1) := (hv.subtype
        _).subtype _
      have hgs : Summable (fun p : {p : I // p.1.1 = r} => v p.1) := hv.subtype _
      have hb := Summable.tsum_le_tsum_of_inj e he (fun p _ => hv0 p.1)
        (fun _ => le_rfl) hfs hgs
      exact hb.trans ((bridge_maximal_row_mass W q hq cap r (hfin r (by omega)) (volume
        W).toReal).2.le.trans
        (hrow r (by omega)))
    · let : IsEmpty {p : Ifine // p.1.1.1 = r} := ⟨fun p => by have := p.1.2; have := p.2; omega⟩
      simp only [tsum_empty]
      positivity
  have hraw := hfine m mPlus hm hmPlus newEnd (by omega) hwindow W hW Ifine
    (fun p => p.1.1.1) (fun p => adaptedCellCenter q p.1.1.1 p.1.1.2) (fun p => v p.1)
    (fun p => p.2) (fun p => hv0 p.1) (hv.subtype _) (fun p => hsub _ _ p.1.2)
    j hjJ Cw hCw.le hrowFine
  have hMmem : SchattenMemLp P (Q : ℝ) M := hraw.1
  have hTmem : SchattenMemLp P (Q : ℝ) T := Source.memLqSchatten_normalizedBlock hMmem hQ H
  have hH := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj mPlus hmPlus newEnd
  have hTdata : ∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat 0) (T a) ∧
      BlockMatLoewnerLE (T a) (blockScale ((Ct * Cw) * B * decay * X a) (Book.Ch02.blockIdentity
        d)) := by
    filter_upwards [hraw.2.1] with a ha
    have hMpsd : (toFullBlockMat (M a)).PosSemidef := by
      rw [toFullBlockMat_ofFullBlockMat]
      exact transport_positive_matrix_series _ ha.1 fun p =>
        (posDef_toFullBlockMat (isSymmetricBlockMat_coarseBlockMatrix _ (⇑a.1))
          (blockPosDef_coarseBlock_adapted q hq _ _ a)).posSemidef.smul (hv0 p.1)
    have hb : Ct * Cw * aspectRatio E * Real.sqrt (‖m‖ * ‖m⁻¹‖) *
        Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖) * X a * decay ≤ (Ct * Cw) * B * decay * X a := by
      have hPi := aspectRatio_nonneg E
      have hx := hX0 a
      dsimp only [B]
      calc
        _ = (Ct * Cw * aspectRatio E * Real.sqrt (‖m‖ * ‖m⁻¹‖) *
          Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖) * X a * decay) * 1 := (mul_one _).symm
        _ ≤ (Ct * Cw * aspectRatio E * Real.sqrt (‖m‖ * ‖m⁻¹‖) *
          Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖) * X a * decay) * K₀ := mul_le_mul_of_nonneg_left hK₀
            (by positivity)
        _ = _ := by ring
    have hn := transport_normalized_psd_bound hMpsd hH (by have := hX0 a; positivity)
      (ha.2.trans (Source.blockScale_le_blockScale_of_pos
        (blockPosDef_annealedBlock
          (by simpa only [adaptedCellTranslate, zero_add, Set.image_id',
            HighContrast.adaptedCell, HighContrast.centeredCube] using
            hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag jStar hj mPlus hmPlus
              newEnd 0)
          (fun a => by simpa only [adaptedCellTranslate, zero_add, Set.image_id',
            HighContrast.adaptedCell, HighContrast.centeredCube] using
            blockPosDef_coarseBlock_adapted qPlus hqPlus newEnd 0 a)) hb))
    refine ⟨?_, hn.2⟩
    apply (fullBlock_le_iff (by simp only [toFullBlockMat_ofFullBlockMat]; exact
      Matrix.isHermitian_zero) hn.1.isHermitian).1
    simpa only [toFullBlockMat_ofFullBlockMat] using hn.1.nonneg
  have hord := hordered P E Ψ K S hstat hdag jStar hj hsO m mPlus hm hmPlus hratio
    j newEnd hjJ hjt ell hell (adaptedCellCenter qPlus j w) ⟨w, rfl⟩ Q hQ
  have hGmem : SchattenMemLp P (Q : ℝ) G := hord.2.1
  have hseries : ∀ᵐ a ∂P, Summable (fun p : I => f p a) := hord.2.2.2.2.2
  have hIG : BlockMatLoewnerLE (Book.Ch02.blockIdentity d) MG := by
    have ho := blockMatLoewnerLE_integral (hord.1.integrable_entry hQ) (hGmem.integrable_entry hQ)
      (hord.2.2.1.mono fun _ h => h.2)
    rw [hord.2.2.2.1] at ho; exact hord.2.2.2.2.1.trans ho
  have hmass : (∑ r ∈ Finset.Icc (jStar : ℤ) cap,
      ∑ _z ∈ Z r, (volume (adaptedCell q r)).toReal / (volume W).toReal) ≤ 1 :=
    transport_finite_whitney_mass q W jStar cap hfin htotal
  constructor
  · have hb := transport_centered_whitney_bound d hd P γ E Ψ K S hstat hdag jStar hj m mPlus hm
    hmPlus
      oldEnd newEnd cap hJcap W hfin (Q : ℝ) hQ X hXi hEX ((Ct * Cw) * B * decay)
      (by positivity) δ hδ hlow hup hGmem hTmem hseries (hTdata.mono fun _ h => h.1)
      (by simpa only [mul_assoc] using hTdata.mono fun _ h => h.2)
    simpa only [mul_assoc] using! hb
  · apply hmean P E Ψ K S hstat hdag jStar hj m mPlus hm hmPlus oldEnd newEnd j cap hJcap hcapold
      (by omega) W hfin B hB X hXi hEX δ hδ hlow hup hGmem hTmem hseries
      (hTdata.mono fun _ h => h.1) (hTdata.mono fun _ h => h.2) hIG hmass
    intro r hr
    have hrc : r < cap := by have := (Finset.mem_Icc.mp hr).2; omega
    simpa only [Z, dite_eq_left hrc.le] using! hrow r hrc

end
end HCPolySupport.HighContrast.Annealed
