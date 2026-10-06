/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.TransportFluctuations

/-!
# High-contrast homogenization: Entry.Annealed.TransportProfile

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Boundary profiles for the two-grid transport

The old-history boundary and bulk profile bounds behind `p.two.grid.transport`.  All
generations at or below the cutoff `k` are dominated by one common parent-history envelope
under a single target maximum, and the actual Whitney rows are exhibited with their
mass-one identity and weighted row bounds, so the complete boundary fluctuation history is
paid by the fine profile.  The above-`k` bulk rows are then reindexed through the target
cardinalities and the two generation values and are again absorbed by the profile.
Supporting this, block subtraction is subtraction of full matrices, normalization commutes
with it, and the transported trace loses no dimensional factor; the mean-penalty split is
carried to the actual old-grid means through three ordered normalizers, and the exact
mean-weight ratio yields the printed half-`(1 - γ)` loss in `L` for the initial, later and
bulk mean rows.
-/
open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter adaptedMean blockSub blockTrace
  coarseBlock gridRatio matSqrt normalizedBlock)
open HCPolySupport.HighContrast (adaptedCell adaptedCellTranslate centeredCube
  standardCellCenter)
namespace HCPolySupport.HighContrast.Annealed
open MeasureTheory Geometry Multiscale Analysis
open scoped Matrix.Norms.L2Operator MatrixOrder Matrix
noncomputable section

/-- The boundary generations at or below k use one common parent-history
field under the complete target maximum. -/
theorem transport_old_boundary_profile (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
      (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K
      S) (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (qPlus : Mat d) (k n : ℤ) (hk : (jStar : ℤ) ≤ k) (hkn : k ≤ n) (L h : ℕ) (hcover :
      adaptedCell qPlus (n + L) ⊆ adaptedCell (explicitRoundedGrid jStar m) (n + L + h))
    {ι : Type*} (I : Finset ι) (hI : I.Nonempty) (j cap : ι → ℤ) (D : ℝ) (hD : 0 ≤ D)
    (Z : ι → ℤ → Finset (Vec d)) (v : ι → ℤ → ℝ) (hcapk : ∀ i ∈ I, cap i ≤ k) (hcapj : ∀ i ∈ I,
      cap i ≤ j i)
    (hZ : ∀ i ∈ I, ∀ r ∈ Finset.Icc (jStar : ℤ) (cap i), (Z i r : Set (Vec d)) ⊆
      adaptedLatticeAtScale (explicitRoundedGrid jStar m) r ∩ adaptedCell qPlus (n + L))
    (hv : ∀ i ∈ I, ∀ r ∈ Finset.Icc (jStar : ℤ) (cap i), 0 ≤ v i r)
    (hmass : ∀ i ∈ I, ∀ r ∈ Finset.Icc (jStar : ℤ) (cap i),
      ∑ _z ∈ Z i r, v i r ≤ D * (3 : ℝ) ^ ((r : ℝ) - j i)) :
    let q := explicitRoundedGrid jStar m
    let Q := bigQ d γ
    let Cb := D * (1 / (1 - (3 : ℝ) ^ (-(1 - rhoMax d γ))))
    (∫ a, (⨆ i ∈ (I : Set ι), (3 : ℝ) ^ (-rhoMax d γ * ((n : ℝ) + L - j i)) *
      ∑ r ∈ Finset.Icc (jStar : ℤ) (cap i), absSchattenNorm (Q : ℝ) (ofFullBlockMat
        (∑ z ∈ Z i r, v i r • toFullBlockMat (normalizedFluctuation P q r (n + 2 * (L : ℤ)) z
          a)))) ^ (Q : ℝ) ∂P) ≤
      Cb ^ Q * ((2 * (d : ℝ)) * (3 : ℝ) ^ ((Q : ℝ) * rhoMax d γ + (d : ℝ) * h)) *
        (3 : ℝ) ^ ((1 - γ) / 4 * (L : ℝ)) * profile P γ q jStar k (n + 2 * (L : ℤ)) := by
  intro q Q Cb
  classical
  let ρ := rhoMax d γ
  let T := fun i => Finset.Icc (jStar : ℤ) (cap i)
  let M := relMean P q k (n + 2 * (L : ℤ))
  let B := (2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ * (3 : ℝ) ^ ρ *
    (3 : ℝ) ^ (-ρ * ((n : ℝ) + L - k)) * blockOpNorm M
  let w := fun i => (3 : ℝ) ^ (-ρ * ((n : ℝ) + L - j i))
  let R := fun i r a => ofFullBlockMat (∑ z ∈ Z i r, v i r •
    toFullBlockMat (normalizedFluctuation P q r (n + 2 * (L : ℤ)) z a))
  let f := fun i a => w i * ∑ r ∈ T i, absSchattenNorm (Q : ℝ) (R i r a)
  have hQr := bigQ_real_pos d γ hγ
  have hQ1 : 1 ≤ (Q : ℝ) := by exact_mod_cast bigQ_pos d γ hγ
  have hρ : ρ < 1 := rhoMax_lt_one d hd γ hγ
  have hρ0 : 0 ≤ ρ := hγ.1.trans (gamma_le_rhoMax d hd γ hγ)
  have hC : 0 ≤ Cb := mul_nonneg hD (one_div_pos.mpr
    (transport_geometric_Icc (1 - ρ) (sub_pos.mpr hρ) 0 0).1).le
  have hMn : 0 ≤ blockOpNorm M := norm_nonneg _
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨X, hX0, hXmem, hXmoment, hXbound⟩ := transport_old_history_envelope d hd P γ E Ψ K S
    hstat hdag jStar hj m hm qPlus k (n + (L : ℤ)) hk (by omega) h hcover
  have hR (i r) : SchattenMemLp P (Q : ℝ) (R i r) := memLqSchatten_normalizedCentered_sum d hd P
    γ E Ψ K S hstat hdag jStar hj m hm r
      (adaptedMean P q (n + 2 * (L : ℤ))) Q hQ1 (Z i r) (fun _ => v i r) id
  have hf0 (i) (_hi : i ∈ I) : ∀ᵐ a ∂P, 0 ≤ f i a := by
    filter_upwards [(Filter.eventually_all_finset (T i)).mpr (fun r _ => (hR i r).symmetric)]
      with a ha
    exact mul_nonneg (by dsimp only [w]; positivity) (Finset.sum_nonneg fun r hr =>
      absSchattenNorm_nonneg ((toFullBlockMat_isHermitian_iff _).2 (ha r hr)) hQ1)
  have hf (i) (_hi : i ∈ I) : MemLp (f i) (ENNReal.ofReal (Q : ℝ)) P :=
    (memLp_finsetSum (T i) (fun r _ => (hR i r).memLp_absSchattenNorm hQ1)).const_mul (w i)
  have hAk := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm k
  have hAt := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm (n + 2 * (L : ℤ))
  have hfield (i) (hi : i ∈ I) : ∀ᵐ a ∂P, f i a ≤ (Cb * B) * X a := by
    have hentry (r z) := (bridge_fluctuation_memLqSchatten d hd P γ E Ψ K S hstat hdag jStar hj m hm
      r (n + 2 * (L : ℤ)) z).symmetric
    filter_upwards [(Filter.eventually_all_finset (T i)).mpr (fun r _ =>
      (Filter.eventually_all_finset (Z i r)).mpr (fun z _ => hentry r z))] with a ha
    have hxa : 0 ≤ X a := hX0 a
    have hrbound (r) (hr : r ∈ T i) : absSchattenNorm (Q : ℝ) (R i r a) ≤
        (2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ *
          ((D * (3 : ℝ) ^ ((r : ℝ) - j i)) * (blockOpNorm M * ((3 : ℝ) ^ (ρ * ((k : ℝ) - r)) * X
            a))) := by
      have hrng := Finset.mem_Icc.mp hr
      have hbound (z) (hz : z ∈ Z i r) :
          blockOpNorm (normalizedFluctuation P q r (n + 2 * (L : ℤ)) z a) ≤
            blockOpNorm M * ((3 : ℝ) ^ (ρ * ((k : ℝ) - r)) * X a) := by
        obtain ⟨u, hu⟩ := (hZ i hi r hr hz).1
        have hx := hXbound r ⟨hrng.1, hrng.2.trans (hcapk i hi)⟩ u
          (hu.symm ▸ (hZ i hi r hr hz).2) a
        rw [hu] at hx
        exact (transport_opNorm_normalizer hAk hAt
          (blockSub (coarseBlock (adaptedCellTranslate q r z) a) (adaptedMean P q r))).trans
          (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
      have hb := transport_finite_row_bound (Z i r) hQ1 (fun _ => v i r) (fun _ _ => hv i hi r hr)
        (fun z => normalizedFluctuation P q r (n + 2 * (L : ℤ)) z a)
        (fun z hz => (toFullBlockMat_isHermitian_iff _).2 (ha r hr z hz)) hbound
      have hn0 : 0 ≤ blockOpNorm M * ((3 : ℝ) ^ (ρ * ((k : ℝ) - r)) * X a) := mul_nonneg hMn
        (mul_nonneg (by positivity) (hX0 a))
      have hp := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hmass i hi r hr) hn0)
        (show 0 ≤ (2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ by positivity)
      exact hb.trans (by simpa only [mul_assoc] using hp)
    have hgeom := transport_boundary_history_below hρ (jStar : ℤ) (cap i) k (j i) (hcapj i hi)
    have he : w i * (3 : ℝ) ^ (ρ * ((k : ℝ) - j i)) =
        (3 : ℝ) ^ (-ρ * ((n : ℝ) + L - k)) := by
      dsimp only [w]; rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1; ring
    have hpre : (2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ *
        (3 : ℝ) ^ (-ρ * ((n : ℝ) + L - k)) * blockOpNorm M ≤ B := by
      calc
        _ = 1 * ((2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ *
          (3 : ℝ) ^ (-ρ * ((n : ℝ) + L - k)) * blockOpNorm M) := by ring
        _ ≤ (3 : ℝ) ^ ρ * ((2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ *
          (3 : ℝ) ^ (-ρ * ((n : ℝ) + L - k)) * blockOpNorm M) :=
          mul_le_mul_of_nonneg_right (Real.one_le_rpow (by norm_num) hρ0) (by positivity)
        _ = B := by dsimp only [B]; ring
    calc
      _ ≤ w i * ∑ r ∈ T i, (2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ *
          ((D * (3 : ℝ) ^ ((r : ℝ) - j i)) * (blockOpNorm M * ((3 : ℝ) ^ (ρ * ((k : ℝ) - r)) * X
            a))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hrbound) (by dsimp only [w]; positivity)
      _ = ((2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ * D * blockOpNorm M * w i * X a) *
          ∑ r ∈ T i, (3 : ℝ) ^ ((r : ℝ) - j i) * (3 : ℝ) ^ (ρ * ((k : ℝ) - r)) := by
        simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _; ring
      _ ≤ ((2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ * D * blockOpNorm M * w i * X a) *
          ((1 / (1 - (3 : ℝ) ^ (-(1 - ρ)))) * (3 : ℝ) ^ (ρ * ((k : ℝ) - j i))) :=
        mul_le_mul_of_nonneg_left hgeom (by dsimp only [w]; positivity)
      _ = Cb * ((2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ * blockOpNorm M) *
          (w i * (3 : ℝ) ^ (ρ * ((k : ℝ) - j i))) * X a := by dsimp only [Cb, ρ]; ring
      _ = Cb * ((2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ *
          (3 : ℝ) ^ (-ρ * ((n : ℝ) + L - k)) * blockOpNorm M) * X a := by rw [he]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpre hC) (hX0 a)
  have hb := (transport_joint_envelope_moment hQr (mul_nonneg hC hB) I hI f hf0 hf
    X (ae_of_all P hX0) hXmem hfield).2
  simp only [Real.rpow_natCast, mul_pow] at hb
  have hpay := transport_old_history_profile_payment d hd P γ E Ψ K S hstat hdag jStar hj m hm k
    n hk hkn L h
  calc
    _ ≤ (Cb ^ Q * B ^ Q) * ∫ a, X a ^ Q ∂P := by simpa only [Real.rpow_natCast] using hb
    _ ≤ (Cb ^ Q * B ^ Q) * ((3 : ℝ) ^ (d * ((n + (L : ℤ) - k).toNat + h)) *
        fluctuationHistory P γ q jStar k) := mul_le_mul_of_nonneg_left hXmoment (by positivity)
    _ = Cb ^ Q * (B ^ Q * ((3 : ℝ) ^ (d * ((n + (L : ℤ) - k).toNat + h)) *
        fluctuationHistory P γ q jStar k)) := by ring
    _ ≤ Cb ^ Q * (((2 * (d : ℝ)) * (3 : ℝ) ^ ((Q : ℝ) * rhoMax d γ + (d : ℝ) * h)) *
        (3 : ℝ) ^ ((1 - γ) / 4 * (L : ℝ)) * profile P γ q jStar k (n + 2 * (L : ℤ))) :=
      mul_le_mul_of_nonneg_left hpay (pow_nonneg hC Q)
    _ = _ := by ring
/-- The actual Whitney rows supply all row guards simultaneously.
The mass-one identity also pays the cap row, including an empty row. -/
theorem exists_transport_whitney_rows (d : ℕ) (hd : 2 ≤ d)
    (K₀ : ℝ) (hK₀ : 1 ≤ K₀) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧ ∃ C : ℝ, 0 < C ∧
      ∀ K : ℝ, 1 < K → ∀ jStar : ℕ, 2 * d ≤ 3 ^ jStar →
      ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
      ∀ m mPlus : Mat d, m.PosDef → mPlus.PosDef →
      gridRatio (explicitRoundedGrid jStar m) (explicitRoundedGrid jStar mPlus) ≤ K₀ →
      ∀ (k t : ℤ) (L : ℕ), 1 ≤ L →
      let q := explicitRoundedGrid jStar m
      let qPlus := explicitRoundedGrid jStar mPlus
      let ell := fun j : ℤ => if j ≤ k + (L : ℤ) then 1 else L
      let cap := fun j : ℤ => j - (ell j : ℤ)
      let W := fun p : ℤ × (Fin d → ℤ) => adaptedCellAtCenter qPlus p.1 p.2
      ∀ (I : Finset (ℤ × (Fin d → ℤ))), (∀ p ∈ I, p.1 ≤ t) →
        (∀ p ∈ I, standardCellCenter p.1 p.2 ∈ centeredCube d t) →
      ∃ hfin : ∀ p : ℤ × (Fin d → ℤ), ∀ r : ℤ, r ≤ cap p.1 →
          (maximalAdaptedCellCenters (W p) q (cap p.1) r).Finite,
        let Z := fun p r => if hr : r ≤ cap p.1 then (hfin p r hr).toFinset else ∅
        let v := fun p r => (volume (adaptedCell q r)).toReal / (volume (W p)).toReal
        ∀ p ∈ I,
          (∀ r ≤ cap p.1, (Z p r : Set (Vec d)) ⊆ adaptedLatticeAtScale q r ∩ adaptedCell qPlus t) ∧
          (∑ _z ∈ Z p (cap p.1), v p (cap p.1)) ≤ 1 ∧
          (∑ _z ∈ Z p (cap p.1), v p (cap p.1) ^ 2) ^ ((1 : ℝ) / 2) ≤
            C * (3 : ℝ) ^ (-(d : ℝ) / 2 * (ell p.1 : ℝ)) ∧
          ∀ r < cap p.1,
            (∑ _z ∈ Z p r, v p r ^ 2) ^ ((1 : ℝ) / 2) ≤
              C * (3 : ℝ) ^ (-((d : ℝ) + 1) / 2 * ((p.1 : ℝ) - r)) ∧
            (∑ _z ∈ Z p r, v p r) ≤ C * (3 : ℝ) ^ ((r : ℝ) - p.1) := by
  classical
  obtain ⟨Cs, hCs, C, hC, hdata⟩ := exists_transport_whitney_coefficients d hd K₀ hK₀ γ hγ
  refine ⟨Cs, hCs, C, hC, ?_⟩
  intro K hK jStar hj hsrc m mPlus hm hmPlus hratio k t L hL q qPlus ell cap W I hgen hcenter
  have hell (j : ℤ) : 1 ≤ ell j := by dsimp only [ell]; split_ifs <;> omega
  have hget (p : ℤ × (Fin d → ℤ)) := hdata K hK jStar hj hsrc m mPlus hm hmPlus hratio
    p.1 (ell p.1) (hell p.1) (adaptedCellCenter qPlus p.1 p.2) ⟨p.2, rfl⟩
  choose hfin hrows using hget
  refine ⟨hfin, ?_⟩
  intro Z v p hp
  have hpt := hgen p hp
  have hgap : p.1 + ((t - p.1).toNat : ℤ) = t := by omega
  have hW : W p ⊆ adaptedCell qPlus t := by
    have hh := (aligned_adapted_partition qPlus (isUnit_roundedGrid hj hmPlus) p.1
      (t - p.1).toNat).1 p.2 (by simpa only [hgap] using! hcenter p hp)
    simpa only [hgap] using hh
  have htotal : (∑' r : {r : ℤ // r ≤ cap p.1},
      ∑ _z ∈ (hfin p r.1 r.2).toFinset, v p r.1) = 1 := (hrows p).1
  have hs : Summable (fun r : {r : ℤ // r ≤ cap p.1} =>
      ∑ _z ∈ (hfin p r.1 r.2).toFinset, v p r.1) := by
    by_contra hn
    rw [tsum_eq_zero_of_not_summable hn] at htotal; norm_num at htotal
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr z hz
    have hz' : z ∈ maximalAdaptedCellCenters (W p) q (cap p.1) r := (hfin p r
      hr).mem_toFinset.mp (by simpa only [Z, dite_eq_left hr] using! hz)
    have hh := transport_maximal_centers_subset (W p) q (cap p.1) r hz'
    exact ⟨hh.1, hW hh.2⟩
  · have hh := hs.sum_le_tsum ({⟨cap p.1, le_rfl⟩} : Finset {r : ℤ // r ≤ cap p.1})
      (fun _ _ => Finset.sum_nonneg fun _ _ => by dsimp only [v]; positivity)
    rw [htotal] at hh
    simpa only [Z, dite_eq_left le_rfl, Finset.sum_singleton] using! hh
  · simpa only [Z, dite_eq_left le_rfl] using! (hrows p).2.1
  · intro r hr
    simpa only [Z, dite_eq_left hr.le] using! (hrows p).2.2 r hr
/-- The printed boundary fluctuation estimate for the actual Whitney rows,
with the old and averaged generations combined under one joint maximum. -/
theorem exists_transport_boundary_fluctuations (d : ℕ) (hd : 2 ≤ d)
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
        let Z := fun p r => if hr : r ≤ cap p.1 then (hfin p r hr).toFinset else ∅
        let v := fun p r => (volume (adaptedCell q r)).toReal / (volume (W p)).toReal
        (∫ a, (⨆ p ∈ (I : Set (ℤ × (Fin d → ℤ))),
          (3 : ℝ) ^ (-rhoMax d γ * ((n : ℝ) + L - p.1)) *
            ∑ r ∈ Finset.Icc (jStar : ℤ) (cap p.1 - 1), absSchattenNorm (Q : ℝ)
              (ofFullBlockMat (∑ z ∈ Z p r, v p r • toFullBlockMat
                (normalizedFluctuation P q r (n + 2 * (L : ℤ)) z a)))) ^ (Q : ℝ) ∂P) ≤
          C * (3 : ℝ) ^ ((1 - γ) / 4 * (L : ℝ)) * profile P γ q jStar k (n + 2 * (L : ℤ)) := by
  classical
  obtain ⟨Cr, hCr, D, hD, hrows⟩ := exists_transport_whitney_rows d hd K₀ hK₀ γ hγ
  obtain ⟨Cb, hCb, hhigh⟩ := exists_transport_high_boundary_profile d hd γ hγ
  obtain ⟨h, hcover⟩ := exists_transport_parent_enlargement d hd K₀ hK₀
  let β := ((d : ℝ) + 1) / 2 - (1 - γ) / (4 * (bigQ d γ : ℝ))
  let G := 1 / (1 - (3 : ℝ) ^ (-(1 - rhoMax d γ)))
  let M := 1 + 1 / (1 - (3 : ℝ) ^ (-β))
  let B := (D * G) ^ bigQ d γ * ((2 * (d : ℝ)) * (3 : ℝ) ^ ((bigQ d γ : ℝ) * rhoMax d γ + (d :
    ℝ) * h))
  let H := M ^ (bigQ d γ + 1) * ((bigQ d γ : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) * D) ^ bigQ d γ
  have hβ : 0 < β := transport_boundary_decay_pos d hd γ hγ
  have hG : 0 < G := one_div_pos.mpr
    (transport_geometric_Icc (1 - rhoMax d γ) (sub_pos.mpr (rhoMax_lt_one d hd γ hγ)) 0 0).1
  have hM : 0 < M := by
    have hp := one_div_pos.mpr (transport_geometric_Icc β hβ 0 0).1
    dsimp only [M]; linarith only [hp]
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  refine ⟨max Cr Cb, hCr.trans_le (le_max_left _ _), (2 : ℝ) ^ bigQ d γ * (B + H) + 1, by
    positivity, ?_⟩
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
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hP0 := bridge_profile_nonneg d hd P γ E Ψ K S hstat hdag jStar hj m hm k (n + 2 * (L :
    ℤ)) hk (by omega)
  have hQ : 0 < Q := bigQ_pos d γ hγ
  have hQ1 : 1 ≤ (Q : ℝ) := by exact_mod_cast hQ
  by_cases hI : I.Nonempty
  swap
  · have hp : 0 ≤ ((2 : ℝ) ^ Q * (B + H) + 1) * c * profile P γ q jStar k (n + 2 * (L : ℤ)) :=
    mul_nonneg (mul_nonneg (by positivity) hc) hP0
    simpa [Finset.not_nonempty_iff_eq_empty.mp hI, Real.rpow_natCast, zero_pow (Nat.ne_of_gt
      hQ)] using hp
  let lo := fun p : ℤ × (Fin d → ℤ) => min k (cap p.1 - 1)
  let T := fun j => Finset.Icc (k + 1) (cap j - 1)
  let R := fun p r a => ofFullBlockMat (∑ z ∈ Z p r, v p r • toFullBlockMat
    (normalizedFluctuation P q r (n + 2 * (L : ℤ)) z a))
  let w := fun p : ℤ × (Fin d → ℤ) => (3 : ℝ) ^ (-rhoMax d γ * ((n : ℝ) + L - p.1))
  let Fl := fun p a => w p * ∑ r ∈ Finset.Icc (jStar : ℤ) (lo p), absSchattenNorm (Q : ℝ) (R p r a)
  let Fh := fun p a => w p * ∑ r ∈ T p.1, absSchattenNorm (Q : ℝ) (R p r a)
  have hcapj (j : ℤ) : cap j ≤ j := by dsimp only [cap]; omega
  have hrlo (p) {r : ℤ} (hr : r ∈ Finset.Icc (jStar : ℤ) (lo p)) : r < cap p.1 := by
    have hh := (Finset.mem_Icc.mp hr).2
    dsimp only [lo] at hh; omega
  have hl : (∫ a, (⨆ p ∈ (I : Set (ℤ × (Fin d → ℤ))), Fl p a) ^ (Q : ℝ) ∂P) ≤
      B * c * profile P γ q jStar k (n + 2 * (L : ℤ)) := by
    apply transport_old_boundary_profile d hd P γ hγ E Ψ K S hstat hdag jStar hj m hm qPlus k n
      hk hkn L h
      (hcover q qPlus (isUnit_roundedGrid hj hm) hratio (n + (L : ℤ))) I hI Prod.fst lo D hD.le Z v
    · exact fun p _ => min_le_left _ _
    · intro p _
      exact (min_le_right _ _).trans (by have hh := hcapj p.1; omega)
    · exact fun p hp r hr => (hdata p hp).1 r (hrlo p hr).le
    · exact fun p _ r _ => by dsimp only [v]; positivity
    · exact fun p hp r hr => ((hdata p hp).2.2.2 r (hrlo p hr)).2
  have hh : (∫ a, (⨆ p ∈ (I : Set (ℤ × (Fin d → ℤ))), Fh p a) ^ (Q : ℝ) ∂P) ≤
      H * c * profile P γ q jStar k (n + 2 * (L : ℤ)) := by
    apply hhigh P E Ψ K S hP hstat hunit hdag jStar hj hsB m hm k n hk hkn L D hD.le I hI T Z v
    · intro j _ r hr
      have hh := Finset.mem_Icc.mp hr
      exact Finset.mem_Icc.mpr ⟨hh.1, hh.2.trans (by have hh := hcapj j; omega)⟩
    · exact fun p hp => (hgen p hp).2
    · intro j hjmem
      simpa only [Int.cast_add, Int.cast_natCast] using transport_target_fiber_card I (n + (L : ℤ))
        (fun p hp => (hgen p hp).2) hcenter j hjmem
    · intro p hp r hr z hz
      have hr' : r < cap p.1 := by have hh := (Finset.mem_Icc.mp hr).2; omega
      exact ((hdata p hp).1 r hr'.le hz).1
    · exact fun p _ r _ => by dsimp only [v]; positivity
    · intro p hp r hr
      have hr' : r < cap p.1 := by have hh := (Finset.mem_Icc.mp hr).2; omega
      exact ((hdata p hp).2.2.2 r hr').1
  have hR (p r) : SchattenMemLp P (Q : ℝ) (R p r) := memLqSchatten_normalizedCentered_sum d hd P
    γ E Ψ K S hstat hdag jStar hj m hm
      r (adaptedMean P q (n + 2 * (L : ℤ))) Q hQ1 (Z p r) (fun _ => v p r) id
  have hf0 (p) (A : Finset ℤ) : ∀ᵐ a ∂P, 0 ≤ w p * ∑ r ∈ A, absSchattenNorm (Q : ℝ) (R p r a) := by
    filter_upwards [(Filter.eventually_all_finset A).mpr (fun r _ => (hR p r).symmetric)] with a ha
    exact mul_nonneg (by dsimp only [w]; positivity) (Finset.sum_nonneg fun r hr =>
      absSchattenNorm_nonneg ((toFullBlockMat_isHermitian_iff _).2 (ha r hr)) hQ1)
  have hfmem (p) (A : Finset ℤ) : MemLp (fun a => w p * ∑ r ∈ A, absSchattenNorm (Q : ℝ) (R p r a))
      (ENNReal.ofReal (Q : ℝ)) P :=
    (memLp_finsetSum A (fun r _ => (hR p r).memLp_absSchattenNorm hQ1)).const_mul (w p)
  have ht := transport_joint_sum_moment Q hQ I hI Fl Fh
    (fun p _ => hf0 p _) (fun p _ => hf0 p _) (fun p _ => hfmem p _) (fun p _ => hfmem p _)
  have hsplit (p : ℤ × (Fin d → ℤ)) (a : CoeffSpace d) :
      w p * ∑ r ∈ Finset.Icc (jStar : ℤ) (cap p.1 - 1), absSchattenNorm (Q : ℝ) (R p r a) = Fl p
        a + Fh p a := by
    have he : Finset.Icc (jStar : ℤ) (cap p.1 - 1) = Finset.Icc (jStar : ℤ) (lo p) ∪ T p.1 := by
      ext r; simp only [lo, T, Finset.mem_Icc, Finset.mem_union]; omega
    have hdis : Disjoint (Finset.Icc (jStar : ℤ) (lo p)) (T p.1) := by
      apply Finset.disjoint_left.mpr
      intro r hr hs
      have hr' := Finset.mem_Icc.mp hr
      have hs' := Finset.mem_Icc.mp hs
      dsimp only [lo] at hr'; omega
    rw [he, Finset.sum_union hdis]; exact mul_add _ _ _
  have he (a : CoeffSpace d) :
      (⨆ p ∈ (I : Set (ℤ × (Fin d → ℤ))), w p *
        ∑ r ∈ Finset.Icc (jStar : ℤ) (cap p.1 - 1), absSchattenNorm (Q : ℝ) (R p r a)) =
      (⨆ p ∈ (I : Set (ℤ × (Fin d → ℤ))), Fl p a + Fh p a) :=
    iSup_congr fun p => iSup_congr fun _ => hsplit p a
  have hie := integral_congr_ae (ae_of_all P (fun a => congrArg (fun x : ℝ => x ^ (Q : ℝ)) (he a)))
  calc
    _ = ∫ a, (⨆ p ∈ (I : Set (ℤ × (Fin d → ℤ))), Fl p a + Fh p a) ^ (Q : ℝ) ∂P := hie
    _ ≤ _ := ht
    _ ≤ (2 : ℝ) ^ Q * ((B + H) * c * profile P γ q jStar k (n + 2 * (L : ℤ))) :=
      (mul_le_mul_of_nonneg_left (add_le_add hl hh) (by positivity)).trans_eq (by ring)
    _ ≤ _ := by
      have hp := mul_nonneg hc hP0
      nlinarith only [hp]
/-- The above-k bulk rows are paid by the last sum in the actual profile.
Target cardinalities enter before the two-value generation reindexing. -/
theorem exists_transport_high_bulk_profile (d : ℕ) (hd : 2 ≤ d)
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
      let ell := fun j : ℤ => if j ≤ k + (L : ℤ) then 1 else L
      let r := fun j : ℤ => j - (ell j : ℤ)
      ∀ (I : Finset (ℤ × (Fin d → ℤ))), I.Nonempty →
      ∀ (Z : ℤ × (Fin d → ℤ) → Finset (Vec d)) (v : ℤ × (Fin d → ℤ) → ℝ),
      (∀ i ∈ I, r i.1 ∈ Finset.Icc (k + 1) (n + 2 * (L : ℤ))) →
      (∀ i ∈ I, i.1 ≤ n + (L : ℤ)) →
      (∀ j ∈ I.image Prod.fst, ((I.filter (fun i => i.1 = j)).card : ℝ) ≤
        (3 : ℝ) ^ ((d : ℝ) * ((n : ℝ) + L - j))) →
      (∀ i ∈ I, (Z i : Set (Vec d)) ⊆ adaptedLatticeAtScale q (r i.1)) →
      (∀ i ∈ I, 0 ≤ v i) →
      (∀ i ∈ I, (∑ _z ∈ Z i, v i ^ 2) ^ ((1 : ℝ) / 2) ≤
        D * (3 : ℝ) ^ (-(d : ℝ) / 2 * (ell i.1 : ℝ))) →
      (∫ a, (⨆ i ∈ (I : Set (ℤ × (Fin d → ℤ))),
        (3 : ℝ) ^ (-rhoMax d γ * ((n : ℝ) + L - i.1)) *
          absSchattenNorm (Q : ℝ) (ofFullBlockMat (∑ z ∈ Z i, v i •
            toFullBlockMat (normalizedFluctuation P q (r i.1) (n + 2 * (L : ℤ)) z a)))) ^ (Q :
              ℝ) ∂P) ≤
        2 * ((Q : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) * D) ^ Q *
          (3 : ℝ) ^ ((1 - γ) / 4 * (L : ℝ)) * profile P γ q jStar k (n + 2 * (L : ℤ)) := by
  classical
  obtain ⟨Cs, hCs, hrow⟩ := exists_transport_lattice_row_moment d hd γ hγ
  refine ⟨Cs, hCs, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag jStar hj hsrc m hm k n hk hkn L D hD
    q Q ell r I hI Z v hgen hjt hcount hZ hv hcoef
  let := hP
  let t := n + 2 * (L : ℤ)
  let A := ((Q : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) * D) ^ Q
  let c := (3 : ℝ) ^ ((1 - γ) / 4 * (L : ℝ))
  let w := fun j : ℤ => (3 : ℝ) ^ (-rhoMax d γ * ((n : ℝ) + L - j))
  let R := fun i a => ofFullBlockMat (∑ z ∈ Z i, v i •
    toFullBlockMat (normalizedFluctuation P q (r i.1) t z a))
  let f := fun i a => w i.1 * absSchattenNorm (Q : ℝ) (R i a)
  let B := fun j : ℤ => ((3 : ℝ) ^ (-(d : ℝ) / 2 * (ell j : ℝ))) ^ Q *
    Real.exp ((Q : ℝ) * detIncrement P q (r j) t) *
      ∫ a, absSchattenNorm (Q : ℝ) (normalizedFluctuationSelf P q (r j) a) ^ Q ∂P
  let F := fun u : ℤ => (3 : ℝ) ^ (-((1 - γ) / 4) * ((t : ℝ) - u)) *
    Real.exp ((Q : ℝ) * detIncrement P q u t) *
      ∫ a, absSchattenNorm (Q : ℝ) (normalizedFluctuationSelf P q u a) ^ Q ∂P
  have hQ := bigQ_pos d γ hγ
  have hQr := bigQ_real_pos d γ hγ
  have hQ1 : 1 ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hR (i) : SchattenMemLp P (Q : ℝ) (R i) := memLqSchatten_normalizedCentered_sum d hd P γ E
    Ψ K S hstat hdag jStar hj m hm
      (r i.1) (adaptedMean P q t) Q hQ1 (Z i) (fun _ => v i) id
  have hself (u) : SchattenMemLp P (Q : ℝ) (normalizedFluctuationSelf P q u) :=
    bridge_fluctuation_memLqSchatten d hd P γ E Ψ K S hstat hdag jStar hj m hm u u 0
  have hm0 (u) : 0 ≤ ∫ a, absSchattenNorm (Q : ℝ) (normalizedFluctuationSelf P q u a) ^ Q ∂P := by
    apply integral_nonneg_of_ae
    filter_upwards [(hself u).symmetric] with a ha
    exact pow_nonneg (absSchattenNorm_nonneg ((toFullBlockMat_isHermitian_iff _).2 ha) hQ1) Q
  have hF0 (u : ℤ) : 0 ≤ F u := mul_nonneg (by positivity) (hm0 u)
  have hB0 (j : ℤ) : 0 ≤ B j := mul_nonneg (by positivity) (hm0 (r j))
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hf0 (i) (_hi : i ∈ I) : ∀ᵐ a ∂P, 0 ≤ f i a :=
    (hR i).symmetric.mono fun _ ha => mul_nonneg (by dsimp only [w]; positivity)
      (absSchattenNorm_nonneg ((toFullBlockMat_isHermitian_iff _).2 ha) hQ1)
  have hf (i) (_hi : i ∈ I) : MemLp (f i) (ENNReal.ofReal (Q : ℝ)) P := ((hR
    i).memLp_absSchattenNorm hQ1).const_mul (w i.1)
  have hmom (i) (hi : i ∈ I) : (∫ a, f i a ^ (Q : ℝ) ∂P) ≤ w i.1 ^ Q * (A * B i.1) := by
    have hrng := Finset.mem_Icc.mp (hgen i hi)
    have hb := hrow P E Ψ K S hP hstat hunit hdag jStar hj hsrc m hm (r i.1) t (by omega) hrng.2
      (Z i) (hZ i hi) (v i) (hv i hi) (D * (3 : ℝ) ^ (-(d : ℝ) / 2 * (ell i.1 : ℝ))) (hcoef i hi)
    have he : (∫ a, f i a ^ (Q : ℝ) ∂P) =
        w i.1 ^ Q * ∫ a, absSchattenNorm (Q : ℝ) (R i a) ^ Q ∂P := by
      simp only [f, Real.rpow_natCast, mul_pow, integral_const_mul]
    rw [he]
    apply mul_le_mul_of_nonneg_left _ (by dsimp only [w]; positivity)
    apply hb.trans_eq
    dsimp only [A, B]
    rw [show (Q : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) *
        (D * (3 : ℝ) ^ (-(d : ℝ) / 2 * (ell i.1 : ℝ))) =
        ((Q : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) * D) *
          (3 : ℝ) ^ (-(d : ℝ) / 2 * (ell i.1 : ℝ)) by ring, mul_pow]
    ring
  have hscale (j : ℤ) (hjmem : j ∈ I.image Prod.fst) :
      w j ^ Q * (3 : ℝ) ^ ((d : ℝ) * ((n : ℝ) + L - j)) * B j ≤ c * F (r j) := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hjmem
    have hb := transport_bulk_high_weight d hd γ hγ n i.1 L (ell i.1) (hjt i hi)
    have hw : w i.1 ^ Q = (3 : ℝ) ^ (-(Q : ℝ) * rhoMax d γ * ((n : ℝ) + L - i.1)) := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1; ring
    dsimp only [B, F, c]; rw [hw]
    have hpay := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (Real.exp_pos ((Q :
      ℝ) * detIncrement P q (r i.1) t)).le) (hm0 (r i.1))
    simpa only [t, r, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
      Int.cast_natCast, mul_assoc] using hpay
  have hmap : ∀ j ∈ I.image Prod.fst, j - (if j ≤ k + (L : ℤ) then 1 else (L : ℤ)) ∈
      Finset.Icc (k + 1) t := by
    intro j hjmem
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hjmem
    have he : (ell i.1 : ℤ) = if i.1 ≤ k + (L : ℤ) then 1 else (L : ℤ) := by
      dsimp only [ell]; split_ifs <;> rfl
    simpa only [r, he] using hgen i hi
  have hsum := transport_bulk_generation_sum k L (I.image Prod.fst) (Finset.Icc (k + 1) t)
    F (fun u _ => hF0 u) hmap
  have he (j : ℤ) : j - (if j ≤ k + (L : ℤ) then 1 else (L : ℤ)) = r j := by
    dsimp only [r, ell]; split_ifs <;> rfl
  simp only [he] at hsum
  have hpay : (∑ u ∈ Finset.Icc (k + 1) t, F u) ≤ profile P γ q jStar k t :=
    (transport_profile_components d hd P γ E Ψ K S hstat hdag jStar hj m hm k t hk (by omega)).2.2.2
  calc
    _ ≤ ∑ i ∈ I, ∫ a, f i a ^ (Q : ℝ) ∂P := (transport_target_max_moment hQr I hI f hf0 hf).2
    _ ≤ ∑ i ∈ I, w i.1 ^ Q * (A * B i.1) := Finset.sum_le_sum hmom
    _ = ∑ j ∈ I.image Prod.fst, ((I.filter (fun i => i.1 = j)).card : ℝ) *
        (w j ^ Q * (A * B j)) := by
      have himage : ∀ i ∈ I, i.1 ∈ I.image Prod.fst :=
        fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩
      rw [← Finset.sum_fiberwise_of_maps_to himage
        (fun i : ℤ × (Fin d → ℤ) => w i.1 ^ Q * (A * B i.1))]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2]),
        Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ I.image Prod.fst, A * (c * F (r j)) := by
      apply Finset.sum_le_sum
      intro j hjmem
      calc
        _ ≤ (3 : ℝ) ^ ((d : ℝ) * ((n : ℝ) + L - j)) * (w j ^ Q * (A * B j)) :=
          mul_le_mul_of_nonneg_right (hcount j hjmem) (mul_nonneg (by dsimp only [w]; positivity)
            (mul_nonneg hA (hB0 j)))
        _ = A * (w j ^ Q * (3 : ℝ) ^ ((d : ℝ) * ((n : ℝ) + L - j)) * B j) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hscale j hjmem) hA
    _ = A * c * ∑ j ∈ I.image Prod.fst, F (r j) := by simp only [mul_assoc, ← Finset.mul_sum]
    _ ≤ A * c * (2 * ∑ u ∈ Finset.Icc (k + 1) t, F u) := mul_le_mul_of_nonneg_left hsum
      (mul_nonneg hA hc)
    _ ≤ A * c * (2 * profile P γ q jStar k t) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hpay (by norm_num)) (mul_nonneg hA hc)
    _ = _ := by ring
/-- Trace transport for a positive matrix, with no dimensional loss. -/
theorem transport_normalized_trace_le {d : ℕ} {X R S : BlockMat d} (hX : (toFullBlockMat
  X).PosSemidef)
    (hR : (toFullBlockMat R).PosDef) (hS : (toFullBlockMat S).PosDef) :
    blockTrace (normalizedBlock X S) ≤
      blockOpNorm (normalizedBlock R S) * blockTrace (normalizedBlock X R) := by
  have hpos (A : BlockMat d) (hA : (toFullBlockMat A).PosDef) :
      (toFullBlockMat (normalizedBlock X A)).PosSemidef := by
    have hs := matSqrt_inv_posDef_full hA
    simpa only [normalizedBlock, toFullBlockMat_ofFullBlockMat, hs.isHermitian.eq] using
      hX.conjTranspose_mul_mul_same (matSqrt (toFullBlockMat A)⁻¹)
  have hh := absSchattenNorm_congr_le (normalizedBlock X R) (bridgeMap R S) (hpos R hR).isHermitian
    (N := 1) le_rfl
  rw [← normalizedBlock_transport_congr hR hS X, ofFullBlockMat_toFullBlockMat,
    absSchattenNorm_one_eq_blockTrace (hpos S hS), absSchattenNorm_one_eq_blockTrace (hpos R hR),
    transportMatrix_sq_opNorm_eq_general hR hS] at hh
  exact hh
/-- The printed mean-penalty split for three ordered positive normalizers. -/
theorem transport_meanPenalty_split {d : ℕ} (Q : ℕ) (A B C : BlockMat d) (hA : (toFullBlockMat
  A).PosDef) (hB : (toFullBlockMat B).PosDef) (hC : (toFullBlockMat C).PosDef)
    (hBA : BlockMatLoewnerLE B A) (hCB : BlockMatLoewnerLE C B) :
    meanPenalty Q (normalizedBlock A C) ≤
      (1 + meanPenalty Q (normalizedBlock B C)) * meanPenalty Q (normalizedBlock A B) +
        meanPenalty Q (normalizedBlock B C) := by
  let I := Book.Ch02.blockIdentity d
  let x := blockTrace (blockSub (normalizedBlock A C) I)
  let a := blockTrace (blockSub (normalizedBlock A B) I)
  let b := blockTrace (blockSub (normalizedBlock B C) I)
  have hCA : BlockMatLoewnerLE C A := fun X => (hCB X).trans (hBA X)
  have hx : 0 ≤ x := blockTrace_identity_sub_nonneg _ ((toFullBlockMat_isHermitian_iff _).1
    (normalizedBlock_posDef A C hA hC).isHermitian)
    (normalizedBlock_order_consequences Q A C hA hC hCA).1
  have ha : 0 ≤ a := blockTrace_identity_sub_nonneg _ ((toFullBlockMat_isHermitian_iff _).1
    (normalizedBlock_posDef A B hA hB).isHermitian)
    (normalizedBlock_order_consequences Q A B hA hB hBA).1
  have hb : 0 ≤ b := blockTrace_identity_sub_nonneg _ ((toFullBlockMat_isHermitian_iff _).1
    (normalizedBlock_posDef B C hB hC).isHermitian)
    (normalizedBlock_order_consequences Q B C hB hC hCB).1
  have hgap : (toFullBlockMat (blockSub A B)).PosSemidef := by
    rw [toFullBlockMat_blockSub_annealed]; exact Matrix.le_iff.mp ((fullBlock_le_iff
      hB.isHermitian hA.isHermitian).2 hBA)
  have ht := transport_normalized_trace_le hgap hB hC
  rw [normalizedBlock_blockSub, normalizedBlock_blockSub, normalizedBlock_self_of_posDef B hB] at ht
  have hn := blockOpNorm_le_one_add_trace (normalizedBlock B C) (normalizedBlock_posDef B C hB
    hC).isHermitian
    (normalizedBlock_order_consequences Q B C hB hC hCB).1
  have he : x = blockTrace (blockSub (normalizedBlock A C) (normalizedBlock B C)) + b := by
    simp only [x, b, blockTrace, toFullBlockMat_blockSub_annealed, Matrix.trace_sub]
    ring
  have ht' : blockTrace (blockSub (normalizedBlock A C) (normalizedBlock B C)) ≤
      blockOpNorm (normalizedBlock B C) * a := ht
  have hn' : blockOpNorm (normalizedBlock B C) ≤ 1 + b := hn
  have hbound : x ≤ a * (1 + b) + b := by
    calc
      x = blockTrace (blockSub (normalizedBlock A C) (normalizedBlock B C)) + b := he
      _ ≤ blockOpNorm (normalizedBlock B C) * a + b := add_le_add ht' le_rfl
      _ ≤ (1 + b) * a + b := add_le_add (mul_le_mul_of_nonneg_right hn' ha) le_rfl
      _ = _ := by ring
  change (1 + x) ^ Q - 1 ≤ (1 + ((1 + b) ^ Q - 1)) * ((1 + a) ^ Q - 1) + ((1 + b) ^ Q - 1)
  calc
    _ ≤ ((1 + a) * (1 + b)) ^ Q - 1 := sub_le_sub_right (pow_le_pow_left₀ (by linarith only
      [hx]) (by nlinarith only [hbound]) Q) 1
    _ = _ := by rw [mul_pow]; ring
/-- The same split at the actual old-grid means; all order and positivity
hypotheses come from the standing law and the generation order. -/
theorem transport_meanPenalty_split_scales (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ)
      (K : ℝ) (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger
      P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (r k t : ℤ) (hr : (jStar : ℤ) ≤ r) (hrk : r ≤ k) (hkt : k ≤ t) :
    let q := explicitRoundedGrid jStar m
    meanPenalty (bigQ d γ) (relMean P q r t) ≤
      (1 + meanPenalty (bigQ d γ) (relMean P q k t)) *
        meanPenalty (bigQ d γ) (relMean P q r k) +
          meanPenalty (bigQ d γ) (relMean P q k t) := by
  intro q; exact transport_meanPenalty_split (bigQ d γ) (adaptedMean P q r) (adaptedMean P q k)
    (adaptedMean P q t) (adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm r)
    (adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm k) (adaptedMean_posDef d hd P
      γ E Ψ K S hstat hdag jStar hj m hm t)
    (adaptedMean_antitone d hd P γ E Ψ K S hstat hdag jStar hj m hm r k hr hrk)
      (adaptedMean_antitone d hd P γ E Ψ K S hstat hdag jStar hj m hm k t (hr.trans hrk) hkt)
/-- The exact mean-weight ratio gives the printed half-(1-gamma) loss in L. -/
theorem transport_mean_weight_ratio (γ : ℝ) (hγ : γ < 1) (n j : ℤ) (L ell : ℕ) (hell : ell ≤ L) :
    (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) + L - 1 - j)) =
      (3 : ℝ) ^ ((1 - γ) / 4 * ((L : ℝ) + ell)) *
        (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) + 2 * L - 1 - ((j : ℝ) - ell))) ∧
    (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) + L - 1 - j)) ≤
      (3 : ℝ) ^ ((1 - γ) / 2 * (L : ℝ)) *
        (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) + 2 * L - 1 - ((j : ℝ) - ell))) := by
  have he : (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) + L - 1 - j)) =
      (3 : ℝ) ^ ((1 - γ) / 4 * ((L : ℝ) + ell)) *
        (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) + 2 * L - 1 - ((j : ℝ) - ell))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1; ring
  refine ⟨he, he.trans_le ?_⟩
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hh : (ell : ℝ) ≤ L := by exact_mod_cast hell
  nlinarith only [hh, hγ]
/-- The initial mean history is part of the first profile summand. -/
theorem transport_initial_mean_history (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (γ : ℝ) (_hγ : γ ∈ Set.Ico (0 : ℝ) 1)
      (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K
      S) (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (k t : ℤ) (hk : (jStar : ℤ) ≤ k) (hkt : k ≤ t) :
    let q := explicitRoundedGrid jStar m
    (3 : ℝ) ^ (-((1 - γ) / 4) * ((t : ℝ) - k)) *
      (1 + meanPenalty (bigQ d γ) (relMean P q k t)) * meanHistory P γ q jStar k ≤
        profile P γ q jStar k t := by
  intro q
  have hp := (adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag jStar hj m hm k t hk
    hkt).2.2.2.2.2
  have hh := (bridge_fluctuationHistory_integrable d hd P γ E Ψ K S hstat hdag jStar hj m hm k hk).2
  apply le_trans (b := (3 : ℝ) ^ (-((1 - γ) / 4) * ((t : ℝ) - k)) *
    (1 + meanPenalty (bigQ d γ) (relMean P q k t)) * history P γ q jStar k) ?_
    (transport_profile_components d hd P γ E Ψ K S hstat hdag jStar hj m hm k t hk hkt).2.1
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (by linarith only [hp]))
  change meanHistory P γ q jStar k ≤ fluctuationHistory P γ q jStar k + meanHistory P γ q jStar k
  linarith only [hh]
/-- A later mean row belongs to the Ico range, which excludes the terminal scale. -/
theorem transport_later_mean_row (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ)
      (K : ℝ) (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger
      P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (k t : ℤ) (hk : (jStar : ℤ) ≤ k) (r : ℤ) (hr : r ∈ Finset.Ico k t) :
    let q := explicitRoundedGrid jStar m
    (3 : ℝ) ^ (-((1 - γ) / 4) * ((t : ℝ) - 1 - r)) *
      meanPenalty (bigQ d γ) (relMean P q r t) ≤ meanHistory P γ q k t := by
  intro q
  apply Finset.single_le_sum (f := fun u : ℤ => (3 : ℝ) ^ (-((1 - γ) / 4) * ((t : ℝ) - 1 - u)) *
    meanPenalty (bigQ d γ) (relMean P q u t)) ?_ hr
  intro u hu
  obtain ⟨hku, hut⟩ := Finset.mem_Ico.mp hu
  exact mul_nonneg (by positivity)
    (adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag jStar hj m hm u t (hk.trans hku)
      hut.le).2.2.2.2.2
/-- Changing the starting scale of the full mean history is paid by the
initial and later profile components, with an explicit geometric constant. -/
theorem transport_meanHistory_to_profile (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ)
      (K : ℝ)
    (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K
      S) (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (k t : ℤ) (hk : (jStar : ℤ) ≤ k) (hkt : k < t) :
    let q := explicitRoundedGrid jStar m
    meanHistory P γ q jStar t ≤
      (2 + 1 / (1 - (3 : ℝ) ^ (-((1 - γ) / 4)))) * profile P γ q jStar k t := by
  intro q
  have hγ := hdag.g_mem
  classical
  let a := (1 - γ) / 4
  let G := 1 / (1 - (3 : ℝ) ^ (-a))
  let p := fun r s : ℤ => meanPenalty (bigQ d γ) (relMean P q r s)
  let w := fun s r : ℤ => (3 : ℝ) ^ (-a * ((s : ℝ) - 1 - r))
  let A := (3 : ℝ) ^ (-a * ((t : ℝ) - k)) * (1 + p k t)
  have ha : 0 < a := by dsimp only [a]; linarith only [hγ.2]
  have hG : 0 < G := one_div_pos.mpr (transport_geometric_Icc a ha jStar k).1
  have hp : 0 ≤ p k t := (adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag jStar hj m
    hm k t hk hkt.le).2.2.2.2.2
  have hw (r) : w t r = (3 : ℝ) ^ (-a * ((t : ℝ) - k)) * w k r := by
    dsimp only [w]; rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1; ring
  have hgeo : (∑ r ∈ Finset.Ico (jStar : ℤ) k, w t r) ≤ G * w t k := by
    have he (r : ℤ) : w t r = w t k * (3 : ℝ) ^ (-a * ((k : ℝ) - r)) := by
      dsimp only [w]; rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1; ring
    rw [Finset.sum_congr rfl (fun r _ => he r), ← Finset.mul_sum]
    apply (mul_le_mul_of_nonneg_left (le_trans
      (Finset.sum_le_sum_of_subset_of_nonneg (fun r hr => Finset.mem_Icc.mpr
        ⟨(Finset.mem_Ico.mp hr).1, (Finset.mem_Ico.mp hr).2.le⟩) (fun _ _ _ => by positivity))
      (transport_geometric_Icc a ha jStar k).2) (by dsimp only [w]; positivity)).trans_eq
    ring
  have hlo : (∑ r ∈ Finset.Ico (jStar : ℤ) k, w t r * p r t) ≤
      A * meanHistory P γ q jStar k + G * (w t k * p k t) := by
    calc
      _ ≤ ∑ r ∈ Finset.Ico (jStar : ℤ) k, w t r * ((1 + p k t) * p r k + p k t) := by
        apply Finset.sum_le_sum
        intro r hr
        obtain ⟨hJr, hrk⟩ := Finset.mem_Ico.mp hr
        exact mul_le_mul_of_nonneg_left (transport_meanPenalty_split_scales d hd P γ E Ψ K S
          hstat hdag jStar hj m hm r k t hJr hrk.le hkt.le) (by dsimp only [w]; positivity)
      _ = (∑ r ∈ Finset.Ico (jStar : ℤ) k, w t r * ((1 + p k t) * p r k)) +
          (∑ r ∈ Finset.Ico (jStar : ℤ) k, w t r) * p k t := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
      _ = A * meanHistory P γ q jStar k + (∑ r ∈ Finset.Ico (jStar : ℤ) k, w t r) * p k t := by
        congr 1
        change _ = A * ∑ r ∈ Finset.Ico (jStar : ℤ) k, w k r * p r k
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _; rw [hw]
        dsimp only [A]; ring
      _ ≤ _ := add_le_add le_rfl (by
        calc
          _ ≤ (G * w t k) * p k t := mul_le_mul_of_nonneg_right hgeo hp
          _ = G * (w t k * p k t) := mul_assoc _ _ _)
  have hinit : A * meanHistory P γ q jStar k ≤ profile P γ q jStar k t :=
    transport_initial_mean_history d hd P γ hγ E Ψ K S hstat hdag jStar hj m hm k t hk hkt.le
  have hrow : w t k * p k t ≤ meanHistory P γ q k t := transport_later_mean_row d hd P γ E Ψ K S
    hstat hdag jStar hj m hm k t hk k (Finset.mem_Ico.mpr ⟨le_rfl, hkt⟩)
  have hpay := (transport_profile_components d hd P γ E Ψ K S hstat hdag jStar hj m hm k t hk
    hkt.le).2.2.1
  have he : Finset.Ico (jStar : ℤ) t = Finset.Ico (jStar : ℤ) k ∪ Finset.Ico k t := by
    ext r; simp only [Finset.mem_Ico, Finset.mem_union]; omega
  have hdis : Disjoint (Finset.Ico (jStar : ℤ) k) (Finset.Ico k t) := by
    apply Finset.disjoint_left.mpr
    intro r hr hs
    have hr' := Finset.mem_Ico.mp hr
    have hs' := Finset.mem_Ico.mp hs
    omega
  change (∑ r ∈ Finset.Ico (jStar : ℤ) t, w t r * p r t) ≤ _
  rw [he, Finset.sum_union hdis]
  calc
    _ ≤ (A * meanHistory P γ q jStar k + G * (w t k * p k t)) + meanHistory P γ q k t :=
      add_le_add hlo le_rfl
    _ ≤ (profile P γ q jStar k t + G * profile P γ q jStar k t) + profile P γ q jStar k t :=
      add_le_add (add_le_add hinit (mul_le_mul_of_nonneg_left (hrow.trans hpay) hG.le)) hpay
    _ = _ := by ring
/-- The actual bulk mean sum has the printed half-(1-gamma) loss in L. -/
theorem transport_bulk_mean_bound (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
      (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K
      S) (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (k n : ℤ) (hk : (jStar : ℤ) ≤ k) (hkn : k ≤ n) (L : ℕ) (hL : 1 ≤ L) :
    let q := explicitRoundedGrid jStar m
    let ell := fun j : ℤ => if j ≤ k + (L : ℤ) then 1 else L
    (∑ j ∈ Finset.Icc ((jStar : ℤ) + L) (n + L),
      (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) + L - 1 - j)) *
        meanPenalty (bigQ d γ) (relMean P q (j - (ell j : ℤ)) (n + 2 * (L : ℤ)))) ≤
      (2 * (2 + 1 / (1 - (3 : ℝ) ^ (-((1 - γ) / 4))))) *
        (3 : ℝ) ^ ((1 - γ) / 2 * (L : ℝ)) * profile P γ q jStar k (n + 2 * (L : ℤ)) := by
  intro q ell
  let t := n + 2 * (L : ℤ)
  let J := Finset.Icc ((jStar : ℤ) + L) (n + L)
  let U := Finset.Ico (jStar : ℤ) t
  let cap := fun j : ℤ => j - (ell j : ℤ)
  let D := (3 : ℝ) ^ ((1 - γ) / 2 * (L : ℝ))
  let w := fun r : ℤ => (3 : ℝ) ^ (-((1 - γ) / 4) * ((t : ℝ) - 1 - r))
  let p := fun r : ℤ => meanPenalty (bigQ d γ) (relMean P q r t)
  let F := fun r : ℤ => w r * p r
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hell (j : ℤ) : 1 ≤ ell j ∧ ell j ≤ L := by dsimp only [ell]; split_ifs <;> omega
  have hgen (j : ℤ) (hjmem : j ∈ J) : cap j ∈ U := by
    obtain ⟨hJj, hjt⟩ := Finset.mem_Icc.mp hjmem
    have he := hell j
    change j - (ell j : ℤ) ∈ Finset.Ico (jStar : ℤ) t
    exact Finset.mem_Ico.mpr ⟨by omega, by dsimp only [t]; omega⟩
  have hp (r) (hr : r ∈ U) : 0 ≤ p r :=
    (adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag jStar hj m hm r t
      (Finset.mem_Ico.mp hr).1 (Finset.mem_Ico.mp hr).2.le).2.2.2.2.2
  have hF (r) (hr : r ∈ U) : 0 ≤ F r := mul_nonneg (by dsimp only [w]; positivity) (hp r hr)
  have he (j : ℤ) : j - (if j ≤ k + (L : ℤ) then 1 else (L : ℤ)) = cap j := by
    dsimp only [cap, ell]; split_ifs <;> rfl
  have hsum : (∑ j ∈ J, F (cap j)) ≤ 2 * ∑ r ∈ U, F r := by
    have hh := transport_bulk_generation_sum k L J U F hF (by intro j hjmem; rw [he]; exact hgen
      j hjmem)
    simpa only [he] using hh
  have hpay : (∑ r ∈ U, F r) ≤
      (2 + 1 / (1 - (3 : ℝ) ^ (-((1 - γ) / 4)))) * profile P γ q jStar k t :=
    transport_meanHistory_to_profile d hd P γ E Ψ K S hstat hdag jStar hj m hm k t hk (by dsimp
      only [t]; omega)
  calc
    _ ≤ ∑ j ∈ J, D * F (cap j) := by
      apply Finset.sum_le_sum
      intro j hjmem
      have hh := mul_le_mul_of_nonneg_right (transport_mean_weight_ratio γ hγ.2 n j L (ell j)
        (hell j).2).2 (hp (cap j) (hgen j hjmem))
      simpa only [D, F, w, cap, t, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
        Int.cast_sub, mul_assoc] using hh
    _ = D * ∑ j ∈ J, F (cap j) := (Finset.mul_sum _ _ _).symm
    _ ≤ D * (2 * ∑ r ∈ U, F r) := mul_le_mul_of_nonneg_left hsum hD
    _ ≤ D * (2 * ((2 + 1 / (1 - (3 : ℝ) ^ (-((1 - γ) / 4)))) * profile P γ q jStar k t)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpay (by norm_num)) hD
    _ = _ := by ring

end
end HCPolySupport.HighContrast.Annealed
