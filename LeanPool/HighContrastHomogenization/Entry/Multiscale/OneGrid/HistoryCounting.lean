/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.OneGrid.MeanPenaltyDrift

/-!
# High-contrast homogenization: Entry.Multiscale.OneGrid.HistoryCounting

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Step 1 — counting, integrability and transport

Group D of the printed proof (`p.fixed.geometry.one.grid.propagation`), first half: the cell
counts of an
adapted grid, the integrability and domination facts for the history integrands, stationarity
transport, and the pointwise bounds the fluctuation decomposition consumes.

Part of the proof of the statement in
`HCPoly/Entry/Statements/OneGridPropagation.lean`.  Conventions of the group:
`q = 𝒬(𝔪)` is `Geometry.explicitRoundedGrid jStar metric` at every loss, history, profile and drift;
`metric` (not `m`) names the positive matrix, because `m`, `n`, `m₀` are generations; the
source lower scale `e.source.lower.scale` is carried exactly by the source-facing statement in
`HCPoly/Entry/OneGridPropagation.lean`; this group's stronger algebraic and history lemmas
omit an unused threshold, and this group's generic integration helpers take finiteness,
integrability or measurability inputs that are proved at their actual use sites, not extra
premises of the printed proposition.

-/

open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter adaptedMean blockSub coarseBlock
  matSqrt measurable_translateCoeff normalizedBlock toFullBlockMat_eq_blockMatEntry
  translateCoeff)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-! ## Group D. Step 1 — control of the histories (`p.fixed.geometry.one.grid.propagation`) -/

/-- The mean history is nonnegative on the admissible range: every `Ψ_Q(P^q_{j,m})` is, because
the adapted annealed means decrease and normalize above the identity. -/
theorem meanHistory_nonneg (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (S : CoeffSpace d → ℝ),
      IsProbabilityMeasure P →
      IsStationaryLaw P →
      IsUnitRangeLaw P →
      CoarseEllipticityDagger P γ E Ψ K S →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
        ∀ (metric : Mat d), metric.PosDef →
          ∀ n m : ℤ, (jStar : ℤ) ≤ n → n ≤ m →
            0 ≤ meanHistory P γ (Geometry.explicitRoundedGrid jStar metric) n m := by
  intro P E Ψ K S hP hstat hunit hdag jStar hjStar metric hmetric n m hjStar_n hn_m
  unfold HCPolySupport.HighContrast.meanHistory
  apply Finset.sum_nonneg
  intro j hj
  have hjStar_j : (jStar : ℤ) ≤ j := by
    exact le_trans hjStar_n (Finset.mem_Ico.mp hj).1
  have hj_m : j ≤ m := by
    exact le_of_lt (Finset.mem_Ico.mp hj).2
  apply mul_nonneg
  · exact Real.rpow_nonneg (le_trans hγ.1 (le_of_lt (lt_trans hγ.2 (by norm_num)))) _
  ·
    exact
      (HCPolySupport.HighContrast.Annealed.normalizedBlock_order_consequences
        (HCPolySupport.HighContrast.bigQ d γ)
        (HCPolySupport.HighContrast.adaptedMean P
          (HCPolySupport.HighContrast.Geometry.explicitRoundedGrid jStar metric) j)
        (HCPolySupport.HighContrast.adaptedMean P
          (HCPolySupport.HighContrast.Geometry.explicitRoundedGrid jStar metric) m)
        (HCPolySupport.HighContrast.Annealed.adaptedMean_posDef
          d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric j)
        (HCPolySupport.HighContrast.Annealed.adaptedMean_posDef
          d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric m)
        (HCPolySupport.HighContrast.Annealed.adaptedMean_antitone
          d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric j m
          hjStar_j hj_m)).2.2.2.2.2

/-- Finite nonnegative suprema are integrable and dominate each entry. This supplies the
real-supremum justification in the carried-history step, `p.fixed.geometry.one.grid.propagation`. -/
theorem oneGrid_integrable_biSup {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (s : Set ι) (hs : s.Finite) (f : ι → Ω → ℝ)
    (hf : ∀ i a, 0 ≤ f i a) (hint : ∀ i ∈ s, Integrable (f i) P) :
    Integrable (fun a => ⨆ i ∈ s, f i a) P ∧
      ∀ a i, i ∈ s → f i a ≤ ⨆ k ∈ s, f k a := by
  classical
  have hsum (a : Ω) : 0 ≤ ∑ i ∈ hs.toFinset, f i a :=
    Finset.sum_nonneg fun i _ => hf i a
  have hbound (a : Ω) (i : ι) :
      (⨆ _hi : i ∈ s, f i a) ≤ ∑ k ∈ hs.toFinset, f k a := by
    refine Real.iSup_le (fun hi => ?_) (hsum a)
    exact Finset.single_le_sum (fun k _ => hf k a) (hs.mem_toFinset.mpr hi)
  have hbdd (a : Ω) : BddAbove (Set.range (fun i => ⨆ _hi : i ∈ s, f i a)) := by
    refine ⟨∑ k ∈ hs.toFinset, f k a, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact hbound a i
  have hm : AEStronglyMeasurable (fun a => ⨆ i ∈ s, f i a) P :=
    (AEMeasurable.biSup s hs.countable (fun i hi => (hint i hi).aemeasurable)).aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · apply (integrable_finsetSum hs.toFinset (fun i hi => hint i (hs.mem_toFinset.mp hi))).mono' hm
    filter_upwards [] with a
    rw [Real.norm_eq_abs, abs_of_nonneg
      (Real.iSup_nonneg (fun i => Real.iSup_nonneg (fun _ => hf i a)))]
    exact Real.iSup_le (hbound a) (hsum a)
  · intro a i hi
    have h := le_ciSup (hbdd a) i
    simpa only [ciSup_pos hi] using h

/-- Exact centre count in an invertible adapted grid, used to absorb the maximum by a sum
in the carried-history step, `p.fixed.geometry.one.grid.propagation`. -/
theorem oneGrid_centers_finite_card {d : ℕ} (q : Mat d) (hq : IsUnit q)
    (j m : ℤ) (hjm : j ≤ m) :
    (adaptedLatticeAtScale q j ∩ HighContrast.adaptedCell q m).Finite ∧
      (adaptedLatticeAtScale q j ∩ HighContrast.adaptedCell q m).ncard = 3 ^ (d * (m - j).toNat)
        := by
  have hqinj : Function.Injective (matVecMul q) := Matrix.mulVec_injective_iff_isUnit.mpr hq
  have heq : j + ((m - j).toNat : ℤ) = m := by omega
  have hs := Annealed.alignedCenterSet_finite_card d j (m - j).toNat
  rw [heq] at hs
  have hset : adaptedLatticeAtScale q j ∩ HighContrast.adaptedCell q m =
      adaptedCellCenter q j '' {w : Fin d → ℤ | HighContrast.standardCellCenter j w ∈
        HighContrast.centeredCube d m} := by
    ext z
    constructor
    · rintro ⟨⟨w, rfl⟩, hw⟩
      refine ⟨w, ?_, rfl⟩
      rw [Recurrence.adaptedCellCenter_eq] at hw
      obtain ⟨x, hx, he⟩ := hw
      change HighContrast.standardCellCenter j w ∈ HighContrast.centeredCube d m
      exact hqinj he ▸ hx
    · rintro ⟨w, hw, rfl⟩
      refine ⟨⟨w, rfl⟩, ?_⟩
      rw [Recurrence.adaptedCellCenter_eq]
      exact ⟨_, hw, rfl⟩
  have hinj : Function.Injective (adaptedCellCenter q j) := by
    intro v w hvw
    simp only [Recurrence.adaptedCellCenter_eq] at hvw
    have hh := hqinj hvw
    funext i
    have hi := congrFun hh i
    simp only [HighContrast.standardCellCenter] at hi
    have h3 : (3 : ℝ) ^ j ≠ 0 := by positivity
    exact_mod_cast (mul_left_cancel₀ h3 hi)
  rw [hset]
  exact ⟨hs.1.image _, (Set.ncard_image_of_injective _ hinj).trans hs.2⟩

/-- Compatible centre decomposition through an intermediate generation. The same parent
cell is used for every fine scale in the carried-history step,
`p.fixed.geometry.one.grid.propagation`. -/
theorem oneGrid_centers_decompose {d : ℕ} (q : Mat d) (hq : IsUnit q)
    (j n m : ℤ) (hjn : j ≤ n) (hnm : n ≤ m) (z : Vec d)
    (hz : z ∈ adaptedLatticeAtScale q j ∩ HighContrast.adaptedCell q m) :
    ∃ y ∈ adaptedLatticeAtScale q n ∩ HighContrast.adaptedCell q m,
      z - y ∈ adaptedLatticeAtScale q j ∩ HighContrast.adaptedCell q n := by
  have hqinj : Function.Injective (matVecMul q) := Matrix.mulVec_injective_iff_isUnit.mpr hq
  obtain ⟨⟨w, rfl⟩, hw⟩ := hz
  have hw' : HighContrast.standardCellCenter j w ∈ HighContrast.centeredCube d m := by
    rw [Recurrence.adaptedCellCenter_eq] at hw
    obtain ⟨x, hx, he⟩ := hw
    exact hqinj he ▸ hx
  have hancestor (h : ℕ) : ∃ v : Fin d → ℤ,
      HighContrast.standardCell d j w ⊆ HighContrast.standardCell d (j + h) v := by
    induction h with
    | zero => exact ⟨w, by simp⟩
    | succ h ih =>
      obtain ⟨v, hv⟩ := ih
      refine ⟨Transport.gridParent v, ?_⟩
      simpa only [Nat.cast_add, Nat.cast_one, ← add_assoc] using
        hv.trans (Transport.standardCell_subset_parent (j + h) v)
  obtain ⟨v, hv⟩ := hancestor (n - j).toNat
  have hnj : j + ((n - j).toNat : ℤ) = n := by omega
  rw [hnj] at hv
  have hwv := hv (Recurrence.standardCellCenter_mem_standardCell j w)
  have hvsub : HighContrast.standardCell d n v ⊆ HighContrast.centeredCube d m := by
    rw [Geometry.centeredCube_eq_standardCell] at hw' ⊢
    exact Geometry.standardCell_subset_of_mem hnm hwv hw'
  refine ⟨adaptedCellCenter q n v, ⟨⟨v, rfl⟩, ?_⟩, ?_, ?_⟩
  · rw [Recurrence.adaptedCellCenter_eq]
    exact ⟨_, hvsub (Recurrence.standardCellCenter_mem_standardCell n v), rfl⟩
  · refine ⟨fun i => w i - (3 : ℤ) ^ (n - j).toNat * v i, ?_⟩
    simp only [Recurrence.adaptedCellCenter_eq,
      Geometry.matVecMul_eq_mulVec]
    rw [← Matrix.mulVec_sub]
    congr 1
    funext i
    have hpow : (3 : ℝ) ^ n = (3 : ℝ) ^ j * (3 : ℝ) ^ (n - j).toNat := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), hnj]
    simp only [HighContrast.standardCellCenter, Pi.sub_apply, Int.cast_sub, Int.cast_mul,
      Int.cast_pow, Int.cast_ofNat]
    rw [hpow]
    ring
  · refine ⟨HighContrast.standardCellCenter j w - HighContrast.standardCellCenter n v, ?_, ?_⟩
    · rw [Recurrence.mem_centeredCube_iff]
      rw [Recurrence.mem_standardCell_iff] at hwv
      intro i
      have hi := hwv i
      simp only [Pi.sub_apply, HighContrast.standardCellCenter] at hi ⊢
      constructor <;> linarith only [hi.1, hi.2]
    · simp only [Recurrence.adaptedCellCenter_eq,
        Geometry.matVecMul_eq_mulVec, Matrix.mulVec_sub]

/-- Stationarity transports an entire scalar integrand, including its joint supremum.
This is the shared-translation step of carried history, `p.fixed.geometry.one.grid.propagation`. -/
theorem oneGrid_integral_translate {d : ℕ} (P : Measure (CoeffSpace d))
    (hstat : IsStationaryLaw P) (f : CoeffSpace d → ℝ)
    (hf : AEStronglyMeasurable f P) (v : Fin d → ℤ) :
    (∫ a, f (translateCoeff v a) ∂P) = ∫ a, f a ∂P := by
  have h := integral_map (μ := P) (φ := translateCoeff v)
    (measurable_translateCoeff v).aemeasurable (f := f) (by rw [hstat v]; exact hf)
  rw [hstat v] at h
  exact h.symm

/-- The scale-cell count is absorbed with coefficient one in the decay of carried history,
`p.fixed.geometry.one.grid.propagation`. -/
theorem oneGrid_count_absorption (d : ℕ) (_hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (j m : ℤ) (hjm : j ≤ m) :
    (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((m : ℝ) - (j : ℝ))) *
        (3 ^ (d * (m - j).toNat) : ℕ) ≤
      (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (j : ℝ))) := by
  have hQ := bigQ_real_pos d γ hγ
  have hexp : (d : ℝ) + (1 - γ) / 4 ≤ (bigQ d γ : ℝ) * rhoMax d γ := by
    unfold rhoMax
    rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hQ.ne', one_mul]
    nlinarith only [mul_nonneg hQ.le hγ.1]
  have hgap : ((m - j).toNat : ℝ) = (m : ℝ) - (j : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hjm)
  push_cast
  rw [← Real.rpow_natCast (3 : ℝ), Nat.cast_mul, hgap,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hg : 0 ≤ (m : ℝ) - (j : ℝ) := by exact_mod_cast sub_nonneg.mpr hjm
  nlinarith only [mul_le_mul_of_nonneg_right hexp hg]

/-- Change of normalization in operator norm, without commuting the square roots. This is
the matrix congruence in the carried-history step, `p.fixed.geometry.one.grid.propagation`. -/
theorem oneGrid_normalizedBlock_opNorm_le {d : ℕ} (A F G : BlockMat d)
    (hF : (toFullBlockMat F).PosDef) (hG : (toFullBlockMat G).PosDef) :
    blockOpNorm (normalizedBlock A G) ≤
      blockOpNorm (normalizedBlock F G) * blockOpNorm (normalizedBlock A F) := by
  open scoped Matrix.Norms.L2Operator in
  let T := matSqrt (toFullBlockMat F)⁻¹
  let R := T⁻¹
  let S := matSqrt (toFullBlockMat G)⁻¹
  have hT : T.PosDef := matSqrt_inv_posDef_full hF
  have hS : S.PosDef := matSqrt_inv_posDef_full hG
  have hRT : R * T = 1 := Matrix.nonsing_inv_mul T ((Matrix.isUnit_iff_isUnit_det T).mp hT.isUnit)
  have hTR : T * R = 1 := Matrix.mul_nonsing_inv T ((Matrix.isUnit_iff_isUnit_det T).mp hT.isUnit)
  have hTFT : T * toFullBlockMat F * T = 1 := matSqrt_inv_conj hF
  have hRR : R * R = toFullBlockMat F := by
    calc
      R * R = R * (T * toFullBlockMat F * T) * R := by rw [hTFT, mul_one]
      _ = (R * T) * toFullBlockMat F * (T * R) := by simp only [mul_assoc]
      _ = _ := by rw [hRT, hTR, one_mul, mul_one]
  let U := R * S
  have hstar : star U = S * R := by
    change (R * S).conjTranspose = S * R
    rw [Matrix.conjTranspose_mul, hS.isHermitian.eq, hT.inv.isHermitian.eq]
  have hcong : toFullBlockMat (normalizedBlock A G) =
      star U * toFullBlockMat (normalizedBlock A F) * U := by
    simp only [normalizedBlock, toFullBlockMat_ofFullBlockMat]
    change S * toFullBlockMat A * S = star U * (T * toFullBlockMat A * T) * U
    rw [hstar]
    dsimp only [U]
    simp only [mul_assoc, ← mul_assoc R T, hRT, one_mul,
      ← mul_assoc T R, hTR]
  have hUU : star U * U = toFullBlockMat (normalizedBlock F G) := by
    rw [hstar]
    simp only [normalizedBlock, toFullBlockMat_ofFullBlockMat]
    change S * R * (R * S) = S * toFullBlockMat F * S
    rw [mul_assoc S R, ← mul_assoc R R, hRR, ← mul_assoc]
  have hnorm : ‖U‖ * ‖U‖ = blockOpNorm (normalizedBlock F G) := by
    rw [← CStarRing.norm_star_mul_self, hUU]
    rfl
  change ‖toFullBlockMat (normalizedBlock A G)‖ ≤ _
  rw [hcong]
  calc
    _ ≤ (‖star U‖ * ‖toFullBlockMat (normalizedBlock A F)‖) * ‖U‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = (‖U‖ * ‖U‖) * blockOpNorm (normalizedBlock A F) := by
      rw [norm_star, blockOpNorm]
      ring
    _ = _ := by rw [hnorm]

/-- Operator moments are integrable under the existing Schatten membership theorem. This
justifies the finite maxima of carried history, `p.fixed.geometry.one.grid.propagation`. -/
theorem oneGrid_integrable_opNorm_pow {d : ℕ} (P : Measure (CoeffSpace d))
    (N : ℕ) (hN : (1 : ℝ) ≤ (N : ℝ)) (H : CoeffSpace d → BlockMat d)
    (hmem : SchattenMemLp P (N : ℝ) H) :
    Integrable (fun a => blockOpNorm (H a) ^ N) P := by
  open scoped Matrix.Norms.L2Operator in
  have hm : AEMeasurable (fun a => toFullBlockMat (H a)) P :=
    AEMeasurable.of_eval fun α => AEMeasurable.of_eval fun β => by
      simpa only [toFullBlockMat_eq_blockMatEntry] using (hmem.measurable α β).aemeasurable
  have hmoment : Integrable (fun a => absSchattenNorm (N : ℝ) (H a) ^ N) P := by
    simpa only [Real.rpow_natCast] using hmem.integrable
  apply hmoment.mono' ((hm.norm.pow_const N).aestronglyMeasurable)
  filter_upwards [hmem.symmetric] with a ha
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (Analysis.blockOpNorm_le_absSchattenNorm ((Analysis.toFullBlockMat_isHermitian_iff _).mpr
      ha) hN) _

/-- Integrability and pointwise domination for the actual weighted history integrand,
as used in the carried-history step, `p.fixed.geometry.one.grid.propagation`. -/
theorem oneGrid_fluctuation_integrable_dominate (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (metric : Mat d) (hmetric : metric.PosDef)
    (k : ℤ) :
    let q := Geometry.explicitRoundedGrid jStar metric
    let f := fun a => ⨆ j ∈ Set.Icc (jStar : ℤ) k,
      (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((k : ℝ) - (j : ℝ))) *
        ⨆ z ∈ adaptedLatticeAtScale q j ∩ HighContrast.adaptedCell q k,
          blockOpNorm (normalizedFluctuation P q j k z a) ^ bigQ d γ
    Integrable f P ∧ ∀ a j, j ∈ Set.Icc (jStar : ℤ) k →
      ∀ z ∈ adaptedLatticeAtScale q j ∩ HighContrast.adaptedCell q k,
        (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((k : ℝ) - (j : ℝ))) *
          blockOpNorm (normalizedFluctuation P q j k z a) ^ bigQ d γ ≤ f a := by
  intro q f
  have hγ := hdag.g_mem
  open scoped Matrix.Norms.L2Operator in
  have hQ : (1 : ℝ) ≤ (bigQ d γ : ℝ) := by
    exact_mod_cast (show 1 ≤ bigQ d γ from le_trans (by norm_num) (bigQ_two_le d γ hγ))
  have hq : IsUnit q := Geometry.isUnit_roundedGrid hjStar hmetric
  let w (j : ℤ) := (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((k : ℝ) - (j : ℝ)))
  have hw (j : ℤ) : 0 ≤ w j := Real.rpow_nonneg (by norm_num) _
  have hinner (j : ℤ) (hjk : j ≤ k) := oneGrid_integrable_biSup P
    (adaptedLatticeAtScale q j ∩ HighContrast.adaptedCell q k)
    (oneGrid_centers_finite_card q hq j k hjk).1
    (fun z a => blockOpNorm (normalizedFluctuation P q j k z a) ^ bigQ d γ)
    (fun _ _ => pow_nonneg (norm_nonneg _) _)
    (fun z _ => oneGrid_integrable_opNorm_pow P (bigQ d γ) hQ _
      (Annealed.memLqSchatten_normalizedFluctuation d hd P γ E Ψ K S hstat hdag
        jStar hjStar metric hmetric j k z _ hQ))
  have houter := oneGrid_integrable_biSup P (Set.Icc (jStar : ℤ) k) (Set.finite_Icc _ _)
    (fun j a => w j * ⨆ z ∈ adaptedLatticeAtScale q j ∩ HighContrast.adaptedCell q k,
      blockOpNorm (normalizedFluctuation P q j k z a) ^ bigQ d γ)
    (fun j _ => mul_nonneg (hw j) (Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ =>
      pow_nonneg (norm_nonneg _) _))
    (fun j hj => (hinner j hj.2).1.const_mul _)
  refine ⟨houter.1, ?_⟩
  intro a j hj z hz
  exact (mul_le_mul_of_nonneg_left ((hinner j hj.2).2 a z hz) (hw j)).trans
    (houter.2 a j hj)

/-- Powered change of normalization for an individual fluctuation. This supplies the
matrix factor in the carried-history step, `p.fixed.geometry.one.grid.propagation`. -/
theorem oneGrid_fluctuation_pow_transport {d : ℕ} (P : Measure (CoeffSpace d))
    (q : Mat d) (Q : ℕ) (j k l : ℤ) (z : Vec d) (a : CoeffSpace d)
    (hk : (toFullBlockMat (adaptedMean P q k)).PosDef)
    (hl : (toFullBlockMat (adaptedMean P q l)).PosDef) :
    blockOpNorm (normalizedFluctuation P q j l z a) ^ Q ≤
      blockOpNorm (relMean P q k l) ^ Q *
        blockOpNorm (normalizedFluctuation P q j k z a) ^ Q := by
  open scoped Matrix.Norms.L2Operator in
  have ht := oneGrid_normalizedBlock_opNorm_le
    (blockSub (coarseBlock (HighContrast.adaptedCellTranslate q j z) a) (adaptedMean P q j))
    (adaptedMean P q k) (adaptedMean P q l) hk hl
  have ht' := pow_le_pow_left₀ (norm_nonneg _) ht Q
  simpa only [mul_pow] using! ht'

/-- Stationarity and normalization bound a single fine-cell moment by its diagonal
Schatten moment, in the carried-history step, `p.fixed.geometry.one.grid.propagation`. -/
theorem oneGrid_lattice_moment_le (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (metric : Mat d) (hmetric : metric.PosDef)
    (j m : ℤ) (hj : (jStar : ℤ) ≤ j) (hjm : j ≤ m) (z : Vec d)
    (hz : z ∈ adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar metric) j) :
    let q := Geometry.explicitRoundedGrid jStar metric
    (∫ a, blockOpNorm (normalizedFluctuation P q j m z a) ^ bigQ d γ ∂P) ≤
      Real.exp ((bigQ d γ : ℝ) * detIncrement P q j m) *
        ∫ a, absSchattenNorm (bigQ d γ : ℝ) (normalizedFluctuationSelf P q j a) ^ bigQ d γ ∂P := by
  intro q
  open scoped Matrix.Norms.L2Operator in
  let Q := bigQ d γ
  let v (k : ℤ) (z : Vec d) (a : CoeffSpace d) :=
    blockOpNorm (normalizedFluctuation P q j k z a) ^ Q
  have hQ : (1 : ℝ) ≤ (Q : ℝ) := by
    exact_mod_cast (show 1 ≤ Q from le_trans (by norm_num) (bigQ_two_le d γ hγ))
  have hmem (k : ℤ) (z : Vec d) := Annealed.memLqSchatten_normalizedFluctuation
    d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric j k z (Q : ℝ) hQ
  have hint (k : ℤ) (z : Vec d) : Integrable (v k z) P :=
    oneGrid_integrable_opNorm_pow P Q hQ _ (hmem k z)
  have hpos (k : ℤ) := Annealed.adaptedMean_posDef d hd P γ E Ψ K S hstat hdag
    jStar hjStar metric hmetric k
  have hc : blockOpNorm (relMean P q j m) ^ Q ≤
      Real.exp ((Q : ℝ) * detIncrement P q j m) := by
    have hp := pow_le_pow_left₀ (norm_nonneg _)
      (Annealed.adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag
        jStar hjStar metric hmetric j m hj hjm).2.2.2.1 Q
    simpa only [Real.exp_nat_mul] using! hp
  have hi : (∫ a, v m z a ∂P) ≤
      Real.exp ((Q : ℝ) * detIncrement P q j m) * ∫ a, v j z a ∂P := by
    rw [← integral_const_mul]
    apply integral_mono (hint m z) ((hint j z).const_mul _)
    intro a
    exact (oneGrid_fluctuation_pow_transport P q Q j j m z a (hpos j) (hpos m)).trans
      (mul_le_mul_of_nonneg_right hc (pow_nonneg (norm_nonneg _) _))
  obtain ⟨u, rfl⟩ := hz
  obtain ⟨t, ht⟩ := Annealed.adaptedCellCenter_eq_intTranslation jStar metric hj u
  have he : (∫ a, v j (adaptedCellCenter q j u) a ∂P) = ∫ a, v j 0 a ∂P := by
    have hf : (fun a => v j (adaptedCellCenter q j u) a) =
        (fun a => v j 0 (translateCoeff t a)) := by
      funext a
      dsimp only [v, normalizedFluctuation]
      rw [Annealed.coarseBlock_adapted_translateCoeff, zero_add, ht]
    rw [hf]
    exact oneGrid_integral_translate P hstat _ (hint j 0).aestronglyMeasurable t
  have hmoment : Integrable (fun a => absSchattenNorm (Q : ℝ)
      (normalizedFluctuationSelf P q j a) ^ Q) P := by
    simpa only [Real.rpow_natCast] using! (hmem j 0).integrable
  have hspectral : (∫ a, v j 0 a ∂P) ≤
      ∫ a, absSchattenNorm (Q : ℝ) (normalizedFluctuationSelf P q j a) ^ Q ∂P := by
    apply integral_mono_ae (hint j 0) hmoment
    filter_upwards [(hmem j 0).symmetric] with a ha
    exact pow_le_pow_left₀ (norm_nonneg _)
      (Analysis.blockOpNorm_le_absSchattenNorm ((Analysis.toFullBlockMat_isHermitian_iff _).mpr
        ha) hQ) Q
  rw [he] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left hspectral (Real.exp_nonneg _))

/-- Split a weighted real supremum at an intermediate generation and replace the upper
maxima by finite sums. This is the scalar integration step of carried history,
`p.fixed.geometry.one.grid.propagation`. -/
theorem oneGrid_integral_sup_split {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (b n m : ℤ) (w : ℤ → ℝ) (hw : ∀ j, 0 < w j)
    (Z : ℤ → Set ι) (F : ℤ → Finset ι) (f : ℤ → ι → Ω → ℝ)
    (hf : ∀ j z a, 0 ≤ f j z a)
    (hcover : ∀ j ∈ Finset.Icc (n + 1) m, ∀ z ∈ Z j, z ∈ F j)
    (hfint : ∀ j ∈ Finset.Icc (n + 1) m, ∀ z ∈ F j, Integrable (f j z) P)
    (L : Ω → ℝ) (hL : ∀ a, 0 ≤ L a) (hLint : Integrable L P)
    (hHint : Integrable (fun a => ⨆ j ∈ Set.Icc b m, w j * ⨆ z ∈ Z j, f j z a) P)
    (hlower : ∀ a j, b ≤ j → j ≤ n → ∀ z ∈ Z j, w j * f j z a ≤ L a) :
    (∫ a, ⨆ j ∈ Set.Icc b m, w j * ⨆ z ∈ Z j, f j z a ∂P) ≤
      (∫ a, L a ∂P) + ∑ j ∈ Finset.Icc (n + 1) m, ∫ a, w j * ∑ z ∈ F j, f j z a ∂P := by
  classical
  let U (j : ℤ) (a : Ω) := w j * ∑ z ∈ F j, f j z a
  have hU (j : ℤ) (a : Ω) : 0 ≤ U j a :=
    mul_nonneg (hw j).le (Finset.sum_nonneg fun z _ => hf j z a)
  have hUint (j : ℤ) (hj : j ∈ Finset.Icc (n + 1) m) : Integrable (U j) P :=
    (integrable_finsetSum _ (fun z hz => hfint j hj z hz)).const_mul _
  have hsumU (a : Ω) : 0 ≤ ∑ j ∈ Finset.Icc (n + 1) m, U j a :=
    Finset.sum_nonneg fun j _ => hU j a
  have hsup_le (a : Ω) (j : ℤ) (D : ℝ) (hD : 0 ≤ D)
      (ht : ∀ z ∈ Z j, w j * f j z a ≤ D) :
      w j * (⨆ z ∈ Z j, f j z a) ≤ D := by
    apply (le_div_iff₀' (hw j)).mp
    apply Real.iSup_le _ (div_nonneg hD (hw j).le)
    intro z
    apply Real.iSup_le _ (div_nonneg hD (hw j).le)
    intro hz
    exact (le_div_iff₀' (hw j)).mpr (ht z hz)
  have hpoint (a : Ω) : (⨆ j ∈ Set.Icc b m, w j * ⨆ z ∈ Z j, f j z a) ≤
      L a + ∑ j ∈ Finset.Icc (n + 1) m, U j a := by
    apply Real.iSup_le _ (add_nonneg (hL a) (hsumU a))
    intro j
    apply Real.iSup_le _ (add_nonneg (hL a) (hsumU a))
    intro hj
    apply hsup_le a j _ (add_nonneg (hL a) (hsumU a))
    intro z hz
    by_cases hjn : j ≤ n
    · exact (hlower a j hj.1 hjn z hz).trans (le_add_of_nonneg_right (hsumU a))
    · have hjI : j ∈ Finset.Icc (n + 1) m := Finset.mem_Icc.mpr ⟨by omega, hj.2⟩
      have hzsum : f j z a ≤ ∑ z ∈ F j, f j z a :=
        Finset.single_le_sum (fun z _ => hf j z a) (hcover j hjI z hz)
      have hzu : w j * f j z a ≤ U j a := mul_le_mul_of_nonneg_left hzsum (hw j).le
      exact hzu.trans ((Finset.single_le_sum (fun k _ => hU k a) hjI).trans
        (le_add_of_nonneg_left (hL a)))
  have hi := integrable_finsetSum (Finset.Icc (n + 1) m) hUint
  change _ ≤ (∫ a, L a ∂P) + ∑ j ∈ Finset.Icc (n + 1) m, ∫ a, U j a ∂P
  rw [← integral_finsetSum _ hUint, ← integral_add hLint hi]
  exact integral_mono hHint (hLint.add hi) hpoint

/-- The trace penalty controls the powered normalization factor, for arbitrary fine
generation and centre, in carried history, `p.fixed.geometry.one.grid.propagation`. -/
theorem oneGrid_fluctuation_pow_le_penalty (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (metric : Mat d) (hmetric : metric.PosDef)
    (j n m : ℤ) (hn : (jStar : ℤ) ≤ n) (hnm : n ≤ m) (z : Vec d) (a : CoeffSpace d) :
    let q := Geometry.explicitRoundedGrid jStar metric
    blockOpNorm (normalizedFluctuation P q j m z a) ^ bigQ d γ ≤
      (1 + meanPenalty (bigQ d γ) (relMean P q n m)) *
        blockOpNorm (normalizedFluctuation P q j n z a) ^ bigQ d γ := by
  intro q
  open scoped Matrix.Norms.L2Operator in
  have hpos (k : ℤ) := Annealed.adaptedMean_posDef d hd P γ E Ψ K S hstat hdag
    jStar hjStar metric hmetric k
  have ht := Annealed.blockOpNorm_le_one_add_trace (relMean P q n m)
    (Annealed.normalizedBlock_posDef _ _ (hpos n) (hpos m)).isHermitian
    (Annealed.adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag
      jStar hjStar metric hmetric n m hn hnm).1
  have hb : blockOpNorm (relMean P q n m) ^ bigQ d γ ≤
      1 + meanPenalty (bigQ d γ) (relMean P q n m) := by
    have hp := pow_le_pow_left₀ (norm_nonneg _) ht (bigQ d γ)
    simpa only [meanPenalty, add_sub_cancel] using! hp
  exact (oneGrid_fluctuation_pow_transport P q (bigQ d γ) j n m z a (hpos n) (hpos m)).trans
    (mul_le_mul_of_nonneg_right hb (pow_nonneg (norm_nonneg _) _))

/-- The old-generation bound uses one translated joint supremum per parent cell. This is
the compatible partition argument of carried history, `p.fixed.geometry.one.grid.propagation`. -/
theorem oneGrid_lower_pointwise (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (_hγ : γ ∈ Set.Ico (0 : ℝ) 1) (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (metric : Mat d) (hmetric : metric.PosDef)
    (n m : ℤ) (hn : (jStar : ℤ) ≤ n) (hnm : n ≤ m) (C : Finset (Vec d))
    (hC : (C : Set (Vec d)) = adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar metric) n ∩
      HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar metric) m)
    (τ : Vec d → Fin d → ℤ)
    (hτ : ∀ y ∈ adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar metric) n ∩
      HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar metric) m, y =
        Source.AKL.intTranslation (τ y)) :
    let q := Geometry.explicitRoundedGrid jStar metric
    let H := fun a => ⨆ j ∈ Set.Icc (jStar : ℤ) n,
      (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((n : ℝ) - (j : ℝ))) *
        ⨆ z ∈ adaptedLatticeAtScale q j ∩ HighContrast.adaptedCell q n,
          blockOpNorm (normalizedFluctuation P q j n z a) ^ bigQ d γ
    ∀ a j, (jStar : ℤ) ≤ j → j ≤ n →
      ∀ z ∈ adaptedLatticeAtScale q j ∩ HighContrast.adaptedCell q m,
        (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((m : ℝ) - (j : ℝ))) *
          blockOpNorm (normalizedFluctuation P q j m z a) ^ bigQ d γ ≤
        (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((m : ℝ) - (n : ℝ))) *
          (1 + meanPenalty (bigQ d γ) (relMean P q n m)) *
            ∑ y ∈ C, H (translateCoeff (τ y) a) := by
  classical
  intro q H
  open scoped Matrix.Norms.L2Operator in
  let Q := bigQ d γ
  let Z (j k : ℤ) := adaptedLatticeAtScale q j ∩ HighContrast.adaptedCell q k
  let w (j k : ℤ) := (3 : ℝ) ^ (-(Q : ℝ) * rhoMax d γ * ((k : ℝ) - (j : ℝ)))
  let v (j k : ℤ) (z : Vec d) (a : CoeffSpace d) :=
    blockOpNorm (normalizedFluctuation P q j k z a) ^ Q
  let B := 1 + meanPenalty Q (relMean P q n m)
  have hq : IsUnit q := Geometry.isUnit_roundedGrid hjStar hmetric
  have hw (j k : ℤ) : 0 < w j k := Real.rpow_pos_of_pos (by norm_num) _
  have hv (j k : ℤ) (z : Vec d) (a : CoeffSpace d) : 0 ≤ v j k z a :=
    pow_nonneg (norm_nonneg _) _
  have hH (a : CoeffSpace d) : 0 ≤ H a :=
    Real.iSup_nonneg fun j => Real.iSup_nonneg fun _ =>
      mul_nonneg (hw j n).le (Real.iSup_nonneg fun z => Real.iSup_nonneg fun _ => hv j n z a)
  have houter := oneGrid_fluctuation_integrable_dominate d hd γ P E Ψ K S
    hstat hdag jStar hjStar metric hmetric n
  have hdom (a : CoeffSpace d) (j : ℤ) (hj : j ∈ Set.Icc (jStar : ℤ) n)
      (z : Vec d) (hz : z ∈ Z j n) : w j n * v j n z a ≤ H a :=
    houter.2 a j hj z hz
  have hB : 0 ≤ B := by
    have hp := (Annealed.adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag
      jStar hjStar metric hmetric n m hn hnm).2.2.2.2.2
    dsimp only [B, Q, q]
    linarith only [hp]
  have htranslate (j k : ℤ) (z : Vec d) (t : Fin d → ℤ) (a : CoeffSpace d) :
      v j k (z + Source.AKL.intTranslation t) a = v j k z (translateCoeff t a) := by
    dsimp only [v, normalizedFluctuation]
    rw [Annealed.coarseBlock_adapted_translateCoeff]
  let L (a : CoeffSpace d) := w n m * B * ∑ y ∈ C, H (translateCoeff (τ y) a)
  have hsplit (j : ℤ) : w j m = w n m * w j n := by
    dsimp only [w]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  change ∀ a j, (jStar : ℤ) ≤ j → j ≤ n → ∀ z ∈ Z j m, w j m * v j m z a ≤ L a
  intro a j hj hjn z hz
  obtain ⟨y, hy, hzy⟩ := oneGrid_centers_decompose q hq j n m hjn hnm z hz
  have ht : v j n z a = v j n (z - y) (translateCoeff (τ y) a) := by
    have ht' := htranslate j n (z - y) (τ y) a
    rw [← hτ y hy, sub_add_cancel] at ht'
    exact ht'
  have hp : v j m z a ≤ B * v j n z a := oneGrid_fluctuation_pow_le_penalty
    d hd γ P E Ψ K S hstat hdag jStar hjStar metric hmetric j n m hn hnm z a
  have hd' := hdom (translateCoeff (τ y) a) j ⟨hj, hjn⟩ (z - y) hzy
  have hsum : H (translateCoeff (τ y) a) ≤ ∑ y ∈ C, H (translateCoeff (τ y) a) :=
    Finset.single_le_sum (f := fun y => H (translateCoeff (τ y) a))
      (fun y _ => hH (translateCoeff (τ y) a)) (by rw [← hC] at hy; exact hy)
  calc
    _ ≤ w j m * (B * v j n z a) := mul_le_mul_of_nonneg_left hp (hw j m).le
    _ = w n m * B * (w j n * v j n (z - y) (translateCoeff (τ y) a)) := by
      rw [hsplit, ht]
      ring
    _ ≤ w n m * B * H (translateCoeff (τ y) a) :=
      mul_le_mul_of_nonneg_left hd' (mul_nonneg (hw n m).le hB)
    _ ≤ L a := mul_le_mul_of_nonneg_left hsum (mul_nonneg (hw n m).le hB)

end

end HCPolySupport.HighContrast.Multiscale
