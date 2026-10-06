/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.BridgeBoundarySum

/-!
# High-contrast homogenization: Entry.Annealed.ShortBridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The successful short bridge on rounded grids

Ordinary support for `p.successful.short.bridge`. The actual
profile and histories retain their definitions. Their finite suprema
and moments are justified before the profile is used. Constants are selected
before the law in the printed order.

S5 is consumed transitively at ,
as documented in `BridgeSourceTail`.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter adaptedMean aspectRatio blockScale
  blockSub matSqrt normalizedBlock)
open HCPolySupport.HighContrast (adaptedCell adaptedCellTranslate centeredCube)
namespace HCPolySupport.HighContrast.Annealed
open MeasureTheory Geometry Multiscale
open scoped Matrix.Norms.L2Operator MatrixOrder
noncomputable section

private theorem bridge_zero_mem_cell {d : ℕ} (q : Mat d) (j : ℤ) :
    (0 : Vec d) ∈ adaptedCell q j := by
  refine ⟨0, ?_, matVecMul_zero q⟩
  rw [Recurrence.mem_centeredCube_iff]
  intro i
  have hp : (0 : ℝ) < 3 ^ j := zpow_pos (by norm_num) _
  simp only [Pi.zero_apply]
  constructor <;> linarith only [hp]

private theorem bridge_center_zero {d : ℕ} (q : Mat d) (j : ℤ) :
    adaptedCellCenter q j 0 = 0 := by
  simp only [adaptedCellCenter, Pi.zero_apply, Int.cast_zero]
  change (3 : ℝ) ^ j • matVecMul q 0 = 0
  rw [matVecMul_zero, smul_zero]

private theorem bridge_lattice_cell_finite {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q)
    (j k : ℤ) (hjk : j ≤ k) :
    (adaptedLatticeAtScale q j ∩ adaptedCell q k).Finite ∧
      (adaptedLatticeAtScale q j ∩ adaptedCell q k).Nonempty := by
  classical
  have hzero : adaptedCellAtCenter q k 0 = adaptedCell q k := by
    simp only [adaptedCellAtCenter, bridge_center_zero, adaptedCellTranslate, zero_add,
      Set.image_id']
  have hv : volume (adaptedCell q k) ≠ ⊤ := by
    simpa only [adaptedCellTranslate, zero_add, Set.image_id'] using
      Transport.volume_adaptedCellTranslate_ne_top q k 0
  have hf := finite_contained_adaptedCellIndices hq hv j
  refine ⟨(hf.image (adaptedCellCenter q j)).subset ?_, ⟨0, ⟨⟨0, bridge_center_zero q j⟩,
    bridge_zero_mem_cell q k⟩⟩⟩
  rintro z ⟨⟨w, rfl⟩, hz⟩
  refine ⟨w, ?_, rfl⟩
  rcases adaptedCellAtCenter_subset_or_disjoint hq hjk w 0 with hs | hs
  · rwa [hzero] at hs
  · have hc : adaptedCellCenter q j w ∈ adaptedCellAtCenter q j w := by
      exact ⟨0, bridge_zero_mem_cell q j, add_zero _⟩
    rw [hzero] at hs
    exact False.elim (Set.disjoint_left.mp hs hc hz)

private theorem bridge_integrable_finite_sup {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {s : Set ι} (hs : s.Finite) (hne : s.Nonempty)
    (f : ι → Ω → ℝ) (hf : ∀ i ∈ s, Integrable (f i) P)
    (hf0 : ∀ i ∈ s, ∀ a, 0 ≤ f i a) :
    Integrable (fun a => ⨆ i ∈ s, f i a) P ∧ (∀ a, 0 ≤ ⨆ i ∈ s, f i a) := by
  classical
  have hm := AEMeasurable.biSup s hs.countable (fun i hi => (hf i hi).aemeasurable)
  have hmax (a : Ω) : ∃ i ∈ s, f i a = ⨆ i ∈ s, f i a := by
    have hx : ∃ i ∈ s, sSup (∅ : Set ℝ) ≤ f i a := by
      obtain ⟨i, hi⟩ := hne
      exact ⟨i, hi, by simpa using hf0 i hi a⟩
    exact hs.ciSup_mem_image (fun i => f i a) hx
  have hnonneg (a : Ω) : 0 ≤ ⨆ i ∈ s, f i a := by
    obtain ⟨i, hi, he⟩ := hmax a
    rw [← he]
    exact hf0 i hi a
  refine ⟨?_, hnonneg⟩
  have hsum : Integrable (fun a => ∑ i ∈ hs.toFinset, f i a) P := by
    apply integrable_finsetSum
    intro i hi
    exact hf i (hs.mem_toFinset.mp hi)
  apply hsum.mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro a
  rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg a)]
  obtain ⟨i, hi, he⟩ := hmax a
  rw [← he]
  exact Finset.single_le_sum (fun r hr => hf0 r (hs.mem_toFinset.mp hr) a) (hs.mem_toFinset.mpr hi)

private theorem bridge_integrable_opNorm_pow {d Q : ℕ} {P : Measure (CoeffSpace d)}
    {H : CoeffSpace d → BlockMat d} (hH : SchattenMemLp P (Q : ℝ) H) (hQ : 1 ≤ (Q : ℝ)) :
    Integrable (fun a => blockOpNorm (H a) ^ Q) P := by
  have hm : AEMeasurable (fun a => toFullBlockMat (H a)) P :=
    AEMeasurable.of_eval fun i => AEMeasurable.of_eval fun j => (hH.measurable i j).aemeasurable
  have hi : Integrable (fun a => absSchattenNorm (Q : ℝ) (H a) ^ Q) P := by
    simpa only [Real.rpow_natCast] using hH.integrable
  apply hi.mono' (hm.norm.pow_const Q).aestronglyMeasurable
  filter_upwards [hH.symmetric] with a ha
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (Analysis.blockOpNorm_le_absSchattenNorm
    ((Analysis.toFullBlockMat_isHermitian_iff _).2 ha) hQ) Q

/-- All translated normalized fluctuations have the actual finite moments used
in both the profile and its history. This invokes bounded-window finiteness,
without imposing the original source window on auxiliary cells. -/
theorem bridge_fluctuation_memLqSchatten (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef) (j k : ℤ) (z : Vec d) :
    SchattenMemLp P (bigQ d γ : ℝ) (normalizedFluctuation P (explicitRoundedGrid jStar m) j k z)
      := by
  have hγ := hdag.g_mem
  have hQ : 1 ≤ (bigQ d γ : ℝ) := by exact_mod_cast (bigQ_pos d γ hγ)
  have hA := Source.memLqSchatten_coarseBlock_adapted d hd P γ E Ψ K S hstat hdag jStar hj m hm
    j z _ hQ
  have hc := Analysis.memLqSchatten_const P hQ (adaptedMean P (explicitRoundedGrid jStar m) j)
    ((Analysis.toFullBlockMat_isHermitian_iff _).1
      (adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm j).isHermitian)
  exact Source.memLqSchatten_normalizedBlock (hA.sub hc hQ) hQ _

/-- The history's two real suprema are finite, attained maxima on nonempty
families, and its defining random variable is integrable. In particular its
expectation is nonnegative for its intended reason. -/
theorem bridge_fluctuationHistory_integrable (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (k : ℤ) (hk : (jStar : ℤ) ≤ k) :
    Integrable (fun a => ⨆ j ∈ Set.Icc (jStar : ℤ) k,
      (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((k : ℝ) - j)) *
        ⨆ z ∈ adaptedLatticeAtScale (explicitRoundedGrid jStar m) j ∩ adaptedCell
          (explicitRoundedGrid jStar m) k,
          blockOpNorm (normalizedFluctuation P (explicitRoundedGrid jStar m) j k z a) ^ bigQ d
            γ) P ∧
      0 ≤ fluctuationHistory P γ (explicitRoundedGrid jStar m) jStar k := by
  let : NeZero d := ⟨by omega⟩
  have hγ := hdag.g_mem
  have hQ : 1 ≤ (bigQ d γ : ℝ) := by exact_mod_cast (bigQ_pos d γ hγ)
  let q := explicitRoundedGrid jStar m
  have hq := isUnit_roundedGrid hj hm
  have hinner (j : ℤ) (hji : j ∈ Set.Icc (jStar : ℤ) k) :=
    bridge_integrable_finite_sup P (bridge_lattice_cell_finite q hq j k hji.2).1
      (bridge_lattice_cell_finite q hq j k hji.2).2
      (fun z a => blockOpNorm (normalizedFluctuation P q j k z a) ^ bigQ d γ)
      (fun z _ => bridge_integrable_opNorm_pow
        (bridge_fluctuation_memLqSchatten d hd P γ E Ψ K S hstat hdag jStar hj m hm j k z) hQ)
      (fun _ _ _ => pow_nonneg (norm_nonneg _) _)
  have houter := bridge_integrable_finite_sup P (Set.finite_Icc (jStar : ℤ) k)
    (Set.nonempty_Icc.mpr hk)
    (fun j a => (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((k : ℝ) - j)) *
      ⨆ z ∈ adaptedLatticeAtScale q j ∩ adaptedCell q k,
        blockOpNorm (normalizedFluctuation P q j k z a) ^ bigQ d γ)
    (fun j hj => (hinner j hj).1.const_mul _)
    (fun j hj a => mul_nonneg (Real.rpow_nonneg (by norm_num) _) ((hinner j hj).2 a))
  exact ⟨houter.1, integral_nonneg houter.2⟩

/-- Nonnegativity of the actual complete profile, with all its random moments
and history suprema justified by the preceding receipts. -/
theorem bridge_profile_nonneg (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (k n : ℤ) (hk : (jStar : ℤ) ≤ k) (hkn : k ≤ n) :
    0 ≤ profile P γ (explicitRoundedGrid jStar m) jStar k n := by
  have hγ := hdag.g_mem
  let q := explicitRoundedGrid jStar m
  have hQ : 1 ≤ (bigQ d γ : ℝ) := by exact_mod_cast (bigQ_pos d γ hγ)
  have hmean (a b : ℤ) (ha : (jStar : ℤ) ≤ a) (hab : a ≤ b) :
      0 ≤ meanPenalty (bigQ d γ) (relMean P q a b) :=
    (adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag jStar hj m hm a b ha hab).2.2.2.2.2
  have hhist (a b : ℤ) (ha : (jStar : ℤ) ≤ a) : 0 ≤ meanHistory P γ q a b := by
    unfold meanHistory
    exact Finset.sum_nonneg (fun j hj => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (hmean j b (ha.trans (Finset.mem_Ico.mp hj).1) (Finset.mem_Ico.mp hj).2.le))
  obtain ⟨_hHistoryIntegrable, hfluc⟩ := bridge_fluctuationHistory_integrable d hd P γ E Ψ K S
    hstat hdag jStar hj m hm k hk
  have hHistory : 0 ≤ history P γ q jStar k := add_nonneg hfluc (hhist jStar k le_rfl)
  unfold profile
  apply add_nonneg (add_nonneg (mul_nonneg
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith only [hmean k n hk hkn])) hHistory)
    (hhist k n hk))
  apply Finset.sum_nonneg
  intro j _
  have hmem := bridge_fluctuation_memLqSchatten d hd P γ E Ψ K S hstat hdag jStar hj m hm j j 0
  have _hMomentIntegrable : Integrable (fun a =>
      absSchattenNorm (bigQ d γ : ℝ) (normalizedFluctuationSelf P q j a) ^ bigQ d γ) P := by
    simpa only [Real.rpow_natCast] using! hmem.integrable
  apply mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.exp_pos _).le)
  apply integral_nonneg_of_ae
  filter_upwards [hmem.symmetric] with a ha
  exact pow_nonneg (Analysis.absSchattenNorm_nonneg ((Analysis.toFullBlockMat_isHermitian_iff
    _).2 ha) hQ) _

private theorem bridge_polynomial_exp_decay {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    (1 + t) * Real.exp (-2 * b * t) ≤ (1 + 1 / b) * Real.exp (-b * t) := by
  have he : 1 ≤ Real.exp (b * t) := Real.one_le_exp_iff.mpr (mul_nonneg hb.le ht)
  have hte : t ≤ Real.exp (b * t) / b := by
    apply (le_div_iff₀ hb).2
    have h := Real.add_one_le_exp (b * t)
    linarith only [h]
  have hsum : 1 + t ≤ (1 + 1 / b) * Real.exp (b * t) := by
    calc
      _ ≤ Real.exp (b * t) + Real.exp (b * t) / b := add_le_add he hte
      _ = _ := by ring
  calc
    _ ≤ ((1 + 1 / b) * Real.exp (b * t)) * Real.exp (-2 * b * t) :=
      mul_le_mul_of_nonneg_right hsum (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- The printed source bound, including its bracket-dependent exponential.
Its explicit constant depends only on gamma; both real-power bases are positive
before they are converted to exponentials. -/
theorem bridge_source_bound (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pi c₀ B₀ : ℝ), 1 ≤ Pi → 0 < c₀ →
      ∀ (L : ℕ), 1 ≤ L → ∀ (m mPlus : Mat d), m.PosDef → mPlus.PosDef →
        projectiveDistance m mPlus ≤ 1 → ∀ (jStar k n : ℤ), jStar ≤ k → k ≤ n →
        Real.log (‖m‖ * ‖m⁻¹‖) ≤ c₀ / (L : ℝ) *
          ((k : ℝ) - jStar - (⌈B₀ * Real.logb 3 (2 + Pi)⌉ : ℤ)) →
        (1 + Pi * (Real.sqrt (‖m‖ * ‖m⁻¹‖) + Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖)) ^ 2) *
            (1 + (n : ℝ) + L - jStar) * (3 : ℝ) ^ (-((1 - γ) / 8) * ((n : ℝ) - jStar)) ≤
          C * (1 + (L : ℝ)) * (2 + Pi) ^ (1 - (1 - γ) * B₀ / 16) *
            Real.exp (-((k : ℝ) - jStar - (⌈B₀ * Real.logb 3 (2 + Pi)⌉ : ℤ)) *
              ((1 - γ) * Real.log 3 / 16 - 2 * c₀ / (L : ℝ))) := by
  let : NeZero d := ⟨by omega⟩
  let b := (1 - γ) * Real.log 3 / 16
  let D := (1 + Real.exp 1) ^ 2
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hb : 0 < b := div_pos (mul_pos (sub_pos.mpr hγ.2) hlog) (by norm_num)
  have hD : 1 ≤ D := by dsimp [D]; nlinarith only [Real.exp_pos 1]
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  refine ⟨D * (1 + 1 / b), by positivity, ?_⟩
  intro Pi c₀ B₀ hPi hc₀ L hL m mPlus hm hmPlus hpr jStar k n hjk hkn hecc
  let R := (k : ℝ) - jStar - (⌈B₀ * Real.logb 3 (2 + Pi)⌉ : ℤ)
  let t := (n : ℝ) - jStar
  let x := c₀ / (L : ℝ) * R
  have hR : 0 ≤ R := bracket_nonneg_of_eccentricity hm hc₀ hL hecc
  have hLn : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have ht : 0 ≤ t := by dsimp [t]; exact_mod_cast (sub_nonneg.mpr (hjk.trans hkn))
  have hx : 0 ≤ x := mul_nonneg (div_nonneg hc₀.le hLn) hR
  have hbase : 0 < 2 + Pi := by linarith only [hPi]
  have hPi0 : 0 ≤ Pi := by linarith only [hPi]
  have he := eccentricity_le_exp_of_log_le hm hecc
  have hePlus := eccentricity_le_of_projectiveDistance_le hm hmPlus hpr
  have hsum : Real.sqrt (‖m‖ * ‖m⁻¹‖) + Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖) ≤
      (1 + Real.exp 1) * Real.exp x := by
    have hmul := mul_le_mul_of_nonneg_left he (Real.exp_pos 1).le
    linarith only [he, hePlus, hmul]
  have hsquare : (Real.sqrt (‖m‖ * ‖m⁻¹‖) + Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖)) ^ 2 ≤
      D * Real.exp (2 * x) := by
    have hsq := pow_le_pow_left₀ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hsum 2
    simpa only [mul_pow, D, ← Real.exp_nat_mul] using! hsq
  have he1 : 1 ≤ Real.exp (2 * x) := Real.one_le_exp_iff.mpr (by linarith only [hx])
  have hDE : 1 ≤ D * Real.exp (2 * x) := by simpa only [one_mul] using mul_le_mul hD he1 (by
    norm_num : (0 : ℝ) ≤ 1) hD0.le
  have hW : 1 + Pi * (Real.sqrt (‖m‖ * ‖m⁻¹‖) + Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖)) ^ 2 ≤
      D * (2 + Pi) * Real.exp (2 * x) := by
    have hmul := mul_le_mul_of_nonneg_left hsquare hPi0
    nlinarith only [hmul, hDE]
  have hpoly : (1 + (n : ℝ) + L - jStar) *
      (3 : ℝ) ^ (-((1 - γ) / 8) * ((n : ℝ) - jStar)) ≤
      (1 + (L : ℝ)) * (1 + 1 / b) * Real.exp (-b * t) := by
    have hlinear : 1 + (n : ℝ) + L - jStar ≤ (1 + (L : ℝ)) * (1 + t) := by
      dsimp only [t] at ht ⊢
      nlinarith only [mul_nonneg hLn ht]
    have heq : (3 : ℝ) ^ (-((1 - γ) / 8) * ((n : ℝ) - jStar)) = Real.exp (-2 * b * t) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      congr 1
      dsimp [b, t]
      ring
    rw [heq]
    calc
      _ ≤ ((1 + (L : ℝ)) * (1 + t)) * Real.exp (-2 * b * t) :=
        mul_le_mul_of_nonneg_right hlinear (Real.exp_pos _).le
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (bridge_polynomial_exp_decay hb ht) (by positivity : 0 ≤ 1 + (L : ℝ))
  have htR : R + (⌈B₀ * Real.logb 3 (2 + Pi)⌉ : ℤ) ≤ t := by
    dsimp [R, t]
    have hkR : (k : ℝ) ≤ n := by exact_mod_cast hkn
    linarith only [hkR]
  have hceil : B₀ * Real.logb 3 (2 + Pi) ≤ (⌈B₀ * Real.logb 3 (2 + Pi)⌉ : ℤ) := Int.le_ceil _
  have hsep : Real.exp (2 * x) * Real.exp (-b * t) ≤
      Real.exp (-R * (b - 2 * c₀ / (L : ℝ))) * Real.exp (-b * B₀ * Real.logb 3 (2 + Pi)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h₁ := mul_le_mul_of_nonneg_left htR hb.le
    have h₂ := mul_le_mul_of_nonneg_left hceil hb.le
    dsimp only [x]
    simp only [div_eq_mul_inv]
    nlinarith only [h₁, h₂]
  have hpower : (2 + Pi) * Real.exp (-b * B₀ * Real.logb 3 (2 + Pi)) =
      (2 + Pi) ^ (1 - (1 - γ) * B₀ / 16) := by
    rw [← Real.exp_log hbase, ← Real.exp_add, Real.rpow_def_of_pos (Real.exp_pos _)]
    congr 1
    dsimp [b, Real.logb]
    simp only [Real.log_exp]
    field_simp [hlog.ne']
    ring
  calc
    _ ≤ (D * (2 + Pi) * Real.exp (2 * x)) *
        ((1 + (L : ℝ)) * (1 + 1 / b) * Real.exp (-b * t)) := by
      rw [mul_assoc]
      apply mul_le_mul hW hpoly
      · exact mul_nonneg (by dsimp [t] at ht; linarith only [ht, hLn]) (Real.rpow_nonneg (by
        norm_num) _)
      · positivity
    _ = (D * (1 + 1 / b) * (1 + (L : ℝ))) * (2 + Pi) *
        (Real.exp (2 * x) * Real.exp (-b * t)) := by ring
    _ ≤ (D * (1 + 1 / b) * (1 + (L : ℝ))) * (2 + Pi) *
        (Real.exp (-R * (b - 2 * c₀ / (L : ℝ))) * Real.exp (-b * B₀ * Real.logb 3 (2 + Pi))) :=
      mul_le_mul_of_nonneg_left hsep (by positivity)
    _ = _ := by
      calc
        _ = D * (1 + 1 / b) * (1 + (L : ℝ)) *
            ((2 + Pi) * Real.exp (-b * B₀ * Real.logb 3 (2 + Pi))) *
            Real.exp (-R * (b - 2 * c₀ / (L : ℝ))) := by ring
        _ = _ := by rw [hpower]

private theorem bridge_full_scale {d : ℕ} (c : ℝ) (F : BlockMat d) :
    toFullBlockMat (blockScale c F) = c • toFullBlockMat F := by
  ext (i | i) (j | j) <;> rfl

private theorem bridge_full_difference {d : ℕ} (H F : BlockMat d) :
    toFullBlockMat (blockSub H F) = toFullBlockMat H - toFullBlockMat F := by
  ext (i | i) (j | j) <;> rfl

private theorem bridge_full_identity (d : ℕ) : toFullBlockMat (Book.Ch02.blockIdentity d) = 1 := by
  ext (i | i) (j | j) <;>
    simp [Book.Ch02.blockIdentity, Book.Ch02.blockDiag, toFullBlockMat, Matrix.one_apply]

private theorem bridge_normalize_order {d : ℕ} {A B F : BlockMat d}
    (hA : (toFullBlockMat A).IsHermitian) (hB : (toFullBlockMat B).IsHermitian)
    (hF : (toFullBlockMat F).PosDef) (h : BlockMatLoewnerLE A B) :
    BlockMatLoewnerLE (normalizedBlock A F) (normalizedBlock B F) := by
  let R := matSqrt (toFullBlockMat F)⁻¹
  have hR : R.PosDef := matSqrt_inv_posDef_full hF
  have hsym (H : BlockMat d) (hH : (toFullBlockMat H).IsHermitian) :
      (toFullBlockMat (normalizedBlock H F)).IsHermitian := by
    rw [normalizedBlock, toFullBlockMat_ofFullBlockMat]
    change (R * toFullBlockMat H * R).IsHermitian
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_mul, hR.isHermitian.eq, hH.eq, mul_assoc]
  apply (fullBlock_le_iff (hsym A hA) (hsym B hB)).1
  apply Matrix.le_iff.mpr
  have hh := (Matrix.le_iff.mp ((fullBlock_le_iff hA hB).2 h)).conjTranspose_mul_mul_same R
  simpa only [normalizedBlock, toFullBlockMat_ofFullBlockMat, R, hR.isHermitian.eq, mul_sub,
    sub_mul] using hh

private theorem bridge_hermitian_norm_iff {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {M : Matrix ι ι ℝ} (hM : M.IsHermitian) (ε : ℝ) :
    ‖M‖ ≤ ε ↔ -(ε • (1 : Matrix ι ι ℝ)) ≤ M ∧ M ≤ ε • 1 := by
  rw [← Algebra.algebraMap_eq_smul_one, ← map_neg]
  constructor
  · intro h
    constructor
    · apply algebraMap_le_of_le_spectrum (ha := hM)
      intro x hx
      have hb := spectrum.norm_le_norm_of_mem hx
      rw [Real.norm_eq_abs] at hb
      have hn := (abs_le.mp (hb.trans h)).1
      exact hn
    · apply le_algebraMap_of_spectrum_le (ha := hM)
      intro x hx
      exact (le_abs_self x).trans ((spectrum.norm_le_norm_of_mem hx).trans h)
  · rintro ⟨hl, hu⟩
    have hunitnorm (U : unitary (Matrix ι ι ℝ)) (A : Matrix ι ι ℝ) :
        ‖(Unitary.conjStarAlgAut ℝ _ U) A‖ = ‖A‖ := by
      rw [Unitary.conjStarAlgAut_apply]
      rw [CStarRing.norm_mul_mem_unitary
        (A := (U : Matrix ι ι ℝ) * A) (hU := Unitary.star_mem U.prop)]
      exact CStarRing.norm_mem_unitary_mul A U.prop
    have hnorm : ‖M‖ = ‖hM.eigenvalues‖ := by
      conv_lhs => rw [hM.spectral_theorem]
      rw [hunitnorm]
      simp
    have he (i : ι) : |hM.eigenvalues i| ≤ ε := by
      have hspec : hM.eigenvalues i ∈ spectrum ℝ M := by
        rw [hM.spectrum_real_eq_range_eigenvalues]
        exact ⟨i, rfl⟩
      exact abs_le.mpr ⟨(algebraMap_le_iff_le_spectrum (ha := hM)).mp hl _ hspec,
        (le_algebraMap_iff_spectrum_le (ha := hM)).mp hu _ hspec⟩
    have hε : 0 ≤ ε := (abs_nonneg _).trans (he (Classical.arbitrary ι))
    rw [hnorm]
    exact (pi_norm_le_iff_of_nonneg hε).2 (fun i => by simpa only [Real.norm_eq_abs] using he i)

/-- The normalized operator error and the two relative quadratic errors are
equivalent. The positive normalizer is used in both directions; no singular
normalization or scalar commutation of matrices is used. -/
private theorem bridge_normalized_error_iff {d : ℕ} [NeZero d] (H F : BlockMat d)
    (hH : (toFullBlockMat H).IsHermitian) (hF : (toFullBlockMat F).PosDef) (ε : ℝ) :
    blockOpNorm (blockSub (normalizedBlock H F) (Book.Ch02.blockIdentity d)) ≤ ε ↔
      BlockMatLoewnerLE (blockSub H F) (blockScale ε F) ∧
        BlockMatLoewnerLE (blockSub F H) (blockScale ε F) := by
  let R := matSqrt (toFullBlockMat F)⁻¹
  have hR : R.PosDef := matSqrt_inv_posDef_full hF
  have hsym (A : BlockMat d) (hA : (toFullBlockMat A).IsHermitian) :
      (toFullBlockMat (normalizedBlock A F)).IsHermitian := by
    rw [normalizedBlock, toFullBlockMat_ofFullBlockMat]
    change (R * toFullBlockMat A * R).IsHermitian
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_mul, hR.isHermitian.eq, hA.eq, mul_assoc]
  have hsubHF : (toFullBlockMat (blockSub H F)).IsHermitian := by
    rw [bridge_full_difference]; exact hH.sub hF.isHermitian
  have hsubFH : (toFullBlockMat (blockSub F H)).IsHermitian := by
    rw [bridge_full_difference]; exact hF.isHermitian.sub hH
  have hscale : (toFullBlockMat (blockScale ε F)).IsHermitian := by
    rw [bridge_full_scale]
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, hF.isHermitian.eq]
  have hs : toFullBlockMat (normalizedBlock (blockScale ε F) F) = ε • 1 := by
    rw [normalizedBlock, toFullBlockMat_ofFullBlockMat, bridge_full_scale, Matrix.mul_smul,
      Matrix.smul_mul, matSqrt_inv_conj hF]
  let M := toFullBlockMat (blockSub (normalizedBlock H F) (Book.Ch02.blockIdentity d))
  have hM : M.IsHermitian := by
    dsimp only [M]
    rw [bridge_full_difference, bridge_full_identity]
    exact (hsym H hH).sub Matrix.isHermitian_one
  have h₁ : toFullBlockMat (normalizedBlock (blockSub H F) F) = M := by
    dsimp only [M]
    rw [bridge_full_difference, bridge_full_identity]
    simp only [normalizedBlock, toFullBlockMat_ofFullBlockMat, bridge_full_difference, mul_sub,
      sub_mul, matSqrt_inv_conj hF]
  have h₂ : toFullBlockMat (normalizedBlock (blockSub F H) F) = -M := by
    dsimp only [M]
    rw [bridge_full_difference, bridge_full_identity]
    simp only [normalizedBlock, toFullBlockMat_ofFullBlockMat, bridge_full_difference, mul_sub,
      sub_mul, matSqrt_inv_conj hF, neg_sub]
  change ‖M‖ ≤ ε ↔ _
  rw [bridge_hermitian_norm_iff hM ε]
  constructor
  · rintro ⟨hl, hu⟩
    constructor
    · apply bridge_unnormalize_order hsubHF hscale hF
      apply (fullBlock_le_iff (hsym _ hsubHF) (hsym _ hscale)).1
      simpa only [h₁, hs] using hu
    · apply bridge_unnormalize_order hsubFH hscale hF
      apply (fullBlock_le_iff (hsym _ hsubFH) (hsym _ hscale)).1
      simpa only [h₂, hs, neg_le] using hl
  · rintro ⟨hu, hl⟩
    have hu' := (fullBlock_le_iff (hsym _ hsubHF) (hsym _ hscale)).2
      (bridge_normalize_order hsubHF hscale hF hu)
    have hl' := (fullBlock_le_iff (hsym _ hsubFH) (hsym _ hscale)).2
      (bridge_normalize_order hsubFH hscale hF hl)
    simpa only [h₁, h₂, hs, neg_le] using And.intro hl' hu'

/-- The ceiling in the length hypothesis supplies precisely the factor sigma. -/
theorem bridge_length_decay (L₀ L : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioc (0 : ℝ) 1)
    (hL : (L₀ : ℤ) + ⌈Real.logb 3 σ⁻¹⌉ ≤ (L : ℤ)) :
    L₀ ≤ L ∧ (3 : ℝ) ^ (-(L : ℝ)) ≤ (3 : ℝ) ^ (-(L₀ : ℝ)) * σ := by
  have hinv : 1 ≤ σ⁻¹ := (one_le_inv₀ hσ.1).2 hσ.2
  have hlog : 0 ≤ Real.logb 3 σ⁻¹ := Real.logb_nonneg (by norm_num) hinv
  have hc : (0 : ℤ) ≤ ⌈Real.logb 3 σ⁻¹⌉ := Int.ceil_nonneg hlog
  have hreal : (L₀ : ℝ) + Real.logb 3 σ⁻¹ ≤ L := by
    have hcast : (L₀ : ℝ) + (⌈Real.logb 3 σ⁻¹⌉ : ℤ) ≤ L := by exact_mod_cast hL
    have hceil := Int.le_ceil (Real.logb 3 σ⁻¹)
    linarith only [hcast, hceil]
  refine ⟨by omega, ?_⟩
  have he : (3 : ℝ) ^ (-Real.logb 3 σ⁻¹) = σ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_logb (by norm_num) (by norm_num)
      (inv_pos.mpr hσ.1), inv_inv]
  calc
    _ ≤ (3 : ℝ) ^ (-((L₀ : ℝ) + Real.logb 3 σ⁻¹)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg hreal)
    _ = _ := by rw [neg_add, Real.rpow_add (by norm_num), he]

private theorem bridge_choose_initial (γ C K₀ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (hC : 0 < C) (hK₀ : 1 ≤ K₀) :
    ∃ (c₀ : ℝ) (L₀ : ℕ), c₀ ∈ Set.Ioo (0 : ℝ) 1 ∧ 1 ≤ L₀ ∧
      C * c₀ ≤ 1 / 3 ∧ 2 * c₀ / (L₀ : ℝ) ≤ (1 - γ) * Real.log 3 / 16 ∧
        C * K₀ * (3 : ℝ) ^ (-(L₀ : ℝ)) ≤ 1 / 3 := by
  let c₀ := 1 / (3 * (C + 1))
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  have hcid : 3 * (C + 1) * c₀ = 1 := by dsimp [c₀]; field_simp
  have hc₁ : c₀ < 1 := by nlinarith only [hcid, hc₀, hC]
  have hCc : C * c₀ ≤ 1 / 3 := by nlinarith only [hcid, hc₀]
  let b := (1 - γ) * Real.log 3 / 16
  have hb : 0 < b := div_pos (mul_pos (sub_pos.mpr hγ.2) (Real.log_pos (by norm_num))) (by norm_num)
  let L₀ := 1 + ⌈max (2 * c₀ / b) (Real.logb 3 (3 * C * K₀))⌉₊
  have hL₁ : 1 ≤ L₀ := by dsimp [L₀]; omega
  have hLp : 0 < (L₀ : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hL₁)
  have hmax : max (2 * c₀ / b) (Real.logb 3 (3 * C * K₀)) ≤ (L₀ : ℝ) := by
    have hh := Nat.le_ceil (max (2 * c₀ / b) (Real.logb 3 (3 * C * K₀)))
    dsimp only [L₀]
    push_cast
    linarith only [hh]
  have hsmall : 2 * c₀ / (L₀ : ℝ) ≤ b := by
    apply (div_le_iff₀ hLp).2
    have hh := (div_le_iff₀ hb).mp ((le_max_left _ _).trans hmax)
    linarith only [hh]
  have harg : 0 < 3 * C * K₀ := mul_pos (by positivity) (zero_lt_one.trans_le hK₀)
  have hpow : 3 * C * K₀ ≤ (3 : ℝ) ^ (L₀ : ℝ) :=
    (Real.logb_le_iff_le_rpow (by norm_num) harg).mp ((le_max_right _ _).trans hmax)
  have hdecay : C * K₀ * (3 : ℝ) ^ (-(L₀ : ℝ)) ≤ 1 / 3 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), ← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.rpow_pos_of_pos (by norm_num) _)).2
    linarith only [hpow]
  exact ⟨c₀, L₀, ⟨hc₀, hc₁⟩, hL₁, hCc, hsmall, hdecay⟩

/-- A logarithm and ceiling choose B0 before Pi, uniformly for all Pi at least
one. Thus this choice precedes the coefficient law and reference block. -/
theorem bridge_choose_source_separation (γ C : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (hC : 0 < C) (σ : ℝ) (hσ : 0 < σ) (L : ℕ) :
    ∃ B₀ : ℝ, 1 ≤ B₀ ∧ ∀ Pi : ℝ, 1 ≤ Pi →
      C * (1 + (L : ℝ)) * (2 + Pi) ^ (1 - (1 - γ) * B₀ / 16) ≤ σ / 3 := by
  let N : ℤ := max 0 ⌈Real.logb 3 (3 * C * (1 + (L : ℝ)) / σ)⌉
  let B₀ := 16 / (1 - γ) * (1 + (N : ℝ))
  have hden : 0 < 1 - γ := sub_pos.mpr hγ.2
  have hN0 : (0 : ℝ) ≤ N := by exact_mod_cast (show (0 : ℤ) ≤ N from le_max_left _ _)
  have hb16 : 16 ≤ 16 / (1 - γ) := by
    apply (le_div_iff₀ hden).2
    linarith only [hγ.1]
  have hB : 1 ≤ B₀ := by
    dsimp only [B₀]
    nlinarith only [hb16, hN0, mul_nonneg (show (0 : ℝ) ≤ 16 / (1 - γ) by positivity) hN0]
  have hExp : 1 - (1 - γ) * B₀ / 16 = -(N : ℝ) := by
    dsimp [B₀]
    field_simp [hden.ne']
    ring
  refine ⟨B₀, hB, ?_⟩
  intro Pi hPi
  have _hbase : 0 < 2 + Pi := by linarith only [hPi]
  have harg : 0 < 3 * C * (1 + (L : ℝ)) / σ := by positivity
  have hlog : Real.logb 3 (3 * C * (1 + (L : ℝ)) / σ) ≤ (N : ℝ) := by
    have hcast : ((⌈Real.logb 3 (3 * C * (1 + (L : ℝ)) / σ)⌉ : ℤ) : ℝ) ≤ (N : ℝ) :=
      Int.cast_le.mpr (le_max_right (0 : ℤ) _)
    exact (Int.le_ceil _).trans hcast
  have hpow := (Real.logb_le_iff_le_rpow (by norm_num) harg).mp hlog
  have h₃ : C * (1 + (L : ℝ)) * (3 : ℝ) ^ (-(N : ℝ)) ≤ σ / 3 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), ← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.rpow_pos_of_pos (by norm_num) _)).2
    have hh := (div_le_iff₀ hσ).mp hpow
    linarith only [hh]
  rw [hExp]
  apply le_trans _ h₃
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith only [hPi]) (neg_nonpos.mpr hN0)

/-- The preliminary normalized short-bridge comparison. The displayed lower
bound on length is discharged by the ordered constant choice in the endpoint. -/
theorem bridge_preliminary_comparison (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ K₀ Csrc C : ℝ, 1 ≤ K₀ ∧ 0 < Csrc ∧ 0 < C ∧
      ∀ c₀ : ℝ, c₀ ∈ Set.Ioo (0 : ℝ) 1 → ∀ σ : ℝ, σ ∈ Set.Ioc (0 : ℝ) 1 →
        ∀ L : ℕ, 1 ≤ L → 2 * c₀ / (L : ℝ) ≤ (1 - γ) * Real.log 3 / 16 → ∀ B₀ : ℝ,
          ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
            (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
            IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ K S →
            ∀ jStar : ℕ, 2 * d ≤ 3 ^ jStar →
              ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
              ∀ (m mPlus : Mat d), m.PosDef → mPlus.PosDef →
                ∀ k n : ℤ, (jStar : ℤ) ≤ k → k ≤ n →
                  adaptedCell (explicitRoundedGrid jStar m) (n + 2 * (L : ℤ)) ∪
                      adaptedCell (explicitRoundedGrid jStar mPlus) (n + (L : ℤ)) ⊆
                    centeredCube d (2 * (jStar : ℤ)) →
                  Real.log (‖m‖ * ‖m⁻¹‖) ≤ c₀ / (L : ℝ) * ((k : ℝ) - jStar -
                    (⌈B₀ * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)) →
                  projectiveDistance m mPlus ≤ 1 →
                  profile P γ (explicitRoundedGrid jStar m) jStar k n +
                      determinantDrift P γ (explicitRoundedGrid jStar m) jStar n +
                    detIncrement P (explicitRoundedGrid jStar m) n (n + 2 * (L : ℤ)) ≤ c₀ * σ →
                  blockOpNorm (blockSub
                    (normalizedBlock (adaptedMean P (explicitRoundedGrid jStar mPlus) (n + (L : ℤ)))
                      (adaptedMean P (explicitRoundedGrid jStar m) (n + 2 * (L : ℤ))))
                        (Book.Ch02.blockIdentity d)) ≤
                    C * c₀ * σ + C * K₀ * (3 : ℝ) ^ (-(L : ℝ)) +
                      C * (1 + (L : ℝ)) * (2 + aspectRatio E) ^ (1 - (1 - γ) * B₀ / 16) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨K₀, hK₀, hratio⟩ := exists_gridRatio_bound d hd
  obtain ⟨Csrc, Cb, hCsrc, hCb, hbridge⟩ := bridge_endpoint_errors d hd γ hγ K₀ hK₀
  obtain ⟨Cs, hCs, hsource⟩ := bridge_source_bound d hd γ hγ
  let C := Cb * (Cs + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hCbC : Cb ≤ C := by dsimp [C]; nlinarith only [mul_pos hCb hCs]
  have hCbCsC : Cb * Cs ≤ C := by dsimp [C]; nlinarith only [hCb]
  refine ⟨K₀, Csrc, C, hK₀, hCsrc, hC, ?_⟩
  intro c₀ hc₀ σ hσ L hL hlength B₀ P hP E Ψ K S hstat hdag jStar hj hsrc
    m mPlus hm hmPlus k n hk hkn hcontain hecc hpr hsmall
  let q := explicitRoundedGrid jStar m
  let F := adaptedMean P q (n + 2 * (L : ℤ))
  let H := adaptedMean P (explicitRoundedGrid jStar mPlus) (n + (L : ℤ))
  let T := (1 + aspectRatio E * (Real.sqrt (‖m‖ * ‖m⁻¹‖) + Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖)) ^ 2) *
    (1 + (n : ℝ) + L - jStar) * (3 : ℝ) ^ (-((1 - γ) / 8) * ((n : ℝ) - jStar))
  let V := (1 + (L : ℝ)) * (2 + aspectRatio E) ^ (1 - (1 - γ) * B₀ / 16)
  have hε0 : 0 ≤ c₀ * σ := mul_nonneg hc₀.1.le hσ.1.le
  have hε1 : c₀ * σ ≤ 1 := by
    exact (mul_le_mul_of_nonneg_right hc₀.2.le hσ.1.le).trans (by simpa using hσ.2)
  have hprofile := bridge_profile_nonneg d hd P γ E Ψ K S hstat hdag jStar hj m hm k n hk hkn
  have hD0 := bridge_determinantDrift_nonneg d hd P γ E Ψ K S hstat hdag jStar hj m hm n
  have hΔ0 := logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hj m hm n
    (n + 2 * (L : ℤ)) (hk.trans hkn) (by omega)
  have hD : determinantDrift P γ q jStar n ≤ c₀ * σ := by linarith only [hsmall, hprofile, hΔ0]
  have hΔ : detIncrement P q n (n + 2 * (L : ℤ)) ≤ c₀ * σ := by linarith only [hsmall, hprofile,
    hD0]
  have herr := hbridge P E Ψ K S hstat hdag jStar hj hsrc m mPlus hm hmPlus
    (hratio jStar hj m mPlus hm hmPlus hpr) n L (hk.trans hkn) hL hcontain (c₀ * σ) ⟨hε0, hε1⟩ hD hΔ
  have hnorm := (bridge_normalized_error_iff H F
    (adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj mPlus hmPlus (n + (L : ℤ))).isHermitian
    (adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm (n + 2 * (L : ℤ)))
    (Cb * (c₀ * σ) + Cb * K₀ * (3 : ℝ) ^ (-(L : ℝ)) + Cb * T)).2 herr
  have hPi := one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hbase : 0 < 2 + aspectRatio E := by linarith only [hPi]
  have hV : 0 ≤ V := mul_nonneg (by positivity) (Real.rpow_nonneg hbase.le _)
  have hR := bracket_nonneg_of_eccentricity hm hc₀.1 hL hecc
  have hse := hsource (aspectRatio E) c₀ B₀ hPi hc₀.1 L hL m mPlus hm hmPlus hpr jStar k n hk
    hkn hecc
  have hexp : Real.exp (-((k : ℝ) - jStar -
      (⌈B₀ * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)) *
        ((1 - γ) * Real.log 3 / 16 - 2 * c₀ / (L : ℝ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hR) (sub_nonneg.mpr hlength)
  have hT : T ≤ Cs * V := by
    have hh := mul_le_of_le_one_right (mul_nonneg hCs.le hV) hexp
    dsimp only [V] at hh ⊢
    simp only [← mul_assoc, Int.cast_natCast] at hse hh
    simpa only [T, mul_assoc] using hse.trans hh
  have h₁ := mul_le_mul_of_nonneg_right hCbC hε0
  have h₂ := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCbC (zero_lt_one.trans_le hK₀).le)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (-(L : ℝ)))
  have h₃ : Cb * T ≤ C * V := by
    calc
      _ ≤ Cb * (Cs * V) := mul_le_mul_of_nonneg_left hT hCb.le
      _ ≤ _ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hCbCsC hV
  have htot := add_le_add (add_le_add h₁ h₂) h₃
  dsimp only [V] at htot
  simp only [← mul_assoc] at hnorm htot
  exact hnorm.trans htot

/-- The ordinary rounded-grid endpoint with all stochastic, source, and normalization obligations
discharged. The unit-range and separation premises retain their positions. -/
theorem successful_short_bridge_roundedGrid (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ (L₀ : ℕ) (c₀ : ℝ), c₀ ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∃ Csrc : ℝ, 0 < Csrc ∧
        ∀ σ : ℝ, σ ∈ Set.Ioc (0 : ℝ) 1 →
        ∀ L : ℕ, (L₀ : ℤ) + ⌈Real.logb 3 σ⁻¹⌉ ≤ (L : ℤ) →
          ∃ B₀ : ℝ, 1 ≤ B₀ ∧
            ∀ (P : MeasureTheory.Measure (CoeffSpace d))
              [MeasureTheory.IsProbabilityMeasure P]
              (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
              IsStationaryLaw P → IsUnitRangeLaw P →
              CoarseEllipticityDagger P γ E Ψ K S →
              ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
                ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
                ∀ (m mPlus : Mat d), m.PosDef → mPlus.PosDef →
                  ∀ k n : ℤ, (jStar : ℤ) ≤ k → k ≤ n →
                    HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L
                      : ℤ)) ∪
                        HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar mPlus) (n +
                          (L : ℤ)) ⊆
                      HighContrast.centeredCube d (2 * (jStar : ℤ)) →
                    Real.log (‖m‖ * ‖m⁻¹‖) ≤
                      c₀ / (L : ℝ) * ((k : ℝ) - (jStar : ℝ) -
                        (⌈B₀ * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)) →
                    k + 2 * (bigQ d γ : ℤ) ≤ n →
                    projectiveDistance m mPlus ≤ 1 →
                    profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
                          determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n +
                        detIncrement P (Geometry.explicitRoundedGrid jStar m) n (n + 2 * (L : ℤ)) ≤
                      c₀ * σ →
                    BlockMatLoewnerLE
                        (blockScale (1 - σ)
                          (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L : ℤ))))
                        (adaptedMean P (Geometry.explicitRoundedGrid jStar mPlus) (n + (L : ℤ))) ∧
                      BlockMatLoewnerLE
                        (adaptedMean P (Geometry.explicitRoundedGrid jStar mPlus) (n + (L : ℤ)))
                        (blockScale (1 + σ)
                          (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L :
                            ℤ)))) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨K₀, Csrc, C, hK₀, hCsrc, hC, hpre⟩ := bridge_preliminary_comparison d hd γ hγ
  obtain ⟨c₀, L₀, hc₀, hL₀, hCc, hlength, hboundary⟩ := bridge_choose_initial γ C K₀ hγ hC hK₀
  refine ⟨L₀, c₀, hc₀, Csrc, hCsrc, ?_⟩
  intro σ hσ L hL
  obtain ⟨hL₀L, hdecay⟩ := bridge_length_decay L₀ L σ hσ hL
  have hLpos : 1 ≤ L := hL₀.trans hL₀L
  have hL₀p : 0 < (L₀ : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hL₀)
  have hlong : 2 * c₀ / (L : ℝ) ≤ (1 - γ) * Real.log 3 / 16 := by
    exact (div_le_div_of_nonneg_left (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc₀.1.le) hL₀p (by
      exact_mod_cast hL₀L)).trans hlength
  obtain ⟨B₀, hB₀, hsource⟩ := bridge_choose_source_separation γ C hγ hC σ hσ.1 L
  refine ⟨B₀, hB₀, ?_⟩
  intro P hP E Ψ K S hstat _hunit hdag jStar hj hsrc m mPlus hm hmPlus k n hk hkn
    hcontain hecc _hgap hpr hsmall
  have hn := hpre c₀ hc₀ σ hσ L hLpos hlong B₀ P E Ψ K S hstat hdag jStar hj hsrc
    m mPlus hm hmPlus k n hk hkn hcontain hecc hpr hsmall
  have h₁ : C * c₀ * σ ≤ σ / 3 := by
    have hh := mul_le_mul_of_nonneg_right hCc hσ.1.le
    linarith only [hh]
  have h₂ : C * K₀ * (3 : ℝ) ^ (-(L : ℝ)) ≤ σ / 3 := by
    have hh := mul_le_mul_of_nonneg_left hdecay (mul_nonneg hC.le (zero_lt_one.trans_le hK₀).le)
    have hb := mul_le_mul_of_nonneg_right hboundary hσ.1.le
    nlinarith only [hh, hb]
  have h₃ := hsource (aspectRatio E) (one_le_aspectRatio_of_coarseEllipticityDagger hdag)
  have hnorm : blockOpNorm (blockSub
      (normalizedBlock (adaptedMean P (explicitRoundedGrid jStar mPlus) (n + (L : ℤ)))
        (adaptedMean P (explicitRoundedGrid jStar m) (n + 2 * (L : ℤ))))
          (Book.Ch02.blockIdentity d)) ≤ σ := by
    linarith only [hn, h₁, h₂, h₃]
  have herr := (bridge_normalized_error_iff _ _
    (adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj mPlus hmPlus (n + (L : ℤ))).isHermitian
    (adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm (n + 2 * (L : ℤ))) σ).1 hnorm
  have hquad (A B : BlockMat d) (v : BlockVec d) :
      (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (blockSub A B) v) =
        (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul A v) -
          (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul B v) := by
    have hh := blockVecDot_blockMatVecMul_ofFullBlockMat_sub A B v
    change blockVecDot v (blockMatVecMul (blockSub A B) v) = _ at hh
    rw [hh]
    ring
  constructor
  · intro v
    have hh := herr.2 v
    simp only [hquad, Source.quadratic_blockScale] at hh ⊢
    linarith only [hh]
  · intro v
    have hh := herr.1 v
    simp only [hquad, Source.quadratic_blockScale] at hh ⊢
    linarith only [hh]

end
end HCPolySupport.HighContrast.Annealed
