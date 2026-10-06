/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.OneGrid.FixedSpan

/-!
# High-contrast homogenization: Entry.Multiscale.OneGrid.StartupMoments

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Step 5 — the diagonal profile and the initial moments

Group H of the printed proof (`p.fixed.geometry.one.grid.propagation`), first part: `𝒫_q(n;n) =
ℋ_q(n)`,
the diagonal moment comparison, and the new fluctuation terms of the initial advance.

Part of the proof of the statement in
`HCPoly/Entry/Statements/OneGridPropagation.lean`.  Conventions of the group:
`q = 𝒬(𝔪)` is `Geometry.explicitRoundedGrid jStar metric` at every loss, history, profile and drift;
`metric` (not `m`) names the positive matrix, because `m`, `n`, `m₀` are generations; the
source lower scale `e.source.lower.scale` is carried exactly by the
source-facing `HCPoly/Entry/OneGridPropagation.lean`; this group's stronger internal
algebraic and history lemmas omit an unused threshold, and this group's generic
integration helpers take finiteness, integrability or measurability inputs that are proved
at their actual use sites, not extra premises of the printed proposition.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter adaptedMean
  toFullBlockMat_eq_blockMatEntry)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-! ## Group H. Step 5 — the initial advance and the drift assembly
(`p.fixed.geometry.one.grid.propagation`) -/

/-- `𝒫_q(n;n) = ℋ_q(n)` at the actual geometry (near `e.scale.selection.complete.profile`): the
diagonal
identity `Multiscale.profile_self_of_posDef` with its positive-definiteness discharged. -/
theorem profile_diagonal_eq_history (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (_hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (S : CoeffSpace d → ℝ),
      IsProbabilityMeasure P →
      IsStationaryLaw P →
      IsUnitRangeLaw P →
      CoarseEllipticityDagger P γ E Ψ K S →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
        ∀ (metric : Mat d), metric.PosDef →
          ∀ n : ℤ,
            profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n n =
              history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n := by
  intro P E Ψ K S hP hstat _ hdag jStar hjStar metric hmetric n
  have : IsProbabilityMeasure P := hP
  rw [profile_self_eq_factor_mul_history]
  have hF :
      Matrix.PosDef
        (toFullBlockMat
          (adaptedMean P (Geometry.explicitRoundedGrid jStar metric) n)) :=
    Annealed.adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric n
  simp [relMean,
    normalizedBlock_self_of_posDef (adaptedMean P (Geometry.explicitRoundedGrid jStar metric) n) hF,
    meanPenalty_identity]

/-- `E[|V^q_n|_{S_Q}^Q] ≤ 2d·ℋ^fluc_q(n)` (`p.fixed.geometry.one.grid.propagation`): comparison of
the Schatten and
operator norms at the diagonal generation, where the printed supremum of the fluctuation
history is taken at `j = n` and the lattice point `0`. -/
theorem moment_diagonal_le_fluctuationHistory (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (S : CoeffSpace d → ℝ),
      IsProbabilityMeasure P →
      IsStationaryLaw P →
      IsUnitRangeLaw P →
      CoarseEllipticityDagger P γ E Ψ K S →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
        ∀ (metric : Mat d), metric.PosDef →
          ∀ n : ℤ, (jStar : ℤ) ≤ n →
            (∫ a, absSchattenNorm (bigQ d γ : ℝ)
                (normalizedFluctuationSelf P
                  (Geometry.explicitRoundedGrid jStar metric) n a) ^ bigQ d γ ∂P) ≤
              2 * (d : ℝ) *
                fluctuationHistory P γ (Geometry.explicitRoundedGrid jStar metric) jStar n := by
  classical
  intro P E Ψ K S hP hstat _hunit hdag jStar hjStar metric hmetric n hn
  let := hP
  open scoped Matrix.Norms.L2Operator in
  set q := Geometry.explicitRoundedGrid jStar metric
  have hQ : 1 ≤ bigQ d γ := le_trans (by norm_num) (bigQ_two_le d γ hγ)
  have hQR : (1 : ℝ) ≤ (bigQ d γ : ℝ) := by exact_mod_cast hQ
  have hfiniteSup {ι : Type} (s : Set ι) (hs : s.Finite)
      (f : ι → CoeffSpace d → ℝ) (hf : ∀ i a, 0 ≤ f i a)
      (hint : ∀ i ∈ s, Integrable (f i) P) :
      Integrable (fun a => ⨆ i ∈ s, f i a) P ∧
      ∀ a i, i ∈ s → f i a ≤ ⨆ k ∈ s, f k a := by
    have hsum (a : CoeffSpace d) : 0 ≤ ∑ i ∈ hs.toFinset, f i a :=
      Finset.sum_nonneg fun i _ => hf i a
    have hbound (a : CoeffSpace d) (i : ι) :
        (⨆ _hi : i ∈ s, f i a) ≤ ∑ k ∈ hs.toFinset, f k a := by
      refine Real.iSup_le (fun hi => ?_) (hsum a)
      exact Finset.single_le_sum (fun k _ => hf k a) (hs.mem_toFinset.mpr hi)
    have hbdd (a : CoeffSpace d) : BddAbove (Set.range (fun i => ⨆ _hi : i ∈ s, f i a)) := by
      refine ⟨∑ k ∈ hs.toFinset, f k a, ?_⟩
      rintro _ ⟨i, rfl⟩
      exact hbound a i
    have hm : AEStronglyMeasurable (fun a => ⨆ i ∈ s, f i a) P :=
      (AEMeasurable.biSup s hs.countable (fun i hi => (hint i hi).aemeasurable)).aestronglyMeasurable
    refine ⟨?_, ?_⟩
    · apply (integrable_finsetSum hs.toFinset (fun i hi => hint i (hs.mem_toFinset.mp hi))).mono' hm
      filter_upwards [] with a
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.iSup_nonneg (fun i => Real.iSup_nonneg (fun _ => hf i a)))]
      exact Real.iSup_le (hbound a) (hsum a)
    · intro a i hi
      have h := le_ciSup (hbdd a) i
      simpa only [ciSup_pos hi] using h
  have hq : IsUnit q := Geometry.isUnit_roundedGrid hjStar hmetric
  have hqinj : Function.Injective (matVecMul q) := Matrix.mulVec_injective_iff_isUnit.mpr hq
  have hfin (j : ℤ) (hj : j ≤ n) :
      (adaptedLatticeAtScale q j ∩ HighContrast.adaptedCell q n).Finite := by
    have heq : j + ((n - j).toNat : ℤ) = n := by omega
    have hs := (Annealed.alignedCenterSet_finite_card d j (n - j).toNat).1
    rw [heq] at hs
    have hset : adaptedLatticeAtScale q j ∩ HighContrast.adaptedCell q n =
        adaptedCellCenter q j '' {w : Fin d → ℤ | HighContrast.standardCellCenter j w ∈ HighContrast.centeredCube d n} := by
      ext z
      constructor
      · rintro ⟨⟨w, rfl⟩, hw⟩
        refine ⟨w, ?_, rfl⟩
        rw [Recurrence.adaptedCellCenter_eq] at hw
        obtain ⟨x, hx, he⟩ := hw
        have he' := hqinj he
        change HighContrast.standardCellCenter j w ∈ HighContrast.centeredCube d n
        exact he' ▸ hx
      · rintro ⟨w, hw, rfl⟩
        refine ⟨⟨w, rfl⟩, ?_⟩
        rw [Recurrence.adaptedCellCenter_eq]
        exact ⟨_, hw, rfl⟩
    rw [hset]
    exact hs.image _
  have hzero : (0 : Vec d) ∈ adaptedLatticeAtScale q n ∩ HighContrast.adaptedCell q n := by
    constructor
    · refine ⟨0, ?_⟩
      simp only [adaptedCellCenter, Pi.zero_apply, Int.cast_zero]
      change (3 : ℝ) ^ n • (Matrix.mulVec q (0 : Vec d)) = 0
      rw [Matrix.mulVec_zero, smul_zero]
    · refine ⟨(0 : Vec d), ?_, ?_⟩
      · rw [Recurrence.mem_centeredCube_iff]
        intro i
        simp only [Pi.zero_apply]
        have hpos : 0 < (3 : ℝ) ^ n / 2 := by positivity
        constructor <;> linarith only [hpos]
      · exact Matrix.mulVec_zero q
  have hmem (j : ℤ) (z : Vec d) := Annealed.memLqSchatten_normalizedFluctuation d hd P γ E Ψ K S
    hstat hdag jStar hjStar metric hmetric j n z (bigQ d γ : ℝ) hQR
  have hopint (j : ℤ) (z : Vec d) : Integrable (fun a =>
      blockOpNorm (normalizedFluctuation P q j n z a) ^ bigQ d γ) P := by
    have hm : AEMeasurable (fun a => toFullBlockMat (normalizedFluctuation P q j n z a)) P :=
      AEMeasurable.of_eval fun α => AEMeasurable.of_eval fun β => by
        simpa only [toFullBlockMat_eq_blockMatEntry] using ((hmem j z).measurable α β).aemeasurable
    have hmoment : Integrable (fun a => absSchattenNorm (bigQ d γ : ℝ)
        (normalizedFluctuation P q j n z a) ^ bigQ d γ) P := by
      simpa only [Real.rpow_natCast] using (hmem j z).integrable
    apply hmoment.mono' ((hm.norm.pow_const (bigQ d γ)).aestronglyMeasurable)
    filter_upwards [(hmem j z).symmetric] with a ha
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (Analysis.blockOpNorm_le_absSchattenNorm ((Analysis.toFullBlockMat_isHermitian_iff _).mpr ha) hQR) _
  let f : ℤ → CoeffSpace d → ℝ := fun j a =>
    (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((n : ℝ) - (j : ℝ))) *
      ⨆ z ∈ adaptedLatticeAtScale q j ∩ HighContrast.adaptedCell q n,
        blockOpNorm (normalizedFluctuation P q j n z a) ^ bigQ d γ
  have hinner (j : ℤ) (hj : j ≤ n) := hfiniteSup
    (adaptedLatticeAtScale q j ∩ HighContrast.adaptedCell q n) (hfin j hj)
    (fun z a => blockOpNorm (normalizedFluctuation P q j n z a) ^ bigQ d γ)
    (fun _ _ => pow_nonneg (norm_nonneg _) _) (fun z _ => hopint j z)
  have hf (j : ℤ) (a : CoeffSpace d) : 0 ≤ f j a := mul_nonneg
    (Real.rpow_nonneg (by norm_num) _) (Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => pow_nonneg (norm_nonneg _) _)
  have houter := hfiniteSup (Set.Icc (jStar : ℤ) n) (Set.finite_Icc _ _) f hf
    (fun j hj => (hinner j hj.2).1.const_mul _)
  have hpoint (a : CoeffSpace d) :
      blockOpNorm (normalizedFluctuationSelf P q n a) ^ bigQ d γ ≤
        ⨆ j ∈ Set.Icc (jStar : ℤ) n, f j a := by
    have h₁ := (hinner n le_rfl).2 a 0 hzero
    have h₂ := houter.2 a n ⟨hn, le_rfl⟩
    simp only [f, sub_self, mul_zero, Real.rpow_zero, one_mul] at h₂
    exact h₁.trans h₂
  have hspectral (M : BlockMat d) (hM : (toFullBlockMat M).IsHermitian) :
      absSchattenNorm (bigQ d γ : ℝ) M ^ bigQ d γ ≤
        2 * (d : ℝ) * blockOpNorm M ^ bigQ d γ := by
    have hconj (U : unitary (FullBlockMat d)) (A : FullBlockMat d) :
        ‖Unitary.conjStarAlgAut ℝ _ U A‖ = ‖A‖ := by
      rw [Unitary.conjStarAlgAut_apply]
      rw [CStarRing.norm_mul_mem_unitary (A := (U : FullBlockMat d) * A)
        (hU := Unitary.star_mem U.prop)]
      exact CStarRing.norm_mem_unitary_mul A U.prop
    have hnorm : ‖toFullBlockMat M‖ = ‖hM.eigenvalues‖ := by
      conv_lhs => rw [hM.spectral_theorem]
      rw [hconj]
      simp
    have hspec := Analysis.absSchattenNorm_rpow_eq_sum hM hQR
    simp only [Real.rpow_natCast] at hspec
    rw [hspec]
    calc
      _ ≤ ∑ _i : BlockCoord d, blockOpNorm M ^ bigQ d γ := by
        apply Finset.sum_le_sum
        intro i _
        apply pow_le_pow_left₀ (abs_nonneg _)
        change |hM.eigenvalues i| ≤ ‖toFullBlockMat M‖
        rw [hnorm]
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm hM.eigenvalues i
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, BlockCoord, Fintype.card_sum,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_add]
        ring
  have hmoment : Integrable (fun a => absSchattenNorm (bigQ d γ : ℝ)
      (normalizedFluctuationSelf P q n a) ^ bigQ d γ) P := by
    simpa only [Real.rpow_natCast] using! (hmem n 0).integrable
  change _ ≤ 2 * (d : ℝ) * ∫ a, ⨆ j ∈ Set.Icc (jStar : ℤ) n, f j a ∂P
  rw [← integral_const_mul]
  apply integral_mono_ae hmoment (houter.1.const_mul (2 * (d : ℝ)))
  filter_upwards [(hmem n 0).symmetric] with a ha
  exact (hspectral _ ((Analysis.toFullBlockMat_isHermitian_iff _).mpr ha)).trans
    (mul_le_mul_of_nonneg_left (hpoint a) (by positivity))

private theorem moment_weight_comparison (d A B H x decay recurrenceExp laterExp seed current weight : ℝ)
    (hd : 0 ≤ d) (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H) (hx : 0 ≤ x)
    (hHone : H ≤ 1) (hdecay_le : decay ≤ 1)
    (hexp : 0 ≤ recurrenceExp) (hlater : 1 ≤ laterExp)
    (hseed : 0 ≤ seed) (hcurrent : 0 ≤ current) (hseed_bound : seed ≤ 2 * d * H)
    (hrecurrence : current ≤ A * decay * recurrenceExp * seed +
      B * (recurrenceExp - 1))
    (hexp_mul : recurrenceExp * laterExp = Real.exp x) (hweight_le : weight ≤ 1) :
    weight * laterExp * current ≤ (2 * d * A + B) * (H + Real.exp x - 1) := by
  have hlater_nonneg : 0 ≤ laterExp := by linarith
  have hrecurrence_mul := mul_le_mul_of_nonneg_left hrecurrence hlater_nonneg
  have hdecay_drop :
      A * decay * recurrenceExp * seed * laterExp ≤ A * recurrenceExp * seed * laterExp := by
    have hcoeff : 0 ≤ A * recurrenceExp * seed * laterExp := by positivity
    calc
      A * decay * recurrenceExp * seed * laterExp =
          (A * recurrenceExp * seed * laterExp) * decay := by ring
      _ ≤ (A * recurrenceExp * seed * laterExp) * 1 :=
          mul_le_mul_of_nonneg_left hdecay_le hcoeff
      _ = A * recurrenceExp * seed * laterExp := by ring
  have hrecurrence_simplified : laterExp * current ≤
      A * Real.exp x * seed + B * (Real.exp x - laterExp) := by
    calc
      laterExp * current ≤
          A * decay * recurrenceExp * seed * laterExp +
            B * (recurrenceExp - 1) * laterExp := by
              simpa [mul_add, mul_assoc, mul_left_comm, mul_comm] using hrecurrence_mul
      _ ≤ A * recurrenceExp * seed * laterExp +
            B * (recurrenceExp - 1) * laterExp :=
              add_le_add hdecay_drop le_rfl
      _ = A * Real.exp x * seed + B * (Real.exp x - laterExp) := by
        calc
          _ = A * (recurrenceExp * laterExp) * seed +
                B * (recurrenceExp * laterExp - laterExp) := by ring
          _ = _ := by rw [hexp_mul]
  have hBterm : B * (Real.exp x - laterExp) ≤ B * (Real.exp x - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hB
  have hseed_term : A * Real.exp x * seed ≤ A * Real.exp x * (2 * d * H) :=
    mul_le_mul_of_nonneg_left hseed_bound (by positivity)
  have hexpH : Real.exp x * H ≤ H + Real.exp x - 1 :=
    exp_mul_le_add_exp_sub_one x H hx hH hHone
  have hmain : 2 * d * A * (Real.exp x * H) ≤
      2 * d * A * (H + Real.exp x - 1) :=
    mul_le_mul_of_nonneg_left hexpH (by positivity)
  have hbase : laterExp * current ≤
      (2 * d * A + B) * (H + Real.exp x - 1) := by
    calc
      laterExp * current ≤ A * Real.exp x * seed + B * (Real.exp x - laterExp) :=
        hrecurrence_simplified
      _ ≤ A * Real.exp x * (2 * d * H) + B * (Real.exp x - 1) :=
        add_le_add hseed_term hBterm
      _ = 2 * d * A * (Real.exp x * H) + B * (Real.exp x - 1) := by ring
      _ ≤ 2 * d * A * (H + Real.exp x - 1) + B * (H + Real.exp x - 1) :=
        add_le_add hmain (mul_le_mul_of_nonneg_left (by linarith) hB)
      _ = (2 * d * A + B) * (H + Real.exp x - 1) := by ring
  calc
    weight * laterExp * current = weight * (laterExp * current) := by ring
    _ ≤ 1 * (laterExp * current) := mul_le_mul_of_nonneg_right hweight_le
      (mul_nonneg hlater_nonneg hcurrent)
    _ = laterExp * current := by ring
    _ ≤ (2 * d * A + B) * (H + Real.exp x - 1) := hbase

/-- The new fluctuation terms of the initial advance (`p.fixed.geometry.one.grid.propagation`):
apply the powered
recurrence with span `r` at the base generation `n`, seed with
`E[|V^q_n|_{S_Q}^Q] ≤ 2d ℋ_q(n)`, use `e^x a ≤ a + e^x - 1` at `a = ℋ_q(n) ≤ 1`, and sum.  The
constant is uniform in `1 ≤ r ≤ L`. -/
theorem startup_fluctuation_sum_le (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
          (S : CoeffSpace d → ℝ),
          IsProbabilityMeasure P →
          IsStationaryLaw P →
          IsUnitRangeLaw P →
          CoarseEllipticityDagger P γ E Ψ K S →
          ∀ L : ℤ, 1 ≤ L →
            ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
              ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
                ∀ (metric : Mat d), metric.PosDef →
                  ∀ n : ℤ, (jStar : ℤ) ≤ n →
                    history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n ≤ 1 →
                      ∑ j ∈ Finset.Icc (n + 1) (n + L),
                          (3 : ℝ) ^ (-((1 - γ) / 4) * (((n + L : ℤ) : ℝ) - (j : ℝ))) *
                              Real.exp ((bigQ d γ : ℝ) *
                                detIncrement P (Geometry.explicitRoundedGrid jStar metric) j (n + L)) *
                            ∫ a, absSchattenNorm (bigQ d γ : ℝ)
                                (normalizedFluctuationSelf P
                                  (Geometry.explicitRoundedGrid jStar metric) j a) ^ bigQ d γ ∂P ≤
                        C * (L : ℝ) *
                          (history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n +
                            Real.exp ((bigQ d γ : ℝ) *
                              detIncrement P (Geometry.explicitRoundedGrid jStar metric)
                                n (n + L)) - 1) := by
  obtain ⟨Csrc, hCsrc, hpow⟩ := parent_child_powered d hd γ hγ
  set A : ℝ := (2 : ℝ) ^ (bigQ d γ - 1) * ((3 : ℝ) ^ d * (bigQ d γ : ℝ)) ^ bigQ d γ with hAdef
  set B : ℝ := (2 : ℝ) ^ (2 * bigQ d γ - 1) *
      (1 + (d : ℝ) ^ (1 - ((bigQ d γ : ℝ))⁻¹)) ^ bigQ d γ with hBdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hC0 : 0 < 2 * (d : ℝ) * A + B := by rw [hAdef, hBdef]; positivity
  refine ⟨Csrc, hCsrc, 2 * (d : ℝ) * A + B, hC0, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag L hL jStar hjStar hjStarLB metric hmetric n hn hH1
  let := hP
  set q := Geometry.explicitRoundedGrid jStar metric with hqdef
  set H := history P γ q jStar n with hHdef
  set x := (bigQ d γ : ℝ) * detIncrement P q n (n + L) with hxdef
  have hnL : n ≤ n + L := by omega
  have hnnL : (jStar : ℤ) ≤ n + L := by omega
  have hx0 : 0 ≤ x := by
    rw [hxdef]
    exact mul_nonneg (Nat.cast_nonneg _)
      (Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric
        n (n + L) hn hnL)
  have hH0 : 0 ≤ H := by
    rw [hHdef]
    have hmean0 := meanHistory_nonneg d hd γ hγ P E Ψ K S hP hstat hunit hdag
      jStar hjStar metric hmetric (jStar : ℤ) n le_rfl hn
    have hfluc : 0 ≤ fluctuationHistory P γ q jStar n := by
      apply integral_nonneg
      intro a
      apply Real.iSup_nonneg
      intro j
      apply Real.iSup_nonneg
      intro _hj
      apply mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      apply Real.iSup_nonneg
      intro z
      apply Real.iSup_nonneg
      intro _hz
      exact (bigQ_even d γ).pow_nonneg _
    unfold history
    linarith only [hmean0, hfluc]
  have hmom (j : ℤ) : 0 ≤ ∫ a, absSchattenNorm (bigQ d γ : ℝ)
      (normalizedFluctuationSelf P q j a) ^ bigQ d γ ∂P :=
    integral_nonneg fun _ => (bigQ_even d γ).pow_nonneg _
  have hseed : (∫ a, absSchattenNorm (bigQ d γ : ℝ)
      (normalizedFluctuationSelf P q n a) ^ bigQ d γ ∂P) ≤ 2 * (d : ℝ) * H := by
    have hmm := moment_diagonal_le_fluctuationHistory d hd γ hγ P E Ψ K S hP hstat hunit hdag
      jStar hjStar metric hmetric n hn
    have hfluc_le : fluctuationHistory P γ q jStar n ≤ H := by
      rw [hHdef]
      have hmean0 := meanHistory_nonneg d hd γ hγ P E Ψ K S hP hstat hunit hdag
        jStar hjStar metric hmetric (jStar : ℤ) n le_rfl hn
      unfold history
      linarith only [hmean0]
    calc (∫ a, absSchattenNorm (bigQ d γ : ℝ)
          (normalizedFluctuationSelf P q n a) ^ bigQ d γ ∂P)
        ≤ 2 * (d : ℝ) * fluctuationHistory P γ q jStar n := hmm
      _ ≤ 2 * (d : ℝ) * H := by
          apply mul_le_mul_of_nonneg_left hfluc_le
          positivity
  have hterm : ∀ j ∈ Finset.Icc (n + 1) (n + L),
      (3 : ℝ) ^ (-((1 - γ) / 4) * (((n + L : ℤ) : ℝ) - (j : ℝ))) *
          Real.exp ((bigQ d γ : ℝ) * detIncrement P q j (n + L)) *
        (∫ a, absSchattenNorm (bigQ d γ : ℝ)
            (normalizedFluctuationSelf P q j a) ^ bigQ d γ ∂P) ≤
      (2 * (d : ℝ) * A + B) * (H + Real.exp x - 1) := by
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    set r : ℤ := j - n with hrdef
    have hr1 : 1 ≤ r := by omega
    have hjn : n + r = j := by omega
    have hpj : (jStar : ℤ) ≤ j := by omega
    have hjnL : j ≤ n + L := hj'.2
    have hstep := hpow P E Ψ K S hP hstat hunit hdag jStar hjStar hjStarLB metric hmetric
      n r hn hr1
    rw [hjn] at hstep
    have hdrop : (3 : ℝ) ^ (-((bigQ d γ : ℝ) * (d : ℝ) / 2) * (r : ℝ)) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      have h1 : -((bigQ d γ : ℝ) * (d : ℝ) / 2) ≤ 0 := neg_nonpos.mpr (by positivity)
      have h2 : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ r)
      exact mul_nonpos_of_nonpos_of_nonneg h1 h2
    set e2 : ℝ := Real.exp ((bigQ d γ : ℝ) * detIncrement P q j (n + L)) with he2def
    have he2_1 : 1 ≤ e2 := by
      rw [he2def]
      apply Real.one_le_exp
      apply mul_nonneg (Nat.cast_nonneg _)
      exact Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric
        j (n + L) hpj hjnL
    have hadd : detIncrement P q n j + detIncrement P q j (n + L) = detIncrement P q n (n + L) :=
      logDetLoss_add P q n j (n + L)
    have hexp_mul : Real.exp ((bigQ d γ : ℝ) * detIncrement P q n j) * e2 = Real.exp x := by
      rw [he2def, hxdef, ← Real.exp_add]
      congr 1
      rw [← mul_add, hadd]
    have hrecurrenceExp_nonneg :
        0 ≤ Real.exp ((bigQ d γ : ℝ) * detIncrement P q n j) := Real.exp_nonneg _
    have hw : (3 : ℝ) ^ (-((1 - γ) / 4) * (((n + L : ℤ) : ℝ) - (j : ℝ))) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      have h1 : -((1 - γ) / 4) ≤ 0 := by linarith only [hγ.2]
      have h2 : (0 : ℝ) ≤ ((n + L : ℤ) : ℝ) - (j : ℝ) := by
        have : (j : ℝ) ≤ ((n + L : ℤ) : ℝ) := by exact_mod_cast hj'.2
        linarith only [this]
      exact mul_nonpos_of_nonpos_of_nonneg h1 h2
    simpa only [he2def] using moment_weight_comparison (d : ℝ) A B H x
      (3 : ℝ) ^ (-((bigQ d γ : ℝ) * (d : ℝ) / 2) * (r : ℝ))
      (Real.exp ((bigQ d γ : ℝ) * detIncrement P q n j)) e2
      (∫ a, absSchattenNorm (bigQ d γ : ℝ)
        (normalizedFluctuationSelf P q n a) ^ bigQ d γ ∂P)
      (∫ a, absSchattenNorm (bigQ d γ : ℝ)
        (normalizedFluctuationSelf P q j a) ^ bigQ d γ ∂P)
      ((3 : ℝ) ^ (-((1 - γ) / 4) * (((n + L : ℤ) : ℝ) - (j : ℝ))))
      (by positivity) hA0 hB0 hH0 hx0 hH1
      hdrop hrecurrenceExp_nonneg he2_1
      (hmom n) (hmom j) hseed hstep hexp_mul hw
  have hsum := Finset.sum_le_card_nsmul (Finset.Icc (n + 1) (n + L))
    (fun j => (3 : ℝ) ^ (-((1 - γ) / 4) * (((n + L : ℤ) : ℝ) - (j : ℝ))) *
        Real.exp ((bigQ d γ : ℝ) * detIncrement P q j (n + L)) *
      (∫ a, absSchattenNorm (bigQ d γ : ℝ)
          (normalizedFluctuationSelf P q j a) ^ bigQ d γ ∂P))
    ((2 * (d : ℝ) * A + B) * (H + Real.exp x - 1)) hterm
  have hcard : (Finset.Icc (n + 1) (n + L)).card = L.toNat := by
    rw [Int.card_Icc]
    congr 1
    omega
  rw [hcard, nsmul_eq_mul] at hsum
  have hLcast : ((L.toNat : ℕ) : ℝ) = (L : ℝ) := by
    have h : ((L.toNat : ℤ)) = L := Int.toNat_of_nonneg (by omega)
    exact_mod_cast h
  rw [hLcast] at hsum
  calc (∑ j ∈ Finset.Icc (n + 1) (n + L),
        (3 : ℝ) ^ (-((1 - γ) / 4) * (((n + L : ℤ) : ℝ) - (j : ℝ))) *
            Real.exp ((bigQ d γ : ℝ) * detIncrement P q j (n + L)) *
          (∫ a, absSchattenNorm (bigQ d γ : ℝ)
              (normalizedFluctuationSelf P q j a) ^ bigQ d γ ∂P))
      ≤ (L : ℝ) * ((2 * (d : ℝ) * A + B) * (H + Real.exp x - 1)) := hsum
    _ = (2 * (d : ℝ) * A + B) * (L : ℝ) * (H + Real.exp x - 1) := by ring

end

end HCPolySupport.HighContrast.Multiscale
