/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.OneGrid.HistoryCounting

/-!
# High-contrast homogenization: Entry.Multiscale.OneGrid.HistoryMajorization

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Step 1 — the histories are majorized by the profile

Group D of the printed proof (`p.fixed.geometry.one.grid.propagation`), second half: the fluctuation
decomposition, the mean-history estimates, and **conjuncts 1 and 5**,
`e.fixed.geometry.profile.majorization` and `e.fixed.geometry.carried.majorization`.

Part of the proof of the statement in
`HCPoly/Entry/Statements/OneGridPropagation.lean`.  Group conventions:
`q = 𝒬(𝔪)` is `Geometry.explicitRoundedGrid jStar metric` at every loss, history, profile and drift;
`metric` (not `m`) names the positive matrix, because `m`, `n`, `m₀` are generations; the
source lower scale `e.source.lower.scale` is carried exactly by the statement in
`HCPoly/Entry/OneGridPropagation.lean`; this group's stronger
algebraic and history lemmas omit an unused threshold, and this group's generic
integration helpers take finiteness, integrability or measurability inputs that are proved
at their actual use sites, not extra premises of the printed proposition.

-/

open HCPolySupport.HighContrast (CoeffSpace measurable_translateCoeff translateCoeff)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The printed fluctuation estimate of Step 1 (`p.fixed.geometry.one.grid.propagation`): change
of normalization for
the generations up to `n`, and a cell-wise bound for the remaining generations, using
`Qρ_max - d ≥ ¼(1-γ)`.  The right-hand side is the fluctuation part of `𝒫_q(m;n)`. -/
theorem fluctuationHistory_decompose (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (S : CoeffSpace d → ℝ),
      IsProbabilityMeasure P →
      IsStationaryLaw P →
      IsUnitRangeLaw P →
      CoarseEllipticityDagger P γ E Ψ K S →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
        ∀ (metric : Mat d), metric.PosDef →
          ∀ n m : ℤ, (jStar : ℤ) ≤ n → n ≤ m →
            fluctuationHistory P γ (Geometry.explicitRoundedGrid jStar metric) jStar m ≤
              (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (n : ℝ))) *
                  (1 + meanPenalty (bigQ d γ)
                    (relMean P (Geometry.explicitRoundedGrid jStar metric) n m)) *
                  fluctuationHistory P γ (Geometry.explicitRoundedGrid jStar metric) jStar n +
                ∑ j ∈ Finset.Icc (n + 1) m,
                  (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (j : ℝ))) *
                      Real.exp ((bigQ d γ : ℝ) *
                        detIncrement P (Geometry.explicitRoundedGrid jStar metric) j m) *
                    ∫ a, absSchattenNorm (bigQ d γ : ℝ)
                        (normalizedFluctuationSelf P
                          (Geometry.explicitRoundedGrid jStar metric) j a) ^ bigQ d γ ∂P := by
  classical
  intro P E Ψ K S hP hstat _hunit hdag jStar hjStar metric hmetric n m hn hnm
  let := hP
  open scoped Matrix.Norms.L2Operator in
  let q := Geometry.explicitRoundedGrid jStar metric
  let Q := bigQ d γ
  let Z (j k : ℤ) := adaptedLatticeAtScale q j ∩ HighContrast.adaptedCell q k
  let w (j k : ℤ) := (3 : ℝ) ^ (-(Q : ℝ) * rhoMax d γ * ((k : ℝ) - (j : ℝ)))
  let v (j k : ℤ) (z : Vec d) (a : CoeffSpace d) :=
    blockOpNorm (normalizedFluctuation P q j k z a) ^ Q
  let H (k : ℤ) (a : CoeffSpace d) :=
    ⨆ j ∈ Set.Icc (jStar : ℤ) k, w j k * ⨆ z ∈ Z j k, v j k z a
  let M (j : ℤ) := ∫ a, absSchattenNorm (Q : ℝ) (normalizedFluctuationSelf P q j a) ^ Q ∂P
  let B := 1 + meanPenalty Q (relMean P q n m)
  have hQ : (1 : ℝ) ≤ (Q : ℝ) := by
    exact_mod_cast (show 1 ≤ Q from le_trans (by norm_num) (bigQ_two_le d γ hγ))
  have hq : IsUnit q := Geometry.isUnit_roundedGrid hjStar hmetric
  have hw (j k : ℤ) : 0 < w j k := Real.rpow_pos_of_pos (by norm_num) _
  have hv (j k : ℤ) (z : Vec d) (a : CoeffSpace d) : 0 ≤ v j k z a :=
    pow_nonneg (norm_nonneg _) _
  have hH (k : ℤ) (a : CoeffSpace d) : 0 ≤ H k a :=
    Real.iSup_nonneg fun j => Real.iSup_nonneg fun _ =>
      mul_nonneg (hw j k).le (Real.iSup_nonneg fun z => Real.iSup_nonneg fun _ => hv j k z a)
  have hmem (j k : ℤ) (z : Vec d) := Annealed.memLqSchatten_normalizedFluctuation
    d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric j k z (Q : ℝ) hQ
  have hint (j k : ℤ) (z : Vec d) : Integrable (v j k z) P :=
    oneGrid_integrable_opNorm_pow P Q hQ _ (hmem j k z)
  have hfin (j k : ℤ) (hjk : j ≤ k) : (Z j k).Finite :=
    (oneGrid_centers_finite_card q hq j k hjk).1
  have houter (k : ℤ) := oneGrid_fluctuation_integrable_dominate d hd γ P E Ψ K S
    hstat hdag jStar hjStar metric hmetric k
  have hB : 0 ≤ B := by
    have hp := (Annealed.adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag
      jStar hjStar metric hmetric n m hn hnm).2.2.2.2.2
    dsimp only [B, Q, q]
    linarith only [hp]
  have hshift (j : ℤ) (hj : (jStar : ℤ) ≤ j) (z : Vec d)
      (hz : z ∈ adaptedLatticeAtScale q j) : ∃ t : Fin d → ℤ, z = Source.AKL.intTranslation t := by
    obtain ⟨u, rfl⟩ := hz
    exact Annealed.adaptedCellCenter_eq_intTranslation jStar metric hj u
  have hsh : ∀ y : Vec d, ∃ t : Fin d → ℤ, y ∈ Z n m → y = Source.AKL.intTranslation t := by
    intro y
    by_cases hy : y ∈ Z n m
    · obtain ⟨t, ht⟩ := hshift n hn y hy.1
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h => False.elim (hy h)⟩
  choose τ hτ using hsh
  let C := (hfin n m hnm).toFinset
  let L (a : CoeffSpace d) := w n m * B * ∑ y ∈ C, H n (translateCoeff (τ y) a)
  let U (j : ℤ) (a : CoeffSpace d) :=
    w j m * ∑ z ∈ (if h : j ≤ m then (hfin j m h).toFinset else ∅), v j m z a
  have hL (a : CoeffSpace d) : 0 ≤ L a :=
    mul_nonneg (mul_nonneg (hw n m).le hB) (Finset.sum_nonneg fun y _ => hH n _)
  have hHshift (y : Vec d) : Integrable (fun a => H n (translateCoeff (τ y) a)) P :=
    (show MeasurePreserving (translateCoeff (τ y)) P P from
      ⟨measurable_translateCoeff _, hstat _⟩).integrable_comp_of_integrable (houter n).1
  have hLint : Integrable L P :=
    (integrable_finsetSum C (fun y _ => hHshift y)).const_mul _
  have hlower (a : CoeffSpace d) (j : ℤ) (hj : (jStar : ℤ) ≤ j) (hjn : j ≤ n)
      (z : Vec d) (hz : z ∈ Z j m) : w j m * v j m z a ≤ L a :=
    oneGrid_lower_pointwise d hd γ hγ P E Ψ K S hstat hdag jStar hjStar metric hmetric
      n m hn hnm C (hfin n m hnm).coe_toFinset τ hτ a j hj hjn z hz
  have hupperMoment (j : ℤ) (hj : (jStar : ℤ) ≤ j) (hjm : j ≤ m)
      (z : Vec d) (hz : z ∈ Z j m) :
      (∫ a, v j m z a ∂P) ≤ Real.exp ((Q : ℝ) * detIncrement P q j m) * M j :=
    oneGrid_lattice_moment_le d hd γ hγ P E Ψ K S hstat hdag
      jStar hjStar metric hmetric j m hj hjm z hz.1
  have htotal : (∫ a, H m a ∂P) ≤ (∫ a, L a ∂P) +
      ∑ j ∈ Finset.Icc (n + 1) m, ∫ a, U j a ∂P := by
    apply oneGrid_integral_sup_split P (jStar : ℤ) n m (fun j => w j m) (fun j => hw j m)
      (fun j => Z j m) (fun j => if h : j ≤ m then (hfin j m h).toFinset else ∅)
      (fun j => v j m) (fun j => hv j m) ?_ ?_ L hL hLint (houter m).1 hlower
    · intro j hj z hz
      rw [dite_eq_left (Finset.mem_Icc.mp hj).2]
      exact (hfin j m (Finset.mem_Icc.mp hj).2).mem_toFinset.mpr hz
    · intro j _ z _
      exact hint j m z
  have hcard (j : ℤ) (hjm : j ≤ m) : (hfin j m hjm).toFinset.card =
      3 ^ (d * (m - j).toNat) := by
    rw [← Set.ncard_eq_toFinset_card (Z j m) (hfin j m hjm)]
    exact (oneGrid_centers_finite_card q hq j m hjm).2
  have hcount (j : ℤ) (hjm : j ≤ m) :
      w j m * ((hfin j m hjm).toFinset.card : ℝ) ≤
        (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (j : ℝ))) := by
    rw [hcard j hjm]
    exact oneGrid_count_absorption d hd γ hγ j m hjm
  have hLbound : (∫ a, L a ∂P) ≤
      (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (n : ℝ))) * B *
        fluctuationHistory P γ q jStar n := by
    have hli : (∫ a, L a ∂P) =
        (w n m * (C.card : ℝ)) * (B * fluctuationHistory P γ q jStar n) := by
      dsimp only [L]
      rw [integral_const_mul, integral_finsetSum C (fun y _ => hHshift y)]
      simp_rw [oneGrid_integral_translate P hstat (H n) (houter n).1.aestronglyMeasurable]
      rw [Finset.sum_const, nsmul_eq_mul]
      change w n m * B * ((C.card : ℝ) * fluctuationHistory P γ q jStar n) = _
      ring
    rw [hli]
    have hfluc : 0 ≤ fluctuationHistory P γ q jStar n := integral_nonneg (hH n)
    calc
      _ ≤ _ * (B * fluctuationHistory P γ q jStar n) :=
        mul_le_mul_of_nonneg_right (hcount n hnm) (mul_nonneg hB hfluc)
      _ = _ := by ring
  have hUbound (j : ℤ) (hj : j ∈ Finset.Icc (n + 1) m) :
      (∫ a, U j a ∂P) ≤
        (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (j : ℝ))) *
          Real.exp ((Q : ℝ) * detIncrement P q j m) * M j := by
    have hjm := (Finset.mem_Icc.mp hj).2
    have hj' : (jStar : ℤ) ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
    have hM : 0 ≤ M j := integral_nonneg fun _ => (bigQ_even d γ).pow_nonneg _
    have hs : (∫ a, U j a ∂P) ≤
        (w j m * ((hfin j m hjm).toFinset.card : ℝ)) *
          (Real.exp ((Q : ℝ) * detIncrement P q j m) * M j) := by
      dsimp only [U]
      rw [dite_eq_left hjm, integral_const_mul, integral_finsetSum _ (fun z _ => hint j m z)]
      calc
        _ ≤ w j m * ∑ _z ∈ (hfin j m hjm).toFinset,
            (Real.exp ((Q : ℝ) * detIncrement P q j m) * M j) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun z hz =>
            hupperMoment j hj' hjm z ((hfin j m hjm).mem_toFinset.mp hz))) (hw j m).le
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    calc
      _ ≤ _ := hs
      _ ≤ _ * (Real.exp ((Q : ℝ) * detIncrement P q j m) * M j) :=
        mul_le_mul_of_nonneg_right (hcount j hjm) (mul_nonneg (Real.exp_nonneg _) hM)
      _ = _ := by ring
  exact htotal.trans (add_le_add hLbound (Finset.sum_le_sum hUbound))


/-- `ℋ^fluc_q(m) ≤ 𝒫_q(m;n)` with coefficient one (`p.fixed.geometry.one.grid.propagation`). -/
theorem fluctuationHistory_le_profile (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (S : CoeffSpace d → ℝ),
      IsProbabilityMeasure P →
      IsStationaryLaw P →
      IsUnitRangeLaw P →
      CoarseEllipticityDagger P γ E Ψ K S →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
        ∀ (metric : Mat d), metric.PosDef →
          ∀ n m : ℤ, (jStar : ℤ) ≤ n → n ≤ m →
            fluctuationHistory P γ (Geometry.explicitRoundedGrid jStar metric) jStar m ≤
              profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m := by
  intro P E Ψ K S hP hstat hunit hdag jStar hjStar metric hmetric n m hn hnm
  let := hP
  let q := Geometry.explicitRoundedGrid jStar metric
  have hf := fluctuationHistory_decompose d hd γ hγ P E Ψ K S hP hstat hunit hdag
    jStar hjStar metric hmetric n m hn hnm
  have hm0 := meanHistory_nonneg d hd γ hγ P E Ψ K S hP hstat hunit hdag
    jStar hjStar metric hmetric (jStar : ℤ) n le_rfl hn
  have hm := meanHistory_nonneg d hd γ hγ P E Ψ K S hP hstat hunit hdag
    jStar hjStar metric hmetric n m hn hnm
  have hpen := (Annealed.adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag
    jStar hjStar metric hmetric n m hn hnm).2.2.2.2.2
  have hc : 0 ≤ (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (n : ℝ))) *
      (1 + meanPenalty (bigQ d γ) (relMean P q n m)) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith only [hpen])
  have hextra := mul_nonneg hc hm0
  unfold profile history
  nlinarith only [hf, hm, hextra]

/-- The printed estimate for the mean-history terms below `n`
(`p.fixed.geometry.one.grid.propagation`): multiply the
composed penalty by `3^{-¼(1-γ)(m-1-j)}` and sum over `j_* ≤ j < n`. -/
theorem meanHistory_lower_part_le (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (S : CoeffSpace d → ℝ),
      IsProbabilityMeasure P →
      IsStationaryLaw P →
      IsUnitRangeLaw P →
      CoarseEllipticityDagger P γ E Ψ K S →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
        ∀ (metric : Mat d), metric.PosDef →
          ∀ n m : ℤ, (jStar : ℤ) ≤ n → n ≤ m →
            ∑ j ∈ Finset.Ico (jStar : ℤ) n,
                (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - 1 - (j : ℝ))) *
                  meanPenalty (bigQ d γ)
                    (relMean P (Geometry.explicitRoundedGrid jStar metric) j m) ≤
              (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (n : ℝ))) *
                  (1 + meanPenalty (bigQ d γ)
                    (relMean P (Geometry.explicitRoundedGrid jStar metric) n m)) *
                  meanHistory P γ (Geometry.explicitRoundedGrid jStar metric) (jStar : ℤ) n +
                (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (n : ℝ))) *
                  meanPenalty (bigQ d γ)
                    (relMean P (Geometry.explicitRoundedGrid jStar metric) n m) *
                  ∑ j ∈ Finset.Ico (jStar : ℤ) n,
                    (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) - 1 - (j : ℝ))) := by
  intro P E Ψ K S hP hstat hunit hdag jStar hjStar metric hmetric n m hn hnm
  set q := Geometry.explicitRoundedGrid jStar metric
  let w : ℝ → ℝ := fun x => (3 : ℝ) ^ (-((1 - γ) / 4) * x)
  let p : ℤ → ℤ → ℝ := fun j k => meanPenalty (bigQ d γ) (relMean P q j k)
  have hsplit (j : ℤ) : w ((m : ℝ) - 1 - (j : ℝ)) =
      w ((m : ℝ) - (n : ℝ)) * w ((n : ℝ) - 1 - (j : ℝ)) := by
    dsimp only [w]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hterms : (∑ j ∈ Finset.Ico (jStar : ℤ) n, w ((m : ℝ) - 1 - (j : ℝ)) * p j m) ≤
      ∑ j ∈ Finset.Ico (jStar : ℤ) n,
        (w ((m : ℝ) - (n : ℝ)) * (1 + p n m) * (w ((n : ℝ) - 1 - (j : ℝ)) * p j n) +
          (w ((m : ℝ) - (n : ℝ)) * p n m) * w ((n : ℝ) - 1 - (j : ℝ))) := by
    apply Finset.sum_le_sum
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    have hc := meanPenalty_normalizedMean_compose d hd γ hγ P E Ψ K S hP hstat hunit hdag
      jStar hjStar metric hmetric j n m hj'.1 hj'.2.le hnm
    change 1 + p j m ≤ (1 + p n m) * (1 + p j n) at hc
    have hpen : p j m ≤ (1 + p n m) * p j n + p n m := by nlinarith only [hc]
    have hw : 0 ≤ w ((m : ℝ) - (n : ℝ)) * w ((n : ℝ) - 1 - (j : ℝ)) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _)
    rw [hsplit]
    have ht := mul_le_mul_of_nonneg_left hpen hw
    convert ht using 1
    ring
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hterms
  exact hterms

/-- `ℋ^mean_q(m) ≤ C 𝒫_q(m;n)` (`p.fixed.geometry.one.grid.propagation`): the geometric sum is
bounded by `C`, the
first term by the first term of the profile, and — when `m > n` — the leftover penalty by the
`j = n` term of `ℋ^mean_q(m;n)`; when `m = n` that leftover vanishes. -/
theorem meanHistory_le_profile (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ∀ (metric : Mat d), metric.PosDef →
            ∀ n m : ℤ, (jStar : ℤ) ≤ n → n ≤ m →
              meanHistory P γ (Geometry.explicitRoundedGrid jStar metric) (jStar : ℤ) m ≤
                C * profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m := by
  let B : ℝ := (1 - (3 : ℝ) ^ (-((1 - γ) / 4)))⁻¹
  have hB : 0 < B := by
    apply inv_pos.mpr
    apply sub_pos.mpr
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith only [hγ.2]
  refine ⟨1 + B, by linarith only [hB], ?_⟩
  intro P E Ψ K S hP hstat hunit hdag jStar hjStar metric hmetric n m hn hnm
  let := hP
  set q := Geometry.explicitRoundedGrid jStar metric
  let W := (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (n : ℝ)))
  let T := meanPenalty (bigQ d γ) (relMean P q n m)
  let R := meanHistory P γ q n m
  let A := W * (1 + T) * history P γ q jStar n
  have hW : 0 ≤ W := Real.rpow_nonneg (by norm_num) _
  have hT : 0 ≤ T := (Annealed.adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag
    jStar hjStar metric hmetric n m hn hnm).2.2.2.2.2
  have hR : 0 ≤ R := meanHistory_nonneg d hd γ hγ P E Ψ K S hP hstat hunit hdag
    jStar hjStar metric hmetric n m hn hnm
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
  have hhistory : 0 ≤ history P γ q jStar n := add_nonneg hfluc hmean0
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg hW (by linarith only [hT])) hhistory
  have hsum : 0 ≤ ∑ j ∈ Finset.Icc (n + 1) m,
      (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (j : ℝ))) *
      Real.exp ((bigQ d γ : ℝ) * detIncrement P q j m) *
      ∫ a, absSchattenNorm (bigQ d γ : ℝ) (normalizedFluctuationSelf P q j a) ^ bigQ d γ ∂P :=
    Finset.sum_nonneg fun j _ => mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.exp_nonneg _))
      (integral_nonneg fun _ => (bigQ_even d γ).pow_nonneg _)
  have hbase : A + R ≤ profile P γ q jStar n m := by
    unfold profile
    change A + R ≤ A + R + _
    linarith only [hsum]
  have hRp : R ≤ profile P γ q jStar n m := (le_add_of_nonneg_left hA).trans hbase
  have hWT : W * T ≤ R := by
    by_cases heq : n = m
    · subst m
      have ht : T = 0 := by
        dsimp only [T]
        rw [Annealed.normalizedMean_self d hd P γ E Ψ K S hstat hdag
          jStar hjStar metric hmetric n, meanPenalty_identity]
      rw [ht, mul_zero]
      exact hR
    · have hlt : n < m := lt_of_le_of_ne hnm heq
      have hterm (j : ℤ) (hj : j ∈ Finset.Ico n m) : 0 ≤
          (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - 1 - (j : ℝ))) *
            meanPenalty (bigQ d γ) (relMean P q j m) := by
        apply mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        exact (Annealed.adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag
          jStar hjStar metric hmetric j m (hn.trans (Finset.mem_Ico.mp hj).1)
          (Finset.mem_Ico.mp hj).2.le).2.2.2.2.2
      have hs := Finset.single_le_sum hterm (Finset.mem_Ico.mpr ⟨le_rfl, hlt⟩)
      have hw : W ≤ (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - 1 - (n : ℝ))) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        linarith only [hγ.2]
      exact (mul_le_mul_of_nonneg_right hw hT).trans hs
  have hfirst : W * (1 + T) * meanHistory P γ q (jStar : ℤ) n ≤ A := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hW (by linarith only [hT]))
    exact le_add_of_nonneg_left hfluc
  have htail : W * T * (∑ j ∈ Finset.Ico (jStar : ℤ) n,
      (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) - 1 - (j : ℝ)))) ≤ B * R := by
    calc
      _ ≤ W * T * B := mul_le_mul_of_nonneg_left
        (profile_geometric_weight_sum_le γ hγ (jStar : ℤ) n) (mul_nonneg hW hT)
      _ = B * (W * T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hWT hB.le
  have hlower := meanHistory_lower_part_le d hd γ hγ P E Ψ K S hP hstat hunit hdag
    jStar hjStar metric hmetric n m hn hnm
  have hset : Finset.Ico (jStar : ℤ) m = Finset.Ico (jStar : ℤ) n ∪ Finset.Ico n m := by
    ext j
    simp only [Finset.mem_Ico, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Ico (jStar : ℤ) n) (Finset.Ico n m) := by
    rw [Finset.disjoint_left]
    intro j hj hk
    have := Finset.mem_Ico.mp hj
    have := Finset.mem_Ico.mp hk
    omega
  have hsplit : meanHistory P γ q (jStar : ℤ) m =
      (∑ j ∈ Finset.Ico (jStar : ℤ) n,
        (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - 1 - (j : ℝ))) *
          meanPenalty (bigQ d γ) (relMean P q j m)) + R := by
    unfold meanHistory
    rw [hset, Finset.sum_union hdisj]
    rfl
  rw [hsplit]
  have hlow := hlower.trans (add_le_add hfirst htail)
  have htotal := add_le_add hlow (le_refl R)
  have hBR := mul_le_mul_of_nonneg_left hRp hB.le
  calc
    _ ≤ (A + B * R) + R := htotal
    _ ≤ _ := by nlinarith only [hbase, hBR]

/-- **Conjunct 1**, `e.fixed.geometry.profile.majorization`: the profile majorizes the history. -/
theorem history_le_profile (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ∀ (metric : Mat d), metric.PosDef →
            ∀ n m : ℤ, (jStar : ℤ) ≤ n → n ≤ m →
              history P γ (Geometry.explicitRoundedGrid jStar metric) jStar m ≤
                C * profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m := by
  obtain ⟨C, hC, hmean⟩ := meanHistory_le_profile d hd γ hγ
  refine ⟨1 + C, by linarith only [hC], ?_⟩
  intro P E Ψ K S hP hstat hunit hdag jStar hjStar metric hmetric n m hn hnm
  have hf := fluctuationHistory_le_profile d hd γ hγ P E Ψ K S hP hstat hunit hdag
    jStar hjStar metric hmetric n m hn hnm
  have hm := hmean P E Ψ K S hP hstat hunit hdag jStar hjStar metric hmetric n m hn hnm
  unfold history
  nlinarith only [hf, hm]

/-- **Conjunct 5**, `e.fixed.geometry.carried.majorization`
(`p.fixed.geometry.one.grid.propagation`):
the same majorization with the determinant drift carried on both sides. -/
theorem carried_history_majorization (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ∀ (metric : Mat d), metric.PosDef →
            ∀ n m : ℤ, (jStar : ℤ) ≤ n → n ≤ m →
              fluctuationHistory P γ (Geometry.explicitRoundedGrid jStar metric) jStar m +
                    meanHistory P γ (Geometry.explicitRoundedGrid jStar metric) (jStar : ℤ) m +
                    determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m ≤
                  C * (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                    determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m) := by
  obtain ⟨C, hC, hhistory⟩ := history_le_profile d hd γ hγ
  refine ⟨C + 1, by linarith only [hC], ?_⟩
  intro P E Ψ K S hP hstat hunit hdag jStar hjStar metric hmetric n m hn hnm
  let q := Geometry.explicitRoundedGrid jStar metric
  have hh := hhistory P E Ψ K S hP hstat hunit hdag jStar hjStar metric hmetric n m hn hnm
  have hf := fluctuationHistory_le_profile d hd γ hγ P E Ψ K S hP hstat hunit hdag
    jStar hjStar metric hmetric n m hn hnm
  have hf0 : 0 ≤ fluctuationHistory P γ q jStar m := by
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
  have hp : 0 ≤ profile P γ q jStar n m := hf0.trans hf
  have hD := determinantDrift_nonneg d hd γ P E Ψ K S hP hstat hunit hdag
    jStar hjStar metric hmetric m
  have hCD := mul_nonneg hC.le hD
  unfold history at hh
  nlinarith only [hh, hp, hCD]


end

end HCPolySupport.HighContrast.Multiscale
