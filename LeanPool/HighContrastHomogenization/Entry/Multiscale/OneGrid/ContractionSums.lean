/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.OneGrid.Recurrence

/-!
# High-contrast homogenization: Entry.Multiscale.OneGrid.ContractionSums

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Step 2 — the fluctuation and mean sums of a synchronized step

Group E of the printed proof (`p.fixed.geometry.one.grid.propagation`), second part: the new
fluctuation
terms of `𝒫_q(m+h;n)`, transport of the mean-history terms across a synchronized step, and
the mean terms of the new block `m ≤ j < m+h`.

Part of the proof of the result stated in
`HCPoly/Entry/Statements/OneGridPropagation.lean`.  Conventions of this group:
`q = 𝒬(𝔪)` is `Geometry.explicitRoundedGrid jStar metric` at every loss, history, profile and drift;
`metric` (not `m`) names the positive matrix, because `m`, `n`, `m₀` are generations; the
source lower scale `e.source.lower.scale` is carried exactly by the
source-facing module `HCPoly/Entry/OneGridPropagation.lean`; this group's stronger internal
algebraic and history lemmas omit an unused source threshold, and this group's generic
integration helpers take finiteness, integrability or measurability inputs that are proved
at their actual use sites, not extra premises of the printed proposition.

-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

private theorem weighted_exp_product_bound (a b v u w x y z upper : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (hp : v ≤ a * Real.exp y * u + b * (Real.exp y - 1))
    (heq : Real.exp x * Real.exp y = Real.exp z)
    (hupper : Real.exp z ≤ upper) (hx : 1 ≤ Real.exp x) :
    w * Real.exp x * v ≤ a * upper * (w * u) + b * (upper - 1) * w := by
  have hproduct : Real.exp x * Real.exp y ≤ upper := by rw [heq]; exact hupper
  have hshifted : Real.exp x * (Real.exp y - 1) ≤ upper - 1 := by
    calc
      Real.exp x * (Real.exp y - 1) = Real.exp z - Real.exp x := by
        rw [mul_sub, mul_one, heq]
      _ ≤ upper - 1 := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hp (mul_nonneg hw (Real.exp_nonneg x))
  have hfirst : w * Real.exp x * (a * Real.exp y * u) ≤ a * upper * (w * u) := by
    calc
      _ = (a * (Real.exp x * Real.exp y)) * (w * u) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hproduct ha) (mul_nonneg hw hu)
  have hsecond : w * Real.exp x * (b * (Real.exp y - 1)) ≤ b * (upper - 1) * w := by
    calc
      _ = (b * (Real.exp x * (Real.exp y - 1))) * w := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hshifted hb) hw
  calc
    w * Real.exp x * v ≤ w * Real.exp x * (a * Real.exp y * u + b * (Real.exp y - 1)) := hscaled
    _ = w * Real.exp x * (a * Real.exp y * u) + w * Real.exp x * (b * (Real.exp y - 1)) := by ring
    _ ≤ _ := add_le_add hfirst hsecond

private theorem weighted_sum_le_expanded_sum_of_subset
    (s t : Finset ℤ) (w v e : ℤ → ℝ) (hsubset : s ⊆ t)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hv : ∀ i ∈ t, 0 ≤ v i)
    (he : ∀ i ∈ s, 1 ≤ e i) (hen : ∀ i ∈ t, 0 ≤ e i) :
    ∑ i ∈ s, w i * v i ≤ ∑ i ∈ t, w i * e i * v i := by
  calc
    ∑ i ∈ s, w i * v i ≤ ∑ i ∈ s, w i * e i * v i := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_right (hw i (hsubset hi)) (he i hi)) (hv i (hsubset hi))
    _ ≤ ∑ i ∈ t, w i * e i * v i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset fun i hi _ =>
        mul_nonneg (mul_nonneg (hw i hi) (hen i hi)) (hv i hi)

private theorem shifted_geometric_weight_sum_le (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (m : ℤ) (h : ℕ) :
    ∑ j ∈ Finset.Icc (m + 1) (m + (h : ℤ)),
      (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + (h : ℤ) : ℤ) : ℝ) - (j : ℝ))) ≤
      (1 - (3 : ℝ) ^ (-((1 - γ) / 4)))⁻¹ := by
  have hset : Finset.Icc (m + 1) (m + (h : ℤ)) = Finset.Ico (m + 1) (m + (h : ℤ) + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have heq : ∑ j ∈ Finset.Ico (m + 1) (m + (h : ℤ) + 1),
      (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + (h : ℤ) : ℤ) : ℝ) - (j : ℝ))) =
      ∑ j ∈ Finset.Ico (m + 1) (m + (h : ℤ) + 1),
        (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + (h : ℤ) + 1 : ℤ) : ℝ) - 1 - (j : ℝ))) := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    push_cast
    try ring
  rw [hset, heq]
  exact profile_geometric_weight_sum_le γ hγ (m + 1) (m + (h : ℤ) + 1)

/-- The new fluctuation terms of `𝒫_q(m+h;n)` (`p.fixed.geometry.one.grid.propagation`): apply the
powered
recurrence at `j-h ∈ [n+1,m]`, use additivity
`Δ^q_{j,m+h} + Δ^q_{j-h,j} = Δ^q_{j-h,m+h} ≤ Δ̂^q_h(m)` and
`e^{QΔ^q_{j,m+h}}(e^{QΔ^q_{j-h,j}} - 1) ≤ e^{QΔ̂^q_h(m)} - 1`, then sum. -/
theorem new_fluctuation_sum_le (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
          (S : CoeffSpace d → ℝ),
          IsProbabilityMeasure P →
          IsStationaryLaw P →
          IsUnitRangeLaw P →
          CoarseEllipticityDagger P γ E Ψ K S →
          ∀ (h : ℕ), 2 * bigQ d γ ≤ h →
            ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
              ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
                ∀ (metric : Mat d), metric.PosDef →
                  ∀ n m : ℤ, (jStar : ℤ) ≤ n → n + (h : ℤ) ≤ m →
                    ∑ j ∈ Finset.Icc (m + 1) (m + (h : ℤ)),
                        (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + (h : ℤ) : ℤ) : ℝ) - (j : ℝ))) *
                            Real.exp ((bigQ d γ : ℝ) *
                              detIncrement P (Geometry.explicitRoundedGrid jStar metric)
                                j (m + (h : ℤ))) *
                          ∫ a, absSchattenNorm (bigQ d γ : ℝ)
                              (normalizedFluctuationSelf P
                                (Geometry.explicitRoundedGrid jStar metric) j a) ^ bigQ d γ ∂P ≤
                      (2 : ℝ) ^ (bigQ d γ - 1) * ((3 : ℝ) ^ d * (bigQ d γ : ℝ)) ^ bigQ d γ *
                            (3 : ℝ) ^ (-((bigQ d γ : ℝ) * (d : ℝ) / 2) * (h : ℝ)) *
                            Real.exp ((bigQ d γ : ℝ) *
                              synchCharge P
                                (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) *
                            profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                          C * (Real.exp ((bigQ d γ : ℝ) *
                            synchCharge P
                              (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) - 1) := by
  obtain ⟨Csrc, hCsrc, hpow⟩ := parent_child_powered d hd γ hγ
  have hQ2 : 2 ≤ bigQ d γ := bigQ_two_le d γ hγ
  let Bc : ℝ := (2 : ℝ) ^ (2 * bigQ d γ - 1) *
    (1 + (d : ℝ) ^ (1 - (bigQ d γ : ℝ)⁻¹)) ^ bigQ d γ
  let G : ℝ := (1 - (3 : ℝ) ^ (-((1 - γ) / 4))) ⁻¹
  have hGpos : 0 < G := by
    apply inv_pos.mpr
    apply sub_pos.mpr
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith only [hγ.2]
  have hBcpos : 0 < Bc := by positivity
  refine ⟨Csrc, hCsrc, Bc * G, mul_pos hBcpos hGpos, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag h hh jStar hjStar hsrc metric hmetric n m hn hnm
  let := hP
  set q := Geometry.explicitRoundedGrid jStar metric
  have hh1N : 1 ≤ h := by omega
  have hh1 : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hh1N
  have hQnn : (0 : ℝ) ≤ (bigQ d γ : ℝ) := Nat.cast_nonneg _
  have hw : ∀ x : ℝ, 0 ≤ (3 : ℝ) ^ (-((1 - γ) / 4) * x) := fun x => Real.rpow_nonneg (by norm_num) _
  have hVnn : ∀ i : ℤ, 0 ≤ ∫ a, absSchattenNorm (bigQ d γ : ℝ)
      (normalizedFluctuationSelf P q i a) ^ bigQ d γ ∂P :=
    fun i => integral_nonneg fun _ => (bigQ_even d γ).pow_nonneg _
  let Ah : ℝ := (2 : ℝ) ^ (bigQ d γ - 1) * ((3 : ℝ) ^ d * (bigQ d γ : ℝ)) ^ bigQ d γ *
    (3 : ℝ) ^ (-((bigQ d γ : ℝ) * (d : ℝ) / 2) * (h : ℝ))
  let ehat : ℝ := Real.exp ((bigQ d γ : ℝ) * synchCharge P q (h : ℤ) m)
  have hAhnn : 0 ≤ Ah := by positivity
  have hBcnn : 0 ≤ Bc := hBcpos.le
  have hehat1 : 1 ≤ ehat := by
    apply Real.one_le_exp
    apply mul_nonneg hQnn
    unfold synchCharge
    apply Finset.sum_nonneg
    intro a ha
    simp only [Finset.mem_Icc] at ha
    exact Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric
      (a - (h : ℤ)) a (by omega) (by omega)
  -- termwise bound
  have hterm : ∀ j ∈ Finset.Icc (m + 1) (m + (h : ℤ)),
      (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + (h : ℤ) : ℤ) : ℝ) - (j : ℝ))) *
          Real.exp ((bigQ d γ : ℝ) * detIncrement P q j (m + (h : ℤ))) *
        ∫ a, absSchattenNorm (bigQ d γ : ℝ) (normalizedFluctuationSelf P q j a) ^ bigQ d γ ∂P ≤
      Ah * ehat * ((3 : ℝ) ^ (-((1 - γ) / 4) * (((m + (h : ℤ) : ℤ) : ℝ) - (j : ℝ))) *
          ∫ a, absSchattenNorm (bigQ d γ : ℝ)
            (normalizedFluctuationSelf P q (j - (h : ℤ)) a) ^ bigQ d γ ∂P) +
        Bc * (ehat - 1) *
          (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + (h : ℤ) : ℤ) : ℝ) - (j : ℝ))) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    obtain ⟨hj1, hj2⟩ := hj
    have hjhge : (jStar : ℤ) ≤ j - (h : ℤ) := by omega
    have hp : ∫ a, absSchattenNorm (bigQ d γ : ℝ) (normalizedFluctuationSelf P q j a) ^ bigQ d γ
      ∂P ≤
        Ah * Real.exp ((bigQ d γ : ℝ) * detIncrement P q (j - (h : ℤ)) j) *
            (∫ a, absSchattenNorm (bigQ d γ : ℝ)
              (normalizedFluctuationSelf P q (j - (h : ℤ)) a) ^ bigQ d γ ∂P) +
          Bc * (Real.exp ((bigQ d γ : ℝ) * detIncrement P q (j - (h : ℤ)) j) - 1) := by
      have hraw := hpow P E Ψ K S hP hstat hunit hdag jStar hjStar hsrc metric hmetric
        (j - (h : ℤ)) (h : ℤ) hjhge hh1
      rwa [show j - (h : ℤ) + (h : ℤ) = j from by ring] at hraw
    have hnn1 : 0 ≤ detIncrement P q j (m + (h : ℤ)) :=
      Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric
        j (m + (h : ℤ)) (by omega) (by omega)
    have he1 : (1 : ℝ) ≤ Real.exp ((bigQ d γ : ℝ) * detIncrement P q j (m + (h : ℤ))) :=
      Real.one_le_exp (mul_nonneg hQnn hnn1)
    have hadd := logDetLoss_add P q (j - (h : ℤ)) j (m + (h : ℤ))
    have hsync := logDetLoss_le_synchronizedLogDetLoss d hd γ hγ P E Ψ K S hP hstat hunit hdag
      h hh1N jStar hjStar metric hmetric m j (by omega) (by omega) (by omega)
    have hexpeq : Real.exp ((bigQ d γ : ℝ) * detIncrement P q j (m + (h : ℤ))) *
        Real.exp ((bigQ d γ : ℝ) * detIncrement P q (j - (h : ℤ)) j) =
        Real.exp ((bigQ d γ : ℝ) * detIncrement P q (j - (h : ℤ)) (m + (h : ℤ))) := by
      rw [← Real.exp_add, ← mul_add,
        add_comm (detIncrement P q j (m + (h : ℤ))) (detIncrement P q (j - (h : ℤ)) j), hadd]
    have hle1 : Real.exp ((bigQ d γ : ℝ) *
        detIncrement P q (j - (h : ℤ)) (m + (h : ℤ))) ≤ ehat :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsync hQnn)
    have hnn0 : 0 ≤ (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + (h : ℤ) : ℤ) : ℝ) - (j : ℝ))) := hw _
    exact weighted_exp_product_bound Ah Bc
      (∫ a, absSchattenNorm (bigQ d γ : ℝ)
        (normalizedFluctuationSelf P q j a) ^ bigQ d γ ∂P)
      (∫ a, absSchattenNorm (bigQ d γ : ℝ)
        (normalizedFluctuationSelf P q (j - (h : ℤ)) a) ^ bigQ d γ ∂P)
      ((3 : ℝ) ^ (-((1 - γ) / 4) * (((m + (h : ℤ) : ℤ) : ℝ) - (j : ℝ))))
      ((bigQ d γ : ℝ) * detIncrement P q j (m + (h : ℤ)))
      ((bigQ d γ : ℝ) * detIncrement P q (j - (h : ℤ)) j)
      ((bigQ d γ : ℝ) * detIncrement P q (j - (h : ℤ)) (m + (h : ℤ))) ehat
      hAhnn hBcnn (hVnn (j - (h : ℤ))) hnn0 hp hexpeq hle1 he1
  -- group 2: geometric weight sum
  have hsum2 : ∑ j ∈ Finset.Icc (m + 1) (m + (h : ℤ)),
      (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + (h : ℤ) : ℤ) : ℝ) - (j : ℝ))) ≤ G :=
    shifted_geometric_weight_sum_le γ hγ m h
  -- group 1: reindex, extend, compare to profile
  have hsum1 : ∑ j ∈ Finset.Icc (m + 1) (m + (h : ℤ)),
      ((3 : ℝ) ^ (-((1 - γ) / 4) * (((m + (h : ℤ) : ℤ) : ℝ) - (j : ℝ))) *
        ∫ a, absSchattenNorm (bigQ d γ : ℝ)
          (normalizedFluctuationSelf P q (j - (h : ℤ)) a) ^ bigQ d γ ∂P) ≤
      profile P γ q jStar n m := by
    have hreindex : ∑ j ∈ Finset.Icc (m + 1) (m + (h : ℤ)),
        ((3 : ℝ) ^ (-((1 - γ) / 4) * (((m + (h : ℤ) : ℤ) : ℝ) - (j : ℝ))) *
          ∫ a, absSchattenNorm (bigQ d γ : ℝ)
            (normalizedFluctuationSelf P q (j - (h : ℤ)) a) ^ bigQ d γ ∂P) =
        ∑ i ∈ Finset.Icc (m + 1 - (h : ℤ)) m,
          ((3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (i : ℝ))) *
            ∫ a, absSchattenNorm (bigQ d γ : ℝ)
              (normalizedFluctuationSelf P q i a) ^ bigQ d γ ∂P) := by
      apply Finset.sum_nbij' (fun j => j - (h : ℤ)) (fun i => i + (h : ℤ))
      · intro a ha
        simp only [Finset.mem_Icc] at ha ⊢
        omega
      · intro a ha
        simp only [Finset.mem_Icc] at ha ⊢
        omega
      · intro a _; ring
      · intro a _; ring
      · intro a _
        congr 2
        push_cast
        try ring
    rw [hreindex]
    have hie1 : ∀ i ∈ Finset.Icc (m + 1 - (h : ℤ)) m,
        (1 : ℝ) ≤ Real.exp ((bigQ d γ : ℝ) * detIncrement P q i m) := by
      intro i hi
      simp only [Finset.mem_Icc] at hi
      apply Real.one_le_exp
      apply mul_nonneg hQnn
      exact Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric
        i m (by omega) (by omega)
    have hstep : ∑ i ∈ Finset.Icc (m + 1 - (h : ℤ)) m,
        ((3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (i : ℝ))) *
          ∫ a, absSchattenNorm (bigQ d γ : ℝ)
            (normalizedFluctuationSelf P q i a) ^ bigQ d γ ∂P) ≤
        ∑ i ∈ Finset.Icc (n + 1) m,
          ((3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (i : ℝ))) *
              Real.exp ((bigQ d γ : ℝ) * detIncrement P q i m) *
            ∫ a, absSchattenNorm (bigQ d γ : ℝ)
              (normalizedFluctuationSelf P q i a) ^ bigQ d γ ∂P) := by
      exact weighted_sum_le_expanded_sum_of_subset
        (Finset.Icc (m + 1 - (h : ℤ)) m) (Finset.Icc (n + 1) m)
        (fun i => (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (i : ℝ))))
        (fun i => ∫ a, absSchattenNorm (bigQ d γ : ℝ)
          (normalizedFluctuationSelf P q i a) ^ bigQ d γ ∂P)
        (fun i => Real.exp ((bigQ d γ : ℝ) * detIncrement P q i m))
        (Finset.Icc_subset_Icc (by omega) le_rfl)
        (fun i _ => hw _) (fun i _ => hVnn i) hie1 (fun i _ => Real.exp_nonneg _)
    have hprofnn : 0 ≤ (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (n : ℝ))) *
          (1 + meanPenalty (bigQ d γ) (relMean P q n m)) * history P γ q jStar n +
        meanHistory P γ q n m := by
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
      have hpen := (Annealed.adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag
        jStar hjStar metric hmetric n m hn (by omega)).2.2.2.2.2
      have hmean0' := meanHistory_nonneg d hd γ hγ P E Ψ K S hP hstat hunit hdag
        jStar hjStar metric hmetric n m hn (by omega)
      apply add_nonneg
      · exact mul_nonneg (mul_nonneg (hw _) (by linarith only [hpen])) hhistory
      · exact hmean0'
    have hcombine : ∑ i ∈ Finset.Icc (n + 1) m,
        ((3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (i : ℝ))) *
            Real.exp ((bigQ d γ : ℝ) * detIncrement P q i m) *
          ∫ a, absSchattenNorm (bigQ d γ : ℝ)
            (normalizedFluctuationSelf P q i a) ^ bigQ d γ ∂P) ≤
        profile P γ q jStar n m := by
      unfold profile
      exact le_add_of_nonneg_left hprofnn
    exact hstep.trans hcombine
  -- combine
  calc
    ∑ j ∈ Finset.Icc (m + 1) (m + (h : ℤ)),
        (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + (h : ℤ) : ℤ) : ℝ) - (j : ℝ))) *
            Real.exp ((bigQ d γ : ℝ) * detIncrement P q j (m + (h : ℤ))) *
          ∫ a, absSchattenNorm (bigQ d γ : ℝ) (normalizedFluctuationSelf P q j a) ^ bigQ d γ ∂P
      ≤ ∑ j ∈ Finset.Icc (m + 1) (m + (h : ℤ)),
          (Ah * ehat * ((3 : ℝ) ^ (-((1 - γ) / 4) * (((m + (h : ℤ) : ℤ) : ℝ) - (j : ℝ))) *
              ∫ a, absSchattenNorm (bigQ d γ : ℝ)
                (normalizedFluctuationSelf P q (j - (h : ℤ)) a) ^ bigQ d γ ∂P) +
            Bc * (ehat - 1) *
              (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + (h : ℤ) : ℤ) : ℝ) - (j : ℝ)))) :=
        Finset.sum_le_sum hterm
    _ = Ah * ehat * (∑ j ∈ Finset.Icc (m + 1) (m + (h : ℤ)),
            ((3 : ℝ) ^ (-((1 - γ) / 4) * (((m + (h : ℤ) : ℤ) : ℝ) - (j : ℝ))) *
              ∫ a, absSchattenNorm (bigQ d γ : ℝ)
                (normalizedFluctuationSelf P q (j - (h : ℤ)) a) ^ bigQ d γ ∂P)) +
          Bc * (ehat - 1) * (∑ j ∈ Finset.Icc (m + 1) (m + (h : ℤ)),
            (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + (h : ℤ) : ℤ) : ℝ) - (j : ℝ)))) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ Ah * ehat * profile P γ q jStar n m + Bc * (ehat - 1) * G :=
        add_le_add (mul_le_mul_of_nonneg_left hsum1 (mul_nonneg hAhnn (by linarith only [hehat1])))
          (mul_le_mul_of_nonneg_left hsum2
            (mul_nonneg hBcnn (by linarith only [hehat1])))
    _ = Ah * ehat * profile P γ q jStar n m + Bc * G * (ehat - 1) := by ring

/-- Transport of the mean-history terms across a synchronized step
(`p.fixed.geometry.one.grid.propagation`). -/
theorem meanHistory_transport_le (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (h : ℕ), 2 * bigQ d γ ≤ h →
          ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
            ∀ (metric : Mat d), metric.PosDef →
              ∀ n m : ℤ, (jStar : ℤ) ≤ n → n + (h : ℤ) ≤ m →
                ∑ j ∈ Finset.Ico n m,
                    (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + (h : ℤ) : ℤ) : ℝ) - 1 - (j : ℝ))) *
                      meanPenalty (bigQ d γ)
                        (relMean P (Geometry.explicitRoundedGrid jStar metric)
                          j (m + (h : ℤ))) ≤
                  (3 : ℝ) ^ (-((1 - γ) / 4) * (h : ℝ)) *
                        Real.exp ((bigQ d γ : ℝ) *
                          detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m + (h :
                            ℤ))) *
                        meanHistory P γ (Geometry.explicitRoundedGrid jStar metric) n m +
                      C * (Real.exp ((bigQ d γ : ℝ) *
                        detIncrement P (Geometry.explicitRoundedGrid jStar metric)
                          m (m + (h : ℤ))) - 1) := by
  let B : ℝ := (1 - (3 : ℝ) ^ (-((1 - γ) / 4)))⁻¹
  have hB : 0 < B := by
    apply inv_pos.mpr
    apply sub_pos.mpr
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith only [hγ.2]
  refine ⟨B, hB, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag h hh jStar hjStar metric hmetric n m hn hnm0
  let L : ℤ := h
  have hL : 1 ≤ L := by
    have hQ := bigQ_two_le d γ hγ
    dsimp only [L]
    omega
  have hnm : n ≤ m := by omega
  let := hP
  set q := Geometry.explicitRoundedGrid jStar metric
  let w : ℝ → ℝ := fun x => (3 : ℝ) ^ (-((1 - γ) / 4) * x)
  let p : ℤ → ℤ → ℝ := fun j k => meanPenalty (bigQ d γ) (relMean P q j k)
  let e := Real.exp ((bigQ d γ : ℝ) * detIncrement P q m (m + L))
  have hw (x : ℝ) : 0 ≤ w x := Real.rpow_nonneg (by norm_num) _
  have hwL : w (L : ℝ) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith only [hγ.2]) (by exact_mod_cast (by omega
      : (0 : ℤ) ≤ L))
  have hsplit (x : ℝ) : w ((L : ℝ) + x) = w (L : ℝ) * w x := by
    dsimp only [w]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have he : 1 ≤ e := Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _)
    (Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric
      m (m + L) (hn.trans hnm) (by omega)))
  have hadv (j : ℤ) (hj : (jStar : ℤ) ≤ j) (hjm : j ≤ m) :
      1 + p j (m + L) ≤ e * (1 + p j m) := by
    have h := meanPenalty_normalizedMean_advance d hd γ hγ P E Ψ K S hP hstat hunit hdag
      jStar hjStar metric hmetric j m (m + L) hj hjm (by omega)
    change p j (m + L) ≤ e * p j m + e - 1 at h
    linarith only [h]
  have hmean : (∑ j ∈ Finset.Ico n m,
      w (((m + L : ℤ) : ℝ) - 1 - (j : ℝ)) * p j (m + L)) ≤
      w (L : ℝ) * e * meanHistory P γ q n m + B * (e - 1) := by
    have hterms : (∑ j ∈ Finset.Ico n m,
        w (((m + L : ℤ) : ℝ) - 1 - (j : ℝ)) * p j (m + L)) ≤
        ∑ j ∈ Finset.Ico n m, (w (L : ℝ) * e *
          (w ((m : ℝ) - 1 - (j : ℝ)) * p j m) +
          (w (L : ℝ) * (e - 1)) * w ((m : ℝ) - 1 - (j : ℝ))) := by
      apply Finset.sum_le_sum
      intro j hj
      have had := hadv j (hn.trans (Finset.mem_Ico.mp hj).1) (Finset.mem_Ico.mp hj).2.le
      have hweight : w (((m + L : ℤ) : ℝ) - 1 - (j : ℝ)) =
          w (L : ℝ) * w ((m : ℝ) - 1 - (j : ℝ)) := by
        convert hsplit ((m : ℝ) - 1 - (j : ℝ)) using 1; congr 1; push_cast; ring
      rw [hweight]
      have hp : p j (m + L) ≤ e * p j m + (e - 1) := by linarith only [had]
      have h := mul_le_mul_of_nonneg_left hp (mul_nonneg (hw (L : ℝ)) (hw ((m : ℝ) - 1 - (j : ℝ))))
      convert h using 1
      ring
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hterms
    have hs := profile_geometric_weight_sum_le γ hγ n m
    change ∑ j ∈ Finset.Ico n m, w ((m : ℝ) - 1 - (j : ℝ)) ≤ B at hs
    have htail : (w (L : ℝ) * (e - 1)) *
        (∑ j ∈ Finset.Ico n m, w ((m : ℝ) - 1 - (j : ℝ))) ≤ B * (e - 1) := by
      calc
        _ ≤ (w (L : ℝ) * (e - 1)) * B :=
          mul_le_mul_of_nonneg_left hs (mul_nonneg (hw _) (sub_nonneg.mpr he))
        _ ≤ B * (e - 1) := by
          have h := mul_le_mul_of_nonneg_right hwL (mul_nonneg (sub_nonneg.mpr he) hB.le)
          convert h using 1 <;> first | rfl | ring
    exact hterms.trans (add_le_add le_rfl htail)
  exact hmean

/-- The mean terms of the new block `m ≤ j < m+h` (`p.fixed.geometry.one.grid.propagation`): there
the eigenvalues of
`P^q_{j,m+h}` are at least one, so `1 + tr(P^q_{j,m+h} - I) ≤ det P^q_{j,m+h} = e^{Δ^q_{j,m+h}}
≤ e^{Δ̂^q_h(m)}`. -/
theorem meanPenalty_upper_block_sum_le (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (h : ℕ), 2 * bigQ d γ ≤ h →
          ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
            ∀ (metric : Mat d), metric.PosDef →
              ∀ n m : ℤ, (jStar : ℤ) ≤ n → n + (h : ℤ) ≤ m →
                ∑ j ∈ Finset.Ico m (m + (h : ℤ)),
                    (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + (h : ℤ) : ℤ) : ℝ) - 1 - (j : ℝ))) *
                      meanPenalty (bigQ d γ)
                        (relMean P (Geometry.explicitRoundedGrid jStar metric)
                          j (m + (h : ℤ))) ≤
                  C * (Real.exp ((bigQ d γ : ℝ) *
                    synchCharge P
                      (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) - 1) := by
  let B : ℝ := (1 - (3 : ℝ) ^ (-((1 - γ) / 4)))⁻¹
  have hB : 0 < B := by
    apply inv_pos.mpr
    apply sub_pos.mpr
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith only [hγ.2]
  refine ⟨B, hB, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag h hh jStar hjStar metric hmetric n m hn hnm
  let := hP
  set q := Geometry.explicitRoundedGrid jStar metric
  have hh1 : 1 ≤ h := by
    have := bigQ_two_le d γ hγ
    omega
  have hsync : detIncrement P q m (m + (h : ℤ)) ≤ synchCharge P q (h : ℤ) m := by
    have hbound := logDetLoss_le_synchronizedLogDetLoss d hd γ hγ P E Ψ K S hP hstat hunit hdag
      h hh1 jStar hjStar metric hmetric m (m + (h : ℤ)) (by omega) (by omega) le_rfl
    simpa only [add_sub_cancel_right] using hbound
  have he : 0 ≤ Real.exp ((bigQ d γ : ℝ) * synchCharge P q (h : ℤ) m) - 1 := by
    apply sub_nonneg.mpr
    apply Real.one_le_exp
    apply mul_nonneg (Nat.cast_nonneg _)
    exact (Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag
      jStar hjStar metric hmetric m (m + (h : ℤ)) (by omega) (by omega)).trans hsync
  have hterm (j : ℤ) (hj : j ∈ Finset.Ico m (m + (h : ℤ))) :
      meanPenalty (bigQ d γ) (relMean P q j (m + (h : ℤ))) ≤
      Real.exp ((bigQ d γ : ℝ) * synchCharge P q (h : ℤ) m) - 1 := by
    have hj' := Finset.mem_Ico.mp hj
    have hpen := meanPenalty_normalizedMean_le_exp_sub_one d hd γ hγ P E Ψ K S hP hstat hunit hdag
      jStar hjStar metric hmetric j (m + (h : ℤ)) (by omega) hj'.2.le
    have hinc := Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag
      jStar hjStar metric hmetric m j (by omega) hj'.1
    have hadd := logDetLoss_add P q m j (m + (h : ℤ))
    have hloss : detIncrement P q j (m + (h : ℤ)) ≤ synchCharge P q (h : ℤ) m := by
      linarith only [hinc, hadd, hsync]
    exact hpen.trans (sub_le_sub_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hloss (Nat.cast_nonneg _))) 1)
  calc
    _ ≤ ∑ j ∈ Finset.Ico m (m + (h : ℤ)),
        (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + (h : ℤ) : ℤ) : ℝ) - 1 - (j : ℝ))) *
        (Real.exp ((bigQ d γ : ℝ) * synchCharge P q (h : ℤ) m) - 1) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hterm j hj) (Real.rpow_nonneg (by norm_num) _)
    _ ≤ _ := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (profile_geometric_weight_sum_le γ hγ m (m + (h : ℤ))) he

end

end HCPolySupport.HighContrast.Multiscale
