/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.TransportDrift

/-!
# High-contrast homogenization: Entry.Annealed.TransportProfileComparison

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Profile comparison for the two-grid transport

This module proves the profile comparison behind `p.two.grid.transport`. It bounds the
joint maximum of a common source envelope and two fluctuation envelopes by three scalar
moments, with no factor for the number of targets or generations; pays the actual lattice
count on the target range through the mean-decay gap; records the weighted mean-history
convention with its fixed factor `3^{(1−γ)/4}`; accumulates the bulk and boundary means,
the comparison error and both source powers while keeping the early target range separate;
and shows that a source bound on an actual target controls both its centered matrix and
its deterministic mean penalty at the same geometric amplitude. The resulting printed
estimate compares the profiles of two geometries within projective distance and
Loewner-close annealed blocks, at the growth `3^{(1−γ)L/2}`, the comparison error and the
determinant drift of the transported geometry, with the two source amplitudes kept
separate.
-/
open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter adaptedMean aspectRatio
  aspectRatio_nonneg blockScale blockSub blockTrace coarseBlock gridRatio normalizedBlock)
open HCPolySupport.HighContrast (adaptedCell aspectRatio_nonneg centeredCube standardCellCenter)
namespace HCPolySupport.HighContrast.Annealed
open MeasureTheory Geometry Multiscale Analysis
open scoped Matrix.Norms.L2Operator MatrixOrder Matrix
noncomputable section

/-- The power of three with an arbitrary real exponent is nonnegative. -/
private lemma three_rpow_nonneg (x : ℝ) : 0 ≤ (3 : ℝ) ^ x :=
  Real.rpow_nonneg (by norm_num) x

/-- A power of a power of three is nonnegative. -/
private lemma three_rpow_rpow_nonneg (x y : ℝ) : 0 ≤ ((3 : ℝ) ^ x) ^ y :=
  Real.rpow_nonneg (three_rpow_nonneg x) y

/-- A common source envelope and two fluctuation maxima combine with three
scalar moments. There is no factor for the number of targets or generations. -/
theorem transport_joint_three_envelopes {α ι : Type*} [MeasurableSpace α]
    {P : Measure α} (Q : ℕ) (hQ : 0 < Q) (I : Finset ι) (hI : I.Nonempty)
    (f : ι → α → ℝ) (hf0 : ∀ i ∈ I, ∀ᵐ a ∂P, 0 ≤ f i a) (hf : ∀ i ∈ I, MemLp (f i)
      (ENNReal.ofReal (Q : ℝ)) P) (X Y Z : α → ℝ) (hX0 : ∀ᵐ a ∂P, 0 ≤ X a) (hY0 : ∀ᵐ a ∂P, 0 ≤ Y a)
    (hZ0 : ∀ᵐ a ∂P, 0 ≤ Z a) (hX : MemLp X (ENNReal.ofReal (Q : ℝ)) P) (hY : MemLp Y
      (ENNReal.ofReal (Q : ℝ)) P) (hZ : MemLp Z (ENNReal.ofReal (Q : ℝ)) P) (A D : ℝ) (hA : 0 ≤
      A) (hD : 0 ≤ D)
    (hbound : ∀ i ∈ I, ∀ᵐ a ∂P, f i a ≤ A * (X a + Y a) + D * Z a) :
    (∫ a, (⨆ i ∈ (I : Set ι), f i a) ^ (Q : ℝ) ∂P) ≤
      (3 : ℝ) ^ Q * (A ^ Q * ((∫ a, X a ^ Q ∂P) + ∫ a, Y a ^ Q ∂P) +
        D ^ Q * ∫ a, Z a ^ Q ∂P) := by
  have hQr : 0 < (Q : ℝ) := by exact_mod_cast hQ
  let F : Fin 3 → α → ℝ := ![fun a => A * X a, fun a => A * Y a, fun a => D * Z a]
  have hF0 (i : Fin 3) : ∀ᵐ a ∂P, 0 ≤ F i a := by
    fin_cases i
    · exact hX0.mono fun _ ha => mul_nonneg hA ha
    · exact hY0.mono fun _ ha => mul_nonneg hA ha
    · exact hZ0.mono fun _ ha => mul_nonneg hD ha
  have hF (i : Fin 3) : MemLp (F i) (ENNReal.ofReal (Q : ℝ)) P := by
    fin_cases i
    · exact hX.const_mul A
    · exact hY.const_mul A
    · exact hZ.const_mul D
  have hs := transport_weighted_moment_sum Q hQ Finset.univ (fun _ : Fin 3 => (1 : ℝ))
    (fun _ _ => by norm_num) F (fun i _ => hF0 i) (fun i _ => hF i) (M := 3) (by norm_num) (by
      norm_num)
  have ht := transport_joint_envelope_moment hQr (by norm_num : (0 : ℝ) ≤ 1) I hI f hf0 hf
    (fun a => A * (X a + Y a) + D * Z a)
    (by filter_upwards [hX0, hY0, hZ0] with a ha hb hc; positivity) (((hX.add hY).const_mul
      A).add (hZ.const_mul D)) (by simpa only [one_mul] using hbound)
  have he (a : α) : (∑ i : Fin 3, F i a) = A * (X a + Y a) + D * Z a := by
    simp only [Fin.sum_univ_succ, F, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero]
    ring
  simp only [Real.one_rpow, one_mul] at ht
  have hb := hs.2
  simp only [he, Fin.sum_univ_succ, F, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero, one_pow, inv_one, one_mul] at hb
  simp_rw [mul_pow, integral_const_mul] at hb
  simp only [Real.rpow_natCast] at ht ⊢
  calc
    _ ≤ (3 : ℝ) ^ Q * (A ^ Q * (∫ a, X a ^ Q ∂P) +
        (A ^ Q * (∫ a, Y a ^ Q ∂P) + D ^ Q * ∫ a, Z a ^ Q ∂P)) := ht.2.trans hb
    _ = _ := by ring
/-- The deterministic target sum pays the actual lattice count, then uses
Qρ−d ≥ (1−γ)/4. Only this mean term is summed over the target cells. -/
theorem transport_pair_mean_bound (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (I :
  Finset (ℤ × (Fin d → ℤ))) (J t : ℤ) (hgen : ∀ p ∈ I, p.1 ∈ Set.Icc J t)
    (hcenter : ∀ p ∈ I, standardCellCenter p.1 p.2 ∈ centeredCube d t) (M : ℤ × (Fin d → ℤ) → ℝ)
      (B : ℤ → ℝ) (hB : ∀ j ∈ Finset.Icc J t, 0 ≤ B j)
    (hM : ∀ p ∈ I, M p ≤ B p.1) :
    (∑ p ∈ I, ((3 : ℝ) ^ (-rhoMax d γ * ((t : ℝ) - p.1))) ^ (bigQ d γ : ℝ) * M p) ≤
      ∑ j ∈ Finset.Icc J t, (3 : ℝ) ^ (-((1 - γ) / 4) * ((t : ℝ) - j)) * B j := by
  classical
  let w := fun j : ℤ => ((3 : ℝ) ^ (-rhoMax d γ * ((t : ℝ) - j))) ^ (bigQ d γ : ℝ)
  have hmap : ∀ p ∈ I, p.1 ∈ Finset.Icc J t := fun p hp => Finset.mem_Icc.mpr (hgen p hp)
  change (∑ p ∈ I, w p.1 * M p) ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun p => w p.1 * M p)]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hne : (I.filter (fun p => p.1 = j)).Nonempty
  · have hc := transport_target_fiber_card I t (fun p hp => (hgen p hp).2) hcenter j (by
      obtain ⟨p, hp⟩ := hne
      exact Finset.mem_image.mpr ⟨p, (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩)
    have he : w j * (3 : ℝ) ^ ((d : ℝ) * ((t : ℝ) - j)) =
        (3 : ℝ) ^ (-((bigQ d γ : ℝ) * rhoMax d γ - (d : ℝ)) * ((t : ℝ) - j)) := by
      dsimp only [w]; rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), ← Real.rpow_add (by
        norm_num : (0 : ℝ) < 3)]
      congr 1; ring
    calc
      _ ≤ ∑ _p ∈ I.filter (fun p => p.1 = j), w j * B j := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hpI, hpj⟩ := Finset.mem_filter.mp hp
        simpa only [hpj] using mul_le_mul_of_nonneg_left (hM p hpI) (show 0 ≤ w p.1 from
          three_rpow_rpow_nonneg (-rhoMax d γ * ((t : ℝ) - p.1)) (bigQ d γ : ℝ))
      _ = (w j * ((I.filter (fun p => p.1 = j)).card : ℝ)) * B j := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ (w j * (3 : ℝ) ^ ((d : ℝ) * ((t : ℝ) - j))) * B j := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc (by dsimp only [w]; exact three_rpow_rpow_nonneg _ _)) (hB
        j hj)
      _ ≤ _ := by
        rw [he]
        exact mul_le_mul_of_nonneg_right (transport_mean_weight_le d hd γ hγ _
          (by exact_mod_cast sub_nonneg.mpr (Finset.mem_Icc.mp hj).2)).2 (hB j hj)
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
    exact mul_nonneg (three_rpow_nonneg _) (hB j hj)
/-- The mean-history convention uses t−1−j; its extra fixed factor is 3^a. -/
theorem transport_meanHistory_weighted_bound {d : ℕ} (P : Measure (CoeffSpace d)) (γ : ℝ) (q :
  Mat d) (J t : ℤ) (B : ℤ → ℝ) (hB : ∀ j ∈ Finset.Icc J t, 0 ≤ B j)
    (hM : ∀ j ∈ Finset.Ico J t, meanPenalty (bigQ d γ) (relMean P q j t) ≤ B j) :
    meanHistory P γ q J t ≤ (3 : ℝ) ^ ((1 - γ) / 4) *
      ∑ j ∈ Finset.Icc J t, (3 : ℝ) ^ (-((1 - γ) / 4) * ((t : ℝ) - j)) * B j := by
  have he (j : ℤ) : (3 : ℝ) ^ (-((1 - γ) / 4) * ((t : ℝ) - 1 - j)) =
      (3 : ℝ) ^ ((1 - γ) / 4) * (3 : ℝ) ^ (-((1 - γ) / 4) * ((t : ℝ) - j)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1; ring
  unfold meanHistory
  calc
    _ ≤ ∑ j ∈ Finset.Ico J t, (3 : ℝ) ^ (-((1 - γ) / 4) * ((t : ℝ) - 1 - j)) * B j :=
      Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hM j hj) (three_rpow_nonneg _)
    _ = (3 : ℝ) ^ ((1 - γ) / 4) *
        ∑ j ∈ Finset.Ico J t, (3 : ℝ) ^ (-((1 - γ) / 4) * ((t : ℝ) - j)) * B j := by
      simp_rw [he, mul_assoc]
      exact (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.Ico_subset_Icc_self
        (fun j hj _ => mul_nonneg (three_rpow_nonneg _) (hB j hj))) (three_rpow_nonneg _)
/-- Accumulation of the actual bulk and boundary means, comparison error and
both source powers, with the early target range kept separate. -/
theorem transport_weighted_mean_accumulation (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
      (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K
      S) (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (k n : ℤ) (hk : (jStar : ℤ) ≤ k) (hkn : k ≤ n) (L : ℕ) (hL : 1 ≤ L)
    (Cm Ce δ B : ℝ) (hCm : 0 ≤ Cm) (hCe : 0 ≤ Ce) (hδ : 0 ≤ δ) (hB : 0 ≤ B) :
    let q := explicitRoundedGrid jStar m
    let Q := bigQ d γ
    let a := (1 - γ) / 4
    let G₁ := 1 / (1 - (3 : ℝ) ^ (-a))
    let G₃ := 1 / (1 - (3 : ℝ) ^ (-(3 * (1 - γ) / 4)))
    let ell := fun j : ℤ => if j ≤ k + (L : ℤ) then 1 else L
    let p := fun r => meanPenalty Q (relMean P q r (n + 2 * (L : ℤ)))
    let decay := fun j : ℤ => (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - jStar))
    let M := fun j : ℤ => if j < (jStar : ℤ) + L then Ce * B ^ Q else Cm *
      (p (j - (ell j : ℤ)) +
        (∑ r ∈ Finset.Icc (jStar : ℤ) (j - (ell j : ℤ) - 1),
          (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - r)) * p r) + δ + B ^ Q * (decay j + decay j ^ Q))
    (∀ j ∈ Finset.Icc (jStar : ℤ) (n + (L : ℤ)), 0 ≤ M j) ∧
    (∑ j ∈ Finset.Icc (jStar : ℤ) (n + (L : ℤ)),
      (3 : ℝ) ^ (-a * ((n : ℝ) + L - j)) * M j) ≤
      Cm * ((2 + G₃) * (2 + G₁) * (3 : ℝ) ^ ((1 - γ) / 2 * (L : ℝ)) *
        profile P γ q jStar k (n + 2 * (L : ℤ)) + G₁ * δ +
        2 * G₃ * B ^ Q * (3 : ℝ) ^ (-a * ((n : ℝ) - jStar))) +
      Ce * G₁ * B ^ Q * (3 : ℝ) ^ (-a * ((n : ℝ) - jStar)) := by
  classical
  intro q Q a G₁ G₃ ell p decay M
  let J := (jStar : ℤ)
  let t := n + (L : ℤ)
  let U := Finset.Icc (J + (L : ℤ)) t
  let V := Finset.Icc J (J + (L : ℤ) - 1)
  let w := fun j : ℤ => (3 : ℝ) ^ (-a * ((n : ℝ) + L - j))
  let wb := fun j : ℤ => (3 : ℝ) ^ (-a * ((n : ℝ) + L - 1 - j))
  let bulk := fun j : ℤ => p (j - (ell j : ℤ))
  let bd := fun j : ℤ => ∑ r ∈ Finset.Icc J (j - (ell j : ℤ) - 1),
    (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - r)) * p r
  let D := (3 : ℝ) ^ ((1 - γ) / 2 * (L : ℝ))
  let R := (3 : ℝ) ^ (-a * ((n : ℝ) - jStar))
  let H := profile P γ q jStar k (n + 2 * (L : ℤ))
  have ha : 0 < a := by dsimp only [a]; linarith only [hγ.2]
  have hG₁ : 0 ≤ G₁ := (one_div_pos.mpr (transport_geometric_Icc a ha 0 0).1).le
  have hG₃ : 0 ≤ G₃ := (one_div_pos.mpr (transport_geometric_Icc (3 * (1 - γ) / 4) (by linarith
    only [hγ.2]) 0 0).1).le
  have hH : 0 ≤ H := bridge_profile_nonneg d hd P γ E Ψ K S hstat hdag jStar hj m hm k _ hk (by
    omega)
  have hell (j : ℤ) : 1 ≤ ell j ∧ ell j ≤ L := by dsimp only [ell]; split_ifs <;> omega
  have hcap (j) (hju : j ∈ U) : (jStar : ℤ) ≤ j - (ell j : ℤ) ∧ j - (ell j : ℤ) ≤ n + 2 * (L :
    ℤ) := by
    have hh := Finset.mem_Icc.mp hju
    have he := hell j
    dsimp only [J, t] at hh; omega
  have hp (r) (hr : (jStar : ℤ) ≤ r) (hrt : r ≤ n + 2 * (L : ℤ)) : 0 ≤ p r :=
    (adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag jStar hj m hm r _ hr hrt).2.2.2.2.2
  have hbulk (j) (hju : j ∈ U) : 0 ≤ bulk j := hp _ (hcap j hju).1 (hcap j hju).2
  have hbd (j) (hju : j ∈ U) : 0 ≤ bd j := Finset.sum_nonneg fun r hr =>
    mul_nonneg (three_rpow_nonneg _) (hp r (Finset.mem_Icc.mp hr).1
      (by have := (Finset.mem_Icc.mp hr).2; have := (hcap j hju).2; omega))
  constructor
  · intro j hjj
    dsimp only [M]
    split_ifs with he
    · exact mul_nonneg hCe (pow_nonneg hB Q)
    · have hju : j ∈ U := Finset.mem_Icc.mpr ⟨by dsimp only [J]; omega, (Finset.mem_Icc.mp hjj).2⟩
      change 0 ≤ Cm * (bulk j + bd j + δ + B ^ Q * (decay j + decay j ^ Q))
      have hb0 := hbulk j hju
      have hbd0 := hbd j hju
      have hdecay : 0 ≤ decay j := by dsimp only [decay]; exact three_rpow_nonneg _
      exact mul_nonneg hCm (add_nonneg (add_nonneg (add_nonneg hb0 hbd0) hδ)
        (mul_nonneg (pow_nonneg hB Q) (add_nonneg hdecay (pow_nonneg hdecay Q))))
  have hweight (j) : w j ≤ wb j := by
    dsimp only [w, wb]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith only [ha]
  have hwb : (∑ j ∈ U, w j * bulk j) ≤ 2 * (2 + G₁) * D * H := by
    calc
      _ ≤ ∑ j ∈ U, wb j * bulk j := Finset.sum_le_sum fun j hjj =>
        mul_le_mul_of_nonneg_right (hweight j) (hbulk j hjj)
      _ ≤ _ := transport_bulk_mean_bound d hd P γ hγ E Ψ K S hstat hdag jStar hj m hm k n hk hkn
        L hL
  have hwbd : (∑ j ∈ U, w j * bd j) ≤ G₃ * (2 + G₁) * D * H := by
    have hh := transport_boundary_mean_bound d hd P γ hγ E Ψ K S hstat hdag jStar hj m hm k n hk
      hkn L hL
    rw [show (3 : ℝ) / 4 * (1 - γ) = 3 * (1 - γ) / 4 by ring] at hh
    calc
      _ ≤ ∑ j ∈ U, wb j * bd j := Finset.sum_le_sum fun j hjj =>
        mul_le_mul_of_nonneg_right (hweight j) (hbd j hjj)
      _ ≤ G₃ * (2 + G₁) * (3 : ℝ) ^ (a * (L : ℝ)) * H := hh
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hH
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hG₃ (add_nonneg (by norm_num) hG₁))
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
          dsimp only [a]
          nlinarith only [mul_nonneg (sub_pos.mpr hγ.2).le (Nat.cast_nonneg L)])
  have hdelt : (∑ j ∈ U, w j * δ) ≤ G₁ * δ := by
    simpa only [t, Int.cast_add, Int.cast_natCast] using transport_comparison_error_sum a ha (J
      + (L : ℤ)) t δ hδ
  have hsrc : (∑ j ∈ U, w j * (decay j + decay j ^ Q)) ≤ 2 * G₃ * R := by
    have he (j : ℤ) : decay j ^ Q = (3 : ℝ) ^ (-(Q : ℝ) * (1 - γ) * ((j : ℝ) - jStar)) := by
      dsimp only [decay]; rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1; ring
    simp_rw [he]
    have hh := transport_fine_weight_sum γ hγ.2 Q (bigQ_pos d γ hγ) J n L
    apply hh.trans
    have hR : (3 : ℝ) ^ (-a * ((n : ℝ) + L - jStar)) ≤ R := Real.rpow_le_rpow_of_exponent_le (by
      norm_num) (by nlinarith only [mul_nonneg ha.le (Nat.cast_nonneg L)])
    have hc : 2 / (1 - (3 : ℝ) ^ (-(3 * (1 - γ) / 4))) = 2 * G₃ := by dsimp only [G₃]; ring
    rw [hc]; exact mul_le_mul_of_nonneg_left hR (mul_nonneg (by norm_num) hG₃)
  have hearly : (∑ j ∈ V, w j * (Ce * B ^ Q)) ≤ Ce * G₁ * B ^ Q * R := by
    have he : (∑ j ∈ V, w j * (Ce * B ^ Q)) = (Ce * B ^ Q) * ∑ j ∈ V, w j := by
      rw [← Finset.sum_mul]; ring
    rw [he]
    calc
      _ ≤ (Ce * B ^ Q) * (G₁ * R) := mul_le_mul_of_nonneg_left (transport_early_weight_sum a ha
        J n L) (mul_nonneg hCe (pow_nonneg hB Q))
      _ = _ := by ring
  have hu : V ∪ U = Finset.Icc J t := by
    ext j; simp only [V, U, Finset.mem_union, Finset.mem_Icc]
    dsimp only [J, t]; omega
  have hdis : Disjoint V U := by
    apply Finset.disjoint_left.mpr
    intro j h1 h2
    have hh1 := Finset.mem_Icc.mp h1
    have hh2 := Finset.mem_Icc.mp h2
    omega
  have he : (∑ j ∈ V, w j * M j) = ∑ j ∈ V, w j * (Ce * B ^ Q) :=
    Finset.sum_congr rfl fun j hjj => by
      dsimp only [M]
      rw [ite_eq_left (by
        have := (Finset.mem_Icc.mp hjj).2
        dsimp only [J] at this
        omega)]
  have hl : (∑ j ∈ U, w j * M j) = Cm * ((∑ j ∈ U, w j * bulk j) + (∑ j ∈ U, w j * bd j) +
      (∑ j ∈ U, w j * δ) + B ^ Q * ∑ j ∈ U, w j * (decay j + decay j ^ Q)) := by
    calc
      _ = ∑ j ∈ U, Cm * (w j * bulk j + w j * bd j + w j * δ +
          B ^ Q * (w j * (decay j + decay j ^ Q))) := by
        apply Finset.sum_congr rfl
        intro j hjj
        dsimp only [M]
        rw [ite_eq_right (by
          have := (Finset.mem_Icc.mp hjj).1
          dsimp only [J] at this
          omega)]
        dsimp only [bulk, bd, J]; ring
      _ = _ := by simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  change (∑ j ∈ Finset.Icc J t, w j * M j) ≤ _
  rw [← hu, Finset.sum_union hdis, he, hl]
  have hlate := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add hwb hwbd) hdelt)
    (mul_le_mul_of_nonneg_left hsrc (pow_nonneg hB Q))) hCm
  calc
    _ ≤ Ce * G₁ * B ^ Q * R + Cm * ((2 * (2 + G₁) * D * H + G₃ * (2 + G₁) * D * H) +
        G₁ * δ + B ^ Q * (2 * G₃ * R)) := add_le_add hearly hlate
    _ = _ := by ring
/-- The source bound on an actual target controls both its centered matrix
and its deterministic mean penalty with the same geometric amplitude. -/
theorem transport_target_source_moments {d Q : ℕ} {P : Measure (CoeffSpace d)}
  [IsProbabilityMeasure P] (hQ : 1 ≤ Q) (F : CoeffSpace d → BlockMat d) (hF : SchattenMemLp P (Q
  : ℝ) F)
    (hF0 : ∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat 0) (F a)) (X : CoeffSpace d → ℝ) (hX :
      Integrable X P) (hEX : ∫ a, X a ∂P ≤ 2) (C B : ℝ) (hC : 0 ≤ C) (hB : 1 ≤ B)
    (hbound : ∀ᵐ a ∂P, BlockMatLoewnerLE (F a)
      (blockScale (C * B * X a) (Book.Ch02.blockIdentity d))) :
    let MF := ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F a) α β ∂P)
    BlockMatLoewnerLE (Book.Ch02.blockIdentity d) MF →
      (∀ᵐ a ∂P, absSchattenNorm (Q : ℝ) (blockSub (F a) MF) ≤
        2 * (d : ℝ) * C * B * (X a + 2)) ∧
      meanPenalty Q MF ≤ (1 + 4 * (d : ℝ) * C) ^ Q * B ^ Q := by
  intro MF hIF
  have hQr : 1 ≤ (Q : ℝ) := by exact_mod_cast hQ
  have ht := transport_centered_tail_envelope hQr F hF X hX hEX (C * B) (mul_nonneg hC
    (zero_le_one.trans hB)) hF0 hbound
  refine ⟨by simpa only [mul_assoc] using ht.2, ?_⟩
  have ht0 := blockTrace_identity_sub_nonneg MF (isSymmetricBlockMat_integral hF.symmetric) hIF
  have htr : blockTrace (blockSub MF (Book.Ch02.blockIdentity d)) ≤ 4 * (d : ℝ) * C * B := by
    have he : blockTrace (blockSub MF (Book.Ch02.blockIdentity d)) = blockTrace MF - 2 * (d : ℝ)
      := by
      rw [blockTrace, toFullBlockMat_blockSub_annealed, Matrix.trace_sub,
        toFullBlockMat_blockIdentity, Matrix.trace_one]; simp only [BlockCoord,
        Fintype.card_sum, Fintype.card_fin, Nat.cast_add, two_mul]; rfl
    rw [he]; nlinarith only [ht.1, (show (0 : ℝ) ≤ d from Nat.cast_nonneg d)]
  have hs : 1 + blockTrace (blockSub MF (Book.Ch02.blockIdentity d)) ≤ (1 + 4 * (d : ℝ) * C) * B
    := by
    nlinarith only [htr, hB]
  calc
    _ ≤ (1 + blockTrace (blockSub MF (Book.Ch02.blockIdentity d))) ^ Q := sub_le_self _ (by
      norm_num)
    _ ≤ ((1 + 4 * (d : ℝ) * C) * B) ^ Q := pow_le_pow_left₀ (by linarith only [ht0]) hs Q
    _ = _ := mul_pow _ _ _

/- The geometric fiber estimate and the targetwise Loewner comparison turn the
accumulated penalty envelope into the mean history of the comparison geometry. -/
private theorem transport_profile_mean_history_control (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (qPlus : Mat d) (jStar : ℕ) (n : ℤ) (L : ℕ)
    (I : Finset (ℤ × (Fin d → ℤ)))
    (hIeq : ∀ p, p ∈ I ↔ (p.1 ∈ Set.Icc (jStar : ℤ) (n + (L : ℤ)) ∧
      standardCellCenter p.1 p.2 ∈ centeredCube d (n + (L : ℤ))))
    (hzero : ∀ j : ℤ,
      standardCellCenter j (0 : Fin d → ℤ) ∈ centeredCube d (n + (L : ℤ)))
    (F G : ℤ × (Fin d → ℤ) → CoeffSpace d → BlockMat d) (M : ℤ → ℝ)
    (hM0 : ∀ j ∈ Finset.Icc (jStar : ℤ) (n + (L : ℤ)), 0 ≤ M j)
    (hFmem : ∀ p ∈ I, SchattenMemLp P (bigQ d γ : ℝ) (F p))
    (hGmem : ∀ p ∈ I, SchattenMemLp P (bigQ d γ : ℝ) (G p)) :
    let Q := bigQ d γ
    let t := n + (L : ℤ)
    let MF := fun p => ofFullBlockMat (Matrix.of fun α β =>
      ∫ a, blockMatEntry (F p a) α β ∂P)
    let MG := fun p => ofFullBlockMat (Matrix.of fun α β =>
      ∫ a, blockMatEntry (G p a) α β ∂P)
    (∀ p ∈ I, MF p = relMean P qPlus p.1 t) →
    (∀ p ∈ I, BlockMatLoewnerLE (Book.Ch02.blockIdentity d) (MF p)) →
    (∀ p ∈ I, ∀ᵐ a ∂P, BlockMatLoewnerLE (F p a) (G p a)) →
    (∀ p ∈ I, meanPenalty Q (MG p) ≤ M p.1) →
    (∑ p ∈ I, ((3 : ℝ) ^ (-rhoMax d γ * ((n : ℝ) + L - p.1))) ^
      (Q : ℝ) * meanPenalty Q (MG p)) ≤
        ∑ j ∈ Finset.Icc (jStar : ℤ) t,
          (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) + L - j)) * M j ∧
    meanHistory P γ qPlus (jStar : ℤ) t ≤ (3 : ℝ) ^ ((1 - γ) / 4) *
      ∑ j ∈ Finset.Icc (jStar : ℤ) t,
        (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) + L - j)) * M j := by
  intro Q t MF MG hFmean hIF hFG hMbound
  have hQ : 0 < Q := bigQ_pos d γ hγ
  have hQ1 : 1 ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hdet := transport_pair_mean_bound d hd γ hγ I (jStar : ℤ) t
    (fun p hp => ((hIeq p).mp hp).1) (fun p hp => ((hIeq p).mp hp).2)
    (fun p => meanPenalty Q (MG p)) M hM0 hMbound
  have hjmean (j : ℤ) (hjj : j ∈ Finset.Ico (jStar : ℤ) t) :
      meanPenalty Q (relMean P qPlus j t) ≤ M j := by
    have hp : (j, 0) ∈ I := (hIeq _).mpr
      ⟨⟨(Finset.mem_Ico.mp hjj).1, (Finset.mem_Ico.mp hjj).2.le⟩, hzero j⟩
    have ho : BlockMatLoewnerLE (MF (j, 0)) (MG (j, 0)) :=
      blockMatLoewnerLE_integral ((hFmem _ hp).integrable_entry hQ1)
        ((hGmem _ hp).integrable_entry hQ1) (hFG _ hp)
    have hm := (meanPenalty_mono_and_dominates Q (by omega)
      (isSymmetricBlockMat_integral (hFmem _ hp).symmetric)
      (isSymmetricBlockMat_integral (hGmem _ hp).symmetric) (hIF _ hp) ho).1
    change meanPenalty Q (MF (j, 0)) ≤ meanPenalty Q (MG (j, 0)) at hm
    rw [hFmean _ hp] at hm
    exact hm.trans (hMbound _ hp)
  refine ⟨?_, ?_⟩
  · simpa only [t, Int.cast_add, Int.cast_natCast] using hdet
  · have hhistory := transport_meanHistory_weighted_bound P γ qPlus (jStar : ℤ) t M hM0 hjmean
    simpa only [t, Int.cast_add, Int.cast_natCast] using hhistory

/- Three targetwise envelopes reduce to their scalar moments; the bulk and
boundary contributions then share the same profile growth factor. -/
private theorem transport_profile_fluctuation_moment_control (Q : ℕ) (hQ : 0 < Q)
    {ι : Type*} {α : Type*} [MeasurableSpace α] {P : Measure α}
    (I : Finset ι) (hI : I.Nonempty) (f : ι → α → ℝ)
    (hf0 : ∀ i ∈ I, ∀ᵐ a ∂P, 0 ≤ f i a)
    (hf : ∀ i ∈ I, MemLp (f i) (ENNReal.ofReal (Q : ℝ)) P)
    (Xb Xd Xs : α → ℝ) (hXb0 : ∀ᵐ a ∂P, 0 ≤ Xb a)
    (hXd0 : ∀ᵐ a ∂P, 0 ≤ Xd a) (hXs0 : ∀ᵐ a ∂P, 0 ≤ Xs a)
    (hXb : MemLp Xb (ENNReal.ofReal (Q : ℝ)) P)
    (hXd : MemLp Xd (ENNReal.ofReal (Q : ℝ)) P)
    (hXs : MemLp Xs (ENNReal.ofReal (Q : ℝ)) P) (A D B root Fb Fs Xm grow H R Cb Cd a : ℝ)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hCb : 0 ≤ Cb) (hCd : 0 ≤ Cd)
    (hH : 0 ≤ H) (hB : 0 ≤ B) (hroot : 0 ≤ root)
    (hXbm : (∫ x, Xb x ^ Q ∂P) ≤ Cb * (3 : ℝ) ^ (a) * H)
    (hXdm : (∫ x, Xd x ^ Q ∂P) ≤ Cd * (3 : ℝ) ^ (a) * H)
    (hXsm : (∫ x, Xs x ^ Q ∂P) ≤ Xm)
    (hrootpow : (D * B * root) ^ Q = D ^ Q * B ^ Q * R)
    (hFb : Fb = (3 : ℝ) ^ Q * A ^ Q * (Cb + Cd))
    (hFs : Fs = (3 : ℝ) ^ Q * D ^ Q * Xm)
    (hdecay : (3 : ℝ) ^ a ≤ grow)
    (hbound : ∀ i ∈ I, ∀ᵐ x ∂P,
      f i x ≤ A * (Xb x + Xd x) + (D * B * root) * Xs x) :
    (∫ x, (⨆ i ∈ (I : Set ι), f i x) ^ (Q : ℝ) ∂P) ≤
      Fb * grow * H + Fs * B ^ Q * R := by
  have hthree := transport_joint_three_envelopes Q hQ I hI f hf0 hf Xb Xd Xs hXb0 hXd0 hXs0
    hXb hXd hXs A (D * B * root) hA (by positivity) hbound
  calc
    _ ≤ (3 : ℝ) ^ Q * (A ^ Q * ((∫ x, Xb x ^ Q ∂P) + ∫ x, Xd x ^ Q ∂P) +
        (D * B * root) ^ Q * ∫ x, Xs x ^ Q ∂P) := hthree
    _ ≤ (3 : ℝ) ^ Q * (A ^ Q * (Cb * grow * H + Cd * grow * H) +
        (D * B * root) ^ Q * Xm) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (add_le_add
          (hXbm.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hdecay hCb) hH))
          (hXdm.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hdecay hCd) hH)))
          (pow_nonneg hA Q)
      · exact mul_le_mul_of_nonneg_left hXsm (by positivity)
    _ = ((3 : ℝ) ^ Q * A ^ Q * (Cb + Cd)) * grow * H +
        ((3 : ℝ) ^ Q * D ^ Q * Xm) * B ^ Q * R := by rw [hrootpow]; ring
    _ = _ := by rw [← hFb, ← hFs]

/- The weighted Loewner gap compares the reindexed cell history with the
centered comparison field and its deterministic mean penalty. -/
private theorem transport_profile_fluctuation_history_control {d Q : ℕ}
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] (γ : ℝ) (qPlus : Mat d)
    (jStar : ℕ) (t : ℤ) (I : Finset (ℤ × (Fin d → ℤ))) (hI : I.Nonempty)
    (weight : (ℤ × (Fin d → ℤ)) → ℝ) (hweight : ∀ p, 0 ≤ weight p)
    (G : (ℤ × (Fin d → ℤ)) → CoeffSpace d → BlockMat d) (hQ : 2 ≤ Q)
    (Fb Sm : ℝ) :
    let F := fun (p : ℤ × (Fin d → ℤ)) a => normalizedBlock
      (coarseBlock (adaptedCellAtCenter qPlus p.1 p.2) a) (adaptedMean P qPlus t)
    let MF := fun p => ofFullBlockMat (Matrix.of fun α β =>
      ∫ a, blockMatEntry (F p a) α β ∂P)
    let MG := fun p => ofFullBlockMat (Matrix.of fun α β =>
      ∫ a, blockMatEntry (G p a) α β ∂P)
    let Ag := (2 : ℝ) ^ ((Q : ℝ) - 1) * (1 + (2 * (d : ℝ)) ^ (Q : ℝ)⁻¹) ^ (Q : ℝ)
    let Bg := (2 : ℝ) ^ (2 * (Q : ℝ) - 1) * (1 + (d : ℝ) ^ (1 - (Q : ℝ)⁻¹)) ^ (Q : ℝ)
    (∀ p ∈ I, SchattenMemLp P (Q : ℝ) (F p)) →
    (∀ p ∈ I, SchattenMemLp P (Q : ℝ) (G p)) →
    (∀ p ∈ I, ∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat 0) (F p a)) →
    (∀ p ∈ I, ∀ᵐ a ∂P, BlockMatLoewnerLE (F p a) (G p a)) →
    (∀ p ∈ I, BlockMatLoewnerLE (Book.Ch02.blockIdentity d) (MF p)) →
    (∀ p ∈ I, MF p = relMean P qPlus p.1 t) →
    fluctuationHistory P γ qPlus jStar t =
      (∫ a, (⨆ p ∈ (I : Set (ℤ × (Fin d → ℤ))), weight p *
        blockOpNorm (normalizedFluctuation P qPlus p.1 t
          (adaptedCellCenter qPlus p.1 p.2) a)) ^ (Q : ℝ) ∂P) →
    (∫ a, (⨆ p ∈ (I : Set (ℤ × (Fin d → ℤ))), weight p *
      absSchattenNorm (Q : ℝ) (blockSub (G p a) (MG p))) ^ (Q : ℝ) ∂P) ≤ Fb →
    (∑ p ∈ I, weight p ^ (Q : ℝ) * meanPenalty Q (MG p)) ≤ Sm →
    fluctuationHistory P γ qPlus jStar t ≤ Ag * Fb + Bg * Sm := by
  intro F MF MG Ag Bg hF hG hFpos hFG hmean hFmean hhist hflucMoment hdet
  have hcenterF (p) (hp : p ∈ I) (a) :
      normalizedFluctuation P qPlus p.1 t (adaptedCellCenter qPlus p.1 p.2) a =
        blockSub (F p a) (MF p) := by
    rw [hFmean p hp]
    exact normalizedBlock_blockSub _ _ _
  have hSup (a) :
      (⨆ p ∈ (I : Set (ℤ × (Fin d → ℤ))), weight p *
        blockOpNorm (normalizedFluctuation P qPlus p.1 t
          (adaptedCellCenter qPlus p.1 p.2) a)) =
      ⨆ p ∈ (I : Set (ℤ × (Fin d → ℤ))),
        weight p * blockOpNorm (blockSub (F p a) (MF p)) := by
    apply iSup_congr
    intro p
    apply iSup_congr
    intro hp
    rw [hcenterF p hp]
  have hleft : fluctuationHistory P γ qPlus jStar t =
      ∫ a, (⨆ p ∈ (I : Set (ℤ × (Fin d → ℤ))),
        weight p * blockOpNorm (blockSub (F p a) (MF p))) ^ (Q : ℝ) ∂P := by
    rw [hhist]
    apply integral_congr_ae
    exact ae_of_all P fun a => congrArg (fun x : ℝ => x ^ (Q : ℝ)) (hSup a)
  have hgap := transport_weighted_gap_mean Q hQ I hI weight hweight F G hF hG hFpos hFG hmean
  exact hleft.le.trans (hgap.trans
    (add_le_add (mul_le_mul_of_nonneg_left hflucMoment (by
      change 0 ≤ (2 : ℝ) ^ ((Q : ℝ) - 1) *
        (1 + (2 * (d : ℝ)) ^ (Q : ℝ)⁻¹) ^ (Q : ℝ)
      positivity))
      (mul_le_mul_of_nonneg_left hdet (by
        change 0 ≤ (2 : ℝ) ^ (2 * (Q : ℝ) - 1) *
          (1 + (d : ℝ) ^ (1 - (Q : ℝ)⁻¹)) ^ (Q : ℝ)
        positivity))))

/-- The reindexed history provides centered boxes and hence a centered cell family. -/
private theorem transport_reindexed_centered_cells (d : ℕ) (qPlus : Mat d)
    (hqPlus : IsUnit qPlus) (jStar : ℕ) (t : ℤ)
    (I : Finset (ℤ × (Fin d → ℤ)))
    (hIeq : ∀ p, p ∈ I ↔ (p.1 ∈ Set.Icc (jStar : ℤ) t ∧
      standardCellCenter p.1 p.2 ∈ centeredCube d t))
    (htW : adaptedCell qPlus t ⊆ centeredCube d (2 * (jStar : ℤ))) :
    (∀ j : ℤ, standardCellCenter j (0 : Fin d → ℤ) ∈ centeredCube d t) ∧
      (∀ p, p ∈ I → standardCellCenter p.1 p.2 ∈ centeredCube d t) ∧
      (∀ p, p ∈ I →
        adaptedCellAtCenter qPlus p.1 p.2 ⊆ centeredCube d (2 * (jStar : ℤ))) := by
  have hzero (j : ℤ) : standardCellCenter j (0 : Fin d → ℤ) ∈ centeredCube d t := by
    rw [Recurrence.mem_centeredCube_iff]
    intro i
    simp only [HighContrast.standardCellCenter, Pi.zero_apply, Int.cast_zero, mul_zero]
    have hpt : (0 : ℝ) < 3 ^ t := by positivity
    constructor <;> nlinarith only [hpt]
  have hcenter (p) (hp : p ∈ I) : standardCellCenter p.1 p.2 ∈ centeredCube d t :=
    ((hIeq p).mp hp).2
  have hCell (p) (hp : p ∈ I) :
      adaptedCellAtCenter qPlus p.1 p.2 ⊆ centeredCube d (2 * (jStar : ℤ)) := by
    have hpt := ((hIeq p).mp hp).1.2
    have he : p.1 + ((t - p.1).toNat : ℤ) = t := by omega
    have hh := (aligned_adapted_partition qPlus hqPlus p.1 (t - p.1).toNat).1 p.2
      (by simpa only [he] using! ((hIeq p).mp hp).2)
    rw [he] at hh
    exact hh.trans htW
  exact ⟨hzero, hcenter, hCell⟩

/-- Positivity of the profile comparison exponents and coefficients. -/
private theorem transport_profile_coefficient_signs (d : ℕ) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (Cf Ce Cb Cd Cm : ℝ)
    (hCf : 0 ≤ Cf) (hCe : 0 ≤ Ce) (hCb : 0 ≤ Cb) (hCd : 0 ≤ Cd) (hCm : 0 ≤ Cm) :
    let Q := bigQ d γ
    let a := (1 - γ) / 4
    let G₁ := 1 / (1 - (3 : ℝ) ^ (-a))
    let G₃ := 1 / (1 - (3 : ℝ) ^ (-(3 * (1 - γ) / 4)))
    let A := (4 / 3 : ℝ) * (2 * (d : ℝ)) ^ (Q : ℝ)⁻¹
    let D := (2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ * (2 * (d : ℝ)) * Cf + 2 * (d : ℝ) * Ce
    let Em := (1 + 4 * (d : ℝ) * Ce) ^ Q
    let Xm := (3 : ℝ) ^ Q * (2 * 2 ^ Q + 4 ^ Q)
    let Fb := (3 : ℝ) ^ Q * A ^ Q * (Cb + Cd)
    let Fs := (3 : ℝ) ^ Q * D ^ Q * Xm
    let Mb := Cm * (2 + G₃) * (2 + G₁)
    let Md := Cm * G₁
    let Ms := Cm * 2 * G₃ + Em * G₁
    let Ag := (2 : ℝ) ^ ((Q : ℝ) - 1) * (1 + (2 * (d : ℝ)) ^ (Q : ℝ)⁻¹) ^ (Q : ℝ)
    let Bg := (2 : ℝ) ^ (2 * (Q : ℝ) - 1) * (1 + (d : ℝ) ^ (1 - (Q : ℝ)⁻¹)) ^ (Q : ℝ)
    let C := Ag * (Fb + Fs) + (Bg + (3 : ℝ) ^ a) * (Mb + Md + Ms) + 1
    0 < Q ∧ 1 ≤ (Q : ℝ) ∧ 2 ≤ Q ∧ 0 < a ∧
      0 ≤ G₁ ∧ 0 ≤ G₃ ∧ 0 ≤ A ∧ 0 ≤ D ∧ 0 ≤ Em ∧ 0 ≤ Fb ∧ 0 ≤ Fs ∧
      0 ≤ Mb ∧ 0 ≤ Md ∧ 0 ≤ Ms ∧ 0 ≤ Ag ∧ 0 ≤ Bg ∧ 0 < C := by
  have hQ : 0 < bigQ d γ := bigQ_pos d γ hγ
  have hQ1 : 1 ≤ (bigQ d γ : ℝ) := by exact_mod_cast hQ
  have hQ2 : 2 ≤ bigQ d γ := bigQ_two_le d γ hγ
  have ha : 0 < (1 - γ) / 4 := by linarith only [hγ.2]
  let Q := bigQ d γ
  let a := (1 - γ) / 4
  let G₁ := 1 / (1 - (3 : ℝ) ^ (-a))
  let G₃ := 1 / (1 - (3 : ℝ) ^ (-(3 * (1 - γ) / 4)))
  let A := (4 / 3 : ℝ) * (2 * (d : ℝ)) ^ (Q : ℝ)⁻¹
  let D := (2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ * (2 * (d : ℝ)) * Cf + 2 * (d : ℝ) * Ce
  let Em := (1 + 4 * (d : ℝ) * Ce) ^ Q
  let Xm := (3 : ℝ) ^ Q * (2 * 2 ^ Q + 4 ^ Q)
  let Fb := (3 : ℝ) ^ Q * A ^ Q * (Cb + Cd)
  let Fs := (3 : ℝ) ^ Q * D ^ Q * Xm
  let Mb := Cm * (2 + G₃) * (2 + G₁)
  let Md := Cm * G₁
  let Ms := Cm * 2 * G₃ + Em * G₁
  let Ag := (2 : ℝ) ^ ((Q : ℝ) - 1) * (1 + (2 * (d : ℝ)) ^ (Q : ℝ)⁻¹) ^ (Q : ℝ)
  let Bg := (2 : ℝ) ^ (2 * (Q : ℝ) - 1) * (1 + (d : ℝ) ^ (1 - (Q : ℝ)⁻¹)) ^ (Q : ℝ)
  let C := Ag * (Fb + Fs) + (Bg + (3 : ℝ) ^ a) * (Mb + Md + Ms) + 1
  have hG₁ : 0 ≤ G₁ := (one_div_pos.mpr
    (transport_geometric_Icc a ha 0 0).1).le
  have hG₃ : 0 ≤ G₃ := (one_div_pos.mpr (transport_geometric_Icc (3 * (1 - γ) / 4)
    (by linarith only [hγ.2]) 0 0).1).le
  have hA : 0 ≤ A := by dsimp only [A]; exact mul_nonneg (by norm_num) (Real.rpow_nonneg
    (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) _)
  have hD : 0 ≤ D := by dsimp only [D]; exact add_nonneg (mul_nonneg (mul_nonneg
    (Real.rpow_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) _) (mul_nonneg (by
    norm_num) (Nat.cast_nonneg d))) hCf) (mul_nonneg (mul_nonneg (by norm_num)
    (Nat.cast_nonneg d)) hCe)
  have hEm : 0 ≤ Em := by dsimp only [Em]; exact pow_nonneg (add_nonneg (by norm_num)
    (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hCe)) Q
  have hFb : 0 ≤ Fb := by dsimp only [Fb]; exact mul_nonneg (mul_nonneg (pow_nonneg (by
    norm_num) Q) (pow_nonneg hA Q)) (add_nonneg hCb hCd)
  have hFs : 0 ≤ Fs := by dsimp only [Fs, Xm]; exact mul_nonneg (mul_nonneg (pow_nonneg (by
    norm_num) Q) (pow_nonneg hD Q)) (mul_nonneg (pow_nonneg (by norm_num) Q) (add_nonneg
    (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) Q)) (pow_nonneg (by norm_num) Q)))
  have hMb : 0 ≤ Mb := by
    dsimp only [Mb]
    exact mul_nonneg (mul_nonneg hCm (add_nonneg (by norm_num) hG₃))
      (add_nonneg (by norm_num) hG₁)
  have hMd : 0 ≤ Md := mul_nonneg hCm hG₁
  have hMs : 0 ≤ Ms := by
    dsimp only [Ms]
    exact add_nonneg (mul_nonneg (mul_nonneg hCm (by norm_num)) hG₃) (mul_nonneg hEm hG₁)
  have hAg : 0 ≤ Ag := by
    dsimp only [Ag]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (add_nonneg (by norm_num) (Real.rpow_nonneg (mul_nonneg (by norm_num)
        (Nat.cast_nonneg d)) _)) _)
  have hBg : 0 ≤ Bg := by
    dsimp only [Bg]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (add_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg d) _)) _)
  have hC : 0 < C := by
    dsimp only [C]
    exact lt_of_lt_of_le (by norm_num)
      (le_add_of_nonneg_left (add_nonneg (mul_nonneg hAg (add_nonneg hFb hFs)) (mul_nonneg
        (add_nonneg hBg (three_rpow_nonneg a)) (add_nonneg (add_nonneg hMb hMd) hMs))))
  exact ⟨hQ, hQ1, hQ2, ha, hG₁, hG₃, hA, hD, hEm, hFb, hFs, hMb, hMd, hMs, hAg, hBg, hC⟩

/-- Weighted maxima of the bulk and boundary cell families retain their source moments. -/
private theorem transport_weighted_V_envelopes {d Q : ℕ} {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (jStar : ℕ) (hQ1 : 1 ≤ (Q : ℝ))
    (U : Finset (ℤ × (Fin d → ℤ))) (hU : U.Nonempty)
    (V : (ℤ × (Fin d → ℤ)) → ℤ → CoeffSpace d → BlockMat d)
    (hVmem : ∀ p r, SchattenMemLp P (Q : ℝ) (V p r))
    (weight : (ℤ × (Fin d → ℤ)) → ℝ) (hweight : ∀ p, 0 ≤ weight p) (cap : ℤ → ℤ)
    (X Y : CoeffSpace d → ℝ) (hX0 : ∀ᵐ a ∂P, 0 ≤ X a) (hY0 : ∀ᵐ a ∂P, 0 ≤ Y a)
    (hX : MemLp X (ENNReal.ofReal (Q : ℝ)) P)
    (hY : MemLp Y (ENNReal.ofReal (Q : ℝ)) P)
    (hXN : eLpNorm X (ENNReal.ofReal (Q : ℝ)) P ≤ ENNReal.ofReal 2)
    (hYN : eLpNorm Y (ENNReal.ofReal (Q : ℝ)) P ≤ ENNReal.ofReal 2) :
    let fb := fun p a => weight p * absSchattenNorm (Q : ℝ) (V p (cap p.1) a)
    let fd := fun p a => weight p * ∑ r ∈ Finset.Icc (jStar : ℤ) (cap p.1 - 1),
      absSchattenNorm (Q : ℝ) (V p r a)
    let Xb := fun a => ⨆ p ∈ (U : Set (ℤ × (Fin d → ℤ))), fb p a
    let Xd := fun a => ⨆ p ∈ (U : Set (ℤ × (Fin d → ℤ))), fd p a
    let Xs := fun a => X a + Y a + 4
    (∀ p, ∀ᵐ a ∂P, 0 ≤ fb p a) ∧ (∀ p, ∀ᵐ a ∂P, 0 ≤ fd p a) ∧
    MemLp Xb (ENNReal.ofReal (Q : ℝ)) P ∧ MemLp Xd (ENNReal.ofReal (Q : ℝ)) P ∧
    (∀ᵐ a ∂P, 0 ≤ Xb a) ∧ (∀ᵐ a ∂P, 0 ≤ Xd a) ∧
    MemLp Xs (ENNReal.ofReal (Q : ℝ)) P ∧ (∀ᵐ a ∂P, 0 ≤ Xs a) ∧
    (∫ a, Xs a ^ Q ∂P) ≤ (3 : ℝ) ^ Q * (2 * 2 ^ Q + 4 ^ Q) ∧
    (∀ p ∈ U, ∀ᵐ a ∂P, fb p a ≤ Xb a) ∧ (∀ p ∈ U, ∀ᵐ a ∂P, fd p a ≤ Xd a) := by
  classical
  intro fb fd Xb Xd Xs
  have hV0 (p r) : ∀ᵐ a ∂P, 0 ≤ absSchattenNorm (Q : ℝ) (V p r a) :=
    (hVmem p r).symmetric.mono fun _ ha => absSchattenNorm_nonneg
      ((toFullBlockMat_isHermitian_iff _).2 ha) hQ1
  have hfb0 (p) : ∀ᵐ a ∂P, 0 ≤ fb p a :=
    (hV0 p (cap p.1)).mono fun _ ha => mul_nonneg (hweight p) ha
  have hfd0 (p) : ∀ᵐ a ∂P, 0 ≤ fd p a :=
    ((Filter.eventually_all_finset (Finset.Icc (jStar : ℤ) (cap p.1 - 1))).mpr
      (fun r _ => hV0 p r)).mono fun _ ha => mul_nonneg (hweight p) (Finset.sum_nonneg ha)
  have hfb (p) : MemLp (fb p) (ENNReal.ofReal (Q : ℝ)) P :=
    ((hVmem p (cap p.1)).memLp_absSchattenNorm hQ1).const_mul _
  have hfd (p) : MemLp (fd p) (ENNReal.ofReal (Q : ℝ)) P :=
    (memLp_finsetSum _ (fun r _ => (hVmem p r).memLp_absSchattenNorm hQ1)).const_mul _
  have hXb : MemLp Xb (ENNReal.ofReal (Q : ℝ)) P :=
    weightedMax_memLp U hU fb (fun p _ => hfb0 p) (fun p _ => hfb p)
  have hXd : MemLp Xd (ENNReal.ofReal (Q : ℝ)) P :=
    weightedMax_memLp U hU fd (fun p _ => hfd0 p) (fun p _ => hfd p)
  have hXb0 := weightedMax_nonneg U hU fb (fun p _ => hfb0 p)
  have hXd0 := weightedMax_nonneg U hU fd (fun p _ => hfd0 p)
  have hXs : MemLp Xs (ENNReal.ofReal (Q : ℝ)) P := (hX.add hY).add (memLp_const 4)
  have hXs0 : ∀ᵐ a ∂P, 0 ≤ Xs a := by
    filter_upwards [hX0, hY0] with aa hxa hya
    exact add_nonneg (add_nonneg hxa hya) (by norm_num)
  have hXsm : (∫ a, Xs a ^ Q ∂P) ≤ (3 : ℝ) ^ Q * (2 * 2 ^ Q + 4 ^ Q) := by
    have hQ : 0 < Q := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hQ1)
    exact transport_source_sum_moment Q hQ X Y hX0 hY0 hX hY hXN hYN
  have hfbMax (p) (hp : p ∈ U) : ∀ᵐ a ∂P, fb p a ≤ Xb a := by
    filter_upwards [(Filter.eventually_all_finset U).mpr (fun p _ => hfb0 p)] with aa haa
    dsimp only [Xb]; rw [iSup_mem_finset_eq_finset_sup U hU _ haa]
    exact Finset.le_sup' (fun p => fb p aa) hp
  have hfdMax (p) (hp : p ∈ U) : ∀ᵐ a ∂P, fd p a ≤ Xd a := by
    filter_upwards [(Filter.eventually_all_finset U).mpr (fun p _ => hfd0 p)] with aa haa
    dsimp only [Xd]; rw [iSup_mem_finset_eq_finset_sup U hU _ haa]
    exact Finset.le_sup' (fun p => fd p aa) hp
  exact ⟨hfb0, hfd0, hXb, hXd, hXb0, hXd0, hXs, hXs0, hXsm, hfbMax, hfdMax⟩

/-- Combine early-source and late-Whitney centered bounds into one weighted envelope. -/
private theorem transport_profile_pointwise_weighted_fluctuation_bound
    {d : ℕ} {P : Measure (CoeffSpace d)}
    (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (jStar : ℕ) (k n : ℤ) (L : ℕ) (hk : (jStar : ℤ) ≤ k) (hkn : k ≤ n)
    (I : Finset (ℤ × (Fin d → ℤ)))
    (hgen : ∀ p ∈ I, p.1 ∈ Set.Icc (jStar : ℤ) (n + (L : ℤ)))
    (F Graw : (ℤ × (Fin d → ℤ)) → CoeffSpace d → BlockMat d)
    (V : (ℤ × (Fin d → ℤ)) → ℤ → CoeffSpace d → BlockMat d) (cap : ℤ → ℤ)
    (Xb Xd X Y : CoeffSpace d → ℝ) (A Cf Ce B Bf : ℝ)
    (hA : 0 ≤ A) (hCf : 0 ≤ Cf) (hCe : 0 ≤ Ce) (hB : 0 ≤ B)
    (hBf0 : 0 ≤ Bf) (hBf : Bf ≤ B) (hX0 : ∀ a, 0 ≤ X a) (hY0 : ∀ a, 0 ≤ Y a)
    (hXb0 : ∀ᵐ a ∂P, 0 ≤ Xb a) (hXd0 : ∀ᵐ a ∂P, 0 ≤ Xd a) :
    let Q := bigQ d γ
    let U := I.filter (fun p => (jStar : ℤ) + L ≤ p.1)
    let weight := fun p : ℤ × (Fin d → ℤ) =>
      (3 : ℝ) ^ (-rhoMax d γ * ((n : ℝ) + L - p.1))
    let G := fun p a => if p.1 < (jStar : ℤ) + L then F p a else Graw p a
    let MF := fun p => ofFullBlockMat (Matrix.of fun α β =>
      ∫ a, blockMatEntry (F p a) α β ∂P)
    let MG := fun p => ofFullBlockMat (Matrix.of fun α β =>
      ∫ a, blockMatEntry (G p a) α β ∂P)
    let MGraw := fun p => ofFullBlockMat (Matrix.of fun α β =>
      ∫ a, blockMatEntry (Graw p a) α β ∂P)
    let fb := fun p a => weight p * absSchattenNorm (Q : ℝ) (V p (cap p.1) a)
    let fd := fun p a => weight p * ∑ r ∈ Finset.Icc (jStar : ℤ) (cap p.1 - 1),
      absSchattenNorm (Q : ℝ) (V p r a)
    let Xs := fun a => X a + Y a + 4
    let root := (3 : ℝ) ^ (-(((1 - γ) / 4) / (Q : ℝ)) * ((n : ℝ) - jStar))
    let D := (2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ * (2 * (d : ℝ)) * Cf + 2 * (d : ℝ) * Ce
    (∀ p ∈ I, ∀ᵐ a ∂P,
      absSchattenNorm (Q : ℝ) (blockSub (F p a) (MF p)) ≤
        2 * (d : ℝ) * Ce * B * (Y a + 2)) →
    (∀ p ∈ U, ∀ᵐ a ∂P,
      absSchattenNorm (Q : ℝ) (blockSub (Graw p a) (MGraw p)) ≤
        A * (absSchattenNorm (Q : ℝ) (V p (cap p.1) a) +
          ∑ r ∈ Finset.Icc (jStar : ℤ) (cap p.1 - 1), absSchattenNorm (Q : ℝ) (V p r a)) +
        ((2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ * (2 * (d : ℝ)) * Cf) * Bf *
          (3 : ℝ) ^ (-(1 - γ) * ((p.1 : ℝ) - jStar)) * (X a + 2)) →
    (∀ p ∈ U, ∀ᵐ a ∂P, fb p a ≤ Xb a) →
    (∀ p ∈ U, ∀ᵐ a ∂P, fd p a ≤ Xd a) →
    ∀ p ∈ I, ∀ᵐ a ∂P,
      weight p * absSchattenNorm (Q : ℝ) (blockSub (G p a) (MG p)) ≤
        A * (Xb a + Xd a) + (D * B * root) * Xs a := by
  classical
  intro Q U weight G MF MG MGraw fb fd Xs root D hEarly hLate hfbMax hfdMax p hp
  have hroot : 0 ≤ root := three_rpow_nonneg _
  have hDf : (2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ * (2 * (d : ℝ)) * Cf ≤ D :=
    le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hCe)
  have hDe : 2 * (d : ℝ) * Ce ≤ D := le_add_of_nonneg_left (mul_nonneg (mul_nonneg
    (Real.rpow_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) _)
    (mul_nonneg (by norm_num) (Nat.cast_nonneg d))) hCf)
  have hw := transport_source_max_weight d hd γ hγ (jStar : ℤ) n p.1 L (hk.trans hkn)
    (hgen p hp)
  by_cases he : p.1 < (jStar : ℤ) + L
  · have hce : ∀ᵐ a ∂P, absSchattenNorm (Q : ℝ) (blockSub (G p a) (MG p)) ≤
        2 * (d : ℝ) * Ce * B * (Y a + 2) := by
      simpa only [MG, G, ite_eq_left he] using hEarly p hp
    filter_upwards [hce, hXb0, hXd0] with a ha hba hda
    have hYa : 0 ≤ Y a + 2 := by linarith only [hY0 a]
    have hYs : Y a + 2 ≤ Xs a := by dsimp only [Xs]; linarith only [hX0 a]
    calc
      _ ≤ weight p * (2 * (d : ℝ) * Ce * B * (Y a + 2)) :=
        mul_le_mul_of_nonneg_left ha (three_rpow_nonneg _)
      _ = (2 * (d : ℝ) * Ce) * B * weight p * (Y a + 2) := by ring
      _ ≤ D * B * root * Xs a := by gcongr; exact hw.1 he
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hA (add_nonneg hba hda))
  · have hpU : p ∈ U := Finset.mem_filter.mpr ⟨hp, by omega⟩
    have hce : ∀ᵐ a ∂P, absSchattenNorm (Q : ℝ) (blockSub (G p a) (MG p)) ≤
        A * (absSchattenNorm (Q : ℝ) (V p (cap p.1) a) +
          ∑ r ∈ Finset.Icc (jStar : ℤ) (cap p.1 - 1), absSchattenNorm (Q : ℝ) (V p r a)) +
        ((2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ * (2 * (d : ℝ)) * Cf) * Bf *
          (3 : ℝ) ^ (-(1 - γ) * ((p.1 : ℝ) - jStar)) * (X a + 2) := by
      simpa only [MG, G, ite_eq_right he] using hLate p hpU
    filter_upwards [hce, hfbMax p hpU, hfdMax p hpU] with a ha hba hda
    have hXa : 0 ≤ X a + 2 := by linarith only [hX0 a]
    have hXs' : X a + 2 ≤ Xs a := by dsimp only [Xs]; linarith only [hY0 a]
    calc
      _ ≤ weight p * (A * (absSchattenNorm (Q : ℝ) (V p (cap p.1) a) +
          ∑ r ∈ Finset.Icc (jStar : ℤ) (cap p.1 - 1), absSchattenNorm (Q : ℝ) (V p r a)) +
          ((2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ * (2 * (d : ℝ)) * Cf) * Bf *
            (3 : ℝ) ^ (-(1 - γ) * ((p.1 : ℝ) - jStar)) * (X a + 2)) :=
        mul_le_mul_of_nonneg_left ha (three_rpow_nonneg _)
      _ = A * (fb p a + fd p a) +
          ((2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ * (2 * (d : ℝ)) * Cf) * Bf *
            (weight p * (3 : ℝ) ^ (-(1 - γ) * ((p.1 : ℝ) - jStar))) * (X a + 2) := by
        dsimp only [fb, fd]
        ring
      _ ≤ A * (Xb a + Xd a) + (D * B * root) * Xs a := by
        apply add_le_add (mul_le_mul_of_nonneg_left (add_le_add hba hda) hA)
        gcongr
        exact hw.2.1

/-- The early source and fine tail amplitudes fit inside the printed source bracket. -/
private theorem transport_profile_source_amplitudes (β K u v : ℝ)
    (hβ : 0 ≤ β) (hK : 0 ≤ K) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    let B := 1 + β * (K * u * v + v ^ 2)
    let Bf := β * K * u * v
    1 ≤ B ∧ 0 ≤ Bf ∧ Bf ≤ B ∧ β * v ^ 2 ≤ B := by
  intro B Bf
  have hb := transport_profile_source_bracket hβ hK hu hv
  exact ⟨hb.1, mul_nonneg (mul_nonneg (mul_nonneg hβ hK) hu) hv, hb.2⟩

/-- Selecting the early field or its ordered Whitney comparison preserves integrability. -/
private theorem transport_profile_selected_ordered_field {d Q : ℕ}
    {P : Measure (CoeffSpace d)} (jStar L : ℕ)
    (I : Finset (ℤ × (Fin d → ℤ)))
    (F Graw : (ℤ × (Fin d → ℤ)) → CoeffSpace d → BlockMat d)
    (hFmem : ∀ p ∈ I, SchattenMemLp P (Q : ℝ) (F p))
    (hGrawmem : ∀ p ∈ I, SchattenMemLp P (Q : ℝ) (Graw p))
    (hFGraw : ∀ p ∈ I, ∀ᵐ a ∂P, BlockMatLoewnerLE (F p a) (Graw p a)) :
    let G := fun p a => if p.1 < (jStar : ℤ) + L then F p a else Graw p a
    (∀ p ∈ I, SchattenMemLp P (Q : ℝ) (G p)) ∧
    (∀ p ∈ I, ∀ᵐ a ∂P, BlockMatLoewnerLE (F p a) (G p a)) := by
  classical
  intro G
  constructor
  · intro p hp
    by_cases he : p.1 < (jStar : ℤ) + L
    · simpa only [G, ite_eq_left he] using hFmem p hp
    · simpa only [G, ite_eq_right he] using hGrawmem p hp
  · intro p hp
    by_cases he : p.1 < (jStar : ℤ) + L
    · exact ae_of_all P fun _ => by
        simp only [G, ite_eq_left he]
        exact fun _ => le_rfl
    · simpa only [G, ite_eq_right he] using hFGraw p hp

/-- A larger source amplitude controls the mean of the selected early/late field. -/
private theorem transport_profile_selected_mean_bound {d Q : ℕ}
    {P : Measure (CoeffSpace d)} (jStar L : ℕ)
    (I : Finset (ℤ × (Fin d → ℤ)))
    (F Graw : (ℤ × (Fin d → ℤ)) → CoeffSpace d → BlockMat d)
    (base decay : ℤ → ℝ) (Cm Em B Bf : ℝ) (hCm : 0 ≤ Cm)
    (hBf0 : 0 ≤ Bf) (hBf : Bf ≤ B) (hdecay : ∀ j, 0 ≤ decay j) :
    let U := I.filter (fun p => (jStar : ℤ) + L ≤ p.1)
    let G := fun p a => if p.1 < (jStar : ℤ) + L then F p a else Graw p a
    let MF := fun p => ofFullBlockMat (Matrix.of fun α β =>
      ∫ a, blockMatEntry (F p a) α β ∂P)
    let MGraw := fun p => ofFullBlockMat (Matrix.of fun α β =>
      ∫ a, blockMatEntry (Graw p a) α β ∂P)
    let MG := fun p => ofFullBlockMat (Matrix.of fun α β =>
      ∫ a, blockMatEntry (G p a) α β ∂P)
    let M := fun j => if j < (jStar : ℤ) + L then Em * B ^ Q else
      Cm * (base j + B ^ Q * (decay j + decay j ^ Q))
    (∀ p ∈ I, meanPenalty Q (MF p) ≤ Em * B ^ Q) →
    (∀ p ∈ U, meanPenalty Q (MGraw p) ≤
      Cm * (base p.1 + Bf ^ Q * (decay p.1 + decay p.1 ^ Q))) →
    ∀ p ∈ I, meanPenalty Q (MG p) ≤ M p.1 := by
  classical
  intro U G MF MGraw MG M hEarly hLate p hp
  by_cases he : p.1 < (jStar : ℤ) + L
  · simpa only [MG, G, M, ite_eq_left he] using hEarly p hp
  · have hpU : p ∈ U := Finset.mem_filter.mpr ⟨hp, by omega⟩
    have hm := (hLate p hpU).trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hBf0 hBf Q)
        (add_nonneg (hdecay p.1) (pow_nonneg (hdecay p.1) Q)))) hCm)
    simpa only [MG, G, M, ite_eq_right he] using hm

/-- The fluctuation and mean coefficients share one constant for all three contributions. -/
private theorem transport_profile_scalar_accumulation
    (Ag Bg Fb Fs Mb Md Ms a growthProfile error source Sm fluctuation mean : ℝ)
    (hAg : 0 ≤ Ag) (hBg : 0 ≤ Bg) (hFb : 0 ≤ Fb) (hFs : 0 ≤ Fs)
    (hMb : 0 ≤ Mb) (hMd : 0 ≤ Md) (hMs : 0 ≤ Ms)
    (hgrowth : 0 ≤ growthProfile) (herror : 0 ≤ error) (hsource : 0 ≤ source)
    (hSm : Sm ≤ Mb * growthProfile + Md * error + Ms * source)
    (hfluctuation : fluctuation ≤ Ag * (Fb * growthProfile + Fs * source) + Bg * Sm)
    (hmean : mean ≤ (3 : ℝ) ^ a * Sm) :
    let C := Ag * (Fb + Fs) + (Bg + (3 : ℝ) ^ a) * (Mb + Md + Ms) + 1
    fluctuation + mean ≤ C * growthProfile + C * error + C * source := by
  intro C
  have hT : 0 ≤ Bg + (3 : ℝ) ^ a := add_nonneg hBg (three_rpow_nonneg a)
  have hC₁ : Ag * Fb + (Bg + (3 : ℝ) ^ a) * Mb ≤ C := by
    dsimp only [C]; nlinarith only [mul_nonneg hAg hFs, mul_nonneg hT hMd, mul_nonneg hT hMs]
  have hC₂ : (Bg + (3 : ℝ) ^ a) * Md ≤ C := by
    dsimp only [C]; nlinarith only [mul_nonneg hAg (add_nonneg hFb hFs), mul_nonneg hT hMb,
      mul_nonneg hT hMs]
  have hC₃ : Ag * Fs + (Bg + (3 : ℝ) ^ a) * Ms ≤ C := by
    dsimp only [C]; nlinarith only [mul_nonneg hAg hFb, mul_nonneg hT hMb, mul_nonneg hT hMd]
  calc
    _ ≤ (Ag * (Fb * growthProfile + Fs * source) + Bg * Sm) + (3 : ℝ) ^ a * Sm :=
      add_le_add hfluctuation hmean
    _ = Ag * (Fb * growthProfile + Fs * source) + (Bg + (3 : ℝ) ^ a) * Sm := by ring
    _ ≤ Ag * (Fb * growthProfile + Fs * source) + (Bg + (3 : ℝ) ^ a) *
        (Mb * growthProfile + Md * error + Ms * source) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hSm hT)
    _ = (Ag * Fb + (Bg + (3 : ℝ) ^ a) * Mb) * growthProfile +
        (Bg + (3 : ℝ) ^ a) * Md * error + (Ag * Fs + (Bg + (3 : ℝ) ^ a) * Ms) * source := by ring
    _ ≤ C * growthProfile + C * error + C * source := add_le_add (add_le_add
      (mul_le_mul_of_nonneg_right hC₁ hgrowth) (mul_le_mul_of_nonneg_right hC₂ herror))
      (mul_le_mul_of_nonneg_right hC₃ hsource)

/-- Both cap choices stay in the source generation range for every late target. -/
private theorem transport_profile_generation_caps (jStar : ℕ) (k n : ℤ) (L : ℕ)
    (hL : 1 ≤ L) :
    let ell := fun j : ℤ => if j ≤ k + (L : ℤ) then 1 else L
    let cap := fun j : ℤ => j - (ell j : ℤ)
    (∀ j : ℤ, 1 ≤ ell j ∧ ell j ≤ L) ∧
    (∀ j ∈ Set.Icc ((jStar : ℤ) + L) (n + (L : ℤ)),
      (jStar : ℤ) ≤ cap j ∧ cap j ≤ n + 2 * (L : ℤ)) := by
  intro ell cap
  have hell (j : ℤ) : 1 ≤ ell j ∧ ell j ≤ L := by
    dsimp only [ell]; split_ifs <;> omega
  refine ⟨hell, ?_⟩
  intro j hj
  obtain ⟨hjl, hju⟩ := hj
  obtain ⟨hell1, hellL⟩ := hell j
  dsimp only [cap]; omega

/-- Centering an integrable matrix family gives nonnegative integrable weighted norms. -/
private theorem transport_profile_centered_weighted_integrability {d Q : ℕ}
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {ι : Type*} (I : Finset ι) (hQ : 1 ≤ (Q : ℝ)) (weight : ι → ℝ)
    (hweight : ∀ p, 0 ≤ weight p) (G : ι → CoeffSpace d → BlockMat d)
    (hGmem : ∀ p ∈ I, SchattenMemLp P (Q : ℝ) (G p)) :
    let MG := fun p => ofFullBlockMat (Matrix.of fun α β =>
      ∫ a, blockMatEntry (G p a) α β ∂P)
    let f := fun p a => weight p * absSchattenNorm (Q : ℝ) (blockSub (G p a) (MG p))
    (∀ p ∈ I, ∀ᵐ a ∂P, 0 ≤ f p a) ∧
    (∀ p ∈ I, MemLp (f p) (ENNReal.ofReal (Q : ℝ)) P) := by
  intro MG f
  constructor
  · intro p hp
    exact ((hGmem p hp).center hQ).symmetric.mono fun _ ha =>
      mul_nonneg (hweight p) (absSchattenNorm_nonneg
        ((toFullBlockMat_isHermitian_iff _).2 ha) hQ)
  · intro p hp
    exact (((hGmem p hp).center hQ).memLp_absSchattenNorm hQ).const_mul _

/-- The complete printed profile comparison. All constants precede the law,
geometry and comparison error; both source amplitudes retain their asymmetry. -/
theorem exists_two_grid_profile_comparison (d : ℕ) (hd : 2 ≤ d)
    (K₀ : ℝ) (hK₀ : 1 ≤ K₀) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc C : ℝ, 0 < Csrc ∧ 0 < C ∧
    ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
      (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
      IsStationaryLaw P → IsUnitRangeLaw P → CoarseEllipticityDagger P γ E Ψ K S →
      ∀ jStar : ℕ, 2 * d ≤ 3 ^ jStar → ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
      ∀ m mPlus : Mat d, m.PosDef → mPlus.PosDef →
        gridRatio (explicitRoundedGrid jStar m) (explicitRoundedGrid jStar mPlus) ≤ K₀ →
      ∀ k n : ℤ, (jStar : ℤ) ≤ k → k ≤ n → ∀ L : ℕ, 1 ≤ L →
        adaptedCell (explicitRoundedGrid jStar m) (n + 2 * (L : ℤ)) ∪
          adaptedCell (explicitRoundedGrid jStar mPlus) (n + (L : ℤ)) ⊆ centeredCube d (2 *
            (jStar : ℤ)) →
      ∀ δ : ℝ, δ ∈ Set.Icc (0 : ℝ) (1 / 4) →
        BlockMatLoewnerLE (blockScale (1 - δ) (adaptedMean P (explicitRoundedGrid jStar m) (n +
          2 * (L : ℤ))))
          (adaptedMean P (explicitRoundedGrid jStar mPlus) (n + (L : ℤ))) →
        BlockMatLoewnerLE (adaptedMean P (explicitRoundedGrid jStar mPlus) (n + (L : ℤ)))
          (blockScale (1 + δ) (adaptedMean P (explicitRoundedGrid jStar m) (n + 2 * (L : ℤ)))) →
      profile P γ (explicitRoundedGrid jStar mPlus) jStar (n + (L : ℤ)) (n + (L : ℤ)) ≤
        C * (3 : ℝ) ^ ((1 - γ) / 2 * (L : ℝ)) * profile P γ (explicitRoundedGrid jStar m) jStar
          k (n + 2 * (L : ℤ)) + C * δ +
        C * (1 + aspectRatio E * (K₀ * Real.sqrt (‖m‖ * ‖m⁻¹‖) * Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖) +
          Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖) ^ 2)) ^ bigQ d γ *
          (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) - jStar)) := by
  classical
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Cr, Cf, Cm, hCr, hCf, hCm, hred⟩ := exists_transport_whitney_reduction d hd K₀ hK₀ γ hγ
  obtain ⟨Cs, Ce, hCs, hCe, hearly⟩ := exists_transport_target_source d hd γ hγ
  obtain ⟨CbSrc, hCbSrc, Cb, hCb, hbulk⟩ := exists_transport_bulk_fluctuations d hd K₀ hK₀ γ hγ
  obtain ⟨CdSrc, hCdSrc, Cd, hCd, hboundary⟩ := exists_transport_boundary_fluctuations d hd K₀
    hK₀ γ hγ
  obtain ⟨Co, hCo, hordered⟩ := exists_transport_whitney_ordered_data d hd K₀ hK₀ γ hγ
  let Q := bigQ d γ
  let a := (1 - γ) / 4
  let G₁ := 1 / (1 - (3 : ℝ) ^ (-a))
  let G₃ := 1 / (1 - (3 : ℝ) ^ (-(3 * (1 - γ) / 4)))
  let A := (4 / 3 : ℝ) * (2 * (d : ℝ)) ^ (Q : ℝ)⁻¹
  let D := (2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ * (2 * (d : ℝ)) * Cf + 2 * (d : ℝ) * Ce
  let Em := (1 + 4 * (d : ℝ) * Ce) ^ Q
  let Xm := (3 : ℝ) ^ Q * (2 * 2 ^ Q + 4 ^ Q)
  let Fb := (3 : ℝ) ^ Q * A ^ Q * (Cb + Cd)
  let Fs := (3 : ℝ) ^ Q * D ^ Q * Xm
  let Mb := Cm * (2 + G₃) * (2 + G₁)
  let Md := Cm * G₁
  let Ms := Cm * 2 * G₃ + Em * G₁
  let Ag := (2 : ℝ) ^ ((Q : ℝ) - 1) * (1 + (2 * (d : ℝ)) ^ (Q : ℝ)⁻¹) ^ (Q : ℝ)
  let Bg := (2 : ℝ) ^ (2 * (Q : ℝ) - 1) * (1 + (d : ℝ) ^ (1 - (Q : ℝ)⁻¹)) ^ (Q : ℝ)
  let C := Ag * (Fb + Fs) + (Bg + (3 : ℝ) ^ a) * (Mb + Md + Ms) + 1
  obtain ⟨hQ, hQ1, hQ2, ha, hG₁, hG₃, hA, hD, hEm, hFb, hFs, hMb, hMd, hMs, hAg, hBg, hC⟩ := by
    simpa only [Q, a, G₁, G₃, A, D, Em, Xm, Fb, Fs, Mb, Md, Ms, Ag, Bg, C] using
      transport_profile_coefficient_signs d γ hγ (Cf := Cf) (Ce := Ce) (Cb := Cb)
        (Cd := Cd) (Cm := Cm) hCf.le hCe.le hCb.le hCd.le hCm.le
  let Csrc := max Cr (max Cs (max CbSrc (max CdSrc Co)))
  refine ⟨Csrc, C, hCr.trans_le (le_max_left _ _), hC, ?_⟩
  intro P hP E Ψ K S hstat hunit hdag jStar hj hsrc m mPlus hm hmPlus hratio k n hk hkn L hL
    hwindow δ hδ hlow hup
  have hlog : 0 ≤ Real.logb 3 (2 * K) := (Real.logb_pos (by norm_num)
    (by linarith only [hdag.one_lt_growthWitness] : (1 : ℝ) < 2 * K)).le
  have hs (c : ℝ) (hc : c ≤ Csrc) : ⌈c * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) := (Int.ceil_mono
    (mul_le_mul_of_nonneg_right hc hlog)).trans hsrc
  obtain ⟨X, hX0, hX, hXN, hXi, hEX, hred⟩ := hred P E Ψ K S hstat hdag jStar hj (hs Cr
    (le_max_left _ _))
  obtain ⟨Y, hY0, hY, hYN, hYi, hEY, hearly⟩ := hearly P E Ψ K S hstat hdag jStar hj (hs Cs
    ((le_max_left _ _).trans (le_max_right _ _)))
  have hsB := hs CbSrc ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hsD := hs CdSrc ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _
    _).trans (le_max_right _ _))))
  have hsO := hs Co ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _
    _).trans (le_max_right _ _))))
  let q := explicitRoundedGrid jStar m
  let qPlus := explicitRoundedGrid jStar mPlus
  let t := n + (L : ℤ)
  let s := n + 2 * (L : ℤ)
  let B := 1 + aspectRatio E * (K₀ * Real.sqrt (‖m‖ * ‖m⁻¹‖) * Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖) +
    Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖) ^ 2)
  let Bf := aspectRatio E * K₀ * Real.sqrt (‖m‖ * ‖m⁻¹‖) * Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖)
  obtain ⟨hB, hBf0, hBf, hBnew⟩ := transport_profile_source_amplitudes
    (aspectRatio E) K₀ (Real.sqrt (‖m‖ * ‖m⁻¹‖)) (Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖))
    (aspectRatio_nonneg E) (zero_le_one.trans hK₀) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have ht : (jStar : ℤ) ≤ t := by dsimp only [t]; omega
  have hqPlus := isUnit_roundedGrid hj hmPlus
  have htW : adaptedCell qPlus t ⊆ centeredCube d (2 * (jStar : ℤ)) := Set.Subset.trans
    Set.subset_union_right hwindow
  obtain ⟨I, hI, hIeq, hhist⟩ := transport_fluctuation_history_reindex P γ qPlus hqPlus jStar t ht
  let U := I.filter (fun p => (jStar : ℤ) + L ≤ p.1)
  obtain ⟨hzero, hcenterAll, hCellAll⟩ :=
    transport_reindexed_centered_cells d qPlus hqPlus jStar t I hIeq htW
  have hU : U.Nonempty := ⟨(t, 0), Finset.mem_filter.mpr ⟨(hIeq _).mpr
    ⟨⟨ht, le_rfl⟩, hzero t⟩, by dsimp only [t]; omega⟩⟩
  have hgen (p) (hp : p ∈ U) : p.1 ∈ Set.Icc ((jStar : ℤ) + L) (n + (L : ℤ)) :=
    ⟨(Finset.mem_filter.mp hp).2, ((hIeq p).mp (Finset.mem_filter.mp hp).1).1.2⟩
  have hcenter (p) (hp : p ∈ U) : standardCellCenter p.1 p.2 ∈ centeredCube d t :=
    hcenterAll p ((Finset.mem_filter.mp hp).1)
  obtain ⟨hfin, hbul⟩ := hbulk P E Ψ K S hP hstat hunit hdag jStar hj hsB m mPlus hm hmPlus
    hratio k n hk hkn L hL U hgen hcenter
  obtain ⟨hfinBd, hbd⟩ := hboundary P E Ψ K S hP hstat hunit hdag jStar hj hsD m mPlus hm hmPlus
    hratio k n hk hkn L hL U hgen hcenter
  let ell := fun j : ℤ => if j ≤ k + (L : ℤ) then 1 else L
  let cap := fun j : ℤ => j - (ell j : ℤ)
  let W := fun p : ℤ × (Fin d → ℤ) => adaptedCellAtCenter qPlus p.1 p.2
  have hCell (p) (hp : p ∈ I) : W p ⊆ centeredCube d (2 * (jStar : ℤ)) := by
    simpa only [W] using hCellAll p hp
  let Z := fun p r => if hr : r ≤ cap p.1 then (hfin p r hr).toFinset else ∅
  let v := fun p r => (volume (adaptedCell q r)).toReal / (volume (W p)).toReal
  let V := fun p r a => ofFullBlockMat (∑ z ∈ Z p r, v p r • toFullBlockMat
    (normalizedFluctuation P q r s z a))
  let weight := fun p : ℤ × (Fin d → ℤ) => (3 : ℝ) ^ (-rhoMax d γ * ((n : ℝ) + L - p.1))
  let fb := fun p a => weight p * absSchattenNorm (Q : ℝ) (V p (cap p.1) a)
  let fd := fun p a => weight p * ∑ r ∈ Finset.Icc (jStar : ℤ) (cap p.1 - 1), absSchattenNorm (Q
    : ℝ) (V p r a)
  let Xb := fun a => ⨆ p ∈ (U : Set (ℤ × (Fin d → ℤ))), fb p a
  let Xd := fun a => ⨆ p ∈ (U : Set (ℤ × (Fin d → ℤ))), fd p a
  let Xs := fun a => X a + Y a + 4
  let H := profile P γ q jStar k s
  let R := (3 : ℝ) ^ (-a * ((n : ℝ) - jStar))
  let root := (3 : ℝ) ^ (-(a / (Q : ℝ)) * ((n : ℝ) - jStar))
  let grow := (3 : ℝ) ^ ((1 - γ) / 2 * (L : ℝ))
  have hH : 0 ≤ H := bridge_profile_nonneg d hd P γ E Ψ K S hstat hdag jStar hj m hm k s hk (by
    dsimp only [s]; omega)
  have hgrow : 0 ≤ grow := by dsimp only [grow]; exact three_rpow_nonneg _
  have hR : 0 ≤ R := by dsimp only [R]; exact three_rpow_nonneg _
  have hroot : 0 ≤ root := by dsimp only [root]; exact three_rpow_nonneg _
  have hB0 := zero_le_one.trans hB
  have hBpow : 0 ≤ B ^ Q := pow_nonneg hB0 Q
  have hVmem (p) (r) : SchattenMemLp P (Q : ℝ) (V p r) := memLqSchatten_normalizedCentered_sum d
    hd P γ E Ψ K S hstat hdag jStar hj m hm r
      (adaptedMean P q s) Q hQ1 (Z p r) (fun _ => v p r) id
  have hXbm : (∫ a, Xb a ^ Q ∂P) ≤ Cb * (3 : ℝ) ^ (a * (L : ℝ)) * H := by
    simpa only [Xb, fb, V, Z, dite_eq_left le_rfl, Real.rpow_natCast] using hbul
  have hXdm : (∫ a, Xd a ^ Q ∂P) ≤ Cd * (3 : ℝ) ^ (a * (L : ℝ)) * H := by
    simpa only [Real.rpow_natCast] using hbd
  obtain ⟨hfb0, hfd0, hXb, hXd, hXb0, hXd0, hXs, hXs0, hXsm, hfbMax, hfdMax⟩ :=
    transport_weighted_V_envelopes jStar hQ1 U hU V hVmem weight
      (fun _ => three_rpow_nonneg _) cap X Y (ae_of_all P hX0) (ae_of_all P hY0) hX hY hXN hYN
  have hrootpow : root ^ Q = R := (transport_source_max_weight d hd γ hγ (jStar : ℤ) n (jStar :
    ℤ) L (hk.trans hkn) ⟨le_rfl, ht⟩).2.2
  obtain ⟨hell, hcapGeneration⟩ := transport_profile_generation_caps jStar k n L hL
  have hcap (p) (hp : p ∈ U) := hcapGeneration p.1 (hgen p hp)
  let F := fun p a => normalizedBlock (coarseBlock (W p) a) (adaptedMean P qPlus t)
  let Graw := fun p a => normalizedBlock (ofFullBlockMat (∑' z :
    {z : ℤ × (Fin d → ℤ) // IsMaximalAdaptedCellIn (W p) q (cap p.1) z.1 z.2},
      ((volume (adaptedCellAtCenter q z.1.1 z.1.2)).toReal / (volume (W p)).toReal) •
        toFullBlockMat (coarseBlock (adaptedCellAtCenter q z.1.1 z.1.2) a))) (adaptedMean P qPlus t)
  let G := fun p a => if p.1 < (jStar : ℤ) + L then F p a else Graw p a
  let MF := fun p => ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F p a) α β ∂P)
  let MG := fun p => ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G p a) α β ∂P)
  have hFdata (p) (hp : p ∈ I) := transport_target_ordered_mean d hd P γ E Ψ K S hstat hdag
    jStar hj mPlus hmPlus p.1 t ((hIeq p).mp hp).1.1 ((hIeq p).mp hp).1.2 p.2 (Q : ℝ) hQ1
  have hOrd (p) (hp : p ∈ I) := hordered P E Ψ K S hstat hdag jStar hj hsO m mPlus hm hmPlus hratio
    p.1 t ((hIeq p).mp hp).1.1 ((hIeq p).mp hp).1.2 (ell p.1) (hell p.1).1
    (adaptedCellCenter qPlus p.1 p.2) ⟨p.2, rfl⟩ Q hQ1
  have hFmem (p) (hp : p ∈ I) : SchattenMemLp P (Q : ℝ) (F p) := (hFdata p hp).1
  have hFmean (p) (hp : p ∈ I) : MF p = relMean P qPlus p.1 t := (hFdata p hp).2.2.1
  have hIF (p) (hp : p ∈ I) : BlockMatLoewnerLE (Book.Ch02.blockIdentity d) (MF p) := by
    rw [hFmean p hp]; exact (hFdata p hp).2.2.2
  obtain ⟨hGmem, hFG⟩ := transport_profile_selected_ordered_field jStar L I F Graw hFmem
    (fun p hp => by simpa only [Graw] using! (hOrd p hp).2.1)
    (fun p hp => by simpa only [Graw] using! (hOrd p hp).2.2.1.mono fun _ h => h.2)
  have hEarly (p) (hp : p ∈ I) := transport_target_source_moments (Nat.one_le_iff_ne_zero.mpr
    hQ.ne')
    (F p) (hFmem p hp) (ae_of_all P ((hFdata p hp).2.1)) Y hYi hEY Ce B hCe.le hB
    (by
      filter_upwards [hearly] with aa haa
      have hh := haa mPlus hmPlus t ht htW p.1 ((hIeq p).mp hp).1.1 (adaptedCellCenter qPlus p.1
        p.2) (hCell p hp)
      exact hh.trans (transport_identity_scale_mono (by
        have := mul_le_mul_of_nonneg_left hBnew hCe.le
        have := mul_le_mul_of_nonneg_right this (hY0 aa)
        simpa only [B, mul_assoc] using this))) (hIF p hp)
  let pen := fun r => meanPenalty Q (relMean P q r s)
  let decay := fun j : ℤ => (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - jStar))
  let M := fun j : ℤ => if j < (jStar : ℤ) + L then Em * B ^ Q else Cm *
    (pen (cap j) + (∑ r ∈ Finset.Icc (jStar : ℤ) (cap j - 1),
      (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - r)) * pen r) + δ + B ^ Q * (decay j + decay j ^ Q))
  have hMeans := transport_weighted_mean_accumulation d hd P γ hγ E Ψ K S hstat hdag jStar hj m hm
    k n hk hkn L hL Cm Em δ B hCm.le hEm hδ.1 hB0
  have hM0 (j) (hjj : j ∈ Finset.Icc (jStar : ℤ) t) : 0 ≤ M j := hMeans.1 j hjj
  have hLate (p) (hp : p ∈ U) :=
    (hred m mPlus hm hmPlus hratio s t p.1 (hgen p hp).2 (ell p.1) (hell p.1).1
      (hcap p hp).1 (hcap p hp).2 htW p.2 (hcenter p hp) δ hδ hlow hup).2
  have hMbound := transport_profile_selected_mean_bound (Q := Q) jStar L I F Graw
    (fun j => pen (cap j) + (∑ r ∈ Finset.Icc (jStar : ℤ) (cap j - 1),
      (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - r)) * pen r) + δ)
    decay Cm Em B Bf hCm.le hBf0 hBf (fun _ => three_rpow_nonneg _)
    (fun p hp => (hEarly p hp).2) (fun p hp => (hLate p hp).2)
  let f := fun p aa => weight p * absSchattenNorm (Q : ℝ) (blockSub (G p aa) (MG p))
  obtain ⟨hf0, hf⟩ := transport_profile_centered_weighted_integrability I hQ1 weight
    (fun _ => three_rpow_nonneg _) G hGmem
  have hfbound := transport_profile_pointwise_weighted_fluctuation_bound hd γ hγ jStar k n L
    hk hkn I (fun p hp => ((hIeq p).mp hp).1) F Graw V cap Xb Xd X Y A Cf Ce B Bf
    hA hCf.le hCe.le hB0 hBf0 hBf hX0 hY0 hXb0 hXd0
    (fun p hp => (hEarly p hp).1) (fun p hp => (hLate p hp).1) hfbMax hfdMax
  have hdecay : (3 : ℝ) ^ (a * (L : ℝ)) ≤ grow :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      dsimp only [a]; nlinarith only [mul_nonneg (sub_pos.mpr hγ.2).le (Nat.cast_nonneg L)])
  have hflucG := transport_profile_fluctuation_moment_control Q hQ I hI f hf0 hf Xb Xd Xs hXb0
    hXd0 hXs0 hXb hXd hXs A D B root Fb Fs Xm grow H R Cb Cd (a * (L : ℝ)) hA hD hCb.le
    hCd.le hH hB0 hroot hXbm hXdm hXsm (by rw [mul_pow, mul_pow, hrootpow]) (by
      dsimp only [Fb]) (by dsimp only [Fs]) hdecay hfbound
  let Sm := ∑ j ∈ Finset.Icc (jStar : ℤ) t, (3 : ℝ) ^ (-a * ((n : ℝ) + L - j)) * M j
  have hSm : Sm ≤ Mb * grow * H + Md * δ + Ms * B ^ Q * R := by
    calc
      _ ≤ Cm * ((2 + G₃) * (2 + G₁) * grow * H + G₁ * δ + 2 * G₃ * B ^ Q * R) + Em * G₁ * B ^ Q
        * R := hMeans.2
      _ = _ := by dsimp only [Mb, Md, Ms]; ring
  have hmeanHistory := transport_profile_mean_history_control d hd P γ hγ qPlus jStar n L I
    hIeq hzero F G M hM0 hFmem hGmem hFmean hIF hFG hMbound
  have hdet := hmeanHistory.1
  have hMH := hmeanHistory.2
  have hFluc := transport_profile_fluctuation_history_control (d := d) (Q := Q) (P := P) γ
    qPlus jStar t I hI weight (fun _ => three_rpow_nonneg _) G hQ2
    (Fb * grow * H + Fs * B ^ Q * R) Sm hFmem hGmem
    (fun p hp => ae_of_all P ((hFdata p hp).2.1)) hFG hIF hFmean
    (by simpa only [t, Int.cast_add, Int.cast_natCast] using hhist)
    (by simpa only [f] using hflucG) hdet
  rw [transport_profile_self d hd P γ E Ψ K S hstat hdag jStar hj mPlus hmPlus]
  have htotal := transport_profile_scalar_accumulation Ag Bg Fb Fs Mb Md Ms a (grow * H) δ
    (B ^ Q * R) Sm _ _ hAg hBg hFb hFs hMb hMd hMs (mul_nonneg hgrow hH) hδ.1
    (mul_nonneg hBpow hR) (by simpa only [mul_assoc] using hSm)
    (by simpa only [Ag, Bg, mul_assoc] using hFluc) hMH
  simpa only [C, grow, H, q, qPlus, t, s, R, a, Q, B, mul_assoc] using htotal

end
end HCPolySupport.HighContrast.Annealed
