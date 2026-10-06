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
    (f : ι → α → ℝ) (hf0 : ∀ i ∈ I, ∀ᵐ a ∂P, 0 ≤ f i a) (hf : ∀ i ∈ I, MemLp (f i) (ENNReal.ofReal (Q : ℝ)) P) (X Y Z : α → ℝ) (hX0 : ∀ᵐ a ∂P, 0 ≤ X a) (hY0 : ∀ᵐ a ∂P, 0 ≤ Y a)
    (hZ0 : ∀ᵐ a ∂P, 0 ≤ Z a) (hX : MemLp X (ENNReal.ofReal (Q : ℝ)) P) (hY : MemLp Y (ENNReal.ofReal (Q : ℝ)) P) (hZ : MemLp Z (ENNReal.ofReal (Q : ℝ)) P) (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
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
    (fun _ _ => by norm_num) F (fun i _ => hF0 i) (fun i _ => hF i) (M := 3) (by norm_num) (by norm_num)
  have ht := transport_joint_envelope_moment hQr (by norm_num : (0 : ℝ) ≤ 1) I hI f hf0 hf
    (fun a => A * (X a + Y a) + D * Z a)
    (by filter_upwards [hX0, hY0, hZ0] with a ha hb hc; positivity) (((hX.add hY).const_mul A).add (hZ.const_mul D)) (by simpa only [one_mul] using hbound)
  have he (a : α) : (∑ i : Fin 3, F i a) = A * (X a + Y a) + D * Z a := by
    simp only [Fin.sum_univ_succ, F, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
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
theorem transport_pair_mean_bound (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (I : Finset (ℤ × (Fin d → ℤ))) (J t : ℤ) (hgen : ∀ p ∈ I, p.1 ∈ Set.Icc J t)
    (hcenter : ∀ p ∈ I, standardCellCenter p.1 p.2 ∈ centeredCube d t) (M : ℤ × (Fin d → ℤ) → ℝ) (B : ℤ → ℝ) (hB : ∀ j ∈ Finset.Icc J t, 0 ≤ B j)
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
      dsimp only [w]; rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1; ring
    calc
      _ ≤ ∑ _p ∈ I.filter (fun p => p.1 = j), w j * B j := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hpI, hpj⟩ := Finset.mem_filter.mp hp
        simpa only [hpj] using mul_le_mul_of_nonneg_left (hM p hpI) (by dsimp only [w]; exact three_rpow_rpow_nonneg _ _)
      _ = (w j * ((I.filter (fun p => p.1 = j)).card : ℝ)) * B j := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ (w j * (3 : ℝ) ^ ((d : ℝ) * ((t : ℝ) - j))) * B j := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by dsimp only [w]; exact three_rpow_rpow_nonneg _ _)) (hB j hj)
      _ ≤ _ := by
        rw [he]
        exact mul_le_mul_of_nonneg_right (transport_mean_weight_le d hd γ hγ _
          (by exact_mod_cast sub_nonneg.mpr (Finset.mem_Icc.mp hj).2)).2 (hB j hj)
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
    exact mul_nonneg (three_rpow_nonneg _) (hB j hj)
/-- The mean-history convention uses t−1−j; its extra fixed factor is 3^a. -/
theorem transport_meanHistory_weighted_bound {d : ℕ} (P : Measure (CoeffSpace d)) (γ : ℝ) (q : Mat d) (J t : ℤ) (B : ℤ → ℝ) (hB : ∀ j ∈ Finset.Icc J t, 0 ≤ B j)
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
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S) (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
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
  have hG₃ : 0 ≤ G₃ := (one_div_pos.mpr (transport_geometric_Icc (3 * (1 - γ) / 4) (by linarith only [hγ.2]) 0 0).1).le
  have hH : 0 ≤ H := bridge_profile_nonneg d hd P γ E Ψ K S hstat hdag jStar hj m hm k _ hk (by omega)
  have hell (j : ℤ) : 1 ≤ ell j ∧ ell j ≤ L := by dsimp only [ell]; split_ifs <;> omega
  have hcap (j) (hju : j ∈ U) : (jStar : ℤ) ≤ j - (ell j : ℤ) ∧ j - (ell j : ℤ) ≤ n + 2 * (L : ℤ) := by
    have hh := Finset.mem_Icc.mp hju
    have he := hell j
    dsimp only [J, t] at hh; omega
  have hp (r) (hr : (jStar : ℤ) ≤ r) (hrt : r ≤ n + 2 * (L : ℤ)) : 0 ≤ p r := (adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag jStar hj m hm r _ hr hrt).2.2.2.2.2
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
      _ ≤ _ := transport_bulk_mean_bound d hd P γ hγ E Ψ K S hstat hdag jStar hj m hm k n hk hkn L hL
  have hwbd : (∑ j ∈ U, w j * bd j) ≤ G₃ * (2 + G₁) * D * H := by
    have hh := transport_boundary_mean_bound d hd P γ hγ E Ψ K S hstat hdag jStar hj m hm k n hk hkn L hL
    rw [show (3 : ℝ) / 4 * (1 - γ) = 3 * (1 - γ) / 4 by ring] at hh
    calc
      _ ≤ ∑ j ∈ U, wb j * bd j := Finset.sum_le_sum fun j hjj =>
        mul_le_mul_of_nonneg_right (hweight j) (hbd j hjj)
      _ ≤ G₃ * (2 + G₁) * (3 : ℝ) ^ (a * (L : ℝ)) * H := hh
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hH
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hG₃ (add_nonneg (by norm_num) hG₁))
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by dsimp only [a]; nlinarith only [mul_nonneg (sub_pos.mpr hγ.2).le (Nat.cast_nonneg L)])
  have hdelt : (∑ j ∈ U, w j * δ) ≤ G₁ * δ := by
    simpa only [t, Int.cast_add, Int.cast_natCast] using transport_comparison_error_sum a ha (J + (L : ℤ)) t δ hδ
  have hsrc : (∑ j ∈ U, w j * (decay j + decay j ^ Q)) ≤ 2 * G₃ * R := by
    have he (j : ℤ) : decay j ^ Q = (3 : ℝ) ^ (-(Q : ℝ) * (1 - γ) * ((j : ℝ) - jStar)) := by
      dsimp only [decay]; rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1; ring
    simp_rw [he]
    have hh := transport_fine_weight_sum γ hγ.2 Q (bigQ_pos d γ hγ) J n L
    apply hh.trans
    have hR : (3 : ℝ) ^ (-a * ((n : ℝ) + L - jStar)) ≤ R := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith only [mul_nonneg ha.le (Nat.cast_nonneg L)])
    have hc : 2 / (1 - (3 : ℝ) ^ (-(3 * (1 - γ) / 4))) = 2 * G₃ := by dsimp only [G₃]; ring
    rw [hc]; exact mul_le_mul_of_nonneg_left hR (mul_nonneg (by norm_num) hG₃)
  have hearly : (∑ j ∈ V, w j * (Ce * B ^ Q)) ≤ Ce * G₁ * B ^ Q * R := by
    have he : (∑ j ∈ V, w j * (Ce * B ^ Q)) = (Ce * B ^ Q) * ∑ j ∈ V, w j := by
      rw [← Finset.sum_mul]; ring
    rw [he]
    calc
      _ ≤ (Ce * B ^ Q) * (G₁ * R) := mul_le_mul_of_nonneg_left (transport_early_weight_sum a ha J n L) (mul_nonneg hCe (pow_nonneg hB Q))
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
  have he : (∑ j ∈ V, w j * M j) = ∑ j ∈ V, w j * (Ce * B ^ Q) := Finset.sum_congr rfl fun j hjj => by
    dsimp only [M]; rw [ite_eq_left (by have := (Finset.mem_Icc.mp hjj).2; dsimp only [J] at this; omega)]
  have hl : (∑ j ∈ U, w j * M j) = Cm * ((∑ j ∈ U, w j * bulk j) + (∑ j ∈ U, w j * bd j) +
      (∑ j ∈ U, w j * δ) + B ^ Q * ∑ j ∈ U, w j * (decay j + decay j ^ Q)) := by
    calc
      _ = ∑ j ∈ U, Cm * (w j * bulk j + w j * bd j + w j * δ +
          B ^ Q * (w j * (decay j + decay j ^ Q))) := by
        apply Finset.sum_congr rfl
        intro j hjj
        dsimp only [M]; rw [ite_eq_right (by have := (Finset.mem_Icc.mp hjj).1; dsimp only [J] at this; omega)]
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
theorem transport_target_source_moments {d Q : ℕ} {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] (hQ : 1 ≤ Q) (F : CoeffSpace d → BlockMat d) (hF : SchattenMemLp P (Q : ℝ) F)
    (hF0 : ∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat 0) (F a)) (X : CoeffSpace d → ℝ) (hX : Integrable X P) (hEX : ∫ a, X a ∂P ≤ 2) (C B : ℝ) (hC : 0 ≤ C) (hB : 1 ≤ B)
    (hbound : ∀ᵐ a ∂P, BlockMatLoewnerLE (F a)
      (blockScale (C * B * X a) (Book.Ch02.blockIdentity d))) :
    let MF := ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F a) α β ∂P)
    BlockMatLoewnerLE (Book.Ch02.blockIdentity d) MF →
      (∀ᵐ a ∂P, absSchattenNorm (Q : ℝ) (blockSub (F a) MF) ≤
        2 * (d : ℝ) * C * B * (X a + 2)) ∧
      meanPenalty Q MF ≤ (1 + 4 * (d : ℝ) * C) ^ Q * B ^ Q := by
  intro MF hIF
  have hQr : 1 ≤ (Q : ℝ) := by exact_mod_cast hQ
  have ht := transport_centered_tail_envelope hQr F hF X hX hEX (C * B) (mul_nonneg hC (zero_le_one.trans hB)) hF0 hbound
  refine ⟨by simpa only [mul_assoc] using ht.2, ?_⟩
  have ht0 := blockTrace_identity_sub_nonneg MF (isSymmetricBlockMat_integral hF.symmetric) hIF
  have htr : blockTrace (blockSub MF (Book.Ch02.blockIdentity d)) ≤ 4 * (d : ℝ) * C * B := by
    have he : blockTrace (blockSub MF (Book.Ch02.blockIdentity d)) = blockTrace MF - 2 * (d : ℝ) := by
      rw [blockTrace, toFullBlockMat_blockSub_annealed, Matrix.trace_sub, toFullBlockMat_blockIdentity, Matrix.trace_one]; simp only [BlockCoord, Fintype.card_sum, Fintype.card_fin, Nat.cast_add, two_mul]; rfl
    rw [he]; nlinarith only [ht.1, (show (0 : ℝ) ≤ d from Nat.cast_nonneg d)]
  have hs : 1 + blockTrace (blockSub MF (Book.Ch02.blockIdentity d)) ≤ (1 + 4 * (d : ℝ) * C) * B := by
    nlinarith only [htr, hB]
  calc
    _ ≤ (1 + blockTrace (blockSub MF (Book.Ch02.blockIdentity d))) ^ Q := sub_le_self _ (by norm_num)
    _ ≤ ((1 + 4 * (d : ℝ) * C) * B) ^ Q := pow_le_pow_left₀ (by linarith only [ht0]) hs Q
    _ = _ := mul_pow _ _ _
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
          adaptedCell (explicitRoundedGrid jStar mPlus) (n + (L : ℤ)) ⊆ centeredCube d (2 * (jStar : ℤ)) →
      ∀ δ : ℝ, δ ∈ Set.Icc (0 : ℝ) (1 / 4) →
        BlockMatLoewnerLE (blockScale (1 - δ) (adaptedMean P (explicitRoundedGrid jStar m) (n + 2 * (L : ℤ))))
          (adaptedMean P (explicitRoundedGrid jStar mPlus) (n + (L : ℤ))) →
        BlockMatLoewnerLE (adaptedMean P (explicitRoundedGrid jStar mPlus) (n + (L : ℤ)))
          (blockScale (1 + δ) (adaptedMean P (explicitRoundedGrid jStar m) (n + 2 * (L : ℤ)))) →
      profile P γ (explicitRoundedGrid jStar mPlus) jStar (n + (L : ℤ)) (n + (L : ℤ)) ≤
        C * (3 : ℝ) ^ ((1 - γ) / 2 * (L : ℝ)) * profile P γ (explicitRoundedGrid jStar m) jStar k (n + 2 * (L : ℤ)) + C * δ +
        C * (1 + aspectRatio E * (K₀ * Real.sqrt (‖m‖ * ‖m⁻¹‖) * Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖) +
          Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖) ^ 2)) ^ bigQ d γ *
          (3 : ℝ) ^ (-((1 - γ) / 4) * ((n : ℝ) - jStar)) := by
  classical
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Cr, Cf, Cm, hCr, hCf, hCm, hred⟩ := exists_transport_whitney_reduction d hd K₀ hK₀ γ hγ
  obtain ⟨Cs, Ce, hCs, hCe, hearly⟩ := exists_transport_target_source d hd γ hγ
  obtain ⟨CbSrc, hCbSrc, Cb, hCb, hbulk⟩ := exists_transport_bulk_fluctuations d hd K₀ hK₀ γ hγ
  obtain ⟨CdSrc, hCdSrc, Cd, hCd, hboundary⟩ := exists_transport_boundary_fluctuations d hd K₀ hK₀ γ hγ
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
  have hQ : 0 < Q := bigQ_pos d γ hγ
  have hQ1 : 1 ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQ2 : 2 ≤ Q := bigQ_two_le d γ hγ
  have ha : 0 < a := by dsimp only [a]; linarith only [hγ.2]
  have hG₁ : 0 ≤ G₁ := (one_div_pos.mpr (transport_geometric_Icc a ha 0 0).1).le
  have hG₃ : 0 ≤ G₃ := (one_div_pos.mpr (transport_geometric_Icc (3 * (1 - γ) / 4) (by linarith only [hγ.2]) 0 0).1).le
  have hA : 0 ≤ A := by dsimp only [A]; exact mul_nonneg (by norm_num) (Real.rpow_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) _)
  have hD : 0 ≤ D := by dsimp only [D]; exact add_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) _) (mul_nonneg (by norm_num) (Nat.cast_nonneg d))) hCf.le) (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hCe.le)
  have hEm : 0 ≤ Em := by dsimp only [Em]; exact pow_nonneg (add_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hCe.le)) Q
  have hFb : 0 ≤ Fb := by dsimp only [Fb]; exact mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) Q) (pow_nonneg hA Q)) (add_nonneg hCb.le hCd.le)
  have hFs : 0 ≤ Fs := by dsimp only [Fs, Xm]; exact mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) Q) (pow_nonneg hD Q)) (mul_nonneg (pow_nonneg (by norm_num) Q) (add_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) Q)) (pow_nonneg (by norm_num) Q)))
  have hMb : 0 ≤ Mb := by dsimp only [Mb]; exact mul_nonneg (mul_nonneg hCm.le (add_nonneg (by norm_num) hG₃)) (add_nonneg (by norm_num) hG₁)
  have hMd : 0 ≤ Md := mul_nonneg hCm.le hG₁
  have hMs : 0 ≤ Ms := by dsimp only [Ms]; exact add_nonneg (mul_nonneg (mul_nonneg hCm.le (by norm_num)) hG₃) (mul_nonneg hEm hG₁)
  have hAg : 0 ≤ Ag := by dsimp only [Ag]; exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (add_nonneg (by norm_num) (Real.rpow_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) _)) _)
  have hBg : 0 ≤ Bg := by dsimp only [Bg]; exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (add_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg d) _)) _)
  have hC : 0 < C := by dsimp only [C]; exact lt_of_lt_of_le (by norm_num) (le_add_of_nonneg_left (add_nonneg (mul_nonneg hAg (add_nonneg hFb hFs)) (mul_nonneg (add_nonneg hBg (three_rpow_nonneg a)) (add_nonneg (add_nonneg hMb hMd) hMs))))
  let Csrc := max Cr (max Cs (max CbSrc (max CdSrc Co)))
  refine ⟨Csrc, C, hCr.trans_le (le_max_left _ _), hC, ?_⟩
  intro P hP E Ψ K S hstat hunit hdag jStar hj hsrc m mPlus hm hmPlus hratio k n hk hkn L hL hwindow δ hδ hlow hup
  have hlog : 0 ≤ Real.logb 3 (2 * K) := (Real.logb_pos (by norm_num)
    (by linarith only [hdag.one_lt_growthWitness] : (1 : ℝ) < 2 * K)).le
  have hs (c : ℝ) (hc : c ≤ Csrc) : ⌈c * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) := (Int.ceil_mono (mul_le_mul_of_nonneg_right hc hlog)).trans hsrc
  obtain ⟨X, hX0, hX, hXN, hXi, hEX, hred⟩ := hred P E Ψ K S hstat hdag jStar hj (hs Cr (le_max_left _ _))
  obtain ⟨Y, hY0, hY, hYN, hYi, hEY, hearly⟩ := hearly P E Ψ K S hstat hdag jStar hj (hs Cs ((le_max_left _ _).trans (le_max_right _ _)))
  have hsB := hs CbSrc ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hsD := hs CdSrc ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  have hsO := hs Co ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  let q := explicitRoundedGrid jStar m
  let qPlus := explicitRoundedGrid jStar mPlus
  let t := n + (L : ℤ)
  let s := n + 2 * (L : ℤ)
  let B := 1 + aspectRatio E * (K₀ * Real.sqrt (‖m‖ * ‖m⁻¹‖) * Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖) +
    Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖) ^ 2)
  let Bf := aspectRatio E * K₀ * Real.sqrt (‖m‖ * ‖m⁻¹‖) * Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖)
  have hbracket := transport_profile_source_bracket (aspectRatio_nonneg E) (zero_le_one.trans hK₀) (Real.sqrt_nonneg (‖m‖ * ‖m⁻¹‖)) (Real.sqrt_nonneg (‖mPlus‖ * ‖mPlus⁻¹‖))
  have hB : 1 ≤ B := hbracket.1
  have hBf : Bf ≤ B := hbracket.2.1
  have hBf0 : 0 ≤ Bf := by dsimp only [Bf]; exact mul_nonneg (mul_nonneg (mul_nonneg (aspectRatio_nonneg E) (zero_le_one.trans hK₀)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hBnew : aspectRatio E * Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖) ^ 2 ≤ B := hbracket.2.2
  have ht : (jStar : ℤ) ≤ t := by dsimp only [t]; omega
  have hqPlus := isUnit_roundedGrid hj hmPlus
  have htW : adaptedCell qPlus t ⊆ centeredCube d (2 * (jStar : ℤ)) := Set.Subset.trans Set.subset_union_right hwindow
  obtain ⟨I, hI, hIeq, hhist⟩ := transport_fluctuation_history_reindex P γ qPlus hqPlus jStar t ht
  let U := I.filter (fun p => (jStar : ℤ) + L ≤ p.1)
  have hzero (j : ℤ) : standardCellCenter j (0 : Fin d → ℤ) ∈ centeredCube d t := by
    rw [Recurrence.mem_centeredCube_iff]; intro i; simp only [HighContrast.standardCellCenter, Pi.zero_apply, Int.cast_zero, mul_zero]
    have hpt : (0 : ℝ) < 3 ^ t := by positivity
    constructor <;> nlinarith only [hpt]
  have hU : U.Nonempty := ⟨(t, 0), Finset.mem_filter.mpr ⟨(hIeq _).mpr ⟨⟨ht, le_rfl⟩, hzero t⟩, by dsimp only [t]; omega⟩⟩
  have hgen (p) (hp : p ∈ U) : p.1 ∈ Set.Icc ((jStar : ℤ) + L) (n + (L : ℤ)) := ⟨(Finset.mem_filter.mp hp).2, ((hIeq p).mp (Finset.mem_filter.mp hp).1).1.2⟩
  have hcenter (p) (hp : p ∈ U) : standardCellCenter p.1 p.2 ∈ centeredCube d t := ((hIeq p).mp (Finset.mem_filter.mp hp).1).2
  obtain ⟨hfin, hbul⟩ := hbulk P E Ψ K S hP hstat hunit hdag jStar hj hsB m mPlus hm hmPlus hratio k n hk hkn L hL U hgen hcenter
  obtain ⟨hfinBd, hbd⟩ := hboundary P E Ψ K S hP hstat hunit hdag jStar hj hsD m mPlus hm hmPlus hratio k n hk hkn L hL U hgen hcenter
  let ell := fun j : ℤ => if j ≤ k + (L : ℤ) then 1 else L
  let cap := fun j : ℤ => j - (ell j : ℤ)
  let W := fun p : ℤ × (Fin d → ℤ) => adaptedCellAtCenter qPlus p.1 p.2
  let Z := fun p r => if hr : r ≤ cap p.1 then (hfin p r hr).toFinset else ∅
  let v := fun p r => (volume (adaptedCell q r)).toReal / (volume (W p)).toReal
  let V := fun p r a => ofFullBlockMat (∑ z ∈ Z p r, v p r • toFullBlockMat (normalizedFluctuation P q r s z a))
  let weight := fun p : ℤ × (Fin d → ℤ) => (3 : ℝ) ^ (-rhoMax d γ * ((n : ℝ) + L - p.1))
  let fb := fun p a => weight p * absSchattenNorm (Q : ℝ) (V p (cap p.1) a)
  let fd := fun p a => weight p * ∑ r ∈ Finset.Icc (jStar : ℤ) (cap p.1 - 1), absSchattenNorm (Q : ℝ) (V p r a)
  let Xb := fun a => ⨆ p ∈ (U : Set (ℤ × (Fin d → ℤ))), fb p a
  let Xd := fun a => ⨆ p ∈ (U : Set (ℤ × (Fin d → ℤ))), fd p a
  let Xs := fun a => X a + Y a + 4
  let H := profile P γ q jStar k s
  let R := (3 : ℝ) ^ (-a * ((n : ℝ) - jStar))
  let root := (3 : ℝ) ^ (-(a / (Q : ℝ)) * ((n : ℝ) - jStar))
  let grow := (3 : ℝ) ^ ((1 - γ) / 2 * (L : ℝ))
  have hH : 0 ≤ H := bridge_profile_nonneg d hd P γ E Ψ K S hstat hdag jStar hj m hm k s hk (by dsimp only [s]; omega)
  have hgrow : 0 ≤ grow := by dsimp only [grow]; exact three_rpow_nonneg _
  have hR : 0 ≤ R := by dsimp only [R]; exact three_rpow_nonneg _
  have hroot : 0 ≤ root := by dsimp only [root]; exact three_rpow_nonneg _
  have hB0 := zero_le_one.trans hB
  have hBpow : 0 ≤ B ^ Q := pow_nonneg hB0 Q
  have hVmem (p) (r) : SchattenMemLp P (Q : ℝ) (V p r) := memLqSchatten_normalizedCentered_sum d hd P γ E Ψ K S hstat hdag jStar hj m hm r
      (adaptedMean P q s) Q hQ1 (Z p r) (fun _ => v p r) id
  have hV0 (p r) : ∀ᵐ a ∂P, 0 ≤ absSchattenNorm (Q : ℝ) (V p r a) :=
    (hVmem p r).symmetric.mono fun _ ha => absSchattenNorm_nonneg ((toFullBlockMat_isHermitian_iff _).2 ha) hQ1
  have hfb0 (p) : ∀ᵐ a ∂P, 0 ≤ fb p a := (hV0 p (cap p.1)).mono fun _ ha => mul_nonneg (by dsimp only [weight]; exact three_rpow_nonneg _) ha
  have hfd0 (p) : ∀ᵐ a ∂P, 0 ≤ fd p a :=
    ((Filter.eventually_all_finset (Finset.Icc (jStar : ℤ) (cap p.1 - 1))).mpr
      (fun r _ => hV0 p r)).mono fun _ ha => mul_nonneg (by dsimp only [weight]; exact three_rpow_nonneg _) (Finset.sum_nonneg ha)
  have hfb (p) : MemLp (fb p) (ENNReal.ofReal (Q : ℝ)) P := ((hVmem p (cap p.1)).memLp_absSchattenNorm hQ1).const_mul _
  have hfd (p) : MemLp (fd p) (ENNReal.ofReal (Q : ℝ)) P :=
    (memLp_finsetSum _ (fun r _ => (hVmem p r).memLp_absSchattenNorm hQ1)).const_mul _
  have hXb := weightedMax_memLp U hU fb (fun p _ => hfb0 p) (fun p _ => hfb p)
  have hXd := weightedMax_memLp U hU fd (fun p _ => hfd0 p) (fun p _ => hfd p)
  have hXb0 := weightedMax_nonneg U hU fb (fun p _ => hfb0 p)
  have hXd0 := weightedMax_nonneg U hU fd (fun p _ => hfd0 p)
  have hXs : MemLp Xs (ENNReal.ofReal (Q : ℝ)) P := (hX.add hY).add (memLp_const 4)
  have hXs0 : ∀ᵐ a ∂P, 0 ≤ Xs a := ae_of_all P fun aa =>
    add_nonneg (add_nonneg (hX0 aa) (hY0 aa)) (by norm_num)
  have hXbm : (∫ a, Xb a ^ Q ∂P) ≤ Cb * (3 : ℝ) ^ (a * (L : ℝ)) * H := by
    simpa only [Xb, fb, V, Z, dite_eq_left le_rfl, Real.rpow_natCast] using hbul
  have hXdm : (∫ a, Xd a ^ Q ∂P) ≤ Cd * (3 : ℝ) ^ (a * (L : ℝ)) * H := by
    simpa only [Real.rpow_natCast] using hbd
  have hXsm : (∫ a, Xs a ^ Q ∂P) ≤ Xm := transport_source_sum_moment Q hQ X Y (ae_of_all P hX0) (ae_of_all P hY0) hX hY hXN hYN
  have hrootpow : root ^ Q = R := (transport_source_max_weight d hd γ hγ (jStar : ℤ) n (jStar : ℤ) L (hk.trans hkn) ⟨le_rfl, ht⟩).2.2
  have hell (j : ℤ) : 1 ≤ ell j ∧ ell j ≤ L := by dsimp only [ell]; split_ifs <;> omega
  have hcap (p) (hp : p ∈ U) : (jStar : ℤ) ≤ cap p.1 ∧ cap p.1 ≤ s := by
    obtain ⟨hjl, hju⟩ := hgen p hp
    obtain ⟨hell1, hellL⟩ := hell p.1
    dsimp only [cap, s]; omega
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
  have hGmem (p) (hp : p ∈ I) : SchattenMemLp P (Q : ℝ) (G p) := by
    by_cases he : p.1 < (jStar : ℤ) + L
    · simpa only [G, ite_eq_left he] using hFmem p hp
    · simpa only [G, ite_eq_right he] using! (hOrd p hp).2.1
  have hFG (p) (hp : p ∈ I) : ∀ᵐ a ∂P, BlockMatLoewnerLE (F p a) (G p a) := by
    by_cases he : p.1 < (jStar : ℤ) + L
    · exact ae_of_all P fun _ => by simp only [G, ite_eq_left he]; exact fun _ => le_rfl
    · simpa only [G, ite_eq_right he] using! (hOrd p hp).2.2.1.mono fun _ h => h.2
  have hCell (p) (hp : p ∈ I) : W p ⊆ centeredCube d (2 * (jStar : ℤ)) := by
    have hpt := ((hIeq p).mp hp).1.2
    have he : p.1 + ((t - p.1).toNat : ℤ) = t := by omega
    have hh := (aligned_adapted_partition qPlus hqPlus p.1 (t - p.1).toNat).1 p.2 (by simpa only [he] using! ((hIeq p).mp hp).2)
    rw [he] at hh; exact hh.trans htW
  have hEarly (p) (hp : p ∈ I) := transport_target_source_moments (Nat.one_le_iff_ne_zero.mpr hQ.ne')
    (F p) (hFmem p hp) (ae_of_all P ((hFdata p hp).2.1)) Y hYi hEY Ce B hCe.le hB
    (by
      filter_upwards [hearly] with aa haa
      have hh := haa mPlus hmPlus t ht htW p.1 ((hIeq p).mp hp).1.1 (adaptedCellCenter qPlus p.1 p.2) (hCell p hp)
      exact hh.trans (transport_identity_scale_mono (by
        have := mul_le_mul_of_nonneg_left hBnew hCe.le
        have := mul_le_mul_of_nonneg_right this (hY0 aa)
        simpa only [mul_assoc] using this))) (hIF p hp)
  let pen := fun r => meanPenalty Q (relMean P q r s)
  let decay := fun j : ℤ => (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - jStar))
  let M := fun j : ℤ => if j < (jStar : ℤ) + L then Em * B ^ Q else Cm *
    (pen (cap j) + (∑ r ∈ Finset.Icc (jStar : ℤ) (cap j - 1),
      (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - r)) * pen r) + δ + B ^ Q * (decay j + decay j ^ Q))
  have hMeans := transport_weighted_mean_accumulation d hd P γ hγ E Ψ K S hstat hdag jStar hj m hm
    k n hk hkn L hL Cm Em δ B hCm.le hEm hδ.1 hB0
  have hM0 (j) (hjj : j ∈ Finset.Icc (jStar : ℤ) t) : 0 ≤ M j := hMeans.1 j hjj
  have hLate (p) (hp : p ∈ U) :
      (∀ᵐ aa ∂P, absSchattenNorm (Q : ℝ) (blockSub (Graw p aa)
        (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (Graw p a) α β ∂P))) ≤
        A * (absSchattenNorm (Q : ℝ) (V p (cap p.1) aa) +
          ∑ r ∈ Finset.Icc (jStar : ℤ) (cap p.1 - 1), absSchattenNorm (Q : ℝ) (V p r aa)) +
        ((2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ * (2 * (d : ℝ)) * Cf) * Bf * decay p.1 * (X aa + 2)) ∧
      meanPenalty Q (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (Graw p a) α β ∂P)) ≤
        Cm * (pen (cap p.1) + (∑ r ∈ Finset.Icc (jStar : ℤ) (cap p.1 - 1),
          (3 : ℝ) ^ (-(1 - γ) * ((p.1 : ℝ) - r)) * pen r) + δ + Bf ^ Q * (decay p.1 + decay p.1 ^ Q)) := by
    obtain ⟨hf, hcentered, hmean⟩ := hred m mPlus hm hmPlus hratio s t p.1 (hgen p hp).2
      (ell p.1) (hell p.1).1 (hcap p hp).1 (hcap p hp).2 htW p.2 (hcenter p hp) δ hδ hlow hup
    exact ⟨hcentered, hmean⟩
  have hMbound (p) (hp : p ∈ I) : meanPenalty Q (MG p) ≤ M p.1 := by
    by_cases he : p.1 < (jStar : ℤ) + L
    · simpa only [MG, G, M, ite_eq_left he] using (hEarly p hp).2
    · have hpU : p ∈ U := Finset.mem_filter.mpr ⟨hp, by omega⟩
      have hz : 0 ≤ decay p.1 := by dsimp only [decay]; exact three_rpow_nonneg _
      have hm : meanPenalty Q (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (Graw p a) α β ∂P)) ≤
          Cm * (pen (cap p.1) + (∑ r ∈ Finset.Icc (jStar : ℤ) (cap p.1 - 1),
            (3 : ℝ) ^ (-(1 - γ) * ((p.1 : ℝ) - r)) * pen r) + δ + B ^ Q * (decay p.1 + decay p.1 ^ Q)) :=
        (hLate p hpU).2.trans (mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hBf0 hBf Q)
            (add_nonneg hz (pow_nonneg hz Q)))) hCm.le)
      simpa only [MG, G, M, ite_eq_right he] using hm
  let f := fun p aa => weight p * absSchattenNorm (Q : ℝ) (blockSub (G p aa) (MG p))
  have hf0 (p) (hp : p ∈ I) : ∀ᵐ aa ∂P, 0 ≤ f p aa :=
    ((hGmem p hp).center hQ1).symmetric.mono fun _ ha =>
      mul_nonneg (by dsimp only [weight]; exact three_rpow_nonneg _) (absSchattenNorm_nonneg ((toFullBlockMat_isHermitian_iff _).2 ha) hQ1)
  have hf (p) (hp : p ∈ I) : MemLp (f p) (ENNReal.ofReal (Q : ℝ)) P := (((hGmem p hp).center hQ1).memLp_absSchattenNorm hQ1).const_mul _
  have hDf : (2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ * (2 * (d : ℝ)) * Cf ≤ D := le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hCe.le)
  have hDe : 2 * (d : ℝ) * Ce ≤ D := le_add_of_nonneg_left (mul_nonneg (mul_nonneg (Real.rpow_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) _) (mul_nonneg (by norm_num) (Nat.cast_nonneg d))) hCf.le)
  have hfbMax (p) (hp : p ∈ U) : ∀ᵐ aa ∂P, fb p aa ≤ Xb aa := by
    filter_upwards [(Filter.eventually_all_finset U).mpr (fun p _ => hfb0 p)] with aa haa
    dsimp only [Xb]; rw [iSup_mem_finset_eq_finset_sup U hU _ haa]
    exact Finset.le_sup' (fun p => fb p aa) hp
  have hfdMax (p) (hp : p ∈ U) : ∀ᵐ aa ∂P, fd p aa ≤ Xd aa := by
    filter_upwards [(Filter.eventually_all_finset U).mpr (fun p _ => hfd0 p)] with aa haa
    dsimp only [Xd]; rw [iSup_mem_finset_eq_finset_sup U hU _ haa]
    exact Finset.le_sup' (fun p => fd p aa) hp
  have hfbound (p) (hp : p ∈ I) : ∀ᵐ aa ∂P,
      f p aa ≤ A * (Xb aa + Xd aa) + (D * B * root) * Xs aa := by
    have hw := transport_source_max_weight d hd γ hγ (jStar : ℤ) n p.1 L (hk.trans hkn) ((hIeq p).mp hp).1
    by_cases he : p.1 < (jStar : ℤ) + L
    · have hce : ∀ᵐ aa ∂P, absSchattenNorm (Q : ℝ) (blockSub (G p aa) (MG p)) ≤
          2 * (d : ℝ) * Ce * B * (Y aa + 2) := by
        simpa only [MG, G, ite_eq_left he] using (hEarly p hp).1
      filter_upwards [hce, hXb0, hXd0] with aa haa hba hda
      have hYa : 0 ≤ Y aa + 2 := by linarith only [hY0 aa]
      have hYs : Y aa + 2 ≤ Xs aa := by dsimp only [Xs]; linarith only [hX0 aa]
      calc
        _ ≤ weight p * (2 * (d : ℝ) * Ce * B * (Y aa + 2)) := mul_le_mul_of_nonneg_left haa (by positivity)
        _ = (2 * (d : ℝ) * Ce) * B * weight p * (Y aa + 2) := by ring
        _ ≤ D * B * root * Xs aa := by gcongr; exact hw.1 he
        _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hA (add_nonneg hba hda))
    · have hpU : p ∈ U := Finset.mem_filter.mpr ⟨hp, by omega⟩
      have hce : ∀ᵐ aa ∂P, absSchattenNorm (Q : ℝ) (blockSub (G p aa) (MG p)) ≤
          A * (absSchattenNorm (Q : ℝ) (V p (cap p.1) aa) +
            ∑ r ∈ Finset.Icc (jStar : ℤ) (cap p.1 - 1), absSchattenNorm (Q : ℝ) (V p r aa)) +
          ((2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ * (2 * (d : ℝ)) * Cf) * Bf * decay p.1 * (X aa + 2) := by
        simpa only [MG, G, ite_eq_right he] using (hLate p hpU).1
      filter_upwards [hce, hfbMax p hpU, hfdMax p hpU] with aa haa hba hda
      have hXa : 0 ≤ X aa + 2 := by linarith only [hX0 aa]
      have hXs' : X aa + 2 ≤ Xs aa := by dsimp only [Xs]; linarith only [hY0 aa]
      calc
        _ ≤ weight p * (A * (absSchattenNorm (Q : ℝ) (V p (cap p.1) aa) +
            ∑ r ∈ Finset.Icc (jStar : ℤ) (cap p.1 - 1), absSchattenNorm (Q : ℝ) (V p r aa)) +
          ((2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ * (2 * (d : ℝ)) * Cf) * Bf * decay p.1 * (X aa + 2)) :=
          mul_le_mul_of_nonneg_left haa (by positivity)
        _ = A * (fb p aa + fd p aa) +
            ((2 * (d : ℝ)) ^ (Q : ℝ)⁻¹ * (2 * (d : ℝ)) * Cf) * Bf * (weight p * decay p.1) * (X aa + 2) := by
          dsimp only [fb, fd]; ring
        _ ≤ A * (Xb aa + Xd aa) + (D * B * root) * Xs aa := by
          apply add_le_add (mul_le_mul_of_nonneg_left (add_le_add hba hda) hA)
          gcongr
          exact hw.2.1
  have hthree := transport_joint_three_envelopes Q hQ I hI f hf0 hf Xb Xd Xs hXb0 hXd0 hXs0
    hXb hXd hXs A (D * B * root) hA (by positivity) hfbound
  have hflucG : (∫ aa, (⨆ p ∈ (I : Set (ℤ × (Fin d → ℤ))), f p aa) ^ (Q : ℝ) ∂P) ≤
      Fb * grow * H + Fs * B ^ Q * R := by
    have hpow : (D * B * root) ^ Q = D ^ Q * B ^ Q * R := by rw [mul_pow, mul_pow, hrootpow]
    have hdecay : (3 : ℝ) ^ (a * (L : ℝ)) ≤ grow := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by dsimp only [a]; nlinarith only [mul_nonneg (sub_pos.mpr hγ.2).le (Nat.cast_nonneg L)])
    have hbl := hXbm.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdecay hCb.le) hH)
    have hdl := hXdm.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdecay hCd.le) hH)
    calc
      _ ≤ (3 : ℝ) ^ Q * (A ^ Q * ((∫ aa, Xb aa ^ Q ∂P) + ∫ aa, Xd aa ^ Q ∂P) +
          (D * B * root) ^ Q * ∫ aa, Xs aa ^ Q ∂P) := hthree
      _ ≤ (3 : ℝ) ^ Q * (A ^ Q * (Cb * grow * H + Cd * grow * H) +
          (D * B * root) ^ Q * Xm) := mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hbl hdl) (pow_nonneg hA Q))
              (mul_le_mul_of_nonneg_left hXsm (by positivity))) (by positivity)
      _ = _ := by rw [hpow]; dsimp only [Fb, Fs]; ring
  let Sm := ∑ j ∈ Finset.Icc (jStar : ℤ) t, (3 : ℝ) ^ (-a * ((n : ℝ) + L - j)) * M j
  have hSm : Sm ≤ Mb * grow * H + Md * δ + Ms * B ^ Q * R := by
    calc
      _ ≤ Cm * ((2 + G₃) * (2 + G₁) * grow * H + G₁ * δ + 2 * G₃ * B ^ Q * R) + Em * G₁ * B ^ Q * R := hMeans.2
      _ = _ := by dsimp only [Mb, Md, Ms]; ring
  have hdet : (∑ p ∈ I, weight p ^ (Q : ℝ) * meanPenalty Q (MG p)) ≤ Sm := by
    simpa only [t, Int.cast_add, Int.cast_natCast] using transport_pair_mean_bound d hd γ hγ I (jStar : ℤ) t
      (fun p hp => ((hIeq p).mp hp).1) (fun p hp => ((hIeq p).mp hp).2) (fun p => meanPenalty Q (MG p)) M hM0 hMbound
  have hMH : meanHistory P γ qPlus (jStar : ℤ) t ≤ (3 : ℝ) ^ a * Sm := by
    have hjmean (j) (hjj : j ∈ Finset.Ico (jStar : ℤ) t) : meanPenalty Q (relMean P qPlus j t) ≤ M j := by
      have hp : (j, 0) ∈ I := (hIeq _).mpr ⟨⟨(Finset.mem_Ico.mp hjj).1, (Finset.mem_Ico.mp hjj).2.le⟩, hzero j⟩
      have ho : BlockMatLoewnerLE (MF (j, 0)) (MG (j, 0)) := blockMatLoewnerLE_integral ((hFmem _ hp).integrable_entry hQ1) ((hGmem _ hp).integrable_entry hQ1) (hFG _ hp)
      have hm := (meanPenalty_mono_and_dominates Q (by omega)
        (isSymmetricBlockMat_integral (hFmem _ hp).symmetric)
        (isSymmetricBlockMat_integral (hGmem _ hp).symmetric) (hIF _ hp) ho).1
      change meanPenalty Q (MF (j, 0)) ≤ meanPenalty Q (MG (j, 0)) at hm
      rw [hFmean _ hp] at hm; exact hm.trans (hMbound _ hp)
    simpa only [t, Int.cast_add, Int.cast_natCast] using transport_meanHistory_weighted_bound P γ qPlus (jStar : ℤ) t M hM0 hjmean
  have hcenterF (p) (hp : p ∈ I) (aa) : normalizedFluctuation P qPlus p.1 t (adaptedCellCenter qPlus p.1 p.2) aa =
      blockSub (F p aa) (MF p) := by
    rw [hFmean p hp]; exact normalizedBlock_blockSub _ _ _
  have hSup (aa) : (⨆ p ∈ (I : Set (ℤ × (Fin d → ℤ))), weight p *
      blockOpNorm (normalizedFluctuation P qPlus p.1 t (adaptedCellCenter qPlus p.1 p.2) aa)) =
      ⨆ p ∈ (I : Set (ℤ × (Fin d → ℤ))), weight p * blockOpNorm (blockSub (F p aa) (MF p)) := by
    apply iSup_congr; intro p
    apply iSup_congr; intro hp
    rw [hcenterF p hp]
  have hLeft : fluctuationHistory P γ qPlus jStar t =
      ∫ aa, (⨆ p ∈ (I : Set (ℤ × (Fin d → ℤ))), weight p * blockOpNorm (blockSub (F p aa) (MF p))) ^ (Q : ℝ) ∂P := by
    have hh : fluctuationHistory P γ qPlus jStar t = ∫ aa,
        (⨆ p ∈ (I : Set (ℤ × (Fin d → ℤ))), weight p *
          blockOpNorm (normalizedFluctuation P qPlus p.1 t (adaptedCellCenter qPlus p.1 p.2) aa)) ^ (Q : ℝ) ∂P := by
      simpa only [t, Int.cast_add, Int.cast_natCast] using hhist
    exact hh.trans (integral_congr_ae (ae_of_all P fun aa => congrArg (fun x : ℝ => x ^ (Q : ℝ)) (hSup aa)))
  have hgap := transport_weighted_gap_mean Q hQ2 I hI weight (fun _ => by positivity) F G hFmem hGmem
    (fun p hp => ae_of_all P ((hFdata p hp).2.1)) hFG hIF
  have hFluc : fluctuationHistory P γ qPlus jStar t ≤ Ag * (Fb * grow * H + Fs * B ^ Q * R) + Bg * Sm :=
    hLeft.le.trans (hgap.trans (add_le_add (mul_le_mul_of_nonneg_left hflucG hAg) (mul_le_mul_of_nonneg_left hdet hBg)))
  have hT : 0 ≤ Bg + (3 : ℝ) ^ a := add_nonneg hBg (by positivity)
  have hC₁ : Ag * Fb + (Bg + (3 : ℝ) ^ a) * Mb ≤ C := by
    dsimp only [C]; nlinarith only [mul_nonneg hAg hFs, mul_nonneg hT hMd, mul_nonneg hT hMs]
  have hC₂ : (Bg + (3 : ℝ) ^ a) * Md ≤ C := by
    dsimp only [C]; nlinarith only [mul_nonneg hAg (add_nonneg hFb hFs), mul_nonneg hT hMb, mul_nonneg hT hMs]
  have hC₃ : Ag * Fs + (Bg + (3 : ℝ) ^ a) * Ms ≤ C := by
    dsimp only [C]; nlinarith only [mul_nonneg hAg hFb, mul_nonneg hT hMb, mul_nonneg hT hMd]
  rw [transport_profile_self d hd P γ E Ψ K S hstat hdag jStar hj mPlus hmPlus]
  calc
    _ ≤ (Ag * (Fb * grow * H + Fs * B ^ Q * R) + Bg * Sm) + (3 : ℝ) ^ a * Sm := add_le_add hFluc hMH
    _ = Ag * (Fb * grow * H + Fs * B ^ Q * R) + (Bg + (3 : ℝ) ^ a) * Sm := by ring
    _ ≤ Ag * (Fb * grow * H + Fs * B ^ Q * R) + (Bg + (3 : ℝ) ^ a) * (Mb * grow * H + Md * δ + Ms * B ^ Q * R) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hSm hT)
    _ = (Ag * Fb + (Bg + (3 : ℝ) ^ a) * Mb) * (grow * H) + (Bg + (3 : ℝ) ^ a) * Md * δ +
        (Ag * Fs + (Bg + (3 : ℝ) ^ a) * Ms) * (B ^ Q * R) := by ring
    _ ≤ C * (grow * H) + C * δ + C * (B ^ Q * R) := add_le_add (add_le_add (mul_le_mul_of_nonneg_right hC₁ (mul_nonneg hgrow hH)) (mul_le_mul_of_nonneg_right hC₂ hδ.1))
      (mul_le_mul_of_nonneg_right hC₃ (mul_nonneg hBpow hR))
    _ = _ := by ring

end
end HCPolySupport.HighContrast.Annealed
