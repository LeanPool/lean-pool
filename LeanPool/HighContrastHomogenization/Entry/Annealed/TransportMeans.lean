/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.TransportReduction

/-!
# High-contrast homogenization: Entry.Annealed.TransportMeans

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Mean comparison for the two-grid transport

This module proves the mean comparison of `p.two.grid.transport` on the rounded grid: the
boundary mean-row weight sums that concentrate the coarse-block weight on the deepest scale,
the Whitney mean bound that decomposes the mean penalty into its bulk, boundary and fine-tail
parts, and the geometric-series, generation-fiber and weighted power-sum estimates that keep
the two decay powers of the fine amplitude separate. It also records the parent-center shift
identifying a child fluctuation with a translated one and the weighted history bound for its
moment.
-/
open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter adaptedMean blockScale blockSub
  blockTrace coarseBlock normalizedBlock translateCoeff)
open HCPolySupport.HighContrast (adaptedCell adaptedCellTranslate centeredCube
  standardCellCenter)
namespace HCPolySupport.HighContrast.Annealed
open MeasureTheory Geometry Multiscale Analysis
open scoped Matrix.Norms.L2Operator MatrixOrder Matrix
noncomputable section

/-- A geometric source amplitude at least one absorbs both the linear and
Q-th-power scalar errors without changing their distinct decay powers. -/
theorem transport_source_two_powers (Q : ℕ) (hQ : 1 ≤ Q) {A B z : ℝ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hz : 0 ≤ z) :
    A * B * z + (A * B * z) ^ Q ≤ (A + A ^ Q) * B ^ Q * (z + z ^ Q) := by
  have hB0 := zero_le_one.trans hB
  have hBB : B ≤ B ^ Q := by
    calc
      _ = 1 * B := (one_mul B).symm
      _ ≤ B ^ (Q - 1) * B := mul_le_mul_of_nonneg_right (one_le_pow₀ hB) hB0
      _ = B ^ Q := by rw [← pow_succ, Nat.sub_add_cancel hQ]
  have h1 : A * B * z ≤ (A + A ^ Q) * B ^ Q * z := by
    apply mul_le_mul_of_nonneg_right _ hz
    exact mul_le_mul (le_add_of_nonneg_right (pow_nonneg hA Q)) hBB hB0 (add_nonneg hA (pow_nonneg hA Q))
  have h2 : (A * B * z) ^ Q ≤ (A + A ^ Q) * B ^ Q * z ^ Q := by
    rw [mul_pow, mul_pow]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) (pow_nonneg hB0 Q)) (pow_nonneg hz Q)
  calc
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring
/-- The cap has mass at most one; only the smaller rows use the boundary
mass estimate. Weakening 3^(r−j) preserves the printed (1−γ)-decay. -/
theorem transport_boundary_mean_row_weights {γ Cw : ℝ} (hγ : 0 ≤ γ) (hCw : 0 ≤ Cw) (J cap j : ℤ) (hJ : J ≤ cap) (hcap : cap ≤ j) (lam M : ℤ → ℝ)
    (hlam : ∀ r ∈ Finset.Icc J cap, 0 ≤ lam r) (hM : ∀ r ∈ Finset.Icc J cap, 0 ≤ M r) (hmass : ∑ r ∈ Finset.Icc J cap, lam r ≤ 1)
    (hrow : ∀ r ∈ Finset.Icc J (cap - 1), lam r ≤ Cw * (3 : ℝ) ^ ((r : ℝ) - j)) :
    (∑ r ∈ Finset.Icc J cap, lam r * M r) ≤ (1 + Cw) *
      (M cap + ∑ r ∈ Finset.Icc J (cap - 1), (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - r)) * M r) := by
  have hc : cap ∈ Finset.Icc J cap := Finset.mem_Icc.mpr ⟨hJ, le_rfl⟩
  have he : (Finset.Icc J cap).erase cap = Finset.Icc J (cap - 1) := by
    ext r; simp only [Finset.mem_erase, Finset.mem_Icc]; omega
  have hcapmass : lam cap ≤ 1 := (Finset.single_le_sum hlam hc).trans hmass
  have hb (r) (hr : r ∈ Finset.Icc J (cap - 1)) :
      lam r * M r ≤ Cw * ((3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - r)) * M r) := by
    have hr' : r ∈ Finset.Icc J cap := Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, by have := (Finset.mem_Icc.mp hr).2; omega⟩
    have hgap : 0 ≤ (j : ℝ) - r := by have := (Finset.mem_Icc.mp hr).2; exact_mod_cast (show 0 ≤ j - r by omega)
    have hw : (3 : ℝ) ^ ((r : ℝ) - j) ≤ (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - r)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith only [mul_nonneg hγ hgap])
    calc
      _ ≤ (Cw * (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - r))) * M r := mul_le_mul_of_nonneg_right ((hrow r hr).trans (mul_le_mul_of_nonneg_left hw hCw)) (hM r hr')
      _ = _ := mul_assoc _ _ _
  have hsum := Finset.sum_le_sum hb
  rw [← Finset.mul_sum] at hsum
  have hs0 : 0 ≤ ∑ r ∈ Finset.Icc J (cap - 1), (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - r)) * M r :=
    Finset.sum_nonneg fun r hr => mul_nonneg (by positivity) (hM r
      (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, by have := (Finset.mem_Icc.mp hr).2; omega⟩))
  rw [← Finset.sum_erase_add _ _ hc, he, add_comm]
  calc
    _ ≤ M cap + Cw * (∑ r ∈ Finset.Icc J (cap - 1), (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - r)) * M r) := add_le_add (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hcapmass (hM cap hc)) hsum
    _ ≤ _ := by nlinarith only [mul_nonneg hCw (hM cap hc), hs0]
/-- `p.two.grid.transport`, expanded to include its actual premises and derivation. Cfine and Cw
are the law-independent source and Whitney
constants. The fine amplitude B is geometric; its two decay powers remain
separate. Total mass, boundary row mass and the fine-tail hypotheses are exactly
the corresponding outputs of the Whitney and source constructions. -/
theorem transport_whitney_mean_bound (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (Q : ℕ) (hQ : 1 ≤ Q)
    (Cfine Cw : ℝ) (hCfine : 0 ≤ Cfine) (hCw : 0 ≤ Cw) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ jStar : ℕ, 2 * d ≤ 3 ^ jStar → ∀ m mPlus : Mat d, m.PosDef → mPlus.PosDef →
        ∀ oldEnd newEnd j cap : ℤ, (jStar : ℤ) ≤ cap → cap ≤ oldEnd → cap ≤ j →
        ∀ W : Set (Vec d), ∀ hfin : ∀ r ≤ cap, (maximalAdaptedCellCenters W (explicitRoundedGrid jStar m) cap r).Finite,
        ∀ B : ℝ, 1 ≤ B → ∀ X : CoeffSpace d → ℝ, Integrable X P → (∫ a, X a ∂P ≤ 2) →
        ∀ δ : ℝ, δ ∈ Set.Icc (0 : ℝ) (1 / 4) →
        let q := explicitRoundedGrid jStar m
        let F := adaptedMean P q oldEnd
        let H := adaptedMean P (explicitRoundedGrid jStar mPlus) newEnd
        let I := {p : ℤ × (Fin d → ℤ) // IsMaximalAdaptedCellIn W q cap p.1 p.2}
        let f := fun (p : I) a => ((volume (adaptedCellAtCenter q p.1.1 p.1.2)).toReal / (volume W).toReal) •
          toFullBlockMat (coarseBlock (adaptedCellAtCenter q p.1.1 p.1.2) a)
        let Z := fun r => if hr : r ≤ cap then (hfin r hr).toFinset else ∅
        let lam := fun r => ∑ _z ∈ Z r, (volume (adaptedCell q r)).toReal / (volume W).toReal
        let G := fun a => normalizedBlock (ofFullBlockMat (∑' p, f p a)) H
        let T := fun a => normalizedBlock (ofFullBlockMat (∑' p : {p : I // p.1.1 < (jStar : ℤ)}, f p a)) H
        let MG := ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G a) α β ∂P)
        let decay := (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - jStar))
        BlockMatLoewnerLE (blockScale (1 - δ) F) H → BlockMatLoewnerLE H (blockScale (1 + δ) F) →
        SchattenMemLp P Q G → SchattenMemLp P Q T → (∀ᵐ a ∂P, Summable (fun p => f p a)) →
        (∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat 0) (T a)) →
        (∀ᵐ a ∂P, BlockMatLoewnerLE (T a) (blockScale (Cfine * B * decay * X a) (Book.Ch02.blockIdentity d))) →
        BlockMatLoewnerLE (Book.Ch02.blockIdentity d) MG → (∑ r ∈ Finset.Icc (jStar : ℤ) cap, lam r) ≤ 1 →
        (∀ r ∈ Finset.Icc (jStar : ℤ) (cap - 1), lam r ≤ Cw * (3 : ℝ) ^ ((r : ℝ) - j)) →
        meanPenalty Q MG ≤ C * (meanPenalty Q (relMean P q cap oldEnd) +
          (∑ r ∈ Finset.Icc (jStar : ℤ) (cap - 1), (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - r)) *
            meanPenalty Q (relMean P q r oldEnd)) + δ + B ^ Q * (decay + decay ^ Q)) := by
  let A : ℝ := 2 * (d : ℝ) * Cfine * 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  obtain ⟨C₀, hC₀, hpen⟩ := transport_penalty_convex_error Q hQ ((8 / 3 : ℝ) * d) (by positivity)
  let C₁ := 1 + Cw + A + A ^ Q
  have hC₁ : 0 < C₁ := by dsimp only [C₁]; positivity
  have hC₁w : 1 + Cw ≤ C₁ := by dsimp only [C₁]; have := pow_nonneg hA Q; linarith only [hA, this]
  have hC₁one : 1 ≤ C₁ := (le_add_of_nonneg_right hCw).trans hC₁w
  have hC₁A : A + A ^ Q ≤ C₁ := by dsimp only [C₁]; linarith only [hCw]
  refine ⟨C₀ * C₁, mul_pos hC₀ hC₁, ?_⟩
  intro P hP E Ψ K S hstat hdag jStar hjStar m mPlus hm hmPlus oldEnd newEnd j cap hcap hcapOld hcapj
    W hfin B hB X hX hEX δ hδ q F H I f Z lam G T MG decay hlow hup hG hT hseries hTpos hTbound hIG hmass hrow
  have hQR : 1 ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hB0 := zero_le_one.trans hB
  have hz : 0 ≤ decay := by dsimp only [decay]; positivity
  let J := Finset.Icc (jStar : ℤ) cap
  let MT := ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (T a) α β ∂P)
  let Pm := fun r => relMean P q r oldEnd
  have hF := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar m hm oldEnd
  have hH := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar mPlus hmPlus newEnd
  have hAr (r : ℤ) := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar m hm r
  have hsym (r : ℤ) : IsSymmetricBlockMat (Pm r) := (toFullBlockMat_isHermitian_iff _).mp
    (normalizedBlock_posDef (adaptedMean P q r) F (hAr r) hF).isHermitian
  have horder (r) (hr : r ∈ J) : BlockMatLoewnerLE (Book.Ch02.blockIdentity d) (Pm r) :=
    (adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag jStar hjStar m hm r oldEnd
      (Finset.mem_Icc.mp hr).1 ((Finset.mem_Icc.mp hr).2.trans hcapOld)).1
  have ht (r) (hr : r ∈ J) : 0 ≤ blockTrace (blockSub (Pm r) (Book.Ch02.blockIdentity d)) := blockTrace_identity_sub_nonneg _ (hsym r) (horder r hr)
  have hM (r) (hr : r ∈ J) : 0 ≤ meanPenalty Q (Pm r) := meanPenalty_nonneg Q _ (hsym r) (horder r hr)
  have hlam (r) : 0 ≤ lam r := Finset.sum_nonneg fun _ _ => by positivity
  have hMT := (transport_centered_tail_envelope hQR T hT X hX hEX (Cfine * B * decay)
    (by positivity) hTpos hTbound).1
  have hMT' : blockTrace MT ≤ A * B * decay := hMT.trans_eq (by dsimp only [A]; ring)
  have hmean : toFullBlockMat MG =
      (∑ r ∈ J, lam r • toFullBlockMat (normalizedBlock (adaptedMean P q r) H)) + toFullBlockMat MT :=
    transport_whitney_mean_identity d hd P γ E Ψ K S hstat hdag jStar hjStar m hm W cap hcap hfin Q hQR H hT hseries
  have htrace := transport_mean_trace_split J lam (fun r => adaptedMean P q r) F H MG MT hF hH hδ hlow hup
    (fun r _ => hlam r) hmass (fun r _ => (hAr r).posSemidef) ht hmean (A * B * decay) hMT'
  have hMG0 := blockTrace_identity_sub_nonneg MG (isSymmetricBlockMat_integral hG.symmetric) hIG
  have hp := hpen ℤ J lam (fun r => blockTrace (blockSub (Pm r) (Book.Ch02.blockIdentity d)))
    (fun r _ => hlam r) ht hmass δ (A * B * decay) (blockTrace (blockSub MG (Book.Ch02.blockIdentity d)))
    ⟨hδ.1, hδ.2.trans (by norm_num)⟩ (by positivity) hMG0 (by simpa only [add_assoc] using! htrace)
  change meanPenalty Q MG ≤ C₀ * ((∑ r ∈ J, lam r * meanPenalty Q (Pm r)) + δ +
    A * B * decay + (A * B * decay) ^ Q) at hp
  let BulkBoundary := meanPenalty Q (Pm cap) + ∑ r ∈ Finset.Icc (jStar : ℤ) (cap - 1),
    (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - r)) * meanPenalty Q (Pm r)
  let Tail := B ^ Q * (decay + decay ^ Q)
  have hBB : 0 ≤ BulkBoundary := add_nonneg (hM cap (Finset.mem_Icc.mpr ⟨hcap, le_rfl⟩))
    (Finset.sum_nonneg fun r hr => mul_nonneg (by positivity) (hM r
      (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, by have := (Finset.mem_Icc.mp hr).2; omega⟩)))
  have hTail : 0 ≤ Tail := mul_nonneg (pow_nonneg hB0 Q) (add_nonneg hz (pow_nonneg hz Q))
  have hw : (∑ r ∈ J, lam r * meanPenalty Q (Pm r)) ≤ (1 + Cw) * BulkBoundary := transport_boundary_mean_row_weights hγ.1 hCw jStar cap j hcap hcapj lam
      (fun r => meanPenalty Q (Pm r)) (fun r _ => hlam r) hM hmass hrow
  have hsrc : A * B * decay + (A * B * decay) ^ Q ≤ (A + A ^ Q) * Tail := by
    simpa only [Tail, mul_assoc] using transport_source_two_powers Q hQ hA hB hz
  calc
    _ ≤ C₀ * (((∑ r ∈ J, lam r * meanPenalty Q (Pm r)) + δ) +
        (A * B * decay + (A * B * decay) ^ Q)) := by convert hp using 1; ring
    _ ≤ C₀ * (((1 + Cw) * BulkBoundary + δ) + (A + A ^ Q) * Tail) := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hw le_rfl) hsrc) hC₀.le
    _ ≤ C₀ * ((C₁ * BulkBoundary + C₁ * δ) + C₁ * Tail) := by
      apply mul_le_mul_of_nonneg_left _ hC₀.le
      apply add_le_add (add_le_add (mul_le_mul_of_nonneg_right hC₁w hBB) _) (mul_le_mul_of_nonneg_right hC₁A hTail)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hC₁one hδ.1
    _ = _ := by dsimp only [BulkBoundary, Tail, Pm]; ring
/-- Every source generation occurs for at most the two targets r+1 and r+L. -/
theorem transport_bulk_generation_fiber (k : ℤ) (L : ℕ) (r : ℤ) :
    {j : ℤ | j - (if j ≤ k + (L : ℤ) then 1 else (L : ℤ)) = r} ⊆ {r + 1, r + L} := by
  intro j hj
  dsimp only [Set.mem_ofPred_eq] at hj
  split_ifs at hj with h
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inl (by omega)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inr (by omega)
/-- The profile pays for each of its three nonnegative components. Its first
component pays for the fluctuation history while retaining the mean history. -/
theorem transport_profile_components (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S) (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (k t : ℤ) (hk : (jStar : ℤ) ≤ k) (hkt : k ≤ t) :
    let q := explicitRoundedGrid jStar m
    let A := (3 : ℝ) ^ (-((1 - γ) / 4) * ((t : ℝ) - k)) * (1 + meanPenalty (bigQ d γ) (relMean P q k t))
    A * fluctuationHistory P γ q jStar k ≤ profile P γ q jStar k t ∧
    A * history P γ q jStar k ≤ profile P γ q jStar k t ∧
    meanHistory P γ q k t ≤ profile P γ q jStar k t ∧
    (∑ r ∈ Finset.Icc (k + 1) t,
      (3 : ℝ) ^ (-((1 - γ) / 4) * ((t : ℝ) - r)) *
        Real.exp ((bigQ d γ : ℝ) * detIncrement P q r t) *
        ∫ a, absSchattenNorm (bigQ d γ : ℝ) (normalizedFluctuationSelf P q r a) ^ bigQ d γ ∂P)
      ≤ profile P γ q jStar k t := by
  intro q A
  have hγ := hdag.g_mem
  have hQ : 1 ≤ (bigQ d γ : ℝ) := by exact_mod_cast bigQ_pos d γ hγ
  have hmean (a b : ℤ) (ha : (jStar : ℤ) ≤ a) (hab : a ≤ b) :
      0 ≤ meanPenalty (bigQ d γ) (relMean P q a b) :=
    (adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag jStar hj m hm a b ha hab).2.2.2.2.2
  have hh (a b : ℤ) (ha : (jStar : ℤ) ≤ a) : 0 ≤ meanHistory P γ q a b :=
    Finset.sum_nonneg fun r hr => mul_nonneg (by positivity)
      (hmean r b (ha.trans (Finset.mem_Ico.mp hr).1) (Finset.mem_Ico.mp hr).2.le)
  have hA : 0 ≤ A := mul_nonneg (by positivity) (by linarith only [hmean k t hk hkt])
  obtain ⟨_hHistoryIntegrable, hf⟩ := bridge_fluctuationHistory_integrable d hd P γ E Ψ K S
    hstat hdag jStar hj m hm k hk
  have hhist : 0 ≤ history P γ q jStar k := add_nonneg hf (hh jStar k le_rfl)
  have hthird : 0 ≤ ∑ r ∈ Finset.Icc (k + 1) t,
      (3 : ℝ) ^ (-((1 - γ) / 4) * ((t : ℝ) - r)) *
        Real.exp ((bigQ d γ : ℝ) * detIncrement P q r t) *
        ∫ a, absSchattenNorm (bigQ d γ : ℝ) (normalizedFluctuationSelf P q r a) ^ bigQ d γ ∂P := by
    apply Finset.sum_nonneg
    intro r _
    have hmem := bridge_fluctuation_memLqSchatten d hd P γ E Ψ K S hstat hdag jStar hj m hm r r 0
    have _hIntegral : Integrable (fun a =>
        absSchattenNorm (bigQ d γ : ℝ) (normalizedFluctuationSelf P q r a) ^ bigQ d γ) P := by
      simpa only [Real.rpow_natCast] using! hmem.integrable
    apply mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
    apply integral_nonneg_of_ae
    filter_upwards [hmem.symmetric] with a ha
    exact pow_nonneg (absSchattenNorm_nonneg ((toFullBlockMat_isHermitian_iff _).2 ha) hQ) _
  have hfhi : A * fluctuationHistory P γ q jStar k ≤ A * history P γ q jStar k := by
    apply mul_le_mul_of_nonneg_left _ hA
    change _ ≤ fluctuationHistory P γ q jStar k + meanHistory P γ q jStar k
    linarith only [hh jStar k le_rfl]
  have hh0 := mul_nonneg hA hhist
  have hm0 := hh k t hk
  have hpay : A * history P γ q jStar k ≤ profile P γ q jStar k t := by
    change _ ≤ A * history P γ q jStar k + meanHistory P γ q k t + _
    linarith only [hm0, hthird]
  refine ⟨hfhi.trans hpay, hpay, ?_, ?_⟩ <;>
    change _ ≤ A * history P γ q jStar k + meanHistory P γ q k t + _ <;>
    linarith only [hh0, hm0, hthird]
/-- Reverse integer geometric weights are bounded uniformly in both endpoints,
including an empty interval. The denominator is recorded with its positivity. -/
theorem transport_geometric_Icc (a : ℝ) (ha : 0 < a) (J cap : ℤ) :
    0 < 1 - (3 : ℝ) ^ (-a) ∧
      (∑ r ∈ Finset.Icc J cap, (3 : ℝ) ^ (-a * ((cap : ℝ) - r))) ≤
        1 / (1 - (3 : ℝ) ^ (-a)) := by
  have hq0 : 0 ≤ (3 : ℝ) ^ (-a) := by positivity
  have hq1 : (3 : ℝ) ^ (-a) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos ha)
  refine ⟨sub_pos.mpr hq1, ?_⟩
  classical
  let I := Finset.Icc J cap
  have hinj : Set.InjOn (fun r : ℤ => (cap - r).toNat) (I : Set ℤ) := by
    intro r hr s hs he
    change (cap - r).toNat = (cap - s).toNat at he
    have hr' := (Finset.mem_Icc.mp (show r ∈ Finset.Icc J cap from hr)).2
    have hs' := (Finset.mem_Icc.mp (show s ∈ Finset.Icc J cap from hs)).2
    omega
  have he (r : ℤ) (hr : r ∈ I) :
      (3 : ℝ) ^ (-a * ((cap : ℝ) - r)) = ((3 : ℝ) ^ (-a)) ^ (cap - r).toNat := by
    have hc : ((cap - r).toNat : ℝ) = (cap : ℝ) - r := by
      exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr (Finset.mem_Icc.mp hr).2)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), hc]
  calc
    _ = ∑ r ∈ I, ((3 : ℝ) ^ (-a)) ^ (cap - r).toNat := Finset.sum_congr rfl he
    _ = ∑ s ∈ I.image (fun r => (cap - r).toNat), ((3 : ℝ) ^ (-a)) ^ s :=
      (Finset.sum_image hinj).symm
    _ ≤ ∑' s : ℕ, ((3 : ℝ) ^ (-a)) ^ s :=
      (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _ (fun _ _ => pow_nonneg hq0 _)
    _ = 1 / (1 - (3 : ℝ) ^ (-a)) := by
      simpa only [one_div] using tsum_geometric_of_lt_one hq0 hq1
/-- The actual bulk generation map charges each old summand at most twice.
This remains valid when either finite range is empty. -/
theorem transport_bulk_generation_sum (k : ℤ) (L : ℕ) (S T : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ r ∈ T, 0 ≤ f r)
    (hmap : ∀ j ∈ S, j - (if j ≤ k + (L : ℤ) then 1 else (L : ℤ)) ∈ T) :
    (∑ j ∈ S, f (j - (if j ≤ k + (L : ℤ) then 1 else (L : ℤ)))) ≤ 2 * ∑ r ∈ T, f r := by
  classical
  let g := fun j : ℤ => j - (if j ≤ k + (L : ℤ) then 1 else (L : ℤ))
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun j => f (g j)), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hsub : S.filter (fun j => g j = r) ⊆ {r + 1, r + L} := by
    intro j hj
    have hh := transport_bulk_generation_fiber k L r (Finset.mem_filter.mp hj).2
    simpa only [Finset.mem_insert, Finset.mem_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] using hh
  have hc : (S.filter (fun j => g j = r)).card ≤ 2 :=
    (Finset.card_le_card hsub).trans (by
      simpa only [Finset.card_singleton] using Finset.card_insert_le (r + 1) {r + L})
  have he : (∑ j ∈ S.filter (fun j => g j = r), f (g j)) =
      ((S.filter (fun j => g j = r)).card : ℝ) * f r := by
    rw [Finset.sum_congr rfl (fun j hj => congrArg f (Finset.mem_filter.mp hj).2),
      Finset.sum_const, nsmul_eq_mul]
  rw [he]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hf r hr)
/-- Weighted convexity uses a bound on total weight, without charging the
number of summands. The missing weight is placed at zero. -/
theorem transport_weighted_power_sum {ι : Type*} (Q : ℕ) (hQ : 0 < Q) (s : Finset ι) (w x : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hx : ∀ i ∈ s, 0 ≤ x i) {M : ℝ} (hM : 1 ≤ M) (hs : ∑ i ∈ s, w i ≤ M) :
    (∑ i ∈ s, w i * x i) ^ Q ≤ M ^ Q * ∑ i ∈ s, w i * x i ^ Q := by
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hmass : ∑ i ∈ s, w i / M ≤ 1 := by
    rw [← Finset.sum_div, div_le_one hM0]; exact hs
  have hh := (convexOn_pow (𝕜 := ℝ) Q).map_add_sum_le
    (w := fun i => w i / M) (p := x) (v := 1 - ∑ i ∈ s, w i / M) (q := 0)
    (fun i hi => div_nonneg (hw i hi) hM0.le) (by ring) hx
    (sub_nonneg.mpr hmass) (by norm_num)
  simp only [smul_eq_mul, mul_zero, zero_add, zero_pow (Nat.ne_of_gt hQ)] at hh
  have he : (∑ i ∈ s, w i / M * x i) = (∑ i ∈ s, w i * x i) / M := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [he, div_pow] at hh
  have hbound : (∑ i ∈ s, w i / M * x i ^ Q) ≤ ∑ i ∈ s, w i * x i ^ Q := by
    apply Finset.sum_le_sum
    intro i hi; exact mul_le_mul_of_nonneg_right (div_le_self (hw i hi) hM) (pow_nonneg (hx i hi) Q)
  exact (div_le_iff₀ (pow_pos hM0 Q)).mp (hh.trans hbound) |>.trans_eq (by ring)
/-- The weighted power estimate for integrable random moments, including
empty generation ranges. Positivity and finite moments are explicit guards. -/
theorem transport_weighted_moment_sum {α ι : Type*} [MeasurableSpace α]
    {P : Measure α} (Q : ℕ) (hQ : 0 < Q) (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (f : ι → α → ℝ) (hf0 : ∀ i ∈ s, ∀ᵐ a ∂P, 0 ≤ f i a) (hf : ∀ i ∈ s, MemLp (f i) (ENNReal.ofReal (Q : ℝ)) P)
    {M : ℝ} (hM : 1 ≤ M) (hs : ∑ i ∈ s, w i ≤ M) :
    Integrable (fun a => (∑ i ∈ s, f i a) ^ Q) P ∧
      (∫ a, (∑ i ∈ s, f i a) ^ Q ∂P) ≤
        M ^ Q * ∑ i ∈ s, (w i * (w i)⁻¹ ^ Q) * ∫ a, f i a ^ Q ∂P := by
  have hQr : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hmoment (g : α → ℝ) (hg0 : ∀ᵐ a ∂P, 0 ≤ g a)
      (hg : MemLp g (ENNReal.ofReal (Q : ℝ)) P) : Integrable (fun a => g a ^ Q) P := by
    apply (hg.integrable_norm_rpow (ne_of_gt (ENNReal.ofReal_pos.mpr hQr)) ENNReal.ofReal_ne_top).congr
    filter_upwards [hg0] with a ha
    simp only [Real.norm_of_nonneg ha, ENNReal.toReal_ofReal hQr.le, Real.rpow_natCast]
  have hs0 : ∀ᵐ a ∂P, 0 ≤ ∑ i ∈ s, f i a :=
    ((Filter.eventually_all_finset s).mpr hf0).mono fun _ ha => Finset.sum_nonneg ha
  have hint := hmoment (fun a => ∑ i ∈ s, f i a) hs0 (memLp_finsetSum s hf)
  have hri (i) (hi : i ∈ s) := (hmoment (f i) (hf0 i hi) (hf i hi)).const_mul (w i * (w i)⁻¹ ^ Q)
  refine ⟨hint, ?_⟩
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum s hri, ← integral_const_mul]
  apply integral_mono_ae hint ((integrable_finsetSum s hri).const_mul (M ^ Q))
  filter_upwards [(Filter.eventually_all_finset s).mpr hf0] with a ha
  have hh := transport_weighted_power_sum Q hQ s w (fun i => (w i)⁻¹ * f i a)
    (fun i hi => (hw i hi).le) (fun i hi => mul_nonneg (inv_nonneg.mpr (hw i hi).le) (ha i hi)) hM hs
  have he : ∑ i ∈ s, w i * ((w i)⁻¹ * f i a) = ∑ i ∈ s, f i a := by
    apply Finset.sum_congr rfl
    intro i hi; rw [← mul_assoc, mul_inv_cancel₀ (hw i hi).ne', one_mul]
  rw [he] at hh
  simpa only [mul_pow, mul_assoc] using hh
/-- Forward geometric weights have the same endpoint-independent sum bound. -/
theorem transport_geometric_forward (a : ℝ) (ha : 0 < a) (J cap : ℤ) :
    (∑ r ∈ Finset.Icc J cap, (3 : ℝ) ^ (-a * ((r : ℝ) - J))) ≤
      1 / (1 - (3 : ℝ) ^ (-a)) := by
  classical
  let S := (Finset.Icc J cap).image (fun r : ℤ => -r)
  have hsub : S ⊆ Finset.Icc (-cap) (-J) := by
    intro u hu
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hu
    have hr' := Finset.mem_Icc.mp hr
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  calc
    _ = ∑ u ∈ S, (3 : ℝ) ^ (-a * ((-J : ℤ) - u : ℝ)) := by
      rw [Finset.sum_image (fun r _ s _ he => neg_injective he)]
      apply Finset.sum_congr rfl
      intro r _; simp only [Int.cast_neg]
      congr 1; ring
    _ ≤ ∑ u ∈ Finset.Icc (-cap) (-J), (3 : ℝ) ^ (-a * ((-J : ℤ) - u : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ _ := (transport_geometric_Icc a ha (-cap) (-J)).2
/-- Interchanging the finite target/source sums costs only one geometric
mass, even when the generation ranges depend on the target generation. -/
theorem transport_geometric_convolution (a : ℝ) (ha : 0 < a) (S U : Finset ℤ) (T : ℤ → Finset ℤ) (t : ℤ) (hst : ∀ j ∈ S, j ≤ t) (hTU : ∀ j ∈ S, T j ⊆ U) (hTj : ∀ j ∈ S, ∀ r ∈ T j, r ≤ j)
    (F : ℤ → ℝ) (hF : ∀ r ∈ U, 0 ≤ F r) :
    (∑ j ∈ S, ∑ r ∈ T j, (3 : ℝ) ^ (-a * ((j : ℝ) - r)) * F r) ≤
      (1 / (1 - (3 : ℝ) ^ (-a))) * ∑ r ∈ U, F r := by
  classical
  have hrow (j : ℤ) (hj : j ∈ S) :
      (∑ r ∈ T j, (3 : ℝ) ^ (-a * ((j : ℝ) - r)) * F r) ≤
        ∑ r ∈ U, if r ≤ j then (3 : ℝ) ^ (-a * ((j : ℝ) - r)) * F r else 0 := by
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (fun r hr => Finset.mem_filter.mpr ⟨hTU j hj hr, hTj j hj r hr⟩)
    intro r hr _; exact mul_nonneg (by positivity) (hF r (Finset.mem_filter.mp hr).1)
  calc
    _ ≤ ∑ j ∈ S, ∑ r ∈ U, if r ≤ j then (3 : ℝ) ^ (-a * ((j : ℝ) - r)) * F r else 0 :=
      Finset.sum_le_sum hrow
    _ = ∑ r ∈ U, ∑ j ∈ S.filter (fun j => r ≤ j),
        (3 : ℝ) ^ (-a * ((j : ℝ) - r)) * F r := by
      rw [Finset.sum_comm]; simp only [Finset.sum_filter]
    _ ≤ ∑ r ∈ U, (1 / (1 - (3 : ℝ) ^ (-a))) * F r := by
      apply Finset.sum_le_sum
      intro r hr; rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_right _ (hF r hr)
      apply (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.Icc r t) ?_ (fun _ _ _ => by positivity)).trans
        (transport_geometric_forward a ha r t)
      intro j hj; exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp hj).2, hst j (Finset.mem_filter.mp hj).1⟩
    _ = _ := (Finset.mul_sum U _ _).symm
/-- Any selected target family has the actual aligned target-count bound. -/
theorem transport_target_fiber_card {d : ℕ} (I : Finset (ℤ × (Fin d → ℤ))) (t : ℤ) (hgen : ∀ i ∈ I, i.1 ≤ t) (hcenter : ∀ i ∈ I, standardCellCenter i.1 i.2 ∈ centeredCube d t)
    (j : ℤ) (hj : j ∈ I.image Prod.fst) :
    ((I.filter (fun i => i.1 = j)).card : ℝ) ≤ (3 : ℝ) ^ ((d : ℝ) * ((t : ℝ) - j)) := by
  classical
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  let h := (t - i.1).toNat
  have hit := hgen i hi
  have hgap : i.1 + (h : ℤ) = t := by dsimp only [h]; omega
  obtain ⟨hfin, hc⟩ := alignedCenterSet_finite_card d i.1 h
  let Z := I.filter (fun p => p.1 = i.1)
  have hinj : Set.InjOn (Prod.snd : ℤ × (Fin d → ℤ) → (Fin d → ℤ)) (Z : Set _) := by
    intro p hp q hq he; exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) he
  have hsub : Z.image Prod.snd ⊆ hfin.toFinset := by
    intro u hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
    apply hfin.mem_toFinset.mpr
    have hh := hcenter p (Finset.mem_filter.mp hp).1
    simpa only [(Finset.mem_filter.mp hp).2, hgap] using! hh
  have hn : Z.card ≤ 3 ^ (d * h) := by
    rw [Set.ncard_eq_toFinset_card _ hfin] at hc
    calc
      Z.card = (Z.image Prod.snd).card := (Finset.card_image_iff.mpr hinj).symm
      _ ≤ hfin.toFinset.card := Finset.card_le_card hsub
      _ = _ := hc
  have he : (3 : ℝ) ^ (d * h) = (3 : ℝ) ^ ((d : ℝ) * ((t : ℝ) - i.1)) := by
    rw [← Real.rpow_natCast]
    congr 1; simp only [Nat.cast_mul]
    congr 1
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr (hgen i hi))
  rw [← he]
  exact_mod_cast hn
/-- An actual maximal cell center lies in its target and in the old lattice. -/
theorem transport_maximal_centers_subset {d : ℕ} (W : Set (Vec d)) (q : Mat d) (cap r : ℤ) :
    maximalAdaptedCellCenters W q cap r ⊆ adaptedLatticeAtScale q r ∩ W := by
  rintro z ⟨u, hu, rfl⟩
  refine ⟨⟨u, rfl⟩, hu.1.2 ?_⟩
  rw [adaptedCellAtCenter_eq_affine_standardCell]; exact ⟨standardCellCenter r u, Recurrence.standardCellCenter_mem_standardCell r u,
    (Recurrence.adaptedCellCenter_eq q r u).symm⟩
/-- Two nonnegative random families can be combined under the same joint
maximum, paying only the fixed power constant. -/
theorem transport_joint_sum_moment {α ι : Type*} [MeasurableSpace α]
    {P : Measure α} (Q : ℕ) (hQ : 0 < Q) (I : Finset ι) (hI : I.Nonempty)
    (f g : ι → α → ℝ) (hf0 : ∀ i ∈ I, ∀ᵐ a ∂P, 0 ≤ f i a) (hg0 : ∀ i ∈ I, ∀ᵐ a ∂P, 0 ≤ g i a) (hf : ∀ i ∈ I, MemLp (f i) (ENNReal.ofReal (Q : ℝ)) P)
    (hg : ∀ i ∈ I, MemLp (g i) (ENNReal.ofReal (Q : ℝ)) P) :
    (∫ a, (⨆ i ∈ (I : Set ι), f i a + g i a) ^ (Q : ℝ) ∂P) ≤
      (2 : ℝ) ^ Q * ((∫ a, (⨆ i ∈ (I : Set ι), f i a) ^ (Q : ℝ) ∂P) +
        ∫ a, (⨆ i ∈ (I : Set ι), g i a) ^ (Q : ℝ) ∂P) := by
  have hQr : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hs0 (i) (hi : i ∈ I) : ∀ᵐ a ∂P, 0 ≤ f i a + g i a := by
    filter_upwards [hf0 i hi, hg0 i hi] with a ha hb
    exact add_nonneg ha hb
  have hint := (transport_target_max_moment hQr I hI (fun i a => f i a + g i a)
    hs0 (fun i hi => (hf i hi).add (hg i hi))).1
  have hfint := (transport_target_max_moment hQr I hI f hf0 hf).1
  have hgint := (transport_target_max_moment hQr I hI g hg0 hg).1
  rw [← integral_add hfint hgint, ← integral_const_mul]
  apply integral_mono_ae hint ((hfint.add hgint).const_mul ((2 : ℝ) ^ Q))
  filter_upwards [(Filter.eventually_all_finset I).mpr hf0,
    (Filter.eventually_all_finset I).mpr hg0] with a ha hb
  change _ ≤ (2 : ℝ) ^ Q * ((⨆ i ∈ (I : Set ι), f i a) ^ (Q : ℝ) +
    (⨆ i ∈ (I : Set ι), g i a) ^ (Q : ℝ))
  rw [iSup_mem_finset_eq_finset_sup I hI _ (fun i hi => add_nonneg (ha i hi) (hb i hi)),
    iSup_mem_finset_eq_finset_sup I hI _ ha, iSup_mem_finset_eq_finset_sup I hI _ hb]
  simp only [Real.rpow_natCast]
  obtain ⟨i, hi⟩ := hI
  have hI : I.Nonempty := ⟨i, hi⟩
  have hF : 0 ≤ I.sup' hI (fun i => f i a) := (ha i hi).trans (Finset.le_sup' (fun i : ι => f i a) hi)
  have hG : 0 ≤ I.sup' hI (fun i => g i a) := (hb i hi).trans (Finset.le_sup' (fun i : ι => g i a) hi)
  have hs : I.sup' hI (fun i => f i a + g i a) ≤
      I.sup' hI (fun i => f i a) + I.sup' hI (fun i => g i a) :=
    Finset.sup'_le hI _ (fun j hj => add_le_add (Finset.le_sup' (fun j : ι => f j a) hj)
      (Finset.le_sup' (fun j : ι => g j a) hj))
  have hsnonneg := (add_nonneg (ha i hi) (hb i hi)).trans
    (Finset.le_sup' (fun i : ι => f i a + g i a) hi)
  apply (pow_le_pow_left₀ hsnonneg hs Q).trans
  have hh := transport_weighted_power_sum Q hQ Finset.univ (fun _ : Bool => (1 : ℝ))
    (fun b => if b then I.sup' hI (fun i => f i a) else I.sup' hI (fun i => g i a))
    (by intro b _; norm_num) (by intro b _; cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]; exact hG; exact hF) (M := 2) (by norm_num) (by norm_num [Fintype.sum_bool])
  simpa only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, one_mul, add_comm] using hh
/-- A union of target families is paid by the sum of their moments.
Either subfamily may be empty; no generation-count factor is introduced. -/
theorem transport_joint_union_moment {α ι : Type*} [MeasurableSpace α] [DecidableEq ι]
    {P : Measure α} (Q : ℕ) (hQ : 0 < Q) (I J : Finset ι)
    (f : ι → α → ℝ) (hf0 : ∀ i ∈ I ∪ J, ∀ᵐ a ∂P, 0 ≤ f i a)
    (hf : ∀ i ∈ I ∪ J, MemLp (f i) (ENNReal.ofReal (Q : ℝ)) P) :
    (∫ a, (⨆ i ∈ ((I ∪ J : Finset ι) : Set ι), f i a) ^ (Q : ℝ) ∂P) ≤
      (∫ a, (⨆ i ∈ (I : Set ι), f i a) ^ (Q : ℝ) ∂P) +
        ∫ a, (⨆ i ∈ (J : Set ι), f i a) ^ (Q : ℝ) ∂P := by
  classical
  by_cases hI : I.Nonempty
  · by_cases hJ : J.Nonempty
    · have hQr : 0 < (Q : ℝ) := by exact_mod_cast hQ
      have hU := hI.mono (Finset.subset_union_left (s₂ := J))
      have hfi := (transport_target_max_moment hQr I hI f
        (fun i hi => hf0 i (Finset.mem_union_left J hi)) (fun i hi => hf i (Finset.mem_union_left J hi))).1
      have hfj := (transport_target_max_moment hQr J hJ f
        (fun i hi => hf0 i (Finset.mem_union_right I hi)) (fun i hi => hf i (Finset.mem_union_right I hi))).1
      rw [← integral_add hfi hfj]
      apply integral_mono_ae (transport_target_max_moment hQr (I ∪ J) hU f hf0 hf).1 (hfi.add hfj)
      filter_upwards [(Filter.eventually_all_finset (I ∪ J)).mpr hf0] with a ha
      change _ ≤ (⨆ i ∈ (I : Set ι), f i a) ^ (Q : ℝ) + (⨆ i ∈ (J : Set ι), f i a) ^ (Q : ℝ)
      rw [iSup_mem_finset_eq_finset_sup (I ∪ J) hU _ ha,
        iSup_mem_finset_eq_finset_sup I hI _ (fun i hi => ha i (Finset.mem_union_left J hi)),
        iSup_mem_finset_eq_finset_sup J hJ _ (fun i hi => ha i (Finset.mem_union_right I hi)),
        Finset.sup'_union hI hJ]
      simp only [Real.rpow_natCast]
      change (max (I.sup' hI (fun i => f i a)) (J.sup' hJ (fun i => f i a))) ^ Q ≤
        (I.sup' hI (fun i => f i a)) ^ Q + (J.sup' hJ (fun i => f i a)) ^ Q
      have hIP : 0 ≤ I.sup' hI (fun i => f i a) :=
        (ha hI.choose (Finset.mem_union_left J hI.choose_spec)).trans
          (Finset.le_sup' (fun i : ι => f i a) hI.choose_spec)
      have hJP : 0 ≤ J.sup' hJ (fun i => f i a) :=
        (ha hJ.choose (Finset.mem_union_right I hJ.choose_spec)).trans
          (Finset.le_sup' (fun i : ι => f i a) hJ.choose_spec)
      rcases le_total (I.sup' hI (fun i => f i a)) (J.sup' hJ (fun i => f i a)) with h | h
      · rw [max_eq_right h]
        exact le_add_of_nonneg_left (pow_nonneg hIP Q)
      · rw [max_eq_left h]
        exact le_add_of_nonneg_right (pow_nonneg hJP Q)
    · simp [Finset.not_nonempty_iff_eq_empty.mp hJ, Real.rpow_natCast, zero_pow (Nat.ne_of_gt hQ)]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hI, Real.rpow_natCast, zero_pow (Nat.ne_of_gt hQ)]
/-- An equal-volume row is its relative mass times its unweighted average. -/
theorem transport_uniform_row_average {ι : Type*} {d : ℕ} (Z : Finset ι)
    (hZ : Z.Nonempty) (v : ℝ) (F : ι → FullBlockMat d) :
    (∑ z ∈ Z, v • F z) = ((Z.card : ℝ) * v) • ((Z.card : ℝ)⁻¹ • ∑ z ∈ Z, F z) := by
  have hc : (Z.card : ℝ) ≠ 0 := by exact_mod_cast hZ.card_pos.ne'
  rw [smul_smul, mul_comm (Z.card : ℝ) v, mul_assoc, mul_inv_cancel₀ hc, mul_one,
    Finset.smul_sum]
/-- The averaging estimate is instantiated at the actual lattice row (N,j,Z,R).
The standing unit-range law is consumed here. The empty row has zero norm. -/
theorem exists_transport_lattice_row_average (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (S : CoeffSpace d → ℝ) (_hP : IsProbabilityMeasure P),
      IsStationaryLaw P → IsUnitRangeLaw P → CoarseEllipticityDagger P γ E Ψ K S →
      ∀ (N : ℕ), 2 ≤ N → Even N → ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
      ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
      ∀ (m : Mat d), m.PosDef → ∀ (j : ℤ), (jStar : ℤ) ≤ j →
      ∀ (Z : Finset (Vec d)), (Z : Set (Vec d)) ⊆ adaptedLatticeAtScale (explicitRoundedGrid jStar m) j →
      ∀ (R : BlockMat d), IsSymmetricBlockMat R → Book.Ch02.BlockPosDef R →
      ∀ (v : ℝ), 0 ≤ v →
      lqSchattenNorm P (N : ℝ) (fun a => ofFullBlockMat
        (∑ z ∈ Z, v • toFullBlockMat (normalizedBlock
          (blockSub (coarseBlock (adaptedCellTranslate (explicitRoundedGrid jStar m) j z) a)
            (adaptedMean P (explicitRoundedGrid jStar m) j)) R))) ≤
        ((Z.card : ℝ) * v) *
          ((N : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) / (Z.card : ℝ) ^ ((1 : ℝ) / 2)) *
          lqSchattenNorm P (N : ℝ) (fun a => normalizedBlock
            (blockSub (coarseBlock (adaptedCell (explicitRoundedGrid jStar m) j) a)
              (adaptedMean P (explicitRoundedGrid jStar m) j)) R) := by
  obtain ⟨Cs, hCs, havg⟩ := Entry.fixed_geometry_matrix_averaging d hd γ hγ
  refine ⟨Cs, hCs, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag N hN hNeven jStar hj hsrc m hm j hjgen Z hZ R hRs hRp v hv
  let := hP
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  by_cases hne : Z.Nonempty
  · have hmem := memLqSchatten_normalizedCentered_sum d hd P γ E Ψ K S hstat hdag
      jStar hj m hm j R N hN1 Z (fun _ => (Z.card : ℝ)⁻¹) id
    have hmem' : SchattenMemLp P (N : ℝ) (fun a => ofFullBlockMat
        ((Z.card : ℝ)⁻¹ • ∑ z ∈ Z, toFullBlockMat (normalizedBlock
          (blockSub (coarseBlock (adaptedCellTranslate (explicitRoundedGrid jStar m) j z) a)
            (adaptedMean P (explicitRoundedGrid jStar m) j)) R))) := by
      simpa only [Finset.smul_sum, id_eq] using hmem
    simp_rw [transport_uniform_row_average Z hne v]
    have he := lqSchattenNorm_smul hN1 hmem' ((Z.card : ℝ) * v)
    simp only [toFullBlockMat_ofFullBlockMat, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hv)] at he
    rw [he]
    exact (mul_le_mul_of_nonneg_left
      (havg P E Ψ K S hP hstat hunit hdag N hN hNeven jStar hj hsrc m hm j hjgen Z hne hZ R hRs hRp)
      (mul_nonneg (Nat.cast_nonneg _) hv)).trans_eq (by ring)
  · have hZ0 := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [hZ0, Finset.sum_empty, Finset.card_empty, Nat.cast_zero, zero_mul]
    simp only [lqSchattenNorm, absSchattenNorm_ofFullBlockMat_zero hN1,
      Real.zero_rpow (by positivity : (N : ℝ) ≠ 0), integral_zero,
      Real.zero_rpow (inv_ne_zero (by positivity : (N : ℝ) ≠ 0)), le_refl]
/-- Count times equal cell volume gives the square-sum coefficient, with no
nonempty-row assumption. Exponents b=d ell or b=(d-1)(j-r) give both rows. -/
theorem transport_row_square_sum_bound {ι : Type*} (Z : Finset ι)
    {C v a b : ℝ} (hC : 0 ≤ C) (hv : 0 ≤ v)
    (hcard : (Z.card : ℝ) ≤ C * (3 : ℝ) ^ b)
    (hvol : v ≤ C * (3 : ℝ) ^ (-a)) :
    (∑ _z ∈ Z, v ^ 2) ^ ((1 : ℝ) / 2) ≤
      C * Real.sqrt C * (3 : ℝ) ^ (b / 2 - a) := by
  have hs : (∑ _z ∈ Z, v ^ 2) ^ ((1 : ℝ) / 2) = Real.sqrt (Z.card : ℝ) * v := by
    rw [← Real.sqrt_eq_rpow, Finset.sum_const, nsmul_eq_mul, Real.sqrt_mul (Nat.cast_nonneg _),
      Real.sqrt_sq hv]
  have hr : Real.sqrt ((3 : ℝ) ^ b) = (3 : ℝ) ^ (b / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1; ring
  rw [hs]
  calc
    _ ≤ Real.sqrt (C * (3 : ℝ) ^ b) * (C * (3 : ℝ) ^ (-a)) := mul_le_mul (Real.sqrt_le_sqrt hcard) hvol hv (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul hC, hr]; rw [show b / 2 - a = b / 2 + (-a) by ring, Real.rpow_add (by norm_num : (0 : ℝ) < 3)]; ring
/-- Boundary averaging has still more geometric decay than bulk averaging. -/
theorem transport_boundary_decay_pos (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    0 < ((d : ℝ) + 1) / 2 - (1 - γ) / (4 * (bigQ d γ : ℝ)) := by
  have h := fluctuation_decay_exponent_pos d hd γ hγ
  linarith only [h]
/-- The old-history factor uses the trace penalty at scale k, with the d/Q
loss from counting the old parents. -/
theorem transport_old_history_factor (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (M : BlockMat d) (hM : (toFullBlockMat M).IsHermitian)
    (hIM : BlockMatLoewnerLE (Book.Ch02.blockIdentity d) M)
    (n k : ℤ) (hnk : k ≤ n) (L : ℕ) :
    (3 : ℝ) ^ (-(rhoMax d γ - (d : ℝ) / (bigQ d γ : ℝ)) * ((n : ℝ) + L - k)) *
        blockOpNorm M ≤
      (3 : ℝ) ^ ((1 - γ) / (4 * (bigQ d γ : ℝ)) * (L : ℝ)) *
        (3 : ℝ) ^ (-(1 - γ) / (4 * (bigQ d γ : ℝ)) * ((n : ℝ) + 2 * L - k)) *
        (1 + meanPenalty (bigQ d γ) M) ^ (bigQ d γ : ℝ)⁻¹ := by
  have hnorm := blockOpNorm_le_one_add_trace M hM hIM
  have hbase : 0 ≤ 1 + blockTrace (blockSub M (Book.Ch02.blockIdentity d)) := (norm_nonneg _).trans hnorm
  have hroot : (1 + meanPenalty (bigQ d γ) M) ^ (bigQ d γ : ℝ)⁻¹ =
      1 + blockTrace (blockSub M (Book.Ch02.blockIdentity d)) := by
    rw [meanPenalty, add_sub_cancel, ← Real.rpow_natCast]; exact Real.rpow_rpow_inv hbase (bigQ_real_pos d γ hγ).ne'
  have hgap : 0 ≤ (n : ℝ) + L - k := by
    have hn : (k : ℝ) ≤ n := by exact_mod_cast hnk
    linarith only [hn, Nat.cast_nonneg (α := ℝ) L]
  have hw : (3 : ℝ) ^ (-(rhoMax d γ - (d : ℝ) / (bigQ d γ : ℝ)) * ((n : ℝ) + L - k)) ≤
      (3 : ℝ) ^ ((1 - γ) / (4 * (bigQ d γ : ℝ)) * (L : ℝ)) *
        (3 : ℝ) ^ (-(1 - γ) / (4 * (bigQ d γ : ℝ)) * ((n : ℝ) + 2 * L - k)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3), rhoMax_sub_d_div_bigQ d hd γ hγ]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hγgap := mul_nonneg hγ.1 hgap
    simp only [neg_div]
    nlinarith only [hγgap]
  rw [hroot]; exact mul_le_mul hw hnorm (norm_nonneg _) (by positivity)
/-- The exact target count changes rho to rho-d/Q. This is the loss paid
before applying the averaging estimate. -/
theorem transport_target_count_weight (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (s : ℝ) :
    (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * s) * (3 : ℝ) ^ ((d : ℝ) * s) =
      (3 : ℝ) ^ (-(bigQ d γ : ℝ) *
        (γ + (1 - γ) / (4 * (bigQ d γ : ℝ))) * s) := by
  rw [← rhoMax_sub_d_div_bigQ d hd γ hγ, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  field_simp [(bigQ_real_pos d γ hγ).ne']
  ring
/-- The boundary history convolution before choosing the branch j≥k or j<k. -/
theorem transport_boundary_history_sum {ρ : ℝ} (hρ : ρ < 1) (J cap k j : ℤ) :
    (∑ r ∈ Finset.Icc J cap, (3 : ℝ) ^ ((r : ℝ) - j) * (3 : ℝ) ^ (ρ * ((k : ℝ) - r))) ≤
      (1 / (1 - (3 : ℝ) ^ (-(1 - ρ)))) *
        (3 : ℝ) ^ ((cap : ℝ) - j + ρ * ((k : ℝ) - cap)) := by
  have he (r : ℤ) : (3 : ℝ) ^ ((r : ℝ) - j) * (3 : ℝ) ^ (ρ * ((k : ℝ) - r)) =
      (3 : ℝ) ^ ((cap : ℝ) - j + ρ * ((k : ℝ) - cap)) *
        (3 : ℝ) ^ (-(1 - ρ) * ((cap : ℝ) - r)) := by
    simp only [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1; ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left (transport_geometric_Icc (1 - ρ) (sub_pos.mpr hρ) J cap).2
    (by positivity)).trans_eq (mul_comm _ _)
/-- For j<k the boundary history coefficient has 3^(rho(k-j)) growth.
The same bound applies to the first branch since rho<1. -/
theorem transport_boundary_history_below {ρ : ℝ} (hρ : ρ < 1) (J cap k j : ℤ)
    (hcap : cap ≤ j) :
    (∑ r ∈ Finset.Icc J cap, (3 : ℝ) ^ ((r : ℝ) - j) * (3 : ℝ) ^ (ρ * ((k : ℝ) - r))) ≤
      (1 / (1 - (3 : ℝ) ^ (-(1 - ρ)))) * (3 : ℝ) ^ (ρ * ((k : ℝ) - j)) := by
  apply (transport_boundary_history_sum hρ J cap k j).trans
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (one_div_pos.mpr
    (transport_geometric_Icc (1 - ρ) (sub_pos.mpr hρ) J cap).1))
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hc : (cap : ℝ) ≤ j := by exact_mod_cast hcap
  have hn := mul_nonneg (sub_nonneg.mpr hρ.le) (sub_nonneg.mpr hc)
  nlinarith only [hn]
/-- Subtracting a scale-k parent center leaves an aligned scale-r center.
The child center then lies in the untranslated parent used by the history. -/
theorem transport_parent_center_shift {d : ℕ} (q : Mat d) (r k : ℤ) (hrk : r ≤ k)
    (w v : Fin d → ℤ) :
    ∃ u : Fin d → ℤ,
      adaptedCellCenter q r u + adaptedCellCenter q k v = adaptedCellCenter q r w ∧
      (adaptedCellCenter q r w ∈ adaptedCellAtCenter q k v →
        adaptedCellCenter q r u ∈ adaptedCell q k) := by
  let b : ℤ := 3 ^ (k - r).toNat
  let u : Fin d → ℤ := fun i => w i - b * v i
  have hscale : (3 : ℝ) ^ k = (3 : ℝ) ^ r * (b : ℝ) := by
    have he : k = r + ((k - r).toNat : ℤ) := by omega
    conv_lhs => rw [he, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
    simp only [b, Int.cast_pow, Int.cast_ofNat]
  have hu : (fun i => (u i : ℝ)) = (fun i => (w i : ℝ)) - (b : ℝ) • (fun i => (v i : ℝ)) := by
    funext i
    simp only [u, Int.cast_sub, Int.cast_mul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have he : adaptedCellCenter q r u + adaptedCellCenter q k v = adaptedCellCenter q r w := by
    simp only [adaptedCellCenter, hu, matVecMul_eq_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul,
      smul_sub, hscale, mul_smul]
    exact sub_add_cancel _ _
  refine ⟨u, he, ?_⟩
  rintro ⟨x, hx, hxe⟩
  have hx' : x = adaptedCellCenter q r u := by
    apply add_left_cancel (a := adaptedCellCenter q k v)
    exact hxe.trans ((add_comm _ _).trans he).symm
  exact hx' ▸ hx
/-- One parent translation works simultaneously for every child generation;
this pointwise equality therefore survives the joint maximum. -/
theorem transport_parent_fluctuation_shift (d : ℕ) (jStar : ℕ) (m : Mat d)
    (k : ℤ) (hk : (jStar : ℤ) ≤ k) (v : Fin d → ℤ) :
    ∃ p : Fin d → ℤ, ∀ (P : Measure (CoeffSpace d)) (r t : ℤ), r ≤ k →
      ∀ w : Fin d → ℤ, adaptedCellCenter (explicitRoundedGrid jStar m) r w ∈
        adaptedCellAtCenter (explicitRoundedGrid jStar m) k v →
      ∃ z ∈ adaptedLatticeAtScale (explicitRoundedGrid jStar m) r ∩ adaptedCell (explicitRoundedGrid jStar m) k,
        ∀ a : CoeffSpace d,
          normalizedFluctuation P (explicitRoundedGrid jStar m) r t
            (adaptedCellCenter (explicitRoundedGrid jStar m) r w) a =
          normalizedFluctuation P (explicitRoundedGrid jStar m) r t z (translateCoeff p a) := by
  obtain ⟨p, hp⟩ := adaptedCellCenter_eq_intTranslation jStar m hk v
  refine ⟨p, ?_⟩
  intro P r t hr w hw
  obtain ⟨u, he, hu⟩ := transport_parent_center_shift (explicitRoundedGrid jStar m) r k hr w v
  refine ⟨adaptedCellCenter (explicitRoundedGrid jStar m) r u, ⟨⟨u, rfl⟩, hu hw⟩, ?_⟩
  intro a
  have hc := coarseBlock_adapted_translateCoeff (explicitRoundedGrid jStar m) r
    (adaptedCellCenter (explicitRoundedGrid jStar m) r u) p a
  rw [← hp, he] at hc; simp only [normalizedFluctuation, hc]
/-- The history's actual center set is a finite nonempty image of an aligned
integer box. This supplies the boundedness needed when using its real suprema. -/
theorem transport_history_centers {d : ℕ} (q : Mat d) (hq : IsUnit q)
    (r k : ℤ) (hrk : r ≤ k) :
    (adaptedLatticeAtScale q r ∩ adaptedCell q k).Finite ∧
      (adaptedLatticeAtScale q r ∩ adaptedCell q k).Nonempty := by
  have hgap : r + ((k - r).toNat : ℤ) = k := by omega
  have hf := (alignedCenterSet_finite_card d r (k - r).toNat).1
  rw [hgap] at hf
  have heq : adaptedLatticeAtScale q r ∩ adaptedCell q k =
      adaptedCellCenter q r '' {w : Fin d → ℤ | standardCellCenter r w ∈ centeredCube d k} := by
    ext z
    constructor
    · rintro ⟨⟨w, rfl⟩, x, hx, he⟩
      refine ⟨w, ?_, rfl⟩
      rw [Recurrence.adaptedCellCenter_eq] at he
      change standardCellCenter r w ∈ centeredCube d k
      exact (matVecMul_injective_of_isUnit q hq he) ▸ hx
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, rfl⟩, ⟨standardCellCenter r w, hw,
        (Recurrence.adaptedCellCenter_eq q r w).symm⟩⟩
  rw [heq]
  refine ⟨hf.image _, Set.Nonempty.image _ ⟨0, ?_⟩⟩
  change standardCellCenter r 0 ∈ centeredCube d k
  rw [Recurrence.mem_centeredCube_iff]
  intro i; simp only [HighContrast.standardCellCenter, Pi.zero_apply, Int.cast_zero, mul_zero]
  have hp : (0 : ℝ) < 3 ^ k := by positivity
  constructor <;> nlinarith only [hp]
/-- A chosen child moment is bounded by the single joint history integrand.
No sum over source generations is introduced. -/
theorem transport_history_pointwise {d : ℕ} (P : Measure (CoeffSpace d)) (γ : ℝ) (q : Mat d) (hq : IsUnit q) (jStar : ℕ) (k r : ℤ) (hr : r ∈ Set.Icc (jStar : ℤ) k)
    (z : Vec d) (hz : z ∈ adaptedLatticeAtScale q r ∩ adaptedCell q k) (a : CoeffSpace d) :
    (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((k : ℝ) - r)) *
        blockOpNorm (normalizedFluctuation P q r k z a) ^ bigQ d γ ≤
      ⨆ j ∈ Set.Icc (jStar : ℤ) k,
        (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((k : ℝ) - j)) *
          ⨆ y ∈ adaptedLatticeAtScale q j ∩ adaptedCell q k,
            blockOpNorm (normalizedFluctuation P q j k y a) ^ bigQ d γ := by
  classical
  have hinner (j : ℤ) (hj : j ∈ Set.Icc (jStar : ℤ) k) := transport_history_centers q hq j k hj.2
  have he (j : ℤ) (hj : j ∈ Set.Icc (jStar : ℤ) k) :
      (⨆ y ∈ adaptedLatticeAtScale q j ∩ adaptedCell q k,
        blockOpNorm (normalizedFluctuation P q j k y a) ^ bigQ d γ) =
      (hinner j hj).1.toFinset.sup' ((hinner j hj).1.toFinset_nonempty.mpr (hinner j hj).2)
        (fun y => blockOpNorm (normalizedFluctuation P q j k y a) ^ bigQ d γ) := by
    simpa only [Set.Finite.coe_toFinset] using! iSup_mem_finset_eq_finset_sup (hinner j hj).1.toFinset
      ((hinner j hj).1.toFinset_nonempty.mpr (hinner j hj).2) _
      (fun _ _ => pow_nonneg (norm_nonneg _) _)
  have hpos (j : ℤ) (hj : j ∈ Finset.Icc (jStar : ℤ) k) :
      0 ≤ (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((k : ℝ) - j)) *
        ⨆ y ∈ adaptedLatticeAtScale q j ∩ adaptedCell q k,
          blockOpNorm (normalizedFluctuation P q j k y a) ^ bigQ d γ := by
    apply mul_nonneg (by positivity)
    rw [he j (Finset.mem_Icc.mp hj)]
    obtain ⟨y, hy⟩ := (hinner j (Finset.mem_Icc.mp hj)).2
    exact (pow_nonneg (norm_nonneg _) _).trans
      (Finset.le_sup' (fun y => blockOpNorm (normalizedFluctuation P q j k y a) ^ bigQ d γ)
        ((hinner j (Finset.mem_Icc.mp hj)).1.mem_toFinset.mpr hy))
  have hne : (Finset.Icc (jStar : ℤ) k).Nonempty := Finset.nonempty_Icc.mpr (hr.1.trans hr.2)
  rw [show Set.Icc (jStar : ℤ) k = (Finset.Icc (jStar : ℤ) k : Set ℤ) by ext; simp,
    iSup_mem_finset_eq_finset_sup _ hne _ hpos]
  have hi : blockOpNorm (normalizedFluctuation P q r k z a) ^ bigQ d γ ≤
      ⨆ y ∈ adaptedLatticeAtScale q r ∩ adaptedCell q k,
        blockOpNorm (normalizedFluctuation P q r k y a) ^ bigQ d γ := by
    rw [he r hr]
    exact Finset.le_sup' (fun y : Vec d =>
      blockOpNorm (normalizedFluctuation P q r k y a) ^ bigQ d γ)
      ((hinner r hr).1.mem_toFinset.mpr hz)
  exact (mul_le_mul_of_nonneg_left hi (by positivity)).trans
    (Finset.le_sup' (fun j : ℤ =>
      (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((k : ℝ) - j)) *
        ⨆ y ∈ adaptedLatticeAtScale q j ∩ adaptedCell q k,
          blockOpNorm (normalizedFluctuation P q j k y a) ^ bigQ d γ)
      (Finset.mem_Icc.mpr hr))

end
end HCPolySupport.HighContrast.Annealed
