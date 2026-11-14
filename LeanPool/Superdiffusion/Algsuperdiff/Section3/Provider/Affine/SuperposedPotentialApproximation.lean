/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.FiniteComponentPotential
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.SuperposedEnvelope
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.ConclusionAssembly

/-!
# SuperposedPotentialApproximation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Finite layer approximations of the superposed potential field

The full bad-component family need not be finite.  This file truncates it by
Whitney layer: the prefix at `N` contains every component active at a cube in a
layer `k < N`.  Such a prefix is finite, its slope defect is a zero-trace
potential field, and on every earlier layer its cell value agrees exactly with
the full superposed cell value.

The remaining cell defect has the same summable layer envelope, up to the
harmless factor from `vecNormSq_sub_le`.  The final `L²` closure argument is
kept in a separate file.
-/

namespace Algsuperdiff.Section3.Provider.Affine

open HCPolySupport Set
open Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.Percolation

noncomputable section

variable {d : ℕ}

/-! ## Finite prefixes of the bad component family -/

/-- The manuscript scale profile is at least one under its terminal lower
bound `3 ≤ k₀`. -/
theorem whitneyScale_one_le (M : ABKModel d) (m : ℤ) (E b : ℝ)
    (k₀ : ℕ) (omega : Cutoff.CutoffSample d) (hk₀ : 3 ≤ k₀) :
    ∀ j, 1 ≤ whitneyScale M m E b k₀ omega j := by
  intro j
  have h := add_le_whitneyScaleSeq b (hsep M m E b omega) k₀ j
  change 1 ≤ whitneyScaleSeq b (hsep M m E b omega) k₀ j
  omega

/-- A finite prefix of the actual bad components.  It contains the component
of every bad cube in layers `j ≤ N`.  The extra terminal layer is what makes
the prefix contain all components active at cubes in layers `k < N`. -/
noncomputable def badFamilyComponentPrefix (M : ABKModel d) (m : ℤ)
    (E b : ℝ) (k₀ : ℕ) (omega : Cutoff.CutoffSample d) (N : ℕ) :
    Finset (Set (TriadicCube d)) := by
  classical
  exact (Finset.range (N + 1)).biUnion fun j =>
    (badFamilyLayer M m (whitneyScale M m E b k₀ omega) j omega).image
      (badComponent
        (badFamily M m (whitneyScale M m E b k₀ omega) omega))

theorem badFamilyComponentPrefix_subset_badComponents
    (M : ABKModel d) (m : ℤ) (E b : ℝ) (k₀ : ℕ)
    (omega : Cutoff.CutoffSample d) (N : ℕ) :
    ∀ C ∈ badFamilyComponentPrefix M m E b k₀ omega N,
      C ∈ badComponents
        (badFamily M m (whitneyScale M m E b k₀ omega) omega) := by
  classical
  intro C hC
  rw [badFamilyComponentPrefix] at hC
  obtain ⟨j, -, hCj⟩ := Finset.mem_biUnion.mp hC
  obtain ⟨Q, hQ, hQC⟩ := Finset.mem_image.mp hCj
  rw [← hQC]
  exact badComponent_mem_badComponents
    ⟨⟨j, (mem_badFamilyLayer_iff.mp hQ).1⟩,
      (mem_badFamilyLayer_iff.mp hQ).2⟩

/-- Every component active at a cube in layer `k < N` occurs in the finite
bad-family prefix. -/
theorem activeComponent_mem_badFamilyComponentPrefix_of_lt
    {M : ABKModel d} {m : ℤ} {E b : ℝ} {k₀ : ℕ}
    {omega : Cutoff.CutoffSample d} (hk₀ : 3 ≤ k₀)
    {N k : ℕ} (hk : k < N) {Q : TriadicCube d}
    (hQ : Q ∈ whitneyLayer m (whitneyScale M m E b k₀ omega) k)
    {C : Set (TriadicCube d)}
    (hC : C ∈ activeComponents m (whitneyScale M m E b k₀ omega)
      (badFamily M m (whitneyScale M m E b k₀ omega) omega) Q) :
    C ∈ badFamilyComponentPrefix M m E b k₀ omega N := by
  classical
  obtain ⟨B, hB, htouch, hBC⟩ :=
    exists_mem_cubeTouch_badComponent_eq_of_mem_activeComponents hC
  obtain ⟨j, hBj⟩ := hB.1
  have hclose := mem_Icc_of_cubeTouch_of_mem_whitneyLayer
    (whitneyScale_one_le M m E b k₀ omega hk₀) hQ hBj htouch
  have hjN : j ≤ N := by
    have := (Finset.mem_Icc.mp hclose).1
    omega
  rw [badFamilyComponentPrefix]
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_range.mpr (by omega), ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨B, mem_badFamilyLayer_iff.mpr ⟨hBj, hB.2⟩, hBC⟩

/-- Every finite active-layer prefix gives a zero-trace potential field. -/
theorem potentialZeroTraceFieldOn_badFamily_activeComponentPrefix
    {M : ABKModel d} {m : ℤ} {E b : ℝ} {k₀ : ℕ}
    {omega : Cutoff.CutoffSample d} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hk₀ : 3 ≤ k₀) (hne : (hsepSet M m E b omega).Nonempty)
    (N : ℕ) (p : Vec d) :
    HCPolySupport.Book.Ch01.PotentialZeroTraceFieldOn
      (openCubeSet (originCube d m))
      (fun x => ∑ C ∈ badFamilyComponentPrefix M m E b k₀ omega N,
          (globalCompetitorSlope m
            (simplexScale m (whitneyScale M m E b k₀ omega)
              (componentWindowLayer m
                (whitneyScale M m E b k₀ omega) C)) C p x - p)) := by
  exact potentialZeroTraceFieldOn_sum_globalCompetitorSlope_sub_badComponents
    hb0 hb hk₀ hne _
      (badFamilyComponentPrefix_subset_badComponents M m E b k₀ omega N) p

/-! ## Cell bounds for arbitrary finite partial sums -/

private theorem badFamily_vecNormSq_componentCellSlope_sub_le_layerEnvelope
     {M : ABKModel d} {m : ℤ} {E b : ℝ} {k₀ : ℕ}
    {omega : Cutoff.CutoffSample d} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hk₀ : 3 ≤ k₀) (hne : (hsepSet M m E b omega).Nonempty)
    (p : Vec d) {k : ℕ} {Q : TriadicCube d}
    (hQ : Q ∈ whitneyLayer m (whitneyScale M m E b k₀ omega) k)
    {T : KuhnCell d}
    (hT : T ∈ whitneySimplexCells m
      (whitneyScale M m E b k₀ omega) k Q)
    {C : Set (TriadicCube d)}
    (hC : C ∈ activeComponents m
      (whitneyScale M m E b k₀ omega)
      (badFamily M m (whitneyScale M m E b k₀ omega) omega) Q) :
    vecNormSq (globalCompetitorCellSlope m
        (simplexScale m (whitneyScale M m E b k₀ omega)
          (componentWindowLayer m
            (whitneyScale M m E b k₀ omega) C)) C p T - p) ≤
      (648 * (d : ℝ)) ^ 2 *
        (3 : ℝ) ^ (2 * (b * ((k : ℝ) +
          (whitneyScale M m E b k₀ omega k : ℝ)))) * vecNormSq p :=
  vecNormSq_globalCompetitorCellSlope_sub_le_layerEnvelope hb0 hb hk₀
    (fun _ hh _ hu => badClusterDiam_lt_of_hsep_le hne hh hu)
    (fun _ hR => hR.1) (fun _ hR => hR.2) p hQ hT hC

/-- Any finite partial sum of bad-component cell defects obeys the full
superposed layer envelope.  Components inactive at the current Whitney cube
are removed before applying the multiplicity estimate. -/
theorem vecNormSq_sum_globalCompetitorCellSlope_sub_le_layerEnvelope
    [NeZero d] {M : ABKModel d} {m : ℤ} {E b : ℝ} {k₀ : ℕ}
    {omega : Cutoff.CutoffSample d} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hk₀ : 3 ≤ k₀) (hne : (hsepSet M m E b omega).Nonempty)
    (A : Finset (Set (TriadicCube d)))
    (hA : ∀ C ∈ A, C ∈ badComponents
      (badFamily M m (whitneyScale M m E b k₀ omega) omega))
    (p : Vec d) {k : ℕ} {Q : TriadicCube d}
    (hQ : Q ∈ whitneyLayer m (whitneyScale M m E b k₀ omega) k)
    {T : KuhnCell d}
    (hT : T ∈ whitneySimplexCells m
      (whitneyScale M m E b k₀ omega) k Q) :
    vecNormSq (∑ C ∈ A, (globalCompetitorCellSlope m
        (simplexScale m (whitneyScale M m E b k₀ omega)
          (componentWindowLayer m
            (whitneyScale M m E b k₀ omega) C)) C p T - p)) ≤
      superposedGradConst d ^ 2 *
        (3 : ℝ) ^ (2 * (b * ((k : ℝ) +
          (whitneyScale M m E b k₀ omega k : ℝ)))) * vecNormSq p := by
  classical
  let hn := whitneyScale M m E b k₀ omega
  let I := badFamily M m hn omega
  let B := A.filter fun C => C ∈ activeComponents m hn I Q
  have hn1 : ∀ j, 1 ≤ hn j :=
    whitneyScale_one_le M m E b k₀ omega hk₀
  have hmono : Monotone hn := by
    change Monotone (whitneyScaleSeq b (hsep M m E b omega) k₀)
    exact whitneyScaleSeq_mono hb0.le (by linarith) _ _
  have hgap : ∀ j, hn (j + 1) ≤ hn j + 1 := by
    intro j
    exact whitneyScaleSeq_succ_le hb0 hb (hsep M m E b omega) k₀ j
  have hI : I ⊆ whitneyPartition m hn := fun _ hR => hR.1
  have hwin := badComponents_window_badFamily hb0 hb hk₀ hne
  have hBsub : ∀ C ∈ B, C ∈ activeComponents m hn I Q := by
    intro C hC
    exact (Finset.mem_filter.mp hC).2
  have hcardNat : B.card ≤ multiplicityBound d :=
    card_le_multiplicityBound_of_forall_mem_activeComponents
      hn1 hmono hgap hI hQ hBsub
  have hcard : (B.card : ℝ) ≤ (multiplicityBound d : ℝ) := by
    exact_mod_cast hcardNat
  set X : ℝ := (648 * (d : ℝ)) ^ 2 *
    (3 : ℝ) ^ (2 * (b * ((k : ℝ) + (hn k : ℝ)))) * vecNormSq p with hX
  have hX0 : 0 ≤ X := by
    rw [hX]
    exact mul_nonneg
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by norm_num) _))
      (vecNormSq_nonneg p)
  have hterm : ∀ C ∈ B,
      vecNormSq (globalCompetitorCellSlope m
        (simplexScale m hn (componentWindowLayer m hn C)) C p T - p) ≤ X := by
    intro C hC
    rw [hX]
    exact badFamily_vecNormSq_componentCellSlope_sub_le_layerEnvelope
      hb0 hb hk₀ hne p hQ hT (hBsub C hC)
  have hrestrict :
      (∑ C ∈ A, (globalCompetitorCellSlope m
        (simplexScale m hn (componentWindowLayer m hn C)) C p T - p)) =
      ∑ C ∈ B, (globalCompetitorCellSlope m
        (simplexScale m hn (componentWindowLayer m hn C)) C p T - p) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro C hCA hCB
    have hCbad : C ∈ badComponents I := hA C hCA
    have hCnot : C ∉ activeComponents m hn I Q := by
      intro hCact
      exact hCB (Finset.mem_filter.mpr ⟨hCA, hCact⟩)
    rw [globalCompetitorCellSlope_eq_of_notMem_activeComponents
      hmono hI hwin p hQ hT hCbad hCnot, sub_self]
  have hsum : ∑ C ∈ B, vecNormSq (globalCompetitorCellSlope m
      (simplexScale m hn (componentWindowLayer m hn C)) C p T - p) ≤
      (B.card : ℝ) * X := by
    calc
      ∑ C ∈ B, vecNormSq (globalCompetitorCellSlope m
          (simplexScale m hn (componentWindowLayer m hn C)) C p T - p)
          ≤ ∑ _C ∈ B, X := Finset.sum_le_sum hterm
      _ = (B.card : ℝ) * X := by
        rw [Finset.sum_const, nsmul_eq_mul]
  rw [hrestrict]
  calc
    vecNormSq (∑ C ∈ B, (globalCompetitorCellSlope m
        (simplexScale m hn (componentWindowLayer m hn C)) C p T - p))
        ≤ (B.card : ℝ) * ∑ C ∈ B,
          vecNormSq (globalCompetitorCellSlope m
            (simplexScale m hn (componentWindowLayer m hn C)) C p T - p) :=
      vecNormSq_sum_le_card_mul_sum_vecNormSq _ _
    _ ≤ (B.card : ℝ) * ((B.card : ℝ) * X) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ ≤ (multiplicityBound d : ℝ) * ((B.card : ℝ) * X) :=
      mul_le_mul_of_nonneg_right hcard
        (mul_nonneg (Nat.cast_nonneg _) hX0)
    _ ≤ (multiplicityBound d : ℝ) * ((multiplicityBound d : ℝ) * X) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcard hX0) (Nat.cast_nonneg _)
    _ = superposedGradConst d ^ 2 *
        (3 : ℝ) ^ (2 * (b * ((k : ℝ) + (hn k : ℝ)))) * vecNormSq p := by
      rw [superposedGradConst, hX]
      ring

/-! ## Exactness and residual bounds -/

/-- On a cell in a layer below `N`, the full superposed cell defect is exactly
the finite prefix sum. -/
theorem superposedCompetitorCellSlope_sub_eq_activeComponentPrefix_sum
    [NeZero d] {M : ABKModel d} {m : ℤ} {E b : ℝ} {k₀ : ℕ}
    {omega : Cutoff.CutoffSample d} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hk₀ : 3 ≤ k₀) (hne : (hsepSet M m E b omega).Nonempty)
    {N k : ℕ} (hk : k < N) (p : Vec d) {Q : TriadicCube d}
    (hQ : Q ∈ whitneyLayer m (whitneyScale M m E b k₀ omega) k)
    {T : KuhnCell d}
    (hT : T ∈ whitneySimplexCells m
      (whitneyScale M m E b k₀ omega) k Q) :
    superposedCompetitorCellSlope m
        (whitneyScale M m E b k₀ omega)
        (badFamily M m (whitneyScale M m E b k₀ omega) omega) p T - p =
      ∑ C ∈ badFamilyComponentPrefix M m E b k₀ omega N,
        (globalCompetitorCellSlope m
          (simplexScale m (whitneyScale M m E b k₀ omega)
            (componentWindowLayer m
              (whitneyScale M m E b k₀ omega) C)) C p T - p) := by
  let hn := whitneyScale M m E b k₀ omega
  let I := badFamily M m hn omega
  have hmono : Monotone hn := by
    change Monotone (whitneyScaleSeq b (hsep M m E b omega) k₀)
    exact whitneyScaleSeq_mono hb0.le (by linarith) _ _
  have hI : I ⊆ whitneyPartition m hn := fun _ hR => hR.1
  have hwin := badComponents_window_badFamily hb0 hb hk₀ hne
  apply superposedCompetitorCellSlope_sub_eq_sum hmono hI hwin p hQ hT
  · exact badFamilyComponentPrefix_subset_badComponents M m E b k₀ omega N
  · intro C hC
    exact activeComponent_mem_badFamilyComponentPrefix_of_lt hk₀ hk hQ hC

/-! ## The half-rate decay available under `b ≤ 1/8` -/

/-- The layer mass beats the squared collar growth at geometric rate
`3^{-k/2}` under the source window `b ≤ 1/8`.  This deliberately uses a weaker
rate than `three_rpow_layerQuantity_decay`, whose `4 α` gate is unnecessary for
the present `L²` closure argument. -/
theorem three_rpow_layerQuantity_half_decay {b : ℝ}
    (hb0 : 0 < b) (hb : b ≤ 1 / 8) (hs k₀ k : ℕ) :
    (3 : ℝ) ^ (-(k : ℝ)) *
        (3 : ℝ) ^ (2 * b *
          Multiscale.layerQuantity b hs k₀ k) ≤
      (3 : ℝ) ^ (2 * b * ((hs : ℝ) + (k₀ : ℝ) + 1)) *
        ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ k := by
  have hb1 : b < 1 := by linarith
  have h1b : (0 : ℝ) < 1 - b := by linarith
  have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hcoef : 2 * b * (1 - b)⁻¹ ≤ 1 / 2 := by
    have hbase : 2 * b ≤ (1 - b) / 2 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hbase
      (le_of_lt (inv_pos.2 h1b))
    have hcancel : ((1 - b) / 2) * (1 - b)⁻¹ = 1 / 2 := by
      field_simp
    linarith
  have hmul : 2 * b * Multiscale.layerQuantity b hs k₀ k ≤
      2 * b * ((1 - b)⁻¹ * (k : ℝ) +
        ((hs : ℝ) + (k₀ : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left
      (Multiscale.layerQuantity_le hb0 hb1 hs k₀ k) (by linarith)
  have hexp : 2 * b * ((1 - b)⁻¹ * (k : ℝ) +
      ((hs : ℝ) + (k₀ : ℝ) + 1)) =
      2 * b * (1 - b)⁻¹ * (k : ℝ) +
        2 * b * ((hs : ℝ) + (k₀ : ℝ) + 1) := by
    ring
  have hstep : 2 * b * (1 - b)⁻¹ * (k : ℝ) ≤
      1 / 2 * (k : ℝ) :=
    mul_le_mul_of_nonneg_right hcoef hknn
  have hkey : 2 * b * Multiscale.layerQuantity b hs k₀ k - (k : ℝ) ≤
      2 * b * ((hs : ℝ) + (k₀ : ℝ) + 1) +
        (-(1 / 2 : ℝ)) * (k : ℝ) := by
    linarith [hmul, hstep, hexp.le, hexp.ge]
  calc
    (3 : ℝ) ^ (-(k : ℝ)) *
        (3 : ℝ) ^ (2 * b * Multiscale.layerQuantity b hs k₀ k) =
      (3 : ℝ) ^
        (2 * b * Multiscale.layerQuantity b hs k₀ k - (k : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    _ ≤ (3 : ℝ) ^ (2 * b * ((hs : ℝ) + (k₀ : ℝ) + 1) +
        (-(1 / 2 : ℝ)) * (k : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hkey
    _ = (3 : ℝ) ^ (2 * b * ((hs : ℝ) + (k₀ : ℝ) + 1)) *
        ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ k := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3),
        Multiscale.three_rpow_pow_eq]

end


end Algsuperdiff.Section3.Provider.Affine
