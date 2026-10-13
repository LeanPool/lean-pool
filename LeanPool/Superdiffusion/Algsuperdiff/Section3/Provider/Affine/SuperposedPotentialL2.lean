/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.SuperposedPotentialApproximation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.ConclusionSeam1PerCube
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalL2Realization

/-!
# SuperposedPotentialL2

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The full superposed slope defect is a zero-trace potential field

Finite Whitney-layer prefixes of the bad-component superposition are genuine
zero-trace potential fields.  This file proves that those prefixes are Cauchy
in `L²`, identifies their limit almost everywhere with the full superposed
slope defect, and uses the closed-range realization on the open root cube.

The `L²` argument is non-circular: every integral used in the Cauchy estimate
is an integral of a difference of two finite prefixes, whose `MemVectorL2`
witnesses are already supplied by the finite potential theorem.
-/

namespace Algsuperdiff.Section3.Provider.Affine

open HCPolySupport Set MeasureTheory
open Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Multiscale

noncomputable section

variable {d : ℕ}

/-! ## The finite fields and their cell constants -/

/-- The finite bad-component slope defect obtained by truncating in Whitney
layer. -/
def badFamilyPotentialApproximation (M : ABKModel d) (m : ℤ)
    (E b : ℝ) (k₀ : ℕ) (omega : Cutoff.CutoffSample d) (N : ℕ)
    (p : Vec d) : Vec d → Vec d := fun x =>
  ∑ C ∈ badFamilyComponentPrefix M m E b k₀ omega N,
    (globalCompetitorSlope m
      (simplexScale m (whitneyScale M m E b k₀ omega)
        (componentWindowLayer m
          (whitneyScale M m E b k₀ omega) C)) C p x - p)

/-- The cell constant associated with a finite bad-component prefix. -/
def badFamilyPotentialApproximationCell (M : ABKModel d) (m : ℤ)
    (E b : ℝ) (k₀ : ℕ) (omega : Cutoff.CutoffSample d) (N : ℕ)
    (p : Vec d) (T : KuhnCell d) : Vec d :=
  ∑ C ∈ badFamilyComponentPrefix M m E b k₀ omega N,
    (globalCompetitorCellSlope m
      (simplexScale m (whitneyScale M m E b k₀ omega)
        (componentWindowLayer m
          (whitneyScale M m E b k₀ omega) C)) C p T - p)

private theorem window_layer_for_globalCompetitor
    {m : ℤ} {hn : ℕ → ℕ} (hmono : Monotone hn)
    {C : Set (TriadicCube d)} (hfin : (whitneyNeighborhood m hn C).Finite)
    (hlayer : ∀ R ∈ whitneyNeighborhood m hn C,
      R ∈ whitneyLayer m hn (componentWindowLayer m hn C) ∨
        R ∈ whitneyLayer m hn (componentWindowLayer m hn C + 1)) :
    ∀ Q ∈ hfin.toFinset, ∀ n : ℕ, Q ∈ whitneyLayer m hn n →
      n = componentWindowLayer m hn C ∨
        n = componentWindowLayer m hn C + 1 := by
  intro Q hQ n hQn
  rcases hlayer Q ((Set.Finite.mem_toFinset hfin).mp hQ) with h | h
  · exact Or.inl (whitneyLayer_index_unique hmono hQn h)
  · exact Or.inr (whitneyLayer_index_unique hmono hQn h)

private theorem globalCompetitorSlope_eq_cellSlope_of_badComponent
    [NeZero d] {m : ℤ} {hn : ℕ → ℕ} (hmono : Monotone hn)
    {I : Set (TriadicCube d)} (hI : I ⊆ whitneyPartition m hn)
    (hwin : ∀ C ∈ badComponents I,
      (whitneyNeighborhood m hn C).Finite ∧
        ∀ R ∈ whitneyNeighborhood m hn C,
          R ∈ whitneyLayer m hn (componentWindowLayer m hn C) ∨
            R ∈ whitneyLayer m hn (componentWindowLayer m hn C + 1))
    {C : Set (TriadicCube d)} (hC : C ∈ badComponents I) (p : Vec d)
    {T : KuhnCell d} (hT : T ∈ simplexPartition m hn) :
    ∀ x ∈ T.openCarrier,
      globalCompetitorSlope m
          (simplexScale m hn (componentWindowLayer m hn C)) C p x =
        globalCompetitorCellSlope m
          (simplexScale m hn (componentWindowLayer m hn C)) C p T := by
  exact (globalCompetitorSlope_eq_cellSlope
    (step_of_monotone hmono)
    (step_of_monotone hmono (componentWindowLayer m hn C + 1))
    ((badComponents_subset hC).trans hI)
    (fun _ => Set.Finite.mem_toFinset (hwin C hC).1)
    (window_layer_for_globalCompetitor hmono (hwin C hC).1 (hwin C hC).2)
    p hT).1

/-- A finite prefix is constant on every open simplex cell, with the advertised
finite cell sum as its value. -/
theorem badFamilyPotentialApproximation_eq_cell
    [NeZero d] {M : ABKModel d} {m : ℤ} {E b : ℝ} {k₀ N : ℕ}
    {omega : Cutoff.CutoffSample d} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hk₀ : 3 ≤ k₀) (hne : (hsepSet M m E b omega).Nonempty)
    (p : Vec d) {T : KuhnCell d}
    (hT : T ∈ simplexPartition m (whitneyScale M m E b k₀ omega)) :
    ∀ x ∈ T.openCarrier,
      badFamilyPotentialApproximation M m E b k₀ omega N p x =
        badFamilyPotentialApproximationCell M m E b k₀ omega N p T := by
  classical
  let hn := whitneyScale M m E b k₀ omega
  let I := badFamily M m hn omega
  have hmono : Monotone hn := by
    change Monotone (whitneyScaleSeq b (hsep M m E b omega) k₀)
    exact whitneyScaleSeq_mono hb0.le (by linarith) _ _
  have hI : I ⊆ whitneyPartition m hn := fun _ hR => hR.1
  have hwin := badComponents_window_badFamily hb0 hb hk₀ hne
  intro x hx
  simp only [badFamilyPotentialApproximation,
    badFamilyPotentialApproximationCell]
  apply Finset.sum_congr rfl
  intro C hC
  rw [globalCompetitorSlope_eq_cellSlope_of_badComponent hmono hI hwin
    (badFamilyComponentPrefix_subset_badComponents M m E b k₀ omega N C hC)
    p hT x hx]

/-- The difference of two finite prefixes obeys the same layer envelope, up to
the elementary factor from `vecNormSq_sub_le`. -/
theorem vecNormSq_badFamilyPotentialApproximationCell_sub_le_layerEnvelope
    [NeZero d] {M : ABKModel d} {m : ℤ} {E b : ℝ} {k₀ : ℕ}
    {omega : Cutoff.CutoffSample d} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hk₀ : 3 ≤ k₀) (hne : (hsepSet M m E b omega).Nonempty)
    (N N' : ℕ) (p : Vec d) {k : ℕ} {Q : TriadicCube d}
    (hQ : Q ∈ whitneyLayer m (whitneyScale M m E b k₀ omega) k)
    {T : KuhnCell d}
    (hT : T ∈ whitneySimplexCells m
      (whitneyScale M m E b k₀ omega) k Q) :
    vecNormSq (badFamilyPotentialApproximationCell M m E b k₀ omega N p T -
      badFamilyPotentialApproximationCell M m E b k₀ omega N' p T) ≤
      (2 * superposedGradConst d) ^ 2 *
        (3 : ℝ) ^ (2 * (b * ((k : ℝ) +
          (whitneyScale M m E b k₀ omega k : ℝ)))) * vecNormSq p := by
  have hN := vecNormSq_sum_globalCompetitorCellSlope_sub_le_layerEnvelope
    hb0 hb hk₀ hne (badFamilyComponentPrefix M m E b k₀ omega N)
    (badFamilyComponentPrefix_subset_badComponents M m E b k₀ omega N)
    p hQ hT
  have hN' := vecNormSq_sum_globalCompetitorCellSlope_sub_le_layerEnvelope
    hb0 hb hk₀ hne (badFamilyComponentPrefix M m E b k₀ omega N')
    (badFamilyComponentPrefix_subset_badComponents M m E b k₀ omega N')
    p hQ hT
  simp only [badFamilyPotentialApproximationCell]
  calc
    vecNormSq ((∑ C ∈ badFamilyComponentPrefix M m E b k₀ omega N,
        (globalCompetitorCellSlope m
          (simplexScale m (whitneyScale M m E b k₀ omega)
            (componentWindowLayer m
              (whitneyScale M m E b k₀ omega) C)) C p T - p)) -
      ∑ C ∈ badFamilyComponentPrefix M m E b k₀ omega N',
        (globalCompetitorCellSlope m
          (simplexScale m (whitneyScale M m E b k₀ omega)
            (componentWindowLayer m
              (whitneyScale M m E b k₀ omega) C)) C p T - p))
        ≤ 2 * vecNormSq (∑ C ∈ badFamilyComponentPrefix M m E b k₀ omega N,
          (globalCompetitorCellSlope m
            (simplexScale m (whitneyScale M m E b k₀ omega)
              (componentWindowLayer m
                (whitneyScale M m E b k₀ omega) C)) C p T - p)) +
          2 * vecNormSq (∑ C ∈ badFamilyComponentPrefix M m E b k₀ omega N',
            (globalCompetitorCellSlope m
              (simplexScale m (whitneyScale M m E b k₀ omega)
                (componentWindowLayer m
                  (whitneyScale M m E b k₀ omega) C)) C p T - p)) :=
      by simpa [mul_add] using (vecNormSq_sub_le
        (∑ C ∈ badFamilyComponentPrefix M m E b k₀ omega N,
          (globalCompetitorCellSlope m
            (simplexScale m (whitneyScale M m E b k₀ omega)
              (componentWindowLayer m
                (whitneyScale M m E b k₀ omega) C)) C p T - p))
        (∑ C ∈ badFamilyComponentPrefix M m E b k₀ omega N',
          (globalCompetitorCellSlope m
            (simplexScale m (whitneyScale M m E b k₀ omega)
              (componentWindowLayer m
                (whitneyScale M m E b k₀ omega) C)) C p T - p)))
    _ ≤ 2 * (superposedGradConst d ^ 2 *
          (3 : ℝ) ^ (2 * (b * ((k : ℝ) +
            (whitneyScale M m E b k₀ omega k : ℝ)))) * vecNormSq p) +
        2 * (superposedGradConst d ^ 2 *
          (3 : ℝ) ^ (2 * (b * ((k : ℝ) +
            (whitneyScale M m E b k₀ omega k : ℝ)))) * vecNormSq p) :=
      add_le_add (mul_le_mul_of_nonneg_left hN (by norm_num))
        (mul_le_mul_of_nonneg_left hN' (by norm_num))
    _ = (2 * superposedGradConst d) ^ 2 *
        (3 : ℝ) ^ (2 * (b * ((k : ℝ) +
          (whitneyScale M m E b k₀ omega k : ℝ)))) * vecNormSq p := by
      ring_nf

/-- Below the smaller cutoff, two finite prefixes have identical cell value. -/
theorem badFamilyPotentialApproximationCell_eq_of_layer_lt
    [NeZero d] {M : ABKModel d} {m : ℤ} {E b : ℝ} {k₀ : ℕ}
    {omega : Cutoff.CutoffSample d} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hk₀ : 3 ≤ k₀) (hne : (hsepSet M m E b omega).Nonempty)
    {N N' k : ℕ} (hkN : k < N) (hkN' : k < N') (p : Vec d)
    {Q : TriadicCube d}
    (hQ : Q ∈ whitneyLayer m (whitneyScale M m E b k₀ omega) k)
    {T : KuhnCell d}
    (hT : T ∈ whitneySimplexCells m
      (whitneyScale M m E b k₀ omega) k Q) :
    badFamilyPotentialApproximationCell M m E b k₀ omega N p T =
      badFamilyPotentialApproximationCell M m E b k₀ omega N' p T := by
  have hN := superposedCompetitorCellSlope_sub_eq_activeComponentPrefix_sum
    hb0 hb hk₀ hne hkN p hQ hT
  have hN' := superposedCompetitorCellSlope_sub_eq_activeComponentPrefix_sum
    hb0 hb hk₀ hne hkN' p hQ hT
  simpa only [badFamilyPotentialApproximationCell] using hN.symm.trans hN'

/-! ## The `L²` increment estimate -/

/-- The canonical `VectorL2` class of a finite prefix. -/
noncomputable def badFamilyPotentialApproximationL2
    {M : ABKModel d} {m : ℤ} {E b : ℝ} {k₀ : ℕ}
    {omega : Cutoff.CutoffSample d} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hk₀ : 3 ≤ k₀) (hne : (hsepSet M m E b omega).Nonempty)
    (N : ℕ) (p : Vec d) :
    VectorL2 (openCubeSet (originCube d m)) :=
  toVectorL2
    (potentialZeroTraceFieldOn_badFamily_activeComponentPrefix
      hb0 hb hk₀ hne N p).1

private theorem tsum_geometric_indicator_ge {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    (∑' k : ℕ, if N ≤ k then r ^ k else 0) =
      r ^ N * (1 - r)⁻¹ := by
  have hs : Summable fun k : ℕ => if N ≤ k then r ^ k else 0 := by
    simpa only [← Set.piecewise_eq_indicator]
      using! (summable_geometric_of_lt_one hr0 hr1).indicator {k | N ≤ k}
  have hz : (∑ k ∈ Finset.range N, if N ≤ k then r ^ k else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [ite_eq_right]
    exact Nat.not_le_of_lt (Finset.mem_range.mp hk)
  rw [← hs.sum_add_tsum_nat_add N, hz, zero_add]
  simp only [Nat.le_add_left, ite_true, pow_add]
  rw [tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1]
  ring_nf

private theorem badFamilyPotentialIncrement_integrable
    {M : ABKModel d} {m : ℤ} {E b : ℝ} {k₀ : ℕ}
    {omega : Cutoff.CutoffSample d} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hk₀ : 3 ≤ k₀) (hne : (hsepSet M m E b omega).Nonempty)
    (N : ℕ) (p : Vec d) :
    IntegrableOn (fun x => vecNormSq
      (badFamilyPotentialApproximation M m E b k₀ omega N p x -
        badFamilyPotentialApproximation M m E b k₀ omega (N + 1) p x))
      (openCubeSet (originCube d m)) volume := by
  have hN := potentialZeroTraceFieldOn_badFamily_activeComponentPrefix
    hb0 hb hk₀ hne N p
  have hNs := potentialZeroTraceFieldOn_badFamily_activeComponentPrefix
    hb0 hb hk₀ hne (N + 1) p
  simpa only [vecNormSq, badFamilyPotentialApproximation] using!
    integrableOn_vecDot_of_memVectorL2 (hN.1.sub hNs.1) (hN.1.sub hNs.1)

/-- The squared finite-prefix increment, integrated over the root cube, has a
geometrically decaying upper bound. -/
theorem integral_vecNormSq_badFamilyPotentialApproximation_sub_succ_le
    {M : ABKModel d} {m : ℤ} {E b : ℝ} {k₀ : ℕ}
    {omega : Cutoff.CutoffSample d} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hk₀ : 3 ≤ k₀) (hne : (hsepSet M m E b omega).Nonempty)
    (N : ℕ) (p : Vec d) :
    ∫ x in openCubeSet (originCube d m), vecNormSq
        (badFamilyPotentialApproximation M m E b k₀ omega N p x -
          badFamilyPotentialApproximation M m E b k₀ omega (N + 1) p x)
        ∂volume ≤
      cubeVolume (originCube d m) *
        (6 * (d : ℝ) * (2 * superposedGradConst d) ^ 2 * vecNormSq p *
          (3 : ℝ) ^ (2 * b *
            ((hsep M m E b omega : ℝ) + (k₀ : ℝ) + 1))) *
        ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ N *
        (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ := by
  classical
  let hn := whitneyScale M m E b k₀ omega
  let U := openCubeSet (originCube d m)
  let fN := badFamilyPotentialApproximation M m E b k₀ omega N p
  let fNs := badFamilyPotentialApproximation M m E b k₀ omega (N + 1) p
  let e : KuhnCell d → ℝ := fun T =>
    vecNormSq (badFamilyPotentialApproximationCell M m E b k₀ omega N p T -
      badFamilyPotentialApproximationCell M m E b k₀ omega (N + 1) p T)
  let A : ℝ := 6 * (d : ℝ) * (2 * superposedGradConst d) ^ 2 *
    vecNormSq p * (3 : ℝ) ^ (2 * b *
      ((hsep M m E b omega : ℝ) + (k₀ : ℝ) + 1))
  let r : ℝ := (3 : ℝ) ^ (-(1 / 2 : ℝ))
  have : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  have hmono : Monotone hn := by
    change Monotone (whitneyScaleSeq b (hsep M m E b omega) k₀)
    exact whitneyScaleSeq_mono hb0.le (by linarith) _ _
  have hstep : ∀ k, hn k ≤ hn (k + 1) + 1 := step_of_monotone hmono
  have hr0 : 0 ≤ r := by
    exact Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
          (sq_nonneg _))
        (vecNormSq_nonneg p))
      (Real.rpow_nonneg (by norm_num) _)
  have he0 : ∀ T, 0 ≤ e T := fun T => vecNormSq_nonneg _
  have hcellWeight0 : ∀ T : KuhnCell d, 0 ≤ cellWeight m T :=
    fun T => cellWeight_nonneg m T
  let F : KuhnCell d → ENNReal := fun T => ENNReal.ofReal (cellWeight m T * e T)
  let g : ℕ → ℝ := fun k => if N ≤ k then A * r ^ k else 0
  have hg0 : ∀ k, 0 ≤ g k := by
    intro k
    dsimp [g]
    split_ifs
    · exact mul_nonneg hA0 (pow_nonneg hr0 _)
    · exact le_rfl
  have hgsum : Summable g := by
    have hs := (summable_geometric_of_lt_one hr0 hr1).indicator {k | N ≤ k}
    refine (hs.mul_left A).congr fun k => ?_
    by_cases hk : N ≤ k <;> simp [g, Set.indicator, hk]
  have hlayerReal : ∀ k : ℕ,
      ∑ Q ∈ whitneyLayer (d := d) m hn k,
          ∑ T ∈ whitneySimplexCells m hn k Q, cellWeight m T * e T ≤ g k := by
    intro k
    by_cases hk : k < N
    · have heq0 : ∀ Q ∈ whitneyLayer (d := d) m hn k,
          ∀ T ∈ whitneySimplexCells m hn k Q, e T = 0 := by
        intro Q hQ T hT
        dsimp [e]
        have heq :
            badFamilyPotentialApproximationCell M m E b k₀ omega N p T =
              badFamilyPotentialApproximationCell M m E b k₀ omega (N + 1) p T :=
          badFamilyPotentialApproximationCell_eq_of_layer_lt
            hb0 hb hk₀ hne hk (by omega) p hQ hT
        rw [heq, sub_self]
        simp [vecNormSq, vecDot]
      calc
        ∑ Q ∈ whitneyLayer (d := d) m hn k,
            ∑ T ∈ whitneySimplexCells m hn k Q, cellWeight m T * e T = 0 := by
          apply Finset.sum_eq_zero
          intro Q hQ
          apply Finset.sum_eq_zero
          intro T hT
          rw [heq0 Q hQ T hT, mul_zero]
        _ ≤ g k := hg0 k
    · have hkN : N ≤ k := Nat.le_of_not_gt hk
      let X : ℝ := (2 * superposedGradConst d) ^ 2 *
        (3 : ℝ) ^ (2 * (b * ((k : ℝ) + (hn k : ℝ)))) * vecNormSq p
      have hX0 : 0 ≤ X := by
        dsimp [X]
        exact mul_nonneg
          (mul_nonneg (sq_nonneg _)
            (Real.rpow_nonneg (by norm_num) _))
          (vecNormSq_nonneg p)
      have hcell : ∀ Q ∈ whitneyLayer (d := d) m hn k,
          ∀ T ∈ whitneySimplexCells m hn k Q, e T ≤ X := by
        intro Q hQ T hT
        exact vecNormSq_badFamilyPotentialApproximationCell_sub_le_layerEnvelope
          hb0 hb hk₀ hne N (N + 1) p hQ hT
      have hsumCell : ∀ Q ∈ whitneyLayer (d := d) m hn k,
          ∑ T ∈ whitneySimplexCells m hn k Q, cellWeight m T * e T ≤
            cubeMassRatio (originCube d m) Q * X := by
        intro Q hQ
        calc
          ∑ T ∈ whitneySimplexCells m hn k Q, cellWeight m T * e T ≤
              ∑ T ∈ whitneySimplexCells m hn k Q, cellWeight m T * X :=
            Finset.sum_le_sum fun T hT =>
              mul_le_mul_of_nonneg_left (hcell Q hQ T hT) (hcellWeight0 T)
          _ = (∑ T ∈ whitneySimplexCells m hn k Q, cellWeight m T) * X := by
            rw [Finset.sum_mul]
          _ = cubeMassRatio (originCube d m) Q * X := by
            rw [sum_cellWeight_whitneySimplexCells_eq (hstep k) hQ]
      have hmass :
          ∑ Q ∈ whitneyLayer (d := d) m hn k,
              cubeMassRatio (originCube d m) Q ≤
            6 * (d : ℝ) * (3 : ℝ) ^ (-(k : ℝ)) :=
        sum_cubeMassRatio_whitneyLayer_le m hn k
      have hdecay := three_rpow_layerQuantity_half_decay
        hb0 hb (hsep M m E b omega) k₀ k
      have hquantity : ((k : ℝ) + (hn k : ℝ)) =
          layerQuantity b (hsep M m E b omega) k₀ k := by
        rfl
      calc
        ∑ Q ∈ whitneyLayer (d := d) m hn k,
            ∑ T ∈ whitneySimplexCells m hn k Q, cellWeight m T * e T ≤
            ∑ Q ∈ whitneyLayer (d := d) m hn k,
              cubeMassRatio (originCube d m) Q * X :=
          Finset.sum_le_sum hsumCell
        _ = (∑ Q ∈ whitneyLayer (d := d) m hn k,
              cubeMassRatio (originCube d m) Q) * X := by
          rw [Finset.sum_mul]
        _ ≤ (6 * (d : ℝ) * (3 : ℝ) ^ (-(k : ℝ))) * X :=
          mul_le_mul_of_nonneg_right hmass hX0
        _ ≤ A * r ^ k := by
          let C : ℝ := 6 * (d : ℝ) * (2 * superposedGradConst d) ^ 2 *
            vecNormSq p
          have hC0 : 0 ≤ C := by
            dsimp [C]
            exact mul_nonneg
              (mul_nonneg
                (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
                (sq_nonneg _))
              (vecNormSq_nonneg p)
          calc
            (6 * (d : ℝ) * (3 : ℝ) ^ (-(k : ℝ))) * X =
                C * ((3 : ℝ) ^ (-(k : ℝ)) *
                  (3 : ℝ) ^ (2 * b *
                    layerQuantity b (hsep M m E b omega) k₀ k)) := by
              dsimp [X, C]
              rw [hquantity]
              ring_nf
            _ ≤ C * ((3 : ℝ) ^ (2 * b *
                  ((hsep M m E b omega : ℝ) + (k₀ : ℝ) + 1)) *
                ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ k) :=
              mul_le_mul_of_nonneg_left hdecay hC0
            _ = A * r ^ k := by
              dsimp [C, A, r]
              ring_nf
        _ = g k := by simp [g, hkN]
  have hlayer : ∀ k : ℕ,
      ∑ Q ∈ whitneyLayer (d := d) m hn k,
          ∑ T ∈ whitneySimplexCells m hn k Q, F T ≤ ENNReal.ofReal (g k) := by
    intro k
    have hconvert : ENNReal.ofReal
        (∑ Q ∈ whitneyLayer (d := d) m hn k,
          ∑ T ∈ whitneySimplexCells m hn k Q, cellWeight m T * e T) =
        ∑ Q ∈ whitneyLayer (d := d) m hn k,
          ∑ T ∈ whitneySimplexCells m hn k Q, F T := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro Q hQ
        dsimp [F]
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro T hT
        exact mul_nonneg (hcellWeight0 T) (he0 T)
      · intro Q hQ
        exact Finset.sum_nonneg fun T hT =>
          mul_nonneg (hcellWeight0 T) (he0 T)
    rw [← hconvert]
    exact ENNReal.ofReal_le_ofReal (hlayerReal k)
  have hweighted := toReal_tsum_simplexPartition_le_tsum hmono F hg0 hgsum hlayer
  have hgtsum : (∑' k : ℕ, g k) = A * r ^ N * (1 - r)⁻¹ := by
    calc
      (∑' k : ℕ, g k) =
          A * (∑' k : ℕ, if N ≤ k then r ^ k else 0) := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro k
        by_cases hk : N ≤ k <;> simp [g, hk]
      _ = A * r ^ N * (1 - r)⁻¹ := by
        rw [tsum_geometric_indicator_ge hr0 hr1 N]
        ring_nf
  rw [hgtsum] at hweighted
  have hInt := badFamilyPotentialIncrement_integrable hb0 hb hk₀ hne N p
  have hUnionSub : (⋃ T : ↑(simplexPartition (d := d) m hn), T.1.openCarrier) ⊆ U := by
    intro x hx
    obtain ⟨T, hxT⟩ := Set.mem_iUnion.mp hx
    have hxCarrier : x ∈ T.1.carrier := T.1.openCarrier_subset_carrier hxT
    dsimp [U]
    rw [← iUnion_carrier_simplexPartition_eq_openCubeSet hstep]
    exact Set.mem_iUnion.mpr ⟨T.1, Set.mem_iUnion.mpr ⟨T.2, hxCarrier⟩⟩
  have haeSet : U =ᵐ[volume]
      ⋃ T : ↑(simplexPartition (d := d) m hn), T.1.openCarrier := by
    apply MeasureTheory.ae_eq_set.mpr
    constructor
    · dsimp [U]
      simpa only [Set.iUnion_subtype] using
        volume_openCubeSet_diff_iUnion_openCarrier hstep
    · rw [Set.sdiff_eq_empty.mpr hUnionSub]
      exact measure_empty
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun T : ↑(simplexPartition (d := d) m hn) => T.1.openCarrier)) := by
    intro T T' hTT'
    exact (simplexPartition_pairwiseDisjoint T.2 T'.2
      (Subtype.coe_ne_coe.mpr hTT')).mono
        T.1.openCarrier_subset_carrier T'.1.openCarrier_subset_carrier
  have hHasSum : HasSum (fun T : ↑(simplexPartition (d := d) m hn) =>
      ∫ x in T.1.openCarrier, vecNormSq (fN x - fNs x) ∂volume)
      (∫ x in U, vecNormSq (fN x - fNs x) ∂volume) := by
    have h := MeasureTheory.hasSum_integral_iUnion
      (f := fun x => vecNormSq (fN x - fNs x))
      (fun T : ↑(simplexPartition (d := d) m hn) =>
        (isOpen_openCarrier T.1).measurableSet)
      hdisj (hInt.mono_set hUnionSub)
    rwa [← MeasureTheory.setIntegral_congr_set haeSet] at h
  have hcellIntegral : ∀ T : ↑(simplexPartition (d := d) m hn),
      (∫ x in T.1.openCarrier, vecNormSq (fN x - fNs x) ∂volume) =
        cubeVolume (originCube d m) * (cellWeight m T.1 * e T.1) := by
    intro T
    have hconst : ∀ x ∈ T.1.openCarrier,
        vecNormSq (fN x - fNs x) = e T.1 := by
      intro x hx
      dsimp [fN, fNs, e]
      rw [badFamilyPotentialApproximation_eq_cell hb0 hb hk₀ hne p T.2 x hx,
        badFamilyPotentialApproximation_eq_cell hb0 hb hk₀ hne p T.2 x hx]
    rw [MeasureTheory.setIntegral_congr_fun
      (isOpen_openCarrier T.1).measurableSet hconst,
      MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
      smul_eq_mul, cellWeight, volume_openCubeSet_toReal]
    field_simp [(cubeVolume_pos (originCube d m)).ne']
  have hIntegralEq :
      (∫ x in U, vecNormSq (fN x - fNs x) ∂volume) =
        cubeVolume (originCube d m) *
          (∑' T : ↑(simplexPartition (d := d) m hn), cellWeight m T.1 * e T.1) := by
    rw [← hHasSum.tsum_eq, tsum_congr hcellIntegral, tsum_mul_left]
  have htoReal :
      (∑' T : ↑(simplexPartition (d := d) m hn), cellWeight m T.1 * e T.1) =
        (∑' T : ↑(simplexPartition (d := d) m hn), F T.1).toReal := by
    rw [ENNReal.tsum_toReal_eq]
    apply tsum_congr
    intro T
    dsimp [F]
    rw [ENNReal.toReal_ofReal]
    exact mul_nonneg (hcellWeight0 T.1) (he0 T.1)
    intro T
    exact ENNReal.ofReal_ne_top
  rw [hIntegralEq, htoReal]
  refine mul_le_mul_of_nonneg_left hweighted (cubeVolume_pos _).le |>.trans_eq ?_
  dsimp [A, r]
  ring_nf

def badFamilyPotentialIncrementConst
    (M : ABKModel d) (m : ℤ) (E b : ℝ) (k₀ : ℕ)
    (omega : Cutoff.CutoffSample d) (p : Vec d) : ℝ :=
  cubeVolume (originCube d m) *
    (6 * (d : ℝ) * (2 * superposedGradConst d) ^ 2 * vecNormSq p *
      (3 : ℝ) ^ (2 * b *
        ((hsep M m E b omega : ℝ) + (k₀ : ℝ) + 1))) *
    (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹

private theorem badFamilyPotentialIncrementConst_nonneg
    (M : ABKModel d) (m : ℤ) (E b : ℝ) (k₀ : ℕ)
    (omega : Cutoff.CutoffSample d) (p : Vec d) :
    0 ≤ badFamilyPotentialIncrementConst M m E b k₀ omega p := by
  have hrlt : (3 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hmain : 0 ≤ 6 * (d : ℝ) * (2 * superposedGradConst d) ^ 2 *
      vecNormSq p * (3 : ℝ) ^ (2 * b *
        ((hsep M m E b omega : ℝ) + (k₀ : ℝ) + 1)) := by
    have h1 : 0 ≤ (6 : ℝ) * (d : ℝ) :=
      mul_nonneg (by norm_num) (Nat.cast_nonneg d)
    have h2 : 0 ≤ (6 : ℝ) * (d : ℝ) *
        (2 * superposedGradConst d) ^ 2 := mul_nonneg h1 (sq_nonneg _)
    have h3 : 0 ≤ (6 : ℝ) * (d : ℝ) *
        (2 * superposedGradConst d) ^ 2 * vecNormSq p :=
      mul_nonneg h2 (vecNormSq_nonneg p)
    exact mul_nonneg h3 (Real.rpow_nonneg (by norm_num) _)
  dsimp [badFamilyPotentialIncrementConst]
  exact mul_nonneg (mul_nonneg (cubeVolume_pos _).le hmain)
    (inv_nonneg.mpr (sub_nonneg.mpr hrlt.le))

/-- Consecutive finite-prefix classes have a summable geometric distance
majorant. -/
theorem dist_badFamilyPotentialApproximationL2_succ_le
    {M : ABKModel d} {m : ℤ} {E b : ℝ} {k₀ : ℕ}
    {omega : Cutoff.CutoffSample d} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hk₀ : 3 ≤ k₀) (hne : (hsepSet M m E b omega).Nonempty)
    (N : ℕ) (p : Vec d) :
    dist (badFamilyPotentialApproximationL2 hb0 hb hk₀ hne N p)
        (badFamilyPotentialApproximationL2 hb0 hb hk₀ hne (N + 1) p) ≤
      Real.sqrt (badFamilyPotentialIncrementConst M m E b k₀ omega p) *
        ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ N := by
  let hN := potentialZeroTraceFieldOn_badFamily_activeComponentPrefix
    hb0 hb hk₀ hne N p
  let hNs := potentialZeroTraceFieldOn_badFamily_activeComponentPrefix
    hb0 hb hk₀ hne (N + 1) p
  let hd : MemVectorL2 (openCubeSet (originCube d m))
      (badFamilyPotentialApproximation M m E b k₀ omega N p -
        badFamilyPotentialApproximation M m E b k₀ omega (N + 1) p) :=
    hN.1.sub hNs.1
  let H := toHilbertVectorL2OfVecField hd
  let B := badFamilyPotentialIncrementConst M m E b k₀ omega p
  let r : ℝ := (3 : ℝ) ^ (-(1 / 2 : ℝ))
  let t : ℝ := (3 : ℝ) ^ (-(1 / 4 : ℝ))
  have hB0 : 0 ≤ B :=
    badFamilyPotentialIncrementConst_nonneg M m E b k₀ omega p
  have ht0 : 0 ≤ t := Real.rpow_nonneg (by norm_num) _
  have hclass :
      badFamilyPotentialApproximationL2 hb0 hb hk₀ hne N p -
          badFamilyPotentialApproximationL2 hb0 hb hk₀ hne (N + 1) p =
        toVectorL2 hd := by
    dsimp [badFamilyPotentialApproximationL2, hd, hN, hNs]
    exact (MeasureTheory.MemLp.toLp_sub _ _).symm
  have hdistHilbert :
      dist (badFamilyPotentialApproximationL2 hb0 hb hk₀ hne N p)
          (badFamilyPotentialApproximationL2 hb0 hb hk₀ hne (N + 1) p) ≤
        ‖H‖ := by
    rw [dist_eq_norm, hclass]
    exact norm_toVectorL2_le_toHilbertVectorL2OfVecField hd
  have hHilbertSq : ‖H‖ ^ 2 =
      ∫ x in openCubeSet (originCube d m), vecNormSq
        (badFamilyPotentialApproximation M m E b k₀ omega N p x -
          badFamilyPotentialApproximation M m E b k₀ omega (N + 1) p x)
        ∂volume := by
    calc
      ‖H‖ ^ 2 = inner ℝ H H := (real_inner_self_eq_norm_sq H).symm
      _ = ∫ x in openCubeSet (originCube d m), vecDot
          ((badFamilyPotentialApproximation M m E b k₀ omega N p -
            badFamilyPotentialApproximation M m E b k₀ omega (N + 1) p) x)
          ((badFamilyPotentialApproximation M m E b k₀ omega N p -
            badFamilyPotentialApproximation M m E b k₀ omega (N + 1) p) x)
          ∂volume := inner_toHilbertVectorL2OfVecField_eq_integral hd hd
      _ = ∫ x in openCubeSet (originCube d m), vecNormSq
          (badFamilyPotentialApproximation M m E b k₀ omega N p x -
            badFamilyPotentialApproximation M m E b k₀ omega (N + 1) p x)
          ∂volume := by rfl
  have hInt :
      ∫ x in openCubeSet (originCube d m), vecNormSq
          (badFamilyPotentialApproximation M m E b k₀ omega N p x -
            badFamilyPotentialApproximation M m E b k₀ omega (N + 1) p x)
          ∂volume ≤ B * r ^ N := by
    refine (integral_vecNormSq_badFamilyPotentialApproximation_sub_succ_le
      hb0 hb hk₀ hne N p).trans_eq ?_
    dsimp [B, r, badFamilyPotentialIncrementConst]
    ring_nf
  have hdistSq :
      dist (badFamilyPotentialApproximationL2 hb0 hb hk₀ hne N p)
          (badFamilyPotentialApproximationL2 hb0 hb hk₀ hne (N + 1) p) ^ 2 ≤
        B * r ^ N := by
    calc
      dist (badFamilyPotentialApproximationL2 hb0 hb hk₀ hne N p)
          (badFamilyPotentialApproximationL2 hb0 hb hk₀ hne (N + 1) p) ^ 2 ≤
          ‖H‖ ^ 2 := (sq_le_sq₀ dist_nonneg (norm_nonneg H)).mpr hdistHilbert
      _ ≤ B * r ^ N := hHilbertSq.trans_le hInt
  have htr : t ^ 2 = r := by
    dsimp [t, r]
    rw [three_rpow_pow_eq]
    congr 1
    norm_num
  apply (sq_le_sq₀ dist_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg ht0 _))).mp
  calc
    dist (badFamilyPotentialApproximationL2 hb0 hb hk₀ hne N p)
        (badFamilyPotentialApproximationL2 hb0 hb hk₀ hne (N + 1) p) ^ 2 ≤
      B * r ^ N := hdistSq
    _ = (Real.sqrt B * t ^ N) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hB0, ← pow_mul, Nat.mul_comm, pow_mul, htr]

/-- The finite bad-family potential approximations form a Cauchy sequence in
the canonical vector `L²` space. -/
theorem cauchySeq_badFamilyPotentialApproximationL2
    {M : ABKModel d} {m : ℤ} {E b : ℝ} {k₀ : ℕ}
    {omega : Cutoff.CutoffSample d} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hk₀ : 3 ≤ k₀) (hne : (hsepSet M m E b omega).Nonempty)
    (p : Vec d) :
    CauchySeq (fun N =>
      badFamilyPotentialApproximationL2 hb0 hb hk₀ hne N p) := by
  let C := Real.sqrt (badFamilyPotentialIncrementConst M m E b k₀ omega p)
  let t : ℝ := (3 : ℝ) ^ (-(1 / 4 : ℝ))
  apply cauchySeq_of_dist_le_of_summable (fun N => C * t ^ N)
  · intro N
    exact dist_badFamilyPotentialApproximationL2_succ_le
      hb0 hb hk₀ hne N p
  · exact (summable_geometric_of_lt_one
      (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))).mul_left C

end

end Algsuperdiff.Section3.Provider.Affine
