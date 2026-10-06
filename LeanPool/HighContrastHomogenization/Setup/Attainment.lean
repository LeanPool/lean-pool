/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.Contrast
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.Compact

/-!
# High-contrast homogenization: Setup.Attainment

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The minimum over the skew parameter is attained

The reference text writes the intrinsic contrast and the reference constant `Λ_0`
as *minima* over the skew matrices `h` (the intrinsic contrast of the reference
block, `e.Theta.m` and `e.reference.aspect.ratio`), while the encodings
`blockContrast` and `bigLambdaRef` are infima.  This file proves that on the data
where the reference text reads them — a symmetric doubled block matrix that is
positive definite — the two readings agree: the infimum is attained at some skew
matrix, so it is the printed minimum.

The mechanism is the classical one.  On a positive definite doubled block matrix
the lower-right block `σ_*⁻¹` is coercive, so the correction
`(k - h)ᵗ σ_*⁻¹ (k - h)` grows quadratically in `h`: the set of skew `h` admitting
a fixed Loewner bound is bounded, and it is closed because the Loewner order is a
closed condition.  Cantor's intersection theorem along a sequence of thresholds
decreasing to the infimum then produces a skew matrix realizing it.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

variable {d : ℕ}

/-! ## Coercivity of a positive quadratic form -/

private theorem vecNormSq_smul_sq (c : ℝ) (x : Vec d) :
    vecNormSq (c • x) = c ^ 2 * vecNormSq x := by
  show vecDot (c • x) (c • x) = c ^ 2 * vecDot x x
  rw [vecDot_smul_left, vecDot_smul_right]
  ring

private theorem vecDot_matVecMul_smul_self (c : ℝ) (M : Mat d) (x : Vec d) :
    vecDot (c • x) (matVecMul M (c • x)) = c ^ 2 * vecDot x (matVecMul M x) := by
  rw [matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
  ring

private theorem eq_zero_of_vecNormSq_eq_zero {x : Vec d} (h : vecNormSq x = 0) : x = 0 := by
  funext i
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin d)), 0 ≤ x i * x i :=
    fun i _ => mul_self_nonneg (x i)
  exact mul_self_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg hnn).1 h i (Finset.mem_univ i))

private theorem vecNormSq_zero' : vecNormSq (0 : Vec d) = 0 := by
  show vecDot (0 : Vec d) (0 : Vec d) = 0
  simp [vecDot]

private theorem continuous_vecNormSq : Continuous (vecNormSq : Vec d → ℝ) := by
  show Continuous fun x : Vec d => ∑ i, x i * x i
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul (continuous_apply i)

/-- The quadratic form of a matrix depends continuously on the matrix. -/
private theorem continuous_quadratic {X : Type*} [TopologicalSpace X] {F : X → Mat d}
    (hF : Continuous F) (x : Vec d) :
    Continuous fun p : X => vecDot x (matVecMul (F p) x) := by
  show Continuous fun p : X => ∑ i, x i * ∑ j, F p i j * x j
  exact continuous_finsetSum _ fun i _ =>
    continuous_const.mul (continuous_finsetSum _ fun j _ =>
      (hF.matrix_elem i j).mul continuous_const)

/-- **Coercivity.**  A matrix whose quadratic form is positive away from the origin
dominates a positive multiple of the squared length.  The minimum of the quadratic
form on the unit sphere, which is compact, is the constant. -/
theorem exists_coercivity_of_quadratic_pos {M : Mat d}
    (hM : ∀ x : Vec d, x ≠ 0 → 0 < vecDot x (matVecMul M x)) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ x : Vec d, lam * vecNormSq x ≤ vecDot x (matVecMul M x) := by
  classical
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · refine ⟨1, one_pos, fun x => ?_⟩
    have h1 : vecNormSq x = 0 := by
      show vecDot x x = 0
      simp [vecDot]
    have h2 : vecDot x (matVecMul M x) = 0 := by simp [vecDot]
    rw [h1, h2, mul_zero]
  · set K : Set (Vec d) := {x : Vec d | vecNormSq x = 1} with hKdef
    have hKclosed : IsClosed K := isClosed_eq continuous_vecNormSq continuous_const
    have hKsub : K ⊆ Set.univ.pi fun _ : Fin d => Set.Icc (-1 : ℝ) 1 := by
      intro x hx i _
      have h : x i ^ 2 ≤ 1 := by
        have hle := sq_apply_le_vecNormSq x i
        rw [show vecNormSq x = 1 from hx] at hle
        exact hle
      exact abs_le.1 ((sq_le_one_iff_abs_le_one (x i)).1 h)
    have hKcompact : IsCompact K :=
      (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hKclosed hKsub
    have hKne : K.Nonempty := by
      refine ⟨Pi.single (Classical.arbitrary (Fin d)) 1, ?_⟩
      show vecDot _ _ = 1
      simp [vecDot, Pi.single_apply, mul_ite, Finset.sum_ite_eq']
    have hcont : Continuous fun x : Vec d => vecDot x (matVecMul M x) := by
      show Continuous fun x : Vec d => ∑ i, x i * ∑ j, M i j * x j
      exact continuous_finsetSum _ fun i _ =>
        (continuous_apply i).mul (continuous_finsetSum _ fun j _ =>
          continuous_const.mul (continuous_apply j))
    obtain ⟨x₀, hx₀K, hx₀min⟩ := hKcompact.exists_isMinOn hKne hcont.continuousOn
    have hx₀ne : x₀ ≠ 0 := by
      intro h0
      have h1 : vecNormSq x₀ = 1 := hx₀K
      rw [h0, vecNormSq_zero'] at h1
      exact zero_ne_one h1
    refine ⟨vecDot x₀ (matVecMul M x₀), hM x₀ hx₀ne, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx
      rw [vecNormSq_zero', mul_zero]
      simp [vecDot]
    · have hpos : 0 < vecNormSq x :=
        lt_of_le_of_ne (vecNormSq_nonneg x) fun hc => hx (eq_zero_of_vecNormSq_eq_zero hc.symm)
      set s : ℝ := Real.sqrt (vecNormSq x) with hsdef
      have hs : 0 < s := Real.sqrt_pos.2 hpos
      have hs2 : s ^ 2 = vecNormSq x := Real.sq_sqrt hpos.le
      have hyK : (s⁻¹ • x) ∈ K := by
        show vecNormSq (s⁻¹ • x) = 1
        rw [vecNormSq_smul_sq, ← hs2]
        field_simp
      have hmin := isMinOn_iff.1 hx₀min (s⁻¹ • x) hyK
      rw [vecDot_matVecMul_smul_self] at hmin
      have hs2pos : (0 : ℝ) < s ^ 2 := by positivity
      have hstep := mul_le_mul_of_nonneg_left hmin hs2pos.le
      rw [← mul_assoc, show s ^ 2 * (s⁻¹) ^ 2 = 1 by field_simp, one_mul, hs2] at hstep
      rw [mul_comm (vecNormSq x)] at hstep
      exact hstep

/-! ## The quadratic form of the skew-corrected Schur form -/

private theorem matVecMul_smul_one' (t : ℝ) (x : Vec d) :
    matVecMul (t • (1 : Mat d)) x = t • x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq, mul_comm]

private theorem quad_smul' (t : ℝ) (A : Mat d) (x : Vec d) :
    vecDot x (matVecMul (t • A) x) = t * vecDot x (matVecMul A x) := by
  simp only [vecDot, matVecMul, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem quad_le_of_smul_one {M : Mat d} {b : ℝ}
    (h : MatLoewnerLE M (b • (1 : Mat d))) (x : Vec d) :
    vecDot x (matVecMul M x) ≤ b * vecNormSq x := by
  have h1 := h x
  rw [matVecMul_smul_one', vecDot_smul_right, show vecDot x x = vecNormSq x from rfl] at h1
  linarith only [h1]

private theorem quad_of_matLoewnerLE {A B : Mat d} (h : MatLoewnerLE A B) (x : Vec d) :
    vecDot x (matVecMul A x) ≤ vecDot x (matVecMul B x) := by
  have := h x
  linarith only [this]

private theorem matLoewnerLE_of_quad {A B : Mat d}
    (h : ∀ x : Vec d, vecDot x (matVecMul A x) ≤ vecDot x (matVecMul B x)) :
    MatLoewnerLE A B := fun x => by
  have := h x
  linarith only [this]

/-- The quadratic form of the skew-corrected Schur form splits into the Schur block
and the correction carried by the lower-right block. -/
private theorem quad_skewCorrectedForm (H : BlockMat d) (h : Mat d) (x : Vec d) :
    vecDot x (matVecMul (skewCorrectedForm H h) x) =
      vecDot x (matVecMul (schurSigma H) x) +
        vecDot (matVecMul (schurSkew H - h) x)
          (matVecMul H.lowerRight (matVecMul (schurSkew H - h) x)) := by
  rw [skewCorrectedForm, add_matVecMul, vecDot_add_right]
  congr 1
  rw [mul_assoc, ← matVecMul_mul, vecDot_matVecMul_transpose, matVecMul_mul]

/-! ## The admissible skew matrices form a compact set -/

private theorem matVecMul_single (D : Mat d) (j : Fin d) :
    matVecMul D (Pi.single j (1 : ℝ)) = fun i => D i j := by
  funext i
  simp [matVecMul, Pi.single_apply, mul_ite, Finset.sum_ite_eq']

private theorem vecNormSq_single (j : Fin d) : vecNormSq (Pi.single j (1 : ℝ)) = 1 := by
  show vecDot _ _ = 1
  simp [vecDot, Pi.single_apply, mul_ite, Finset.sum_ite_eq']

private theorem abs_apply_le_entrySum (A : Mat d) (i j : Fin d) :
    |A i j| ≤ ∑ p : Fin d, ∑ q : Fin d, |A p q| := by
  refine le_trans ?_
    (Finset.single_le_sum (f := fun p : Fin d => ∑ q : Fin d, |A p q|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun q : Fin d => |A i q|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ j)

/-- **The sublevel sets are bounded.**  If the lower-right block is coercive, then the
skew matrices admitting a fixed Loewner bound on the skew-corrected Schur form have
uniformly bounded entries. -/
private theorem exists_entry_bound_of_matLoewnerLE {H : BlockMat d} {N : Mat d} {t lam : ℝ}
    (ht : 0 ≤ t) (hlam : 0 < lam)
    (hcoer : ∀ y : Vec d, lam * vecNormSq y ≤ vecDot y (matVecMul H.lowerRight y)) :
    ∃ C : ℝ, ∀ h : Mat d,
      MatLoewnerLE (skewCorrectedForm H h) (t • N) → ∀ i j, h i j ∈ Set.Icc (-C) C := by
  classical
  obtain ⟨bN, hbN0, hbN⟩ := exists_matLoewnerLE_smul_one N
  obtain ⟨bS, hbS0, hbS⟩ := exists_matLoewnerLE_smul_one (-(schurSigma H))
  set bk : ℝ := ∑ p : Fin d, ∑ q : Fin d, |schurSkew H p q| with hbkdef
  have hbk0 : 0 ≤ bk := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  set c0 : ℝ := t * bN + bS with hc0def
  have hc00 : 0 ≤ c0 := by positivity
  have hquot : 0 ≤ c0 / lam := div_nonneg hc00 hlam.le
  refine ⟨bk + Real.sqrt (c0 / lam), fun h hle i j => ?_⟩
  set D : Mat d := schurSkew H - h with hDdef
  set e : Vec d := Pi.single j (1 : ℝ) with hedef
  have hsplit := quad_skewCorrectedForm H h e
  have hupper : vecDot e (matVecMul (skewCorrectedForm H h) e) ≤ t * bN := by
    refine le_trans (quad_of_matLoewnerLE hle e) ?_
    rw [quad_smul']
    have hN := quad_le_of_smul_one hbN e
    rw [vecNormSq_single] at hN
    have := mul_le_mul_of_nonneg_left hN ht
    rw [mul_one] at this
    exact this
  have hlower : -(vecDot e (matVecMul (schurSigma H) e)) ≤ bS := by
    have hS := quad_le_of_smul_one hbS e
    rw [vecNormSq_single, mul_one, neg_matVecMul, vecDot_neg_right] at hS
    exact hS
  have hcorr : vecDot (matVecMul D e) (matVecMul H.lowerRight (matVecMul D e)) ≤ c0 := by
    rw [hc0def]
    linarith only [hsplit, hupper, hlower]
  have hnorm : vecNormSq (matVecMul D e) ≤ c0 / lam := by
    have := le_trans (hcoer (matVecMul D e)) hcorr
    rw [le_div_iff₀ hlam, mul_comm]
    exact this
  have hentry : (D i j) ^ 2 ≤ c0 / lam := by
    have hDe : matVecMul D e i = D i j := congrFun (matVecMul_single D j) i
    have hsq := sq_apply_le_vecNormSq (matVecMul D e) i
    rw [hDe] at hsq
    exact le_trans hsq hnorm
  have habsD : |D i j| ≤ Real.sqrt (c0 / lam) := by
    refine abs_le_of_sq_le_sq ?_ (Real.sqrt_nonneg _)
    rw [Real.sq_sqrt hquot]
    exact hentry
  have hhij : h i j = schurSkew H i j - D i j := by
    rw [hDdef]
    simp
  have habsk : |schurSkew H i j| ≤ bk := abs_apply_le_entrySum _ i j
  have : |h i j| ≤ bk + Real.sqrt (c0 / lam) := by
    rw [hhij]
    refine le_trans (abs_sub _ _) ?_
    exact add_le_add habsk habsD
  exact abs_le.1 this

/-! ## Attainment -/

/-- **Attainment of the minimum over the skew parameter.**  On a doubled block matrix
whose lower-right block has a positive quadratic form away from the origin, and against
a coercive comparison matrix, the infimum of the admissible Loewner scalings is itself
admissible: some skew matrix realizes it. -/
theorem exists_isSkewMat_matLoewnerLE_sInf_smul {H : BlockMat d} {N : Mat d}
    (hposH : ∀ x : Vec d, x ≠ 0 → 0 < vecDot x (matVecMul H.lowerRight x))
    (hcoerN : ∃ lamN : ℝ, 0 < lamN ∧
      ∀ x : Vec d, lamN * vecNormSq x ≤ vecDot x (matVecMul N x)) :
    ∃ h : Mat d, IsSkewMat h ∧
      MatLoewnerLE (skewCorrectedForm H h)
        (sInf {t : ℝ | 0 ≤ t ∧ ∃ h' : Mat d, IsSkewMat h' ∧
          MatLoewnerLE (skewCorrectedForm H h') (t • N)} • N) := by
  classical
  obtain ⟨lamL, hlamL, hcoerL⟩ := exists_coercivity_of_quadratic_pos hposH
  obtain ⟨lamN, hlamN, hcoerN'⟩ := hcoerN
  set A : Set ℝ := {t : ℝ | 0 ≤ t ∧ ∃ h' : Mat d, IsSkewMat h' ∧
      MatLoewnerLE (skewCorrectedForm H h') (t • N)} with hAdef
  set W : ℝ → Set (Mat d) := fun t =>
    {h : Mat d | IsSkewMat h ∧ MatLoewnerLE (skewCorrectedForm H h) (t • N)} with hWdef
  have hNnn : ∀ x : Vec d, 0 ≤ vecDot x (matVecMul N x) := fun x =>
    le_trans (mul_nonneg hlamN.le (vecNormSq_nonneg x)) (hcoerN' x)
  have hWmono : ∀ t₁ t₂ : ℝ, t₁ ≤ t₂ → W t₁ ⊆ W t₂ := by
    intro t₁ t₂ hle h hh
    refine ⟨hh.1, matLoewnerLE_of_quad fun x => ?_⟩
    have h1 := quad_of_matLoewnerLE hh.2 x
    rw [quad_smul'] at h1 ⊢
    exact le_trans h1 (mul_le_mul_of_nonneg_right hle (hNnn x))
  have hAne : A.Nonempty := by
    obtain ⟨b, hb0, hb⟩ := exists_matLoewnerLE_smul_one (skewCorrectedForm H 0)
    refine ⟨b / lamN, div_nonneg hb0 hlamN.le, 0, isSkewMat_zero, ?_⟩
    refine matLoewnerLE_of_quad fun x => ?_
    rw [quad_smul']
    have h1 := quad_le_of_smul_one hb x
    have h2 := mul_le_mul_of_nonneg_left (hcoerN' x) (div_nonneg hb0 hlamN.le)
    have h3 : b / lamN * (lamN * vecNormSq x) = b * vecNormSq x := by
      field_simp
    rw [h3] at h2
    exact le_trans h1 h2
  have hAbdd : BddBelow A := ⟨0, fun t ht => ht.1⟩
  set c : ℝ := sInf A with hcdef
  have hc0 : 0 ≤ c := Real.sInf_nonneg fun t ht => ht.1
  have hWne : ∀ t : ℝ, c < t → (W t).Nonempty := by
    intro t hct
    obtain ⟨a, haA, hat⟩ := exists_lt_of_csInf_lt hAne hct
    obtain ⟨-, h', hskew, hle⟩ := haA
    exact ⟨h', hWmono a t hat.le ⟨hskew, hle⟩⟩
  have hcontForm : Continuous fun h : Mat d => skewCorrectedForm H h := by
    show Continuous fun h : Mat d =>
      schurSigma H + matTranspose (schurSkew H - h) * H.lowerRight * (schurSkew H - h)
    exact continuous_const.add
      ((((continuous_const.sub continuous_id).matrix_transpose).matrix_mul
        continuous_const).matrix_mul (continuous_const.sub continuous_id))
  have hWclosed : ∀ t : ℝ, IsClosed (W t) := by
    intro t
    have h1 : IsClosed {h : Mat d | IsSkewMat h} :=
      isClosed_eq (continuous_id.matrix_transpose) continuous_neg
    have h2 : IsClosed {h : Mat d | MatLoewnerLE (skewCorrectedForm H h) (t • N)} := by
      have hrw : {h : Mat d | MatLoewnerLE (skewCorrectedForm H h) (t • N)} =
          ⋂ x : Vec d, {h : Mat d |
            (1 / 2 : ℝ) * vecDot x (matVecMul (skewCorrectedForm H h) x) ≤
              (1 / 2 : ℝ) * vecDot x (matVecMul (t • N) x)} := by
        ext h
        simp only [Set.mem_ofPred_eq, Set.mem_iInter, MatLoewnerLE]
      rw [hrw]
      exact isClosed_iInter fun x =>
        isClosed_le (continuous_const.mul (continuous_quadratic hcontForm x)) continuous_const
    exact h1.inter h2
  obtain ⟨C, hC⟩ :=
    exists_entry_bound_of_matLoewnerLE (H := H) (N := N) (t := c + 1)
      (by linarith only [hc0]) hlamL hcoerL
  have hWcompact : IsCompact (W (c + 1)) := by
    refine (isCompact_Icc (a := -C) (b := C)).matrix.of_isClosed_subset (hWclosed _) ?_
    intro h hh
    exact fun i j => hC h hh.2 i j
  set Z : ℕ → Set (Mat d) := fun n => W (c + 1 / ((n : ℝ) + 1)) with hZdef
  have hZ0 : Z 0 = W (c + 1) := by norm_num [hZdef]
  have hZmono : ∀ n : ℕ, Z (n + 1) ⊆ Z n := by
    intro n
    refine hWmono _ _ ?_
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h3 : (1 : ℝ) / ((n : ℝ) + 1 + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le h1 (by linarith only [])
    push_cast
    linarith only [h3]
  have hZne : ∀ n : ℕ, (Z n).Nonempty := by
    intro n
    refine hWne _ ?_
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith only [this]
  have hZclosed : ∀ n : ℕ, IsClosed (Z n) := fun n => hWclosed _
  obtain ⟨h, hh⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed Z hZmono hZne
      (by rw [hZ0]; exact hWcompact) hZclosed
  rw [Set.mem_iInter] at hh
  refine ⟨h, (hh 0).1, matLoewnerLE_of_quad fun x => ?_⟩
  rw [quad_smul']
  have hqN : ∀ n : ℕ, vecDot x (matVecMul (skewCorrectedForm H h) x) ≤
      (c + 1 / ((n : ℝ) + 1)) * vecDot x (matVecMul N x) := by
    intro n
    have := quad_of_matLoewnerLE (hh n).2 x
    rwa [quad_smul'] at this
  have hlim : Filter.Tendsto
      (fun n : ℕ => (c + 1 / ((n : ℝ) + 1)) * vecDot x (matVecMul N x))
      Filter.atTop (nhds (c * vecDot x (matVecMul N x))) := by
    have h0 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using (h0.const_add c).mul_const (vecDot x (matVecMul N x))
  exact ge_of_tendsto hlim (Filter.Eventually.of_forall hqN)

/-! ## The printed minima -/

private theorem matVecMul_one' (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

private theorem coercivity_one :
    ∃ lam : ℝ, 0 < lam ∧
      ∀ x : Vec d, lam * vecNormSq x ≤ vecDot x (matVecMul (1 : Mat d) x) := by
  refine ⟨1, one_pos, fun x => ?_⟩
  rw [matVecMul_one', one_mul]
  exact le_of_eq rfl

/-- The lower-right block of a positive definite doubled block matrix has a positive
quadratic form away from the origin. -/
theorem quadratic_pos_lowerRight {H : BlockMat d} (hpos : Book.Ch02.BlockPosDef H)
    (x : Vec d) (hx : x ≠ 0) : 0 < vecDot x (matVecMul H.lowerRight x) := by
  rw [← blockVecDot_inr]
  exact hpos ((0 : Vec d), x) fun hc => hx (congrArg Prod.snd hc)

/-- The lower-right block of a symmetric positive definite doubled block matrix is a
positive definite matrix. -/
theorem posDef_lowerRight {H : BlockMat d} (hsymm : IsSymmetricBlockMat H)
    (hpos : Book.Ch02.BlockPosDef H) : H.lowerRight.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (isHermitian_lowerRight hsymm) ?_
  intro x hx
  have h := quadratic_pos_lowerRight hpos x hx
  simpa [star_trivial, dotProduct, Matrix.mulVec, vecDot, matVecMul] using h

/-- The Schur block `σ_*` of a symmetric positive definite doubled block matrix has a
positive quadratic form away from the origin. -/
theorem quadratic_pos_schurSigmaStar {H : BlockMat d} (hsymm : IsSymmetricBlockMat H)
    (hpos : Book.Ch02.BlockPosDef H) (x : Vec d) (hx : x ≠ 0) :
    0 < vecDot x (matVecMul (schurSigmaStar H) x) := by
  have hinv : (H.lowerRight)⁻¹.PosDef :=
    Matrix.posDef_inv_iff.2 (posDef_lowerRight hsymm hpos)
  have h := hinv.dotProduct_mulVec_pos hx
  rw [schurSigmaStar]
  simpa [star_trivial, dotProduct, Matrix.mulVec, vecDot, matVecMul] using h

/-- **The conjugating matrix.**  On a symmetric positive definite doubled block matrix
the positive semidefinite square root of the lower-right block is symmetric, invertible,
and conjugates `σ_*` to the identity: it is the inverse square root `σ_*^{-1/2}`. -/
theorem matSqrt_lowerRight_spec {H : BlockMat d} (hsymm : IsSymmetricBlockMat H)
    (hpos : Book.Ch02.BlockPosDef H) :
    matTranspose (matSqrt H.lowerRight) = matSqrt H.lowerRight ∧
      IsUnit (matSqrt H.lowerRight).det ∧
      matSqrt H.lowerRight * schurSigmaStar H * matSqrt H.lowerRight = 1 := by
  have hdet : IsUnit H.lowerRight.det := isUnit_det_lowerRight hpos
  obtain ⟨hRpsd, hRR⟩ := matSqrt_spec (posSemidef_lowerRight hsymm hpos)
  set R : Mat d := matSqrt H.lowerRight with hRdef
  have hRsymm : matTranspose R = R := by
    have hH := hRpsd.isHermitian
    ext i j
    simpa [matTranspose, Matrix.IsHermitian, Matrix.conjTranspose_apply] using
      congrArg (fun M : Mat d => M i j) hH
  have hRdet : IsUnit R.det := by
    refine isUnit_of_mul_isUnit_left (y := R.det) ?_
    rw [← Matrix.det_mul, hRR]
    exact hdet
  refine ⟨hRsymm, hRdet, ?_⟩
  rw [schurSigmaStar, ← hRR, Matrix.mul_inv_rev]
  calc R * (R⁻¹ * R⁻¹) * R = (R * R⁻¹) * (R⁻¹ * R) := by
        simp [Matrix.mul_assoc]
    _ = 1 := by
        rw [Matrix.mul_nonsing_inv R hRdet, Matrix.nonsing_inv_mul R hRdet, one_mul]

private theorem bigLambdaRef_eq_sInf_form (E : BlockMat d) :
    bigLambdaRef E = sInf {t : ℝ | 0 ≤ t ∧ ∃ h : Mat d, IsSkewMat h ∧
      MatLoewnerLE (skewCorrectedForm E h) (t • (1 : Mat d))} := rfl

private theorem blockContrast_eq_sInf_form (H : BlockMat d) :
    blockContrast H = sInf {t : ℝ | 0 ≤ t ∧ ∃ h : Mat d, IsSkewMat h ∧
      MatLoewnerLE (skewCorrectedForm H h) (t • schurSigmaStar H)} := rfl

/-- **`Λ_0` is the printed minimum.**  On a positive definite reference block the
infimum defining `bigLambdaRef` is attained: it is the least element of the family
`|σ_0 + (k_0 - h)ᵗ σ_{*,0}^{-1} (k_0 - h)|` indexed by the skew matrices, which is the
minimum written at `e.reference.aspect.ratio`. -/
theorem isLeast_bigLambdaRef {E : BlockMat d} (hpos : Book.Ch02.BlockPosDef E) :
    IsLeast ((fun h => specBound (skewCorrectedForm E h)) '' {h : Mat d | IsSkewMat h})
      (bigLambdaRef E) := by
  have hbdd : BddBelow ((fun h => specBound (skewCorrectedForm E h)) ''
      {h : Mat d | IsSkewMat h}) := by
    refine ⟨0, ?_⟩
    rintro y ⟨h, -, rfl⟩
    exact specBound_nonneg _
  have hlb : ∀ y ∈ (fun h => specBound (skewCorrectedForm E h)) '' {h : Mat d | IsSkewMat h},
      bigLambdaRef E ≤ y := by
    intro y hy
    rw [bigLambdaRef_eq_sInf E]
    exact csInf_le hbdd hy
  refine ⟨?_, hlb⟩
  obtain ⟨h, hskew, hle⟩ :=
    exists_isSkewMat_matLoewnerLE_sInf_smul (H := E) (N := (1 : Mat d))
      (quadratic_pos_lowerRight hpos) coercivity_one
  rw [← bigLambdaRef_eq_sInf_form E] at hle
  have hup : specBound (skewCorrectedForm E h) ≤ bigLambdaRef E :=
    specBound_le (bigLambdaRef_nonneg E) hle
  have hdown : bigLambdaRef E ≤ specBound (skewCorrectedForm E h) :=
    hlb _ ⟨h, hskew, rfl⟩
  exact ⟨h, hskew, le_antisymm hup hdown⟩

/-- **The intrinsic contrast is the printed minimum.**  On a symmetric positive definite
doubled block matrix the infimum defining `blockContrast` is attained: it is the least
element of the family
`|σ_*^{-1/2} (σ + (k - h)ᵗ σ_*⁻¹ (k - h)) σ_*^{-1/2}|` indexed by the skew matrices,
which is the minimum written for the intrinsic contrast of the reference block
and at `e.Theta.m`. -/
theorem isLeast_blockContrast {H : BlockMat d} (hsymm : IsSymmetricBlockMat H)
    (hpos : Book.Ch02.BlockPosDef H) :
    IsLeast ((fun h => specBound (matSqrt H.lowerRight * skewCorrectedForm H h *
        matSqrt H.lowerRight)) '' {h : Mat d | IsSkewMat h})
      (blockContrast H) := by
  have hbdd : BddBelow ((fun h => specBound (matSqrt H.lowerRight *
      skewCorrectedForm H h * matSqrt H.lowerRight)) '' {h : Mat d | IsSkewMat h}) := by
    refine ⟨0, ?_⟩
    rintro y ⟨h, -, rfl⟩
    exact specBound_nonneg _
  have hlb : ∀ y ∈ (fun h => specBound (matSqrt H.lowerRight * skewCorrectedForm H h *
      matSqrt H.lowerRight)) '' {h : Mat d | IsSkewMat h}, blockContrast H ≤ y := by
    intro y hy
    rw [blockContrast_eq_sInf_conj hsymm hpos]
    exact csInf_le hbdd hy
  refine ⟨?_, hlb⟩
  obtain ⟨hRsymm, hRdet, hRRinv⟩ := matSqrt_lowerRight_spec hsymm hpos
  obtain ⟨h, hskew, hle⟩ :=
    exists_isSkewMat_matLoewnerLE_sInf_smul (H := H) (N := schurSigmaStar H)
      (quadratic_pos_lowerRight hpos)
      (exists_coercivity_of_quadratic_pos (quadratic_pos_schurSigmaStar hsymm hpos))
  rw [← blockContrast_eq_sInf_form H] at hle
  have hconj := (matLoewnerLE_smul_iff_conj hRsymm hRRinv hRdet (blockContrast H)).1 hle
  have hup : specBound (matSqrt H.lowerRight * skewCorrectedForm H h *
      matSqrt H.lowerRight) ≤ blockContrast H :=
    specBound_le (blockContrast_nonneg H) hconj
  have hdown : blockContrast H ≤ specBound (matSqrt H.lowerRight *
      skewCorrectedForm H h * matSqrt H.lowerRight) := hlb _ ⟨h, hskew, rfl⟩
  exact ⟨h, hskew, le_antisymm hup hdown⟩

/-- The reference constant `Λ_0` is realized at some skew matrix. -/
theorem exists_isSkewMat_bigLambdaRef_eq {E : BlockMat d}
    (hpos : Book.Ch02.BlockPosDef E) :
    ∃ h : Mat d, IsSkewMat h ∧ bigLambdaRef E = specBound (skewCorrectedForm E h) := by
  obtain ⟨h, hskew, heq⟩ := (isLeast_bigLambdaRef hpos).1
  exact ⟨h, hskew, heq.symm⟩

/-- The intrinsic contrast is realized at some skew matrix. -/
theorem exists_isSkewMat_blockContrast_eq {H : BlockMat d}
    (hsymm : IsSymmetricBlockMat H) (hpos : Book.Ch02.BlockPosDef H) :
    ∃ h : Mat d, IsSkewMat h ∧ blockContrast H =
      specBound (matSqrt H.lowerRight * skewCorrectedForm H h * matSqrt H.lowerRight) := by
  obtain ⟨h, hskew, heq⟩ := (isLeast_blockContrast hsymm hpos).1
  exact ⟨h, hskew, heq.symm⟩

end

end HighContrast
end HCPolySupport
