/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyCutoff
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradientSq
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics

/-!
# The compactness hypotheses for the cutoff blow-up sequence

The modified sequence of `prop:blowup-limit` (cutoffs growing with the index,
applied to a reindexed tail of the blow-up fields) satisfies the uniform
slice, gradient, and pairing-modulus hypotheses of `lem:compactness` of the CKN manuscript on all
of space and all negative times. Each hypothesis is reduced to the
corresponding estimate for the original fields on a fixed bounded past
cylinder, valid from a stage-dependent index on.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A strictly increasing index dominating the first m + 1 stage indices. -/
@[expose] def blowupLimitAssemblyIndex (N : ℕ → ℕ) (m : ℕ) : ℕ :=
  (∑ j ∈ Finset.range (m + 1), N j) + m

theorem strictMono_blowupLimitAssemblyIndex (N : ℕ → ℕ) :
    StrictMono (blowupLimitAssemblyIndex N) := by
  apply strictMono_nat_of_lt_succ
  intro m
  unfold blowupLimitAssemblyIndex
  rw [Finset.sum_range_succ _ (m + 1)]
  omega

theorem le_blowupLimitAssemblyIndex (N : ℕ → ℕ) {j m : ℕ} (hjm : j ≤ m) :
    N j ≤ blowupLimitAssemblyIndex N m := by
  unfold blowupLimitAssemblyIndex
  have hj : j ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hjm)
  have hle : N j ≤ ∑ i ∈ Finset.range (m + 1), N i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (N i)) hj
  omega

/-! ### Pointwise estimates -/

/-- A velocity component is controlled by one plus the squared Euclidean
norm. -/
theorem blowupLimitAssembly_ofReal_abs_component_le (v : Vec3) (i : Fin 3) :
    ENNReal.ofReal |v i| ≤
      1 + ENNReal.ofReal (vec3EuclideanNorm v) ^ (2 : ℝ) := by
  have hcomp : |v i| ≤ vec3EuclideanNorm v :=
    (norm_le_pi_norm v i).trans (norm_le_vec3EuclideanNorm v)
  have hnn := vec3EuclideanNorm_nonneg v
  have hle : |v i| ≤ 1 + vec3EuclideanNorm v ^ 2 := by
    nlinarith only [hcomp, hnn]
  calc
    ENNReal.ofReal |v i| ≤ ENNReal.ofReal (1 + vec3EuclideanNorm v ^ 2) :=
      ENNReal.ofReal_le_ofReal hle
    _ = 1 + ENNReal.ofReal (vec3EuclideanNorm v) ^ (2 : ℝ) := by
      rw [ENNReal.ofReal_add zero_le_one (sq_nonneg _), ENNReal.ofReal_one,
        ENNReal.ofReal_rpow_of_nonneg hnn (by norm_num)]
      norm_num

/-- A gradient entry is controlled by one plus the gradient energy density. -/
theorem blowupLimitAssembly_ofReal_abs_gradient_le
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) (i j : Fin 3) :
    ENNReal.ofReal |Du z i j| ≤ 1 + ENNReal.ofReal (spatialGradientSq u Du z) := by
  have hentry : (Du z i j) ^ 2 ≤ spatialGradientSq u Du z := by
    unfold spatialGradientSq
    have hrow : (Du z i j) ^ 2 ≤ ∑ m : Fin 3, (Du z i m) ^ 2 :=
      Finset.single_le_sum (f := fun m => (Du z i m) ^ 2)
        (fun m _ => sq_nonneg _) (Finset.mem_univ j)
    have hall : ∑ m : Fin 3, (Du z i m) ^ 2 ≤
        ∑ l : Fin 3, ∑ m : Fin 3, (Du z l m) ^ 2 :=
      Finset.single_le_sum (f := fun l => ∑ m : Fin 3, (Du z l m) ^ 2)
        (fun l _ => Finset.sum_nonneg fun m _ => sq_nonneg _)
        (Finset.mem_univ i)
    exact hrow.trans hall
  have hsgs : 0 ≤ spatialGradientSq u Du z := (sq_nonneg _).trans hentry
  have hle : |Du z i j| ≤ 1 + spatialGradientSq u Du z := by
    have habs : |Du z i j| ^ 2 = (Du z i j) ^ 2 := sq_abs _
    nlinarith only [habs, hentry, abs_nonneg (Du z i j)]
  calc
    ENNReal.ofReal |Du z i j| ≤ ENNReal.ofReal (1 + spatialGradientSq u Du z) :=
      ENNReal.ofReal_le_ofReal hle
    _ = 1 + ENNReal.ofReal (spatialGradientSq u Du z) := by
      rw [ENNReal.ofReal_add zero_le_one hsgs, ENNReal.ofReal_one]

/-- A function dominated by one plus a function of finite integral is
integrable on a set of finite measure. -/
theorem blowupLimitAssembly_integrableOn_of_le_one_add
    {B : Set Vec3} (hB : volume B < ⊤) {g : Vec3 → ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict B))
    {F : Vec3 → ℝ≥0∞} (hpt : ∀ x, ENNReal.ofReal |g x| ≤ 1 + F x)
    (hF : (∫⁻ x in B, F x) < ⊤) :
    IntegrableOn g B volume := by
  refine ⟨hg, ?_⟩
  change (∫⁻ x in B, ‖g x‖ₑ) < ⊤
  calc
    (∫⁻ x in B, ‖g x‖ₑ) ≤ ∫⁻ x in B, (1 + F x) := by
      apply lintegral_mono
      intro x
      change ‖g x‖ₑ ≤ 1 + F x
      rw [Real.enorm_eq_ofReal_abs]
      exact hpt x
    _ = volume B + ∫⁻ x in B, F x := by
      rw [lintegral_add_left measurable_const, lintegral_const,
        Measure.restrict_apply_univ, one_mul]
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hB, hF⟩

/-- The gradient energy density of the modified field is controlled by the
original gradient and velocity. -/
theorem blowupLimitAssemblyCutoffGradient_sq_le
    (f : ℕ → ParabolicPoint → Vec3)
    (Df : ℕ → ParabolicPoint → Fin 3 → Vec3) (ν : ℕ → ℕ) (k : ℕ)
    (z : ParabolicPoint) :
    spatialGradientSq (blowupLimitAssemblyCutoffField f ν k)
        (blowupLimitAssemblyCutoffGradient f Df ν k) z ≤
      2 * spatialGradientSq (f (ν k)) (Df (ν k)) z +
        2 * 64 ^ 2 * vec3EuclideanNorm (f (ν k) z) ^ 2 := by
  set T := blowupLimitAssemblyTimeRamp k z.2
  set S := blowupLimitAssemblySpaceCutoff k z.1
  set G := classicalGradient (blowupLimitAssemblySpaceCutoff k) z.1
  have hT0 : 0 ≤ T := blowupLimitAssemblyTimeRamp_nonneg k z.2
  have hT1 : T ≤ 1 := blowupLimitAssemblyTimeRamp_le_one k z.2
  have hS0 : 0 ≤ S := blowupLimitAssemblySpaceCutoff_nonneg k z.1
  have hS1 : S ≤ 1 := blowupLimitAssemblySpaceCutoff_le_one k z.1
  have hG : ∑ j : Fin 3, (G j) ^ 2 ≤ 64 ^ 2 :=
    blowupLimitAssemblySpaceCutoff_gradient_sq_le k z.1
  have hfsq : vec3EuclideanNorm (f (ν k) z) ^ 2 = ∑ i : Fin 3, (f (ν k) z i) ^ 2 := by
    rw [vec3EuclideanNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  have hentry (i j : Fin 3) :
      (blowupLimitAssemblyCutoffGradient f Df ν k z i j) ^ 2 ≤
        2 * (Df (ν k) z i j) ^ 2 + 2 * ((f (ν k) z i) ^ 2 * (G j) ^ 2) := by
    have hval : blowupLimitAssemblyCutoffGradient f Df ν k z i j =
        T * (S * Df (ν k) z i j + f (ν k) z i * G j) := by
      simp [blowupLimitAssemblyCutoffGradient, T, S, G, smul_eq_mul]
    rw [hval]
    have hT2 : T ^ 2 ≤ 1 := by nlinarith only [hT0, hT1]
    have hS2 : S ^ 2 ≤ 1 := by nlinarith only [hS0, hS1]
    set a := Df (ν k) z i j
    set c := f (ν k) z i * G j
    have hsum : (S * a + c) ^ 2 ≤ 2 * a ^ 2 + 2 * c ^ 2 := by
      nlinarith only [sq_nonneg (S * a - c), hS2, sq_nonneg a]
    have hc : c ^ 2 = (f (ν k) z i) ^ 2 * (G j) ^ 2 := by
      simp only [c]
      ring
    calc
      (T * (S * a + c)) ^ 2 = T ^ 2 * (S * a + c) ^ 2 := by ring
      _ ≤ 1 * (S * a + c) ^ 2 :=
        mul_le_mul_of_nonneg_right hT2 (sq_nonneg _)
      _ ≤ 2 * a ^ 2 + 2 * c ^ 2 := by rw [one_mul]; exact hsum
      _ = 2 * a ^ 2 + 2 * ((f (ν k) z i) ^ 2 * (G j) ^ 2) := by rw [hc]
  unfold spatialGradientSq
  calc
    ∑ i : Fin 3, ∑ j : Fin 3,
        (blowupLimitAssemblyCutoffGradient f Df ν k z i j) ^ 2 ≤
        ∑ i : Fin 3, ∑ j : Fin 3,
          (2 * (Df (ν k) z i j) ^ 2 + 2 * ((f (ν k) z i) ^ 2 * (G j) ^ 2)) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ = 2 * ∑ i : Fin 3, ∑ j : Fin 3, (Df (ν k) z i j) ^ 2 +
          2 * ((∑ i : Fin 3, (f (ν k) z i) ^ 2) * ∑ j : Fin 3, (G j) ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      congr 1
      exact Finset.sum_comm
    _ ≤ 2 * ∑ i : Fin 3, ∑ j : Fin 3, (Df (ν k) z i j) ^ 2 +
          2 * ((∑ i : Fin 3, (f (ν k) z i) ^ 2) * 64 ^ 2) := by
      have hf0 : 0 ≤ ∑ i : Fin 3, (f (ν k) z i) ^ 2 :=
        Finset.sum_nonneg fun i _ => sq_nonneg _
      nlinarith only [mul_le_mul_of_nonneg_left hG hf0]
    _ = 2 * ∑ i : Fin 3, ∑ j : Fin 3, (Df (ν k) z i j) ^ 2 +
          2 * 64 ^ 2 * vec3EuclideanNorm (f (ν k) z) ^ 2 := by
      rw [hfsq]
      ring

/-- The modified gradient vanishes off the support of the cutoffs. -/
theorem blowupLimitAssemblyCutoffGradient_eq_zero
    (f : ℕ → ParabolicPoint → Vec3)
    (Df : ℕ → ParabolicPoint → Fin 3 → Vec3) (ν : ℕ → ℕ) (k : ℕ)
    (z : ParabolicPoint)
    (hz : z.1 ∉ vec3Ball (0 : Vec3) ((k : ℝ) + 1) ∨ z.2 ≤ -((k : ℝ) + 1)) :
    blowupLimitAssemblyCutoffGradient f Df ν k z = 0 := by
  rcases hz with hx | ht
  · have hS := blowupLimitAssemblySpaceCutoff_eq_zero_of_notMem hx
    have hG := blowupLimitAssemblySpaceCutoff_gradient_eq_zero_of_notMem hx
    funext i
    simp [blowupLimitAssemblyCutoffGradient, hS, hG]
  · have hT := blowupLimitAssemblyTimeRamp_eq_zero ht
    funext i
    simp [blowupLimitAssemblyCutoffGradient, hT]

end ESS

end
