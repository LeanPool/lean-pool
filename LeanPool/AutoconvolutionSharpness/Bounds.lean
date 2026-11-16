/-
Copyright (c) 2026 Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić
-/
module

public import LeanPool.AutoconvolutionSharpness.Step
public import LeanPool.AutoconvolutionSharpness.Interpolation
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Norm estimates from coefficient plateaus
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

namespace Autoconvolutions

theorem auto_step_memLp (d : ℕ) (p : Fin (d + 1) → ℝ) (q : ℝ≥0∞) :
    MemLp (auto (step d p)) q volume :=
  (continuous_auto_step d p).memLp_of_hasCompactSupport (hasCompactSupport_auto_step d p)

theorem auto_step_L1 (d : ℕ) (p : Fin (d + 1) → ℝ) (hp : ∀ i, 0 ≤ p i) :
    (eLpNorm (auto (step d p)) 1 volume).toReal = (∑ i, p i) ^ 2 := by
  rw [toReal_eLpNorm, lpNorm_one_eq_integral_norm (continuous_auto_step d p).aestronglyMeasurable]
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (auto_step_nonneg hp _)]
  exact integral_auto_step d p

theorem auto_step_L2_sq (d : ℕ) (p : Fin (d + 1) → ℝ) :
    (eLpNorm (auto (step d p)) 2 volume).toReal ^ 2 = ∫ x, auto (step d p) x ^ 2 := by
  rw [toReal_eLpNorm, lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    (continuous_auto_step d p).aestronglyMeasurable]
  norm_num [Real.norm_eq_abs, ← Real.sqrt_eq_rpow]
  rw [Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]

/-- An upper bound on every coefficient bounds the actual essential supremum. -/
theorem auto_step_Linf_le (d : ℕ) (p : Fin (d + 1) → ℝ) (hp : ∀ i, 0 ≤ p i)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ k : ℤ, convCoeff d p k ≤ M) :
    (eLpNorm (auto (step d p)) ∞ volume).toReal ≤ M := by
  rw [eLpNorm_exponent_top (continuous_auto_step d p).aestronglyMeasurable]
  have bound (x : ℝ) : ‖auto (step d p) x‖ ≤ M := by
    let k : ℤ := ⌊x - 1⌋
    have hl : (k : ℝ) ≤ x - 1 := Int.floor_le _
    have hr : x - 1 < (k : ℝ) + 1 := Int.lt_floor_add_one _
    let u : ℝ := x - ((k : ℝ) + 1)
    have hu : 0 ≤ u := by dsimp [u]; linarith
    have hu' : u ≤ 1 := by dsimp [u]; linarith
    have hx : (k : ℝ) + 1 + u = x := by dsimp [u]; ring
    rw [Real.norm_eq_abs, abs_of_nonneg (auto_step_nonneg hp _), ← hx,
      auto_step_interpolate _ _ _ _ hu hu']
    calc
      _ ≤ (1 - u) * M + u * M := add_le_add
        (mul_le_mul_of_nonneg_left (hb k) (by linarith))
        (mul_le_mul_of_nonneg_left (hb (k + 1)) hu)
      _ = M := by ring
  simpa [ENNReal.toReal_ofReal hM] using ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (eLpNormEssSup_le_of_ae_bound (.of_forall bound))

theorem auto_step_Linf_pos {d : ℕ} {p : Fin (d + 1) → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hne : ∃ i, 0 < p i) :
    0 < (eLpNorm (auto (step d p)) ∞ volume).toReal := by
  apply ENNReal.toReal_pos _ (auto_step_memLp d p ∞).eLpNorm_ne_top
  intro h
  exact auto_step_not_ae_zero hp hne ((eLpNorm_eq_zero_iff (by simp)).mp h)

/-- Summing over any finite set of unit cells on which two neighboring
coefficients agree gives a lower bound on the true squared L² norm. -/
theorem plateau_energy_le (d : ℕ) (p : Fin (d + 1) → ℝ) (S : Finset ℤ)
    (H : ℤ → ℝ) (hl : ∀ k ∈ S, convCoeff d p k = H k)
    (hr : ∀ k ∈ S, convCoeff d p (k + 1) = H k) :
    ∑ k ∈ S, (H k) ^ 2 ≤ (eLpNorm (auto (step d p)) 2 volume).toReal ^ 2 := by
  classical
  rw [auto_step_L2_sq]
  let I (k : ℤ) := Ico ((k : ℝ) + 1) ((k : ℝ) + 2)
  have hi := (auto_step_memLp d p 2).integrable_sq
  have disj : Set.Pairwise (↑S) (fun i j => Disjoint (I i) (I j)) := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    rintro x ⟨hx₁,hx₂⟩ ⟨hy₁,hy₂⟩
    rcases lt_or_gt_of_ne hij with h | h
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast (show i + 1 ≤ j by omega)
      linarith
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast (show j + 1 ≤ i by omega)
      linarith
  have unit (k : ℤ) (hk : k ∈ S) : (∫ x in I k, auto (step d p) x ^ 2) = (H k) ^ 2 := by
    calc
      _ = ∫ _ in I k, (H k) ^ 2 := by
        apply setIntegral_congr_fun measurableSet_Ico
        intro x hx
        change auto (step d p) x ^ 2 = (H k) ^ 2
        rw [auto_step_plateau _ _ _ _ (hl k hk) (hr k hk) x ⟨hx.1,hx.2.le⟩]
      _ = _ := by
        rw [setIntegral_const, Real.volume_real_Ico]
        have hh : (k : ℝ) + 2 - ((k : ℝ) + 1) = 1 := by ring
        simp [hh]
  calc
    _ = ∫ x in ⋃ k ∈ S, I k, auto (step d p) x ^ 2 := by
      rw [integral_biUnion_finset S (fun _ _ => measurableSet_Ico) disj
        (fun _ _ => hi.integrableOn)]
      exact Finset.sum_congr rfl fun k hk => (unit k hk).symm
    _ ≤ _ := setIntegral_le_integral hi (.of_forall fun x => sq_nonneg _)

/-- For block starts with distinct higher digits, distinctness of the unit cells
follows arithmetically. A block of width zero contributes zero. -/
theorem blocks_energy_le {ι : Type*} (d : ℕ) (p : Fin (d + 1) → ℝ)
    (D : ℕ) (T : Finset ι) (code width : ι → ℕ) (height : ι → ℝ)
    (hinj : Set.InjOn code (↑T)) (hw : ∀ i ∈ T, width i ≤ D)
    (heq : ∀ i ∈ T, ∀ h ≤ width i, convCoeff d p ((D * code i + h : ℕ) : ℤ) = height i) :
    ∑ i ∈ T, (width i : ℝ) * (height i) ^ 2 ≤ (eLpNorm (auto (step d p)) 2 volume).toReal ^ 2 := by
  classical
  let encode (i : ι) (h : ℕ) : ℤ := (D * code i + h : ℕ)
  let cells (i : ι) : Finset ℤ := (Finset.range (width i)).image (encode i)
  let S := T.biUnion cells
  have sep {i j : ι} {u v : ℕ} (hij : code i < code j) (hu : u < width i) (hi : i ∈ T) :
      D * code i + u < D * code j + v := by
    have ha := Nat.mul_le_mul_left D (show code i + 1 ≤ code j by omega)
    rw [Nat.mul_add, Nat.mul_one] at ha
    have := hw i hi
    omega
  have disj : Set.Pairwise (↑T) (fun i j => Disjoint (cells i) (cells j)) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨v,hv,h⟩ := Finset.mem_image.mp hz'
    have h' : D * code j + v = D * code i + u := by
      dsimp [encode] at h
      exact_mod_cast h
    have hne' : code i ≠ code j := fun hh => hij (hinj hi hj hh)
    rcases lt_or_gt_of_ne hne' with hc | hc
    · exact (sep (v := v) hc (Finset.mem_range.mp hu) hi).ne h'.symm
    · exact (sep (v := u) hc (Finset.mem_range.mp hv) hj).ne h'
  have mass : ∑ k ∈ S, (convCoeff d p k) ^ 2 = ∑ i ∈ T, (width i : ℝ) * (height i) ^ 2 := by
    rw [show S = T.biUnion cells from rfl, Finset.sum_biUnion disj]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show cells i = (Finset.range (width i)).image (encode i) from rfl,
      Finset.sum_image (fun u _ v _ huv => by
        have : D * code i + u = D * code i + v := by
          dsimp [encode] at huv
          exact_mod_cast huv
        omega)]
    calc
      _ = ∑ _h ∈ Finset.range (width i), (height i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [show convCoeff d p (encode i h) = height i from
          heq i hi h (Finset.mem_range.mp hh).le]
      _ = _ := by simp
  rw [← mass]
  apply plateau_energy_le _ _ S (convCoeff d p) (fun _ _ => rfl)
  intro z hz
  obtain ⟨i,hi,hzi⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp hzi
  have hm : h < width i := Finset.mem_range.mp hh
  have hcast : encode i h + 1 = ((D * code i + (h + 1) : ℕ) : ℤ) := by
    simp [encode, add_assoc]
  rw [hcast, heq i hi (h + 1) (by omega)]
  exact (heq i hi h hm.le).symm

/-- The contribution of an injectively indexed family of blocks to the ratio. -/
theorem ratio_ge_blocks {ι : Type*} (d : ℕ) (p : Fin (d + 1) → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hne : ∃ i, 0 < p i) (M : ℝ) (hM : 0 < M) (hb : ∀ k : ℤ, convCoeff d p k ≤ M)
    (D : ℕ) (T : Finset ι) (code width : ι → ℕ) (height : ι → ℝ)
    (hinj : Set.InjOn code (↑T)) (hw : ∀ i ∈ T, width i ≤ D)
    (heq : ∀ i ∈ T, ∀ h ≤ width i, convCoeff d p ((D * code i + h : ℕ) : ℤ) = height i) :
    (∑ i ∈ T, (width i : ℝ) * (height i) ^ 2) / ((∑ j, p j) ^ 2 * M) ≤ ratio (step d p) := by
  unfold ratio
  rw [auto_step_L1 d p hp]
  have hmass := pow_pos (sum_pos_of_positive_cell hp hne) 2
  exact div_le_div₀ (sq_nonneg _) (blocks_energy_le d p D T code width height hinj hw heq)
    (mul_pos hmass (auto_step_Linf_pos hp hne))
    (mul_le_mul_of_nonneg_left (auto_step_Linf_le d p hp M hM.le hb) hmass.le)

end Autoconvolutions
