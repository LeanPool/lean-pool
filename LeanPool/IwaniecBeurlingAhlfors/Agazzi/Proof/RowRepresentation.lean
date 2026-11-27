/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.Agazzi.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.Function

/-!
# §2: the row representation of `L` (Lemma 3)

The notation of §2 (TeX lines 332–344). For a matrix `A` with rows `A¹ = A 0`, `A² = A 1`:

* `rot a = J a`, `J = [[0, −1], [1, 0]]`, and `det2 a b = det (a, b) = J a · b`
  (`det_eq_det2`, `det2_eq_rot_dotProduct`);
* `euclidNorm a = |a|`, the Euclidean norm of `a ∈ ℝ²`, and `unitCircle = 𝕊¹`;
* `rowG z a b = G_z (a, b) = det (z, b) + z · (a − z)`;
* `rowF A = F (A) = sup_{|z| = 1} G_z (A¹, A²)`, which is `|A² + J A¹| − 1 = 2 |a₊| − 1`
  (`rowF_eq_norm`, `rowF_eq`), a convex function (`convexOn_rowF`);
* `rowZ a = 𝒵 (a) = 𝕊¹ ∪ {a}` if `|a| ≤ 1`, `𝕊¹` if `|a| > 1`.

Lemma 3 (`lemma3`, the display `(eq:L-row-representation)`):
`L (A) = sup_{z ∈ 𝒵 (A¹)} G_z (A¹, A²)`. Its consequences `G_z (A¹, A²) ≤ L (A)` for
`z ∈ 𝒵 (A¹)` (`rowG_le_integrandL`) and `F ≤ L` (`rowF_le_integrandL`); `|a| = √(a₁² + a₂²)`
(`euclidNorm_eq`).
-/

@[expose] public section

noncomputable section

namespace Agazzi

/-- `J a = (−a₂, a₁)`, the rotation by `π/2`: `J = [[0, −1], [1, 0]]`. -/
def rot (a : Fin 2 → ℝ) : Fin 2 → ℝ := ![-a 1, a 0]

/-- `det (a, b) = a₁ b₂ − a₂ b₁`, the determinant of the matrix with rows `a`, `b`. -/
def det2 (a b : Fin 2 → ℝ) : ℝ := a 0 * b 1 - a 1 * b 0

/-- The Euclidean norm `|a|` of `a ∈ ℝ²`. -/
def euclidNorm (a : Fin 2 → ℝ) : ℝ := ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin 2))‖

/-- The unit circle `𝕊¹ = {z : |z| = 1}`. -/
def unitCircle : Set (Fin 2 → ℝ) := {z | euclidNorm z = 1}

/-- `G_z (a, b) = det (z, b) + z · (a − z)`. -/
def rowG (z a b : Fin 2 → ℝ) : ℝ := det2 z b + z ⬝ᵥ (a - z)

/-- `F (A) = sup_{|z| = 1} G_z (A¹, A²)`. -/
def rowF (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  sSup ((fun z => rowG z (A 0) (A 1)) '' unitCircle)

open Classical in
/-- `𝒵 (a) = 𝕊¹ ∪ {a}` if `|a| ≤ 1`, and `𝒵 (a) = 𝕊¹` if `|a| > 1`. -/
def rowZ (a : Fin 2 → ℝ) : Set (Fin 2 → ℝ) :=
  unitCircle ∪ (if euclidNorm a ≤ 1 then {a} else ∅)

/-- `det A = det (A¹, A²) = J A¹ · A²` (TeX line 335).

Proof: both are `a₁₁ a₂₂ − a₁₂ a₂₁`. -/
theorem det_eq_det2 (A : Matrix (Fin 2) (Fin 2) ℝ) : A.det = det2 (A 0) (A 1) := by
  rw [Matrix.det_fin_two, det2]

/-- `det (a, b) = J a · b`. Proof: both are `a₁ b₂ − a₂ b₁`. -/
theorem det2_eq_rot_dotProduct (a b : Fin 2 → ℝ) : det2 a b = rot a ⬝ᵥ b := by
  simp [det2, rot, dotProduct, Fin.sum_univ_two]
  ring

/-- `|a| = √(a₁² + a₂²)`. -/
theorem euclidNorm_eq (a : Fin 2 → ℝ) : euclidNorm a = √(a 0 ^ 2 + a 1 ^ 2) := by
  rw [euclidNorm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

private lemma rowalg_mem_unitCircle {z : Fin 2 → ℝ} : z ∈ unitCircle ↔ z 0 ^ 2 + z 1 ^ 2 = 1 := by
  rw [unitCircle, Set.mem_ofPred_eq, euclidNorm_eq, Real.sqrt_eq_one]

/-- `G_z (a, b) = z₁ (a₁ + b₂) + z₂ (a₂ − b₁) − |z|²`. -/
private lemma rowalg_rowG (z a b : Fin 2 → ℝ) :
    rowG z a b = z 0 * (a 0 + b 1) + z 1 * (a 1 - b 0) - (z 0 ^ 2 + z 1 ^ 2) := by
  simp [rowG, det2, dotProduct, Fin.sum_univ_two]
  ring

/-- `|A² + J A¹| − 1` is the largest value of `G_z (A¹, A²)` on `𝕊¹`: for `|z| = 1`,
`G_z (A¹, A²) = z · v − 1` with `v = A¹ − J A²`, `|v| = |A² + J A¹|`; Cauchy–Schwarz, with equality
at `z = v / |v|` (any unit `z` if `v = 0`). -/
private lemma rowalg_isGreatest (A : Matrix (Fin 2) (Fin 2) ℝ) :
    IsGreatest ((fun z => rowG z (A 0) (A 1)) '' unitCircle)
      (euclidNorm (A 1 + rot (A 0)) - 1) := by
  set v0 := A 0 0 + A 1 1
  set v1 := A 0 1 - A 1 0
  have hn : euclidNorm (A 1 + rot (A 0)) = √(v0 ^ 2 + v1 ^ 2) := by
    rw [euclidNorm_eq]
    congr 1
    simp [rot, v0, v1]
    ring
  rw [hn]
  set s := √(v0 ^ 2 + v1 ^ 2)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = v0 ^ 2 + v1 ^ 2 := Real.sq_sqrt (by positivity)
  have hG : ∀ z : Fin 2 → ℝ, z ∈ unitCircle →
      rowG z (A 0) (A 1) = z 0 * v0 + z 1 * v1 - 1 := by
    intro z hz
    rw [rowalg_mem_unitCircle] at hz
    rw [rowalg_rowG, hz]
  constructor
  · by_cases h0 : s = 0
    · have hv : v0 ^ 2 + v1 ^ 2 = 0 := by rw [← hs2, h0]; ring
      have hv0' : v0 = 0 := by nlinarith [sq_nonneg v0, sq_nonneg v1]
      have hv1' : v1 = 0 := by nlinarith [sq_nonneg v0, sq_nonneg v1]
      have hmem : (![1, 0] : Fin 2 → ℝ) ∈ unitCircle := by
        rw [rowalg_mem_unitCircle]; simp
      refine ⟨![1, 0], hmem, ?_⟩
      simp only
      rw [hG _ hmem, h0, hv0', hv1']
      simp
    · have hpos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h0)
      have hmem : (![v0 / s, v1 / s] : Fin 2 → ℝ) ∈ unitCircle := by
        rw [rowalg_mem_unitCircle]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        rw [div_pow, div_pow, ← add_div, ← hs2]
        exact div_self (by positivity)
      refine ⟨_, hmem, ?_⟩
      simp only
      rw [hG _ hmem]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      field_simp
      rw [← hs2]
      ring
  · rintro _ ⟨z, hz, rfl⟩
    simp only
    rw [hG z hz]
    rw [rowalg_mem_unitCircle] at hz
    have hL : (z 0 * v0 + z 1 * v1) ^ 2 ≤ v0 ^ 2 + v1 ^ 2 := by
      have : (z 0 * v0 + z 1 * v1) ^ 2 =
          (z 0 ^ 2 + z 1 ^ 2) * (v0 ^ 2 + v1 ^ 2) - (z 0 * v1 - z 1 * v0) ^ 2 := by ring
      rw [this, hz]
      nlinarith [sq_nonneg (z 0 * v1 - z 1 * v0)]
    have := Real.abs_le_sqrt hL
    linarith [le_abs_self (z 0 * v0 + z 1 * v1)]

/-- `F (A) = |A² + J A¹| − 1` (TeX line 341).

Proof: for `|z| = 1`, `G_z (A¹, A²) = z · v − 1` with `v = A¹ − J A²`, and `|v| = |A² + J A¹|`; by
Cauchy–Schwarz the supremum is `|v| − 1`, attained at `z = v / |v|` (at any unit `z` if `v = 0`). -/
theorem rowF_eq_norm (A : Matrix (Fin 2) (Fin 2) ℝ) :
    rowF A = euclidNorm (A 1 + rot (A 0)) - 1 :=
  (rowalg_isGreatest A).csSup_eq

/-- `F (A) = 2 |a₊| − 1` (TeX line 341).

Proof: `A² + J A¹ = (a₂₁ − a₁₂, a₂₂ + a₁₁)`, of length `2 |a₊|`. -/
theorem rowF_eq (A : Matrix (Fin 2) (Fin 2) ℝ) : rowF A = 2 * ‖conformalPart A‖ - 1 := by
  rw [rowF_eq_norm, euclidNorm_eq]
  congr 1
  rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity), mul_pow, Complex.sq_norm,
    Complex.normSq_apply]
  simp [rot, conformalPart]
  ring

/-- `F` is convex (TeX line 344).

Proof: `F (A) = 2 |a₊| − 1` (`rowF_eq`), with `a₊` real-linear in `A`; the triangle inequality.
-/
theorem convexOn_rowF : ConvexOn ℝ Set.univ rowF := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [rowF_eq, smul_eq_mul]
  have hlin : conformalPart (a • x + b • y) =
      (a : ℂ) * conformalPart x + (b : ℂ) * conformalPart y := by
    apply Complex.ext <;> simp [conformalPart] <;> ring
  rw [hlin]
  have h := norm_add_le ((a : ℂ) * conformalPart x) ((b : ℂ) * conformalPart y)
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb] at h
  nlinarith

/-- `G_{A¹} (A¹, A²) = det A`. -/
private lemma rowalg_rowG_self (A : Matrix (Fin 2) (Fin 2) ℝ) :
    rowG (A 0) (A 0) (A 1) = A.det := by
  rw [rowG, sub_self, dotProduct_zero, add_zero, det_eq_det2]

/-- `det A = |a₊|² − |a₋|²` (as `Agazzi.det_eq` of `Agazzi.Bridges`). -/
private lemma rowalg_det_eq (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.det = ‖conformalPart A‖ ^ 2 - ‖anticonformalPart A‖ ^ 2 := by
  rw [Matrix.det_fin_two, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [conformalPart, anticonformalPart]
  ring

/-- The first identity of the proof of Lemma 3:
`det A − F (A) = (1 − |a₊| − |a₋|) (1 − |a₊| + |a₋|)`. -/
private lemma rowalg_det_sub_rowF (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.det - rowF A = (1 - ‖conformalPart A‖ - ‖anticonformalPart A‖) *
      (1 - ‖conformalPart A‖ + ‖anticonformalPart A‖) := by
  rw [rowalg_det_eq, rowF_eq]
  ring

/-- `|A¹| = |a₊ + ā₋|`: the first row of `A` is `(a₁₁, a₁₂)` and `a₊ + ā₋ = a₁₁ − i a₁₂`. -/
private lemma rowalg_euclidNorm_row0 (A : Matrix (Fin 2) (Fin 2) ℝ) :
    euclidNorm (A 0) = ‖conformalPart A + (starRingEnd ℂ) (anticonformalPart A)‖ := by
  rw [euclidNorm_eq, Complex.norm_eq_sqrt_sq_add_sq]
  congr 1
  simp [conformalPart, anticonformalPart]
  ring

/-- The second identity of the proof of Lemma 3: `||a₊| − |a₋|| ≤ |A¹| ≤ |a₊| + |a₋|`. -/
private lemma rowalg_row0_bounds (A : Matrix (Fin 2) (Fin 2) ℝ) :
    |‖conformalPart A‖ - ‖anticonformalPart A‖| ≤ euclidNorm (A 0) ∧
      euclidNorm (A 0) ≤ ‖conformalPart A‖ + ‖anticonformalPart A‖ := by
  rw [rowalg_euclidNorm_row0]
  constructor
  · have h := abs_norm_sub_norm_le (conformalPart A) (-(starRingEnd ℂ) (anticonformalPart A))
    rwa [norm_neg, Complex.norm_conj, sub_neg_eq_add] at h
  · have h := norm_add_le (conformalPart A) ((starRingEnd ℂ) (anticonformalPart A))
    rwa [Complex.norm_conj] at h

/-- **Lemma 3** (`eq:L-row-representation`). `L (A) = sup_{z ∈ 𝒵 (A¹)} G_z (A¹, A²)`. -/
theorem lemma3 (A : Matrix (Fin 2) (Fin 2) ℝ) :
    integrandL A = sSup ((fun z => rowG z (A 0) (A 1)) '' rowZ (A 0)) := by
  -- `G_{A¹} (A¹, A²) = det A`, so the supremum over `𝒵 (A¹)` is `max {det A, F (A)}` if
  -- `|A¹| ≤ 1` and `F (A)` if `|A¹| > 1`.
  have hsup : sSup ((fun z => rowG z (A 0) (A 1)) '' rowZ (A 0)) =
      if euclidNorm (A 0) ≤ 1 then max A.det (rowF A) else rowF A := by
    have hG := rowalg_isGreatest A
    by_cases h : euclidNorm (A 0) ≤ 1
    · rw [ite_eq_left h, rowZ, ite_eq_left h, Set.image_union, Set.image_singleton,
        rowalg_rowG_self, csSup_union hG.bddAbove hG.nonempty bddAbove_singleton
          (Set.singleton_nonempty _), csSup_singleton, rowF]
      exact sup_comm _ _
    · rw [ite_eq_right h, rowZ, ite_eq_right h, Set.union_empty, rowF]
  rw [hsup]
  -- The identities `det A − F (A) = (1 − |a₊| − |a₋|) (1 − |a₊| + |a₋|)` and
  -- `||a₊| − |a₋|| ≤ |A¹| ≤ |a₊| + |a₋|`.
  have hid := rowalg_det_sub_rowF A
  obtain ⟨hlo, hhi⟩ := rowalg_row0_bounds A
  have hm := norm_nonneg (anticonformalPart A)
  by_cases h1 : ‖conformalPart A‖ + ‖anticonformalPart A‖ ≤ 1
  · -- `|a₊| + |a₋| ≤ 1`: then `|A¹| ≤ 1` and `det A ≥ F (A)`.
    have hA : euclidNorm (A 0) ≤ 1 := hhi.trans h1
    have hdet : rowF A ≤ A.det := by
      have : 0 ≤ (1 - ‖conformalPart A‖ - ‖anticonformalPart A‖) *
          (1 - ‖conformalPart A‖ + ‖anticonformalPart A‖) :=
        mul_nonneg (by linarith) (by linarith)
      linarith
    rw [integrandL, ite_eq_left h1, ite_eq_left hA, max_eq_left hdet, rowalg_det_eq]
  · by_cases hA : euclidNorm (A 0) ≤ 1
    · -- `|a₊| + |a₋| > 1` and `|A¹| ≤ 1`: then `|a₊| − |a₋| ≤ 1` and `det A ≤ F (A)`.
      have hpm : ‖conformalPart A‖ - ‖anticonformalPart A‖ ≤ 1 :=
        (le_abs_self _).trans (hlo.trans hA)
      have hdet : A.det ≤ rowF A := by
        have : (1 - ‖conformalPart A‖ - ‖anticonformalPart A‖) *
            (1 - ‖conformalPart A‖ + ‖anticonformalPart A‖) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
        linarith
      rw [integrandL, ite_eq_right h1, ite_eq_left hA, max_eq_right hdet, rowF_eq]
    · -- `|A¹| > 1`: then `|a₊| + |a₋| > 1` and `𝒵 (A¹) = 𝕊¹`.
      have h1' : 1 < ‖conformalPart A‖ + ‖anticonformalPart A‖ := (not_le.1 hA).trans_le hhi
      rw [integrandL, ite_eq_right h1'.not_ge, ite_eq_right hA, rowF_eq]

/-- `𝕊¹ ⊆ 𝒵 (a)`. -/
private lemma rowalg_unitCircle_subset_rowZ (a : Fin 2 → ℝ) : unitCircle ⊆ rowZ a :=
  Set.subset_union_left

/-- The values `G_z (A¹, A²)`, `z ∈ 𝒵 (A¹)`, are bounded above. -/
private lemma rowalg_bddAbove_rowZ (A : Matrix (Fin 2) (Fin 2) ℝ) :
    BddAbove ((fun z => rowG z (A 0) (A 1)) '' rowZ (A 0)) := by
  rw [rowZ, Set.image_union]
  refine BddAbove.union (rowalg_isGreatest A).bddAbove ?_
  split_ifs
  · rw [Set.image_singleton]; exact bddAbove_singleton
  · rw [Set.image_empty]; exact bddAbove_empty

/-- `G_z (A¹, A²) ≤ L (A)` for `z ∈ 𝒵 (A¹)` (Lemma 3). -/
theorem rowG_le_integrandL (A : Matrix (Fin 2) (Fin 2) ℝ) {z : Fin 2 → ℝ} (hz : z ∈ rowZ (A 0)) :
    rowG z (A 0) (A 1) ≤ integrandL A := by
  rw [lemma3]
  exact le_csSup (rowalg_bddAbove_rowZ A) (Set.mem_image_of_mem _ hz)

/-- `F (A) ≤ L (A)` (Lemma 3: `F (A)` is a value `G_z (A¹, A²)` with `|z| = 1`). -/
theorem rowF_le_integrandL (A : Matrix (Fin 2) (Fin 2) ℝ) : rowF A ≤ integrandL A := by
  obtain ⟨z, hz, hzF⟩ := (rowalg_isGreatest A).1
  rw [rowF_eq_norm, ← hzF]
  exact rowG_le_integrandL A (rowalg_unitCircle_subset_rowZ _ hz)

end Agazzi
