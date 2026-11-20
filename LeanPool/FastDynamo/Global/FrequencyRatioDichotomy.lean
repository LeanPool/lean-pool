/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.CellGeometry

/-!
# The frequency-ratio dichotomy of distinct cells

For the rounded frequencies `K n` and core scales `ell n` of a scale family, this file
defines the frequency ratio `frequencyRatio n m = K n / K m` of the `n`th Fourier mode seen in
the `m`th cell and proves

* geometric growth restarted at an arbitrary cell, `K (n + k) ≥ q^k K n`;
* the dichotomy for distinct cells: the ratio is at least `q` or at most `q⁻¹`
  (`nonselected_frequencyRatio_dichotomy`), the two geometric branches of the proof of
  `prop:background-resolvent`;
* the identity of the scale ratio with the inverse frequency ratio
  (`ell_ratio_eq_frequencyRatio`).

`Global/TorusBackgroundParameters.lean` uses the dichotomy for the background parameters.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

namespace ScaleFamily

variable {p : LocalSeedParameters} {r : ScaleRatios p}

/-! ## Two-index frequency and scale identities -/

/-- The frequency ratio appearing when the `n`th Fourier mode is inspected
inside the `m`th cell. -/
def frequencyRatio (f : ScaleFamily r) (n m : ℕ) : ℝ :=
  (f.fourierIndex n : ℝ) / (f.fourierIndex m : ℝ)

/-- A cell inspected at its own Fourier mode has frequency ratio `1`. -/
@[simp] theorem frequencyRatio_self (f : ScaleFamily r) (n : ℕ) :
    f.frequencyRatio n n = 1 := by
  exact div_self (ne_of_gt (Nat.cast_pos.2 (f.fourierIndex_pos n)))

/-- Geometric growth restarted at an arbitrary cell, rather than only at
`K0`. -/
theorem fourierIndex_geometric_from (f : ScaleFamily r) (n k : ℕ) :
    r.q ^ k * (f.fourierIndex n : ℝ) ≤
      (f.fourierIndex (n + k) : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hq : 0 ≤ r.q := r.q_pos.le
      have hKnk : 0 < (f.fourierIndex (n + k) : ℝ) :=
        Nat.cast_pos.2 (f.fourierIndex_pos (n + k))
      have hstep : r.q * (f.fourierIndex (n + k) : ℝ) ≤
          (f.fourierIndex (n + k + 1) : ℝ) :=
        (le_div_iff₀ hKnk).mp (f.adjacent_ratio_lower (n + k))
      calc
        r.q ^ (k + 1) * (f.fourierIndex n : ℝ) =
            r.q * (r.q ^ k * (f.fourierIndex n : ℝ)) := by ring
        _ ≤ r.q * (f.fourierIndex (n + k) : ℝ) :=
          mul_le_mul_of_nonneg_left ih hq
        _ ≤ (f.fourierIndex (n + k + 1) : ℝ) := hstep
        _ = (f.fourierIndex (n + (k + 1)) : ℝ) := by
          simp [Nat.add_assoc]

/-- A later cell has frequency at least `q` times that of any earlier cell. -/
theorem q_le_frequencyRatio_of_lt (f : ScaleFamily r) {n m : ℕ}
    (hnm : n < m) :
    r.q ≤ f.frequencyRatio m n := by
  obtain ⟨k, rfl⟩ : ∃ k, m = n + (k + 1) := by
    use m - n - 1
    omega
  have hKn : 0 < (f.fourierIndex n : ℝ) :=
    Nat.cast_pos.2 (f.fourierIndex_pos n)
  apply (le_div_iff₀ hKn).2
  have hgeom := f.fourierIndex_geometric_from n (k + 1)
  have hqpow : r.q ≤ r.q ^ (k + 1) := by
    rw [pow_succ']
    simpa using mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ r.one_lt_q.le (Nat.zero_le k)) r.q_pos.le
  calc
    r.q * (f.fourierIndex n : ℝ) ≤
        r.q ^ (k + 1) * (f.fourierIndex n : ℝ) :=
      mul_le_mul_of_nonneg_right hqpow hKn.le
    _ ≤ (f.fourierIndex (n + (k + 1)) : ℝ) := hgeom

/-- Looking from a later mode into an earlier cell gives the reciprocal
branch of the ratio dichotomy. -/
theorem frequencyRatio_le_inv_q_of_lt (f : ScaleFamily r) {n m : ℕ}
    (hnm : n < m) :
    f.frequencyRatio n m ≤ r.q⁻¹ := by
  have hratio := f.q_le_frequencyRatio_of_lt hnm
  have hKn : 0 < (f.fourierIndex n : ℝ) :=
    Nat.cast_pos.2 (f.fourierIndex_pos n)
  have hKm : 0 < (f.fourierIndex m : ℝ) :=
    Nat.cast_pos.2 (f.fourierIndex_pos m)
  have hq : 0 < r.q := r.q_pos
  change (f.fourierIndex n : ℝ) / (f.fourierIndex m : ℝ) ≤ r.q⁻¹
  change r.q ≤
    (f.fourierIndex m : ℝ) / (f.fourierIndex n : ℝ) at hratio
  apply (div_le_iff₀ hKm).2
  have hcross : r.q * (f.fourierIndex n : ℝ) ≤
      (f.fourierIndex m : ℝ) := (le_div_iff₀ hKn).1 hratio
  calc
    (f.fourierIndex n : ℝ) = r.q⁻¹ *
        (r.q * (f.fourierIndex n : ℝ)) := by field_simp
    _ ≤ r.q⁻¹ * (f.fourierIndex m : ℝ) :=
      mul_le_mul_of_nonneg_left hcross (inv_nonneg.mpr hq.le)

/-- For distinct cells, the frequency ratio is separated from one on one of the two
geometric branches `r_m ≥ q`, `r_m ≤ q⁻¹` of the proof of `prop:background-resolvent`. -/
theorem nonselected_frequencyRatio_dichotomy (f : ScaleFamily r)
    {m n : ℕ} (hmn : m ≠ n) :
    r.q ≤ f.frequencyRatio n m ∨
      f.frequencyRatio n m ≤ r.q⁻¹ := by
  rcases lt_or_gt_of_ne hmn with hmn' | hnm'
  · exact Or.inl (f.q_le_frequencyRatio_of_lt hmn')
  · exact Or.inr (f.frequencyRatio_le_inv_q_of_lt hnm')

/-- The scale ratio is exactly the inverse-looking frequency ratio. -/
theorem ell_ratio_eq_frequencyRatio (f : ScaleFamily r) (n m : ℕ) :
    f.ell m / f.ell n = f.frequencyRatio n m := by
  unfold ell frequencyRatio
  field_simp [ne_of_gt (Nat.cast_pos.2 p.kStar_pos),
    ne_of_gt (Nat.cast_pos.2 (f.fourierIndex_pos n)),
    ne_of_gt (Nat.cast_pos.2 (f.fourierIndex_pos m))]

end ScaleFamily

end

end FastDynamo
