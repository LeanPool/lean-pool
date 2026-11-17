/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.FilteredDeterminant
import LeanPool.CCDN.Determinant.HypersurfaceHilbert

/-! A coefficient-independent local determinant exponent for hypersurfaces.
The exponent is an explicit finite sum depending only on dimension,
multiplicity and the number of rows, and admits sharp binomial cutoff bounds. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Deficit exponent from the cumulative bound μ binomial(n+k,n), where n
is the hypersurface dimension. -/
def hypersurfaceMultiplicityExponent (n μ s : ℕ) : ℕ :=
  Finset.univ.sum fun k : Fin s => s - μ * (n + k.val).choose n

private lemma hypersurfaceMultiplicityExponent_le_origin {K : Type*} [Field K] {n μ s : ℕ}
    (f : MvPolynomial (Fin (n + 2)) K)
    (hf : f ∈ idealOfVars (Fin (n + 2)) K ^ μ)
    (hμ : homogeneousComponent μ f ≠ 0) :
    hypersurfaceMultiplicityExponent (n + 1) μ s ≤
      filtrationExponent (fun k => Module.finrank K (originLayer f k)) s := by
  unfold hypersurfaceMultiplicityExponent filtrationExponent
  apply Finset.sum_le_sum
  intro k _
  have h := originLayer_cumulative_le f hf hμ k.val
  rw [show n + k.val + 1 = n + 1 + k.val by omega] at h
  exact Nat.sub_le_sub_left h s

private lemma hypersurface_cumulative_capacity_ge (n k : ℕ) {μ : ℕ} (hμ : 0 < μ) :
    k + 1 ≤ μ * (n + 1 + k).choose (n + 1) := by
  have h := Nat.choose_le_choose k (show 1 + k ≤ n + 1 + k by omega)
  rw [Nat.choose_symm_add (a := n + 1)]
  rw [Nat.add_comm 1 k, Nat.choose_succ_self_right] at h
  exact h.trans (Nat.le_mul_of_pos_left _ hμ)

/-- Hockey-stick identity: `∑_{k < K} (n + k).choose n = (n + K).choose (n + 1)`. -/
lemma sum_cumulative_binomial (n K : ℕ) :
    (∑ k ∈ Finset.range K, (n + k).choose n) = (n + K).choose (n + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    rw [show n + (K + 1) = (n + K) + 1 by omega, Nat.choose_succ_succ']
    omega

/-- Cutoffs beyond s add no positive deficits. Hence the finite
exponent controls every numerical cutoff. -/
private lemma sum_hypersurface_deficits_le (n s K : ℕ) {μ : ℕ} (hμ : 0 < μ) :
    (∑ k ∈ Finset.range K, (s - μ * (n + 1 + k).choose (n + 1))) ≤
      hypersurfaceMultiplicityExponent (n + 1) μ s := by
  unfold hypersurfaceMultiplicityExponent
  rw [Fin.sum_univ_eq_sum_range (fun k => s - μ * (n + 1 + k).choose (n + 1))]
  by_cases hK : K ≤ s
  · exact Finset.sum_le_sum_of_subset (Finset.range_mono hK)
  · have hsub : Finset.range s ⊆ Finset.range K := Finset.range_mono (by omega)
    have he := Finset.sum_subset hsub (f := fun k => s - μ * (n + 1 + k).choose (n + 1))
    apply le_of_eq (he ?_).symm
    intro k _ hk
    have hs : s ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    have hc := hypersurface_cumulative_capacity_ge n k hμ
    omega

/-- Exact integer cutoff inequality. Optimizing K gives the leading
(n!/μ)^(1/n) * n/(n+1) * s^(1+1/n) term of CCDN's local determinant bound. -/
theorem hypersurfaceMultiplicityExponent_cutoff (n s K : ℕ) {μ : ℕ} (hμ : 0 < μ) :
    s * K ≤ hypersurfaceMultiplicityExponent (n + 1) μ s +
      μ * (n + 1 + K).choose (n + 2) := by
  have hsum := Finset.sum_le_sum (s := Finset.range K)
    (f := fun _ => s)
    (g := fun k => (s - μ * (n + 1 + k).choose (n + 1)) +
      μ * (n + 1 + k).choose (n + 1)) (fun k _ => by omega)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_cumulative_binomial] at hsum
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum
  have h := sum_hypersurface_deficits_le n s K hμ
  nlinarith

/-- Every evaluation determinant in one hypersurface residue class has the
explicit dimension/multiplicity divisor, even for zeros only modulo that power. -/
theorem hypersurface_pow_dvd_det_mod {p n μ s : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 2)) ℤ)
    (hf : map (Int.castRingHom (ZMod p)) f ∈ idealOfVars (Fin (n + 2)) (ZMod p) ^ μ)
    (hμ : homogeneousComponent μ (map (Int.castRingHom (ZMod p)) f) ≠ 0)
    (x : Fin s → Fin (n + 2) → ℤ) (hx : ∀ i j, (p : ℤ) ∣ x i j)
    (hfx : ∀ i, (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) μ s ∣ eval (x i) f)
    (F : Fin s → MvPolynomial (Fin (n + 2)) ℤ) :
    (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) μ s ∣
      (Matrix.of fun i j => eval (x i) (F j)).det :=
  origin_filtration_pow_dvd_det_mod f x hx
    (hypersurfaceMultiplicityExponent_le_origin _ hf hμ) hfx F

end
end CCDN
