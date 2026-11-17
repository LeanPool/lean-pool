/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianHermitePhaseSpectrum.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GaussianHermitePhase
public import LeanPool.GinibrePoincare.Analysis.GaussianDbarParseval

/-! # Mixed phase orthogonality and exact coefficient support -/


@[expose] public section


open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
open ComplexHermite
noncomputable section

private theorem unit_phase_clear (u : ℂ) (hu : ‖u‖ = 1) (p q s : ℕ) :
    (u ^ p * (conj u) ^ q) * u ^ (q + s) = u ^ (p + s) := by
  have hc : conj u * u = 1 := by
    rw [mul_comm, Complex.mul_conj, ← Complex.sq_norm, hu]
    norm_num
  rw [pow_add, pow_add]
  calc
    _ = (u ^ p * u ^ s) * ((conj u) ^ q * u ^ q) := by ring
    _ = _ := by rw [← mul_pow, hc]; simp

/-- Distinct mixed phase degrees are orthogonal on the entire Gaussian Hilbert space. -/
theorem inner_eq_zero_of_gaussian_mixed_phase_degrees_ne {n p q r s : ℕ} (hn : 0 < n)
    (x y : Lp ℂ 2 (complexGaussianMeasure n)) (hdeg : p + s ≠ r + q)
    (hx : ∀ (u : ℂ) (hu : ‖u‖ = 1), gaussianGlobalPhaseL2 hn u hu x =
      (u ^ p * (conj u) ^ q) • x)
    (hy : ∀ (u : ℂ) (hu : ‖u‖ = 1), gaussianGlobalPhaseL2 hn u hu y =
      (u ^ r * (conj u) ^ s) • y) : inner ℂ x y = 0 := by
  obtain ⟨u, hu, hsep⟩ := exists_unit_phase_pow_ne (p + s) (r + q) hdeg
  apply inner_eq_zero_of_isometry_eigencharacters (gaussianGlobalPhaseL2 hn u hu) x y
    (u ^ p * (conj u) ^ q) (u ^ r * (conj u) ^ s) (hx u hu) (hy u hu)
  intro he
  have hnorm : Complex.normSq (u ^ p * (conj u) ^ q) = 1 := by
    rw [← Complex.sq_norm, norm_mul, norm_pow, norm_pow, Complex.norm_conj, hu]
    norm_num
  have hc : u ^ p * (conj u) ^ q = u ^ r * (conj u) ^ s := by
    calc
      _ = (u ^ p * (conj u) ^ q) * 1 := by ring
      _ = (u ^ p * (conj u) ^ q) *
        (conj (u ^ p * (conj u) ^ q) * (u ^ r * (conj u) ^ s)) := by rw [he]
      _ = Complex.normSq (u ^ p * (conj u) ^ q) * (u ^ r * (conj u) ^ s) := by
        rw [← mul_assoc, Complex.mul_conj]
      _ = _ := by simp [hnorm]
  apply hsep
  calc
    u ^ (p + s) = (u ^ p * (conj u) ^ q) * u ^ (q + s) := (unit_phase_clear u hu p q s).symm
    _ = (u ^ r * (conj u) ^ s) * u ^ (s + q) := by rw [hc, Nat.add_comm q s]
    _ = _ := unit_phase_clear u hu r s q

/-- A genuine mixed phase eigenvector has coefficients only at its exact degree difference. -/
theorem gaussianHermiteCoefficient_eq_zero_of_mixed_phase {n r s : ℕ} (hn : 0 < n)
    (x : Lp ℂ 2 (complexGaussianMeasure n))
    (hx : ∀ (u : ℂ) (hu : ‖u‖ = 1), gaussianGlobalPhaseL2 hn u hu x =
      (u ^ r * (conj u) ^ s) • x)
    (pq : ComplexHermite.HermiteMultiIndex n)
    (hdeg : totalHolomorphicDegree pq.1 + s ≠ r + totalHolomorphicDegree pq.2) :
    gaussianHermiteCoefficient hn x pq = 0 := by
  rw [gaussianHermiteCoefficient_eq_inner]
  exact inner_eq_zero_of_gaussian_mixed_phase_degrees_ne hn
    (ComplexHermite.hermiteL2Family n hn pq) x hdeg
    (fun u hu => gaussianGlobalPhaseL2_hermite n hn u hu pq.1 pq.2) hx

/-- At a fixed mixed phase and bounded antiholomorphic degree, only finitely many
actual Hermite indices can occur. -/
theorem gaussian_mixed_phase_bounded_indices_finite (n r s K : ℕ) :
    {pq : ComplexHermite.HermiteMultiIndex n |
      ComplexHermite.totalAntiDegree pq ≤ K ∧
      totalHolomorphicDegree pq.1 + s = r + totalHolomorphicDegree pq.2}.Finite := by
  classical
  let S := {pq : ComplexHermite.HermiteMultiIndex n |
    ComplexHermite.totalAntiDegree pq ≤ K ∧
    totalHolomorphicDegree pq.1 + s = r + totalHolomorphicDegree pq.2}
  have hb (pq : S) (i : Fin n) : pq.val.1 i ≤ r + K ∧ pq.val.2 i ≤ K := by
    have hq : totalHolomorphicDegree pq.val.2 ≤ K := pq.property.1
    have hp : totalHolomorphicDegree pq.val.1 ≤ r + K := by
      have he := pq.property.2
      omega
    have hpi : pq.val.1 i ≤ totalHolomorphicDegree pq.val.1 :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hqi : pq.val.2 i ≤ totalHolomorphicDegree pq.val.2 :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact ⟨hpi.trans hp, hqi.trans hq⟩
  let f : S → (Fin n → Fin (r + K + 1)) × (Fin n → Fin (K + 1)) := fun pq =>
    (fun i => ⟨pq.val.1 i, Nat.lt_succ_of_le (hb pq i).1⟩,
      fun i => ⟨pq.val.2 i, Nat.lt_succ_of_le (hb pq i).2⟩)
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact congrArg Fin.val (congrFun (congrArg Prod.fst he) i)
    · funext i
      exact congrArg Fin.val (congrFun (congrArg Prod.snd he) i)
  let : Finite S := Finite.of_injective f hf
  exact Set.toFinite S

/-- Every actual fixed mixed-phase vector with bounded anti degree is a finite
Hermite polynomial, without any polynomial assumption on the input. -/
theorem gaussian_mixed_phase_finite_reconstruction {n r s K : ℕ} (hn : 0 < n)
    (x : Lp ℂ 2 (complexGaussianMeasure n))
    (hx : ∀ (u : ℂ) (hu : ‖u‖ = 1), gaussianGlobalPhaseL2 hn u hu x =
      (u ^ r * (conj u) ^ s) • x)
    (hanti : ∀ pq : ComplexHermite.HermiteMultiIndex n,
      K < ComplexHermite.totalAntiDegree pq → gaussianHermiteCoefficient hn x pq = 0) :
    ∃ c : ComplexHermite.HermiteMultiIndex n →₀ ℂ,
      ComplexHermite.finiteHermiteCombination n hn c = x ∧
      ∀ pq ∈ c.support, ComplexHermite.totalAntiDegree pq ≤ K ∧
        totalHolomorphicDegree pq.1 + s = r + totalHolomorphicDegree pq.2 := by
  classical
  let S := {pq : ComplexHermite.HermiteMultiIndex n |
    ComplexHermite.totalAntiDegree pq ≤ K ∧
    totalHolomorphicDegree pq.1 + s = r + totalHolomorphicDegree pq.2}
  have hS : S.Finite := gaussian_mixed_phase_bounded_indices_finite n r s K
  have hzero : ∀ pq ∉ S, gaussianHermiteCoefficient hn x pq = 0 := by
    intro pq hpq
    by_cases ha : ComplexHermite.totalAntiDegree pq ≤ K
    · have he : totalHolomorphicDegree pq.1 + s ≠ r + totalHolomorphicDegree pq.2 := by
        intro he
        exact hpq ⟨ha, he⟩
      exact gaussianHermiteCoefficient_eq_zero_of_mixed_phase hn x hx pq he
    · exact hanti pq (lt_of_not_ge ha)
  let c : ComplexHermite.HermiteMultiIndex n →₀ ℂ :=
    Finsupp.onFinset hS.toFinset (gaussianHermiteCoefficient hn x) (by
      intro pq hpq
      by_contra hs
      exact hpq (hzero pq (by simpa using hs)))
  refine ⟨c, ?_, ?_⟩
  · apply (gaussianHermiteHilbertBasis n hn).repr.injective
    ext pq
    change gaussianHermiteCoefficient hn (ComplexHermite.finiteHermiteCombination n hn c) pq =
      gaussianHermiteCoefficient hn x pq
    rw [gaussianHermiteCoefficient_finiteHermiteCombination]
    rfl
  · intro pq hpq
    by_contra hs
    have hc : c pq = 0 := hzero pq hs
    exact (Finsupp.mem_support_iff.mp hpq) hc

/-- A genuine Gaussian holomorphic phase eigenvector has finite homogeneous
Hermite support, even when no polynomial representation is assumed. -/
theorem gaussian_holomorphic_phase_finite_reconstruction {n r : ℕ} (hn : 0 < n)
    (x : Lp ℂ 2 (complexGaussianMeasure n))
    (hx : x ∈ hermiteAntiDegreeClosedSpan n hn 0)
    (hphase : ∀ (u : ℂ) (hu : ‖u‖ = 1),
      gaussianGlobalPhaseL2 hn u hu x = u ^ r • x) :
    ∃ c : ComplexHermite.HermiteMultiIndex n →₀ ℂ,
      ComplexHermite.finiteHermiteCombination n hn c = x ∧
      ∀ pq ∈ c.support, ComplexHermite.totalAntiDegree pq = 0 ∧
        totalHolomorphicDegree pq.1 = r := by
  have hzero : gaussianHermiteMode hn 0 x = x := by
    rw [gaussianHermiteMode_eq_antiDegreeProjection]
    exact Submodule.starProjection_eq_self_iff.mpr hx
  have hanti : ∀ pq : ComplexHermite.HermiteMultiIndex n,
      0 < ComplexHermite.totalAntiDegree pq → gaussianHermiteCoefficient hn x pq = 0 := by
    intro pq hpq
    have h := inner_basis_gaussianHermiteMode hn x 0 pq
    rw [hzero, ite_eq_right (by omega)] at h
    rw [gaussianHermiteCoefficient_eq_inner]
    exact h
  obtain ⟨c, hc, hs⟩ := gaussian_mixed_phase_finite_reconstruction (r := r) (s := 0)
    (K := 0) hn x (by simpa using hphase) hanti
  refine ⟨c, hc, ?_⟩
  intro pq hpq
  obtain ⟨ha, hd⟩ := hs pq hpq
  have ha0 : ComplexHermite.totalAntiDegree pq = 0 := by omega
  refine ⟨ha0, ?_⟩
  change totalHolomorphicDegree pq.2 = 0 at ha0
  omega

end
end GinibrePoincare
