/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.PowerSeries.Basic
import LeanPool.CCDN.Algebra.SectionImageRank
import LeanPool.CCDN.Hilbert.PlaneHilbert
import LeanPool.CCDN.Noether.PowerSeriesFrobenius
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! A local Bézout bound on formal vanishing orders. It gives injective jets
on low-degree functions and verifies the jet condition in Frobenius
noncancellation for irreducible plane curves. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- If `X ^ N` divides the power series `g`, then the images of `1, X, …, X ^ (N - 1)` in the
quotient by `g` are linearly independent. -/
lemma powerSeries_quotient_powers_independent {K : Type*} [Field K]
    (g : PowerSeries K) (N : ℕ) (hvan : PowerSeries.X ^ N ∣ g) :
    LinearIndependent K (fun i : Fin N =>
      (Ideal.Quotient.mkₐ K (Ideal.span {g})) (PowerSeries.X ^ i.val)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  let P := ∑ j : Fin N, a j • (PowerSeries.X : PowerSeries K) ^ j.val
  have hP : P ∈ Ideal.span {g} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change (Ideal.Quotient.mkₐ K (Ideal.span {g})) P = 0
    simpa only [P, map_sum, map_smul] using ha
  have hX : PowerSeries.X ^ N ∣ P := hvan.trans (Ideal.mem_span_singleton.mp hP)
  have hc := PowerSeries.X_pow_dvd_iff.mp hX i.val i.isLt
  simp only [P, map_sum, PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_X_pow] at hc
  have hsum : (∑ j : Fin N, a j * if i.val = j.val then (1 : K) else 0) = a i := by
    simp [Fin.val_inj]
  rwa [hsum] at hc

/-- If a proper degree-m section vanishes to order N on a formal plane
branch, then N<=d*m. The parameter map and its equation are maps. -/
private theorem formal_plane_vanishing_order_bound {K : Type*} [Field K]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (ψ : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K) (hψ : ψ f = 0)
    (j : Fin 2) (a : K) (hparam : ψ (X j - C a) = PowerSeries.X)
    (g : MvPolynomial (Fin 2) K) (hnd : ¬ f ∣ g) {N : ℕ}
    (hvan : PowerSeries.X ^ N ∣ ψ g) : N ≤ f.totalDegree * g.totalDegree := by
  let p : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {f}
  have : p.IsPrime := Ideal.isPrime_span_singleton_of_prime hf.prime
  let J : Ideal (PowerSeries K) := Ideal.span {ψ g}
  let q := (Ideal.Quotient.mkₐ K J).comp ψ
  let φ : (MvPolynomial (Fin 2) K ⧸ p) →ₐ[K] (PowerSeries K ⧸ J) :=
    Ideal.Quotient.liftₐ p q (by
      intro l hl
      obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton.mp hl
      simp only [q, AlgHom.comp_apply, map_mul, hψ, map_zero, zero_mul])
  have hφ (l : MvPolynomial (Fin 2) K) : φ ((Ideal.Quotient.mk p) l) = q l := rfl
  let h : Fin N → MvPolynomial (Fin 2) K := fun i => (X j - C a) ^ i.val
  have hi : LinearIndependent K (fun i => φ ((Ideal.Quotient.mk p) (h i))) := by
    have he : (fun i => φ ((Ideal.Quotient.mk p) (h i))) =
        (fun i : Fin N => (Ideal.Quotient.mkₐ K J) (PowerSeries.X ^ i.val)) := by
      funext i
      rw [hφ]
      simp only [q, AlgHom.comp_apply, h, map_pow, hparam]
    rw [he]
    exact powerSeries_quotient_powers_independent (ψ g) N hvan
  have hz : φ ((Ideal.Quotient.mk p) g) = 0 := by
    rw [hφ]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp)
  have hh := section_image_rank_le p f.totalDegree
    ⟨f.totalDegree, (f.totalDegree : ℤ) - f.totalDegree.choose 2,
      fun M hM => principal_plane_hilbert_function f hf.ne_zero hM⟩
    φ h hi g (by simpa only [p, Ideal.mem_span_singleton] using hnd) g.totalDegree le_rfl hz
  simpa only [Fintype.card_fin] using hh

/-- Jets longer than d*D detect every degree-at-most-D function on the curve. -/
private theorem formal_plane_jet_detects_divisibility {K : Type*} [Field K]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (ψ : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K) (hψ : ψ f = 0)
    (j : Fin 2) (a : K) (hparam : ψ (X j - C a) = PowerSeries.X)
    {D N : ℕ} (hN : f.totalDegree * D < N)
    (g : MvPolynomial (Fin 2) K) (hg : g.totalDegree ≤ D)
    (hzero : ∀ n < N, PowerSeries.coeff n (ψ g) = 0) : f ∣ g := by
  by_contra hnd
  have hh := formal_plane_vanishing_order_bound f hf ψ hψ j a hparam g hnd
    (PowerSeries.X_pow_dvd_iff.mpr hzero)
  exact (not_lt_of_ge (hh.trans (Nat.mul_le_mul_left _ hg))) hN

/-- Low-degree independent classes give independent local jets, with the
explicit length d*D+1 supplied by the preceding local intersection bound. -/
private theorem formal_plane_independent_jets {K ι : Type*} [Field K] [Fintype ι]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (ψ : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K) (hψ : ψ f = 0)
    (j : Fin 2) (a : K) (hparam : ψ (X j - C a) = PowerSeries.X)
    {D N : ℕ} (hN : f.totalDegree * D < N) (h : ι → MvPolynomial (Fin 2) K)
    (hd : ∀ i, (h i).totalDegree ≤ D)
    (hi : LinearIndependent K (fun i => (Ideal.Quotient.mkₐ K (Ideal.span {f})) (h i))) :
    ∀ c : ι → K, (∀ n < N, PowerSeries.coeff n (∑ i, c i • ψ (h i)) = 0) → ∀ i, c i = 0 := by
  classical
  intro c hc
  let g := ∑ i, c i • h i
  have hg : g.totalDegree ≤ D := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    exact (MvPolynomial.totalDegree_smul_le _ _).trans (hd i)
  have hdiv := formal_plane_jet_detects_divisibility f hf ψ hψ j a hparam hN g hg
    (by simpa only [g, map_sum, map_smul] using hc)
  have he : (Ideal.Quotient.mkₐ K (Ideal.span {f})) g = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv)
  have hz : ∑ i, c i • (Ideal.Quotient.mkₐ K (Ideal.span {f})) (h i) = 0 := by
    simpa only [g, map_sum, map_smul] using he
  exact Fintype.linearIndependent_iff.mp hi c hz

/-- Frobenius coefficients cannot cancel a low-degree basis on a
formal plane branch. The numerical condition is d*D<p^r. -/
theorem formal_plane_frobenius_relation_trivial {K ι : Type*} [Field K]
    [Fintype ι] (p r : ℕ) [Fact p.Prime] [CharP K p]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (ψ : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K) (hψ : ψ f = 0)
    (j : Fin 2) (a : K) (hparam : ψ (X j - C a) = PowerSeries.X)
    {D : ℕ} (hD : f.totalDegree * D < p ^ r) (h : ι → MvPolynomial (Fin 2) K)
    (hd : ∀ i, (h i).totalDegree ≤ D)
    (hi : LinearIndependent K (fun i => (Ideal.Quotient.mkₐ K (Ideal.span {f})) (h i)))
    (g : ι → PowerSeries K) (hrel : ∑ i, ψ (h i) * (g i) ^ (p ^ r) = 0) : ∀ i, g i = 0 := by
  classical
  exact powerSeries_frobenius_relation_trivial p r (fun i => ψ (h i))
    (formal_plane_independent_jets f hf ψ hψ j a hparam hD h hd hi) g hrel

end
end CCDN
