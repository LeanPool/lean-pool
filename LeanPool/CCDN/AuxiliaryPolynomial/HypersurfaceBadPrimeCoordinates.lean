/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Analysis.PrimeCutoff
public import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimes
public import LeanPool.CCDN.Plane.IntegerPlaneLogHeight
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeHeight

/-! Coordinate invariance of geometric bad reduction and coefficient height,
with the exact bad-prime charge in standard Fin-indexed coordinates. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Geometric bad reduction at `p` is invariant under a bijective renaming of the
variables. -/
lemma hypersurfaceBadReduction_renameEquiv {σ τ : Type*} (e : σ ≃ τ)
    (f : MvPolynomial σ ℤ) (p : ℕ) :
    HypersurfaceBadReduction (rename e f) p ↔ HypersurfaceBadReduction f p := by
  unfold HypersurfaceBadReduction
  apply exists_congr
  intro hp
  let : Fact p.Prime := ⟨hp⟩
  dsimp only
  have hd : (rename e f).totalDegree = f.totalDegree := totalDegree_renameEquiv e f
  have hd' : (rename e (map (Int.castRingHom (AlgebraicClosure (ZMod p))) f)).totalDegree =
      (map (Int.castRingHom (AlgebraicClosure (ZMod p))) f).totalDegree :=
    totalDegree_renameEquiv e _
  rw [map_rename, hd, hd']
  apply or_congr Iff.rfl
  exact not_congr (MulEquiv.irreducible_iff (f := renameEquiv (AlgebraicClosure (ZMod p)) e))

/-- A bound `H` on the coefficients of `f` also bounds the coefficients of `f` after a
bijective renaming of the variables. -/
lemma polynomial_coefficient_bound_renameEquiv {σ τ : Type*} (e : σ ≃ τ)
    (f : MvPolynomial σ ℤ) (H : ℝ) (hf : CoefficientHeightLE f H) :
    CoefficientHeightLE (rename e f) H := by
  intro m
  have he : rename e.symm (rename e f) = f := by simp [rename_rename]
  have hc := coeff_rename_mapDomain e.symm e.symm.injective (rename e f) m
  rw [he] at hc
  rw [← hc]
  exact hf _

/-- The exact geometric bad-prime set exists, and its charge is bounded. -/
theorem exists_fin_hypersurface_bad_prime_charge
    {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : Irreducible (map (Int.castRingHom L) f))
    (hpos : 0 < f.totalDegree) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : CoefficientHeightLE f H) :
    ∃ bad : Finset ℕ,
      (∀ p, p ∈ bad ↔ stepanovThreshold f.totalDegree < p ∧ HypersurfaceBadReduction f p) ∧
      (∑ p ∈ bad, Real.log p / p) ≤
        Real.log (hypersurfaceHeightConstant (n + 1) *
          (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) + 2 * mertensError + 1 := by
  classical
  let e : Fin (n + 1) ≃ Option (Fin n) := finSuccEquiv' 0
  let g := rename e f
  have hg : Irreducible (map (Int.castRingHom L) g) := by
    rw [show g = rename e f from rfl, map_rename]
    exact (MulEquiv.irreducible_iff (f := renameEquiv L e)).mpr hf
  have hd : g.totalDegree = f.totalDegree := totalDegree_renameEquiv e f
  have hgc : CoefficientHeightLE g H := polynomial_coefficient_bound_renameEquiv e f H hcoeff
  let bad := (finite_hypersurface_bad_primes g hg (hd ▸ hpos)).toFinset
  have hmem (p : ℕ) : p ∈ bad ↔ stepanovThreshold f.totalDegree < p ∧
      HypersurfaceBadReduction f p := by
    simp only [bad, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hd, g,
      hypersurfaceBadReduction_renameEquiv]
  refine ⟨bad, hmem, ?_⟩
  have hc := hypersurface_bad_prime_charge g hg (hd ▸ hpos) H hH hgc bad
    (fun p hp => ((hypersurfaceBadReduction_renameEquiv e f p).mpr ((hmem p).mp hp).2))
    (fun p hp => hd ▸ ((hmem p).mp hp).1)
  simpa only [hd, Fintype.card_option, Fintype.card_fin] using hc

/-- Finiteness is invariant under the standard Fin-to-Option reindexing. -/
theorem finite_fin_hypersurface_bad_primes
    {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : Irreducible (map (Int.castRingHom L) f)) (hpos : 0 < f.totalDegree) :
    {p : ℕ | stepanovThreshold f.totalDegree < p ∧ HypersurfaceBadReduction f p}.Finite := by
  let e : Fin (n + 1) ≃ Option (Fin n) := finSuccEquiv' 0
  let g := rename e f
  have hg : Irreducible (map (Int.castRingHom L) g) := by
    rw [show g = rename e f from rfl, map_rename]
    exact (MulEquiv.irreducible_iff (f := renameEquiv L e)).mpr hf
  have hd : g.totalDegree = f.totalDegree := totalDegree_renameEquiv e f
  have hh := finite_hypersurface_bad_primes g hg (hd ▸ hpos)
  simpa only [hd, g, hypersurfaceBadReduction_renameEquiv] using hh

/-- For a nonzero homogeneous equation, degree loss is already included in
failure of geometric irreducibility, so the predicate agrees with the paper. -/
lemma homogeneous_hypersurfaceBadReduction_iff {σ : Type*} {d : ℕ}
    (f : MvPolynomial σ ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0)
    (p : ℕ) [Fact p.Prime] :
    HypersurfaceBadReduction f p ↔
      ¬Irreducible (map (Int.castRingHom (AlgebraicClosure (ZMod p))) f) := by
  constructor
  · rintro ⟨_, hbad⟩ hi
    rcases hbad with hdegree | hnot
    · apply hdegree
      rw [hf.totalDegree hf0]
      exact (hf.map _).totalDegree hi.ne_zero
    · exact hnot hi
  · intro hbad
    exact ⟨Fact.out, Or.inr hbad⟩

/-- Outside the bad-prime predicate, both full degree and geometric
irreducibility hold for the coefficient reduction. -/
lemma hypersurface_good_reduction {σ : Type*} (f : MvPolynomial σ ℤ)
    (p : ℕ) [Fact p.Prime] (hgood : ¬HypersurfaceBadReduction f p) :
    HasGoodReduction f p := by
  have hg : Irreducible (map (Int.castRingHom (AlgebraicClosure (ZMod p))) f) := by
    by_contra hn
    exact hgood ⟨Fact.out, Or.inr hn⟩
  have he : (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).comp (Int.castRingHom (ZMod p)) =
      Int.castRingHom (AlgebraicClosure (ZMod p)) := by ext; simp
  have hi : Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
      (map (Int.castRingHom (ZMod p)) f)) := by
    simpa only [map_map, he] using hg
  refine ⟨?_, hi⟩
  intro hz
  exact hi.ne_zero (by rw [hz, map_zero])

/-- The finite set of primes `p > 27 d ^ 4` of bad reduction of an absolutely
irreducible form of degree `d > 0`. -/
theorem exists_hypersurface_bad_prime_finset
    {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom L) f)) :
    ∃ bad : Finset ℕ, ∀ p, p ∈ bad ↔ stepanovThreshold d < p ∧ HypersurfaceBadReduction f p := by
  have hdeg : f.totalDegree = d := hf.totalDegree (ne_zero_of_irreducible_map hir)
  refine ⟨(finite_fin_hypersurface_bad_primes f hir (hdeg ▸ hd)).toFinset, fun p => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hdeg]

/-- A prime above the cutoff outside the bad-prime set has good reduction. -/
lemma hasGoodReduction_of_not_mem {σ : Type*} {f : MvPolynomial σ ℤ} {d : ℕ}
    {bad : Finset ℕ} (hbad : ∀ p, p ∈ bad ↔ stepanovThreshold d < p ∧ HypersurfaceBadReduction f p)
    (p : ℕ) [Fact p.Prime] (hp : p ∉ bad) (hcut : stepanovThreshold (d : ℝ) < p) :
    HasGoodReduction f p :=
  hypersurface_good_reduction f p fun hb => hp ((hbad p).mpr ⟨by exact_mod_cast hcut, hb⟩)

end
end CCDN
