/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hypersurface.UniversalHyperplaneRestriction
public import LeanPool.CCDN.Noether.UniversalHomogeneousForm
import LeanPool.CCDN.Hypersurface.CoefficientwiseSubstitution
import LeanPool.CCDN.Hypersurface.GoodHyperplaneReindex
import LeanPool.CCDN.Noether.UniversalNoetherForms

/-! Effective hyperplane avoidance from the universal Noether forms.
The polynomial is nonzero by a constructed geometrically good section.
It is homogeneous of degree d(d²−1)+1 and vanishes on every bad graph
section, as well as on the omitted chart. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
universe u

private lemma hyperplaneNoether_specialize {K σ : Type*}
    [CommRing K] [Fintype σ] [DecidableEq σ]
    (d : ℕ) (f : MvPolynomial (Option σ) ℤ) (A : Option σ → K)
    (Φ : MvPolynomial (Sym σ d) ℤ) :
    eval₂Hom (Int.castRingHom K) A
        (homogeneousCoefficientSpecialization d (universalHyperplaneRestriction f) Φ) =
      homogeneousCoefficientSpecialization d
        (scaledHyperplaneRestriction A (map (Int.castRingHom K) f)) Φ := by
  rw [homogeneousCoefficientSpecialization_map, universalHyperplaneRestriction_specialize]

private lemma scaledHyperplaneRestriction_not_absolutely_irreducible {K σ : Type*}
    [Field K] [Fintype σ] (A : Option σ → K) (hA : A none ≠ 0)
    {d : ℕ} {f : MvPolynomial (Option σ) K} (hf : f.IsHomogeneous d)
    (hbad : ¬Irreducible (map (algebraMap K (AlgebraicClosure K))
      (graphHyperplaneRestriction (fun i => -A (some i) / A none) f))) :
    ¬Irreducible (map (algebraMap K (AlgebraicClosure K))
      (scaledHyperplaneRestriction A f)) := by
  rw [scaledHyperplaneRestriction_eq_graph A hA hf, map_mul, map_C]
  have hu : IsUnit (C ((algebraMap K (AlgebraicClosure K)) (A none ^ d)) :
      MvPolynomial σ (AlgebraicClosure K)) :=
    (isUnit_iff_ne_zero.mpr
      (by simpa only [map_zero] using
        (algebraMap K (AlgebraicClosure K)).injective.ne (pow_ne_zero d hA))).map C
  exact fun hi => hbad ((irreducible_isUnit_mul hu).mp hi)

/-- A corrected form of CCDN Lemma 4.3.7 for degree `d ≥ 2`, in explicit hyperplane coordinates:
for an absolutely irreducible integer form `f` of degree `d`, there is a nonzero integer form `G`
in the hyperplane coefficients, homogeneous of degree `d * (d ^ 2 - 1) + 1` and of total degree at
most `(4 + n) * d * (d ^ 2 - 1)`, that vanishes at every coefficient vector `A` over any field,
either with `A₀ = 0` or for which the restriction of `f` to the hyperplane `A` is not absolutely
irreducible. -/
theorem exists_effective_hyperplane_avoidance {n : ℕ}
    (f : MvPolynomial (Option (Option (Fin (2 + n)))) ℤ)
    (d : ℕ) (hd : 2 ≤ d) (hf : f.IsHomogeneous d)
    (hir : AbsolutelyIrreducible f) :
    ∃ G : MvPolynomial (Option (Option (Fin (2 + n)))) ℤ,
      G ≠ 0 ∧ G.IsHomogeneous (d * (d ^ 2 - 1) + 1) ∧
      G.totalDegree ≤ (4 + n) * d * (d ^ 2 - 1) ∧
      ∀ (K : Type u) [Field K] (A : Option (Option (Fin (2 + n))) → K),
        (A none ≠ 0 →
          ¬Irreducible (map (algebraMap K (AlgebraicClosure K))
            (graphHyperplaneRestriction (fun i => -A (some i) / A none)
              (map (Int.castRingHom K) f)))) →
        eval₂ (Int.castRingHom K) A G = 0 := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have hf0 : f ≠ 0 := by
    intro hz
    exact hir.ne_zero (by rw [hz, map_zero])
  have hdegree : f.totalDegree = k + 2 := hf.totalDegree hf0
  obtain ⟨a,ha⟩ := exists_geometrically_good_graph_reindexed f hir (by omega)
  let q := graphHyperplaneRestriction a (map (Int.castRingHom ℚ) f)
  have hq : q.IsHomogeneous (k + 2) :=
    graphHyperplaneRestriction_homogeneous a (hf.map (Int.castRingHom ℚ))
  obtain ⟨Φ,hΦ,hn⟩ := universalNoetherForms_nonvanishing k q hq ha
  let H := homogeneousCoefficientSpecialization (k + 2) (universalHyperplaneRestriction f) Φ
  let A : Option (Option (Fin (2 + n))) → ℚ :=
    fun i => Option.elim i 1 (fun j => -a j)
  have hvalue : eval₂Hom (Int.castRingHom ℚ) A H =
      homogeneousCoefficientSpecialization (k + 2) q Φ := by
    dsimp only [H, A]
    rw [hyperplaneNoether_specialize, scaledHyperplaneRestriction_normalized]
  have hH : H ≠ 0 := by
    intro hz
    apply hn
    rw [← hvalue, hz, map_zero]
  have hHhom : H.IsHomogeneous ((k + 2) * ((k + 2) ^ 2 - 1)) :=
    homogeneousCoefficientSpecialization_homogeneous _ _ _ _
      (universalHyperplaneRestriction_coefficientwiseHomogeneous hf) Φ
      (universalNoetherForms_homogeneous k Φ hΦ)
  let G := X none * H
  have hG : G ≠ 0 := mul_ne_zero (X_ne_zero none) hH
  have hGhom : G.IsHomogeneous ((k + 2) * ((k + 2) ^ 2 - 1) + 1) := by
    simpa only [add_comm 1] using (isHomogeneous_X ℤ none).mul hHhom
  refine ⟨G,hG,hGhom,?_,?_⟩
  · rw [hGhom.totalDegree hG]
    have hr : 0 < (k + 2) ^ 2 - 1 := by
      have hh : 4 ≤ (k + 2) ^ 2 := by nlinarith
      omega
    have hp : 1 ≤ (k + 2) * ((k + 2) ^ 2 - 1) := Nat.succ_le_of_lt (Nat.mul_pos (by omega) hr)
    nlinarith
  · intro K _ A hbad
    change (eval₂Hom (Int.castRingHom K) A) (X none * H) = 0
    rw [map_mul]
    have hx : eval₂Hom (Int.castRingHom K) A (X none) = A none := eval₂_X _ _ _
    rw [hx]
    by_cases hA : A none = 0
    · rw [hA, zero_mul]
    · have hh := scaledHyperplaneRestriction_not_absolutely_irreducible A hA
        (hf.map (Int.castRingHom K)) (hbad hA)
      have hz := universalNoetherForms_vanish k
        (scaledHyperplaneRestriction A (map (Int.castRingHom K) f))
        (scaledHyperplaneRestriction_homogeneous A (hf.map (Int.castRingHom K))) hh Φ hΦ
      change A none * eval₂Hom (Int.castRingHom K) A
        (homogeneousCoefficientSpecialization (k + 2) (universalHyperplaneRestriction f) Φ) = 0
      rw [hyperplaneNoether_specialize, hz, mul_zero]

end
end CCDN
