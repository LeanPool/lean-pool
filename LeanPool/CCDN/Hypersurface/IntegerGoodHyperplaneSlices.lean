/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hypersurface.GraphHyperplaneRestriction
import LeanPool.CCDN.Algebra.PrimitiveNormalization
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Hypersurface.AffineHyperplaneSlice
import LeanPool.CCDN.Surface.TopFormIrreducibility
import Mathlib.Algebra.BigOperators.Field

/-! Integer equations for every parallel level of a constructed good
hyperplane. Degrees and geometric irreducibility of the leading forms are
preserved, and deleting the solved coordinate does not enlarge the box. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
local notation "Qbar" => AlgebraicClosure ℚ

/-- A rational polynomial whose top-degree form is absolutely irreducible has an integer model of
the same total degree, also with absolutely irreducible top-degree form, that has the same
integer zeros. -/
theorem exists_integer_model_absolute_top {n : ℕ} (f : MvPolynomial (Fin n) ℚ)
    (hir : Irreducible (map (algebraMap ℚ Qbar) (homogeneousComponent f.totalDegree f))) :
    ∃ g : MvPolynomial (Fin n) ℤ,
      g.totalDegree = f.totalDegree ∧
      Irreducible (map (Int.castRingHom Qbar) (homogeneousComponent g.totalDegree g)) ∧
      ∀ x : Fin n → ℤ, eval x g = 0 ↔ eval (fun i => (x i : ℚ)) f = 0 := by
  have hf : f ≠ 0 := by
    intro hz
    exact hir.ne_zero (by simp [hz])
  obtain ⟨g, r, _, hr, he⟩ := exists_primitive_integer_model f hf
  have hdegree := rational_scalar_model_degree hr hf he
  let φ : ℚ →+* Qbar := algebraMap ℚ Qbar
  have hφ : φ.comp (Int.castRingHom ℚ) = Int.castRingHom Qbar := by
    ext z
    simp
  have hmodel : map (Int.castRingHom Qbar) g = C (φ r) * map φ f := by
    have hh := congrArg (map φ) he
    simpa only [map_mul, map_C, map_map, hφ] using hh
  have htop : map (Int.castRingHom Qbar) (homogeneousComponent g.totalDegree g) =
      C (φ r) * map φ (homogeneousComponent f.totalDegree f) := by
    rw [map_homogeneousComponent, hmodel, homogeneousComponent_C_mul,
      hdegree, ← map_homogeneousComponent]
  refine ⟨g, hdegree, ?_, ?_⟩
  · rw [htop]
    exact (irreducible_isUnit_mul
      ((isUnit_iff_ne_zero.mpr ((map_ne_zero_iff φ φ.injective).mpr hr)).map C)).mpr hir
  · intro x
    have hh := rational_scalar_model_zero_iff hr he (fun i => (x i : ℚ))
    constructor
    · intro hx
      apply hh.mp
      have hxQ := congrArg (Int.castRingHom ℚ) hx
      rw [map_eval, map_zero] at hxQ
      exact hxQ
    · intro hx
      apply Int.cast_injective (α := ℚ)
      change (Int.castRingHom ℚ) (eval x g) = (Int.castRingHom ℚ) 0
      rw [map_eval, map_zero]
      exact hh.mpr hx

/-- Integer models for all parallel slices of any chosen good rational
hyperplane; the normal may come from any quantitative construction. -/
theorem exists_integer_hyperplane_slice_models {n : ℕ}
    (f : MvPolynomial (Option (Fin n)) ℤ) (D : ℤ) (a : Fin n → ℤ)
    (hD : D ≠ 0)
    (hgood : Irreducible (map (algebraMap ℚ Qbar)
      (graphHyperplaneRestriction (fun i => (a i : ℚ) / D)
        (map (Int.castRingHom ℚ) (homogeneousComponent f.totalDegree f))))) :
    ∃ g : ℤ → MvPolynomial (Fin n) ℤ, ∀ k : ℤ,
      (g k).totalDegree = f.totalDegree ∧
      Irreducible (map (Int.castRingHom Qbar)
        (homogeneousComponent (g k).totalDegree (g k))) ∧
      ∀ x : Option (Fin n) → ℤ,
        D * x none - ∑ i, a i * x (some i) = k →
        eval x f = 0 → eval (fun i => x (some i)) (g k) = 0 := by
  classical
  let p := map (Int.castRingHom ℚ) f
  let α : Fin n → ℚ := fun i => (a i : ℚ) / D
  have hpdegree : p.totalDegree = f.totalDegree :=
    totalDegree_map_of_injective (RingHom.injective_int _) f
  have htopir : Irreducible (map (algebraMap ℚ Qbar)
      (graphHyperplaneRestriction α (homogeneousComponent p.totalDegree p))) := by
    rw [hpdegree, ← map_homogeneousComponent]
    exact hgood
  have htop : graphHyperplaneRestriction α (homogeneousComponent p.totalDegree p) ≠ 0 := by
    intro hz
    exact htopir.ne_zero (by rw [hz, map_zero])
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have hslices (k : ℤ) : ∃ g : MvPolynomial (Fin n) ℤ,
      g.totalDegree = f.totalDegree ∧
      Irreducible (map (Int.castRingHom Qbar) (homogeneousComponent g.totalDegree g)) ∧
      ∀ x : Option (Fin n) → ℤ,
        D * x none - ∑ i, a i * x (some i) = k →
        eval x f = 0 → eval (fun i => x (some i)) g = 0 := by
    let q := affineGraphHyperplaneSlice α ((k : ℚ) / D) p
    have hqdegree : q.totalDegree = p.totalDegree :=
      affineGraphHyperplaneSlice_degree α ((k : ℚ) / D) p htop
    have hqir : Irreducible (map (algebraMap ℚ Qbar)
        (homogeneousComponent q.totalDegree q)) := by
      rw [hqdegree, affineGraphHyperplaneSlice_top]
      exact htopir
    obtain ⟨g, hgdegree, hgir, hgzero⟩ := exists_integer_model_absolute_top q hqir
    refine ⟨g, hgdegree.trans (hqdegree.trans hpdegree), hgir, ?_⟩
    intro x hxlevel hxf
    apply (hgzero (fun i => x (some i))).2
    rw [affineGraphHyperplaneSlice_eval]
    have hlevel : (D : ℚ) * (x none : ℚ) -
        ∑ i, (a i : ℚ) * (x (some i) : ℚ) = k := by exact_mod_cast hxlevel
    have hin : (fun i => Option.elim i
        ((∑ j, α j * (x (some j) : ℚ)) + (k : ℚ) / D)
        (fun j => (x (some j) : ℚ))) = (fun i => (x i : ℚ)) := by
      funext i
      cases i with
      | none =>
        change (∑ j, (a j : ℚ) / D * (x (some j) : ℚ)) + (k : ℚ) / D = (x none : ℚ)
        have hsum : (∑ j, (a j : ℚ) / D * (x (some j) : ℚ)) =
            (∑ j, (a j : ℚ) * (x (some j) : ℚ)) / D := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro j _
          ring
        rw [hsum, ← add_div]
        apply (div_eq_iff hDq).2
        nlinarith only [hlevel]
      | some i => rfl
    rw [hin]
    have hh := congrArg (Int.castRingHom ℚ) hxf
    rw [map_eval, map_zero] at hh
    exact hh
  choose g hg using hslices
  exact ⟨g, hg⟩

end
end CCDN
