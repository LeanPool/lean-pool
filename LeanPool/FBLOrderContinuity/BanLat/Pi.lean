/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

public import LeanPool.OrderClosures.BanLat.Pi
public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Products of vector, normed and Banach lattices

Given a family `(X i)` of vector lattices, the product `∀ i, X i` carries a
pointwise vector lattice structure. When each `X i` is a normed (resp. Banach)
lattice and the index set is finite, the ℓ^p product `PiLp p X` is again a
normed (resp. Banach) lattice for `1 ≤ p ≤ ∞`. Moreover, the ℓ^∞ product of
AM-spaces is an AM-space, and the ℓ^1 product of AL-spaces is an AL-space.
-/

@[expose] public section

open scoped ENNReal

/-! ### ℓ^p product

For a finite index set `ι` and `1 ≤ p ≤ ∞`, the ℓ^p product of normed vector
lattices is again a normed vector lattice, and Banachness is preserved. The
order structure is pointwise; only the norm depends on `p`.
-/

namespace PiLp

variable {ι : Type*} [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)] {X : ι → Type*}

section Order

variable [∀ i, NormedAddCommGroup (X i)] [∀ i, Lattice (X i)]
  [∀ i, IsOrderedAddMonoid (X i)]

/-- Pointwise `≤` on `PiLp p X`. -/
instance instLE : LE (PiLp p X) where
  le x y := ∀ i, x i ≤ y i

/-- Pointwise `<` on `PiLp p X`. -/
instance instLT : LT (PiLp p X) where
  lt x y := WithLp.ofLp x < WithLp.ofLp y

/-- Pointwise `⊔` on `PiLp p X`. -/
instance instMax : Max (PiLp p X) where
  max x y := WithLp.toLp p (fun i => x i ⊔ y i)

/-- Pointwise `⊓` on `PiLp p X`. -/
instance instMin : Min (PiLp p X) where
  min x y := WithLp.toLp p (fun i => x i ⊓ y i)

/-- Pointwise lattice structure on `PiLp p X`. -/
instance instLattice : Lattice (PiLp p X) :=
  Function.Injective.lattice (β := ∀ i, X i) WithLp.ofLp (WithLp.ofLp_injective p)
    Iff.rfl Iff.rfl (fun _ _ => rfl) (fun _ _ => rfl)

/-- The order on `PiLp p X` is compatible with addition. -/
instance instIsOrderedAddMonoid : IsOrderedAddMonoid (PiLp p X) :=
  Function.Injective.isOrderedAddMonoid (β := PiLp p X) (α := ∀ i, X i)
    WithLp.ofLp (fun _ _ => rfl) Iff.rfl

/-- The ℓ^p norm is solid: `|x| ≤ |y|` implies `‖x‖ ≤ ‖y‖`. -/
instance instHasSolidNorm [∀ i, HasSolidNorm (X i)] : HasSolidNorm (PiLp p X) where
  solid := fun x y h => by
    -- pointwise bound on norms via the solid norm of each factor
    have hpt : ∀ i, ‖x i‖ ≤ ‖y i‖ := fun i =>
      HasSolidNorm.solid (α := X i) (h i)
    rcases eq_or_ne p ∞ with hp | hp
    · subst hp
      simp only [PiLp.norm_eq_ciSup]
      exact ciSup_mono (Set.Finite.bddAbove (Set.finite_range _)) hpt
    · have h1 : (1 : ℝ≥0∞) ≤ p := Fact.out
      have hpos : 0 < p.toReal := by
        have := ENNReal.toReal_lt_toReal (by norm_num) hp |>.mpr
          (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) h1)
        simpa using this
      simp only [PiLp.norm_eq_sum hpos]
      gcongr with i
      exact hpt i

end Order

/-! #### Vector and Banach lattice structure -/

variable [∀ i, NormedAddCommGroup (X i)] [∀ i, Lattice (X i)]
  [∀ i, IsOrderedAddMonoid (X i)]

instance instPosSMulMono [∀ i, NormedVectorLattice (X i)] :
    PosSMulMono ℝ (PiLp p X) where
  smul_le_smul_of_nonneg_left := by
    intro a ha b₁ b₂ hb i
    exact smul_le_smul_of_nonneg_left (hb i) ha

/-- The ℓ^p product of normed vector lattices is a vector lattice. -/
instance instVectorLattice [∀ i, NormedVectorLattice (X i)] :
    VectorLattice (PiLp p X) := ⟨⟩

/-- The ℓ^p product of normed vector lattices is a normed vector lattice. -/
instance instNormedVectorLattice [∀ i, NormedVectorLattice (X i)] :
    NormedVectorLattice (PiLp p X) where

/-- The ℓ^p product of Banach lattices is a Banach lattice. -/
instance instBanachLattice [∀ i, BanachLattice (X i)] :
    BanachLattice (PiLp p X) where

end PiLp
