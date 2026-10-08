/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedNormalizedRootDoubledResponseSubadditivity

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.GeneralAdaptedCellDoubledResponseFilling

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Doubled-response filling of a general adapted cell

The maximal filling theorem applies to two arbitrary positive-definite grids.
This module exposes the corresponding doubled-response subadditivity theorem
without specializing the target to the base-rounded grid.  It is the filling
surface needed when a bounded residual dilation changes the target adapted
cell but leaves the exact normalized-root grid used by the response rows.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- A general adapted cell is exhausted by a maximal family of cells from a
second positive-definite grid.  The row masses retain the exact cross-grid
factor, and doubled response is subadditive over the resulting almost-
everywhere partition whenever the weighted response series is summable. -/
theorem exists_coeffSpaceDoubledResponse_adaptedCellTranslate_le_tsum_filling
    [NeZero d] {p q : Mat d} (hp : p.PosDef) (hq : q.PosDef)
    (n j : ℤ) (y : Vec d) (a : CoeffSpace d) (P Q : BlockVec d) :
    ∃ Z : ℤ → Finset (Fin d → ℤ),
      (∀ r, ↑(Z r) = Transport.fillingIndex q n (adaptedCellTranslate p j y) r) ∧
      (∀ r : ℤ, r < n →
        ∑ w ∈ Z r, (volume (adaptedCellAt q r w)).toReal /
            (volume (adaptedCellTranslate p j y)).toReal ≤
          6 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ * (3 : ℝ) ^ (r - j)) ∧
      (∀ r : ℤ,
        ∑ w ∈ Z r, (volume (adaptedCellAt q r w)).toReal /
            (volume (adaptedCellTranslate p j y)).toReal ≤ 1) ∧
      (Summable (fun i : Σ u : ℕ, {w // w ∈ Z (n - (u : ℤ))} ↦
        (volume (adaptedCellAt q (n - (i.1 : ℤ)) i.2.1)).toReal /
            (volume (adaptedCellTranslate p j y)).toReal *
          Transport.coeffSpaceDoubledResponse
            (adaptedCellAt q (n - (i.1 : ℤ)) i.2.1) a P Q) →
        Transport.coeffSpaceDoubledResponse (adaptedCellTranslate p j y) a P Q ≤
          ∑' i : Σ u : ℕ, {w // w ∈ Z (n - (u : ℤ))},
            (volume (adaptedCellAt q (n - (i.1 : ℤ)) i.2.1)).toReal /
              (volume (adaptedCellTranslate p j y)).toReal *
            Transport.coeffSpaceDoubledResponse
              (adaptedCellAt q (n - (i.1 : ℤ)) i.2.1) a P Q) := by
  classical
  obtain ⟨Z, hZ, hsub, hdom, _hvol, hdisj, _hrow, _hrowOne, hnull⟩ :=
    Transport.maximal_filling hp hq n j y
  refine ⟨Z, hZ, ?_, ?_, ?_⟩
  · intro r hrn
    exact Transport.sum_relative_volume_row_le hp hq hrn (hZ r)
  · intro r
    exact Transport.sum_relative_volume_row_le_one hp hq (hZ r)
  · intro hsum
    let I := Σ u : ℕ, {w // w ∈ Z (n - (u : ℤ))}
    let c : I → Set (Vec d) := fun i ↦
      adaptedCellAt q (n - (i.1 : ℤ)) i.2.1
    let : Countable I := inferInstance
    have hc : ∀ i : I, IsOpenBoundedConvexDomain (c i) := fun i ↦
      hdom _ _ i.2.2
    have hcsub : ∀ i : I, c i ⊆ adaptedCellTranslate p j y := fun i ↦
      hsub _ _ i.2.2
    have hcpair : Pairwise fun i k : I ↦ Disjoint (c i) (c k) := by
      intro i k hik
      apply hdisj _ _ _ i.2.2 _ k.2.2
      intro heq
      apply hik
      rcases i with ⟨u, w⟩
      rcases k with ⟨v, z⟩
      have huv : u = v := by
        have hs := congrArg Prod.fst heq
        dsimp at hs
        omega
      subst v
      have hwz : w = z := Subtype.ext (congrArg Prod.snd heq)
      subst z
      rfl
    have hc0 : ∀ i : I, volume (c i) ≠ 0 := fun i ↦
      (Recurrence.volume_adaptedCellAt_pos hq _ _).ne'
    have hcover : (⋃ i : I, c i) =
        ⋃ r ∈ Set.Iic n, ⋃ w ∈ (Z r : Set (Fin d → ℤ)),
          adaptedCellAt q r w := by
      ext x
      constructor
      · intro hx
        obtain ⟨⟨u, w⟩, hx⟩ := Set.mem_iUnion.mp hx
        refine Set.mem_iUnion.mpr ⟨n - (u : ℤ), Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
        · exact Set.mem_Iic.mpr (by omega)
        · exact Set.mem_iUnion.mpr ⟨w.1, Set.mem_iUnion.mpr ⟨w.2, hx⟩⟩
      · intro hx
        obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
        obtain ⟨hrn, hr⟩ := Set.mem_iUnion.mp hr
        obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hr
        obtain ⟨hwZ, hx⟩ := Set.mem_iUnion.mp hw
        have hscale : n - (((n - r).toNat : ℕ) : ℤ) = r := by
          rw [Int.toNat_of_nonneg (sub_nonneg.mpr (Set.mem_Iic.mp hrn))]
          omega
        have hwZ' : w ∈ Z (n - (((n - r).toNat : ℕ) : ℤ)) := by
          rw [hscale]
          exact hwZ
        let i : I := ⟨(n - r).toNat, ⟨w, hwZ'⟩⟩
        refine Set.mem_iUnion.mpr ⟨i, ?_⟩
        change x ∈ adaptedCellAt q (n - (((n - r).toNat : ℕ) : ℤ)) w
        rwa [hscale]
    have hcnull : volume
        (adaptedCellTranslate p j y \ ⋃ i : I, c i) = 0 := by
      rw [hcover]
      exact hnull
    have hparent0 : volume (adaptedCellTranslate p j y) ≠ 0 :=
      Transport.volume_adaptedCellTranslate_ne_zero hp j y
    change Summable (fun i : I ↦
      (volume (c i)).toReal / (volume (adaptedCellTranslate p j y)).toReal *
        Transport.coeffSpaceDoubledResponse (c i) a P Q) at hsum
    change Transport.coeffSpaceDoubledResponse (adaptedCellTranslate p j y) a P Q ≤
      ∑' i : I, (volume (c i)).toReal /
        (volume (adaptedCellTranslate p j y)).toReal *
          Transport.coeffSpaceDoubledResponse (c i) a P Q
    exact Transport.coeffSpaceDoubledResponse_le_tsum_weight_of_countable_aePartition
      (Transport.isOpenBoundedConvexDomain_adaptedCellTranslate hp j y) hparent0 a hc hcsub
        hcpair hcnull hc0 P Q hsum

end

end RowSupply
end HighContrast
end HCPolySupport
