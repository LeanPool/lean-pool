/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.GeneralAdaptedCellDoubledResponseFilling
public import LeanPool.HighContrastHomogenization.Provider.Entry.AdapterQuadratic

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.GeneralAdaptedCellDoubledResponseAggregation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Row-majorant aggregation on a general adapted-cell filling

The response bound produced by the general filling is aggregated here against
one nonnegative majorant per exact-grid row.  This is the form consumed by a
power-tail response certificate after translation, dilation, and gauge have
identified its exact-grid cell responses.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- A summable rowwise majorant on the filling grid controls doubled response
on an arbitrary adapted target.  The top row pays one and lower rows pay the
exact cross-grid boundary factor. -/
theorem exists_coeffSpaceDoubledResponse_adaptedCellTranslate_le_tsum_rowMajorant
    [NeZero d] {p q : Mat d} (hp : p.PosDef) (hq : q.PosDef)
    (n j : ℤ) (y : Vec d) (a : CoeffSpace d) (P Q : BlockVec d) :
    ∃ Z : ℤ → Finset (Fin d → ℤ),
      (∀ r, ↑(Z r) = Transport.fillingIndex q n (adaptedCellTranslate p j y) r) ∧
      (∀ B : ℤ → ℝ,
        (∀ r, 0 ≤ B r) →
        (∀ (u : ℕ) (w : Fin d → ℤ), w ∈ Z (n - (u : ℤ)) →
          Book.Ch02.doubledResponseJ
              (Response.adaptedDomainAt hq (n - (u : ℤ)) w)
              (a.coeffOn (Response.adaptedDomainAt hq (n - (u : ℤ)) w)) P Q ≤
            B (n - (u : ℤ))) →
        Summable (fun u : ℕ ↦
          (if u = 0 then 1 else
            6 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ *
              (3 : ℝ) ^ ((n - (u : ℤ)) - j)) * B (n - (u : ℤ))) →
        Transport.coeffSpaceDoubledResponse (adaptedCellTranslate p j y) a P Q ≤
          ∑' u : ℕ,
            (if u = 0 then 1 else
              6 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ *
                (3 : ℝ) ^ ((n - (u : ℤ)) - j)) * B (n - (u : ℤ))) := by
  classical
  obtain ⟨Z, hZ, hrow, hrowOne, hresponse⟩ :=
    exists_coeffSpaceDoubledResponse_adaptedCellTranslate_le_tsum_filling
      hp hq n j y a P Q
  refine ⟨Z, hZ, ?_⟩
  intro B hB0 hcell hmajor
  let I := Σ u : ℕ, {w // w ∈ Z (n - (u : ℤ))}
  let term : I → ℝ := fun i ↦
    (volume (adaptedCellAt q (n - (i.1 : ℤ)) i.2.1)).toReal /
        (volume (adaptedCellTranslate p j y)).toReal *
      Transport.coeffSpaceDoubledResponse
        (adaptedCellAt q (n - (i.1 : ℤ)) i.2.1) a P Q
  let rowBound : ℕ → ℝ := fun u ↦
    if u = 0 then 1 else
      6 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ *
        (3 : ℝ) ^ ((n - (u : ℤ)) - j)
  change Summable (fun u : ℕ ↦ rowBound u * B (n - (u : ℤ))) at hmajor
  change Transport.coeffSpaceDoubledResponse (adaptedCellTranslate p j y) a P Q ≤
    ∑' u : ℕ, rowBound u * B (n - (u : ℤ))
  have hrowWeight : ∀ u : ℕ,
      ∑ w ∈ Z (n - (u : ℤ)),
          (volume (adaptedCellAt q (n - (u : ℤ)) w)).toReal /
            (volume (adaptedCellTranslate p j y)).toReal ≤ rowBound u := by
    intro u
    by_cases hu : u = 0
    · subst u
      simp only [rowBound, ite_eq_left, Nat.cast_zero, sub_zero]
      exact hrowOne n
    · have hun : n - (u : ℤ) < n := by
        have huPos : 0 < u := Nat.pos_of_ne_zero hu
        omega
      dsimp only [rowBound]
      rw [ite_eq_right hu]
      exact hrow (n - (u : ℤ)) hun
  have hcellCoeff : ∀ (u : ℕ) (w : Fin d → ℤ),
      w ∈ Z (n - (u : ℤ)) →
      Transport.coeffSpaceDoubledResponse
          (adaptedCellAt q (n - (u : ℤ)) w) a P Q ≤
        B (n - (u : ℤ)) := by
    intro u w hw
    calc
      Transport.coeffSpaceDoubledResponse
          (adaptedCellAt q (n - (u : ℤ)) w) a P Q =
          Book.Ch02.doubledResponseJ
            (Response.adaptedDomainAt hq (n - (u : ℤ)) w)
            (a.coeffOn (Response.adaptedDomainAt hq (n - (u : ℤ)) w)) P Q := by
              simpa only [Response.adaptedDomainAt_carrier] using
                Transport.coeffSpaceDoubledResponse_eq_doubledResponseJ
                  (Response.adaptedDomainAt hq (n - (u : ℤ)) w) a P Q
      _ ≤ B (n - (u : ℤ)) := hcell u w hw
  have hterm0 : ∀ i : I, 0 ≤ term i := by
    intro i
    have hresponse0 : 0 ≤ Transport.coeffSpaceDoubledResponse
        (adaptedCellAt q (n - (i.1 : ℤ)) i.2.1) a P Q := by
      have heq : Transport.coeffSpaceDoubledResponse
          (adaptedCellAt q (n - (i.1 : ℤ)) i.2.1) a P Q =
          Book.Ch02.doubledResponseJ
            (Response.adaptedDomainAt hq (n - (i.1 : ℤ)) i.2.1)
            (a.coeffOn (Response.adaptedDomainAt hq (n - (i.1 : ℤ)) i.2.1)) P Q := by
        simpa only [Response.adaptedDomainAt_carrier] using
          Transport.coeffSpaceDoubledResponse_eq_doubledResponseJ
            (Response.adaptedDomainAt hq (n - (i.1 : ℤ)) i.2.1) a P Q
      rw [heq]
      exact Book.Ch02.doubledResponseJ_nonneg
        (Response.adaptedDomainAt hq (n - (i.1 : ℤ)) i.2.1)
        (a.coeffOn (Response.adaptedDomainAt hq (n - (i.1 : ℤ)) i.2.1)) P Q
    exact mul_nonneg
      (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) hresponse0
  have hrowTerm : ∀ u : ℕ,
      (∑' w : {w // w ∈ Z (n - (u : ℤ))}, term ⟨u, w⟩) ≤
        rowBound u * B (n - (u : ℤ)) := by
    intro u
    rw [tsum_fintype]
    let rowTerm : (Fin d → ℤ) → ℝ := fun w ↦
      (volume (adaptedCellAt q (n - (u : ℤ)) w)).toReal /
          (volume (adaptedCellTranslate p j y)).toReal *
        Transport.coeffSpaceDoubledResponse
          (adaptedCellAt q (n - (u : ℤ)) w) a P Q
    change (∑ w : {w // w ∈ Z (n - (u : ℤ))}, rowTerm w.1) ≤ _
    rw [← Finset.sum_subtype (Z (n - (u : ℤ))) (fun _ ↦ Iff.rfl) rowTerm]
    exact Entry.sum_weight_mul_le (hB0 (n - (u : ℤ)))
      (fun w hw ↦ hcellCoeff u w hw) (hrowWeight u)
  have hrow0 : ∀ u : ℕ,
      0 ≤ ∑' w : {w // w ∈ Z (n - (u : ℤ))}, term ⟨u, w⟩ :=
    fun u ↦ tsum_nonneg fun w ↦ hterm0 ⟨u, w⟩
  have hrowSummable : Summable fun u : ℕ ↦
      ∑' w : {w // w ∈ Z (n - (u : ℤ))}, term ⟨u, w⟩ :=
    Summable.of_nonneg_of_le hrow0 hrowTerm hmajor
  have htermSummable : Summable term :=
    (summable_sigma_of_nonneg hterm0).2
      ⟨fun _ ↦ (hasSum_fintype _).summable, hrowSummable⟩
  calc
    Transport.coeffSpaceDoubledResponse (adaptedCellTranslate p j y) a P Q ≤
        ∑' i : I, term i := hresponse (by
          change Summable term
          exact htermSummable)
    _ = ∑' u : ℕ, ∑' w : {w // w ∈ Z (n - (u : ℤ))}, term ⟨u, w⟩ :=
      htermSummable.tsum_sigma' (fun _ ↦ (hasSum_fintype _).summable)
    _ ≤ ∑' u : ℕ, rowBound u * B (n - (u : ℤ)) :=
      hrowSummable.tsum_le_tsum hrowTerm hmajor

end

end RowSupply
end HighContrast
end HCPolySupport
