/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedGenerationData

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderRoundedGenerationGeometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Normalized-root fillings for a selected rounded grid

All geometric estimates below are uniform over rounding generations above the
admissibility threshold.  The exact normalized-root cells fill a target cell
of the selected grid with the same row constants as in the canonical case.
-/

namespace HCPolySupport
namespace HighContrast
open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem roundedGrid_inv_mul_normalizedRoot_le [NeZero d]
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l) {m : Mat d} (hm : m.PosDef) :
    ‖(roundedGrid l m)⁻¹ * Selection.normalizedRoot m‖ ≤
      (101 / 100 : ℝ) * witnessEccentricity m := by
  calc
    ‖(roundedGrid l m)⁻¹ * Selection.normalizedRoot m‖ ≤
        ‖(roundedGrid l m)⁻¹‖ * ‖Selection.normalizedRoot m‖ := norm_mul_le _ _
    _ ≤ (101 / 100 : ℝ) * ‖Selection.normalizedRoot m‖ :=
      mul_le_mul_of_nonneg_right (Selection.norm_inv_roundedGrid_le hl hm)
        (norm_nonneg _)
    _ = (101 / 100 : ℝ) * witnessEccentricity m := by
      rw [Selection.norm_normalizedRoot_eq_witnessEccentricity hm]

private theorem exists_normalizedRoot_filling_roundedGrid [NeZero d]
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l) {m : Mat d} (hm : m.PosDef)
    (n j : ℤ) (y : Vec d) :
    ∃ Z : ℤ → Finset (Fin d → ℤ),
      (∀ a, ↑(Z a) = Transport.fillingIndex (Selection.normalizedRoot m) n
        (adaptedCellTranslate (roundedGrid l m) j y) a) ∧
      (∀ a, ∀ w ∈ Z a, adaptedCellAt (Selection.normalizedRoot m) a w ⊆
        adaptedCellTranslate (roundedGrid l m) j y) ∧
      (∀ a, ∀ w ∈ Z a,
        IsOpenBoundedConvexDomain (adaptedCellAt (Selection.normalizedRoot m) a w)) ∧
      (∀ a b : ℤ, ∀ w ∈ Z a, ∀ v ∈ Z b, (a, w) ≠ (b, v) →
        Disjoint (adaptedCellAt (Selection.normalizedRoot m) a w)
          (adaptedCellAt (Selection.normalizedRoot m) b v)) ∧
      (∀ a : ℤ, a < n →
        ∑ w ∈ Z a, (volume (adaptedCellAt (Selection.normalizedRoot m) a w)).toReal /
            (volume (adaptedCellTranslate (roundedGrid l m) j y)).toReal ≤
          6 * (d : ℝ) * Real.sqrt d *
            ((101 / 100 : ℝ) * witnessEccentricity m) *
              (3 : ℝ) ^ (a - j)) ∧
      (∀ a : ℤ,
        ∑ w ∈ Z a, (volume (adaptedCellAt (Selection.normalizedRoot m) a w)).toReal /
            (volume (adaptedCellTranslate (roundedGrid l m) j y)).toReal ≤ 1) ∧
      volume (adaptedCellTranslate (roundedGrid l m) j y \
        ⋃ a ∈ Set.Iic n, ⋃ w ∈ (Z a : Set (Fin d → ℤ)),
          adaptedCellAt (Selection.normalizedRoot m) a w) = 0 := by
  let hp := Recurrence.posDef_roundedGrid hl hm
  let hq := normalizedRoot_posDef_of_posDef hm
  obtain ⟨Z, hZ, hsub, hdom, _hvol, hdisj, _hrow, _hrowOne, hnull⟩ :=
    Transport.maximal_filling hp hq n j y
  refine ⟨Z, hZ, hsub, hdom, hdisj, ?_, ?_, hnull⟩
  · intro a han
    refine (Transport.sum_relative_volume_row_le hp hq han (hZ a)).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (roundedGrid_inv_mul_normalizedRoot_le hl hm) (by positivity))
      (by positivity)
  · intro a
    exact Transport.sum_relative_volume_row_le_one hp hq (hZ a)

private theorem exists_coeffSpaceDoubledResponse_roundedGrid_le_filling
    [NeZero d] {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {m : Mat d} (hm : m.PosDef) (n j : ℤ) (y : Vec d)
    (a : CoeffSpace d) (P Q : BlockVec d) :
    ∃ Z : ℤ → Finset (Fin d → ℤ),
      (∀ r, ↑(Z r) = Transport.fillingIndex (Selection.normalizedRoot m) n
        (adaptedCellTranslate (roundedGrid l m) j y) r) ∧
      (∀ r : ℤ, r < n →
        ∑ w ∈ Z r, (volume (adaptedCellAt (Selection.normalizedRoot m) r w)).toReal /
            (volume (adaptedCellTranslate (roundedGrid l m) j y)).toReal ≤
          6 * (d : ℝ) * Real.sqrt d *
            ((101 / 100 : ℝ) * witnessEccentricity m) *
              (3 : ℝ) ^ (r - j)) ∧
      (∀ r : ℤ,
        ∑ w ∈ Z r, (volume (adaptedCellAt (Selection.normalizedRoot m) r w)).toReal /
            (volume (adaptedCellTranslate (roundedGrid l m) j y)).toReal ≤ 1) ∧
      (Summable (fun i : Σ u : ℕ, {w // w ∈ Z (n - (u : ℤ))} ↦
        (volume
            (adaptedCellAt (Selection.normalizedRoot m)
              (n - (i.1 : ℤ)) i.2.1)).toReal /
            (volume (adaptedCellTranslate (roundedGrid l m) j y)).toReal *
          Transport.coeffSpaceDoubledResponse
            (adaptedCellAt (Selection.normalizedRoot m)
              (n - (i.1 : ℤ)) i.2.1) a P Q) →
        Transport.coeffSpaceDoubledResponse
            (adaptedCellTranslate (roundedGrid l m) j y) a P Q ≤
          ∑' i : Σ u : ℕ, {w // w ∈ Z (n - (u : ℤ))},
            (volume
                (adaptedCellAt (Selection.normalizedRoot m)
                  (n - (i.1 : ℤ)) i.2.1)).toReal /
              (volume (adaptedCellTranslate (roundedGrid l m) j y)).toReal *
            Transport.coeffSpaceDoubledResponse
              (adaptedCellAt (Selection.normalizedRoot m)
                (n - (i.1 : ℤ)) i.2.1) a P Q) := by
  classical
  let hp := Recurrence.posDef_roundedGrid hl hm
  let hq := normalizedRoot_posDef_of_posDef hm
  obtain ⟨Z, hZ, hsub, hdom, hdisj, hrow, hrowOne, hnull⟩ :=
    exists_normalizedRoot_filling_roundedGrid hl hm n j y
  refine ⟨Z, hZ, hrow, hrowOne, ?_⟩
  intro hsum
  let I := Σ u : ℕ, {w // w ∈ Z (n - (u : ℤ))}
  let c : I → Set (Vec d) := fun i ↦
    adaptedCellAt (Selection.normalizedRoot m) (n - (i.1 : ℤ)) i.2.1
  let : Countable I := inferInstance
  have hc : ∀ i : I, IsOpenBoundedConvexDomain (c i) := fun i ↦
    hdom _ _ i.2.2
  have hcsub : ∀ i : I,
      c i ⊆ adaptedCellTranslate (roundedGrid l m) j y := fun i ↦
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
        adaptedCellAt (Selection.normalizedRoot m) r w := by
    ext x
    constructor
    · intro hx
      obtain ⟨⟨u, w⟩, hx⟩ := Set.mem_iUnion.mp hx
      refine Set.mem_iUnion.mpr
        ⟨n - (u : ℤ), Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
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
      change x ∈ adaptedCellAt (Selection.normalizedRoot m)
        (n - (((n - r).toNat : ℕ) : ℤ)) w
      rwa [hscale]
  have hcnull : volume
      (adaptedCellTranslate (roundedGrid l m) j y \ ⋃ i : I, c i) = 0 := by
    rw [hcover]
    exact hnull
  have hparent0 :
      volume (adaptedCellTranslate (roundedGrid l m) j y) ≠ 0 :=
    Transport.volume_adaptedCellTranslate_ne_zero hp j y
  change Summable (fun i : I ↦
    (volume (c i)).toReal /
        (volume (adaptedCellTranslate (roundedGrid l m) j y)).toReal *
      Transport.coeffSpaceDoubledResponse (c i) a P Q) at hsum
  change Transport.coeffSpaceDoubledResponse
      (adaptedCellTranslate (roundedGrid l m) j y) a P Q ≤
    ∑' i : I, (volume (c i)).toReal /
        (volume (adaptedCellTranslate (roundedGrid l m) j y)).toReal *
      Transport.coeffSpaceDoubledResponse (c i) a P Q
  exact Transport.coeffSpaceDoubledResponse_le_tsum_weight_of_countable_aePartition
    (Transport.isOpenBoundedConvexDomain_adaptedCellTranslate hp j y)
    hparent0 a hc hcsub hcpair hcnull hc0 P Q hsum

theorem exists_coeffSpaceDoubledResponse_roundedGrid_le_rowMajorant
    [NeZero d] {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {m : Mat d} (hm : m.PosDef) (n j : ℤ) (y : Vec d)
    (a : CoeffSpace d) (P Q : BlockVec d) :
    ∃ Z : ℤ → Finset (Fin d → ℤ),
      (∀ r, ↑(Z r) = Transport.fillingIndex (Selection.normalizedRoot m) n
        (adaptedCellTranslate (roundedGrid l m) j y) r) ∧
      ∀ B : ℤ → ℝ,
        (∀ r, 0 ≤ B r) →
        (∀ (u : ℕ) (w : Fin d → ℤ), w ∈ Z (n - (u : ℤ)) →
          Book.Ch02.doubledResponseJ
              (Response.adaptedDomainAt (normalizedRoot_posDef_of_posDef hm)
                (n - (u : ℤ)) w)
              (a.coeffOn
                (Response.adaptedDomainAt (normalizedRoot_posDef_of_posDef hm)
                  (n - (u : ℤ)) w)) P Q ≤ B (n - (u : ℤ))) →
        Summable (fun u : ℕ ↦
          (if u = 0 then 1 else
            6 * (d : ℝ) * Real.sqrt d *
              ((101 / 100 : ℝ) * witnessEccentricity m) *
                (3 : ℝ) ^ ((n - (u : ℤ)) - j)) * B (n - (u : ℤ))) →
        Transport.coeffSpaceDoubledResponse
            (adaptedCellTranslate (roundedGrid l m) j y) a P Q ≤
          ∑' u : ℕ,
            (if u = 0 then 1 else
              6 * (d : ℝ) * Real.sqrt d *
                ((101 / 100 : ℝ) * witnessEccentricity m) *
                  (3 : ℝ) ^ ((n - (u : ℤ)) - j)) * B (n - (u : ℤ)) := by
  classical
  obtain ⟨Z, hZ, hrow, hrowOne, hresponse⟩ :=
    exists_coeffSpaceDoubledResponse_roundedGrid_le_filling
      hl hm n j y a P Q
  refine ⟨Z, hZ, ?_⟩
  intro B hB0 hcell hmajor
  let I := Σ u : ℕ, {w // w ∈ Z (n - (u : ℤ))}
  let term : I → ℝ := fun i ↦
    (volume
        (adaptedCellAt (Selection.normalizedRoot m)
          (n - (i.1 : ℤ)) i.2.1)).toReal /
      (volume (adaptedCellTranslate (roundedGrid l m) j y)).toReal *
      Transport.coeffSpaceDoubledResponse
        (adaptedCellAt (Selection.normalizedRoot m)
          (n - (i.1 : ℤ)) i.2.1) a P Q
  let rowBound : ℕ → ℝ := fun u ↦
    if u = 0 then 1 else
      6 * (d : ℝ) * Real.sqrt d *
        ((101 / 100 : ℝ) * witnessEccentricity m) *
          (3 : ℝ) ^ ((n - (u : ℤ)) - j)
  change Summable (fun u : ℕ ↦ rowBound u * B (n - (u : ℤ))) at hmajor
  change Transport.coeffSpaceDoubledResponse
      (adaptedCellTranslate (roundedGrid l m) j y) a P Q ≤
    ∑' u : ℕ, rowBound u * B (n - (u : ℤ))
  have hrowWeight : ∀ u : ℕ,
      ∑ w ∈ Z (n - (u : ℤ)),
          (volume
              (adaptedCellAt (Selection.normalizedRoot m)
                (n - (u : ℤ)) w)).toReal /
            (volume (adaptedCellTranslate (roundedGrid l m) j y)).toReal ≤
        rowBound u := by
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
  have hq := normalizedRoot_posDef_of_posDef hm
  have hcellCoeff : ∀ (u : ℕ) (w : Fin d → ℤ),
      w ∈ Z (n - (u : ℤ)) →
      Transport.coeffSpaceDoubledResponse
          (adaptedCellAt (Selection.normalizedRoot m)
            (n - (u : ℤ)) w) a P Q ≤ B (n - (u : ℤ)) := by
    intro u w hw
    calc
      Transport.coeffSpaceDoubledResponse
          (adaptedCellAt (Selection.normalizedRoot m)
            (n - (u : ℤ)) w) a P Q =
          Book.Ch02.doubledResponseJ
            (Response.adaptedDomainAt hq (n - (u : ℤ)) w)
            (a.coeffOn (Response.adaptedDomainAt hq
              (n - (u : ℤ)) w)) P Q := by
                simpa only [Response.adaptedDomainAt_carrier] using
                  Transport.coeffSpaceDoubledResponse_eq_doubledResponseJ
                    (Response.adaptedDomainAt hq (n - (u : ℤ)) w) a P Q
      _ ≤ B (n - (u : ℤ)) := hcell u w hw
  have hterm0 : ∀ i : I, 0 ≤ term i := by
    intro i
    have hresponse0 : 0 ≤ Transport.coeffSpaceDoubledResponse
        (adaptedCellAt (Selection.normalizedRoot m)
          (n - (i.1 : ℤ)) i.2.1) a P Q := by
      have heq : Transport.coeffSpaceDoubledResponse
          (adaptedCellAt (Selection.normalizedRoot m)
            (n - (i.1 : ℤ)) i.2.1) a P Q =
          Book.Ch02.doubledResponseJ
            (Response.adaptedDomainAt hq (n - (i.1 : ℤ)) i.2.1)
            (a.coeffOn
              (Response.adaptedDomainAt hq (n - (i.1 : ℤ)) i.2.1)) P Q := by
        simpa only [Response.adaptedDomainAt_carrier] using
          Transport.coeffSpaceDoubledResponse_eq_doubledResponseJ
            (Response.adaptedDomainAt hq (n - (i.1 : ℤ)) i.2.1) a P Q
      rw [heq]
      exact Book.Ch02.doubledResponseJ_nonneg
        (Response.adaptedDomainAt hq (n - (i.1 : ℤ)) i.2.1)
        (a.coeffOn (Response.adaptedDomainAt hq
          (n - (i.1 : ℤ)) i.2.1)) P Q
    exact mul_nonneg
      (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) hresponse0
  have hrowTerm : ∀ u : ℕ,
      (∑' w : {w // w ∈ Z (n - (u : ℤ))}, term ⟨u, w⟩) ≤
        rowBound u * B (n - (u : ℤ)) := by
    intro u
    rw [tsum_fintype]
    let rowTerm : (Fin d → ℤ) → ℝ := fun w ↦
      (volume
          (adaptedCellAt (Selection.normalizedRoot m)
            (n - (u : ℤ)) w)).toReal /
        (volume (adaptedCellTranslate (roundedGrid l m) j y)).toReal *
        Transport.coeffSpaceDoubledResponse
          (adaptedCellAt (Selection.normalizedRoot m)
            (n - (u : ℤ)) w) a P Q
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
    Transport.coeffSpaceDoubledResponse
        (adaptedCellTranslate (roundedGrid l m) j y) a P Q ≤
        ∑' i : I, term i := hresponse (by
          change Summable term
          exact htermSummable)
    _ = ∑' u : ℕ, ∑' w : {w // w ∈ Z (n - (u : ℤ))}, term ⟨u, w⟩ :=
      htermSummable.tsum_sigma' (fun _ ↦ (hasSum_fintype _).summable)
    _ ≤ ∑' u : ℕ, rowBound u * B (n - (u : ℤ)) :=
      hrowSummable.tsum_le_tsum hrowTerm hmajor

private theorem adaptedCell_subset_adaptedCell_add_of_norm_inv_mul_le
    [NeZero d] {p q : Mat d} (hq : q.PosDef) {M : ℤ} {G : ℕ}
    (hsize : ‖q⁻¹ * p‖ * Real.sqrt d ≤ (3 : ℝ) ^ (G : ℤ)) :
    adaptedCell p M ⊆ adaptedCell q (M + (G : ℤ)) := by
  have hsmall : adaptedCell (q⁻¹ * p) M ⊆
      centeredCube d (M + (G : ℤ)) :=
    Selection.adaptedCell_subset_centeredCube_add
      (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)) hsize
  rintro x ⟨y, hy, rfl⟩
  have hz : matVecMul (q⁻¹ * p) y ∈ centeredCube d (M + (G : ℤ)) :=
    hsmall ⟨y, hy, rfl⟩
  refine ⟨matVecMul (q⁻¹ * p) y, hz, ?_⟩
  rw [matVecMul_mul, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv q (isUnit_det_of_posDef hq), Matrix.one_mul]

theorem exists_outerCellIndices_enclosed_by_normalizedRoot_at_generation
    [NeZero d] {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {m : Mat d} (hm : m.PosDef) (M : ℤ) :
    ∃ G : ℕ, ∃ Z : ℕ → Finset (Fin d → ℤ),
      (3 : ℝ) ^ (G : ℤ) ≤
          1 + 3 * ((100 / 99 : ℝ) * witnessEccentricity m * Real.sqrt d) ∧
      (∀ u : ℕ,
        ↑(Z u) = {w : Fin d → ℤ |
          adaptedCellCenter (roundedGrid l m) (M - (u : ℤ)) w ∈
            adaptedCell (roundedGrid l m) M}) ∧
      (∀ u : ℕ, (Z u).card = 3 ^ (d * u)) ∧
      ∀ u : ℕ, ∀ w ∈ Z u,
        adaptedCellTranslate (roundedGrid l m) (M - (u : ℤ))
            (adaptedCellCenter (roundedGrid l m) (M - (u : ℤ)) w) ⊆
          adaptedCell (Selection.normalizedRoot m) (M + (G : ℤ)) := by
  classical
  let p : Mat d := roundedGrid l m
  let q : Mat d := Selection.normalizedRoot m
  let x : ℝ := (100 / 99 : ℝ) * witnessEccentricity m * Real.sqrt d
  have hp : p.PosDef := Recurrence.posDef_roundedGrid hl hm
  have hq : q.PosDef := normalizedRoot_posDef_of_posDef hm
  have hecc0 : 0 ≤ witnessEccentricity m :=
    (Transport.zero_lt_witnessEccentricity hm).le
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hcross : ‖q⁻¹ * p‖ ≤
      (100 / 99 : ℝ) * witnessEccentricity m := by
    calc
      ‖q⁻¹ * p‖ ≤ ‖q⁻¹‖ * ‖p‖ := norm_mul_le _ _
      _ ≤ 1 * ‖p‖ := mul_le_mul_of_nonneg_right
        (by simpa only [q] using Selection.normalizedRoot_inv_norm_le_one hm)
        (norm_nonneg p)
      _ ≤ 1 * ((100 / 99 : ℝ) * witnessEccentricity m) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [p] using Selection.norm_roundedGrid_le hl hm) zero_le_one
      _ = (100 / 99 : ℝ) * witnessEccentricity m := by ring
  obtain ⟨G, hGlo, hGhi⟩ := Entry.exists_pow_three_bracket hx0
  have hsize : ‖q⁻¹ * p‖ * Real.sqrt d ≤ (3 : ℝ) ^ (G : ℤ) :=
    (mul_le_mul_of_nonneg_right hcross (Real.sqrt_nonneg d)).trans hGlo
  have houter : adaptedCell p M ⊆ adaptedCell q (M + (G : ℤ)) :=
    adaptedCell_subset_adaptedCell_add_of_norm_inv_mul_le hq hsize
  have hrows : ∀ u : ℕ, ∃ Z : Finset (Fin d → ℤ),
      ↑Z = {w : Fin d → ℤ |
        adaptedCellCenter p (M - (u : ℤ)) w ∈ adaptedCell p M} ∧
        Z.card = 3 ^ (d * u) := by
    intro u
    obtain ⟨Z, hZ, hcard⟩ := Recurrence.exists_finset_adaptedCellCenter_mem
      hp (show M - (u : ℤ) ≤ M by omega)
    refine ⟨Z, hZ, ?_⟩
    have hdiff : M - (M - (u : ℤ)) = (u : ℤ) := by omega
    simpa only [hdiff, Int.toNat_natCast] using hcard
  choose Z hZ hcard using hrows
  refine ⟨G, Z, by simpa only [x] using hGhi, ?_, hcard, ?_⟩
  · intro u
    simpa only [p] using hZ u
  · intro u w hw
    have hwCenter :
        adaptedCellCenter p (M - (u : ℤ)) w ∈ adaptedCell p M := by
      have hw' : w ∈ (↑(Z u) : Set (Fin d → ℤ)) := by
        simpa only [Finset.mem_coe] using hw
      rw [hZ u] at hw'
      exact hw'
    have hcell : adaptedCellAt p (M - (u : ℤ)) w ⊆ adaptedCell p M :=
      Recurrence.adaptedCellAt_subset_adaptedCell hp
        (show M - (u : ℤ) ≤ M by omega) hwCenter
    simpa only [p, q, adaptedCellAt_eq_adaptedCellTranslate] using
      hcell.trans houter

theorem translateCube_mem_descendants_of_generation_filling
    [NeZero d] {l : ℤ} {m : Mat d} (hm : m.PosDef)
    {n j M : ℤ} (hnM : n ≤ M) {y : Vec d}
    {Z : ℤ → Finset (Fin d → ℤ)}
    (hZ : ∀ r, ↑(Z r) = Transport.fillingIndex (Selection.normalizedRoot m) n
      (adaptedCellTranslate (roundedGrid l m) j y) r)
    (hEnclose : adaptedCellTranslate (roundedGrid l m) j y ⊆
      adaptedCell (Selection.normalizedRoot m) M)
    {r : ℤ} {w : Fin d → ℤ} (hw : w ∈ Z r) :
    translateCube w (originCube d r) ∈
      descendantsAtScale (originCube d M) r := by
  have hwFill : w ∈ Transport.fillingIndex (Selection.normalizedRoot m) n
      (adaptedCellTranslate (roundedGrid l m) j y) r := by
    rw [← hZ r]
    exact Finset.mem_coe.mpr hw
  have hrM : r ≤ M := (Transport.le_of_mem_fillingIndex hwFill).trans hnM
  have hq := normalizedRoot_posDef_of_posDef hm
  have hcenterCell : adaptedCellCenter (Selection.normalizedRoot m) r w ∈
      adaptedCellAt (Selection.normalizedRoot m) r w := by
    rw [Recurrence.adaptedCellAt_eq_image, Recurrence.adaptedCellCenter_eq]
    exact ⟨standardCellCenter r w,
      Recurrence.standardCellCenter_mem_standardCell r w, rfl⟩
  have hcenterParent : adaptedCellCenter (Selection.normalizedRoot m) r w ∈
      adaptedCell (Selection.normalizedRoot m) M :=
    hEnclose (Transport.adaptedCellAt_subset_of_mem_fillingIndex hwFill hcenterCell)
  have hwAligned : w ∈ Response.alignedIndex (Selection.normalizedRoot m) r M :=
    (Response.mem_alignedIndex_iff hq hrM).mpr hcenterParent
  have hDepth :=
    Response.translateCube_mem_descendantsAtDepth_of_mem_alignedIndex
      hq hrM hwAligned
  rw [mem_descendantsAtScale_iff hrM]
  simpa only [originCube] using hDepth

end

end HighContrast
end HCPolySupport
