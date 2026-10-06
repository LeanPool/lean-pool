/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Window.CountableSubadditivity
public import LeanPool.HighContrastHomogenization.Provider.Window.BurnSeries
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCellPositivity
public import LeanPool.HighContrastHomogenization.Provider.Sharp.ReflectionOrder
public import LeanPool.HighContrastHomogenization.Provider.Transport.WindowCellBounds

/-!
# High-contrast homogenization: Provider.Window.ScaledStandardToAdapted

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The scale-adapted standard-to-adapted bridge

The standard-to-adapted bridge carries a uniform standard
envelope `Y · burnDiscount` to the adapted cell at the same burn base as the
grid.  The per-generation caps need the *scale-adapted* variant: when every
standard subcell of scale `k` obeys the envelope `Y · 3^{g(r−k)}` (as the
Dagger coarse bound provides at any burn scale, relative to the adapted
cell's own scale `r`), the adapted cell obeys `boundaryConst · Y` — the
Whitney rows lose `3^{-u}` in volume and gain only `3^{gu}` in envelope, so
the same geometric series `ζ_g` closes with no burn factor at all.
-/

namespace HCPolySupport
namespace HighContrast
namespace Window

open MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The scaled Whitney series: `Σ_u 3^{-u}·3^{gu} = ζ_g`. -/
private theorem summable_scaled_and_tsum_le {g : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    Summable (fun u : ℕ =>
      (3 : ℝ) ^ (-(u : ℤ)) * (3 : ℝ) ^ (g * (u : ℝ))) ∧
    ∑' u : ℕ, (3 : ℝ) ^ (-(u : ℤ)) * (3 : ℝ) ^ (g * (u : ℝ)) ≤
      zetaG g := by
  have hterm : ∀ u : ℕ,
      (3 : ℝ) ^ (-(u : ℤ)) * (3 : ℝ) ^ (g * (u : ℝ)) =
        ((3 : ℝ) ^ (-(1 - g))) ^ u := by
    intro u
    rw [← Real.rpow_intCast (3 : ℝ) (-(u : ℤ)),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      ← Real.rpow_natCast ((3 : ℝ) ^ (-(1 - g))) u,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    ring
  have hr0 : 0 ≤ (3 : ℝ) ^ (-(1 - g)) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hr1 : (3 : ℝ) ^ (-(1 - g)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (by linarith only [hg.2])
  constructor
  · refine Summable.congr (summable_geometric_of_lt_one hr0 hr1) ?_
    intro u
    exact (hterm u).symm
  · rw [tsum_congr hterm, tsum_geometric_of_lt_one hr0 hr1]
    exact le_of_eq (by rw [zetaG])

/-- **The scale-adapted Whitney bridge.**  Simultaneous standard-cell bounds
with the scale-adapted envelope `Y·3^{g(r−k)}` imply the adapted-cell bound
`boundaryConst·Y`, with no burn factor. -/
theorem adapted_scaled_of_standard
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {jStar : ℤ} (hj : (kZero d : ℤ) ≤ jStar)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {n : Mat d} (hn : n.PosDef) {a : CoeffSpace d} {E : BlockMat d}
    (hE : Book.Ch02.BlockPosDef E) {Y : ℝ} (hY : 0 ≤ Y)
    (r : ℤ) (y : Vec d)
    (hstandard : ∀ (k : ℤ) (w : Fin d → ℤ),
      standardCell d k w ⊆
        adaptedCellTranslate (roundedGrid jStar n) r y →
        BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
          (blockScale (Y * (3 : ℝ) ^ (g * ((r : ℝ) - (k : ℝ)))) E)) :
    BlockMatLoewnerLE
      (coarseBlock (adaptedCellTranslate (roundedGrid jStar n) r y) a)
      (blockScale (boundaryConst Cd g n * Y) E) := by
  classical
  let : NeZero d := ⟨by omega⟩
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  let p : Mat d := roundedGrid jStar n
  have hp : p.PosDef := Recurrence.posDef_roundedGrid hj hn
  obtain ⟨Z, hZ, hsub, hdom, _hvol, hdisj, _hrowENN, _hrowOneENN, hnull⟩ :=
    Transport.maximal_filling hp Matrix.PosDef.one r r y
  have hidentity : ∀ (b : ℤ) (w : Fin d → ℤ),
      adaptedCellAt (1 : Mat d) b w = standardCell d b w := by
    intro b w
    rw [Recurrence.adaptedCellAt_eq_image]
    have hone : matVecMul (1 : Mat d) = fun x => x := by
      funext x i
      exact congrFun (Matrix.one_mulVec x) i
    rw [hone, Set.image_id']
  let I := Σ u : ℕ, {w // w ∈ Z (r - (u : ℤ))}
  let c : I → Set (Vec d) := fun i =>
    adaptedCellAt (1 : Mat d) (r - (i.1 : ℤ)) i.2.1
  let : Countable I := inferInstance
  have hc : ∀ i : I, IsOpenBoundedConvexDomain (c i) := fun i =>
    hdom _ _ i.2.2
  have hcsub : ∀ i : I, c i ⊆ adaptedCellTranslate p r y := fun i =>
    hsub _ _ i.2.2
  have hcpair : Pairwise fun i j : I => Disjoint (c i) (c j) := by
    intro i j hij
    apply hdisj _ _ _ i.2.2 _ j.2.2
    intro heq
    apply hij
    rcases i with ⟨u, w⟩
    rcases j with ⟨v, z⟩
    have huv : u = v := by
      have hs := congrArg Prod.fst heq
      dsimp at hs
      omega
    subst v
    have hwz : w = z := Subtype.ext (congrArg Prod.snd heq)
    subst z
    rfl
  have hc0 : ∀ i : I, volume (c i) ≠ 0 := fun i =>
    (Recurrence.volume_adaptedCellAt_pos Matrix.PosDef.one _ _).ne'
  have hcover : (⋃ i : I, c i) =
      ⋃ b ∈ Set.Iic r, ⋃ w ∈ (Z b : Set (Fin d → ℤ)),
        adaptedCellAt (1 : Mat d) b w := by
    ext x
    constructor
    · intro hx
      obtain ⟨⟨u, w⟩, hx⟩ := Set.mem_iUnion.mp hx
      refine Set.mem_iUnion.mpr ⟨r - (u : ℤ), Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · exact Set.mem_Iic.mpr (by omega)
      · exact Set.mem_iUnion.mpr ⟨w.1, Set.mem_iUnion.mpr ⟨w.2, hx⟩⟩
    · intro hx
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hbr, hb⟩ := Set.mem_iUnion.mp hb
      obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hb
      obtain ⟨hwZ, hx⟩ := Set.mem_iUnion.mp hw
      have hscale : r - (((r - b).toNat : ℕ) : ℤ) = b := by
        rw [Int.toNat_of_nonneg (sub_nonneg.mpr (Set.mem_Iic.mp hbr))]
        omega
      have hwZ' : w ∈ Z (r - (((r - b).toNat : ℕ) : ℤ)) := by
        rw [hscale]
        exact hwZ
      let i : I := ⟨(r - b).toNat, ⟨w, hwZ'⟩⟩
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      change x ∈ adaptedCellAt (1 : Mat d)
        (r - (((r - b).toNat : ℕ) : ℤ)) w
      rwa [hscale]
  have hcnull : volume (adaptedCellTranslate p r y \ ⋃ i : I, c i) = 0 := by
    rw [hcover]
    exact hnull
  have hparent0 : volume (adaptedCellTranslate p r y) ≠ 0 :=
    Transport.volume_adaptedCellTranslate_ne_zero hp r y
  intro X
  let eQuad : ℝ :=
    1 / 2 * blockVecDot X (blockMatVecMul E X)
  have heQuad0 : 0 ≤ eQuad := by
    by_cases hX : X = 0
    · subst X
      simp [eQuad, blockMatVecMul, blockVecDot, vecDot]
    · exact mul_nonneg (by norm_num) (hE X hX).le
  let term : I → ℝ := fun i =>
    (volume (c i)).toReal / (volume (adaptedCellTranslate p r y)).toReal *
      (1 / 2 * blockVecDot X (blockMatVecMul (coarseBlock (c i) a) X))
  have hterm0 : ∀ i : I, 0 ≤ term i := by
    intro i
    have hquad0 : 0 ≤ 1 / 2 *
        blockVecDot X (blockMatVecMul (coarseBlock (c i) a) X) := by
      by_cases hX : X = 0
      · subst X
        simp [blockMatVecMul, blockVecDot, vecDot]
      · exact mul_nonneg (by norm_num)
          ((Recurrence.blockPosDef_coarseBlock_adaptedCellAt
            Matrix.PosDef.one _ _ a) X hX).le
    exact mul_nonneg
      (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) hquad0
  have hecc : 1 ≤ witnessEccentricity n := Initialization.one_le_witnessEccentricity hn
  have hCd1 : 1 ≤ Cd := (le_max_left _ _).trans hCd
  have hCdDim : 12 * (d : ℝ) * Real.sqrt d ≤ Cd :=
    (le_max_right _ _).trans hCd
  have hnorm : ‖p⁻¹ * (1 : Mat d)‖ ≤ 2 := by
    rw [Matrix.mul_one]
    exact (norm_inv_roundedGrid_le hj hn).trans (by norm_num)
  have hdim : 6 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * (1 : Mat d)‖ ≤
      Cd * witnessEccentricity n := by
    have hbase : 6 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * (1 : Mat d)‖ ≤
        12 * (d : ℝ) * Real.sqrt d := by
      have hnonneg : 0 ≤ 6 * (d : ℝ) * Real.sqrt d := by positivity
      have := mul_le_mul_of_nonneg_left hnorm hnonneg
      linarith only [this]
    exact hbase.trans <| hCdDim.trans <|
      (le_mul_of_one_le_right (by linarith only [hCd1]) hecc)
  have hrowWeight : ∀ u : ℕ,
      ∑ w ∈ Z (r - (u : ℤ)),
          (volume (adaptedCellAt (1 : Mat d) (r - (u : ℤ)) w)).toReal /
            (volume (adaptedCellTranslate p r y)).toReal ≤
        Cd * witnessEccentricity n * (3 : ℝ) ^ (-(u : ℤ)) := by
    intro u
    by_cases hu : u = 0
    · subst u
      simp only [Nat.cast_zero, sub_zero, neg_zero, zpow_zero, mul_one]
      exact (Transport.sum_relative_volume_row_le_one hp
        Matrix.PosDef.one (hZ r)).trans
        (one_le_mul_of_one_le_of_one_le hCd1 hecc)
    · have hur : r - (u : ℤ) < r := by omega
      have hrow := Transport.sum_relative_volume_row_le hp Matrix.PosDef.one hur
        (hZ (r - (u : ℤ)))
      refine hrow.trans ?_
      have hpw : (r - (u : ℤ)) - r = -(u : ℤ) := by omega
      rw [hpw]
      exact mul_le_mul_of_nonneg_right hdim (by positivity)
  have hcastu : ∀ u : ℕ,
      (3 : ℝ) ^ (g * ((r : ℝ) - ((r - (u : ℤ) : ℤ) : ℝ))) =
        (3 : ℝ) ^ (g * (u : ℝ)) := by
    intro u
    congr 1
    push_cast
    ring
  have hrow : ∀ u : ℕ, (∑' w : {w // w ∈ Z (r - (u : ℤ))},
      term ⟨u, w⟩) ≤
      (Cd * witnessEccentricity n * Y * eQuad) *
        ((3 : ℝ) ^ (-(u : ℤ)) * (3 : ℝ) ^ (g * (u : ℝ))) := by
    intro u
    rw [tsum_fintype]
    let rowTerm : (Fin d → ℤ) → ℝ := fun w =>
      (volume (adaptedCellAt (1 : Mat d) (r - (u : ℤ)) w)).toReal /
          (volume (adaptedCellTranslate p r y)).toReal *
        (1 / 2 * blockVecDot X
          (blockMatVecMul
            (coarseBlock (adaptedCellAt (1 : Mat d) (r - (u : ℤ)) w) a) X))
    change (∑ w : {w // w ∈ Z (r - (u : ℤ))}, rowTerm w.1) ≤ _
    rw [← Finset.sum_subtype (Z (r - (u : ℤ))) (fun _ => Iff.rfl) rowTerm]
    calc
      ∑ w ∈ Z (r - (u : ℤ)), rowTerm w ≤
          ∑ w ∈ Z (r - (u : ℤ)),
            ((volume (adaptedCellAt (1 : Mat d) (r - (u : ℤ)) w)).toReal /
                (volume (adaptedCellTranslate p r y)).toReal) *
              (Y * (3 : ℝ) ^ (g * (u : ℝ)) * eQuad) := by
        refine Finset.sum_le_sum fun w hw => ?_
        dsimp [rowTerm]
        refine mul_le_mul_of_nonneg_left ?_
          (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
        calc
          1 / 2 * blockVecDot X
              (blockMatVecMul (coarseBlock (c ⟨u, ⟨w, hw⟩⟩) a) X) =
              1 / 2 * blockVecDot X
                (blockMatVecMul
                  (coarseBlock (standardCell d (r - (u : ℤ)) w) a) X) := by
            rw [show c ⟨u, ⟨w, hw⟩⟩ = standardCell d (r - (u : ℤ)) w from
              hidentity _ _]
          _ ≤ 1 / 2 * blockVecDot X
              (blockMatVecMul
                (blockScale
                  (Y * (3 : ℝ) ^
                    (g * ((r : ℝ) - ((r - (u : ℤ) : ℤ) : ℝ)))) E) X) :=
            hstandard _ _ (by
              rw [← hidentity]
              exact hsub _ _ hw) X
          _ = Y * (3 : ℝ) ^ (g * (u : ℝ)) * eQuad := by
            rw [Sharp.blockVecDot_blockMatVecMul_blockScale, hcastu u]
            dsimp [eQuad]
            ring
      _ = (∑ w ∈ Z (r - (u : ℤ)),
            (volume (adaptedCellAt (1 : Mat d) (r - (u : ℤ)) w)).toReal /
              (volume (adaptedCellTranslate p r y)).toReal) *
          (Y * (3 : ℝ) ^ (g * (u : ℝ)) * eQuad) := by
        rw [Finset.sum_mul]
      _ ≤ (Cd * witnessEccentricity n * (3 : ℝ) ^ (-(u : ℤ))) *
          (Y * (3 : ℝ) ^ (g * (u : ℝ)) * eQuad) := by
        exact mul_le_mul_of_nonneg_right (hrowWeight u)
          (mul_nonneg (mul_nonneg hY (Real.rpow_nonneg (by norm_num) _))
            heQuad0)
      _ = (Cd * witnessEccentricity n * Y * eQuad) *
          ((3 : ℝ) ^ (-(u : ℤ)) * (3 : ℝ) ^ (g * (u : ℝ))) := by ring
  obtain ⟨hgeomSummable, hgeomTsum⟩ := summable_scaled_and_tsum_le hg
  have hK0 : 0 ≤ Cd * witnessEccentricity n * Y * eQuad := by
    have hecc0 : (0 : ℝ) ≤ witnessEccentricity n := by
      linarith only [hecc]
    have hCd0 : (0 : ℝ) ≤ Cd := by linarith only [hCd1]
    positivity
  have hrow0 : ∀ u : ℕ, 0 ≤ ∑' w : {w // w ∈ Z (r - (u : ℤ))},
      term ⟨u, w⟩ :=
    fun u => tsum_nonneg fun w => hterm0 ⟨u, w⟩
  have hrowSummable : Summable fun u : ℕ =>
      ∑' w : {w // w ∈ Z (r - (u : ℤ))}, term ⟨u, w⟩ :=
    Summable.of_nonneg_of_le hrow0 hrow (hgeomSummable.mul_left _)
  have htermSummable : Summable term :=
    (summable_sigma_of_nonneg hterm0).2
      ⟨fun _ => (hasSum_fintype _).summable, hrowSummable⟩
  have hsubadd := blockQuadratic_le_tsum_weight_of_countable_aePartition
    (Transport.isOpenBoundedConvexDomain_adaptedCellTranslate hp r y) hparent0 a
    hc hcsub hcpair hcnull hc0 X htermSummable
  calc
    1 / 2 * blockVecDot X
        (blockMatVecMul (coarseBlock (adaptedCellTranslate p r y) a) X) ≤
        ∑' i : I, term i := hsubadd
    _ = ∑' u : ℕ, ∑' w : {w // w ∈ Z (r - (u : ℤ))}, term ⟨u, w⟩ :=
      htermSummable.tsum_sigma' (fun _ => (hasSum_fintype _).summable)
    _ ≤ ∑' u : ℕ, (Cd * witnessEccentricity n * Y * eQuad) *
        ((3 : ℝ) ^ (-(u : ℤ)) * (3 : ℝ) ^ (g * (u : ℝ))) :=
      hrowSummable.tsum_le_tsum hrow (hgeomSummable.mul_left _)
    _ = (Cd * witnessEccentricity n * Y * eQuad) *
        (∑' u : ℕ, (3 : ℝ) ^ (-(u : ℤ)) *
          (3 : ℝ) ^ (g * (u : ℝ))) := by rw [tsum_mul_left]
    _ ≤ (Cd * witnessEccentricity n * Y * eQuad) * zetaG g :=
      mul_le_mul_of_nonneg_left hgeomTsum hK0
    _ = 1 / 2 * blockVecDot X
        (blockMatVecMul (blockScale (boundaryConst Cd g n * Y) E) X) := by
      rw [Sharp.blockVecDot_blockMatVecMul_blockScale]
      dsimp [boundaryConst, eQuad]
      ring

end

end Window
end HighContrast
end HCPolySupport
