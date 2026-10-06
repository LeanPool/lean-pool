/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBurnSplitTsum
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRowWeightSummable
public import LeanPool.HighContrastHomogenization.Provider.Window.ScaledStandardToAdapted

/-!
# High-contrast homogenization: Provider.Window.BurnSplitStandardToAdapted

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The burn-split standard-to-adapted bridge

`adapted_scaled_of_standard` transfers simultaneous standard-cell bounds to an
adapted cell and pays `boundaryConst Cd g n` for the transfer, because it applies
the eccentricity-carrying Whitney row estimate to every row — including the top
one, where the sharp estimate is the partition property.

The printed conversion (Lemma 2.13 of HC, whose conclusion is (2.124)) does
not pay that.  It splits the Whitney rows at the burn depth `D`: on the band
`u ≤ D` the hypothesis envelope is flat, so those rows are covered by the
total row weight alone, which is at most one; only the
rows below the band meet the geometric estimate, and there the envelope's growth
`3 ^ (g (u - D))` is beaten by the volume decay `3 ^ (-u)`, leaving `3 ^ (-D)`.
The geometric constant therefore multiplies `3 ^ (-D)` rather than the whole
sum, and is absorbed once the depth exceeds `log₃ (Cd 𝔢 ζ_g / δ)` — HC (2.123),
and its stated principle that the aspect ratio enters through a scale
restriction and nowhere else.

Everything outside the row accounting is `adapted_scaled_of_standard`'s proof
unchanged.
-/

namespace HCPolySupport
namespace HighContrast
namespace Window

open MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- **The burn-split Whitney bridge.**  Standard-cell bounds whose envelope is
truncated `D` scales above the adapted cell's own imply the adapted-cell bound
with constant `1 + Cd * 𝔢 * ζ_g * 3 ^ (-D)`: the eccentricity rides on the burn
depth instead of multiplying. -/
theorem adapted_burnsplit_of_standard
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {jStar : ℤ} (hj : (kZero d : ℤ) ≤ jStar)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {n : Mat d} (hn : n.PosDef) {a : CoeffSpace d} {E : BlockMat d}
    (hE : Book.Ch02.BlockPosDef E) {Y : ℝ} (hY : 0 ≤ Y)
    (D : ℕ) (r : ℤ) (y : Vec d)
    (hstandard : ∀ (k : ℤ) (w : Fin d → ℤ),
      standardCell d k w ⊆
        adaptedCellTranslate (roundedGrid jStar n) r y →
        BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
          (blockScale
            (Y * (3 : ℝ) ^
              (g * max ((r : ℝ) - (k : ℝ) - (D : ℝ)) 0)) E)) :
    BlockMatLoewnerLE
      (coarseBlock (adaptedCellTranslate (roundedGrid jStar n) r y) a)
      (blockScale
        ((1 + Cd * witnessEccentricity n * zetaG g *
          (3 : ℝ) ^ (-(D : ℤ))) * Y) E) := by
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
      refine Set.mem_iUnion.mpr ⟨⟨(r - b).toNat, ⟨w, hwZ'⟩⟩, ?_⟩
      change x ∈ adaptedCellAt (1 : Mat d)
        (r - (((r - b).toNat : ℕ) : ℤ)) w
      rwa [hscale]
  have hcnull : volume (adaptedCellTranslate p r y \ ⋃ i : I, c i) = 0 := by
    rw [hcover]
    exact hnull
  have hparent0 : volume (adaptedCellTranslate p r y) ≠ 0 :=
    Transport.volume_adaptedCellTranslate_ne_zero hp r y
  have hparentTop : volume (adaptedCellTranslate p r y) ≠ ⊤ :=
    Transport.volume_adaptedCellTranslate_ne_top p r y
  intro X
  let eQuad : ℝ := 1 / 2 * blockVecDot X (blockMatVecMul E X)
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
  have hecc0 : (0 : ℝ) ≤ witnessEccentricity n := by linarith only [hecc]
  have hCd1 : 1 ≤ Cd := (le_max_left _ _).trans hCd
  have hCd0 : (0 : ℝ) ≤ Cd := by linarith only [hCd1]
  -- the row weights
  let wrow : ℕ → ℝ := fun u =>
    ∑ w ∈ Z (r - (u : ℤ)),
      (volume (adaptedCellAt (1 : Mat d) (r - (u : ℤ)) w)).toReal /
        (volume (adaptedCellTranslate p r y)).toReal
  let envu : ℕ → ℝ := fun u =>
    (3 : ℝ) ^ (g * max ((u : ℝ) - (D : ℝ)) 0)
  have hwrow0 : ∀ u : ℕ, 0 ≤ wrow u := by
    intro u
    exact Finset.sum_nonneg fun w _ =>
      div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hdim : 6 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * (1 : Mat d)‖ ≤
      Cd * witnessEccentricity n := by
    have hnorm : ‖p⁻¹ * (1 : Mat d)‖ ≤ 2 := by
      rw [Matrix.mul_one]
      exact (norm_inv_roundedGrid_le hj hn).trans (by norm_num)
    have hCdDim : 12 * (d : ℝ) * Real.sqrt d ≤ Cd :=
      (le_max_right _ _).trans hCd
    have hbase : 6 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * (1 : Mat d)‖ ≤
        12 * (d : ℝ) * Real.sqrt d := by
      have hnonneg : 0 ≤ 6 * (d : ℝ) * Real.sqrt d := by positivity
      have := mul_le_mul_of_nonneg_left hnorm hnonneg
      linarith only [this]
    exact hbase.trans <| hCdDim.trans <|
      (le_mul_of_one_le_right (by linarith only [hCd1]) hecc)
  -- OBLIGATIONS 1 and 2 : summability and the partition bound, together
  have hwrowPartial : ∀ N : ℕ, ∑ u ∈ Finset.range N, wrow u ≤ 1 := by
    intro N
    classical
    have hmemZ : ∀ i ∈ (Finset.range N).sigma (fun u => Z (r - (u : ℤ))),
        i.2 ∈ Z (r - (i.1 : ℤ)) := by
      intro i hi
      exact (Finset.mem_sigma.mp hi).2
    have hnested : ∑ u ∈ Finset.range N, wrow u =
        ∑ i ∈ (Finset.range N).sigma (fun u => Z (r - (u : ℤ))),
          (volume (adaptedCellAt (1 : Mat d) (r - (i.1 : ℤ)) i.2)).toReal /
            (volume (adaptedCellTranslate p r y)).toReal :=
      Finset.sum_sigma' (Finset.range N) (fun u => Z (r - (u : ℤ)))
        (fun u w =>
          (volume (adaptedCellAt (1 : Mat d) (r - (u : ℤ)) w)).toReal /
            (volume (adaptedCellTranslate p r y)).toReal)
    rw [hnested]
    refine Quenched.finset_relative_volume_le_one
      ((Finset.range N).sigma (fun u => Z (r - (u : ℤ))))
      (c := fun i => adaptedCellAt (1 : Mat d) (r - (i.1 : ℤ)) i.2)
      ?_ ?_ ?_ hparentTop hparent0
    · intro i hi
      exact (hdom _ _ (hmemZ i hi)).isOpen.measurableSet
    · intro i hi j hj hij
      refine hdisj _ _ _ (hmemZ i (by simpa using hi)) _
        (hmemZ j (by simpa using hj)) ?_
      intro heq
      apply hij
      have h1 : r - (i.1 : ℤ) = r - (j.1 : ℤ) := congrArg Prod.fst heq
      have h2 : i.2 = j.2 := congrArg Prod.snd heq
      have h3 : i.1 = j.1 := by omega
      exact Sigma.ext h3 (heq_of_eq h2)
    · intro i hi
      exact hsub _ _ (hmemZ i hi)
  obtain ⟨hwrowSummable, hwrowTotal⟩ :=
    Quenched.summable_and_tsum_le_one_of_sum_range_le hwrow0 hwrowPartial
  -- OBLIGATION 3 : the deep-row bound
  have hwrowDeep : ∀ v : ℕ, wrow (v + (D + 1)) ≤
      (Cd * witnessEccentricity n) *
        (3 : ℝ) ^ (-((v : ℝ) + (D : ℝ) + 1)) := by
    intro v
    have hlt : r - ((v + (D + 1) : ℕ) : ℤ) < r := by omega
    have hrowle := Transport.sum_relative_volume_row_le hp Matrix.PosDef.one hlt
      (hZ (r - ((v + (D + 1) : ℕ) : ℤ)))
    have hpw : (r - ((v + (D + 1) : ℕ) : ℤ)) - r =
        -((v + (D + 1) : ℕ) : ℤ) := by omega
    rw [hpw] at hrowle
    have hzr : (3 : ℝ) ^ (-((v + (D + 1) : ℕ) : ℤ)) =
        (3 : ℝ) ^ (-((v : ℝ) + (D : ℝ) + 1)) := by
      rw [← Real.rpow_intCast (3 : ℝ) (-((v + (D + 1) : ℕ) : ℤ))]
      congr 1
      push_cast
      ring
    rw [hzr] at hrowle
    exact hrowle.trans
      (mul_le_mul_of_nonneg_right hdim (Real.rpow_nonneg (by norm_num) _))
  -- the geometric comparison series
  have hr0 : (0 : ℝ) < (3 : ℝ) ^ (-(1 - g)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : (3 : ℝ) ^ (-(1 - g)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hg.2])
  have hgeomS : Summable fun v : ℕ => ((3 : ℝ) ^ (-(1 - g))) ^ (v + 1) := by
    have := (summable_geometric_of_lt_one hr0.le hr1).mul_left
      ((3 : ℝ) ^ (-(1 - g)))
    refine this.congr fun v => ?_
    rw [pow_succ]
    ring
  have hB0 : (0 : ℝ) ≤ Cd * witnessEccentricity n := mul_nonneg hCd0 hecc0
  have hD0 : (0 : ℝ) < (3 : ℝ) ^ (-(D : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  -- OBLIGATION 4 : summability of the weighted row series
  have hprodSummable : Summable fun u : ℕ => wrow u * envu u := by
    rw [← summable_nat_add_iff (D + 1)]
    refine Summable.of_nonneg_of_le
      (fun v => mul_nonneg (hwrow0 _) (Real.rpow_nonneg (by norm_num) _))
      (fun v => ?_) ((hgeomS.mul_left ((Cd * witnessEccentricity n) *
        (3 : ℝ) ^ (-(D : ℝ)))))
    have henv : envu (v + (D + 1)) = (3 : ℝ) ^ (g * ((v : ℝ) + 1)) := by
      show (3 : ℝ) ^ (g * max (((v + (D + 1) : ℕ) : ℝ) - (D : ℝ)) 0) = _
      congr 1
      have hpos : (0 : ℝ) ≤ ((v + (D + 1) : ℕ) : ℝ) - (D : ℝ) := by
        push_cast
        linarith only [Nat.cast_nonneg (α := ℝ) v]
      rw [max_eq_left hpos]
      push_cast
      ring
    have hgrow : (0 : ℝ) ≤ (3 : ℝ) ^ (g * ((v : ℝ) + 1)) :=
      Real.rpow_nonneg (by norm_num) _
    have hsplit : (3 : ℝ) ^ (-((v : ℝ) + (D : ℝ) + 1)) =
        (3 : ℝ) ^ (-(D : ℝ)) * (3 : ℝ) ^ (-((v : ℝ) + 1)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    have hterm : ((3 : ℝ) ^ (-(1 - g))) ^ (v + 1) =
        (3 : ℝ) ^ (-((v : ℝ) + 1)) * (3 : ℝ) ^ (g * ((v : ℝ) + 1)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
        ← Real.rpow_natCast ((3 : ℝ) ^ (-(1 - g))) (v + 1),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      push_cast
      ring
    have hbase := hwrowDeep v
    rw [hsplit] at hbase
    calc
      wrow (v + (D + 1)) * envu (v + (D + 1)) =
          wrow (v + (D + 1)) * (3 : ℝ) ^ (g * ((v : ℝ) + 1)) := by rw [henv]
      _ ≤ ((Cd * witnessEccentricity n) *
            ((3 : ℝ) ^ (-(D : ℝ)) * (3 : ℝ) ^ (-((v : ℝ) + 1)))) *
          (3 : ℝ) ^ (g * ((v : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hbase hgrow
      _ = ((Cd * witnessEccentricity n) * (3 : ℝ) ^ (-(D : ℝ))) *
          ((3 : ℝ) ^ (-((v : ℝ) + 1)) * (3 : ℝ) ^ (g * ((v : ℝ) + 1))) := by
        ring
      _ = ((Cd * witnessEccentricity n) * (3 : ℝ) ^ (-(D : ℝ))) *
          ((3 : ℝ) ^ (-(1 - g))) ^ (v + 1) := by rw [hterm]
  -- OBLIGATION 5 : the per-row quadratic bound, with wrow kept explicit
  have hcastu : ∀ u : ℕ,
      (3 : ℝ) ^ (g * max ((r : ℝ) - ((r - (u : ℤ) : ℤ) : ℝ) - (D : ℝ)) 0) =
        envu u := by
    intro u
    show _ = (3 : ℝ) ^ (g * max ((u : ℝ) - (D : ℝ)) 0)
    have harg : (r : ℝ) - ((r - (u : ℤ) : ℤ) : ℝ) - (D : ℝ) =
        (u : ℝ) - (D : ℝ) := by
      push_cast
      ring
    rw [harg]
  have hrow : ∀ u : ℕ, (∑' w : {w // w ∈ Z (r - (u : ℤ))}, term ⟨u, w⟩) ≤
      (Y * eQuad) * (wrow u * envu u) := by
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
              (Y * envu u * eQuad) := by
        refine Finset.sum_le_sum fun w hw => ?_
        dsimp only [rowTerm]
        refine mul_le_mul_of_nonneg_left ?_
          (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
        calc
          1 / 2 * blockVecDot X
              (blockMatVecMul
                (coarseBlock (adaptedCellAt (1 : Mat d) (r - (u : ℤ)) w) a)
                X) =
              1 / 2 * blockVecDot X
                (blockMatVecMul
                  (coarseBlock (standardCell d (r - (u : ℤ)) w) a) X) := by
            rw [hidentity]
          _ ≤ 1 / 2 * blockVecDot X
              (blockMatVecMul
                (blockScale
                  (Y * (3 : ℝ) ^
                    (g * max ((r : ℝ) - ((r - (u : ℤ) : ℤ) : ℝ) -
                      (D : ℝ)) 0)) E) X) :=
            hstandard _ _ (by
              rw [← hidentity]
              exact hsub _ _ hw) X
          _ = Y * envu u * eQuad := by
            rw [Sharp.blockVecDot_blockMatVecMul_blockScale, hcastu u]
            dsimp only [eQuad]
            ring
      _ = (∑ w ∈ Z (r - (u : ℤ)),
            (volume (adaptedCellAt (1 : Mat d) (r - (u : ℤ)) w)).toReal /
              (volume (adaptedCellTranslate p r y)).toReal) *
          (Y * envu u * eQuad) := by rw [Finset.sum_mul]
      _ = (Y * eQuad) * (wrow u * envu u) := by
        have hwu : wrow u =
            ∑ w ∈ Z (r - (u : ℤ)),
              (volume (adaptedCellAt (1 : Mat d) (r - (u : ℤ)) w)).toReal /
                (volume (adaptedCellTranslate p r y)).toReal := rfl
        rw [hwu]
        ring
  -- OBLIGATION 6 : summability of the row sums
  have hrowSummable : Summable fun u : ℕ =>
      ∑' w : {w // w ∈ Z (r - (u : ℤ))}, term ⟨u, w⟩ :=
    Summable.of_nonneg_of_le
      (fun u => tsum_nonneg fun w => hterm0 ⟨u, w⟩) hrow
      (hprodSummable.mul_left _)
  -- OBLIGATION 7 : summability of the majorant
  have hmajSummable : Summable fun u : ℕ =>
      (Y * eQuad) * (wrow u * envu u) := hprodSummable.mul_left _
  -- OBLIGATION 7 : summability of term over the sigma index
  have htermSummable : Summable term :=
    (summable_sigma_of_nonneg hterm0).2
      ⟨fun _ => (hasSum_fintype _).summable, hrowSummable⟩
  have hsubadd := blockQuadratic_le_tsum_weight_of_countable_aePartition
    (Transport.isOpenBoundedConvexDomain_adaptedCellTranslate hp r y) hparent0 a
    hc hcsub hcpair hcnull hc0 X htermSummable
  have hYeQuad0 : (0 : ℝ) ≤ Y * eQuad := mul_nonneg hY heQuad0
  have hB0 : (0 : ℝ) ≤ Cd * witnessEccentricity n :=
    mul_nonneg hCd0 hecc0
  calc
    1 / 2 * blockVecDot X
        (blockMatVecMul (coarseBlock (adaptedCellTranslate p r y) a) X) ≤
        ∑' i : I, term i := hsubadd
    _ = ∑' u : ℕ, ∑' w : {w // w ∈ Z (r - (u : ℤ))}, term ⟨u, w⟩ :=
      htermSummable.tsum_sigma' (fun _ => (hasSum_fintype _).summable)
    _ ≤ ∑' u : ℕ, (Y * eQuad) * (wrow u * envu u) :=
      hrowSummable.tsum_le_tsum hrow hmajSummable
    _ = (Y * eQuad) * ∑' u : ℕ, (wrow u * envu u) := tsum_mul_left
    _ ≤ (Y * eQuad) *
        (1 + (Cd * witnessEccentricity n) * zetaG g *
          (3 : ℝ) ^ (-(D : ℤ))) :=
      mul_le_mul_of_nonneg_left
        (Quenched.tsum_burn_split_le hg.2 hB0 D hwrow0 hwrowSummable
          hwrowTotal hwrowDeep hprodSummable) hYeQuad0
    _ = 1 / 2 * blockVecDot X
        (blockMatVecMul
          (blockScale
            ((1 + Cd * witnessEccentricity n * zetaG g *
              (3 : ℝ) ^ (-(D : ℤ))) * Y) E) X) := by
      rw [Sharp.blockVecDot_blockMatVecMul_blockScale]
      dsimp only [eQuad]
      ring

end

end Window
end HighContrast
end HCPolySupport
