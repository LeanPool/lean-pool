/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastIsotropyPack
public import LeanPool.HighContrastHomogenization.Provider.Window.BurnSplitStandardToAdapted

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastBurnSplitMaximumEnvelope

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The maximal envelope at a dimension-only constant

The parametrized diagonal-weak maximum bound reads the source envelope on adapted
cells through the fixed-level Whitney bridge, so its normalizing constant
carries the boundary constant `C_d 𝔢 ζ_g` of the cell conversion and the
enlargement factor `3^{gG}` of the containment.  The printed conversion
(Lemma 2.13 of HC, whose conclusion is (2.124)) carries neither: it splits
the Whitney rows at a burn depth and absorbs the geometry
into a scale restriction, as HC (2.123) records.

The input the printed conversion uses is not the all-scale bound of
`e.coarse.ellipticity` but its mesoscale improvement (Lemma 2.8 of HC,
conclusion (2.91)): at burn depth `h` the standard-cube envelope is the
*truncated* `3^{g(m-h-k)_+}`, whose localizing cube `□_m` sits `h` scales
above the envelope's own base.
That gap is what buys the flat band, and this module is the chain over it.

At depth `2D` the adapted-cell envelope becomes `(1 + C_d 𝔢 ζ_g 3^{-D})`
times the truncated `3^{g(m-D-k)_+}`, and once the depth absorbs the
geometry — `boundaryConst ≤ 3^D`, the Lean form of HC (2.123) — the
`ρ`-weighted maximal function of the aligned cells obeys the printed envelope
`(max 1 (3·𝒮·3^{-(t+D)}))^g` with the normalizing constant `4/γ`: dimensional,
with the aspect ratio riding only in the enlargement `D` and hence in a scale
threshold.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- **The adapted-cell envelope at the burn split.**  The mesoscale envelope at
depth `2D` gives every aligned adapted cell of the fixed grid contained in the
cube of scale `m` the coarse-block bound
`(1 + C_d 𝔢 ζ_g 3^{-D})·3^{g(m-D-k)_+}·E`, with the geometry on `3^{-D}`
instead of multiplying. -/
theorem coarseBlock_adaptedCell_burnsplit_le_of_mesoEnvelope
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} {E : BlockMat d}
    (hE : Book.Ch02.BlockPosDef E)
    {Sh : CoeffSpace d → ℝ} {D : ℕ}
    (hmeso : ∀ᵐ a ∂P, ∀ m : ℤ, Sh a ≤ (3 : ℝ) ^ m → ∀ k : ℤ, k ≤ m →
      ∀ w : Fin d → ℤ, standardCellCenter k w ∈ centeredCube d m →
        BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
          (blockScale
            ((3 : ℝ) ^ (g * max ((m : ℝ) - 2 * (D : ℝ) - (k : ℝ)) 0)) E))
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {n : Mat d} (hn : n.PosDef) :
    ∀ᵐ a ∂P, ∀ m : ℤ, Sh a ≤ (3 : ℝ) ^ m →
      ∀ (k : ℤ) (w : Fin d → ℤ),
        adaptedCellAt (roundedGrid l n) k w ⊆ centeredCube d m →
        BlockMatLoewnerLE
          (coarseBlock (adaptedCellAt (roundedGrid l n) k w) a)
          (blockScale
            ((1 + Cd * witnessEccentricity n * zetaG g * (3 : ℝ) ^ (-(D : ℤ))) *
              (3 : ℝ) ^ (g * max ((m : ℝ) - (D : ℝ) - (k : ℝ)) 0)) E) := by
  filter_upwards [hmeso] with a hbound
  intro m hm k w hsub
  have hd0 : 0 < d := by omega
  rw [adaptedCellAt_eq_adaptedCellTranslate]
  rw [adaptedCellAt_eq_adaptedCellTranslate] at hsub
  refine Window.adapted_burnsplit_of_standard hd hg hl hCd hn hE
    (Real.rpow_nonneg (by norm_num) _) D k
    (adaptedCellCenter (roundedGrid l n) k w) ?_
  intro k' w' hsub'
  have hstdcube : standardCell d k' w' ⊆ centeredCube d m :=
    hsub'.trans hsub
  have hk'm : k' ≤ m :=
    Window.scale_le_of_standardCell_subset_centeredCube hd0 hstdcube
  have hcenter : standardCellCenter k' w' ∈ centeredCube d m :=
    hstdcube (Recurrence.standardCellCenter_mem_standardCell k' w')
  have hbase := hbound m hm k' hk'm w' hcenter
  refine BlockMatLoewnerLE.trans hbase ?_
  refine blockMatLoewnerLE_blockScale_of_scalar_le ?_ hE
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hsplit : max ((m : ℝ) - 2 * (D : ℝ) - (k' : ℝ)) 0 ≤
      max ((m : ℝ) - (D : ℝ) - (k : ℝ)) 0 +
        max ((k : ℝ) - (k' : ℝ) - (D : ℝ)) 0 := by
    refine max_le ?_ (add_nonneg (le_max_right _ _) (le_max_right _ _))
    have h1 := le_max_left ((m : ℝ) - (D : ℝ) - (k : ℝ)) 0
    have h2 := le_max_left ((k : ℝ) - (k' : ℝ) - (D : ℝ)) 0
    linarith only [h1, h2]
  calc g * max ((m : ℝ) - 2 * (D : ℝ) - (k' : ℝ)) 0 ≤
      g * (max ((m : ℝ) - (D : ℝ) - (k : ℝ)) 0 +
        max ((k : ℝ) - (k' : ℝ) - (D : ℝ)) 0) :=
        mul_le_mul_of_nonneg_left hsplit hg.1
    _ = g * max ((m : ℝ) - (D : ℝ) - (k : ℝ)) 0 +
        g * max ((k : ℝ) - (k' : ℝ) - (D : ℝ)) 0 := by ring

/-- The domination hypothesis in the form the excess step consumes. -/
private theorem le_blockScale_inv_of_dominates' {E F : BlockMat d} {gam : ℝ}
    (hgam : 0 < gam) (hFE : BlockMatLoewnerLE (blockScale gam E) F) :
    BlockMatLoewnerLE E (blockScale gam⁻¹ F) := by
  intro X
  have h := hFE X
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at h
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale]
  have hstep : gam * blockVecDot X (blockMatVecMul E X) ≤
      blockVecDot X (blockMatVecMul F X) := by linarith only [h]
  have hmul := mul_le_mul_of_nonneg_left hstep (inv_nonneg.mpr hgam.le)
  rw [← mul_assoc, inv_mul_cancel₀ hgam.ne', one_mul] at hmul
  linarith only [hmul]

/-- **The weak maximum at a dimension-only normalizer.**  With the burn depth
absorbing the geometry (`boundaryConst Cd g n ≤ 3^D`, the Lean form of
HC (2.123)), the `ρ`-weighted maximal function of the aligned cells
obeys the printed envelope with normalizing constant `4/γ`. -/
theorem diagonalWeakMaximum_burnsplit_parametrized_le [NeZero d]
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} {E : BlockMat d}
    (hE : Book.Ch02.BlockPosDef E)
    {Sh : CoeffSpace d → ℝ} {D : ℕ}
    (hmeso : ∀ᵐ a ∂P, ∀ m : ℤ, Sh a ≤ (3 : ℝ) ^ m → ∀ k : ℤ, k ≤ m →
      ∀ w : Fin d → ℤ, standardCellCenter k w ∈ centeredCube d m →
        BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
          (blockScale
            ((3 : ℝ) ^ (g * max ((m : ℝ) - 2 * (D : ℝ) - (k : ℝ)) 0)) E))
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {n : Mat d} (hn : n.PosDef)
    (hD : boundaryConst Cd g n ≤ (3 : ℝ) ^ D)
    {rho : ℝ} (hrho : g ≤ rho) (t : ℤ)
    (hgeom : ∀ k : ℤ, k ≤ t →
      ∀ w ∈ Response.alignedIndex (roundedGrid l n) k t,
        adaptedCellAt (roundedGrid l n) k w ⊆
          centeredCube d (t + (D : ℤ)))
    {F : BlockMat d} (hFsym : IsSymmetricBlockMat F) (hFpd : BlockPosDef F)
    {gam : ℝ} (hgam : 0 < gam)
    (hFE : BlockMatLoewnerLE (blockScale gam E) F) :
    ∀ᵐ a ∂P,
      Response.diagonalWeakMaximum rho (roundedGrid l n) t F a ≤
        ENNReal.ofReal
          (4 / gam *
            ((max 1 (3 * Sh a * (3 : ℝ) ^ (-((t : ℝ) + (D : ℝ))))) ^ g / 2)) := by
  have hCd1 : (1 : ℝ) ≤ Cd := (le_max_left _ _).trans hCd
  have hbC0 : 0 < boundaryConst Cd g n :=
    Transport.zero_lt_boundaryConst (by linarith only [hCd1]) hg.2 hn
  have h3D : (0 : ℝ) < (3 : ℝ) ^ (-(D : ℤ)) := zpow_pos (by norm_num) _
  have hCDle : Cd * witnessEccentricity n * zetaG g * (3 : ℝ) ^ (-(D : ℤ)) ≤ 1 := by
    have hstep := mul_le_mul_of_nonneg_right hD h3D.le
    rw [← zpow_natCast (3 : ℝ) D, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)] at hstep
    rw [boundaryConst] at hstep
    simpa using hstep
  have hCD0 : (0 : ℝ) ≤
      Cd * witnessEccentricity n * zetaG g * (3 : ℝ) ^ (-(D : ℤ)) := by
    have hb : (0 : ℝ) ≤ Cd * witnessEccentricity n * zetaG g := by
      rw [← boundaryConst]
      exact hbC0.le
    exact mul_nonneg hb h3D.le
  have hcomp : BlockMatLoewnerLE E (blockScale gam⁻¹ F) :=
    le_blockScale_inv_of_dominates' hgam hFE
  have hR0 : (0 : ℝ) ≤ 4 / gam := div_nonneg (by norm_num) hgam.le
  have hgaminv : (0 : ℝ) ≤ gam⁻¹ := inv_nonneg.mpr hgam.le
  filter_upwards [coarseBlock_adaptedCell_burnsplit_le_of_mesoEnvelope
    hd hg hE hmeso hl hCd hn] with a henv
  have hcore : ∀ m : ℤ, t + (D : ℤ) ≤ m → Sh a ≤ (3 : ℝ) ^ m →
      Response.diagonalWeakMaximum rho (roundedGrid l n) t F a ≤
      ENNReal.ofReal
        (4 / gam *
          ((3 : ℝ) ^ (g * ((m : ℝ) - (t : ℝ) - (D : ℝ))) / 2)) := by
    intro m hmge hmS
    refine iSup_le fun k => iSup_le fun hk => iSup_le fun w =>
      iSup_le fun hw => ?_
    have hsub : adaptedCellAt (roundedGrid l n) k w ⊆ centeredCube d m :=
      (hgeom k hk w hw).trans (Window.centeredCube_mono hmge)
    have hcell := henv m hmS k w hsub
    have hsym : IsSymmetricBlockMat (adaptedResponse (roundedGrid l n) k w a) := by
      rw [adaptedResponse]
      exact isSymmetricBlockMat_coarseBlock _ _
    have hq : (roundedGrid l n).PosDef := Recurrence.posDef_roundedGrid hl hn
    have hpd : BlockPosDef (adaptedResponse (roundedGrid l n) k w a) := by
      rw [adaptedResponse]
      exact Recurrence.blockPosDef_coarseBlock_adaptedCellAt hq k w a
    have hcellR : BlockMatLoewnerLE
        (adaptedResponse (roundedGrid l n) k w a)
        (blockScale
          ((1 + Cd * witnessEccentricity n * zetaG g * (3 : ℝ) ^ (-(D : ℤ))) *
            (3 : ℝ) ^ (g * max ((m : ℝ) - (D : ℝ) - (k : ℝ)) 0)) E) := by
      rw [adaptedResponse]
      exact hcell
    have hscal0 : (0 : ℝ) ≤
        (1 + Cd * witnessEccentricity n * zetaG g * (3 : ℝ) ^ (-(D : ℤ))) *
          (3 : ℝ) ^ (g * max ((m : ℝ) - (D : ℝ) - (k : ℝ)) 0) :=
      mul_nonneg (by linarith only [hCD0])
        (Real.rpow_nonneg (by norm_num) _)
    have hexc := blockExcess_le_of_blockMatLoewnerLE hsym
      (posDef_toFullBlockMat hsym hpd).posSemidef hFsym hFpd
      hscal0 hgaminv hcellR hcomp
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have hweight0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-rho * ((t : ℝ) - (k : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    have hkt : (k : ℝ) ≤ (t : ℝ) := by exact_mod_cast hk
    have hmt : (t : ℝ) + (D : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmge
    have hmaxeq : max ((m : ℝ) - (D : ℝ) - (k : ℝ)) 0 =
        (m : ℝ) - (D : ℝ) - (k : ℝ) :=
      max_eq_left (by linarith only [hkt, hmt])
    have hexpo : -rho * ((t : ℝ) - (k : ℝ)) +
        g * ((m : ℝ) - (D : ℝ) - (k : ℝ)) ≤
        g * ((m : ℝ) - (t : ℝ) - (D : ℝ)) := by
      have hprod : 0 ≤ (rho - g) * ((t : ℝ) - (k : ℝ)) :=
        mul_nonneg (sub_nonneg.mpr hrho) (sub_nonneg.mpr hkt)
      nlinarith only [hprod]
    calc
      (3 : ℝ) ^ (-rho * ((t : ℝ) - (k : ℝ))) *
          blockExcess (adaptedResponse (roundedGrid l n) k w a) F ≤
          (3 : ℝ) ^ (-rho * ((t : ℝ) - (k : ℝ))) *
            ((1 + Cd * witnessEccentricity n * zetaG g *
                (3 : ℝ) ^ (-(D : ℤ))) *
              (3 : ℝ) ^ (g * max ((m : ℝ) - (D : ℝ) - (k : ℝ)) 0) * gam⁻¹) :=
        mul_le_mul_of_nonneg_left hexc hweight0
      _ = (1 + Cd * witnessEccentricity n * zetaG g *
              (3 : ℝ) ^ (-(D : ℤ))) * gam⁻¹ *
            (3 : ℝ) ^ (-rho * ((t : ℝ) - (k : ℝ)) +
              g * ((m : ℝ) - (D : ℝ) - (k : ℝ))) := by
        rw [hmaxeq, Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        ring
      _ ≤ (1 + Cd * witnessEccentricity n * zetaG g *
              (3 : ℝ) ^ (-(D : ℤ))) * gam⁻¹ *
            (3 : ℝ) ^ (g * ((m : ℝ) - (t : ℝ) - (D : ℝ))) := by
        refine mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexpo) ?_
        exact mul_nonneg (by linarith only [hCD0]) hgaminv
      _ ≤ 2 * gam⁻¹ * (3 : ℝ) ^ (g * ((m : ℝ) - (t : ℝ) - (D : ℝ))) := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith only [hCDle]) hgaminv)
          (Real.rpow_nonneg (by norm_num) _)
      _ = 4 / gam * ((3 : ℝ) ^ (g * ((m : ℝ) - (t : ℝ) - (D : ℝ))) / 2) := by
        field_simp
        ring
  by_cases hS : Sh a ≤ (3 : ℝ) ^ (t + (D : ℤ))
  · refine le_trans (hcore (t + (D : ℤ)) le_rfl hS) ?_
    refine ENNReal.ofReal_le_ofReal ?_
    refine mul_le_mul_of_nonneg_left ?_ hR0
    have hzero : g * (((t + (D : ℤ) : ℤ) : ℝ) - (t : ℝ) - (D : ℝ)) = 0 := by
      push_cast
      ring
    rw [hzero, Real.rpow_zero]
    have h1 := Real.one_le_rpow
      (le_max_left 1 (3 * Sh a * (3 : ℝ) ^ (-((t : ℝ) + (D : ℝ))))) hg.1
    linarith only [h1]
  · push Not at hS
    have hS0 : 0 < Sh a := lt_trans (zpow_pos (by norm_num) _) hS
    set m : ℤ := ⌈Real.logb 3 (Sh a)⌉ with hmdef
    have hlogS : ((t + (D : ℤ) : ℤ) : ℝ) < Real.logb 3 (Sh a) := by
      rw [Real.lt_logb_iff_rpow_lt (by norm_num) hS0]
      rw [← Real.rpow_intCast (3 : ℝ) (t + (D : ℤ))] at hS
      exact hS
    have hm1 : t + (D : ℤ) ≤ m := by
      have h := le_trans hlogS.le (Int.le_ceil (Real.logb 3 (Sh a)))
      rw [hmdef]
      exact_mod_cast h
    have hm2 : Sh a ≤ (3 : ℝ) ^ m := by
      have h1 : Sh a = (3 : ℝ) ^ Real.logb 3 (Sh a) :=
        (Real.rpow_logb (by norm_num) (by norm_num) hS0).symm
      rw [h1, ← Real.rpow_intCast (3 : ℝ) m]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (hmdef ▸ Int.le_ceil _)
    refine le_trans (hcore m hm1 hm2) (ENNReal.ofReal_le_ofReal ?_)
    refine mul_le_mul_of_nonneg_left ?_ hR0
    refine (div_le_div_iff_of_pos_right (by norm_num)).2 ?_
    have hup : (m : ℝ) - (t : ℝ) - (D : ℝ) ≤
        Real.logb 3 (Sh a) + 1 - (t : ℝ) - (D : ℝ) := by
      have hlt := Int.ceil_lt_add_one (Real.logb 3 (Sh a))
      have hcast : (m : ℝ) < Real.logb 3 (Sh a) + 1 := by
        rw [hmdef]
        exact_mod_cast hlt
      linarith only [hcast]
    calc
      (3 : ℝ) ^ (g * ((m : ℝ) - (t : ℝ) - (D : ℝ))) ≤
          (3 : ℝ) ^ (g * (Real.logb 3 (Sh a) + 1 - (t : ℝ) - (D : ℝ))) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        exact mul_le_mul_of_nonneg_left hup hg.1
      _ = ((3 : ℝ) ^ (Real.logb 3 (Sh a) + 1 - (t : ℝ) - (D : ℝ))) ^ g := by
        rw [mul_comm g, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      _ = (3 * Sh a * (3 : ℝ) ^ (-((t : ℝ) + (D : ℝ)))) ^ g := by
        congr 1
        rw [show Real.logb 3 (Sh a) + 1 - (t : ℝ) - (D : ℝ) =
            Real.logb 3 (Sh a) + (1 + (-((t : ℝ) + (D : ℝ)))) from by ring,
          Real.rpow_add (by norm_num : (0 : ℝ) < 3),
          Real.rpow_add (by norm_num : (0 : ℝ) < 3),
          Real.rpow_logb (by norm_num) (by norm_num) hS0,
          Real.rpow_one]
        ring
      _ ≤ (max 1 (3 * Sh a * (3 : ℝ) ^ (-((t : ℝ) + (D : ℝ))))) ^ g := by
        refine Real.rpow_le_rpow ?_ (le_max_right _ _) hg.1
        positivity

/-- **The maximal envelope at the isotropy block, with no reference ratio.**
The burn-split chain read at `isotropyReference cIso 𝐄`: the normalizing
constant is `4/(1+cIso)`, and neither the boundary constant nor the enlargement
factor appears. -/
theorem henvMax_burnsplit_of_isotropyReference [NeZero d]
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} {E : BlockMat d}
    (hEsym : IsSymmetricBlockMat E) (hE : Book.Ch02.BlockPosDef E)
    {Sh : CoeffSpace d → ℝ} {D : ℕ}
    (hmeso : ∀ᵐ a ∂P, ∀ m : ℤ, Sh a ≤ (3 : ℝ) ^ m → ∀ k : ℤ, k ≤ m →
      ∀ w : Fin d → ℤ, standardCellCenter k w ∈ centeredCube d m →
        BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
          (blockScale
            ((3 : ℝ) ^ (g * max ((m : ℝ) - 2 * (D : ℝ) - (k : ℝ)) 0)) E))
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {nu : Mat d} (hnu : nu.PosDef)
    (hD : boundaryConst Cd g nu ≤ (3 : ℝ) ^ D)
    {rho : ℝ} (hrho : g ≤ rho) (t : ℤ)
    (hgeom : ∀ k : ℤ, k ≤ t →
      ∀ w ∈ Response.alignedIndex (roundedGrid l nu) k t,
        adaptedCellAt (roundedGrid l nu) k w ⊆
          centeredCube d (t + (D : ℤ)))
    {cIso : ℝ} (hcIso : 0 ≤ cIso) :
    ∀ᵐ a ∂P,
      Response.diagonalWeakMaximum rho (roundedGrid l nu) t
          (isotropyReference cIso E) a ≤
        ENNReal.ofReal
          (4 / (1 + cIso) *
            ((max 1 (3 * Sh a * (3 : ℝ) ^ (-((t : ℝ) + (D : ℝ))))) ^ g / 2)) := by
  have hpos : (0 : ℝ) < 1 + cIso := by linarith only [hcIso]
  refine diagonalWeakMaximum_burnsplit_parametrized_le hd hg hE hmeso hl hCd hnu
    hD hrho t hgeom
    (isSymmetricBlockMat_isotropyReference cIso hEsym)
    (blockPosDef_isotropyReference hcIso hE) hpos ?_
  rw [isotropyReference_eq_blockScale]
  intro X
  exact le_rfl

end

end HCPolySupport.HighContrast.Quenched
