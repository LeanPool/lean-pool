/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Transport.FillingSubadditivity
public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneyRows
public import LeanPool.HighContrastHomogenization.Provider.Transport.WindowCellBounds

/-!
# High-contrast homogenization: Provider.Transport.FillingExhaustion

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The moving finite exhaustion of a target cell

`e.two.grid.whitney.average` is the display

`0 ≤ 𝐀(W) ≤ Σ_{r=j_*}^{j-λ_j} Σ_{V∈𝒱_r(W;q)} (|V|/|W|)𝐀(V) + G_W^{<j_*}`,

together with its adjoint version, for a target `W = z + ⋄_j^{q'}` filled by the
cells of the second grid `q` from the scale `n = j - λ_j` downwards.  The printed
proof continues the filling to a finite cutoff `J < j_*`, triangulates the
remaining set, and lets `J → -∞`; the right side is then the increasing limit of
the finite partial sums, the residual integral vanishing by absolute continuity.

Here the triangulation is bypassed, as it is for the geometry.  The residual of
the filling at the cutoff `J` is *not* decomposed: the sub-partition estimate of
`FillingSubadditivity` charges it to one constant, and `volume_residual_le` --
the residual volume of the Whitney selection, with its rate
`2d^{3/2}K_{hop}3^{J-j}` -- sends the weight in front of that constant to zero.
Two consequences are recorded.

*The finite exhaustion.*  At every cutoff `J ≤ n` the coarse response of the
target lies below the finite double sum over the rows `J ≤ r ≤ n` of the filling,
plus the printed residual rate times one constant independent of `J`.  This is
subadditivity over a finite Whitney exhaustion, with the residual left whole.

*The limit.*  Consequently the coarse response of the target lies below *any*
bound valid for every finite partial double sum.  That is the form
`e.two.grid.whitney.average` is consumed in: its right side is a sum of
nonnegative terms -- the rows from `j_*` to `n`, and the below-start series
`G_W^{<j_*}` of `e.two.grid.whitney.source` -- so it
dominates every finite partial sum, and no series has to be summed to apply it.

The rows of the truncated filling are gathered into one finite index set of
scale-centre pairs, the disjoint union over the scales of the rows themselves; no
new object is introduced for it.
-/

namespace HCPolySupport
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

section Exhaustion

variable {p q : Mat d} {n j : ℤ} {y : Vec d} {Z : ℤ → Finset (Fin d → ℤ)}

/-! ## The rows of a truncated filling as one finite family -/

private theorem mem_fillingIndex_of_mem
    (hZ : ∀ r, ↑(Z r) = fillingIndex q n (adaptedCellTranslate p j y) r) {r : ℤ}
    {w : Fin d → ℤ} (hw : w ∈ Z r) :
    w ∈ fillingIndex q n (adaptedCellTranslate p j y) r := by
  rw [← hZ r]
  exact Finset.mem_coe.mpr hw

private theorem mem_of_mem_fillingIndex
    (hZ : ∀ r, ↑(Z r) = fillingIndex q n (adaptedCellTranslate p j y) r) {r : ℤ}
    {w : Fin d → ℤ} (hw : w ∈ fillingIndex q n (adaptedCellTranslate p j y) r) :
    w ∈ Z r := by
  rw [← hZ r] at hw
  exact Finset.mem_coe.mp hw

private theorem mem_rows {J : ℤ} {i : ℤ × (Fin d → ℤ)} :
    i ∈ (Finset.Icc J n).biUnion
        (fun r => (Z r).image (Prod.mk r)) ↔
      i.1 ∈ Finset.Icc J n ∧ i.2 ∈ Z i.1 := by
  classical
  constructor
  · intro hi
    obtain ⟨r, hr, hi⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨hr, hw⟩
  · rintro ⟨h1, h2⟩
    exact Finset.mem_biUnion.mpr ⟨i.1, h1, Finset.mem_image.mpr ⟨i.2, h2, rfl⟩⟩

private theorem sum_rows {J : ℤ} (F : ℤ × (Fin d → ℤ) → ℝ) :
    ∑ i ∈ (Finset.Icc J n).biUnion
        (fun r => (Z r).image (Prod.mk r)), F i =
      ∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r, F (r, w) := by
  classical
  rw [Finset.sum_biUnion]
  · exact Finset.sum_congr rfl fun r _ =>
      Finset.sum_image fun _ _ _ _ h => congrArg Prod.snd h
  · intro r _ s _ hrs
    refine Finset.disjoint_left.mpr fun i hi hi' => hrs ?_
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hi'
    exact (congrArg Prod.fst hv).symm

private theorem iUnion_rows {J : ℤ}
    (hZ : ∀ r, ↑(Z r) = fillingIndex q n (adaptedCellTranslate p j y) r) :
    (⋃ i ∈ ((Finset.Icc J n).biUnion
        (fun r => (Z r).image (Prod.mk r)) :
          Finset (ℤ × (Fin d → ℤ))), adaptedCellAt q i.1 i.2) =
      ⋃ r ∈ Set.Icc J n, ⋃ w ∈ fillingIndex q n (adaptedCellTranslate p j y) r,
        adaptedCellAt q r w := by
  ext x
  simp only [Set.mem_iUnion, exists_prop, Set.mem_Icc]
  constructor
  · rintro ⟨i, hi, hx⟩
    obtain ⟨h1, h2⟩ := mem_rows.mp hi
    exact ⟨i.1, Finset.mem_Icc.mp h1, i.2, mem_fillingIndex_of_mem hZ h2, hx⟩
  · rintro ⟨r, hr, w, hw, hx⟩
    exact ⟨(r, w), mem_rows.mpr ⟨Finset.mem_Icc.mpr hr, mem_of_mem_fillingIndex hZ hw⟩, hx⟩

/-! ## The finite exhaustion at a cutoff -/

/-- **Subadditivity over a finite Whitney exhaustion, with the residual left
whole.**  At every cutoff `J ≤ n` the quadratic form of the coarse response of the
target is below the finite double sum over the rows of the filling, plus the
printed residual rate `2d^{3/2}|p^{-1}q|3^{J-j}` of the residual volume of the
Whitney selection times a single nonnegative constant that does not depend on the
cutoff.

That constant is the elliptic majorant of the response integrand together with the
affine term the incomplete weights leave behind; it is not exhibited, because the
rate annihilates it. -/
theorem exists_blockQuadratic_coarseBlock_le_filling_rows [NeZero d] (hp : p.PosDef)
    (hq : q.PosDef) (hZ : ∀ r, ↑(Z r) = fillingIndex q n (adaptedCellTranslate p j y) r)
    (a : CoeffSpace d) (X : BlockVec d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ J : ℤ, J ≤ n →
      1 / 2 * blockVecDot X
          (blockMatVecMul (coarseBlock (adaptedCellTranslate p j y) a) X) ≤
        (∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
            (volume (adaptedCellAt q r w)).toReal /
                (volume (adaptedCellTranslate p j y)).toReal *
              (1 / 2 * blockVecDot X
                (blockMatVecMul (coarseBlock (adaptedCellAt q r w) a) X))) +
          2 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ * (3 : ℝ) ^ (J - j) * K := by
  classical
  have hW : IsOpenBoundedConvexDomain (adaptedCellTranslate p j y) :=
    isOpenBoundedConvexDomain_adaptedCellTranslate hp j y
  obtain ⟨lam, Lam, f, _, _, hfm, hfell, hae⟩ :=
    exists_pointwise_elliptic_representative a.2 hW.isBoundedDomain.isBounded
  have hW0 : volume (adaptedCellTranslate p j y) ≠ 0 :=
    volume_adaptedCellTranslate_ne_zero hp j y
  have hWtop : volume (adaptedCellTranslate p j y) ≠ ⊤ :=
    volume_adaptedCellTranslate_ne_top p j y
  have hWpos : (0 : ℝ) < (volume (adaptedCellTranslate p j y)).toReal :=
    ENNReal.toReal_pos hW0 hWtop
  have hrep : ∀ V : Set (Vec d), coarseBlock V a = coarseBlockMatrix V f :=
    fun V => coarseBlock_eq_of_ae_eq a hae
  refine ⟨|lam⁻¹ * (Lam ^ 2 * vecNormSq X.1 + vecNormSq X.2) - vecDot X.1 X.2|,
    abs_nonneg _, fun J hJn => ?_⟩
  set S : Finset (ℤ × (Fin d → ℤ)) := (Finset.Icc J n).biUnion
    (fun r => (Z r).image (Prod.mk r)) with hS
  have hcells : ∀ i ∈ S, IsOpenBoundedConvexDomain (adaptedCellAt q i.1 i.2) :=
    fun i _ => Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq i.1 i.2
  have hmemS : ∀ i ∈ S, i.2 ∈ fillingIndex q n (adaptedCellTranslate p j y) i.1 := by
    intro i hi
    rw [hS] at hi
    exact mem_fillingIndex_of_mem hZ (mem_rows.mp hi).2
  have hsub : ∀ i ∈ S, adaptedCellAt q i.1 i.2 ⊆ adaptedCellTranslate p j y :=
    fun i hi => adaptedCellAt_subset_of_mem_fillingIndex (hmemS i hi)
  have hdisj : (↑S : Set (ℤ × (Fin d → ℤ))).PairwiseDisjoint
      fun i => adaptedCellAt q i.1 i.2 := fun i hi k hk hik =>
    disjoint_of_mem_fillingIndex hq (hmemS i (Finset.mem_coe.mp hi))
      (hmemS k (Finset.mem_coe.mp hk)) (by simpa using hik)
  have hcell0 : ∀ i ∈ S, volume (adaptedCellAt q i.1 i.2) ≠ 0 :=
    fun i _ => (Recurrence.volume_adaptedCellAt_pos hq i.1 i.2).ne'
  have hbase := blockQuadratic_le_sum_weight_add_residual (lam := lam) (Lam := Lam)
    (c := fun i : ℤ × (Fin d → ℤ) => adaptedCellAt q i.1 i.2) hW
    (Recurrence.isEllipticFieldOn_of_measurable hfm hfell hW.isOpen.measurableSet) hW0 hcells hsub
    hdisj hcell0 X
  -- the residual weight is below the printed rate
  have hrate : (0 : ℝ) ≤ 2 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ * (3 : ℝ) ^ (J - j) := by
    positivity
  have hres := volume_residual_le hp hq (n := n) (j := j) (J := J) hJn (y := y)
  rw [← iUnion_rows (J := J) hZ, ← hS] at hres
  have hresR : (volume (adaptedCellTranslate p j y \
        ⋃ i ∈ (↑S : Set (ℤ × (Fin d → ℤ))), adaptedCellAt q i.1 i.2)).toReal ≤
      2 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ * (3 : ℝ) ^ (J - j) *
        (volume (adaptedCellTranslate p j y)).toReal := by
    have hmono := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWtop) hres
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hrate] at hmono
  have hpay : (volume (adaptedCellTranslate p j y \
        ⋃ i ∈ (↑S : Set (ℤ × (Fin d → ℤ))), adaptedCellAt q i.1 i.2)).toReal /
          (volume (adaptedCellTranslate p j y)).toReal *
        (lam⁻¹ * (Lam ^ 2 * vecNormSq X.1 + vecNormSq X.2) - vecDot X.1 X.2) ≤
      2 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ * (3 : ℝ) ^ (J - j) *
        |lam⁻¹ * (Lam ^ 2 * vecNormSq X.1 + vecNormSq X.2) - vecDot X.1 X.2| := by
    refine le_trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)) ?_
    exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hWpos).mpr hresR) (abs_nonneg _)
  simp only [hrep]
  refine le_trans hbase (add_le_add (le_of_eq ?_) hpay)
  rw [hS]
  exact sum_rows fun i => (volume (adaptedCellAt q i.1 i.2)).toReal /
    (volume (adaptedCellTranslate p j y)).toReal *
      (1 / 2 * blockVecDot X (blockMatVecMul (coarseBlockMatrix (adaptedCellAt q i.1 i.2) f) X))

/-! ## The limit `J → -∞` -/

private theorem le_of_forall_geometric {x T C : ℝ}
    (h : ∀ m : ℕ, x ≤ T + C * (1 / 3 : ℝ) ^ m) : x ≤ T := by
  have hlim : Filter.Tendsto (fun m : ℕ => T + C * (1 / 3 : ℝ) ^ m)
      Filter.atTop (nhds T) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (by norm_num : (1 : ℝ) / 3 < 1)
    simpa using (hpow.const_mul C).const_add T
  exact ge_of_tendsto' hlim h

/-- **`e.two.grid.whitney.average`, the upper clause.**  If a real number
dominates every finite partial double sum of the filling's rows, then it dominates
the quadratic form of the coarse response of the target.

This is the limiting form of the exhaustion: the printed right side
`Σ_{r=j_*}^{n}Σ_V(|V|/|W|)𝐀(V) + G_W^{<j_*}` is a sum of nonnegative terms and
therefore dominates every finite partial sum, so it is admissible here.  No series
is summed and no triangulation of the residual is used; the residual is paid by
the residual volume of the Whitney selection alone. -/
theorem blockQuadratic_coarseBlock_le_of_forall_filling_rows [NeZero d] (hp : p.PosDef)
    (hq : q.PosDef) (hZ : ∀ r, ↑(Z r) = fillingIndex q n (adaptedCellTranslate p j y) r)
    (a : CoeffSpace d) (X : BlockVec d) {T : ℝ}
    (hT : ∀ J : ℤ, J ≤ n → (∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
        (volume (adaptedCellAt q r w)).toReal /
            (volume (adaptedCellTranslate p j y)).toReal *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (coarseBlock (adaptedCellAt q r w) a) X))) ≤ T) :
    1 / 2 * blockVecDot X
      (blockMatVecMul (coarseBlock (adaptedCellTranslate p j y) a) X) ≤ T := by
  obtain ⟨K, hK0, hKle⟩ := exists_blockQuadratic_coarseBlock_le_filling_rows hp hq hZ a X
  refine le_of_forall_geometric
    (C := 2 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ * (3 : ℝ) ^ (n - j) * K) fun m => ?_
  have hrate : 2 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ * (3 : ℝ) ^ (n - (m : ℤ) - j) * K =
      2 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ * (3 : ℝ) ^ (n - j) * K * (1 / 3 : ℝ) ^ m := by
    have hpow : (3 : ℝ) ^ (n - (m : ℤ) - j) = (3 : ℝ) ^ (n - j) * (1 / 3 : ℝ) ^ m := by
      rw [show n - (m : ℤ) - j = n - j + -(m : ℤ) by ring,
        zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_neg, one_div, inv_pow, zpow_natCast]
    rw [hpow]
    ring
  refine le_trans (hKle (n - (m : ℤ)) (by omega)) ?_
  rw [hrate]
  exact add_le_add (hT (n - (m : ℤ)) (by omega)) le_rfl

/-- **The adjoint half of `e.two.grid.whitney.average`.**  The sharp adjoint
response is the block reflection of the coarse response, and the reflection swaps
the halves of the doubled vector, so the same limiting exhaustion holds for
`𝐀_*^{-1}` with `G_{*,W}^{<j_*}` in place of `G_W^{<j_*}`. -/
theorem blockQuadratic_coarseStarInv_le_of_forall_filling_rows [NeZero d] (hp : p.PosDef)
    (hq : q.PosDef) (hZ : ∀ r, ↑(Z r) = fillingIndex q n (adaptedCellTranslate p j y) r)
    (a : CoeffSpace d) (X : BlockVec d) {T : ℝ}
    (hT : ∀ J : ℤ, J ≤ n → (∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
        (volume (adaptedCellAt q r w)).toReal /
            (volume (adaptedCellTranslate p j y)).toReal *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (coarseStarInv (adaptedCellAt q r w) a) X))) ≤ T) :
    1 / 2 * blockVecDot X
      (blockMatVecMul (coarseStarInv (adaptedCellTranslate p j y) a) X) ≤ T := by
  have hswap : ∀ V : Set (Vec d),
      blockVecDot X (blockMatVecMul (coarseStarInv V a) X) =
        blockVecDot ((X.2, X.1) : BlockVec d)
          (blockMatVecMul (coarseBlock V a) ((X.2, X.1) : BlockVec d)) := fun V =>
    blockVecDot_blockMatVecMul_blockReflect (coarseBlock V a) X
  simp only [hswap] at hT ⊢
  exact blockQuadratic_coarseBlock_le_of_forall_filling_rows hp hq hZ a _ hT

/-! ## The Loewner form, and the two clauses together -/

/-- **The coarse response of a target is positive semidefinite as a doubled
matrix**, the first clause of `e.two.grid.whitney.average` in the currency
the transport's matrix algebra works in. -/
theorem posSemidef_toFullBlockMat_coarseBlock [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hU0 : volume U ≠ 0) (a : CoeffSpace d) :
    (toFullBlockMat (coarseBlock U a)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (isHermitian_toFullBlockMat (isSymmetricBlockMat_coarseBlock U a)) fun x => ?_
  have h := zero_le_blockQuadratic_coarseBlock hU hU0 a (ofFullBlockVec x)
  rw [blockVecDot_blockMatVecMul_eq_dotProduct, toFullBlockVec_ofFullBlockVec] at h
  simp only [star_trivial]
  linarith only [h]

/-- **`e.two.grid.whitney.average`**, both clauses, in both orientations and
in the Loewner order of the doubled matrices: the coarse response of the target is
positive, and it is below every symmetric block whose quadratic form dominates all
the finite partial double sums of the filling's rows.

The printed right side `Σ_{r=j_*}^{n}Σ_V(|V|/|W|)𝐀(V) + G_W^{<j_*}` is such a
block: every one of its terms is a positive multiple of a coarse response, hence
positive, so its quadratic form dominates each partial sum. -/
theorem grid_transport_exhaustion [NeZero d] (hp : p.PosDef) (hq : q.PosDef)
    (hZ : ∀ r, ↑(Z r) = fillingIndex q n (adaptedCellTranslate p j y) r)
    (a : CoeffSpace d) {B Bstar : BlockMat d} (hB : IsSymmetricBlockMat B)
    (hBstar : IsSymmetricBlockMat Bstar)
    (hT : ∀ (X : BlockVec d) (J : ℤ), J ≤ n → (∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
        (volume (adaptedCellAt q r w)).toReal /
            (volume (adaptedCellTranslate p j y)).toReal *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (coarseBlock (adaptedCellAt q r w) a) X))) ≤
      1 / 2 * blockVecDot X (blockMatVecMul B X))
    (hTstar : ∀ (X : BlockVec d) (J : ℤ), J ≤ n → (∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
        (volume (adaptedCellAt q r w)).toReal /
            (volume (adaptedCellTranslate p j y)).toReal *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (coarseStarInv (adaptedCellAt q r w) a) X))) ≤
      1 / 2 * blockVecDot X (blockMatVecMul Bstar X)) :
    (toFullBlockMat (coarseBlock (adaptedCellTranslate p j y) a)).PosSemidef ∧
      toFullBlockMat (coarseBlock (adaptedCellTranslate p j y) a) ≤ toFullBlockMat B ∧
        toFullBlockMat (coarseStarInv (adaptedCellTranslate p j y) a) ≤
          toFullBlockMat Bstar :=
  ⟨posSemidef_toFullBlockMat_coarseBlock
      (isOpenBoundedConvexDomain_adaptedCellTranslate hp j y)
      (volume_adaptedCellTranslate_ne_zero hp j y) a,
    le_of_blockMatLoewnerLE (isSymmetricBlockMat_coarseBlock _ a) hB fun X =>
      blockQuadratic_coarseBlock_le_of_forall_filling_rows hp hq hZ a X (hT X),
    le_of_blockMatLoewnerLE (isSymmetricBlockMat_coarseStarInv _ a) hBstar fun X =>
      blockQuadratic_coarseStarInv_le_of_forall_filling_rows hp hq hZ a X (hTstar X)⟩

end Exhaustion

end

end Transport
end HighContrast
end HCPolySupport
