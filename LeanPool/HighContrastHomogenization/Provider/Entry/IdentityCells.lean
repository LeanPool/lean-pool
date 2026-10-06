/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Entry.EuclideanAdapter
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.MeanOrder
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.CellMuMeasurability

/-!
# High-contrast homogenization: Provider.Entry.IdentityCells

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The identity grid at nonnegative alignment

The comparison between adapted and Euclidean cubes compares the adapted grid
with the Euclidean one, and the Euclidean grid is the identity witness.  Two
facts about that witness are needed at every nonnegative generation, below the
rounding scale `k_0(d)` as well as above it.

*The cells.*  The aligned cells of the identity grid are the standard aligned
cubes and its cell at the origin is the centered triadic cube, so the
cross-grid filling of `l.two.grid.whitney` reads on Euclidean
cubes without any translation of dialect.

*The alignment.*  `IsRoundedGrid` carries the rounding threshold `k_0(d)`
because the rounding of a general witness is only faithful above it.  For the
identity witness the aligned-subdivision property of the coarse block — that a
scale-`j` translation vector is integral — is the statement `3^j ℤ^d ⊆ ℤ^d`,
true at every `j ≥ 0`.  The aligned subdivision and the annealed mean order of
`p.fixed.geometry.parent.child.recurrence` therefore hold on the centered cubes from
generation zero up, which is the range the persistence transfer's consumer
obligation quantifies over.

Every standard aligned cube is moreover an integer translate of one whose center
lies in the unit cube: at a nonnegative generation the center is itself
integral, and at a negative one the index reduces modulo `3^{-k}`.  This is what
lets integer stationarity be applied to the boundary layers of the comparison at
every generation, however deep.

There are no definitions in this file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Entry

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The cells of the identity grid -/

/-- The aligned center of the identity grid is the center of the standard
aligned cube. -/
theorem adaptedCellCenter_one (k : ℤ) (w : Fin d → ℤ) :
    adaptedCellCenter (1 : Mat d) k w = standardCellCenter k w := by
  rw [Recurrence.adaptedCellCenter_eq, matVecMul_one]

/-- The aligned cell of the identity grid is the standard aligned cube. -/
theorem adaptedCellAt_one (k : ℤ) (w : Fin d → ℤ) :
    adaptedCellAt (1 : Mat d) k w = standardCell d k w := by
  rw [Recurrence.adaptedCellAt_eq_image]
  have h : matVecMul (1 : Mat d) = id := funext fun x => matVecMul_one x
  rw [h, Set.image_id]

/-- The untranslated cell of the identity grid is the centered triadic cube. -/
theorem adaptedCellTranslate_one_zero (j : ℤ) :
    adaptedCellTranslate (1 : Mat d) j 0 = centeredCube d j := by
  rw [adaptedCellTranslate, Initialization.adaptedCell_one]
  simp

/-! ## Reduction of a standard aligned cube to the unit cube -/

/-- A standard aligned cube is the integer translate of a second one as soon as
their centers differ by the integer vector. -/
theorem standardCell_eq_translateSet {k : ℤ} {w u v : Fin d → ℤ}
    (h : ∀ i, (w i : ℝ) * (3 : ℝ) ^ k = (u i : ℝ) + (v i : ℝ) * (3 : ℝ) ^ k) :
    standardCell d k w = translateSet (Source.AKL.intTranslation u) (standardCell d k v) := by
  have hlo : ∀ i, ((w i : ℝ) - 1 / 2) * (3 : ℝ) ^ k
      = (u i : ℝ) + ((v i : ℝ) - 1 / 2) * (3 : ℝ) ^ k := by
    intro i
    rw [sub_mul, sub_mul, h i]
    ring
  have hhi : ∀ i, ((w i : ℝ) + 1 / 2) * (3 : ℝ) ^ k
      = (u i : ℝ) + ((v i : ℝ) + 1 / 2) * (3 : ℝ) ^ k := by
    intro i
    rw [add_mul, add_mul, h i]
    ring
  ext x
  rw [mem_translateSet_iff_sub_mem, Recurrence.mem_standardCell_iff,
    Recurrence.mem_standardCell_iff]
  have hsub : ∀ i, (x - Source.AKL.intTranslation u) i = x i - (u i : ℝ) := fun _ => rfl
  constructor
  · intro hx i
    rw [hsub i]
    constructor
    · linarith only [(hx i).1, hlo i]
    · linarith only [(hx i).2, hhi i]
  · intro hx i
    have hxi := hx i
    rw [hsub i] at hxi
    constructor
    · linarith only [hxi.1, hlo i]
    · linarith only [hxi.2, hhi i]

/-- **Every standard aligned cube is an integer translate of one centered in the
unit cube.**  At a nonnegative generation the cube is an integer translate of the
centered cube; at a negative one its index reduces modulo `3^{-k}`, and the
reduced center lies in `[0,1)^d`. -/
theorem exists_reduced_standardCell (k : ℤ) (w : Fin d → ℤ) :
    ∃ u v : Fin d → ℤ,
      standardCell d k w = translateSet (Source.AKL.intTranslation u) (standardCell d k v) ∧
        ∀ i, |standardCellCenter k v i| < 1 := by
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    refine ⟨fun i => (3 : ℤ) ^ n * w i, 0, standardCell_eq_translateSet ?_, ?_⟩
    · intro i
      simp only [Pi.zero_apply, Int.cast_zero, zero_mul, add_zero, Int.cast_mul,
        Int.cast_pow, Int.cast_ofNat, zpow_natCast]
      ring
    · intro i
      simp only [standardCellCenter, Pi.zero_apply, Int.cast_zero, mul_zero, abs_zero]
      norm_num
  · obtain ⟨p, hp⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ -k by omega)
    have hkp : k = -(p : ℤ) := by omega
    subst hkp
    have hNpos : (0 : ℤ) < (3 : ℤ) ^ p := by positivity
    have hNreal : (((3 : ℤ) ^ p : ℤ) : ℝ) = (3 : ℝ) ^ ((p : ℤ)) := by
      push_cast
      rw [zpow_natCast]
    refine ⟨fun i => w i / (3 : ℤ) ^ p, fun i => w i % (3 : ℤ) ^ p,
      standardCell_eq_translateSet ?_, ?_⟩
    · intro i
      have hdiv : (3 : ℤ) ^ p * (w i / (3 : ℤ) ^ p) + w i % (3 : ℤ) ^ p = w i := by
        rw [add_comm]
        exact Int.emod_add_mul_ediv _ _
      have hcast : (((3 : ℤ) ^ p : ℤ) : ℝ) * ((w i / (3 : ℤ) ^ p : ℤ) : ℝ)
          + ((w i % (3 : ℤ) ^ p : ℤ) : ℝ) = (w i : ℝ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hdiv
      have hunit : (3 : ℝ) ^ ((p : ℤ)) * (3 : ℝ) ^ (-(p : ℤ)) = 1 := by
        rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), add_neg_cancel, zpow_zero]
      rw [← hcast, hNreal]
      linear_combination (((w i / (3 : ℤ) ^ p : ℤ) : ℝ)) * hunit
    · intro i
      have hlo : (0 : ℤ) ≤ w i % (3 : ℤ) ^ p := Int.emod_nonneg _ (by positivity)
      have hhi : w i % (3 : ℤ) ^ p < (3 : ℤ) ^ p := Int.emod_lt_of_pos _ hNpos
      have hloR : (0 : ℝ) ≤ ((w i % (3 : ℤ) ^ p : ℤ) : ℝ) := by exact_mod_cast hlo
      have hhiR : ((w i % (3 : ℤ) ^ p : ℤ) : ℝ) < (3 : ℝ) ^ ((p : ℤ)) := by
        rw [← hNreal]
        exact_mod_cast hhi
      have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(p : ℤ)) := by positivity
      have hunit : (3 : ℝ) ^ (-(p : ℤ)) * (3 : ℝ) ^ ((p : ℤ)) = 1 := by
        rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), neg_add_cancel, zpow_zero]
      show |(3 : ℝ) ^ (-(p : ℤ)) * ((w i % (3 : ℤ) ^ p : ℤ) : ℝ)| < 1
      rw [abs_of_nonneg (by positivity)]
      nlinarith only [hloR, hhiR, h3, hunit]

/-! ## The aligned subdivision of the identity grid at nonnegative alignment -/

/-- **The alignment clause at the identity grid.**  A scale-`j` translation
vector of the identity grid is integral at every `j ≥ 0`: this is
`3^j ℤ^d ⊆ ℤ^d`, and it needs no rounding threshold. -/
theorem exists_intVec_adaptedCellCenter_one {j : ℤ} (hj : 0 ≤ j) (w : Fin d → ℤ) :
    ∃ v : Fin d → ℤ, adaptedCellCenter (1 : Mat d) j w = fun i => (v i : ℝ) := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
  refine ⟨fun i => (3 : ℤ) ^ n * w i, ?_⟩
  funext i
  rw [adaptedCellCenter_one]
  simp only [standardCellCenter, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, zpow_natCast]

/-- The aligned cells of the identity grid at a nonnegative generation are
integer translates of the centered cube. -/
theorem adaptedCellAt_one_eq_translateSet {j : ℤ} (hj : 0 ≤ j) (w : Fin d → ℤ) :
    ∃ v : Fin d → ℤ,
      adaptedCellAt (1 : Mat d) j w = translateSet (Source.AKL.intTranslation v) (centeredCube d
        j) := by
  obtain ⟨v, hv⟩ := exists_intVec_adaptedCellCenter_one hj w
  exact ⟨v, by rw [Recurrence.adaptedCellAt_eq_translateSet_intVec hv,
    Initialization.adaptedCell_one]⟩

/-- The annealed block of an aligned identity cell at a nonnegative generation is
the Euclidean mean at that generation. -/
theorem annealedBlock_adaptedCellAt_one {P : Measure (CoeffSpace d)}
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {j : ℤ} (hj : 0 ≤ j) (w : Fin d → ℤ) :
    annealedBlock P (adaptedCellAt (1 : Mat d) j w) = annealedBlock P (centeredCube d j) := by
  obtain ⟨v, hv⟩ := adaptedCellAt_one_eq_translateSet hj w
  rw [hv]
  exact Recurrence.annealedBlock_translateSet hstat (hasMeasurableCoarseBlock_centeredCube P j) v

/-- The finiteness of the Euclidean mean transports to every aligned identity
cell at a nonnegative generation. -/
theorem hasIntegrableCoarseBlock_adaptedCellAt_one {P : Measure (CoeffSpace d)}
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {j : ℤ} (hj : 0 ≤ j)
    (hint : HasIntegrableCoarseBlock P (centeredCube d j)) (w : Fin d → ℤ) :
    HasIntegrableCoarseBlock P (adaptedCellAt (1 : Mat d) j w) := by
  obtain ⟨v, hv⟩ := adaptedCellAt_one_eq_translateSet hj w
  rw [hv]
  exact Recurrence.hasIntegrableCoarseBlock_translateSet hstat hint v

/-- **The annealed mean order of `p.fixed.geometry.parent.child.recurrence` on
the Euclidean cubes, from generation zero up.**  The averaging step of the recurrence needs the
rounding threshold only to know that the children's translation vectors are
integral; at the identity witness they are integral from generation zero, so the
order `F_p ≤ F_j` holds on the whole nonnegative range. -/
theorem annealedBlock_centeredCube_le_of_nonneg [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ} (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) {j p : ℤ}
    (hj : 0 ≤ j) (hjp : j ≤ p) :
    BlockMatLoewnerLE (annealedBlock P (centeredCube d p))
      (annealedBlock P (centeredCube d j)) := by
  classical
  have hone : (1 : Mat d).PosDef := Matrix.PosDef.one
  have hintj : HasIntegrableCoarseBlock P (centeredCube d j) :=
    hasIntegrableCoarseBlock_of_coarseEllipticityDagger hdag j
  have hintp : HasIntegrableCoarseBlock P (centeredCube d p) :=
    hasIntegrableCoarseBlock_of_coarseEllipticityDagger hdag p
  obtain ⟨Z, hZ, hcard⟩ := Recurrence.exists_finset_adaptedCellCenter_mem hone hjp
  have hZne : Z.Nonempty := by
    rw [← Finset.card_pos, hcard]
    positivity
  have hcell : ∀ w ∈ Z, HasIntegrableCoarseBlock P (adaptedCellAt (1 : Mat d) j w) :=
    fun w _ => hasIntegrableCoarseBlock_adaptedCellAt_one hstat hj hintj w
  have hterm : ∀ w ∈ Z,
      Integrable (fun a => toFullBlockMat (coarseBlock (adaptedCellAt (1 : Mat d) j w) a)) P :=
    fun w hw => integrable_toFullBlockMat (hcell w hw)
  have hsum : Integrable
      (fun a => ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt (1 : Mat d) j w) a)) P := by
    refine integrable_of_entries fun p q => ?_
    simp only [Matrix.sum_apply, toFullBlockMat_eq_blockMatEntry]
    exact integrable_finsetSum Z (fun w hw => hcell w hw p q)
  have hgint : Integrable
      (fun a => (Z.card : ℝ)⁻¹ •
        ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt (1 : Mat d) j w) a)) P := by
    refine integrable_of_entries fun p q => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, toFullBlockMat_eq_blockMatEntry]
    exact (integrable_finsetSum Z (fun w hw => hcell w hw p q)).const_mul _
  have hle : ∀ a : CoeffSpace d,
      toFullBlockMat (coarseBlock (adaptedCell (1 : Mat d) p) a) ≤
        (Z.card : ℝ)⁻¹ •
          ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt (1 : Mat d) j w) a) :=
    fun a => Recurrence.toFullBlockMat_coarseBlock_adaptedCell_le_average hone hjp hZ a
  have hintp' : HasIntegrableCoarseBlock P (adaptedCell (1 : Mat d) p) := by
    rw [Initialization.adaptedCell_one]; exact hintp
  have hmono := integral_mono' (integrable_toFullBlockMat hintp') hgint
    (Filter.Eventually.of_forall hle)
  have hcardpos : (0 : ℝ) < (Z.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hZne
  have hval : ∀ w ∈ Z,
      ∫ a, toFullBlockMat (coarseBlock (adaptedCellAt (1 : Mat d) j w) a) ∂P =
        toFullBlockMat (annealedBlock P (centeredCube d j)) := by
    intro w hw
    rw [← toFullBlockMat_annealedBlock (hcell w hw), annealedBlock_adaptedCellAt_one hstat hj w]
  have haver : ∫ a, (Z.card : ℝ)⁻¹ •
      ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt (1 : Mat d) j w) a) ∂P =
        toFullBlockMat (annealedBlock P (centeredCube d j)) := by
    ext p q
    have hlhs : (∫ a, (Z.card : ℝ)⁻¹ •
        ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt (1 : Mat d) j w) a) ∂P) p q =
          ∫ a, (Z.card : ℝ)⁻¹ *
            ∑ w ∈ Z, blockMatEntry (coarseBlock (adaptedCellAt (1 : Mat d) j w) a) p q ∂P := by
      rw [entry_integral hgint p q]
      refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, toFullBlockMat_eq_blockMatEntry]
    have hentry : ∀ w ∈ Z,
        ∫ a, blockMatEntry (coarseBlock (adaptedCellAt (1 : Mat d) j w) a) p q ∂P =
          blockMatEntry (annealedBlock P (centeredCube d j)) p q := by
      intro w hw
      have h := (entry_integral (hterm w hw) p q).symm.trans
        (congrFun (congrFun (hval w hw) p) q)
      simpa only [toFullBlockMat_eq_blockMatEntry] using h
    rw [hlhs, integral_const_mul, integral_finsetSum Z (fun w hw => hcell w hw p q),
      Finset.sum_congr rfl hentry, Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hcardpos.ne', one_mul, toFullBlockMat_eq_blockMatEntry]
  rw [haver, Initialization.adaptedCell_one] at hmono
  refine blockMatLoewnerLE_of_le ?_
  rw [toFullBlockMat_annealedBlock hintp]
  exact hmono

/-- **The Euclidean mean order at an arbitrary aligned center.**  Every standard
aligned cube of a generation at or above `k ≥ 0` has annealed block below the
Euclidean mean `F_k`: integer stationarity moves the cube to the origin, and the
alignment-zero mean order compares the generations.  This is the bound the layers
at or above the comparison generation consume. -/
theorem annealedBlock_standardCell_le_centeredCube [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ} (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) {k r : ℤ} (hk : 0 ≤ k)
    (hkr : k ≤ r) (w : Fin d → ℤ) :
    BlockMatLoewnerLE (annealedBlock P (standardCell d r w))
      (annealedBlock P (centeredCube d k)) := by
  have h1 : annealedBlock P (standardCell d r w) = annealedBlock P (centeredCube d r) := by
    rw [← adaptedCellAt_one]
    exact annealedBlock_adaptedCellAt_one hstat (le_trans hk hkr) w
  rw [h1]
  exact annealedBlock_centeredCube_le_of_nonneg hstat hdag hk hkr

end

end Entry
end HighContrast
end HCPolySupport
