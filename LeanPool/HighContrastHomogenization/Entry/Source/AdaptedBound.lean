/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.AdaptedLocality
public import LeanPool.HighContrastHomogenization.Entry.Source.Multiplier
public import LeanPool.HighContrastHomogenization.Entry.Geometry.RoundedGridBasic
public import LeanPool.HighContrastHomogenization.Entry.Source.Subdivision
public import LeanPool.HighContrastHomogenization.Entry.Source.CoarseSubadditivity
public import LeanPool.HighContrastHomogenization.Provider.Window.CellGeometry

/-!
# High-contrast homogenization: Entry.Source.AdaptedBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# From a successful source depth to adapted bounds

Near `l.source.whitney`. Dagger is used on a single event simultaneously
for every integer source translate. Finer standard cells are assigned to their aligned
ancestor, and coarser cells use the actual standard subdivision and source subadditivity.
-/

open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (CoeffSpace blockScale coarseBlock translateCoeff)
open HCPolySupport.HighContrast (adaptedCellTranslate centeredCube standardCell
  standardCellCenter)
namespace HCPolySupport.HighContrast.Source
open Set MeasureTheory Filter Geometry
open scoped Matrix.Norms.L2Operator
noncomputable section

/-- At a successful source offset, dagger controls every finer standard cell in the
original window on the one simultaneous integer-translation event. -/
theorem source_finer_standard_bound {d : ℕ} (γ : ℝ) (E : BlockMat d)
    (S : CoeffSpace d → ℝ) (a : CoeffSpace d) (jStar r : ℕ)
    (hcoarse : ∀ z : Fin d → ℤ, ∀ m : ℤ, S (translateCoeff z a) ≤ (3 : ℝ) ^ m →
      ∀ k : ℤ, k ≤ m → ∀ w : Fin d → ℤ,
        standardCellCenter k w ∈ centeredCube d m →
        BlockMatLoewnerLE (coarseBlock (standardCell d k w) (translateCoeff z a))
          (blockScale ((3 : ℝ) ^ (γ * ((m : ℝ) - (k : ℝ)))) E))
    (hsuccess : ∀ v : Fin d → ℤ,
      standardCellCenter ((jStar + r : ℕ) : ℤ) v ∈
        centeredCube d ((2 * jStar + r : ℕ) : ℤ) →
      S (translateCoeff (fun i => (3 : ℤ) ^ (jStar + r) * v i) a) ≤
        (3 : ℝ) ^ (jStar + r))
    (k : ℤ) (w : Fin d → ℤ) (hkm : k ≤ (jStar + r : ℕ))
    (hcell : standardCell d k w ⊆ centeredCube d (2 * (jStar : ℤ))) :
    BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
      (blockScale ((3 : ℝ) ^ (γ * (((jStar + r : ℕ) : ℝ) - (k : ℝ)))) E) := by
  let m : ℤ := (jStar + r : ℕ)
  obtain ⟨v, hv⟩ := exists_standardCell_ancestor hkm w
  have hcenter := hv (Recurrence.standardCellCenter_mem_standardCell k w)
  have hbig : standardCell d m v ⊆ centeredCube d ((2 * jStar + r : ℕ) : ℤ) := by
    have hpoint := (Window.centeredCube_mono (d := d)
      (show 2 * (jStar : ℤ) ≤ ((2 * jStar + r : ℕ) : ℤ) by omega))
      (hcell (Recurrence.standardCellCenter_mem_standardCell k w))
    rw [centeredCube_eq_standardCell] at hpoint ⊢
    exact standardCell_subset_of_mem (by dsimp [m]; omega) hcenter hpoint
  have hs := hsuccess v (hbig (Recurrence.standardCellCenter_mem_standardCell m v))
  let n : ℕ := (m - k).toNat
  have hkn : k + (n : ℤ) = m := by
    dsimp [n]
    rw [Int.toNat_of_nonneg (by exact sub_nonneg.mpr hkm)]
    omega
  let u : Fin d → ℤ := fun i => w i - (3 : ℤ) ^ n * v i
  have hp : (3 : ℝ) ^ m = (3 : ℝ) ^ k * (3 : ℝ) ^ n := by
    rw [← hkn, zpow_add₀ (by norm_num), zpow_natCast]
  have hrel (i : Fin d) : standardCellCenter k u i =
      standardCellCenter k w i - standardCellCenter m v i := by
    simp only [standardCellCenter, u, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, hp]
    ring
  have hu : standardCellCenter k u ∈ centeredCube d m := by
    rw [Recurrence.mem_centeredCube_iff]
    rw [Recurrence.mem_standardCell_iff] at hcenter
    change ∀ i, ((v i : ℝ) - 1 / 2) * (3 : ℝ) ^ m < standardCellCenter k w i ∧
      standardCellCenter k w i < ((v i : ℝ) + 1 / 2) * (3 : ℝ) ^ m at hcenter
    intro i
    rw [hrel]
    dsimp only [standardCellCenter] at hcenter ⊢
    constructor <;> linarith only [(hcenter i).1, (hcenter i).2]
  have htranslate : translateSet (standardCellCenter m v) (standardCell d k u) = standardCell d
    k w := by
    simpa only [hkn, u, sub_add_cancel] using translate_standardCell_by_coarser_center k n v u
  have hb := hcoarse (fun i => (3 : ℤ) ^ (jStar + r) * v i) m
    (by simpa only [m, zpow_natCast] using hs) k hkm u hu
  rw [coarseBlock_translateCoeff_eq_translateSet, intTranslation_sourceCenter, htranslate] at hb
  simpa only [m, Int.cast_natCast] using hb

/-- Standard-cell subdivision extends the successful-depth estimate to every generation,
including coarser cells, with the printed positive part and no geometric factor. -/
theorem source_standard_bound {d : ℕ} [NeZero d] (γ : ℝ) (E : BlockMat d)
    (S : CoeffSpace d → ℝ) (a : CoeffSpace d) (jStar r : ℕ)
    (hcoarse : ∀ z : Fin d → ℤ, ∀ m : ℤ, S (translateCoeff z a) ≤ (3 : ℝ) ^ m →
      ∀ k : ℤ, k ≤ m → ∀ w : Fin d → ℤ,
        standardCellCenter k w ∈ centeredCube d m →
        BlockMatLoewnerLE (coarseBlock (standardCell d k w) (translateCoeff z a))
          (blockScale ((3 : ℝ) ^ (γ * ((m : ℝ) - (k : ℝ)))) E))
    (hsuccess : ∀ v : Fin d → ℤ,
      standardCellCenter ((jStar + r : ℕ) : ℤ) v ∈
        centeredCube d ((2 * jStar + r : ℕ) : ℤ) →
      S (translateCoeff (fun i => (3 : ℤ) ^ (jStar + r) * v i) a) ≤
        (3 : ℝ) ^ (jStar + r))
    (k : ℤ) (w : Fin d → ℤ)
    (hcell : standardCell d k w ⊆ centeredCube d (2 * (jStar : ℤ))) :
    BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
      (blockScale ((3 : ℝ) ^ (γ * max (((jStar + r : ℕ) : ℝ) - (k : ℝ)) 0)) E) := by
  by_cases hkm : k ≤ ((jStar + r : ℕ) : ℤ)
  · have hkmR : 0 ≤ ((jStar + r : ℕ) : ℝ) - (k : ℝ) := by
      have hh : (k : ℝ) ≤ ((jStar + r : ℕ) : ℝ) := by exact_mod_cast hkm
      linarith only [hh]
    rw [max_eq_left hkmR]
    exact source_finer_standard_bound γ E S a jStar r hcoarse hsuccess k w hkm hcell
  have hmk : ((jStar + r : ℕ) : ℤ) ≤ k := le_of_lt (lt_of_not_ge hkm)
  have hmkR : ((jStar + r : ℕ) : ℝ) - (k : ℝ) ≤ 0 := by
    have hh : ((jStar + r : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
    linarith only [hh]
  rw [max_eq_right hmkR, mul_zero, Real.rpow_zero]
  let m : ℤ := (jStar + r : ℕ)
  let W : Set (Vec d) := standardCell d k w
  let U : (Fin d → ℤ) → Set (Vec d) := fun u => standardCell d m u
  let s : Set (Fin d → ℤ) := {u | U u ⊆ W}
  have hs : s.Countable := Set.to_countable _
  have hsub : ∀ u ∈ s, U u ⊆ W := fun _ hu => hu
  have hdisj : s.PairwiseDisjoint U := fun _ _ _ _ hne => standardCell_disjoint_of_ne m hne
  have hnull : volume (W \ ⋃ u ∈ s, U u) = 0 := by
    simpa only [iUnion_subtype] using standardCell_subdivision_null hmk w
  have hWfin : volume W ≠ ⊤ := volume_standardCell_ne_top k w
  let : IsFiniteMeasure (volumeMeasureOn W) := ⟨by simpa [volumeMeasureOn] using hWfin.lt_top⟩
  have hWvol : (volume W).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨(volume_standardCell_pos k w).ne', hWfin⟩
  have hc : Summable (fun u : s => (volume (U u)).toReal / (volume W).toReal * (1 : ℝ)) := by
    simpa only [mul_one] using summable_volumeRatio
      (fun u _ => measurableSet_standardCell m u) hsub hdisj
  have hweights : (∑' u : s, (volume (U u)).toReal / (volume W).toReal * (1 : ℝ)) = 1 := by
    simpa only [mul_one] using tsum_volumeRatio_eq_one hs hWvol
      (fun u _ => measurableSet_standardCell m u) hsub hdisj hnull
  have hb : ∀ u ∈ s, BlockMatLoewnerLE (coarseBlock (U u) a) (blockScale 1 E) := by
    intro u hu
    have ht := source_finer_standard_bound γ E S a jStar r hcoarse hsuccess m u le_rfl (hu.trans
      hcell)
    simpa only [m, Int.cast_natCast, sub_self, mul_zero, Real.rpow_zero] using ht
  have hresult := coarseBlock_adapted_partition_bound hs (1 : Mat d) isUnit_one k
    (standardCellCenter k w) (fun _ => (1 : Mat d)) (fun _ _ => isUnit_one)
    (fun _ => m) (standardCellCenter m) a E (fun _ => 1)
  simp only [← standardCell_eq_adapted_identity] at hresult
  have hfinal := hresult hsub hdisj hnull hc hb
  dsimp only [U, W] at hweights
  simpa only [hweights] using hfinal

/-- The positive-part source penalty combines with boundary-layer decay geometrically. -/
theorem source_penalty_decay (γ J j r : ℝ) (hγ : 0 ≤ γ) (hr : r ≤ j) :
    (3 : ℝ) ^ (r - j) * (3 : ℝ) ^ (γ * max (J - r) 0) ≤
      (3 : ℝ) ^ (γ * max (J - j) 0) * (3 : ℝ) ^ ((1 - γ) * (r - j)) := by
  have hm : max (J - r) 0 ≤ max (J - j) 0 + (j - r) := by
    apply max_le
    · linarith only [le_max_left (J - j) 0]
    · linarith only [le_max_right (J - j) 0, hr]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith only [mul_le_mul_of_nonneg_left hm hγ]

/-- The full Whitney series has a summable source penalty, with the exact geometric
ratio. Reindexing by the nonnegative deficit retains every selected cell. -/
theorem source_whitney_weighted_sum {d : ℕ} [NeZero d]
    {q : Mat d} (hq : InverseNormLE q 2) (j : ℤ) (y : Vec d)
    (J : ℕ) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    let W := adaptedCellTranslate q j y
    let s := maximalCellPairs W j
    Summable (fun t : s => (volume (standardCell d t.1.1 t.1.2)).toReal / (volume W).toReal *
      (3 : ℝ) ^ (γ * max ((J : ℝ) - (t.1.1 : ℝ)) 0)) ∧
    (∑' t : s, (volume (standardCell d t.1.1 t.1.2)).toReal / (volume W).toReal *
      (3 : ℝ) ^ (γ * max ((J : ℝ) - (t.1.1 : ℝ)) 0)) ≤
      12 * (d : ℝ) ^ ((3 : ℝ) / 2) * (3 : ℝ) ^ (γ * max ((J : ℝ) - (j : ℝ)) 0) /
        (1 - (3 : ℝ) ^ (-(1 - γ))) := by
  classical
  intro W s
  let f : s → ℝ := fun t => (volume (standardCell d t.1.1 t.1.2)).toReal / (volume W).toReal *
    (3 : ℝ) ^ (γ * max ((J : ℝ) - (t.1.1 : ℝ)) 0)
  let deficit : s → ℕ := fun t => (j - t.1.1).toNat
  let F : ℕ → Set s := fun n => {t | deficit t = n}
  let D : ℝ := 12 * (d : ℝ) ^ ((3 : ℝ) / 2) * (3 : ℝ) ^ (γ * max ((J : ℝ) - (j : ℝ)) 0)
  let ρ : ℝ := (3 : ℝ) ^ (-(1 - γ))
  have hf0 (t : s) : 0 ≤ f t := by dsimp [f]; positivity
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hγ.2])
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hgeom : Summable (fun n : ℕ => D * ρ ^ n) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left D
  have hgen (t : s) (n : ℕ) (ht : deficit t = n) : t.1.1 = j - (n : ℤ) := by
    have ht0 : 0 ≤ j - t.1.1 := sub_nonneg.mpr t.2.le
    have hh : ((j - t.1.1).toNat : ℤ) = (n : ℤ) := by exact_mod_cast ht
    rw [Int.toNat_of_nonneg ht0] at hh
    omega
  have hrows (n : ℕ) : Summable (fun t : F n => f t) ∧ (∑' t : F n, f t) ≤ D * ρ ^ n := by
    let r : ℤ := j - n
    obtain ⟨hfin, hrow⟩ := (source_whitney hq j y).2.2.2 r (by dsimp [r]; omega)
    let := hfin.fintype
    let e : F n ≃ maximalCellIndices W j r :=
      { toFun := fun t => ⟨t.1.1.2, by
          have ht := t.1.2
          change IsMaximalCellIn W j t.1.1.1 t.1.1.2 at ht
          rw [hgen t.1 n t.2] at ht
          exact ht⟩
        invFun := fun w => ⟨⟨(r, w.1), w.2⟩, by simp [F, deficit, r]⟩
        left_inv := by
          intro t
          apply Subtype.ext
          apply Subtype.ext
          apply Prod.ext
          · exact (hgen t.1 n t.2).symm
          · rfl
        right_inv := fun _ => rfl }
    let : Fintype (F n) := Fintype.ofEquiv (maximalCellIndices W j r) e.symm
    refine ⟨(hasSum_fintype _).summable, ?_⟩
    have heq : (∑' t : F n, f t) =
        (∑ w ∈ hfin.toFinset, (volume (standardCell d r w)).toReal / (volume W).toReal) *
          (3 : ℝ) ^ (γ * max ((J : ℝ) - (r : ℝ)) 0) := by
      rw [← e.symm.tsum_eq]
      change (∑' w : maximalCellIndices W j r,
        (volume (standardCell d r w)).toReal / (volume W).toReal *
          (3 : ℝ) ^ (γ * max ((J : ℝ) - (r : ℝ)) 0)) = _
      rw [tsum_mul_right]
      congr 1
      have hh := Finset.tsum_subtype hfin.toFinset
        (fun w => (volume (standardCell d r w)).toReal / (volume W).toReal)
      let e' : maximalCellIndices W j r ≃ {x // x ∈ hfin.toFinset} :=
        Equiv.subtypeEquivRight (fun _ => by simp [W])
      exact (e'.tsum_eq (fun w => (volume (standardCell d r w)).toReal /
        (volume W).toReal)).trans hh
    rw [heq]
    calc
      _ ≤ (12 * (d : ℝ) ^ ((3 : ℝ) / 2) * (3 : ℝ) ^ (r - j)) *
          (3 : ℝ) ^ (γ * max ((J : ℝ) - (r : ℝ)) 0) := by gcongr
      _ ≤ (12 * (d : ℝ) ^ ((3 : ℝ) / 2)) *
          ((3 : ℝ) ^ (γ * max ((J : ℝ) - (j : ℝ)) 0) * (3 : ℝ) ^ ((1 - γ) * ((r : ℝ) - (j :
            ℝ)))) := by
        rw [mul_assoc, ← Real.rpow_intCast, Int.cast_sub]
        exact mul_le_mul_of_nonneg_left
          (source_penalty_decay γ J j r hγ.1 (by
            dsimp [r]
            push_cast
            linarith only [Nat.cast_nonneg (α := ℝ) n])) (by positivity)
      _ = D * ρ ^ n := by
        simp only [D, ρ, r, Int.cast_sub, Int.cast_natCast, ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
        rw [show (1 - γ) * (((j : ℝ) - (n : ℝ)) - (j : ℝ)) =
          -(1 - γ) * (n : ℝ) by ring]
        ring
  have hpart : ∀ t : s, ∃! n, t ∈ F n := by
    intro t
    exact ⟨deficit t, rfl, fun _ h => h.symm⟩
  have hsumrows : Summable (fun n => ∑' t : F n, f t) :=
    Summable.of_nonneg_of_le (fun n => tsum_nonneg (fun t => hf0 t)) (fun n => (hrows n).2) hgeom
  have hsum : Summable f := (summable_partition hf0 hpart).2 ⟨fun n => (hrows n).1, hsumrows⟩
  refine ⟨hsum, ?_⟩
  have hgroup := hsum.hasSum.tsum_fiberwise deficit
  have htotal : (∑' t : s, f t) = ∑' n, ∑' t : F n, f t := hgroup.tsum_eq.symm
  change (∑' t : s, f t) ≤ _
  rw [htotal]
  calc
    _ ≤ ∑' n, D * ρ ^ n := hsumrows.tsum_le_tsum (fun n => (hrows n).2) hgeom
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]; rfl

/-- Separating the least offset retains the factor-one standard bound at every
integer scale, including scales below the source window. -/
theorem source_penalty_factor (γ : ℝ) (hγ : 0 ≤ γ) (J r : ℕ) (k : ℤ) :
    (3 : ℝ) ^ (γ * max (((J + r : ℕ) : ℝ) - (k : ℝ)) 0) ≤
      (3 : ℝ) ^ (γ * (r : ℝ)) * (3 : ℝ) ^ (γ * max ((J : ℝ) - (k : ℝ)) 0) := by
  have hm : max (((J + r : ℕ) : ℝ) - (k : ℝ)) 0 ≤
      (r : ℝ) + max ((J : ℝ) - (k : ℝ)) 0 := by
    push_cast
    apply max_le
    · linarith only [le_max_left ((J : ℝ) - (k : ℝ)) 0]
    · positivity
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith only [mul_le_mul_of_nonneg_left hm hγ]

/-- One simultaneous standard bound controls every contained adapted cell.
The full countable partition is assembled through the mixed response identity. -/
theorem adapted_bound_of_standard {d : ℕ} [NeZero d]
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (E : BlockMat d)
    (hE : Book.Ch02.BlockPosDef E) (a : CoeffSpace d) (J : ℕ) (X : ℝ) (hX : 0 ≤ X)
    (hstd : ∀ (k : ℤ) (w : Fin d → ℤ),
      standardCell d k w ⊆ centeredCube d (2 * (J : ℤ)) →
      BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
        (blockScale (X * (3 : ℝ) ^ (γ * max ((J : ℝ) - (k : ℝ)) 0)) E))
    {q : Mat d} (hq : InverseNormLE q 2) (j : ℤ) (y : Vec d)
    (hcell : adaptedCellTranslate q j y ⊆ centeredCube d (2 * (J : ℤ))) :
    BlockMatLoewnerLE (coarseBlock (adaptedCellTranslate q j y) a)
      (blockScale ((12 * (d : ℝ) ^ ((3 : ℝ) / 2) / (1 - (3 : ℝ) ^ (-(1 - γ)))) *
        X * (3 : ℝ) ^ (γ * max ((J : ℝ) - (j : ℝ)) 0)) E) := by
  classical
  let W := adaptedCellTranslate q j y
  let s := maximalCellPairs W j
  let c : ℤ × (Fin d → ℤ) → ℝ := fun t => X * (3 : ℝ) ^ (γ * max ((J : ℝ) - (t.1 : ℝ)) 0)
  obtain ⟨hsub, hdisj, hnull, _⟩ := source_whitney hq j y
  obtain ⟨hsum, hbound⟩ := source_whitney_weighted_sum hq j y J γ hγ
  have hs : Summable (fun t : s =>
      (volume (standardCell d t.1.1 t.1.2)).toReal / (volume W).toReal * c t) := by
    simpa only [c, mul_left_comm] using hsum.mul_left X
  have hb := coarseBlock_adapted_partition_bound (Set.to_countable s) q hq.isUnit j y
    (fun _ => (1 : Mat d)) (fun _ _ => isUnit_one)
    (fun t => t.1) (fun t => standardCellCenter t.1 t.2) a E c
  simp only [← standardCell_eq_adapted_identity] at hb
  have hb' := hb hsub hdisj hnull hs (fun t ht => hstd t.1 t.2 ((hsub t ht).trans hcell))
  have hscalar : (∑' t : s,
      (volume (standardCell d t.1.1 t.1.2)).toReal / (volume W).toReal * c t) ≤
      (12 * (d : ℝ) ^ ((3 : ℝ) / 2) / (1 - (3 : ℝ) ^ (-(1 - γ)))) *
        X * (3 : ℝ) ^ (γ * max ((J : ℝ) - (j : ℝ)) 0) := by
    simp only [c, mul_left_comm]
    rw [tsum_mul_left]
    calc
      _ ≤ X * (12 * (d : ℝ) ^ ((3 : ℝ) / 2) *
          (3 : ℝ) ^ (γ * max ((J : ℝ) - (j : ℝ)) 0) /
          (1 - (3 : ℝ) ^ (-(1 - γ)))) := mul_le_mul_of_nonneg_left hbound hX
      _ = _ := by ring
  exact fun v => (hb' v).trans ((blockScale_le_blockScale_of_pos hE hscalar) v)

/-- The same attained source value gives the printed factor-one standard-cell estimate. -/
theorem source_standard_multiplier_bound {d : ℕ} [NeZero d] (γ : ℝ) (E : BlockMat d)
    (hγ : 0 ≤ γ) (hE : Book.Ch02.BlockPosDef E)
    (S : CoeffSpace d → ℝ) (a : CoeffSpace d) (jStar r : ℕ)
    (hcoarse : ∀ z : Fin d → ℤ, ∀ m : ℤ, S (translateCoeff z a) ≤ (3 : ℝ) ^ m →
      ∀ k : ℤ, k ≤ m → ∀ w : Fin d → ℤ,
        standardCellCenter k w ∈ centeredCube d m →
        BlockMatLoewnerLE (coarseBlock (standardCell d k w) (translateCoeff z a))
          (blockScale ((3 : ℝ) ^ (γ * ((m : ℝ) - (k : ℝ)))) E))
    (hsuccess : ∀ v : Fin d → ℤ,
      standardCellCenter ((jStar + r : ℕ) : ℤ) v ∈
        centeredCube d ((2 * jStar + r : ℕ) : ℤ) →
      S (translateCoeff (fun i => (3 : ℤ) ^ (jStar + r) * v i) a) ≤
        (3 : ℝ) ^ (jStar + r))
    (k : ℤ) (w : Fin d → ℤ)
    (hcell : standardCell d k w ⊆ centeredCube d (2 * (jStar : ℤ))) :
    BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
      (blockScale ((3 : ℝ) ^ (γ * (r : ℝ)) *
        (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (k : ℝ)) 0)) E) := by
  have hb := source_standard_bound γ E S a jStar r hcoarse hsuccess k w hcell
  have hm := blockScale_le_blockScale_of_pos hE (source_penalty_factor γ hγ jStar r k)
  exact fun v => (hb v).trans (hm v)

/-- The printed eccentricity is at least one for a positive metric in nonzero dimension. -/
theorem one_le_source_eccentricity {d : ℕ} [NeZero d] {m : Mat d} (hm : m.PosDef) :
    1 ≤ Real.sqrt (‖m‖ * ‖m⁻¹‖) := by
  have hv : (fun _ : Fin d => (1 : ℝ)) ≠ 0 := by
    intro h
    have hh := congrFun h ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
    norm_num at hh
  have h := one_le_opNorm_mul_opNorm_inv hm hv
  exact (Real.le_sqrt (by norm_num) (by positivity)).2 (by simpa using h)

/-- The characterized source multiplier, its fixed-Q norm, and one simultaneous
standard/adapted event. Both constants are chosen before all source laws and data. -/
theorem source_multiplier_and_adapted_bound (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc C : ℝ, 0 < Csrc ∧ 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          let Good : ℕ → CoeffSpace d → Prop := fun r a =>
            ∀ w : Fin d → ℤ,
              standardCellCenter ((jStar + r : ℕ) : ℤ) w ∈
                centeredCube d ((2 * jStar + r : ℕ) : ℤ) →
              S (translateCoeff (fun i => (3 : ℤ) ^ (jStar + r) * w i) a) ≤
                (3 : ℝ) ^ (jStar + r)
          ∃ (ell : CoeffSpace d → ℕ) (X : CoeffSpace d → ℝ),
            Measurable ell ∧ Measurable X ∧
            (∀ a, X a = (3 : ℝ) ^ (γ * (ell a : ℝ))) ∧
            (∀ᵐ a ∂P, Good (ell a) a ∧
              (∀ r : ℕ, Good r a → ell a ≤ r) ∧
              (∀ r : ℕ, Good r a → X a ≤ (3 : ℝ) ^ (γ * (r : ℝ)))) ∧
            MemLp X (ENNReal.ofReal (bigQ d γ : ℝ)) P ∧
            Integrable (fun a => X a ^ bigQ d γ) P ∧
            (∫ a, X a ^ bigQ d γ ∂P) ≤ (2 : ℝ) ^ bigQ d γ ∧
            eLpNorm X (ENNReal.ofReal (bigQ d γ : ℝ)) P ≤ ENNReal.ofReal 2 ∧
            (∀ᵐ a ∂P,
              (∀ (k : ℤ) (w : Fin d → ℤ),
                standardCell d k w ⊆ centeredCube d (2 * (jStar : ℤ)) →
                BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
                  (blockScale (X a * (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (k : ℝ)) 0)) E)) ∧
              (∀ (m : Mat d), m.PosDef → ∀ (j : ℤ) (y : Vec d),
                adaptedCellTranslate (explicitRoundedGrid jStar m) j y ⊆ centeredCube d (2 *
                  (jStar : ℤ)) →
                BlockMatLoewnerLE (coarseBlock (adaptedCellTranslate (explicitRoundedGrid jStar
                  m) j y) a)
                  (blockScale (C * Real.sqrt (‖m‖ * ‖m⁻¹‖) * X a *
                    (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (j : ℝ)) 0)) E))) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Csrc, hCsrc, hsource⟩ := source_multiplier d hd γ hγ
  let C : ℝ := 12 * (d : ℝ) ^ ((3 : ℝ) / 2) / (1 - (3 : ℝ) ^ (-(1 - γ)))
  have hden : 0 < 1 - (3 : ℝ) ^ (-(1 - γ)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hγ.2]))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨Csrc, C, hCsrc, hC, ?_⟩
  intro P hP E Ψ K S hstat hdag jStar hj hthreshold Good
  obtain ⟨ell, X, hell, hX, hform, hmin, hlp, hi, hmoment, hnorm⟩ :=
    hsource P E Ψ K S hstat hdag jStar hj hthreshold
  refine ⟨ell, X, hell, hX, hform, hmin, hlp, hi, hmoment, hnorm, ?_⟩
  filter_upwards [hmin, stationary_all_integer_dagger_event hstat hdag] with a ha hcoarse
  have hX0 : 0 ≤ X a := by rw [hform]; positivity
  have hstd (k : ℤ) (w : Fin d → ℤ)
      (hw : standardCell d k w ⊆ centeredCube d (2 * (jStar : ℤ))) :
      BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
        (blockScale (X a * (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (k : ℝ)) 0)) E) := by
    rw [hform]
    exact source_standard_multiplier_bound γ E hγ.1 hdag.refBlock_posDef S a
      jStar (ell a) hcoarse ha.1 k w hw
  refine ⟨hstd, ?_⟩
  intro m hm j y hcell
  have hb := adapted_bound_of_standard γ hγ E hdag.refBlock_posDef a jStar
    (X a) hX0 hstd (inverseNormLE_roundedGrid hj hm) j y hcell
  have hc : C * X a * (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (j : ℝ)) 0) ≤
      C * Real.sqrt (‖m‖ * ‖m⁻¹‖) * X a *
        (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (j : ℝ)) 0) := by
    have he := one_le_source_eccentricity hm
    calc
      _ = C * 1 * X a * (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (j : ℝ)) 0) := by ring
      _ ≤ _ := by gcongr
  exact fun v => (hb v).trans ((blockScale_le_blockScale_of_pos hdag.refBlock_posDef hc) v)

end
end HCPolySupport.HighContrast.Source
