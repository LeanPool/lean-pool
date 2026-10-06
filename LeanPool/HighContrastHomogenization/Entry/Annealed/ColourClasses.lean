/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.AdaptedLocality
public import LeanPool.HighContrastHomogenization.Entry.Geometry.AdaptedCellTransport
public import LeanPool.HighContrastHomogenization.Entry.Geometry.RoundedGridBasic
public import LeanPool.HighContrastHomogenization.Entry.Setup.ProjectiveDistance
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Data.ZMod.Basic
public import LeanPool.HighContrastHomogenization.Analytic.NormComparison
public import LeanPool.HighContrastHomogenization.Analytic.AffineFractionalKernel

/-!
# High-contrast homogenization: Entry.Annealed.ColourClasses

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Residue colouring modulo three: separation, classwise independence, the `3^{d/2}` count

The first paragraph of the printed proof
(`l.fixed.geometry.matrix.averaging`):

> Write `z = 3^j q w` and color the adapted cubes by the residue class of `w` modulo three.
> There are at most `3^d` classes.  Before applying `3^j q`, distinct cubes in one class are
> separated by Euclidean distance at least two.  By `e.rounded.grid.bounds`, their images have
> Euclidean separation at least `3^j`, and hence `ℓ^∞`-separation at least `3^j/√d ≥ 1`.  The
> range-of-dependence assumption therefore makes the cubes in each class jointly independent.

Every constant below depends on `d` alone; no ellipticity constant occurs.

* `exists_unique_index_of_mem_adaptedLatticeAtScale` — for `IsUnit q` every lattice centre has a
unique
  integer index, so the colouring of centres by `w mod 3` is well posed.  The index map itself is
  taken proof-locally by `Classical.choose` at the use site; no production definition is added.
* `unitSeparated_adaptedCellAtCenter_of_residue_eq` — the separation, stated as the
  `UnitSeparated` of `HCPoly/Setup/LocalSigmaFields.lean`.  `Source.AKL.supDist x y = ‖x - y‖` and
  the norm of `Vec d = Fin d → ℝ` is the `ℓ^∞` norm, so this is exactly the printed
  `ℓ^∞`-separation.
* `iIndepFun_coarseBlockNormalized_of_unitSeparated` — classwise joint independence, from the
  full-matrix `iIndepFun_of_coeffSigma_measurable`, pushed through the fixed measurable map
  `M ↦ S (M - A) S`.  The full-matrix export is used, not the fixed-entry consumer, which would
  give independence one entry at a time.
* `sum_rpow_card_fiber_le` and `card_residue_colours` — the class-size estimate
  `∑_c (#C_c)^{1/2} ≤ 3^{d/2} (#Z)^{1/2}` by Cauchy-Schwarz over at most `3^d` classes.  Empty
  classes contribute `0` to both sides and are not excluded by a hypothesis.
-/

open HCPolySupport.HighContrast (CoeffSpace UnitSeparated adaptedCellCenter blockSub coarseBlock
  matSqrt normalizedBlock)
namespace HCPolySupport.HighContrast.Annealed

open MeasureTheory

open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## Lattice indexing -/

/-- For an invertible `q` the index of a lattice centre is unique
(`Geometry.adaptedCellCenter_injective`), so colouring a centre by the residue of its index is
well posed.  The index map is produced proof-locally by `Classical.choose` on this statement. -/
theorem exists_unique_index_of_mem_adaptedLatticeAtScale {q : Mat d} (hq : IsUnit q) (j : ℤ)
    {z : Vec d} (hz : z ∈ adaptedLatticeAtScale q j) :
    ∃! w : Fin d → ℤ, adaptedCellCenter q j w = z := by
  obtain ⟨w, hw⟩ := hz
  refine ⟨w, hw, fun w' hw' => ?_⟩
  exact Geometry.adaptedCellCenter_injective q j hq (hw'.trans hw.symm)

/-! ## Elementary norm comparisons on `Vec d` -/

/-- `q` does not contract by more than a factor two, in the Euclidean norm: this is the printed
use of `e.rounded.grid.bounds`'s `q ≥ ½ Id`, through Cauchy-Schwarz and the symmetry of `q`. -/
theorem quarter_vecNormSq_le_vecNormSq_roundedGrid_mulVec {jStar : ℕ} {m : Mat d}
    (hj : 2 * d ≤ 3 ^ jStar) (hm : m.PosDef) (v : Vec d) :
    vecNormSq v / 4 ≤ vecNormSq (matVecMul (Geometry.explicitRoundedGrid jStar m) v) := by
  set q := Geometry.explicitRoundedGrid jStar m with hqdef
  have hlow : 1 / 2 * vecNormSq v ≤ vecDot v (matVecMul q v) := by
    have h := Geometry.half_vecNormSq_le_dotProduct_roundedGrid hj hm v
    simpa [vecDot, matVecMul, Matrix.mulVec, dotProduct] using h
  have hcs : vecDot v (matVecMul q v) ^ 2
      ≤ vecNormSq v * vecNormSq (matVecMul q v) :=
    sq_vecDot_le_vecNormSq_mul_vecNormSq _ _
  have hvnn : 0 ≤ vecNormSq v := vecNormSq_nonneg v
  rcases eq_or_lt_of_le hvnn with hS | hS
  · rw [← hS]
    simpa using vecNormSq_nonneg (matVecMul q v)
  · have hD0 : 0 ≤ vecNormSq v / 2 := by linarith only [hvnn]
    have hDD : (vecNormSq v / 2) * (vecNormSq v / 2)
        ≤ vecDot v (matVecMul q v) * vecDot v (matVecMul q v) :=
      mul_self_le_mul_self hD0 (by linarith only [hlow])
    have h1 : vecNormSq v * (vecNormSq v / 4)
        ≤ vecNormSq v * vecNormSq (matVecMul q v) := by
      calc vecNormSq v * (vecNormSq v / 4)
          = (vecNormSq v / 2) * (vecNormSq v / 2) := by ring
        _ ≤ vecDot v (matVecMul q v) * vecDot v (matVecMul q v) := hDD
        _ = vecDot v (matVecMul q v) ^ 2 := by ring
        _ ≤ vecNormSq v * vecNormSq (matVecMul q v) := hcs
    exact le_of_mul_le_mul_left h1 hS

/-! ## Separation inside one colour class -/

/-- **Separation.** Two distinct indices with the same residue modulo three give
`UnitSeparated` adapted cells, for `q = 𝒬(𝔪)`, `3^{j_*} ≥ 2d`, `d ≥ 2` and `j ≥ j_*`.

Route: some coordinate of `w - w'` has absolute value at least three, so the standard cells are
`ℓ^∞`-separated by more than `2·3^j`; `q ≥ ½ Id` with the symmetry of `q` contracts the Euclidean
norm by at most a factor two; and `‖·‖_∞ ≥ ‖·‖₂/√d` with `3^j ≥ 3^{j_*} ≥ 2d` closes it. -/
theorem unitSeparated_adaptedCellAtCenter_of_residue_eq {jStar : ℕ} {m : Mat d}
    (hd : 2 ≤ d) (hj : 2 * d ≤ 3 ^ jStar) (hm : m.PosDef) {j : ℤ} (hjgen : (jStar : ℤ) ≤ j)
    {w w' : Fin d → ℤ} (hne : w ≠ w') (hres : ∀ i, ((w i : ZMod 3)) = ((w' i : ZMod 3))) :
    UnitSeparated (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar m) j w)
      (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar m) j w') := by
  classical
  set q := Geometry.explicitRoundedGrid jStar m with hqdef
  -- a coordinate where the indices differ by at least three
  obtain ⟨i₀, hi₀⟩ : ∃ i, w i ≠ w' i := by
    by_contra hcon
    push Not at hcon
    exact hne (funext hcon)
  have hmodeq : w i₀ ≡ w' i₀ [ZMOD (3 : ℕ)] :=
    (ZMod.intCast_eq_intCast_iff (w i₀) (w' i₀) 3).1 (hres i₀)
  have hdvd : (3 : ℤ) ∣ w i₀ - w' i₀ := by
    simpa using Int.ModEq.dvd hmodeq.symm
  have hgap : (3 : ℤ) ≤ |w i₀ - w' i₀| := by
    have hnz : w i₀ - w' i₀ ≠ 0 := sub_ne_zero.2 hi₀
    exact Int.le_of_dvd (abs_pos.2 hnz) ((dvd_abs _ _).2 hdvd)
  -- scale facts
  have h3j : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  have hscale : (2 : ℝ) * (d : ℝ) ≤ (3 : ℝ) ^ j := by
    have hstar : ((2 * d : ℕ) : ℝ) ≤ ((3 ^ jStar : ℕ) : ℝ) := by exact_mod_cast hj
    have hmono : ((3 : ℝ) ^ (jStar : ℤ)) ≤ (3 : ℝ) ^ j :=
      zpow_le_zpow_right₀ (by norm_num) hjgen
    push_cast at hstar
    have hnat : ((3 : ℝ) ^ jStar) = (3 : ℝ) ^ (jStar : ℤ) := (zpow_natCast (3 : ℝ) jStar).symm
    rw [hnat] at hstar
    linarith only [hstar, hmono]
  -- the separation itself
  intro x y hx hy
  rw [Geometry.adaptedCellAtCenter_eq_affine_standardCell] at hx hy
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨u', hu', rfl⟩ := hy
  set v : Vec d := u - u' with hvdef
  have hxy : matVecMul q u - matVecMul q u' = matVecMul q v := matVecMul_sub_vec q u u'
  -- coordinatewise gap
  have hbig : (2 : ℝ) * (3 : ℝ) ^ j < |v i₀| := by
    rw [Recurrence.mem_standardCell_iff] at hu hu'
    obtain ⟨hu1, hu2⟩ := hu i₀
    obtain ⟨hu'1, hu'2⟩ := hu' i₀
    have hvi : v i₀ = u i₀ - u' i₀ := rfl
    rcases le_or_gt (w' i₀) (w i₀) with hc | hc
    · have h3 : (3 : ℤ) ≤ w i₀ - w' i₀ := by
        rcases abs_cases (w i₀ - w' i₀) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
      have h3R : (3 : ℝ) ≤ (w i₀ : ℝ) - (w' i₀ : ℝ) := by exact_mod_cast h3
      have : (2 : ℝ) * (3 : ℝ) ^ j < v i₀ := by
        rw [hvi]; nlinarith only [hu1, hu'2, h3R, h3j]
      rw [abs_of_pos (by linarith only [this, h3j] : (0:ℝ) < v i₀)]
      exact this
    · have h3 : (3 : ℤ) ≤ w' i₀ - w i₀ := by
        rcases abs_cases (w i₀ - w' i₀) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
      have h3R : (3 : ℝ) ≤ (w' i₀ : ℝ) - (w i₀ : ℝ) := by exact_mod_cast h3
      have : v i₀ < -((2 : ℝ) * (3 : ℝ) ^ j) := by
        rw [hvi]; nlinarith only [hu2, hu'1, h3R, h3j]
      rw [abs_of_neg (by linarith only [this, h3j] : v i₀ < 0)]
      linarith only [this]
  -- from the coordinate gap to the Euclidean norm
  have hvsq : (2 : ℝ) * (3 : ℝ) ^ j * ((2 : ℝ) * (3 : ℝ) ^ j) < vecNormSq v := by
    have h := sq_apply_le_vecNormSq v i₀
    have habs : v i₀ ^ 2 = |v i₀| ^ 2 := (sq_abs _).symm
    nlinarith only [hbig, h, habs, h3j, abs_nonneg (v i₀)]
  -- contraction bound and the sup-norm comparison
  have hq4 := quarter_vecNormSq_le_vecNormSq_roundedGrid_mulVec (m := m) hj hm v
  have hsup := vecNormSq_le_dim_mul_norm_sq (matVecMul q v)
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdsq : (d : ℝ) ≤ (3 : ℝ) ^ j * (3 : ℝ) ^ j := by
    have hstep : (2 * (d : ℝ)) * (2 * (d : ℝ)) ≤ (3 : ℝ) ^ j * (3 : ℝ) ^ j :=
      mul_le_mul hscale hscale (by linarith only [hd2]) h3j.le
    nlinarith only [hstep, hd2]
  have hnormsq : (1 : ℝ) ≤ ‖matVecMul q v‖ ^ 2 := by
    nlinarith only [hq4, hsup, hvsq, hdpos, h3j, hdsq]
  have hnn : (0 : ℝ) ≤ ‖matVecMul q v‖ := norm_nonneg _
  have : (1 : ℝ) ≤ ‖matVecMul q v‖ := by nlinarith only [hnormsq, hnn]
  simpa [Source.AKL.supDist, hxy] using this

/-! ## Classwise joint independence -/

/-- The fixed deterministic map `M ↦ S (M - toFullBlockMat A) S` through which the coarse block
is pushed; `S = matSqrt ((toFullBlockMat R)⁻¹)`.  Written out so that its measurability is proved
once. -/
private theorem measurable_normalizedBlock_comp (A R : BlockMat d) :
    Measurable (fun M : FullBlockMat d =>
      toFullBlockMat (normalizedBlock (blockSub (ofFullBlockMat M) A) R)) := by
  have hsub : ∀ M : FullBlockMat d,
      toFullBlockMat (blockSub (ofFullBlockMat M) A) = M - toFullBlockMat A := by
    intro M
    ext α β
    cases α <;> cases β <;> rfl
  have hrw : (fun M : FullBlockMat d =>
      toFullBlockMat (normalizedBlock (blockSub (ofFullBlockMat M) A) R))
      = fun M : FullBlockMat d =>
        matSqrt ((toFullBlockMat R)⁻¹) * (M - toFullBlockMat A) *
          matSqrt ((toFullBlockMat R)⁻¹) := by
    funext M
    rw [normalizedBlock, toFullBlockMat_ofFullBlockMat, hsub]
  rw [hrw]
  refine Measurable.of_eval fun α => Measurable.of_eval fun β => ?_
  simp only [Matrix.mul_apply]
  refine Finset.measurable_sum _ fun γ _ => ?_
  refine Measurable.mul ?_ measurable_const
  refine Finset.measurable_sum _ fun δ _ => ?_
  refine Measurable.mul measurable_const ?_
  simp only [Matrix.sub_apply]
  refine Measurable.sub ?_ measurable_const
  have h1 : Measurable (fun M : FullBlockMat d => M δ) := measurable_pi_apply δ
  have h2 : Measurable (fun r : BlockCoord d → ℝ => r γ) := measurable_pi_apply γ
  exact h2.comp h1

/-- **Classwise joint independence.**  A family of adapted cells that is pairwise
`UnitSeparated` gives a jointly independent family of normalized centered blocks.

This instantiates the full-matrix `iIndepFun_of_coeffSigma_measurable`, giving independence of
the entire family at once rather than one entry at a time. -/
theorem iIndepFun_coarseBlockNormalized_of_unitSeparated [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hunit : IsUnitRangeLaw P)
    (q : Mat d) (hq : IsUnit q) (j : ℤ) {ι : Type*} (y : ι → Vec d)
    (hsep : Pairwise fun i i' => UnitSeparated (HighContrast.adaptedCellTranslate q j (y i))
      (HighContrast.adaptedCellTranslate q j (y i')))
    (A R : BlockMat d) :
    ProbabilityTheory.iIndepFun
      (fun (i : ι) a => toFullBlockMat (normalizedBlock
        (blockSub (coarseBlock (HighContrast.adaptedCellTranslate q j (y i)) a) A) R)) P := by
  refine iIndepFun_of_coeffSigma_measurable P hunit
    (fun i => HighContrast.adaptedCellTranslate q j (y i))
    (fun i => (Geometry.isOpen_adaptedCellTranslate hq j (y i)).measurableSet) _ ?_ hsep
  intro i
  have hbase := measurable_coarseBlock_matrix_adapted (d := d) q hq j (y i)
  have heq : (fun a => toFullBlockMat (normalizedBlock
      (blockSub (coarseBlock (HighContrast.adaptedCellTranslate q j (y i)) a) A) R))
      = (fun M : FullBlockMat d =>
          toFullBlockMat (normalizedBlock (blockSub (ofFullBlockMat M) A) R)) ∘
        (fun a => toFullBlockMat
          (coarseBlock (HighContrast.adaptedCellTranslate q j (y i)) a)) := by
    funext a
    simp
  rw [heq]
  exact (measurable_normalizedBlock_comp (d := d) A R).comp hbase

/-! ## The colour partition and its size estimate -/

/-- There are exactly `3^d` residue colours, so at most `3^d` nonempty classes. -/
theorem card_residue_colours : Fintype.card (Fin d → ZMod 3) = 3 ^ d := by
  simp

/-- **The class-size estimate.**  For any colouring of a finite set `Z` by a finite palette,
`∑_c (#C_c)^{1/2} ≤ (#palette)^{1/2} (#Z)^{1/2}`, by Cauchy-Schwarz.  Empty classes contribute
`0` to both sides; no nonemptiness hypothesis is used.  With the palette `Fin d → ZMod 3` and
`card_residue_colours` this is the printed `∑_C (#C)^{1/2} ≤ 3^{d/2}(#Z)^{1/2}`. -/
theorem sum_rpow_card_fiber_le {ι κ : Type*} [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (Z : Finset ι) (col : ι → κ) :
    ∑ c : κ, (((Z.filter fun z => col z = c).card : ℝ)) ^ ((1 : ℝ) / 2)
      ≤ ((Fintype.card κ : ℝ)) ^ ((1 : ℝ) / 2) * ((Z.card : ℝ)) ^ ((1 : ℝ) / 2) := by
  classical
  set n : κ → ℝ := fun c => ((Z.filter fun z => col z = c).card : ℝ) with hn
  have hnn : ∀ c, 0 ≤ n c := fun c => by positivity
  have htotal : ∑ c : κ, n c = (Z.card : ℝ) := by
    rw [hn]
    rw [← Nat.cast_sum]
    congr 1
    exact (Finset.card_eq_sum_card_fiberwise (fun z _ => Finset.mem_univ (col z))).symm
  have hholder := Real.inner_le_weight_mul_Lp_of_nonneg (Finset.univ : Finset κ)
    (p := 2) (by norm_num) (fun _ => (1 : ℝ)) (fun c => n c ^ ((1 : ℝ) / 2))
    (fun _ => zero_le_one) (fun c => Real.rpow_nonneg (hnn c) _)
  simp only [one_mul] at hholder
  have hsq : ∀ c : κ, (n c ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) = n c := by
    intro c
    rw [← Real.rpow_mul (hnn c)]
    norm_num
  have hcard : ∑ _c : κ, (1 : ℝ) = (Fintype.card κ : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  calc ∑ c : κ, n c ^ ((1 : ℝ) / 2)
      ≤ (∑ _c : κ, (1 : ℝ)) ^ (1 - (2 : ℝ)⁻¹) *
          (∑ c : κ, (n c ^ ((1 : ℝ) / 2)) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) := by
        simpa using hholder
    _ = ((Fintype.card κ : ℝ)) ^ ((1 : ℝ) / 2) * ((Z.card : ℝ)) ^ ((1 : ℝ) / 2) := by
        rw [hcard]
        simp only [hsq]
        rw [htotal]
        norm_num

end

end HCPolySupport.HighContrast.Annealed
