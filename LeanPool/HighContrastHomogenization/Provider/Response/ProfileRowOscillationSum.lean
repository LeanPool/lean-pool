/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowMeanEstimates
public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.Geometric

/-!
# High-contrast homogenization: Provider.Response.ProfileRowOscillationSum

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The scale sum of the cutoff-oscillation row

The cutoff-oscillation contribution to a cutoff-defect mean row is a sum over
scales of a normalized cell average of a product: a cell energy root against a
cell Schur load.  Cauchy-Schwarz in the cell index and then in the scale index,
with the geometric weight split between the two factors, converts that sum into
the energy root times the root of the all-earlier Schur row.

The scale weights are split as `3^{k-s} = 3^{(k-s)/4}·3^{3(k-s)/4}`, so the
energy side collects a convergent geometric factor and the load side collects
exactly the row weight `3^{3(k-s)/2}`.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ}

/-! ## Cauchy-Schwarz for the normalized cell average -/

/-- The normalized cell average of a product is at most the product of the
normalized quadratic means. -/
theorem avsum_mul_le_sqrt_mul_sqrt {ι : Type*} (Z : Finset ι) (f g : ι → ℝ) :
    avsum Z (fun z ↦ f z * g z) ≤
      Real.sqrt (avsum Z (fun z ↦ f z ^ 2)) *
        Real.sqrt (avsum Z (fun z ↦ g z ^ 2)) := by
  classical
  have hcs : (∑ z ∈ Z, f z * g z) ^ 2 ≤
      (∑ z ∈ Z, f z ^ 2) * ∑ z ∈ Z, g z ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Z f g
  have hcard : (0 : ℝ) ≤ ((Z.card : ℝ))⁻¹ := by positivity
  have hsq : avsum Z (fun z ↦ f z * g z) ^ 2 ≤
      avsum Z (fun z ↦ f z ^ 2) * avsum Z (fun z ↦ g z ^ 2) := by
    rw [avsum_eq, avsum_eq, avsum_eq, mul_pow]
    calc ((Z.card : ℝ))⁻¹ ^ 2 * (∑ z ∈ Z, f z * g z) ^ 2
        ≤ ((Z.card : ℝ))⁻¹ ^ 2 * ((∑ z ∈ Z, f z ^ 2) * ∑ z ∈ Z, g z ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = (((Z.card : ℝ))⁻¹ * ∑ z ∈ Z, f z ^ 2) *
            (((Z.card : ℝ))⁻¹ * ∑ z ∈ Z, g z ^ 2) := by ring
  have hfg_nonneg : 0 ≤ avsum Z (fun z ↦ f z ^ 2) :=
    avsum_nonneg fun z _ ↦ sq_nonneg _
  have hg_nonneg : 0 ≤ avsum Z (fun z ↦ g z ^ 2) :=
    avsum_nonneg fun z _ ↦ sq_nonneg _
  have hroot := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_mul hfg_nonneg] at hroot
  exact le_trans (le_abs_self _) (by rwa [← Real.sqrt_sq_eq_abs])

/-! ## The geometric scale factor -/

/-- The half-power scale weights of an all-earlier row sum to a convergent
geometric total. -/
theorem sum_geom_half_Icc_le (Klo s : ℤ) :
    ∑ k ∈ Finset.Icc Klo s, (3 : ℝ) ^ ((1 / 2 : ℝ) * ((k : ℝ) - (s : ℝ))) ≤
      1 / (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ)) := by
  have hset : Finset.Icc Klo s = Finset.Ico Klo (s + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hbase := PortableHistory.sum_geom_Ico_le (a := (1 / 2 : ℝ)) (by norm_num) Klo (s + 1)
  rw [hset]
  refine le_trans (le_of_eq ?_) hbase
  refine Finset.sum_congr rfl ?_
  intro k _hk
  congr 1
  push_cast
  ring

/-! ## The weighted scale sum -/

/-- **The weighted scale sum.**  A geometrically weighted sum of products, with
the first factor uniformly bounded, is controlled by that bound times the root of
the row-weighted sum of the second factor's squares. -/
theorem sum_scaleWeighted_mul_le {Klo s : ℤ} {A B : ℤ → ℝ} {SE : ℝ}
    (hSE : 0 ≤ SE)
    (hB : ∀ k ∈ Finset.Icc Klo s, 0 ≤ B k)
    (hAE : ∀ k ∈ Finset.Icc Klo s, A k ≤ SE) :
    ∑ k ∈ Finset.Icc Klo s, (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) * (A k * B k) ≤
      Real.sqrt (1 / (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))) * SE *
        Real.sqrt (∑ k ∈ Finset.Icc Klo s, profileRowWeight k s * B k ^ 2) := by
  classical
  set I : Finset ℤ := Finset.Icc Klo s with hI
  set u : ℤ → ℝ := fun k ↦ (3 : ℝ) ^ ((1 / 4 : ℝ) * ((k : ℝ) - (s : ℝ))) with hu
  set v : ℤ → ℝ := fun k ↦ (3 : ℝ) ^ ((3 / 4 : ℝ) * ((k : ℝ) - (s : ℝ))) * B k with hv
  have hthree : (0 : ℝ) < 3 := by norm_num
  have huv : ∀ k, u k * v k = (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) * B k := by
    intro k
    rw [hu, hv, ← mul_assoc, ← Real.rpow_add hthree]
    congr 2
    ring
  have husq : ∀ k, u k ^ 2 = (3 : ℝ) ^ ((1 / 2 : ℝ) * ((k : ℝ) - (s : ℝ))) := by
    intro k
    rw [hu, ← Real.rpow_natCast ((3 : ℝ) ^ ((1 / 4 : ℝ) * ((k : ℝ) - (s : ℝ)))) 2,
      ← Real.rpow_mul hthree.le]
    congr 1
    push_cast
    ring
  have hvsq : ∀ k, v k ^ 2 = profileRowWeight k s * B k ^ 2 := by
    intro k
    rw [hv, mul_pow, profileRowWeight,
      ← Real.rpow_natCast ((3 : ℝ) ^ ((3 / 4 : ℝ) * ((k : ℝ) - (s : ℝ)))) 2,
      ← Real.rpow_mul hthree.le]
    congr 2
    push_cast
    ring
  have hfirst : ∑ k ∈ I, (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) * (A k * B k) ≤
      SE * ∑ k ∈ I, (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) * B k := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro k hk
    have hpow : (0 : ℝ) ≤ (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) :=
      Real.rpow_nonneg hthree.le _
    have hstep : A k * B k ≤ SE * B k :=
      mul_le_mul_of_nonneg_right (hAE k hk) (hB k hk)
    calc (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) * (A k * B k)
        ≤ (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) * (SE * B k) :=
          mul_le_mul_of_nonneg_left hstep hpow
      _ = SE * ((3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) * B k) := by ring
  have husum_nonneg : 0 ≤ ∑ k ∈ I, u k ^ 2 :=
    Finset.sum_nonneg fun k _ ↦ sq_nonneg _
  have hvsum_nonneg : 0 ≤ ∑ k ∈ I, v k ^ 2 :=
    Finset.sum_nonneg fun k _ ↦ sq_nonneg _
  have hcs : (∑ k ∈ I, u k * v k) ^ 2 ≤ (∑ k ∈ I, u k ^ 2) * ∑ k ∈ I, v k ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq I u v
  have hsecond : ∑ k ∈ I, (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) * B k ≤
      Real.sqrt (∑ k ∈ I, u k ^ 2) * Real.sqrt (∑ k ∈ I, v k ^ 2) := by
    have hroot := Real.sqrt_le_sqrt hcs
    rw [Real.sqrt_mul husum_nonneg] at hroot
    have hcast : ∑ k ∈ I, u k * v k =
        ∑ k ∈ I, (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) * B k :=
      Finset.sum_congr rfl fun k _ ↦ huv k
    rw [hcast] at hroot
    exact le_trans (le_abs_self _) (by rwa [← Real.sqrt_sq_eq_abs])
  have hgeom : Real.sqrt (∑ k ∈ I, u k ^ 2) ≤
      Real.sqrt (1 / (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))) := by
    refine Real.sqrt_le_sqrt ?_
    calc ∑ k ∈ I, u k ^ 2
        = ∑ k ∈ I, (3 : ℝ) ^ ((1 / 2 : ℝ) * ((k : ℝ) - (s : ℝ))) :=
          Finset.sum_congr rfl fun k _ ↦ husq k
      _ ≤ 1 / (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ)) := by
          rw [hI]; exact sum_geom_half_Icc_le Klo s
  have hvcast : Real.sqrt (∑ k ∈ I, v k ^ 2) =
      Real.sqrt (∑ k ∈ I, profileRowWeight k s * B k ^ 2) :=
    congrArg Real.sqrt (Finset.sum_congr rfl fun k _ ↦ hvsq k)
  have hvroot_nonneg : 0 ≤ Real.sqrt (∑ k ∈ I, v k ^ 2) := Real.sqrt_nonneg _
  calc ∑ k ∈ I, (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) * (A k * B k)
      ≤ SE * ∑ k ∈ I, (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) * B k := hfirst
    _ ≤ SE * (Real.sqrt (∑ k ∈ I, u k ^ 2) * Real.sqrt (∑ k ∈ I, v k ^ 2)) :=
        mul_le_mul_of_nonneg_left hsecond hSE
    _ ≤ SE * (Real.sqrt (1 / (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))) *
          Real.sqrt (∑ k ∈ I, v k ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hgeom hvroot_nonneg) hSE
    _ = Real.sqrt (1 / (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))) * SE *
          Real.sqrt (∑ k ∈ I, profileRowWeight k s * B k ^ 2) := by
        rw [hvcast]; ring

/-! ## The flux half of the row -/

theorem profileRowWeight_pos (k s : ℤ) : 0 < profileRowWeight k s :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- The square of the flux half of the Schur load is at most the load. -/
theorem sq_profileSchurLoadFlux_le_profileSchurLoad (H : BlockMat d)
    (Pcen Qcen : Vec d) :
    profileSchurLoadFlux H Qcen ^ 2 ≤ profileSchurLoad H Pcen Qcen := by
  rw [profileSchurLoad_eq_add_sq]
  have hf := profileSchurLoadFlux_nonneg H Qcen
  have hg := profileSchurLoadGradient_nonneg H Pcen
  nlinarith only [hf, hg]

theorem profilePrimalHattedRowPartial_nonneg
    (P : Measure (CoeffSpace d)) (q h : Mat d)
    (Klo s : ℤ) (Pcen Qcen : Vec d) :
    0 ≤ profilePrimalHattedRowPartial P q h Klo s Pcen Qcen := by
  rw [profilePrimalHattedRowPartial]
  refine Finset.sum_nonneg ?_
  intro k _hk
  refine mul_nonneg (profileRowWeight_pos k s).le ?_
  refine avsum_nonneg ?_
  intro w _hw
  exact profileSchurLoad_nonneg _ Pcen Qcen

/-! ## The row bound in the mixed carrier -/

/-! ## The generic closing form -/

/-- The square of the gradient half of the Schur load is at most the load. -/
theorem sq_profileSchurLoadGradient_le_profileSchurLoad (H : BlockMat d)
    (Pcen Qcen : Vec d) :
    profileSchurLoadGradient H Pcen ^ 2 ≤ profileSchurLoad H Pcen Qcen := by
  rw [profileSchurLoad_eq_add_sq]
  have hf := profileSchurLoadFlux_nonneg H Qcen
  have hg := profileSchurLoadGradient_nonneg H Pcen
  nlinarith only [hf, hg]

/-- A row-weighted sum of squared cell loads is dominated by the corresponding
row-weighted sum of Schur loads. -/
theorem sum_rowWeight_avsum_sq_le (q : Mat d) (Klo s : ℤ) (Pcen Qcen : Vec d)
    (blk : ℤ → (Fin d → ℤ) → BlockMat d) (load : ℤ → (Fin d → ℤ) → ℝ)
    (hsq : ∀ k w, load k w ^ 2 ≤ profileSchurLoad (blk k w) Pcen Qcen) :
    ∑ k ∈ Finset.Icc Klo s, profileRowWeight k s *
        avsum (alignedIndex q k s) (fun w ↦ load k w ^ 2) ≤
      ∑ k ∈ Finset.Icc Klo s, profileRowWeight k s *
        avsum (alignedIndex q k s) (fun w ↦
          profileSchurLoad (blk k w) Pcen Qcen) := by
  refine Finset.sum_le_sum ?_
  intro k _hk
  refine mul_le_mul_of_nonneg_left ?_ (profileRowWeight_pos k s).le
  exact avsum_le_avsum fun w _hw ↦ hsq k w

/-- A row-weighted sum of Schur loads is nonnegative. -/
theorem sum_rowWeight_avsum_profileSchurLoad_nonneg (q : Mat d) (Klo s : ℤ)
    (Pcen Qcen : Vec d) (blk : ℤ → (Fin d → ℤ) → BlockMat d) :
    0 ≤ ∑ k ∈ Finset.Icc Klo s, profileRowWeight k s *
      avsum (alignedIndex q k s) (fun w ↦
        profileSchurLoad (blk k w) Pcen Qcen) := by
  refine Finset.sum_nonneg ?_
  intro k _hk
  exact mul_nonneg (profileRowWeight_pos k s).le
    (avsum_nonneg fun w _hw ↦ profileSchurLoad_nonneg _ Pcen Qcen)

theorem profileAdjointHattedRowPartial_nonneg
    (P : Measure (CoeffSpace d)) (q h : Mat d) (Klo s : ℤ) (Pcen Qcen : Vec d) :
    0 ≤ profileAdjointHattedRowPartial P q h Klo s Pcen Qcen :=
  sum_rowWeight_avsum_profileSchurLoad_nonneg q Klo s Pcen Qcen
    (fun k w ↦ profileHattedAdjointBlock h (annealedBlock P (adaptedCellAt q k w)))

/-- A quantity dominated by a constant times the root of a lower-cutoff row is
dominated, in the mixed carrier, by that constant against the root of any
majorant of the row. -/
theorem ofReal_abs_le_mul_row_rpow {row : ℝ≥0∞} {rowPartial T G : ℝ}
    (hG : 0 ≤ G) (hrowPartial : 0 ≤ rowPartial)
    (hrowLe : ENNReal.ofReal rowPartial ≤ row)
    (hT : |T| ≤ G * Real.sqrt rowPartial) :
    ENNReal.ofReal |T| ≤ ENNReal.ofReal G * row ^ (1 / 2 : ℝ) := by
  have hroot : ENNReal.ofReal (Real.sqrt rowPartial) ≤ row ^ (1 / 2 : ℝ) := by
    have hrpow : ENNReal.ofReal rowPartial ^ (1 / 2 : ℝ) ≤ row ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hrowLe (by norm_num)
    rwa [Real.sqrt_eq_rpow,
      ← ENNReal.ofReal_rpow_of_nonneg hrowPartial (by norm_num)]
  calc ENNReal.ofReal |T|
      ≤ ENNReal.ofReal (G * Real.sqrt rowPartial) := ENNReal.ofReal_le_ofReal hT
    _ = ENNReal.ofReal G * ENNReal.ofReal (Real.sqrt rowPartial) :=
        ENNReal.ofReal_mul hG
    _ ≤ ENNReal.ofReal G * row ^ (1 / 2 : ℝ) := mul_le_mul' le_rfl hroot

/-- **The cutoff-oscillation contribution to a cutoff-defect mean row.**  The
scale sum of cell products, with the cell energy roots uniformly bounded by the
parent energy root, is dominated by the geometric constant times that energy root
times the root of the row. -/
theorem ofReal_abs_scaleSum_le_mul_row_rpow (q : Mat d) (Klo s : ℤ)
    (energy load : ℤ → (Fin d → ℤ) → ℝ) {row : ℝ≥0∞} {rowPartial SE Cd T : ℝ}
    (hSE : 0 ≤ SE) (hCd : 0 ≤ Cd)
    (hrowPartial : 0 ≤ rowPartial)
    (hrowSum : ∑ k ∈ Finset.Icc Klo s, profileRowWeight k s *
      avsum (alignedIndex q k s) (fun w ↦ load k w ^ 2) ≤ rowPartial)
    (hrowLe : ENNReal.ofReal rowPartial ≤ row)
    (hbound : ∀ k ∈ Finset.Icc Klo s,
      Real.sqrt (avsum (alignedIndex q k s) (fun w ↦ energy k w ^ 2)) ≤ SE)
    (hT : |T| ≤ Cd * ∑ k ∈ Finset.Icc Klo s, (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) *
      avsum (alignedIndex q k s) (fun w ↦ energy k w * load k w)) :
    ENNReal.ofReal |T| ≤
      ENNReal.ofReal
          (Cd * Real.sqrt (1 / (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))) * SE) *
        row ^ (1 / 2 : ℝ) := by
  classical
  set A : ℤ → ℝ := fun k ↦
    Real.sqrt (avsum (alignedIndex q k s) (fun w ↦ energy k w ^ 2)) with hA
  set B : ℤ → ℝ := fun k ↦
    Real.sqrt (avsum (alignedIndex q k s) (fun w ↦ load k w ^ 2)) with hB
  have hscale : ∑ k ∈ Finset.Icc Klo s, (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) *
      avsum (alignedIndex q k s) (fun w ↦ energy k w * load k w) ≤
      ∑ k ∈ Finset.Icc Klo s, (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) * (A k * B k) := by
    refine Finset.sum_le_sum ?_
    intro k _hk
    exact mul_le_mul_of_nonneg_left (avsum_mul_le_sqrt_mul_sqrt _ _ _)
      (Real.rpow_nonneg (by norm_num) _)
  have hweighted :=
    sum_scaleWeighted_mul_le (Klo := Klo) (s := s) (A := A) (B := B) (SE := SE)
      hSE (fun k _ ↦ Real.sqrt_nonneg _) (fun k hk ↦ hbound k hk)
  have hBsq : ∀ k, B k ^ 2 =
      avsum (alignedIndex q k s) (fun w ↦ load k w ^ 2) := by
    intro k
    rw [hB]
    exact Real.sq_sqrt (avsum_nonneg fun w _ ↦ sq_nonneg _)
  have hrow : ∑ k ∈ Finset.Icc Klo s, profileRowWeight k s * B k ^ 2 ≤
      rowPartial := by
    refine le_trans (le_of_eq ?_) hrowSum
    exact Finset.sum_congr rfl fun k _ ↦ by rw [hBsq k]
  have hgeom_nonneg :
      0 ≤ Real.sqrt (1 / (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))) := Real.sqrt_nonneg _
  have hfinal : |T| ≤
      Cd * Real.sqrt (1 / (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))) * SE *
        Real.sqrt rowPartial := by
    refine hT.trans ?_
    have hstep := hscale.trans (hweighted.trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrow)
        (mul_nonneg hgeom_nonneg hSE)))
    calc Cd * ∑ k ∈ Finset.Icc Klo s, (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) *
            avsum (alignedIndex q k s) (fun w ↦ energy k w * load k w)
        ≤ Cd * (Real.sqrt (1 / (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))) * SE *
            Real.sqrt rowPartial) := mul_le_mul_of_nonneg_left hstep hCd
      _ = Cd * Real.sqrt (1 / (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))) * SE *
            Real.sqrt rowPartial := by ring
  exact ofReal_abs_le_mul_row_rpow
    (mul_nonneg (mul_nonneg hCd hgeom_nonneg) hSE) hrowPartial hrowLe hfinal

/-! ## The four row instances -/

/-- The primal flux-half instance: the second term of the gradient-mean row
estimate. -/
theorem ofReal_abs_scaleSum_flux_le_mul_profilePrimalHattedEarlierRow_rpow
    (P : Measure (CoeffSpace d)) (q h : Mat d) (Klo s : ℤ) (Pcen Qcen : Vec d)
    (energy : ℤ → (Fin d → ℤ) → ℝ) {SE Cd T : ℝ}
    (hSE : 0 ≤ SE) (hCd : 0 ≤ Cd)
    (hbound : ∀ k ∈ Finset.Icc Klo s,
      Real.sqrt (avsum (alignedIndex q k s) (fun w ↦ energy k w ^ 2)) ≤ SE)
    (hT : |T| ≤ Cd * ∑ k ∈ Finset.Icc Klo s, (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) *
      avsum (alignedIndex q k s) (fun w ↦ energy k w *
        profileSchurLoadFlux
          (profileHattedBlock h (annealedBlock P (adaptedCellAt q k w))) Qcen)) :
    ENNReal.ofReal |T| ≤
      ENNReal.ofReal
          (Cd * Real.sqrt (1 / (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))) * SE) *
        profilePrimalHattedEarlierRow P q h s Pcen Qcen ^ (1 / 2 : ℝ) :=
  ofReal_abs_scaleSum_le_mul_row_rpow q Klo s energy
    (fun k w ↦ profileSchurLoadFlux
      (profileHattedBlock h (annealedBlock P (adaptedCellAt q k w))) Qcen)
    hSE hCd (profilePrimalHattedRowPartial_nonneg P q h Klo s Pcen Qcen)
    (sum_rowWeight_avsum_sq_le q Klo s Pcen Qcen _ _
      (fun _ _ ↦ sq_profileSchurLoadFlux_le_profileSchurLoad _ Pcen Qcen))
    (le_iSup (fun K : ℤ ↦
      ENNReal.ofReal (profilePrimalHattedRowPartial P q h K s Pcen Qcen)) Klo)
    hbound hT

/-- The primal gradient-half instance: the second term of the flux-mean row
estimate. -/
theorem ofReal_abs_scaleSum_gradient_le_mul_profilePrimalHattedEarlierRow_rpow
    (P : Measure (CoeffSpace d)) (q h : Mat d) (Klo s : ℤ) (Pcen Qcen : Vec d)
    (energy : ℤ → (Fin d → ℤ) → ℝ) {SE Cd T : ℝ}
    (hSE : 0 ≤ SE) (hCd : 0 ≤ Cd)
    (hbound : ∀ k ∈ Finset.Icc Klo s,
      Real.sqrt (avsum (alignedIndex q k s) (fun w ↦ energy k w ^ 2)) ≤ SE)
    (hT : |T| ≤ Cd * ∑ k ∈ Finset.Icc Klo s, (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) *
      avsum (alignedIndex q k s) (fun w ↦ energy k w *
        profileSchurLoadGradient
          (profileHattedBlock h (annealedBlock P (adaptedCellAt q k w))) Pcen)) :
    ENNReal.ofReal |T| ≤
      ENNReal.ofReal
          (Cd * Real.sqrt (1 / (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))) * SE) *
        profilePrimalHattedEarlierRow P q h s Pcen Qcen ^ (1 / 2 : ℝ) :=
  ofReal_abs_scaleSum_le_mul_row_rpow q Klo s energy
    (fun k w ↦ profileSchurLoadGradient
      (profileHattedBlock h (annealedBlock P (adaptedCellAt q k w))) Pcen)
    hSE hCd (profilePrimalHattedRowPartial_nonneg P q h Klo s Pcen Qcen)
    (sum_rowWeight_avsum_sq_le q Klo s Pcen Qcen _ _
      (fun _ _ ↦ sq_profileSchurLoadGradient_le_profileSchurLoad _ Pcen Qcen))
    (le_iSup (fun K : ℤ ↦
      ENNReal.ofReal (profilePrimalHattedRowPartial P q h K s Pcen Qcen)) Klo)
    hbound hT

/-- The coefficient-transpose flux-half instance. -/
theorem ofReal_abs_scaleSum_flux_le_mul_profileAdjointHattedEarlierRow_rpow
    (P : Measure (CoeffSpace d)) (q h : Mat d) (Klo s : ℤ) (Pcen Qcen : Vec d)
    (energy : ℤ → (Fin d → ℤ) → ℝ) {SE Cd T : ℝ}
    (hSE : 0 ≤ SE) (hCd : 0 ≤ Cd)
    (hbound : ∀ k ∈ Finset.Icc Klo s,
      Real.sqrt (avsum (alignedIndex q k s) (fun w ↦ energy k w ^ 2)) ≤ SE)
    (hT : |T| ≤ Cd * ∑ k ∈ Finset.Icc Klo s, (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) *
      avsum (alignedIndex q k s) (fun w ↦ energy k w *
        profileSchurLoadFlux
          (profileHattedAdjointBlock h
            (annealedBlock P (adaptedCellAt q k w))) Qcen)) :
    ENNReal.ofReal |T| ≤
      ENNReal.ofReal
          (Cd * Real.sqrt (1 / (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))) * SE) *
        profileAdjointHattedEarlierRow P q h s Pcen Qcen ^ (1 / 2 : ℝ) :=
  ofReal_abs_scaleSum_le_mul_row_rpow q Klo s energy
    (fun k w ↦ profileSchurLoadFlux
      (profileHattedAdjointBlock h (annealedBlock P (adaptedCellAt q k w))) Qcen)
    hSE hCd (profileAdjointHattedRowPartial_nonneg P q h Klo s Pcen Qcen)
    (sum_rowWeight_avsum_sq_le q Klo s Pcen Qcen _ _
      (fun _ _ ↦ sq_profileSchurLoadFlux_le_profileSchurLoad _ Pcen Qcen))
    (le_iSup (fun K : ℤ ↦
      ENNReal.ofReal (profileAdjointHattedRowPartial P q h K s Pcen Qcen)) Klo)
    hbound hT

/-- The coefficient-transpose gradient-half instance. -/
theorem ofReal_abs_scaleSum_gradient_le_mul_profileAdjointHattedEarlierRow_rpow
    (P : Measure (CoeffSpace d)) (q h : Mat d) (Klo s : ℤ) (Pcen Qcen : Vec d)
    (energy : ℤ → (Fin d → ℤ) → ℝ) {SE Cd T : ℝ}
    (hSE : 0 ≤ SE) (hCd : 0 ≤ Cd)
    (hbound : ∀ k ∈ Finset.Icc Klo s,
      Real.sqrt (avsum (alignedIndex q k s) (fun w ↦ energy k w ^ 2)) ≤ SE)
    (hT : |T| ≤ Cd * ∑ k ∈ Finset.Icc Klo s, (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) *
      avsum (alignedIndex q k s) (fun w ↦ energy k w *
        profileSchurLoadGradient
          (profileHattedAdjointBlock h
            (annealedBlock P (adaptedCellAt q k w))) Pcen)) :
    ENNReal.ofReal |T| ≤
      ENNReal.ofReal
          (Cd * Real.sqrt (1 / (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))) * SE) *
        profileAdjointHattedEarlierRow P q h s Pcen Qcen ^ (1 / 2 : ℝ) :=
  ofReal_abs_scaleSum_le_mul_row_rpow q Klo s energy
    (fun k w ↦ profileSchurLoadGradient
      (profileHattedAdjointBlock h (annealedBlock P (adaptedCellAt q k w))) Pcen)
    hSE hCd (profileAdjointHattedRowPartial_nonneg P q h Klo s Pcen Qcen)
    (sum_rowWeight_avsum_sq_le q Klo s Pcen Qcen _ _
      (fun _ _ ↦ sq_profileSchurLoadGradient_le_profileSchurLoad _ Pcen Qcen))
    (le_iSup (fun K : ℤ ↦
      ENNReal.ofReal (profileAdjointHattedRowPartial P q h K s Pcen Qcen)) Klo)
    hbound hT

end

end HCPolySupport.HighContrast.Response
