/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.VariationalIdentities
public import LeanPool.HighContrastHomogenization.Provider.Sharp.ReflectionOrder

/-!
# High-contrast homogenization: Provider.Response.EnergyMap

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The coarse energy map on the doubled response space

The second half of the deterministic input to the weak-norm estimate for the
optimizer state is the coarse energy-map estimate.  The paper derives it by
combining the doubled splitting [Armstrong–Kuusi, (2.17)], the row-swap identity
[Armstrong–Kuusi, (2.18)], and the doubled variational formula [Armstrong–Kuusi, (2.20)], then
putting the first load equal to zero:
`½Q·𝐀_*^{-1}(V)Q = max_{Z ∈ 𝒮(V;a)} ⨍_V(-½Z·𝐀Z + Q·Z)`.  Evaluating at a fixed
`Y ∈ 𝒮(V;a)` and taking the supremum over `Q` gives the energy bound for the
dual block, `½y·𝐀_*(V)y ≤ ½⨍_V Y·𝐀Y` with `y = (Y)_V`, and its metric form
follows by comparing `M_0` with `𝐀_*(V)`.

All three steps are carried out here on an arbitrary Chapter 2 domain.  The
supremum over `Q` is taken at the single admissible choice `Q = 𝐀_*(V)y`, which
is what makes the argument finite; the two inverse clauses of
`BlockCoarseMatrixTheory` supply `𝐀_*^{-1}𝐀_* = I`.

The Loewner encoding of the matrix norms is the one fixed by `Setup/Moments`:
`|M_0^{-1/2}HM_0^{-1/2}| ≤ c` is read as `H ≤ cM_0`, so the metric form is
stated with that hypothesis rather than with a spectral norm.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02

noncomputable section

variable {d : ℕ}

/-! ## The doubled zero load -/

/-- Pairing against the zero doubled vector. -/
@[simp] theorem blockVecDot_zero_left (X : BlockVec d) :
    blockVecDot (0 : BlockVec d) X = 0 := by
  show vecDot (0 : Vec d) X.1 + vecDot (0 : Vec d) X.2 = 0
  rw [vecDot_zero_left, vecDot_zero_left, add_zero]

/-! ## Averages of a doubled field against a fixed load -/

/-- The normalized average of a scalar sum splits, given integrability. -/
theorem average_add {U : Domain d} {f g : Vec d → ℝ}
    (hf : MeasureTheory.IntegrableOn f (U : Set (Vec d)) MeasureTheory.volume)
    (hg : MeasureTheory.IntegrableOn g (U : Set (Vec d)) MeasureTheory.volume) :
    Book.Ch02.average U (fun x => f x + g x) =
      Book.Ch02.average U f + Book.Ch02.average U g := by
  unfold Book.Ch02.average
  rw [MeasureTheory.integral_add hf hg]
  ring

/-- A component of a square-integrable vector field is integrable on a Chapter 2
domain. -/
theorem integrableOn_component {U : Domain d} {F : Vec d → Vec d}
    (hF : MemVectorL2 (U : Set (Vec d)) F) (i : Fin d) :
    MeasureTheory.IntegrableOn (fun x => F x i) (U : Set (Vec d)) MeasureTheory.volume := by
  have hcomp : MeasureTheory.MemLp (fun x => F x i) 2
      (volumeMeasureOn (U : Set (Vec d))) := by
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).comp_memLp' hF
    simpa using! this
  exact hcomp.integrable (by norm_num)

/-- **The average commutes with pairing against a fixed vector**: `(c·F)_U =
c·(F)_U` for the volume average over a domain. -/
theorem average_vecDot_const {U : Domain d} (c : Vec d) {F : Vec d → Vec d}
    (hF : MemVectorL2 (U : Set (Vec d)) F) :
    Book.Ch02.average U (fun x => vecDot c (F x)) = vecDot c (Book.Ch02.averageVec U F) := by
  have hsum : ∫ x in (U : Set (Vec d)), (∑ i : Fin d, c i * F x i) ∂MeasureTheory.volume =
      ∑ i : Fin d, c i * ∫ x in (U : Set (Vec d)), F x i ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_finsetSum _
      (fun i _ => (integrableOn_component hF i).const_mul (c i))]
    exact Finset.sum_congr rfl fun i _ => MeasureTheory.integral_const_mul _ _
  show (MeasureTheory.volume (U : Set (Vec d))).toReal⁻¹ *
      ∫ x in (U : Set (Vec d)), (∑ i : Fin d, c i * F x i) ∂MeasureTheory.volume =
    ∑ i : Fin d, c i *
      ((MeasureTheory.volume (U : Set (Vec d))).toReal⁻¹ *
        ∫ x in (U : Set (Vec d)), F x i ∂MeasureTheory.volume)
  rw [hsum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The average of a doubled field against a fixed load**: `(Q·Y)_U = Q·(Y)_U`,
the step that turns the doubled response value into a function of the cell
average `(Y)_U` alone. -/
theorem average_blockVecDot_const {U : Domain d} (Q : BlockVec d) (Y : DoubledField d)
    (hp : MemVectorL2 (U : Set (Vec d)) Y.potential)
    (hf : MemVectorL2 (U : Set (Vec d)) Y.flux) :
    Book.Ch02.average U (fun x => blockVecDot Q (Y.eval x)) =
      blockVecDot Q
        ((Book.Ch02.averageVec U Y.potential, Book.Ch02.averageVec U Y.flux) : BlockVec d) := by
  have hint1 : MeasureTheory.IntegrableOn (fun x => vecDot Q.1 (Y.potential x))
      (U : Set (Vec d)) MeasureTheory.volume := by
    refine MeasureTheory.integrable_finsetSum _ fun i _ => ?_
    exact (integrableOn_component hp i).const_mul (Q.1 i)
  have hint2 : MeasureTheory.IntegrableOn (fun x => vecDot Q.2 (Y.flux x))
      (U : Set (Vec d)) MeasureTheory.volume := by
    refine MeasureTheory.integrable_finsetSum _ fun i _ => ?_
    exact (integrableOn_component hf i).const_mul (Q.2 i)
  show Book.Ch02.average U (fun x => vecDot Q.1 (Y.potential x) + vecDot Q.2 (Y.flux x)) =
    vecDot Q.1 (Book.Ch02.averageVec U Y.potential) + vecDot Q.2 (Book.Ch02.averageVec U Y.flux)
  rw [average_add hint1 hint2, average_vecDot_const Q.1 hp, average_vecDot_const Q.2 hf]

/-! ## The doubled response at zero primal load -/

/-- **The doubled variational formula at zero first load**
([Armstrong–Kuusi, (2.17)], [Armstrong–Kuusi, (2.20)]):
`𝐉(V,0,Q;a) = ½Q·𝐀_*^{-1}(V)Q`. -/
theorem doubledResponseJ_zero_left {U : Domain d} (a : CoeffOn U) (Q : BlockVec d) :
    doubledResponseJ U a 0 Q =
      (1 / 2 : ℝ) *
        blockVecDot Q (blockMatVecMul (Book.Ch02.coarseStarredBlockMatrixInv U a) Q) := by
  have h := (Internal.Ch02.BookCh02.blockCoarseMatrixTheory U a).doubled_response_splitting 0 Q
  rw [h, blockVecDot_zero_left, blockVecDot_zero_left]
  ring

/-- **Every element of the response space is dominated by the doubled formula**:
for `Y ∈ 𝒮(V;a)`, the value `⨍_V(-½Y·𝐀Y + Q·Y)` is at most
`½Q·𝐀_*^{-1}(V)Q`.  The maximizer supplied by `DoubledResponseTheory` makes the
supremum a greatest element, so no boundedness argument is needed. -/
theorem doubledResponseValue_le {U : Domain d} (a : CoeffOn U) (Q : BlockVec d)
    {Y : DoubledField d} (hY : IsDoubledResponseField U a Y) :
    doubledResponseValue U a 0 Q Y ≤
      (1 / 2 : ℝ) *
        blockVecDot Q (blockMatVecMul (Book.Ch02.coarseStarredBlockMatrixInv U a) Q) := by
  obtain ⟨X, hX⟩ := (Internal.Ch02.BookCh02.doubledResponseTheory U a).maximizer_exists 0 Q
  have hgreat : IsGreatest (doubledResponseValueSet U a 0 Q)
      (doubledResponseValue U a 0 Q X) := by
    refine ⟨⟨X, hX.1, rfl⟩, ?_⟩
    rintro y ⟨Z, hZ, rfl⟩
    exact hX.2 Z hZ
  have hJ : doubledResponseJ U a 0 Q = doubledResponseValue U a 0 Q X := hgreat.csSup_eq
  rw [← doubledResponseJ_zero_left, hJ]
  exact hX.2 Y hY

/-- **The doubled response value at zero first load, expanded**: the value of a
response field `Y` is `Q·(Y)_V - ½⨍_V Y·𝐀Y`, the form in which the supremum over
`Q` is taken in the energy bound for the dual block. -/
theorem doubledResponseValue_zero_left_eq {U : Domain d} {lam Lam : ℝ} (a : CoeffOn U)
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) a.toCoeffField)
    (Q : BlockVec d) {Y : DoubledField d} (hY : IsDoubledResponseField U a Y) :
    doubledResponseValue U a 0 Q Y =
      blockVecDot Q
          ((Book.Ch02.averageVec U Y.potential,
            Book.Ch02.averageVec U Y.flux) : BlockVec d) -
        (1 / 2 : ℝ) *
          Book.Ch02.average U (fun x =>
            blockVecDot (Y.eval x) (blockMatVecMul (blockMatrixField a x) (Y.eval x))) := by
  have hp : MemVectorL2 (U : Set (Vec d)) Y.potential := hY.1.1.1
  have hf : MemVectorL2 (U : Set (Vec d)) Y.flux := hY.1.2.1
  have hblock : MemBlockL2 (U : Set (Vec d))
      (({ potential := Y.potential, flux := Y.flux } : BlockState d)).eval :=
    memBlockL2_blockField hp hf
  have hE : MeasureTheory.IntegrableOn (fun x =>
      -blockEnergyDensityAt a (Y.eval x) x) (U : Set (Vec d)) MeasureTheory.volume :=
    (blockEnergyDensity_integrableOn_of_memBlockL2_of_isEllipticFieldOn hblock hEll).neg
  have hQ : MeasureTheory.IntegrableOn (fun x => blockVecDot Q (Y.eval x))
      (U : Set (Vec d)) MeasureTheory.volume := by
    refine MeasureTheory.Integrable.add ?_ ?_
    · exact MeasureTheory.integrable_finsetSum _ fun i _ =>
        (integrableOn_component hp i).const_mul (Q.1 i)
    · exact MeasureTheory.integrable_finsetSum _ fun i _ =>
        (integrableOn_component hf i).const_mul (Q.2 i)
  have hval : doubledResponseValue U a 0 Q Y =
      Book.Ch02.average U (fun x =>
        -blockEnergyDensityAt a (Y.eval x) x + blockVecDot Q (Y.eval x)) := by
    unfold doubledResponseValue doubledResponseIntegrand
    congr 1
    funext x
    rw [blockVecDot_zero_left, sub_zero]
  have hhalf : Book.Ch02.average U (fun x => -blockEnergyDensityAt a (Y.eval x) x) =
      -((1 / 2 : ℝ) *
        Book.Ch02.average U (fun x =>
          blockVecDot (Y.eval x) (blockMatVecMul (blockMatrixField a x) (Y.eval x)))) := by
    unfold Book.Ch02.average blockEnergyDensityAt
    rw [MeasureTheory.integral_neg, MeasureTheory.integral_const_mul]
    ring
  rw [hval, average_add hE hQ, hhalf, average_blockVecDot_const Q Y hp hf]
  ring

/-! ## The energy map -/

/-- **The coarse energy-map estimate**, the energy bound for the dual block: for
every field `Y` in the doubled response space `𝒮(V;a)` with cell average
`y = (Y)_V`,
`½y·𝐀_*(V)y ≤ ½⨍_V Y·𝐀Y`.  The supremum over `Q` is realized at
`Q = 𝐀_*(V)y`. -/
theorem energy_map_le {U : Domain d} {lam Lam : ℝ} (a : CoeffOn U)
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) a.toCoeffField)
    {Y : DoubledField d} (hY : IsDoubledResponseField U a Y) :
    (1 / 2 : ℝ) *
        blockVecDot
          ((Book.Ch02.averageVec U Y.potential,
            Book.Ch02.averageVec U Y.flux) : BlockVec d)
          (blockMatVecMul (Book.Ch02.coarseStarredBlockMatrix U a)
            ((Book.Ch02.averageVec U Y.potential,
              Book.Ch02.averageVec U Y.flux) : BlockVec d)) ≤
      (1 / 2 : ℝ) *
        Book.Ch02.average U (fun x =>
          blockVecDot (Y.eval x) (blockMatVecMul (blockMatrixField a x) (Y.eval x))) := by
  set y : BlockVec d :=
    (Book.Ch02.averageVec U Y.potential, Book.Ch02.averageVec U Y.flux) with hy
  set E : ℝ := Book.Ch02.average U (fun x =>
    blockVecDot (Y.eval x) (blockMatVecMul (blockMatrixField a x) (Y.eval x))) with hE
  set Q : BlockVec d := blockMatVecMul (Book.Ch02.coarseStarredBlockMatrix U a) y with hQ
  have hinv : blockMatVecMul (Book.Ch02.coarseStarredBlockMatrixInv U a) Q = y := by
    rw [hQ, ← blockMatVecMul_blockMatMul,
      (Internal.Ch02.BookCh02.blockCoarseMatrixTheory U a).starred_right_inverse,
      blockMatVecMul_blockIdentity]
  have hle := doubledResponseValue_le a Q hY
  rw [doubledResponseValue_zero_left_eq a hEll Q hY, hinv] at hle
  have hcomm : blockVecDot Q y =
      blockVecDot y (blockMatVecMul (Book.Ch02.coarseStarredBlockMatrix U a) y) :=
    blockVecDot_comm _ _
  rw [hcomm] at hle
  linarith only [hle]

/-- **The metric form of the energy map**: once the diagonal metric is dominated
by the starred coarse block, `M_0 ≤ c𝐀_*(V)`, the metric
size of the cell average is controlled by the cell energy,
`|M_0^{1/2}(Y)_V|² ≤ c⨍_V Y·𝐀Y`.  The hypothesis is the Loewner encoding of the
comparison coefficient `|M_0^{1/2}𝐀_*^{-1}(V)M_0^{1/2}|` displayed. -/
theorem energy_map_metric_le {U : Domain d} {lam Lam : ℝ} (a : CoeffOn U)
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) a.toCoeffField)
    {Y : DoubledField d} (hY : IsDoubledResponseField U a Y) (m : Mat d) {c : ℝ}
    (hc : 0 ≤ c)
    (hcmp : BlockMatLoewnerLE (blockDiag m m⁻¹)
      (blockScale c (Book.Ch02.coarseStarredBlockMatrix U a))) :
    (1 / 2 : ℝ) *
        blockVecDot
          ((Book.Ch02.averageVec U Y.potential,
            Book.Ch02.averageVec U Y.flux) : BlockVec d)
          (blockMatVecMul (blockDiag m m⁻¹)
            ((Book.Ch02.averageVec U Y.potential,
              Book.Ch02.averageVec U Y.flux) : BlockVec d)) ≤
      c *
        ((1 / 2 : ℝ) *
          Book.Ch02.average U (fun x =>
            blockVecDot (Y.eval x) (blockMatVecMul (blockMatrixField a x) (Y.eval x)))) := by
  set y : BlockVec d :=
    (Book.Ch02.averageVec U Y.potential, Book.Ch02.averageVec U Y.flux) with hy
  have h1 := hcmp y
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at h1
  have h2 := energy_map_le a hEll hY
  have hprod := mul_le_mul_of_nonneg_left h2 hc
  linarith only [h1, hprod]

end

end Response
end HighContrast
end HCPolySupport
