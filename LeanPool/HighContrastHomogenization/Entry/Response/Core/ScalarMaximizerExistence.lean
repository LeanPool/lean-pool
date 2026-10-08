/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AdaptedDomainBridge
public import LeanPool.HighContrastHomogenization.Provider.Response.ResponseCongruence

/-!
# High-contrast homogenization: Entry.Response.Core.ScalarMaximizerExistence

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Existence of the canonical scalar maximizer

This file proves existence of the canonical scalar maximizer on an adapted cell for each of the
recentred coefficient `a_- = a - g` and its adjoint `a_+ = aᵀ + g`. It shows the set defining the
weak response energy `respWeakEnergy` as a supremum is bounded above — both in general and for
each of the two recentred coefficients and their associated `respWMinus`/`respWPlus` families —
and that this energy equals the supremum over that set. Along the way it records that the
Chapter-2 coefficient functional on an elliptic field is well defined and that the cell average
respects almost-everywhere equality of the underlying field. This is the scalar-maximizer input
to the response transfer `p.response.transfer`.
-/

section
/-!
## Maximizer existence on adapted cells

This file proves existence of canonical scalar maximizers on adapted cells for the recentred
coefficient `a_- = a - g` and its adjoint `a_+ = a^t + g`, and the boundedness of the defining
set of `respWeakEnergy`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
theorem adaptedCellTranslate_zero (q : Mat d) (j : ℤ) :
    HighContrast.adaptedCellTranslate q j 0 = HighContrast.adaptedCell q j := by
  ext x
  simp [HighContrast.adaptedCellTranslate]

omit [NeZero d] in
theorem volumeAverage_scalarResponseIntegrand_congr {U : Set (Vec d)} {a b : CoeffField d}
    (h : a =ᵐ[volumeMeasureOn U] b) (p q : Vec d)
    (u : AHarmonicFunction a U) (v : AHarmonicFunction b U)
    (hgrad : ∀ x, u.toH1.grad x = v.toH1.grad x) :
    volumeAverage U (scalarResponseIntegrand U a p q u) =
      volumeAverage U (scalarResponseIntegrand U b p q v) := by
  unfold volumeAverage
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [h] with x hx
  simp [scalarResponseIntegrand, hx, hgrad x]

omit [NeZero d] in
theorem nonempty_scalarCanonicalMaximizer_of_aeEq {U : Set (Vec d)} {a b : CoeffField d}
    (h : a =ᵐ[volumeMeasureOn U] b) (p q : Vec d)
    (hv : Nonempty (ScalarCanonicalMaximizer U p q a)) :
    Nonempty (ScalarCanonicalMaximizer U p q b) := by
  obtain ⟨v⟩ := hv
  refine ⟨⟨⟨Response.aHarmonicOfAEEq h v.toAHarmonicFunctionMeanZero.toAHarmonicFunction,
      v.toAHarmonicFunctionMeanZero.meanZero⟩, ?_⟩⟩
  intro w
  have key := v.isMaximizer (Response.aHarmonicOfAEEq h.symm w)
  have h1 : volumeAverage U (scalarResponseIntegrand U b p q w) =
      volumeAverage U (scalarResponseIntegrand U a p q (Response.aHarmonicOfAEEq h.symm w)) :=
    volumeAverage_scalarResponseIntegrand_congr h.symm p q w _ (fun _ => rfl)
  have h2 : volumeAverage U
        (scalarResponseIntegrand U a p q v.toAHarmonicFunctionMeanZero.toAHarmonicFunction) =
      volumeAverage U (scalarResponseIntegrand U b p q
        (Response.aHarmonicOfAEEq h v.toAHarmonicFunctionMeanZero.toAHarmonicFunction)) :=
    volumeAverage_scalarResponseIntegrand_congr h p q _ _ (fun _ => rfl)
  rw [h1, ← h2]
  exact key

omit [NeZero d] in
/-- Existence of a canonical maximizer for `a_- = a - g` on `U_t`
(`p.response.transfer`, `e.response.energy.and.defect`). -/
theorem nonempty_scalarCanonicalMaximizer_respCoeffMinus (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d) :
    Nonempty (ScalarCanonicalMaximizer (HighContrast.adaptedCell q t) p r (respCoeffMinus F a))
      := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq t 0 a
  rw [adaptedCellTranslate_zero] at hEll
  have hEll' := isEllipticFieldOn_sub_skew hEll (respg F) (respg_isSkew F)
  have hbase : Nonempty (ScalarCanonicalMaximizer (HighContrast.adaptedCell q t) p r
      (fun x => f x - respg F)) :=
    ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain
      (Recurrence.adaptedCell_nonempty q t) (adaptedCell_isOpenBoundedConvexDomain q hq t) hEll' p r
  refine nonempty_scalarCanonicalMaximizer_of_aeEq ?_ p r hbase
  refine MeasureTheory.ae_restrict_of_ae ?_
  filter_upwards [hae] with x hx
  simp [respCoeffMinus, hx]

omit [NeZero d] in
/-- The adjoint twin for `a_+ = a^t + g`. -/
theorem nonempty_scalarCanonicalMaximizer_respCoeffPlus (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d) :
    Nonempty (ScalarCanonicalMaximizer (HighContrast.adaptedCell q t) p r (respCoeffPlus F a)) := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq t 0 a
  rw [adaptedCellTranslate_zero] at hEll
  have hEll' := isEllipticFieldOn_transpose_add_skew hEll (respg F) (respg_isSkew F)
  have hbase : Nonempty (ScalarCanonicalMaximizer (HighContrast.adaptedCell q t) p r
      (fun x => matTranspose (f x) + respg F)) :=
    ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain
      (Recurrence.adaptedCell_nonempty q t) (adaptedCell_isOpenBoundedConvexDomain q hq t) hEll' p r
  refine nonempty_scalarCanonicalMaximizer_of_aeEq ?_ p r hbase
  refine MeasureTheory.ae_restrict_of_ae ?_
  filter_upwards [hae] with x hx
  simp [respCoeffPlus, hx]

/-! ## `BddAbove` for the `sSup` defining `respWeakEnergy`

The lemmas `standardCell_subset_centeredCube_of_mem_triadicIndexBox` and
`adaptedCellAtCenter_subset_adaptedCell` below are also declared, under the same names, in
`ScaleAverageSeminorm.lean`, which imports this file. The declarations here provide the copies
needed in this file to prove `bddAbove_respWeakEnergySet`. -/

-- The scale-`t-n` grid cells indexed by `triadicIndexBox d n` sit inside `U_t`.
omit [NeZero d] in
theorem standardCell_subset_centeredCube_of_mem_triadicIndexBox (t : ℤ) (n : ℕ)
    {w : Fin d → ℤ} (hw : w ∈ triadicIndexBox d n) :
    HighContrast.standardCell d (t - (n : ℤ)) w ⊆ HighContrast.centeredCube d t := by
  intro x hx
  rw [Recurrence.mem_standardCell_iff] at hx
  rw [Recurrence.mem_centeredCube_iff]
  intro i
  obtain ⟨h1, h2⟩ := hx i
  have hwi : w i ∈ Finset.Icc (-(((3 ^ n - 1) / 2 : ℕ) : ℤ)) (((3 ^ n - 1) / 2 : ℕ) : ℤ) :=
    (Fintype.mem_piFinset.mp hw) i
  rw [Finset.mem_Icc] at hwi
  set m : ℕ := (3 ^ n - 1) / 2 with hm
  have hone : 1 ≤ (3 : ℕ) ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hdvd : 2 ∣ (3 : ℕ) ^ n - 1 := by
    have hodd : Odd ((3 : ℕ) ^ n) := Odd.pow (by decide)
    exact (Nat.Odd.sub_odd hodd odd_one).two_dvd
  have hm2 : 2 * m = (3 : ℕ) ^ n - 1 := by
    rw [hm, Nat.mul_div_cancel' hdvd]
  have hmR : 2 * (m : ℝ) = (3 : ℝ) ^ n - 1 := by
    have := congrArg (fun k : ℕ => (k : ℝ)) hm2
    push_cast [Nat.cast_sub hone] at this
    linarith only [this]
  set c : ℝ := (3 : ℝ) ^ (t - (n : ℤ)) with hcdef
  have hc : 0 < c := by positivity
  have h3n : ((3 : ℝ) ^ (n : ℤ)) * c = (3 : ℝ) ^ t := by
    rw [hcdef, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring_nf
  have h3nn : ((3 : ℝ) ^ (n : ℤ)) = (3 : ℝ) ^ n := by
    exact zpow_natCast (3 : ℝ) n
  have hkey : ((m : ℝ) + 1 / 2) * c = 1 / 2 * (3 : ℝ) ^ t := by
    have hmhalf : (m : ℝ) + 1 / 2 = 1 / 2 * (3 : ℝ) ^ n := by linarith only [hmR]
    rw [hmhalf, ← h3nn, mul_assoc, h3n]
  have hwloR : -((m : ℝ)) ≤ (w i : ℝ) := by exact_mod_cast hwi.1
  have hwhiR : (w i : ℝ) ≤ (m : ℝ) := by exact_mod_cast hwi.2
  have hup : ((w i : ℝ) + 1 / 2) * c ≤ ((m : ℝ) + 1 / 2) * c :=
    mul_le_mul_of_nonneg_right (by linarith only [hwhiR]) hc.le
  have hlo : (-((m : ℝ)) - 1 / 2) * c ≤ ((w i : ℝ) - 1 / 2) * c :=
    mul_le_mul_of_nonneg_right (by linarith only [hwloR]) hc.le
  have hlokey : (-((m : ℝ)) - 1 / 2) * c = -(1 / 2) * (3 : ℝ) ^ t := by
    have : (-((m : ℝ)) - 1 / 2) * c = -(((m : ℝ) + 1 / 2) * c) := by ring
    rw [this, hkey]; ring
  constructor
  · calc -(1 / 2 : ℝ) * (3 : ℝ) ^ t = (-((m : ℝ)) - 1 / 2) * c := hlokey.symm
      _ ≤ ((w i : ℝ) - 1 / 2) * c := hlo
      _ < x i := h1
  · calc x i < ((w i : ℝ) + 1 / 2) * c := h2
      _ ≤ ((m : ℝ) + 1 / 2) * c := hup
      _ = 1 / 2 * (3 : ℝ) ^ t := hkey

omit [NeZero d] in
theorem adaptedCellAtCenter_subset_adaptedCell (q : Mat d) (t : ℤ) (n : ℕ) {w : Fin d → ℤ}
    (hw : w ∈ triadicIndexBox d n) :
    adaptedCellAtCenter q (t - (n : ℤ)) w ⊆ HighContrast.adaptedCell q t := by
  rw [Geometry.adaptedCellAtCenter_eq_affine_standardCell]
  rintro x ⟨v, hv, rfl⟩
  exact ⟨v, standardCell_subset_centeredCube_of_mem_triadicIndexBox t n hw hv, rfl⟩

/-- The defining set of `respWeakEnergy` (`ResponseBlockObjects.lean`), named so that its
boundedness can be stated. -/
@[expose]
def respWeakEnergySet (P : Measure (CoeffSpace d)) (qq : Mat d) (t : ℤ) (M0 : BlockMat d)
    (p q' : Vec d) (b : CoeffSpace d → CoeffField d) (Y : BlockVec d) : Set ℝ :=
  {c : ℝ |
    ∃ u : (a : CoeffSpace d) → AHarmonicFunction (b a) (HighContrast.adaptedCell qq t),
      (∀ a, IsResponseMaximizer (HighContrast.adaptedCell qq t) p q' (b a) (u a)) ∧
      c = (3 : ℝ) ^ (-(t : ℝ)) *
        ∫ a, besovSeminorm t (fun n z =>
              blockMatVecMul (blockSqrt M0)
                (cellAverage (adaptedCellAtCenter qq (t - (n : ℤ)) z) (optimizerField (b a) (u a)) -
                  Y)) ^ 2 ∂P}

omit [NeZero d] in
theorem respWeakEnergy_eq_sSup_respWeakEnergySet (P : Measure (CoeffSpace d)) (qq : Mat d)
    (t : ℤ) (M0 : BlockMat d) (p q' : Vec d) (b : CoeffSpace d → CoeffField d) (Y : BlockVec d) :
    respWeakEnergy P qq t M0 p q' b Y = sSup (respWeakEnergySet P qq t M0 p q' b Y) := rfl

/-- A Chapter-2 coefficient object from a pointwise elliptic field on the domain. -/
@[expose]
def coeffOnOfIsEllipticFieldOn {U : Book.Ch02.Domain d} {lam Lam : ℝ} {f : CoeffField d}
    (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) f) : Book.Ch02.CoeffOn U where
  toCoeffField := f
  lam := lam
  Lam := Lam
  lam_pos := hlam
  lam_le_Lam := hle
  aeStronglyMeasurable := by
    classical
    intro i j
    have heq : (fun x : Vec d => restrictCoeffField (U : Set (Vec d)) f x i j) =
        fun x : Vec d => (if x ∈ (U : Set (Vec d)) then f x i j else 0) := by
      funext x
      by_cases hx : x ∈ (U : Set (Vec d)) <;> simp [restrictCoeffField, hx]
    rw [heq]
    exact (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      hEll.1)).aestronglyMeasurable)
  aeElliptic := by
    filter_upwards [MeasureTheory.ae_restrict_mem U.measurableSet] with x hx
    exact hEll.2 x hx

omit [NeZero d] in
theorem book_isResponseMaximizer_iff {U : Book.Ch02.Domain d} {a : Book.Ch02.CoeffOn U}
    {p q : Vec d} {v : Book.Ch02.Solution U a} :
    Book.Ch02.IsResponseMaximizer U a p q v ↔
      IsResponseMaximizer (U : Set (Vec d)) p q a.toCoeffField v := Iff.rfl

omit [NeZero d] in
theorem besovSeminorm_congr {t : ℤ} {avg1 avg2 : ℕ → (Fin d → ℤ) → BlockVec d}
    (h : ∀ n : ℕ, ∀ w ∈ triadicIndexBox d n, avg1 n w = avg2 n w) :
    besovSeminorm t avg1 = besovSeminorm t avg2 := by
  unfold besovSeminorm
  refine tsum_congr fun n => ?_
  have hs : ∑ w ∈ triadicIndexBox d n, blockVecDot (avg1 n w) (avg1 n w) =
      ∑ w ∈ triadicIndexBox d n, blockVecDot (avg2 n w) (avg2 n w) :=
    Finset.sum_congr rfl fun w hw => by rw [h n w hw]
  rw [hs]

omit [NeZero d] in
theorem cellAverage_congr_ae {V U : Set (Vec d)} (hVU : V ⊆ U) {X Z : Vec d → BlockVec d}
    (h : X =ᵐ[volumeMeasureOn U] Z) : cellAverage V X = cellAverage V Z := by
  have h2 : X =ᵐ[volumeMeasureOn V] Z :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) h
  have hfst : (fun i => volumeAverage V fun x => (X x).1 i) =
      fun i => volumeAverage V fun x => (Z x).1 i := by
    funext i
    unfold volumeAverage
    congr 1
    exact MeasureTheory.integral_congr_ae
      (h2.mono fun x hx => congrArg (fun v : BlockVec d => v.1 i) hx)
  have hsnd : (fun i => volumeAverage V fun x => (X x).2 i) =
      fun i => volumeAverage V fun x => (Z x).2 i := by
    funext i
    unfold volumeAverage
    congr 1
    exact MeasureTheory.integral_congr_ae
      (h2.mono fun x hx => congrArg (fun v : BlockVec d => v.2 i) hx)
  simp only [cellAverage, hfst, hsnd]

omit [NeZero d] in
/-- The defining set of `respWeakEnergy` is bounded above: by Chapter-2 a.e. gradient
uniqueness any two admissible maximizer families give the same value. -/
theorem bddAbove_respWeakEnergySet (P : Measure (CoeffSpace d)) (qq : Mat d) (hq : IsUnit qq)
    (t : ℤ) (M0 : BlockMat d) (p q' : Vec d) (b : CoeffSpace d → CoeffField d) (Y : BlockVec d)
    (hb : ∀ a : CoeffSpace d, ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (HighContrast.adaptedCell qq t) f ∧
        b a =ᵐ[volumeMeasureOn (HighContrast.adaptedCell qq t)] f) :
    BddAbove (respWeakEnergySet P qq t M0 p q' b Y) := by
  classical
  set U : Set (Vec d) := HighContrast.adaptedCell qq t with hU
  set Udom : Book.Ch02.Domain d :=
    { carrier := U
      isDomain := adaptedCell_isOpenBoundedConvexDomain qq hq t
      nonempty := Recurrence.adaptedCell_nonempty qq t } with hUdom
  have hgrad : ∀ (a : CoeffSpace d) (v w : AHarmonicFunction (b a) U),
      IsResponseMaximizer U p q' (b a) v → IsResponseMaximizer U p q' (b a) w →
      v.toH1.grad =ᵐ[volumeMeasureOn U] w.toH1.grad := by
    intro a v w hv hw
    obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ := hb a
    set A : Book.Ch02.CoeffOn Udom := coeffOnOfIsEllipticFieldOn (U := Udom) hlam hle hEll with hA
    have hvT : IsResponseMaximizer U p q' f (Response.aHarmonicOfAEEq hae v) := by
      intro z
      have key := hv (Response.aHarmonicOfAEEq hae.symm z)
      have h1 : volumeAverage U (scalarResponseIntegrand U f p q' z) =
          volumeAverage U (scalarResponseIntegrand U (b a) p q'
            (Response.aHarmonicOfAEEq hae.symm z)) :=
        volumeAverage_scalarResponseIntegrand_congr hae.symm p q' z _ (fun _ => rfl)
      have h2 : volumeAverage U (scalarResponseIntegrand U (b a) p q' v) =
          volumeAverage U (scalarResponseIntegrand U f p q'
            (Response.aHarmonicOfAEEq hae v)) :=
        volumeAverage_scalarResponseIntegrand_congr hae p q' v _ (fun _ => rfl)
      rw [h1, ← h2]
      exact key
    have hwT : IsResponseMaximizer U p q' f (Response.aHarmonicOfAEEq hae w) := by
      intro z
      have key := hw (Response.aHarmonicOfAEEq hae.symm z)
      have h1 : volumeAverage U (scalarResponseIntegrand U f p q' z) =
          volumeAverage U (scalarResponseIntegrand U (b a) p q'
            (Response.aHarmonicOfAEEq hae.symm z)) :=
        volumeAverage_scalarResponseIntegrand_congr hae.symm p q' z _ (fun _ => rfl)
      have h2 : volumeAverage U (scalarResponseIntegrand U (b a) p q' w) =
          volumeAverage U (scalarResponseIntegrand U f p q'
            (Response.aHarmonicOfAEEq hae w)) :=
        volumeAverage_scalarResponseIntegrand_congr hae p q' w _ (fun _ => rfl)
      rw [h1, ← h2]
      exact key
    exact Book.Ch02.sameGradientAE_of_isResponseMaximizer (U := Udom) (a := A)
      (v := Response.aHarmonicOfAEEq hae v) (w := Response.aHarmonicOfAEEq hae w)
      (book_isResponseMaximizer_iff.mpr hvT) (book_isResponseMaximizer_iff.mpr hwT)
  have hsub : (respWeakEnergySet P qq t M0 p q' b Y).Subsingleton := by
    rintro c1 ⟨u1, hu1, rfl⟩ c2 ⟨u2, hu2, rfl⟩
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    have hof : optimizerField (b a) (u1 a) =ᵐ[volumeMeasureOn U] optimizerField (b a) (u2 a) := by
      filter_upwards [hgrad a (u1 a) (u2 a) (hu1 a) (hu2 a)] with x hx
      simp [optimizerField, hx]
    have : besovSeminorm t (fun n z => blockMatVecMul (blockSqrt M0)
            (cellAverage (adaptedCellAtCenter qq (t - (n : ℤ)) z) (optimizerField (b a) (u1 a))
              - Y)) =
        besovSeminorm t (fun n z => blockMatVecMul (blockSqrt M0)
            (cellAverage (adaptedCellAtCenter qq (t - (n : ℤ)) z) (optimizerField (b a) (u2 a))
              - Y)) := by
      refine besovSeminorm_congr fun n w hw => ?_
      rw [cellAverage_congr_ae (adaptedCellAtCenter_subset_adaptedCell qq t n hw) hof]
    exact congrArg (fun r : ℝ => r ^ 2) this
  rcases Set.eq_empty_or_nonempty (respWeakEnergySet P qq t M0 p q' b Y) with he | ⟨c, hc⟩
  · rw [he]; exact bddAbove_empty
  · exact ⟨c, fun y hy => le_of_eq (hsub hy hc)⟩

omit [NeZero d] in
/-- The defining set of `respWeakEnergy` for `a_- = a - g` is bounded above. -/
theorem bddAbove_respWeakEnergySet_respCoeffMinus (P : Measure (CoeffSpace d)) (qq : Mat d)
    (hq : IsUnit qq) (t : ℤ) (M0 : BlockMat d) (p q' : Vec d) (F : BlockMat d) (Y : BlockVec d) :
    BddAbove (respWeakEnergySet P qq t M0 p q' (respCoeffMinus F) Y) := by
  refine bddAbove_respWeakEnergySet P qq hq t M0 p q' _ Y ?_
  intro a
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted qq hq t 0 a
  rw [adaptedCellTranslate_zero] at hEll
  refine ⟨lam, 2 * Lam + 2 * ‖respg F‖ ^ 2 / lam, fun x => f x - respg F, hlam, ?_,
    isEllipticFieldOn_sub_skew hEll _ (respg_isSkew F), ?_⟩
  · have hn : (0:ℝ) ≤ 2 * ‖respg F‖ ^ 2 / lam := by positivity
    linarith only [hlam, hle, hn]
  · refine MeasureTheory.ae_restrict_of_ae ?_
    filter_upwards [hae] with x hx
    simp [respCoeffMinus, hx]

omit [NeZero d] in
/-- The defining set of `respWeakEnergy` for `a_+ = a^t + g` is bounded above. -/
theorem bddAbove_respWeakEnergySet_respCoeffPlus (P : Measure (CoeffSpace d)) (qq : Mat d)
    (hq : IsUnit qq) (t : ℤ) (M0 : BlockMat d) (p q' : Vec d) (F : BlockMat d) (Y : BlockVec d) :
    BddAbove (respWeakEnergySet P qq t M0 p q' (respCoeffPlus F) Y) := by
  refine bddAbove_respWeakEnergySet P qq hq t M0 p q' _ Y ?_
  intro a
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted qq hq t 0 a
  rw [adaptedCellTranslate_zero] at hEll
  refine ⟨lam, 2 * Lam + 2 * ‖respg F‖ ^ 2 / lam, fun x => matTranspose (f x) + respg F, hlam, ?_,
    isEllipticFieldOn_transpose_add_skew hEll _ (respg_isSkew F), ?_⟩
  · have hn : (0:ℝ) ≤ 2 * ‖respg F‖ ^ 2 / lam := by positivity
    linarith only [hlam, hle, hn]
  · refine MeasureTheory.ae_restrict_of_ae ?_
    filter_upwards [hae] with x hx
    simp [respCoeffPlus, hx]

omit [NeZero d] in
/-- The `sSup` in `respWMinus` is over a set bounded above. -/
theorem bddAbove_respWeakEnergySet_respWMinus (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (t : ℤ) (e : Vec d) (hgrid : IsUnit (respGrid jStar F)) :
    BddAbove (respWeakEnergySet P (respGrid jStar F) t (respM0 F)
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F)
      (respYMinus P jStar F t e)) :=
  bddAbove_respWeakEnergySet_respCoeffMinus _ _ hgrid _ _ _ _ _ _

omit [NeZero d] in
/-- The `sSup` in `respWPlus` is over a set bounded above. -/
theorem bddAbove_respWeakEnergySet_respWPlus (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (t : ℤ) (e : Vec d) (hgrid : IsUnit (respGrid jStar F)) :
    BddAbove (respWeakEnergySet P (respGrid jStar F) t (respM0 F)
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F)
      (respYPlus P jStar F t e)) :=
  bddAbove_respWeakEnergySet_respCoeffPlus _ _ hgrid _ _ _ _ _ _

/-! ## AK.HC (2.32), the optimizer-mean identity `blockAverage_eq`, stated on
`Book.Ch02.Domain`; `Internal.Ch02.BookCh02.responseBasicVariationalIdentitiesTheory`.
Paper `e.response.energy.and.defect` (`Y = (I + R A) x`), the optimizer-mean identity. -/

end

end HCPolySupport.HighContrast.Multiscale
end
