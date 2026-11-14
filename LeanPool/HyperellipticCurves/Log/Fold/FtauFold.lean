/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.FoldCerts
public import LeanPool.HyperellipticCurves.Log.Fold.FoldWitness
public import LeanPool.HyperellipticCurves.Log.Ftau.FtauCerts

import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian

/-!
# The fold form of the translated group law

The upstairs fold configuration and the fold form of the translated law `F_τ`. The `2n`-step
pipeline starts at the `X`-side chart and adds, one at a time, the `n` *moving points* — the Hensel
roots of the `Y`-side chart with the chart square root as `y`-coordinate — and then the `n`
constant involuted `τ`-points.

## Main definitions

* `ChabautyColeman.phaseSeq`: the generic two-phase point sequence (the centre sequences
  `foldXs`/`foldYs` are its diagonal and negated-diagonal instances).
* `ChabautyColeman.ftauFoldXs`, `ChabautyColeman.ftauFoldYs`: the fold-`F_τ` point
  sequences; `ChabautyColeman.IsFtauFoldCerts`: validity of a fold pack there.
* `ChabautyColeman.ftauFoldPipe`, `ChabautyColeman.FtauFold`: the fold-`F_τ` pipeline and the fold
  form of `F_τ` — the coordinates of its output.

## Main statements

* `ChabautyColeman.exists_ftauUY_root`: the moving points exist — Hensel's lemma along
  the ideal of the variables (no completeness of the base needed); together they split
  the chart, `ChabautyColeman.ftauUY_eq_prod`.
* `ChabautyColeman.isFoldState_ftauUX`, `ChabautyColeman.ftauFoldYs_sq`: the start state
  and the points-on-curve identities of the configuration.
* `ChabautyColeman.ftauFoldPipe_fst_eq`: the output shape — the translated `u` with the `F_τ`-fold
  coordinates as lower coefficients.
* `ChabautyColeman.exists_isFoldCerts_ftau`: a valid pack for the centre configuration over the
  residue field lifts to a valid pack for the fold-`F_τ` pipeline, with prescribed residues.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

/-! ### The generic two-phase point sequence -/

section PhaseSeq

variable {S : Type*} [CommRing S] {n : ℕ}

/-- The generic two-phase point sequence of a `2n`-step fold: `n` first-phase points,
then the `n` second-phase points in reverse order; stages the fold never reaches are set
to `0`. -/
def phaseSeq (p q : Fin n → S) : ℕ → S := fun j ↦
  if h : j < n then p ⟨j, h⟩ else if h' : j - n < n then q (Fin.rev ⟨j - n, h'⟩) else 0

theorem phaseSeq_of_lt (p q : Fin n → S) {j : ℕ} (hj : j < n) :
    phaseSeq p q j = p ⟨j, hj⟩ := dite_eq_left hj

theorem phaseSeq_of_ge (p q : Fin n → S) {j : ℕ} (hj : n ≤ j) (hj' : j - n < n) :
    phaseSeq p q j = q (Fin.rev ⟨j - n, hj'⟩) := by
  rw [phaseSeq, dite_eq_right (by lia), dite_eq_left hj']

theorem phaseSeq_add (p q : Fin n → S) {i : ℕ} (hi : i < n) :
    phaseSeq p q (n + i) = q (Fin.rev ⟨i, hi⟩) := by
  rw [phaseSeq_of_ge _ _ (by lia) (by lia)]
  exact congrArg (q ∘ Fin.rev) (Fin.ext (by simp))

theorem map_phaseSeq {S' : Type*} [CommRing S'] (φ : S →+* S') (p q : Fin n → S) (j : ℕ) :
    φ (phaseSeq p q j) = phaseSeq (fun i ↦ φ (p i)) (fun i ↦ φ (q i)) j := by
  rw [phaseSeq, phaseSeq]
  split_ifs <;> simp

/-- The centre `x`-sequence is the two-phase sequence revisiting the tuple. -/
theorem foldXs_eq_phaseSeq (x : Fin n → S) : foldXs x = phaseSeq x x := by
  funext j
  rw [foldXs, phaseSeq]

/-- The centre `y`-sequence is the two-phase sequence with negated second phase. -/
theorem foldYs_eq_phaseSeq (y : Fin n → S) : foldYs y = phaseSeq y (-y) := by
  funext j
  rw [foldYs, phaseSeq]
  split_ifs <;> rfl

end PhaseSeq

/-! ### The Hensel roots of the `Y`-side chart -/

section Root

variable {O : Type*} [CommRing O] [Nontrivial O] {n : ℕ} {u : O[X]}

/-- **The moving points exist**: each simple root `a` of `u` lifts to a root of the
`Y`-side chart polynomial over the doubled power-series ring, with constant coefficient
`a` — Hensel's lemma along the ideal of the variables, which needs no completeness of the
base. -/
theorem exists_ftauUY_root (hu : u.Monic) (hn : n ≤ u.natDegree) {a : O}
    (ha : u.eval a = 0) (hder : IsUnit (u.derivative.eval a)) :
    ∃ A : MvPowerSeries (Fin n ⊕ Fin n) O,
      (ftauUY u n).eval A = 0 ∧ MvPowerSeries.constantCoeff A = a := by
  set J : Ideal (MvPowerSeries (Fin n ⊕ Fin n) O) :=
    Ideal.span (Set.range MvPowerSeries.X)
  have hshape : ftauUY u n
      = u.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O)
        + ∑ i : Fin n, C (MvPowerSeries.X (Sum.inr i)) * X ^ (i : ℕ) := by
    rw [ftauUY, chartU, Polynomial.map_add, Polynomial.map_map, rename_comp_C,
      Polynomial.map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, map_C,
      show (MvPowerSeries.rename (Sum.inr : Fin n → Fin n ⊕ Fin n)).toRingHom
          (MvPowerSeries.X i) = MvPowerSeries.X (Sum.inr i) from MvPowerSeries.rename_X Sum.inr i]
  have hccJ : ∀ x ∈ J, MvPowerSeries.constantCoeff x = (0 : O) := by
    intro x hx
    have h := Ideal.mem_map_of_mem
      (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n ⊕ Fin n) O →+* O) hx
    rwa [MvPowerSeries.map_constantCoeff_span_range_X, Ideal.mem_bot] at h
  have heval : (ftauUY u n).eval (MvPowerSeries.C a) ∈ J := by
    rw [hshape, eval_add, eval_finsetSum]
    refine Ideal.add_mem _ ?_ (Submodule.sum_mem _ fun i _ ↦ ?_)
    · rw [eval_map_apply, ha, map_zero]
      exact J.zero_mem
    · rw [eval_mul, eval_C]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨Sum.inr i, rfl⟩)
  have hder' : IsUnit (Ideal.Quotient.mk J
      ((ftauUY u n).derivative.eval (MvPowerSeries.C a))) := by
    have hmem : (ftauUY u n).derivative.eval (MvPowerSeries.C a)
        - MvPowerSeries.C (u.derivative.eval a) ∈ J := by
      rw [hshape, derivative_add, derivative_map, eval_add, eval_map_apply,
        add_sub_cancel_left, derivative_sum, eval_finsetSum]
      refine Submodule.sum_mem _ fun i _ ↦ ?_
      rw [derivative_C_mul, eval_mul, eval_C]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨Sum.inr i, rfl⟩)
    rw [Ideal.Quotient.eq.mpr hmem]
    exact hder.map ((Ideal.Quotient.mk J).comp
      (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O))
  have : HenselianRing (MvPowerSeries (Fin n ⊕ Fin n) O) J :=
    IsAdicComplete.henselianRing _ _
  obtain ⟨A, hA1, hA2⟩ := HenselianRing.is_henselian (ftauUY u n)
    (chartU_map_rename_monic Sum.inr hu hn) (MvPowerSeries.C a) heval hder'
  refine ⟨A, hA1, ?_⟩
  have h := hccJ _ hA2
  rwa [map_sub, MvPowerSeries.constantCoeff_C, sub_eq_zero] at h

end Root

/-! ### The fold configuration and the fold form of the translated law -/

section Config

variable {O : Type*} [CommRing O] {n : ℕ} {f u v w c₁ c₂ : O[X]}

/-- The `x`-coordinates of the fold-`F_τ` point sequence: the moving points (Hensel roots
of the `Y`-side chart), then the constant `x`-coordinates of the involuted `τ`-points. -/
noncomputable def ftauFoldXs (A : Fin n → MvPowerSeries (Fin n ⊕ Fin n) O) (a : Fin n → O) :
    ℕ → MvPowerSeries (Fin n ⊕ Fin n) O :=
  phaseSeq A fun m ↦ MvPowerSeries.C (a m)

/-- The `y`-coordinates of the fold-`F_τ` point sequence: the chart square root at the
moving points, then the negated constant `y`-coordinates of the `τ`-points. -/
noncomputable def ftauFoldYs (V : Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O))
    (A : Fin n → MvPowerSeries (Fin n ⊕ Fin n) O) (b : Fin n → O) :
    ℕ → MvPowerSeries (Fin n ⊕ Fin n) O :=
  phaseSeq (fun i ↦ V.eval (A i)) fun m ↦ -MvPowerSeries.C (b m)

variable {A : Fin n → MvPowerSeries (Fin n ⊕ Fin n) O} {a b : Fin n → O}

/-- **Whenever the moving points and the `τ`-constants have a common image**, the fold-`F_τ`
`x`-sequence collapses to the two-phase revisit of that image. -/
theorem ftauFoldXs_map_of_eq {T : Type*} [CommRing T]
    {ψ : MvPowerSeries (Fin n ⊕ Fin n) O →+* T} {c : Fin n → T}
    (hA : (fun i ↦ ψ (A i)) = c) (hC : (fun i ↦ ψ (MvPowerSeries.C (a i))) = c) :
    (fun j ↦ ψ (ftauFoldXs A a j)) = foldXs c := by
  funext j
  rw [ftauFoldXs]
  simp only [map_phaseSeq]
  rw [hA, hC, foldXs_eq_phaseSeq]

/-- **Along any homomorphism factoring through the constant coefficient**, the
fold-`F_τ` `x`-sequence collapses to the two-phase revisit of the images of the
`τ`-roots. -/
theorem ftauFoldXs_map {T : Type*} [CommRing T]
    {ψ : MvPowerSeries (Fin n ⊕ Fin n) O →+* T} {χ : O →+* T}
    (hψ : ∀ p, ψ p = χ (MvPowerSeries.constantCoeff p))
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i) :
    (fun j ↦ ψ (ftauFoldXs A a j)) = foldXs fun i ↦ χ (a i) :=
  ftauFoldXs_map_of_eq (funext fun i ↦ (hψ _).trans (congrArg χ (hcc i)))
    (funext fun _ ↦ (hψ _).trans (congrArg χ (MvPowerSeries.constantCoeff_C _)))

/-- **Whenever the interpolated values and the negated `τ`-constants have matching images**,
the fold-`F_τ` `y`-sequence collapses to the two-phase `±`-values of that image. -/
theorem ftauFoldYs_map_of_eq {T : Type*} [CommRing T]
    {V : Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O)}
    {ψ : MvPowerSeries (Fin n ⊕ Fin n) O →+* T} {c : Fin n → T}
    (hV : (fun i ↦ ψ (V.eval (A i))) = c)
    (hC : (fun i ↦ ψ (-MvPowerSeries.C (b i))) = -c) :
    (fun j ↦ ψ (ftauFoldYs V A b j)) = foldYs c := by
  funext j
  rw [ftauFoldYs]
  simp only [map_phaseSeq]
  rw [hV, hC, foldYs_eq_phaseSeq]

variable [Nontrivial O] (hu : u.Monic) (hne : u.natDegree = n) (hv : v.degree < u.degree)
  (hw : v ^ 2 - f = u * w) (hbez : c₁ * u + c₂ * (2 * v) = 1)

/-- **The start state of the fold-`F_τ` pipeline**: the `X`-side chart is a fold state. -/
theorem isFoldState_ftauUX :
    IsFoldState n (f.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O))
      (ftauUX u n) (ftauVX hu hne hv hw hbez) := by
  refine ⟨chartU_map_rename_monic Sum.inl hu hne.ge,
    (chartU_map_rename_natDegree Sum.inl hu hne.ge).trans hne,
    chartV_map_rename_dvd hu hne hv hw hbez Sum.inl, ?_⟩
  exact degree_map_le.trans_lt ((chartV_degree_lt hu hne.ge hv hw hbez).trans_le
    (degree_le_natDegree.trans_eq (by rw [hne])))

include hu hne in
/-- **The Hensel factorization of the `Y`-side chart**: when the `τ`-roots are pairwise
distinct up to units, the chart polynomial splits over the power-series ring into the
linear factors at the moving points. -/
theorem ftauUY_eq_prod (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
    (hunit : ∀ i j : Fin n, i ≠ j → IsUnit (a i - a j)) :
    ftauUY u n = ∏ i : Fin n, (X - C (A i)) := by
  have hAunit : ∀ i j : Fin n, i ≠ j → IsUnit (A i - A j) := fun i j hij ↦ by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, map_sub, hcc i, hcc j]
    exact hunit i j hij
  have hpair : Pairwise (Function.onFun IsCoprime fun i : Fin n ↦
      (X : Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O)) - C (A i)) :=
    fun i j hij ↦ isCoprime_X_sub_C_of_isUnit_sub (hAunit i j hij)
  have hdvd : (∏ i : Fin n,
      ((X : Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O)) - C (A i))) ∣ ftauUY u n :=
    Fintype.prod_dvd_of_coprime hpair fun i ↦ dvd_iff_isRoot.mpr (hroot i)
  have hdeg : (ftauUY u n).natDegree
      ≤ (∏ i : Fin n,
          ((X : Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O)) - C (A i))).natDegree := by
    rw [show (ftauUY u n).natDegree = n from
        (chartU_map_rename_natDegree Sum.inr hu hne.ge).trans hne,
      natDegree_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C _]
    simp
  exact eq_of_monic_of_dvd_of_natDegree_le
    (monic_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C _)
    (chartU_map_rename_monic Sum.inr hu hne.ge) hdvd hdeg

/-- Along any homomorphism factoring through the constant coefficient, the fold-`F_τ`
`y`-sequence collapses to the two-phase `±`-values of the images of the `τ`-roots'
square roots. -/
theorem ftauFoldYs_map {T : Type*} [CommRing T]
    {ψ : MvPowerSeries (Fin n ⊕ Fin n) O →+* T} {χ : O →+* T}
    (hψ : ∀ p, ψ p = χ (MvPowerSeries.constantCoeff p))
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
    (hb : ∀ i, v.eval (a i) = b i) :
    (fun j ↦ ψ (ftauFoldYs (ftauVY hu hne hv hw hbez) A b j)) = foldYs fun i ↦ χ (b i) :=
  ftauFoldYs_map_of_eq
    (funext fun i ↦ by
      rw [hψ, ← Polynomial.eval_map_apply, ftauVY_map_constantCoeff, hcc i]
      exact congrArg χ (hb i))
    (funext fun i ↦ by rw [map_neg, hψ, MvPowerSeries.constantCoeff_C]; rfl)

/-- **The fold-`F_τ` points lie on the curve.** -/
theorem ftauFoldYs_sq (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (ha : ∀ i, u.eval (a i) = 0) (hb : ∀ i, v.eval (a i) = b i) {j : ℕ} (hj : j < 2 * n) :
    ftauFoldYs (ftauVY hu hne hv hw hbez) A b j ^ 2
      = (f.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O)).eval
        (ftauFoldXs A a j) := by
  rcases lt_or_ge j n with h1 | h1
  · rw [ftauFoldXs, ftauFoldYs, phaseSeq_of_lt _ _ h1, phaseSeq_of_lt _ _ h1]
    obtain ⟨q, hq⟩ := chartV_map_rename_dvd hu hne hv hw hbez Sum.inr
    have hq' : ftauVY hu hne hv hw hbez ^ 2
        - f.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O)
        = ftauUY u n * q := hq
    have h := congrArg (Polynomial.eval (A ⟨j, h1⟩)) hq'
    rw [eval_sub, eval_pow, eval_mul, hroot ⟨j, h1⟩, zero_mul] at h
    exact sub_eq_zero.mp h
  · have h2 : j - n < n := by lia
    rw [ftauFoldXs, ftauFoldYs, phaseSeq_of_ge _ _ h1 h2, phaseSeq_of_ge _ _ h1 h2, neg_sq]
    exact sq_eq_map_of_sq_eq _
      (hb (Fin.rev ⟨j - n, h2⟩) ▸ eval_sq_eq_of_root hw (ha (Fin.rev ⟨j - n, h2⟩)))

variable (A) (a b) in
/-- **Validity of a fold pack at the fold-`F_τ` configuration**: the per-step Bézout
identities along the fold of the two charts by the moving points and the involuted
`τ`-points. -/
abbrev IsFtauFoldCerts (d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n) : Prop :=
  IsFoldCerts (f.map MvPowerSeries.C) (ftauFoldXs A a)
    (ftauFoldYs (ftauVY hu hne hv hw hbez) A b) (ftauUX u n)
    (ftauVX hu hne hv hw hbez) d

variable (A) (a b) in
/-- **Weierstrass avoidance at the fold-`F_τ` configuration**: every stage of the fold pipeline —
the `X`-side chart start included — has components coprime up to the `2` of the
half-differential. -/
abbrev IsFtauFoldAvoid (d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n) : Prop :=
  IsFoldAvoid (f.map MvPowerSeries.C) (ftauFoldXs A a)
    (ftauFoldYs (ftauVY hu hne hv hw hbez) A b) (ftauUX u n)
    (ftauVX hu hne hv hw hbez) d

variable (A) (a b) in
/-- **The fold-`F_τ` pipeline**: the `2n`-step fold of the two charts along the moving points and
the involuted `τ`-points, at a fold pack. -/
noncomputable def ftauFoldPipe (d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n) :
    Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O)
      × Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O) :=
  foldPipe (f.map MvPowerSeries.C) (ftauFoldXs A a)
    (ftauFoldYs (ftauVY hu hne hv hw hbez) A b) d.seq (ftauUX u n)
    (ftauVX hu hne hv hw hbez) (2 * n)

/-- The defining equation of the fold-`F_τ` pipeline, for rewriting. -/
theorem ftauFoldPipe_def (d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n) :
    ftauFoldPipe A a b hu hne hv hw hbez d
      = foldPipe (f.map MvPowerSeries.C) (ftauFoldXs A a)
        (ftauFoldYs (ftauVY hu hne hv hw hbez) A b) d.seq (ftauUX u n)
        (ftauVX hu hne hv hw hbez) (2 * n) := rfl

/-- **Output avoidance of the fold pipeline**: the top conjunct of the fold avoidance is the
coprimality of the output's components. -/
theorem isCoprime_ftauFoldPipe {d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n}
    (hav : IsFtauFoldAvoid A a b hu hne hv hw hbez d) :
    IsCoprime (ftauFoldPipe A a b hu hne hv hw hbez d).1
      (2 * (ftauFoldPipe A a b hu hne hv hw hbez d).2) :=
  hav (2 * n) le_rfl

variable (A) (a b) in
/-- **The fold form of the translated group law**: the coordinates of the output of the
point-by-point pipeline. -/
noncomputable def FtauFold (d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n) :
    Fin n → MvPowerSeries (Fin n ⊕ Fin n) O := fun i ↦
  ((ftauFoldPipe A a b hu hne hv hw hbez d).1 - u.map MvPowerSeries.C).coeff (i : ℕ)

/-- **The output shape of the fold pipeline**: with a valid pack, the `u`-part of the final state
is the translated `u` with the `F_τ`-fold coordinates as its lower coefficients. -/
theorem ftauFoldPipe_fst_eq (hf : f.Monic) (hfdeg : f.natDegree = 2 * n + 1)
    (hroot : ∀ i, (ftauUY u n).eval (A i) = 0) (ha : ∀ i, u.eval (a i) = 0)
    (hb : ∀ i, v.eval (a i) = b i)
    {d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n}
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d) :
    (ftauFoldPipe A a b hu hne hv hw hbez d).1
      = u.map MvPowerSeries.C
        + ∑ i : Fin n, C (FtauFold A a b hu hne hv hw hbez d i) * X ^ (i : ℕ) := by
  have hstate := hd.isFoldState (hf.map _) ((hf.natDegree_map _).trans hfdeg)
    (isFoldState_ftauUX hu hne hv hw hbez)
    (fun j hj ↦ ftauFoldYs_sq hu hne hv hw hbez hroot ha hb hj) le_rfl
  exact Monic.eq_add_sum_coeff_sub hstate.monicU (hu.map _) hstate.natDegree_U
    ((hu.natDegree_map _).trans hne)

/-- The `i`-th coefficient of the mapped `u`-part of the fold pipeline: the
`u`-coefficient plus the image of the `i`-th coordinate of the fold form of `F_τ`. -/
theorem coeff_map_ftauFoldPipe_fst {T : Type*} [CommRing T] (hf : f.Monic)
    (hfdeg : f.natDegree = 2 * n + 1) (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (ha : ∀ i, u.eval (a i) = 0) (hb : ∀ i, v.eval (a i) = b i)
    {d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n}
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
    (φ : MvPowerSeries (Fin n ⊕ Fin n) O →+* T) {χ : O →+* T}
    (hχ : φ.comp (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O) = χ)
    (i : Fin n) :
    ((ftauFoldPipe A a b hu hne hv hw hbez d).1.map φ).coeff (i : ℕ)
      = (u.map χ).coeff (i : ℕ) + φ (FtauFold A a b hu hne hv hw hbez d i) := by
  rw [ftauFoldPipe_fst_eq hu hne hv hw hbez hf hfdeg hroot ha hb hd,
    Polynomial.coeff_map_add_sum_C_mul_X_pow, Polynomial.map_map, hχ]

end Config

/-! ### Existence of valid packs at the fold configuration -/

section Exists

open IsLocalRing

variable {O : Type*} [CommRing O] [IsLocalRing O] {n : ℕ} {f u v w c₁ c₂ : O[X]}

variable (hu : u.Monic) (hne : u.natDegree = n) (hv : v.degree < u.degree)
  (hw : v ^ 2 - f = u * w) (hbez : c₁ * u + c₂ * (2 * v) = 1)

/-- **Existence of a valid fold pack at the fold-`F_τ` configuration**: a valid pack for the centre
configuration over the residue field lifts to a valid pack for the fold-`F_τ` pipeline, with
prescribed residues. -/
theorem exists_isFoldCerts_ftau (hf : f.Monic) (hfdeg : f.natDegree = 2 * n + 1)
    {A : Fin n → MvPowerSeries (Fin n ⊕ Fin n) O} {a b : Fin n → O}
    (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
    (ha : ∀ i, u.eval (a i) = 0) (hb : ∀ i, v.eval (a i) = b i)
    (d' : FoldCertData (ResidueField O) n)
    (hd' : IsFoldCerts (f.map (residue O)) (foldXs fun i ↦ residue O (a i))
      (foldYs fun i ↦ residue O (b i)) (u.map (residue O)) (v.map (residue O)) d') :
    ∃ d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n,
      IsFtauFoldCerts A a b hu hne hv hw hbez d
      ∧ d.map (mvSeriesResidue (Fin n ⊕ Fin n) O) = d' := by
  have hmap (p : Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O)) :
      p.map (mvSeriesResidue (Fin n ⊕ Fin n) O)
        = (p.map MvPowerSeries.constantCoeff).map (residue O) :=
    (Polynomial.map_map _ _ p).symm
  -- the residue of the fold configuration is the centre configuration
  have hψxs : (fun j ↦ mvSeriesResidue (Fin n ⊕ Fin n) O (ftauFoldXs A a j))
      = foldXs fun i ↦ residue O (a i) := ftauFoldXs_map (fun _ ↦ rfl) hcc
  have hψys : (fun j ↦ mvSeriesResidue (Fin n ⊕ Fin n) O
        (ftauFoldYs (ftauVY hu hne hv hw hbez) A b j))
      = foldYs fun i ↦ residue O (b i) :=
    ftauFoldYs_map hu hne hv hw hbez (fun _ ↦ rfl) hcc hb
  have hψU : (ftauUX u n).map (mvSeriesResidue (Fin n ⊕ Fin n) O)
      = u.map (residue O) := by
    rw [hmap, ftauUX_map_constantCoeff]
  have hψV : (ftauVX hu hne hv hw hbez).map (mvSeriesResidue (Fin n ⊕ Fin n) O)
      = v.map (residue O) := by
    rw [hmap, ftauVX_map_constantCoeff]
  have hψF : ((f.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O)).map
        (mvSeriesResidue (Fin n ⊕ Fin n) O))
      = f.map (residue O) := by
    rw [hmap, map_C_map_constantCoeff]
  rw [← hψxs, ← hψys, ← hψU, ← hψV, ← hψF] at hd'
  exact exists_isFoldCerts_lift (mvSeriesResidue_surjective _ O)
    (ker_mvSeriesResidue_le_jacobson _ O) (hf.map _) ((hf.natDegree_map _).trans hfdeg)
    (isFoldState_ftauUX hu hne hv hw hbez)
    (fun j hj ↦ ftauFoldYs_sq hu hne hv hw hbez hroot ha hb hj) d' hd'

end Exists

end ChabautyColeman

end
