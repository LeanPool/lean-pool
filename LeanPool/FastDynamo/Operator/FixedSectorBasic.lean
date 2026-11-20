/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Operator.FixedSector
public import LeanPool.FastDynamo.Operator.ResolventPropagation
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Basic closed-graph and compact-resolvent facts for a fixed torus sector

This module isolates the functional-analytic part of Paper Lemma 5.1 (`lem:torus-sector-basic`).
For a domain operator `A : D -> X`, one bounded two-sided inverse of one
pencil `z - A` has three immediate consequences:

* the unbounded graph of `A` in `X x X` is closed;
* the Banach-domain norm is controlled by the ordinary graph norm;
* if the domain embedding `D -> X` is compact, every available state
  resolvent is compact.

These statements apply to every operator whose domain is the transverse
Fourier-graph `H²`.  The remaining analytic input in Lemma 5.1 is the construction of one such
inverse.  For the horizontal operator it is built by a Neumann series along the real ray
(`FastDynamo/Operator/HorizontalSectorBasic.lean`); the paper instead obtains it from Fredholm
index zero and injectivity by coercivity (proof of `lem:torus-sector-basic`).
The transverse `H^2 -> L^2` Rellich embedding is proved below by explicit
finite-frequency approximation.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

namespace DomainOperator

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]

/-- The ordinary unbounded-operator graph in the ambient product `X x X`. -/
def graphSet (A : DomainOperator X D) : Set (X × X) :=
  Set.range fun d ↦ (A.embedding d, A.op d)

/-- Closedness of a bundled-domain operator means closedness of its ordinary
ambient graph. -/
def IsClosedGraph (A : DomainOperator X D) : Prop :=
  IsClosed A.graphSet

/-- The continuous domain parametrization of the ordinary graph. -/
def graphMap (A : DomainOperator X D) : D →L[ℂ] X × X :=
  A.embedding.prod A.op

/--
The graph parametrization sends a domain element `d` to the pair `(embedding d, op d)`, whose
range is the ordinary ambient graph.
-/
@[simp] theorem graphMap_apply (A : DomainOperator X D) (d : D) :
    A.graphMap d = (A.embedding d, A.op d) :=
  rfl

/-- Apply the formal pencil `z * x - y` to an ambient graph candidate
`(x,y)`. -/
def graphPairPencil (z : ℂ) : (X × X) →L[ℂ] X :=
  z • ContinuousLinearMap.fst ℂ X X - ContinuousLinearMap.snd ℂ X X

/-- The formal pencil acts on an ambient graph candidate `(x, y)` by `z • x - y`. -/
@[simp] theorem graphPairPencil_apply (z : ℂ) (p : X × X) :
    graphPairPencil (X := X) z p = z • p.1 - p.2 :=
  rfl

/-- Applying the formal pencil to a graph point recovers the domain pencil
`A.pencil z d`. -/
@[simp] theorem graphPairPencil_graphMap
    (A : DomainOperator X D) (z : ℂ) (d : D) :
    graphPairPencil (X := X) z (A.graphMap d) = A.pencil z d :=
  rfl

/-- If `T` is a left inverse of the pencil, this defect cuts out the graph as
a closed kernel. -/
def graphRetractionDefect (A : DomainOperator X D) (z : ℂ)
    (T : X →L[ℂ] D) : (X × X) →L[ℂ] X × X :=
  ContinuousLinearMap.id ℂ (X × X) -
    A.graphMap.comp (T.comp (graphPairPencil (X := X) z))

/--
Given a bounded left inverse `T` of the pencil at one point, the ordinary ambient graph of `A` is
exactly the kernel of the continuous defect `graphRetractionDefect A z T`; this is what exhibits
the graph as a closed set.
-/
theorem graphSet_eq_ker_graphRetractionDefect
    (A : DomainOperator X D) (z : ℂ) (T : X →L[ℂ] D)
    (hleft : T.comp (A.pencil z) = ContinuousLinearMap.id ℂ D) :
    A.graphSet = (A.graphRetractionDefect z T).ker := by
  ext p
  constructor
  · rintro ⟨d, rfl⟩
    change A.graphMap d -
      A.graphMap (T (graphPairPencil (X := X) z (A.graphMap d))) = 0
    rw [graphPairPencil_graphMap]
    have hd := congrArg (fun L : D →L[ℂ] D ↦ L d) hleft
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] at hd
    rw [hd, sub_self]
  · intro hp
    change p - A.graphMap
      (T (graphPairPencil (X := X) z p)) = 0 at hp
    refine ⟨T (graphPairPencil (X := X) z p), ?_⟩
    exact (sub_eq_zero.mp hp).symm

/-- A bounded left inverse at one spectral point already proves closedness of
the ordinary unbounded graph.  Surjectivity of the pencil is not needed for
this implication. -/
theorem isClosedGraph_of_leftInverse
    (A : DomainOperator X D) (z : ℂ) (T : X →L[ℂ] D)
    (hleft : T.comp (A.pencil z) = ContinuousLinearMap.id ℂ D) :
    A.IsClosedGraph := by
  rw [IsClosedGraph, graphSet_eq_ker_graphRetractionDefect A z T hleft]
  exact (A.graphRetractionDefect z T).isClosed_ker

/-- The pencil is bounded by the ordinary graph norm. -/
theorem norm_pencil_apply_le (A : DomainOperator X D) (z : ℂ) (d : D) :
    ‖A.pencil z d‖ ≤ ‖z‖ * ‖A.embedding d‖ + ‖A.op d‖ := by
  rw [pencil]
  simp only [sub_apply, smul_apply]
  exact (norm_sub_le _ _).trans_eq (by rw [norm_smul])

/-- A bounded left inverse controls the chosen Banach-domain norm by the
ordinary ambient graph norm.  This is the abstract graph-`H^2` estimate used
in Lemma 5.1. -/
theorem norm_domain_le_of_leftInverse
    (A : DomainOperator X D) (z : ℂ) (T : X →L[ℂ] D)
    (hleft : T.comp (A.pencil z) = ContinuousLinearMap.id ℂ D)
    (d : D) :
    ‖d‖ ≤ ‖T‖ * (‖z‖ * ‖A.embedding d‖ + ‖A.op d‖) := by
  have hd := congrArg (fun L : D →L[ℂ] D ↦ L d) hleft
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hd
  calc
    ‖d‖ = ‖T (A.pencil z d)‖ := by rw [hd]
    _ ≤ ‖T‖ * ‖A.pencil z d‖ := T.le_opNorm _
    _ ≤ ‖T‖ * (‖z‖ * ‖A.embedding d‖ + ‖A.op d‖) :=
      mul_le_mul_of_nonneg_left (A.norm_pencil_apply_le z d) (norm_nonneg T)

/-- Package a two-sided inverse of one pencil as a resolvent on the singleton
set containing that point. -/
def hasResolventOnSingleton
    (A : DomainOperator X D) (z : ℂ) (T : X →L[ℂ] D)
    (hleft : T.comp (A.pencil z) = ContinuousLinearMap.id ℂ D)
    (hright : (A.pencil z).comp T = ContinuousLinearMap.id ℂ X) :
    HasResolventOn A {z} where
  inv := fun _ ↦ T
  left_inv w hw := by
    have hwz : w = z := Set.mem_singleton_iff.mp hw
    subst w
    exact hleft
  right_inv w hw := by
    have hwz : w = z := Set.mem_singleton_iff.mp hw
    subst w
    exact hright
  continuousOn := continuousOn_const

/-- The exact bundled-domain meaning of a nonempty resolvent set. -/
def HasNonemptyResolvent (A : DomainOperator X D) : Prop :=
  ∃ (z : ℂ) (T : X →L[ℂ] D),
    T.comp (A.pencil z) = ContinuousLinearMap.id ℂ D ∧
      (A.pencil z).comp T = ContinuousLinearMap.id ℂ X

/--
Having a nonempty resolvent set, in the sense of a two-sided bounded inverse of some pencil, is
equivalent to the existence of a singleton `HasResolventOn` certificate.
-/
theorem hasNonemptyResolvent_iff_exists_singleton
    (A : DomainOperator X D) :
    A.HasNonemptyResolvent ↔
      ∃ z : ℂ, Nonempty (HasResolventOn A {z}) := by
  constructor
  · rintro ⟨z, T, hleft, hright⟩
    exact ⟨z, ⟨A.hasResolventOnSingleton z T hleft hright⟩⟩
  · rintro ⟨z, ⟨h⟩⟩
    refine ⟨z, h.inv z, ?_, ?_⟩
    · exact h.left_inv z (by simp)
    · exact h.right_inv z (by simp)

/-- Compactness of the domain embedding makes the state resolvent compact at
every point certified to lie in the supplied resolvent set. -/
theorem isCompactOperator_stateResolvent_of_embedding
    {S : Set ℂ} (A : DomainOperator X D)
    (hcompact : IsCompactOperator A.embedding)
    (h : HasResolventOn A S) (z : ℂ) (_hz : z ∈ S) :
    IsCompactOperator (h.stateResolvent z) := by
  exact hcompact.comp_clm (h.inv z)

end DomainOperator

/-! ## Compactness of the transverse Fourier-graph embedding -/

open scoped ENNReal

/-- A finite square of transverse Fourier frequencies. -/
def transverseFrequencyBox (N : ℕ) : Finset TransverseFrequency :=
  Fintype.piFinset fun _ : Fin 2 ↦
    Finset.Icc (-(N : ℤ)) (N : ℤ)

/-- A frequency outside the box `[-N, N]²` has some coordinate of absolute value exceeding `N`. -/
lemma exists_abs_gt_of_not_mem_transverseFrequencyBox
    (N : ℕ) (n : TransverseFrequency)
    (hn : n ∉ transverseFrequencyBox N) :
    ∃ j : Fin 2, (N : ℝ) < |(n j : ℝ)| := by
  rw [transverseFrequencyBox, Fintype.mem_piFinset] at hn
  push Not at hn
  rcases hn with ⟨j, hj⟩
  simp only [Finset.mem_Icc] at hj
  refine ⟨j, ?_⟩
  by_cases hleft : -(N : ℤ) ≤ n j
  · have hright : (N : ℤ) < n j := by
      exact lt_of_not_ge (fun h ↦ hj ⟨hleft, h⟩)
    have hright' : (N : ℝ) < (n j : ℝ) := by exact_mod_cast hright
    exact hright'.trans_le (le_abs_self (n j : ℝ))
  · have hjneg : n j < -(N : ℤ) := lt_of_not_ge hleft
    have hj' : (n j : ℝ) < -(N : ℝ) := by exact_mod_cast hjneg
    exact lt_of_lt_of_le (by linarith) (neg_le_abs (n j : ℝ))

/-- The inhomogeneous `H²` weight dominates each coordinate frequency.
This coarse bound is sufficient to prove that its inverse vanishes at
infinity. -/
lemma abs_transverseFrequency_le_transverseH2Weight
    (n : TransverseFrequency) (j : Fin 2) :
    |(n j : ℝ)| ≤ transverseH2Weight n := by
  have hcoord : (n j : ℝ) ^ 2 ≤ ∑ i, (n i : ℝ) ^ 2 :=
    Finset.single_le_sum (fun i _ ↦ sq_nonneg (n i : ℝ))
      (Finset.mem_univ j)
  have hpi : 1 ≤ (2 * Real.pi) ^ 2 := by
    nlinarith [Real.one_le_pi_div_two]
  have hsum : 0 ≤ ∑ i, (n i : ℝ) ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ sq_nonneg (n i : ℝ)
  have hmul : (n j : ℝ) ^ 2 ≤
      (2 * Real.pi) ^ 2 * ∑ i, (n i : ℝ) ^ 2 := by
    calc
      (n j : ℝ) ^ 2 ≤ ∑ i, (n i : ℝ) ^ 2 := hcoord
      _ ≤ (2 * Real.pi) ^ 2 * ∑ i, (n i : ℝ) ^ 2 := by
        have hprod := mul_nonneg (sub_nonneg.mpr hpi) hsum
        nlinarith
  have habs : |(n j : ℝ)| ≤ 1 + (n j : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (|(n j : ℝ)| - 1), abs_nonneg (n j : ℝ),
      sq_abs (n j : ℝ)]
  unfold transverseH2Weight transverseFrequencyEnergy
  linarith

/-- The inverse `H²` weight tends uniformly to zero off finite frequency
sets, in the epsilon/finite-set form used by compactness. -/
lemma transverseH2InverseWeight_czero :
    ∀ δ : ℝ, 0 < δ → ∃ s : Finset TransverseFrequency,
      ∀ n ∉ s, ‖(transverseH2Weight n : ℂ)⁻¹‖ < δ := by
  intro δ hδ
  obtain ⟨N : ℕ, hN⟩ := exists_nat_ge (1 / δ)
  refine ⟨transverseFrequencyBox N, ?_⟩
  intro n hn
  obtain ⟨j, hj⟩ :=
    exists_abs_gt_of_not_mem_transverseFrequencyBox N n hn
  have hweight : 1 / δ < transverseH2Weight n :=
    hN.trans_lt (hj.trans_le
      (abs_transverseFrequency_le_transverseH2Weight n j))
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (transverseH2Weight_pos n)]
  rw [inv_lt_iff_one_lt_mul₀ (transverseH2Weight_pos n)]
  have hmul := mul_lt_mul_of_pos_left hweight hδ
  simpa [hδ.ne'] using hmul

/-- The scalar diagonal which divides Fourier coefficients by the
inhomogeneous `H²` weight. -/
def transverseH2InverseWeightCoeffMap :
    TransverseScalarFourierL2 →L[ℂ] TransverseScalarFourierL2 :=
  lp.mapCLM 2
    (fun n ↦ (ContinuousLinearMap.lsmul ℂ ℂ)
      (transverseH2Weight n : ℂ)⁻¹)
    zero_le_one
    (fun n ↦ (ContinuousLinearMap.opNorm_lsmul_apply_le
      (E := ℂ) (transverseH2Weight n : ℂ)⁻¹).trans (by
        rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (transverseH2Weight_pos n)]
        exact (inv_le_one₀ (transverseH2Weight_pos n)).2
          (one_le_transverseH2Weight n)))

/-- The inverse-weight diagonal divides the `n`-th Fourier coefficient by `transverseH2Weight n`. -/
@[simp] theorem transverseH2InverseWeightCoeffMap_apply
    (a : TransverseScalarFourierL2) (n : TransverseFrequency) :
    transverseH2InverseWeightCoeffMap a n =
      (transverseH2Weight n : ℂ)⁻¹ * a n :=
  rfl

/-- Finite-frequency truncation of the inverse-weight diagonal. -/
def transverseH2InverseWeightFiniteCoeffMap
    (s : Finset TransverseFrequency) :
    TransverseScalarFourierL2 →L[ℂ] TransverseScalarFourierL2 :=
  ∑ n ∈ s,
    (lp.singleContinuousLinearMap ℂ
      (fun _ : TransverseFrequency ↦ ℂ) 2 n).comp
        (((ContinuousLinearMap.lsmul ℂ ℂ)
          (transverseH2Weight n : ℂ)⁻¹).comp
            (lp.evalCLM ℂ (fun _ : TransverseFrequency ↦ ℂ) 2 n))

/--
The truncated inverse-weight diagonal divides by the weight on the finite frequency set `s` and
returns zero off it.
-/
@[simp] theorem transverseH2InverseWeightFiniteCoeffMap_apply
    (s : Finset TransverseFrequency) (a : TransverseScalarFourierL2)
    (n : TransverseFrequency) :
    transverseH2InverseWeightFiniteCoeffMap s a n =
      if n ∈ s then (transverseH2Weight n : ℂ)⁻¹ * a n else 0 := by
  classical
  simp only [transverseH2InverseWeightFiniteCoeffMap, sum_apply,
    ContinuousLinearMap.comp_apply,
    lp.singleContinuousLinearMap_apply,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  change ((∑ i ∈ s, lp.single 2 i
    ((transverseH2Weight i : ℂ)⁻¹ * a i)) :
      TransverseScalarFourierL2) n = _
  rw [show ((∑ i ∈ s, lp.single 2 i
      ((transverseH2Weight i : ℂ)⁻¹ * a i)) :
        TransverseScalarFourierL2) n =
      ∑ i ∈ s, (lp.single 2 i
        ((transverseH2Weight i : ℂ)⁻¹ * a i)) n by
    simpa only [Finset.sum_apply] using congrFun (lp.coeFn_sum
      (fun i ↦ lp.single 2 i
        ((transverseH2Weight i : ℂ)⁻¹ * a i)) s) n]
  by_cases hn : n ∈ s
  · rw [ite_eq_left hn, Finset.sum_eq_single n]
    · exact lp.single_apply_self 2 n _
    · intro i hi hin
      have hni : n ≠ i := Ne.symm hin
      exact lp.single_apply_ne 2 i _ hni
    · exact fun h ↦ (h hn).elim
  · rw [ite_eq_right hn]
    apply Finset.sum_eq_zero
    intro i hi
    have hni : n ≠ i := by
      intro h
      apply hn
      simpa [h] using hi
    exact lp.single_apply_ne 2 i _ hni

/--
Each finite truncation of the inverse-weight diagonal is compact, being a finite sum of
rank-one maps.
-/
lemma isCompactOperator_transverseH2InverseWeightFiniteCoeffMap
    (s : Finset TransverseFrequency) :
    IsCompactOperator (transverseH2InverseWeightFiniteCoeffMap s) := by
  classical
  unfold transverseH2InverseWeightFiniteCoeffMap
  induction s using Finset.induction_on with
  | empty =>
      simpa using (isCompactOperator_zero :
        IsCompactOperator
          (0 : TransverseScalarFourierL2 → TransverseScalarFourierL2))
  | @insert n s hn ih =>
      rw [Finset.sum_insert hn]
      have hscalar : IsCompactOperator
          (((ContinuousLinearMap.lsmul ℂ ℂ)
            (transverseH2Weight n : ℂ)⁻¹).comp
              (lp.evalCLM ℂ
                (fun _ : TransverseFrequency ↦ ℂ) 2 n)) :=
        isCompactOperator_of_locallyCompactSpace_dom _
      exact (hscalar.clm_comp
        (lp.singleContinuousLinearMap ℂ
          (fun _ : TransverseFrequency ↦ ℂ) 2 n)).add ih

/-- Division by the inhomogeneous order-two weight is compact on scalar
`ℓ²` Fourier coefficients. -/
theorem isCompactOperator_transverseH2InverseWeightCoeffMap :
    IsCompactOperator transverseH2InverseWeightCoeffMap := by
  apply (isClosed_setOfPred_isCompactOperator :
    IsClosed {T : TransverseScalarFourierL2 →L[ℂ]
      TransverseScalarFourierL2 | IsCompactOperator T}).closure_subset
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨s, hs⟩ := transverseH2InverseWeight_czero (ε / 2) (by linarith)
  let c : TransverseFrequency → ℂ := fun n ↦
    if n ∈ s then 0 else (transverseH2Weight n : ℂ)⁻¹
  have hc : ∀ n, ‖c n‖ ≤ ε / 2 := by
    intro n
    by_cases hn : n ∈ s
    · have hhalf : 0 ≤ ε / 2 := by linarith
      simpa [c, hn] using hhalf
    · simp only [c, ite_eq_right hn]
      exact (hs n hn).le
  let tail : TransverseScalarFourierL2 →L[ℂ]
      TransverseScalarFourierL2 :=
    lp.mapCLM 2
      (fun n ↦ (ContinuousLinearMap.lsmul ℂ ℂ) (c n))
      (by linarith)
      (fun n ↦ (ContinuousLinearMap.opNorm_lsmul_apply_le
        (E := ℂ) (c n)).trans (hc n))
  have htail : ‖tail‖ ≤ ε / 2 :=
    lp.norm_mapCLM_le 2
      (fun n ↦ (ContinuousLinearMap.lsmul ℂ ℂ) (c n))
      (by linarith)
      (fun n ↦ (ContinuousLinearMap.opNorm_lsmul_apply_le
        (E := ℂ) (c n)).trans (hc n))
  have heq : transverseH2InverseWeightFiniteCoeffMap s -
      transverseH2InverseWeightCoeffMap = -tail := by
    apply ContinuousLinearMap.ext
    intro a
    apply lp.ext
    funext n
    by_cases hn : n ∈ s <;>
      simp [transverseH2InverseWeightFiniteCoeffMap_apply,
        transverseH2InverseWeightCoeffMap_apply, tail, c, hn]
  have heq' : transverseH2InverseWeightCoeffMap -
      transverseH2InverseWeightFiniteCoeffMap s = tail := by
    calc
      transverseH2InverseWeightCoeffMap -
          transverseH2InverseWeightFiniteCoeffMap s =
          -(transverseH2InverseWeightFiniteCoeffMap s -
            transverseH2InverseWeightCoeffMap) := by abel
      _ = -(-tail) := by rw [heq]
      _ = tail := neg_neg _
  refine ⟨transverseH2InverseWeightFiniteCoeffMap s,
    isCompactOperator_transverseH2InverseWeightFiniteCoeffMap s, ?_⟩
  simpa only [dist_eq_norm, heq'] using
    htail.trans_lt (show ε / 2 < ε by linarith)

/-- Scalar synthesis after division by the order-two weight. -/
def transverseH2InverseWeightSynthesis :
    TransverseScalarFourierL2 →L[ℂ] TransverseScalarL2 :=
  transverseScalarFourierSynthesis.comp
    transverseH2InverseWeightCoeffMap

/--
Dividing by the order-two weight and then synthesizing is a compact map from coefficient `ℓ²`
into physical scalar `L²`.
-/
lemma isCompactOperator_transverseH2InverseWeightSynthesis :
    IsCompactOperator transverseH2InverseWeightSynthesis :=
  isCompactOperator_transverseH2InverseWeightCoeffMap.clm_comp
    transverseScalarFourierSynthesis

/-- Coordinatewise inverse-weight synthesis from the stored `H²` coefficient arrays of a
fibre `ℂ^ι` into physical vector-valued `L²`. -/
def transverseH2InverseWeightVecSynthesis (ι : Type*) [Fintype ι] [DecidableEq ι] :
    WeightedTransverseCoeffs ι →L[ℂ] TransverseVecL2 ι :=
  transverseVecOfCoordsL2.comp
    (mapWeightedTransverseCoords transverseH2InverseWeightSynthesis)

/--
The Fourier coefficients of the vector-valued inverse-weight synthesis are the stored
coefficients divided by `transverseH2Weight n`.
-/
theorem transverseCoeffCLM_transverseH2InverseWeightVecSynthesis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : WeightedTransverseCoeffs ι) (n : TransverseFrequency) (i : ι) :
    transverseCoeffCLM n i
      (transverseH2InverseWeightVecSynthesis ι a) =
        (transverseH2Weight n : ℂ)⁻¹ * (a i) n := by
  change transverseCoeffCLM n i
    (transverseVecOfCoordsL2
      (mapWeightedTransverseCoords transverseH2InverseWeightSynthesis a)) = _
  rw [transverseCoeffCLM, ContinuousLinearMap.comp_apply,
    transverseCoordL2_transverseVecOfCoordsL2,
    mapWeightedTransverseCoords_apply,
    transverseH2InverseWeightSynthesis,
    ContinuousLinearMap.comp_apply,
    transverseScalarCoeffCLM_synthesis,
    transverseH2InverseWeightCoeffMap_apply]

/--
The coordinatewise inverse-weight synthesis into vector-valued `L²` is compact, being a finite
sum of compositions of the compact scalar version.  The induction is over the fibre index set,
so the statement is uniform in `ι`.
-/
lemma isCompactOperator_transverseH2InverseWeightVecSynthesis
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    IsCompactOperator (transverseH2InverseWeightVecSynthesis ι) := by
  have hEq : transverseH2InverseWeightVecSynthesis ι =
      ∑ i : ι,
        (scalarToVecCoordL2 i).comp
          (transverseH2InverseWeightSynthesis.comp
            (PiLp.proj 2
              (fun _ : ι ↦ TransverseScalarFourierL2) i)) := by
    apply ContinuousLinearMap.ext
    intro a
    simp [transverseH2InverseWeightVecSynthesis,
      transverseVecOfCoordsL2]
  rw [hEq]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simpa using (isCompactOperator_zero :
        IsCompactOperator
          (0 : WeightedTransverseCoeffs ι → TransverseVecL2 ι))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact ((isCompactOperator_transverseH2InverseWeightSynthesis.comp_clm
        (PiLp.proj 2
          (fun _ : ι ↦ TransverseScalarFourierL2) i)).clm_comp
            (scalarToVecCoordL2 i)).add ih

/-- Fourier-series proof of the Rellich input needed in Lemma 5.1: the
closed Fourier-graph realization of periodic `H²(T²; ℂ^ι)` embeds compactly
into physical `L²`, for every finite fibre index `ι`. -/
theorem isCompactOperator_transverseVecH2Embedding
    (ι : Type*) [Fintype ι] :
    IsCompactOperator (transverseH2Embedding (ι := ι)) := by
  classical
  have hEq : (transverseH2Embedding (ι := ι)) =
      (transverseH2InverseWeightVecSynthesis ι).comp
        transverseH2WeightedCoeffs := by
    apply ContinuousLinearMap.ext
    intro b
    apply transverseVecL2_ext_coeff
    intro n i
    rw [ContinuousLinearMap.comp_apply,
      transverseCoeffCLM_transverseH2InverseWeightVecSynthesis,
      transverseH2WeightedCoeffs_apply]
    have hw : (transverseH2Weight n : ℂ) ≠ 0 := by
      exact_mod_cast (transverseH2Weight_pos n).ne'
    field_simp [hw]
  rw [hEq]
  exact (isCompactOperator_transverseH2InverseWeightVecSynthesis ι).comp_clm
    transverseH2WeightedCoeffs

/-! ## Fibre-generic form of the functional-analytic clauses of Lemma 5.1

The three clauses of Lemma 5.1 (`lem:torus-sector-basic`) that do not mention the
velocity — closed graph, graph norm equivalent to the `H²` norm, and compact resolvent — hold
for *any* domain operator whose bundled domain is the transverse Fourier-graph `H²` of a finite
fibre `ℂ^ι` and whose domain embedding is the graph inclusion.  The two-component
horizontal operator of the paper is an instance.
-/

section FibreGeneric

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A bounded resolvent at one point already closes the ambient graph. -/
theorem transverseGraphOperator_isClosedGraph_of_hasResolventOn
    (A : DomainOperator (TransverseVecL2 ι) (TransverseVecH2 ι))
    {S : Set ℂ} (h : HasResolventOn A S) (z : ℂ) (hz : z ∈ S) :
    A.IsClosedGraph :=
  DomainOperator.isClosedGraph_of_leftInverse A z (h.inv z) (h.left_inv z hz)

omit [DecidableEq ι] in
/-- A bounded resolvent at one point makes the Fourier-graph `H²` norm dominated by the
ordinary graph norm `‖z‖‖b‖ + ‖A b‖`. -/
theorem norm_transverseVecH2_le_graph_of_hasResolventOn
    (A : DomainOperator (TransverseVecL2 ι) (TransverseVecH2 ι))
    {S : Set ℂ} (h : HasResolventOn A S) (z : ℂ) (hz : z ∈ S)
    (b : TransverseVecH2 ι) :
    ‖b‖ ≤ ‖h.inv z‖ * (‖z‖ * ‖A.embedding b‖ + ‖A.op b‖) :=
  DomainOperator.norm_domain_le_of_leftInverse A z (h.inv z) (h.left_inv z hz) b

omit [DecidableEq ι] in
/-- Every available state resolvent of such an operator is compact on transverse `L²`,
by the Rellich embedding `isCompactOperator_transverseVecH2Embedding`. -/
theorem isCompactOperator_transverseGraphOperator_stateResolvent
    (A : DomainOperator (TransverseVecL2 ι) (TransverseVecH2 ι))
    (hemb : A.embedding = transverseH2Embedding)
    {S : Set ℂ} (h : HasResolventOn A S) (z : ℂ) (hz : z ∈ S) :
    IsCompactOperator (h.stateResolvent z) := by
  refine DomainOperator.isCompactOperator_stateResolvent_of_embedding A ?_ h z hz
  rw [hemb]
  exact isCompactOperator_transverseVecH2Embedding ι

end FibreGeneric

end

end FastDynamo
