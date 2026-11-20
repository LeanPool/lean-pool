/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.CompactAtkinson
public import LeanPool.FastDynamo.Operator.FiniteDimensionalDeterminant
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Continuation of local analytic Fredholm reductions

The finite-dimensional Schur construction is local: different parameter
neighborhoods may use different splittings and hence different determinant
functions.  This file proves that this causes no ambiguity for analytic
Fredholm continuation: the zero sets of all local determinants encode
noninvertibility of the same operator family, and if connected local
scalar-reduction patches cover a connected open domain, one invertible point
makes the invertible locus dense throughout that domain.

The argument is analytic.  On
each patch the isolated-zero theorem already present in `AnalyticFredholm`
makes invertible parameters codiscrete.  A relative clopen argument then
propagates the closure of the invertible locus through the cover.

This is the continuation part of the analytic Fredholm theorem.  To apply it
to a family `1 - K(z)`, one needs a local finite Schur reduction at every
point of the domain (for instance from a Fredholm splitting).  Compactness
supplies finite-dimensional kernels, but on a general Banach space it does not
by itself supply complemented local splittings; on a Hilbert space the last
sections of this file build the cover by local finite-range regularization of
a compact analytic pencil (`compactPencilCover`).
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter Set Topology

namespace AnalyticFredholm

universe u

variable {X : Type u}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

variable {F : ℂ → (X →L[ℂ] X)} {U V W : Set ℂ}

/-! ## A finite-range factorization lemma -/

variable {P : Type*}
  [NormedAddCommGroup P] [NormedSpace ℂ P]

omit [CompleteSpace X] in
/-- Rectangular Jacobson lemma for continuous linear maps.  This is the
operator form of `1 - ab` being invertible exactly when `1 - ba` is
invertible.  It lets a finite-range perturbation of the identity be reduced
to an endomorphism of any fixed finite-dimensional space through which the
perturbation factors. -/
theorem isInvertible_id_sub_comp_iff
    (a : P →L[ℂ] X) (b : X →L[ℂ] P) :
    (ContinuousLinearMap.id ℂ X - a.comp b).IsInvertible ↔
      (ContinuousLinearMap.id ℂ P - b.comp a).IsInvertible := by
  constructor
  · intro hT
    let T : X →L[ℂ] X := ContinuousLinearMap.id ℂ X - a.comp b
    let S : P →L[ℂ] P := ContinuousLinearMap.id ℂ P - b.comp a
    let Sinv : P →L[ℂ] P :=
      ContinuousLinearMap.id ℂ P + (b.comp T.inverse).comp a
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := Sinv)
    · apply ContinuousLinearMap.ext
      intro p
      have hrel := hT.self_apply_inverse (a p)
      change T (T.inverse (a p)) = a p at hrel
      change T.inverse (a p) - a (b (T.inverse (a p))) = a p at hrel
      have hb := congrArg b hrel
      simp only [map_sub] at hb
      simp only [Sinv, ContinuousLinearMap.comp_apply, sub_apply, add_apply,
        ContinuousLinearMap.id_apply, map_add]
      calc
        p - b (a p) + (b (T.inverse (a p)) -
              b (a (b (T.inverse (a p))))) =
            p - b (a p) + b (a p) := by rw [hb]
        _ = p := by abel
    · apply ContinuousLinearMap.ext
      intro p
      have hrel := hT.inverse_apply_self (a p)
      change T.inverse (T (a p)) = a p at hrel
      change T.inverse (a p - a (b (a p))) = a p at hrel
      rw [map_sub] at hrel
      have hb := congrArg b hrel
      simp only [map_sub] at hb
      simp only [Sinv, ContinuousLinearMap.comp_apply, sub_apply, add_apply,
        ContinuousLinearMap.id_apply, map_sub]
      calc
        p + b (T.inverse (a p)) -
              (b (a p) + b (T.inverse (a (b (a p))))) =
            p + (b (T.inverse (a p)) -
              b (T.inverse (a (b (a p))))) - b (a p) := by abel
        _ = p + b (a p) - b (a p) := by rw [hb]
        _ = p := by abel
  · intro hS
    let S : P →L[ℂ] P := ContinuousLinearMap.id ℂ P - b.comp a
    let T : X →L[ℂ] X := ContinuousLinearMap.id ℂ X - a.comp b
    let Tinv : X →L[ℂ] X :=
      ContinuousLinearMap.id ℂ X + (a.comp S.inverse).comp b
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := Tinv)
    · apply ContinuousLinearMap.ext
      intro x
      have hrel := hS.self_apply_inverse (b x)
      change S (S.inverse (b x)) = b x at hrel
      change S.inverse (b x) - b (a (S.inverse (b x))) = b x at hrel
      have ha := congrArg a hrel
      simp only [map_sub] at ha
      simp only [Tinv, ContinuousLinearMap.comp_apply, sub_apply, add_apply,
        ContinuousLinearMap.id_apply, map_add]
      calc
        x - a (b x) + (a (S.inverse (b x)) -
              a (b (a (S.inverse (b x))))) =
            x - a (b x) + a (b x) := by rw [ha]
        _ = x := by abel
    · apply ContinuousLinearMap.ext
      intro x
      have hrel := hS.inverse_apply_self (b x)
      change S.inverse (S (b x)) = b x at hrel
      change S.inverse (b x - b (a (b x))) = b x at hrel
      rw [map_sub] at hrel
      have ha := congrArg a hrel
      simp only [map_sub] at ha
      simp only [Tinv, ContinuousLinearMap.comp_apply, sub_apply, add_apply,
        ContinuousLinearMap.id_apply, map_sub]
      calc
        x + a (S.inverse (b x)) -
              (a (b x) + a (S.inverse (b (a (b x))))) =
            x + (a (S.inverse (b x)) -
              a (S.inverse (b (a (b x))))) - a (b x) := by abel
        _ = x + a (b x) - a (b x) := by rw [ha]
        _ = x := by abel

/-! ## Local finite-range regularization of a compact pencil -/

/-- The analytically invertible remainder after freezing a finite-range
approximation `A` to `K` at one parameter. -/
def finiteRangeRegularFactor
    (K : ℂ → (X →L[ℂ] X)) (A : X →L[ℂ] X) (z : ℂ) : X →L[ℂ] X :=
  ContinuousLinearMap.id ℂ X - (K z - A)

/-- The finite-dimensional endomorphism obtained from the factorization

`1 - K(z) = (1 - A R(z)⁻¹) R(z)`

where `R(z) = 1 - (K(z) - A)`. -/
def finiteRangeReduction
    (K : ℂ → (X →L[ℂ] X)) (A : X →L[ℂ] X) (z : ℂ) :
    A.range →L[ℂ] A.range :=
  ContinuousLinearMap.id ℂ A.range -
    A.rangeRestrict.comp
      ((finiteRangeRegularFactor K A z).inverse.comp A.range.subtypeL)

/-- The finite-range reduction is analytic wherever the original family is
analytic and the regular factor is invertible. -/
theorem analyticOnNhd_finiteRangeReduction
    {K : ℂ → (X →L[ℂ] X)} {A : X →L[ℂ] X} {V : Set ℂ}
    (hK : AnalyticOnNhd ℂ K V)
    (hregular : ∀ z ∈ V, (finiteRangeRegularFactor K A z).IsInvertible) :
    AnalyticOnNhd ℂ (finiteRangeReduction K A) V := by
  intro z hz
  have hR : AnalyticAt ℂ (finiteRangeRegularFactor K A) z := by
    exact analyticAt_const.sub ((hK z hz).sub analyticAt_const)
  have hRinv : AnalyticAt ℂ
      (fun w ↦ (finiteRangeRegularFactor K A w).inverse) z :=
    analyticAt_inverse hR (hregular z hz)
  have hinner : AnalyticAt ℂ
      (fun w ↦ (finiteRangeRegularFactor K A w).inverse.comp A.range.subtypeL) z :=
    FiniteDimensionalSchur.analyticAt_clm_comp hRinv analyticAt_const
  have hfinite : AnalyticAt ℂ
      (fun w ↦ A.rangeRestrict.comp
        ((finiteRangeRegularFactor K A w).inverse.comp A.range.subtypeL)) z :=
    FiniteDimensionalSchur.analyticAt_clm_comp analyticAt_const hinner
  exact analyticAt_const.sub hfinite

omit [CompleteSpace X] in
/-- Exact invertibility criterion for the finite-range regularization.  This
is the operator-theoretic reduction to the finite-dimensional determinant. -/
theorem compactPencil_isInvertible_iff_finiteRangeReduction
    {K : ℂ → (X →L[ℂ] X)} {A : X →L[ℂ] X} {z : ℂ}
    (hregular : (finiteRangeRegularFactor K A z).IsInvertible) :
    (compactPencil K z).IsInvertible ↔
      (finiteRangeReduction K A z).IsInvertible := by
  let R : X →L[ℂ] X := finiteRangeRegularFactor K A z
  have hfactor : compactPencil K z =
      (ContinuousLinearMap.id ℂ X - A.comp R.inverse).comp R := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [compactPencil_apply, ContinuousLinearMap.comp_apply, sub_apply,
      ContinuousLinearMap.id_apply, R]
    rw [hregular.inverse_apply_self]
    simp only [finiteRangeRegularFactor, sub_apply,
      ContinuousLinearMap.id_apply]
    module
  rw [hfactor]
  rw [FiniteDimensionalDeterminant.isInvertible_comp_iff_of_right hregular]
  let a : A.range →L[ℂ] X := A.range.subtypeL
  let b : X →L[ℂ] A.range := A.rangeRestrict.comp R.inverse
  have hab : a.comp b = A.comp R.inverse := by
    ext x
    rfl
  have hba : b.comp a =
      A.rangeRestrict.comp (R.inverse.comp A.range.subtypeL) := by
    ext x
    rfl
  have hjac := isInvertible_id_sub_comp_iff a b
  rw [hab, hba] at hjac
  simpa only [finiteRangeReduction, R, a, b] using hjac

/-- A fixed finite-range approximation and an invertible analytic regular
factor produce an exact scalar reduction of the original compact pencil. -/
def scalarReductionOfFiniteRangeRegularization
    {K : ℂ → (X →L[ℂ] X)} (A : X →L[ℂ] X) (V : Set ℂ)
    [FiniteDimensional ℂ A.range]
    (hK : AnalyticOnNhd ℂ K V)
    (hregular : ∀ z ∈ V, (finiteRangeRegularFactor K A z).IsInvertible) :
    ScalarReduction (compactPencil K) V :=
  FiniteDimensionalSchur.scalarReductionOfFiniteDimensionalCriterion
    (compactPencil K) (finiteRangeReduction K A) V
    (analyticOnNhd_finiteRangeReduction hK hregular)
    (fun z hz ↦ compactPencil_isInvertible_iff_finiteRangeReduction
      (hregular z hz))

section CompactHilbert

universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every point of an analytic compact-operator pencil on a complex Hilbert
space has a connected open ball carrying an exact finite-dimensional scalar
reduction.  The proof freezes a finite-range approximation to `K(z₀)` with
error less than one and uses a Neumann inverse for the regular factor. -/
theorem exists_ball_scalarReduction_compactPencil
    {K : ℂ → (H →L[ℂ] H)} {U : Set ℂ} {z₀ : ℂ}
    (hUopen : IsOpen U) (hz₀U : z₀ ∈ U)
    (hKanalytic : AnalyticOnNhd ℂ K U)
    (hKcompact : ∀ z ∈ U, IsCompactOperator (K z)) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z₀ r ⊆ U ∧
      Nonempty (ScalarReduction (compactPencil K) (Metric.ball z₀ r)) := by
  obtain ⟨A, hAfin, herror⟩ :=
    CompactAtkinson.exists_hasFiniteRange_norm_sub_lt
      (hKcompact z₀ hz₀U) (epsilon := (1 / 2 : ℝ)) (by norm_num)
  have hR₀ : (finiteRangeRegularFactor K A z₀).IsInvertible := by
    have hsmall : ‖-(K z₀ - A)‖ < 1 := by
      rw [norm_neg]
      exact herror.trans (by norm_num)
    simpa only [finiteRangeRegularFactor, sub_eq_add_neg] using
      ContinuousLinearMap.isInvertible_id_add_of_norm_lt_one hsmall
  have hRanalytic : AnalyticAt ℂ (finiteRangeRegularFactor K A) z₀ := by
    exact analyticAt_const.sub
      ((hKanalytic z₀ hz₀U).sub analyticAt_const)
  have hReventually : ∀ᶠ z in 𝓝 z₀,
      (finiteRangeRegularFactor K A z).IsInvertible :=
    eventually_isInvertible hRanalytic.continuousAt hR₀
  have hcommon : U ∩
      {z | (finiteRangeRegularFactor K A z).IsInvertible} ∈ 𝓝 z₀ :=
    inter_mem (hUopen.mem_nhds hz₀U) hReventually
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hcommon
  have hballU : Metric.ball z₀ r ⊆ U := fun z hz ↦ (hball hz).1
  have hballRegular : ∀ z ∈ Metric.ball z₀ r,
      (finiteRangeRegularFactor K A z).IsInvertible :=
    fun z hz ↦ (hball hz).2
  let : FiniteDimensional ℂ A.range :=
    (Submodule.fg_iff_finiteDimensional A.range).1 hAfin.fg_range
  have hKball : AnalyticOnNhd ℂ K (Metric.ball z₀ r) :=
    fun z hz ↦ hKanalytic z (hballU hz)
  exact ⟨r, hr, hballU,
    ⟨scalarReductionOfFiniteRangeRegularization A (Metric.ball z₀ r)
      hKball hballRegular⟩⟩

end CompactHilbert

namespace ScalarReduction

omit [CompleteSpace X] in
/-- Once a connected open scalar-reduction patch contains one invertible
parameter, invertible parameters in that patch are dense in every ambient
set containing the patch.  The ambient-set formulation is useful when local
patches are assembled into an atlas. -/
theorem subset_closure_invertibleSet_inter
    (h : ScalarReduction F V) (hV : IsConnected V) (hVopen : IsOpen V)
    {z₀ : ℂ} (hz₀V : z₀ ∈ V) (hz₀ : (F z₀).IsInvertible)
    (hVU : V ⊆ U) :
    V ⊆ closure (invertibleSet F ∩ U) := by
  intro z hzV
  have hcod := h.eventually_isInvertible_of_mem hV hz₀V hz₀ hzV
  have hVnhds : ∀ᶠ w in 𝓝 z, w ∈ V := hVopen.mem_nhds hzV
  have hVevent : ∀ᶠ w in 𝓝[≠] z, w ∈ V :=
    hVnhds.filter_mono nhdsWithin_le_nhds
  have hgood : ∀ᶠ w in 𝓝[≠] z, w ∈ invertibleSet F ∩ U := by
    filter_upwards [hcod, hVevent] with w hw hwV
    exact ⟨hw.resolve_right (by simpa using hwV), hVU hwV⟩
  exact mem_closure_iff_frequently.mpr
    (hgood.frequently.filter_mono nhdsWithin_le_nhds)

end ScalarReduction

/-! ## Local reduction covers -/

/-- A cover by local scalar reductions.  Each point has a connected
open patch contained in the ambient domain.  The patch may depend on the
point, and no compatibility between its determinant and determinants on
other patches is assumed. -/
structure LocalScalarReductionCover
    (F : ℂ → (X →L[ℂ] X)) (U : Set ℂ) where
  /-- A local parameter patch around each point of the domain. -/
  patch : ∀ z : ℂ, z ∈ U → Set ℂ
  /-- The center belongs to its patch. -/
  mem_patch : ∀ z (hz : z ∈ U), z ∈ patch z hz
  /-- Patches are open. -/
  patch_isOpen : ∀ z (hz : z ∈ U), IsOpen (patch z hz)
  /-- Patches are connected. -/
  patch_isConnected : ∀ z (hz : z ∈ U), IsConnected (patch z hz)
  /-- Every patch remains in the ambient domain. -/
  patch_subset : ∀ z (hz : z ∈ U), patch z hz ⊆ U
  /-- The operator family has an exact scalar analytic reduction on every
  patch. -/
  reduction : ∀ z (hz : z ∈ U), ScalarReduction F (patch z hz)

namespace LocalScalarReductionCover

universe w

variable {H : Type w}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An analytic compact-operator family on an open complex domain has an
automatic local scalar-reduction cover.  No Fredholm alternative is assumed:
the patches are constructed directly from finite-range approximation and a
Neumann-regular factor. -/
theorem nonempty_compactPencil
    {K : ℂ → (H →L[ℂ] H)} {U : Set ℂ}
    (hUopen : IsOpen U) (hKanalytic : AnalyticOnNhd ℂ K U)
    (hKcompact : ∀ z ∈ U, IsCompactOperator (K z)) :
    Nonempty (LocalScalarReductionCover (compactPencil K) U) := by
  classical
  have hlocal : ∀ z : ℂ, ∀ hz : z ∈ U,
      ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ U ∧
        Nonempty (ScalarReduction (compactPencil K) (Metric.ball z r)) :=
    fun z hz ↦ exists_ball_scalarReduction_compactPencil
      hUopen hz hKanalytic hKcompact
  choose r hr hsubset hred using hlocal
  exact ⟨{
    patch := fun z hz ↦ Metric.ball z (r z hz)
    mem_patch := fun z hz ↦ Metric.mem_ball_self (hr z hz)
    patch_isOpen := fun _ _ ↦ Metric.isOpen_ball
    patch_isConnected := fun z hz ↦ Metric.isConnected_ball (hr z hz)
    patch_subset := fun z hz ↦ hsubset z hz
    reduction := fun z hz ↦ Classical.choice (hred z hz)
  }⟩

/-- A chosen automatic local scalar-reduction cover for an analytic compact
pencil on an open complex domain. -/
def compactPencilCover
    (K : ℂ → (H →L[ℂ] H)) (U : Set ℂ)
    (hUopen : IsOpen U) (hKanalytic : AnalyticOnNhd ℂ K U)
    (hKcompact : ∀ z ∈ U, IsCompactOperator (K z)) :
    LocalScalarReductionCover (compactPencil K) U :=
  Classical.choice (nonempty_compactPencil hUopen hKanalytic hKcompact)

omit [CompleteSpace X] in
/-- Analytic-Fredholm continuation through a local reduction cover.  If the
ambient domain is connected and contains one invertible parameter, its
invertible parameters are dense relative to the domain.

The proof considers `U ∩ closure (invertibleSet F ∩ U)`.  Local isolated-zero
theory makes this set open; it is relatively closed by construction, hence
connectedness forces it to contain all of `U`. -/
theorem subset_closure_invertibleSet_inter
    (atlas : LocalScalarReductionCover F U) (hU : IsConnected U)
    {z₀ : ℂ} (hz₀U : z₀ ∈ U) (hz₀ : (F z₀).IsInvertible) :
    U ⊆ closure (invertibleSet F ∩ U) := by
  let G : Set ℂ := U ∩ closure (invertibleSet F ∩ U)
  have hGopen : IsOpen G := by
    rw [isOpen_iff_mem_nhds]
    intro z hzG
    let Vz : Set ℂ := atlas.patch z hzG.1
    have hzVz : z ∈ Vz := atlas.mem_patch z hzG.1
    have hVzopen : IsOpen Vz := atlas.patch_isOpen z hzG.1
    have hfreq : ∃ᶠ w in 𝓝 z, w ∈ invertibleSet F ∩ U :=
      mem_closure_iff_frequently.mp hzG.2
    obtain ⟨w, hw, hwVz⟩ :=
      (hfreq.and_eventually (hVzopen.mem_nhds hzVz)).exists
    have hVzclosure : Vz ⊆ closure (invertibleSet F ∩ U) :=
      (atlas.reduction z hzG.1).subset_closure_invertibleSet_inter
        (atlas.patch_isConnected z hzG.1) hVzopen hwVz hw.1
        (atlas.patch_subset z hzG.1)
    exact Filter.mem_of_superset (hVzopen.mem_nhds hzVz) fun w hwVz' ↦
      ⟨atlas.patch_subset z hzG.1 hwVz', hVzclosure hwVz'⟩
  have hGnonempty : (U ∩ G).Nonempty := by
    refine ⟨z₀, hz₀U, hz₀U, ?_⟩
    exact subset_closure ⟨hz₀, hz₀U⟩
  have hclosureG : closure G ∩ U ⊆ G := by
    have hGsubset : G ⊆ closure (invertibleSet F ∩ U) := inter_subset_right
    have hclosureSubset : closure G ⊆ closure (invertibleSet F ∩ U) :=
      closure_minimal hGsubset isClosed_closure
    rintro z ⟨hzclosure, hzU⟩
    exact ⟨hzU, hclosureSubset hzclosure⟩
  have hUG : U ⊆ G :=
    hU.isPreconnected.subset_of_closure_inter_subset
      hGopen hGnonempty hclosureG
  exact fun z hzU ↦ (hUG hzU).2

omit [CompleteSpace X] in
/-- Every nonempty open subset of the connected domain contains an
invertible parameter. -/
theorem exists_invertible_on_isOpen
    (atlas : LocalScalarReductionCover F U) (hU : IsConnected U)
    {z₀ : ℂ} (hz₀U : z₀ ∈ U) (hz₀ : (F z₀).IsInvertible)
    (hVopen : IsOpen V) (hV : V.Nonempty) (hVU : V ⊆ U) :
    ∃ z ∈ V, (F z).IsInvertible := by
  obtain ⟨v, hvV⟩ := hV
  have hvclosure : v ∈ closure (invertibleSet F ∩ U) :=
    atlas.subset_closure_invertibleSet_inter hU hz₀U hz₀ (hVU hvV)
  have hfreq : ∃ᶠ z in 𝓝 v, z ∈ invertibleSet F ∩ U :=
    mem_closure_iff_frequently.mp hvclosure
  obtain ⟨z, hz, hzV⟩ :=
    (hfreq.and_eventually (hVopen.mem_nhds hvV)).exists
  exact ⟨z, hzV, hz.1⟩

end LocalScalarReductionCover

end AnalyticFredholm

end

end FastDynamo
