/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GermPrimitiveElement
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GermParametrizationFunctions
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GermParametrizationSets
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GermParametrizationDense
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.RegularAtDimChart

/-!
# The local parametrization theorem for irreducible germs

Blueprint `lag:parametrization-dense` and its predecessors (Demailly, *Complex analytic and
differential geometry*, II.4.19).

For an irreducible analytic germ `A` at `0 ∈ ℂⁿ` the vanishing ideal is prime; after a
linear change of coordinates `L` it is in Noether position over `𝒪_d`
(`exists_isNoetherNormalization`), and the transformed ideal is the vanishing ideal of
`L⁻¹ A` (`map_vanishingIdeal_comapEquiv`).  The algebraic data
(`exists_algebraicParametrization`), the pointwise identities, the parametrizing sets and
density give `LocalParametrization (L⁻¹ A)`, which is carried back to `A` along `L`
(`LocalParametrization.transport`).
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.GermParametrization

open FirstPass AnalyticGermDecomposition HolGerm GermAlgebraicParametrization

variable {n : ℕ}

/-- Regular points pull back along linear automorphisms of the model space. -/
theorem regularAtDim_preimage_linearEquiv (T : ComplexModel n ≃L[ℂ] ComplexModel n)
    {B : Set (ComplexModel n)} {x : ComplexModel n} {k : ℕ}
    (h : RegularAtDim (n := n) (M := ComplexModel n) B (T x) k) :
    RegularAtDim (n := n) (M := ComplexModel n) (T ⁻¹' B) x k := by
  obtain ⟨hk, hxB, Φ, -, hΦ0, hflat⟩ := h
  let T' : OpenPartialHomeomorph (ComplexModel n) (ComplexModel n) :=
    T.toHomeomorph.toOpenPartialHomeomorph
  refine ⟨hk, hxB, RegularAtDimChart.precomp T' T.differentiable.differentiableOn
    T.symm.differentiable.differentiableOn (c := x) (q := T x) (mem_univ _) rfl Φ,
    fun _ _ => mem_univ _, hΦ0, ?_⟩
  intro y _ hy
  exact hflat (y := T y) (mem_univ _) hy.2

theorem tendsto_linearEquiv_nhds_zero (T : ComplexModel n ≃L[ℂ] ComplexModel n) :
    Tendsto T (𝓝 0) (𝓝 0) := by
  simpa using T.continuous.tendsto 0

/-- Analytic germs pull back along linear automorphisms. -/
theorem isAnalyticGerm_preimage (T : ComplexModel n ≃L[ℂ] ComplexModel n)
    {B : Set (ComplexModel n)} (hB : IsAnalyticGerm B) : IsAnalyticGerm (T ⁻¹' B) := by
  obtain ⟨s, g, hg, hB⟩ := hB
  have hT := tendsto_linearEquiv_nhds_zero T
  refine ⟨s, fun j => g j ∘ T, fun j => ?_, hT.eventually hB⟩
  exact (hT.eventually (hg j)).mono fun z hz => hz.comp z T.differentiableAt

/-- The vanishing ideal of `L⁻¹ A` is the transform of the vanishing ideal of `A`. -/
theorem map_vanishingIdeal_comapEquiv (L : ComplexModel n ≃L[ℂ] ComplexModel n)
    (A : Set (ComplexModel n)) :
    (vanishingIdeal A).map (comapEquiv L) = vanishingIdeal (L ⁻¹' A) := by
  ext φ
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨ψ, ⟨f, hf, rfl, hfA⟩, rfl⟩
    exact ⟨f ∘ L, _, comapEquiv_mk L f hf, (tendsto_linearEquiv_nhds_zero L).eventually hfA⟩
  · rintro ⟨f, hf, rfl, hfA⟩
    refine ⟨(comapEquiv L).symm (mk f hf), ⟨f ∘ L.symm, _, comapEquiv_symm_mk L f hf, ?_⟩,
      by simp⟩
    exact ((tendsto_linearEquiv_nhds_zero L.symm).eventually hfA).mono fun z hz hzA =>
      hz (by simpa using hzA)

/-- Local parametrization data carried along a linear change of coordinates. -/
noncomputable def LocalParametrization.transport (L : ComplexModel n ≃L[ℂ] ComplexModel n)
    {A : Set (ComplexModel n)} (P : LocalParametrization (L ⁻¹' A)) :
    LocalParametrization A where
  dim := P.dim
  proj := P.proj.comp (L.symm : ComplexModel n →L[ℂ] ComplexModel n)
  nbhd := L.symm ⁻¹' P.nbhd
  isOpen_nbhd := P.isOpen_nbhd.preimage L.symm.continuous
  zero_mem_nbhd := by simpa using P.zero_mem_nbhd
  good := L.symm ⁻¹' P.good
  good_subset := fun z hz => by
    have := P.good_subset hz
    exact ⟨by simpa using this.1, this.2⟩
  regularAtDim_of_mem_good := fun y hy => by
    have h := regularAtDim_preimage_linearEquiv L.symm (P.regularAtDim_of_mem_good _ hy)
    have hset : L.symm ⁻¹' (L ⁻¹' A ∩ P.nbhd) = A ∩ L.symm ⁻¹' P.nbhd := by
      ext z; simp
    rwa [hset] at h
  isOpen_image_inter_good := fun O hO => by
    have hset : (P.proj.comp (L.symm : ComplexModel n →L[ℂ] ComplexModel n)) ''
        (O ∩ L.symm ⁻¹' P.good) = P.proj '' ((L ⁻¹' O) ∩ P.good) := by
      ext v
      simp only [mem_image, mem_inter_iff, mem_preimage, ContinuousLinearMap.coe_comp,
        Function.comp_apply, ContinuousLinearEquiv.coe_coe]
      constructor
      · rintro ⟨z, ⟨hzO, hzg⟩, rfl⟩
        exact ⟨L.symm z, ⟨by simpa using hzO, hzg⟩, rfl⟩
      · rintro ⟨w, ⟨hwO, hwg⟩, rfl⟩
        exact ⟨L w, ⟨hwO, by simpa using hwg⟩, by simp⟩
    rw [hset]
    exact P.isOpen_image_inter_good _ (hO.preimage L.continuous)
  subset_closure_good := fun z hz => by
    have h := P.subset_closure_good ⟨by simpa using hz.1, hz.2⟩
    have hc : L.symm ⁻¹' closure P.good = closure (L.symm ⁻¹' P.good) :=
      (L.symm.toHomeomorph.preimage_closure P.good)
    rw [← hc]
    exact h
  exists_eqn_of_not_le := fun B hB hAB => by
    have hAB' : ¬ (L ⁻¹' A) ≤ᶠ[𝓝 0] (L ⁻¹' B) := by
      intro h
      apply hAB
      have := (tendsto_linearEquiv_nhds_zero L.symm).eventually h
      refine this.mono fun z hz hzA => ?_
      have hz' : L.symm z ∈ L ⁻¹' A → L.symm z ∈ L ⁻¹' B := hz
      have hzA' : z ∈ A := hzA
      have hzB : L.symm z ∈ L ⁻¹' B := hz' (by simpa using hzA')
      change z ∈ B
      simpa using hzB
    obtain ⟨h, hhd, hhne, hhB⟩ := P.exists_eqn_of_not_le _ (isAnalyticGerm_preimage L hB) hAB'
    refine ⟨h, hhd, hhne, ?_⟩
    refine ((tendsto_linearEquiv_nhds_zero L.symm).eventually hhB).mono fun z hz hzA hzB => ?_
    exact hz (by simpa using hzA) (by simpa using hzB)

/-- **Algebraic parametrization of a prime in Noether position.** -/
theorem exists_algebraicParametrization {Q : Ideal (HolGerm (ComplexModel n))} [Q.IsPrime]
    {d : ℕ} (hQ : IsNoetherNormalization Q d) : Nonempty (AlgebraicParametrization Q d) := by
  classical
  obtain ⟨c, W, δ, B, hW, hWdeg, hWmem, hWdvd, hδ, hBdeg, hBmem, hrec, hbez⟩ :=
    GermPrimitiveElement.exists_primitiveElement hQ
  have hcoord : ∀ k : Fin n, ∃ p : Polynomial (HolGerm (ComplexModel d)),
      IsWeierstrass p ∧ evalGerm n p (coord k) ∈ Q := fun k => by
    have h0 : HolGerm.eval (coord k) = 0 := by
      simp [coord, coordGerm, HolGerm.eval_mk]
    obtain ⟨p, hp, -, hpm, -⟩ := GermMinimalPolynomial.exists_minpoly_isWeierstrass hQ _ h0
    exact ⟨p, hp, hpm⟩
  choose p hp hpm using hcoord
  exact ⟨{ le := hQ.le
           eq_zero_of_mem := hQ.eq_zero_of_mem
           coordPoly := p
           isWeierstrass_coordPoly := fun k _ => hp k
           coordPoly_mem := fun k _ => hpm k
           coef := c
           minpoly := W
           isWeierstrass_minpoly := hW
           natDegree_minpoly_pos := hWdeg
           minpoly_mem := hWmem
           dvd_of_mem := hWdvd
           disc := δ
           disc_ne_zero := hδ
           B := B
           natDegree_B_lt := hBdeg
           disc_mul_sub_mem := hBmem
           dvd_recover := hrec
           bezout := hbez
           exists_eqn := fun f hf => GermMinimalPolynomial.exists_eqn_of_not_mem hQ hf
           reduce := GermMinimalPolynomial.exists_reduce hQ.le p fun k _ => hp k }⟩

/-- **Local parametrization theorem** (output form), blueprint `lag:parametrization-dense`. -/
theorem exists_localParametrization {A : Set (ComplexModel n)} (hA : IsIrreducibleGerm A) :
    Nonempty (LocalParametrization A) := by
  have hprime : (vanishingIdeal A).IsPrime := (isIrreducibleGerm_iff_isPrime hA.1).1 hA
  obtain ⟨d, L, hN⟩ := exists_isNoetherNormalization (vanishingIdeal A)
  rw [map_vanishingIdeal_comapEquiv] at hN
  have : (vanishingIdeal (L ⁻¹' A)).IsPrime := by
    rw [← map_vanishingIdeal_comapEquiv]
    exact Ideal.map_isPrime_of_equiv _
  obtain ⟨AP⟩ := exists_algebraicParametrization hN
  obtain ⟨PD⟩ := GermParametrizationData.nonempty_parametrizationData
    (isAnalyticGerm_preimage L hA.1) AP
  obtain ⟨SD⟩ := GermParametrizationData.nonempty_setsData PD
  obtain ⟨LP⟩ := GermParametrizationData.nonempty_localParametrization PD SD
  exact ⟨LP.transport L⟩

end SGPT.Foundations.Analysis.Pending.GermParametrization
