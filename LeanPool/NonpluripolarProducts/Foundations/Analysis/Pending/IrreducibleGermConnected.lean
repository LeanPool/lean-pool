/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GermParametrizationConnected
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GermParametrizationProof

/-!
# Connected dense regular parts of irreducible germs, off finitely many other germs

Blueprint `lag:local-statement-connected` (germ-level step) (Demailly, *Complex analytic and
differential geometry*, II.4.19, II.4.26).

For an irreducible analytic germ `A` at `0 ∈ ℂⁿ` and finitely many analytic germs `B_j` not
containing `A`, there are arbitrarily small open neighbourhoods `Δ` of `0` and a connected
set `G ⊆ A ∩ Δ`, dense in `A ∩ Δ`, avoiding every `B_j`, of regular points of `A ∩ Δ` of one
dimension `d`.  In the coordinates of Noether normalization this is
`GermParametrizationData.exists_isPreconnected_regularPart` with `g = ∏ h_j`, `h_j ∘ π = 0`
on `A ∩ B_j`; the data are carried back along the linear change of coordinates.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.IrreducibleGermConnected

open FirstPass AnalyticGermDecomposition GermParametrization RegularLocusDense

variable {n : ℕ}

/-- A product of two holomorphic germs, neither identically zero, is not identically zero. -/
theorem not_eventually_mul_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : E → ℂ} (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z) (hf0 : ¬ ∀ᶠ z in 𝓝 0, f z = 0)
    (hg0 : ¬ ∀ᶠ z in 𝓝 0, g z = 0) : ¬ ∀ᶠ z in 𝓝 0, f z * g z = 0 := by
  intro h
  have hmk : HolGerm.mk f hf * HolGerm.mk g hg = 0 := by
    rw [← HolGerm.mk_mul, ← HolGerm.mk_zero, HolGerm.mk_eq_mk_iff]
    exact h
  rcases mul_eq_zero.1 hmk with h1 | h1
  · rw [← HolGerm.mk_zero, HolGerm.mk_eq_mk_iff] at h1
    exact hf0 h1
  · rw [← HolGerm.mk_zero, HolGerm.mk_eq_mk_iff] at h1
    exact hg0 h1

/-- A finite product of holomorphic germs, none identically zero, is holomorphic near `0` and
not identically zero. -/
theorem finset_prod_holomorphic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (s : Finset ι) (f : ι → E → ℂ)
    (hd : ∀ j, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (f j) z)
    (h0 : ∀ j, ¬ ∀ᶠ z in 𝓝 0, f j z = 0) :
    (∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℂ (fun z => ∏ j ∈ s, f j z) z) ∧
      ¬ ∀ᶠ z in 𝓝 (0 : E), ∏ j ∈ s, f j z = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using NeBot.ne (nhds_neBot (x := (0 : E)))
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact ⟨((hd a).and ih.1).mono fun z hz => hz.1.mul hz.2,
      not_eventually_mul_eq_zero (hd a) ih.1 (h0 a) ih.2⟩

/-- **Connected dense regular parts off other germs.** -/
theorem exists_connected_nhds {A : Set (ComplexModel n)} (hA : IsIrreducibleGerm A) {m : ℕ}
    (B : Fin m → Set (ComplexModel n)) (hB : ∀ j, IsAnalyticGerm (B j))
    (hAB : ∀ j, ¬ A ≤ᶠ[𝓝 0] B j) {N : Set (ComplexModel n)} (hN : N ∈ 𝓝 0) :
    ∃ (d : ℕ) (Δ G : Set (ComplexModel n)), IsOpen Δ ∧ (0 : ComplexModel n) ∈ Δ ∧
      A ∩ Δ ⊆ N ∧ G ⊆ A ∩ Δ ∧ IsPreconnected G ∧ A ∩ Δ ⊆ closure G ∧
      (∀ y ∈ G, ∀ j, y ∉ B j) ∧
      ∀ y ∈ G, RegularAtDim (n := n) (M := ComplexModel n) (A ∩ Δ) y d := by
  classical
  have hprime : (vanishingIdeal A).IsPrime := (isIrreducibleGerm_iff_isPrime hA.1).1 hA
  obtain ⟨d₀, L, hNN⟩ := exists_isNoetherNormalization (vanishingIdeal A)
  rw [map_vanishingIdeal_comapEquiv] at hNN
  have : (vanishingIdeal (L ⁻¹' A)).IsPrime := by
    rw [← map_vanishingIdeal_comapEquiv]
    exact Ideal.map_isPrime_of_equiv _
  obtain ⟨AP⟩ := exists_algebraicParametrization hNN
  obtain ⟨P⟩ := GermParametrizationData.nonempty_parametrizationData
    (isAnalyticGerm_preimage L hA.1) AP
  obtain ⟨S⟩ := GermParametrizationData.nonempty_setsData P
  have hT := tendsto_linearEquiv_nhds_zero L.symm
  have hAB' : ∀ j, ¬ (L ⁻¹' A) ≤ᶠ[𝓝 0] (L ⁻¹' B j) := fun j h => by
    apply hAB j
    refine (hT.eventually h).mono fun z hz hzA => ?_
    have hz' : L.symm z ∈ L ⁻¹' A → L.symm z ∈ L ⁻¹' B j := hz
    have hzA' : z ∈ A := hzA
    have hzB : L.symm z ∈ L ⁻¹' B j := hz' (by simpa using hzA')
    change z ∈ B j
    simpa using hzB
  choose f hfd hfne hfB using fun j =>
    P.exists_eqn_of_not_le _ (isAnalyticGerm_preimage L (hB j)) (hAB' j)
  let g : ComplexModel P.dim → ℂ := fun x => ∏ j, f j x
  have hg := finset_prod_holomorphic Finset.univ f hfd hfne
  have hgd : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ g x := hg.1
  have hgne : ¬ ∀ᶠ x in 𝓝 0, g x = 0 := hg.2
  let N' : Set (ComplexModel n) := L ⁻¹' N ∩
    {z | ∀ j, z ∈ L ⁻¹' A → z ∈ L ⁻¹' B j → f j (coordinateProjection n P.dim z) = 0}
  have hN' : N' ∈ 𝓝 0 := inter_mem (tendsto_linearEquiv_nhds_zero L hN) (eventually_all.2 hfB)
  obtain ⟨Δ', hΔ'o, hΔ'0, hΔ'N, hconn, hdense, hreg⟩ :=
    GermParametrizationData.exists_isPreconnected_regularPart P S hgd hgne hN'
  let G' : Set (ComplexModel n) :=
    L ⁻¹' A ∩ Δ' ∩ coordinateProjection n P.dim ⁻¹' {x | P.disc x * g x ≠ 0}
  refine ⟨P.dim, L.symm ⁻¹' Δ', L.symm ⁻¹' G', hΔ'o.preimage L.symm.continuous,
    by simpa using hΔ'0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro z ⟨hzA, hzΔ⟩
    have hz : L.symm z ∈ N' := hΔ'N ⟨by simpa using hzA, hzΔ⟩
    simpa using hz.1
  · rintro z ⟨⟨hzA, hzΔ⟩, -⟩
    exact ⟨by simpa using hzA, hzΔ⟩
  · have h := hconn.image L L.continuous.continuousOn
    rwa [L.image_eq_preimage_symm] at h
  · rintro z ⟨hzA, hzΔ⟩
    have h1 : L.symm z ∈ closure G' := hdense ⟨by simpa using hzA, hzΔ⟩
    have hc : L.symm ⁻¹' closure G' = closure (L.symm ⁻¹' G') :=
      L.symm.toHomeomorph.preimage_closure G'
    rw [← hc]
    exact h1
  · rintro y ⟨⟨hyA, hyΔ⟩, hyg⟩ j hyB
    have hN'y : L.symm y ∈ N' := hΔ'N ⟨hyA, hyΔ⟩
    have h0 := hN'y.2 j hyA (by simpa using hyB)
    have hyg' : P.disc (coordinateProjection n P.dim (L.symm y)) *
        g (coordinateProjection n P.dim (L.symm y)) ≠ 0 := hyg
    exact (mul_ne_zero_iff.1 hyg').2 (Finset.prod_eq_zero (Finset.mem_univ j) h0)
  · rintro y ⟨⟨hyA, hyΔ⟩, hyg⟩
    have h := regularAtDim_preimage_linearEquiv L.symm (hreg _ ⟨hyA, hyΔ⟩ hyg)
    have hset : L.symm ⁻¹' (L ⁻¹' A ∩ Δ') = A ∩ L.symm ⁻¹' Δ' := by
      ext z; simp
    rwa [hset] at h

end SGPT.Foundations.Analysis.Pending.IrreducibleGermConnected
