/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GermParametrizationProof
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.RegularPointDimension
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HolomorphicZeroSetThin

/-!
# Local structure of irreducible analytic germs

Two consequences of the local parametrization theorem for an irreducible analytic germ `A`
at `0 ∈ ℂⁿ` (Demailly, *Complex analytic and differential geometry*, II.4.19--4.26), in the
form used to assemble the local statement (LS):

* `exists_pure_nhds` (blueprint `lag:irreducible-germ-pure`): there are `d` and an open
  neighbourhood `Ω` of `0` such that on every open `Ω' ⊆ Ω`, EVERY regular point of `A ∩ Ω'`
  has dimension `d` and the regular points of dimension `d` are dense in `A ∩ Ω'`;
* `exists_thin_nhds` (blueprint `lag:thin-subgerm`): if `B` is an analytic germ with
  `A ⊄ B` near `0`, then on some open neighbourhood `Ω` of `0` the set `A ∩ B ∩ Ω` has empty
  interior relative to `A ∩ Ω`.

Regular points are taken in `ℂⁿ` regarded as a complex manifold with its identity chart.
Both are derived from the local parametrization data
`GermParametrization.LocalParametrization`: a regular point of `A ∩ Ω'` of dimension `k`
has nearby points of the dense regular part `good`, which are regular of dimension `d`
(`RegularPointDimension.eq_of_regularAtDim`); and if a nonempty relatively open part of
`A` lay in `B`, the equation `h ∘ π = 0` would hold on the nonempty open set `π(O ∩ good)`,
contradicting `h ≢ 0` (`RiemannExtension.dense_compl_zeroSet`).
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.IrreducibleGermLocal

open FirstPass AnalyticGermDecomposition GermParametrization RegularPointDimension

variable {n : ℕ}

/-- **Representatives of irreducible germs are pure-dimensional.** -/
theorem exists_pure_nhds {A : Set (ComplexModel n)} (hA : IsIrreducibleGerm A) :
    ∃ d : ℕ, ∃ Ω : Set (ComplexModel n), IsOpen Ω ∧ (0 : ComplexModel n) ∈ Ω ∧
      ∀ Ω' : Set (ComplexModel n), IsOpen Ω' → Ω' ⊆ Ω →
        (∀ {y : ComplexModel n} {k : ℕ},
          RegularAtDim (n := n) (M := ComplexModel n) (A ∩ Ω') y k → k = d) ∧
        A ∩ Ω' ⊆ closure (regularLocus (n := n) (M := ComplexModel n) (A ∩ Ω') d) := by
  obtain ⟨P⟩ := exists_localParametrization hA
  refine ⟨P.dim, P.nbhd, P.isOpen_nbhd, P.zero_mem_nbhd, fun Ω' hΩ' hsub => ⟨?_, ?_⟩⟩
  all_goals
    have heq : A ∩ P.nbhd ∩ Ω' = A ∩ Ω' ∩ Ω' := by
      ext z
      exact ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.2⟩, fun h => ⟨⟨h.1.1, hsub h.2⟩, h.2⟩⟩
  · intro y k hy
    obtain ⟨W, hWsub, hWo, hyW⟩ := mem_nhds_iff.mp
      ((RegularPatchNeighborhood.eventually_regularAtDim hy).and (hΩ'.mem_nhds hy.2.1.2))
    obtain ⟨z, hzW, hzg⟩ :=
      mem_closure_iff.mp (P.subset_closure_good ⟨hy.2.1.1, hsub hy.2.1.2⟩) W hWo hyW
    have hzA := P.good_subset hzg
    have hz1 : RegularAtDim (n := n) (M := ComplexModel n) (A ∩ Ω') z k :=
      (hWsub hzW).1 ⟨hzA.1, (hWsub hzW).2⟩
    have hz2 : RegularAtDim (n := n) (M := ComplexModel n) (A ∩ Ω') z P.dim :=
      regularAtDim_of_inter_eq hΩ' (hWsub hzW).2 heq (P.regularAtDim_of_mem_good z hzg)
    exact eq_of_regularAtDim hz1 hz2
  · intro y hy
    rw [mem_closure_iff]
    intro O hO hyO
    obtain ⟨z, ⟨hzO, hzΩ'⟩, hzg⟩ := mem_closure_iff.mp
      (P.subset_closure_good ⟨hy.1, hsub hy.2⟩) (O ∩ Ω') (hO.inter hΩ') ⟨hyO, hy.2⟩
    exact ⟨z, hzO, regularAtDim_of_inter_eq hΩ' hzΩ' heq (P.regularAtDim_of_mem_good z hzg)⟩

/-- **Proper analytic subgerms of an irreducible germ are thin.** -/
theorem exists_thin_nhds {A B : Set (ComplexModel n)} (hA : IsIrreducibleGerm A)
    (hB : IsAnalyticGerm B) (hAB : ¬ A ≤ᶠ[𝓝 0] B) :
    ∃ Ω : Set (ComplexModel n), IsOpen Ω ∧ (0 : ComplexModel n) ∈ Ω ∧
      ∀ O : Set (ComplexModel n), IsOpen O → (O ∩ (A ∩ Ω)).Nonempty →
        ∃ y ∈ O ∩ (A ∩ Ω), y ∉ B := by
  obtain ⟨P⟩ := exists_localParametrization hA
  obtain ⟨h, hhd, hhne, hhB⟩ := P.exists_eqn_of_not_le B hB hAB
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hhd
  obtain ⟨U, hUsub, hUo, hU0⟩ := mem_nhds_iff.mp hhB
  let Ω := P.nbhd ∩ U ∩ P.proj ⁻¹' Metric.ball 0 ρ
  have hΩo : IsOpen Ω :=
    (P.isOpen_nbhd.inter hUo).inter (Metric.isOpen_ball.preimage P.proj.continuous)
  refine ⟨Ω, hΩo, ⟨⟨P.zero_mem_nbhd, hU0⟩, by simp [hρ]⟩, fun O hO hne => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨y, hyO, hyA, hyΩ⟩ := hne
  obtain ⟨z, ⟨hzO, hzΩ⟩, hzg⟩ := mem_closure_iff.mp
    (P.subset_closure_good ⟨hyA, hyΩ.1.1⟩) (O ∩ Ω) (hO.inter hΩo) ⟨hyO, hyΩ⟩
  have hVo : IsOpen (P.proj '' ((O ∩ Ω) ∩ P.good)) :=
    P.isOpen_image_inter_good _ (hO.inter hΩo)
  have hV0 : ∀ v ∈ P.proj '' ((O ∩ Ω) ∩ P.good), h v = 0 := by
    rintro _ ⟨w, ⟨⟨hwO, hwΩ⟩, hwg⟩, rfl⟩
    have hwA := (P.good_subset hwg).1
    exact hUsub hwΩ.1.2 hwA (hcon w ⟨hwO, hwA, hwΩ⟩)
  have hdense := RiemannExtension.dense_compl_zeroSet Metric.isOpen_ball
    (convex_ball (0 : ComplexModel P.dim) ρ).isPreconnected
    (fun w hw => (hball w hw).differentiableWithinAt) (Metric.mem_ball_self hρ) hhne
  have hzV : P.proj z ∈ P.proj '' ((O ∩ Ω) ∩ P.good) := ⟨z, ⟨⟨hzO, hzΩ⟩, hzg⟩, rfl⟩
  obtain ⟨v, hvV, -, hvnz⟩ := mem_closure_iff.mp (hdense hzΩ.2) _ hVo hzV
  exact hvnz (hV0 v hvV)

end SGPT.Foundations.Analysis.Pending.IrreducibleGermLocal
