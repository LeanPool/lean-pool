/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Extension.ReflectionExtensionOperator

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# `W^1_p` on bounded Lipschitz domains as the space of restrictions

Let `Ω` be a bounded Lipschitz domain in a finite-dimensional real inner product space `V` of
dimension `n`. By the extension theorem, every `f ∈ W^1_p(Ω)` (weak derivatives on `Ω`)
agrees on `Ω` with some `F ∈ W^1_p(V)`, for every `1 ≤ p ≤ ∞`, by reflection
(`Rd.BoundedLipschitzDomain.memWeakSobolev_iff_exists_memSobolev`). For `p = 2` this gives:

* `H^1(Ω) = W^1_2(Ω)`: the restriction space `H^1(Ω)` is the weak-derivative space
  (`Rd.BoundedLipschitzDomain.memSobolevOn_iff_memWeakSobolev`,
  `Rd.BoundedLipschitzDomain.memWeakSobolev_iff_exists_restrictL2`);
* Rellich's theorem in `W^1_2(Ω)`
  (`Rd.BoundedLipschitzDomain.exists_subseq_tendsto_of_memWeakSobolev`), from the bounded
  extensions of `Rd.BoundedLipschitzDomain.exists_extendsSobolev`;
* the quotient norm of `H^1(Ω)` is bounded by the `W^1_2(Ω)` norm
  (`Rd.BoundedLipschitzDomain.exists_norm_le_restrictL2`), so the two norms are equivalent;
* the boundary traces of `H^1(Ω)` serve for `W^1_2(Ω)`
  (`Rd.BoundedLipschitzDomain.exists_isBoundaryTrace_of_memWeakSobolev`,
  `Rd.BoundedLipschitzDomain.isBoundaryTrace_unique_of_memWeakSobolev`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric TopologicalSpace
open scoped ENNReal SchwartzMap FourierTransform LineDeriv Real BesselPotentialSpace

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞}

namespace BoundedLipschitzDomain

variable (Ω : BoundedLipschitzDomain V)

/-- **`H^1(Ω) = W^1_2(Ω)`**: for a bounded Lipschitz domain `Ω`, `f ∈ L_2(V)`
lies in the restriction space `H^1(Ω)` iff it lies in the Sobolev space
`W^1_2(Ω)` of weak derivatives on `Ω`. -/
theorem memSobolevOn_iff_memWeakSobolev (f : Lp ℂ 2 (volume : Measure V)) :
    Ω.MemSobolevOn f ↔ MemWeakSobolev Ω.toOpens 1 2 f :=
  (Ω.memWeakSobolev_iff_exists_memSobolev one_le_two f).symm

/-- **Rellich's theorem in `W^1_2(Ω)`**, the form with weak derivatives: for a bounded
Lipschitz domain `Ω` in dimension `n ≥ 1`, every sequence `f_n ∈ L_2(Ω)` with weak derivatives
`g_{n,i} = ∂_{e_i} f_n ∈ L_2(Ω)` and `‖f_n‖_{L_2(Ω)} + ∑_i ‖g_{n,i}‖_{L_2(Ω)} ≤ M` has a
subsequence converging in `L_2(Ω)`: the bounded extensions
(`Rd.BoundedLipschitzDomain.exists_extendsSobolev`) are bounded in `W^1_2(V)`, and Rellich's
compactness on `V` (`Rd.exists_subseq_tendsto_restr_of_hasWeakLineDeriv`) gives the subsequence.
-/
theorem exists_subseq_tendsto_of_memWeakSobolev [Nontrivial V] {f : ℕ → V → ℂ}
    {g : ℕ → Fin (finrank ℝ V) → V → ℂ} (hf : ∀ n, MemLp (f n) 2 (volume.restrict Ω.carrier))
    (hg : ∀ n i, MemLp (g n i) 2 (volume.restrict Ω.carrier))
    (hfg : ∀ n i, HasWeakLineDeriv Ω.toOpens (fun _ : Fin 1 => gridBasis V i) (f n) (g n i))
    {M : ℝ≥0∞} (hM : M ≠ ∞) (hb : ∀ n, eLpNorm (f n) 2 (volume.restrict Ω.carrier) +
      ∑ i, eLpNorm (g n i) 2 (volume.restrict Ω.carrier) ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u : Lp ℂ 2 (volume.restrict Ω.carrier),
      Tendsto (fun k => eLpNorm (f (φ k) - (u : V → ℂ)) 2 (volume.restrict Ω.carrier)) atTop
        (𝓝 0) := by
  obtain ⟨C, hC, hext⟩ := Ω.exists_extendsSobolev (p := 2) ENNReal.one_lt_two ENNReal.ofNat_ne_top
  choose F hF hFf G hG hFG using fun n => hext (f n) (g n) (hf n) (hg n) (hfg n)
  have hK : C * M ≠ ∞ := ENNReal.mul_ne_top hC hM
  obtain ⟨φ, hφ, u, hu⟩ := exists_subseq_tendsto_restr_of_hasWeakLineDeriv Ω.isBounded
    (gridBasis V) hG (M := (C * M).toReal) fun n =>
      sq_norm_add_sum_sq_le hK ((hFG n).trans (mul_le_mul_right (hb n) _))
  refine ⟨φ, hφ, u, ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 hu).congr fun k => ?_⟩
  refine eLpNorm_congr_ae (EventuallyEq.sub ?_ EventuallyEq.rfl)
  exact (LpToLpRestrictCLM_coeFn ℂ _ _).trans ((ae_restrict_iff' Ω.measurableSet).2 (hFf (φ k)))

/-- **The quotient norm of `H^1(Ω)` is bounded by the `W^1_2(Ω)` norm**: for a bounded Lipschitz
domain `Ω` in dimension `n ≥ 1` there is a constant `C` such that every `u ∈ H^1(Ω)` and all
`g_i ∈ L_2(Ω)` with `g_i = ∂_{e_i} u` weakly on `Ω` (`u` read as its `L_2` function) satisfy
`‖u‖_{H^1(Ω)} ≤ C (‖u|_Ω‖_{L_2(Ω)} + ∑_i ‖g_i‖_{L_2(Ω)})`. With
`Rd.sq_norm_restrictL2_add_sum_le`, the quotient norm of `H^1(Ω)` and the `W^1_2(Ω)` norm are
equivalent. The bounded extension `F` of `u|_Ω` (`Rd.BoundedLipschitzDomain.exists_extendsSobolev`)
is an element of `H^1(V)` whose restriction is `u` (`Rd.restrictProj_eq_of_ae_eq`). -/
theorem exists_norm_le_restrictL2 [Nontrivial V] :
    ∃ C : ℝ, ∀ (u : RestrictionSpace 1 Ω.toOpens)
      (g : Fin (finrank ℝ V) → Lp ℂ 2 (volume.restrict Ω.carrier)),
      (∀ i, HasWeakLineDeriv Ω.toOpens (fun _ : Fin 1 => gridBasis V i)
        (toL2 (u : H^{1}(V))) (g i)) →
      ‖u‖ ≤ C * (‖restrictL2 Ω.toOpens u‖ + ∑ i, ‖g i‖) := by
  obtain ⟨C, hC, hext⟩ := Ω.exists_extendsSobolev (p := 2) ENNReal.one_lt_two ENNReal.ofNat_ne_top
  refine ⟨C.toReal, fun u g hg => ?_⟩
  have hf : MemLp (toL2 (u : H^{1}(V)) : V → ℂ) 2 (volume.restrict Ω.carrier) :=
    (Lp.memLp _).restrict _
  obtain ⟨F, hF, hFf, G, hG, hb⟩ := hext _ (fun i => g i) hf (fun i => Lp.memLp (g i)) hg
  have hS := (memSobolev_one_iff F).1 hF
  have hU : toL2 hS.toBesselPotentialSpace = F :=
    toL2_eq_of_toDistr_eq _ hS.toBesselPotentialSpace_toDistr.symm
  have hproj : restrictProj 1 Ω.toOpens hS.toBesselPotentialSpace = u :=
    restrictProj_eq_of_ae_eq (by rw [hU]; exact (ae_restrict_iff' Ω.measurableSet).2 hFf)
  have hY : eLpNorm (toL2 (u : H^{1}(V)) : V → ℂ) 2 (volume.restrict (Ω.toOpens : Set V)) +
      ∑ i, eLpNorm (g i : V → ℂ) 2 (volume.restrict (Ω.toOpens : Set V)) =
      ENNReal.ofReal (‖restrictL2 Ω.toOpens u‖ + ∑ i, ‖g i‖) := by
    rw [ENNReal.ofReal_add (norm_nonneg _) (Finset.sum_nonneg fun i _ => norm_nonneg _),
      ENNReal.ofReal_sum_of_nonneg fun i _ => norm_nonneg _, ofReal_norm, restrictL2_apply,
      Lp.eNorm_def, eLpNorm_congr_ae (LpToLpRestrictCLM_coeFn ℂ _ _)]
    simp_rw [ofReal_norm, Lp.eNorm_def]
    rfl
  rw [hY] at hb
  have hFG : ‖F‖ + ∑ i, ‖G i‖ ≤ C.toReal * (‖restrictL2 Ω.toOpens u‖ + ∑ i, ‖g i‖) := by
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) hb
    rwa [toReal_enorm_add_sum, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h1
  calc ‖u‖ = ‖restrictProj 1 Ω.toOpens hS.toBesselPotentialSpace‖ := by rw [hproj]
    _ ≤ ‖hS.toBesselPotentialSpace‖ := norm_restrictProj_apply_le _
    _ ≤ ‖toL2 hS.toBesselPotentialSpace‖ + ∑ i, ‖G i‖ :=
        norm_le_norm_toL2_add_sum (gridBasis V) _ fun i => by rw [hU]; exact hG i
    _ ≤ _ := by rw [hU]; exact hFG

/-- **`W^1_2(Ω)` and the Hilbert space `H^1(Ω)`**: for a bounded Lipschitz domain `Ω`,
`f ∈ L_2(V)` lies in `W^1_2(Ω)` iff its restriction to `Ω` is `u|_Ω` for some `u` in
the Hilbert space `H^1(Ω)` (`Rd.BoundedLipschitzDomain.memSobolevOn_iff_memWeakSobolev`,
`Rd.BoundedLipschitzDomain.memSobolevOn_iff_exists_restrictL2`). -/
theorem memWeakSobolev_iff_exists_restrictL2 (f : Lp ℂ 2 (volume : Measure V)) :
    MemWeakSobolev Ω.toOpens 1 2 f ↔ ∃ u : RestrictionSpace 1 Ω.toOpens,
      restrictL2 Ω.toOpens u = LpToLpRestrictCLM V ℂ ℂ volume 2 Ω.carrier f := by
  rw [← Ω.memSobolevOn_iff_memWeakSobolev f, Ω.memSobolevOn_iff_exists_restrictL2 f]

/-- **The boundary trace of a function of `W^1_2(Ω)`**: for a bounded Lipschitz domain `Ω`, every
resolution of unity `ψ` on the boundary `Γ` and every `f ∈ L_2(V)` whose restriction lies in
`W^1_2(Ω)`, `f` has a boundary trace `g ∈ B^{1/2}_{2,2}(Γ)`
(`Rd.BoundedLipschitzDomain.exists_isBoundaryTrace_of_memSobolevOn` through
`Rd.BoundedLipschitzDomain.memSobolevOn_iff_memWeakSobolev`). -/
theorem exists_isBoundaryTrace_of_memWeakSobolev (ψ : Ω.BoundaryPartition)
    {f : Lp ℂ 2 (volume : Measure V)} (hf : MemWeakSobolev Ω.toOpens 1 2 f) :
    ∃ g : V → ℂ, Ω.MemBoundaryBesov 2 ψ (1 / 2) 2 g ∧
      Ω.IsBoundaryTrace ψ two_ne_top 2 1 2 f g :=
  exists_isBoundaryTrace_of_memSobolevOn ψ ((Ω.memSobolevOn_iff_memWeakSobolev f).2 hf)

/-- **The boundary trace of a function of `W^1_2(Ω)` is unique** up to null sets of the boundary:
for every resolution of unity `ψ` on `Γ` and every `f ∈ L_2(V)` whose restriction lies in
`W^1_2(Ω)`, two boundary traces `g`, `g'` of `f` agree almost everywhere on `Γ`
(`Rd.BoundedLipschitzDomain.MemSobolevOn.isBoundaryTrace_unique` through
`Rd.BoundedLipschitzDomain.memSobolevOn_iff_memWeakSobolev`). -/
theorem isBoundaryTrace_unique_of_memWeakSobolev (ψ : Ω.BoundaryPartition)
    {f : Lp ℂ 2 (volume : Measure V)} (hf : MemWeakSobolev Ω.toOpens 1 2 f) {g g' : V → ℂ}
    (hg : Ω.IsBoundaryTrace ψ two_ne_top 2 1 2 f g)
    (hg' : Ω.IsBoundaryTrace ψ two_ne_top 2 1 2 f g') : g =ᶠ[Ω.aeBoundary] g' :=
  MemSobolevOn.isBoundaryTrace_unique ψ ((Ω.memSobolevOn_iff_memWeakSobolev f).2 hf) hg hg'

end BoundedLipschitzDomain

end Rd
