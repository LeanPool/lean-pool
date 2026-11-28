/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Extension.ReflectionExtension
public import LeanPool.FunctionSpaces.Domains.Extension.SobolevExtensionOperator

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The extension operator for `W^1_p` on bounded Lipschitz domains, by reflection

Let `Ω` be a bounded Lipschitz domain in a finite-dimensional real inner product space `V` of
dimension `n ≥ 1`, and `1 ≤ p ≤ ∞`. There is a bounded linear operator `E` (built by reflection)
from the jets of `W^1_p(Ω)` to the jets of `W^1_p(V)` with `E u = u` on `Ω`
(`Rd.BoundedLipschitzDomain.sobolevExtensionL`,
`Rd.BoundedLipschitzDomain.restrictL_comp_sobolevExtensionL`), in the shape of TauCeti's
`W1p.exists_extensionL_of_isLipschitzDomainWith` (`Rd.BoundedLipschitzDomain.exists_extensionL`,
`Rd.exists_extensionL_of_isBoundedLipschitzDomain`). It is the chosen extension operator of the
project for every `1 ≤ p ≤ ∞`.

* **Linear extensions of functions** (`Rd.IsSobolevExtensionMap`): a linear map on functions
  `V → ℂ` that sees only the values on `O` and extends every Sobolev function on `O` from `U` with
  the constant `C` is an extension operator on jets
  (`Rd.IsSobolevExtensionMap.toSobolevExtensionOp`).
* **Bounded Lipschitz domains**: the boundary patches by a cutoff and reflection
  (`Rd.LipschitzGraph.reflectionExtensionLinearMap`) and the inner patch by a cutoff are linear
  extensions of functions (`Rd.BoundedLipschitzDomain.isSobolevExtensionMap_boundary_reflection`,
  `Rd.BoundedLipschitzDomain.isSobolevExtensionMap_interior_cutoff`), and pasting gives an
  extension operator from `Ω` (`Rd.BoundedLipschitzDomain.exists_sobolevExtensionOp_reflection`).
* **The extension theorem for `1 ≤ p ≤ ∞`** (Evans–Gariepy, Section 4.4): applied to single
  functions, the operators extend from the patches
  (`Rd.BoundedLipschitzDomain.exists_extendsSobolev_boundary_reflection`,
  `Rd.BoundedLipschitzDomain.exists_extendsSobolev_interior_cutoff`) and from `Ω` with a bound
  (`Rd.BoundedLipschitzDomain.exists_extendsSobolev_reflection`), so `W^1_p(Ω)` is the space of
  restrictions of `W^1_p(V)` in every dimension
  (`Rd.BoundedLipschitzDomain.memWeakSobolev_iff_exists_memSobolev`), and the value of
  every jet of `W^1_p(Ω)` lies in `W^1_p(Ω)`
  (`Rd.BoundedLipschitzDomain.memWeakSobolev_of_mem_weakSobolevJet`).
-/

@[expose] public section

open MeasureTheory Filter Topology TopologicalSpace Module Set Metric
open scoped ENNReal NNReal

namespace Rd

/-! ### Linear extensions of functions -/

section LinearExtensions

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞}

variable (p) in
/-- A **linear extension of Sobolev functions from `U` with constant `C`**: a complex linear map
`E` on functions `V → ℂ` such that `E f` depends only on the values of `f` on `O` up to null sets,
and every `f ∈ L_p(O)` with weak derivatives `g_i = ∂_{e_i} f ∈ L_p(O)` on `O` has an extension
`E f` with weak derivatives `G_i = ∂_{e_i} (E f)` on `V`, `E f = f` almost everywhere on `U`, and
`‖E f‖_p + ∑_i ‖G_i‖_p ≤ C (‖f‖_{L_p(O)} + ∑_i ‖g_i‖_{L_p(O)})`. -/
structure IsSobolevExtensionMap (O : Opens V) (U : Set V) (C : ℝ≥0∞)
    (E : (V → ℂ) →ₗ[ℂ] V → ℂ) : Prop where
  /-- `E f` depends only on the values of `f` on `O`, up to null sets. -/
  ae_eq_of_ae_eq : ∀ f f' : V → ℂ, f =ᵐ[volume.restrict (O : Set V)] f' → E f =ᵐ[volume] E f'
  /-- `E` extends Sobolev functions on `O` from `U` with the constant `C`. -/
  exists_hasWeakLineDeriv : ∀ (f : V → ℂ) (g : Fin (finrank ℝ V) → V → ℂ),
    MemLp f p (volume.restrict (O : Set V)) → (∀ i, MemLp (g i) p (volume.restrict (O : Set V))) →
    (∀ i, HasWeakLineDeriv O (fun _ : Fin 1 => gridBasis V i) f (g i)) →
    ∃ G : Fin (finrank ℝ V) → V → ℂ,
      (∀ i, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V i) (E f) (G i)) ∧
      (∀ᵐ x ∂volume, x ∈ U → E f x = f x) ∧
      eLpNorm (E f) p volume + ∑ i, eLpNorm (G i) p volume ≤
        C * (eLpNorm f p (volume.restrict (O : Set V)) +
          ∑ i, eLpNorm (g i) p (volume.restrict (O : Set V)))

namespace IsSobolevExtensionMap

variable [Fact (1 ≤ p)] {O : Opens V} {U : Set V} {C : ℝ≥0∞} {E : (V → ℂ) →ₗ[ℂ] V → ℂ}

/-- **A linear extension of a jet**: for a jet `u = (f, (g_i)_i)` of `W^1_p(O)`, `E f` has weak
derivatives `G_i` on `V`, agrees with `f` on `U`, and
`‖E f‖_p + ∑_i ‖G_i‖_p ≤ C (‖f‖_{L_p(O)} + ∑_i ‖g_i‖_{L_p(O)})`. -/
theorem exists_hasWeakLineDeriv_jet (hE : IsSobolevExtensionMap p O U C E)
    (u : weakSobolevJet p O) :
    ∃ G : Fin (finrank ℝ V) → V → ℂ,
      (∀ i, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V i) (E u.1.1) (G i)) ∧
      (∀ᵐ x ∂volume, x ∈ U → E u.1.1 x = u.1.1 x) ∧
      eLpNorm (E u.1.1) p volume + ∑ i, eLpNorm (G i) p volume ≤
        C * (‖u.1.1‖ₑ + ∑ i, ‖u.1.2 i‖ₑ) := by
  obtain ⟨G, hG, hU, hb⟩ := hE.exists_hasWeakLineDeriv u.1.1 (fun i => u.1.2 i) (Lp.memLp _)
    (fun i => Lp.memLp _) u.2
  exact ⟨G, hG, hU, by simpa only [Lp.eNorm_def] using hb⟩

/-- The linear extension of the value of a jet lies in `L_p(V)` for finite `C`
(`Rd.memLp_of_eLpNorm_add_sum_le`). -/
theorem memLp_apply (hE : IsSobolevExtensionMap p O U C E) (hC : C ≠ ∞)
    (u : weakSobolevJet p O) : MemLp (E u.1.1) p volume := by
  obtain ⟨G, -, -, hb⟩ := hE.exists_hasWeakLineDeriv_jet u
  exact (memLp_of_eLpNorm_add_sum_le hC (ENNReal.add_ne_top.2 ⟨eNorm_ne_top,
    ENNReal.sum_ne_top.2 fun _ _ => eNorm_ne_top⟩) hb).1

/-- **The values of the extension of jets**: `u = (f, (g_i)_i) ↦ E f`, a linear map from the jets
of `W^1_p(O)` into `L_p(V)`; it is additive and homogeneous since `E` is linear and sees only the
classes of the values on `O`. -/
noncomputable def valueMap (hE : IsSobolevExtensionMap p O U C E) (hC : C ≠ ∞) :
    weakSobolevJet p O →ₗ[ℂ] Lp ℂ p (volume : Measure V) where
  toFun u := (hE.memLp_apply hC u).toLp _
  map_add' u v := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ?_
    have h := hE.ae_eq_of_ae_eq _ _ (Lp.coeFn_add u.1.1 v.1.1)
    rw [map_add] at h
    exact h
  map_smul' c u := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ?_
    have h := hE.ae_eq_of_ae_eq _ _ (Lp.coeFn_smul c u.1.1)
    rw [map_smul] at h
    exact h

/-- The value map of a linear extension is the class of `E f`. -/
theorem valueMap_apply (hE : IsSobolevExtensionMap p O U C E) (hC : C ≠ ∞)
    (u : weakSobolevJet p O) : hE.valueMap hC u = (hE.memLp_apply hC u).toLp _ :=
  rfl

/-- **The derivatives of the extension of a jet**: the derivatives `G_i` of
`Rd.IsSobolevExtensionMap.exists_hasWeakLineDeriv_jet` lie in `L_p(V)` and are the weak derivatives
`∂_{e_i}` of the value map on `V`, with
`‖F‖_p + ∑_i ‖G_i‖_p ≤ C (‖f‖_{L_p(O)} + ∑_i ‖g_i‖_{L_p(O)})` for the value `F` of the extension
of the jet `u = (f, (g_i)_i)`. -/
theorem exists_hasWeakLineDeriv_valueMap (hE : IsSobolevExtensionMap p O U C E) (hC : C ≠ ∞)
    (u : weakSobolevJet p O) :
    ∃ G : Fin (finrank ℝ V) → Lp ℂ p (volume : Measure V),
      (∀ i, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V i) (hE.valueMap hC u) (G i)) ∧
      ‖hE.valueMap hC u‖ₑ + ∑ i, ‖G i‖ₑ ≤ C * (‖u.1.1‖ₑ + ∑ i, ‖u.1.2 i‖ₑ) := by
  obtain ⟨G, hG, -, hb⟩ := hE.exists_hasWeakLineDeriv_jet u
  have hm := memLp_of_eLpNorm_add_sum_le hC (ENNReal.add_ne_top.2 ⟨eNorm_ne_top,
    ENNReal.sum_ne_top.2 fun _ _ => eNorm_ne_top⟩) hb
  refine ⟨fun i => (hm.2 i).toLp (G i), fun i => (hG i).congr_ae ?_ ?_, ?_⟩
  · rw [volume_restrict_top, valueMap_apply]
    exact (hE.memLp_apply hC u).coeFn_toLp.symm
  · rw [volume_restrict_top]
    exact (hm.2 i).coeFn_toLp.symm
  · simpa only [valueMap_apply, Lp.eNorm_toLp] using hb

/-- The value map of a linear extension agrees with the value of the jet almost everywhere on
`U`. -/
theorem ae_valueMap_eq (hE : IsSobolevExtensionMap p O U C E) (hC : C ≠ ∞)
    (u : weakSobolevJet p O) : ∀ᵐ x ∂volume, x ∈ U → hE.valueMap hC u x = u.1.1 x := by
  obtain ⟨G, -, hU, -⟩ := hE.exists_hasWeakLineDeriv_jet u
  filter_upwards [(hE.memLp_apply hC u).coeFn_toLp, hU] with x h1 h2 hx
  rw [valueMap_apply, h1, h2 hx]

/-- **The bound of the extension of jets**: for weak derivatives `G_i = ∂_{e_i} F ∈ L_p(V)` of the
value `F` of the extension of a jet `u = (f, (g_i)_i)`,
`‖F‖_p + ∑_i ‖G_i‖_p ≤ C (‖f‖_{L_p(O)} + ∑_i ‖g_i‖_{L_p(O)})`; the `G_i` are those of
`Rd.IsSobolevExtensionMap.exists_hasWeakLineDeriv_valueMap` (`Rd.HasWeakLineDeriv.eq_of_top`). -/
theorem enorm_valueMap_add_le (hE : IsSobolevExtensionMap p O U C E) (hC : C ≠ ∞)
    (u : weakSobolevJet p O) {G : Fin (finrank ℝ V) → Lp ℂ p (volume : Measure V)}
    (hG : ∀ i, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V i) (hE.valueMap hC u) (G i)) :
    ‖hE.valueMap hC u‖ₑ + ∑ i, ‖G i‖ₑ ≤ C * (‖u.1.1‖ₑ + ∑ i, ‖u.1.2 i‖ₑ) := by
  obtain ⟨G', hG', hb⟩ := hE.exists_hasWeakLineDeriv_valueMap hC u
  have hGG : G = G' := funext fun i => (hG i).eq_of_top (hG' i)
  rw [hGG]
  exact hb

/-- **Linear extensions of functions are extension operators**: for finite `C`, the value map with
its weak derivatives (`Rd.sobolevJet.lift`) is an extension operator from `U` with the constant
`C`. -/
noncomputable def toSobolevExtensionOp (hE : IsSobolevExtensionMap p O U C E) (hC : C ≠ ∞) :
    SobolevExtensionOp p O U C :=
  let L := sobolevJet.lift (hE.valueMap hC) fun u i =>
    (hE.exists_hasWeakLineDeriv_valueMap hC u).elim fun G hG => ⟨G i, hG.1 i⟩
  { toLinearMap := L
    memSobolev := fun u => memSobolev_one_of_forall_gridBasis (L u).2
    ae_eq := hE.ae_valueMap_eq hC
    bound := fun u => hE.enorm_valueMap_add_le hC u fun i => (L u).2 i }

end IsSobolevExtensionMap

end LinearExtensions

/-! ### Extension operators on bounded Lipschitz domains -/

section BoundedDomains

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞}

/-- **Cutoffs see only the values on a set**: if `χ` has closed support in `B`, `s ∩ B ⊆ t` and
`f = f'` almost everywhere on `t`, then `χ f = χ f'` almost everywhere on `s`. -/
theorem mul_ae_eq_of_tsupport_subset {s t B : Set V} (hs : MeasurableSet s) (ht : MeasurableSet t)
    {χ : V → ℝ} (hχ : tsupport χ ⊆ B) (hst : s ∩ B ⊆ t) {f f' : V → ℂ}
    (h : f =ᵐ[volume.restrict t] f') :
    (fun x => (χ x : ℂ) * f x) =ᵐ[volume.restrict s] fun x => (χ x : ℂ) * f' x := by
  refine (ae_restrict_iff' hs).2 ?_
  filter_upwards [(ae_restrict_iff' ht).1 h] with x hx hxs
  by_cases hxB : x ∈ B
  · rw [hx (hst ⟨hxs, hxB⟩)]
  · rw [image_eq_zero_of_notMem_tsupport fun h => hxB (hχ h), Complex.ofReal_zero, zero_mul,
      zero_mul]

namespace BoundedLipschitzDomain

variable (Ω : BoundedLipschitzDomain V)

/-- **The boundary patches by reflection are linear**: for `1 ≤ p ≤ ∞`, `ε ≥ 0` and a smooth `χ`
with values in `[0, 1]`, closed support in `B(c_j, ρ_j)`, `|∂_{e_i} χ| ≤ d_i` and `χ = 1` near
`closedBall(c_j, ρ_j - 2ε)`, the map `f ↦ E_j(χ f)` (the extension by reflection in the graph
domain `Ω_j`)
is a linear extension of Sobolev functions on `Ω` from `Ω ∩ B(c_j, ρ_j - 2ε)` with the constant
`Rd.reflectionConst` (`Rd.BoundedLipschitzDomain.exists_hasWeakLineDeriv_reflectionExtension_mul`,
`Rd.BoundedLipschitzDomain.reflectionExtension_mul_eq_of_mem`). -/
theorem isSobolevExtensionMap_boundary_reflection [Fact (1 ≤ p)] (j : Fin Ω.N) {ε : ℝ}
    (hε : 0 ≤ ε) {χ : V → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχB : tsupport χ ⊆ ball (Ω.center j) (Ω.radius j)) (hχ01 : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    {d : Fin (finrank ℝ V) → ℝ≥0} (hd : ∀ i x, ‖fderiv ℝ χ x (gridBasis V i)‖ ≤ d i)
    (hχ1 : ∀ᶠ x in 𝓝ˢ (closedBall (Ω.center j) (Ω.radius j - 2 * ε)), χ x = 1) :
    IsSobolevExtensionMap p Ω.toOpens (Ω.carrier ∩ ball (Ω.center j) (Ω.radius j - 2 * ε))
      (reflectionConst (finrank ℝ V) (Ω.graph j).M (∑ i, (d i : ℝ≥0∞)))
      ((Ω.graph j).reflectionExtensionLinearMap.comp
        (LinearMap.mulLeft ℂ fun x => (χ x : ℂ))) where
  ae_eq_of_ae_eq f f' h := (Ω.graph j).reflectionExtension_congr_ae
    (mul_ae_eq_of_tsupport_subset (Ω.graph j).measurableSet_domain Ω.measurableSet hχB
      (fun x hx => Ω.graph_toOpens_inf_ball_le j hx) h)
  exists_hasWeakLineDeriv f g hf hg hfg := by
    obtain ⟨G, hG, hb⟩ := Ω.exists_hasWeakLineDeriv_reflectionExtension_mul j Fact.out hχ hχB
      hχ01 hd hf hg hfg
    exact ⟨G, hG, ae_of_all _ fun x hx => Ω.reflectionExtension_mul_eq_of_mem j hε hχ1 f hx, hb⟩

/-- **The boundary patches by reflection carry extension operators**: for `1 ≤ p ≤ ∞` and
`ε > 0` there is an extension operator from `Ω ∩ B(c_j, ρ_j - 2ε)` with a finite constant
(`Rd.BoundedLipschitzDomain.isSobolevExtensionMap_boundary_reflection` with the cutoff of
`Rd.BoundedLipschitzDomain.exists_cutoff_boundary`). -/
theorem exists_sobolevExtensionOp_boundary_reflection [Fact (1 ≤ p)] {ε : ℝ} (hε : 0 < ε)
    (j : Fin Ω.N) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ Nonempty (SobolevExtensionOp p Ω.toOpens
      (Ω.carrier ∩ ball (Ω.center j) (Ω.radius j - 2 * ε)) C) := by
  obtain ⟨χ, hχ, hχc, hχB, hχ01, hχ1⟩ := Ω.exists_cutoff_boundary hε j
  obtain ⟨d, hd⟩ := exists_norm_fderiv_gridBasis_le hχ hχc
  have hC := reflectionConst_ne_top (finrank ℝ V) (Ω.graph j).M
    (ENNReal.sum_ne_top.2 fun i _ => ENNReal.coe_ne_top : ∑ i, (d i : ℝ≥0∞) ≠ ∞)
  exact ⟨_, hC, ⟨(Ω.isSobolevExtensionMap_boundary_reflection j hε.le hχ hχB hχ01 hd
    hχ1).toSobolevExtensionOp hC⟩⟩

/-- **The boundary patches by reflection**: for `1 ≤ p ≤ ∞` and `ε > 0`, Sobolev functions on `Ω`
extend from `Ω ∩ B(c_j, ρ_j - 2ε)` with a finite constant, by the extension operator of the patch
(`Rd.BoundedLipschitzDomain.exists_sobolevExtensionOp_boundary_reflection`,
`Rd.SobolevExtensionOp.extendsSobolev`). -/
theorem exists_extendsSobolev_boundary_reflection [Fact (1 ≤ p)] {ε : ℝ} (hε : 0 < ε)
    (j : Fin Ω.N) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ExtendsSobolev p Ω.toOpens
      (Ω.carrier ∩ ball (Ω.center j) (Ω.radius j - 2 * ε)) C := by
  obtain ⟨C, hC, ⟨E⟩⟩ := Ω.exists_sobolevExtensionOp_boundary_reflection (p := p) hε j
  exact ⟨C, hC, E.extendsSobolev fun _ hx => hx.1⟩

/-- **The inner patch by a cutoff is linear**: for `1 ≤ p ≤ ∞` and a smooth `χ` with values in
`[0, 1]`, compact closed support in `Ω`, `|∂_{e_i} χ| ≤ d_i` and `χ = 1` near
`{infDist(·, Ωᶜ) ≥ 2δ}`, the map `f ↦ χ f` is a linear extension of Sobolev functions on `Ω` from
`{x ∈ Ω : infDist(x, Ωᶜ) > 2δ}` with the constant `1 + ∑_i d_i`
(`Rd.BoundedLipschitzDomain.exists_hasWeakLineDeriv_mul_interior`). -/
theorem isSobolevExtensionMap_interior_cutoff [Fact (1 ≤ p)] {δ : ℝ} {χ : V → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω.carrier) (hχ01 : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    {d : Fin (finrank ℝ V) → ℝ≥0} (hd : ∀ i x, ‖fderiv ℝ χ x (gridBasis V i)‖ ≤ d i)
    (hχ1 : ∀ᶠ x in 𝓝ˢ {x : V | 2 * δ ≤ infDist x Ω.carrierᶜ}, χ x = 1) :
    IsSobolevExtensionMap p Ω.toOpens (Ω.carrier ∩ {x : V | 2 * δ < infDist x Ω.carrierᶜ})
      (1 + ∑ i, (d i : ℝ≥0∞)) (LinearMap.mulLeft ℂ fun x => (χ x : ℂ)) where
  ae_eq_of_ae_eq f f' h := by
    have h' := mul_ae_eq_of_tsupport_subset (s := univ) MeasurableSet.univ Ω.measurableSet hχΩ
      (fun x hx => hx.2) h
    rwa [Measure.restrict_univ] at h'
  exists_hasWeakLineDeriv f g _ _ hfg := by
    obtain ⟨G, hG, hU, hb⟩ :=
      Ω.exists_hasWeakLineDeriv_mul_interior (p := p) Fact.out hχ hχc hχΩ hχ01 hd hχ1 hfg
    exact ⟨G, hG, ae_of_all _ hU, hb⟩

/-- **The inner patch carries an extension operator**: for `1 ≤ p ≤ ∞` and `δ > 0` there is an
extension operator from `{x ∈ Ω : infDist(x, Ωᶜ) > 2δ}` with a finite constant
(`Rd.BoundedLipschitzDomain.isSobolevExtensionMap_interior_cutoff` with the cutoff of
`Rd.BoundedLipschitzDomain.exists_cutoff_interior`). -/
theorem exists_sobolevExtensionOp_interior_cutoff [Fact (1 ≤ p)] {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ Nonempty (SobolevExtensionOp p Ω.toOpens
      (Ω.carrier ∩ {x : V | 2 * δ < infDist x Ω.carrierᶜ}) C) := by
  obtain ⟨χ, hχ, hχc, hχΩ, hχ01, hχ1⟩ := Ω.exists_cutoff_interior hδ
  obtain ⟨d, hd⟩ := exists_norm_fderiv_gridBasis_le hχ hχc
  have hC : 1 + ∑ i, (d i : ℝ≥0∞) ≠ ∞ := by simp [ENNReal.sum_eq_top]
  exact ⟨_, hC, ⟨(Ω.isSobolevExtensionMap_interior_cutoff hχ hχc hχΩ hχ01 hd
    hχ1).toSobolevExtensionOp hC⟩⟩

/-- **The inner patch by a cutoff**: for `1 ≤ p ≤ ∞` and `δ > 0`, Sobolev functions on `Ω` extend
from `{x ∈ Ω : infDist(x, Ωᶜ) > 2δ}` with a finite constant, by the extension operator of the patch
(`Rd.BoundedLipschitzDomain.exists_sobolevExtensionOp_interior_cutoff`,
`Rd.SobolevExtensionOp.extendsSobolev`). -/
theorem exists_extendsSobolev_interior_cutoff [Fact (1 ≤ p)] {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ExtendsSobolev p Ω.toOpens
      (Ω.carrier ∩ {x : V | 2 * δ < infDist x Ω.carrierᶜ}) C := by
  obtain ⟨C, hC, ⟨E⟩⟩ := Ω.exists_sobolevExtensionOp_interior_cutoff (p := p) hδ
  exact ⟨C, hC, E.extendsSobolev fun _ hx => hx.1⟩

/-- **The extension operator by reflection with a finite constant**: for a bounded Lipschitz
domain `Ω` in dimension `n ≥ 1` and `1 ≤ p ≤ ∞` there is an extension operator from `Ω` with a
finite constant (`Rd.BoundedLipschitzDomain.exists_sobolevExtensionOp_of_patches` with the patch
operators `Rd.BoundedLipschitzDomain.exists_sobolevExtensionOp_boundary_reflection` and
`Rd.BoundedLipschitzDomain.exists_sobolevExtensionOp_interior_cutoff`). -/
theorem exists_sobolevExtensionOp_reflection [Fact (1 ≤ p)] [Nontrivial V] :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ Nonempty (SobolevExtensionOp p Ω.toOpens Ω.carrier C) :=
  Ω.exists_sobolevExtensionOp_of_patches
    (fun _ hε j => Ω.exists_sobolevExtensionOp_boundary_reflection hε j)
    (fun _ hδ => Ω.exists_sobolevExtensionOp_interior_cutoff hδ)

/-- **The extension theorem for `1 ≤ p ≤ ∞` with a bound**: for a bounded Lipschitz domain `Ω` in
dimension `n ≥ 1` and `1 ≤ p ≤ ∞` there is a finite constant `C` such that every `f ∈ L_p(Ω)` with
weak derivatives `g_i = ∂_{e_i} f ∈ L_p(Ω)` agrees on `Ω` with some `F ∈ W^1_p(V)` whose weak
derivatives `G_i = ∂_{e_i} F` satisfy
`‖F‖_p + ∑_i ‖G_i‖_p ≤ C (‖f‖_{L_p(Ω)} + ∑_i ‖g_i‖_{L_p(Ω)})`: the extension operator by
reflection (`Rd.BoundedLipschitzDomain.exists_sobolevExtensionOp_reflection`) applied to `f`
(`Rd.SobolevExtensionOp.extendsSobolev`). -/
theorem exists_extendsSobolev_reflection [Nontrivial V] (hp : 1 ≤ p) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ExtendsSobolev p Ω.toOpens Ω.carrier C := by
  have : Fact (1 ≤ p) := ⟨hp⟩
  obtain ⟨C, hC, ⟨E⟩⟩ := Ω.exists_sobolevExtensionOp_reflection (p := p)
  exact ⟨C, hC, E.extendsSobolev subset_rfl⟩

/-- **The extension theorem for `W^1_p`, `1 ≤ p ≤ ∞`** (Evans–Gariepy, Section 4.4; Brezis 2011,
Chapter 9): for a bounded Lipschitz domain `Ω` and `1 ≤ p ≤ ∞`, every `f ∈ W^1_p(Ω)` agrees almost
everywhere on `Ω` with some `F ∈ W^1_p(V)`
(`Rd.BoundedLipschitzDomain.exists_extendsSobolev_reflection` in dimension `n ≥ 1`,
`Rd.exists_memSobolev_of_memWeakSobolev_of_subsingleton` in dimension `0`). -/
theorem exists_memSobolev_of_memWeakSobolev (hp : 1 ≤ p) {f : V → ℂ}
    (hf : MemWeakSobolev Ω.toOpens 1 p f) :
    ∃ F : Lp ℂ p (volume : Measure V), MemSobolev 1 F ∧
      (F : V → ℂ) =ᵐ[volume.restrict Ω.carrier] f := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact exists_memSobolev_of_memWeakSobolev_of_subsingleton hf
  obtain ⟨C, -, hC⟩ := Ω.exists_extendsSobolev_reflection hp
  choose g hg hfg using fun i => hf.2 1 le_rfl fun _ => gridBasis V i
  obtain ⟨F, hF, hFf, -⟩ := hC f g hf.1 hg hfg
  exact ⟨F, hF, (ae_restrict_iff' Ω.measurableSet).2 hFf⟩

/-- **`W^1_p(Ω)` is the space of restrictions of `W^1_p(V)` for `1 ≤ p ≤ ∞`**: for a bounded
Lipschitz domain `Ω`, `f` lies in `W^1_p(Ω)` iff it agrees almost everywhere on `Ω` with some
`F ∈ W^1_p(V)` (`Rd.BoundedLipschitzDomain.exists_memSobolev_of_memWeakSobolev`; the
converse restricts the weak derivatives, `Rd.MemWeakSobolev.mono_set`). -/
theorem memWeakSobolev_iff_exists_memSobolev (hp : 1 ≤ p) (f : V → ℂ) :
    MemWeakSobolev Ω.toOpens 1 p f ↔ ∃ F : Lp ℂ p (volume : Measure V), MemSobolev 1 F ∧
      (F : V → ℂ) =ᵐ[volume.restrict Ω.carrier] f := by
  refine ⟨Ω.exists_memSobolev_of_memWeakSobolev hp, ?_⟩
  rintro ⟨F, hF, hFf⟩
  exact (MemWeakSobolev.mono_set hF le_top).congr_ae hFf

variable (p) in
/-- **The extension operator for `W^1_p`, `1 ≤ p ≤ ∞`** (Evans–Gariepy, Section 4.4, by
reflection): for a bounded Lipschitz domain `Ω` in dimension `n ≥ 1`, a bounded linear operator
`E` from the jets of `W^1_p(Ω)` to the jets of `W^1_p(V)` with `E u = u` on `Ω`, chosen among the
extension operators of `Rd.BoundedLipschitzDomain.exists_sobolevExtensionOp_reflection`. -/
noncomputable def sobolevExtensionL [Fact (1 ≤ p)] [Nontrivial V] :
    weakSobolevJet p Ω.toOpens →L[ℂ] sobolevJet (V := V) p :=
  SobolevExtensionOp.toContinuousLinearMap
    (Classical.choice (Ω.exists_sobolevExtensionOp_reflection (p := p)).choose_spec.2)
    (Ω.exists_sobolevExtensionOp_reflection (p := p)).choose_spec.1

/-- The values of the extension operator lie in `W^1_p(V)`. -/
theorem memSobolev_sobolevExtensionL [Fact (1 ≤ p)] [Nontrivial V]
    (u : weakSobolevJet p Ω.toOpens) : MemSobolev 1 (Ω.sobolevExtensionL p u).1.1 :=
  (Classical.choice (Ω.exists_sobolevExtensionOp_reflection (p := p)).choose_spec.2).memSobolev u

/-- **The extension operator extends**: the value of `E u` agrees with the value of `u` almost
everywhere on `Ω`. -/
theorem sobolevExtensionL_fst_ae_eq [Fact (1 ≤ p)] [Nontrivial V]
    (u : weakSobolevJet p Ω.toOpens) :
    ⇑(Ω.sobolevExtensionL p u).1.1 =ᵐ[volume.restrict Ω.carrier] ⇑u.1.1 :=
  (ae_restrict_iff' Ω.measurableSet).2
    ((Classical.choice (Ω.exists_sobolevExtensionOp_reflection (p := p)).choose_spec.2).ae_eq u)

/-- **The value of every jet of `W^1_p(Ω)` lies in `W^1_p(Ω)`** for `1 ≤ p ≤ ∞`: it agrees on `Ω`
with the value of `E u ∈ W^1_p(V)` (`Rd.BoundedLipschitzDomain.memSobolev_sobolevExtensionL`,
`Rd.BoundedLipschitzDomain.sobolevExtensionL_fst_ae_eq`). With
`Rd.exists_mem_weakSobolevJet_of_memWeakSobolev`, the values of the jets of `W^1_p(Ω)` are exactly
the functions of `W^1_p(Ω)`. On every open set the same follows from the weak derivatives along
the basis (`Rd.hasWeakLineDeriv_of_forall_gridBasis`). -/
theorem memWeakSobolev_of_mem_weakSobolevJet [Fact (1 ≤ p)] [Nontrivial V]
    (u : weakSobolevJet p Ω.toOpens) : MemWeakSobolev Ω.toOpens 1 p u.1.1 :=
  ((Ω.memSobolev_sobolevExtensionL u).mono_set le_top).congr_ae (Ω.sobolevExtensionL_fst_ae_eq u)

/-- **The bound of the extension operator** in the norm `‖f‖_p + ∑_i ‖g_i‖_p`: there is a finite
`C` with `‖F‖_p + ∑_i ‖G_i‖_p ≤ C (‖f‖_{L_p(Ω)} + ∑_i ‖g_i‖_{L_p(Ω)})` for `E (f, g) = (F, G)`. -/
theorem exists_enorm_sobolevExtensionL_le [Fact (1 ≤ p)] [Nontrivial V] :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ u : weakSobolevJet p Ω.toOpens,
      ‖(Ω.sobolevExtensionL p u).1.1‖ₑ + ∑ i, ‖(Ω.sobolevExtensionL p u).1.2 i‖ₑ ≤
        C * (‖u.1.1‖ₑ + ∑ i, ‖u.1.2 i‖ₑ) :=
  ⟨_, (Ω.exists_sobolevExtensionOp_reflection (p := p)).choose_spec.1,
    (Classical.choice (Ω.exists_sobolevExtensionOp_reflection (p := p)).choose_spec.2).bound⟩

/-- **Restriction after extension is the identity**: `(E u)|_Ω = u` for every jet `u` of
`W^1_p(Ω)` (`Rd.SobolevExtensionOp.restrictL_comp_toContinuousLinearMap`). -/
theorem restrictL_comp_sobolevExtensionL [Fact (1 ≤ p)] [Nontrivial V] :
    (sobolevJet.restrictL Ω.toOpens).comp (Ω.sobolevExtensionL p) =
      ContinuousLinearMap.id ℂ _ :=
  SobolevExtensionOp.restrictL_comp_toContinuousLinearMap _ _ subset_rfl

/-- **The extension theorem in operator form** (TauCeti's
`W1p.exists_extensionL_of_isLipschitzDomainWith`): for a bounded Lipschitz domain `Ω` in dimension
`n ≥ 1` and `1 ≤ p ≤ ∞` there is a bounded linear operator `E` from the jets of `W^1_p(Ω)` to the
jets of `W^1_p(V)` that is a right inverse of the restriction and has values in `W^1_p(V)`. -/
theorem exists_extensionL [Fact (1 ≤ p)] [Nontrivial V] :
    ∃ E : weakSobolevJet p Ω.toOpens →L[ℂ] sobolevJet (V := V) p,
      (sobolevJet.restrictL Ω.toOpens).comp E = ContinuousLinearMap.id ℂ _ ∧
        ∀ u, MemSobolev 1 (E u).1.1 :=
  ⟨Ω.sobolevExtensionL p, Ω.restrictL_comp_sobolevExtensionL, Ω.memSobolev_sobolevExtensionL⟩

end BoundedLipschitzDomain

/-- **The extension theorem in operator form for the usual definition**: for a bounded Lipschitz
set `Ω` (`Rd.IsBoundedLipschitzDomain`) in dimension `n ≥ 1` and `1 ≤ p ≤ ∞` there is a bounded
linear extension operator from the jets of `W^1_p(Ω)` to those of `W^1_p(V)`
(`Rd.BoundedLipschitzDomain.exists_extensionL` for
`Rd.BoundedLipschitzDomain.ofIsBoundedLipschitzDomain`). -/
theorem exists_extensionL_of_isBoundedLipschitzDomain [Fact (1 ≤ p)] [Nontrivial V]
    {Ω : Set V} (h : IsBoundedLipschitzDomain Ω) :
    ∃ E : weakSobolevJet p ⟨Ω, h.1⟩ →L[ℂ] sobolevJet (V := V) p,
      (sobolevJet.restrictL ⟨Ω, h.1⟩).comp E = ContinuousLinearMap.id ℂ _ ∧
        ∀ u, MemSobolev 1 (E u).1.1 :=
  (BoundedLipschitzDomain.ofIsBoundedLipschitzDomain h).exists_extensionL

end BoundedDomains

end Rd
