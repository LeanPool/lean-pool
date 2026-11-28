/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Extension.SobolevExtension
public import LeanPool.FunctionSpaces.Domains.Lipschitz.LocalLipschitzGraphs
public import LeanPool.FunctionSpaces.Rd.Sobolev.SobolevJets

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Rychkov's extension operator for `W^1_p` on bounded Lipschitz domains

Let `Ω` be a bounded Lipschitz domain in a finite-dimensional real inner product space `V` of
dimension `n ≥ 1`, and `1 < p < ∞`. Rychkov's local extension gives a linear extension operator
from the jets of `W^1_p(Ω)` to the jets of `W^1_p(V)` (`Rd.weakSobolevJet`, `Rd.sobolevJet`) with
a finite constant (`Rd.BoundedLipschitzDomain.exists_sobolevExtensionOp`).

* **Extension operators** (`Rd.SobolevExtensionOp p O U C`): linear maps from the jets on `O` to the
  jets on `V` that agree with the value on `U` and have the constant `C` in the norm
  `‖f‖_p + ∑_i ‖g_i‖_p`; they give the extensions of `Rd.ExtendsSobolev`
  (`Rd.SobolevExtensionOp.extendsSobolev`), and for a finite constant bounded linear operators
  (`Rd.SobolevExtensionOp.toContinuousLinearMap`).
* **One patch** (`Rd.LocalMeansBump.sobolevExtensionOp`): Rychkov's local extension
  `∑_j η_j ⋆ 1_W (k_j ⋆ 1_T f)` converges for every jet, so it is linear in the jet; applied to
  one function it is the extension from one patch (`Rd.LocalMeansBump.extendsSobolev`).
* **Pasting** (`Rd.sobolevExtensionOp_of_cover`): `∑_k ψ_k E_k u` for a smooth resolution of unity
  `(ψ_k)`, with the derivatives of the product rule.
* **Bounded Lipschitz domains**: the boundary and inner patches carry extension operators
  (`Rd.BoundedLipschitzDomain.exists_sobolevExtensionOp_boundary`,
  `Rd.BoundedLipschitzDomain.exists_sobolevExtensionOp_interior`), pasted to one from `Ω`
  (`Rd.BoundedLipschitzDomain.exists_sobolevExtensionOp_of_patches`, for every `1 ≤ p ≤ ∞`;
  `Rd.BoundedLipschitzDomain.exists_sobolevExtensionOp`).
* **The extension theorem** (Calderón and Stein, here by Rychkov's extension): every `f ∈ L_p(Ω)`
  with weak derivatives `g_i = ∂_{e_i} f ∈ L_p(Ω)` agrees on `Ω` with some `F ∈ W^1_p(V)` with
  `‖F‖_p + ∑_i ‖∂_{e_i} F‖_p ≤ C (‖f‖_{L_p(Ω)} + ∑_i ‖g_i‖_{L_p(Ω)})`
  (`Rd.BoundedLipschitzDomain.exists_extendsSobolev`), and the same holds on every patch
  (`Rd.BoundedLipschitzDomain.exists_extendsSobolev_boundary`,
  `Rd.BoundedLipschitzDomain.exists_extendsSobolev_interior`): each is an extension operator
  applied to one function.
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric TopologicalSpace
open scoped ENNReal

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Extension operators -/

variable (p) in
/-- An **extension operator for `W^1_p` from `U` with constant `C`**: a linear map `E` from the jets
of `W^1_p(O)` to the jets of `W^1_p(V)` whose values lie in `W^1_p(V)`, agree with the value of the
jet almost everywhere on `U`, and satisfy
`‖F‖_p + ∑_i ‖G_i‖_p ≤ C (‖f‖_{L_p(O)} + ∑_i ‖g_i‖_{L_p(O)})` for `E (f, g) = (F, G)`. The
condition on `U` is meant for `U ⊆ O`, the case of every use. -/
structure SobolevExtensionOp (O : Opens V) (U : Set V) (C : ℝ≥0∞) where
  /-- The linear map on jets. -/
  toLinearMap : weakSobolevJet p O →ₗ[ℂ] sobolevJet (V := V) p
  /-- The values lie in `W^1_p(V)`. -/
  memSobolev : ∀ u, MemSobolev 1 (toLinearMap u).1.1
  /-- The value of `E u` agrees with the value of `u` almost everywhere on `U`. -/
  ae_eq : ∀ u, ∀ᵐ x ∂volume, x ∈ U → (toLinearMap u).1.1 x = u.1.1 x
  /-- The bound with the constant `C`. -/
  bound : ∀ u, ‖(toLinearMap u).1.1‖ₑ + ∑ i, ‖(toLinearMap u).1.2 i‖ₑ ≤
    C * (‖u.1.1‖ₑ + ∑ i, ‖u.1.2 i‖ₑ)

namespace SobolevExtensionOp

variable {O : Opens V} {U : Set V} {C : ℝ≥0∞}

/-- **Extension operators give extensions**: an extension operator from `U ⊆ O` extends every
`f ∈ L_p(O)` with weak derivatives `g_i ∈ L_p(O)` in the sense of `Rd.ExtendsSobolev`, applied to
the jet of the classes of `f` and `g_i`. -/
theorem extendsSobolev (E : SobolevExtensionOp p O U C) (hUO : U ⊆ O) :
    ExtendsSobolev p O U C := by
  intro f g hf hg hfg
  let u : weakSobolevJet p O := ⟨(hf.toLp f, fun i => (hg i).toLp (g i)), fun i =>
    (hfg i).congr_ae hf.coeFn_toLp.symm (hg i).coeFn_toLp.symm⟩
  refine ⟨(E.toLinearMap u).1.1, E.memSobolev u, ?_, (E.toLinearMap u).1.2,
    (E.toLinearMap u).2, ?_⟩
  · filter_upwards [E.ae_eq u, (ae_restrict_iff' O.isOpen.measurableSet).1 hf.coeFn_toLp]
      with x h1 h2 hxU
    rw [h1 hxU]
    exact h2 (hUO hxU)
  · refine (E.bound u).trans_eq ?_
    simp only [u, Lp.eNorm_toLp]

/-- The norm bound of an extension operator in the product norm of the jets:
`‖E u‖ ≤ (n + 1) C ‖u‖` for finite `C` (`Rd.norm_le_norm_fst_add_sum`,
`Rd.norm_fst_add_sum_le`). -/
theorem norm_apply_le (E : SobolevExtensionOp p O U C) (hC : C ≠ ∞) (u : weakSobolevJet p O) :
    ‖E.toLinearMap u‖ ≤ (finrank ℝ V + 1) * C.toReal * ‖u‖ := by
  have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top hC (ENNReal.add_ne_top.2
    ⟨eNorm_ne_top, ENNReal.sum_ne_top.2 fun _ _ => eNorm_ne_top⟩)) (E.bound u)
  rw [ENNReal.toReal_mul, toReal_enorm_add_sum, toReal_enorm_add_sum] at h1
  have h2 := norm_fst_add_sum_le u.1
  rw [Fintype.card_fin] at h2
  calc ‖E.toLinearMap u‖ = ‖(E.toLinearMap u).1‖ := rfl
    _ ≤ _ := norm_le_norm_fst_add_sum _
    _ ≤ C.toReal * (‖u.1.1‖ + ∑ i, ‖u.1.2 i‖) := h1
    _ ≤ C.toReal * ((finrank ℝ V + 1) * ‖u‖) := by gcongr; exact h2
    _ = _ := by ring

/-- An extension operator with a finite constant as a **bounded linear operator**
(`Rd.SobolevExtensionOp.norm_apply_le`). -/
noncomputable def toContinuousLinearMap (E : SobolevExtensionOp p O U C) (hC : C ≠ ∞) :
    weakSobolevJet p O →L[ℂ] sobolevJet (V := V) p :=
  E.toLinearMap.mkContinuous ((finrank ℝ V + 1) * C.toReal) (E.norm_apply_le hC)

/-- The bounded linear operator of an extension operator with a finite constant `C` has norm at
most `(n + 1) C` (Mathlib's `LinearMap.mkContinuous_norm_le`). -/
theorem norm_toContinuousLinearMap_le (E : SobolevExtensionOp p O U C) (hC : C ≠ ∞) :
    ‖E.toContinuousLinearMap hC‖ ≤ (finrank ℝ V + 1) * C.toReal :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- **Restriction after extension is the identity** for an extension operator from `U ⊇ O`: the
restriction of `E u` to `O` has the value of `u`, hence it is `u`
(`Rd.weakSobolevJet.ext_of_fst_eq`). -/
theorem restrictL_comp_toContinuousLinearMap (E : SobolevExtensionOp p O U C) (hC : C ≠ ∞)
    (hOU : (O : Set V) ⊆ U) :
    (sobolevJet.restrictL O).comp (E.toContinuousLinearMap hC) = ContinuousLinearMap.id ℂ _ := by
  refine ContinuousLinearMap.ext fun u => weakSobolevJet.ext_of_fst_eq (Lp.ext ?_)
  change ⇑(LpToLpRestrictCLM V ℂ ℂ volume p O (E.toLinearMap u).1.1) =ᵐ[volume.restrict O]
    ⇑u.1.1
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (O : Set V) (E.toLinearMap u).1.1,
    (ae_restrict_iff' O.isOpen.measurableSet).2 ((E.ae_eq u).mono fun x hx hxO => hx (hOU hxO))]
    with x h1 h2
  exact h1.trans h2

end SobolevExtensionOp

/-! ### One patch -/

namespace LocalMeansBump

variable (b : LocalMeansBump V)

/-- **The local means of Triebel–Lizorkin type of a jet**: for a jet `u = (f, (g_i)_i)` of
`W^1_p(O)`, an open `T ⊆ O` and the support condition of
`Rd.LocalMeansBump.tlLocalNormOn_le_patchConst`, the local means quasi-norm on `W` of `1_T f` is
at most `C_b (‖f‖_{L_p(O)} + ∑_i ‖g_i‖_{L_p(O)})`, `C_b = Rd.LocalMeansBump.patchConst b p`. -/
theorem tlLocalNormOn_indicatorExtendLp_le [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {W : Set V}
    (hW : MeasurableSet W) {T O : Opens V} (hTO : T ≤ O)
    (hsupp : ∀ x ∈ W, ∀ j i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)), x - y ∈ T)
    (u : weakSobolevJet p O) :
    b.tlLocalNormOn hp hW 2 1 2 (indicatorExtendLp T.isOpen.measurableSet hTO u.1.1) ≤
      b.patchConst p * (‖u.1.1‖ₑ + ∑ i, ‖u.1.2 i‖ₑ) := by
  have hμ : volume.restrict (T : Set V) ≤ volume.restrict (O : Set V) :=
    Measure.restrict_mono (show (T : Set V) ⊆ O from hTO) le_rfl
  refine (b.tlLocalNormOn_le_patchConst hp1 hp hW ((Lp.memLp u.1.1).mono_measure hμ)
    (fun i => (Lp.memLp (u.1.2 i)).mono_measure hμ) (fun i => (u.2 i).mono hTO) hsupp
    (indicatorExtendLp_apply_ae _ _ u.1.1)).trans ?_
  gcongr with i <;> exact (eLpNorm_mono_measure _ hμ).trans_eq (Lp.eNorm_def _).symm

/-- The local means quasi-norm of Triebel–Lizorkin type of a jet is finite
(`Rd.LocalMeansBump.tlLocalNormOn_indicatorExtendLp_le`). -/
theorem tlLocalNormOn_indicatorExtendLp_lt_top [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {W : Set V} (hW : MeasurableSet W) {T O : Opens V} (hTO : T ≤ O)
    (hsupp : ∀ x ∈ W, ∀ j i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)), x - y ∈ T)
    (u : weakSobolevJet p O) :
    b.tlLocalNormOn hp hW 2 1 2 (indicatorExtendLp T.isOpen.measurableSet hTO u.1.1) < ∞ :=
  (b.tlLocalNormOn_indicatorExtendLp_le hp1 hp hW hTO hsupp u).trans_lt (ENNReal.mul_lt_top
    (b.patchConst_ne_top hp1 hp).lt_top (ENNReal.add_lt_top.2 ⟨eNorm_lt_top,
      ENNReal.sum_lt_top.2 fun _ _ => eNorm_lt_top⟩))

/-- **The local extension of a jet converges absolutely**
(`Rd.LocalMeansBump.summable_localExtTerm_of_tlLocalNormOn`). -/
theorem summable_localExtTerm_indicatorExtendLp [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {W : Set V} (hW : MeasurableSet W) {T O : Opens V} (hTO : T ≤ O)
    (hsupp : ∀ x ∈ W, ∀ j i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)), x - y ∈ T)
    (u : weakSobolevJet p O) :
    Summable fun j =>
      b.localExtTerm hp hW 2 j (indicatorExtendLp T.isOpen.measurableSet hTO u.1.1) :=
  b.summable_localExtTerm_of_tlLocalNormOn hp hW 2 one_pos two_ne_zero
    (b.tlLocalNormOn_indicatorExtendLp_lt_top hp1 hp hW hTO hsupp u)

/-- **The local extension of jets**: `u = (f, (g_i)_i) ↦ ∑_j η_j ⋆ 1_W (k_j ⋆ 1_T f)`, a linear
map from the jets of `W^1_p(O)` into `L_p(V)`; the series converges for every jet
(`Rd.LocalMeansBump.summable_localExtTerm_indicatorExtendLp`), so it is additive. -/
noncomputable def localExtensionJet [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {W : Set V}
    (hW : MeasurableSet W) {T O : Opens V} (hTO : T ≤ O)
    (hsupp : ∀ x ∈ W, ∀ j i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)), x - y ∈ T) :
    weakSobolevJet p O →ₗ[ℂ] Lp ℂ p (volume : Measure V) where
  toFun u := b.localExtension hp hW 2 (indicatorExtendLp T.isOpen.measurableSet hTO u.1.1)
  map_add' u v := by
    simp only [localExtension, Submodule.coe_add, Prod.fst_add, map_add, localExtTerm_add]
    exact (b.summable_localExtTerm_indicatorExtendLp hp1 hp hW hTO hsupp u).tsum_add
      (b.summable_localExtTerm_indicatorExtendLp hp1 hp hW hTO hsupp v)
  map_smul' c u := by
    simp only [localExtension, Submodule.coe_smul, Prod.smul_fst, map_smul, localExtTerm_smul,
      RingHom.id_apply]
    exact tsum_const_smul'' c

/-- The local extension of a jet lies in `F^1_{p,2}(V)`
(`Rd.LocalMeansBump.memTriebelLizorkin_localExtension_of_tlLocalNormOn`). -/
theorem memTriebelLizorkin_localExtensionJet [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {W : Set V} (hW : MeasurableSet W) {T O : Opens V} (hTO : T ≤ O)
    (hsupp : ∀ x ∈ W, ∀ j i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)), x - y ∈ T)
    (u : weakSobolevJet p O) :
    MemTriebelLizorkin ((1 : ℕ) : ℝ) 2 (b.localExtensionJet hp1 hp hW hTO hsupp u) :=
  b.memTriebelLizorkin_localExtension_of_tlLocalNormOn hp1 hp hW
    (b.tlLocalNormOn_indicatorExtendLp_lt_top hp1 hp hW hTO hsupp u)

/-- **The local extension of a jet agrees with its value on `U`** if `U ⊆ T` and the dual kernels
at points of `U` only see `W` (`Rd.LocalMeansBump.ae_localExtension_eq_of_ae_eq_indicator`). -/
theorem ae_localExtensionJet_eq [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {U W : Set V}
    (hU : MeasurableSet U) (hW : MeasurableSet W) {T O : Opens V} (hTO : T ≤ O) (hUT : U ⊆ T)
    (hUW : ∀ x ∈ U, ∀ j y, b.dual 2 j y ≠ 0 → x - y ∈ W)
    (hsupp : ∀ x ∈ W, ∀ j i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)), x - y ∈ T)
    (u : weakSobolevJet p O) :
    ∀ᵐ x ∂volume, x ∈ U → b.localExtensionJet hp1 hp hW hTO hsupp u x = u.1.1 x :=
  b.ae_localExtension_eq_of_ae_eq_indicator hp one_le_two hU hW hUT hUW
    (indicatorExtendLp_apply_ae T.isOpen.measurableSet hTO u.1.1)
    (b.summable_localExtTerm_indicatorExtendLp hp1 hp hW hTO hsupp u)

/-- **The bound of the local extension of jets**: for the local extension `F` of a jet
`u = (f, (g_i)_i)` and weak derivatives `G_i = ∂_{e_i} F ∈ L_p(V)`,
`‖F‖_p + ∑_i ‖G_i‖_p ≤ C (‖f‖_{L_p(O)} + ∑_i ‖g_i‖_{L_p(O)})` with
`C = Rd.LocalMeansBump.extensionConst b p`
(`Rd.LocalMeansBump.enorm_localExtension_add_le_extensionConst`). -/
theorem enorm_localExtensionJet_add_le [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {W : Set V}
    (hW : MeasurableSet W) {T O : Opens V} (hTO : T ≤ O)
    (hsupp : ∀ x ∈ W, ∀ j i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)), x - y ∈ T)
    (u : weakSobolevJet p O) {G : Fin (finrank ℝ V) → Lp ℂ p (volume : Measure V)}
    (hG : ∀ i, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V i)
      (b.localExtensionJet hp1 hp hW hTO hsupp u) (G i)) :
    ‖b.localExtensionJet hp1 hp hW hTO hsupp u‖ₑ + ∑ i, ‖G i‖ₑ ≤
      b.extensionConst p * (‖u.1.1‖ₑ + ∑ i, ‖u.1.2 i‖ₑ) :=
  b.enorm_localExtension_add_le_extensionConst hp1 hp hW
    (b.tlLocalNormOn_indicatorExtendLp_le hp1 hp hW hTO hsupp u)
    (b.tlLocalNormOn_indicatorExtendLp_lt_top hp1 hp hW hTO hsupp u) hG

/-- **The extension operator from one patch** (Rychkov's local extension with the local means of
the gradient): let `U ⊆ T ⊆ O` with `T` and `O` open, let the dual kernels at points of `U` only
see `W`, and let `x - y ∈ T` for every `x ∈ W`, every level `j` and every `y` in the support of
`(K_i)_{2^j}`. Then for `1 < p < ∞` the local extension of jets
(`Rd.LocalMeansBump.localExtensionJet`) with its weak derivatives (`Rd.sobolevJet.lift`) is an
extension operator from `U` with the constant `Rd.LocalMeansBump.extensionConst b p`. -/
noncomputable def sobolevExtensionOp [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {U W : Set V}
    (hU : MeasurableSet U) (hW : MeasurableSet W) {T O : Opens V} (hTO : T ≤ O) (hUT : U ⊆ T)
    (hUW : ∀ x ∈ U, ∀ j y, b.dual 2 j y ≠ 0 → x - y ∈ W)
    (hsupp : ∀ x ∈ W, ∀ j i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)), x - y ∈ T) :
    SobolevExtensionOp p O U (b.extensionConst p) :=
  let L := sobolevJet.lift (b.localExtensionJet hp1 hp hW hTO hsupp) fun u i =>
    (exists_hasWeakLineDeriv_of_memTriebelLizorkin hp1 hp (fun _ : Fin 1 => gridBasis V i)
      (b.memTriebelLizorkin_localExtensionJet hp1 hp hW hTO hsupp u)).imp fun _ h => h.1
  { toLinearMap := L
    memSobolev := fun u => memSobolev_of_memTriebelLizorkin hp1 hp
      (b.memTriebelLizorkin_localExtensionJet hp1 hp hW hTO hsupp u)
    ae_eq := fun u => b.ae_localExtensionJet_eq hp1 hp hU hW hTO hUT hUW hsupp u
    bound := fun u => b.enorm_localExtensionJet_add_le hp1 hp hW hTO hsupp u fun i => (L u).2 i }

omit [Fact (1 ≤ p)] in
/-- **The extension from one patch** (Rychkov's local extension with the local means of the
gradient): let `U ⊆ T` with `T` open, let the dual kernels at points of `U` only see `W`, and let
`x - y ∈ T` for every `x ∈ W`, every level `j` and every `y` in the support of `(K_i)_{2^j}`. Then
for `1 < p < ∞` the local extension `F = ∑_j η_j ⋆ 1_W (k_j ⋆ 1_T f)` of order two lies in
`F^1_{p,2}(V) = W^1_p(V)` and agrees with `f` on `U`, with the constant
`Rd.LocalMeansBump.extensionConst b p`: the extension operator from one patch
(`Rd.LocalMeansBump.sobolevExtensionOp` with `O = T`) applied to `f`
(`Rd.SobolevExtensionOp.extendsSobolev`). -/
theorem extendsSobolev [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {U W : Set V}
    (hU : MeasurableSet U) (hW : MeasurableSet W) {T : Opens V} (hUT : U ⊆ T)
    (hUW : ∀ x ∈ U, ∀ j y, b.dual 2 j y ≠ 0 → x - y ∈ W)
    (hsupp : ∀ x ∈ W, ∀ j i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)), x - y ∈ T) :
    ExtendsSobolev p T U (b.extensionConst p) :=
  have : Fact (1 ≤ p) := ⟨hp1.le⟩
  (b.sobolevExtensionOp hp1 hp hU hW (O := T) le_rfl hUT hUW hsupp).extendsSobolev hUT

end LocalMeansBump

/-! ### Pasting -/

namespace SobolevExtensionOp

variable {ι : Type*} [Fintype ι] {O : Opens V} {U : ι → Set V} {C : ι → ℝ≥0∞}
  {ψ : ι → V → ℝ} {a : ι → ℝ} {d : ι → Fin (finrank ℝ V) → ℝ}

/-- **The values of the pasted extension**: `u ↦ ∑_k ψ_k F_k` with `F_k` the value of `E_k u`, a
linear map from the jets of `W^1_p(O)` into `L_p(V)` (`Rd.mulLp`, `Rd.mulLp_add`,
`Rd.mulLp_smul`). -/
noncomputable def pasteValue (E : ∀ k, SobolevExtensionOp p O ((O : Set V) ∩ U k) (C k))
    (hc : ∀ k, Continuous fun x => ((ψ k x : ℝ) : ℂ)) (ha : ∀ k x, ‖((ψ k x : ℝ) : ℂ)‖ ≤ a k) :
    weakSobolevJet p O →ₗ[ℂ] Lp ℂ p (volume : Measure V) where
  toFun u := ∑ k, mulLp (hc k) (ha k) ((E k).toLinearMap u).1.1
  map_add' u v := by
    simp only [map_add, Submodule.coe_add, Prod.fst_add, mulLp_add, Finset.sum_add_distrib]
  map_smul' c u := by
    simp only [map_smul, Submodule.coe_smul, Prod.smul_fst, mulLp_smul, Finset.smul_sum,
      RingHom.id_apply]

/-- **The derivatives of the pasted extension** (the product rule, `Rd.hasWeakLineDeriv_mulLp`):
`∂_{e_i} ∑_k ψ_k F_k = ∑_k (ψ_k G_{k,i} + (∂_{e_i} ψ_k) F_k)` weakly on `V`, for
`E_k u = (F_k, (G_{k,i})_i)`. -/
theorem hasWeakLineDeriv_pasteValue (E : ∀ k, SobolevExtensionOp p O ((O : Set V) ∩ U k) (C k))
    (hψ : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ k))
    (hc : ∀ k, Continuous fun x => ((ψ k x : ℝ) : ℂ)) (ha : ∀ k x, ‖((ψ k x : ℝ) : ℂ)‖ ≤ a k)
    (hc' : ∀ k i, Continuous fun x => ((fderiv ℝ (ψ k) x (gridBasis V i) : ℝ) : ℂ))
    (hd : ∀ k i x, ‖((fderiv ℝ (ψ k) x (gridBasis V i) : ℝ) : ℂ)‖ ≤ d k i)
    (u : weakSobolevJet p O) (i : Fin (finrank ℝ V)) :
    HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V i) (pasteValue E hc ha u)
      (∑ k, (mulLp (hc k) (ha k) (((E k).toLinearMap u).1.2 i) +
        mulLp (hc' k i) (hd k i) ((E k).toLinearMap u).1.1) : Lp ℂ p (volume : Measure V)) := by
  refine (HasWeakLineDeriv.sum (s := Finset.univ) fun k _ => hasWeakLineDeriv_mulLp
    (((E k).toLinearMap u).2 i) (hψ k) (hc k) (ha k) (hc' k i) (hd k i)).congr_ae ?_ ?_ <;>
    rw [volume_restrict_top]
  · exact (Lp.coeFn_finsetSum _ _).symm
  · exact (Lp.coeFn_finsetSum _ _).symm

/-- The pasted extension agrees with the value of the jet on `O`: `ψ_k F_k = ψ_k f` on `O` since
`F_k = f` on `O ∩ U_k ⊇ O ∩ supp ψ_k`, and `∑_k ψ_k = 1` on `O` (`Rd.ae_sum_mul_eq`). -/
theorem ae_pasteValue_eq (E : ∀ k, SobolevExtensionOp p O ((O : Set V) ∩ U k) (C k))
    (hψU : ∀ k, tsupport (ψ k) ⊆ U k) (hψ1 : ∀ x ∈ (O : Set V), ∑ k, ψ k x = 1)
    (hc : ∀ k, Continuous fun x => ((ψ k x : ℝ) : ℂ)) (ha : ∀ k x, ‖((ψ k x : ℝ) : ℂ)‖ ≤ a k)
    (u : weakSobolevJet p O) :
    ∀ᵐ x ∂volume, x ∈ (O : Set V) → pasteValue E hc ha u x = u.1.1 x := by
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ fun k =>
      mulLp (hc k) (ha k) ((E k).toLinearMap u).1.1,
    ae_all_iff.2 fun k => mulLp_apply_ae (hc k) (ha k) ((E k).toLinearMap u).1.1,
    ae_sum_mul_eq hψU hψ1 fun k => (E k).ae_eq u] with x h1 h2 h3 hxO
  change (⇑(∑ k, mulLp (hc k) (ha k) ((E k).toLinearMap u).1.1)) x = u.1.1 x
  rw [h1, ← h3 hxO]
  exact Finset.sum_congr rfl fun k _ => h2 k

/-- **The pasted extension operator**: for extension operators `E_k` from `O ∩ U_k` and a smooth,
compactly supported resolution of unity `(ψ_k)` on `O` subordinate to `(U_k)` with `|ψ_k| ≤ a_k`,
`|∂_{e_i} ψ_k| ≤ d_{k,i}`, the map `u ↦ ∑_k ψ_k E_k u` with the derivatives of the product rule is
an extension operator from `O` with the constant `∑_k (a_k + ∑_i d_{k,i}) C_k`
(`Rd.pasting_bound`). -/
noncomputable def paste (E : ∀ k, SobolevExtensionOp p O ((O : Set V) ∩ U k) (C k))
    (hψ : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ k)) (hcs : ∀ k, HasCompactSupport (ψ k))
    (hψU : ∀ k, tsupport (ψ k) ⊆ U k) (hψ1 : ∀ x ∈ (O : Set V), ∑ k, ψ k x = 1)
    (hc : ∀ k, Continuous fun x => ((ψ k x : ℝ) : ℂ)) (ha : ∀ k x, ‖((ψ k x : ℝ) : ℂ)‖ ≤ a k)
    (hc' : ∀ k i, Continuous fun x => ((fderiv ℝ (ψ k) x (gridBasis V i) : ℝ) : ℂ))
    (hd : ∀ k i x, ‖((fderiv ℝ (ψ k) x (gridBasis V i) : ℝ) : ℂ)‖ ≤ d k i) :
    SobolevExtensionOp p O O (∑ k, (ENNReal.ofReal (a k) + ∑ i, ENNReal.ofReal (d k i)) * C k)
    where
  toLinearMap := sobolevJet.lift (pasteValue E hc ha) fun u i =>
    ⟨_, hasWeakLineDeriv_pasteValue E hψ hc ha hc' hd u i⟩
  memSobolev u := MemSobolev.sum _ fun k _ =>
    ((E k).memSobolev u).mulLp (hψ k) (hcs k) (hc k) (ha k)
  ae_eq u := ae_pasteValue_eq E hψU hψ1 hc ha u
  bound u := by
    simp only [sobolevJet.lift_apply_fst,
      sobolevJet.lift_apply_snd _ _ u _ (hasWeakLineDeriv_pasteValue E hψ hc ha hc' hd u _)]
    exact pasting_bound (x := fun k => ‖((E k).toLinearMap u).1.1‖ₑ)
      (y := fun k i => ‖((E k).toLinearMap u).1.2 i‖ₑ)
      ((eNorm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => enorm_mulLp_le _ _ _))
      (fun i => (eNorm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => (eNorm_add_le _ _).trans
        (add_le_add (enorm_mulLp_le _ _ _) (enorm_mulLp_le _ _ _)))) fun k => (E k).bound u

end SobolevExtensionOp

/-- **Pasting extension operators**: let `(U_k)` be a finite cover of `Ō` by bounded open sets and
let `E_k` be extension operators from `O ∩ U_k` with finite constants. Then there is an extension
operator from `O` with a finite constant (`Rd.SobolevExtensionOp.paste` with a smooth resolution of
unity, `Rd.exists_smooth_partition`). -/
theorem sobolevExtensionOp_of_cover {ι : Type*} [Finite ι] {O : Opens V} (U : ι → Set V)
    (hUo : ∀ k, IsOpen (U k)) (hUb : ∀ k, Bornology.IsBounded (U k))
    (hcov : closure (O : Set V) ⊆ ⋃ k, U k) {C : ι → ℝ≥0∞} (hC : ∀ k, C k ≠ ∞)
    (E : ∀ k, SobolevExtensionOp p O ((O : Set V) ∩ U k) (C k)) :
    ∃ C' : ℝ≥0∞, C' ≠ ∞ ∧ Nonempty (SobolevExtensionOp p O O C') := by
  let := Fintype.ofFinite ι
  obtain ⟨ψ, hψ, hψU, hψ1, -⟩ := exists_smooth_partition isClosed_closure U hUo hcov
  have hcs : ∀ k, HasCompactSupport (ψ k) := fun k =>
    isCompact_of_isClosed_isBounded (isClosed_tsupport _) ((hUb k).subset (hψU k))
  have hc : ∀ k, Continuous fun x => ((ψ k x : ℝ) : ℂ) := fun k =>
    Complex.continuous_ofReal.comp (hψ k).continuous
  have hc' : ∀ k i, Continuous fun x => ((fderiv ℝ (ψ k) x (gridBasis V i) : ℝ) : ℂ) :=
    fun k i => Complex.continuous_ofReal.comp
      (((hψ k).continuous_fderiv (by simp)).clm_apply continuous_const)
  choose a ha using fun k =>
    (hc k).bounded_above_of_compact_support ((hcs k).comp_left Complex.ofReal_zero)
  choose d hd using fun k i => (hc' k i).bounded_above_of_compact_support
    (((hcs k).fderiv_apply (𝕜 := ℝ) (gridBasis V i)).comp_left Complex.ofReal_zero)
  exact ⟨_, ENNReal.sum_ne_top.2 fun k _ => ENNReal.mul_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.ofReal_ne_top, ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top⟩) (hC k),
    ⟨SobolevExtensionOp.paste E hψ hcs hψU (fun x hx => hψ1 x (subset_closure hx)) hc ha hc'
      hd⟩⟩

/-! ### Bounded Lipschitz domains -/

namespace BoundedLipschitzDomain

variable (Ω : BoundedLipschitzDomain V)

/-- **The boundary patches**: there are extension operators from `Ω ∩ B(c_j, ρ_j - 2ε)` with finite
constants (`Rd.LocalMeansBump.sobolevExtensionOp` on `T = Ω_j ∩ B(c_j, ρ_j) ⊆ Ω` with the cone
bump of `Ω_j` rescaled to radius `≤ ε / 2`, `Rd.LipschitzGraph.exists_coneBump_radius_le`). -/
theorem exists_sobolevExtensionOp_boundary [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {ε : ℝ}
    (hε : 0 < ε) (j : Fin Ω.N) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ Nonempty (SobolevExtensionOp p Ω.toOpens
      (Ω.carrier ∩ ball (Ω.center j) (Ω.radius j - 2 * ε)) C) := by
  set G := Ω.graph j
  set c := Ω.center j
  set ρ := Ω.radius j
  obtain ⟨b, hb, -, hR⟩ := G.exists_coneBump_radius_le zero_le_two hε
  have hLR : ((2 : ℕ) : ℝ) * b.radius ≤ ε := by exact_mod_cast hR
  have hTo : IsOpen (G.domain ∩ ball c ρ) := G.isOpen_domain.inter isOpen_ball
  have hTΩ : (⟨_, hTo⟩ : Opens V) ≤ Ω.toOpens := by
    change G.domain ∩ ball c ρ ⊆ Ω.carrier
    rw [← Ω.inter_ball_eq j le_rfl]
    exact Set.inter_subset_left
  have hU : Ω.carrier ∩ ball c (ρ - 2 * ε) = G.domain ∩ ball c (ρ - 2 * ε) :=
    Ω.inter_ball_eq j (by linarith)
  refine ⟨b.extensionConst p, b.extensionConst_ne_top hp1 hp, ?_⟩
  rw [hU]
  exact ⟨b.sobolevExtensionOp hp1 hp ((G.isOpen_domain.inter isOpen_ball).measurableSet)
    ((G.isOpen_domain.inter isOpen_ball).measurableSet) (T := ⟨_, hTo⟩) hTΩ
    (Set.inter_subset_inter_right _ (ball_subset_ball (by linarith)))
    (G.patch_support hb hLR) (G.patch_support_divKernel hb hR)⟩

omit [Fact (1 ≤ p)] in
/-- **The boundary patches**: Sobolev functions on `Ω` extend from `Ω ∩ B(c_j, ρ_j - 2ε)` with a
finite constant, by the extension operator of the patch
(`Rd.BoundedLipschitzDomain.exists_sobolevExtensionOp_boundary`,
`Rd.SobolevExtensionOp.extendsSobolev`). -/
theorem exists_extendsSobolev_boundary [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {ε : ℝ}
    (hε : 0 < ε) (j : Fin Ω.N) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ExtendsSobolev p Ω.toOpens
      (Ω.carrier ∩ ball (Ω.center j) (Ω.radius j - 2 * ε)) C := by
  have : Fact (1 ≤ p) := ⟨hp1.le⟩
  obtain ⟨C, hC, ⟨E⟩⟩ := Ω.exists_sobolevExtensionOp_boundary hp1 hp hε j
  exact ⟨C, hC, E.extendsSobolev fun _ hx => hx.1⟩

/-- **The inner patch**: there is an extension operator from `{infDist(·, Ωᶜ) > 2δ}` with a finite
constant (`Rd.LocalMeansBump.sobolevExtensionOp` on `T = Ω` with a centred bump of radius
`≤ δ / 2`, `Rd.sub_mem_of_lt_infDist_of_norm_le`). -/
theorem exists_sobolevExtensionOp_interior [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ Nonempty (SobolevExtensionOp p Ω.toOpens
      (Ω.carrier ∩ {x : V | 2 * δ < infDist x Ω.carrierᶜ}) C) := by
  have hR0 : 0 < δ / 2 := by positivity
  set b := LocalMeansBump.centered (V := V) hR0
  have hR : 2 * b.radius = δ := by rw [LocalMeansBump.centered_radius]; ring
  have hUΩ := setOf_lt_infDist_compl_subset Ω.carrier (by positivity : (0 : ℝ) ≤ 2 * δ)
  refine ⟨b.extensionConst p, b.extensionConst_ne_top hp1 hp, ?_⟩
  rw [Set.inter_eq_right.2 hUΩ]
  refine ⟨b.sobolevExtensionOp hp1 hp (measurableSet_infDist_gt Ω.carrier (2 * δ))
    (measurableSet_infDist_gt Ω.carrier δ) (T := Ω.toOpens) le_rfl hUΩ
    (fun x hx j y hy => interior_patch_support Ω.carrier (fun y hy =>
      (not_lt.1 fun h => hy (b.dual_eq_zero 2 j h)).trans (by rw [← hR]; push_cast; rfl)) x hx y hy)
    fun x hx j i y hy => sub_mem_of_lt_infDist_of_norm_le Ω.carrier hx (by
      rw [← hR]
      exact mem_closedBall_zero_iff.1 (b.tsupport_dilate_divKernel_subset_closedBall i j hy))⟩

omit [Fact (1 ≤ p)] in
/-- **The inner patch**: Sobolev functions on `Ω` extend from `{infDist(·, Ωᶜ) > 2δ}` with a finite
constant, by the extension operator of the patch
(`Rd.BoundedLipschitzDomain.exists_sobolevExtensionOp_interior`,
`Rd.SobolevExtensionOp.extendsSobolev`). -/
theorem exists_extendsSobolev_interior [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ExtendsSobolev p Ω.toOpens
      (Ω.carrier ∩ {x : V | 2 * δ < infDist x Ω.carrierᶜ}) C := by
  have : Fact (1 ≤ p) := ⟨hp1.le⟩
  obtain ⟨C, hC, ⟨E⟩⟩ := Ω.exists_sobolevExtensionOp_interior hp1 hp hδ
  exact ⟨C, hC, E.extendsSobolev fun _ hx => hx.1⟩

/-- **Pasting the patch operators**: for a bounded Lipschitz domain `Ω` in dimension `n ≥ 1` and
`1 ≤ p ≤ ∞`, if for every `ε > 0` and every `j` there is an extension operator from the boundary
patch `Ω ∩ B(c_j, ρ_j - 2ε)` with a finite constant, and for every `δ > 0` one from the inner patch
`{x ∈ Ω : infDist(x, Ωᶜ) > 2δ}`, then there is an extension operator from `Ω` with a finite
constant (the patches of `Rd.BoundedLipschitzDomain.patch`, pasted by
`Rd.sobolevExtensionOp_of_cover`, `Rd.BoundedLipschitzDomain.exists_of_patches`). -/
theorem exists_sobolevExtensionOp_of_patches [Nontrivial V]
    (hbd : ∀ ε : ℝ, 0 < ε → ∀ j : Fin Ω.N, ∃ C : ℝ≥0∞, C ≠ ∞ ∧ Nonempty (SobolevExtensionOp p
      Ω.toOpens (Ω.carrier ∩ ball (Ω.center j) (Ω.radius j - 2 * ε)) C))
    (hin : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ Nonempty (SobolevExtensionOp p Ω.toOpens
      (Ω.carrier ∩ {x : V | 2 * δ < infDist x Ω.carrierᶜ}) C)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ Nonempty (SobolevExtensionOp p Ω.toOpens Ω.carrier C) :=
  Ω.exists_of_patches (fun U C => Nonempty (SobolevExtensionOp p Ω.toOpens U C))
    (fun U hUo hUb hcov _ hC hext => sobolevExtensionOp_of_cover (O := Ω.toOpens) U hUo hUb hcov
      hC fun i => Nonempty.some (hext i)) hbd hin

/-- **Rychkov's extension operator with a finite constant**: for a bounded Lipschitz domain
`Ω` in dimension `n ≥ 1` and `1 < p < ∞` there is an extension operator from `Ω` with a finite
constant (`Rd.BoundedLipschitzDomain.exists_sobolevExtensionOp_of_patches` with the patch operators
`Rd.BoundedLipschitzDomain.exists_sobolevExtensionOp_boundary` and
`Rd.BoundedLipschitzDomain.exists_sobolevExtensionOp_interior`). -/
theorem exists_sobolevExtensionOp [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ Nonempty (SobolevExtensionOp p Ω.toOpens Ω.carrier C) :=
  Ω.exists_sobolevExtensionOp_of_patches
    (fun _ hε j => Ω.exists_sobolevExtensionOp_boundary hp1 hp hε j)
    (fun _ hδ => Ω.exists_sobolevExtensionOp_interior hp1 hp hδ)

omit [Fact (1 ≤ p)] in
/-- **The extension theorem with a bound**: for a bounded Lipschitz domain `Ω` in dimension
`n ≥ 1` and `1 < p < ∞` there is a finite constant `C` such that every `f ∈ L_p(Ω)` with weak
derivatives `g_i = ∂_{e_i} f ∈ L_p(Ω)` agrees on `Ω` with some `F ∈ W^1_p(V)` whose weak
derivatives `G_i = ∂_{e_i} F` satisfy
`‖F‖_p + ∑_i ‖G_i‖_p ≤ C (‖f‖_{L_p(Ω)} + ∑_i ‖g_i‖_{L_p(Ω)})`: the extension operator of
`Rd.BoundedLipschitzDomain.exists_sobolevExtensionOp` applied to `f`
(`Rd.SobolevExtensionOp.extendsSobolev`). -/
theorem exists_extendsSobolev [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ExtendsSobolev p Ω.toOpens Ω.carrier C := by
  have : Fact (1 ≤ p) := ⟨hp1.le⟩
  obtain ⟨C, hC, ⟨E⟩⟩ := Ω.exists_sobolevExtensionOp hp1 hp
  exact ⟨C, hC, E.extendsSobolev subset_rfl⟩

end BoundedLipschitzDomain

end Rd
