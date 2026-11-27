/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Sobolev.WeakDerivatives
public import LeanPool.FunctionSpaces.Analysis.Maximal.DyadicGrid

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Value–derivative jets of `W^1_p`

Let `V` be a finite-dimensional real inner product space of dimension `n`, `e_i = Rd.gridBasis V i`
its orthonormal basis, `O ⊆ V` open and `1 ≤ p ≤ ∞`. A **jet** of `W^1_p(O)` is a pair
`(f, (g_i)_i)` of elements of `L_p(O)` with `g_i = ∂_{e_i} f` weakly on `O`
(`Rd.weakSobolevJet p O`); the jets of `W^1_p(V)` are the same over `L_p(V)` (`Rd.sobolevJet p`).
Both are complex linear subspaces of `L_p × L_p^n` with the norm `max(‖f‖_p, max_i ‖g_i‖_p)`, which
is equivalent to `‖f‖_p + ∑_i ‖g_i‖_p` (`Rd.norm_le_norm_fst_add_sum`,
`Rd.norm_fst_add_sum_le`; in `ℝ≥0∞`, `Rd.toReal_enorm_add_sum`, and the squared form
`Rd.sq_norm_add_sum_sq_le`).

* The derivatives of a jet are determined by its value (`Rd.weakSobolevJet.snd_eq_of_fst_eq`,
  `Rd.sobolevJet.snd_eq_of_fst_eq`), and every `f ∈ W^1_p(O)` is the value of a jet
  (`Rd.exists_mem_weakSobolevJet_of_memWeakSobolev`).
* The restriction `Rd.sobolevJet.restrictL O` from the jets of `W^1_p(V)` to those of `W^1_p(O)`
  is a bounded linear operator.
* A linear map into `L_p(V)` whose values have weak derivatives along the `e_i` in `L_p(V)` is a
  linear map into the jets (`Rd.sobolevJet.lift`).
-/

@[expose] public section

open MeasureTheory Module TopologicalSpace
open scoped ENNReal

namespace Rd

/-! ### Norms on products -/

/-- The sup norm of `(x, (y_i)_i) ∈ E × F^ι` is at most `‖x‖ + ∑_i ‖y_i‖`. -/
theorem norm_le_norm_fst_add_sum {E F ι : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] [Fintype ι] (u : E × (ι → F)) :
    ‖u‖ ≤ ‖u.1‖ + ∑ i, ‖u.2 i‖ := by
  have hs : 0 ≤ ∑ i, ‖u.2 i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  refine max_le (le_add_of_nonneg_right hs) ((pi_norm_le_iff_of_nonneg (by positivity)).2
    fun i => ?_)
  exact (Finset.single_le_sum (f := fun i => ‖u.2 i‖) (fun i _ => norm_nonneg _)
    (Finset.mem_univ i)).trans (le_add_of_nonneg_left (norm_nonneg _))

/-- `‖x‖ + ∑_i ‖y_i‖` is at most `(#ι + 1)` times the sup norm of `(x, (y_i)_i) ∈ E × F^ι`
(Mathlib's `Pi.sum_norm_apply_le_norm`, `∑_i ‖y_i‖ ≤ #ι ‖y‖`). -/
theorem norm_fst_add_sum_le {E F ι : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] [Fintype ι] (u : E × (ι → F)) :
    ‖u.1‖ + ∑ i, ‖u.2 i‖ ≤ (Fintype.card ι + 1) * ‖u‖ := by
  have h2 : ∑ i, ‖u.2 i‖ ≤ Fintype.card ι * ‖u‖ := by
    rw [← nsmul_eq_mul]
    exact (Pi.sum_norm_apply_le_norm u.2).trans (nsmul_le_nsmul_right (norm_snd_le u) _)
  linarith [norm_fst_le u]

/-- `(‖x‖ₑ + ∑_i ‖y_i‖ₑ).toReal = ‖x‖ + ∑_i ‖y_i‖` in a normed group: the norm
`‖x‖ + ∑_i ‖y_i‖` in `ℝ≥0∞` and in `ℝ`. -/
theorem toReal_enorm_add_sum {E ι : Type*} [NormedAddCommGroup E] [Fintype ι] (x : E)
    (y : ι → E) : (‖x‖ₑ + ∑ i, ‖y i‖ₑ).toReal = ‖x‖ + ∑ i, ‖y i‖ := by
  rw [ENNReal.toReal_add eNorm_ne_top (ENNReal.sum_ne_top.2 fun _ _ => eNorm_ne_top),
    ENNReal.toReal_sum fun _ _ => eNorm_ne_top]
  simp only [toReal_eNorm]

/-- If `‖x‖ + ∑_i ‖y_i‖ ≤ K` in `ℝ≥0∞` with `K` finite, then `‖x‖² + ∑_i ‖y_i‖² ≤ K²` in `ℝ`. -/
theorem sq_norm_add_sum_sq_le {E : Type*} [NormedAddCommGroup E] {ι : Type*} [Fintype ι] {x : E}
    {y : ι → E} {K : ℝ≥0∞} (hK : K ≠ ∞) (h : ‖x‖ₑ + ∑ i, ‖y i‖ₑ ≤ K) :
    ‖x‖ ^ 2 + ∑ i, ‖y i‖ ^ 2 ≤ K.toReal ^ 2 := by
  have hr : ‖x‖ + ∑ i, ‖y i‖ ≤ K.toReal :=
    toReal_enorm_add_sum x y ▸ ENNReal.toReal_mono hK h
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) fun i _ => norm_nonneg (y i)
  have h0 : 0 ≤ ∑ i, ‖y i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  nlinarith [norm_nonneg x]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞}

/-! ### Jets on an open set -/

variable (p) in
/-- The **jets of `W^1_p(O)`**: the pairs `(f, (g_i)_i)` of elements of `L_p(O)` with
`g_i = ∂_{e_i} f` weakly on `O`, `e_i = Rd.gridBasis V i`; a complex linear subspace of
`L_p(O) × L_p(O)^n`. -/
noncomputable def weakSobolevJet (O : Opens V) :
    Submodule ℂ (Lp ℂ p (volume.restrict (O : Set V)) ×
      (Fin (finrank ℝ V) → Lp ℂ p (volume.restrict (O : Set V)))) where
  carrier := {u | ∀ i, HasWeakLineDeriv O (fun _ : Fin 1 => gridBasis V i) u.1 (u.2 i)}
  zero_mem' := fun _ =>
    hasWeakLineDeriv_zero.congr_ae (Lp.coeFn_zero ..).symm (Lp.coeFn_zero ..).symm
  add_mem' := fun hu hv i =>
    ((hu i).add (hv i)).congr_ae (Lp.coeFn_add ..).symm (Lp.coeFn_add ..).symm
  smul_mem' := fun c _ hu i =>
    ((hu i).smul c).congr_ae (Lp.coeFn_smul ..).symm (Lp.coeFn_smul ..).symm

/-- Membership in the jets of `W^1_p(O)`: `g_i = ∂_{e_i} f` weakly on `O` for every `i`. -/
theorem mem_weakSobolevJet {O : Opens V}
    {u : Lp ℂ p (volume.restrict (O : Set V)) ×
      (Fin (finrank ℝ V) → Lp ℂ p (volume.restrict (O : Set V)))} :
    u ∈ weakSobolevJet p O ↔
      ∀ i, HasWeakLineDeriv O (fun _ : Fin 1 => gridBasis V i) u.1 (u.2 i) :=
  Iff.rfl

/-- **The derivatives of a jet of `W^1_p(O)` are determined by its value**: two jets with the same
value have the same derivatives (`Rd.HasWeakLineDeriv.unique`). -/
theorem weakSobolevJet.snd_eq_of_fst_eq {O : Opens V}
    {u v : Lp ℂ p (volume.restrict (O : Set V)) ×
      (Fin (finrank ℝ V) → Lp ℂ p (volume.restrict (O : Set V)))}
    (hu : u ∈ weakSobolevJet p O) (hv : v ∈ weakSobolevJet p O) (h : u.1 = v.1) : u.2 = v.2 := by
  funext i
  have hv' := hv i
  rw [← h] at hv'
  exact Lp.ext ((hu i).unique hv')

/-- Two jets of `W^1_p(O)` with the same value are equal
(`Rd.weakSobolevJet.snd_eq_of_fst_eq`). -/
theorem weakSobolevJet.ext_of_fst_eq {O : Opens V} {u v : weakSobolevJet p O}
    (h : u.1.1 = v.1.1) : u = v :=
  Subtype.ext (Prod.ext h (weakSobolevJet.snd_eq_of_fst_eq u.2 v.2 h))

/-- **Every `f ∈ W^1_p(O)` is the value of a jet**: some jet of `W^1_p(O)` has a value equal to `f`
almost everywhere on `O`. -/
theorem exists_mem_weakSobolevJet_of_memWeakSobolev {O : Opens V} {f : V → ℂ}
    (hf : MemWeakSobolev O 1 p f) :
    ∃ u ∈ weakSobolevJet p O, (u.1 : V → ℂ) =ᵐ[volume.restrict (O : Set V)] f := by
  choose g hg hfg using fun i => hf.2 1 le_rfl fun _ : Fin 1 => gridBasis V i
  refine ⟨(hf.1.toLp f, fun i => (hg i).toLp (g i)), fun i => ?_, hf.1.coeFn_toLp⟩
  exact (hfg i).congr_ae hf.1.coeFn_toLp.symm (hg i).coeFn_toLp.symm

/-! ### Jets on the whole space -/

variable (p) in
/-- The **jets of `W^1_p(V)`**: the pairs `(F, (G_i)_i)` of elements of `L_p(V)` with
`G_i = ∂_{e_i} F` weakly on `V`, `e_i = Rd.gridBasis V i`; a complex linear subspace of
`L_p(V) × L_p(V)^n`. -/
noncomputable def sobolevJet :
    Submodule ℂ (Lp ℂ p (volume : Measure V) × (Fin (finrank ℝ V) → Lp ℂ p (volume : Measure V)))
    where
  carrier := {u | ∀ i, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V i) u.1 (u.2 i)}
  zero_mem' := fun _ => hasWeakLineDeriv_zero.congr_ae
    (ae_restrict_of_ae (Lp.coeFn_zero ..).symm) (ae_restrict_of_ae (Lp.coeFn_zero ..).symm)
  add_mem' := fun hu hv i => ((hu i).add (hv i)).congr_ae
    (ae_restrict_of_ae (Lp.coeFn_add ..).symm) (ae_restrict_of_ae (Lp.coeFn_add ..).symm)
  smul_mem' := fun c _ hu i => ((hu i).smul c).congr_ae
    (ae_restrict_of_ae (Lp.coeFn_smul ..).symm) (ae_restrict_of_ae (Lp.coeFn_smul ..).symm)

/-- Membership in the jets of `W^1_p(V)`: `G_i = ∂_{e_i} F` weakly on `V` for every `i`. -/
theorem mem_sobolevJet
    {u : Lp ℂ p (volume : Measure V) × (Fin (finrank ℝ V) → Lp ℂ p (volume : Measure V))} :
    u ∈ sobolevJet p ↔ ∀ i, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V i) u.1 (u.2 i) :=
  Iff.rfl

/-- **The derivatives of a jet of `W^1_p(V)` are determined by its value**
(`Rd.HasWeakLineDeriv.eq_of_top`). -/
theorem sobolevJet.snd_eq_of_fst_eq
    {u v : Lp ℂ p (volume : Measure V) × (Fin (finrank ℝ V) → Lp ℂ p (volume : Measure V))}
    (hu : u ∈ sobolevJet p) (hv : v ∈ sobolevJet p) (h : u.1 = v.1) : u.2 = v.2 := by
  funext i
  have hv' := hv i
  rw [← h] at hv'
  exact (hu i).eq_of_top hv'

/-- Two jets of `W^1_p(V)` with the same value are equal (`Rd.sobolevJet.snd_eq_of_fst_eq`). -/
theorem sobolevJet.ext_of_fst_eq {u v : sobolevJet (V := V) p}
    (h : u.1.1 = v.1.1) : u = v :=
  Subtype.ext (Prod.ext h (sobolevJet.snd_eq_of_fst_eq u.2 v.2 h))

/-! ### Linear maps into the jets -/

/-- **Linear maps into the jets of `W^1_p(V)`**: a linear map `L` into `L_p(V)` whose values have
weak derivatives `∂_{e_i} (L u) ∈ L_p(V)` is the linear map `u ↦ (L u, (∂_{e_i} (L u))_i)` into
the jets; it is additive and homogeneous since the derivatives are determined by the value
(`Rd.sobolevJet.ext_of_fst_eq`). -/
noncomputable def sobolevJet.lift {M : Type*} [AddCommGroup M] [Module ℂ M]
    (L : M →ₗ[ℂ] Lp ℂ p (volume : Measure V))
    (h : ∀ u i, ∃ G : Lp ℂ p (volume : Measure V),
      HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V i) (L u) G) :
    M →ₗ[ℂ] sobolevJet (V := V) p where
  toFun u := ⟨(L u, fun i => (h u i).choose), fun i => (h u i).choose_spec⟩
  map_add' u v := sobolevJet.ext_of_fst_eq (map_add L u v)
  map_smul' c u := sobolevJet.ext_of_fst_eq (map_smul L c u)

/-- The value of `Rd.sobolevJet.lift L h u` is `L u`. -/
theorem sobolevJet.lift_apply_fst {M : Type*} [AddCommGroup M] [Module ℂ M]
    (L : M →ₗ[ℂ] Lp ℂ p (volume : Measure V))
    (h : ∀ u i, ∃ G : Lp ℂ p (volume : Measure V),
      HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V i) (L u) G) (u : M) :
    (sobolevJet.lift L h u).1.1 = L u :=
  rfl

/-- The derivatives of `Rd.sobolevJet.lift L h u` are the weak derivatives of `L u`: every weak
derivative `G = ∂_{e_i} (L u)` in `L_p(V)` is the `i`-th one (`Rd.HasWeakLineDeriv.eq_of_top`). -/
theorem sobolevJet.lift_apply_snd {M : Type*} [AddCommGroup M] [Module ℂ M]
    (L : M →ₗ[ℂ] Lp ℂ p (volume : Measure V))
    (h : ∀ u i, ∃ G : Lp ℂ p (volume : Measure V),
      HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V i) (L u) G) (u : M) (i : Fin (finrank ℝ V))
    {G : Lp ℂ p (volume : Measure V)}
    (hG : HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V i) (L u) G) :
    (sobolevJet.lift L h u).1.2 i = G :=
  (h u i).choose_spec.eq_of_top hG

/-! ### The restriction -/

variable [Fact (1 ≤ p)]

/-- **The restriction of jets** `(F, (G_i)_i) ↦ (F|_O, (G_i|_O)_i)` from `W^1_p(V)` to `W^1_p(O)`,
a bounded linear operator (Mathlib's `MeasureTheory.LpToLpRestrictCLM` in each component; weak
derivatives restrict by `Rd.HasWeakLineDeriv.mono`). -/
noncomputable def sobolevJet.restrictL (O : Opens V) :
    sobolevJet (V := V) p →L[ℂ] weakSobolevJet p O :=
  (((LpToLpRestrictCLM V ℂ ℂ volume p O).prodMap (ContinuousLinearMap.pi fun i =>
      (LpToLpRestrictCLM V ℂ ℂ volume p O).comp (ContinuousLinearMap.proj i))).comp
    (sobolevJet p).subtypeL).codRestrict (weakSobolevJet p O) fun u i =>
  ((u.2 i).mono le_top).congr_ae (LpToLpRestrictCLM_coeFn ℂ _ _).symm
    (LpToLpRestrictCLM_coeFn ℂ _ _).symm

/-- The value of the restricted jet is the restriction of the value. -/
theorem sobolevJet.restrictL_apply_fst (O : Opens V) (u : sobolevJet (V := V) p) :
    (sobolevJet.restrictL O u).1.1 = LpToLpRestrictCLM V ℂ ℂ volume p O u.1.1 :=
  rfl

/-- The derivatives of the restricted jet are the restrictions of the derivatives. -/
theorem sobolevJet.restrictL_apply_snd (O : Opens V) (u : sobolevJet (V := V) p)
    (i : Fin (finrank ℝ V)) :
    (sobolevJet.restrictL O u).1.2 i =
      LpToLpRestrictCLM V ℂ ℂ volume p O (u.1.2 i) :=
  rfl

end Rd
