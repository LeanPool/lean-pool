/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingLerayApply
public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevCalculus
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Sobolev spaces of slot vectors

`prop:lps-smoothing`: the space `H^M(ℝ³)` realized as the closed subspace of the vectors of
`L²(ℝ³)` classes indexed by the ordered derivative words of length at most `M` whose entries
satisfy the weak derivative relations. With the inclusions and the partial derivatives between
them, these spaces form the tower of Banach spaces in which the projected Navier–Stokes evolution
is smooth in time.
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Vectors of `L²(ℝ³)` classes indexed by the ordered derivative words of length at most `M`
(`prop:lps-smoothing`). -/
abbrev LpsSlots (M : ℕ) : Type :=
  {α : List (Fin 3) // α ∈ sobolevWords M} → Lp ℝ 2 (volume : Measure Vec3)

/-- The `L²` pairing with a fixed square-integrable function (`prop:lps-smoothing`). -/
@[expose] def lpsPairCLM (ψ : Vec3 → ℝ) (hψ : MemLp ψ 2 volume) :
    Lp ℝ 2 (volume : Measure Vec3) →L[ℝ] ℝ :=
  innerSL ℝ (hψ.toLp ψ)

/-- The `L²` pairing with a square-integrable function is the integral of the product
(`prop:lps-smoothing`). -/
theorem lpsPairCLM_apply {ψ : Vec3 → ℝ} (hψ : MemLp ψ 2 volume)
    (f : Lp ℝ 2 (volume : Measure Vec3)) : lpsPairCLM ψ hψ f = ∫ x, f x * ψ x := by
  simp only [lpsPairCLM, innerSL_apply_apply]
  rw [real_inner_comm]
  exact lpsLeray_inner_toLp f hψ

/-- Removing the last letter keeps a word within the order bound (`prop:lps-smoothing`). -/
theorem lps_mem_sobolevWords_of_append {M : ℕ} {α : List (Fin 3)} {j : Fin 3}
    (h : α ++ [j] ∈ sobolevWords M) : α ∈ sobolevWords M := by
  rw [mem_sobolevWords] at h ⊢
  simp only [List.length_append, List.length_singleton] at h
  omega

/-- Words of length at most `M` have length at most `M + 1` (`prop:lps-smoothing`). -/
theorem lps_mem_sobolevWords_succ {M : ℕ} {α : List (Fin 3)} (h : α ∈ sobolevWords M) :
    α ∈ sobolevWords (M + 1) := by
  rw [mem_sobolevWords] at h ⊢
  omega

/-- Adding a first letter raises the order bound by one (`prop:lps-smoothing`). -/
theorem lps_cons_mem_sobolevWords {M : ℕ} {α : List (Fin 3)} (k : Fin 3)
    (h : α ∈ sobolevWords M) : k :: α ∈ sobolevWords (M + 1) := by
  rw [mem_sobolevWords] at h ⊢
  simp only [List.length_cons]
  omega

/-- The weak derivative relation between two slots, tested against one function, as a
continuous linear functional (`prop:lps-smoothing`). -/
@[expose] def lpsRelCLM (M : ℕ) (α : List (Fin 3)) (j : Fin 3) (h : α ++ [j] ∈ sobolevWords M)
    (φ : LpsTestFunction) : LpsSlots M →L[ℝ] ℝ :=
  (lpsPairCLM (spatialDeriv φ.1 j) (lpsLeray_memLp_spatialDeriv_test φ.2.1 φ.2.2 j)).comp
      (ContinuousLinearMap.proj ⟨α, lps_mem_sobolevWords_of_append h⟩) +
    (lpsPairCLM φ.1 (lpsLeray_memLp_test φ.2.1 φ.2.2)).comp
      (ContinuousLinearMap.proj ⟨α ++ [j], h⟩)

/-- The weak derivative relation functional evaluated on a slot vector (`prop:lps-smoothing`). -/
theorem lpsRelCLM_apply (M : ℕ) (α : List (Fin 3)) (j : Fin 3) (h : α ++ [j] ∈ sobolevWords M)
    (φ : LpsTestFunction) (v : LpsSlots M) :
    lpsRelCLM M α j h φ v =
      (∫ x, v ⟨α, lps_mem_sobolevWords_of_append h⟩ x * spatialDeriv φ.1 j x) +
      ∫ x, v ⟨α ++ [j], h⟩ x * φ.1 x := by
  simp only [lpsRelCLM, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, lpsPairCLM_apply]

/-- The Sobolev space `H^M(ℝ³)` as a space of slot vectors: the slot `α ++ [j]` is the weak
`j`-th derivative of the slot `α` (`prop:lps-smoothing`). -/
@[expose] def lpsSobolevSpace (M : ℕ) : Submodule ℝ (LpsSlots M) :=
  ⨅ (α : List (Fin 3)) (j : Fin 3) (h : α ++ [j] ∈ sobolevWords M) (φ : LpsTestFunction),
    LinearMap.ker (lpsRelCLM M α j h φ : LpsSlots M →ₗ[ℝ] ℝ)

/-- Membership in `H^M(ℝ³)` is the family of weak derivative relations between consecutive
slots (`prop:lps-smoothing`). -/
theorem mem_lpsSobolevSpace {M : ℕ} {v : LpsSlots M} :
    v ∈ lpsSobolevSpace M ↔ ∀ (α : List (Fin 3)) (j : Fin 3) (h : α ++ [j] ∈ sobolevWords M),
      HasWeakPartialDerivOn (univ : Set Vec3) j ⇑(v ⟨α, lps_mem_sobolevWords_of_append h⟩)
        ⇑(v ⟨α ++ [j], h⟩) := by
  simp only [lpsSobolevSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  refine forall_congr' fun α => forall_congr' fun j => forall_congr' fun h => ?_
  constructor
  · intro hv φ hφ hφc _
    have hrel := hv ⟨φ, hφ, hφc⟩
    rw [ContinuousLinearMap.coe_coe, lpsRelCLM_apply] at hrel
    simp only [Measure.restrict_univ]
    change ∫ x, _ * spatialDeriv φ j x = _
    linarith only [hrel]
  · intro hv φ
    have hrel := hv φ.1 φ.2.1 φ.2.2 (subset_univ _)
    simp only [Measure.restrict_univ] at hrel
    rw [ContinuousLinearMap.coe_coe, lpsRelCLM_apply]
    change ∫ x, _ * spatialDeriv φ.1 j x = _ at hrel
    linarith only [hrel]

/-- `H^M(ℝ³)` is closed in the space of slot vectors (`prop:lps-smoothing`). -/
theorem isClosed_lpsSobolevSpace (M : ℕ) :
    IsClosed (lpsSobolevSpace M : Set (LpsSlots M)) := by
  simp only [lpsSobolevSpace, Submodule.coe_iInf]
  exact isClosed_iInter fun α => isClosed_iInter fun j => isClosed_iInter fun h =>
    isClosed_iInter fun φ => (lpsRelCLM M α j h φ).isClosed_ker

/-- `H^M(ℝ³)` is complete (`prop:lps-smoothing`). -/
@[expose] instance (M : ℕ) : CompleteSpace (lpsSobolevSpace M) :=
  (isClosed_lpsSobolevSpace M).completeSpace_coe

/-- The slot of an element of `H^M(ℝ³)` at the word `α` cut to its first `M` letters; for words
of length at most `M` this is the slot `α` itself (`prop:lps-smoothing`). -/
@[expose] def lpsSlotCLM (M : ℕ) (α : List (Fin 3)) :
    lpsSobolevSpace M →L[ℝ] Lp ℝ 2 (volume : Measure Vec3) :=
  (ContinuousLinearMap.proj ⟨α.take M, mem_sobolevWords.2 (List.length_take_le M α)⟩).comp
    (lpsSobolevSpace M).subtypeL

/-- The slot of a word within the order bound is the corresponding entry (`prop:lps-smoothing`). -/
theorem lpsSlotCLM_of_mem {M : ℕ} {α : List (Fin 3)} (h : α ∈ sobolevWords M)
    (v : lpsSobolevSpace M) : lpsSlotCLM M α v = (v : LpsSlots M) ⟨α, h⟩ := by
  have hα : α.take M = α := List.take_of_length_le (mem_sobolevWords.1 h)
  simp only [lpsSlotCLM, ContinuousLinearMap.coe_comp, Function.comp_apply,
    Submodule.subtypeL_apply, ContinuousLinearMap.proj_apply, hα]

/-- Each slot is bounded by the norm of the slot vector (`prop:lps-smoothing`). -/
theorem lpsSlotCLM_norm_le {M : ℕ} (α : List (Fin 3)) (v : lpsSobolevSpace M) :
    ‖lpsSlotCLM M α v‖ ≤ ‖v‖ :=
  norm_le_pi_norm (v : LpsSlots M) _

/-- The slots of an element of `H^M(ℝ³)` form a Sobolev family through order `M`
(`prop:lps-smoothing`). -/
theorem lps_isSobolevFamilyOn_slot {M : ℕ} (v : lpsSobolevSpace M) :
    IsSobolevFamilyOn M univ ⇑(lpsSlotCLM M [] v) (fun α => ⇑(lpsSlotCLM M α v)) := by
  refine ⟨Filter.EventuallyEq.rfl, fun α _ => ?_, fun α j hα => ?_⟩
  · rw [Measure.restrict_univ]
    exact Lp.memLp _
  · have h : α ++ [j] ∈ sobolevWords M := by
      rw [mem_sobolevWords]
      simp only [List.length_append, List.length_singleton]
      omega
    have hrel := (mem_lpsSobolevSpace.1 v.2) α j h
    rw [lpsSlotCLM_of_mem (lps_mem_sobolevWords_of_append h), lpsSlotCLM_of_mem h]
    exact hrel

/-- An element of `H^M(ℝ³)` is determined by its slots (`prop:lps-smoothing`). -/
theorem lps_sobolevSpace_ext {M : ℕ} {v w : lpsSobolevSpace M}
    (h : ∀ α : List (Fin 3), α.length ≤ M → lpsSlotCLM M α v = lpsSlotCLM M α w) : v = w := by
  apply Subtype.ext
  funext α
  have := h α.1 (mem_sobolevWords.1 α.2)
  rwa [lpsSlotCLM_of_mem α.2, lpsSlotCLM_of_mem α.2] at this

/-- An element of `H^M(ℝ³)` is determined by its order-zero slot, since weak derivatives are
unique (`prop:lps-smoothing`). -/
theorem lps_sobolevSpace_eq_of_slot_nil {M : ℕ} {v w : lpsSobolevSpace M}
    (h : lpsSlotCLM M [] v = lpsSlotCLM M [] w) : v = w := by
  rw [← sub_eq_zero]
  have h0 : lpsSlotCLM M [] (v - w) = 0 := by rw [map_sub, h, sub_self]
  have hfam := lps_isSobolevFamilyOn_slot (v - w)
  have hfam0 : IsSobolevFamilyOn M univ (fun _ => (0 : ℝ)) (fun α => ⇑(lpsSlotCLM M α (v - w))) :=
    hfam.congr_ae (by rw [h0]; exact ae_restrict_of_ae (Lp.coeFn_zero _ _ _))
      fun _ _ => Filter.EventuallyEq.rfl
  have hzero : IsSobolevFamilyOn M univ (fun _ => (0 : ℝ)) (fun _ _ => 0) :=
    ⟨Filter.EventuallyEq.rfl, fun _ _ => MemLp.zero, fun _ _ _ φ _ _ _ => by simp⟩
  have hae := hfam0.ae_eq isOpen_univ hzero
  refine lps_sobolevSpace_ext fun α hα => ?_
  rw [map_zero]
  apply Lp.ext
  have := hae α hα
  rw [Measure.restrict_univ] at this
  exact this.trans (Lp.coeFn_zero _ _ _).symm

/-- Two `L²` classes with the same pairings against all test functions coincide
(`prop:lps-smoothing`). -/
theorem lps_Lp_eq_of_pairing {f g : Lp ℝ 2 (volume : Measure Vec3)}
    (h : ∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, f x * φ x = ∫ x, g x * φ x) : f = g := by
  apply Lp.ext
  refine ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp f).locallyIntegrable (by norm_num))
    ((Lp.memLp g).locallyIntegrable (by norm_num)) fun φ hφ hφc => ?_
  simp only [smul_eq_mul]
  simp only [mul_comm (φ _)]
  exact h φ hφ hφc

/-- The inclusion `H^(M+1)(ℝ³) → H^M(ℝ³)` (`prop:lps-smoothing`). -/
@[expose] def lpsInclCLM (M : ℕ) : lpsSobolevSpace (M + 1) →L[ℝ] lpsSobolevSpace M :=
  ((ContinuousLinearMap.pi fun α : {α : List (Fin 3) // α ∈ sobolevWords M} =>
      (ContinuousLinearMap.proj ⟨α.1, lps_mem_sobolevWords_succ α.2⟩ :
        LpsSlots (M + 1) →L[ℝ] Lp ℝ 2 (volume : Measure Vec3))).comp
      (lpsSobolevSpace (M + 1)).subtypeL).codRestrict (lpsSobolevSpace M) fun v =>
    mem_lpsSobolevSpace.2 fun α j h =>
      (mem_lpsSobolevSpace.1 v.2) α j (lps_mem_sobolevWords_succ h)

/-- The inclusion keeps the slots of order at most `M` (`prop:lps-smoothing`). -/
theorem lpsSlotCLM_incl {M : ℕ} (v : lpsSobolevSpace (M + 1)) {α : List (Fin 3)}
    (hα : α.length ≤ M) : lpsSlotCLM M α (lpsInclCLM M v) = lpsSlotCLM (M + 1) α v := by
  have h : α ∈ sobolevWords M := mem_sobolevWords.2 hα
  rw [lpsSlotCLM_of_mem h, lpsSlotCLM_of_mem (lps_mem_sobolevWords_succ h)]
  rfl

/-- The weak partial derivative `∂_k : H^(M+1)(ℝ³) → H^M(ℝ³)`: the slot `α` of `∂_k v` is the
slot `k :: α` of `v` (`prop:lps-smoothing`). -/
@[expose] def lpsDerivCLM (M : ℕ) (k : Fin 3) : lpsSobolevSpace (M + 1) →L[ℝ] lpsSobolevSpace M :=
  ((ContinuousLinearMap.pi fun α : {α : List (Fin 3) // α ∈ sobolevWords M} =>
      (ContinuousLinearMap.proj ⟨k :: α.1, lps_cons_mem_sobolevWords k α.2⟩ :
        LpsSlots (M + 1) →L[ℝ] Lp ℝ 2 (volume : Measure Vec3))).comp
      (lpsSobolevSpace (M + 1)).subtypeL).codRestrict (lpsSobolevSpace M) fun v =>
    mem_lpsSobolevSpace.2 fun α j h =>
      (mem_lpsSobolevSpace.1 v.2) (k :: α) j (lps_cons_mem_sobolevWords k h)

/-- The slot `α` of `∂_k v` is the slot `k :: α` of `v` (`prop:lps-smoothing`). -/
theorem lpsSlotCLM_deriv {M : ℕ} (k : Fin 3) (v : lpsSobolevSpace (M + 1)) {α : List (Fin 3)}
    (hα : α.length ≤ M) : lpsSlotCLM M α (lpsDerivCLM M k v) = lpsSlotCLM (M + 1) (k :: α) v := by
  have h : α ∈ sobolevWords M := mem_sobolevWords.2 hα
  rw [lpsSlotCLM_of_mem h, lpsSlotCLM_of_mem (lps_cons_mem_sobolevWords k h)]
  rfl

/-- The members of a Sobolev family of order at most `M` are square integrable
(`prop:lps-smoothing`). -/
theorem lps_memLp_of_family {M : ℕ} {D : List (Fin 3) → Vec3 → ℝ}
    (hD : IsSobolevFamilyOn M univ (D []) D) {α : List (Fin 3)} (hα : α.length ≤ M) :
    MemLp (D α) 2 volume := by
  simpa only [Measure.restrict_univ] using hD.memL2 α hα

/-- The `L²` classes of a Sobolev family through order `M` form an element of `H^M(ℝ³)`
(`prop:lps-smoothing`). -/
theorem lps_slots_mem_of_family {M : ℕ} {D : List (Fin 3) → Vec3 → ℝ}
    (hD : IsSobolevFamilyOn M univ (D []) D) :
    (fun α : {α : List (Fin 3) // α ∈ sobolevWords M} =>
      (lps_memLp_of_family hD (mem_sobolevWords.1 α.2)).toLp (D α.1)) ∈ lpsSobolevSpace M := by
  refine mem_lpsSobolevSpace.2 fun α j h => ?_
  have hlen : (α ++ [j]).length ≤ M := mem_sobolevWords.1 h
  have hα : α.length < M := by
    simp only [List.length_append, List.length_singleton] at hlen
    omega
  refine lps_hasWeakPartialDerivOn_congr (hD.weak α j hα) ?_ ?_
  · rw [Measure.restrict_univ]
    exact (MemLp.coeFn_toLp _).symm
  · rw [Measure.restrict_univ]
    exact (MemLp.coeFn_toLp _).symm

/-- The element of `H^M(ℝ³)` whose slots are the `L²` classes of a Sobolev family through order
`M` (`prop:lps-smoothing`). -/
@[expose] def lpsSobolevOf (M : ℕ) (D : List (Fin 3) → Vec3 → ℝ)
    (hD : IsSobolevFamilyOn M univ (D []) D) : lpsSobolevSpace M :=
  ⟨_, lps_slots_mem_of_family hD⟩

/-- The slots of the element of `H^M(ℝ³)` built from a Sobolev family are the `L²` classes of
the family (`prop:lps-smoothing`). -/
theorem lpsSlotCLM_sobolevOf {M : ℕ} {D : List (Fin 3) → Vec3 → ℝ}
    (hD : IsSobolevFamilyOn M univ (D []) D) {α : List (Fin 3)} (hα : α.length ≤ M) :
    lpsSlotCLM M α (lpsSobolevOf M D hD) = (lps_memLp_of_family hD hα).toLp (D α) :=
  lpsSlotCLM_of_mem (mem_sobolevWords.2 hα) _

end ESS
