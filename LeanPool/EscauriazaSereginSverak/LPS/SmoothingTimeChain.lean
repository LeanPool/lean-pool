/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingTimeChainCurve
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingOdeTower

/-!
# Time smoothness of the projected Navier–Stokes evolution

`prop:lps-smoothing`: slot data of a velocity field that are Sobolev families of every order,
continuous in time in `L²`, consistent across orders, and that solve the Leray-projected
Navier–Stokes equation `∂ₜ u = Δu - P(u · ∇u)` weakly in time, have time derivatives of every
order. For each `j` and each word `α`, the slot `α` of `∂ₜ^j u` is an `L²`-continuous curve on
the closed interval whose test pairings are differentiable with the pairings of `∂ₜ^(j+1) u` as
derivatives. The tower curves are `C^∞` by `lps_ode_tower_contDiffOn`, and the slots of their
iterated derivatives are the required data.
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The inclusion `H^(n+2) → H^(n+1)` of vector fields (`prop:lps-smoothing`). -/
@[expose] def lpsFieldInclCLM (n : ℕ) :
    (Fin 3 → lpsSobolevSpace (n + 1 + 1)) →L[ℝ] (Fin 3 → lpsSobolevSpace (n + 1)) :=
  ContinuousLinearMap.pi fun i => (lpsInclCLM (n + 1)).comp (ContinuousLinearMap.proj i)

/-- The slot `α` of the `j`-th time derivative of the `i`-th velocity component at time `t`,
read off the tower curve of level `α.length + 1` (`prop:lps-smoothing`). -/
@[expose] def lpsTimeChainSlots (a T : ℝ) (Zm : ℕ → Fin 3 → ℝ → List (Fin 3) → Vec3 → ℝ)
    (hfam : ∀ (m : ℕ) (i : Fin 3) (t : ℝ),
      IsSobolevFamilyOn m (Set.univ : Set Vec3) (Zm m i t []) (Zm m i t))
    (j : ℕ) (i : Fin 3) (t : ℝ) (α : List (Fin 3)) : Vec3 → ℝ :=
  ⇑(lpsSlotCLM (α.length + 1) α
    (iteratedDerivWithin j (lpsTowerCurve Zm hfam α.length) (Icc a T) t i))

section Extraction

variable {a T : ℝ} {Zm : ℕ → Fin 3 → ℝ → List (Fin 3) → Vec3 → ℝ}

/-- Consecutive tower curves are related by the inclusion (`prop:lps-smoothing`). -/
theorem lps_towerCurve_incl
    (hfam : ∀ (m : ℕ) (i : Fin 3) (t : ℝ),
      IsSobolevFamilyOn m (Set.univ : Set Vec3) (Zm m i t []) (Zm m i t))
    (hcons : ∀ (m m' : ℕ) (i : Fin 3) (α : List (Fin 3)), α.length ≤ m → α.length ≤ m' →
      ∀ t ∈ Icc a T, Zm m i t α =ᵐ[volume] Zm m' i t α)
    (n : ℕ) : EqOn (lpsTowerCurve Zm hfam n) (lpsFieldInclCLM n ∘ lpsTowerCurve Zm hfam (n + 1))
      (Icc a T) := by
  intro t ht
  funext i
  refine lps_sobolevSpace_ext fun α hα => ?_
  change _ = lpsSlotCLM (n + 1) α (lpsInclCLM (n + 1) (lpsTowerCurve Zm hfam (n + 1) t i))
  rw [lps_towerCurve_slot hfam n i t hα, lpsSlotCLM_incl _ hα,
    lps_towerCurve_slot hfam (n + 1) i t (by omega)]
  exact MemLp.toLp_congr _ _ (hcons (n + 1) (n + 1 + 1) i α hα (by omega) t ht)

/-- The iterated time derivatives of consecutive tower curves are related by the inclusion
(`prop:lps-smoothing`). -/
theorem lps_towerCurve_iteratedDeriv_incl (hab : a < T)
    (hfam : ∀ (m : ℕ) (i : Fin 3) (t : ℝ),
      IsSobolevFamilyOn m (Set.univ : Set Vec3) (Zm m i t []) (Zm m i t))
    (hcons : ∀ (m m' : ℕ) (i : Fin 3) (α : List (Fin 3)), α.length ≤ m → α.length ≤ m' →
      ∀ t ∈ Icc a T, Zm m i t α =ᵐ[volume] Zm m' i t α)
    (hsmooth : ∀ (k n : ℕ), ContDiffOn ℝ k (lpsTowerCurve Zm hfam n) (Icc a T))
    (n j : ℕ) {t : ℝ} (ht : t ∈ Icc a T) :
    iteratedDerivWithin j (lpsTowerCurve Zm hfam n) (Icc a T) t =
      lpsFieldInclCLM n (iteratedDerivWithin j (lpsTowerCurve Zm hfam (n + 1)) (Icc a T) t) := by
  rw [iteratedDerivWithin_congr (lps_towerCurve_incl hfam hcons n) ht,
    iteratedDerivWithin_eq_iteratedFDerivWithin,
    (lpsFieldInclCLM n).iteratedFDerivWithin_comp_left ((hsmooth j (n + 1)) t ht)
      (uniqueDiffOn_Icc hab) ht le_rfl]
  rfl

/-- The slot `α` of an iterated time derivative does not depend on the level of the tower curve
it is read from (`prop:lps-smoothing`). -/
theorem lps_towerCurve_slot_level (hab : a < T)
    (hfam : ∀ (m : ℕ) (i : Fin 3) (t : ℝ),
      IsSobolevFamilyOn m (Set.univ : Set Vec3) (Zm m i t []) (Zm m i t))
    (hcons : ∀ (m m' : ℕ) (i : Fin 3) (α : List (Fin 3)), α.length ≤ m → α.length ≤ m' →
      ∀ t ∈ Icc a T, Zm m i t α =ᵐ[volume] Zm m' i t α)
    (hsmooth : ∀ (k n : ℕ), ContDiffOn ℝ k (lpsTowerCurve Zm hfam n) (Icc a T))
    (j : ℕ) (i : Fin 3) {t : ℝ} (ht : t ∈ Icc a T) (α : List (Fin 3)) :
    ∀ n, α.length ≤ n →
      lpsSlotCLM (n + 1) α (iteratedDerivWithin j (lpsTowerCurve Zm hfam n) (Icc a T) t i) =
        lpsSlotCLM (α.length + 1) α
          (iteratedDerivWithin j (lpsTowerCurve Zm hfam α.length) (Icc a T) t i) := by
  refine Nat.le_induction rfl fun n hn ih => ?_
  rw [← ih, lps_towerCurve_iteratedDeriv_incl hab hfam hcons hsmooth n j ht]
  exact (lpsSlotCLM_incl _ (by omega)).symm

/-- The extracted slots are Sobolev families of every order (`prop:lps-smoothing`). -/
theorem lps_timeChainSlots_family (hab : a < T)
    (hfam : ∀ (m : ℕ) (i : Fin 3) (t : ℝ),
      IsSobolevFamilyOn m (Set.univ : Set Vec3) (Zm m i t []) (Zm m i t))
    (hcons : ∀ (m m' : ℕ) (i : Fin 3) (α : List (Fin 3)), α.length ≤ m → α.length ≤ m' →
      ∀ t ∈ Icc a T, Zm m i t α =ᵐ[volume] Zm m' i t α)
    (hsmooth : ∀ (k n : ℕ), ContDiffOn ℝ k (lpsTowerCurve Zm hfam n) (Icc a T))
    (j : ℕ) (i : Fin 3) {t : ℝ} (ht : t ∈ Icc a T) (m : ℕ) :
    IsSobolevFamilyOn m (Set.univ : Set Vec3) (lpsTimeChainSlots a T Zm hfam j i t [])
      (lpsTimeChainSlots a T Zm hfam j i t) := by
  refine ⟨Filter.EventuallyEq.rfl, fun α _ => ?_, fun α k _ => ?_⟩
  · rw [Measure.restrict_univ]
    exact Lp.memLp _
  · have h1 := lps_towerCurve_slot_level hab hfam hcons hsmooth j i ht α (α.length + 1)
      (by omega)
    have h2 := lps_towerCurve_slot_level hab hfam hcons hsmooth j i ht (α ++ [k])
      (α.length + 1) (by simp)
    unfold lpsTimeChainSlots
    rw [← h1, ← h2]
    exact (lps_isSobolevFamilyOn_slot _).weak α k (by omega)

/-- The extracted slots are continuous in time in `L²` (`prop:lps-smoothing`). -/
theorem lps_timeChainSlots_tendsto (hab : a < T)
    (hfam : ∀ (m : ℕ) (i : Fin 3) (t : ℝ),
      IsSobolevFamilyOn m (Set.univ : Set Vec3) (Zm m i t []) (Zm m i t))
    (hsmooth : ∀ (k n : ℕ), ContDiffOn ℝ k (lpsTowerCurve Zm hfam n) (Icc a T))
    (j : ℕ) (i : Fin 3) (α : List (Fin 3)) {t : ℝ} (ht : t ∈ Icc a T) :
    Tendsto (fun s => eLpNorm (lpsTimeChainSlots a T Zm hfam j i s α -
      lpsTimeChainSlots a T Zm hfam j i t α) 2 volume) (𝓝[Icc a T] t) (𝓝 0) := by
  have hc : ContinuousOn (iteratedDerivWithin j (lpsTowerCurve Zm hfam α.length) (Icc a T))
      (Icc a T) :=
    (hsmooth j α.length).continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Icc hab)
  let F : ℝ → Lp ℝ 2 (volume : Measure Vec3) := fun s => lpsSlotCLM (α.length + 1) α
    (iteratedDerivWithin j (lpsTowerCurve Zm hfam α.length) (Icc a T) s i)
  have hF0 : Continuous fun y : Fin 3 → lpsSobolevSpace (α.length + 1) =>
      lpsSlotCLM (α.length + 1) α (y i) :=
    (lpsSlotCLM (α.length + 1) α).continuous.comp (continuous_apply i)
  have hF : ContinuousWithinAt F (Icc a T) t :=
    hF0.continuousAt.comp_continuousWithinAt (hc t ht)
  have h : Tendsto (fun s => edist (F s) (F t)) (𝓝[Icc a T] t) (𝓝 0) :=
    tendsto_iff_edist_tendsto_0.1 hF
  have e : ∀ s, edist (F s) (F t) = eLpNorm (⇑(F s) - ⇑(F t)) 2 volume := fun s =>
    Lp.edist_def (F s) (F t)
  simp only [e] at h
  exact h

/-- The test pairings of the extracted slots are differentiable in time, with the pairings of the
next time derivative as derivatives (`prop:lps-smoothing`). -/
theorem lps_timeChainSlots_hasDerivWithinAt (hab : a < T)
    (hfam : ∀ (m : ℕ) (i : Fin 3) (t : ℝ),
      IsSobolevFamilyOn m (Set.univ : Set Vec3) (Zm m i t []) (Zm m i t))
    (hsmooth : ∀ (k n : ℕ), ContDiffOn ℝ k (lpsTowerCurve Zm hfam n) (Icc a T))
    (j : ℕ) (i : Fin 3) (α : List (Fin 3)) {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) {t : ℝ} (ht : t ∈ Icc a T) :
    HasDerivWithinAt (fun s => ∫ x, lpsTimeChainSlots a T Zm hfam j i s α x * ψ x)
      (∫ x, lpsTimeChainSlots a T Zm hfam (j + 1) i t α x * ψ x) (Icc a T) t := by
  have hψ2 := lpsLeray_memLp_test hψ hψc
  let ℓ : (Fin 3 → lpsSobolevSpace (α.length + 1)) →L[ℝ] ℝ :=
    (lpsPairCLM ψ hψ2).comp ((lpsSlotCLM (α.length + 1) α).comp (ContinuousLinearMap.proj i))
  have hℓ : ∀ y, ℓ y = ∫ x, lpsSlotCLM (α.length + 1) α (y i) x * ψ x := fun y =>
    lpsPairCLM_apply hψ2 _
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin j (lpsTowerCurve Zm hfam α.length) (Icc a T))
      (Icc a T) :=
    (hsmooth (j + 1) α.length).differentiableOn_iteratedDerivWithin
      (by exact_mod_cast Nat.lt_succ_self j) (uniqueDiffOn_Icc hab)
  have hd : HasDerivWithinAt (iteratedDerivWithin j (lpsTowerCurve Zm hfam α.length) (Icc a T))
      (iteratedDerivWithin (j + 1) (lpsTowerCurve Zm hfam α.length) (Icc a T) t) (Icc a T) t := by
    rw [iteratedDerivWithin_succ]
    exact (hdiff t ht).hasDerivWithinAt
  convert ℓ.hasFDerivAt.comp_hasDerivWithinAt t hd using 1
  · funext s
    exact (hℓ _).symm
  · exact (hℓ _).symm

/-- The order-zero slot of the order-zero time derivative is the velocity data
(`prop:lps-smoothing`). -/
theorem lps_timeChainSlots_zero
    (hfam : ∀ (m : ℕ) (i : Fin 3) (t : ℝ),
      IsSobolevFamilyOn m (Set.univ : Set Vec3) (Zm m i t []) (Zm m i t))
    (hcons : ∀ (m m' : ℕ) (i : Fin 3) (α : List (Fin 3)), α.length ≤ m → α.length ≤ m' →
      ∀ t ∈ Icc a T, Zm m i t α =ᵐ[volume] Zm m' i t α)
    {t : ℝ} (ht : t ∈ Icc a T) (i : Fin 3) :
    lpsTimeChainSlots a T Zm hfam 0 i t [] =ᵐ[volume] Zm 0 i t [] := by
  change ⇑(lpsSlotCLM (0 + 1) [] (iteratedDerivWithin 0 (lpsTowerCurve Zm hfam 0) (Icc a T) t i))
    =ᵐ[volume] _
  rw [iteratedDerivWithin_zero, lps_towerCurve_slot hfam 0 i t (Nat.zero_le _)]
  exact (MemLp.coeFn_toLp _).trans
    (hcons (0 + 1) 0 i [] (Nat.zero_le _) le_rfl t ht)

end Extraction

/-- Time chain of the projected Navier–Stokes evolution for slot data defined at all times
(`prop:lps-smoothing`): the statement of `lps_time_chain` with the family hypothesis at every
time. -/
theorem lps_time_chain_of_family {a T : ℝ} (hab : a < T) {u : ParabolicPoint → Vec3}
    {Dtu : ParabolicPoint → Vec3}
    (Zm : ℕ → Fin 3 → ℝ → List (Fin 3) → Vec3 → ℝ)
    (hfam : ∀ (m : ℕ) (i : Fin 3) (t : ℝ),
      IsSobolevFamilyOn m (Set.univ : Set Vec3) (Zm m i t []) (Zm m i t))
    (hcont : ∀ (m : ℕ) (i : Fin 3) (α : List (Fin 3)), α.length ≤ m → ∀ t ∈ Icc a T,
      Tendsto (fun s => eLpNorm (Zm m i s α - Zm m i t α) 2 volume) (nhdsWithin t (Icc a T))
        (nhds 0))
    (hcons : ∀ (m m' : ℕ) (i : Fin 3) (α : List (Fin 3)), α.length ≤ m → α.length ≤ m' →
      ∀ t ∈ Icc a T, Zm m i t α =ᵐ[volume] Zm m' i t α)
    (hae : ∀ᵐ t ∂(volume.restrict (Ioo a T)), ∀ i, Zm 0 i t [] =ᵐ[volume] fun x => u (x, t) i)
    (htw : ∀ (i : Fin 3) (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∀ s t, a ≤ s → s ≤ t → t ≤ T →
        (∫ x, Zm 0 i t [] x * ψ x) - ∫ x, Zm 0 i s [] x * ψ x =
          ∫ τ in s..t, ∫ x, Dtu (x, τ) i * ψ x)
    (hequ : ∀ᵐ τ ∂(volume.restrict (Ioo a T)), ∀ (i : Fin 3)
      (hg : ∀ i' : Fin 3, MemLp (fun x => ∑ j, Zm 1 j τ [] x * Zm 1 i' τ [j] x) 2 volume),
      (fun x => Dtu (x, τ) i) =ᵐ[volume]
        fun x => (∑ k, Zm 2 i τ [k, k] x) -
          lpsLerayApply (fun i' x => ∑ j, Zm 1 j τ [] x * Zm 1 i' τ [j] x) hg i x) :
    ∃ Z : ℕ → Fin 3 → ℝ → List (Fin 3) → Vec3 → ℝ,
      (∀ (i : Fin 3) (j : ℕ), ∀ t ∈ Icc a T, ∀ m : ℕ,
        IsSobolevFamilyOn m (Set.univ : Set Vec3) (Z j i t []) (Z j i t)) ∧
      (∀ (i : Fin 3) (j : ℕ) (α : List (Fin 3)), ∀ t ∈ Icc a T,
        Tendsto (fun s => eLpNorm (Z j i s α - Z j i t α) 2 volume) (nhdsWithin t (Icc a T))
          (nhds 0)) ∧
      (∀ (i : Fin 3) (j : ℕ) (α : List (Fin 3)) (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ → ∀ t ∈ Icc a T,
          HasDerivWithinAt (fun s => ∫ x, Z j i s α x * ψ x) (∫ x, Z (j + 1) i t α x * ψ x)
            (Icc a T) t) ∧
      (∀ᵐ t ∂(volume.restrict (Ioo a T)), ∀ i, Z 0 i t [] =ᵐ[volume] fun x => u (x, t) i) := by
  have hsmooth : ∀ (k n : ℕ), ContDiffOn ℝ k (lpsTowerCurve Zm hfam n) (Icc a T) := fun k n =>
    lps_ode_tower_contDiffOn hab (X := fun n => Fin 3 → lpsSobolevSpace (n + 1)) lpsNSMap
      lpsNSMap_contDiff (fun n => lpsTowerCurve Zm hfam n) (lps_towerCurve_continuousOn hfam hcont)
      (lps_towerCurve_integral hfam hcont hcons htw hequ) k n
  refine ⟨lpsTimeChainSlots a T Zm hfam,
    fun i j t ht m => lps_timeChainSlots_family hab hfam hcons hsmooth j i ht m,
    fun i j α t ht => lps_timeChainSlots_tendsto hab hfam hsmooth j i α ht,
    fun i j α ψ hψ hψc t ht => lps_timeChainSlots_hasDerivWithinAt hab hfam hsmooth j i α hψ hψc ht,
    ?_⟩
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with t ht htI i
  exact (lps_timeChainSlots_zero hfam hcons (Ioo_subset_Icc_self htI) i).trans (ht i)

/-- Time chain of the projected Navier–Stokes evolution (`prop:lps-smoothing`). Slot data `Zm m i t`
of the velocity components that are Sobolev families of every order `m`, continuous in time in
`L²`, consistent across orders, equal to the velocity at almost every time, and that solve
`∂ₜ u = Δu - P(u · ∇u)` weakly in time, have all time derivatives: there are slots `Z j i t α` of
`∂ₜ^j u_i(t)` forming Sobolev families of every order, continuous in time in `L²` on the closed
interval, whose test pairings are differentiable in time with the pairings of `Z (j + 1)` as
derivatives, and with `Z 0 i t [] = u(·, t)_i` at almost every time. -/
theorem lps_time_chain {a T : ℝ} (hab : a < T) {u : ParabolicPoint → Vec3}
    {Dtu : ParabolicPoint → Vec3}
    (Zm : ℕ → Fin 3 → ℝ → List (Fin 3) → Vec3 → ℝ)
    (hfam : ∀ (m : ℕ) (i : Fin 3), ∀ t ∈ Icc a T,
      IsSobolevFamilyOn m (Set.univ : Set Vec3) (Zm m i t []) (Zm m i t))
    (hcont : ∀ (m : ℕ) (i : Fin 3) (α : List (Fin 3)), α.length ≤ m → ∀ t ∈ Icc a T,
      Tendsto (fun s => eLpNorm (Zm m i s α - Zm m i t α) 2 volume) (nhdsWithin t (Icc a T))
        (nhds 0))
    (hcons : ∀ (m m' : ℕ) (i : Fin 3) (α : List (Fin 3)), α.length ≤ m → α.length ≤ m' →
      ∀ t ∈ Icc a T, Zm m i t α =ᵐ[volume] Zm m' i t α)
    (hae : ∀ᵐ t ∂(volume.restrict (Ioo a T)), ∀ i, Zm 0 i t [] =ᵐ[volume] fun x => u (x, t) i)
    (htw : ∀ (i : Fin 3) (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∀ s t, a ≤ s → s ≤ t → t ≤ T →
        (∫ x, Zm 0 i t [] x * ψ x) - ∫ x, Zm 0 i s [] x * ψ x =
          ∫ τ in s..t, ∫ x, Dtu (x, τ) i * ψ x)
    (hequ : ∀ᵐ τ ∂(volume.restrict (Ioo a T)), ∀ (i : Fin 3)
      (hg : ∀ i' : Fin 3, MemLp (fun x => ∑ j, Zm 1 j τ [] x * Zm 1 i' τ [j] x) 2 volume),
      (fun x => Dtu (x, τ) i) =ᵐ[volume]
        fun x => (∑ k, Zm 2 i τ [k, k] x) -
          lpsLerayApply (fun i' x => ∑ j, Zm 1 j τ [] x * Zm 1 i' τ [j] x) hg i x) :
    ∃ Z : ℕ → Fin 3 → ℝ → List (Fin 3) → Vec3 → ℝ,
      (∀ (i : Fin 3) (j : ℕ), ∀ t ∈ Icc a T, ∀ m : ℕ,
        IsSobolevFamilyOn m (Set.univ : Set Vec3) (Z j i t []) (Z j i t)) ∧
      (∀ (i : Fin 3) (j : ℕ) (α : List (Fin 3)), ∀ t ∈ Icc a T,
        Tendsto (fun s => eLpNorm (Z j i s α - Z j i t α) 2 volume) (nhdsWithin t (Icc a T))
          (nhds 0)) ∧
      (∀ (i : Fin 3) (j : ℕ) (α : List (Fin 3)) (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ → ∀ t ∈ Icc a T,
          HasDerivWithinAt (fun s => ∫ x, Z j i s α x * ψ x) (∫ x, Z (j + 1) i t α x * ψ x)
            (Icc a T) t) ∧
      (∀ᵐ t ∂(volume.restrict (Ioo a T)), ∀ i, Z 0 i t [] =ᵐ[volume] fun x => u (x, t) i) := by
  -- extend the slot data constantly beyond the interval, so that the family hypothesis holds at
  -- every time
  have hZc : ∀ t ∈ Icc a T, ((Set.projIcc a T hab.le t : Icc a T) : ℝ) = t := fun t ht =>
    congrArg Subtype.val (Set.projIcc_of_mem hab.le ht)
  let Zc : ℕ → Fin 3 → ℝ → List (Fin 3) → Vec3 → ℝ := fun m i t =>
    Zm m i (Set.projIcc a T hab.le t)
  have hZcd : ∀ (m : ℕ) (i : Fin 3) (t : ℝ) (α : List (Fin 3)), t ∈ Icc a T →
      Zc m i t α = Zm m i t α := fun m i t α ht => by
    simp only [Zc, hZc t ht]
  refine lps_time_chain_of_family hab (u := u) (Dtu := Dtu) Zc (fun m i t => hfam m i _
    (Subtype.property _))
    (fun m i α hα t ht => ?_) (fun m m' i α hα hα' t ht => ?_) ?_ (fun i ψ hψ hψc s t hs hst ht
      => ?_)
    ?_
  · refine (hcont m i α hα t ht).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [hZcd m i s α hs, hZcd m i t α ht]
  · rw [hZcd m i t α ht, hZcd m' i t α ht]
    exact hcons m m' i α hα hα' t ht
  · filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with t h htI i
    rw [hZcd 0 i t [] (Ioo_subset_Icc_self htI)]
    exact h i
  · rw [hZcd 0 i t [] ⟨hs.trans hst, ht⟩, hZcd 0 i s [] ⟨hs, hst.trans ht⟩]
    exact htw i ψ hψ hψc s t hs hst ht
  · filter_upwards [hequ, ae_restrict_mem measurableSet_Ioo] with τ h hτI i hg
    have hτ := Ioo_subset_Icc_self hτI
    have hg' : ∀ i' : Fin 3, MemLp (fun x => ∑ j, Zm 1 j τ [] x * Zm 1 i' τ [j] x) 2 volume := by
      simpa only [Zc, hZcd 1 _ τ _ hτ] using hg
    have := h i hg'
    simpa only [Zc, hZcd 1 _ τ _ hτ, hZcd 2 _ τ _ hτ] using this

end ESS
