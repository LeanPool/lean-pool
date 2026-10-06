/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingTimeChainProduct

/-!
# The velocity as a curve in the Sobolev tower

`prop:lps-smoothing`: slot data of a velocity field that are square-integrable Sobolev families
of every order, continuous in time in `L²`, and satisfy the projected Navier–Stokes equation
weakly in time, define continuous curves `c_n : [a, T] → H^(n+1)` that solve
`c_n(t) - c_n(s) = ∫_s^t N(c_(n+2)(τ)) dτ` in every space of the tower.
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The curve of the level-`(n+1)` slot vectors of the velocity data (`prop:lps-smoothing`). -/
@[expose] def lpsTowerCurve (Zm : ℕ → Fin 3 → ℝ → List (Fin 3) → Vec3 → ℝ)
    (hfam : ∀ (m : ℕ) (i : Fin 3) (t : ℝ),
      IsSobolevFamilyOn m (Set.univ : Set Vec3) (Zm m i t []) (Zm m i t))
    (n : ℕ) (t : ℝ) : Fin 3 → lpsSobolevSpace (n + 1) :=
  fun i => lpsSobolevOf (n + 1) (Zm (n + 1) i t) (hfam (n + 1) i t)

/-- A sum of three `L²` classes is represented by the sum of representatives
(`prop:lps-smoothing`). -/
theorem lps_coeFn_sum_three (X : Fin 3 → Lp ℝ 2 (volume : Measure Vec3)) :
    ⇑(∑ k, X k) =ᵐ[volume] fun x => ∑ k, X k x := by
  rw [Fin.sum_univ_three]
  filter_upwards [Lp.coeFn_add (X 0 + X 1) (X 2), Lp.coeFn_add (X 0) (X 1)] with x h1 h2
  rw [h1, Pi.add_apply, h2, Pi.add_apply, Fin.sum_univ_three]

section Curve

variable {a T : ℝ} {Zm : ℕ → Fin 3 → ℝ → List (Fin 3) → Vec3 → ℝ}

/-- The slots of the velocity data are square integrable (`prop:lps-smoothing`). -/
theorem lps_towerCurve_memLp
    (hfam : ∀ (m : ℕ) (i : Fin 3) (t : ℝ),
      IsSobolevFamilyOn m (Set.univ : Set Vec3) (Zm m i t []) (Zm m i t))
    {m : ℕ} (i : Fin 3) (t : ℝ) {α : List (Fin 3)} (hα : α.length ≤ m) :
    MemLp (Zm m i t α) 2 volume :=
  lps_memLp_of_family (hfam m i t) hα

/-- The slots of the tower curve are the `L²` classes of the slot data (`prop:lps-smoothing`). -/
theorem lps_towerCurve_slot
    (hfam : ∀ (m : ℕ) (i : Fin 3) (t : ℝ),
      IsSobolevFamilyOn m (Set.univ : Set Vec3) (Zm m i t []) (Zm m i t))
    (n : ℕ) (i : Fin 3) (t : ℝ) {α : List (Fin 3)} (hα : α.length ≤ n + 1) :
    lpsSlotCLM (n + 1) α (lpsTowerCurve Zm hfam n t i) =
      (lps_towerCurve_memLp hfam i t hα).toLp (Zm (n + 1) i t α) :=
  lpsSlotCLM_sobolevOf (hfam (n + 1) i t) hα

/-- The tower curves are continuous on the closed interval (`prop:lps-smoothing`). -/
theorem lps_towerCurve_continuousOn
    (hfam : ∀ (m : ℕ) (i : Fin 3) (t : ℝ),
      IsSobolevFamilyOn m (Set.univ : Set Vec3) (Zm m i t []) (Zm m i t))
    (hcont : ∀ (m : ℕ) (i : Fin 3) (α : List (Fin 3)), α.length ≤ m → ∀ t ∈ Icc a T,
      Tendsto (fun s => eLpNorm (Zm m i s α - Zm m i t α) 2 volume) (nhdsWithin t (Icc a T))
        (nhds 0))
    (n : ℕ) : ContinuousOn (lpsTowerCurve Zm hfam n) (Icc a T) := by
  intro t ht
  refine continuousWithinAt_pi.2 fun i => ?_
  refine (Topology.IsInducing.subtypeVal.continuousWithinAt_iff).2 ?_
  refine continuousWithinAt_pi.2 fun α => ?_
  have hα : α.1.length ≤ n + 1 := mem_sobolevWords.1 α.2
  have hg : ContinuousWithinAt
      (fun s => (lps_towerCurve_memLp hfam i s hα).toLp (Zm (n + 1) i s α.1)) (Icc a T) t := by
    rw [ContinuousWithinAt, tendsto_iff_edist_tendsto_0]
    refine (hcont (n + 1) i α.1 hα t ht).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Lp.edist_toLp_toLp]
  refine hg.congr (fun s hs => ?_) ?_
  · change ((lpsTowerCurve Zm hfam n s i : lpsSobolevSpace (n + 1)) : LpsSlots (n + 1)) α = _
    rw [← lpsSlotCLM_of_mem α.2, lps_towerCurve_slot hfam n i s hα]
  · change ((lpsTowerCurve Zm hfam n t i : lpsSobolevSpace (n + 1)) : LpsSlots (n + 1)) α = _
    rw [← lpsSlotCLM_of_mem α.2, lps_towerCurve_slot hfam n i t hα]

/-- The order-zero slot of the projected Navier–Stokes right-hand side along the tower curve
is almost everywhere the right-hand side computed from the slot data (`prop:lps-smoothing`);
the convection term computed from the slot data is square integrable. -/
theorem lps_towerCurve_NS_slot_ae
    (hfam : ∀ (m : ℕ) (i : Fin 3) (t : ℝ),
      IsSobolevFamilyOn m (Set.univ : Set Vec3) (Zm m i t []) (Zm m i t))
    (hcons : ∀ (m m' : ℕ) (i : Fin 3) (α : List (Fin 3)), α.length ≤ m → α.length ≤ m' →
      ∀ t ∈ Icc a T, Zm m i t α =ᵐ[volume] Zm m' i t α)
    (n : ℕ) {τ : ℝ} (hτ : τ ∈ Icc a T) :
    ∃ hg : ∀ i' : Fin 3, MemLp (fun x => ∑ j, Zm 1 j τ [] x * Zm 1 i' τ [j] x) 2 volume,
      ∀ i : Fin 3, ⇑(lpsSlotCLM (n + 1) [] (lpsNSMap n (lpsTowerCurve Zm hfam (n + 2) τ) i))
        =ᵐ[volume] fun x => (∑ k, Zm 2 i τ [k, k] x) -
          lpsLerayApply (fun i' x => ∑ j, Zm 1 j τ [] x * Zm 1 i' τ [j] x) hg i x := by
  set v := lpsTowerCurve Zm hfam (n + 2) τ with hv
  have hZ : ∀ (i : Fin 3) (α : List (Fin 3)), α.length ≤ n + 2 + 1 → ∀ m' : ℕ,
      α.length ≤ m' → ⇑(lpsSlotCLM (n + 2 + 1) α (v i)) =ᵐ[volume] Zm m' i τ α := by
    intro i α hα m' hm'
    rw [hv, lps_towerCurve_slot hfam (n + 2) i τ hα]
    exact (MemLp.coeFn_toLp _).trans (hcons (n + 2 + 1) m' i α hα hm' τ hτ)
  -- the projected transport part
  let G : Fin 3 → Lp ℝ 2 (volume : Measure Vec3) := fun i' => ∑ j,
    (lps_memLp_slot_mul n v j i').toLp (fun x => lpsSlotCLM (n + 2 + 1) [] (v j) x *
      lpsSlotCLM (n + 2 + 1) [j] (v i') x)
  let g : Fin 3 → Vec3 → ℝ := fun i' x => ∑ j, Zm 1 j τ [] x * Zm 1 i' τ [j] x
  have hG : ∀ i', ⇑(G i') =ᵐ[volume] g i' := by
    intro i'
    have hj : ∀ᵐ x ∂volume, ∀ j : Fin 3,
        ((lps_memLp_slot_mul n v j i').toLp (fun x => lpsSlotCLM (n + 2 + 1) [] (v j) x *
          lpsSlotCLM (n + 2 + 1) [j] (v i') x)) x = Zm 1 j τ [] x * Zm 1 i' τ [j] x := by
      refine ae_all_iff.2 fun j => ?_
      filter_upwards [(lps_memLp_slot_mul n v j i').coeFn_toLp,
        hZ j [] (by simp) 1 (by simp), hZ i' [j] (by simp) 1 (by simp)] with x h1 h2 h3
      rw [h1]
      rw [h2, h3]
    filter_upwards [lps_coeFn_sum_three fun j => (lps_memLp_slot_mul n v j i').toLp
      (fun x => lpsSlotCLM (n + 2 + 1) [] (v j) x * lpsSlotCLM (n + 2 + 1) [j] (v i') x),
      hj] with x h1 h2
    rw [h1]
    exact Finset.sum_congr rfl fun j _ => h2 j
  have hg : ∀ i', MemLp (g i') 2 volume := fun i' => (Lp.memLp (G i')).ae_eq (hG i')
  have hfield : lpsFieldOf g hg = WithLp.toLp 2 G := by
    unfold lpsFieldOf
    congr 1
    funext i'
    exact Lp.ext ((hg i').coeFn_toLp.trans (hG i').symm)
  refine ⟨hg, fun i => ?_⟩
  -- the Laplacian part
  have hlap : ⇑(∑ k, lpsSlotCLM (n + 2 + 1) [k, k] (v i)) =ᵐ[volume]
      fun x => ∑ k, Zm 2 i τ [k, k] x := by
    have hk : ∀ᵐ x ∂volume, ∀ k : Fin 3,
        lpsSlotCLM (n + 2 + 1) [k, k] (v i) x = Zm 2 i τ [k, k] x :=
      ae_all_iff.2 fun k => hZ i [k, k] (by simp) 2 (by simp)
    filter_upwards [lps_coeFn_sum_three fun k => lpsSlotCLM (n + 2 + 1) [k, k] (v i), hk]
      with x h1 h2
    rw [h1]
    exact Finset.sum_congr rfl fun k _ => h2 k
  have hler : ⇑(lpsLerayP (WithLp.toLp 2 G) i) = lpsLerayApply g hg i := by
    rw [lpsLerayApply_eq hg, hfield]
  rw [lpsSlotCLM_NSMap_nil n v i]
  filter_upwards [Lp.coeFn_sub (∑ k, lpsSlotCLM (n + 2 + 1) [k, k] (v i))
    (lpsLerayP (WithLp.toLp 2 G) i), hlap] with x h1 h2
  rw [h1, Pi.sub_apply, h2, hler]

/-- The pairing of the order-zero slot of the tower curve with a test function is the pairing of
the velocity data (`prop:lps-smoothing`). -/
theorem lps_towerCurve_pair
    (hfam : ∀ (m : ℕ) (i : Fin 3) (t : ℝ),
      IsSobolevFamilyOn m (Set.univ : Set Vec3) (Zm m i t []) (Zm m i t))
    (hcons : ∀ (m m' : ℕ) (i : Fin 3) (α : List (Fin 3)), α.length ≤ m → α.length ≤ m' →
      ∀ t ∈ Icc a T, Zm m i t α =ᵐ[volume] Zm m' i t α)
    (n : ℕ) (i : Fin 3) {t : ℝ} (ht : t ∈ Icc a T) {φ : Vec3 → ℝ} (hφ : MemLp φ 2 volume) :
    lpsPairCLM φ hφ (lpsSlotCLM (n + 1) [] (lpsTowerCurve Zm hfam n t i)) =
      ∫ x, Zm 0 i t [] x * φ x := by
  rw [lpsPairCLM_apply hφ, lps_towerCurve_slot hfam n i t (Nat.zero_le _)]
  refine integral_congr_ae ?_
  filter_upwards [(lps_towerCurve_memLp hfam (m := n + 1) (α := []) i t
      (Nat.zero_le _)).coeFn_toLp,
    hcons (n + 1) 0 i [] (Nat.zero_le _) le_rfl t ht] with x h1 h2
  rw [h1, h2]

/-- The tower curves solve the projected Navier–Stokes equation in integral form in every space
of the tower (`prop:lps-smoothing`). -/
theorem lps_towerCurve_integral {Dtu : ParabolicPoint → Vec3}
    (hfam : ∀ (m : ℕ) (i : Fin 3) (t : ℝ),
      IsSobolevFamilyOn m (Set.univ : Set Vec3) (Zm m i t []) (Zm m i t))
    (hcont : ∀ (m : ℕ) (i : Fin 3) (α : List (Fin 3)), α.length ≤ m → ∀ t ∈ Icc a T,
      Tendsto (fun s => eLpNorm (Zm m i s α - Zm m i t α) 2 volume) (nhdsWithin t (Icc a T))
        (nhds 0))
    (hcons : ∀ (m m' : ℕ) (i : Fin 3) (α : List (Fin 3)), α.length ≤ m → α.length ≤ m' →
      ∀ t ∈ Icc a T, Zm m i t α =ᵐ[volume] Zm m' i t α)
    (htw : ∀ (i : Fin 3) (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∀ s t, a ≤ s → s ≤ t → t ≤ T →
        (∫ x, Zm 0 i t [] x * ψ x) - ∫ x, Zm 0 i s [] x * ψ x =
          ∫ τ in s..t, ∫ x, Dtu (x, τ) i * ψ x)
    (hequ : ∀ᵐ τ ∂(volume.restrict (Ioo a T)), ∀ (i : Fin 3)
      (hg : ∀ i' : Fin 3, MemLp (fun x => ∑ j, Zm 1 j τ [] x * Zm 1 i' τ [j] x) 2 volume),
      (fun x => Dtu (x, τ) i) =ᵐ[volume]
        fun x => (∑ k, Zm 2 i τ [k, k] x) -
          lpsLerayApply (fun i' x => ∑ j, Zm 1 j τ [] x * Zm 1 i' τ [j] x) hg i x)
    (n : ℕ) : ∀ s ∈ Icc a T, ∀ t ∈ Icc a T, s ≤ t →
      lpsTowerCurve Zm hfam n t - lpsTowerCurve Zm hfam n s =
        ∫ τ in s..t, lpsNSMap n (lpsTowerCurve Zm hfam (n + 2) τ) := by
  intro s hs t ht hst
  have hsub : uIcc s t ⊆ Icc a T := by
    rw [uIcc_of_le hst]
    exact Icc_subset_Icc hs.1 ht.2
  have hNc : ContinuousOn (fun τ => lpsNSMap n (lpsTowerCurve Zm hfam (n + 2) τ)) (uIcc s t) :=
    (lpsNSMap_contDiff n).continuous.comp_continuousOn
      ((lps_towerCurve_continuousOn hfam hcont (n + 2)).mono hsub)
  funext i
  have hproj : (∫ τ in s..t, lpsNSMap n (lpsTowerCurve Zm hfam (n + 2) τ)) i =
      ∫ τ in s..t, lpsNSMap n (lpsTowerCurve Zm hfam (n + 2) τ) i :=
    ((ContinuousLinearMap.proj (R := ℝ) i).intervalIntegral_comp_comm
      hNc.intervalIntegrable).symm
  rw [Pi.sub_apply, hproj]
  have hNi : ContinuousOn (fun τ => lpsNSMap n (lpsTowerCurve Zm hfam (n + 2) τ) i) (uIcc s t) :=
    (continuous_apply i).comp_continuousOn hNc
  apply lps_sobolevSpace_eq_of_slot_nil
  rw [← (lpsSlotCLM (n + 1) []).intervalIntegral_comp_comm hNi.intervalIntegrable]
  apply lps_Lp_eq_of_pairing
  intro φ hφ hφc
  have hφ2 : MemLp φ 2 volume := lpsLeray_memLp_test hφ hφc
  have hSi : ContinuousOn
      (fun τ => lpsSlotCLM (n + 1) [] (lpsNSMap n (lpsTowerCurve Zm hfam (n + 2) τ) i)) (uIcc s t) :=
    (lpsSlotCLM (n + 1) []).continuous.comp_continuousOn hNi
  rw [← lpsPairCLM_apply hφ2, ← lpsPairCLM_apply hφ2,
    ← (lpsPairCLM φ hφ2).intervalIntegral_comp_comm hSi.intervalIntegrable, map_sub, map_sub,
    lps_towerCurve_pair hfam hcons n i ht hφ2, lps_towerCurve_pair hfam hcons n i hs hφ2,
    htw i φ hφ hφc s t hs.1 hst ht.2]
  refine intervalIntegral.integral_congr_ae ?_
  have hequ' := (ae_restrict_iff' measurableSet_Ioo).1 hequ
  filter_upwards [hequ', Measure.ae_ne volume T] with τ hτ hτT hτst
  rw [uIoc_of_le hst] at hτst
  have hτI : τ ∈ Ioo a T :=
    ⟨lt_of_le_of_lt hs.1 hτst.1, lt_of_le_of_ne (hτst.2.trans ht.2) hτT⟩
  rw [lpsPairCLM_apply hφ2]
  refine integral_congr_ae ?_
  obtain ⟨hg, hslot⟩ := lps_towerCurve_NS_slot_ae hfam hcons n (Ioo_subset_Icc_self hτI)
  filter_upwards [hτ hτI i hg, hslot i] with x h1 h2
  rw [h1, h2]

end Curve

end ESS
