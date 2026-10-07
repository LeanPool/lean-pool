/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingAssemblyFamily
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingTimeChain
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingJointPatch
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSlotConsistency
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSourceProjected
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingTimeJensen
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateGoodSlices
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateSliceConvection
public import LeanPool.EscauriazaSereginSverak.LPS.OverlapStrongSerrin

/-!
# Assembly of the smoothing of strong solutions

`prop:lps-smoothing`: the regularity ladder of a strong solution on a positive-time slab, together
with the projected equation and the time continuity of the strong class, feeds the time chain and
the joint smoothness step.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Almost every time slice of an almost everywhere identity on a slab is an almost everywhere
identity on `ℝ³` (`prop:lps-smoothing`). -/
theorem lps_ae_slices_univ {a b : ℝ} {f g : Vec3 × ℝ → ℝ}
    (h : f =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))] g) :
    ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      (fun x => f (x, t)) =ᵐ[volume] fun x => g (x, t) := by
  have := ae_slices_of_ae_prod (B := Set.univ) (I := Ioo a b) h
  simpa only [Measure.restrict_univ] using this

/-- The data of `lps_smoothing_of_curves` on a positive-time slab, from the regularity ladder of
all orders (`prop:lps-smoothing`). -/
theorem lps_smoothing_data_of_ladder {t₀ t₁ δ : ℝ} (hδ : 0 < δ) (hδT : t₀ + δ < t₁)
    {U : ParabolicPoint → Vec3} {DU : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtu : ParabolicPoint → Vec3}
    (h : IsLpsStrongSolution t₀ t₁ U DU p)
    (hderiv : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ t₁) U DU D2u Dtu)
    (hu : MemLp U 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))))
    (hDu : MemLp DU 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))))
    (hD2u : MemLp D2u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))))
    (hDtu : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))))
    (hlad : ∀ M : ℕ, 1 ≤ M →
      ∃ (Z : Fin 3 → ℝ → List (Fin 3) → Vec3 → ℝ)
        (DD : Fin 3 → List (Fin 3) → Vec3 × ℝ → ℝ),
        (∀ i, ∀ t ∈ Icc (t₀ + δ) t₁, IsSobolevFamilyOn M univ (Z i t []) (Z i t)) ∧
        (∀ i α, α.length ≤ M → ∀ t ∈ Icc (t₀ + δ) t₁,
          Tendsto (fun s => eLpNorm (Z i s α - Z i t α) 2 volume) (𝓝[Icc (t₀ + δ) t₁] t)
            (𝓝 0)) ∧
        (∀ᵐ t ∂(volume.restrict (Ioo (t₀ + δ) t₁)), ∀ i, ∀ α, α.length ≤ M →
          Z i t α =ᵐ[volume] fun x => DD i α (x, t)) ∧
        (∀ i, IsL2SobolevFamilyOn (M + 1) univ (Ioo (t₀ + δ) t₁) (fun z => U z i) (DD i)) ∧
        (∀ i k, DD i [k] =ᵐ[volume.restrict (spaceTimeSet univ (Ioo (t₀ + δ) t₁))]
          fun z => DU z i k) ∧
        (∀ i k, DD i [k, k] =ᵐ[volume.restrict (spaceTimeSet univ (Ioo (t₀ + δ) t₁))]
          fun z => D2u z i k k)) :
    ∃ Z : ℕ → Fin 3 → ℝ → List (Fin 3) → Vec3 → ℝ,
      (∀ (i : Fin 3) (j : ℕ), ∀ t ∈ Icc (t₀ + δ) t₁, ∀ m : ℕ,
        IsSobolevFamilyOn m univ (Z j i t []) (Z j i t)) ∧
      (∀ (i : Fin 3) (j : ℕ) (α : List (Fin 3)), ∀ t ∈ Icc (t₀ + δ) t₁,
        Tendsto (fun s => eLpNorm (Z j i s α - Z j i t α) 2 volume)
          (𝓝[Icc (t₀ + δ) t₁] t) (𝓝 0)) ∧
      (∀ (i : Fin 3) (j : ℕ) (α : List (Fin 3)) (ψ : Vec3 → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → ∀ t ∈ Icc (t₀ + δ) t₁,
          HasDerivWithinAt (fun s => ∫ x, Z j i s α x * ψ x)
            (∫ x, Z (j + 1) i t α x * ψ x) (Icc (t₀ + δ) t₁) t) ∧
      (∀ᵐ t ∂(volume.restrict (Ioo (t₀ + δ) t₁)), ∀ i : Fin 3,
        Z 0 i t [] =ᵐ[volume] fun x => U (x, t) i) := by
  classical
  choose Zl DDl hF hC hS hD hDuE hD2E using fun m : ℕ => hlad (max m 1) (le_max_right m 1)
  have hfam : ∀ (m : ℕ) (i : Fin 3), ∀ t ∈ Icc (t₀ + δ) t₁,
      IsSobolevFamilyOn m (Set.univ : Set Vec3) (Zl m i t []) (Zl m i t) :=
    fun m i t ht => (hF m i t ht).mono_order (le_max_left m 1)
  have hcont : ∀ (m : ℕ) (i : Fin 3) (α : List (Fin 3)), α.length ≤ m → ∀ t ∈ Icc (t₀ + δ) t₁,
      Tendsto (fun s => eLpNorm (Zl m i s α - Zl m i t α) 2 volume)
        (nhdsWithin t (Icc (t₀ + δ) t₁)) (nhds 0) :=
    fun m i α hα t ht => hC m i α (hα.trans (le_max_left m 1)) t ht
  have hDD : ∀ (m m' : ℕ) (i : Fin 3) (α : List (Fin 3)), α.length ≤ max m 1 →
      α.length ≤ max m' 1 →
      DDl m i α =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo (t₀ + δ) t₁))]
        DDl m' i α := fun m m' i α h1 h2 =>
    lps_l2SobolevFamily_unique isOpen_Ioo (hD m i) (hD m' i) α (by omega) (by omega)
  have hcons : ∀ (m m' : ℕ) (i : Fin 3) (α : List (Fin 3)), α.length ≤ m → α.length ≤ m' →
      ∀ t ∈ Icc (t₀ + δ) t₁, Zl m i t α =ᵐ[volume] Zl m' i t α := by
    intro m m' i α h1 h2
    have hm : α.length ≤ max m 1 := h1.trans (le_max_left _ _)
    have hm' : α.length ≤ max m' 1 := h2.trans (le_max_left _ _)
    refine lps_curves_eq_of_ae_eq hδT (f := fun t => Zl m i t α) (g := fun t => Zl m' i t α)
      ?_ ?_ (fun t ht => hcont m i α h1 t ht) (fun t ht => hcont m' i α h2 t ht) ?_
    · intro t ht
      have := (hfam m i t ht).memL2 α h1
      rwa [Measure.restrict_univ] at this
    · intro t ht
      have := (hfam m' i t ht).memL2 α h2
      rwa [Measure.restrict_univ] at this
    · have e3 := lps_ae_slices_univ (hDD m m' i α hm hm')
      filter_upwards [hS m, hS m', e3] with t e1 e2 e3
      exact (e1 i α hm).trans (e3.trans (e2 i α hm').symm)
  have hae : ∀ᵐ t ∂(volume.restrict (Ioo (t₀ + δ) t₁)), ∀ i : Fin 3,
      Zl 0 i t [] =ᵐ[volume] fun x => U (x, t) i := by
    have h0 : ∀ i, ∀ᵐ t ∂(volume.restrict (Ioo (t₀ + δ) t₁)),
        (fun x => DDl 0 i [] (x, t)) =ᵐ[volume] fun x => U (x, t) i :=
      fun i => lps_ae_slices_univ (hD 0 i).zero
    filter_upwards [hS 0, ae_all_iff.2 h0] with t e1 e2 i
    exact (e1 i [] (by simp)).trans (e2 i)
  have hIcc : Icc (t₀ + δ) t₁ ⊆ Icc t₀ t₁ := Icc_subset_Icc (by linarith only [hδ]) le_rfl
  have hslice : ∀ t ∈ Icc t₀ t₁, MemLp (fun x : Vec3 => U (x, t)) 2 volume :=
    fun t ht => (lps_strong_solution_slice_memLp_two h ht).1
  have hcontU : ∀ t ∈ Icc t₀ t₁, Tendsto
      (fun s : ℝ => eLpNorm (fun x : Vec3 => U (x, s) - U (x, t)) 2 volume)
      (𝓝[Icc t₀ t₁] t) (𝓝 0) := fun t ht => (h.2.2.1 t ht).1
  have hEq : ∀ i, ∀ t ∈ Icc (t₀ + δ) t₁, Zl 0 i t [] =ᵐ[volume] fun x => U (x, t) i := by
    intro i
    refine lps_curves_eq_of_ae_eq hδT (f := fun t => Zl 0 i t [])
      (g := fun t x => U (x, t) i) ?_ ?_ (fun t ht => hcont 0 i [] (by simp) t ht) ?_ ?_
    · intro t ht
      have := (hfam 0 i t ht).memL2 [] (by simp)
      rwa [Measure.restrict_univ] at this
    · intro t ht
      exact (hslice t (hIcc ht)).eval i
    · intro t ht
      have h1 := (hcontU t (hIcc ht)).mono_left (nhdsWithin_mono t hIcc)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1
        (Eventually.of_forall fun _ => bot_le)
        (eventually_nhdsWithin_of_forall fun s hs => eLpNorm_mono
          (((hslice s (hIcc hs)).eval i).aestronglyMeasurable.sub
            ((hslice t (hIcc ht)).eval i).aestronglyMeasurable) fun x => ?_)
      simpa [Pi.sub_apply] using norm_le_pi_norm (U (x, s) - U (x, t)) i
    · filter_upwards [hae] with t ht using ht i
  have htw : ∀ (i : Fin 3) (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∀ s t, t₀ + δ ≤ s → s ≤ t → t ≤ t₁ →
        (∫ x, Zl 0 i t [] x * ψ x) - ∫ x, Zl 0 i s [] x * ψ x =
          ∫ τ in s..t, ∫ x, Dtu (x, τ) i * ψ x := by
    intro i ψ hψ hψc s t hs hst ht
    have key := lps_slice_pairing_sub_eq_integral h.1 hu hDtu
      (fun i' φ hφ => (hderiv.2.2.2.2 φ hφ).2.2 i') hslice hcontU hψ hψc i
      (hs := by linarith only [hs, hδ]) hst ht
    have e1 : ∫ x, Zl 0 i t [] x * ψ x = ∫ x, U (x, t) i * ψ x :=
      integral_congr_ae ((hEq i t ⟨hs.trans hst, ht⟩).mono fun x hx => by simp only [hx])
    have e2 : ∫ x, Zl 0 i s [] x * ψ x = ∫ x, U (x, s) i * ψ x :=
      integral_congr_ae ((hEq i s ⟨hs, hst.trans ht⟩).mono fun x hx => by simp only [hx])
    rw [e1, e2]
    exact key
  have hequ : ∀ᵐ τ ∂(volume.restrict (Ioo (t₀ + δ) t₁)), ∀ (i : Fin 3)
      (hg : ∀ i' : Fin 3, MemLp (fun x => ∑ j, Zl 1 j τ [] x * Zl 1 i' τ [j] x) 2 volume),
      (fun x => Dtu (x, τ) i) =ᵐ[volume] fun x =>
        (∑ k, Zl 2 i τ [k, k] x) -
          lpsLerayApply (fun i' x => ∑ j, Zl 1 j τ [] x * Zl 1 i' τ [j] x) hg i x := by
    have hsub : Ioo (t₀ + δ) t₁ ⊆ Ioo t₀ t₁ := Ioo_subset_Ioo (by linarith only [hδ]) le_rfl
    have p1 := ae_restrict_of_ae_restrict_of_subset hsub
      (lps_strong_slice_projected_equation h hderiv hu hDu hD2u hDtu)
    have p2 := ae_restrict_of_ae_restrict_of_subset hsub
      (lps_strong_good_slices h hderiv hu hDu hD2u hDtu)
    have s2 : ∀ᵐ τ ∂(volume.restrict (Ioo (t₀ + δ) t₁)), ∀ i k,
        (fun x => DDl 2 i [k, k] (x, τ)) =ᵐ[volume] fun x => D2u (x, τ) i k k := by
      rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro k
      exact lps_ae_slices_univ (hD2E 2 i k)
    have s1 : ∀ᵐ τ ∂(volume.restrict (Ioo (t₀ + δ) t₁)), ∀ i k,
        (fun x => DDl 1 i [k] (x, τ)) =ᵐ[volume] fun x => DU (x, τ) i k := by
      rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro k
      exact lps_ae_slices_univ (hDuE 1 i k)
    have s0 : ∀ᵐ τ ∂(volume.restrict (Ioo (t₀ + δ) t₁)), ∀ i,
        (fun x => DDl 1 i [] (x, τ)) =ᵐ[volume] fun x => U (x, τ) i := by
      rw [ae_all_iff]; intro i
      exact lps_ae_slices_univ (hD 1 i).zero
    filter_upwards [p1, p2, s2, s1, s0, hS 1, hS 2, ae_restrict_mem measurableSet_Ioo]
      with τ e1 e2 e3 e4 e5 e6 e7 hτI
    intro i hg
    obtain ⟨-, hD2s, hgrad, -⟩ := e2
    have hτ : τ ∈ Icc t₀ t₁ := ⟨by linarith only [hτI.1, hδ], hτI.2.le⟩
    obtain ⟨hu2t, hDu2t⟩ := lps_strong_solution_slice_memLp_two h hτ
    have hH1t := (lps_strong_solution_slice_h1 h hτ).2.2
    have hg'2 : ∀ i', MemLp (fun y => ∑ j, U (y, τ) j * DU (y, τ) i' j) 2 volume := fun i' =>
      lps_h1_convection_memLp_two (u := fun x => U (x, τ)) (Du := fun x => DU (x, τ))
        (D2u := fun x => D2u (x, τ)) hu2t hDu2t hD2s hH1t hgrad i'
    have eZ0 : ∀ j, Zl 1 j τ [] =ᵐ[volume] fun x => U (x, τ) j :=
      fun j => (e6 j [] (by simp)).trans (e5 j)
    have eZ1 : ∀ i' j, Zl 1 i' τ [j] =ᵐ[volume] fun x => DU (x, τ) i' j :=
      fun i' j => (e6 i' [j] (by simp)).trans (e4 i' j)
    have eZ2 : ∀ k, Zl 2 i τ [k, k] =ᵐ[volume] fun x => D2u (x, τ) i k k :=
      fun k => (e7 i [k, k] (by simp)).trans (e3 i k)
    have hgg : ∀ i', (fun y => ∑ j, U (y, τ) j * DU (y, τ) i' j) =ᵐ[volume]
        fun y => ∑ j, Zl 1 j τ [] y * Zl 1 i' τ [j] y := by
      intro i'
      filter_upwards [ae_all_iff.2 eZ0, ae_all_iff.2 fun j => eZ1 i' j] with y h0 h1'
      exact Finset.sum_congr rfl fun j _ => by rw [h0 j, h1' j]
    have hLc := lpsLerayApply_congr_ae hg'2 hg hgg i
    filter_upwards [e1 i hg'2, ae_all_iff.2 eZ2, hLc] with x hx h2 h3
    have hs : ∑ k, Zl 2 i τ [k, k] x = ∑ j, D2u (x, τ) i j j :=
      Finset.sum_congr rfl fun k _ => h2 k
    rw [hs]
    linarith only [hx, h3]
  exact lps_time_chain hδT Zl hfam hcont hcons hae htw hequ

/-- `prop:lps-smoothing`, given the regularity ladder: a strong solution on `[t₀, t₁]` has a
representative that is `C^∞` on `ℝ³ × (t₀, t₁]`. -/
theorem lps_smoothing_of_ladder {t₀ t₁ : ℝ} {U : ParabolicPoint → Vec3}
    {DU : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtu : ParabolicPoint → Vec3}
    (h : IsLpsStrongSolution t₀ t₁ U DU p)
    (hderiv : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ t₁) U DU D2u Dtu)
    (hu : MemLp U 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))))
    (hDu : MemLp DU 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))))
    (hD2u : MemLp D2u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))))
    (hDtu : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))))
    (hlad : ∀ M : ℕ, 1 ≤ M → ∀ δ : ℝ, 0 < δ → t₀ + δ < t₁ →
      ∃ (Z : Fin 3 → ℝ → List (Fin 3) → Vec3 → ℝ)
        (DD : Fin 3 → List (Fin 3) → Vec3 × ℝ → ℝ),
        (∀ i, ∀ t ∈ Icc (t₀ + δ) t₁, IsSobolevFamilyOn M univ (Z i t []) (Z i t)) ∧
        (∀ i α, α.length ≤ M → ∀ t ∈ Icc (t₀ + δ) t₁,
          Tendsto (fun s => eLpNorm (Z i s α - Z i t α) 2 volume) (𝓝[Icc (t₀ + δ) t₁] t)
            (𝓝 0)) ∧
        (∀ᵐ t ∂(volume.restrict (Ioo (t₀ + δ) t₁)), ∀ i, ∀ α, α.length ≤ M →
          Z i t α =ᵐ[volume] fun x => DD i α (x, t)) ∧
        (∀ i, IsL2SobolevFamilyOn (M + 1) univ (Ioo (t₀ + δ) t₁) (fun z => U z i) (DD i)) ∧
        (∀ i k, DD i [k] =ᵐ[volume.restrict (spaceTimeSet univ (Ioo (t₀ + δ) t₁))]
          fun z => DU z i k) ∧
        (∀ i k, DD i [k, k] =ᵐ[volume.restrict (spaceTimeSet univ (Ioo (t₀ + δ) t₁))]
          fun z => D2u z i k k)) :
    ∃ R : ParabolicPoint → Vec3,
      R =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))] U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => R z)
        ((Set.univ : Set Vec3) ×ˢ Ioc t₀ t₁) :=
  lps_smoothing_of_curves h.1 (fun i => (hu.eval i).aestronglyMeasurable)
    fun δ hδ hδT => lps_smoothing_data_of_ladder hδ hδT h hderiv hu hDu hD2u hDtu
      fun M hM => hlad M hM δ hδ hδT

end ESS
