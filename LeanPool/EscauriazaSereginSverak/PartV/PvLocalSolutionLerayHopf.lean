/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.PvLocalSolutionLerayHopfClauses
public import LeanPool.EscauriazaSereginSverak.PartV.PvLocalSolutionClauses
public import LeanPool.EscauriazaSereginSverak.PartV.HeatOrbitStrongContinuity

/-!
# The short-time Leray–Hopf solution

`prop:pv-local-solution`, from the strong `L²` and `L³` continuity of the forced
heat response: for every divergence-free datum `a ∈ L² ∩ L³` there are `τ > 0` and
a Leray–Hopf solution `(U, DU)` on `ℝ³ × [0, τ]` with datum `a`, lying in
`L⁵ ∩ L⁴` of the slab, with `U(t) → a` strongly in `L³` as `t ↓ 0`, and whose
associated pressure `P[U ⊗ U]` (the canonical double Riesz transform of
`def:riesz-pressure`, cut off to the slab) lies in `L² ∩ L^{5/2}` of the slab and
satisfies the momentum equation with `U`.

The solution is the Duhamel fixed point `U = S(t)a + Z`, `Z` the forced heat
response of `-(U ⊗ U + P[U ⊗ U] I)`. Its slices are continuous into `L²` and `L³`
on `[0, τ]`: the heat flow is strongly continuous there, and so is `Z`, with
`Z(0) = 0`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A function vanishing at `0` and tending to `0` from the right tends to `0`
within `[0, σ]`. -/
theorem pvLS_tendsto_Icc_zero {σ : ℝ} {g : ℝ → ℝ≥0∞} (hg0 : g 0 = 0)
    (hg : Tendsto g (𝓝[>] 0) (𝓝 0)) : Tendsto g (𝓝[Icc 0 σ] 0) (𝓝 0) := by
  have hsub : Icc 0 σ ⊆ insert 0 (Ioi 0) := fun s hs => by
    rcases eq_or_lt_of_le hs.1 with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  refine Tendsto.mono_left ?_ (nhdsWithin_mono _ hsub)
  rw [nhdsWithin_insert]
  refine tendsto_sup.2 ⟨?_, hg⟩
  rw [← hg0]
  exact tendsto_pure_nhds g 0

/-- `prop:pv-local-solution`, from the strong continuity of the forced heat
response. -/
theorem pvLocalSolution_lerayHopf_of_strongContinuity
    (hA : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ∀ G : Fin 3 → Fin 3 → ParabolicPoint → ℝ,
      (∀ i j, MemLp (G i j) (ENNReal.ofReal (5 / 2)) volume) →
      (∀ i j, MemLp (G i j) 2 volume) →
      (∀ i j z, z ∉ CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) → G i j z = 0) →
      (∀ t ∈ Icc 0 τ,
        MemLp (fun x : Vec3 => forcedHeat G (x, t)) 2 volume ∧
        MemLp (fun x : Vec3 => forcedHeat G (x, t)) 3 volume ∧
        eLpNorm (fun x : Vec3 => forcedHeat G (x, t)) 2 volume ≤
          ENNReal.ofReal C * eLpNorm (fun z => fun i j => G i j z) 2
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
        eLpNorm (fun x : Vec3 => forcedHeat G (x, t)) 3 volume ≤
          ENNReal.ofReal C * eLpNorm (fun z => fun i j => G i j z) (ENNReal.ofReal (5 / 2))
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) ∧
      (∀ t ∈ Icc 0 τ, Tendsto (fun s => eLpNorm (fun x : Vec3 =>
          forcedHeat G (x, s) - forcedHeat G (x, t)) 2 volume) (𝓝[Icc 0 τ] t) (𝓝 0)) ∧
      (∀ t ∈ Icc 0 τ, Tendsto (fun s => eLpNorm (fun x : Vec3 =>
          forcedHeat G (x, s) - forcedHeat G (x, t)) 3 volume) (𝓝[Icc 0 τ] t) (𝓝 0)))
    {a : Vec3 → Vec3} (ha : IsInJ a) (ha3 : MemLp a (ENNReal.ofReal 3) volume) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ U : ParabolicPoint → Vec3, ∃ DU : ParabolicPoint → Fin 3 → Vec3,
      IsLerayHopfSolution τ a U DU ∧
      MemLp U (ENNReal.ofReal 5) (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
      MemLp U (ENNReal.ofReal 4) (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
      Tendsto (fun t => eLpNorm (fun x : Vec3 => U (x, t) - a x) (ENNReal.ofReal 3) volume)
        (𝓝[>] 0) (𝓝 0) ∧
      IsSerrinWeakSolution τ a U DU (pvSlabPressure τ U) ∧
      MemLp (pvSlabPressure τ U) (ENNReal.ofReal 2)
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
      MemLp (pvSlabPressure τ U) (ENNReal.ofReal (5 / 2))
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) := by
  have e2 : ENNReal.ofReal 2 = 2 := by simp
  have e3 : ENNReal.ofReal 3 = 3 := by simp
  have ha2' : MemLp a (ENNReal.ofReal 2) volume := by
    rw [e2]
    exact ha.1
  have ha3' : MemLp a 3 volume := by
    rw [← e3]
    exact ha3
  obtain ⟨σ, hσ, U, hU5, hU4, hfix, hinit⟩ := pvLocal_fixedPoint ha.1 ha3'
  obtain ⟨DU, hS⟩ := pvLocalClauses_bundle ha hσ hU5 hU4 hfix hinit
  set G := pvSlabForce σ U with hGdef
  have hG52 (i j : Fin 3) := (pvSlabForce_memLp_both hU5 hU4 i j).1
  have hG2 (i j : Fin 3) := (pvSlabForce_memLp_both hU5 hU4 i j).2
  have hGsupp (i j : Fin 3) (z : ParabolicPoint)
      (hz : z ∉ spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ)) : G i j z = 0 :=
    pvSlabForce_eq_zero hz i j
  obtain ⟨CA, -, hA'⟩ := hA
  obtain ⟨hevery, hc2, hc3⟩ := hA' σ hσ G hG52 hG2 hGsupp
  have hGpos : ∀ i j (p : ParabolicPoint), G i j p ≠ 0 → 0 < p.2 := fun i j p hp => by
    by_contra hneg
    exact hp (hGsupp i j p fun h => hneg h.2.1)
  have hZ0 (x : Vec3) : forcedHeat G (x, 0) = 0 := forcedHeat_eq_zero_of_nonpos hGpos le_rfl
  have hUeq (x : Vec3) (t : ℝ) (ht : 0 < t) :
      U (x, t) = heatConvVec3 t a x + forcedHeat G (x, t) := hfix (x, t) ht.ne'
  -- the heat part `H(s) = U(s) - Z(s)`
  set H : ℝ → Vec3 → Vec3 := fun s x => U (x, s) - forcedHeat G (x, s) with hHdef
  have hHpos (s : ℝ) (hs : 0 < s) : H s = heatConvVec3 s a := by
    funext x
    simp only [hHdef, hUeq x s hs, add_sub_cancel_right]
  have hH0 : H 0 = a := by
    funext x
    simp only [hHdef, hinit x, hZ0 x, sub_zero]
  have hHcont (p : ℝ) (hp : 2 ≤ p) (hap : MemLp a (ENNReal.ofReal p) volume) (t : ℝ)
      (ht : t ∈ Icc 0 σ) :
      Tendsto (fun s => eLpNorm (fun x => H s x - H t x) (ENNReal.ofReal p) volume)
        (𝓝[Icc 0 σ] t) (𝓝 0) := by
    rcases eq_or_lt_of_le ht.1 with h0 | hpos
    · subst h0
      refine pvLS_tendsto_Icc_zero (by simp) ?_
      refine (heatConvVec3_tendsto_self hp hap).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [hHpos s hs, hH0]
    · refine ((heatConvVec3_tendsto_pos hp hap hpos).mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds hpos)] with s hs
      rw [hHpos s hs, hHpos t hpos]
  have hsplit (p : ℝ≥0∞) (hp : 1 ≤ p) (s t : ℝ) :
      eLpNorm (fun x : Vec3 => U (x, s) - U (x, t)) p volume ≤
        eLpNorm (fun x => H s x - H t x) p volume +
          eLpNorm (fun x : Vec3 => forcedHeat G (x, s) - forcedHeat G (x, t)) p volume := by
    have hpt : (fun x : Vec3 => U (x, s) - U (x, t)) =
        (fun x => H s x - H t x) + fun x : Vec3 => forcedHeat G (x, s) - forcedHeat G (x, t) := by
      funext x
      simp only [hHdef, Pi.add_apply]
      abel
    rw [hpt]
    exact eLpNorm_add_le hp
  have hmem2 (t : ℝ) (ht : t ∈ Icc 0 σ) : MemLp (fun x : Vec3 => U (x, t)) 2 volume := by
    rcases eq_or_lt_of_le ht.1 with h0 | hpos
    · subst h0
      simpa only [hinit] using ha.1
    · have hh := heatConvVec3_memLp (p := 2) (by norm_num) hpos ha2'
      rw [e2] at hh
      have h := hh.add (hevery t ht).1
      have hpt : (fun x : Vec3 => U (x, t)) =
          heatConvVec3 t a + fun x : Vec3 => forcedHeat G (x, t) := by
        funext x
        rw [Pi.add_apply, hUeq x t hpos]
      rw [hpt]
      exact h
  have hcont2 (t : ℝ) (ht : t ∈ Icc 0 σ) :
      Tendsto (fun s => eLpNorm (fun x : Vec3 => U (x, s) - U (x, t)) 2 volume)
        (𝓝[Icc 0 σ] t) (𝓝 0) := by
    have hH := hHcont 2 le_rfl ha2' t ht
    rw [e2] at hH
    have hsum := hH.add (hc2 t ht)
    rw [add_zero] at hsum
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => bot_le) fun s => hsplit 2 one_le_two s t
  have hLH := pvLH_lerayHopf_of_strongL2 hσ ha hS hU5 hmem2 hcont2 hinit
  -- the strong `L³` trace
  have hL3 : Tendsto (fun t => eLpNorm (fun x : Vec3 => U (x, t) - a x) (ENNReal.ofReal 3) volume)
      (𝓝[>] 0) (𝓝 0) := by
    have hnear : Icc 0 σ ∈ 𝓝[>] (0 : ℝ) :=
      mem_of_superset (Ioo_mem_nhdsGT hσ) Ioo_subset_Icc_self
    have hH := (hHcont 3 (by norm_num) ha3 0 (left_mem_Icc.2 hσ.le)).mono_left
      (nhdsWithin_le_of_mem hnear)
    have hZ := (hc3 0 (left_mem_Icc.2 hσ.le)).mono_left (nhdsWithin_le_of_mem hnear)
    rw [← e3] at hZ
    have hsum := hH.add hZ
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => bot_le) fun s => ?_
    have h := hsplit (ENNReal.ofReal 3) (by rw [e3]; norm_num) s 0
    have hpt : (fun x : Vec3 => U (x, s) - U (x, 0)) = fun x : Vec3 => U (x, s) - a x := by
      funext x
      rw [hinit x]
    rw [hpt] at h
    exact h
  -- the pressure
  have hT2 : ∀ i j, MemLp (pvSlabTensor σ U U i j) (ENNReal.ofReal 2) volume :=
    fun i j => (pvSlabTensor_memLp_both hU5 hU4 i j).2
  have hT52 : ∀ i j, MemLp (pvSlabTensor σ U U i j) (ENNReal.ofReal (5 / 2)) volume :=
    fun i j => (pvSlabTensor_memLp_both hU5 hU4 i j).1
  exact ⟨σ, hσ, U, DU, hLH, hU5, hU4, hL3, hS,
    (pvSlabPressure_memLp (by norm_num) hT2 hT2).restrict _,
    (pvSlabPressure_memLp (by norm_num) hT2 hT52).restrict _⟩

end ESS

end
