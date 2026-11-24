/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutSimilar
import Mathlib.Topology.LocalAtTarget

/-!
# Parallel arcs

We prove `ParallelArcsStatement` (`parallelArcs`). Let `α` map `F` to `F'`, fix the two ends, and
keep the orientation of each
cuff. Cut `S` along `F'`. We look for a homeomorphism of the cut surface that fixes the two lifts of
`F'` and that covers `α` on
the rest of the boundary. It then descends to a homeomorphism `γ` of `S` that fixes `F'` and agrees
with `α` on `bd S`, and
`γ⁻¹ ∘ α` is the map we want.

Such a homeomorphism is built one cuff at a time with `exists_move_loop`. On a cuff of the cut
surface we need an increasing map
`τ` of the parameter. Over the lifts of `F'` it is the identity. On a gap between lifts, `α` acts on
a part of a cuff of `S`
by an increasing map `l`, and `τ` is `l` read in the parameter of the cut surface. The two
parameters are related by a monotone
map `k`, so `τ = k⁻¹ ∘ l ∘ k` is increasing whichever way `k` runs. The ends of a gap lie over the
fixed points `s` and `t`, so
`l` maps the gap onto itself. An increasing map onto an interval is continuous, so no limits are
needed at the ends of a gap.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Function

universe u

/-- A circle can be parametrized to start at a given point. -/
theorem exists_based {T : Type*} [TopologicalSpace T] {C : Set T} (φ₀ : Circle ≃ₜ C) {b : T}
  (hb : b ∈ C) :
    ∃ φ : Circle ≃ₜ C, (φ (ee 0)).1 = b := by
  refine ⟨(Homeomorph.mulLeft (φ₀.symm ⟨b, hb⟩)).trans φ₀, ?_⟩
  have e : ee 0 = 1 := by simp [ee]
  simp [e]

/-- Every point of the circle has a parameter in `[0, 1)`. -/
theorem exists_param (c : Circle) : ∃ u ∈ Ico (0 : ℝ) 1, ee u = c := by
  obtain ⟨x, rfl⟩ := ee_surjective c
  refine ⟨Int.fract x, ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩, ee_eq_iff.mpr ⟨-⌊x⌋, ?_⟩⟩
  rw [Int.fract]
  push_cast
  ring

/-- A map with null signature that fixes a point of a cuff has an increasing lift that fixes `0` and
`1`. -/
theorem exists_null_lift {S : Type u} [TopologicalSpace S] {α : S ≃ₜ S}
  (hα : HasNullSignature α) {D : Set S} (hD : D ∈ cuffs S)
    (hO : IsOArc D) {b : S} (hb : b ∈ D) (hab : α b = b) :
    ∃ (φ : Circle ≃ₜ D) (l : ℝ → ℝ), (φ (ee 0)).1 = b ∧ Continuous l ∧ StrictMono l ∧ l 0 = 0 ∧ l 1
      = 1 ∧
      ∀ u, α (φ (ee u)).1 = (φ (ee (l u))).1 := by
  obtain ⟨φ₀⟩ := id hO
  obtain ⟨φ, h0⟩ := exists_based φ₀ hb
  obtain ⟨h, ⟨l₀, c₀, m₀, hl⟩, hh⟩ := hα D φ hD
  have hpi := Real.pi_pos
  have e1 : ∀ u, h (ee u) = ee (l₀ (2 * Real.pi * u) / (2 * Real.pi)) := fun u => by
    have e2 : 2 * Real.pi * (l₀ (2 * Real.pi * u) / (2 * Real.pi)) = l₀ (2 * Real.pi * u) := by
      field_simp
    simp only [ee]
    rw [e2, hl]
  have e0 : h (ee 0) = ee 0 := by
    have h3 := hh (ee 0)
    rw [h0, hab] at h3
    exact φ.injective (Subtype.ext (h3.symm.trans h0.symm))
  set l₁ : ℝ → ℝ := fun u => l₀ (2 * Real.pi * u) / (2 * Real.pi) with hl₁
  have c₁ : Continuous l₁ := by
    simp only [hl₁]
    exact (c₀.comp (continuous_const.mul continuous_id)).div_const _
  have m₁ : StrictMono l₁ := fun x y hxy => by
    simp only [hl₁]
    exact div_lt_div_of_pos_right (m₀ (mul_lt_mul_of_pos_left hxy (by positivity))) (by positivity)
  obtain ⟨m, hm⟩ := ee_eq_iff.mp ((e1 0).symm.trans e0)
  have hz : l₁ 0 = m := by
    rw [zero_add] at hm
    exact hm
  set l : ℝ → ℝ := fun u => l₁ u - m with hl'
  have c' : Continuous l := c₁.sub continuous_const
  have m' : StrictMono l := fun x y hxy => sub_lt_sub_right (m₁ hxy) _
  have e3 : ∀ u, h (ee u) = ee (l u) := fun u => by
    rw [e1]
    exact ee_eq_iff.mpr ⟨m, by simp [hl', hl₁]⟩
  have l0 : l 0 = 0 := by simp only [hl']; rw [hz]; ring
  have e4 : ee (l 1) = ee 0 := by rw [← e3, ee_one, e0]
  obtain ⟨n, hn⟩ := ee_eq_iff.mp e4
  have hn0 : l 1 = n := by simpa using hn
  have hpos : (0 : ℝ) < n := by
    rw [← hn0, ← l0]
    exact m' zero_lt_one
  have hn1 : 1 ≤ n := by exact_mod_cast hpos
  have hn2 : n = 1 := by
    by_contra hne
    have hn3 : 2 ≤ n := by omega
    have hn4 : (2 : ℝ) ≤ n := by exact_mod_cast hn3
    obtain ⟨x, hx, hx1⟩ := intermediate_value_Ioo zero_le_one c'.continuousOn (show (1 : ℝ) ∈ Ioo
      (l 0) (l 1) by
      rw [l0, hn0]
      constructor <;> linarith)
    have e5 : h (ee x) = h (ee 0) := by rw [e3, hx1, ee_one, e0]
    obtain ⟨r, hr⟩ := ee_eq_iff.mp (h.injective e5)
    have h1 : (0 : ℝ) < r := by linarith [hx.1]
    have h2 : (r : ℝ) < 1 := by linarith [hx.2]
    have h3 : 0 < r := by exact_mod_cast h1
    have h4 : r < 1 := by exact_mod_cast h2
    omega
  refine ⟨φ, l, h0, c', m', l0, by rw [hn0, hn2]; simp, fun u => ?_⟩
  rw [hh, e3]

/-- A point of `[0, 1]` that keeps its class modulo one under an increasing map fixing `0` and `1`
is fixed. -/
theorem fix_of {l : ℝ → ℝ} (hm : StrictMono l) (l0 : l 0 = 0) (l1 : l 1 = 1) {v : ℝ} (hv : v ∈ Icc
  (0 : ℝ) 1) (he : ee (l v) = ee v) :
    l v = v := by
  rcases eq_or_lt_of_le hv.1 with rfl | h1
  · exact l0
  rcases eq_or_lt_of_le hv.2 with rfl | h2
  · exact l1
  have h3 : 0 < l v := by rw [← l0]; exact hm h1
  have h4 : l v < 1 := by rw [← l1]; exact hm h2
  obtain ⟨r, hr⟩ := ee_eq_iff.mp he
  have h5 : (r : ℝ) < 1 := by linarith
  have h6 : (-1 : ℝ) < r := by linarith
  have h7 : r < 1 := by exact_mod_cast h5
  have h8 : -1 < r := by exact_mod_cast h6
  have h9 : r = 0 := by omega
  rw [hr, h9]
  simp

/-- Conjugating an increasing map of an interval by a monotone map gives an increasing map. -/
theorem gap_conj {k l : ℝ → ℝ} {p q a b : ℝ} (hab : a < b) (hk : StrictMonoOn k (Icc p q)
  ∨ StrictAntiOn k (Icc p q))
    (hc : ContinuousOn k (Icc p q)) (hpq : p < q) (he : (k p = a ∧ k q = b) ∨ (k p = b ∧ k q = a))
      (cl : Continuous l) (ml : StrictMono l)
    (la : l a = a) (lb : l b = b) :
    ∃ τ : ℝ → ℝ, (∀ u ∈ Ioo p q, τ u ∈ Ioo p q ∧ k (τ u) = l (k u)) ∧ StrictMonoOn τ (Ioo p q)
      ∧ Ioo p q ⊆ τ '' Ioo p q := by
  have mp : p ∈ Icc p q := left_mem_Icc.mpr hpq.le
  have mq : q ∈ Icc p q := right_mem_Icc.mpr hpq.le
  have hI : ∀ {u}, u ∈ Ioo p q → u ∈ Icc p q := fun hu => Ioo_subset_Icc_self hu
  have mem : ∀ u ∈ Ioo p q, k u ∈ Ioo a b := by
    intro u hu
    rcases hk with hk | hk <;> rcases he with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨e1 ▸ hk mp (hI hu) hu.1, e2 ▸ hk (hI hu) mq hu.2⟩
    · have := hk mp mq hpq
      linarith
    · have := hk mp mq hpq
      linarith
    · exact ⟨e2 ▸ hk (hI hu) mq hu.2, e1 ▸ hk mp (hI hu) hu.1⟩
  have sur : ∀ v ∈ Ioo a b, ∃ u ∈ Ioo p q, k u = v := by
    intro v hv
    have h1 : v ∈ uIcc (k p) (k q) := by
      rcases he with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
      · exact Ioo_subset_Icc_self hv |> fun h => by rwa [uIcc_of_le hab.le]
      · exact Ioo_subset_Icc_self hv |> fun h => by rwa [uIcc_of_ge hab.le]
    have h2 : uIcc p q = Icc p q := uIcc_of_le hpq.le
    obtain ⟨u, hu, rfl⟩ := intermediate_value_uIcc (h2 ▸ hc) h1
    rw [h2] at hu
    have h3 : u ≠ p := by
      rintro rfl
      rcases he with ⟨e1, -⟩ | ⟨e1, -⟩ <;> rw [e1] at hv <;> simp at hv
    have h4 : u ≠ q := by
      rintro rfl
      rcases he with ⟨-, e1⟩ | ⟨-, e1⟩ <;> rw [e1] at hv <;> simp at hv
    exact ⟨u, ⟨lt_of_le_of_ne hu.1 h3.symm, lt_of_le_of_ne hu.2 h4⟩, rfl⟩
  have hl : ∀ x ∈ Ioo a b, l x ∈ Ioo a b := fun x hx => ⟨la ▸ ml hx.1, lb ▸ ml hx.2⟩
  have ex : ∀ u ∈ Ioo p q, ∃ w ∈ Ioo p q, k w = l (k u) := fun u hu => sur _ (hl _ (mem u hu))
  choose! τ h1 h2 using ex
  have hinj : InjOn k (Icc p q) := hk.elim StrictMonoOn.injOn StrictAntiOn.injOn
  refine ⟨τ, fun u hu => ⟨h1 u hu, h2 u hu⟩, ?_, ?_⟩
  · intro u hu v hv huv
    rcases hk with hk | hk
    · have h3 := ml (hk (hI hu) (hI hv) huv)
      rw [← h2 u hu, ← h2 v hv] at h3
      exact (StrictMonoOn.lt_iff_lt hk (hI (h1 u hu)) (hI (h1 v hv))).mp h3
    · have h3 := ml (hk (hI hu) (hI hv) huv)
      rw [← h2 u hu, ← h2 v hv] at h3
      exact (StrictAntiOn.lt_iff_gt hk (hI (h1 v hv)) (hI (h1 u hu))).mp h3
  · intro v hv
    obtain ⟨x, hx, hx1⟩ := intermediate_value_Ioo hab.le cl.continuousOn (show k v ∈ Ioo (l a)
      (l b) by
      rw [la, lb]
      exact mem v hv)
    obtain ⟨u, hu, rfl⟩ := sur x hx
    exact ⟨u, hu, hinj (hI (h1 u hu)) (hI hv) ((h2 u hu).trans hx1)⟩

section cut

variable {Y S : Type u} [TopologicalSpace Y] [TopologicalSpace S] [T2Space S] {ψ : Y
  → S} {F : Set S} {α : S ≃ₜ S} {s t : S}

/-- A point off the lifts of `F` over the boundary of `S` is a boundary point of the cut surface. -/
theorem bd_lift [CompactSpace Y] (hψ : IsCutting ψ F) (hF : IsClosed F) {y : Y} (hy : ψ y ∈ bd S)
  (hyF : ψ y ∉ F) : y ∈ bd Y := by
  intro hi
  apply hy
  obtain ⟨h1, h2, h3, -, -⟩ := hψ
  have hO : IsOpen (ψ ⁻¹' F)ᶜ := (hF.preimage h1).isOpen_compl
  obtain ⟨U, hU, hx, hsub, ⟨e⟩⟩ := hi.exists_subset hO hyF
  have hcl : IsClosedMap ψ := h1.isClosedMap
  have hq : IsQuotientMap ψ := hcl.isQuotientMap h1 h2
  have he : ψ ⁻¹' (ψ '' U) = U := by
    apply subset_antisymm
    · rintro a ⟨b, hb, hab⟩
      have hb' : ψ b ∉ F := hsub hb
      have ha' : ψ a ∉ F := hab ▸ hb'
      rwa [h3 ha' hb' hab.symm]
    · exact subset_preimage_image ψ U
  have hV : IsOpen (ψ '' U) := by
    rw [← hq.isOpen_preimage, he]
    exact hU
  have hbij : Bijective ((ψ '' U).restrictPreimage ψ) := by
    constructor
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ he'
      have he2 : ψ a = ψ b := congrArg Subtype.val he'
      have ha' : a ∈ U := he ▸ ha
      have hb' : b ∈ U := he ▸ hb
      exact Subtype.ext (h3 (hsub ha') (hsub hb') he2)
    · rintro ⟨w, hw⟩
      obtain ⟨y', rfl⟩ := h2 w
      exact ⟨⟨y', hw⟩, rfl⟩
  have hh : IsHomeomorph ((ψ '' U).restrictPreimage ψ) :=
    isHomeomorph_iff_continuous_isClosedMap_bijective.mpr ⟨h1.restrictPreimage,
      hcl.restrictPreimage _, hbij⟩
  exact ⟨ψ '' U, hV, mem_image_of_mem ψ hx, ⟨hh.homeomorph.symm.trans
    ((Homeomorph.setCongr he).trans e)⟩⟩

/-- `α` read on a gap between two lifts. -/
theorem exists_gap_map [CompactSpace Y] (hS : IsSurface S) (hψ : IsCutting ψ F)
  (hF : IsClosed F) (hb : F ∩ bd S = {s, t})
    (hα : HasNullSignature α) (hs : α s = s) (ht : α t = t) {T : ℝ → Y} (hT : Continuous T)
      (hTb : ∀ u, T u ∈ bd Y)
    {p q : ℝ} (hpq : p < q) (hTp : ψ (T p) ∈ F) (hTq : ψ (T q) ∈ F) (hgap : ∀ u ∈ Ioo p q, ψ
      (T u) ∉ F) (hinj : InjOn T (Ioo p q)) :
    ∃ τ : ℝ → ℝ, (∀ u ∈ Ioo p q, τ u ∈ Ioo p q ∧ ψ (T (τ u)) = α (ψ (T u))) ∧ StrictMonoOn τ
      (Ioo p q) ∧ Ioo p q ⊆ τ '' Ioo p q := by
  have hcuff := cuff_statement.{u} S hS
  have cc : Continuous fun u => ψ (T u) := hψ.1.comp hT
  have hcl : closure (Ioo p q) = Icc p q := closure_Ioo hpq.ne
  have hIcc : ∀ u ∈ Icc p q, ψ (T u) ∈ bd S := by
    intro u hu
    have h1 : ψ (T u) ∈ closure (bd S) :=
      map_mem_closure (f := fun u => ψ (T u)) (t := bd S) cc (hcl ▸ hu) fun x hx => bd_of_bd hψ hF
        (hTb x) (hgap x hx)
    rwa [hcuff.1.closure_eq] at h1
  have mp : p ∈ Icc p q := left_mem_Icc.mpr hpq.le
  have mq : q ∈ Icc p q := right_mem_Icc.mpr hpq.le
  have fx : ∀ x ∈ F, x ∈ bd S → α x = x := by
    intro x hx hx'
    have h1 : x ∈ ({s, t} : Set S) := hb ▸ ⟨hx, hx'⟩
    rcases h1 with rfl | h1
    · exact hs
    · rw [mem_singleton_iff.mp h1]
      exact ht
  set D := connectedComponentIn (bd S) (ψ (T p)) with hDdef
  have hD : D ∈ cuffs S := ⟨_, hIcc p mp, rfl⟩
  have hsub : (fun u => ψ (T u)) '' Icc p q ⊆ D :=
    (isPreconnected_Icc.image _ cc.continuousOn).subset_connectedComponentIn ⟨p, mp, rfl⟩ (by
      rintro _ ⟨u, hu, rfl⟩
      exact hIcc u hu)
  have hbD : ψ (T p) ∈ D := hsub ⟨p, mp, rfl⟩
  obtain ⟨φ, l, h0, cl, ml, l0, l1, hl⟩ := exists_null_lift hα hD (hcuff.2.2 D hD) hbD (fx _ hTp
    (hIcc p mp))
  have hne : q - p ≠ 0 := sub_ne_zero.mpr hpq.ne'
  have hp0 : 0 < q - p := sub_pos.mpr hpq
  have mem0 : ∀ v ∈ Icc (0 : ℝ) 1, p + v * (q - p) ∈ Icc p q := fun v hv => by
    constructor
    · nlinarith [hv.1]
    · nlinarith [hv.2]
  obtain ⟨m, cm, hm⟩ := exists_lift φ (η := fun v => ψ (T (p + v * (q - p)))) (cc.comp
    (continuous_const.add (continuous_id.mul continuous_const))).continuousOn (fun v hv
      => hsub ⟨_, mem0 v hv, rfl⟩)
  set θ : ℝ → S := fun x => (φ (ee x)).1 with hθ
  set k₀ : ℝ → ℝ := fun u => m ((u - p) / (q - p)) with hk₀
  have mem1 : ∀ u ∈ Icc p q, (u - p) / (q - p) ∈ Icc (0 : ℝ) 1 := fun u hu => by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hu.1) hp0.le
    · rw [div_le_one hp0]
      linarith [hu.2]
  have vk₀ : ∀ u ∈ Icc p q, θ (k₀ u) = ψ (T u) := fun u hu => by
    have h1 := hm _ (mem1 u hu)
    have h2 : p + (u - p) / (q - p) * (q - p) = u := by
      field_simp
      ring
    simp only [h2] at h1
    exact h1
  have ck₀ : ContinuousOn k₀ (Icc p q) := cm.comp (by fun_prop) mem1
  have θint : ∀ (x : ℝ) (n : ℤ), θ (x + n) = θ x := fun x n => by
    have h1 : ee (x + n) = ee x := ee_eq_iff.mpr ⟨n, rfl⟩
    simp only [hθ, h1]
  have θ0 : θ 0 = ψ (T p) := h0
  have θn : ∀ n : ℤ, θ n = ψ (T p) := fun n => by
    rw [← θ0, ← θint 0 n, zero_add]
  have hIoo : ∀ {u}, u ∈ Ioo p q → u ∈ Icc p q := fun hu => Ioo_subset_Icc_self hu
  have noint : ∀ u ∈ Ioo p q, ∀ n : ℤ, k₀ u ≠ n := fun u hu n he => by
    apply hgap u hu
    rw [← vk₀ u (hIoo hu), he, θn]
    exact hTp
  have hmid : (p + q) / 2 ∈ Ioo p q := ⟨by linarith, by linarith⟩
  set m₀ : ℤ := ⌊k₀ ((p + q) / 2)⌋ with hm₀
  have hm1 : (m₀ : ℝ) < k₀ ((p + q) / 2) := lt_of_le_of_ne (Int.floor_le _) (noint _ hmid m₀).symm
  have hm2 : k₀ ((p + q) / 2) < m₀ + 1 := Int.lt_floor_add_one _
  have pre : IsPreconnected (k₀ '' Ioo p q) := isPreconnected_Ioo.image _
    (ck₀.mono Ioo_subset_Icc_self)
  have hrange : ∀ u ∈ Ioo p q, k₀ u ∈ Ioo (m₀ : ℝ) (m₀ + 1) := by
    intro u hu
    constructor
    · by_contra hc
      obtain ⟨w, hw, hw1⟩ := pre.Icc_subset ⟨u, hu, rfl⟩ ⟨_, hmid, rfl⟩ ⟨not_lt.mp hc, hm1.le⟩
      exact noint w hw m₀ hw1
    · by_contra hc
      obtain ⟨w, hw, hw1⟩ := pre.Icc_subset ⟨_, hmid, rfl⟩ ⟨u, hu, rfl⟩ ⟨hm2.le, not_lt.mp hc⟩
      exact noint w hw (m₀ + 1) (by rw [hw1]; push_cast; rfl)
  set k : ℝ → ℝ := fun u => k₀ u - m₀ with hk
  have ck : ContinuousOn k (Icc p q) := ck₀.sub continuousOn_const
  have vk : ∀ u ∈ Icc p q, θ (k u) = ψ (T u) := fun u hu => by
    have h1 := θint (k u) m₀
    simp only [hk, sub_add_cancel] at h1
    rw [← vk₀ u hu]
    exact h1.symm
  have kIoo : ∀ u ∈ Ioo p q, k u ∈ Ioo (0 : ℝ) 1 := fun u hu => by
    have h1 := hrange u hu
    simp only [hk]
    constructor <;> linarith [h1.1, h1.2]
  have kIcc : ∀ u ∈ Icc p q, k u ∈ Icc (0 : ℝ) 1 := by
    have h1 : k '' Icc p q ⊆ Icc 0 1 := by
      rw [← hcl]
      refine (ContinuousOn.image_closure (hcl ▸ ck)).trans (closure_minimal ?_ isClosed_Icc)
      rintro _ ⟨u, hu, rfl⟩
      exact Ioo_subset_Icc_self (kIoo u hu)
    exact fun u hu => h1 ⟨u, hu, rfl⟩
  have kinj : InjOn k (Ioo p q) := fun u hu u' hu' he => by
    have h1 : ψ (T u) = ψ (T u') := by rw [← vk u (hIoo hu), ← vk u' (hIoo hu'), he]
    exact hinj hu hu' (hψ.2.2.1 (hgap u hu) (hgap u' hu') h1)
  have kend : ∀ e ∈ Icc p q, ψ (T e) ∈ F → ∀ u ∈ Ioo p q, k u ≠ k e := fun e he hF' u hu h => by
    apply hgap u hu
    rw [← vk u (hIoo hu), h, vk e he]
    exact hF'
  have knq : k p ≠ k q := by
    intro he
    have h1 : k ((p + q) / 2) ≠ k p := kend p mp hTp _ hmid
    set y := k ((p + q) / 2) with hy
    set v := (k p + y) / 2 with hv
    have hv1 : v ≠ k p := fun h => h1 (by linarith)
    have hv2 : v ≠ y := fun h => h1 (by linarith)
    have hv3 : v ∈ uIcc (k p) y := by
      rcases lt_or_gt_of_ne h1 with h | h
      · rw [uIcc_of_ge h.le]
        constructor <;> linarith
      · rw [uIcc_of_le h.le]
        constructor <;> linarith
    have h3 := hmid
    have s1 : uIcc p ((p + q) / 2) = Icc p ((p + q) / 2) := uIcc_of_le h3.1.le
    have s2 : uIcc ((p + q) / 2) q = Icc ((p + q) / 2) q := uIcc_of_le h3.2.le
    obtain ⟨u₁, hu₁, e₁⟩ := intermediate_value_uIcc (s1 ▸ ck.mono (Icc_subset_Icc_right h3.2.le))
      hv3
    obtain ⟨u₂, hu₂, e₂⟩ := intermediate_value_uIcc (s2 ▸ ck.mono (Icc_subset_Icc_left h3.1.le))
      (show v ∈ uIcc (k ((p + q) / 2)) (k q) by rw [← he, uIcc_comm]; exact hv3)
    rw [s1] at hu₁
    rw [s2] at hu₂
    have n1 : u₁ ≠ p := fun h => hv1 (by rw [← e₁, h])
    have n2 : u₁ ≠ (p + q) / 2 := fun h => hv2 (by rw [← e₁, h])
    have n3 : u₂ ≠ q := fun h => hv1 (by rw [← e₂, h, he])
    have n4 : u₂ ≠ (p + q) / 2 := fun h => hv2 (by rw [← e₂, h])
    have l1' : u₁ < (p + q) / 2 := lt_of_le_of_ne hu₁.2 n2
    have l2' : (p + q) / 2 < u₂ := lt_of_le_of_ne hu₂.1 n4.symm
    have := kinj (x₁ := u₁) (x₂ := u₂) ⟨lt_of_le_of_ne hu₁.1 n1.symm, by linarith⟩ ⟨by linarith,
      lt_of_le_of_ne hu₂.2 n3⟩ (e₁.trans e₂.symm)
    linarith
  have hsplit : ∀ u ∈ Icc p q, u = p ∨ u = q ∨ u ∈ Ioo p q := fun u hu => by
    rcases eq_or_lt_of_le hu.1 with h | h
    · exact .inl h.symm
    rcases eq_or_lt_of_le hu.2 with h' | h'
    · exact .inr (.inl h')
    exact .inr (.inr ⟨h, h'⟩)
  have kp := kend p mp hTp
  have kq := kend q mq hTq
  have hI : InjOn k (Icc p q) := by
    intro u hu u' hu' he
    rcases hsplit u hu with rfl | rfl | h1 <;> rcases hsplit u' hu' with rfl | rfl | h2
    · rfl
    · exact absurd he knq
    · exact absurd he.symm (kp _ h2)
    · exact absurd he.symm knq
    · rfl
    · exact absurd he.symm (kq _ h2)
    · exact absurd he (kp _ h1)
    · exact absurd he (kq _ h1)
    · exact kinj h1 h2 he
  have mon := ck.strictMonoOn_of_injOn_Icc' hpq.le hI
  have fixl : ∀ e ∈ Icc p q, ψ (T e) ∈ F → l (k e) = k e := fun e he hFe => by
    have h1 : α (θ (k e)) = θ (k e) := by
      rw [vk e he]
      exact fx _ hFe (hIcc e he)
    have h2 : θ (l (k e)) = θ (k e) := (hl (k e)).symm.trans h1
    exact fix_of ml l0 l1 (kIcc e he) (φ.injective (Subtype.ext h2))
  have finish : ∀ a b : ℝ, a < b → ((k p = a ∧ k q = b) ∨ (k p = b ∧ k q = a)) → l a = a → l b = b →
      ∃ τ : ℝ → ℝ, (∀ u ∈ Ioo p q, τ u ∈ Ioo p q ∧ ψ (T (τ u)) = α (ψ (T u))) ∧ StrictMonoOn τ
        (Ioo p q) ∧ Ioo p q ⊆ τ '' Ioo p q := by
    intro a b hab he la lb
    obtain ⟨τ, h1, h2, h3⟩ := gap_conj hab mon ck hpq he cl ml la lb
    refine ⟨τ, fun u hu => ⟨(h1 u hu).1, ?_⟩, h2, h3⟩
    rw [← vk _ (hIoo (h1 u hu).1), (h1 u hu).2, ← vk u (hIoo hu)]
    exact (hl (k u)).symm
  rcases lt_or_gt_of_ne knq with h | h
  · exact finish _ _ h (.inl ⟨rfl, rfl⟩) (fixl p mp hTp) (fixl q mq hTq)
  · exact finish _ _ h (.inr ⟨rfl, rfl⟩) (fixl q mq hTq) (fixl p mp hTp)

/-- The increasing map of the parameter of a cuff of the cut surface that meets the lifts. -/
theorem exists_tau [CompactSpace Y] (hS : IsSurface S) (hψ : IsCutting ψ F)
  (hF : IsClosed F) (hb : F ∩ bd S = {s, t})
    (hα : HasNullSignature α) (hs : α s = s) (ht : α t = t) {T : ℝ → Y} (hT : Continuous T)
      (hTb : ∀ u, T u ∈ bd Y)
    (h0 : ψ (T 0) ∈ F) (h1 : ψ (T 1) ∈ F) (hinj : InjOn T (Ioo 0 1)) :
    ∃ τ : ℝ → ℝ, ContinuousOn τ (Icc 0 1) ∧ StrictMonoOn τ (Icc 0 1) ∧ τ 0 = 0 ∧ τ 1 = 1
      ∧ ∀ u ∈ Icc (0 : ℝ) 1, τ u ∈ Icc (0 : ℝ) 1 ∧
      (ψ (T u) ∈ F → τ u = u) ∧ (ψ (T u) ∉ F → ψ (T (τ u)) = α (ψ (T u))) := by
  set E : Set ℝ := {u | ψ (T u) ∈ F} with hE
  have hEc : IsClosed E := hF.preimage (hψ.1.comp hT)
  have hE0 : (0 : ℝ) ∈ E := h0
  have hE1 : (1 : ℝ) ∈ E := h1
  have gapex : ∀ u ∈ Icc (0 : ℝ) 1, u ∉ E → ∃ p q : ℝ, 0 ≤ p ∧ q ≤ 1 ∧ p < u ∧ u < q ∧ p ∈ E
    ∧ q ∈ E ∧ ∀ v ∈ Ioo p q, v ∉ E := by
    intro u hu hnE
    have cA : IsCompact (E ∩ Icc 0 u) := isCompact_Icc.inter_left hEc
    have cB : IsCompact (E ∩ Icc u 1) := isCompact_Icc.inter_left hEc
    have nA : (E ∩ Icc 0 u).Nonempty := ⟨0, hE0, le_rfl, hu.1⟩
    have nB : (E ∩ Icc u 1).Nonempty := ⟨1, hE1, hu.2, le_rfl⟩
    have mA := cA.sSup_mem nA
    have mB := cB.sInf_mem nB
    have l1 : sSup (E ∩ Icc 0 u) < u := lt_of_le_of_ne mA.2.2 fun h => hnE (h ▸ mA.1)
    have l2 : u < sInf (E ∩ Icc u 1) := lt_of_le_of_ne mB.2.1 fun h => hnE (h ▸ mB.1)
    refine ⟨_, _, mA.2.1, mB.2.2, l1, l2, mA.1, mB.1, fun v hv hvE => ?_⟩
    rcases le_total v u with h | h
    · exact absurd (le_csSup cA.bddAbove ⟨hvE, (mA.2.1.trans hv.1.le), h⟩) (not_le.mpr hv.1)
    · exact absurd (csInf_le cB.bddBelow ⟨hvE, h, hv.2.le.trans mB.2.2⟩) (not_le.mpr hv.2)
  have gm : ∀ p q : ℝ, 0 ≤ p → q ≤ 1 → p < q → p ∈ E → q ∈ E → (∀ v ∈ Ioo p q, v ∉ E) →
      ∃ τ : ℝ → ℝ, (∀ u ∈ Ioo p q, τ u ∈ Ioo p q ∧ ψ (T (τ u)) = α (ψ (T u))) ∧ StrictMonoOn τ
        (Ioo p q) ∧ Ioo p q ⊆ τ '' Ioo p q :=
    fun p q hp hq hpq mp mq hg => exists_gap_map hS hψ hF hb hα hs ht hT hTb hpq mp mq hg
      (hinj.mono (Ioo_subset_Ioo hp hq))
  have ex : ∀ u ∈ Icc (0 : ℝ) 1, ∃ w, w ∈ Icc (0 : ℝ) 1 ∧ (u ∈ E → w = u) ∧ (u ∉ E → w ∈ Ioo
    (0 : ℝ) 1 ∧ w ∉ E ∧ ψ (T w) = α (ψ (T u))) := by
    intro u hu
    by_cases hn : u ∈ E
    · exact ⟨u, hu, fun _ => rfl, fun h => absurd hn h⟩
    · obtain ⟨p, q, hp, hq, l1, l2, mp, mq, hg⟩ := gapex u hu hn
      obtain ⟨τ', h2, -, -⟩ := gm p q hp hq (l1.trans l2) mp mq hg
      obtain ⟨h3, h4⟩ := h2 u ⟨l1, l2⟩
      have h5 : τ' u ∈ Ioo (0 : ℝ) 1 := ⟨hp.trans_lt h3.1, h3.2.trans_le hq⟩
      exact ⟨τ' u, Ioo_subset_Icc_self h5, fun h => absurd h hn, fun _ => ⟨h5, hg _ h3, h4⟩⟩
  choose! τ t1 t2 t3 using ex
  have hG : ∀ u ∈ Icc (0 : ℝ) 1, u ∉ E → ∃ p q : ℝ, 0 ≤ p ∧ q ≤ 1 ∧ p < u ∧ u < q ∧ p ∈ E ∧ q ∈ E ∧
    (∀ v ∈ Ioo p q, v ∉ E) ∧
      τ u ∈ Ioo p q ∧ StrictMonoOn τ (Ioo p q) ∧ Ioo p q ⊆ τ '' Ioo p q := by
    intro u hu hn
    obtain ⟨p, q, hp, hq, l1, l2, mp, mq, hg⟩ := gapex u hu hn
    obtain ⟨τ', h2, h3, h4⟩ := gm p q hp hq (l1.trans l2) mp mq hg
    have same : ∀ v ∈ Ioo p q, τ v = τ' v := by
      intro v hv
      have hvI : v ∈ Icc (0 : ℝ) 1 := ⟨hp.trans hv.1.le, hv.2.le.trans hq⟩
      obtain ⟨a1, a2, a3⟩ := t3 v hvI (hg v hv)
      obtain ⟨b1, b2⟩ := h2 v hv
      have b3 : τ' v ∈ Ioo (0 : ℝ) 1 := ⟨hp.trans_lt b1.1, b1.2.trans_le hq⟩
      exact hinj a1 b3 (hψ.2.2.1 a2 (hg _ b1) (a3.trans b2.symm))
    refine ⟨p, q, hp, hq, l1, l2, mp, mq, hg, ?_, ?_, ?_⟩
    · rw [same u ⟨l1, l2⟩]
      exact (h2 u ⟨l1, l2⟩).1
    · intro x hx y hy hxy
      rw [same x hx, same y hy]
      exact h3 hx hy hxy
    · intro w hw
      obtain ⟨v, hv, rfl⟩ := h4 hw
      exact ⟨v, hv, same v hv⟩
  have hmono : StrictMonoOn τ (Icc 0 1) := by
    intro u hu u' hu' huu
    by_cases h2 : u ∈ E <;> by_cases h3 : u' ∈ E
    · rw [t2 u hu h2, t2 u' hu' h3]
      exact huu
    · obtain ⟨p, q, -, -, l1, l2, -, -, hg, h4, -, -⟩ := hG u' hu' h3
      have h5 : u ≤ p := by
        by_contra hc
        exact hg u ⟨not_le.mp hc, huu.trans l2⟩ h2
      rw [t2 u hu h2]
      exact h5.trans_lt h4.1
    · obtain ⟨p, q, -, -, l1, l2, -, -, hg, h4, -, -⟩ := hG u hu h2
      have h5 : q ≤ u' := by
        by_contra hc
        exact hg u' ⟨l1.trans huu, not_le.mp hc⟩ h3
      rw [t2 u' hu' h3]
      exact h4.2.trans_le h5
    · obtain ⟨p, q, -, -, l1, l2, -, mq, hg, h4, h5, -⟩ := hG u hu h2
      by_cases h6 : u' < q
      · exact h5 ⟨l1, l2⟩ ⟨l1.trans huu, h6⟩ huu
      · obtain ⟨p', q', -, -, l1', l2', -, -, hg', h4', -, -⟩ := hG u' hu' h3
        have h7 : q ≤ p' := by
          by_contra hc
          exact hg' q ⟨not_le.mp hc, (not_lt.mp h6).trans_lt l2'⟩ mq
        exact h4.2.trans (h7.trans_lt h4'.1)
  have hsurj : ∀ w ∈ Icc (0 : ℝ) 1, ∃ u ∈ Icc (0 : ℝ) 1, τ u = w := by
    intro w hw
    by_cases h2 : w ∈ E
    · exact ⟨w, hw, t2 w hw h2⟩
    · obtain ⟨p, q, hp, hq, l1, l2, -, -, -, -, -, h5⟩ := hG w hw h2
      obtain ⟨v, hv, rfl⟩ := h5 ⟨l1, l2⟩
      exact ⟨v, ⟨hp.trans hv.1.le, hv.2.le.trans hq⟩, rfl⟩
  have hcont : ContinuousOn τ (Icc 0 1) := by
    let f : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun u => ⟨τ u.1, t1 u.1 u.2⟩
    have fm : StrictMono f := fun x y hxy => hmono x.2 y.2 hxy
    have fs : Surjective f := fun w => by
      obtain ⟨u, hu, h2⟩ := hsurj w.1 w.2
      exact ⟨⟨u, hu⟩, Subtype.ext h2⟩
    have fc : Continuous f := (fm.orderIsoOfSurjective f fs).continuous
    exact continuousOn_iff_continuous_domRestrict.mpr (continuous_subtype_val.comp fc)
  have m0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have m1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  refine ⟨τ, hcont, hmono, t2 0 m0 hE0, t2 1 m1 hE1, fun u hu => ⟨t1 u hu, t2 u hu, fun h => ?_⟩⟩
  exact (t3 u hu h).2.2

/-- What a homeomorphism of the cut surface does at a boundary point. -/
def Covers (ψ : Y → S) (F : Set S) (α : S ≃ₜ S) (C : Set Y) (z z' : Y) : Prop :=
  z' ∈ C ∧ (ψ z ∈ F → z' = z) ∧ (ψ z ∉ F → ψ z' = α (ψ z))

/-- The move on a cuff of the cut surface that meets the lifts. -/
theorem cuff_move (hY : IsSurface Y) (hS : IsSurface S) (hψ : IsCutting ψ F)
  (hF : IsClosed F) (hb : F ∩ bd S = {s, t})
    (hα : HasNullSignature α) (hs : α s = s) (ht : α t = t) {C U : Set Y} (hC : C ∈ cuffs Y)
      (hU : IsOpen U) (hCU : C ⊆ U)
    (hO : IsOArc C) {z₀ : Y} (hz : z₀ ∈ C) (hz0 : ψ z₀ ∈ F) :
    ∃ G : Y ≃ₜ Y, (∀ z ∈ C, Covers ψ F α C z (G z)) ∧ ∀ x ∉ U, G x = x := by
  have hcY : CompactSpace Y := hY.1
  obtain ⟨φ₀⟩ := id hO
  obtain ⟨φ, h0⟩ := exists_based φ₀ hz
  have hCb : C ⊆ bd Y := by
    obtain ⟨x, hx, rfl⟩ := hC
    exact connectedComponentIn_subset _ _
  set T : ℝ → Y := fun u => (φ (ee u)).1 with hTdef
  have hT : Continuous T := continuous_subtype_val.comp (φ.continuous.comp continuous_ee)
  have hT1 : T 1 = T 0 := by simp only [hTdef, ee_one]
  have hT0 : T 0 = z₀ := h0
  have hinj : InjOn T (Ioo 0 1) := fun x hx y hy he =>
    ee_injOn (Ioo_subset_Ico_self hx) (Ioo_subset_Ico_self hy) (φ.injective (Subtype.ext he))
  obtain ⟨τ, c1, c2, c3, c4, c5⟩ := exists_tau hS hψ hF hb hα hs ht hT (fun u => hCb (φ (ee u)).2)
    (by rw [hT0]; exact hz0) (by rw [hT1, hT0]; exact hz0) hinj
  obtain ⟨G, g1, g2⟩ := exists_move_loop hY hC hU hCU φ c1 c2 (by rw [c3, c4]; norm_num)
  refine ⟨G, fun z hzC => ?_, g2⟩
  obtain ⟨u, hu, e⟩ := exists_param (φ.symm ⟨z, hzC⟩)
  have hI := Ico_subset_Icc_self hu
  have e1 : T u = z := by simp only [hTdef, e, Homeomorph.apply_symm_apply]
  obtain ⟨c6, c7, c8⟩ := c5 u hI
  have e2 : G z = T (τ u) := by
    rw [← e1]
    exact g1 u hI
  refine ⟨e2 ▸ (φ (ee (τ u))).2, fun h => ?_, fun h => ?_⟩
  · rw [e2, c7 (e1 ▸ h), e1]
  · rw [e2, ← e1]
    exact c8 (e1 ▸ h)

/-- The move on a cuff of the cut surface that misses the lifts. -/
theorem cuff_move_off (hY : IsSurface Y) (hS : IsSurface S) (hψ : IsCutting ψ F)
  (hF : IsClosed F) (hα : HasNullSignature α)
    {C U : Set Y} (hC : C ∈ cuffs Y) (hU : IsOpen U) (hCU : C ⊆ U) (hO : IsOArc C)
      (hoff : ∀ z ∈ C, ψ z ∉ F) :
    ∃ G : Y ≃ₜ Y, (∀ z ∈ C, Covers ψ F α C z (G z)) ∧ ∀ x ∉ U, G x = x := by
  have hcuff := cuff_statement.{u} S hS
  have hcY : CompactSpace Y := hY.1
  obtain ⟨φ⟩ := id hO
  have hCb : C ⊆ bd Y := by
    obtain ⟨x, hx, rfl⟩ := hC
    exact connectedComponentIn_subset _ _
  set j : Circle → S := fun x => ψ (φ x).1 with hj
  have cj : Continuous j := hψ.1.comp (continuous_subtype_val.comp φ.continuous)
  have ij : Injective j := fun x y he =>
    φ.injective (Subtype.ext (hψ.2.2.1 (hoff _ (φ x).2) (hoff _ (φ y).2) he))
  have hce : IsClosedEmbedding j := cj.isClosedEmbedding ij
  have hX : IsOArc (range j) := ⟨hce.isEmbedding.toHomeomorph⟩
  have hb : range j ⊆ bd S := by
    rintro _ ⟨x, rfl⟩
    exact bd_of_bd hψ hF (hCb (φ x).2) (hoff _ (φ x).2)
  have hsub := (isPreconnected_range cj).subset_connectedComponentIn (mem_range_self 1) hb
  have hD : connectedComponentIn (bd S) (j 1) ∈ cuffs S := ⟨_, hb (mem_range_self 1), rfl⟩
  obtain ⟨φD⟩ := hcuff.2.2 _ hD
  have heq := oarc_eq φD hX hsub
  let φ' : Circle ≃ₜ connectedComponentIn (bd S) (j 1) := hce.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr heq)
  have hφ' : ∀ x, (φ' x).1 = j x := fun _ => rfl
  obtain ⟨h, hp, hh⟩ := hα _ φ' hD
  obtain ⟨G, g1, g2⟩ := move_cuff Y C U φ h hY hC hU hCU hp
  refine ⟨G, fun z hzC => ?_, g2⟩
  have e1 : (φ (φ.symm ⟨z, hzC⟩)).1 = z := by simp
  set x := φ.symm ⟨z, hzC⟩
  have e2 : G z = (φ (h x)).1 := by rw [← e1]; exact g1 x
  refine ⟨e2 ▸ (φ (h x)).2, fun h' => absurd h' (hoff z hzC), fun _ => ?_⟩
  rw [e2, ← e1]
  exact ((hh x).trans (hφ' _)).symm

/-- A homeomorphism of the cut surface that covers `α` on the boundary and fixes the lifts. -/
theorem exists_cover [T2Space Y] (hY : IsSurface Y) (hS : IsSurface S) (hψ : IsCutting ψ F)
  (hF : IsClosed F) (hb : F ∩ bd S = {s, t})
    (hα : HasNullSignature α) (hs : α s = s) (ht : α t = t) :
    ∃ G : Y ≃ₜ Y, ∀ C ∈ cuffs Y, ∀ z ∈ C, Covers ψ F α C z (G z) := by
  have hcuff := cuff_statement.{u} Y hY
  have step : ∀ C ∈ cuffs Y, ∀ U : Set Y, IsOpen U → C ⊆ U → ∃ G : Y ≃ₜ Y,
    (∀ z ∈ C, Covers ψ F α C z (G z)) ∧ ∀ x ∉ U, G x = x := by
    intro C hC U hU hCU
    by_cases h : ∃ z ∈ C, ψ z ∈ F
    · obtain ⟨z, hz, hz'⟩ := h
      exact cuff_move hY hS hψ hF hb hα hs ht hC hU hCU (hcuff.2.2 C hC) hz hz'
    · push Not at h
      exact cuff_move_off hY hS hψ hF hα hC hU hCU (hcuff.2.2 C hC) h
  have key : ∀ A : Set (Set Y), A.Finite → A ⊆ cuffs Y → ∃ G : Y ≃ₜ Y,
    (∀ C ∈ A, ∀ z ∈ C, Covers ψ F α C z (G z)) ∧
      ∀ z ∈ bd Y, (∀ C ∈ A, z ∉ C) → G z = z := by
    intro A hA
    induction A, hA using Set.Finite.induction_on with
    | empty => exact fun _ => ⟨Homeomorph.refl Y, by simp, fun _ _ _ => rfl⟩
    | @insert C A hnot hf ih =>
      intro hsub
      obtain ⟨G, g1, g2⟩ := ih ((subset_insert _ _).trans hsub)
      have hC : C ∈ cuffs Y := hsub (mem_insert _ _)
      have hclosed : IsClosed (⋃₀ (cuffs Y \ {C})) :=
        (hcuff.2.1.subset sdiff_subset).isClosed_sUnion fun D hD => (hcuff.2.2 D
          hD.1).isCompact.isClosed
      have hCU : C ⊆ (⋃₀ (cuffs Y \ {C}))ᶜ := by
        rintro z hz ⟨D, hD, hzD⟩
        exact Set.disjoint_left.mp (cuffs_disjoint hC hD.1 (fun h => hD.2 h.symm)) hz hzD
      obtain ⟨Gc, h1, h2⟩ := step C hC _ hclosed.isOpen_compl hCU
      have off : ∀ D ∈ cuffs Y, D ≠ C → ∀ z ∈ D, Gc z = z := fun D hD hne z hz => h2 z (fun h
        => h ⟨D, ⟨hD, hne⟩, hz⟩)
      refine ⟨G.trans Gc, ?_, ?_⟩
      · intro D hD z hz
        rcases hD with rfl | hD
        · have hzb : z ∈ bd Y := sUnion_cuffs (S := Y) ▸ (⟨D, hC, hz⟩ : z ∈ ⋃₀ cuffs Y)
          have e1 : G z = z := g2 z hzb fun E hE hzE => by
            have hne : E ≠ D := fun h => hnot (h ▸ hE)
            exact Set.disjoint_left.mp (cuffs_disjoint (hsub (.inr hE)) hC hne) hzE hz
          simpa only [Homeomorph.trans_apply, e1] using h1 z hz
        · have hne : D ≠ C := fun h => hnot (h ▸ hD)
          have h3 := g1 D hD z hz
          have e1 : Gc (G z) = G z := off D (hsub (.inr hD)) hne _ h3.1
          simpa only [Homeomorph.trans_apply, e1] using h3
      · intro z hzb hzn
        have e1 : G z = z := g2 z hzb fun E hE => hzn E (.inr hE)
        have hz' : z ∈ ⋃₀ cuffs Y := (sUnion_cuffs (S := Y)).symm ▸ hzb
        obtain ⟨D, hD, hzD⟩ := hz'
        have hne : D ≠ C := fun h => hzn C (mem_insert _ _) (h ▸ hzD)
        simp only [Homeomorph.trans_apply, e1]
        exact off D hD hne z hzD
  obtain ⟨G, h1, -⟩ := key _ hcuff.2.1 subset_rfl
  exact ⟨G, h1⟩

/-- A homeomorphism that fixes the lifts descends along the cut. -/
theorem exists_descend_cut [CompactSpace Y] (hψ : IsCutting ψ F) (G : Y ≃ₜ Y) (hG : ∀ z, ψ z ∈ F
  → G z = z) :
    ∃ γ : S ≃ₜ S, ∀ y, γ (ψ y) = ψ (G y) := by
  have hq : IsQuotientMap ψ := hψ.1.isClosedMap.isQuotientMap hψ.1 hψ.2.1
  have aux : ∀ H : Y ≃ₜ Y, (∀ z, ψ z ∈ F → H z = z) → ∃ f : S → S, Continuous f ∧ ∀ y, f (ψ y) = ψ
    (H y) := by
    intro H hH
    have e0 : ∀ x, ψ (surjInv hψ.2.1 x) = x := surjInv_eq hψ.2.1
    have e1 : ∀ y, ψ (H (surjInv hψ.2.1 (ψ y))) = ψ (H y) := by
      intro y
      by_cases h : ψ y ∈ F
      · rw [hH y h, hH _ ((e0 (ψ y)).symm ▸ h), e0]
      · have h' : ψ (surjInv hψ.2.1 (ψ y)) ∉ F := by
          rw [e0]
          exact h
        rw [hψ.2.2.1 h' h (e0 (ψ y))]
    refine ⟨fun x => ψ (H (surjInv hψ.2.1 x)), ?_, e1⟩
    rw [hq.continuous_iff]
    have e2 : (fun x => ψ (H (surjInv hψ.2.1 x))) ∘ ψ = ψ ∘ H := funext e1
    rw [e2]
    exact hψ.1.comp H.continuous
  obtain ⟨f, c1, h1⟩ := aux G hG
  obtain ⟨f', c2, h2⟩ := aux G.symm fun z hz => (G.symm_apply_eq).mpr (hG z hz).symm
  refine ⟨{
    toFun := f
    invFun := f'
    left_inv := fun x => ?_
    right_inv := fun x => ?_
    continuous_toFun := c1
    continuous_invFun := c2
  }, h1⟩
  · obtain ⟨y, rfl⟩ := hψ.2.1 x
    rw [h1, h2, G.symm_apply_apply]
  · obtain ⟨y, rfl⟩ := hψ.2.1 x
    rw [h2, h1, G.apply_symm_apply]

end cut

/-- `ParallelArcsStatement` for a connected surface. -/
theorem parallel_conn {S : Type u} [TopologicalSpace S] [ConnectedSpace S] {F F' : Set S} {s t : S}
  {α : S ≃ₜ S} (hS : IsSurface S) (hne : s ≠ t)
    (hb : F' ∩ bd S = {s, t}) (hl : IsLineWithEnds F' s t) (hαF : α '' F = F') (hs : α s = s)
      (ht : α t = t) (hα : HasNullSignature α) :
    ∃ β : S ≃ₜ S, β '' F = F' ∧ ∀ x ∈ bd S, β x = x := by
  have ht2 : T2Space S := hS.2.1
  have hF : IsClosed F' := hl.isCompact.isClosed
  obtain ⟨Y, tY, t2Y, ψ, hY, hψ, -, -, -⟩ := exists_cut_arc hS hne hb hl
  have hcY : CompactSpace Y := hY.1
  obtain ⟨G, hG⟩ := exists_cover hY hS hψ hF hb hα hs ht
  have hbdY : ∀ z ∈ bd Y, ∃ C ∈ cuffs Y, z ∈ C := fun z hz => by
    have hz' : z ∈ ⋃₀ cuffs Y := (sUnion_cuffs (S := Y)).symm ▸ hz
    obtain ⟨C, hC, hzC⟩ := hz'
    exact ⟨C, hC, hzC⟩
  have hfix : ∀ z, ψ z ∈ F' → G z = z := fun z hz => by
    obtain ⟨C, hC, hzC⟩ := hbdY z (hψ.2.2.2.2 hz)
    exact (hG C hC z hzC).2.1 hz
  obtain ⟨γ, hγ⟩ := exists_descend_cut hψ G hfix
  have fixF : ∀ x ∈ F', γ x = x := fun x hx => by
    obtain ⟨y, rfl⟩ := hψ.2.1 x
    rw [hγ, hfix y hx]
  have onB : ∀ x ∈ bd S, γ x = α x := fun x hx => by
    obtain ⟨y, rfl⟩ := hψ.2.1 x
    by_cases h : ψ y ∈ F'
    · have h1 : ψ y ∈ ({s, t} : Set S) := hb ▸ ⟨h, hx⟩
      rw [fixF _ h]
      rcases h1 with h1 | h1
      · rw [h1, hs]
      · rw [mem_singleton_iff.mp h1, ht]
    · obtain ⟨C, hC, hzC⟩ := hbdY y (bd_lift hψ hF hx h)
      rw [hγ]
      exact (hG C hC y hzC).2.2 h
  refine ⟨α.trans γ.symm, ?_, fun x hx => ?_⟩
  · ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 : α x ∈ F' := hαF ▸ mem_image_of_mem α hx
      have h2 : γ.symm (α x) = α x := (γ.symm_apply_eq).mpr (fixF _ h1).symm
      simpa only [Homeomorph.trans_apply, h2] using h1
    · intro hw
      obtain ⟨x, hx, rfl⟩ := hαF.symm ▸ hw
      have h2 : γ.symm (α x) = α x := (γ.symm_apply_eq).mpr (fixF _ hw).symm
      exact ⟨x, hx, by simp only [Homeomorph.trans_apply, h2]⟩
  · simp only [Homeomorph.trans_apply]
    exact (γ.symm_apply_eq).mpr (onB x hx).symm

/-- **Parallel arcs.** Graph Minors VII, (3.2), claim (1), page 219. The route is the one the paper
suggests: cut along `F'` and
move the cuffs of the cut surface. Only the component of `s` is changed, since the rest of the
boundary is kept by the identity. -/
theorem parallelArcs : ParallelArcsStatement.{u} := by
  intro S _ F F' s t α hS hne hb hb' hl hl' hαF hs ht hα
  have ht2 : T2Space S := hS.2.1
  have := hS.locallyConnected
  have hW : IsClopen (connectedComponent s) := isClopen_connectedComponent
  have hW1 : IsSurface (connectedComponent s) := isSurface_sub hS hW
  have hc : ConnectedSpace (connectedComponent s) := isConnected_iff_connectedSpace.mp
    isConnected_connectedComponent
  have subOf : ∀ {L : Set S}, IsLineWithEnds L s t → L ⊆ connectedComponent s := fun {L} h => by
    obtain ⟨a, ha, e, -, -⟩ := h.exists_arc
    have hp : IsPreconnected L := e ▸ isPreconnected_range ha.1
    exact hp.subset_connectedComponent h.left_mem
  have hsub := subOf hl
  have hsub' := subOf hl'
  have htW : t ∈ connectedComponent s := hsub hl.right_mem
  have hsW : s ∈ connectedComponent s := mem_connectedComponent
  have keep : ∀ (δ : S ≃ₜ S), δ s = s → ∀ x ∈ connectedComponent s, δ x ∈ connectedComponent s
    := fun δ hδ x hx =>
    (isPreconnected_connectedComponent.image δ δ.continuous.continuousOn).subset_connectedComponent
      ⟨s, hsW, hδ⟩ ⟨x, hx, rfl⟩
  have hsym : α.symm s = s := (α.symm_apply_eq).mpr hs.symm
  let αW : connectedComponent s ≃ₜ connectedComponent s := α.subtype (p :=
    (· ∈ connectedComponent s)) (q := (· ∈ connectedComponent s))
    fun x => ⟨keep α hs x, fun h => by simpa using keep α.symm hsym _ h⟩
  have hαW : ∀ x, (αW x).1 = α x.1 := fun _ => rfl
  have hbW : (Subtype.val ⁻¹' F' : Set (connectedComponent s)) ∩ bd (connectedComponent s)
    = {⟨s, hsW⟩, ⟨t, htW⟩} := by
    ext y
    have h3 : y ∈ bd (connectedComponent s) ↔ y.1 ∈ bd S := mem_bd_sub hW.2
    have h4 := Set.ext_iff.mp hb' y.1
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_preimage, h3, Subtype.ext_iff]
    simpa using h4
  have hlW : IsLineWithEnds (Subtype.val ⁻¹' F' : Set (connectedComponent s)) ⟨s, hsW⟩ ⟨t, htW⟩
    := by
    obtain ⟨u', v', e1, e2, h5⟩ := hl'.pull (j := (Subtype.val : connectedComponent s
      → S)) IsEmbedding.subtypeVal (by rwa [Subtype.range_coe])
    have e3 : u' = ⟨s, hsW⟩ := Subtype.ext e1
    have e4 : v' = ⟨t, htW⟩ := Subtype.ext e2
    rwa [e3, e4] at h5
  have hnull : HasNullSignature αW := by
    intro C φ hC
    have hcuff := cuff_statement.{u} S hS
    have hO : IsOArc (Subtype.val '' C : Set S) := ⟨hatC φ⟩
    have hbC : (Subtype.val '' C : Set S) ⊆ bd S := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hC
      exact (mem_bd_sub hW.2).mp (connectedComponentIn_subset _ _ hy)
    have hx0 : (hatC φ 1).1 ∈ (Subtype.val '' C : Set S) := (hatC φ 1).2
    have hsubC := hO.isPreconnected.subset_connectedComponentIn hx0 hbC
    have hD : connectedComponentIn (bd S) (hatC φ 1).1 ∈ cuffs S := ⟨_, hbC hx0, rfl⟩
    obtain ⟨φD⟩ := hcuff.2.2 _ hD
    have heq := oarc_eq φD hO hsubC
    obtain ⟨h, hp, hh⟩ := hα _ (hatC φ) (heq ▸ hD)
    exact ⟨h, hp, fun x => Subtype.ext (hh x)⟩
  have himg : αW '' (Subtype.val ⁻¹' F) = (Subtype.val ⁻¹' F' : Set (connectedComponent s)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hαF ▸ mem_image_of_mem α hx
    · intro hy
      obtain ⟨x, hx, e⟩ := hαF.symm ▸ (show y.1 ∈ F' from hy)
      exact ⟨⟨x, hsub hx⟩, hx, Subtype.ext e⟩
  obtain ⟨βW, h1, h2⟩ := parallel_conn hW1 (s := ⟨s, hsW⟩) (t := ⟨t, htW⟩) (fun he => hne
    (congrArg Subtype.val he)) hbW hlW himg
    (show αW ⟨s, hsW⟩ = ⟨s, hsW⟩ from Subtype.ext hs) (show αW ⟨t, htW⟩
      = ⟨t, htW⟩ from Subtype.ext ht) hnull
  obtain ⟨β, h3, h4⟩ := exists_extend hW βW
  refine ⟨β, ?_, fun x hx => ?_⟩
  · have e1 : Subtype.val '' (Subtype.val ⁻¹' F : Set (connectedComponent s)) = F := by
      rw [Subtype.image_preimage_coe, inter_eq_right.mpr hsub]
    have e2 : Subtype.val '' (Subtype.val ⁻¹' F' : Set (connectedComponent s)) = F' := by
      rw [Subtype.image_preimage_coe, inter_eq_right.mpr hsub']
    rw [← e1, ← e2, ← h1, image_image, image_image]
    exact image_congr fun y _ => h3 y
  · by_cases hxW : x ∈ connectedComponent s
    · have := h3 ⟨x, hxW⟩
      rw [h2 ⟨x, hxW⟩ ((mem_bd_sub hW.2).mpr hx)] at this
      exact this
    · exact h4 x hxW

end GraphMinor.Surface
