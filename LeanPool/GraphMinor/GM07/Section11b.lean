/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.Surface.ArcInPath
import LeanPool.GraphMinor.Surface.Cuffs
import LeanPool.GraphMinor.Surface.DiscMerge
import Mathlib.Topology.Metrizable.Urysohn

/-!
# Graph Minors VII, Section 11: Local Flatness, Concatenated Loops, and Proof of (11.5)

This file proves:
1. Local flatness and contractibility of chart balls in a surface (`exists_chart_ball_subset`):
   for every `x : S` and open `A ⊆ S` with `x ∈ A`, there is an open, arc-connected, flat
   neighbourhood `W ⊆ A` of `x` in which any two paths with the same endpoints are homotopic in `W`
   relative to their endpoints.
2. Periodic loop concatenation `concatLoop` (`Fin n → C(unitInterval, S) → C(Circle, S)`) and
   homotopy of concatenated loops (`concatLoop_homotopic`).
3. Graph Minors VII, (11.5) (`flat_locallyArcConnected_open_superset`), following the metric `δ` and
   `ε(z) / 3` open-cover proof on pages 251–252 of the paper.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Function Topology Metric unitInterval
open GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-! ## Local Chart Balls in a Surface -/

/-- The closed right half-plane `halfPlane = {z : ℂ | 0 ≤ z.re}` is convex over `ℝ`. -/
private theorem convex_halfPlane : Convex ℝ halfPlane := by
  intro x hx y hy a b ha hb _
  change 0 ≤ (a • x + b • y).re
  simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  have hx' : 0 ≤ x.re := hx
  have hy' : 0 ≤ y.re := hy
  positivity

/-- In a Hausdorff space, two points `a, b ∈ Z` are joined by a path in `Z` (`JoinedIn Z a b`) if
and only if `a = b` or there is a `[0, 1]`-arc in `Z` with ends `a, b`. -/
private theorem joinedIn_iff_eq_or_exists_isLineWithEnds' [T2Space S] {Z : Set S} {a b : S}
    (ha : a ∈ Z) (hb : b ∈ Z) :
    JoinedIn Z a b ↔ a = b ∨ ∃ L : Set S, L ⊆ Z ∧ IsLineWithEnds L a b := by
  constructor
  · intro h
    rcases eq_or_ne a b with rfl | hne
    · exact Or.inl rfl
    · obtain ⟨γ, hγ⟩ := h
      obtain ⟨e, he_cont, he_inj, he0, he1, he_sub⟩ :=
        exists_arc_of_path γ.continuous (by simpa [γ.source, γ.target] using hne)
      have he_emb : IsEmbedding e := (he_cont.isClosedEmbedding he_inj).isEmbedding
      refine Or.inr ⟨range e, ?_, he_emb.toHomeomorph, ?_, ?_⟩
      · intro x hx
        obtain ⟨t, rfl⟩ := he_sub hx
        exact hγ t
      · exact he0.trans γ.source
      · exact he1.trans γ.target
  · rintro (rfl | ⟨L, hLZ, f, hf0, hf1⟩)
    · exact JoinedIn.refl ha
    · let p : Path a b :=
        { toContinuousMap := ⟨fun t => (f t).1, continuous_subtype_val.comp f.continuous⟩
          source' := hf0
          target' := hf1 }
      exact ⟨p, fun t => hLZ (f t).2⟩

/-- In a Hausdorff space, a path-connected subset is arc-connected. -/
private theorem isArcConnected_of_isPathConnected [T2Space S] {Z : Set S}
    (hZ : IsPathConnected Z) : IsArcConnected Z := by
  intro a ha b hb hne
  exact ((joinedIn_iff_eq_or_exists_isLineWithEnds' ha hb).mp
    (hZ.joinedIn a ha b hb)).resolve_left hne

/-- In a Hausdorff space, if `Z` is arc-connected and `a, b ∈ Z`, there is a continuous path
`γ : C(unitInterval, S)` in `Z` from `a` to `b`. -/
theorem exists_path_of_isArcConnected {Z : Set S} (hZ : IsArcConnected Z)
    {a b : S} (ha : a ∈ Z) (hb : b ∈ Z) :
    ∃ γ : C(unitInterval, S), range γ ⊆ Z ∧ γ 0 = a ∧ γ 1 = b := by
  rcases eq_or_ne a b with rfl | hne
  · refine ⟨ContinuousMap.const unitInterval a, ?_, rfl, rfl⟩
    rintro _ ⟨_, rfl⟩
    exact ha
  · obtain ⟨L, hLZ, f, hf0, hf1⟩ := hZ a ha b hb hne
    refine ⟨⟨fun t => (f t).1, continuous_subtype_val.comp f.continuous⟩, ?_, hf0, hf1⟩
    rintro _ ⟨t, rfl⟩
    exact hLZ (f t).2

/-- Two paths `γ₀, γ₁ : C(unitInterval, S)` are homotopic in `W` relative to `{0, 1}`. -/
def PathsHomotopicRelIn (W : Set S) (γ₀ γ₁ : C(unitInterval, S)) : Prop :=
  ∃ H : C(unitInterval × unitInterval, S),
    (∀ p, H p ∈ W) ∧
    (∀ t, H (t, 0) = γ₀ t) ∧
    (∀ t, H (t, 1) = γ₁ t) ∧
    (∀ s, H (0, s) = γ₀ 0) ∧
    (∀ s, H (1, s) = γ₀ 1)

theorem PathsHomotopicRelIn.refl {W : Set S} {γ : C(unitInterval, S)} (hγ : range γ ⊆ W) :
    PathsHomotopicRelIn W γ γ :=
  ⟨⟨fun p => γ p.1, γ.continuous.comp continuous_fst⟩,
    fun p => hγ (mem_range_self p.1), fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem PathsHomotopicRelIn.mono {W₁ W₂ : Set S} {γ₀ γ₁ : C(unitInterval, S)}
    (hsub : W₁ ⊆ W₂) (h : PathsHomotopicRelIn W₁ γ₀ γ₁) :
    PathsHomotopicRelIn W₂ γ₀ γ₁ := by
  obtain ⟨H, hH, h0, h1, hs0, hs1⟩ := h
  exact ⟨H, fun p => hsub (hH p), h0, h1, hs0, hs1⟩

/-- Every point `x` in an open subset `A` of a surface `S` has an open, arc-connected, flat
chart-ball neighbourhood `W ⊆ A` equipped with a pointwise path-interpolation operator
`pt : S → S → unitInterval → S`. -/
theorem exists_chart_ball_interp (hS : IsSurface S) (x : S) {A : Set S}
    (hA : IsOpen A) (hxA : x ∈ A) :
    ∃ (W : Set S) (pt : S → S → unitInterval → S),
      W ⊆ A ∧ x ∈ W ∧ IsOpen W ∧ IsArcConnected W ∧ IsFlat W ∧
      (∀ y₁ ∈ W, ∀ y₂ ∈ W, ∀ s, pt y₁ y₂ s ∈ W) ∧
      (∀ y₁ ∈ W, ∀ y₂ ∈ W, pt y₁ y₂ 0 = y₁) ∧
      (∀ y₁ ∈ W, ∀ y₂ ∈ W, pt y₁ y₂ 1 = y₂) ∧
      (∀ y ∈ W, ∀ s, pt y y s = y) ∧
      (∀ γ₀ γ₁ : C(unitInterval, S), range γ₀ ⊆ W → range γ₁ ⊆ W →
        Continuous (fun p : unitInterval × unitInterval => pt (γ₀ p.1) (γ₁ p.1) p.2)) := by
  have : T2Space S := hS.2.1
  obtain ⟨U, O, j, k, hU, hO, hxU, hj, hk, hjU, _, hkj, hjk⟩ := (hS.2.2 x).exists_chart
  have hUA_open : IsOpen (U ∩ A) := hU.inter hA
  obtain ⟨O₁, hO₁_open, hO₁_eq⟩ := continuousOn_iff'.mp hk (U ∩ A) hUA_open
  have hjx_mem : j x ∈ O ∩ O₁ := by
    refine ⟨(hjU hxU).1, ?_⟩
    have hmem : j x ∈ k ⁻¹' (U ∩ A) ∩ (O ∩ halfPlane) := by
      refine ⟨?_, hjU hxU⟩
      change k (j x) ∈ U ∩ A
      rw [hkj hxU]
      exact ⟨hxU, hxA⟩
    rw [hO₁_eq] at hmem
    exact hmem.1
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hO.inter hO₁_open) (j x) hjx_mem
  let B : Set ℂ := ball (j x) r ∩ halfPlane
  let W : Set S := (U ∩ A) ∩ j ⁻¹' ball (j x) r
  have hB_sub : B ⊆ O ∩ halfPlane := fun z hz => ⟨(hball hz.1).1, hz.2⟩
  have hW_open : IsOpen W :=
    (hj.mono inter_subset_left).isOpen_inter_preimage hUA_open isOpen_ball
  have hxW : x ∈ W := ⟨⟨hxU, hxA⟩, mem_ball_self hr⟩
  have hWA : W ⊆ A := fun _ hy => hy.1.2
  have hjW : MapsTo j W B := fun y hy => ⟨hy.2, (hjU hy.1.1).2⟩
  have hkB : MapsTo k B W := fun z hz => by
    have hz_pre : z ∈ k ⁻¹' (U ∩ A) ∩ (O ∩ halfPlane) := by
      rw [hO₁_eq]
      exact ⟨(hball hz.1).2, (hball hz.1).1, hz.2⟩
    refine ⟨hz_pre.1, ?_⟩
    change j (k z) ∈ ball (j x) r
    rw [hjk (hB_sub hz)]
    exact hz.1
  have hkjW : LeftInvOn k j W := hkj.mono fun _ hy => hy.1.1
  have hB_conv : Convex ℝ B := (convex_ball (j x) r).inter convex_halfPlane
  have hB_pc : IsPathConnected B := hB_conv.isPathConnected ⟨j x, hjW hxW⟩
  have hkB_cont : ContinuousOn k B := hk.mono hB_sub
  have hjW_cont : ContinuousOn j W := hj.mono fun _ hy => hy.1.1
  have hW_eq : k '' B = W := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hkB hz
    · intro hy
      exact ⟨j y, hjW hy, hkjW hy⟩
  have hW_arc : IsArcConnected W := by
    rw [← hW_eq]
    exact isArcConnected_of_isPathConnected (hB_pc.image' hkB_cont)
  have hW_flat : IsFlat W := by
    intro φ hφW
    let L : Circle × unitInterval → ℂ :=
      fun p => (1 - (p.2 : ℝ)) • j (φ p.1) + (p.2 : ℝ) • j x
    have hL_cont : Continuous L := by
      have hjφ : Continuous (j ∘ φ) :=
        hjW_cont.comp_continuous φ.continuous fun z => hφW (mem_range_self z)
      refine Continuous.add ?_ ?_
      · exact (continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
          (hjφ.comp continuous_fst)
      · exact (continuous_subtype_val.comp continuous_snd).smul continuous_const
    have hL_mem : ∀ p, L p ∈ B := fun p =>
      hB_conv (hjW (hφW (mem_range_self p.1))) (hjW hxW)
        (sub_nonneg.mpr p.2.2.2) p.2.2.1 (sub_add_cancel 1 (p.2 : ℝ))
    have hΨ_cont : Continuous (k ∘ L) := hkB_cont.comp_continuous hL_cont hL_mem
    refine ⟨x, mem_univ x, ⟨k ∘ L, hΨ_cont⟩, fun _ => mem_univ _, fun z => ?_, fun z => ?_⟩
    · change k ((1 - (0 : ℝ)) • j (φ z) + (0 : ℝ) • j x) = φ z
      rw [sub_zero, one_smul, zero_smul, add_zero]
      exact hkjW (hφW (mem_range_self z))
    · change k ((1 - (1 : ℝ)) • j (φ z) + (1 : ℝ) • j x) = x
      rw [sub_self, zero_smul, one_smul, zero_add]
      exact hkjW hxW
  let pt : S → S → unitInterval → S :=
    fun y₁ y₂ s => k ((1 - (s : ℝ)) • j y₁ + (s : ℝ) • j y₂)
  refine ⟨W, pt, hWA, hxW, hW_open, hW_arc, hW_flat, ?_, ?_, ?_, ?_, ?_⟩
  · intro y₁ hy₁ y₂ hy₂ s
    exact hkB (hB_conv (hjW hy₁) (hjW hy₂) (sub_nonneg.mpr s.2.2) s.2.1 (sub_add_cancel 1 (s : ℝ)))
  · intro y₁ hy₁ _ _
    change k ((1 - (0 : ℝ)) • j y₁ + (0 : ℝ) • j _) = y₁
    rw [sub_zero, one_smul, zero_smul, add_zero]
    exact hkjW hy₁
  · intro _ _ y₂ hy₂
    change k ((1 - (1 : ℝ)) • j _ + (1 : ℝ) • j y₂) = y₂
    rw [sub_self, zero_smul, one_smul, zero_add]
    exact hkjW hy₂
  · intro y hy s
    change k ((1 - (s : ℝ)) • j y + (s : ℝ) • j y) = y
    rw [← add_smul, sub_add_cancel, one_smul]
    exact hkjW hy
  · intro γ₀ γ₁ hγ₀ hγ₁
    let L : unitInterval × unitInterval → ℂ :=
      fun p => (1 - (p.2 : ℝ)) • j (γ₀ p.1) + (p.2 : ℝ) • j (γ₁ p.1)
    have hjγ₀ : Continuous (j ∘ γ₀) :=
      hjW_cont.comp_continuous γ₀.continuous fun t => hγ₀ (mem_range_self t)
    have hjγ₁ : Continuous (j ∘ γ₁) :=
      hjW_cont.comp_continuous γ₁.continuous fun t => hγ₁ (mem_range_self t)
    have hL_cont : Continuous L := by
      refine Continuous.add ?_ ?_
      · exact (continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
          (hjγ₀.comp continuous_fst)
      · exact (continuous_subtype_val.comp continuous_snd).smul (hjγ₁.comp continuous_fst)
    have hL_mem : ∀ p, L p ∈ B := fun p =>
      hB_conv (hjW (hγ₀ (mem_range_self p.1))) (hjW (hγ₁ (mem_range_self p.1)))
        (sub_nonneg.mpr p.2.2.2) p.2.2.1 (sub_add_cancel 1 (p.2 : ℝ))
    exact hkB_cont.comp_continuous hL_cont hL_mem

/-- Every point `x` in an open subset `A` of a surface `S` has an open, arc-connected, flat
chart-ball neighbourhood `W ⊆ A` in which any two paths with the same endpoints are homotopic rel
endpoints (`PathsHomotopicRelIn W`). -/
theorem exists_chart_ball_subset (hS : IsSurface S) (x : S) {A : Set S}
    (hA : IsOpen A) (hxA : x ∈ A) :
    ∃ W : Set S, W ⊆ A ∧ x ∈ W ∧ IsOpen W ∧ IsArcConnected W ∧ IsFlat W ∧
      (∀ γ₀ γ₁ : C(unitInterval, S), range γ₀ ⊆ W → range γ₁ ⊆ W →
        γ₀ 0 = γ₁ 0 → γ₀ 1 = γ₁ 1 → PathsHomotopicRelIn W γ₀ γ₁) := by
  obtain ⟨W, pt, hWA, hxW, hWopen, hWarc, hWflat, hmem, hzero, hone, hconst, hcontinuous⟩ :=
    exists_chart_ball_interp hS x hA hxA
  refine ⟨W, hWA, hxW, hWopen, hWarc, hWflat, ?_⟩
  intro γ₀ γ₁ hγ₀ hγ₁ h0 h1
  have hmem₀ (t : unitInterval) : γ₀ t ∈ W := hγ₀ (mem_range_self t)
  have hmem₁ (t : unitInterval) : γ₁ t ∈ W := hγ₁ (mem_range_self t)
  refine ⟨⟨_, hcontinuous γ₀ γ₁ hγ₀ hγ₁⟩,
    fun p => hmem _ (hmem₀ p.1) _ (hmem₁ p.1) p.2,
    fun t => hzero _ (hmem₀ t) _ (hmem₁ t), fun t => hone _ (hmem₀ t) _ (hmem₁ t),
    ?_, ?_⟩
  · intro t
    change pt (γ₀ 0) (γ₁ 0) t = γ₀ 0
    rw [← h0]
    exact hconst _ (hmem₀ 0) t
  · intro t
    change pt (γ₀ 1) (γ₁ 1) t = γ₀ 1
    rw [← h1]
    exact hconst _ (hmem₀ 1) t

/-! ## Periodic Functions on `ℝ` and Concatenated Loops on `Circle` -/

/-- Cyclic successor on `Fin n` for `0 < n`. -/
def finNext {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.1 + 1) % n, Nat.mod_lt _ hn⟩

/-- Cyclic predecessor on `Fin n` for `0 < n`. -/
def finPrev {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.1 + (n - 1)) % n, Nat.mod_lt _ hn⟩

theorem finNext_finPrev {n : ℕ} (hn : 0 < n) (i : Fin n) :
    finNext hn (finPrev hn i) = i := by
  ext
  simp only [finNext, finPrev]
  rw [Nat.mod_add_mod, show i.1 + (n - 1) + 1 = i.1 + n by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt i.2]

theorem finPrev_finNext {n : ℕ} (hn : 0 < n) (i : Fin n) :
    finPrev hn (finNext hn i) = i := by
  ext
  simp only [finNext, finPrev]
  rw [Nat.mod_add_mod, show i.1 + 1 + (n - 1) = i.1 + n by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt i.2]

/-- Reduction of an integer `k : ℤ` modulo `n` (`0 < n`) as an element of `Fin n`. -/
def intModFin {n : ℕ} (hn : 0 < n) (k : ℤ) : Fin n :=
  ⟨(k % (n : ℤ)).toNat, by
    have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
    have hnn : 0 ≤ k % (n : ℤ) := Int.emod_nonneg k hnZ.ne'
    have hlt : k % (n : ℤ) < n := Int.emod_lt_of_pos k hnZ
    omega⟩

theorem intModFin_nat {n : ℕ} (hn : 0 < n) (i : Fin n) :
    intModFin hn (i.1 : ℤ) = i := by
  ext
  simp only [intModFin]
  have hi : (i.1 : ℤ) % (n : ℤ) = i.1 := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast i.2)
  rw [hi, Int.toNat_natCast]

theorem intModFin_add_nat {n : ℕ} (hn : 0 < n) (k : ℤ) :
    intModFin hn (k + (n : ℤ)) = intModFin hn k := by
  ext
  simp only [intModFin, Int.add_emod_right]

theorem intModFin_add_one {n : ℕ} (hn : 0 < n) (k : ℤ) :
    intModFin hn (k + 1) = finNext hn (intModFin hn k) := by
  ext
  simp only [intModFin, finNext]
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  have hnn : 0 ≤ k % (n : ℤ) := Int.emod_nonneg k hnZ.ne'
  have hlt : k % (n : ℤ) < n := Int.emod_lt_of_pos k hnZ
  have h1 : (k + 1) % (n : ℤ) = (k % (n : ℤ) + 1) % (n : ℤ) := by
    rw [Int.add_emod (k % (n : ℤ)) 1, Int.emod_emod, ← Int.add_emod]
  rw [h1]
  by_cases hlast : k % (n : ℤ) + 1 = (n : ℤ)
  · rw [hlast, Int.emod_self]
    have h2 : (k % (n : ℤ)).toNat + 1 = n := by omega
    rw [h2, Nat.mod_self]
    rfl
  · have hlt' : k % (n : ℤ) + 1 < (n : ℤ) := by omega
    rw [Int.emod_eq_of_lt (by omega) hlt']
    have h2 : ((k % (n : ℤ)).toNat + 1) % n = (k % (n : ℤ)).toNat + 1 :=
      Nat.mod_eq_of_lt (by omega)
    rw [h2]
    omega

/-- Fractional part of `x : ℝ` as an element of `unitInterval`. -/
noncomputable def unitFract (x : ℝ) : unitInterval :=
  ⟨Int.fract x, Int.fract_nonneg x, (Int.fract_lt_one x).le⟩

theorem unitFract_intCast (k : ℤ) : unitFract (k : ℝ) = 0 := by
  ext
  exact Int.fract_intCast k

/-- Given a family of parameterized paths `γ : Fin n → C(unitInterval × P, S)` with matching
endpoints, `chainFun hn γ : ℝ × P → S` chains them periodically along `ℝ`. -/
noncomputable def chainFun {P : Type*} [TopologicalSpace P] {n : ℕ} (hn : 0 < n)
    (γ : Fin n → C(unitInterval × P, S)) (p : ℝ × P) : S :=
  γ (intModFin hn ⌊p.1⌋) (unitFract p.1, p.2)

theorem chainFun_add_nat {P : Type*} [TopologicalSpace P] {n : ℕ} (hn : 0 < n)
    (γ : Fin n → C(unitInterval × P, S)) (x : ℝ) (p : P) :
    chainFun hn γ (x + (n : ℝ), p) = chainFun hn γ (x, p) := by
  dsimp [chainFun]
  have hfl : ⌊x + (n : ℤ)⌋ = ⌊x⌋ + (n : ℤ) := Int.floor_add_intCast x n
  have hfr : Int.fract (x + (n : ℤ)) = Int.fract x := Int.fract_add_intCast x n
  have hcast : (x + (n : ℝ)) = x + ((n : ℤ) : ℝ) := by push_cast; rfl
  rw [hcast, hfl, intModFin_add_nat]
  congr 2
  ext
  exact hfr

theorem chainFun_int_add {P : Type*} [TopologicalSpace P] {n : ℕ} (hn : 0 < n)
    (γ : Fin n → C(unitInterval × P, S))
    (hmatch : ∀ (i : Fin n) (p : P), γ i (1, p) = γ (finNext hn i) (0, p))
    (k : ℤ) (t : unitInterval) (p : P) :
    chainFun hn γ ((k : ℝ) + (t : ℝ), p) = γ (intModFin hn k) (t, p) := by
  by_cases ht1 : (t : ℝ) = 1
  · have ht_eq : t = 1 := Subtype.ext ht1
    have hsum : (k : ℝ) + (t : ℝ) = ((k + 1 : ℤ) : ℝ) := by
      rw [ht1]
      push_cast
      ring
    dsimp [chainFun]
    rw [hsum, Int.floor_intCast, unitFract_intCast, intModFin_add_one hn k, ht_eq, hmatch]
  · have ht_lt : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 ht1
    dsimp [chainFun]
    have hfl : ⌊(k : ℝ) + (t : ℝ)⌋ = k := by
      rw [add_comm, Int.floor_add_intCast, Int.floor_eq_zero_iff.mpr ⟨t.2.1, ht_lt⟩, zero_add]
    have hfr : unitFract ((k : ℝ) + (t : ℝ)) = t := by
      ext
      change Int.fract ((k : ℝ) + (t : ℝ)) = (t : ℝ)
      rw [Int.fract, hfl, add_sub_cancel_left]
    rw [hfl, hfr]

theorem continuous_chainFun {P : Type*} [TopologicalSpace P] {n : ℕ} (hn : 0 < n)
    (γ : Fin n → C(unitInterval × P, S))
    (hmatch : ∀ (i : Fin n) (p : P), γ i (1, p) = γ (finNext hn i) (0, p)) :
    Continuous (chainFun hn γ) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨x₀, p₀⟩
  let k : ℤ := ⌊x₀⌋
  let f₁ : ℝ × P → S := fun q =>
    γ (intModFin hn (k - 1)) (projIcc 0 1 zero_le_one (q.1 - ((k : ℝ) - 1)), q.2)
  let f₂ : ℝ × P → S := fun q =>
    γ (intModFin hn k) (projIcc 0 1 zero_le_one (q.1 - (k : ℝ)), q.2)
  have hf₁ : Continuous f₁ :=
    (γ _).continuous.comp
      ((continuous_projIcc.comp (continuous_fst.sub continuous_const)).prodMk continuous_snd)
  have hf₂ : Continuous f₂ :=
    (γ _).continuous.comp
      ((continuous_projIcc.comp (continuous_fst.sub continuous_const)).prodMk continuous_snd)
  let g : ℝ × P → S := fun q => if q.1 ≤ (k : ℝ) then f₁ q else f₂ q
  have hg : Continuous g := by
    refine Continuous.if_le hf₁ hf₂ continuous_fst continuous_const ?_
    intro q hq
    have h1 : projIcc 0 1 zero_le_one (q.1 - ((k : ℝ) - 1)) = 1 := by
      rw [hq, sub_sub_cancel]
      ext
      simp
    have h0 : projIcc 0 1 zero_le_one (q.1 - (k : ℝ)) = 0 := by
      rw [hq, sub_self]
      ext
      simp
    change γ (intModFin hn (k - 1)) (projIcc 0 1 zero_le_one (q.1 - ((k : ℝ) - 1)), q.2) =
      γ (intModFin hn k) (projIcc 0 1 zero_le_one (q.1 - (k : ℝ)), q.2)
    rw [h1, h0, hmatch, ← intModFin_add_one, sub_add_cancel]
  refine hg.continuousAt.congr_of_eventuallyEq ?_
  have hmem : (x₀, p₀) ∈ Ioo ((k : ℝ) - 1) ((k : ℝ) + 1) ×ˢ (univ : Set P) := by
    refine ⟨⟨?_, Int.lt_floor_add_one x₀⟩, mem_univ p₀⟩
    linarith [Int.floor_le x₀]
  filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hmem] with q hq
  rcases hq with ⟨⟨hq1, hq2⟩, _⟩
  dsimp [g]
  split_ifs with hle
  · let t : unitInterval := ⟨q.1 - ((k : ℝ) - 1), by linarith, by linarith⟩
    have hq_eq : q.1 = ((k - 1 : ℤ) : ℝ) + (t : ℝ) := by
      simp only [t]
      push_cast
      ring
    have hp_eq : projIcc 0 1 zero_le_one (q.1 - ((k : ℝ) - 1)) = t :=
      projIcc_of_mem zero_le_one t.2
    have hc := chainFun_int_add hn γ hmatch (k - 1) t q.2
    rw [← hq_eq] at hc
    exact hc.trans (by dsimp [f₁]; rw [hp_eq])
  · have hlt : (k : ℝ) < q.1 := not_le.mp hle
    let t : unitInterval := ⟨q.1 - (k : ℝ), by linarith, by linarith⟩
    have hq_eq : q.1 = (k : ℝ) + (t : ℝ) := by
      simp only [t]
      ring
    have hp_eq : projIcc 0 1 zero_le_one (q.1 - (k : ℝ)) = t :=
      projIcc_of_mem zero_le_one t.2
    have hc := chainFun_int_add hn γ hmatch k t q.2
    rw [← hq_eq] at hc
    exact hc.trans (by dsimp [f₂]; rw [hp_eq])

/-- Parameterized loop concatenation `C(Circle × P, S)` obtained from a cyclic chain of paths
`γ : Fin n → C(unitInterval × P, S)`. -/
noncomputable def concatLoopParam {P : Type*} [TopologicalSpace P] {n : ℕ} (hn : 0 < n)
    (γ : Fin n → C(unitInterval × P, S))
    (hmatch : ∀ (i : Fin n) (p : P), γ i (1, p) = γ (finNext hn i) (0, p)) :
    C(Circle × P, S) := by
  let F : ℝ × P → S := fun q => chainFun hn γ (q.1 * (n : ℝ) / (2 * Real.pi), q.2)
  have hF_cont : Continuous F :=
    (continuous_chainFun hn γ hmatch).comp
      (((continuous_fst.mul continuous_const).div_const (2 * Real.pi)).prodMk continuous_snd)
  have hsurj : Function.Surjective Circle.exp := fun w => ⟨Complex.arg w, Circle.exp_arg w⟩
  let G : Circle × P → S := fun q => F (Function.surjInv hsurj q.1, q.2)
  have hG_exp : ∀ (x : ℝ) (p : P), G (Circle.exp x, p) = F (x, p) := by
    intro x p
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (Function.surjInv_eq hsurj (Circle.exp x))
    dsimp [G, F]
    have h1 : Function.surjInv hsurj (Circle.exp x) * (n : ℝ) / (2 * Real.pi) =
        x * (n : ℝ) / (2 * Real.pi) + (m : ℝ) * (n : ℝ) := by
      rw [hm]
      have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      field_simp
    rw [h1]
    have hper : Function.Periodic (fun y => chainFun hn γ (y, p)) (n : ℝ) :=
      fun y => chainFun_add_nat hn γ y p
    exact hper.int_mul m (x * (n : ℝ) / (2 * Real.pi))
  have hq : IsQuotientMap (Prod.map Circle.exp (@id P)) :=
    (isLocalHomeomorph_circleExp.isOpenMap.prodMap IsOpenMap.id).isQuotientMap
      (Circle.exp.continuous.prodMap continuous_id) (hsurj.prodMap surjective_id)
  have hG_cont : Continuous G := by
    rw [hq.continuous_iff]
    have : G ∘ Prod.map Circle.exp (@id P) = F := by
      ext ⟨x, p⟩
      exact hG_exp x p
    rw [this]
    exact hF_cont
  exact ⟨G, hG_cont⟩

theorem concatLoopParam_exp {P : Type*} [TopologicalSpace P] {n : ℕ} (hn : 0 < n)
    (γ : Fin n → C(unitInterval × P, S))
    (hmatch : ∀ (i : Fin n) (p : P), γ i (1, p) = γ (finNext hn i) (0, p))
    (x : ℝ) (p : P) :
    concatLoopParam hn γ hmatch (Circle.exp (2 * Real.pi * x / (n : ℝ)), p) =
      chainFun hn γ (x, p) := by
  have hsurj : Function.Surjective Circle.exp := fun w => ⟨Complex.arg w, Circle.exp_arg w⟩
  let t : ℝ := 2 * Real.pi * x / (n : ℝ)
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (Function.surjInv_eq hsurj (Circle.exp t))
  change chainFun hn γ (Function.surjInv hsurj (Circle.exp t) * (n : ℝ) / (2 * Real.pi), p) =
    chainFun hn γ (x, p)
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : Function.surjInv hsurj (Circle.exp t) * (n : ℝ) / (2 * Real.pi) =
      x + (m : ℝ) * (n : ℝ) := by
    rw [hm]
    dsimp [t]
    field_simp
  rw [h1]
  have hper : Function.Periodic (fun y => chainFun hn γ (y, p)) (n : ℝ) :=
    fun y => chainFun_add_nat hn γ y p
  exact hper.int_mul m x

/-- Concatenated loop `concatLoop hn γ hmatch : C(Circle, S)` of `n` paths `γ : Fin n →
C(unitInterval, S)`
with cyclically matching endpoints `γ i 1 = γ (finNext hn i) 0`. -/
noncomputable def concatLoop {n : ℕ} (hn : 0 < n) (γ : Fin n → C(unitInterval, S))
    (hmatch : ∀ i : Fin n, γ i 1 = γ (finNext hn i) 0) : C(Circle, S) :=
  (concatLoopParam (P := Unit) hn (fun i => (γ i).comp ⟨Prod.fst, continuous_fst⟩)
    (fun i _ => hmatch i)).comp ⟨fun z => (z, ()), continuous_id.prodMk continuous_const⟩

theorem concatLoop_exp_piece {n : ℕ} (hn : 0 < n) (γ : Fin n → C(unitInterval, S))
    (hmatch : ∀ i : Fin n, γ i 1 = γ (finNext hn i) 0) (i : Fin n) (t : unitInterval) :
    concatLoop hn γ hmatch (Circle.exp (2 * Real.pi * ((i.1 : ℝ) + (t : ℝ)) / (n : ℝ))) =
      γ i t := by
  dsimp [concatLoop]
  have h := concatLoopParam_exp (P := Unit) hn (fun j => (γ j).comp ⟨Prod.fst, continuous_fst⟩)
    (fun j _ => hmatch j) ((i.1 : ℝ) + (t : ℝ)) ()
  rw [h]
  have h2 := chainFun_int_add (P := Unit) hn (fun j => (γ j).comp ⟨Prod.fst, continuous_fst⟩)
    (fun j _ => hmatch j) (i.1 : ℤ) t ()
  simp only [Int.cast_natCast, intModFin_nat hn i] at h2
  exact h2

theorem range_concatLoop {n : ℕ} (hn : 0 < n) (γ : Fin n → C(unitInterval, S))
    (hmatch : ∀ i : Fin n, γ i 1 = γ (finNext hn i) 0) :
    range (concatLoop hn γ hmatch) = ⋃ i : Fin n, range (γ i) := by
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    let x : ℝ := toIcoMod h2pi 0 (Complex.arg w) * (n : ℝ) / (2 * Real.pi)
    have hexp : Circle.exp (2 * Real.pi * x / (n : ℝ)) = w := by
      have h1 : 2 * Real.pi * x / (n : ℝ) = toIcoMod h2pi 0 (Complex.arg w) := by
        dsimp [x]
        field_simp
      rw [h1]
      have h2 : toIcoMod h2pi 0 (Complex.arg w) =
          Complex.arg w - toIcoDiv h2pi 0 (Complex.arg w) • (2 * Real.pi) := rfl
      have h3 : Circle.exp (toIcoMod h2pi 0 (Complex.arg w)) = Circle.exp (Complex.arg w) := by
        rw [h2, zsmul_eq_mul]
        exact Circle.exp_eq_exp.mpr ⟨-toIcoDiv h2pi 0 (Complex.arg w), by push_cast; ring⟩
      exact h3.trans (Circle.exp_arg w)
    rw [← hexp]
    dsimp [concatLoop]
    rw [concatLoopParam_exp]
    dsimp [chainFun]
    exact mem_iUnion.mpr ⟨intModFin hn ⌊x⌋, unitFract x, rfl⟩
  · rintro ⟨_, ⟨i, rfl⟩, t, rfl⟩
    exact ⟨Circle.exp (2 * Real.pi * ((i.1 : ℝ) + (t : ℝ)) / (n : ℝ)),
      concatLoop_exp_piece hn γ hmatch i t⟩

/-- If two cyclic chains of paths `γ₀, γ₁ : Fin n → C(unitInterval, S)` are connected by a family
of homotopies `H : Fin n → C(unitInterval × unitInterval, S)` whose endpoints match at each time
`s : unitInterval`, then `concatLoop hn γ₀` and `concatLoop hn γ₁` are homotopic. -/
theorem concatLoop_homotopic {Z : Set S} {n : ℕ} (hn : 0 < n)
    (γ₀ γ₁ : Fin n → C(unitInterval, S))
    (hmatch₀ : ∀ i : Fin n, γ₀ i 1 = γ₀ (finNext hn i) 0)
    (hmatch₁ : ∀ i : Fin n, γ₁ i 1 = γ₁ (finNext hn i) 0)
    (H : Fin n → C(unitInterval × unitInterval, S))
    (hHZ : ∀ i p, H i p ∈ Z)
    (hH0 : ∀ i t, H i (t, 0) = γ₀ i t)
    (hH1 : ∀ i t, H i (t, 1) = γ₁ i t)
    (hHmatch : ∀ i s, H i (1, s) = H (finNext hn i) (0, s)) :
    ClosedCurvesHomotopicIn Z (concatLoop hn γ₀ hmatch₀) (concatLoop hn γ₁ hmatch₁) := by
  let Ψ := concatLoopParam hn H hHmatch
  refine ⟨Ψ, ?_, fun w => ?_, fun w => ?_⟩
  · rintro ⟨w, s⟩
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    let x : ℝ := Complex.arg w * (n : ℝ) / (2 * Real.pi)
    have hexp : Circle.exp (2 * Real.pi * x / (n : ℝ)) = w := by
      have h1 : 2 * Real.pi * x / (n : ℝ) = Complex.arg w := by
        dsimp [x]
        have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        field_simp
      rw [h1, Circle.exp_arg]
    change Ψ (w, s) ∈ Z
    rw [← hexp, concatLoopParam_exp]
    exact hHZ _ _
  · let x : ℝ := Complex.arg w * (n : ℝ) / (2 * Real.pi)
    have hexp : Circle.exp (2 * Real.pi * x / (n : ℝ)) = w := by
      have h1 : 2 * Real.pi * x / (n : ℝ) = Complex.arg w := by
        dsimp [x]
        have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        field_simp
      rw [h1, Circle.exp_arg]
    change Ψ (w, 0) = concatLoop hn γ₀ hmatch₀ w
    rw [← hexp]
    dsimp [Ψ, concatLoop]
    rw [concatLoopParam_exp, concatLoopParam_exp]
    dsimp [chainFun]
    exact hH0 _ _
  · let x : ℝ := Complex.arg w * (n : ℝ) / (2 * Real.pi)
    have hexp : Circle.exp (2 * Real.pi * x / (n : ℝ)) = w := by
      have h1 : 2 * Real.pi * x / (n : ℝ) = Complex.arg w := by
        dsimp [x]
        have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        field_simp
      rw [h1, Circle.exp_arg]
    change Ψ (w, 1) = concatLoop hn γ₁ hmatch₁ w
    rw [← hexp]
    dsimp [Ψ, concatLoop]
    rw [concatLoopParam_exp, concatLoopParam_exp]
    dsimp [chainFun]
    exact hH1 _ _

/-- Any closed curve `φ : C(Circle, S)` equals the `n`-piece concatenation `concatLoop` of its
restrictions to the `n` equal arcs of `Circle`. -/
noncomputable def curvePiece {n : ℕ} (_hn : 0 < n) (φ : C(Circle, S)) (i : Fin n) :
    C(unitInterval, S) :=
  ⟨fun t => φ (Circle.exp (2 * Real.pi * ((i.1 : ℝ) + (t : ℝ)) / (n : ℝ))), by fun_prop⟩

theorem curvePiece_match {n : ℕ} (hn : 0 < n) (φ : C(Circle, S)) (i : Fin n) :
    curvePiece hn φ i 1 = curvePiece hn φ (finNext hn i) 0 := by
  dsimp [curvePiece, finNext]
  by_cases hlast : i.1 + 1 = n
  · have hmod : (i.1 + 1) % n = 0 := by rw [hlast, Nat.mod_self]
    rw [hmod]
    simp only [add_zero, Nat.cast_zero, mul_zero, zero_div, Circle.exp_zero]
    have h1 : (i.1 : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hlast
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [h1, mul_div_cancel_right₀ _ hn', Circle.exp_two_pi]
  · have hlt : i.1 + 1 < n := lt_of_le_of_ne (Nat.succ_le_of_lt i.2) hlast
    rw [Nat.mod_eq_of_lt hlt]
    simp only [add_zero, Nat.cast_add, Nat.cast_one]

theorem concatLoop_curvePiece {n : ℕ} (hn : 0 < n) (φ : C(Circle, S)) :
    concatLoop hn (curvePiece hn φ) (curvePiece_match hn φ) = φ := by
  ext w
  let x : ℝ := Complex.arg w * (n : ℝ) / (2 * Real.pi)
  have hexp : Circle.exp (2 * Real.pi * x / (n : ℝ)) = w := by
    have h1 : 2 * Real.pi * x / (n : ℝ) = Complex.arg w := by
      dsimp [x]
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    rw [h1, Circle.exp_arg]
  rw [← hexp]
  dsimp [concatLoop]
  rw [concatLoopParam_exp]
  dsimp [chainFun, curvePiece, unitFract]
  congr 1
  have hk : ((intModFin hn ⌊x⌋).1 : ℝ) = ((⌊x⌋ % (n : ℤ) : ℤ) : ℝ) := by
    dsimp [intModFin]
    have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
    have hnn : 0 ≤ ⌊x⌋ % (n : ℤ) := Int.emod_nonneg ⌊x⌋ hnZ.ne'
    exact_mod_cast Int.toNat_of_nonneg hnn
  rw [hk]
  have hdiv : (⌊x⌋ : ℝ) = (n : ℝ) * ((⌊x⌋ / (n : ℤ) : ℤ) : ℝ) + ((⌊x⌋ % (n : ℤ) : ℤ) : ℝ) := by
    have := (Int.mul_ediv_add_emod ⌊x⌋ (n : ℤ)).symm
    exact_mod_cast this
  have hx_eq : ((⌊x⌋ % (n : ℤ) : ℤ) : ℝ) + Int.fract x =
      x - (n : ℝ) * ((⌊x⌋ / (n : ℤ) : ℤ) : ℝ) := by
    have hfr := Int.self_sub_floor x
    linarith [hdiv, hfr]
  rw [hx_eq]
  apply Circle.exp_eq_exp.mpr
  refine ⟨-(⌊x⌋ / (n : ℤ)), ?_⟩
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp
  ring

/-! ## Subdivision Lemma for Compact Intervals / Circles -/

/-- Given a continuous curve `φ : C(Circle, S)` with `range φ ⊆ ⋃ i ∈ J, U i` where each `U i` is
open, there exists `n ≥ 1` such that each of the `n` pieces `curvePiece hn φ k` has its range
contained in `U (z k)` for some `z k ∈ J`. -/
theorem exists_subdivision_in_open_cover {ι : Type*} {J : Set ι} {U : ι → Set S}
    (hU_open : ∀ i ∈ J, IsOpen (U i)) (φ : C(Circle, S))
    (hcov : range φ ⊆ ⋃ i ∈ J, U i) :
    ∃ (n : ℕ) (hn : 0 < n) (z : Fin n → ι),
      (∀ k : Fin n, z k ∈ J) ∧ ∀ k : Fin n, range (curvePiece hn φ k) ⊆ U (z k) := by
  let g : ℝ → S := fun θ => φ (Circle.exp θ)
  have hg : Continuous g := φ.continuous.comp Circle.exp.continuous
  let V : J → Set ℝ := fun j => g ⁻¹' U j.1
  have hV_open : ∀ j : J, IsOpen (V j) := fun j => (hU_open j.1 j.2).preimage hg
  have hIcc_cov : Icc (0 : ℝ) (2 * Real.pi) ⊆ ⋃ j : J, V j := fun θ _ => by
    obtain ⟨i, hi, hmem⟩ := mem_iUnion₂.mp (hcov (mem_range_self (Circle.exp θ)))
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hmem⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hV_open hIcc_cov
  obtain ⟨n, hn_gt⟩ := exists_nat_gt (2 * Real.pi / δ)
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hn_pos : (0 : ℝ) < n := lt_trans (div_pos h2pi hδ) hn_gt
  have hn : 0 < n := by exact_mod_cast hn_pos
  have hstep : 2 * Real.pi / (n : ℝ) < δ :=
    (div_lt_iff₀ hn_pos).mpr (by linarith [(div_lt_iff₀ hδ).mp hn_gt])
  have hex : ∀ k : Fin n, ∃ i ∈ J, range (curvePiece hn φ k) ⊆ U i := by
    intro k
    let a : ℝ := 2 * Real.pi * (k.1 : ℝ) / (n : ℝ)
    have ha_mem : a ∈ Icc (0 : ℝ) (2 * Real.pi) := by
      refine ⟨by positivity, ?_⟩
      rw [div_le_iff₀ hn_pos]
      have : (k.1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast k.2.le
      nlinarith
    obtain ⟨j, hball⟩ := hleb a ha_mem
    refine ⟨j.1, j.2, ?_⟩
    rintro _ ⟨t, rfl⟩
    let θ : ℝ := 2 * Real.pi * ((k.1 : ℝ) + (t : ℝ)) / (n : ℝ)
    have hθ_ball : θ ∈ ball a δ := by
      rw [mem_ball, Real.dist_eq]
      have hdiff : θ - a = (2 * Real.pi / (n : ℝ)) * (t : ℝ) := by
        dsimp [θ, a]
        ring
      have ht_nn : 0 ≤ (t : ℝ) := t.2.1
      rw [hdiff, abs_of_nonneg (by positivity)]
      have ht_le : (t : ℝ) ≤ 1 := t.2.2
      have hle : (2 * Real.pi / (n : ℝ)) * (t : ℝ) ≤ 2 * Real.pi / (n : ℝ) :=
        mul_le_of_le_one_right (by positivity) ht_le
      exact lt_of_le_of_lt hle hstep
    exact hball hθ_ball
  choose z hzJ hzU using hex
  exact ⟨n, hn, z, hzJ, hzU⟩

/-! ## Proof of (11.5): Open, Flat, Locally Arc-Connected Superset -/

/-- Transitivity of `ClosedCurvesHomotopicIn Z` for closed curves `φ₀, φ₁, φ₂ : C(Circle, S)`. -/
private theorem closedCurvesHomotopicIn_trans {Z : Set S} {φ₀ φ₁ φ₂ : C(Circle, S)}
    (h₁ : ClosedCurvesHomotopicIn Z φ₀ φ₁) (h₂ : ClosedCurvesHomotopicIn Z φ₁ φ₂) :
    ClosedCurvesHomotopicIn Z φ₀ φ₂ := by
  obtain ⟨ψ₁, hψ₁Z, hψ₁0, hψ₁1⟩ := h₁
  obtain ⟨ψ₂, hψ₂Z, hψ₂0, hψ₂1⟩ := h₂
  let t₁ : Circle × unitInterval → Circle × unitInterval :=
    fun p => (p.1, projIcc 0 1 zero_le_one (2 * (p.2 : ℝ)))
  let t₂ : Circle × unitInterval → Circle × unitInterval :=
    fun p => (p.1, projIcc 0 1 zero_le_one (2 * (p.2 : ℝ) - 1))
  have ht₁_cont : Continuous t₁ :=
    continuous_fst.prodMk (continuous_projIcc.comp (continuous_const.mul
      (continuous_subtype_val.comp continuous_snd)))
  have ht₂_cont : Continuous t₂ :=
    continuous_fst.prodMk (continuous_projIcc.comp
      ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).sub continuous_const))
  let f₁ : Circle × unitInterval → S := ψ₁ ∘ t₁
  let f₂ : Circle × unitInterval → S := ψ₂ ∘ t₂
  have hf₁_cont : Continuous f₁ := ψ₁.continuous.comp ht₁_cont
  have hf₂_cont : Continuous f₂ := ψ₂.continuous.comp ht₂_cont
  let Ψ_fun : Circle × unitInterval → S :=
    fun p => if (p.2 : ℝ) ≤ 1 / 2 then f₁ p else f₂ p
  have hΨ_cont : Continuous Ψ_fun := by
    refine Continuous.if_le hf₁_cont hf₂_cont
      (continuous_subtype_val.comp continuous_snd) continuous_const ?_
    intro p hp
    have hp1 : projIcc 0 1 zero_le_one (2 * (p.2 : ℝ)) = 1 := by
      rw [hp]; ext; simp
    have hp0 : projIcc 0 1 zero_le_one (2 * (p.2 : ℝ) - 1) = 0 := by
      rw [hp]; ext; simp
    change ψ₁ (p.1, projIcc 0 1 zero_le_one (2 * (p.2 : ℝ))) =
      ψ₂ (p.1, projIcc 0 1 zero_le_one (2 * (p.2 : ℝ) - 1))
    rw [hp1, hp0, hψ₁1 p.1, hψ₂0 p.1]
  refine ⟨⟨Ψ_fun, hΨ_cont⟩, fun p => ?_, fun z => ?_, fun z => ?_⟩
  · dsimp [Ψ_fun]
    split_ifs
    · exact hψ₁Z (t₁ p)
    · exact hψ₂Z (t₂ p)
  · have hle : ((0 : unitInterval) : ℝ) ≤ 1 / 2 := by norm_num
    have hp0 : projIcc 0 1 zero_le_one (2 * ((0 : unitInterval) : ℝ)) = 0 := by
      ext; change max (0 : ℝ) (min 1 (2 * 0)) = 0; norm_num
    change (if ((0 : unitInterval) : ℝ) ≤ 1 / 2 then f₁ (z, 0) else f₂ (z, 0)) = φ₀ z
    simp only [hle, ↓reduceIte]
    change ψ₁ (z, projIcc 0 1 zero_le_one (2 * ((0 : unitInterval) : ℝ))) = φ₀ z
    rw [hp0, hψ₁0 z]
  · have hnot : ¬ (((1 : unitInterval) : ℝ) ≤ 1 / 2) := by norm_num
    have hp1 : projIcc 0 1 zero_le_one (2 * ((1 : unitInterval) : ℝ) - 1) = 1 := by
      ext; change max (0 : ℝ) (min 1 (2 * 1 - 1)) = 1; norm_num
    change (if ((1 : unitInterval) : ℝ) ≤ 1 / 2 then f₁ (z, 1) else f₂ (z, 1)) = φ₂ z
    simp only [hnot, ↓reduceIte]
    change ψ₂ (z, projIcc 0 1 zero_le_one (2 * ((1 : unitInterval) : ℝ) - 1)) = φ₂ z
    rw [hp1, hψ₂1 z]

/-- Given paths `γ, α₀, α₁ : C(unitInterval, S)` with `α₀ 1 = γ 0` and `α₁ 1 = γ 1`, the
time-dependent 3-piece concatenation `whiskerHomotopy α₀ γ α₁ : C(unitInterval × unitInterval, S)`
interpolates from a reparameterization of `γ` at `s = 0` to `α₀ * γ * α₁⁻¹` at `s = 1`, with
endpoints `α₀ (1 - s)` and `α₁ (1 - s)` at time `s`. -/
noncomputable def whiskerHomotopy (α₀ γ α₁ : C(unitInterval, S))
    (h0 : α₀ 1 = γ 0) (h1 : α₁ 1 = γ 1) : C(unitInterval × unitInterval, S) := by
  let f₁ : unitInterval × unitInterval → S := fun p =>
    α₀ (projIcc 0 1 zero_le_one (1 - (p.2 : ℝ) + (p.2 : ℝ) * (3 * (p.1 : ℝ))))
  let f₂ : unitInterval × unitInterval → S := fun p =>
    γ (projIcc 0 1 zero_le_one (3 * (p.1 : ℝ) - 1))
  let f₃ : unitInterval × unitInterval → S := fun p =>
    α₁ (projIcc 0 1 zero_le_one (1 - (p.2 : ℝ) * (3 * (p.1 : ℝ) - 2)))
  have hf₁ : Continuous f₁ := by fun_prop
  have hf₂ : Continuous f₂ := by fun_prop
  have hf₃ : Continuous f₃ := by fun_prop
  let f₁₂ : unitInterval × unitInterval → S :=
    fun p => if (p.1 : ℝ) ≤ 1 / 3 then f₁ p else f₂ p
  have hf₁₂ : Continuous f₁₂ := by
    refine Continuous.if_le hf₁ hf₂ (continuous_subtype_val.comp continuous_fst) continuous_const ?_
    intro p hp
    have hp1 : projIcc 0 1 zero_le_one (1 - (p.2 : ℝ) + (p.2 : ℝ) * (3 * (p.1 : ℝ))) = 1 := by
      rw [hp]; ext; change max (0 : ℝ) (min 1 (1 - (p.2 : ℝ) + (p.2 : ℝ) * (3 * (1 / 3)))) = 1
      have : 1 - (p.2 : ℝ) + (p.2 : ℝ) * (3 * (1 / 3)) = 1 := by ring
      rw [this]; norm_num
    have hp0 : projIcc 0 1 zero_le_one (3 * (p.1 : ℝ) - 1) = 0 := by
      rw [hp]; ext; simp
    change α₀ _ = γ _
    rw [hp1, hp0, h0]
  let F : unitInterval × unitInterval → S :=
    fun p => if (p.1 : ℝ) ≤ 2 / 3 then f₁₂ p else f₃ p
  have hF : Continuous F := by
    refine Continuous.if_le hf₁₂ hf₃ (continuous_subtype_val.comp continuous_fst) continuous_const
      ?_
    intro p hp
    have hnot : ¬ ((p.1 : ℝ) ≤ 1 / 3) := by linarith
    have hp1 : projIcc 0 1 zero_le_one (3 * (p.1 : ℝ) - 1) = 1 := by
      rw [hp]; ext; change max (0 : ℝ) (min 1 (3 * (2 / 3) - 1)) = 1; norm_num
    have hp1' : projIcc 0 1 zero_le_one (1 - (p.2 : ℝ) * (3 * (p.1 : ℝ) - 2)) = 1 := by
      rw [hp]; ext; change max (0 : ℝ) (min 1 (1 - (p.2 : ℝ) * (3 * (2 / 3) - 2))) = 1
      have : 1 - (p.2 : ℝ) * (3 * (2 / 3) - 2) = 1 := by ring
      rw [this]; norm_num
    dsimp [f₁₂]
    simp only [hnot, ↓reduceIte]
    change γ _ = α₁ _
    rw [hp1, hp1', h1]
  exact ⟨F, hF⟩

theorem whiskerHomotopy_mem {U₀ U₁ : Set S} (α₀ γ α₁ : C(unitInterval, S))
    (h0 : α₀ 1 = γ 0) (h1 : α₁ 1 = γ 1)
    (hα₀ : range α₀ ⊆ U₀) (hγ : range γ ⊆ U₁) (hα₁ : range α₁ ⊆ U₁)
    (p : unitInterval × unitInterval) :
    whiskerHomotopy α₀ γ α₁ h0 h1 p ∈ U₀ ∪ U₁ := by
  dsimp [whiskerHomotopy]
  split_ifs
  · exact Or.inl (hα₀ (mem_range_self _))
  · exact Or.inr (hγ (mem_range_self _))
  · exact Or.inr (hα₁ (mem_range_self _))

theorem whiskerHomotopy_left (α₀ γ α₁ : C(unitInterval, S))
    (h0 : α₀ 1 = γ 0) (h1 : α₁ 1 = γ 1) (s : unitInterval) :
    whiskerHomotopy α₀ γ α₁ h0 h1 (0, s) = α₀ (symm s) := by
  dsimp [whiskerHomotopy]
  split_ifs with h1 h2
  · congr 1
    have h_eq : 1 - (s : ℝ) + (s : ℝ) * (3 * (0 : ℝ)) = 1 - (s : ℝ) := by ring
    rw [h_eq]
    exact projIcc_of_mem zero_le_one (symm s).2
  · norm_num at h2
  · norm_num at h1

theorem whiskerHomotopy_right (α₀ γ α₁ : C(unitInterval, S))
    (h0 : α₀ 1 = γ 0) (h1 : α₁ 1 = γ 1) (s : unitInterval) :
    whiskerHomotopy α₀ γ α₁ h0 h1 (1, s) = α₁ (symm s) := by
  dsimp [whiskerHomotopy]
  split_ifs with h1 h2
  · norm_num at h1
  · norm_num at h1
  · congr 1
    have h_eq : 1 - (s : ℝ) * (3 * (1 : ℝ) - 2) = 1 - (s : ℝ) := by ring
    rw [h_eq]
    exact projIcc_of_mem zero_le_one (symm s).2

/-- Linear reparameterization homotopy from `γ` to `whiskerHomotopy α₀ γ α₁ h0 h1 (·, 0)`. -/
noncomputable def reparamHomotopy (α₀ γ α₁ : C(unitInterval, S))
    (_h0 : α₀ 1 = γ 0) (_h1 : α₁ 1 = γ 1) : C(unitInterval × unitInterval, S) := by
  let τ : unitInterval × unitInterval → unitInterval := fun p =>
    projIcc 0 1 zero_le_one ((1 - (p.2 : ℝ)) * (p.1 : ℝ) + (p.2 : ℝ) * (3 * (p.1 : ℝ) - 1))
  exact ⟨fun p => γ (τ p), by fun_prop⟩

theorem reparamHomotopy_mem {U : Set S} (α₀ γ α₁ : C(unitInterval, S))
    (h0 : α₀ 1 = γ 0) (h1 : α₁ 1 = γ 1) (hγ : range γ ⊆ U)
    (p : unitInterval × unitInterval) :
    reparamHomotopy α₀ γ α₁ h0 h1 p ∈ U :=
  hγ (mem_range_self _)

theorem reparamHomotopy_zero (α₀ γ α₁ : C(unitInterval, S))
    (h0 : α₀ 1 = γ 0) (h1 : α₁ 1 = γ 1) (t : unitInterval) :
    reparamHomotopy α₀ γ α₁ h0 h1 (t, 0) = γ t := by
  dsimp [reparamHomotopy]
  congr 1
  have h_eq : (1 - (0 : ℝ)) * (t : ℝ) + (0 : ℝ) * (3 * (t : ℝ) - 1) = (t : ℝ) := by ring
  rw [h_eq]
  exact projIcc_of_mem zero_le_one t.2

theorem reparamHomotopy_one (α₀ γ α₁ : C(unitInterval, S))
    (h0 : α₀ 1 = γ 0) (h1 : α₁ 1 = γ 1) (t : unitInterval) :
    reparamHomotopy α₀ γ α₁ h0 h1 (t, 1) = whiskerHomotopy α₀ γ α₁ h0 h1 (t, 0) := by
  dsimp [reparamHomotopy, whiskerHomotopy]
  have h_lhs : (1 - (1 : ℝ)) * (t : ℝ) + (1 : ℝ) * (3 * (t : ℝ) - 1) = 3 * (t : ℝ) - 1 := by ring
  rw [h_lhs]
  split_ifs with h23 h13
  · have h_rhs : 1 - (0 : ℝ) + (0 : ℝ) * (3 * (t : ℝ)) = 1 := by ring
    rw [h_rhs]
    have hp1 : projIcc 0 1 zero_le_one (1 : ℝ) = 1 :=
      projIcc_of_mem zero_le_one (right_mem_Icc.mpr zero_le_one)
    have hp0 : projIcc 0 1 zero_le_one (3 * (t : ℝ) - 1) = 0 :=
      projIcc_of_le_left zero_le_one (by linarith)
    rw [hp1, hp0, h0]
  · rfl
  · have hgt : 2 / 3 < (t : ℝ) := not_le.mp h23
    have h_rhs : 1 - (0 : ℝ) * (3 * (t : ℝ) - 2) = 1 := by ring
    rw [h_rhs]
    have hp1 : projIcc 0 1 zero_le_one (1 : ℝ) = 1 :=
      projIcc_of_mem zero_le_one (right_mem_Icc.mpr zero_le_one)
    have hp1' : projIcc 0 1 zero_le_one (3 * (t : ℝ) - 1) = 1 :=
      projIcc_of_right_le zero_le_one (by linarith)
    rw [hp1, hp1', h1]

theorem reparamHomotopy_left (α₀ γ α₁ : C(unitInterval, S))
    (h0 : α₀ 1 = γ 0) (h1 : α₁ 1 = γ 1) (s : unitInterval) :
    reparamHomotopy α₀ γ α₁ h0 h1 (0, s) = γ 0 := by
  dsimp [reparamHomotopy]
  congr 1
  have hle : (1 - (s : ℝ)) * (0 : ℝ) + (s : ℝ) * (3 * (0 : ℝ) - 1) ≤ 0 := by
    linarith [s.2.1]
  exact projIcc_of_le_left zero_le_one hle

theorem reparamHomotopy_right (α₀ γ α₁ : C(unitInterval, S))
    (h0 : α₀ 1 = γ 0) (h1 : α₁ 1 = γ 1) (s : unitInterval) :
    reparamHomotopy α₀ γ α₁ h0 h1 (1, s) = γ 1 := by
  dsimp [reparamHomotopy]
  congr 1
  have hge : 1 ≤ (1 - (s : ℝ)) * (1 : ℝ) + (s : ℝ) * (3 * (1 : ℝ) - 1) := by
    linarith [s.2.1]
  exact projIcc_of_right_le zero_le_one hge

/-- Graph Minors VII, (11.5) (pages 251–252):
"If $Z \subseteq \Sigma$ is flat and l.a.c., there is an open, flat, l.a.c. set $Y \subseteq \Sigma$
with $Z \subseteq Y$, which may be chosen arc-connected if $Z$ is arc-connected." -/
theorem flat_locallyArcConnected_open_superset (hS : IsSurface S) {Z : Set S}
    (hZ_flat : IsFlat Z) (hZ_lac : IsLocallyArcConnected Z) :
    ∃ Y : Set S, Z ⊆ Y ∧ IsOpen Y ∧ IsFlat Y ∧ IsLocallyArcConnected Y ∧
      (IsArcConnected Z → IsArcConnected Y) := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have : SecondCountableTopology S := secondCountable_of_manifold hS.2.2
  let : MetricSpace S := TopologicalSpace.metrizableSpaceMetric S
  -- Step 1: For each `z ∈ Z`, choose `W z` (open chart ball) and `Δ z ⊆ W z` with `Z ∩ Δ z`
  -- arc-connected.
  have hW_ex : ∀ z : S, ∃ W : Set S, z ∈ W ∧ IsOpen W ∧ IsArcConnected W ∧ IsFlat W ∧
      (∀ γ₀ γ₁ : C(unitInterval, S), range γ₀ ⊆ W → range γ₁ ⊆ W →
        γ₀ 0 = γ₁ 0 → γ₀ 1 = γ₁ 1 → PathsHomotopicRelIn W γ₀ γ₁) := by
    intro z
    obtain ⟨W, _, hzW, hW_open, hW_arc, hW_flat, hW_hom⟩ :=
      exists_chart_ball_subset hS z isOpen_univ (mem_univ z)
    exact ⟨W, hzW, hW_open, hW_arc, hW_flat, hW_hom⟩
  choose W hzW hW_open hW_arc hW_flat hW_hom using hW_ex
  have hΔ_ex : ∀ z : S, ∃ Δ : Set S, Δ ⊆ W z ∧ z ∈ Δ ∧ IsOpen Δ ∧
      (z ∈ Z → IsArcConnected (Z ∩ Δ)) := by
    intro z
    by_cases hz : z ∈ Z
    · obtain ⟨Δ, hΔW, hzΔ, hΔ_open, hZΔ_arc⟩ := hZ_lac z hz (W z) (hW_open z) (hzW z)
      exact ⟨Δ, hΔW, hzΔ, hΔ_open, fun _ => hZΔ_arc⟩
    · exact ⟨W z, Subset.rfl, hzW z, hW_open z, fun hz' => absurd hz' hz⟩
  choose Δ hΔW hzΔ hΔ_open hZΔ_arc using hΔ_ex
  -- Step 2: For each `z`, choose `ε z > 0` such that `closedBall z (ε z) ⊆ Δ z`.
  have hε_ex : ∀ z : S, ∃ ε : ℝ, 0 < ε ∧ closedBall z ε ⊆ Δ z := by
    intro z
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hΔ_open z) z (hzΔ z)
    refine ⟨r / 2, half_pos hr, fun y hy => hball ?_⟩
    exact lt_of_le_of_lt (mem_closedBall.mp hy) (half_lt_self hr)
  choose ε hε_pos hε_ball using hε_ex
  -- Step 3: For each `z`, choose `U z ⊆ ball z (ε z / 3)` open and arc-connected with `z ∈ U z`.
  have hU_ex : ∀ z : S, ∃ U : Set S, U ⊆ ball z (ε z / 3) ∧ z ∈ U ∧ IsOpen U ∧ IsArcConnected U
    := by
    intro z
    have hpos : 0 < ε z / 3 := by linarith [hε_pos z]
    obtain ⟨U, hU_sub, hzU, hU_open, hU_arc, _, _⟩ :=
      exists_chart_ball_subset hS z isOpen_ball (mem_ball_self hpos)
    exact ⟨U, hU_sub, hzU, hU_open, hU_arc⟩
  choose U hU_ball hzU hU_open hU_arc using hU_ex
  -- Key triangle-inequality property (page 252, lines 1029-1033):
  have hU_pair : ∀ z₁ z₂ : S, (U z₁ ∩ U z₂).Nonempty →
      ∃ z ∈ ({z₁, z₂} : Set S), U z₁ ∪ U z₂ ⊆ Δ z := by
    intro z₁ z₂ ⟨u, hu₁, hu₂⟩
    have hu₁' : dist u z₁ < ε z₁ / 3 := mem_ball.mp (hU_ball z₁ hu₁)
    have hu₂' : dist u z₂ < ε z₂ / 3 := mem_ball.mp (hU_ball z₂ hu₂)
    by_cases hle : ε z₁ ≤ ε z₂
    · refine ⟨z₂, Or.inr (mem_singleton z₂), fun y hy => hε_ball z₂ (mem_closedBall.mpr ?_)⟩
      rcases hy with hy₁ | hy₂
      · have hy₁' : dist y z₁ < ε z₁ / 3 := mem_ball.mp (hU_ball z₁ hy₁)
        have htri : dist y z₂ ≤ dist y z₁ + dist z₁ u + dist u z₂ := dist_triangle4 y z₁ u z₂
        rw [dist_comm z₁ u] at htri
        linarith
      · have hy₂' : dist y z₂ < ε z₂ / 3 := mem_ball.mp (hU_ball z₂ hy₂)
        linarith [hε_pos z₂]
    · have hgt : ε z₂ < ε z₁ := not_le.mp hle
      refine ⟨z₁, Or.inl rfl, fun y hy => hε_ball z₁ (mem_closedBall.mpr ?_)⟩
      rcases hy with hy₁ | hy₂
      · have hy₁' : dist y z₁ < ε z₁ / 3 := mem_ball.mp (hU_ball z₁ hy₁)
        linarith [hε_pos z₁]
      · have hy₂' : dist y z₂ < ε z₂ / 3 := mem_ball.mp (hU_ball z₂ hy₂)
        have htri : dist y z₁ ≤ dist y z₂ + dist z₂ u + dist u z₁ := dist_triangle4 y z₂ u z₁
        rw [dist_comm z₂ u] at htri
        linarith
  -- Step 4: Define `Y = ⋃ z ∈ Z, U z` and check `Z ⊆ Y`, `IsOpen Y`, `IsLocallyArcConnected Y`, and
  -- `IsArcConnected Z → IsArcConnected Y`.
  let Y : Set S := ⋃ z ∈ Z, U z
  have hZY : Z ⊆ Y := fun z hz => mem_iUnion₂.mpr ⟨z, hz, hzU z⟩
  have hY_open : IsOpen Y := isOpen_biUnion fun z _ => hU_open z
  have hY_lac : IsLocallyArcConnected Y := by
    intro y hy A hA_open hyA
    obtain ⟨A', hA'_sub, hyA', hA'_open, hA'_arc, _, _⟩ :=
      exists_chart_ball_subset hS y (hY_open.inter hA_open) ⟨hy, hyA⟩
    refine ⟨A', fun w hw => (hA'_sub hw).2, hyA', hA'_open, ?_⟩
    have hYA' : Y ∩ A' = A' := inter_eq_self_of_subset_right fun w hw => (hA'_sub hw).1
    rw [hYA']
    exact hA'_arc
  have hY_arc_imp : IsArcConnected Z → IsArcConnected Y := by
    intro hZ_arc a ha b hb hne
    obtain ⟨z₁, hz₁Z, ha₁⟩ := mem_iUnion₂.mp ha
    obtain ⟨z₂, hz₂Z, hb₂⟩ := mem_iUnion₂.mp hb
    obtain ⟨γ₁, hγ₁, hγ₁0, hγ₁1⟩ := exists_path_of_isArcConnected (hU_arc z₁) ha₁ (hzU z₁)
    obtain ⟨γ₂, hγ₂, hγ₂0, hγ₂1⟩ := exists_path_of_isArcConnected hZ_arc hz₁Z hz₂Z
    obtain ⟨γ₃, hγ₃, hγ₃0, hγ₃1⟩ := exists_path_of_isArcConnected (hU_arc z₂) (hzU z₂) hb₂
    let p₁ : Path a z₁ := ⟨γ₁, hγ₁0, hγ₁1⟩
    let p₂ : Path z₁ z₂ := ⟨γ₂, hγ₂0, hγ₂1⟩
    let p₃ : Path z₂ b := ⟨γ₃, hγ₃0, hγ₃1⟩
    have hj₁ : JoinedIn Y a z₁ := ⟨p₁, fun t => mem_iUnion₂.mpr ⟨z₁, hz₁Z, hγ₁ (mem_range_self t)⟩⟩
    have hj₂ : JoinedIn Y z₁ z₂ := ⟨p₂, fun t => hZY (hγ₂ (mem_range_self t))⟩
    have hj₃ : JoinedIn Y z₂ b := ⟨p₃, fun t => mem_iUnion₂.mpr ⟨z₂, hz₂Z, hγ₃ (mem_range_self t)⟩⟩
    exact ((joinedIn_iff_eq_or_exists_isLineWithEnds' ha hb).mp
      (hj₁.trans (hj₂.trans hj₃))).resolve_left hne
  -- Step 5: Check `IsFlat Y`.
  refine ⟨Y, hZY, hY_open, ?_, hY_lac, hY_arc_imp⟩
  intro φ hφY
  obtain ⟨n, hn, z, hzZ, hpiece⟩ :=
    exists_subdivision_in_open_cover (fun z _ => hU_open z) φ hφY
  let γ₀ : Fin n → C(unitInterval, S) := curvePiece hn φ
  have hmatch₀ : ∀ i : Fin n, γ₀ i 1 = γ₀ (finNext hn i) 0 := curvePiece_match hn φ
  -- For each `i : Fin n`, `γ₀ i 1 ∈ U (z i)` and `z i ∈ U (z i)`, so choose a path `α i` in `U (z
  -- i)` from `z i` to `γ₀ i 1`.
  have hα_ex : ∀ i : Fin n, ∃ α : C(unitInterval, S),
      range α ⊆ U (z i) ∧ α 0 = z i ∧ α 1 = γ₀ i 1 :=
    fun i => exists_path_of_isArcConnected (hU_arc (z i)) (hzU (z i))
      (hpiece i (mem_range_self 1))
  choose α hα_sub hα0 hα1 using hα_ex
  have hα_prev1 : ∀ i : Fin n, α (finPrev hn i) 1 = γ₀ i 0 := by
    intro i
    rw [hα1 (finPrev hn i), hmatch₀ (finPrev hn i), finNext_finPrev hn i]
  -- Define `γ₁ i = whiskerHomotopy (α (finPrev hn i)) (γ₀ i) (α i) (·, 0)` and `ψ i =
  -- whiskerHomotopy ... (·, 1)`.
  let H_reparam : Fin n → C(unitInterval × unitInterval, S) :=
    fun i => reparamHomotopy (α (finPrev hn i)) (γ₀ i) (α i) (hα_prev1 i) (hα1 i)
  let H_whisker : Fin n → C(unitInterval × unitInterval, S) :=
    fun i => whiskerHomotopy (α (finPrev hn i)) (γ₀ i) (α i) (hα_prev1 i) (hα1 i)
  let γ₁ : Fin n → C(unitInterval, S) :=
    fun i => (H_whisker i).comp ⟨fun t => (t, 0), continuous_id.prodMk continuous_const⟩
  let ψ : Fin n → C(unitInterval, S) :=
    fun i => (H_whisker i).comp ⟨fun t => (t, 1), continuous_id.prodMk continuous_const⟩
  have hmatch₁ : ∀ i : Fin n, γ₁ i 1 = γ₁ (finNext hn i) 0 := by
    intro i
    change H_whisker i (1, 0) = H_whisker (finNext hn i) (0, 0)
    rw [whiskerHomotopy_right, whiskerHomotopy_left, finPrev_finNext]
  have hmatch_ψ : ∀ i : Fin n, ψ i 1 = ψ (finNext hn i) 0 := by
    intro i
    change H_whisker i (1, 1) = H_whisker (finNext hn i) (0, 1)
    rw [whiskerHomotopy_right, whiskerHomotopy_left, finPrev_finNext]
  have hhom₁ : ClosedCurvesHomotopicIn univ φ (concatLoop hn γ₁ hmatch₁) := by
    rw [← concatLoop_curvePiece hn φ]
    refine concatLoop_homotopic hn γ₀ γ₁ hmatch₀ hmatch₁ H_reparam (fun _ _ => mem_univ _)
      (fun i t => reparamHomotopy_zero _ _ _ _ _ t)
      (fun i t => reparamHomotopy_one _ _ _ _ _ t) (fun i s => ?_)
    show H_reparam i (1, s) = H_reparam (finNext hn i) (0, s)
    rw [reparamHomotopy_right, reparamHomotopy_left]
    exact hmatch₀ i
  have hhom₂ : ClosedCurvesHomotopicIn univ (concatLoop hn γ₁ hmatch₁) (concatLoop hn ψ hmatch_ψ)
    := by
    refine concatLoop_homotopic hn γ₁ ψ hmatch₁ hmatch_ψ H_whisker (fun _ _ => mem_univ _)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun i s => ?_)
    show H_whisker i (1, s) = H_whisker (finNext hn i) (0, s)
    rw [whiskerHomotopy_right, whiskerHomotopy_left, finPrev_finNext]
  -- Now for each `i : Fin n`, `γ₀ i 0 ∈ U (z (finPrev hn i)) ∩ U (z i)`, so `U (z (finPrev hn i)) ∪
  -- U (z i) ⊆ Δ (w i)` for some `w i ∈ Z`.
  have hψ_ends : ∀ i : Fin n, ψ i 0 = z (finPrev hn i) ∧ ψ i 1 = z i := by
    intro i
    have hsymm1 : symm (1 : unitInterval) = 0 := by ext; simp
    refine ⟨?_, ?_⟩
    · change H_whisker i (0, 1) = z (finPrev hn i)
      rw [whiskerHomotopy_left, hsymm1, hα0]
    · change H_whisker i (1, 1) = z i
      rw [whiskerHomotopy_right, hsymm1, hα0]
  have hθ_ex : ∀ i : Fin n, ∃ (θ : C(unitInterval, S)) (H : C(unitInterval × unitInterval, S)),
      range θ ⊆ Z ∧ θ 0 = z (finPrev hn i) ∧ θ 1 = z i ∧
      (∀ t, H (t, 0) = ψ i t) ∧ (∀ t, H (t, 1) = θ t) ∧
      (∀ s, H (0, s) = z (finPrev hn i)) ∧ (∀ s, H (1, s) = z i) := by
    intro i
    have hnonempty : (U (z (finPrev hn i)) ∩ U (z i)).Nonempty :=
      ⟨γ₀ i 0, by rw [← hα_prev1 i]; exact hα_sub (finPrev hn i) (mem_range_self 1),
        hpiece i (mem_range_self 0)⟩
    obtain ⟨w, hw_pair, hU_sub_Δ⟩ := hU_pair (z (finPrev hn i)) (z i) hnonempty
    have hwZ : w ∈ Z := by
      rcases hw_pair with rfl | h_eq
      · exact hzZ (finPrev hn i)
      · rw [mem_singleton_iff.mp h_eq]
        exact hzZ i
    have hz_prev_Δ : z (finPrev hn i) ∈ Z ∩ Δ w :=
      ⟨hzZ (finPrev hn i), hU_sub_Δ (Or.inl (hzU (z (finPrev hn i))))⟩
    have hz_curr_Δ : z i ∈ Z ∩ Δ w :=
      ⟨hzZ i, hU_sub_Δ (Or.inr (hzU (z i)))⟩
    obtain ⟨θ, hθ_sub, hθ0, hθ1⟩ :=
      exists_path_of_isArcConnected (hZΔ_arc w hwZ) hz_prev_Δ hz_curr_Δ
    have hψ_W : range (ψ i) ⊆ W w := by
      rintro _ ⟨t, rfl⟩
      exact hΔW w (hU_sub_Δ (whiskerHomotopy_mem (α (finPrev hn i)) (γ₀ i) (α i)
        (hα_prev1 i) (hα1 i) (hα_sub (finPrev hn i)) (hpiece i) (hα_sub i) (t, 1)))
    have hθ_W : range θ ⊆ W w := fun x hx => hΔW w (hθ_sub hx).2
    obtain ⟨H, _, hH0, hH1, hHs0, hHs1⟩ :=
      hW_hom w (ψ i) θ hψ_W hθ_W ((hψ_ends i).1.trans hθ0.symm) ((hψ_ends i).2.trans hθ1.symm)
    refine ⟨θ, H, fun x hx => (hθ_sub hx).1, hθ0, hθ1, hH0, hH1, ?_, ?_⟩
    · intro s; rw [hHs0 s, (hψ_ends i).1]
    · intro s; rw [hHs1 s, (hψ_ends i).2]
  choose θ H_θ hθ_Z hθ0 hθ1 hHθ0 hHθ1 hHθ_left hHθ_right using hθ_ex
  have hmatch_θ : ∀ i : Fin n, θ i 1 = θ (finNext hn i) 0 := by
    intro i
    rw [hθ1 i, hθ0 (finNext hn i), finPrev_finNext]
  have hhom₃ : ClosedCurvesHomotopicIn univ (concatLoop hn ψ hmatch_ψ) (concatLoop hn θ hmatch_θ)
    := by
    refine concatLoop_homotopic hn ψ θ hmatch_ψ hmatch_θ H_θ (fun _ _ => mem_univ _)
      hHθ0 hHθ1 (fun i s => ?_)
    rw [hHθ_right i s, hHθ_left (finNext hn i) s, finPrev_finNext]
  have hθ_range : range (concatLoop hn θ hmatch_θ) ⊆ Z := by
    rw [range_concatLoop]
    exact iUnion_subset hθ_Z
  obtain ⟨c, hc_univ, hθ_null⟩ := hZ_flat (concatLoop hn θ hmatch_θ) hθ_range
  exact ⟨c, hc_univ, closedCurvesHomotopicIn_trans hhom₁
    (closedCurvesHomotopicIn_trans hhom₂ (closedCurvesHomotopicIn_trans hhom₃ hθ_null))⟩

end GraphMinor.GM07
