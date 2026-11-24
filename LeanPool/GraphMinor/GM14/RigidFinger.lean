/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.RigidMap
import LeanPool.GraphMinor.GM11.ArcDrawings
import LeanPool.GraphMinor.Surface.ArcTools
import LeanPool.GraphMinor.GM11.PerimeterPull
import LeanPool.GraphMinor.GM11.EdgeSides
import LeanPool.GraphMinor.Surface.SphereDisc
import LeanPool.GraphMinor.GM12.Section4ParallelLine
import LeanPool.GraphMinor.GM14.DiscSlope
import LeanPool.GraphMinor.Surface.Cap
import LeanPool.GraphMinor.Surface.DiscArcs
import LeanPool.GraphMinor.Surface.DiscUnion
import LeanPool.GraphMinor.Surface.Lunes
import LeanPool.GraphMinor.Surface.InvarianceOfDomain
import LeanPool.GraphMinor.Surface.PushOff

/-!
# A finger of a closed disc

Let `E` be a closed disc in a closed surface, let `K ⊆ E` be compact, and let `x ∈ K` be off
`bd(E)`. Let a
line run from a point outside `E` to `x`, and meet `K` only in `x`. We remove from `E` a thin finger
along the
line, up to `x`. Then `E` stays a closed disc that holds `K`, and `x` joins the points of `K` on the
boundary
(`exists_finger`). We repeat this in `exists_disc_around`, to bring a finite set of points of `K` to
the
boundary.

To make the finger, take a parallel copy of the line, by `exists_parallel_line`. The last parts of
the two
lines, from where they enter `E`, form a chord through `x`. In one half of `E` we use coordinates in
which
the chord is straight. In those coordinates the finger is the region under a graph, of height at
most half
the distance to `K`.
-/

@[expose] public section

namespace GraphMinor.GM14.Whitney

open Set Topology Metric GraphMinor.Surface GraphMinor.GM11

universe u

variable {T : Type u} [TopologicalSpace T]

/-- The last part of a line that ends inside a closed disc and starts outside it. -/
theorem exists_last_part (hS : IsClosedSurface T) {E ℓ : Set T} {p x : T} (hE : IsClosedDisc E)
    (hℓ : IsLineWithEnds ℓ p x) (hp : p ∉ E) (hx : x ∈ E) (hxb : x ∉ discBd E) :
    ∃ (z : T) (ℓ' : Set T), z ∈ discBd E ∧ IsLineWithEnds ℓ' z x ∧ ℓ' ⊆ ℓ ∧ ℓ' ⊆ E ∧
      ℓ' ∩ discBd E = {z} := by
  have ht2 : T2Space T := hS.2.1
  have hfr : frontier E = discBd E := IsClosedDisc.frontier_eq_discBd hS hE
  have hin : ∀ {y}, y ∈ E → y ∉ discBd E → y ∈ interior E := fun {y} hy hyb => by
    by_contra hn
    apply hyb
    rw [← hfr, frontier, hE.isClosed.closure_eq]
    exact ⟨hy, hn⟩
  obtain ⟨f, h0, h1⟩ := hℓ
  let γ : ℝ → T := fun t => (f (projIcc 0 1 zero_le_one t)).1
  have hγc : Continuous γ :=
    continuous_subtype_val.comp (f.continuous.comp continuous_projIcc)
  have hγi : InjOn γ (Icc 0 1) := fun s hs t ht h => by
    have := f.injective (Subtype.ext h)
    have h₃ := congrArg Subtype.val this
    simpa [projIcc_of_mem zero_le_one hs, projIcc_of_mem zero_le_one ht] using h₃
  have hγ0 : γ 0 = p := by simpa [γ] using h0
  have hγ1 : γ 1 = x := by simpa [γ] using h1
  let C : Set ℝ := Icc 0 1 ∩ γ ⁻¹' (interior E)ᶜ
  have hCc : IsCompact C :=
    isCompact_Icc.inter_right (isOpen_interior.isClosed_compl.preimage hγc)
  have hCne : C.Nonempty := ⟨0, ⟨by simp, by
    rw [mem_preimage, hγ0]
    exact fun h => hp (interior_subset h)⟩⟩
  obtain ⟨t₀, ht₀, hmax⟩ := hCc.exists_isGreatest hCne |>.imp fun _ h => h
  have ht₁ : t₀ < 1 := by
    refine lt_of_le_of_ne ht₀.1.2 fun h => ?_
    have := ht₀.2
    rw [mem_preimage, h, hγ1] at this
    exact this (hin hx hxb)
  have hafter : ∀ t, t₀ < t → t ≤ 1 → γ t ∈ interior E := fun t h₁ h₂ => by
    by_contra hn
    exact absurd (hmax ⟨⟨ht₀.1.1.trans h₁.le, h₂⟩, hn⟩) (not_le.mpr h₁)
  have hin_E : ∀ t ∈ Icc t₀ 1, γ t ∈ E := by
    intro t ht
    have hsub : Ioc t₀ 1 ⊆ γ ⁻¹' E := fun s hs => by
      have h₁ : γ s ∈ E := interior_subset (hafter s hs.1 hs.2)
      exact h₁
    have hcl : Icc t₀ 1 ⊆ closure (Ioc t₀ 1) := by
      rw [closure_Ioc ht₁.ne]
    exact closure_minimal hsub (hE.isClosed.preimage hγc) (hcl ht)
  have hz : γ t₀ ∈ discBd E := by
    rw [← hfr, frontier, hE.isClosed.closure_eq]
    exact ⟨hin_E t₀ ⟨le_rfl, ht₁.le⟩, ht₀.2⟩
  have hsubI : Icc t₀ 1 ⊆ Icc 0 1 := Icc_subset_Icc_left ht₀.1.1
  refine ⟨γ t₀, γ '' Icc t₀ 1, hz, ?_, ?_, ?_, ?_⟩
  · have := isLine_of_injOn hγc ht₁ (hγi.mono hsubI)
    rwa [hγ1] at this
  · rintro _ ⟨t, -, rfl⟩
    exact (f _).2
  · exact image_subset_iff.mpr hin_E
  · apply subset_antisymm
    · rintro _ ⟨⟨t, ht, rfl⟩, htb⟩
      rcases ht.1.lt_or_eq with h | h
      · have := hafter t h ht.2
        rw [← hfr] at htb
        exact absurd this (disjoint_left.mp disjoint_interior_frontier · htb)
      · rw [h]
        rfl
    · rintro _ rfl
      exact ⟨⟨t₀, ⟨le_rfl, ht₁.le⟩, rfl⟩, hz⟩

theorem hl_start {L : Set T} {u v : T} (h : IsLineWithEnds L u v) : u ∈ L := by
  obtain ⟨f, h0, -⟩ := h
  exact h0 ▸ (f 0).2

theorem hl_end {L : Set T} {u v : T} (h : IsLineWithEnds L u v) : v ∈ L := by
  obtain ⟨f, -, h1⟩ := h
  exact h1 ▸ (f 1).2

/-- The upper rectangle. -/
def Rect : Set ℂ := Icc (-1 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1

/-- Its base. -/
noncomputable def Base : Set ℂ := segment ℝ (-1 : ℂ) 1

theorem mem_Rect {z : ℂ} : z ∈ Rect ↔ z.re ∈ Icc (-1 : ℝ) 1 ∧ z.im ∈ Icc (0 : ℝ) 1 := Iff.rfl

theorem mem_Base {z : ℂ} : z ∈ Base ↔ z.re ∈ Icc (-1 : ℝ) 1 ∧ z.im = 0 := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    have h₁ : (a • (-1 : ℂ) + b • (1 : ℂ)).re = b - a := by simp; ring
    rw [h₁]
    refine ⟨⟨by linarith, by linarith⟩, by simp⟩
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    refine ⟨(1 - z.re) / 2, (1 + z.re) / 2, by linarith, by linarith, by ring, ?_⟩
    apply Complex.ext
    · simp
      ring
    · simp [h₃]

theorem base_sub_frontier : Base ⊆ discBd Rect := by
  have hb := (isClosedDisc_rect (a := -1) (b := 1) (c := 0) (d := 1) (by norm_num) (by norm_num)).2
  change Base ⊆ discBd (Icc (-1 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1)
  rw [hb, Complex.frontier_reProdIm]
  rintro z hz
  obtain ⟨h₁, h₂⟩ := mem_Base.mp hz
  refine Or.inl ⟨?_, ?_⟩
  · change z.re ∈ closure _
    rw [closure_Icc]
    exact h₁
  · change z.im ∈ frontier _
    rw [frontier_Icc (by norm_num : (0 : ℝ) ≤ 1)]
    exact Or.inl h₂

/-- Coordinates on a closed disc in which a line of its boundary is the base of the rectangle. -/
theorem exists_rect_chart [T2Space T] {Δ c : Set T} {a b : T} (hΔ : IsClosedDisc Δ)
    (hc : IsLineWithEnds c a b) (hcb : c ⊆ discBd Δ) :
    ∃ (f : T → ℂ) (f' : ℂ → T), PH Δ Rect f f' ∧ f '' c = Base ∧ f a = -1 ∧ f b = 1 := by
  have hRd : IsClosedDisc Rect :=
    (isClosedDisc_rect (a := -1) (b := 1) (c := 0) (d := 1) (by norm_num) (by norm_num)).1
  have hB : IsLineWithEnds Base (-1) 1 := isLineWithEnds_segment (by norm_num)
  obtain ⟨u, v, huv, hru, hu0, hu1, hun⟩ := exists_arcs_of_line hΔ.isOArc_discBd hc hcb
  obtain ⟨u', v', huv', hru', hu0', hu1', hun'⟩ :=
    exists_arcs_of_line hRd.isOArc_discBd hB base_sub_frontier
  have hl₁ : IsLineWithEnds (range v) a b := by
    have := huv.arc_right.isLineWithEnds
    rwa [huv.zero, huv.one, hu0, hu1] at this
  have hl₂ : IsLineWithEnds (range v') (-1) 1 := by
    have := huv'.arc_right.isLineWithEnds
    rwa [huv'.zero, huv'.one, hu0', hu1'] at this
  have hne : Nonempty T := ⟨a⟩
  obtain ⟨g₁, g₁', hP₁, ha₁, hb₁⟩ := exists_line_PH hc hB
  obtain ⟨g₂, g₂', hP₂, ha₂, hb₂⟩ := exists_line_PH hl₁ hl₂
  have hmeet : ∀ {s t}, u s = v t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := fun {s t} h
    => huv.meet s t h
  have hmeet' : ∀ {s t}, u' s = v' t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) :=
    fun {s t} h => huv'.meet s t h
  have hend : ∀ {x}, x ∈ c → x ∈ range v → x = a ∨ x = b := by
    rintro x hx ⟨t, rfl⟩
    rw [← hru] at hx
    obtain ⟨s, hs⟩ := hx
    rcases hmeet hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (by rw [← hs, hu0])
    · exact Or.inr (by rw [← hs, hu1])
  have hend' : ∀ {x}, x ∈ Base → x ∈ range v' → x = -1 ∨ x = 1 := by
    rintro x hx ⟨t, rfl⟩
    rw [← hru'] at hx
    obtain ⟨s, hs⟩ := hx
    rcases hmeet' hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (by rw [← hs, hu0'])
    · exact Or.inr (by rw [← hs, hu1'])
  have hg₁' : g₁' (-1) = a := by
    have := hP₁.2.2.1 (hl_start hc)
    rwa [ha₁] at this
  have hg₁'' : g₁' 1 = b := by
    have := hP₁.2.2.1 (hl_end hc)
    rwa [hb₁] at this
  have hg₂' : g₂' (-1) = a := by
    have := hP₂.2.2.1 (hl_start hl₁)
    rwa [ha₂] at this
  have hg₂'' : g₂' 1 = b := by
    have := hP₂.2.2.1 (hl_end hl₁)
    rwa [hb₂] at this
  let A : Bool → Set T := fun i => if i then c else range v
  let B' : Bool → Set ℂ := fun i => if i then Base else range v'
  let k : Bool → T → ℂ := fun i => if i then g₁ else g₂
  let k' : Bool → ℂ → T := fun i => if i then g₁' else g₂'
  obtain ⟨F, F', hF, hFe, hFe'⟩ := exists_glue (A := A) (B := B') (f := k) (f' := k')
    (by
      rintro (_ | _)
      · exact (isCompact_range huv.arc_right.1).isClosed
      · exact (hru ▸ isCompact_range huv.arc_left.1).isClosed)
    (by
      rintro (_ | _)
      · exact (isCompact_range huv'.arc_right.1).isClosed
      · exact (hru' ▸ isCompact_range huv'.arc_left.1).isClosed)
    (by
      rintro (_ | _)
      · exact hP₂
      · exact hP₁)
    (by
      rintro (_ | _) (_ | _) x hx hx'
      · rfl
      · rcases hend hx' hx with rfl | rfl
        · exact ha₂.trans ha₁.symm
        · exact hb₂.trans hb₁.symm
      · rcases hend hx hx' with rfl | rfl
        · exact ha₁.trans ha₂.symm
        · exact hb₁.trans hb₂.symm
      · rfl)
    (by
      rintro (_ | _) (_ | _) x hx hx'
      · rfl
      · rcases hend' hx' hx with rfl | rfl
        · exact hg₂'.trans hg₁'.symm
        · exact hg₂''.trans hg₁''.symm
      · rcases hend' hx hx' with rfl | rfl
        · exact hg₁'.trans hg₂'.symm
        · exact hg₁''.trans hg₂''.symm
      · rfl)
  have hUA : (⋃ i, A i) = discBd Δ := by
    rw [← hun, hru]
    ext z
    simp only [mem_iUnion, Bool.exists_bool, A, mem_union]
    simp [or_comm]
  have hUB : (⋃ i, B' i) = discBd Rect := by
    rw [← hun', hru']
    ext z
    simp only [mem_iUnion, Bool.exists_bool, B', mem_union]
    simp [or_comm]
  rw [hUA, hUB] at hF
  obtain ⟨f, f', hf, he, he'⟩ := exists_disc_PH hΔ hRd hF
  have hcb' : ∀ {x}, x ∈ c → f x = g₁ x := fun {x} hx => by
    rw [he (hcb hx)]
    exact hFe true hx
  refine ⟨f, f', hf, ?_, ?_, ?_⟩
  · rw [image_congr fun x hx => hcb' hx]
    exact hP₁.image_eq
  · rw [hcb' (hl_start hc), ha₁]
  · rw [hcb' (hl_end hc), hb₁]

section Graph

variable {w : ℝ → ℝ}

/-- The part of the rectangle over a graph. -/
def Over (w : ℝ → ℝ) : Set ℂ := {z | z.re ∈ Icc (-1 : ℝ) 1 ∧ w z.re ≤ z.im ∧ z.im ≤ 1}

/-- Pushing the rectangle up to the part over a graph. -/
noncomputable def raise (w : ℝ → ℝ) (z : ℂ) : ℂ := ⟨z.re, w z.re + z.im * (1 - w z.re)⟩

/-- The inverse of `raise`. -/
noncomputable def lower (w : ℝ → ℝ) (z : ℂ) : ℂ := ⟨z.re, (z.im - w z.re) / (1 - w z.re)⟩

theorem raise_PH (hw : Continuous w) (_h0 : ∀ s, 0 ≤ w s) (h1 : ∀ s, w s ≤ 1 / 2) :
    PH Rect (Over w) (raise w) (lower w) := by
  have hpos : ∀ s, 0 < 1 - w s := fun s => by linarith [h1 s]
  have hmk : ∀ {a b : ℂ → ℝ}, Continuous a → Continuous b →
      Continuous fun z : ℂ => (⟨a z, b z⟩ : ℂ) := fun ha hb =>
    Complex.equivRealProdCLM.symm.continuous.comp (ha.prodMk hb)
  have hwc : Continuous fun z : ℂ => w z.re := hw.comp Complex.continuous_re
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro z ⟨h₁, h₂⟩
    refine ⟨h₁, ?_, ?_⟩
    · have := mul_nonneg h₂.1 (hpos z.re).le
      change w z.re ≤ w z.re + z.im * (1 - w z.re)
      linarith
    · have := mul_nonneg (sub_nonneg.mpr h₂.2) (hpos z.re).le
      change w z.re + z.im * (1 - w z.re) ≤ 1
      nlinarith
  · rintro z ⟨h₁, h₂, h₃⟩
    refine ⟨h₁, ?_, ?_⟩
    · exact div_nonneg (sub_nonneg.mpr h₂) (hpos z.re).le
    · exact (div_le_one (hpos z.re)).mpr (by linarith)
  · intro z _
    apply Complex.ext
    · rfl
    · change (w z.re + z.im * (1 - w z.re) - w z.re) / (1 - w z.re) = z.im
      field_simp [(hpos z.re).ne']
      ring
  · intro z _
    apply Complex.ext
    · rfl
    · change w z.re + (z.im - w z.re) / (1 - w z.re) * (1 - w z.re) = z.im
      field_simp [(hpos z.re).ne']
      ring
  · exact (hmk Complex.continuous_re
      (hwc.add (Complex.continuous_im.mul (continuous_const.sub hwc)))).continuousOn
  · exact (hmk Complex.continuous_re
      ((Complex.continuous_im.sub hwc).div (continuous_const.sub hwc)
        fun z => (hpos z.re).ne')).continuousOn

end Graph

private theorem base_left_of_tip_avoids_obstacle
    {T : Type u}
    [TopologicalSpace T]
    {K : Set T}
    {ℓ : Set T}
    {x : T}
    (hℓK : ℓ ∩ K ⊆ {x})
    (z₁ : T)
    (ℓ₁ : Set T)
    (hl₁ : IsLineWithEnds ℓ₁ z₁ x)
    (hsub₁ : ℓ₁ ⊆ ℓ)
    (ℓ₂ : Set T)
    (hxℓ₁ : x ∈ ℓ₁)
    (Δ₁ : Set T)
    (f : T → ℂ)
    (f' : ℂ → T)
    (hf : PH Δ₁ Rect f f')
    (hfc : f '' (ℓ₁ ∪ ℓ₂) = Base)
    (hf₁ : f z₁ = -1)
    (hc_sub : ℓ₁ ∪ ℓ₂ ⊆ Δ₁)
    (s₀ : ℝ)
    (hfxe : f x = ↑s₀) :
    ∀ s ∈ Ico (-1) s₀, ↑s ∉ (f '' (K ∩ Δ₁)) := by
  let K' := f '' (K ∩ Δ₁)
  rintro s ⟨h₁, h₂⟩ ⟨y, ⟨hyK, hyΔ⟩, hy⟩
  have hsub : Icc (-1 : ℝ) s₀ ⊆ Complex.re '' (f '' ℓ₁) := by
    have hpre : IsPreconnected (Complex.re '' (f '' ℓ₁)) := by
      have hlc : IsPreconnected ℓ₁ := by
        obtain ⟨q, -, -⟩ := id hl₁
        have hr : range (fun c : unitInterval => (q c).1) = ℓ₁ := by
          ext z
          constructor
          · rintro ⟨c, rfl⟩
            exact (q c).2
          · intro hz
            exact ⟨q.symm ⟨z, hz⟩, by simp⟩
        rw [← hr]
        exact isPreconnected_range (continuous_subtype_val.comp q.continuous)
      have h₃ := hlc.image f (hf.2.2.2.2.1.mono (subset_union_left.trans hc_sub))
      exact h₃.image _ Complex.continuous_re.continuousOn
    have ho := hpre.ordConnected
    exact ho.out ⟨f z₁, mem_image_of_mem f (hl_start hl₁), by rw [hf₁]; simp⟩
      ⟨f x, mem_image_of_mem f hxℓ₁, by rw [hfxe]; simp⟩
  obtain ⟨_, ⟨q, hq, rfl⟩, hqe⟩ := hsub ⟨h₁, h₂.le⟩
  have hqb : f q ∈ Base := hfc ▸ mem_image_of_mem f (Or.inl hq)
  have hqs : f q = (s : ℂ) := Complex.ext (by simpa using hqe) (by simpa using
    (mem_Base.mp hqb).2)
  have hqy : q = y := hf.injOn (hc_sub (Or.inl hq)) hyΔ (hqs.trans hy.symm)
  subst hqy
  have hqx : q = x := by
    have := hℓK ⟨hsub₁ hq, hyK⟩
    exact this
  rw [hqx, hfxe] at hqs
  have : s₀ = s := by exact_mod_cast hqs
  exact h₂.ne this.symm

private theorem mem_right_base_segment
    (s₀ : ℝ)
    (hs₁ : s₀ < 1) :
    ∀ {z : ℂ}, z ∈ segment ℝ (↑s₀) 1 ↔ z.re ∈ Icc s₀ 1 ∧ z.im = 0 := by
  intro z
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    have h₁ : (a • (s₀ : ℂ) + b • (1 : ℂ)).re = a * s₀ + b := by simp
    rw [h₁]
    refine ⟨⟨by nlinarith, by nlinarith⟩, by simp⟩
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    have hd : 0 < 1 - s₀ := by linarith
    have key : (1 - z.re) / (1 - s₀) * s₀ + (z.re - s₀) / (1 - s₀) = z.re := by
      field_simp
      ring
    refine ⟨(1 - z.re) / (1 - s₀), (z.re - s₀) / (1 - s₀), div_nonneg (by linarith) hd.le,
      div_nonneg (by linarith) hd.le, by field_simp; ring, ?_⟩
    apply Complex.ext
    · rw [Complex.add_re, Complex.smul_re, Complex.smul_re]
      simp only [Complex.ofReal_re, Complex.one_re, smul_eq_mul, mul_one]
      exact key
    · rw [Complex.add_im, Complex.smul_im, Complex.smul_im]
      simp [h₃]

private theorem raised_disc_meets_other_half_along_right_base
    {T : Type u}
    [TopologicalSpace T]
    (ℓ₁ : Set T)
    (ℓ₂ : Set T)
    (Δ₁ : Set T)
    (Δ₂ : Set T)
    (hmeet : Δ₁ ∩ Δ₂ = ℓ₁ ∪ ℓ₂)
    (hcbd₂ : ℓ₁ ∪ ℓ₂ ⊆ discBd Δ₂)
    (f : T → ℂ)
    (f' : ℂ → T)
    (hf : PH Δ₁ Rect f f')
    (hfc : f '' (ℓ₁ ∪ ℓ₂) = Base)
    (s₀ : ℝ) (hs₀ : s₀ ∈ Icc (-1) 1)
    (w : ℝ → ℝ)
    (hwright : ∀ (s : ℝ), s₀ ≤ s → w s = 0)
    (hwleft : ∀ s ∈ Ico (-1) s₀, 0 < w s)
    (hUpR : Over w ⊆ Rect)
    (hΔ'sub : f' '' Over w ⊆ Δ₁)
    (hmem₀ : ∀ {z : ℂ}, z ∈ segment ℝ (↑s₀) 1 ↔ z.re ∈ Icc s₀ 1 ∧ z.im = 0)
    (hLc : f' '' segment ℝ (↑s₀) 1 ⊆ ℓ₁ ∪ ℓ₂) :
    f' '' Over w ∩ Δ₂ = f' '' segment ℝ (↑s₀) 1 := by
  apply subset_antisymm
  · rintro _ ⟨⟨u, hu, rfl⟩, hu₂⟩
    have hin : f' u ∈ ℓ₁ ∪ ℓ₂ := hmeet ▸ ⟨hΔ'sub (mem_image_of_mem f' hu), hu₂⟩
    have hub : f (f' u) ∈ Base := hfc ▸ mem_image_of_mem f hin
    rw [hf.right (hUpR hu)] at hub
    obtain ⟨h₁, h₂⟩ := mem_Base.mp hub
    refine mem_image_of_mem f' (hmem₀.mpr ⟨⟨?_, h₁.2⟩, h₂⟩)
    by_contra hn
    have := hwleft u.re ⟨h₁.1, not_le.mp hn⟩
    have h₃ := hu.2.1
    rw [h₂] at h₃
    linarith
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨mem_image_of_mem f' ?_, ?_⟩
    · obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hmem₀.mp hu
      refine ⟨⟨by linarith [hs₀.1], h₂⟩, ?_, by rw [h₃]; norm_num⟩
      rw [hwright _ h₁, h₃]
    · exact Surface.discBd_subset _ (hcbd₂ (hLc (mem_image_of_mem f' hu)))

private theorem raised_disc_union_contains_obstacle
    {T : Type u}
    [TopologicalSpace T]
    {E : Set T}
    {K : Set T}
    (hKE : K ⊆ E)
    (Δ₁ : Set T)
    (Δ₂ : Set T)
    (f : T → ℂ)
    (f' : ℂ → T)
    (hf : PH Δ₁ Rect f f')
    (s₀ : ℝ)
    (w : ℝ → ℝ)
    (hwright : ∀ (s : ℝ), s₀ ≤ s → w s = 0)
    (hwle : ∀ z ∈ (f '' (K ∩ Δ₁)), 0 ≤ z.im → z.re < s₀ → w z.re ≤ z.im / 2)
    (hmemE : ∀ {z : T}, z ∈ E → z ∈ Δ₁ ∨ z ∈ Δ₂) :
    K ⊆ f' '' Over w ∪ Δ₂ := by
  let K' := f '' (K ∩ Δ₁)
  intro z hz
  rcases hmemE (hKE hz) with h₁ | h₁
  · refine Or.inl ⟨f z, ?_, hf.left h₁⟩
    obtain ⟨h₃, h₄⟩ := hf.1 h₁
    refine ⟨h₃, ?_, h₄.2⟩
    by_cases hlt : (f z).re < s₀
    · have := hwle (f z) ⟨z, ⟨hz, h₁⟩, rfl⟩ h₄.1 hlt
      linarith [h₄.1]
    · rw [hwright _ (not_lt.mp hlt)]
      exact h₄.1
  · exact Or.inr h₁

private theorem removed_points_below_raising_graph
    {T : Type u}
    [TopologicalSpace T]
    {E : Set T}
    (Δ₁ : Set T)
    (Δ₂ : Set T)
    (f : T → ℂ)
    (f' : ℂ → T)
    (hf : PH Δ₁ Rect f f')
    (s₀ : ℝ)
    (w : ℝ → ℝ)
    (hwright : ∀ (s : ℝ), s₀ ≤ s → w s = 0)
    (hmemE : ∀ {z : T}, z ∈ E → z ∈ Δ₁ ∨ z ∈ Δ₂) :
    E \ (f' '' Over w ∪ Δ₂) ⊆ f' '' ({z | z.re ∈ Icc (-1) s₀ ∧ 0 ≤ z.im ∧ z.im ≤ w z.re}) := by
  let FgC : Set ℂ := {z | z.re ∈ Icc (-1) s₀ ∧ 0 ≤ z.im ∧ z.im ≤ w z.re}
  rintro y ⟨hyE, hyn⟩
  have hyΔ : y ∈ Δ₁ := (hmemE hyE).resolve_right fun h => hyn (Or.inr h)
  obtain ⟨h₃, h₄⟩ := hf.1 hyΔ
  refine ⟨f y, ?_, hf.left hyΔ⟩
  have hlt : (f y).im < w (f y).re := by
    by_contra hn
    exact hyn (Or.inl ⟨f y, ⟨h₃, not_lt.mp hn, h₄.2⟩, hf.left hyΔ⟩)
  refine ⟨⟨h₃.1, ?_⟩, h₄.1, hlt.le⟩
  by_contra hn
  rw [hwright _ (not_le.mp hn).le] at hlt
  linarith [h₄.1]

private theorem raising_graph_meets_obstacle_at_tip
    {T : Type u}
    [TopologicalSpace T]
    {K : Set T}
    {x : T}
    (Δ₁ : Set T)
    (f : T → ℂ)
    (f' : ℂ → T)
    (hf : PH Δ₁ Rect f f')
    (s₀ : ℝ)
    (hoff : ∀ s ∈ Ico (-1) s₀, ↑s ∉ (f '' (K ∩ Δ₁)))
    (w : ℝ → ℝ)
    (hwright : ∀ (s : ℝ), s₀ ≤ s → w s = 0)
    (hwle : ∀ z ∈ (f '' (K ∩ Δ₁)), 0 ≤ z.im → z.re < s₀ → w z.re ≤ z.im / 2)
    (hf'x : f' ↑s₀ = x)
    (hFgR : ({z | z.re ∈ Icc (-1) s₀ ∧ 0 ≤ z.im ∧ z.im ≤ w z.re}) ⊆ Rect) :
    ∀ {z : T}, z ∈ K → z ∈ f' '' ({z | z.re ∈ Icc (-1) s₀ ∧ 0 ≤ z.im ∧ z.im ≤ w z.re}) → z = x := by
  let K' := f '' (K ∩ Δ₁)
  let FgC : Set ℂ := {z | z.re ∈ Icc (-1) s₀ ∧ 0 ≤ z.im ∧ z.im ≤ w z.re}
  rintro z hz ⟨u, hu, rfl⟩
  have huR := hFgR hu
  have hzΔ : f' u ∈ Δ₁ := hf.2.1 huR
  have hfu : u ∈ K' := ⟨f' u, ⟨hz, hzΔ⟩, hf.right huR⟩
  rcases hu.1.2.lt_or_eq with hlt | heq
  · have h₁ := hwle u hfu hu.2.1 hlt
    have h₂ : u.im = 0 := by linarith [hu.2.1, hu.2.2]
    have h₃ : u = (u.re : ℂ) := Complex.ext (by simp) (by simp [h₂])
    exact absurd (h₃ ▸ hfu) (hoff u.re ⟨hu.1.1, hlt⟩)
  · have h₁ : u.im = 0 := by
      have := hu.2.2
      rw [hwright _ heq.ge] at this
      linarith [hu.2.1]
    have h₃ : u = (s₀ : ℂ) := Complex.ext (by simp [heq]) (by simp [h₁])
    rw [h₃, hf'x]

private theorem raised_disc_boundary_meets_obstacle_at_tip
    {T : Type u}
    [TopologicalSpace T]
    [T2Space T]
    (hS : IsClosedSurface T)
    {E : Set T}
    {K : Set T}
    {x : T}
    (hE : IsClosedDisc E)
    (hKE : K ⊆ E)
    (hx : x ∈ K)
    (hfrE : frontier E = discBd E)
    (ℓ₁ : Set T)
    (ℓ₂ : Set T)
    (Δ₁ : Set T)
    (Δ₂ : Set T)
    (hmeet : Δ₁ ∩ Δ₂ = ℓ₁ ∪ ℓ₂)
    (f : T → ℂ)
    (f' : ℂ → T)
    (hf : PH Δ₁ Rect f f')
    (hfc : f '' (ℓ₁ ∪ ℓ₂) = Base)
    (s₀ : ℝ)
    (hs₀ : s₀ ∈ Icc (-1) 1)
    (w : ℝ → ℝ)
    (hwc : Continuous w)
    (hw0 : ∀ (s : ℝ), 0 ≤ w s)
    (hw1 : ∀ (s : ℝ), w s ≤ 1 / 2)
    (hwright : ∀ (s : ℝ), s₀ ≤ s → w s = 0)
    (hwleft : ∀ s ∈ Ico (-1) s₀, 0 < w s)
    (hUpR : Over w ⊆ Rect)
    (hsm : -1 < s₀)
    (hf'x : f' ↑s₀ = x)
    (hE'd : IsClosedDisc (f' '' Over w ∪ Δ₂))
    (hE'E : f' '' Over w ∪ Δ₂ ⊆ E)
    (hKE' : K ⊆ f' '' Over w ∪ Δ₂)
    (hFg : IsClosed (f' '' ({z | z.re ∈ Icc (-1) s₀ ∧ 0 ≤ z.im ∧ z.im ≤ w z.re})))
    (hdiff : E \ (f' '' Over w ∪ Δ₂) ⊆ f' '' ({z | z.re ∈ Icc (-1) s₀ ∧ 0 ≤ z.im ∧ z.im ≤ w
      z.re}))
    (hKFg : ∀ {z : T}, z ∈ K → z ∈ f' '' ({z | z.re ∈ Icc (-1) s₀ ∧ 0 ≤ z.im ∧ z.im ≤ w z.re}) → z
      = x) :
    discBd (f' '' Over w ∪ Δ₂) ∩ K = discBd E ∩ K ∪ {x} := by
  let K' := f '' (K ∩ Δ₁)
  let FgC : Set ℂ := {z | z.re ∈ Icc (-1) s₀ ∧ 0 ≤ z.im ∧ z.im ≤ w z.re}
  have hfrE' := IsClosedDisc.frontier_eq_discBd hS hE'd
  ext z
  constructor
  · rintro ⟨hzb, hzK⟩
    by_cases hb : z ∈ discBd E
    · exact Or.inl ⟨hb, hzK⟩
    · refine Or.inr ?_
      by_contra hzx
      have hzin : z ∈ interior E := by
        by_contra hn
        apply hb
        rw [← hfrE, frontier, hE.isClosed.closure_eq]
        exact ⟨hKE hzK, hn⟩
      have hzFg : z ∉ f' '' FgC := fun h => hzx (hKFg hzK h)
      have hopen : IsOpen (interior E ∩ (f' '' FgC)ᶜ) := isOpen_interior.inter hFg.isOpen_compl
      have hsub : interior E ∩ (f' '' FgC)ᶜ ⊆ f' '' Over w ∪ Δ₂ := by
        rintro y ⟨h₁, h₂⟩
        by_contra hn
        exact h₂ (hdiff ⟨interior_subset h₁, hn⟩)
      have hint : z ∈ interior (f' '' Over w ∪ Δ₂) :=
        interior_maximal hsub hopen ⟨hzin, hzFg⟩
      rw [← hfrE'] at hzb
      exact disjoint_left.mp disjoint_interior_frontier hint hzb
  · rintro (⟨hzb, hzK⟩ | hzx)
    · refine ⟨?_, hzK⟩
      rw [← hfrE', frontier_eq_closure_inter_closure]
      rw [← hfrE, frontier_eq_closure_inter_closure] at hzb
      exact ⟨subset_closure (hKE' hzK), closure_mono (compl_subset_compl.mpr hE'E) hzb.2⟩
    · have hzx' : z = x := hzx
      subst hzx'
      refine ⟨?_, hx⟩
      rw [← hfrE', frontier_eq_closure_inter_closure]
      refine ⟨subset_closure (hKE' hx), ?_⟩
      let m : ℝ → ℂ := fun s => ⟨s, w s / 2⟩
      have hmc : Continuous m :=
        Complex.equivRealProdCLM.symm.continuous.comp (continuous_id.prodMk (hwc.div_const 2))
      have hmR : ∀ s ∈ Icc (-1 : ℝ) s₀, m s ∈ Rect := fun s hs =>
        ⟨⟨hs.1, hs.2.trans hs₀.2⟩, by
          have h₁ := hw0 s
          have h₂ := hw1 s
          constructor
          · change 0 ≤ w s / 2
            linarith
          · change w s / 2 ≤ 1
            linarith⟩
      have hg : ContinuousOn (f' ∘ m) (Icc (-1 : ℝ) s₀) :=
        hf.2.2.2.2.2.comp hmc.continuousOn hmR
      have hcls : s₀ ∈ closure (Ico (-1 : ℝ) s₀) := by
        rw [closure_Ico hsm.ne]
        exact ⟨hsm.le, le_rfl⟩
      have hcw : ContinuousWithinAt (f' ∘ m) (Ico (-1 : ℝ) s₀) s₀ :=
        (hg s₀ ⟨hsm.le, le_rfl⟩).mono Ico_subset_Icc_self
      have hend : (f' ∘ m) s₀ = z := by
        have : m s₀ = (s₀ : ℂ) := by
          apply Complex.ext
          · rfl
          · change w s₀ / 2 = _
            rw [hwright _ le_rfl]
            simp
        simp only [Function.comp, this, hf'x]
      rw [← hend]
      refine closure_mono ?_ (hcw.mem_closure_image hcls)
      rintro _ ⟨s, hs, rfl⟩
      have hsI : s ∈ Icc (-1 : ℝ) s₀ := ⟨hs.1, hs.2.le⟩
      have hp₀ := hwleft s hs
      rintro (⟨u, hu, hue⟩ | h₁)
      · have h₃ := hf.symm.injOn (hUpR hu) (hmR s hsI) hue
        have h₄ := hu.2.1
        rw [h₃] at h₄
        change w s ≤ w s / 2 at h₄
        linarith
      · have hin : (f' ∘ m) s ∈ ℓ₁ ∪ ℓ₂ := hmeet ▸ ⟨hf.2.1 (hmR s hsI), h₁⟩
        have hub : f ((f' ∘ m) s) ∈ Base := hfc ▸ mem_image_of_mem f hin
        simp only [Function.comp] at hub
        rw [hf.right (hmR s hsI)] at hub
        have h₃ : w s / 2 = 0 := (mem_Base.mp hub).2
        linarith

/-- **A finger.** See the module docstring. -/
theorem exists_finger [T2Space T] [ConnectedSpace T] (hS : IsClosedSurface T) {E K ℓ : Set T} {p x
  : T}
    (hE : IsClosedDisc E) (hKc : IsCompact K) (hKE : K ⊆ E) (hx : x ∈ K) (hxb : x ∉ discBd E)
    (hp : p ∉ E) (hℓ : IsLineWithEnds ℓ p x) (hℓK : ℓ ∩ K ⊆ {x}) :
    ∃ E' : Set T, IsClosedDisc E' ∧ E' ⊆ E ∧ K ⊆ E' ∧ discBd E' ∩ K = (discBd E ∩ K) ∪ {x} := by
  classical
  have hpx : p ≠ x := fun h => hp (h ▸ hKE hx)
  have hfrE : frontier E = discBd E := IsClosedDisc.frontier_eq_discBd hS hE
  -- Two lines, and their last parts.
  obtain ⟨P, hP, hPK, hPℓ⟩ := GM12.exists_parallel_line hS hℓ hpx hKc.isClosed
    (fun z hz => Or.inr (hℓK hz))
  obtain ⟨z₁, ℓ₁, hz₁, hl₁, hsub₁, hE₁, hb₁⟩ := exists_last_part hS hE hℓ hp (hKE hx) hxb
  obtain ⟨z₂, ℓ₂, hz₂, hl₂, hsub₂, hE₂, hb₂⟩ := exists_last_part hS hE hP hp (hKE hx) hxb
  have hxℓ₁ : x ∈ ℓ₁ := hl_end hl₁
  have hxℓ₂ : x ∈ ℓ₂ := hl_end hl₂
  have hcap : ℓ₁ ∩ ℓ₂ = {x} := by
    apply subset_antisymm
    · rintro z ⟨h₁, h₂⟩
      have : z ∈ P ∩ ℓ := ⟨hsub₂ h₂, hsub₁ h₁⟩
      rw [hPℓ] at this
      rcases this with h₃ | h₃
      · exact absurd (h₃ ▸ hE₁ h₁) hp
      · exact h₃
    · rintro z rfl
      exact ⟨hxℓ₁, hxℓ₂⟩
  have hz₁₂ : z₁ ≠ z₂ := fun h => by
    have : z₁ ∈ ℓ₁ ∩ ℓ₂ := ⟨hl_start hl₁, h ▸ hl_start hl₂⟩
    rw [hcap] at this
    exact hxb (this ▸ hz₁)
  have hc : IsLineWithEnds (ℓ₁ ∪ ℓ₂) z₁ z₂ := GraphMinor.Surface.IsLineWithEnds.union hl₁
    (GraphMinor.Surface.IsLineWithEnds.symm hl₂) hcap
  have hcE : ℓ₁ ∪ ℓ₂ ⊆ E := union_subset hE₁ hE₂
  have hcb : (ℓ₁ ∪ ℓ₂) ∩ discBd E = {z₁, z₂} := by
    rw [union_inter_distrib_right, hb₁, hb₂]
    rfl
  obtain ⟨A₁, A₂, Δ₁, Δ₂, -, -, hΔ₁, hΔ₂, hcov, hmeet, hbd₁, hbd₂, -⟩ :=
    disc_iArc E (ℓ₁ ∪ ℓ₂) z₁ z₂ hE hcE hz₁₂ hc hcb
  have hcbd : ℓ₁ ∪ ℓ₂ ⊆ discBd Δ₁ := hbd₁ ▸ subset_union_right
  have hcbd₂ : ℓ₁ ∪ ℓ₂ ⊆ discBd Δ₂ := hbd₂ ▸ subset_union_right
  have hfr₁ : frontier Δ₁ = discBd Δ₁ := IsClosedDisc.frontier_eq_discBd hS hΔ₁
  obtain ⟨f, f', hf, hfc, hf₁, hf₂⟩ := exists_rect_chart hΔ₁ hc hcbd
  have hΔ₁E : Δ₁ ⊆ E := hcov ▸ subset_union_left
  have hΔ₂E : Δ₂ ⊆ E := hcov ▸ subset_union_right
  have hRc : IsCompact Rect := isCompact_Icc.reProdIm isCompact_Icc
  have hc_sub : ℓ₁ ∪ ℓ₂ ⊆ Δ₁ := fun z hz => Surface.discBd_subset _ (hcbd hz)
  -- The point `x` in the chart.
  have hfx : f x ∈ Base := hfc ▸ mem_image_of_mem f (Or.inl hxℓ₁)
  obtain ⟨hs₀, hfxi⟩ := mem_Base.mp hfx
  set s₀ := (f x).re with hs₀def
  have hfxe : f x = (s₀ : ℂ) := Complex.ext (by simp [s₀]) (by simp [hfxi])
  -- The part of `K` in the chart.
  let K' : Set ℂ := f '' (K ∩ Δ₁)
  have hK'c : IsCompact K' :=
    hf.image_isCompact inter_subset_right (hKc.inter_right hΔ₁.isClosed)
  have hsK' : (s₀ : ℂ) ∈ K' := ⟨x, ⟨hx, hc_sub (Or.inl hxℓ₁)⟩, hfxe⟩
  -- Real points before `s₀` are off `K'`.
  have hoff : ∀ s : ℝ, s ∈ Ico (-1 : ℝ) s₀ → (s : ℂ) ∉ K' := by
    exact base_left_of_tip_avoids_obstacle (T := T) (K := K) (ℓ := ℓ) (x := x) hℓK z₁ ℓ₁ hl₁ hsub₁
      ℓ₂ hxℓ₁ Δ₁ f f' hf hfc hf₁ hc_sub s₀ hfxe
  -- The height.
  have hKne : K'.Nonempty := ⟨_, hsK'⟩
  let d : ℝ → ℝ := fun s => infDist (s : ℂ) K'
  have hdc : Continuous d := (continuous_infDist_pt K').comp Complex.continuous_ofReal
  let w : ℝ → ℝ := fun s => min (d (min s s₀) / 2) (1 / 2)
  have hwc : Continuous w :=
    ((hdc.comp (continuous_id.min continuous_const)).div_const 2).min continuous_const
  have hw0 : ∀ s, 0 ≤ w s := fun s =>
    le_min (div_nonneg infDist_nonneg (by norm_num)) (by norm_num)
  have hw1 : ∀ s, w s ≤ 1 / 2 := fun s => min_le_right _ _
  have hwright : ∀ s, s₀ ≤ s → w s = 0 := fun s hs => by
    have h₁ : d (min s s₀) = 0 := by
      rw [min_eq_right hs]
      exact infDist_zero_of_mem hsK'
    simp [w, h₁]
  have hwleft : ∀ s, s ∈ Ico (-1 : ℝ) s₀ → 0 < w s := fun s hs => by
    have h₁ : 0 < d s := by
      refine (hK'c.isClosed.notMem_iff_infDist_pos hKne).mp (hoff s hs)
    have h₂ : min s s₀ = s := min_eq_left hs.2.le
    simp only [w, h₂]
    exact lt_min (by linarith) (by norm_num)
  have hwle : ∀ z : ℂ, z ∈ K' → 0 ≤ z.im → z.re < s₀ → w z.re ≤ z.im / 2 := by
    intro z hz hi hlt
    have h₂ : min z.re s₀ = z.re := min_eq_left hlt.le
    have h₃ : d z.re ≤ dist (z.re : ℂ) z := infDist_le_dist_of_mem hz
    have h₄ : dist (z.re : ℂ) z = z.im := by
      rw [dist_comm, Complex.dist_eq]
      have : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [this]
      simp [abs_of_nonneg hi]
    calc w z.re ≤ d z.re / 2 := by
          simp only [w, h₂]
          exact min_le_left _ _
      _ ≤ z.im / 2 := by linarith
  -- The new disc.
  have hRd : IsClosedDisc Rect :=
    (isClosedDisc_rect (a := -1) (b := 1) (c := 0) (d := 1) (by norm_num) (by norm_num)).1
  have hUpR : Over w ⊆ Rect := fun z hz => ⟨hz.1, (hw0 _).trans hz.2.1, hz.2.2⟩
  have hL := raise_PH hwc hw0 hw1
  have hchain := hL.comp (hf.symm.restrict' hUpR)
  have hΔ'd : IsClosedDisc (f' '' Over w) := by
    have := hchain.disc_image Subset.rfl hRd
    rwa [hchain.image_eq] at this
  have hΔ'sub : f' '' Over w ⊆ Δ₁ := hf.symm.image_sub hUpR
  have hfr' : frontier (f' '' Over w) = discBd (f' '' Over w) :=
    IsClosedDisc.frontier_eq_discBd hS hΔ'd
  have hs₁ : s₀ < 1 := by
    refine lt_of_le_of_ne hs₀.2 fun h => ?_
    have h₁ : f x = 1 := by rw [hfxe, h]; simp
    have h₂ := hf.injOn (hc_sub (Or.inl hxℓ₁)) (hc_sub (Or.inr (hl_start hl₂))) (h₁.trans hf₂.symm)
    exact hxb (h₂ ▸ hz₂)
  have hsm : -1 < s₀ := by
    refine lt_of_le_of_ne hs₀.1 fun h => ?_
    have h₁ : f x = -1 := by rw [hfxe, ← h]; simp
    have h₂ := hf.injOn (hc_sub (Or.inl hxℓ₁)) (hc_sub (Or.inl (hl_start hl₁))) (h₁.trans hf₁.symm)
    exact hxb (h₂ ▸ hz₁)
  have hL₀ : IsLineWithEnds (segment ℝ (s₀ : ℂ) 1) (s₀ : ℂ) 1 :=
    isLineWithEnds_segment (by exact_mod_cast hs₁.ne)
  have hmem₀ : ∀ {z : ℂ}, z ∈ segment ℝ (s₀ : ℂ) 1 ↔ z.re ∈ Icc s₀ 1 ∧ z.im = 0 := by
    exact mem_right_base_segment s₀ hs₁
  have hL₀R : segment ℝ (s₀ : ℂ) 1 ⊆ Rect := fun z hz => by
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hmem₀.mp hz
    exact ⟨⟨by linarith [hs₀.1], h₂⟩, by change z.im ∈ Icc (0 : ℝ) 1; rw [h₃]; norm_num⟩
  have hL₀B : segment ℝ (s₀ : ℂ) 1 ⊆ Base := fun z hz => by
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hmem₀.mp hz
    exact mem_Base.mpr ⟨⟨by linarith [hs₀.1], h₂⟩, h₃⟩
  have hline := hf.symm.line_image hL₀R hL₀
  have hf'x : f' (s₀ : ℂ) = x := by
    rw [← hfxe]
    exact hf.left (hc_sub (Or.inl hxℓ₁))
  have hf'z : f' 1 = z₂ := by
    rw [← hf₂]
    exact hf.left (hc_sub (Or.inr (hl_start hl₂)))
  rw [hf'x, hf'z] at hline
  have hBc : ∀ {u}, u ∈ Base → f' u ∈ ℓ₁ ∪ ℓ₂ := fun {u} hu => by
    rw [← hfc] at hu
    obtain ⟨q, hq, rfl⟩ := hu
    rwa [hf.left (hc_sub hq)]
  have hLc : f' '' segment ℝ (s₀ : ℂ) 1 ⊆ ℓ₁ ∪ ℓ₂ := by
    rintro _ ⟨u, hu, rfl⟩
    exact hBc (hL₀B hu)
  have hmeetRaised : f' '' Over w ∩ Δ₂ = f' '' segment ℝ (s₀ : ℂ) 1 := by
    exact raised_disc_meets_other_half_along_right_base (T := T) ℓ₁ ℓ₂ Δ₁ Δ₂ hmeet hcbd₂ f f' hf
      hfc s₀ hs₀ w hwright hwleft hUpR hΔ'sub hmem₀ hLc
  have hLb₁ : f' '' segment ℝ (s₀ : ℂ) 1 ⊆ discBd (f' '' Over w) := by
    intro y hy
    rw [← hfr', frontier_eq_closure_inter_closure]
    have hyΔ : y ∈ f' '' Over w := (hmeetRaised.symm.subset hy).1
    refine ⟨subset_closure hyΔ, ?_⟩
    have h₁ : y ∈ frontier Δ₁ := hfr₁ ▸ hcbd (hLc hy)
    rw [frontier_eq_closure_inter_closure] at h₁
    exact closure_mono (compl_subset_compl.mpr hΔ'sub) h₁.2
  obtain ⟨hE'd, -⟩ := disc_union _ _ _ _ _ hΔ'd hΔ₂ hline hmeetRaised hLb₁ (hLc.trans hcbd₂)
  have hE'E : f' '' Over w ∪ Δ₂ ⊆ E := union_subset (hΔ'sub.trans hΔ₁E) hΔ₂E
  have hmemE : ∀ {z}, z ∈ E → z ∈ Δ₁ ∨ z ∈ Δ₂ := fun {z} hz => by
    rw [← hcov] at hz
    exact hz
  have hKE' : K ⊆ f' '' Over w ∪ Δ₂ := by
    exact raised_disc_union_contains_obstacle (T := T) (E := E) (K := K) hKE Δ₁ Δ₂ f f' hf s₀ w
      hwright hwle hmemE
  -- The finger.
  let FgC : Set ℂ := {z | z.re ∈ Icc (-1 : ℝ) s₀ ∧ 0 ≤ z.im ∧ z.im ≤ w z.re}
  have hFgR : FgC ⊆ Rect := fun z hz =>
    ⟨⟨hz.1.1, hz.1.2.trans hs₀.2⟩, hz.2.1, hz.2.2.trans ((hw1 _).trans (by norm_num))⟩
  have hFgcl : IsClosed FgC :=
    (isClosed_Icc.preimage Complex.continuous_re).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im (hwc.comp Complex.continuous_re)))
  have hFg : IsClosed (f' '' FgC) :=
    hf.symm.image_isClosed hRc hFgR hFgcl
  have hdiff : E \ (f' '' Over w ∪ Δ₂) ⊆ f' '' FgC := by
    exact removed_points_below_raising_graph (T := T) (E := E) Δ₁ Δ₂ f f' hf s₀ w hwright hmemE
  have hKFg : ∀ {z}, z ∈ K → z ∈ f' '' FgC → z = x := by
    exact raising_graph_meets_obstacle_at_tip (T := T) (K := K) (x := x) Δ₁ f f' hf s₀ hoff w
      hwright hwle hf'x hFgR
  have hRaisedBoundary : discBd (f' '' Over w ∪ Δ₂) ∩ K = (discBd E ∩ K) ∪ {x} := by
    exact raised_disc_boundary_meets_obstacle_at_tip (T := T) hS (E := E) (K := K) (x := x)
      hE hKE hx hfrE ℓ₁ ℓ₂ Δ₁ Δ₂ hmeet f f' hf hfc s₀ hs₀ w hwc hw0 hw1 hwright hwleft hUpR hsm
      hf'x hE'd hE'E hKE' hFg hdiff hKFg
  exact ⟨_, hE'd, hE'E, hKE', hRaisedBoundary⟩

/-- **A closed disc around `K` with a finite set `X` of points on its boundary.** Each point of `X`
is the
end of a line from a fixed point `p` off `K`, which meets `K` only in that end. -/
theorem exists_disc_around [T2Space T] [ConnectedSpace T] (hS : IsClosedSurface T)
  (hsph : IsSphere T)
    {K X : Set T} {p : T} (hKc : IsCompact K) (hp : p ∉ K) (hX : X.Finite) (hXK : X ⊆ K)
    (hl : ∀ x ∈ X, ∃ ℓ, IsLineWithEnds ℓ p x ∧ ℓ ∩ K ⊆ {x}) :
    ∃ E : Set T, IsClosedDisc E ∧ K ⊆ E ∧ p ∉ E ∧ discBd E ∩ K = X := by
  classical
  induction X, hX using Set.Finite.induction_on with
  | empty =>
    obtain ⟨D, D', hD, hD'o, hpD', hD'D, hDO, hb⟩ :=
      exists_closedDisc_nbhd hS hKc.isClosed.isOpen_compl hp
    obtain ⟨Δ₁, Δ₂, -, hd₁, hd₂, hb₁, hb₂, hcov, hcap, -, huniq⟩ :=
      sphere_disc T hsph (discBd D) hD.isOArc_discBd
    have hpb : p ∉ discBd D := fun h => (hb ▸ h).2 hpD'
    rcases huniq D hD rfl with rfl | rfl
    · refine ⟨Δ₂, hd₂, fun z hz => ?_, fun hz => hpb (hcap ▸ ⟨hD'D hpD', hz⟩), ?_⟩
      · have : z ∈ D ∪ Δ₂ := hcov ▸ mem_univ z
        exact this.resolve_left fun h => hDO h hz
      · refine eq_empty_of_forall_notMem fun z hz => ?_
        rw [hb₂] at hz
        exact hDO (Surface.discBd_subset _ hz.1) hz.2
    · refine ⟨Δ₁, hd₁, fun z hz => ?_, fun hz => hpb (hcap ▸ ⟨hz, hD'D hpD'⟩), ?_⟩
      · have : z ∈ Δ₁ ∪ D := hcov ▸ mem_univ z
        exact this.resolve_right fun h => hDO h hz
      · refine eq_empty_of_forall_notMem fun z hz => ?_
        rw [hb₁] at hz
        exact hDO (Surface.discBd_subset _ hz.1) hz.2
  | @insert x X hxX hfin ih =>
    obtain ⟨E, hE, hKE, hpE, hbE⟩ := ih (fun z hz => hXK (mem_insert_of_mem _ hz))
      fun z hz => hl z (mem_insert_of_mem _ hz)
    have hxK : x ∈ K := hXK (mem_insert _ _)
    obtain ⟨ℓ, hℓ, hℓK⟩ := hl x (mem_insert _ _)
    obtain ⟨E', hE', hE'E, hKE', hb⟩ :=
      exists_finger hS hE hKc hKE hxK (fun h => hxX (hbE ▸ ⟨h, hxK⟩)) hpE hℓ hℓK
    refine ⟨E', hE', hKE', fun h => hpE (hE'E h), ?_⟩
    rw [hb, hbE, union_comm]
    rfl

end GraphMinor.GM14.Whitney
