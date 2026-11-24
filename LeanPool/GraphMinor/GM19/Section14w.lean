/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14v

/-!
# Graph Minors XIX, Section 14: a painting seen from `Σ'`

All the paintings of the sequence in (14.1) have their wheels in the same place, after a
homeomorphism of `Σ`. So there is one surface `Σ' = Σ \ T`, and for each painting a map
`e` of `Σ'` to `Σ̂` whose image is the complement of the insides of the wheels.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 TangleDatum

universe w

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space S] [T2Space Shat] {α
  : Type w}
  {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

/-- A cover by wheels in `D`, seen from `Σ' = Σ \ T`. -/
structure Slice (T : Set S) (D : TangleDatum cap χ) where
  /-- The wheel discs used to make the cuts. -/
  𝒲 : Set (Set Shat)
  /-- The chosen wheel frame on each disc. -/
  fr : ∀ W : ↥𝒲, WheelFrame D W.1
  /-- The homeomorphism applied before cutting. -/
  f : S ≃ₜ S
  hf : IsFramePreservingHomeo χ.Φ f
  cut : IsCutData (cap.emb ∘ f) 𝒲
  hT : cutT (cap.emb ∘ f) 𝒲 = T

namespace Slice

variable {T : Set S} {D : TangleDatum cap χ} (s : Slice T D)
include s

/-- The map of `Σ'` to `Σ̂`. -/
def e (x : ↥Tᶜ) : Shat := cap.emb (s.f x.1)

theorem isEmbedding : IsEmbedding s.e := by
  have : IsEmbedding (cap.emb ∘ s.f) := s.cut.emb.isEmbedding
  exact this.comp IsEmbedding.subtypeVal

theorem range_e : range s.e = (⋃ W ∈ s.𝒲, discInt W)ᶜ := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    have h : x.1 ∉ cutT (cap.emb ∘ s.f) s.𝒲 := by
      rw [s.hT]
      exact x.2
    exact h
  · intro hy
    obtain ⟨x, -, rfl⟩ := s.cut.cover hy
    refine ⟨⟨x, ?_⟩, rfl⟩
    have h : x ∉ cutT (cap.emb ∘ s.f) s.𝒲 := hy
    rw [s.hT] at h
    exact h

theorem facts : IsClosed Tᶜ ∧ IsSurface ↥Tᶜ ∧ bd ↥Tᶜ = Subtype.val ⁻¹' cutF (cap.emb ∘ s.f) s.𝒲
  ∧ ConnectedSpace ↥Tᶜ := by
  have := cap.connected
  have h := s.cut.surface_facts cap.isSurface cap.bd_empty
  rw [s.hT] at h
  exact h

theorem isSurface : IsSurface ↥Tᶜ := s.facts.2.1

theorem connected : ConnectedSpace ↥Tᶜ := s.facts.2.2.2

theorem mem_bd {x : ↥Tᶜ} : x ∈ bd ↥Tᶜ ↔ s.e x ∈ ⋃ W ∈ s.𝒲, discBd W := by
  rw [s.facts.2.2.1]
  rfl

/-- The cuff of `Σ'` at a wheel. -/
def cf (W : Set Shat) : Set ↥Tᶜ := s.e ⁻¹' discBd W

theorem image_cf {W : Set Shat} (hW : W ∈ s.𝒲) : s.e '' s.cf W = discBd W := by
  have h := s.cut.image_cuffAt hW
  have key : ∀ (T' : Set S) (hT' : cutT (cap.emb ∘ s.f) s.𝒲 = T'), (fun x : ↥T'ᶜ ↦ cap.emb
    (s.f x.1)) '' ((fun x : ↥T'ᶜ ↦ cap.emb (s.f x.1)) ⁻¹' discBd W) = discBd W := by
    rintro _ rfl
    exact h
  exact key T s.hT

theorem cuffs_eq : cuffs ↥Tᶜ = s.cf '' s.𝒲 := by
  have := cap.connected
  have key : ∀ (T' : Set S) (hT' : cutT (cap.emb ∘ s.f) s.𝒲 = T'), cuffs ↥T'ᶜ = (fun W ↦
    (fun x : ↥T'ᶜ ↦ cap.emb (s.f x.1)) ⁻¹' discBd W) '' s.𝒲 := by
    rintro _ rfl
    exact s.cut.cuffs_eq cap.isSurface cap.bd_empty
  exact key T s.hT

theorem cf_mem {W : Set Shat} (hW : W ∈ s.𝒲) : s.cf W ∈ cuffs ↥Tᶜ := by
  rw [s.cuffs_eq]
  exact mem_image_of_mem _ hW

theorem nonempty_capped : Nonempty (IsCappedSurface ↥Tᶜ Shat) := by
  have := cap.connected
  have key : ∀ (T' : Set S) (_ : cutT (cap.emb ∘ s.f) s.𝒲 = T'), Nonempty
    (IsCappedSurface ↥T'ᶜ Shat) := by
    rintro _ rfl
    exact s.cut.nonempty_capped cap.isSurface cap.bd_empty
  exact key T s.hT

/-- The vertices of `Γ` on `Σ'`. -/
def N : Set ↥Tᶜ := s.e ⁻¹' D.P.Γ.hatV cap

theorem finite_N : s.N.Finite := (D.P.Γ.finite_V.image _).preimage (s.isEmbedding.injective.injOn)

/-- The vertices of `Γ` on the boundary of `Σ'`. -/
def Nb : Set ↥Tᶜ := s.N ∩ bd ↥Tᶜ

theorem finite_Nb : s.Nb.Finite := s.finite_N.subset inter_subset_left

theorem exists_pt {W : Set Shat} (hW : W ∈ s.𝒲) {y : Shat} (hy : y ∈ discBd W) : ∃ x ∈ s.cf W, s.e
  x = y := by
  rw [← s.image_cf hW] at hy
  exact hy

theorem cf_sub_bd {W : Set Shat} (hW : W ∈ s.𝒲) : s.cf W ⊆ bd ↥Tᶜ := fun _ hx ↦ s.mem_bd.mpr
  (mem_iUnion₂.mpr ⟨W, hW, hx⟩)

omit s in
theorem vert_bd (s : Slice T D) (W : ↥s.𝒲) (i : ℕ) : (s.fr W).R.vert i ∈ discBd W.1 :=
  ((s.fr W).R.vert_mem i).2

/-- The point of `Σ'` at the `i`th vertex of the rim of a wheel. -/
noncomputable def vx (W : ↥s.𝒲) (i : ℕ) : ↥Tᶜ := (s.exists_pt W.2 (s.vert_bd W i)).choose

theorem e_vx (W : ↥s.𝒲) (i : ℕ) : s.e (s.vx W i) = (s.fr W).R.vert i := (s.exists_pt W.2
  (s.vert_bd W i)).choose_spec.2

theorem vx_cf (W : ↥s.𝒲) (i : ℕ) : s.vx W i ∈ s.cf W := (s.exists_pt W.2
  (s.vert_bd W i)).choose_spec.1

theorem vx_N (W : ↥s.𝒲) (i : ℕ) : s.vx W i ∈ s.Nb :=
  ⟨show s.e _ ∈ D.P.Γ.hatV cap by rw [s.e_vx]; exact ((s.fr W).R.vert_mem i).1,
    s.cf_sub_bd W.2 (s.vx_cf W i)⟩

theorem vx_inj (W : ↥s.𝒲) {i j : ℕ} (hi : i < (s.fr W).R.k) (hj : j < (s.fr W).R.k) (h : s.vx W i
  = s.vx W j) : i = j :=
  (s.fr W).R.vert_inj hi hj (by rw [← s.e_vx, ← s.e_vx, h])

theorem vx_add_k (W : ↥s.𝒲) (i : ℕ) : s.vx W (i + (s.fr W).R.k) = s.vx W i :=
  s.isEmbedding.injective (by rw [s.e_vx, s.e_vx, (s.fr W).R.vert_add_k])

theorem two (C : cuffs ↥Tᶜ) : ∃ p ∈ s.Nb ∩ C.1, ∃ q ∈ s.Nb ∩ C.1, p ≠ q := by
  obtain ⟨C, hC⟩ := C
  rw [s.cuffs_eq] at hC
  obtain ⟨W, hW, rfl⟩ := hC
  have h3 := (s.fr ⟨W, hW⟩).k_three
  exact ⟨_, ⟨s.vx_N ⟨W, hW⟩ 0, s.vx_cf ⟨W, hW⟩ 0⟩, _, ⟨s.vx_N ⟨W, hW⟩ 1, s.vx_cf ⟨W, hW⟩ 1⟩,
    fun h ↦ absurd (s.vx_inj ⟨W, hW⟩ (by omega) (by omega) h) (by omega)⟩

/-- **A rim arc in `Σ'`.** -/
theorem exists_arc (W : ↥s.𝒲) (i : ℕ) : ∃ A ∈ arcComponentsIn (bd ↥Tᶜ \ s.Nb), A ⊆ s.cf W ∧ tilde A
  = {s.vx W i, s.vx W (i + 1)} ∧ ∃ x ∈ A, s.e x = (s.fr W).R.reg i := by
  obtain ⟨A, h₁, h₂, h₃, h₄, h₅, h₆⟩ := (s.fr W).R.exists_arc i
  have hsur := s.image_cf W.2
  have hAr : s.e '' (s.e ⁻¹' A) = A := image_preimage_eq_of_subset
    (h₂.trans (by rw [← hsur]; exact image_subset_range _ _))
  have hpc : IsPathConnected (s.e ⁻¹' A) := by
    rw [s.isEmbedding.isInducing.isPathConnected_iff, hAr]
    exact h₁
  have hsub : s.e ⁻¹' A ⊆ bd ↥Tᶜ \ s.Nb := fun x hx ↦ ⟨s.cf_sub_bd W.2
    (h₂ hx), fun hN ↦ disjoint_left.mp h₃ hx hN.1⟩
  obtain ⟨c, hc, hAc⟩ := exists_arcComp_superset hpc hsub
  have hcl : ∀ i', (s.fr W).R.vert i' ∈ closure A → s.vx W i' ∈ closure (s.e ⁻¹' A)
    := fun i' hi' ↦ by
    rw [s.isEmbedding.closure_eq_preimage_closure_image, hAr]
    change s.e (s.vx W i') ∈ closure A
    rwa [s.e_vx]
  have hnc : ∀ i', s.vx W i' ∉ c := fun i' h' ↦ (hc.2.1 h').2 (s.vx_N W i')
  have ht := arc_shape s.isSurface s.finite_Nb s.two hc
  have hne : s.vx W i ≠ s.vx W (i + 1) := fun h' ↦ by
    have h₇ : (s.fr W).R.vert i = (s.fr W).R.vert (i + 1) := by rw [← s.e_vx, ← s.e_vx, h']
    have h₈ := (s.fr W).R.mod_lt i
    have h₉ : (s.fr W).R.vert (i % (s.fr W).R.k) = (s.fr W).R.vert i := by
      rw [Rim.vert, Rim.vert, Nat.mod_mod]
    have h₁₀ : (s.fr W).R.vert (i % (s.fr W).R.k + 1) = (s.fr W).R.vert (i + 1) := by
      rw [Rim.vert, Rim.vert, Nat.mod_add_mod]
    exact (s.fr W).R.vert_ne_succ h₈ (by rw [h₉, h₁₀, h₇])
  have hm₁ : s.vx W i ∈ tilde c := ⟨closure_mono hAc (hcl _ h₅), hnc _⟩
  have hm₂ : s.vx W (i + 1) ∈ tilde c := ⟨closure_mono hAc (hcl _ h₆), hnc _⟩
  have htc : tilde c = {s.vx W i, s.vx W (i + 1)} := by
    symm
    apply eq_of_subset_of_ncard_le _ _ ht.2.1
    · rintro _ (rfl | rfl)
      · exact hm₁
      · exact hm₂
    · rw [ht.1, ncard_pair hne]
  have hrb : (s.fr W).R.reg i ∈ discBd W.1 := ((s.fr W).R.reg_mem i).2
  obtain ⟨y, hy, hye⟩ : ∃ y ∈ s.cf W, s.e y = (s.fr W).R.reg i := s.exists_pt W.2 hrb
  have hyA : y ∈ c := hAc (by change s.e y ∈ A; rw [hye]; exact h₄)
  refine ⟨c, hc, ?_, htc, y, hyA, hye⟩
  have hcC : s.cf W.1 ∈ cuffs ↥Tᶜ := s.cf_mem W.2
  obtain ⟨C, a, b, -, -, rfl, -, -, -⟩ := exists_arc_of_mem s.isSurface
    (cuffPar s.isSurface) s.finite_Nb s.two hc
  have hyC : y ∈ C.1 := arcOf_subset _ _ _ hyA
  have hC : C.1 = s.cf W.1 := by
    by_contra hne'
    exact disjoint_left.mp (cuffs_disjoint C.2 hcC hne') hyC hy
  rw [← hC]
  exact arcOf_subset _ _ _

/-- The arc of the rim at `R.reg i`, in `Σ'`. -/
noncomputable def arc (W : ↥s.𝒲) (i : ℕ) : Set ↥Tᶜ := (s.exists_arc W i).choose

theorem arc_mem (W : ↥s.𝒲) (i : ℕ) : s.arc W i ∈ arcComponentsIn (bd ↥Tᶜ \ s.Nb) :=
  (s.exists_arc W i).choose_spec.1

theorem arc_cf (W : ↥s.𝒲) (i : ℕ) : s.arc W i ⊆ s.cf W := (s.exists_arc W i).choose_spec.2.1

theorem tilde_arc (W : ↥s.𝒲) (i : ℕ) : tilde (s.arc W i) = {s.vx W i, s.vx W (i + 1)} :=
  (s.exists_arc W i).choose_spec.2.2.1

theorem arc_reg (W : ↥s.𝒲) (i : ℕ) : ∃ x ∈ s.arc W i, s.e x = (s.fr W).R.reg i :=
  (s.exists_arc W i).choose_spec.2.2.2

theorem vert_mod (W : ↥s.𝒲) (i : ℕ) : (s.fr W).R.vert (i % (s.fr W).R.k) = (s.fr W).R.vert i := by
  rw [Rim.vert, Rim.vert, Nat.mod_mod]

theorem vx_mod_eq (W : ↥s.𝒲) {i j : ℕ} (h : s.vx W i = s.vx W j) : i % (s.fr W).R.k = j %
  (s.fr W).R.k := by
  refine (s.fr W).R.vert_inj ((s.fr W).R.mod_lt i) ((s.fr W).R.mod_lt j) ?_
  rw [s.vert_mod, s.vert_mod, ← s.e_vx, ← s.e_vx, h]

theorem vx_ne_succ (W : ↥s.𝒲) (i : ℕ) : s.vx W i ≠ s.vx W (i + 1) := fun h ↦ by
  have h₁ := s.vx_mod_eq W h
  have h₃ := (s.fr W).k_three
  have : (s.fr W).R.k ∣ (i + 1) - i := (Nat.modEq_iff_dvd' (by omega)).mp h₁
  have := Nat.le_of_dvd (by omega) this
  omega

theorem vx_ne_add_two (W : ↥s.𝒲) (i : ℕ) : s.vx W i ≠ s.vx W (i + 2) := fun h ↦ by
  have h₁ := s.vx_mod_eq W h
  have h₃ := (s.fr W).k_three
  have : (s.fr W).R.k ∣ (i + 2) - i := (Nat.modEq_iff_dvd' (by omega)).mp h₁
  have := Nat.le_of_dvd (by omega) this
  omega

/-- Each arc of `bd(Σ')` between vertices of `Γ` on a cuff is an arc of the rim. -/
theorem arc_cover (W : ↥s.𝒲) {c : Set ↥Tᶜ} (hc : c ∈ arcComponentsIn (bd ↥Tᶜ \ s.Nb)) {x₀ : ↥Tᶜ}
  (hx₀ : x₀ ∈ c) (hx₀W : x₀ ∈ s.cf W) : ∃ i < (s.fr W).R.k, c = s.arc W i := by
  classical
  obtain ⟨C, a, b, hab, hub, rfl, hdis, ha, hb⟩ := exists_arc_of_mem s.isSurface
    (cuffPar s.isSurface) s.finite_Nb s.two hc
  have hC : C.1 = s.cf W.1 := by
    by_contra hne'
    exact disjoint_left.mp (cuffs_disjoint C.2 (s.cf_mem W.2) hne') (arcOf_subset _ _ _ hx₀) hx₀W
  have hsub : arcOf (cuffPar s.isSurface C) a b ⊆ s.cf W := hC ▸ arcOf_subset _ _ _
  by_cases hr : ∃ x ∈ arcOf (cuffPar s.isSurface C) a b, s.e x ∈ D.rad.Rstar
  · obtain ⟨x, hx, hxr⟩ := hr
    obtain ⟨i, hi, e⟩ := (s.fr W).R.exists_reg _ ⟨hxr, hsub hx⟩
    obtain ⟨y, hy, hye⟩ := s.arc_reg W i
    obtain rfl : y = x := s.isEmbedding.injective (hye.trans e.symm)
    exact ⟨i, hi, arcComp_eq_of_mem hc (s.arc_mem W i) hx hy⟩
  · exfalso
    push Not at hr
    have hpc := isPathConnected_arcOf (cuffPar s.isSurface C) hab
    have hdV : Disjoint (s.e '' arcOf (cuffPar s.isSurface C) a b) D.rad.G.V := by
      refine disjoint_left.mpr ?_
      rintro _ ⟨x, hx, rfl⟩ hG
      by_cases hh : s.e x ∈ D.P.Γ.hatV cap
      · exact (hc.2.1 hx).2 ⟨hh, (hc.2.1 hx).1⟩
      · exact hr x hx ⟨hG, hh⟩
    have hcl : ∀ p, p ∈ tilde (arcOf (cuffPar s.isSurface C) a b) → s.e p ∈ closure (s.e '' arcOf
      (cuffPar s.isSurface C) a b) := fun p hp ↦ image_closure_subset_closure_image
        s.isEmbedding.continuous (mem_image_of_mem _ hp.1)
    have ht := tilde_arcOf (cuffPar s.isSurface C) hab hub
    have hne := (GM20.line_facts (isLine_arcOf (cuffPar s.isSurface C) hab hub)).1
    refine (s.fr W).R.no_two_ends (hpc.image s.isEmbedding.continuous) ?_ hdV
      (hcl _ (by rw [ht]; simp)) (hcl _ (by rw [ht]; simp))
      (s.isEmbedding.injective.ne hne) ha.1 hb.1
    rintro _ ⟨x, hx, rfl⟩
    exact hsub hx

end Slice

/-- The two ends of an arc are determined by the arc. -/
theorem arcOf_ends_eq {X : Type} [TopologicalSpace X] {Θ : Set X}
  (f : Circle ≃ₜ Θ) {a b a' b' : ℝ} (hab : a < b) (hub : b < a + 2 * Real.pi) (hab' : a' < b')
    (hub' : b' < a' + 2 * Real.pi)
    (h : arcOf f a b = arcOf f a' b') : cuffPoint f a = cuffPoint f a' ∧ cuffPoint f b
      = cuffPoint f b' := by
  obtain ⟨m, h₁, h₂⟩ := exists_shift f hab hab' hub h.ge
  obtain ⟨m', h₃, h₄⟩ := exists_shift f hab' hab hub' h.le
  have hpi := Real.pi_pos
  have hm : (0 : ℝ) ≤ (m + m' : ℝ) * (2 * Real.pi) := by nlinarith
  have hm' : ((m + m' : ℝ)) * (2 * Real.pi) ≤ 0 := by nlinarith
  have h0 : (m + m' : ℝ) = 0 := by
    have : (m + m' : ℝ) * (2 * Real.pi) = 0 := le_antisymm hm' hm
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exact absurd h' (by positivity)
  have he : (m' : ℝ) = -m := by linarith
  rw [he] at h₃ h₄
  have ea : a = a' + m * (2 * Real.pi) := by nlinarith
  have eb : b = b' + m * (2 * Real.pi) := by nlinarith
  rw [ea, eb, cuffPoint_shift, cuffPoint_shift]
  exact ⟨rfl, rfl⟩

namespace Slice

variable {T : Set S} {D : TangleDatum cap χ} (s : Slice T D)
include s

/-- **All the arcs of a rim run the same way around the cuff.** -/
theorem exists_dir (W : ↥s.𝒲) : ∃ ε : Bool, ∀ i, arcMarch s.isSurface ε (s.arc W i)
  = [s.vx W i, s.vx W (i + 1)] := by
  have hX := s.isSurface
  let Fw : ℕ → Bool → Prop := fun i c ↦ ∃ (C : cuffs ↥Tᶜ) (a b : ℝ), a < b ∧ b < a + 2 * Real.pi
    ∧ s.arc W i = arcOf (cuffPar hX C) a b ∧
    cuffPoint (cuffPar hX C) a = (if c then s.vx W (i + 1) else s.vx W i) ∧ cuffPoint
      (cuffPar hX C) b = (if c then s.vx W i else s.vx W (i + 1))
  have hall : ∀ i, Fw i false ∨ Fw i true := by
    intro i
    obtain ⟨C, a, b, hab, hub, he, -, ha, hb⟩ := exists_arc_of_mem hX
      (cuffPar hX) s.finite_Nb s.two (s.arc_mem W i)
    have ht := tilde_arcOf (cuffPar hX C) hab hub
    rw [← he, s.tilde_arc] at ht
    have hne := s.vx_ne_succ W i
    have h₁ : cuffPoint (cuffPar hX C) a ∈ ({s.vx W i, s.vx W (i + 1)} : Set _) := by rw [ht]; simp
    have h₂ : cuffPoint (cuffPar hX C) b ∈ ({s.vx W i, s.vx W (i + 1)} : Set _) := by rw [ht]; simp
    have hab' := (GM20.line_facts (isLine_arcOf (cuffPar hX C) hab hub)).1
    rcases h₁ with e₁ | e₁ <;> rcases h₂ with e₂ | e₂
    · exact absurd (e₁.trans e₂.symm) hab'
    · exact .inl ⟨C, a, b, hab, hub, he, e₁, e₂⟩
    · exact .inr ⟨C, a, b, hab, hub, he, e₁, e₂⟩
    · exact absurd (e₁.trans (mem_singleton_iff.mp e₂).symm) hab'
  have hcuff : ∀ {C C' : cuffs ↥Tᶜ} {x : ↥Tᶜ}, x ∈ C.1 → x ∈ C'.1 → C = C'
    := fun {C C' x} h₁ h₂ ↦ by
    by_contra hne
    exact disjoint_left.mp (cuffs_disjoint' hne) h₁ h₂
  have hstep : ∀ i c, Fw i c → Fw (i + 1) c := by
    intro i c hF
    obtain ⟨C, a, b, hab, hub, he, h₁, h₂⟩ := hF
    rcases hall (i + 1) with hF' | hF'
    · cases c
      · exact hF'
      · exfalso
        obtain ⟨C', a', b', hab', hub', he', h₁', h₂'⟩ := hF'
        simp only [ite_true, Bool.false_eq_true, ite_false] at h₁ h₂ h₁' h₂'
        obtain rfl : C = C' := hcuff (x := s.vx W (i + 1)) (h₁ ▸ cuffPoint_mem _ _)
          (h₁' ▸ cuffPoint_mem _ _)
        have ea := arc_head_eq hab hab' (he ▸ s.arc_mem W i) (he' ▸ s.arc_mem W (i + 1))
          (h₁.trans h₁'.symm)
        have ht := congrArg tilde (he.trans (ea.trans he'.symm))
        rw [s.tilde_arc, s.tilde_arc] at ht
        have hm : s.vx W i ∈ ({s.vx W (i + 1), s.vx W (i + 1 + 1)} : Set _) := ht ▸ (by simp)
        rcases hm with h' | h'
        · exact s.vx_ne_succ W i h'
        · exact s.vx_ne_add_two W i h'
    · cases c
      · exfalso
        obtain ⟨C', a', b', hab', hub', he', h₁', h₂'⟩ := hF'
        simp only [ite_true, Bool.false_eq_true, ite_false] at h₁ h₂ h₁' h₂'
        obtain rfl : C = C' := hcuff (x := s.vx W (i + 1)) (h₂ ▸ cuffPoint_mem _ _)
          (h₂' ▸ cuffPoint_mem _ _)
        have ea := arc_tail_eq hab hab' (he ▸ s.arc_mem W i) (he' ▸ s.arc_mem W (i + 1))
          (h₂.trans h₂'.symm)
        have ht := congrArg tilde (he.trans (ea.trans he'.symm))
        rw [s.tilde_arc, s.tilde_arc] at ht
        have hm : s.vx W i ∈ ({s.vx W (i + 1), s.vx W (i + 1 + 1)} : Set _) := ht ▸ (by simp)
        rcases hm with h' | h'
        · exact s.vx_ne_succ W i h'
        · exact s.vx_ne_add_two W i h'
      · exact hF'
  have hconst : ∃ c, ∀ i, Fw i c := by
    rcases hall 0 with h₀ | h₀
    · exact ⟨false, fun i ↦ by
        induction i with
        | zero => exact h₀
        | succ i ih => exact hstep i _ ih⟩
    · exact ⟨true, fun i ↦ by
        induction i with
        | zero => exact h₀
        | succ i ih => exact hstep i _ ih⟩
  obtain ⟨c, hc⟩ := hconst
  refine ⟨c, fun i ↦ ?_⟩
  obtain ⟨C, a, b, hab, hub, he, h₁, h₂⟩ := hc i
  obtain ⟨C', a', b', hab', hub', he', hl⟩ := arcMarch_spec hX c hab hub he
  obtain rfl : C = C' := by
    obtain ⟨x, hx⟩ := (s.arc_mem W i).1
    exact hcuff (x := x) (arcOf_subset _ _ _ (he ▸ hx)) (arcOf_subset _ _ _ (he' ▸ hx))
  obtain ⟨e₁, e₂⟩ := arcOf_ends_eq _ hab hub hab' hub' (he.symm.trans he')
  rw [hl, ← e₁, ← e₂, h₁, h₂]
  cases c <;> simp

end Slice

end GraphMinor.GM19
