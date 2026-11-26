/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section5f

/-!
# Graph Minors XIX, (5.3)

We choose the direction of each side of the frame of a fragment as the paper does: `ψ` maps it onto
the direction
of the side of `Φ` below it. Then we collect the five conditions of "fit".
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {S S₁ : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace S₁] [T2Space S₁]


/-- A continuous function on `[0, 1]` that is one-to-one on `(0, 1)` has different values at `0` and
`1`. Otherwise
it would take a value between `G(0)` and `G(t)` on both sides of a point `t`. -/
theorem ne_of_injOn_Ioo {G : ℝ → ℝ} (hc : Continuous G) (hi : InjOn G (Ioo 0 1)) : G 0 ≠ G 1 := by
  intro h
  obtain ⟨t, ht, hne⟩ : ∃ t ∈ Ioo (0 : ℝ) 1, G t ≠ G 0 := by
    by_contra hall
    push Not at hall
    have h₁ : (1 / 3 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
    have h₂ : (2 / 3 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
    have := hi h₁ h₂ ((hall _ h₁).trans (hall _ h₂).symm)
    norm_num at this
  have hmid₁ : (G 0 + G t) / 2 ∈ uIcc (G 0) (G t) := by
    rw [mem_uIcc]
    rcases le_total (G 0) (G t) with h' | h'
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  have hmid₂ : (G 0 + G t) / 2 ∈ uIcc (G t) (G 1) := by
    rw [uIcc_comm, ← h]
    exact hmid₁
  obtain ⟨s, hs, hsv⟩ := intermediate_value_uIcc hc.continuousOn hmid₁
  obtain ⟨s', hs', hsv'⟩ := intermediate_value_uIcc hc.continuousOn hmid₂
  rw [uIcc_of_le ht.1.le] at hs
  rw [uIcc_of_le ht.2.le] at hs'
  have hd₀ : (G 0 + G t) / 2 ≠ G 0 := fun he ↦ hne (by linarith)
  have hd₁ : (G 0 + G t) / 2 ≠ G t := fun he ↦ hne (by linarith)
  have hs₀ : s ≠ 0 := fun he ↦ hd₀ (by rw [← hsv, he])
  have hst : s ≠ t := fun he ↦ hd₁ (by rw [← hsv, he])
  have hs't : s' ≠ t := fun he ↦ hd₁ (by rw [← hsv', he])
  have hs'1 : s' ≠ 1 := fun he ↦ hd₀ (by rw [← hsv', he, ← h])
  have hlt : s < t := lt_of_le_of_ne hs.2 hst
  have hgt : t < s' := lt_of_le_of_ne hs'.1 hs't.symm
  have hsI : s ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hs.1 hs₀.symm, hlt.trans ht.2⟩
  have hsI' : s' ∈ Ioo (0 : ℝ) 1 := ⟨ht.1.trans hgt, lt_of_le_of_ne hs'.2 hs'1⟩
  have heq := hi hsI hsI' (hsv.trans hsv'.symm)
  linarith

/-- A list with no repeats whose set of entries is `{u, w}` is `[u, w]` or `[w, u]`. -/
theorem list_pair {T : Type} {l : List T} {u w : T} (hn : l.Nodup) (hs : {v | v ∈ l} = {u, w})
  (hne : u ≠ w) :
    l = [u, w] ∨ l = [w, u] := by
  have hu : u ∈ l := by
    have : u ∈ {v | v ∈ l} := hs ▸ mem_insert _ _
    exact this
  have hw : w ∈ l := by
    have : w ∈ {v | v ∈ l} := hs ▸ mem_insert_of_mem _ rfl
    exact this
  have hall : ∀ x ∈ l, x = u ∨ x = w := fun x hx ↦ by
    have : x ∈ {v | v ∈ l} := hx
    rw [hs] at this
    exact this
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · simp at hu
  · simp only [List.mem_singleton] at hu hw
    exact absurd (hu.trans hw.symm) hne
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_false_eq_true,
      List.nodup_nil, and_true] at hn hall
    rcases hall x (.inl rfl) with rfl | rfl <;> rcases hall y (.inr rfl) with rfl | rfl
    · exact absurd rfl hn
    · exact .inl rfl
    · exact .inr rfl
    · exact absurd rfl hn
  · simp only [List.nodup_cons, List.mem_cons, not_or] at hn
    have hx := hall x (by simp)
    have hy := hall y (by simp)
    have hz := hall z (by simp)
    obtain ⟨⟨h₁, h₂, -⟩, ⟨h₃, -⟩, -⟩ := hn
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;> simp_all

/-- The march of a side of `Φ` is the two ends of a line. -/
theorem Frame.exists_march (Φ : Frame S) {s : Set S} (hs : s ∈ arcComponentsIn (bd S \ Φ.V)) :
    ∃ u w, Φ.γ s = [u, w] ∧ IsLineWithEnds (closure s) u w := by
  obtain ⟨u₀, hu₀⟩ : (tilde s).Nonempty := by
    rw [← ncard_pos (Φ.side_shape s hs).2.1]
    rw [(Φ.side_shape s hs).1]
    norm_num
  obtain ⟨w, hne, ht, hL⟩ := Φ.exists_line hs hu₀
  rcases list_pair (Φ.γ_nodup s hs) (by rw [Φ.γ_set s hs, ht]) hne with h | h
  · exact ⟨u₀, w, h, hL⟩
  · exact ⟨w, u₀, h, hL.symm⟩

omit [T2Space S] in
/-- For two different points of a line, one order of the points agrees with the line. -/
theorem dirAgrees_of_ne {s e : Set S} {u w x y : S} (hL : IsLineWithEnds (closure s) u w)
  (hes : e ⊆ s)
    (hx : x ∈ closure s) (hy : y ∈ closure s) (hne : x ≠ y) :
    DirAgrees s [u, w] e [x, y] ∨ DirAgrees s [u, w] e [y, x] := by
  obtain ⟨f, hf₀, hf₁⟩ := hL
  have hft : f.symm ⟨x, hx⟩ ≠ f.symm ⟨y, hy⟩ := fun h ↦ hne (congrArg Subtype.val
    (f.symm.injective h))
  have hsx : (f (f.symm ⟨x, hx⟩)).1 = x := by simp
  have hsy : (f (f.symm ⟨y, hy⟩)).1 = y := by simp
  rcases lt_or_gt_of_ne hft with h | h
  · refine .inl ⟨f, _, _, h, hes, by simpa using hf₀.symm, by simpa using hf₁.symm, ?_, ?_⟩
    · simp
    · simp
  · refine .inr ⟨f, _, _, h, hes, by simpa using hf₀.symm, by simpa using hf₁.symm, ?_, ?_⟩
    · simp
    · simp

omit [T2Space S₁] in
/-- The two marches of an arc of a cuff are reverses of each other. -/
theorem arcMarch_true_eq (hS : IsSurface S₁) {e : Set S₁} {C : cuffs S₁} {a b : ℝ} (hab : a < b)
    (hub : b < a + 2 * Real.pi) (he : e = arcOf (cuffPar hS C) a b) :
    arcMarch hS true e = (arcMarch hS false e).reverse := by
  have hpi := Real.pi_pos
  obtain ⟨C₁, a₁, b₁, hab₁, hub₁, he₁, hl₁⟩ := arcMarch_spec hS true hab hub he
  obtain ⟨C₂, a₂, b₂, hab₂, hub₂, he₂, hl₂⟩ := arcMarch_spec hS false hab hub he
  have hCC : C₁ = C₂ := by
    by_contra hne
    have hx : cuffPoint (cuffPar hS C₁) ((a₁ + b₁) / 2) ∈ e :=
      he₁ ▸ ⟨_, ⟨by linarith, by linarith⟩, rfl⟩
    have h₁ : cuffPoint (cuffPar hS C₁) ((a₁ + b₁) / 2) ∈ C₁.1 := cuffPoint_mem _ _
    have h₂ := arcOf_subset _ _ _ (he₂ ▸ hx)
    exact disjoint_left.mp (cuffs_disjoint' hne) h₁ h₂
  subst hCC
  simp only [ite_true, Bool.false_eq_true, ite_false] at hl₁ hl₂
  obtain ⟨m, h₁, h₂⟩ := exists_shift (cuffPar hS C₁) hab₁ hab₂ hub₁ (by rw [← he₁, ← he₂])
  obtain ⟨m', h₃, h₄⟩ := exists_shift (cuffPar hS C₁) hab₂ hab₁ hub₂ (by rw [← he₂, ← he₁])
  have hsum : m + m' = 0 := by
    have hp₁ : 0 ≤ ((m + m' : ℤ) : ℝ) * (2 * Real.pi) := by
      push_cast
      linarith
    have hp₂ : ((m + m' : ℤ) : ℝ) * (2 * Real.pi) ≤ 0 := by
      push_cast
      linarith
    have h₅ : (0 : ℝ) ≤ ((m + m' : ℤ) : ℝ) := by nlinarith
    have h₆ : ((m + m' : ℤ) : ℝ) ≤ 0 := by nlinarith
    have h₅' : 0 ≤ m + m' := by exact_mod_cast h₅
    have h₆' : m + m' ≤ 0 := by exact_mod_cast h₆
    omega
  have hm' : (m' : ℝ) = -m := by
    have : ((m + m' : ℤ) : ℝ) = 0 := by rw [hsum]; simp
    push_cast at this
    linarith
  rw [hm'] at h₃ h₄
  have ha : a₂ + m * (2 * Real.pi) = a₁ := by linarith
  have hb : b₂ + m * (2 * Real.pi) = b₁ := by linarith
  rw [hl₁, hl₂, ← ha, ← hb, cuffPoint_shift, cuffPoint_shift]
  rfl

namespace FrameData

variable {Φ : Frame S} {Γ : Painting S} {K : Drawing S} {ψ : S₁ → S} (D : FrameData Φ Γ K ψ)
include D

/-- `ψ` maps the two ends of a side of the fragment over a side of `Φ` to different points. -/
theorem image_ends_ne {R : Set S₁} (hR : R ∈ arcComponentsIn (bd S₁ \ pullFrameV Φ K ψ)) {s : Set S}
    (hs : s ∈ Φ.sides) (hsub : ψ '' R ⊆ s) {a b : S₁} (hL : IsLineWithEnds (closure R) a b)
    (ht : tilde R = {a, b}) : ψ a ≠ ψ b := by
  classical
  have hc := D.pull.frag.continuous_ψ
  obtain ⟨f, hf₀, hf₁⟩ := hL
  obtain ⟨-, -, ⟨c⟩, -⟩ := Φ.side_shape s hs
  have hm : ∀ t, ψ (f t).1 ∈ closure s := fun t ↦
    closure_mono hsub (image_closure_subset_closure_image hc ⟨_, (f t).2, rfl⟩)
  let G : ℝ → ℝ := fun r ↦ (c.symm ⟨ψ (f (projIcc 0 1 zero_le_one r)).1, hm _⟩ : ℝ)
  have hGc : Continuous G := by
    refine continuous_subtype_val.comp (c.symm.continuous.comp (Continuous.subtype_mk ?_ _))
    exact hc.comp (continuous_subtype_val.comp (f.continuous.comp continuous_projIcc))
  have hmemR : ∀ t : unitInterval, t ≠ 0 → t ≠ 1 → (f t).1 ∈ R := by
    intro t ht₀ ht₁
    by_contra hn
    have : (f t).1 ∈ tilde R := ⟨(f t).2, hn⟩
    rw [ht] at this
    rcases this with h | h
    · exact ht₀ (f.injective (Subtype.ext (h.trans hf₀.symm)))
    · exact ht₁ (f.injective (Subtype.ext (h.trans hf₁.symm)))
  have hp : ∀ {q : ℝ}, q ∈ Ioo (0 : ℝ) 1 → ∃ t : unitInterval, projIcc 0 1 zero_le_one q = t ∧ t.1
    = q ∧
      t ≠ 0 ∧ t ≠ 1 := by
    intro q hq
    refine ⟨⟨q, hq.1.le, hq.2.le⟩, projIcc_of_mem _ _, rfl, fun h ↦ ?_, fun h ↦ ?_⟩
    · exact hq.1.ne' (congrArg Subtype.val h)
    · exact hq.2.ne (congrArg Subtype.val h)
  have hGi : InjOn G (Ioo 0 1) := by
    intro r hr r' hr' hrr
    obtain ⟨t, ht₁, ht₂, ht₃, ht₄⟩ := hp hr
    obtain ⟨t', ht'₁, ht'₂, ht'₃, ht'₄⟩ := hp hr'
    have hu := congrArg Subtype.val (c.symm.injective (Subtype.ext hrr))
    simp only [ht₁, ht'₁] at hu
    have hvv := D.injOn_side hR hR hs hs hsub hsub (hmemR t ht₃ ht₄) (hmemR t' ht'₃ ht'₄) hu
    have htt : t = t' := f.injective (Subtype.ext hvv)
    rw [← ht₂, ← ht'₂, htt]
  intro heq
  refine ne_of_injOn_Ioo hGc hGi ?_
  have e₀ : projIcc 0 1 zero_le_one (0 : ℝ) = (0 : unitInterval) := projIcc_left _
  have e₁ : projIcc 0 1 zero_le_one (1 : ℝ) = (1 : unitInterval) := projIcc_right _
  have hz : (⟨ψ (f (projIcc 0 1 zero_le_one (0 : ℝ))).1, hm _⟩ : closure s) =
      ⟨ψ (f (projIcc 0 1 zero_le_one (1 : ℝ))).1, hm _⟩ := by
    refine Subtype.ext ?_
    simp only [e₀, e₁]
    rw [hf₀, hf₁]
    exact heq
  exact congrArg (fun z ↦ ((c.symm z : unitInterval) : ℝ)) hz

/-- **The direction of each side of the frame of a fragment** (Graph Minors XIX, Section 5, page
336: "if $\psi(R) \subseteq S$ for some side $S$ of $\Phi$, then $R$ is directed such that $\psi$
maps its direction onto that of $S$"). There is such a
choice, because `ψ` maps the two ends of `R` to two different points of the closure of `S`. -/
theorem exists_flip : ∃ flip : Set S₁ → Bool, ∀ R ∈ arcComponentsIn (bd S₁ \ pullFrameV Φ K ψ), ∀ s
  ∈ Φ.sides,
    ψ '' R ⊆ s → DirAgrees s (Φ.γ s) (ψ '' R) ((arcMarch D.pull.frag.isSurface (flip R) R).map ψ)
      := by
  classical
  have hS₁ := D.pull.frag.isSurface
  let flip : Set S₁ → Bool := fun R ↦ !decide (∃ s ∈ Φ.sides, ψ '' R ⊆ s ∧
    DirAgrees s (Φ.γ s) (ψ '' R) ((arcMarch hS₁ false R).map ψ))
  refine ⟨flip, fun R hR s hs hsub ↦ ?_⟩
  have hc := D.pull.frag.continuous_ψ
  obtain ⟨C, a, b, hab, hub, he, -, -, -⟩ := exists_arc_of_mem hS₁ (cuffPar hS₁)
    D.finite_pullFrameV D.two hR
  have hrev := arcMarch_true_eq hS₁ hab hub he
  obtain ⟨C₂, a₂, b₂, hab₂, hub₂, he₂, hl₂⟩ := arcMarch_spec hS₁ false hab hub he
  simp only [Bool.false_eq_true, ite_false] at hl₂
  have hLR : IsLineWithEnds (closure R) (cuffPoint (cuffPar hS₁ C₂) a₂) (cuffPoint
    (cuffPar hS₁ C₂) b₂) := by
    rw [he₂]
    exact isLine_arcOf _ hab₂ hub₂
  have ht : tilde R = {cuffPoint (cuffPar hS₁ C₂) a₂, cuffPoint (cuffPar hS₁ C₂) b₂} := by
    rw [he₂]
    exact tilde_arcOf _ hab₂ hub₂
  have hne := D.image_ends_ne hR hs hsub hLR ht
  have hin : ∀ {x}, x ∈ closure R → ψ x ∈ closure s := fun hx ↦
    closure_mono hsub (image_closure_subset_closure_image hc ⟨_, hx, rfl⟩)
  obtain ⟨u, w, hγ, hL⟩ := Φ.exists_march hs
  have hmap : (arcMarch hS₁ false R).map ψ =
      [ψ (cuffPoint (cuffPar hS₁ C₂) a₂), ψ (cuffPoint (cuffPar hS₁ C₂) b₂)] := by
    rw [hl₂]
    rfl
  have hmaprev : (arcMarch hS₁ true R).map ψ =
      [ψ (cuffPoint (cuffPar hS₁ C₂) b₂), ψ (cuffPoint (cuffPar hS₁ C₂) a₂)] := by
    rw [hrev, hl₂]
    rfl
  have hdir := dirAgrees_of_ne hL hsub (hin hLR.left_mem) (hin hLR.right_mem) hne
  rw [← hγ, ← hmap, ← hmaprev] at hdir
  by_cases hex : ∃ s ∈ Φ.sides, ψ '' R ⊆ s ∧ DirAgrees s (Φ.γ s) (ψ '' R)
    ((arcMarch hS₁ false R).map ψ)
  · have hfl : flip R = false := by simp only [flip, hex, decide_true, Bool.not_true]
    rw [hfl]
    obtain ⟨s', hs', hsub', hd⟩ := hex
    obtain ⟨x, hx⟩ := hR.1
    have hss : s' = s := arcComp_eq_of_mem hs' hs (hsub' (mem_image_of_mem ψ hx)) (hsub
      (mem_image_of_mem ψ hx))
    exact hss ▸ hd
  · have hfl : flip R = true := by simp only [flip, hex, decide_false, Bool.not_false]
    rw [hfl]
    rcases hdir with h | h
    · exact absurd ⟨s, hs, hsub, h⟩ hex
    · exact h

omit [T2Space S] in
/-- The march of a side, or of a border edge of `Γ₁`, in the sense given by `flip`. -/
theorem nodup_arcMarch (flip : Bool) {N : Set S₁} (hN : N.Finite)
    (h2 : ∀ C : cuffs S₁, ∃ p ∈ N ∩ C.1, ∃ q ∈ N ∩ C.1, p ≠ q) {e : Set S₁}
      (he : e ∈ arcComponentsIn (bd S₁ \ N)) :
    (arcMarch D.pull.frag.isSurface flip e).Nodup ∧
      {v | v ∈ arcMarch D.pull.frag.isSurface flip e} = tilde e := by
  have hS := D.pull.frag.isSurface
  obtain ⟨C, a, b, hab, hub, he', -, -, -⟩ := exists_arc_of_mem hS (cuffPar hS) hN h2 he
  exact ⟨(arcMarch_spec hS flip hab hub he').nodup, (arcMarch_spec hS flip hab hub he').set_eq⟩

/-- The march of a border edge of `Γ₁`: "$\gamma_1(e)$ is defined such that the direction of $e$
agrees with the direction of the
side of $\psi^{-1}(\Phi) \cap \Sigma_1$ including it" (Graph Minors XIX, Section 5, page 336). -/
noncomputable def borderMarch (D : FrameData Φ Γ K ψ) (flip : Set S₁ → Bool) (e : Set S₁) : List S₁
  :=
  arcMarch D.pull.frag.isSurface (flip (sideOf Φ K ψ e)) e

/-- **Graph Minors XIX, (5.3).** With `K` a feature in `Φ` and `Γ` a painting that fits `Φ`, such
that each component
of `K` has a vertex of `Γ` in the sense of `IsAnchored`, the painting `ψ⁻¹(Γ) ∩ Σ₁` fits the frame
`ψ⁻¹(Φ) ∩ Σ₁`.
Any choice of `flip` works here, and `exists_flip` gives the one the paper asks for. -/
theorem theorem_5_3_proof [Nonempty S₁] [ConnectedSpace S] (hF : IsFeature Φ K)
  (hA : IsAnchored Γ K)
    (flip : Set S₁ → Bool) :
    (pullPainting D.pull (D.borderMarch flip)
      (fun _ hp ↦ (D.nodup_arcMarch _ D.pull.finite_pullV D.pull.two hp).1)
      (fun _ hp ↦ (D.nodup_arcMarch _ D.pull.finite_pullV D.pull.two hp).2)).Fits
      (pullFrame D flip (D.long_disjoint hF)) := by
  have hE : ∀ {p}, p ∈ arcComponentsIn (bd S₁ \ pullV Γ K ψ) →
      p ∈ arcComponentsIn (pullU Γ ψ \ pullV Γ K ψ) := fun {p} hp ↦ by
    rw [D.pull.arcComponentsIn_eq]
    exact Or.inl hp
  refine ⟨D.pullFrameV_subset, ?_, ?_, ?_, ?_⟩
  · rintro s ⟨hs, hnl⟩
    exact hE (D.mem_arcComponents_of_short hs hnl)
  · intro e he hb s hs hes
    have he' : e ∈ arcComponentsIn (pullU Γ ψ \ pullV Γ K ψ) := he
    rw [D.pull.arcComponentsIn_eq] at he'
    rcases he' with hp | ⟨e₀, he₀, hb₀, hne, rfl⟩
    · have hnl := D.pull.notMem_liftPieces hp
      change DirAgrees s (arcMarch _ (flip s) s) e (pullγ Γ ψ _ e)
      rw [pullγ_arc hnl]
      change DirAgrees s _ e (arcMarch _ (flip (sideOf Φ K ψ e)) e)
      rw [sideOf_eq hp.1 hs hes]
      exact D.dirAgrees_pull flip hp hs hes
    · obtain ⟨x, hx, hxb⟩ := hb
      exact absurd hxb (D.pull.preimage_subset_int (D.pull.subset_R he₀ hb₀ hne) hx)
  · exact D.pull.isInternallyThreeConnected _ _ _ D.fits.internally_three_connected hA
  · exact D.pull.size_three_region D.pull.surface _ _ _ D.fits.size_three_region hA

end FrameData

/-- `Frame.two_on_cuff` for a larger set. -/
theorem Frame.two_on_cuff' {A : Set S} (hS : IsSurface S) (Φ : Frame S) (C : cuffs S) :
    ∃ p ∈ (Φ.V ∪ A) ∩ C.1, ∃ q ∈ (Φ.V ∪ A) ∩ C.1, p ≠ q := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Frame.two_on_cuff hS Φ C
  exact ⟨p, ⟨Or.inl hp.1, hp.2⟩, q, ⟨Or.inl hq.1, hq.2⟩, hpq⟩

/-- A cut along `K` gives for each fragment the data of (5.3). -/
theorem exists_frameData (hS : IsSurface S) [ConnectedSpace S] {Φ : Frame S} {Γ : Painting S}
  (hfit : Γ.Fits Φ)
    {K : Drawing S} {𝓐 𝓛 : Set (Set S)} (hinter : Γ.U ∩ K.U ⊆ Γ.V ∩ K.V)
    (hlines : ∀ e ∈ arcComponentsIn (K.U \ K.V), ∃ u v, u ≠ v ∧ closure e ∩ K.V = {u, v} ∧
      IsLineWithEnds (closure e) u v)
    (hKne : K.V ⊆ ⋃ e ∈ arcComponentsIn (K.U \ K.V), closure e) (hF : IsCutFrame S 𝓐 𝓛)
    (hc : bd S ∪ K.U = ⋃₀ 𝓐 ∪ ⋃₀ 𝓛) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y) (ψ : Y → S), IsSurface Y ∧ IsCutMap ψ K.U
      ∧
      HasSheets ψ K ∧ ∀ y : Y, FrameData Φ Γ K (fun x : connectedComponent y ↦ ψ x.1) := by
  have hKbd : K.U ∩ bd S ⊆ K.V := fun x hx ↦ (hinter ⟨Γ.bd_subset hx.2, hx.1⟩).2
  obtain ⟨Y, tY, t2, ψ, hY, hψ, hsheet⟩ := exists_cut_drawing hS hlines hKbd hKne hF hc
  refine ⟨Y, tY, t2, ψ, hY, hψ, hsheet, fun y ↦ ⟨⟨hS, isCuttingFragment_of_cut hS hY hψ (K
    := K) rfl y, hinter,
    two_of_cut hS hY hψ hsheet hlines hKbd subset_union_right (fun C' ↦ ?_) y⟩, hfit,
    two_of_cut hS hY hψ hsheet hlines hKbd subset_union_right (Frame.two_on_cuff' hS Φ) y, hKbd⟩⟩
  obtain ⟨p, hp, q, hq, hpq⟩ := Frame.two_on_cuff hS Φ C'
  exact ⟨p, ⟨Or.inl (hfit.V_subset hp.1), hp.2⟩, q, ⟨Or.inl (hfit.V_subset hq.1), hq.2⟩, hpq⟩

end GraphMinor.GM19
