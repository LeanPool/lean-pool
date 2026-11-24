/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section5h

/-!
# Graph Minors XIX, proof of (5.4): frame vertices under an inflation

The proof of (5.4) says that a vertex `v'` of the frame satisfies `v' ∈ V(σ'(v'))`. The reason is
that some side at
`v'` is short, because two long sides have no common end, and an inflation that respects a frame
fixes each short
side with its direction. We also show that the direction condition of a linear inflation follows
from respecting the
frame, since both edges are directed as the side that holds them.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S] [T2Space S]


/-- An arc of `bd(Σ) \ N` on a cuff `Θ` is an arc of any parametrisation of `Θ`. -/
theorem exists_arc_param (_hS : IsSurface S) {Θ : Set S} (f : Circle ≃ₜ Θ) {N : Set S}
  (hN : N.Finite)
    {p q : S} (hp : p ∈ N ∩ Θ) (hq : q ∈ N ∩ Θ) (hpq : p ≠ q) (hΘ : Θ ⊆ bd S) {R : Set S}
    (hR : R ∈ arcComponentsIn (bd S \ N)) (hRΘ : R ⊆ Θ) :
    ∃ a b : ℝ, a < b ∧ b < a + 2 * Real.pi ∧ R = arcOf f a b ∧ cuffPoint f a ∈ N
      ∧ cuffPoint f b ∈ N := by
  obtain ⟨x, hx⟩ := hR.1
  obtain ⟨a, b, hab, hub, hxA, hd, ha, hb⟩ := exists_arc_of_two f hN hp hq hpq ⟨hRΘ hx,
    (hR.2.1 hx).2⟩
  refine ⟨a, b, hab, hub, ?_, ha, hb⟩
  refine Subset.antisymm ?_ ?_
  · exact subset_arcOf f hab hub hR.2.2.1.isConnected.isPreconnected hRΘ (fun h ↦ (hR.2.1 h).2 ha)
      (fun h ↦ (hR.2.1 h).2 hb) hx hxA
  · have hpc : IsPathConnected (arcOf f a b) := by
      refine IsPathConnected.image ?_ (continuous_cuffPoint f)
      exact (convex_Ioo a b).isPathConnected ⟨(a + b) / 2, by linarith, by linarith⟩
    have heq := hR.2.2.2 (R ∪ arcOf f a b) (by
      rintro y (hy | hy)
      · exact hR.2.1 hy
      · exact ⟨hΘ (arcOf_subset f a b hy), disjoint_left.mp hd hy⟩) (hR.2.2.1.union hpc ⟨x, hx,
          hxA⟩)
      subset_union_left
    exact fun y hy ↦ heq ▸ Or.inr hy

/-- Each point of a finite set `N` on the boundary, with two points of `N` on each cuff, is an end
of two arcs of
`bd(Σ) \ N`: the arcs just after it and just before it. -/
theorem exists_two_arcs (hS : IsSurface S) {N : Set S} (hN : N.Finite)
    (h2 : ∀ C : cuffs S, ∃ p ∈ N ∩ C.1, ∃ q ∈ N ∩ C.1, p ≠ q) {p : S} (hpN : p ∈ N)
      (hpb : p ∈ bd S) :
    ∃ R₁ ∈ arcComponentsIn (bd S \ N), ∃ R₂ ∈ arcComponentsIn (bd S \ N), R₁ ≠ R₂ ∧ p ∈ tilde R₁
      ∧ p ∈ tilde R₂ := by
  have hpi := Real.pi_pos
  obtain ⟨C₀, hC₀, hpC⟩ := sUnion_cuffs (S := S) ▸ hpb
  let C : cuffs S := ⟨C₀, hC₀⟩
  let f := cuffPar hS C
  obtain ⟨t, -, htp⟩ := exists_angle_in f 0 ⟨p, hpC⟩
  change cuffPoint f t = p at htp
  have hq : ∃ q ∈ N ∩ C.1, q ≠ p := by
    obtain ⟨p', hp', q', hq', hne⟩ := h2 C
    by_cases h : p' = p
    · exact ⟨q', hq', fun h' ↦ hne (h.trans h'.symm)⟩
    · exact ⟨p', hp', h⟩
  obtain ⟨q, hqN, hqp⟩ := hq
  obtain ⟨s₀, hs₀, hs₀q⟩ := exists_angle_in f t ⟨q, hqN.2⟩
  change cuffPoint f s₀ = q at hs₀q
  let A : Set ℝ := {s | s ∈ Ioo t (t + 2 * Real.pi) ∧ cuffPoint f s ∈ N}
  have hAfin : A.Finite := (finite_angles f hN t).subset fun s hs ↦ ⟨⟨hs.1.1.le, hs.1.2⟩, hs.2⟩
  have hAne : A.Nonempty := by
    refine ⟨s₀, ⟨lt_of_le_of_ne hs₀.1 ?_, hs₀.2⟩, hs₀q ▸ hqN.1⟩
    rintro rfl
    exact hqp (hs₀q.symm.trans htp)
  obtain ⟨b, hbA, hbmin⟩ := Set.exists_min_image A id hAfin hAne
  obtain ⟨c, hcA, hcmax⟩ := Set.exists_max_image A id hAfin hAne
  simp only [id] at hbmin hcmax
  have hbc : b ≤ c := hbmin c hcA
  have hub : b < t + 2 * Real.pi := hbA.1.2
  have hpc₁ : ∀ {u v : ℝ}, u < v → IsPathConnected (arcOf f u v) := fun {u v} huv ↦
    ((convex_Ioo u v).isPathConnected ⟨(u + v) / 2, by linarith, by linarith⟩).image
      (continuous_cuffPoint f)
  have hC : ∀ {z : ℝ}, cuffPoint f z ∉ N → cuffPoint f z ∈ bd S \ N := fun hz ↦
    ⟨cuff_subset_bd C (cuffPoint_mem f _), hz⟩
  have hA₁ : arcOf f t b ⊆ bd S \ N := by
    rintro _ ⟨z, hz, rfl⟩
    refine hC fun hzN ↦ ?_
    exact absurd (hbmin z ⟨⟨hz.1, by linarith [hz.2]⟩, hzN⟩) (not_le.mpr hz.2)
  have hct : c < t + 2 * Real.pi := hcA.1.2
  have hA₂ : arcOf f c (t + 2 * Real.pi) ⊆ bd S \ N := by
    rintro _ ⟨z, hz, rfl⟩
    refine hC fun hzN ↦ ?_
    exact absurd (hcmax z ⟨⟨by linarith [hz.1, hcA.1.1], hz.2⟩, hzN⟩) (not_le.mpr hz.1)
  obtain ⟨R₁, hR₁, hs₁⟩ := exists_arcComp_superset (hpc₁ hbA.1.1) hA₁
  obtain ⟨R₂, hR₂, hs₂⟩ := exists_arcComp_superset (hpc₁ hct) hA₂
  have hcl₁ : p ∈ closure (arcOf f t b) := by
    rw [closure_arcOf f hbA.1.1]
    exact ⟨t, ⟨le_rfl, hbA.1.1.le⟩, htp⟩
  have hcl₂ : p ∈ closure (arcOf f c (t + 2 * Real.pi)) := by
    rw [closure_arcOf f hct]
    exact ⟨t + 2 * Real.pi, ⟨hct.le, le_rfl⟩, by rw [cuffPoint_add_two_pi, htp]⟩
  refine ⟨R₁, hR₁, R₂, hR₂, ?_, ⟨closure_mono hs₁ hcl₁, fun h ↦ (hR₁.2.1 h).2 hpN⟩,
    ⟨closure_mono hs₂ hcl₂, fun h ↦ (hR₂.2.1 h).2 hpN⟩⟩
  rintro rfl
  have hxp : cuffPoint f ((t + b) / 2) ∈ R₁ := hs₁ ⟨_, ⟨by linarith [hbA.1.1], by linarith
    [hbA.1.1]⟩, rfl⟩
  have hxm : cuffPoint f ((c + (t + 2 * Real.pi)) / 2) ∈ R₁ := hs₂ ⟨_, ⟨by linarith, by linarith⟩,
    rfl⟩
  have hR₁C : R₁ ⊆ C.1 := by
    obtain ⟨C', a', b', -, -, rfl, -, -, -⟩ := exists_arc_of_mem hS (cuffPar hS) hN h2 hR₁
    have hCC : C' = C := by
      by_contra hne
      exact disjoint_left.mp (cuffs_disjoint' hne) (arcOf_subset _ _ _ hxp) (cuffPoint_mem f _)
    subst hCC
    exact arcOf_subset _ _ _
  have hsub := subset_arcOf f hbA.1.1 hub hR₁.2.2.1.isConnected.isPreconnected hR₁C
    (fun h ↦ (hR₁.2.1 h).2 (htp ▸ hpN)) (fun h ↦ (hR₁.2.1 h).2 hbA.2) hxp
    ⟨_, ⟨by linarith [hbA.1.1], by linarith [hbA.1.1]⟩, rfl⟩
  obtain ⟨u, hu, hue⟩ := hsub hxm
  have huv : u = (c + (t + 2 * Real.pi)) / 2 := cuffPoint_injOn f le_rfl
    ⟨hu.1.le, by linarith [hu.2]⟩ ⟨by linarith [hbA.1.1], by linarith⟩ hue
  linarith [hu.2]

/-- A vertex of a frame lies on a short side, since two sides end at it and they are not both long.
-/
theorem Frame.exists_short_side (hS : IsSurface S) (Φ : Frame S) {v : S} (hv : v ∈ Φ.V) :
    ∃ s ∈ Φ.shortSides, v ∈ tilde s := by
  obtain ⟨R₁, hR₁, R₂, hR₂, hne, h₁, h₂⟩ := exists_two_arcs hS Φ.finite_V
    (Frame.two_on_cuff hS Φ) hv (Φ.V_subset hv)
  by_cases hl₁ : Φ.isLong R₁
  · by_cases hl₂ : Φ.isLong R₂
    · exact absurd h₂ (disjoint_left.mp (Φ.long_disjoint R₁ hR₁ R₂ hR₂ hne hl₁ hl₂) h₁)
    · exact ⟨R₂, ⟨hR₂, hl₂⟩, h₂⟩
  · exact ⟨R₁, ⟨hR₁, hl₁⟩, h₁⟩

/-- The march of a side, read as an edge in the direction of the side, is the march of the side. -/
theorem Frame.march_eq (Φ : Frame S) {s : Set S} (hs : s ∈ Φ.sides) {l : List S} (hn : l.Nodup)
    (hset : {v | v ∈ l} = tilde s) (hd : DirAgrees s (Φ.γ s) s l) : l = Φ.γ s := by
  obtain ⟨u, w, hγ, hL⟩ := Φ.exists_march hs
  have ht : tilde s = {u, w} := by
    rw [← Φ.γ_set s hs, hγ]
    ext x
    simp
  have hne := (GM20.line_facts hL).1
  rcases list_pair hn (hset.trans ht) hne with rfl | rfl
  · exact hγ.symm
  · exfalso
    obtain ⟨f, t₁, t₂, hlt, -, h₁, h₂, h₃, h₄⟩ := hd
    rw [hγ] at h₁ h₂
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_cons_cons,
      List.getLast?_singleton] at h₁ h₂ h₃ h₄
    have e₁ : t₁ = ⟨1, right_mem_Icc.mpr zero_le_one⟩ := f.injective (Subtype.ext
      (h₃.symm.trans h₂))
    have e₂ : t₂ = ⟨0, left_mem_Icc.mpr zero_le_one⟩ := f.injective (Subtype.ext (h₄.symm.trans h₁))
    rw [e₁, e₂] at hlt
    exact absurd hlt (not_lt.mpr (by exact zero_le_one' ℝ))

omit [T2Space S] in
/-- Two edges in a side cannot both follow the direction of the side with the same two ends in
opposite order: the
two parametrisations of the side differ by an increasing map of `[0, 1]`. -/
theorem dirAgrees_not_reverse {s e e' : Set S} {γs : List S} {x y : S}
  (hd : DirAgrees s γs e [x, y])
    (hd' : DirAgrees s γs e' [y, x]) : False := by
  obtain ⟨f, t₁, t₂, hlt, -, h₁, h₂, h₃, h₄⟩ := hd
  obtain ⟨f', t₁', t₂', hlt', -, h₁', h₂', h₃', h₄'⟩ := hd'
  simp only [List.head?_cons, Option.some.injEq, List.getLast?_cons_cons,
    List.getLast?_singleton] at h₃ h₄ h₃' h₄'
  let h : unitInterval → unitInterval := fun t ↦ f'.symm (f t)
  have hc : Continuous h := f'.symm.continuous.comp f.continuous
  have hi : Function.Injective h := f'.symm.injective.comp f.injective
  have h0 : h ⊥ = ⊥ := by
    refine f'.injective (Subtype.ext ?_)
    simp only [h, Homeomorph.apply_symm_apply]
    exact Option.some.inj (h₁.symm.trans h₁')
  have h1 : h ⊤ = ⊤ := by
    refine f'.injective (Subtype.ext ?_)
    simp only [h, Homeomorph.apply_symm_apply]
    exact Option.some.inj (h₂.symm.trans h₂')
  have hmono : StrictMono h := hc.strictMono_of_inj_boundedOrder (by rw [h0, h1]; exact bot_le) hi
  have e₁ : h t₁ = t₂' := by
    refine f'.injective (Subtype.ext ?_)
    simp only [h, Homeomorph.apply_symm_apply]
    rw [← h₃, h₄']
  have e₂ : h t₂ = t₁' := by
    refine f'.injective (Subtype.ext ?_)
    simp only [h, Homeomorph.apply_symm_apply]
    rw [← h₄, h₃']
  have := hmono hlt
  rw [e₁, e₂] at this
  exact absurd hlt' (not_lt.mpr this.le)

/-- A subarc of an arc, in the direction of the arc. -/
theorem dirAgrees_arc {Θ : Set S} (f : Circle ≃ₜ Θ) {a b p q : ℝ} (hab : a < b)
    (hub : b < a + 2 * Real.pi) (hpq : p < q) (hsub : arcOf f p q ⊆ arcOf f a b) :
    DirAgrees (arcOf f a b) [cuffPoint f a, cuffPoint f b] (arcOf f p q) [cuffPoint f p, cuffPoint
      f q] ∧
      DirAgrees (arcOf f a b) [cuffPoint f b, cuffPoint f a] (arcOf f p q) [cuffPoint f q,
        cuffPoint f p] ∧
      q < p + 2 * Real.pi := by
  have hpi := Real.pi_pos
  obtain ⟨m, h₁, h₂⟩ := exists_shift f hab hpq hub hsub
  have hshift := arcOf_shift f p q m
  have hp₁ := cuffPoint_shift f p m
  have hp₂ := cuffPoint_shift f q m
  have hlt : p + m * (2 * Real.pi) < q + m * (2 * Real.pi) := by linarith
  refine ⟨?_, ?_, by linarith⟩
  · rw [← hshift, ← hp₁, ← hp₂]
    exact dirAgrees_forward f hub h₁ hlt h₂
  · rw [← hshift, ← hp₁, ← hp₂]
    exact dirAgrees_backward f hub h₁ hlt h₂

variable {Γ Γ' : Painting S} {Φ : Frame S} {σv : S → Set S} {σe : Set S → Set S}

/-- An inflation that respects a frame fixes each short side, and maps each end of it to a set that
holds the end. -/
theorem mem_σv_of_short (hf : Γ.Fits Φ) (hf' : Γ'.Fits Φ) (I : IsInflation Γ Γ' σv σe)
    (R : RespectsFrame Φ Γ σe) {s : Set S} (hs : s ∈ Φ.shortSides) {v : S}
      (hv : v ∈ tilde s) : v ∈ σv v := by
  have hsE := hf.short_sides hs
  have hsE' := hf'.short_sides hs
  obtain ⟨x, hx⟩ := hs.1.1
  have hb : Painting.IsBorder s := ⟨x, hx, (hs.1.2.1 hx).1⟩
  have hsub : σe s ⊆ s := ((R s hsE hb).2 s hs.1).mp subset_rfl
  have hσ : σe s = s := by
    have hE := I.edge_mem s hsE
    obtain ⟨y, hy⟩ := hE.1
    exact arcComp_eq_of_mem hE hsE' hy (hsub hy)
  have hγ := Φ.march_eq hs.1 (Γ.γ_nodup s hsE) (Γ.γ_set s hsE) (hf.border_dir s hsE hb s hs.1
    subset_rfl)
  have hγ' := Φ.march_eq hs.1 (Γ'.γ_nodup s hsE') (Γ'.γ_set s hsE')
    (hf'.border_dir s hsE' hb s hs.1 subset_rfl)
  obtain ⟨u, w, hm, -⟩ := Φ.exists_march hs.1
  have key := I.ends s hsE
  rw [hσ, hγ', hγ, hm] at key
  have hvm : v ∈ Φ.γ s := by
    have : v ∈ {x | x ∈ Φ.γ s} := (Φ.γ_set s hs.1).symm ▸ hv
    exact this
  rw [hm] at hvm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hvm
  rcases hvm with rfl | rfl
  · exact key 0 (by simp) (by simp)
  · exact key 1 (by simp) (by simp)

/-- An inflation that respects a frame keeps each vertex of the frame in its own set. -/
theorem mem_σv_of_frame (hS : IsSurface S) (hf : Γ.Fits Φ) (hf' : Γ'.Fits Φ)
  (I : IsInflation Γ Γ' σv σe)
    (R : RespectsFrame Φ Γ σe) {v : S} (hv : v ∈ Φ.V) : v ∈ σv v := by
  obtain ⟨s, hs, hvs⟩ := Φ.exists_short_side hS hv
  exact mem_σv_of_short hf hf' I R hs hvs

omit [T2Space S] in
/-- The march of an edge in a side. -/
theorem Painting.march_of_arc (Γ : Painting S) {e : Set S} (he : e ∈ Γ.E) {x y : S} (hne : x ≠ y)
    (ht : tilde e = {x, y}) : Γ.γ e = [x, y] ∨ Γ.γ e = [y, x] :=
  list_pair (Γ.γ_nodup e he) ((Γ.γ_set e he).trans ht) hne

/-- The direction condition of a linear inflation holds for two edges of one side. Each edge is
directed as the side,
so if `e` runs forward along `f` then so does the side, and so does `e'`. -/
theorem immediatelyPrecedes_transfer (hS : IsSurface S) (hf : Γ.Fits Φ)
  (hf' : Γ'.Fits Φ) {e e' s : Set S}
    (he : e ∈ Γ.E) (he' : e' ∈ arcComponentsIn (bd S \ Γ'.V)) (he'E : e' ∈ Γ'.E) (hs : s ∈ Φ.sides)
      (hes : e ⊆ s)
    (hes' : e' ⊆ s) (hb : Painting.IsBorder e) (hb' : Painting.IsBorder e') {Θ : Set S}
    (hΘ : Θ ∈ cuffs S) (hsΘ : (s ∩ Θ).Nonempty) (f : Circle ≃ₜ Θ) {n n' : S}
    (hn : (Γ.γ e).head? = some n) (hn' : (Γ'.γ e').head? = some n') (hp : ImmediatelyPrecedes f n
      e) :
    ImmediatelyPrecedes f n' e' := by
  have hpi := Real.pi_pos
  have hΘb : Θ ⊆ bd S := cuff_subset_bd ⟨Θ, hΘ⟩
  have hsΘ' : s ⊆ Θ := by
    obtain ⟨C, a, b, -, -, hsC, -, -, -⟩ := exists_arc_of_mem hS (cuffPar hS) Φ.finite_V
      (Frame.two_on_cuff hS Φ) hs
    have hCC : C.1 = Θ := by
      by_contra hne
      obtain ⟨x, hx₁, hx₂⟩ := hsΘ
      have hne' : C ≠ ⟨Θ, hΘ⟩ := fun h ↦ hne (congrArg Subtype.val h)
      exact disjoint_left.mp (cuffs_disjoint' hne') (arcOf_subset _ _ _ (hsC ▸ hx₁)) hx₂
    rw [hsC]
    exact hCC ▸ arcOf_subset _ _ _
  obtain ⟨p₀, hp₀, q₀, hq₀, hpq₀⟩ := Frame.two_on_cuff hS Φ ⟨Θ, hΘ⟩
  obtain ⟨a, b, hab, hub, hsab, haV, hbV⟩ := exists_arc_param hS f Φ.finite_V hp₀ hq₀ hpq₀ hΘb hs
    hsΘ'
  obtain ⟨t₀, t₁, ht, -, htn, he₀⟩ := hp
  have he₀' : e = arcOf f t₀ t₁ := he₀
  obtain ⟨hd₁, hd₂, hut⟩ := dirAgrees_arc f hab hub ht (by rw [← he₀', ← hsab]; exact hes)
  have hnet := (GM20.line_facts (isLine_arcOf f hab hub)).1
  have hγs : Φ.γ s = [cuffPoint f a, cuffPoint f b] ∨ Φ.γ s = [cuffPoint f b, cuffPoint f a] :=
    list_pair (Φ.γ_nodup s hs) ((Φ.γ_set s hs).trans (by rw [hsab, tilde_arcOf f hab hub])) hnet
  have hdirΓ := hf.border_dir e he hb s hs hes
  have hsplit : Γ.γ e = [cuffPoint f t₀, cuffPoint f t₁] := by
    have hne := (GM20.line_facts (isLine_arcOf f ht hut)).1
    rcases Γ.march_of_arc he hne (by rw [he₀', tilde_arcOf f ht hut]) with h | h
    · exact h
    · rw [h] at hn
      simp only [List.head?_cons, Option.some.injEq] at hn
      exact absurd (hn.trans htn.symm) hne.symm
  rw [hsplit] at hdirΓ
  rw [he₀'] at hdirΓ
  rcases hγs with hγs | hγs
  · -- the side runs forward
    rw [hγs, hsab] at hdirΓ
    obtain ⟨p', hp', q', hq', hpq'⟩ := id (show ∃ p' ∈ Γ'.V ∩ Θ, ∃ q' ∈ Γ'.V ∩ Θ, p' ≠ q' from
      ⟨p₀, ⟨hf'.V_subset hp₀.1, hp₀.2⟩, q₀, ⟨hf'.V_subset hq₀.1, hq₀.2⟩, hpq₀⟩)
    obtain ⟨p, q, hpq, hu, hee, -, -⟩ := exists_arc_param hS f Γ'.finite_V hp' hq' hpq' hΘb he'
      (hes'.trans hsΘ')
    obtain ⟨hd₃, -, -⟩ := dirAgrees_arc f hab hub hpq (by rw [← hee, ← hsab]; exact hes')
    have hdirΓ' := hf'.border_dir e' he'E hb' s hs hes'
    have hne' := (GM20.line_facts (isLine_arcOf f hpq hu)).1
    rcases Γ'.march_of_arc he'E hne' (by rw [hee, tilde_arcOf f hpq hu]) with h | h
    · rw [h] at hn'
      simp only [List.head?_cons, Option.some.injEq] at hn'
      exact ⟨p, q, hpq, hu.le, hn', hee⟩
    · rw [h, hγs, hsab, hee] at hdirΓ'
      exact (dirAgrees_not_reverse hd₃ hdirΓ').elim
  · rw [hγs, hsab] at hdirΓ
    exact (dirAgrees_not_reverse hd₂ hdirΓ).elim

end GraphMinor.GM19
