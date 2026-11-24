/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.CutDrawing2

/-!
# Cutting a surface along lines

`exists_cut_lines` cuts a connected surface along a finite set of lines that meet only at a finite
set `N` of
points. Over each point of a line off `N` there are two points of the cut surface, and every compact
part of
the line off `N` lies in a part with two lifts. This is all that XIX needs about the cuts of Section
5 and
Sections 10, 11 and 14.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Function GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]
  {W : ℕ → List Letter} {f : ℕ × ℂ → S} {V : Set S} {E : Set (Set S)} {A : Set S → unitInterval → S}
  {lab : Set S → ℕ}

/-- A line in the graph of a word, with ends at vertices, is a chain of edges. -/
theorem exists_chain_of_line (hw : WordEdges W f V E A lab) {L : Set S} {u v : S} (hne : u ≠ v)
    (hl : IsLineWithEnds L u v) (hu : u ∈ V) (hv : v ∈ V) (hLg : L ⊆ gr V E) :
    ∃ (ι : ℝ → S) (m : ℕ) (t : ℕ → ℝ) (ss : ℕ → Set S) (ε : ℕ → Bool), Continuous ι ∧ InjOn ι
      (Icc 0 1) ∧
      ι '' Icc 0 1 = L ∧ ι 0 = u ∧ ι 1 = v ∧ 0 < m ∧ t 0 = 0 ∧ t m = 1 ∧ (∀ p < m, t p < t (p + 1))
        ∧
      (∀ x ∈ Icc (0 : ℝ) 1, ι x ∈ V → ∃ p ≤ m, x = t p) ∧
      (∀ p < m, ss p ∈ E ∧ ι '' Icc (t p) (t (p + 1)) = ss p ∧
        ∀ τ, extI (A (ss p)) (eo τ) = ι (t (chainAt ε p τ))) ∧
      (∀ p < m, ∀ q < m, p ≠ q → ss p ≠ ss q) ∧ ⋃₀ (ss '' Iio m) = L := by
  obtain ⟨a, ha, rfl, rfl, rfl⟩ := hl.exists_arc
  have hιc := continuous_extI ha.1
  have hinj := extI_injOn ha.2
  have hval0 : extI a 0 = a 0 := extI_coe a 0
  have hval1 : extI a 1 = a 1 := extI_coe a 1
  have himg : extI a '' Icc 0 1 = range a := image_extI a
  obtain ⟨m, τ, ss, ε, hm, ht0, htm, hlt, hV, hch, hsne⟩ := exists_chain hw.graph A hw.arc hιc
    (hinj.mono Ico_subset_Icc_self) (hinj.mono Ioc_subset_Icc_self) (himg ▸ hLg)
    (by rw [hval0]; exact hu) (by rw [hval1]; exact hv)
    (.inl (by rw [hval0, hval1]; exact hne))
  refine ⟨extI a, m, τ, ss, ε, hιc, hinj, himg, hval0, hval1, hm, ht0, htm, hlt, hV,
    fun p hp ↦ ⟨(hch p hp).1, (hch p hp).2.1, fun σ ↦ chain_hex (hch p hp).2.2.1
      (hch p hp).2.2.2 σ⟩, hsne, ?_⟩
  have hτI : ∀ k ≤ m, τ k ∈ Icc (0 : ℝ) 1 := fun k hk =>
    ⟨ht0 ▸ chain_mono' hlt (Nat.zero_le k) hk, htm ▸ chain_mono' hlt hk le_rfl⟩
  have hsF : ∀ p < m, ss p ⊆ range a := fun p hp => by
    rw [← (hch p hp).2.1, ← himg]
    exact image_mono (Icc_subset_Icc (hτI p hp.le).1 (hτI (p + 1) hp).2)
  apply subset_antisymm
  · rintro z ⟨_, ⟨p, hp, rfl⟩, hz⟩
    exact hsF p hp hz
  · have key : ∀ k, k ≤ m → extI a '' Icc 0 (τ k) ⊆ ⋃₀ (ss '' Iio m) := by
      intro k
      induction k with
      | zero =>
        intro _ z hz
        obtain ⟨x, hx, rfl⟩ := hz
        rw [ht0] at hx
        have hx0 : x = 0 := le_antisymm hx.2 hx.1
        refine ⟨ss 0, ⟨0, hm, rfl⟩, ?_⟩
        rw [← (hch 0 hm).2.1, ht0]
        exact ⟨x, ⟨hx.1, by rw [hx0]; exact (ht0 ▸ hlt 0 hm).le⟩, rfl⟩
      | succ k ih =>
        intro hk z hz
        obtain ⟨x, hx, rfl⟩ := hz
        by_cases hxk : x ≤ τ k
        · exact ih (by omega) ⟨x, ⟨hx.1, hxk⟩, rfl⟩
        · refine ⟨ss k, ⟨k, by simpa using hk, rfl⟩, ?_⟩
          rw [← (hch k (by omega)).2.1]
          exact ⟨x, ⟨(not_le.mp hxk).le, hx.2⟩, rfl⟩
    have := key m le_rfl
    rw [htm, himg] at this
    exact this

/-- A compact part of an open interval lies in a smaller closed interval, which we may ask to hold a
finite
set too. -/
theorem exists_Icc_of_compact {Q : Set ℝ} (hQ : IsCompact Q) (hsub : Q ⊆ Ioo 0 1) :
    ∃ a b, 0 < a ∧ a < b ∧ b < 1 ∧ Q ⊆ Ioo a b := by
  have hQ' : IsCompact (insert (1 / 2 : ℝ) Q) := hQ.insert _
  have hsub' : insert (1 / 2 : ℝ) Q ⊆ Ioo 0 1 := insert_subset (by norm_num) hsub
  obtain ⟨x, hx, hxm⟩ := hQ'.exists_isMinOn (insert_nonempty _ _) continuous_id.continuousOn
  obtain ⟨y, hy, hym⟩ := hQ'.exists_isMaxOn (insert_nonempty _ _) continuous_id.continuousOn
  have h1 := hsub' hx
  have h2 := hsub' hy
  have h3 : x ≤ 1 / 2 := hxm (mem_insert _ _)
  have h4 : 1 / 2 ≤ y := hym (mem_insert _ _)
  refine ⟨x / 2, (y + 1) / 2, by linarith [h1.1], by linarith [h1.1], by linarith [h2.2],
    fun z hz ↦ ?_⟩
  have h5 : x ≤ z := hxm (mem_insert_of_mem _ hz)
  have h6 : z ≤ y := hym (mem_insert_of_mem _ hz)
  exact ⟨by linarith [h1.1], by linarith [h2.2]⟩

omit [TopologicalSpace S] [T2Space S] in
private theorem chainParameter_injective {ι : ℝ → S} {t : ℕ → ℝ} {m : ℕ}
    (hlt : ∀ p < m, t p < t (p + 1)) (hτI : ∀ k ≤ m, t k ∈ Icc (0 : ℝ) 1)
    (hinj : InjOn ι (Icc (0 : ℝ) 1)) :
    ∀ k ≤ m, ∀ k' ≤ m, ι (t k) = ι (t k') → k = k' := by
  intro k hk k' hk' he
  have heq := hinj (hτI k hk) (hτI k' hk') he
  rcases lt_trichotomy k k' with hlt' | heq' | hgt
  · exact absurd heq (chain_mono hlt hlt' hk').ne
  · exact heq'
  · exact absurd heq (chain_mono hlt hgt hk).ne'

/-- **Cutting along lines.** The lines `𝓔` meet each other and the boundary only in the finite set
`N`. The
map `ψ` is one to one off the lines and has finite fibres, and the lift of the lines lies in the
boundary. Each
compact part `Q` of a line off `N` lies in a part `L'` of that line with two lifts. -/
theorem exists_cut_lines (hS : IsSurface S) [ConnectedSpace S] {N : Set S} {𝓔 𝓐 𝓛 : Set (Set S)}
  (hN : N.Finite)
    (h𝓔 : 𝓔.Finite) (hline : ∀ L ∈ 𝓔, ∃ u v, u ≠ v ∧ IsLineWithEnds L u v ∧ L ∩ N = {u, v})
    (hdisj : ∀ L ∈ 𝓔, ∀ L' ∈ 𝓔, L ≠ L' → L ∩ L' ⊆ N) (hbd : ∀ L ∈ 𝓔, L ∩ bd S ⊆ N) (hNs : N ⊆ ⋃₀ 𝓔)
    (hF : IsCutFrame S 𝓐 𝓛) (hc : bd S ∪ ⋃₀ 𝓔 = ⋃₀ 𝓐 ∪ ⋃₀ 𝓛) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : T2Space Y) (ψ : Y → S), IsSurface Y ∧ Continuous ψ
      ∧
      Function.Surjective ψ ∧ InjOn ψ (ψ ⁻¹' (⋃₀ 𝓔)ᶜ) ∧ (∀ x, (ψ ⁻¹' {x}).Finite) ∧ ψ ⁻¹'
        (⋃₀ 𝓔) ⊆ bd Y ∧
      ∀ L ∈ 𝓔, ∀ Q ⊆ L \ N, IsCompact Q → ∃ L' ⊆ L, Q ⊆ L' ∧ ∃ u v X X', LiftPair ψ L' u v X X'
        := by
  classical
  obtain ⟨V₀, E₀, hNV, hg, hV₀, hU, h𝓔E⟩ := exists_graph_of_lines hS hN h𝓔 hline hdisj hbd
    (hNs.trans subset_union_right)
  obtain ⟨V, E, 𝓕, hd, hVV, hEE⟩ := exists_dissection_lines hS hg hV₀ hF (hU.trans hc)
  obtain ⟨W, f, A, lab, hw, hdn⟩ := exists_word_edges hS hd
  have hLg : ∀ L ∈ 𝓔, L ⊆ gr V E := fun L hL ↦
    (subset_sUnion_of_mem (h𝓔E hL)).trans hEE
  have hchain : ∀ L ∈ 𝓔, ∃ u v, u ≠ v ∧ IsLineWithEnds L u v ∧ L ∩ N = {u, v} ∧ u ∈ V ∧ v ∈ V
    := fun L hL ↦ by
    obtain ⟨u, v, huv, hl, hi⟩ := hline L hL
    have hu : u ∈ L ∩ N := hi ▸ mem_insert _ _
    have hv : v ∈ L ∩ N := hi ▸ mem_insert_of_mem _ rfl
    exact ⟨u, v, huv, hl, hi, hVV (hNV hu.2), hVV (hNV hv.2)⟩
  let D : Set (Set S) := {e ∈ E | ∃ L ∈ 𝓔, e ⊆ L}
  have hDE : D ⊆ E := fun e he ↦ he.1
  have hmemD : ∀ L ∈ 𝓔, ∀ x ∈ L, ∃ e ∈ D, x ∈ e ∧ e ⊆ L := fun L hL x hx ↦ by
    obtain ⟨u, v, huv, hl, -, hu, hv⟩ := hchain L hL
    obtain ⟨ι, m, t, ss, ε, -, -, himg, -, -, -, -, -, -, -, hch, -, hun⟩ :=
      exists_chain_of_line hw huv hl hu hv (hLg L hL)
    obtain ⟨_, ⟨p, hp, rfl⟩, hxp⟩ := hun.symm ▸ hx
    have hsub : ss p ⊆ L := fun z hz ↦ hun ▸ ⟨ss p, ⟨p, hp, rfl⟩, hz⟩
    exact ⟨ss p, ⟨(hch p hp).1, L, hL, hsub⟩, hxp, hsub⟩
  have hUD : ⋃₀ D = ⋃₀ 𝓔 := by
    apply subset_antisymm
    · rintro x ⟨e, ⟨-, L, hL, heL⟩, hx⟩
      exact ⟨L, hL, heL hx⟩
    · rintro x ⟨L, hL, hx⟩
      obtain ⟨e, he, hxe, -⟩ := hmemD L hL x hx
      exact ⟨e, he, hxe⟩
  have hmid : ∀ e ∈ D, edgeMid A e ∉ bd S := by
    rintro e ⟨heE, L, hL, heL⟩ hb
    have hmem : edgeMid A e ∈ L ∩ bd S := ⟨heL (hw.extI_mem heE _), hb⟩
    exact hw.extI_notMem heE (show (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 by norm_num) (hVV (hNV
      (hbd L hL hmem)))
  obtain ⟨Y, tY, t2, ψ, h1, h2, h3, h4, h5, h6, hlift⟩ := WordEdges.exists_cut hw hS hdn hDE hmid
  rw [hUD] at h4 h6
  refine ⟨Y, tY, t2, ψ, h1, h2, h3, h4, h5, h6, ?_⟩
  intro L hL Q hQ hQc
  obtain ⟨u, v, huv, hl, hi, hu, hv⟩ := hchain L hL
  obtain ⟨ι, m, t, ss, ε, hιc, hinj, himg, h0, h1', hm, ht0, htm, hlt, hV, hch, hsne, hun⟩ :=
    exists_chain_of_line hw huv hl hu hv (hLg L hL)
  -- the parameter set of `Q`
  have hQcl : IsClosed Q := hQc.isClosed
  let Q' : Set ℝ := Icc 0 1 ∩ ι ⁻¹' Q
  have hQ'c : IsCompact Q' := isCompact_Icc.inter_right (hQcl.preimage hιc)
  have hQ'I : Q' ⊆ Ioo 0 1 := by
    rintro x ⟨hx, hxQ⟩
    have hoff := (hQ hxQ).2
    refine ⟨lt_of_le_of_ne hx.1 fun h ↦ hoff ?_, lt_of_le_of_ne hx.2 fun h ↦ hoff ?_⟩
    · rw [← h, h0]
      exact (show u ∈ L ∩ N from hi ▸ mem_insert _ _).2
    · rw [h, h1']
      exact (show v ∈ L ∩ N from hi ▸ mem_insert_of_mem _ rfl).2
  have hτI : ∀ k ≤ m, t k ∈ Icc (0 : ℝ) 1 := fun k hk =>
    ⟨ht0 ▸ chain_mono' hlt (Nat.zero_le k) hk, htm ▸ chain_mono' hlt hk le_rfl⟩
  have hin : ∀ k, 0 < k → k < m → t k ∈ Ioo (0 : ℝ) 1 := fun k h0' hk ↦
    ⟨ht0 ▸ chain_mono hlt h0' hk.le, htm ▸ chain_mono hlt hk le_rfl⟩
  let Tf : Set ℝ := t '' {k | 0 < k ∧ k < m}
  have hfinite : {k | 0 < k ∧ k < m}.Finite :=
    (Set.finite_Iio m).subset fun _ hk => hk.2
  have hTf : Tf.Finite := hfinite.image t
  obtain ⟨a, b, ha0, hab, hb1, hsubab⟩ := exists_Icc_of_compact (hQ'c.union hTf.isCompact)
    (union_subset hQ'I (by rintro _ ⟨k, hk, rfl⟩; exact hin k hk.1 hk.2))
  have hta : ∀ k, 0 < k → k < m → a < t k ∧ t k < b := fun k h0' hk ↦
    hsubab (.inr ⟨k, ⟨h0', hk⟩, rfl⟩)
  have hm0 : m ≠ 0 := hm.ne'
  let ι' : ℝ → S := fun x ↦ ι (x + a)
  let T : ℕ → ℝ := fun k ↦ if k = 0 then 0 else if k = m then b - a else t k - a
  have hT0 : T 0 = 0 := by simp [T]
  have hTm : T m = b - a := by simp [T, hm0]
  have hTin : ∀ k, 0 < k → k < m → T k = t k - a := fun k h0' hk ↦ by
    simp [T, h0'.ne', hk.ne]
  have hlow : ∀ p < m, t p ≤ T p + a := fun p hp ↦ by
    rcases Nat.eq_zero_or_pos p with rfl | h
    · rw [hT0, ht0]
      linarith
    · rw [hTin p h hp]
      linarith
  have hhigh : ∀ p < m, T (p + 1) + a ≤ t (p + 1) := fun p hp ↦ by
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hp) with h | h
    · have e : p + 1 = m := h
      rw [e, hTm, htm]
      linarith
    · rw [hTin (p + 1) (by omega) h]
      linarith
  have hlt' : ∀ p < m, T p < T (p + 1) := fun p hp ↦ by
    rcases Nat.eq_zero_or_pos p with rfl | h0'
    · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hp) with h | h
      · have e : 0 + 1 = m := h
        rw [e, hT0, hTm]
        linarith
      · rw [hT0, hTin (0 + 1) (by omega) h]
        linarith [(hta (0 + 1) (by omega) h).1]
    · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hp) with h | h
      · have e : p + 1 = m := h
        rw [e, hTm, hTin p h0' hp]
        linarith [(hta p h0' hp).2]
      · rw [hTin p h0' hp, hTin (p + 1) (by omega) h]
        linarith [hlt p hp]
  have hTI : ∀ k ≤ m, T k + a ∈ Icc a b := fun k hk ↦ by
    rcases Nat.eq_zero_or_pos k with rfl | h0'
    · rw [hT0]
      constructor <;> linarith
    rcases eq_or_lt_of_le hk with rfl | h
    · rw [hTm]
      constructor <;> linarith
    · rw [hTin k h0' h]
      have := hta k h0' h
      constructor <;> linarith
  have habI : Icc a b ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ha0.le hb1.le
  have hx01 : ∀ {x}, x ∈ Icc (0 : ℝ) (T m) → x + a ∈ Icc a b := fun {x} hx ↦ by
    rw [hTm] at hx
    constructor <;> linarith [hx.1, hx.2]
  have hι'inj : InjOn ι' (Icc 0 (T m)) := fun x hx y hy he ↦ by
    have := hinj (habI (hx01 hx)) (habI (hx01 hy)) he
    linarith
  have hι'c : Continuous ι' := by fun_prop
  have hinjk := chainParameter_injective hlt hτI hinj
  have hssL : ∀ p < m, ss p ⊆ L := fun p hp z hz ↦ hun ▸ ⟨ss p, ⟨p, hp, rfl⟩, hz⟩
  have hssD : ∀ p < m, ss p ∈ D := fun p hp ↦ ⟨(hch p hp).1, L, hL, hssL p hp⟩
  have hoffN : ∀ k, 0 < k → k < m → ι (t k) ∉ N := fun k h0' hk hmem ↦ by
    have hmemL : ι (t k) ∈ L := himg ▸ mem_image_of_mem ι (hτI k hk.le)
    have hI := hin k h0' hk
    have : ι (t k) ∈ ({u, v} : Set S) := hi ▸ ⟨hmemL, hmem⟩
    rcases this with h5 | h5
    · have := hinj (hτI k hk.le) ⟨le_rfl, zero_le_one⟩ (h5.trans h0.symm)
      linarith [hI.1]
    · have := hinj (hτI k hk.le) ⟨zero_le_one, le_rfl⟩ (h5.trans h1'.symm)
      linarith [hI.2]
  have hlift' : ∀ p < m, ∃ X X', LiftPair ψ (ι' '' Icc (T p) (T (p + 1))) (ι' (T p)) (ι' (T
    (p + 1))) X X' := by
    intro p hp
    obtain ⟨r, r', hr⟩ := hlift (ss p) (hssD p hp)
    have hrange : ∀ x ∈ Icc (T p) (T (p + 1)), x + a ∈ Icc (t p) (t (p + 1)) := fun x hx ↦
      ⟨(hlow p hp).trans (by linarith [hx.1]), le_trans (by linarith [hx.2]) (hhigh p hp)⟩
    refine liftPair_of_piece hw (hch p hp).1 hr (hlt' p hp) hι'c.continuousOn ?_ ?_ ?_
    · intro x hx y hy he
      have hI : ∀ {z}, z ∈ Icc (T p) (T (p + 1)) → z + a ∈ Icc (0 : ℝ) 1 := fun {z} hz ↦
        ⟨(hτI p hp.le).1.trans (hrange z hz).1, (hrange z hz).2.trans (hτI (p + 1) hp).2⟩
      have := hinj (hI hx) (hI hy) he
      linarith
    · rintro _ ⟨x, hx, rfl⟩
      rw [← (hch p hp).2.1]
      exact mem_image_of_mem ι (hrange x hx)
    · intro x hx τ he
      have hex := (hch p hp).2.2 τ
      obtain ⟨k, hk⟩ : ∃ k, chainAt ε p τ = k := ⟨_, rfl⟩
      have hkm : k ≤ m := by
        rw [← hk]
        unfold chainAt
        split_ifs <;> omega
      have hxI : x + a ∈ Icc a b := by
        have hle1 := hTI p hp.le
        have hle2 := hTI (p + 1) hp
        exact ⟨hle1.1.trans (by linarith [hx.1]), le_trans (by linarith [hx.2]) hle2.2⟩
      have h5 : x + a = t k := hinj (habI hxI) (hτI k hkm) (by
        change ι' x = _
        rw [he, hex, hk])
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with rfl | h
        · rw [ht0] at h5
          linarith [hxI.1]
        · exact h
      have hkm' : k < m := by
        rcases eq_or_lt_of_le hkm with rfl | h
        · rw [htm] at h5
          linarith [hxI.2]
        · exact h
      refine endFine_of_chain (fun q hq σ ↦ (hch q hq).2.2 σ) hinjk hsne hssD hp (by rwa [hk])
        (by rwa [hk])
        ?_ ?_
      · rw [hk]
        intro hb'
        have hmemL : ι (t k) ∈ L := himg ▸ mem_image_of_mem ι (hτI k hkm)
        exact hoffN k hk0 hkm' (hbd L hL ⟨hmemL, hb'⟩)
      · rw [hk]
        rintro e'' ⟨he''E, L'', hL'', heL⟩ τ'' hend
        have hwL : ι (t k) ∈ L := himg ▸ mem_image_of_mem ι (hτI k hkm)
        have hwe : ι (t k) ∈ e'' := hend ▸ hw.extI_mem he''E _
        obtain rfl : L'' = L := by
          by_contra hne
          exact hoffN k hk0 hkm' (hdisj L hL L'' hL'' (Ne.symm hne) ⟨hwL, heL hwe⟩)
        have hmidm : extI (A e'') (1 / 2) ∈ L'' := heL (hw.extI_mem he''E _)
        obtain ⟨_, ⟨q, hq, rfl⟩, hxq⟩ := hun.symm ▸ hmidm
        refine ⟨q, hq, ?_⟩
        by_contra hne
        exact hw.extI_notMem he''E (show (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 by norm_num)
          (hw.graph.disj e'' he''E (ss q) (hch q hq).1 hne ⟨hw.extI_mem he''E _, hxq⟩)
  obtain ⟨X, X', hX⟩ := chain_fold (ψ := ψ) (ι := ι') (t := T)
    (ss := fun p ↦ ι' '' Icc (T p) (T (p + 1))) hlt' hT0 (fun _ _ ↦ rfl) hlift' hm le_rfl hι'inj
  refine ⟨ι' '' Icc 0 (T m), ?_, ?_, _, _, X, X', hX⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact himg ▸ mem_image_of_mem ι (habI (hx01 hx))
  · intro z hz
    obtain ⟨x, hx, rfl⟩ : z ∈ ι '' Icc 0 1 := himg ▸ (hQ hz).1
    have hx' : x ∈ Ioo a b := hsubab (.inl ⟨hx, hz⟩)
    refine ⟨x - a, ⟨by linarith [hx'.1], by rw [hTm]; linarith [hx'.2]⟩, ?_⟩
    simp [ι']

end GraphMinor.GM19
