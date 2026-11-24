/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.OneWord
public import LeanPool.GraphMinor.Surface.WordTrack
public import LeanPool.GraphMinor.Surface.CutNull

/-!
# Pasting polygons and keeping a set off the seam

`exists_one_word` pastes a family of polygons into one, but it does not say which sides stay. For
the sketch on page 216
of Graph Minors VII we need more: all sides of the last word must avoid the open edges of the graph.
So we keep a record
along the way. `OffSides Bad B W f` says that sides of `W` with a label outside `Bad` avoid `B`.
Pasting two polygons along a
label keeps this record (`exists_net_merge`), and so does pasting all polygons into one
(`exists_one_word_off`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Metric Function GraphMinor.Surface

universe u

variable {T : Type u} [TopologicalSpace T] [T2Space T]

/-- The sides of `W` with a label outside `Bad` avoid `B`. -/
def OffSides (Bad : Set ℕ) (B : Set T) (W : ℕ → List Letter) (f : ℕ × ℂ → T) : Prop :=
  ∀ i p k ε, (W i)[p]? = some (k, ε) → k ∉ Bad → ∀ t ∈ Icc (0 : ℝ) 1, f (i, sdPt
    (W i).length p ε t) ∉ B

omit [T2Space T] in
theorem eq_of_stp {W : ℕ → List Letter} {f : ℕ × ℂ → T} (hf : Presents W f) {a b : ℕ × ℂ}
  (h : Stp W a b) : f a = f b :=
  (hf.2.2 _ h.mem_Dsk.1 _ h.mem_Dsk.2).mpr (.rel _ _ h)

variable {Bad : Set ℕ} {B : Set T} {W W' : ℕ → List Letter} {f : ℕ × ℂ → T}

theorem OffSides.of_trk {K : Set ℕ} (h : Trk.{u} K W W') (hf : Presents W f)
  (hok : OffSides Bad B W f)
    (hsub : ∀ (i p c : ℕ) (ε : Bool), (W' i)[p]? = some (c, ε) → c ∉ Bad → c ∈ K ∧ ∃ (i₀ p₀ : ℕ)
      (ε₀ : Bool), (W i₀)[p₀]? = some (c, ε₀)) :
    ∃ f', Presents W' f' ∧ OffSides Bad B W' f' := by
  obtain ⟨f', hf', hv⟩ := h T f hf
  refine ⟨f', hf', fun i p c ε h1 hc t ht he => ?_⟩
  obtain ⟨hK, i₀, p₀, ε₀, h0⟩ := hsub i p c ε h1 hc
  obtain ⟨i', p', h2, h3⟩ := hv c hK i₀ p₀ ε₀ h0
  have h4 := hok i₀ p₀ c ε₀ h0 hc t ht
  rw [← h3 t ht] at h4
  by_cases hs : (i, p) = (i', p')
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hs
    rw [h1] at h2
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h2)
    exact h4 he
  · have h5 := eq_of_stp hf' (a := (i, sdPt (W' i).length p ε t)) (b := (i', sdPt
      (W' i').length p' ε₀ t))
      ⟨i, i', p, p', c, ε, ε₀, t, h1, h2, hs, ht, rfl, rfl⟩
    exact h4 (h5 ▸ he)

omit [T2Space T] in
theorem OffSides.rev {i : ℕ} {w : List Letter} (hf : Presents (update W i w) f)
  (hok : OffSides Bad B (update W i w) f) :
    ∃ f', Presents (update W i (winv w)) f' ∧ OffSides Bad B (update W i (winv w)) f' := by
  refine ⟨_, hf.of_map isPolyMap_rev, fun s p c ε h1 hc t ht => ?_⟩
  by_cases hs : s = i
  · subst hs
    rw [update_self] at h1 ⊢
    have hp : p < (winv w).length := (List.getElem?_eq_some_iff.mp h1).1
    have hlen : (winv w).length = w.length := by simp [winv]
    rw [hlen] at hp
    have hget : w[w.length - 1 - p]? = some (c, !ε) := by
      rw [winv, List.getElem?_map, List.getElem?_reverse hp] at h1
      obtain ⟨l, hl, hl'⟩ := Option.map_eq_some_iff.mp h1
      rw [hl]
      have e1 : l = linv (c, ε) := by rw [← hl', linv_linv]
      rw [e1]
      rfl
    have h2 := hok s (w.length - 1 - p) c (!ε) (by rw [update_self]; exact hget) hc t ht
    rw [update_self] at h2
    simp only [comp_apply, ite_true, hlen, conj_sdPt hp]
    exact h2
  · rw [update_of_ne hs] at h1 ⊢
    have h2 := hok s p c ε (by rw [update_of_ne hs]; exact h1) hc t ht
    rw [update_of_ne hs] at h2
    simp only [comp_apply, hs, ite_false]
    exact h2

theorem exists_getElem_of_mem {w : List Letter} {l : Letter} (h : l ∈ w) : ∃ p : ℕ, w[p]? = some l
  := by
  obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp h
  exact ⟨p, by simp [hp]⟩

/-- Pasting along a label with opposite signs. -/
theorem exists_merge_opp (hW : FinW W) (hf : Presents W f) (hok : OffSides Bad B W f) {i j k : ℕ}
  {e : Bool} (hij : j ≠ i)
    (h0 : (k, e) ∈ W i) (h1 : (k, !e) ∈ W j) (c0 : cnt (W i) k = 1) (c1 : cnt (W j) k = 1)
    (hoth : ∀ s, s ≠ i → s ≠ j → cnt (W s) k = 0) (l0 : 2 ≤ (W i).length) (l1 : 2 ≤ (W j).length) :
    ∃ w f', Presents (update (update W j []) i w) f' ∧ OffSides Bad B (update
      (update W j []) i w) f' ∧ 2 ≤ w.length ∧
      cnt w k = 0 ∧ ∀ c, cnt w c ≤ cnt (W i) c + cnt (W j) c := by
  obtain ⟨a, b, ha⟩ := List.append_of_mem h0
  obtain ⟨c, d, hc⟩ := List.append_of_mem h1
  have hc0 : cnt (b ++ a) k = 0 := by
    have h2 : cnt a k + (1 + cnt b k) = 1 := by simpa [ha, cnt_append, cnt_cons] using c0
    rw [cnt_append]
    omega
  have hc1 : cnt (d ++ c) k = 0 := by
    have h2 : cnt c k + (1 + cnt d k) = 1 := by simpa [hc, cnt_append, cnt_cons] using c1
    rw [cnt_append]
    omega
  have hl0 : 1 ≤ (b ++ a).length := by
    rw [ha] at l0
    simp at l0 ⊢
    omega
  have hl1 : 1 ≤ (d ++ c).length := by
    rw [hc] at l1
    simp at l1 ⊢
    omega
  have hu : b ++ a ≠ [] := fun h => by simp [h] at hl0
  have hv : d ++ c ≠ [] := fun h => by simp [h] at hl1
  have s1 : Trk.{u} univ W (update W i ((k, e) :: (b ++ a))) := by
    have := trk_rot.{u} (W := W) (i := i) a ((k, e) :: b)
    rw [← ha, update_eq_self] at this
    simpa using this
  have s2 : Trk.{u} univ (update W i ((k, e) :: (b ++ a)))
      (update (update W i ((k, e) :: (b ++ a))) j ((k, !e) :: (d ++ c))) := by
    have hj1 : update W i ((k, e) :: (b ++ a)) j = c ++ (k, !e) :: d := by rw [update_of_ne hij, hc]
    have := trk_rot.{u} (W := update W i ((k, e) :: (b ++ a))) (i := j) c ((k, !e) :: d)
    rw [← hj1, update_eq_self] at this
    simpa using this
  have e2 : update (update W i ((k, e) :: (b ++ a))) j ((k, !e) :: (d ++ c)) =
      update (update (update W j []) i ((k, e) :: (b ++ a))) j ((k, !e) :: (d ++ c)) := by
    funext s
    by_cases hs : s = j
    · subst hs
      simp
    · by_cases hs' : s = i
      · subst hs'
        simp [update_of_ne hs]
      · simp [update_of_ne hs, update_of_ne hs']
  have hy : FreshIn (update (update W j []) i (d ++ c ++ (b ++ a))) k := by
    intro s l hl
    by_cases hs : s = i
    · subst hs
      rw [update_self] at hl
      exact (noLab_append.mpr ⟨noLab_of_cnt hc1, noLab_of_cnt hc0⟩) l hl
    · rw [update_of_ne hs] at hl
      by_cases hs' : s = j
      · subst hs'
        simp at hl
      · rw [update_of_ne hs'] at hl
        exact noLab_of_cnt (hoth s hs hs') l hl
  have s3 := trk_glue.{u} (W := update W j []) (i := i) (j := j) (y := k) (u := b ++ a) (v
    := d ++ c) (hW.update _ _) e hij
    (by simp) hu hv hy
  rw [← e2] at s3
  have hT : Trk.{u} {k}ᶜ W (update (update W j []) i (d ++ c ++ (b ++ a))) :=
    (s1.restrict fun _ _ => .inl (mem_univ _)).trans ((s2.restrict fun _ _ => .inl
      (mem_univ _)).trans s3)
  obtain ⟨f', hf', hok'⟩ := hok.of_trk hT hf (by
    intro s p x ε h2 _
    have hmem : (x, ε) ∈ update (update W j []) i (d ++ c ++ (b ++ a)) s := List.mem_of_getElem? h2
    refine ⟨fun hx => hy s (x, ε) hmem hx, ?_⟩
    by_cases hs : s = i
    · subst hs
      rw [update_self] at hmem
      simp only [List.mem_append] at hmem
      have h3 : (x, ε) ∈ W s ∨ (x, ε) ∈ W j := by
        rw [ha, hc]
        simp only [List.mem_append, List.mem_cons]
        tauto
      rcases h3 with h3 | h3
      · obtain ⟨q, hq⟩ := exists_getElem_of_mem h3
        exact ⟨s, q, ε, hq⟩
      · obtain ⟨q, hq⟩ := exists_getElem_of_mem h3
        exact ⟨j, q, ε, hq⟩
    · rw [update_of_ne hs] at h2
      by_cases hs' : s = j
      · subst hs'
        simp at h2
      · rw [update_of_ne hs'] at h2
        exact ⟨s, p, ε, h2⟩)
  refine ⟨_, f', hf', hok', ?_, ?_, fun x => ?_⟩
  · simp only [List.length_append] at hl0 hl1 ⊢
    omega
  · rw [cnt_append, hc1, hc0]
  · rw [ha, hc]
    simp only [cnt_append, cnt_cons]
    split_ifs <;> omega

/-- Pasting two polygons along a label. -/
theorem exists_net_merge (hW : FinW W) (hf : Presents W f) (hok : OffSides Bad B W f) {i j k : ℕ}
  {e e' : Bool} (hij : j ≠ i)
    (h0 : (k, e) ∈ W i) (h1 : (k, e') ∈ W j) (c0 : cnt (W i) k = 1) (c1 : cnt (W j) k = 1)
    (hoth : ∀ s, s ≠ i → s ≠ j → cnt (W s) k = 0) (l0 : 2 ≤ (W i).length) (l1 : 2 ≤ (W j).length) :
    ∃ w f', Presents (update (update W j []) i w) f' ∧ OffSides Bad B (update
      (update W j []) i w) f' ∧ 2 ≤ w.length ∧
      cnt w k = 0 ∧ ∀ c, cnt w c ≤ cnt (W i) c + cnt (W j) c := by
  by_cases he : e' = !e
  · subst he
    exact exists_merge_opp hW hf hok hij h0 h1 c0 c1 hoth l0 l1
  · have he' : e' = e := by
      cases e <;> cases e' <;> simp_all
    subst he'
    have hup : update W j (W j) = W := update_eq_self _ _
    obtain ⟨f₁, hf₁, hok₁⟩ := OffSides.rev (W := W) (i := j) (w := W j) (by rwa [hup])
      (by rwa [hup])
    have hmem : (k, !e') ∈ winv (W j) := by
      have : linv (k, e') ∈ winv (W j) := by
        simp only [winv, List.mem_reverse, List.mem_map]
        exact ⟨_, h1, rfl⟩
      simpa [linv] using this
    obtain ⟨w, f', h2, h3, h4, h5, h6⟩ := exists_merge_opp (hW.update _ _) hf₁ hok₁ hij
      (by rwa [update_of_ne hij.symm]) (by simpa using hmem) (by rwa [update_of_ne hij.symm])
      (by simpa [cnt_winv] using c1) (fun s h h' => by rw [update_of_ne h']; exact hoth s h h')
      (by rwa [update_of_ne hij.symm]) (by simpa [winv] using l1)
    refine ⟨w, f', by simpa using h2, by simpa using h3, h4, h5, fun c => ?_⟩
    have := h6 c
    simpa [update_of_ne hij.symm, cnt_winv] using this

/-- `exists_one_word`, with a record that the sides stay off a set. -/
theorem exists_one_word_off {X : Type u} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] {B :
  Set X} (n : ℕ) :
    ∀ (S : Finset ℕ) (W : ℕ → List Letter) (f : ℕ × ℂ → X), S.card = n → FinW W → W 0 ≠ []
      → Presents W f →
    OffSides ∅ B W f → (∀ i, W i ≠ [] → 2 ≤ (W i).length) → (∀ i, i ∉ S → W i = []) →
    (∀ c, ∑ i ∈ S, cnt (W i) c ≤ 2) → ∃ (w : List Letter) (g : ℕ × ℂ → X), 2 ≤ w.length ∧ Good w
      ∧ Presents (sW w) g ∧
      OffSides ∅ B (sW w) g := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S W f hn hW h0 hf hok hlen hS hsum
  have h0S : 0 ∈ S := by
    by_contra h
    exact h0 (hS 0 h)
  by_cases hall : ∀ j, j ≠ 0 → W j = []
  · have e : W = sW (W 0) := by
      funext i
      by_cases hi : i = 0
      · subst hi
        simp [sW]
      · simp [sW, nW, update_of_ne hi, hall i hi]
    refine ⟨W 0, f, hlen 0 h0, fun c => ?_, e ▸ hf, e ▸ hok⟩
    exact (Finset.single_le_sum (f := fun i => cnt (W i) c) (fun _ _ => Nat.zero_le _) h0S).trans
      (hsum c)
  push Not at hall
  obtain ⟨j₀, hj₀, hne⟩ := hall
  obtain ⟨j, k, e, e', hj, m0, m1⟩ := exists_shared hW hf h0 hj₀ hne
  have hjne : W j ≠ [] := fun he => by simp [he] at m1
  have hjS : j ∈ S := by
    by_contra h
    exact hjne (hS j h)
  have split : ∀ c, cnt (W j) c + (cnt (W 0) c + ∑ i ∈ (S.erase j).erase 0, cnt (W i) c) ≤ 2
    := fun c => by
    have h1 := Finset.add_sum_erase S (fun i => cnt (W i) c) hjS
    have h2 := Finset.add_sum_erase (S.erase j) (fun i => cnt (W i) c)
      (Finset.mem_erase.mpr ⟨hj.symm, h0S⟩)
    have h3 := hsum c
    omega
  have p0 : 0 < cnt (W 0) k := cnt_pos (w := W 0) (l := (k, e)) m0
  have p1 : 0 < cnt (W j) k := cnt_pos (w := W j) (l := (k, e')) m1
  have hk := split k
  have hrest : ∀ i, i ≠ 0 → i ≠ j → cnt (W i) k = 0 := by
    intro i hi0 hij
    by_cases hiS : i ∈ S
    · have h1 : i ∈ (S.erase j).erase 0 := Finset.mem_erase.mpr ⟨hi0, Finset.mem_erase.mpr ⟨hij,
        hiS⟩⟩
      have h2 := Finset.single_le_sum (f := fun i => cnt (W i) k) (fun _ _ => Nat.zero_le _) h1
      omega
    · rw [hS i hiS]
      rfl
  obtain ⟨w, g, hg, hokg, hwl, -, hwc⟩ := exists_net_merge hW hf hok hj m0 m1 (by omega)
    (by omega) hrest (hlen 0 h0)
    (hlen j hjne)
  have hwne : w ≠ [] := fun he => by simp [he] at hwl
  refine ih (S.erase j).card ?_ (S.erase j) _ g rfl ((hW.update _ _).update _ _)
    (by simpa using hwne) hg hokg ?_ ?_ ?_
  · rw [← hn]
    exact Finset.card_erase_lt_of_mem hjS
  · intro i hi
    by_cases hi0 : i = 0
    · subst hi0
      simpa using hwl
    · rw [update_of_ne hi0] at hi ⊢
      by_cases hij : i = j
      · subst hij
        simp at hi
      · rw [update_of_ne hij] at hi ⊢
        exact hlen i hi
  · intro i hi
    have hi0 : i ≠ 0 := fun h => hi (Finset.mem_erase.mpr ⟨h ▸ hj.symm, h ▸ h0S⟩)
    rw [update_of_ne hi0]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [update_of_ne hij]
      exact hS i fun h => hi (Finset.mem_erase.mpr ⟨hij, h⟩)
  · intro c
    have h1 := Finset.add_sum_erase (S.erase j) (fun i => cnt (update (update W j []) 0 w i) c)
      (Finset.mem_erase.mpr ⟨hj.symm, h0S⟩)
    have h2 : ∑ i ∈ (S.erase j).erase 0, cnt (update (update W j []) 0 w i) c =
        ∑ i ∈ (S.erase j).erase 0, cnt (W i) c := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi0 := (Finset.mem_erase.mp hi).1
      have hij := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      rw [update_of_ne hi0, update_of_ne hij]
    simp only [update_self] at h1
    have h3 := hwc c
    have h4 := split c
    omega

/-- The number of letters of `w` with a label in `Bad`. -/
noncomputable def bc (Bad : Set ℕ) (w : List Letter) : ℕ := open Classical in w.countP fun l
  => l.1 ∈ Bad

theorem bc_append (a b : List Letter) : bc Bad (a ++ b) = bc Bad a + bc Bad b := by
  classical
  simp [bc, List.countP_append]

theorem bc_cons (l : Letter) (a : List Letter) : bc Bad (l :: a) = (open Classical in if l.1 ∈ Bad
  then 1 else 0) + bc Bad a := by
  classical
  simp only [bc, List.countP_cons, decide_eq_true_eq]
  split_ifs <;> omega

theorem bc_nil : bc Bad [] = 0 := rfl

theorem bc_pos {w : List Letter} {l : Letter} (h : l ∈ w) (hl : l.1 ∈ Bad) : 0 < bc Bad w := by
  classical
  exact List.countP_pos_iff.mpr ⟨l, h, by simpa using hl⟩

theorem exists_split_two {w : List Letter} (h : 2 ≤ bc Bad w) : ∃ v u, w = v ++ u ∧ 1 ≤ bc Bad v
  ∧ 1 ≤ bc Bad u := by
  classical
  induction w with
  | nil => simp [bc_nil] at h
  | cons l w ih =>
    rw [bc_cons] at h
    by_cases hl : l.1 ∈ Bad
    · simp only [hl, ite_true] at h
      refine ⟨[l], w, rfl, ?_, by omega⟩
      rw [bc_cons, bc_nil]
      simp [hl]
    · simp only [hl, ite_false] at h
      obtain ⟨v, u, rfl, h1, h2⟩ := ih (by omega)
      refine ⟨l :: v, u, rfl, ?_, h2⟩
      rw [bc_cons]
      omega

/-- Two different labels of `Bad` use up two letters. -/
theorem cnt_add_cnt_le_bc {w : List Letter} {c k : ℕ} (hc : c ∈ Bad) (hk : k ∈ Bad)
  (hne : c ≠ k) : cnt w c + cnt w k ≤ bc Bad w := by
  classical
  induction w with
  | nil => simp [cnt_nil, bc_nil]
  | cons l w ih =>
    rw [bc_cons, cnt_cons, cnt_cons]
    by_cases h1 : l.1 = c
    · have h2 : l.1 ≠ k := fun h => hne (h1.symm.trans h)
      simp only [h1, ite_true, hc]
      simp only [h1] at h2
      simp only [h2, ite_false]
      omega
    · by_cases h2 : l.1 = k
      · simp only [h2, ite_true, hk]
        simp only [h2] at h1
        simp only [h1, ite_false]
        omega
      · simp only [h1, h2, ite_false]
        split_ifs <;> omega

theorem cnt_le_bc {w : List Letter} {c : ℕ} (hc : c ∈ Bad) : cnt w c ≤ bc Bad w := by
  classical
  induction w with
  | nil => simp [cnt_nil, bc_nil]
  | cons l w ih =>
    rw [bc_cons, cnt_cons]
    by_cases h1 : l.1 = c
    · simp only [h1, ite_true, hc]
      omega
    · simp only [h1, ite_false]
      split_ifs <;> omega

/-- The points of the discs over `B` are on open sides with a label in `Bad`. -/
def OnBad (Bad : Set ℕ) (B : Set T) (W : ℕ → List Letter) (f : ℕ × ℂ → T) : Prop :=
  ∀ a ∈ Dsk W, f a ∈ B → ∃ (i p k : ℕ) (ε : Bool) (u : ℝ), (W i)[p]? = some (k, ε) ∧ k ∈ Bad
    ∧ u ∈ Ioo (0 : ℝ) 1 ∧ a = spt W i p u

omit [TopologicalSpace T] [T2Space T] in
theorem OnBad.offSides (h : OnBad Bad B W f) : OffSides Bad B W f := by
  intro i p k ε h1 hk t ht hb
  have hmem : (i, sdPt (W i).length p ε t) ∈ Dsk W := by
    refine ⟨fun he => ?_, (norm_per _ _).le⟩
    simp [he] at h1
  obtain ⟨i', p', k', ε', u, h2, hk', hu, he⟩ := h _ hmem hb
  rw [spt, Prod.mk.injEq] at he
  obtain ⟨rfl, he⟩ := he
  rw [sdPt_eq] at he
  obtain ⟨rfl, -⟩ := side_unique (lt_length h2) (lt_length h1) hu (ofs_mem ht) he.symm
  rw [h1] at h2
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h2)
  exact hk hk'

theorem isPaired_of_sum {S : Finset ℕ} (hS : ∀ i, i ∉ S → W i = []) (hsum : ∀ c, ∑ i ∈ S, cnt
  (W i) c ≤ 2) : IsPaired W := by
  classical
  intro k
  have key : ∀ S : Finset ℕ, {s : ℕ × ℕ | s.1 ∈ S ∧ ∃ e, (W s.1)[s.2]? = some (k, e)}.encard ≤
    ((∑ i ∈ S, cnt (W i) k : ℕ) : ℕ∞) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [Finset.sum_insert ha]
      have hs : {s : ℕ × ℕ | s.1 ∈ insert a S ∧ ∃ e, (W s.1)[s.2]? = some (k, e)} ⊆
          (fun p => (a, p)) '' {p : ℕ | ∃ e, (W a)[p]? = some (k, e)} ∪ {s : ℕ × ℕ | s.1 ∈ S ∧ ∃ e,
            (W s.1)[s.2]? = some (k, e)} := by
        rintro ⟨i, p⟩ ⟨h1, h2⟩
        rcases Finset.mem_insert.mp h1 with h3 | h3
        · simp only at h3
          subst h3
          exact .inl ⟨p, h2, rfl⟩
        · exact .inr ⟨h3, h2⟩
      refine (encard_le_encard hs).trans ((encard_union_le _ _).trans ?_)
      rw [Nat.cast_add]
      exact add_le_add ((encard_image_le _ _).trans (idx_encard_le _ _)) ih
  have hs : {s : ℕ × ℕ | ∃ e, (W s.1)[s.2]? = some (k, e)} ⊆ {s : ℕ × ℕ | s.1 ∈ S ∧ ∃ e,
    (W s.1)[s.2]? = some (k, e)} := by
    rintro s ⟨e, he⟩
    refine ⟨?_, e, he⟩
    by_contra h
    simp [hS _ h] at he
  refine (encard_le_encard hs).trans ((key S).trans ?_)
  exact_mod_cast hsum k

theorem sum_update_two {F : List Letter → ℕ} {S : Finset ℕ} {i j : ℕ} (hi : i ∈ S) (hj : j ∉ S)
  (x y : List Letter) :
    ∑ s ∈ insert j S, F (update (update W i x) j y s) = F y + (F x + ∑ s ∈ S.erase i, F (W s)) := by
  classical
  have hij : j ≠ i := fun h => hj (h ▸ hi)
  rw [Finset.sum_insert hj, ← Finset.add_sum_erase S _ hi]
  simp only [update_self, update_of_ne hij.symm]
  congr 2
  refine Finset.sum_congr rfl fun s hs => ?_
  have h1 : s ≠ i := (Finset.mem_erase.mp hs).1
  have h2 : s ≠ j := fun h => hj (h ▸ (Finset.mem_erase.mp hs).2)
  rw [update_of_ne h2, update_of_ne h1]

omit [T2Space T] in
/-- Cutting a polygon along a chord keeps all points over `B` on open sides with a label in `Bad`.
-/
theorem OnBad.cut (hon : OnBad Bad B W f) (hf : Presents W f) {i j y : ℕ} {u v : List Letter}
  (hw : W i = v ++ u) (hij : j ≠ i)
    (hWj : W j = []) (hu : u ≠ []) (hv : v ≠ []) (hy : FreshIn W y)
    (hP : IsPaired (update (update W i ((y, true) :: u)) j ((y, false) :: v))) :
    ∃ f', Presents (update (update W i ((y, true) :: u)) j ((y, false) :: v)) f' ∧
      OnBad Bad B (update (update W i ((y, true) :: u)) j ((y, false) :: v)) f' := by
  have e0 : update W i (v ++ u) = W := by rw [← hw, update_eq_self]
  obtain ⟨θ, hθ, -, hup⟩ := exists_isPolyMap_cut (W := W) (u := u) (v := v) (y := y) (e
    := true) hij hWj hu hv (by rwa [e0])
  rw [e0] at hθ hup
  refine ⟨_, hf.of_map hθ, fun a ha hb => ?_⟩
  obtain ⟨i', p', k, ε, w, h1, hk, hw', he⟩ := hon _ (hθ.maps ha) hb
  obtain ⟨s, q, h2, h3⟩ := hup i' p' k ε h1
  have hwm : ofs ε w ∈ Icc (0 : ℝ) 1 := ofs_mem ⟨hw'.1.le, hw'.2.le⟩
  have h4 := h3 _ hwm
  have hspt : spt W i' p' w = (i', sdPt (W i').length p' ε (ofs ε w)) := by
    rw [spt, sdPt_eq, ofs_ofs]
  have hmem : (s, sdPt ((update (update W i ((y, true) :: u)) j ((y, false) :: v)) s).length q ε
    (ofs ε w)) ∈
      Dsk (update (update W i ((y, true) :: u)) j ((y, false) :: v)) := by
    refine ⟨fun he => ?_, (norm_per _ _).le⟩
    simp [he] at h2
  have hrel := hθ.fib _ hmem a ha (h4.trans (by rw [← hspt, he]))
  have hw2 : ofs ε (ofs ε w) ∈ Ioo (0 : ℝ) 1 := by rwa [ofs_ofs]
  have hsp : (s, sdPt ((update (update W i ((y, true) :: u)) j ((y, false) :: v)) s).length q ε
    (ofs ε w)) =
      spt (update (update W i ((y, true) :: u)) j ((y, false) :: v)) s q (ofs ε (ofs ε w)) := by
    rw [spt, sdPt_eq]
  rw [hsp] at hrel
  rcases hrel.eq_or_stp hP h2 hw2 with h5 | h5
  · exact ⟨s, q, k, ε, _, h2, hk, hw2, h5⟩
  · obtain ⟨j', q', e', h6, -, h7⟩ := stp_of_side hP h2 hw2 h5
    exact ⟨j', q', k, e', _, h6, hk, flp_mem' hw2, h7⟩

theorem exists_fresh_label (hW : FinW W) (hBad : Bad.Finite) : ∃ y, FreshIn W y ∧ y ∉ Bad := by
  classical
  have h1 : (⋃ i ∈ {i | W i ≠ []}, (↑((W i).map Prod.fst).toFinset : Set ℕ)).Finite :=
    hW.biUnion fun _ _ => Finset.finite_toSet _
  obtain ⟨y, hy⟩ := (h1.union hBad).exists_notMem
  refine ⟨y, fun i l hl he => hy (.inl ?_), fun h => hy (.inr h)⟩
  have hne : W i ≠ [] := fun h => by simp [h] at hl
  simp only [mem_iUnion]
  refine ⟨i, hne, ?_⟩
  simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
  exact ⟨l, hl, he⟩

theorem cnt_fresh {y s : ℕ} (hy : FreshIn W y) : cnt (W s) y = 0 := by
  rw [cnt, List.countP_eq_zero]
  intro l hl
  simpa using hy s l hl

omit [T2Space T] in
/-- Cut the polygons along chords until each has at most one letter with a label in `Bad`. This is
the cut of the sketch at each
corner: a polygon with one such letter is a sector. -/
theorem exists_sectors (hBad : Bad.Finite) (m : ℕ) : ∀ (S : Finset ℕ) (W : ℕ → List Letter)
  (f : ℕ × ℂ → T),
    ∑ i ∈ S, (bc Bad (W i) - 1) = m → FinW W → W 0 ≠ [] → Presents W f → OnBad Bad B W f →
      (∀ i, W i ≠ [] → 2 ≤ (W i).length) →
    (∀ i, i ∉ S → W i = []) → (∀ c, ∑ i ∈ S, cnt (W i) c ≤ 2) → ∃ (S' : Finset ℕ) (W' : ℕ
      → List Letter) (f' : ℕ × ℂ → T),
      FinW W' ∧ W' 0 ≠ [] ∧ Presents W' f' ∧ OnBad Bad B W' f' ∧ (∀ i, W' i ≠ [] → 2 ≤
        (W' i).length) ∧ (∀ i, i ∉ S' → W' i = []) ∧
      (∀ c, ∑ i ∈ S', cnt (W' i) c ≤ 2) ∧ (∀ i, bc Bad (W' i) ≤ 1) ∧ ∀ c ∈ Bad, ∑ i ∈ S', cnt
        (W' i) c = ∑ i ∈ S, cnt (W i) c := by
  classical
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro S W f hm hW h0 hf hon hlen hS hsum
  by_cases hall : ∀ i, bc Bad (W i) ≤ 1
  · exact ⟨S, W, f, hW, h0, hf, hon, hlen, hS, hsum, hall, fun _ _ => rfl⟩
  push Not at hall
  obtain ⟨i, hi⟩ := hall
  obtain ⟨v, u, hw, hv1, hu1⟩ := exists_split_two (Bad := Bad) (w := W i) (by omega)
  have hiS : i ∈ S := by
    by_contra h
    rw [hS i h] at hi
    simp [bc_nil] at hi
  have hu : u ≠ [] := fun h => by simp [h, bc_nil] at hu1
  have hv : v ≠ [] := fun h => by simp [h, bc_nil] at hv1
  obtain ⟨y, hy, hyB⟩ := exists_fresh_label hW hBad
  obtain ⟨j, hj⟩ := (hW.union S.finite_toSet).exists_notMem
  have hjS : j ∉ S := fun h => hj (.inr h)
  have hWj : W j = [] := by
    by_contra h
    exact hj (.inl h)
  have hij : j ≠ i := fun h => hjS (h ▸ hiS)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact h0 hWj
  set W' := update (update W i ((y, true) :: u)) j ((y, false) :: v) with hW'
  have hsumF : ∀ F : List Letter → ℕ, ∑ s ∈ insert j S, F (W' s) = F ((y, false) :: v) + (F
    ((y, true) :: u) + ∑ s ∈ S.erase i, F (W s)) :=
    fun F => sum_update_two hiS hjS _ _
  have hrest : ∀ F : List Letter → ℕ, ∑ s ∈ S, F (W s) = F (W i) + ∑ s ∈ S.erase i, F (W s) :=
    fun F => (Finset.add_sum_erase S _ hiS).symm
  have hcy : ∀ s, cnt (W s) y = 0 := fun s => cnt_fresh hy
  have hcount : ∀ c, c ≠ y → ∑ s ∈ insert j S, cnt (W' s) c = ∑ s ∈ S, cnt (W s) c := by
    intro c hc
    rw [hsumF (fun w => cnt w c), hrest (fun w => cnt w c), hw, cnt_append, cnt_cons, cnt_cons]
    simp only [Ne.symm hc, ite_false]
    omega
  have hcounty : ∑ s ∈ insert j S, cnt (W' s) y = 2 := by
    rw [hsumF (fun w => cnt w y), cnt_cons, cnt_cons]
    have h1 : cnt v y = 0 := by
      have := hcy i
      rw [hw, cnt_append] at this
      omega
    have h2 : cnt u y = 0 := by
      have := hcy i
      rw [hw, cnt_append] at this
      omega
    have h3 : ∑ s ∈ S.erase i, cnt (W s) y = 0 := Finset.sum_eq_zero fun s _ => hcy s
    simp [h1, h2, h3]
  have hsum' : ∀ c, ∑ s ∈ insert j S, cnt (W' s) c ≤ 2 := fun c => by
    by_cases hc : c = y
    · subst hc
      exact hcounty.le
    · rw [hcount c hc]
      exact hsum c
  have hS' : ∀ s, s ∉ insert j S → W' s = [] := fun s hs => by
    have h1 : s ≠ j := fun h => hs (Finset.mem_insert.mpr (.inl h))
    have h2 : s ∉ S := fun h => hs (Finset.mem_insert_of_mem h)
    have h3 : s ≠ i := fun h => h2 (h ▸ hiS)
    rw [hW', update_of_ne h1, update_of_ne h3]
    exact hS s h2
  have hP' : IsPaired W' := isPaired_of_sum hS' hsum'
  obtain ⟨f', hf', hon'⟩ := hon.cut hf hw hij hWj hu hv hy hP'
  have hbcy : ∀ (e : Bool) (x : List Letter), bc Bad ((y, e) :: x) = bc Bad x := fun e x => by
    rw [bc_cons]
    simp [hyB]
  have hm' : ∑ s ∈ insert j S, (bc Bad (W' s) - 1) < m := by
    rw [hsumF (fun w => bc Bad w - 1), ← hm, hrest (fun w => bc Bad w - 1), hbcy, hbcy, hw,
      bc_append]
    omega
  obtain ⟨S₂, W₂, f₂, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ih _ hm' (insert j S) W' f' rfl
    ((hW.update _ _).update _ _) (by
      rw [hW', update_of_ne hj0.symm]
      by_cases hi0 : i = 0
      · subst hi0
        simp
      · rwa [update_of_ne (Ne.symm hi0)])
    hf' hon' (fun s hs => by
      by_cases hs1 : s = j
      · subst hs1
        rw [hW', update_self]
        have : v.length ≠ 0 := by simpa using hv
        simp only [List.length_cons]
        omega
      · by_cases hs2 : s = i
        · subst hs2
          rw [hW', update_of_ne hs1, update_self]
          have : u.length ≠ 0 := by simpa using hu
          simp only [List.length_cons]
          omega
        · rw [hW', update_of_ne hs1, update_of_ne hs2] at hs ⊢
          exact hlen s hs) hS' hsum'
  refine ⟨S₂, W₂, f₂, h1, h2, h3, h4, h5, h6, h7, h8, fun c hc => ?_⟩
  rw [h9 c hc]
  exact hcount c fun he => hyB (he ▸ hc)

/-- Paste along each letter with a label in `Bad`. Each polygon has at most one such letter, so its
two sides are in two
polygons. These are the discs of the sketch around the edges of the graph. -/
theorem exists_diamonds (m : ℕ) : ∀ (S : Finset ℕ) (W : ℕ → List Letter) (f : ℕ × ℂ → T),
    ∑ i ∈ S, bc Bad (W i) = m → FinW W → W 0 ≠ [] → Presents W f → OffSides Bad B W f →
      (∀ i, W i ≠ [] → 2 ≤ (W i).length) →
    (∀ i, i ∉ S → W i = []) → (∀ c, ∑ i ∈ S, cnt (W i) c ≤ 2) → (∀ i, bc Bad (W i) ≤ 1) →
      (∀ c ∈ Bad, ∑ i ∈ S, cnt (W i) c ≠ 1) →
    ∃ (S' : Finset ℕ) (W' : ℕ → List Letter) (f' : ℕ × ℂ → T),
      FinW W' ∧ W' 0 ≠ [] ∧ Presents W' f' ∧ OffSides ∅ B W' f' ∧ (∀ i, W' i ≠ [] → 2 ≤
        (W' i).length) ∧ (∀ i, i ∉ S' → W' i = []) ∧
      ∀ c, ∑ i ∈ S', cnt (W' i) c ≤ 2 := by
  classical
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro S W f hm hW h0 hf hok hlen hS hsum hone hodd
  by_cases hall : ∀ i, bc Bad (W i) = 0
  · refine ⟨S, W, f, hW, h0, hf, fun i p k ε h1 _ => hok i p k ε h1 fun hk => ?_, hlen, hS, hsum⟩
    have := bc_pos (Bad := Bad) (l := (k, ε)) (List.mem_of_getElem? h1) hk
    have h2 := hall i
    omega
  push Not at hall
  obtain ⟨i₀, hi₀⟩ := hall
  obtain ⟨l, hl, hlB⟩ : ∃ l ∈ W i₀, l.1 ∈ Bad := by
    obtain ⟨l, hl, hd⟩ := List.countP_pos_iff.mp (Nat.pos_of_ne_zero hi₀)
    exact ⟨l, hl, by simpa using hd⟩
  obtain ⟨k, e⟩ := l
  have hkB : k ∈ Bad := hlB
  have hi₀S : i₀ ∈ S := by
    by_contra h
    simp [hS i₀ h] at hl
  have hci : cnt (W i₀) k = 1 := by
    have h1 := cnt_le_bc (Bad := Bad) (w := W i₀) hkB
    have h2 := hone i₀
    have h3 : 0 < cnt (W i₀) k := cnt_pos (w := W i₀) (l := (k, e)) hl
    omega
  have hsplit : cnt (W i₀) k + ∑ i ∈ S.erase i₀, cnt (W i) k = ∑ i ∈ S, cnt (W i) k
    := Finset.add_sum_erase S (fun i => cnt (W i) k) hi₀S
  obtain ⟨j₀, hj₀, hcj⟩ : ∃ j ∈ S.erase i₀, 0 < cnt (W j) k := by
    by_contra hcon
    push Not at hcon
    have h1 : ∑ i ∈ S.erase i₀, cnt (W i) k = 0 := Finset.sum_eq_zero fun i hi => by
      have := hcon i hi
      omega
    exact hodd k hkB (by omega)
  have hij₀ : j₀ ≠ i₀ := (Finset.mem_erase.mp hj₀).1
  have hj₀S : j₀ ∈ S := (Finset.mem_erase.mp hj₀).2
  have key : ∀ i j, i ∈ S → j ∈ S → j ≠ i → j ≠ 0 → 0 < cnt (W i) k → 0 < cnt (W j) k → ∃
    (S' : Finset ℕ) (W' : ℕ → List Letter) (f' : ℕ × ℂ → T),
      FinW W' ∧ W' 0 ≠ [] ∧ Presents W' f' ∧ OffSides ∅ B W' f' ∧ (∀ i, W' i ≠ [] → 2 ≤
        (W' i).length) ∧ (∀ i, i ∉ S' → W' i = []) ∧
      ∀ c, ∑ i ∈ S', cnt (W' i) c ≤ 2 := by
    intro i j hiS hjS hij hj0 hci' hcj'
    obtain ⟨l₁, h1, h1'⟩ := List.countP_pos_iff.mp hci'
    obtain ⟨l₂, h2, h2'⟩ := List.countP_pos_iff.mp hcj'
    obtain ⟨k₁, e₁⟩ := l₁
    obtain ⟨k₂, e₂⟩ := l₂
    obtain rfl : k₁ = k := by simpa using h1'
    obtain rfl : k₂ = k₁ := by simpa using h2'
    have hspl : ∀ c, cnt (W j) c + (cnt (W i) c + ∑ s ∈ (S.erase j).erase i, cnt (W s) c)
      = ∑ s ∈ S, cnt (W s) c := fun c => by
      have h3 : cnt (W j) c + ∑ s ∈ S.erase j, cnt (W s) c = ∑ s ∈ S, cnt (W s) c
        := Finset.add_sum_erase S (fun s => cnt (W s) c) hjS
      have h4 : cnt (W i) c + ∑ s ∈ (S.erase j).erase i, cnt (W s) c = ∑ s ∈ S.erase j, cnt (W s) c
        :=
        Finset.add_sum_erase (S.erase j) (fun s => cnt (W s) c) (Finset.mem_erase.mpr ⟨hij.symm,
          hiS⟩)
      omega
    have hk2 := hspl k₂
    have hk3 := hsum k₂
    have hrest : ∀ s, s ≠ i → s ≠ j → cnt (W s) k₂ = 0 := by
      intro s hs1 hs2
      by_cases hsS : s ∈ S
      · have h5 : s ∈ (S.erase j).erase i := Finset.mem_erase.mpr ⟨hs1, Finset.mem_erase.mpr ⟨hs2,
          hsS⟩⟩
        have h6 : cnt (W s) k₂ ≤ ∑ s ∈ (S.erase j).erase i, cnt (W s) k₂ :=
          Finset.single_le_sum (f := fun s => cnt (W s) k₂) (fun _ _ => Nat.zero_le _) h5
        omega
      · rw [hS s hsS]
        rfl
    have hc1 : cnt (W i) k₂ = 1 := by omega
    have hc2 : cnt (W j) k₂ = 1 := by omega
    have hne1 : W i ≠ [] := fun h => by simp [h] at h1
    have hne2 : W j ≠ [] := fun h => by simp [h] at h2
    obtain ⟨w, f', h3, h4, h5, h6, h7⟩ := exists_net_merge hW hf hok hij h1 h2 hc1 hc2 hrest
      (hlen i hne1) (hlen j hne2)
    have hoth0 : ∀ c ∈ Bad, c ≠ k₂ → cnt (W i) c = 0 ∧ cnt (W j) c = 0 := fun c hc hne => by
      have h8 := cnt_add_cnt_le_bc (w := W i) hc hkB hne
      have h9 := cnt_add_cnt_le_bc (w := W j) hc hkB hne
      have h10 := hone i
      have h11 := hone j
      omega
    have hbw : bc Bad w = 0 := by
      by_contra hne
      obtain ⟨l, hl1, hl2⟩ := List.countP_pos_iff.mp (Nat.pos_of_ne_zero hne)
      have hlB : l.1 ∈ Bad := by simpa using hl2
      have h12 : 0 < cnt w l.1 := cnt_pos hl1
      by_cases hle : l.1 = k₂
      · rw [hle, h6] at h12
        exact lt_irrefl _ h12
      · have h13 := hoth0 l.1 hlB hle
        have h14 := h7 l.1
        omega
    have hne0 : w ≠ [] := fun he => by simp [he] at h5
    set W' := update (update W j []) i w with hW'
    have hval : ∀ F : List Letter → ℕ, ∑ s ∈ S.erase j, F (W' s) = F w + ∑ s ∈
      (S.erase j).erase i, F (W s) := by
      intro F
      rw [← Finset.add_sum_erase (S.erase j) _ (Finset.mem_erase.mpr ⟨hij.symm, hiS⟩), hW',
        update_self]
      congr 1
      refine Finset.sum_congr rfl fun s hs => ?_
      have hs1 := (Finset.mem_erase.mp hs).1
      have hs2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hs).2).1
      rw [update_of_ne hs1, update_of_ne hs2]
    have hm' : ∑ s ∈ S.erase j, bc Bad (W' s) < m := by
      rw [hval (bc Bad), hbw, zero_add, ← hm, ← Finset.add_sum_erase S _ hjS,
        ← Finset.add_sum_erase (S.erase j) _ (Finset.mem_erase.mpr ⟨hij.symm, hiS⟩)]
      have h15 : 0 < bc Bad (W j) := lt_of_lt_of_le hcj' (cnt_le_bc hkB)
      omega
    refine ih _ hm' (S.erase j) W' f' rfl ((hW.update _ _).update _ _) ?_ h3 h4 ?_ ?_ ?_ ?_ ?_
    · rw [hW']
      by_cases hi0 : i = 0
      · subst hi0
        simpa using hne0
      · rw [update_of_ne (Ne.symm hi0), update_of_ne hj0.symm]
        exact h0
    · intro s hs
      by_cases hs1 : s = i
      · subst hs1
        rw [hW', update_self]
        exact h5
      · rw [hW', update_of_ne hs1] at hs ⊢
        by_cases hs2 : s = j
        · subst hs2
          simp at hs
        · rw [update_of_ne hs2] at hs ⊢
          exact hlen s hs
    · intro s hs
      have hs1 : s ≠ i := fun h => hs (Finset.mem_erase.mpr ⟨h ▸ hij.symm, h ▸ hiS⟩)
      rw [hW', update_of_ne hs1]
      by_cases hs2 : s = j
      · subst hs2
        simp
      · rw [update_of_ne hs2]
        exact hS s fun h => hs (Finset.mem_erase.mpr ⟨hs2, h⟩)
    · intro c
      rw [hval (fun w => cnt w c)]
      have h16 := h7 c
      have h17 := hspl c
      have h18 := hsum c
      omega
    · intro s
      by_cases hs1 : s = i
      · subst hs1
        rw [hW', update_self, hbw]
        omega
      · rw [hW', update_of_ne hs1]
        by_cases hs2 : s = j
        · subst hs2
          simp [bc_nil]
        · rw [update_of_ne hs2]
          exact hone s
    · intro c hc
      rw [hval (fun w => cnt w c)]
      by_cases hck : c = k₂
      · subst hck
        have h19 : ∑ s ∈ (S.erase j).erase i, cnt (W s) c = 0 := Finset.sum_eq_zero fun s hs =>
          hrest s (Finset.mem_erase.mp hs).1 (Finset.mem_erase.mp (Finset.mem_erase.mp hs).2).1
        rw [h6, h19]
        norm_num
      · have h20 := hoth0 c hc hck
        have h21 := h7 c
        have h22 := hspl c
        have h23 := hodd c hc
        omega
  by_cases hj0 : j₀ = 0
  · exact key j₀ i₀ hj₀S hi₀S hij₀.symm (fun h => hij₀ (hj0.trans h.symm)) hcj (by omega)
  · exact key i₀ j₀ hi₀S hj₀S hij₀ hj0 (by omega) hcj

/-- **Pasting.** Let a family of polygons present a connected space, so that every point over `B` is
on an open side with a label
in `Bad`, and each label in `Bad` is on two sides or none. Then the family can be pasted into one
polygon whose boundary avoids `B`. -/
theorem exists_off_word {X : Type u} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] {Bad : Set
  ℕ} {B : Set X} (hBad : Bad.Finite)
    (S : Finset ℕ) {W : ℕ → List Letter} {f : ℕ × ℂ → X} (hW : FinW W) (h0 : W 0 ≠ [])
      (hf : Presents W f) (hon : OnBad Bad B W f)
    (hlen : ∀ i, W i ≠ [] → 2 ≤ (W i).length) (hS : ∀ i, i ∉ S → W i = [])
      (hsum : ∀ c, ∑ i ∈ S, cnt (W i) c ≤ 2)
    (hodd : ∀ c ∈ Bad, ∑ i ∈ S, cnt (W i) c ≠ 1) :
    ∃ (w : List Letter) (g : ℕ × ℂ → X), 2 ≤ w.length ∧ Good w ∧ Presents (sW w) g ∧ ∀ z ∈ sphere
      (0 : ℂ) 1, g (0, z) ∉ B := by
  obtain ⟨S₁, W₁, f₁, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := exists_sectors hBad _ S W f rfl hW h0
    hf hon hlen hS hsum
  obtain ⟨S₂, W₂, f₂, h10, h11, h12, h13, h14, h15, h16⟩ := exists_diamonds _ S₁ W₁ f₁ rfl h1 h2 h3
    h4.offSides h5 h6 h7 h8
    (fun c hc => by rw [h9 c hc]; exact hodd c hc)
  obtain ⟨w, g, h17, h18, h19, h20⟩ := exists_one_word_off _ S₂ W₂ f₂ rfl h10 h11 h12 h13 h14 h15
    h16
  refine ⟨w, g, h17, h18, h19, fun z hz => ?_⟩
  have hn0 : 0 < w.length := by omega
  obtain ⟨p, hp, t, ht, rfl⟩ := exists_side_of_sphere hn0 (fun q => (w[q]?.getD (0, true)).2) (z
    := z) (by simpa using hz)
  have hget : w[p]? = some (w[p]'hp) := by simp [hp]
  have hsgn : (w[p]?.getD (0, true)).2 = (w[p]'hp).2 := by rw [hget]; rfl
  have h21 := h20 0 p (w[p]'hp).1 (w[p]'hp).2 (by rw [sW_zero]; exact hget) (notMem_empty _) t ht
  rwa [sW_zero, ← hsgn] at h21

end GraphMinor.GM07
