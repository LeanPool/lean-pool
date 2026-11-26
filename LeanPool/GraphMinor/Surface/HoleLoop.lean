/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.ModelCriterion
public import LeanPool.GraphMinor.Surface.CircleMove
public import LeanPool.GraphMinor.Surface.WordTrack

/-!
# Holes of the normal word

Each cuff of a model surface is a loop that a free side of the normal word `ew a b c` goes around
once (`hole_loop`). The
moves of `WordTrack.lean` bring any hole, or any two holes, to the front of the word and keep this
side
(`exists_one_hole`, `exists_two_holes`). The rest of the word is `rW a b c L`, for the list `L` of
the holes left.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Function Metric

universe uu

/-- The holes with indices in `L`. -/
def hlW (k : ℕ) (L : List ℕ) : List Letter := L.flatMap fun m => holB (k + 2 * m, true)
  (k + 2 * m + 1, true)

theorem hlW_nil (k : ℕ) : hlW k [] = [] := rfl

theorem hlW_cons (k m : ℕ) (L : List ℕ) : hlW k (m :: L) = holB (k + 2 * m, true)
  (k + 2 * m + 1, true) ++ hlW k L := by
  simp [hlW]

theorem hlW_append (k : ℕ) (L L' : List ℕ) : hlW k (L ++ L') = hlW k L ++ hlW k L' := by
  simp [hlW]

theorem hlW_labels {k : ℕ} {L : List ℕ} : ∀ l ∈ hlW k L, ∃ m ∈ L, l.1 = k + 2 * m ∨ l.1
  = k + 2 * m + 1 := by
  induction L with
  | nil => simp [hlW_nil]
  | cons m L ih =>
    intro l hl
    rw [hlW_cons] at hl
    rcases List.mem_append.mp hl with hl | hl
    · refine ⟨m, by simp, ?_⟩
      simp only [holB, linv, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl <;> simp
    · obtain ⟨m', h1, h2⟩ := ih l hl
      exact ⟨m', List.mem_cons_of_mem _ h1, h2⟩

theorem noLab_hlW {k c : ℕ} {L : List ℕ} (h : ∀ m ∈ L, c ≠ k + 2 * m ∧ c ≠ k + 2 * m + 1) : NoLab
  (hlW k L) c := by
  intro l hl he
  obtain ⟨m, h1, h2⟩ := hlW_labels l hl
  rcases h2 with h2 | h2
  · exact (h m h1).1 (he.symm.trans h2)
  · exact (h m h1).2 (he.symm.trans h2)

theorem tL_hlW (k : ℕ) {L : List ℕ} (hL : L.Nodup) : TL L.length (hlW k L) := by
  induction L with
  | nil => exact .nil
  | cons m L ih =>
    rw [hlW_cons]
    obtain ⟨h1, h2⟩ := List.nodup_cons.mp hL
    refine .cons _ _ (by simp) ?_ (ih h2)
    intro l hl
    refine noLab_hlW fun m' hm' => ?_
    have hne : m' ≠ m := fun he => h1 (he ▸ hm')
    simp only [holB, linv, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl <;> simp only <;> omega

theorem tW_eq (k c s : ℕ) : tW (k + 2 * s) c = hlW k (List.range' s c) := by
  induction c generalizing s with
  | zero => rfl
  | succ c ih =>
    rw [List.range'_succ, hlW_cons, ← ih]
    simp only [tW]
    congr 2

/-- The two more letters at the end of the normal word. -/
def eW (a b c : ℕ) : List Letter := [(2 * a + b + 2 * c, true), (2 * a + b + 2 * c, false)]

/-- The normal word without the holes outside `L`. -/
def rW (a b c : ℕ) (L : List ℕ) : List Letter := hW 0 a ++ cW (2 * a) b ++ hlW
  (2 * a + b) L ++ eW a b c

theorem ew_eq_rW (a b c : ℕ) : ew a b c = rW a b c (List.range' 0 c) := by
  have := tW_eq (2 * a + b) c 0
  simp only [mul_zero, add_zero] at this
  simp [ew, nfW, rW, eW, this]

/-- The tether of the hole `m`. -/
def tL (a b m : ℕ) : Letter := (2 * a + b + 2 * m, true)

/-- The free letter of the hole `m`. -/
def rL (a b m : ℕ) : Letter := (2 * a + b + 2 * m + 1, true)

/-- The hole `m`. -/
def hB (a b m : ℕ) : List Letter := holB (tL a b m) (rL a b m)

/-- A hole in `L` moves to the front of a word. -/
theorem trk_hole {a b c m : ℕ} {U : List Letter} {L : List ℕ} (hL : L.Nodup) (hm : m ∈ L)
  (hmc : ∀ m' ∈ L, m' < c)
    (hU : NoLab U (tL a b m).1) :
    Trk.{uu} {k | k ≠ (tL a b m).1} (sW (U ++ rW a b c L)) (sW (hB a b m ++ (U ++ rW a b c
      (L.erase m)))) := by
  obtain ⟨L₁, L₂, rfl⟩ := List.append_of_mem hm
  have hnd := (List.nodup_append.mp hL)
  have hm1 : m ∉ L₁ := fun h => hnd.2.2 m h m (by simp) rfl
  have hm2 : m ∉ L₂ := (List.nodup_cons.mp hnd.2.1).1
  have he : (L₁ ++ m :: L₂).erase m = L₁ ++ L₂ := by
    rw [List.erase_append_right _ hm1, List.erase_cons_head]
  rw [he]
  have hlab : ∀ {L' : List ℕ}, m ∉ L' → NoLab (hlW (2 * a + b) L') (tL a b m).1 := fun hm' =>
    noLab_hlW fun m' h => by
      have : m' ≠ m := fun e => hm' (e ▸ h)
      simp only [tL]
      omega
  have h1 := hmc m (by simp)
  have hH : NoLab (hW 0 a) (tL a b m).1 := fun l hl h => by
    have := (hW_labels 0 a l hl).2
    simp only [tL] at h
    omega
  have hC : NoLab (cW (2 * a) b) (tL a b m).1 := fun l hl h => by
    have := (cW_labels (2 * a) b l hl).2
    simp only [tL] at h
    omega
  have hE : NoLab (eW a b c) (tL a b m).1 := fun l hl h => by
    simp only [eW, List.mem_cons, List.not_mem_nil, or_false] at hl
    simp only [tL] at h
    rcases hl with rfl | rfl <;> simp only at h <;> omega
  have hP : NoLab (U ++ hW 0 a ++ cW (2 * a) b ++ hlW (2 * a + b) L₁) (tL a b m).1 :=
    noLab_append.mpr ⟨noLab_append.mpr ⟨noLab_append.mpr ⟨hU, hH⟩, hC⟩, hlab hm1⟩
  have hQ : NoLab (hlW (2 * a + b) L₂ ++ eW a b c) (tL a b m).1 := noLab_append.mpr ⟨hlab hm2, hE⟩
  have hs : NoLab [rL a b m] (tL a b m).1 := noLab_cons.mpr ⟨by simp [rL, tL], noLab_nil⟩
  have key := trk_hole_front.{uu} (tL a b m) hs hP hQ
  have e1 : U ++ rW a b c (L₁ ++ m :: L₂) =
      (U ++ hW 0 a ++ cW (2 * a) b ++ hlW (2 * a + b) L₁) ++ (tL a b m :: [rL a b m] ++ [linv
        (tL a b m)]) ++
        (hlW (2 * a + b) L₂ ++ eW a b c) := by
    simp [rW, hlW_append, hlW_cons, holB, tL, rL, add_assoc]
  have e2 : hB a b m ++ (U ++ rW a b c (L₁ ++ L₂)) =
      tL a b m :: [rL a b m] ++ linv (tL a b m) ::
        ((U ++ hW 0 a ++ cW (2 * a) b ++ hlW (2 * a + b) L₁) ++ (hlW (2 * a + b) L₂ ++ eW a b c))
          := by
    simp [rW, hB, holB, hlW_append]
  rw [e1, e2]
  exact key

section loop

variable {Y : Type uu} [TopologicalSpace Y] [T2Space Y] {a b c : ℕ} {f : ℕ × ℂ → Y}

/-- The free side of the hole `i`, with its parameter. -/
noncomputable def holeP (a b c : ℕ) (f : ℕ × ℂ → Y) (i : ℕ) (u : ℝ) : Y :=
  pmap f (per (4 * a + 2 * b + 3 * c + 2) ((4 * a + 2 * b + 3 * i + 1 : ℕ) + u))

omit [TopologicalSpace Y] [T2Space Y] in
theorem holeC_eq (a b c : ℕ) (f : ℕ × ℂ → Y) (i : ℕ) : holeC a b c f i = holeP a b c f i '' Icc 0 1
  := rfl

omit [T2Space Y] in
/-- The free side of a hole goes once around a cuff. -/
theorem hole_loop (hf : Presents (sW (ew a b c)) f) {i : ℕ} (hi : i < c) :
    ContinuousOn (holeP a b c f i) (Icc 0 1) ∧ InjOn (holeP a b c f i) (Ico 0 1)
      ∧ holeP a b c f i 0 = holeP a b c f i 1 := by
  classical
  have hn : 0 < 4 * a + 2 * b + 3 * c + 2 := by omega
  set n := 4 * a + 2 * b + 3 * c + 2 with hn'
  set p := 4 * a + 2 * b + 3 * i + 1 with hp
  have hDsk : ∀ z : ℂ, ‖z‖ = 1 → ((0 : ℕ), z) ∈ Dsk (sW (ew a b c)) := fun z hz =>
    ⟨(ew_mem_dsk a b c).1, by simp [hz]⟩
  have hget : ∀ δ < 3, (ew a b c)[4 * a + 2 * b + 3 * i + δ]? = some (2 * a + b + 2 * i + δ % 2,
    decide (δ < 2)) := by
    intro δ hδ
    rw [ew_get a b c (by omega), lab_t hi hδ, sgn_t hi hδ]
  have hs : ∀ (q : ℕ) (u : ℝ), ((spt (sW (ew a b c)) 0 q u).1, (spt (sW (ew a b c)) 0 q u).2) =
    (0, per n (q + u)) := by
    intro q u
    rw [spt_ew]
  refine ⟨continuousOn_hole hf i, ?_, ?_⟩
  · have hfree := freeSide_hole (a := a) (b := b) hi
    have hpa : IsPaired (sW (ew a b c)) := isPaired_ew a b c
    have hget1 : (sW (ew a b c) 0)[p]? = some (2 * a + b + 2 * i + 1, true) := by
      rw [sW_zero]
      simpa using hget 1 (by norm_num)
    have hkey : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ico (0 : ℝ) 1, holeP a b c f i x = holeP a b c f i y → x
      = y := by
      intro x hx y hy he
      have h1 := (hf.2.2 _ (hDsk _ (norm_per _ _)) _ (hDsk _ (norm_per _ _))).mp he
      have hx' : ((0 : ℕ), per n (p + x)) = spt (sW (ew a b c)) 0 p x := by rw [spt_ew]
      have hy' : ((0 : ℕ), per n (p + y)) = spt (sW (ew a b c)) 0 p y := by rw [spt_ew]
      rw [hx', hy'] at h1
      rcases PRel.eq_or_stp hpa hget1 hx h1 with h2 | h2
      · rw [← hx', ← hy'] at h2
        have h3 : per n (p + y) = per n (p + x) := (Prod.mk.inj h2).2
        have hb : ∀ z ∈ Ico (0 : ℝ) 1, (p : ℝ) + z ∈ Ico (0 : ℝ) n := fun z hz => by
          have hp1 : ((p + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : p + 1 ≤ n)
          push_cast at hp1
          have : (0 : ℝ) ≤ p := Nat.cast_nonneg _
          exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
        have := per_injOn hn (hb y hy) (hb x ⟨hx.1.le, hx.2⟩) h3
        linarith
      · obtain ⟨j, q, e', h3, h4, -⟩ := stp_of_side hpa hget1 hx h2
        exact absurd (hfree j q _ _ _ hget1 h3) h4
    intro x hx y hy he
    rcases eq_or_lt_of_le hx.1 with h0 | h0
    · rcases eq_or_lt_of_le hy.1 with h1 | h1
      · rw [← h0, ← h1]
      · exact (hkey y ⟨h1, hy.2⟩ x hx he.symm).symm
    · exact hkey x ⟨h0, hx.2⟩ y hy he
  · have h1 : Stp (sW (ew a b c)) (spt (sW (ew a b c)) 0 (4 * a + 2 * b + 3 * i + 0) 1)
        (spt (sW (ew a b c)) 0 (4 * a + 2 * b + 3 * i + 2) 0) := by
      refine stp_iff.mpr ⟨0, 0, 4 * a + 2 * b + 3 * i + 0, 4 * a + 2 * b + 3 * i + 2,
        2 * a + b + 2 * i, true, false, 1,
        ?_, ?_, ?_, by simp, rfl, ?_⟩
      · rw [sW_zero]
        simpa using hget 0 (by norm_num)
      · rw [sW_zero]
        simpa using hget 2 (by norm_num)
      · simp
      · simp [flp]
    have h2 := (hf.2.2 _ (h1.mem_Dsk).1 _ (h1.mem_Dsk).2).mpr (.rel _ _ h1)
    rw [spt_ew, spt_ew] at h2
    unfold holeP pmap
    have e1 : ((4 * a + 2 * b + 3 * i + 1 : ℕ) : ℝ) + 0 = ((4 * a + 2 * b + 3 * i + 0 : ℕ) : ℝ) + 1
      := by
      push_cast
      ring
    have e2 : ((4 * a + 2 * b + 3 * i + 1 : ℕ) : ℝ) + 1 = ((4 * a + 2 * b + 3 * i + 2 : ℕ) : ℝ) + 0
      := by
      push_cast
      ring
    rw [e1, e2]
    exact h2

omit [T2Space Y] in
theorem sideVal_hole (_hf : Presents (sW (ew a b c)) f) {i : ℕ} (hi : i < c) :
    SideVal (sW (rW a b c (List.range' 0 c))) f (rL a b i).1 (holeP a b c f i) := by
  rw [← ew_eq_rW]
  refine ⟨0, 4 * a + 2 * b + 3 * i + 1, ?_, fun u _ => ?_⟩
  · rw [sW_zero, ew_get a b c (by omega), lab_t (δ := 1) hi (by norm_num),
      sgn_t (δ := 1) hi (by norm_num)]
    simp [rL]
  · rw [sW_zero, ew_length, sdPt_true]
    rfl

end loop

/-- The list of the holes left after taking out `m`. -/
theorem nodup_range_erase (c m : ℕ) : ((List.range' 0 c).erase m).Nodup :=
  (List.nodup_range').erase _

/-- A cuff of a model surface is a loop on a free side of a word with this hole in front. -/
theorem exists_one_hole {Y : Type uu} [TopologicalSpace Y] [T2Space Y] {a b c : ℕ}
  (e : Y ≃ₜ SurfaceModel a b c) {C : Set Y}
    (hC : C ∈ cuffs Y) : ∃ i < c, ∃ (φ : Circle ≃ₜ C) (g : ℕ × ℂ → Y),
      Presents (sW (hB a b i ++ rW a b c ((List.range' 0 c).erase i))) g ∧
      SideVal (sW (hB a b i ++ rW a b c ((List.range' 0 c).erase i))) g (rL a b i).1 fun u => (φ
        (ee u)).1 := by
  obtain ⟨-, f₀, hf₀⟩ := presents_ew a b c
  have hf : Presents (sW (ew a b c)) (e.symm ∘ f₀) := presents_comp hf₀ e.symm
  rw [cuffs_eq_holeC hf] at hC
  obtain ⟨i, hi, rfl⟩ := hC
  have hi' : i < c := hi
  obtain ⟨h1, h2, h3⟩ := hole_loop hf hi'
  obtain ⟨φ, hφ⟩ := exists_circle_param h1 h2 h3
  have hL : (List.range' 0 c).Nodup := List.nodup_range'
  have hm : i ∈ List.range' 0 c := by simpa using hi'
  have hmc : ∀ m' ∈ List.range' 0 c, m' < c := fun m' h => by simpa using h
  have ht := trk_hole.{uu} (a := a) (b := b) (c := c) (U := []) hL hm hmc noLab_nil
  have hs := sideVal_hole hf hi'
  simp only [List.nil_append] at ht
  rw [ew_eq_rW] at hf
  obtain ⟨g, h4, h5⟩ := ht.sideVal hf
  refine ⟨i, hi', φ, g, h4, ?_⟩
  obtain ⟨i₁, p, h6, h7⟩ := h5 _ (by simp [rL, tL]) _ hs
  exact ⟨i₁, p, h6, fun u hu => (h7 u hu).trans (hφ u hu).symm⟩

/-- Two cuffs of a model surface are loops on free sides of a word with these holes in front. -/
theorem exists_two_holes {Y : Type uu} [TopologicalSpace Y] [T2Space Y] {a b c : ℕ}
  (e : Y ≃ₜ SurfaceModel a b c) {C C' : Set Y}
    (hC : C ∈ cuffs Y) (hC' : C' ∈ cuffs Y) (hne : C ≠ C') : ∃ i < c, ∃ j < c, i ≠ j ∧ ∃
      (φ : Circle ≃ₜ C) (φ' : Circle ≃ₜ C') (g : ℕ × ℂ → Y),
      Presents (sW (hB a b j ++ (hB a b i ++ rW a b c (((List.range' 0 c).erase i).erase j)))) g ∧
      SideVal (sW (hB a b j ++ (hB a b i ++ rW a b c (((List.range' 0 c).erase i).erase j)))) g
        (rL a b i).1 (fun u => (φ (ee u)).1) ∧
      SideVal (sW (hB a b j ++ (hB a b i ++ rW a b c (((List.range' 0 c).erase i).erase j)))) g
        (rL a b j).1 (fun u => (φ' (ee u)).1) := by
  obtain ⟨-, f₀, hf₀⟩ := presents_ew a b c
  have hf : Presents (sW (ew a b c)) (e.symm ∘ f₀) := presents_comp hf₀ e.symm
  rw [cuffs_eq_holeC hf] at hC hC'
  obtain ⟨i, hi, rfl⟩ := hC
  obtain ⟨j, hj, rfl⟩ := hC'
  have hi' : i < c := hi
  have hj' : j < c := hj
  have hij : i ≠ j := fun h => hne (by rw [h])
  obtain ⟨h1, h2, h3⟩ := hole_loop hf hi'
  obtain ⟨φ, hφ⟩ := exists_circle_param h1 h2 h3
  obtain ⟨h1', h2', h3'⟩ := hole_loop hf hj'
  obtain ⟨φ', hφ'⟩ := exists_circle_param h1' h2' h3'
  have hL : (List.range' 0 c).Nodup := List.nodup_range'
  have hm : i ∈ List.range' 0 c := by simpa using hi'
  have hmc : ∀ m' ∈ List.range' 0 c, m' < c := fun m' h => by simpa using h
  have ht := trk_hole.{uu} (a := a) (b := b) (c := c) (U := []) hL hm hmc noLab_nil
  have hs := sideVal_hole hf hi'
  have hs' := sideVal_hole hf hj'
  simp only [List.nil_append] at ht
  rw [ew_eq_rW] at hf
  obtain ⟨g₁, h4, h5⟩ := ht.sideVal hf
  have ht2 := trk_hole.{uu} (a := a) (b := b) (c := c) (U := hB a b i) (L :=
    (List.range' 0 c).erase i) (m := j)
    (nodup_range_erase c i) ((List.mem_erase_of_ne (Ne.symm hij)).mpr (by simpa using hj'))
    (fun m' h => hmc m' (List.mem_of_mem_erase h)) (by
      refine fun l hl he => ?_
      simp only [hB, holB, tL, rL, linv, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl <;> simp only [tL] at he <;> omega)
  obtain ⟨g, h6, h7⟩ := ht2.sideVal h4
  refine ⟨i, hi', j, hj', hij, φ, φ', g, h6, ?_, ?_⟩
  · obtain ⟨i₁, p, h8, h9⟩ := h7 _ (by
      simp only [rL, tL, mem_ofPred_eq]
      omega) _ (h5 _ (by simp [rL, tL]) _ hs)
    exact ⟨i₁, p, h8, fun u hu => (h9 u hu).trans (hφ u hu).symm⟩
  · have hkey := h5 _ (by
      simp only [rL, tL, mem_ofPred_eq]
      omega) _ hs'
    obtain ⟨i₁, p, h8, h9⟩ := h7 _ (by simp [rL, tL]) _ hkey
    exact ⟨i₁, p, h8, fun u hu => (h9 u hu).trans (hφ' u hu).symm⟩

end GraphMinor.Surface
