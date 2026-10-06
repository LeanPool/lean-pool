/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Certificates.CheckerSound
public import LeanPool.ConwaySoifer.Geometry.Canonical
import Mathlib.Tactic

/-!
# The initial model follows from the canonical case hypotheses

`initModel_holds`: if `Canonical c T r s` (and, when `hi ≤ 1/14`, `SmallStrengthening`), then
the model rebuilt by `initModel` for the interval `(lo, hi] ∋ s` holds for `T` at `x = s - lo`.
Together with `CertData.check_sound` this turns every checked certificate into the exclusion of
its parameter interval in its contact case.
-/

/-
Adapted from https://github.com/AnanasClassic/conway-soifer-n3-lean
at b71b1d22b6f7ebb0f0173fc70a66075f44c86ce6 (public release: 11 September 2026).
The original MIT grant is retained below; the Lean Pool adaptation is released under Apache 2.0.

MIT License

Copyright (c) 2026 Vladislav Kuznetsov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

@[expose] public section

namespace ConwaySoifer.Certificates
open IPoly

noncomputable section

/-! ## Evaluation of the constructed points -/

theorem evalR_trimP (p : IPoly) (x : ℝ) : evalR (trimP p) x = evalR p x := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    rcases hq : trimP p with _ | ⟨y, ys⟩
    · rw [hq] at ih
      have hp : evalR p x = 0 := by
        rw [← ih]; rfl
      simp only [trimP, hq]
      split_ifs with hc
      · subst hc; simp [evalR, hp]
      · simp [evalR, hp]
    · rw [hq] at ih
      simp only [trimP, hq, evalR_cons, ih]

theorem evalR_trimKeep (p : IPoly) (x : ℝ) : evalR (trimKeep p) x = evalR p x := by
  have h := evalR_trimP p x
  unfold trimKeep
  rcases hq : trimP p with _ | ⟨y, ys⟩
  · rw [hq] at h
    simp only [evalR, Int.cast_zero, mul_zero, add_zero] at h ⊢
    exact h
  · rw [hq] at h
    simpa [hq] using h

theorem Rat.cast_num_of_den_eq_one {q : Rat} (h : q.den = 1) : ((q.num : Int) : ℝ) = (q : ℝ) := by
  have := Rat.coe_int_num_of_den_eq_one h
  rw [← this]; push_cast; rfl

/-- The real point represented by `mkPt`. -/
theorem realPt_mkPt {denI : Int} {lo a b c d : Rat} {P : IPoint} (h : mkPt denI lo a b c d = some P)
    (hden : 0 < denI) (x : ℝ) :
    realPt (denI : ℝ) P x = ((a : ℝ) + c * (lo + x), (b : ℝ) + d * (lo + x)) := by
  unfold mkPt at h
  dsimp only at h
  split_ifs at h with hint
  · obtain ⟨h0, h1, h2, h3⟩ := hint
    simp only [Option.some.injEq] at h
    subst h
    have hdenR : (0 : ℝ) < denI := by
      exact_mod_cast hden
    apply Prod.ext
    · simp only [realPt, evalF, Prod.smul_fst, smul_eq_mul, evalR_trimKeep, evalR_cons, evalR_nil,
        mul_zero, add_zero]
      rw [Rat.cast_num_of_den_eq_one h0, Rat.cast_num_of_den_eq_one h2]
      push_cast
      field_simp; ring
    · simp only [realPt, evalF, Prod.smul_snd, smul_eq_mul, evalR_trimKeep, evalR_cons, evalR_nil,
        mul_zero, add_zero]
      rw [Rat.cast_num_of_den_eq_one h1, Rat.cast_num_of_den_eq_one h3]
      push_cast
      field_simp; ring

theorem evalF_mkPt_const {denI : Int} {lo a b : Rat} {P : IPoint}
    (h : mkPt denI lo a b 0 0 = some P) (x : ℝ) :
    evalF P x = (denI : ℝ) • ((a : ℝ), (b : ℝ)) := by
  unfold mkPt at h
  dsimp only at h
  split_ifs at h with hint
  · obtain ⟨h0, h1, h2, h3⟩ := hint
    simp only [Option.some.injEq] at h
    subst h
    simp only [mul_zero, add_zero, zero_mul] at h0 h1 h2 h3
    apply Prod.ext
    · simp only [evalF, Prod.smul_fst, smul_eq_mul, evalR_trimKeep, evalR_cons, evalR_nil, mul_zero,
        add_zero, zero_mul]
      rw [Rat.cast_num_of_den_eq_one h0, Rat.cast_num_of_den_eq_one h2]
      push_cast
      ring
    · simp only [evalF, Prod.smul_snd, smul_eq_mul, evalR_trimKeep, evalR_cons, evalR_nil, mul_zero,
        add_zero, zero_mul]
      rw [Rat.cast_num_of_den_eq_one h1, Rat.cast_num_of_den_eq_one h3]
      push_cast
      ring

/-! ## Rational data versus real data -/

theorem vQ_cast (i : Fin 6) : (((vQ i).1 : ℝ), ((vQ i).2 : ℝ)) = vertex i := by
  fin_cases i <;> simp [vQ, vertex]

theorem wQ_cast (j : Fin 3) : (((wQ j).1 : ℝ), ((wQ j).2 : ℝ)) = corner j := by
  fin_cases j <;> simp [wQ, corner]

theorem kQ_cast (j : Fin 6) : (((kQ j).1 : ℝ), ((kQ j).2 : ℝ)) = coreDir j := by
  fin_cases j <;> simp [kQ, coreDir]

theorem recvIdx_eq (c : Case) : ∀ cc : ContactCase,
    (c = .Sext ↔ cc = .Sext) → (c = .Sint ↔ cc = .Sint) → (c = .Aown ↔ cc = .Aown) →
    (c = .Across ↔ cc = .Across) → (recvIdx c = neighbor 0 cc.right) := by
  intro cc h1 h2 h3 h4
  cases c <;> cases cc <;> simp_all [recvIdx, neighbor, ContactCase.right]

/-- The correspondence between the checker's `Case` and the geometric `ContactCase`. -/
def Case.toContact : Case → ContactCase
  | .Sext => .Sext
  | .Sint => .Sint
  | .Aown => .Aown
  | .Across => .Across

theorem recvIdx_toContact (c : Case) : recvIdx c = neighbor 0 c.toContact.right := by
  cases c <;> rfl

/-! ## Membership in the raw lists -/

theorem mem_filterMap_id {P : IPoint} {l : List (Option IPoint)} (h : P ∈ l.filterMap id) :
    some P ∈ l := by
  rw [List.mem_filterMap] at h
  obtain ⟨o, ho, hP⟩ := h
  simp only [id_eq] at hP
  rw [← hP]; exact ho

theorem mem_corePts {lo hi : Rat} {denI : Int} {P : IPoint} (h : some P ∈ corePts lo hi denI) :
    ∃ j : Fin 6, mkPt denI lo 0 0 ((1 - hi) * (kQ j).1 / 3) ((1 - hi) * (kQ j).2 / 3) = some P := by
  unfold corePts at h
  rw [List.mem_map] at h
  obtain ⟨j, -, hj⟩ := h
  exact ⟨j, hj⟩

theorem mem_sidePts {lo : Rat} {denI : Int} {i : Fin 6} {P : IPoint} (h : some P ∈ sidePts lo denI
    i) :
    mkPt denI lo (vQ i).1 (vQ i).2 0 0 = some P ∨
    mkPt denI lo (vQ i).1 (vQ i).2 ((vQ (i + 5)).1 - (vQ i).1) ((vQ (i + 5)).2 - (vQ i).2) = some P
        ∨
    mkPt denI lo (vQ i).1 (vQ i).2 ((vQ (i + 1)).1 - (vQ i).1) ((vQ (i + 1)).2 - (vQ i).2) = some P
        := by
  simp only [sidePts, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr h.symm)

theorem mem_cornerPts {lo : Rat} {denI : Int} {j : Fin 3} {P : IPoint}
    (h : some P ∈ cornerPts lo denI j) :
    mkPt denI lo (wQ j).1 (wQ j).2 0 0 = some P ∨
    mkPt denI lo (wQ j).1 (wQ j).2 ((vQ ⟨2 * j.val, by omega⟩).1 - (wQ j).1)
      ((vQ ⟨2 * j.val, by omega⟩).2 - (wQ j).2) = some P ∨
    mkPt denI lo (wQ j).1 (wQ j).2 ((vQ ⟨2 * j.val + 1, by omega⟩).1 - (wQ j).1)
      ((vQ ⟨2 * j.val + 1, by omega⟩).2 - (wQ j).2) = some P := by
  simp only [cornerPts, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr h.symm)

theorem mem_cornerMids {lo : Rat} {denI : Int} {j : Fin 3} {P : IPoint}
    (h : some P ∈ cornerMids lo denI j) :
    mkPt denI lo (((wQ j).1 + (vQ ⟨2 * j.val, by omega⟩).1) / 2)
      (((wQ j).2 + (vQ ⟨2 * j.val, by omega⟩).2) / 2) 0 0 = some P ∨
    mkPt denI lo (((wQ j).1 + (vQ ⟨2 * j.val + 1, by omega⟩).1) / 2)
      (((wQ j).2 + (vQ ⟨2 * j.val + 1, by omega⟩).2) / 2) 0 0 = some P := by
  simp only [cornerMids, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

theorem mem_rawB {c : Case} {lo hi : Rat} {denI : Int} {j : Fin 10} {P : IPoint}
    (h : some P ∈ rawB c lo hi denI j) :
    (j = 0 ∧ some P ∈ corePts lo hi denI) ∨
    (∃ i : Fin 6, j = sideIndex i ∧
      (some P ∈ sidePts lo denI i ∨
       (c.isS = true ∧ i = recvIdx c ∧ some P = endpointPt c lo denI) ∨
       (c = .Aown ∧ i = 0 ∧ some P = mid0Pt lo denI) ∨
       (c = .Across ∧ i = 1 ∧ some P = mid0Pt lo denI))) ∨
    (∃ k : Fin 3, j = cornerIndex k ∧
      (some P ∈ cornerPts lo denI k ∨
       (c.isS = false ∧ k = 0 ∧ some P = endpointPt c lo denI) ∨
       (c.isS = true ∧ smallHi hi = true ∧ k.val ≠ (recvIdx c).val / 2 ∧
         some P ∈ cornerMids lo denI k) ∨
       (c = .Aown ∧ smallHi hi = true ∧ k ≠ 0 ∧ some P ∈ cornerMids lo denI k))) := by
  unfold rawB at h
  split_ifs at h with hj0 hj6
  · left
    exact ⟨Fin.ext hj0, h⟩
  · right; left
    refine ⟨⟨j.val - 1, by omega⟩, Fin.ext (by simp [sideIndex]; omega), ?_⟩
    simp only [List.mem_append] at h
    rcases h with ((h | h) | h) | h
    · exact Or.inl h
    · right; left
      split_ifs at h with hc
      · simp only [List.mem_singleton] at h; exact ⟨hc.1, hc.2, h⟩
      · simp at h
    · right; right; left
      split_ifs at h with hc
      · simp only [List.mem_singleton] at h; exact ⟨hc.1, hc.2, h⟩
      · simp at h
    · right; right; right
      split_ifs at h with hc
      · simp only [List.mem_singleton] at h; exact ⟨hc.1, hc.2, h⟩
      · simp at h
  · right; right
    refine ⟨⟨j.val - 7, by omega⟩, Fin.ext (by simp [cornerIndex]; omega), ?_⟩
    simp only [List.mem_append] at h
    rcases h with ((h | h) | h) | h
    · exact Or.inl h
    · right; left
      split_ifs at h with hc
      · simp only [List.mem_singleton] at h
        refine ⟨?_, hc.2, h⟩
        simpa using hc.1
      · simp at h
    · right; right; left
      split_ifs at h with hc
      · exact ⟨hc.1, hc.2.1, hc.2.2, h⟩
      · simp at h
    · right; right; right
      split_ifs at h with hc
      · exact ⟨hc.1, hc.2.1, hc.2.2, h⟩
      · simp at h

/-! ## Geometric meaning of the constructed points -/

variable {T : Configuration} {r s : ℝ}

theorem mem_of_le_rayLen' (U : EquilateralTriangle) {v d : Point} (hv : v ∈ U.carrier)
    (hd : sqDist d (0, 0) = 1) {t : ℝ} (ht : 0 ≤ t) (hle : t ≤ rayLen U v d) :
    linePoint v d t ∈ U.carrier :=
  (linePoint_mem_iff_le_rayLen U hv hd ht).mpr hle

theorem linePoint_eq_add (v d : Point) (t : ℝ) : linePoint v d t = v + t • d := rfl

/-- The real point of a side list entry. -/
theorem sidePts_mem {c : ContactCase} (H : Canonical c T r s) {lo : Rat} {denI : Int}
    (hden : 0 < denI) {i : Fin 6} {P : IPoint} (h : some P ∈ sidePts lo denI i) :
    realPt (denI : ℝ) P (s - lo) ∈ (T (sideIndex i)).carrier := by
  have hv : vertex i ∈ (T (sideIndex i)).carrier := by
    have := H.anchored (sideIndex i); rwa [anchor_sideIndex] at this
  rcases mem_sidePts h with h | h | h
  · rw [realPt_mkPt h hden]
    simp only [Rat.cast_zero, zero_mul, add_zero]
    rw [vQ_cast]; exact hv
  · rw [realPt_mkPt h hden]
    have : (((vQ i).1 : ℝ) + ((vQ (i + 5)).1 - (vQ i).1 : Rat) * (lo + (s - lo)),
        ((vQ i).2 : ℝ) + ((vQ (i + 5)).2 - (vQ i).2 : Rat) * (lo + (s - lo))) =
        linePoint (vertex i) (sideDirection i false) s := by
      rw [linePoint_eq_add, sideDirection, neighbor, ← vQ_cast, ← vQ_cast]
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply Prod.ext <;> simp <;> ring
    rw [this]
    exact mem_of_le_rayLen' _ hv (sideDirection_unit i false) H.s_pos.le (H.side_min i false)
  · rw [realPt_mkPt h hden]
    have : (((vQ i).1 : ℝ) + ((vQ (i + 1)).1 - (vQ i).1 : Rat) * (lo + (s - lo)),
        ((vQ i).2 : ℝ) + ((vQ (i + 1)).2 - (vQ i).2 : Rat) * (lo + (s - lo))) =
        linePoint (vertex i) (sideDirection i true) s := by
      rw [linePoint_eq_add, sideDirection, neighbor, ← vQ_cast, ← vQ_cast]
      simp only [↓reduceIte]
      apply Prod.ext <;> simp <;> ring
    rw [this]
    exact mem_of_le_rayLen' _ hv (sideDirection_unit i true) H.s_pos.le (H.side_min i true)

theorem cornerPts_mem {c : ContactCase} (H : Canonical c T r s) {lo : Rat} {denI : Int}
    (hden : 0 < denI) {k : Fin 3} {P : IPoint} (h : some P ∈ cornerPts lo denI k) :
    realPt (denI : ℝ) P (s - lo) ∈ (T (cornerIndex k)).carrier := by
  have hw : corner k ∈ (T (cornerIndex k)).carrier := by
    have := H.anchored (cornerIndex k); rwa [anchor_cornerIndex] at this
  rcases mem_cornerPts h with h | h | h
  · rw [realPt_mkPt h hden]
    simp only [Rat.cast_zero, zero_mul, add_zero]
    rw [wQ_cast]; exact hw
  · rw [realPt_mkPt h hden]
    have : (((wQ k).1 : ℝ) + ((vQ ⟨2 * k.val, by omega⟩).1 - (wQ k).1 : Rat) * (lo + (s - lo)),
        ((wQ k).2 : ℝ) + ((vQ ⟨2 * k.val, by omega⟩).2 - (wQ k).2 : Rat) * (lo + (s - lo))) =
        linePoint (corner k) (cornerDirection k 0) s := by
      rw [linePoint_eq_add, cornerDirection, ← vQ_cast, ← wQ_cast]
      apply Prod.ext <;> simp <;> ring
    rw [this]
    exact mem_of_le_rayLen' _ hw (cornerDirection_unit k 0) H.s_pos.le (H.corner_min k 0)
  · rw [realPt_mkPt h hden]
    have : (((wQ k).1 : ℝ) + ((vQ ⟨2 * k.val + 1, by omega⟩).1 - (wQ k).1 : Rat) * (lo + (s - lo)),
        ((wQ k).2 : ℝ) + ((vQ ⟨2 * k.val + 1, by omega⟩).2 - (wQ k).2 : Rat) * (lo + (s - lo))) =
        linePoint (corner k) (cornerDirection k 1) s := by
      rw [linePoint_eq_add, cornerDirection, ← vQ_cast, ← wQ_cast]
      apply Prod.ext <;> simp <;> ring
    rw [this]
    exact mem_of_le_rayLen' _ hw (cornerDirection_unit k 1) H.s_pos.le (H.corner_min k 1)

theorem corePts_mem {c : ContactCase} (H : Canonical c T r s) {lo hi : Rat} {denI : Int}
    (hden : 0 < denI) (hhi : s ≤ hi) (hhi1 : (hi : ℝ) ≤ 1) {P : IPoint}
    (h : some P ∈ corePts lo hi denI) :
    realPt (denI : ℝ) P (s - lo) ∈ (T 0).carrier := by
  obtain ⟨j, hj⟩ := mem_corePts h
  rw [realPt_mkPt hj hden]
  have h0 : (0 : Point) ∈ (T 0).carrier := by
    change (0, 0) ∈ (T 0).carrier
    simpa [anchor] using H.anchored 0
  have hs1 : s < 1 := by
    linarith [H.s_lt]
  have hpos : 0 < 1 - s := by
    linarith
  have hlam : ((1 - hi : ℝ) / (1 - s)) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith) hpos.le
    · rw [div_le_one hpos]; linarith
  have hmem := (T 0).convex_carrier.smul_mem_of_zero_mem h0 (H.core j) hlam
  convert hmem using 1
  rw [coreVertex, smul_smul, ← kQ_cast]
  apply Prod.ext <;> simp <;> field_simp

theorem endpointPt_real {c : Case} {lo : Rat} {denI : Int} (hden : 0 < denI) {P : IPoint}
    (h : endpointPt c lo denI = some P) (s : ℝ) :
    realPt (denI : ℝ) P (s - lo) = minEndpoint c.toContact s := by
  rw [endpointPt] at h
  rw [realPt_mkPt h hden, minEndpoint, linePoint_eq_add, sideDirection, ← recvIdx_toContact,
    ← vQ_cast (recvIdx c)]
  have h0 : vertex 0 = (1, 0) := rfl
  rw [h0]
  apply Prod.ext <;> simp <;> ring

theorem mid0Pt_real {lo : Rat} {denI : Int} (hden : 0 < denI) {P : IPoint}
    (h : mid0Pt lo denI = some P) (x : ℝ) : realPt (denI : ℝ) P x = extMid0 := by
  rw [mid0Pt] at h
  rw [realPt_mkPt h hden]
  simp [extMid0]

theorem cornerMids_real {lo : Rat} {denI : Int} (hden : 0 < denI) {k : Fin 3} {P : IPoint}
    (h : some P ∈ cornerMids lo denI k) (x : ℝ) :
    realPt (denI : ℝ) P x = cornerMid k 0 ∨ realPt (denI : ℝ) P x = cornerMid k 1 := by
  rcases mem_cornerMids h with h | h
  · left
    rw [realPt_mkPt h hden, cornerMid, cornerDirection, ← vQ_cast, ← wQ_cast]
    apply Prod.ext <;> simp <;> ring
  · right
    rw [realPt_mkPt h hden, cornerMid, cornerDirection, ← vQ_cast, ← wQ_cast]
    apply Prod.ext <;> simp <;> ring

theorem exitDirPt_eval {c : Case} {lo : Rat} {denI : Int} {P : IPoint}
    (h : exitDirPt c lo denI = some P) (x : ℝ) :
    evalF P x = (denI : ℝ) • sideDirection 0 c.toContact.right := by
  rw [exitDirPt] at h
  rw [evalF_mkPt_const h, sideDirection, ← recvIdx_toContact, ← vQ_cast]
  apply Prod.ext <;> simp [vertex]

theorem backDirPt_eval {lo : Rat} {denI : Int} {P : IPoint} (h : backDirPt lo denI = some P)
    (x : ℝ) : evalF P x = (denI : ℝ) • sideDirection 1 false := by
  rw [backDirPt] at h
  rw [evalF_mkPt_const h]
  simp [sideDirection, neighbor, vertex]

theorem toContact_isS (c : Case) : c.isS = true ↔ c.toContact.isS := by
  cases c <;> simp [Case.isS, Case.toContact, ContactCase.isS]

theorem sext_k_ne {k : Fin 3} (hk : k.val ≠ (recvIdx Case.Sext).val / 2) : k ≠ 2 :=
  fun h => hk (by rw [h]; decide)
theorem sint_k_ne {k : Fin 3} (hk : k.val ≠ (recvIdx Case.Sint).val / 2) : k ≠ 0 :=
  fun h => hk (by rw [h]; decide)
theorem sext_i_ne {i : Fin 6} (h : ¬ i = recvIdx Case.Sext) : i ≠ 5 :=
  fun h' => h (h'.trans (by decide))
theorem sint_i_ne {i : Fin 6} (h : ¬ i = recvIdx Case.Sint) : i ≠ 1 :=
  fun h' => h (h'.trans (by decide))

theorem smallMids_sext {T : Configuration} {r : ℝ}
    (hs : SmallStrengthening .Sext T r) {k : Fin 3} (hk : k ≠ 2) (m : Fin 2) :
    cornerMid k m ∈ (T (cornerIndex k)).carrier :=
  hs.mids k m (fun _ => hk) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (by
      decide)
theorem smallMids_sint {T : Configuration} {r : ℝ}
    (hs : SmallStrengthening .Sint T r) {k : Fin 3} (hk : k ≠ 0) (m : Fin 2) :
    cornerMid k m ∈ (T (cornerIndex k)).carrier :=
  hs.mids k m (fun h => absurd h (by decide)) (fun _ => hk) (fun h => absurd h (by decide)) (by
      decide)
theorem smallMids_aown {T : Configuration} {r : ℝ}
    (hs : SmallStrengthening .Aown T r) {k : Fin 3} (hk : k ≠ 0) (m : Fin 2) :
    cornerMid k m ∈ (T (cornerIndex k)).carrier :=
  hs.mids k m (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun _ => hk) (by
      decide)
theorem smallOrd_sext {T : Configuration} {r : ℝ}
    (hs : SmallStrengthening .Sext T r) {i : Fin 6} (hi : i ≠ 5) :
    rayLen (T (sideIndex i)) (vertex i) (sideDirection i false) +
      rayLen (T (sideIndex i)) (vertex i) (sideDirection i true) ≤ r :=
  hs.nonOverfull i (fun _ => hi) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (by decide)
theorem smallOrd_sint {T : Configuration} {r : ℝ}
    (hs : SmallStrengthening .Sint T r) {i : Fin 6} (hi : i ≠ 1) :
    rayLen (T (sideIndex i)) (vertex i) (sideDirection i false) +
      rayLen (T (sideIndex i)) (vertex i) (sideDirection i true) ≤ r :=
  hs.nonOverfull i (fun h => absurd h (by decide)) (fun _ => hi) (fun h => absurd h (by decide))
    (by decide)
theorem smallOrd_aown {T : Configuration} {r : ℝ}
    (hs : SmallStrengthening .Aown T r) {i : Fin 6} (hi : i ≠ 0) :
    rayLen (T (sideIndex i)) (vertex i) (sideDirection i false) +
      rayLen (T (sideIndex i)) (vertex i) (sideDirection i true) ≤ r :=
  hs.nonOverfull i (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun _ => hi)
    (by decide)

theorem ordOf_some {c : Case} {hi : Rat} {j : Fin 10} {i : Fin 6} (h : ordOf c hi j = some i) :
    smallHi hi = true ∧ j = sideIndex i ∧ (c = .Sext → i ≠ 5) ∧ (c = .Sint → i ≠ 1) ∧
      (c = .Aown → i ≠ 0) ∧ c ≠ .Across := by
  unfold ordOf at h
  by_cases hc : smallHi hi = true ∧ 1 ≤ j.val ∧ j.val ≤ 6
  · rw [dite_eq_left hc] at h
    have hj : j = sideIndex ⟨j.val - 1, by omega⟩ := Fin.ext (by simp [sideIndex]; omega)
    cases c with
    | Sext =>
      rw [show Case.isS Case.Sext = true from rfl] at h
      simp only [↓reduceIte] at h
      by_cases hr : (⟨j.val - 1, by omega⟩ : Fin 6) = recvIdx Case.Sext
      · rw [ite_eq_left hr] at h; simp at h
      · rw [ite_eq_right hr, Option.some.injEq] at h
        subst h
        exact ⟨hc.1, hj, fun _ => sext_i_ne hr, (fun h => by cases h), (fun h => by cases h),
          (fun h => by cases h)⟩
    | Sint =>
      rw [show Case.isS Case.Sint = true from rfl] at h
      simp only [↓reduceIte] at h
      by_cases hr : (⟨j.val - 1, by omega⟩ : Fin 6) = recvIdx Case.Sint
      · rw [ite_eq_left hr] at h; simp at h
      · rw [ite_eq_right hr, Option.some.injEq] at h
        subst h
        exact ⟨hc.1, hj, (fun h => by cases h), fun _ => sint_i_ne hr, (fun h => by cases h),
          (fun h => by cases h)⟩
    | Aown =>
      rw [show Case.isS Case.Aown = false from rfl] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      by_cases hr : (⟨j.val - 1, by omega⟩ : Fin 6) = 0
      · rw [ite_eq_left hr] at h; simp at h
      · rw [ite_eq_right hr, Option.some.injEq] at h
        subst h
        exact ⟨hc.1, hj, (fun h => by cases h), (fun h => by cases h), fun _ => hr,
          (fun h => by cases h)⟩
    | Across =>
      rw [show Case.isS Case.Across = false from rfl] at h
      simp at h
  · rw [dite_eq_right hc] at h
    simp at h

/-! ## The main theorem -/

theorem initModel_holds {c : Case} {lo hi : Rat} {denI : Int} {M : Model}
    (hM : initModel c lo hi denI = some M) (hden : 0 < denI) (hhi1 : (hi : ℝ) ≤ 1)
    (H : Canonical c.toContact T r s) (hhi : s ≤ hi)
    (hsmall : smallHi hi = true → SmallStrengthening c.toContact T r) :
    ModelHolds M T (denI : ℝ) (s - lo) := by
  unfold initModel at hM
  split_ifs at hM with hall
  · revert hM
    rcases he : endpointPt c lo denI with _ | e <;> rcases hdv : exitDirPt c lo denI with _ | dv <;>
      rcases hbd : backDirPt lo denI with _ | bd <;> intro hM <;> simp only [reduceCtorEq] at hM
    simp only [Option.some.injEq] at hM
    subst hM
    have hside : ∀ j, (T j).side = r := H.common
    refine ⟨fun j => by rw [hside]; exact H.r_pos, fun j => by rw [hside]; exact H.r_lt, H.covers,
      ?_, ?_, ?_⟩
    · -- mandatory points
      intro j P hP
      have hraw := mem_filterMap_id (mem_thinHullChecked hP)
      rcases mem_rawB hraw with ⟨rfl, h⟩ | ⟨i, rfl, h⟩ | ⟨k, rfl, h⟩
      · exact corePts_mem H hden hhi hhi1 h
      · rcases h with h | ⟨hS, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩
        · exact sidePts_mem H hden h
        · rw [he, Option.some.injEq] at h
          subst h
          rw [endpointPt_real hden he]
          -- the receiver of the minimal endpoint
          cases c with
          | Sext => exact H.contact
          | Sint => exact H.contact
          | Aown => simp [Case.isS] at hS
          | Across => simp [Case.isS] at hS
        · rw [mid0Pt_real hden h.symm]; exact H.contact.2.2
        · rw [mid0Pt_real hden h.symm]; exact H.contact.2.2
      · rcases h with h | ⟨hS, rfl, h⟩ | ⟨hS, hsm, hk, h⟩ | ⟨rfl, hsm, hk, h⟩
        · exact cornerPts_mem H hden h
        · rw [he, Option.some.injEq] at h
          subst h
          rw [endpointPt_real hden he]
          cases c with
          | Sext => simp [Case.isS] at hS
          | Sint => simp [Case.isS] at hS
          | Aown => exact H.contact.1
          | Across => exact H.contact.1
        · have hsm' := hsmall hsm
          rcases cornerMids_real hden h (s - lo) with h' | h' <;> rw [h']
          · cases c with
            | Sext => exact smallMids_sext hsm' (sext_k_ne hk) 0
            | Sint => exact smallMids_sint hsm' (sint_k_ne hk) 0
            | Aown => simp [Case.isS] at hS
            | Across => simp [Case.isS] at hS
          · cases c with
            | Sext => exact smallMids_sext hsm' (sext_k_ne hk) 1
            | Sint => exact smallMids_sint hsm' (sint_k_ne hk) 1
            | Aown => simp [Case.isS] at hS
            | Across => simp [Case.isS] at hS
        · have hsm' := hsmall hsm
          rcases cornerMids_real hden h (s - lo) with h' | h' <;> rw [h']
          · exact smallMids_aown hsm' hk 0
          · exact smallMids_aown hsm' hk 1
    · -- caps
      intro j cp hcp O
      simp only [capsOf] at hcp
      split_ifs at hcp with h1 h2
      · -- the full endpoint of `S₀`
        rw [List.mem_singleton] at hcp
        subst hcp
        have hj : j = 1 := Fin.ext h1
        subst hj
        have hv : vertex 0 ∈ (T 1).carrier := by
          have := H.anchored 1; simpa [anchor, vertex] using this
        obtain ⟨k, hk, hq⟩ := O.full_endpoint hv (sideDirection_unit 0 c.toContact.right)
        refine ⟨k, ?_, ?_⟩
        · rw [exitDirPt_eval hdv, cross_smul_right]
          exact mul_pos (by exact_mod_cast hden) hk
        · intro q hqU
          rw [endpointPt_real hden he, minEndpoint, ← H.endpoint]
          exact ⟨hq q hqU, fun h => by simp at h⟩
      · -- the strict exclusion of the endpoint from `S₁`
        rw [List.mem_singleton] at hcp
        subst hcp
        have hj : j = 2 := Fin.ext h2.1
        subst hj
        have hS : c.isS = false := by
          simpa using h2.2
        have hv : vertex 1 ∈ (T 2).carrier := by
          have := H.anchored 2; simpa [anchor, vertex] using this
        have hright : c.toContact.right = true := by
          cases c <;> simp_all [Case.isS, Case.toContact, ContactCase.right]
        have hout : linePoint (vertex 1) (sideDirection 1 false) (1 - s) ∉ (T 2).carrier := by
          have hp : linePoint (vertex 1) (sideDirection 1 false) (1 - s) = minEndpoint c.toContact s
              := by
            rw [minEndpoint, hright, linePoint_eq_add, linePoint_eq_add, sideDirection,
              sideDirection, neighbor, neighbor]
            simp only [Bool.false_eq_true, ↓reduceIte]
            apply Prod.ext <;> simp [vertex]; ring
          rw [hp]
          cases c with
          | Sext => simp [Case.isS] at hS
          | Sint => simp [Case.isS] at hS
          | Aown => exact H.contact.2.1
          | Across => exact H.contact.2.1
        have hts : 0 < 1 - s := by
          linarith [H.s_lt]
        obtain ⟨k, hk, hq⟩ := O.forbidden hv hts hout
        refine ⟨k, ?_, ?_⟩
        · rw [backDirPt_eval hbd, cross_smul_right]
          exact mul_pos (by exact_mod_cast hden) hk
        · intro q hqU
          have hp : linePoint (vertex 1) (sideDirection 1 false) (1 - s) = realPt (denI : ℝ) e (s -
              lo) := by
            rw [endpointPt_real hden he, minEndpoint, hright, linePoint_eq_add, linePoint_eq_add,
              sideDirection, sideDirection, neighbor, neighbor]
            simp only [Bool.false_eq_true, ↓reduceIte]
            apply Prod.ext <;> simp [vertex]; ring
          rw [← hp]
          exact ⟨(hq q hqU).le, fun _ => hq q hqU⟩
      · simp at hcp
    · -- non-overfull flags
      intro j i hji
      obtain ⟨hsm, rfl, h1, h2, h3, h4⟩ := ordOf_some hji
      have hsm' := hsmall hsm
      refine ⟨?_, ?_⟩
      · have := H.anchored (sideIndex i); rwa [anchor_sideIndex] at this
      · rw [hside]
        cases c with
        | Sext => exact smallOrd_sext hsm' (h1 rfl)
        | Sint => exact smallOrd_sint hsm' (h2 rfl)
        | Aown => exact smallOrd_aown hsm' (h3 rfl)
        | Across => exact absurd rfl h4

end

end ConwaySoifer.Certificates
