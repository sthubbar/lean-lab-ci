/-
P0028, arXiv 1610.02017, Lemma 4.3 proof, page 10.
A shift by t loses at most t points from an interval subset.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSTransference

namespace LeanLab.Ternary.MMS
open Finset

/-- Surviving points after a right shift by t. -/
def shiftRightIn (N t : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (P.filter (fun n => n + t ≤ N)).image (fun n => n + t)

/-- Surviving points after a left shift by t. -/
def shiftLeftIn (t : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (P.filter (fun n => t < n)).image (fun n => n - t)

/-- The right shift stays in the original interval after removing its last t points. -/
theorem shiftRightIn_subset {N t : ℕ} {P : Finset ℕ} (hP : P ⊆ Icc 1 N) :
    shiftRightIn N t P ⊆ Icc 1 N := by
  intro n hn
  obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
  obtain ⟨hmP, hmN⟩ := mem_filter.mp hm
  have hm1 := (mem_Icc.mp (hP hmP)).1
  exact mem_Icc.mpr ⟨by omega, hmN⟩

/-- The left shift stays in the original interval after removing its first t points. -/
theorem shiftLeftIn_subset {N t : ℕ} {P : Finset ℕ} (hP : P ⊆ Icc 1 N) :
    shiftLeftIn t P ⊆ Icc 1 N := by
  intro n hn
  obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
  obtain ⟨hmP, htm⟩ := mem_filter.mp hm
  have hmN := (mem_Icc.mp (hP hmP)).2
  exact mem_Icc.mpr ⟨by omega, by omega⟩

/-- At most t points are lost to the right boundary. -/
theorem shiftRightIn_card {N t : ℕ} {P : Finset ℕ} (hP : P ⊆ Icc 1 N) :
    P.card - t ≤ (shiftRightIn N t P).card := by
  have hbad : P.filter (fun n => ¬ (n + t ≤ N)) ⊆ Icc (N - t + 1) N := by
    intro n hn
    obtain ⟨hnP, hnt⟩ := mem_filter.mp hn
    have hnN := mem_Icc.mp (hP hnP)
    exact mem_Icc.mpr ⟨by omega, hnN.2⟩
  have hb : (P.filter (fun n => ¬ (n + t ≤ N))).card ≤ t :=
    (card_le_card hbad).trans (by simp; omega)
  have hc := card_filter_add_card_filter_not (s := P) (fun n => n + t ≤ N)
  have he : (shiftRightIn N t P).card = (P.filter (fun n => n + t ≤ N)).card := by
    unfold shiftRightIn
    apply card_image_of_injOn
    intro a ha b hb hab
    change a + t = b + t at hab
    omega
  omega

/-- At most t points are lost to the left boundary. -/
theorem shiftLeftIn_card {N t : ℕ} {P : Finset ℕ} (hP : P ⊆ Icc 1 N) :
    P.card - t ≤ (shiftLeftIn t P).card := by
  have hbad : P.filter (fun n => ¬ (t < n)) ⊆ Icc 1 t := by
    intro n hn
    obtain ⟨hnP, hnt⟩ := mem_filter.mp hn
    have hnN := mem_Icc.mp (hP hnP)
    exact mem_Icc.mpr ⟨hnN.1, by omega⟩
  have hb : (P.filter (fun n => ¬ (t < n))).card ≤ t :=
    (card_le_card hbad).trans (by simp)
  have hc := card_filter_add_card_filter_not (s := P) (fun n => t < n)
  have he : (shiftLeftIn t P).card = (P.filter (fun n => t < n)).card := by
    unfold shiftLeftIn
    apply card_image_of_injOn
    intro a ha b hb hab
    change a - t = b - t at hab
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    omega
  omega

end LeanLab.Ternary.MMS
