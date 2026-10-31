/-
P0028, arXiv 1610.02017, Lemma 4.3 item 3, page 10.
A nonempty right translate clipped to the original interval is an arithmetic progression.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSShifts

namespace LeanLab.Ternary.MMS
open Finset

/-- Clipping a right shifted progression preserves its progression structure. -/
theorem shiftRightIn_isAP {N t : ℕ} {P : Finset ℕ} (hP : IsAPIn N P)
    (hne : (shiftRightIn N t P).Nonempty) : IsAPIn N (shiftRightIn N t P) := by
  obtain ⟨a, d, L, hd, hL, rfl, hIn⟩ := hP
  have hsub : (range L).image (fun k => a + d * k) ⊆ Icc 1 N := by
    intro n hn
    exact mem_Icc.mpr (hIn n hn)
  have hQsub := shiftRightIn_subset (t := t) hsub
  obtain ⟨n, hn⟩ := hne
  obtain ⟨m, hm, hmn⟩ := mem_image.mp hn
  obtain ⟨hmP, hmN⟩ := mem_filter.mp hm
  obtain ⟨k, hk, hkm⟩ := mem_image.mp hmP
  have haN : a + t ≤ N := by omega
  set J := min L ((N - (a + t)) / d + 1)
  have hJpos : 1 ≤ J := by
    dsimp [J]
    exact le_min hL (Nat.succ_le_succ (Nat.zero_le _))
  refine ⟨a + t, d, J, hd, hJpos, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨m, hm, rfl⟩ := mem_image.mp hx
      obtain ⟨hmP, hmN⟩ := mem_filter.mp hm
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hmP
      have hjL : j < L := mem_range.mp hj
      have hmul : j * d ≤ N - (a + t) := by
        have hdj : d * j ≤ N - (a + t) := by omega
        simpa only [mul_comm] using hdj
      have hjd : j ≤ (N - (a + t)) / d :=
        (Nat.le_div_iff_mul_le (by omega)).mpr hmul
      refine mem_image.mpr ⟨j, mem_range.mpr ?_, by omega⟩
      dsimp [J]
      exact lt_min hjL (by omega)
    · intro hx
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
      have hjJ : j < min L ((N - (a + t)) / d + 1) := mem_range.mp hj
      have hjL : j < L := (lt_min_iff.mp hjJ).1
      have hjd : j ≤ (N - (a + t)) / d := by
        have := (lt_min_iff.mp hjJ).2
        omega
      have hmul : j * d ≤ N - (a + t) :=
        (Nat.le_div_iff_mul_le (by omega)).mp hjd
      have hdj : d * j ≤ N - (a + t) := by simpa only [mul_comm] using hmul
      apply mem_image.mpr
      refine ⟨a + d * j, mem_filter.mpr ⟨?_, by omega⟩, by omega⟩
      exact mem_image.mpr ⟨j, mem_range.mpr hjL, rfl⟩
  · intro n hn
    exact mem_Icc.mp (hQsub hn)

/-- Clipping a left shifted progression preserves its progression structure. -/
theorem shiftLeftIn_isAP {N t : ℕ} {P : Finset ℕ} (hP : IsAPIn N P)
    (hne : (shiftLeftIn t P).Nonempty) : IsAPIn N (shiftLeftIn t P) := by
  obtain ⟨a, d, L, hd, hL, rfl, hIn⟩ := hP
  have hsub : (range L).image (fun k => a + d * k) ⊆ Icc 1 N := by
    intro n hn
    exact mem_Icc.mpr (hIn n hn)
  have hQsub := shiftLeftIn_subset (t := t) hsub
  obtain ⟨n, hn⟩ := hne
  obtain ⟨m, hm, hmn⟩ := mem_image.mp hn
  obtain ⟨hmP, htm⟩ := mem_filter.mp hm
  obtain ⟨k, hk, hkm⟩ := mem_image.mp hmP
  have hex : ∃ j : ℕ, t < a + d * j := ⟨k, by omega⟩
  let j₀ := Nat.find hex
  have hj₀ : t < a + d * j₀ := Nat.find_spec hex
  have hj₀k : j₀ ≤ k := Nat.find_min' hex (by omega)
  have hj₀L : j₀ < L := lt_of_le_of_lt hj₀k (mem_range.mp hk)
  refine ⟨a + d * j₀ - t, d, L - j₀, hd, by omega, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨m, hm, rfl⟩ := mem_image.mp hx
      obtain ⟨hmP, htm⟩ := mem_filter.mp hm
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hmP
      have hjL := mem_range.mp hj
      have hj : j₀ ≤ j := Nat.find_min' hex htm
      have he : d * j = d * j₀ + d * (j - j₀) := by
        rw [← Nat.mul_add]
        congr 1
        omega
      refine mem_image.mpr ⟨j - j₀, mem_range.mpr (by omega), ?_⟩
      rw [he]
      omega
    · intro hx
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
      have hiL : j₀ + i < L := by have := mem_range.mp hi; omega
      have he : d * (j₀ + i) = d * j₀ + d * i := Nat.mul_add _ _ _
      apply mem_image.mpr
      refine ⟨a + d * (j₀ + i), mem_filter.mpr ⟨?_, by omega⟩, ?_⟩
      · exact mem_image.mpr ⟨j₀ + i, mem_range.mpr hiL, rfl⟩
      · rw [he]
        omega
  · intro n hn
    exact mem_Icc.mp (hQsub hn)

end LeanLab.Ternary.MMS
