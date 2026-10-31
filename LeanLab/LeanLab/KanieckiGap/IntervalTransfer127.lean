/-
P0022, page 373. Transfer the natural interval input to real starting points
without increasing its even integer width.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.KanieckiGap.PaperAssembly127

namespace LeanLab.KanieckiGap.IntervalTransfer127

/-- Page 373. At even integer widths the natural interval statement implies
its real version up to the same natural cutoff. CONDITIONAL ON IntervalProp. -/
theorem real_of_nat {H N₀ : ℕ} (hI : IntervalProp H N₀) (hH : Even H)
    (x : ℝ) (hx0 : 0 ≤ x) (hxN : x ≤ N₀) :
    LeanLab.Kaniecki1995.HasOddPairSumIn x H := by
  have hf : ⌊x⌋₊ ≤ N₀ := Nat.floor_le_of_le hxN
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hfu : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  by_cases hi : x = (⌊x⌋₊ : ℝ)
  · obtain ⟨p, q, hp, op, hq, oq, hlo, hhi⟩ := hI ⌊x⌋₊ hf
    refine ⟨p, q, hp, hq, op, oq, ?_, ?_⟩
    · rw [hi]
      exact_mod_cast hlo
    · rw [hi]
      exact_mod_cast hhi
  have hxlt : x < N₀ := by
    apply lt_of_le_of_ne hxN
    intro heq
    apply hi
    rw [heq, Nat.floor_natCast]
  have hfs : ⌊x⌋₊ + 1 ≤ N₀ := by
    have := (Nat.floor_lt hx0).mpr hxlt
    omega
  rcases Nat.even_or_odd ⌊x⌋₊ with he | ho
  · obtain ⟨p, q, hp, op, hq, oq, hlo, hhi⟩ := hI (⌊x⌋₊ + 1) hfs
    have hsum := op.add_odd oq
    have hcap : p + q ≤ ⌊x⌋₊ + H := by
      obtain ⟨a, ha⟩ := he
      obtain ⟨b, hb⟩ := hH
      obtain ⟨c, hc⟩ := hsum
      omega
    refine ⟨p, q, hp, hq, op, oq, ?_, ?_⟩
    · have : (⌊x⌋₊ : ℝ) + 1 ≤ ((p + q : ℕ) : ℝ) := by exact_mod_cast hlo
      linarith
    · have : ((p + q : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) + H := by exact_mod_cast hcap
      linarith
  · obtain ⟨p, q, hp, op, hq, oq, hlo, hhi⟩ := hI ⌊x⌋₊ hf
    have hsum := op.add_odd oq
    have hstrict : ⌊x⌋₊ + 1 ≤ p + q := by
      obtain ⟨a, ha⟩ := ho
      obtain ⟨b, hb⟩ := hsum
      omega
    refine ⟨p, q, hp, hq, op, oq, ?_, ?_⟩
    · have : (⌊x⌋₊ : ℝ) + 1 ≤ ((p + q : ℕ) : ℝ) := by exact_mod_cast hstrict
      linarith
    · have : ((p + q : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) + H := by exact_mod_cast hhi
      linarith

/-- Page 373. Real starting points from an integer statement at any larger
natural cutoff. CONDITIONAL ON IntervalProp. -/
theorem real_below_cutoff {H N₀ : ℕ} (hI : IntervalProp H N₀) (hH : Even H)
    (x : ℝ) (hx0 : 0 ≤ x) (hxN : x ≤ (N₀ : ℝ)) :
    ∃ p q : ℕ, p.Prime ∧ Odd p ∧ q.Prime ∧ Odd q ∧
      x ≤ ((p + q : ℕ) : ℝ) ∧ ((p + q : ℕ) : ℝ) ≤ x + H := by
  obtain ⟨p, q, hp, hq, op, oq, hlo, hhi⟩ := real_of_nat hI hH x hx0 hxN
  exact ⟨p, q, hp, op, hq, oq, hlo, hhi⟩

/-- Page 373. A concrete nonintegral instance of the unchanged interval width. -/
theorem nonintegral_instance : LeanLab.Kaniecki1995.HasOddPairSumIn 4.5 18 := by
  exact real_of_nat PaperAssembly127.interval_instance (by decide) 4.5 (by norm_num)
    (by norm_num)

end LeanLab.KanieckiGap.IntervalTransfer127

#print axioms LeanLab.KanieckiGap.IntervalTransfer127.real_of_nat
#print axioms LeanLab.KanieckiGap.IntervalTransfer127.real_below_cutoff
#print axioms LeanLab.KanieckiGap.IntervalTransfer127.nonintegral_instance
