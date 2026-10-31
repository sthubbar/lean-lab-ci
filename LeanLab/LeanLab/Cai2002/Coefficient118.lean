/-
P0044, pages 602 to 603. The actual switched pair set and coefficient.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Switching118
import LeanLab.Cai2002.LemmaSum
open Finset Real
noncomputable section
namespace LeanLab.Cai2002
/-- The indexed prime pair set behind E on page 602. -/
def switchedPairs118 (N : ℕ) : Finset (ℕ × ℕ) :=
  ((range (N + 1)).product (range (N + 1))).filter (fun b =>
    b.1.Prime ∧ b.2.Prime ∧ z1 N ≤ (b.1 : ℝ) ∧ (b.1 : ℝ) < z2 N ∧
    z2 N ≤ (b.2 : ℝ) ∧ (b.2 : ℝ) < ((N : ℝ) / (b.1 : ℝ)) ^ (1 / 2 : ℝ) ∧
    Nat.Coprime (b.1 * b.2) N)
/-- The representation coefficient g of page 603 for the actual switched pair set. -/
def switchedMultiplicity118 (N a : ℕ) : ℕ := pairMultiplicity118 (switchedPairs118 N) a

/-- The finite enumeration is exactly the printed pair region for N at least two.
Page 602, the set E before display 4.9. -/
theorem mem_switchedPairs118_iff (N p q : ℕ) (hN : 2 ≤ N) : (p, q) ∈ switchedPairs118 N ↔
    p.Prime ∧ q.Prime ∧ z1 N ≤ (p : ℝ) ∧ (p : ℝ) < z2 N ∧
    z2 N ≤ (q : ℝ) ∧ (q : ℝ) < ((N : ℝ) / (p : ℝ)) ^ (1 / 2 : ℝ) ∧
    Nat.Coprime (p * q) N := by
  constructor
  · intro h
    exact (mem_filter.mp h).2
  · intro h
    obtain ⟨hp, hq, hp1, hp2, hq1, hq2, hc⟩ := h
    have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have he := switched_product_range118 (N : ℝ) p q hNr hp1 hp2 hq1 hq2
    have hroot : (N : ℝ) ^ (2 / 3 : ℝ) < N := by
      simpa using rpow_lt_rpow_of_exponent_lt hNr (by norm_num : (2 / 3 : ℝ) < 1)
    have hpq : p * q < N := by exact_mod_cast he.2.trans hroot
    have hpos : 0 < p * q := Nat.mul_pos hp.pos hq.pos
    have hple : p ≤ p * q := Nat.le_of_dvd hpos (dvd_mul_right p q)
    have hqle : q ≤ p * q := Nat.le_of_dvd hpos (dvd_mul_left q p)
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (by omega),
      mem_range.mpr (by omega)⟩, hp, hq, hp1, hp2, hq1, hq2, hc⟩

/-- Page 603: g is at most one for the paper's actual switched region. -/
theorem switchedMultiplicity118_le_one (N a : ℕ) : switchedMultiplicity118 N a ≤ 1 := by
  apply pairMultiplicity118_le_one (switchedPairs118 N) (z2 N)
  intro b hb
  rcases (mem_filter.mp hb).2 with ⟨hp, hq, _, hp2, hq1, _, _⟩
  exact ⟨hp, hq, hp2, hq1⟩


/-- Page 599 Lemma 4 hypothesis, uniformly verified for the coefficient of page 603. -/
theorem switchedMultiplicity118_log_bound (N : ℕ) (x : ℝ) (hx : Real.exp 1 ≤ x) :
    ∑ a ∈ Icc 1 ⌊x⌋₊, (switchedMultiplicity118 N a : ℝ) ^ 2 / (a : ℝ) ≤ 2 * Real.log x := by
  apply pairMultiplicity118_log_bound (switchedPairs118 N) (z2 N) _ x hx
  intro b hb
  rcases (mem_filter.mp hb).2 with ⟨hp, hq, _, hp2, hq1, _, _⟩
  exact ⟨hp, hq, hp2, hq1⟩

/-- The product set E on page 602. -/
noncomputable def switchedE118 (N : ℕ) : Finset ℕ :=
  (switchedPairs118 N).image (fun b => b.1 * b.2)
/-- The coefficient g of page 603 is the indicator of the product set E.
Uniqueness of the separated prime representation justifies the equality. -/
theorem switchedMultiplicity118_eq_indicator (N a : ℕ) : switchedMultiplicity118 N a = if a ∈ switchedE118 N then 1 else 0 := by
  have hpos : 0 < switchedMultiplicity118 N a ↔ a ∈ switchedE118 N := by
    constructor
    · intro h
      obtain ⟨b, hb⟩ := card_pos.mp h
      obtain ⟨hbT, hba⟩ := mem_filter.mp hb
      exact mem_image.mpr ⟨b, hbT, hba⟩
    · intro h
      obtain ⟨b, hbT, hba⟩ := mem_image.mp h
      exact card_pos.mpr ⟨b, mem_filter.mpr ⟨hbT, hba⟩⟩
  have hle := switchedMultiplicity118_le_one N a
  by_cases ha : a ∈ switchedE118 N
  · rw [ite_eq_left ha]
    have := hpos.mpr ha
    omega
  · rw [ite_eq_right ha]
    have := mt hpos.mp ha
    omega

end LeanLab.Cai2002
