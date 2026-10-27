/-
P0005 page 2033 and P0042 page 423 define minimal partitions using odd primes.
P0042 also orders the two primes. This file relates that convention to minGB.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Verifications.CitedInputs

namespace LeanLab.Verifications.PartitionConventionTask72

/-- The least first prime among ordered odd-prime partitions, or zero without a partition. -/
noncomputable def paperMinGB (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ p, p.Prime ∧ (n - p).Prime ∧ Odd p ∧ Odd (n - p) ∧ p ≤ n - p then
    Nat.find h else 0

/-- A least-prime value has the required prime witnesses whenever a partition exists. -/
theorem minGB_spec_of_exists {n : ℕ} (hex : ∃ p, p.Prime ∧ (n - p).Prime) :
    (minGB n).Prime ∧ (n - minGB n).Prime := by
  unfold minGB
  rw [dif_pos hex]
  exact Nat.find_spec hex

/-- The least first prime never exceeds its complementary prime. -/
theorem minGB_ordered_of_exists {n : ℕ} (hex : ∃ p, p.Prime ∧ (n - p).Prime) :
    minGB n ≤ n - minGB n := by
  unfold minGB
  rw [dif_pos hex]
  have hp := Nat.find_spec hex
  have hle : Nat.find hex ≤ n := by
    have hpos := hp.2.pos
    omega
  apply Nat.find_min' hex
  refine ⟨hp.2, ?_⟩
  simpa only [Nat.sub_sub_self hle] using hp.1

/-- Both primes of an even partition above four are odd. -/
theorem prime_pair_odd {n p q : ℕ} (he : Even n) (h6 : 6 ≤ n)
    (hp : p.Prime) (hq : q.Prime) (hs : p + q = n) : Odd p ∧ Odd q := by
  have ho : ∀ {a b : ℕ}, a.Prime → b.Prime → a + b = n → Odd a := by
    intro a b ha hb hab
    rcases ha.eq_two_or_odd' with rfl | hodd
    · rcases hb.eq_two_or_odd' with rfl | ⟨k, hk⟩
      · omega
      · rcases he with ⟨t, ht⟩
        omega
    · exact hodd
  exact ⟨ho hp hq hs, ho hq hp (by omega)⟩

/-- For even n at least six the lab and paper least-prime conventions agree. -/
theorem minGB_eq_paperMinGB {n : ℕ} (he : Even n) (h6 : 6 ≤ n) :
    minGB n = paperMinGB n := by
  classical
  by_cases hex : ∃ p, p.Prime ∧ (n - p).Prime
  · have hp := minGB_spec_of_exists hex
    have hle : minGB n ≤ n := by
      have hpos := hp.2.pos
      omega
    have hs : minGB n + (n - minGB n) = n := Nat.add_sub_of_le hle
    have ho := prime_pair_odd he h6 hp.1 hp.2 hs
    have hspec : (minGB n).Prime ∧ (n - minGB n).Prime ∧
        Odd (minGB n) ∧ Odd (n - minGB n) ∧ minGB n ≤ n - minGB n :=
      ⟨hp.1, hp.2, ho.1, ho.2, minGB_ordered_of_exists hex⟩
    have hpaper : ∃ p, p.Prime ∧ (n - p).Prime ∧ Odd p ∧ Odd (n - p) ∧ p ≤ n - p :=
      ⟨minGB n, hspec⟩
    unfold paperMinGB
    rw [dif_pos hpaper]
    apply le_antisymm
    · have ht := Nat.find_spec hpaper
      exact (CitedInputs.minGB_le_iff_of_exists hex).mpr
        ⟨Nat.find hpaper, le_rfl, ht.1, ht.2.1⟩
    · exact Nat.find_min' hpaper hspec
  · have hpaper : ¬ ∃ p, p.Prime ∧ (n - p).Prime ∧ Odd p ∧ Odd (n - p) ∧ p ≤ n - p := by
      rintro ⟨p, hp, hq, _⟩
      exact hex ⟨p, hp, hq⟩
    simp only [minGB, paperMinGB, dif_neg hex, dif_neg hpaper]

/-- Six equals three plus three, an ordered odd-prime partition in both conventions. -/
theorem paper_partition_instance :
    Even (6 : ℕ) ∧ (6 : ℕ) ≤ 6 ∧ Nat.Prime 3 ∧ Nat.Prime (6 - 3) ∧
      Odd (3 : ℕ) ∧ Odd (6 - 3 : ℕ) ∧ (3 : ℕ) ≤ 6 - 3 := by
  norm_num

end LeanLab.Verifications.PartitionConventionTask72
