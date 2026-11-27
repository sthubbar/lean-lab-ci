import LeanLab.ChenDoubleSieve.Decomp275b

/-!
Exact cofactor identities for the sieve sums of Wu 2004 pages 35 and 39 to 41.
Source: https://arxiv.org/pdf/0705.1652, equations 9.4 and 10.3 to 10.12.
These identities retain the sealed prime-difference sequence and sifting modulus.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Finset
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task693
open Task275

/-- Reindex the divisor sieve by its cofactor, as in Wu 2004 Sections 9 and 10. -/
theorem sieve_eq_quotient_count (A : Finset ℕ) (N d D : ℕ) (z : ℝ)
    (hd : 0 < d) (hA : ∀ a ∈ A, a ≤ N) :
    Wu41.S A d D z = #{m ∈ range (N / d + 1) | d * m ∈ A ∧ Wu41.Sifted D z (d * m)} := by
  unfold Wu41.S
  apply Finset.card_bij (fun a _ => a / d)
  · intro a ha
    obtain ⟨haA, had, hs⟩ := mem_filter.mp ha
    have he : d * (a / d) = a := Nat.mul_div_cancel' had
    refine mem_filter.mpr ⟨mem_range.mpr ?_, ?_⟩
    · have hle : a / d ≤ N / d := Nat.div_le_div_right (hA a haA)
      omega
    · rw [he]
      exact ⟨haA, hs⟩
  · intro a ha b hb he
    obtain ⟨haA, had, hs⟩ := mem_filter.mp ha
    obtain ⟨hbA, hbd, ht⟩ := mem_filter.mp hb
    calc a = d * (a / d) := (Nat.mul_div_cancel' had).symm
         _ = d * (b / d) := by rw [he]
         _ = b := Nat.mul_div_cancel' hbd
  · intro m hm
    obtain ⟨hmrange, hmA, hs⟩ := mem_filter.mp hm
    refine ⟨d * m, mem_filter.mpr ⟨hmA, dvd_mul_right d m, hs⟩, ?_⟩
    exact Nat.mul_div_cancel_left m hd


/-- Membership in the prime-difference sequence of Wu 2004 page 33. -/
theorem mem_primeSequence_iff (N a : ℕ) :
    a ∈ primeSequence N ↔ a ≤ N ∧ (N - a).Prime := by
  constructor
  · intro ha
    obtain ⟨p, hp, rfl⟩ := mem_image.mp ha
    obtain ⟨hpN, hp⟩ := mem_filter.mp hp
    have hpN' : p ≤ N := by have := mem_range.mp hpN; omega
    exact ⟨Nat.sub_le _ _, by simpa [Nat.sub_sub_self hpN'] using hp⟩
  · rintro ⟨haN, ha⟩
    apply mem_image.mpr
    refine ⟨N - a, mem_filter.mpr ⟨mem_range.mpr ?_, ha⟩, ?_⟩
    · have := Nat.sub_le N a
      omega
    · exact Nat.sub_sub_self haN



/-- Exact prime-difference cofactor count for Wu 2004 pages 39 to 41. -/
theorem sieve_primeSequence_eq (N d D : ℕ) (z : ℝ) (hd : 0 < d) :
    Wu41.S (primeSequence N) d D z =
      #{m ∈ range (N / d + 1) | (N - d * m).Prime ∧ Wu41.Sifted D z (d * m)} := by
  rw [sieve_eq_quotient_count (primeSequence N) N d D z hd (fun a ha =>
    (mem_primeSequence_iff N a).mp ha |>.1)]
  congr 1
  apply Finset.filter_congr
  intro m hm
  have hmN : m ≤ N / d := by have := mem_range.mp hm; omega
  have hprod : d * m ≤ N := by
    have := (Nat.le_div_iff_mul_le hd).mp hmN
    simpa [mul_comm] using this
  rw [mem_primeSequence_iff]
  simp only [hprod, true_and]


/-- A sifted cofactor is rough unless the excluded first prime divides it, Wu page 41. -/
theorem rough_cofactor_or_repeat {N p a m : ℕ} {z : ℝ}
    (hp : p.Prime) (haN : a.Coprime N) (hma : m ∣ a)
    (hs : Wu41.Sifted (N * p) z a) : p ∣ m ∨ Wu41.Sifted 1 z m := by
  by_cases hpm : p ∣ m
  · exact Or.inl hpm
  right
  intro r hr hrz _ hdiv
  have hra : r ∣ a := hdiv.trans hma
  have hrN : ¬ r ∣ N :=
    (Nat.Prime.coprime_iff_not_dvd hr).mp (haN.coprime_dvd_left hra)
  have hrp : ¬ r ∣ p := by
    intro hdivp
    have he : r = p := (Nat.dvd_prime hp).mp hdivp |>.resolve_left hr.ne_one
    exact hpm (he ▸ hdiv)
  have hrNp : ¬ r ∣ N * p := by
    intro hd
    exact (hr.dvd_mul.mp hd).elim hrN hrp
  exact hs r hr hrz hrNp hra


/-- A concrete repeated-prime cofactor in the switching model of Wu pages 40 and 41. -/
theorem composite_cofactor_instance :
    (189 : ℕ) ∈ primeSequence 256 ∧ Nat.Prime 3 ∧ Nat.Coprime 189 256 ∧
      Wu41.Sifted (256 * 3) (7 : ℝ) 189 ∧
      (189 : ℕ) = 3 * 7 * 9 ∧ (0 : ℕ) < 9 ∧ (9 : ℕ) < 7 ^ 2 ∧
      (9 : ℕ) ≠ 1 ∧ ¬ Nat.Prime 9 := by
  have hs : Wu41.Sifted (256 * 3) (7 : ℝ) 189 := by
    intro r hr hr5 hrD hra
    have hr5' : r < 7 := by exact_mod_cast hr5
    interval_cases r <;> norm_num at *
  exact ⟨(mem_primeSequence_iff 256 189).mpr ⟨by decide, by decide⟩,
    by decide, by decide, hs, by decide, by decide, by decide, by decide, by decide⟩

end LeanLab.ChenDoubleSieve.Task693
