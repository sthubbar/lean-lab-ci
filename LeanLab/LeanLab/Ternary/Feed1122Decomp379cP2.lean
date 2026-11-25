/-
Pass 2 split of edge_sieve_upper from Feed1122Decomp379c.
MMS https://arxiv.org/abs/1610.02017v2, page 12 second paragraph, the sentence
"By a simple sieve upper bound" for the two edge pieces of length eta x to the theta.
The majorant of equation 5.1 on page 11 is at most a fixed multiple,
proved here, of the indicator of
x to the 1/10 rough numbers, and those are counted in short intervals and classes
modulo W by an upper bound sieve. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Feed1122Decomp379c

namespace LeanLab.Ternary.MMS.Task379
open Finset

/-- The rough indicator of MMS page 11 is at most one. Derived from its definition. -/
theorem edge_rough_le_one (n : ℕ) (y : ℝ) : Task361.roughIndicator n y ≤ 1 := by
  classical
  unfold Task361.roughIndicator
  split_ifs <;> norm_num

/-- The rough indicator of MMS page 11 takes only the values zero and one. -/
theorem edge_rough_eq_zero_or_one (n : ℕ) (y : ℝ) :
    Task361.roughIndicator n y = 0 ∨ Task361.roughIndicator n y = 1 := by
  classical
  unfold Task361.roughIndicator
  split_ifs <;> simp

/-- A vanishing rough indicator has a small prime factor. MMS page 11 definition. -/
theorem edge_rough_zero_exists {n : ℕ} {y : ℝ} (h : Task361.roughIndicator n y = 0) :
    ∃ q : ℕ, q.Prime ∧ (q : ℝ) < y ∧ q ∣ n := by
  classical
  unfold Task361.roughIndicator at h
  split_ifs at h with hh
  · norm_num at h
  · push_neg at hh
    exact hh

/-- A small prime factor makes the rough indicator vanish. MMS page 11 definition. -/
theorem edge_rough_zero_of {n : ℕ} {y : ℝ} {q : ℕ} (hq : q.Prime) (hqy : (q : ℝ) < y)
    (hqn : q ∣ n) : Task361.roughIndicator n y = 0 := by
  classical
  unfold Task361.roughIndicator
  rw [if_neg]
  intro h
  exact h q hq hqy hqn

/-- The triple sum of MMS page 11 equation 5.1 is at most the cube of the number of
admissible primes. Derived counting step for the pointwise size of rho plus. -/
theorem edge_triple_sum_le (x : ℝ) (n : ℕ) (P : Finset ℕ)
    (hP : ∀ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ x ^ (1 / 10 : ℝ) < p₁ ∧
          p₁ < p₂ ∧ p₂ < p₃ ∧ (p₃ : ℝ) < x ^ (1 / 4 : ℝ) ∧ p₁ * p₂ * p₃ ∣ n →
          p₁ ∈ P ∧ p₂ ∈ P ∧ p₃ ∈ P) :
    (∑ p₁ ∈ range (n + 1), ∑ p₂ ∈ range (n + 1), ∑ p₃ ∈ range (n + 1),
      if p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ x ^ (1 / 10 : ℝ) < p₁ ∧
          p₁ < p₂ ∧ p₂ < p₃ ∧ (p₃ : ℝ) < x ^ (1 / 4 : ℝ) ∧ p₁ * p₂ * p₃ ∣ n then
        Task361.roughIndicator (n / (p₁ * p₂ * p₃)) p₁ else 0) ≤ (P.card : ℝ) ^ 3 := by
  classical
  set a : ℕ → ℝ := fun p => if p ∈ P then 1 else 0 with ha
  have ha0 : ∀ p, 0 ≤ a p := fun p => by simp only [ha]; split_ifs <;> norm_num
  have hsa : ∑ p ∈ range (n + 1), a p ≤ P.card := by
    simp only [ha]
    rw [sum_boole]
    exact_mod_cast card_le_card (fun p hp => (mem_filter.mp hp).2)
  calc _ ≤ ∑ p₁ ∈ range (n + 1), ∑ p₂ ∈ range (n + 1), ∑ p₃ ∈ range (n + 1),
        a p₁ * a p₂ * a p₃ := by
        apply sum_le_sum; intro p₁ _
        apply sum_le_sum; intro p₂ _
        apply sum_le_sum; intro p₃ _
        split_ifs with hc
        · obtain ⟨h1, h2, h3⟩ := hP p₁ p₂ p₃ hc
          simp only [ha, if_pos h1, if_pos h2, if_pos h3]
          norm_num
          exact edge_rough_le_one _ _
        · exact mul_nonneg (mul_nonneg (ha0 _) (ha0 _)) (ha0 _)
    _ = (∑ p ∈ range (n + 1), a p) * (∑ p ∈ range (n + 1), a p) *
          (∑ p ∈ range (n + 1), a p) := by
        simp only [sum_mul, mul_sum]
        exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    _ ≤ (P.card : ℝ) * P.card * P.card := by
        have h0 : 0 ≤ ∑ p ∈ range (n + 1), a p := sum_nonneg (fun p _ => ha0 p)
        gcongr
    _ = (P.card : ℝ) ^ 3 := by ring

/-- Proved, MMS page 11 equation 5.1, the pointwise size of the majorant rho plus.
Every term of equation 5.1 is supported on integers free of primes below x to the 1/10,
since p1 exceeds x to the 1/10 and the cofactor is p1 rough. An integer up to 2 x has at
most ten distinct prime factors above x to the 1/10 once x to the 1/10 exceeds 2, so at
most 1000 ordered triples occur, and the majorant is at most 1 plus 1000. -/
theorem harmanMajorant_le_rough :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ n : ℕ, 0 < n → (n : ℝ) ≤ 2 * x →
      Task361.harmanMajorant x n ≤ 1001 * Task361.roughIndicator n (x ^ (1 / 10 : ℝ)) := by
  classical
  refine ⟨1025, fun x hx n hn hn2 => ?_⟩
  have hx0 : 0 < x := by linarith
  set y := x ^ (1 / 10 : ℝ) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hx0 _
  have hy10 : y ^ (10 : ℕ) = x := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hy2 : 2 < y := by
    by_contra h
    push_neg at h
    have : y ^ (10 : ℕ) ≤ 2 ^ (10 : ℕ) := pow_le_pow_left₀ hy0.le h 10
    rw [hy10] at this
    norm_num at this
    linarith
  have hyz : y ≤ x ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  rcases edge_rough_eq_zero_or_one n y with h0 | h1
  · obtain ⟨q, hq, hqy, hqn⟩ := edge_rough_zero_exists h0
    rw [h0, mul_zero]
    apply le_of_eq
    unfold Task361.harmanMajorant
    rw [edge_rough_zero_of hq (hqy.trans_le hyz) hqn, zero_add]
    apply sum_eq_zero; intro p₁ _
    apply sum_eq_zero; intro p₂ _
    apply sum_eq_zero; intro p₃ _
    split_ifs with hc
    · obtain ⟨h1, h2, h3, h4, h5, h6, -, h8⟩ := hc
      have hq1 : (q : ℝ) < p₁ := hqy.trans h4
      have hq2 : (q : ℝ) < p₂ := hq1.trans (by exact_mod_cast h5)
      have hq3 : (q : ℝ) < p₃ := hq2.trans (by exact_mod_cast h6)
      have cop : ∀ p : ℕ, p.Prime → (q : ℝ) < p → Nat.Coprime q p := fun p hp hlt =>
        (Nat.coprime_primes hq hp).mpr (fun he => by rw [he] at hlt; exact lt_irrefl _ hlt)
      have hcop : Nat.Coprime q (p₁ * p₂ * p₃) :=
        Nat.Coprime.mul_right (Nat.Coprime.mul_right (cop _ h1 hq1) (cop _ h2 hq2))
          (cop _ h3 hq3)
      have hqd : q ∣ n / (p₁ * p₂ * p₃) := by
        apply hcop.dvd_of_dvd_mul_left
        rw [Nat.mul_div_cancel' h8]
        exact hqn
      exact edge_rough_zero_of hq hq1 hqd
    · rfl
  · rw [h1, mul_one]
    set P : Finset ℕ := n.primeFactors.filter (fun p : ℕ => y < (p : ℝ)) with hP
    have hPmem : ∀ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ x ^ (1 / 10 : ℝ) < p₁ ∧
          p₁ < p₂ ∧ p₂ < p₃ ∧ (p₃ : ℝ) < x ^ (1 / 4 : ℝ) ∧ p₁ * p₂ * p₃ ∣ n →
          p₁ ∈ P ∧ p₂ ∈ P ∧ p₃ ∈ P := by
      rintro p₁ p₂ p₃ ⟨h1, h2, h3, h4, h5, h6, -, h8⟩
      have hn0 : n ≠ 0 := hn.ne'
      have d1 : p₁ ∣ n := (Dvd.intro _ rfl).trans ((Dvd.intro _ rfl).trans h8)
      have d2 : p₂ ∣ n := (Dvd.intro_left _ rfl).trans ((Dvd.intro _ rfl).trans h8)
      have d3 : p₃ ∣ n := (Dvd.intro_left _ rfl).trans h8
      have l2 : y < (p₂ : ℝ) := h4.trans (by exact_mod_cast h5)
      have l3 : y < (p₃ : ℝ) := l2.trans (by exact_mod_cast h6)
      refine ⟨?_, ?_, ?_⟩ <;> simp only [hP, mem_filter, Nat.mem_primeFactors]
      · exact ⟨⟨h1, d1, hn0⟩, h4⟩
      · exact ⟨⟨h2, d2, hn0⟩, l2⟩
      · exact ⟨⟨h3, d3, hn0⟩, l3⟩
    have htrip := edge_triple_sum_le x n P hPmem
    have hprod : ∏ p ∈ P, p ∣ n :=
      (Finset.prod_dvd_prod_of_subset P n.primeFactors id (filter_subset _ _)).trans
        (Nat.prod_primeFactors_dvd n)
    have hprodle : ((∏ p ∈ P, p : ℕ) : ℝ) ≤ n := by
      exact_mod_cast Nat.le_of_dvd hn hprod
    have hyk : y ^ P.card ≤ ((∏ p ∈ P, p : ℕ) : ℝ) := by
      rw [Nat.cast_prod, ← prod_const]
      apply Finset.prod_le_prod₀ (fun _ _ => hy0.le)
      intro p hp
      exact (mem_filter.mp hp).2.le
    have hk : P.card ≤ 10 := by
      by_contra hk
      push_neg at hk
      have : y ^ (11 : ℕ) ≤ y ^ P.card := pow_le_pow_right₀ (by linarith) hk
      have h11 : y ^ (11 : ℕ) = x * y := by rw [← hy10]; ring
      nlinarith
    have hk' : (P.card : ℝ) ^ 3 ≤ 1000 := by
      have : (P.card : ℝ) ≤ 10 := by exact_mod_cast hk
      have h0 : (0 : ℝ) ≤ P.card := by positivity
      calc (P.card : ℝ) ^ 3 ≤ 10 ^ 3 := pow_le_pow_left₀ h0 this 3
        _ = 1000 := by norm_num
    unfold Task361.harmanMajorant
    have := edge_rough_le_one n (x ^ (1 / 4 : ℝ))
    linarith

/-- LEAF: MMS page 12 second paragraph, the simple sieve upper bound itself, HARD.
Integers in a subinterval of length eps x to the theta of x minus x to the theta over 3,
x plus x to the theta, in a class c modulo W coprime to W, and free of primes below
x to the 1/10, number O of eps x to the theta over phi W log x, uniformly in eps.
This is the Selberg or Brun upper bound sieve with sifting range w to x to the 1/10,
sieve level a small power of x, together with the Mertens product estimate. -/
theorem edge_rough_sieve (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ c : ℕ, Nat.Coprime c (wheel x) → ∀ a : ℝ, x - x ^ θ / 3 ≤ a →
        a + ε * x ^ θ ≤ x + x ^ θ →
        ∑ n ∈ (ints a (a + ε * x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
            Task361.roughIndicator n (x ^ (1 / 10 : ℝ)) ≤
          C * ε * x ^ θ / ((wheel x).totient * Real.log x) := by
  sorry

/-- The edge sieve bound of MMS page 12 from the LEAF above and the proved pointwise bound.
CONDITIONAL ON edge_rough_sieve. -/
theorem edge_sieve_upper_of_leaves (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ c : ℕ, Nat.Coprime c (wheel x) →
        ∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
            Task361.harmanMajorant x n * (1 - edgeCutoff ε θ x n) ≤
          C * ε * x ^ θ / ((wheel x).totient * Real.log x) := by
  obtain ⟨XA, hA⟩ := harmanMajorant_le_rough
  obtain ⟨C, hC, hB⟩ := edge_rough_sieve θ hθ hθ1
  refine ⟨2002 * C, by positivity, fun ε hε hε1 => ?_⟩
  obtain ⟨XB, hXB⟩ := hB ε hε hε1
  refine ⟨max (max XA XB) 1, fun x hx c hc => ?_⟩
  have hxA : XA ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxB : XB ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have hxθ : 0 < x ^ θ := Real.rpow_pos_of_pos hx0 _
  have hxθx : x ^ θ ≤ x := by
    calc x ^ θ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hθ1.le
      _ = x := Real.rpow_one x
  set δ := ε * x ^ θ with hδ
  have hδ0 : 0 < δ := mul_pos hε hxθ
  have hδ1 : δ ≤ x ^ θ := by
    rw [hδ]; nlinarith
  set S := (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]) with hS
  set ρ := fun n : ℕ => Task361.roughIndicator n (x ^ (1 / 10 : ℝ)) with hρ
  have hmem : ∀ n ∈ S, x - x ^ θ / 3 ≤ n ∧ (n : ℝ) ≤ x + x ^ θ := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := mem_Icc.mp (mem_filter.mp hn).1
    exact ⟨(Nat.le_ceil _).trans (by exact_mod_cast hlo),
      (show (n : ℝ) ≤ (⌊x + x ^ θ⌋₊ : ℝ) by exact_mod_cast hhi).trans
        (Nat.floor_le (by linarith))⟩
  set T₁ := (ints (x - x ^ θ / 3) (x - x ^ θ / 3 + δ)).filter
    (fun n => n ≡ c [MOD wheel x]) with hT₁
  set T₂ := (ints (x + x ^ θ - δ) (x + x ^ θ - δ + δ)).filter
    (fun n => n ≡ c [MOD wheel x]) with hT₂
  have hB₁ := hXB x hxB c hc (x - x ^ θ / 3) le_rfl (by linarith)
  have hB₂ := hXB x hxB c hc (x + x ^ θ - δ) (by linarith) (by linarith)
  have hsub₁ : S.filter (fun n : ℕ => (n : ℝ) < x - x ^ θ / 3 + δ) ⊆ T₁ := by
    intro n hn
    obtain ⟨hnS, hn1⟩ := mem_filter.mp hn
    obtain ⟨hnI, hnc⟩ := mem_filter.mp hnS
    refine mem_filter.mpr ⟨?_, hnc⟩
    obtain ⟨hlo, -⟩ := mem_Icc.mp hnI
    exact mem_Icc.mpr ⟨hlo, Nat.le_floor hn1.le⟩
  have hsub₂ : S.filter (fun n : ℕ => x + x ^ θ - δ < (n : ℝ)) ⊆ T₂ := by
    intro n hn
    obtain ⟨hnS, hn1⟩ := mem_filter.mp hn
    obtain ⟨hnI, hnc⟩ := mem_filter.mp hnS
    refine mem_filter.mpr ⟨?_, hnc⟩
    obtain ⟨-, hhi⟩ := mem_Icc.mp hnI
    refine mem_Icc.mpr ⟨Nat.ceil_le.mpr hn1.le, ?_⟩
    simpa using hhi
  have hρ0 : ∀ n, 0 ≤ ρ n := fun n => Task361.roughIndicator_nonneg _ _
  have hpt : ∀ n ∈ S, Task361.harmanMajorant x n * (1 - edgeCutoff ε θ x n) ≤
      1001 * ((if (n : ℝ) < x - x ^ θ / 3 + δ then ρ n else 0) +
        (if x + x ^ θ - δ < (n : ℝ) then ρ n else 0)) := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := hmem n hn
    have hn0 : 0 < n := by
      have : (0 : ℝ) < n := by linarith
      exact_mod_cast this
    have hA' := hA x hxA n hn0 (by linarith)
    have hg0 := edgeCutoff_nonneg ε θ x n
    have hg1 := edgeCutoff_le_one ε θ x n
    have hM0 := Task361.harmanMajorant_nonneg x n
    have hρn := hρ0 n
    split_ifs with h1 h2 h2
    · nlinarith
    · nlinarith
    · nlinarith
    · push_neg at h1 h2
      have e1 : 1 ≤ ((n : ℝ) - (x - x ^ θ / 3)) / (ε * x ^ θ) :=
        (one_le_div hδ0).mpr (by linarith)
      have e2 : 1 ≤ (x + x ^ θ - (n : ℝ)) / (ε * x ^ θ) :=
        (one_le_div hδ0).mpr (by linarith)
      have hg : edgeCutoff ε θ x n = 1 := by
        unfold edgeCutoff
        rw [Real.smoothTransition.one_of_one_le e1, Real.smoothTransition.one_of_one_le e2]
        norm_num
      rw [hg]; norm_num
  have hsum : ∑ n ∈ S, Task361.harmanMajorant x n * (1 - edgeCutoff ε θ x n) ≤
      1001 * (∑ n ∈ T₁, ρ n + ∑ n ∈ T₂, ρ n) := by
    refine (sum_le_sum hpt).trans ?_
    rw [← mul_sum, sum_add_distrib, ← sum_filter, ← sum_filter]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact add_le_add (sum_le_sum_of_subset_of_nonneg hsub₁ (fun n _ _ => hρ0 n))
      (sum_le_sum_of_subset_of_nonneg hsub₂ (fun n _ _ => hρ0 n))
  have hB₂' : ∑ n ∈ T₂, ρ n ≤ C * ε * x ^ θ / ((wheel x).totient * Real.log x) := by
    exact hB₂
  have hB₁' : ∑ n ∈ T₁, ρ n ≤ C * ε * x ^ θ / ((wheel x).totient * Real.log x) := by
    exact hB₁
  calc _ ≤ 1001 * (∑ n ∈ T₁, ρ n + ∑ n ∈ T₂, ρ n) := hsum
    _ ≤ 1001 * (C * ε * x ^ θ / ((wheel x).totient * Real.log x) +
          C * ε * x ^ θ / ((wheel x).totient * Real.log x)) := by gcongr
    _ = 2002 * C * ε * x ^ θ / ((wheel x).totient * Real.log x) := by ring

end LeanLab.Ternary.MMS.Task379
