/-
P0080 Hathi 2021, arXiv 2109.13174v3, page 10, the product m1.
The integer cutoff N corresponds to the floor of x divided by 2 in the paper.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Hathi2021.Step115

open Finset Real

namespace LeanLab.Hathi2021.Products115

/-- Page 10, m1 at integer cutoff N, with e running from 1 through N. -/
def m1At (N : ℕ) : ℕ := ∏ e ∈ range N, (2 ^ (2 * (e + 1)) - 1)

/-- Page 10, the elementary product bound before applying the function u. -/
theorem m1At_upper (N : ℕ) : m1At N ≤ 2 ^ (N * (N + 1)) := by
  induction N with
  | zero => simp [m1At]
  | succ N ih =>
    have hs : m1At (N + 1) = m1At N * (2 ^ (2 * (N + 1)) - 1) := by
      simp only [m1At, Finset.prod_range_succ]
    rw [hs]
    calc
      m1At N * (2 ^ (2 * (N + 1)) - 1) ≤
          2 ^ (N * (N + 1)) * 2 ^ (2 * (N + 1)) :=
        Nat.mul_le_mul ih (Nat.sub_le _ _)
      _ = 2 ^ ((N + 1) * (N + 1 + 1)) := by
        rw [← pow_add]
        congr 1
        ring

/-- Page 10, adding factors cannot decrease the product m1. -/
theorem m1At_mono : Monotone m1At := by
  apply monotone_nat_of_le_succ
  intro N
  have hp : 2 ≤ 2 ^ (2 * (N + 1)) := by
    calc
      2 = 2 ^ 1 := rfl
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hf : 1 ≤ 2 ^ (2 * (N + 1)) - 1 := by omega
  have h := Nat.mul_le_mul_left (m1At N) hf
  simpa only [mul_one, m1At, Finset.prod_range_succ] using h


/-- Page 10, m1 is at least 30 once the cutoff is at least 2. -/
theorem m1At_ge_30 (N : ℕ) (hN : 2 ≤ N) : 30 ≤ m1At N := by
  have h2 : 30 ≤ m1At 2 := by norm_num [m1At, Finset.prod_range_succ]
  exact h2.trans (m1At_mono hN)


/-- Page 10, every factor of m1 is odd. -/
theorem m1At_odd (N : ℕ) : Odd (m1At N) := by
  induction N with
  | zero => simp [m1At]
  | succ N ih =>
    have he : Even (2 ^ (2 * (N + 1)) : ℕ) :=
      (by decide : Even (2 : ℕ)).pow_of_ne_zero (by omega)
    have ho : Odd (2 ^ (2 * (N + 1)) - 1 : ℕ) := by
      rw [Nat.odd_sub' Nat.one_le_two_pow]
      exact ⟨fun _ => he, fun _ => by decide⟩
    simpa only [m1At, Finset.prod_range_succ] using ih.mul ho

/-- Page 10, the size bound at the 1.06 exponent, including the floor cutoff. -/
theorem two_m1At_floor_le (x : ℝ) (hx : 37 ≤ x) :
    ((2 * m1At ⌊x / 2⌋₊ : ℕ) : ℝ) ≤
      (2 : ℝ) ^ ((106 / 100 : ℝ) * (x / 2) ^ 2) := by
  let n := ⌊x / 2⌋₊
  have hNat : 2 * m1At n ≤ 2 ^ (n * (n + 1) + 1) := by
    calc
      2 * m1At n ≤ 2 ^ 1 * 2 ^ (n * (n + 1)) := by
        simpa only [pow_one] using Nat.mul_le_mul_left 2 (m1At_upper n)
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hcast : ((2 * m1At n : ℕ) : ℝ) ≤ (2 : ℝ) ^ (n * (n + 1) + 1) := by
    exact_mod_cast hNat
  have he : ((n * (n + 1) + 1 : ℕ) : ℝ) ≤ 106 / 100 * (x / 2) ^ 2 := by
    have hn : (n : ℝ) ≤ x / 2 := Nat.floor_le (by linarith)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hm : (n : ℝ) * ((n : ℝ) + 1) ≤ (x / 2) * (x / 2 + 1) :=
      mul_le_mul hn (by linarith) (by positivity) (by linarith)
    have ht : 0 ≤ x / 2 - 37 / 2 := by linarith
    have hq : 0 ≤ (6 / 100 : ℝ) * (x / 2 - 37 / 2) ^ 2 +
        (122 / 100) * (x / 2 - 37 / 2) + 1035 / 1000 := by positivity
    push_cast
    nlinarith only [hm, hq]
  calc
    ((2 * m1At ⌊x / 2⌋₊ : ℕ) : ℝ) ≤ (2 : ℝ) ^ (n * (n + 1) + 1) := hcast
    _ = (2 : ℝ) ^ ((n * (n + 1) + 1 : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) he

/-- Page 11, the product of the three primes excluded from m1. -/
def P : ℕ := 101 * 107 * 131

/-- Pages 10 and 11, the size bound at the 1.12 exponent with the three extra primes. -/
theorem twoP_m1At_floor_le (x : ℝ) (hx : 37 ≤ x) :
    ((2 * P * m1At ⌊x / 2⌋₊ : ℕ) : ℝ) ≤
      (2 : ℝ) ^ ((112 / 100 : ℝ) * (x / 2) ^ 2) := by
  let n := ⌊x / 2⌋₊
  have hNat : 2 * P * m1At n ≤ 2 ^ (n * (n + 1) + 22) := by
    calc
      2 * P * m1At n ≤ 2 ^ 22 * 2 ^ (n * (n + 1)) :=
        Nat.mul_le_mul (by norm_num [P]) (m1At_upper n)
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hcast : ((2 * P * m1At n : ℕ) : ℝ) ≤ (2 : ℝ) ^ (n * (n + 1) + 22) := by
    exact_mod_cast hNat
  have he : ((n * (n + 1) + 22 : ℕ) : ℝ) ≤ 112 / 100 * (x / 2) ^ 2 := by
    have hn : (n : ℝ) ≤ x / 2 := Nat.floor_le (by linarith)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hm : (n : ℝ) * ((n : ℝ) + 1) ≤ (x / 2) * (x / 2 + 1) :=
      mul_le_mul hn (by linarith) (by positivity) (by linarith)
    have ht : 0 ≤ x / 2 - 37 / 2 := by linarith
    have hq : 0 ≤ (12 / 100 : ℝ) * (x / 2 - 37 / 2) ^ 2 +
        (344 / 100) * (x / 2 - 37 / 2) + 57 / 100 := by positivity
    push_cast
    nlinarith only [hm, hq]
  calc
    ((2 * P * m1At ⌊x / 2⌋₊ : ℕ) : ℝ) ≤ (2 : ℝ) ^ (n * (n + 1) + 22) := hcast
    _ = (2 : ℝ) ^ ((n * (n + 1) + 22 : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) he

/-- Page 10, none of the three excluded primes has order at most 99. -/
theorem excluded_pow_ne_one :
    (∀ k < 100, 0 < k → (2 : ZMod 101) ^ k ≠ 1) ∧
    (∀ k < 100, 0 < k → (2 : ZMod 107) ^ k ≠ 1) ∧
    (∀ k < 100, 0 < k → (2 : ZMod 131) ^ k ≠ 1) := by
  decide +kernel


/-- Page 10, the three primes do not divide m1 when the cutoff is at most 49. -/
theorem excluded_not_dvd (N : ℕ) (hN : N ≤ 49) :
    ¬ 101 ∣ m1At N ∧ ¬ 107 ∣ m1At N ∧ ¬ 131 ∣ m1At N := by
  have helper (p : ℕ) (hp : p.Prime)
      (hord : ∀ k < 100, 0 < k → (2 : ZMod p) ^ k ≠ 1) : ¬ p ∣ m1At N := by
    intro hdiv
    change p ∣ ∏ e ∈ range N, (2 ^ (2 * (e + 1)) - 1) at hdiv
    obtain ⟨e, he, hediv⟩ := ((Nat.prime_iff.mp hp).dvd_finsetProd_iff
      (fun e : ℕ => 2 ^ (2 * (e + 1)) - 1)).mp hdiv
    have heN : e < N := Finset.mem_range.mp he
    have hz : (((2 ^ (2 * (e + 1)) - 1 : ℕ) : ZMod p)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hediv
    rw [Nat.cast_sub Nat.one_le_two_pow] at hz
    push_cast at hz
    have hpow : (2 : ZMod p) ^ (2 * (e + 1)) = 1 := sub_eq_zero.mp hz
    exact hord _ (by omega) (by omega) hpow
  exact ⟨helper 101 (by decide) excluded_pow_ne_one.1,
    helper 107 (by decide) excluded_pow_ne_one.2.1,
    helper 131 (by decide) excluded_pow_ne_one.2.2⟩

/-- Display 3.6, page 10. CONDITIONAL ON the cited Rosser and Schoenfeld
bound at the integer 2m1. All scalar and product steps are proved here. -/
theorem m1_totient_of_rs (x : ℝ) (hx : 37 ≤ x)
    (hRS : ((2 * m1At ⌊x / 2⌋₊ : ℕ) : ℝ) / Nat.totient (2 * m1At ⌊x / 2⌋₊) ≤
      Step115.u ((2 * m1At ⌊x / 2⌋₊ : ℕ) : ℝ)) :
    (m1At ⌊x / 2⌋₊ : ℝ) / Nat.totient (m1At ⌊x / 2⌋₊) <
      exp eulerMascheroniConstant * log (x / 2) := by
  let n := ⌊x / 2⌋₊
  have hN : 2 ≤ n := Nat.le_floor (by linarith : (2 : ℝ) ≤ x / 2)
  have hDnat : 30 ≤ 2 * m1At n := by have h := m1At_ge_30 n hN; omega
  have hD : (30 : ℝ) ≤ ((2 * m1At n : ℕ) : ℝ) := by exact_mod_cast hDnat
  have hs := two_m1At_floor_le x hx
  have hu : Step115.u ((2 * m1At n : ℕ) : ℝ) ≤
      Step115.u ((2 : ℝ) ^ ((106 / 100 : ℝ) * (x / 2) ^ 2)) :=
    Step115.u_strictMonoOn.monotoneOn hD (hD.trans hs) hs
  have hbound := (hRS.trans hu).trans_lt (Step115.u_step_106 x hx)
  have hphi : Nat.totient (2 * m1At n) = Nat.totient (m1At n) := by
    rw [Nat.totient_mul (m1At_odd n).coprime_two_left]
    simp
  rw [hphi] at hbound
  push_cast at hbound
  dsimp only [n] at hbound
  rw [mul_div_assoc, mul_assoc] at hbound
  exact (mul_lt_mul_iff_right₀ (by norm_num : (0 : ℝ) < 2)).mp hbound

/-- Pages 10 and 11, P is coprime to m1 on the required cutoff range. -/
theorem P_coprime_m1At (N : ℕ) (hN : N ≤ 49) : Nat.Coprime P (m1At N) := by
  obtain ⟨h101, h107, h131⟩ := excluded_not_dvd N hN
  have h₁ : Nat.Coprime 101 (m1At N) := (by decide : Nat.Prime 101).coprime_iff_not_dvd.mpr h101
  have h₂ : Nat.Coprime 107 (m1At N) := (by decide : Nat.Prime 107).coprime_iff_not_dvd.mpr h107
  have h₃ : Nat.Coprime 131 (m1At N) := (by decide : Nat.Prime 131).coprime_iff_not_dvd.mpr h131
  exact Nat.coprime_mul_iff_left.mpr ⟨Nat.coprime_mul_iff_left.mpr ⟨h₁, h₂⟩, h₃⟩

/-- Page 11, the totient of P gives the numerator of the factor c3 prime. -/
theorem totient_P : Nat.totient P = 1378000 := by
  unfold P
  rw [Nat.totient_mul (by decide : Nat.Coprime (101 * 107) 131),
    Nat.totient_mul (by decide : Nat.Coprime 101 107),
    Nat.totient_prime (by decide : Nat.Prime 101),
    Nat.totient_prime (by decide : Nat.Prime 107),
    Nat.totient_prime (by decide : Nat.Prime 131)]

/-- Display 3.7, page 11. CONDITIONAL ON the cited RS bound at 2Pm1.
The prime exclusions, product bound, and u comparison have proofs. -/
theorem m1_totient_improved_of_rs (x : ℝ) (hx : 37 ≤ x) (hx99 : x ≤ 99)
    (hRS : ((2 * P * m1At ⌊x / 2⌋₊ : ℕ) : ℝ) /
      Nat.totient (2 * P * m1At ⌊x / 2⌋₊) ≤
      Step115.u ((2 * P * m1At ⌊x / 2⌋₊ : ℕ) : ℝ)) :
    (m1At ⌊x / 2⌋₊ : ℝ) / Nat.totient (m1At ⌊x / 2⌋₊) <
      (1 - 1 / 101 : ℝ) * (1 - 1 / 107) * (1 - 1 / 131) *
        exp eulerMascheroniConstant * log (x / 2) := by
  let n := ⌊x / 2⌋₊
  have hNlo : 2 ≤ n := Nat.le_floor (by linarith : (2 : ℝ) ≤ x / 2)
  have hNhi : n ≤ 49 := by
    have hn : (n : ℝ) ≤ x / 2 := Nat.floor_le (by linarith)
    have hr : (n : ℝ) < 50 := by linarith
    have hi : n < 50 := by exact_mod_cast hr
    omega
  have hc : Nat.Coprime (2 * P) (m1At n) :=
    Nat.coprime_mul_iff_left.mpr ⟨(m1At_odd n).coprime_two_left, P_coprime_m1At n hNhi⟩
  have hphi : Nat.totient (2 * P * m1At n) = 1378000 * Nat.totient (m1At n) := by
    rw [Nat.totient_mul hc, Nat.totient_mul (by decide : Nat.Coprime 2 P),
      Nat.totient_two, totient_P]
  have hDnat : 30 ≤ 2 * P * m1At n := by
    have hm := m1At_ge_30 n hNlo
    norm_num [P]
    omega
  have hD : (30 : ℝ) ≤ ((2 * P * m1At n : ℕ) : ℝ) := by exact_mod_cast hDnat
  have hs := twoP_m1At_floor_le x hx
  have hu : Step115.u ((2 * P * m1At n : ℕ) : ℝ) ≤
      Step115.u ((2 : ℝ) ^ ((112 / 100 : ℝ) * (x / 2) ^ 2)) :=
    Step115.u_strictMonoOn.monotoneOn hD (hD.trans hs) hs
  have hbound := (hRS.trans hu).trans_lt (Step115.u_step_112 x hx)
  rw [hphi] at hbound
  push_cast at hbound
  have hpos : 0 < m1At n := by have hm := m1At_ge_30 n hNlo; omega
  have hphiPos : (0 : ℝ) < Nat.totient (m1At n) := by
    exact_mod_cast Nat.totient_pos.mpr hpos
  dsimp only [n] at hbound hphiPos
  have hcross := (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 1378000) hphiPos)).mp hbound
  rw [div_lt_iff₀ hphiPos]
  norm_num [P] at hcross ⊢
  nlinarith only [hcross]

end LeanLab.Hathi2021.Products115
