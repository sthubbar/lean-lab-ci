import LeanLab.Halupczok2012.UniformCRT398
import LeanLab.Halupczok2012.UniformTails398

/-!
Halupczok page 344, the main term estimate uniformly over residue choices.
The U1457 proof is reused with the uniform CRT and singular series tails.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.UniformMain398

open Finset
open scoped Classical

/-- Page 344, the weighted one prime main term uniformly over residue choices.
Only Theorem3 is an analytic hypothesis. -/
theorem mainTerm (h3 : Theorem3) :
  ∀ A ε ε1 ε2 : ℝ, 0 < A → 0 < ε → 0 < ε1 → 0 < ε2 → ∃ B : ℝ, 0 < B ∧
    ∀ c : Fin 7 → ℝ, (∀ i, 0 < c i) → ∃ C Y0 : ℝ,
    ∀ (n : ℕ) (X1 Y1 X2 Y2 Q : ℝ), Y0 ≤ Y1 → Y0 ≤ Y2 →
      Thm2Hyp ε ε1 ε2 B c n X1 Y1 X2 Y2 Q → ∀ a : ℕ → ℤ,
      ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => Int.gcd (a q) q = 1),
        |mainSum n X1 Y1 q (a q) - T n q (a q) * Y1| ≤ C * Y1 * Real.log Y2 ^ (-A) := by
  classical
  intro A ε ε1 ε2 hA hε hε1 hε2
  obtain ⟨D, hD, hS⟩ := UniformTails398.singular_approximation A ε ε1 ε2 hA hε hε1 hε2
  set A' := A + 3 * D with hA'
  have hA'0 : 0 < A' := by rw [hA']; linarith
  obtain ⟨B3, hB3, h3'⟩ := UniformCRT398.crtStep h3 A' ε1 hA'0 hε1
  refine ⟨B3 + D, by linarith, fun c hc => ?_⟩
  have c0 := hc 0; have c2 := hc 2; have c3 := hc 3; have c6 := hc 6
  obtain ⟨C1, K, Y01, hS'⟩ := hS (B3 + D) (by linarith) c hc
  set kX := 2 * |Real.log (c 3 / c 0)| + 2 with hkX
  set kY := 3 + 3 * |Real.log (c 2)| with hkY
  have hkX0 : 0 < kX := by rw [hkX]; positivity
  have hkY0 : 0 < kY := by rw [hkY]; positivity
  obtain ⟨C3, Y03, hcrt⟩ := h3' (c 0) (c 6 * kX ^ B3) c0 (by positivity)
  refine ⟨2 * C1 + |K * C3| * kY ^ A', max Y01 (max Y03 (Real.exp 1)), ?_⟩
  intro n X1 Y1 X2 Y2 Q hY1 hY2 hH a
  have hY01 : Y01 ≤ Y1 := le_trans (le_max_left _ _) hY1
  have hY01' : Y01 ≤ Y2 := le_trans (le_max_left _ _) hY2
  have hY03 : Y03 ≤ Y1 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hY1
  have hYe1 : Real.exp 1 ≤ Y1 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hY1
  have hYe2 : Real.exp 1 ≤ Y2 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hY2
  obtain ⟨Z, g, hZ, hcard, hper, hbd, htail, heul⟩ := hS' n X1 Y1 X2 Y2 Q hY01 hY01' hH a
  obtain ⟨hn, hYX1, h0, hYX2, h1, h2, h3, hD0, hD1, hD2, hQ1, hQ2⟩ := hH
  have he : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hY1pos : 0 < Y1 := by linarith
  have hY2pos : 0 < Y2 := by linarith
  have hL1 : 1 ≤ Real.log Y2 := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hYe2
  have hl1 : 1 ≤ Real.log Y1 := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hYe1
  have hL0 : 0 < Real.log Y2 := by linarith
  have hX1 : 1 ≤ X1 := by linarith
  have hX1pos : 0 < X1 := by linarith
  have hn' : X1 + Y1 ≤ n := by linarith
  -- `log X₁ ≤ kX L`
  have hlogX : Real.log X1 ≤ kX * Real.log Y2 := by
    have hsq := le_sq_of_rpow c0 hX1 (by linarith) h0
    have hb : X1 ≤ (c 3 / c 0 * Y2) ^ 2 := by
      refine hsq.trans ?_
      apply pow_le_pow_left₀ (by positivity)
      rw [div_le_iff₀ c0]
      calc Y1 ≤ c 3 * Y2 := h3
        _ = c 3 / c 0 * Y2 * c 0 := by field_simp
    have h := Real.log_le_log hX1pos hb
    rw [Real.log_pow, Real.log_mul (by positivity) hY2pos.ne'] at h
    have := le_abs_self (Real.log (c 3 / c 0))
    have : |Real.log (c 3 / c 0)| ≤ |Real.log (c 3 / c 0)| * Real.log Y2 :=
      le_mul_of_one_le_right (abs_nonneg _) hL1
    rw [hkX]; push_cast at h; linarith
  -- `L ≤ kY log Y₁`
  have hlogY : Real.log Y2 ≤ kY * Real.log Y1 := by
    have hpos : 0 < c 2 * Y2 ^ (1 / 3 + ε) := by positivity
    have h := Real.log_le_log hpos h2
    rw [Real.log_mul c2.ne' (by positivity), Real.log_rpow hY2pos] at h
    have := neg_abs_le (Real.log (c 2))
    have : |Real.log (c 2)| ≤ |Real.log (c 2)| * Real.log Y1 :=
      le_mul_of_one_le_right (abs_nonneg _) hl1
    have hεL : 0 ≤ ε * Real.log Y2 := mul_nonneg hε.le hL0.le
    have : (1 / 3) * Real.log Y2 ≤ (1 / 3 + ε) * Real.log Y2 := by linarith
    rw [hkY]; linarith
  have hlogX1 : 0 < Real.log X1 := by
    have : Real.log Y1 ≤ Real.log X1 := Real.log_le_log hY1pos hYX1
    linarith
  -- the moduli bound of Theorem 3
  have hQs : ∀ s ∈ Z, Q * s ≤ c 6 * kX ^ B3 * Y1 * X1 ^ (-(1 / 2) : ℝ) * Real.log X1 ^ (-B3) := by
    intro s hs
    obtain ⟨-, -, hsL⟩ := hZ s hs
    have hQ0 : 0 ≤ Q := by linarith
    have hP : 0 ≤ c 6 * Y1 * X1 ^ (-(1 / 2) : ℝ) := by positivity
    have e1 : Real.log Y2 ^ (-(B3 + D)) * Real.log Y2 ^ D = Real.log Y2 ^ (-B3) := by
      rw [← Real.rpow_add hL0]; congr 1; ring
    have hlb := rpow_neg_le_of_le hlogX1 hkX0 hlogX hB3.le
    calc Q * s ≤ (c 6 * Y1 * X1 ^ (-(1 / 2) : ℝ) * Real.log Y2 ^ (-(B3 + D))) *
          Real.log Y2 ^ D := mul_le_mul hQ2 hsL (Nat.cast_nonneg _) (by positivity)
      _ = c 6 * Y1 * X1 ^ (-(1 / 2) : ℝ) * Real.log Y2 ^ (-B3) := by rw [mul_assoc, e1]
      _ ≤ c 6 * Y1 * X1 ^ (-(1 / 2) : ℝ) * (kX ^ B3 * Real.log X1 ^ (-B3)) :=
          mul_le_mul_of_nonneg_left hlb hP
      _ = _ := by ring
  -- one modulus
  set l1 := Real.log Y1 ^ (-A') with hl1def
  set LD := Real.log Y2 ^ D with hLD
  have hLD0 : 0 ≤ LD := by positivity
  have hl10 : 0 ≤ l1 := by positivity
  have hl1le : l1 ≤ kY ^ A' * Real.log Y2 ^ (-A') :=
    rpow_neg_le_of_le hL0 hkY0 hlogY hA'0.le
  have hones : ∀ s ∈ Z,
      ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => Int.gcd (a q) (q : ℤ) = 1),
        |∑ p ∈ P1 n X1 Y1 q (a q), Real.log p * g s p -
          Y1 / (Nat.totient (Nat.lcm q s) : ℝ) * ∑ b ∈ crtG (a q) q s, g s b| ≤
        LD ^ 2 * (|K * C3| * Y1 * (kY ^ A' * Real.log Y2 ^ (-A'))) := by
    intro s hs
    obtain ⟨hs0, hsX, hsL⟩ := hZ s hs
    have h := hcrt n s X1 Y1 Q K a (g s) hY03 hYX1 h0 (hQs s hs) hs0 hsX hn' (hper s hs)
      (hbd s hs)
    have hab : K * C3 * Y1 * l1 ≤ |K * C3| * Y1 * l1 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hY1pos.le) hl10
    have hs2 : (s : ℝ) ^ 2 ≤ LD ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hsL 2
    calc _ ≤ (s : ℝ) ^ 2 * K * C3 * Y1 * l1 := h
      _ = (s : ℝ) ^ 2 * (K * C3 * Y1 * l1) := by ring
      _ ≤ (s : ℝ) ^ 2 * (|K * C3| * Y1 * l1) :=
          mul_le_mul_of_nonneg_left hab (sq_nonneg _)
      _ ≤ LD ^ 2 * (|K * C3| * Y1 * l1) :=
          mul_le_mul_of_nonneg_right hs2 (by positivity)
      _ ≤ LD ^ 2 * (|K * C3| * Y1 * (kY ^ A' * Real.log Y2 ^ (-A'))) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_left hl1le (by positivity)
  -- all moduli
  set Iq := (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => Int.gcd (a q) (q : ℤ) = 1) with hIq
  have hmid : ∑ q ∈ Iq, ∑ s ∈ Z, |∑ p ∈ P1 n X1 Y1 q (a q), Real.log p * g s p -
        Y1 / (Nat.totient (Nat.lcm q s) : ℝ) * ∑ b ∈ crtG (a q) q s, g s b| ≤
      |K * C3| * kY ^ A' * Y1 * Real.log Y2 ^ (-A) := by
    rw [sum_comm]
    have hP0 : 0 ≤ LD ^ 2 * (|K * C3| * Y1 * (kY ^ A' * Real.log Y2 ^ (-A'))) := by positivity
    calc _ ≤ ∑ s ∈ Z, LD ^ 2 * (|K * C3| * Y1 * (kY ^ A' * Real.log Y2 ^ (-A'))) :=
          sum_le_sum hones
      _ = (Z.card : ℝ) * (LD ^ 2 * (|K * C3| * Y1 * (kY ^ A' * Real.log Y2 ^ (-A')))) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ LD * (LD ^ 2 * (|K * C3| * Y1 * (kY ^ A' * Real.log Y2 ^ (-A')))) :=
          mul_le_mul_of_nonneg_right hcard hP0
      _ = |K * C3| * kY ^ A' * Y1 * (LD * LD ^ 2 * Real.log Y2 ^ (-(A + 3 * D))) := by
          rw [hA']; ring
      _ = _ := by rw [hLD, rpow_three_D hL0]
  -- the tail over primes
  have htailP : ∀ q, |∑ p ∈ P1 n X1 Y1 q (a q), Real.log p * (S (n - p) - ∑ s ∈ Z, g s p)| ≤
      ∑ m ∈ W1 n X1 Y1 q (a q), Real.log m * |S (n - m) - ∑ s ∈ Z, g s m| := by
    intro q
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hnn : ∀ m : ℕ, 0 ≤ Real.log m * |S (n - m) - ∑ s ∈ Z, g s m| :=
      fun m => mul_nonneg (Real.log_natCast_nonneg m) (abs_nonneg _)
    calc _ = ∑ p ∈ P1 n X1 Y1 q (a q), Real.log p * |S (n - p) - ∑ s ∈ Z, g s p| := by
          apply sum_congr rfl; intro p _
          rw [abs_mul, abs_of_nonneg (Real.log_natCast_nonneg p)]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (P1_subset_W1 n X1 Y1 q (a q)) (fun m _ _ => hnn m)
  -- assemble
  have hper_q : ∀ q ∈ Iq, |mainSum n X1 Y1 q (a q) - T n q (a q) * Y1| ≤
      ∑ m ∈ W1 n X1 Y1 q (a q), Real.log m * |S (n - m) - ∑ s ∈ Z, g s m| +
      ∑ s ∈ Z, |∑ p ∈ P1 n X1 Y1 q (a q), Real.log p * g s p -
        Y1 / (Nat.totient (Nat.lcm q s) : ℝ) * ∑ b ∈ crtG (a q) q s, g s b| +
      |∑ s ∈ Z, Y1 / (Nat.totient (Nat.lcm q s) : ℝ) * ∑ b ∈ crtG (a q) q s, g s b -
        T n q (a q) * Y1| := by
    intro q _
    rw [mainSum_split n X1 Y1 q (a q) Z g]
    refine (abs_add_le _ _).trans ?_
    refine add_le_add ((abs_add_le _ _).trans (add_le_add (htailP q) ?_)) le_rfl
    exact abs_sum_le_sum_abs _ _
  calc _ ≤ ∑ q ∈ Iq, (∑ m ∈ W1 n X1 Y1 q (a q), Real.log m * |S (n - m) - ∑ s ∈ Z, g s m| +
      ∑ s ∈ Z, |∑ p ∈ P1 n X1 Y1 q (a q), Real.log p * g s p -
        Y1 / (Nat.totient (Nat.lcm q s) : ℝ) * ∑ b ∈ crtG (a q) q s, g s b| +
      |∑ s ∈ Z, Y1 / (Nat.totient (Nat.lcm q s) : ℝ) * ∑ b ∈ crtG (a q) q s, g s b -
        T n q (a q) * Y1|) := sum_le_sum hper_q
    _ = _ := by rw [sum_add_distrib, sum_add_distrib]
    _ ≤ C1 * Y1 * Real.log Y2 ^ (-A) + |K * C3| * kY ^ A' * Y1 * Real.log Y2 ^ (-A) +
          C1 * Y1 * Real.log Y2 ^ (-A) := add_le_add (add_le_add htail hmid) heul
    _ = _ := by ring

end LeanLab.Halupczok2012.UniformMain398
