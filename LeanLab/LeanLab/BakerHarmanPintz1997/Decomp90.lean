/-
P0069, Lemma 6, page 21. CODEX task90.
Both named character sum branches are proved from ported derivative tests.
The final assembly has exactly the sealed Lemma6 proposition.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Decomp1518
import LeanLab.BakerHarmanPintz1997.Parameter219
import LeanLab.BakerHarmanPintz1997.Progression219
import LeanLab.BakerHarmanPintz1997.LowFrequency219

namespace LeanLab.BakerHarmanPintz1997.Decomp90
open Finset
attribute [local instance] Classical.propDecidable

/-- LEAF. Page 21, the partial summation step before 3.35.
A nonnegative decreasing weight costs only its initial value when all partial sums are bounded. -/
theorem abel_bound (w : ℕ → ℝ) (z : ℕ → ℂ) (n : ℕ) {B : ℝ}
    (hB : 0 ≤ B) (hw : ∀ k, 0 ≤ w k) (hanti : Antitone w)
    (hsum : ∀ k, k ≤ n → ‖∑ i ∈ range k, z i‖ ≤ B) :
    ‖∑ i ∈ range n, w i • z i‖ ≤ w 0 * B := by
  cases n with
  | zero => simpa using mul_nonneg (hw 0) hB
  | succ n =>
    rw [sum_range_by_parts w z (n + 1)]
    simp only [Nat.add_sub_cancel]
    calc
      _ ≤ ‖w n • ∑ i ∈ range (n + 1), z i‖ +
          ‖∑ i ∈ range n, (w (i + 1) - w i) • ∑ j ∈ range (i + 1), z j‖ := norm_sub_le _ _
      _ ≤ w n * B + ∑ i ∈ range n, ‖(w (i + 1) - w i) • ∑ j ∈ range (i + 1), z j‖ := by
        apply add_le_add
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw n)]
          exact mul_le_mul_of_nonneg_left (hsum (n + 1) (le_refl _)) (hw n)
        · exact norm_sum_le _ _
      _ ≤ w n * B + ∑ i ∈ range n, (w i - w (i + 1)) * B := by
        apply add_le_add le_rfl
        apply sum_le_sum
        intro i hi
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hanti (Nat.le_succ i))), neg_sub]
        exact mul_le_mul_of_nonneg_left (hsum (i + 1) (by have := mem_range.mp hi; omega)) (sub_nonneg.mpr (hanti (Nat.le_succ i)))
      _ = w 0 * B := by rw [← sum_mul, sum_range_sub']; ring

/-- LEAF. Page 21, partial summation on a fixed residue class.
The inverse square root weight converts exponent 1 - 2η to 1/2 - 2η. -/
theorem weighted_progression {N N1 η C t : ℝ} {q : ℕ} [NeZero q]
    (hN : 0 < N) (hNN1 : N ≤ N1) (hN1 : N1 ≤ 2 * N) (hC : 0 ≤ C)
    (r : ZMod q)
    (hsum : ∀ u : ℝ, N ≤ u → u ≤ 2 * N →
      ‖∑ n ∈ (Ioc ⌊N⌋₊ ⌊u⌋₊).filter (fun n : ℕ => (n : ZMod q) = r),
        (n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ≤ C * N ^ (1 - 2 * η)) :
    ‖∑ n ∈ (Ioc ⌊N⌋₊ ⌊N1⌋₊).filter (fun n : ℕ => (n : ZMod q) = r),
      (n : ℂ) ^ (-(half t))‖ ≤ C * N ^ (1 / 2 - 2 * η) := by
  let a : ℕ := ⌊N⌋₊
  let b : ℕ := ⌊N1⌋₊
  have hab : a ≤ b := Nat.floor_mono hNN1
  let f : ℕ → ℂ := fun n => if (n : ZMod q) = r then (n : ℂ) ^ (-(t : ℂ) * Complex.I) else 0
  let w : ℕ → ℝ := fun i => ((a + 1 + i : ℕ) : ℝ) ^ (-1 / 2 : ℝ)
  have hshift : ∀ (v : ℕ → ℂ) (k : ℕ),
      (∑ i ∈ range k, v (a + 1 + i)) = ∑ n ∈ Ioc a (a + k), v n := by
    intro v k
    rw [← Ico_add_one_add_one_eq_Ioc, sum_Ico_eq_sum_range]
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hB : 0 ≤ C * N ^ (1 - 2 * η) := mul_nonneg hC (Real.rpow_nonneg hN.le _)
  have hpartial : ∀ k, k ≤ b - a → ‖∑ i ∈ range k, f (a + 1 + i)‖ ≤ C * N ^ (1 - 2 * η) := by
    intro k hk
    by_cases hk0 : k = 0
    · simpa [hk0] using hB
    have hNk : N ≤ ((a + k : ℕ) : ℝ) := by
      have hf := Nat.lt_floor_add_one N
      have ha : a + 1 ≤ a + k := by omega
      exact le_trans hf.le (by exact_mod_cast ha)
    have hbk : a + k ≤ b := by omega
    have hupper : ((a + k : ℕ) : ℝ) ≤ 2 * N := by
      have hf := Nat.floor_le (hN.le.trans hNN1)
      exact (show ((a + k : ℕ) : ℝ) ≤ (b : ℝ) by exact_mod_cast hbk).trans (hf.trans hN1)
    have hh := hsum ((a + k : ℕ) : ℝ) hNk hupper
    rw [Nat.floor_natCast] at hh
    rw [hshift f k]
    simpa only [a, sum_filter, f] using hh
  have hw0 : ∀ i, 0 ≤ w i := fun i => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hanti : Antitone w := by
    intro i j hij
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (by exact_mod_cast Nat.add_le_add_left hij (a + 1)) (by norm_num)
  have habel := abel_bound w (fun i => f (a + 1 + i)) (b - a) hB hw0 hanti hpartial
  have hweight : w 0 ≤ N ^ (-1 / 2 : ℝ) := by
    dsimp [w]
    exact Real.rpow_le_rpow_of_nonpos hN (by simpa [a] using (Nat.lt_floor_add_one N).le) (by norm_num)
  have hfactor : N ^ (-1 / 2 : ℝ) * (C * N ^ (1 - 2 * η)) = C * N ^ (1 / 2 - 2 * η) := by
    rw [show N ^ (-1 / 2 : ℝ) * (C * N ^ (1 - 2 * η)) =
      C * (N ^ (-1 / 2 : ℝ) * N ^ (1 - 2 * η)) by ring,
      ← Real.rpow_add hN]
    congr 2
    ring
  have hterm : ∀ n : ℕ, 0 < n →
      ((n : ℝ) ^ (-1 / 2 : ℝ)) • f n =
        if (n : ZMod q) = r then (n : ℂ) ^ (-(half t)) else 0 := by
    intro n hn
    dsimp [f]
    split_ifs
    · rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
      push_cast
      rw [← Complex.cpow_add]
      · congr 1
        unfold half
        push_cast
        ring
      · exact_mod_cast (Nat.ne_of_gt hn)
    · simp
  have hident : (∑ i ∈ range (b - a), w i • f (a + 1 + i)) =
      ∑ n ∈ (Ioc a b).filter (fun n : ℕ => (n : ZMod q) = r), (n : ℂ) ^ (-(half t)) := by
    change (∑ i ∈ range (b - a), (fun n : ℕ => ((n : ℝ) ^ (-1 / 2 : ℝ)) • f n) (a + 1 + i)) = _
    rw [hshift (fun n : ℕ => ((n : ℝ) ^ (-1 / 2 : ℝ)) • f n) (b - a), Nat.add_sub_of_le hab, sum_filter]
    apply sum_congr rfl
    intro n hn
    exact hterm n (lt_of_le_of_lt (Nat.zero_le a) (mem_Ioc.mp hn).1)
  rw [hident] at habel
  exact habel.trans ((mul_le_mul_of_nonneg_right hweight hB).trans_eq hfactor)

/-- LEAF. Page 21, summing the fixed residue class estimates.
A Dirichlet character has norm at most one on every residue class. -/
theorem character_of_progressions {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (S : Finset ℕ) (f : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ r : ZMod q, ‖∑ n ∈ S.filter (fun n : ℕ => (n : ZMod q) = r), f n‖ ≤ B) :
    ‖∑ n ∈ S, χ (n : ZMod q) * f n‖ ≤ (q : ℝ) * B := by
  rw [← sum_fiberwise S (fun n : ℕ => (n : ZMod q)) (fun n => χ (n : ZMod q) * f n)]
  have hfiber : ∀ r : ZMod q,
      (∑ n ∈ S.filter (fun n : ℕ => (n : ZMod q) = r), χ (n : ZMod q) * f n) =
        χ r * ∑ n ∈ S.filter (fun n : ℕ => (n : ZMod q) = r), f n := by
    intro r
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    rw [(mem_filter.mp hn).2]
  simp_rw [hfiber]
  calc
    _ ≤ ∑ r : ZMod q, ‖χ r * ∑ n ∈ S.filter (fun n : ℕ => (n : ZMod q) = r), f n‖ := norm_sum_le _ _
    _ ≤ ∑ _r : ZMod q, B := sum_le_sum fun r _ => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (χ.norm_le_one r) (norm_nonneg _)).trans (by simpa using h r)
    _ = (q : ℝ) * B := by simp [ZMod.card]

/-- LEAF. Page 21, absorbing the logarithmic modulus into half the power saving.
This is uniform for x at least two and N at least x^ε. -/
theorem logarithmic_absorption {ε η A : ℝ} (hε : 0 < ε) (hη : 0 < η) (hA : 0 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x N : ℝ, 2 ≤ x → x ^ ε ≤ N → L x ^ A ≤ K * N ^ η := by
  let δ : ℝ := ε * η / A
  have hδ : 0 < δ := div_pos (mul_pos hε hη) hA
  refine ⟨(1 / δ) ^ A, Real.rpow_nonneg (by positivity) _, ?_⟩
  intro x N hx hN
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hbound := Real.rpow_le_rpow hlog (Real.log_le_rpow_div hx0.le hδ) hA.le
  have hid : (x ^ δ / δ) ^ A = (1 / δ) ^ A * x ^ (ε * η) := by
    rw [div_eq_mul_inv, Real.mul_rpow (Real.rpow_nonneg hx0.le _) (inv_nonneg.mpr hδ.le),
      ← Real.rpow_mul hx0.le]
    have he : δ * A = ε * η := by dsimp [δ]; field_simp
    rw [he, one_div]
    ring
  rw [hid] at hbound
  have hpow : x ^ (ε * η) ≤ N ^ η := by
    rw [Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hx0.le _) hN hη.le
  exact hbound.trans (mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (by positivity) _))

/-- LEAF. Page 21, the final display after the derivative test.
For K at least two both terms save at least 1 divided by 4K minus 4. -/
theorem derivative_power_saving {N K C S : ℝ} (hN : 1 ≤ N) (hK : 2 ≤ K) (hC : 0 ≤ C)
    (hS : S ≤ C * (N * (N ^ (-1 / 2 : ℝ)) ^ (1 / (2 * K - 2)) +
      N ^ (1 - 2 / K + 3 / (4 * K - 4)))) :
    S ≤ 2 * C * N ^ (1 - 1 / (4 * K - 4)) := by
  have hN0 : 0 < N := by linarith
  have hK0 : 0 < K := by linarith
  have hd : 0 < 4 * K - 4 := by linarith
  have hd2 : 0 < 2 * K - 2 := by linarith
  have hexp : 1 - 2 / K + 3 / (4 * K - 4) ≤ 1 - 1 / (4 * K - 4) := by
    have hh : 4 / (4 * K - 4) ≤ 2 / K :=
      (div_le_div_iff₀ hd hK0).2 (by nlinarith)
    simp only [div_eq_mul_inv] at hh ⊢
    linarith only [hh]
  have hid : N * (N ^ (-1 / 2 : ℝ)) ^ (1 / (2 * K - 2)) = N ^ (1 - 1 / (4 * K - 4)) := by
    rw [← Real.rpow_mul hN0.le]
    calc
      _ = N ^ (1 : ℝ) * N ^ ((-1 / 2 : ℝ) * (1 / (2 * K - 2))) := by rw [Real.rpow_one]
      _ = N ^ (1 + (-1 / 2 : ℝ) * (1 / (2 * K - 2))) := (Real.rpow_add hN0 _ _).symm
      _ = _ := by congr 1; field_simp; ring
  have hpow := Real.rpow_le_rpow_of_exponent_le hN hexp
  rw [hid] at hS
  nlinarith

/-- LEAF. Page 21, the frequency split used before 3.35.
With the smaller split parameter ε/4, the second case forces absolute t at least N to the power 3/2. -/
theorem high_frequency_lower_bound {x N t ε : ℝ} (hx : 0 < x) (hN : 0 < N)
    (hlower : x ^ ε ≤ N) (hsmall : N ≤ |t| ^ (1 / 2 : ℝ) * x ^ (ε / 4)) :
    N ^ (3 / 2 : ℝ) ≤ |t| := by
  have hquarter : x ^ (ε / 4) ≤ N ^ (1 / 4 : ℝ) := by
    rw [show ε / 4 = ε * (1 / 4) by ring, Real.rpow_mul hx.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hx.le _) hlower (by norm_num)
  have hs : N ≤ |t| ^ (1 / 2 : ℝ) * N ^ (1 / 4 : ℝ) :=
    hsmall.trans (mul_le_mul_of_nonneg_left hquarter (Real.rpow_nonneg (abs_nonneg _) _))
  have hsquare := Real.rpow_le_rpow hN.le hs (by norm_num : (0 : ℝ) ≤ 2)
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg hN.le _),
    ← Real.rpow_mul (abs_nonneg t), ← Real.rpow_mul hN.le] at hsquare
  norm_num at hsquare
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hN (1 / 2 : ℝ))).mp
  rw [← Real.rpow_add hN]
  norm_num
  simpa [mul_comm] using hsquare

/-- LEAF. Page 21, choice of derivative order in the penultimate display.
A geometric sequence crosses the upper threshold at an order at least three.
The crossing stays above the threshold divided by N. -/
theorem derivative_order_crossing {N B r U : ℝ} {J : ℕ}
    (hN : 0 < N) (hB : 0 ≤ B) (hU : 0 ≤ U) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hrN : 1 / N ≤ r) (hstart : U ≤ B * r ^ 2) (hend : B * r ^ J < U) :
    ∃ j : ℕ, 3 ≤ j ∧ j ≤ J ∧ U / N ≤ B * r ^ j ∧ B * r ^ j < U := by
  let hp : ∃ j : ℕ, B * r ^ j < U := ⟨J, hend⟩
  let j := Nat.find hp
  have hj : B * r ^ j < U := Nat.find_spec hp
  have hjJ : j ≤ J := Nat.find_min' hp hend
  have hj3 : 3 ≤ j := by
    by_contra hn
    have hle : j ≤ 2 := by omega
    have hpow : r ^ 2 ≤ r ^ j := pow_le_pow_of_le_one hr0 hr1 hle
    have hh := mul_le_mul_of_nonneg_left hpow hB
    linarith
  have hj0 : 0 < j := by omega
  have hprev : U ≤ B * r ^ (j - 1) :=
    le_of_not_gt (Nat.find_min hp (by omega))
  have hproduct : U / N ≤ B * r ^ j := by
    calc
      U / N = U * (1 / N) := by ring
      _ ≤ (B * r ^ (j - 1)) * r := mul_le_mul hprev hrN (by positivity)
        (mul_nonneg hB (pow_nonneg hr0 _))
      _ = B * r ^ j := by rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hj0]
  exact ⟨j, hj3, hjJ, hproduct, hj⟩

/-- LEAF. Page 21, the quantitative hypotheses for choosing the derivative order.
If q squared is at most N to the power 1/4, the ratio q squared divided by N crosses the
required window at an order bounded in terms of the exponent R alone. -/
theorem derivative_order_of_ranges {N q t R : ℝ} {J : ℕ}
    (hN : 1 < N) (hq : 1 ≤ q) (hqsmall : q ^ 2 ≤ N ^ (1 / 4 : ℝ))
    (htlow : N ^ (3 / 2 : ℝ) ≤ t) (hthigh : t ≤ N ^ R)
    (hJ : R + 1 / 2 < 3 * (J : ℝ) / 4) :
    ∃ j : ℕ, 3 ≤ j ∧ j ≤ J ∧ N ^ (-3 / 2 : ℝ) ≤ t * (q ^ 2 / N) ^ j ∧
      t * (q ^ 2 / N) ^ j < N ^ (-1 / 2 : ℝ) := by
  have hN0 : 0 < N := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hqone : 1 ≤ q ^ 2 := by nlinarith
  have ht0 : 0 ≤ t := (Real.rpow_nonneg hN0.le _).trans htlow
  have hr0 : 0 ≤ q ^ 2 / N := by positivity
  have hrN : 1 / N ≤ q ^ 2 / N := div_le_div_of_nonneg_right hqone hN0.le
  have hrsmall : q ^ 2 / N ≤ N ^ (-3 / 4 : ℝ) := by
    apply (div_le_iff₀ hN0).2
    have hid : N ^ (-3 / 4 : ℝ) * N = N ^ (1 / 4 : ℝ) := by
      calc
        _ = N ^ (-3 / 4 : ℝ) * N ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = N ^ ((-3 / 4 : ℝ) + 1) := (Real.rpow_add hN0 _ _).symm
        _ = _ := by norm_num
    rw [hid]
    exact hqsmall
  have hr1 : q ^ 2 / N ≤ 1 := hrsmall.trans (Real.rpow_le_one_of_one_le_of_nonpos hN.le (by norm_num))
  have hstart : N ^ (-1 / 2 : ℝ) ≤ t * (q ^ 2 / N) ^ 2 := by
    have hp : (1 / N) ^ 2 ≤ (q ^ 2 / N) ^ 2 := pow_le_pow_left₀ (by positivity) hrN _
    have hh := mul_le_mul htlow hp (by positivity) ht0
    have hid : N ^ (3 / 2 : ℝ) * (1 / N) ^ 2 = N ^ (-1 / 2 : ℝ) := by
      rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le,
        ← Real.rpow_add hN0]
      norm_num
    rw [hid] at hh
    exact hh
  have hend : t * (q ^ 2 / N) ^ J < N ^ (-1 / 2 : ℝ) := by
    have hp := pow_le_pow_left₀ hr0 hrsmall J
    have hh := mul_le_mul hthigh hp (by positivity) (Real.rpow_nonneg hN0.le _)
    have hid : N ^ R * (N ^ (-3 / 4 : ℝ)) ^ J = N ^ (R - 3 * (J : ℝ) / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
      congr 1
      ring
    rw [hid] at hh
    exact hh.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hN (by linarith))
  obtain ⟨j, hj3, hjJ, hjlow, hjhigh⟩ := derivative_order_crossing hN0 ht0
    (Real.rpow_nonneg hN0.le _) hr0 hr1 hrN hstart hend
  refine ⟨j, hj3, hjJ, ?_, hjhigh⟩
  have hid : N ^ (-1 / 2 : ℝ) / N = N ^ (-3 / 2 : ℝ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hN0]
    norm_num
  rwa [hid] at hjlow

/-- LEAF. Page 21, the conclusion that bounded derivative order gives a fixed positive saving.
A bound j at most J permits one saving for all admissible derivative orders. -/
theorem derivative_saving_uniform {N C S : ℝ} {j J : ℕ}
    (hN : 1 ≤ N) (hC : 0 ≤ C) (hj : 3 ≤ j) (hjJ : j ≤ J)
    (hS : S ≤ C * (N * (N ^ (-1 / 2 : ℝ)) ^ (1 / (2 * (2 : ℝ) ^ (j - 1) - 2)) +
      N ^ (1 - 2 / (2 : ℝ) ^ (j - 1) + 3 / (4 * (2 : ℝ) ^ (j - 1) - 4)))) :
    S ≤ 2 * C * N ^ (1 - 1 / (4 * (2 : ℝ) ^ (J - 1) - 4)) := by
  have hjtwo : 2 ≤ (2 : ℝ) ^ (j - 1) := by
    calc
      (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have horder : (2 : ℝ) ^ (j - 1) ≤ (2 : ℝ) ^ (J - 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hden : 0 < 4 * (2 : ℝ) ^ (j - 1) - 4 := by linarith
  have hsave : 1 / (4 * (2 : ℝ) ^ (J - 1) - 4) ≤ 1 / (4 * (2 : ℝ) ^ (j - 1) - 4) :=
    one_div_le_one_div_of_le hden (by linarith)
  exact (derivative_power_saving hN hjtwo hC hS).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) (by positivity))

/-- Page 21, diagnostic for the triangle inequality approach to the high frequency leaf.
The square root scale is not bounded by a constant times a strictly smaller power.
This does not assert an error in the paper. -/
theorem triangle_scale_not_LL {η : ℝ} (hη : 0 < η) :
    ¬ LL (fun x => x ^ (1 / 2 : ℝ)) (fun x => x ^ (1 / 2 - η)) := by
  rintro ⟨c, hc, X, h⟩
  let T : ℝ := max 1 (max X (2 / (c * η)))
  have hTX : X ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hTbig : 2 / (c * η) ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  have htwo : 2 ≤ T * (c * η) := (div_le_iff₀ (mul_pos hc hη)).mp hTbig
  have hx : X ≤ Real.exp T := by have := Real.add_one_le_exp T; linarith
  have hmain := h (Real.exp T) hx
  simp only [Real.rpow_def_of_pos (Real.exp_pos T), Real.log_exp] at hmain
  have hid : Real.exp (T * (1 / 2 : ℝ)) =
      Real.exp (T * (1 / 2 - η)) * Real.exp (T * η) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hid] at hmain
  have hb : c * Real.exp (T * η) ≤ 1 := by
    apply (mul_le_mul_iff_left₀ (Real.exp_pos (T * (1 / 2 - η)))).mp
    calc
      _ = c * (Real.exp (T * (1 / 2 - η)) * Real.exp (T * η)) := by ring
      _ ≤ Real.exp (T * (1 / 2 - η)) := hmain
      _ = _ := by ring
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (T * η)) hc.le
  nlinarith

/-- Page 21. Normalizing by 2π permits order two at the first crossing. -/
theorem derivative_order_from_linear_frequency {N a t R : ℝ} {J : ℕ}
    (hN : 1 < N) (ha : 1 ≤ a) (hasmall : a ≤ N ^ (1 / 4 : ℝ))
    (htlow : N ≤ t) (hthigh : t ≤ N ^ R)
    (hJ : R + 1 / 2 < 3 * (J : ℝ) / 4) :
    ∃ j : ℕ, 2 ≤ j ∧ j ≤ J ∧ N ^ (-3 / 2 : ℝ) ≤ t * (a / N) ^ j ∧
      t * (a / N) ^ j < N ^ (-1 / 2 : ℝ) := by
  have hN0 : 0 < N := by linarith
  have ha0 : 0 < a := by linarith
  have ht0 : 0 ≤ t := by linarith
  let r : ℝ := a / N
  have hr0 : 0 < r := div_pos ha0 hN0
  have hrN : 1 / N ≤ r := div_le_div_of_nonneg_right ha hN0.le
  have hrsmall : r ≤ N ^ (-3 / 4 : ℝ) := by
    apply (div_le_iff₀ hN0).mpr
    have heq : N ^ (-3 / 4 : ℝ) * N = N ^ (1 / 4 : ℝ) := by
      nth_rw 2 [← Real.rpow_one N]
      rw [← Real.rpow_add hN0]
      norm_num
    rw [heq]
    exact hasmall
  have hr1 : r ≤ 1 := hrsmall.trans (Real.rpow_le_one_of_one_le_of_nonpos hN.le (by norm_num))
  have hstart : N ^ (-1 / 2 : ℝ) ≤ (t / r) * r ^ 2 := by
    have hprod : 1 ≤ t * r := by
      have hh := mul_le_mul htlow hrN (by positivity) ht0
      have heq : N * (1 / N) = 1 := by field_simp
      rwa [heq] at hh
    have heq : (t / r) * r ^ 2 = t * r := by field_simp
    rw [heq]
    exact (Real.rpow_le_one_of_one_le_of_nonpos hN.le (by norm_num)).trans hprod
  have hend : (t / r) * r ^ (J + 1) < N ^ (-1 / 2 : ℝ) := by
    have heq : (t / r) * r ^ (J + 1) = t * r ^ J := by rw [pow_succ]; field_simp
    rw [heq]
    have hp := pow_le_pow_left₀ hr0.le hrsmall J
    have hh := mul_le_mul hthigh hp (by positivity) (Real.rpow_nonneg hN0.le _)
    have hid : N ^ R * (N ^ (-3 / 4 : ℝ)) ^ J = N ^ (R - 3 * (J : ℝ) / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
      congr 1
      ring
    rw [hid] at hh
    exact hh.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hN (by linarith))
  obtain ⟨j, hj3, hjJ, hjlow, hjhigh⟩ := derivative_order_crossing hN0 (div_nonneg ht0 hr0.le)
    (Real.rpow_nonneg hN0.le _) hr0.le hr1 hrN hstart hend
  have heq : (t / r) * r ^ j = t * r ^ (j - 1) := by
    have hj : j = (j - 1) + 1 := by omega
    conv_lhs => rw [hj, pow_succ]
    field_simp
  have hid : N ^ (-1 / 2 : ℝ) / N = N ^ (-3 / 2 : ℝ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hN0]
    norm_num
  rw [heq, hid] at hjlow
  rw [heq] at hjhigh
  exact ⟨j - 1, by omega, by omega, hjlow, hjhigh⟩

#print axioms derivative_order_from_linear_frequency

/-- Page 21. The first derivative test yields the low frequency character bound after partial summation. -/
theorem character_sum_small_frequency {N N1 t : ℝ} {q : ℕ} [NeZero q]
    (hN : 0 < N) (hNN1 : N ≤ N1) (hN1 : N1 ≤ 2 * N)
    (ht : 0 < |t|) (hqN : (q : ℝ) ≤ N) (hsmall : |t| * q ≤ Real.pi * N)
    (χ : DirichletCharacter ℂ q) :
    ‖∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, χ (n : ZMod q) * (n : ℂ) ^ (-(half t))‖ ≤
      8 * Real.pi * N ^ (1 / 2 : ℝ) / |t| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  let T : ℝ := |t| / (2 * Real.pi)
  have hT : 0 < T := by dsimp [T]; positivity
  have hsmall' : T * (q : ℝ) ≤ N / 2 := by
    have heq : T * (q : ℝ) = (|t| * q) / (2 * Real.pi) := by dsimp [T]; ring
    rw [heq]
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    nlinarith
  let B : ℝ := 4 * N / (T * q)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hprog : ∀ r : ZMod q,
      ‖∑ n ∈ (Ioc ⌊N⌋₊ ⌊N1⌋₊).filter (fun n : ℕ => (n : ZMod q) = r),
        (n : ℂ) ^ (-(half t))‖ ≤ B * N ^ (-1 / 2 : ℝ) := by
    intro r
    have hb := weighted_progression (η := 1 / 2) (C := B) hN hNN1 hN1 hB r (by
      intro u hNu hu
      rw [Progression219.norm_progression_eq_logarithmic hN hNu q r]
      let p : ℤ := ⌊(N - (r.val : ℝ)) / q⌋ + 1
      let v : ℤ := ⌊(u - (r.val : ℝ)) / q⌋
      have hleft : N ≤ (q : ℝ) * p + r.val := by
        have hh := Int.lt_floor_add_one ((N - (r.val : ℝ)) / q)
        have hh' : (N - (r.val : ℝ)) / q < (p : ℝ) := by simpa only [p, Int.cast_add, Int.cast_one] using hh
        have := (div_lt_iff₀ hq0).mp hh'
        linarith
      have hright : (q : ℝ) * v + r.val ≤ 2 * N := by
        have hh := Int.floor_le ((u - (r.val : ℝ)) / q)
        have := (le_div_iff₀ hq0).mp hh
        linarith
      have hh := LowFrequency219.logarithmic_first_derivative p v hq0 hT hN hqN hsmall' hleft hright
      simpa only [show (1 : ℝ) - 2 * (1 / 2) = 0 by norm_num, Real.rpow_zero, mul_one] using hh)
    simpa only [show (1 / 2 : ℝ) - 2 * (1 / 2) = -1 / 2 by norm_num] using hb
  have hb := character_of_progressions χ (Ioc ⌊N⌋₊ ⌊N1⌋₊)
    (fun n => (n : ℂ) ^ (-(half t))) (mul_nonneg hB (Real.rpow_nonneg hN.le _)) hprog
  have hid : (q : ℝ) * (B * N ^ (-1 / 2 : ℝ)) = 8 * Real.pi * N ^ (1 / 2 : ℝ) / |t| := by
    have hp : N * N ^ (-1 / 2 : ℝ) = N ^ (1 / 2 : ℝ) := by
      nth_rw 1 [← Real.rpow_one N]
      rw [← Real.rpow_add hN]
      norm_num
    calc
      _ = (4 / T) * (N * N ^ (-1 / 2 : ℝ)) := by dsimp [B]; field_simp <;> ring
      _ = (4 / T) * N ^ (1 / 2 : ℝ) := by rw [hp]
      _ = _ := by dsimp [T]; field_simp <;> ring
  exact hb.trans_eq hid

#print axioms character_sum_small_frequency

/-- Page 21. The second derivative test gives an explicit complementary character bound. -/
theorem character_sum_second_derivative {N N1 t : ℝ} {q : ℕ} [NeZero q]
    (hN1 : 1 ≤ N) (hNN1 : N ≤ N1) (hNupper : N1 ≤ 2 * N)
    (ht : 0 < |t|) (hqN : (q : ℝ) ≤ N) (χ : DirichletCharacter ℂ q) :
    ‖∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, χ (n : ZMod q) * (n : ℂ) ^ (-(half t))‖ ≤
      64 * (q : ℝ) ^ 2 * Real.sqrt (|t| / (2 * Real.pi)) * N ^ (-1 / 2 : ℝ) +
        32 * N ^ (1 / 2 : ℝ) / Real.sqrt (|t| / (2 * Real.pi)) := by
  have hN : 0 < N := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  let T : ℝ := |t| / (2 * Real.pi)
  have hT : 0 < T := by dsimp [T]; positivity
  have hsqrt : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  let B : ℝ := 64 * q * Real.sqrt T + 32 * N / (q * Real.sqrt T)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hprog : ∀ r : ZMod q,
      ‖∑ n ∈ (Ioc ⌊N⌋₊ ⌊N1⌋₊).filter (fun n : ℕ => (n : ZMod q) = r),
        (n : ℂ) ^ (-(half t))‖ ≤ B * N ^ (-1 / 2 : ℝ) := by
    intro r
    have hb := weighted_progression (η := 1 / 2) (C := B) hN hNN1 hNupper hB r (by
      intro u hNu hu
      rw [Progression219.norm_progression_eq_logarithmic hN hNu q r]
      let p : ℤ := ⌊(N - (r.val : ℝ)) / q⌋ + 1
      let v : ℤ := ⌊(u - (r.val : ℝ)) / q⌋
      have hleft : N ≤ (q : ℝ) * p + r.val := by
        have hh := Int.lt_floor_add_one ((N - (r.val : ℝ)) / q)
        have hh' : (N - (r.val : ℝ)) / q < (p : ℝ) := by simpa only [p, Int.cast_add, Int.cast_one] using hh
        have := (div_lt_iff₀ hq0).mp hh'
        linarith
      have hright : (q : ℝ) * v + r.val ≤ 2 * N := by
        have hh := Int.floor_le ((u - (r.val : ℝ)) / q)
        have := (le_div_iff₀ hq0).mp hh
        linarith
      have hh := LowFrequency219.logarithmic_second_derivative p v hq1 hT hN1 hqN hleft hright
      simpa only [show (1 : ℝ) - 2 * (1 / 2) = 0 by norm_num, Real.rpow_zero, mul_one] using hh)
    simpa only [show (1 / 2 : ℝ) - 2 * (1 / 2) = -1 / 2 by norm_num] using hb
  have hb := character_of_progressions χ (Ioc ⌊N⌋₊ ⌊N1⌋₊)
    (fun n => (n : ℂ) ^ (-(half t))) (mul_nonneg hB (Real.rpow_nonneg hN.le _)) hprog
  have hid : (q : ℝ) * (B * N ^ (-1 / 2 : ℝ)) =
      64 * (q : ℝ) ^ 2 * Real.sqrt T * N ^ (-1 / 2 : ℝ) + 32 * N ^ (1 / 2 : ℝ) / Real.sqrt T := by
    have hp : N * N ^ (-1 / 2 : ℝ) = N ^ (1 / 2 : ℝ) := by
      nth_rw 1 [← Real.rpow_one N]
      rw [← Real.rpow_add hN]
      norm_num
    calc
      _ = 64 * (q : ℝ) ^ 2 * Real.sqrt T * N ^ (-1 / 2 : ℝ) +
          32 * (N * N ^ (-1 / 2 : ℝ)) / Real.sqrt T := by dsimp [B]; field_simp <;> ring
      _ = _ := by rw [hp]
  exact hb.trans_eq hid

#print axioms character_sum_second_derivative

/-- Page 21. The absolute estimate is uniform in the modulus and the frequency. -/
theorem character_sum_trivial {N N1 t : ℝ} {q : ℕ} [NeZero q]
    (hN : 0 < N) (hNN1 : N ≤ N1) (hN1 : N1 ≤ 2 * N) (χ : DirichletCharacter ℂ q) :
    ‖∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, χ (n : ZMod q) * (n : ℂ) ^ (-(half t))‖ ≤
      2 * N ^ (1 / 2 : ℝ) := by
  have hterm : ∀ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊,
      ‖χ (n : ZMod q) * (n : ℂ) ^ (-(half t))‖ ≤ N ^ (-1 / 2 : ℝ) := by
    intro n hn
    have hnN : N < (n : ℝ) := (Nat.floor_lt hN.le).mp (mem_Ioc.mp hn).1
    have hn0 : 0 < (n : ℝ) := hN.trans hnN
    rw [norm_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
    have hre : (-(half t)).re = (-1 / 2 : ℝ) := by norm_num [half]
    rw [hre]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg hn0.le _) (χ.norm_le_one _)).trans
      (Real.rpow_le_rpow_of_nonpos hN hnN.le (by norm_num))
  have hcard : ((Ioc ⌊N⌋₊ ⌊N1⌋₊).card : ℝ) ≤ 2 * N := by
    calc
      _ ≤ (⌊N1⌋₊ : ℝ) := by rw [Nat.card_Ioc]; exact_mod_cast Nat.sub_le ⌊N1⌋₊ ⌊N⌋₊
      _ ≤ N1 := Nat.floor_le (hN.trans_le hNN1).le
      _ ≤ _ := hN1
  calc
    _ ≤ ∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, ‖χ (n : ZMod q) * (n : ℂ) ^ (-(half t))‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, N ^ (-1 / 2 : ℝ) := sum_le_sum hterm
    _ = ((Ioc ⌊N⌋₊ ⌊N1⌋₊).card : ℝ) * N ^ (-1 / 2 : ℝ) := by simp
    _ ≤ 2 * N * N ^ (-1 / 2 : ℝ) := mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hN.le _)
    _ = _ := by
      rw [mul_assoc]
      nth_rw 1 [← Real.rpow_one N]
      rw [← Real.rpow_add hN]
      norm_num

#print axioms character_sum_trivial

set_option maxHeartbeats 2000000 in
/-- LEAF. Page 21, first sentence of the proof of Lemma 6.
Fujii, Gallagher and Montgomery, reference 6, Theorem 1.
Use the smaller positive parameter ε/4 in the frequency split. -/
theorem fgm_branch :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : ℝ, 2 ≤ x → ∀ N N1 : ℝ, x ^ ε ≤ N → N ≤ x → N ≤ N1 → N1 ≤ 2 * N →
    ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ L x ^ A → ∀ χ : DirichletCharacter ℂ q,
    ∀ t : ℝ, |t| ≤ x → |t| ^ (1 / 2 : ℝ) * x ^ (ε / 4) < N →
      ‖∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, χ (n : ZMod q) * (n : ℂ) ^ (-(half t))‖ ≤
        C * (N ^ (1 / 2 - η) + N ^ (1 / 2 : ℝ) / (1 + |t|)) := by
  intro ε hε
  let η : ℝ := min (ε / 8) (1 / 4)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηε : η ≤ ε / 8 := min_le_left _ _
  have hηquarter : η ≤ 1 / 4 := min_le_right _ _
  refine ⟨η, hη, ?_⟩
  intro A hA
  obtain ⟨K, hK, hmod⟩ := logarithmic_absorption hε (by positivity : 0 < ε / 16) hA
  obtain ⟨Kq, hKq, hmodq⟩ := logarithmic_absorption hε (by norm_num : (0 : ℝ) < 1 / 8) hA
  obtain ⟨Xq, hXq, hqsmall⟩ := Parameter219.constant_mul_rpow_le_eventually Kq (1 / 8) (1 / 4) (by norm_num)
  let X : ℝ := max 16 Xq
  have hX : 0 < X := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  let C : ℝ := 16 * Real.pi + 64 * K ^ 2 + 32 + 4 + 2 * X ^ η
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro x hx N N1 hNlower hNx hNN1 hN1 q _ hq χ t ht hsplit
  have hx0 : 0 < x := by linarith
  have hN1' : 1 < N := (Real.one_lt_rpow (by linarith : 1 < x) hε).trans_le hNlower
  have hN0 : 0 < N := by linarith
  have hmain : 0 ≤ N ^ (1 / 2 - η) := Real.rpow_nonneg hN0.le _
  have htail : 0 ≤ N ^ (1 / 2 : ℝ) / (1 + |t|) := by positivity
  have htriv := character_sum_trivial (t := t) hN0 hNN1 hN1 χ
  have hC4 : 4 ≤ C := by dsimp [C]; nlinarith [Real.pi_pos, sq_nonneg K, Real.rpow_nonneg hX.le η]
  have hCpi : 16 * Real.pi ≤ C := by dsimp [C]; nlinarith [sq_nonneg K, Real.rpow_nonneg hX.le η]
  have hCmain : 64 * K ^ 2 + 32 ≤ C := by dsimp [C]; nlinarith [Real.pi_pos, Real.rpow_nonneg hX.le η]
  by_cases ht1 : |t| ≤ 1
  · have hb : 2 * N ^ (1 / 2 : ℝ) ≤ 4 * (N ^ (1 / 2 : ℝ) / (1 + |t|)) := by
      rw [← mul_div_assoc, le_div_iff₀ (by positivity : 0 < 1 + |t|)]
      nlinarith [Real.rpow_nonneg hN0.le (1 / 2 : ℝ)]
    exact (htriv.trans hb).trans (mul_le_mul hC4 (le_add_of_nonneg_left hmain) htail hC)
  have htpos : 0 < |t| := by linarith
  by_cases hsmallN : N < X
  · have hpow : N ^ η ≤ X ^ η := Real.rpow_le_rpow hN0.le hsmallN.le hη.le
    have hid : 2 * N ^ (1 / 2 : ℝ) = 2 * N ^ η * N ^ (1 / 2 - η) := by
      rw [mul_assoc, ← Real.rpow_add hN0]
      congr 1
      ring
    have hCX : 2 * X ^ η ≤ C := by dsimp [C]; nlinarith [Real.pi_pos, sq_nonneg K]
    calc
      _ ≤ 2 * N ^ (1 / 2 : ℝ) := htriv
      _ = 2 * N ^ η * N ^ (1 / 2 - η) := hid
      _ ≤ (2 * X ^ η) * N ^ (1 / 2 - η) := by gcongr
      _ ≤ C * (N ^ (1 / 2 - η) + N ^ (1 / 2 : ℝ) / (1 + |t|)) :=
        mul_le_mul hCX (le_add_of_nonneg_right htail) hmain hC
  have hlarge : X ≤ N := le_of_not_gt hsmallN
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hlarge
  have hNXq : Xq ≤ N := (le_max_right _ _).trans hlarge
  have hqquarter : (q : ℝ) ≤ N ^ (1 / 4 : ℝ) :=
    hq.trans ((hmodq x N hx hNlower).trans (hqsmall N hNXq))
  have hqN : (q : ℝ) ≤ N := hqquarter.trans (by
    calc N ^ (1 / 4 : ℝ) ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1'.le (by norm_num)
         _ = _ := Real.rpow_one N)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  by_cases hlow : |t| * q ≤ Real.pi * N
  · have hb := character_sum_small_frequency hN0 hNN1 hN1 htpos hqN hlow χ
    have htail' : 8 * Real.pi * N ^ (1 / 2 : ℝ) / |t| ≤
        (16 * Real.pi) * (N ^ (1 / 2 : ℝ) / (1 + |t|)) := by
      rw [← mul_div_assoc, div_le_div_iff₀ htpos (by positivity : 0 < 1 + |t|)]
      nlinarith [mul_pos Real.pi_pos (Real.rpow_pos_of_pos hN0 (1 / 2 : ℝ))]
    exact (hb.trans htail').trans (mul_le_mul hCpi (le_add_of_nonneg_left hmain) htail hC)
  let T : ℝ := |t| / (2 * Real.pi)
  have hT : 0 < T := by dsimp [T]; positivity
  have hTle : T ≤ |t| := div_le_self (abs_nonneg t) (by nlinarith [Real.pi_gt_three])
  have hrootup : Real.sqrt T * N ^ (-1 / 2 : ℝ) ≤ N ^ (1 / 2 - ε / 4) := by
    have hsqrt : Real.sqrt T ≤ |t| ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow hT.le hTle (by norm_num)
    have hpow : N ^ (ε / 4) ≤ x ^ (ε / 4) := Real.rpow_le_rpow hN0.le hNx (by positivity)
    have hprod : Real.sqrt T * N ^ (ε / 4) ≤ N :=
      (mul_le_mul hsqrt hpow (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg (abs_nonneg t) _)).trans hsplit.le
    have hsqrt' : Real.sqrt T ≤ N ^ (1 - ε / 4) := by
      have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hN0 (ε / 4))).mpr hprod
      have hid : N / N ^ (ε / 4) = N ^ (1 - ε / 4) := by
        nth_rw 1 [← Real.rpow_one N]
        rw [← Real.rpow_sub hN0]
      exact hh.trans_eq hid
    calc
      _ ≤ N ^ (1 - ε / 4) * N ^ (-1 / 2 : ℝ) := mul_le_mul_of_nonneg_right hsqrt' (Real.rpow_nonneg hN0.le _)
      _ = _ := by rw [← Real.rpow_add hN0]; congr 1; ring
  have hqpow : (q : ℝ) ^ 2 ≤ K ^ 2 * N ^ (ε / 8) := by
    have hqK := hq.trans (hmod x N hx hNlower)
    have hh := pow_le_pow_left₀ hq0.le hqK 2
    have hid : (N ^ (ε / 16)) ^ 2 = N ^ (ε / 8) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      congr 1
      ring
    simpa only [mul_pow, hid] using hh
  have hfirst : 64 * (q : ℝ) ^ 2 * Real.sqrt T * N ^ (-1 / 2 : ℝ) ≤
      64 * K ^ 2 * N ^ (1 / 2 - ε / 8) := by
    calc
      _ = 64 * (q : ℝ) ^ 2 * (Real.sqrt T * N ^ (-1 / 2 : ℝ)) := by ring
      _ ≤ 64 * (K ^ 2 * N ^ (ε / 8)) * N ^ (1 / 2 - ε / 4) := by gcongr
      _ = _ := by
        rw [show 64 * (K ^ 2 * N ^ (ε / 8)) * N ^ (1 / 2 - ε / 4) =
          (64 * K ^ 2) * (N ^ (ε / 8) * N ^ (1 / 2 - ε / 4)) by ring,
          ← Real.rpow_add hN0]
        congr 2
        ring
  have hNquarter : 2 ≤ N ^ (1 / 4 : ℝ) := by
    have h16 : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [← h16]
    exact Real.rpow_le_rpow (by norm_num) hN16 (by norm_num)
  have hTq : N / 2 < T * (q : ℝ) := by
    dsimp [T]
    rw [div_mul_eq_mul_div]
    apply (lt_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    nlinarith [lt_of_not_ge hlow]
  have hTlower : N ^ (1 / 2 : ℝ) ≤ T := by
    apply le_of_lt
    apply (mul_lt_mul_iff_left₀ hq0).mp
    calc
      N ^ (1 / 2 : ℝ) * q ≤ N ^ (1 / 2 : ℝ) * N ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hqquarter (Real.rpow_nonneg hN0.le _)
      _ = N ^ (3 / 4 : ℝ) := by rw [← Real.rpow_add hN0]; norm_num
      _ ≤ N / 2 := by
        have hh := mul_le_mul_of_nonneg_right hNquarter (Real.rpow_nonneg hN0.le (3 / 4 : ℝ))
        rw [← Real.rpow_add hN0] at hh
        norm_num at hh
        linarith
      _ < T * q := hTq
  have hrootlo : N ^ (1 / 4 : ℝ) ≤ Real.sqrt T := by
    rw [Real.sqrt_eq_rpow]
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hTlower (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [← Real.rpow_mul hN0.le] at hh
    norm_num at hh ⊢
    exact hh
  have hsecond : 32 * N ^ (1 / 2 : ℝ) / Real.sqrt T ≤ 32 * N ^ (1 / 4 : ℝ) := by
    have hh := div_le_div_of_nonneg_left (Real.rpow_nonneg hN0.le (1 / 2 : ℝ))
      (Real.rpow_pos_of_pos hN0 (1 / 4 : ℝ)) hrootlo
    have hid : N ^ (1 / 2 : ℝ) / N ^ (1 / 4 : ℝ) = N ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_sub hN0]
      norm_num
    rw [hid] at hh
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 32)
  have hfirstpow : N ^ (1 / 2 - ε / 8) ≤ N ^ (1 / 2 - η) :=
    Real.rpow_le_rpow_of_exponent_le hN1'.le (by linarith)
  have hsecondpow : N ^ (1 / 4 : ℝ) ≤ N ^ (1 / 2 - η) :=
    Real.rpow_le_rpow_of_exponent_le hN1'.le (by linarith)
  have hb := character_sum_second_derivative hN1'.le hNN1 hN1 htpos hqN χ
  calc
    _ ≤ 64 * (q : ℝ) ^ 2 * Real.sqrt T * N ^ (-1 / 2 : ℝ) +
        32 * N ^ (1 / 2 : ℝ) / Real.sqrt T := hb
    _ ≤ 64 * K ^ 2 * N ^ (1 / 2 - ε / 8) + 32 * N ^ (1 / 4 : ℝ) := add_le_add hfirst hsecond
    _ ≤ (64 * K ^ 2 + 32) * N ^ (1 / 2 - η) := by
      nlinarith [mul_le_mul_of_nonneg_left hfirstpow (by positivity : 0 ≤ 64 * K ^ 2)]
    _ ≤ C * (N ^ (1 / 2 - η) + N ^ (1 / 2 : ℝ) / (1 + |t|)) :=
      mul_le_mul hCmain (le_add_of_nonneg_right htail) hmain hC


/-- LEAF. Page 21, display 3.35 and the last three displays.
Titchmarsh, reference 30, Theorems 5.9 and 5.11.
The sums are written over natural integers in one residue class.
The bound is uniform over every partial endpoint u between N and 2N. -/
theorem titchmarsh_branch :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : ℝ, 2 ≤ x → ∀ N : ℝ, x ^ ε ≤ N → N ≤ x →
    ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ L x ^ A →
    ∀ t : ℝ, |t| ≤ x → N ≤ |t| ^ (1 / 2 : ℝ) * x ^ (ε / 4) →
    ∀ r : ZMod q, ∀ u : ℝ, N ≤ u → u ≤ 2 * N →
      ‖∑ n ∈ (Ioc ⌊N⌋₊ ⌊u⌋₊).filter (fun n : ℕ => (n : ZMod q) = r),
        (n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ≤ C * N ^ (1 - 2 * η) := by
  intro ε hε
  let R : ℝ := 1 / ε
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨J, hJ⟩ := exists_nat_gt (4 * (R + 1))
  have hJrange : R + 1 / 2 < 3 * (J : ℝ) / 4 := by linarith
  obtain ⟨σ, X₀, hσ, hX₀, hbound⟩ := Parameter219.logarithmic_bounded_order J
  refine ⟨σ / 2, by positivity, ?_⟩
  intro A hA
  obtain ⟨K, hK, hmod⟩ := logarithmic_absorption hε (by norm_num : (0 : ℝ) < 1 / 8) hA
  obtain ⟨Xq, hXq, hqsmall⟩ := Parameter219.constant_mul_rpow_le_eventually K (1 / 8) (1 / 4) (by norm_num)
  obtain ⟨Xt, hXt, hfreq⟩ := Parameter219.constant_mul_rpow_le_eventually (2 * Real.pi) 1 (3 / 2) (by norm_num)
  let X : ℝ := max X₀ (max Xq Xt)
  have hX : 1 ≤ X := hX₀.trans (le_max_left _ _)
  refine ⟨16 + 2 * X ^ σ, by positivity, ?_⟩
  intro x hx N hNlower hNx q _ hq t ht hsmall r u hNu hu
  have hx0 : 0 < x := by linarith
  have hN1 : 1 < N := (Real.one_lt_rpow (by linarith : 1 < x) hε).trans_le hNlower
  have hN0 : 0 < N := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hexp : 1 - 2 * (σ / 2) = 1 - σ := by ring
  rw [hexp]
  by_cases hlarge : X ≤ N
  · have hNX₀ : X₀ ≤ N := (le_max_left _ _).trans hlarge
    have hNXq : Xq ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
    have hNXt : Xt ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
    have hqpow : (q : ℝ) ≤ N ^ (1 / 4 : ℝ) :=
      hq.trans ((hmod x N hx hNlower).trans (hqsmall N hNXq))
    have hqN : (q : ℝ) ≤ N := hqpow.trans (by
      calc N ^ (1 / 4 : ℝ) ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1.le (by norm_num)
           _ = N := Real.rpow_one N)
    have hfreq0 : N ^ (3 / 2 : ℝ) ≤ |t| := high_frequency_lower_bound hx0 hN0 hNlower hsmall
    have hfreq1 : 2 * Real.pi * N ≤ |t| := by
      have hh := hfreq N hNXt
      rw [Real.rpow_one] at hh
      exact hh.trans hfreq0
    let T : ℝ := |t| / (2 * Real.pi)
    have hpi : 0 < 2 * Real.pi := by positivity
    have hNT : N ≤ T := (le_div_iff₀ hpi).mpr (by nlinarith [hfreq1])
    have hT : 0 < T := hN0.trans_le hNT
    have hxN : x ≤ N ^ R := by
      have hh := Real.rpow_le_rpow (Real.rpow_nonneg hx0.le _) hNlower (le_of_lt (one_div_pos.mpr hε))
      have heq : (x ^ ε) ^ (1 / ε) = x := by
        rw [← Real.rpow_mul hx0.le, mul_one_div_cancel hε.ne', Real.rpow_one]
      rw [heq] at hh
      exact hh
    have hTupper : T ≤ N ^ R :=
      (div_le_self (abs_nonneg t) (by nlinarith [Real.pi_gt_three])).trans (ht.trans hxN)
    obtain ⟨j, hj2, hjJ, hjlo, hjhi⟩ := derivative_order_from_linear_frequency hN1 hq1 hqpow hNT hTupper hJrange
    let p : ℤ := ⌊(N - (r.val : ℝ)) / q⌋ + 1
    let v : ℤ := ⌊(u - (r.val : ℝ)) / q⌋
    have hleft : N ≤ (q : ℝ) * p + r.val := by
      have hh := Int.lt_floor_add_one ((N - (r.val : ℝ)) / q)
      have hh' : (N - (r.val : ℝ)) / q < (p : ℝ) := by simpa only [p, Int.cast_add, Int.cast_one] using hh
      have := (div_lt_iff₀ hq0).mp hh'
      linarith
    have hright : (q : ℝ) * v + r.val ≤ 2 * N := by
      have hh := Int.floor_le ((u - (r.val : ℝ)) / q)
      have hh' : (v : ℝ) ≤ (u - (r.val : ℝ)) / q := hh
      have := (le_div_iff₀ hq0).mp hh'
      linarith
    have hd : (j - 2) + 2 = j := by omega
    have hb := hbound N hNX₀ q T r.val hq1 hqN hT (j - 2) (by omega)
      (by simpa only [hd] using hjlo) (by simpa only [hd] using hjhi.le) p v hleft hright
    rw [Progression219.norm_progression_eq_logarithmic hN0 hNu q r]
    exact hb.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity : 0 ≤ 2 * X ^ σ))
      (Real.rpow_nonneg hN0.le _))
  · have hNX : N ≤ X := (lt_of_not_ge hlarge).le
    have hpower : N ^ σ ≤ X ^ σ := Real.rpow_le_rpow hN0.le hNX hσ.le
    have hid : 2 * N = 2 * N ^ σ * N ^ (1 - σ) := by
      rw [mul_assoc, ← Real.rpow_add hN0]
      norm_num
    calc
      _ ≤ 2 * N := Progression219.progression_trivial_bound hN0 hNu hu q r
      _ = 2 * N ^ σ * N ^ (1 - σ) := hid
      _ ≤ (16 + 2 * X ^ σ) * N ^ (1 - σ) := by
        gcongr
        linarith


/-- Lemma 6, page 21, assembled from the named leaves.
PROVED from the two character sum branches and the ported derivative estimates.
There is no sorry in this assembly. The resulting type is exactly Lemma6. -/
theorem lemma6_decomposed : Lemma6 := by
  intro ε hε
  obtain ⟨η₁, hη₁, hlarge⟩ := fgm_branch ε hε
  obtain ⟨η₂, hη₂, hsmall⟩ := titchmarsh_branch ε hε
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, ?_⟩
  intro A hA
  obtain ⟨C₁, hC₁, hlarge⟩ := hlarge A hA
  obtain ⟨C₂, hC₂, hsmall⟩ := hsmall A hA
  obtain ⟨K, hK, hmod⟩ := logarithmic_absorption hε hη₂ hA
  refine ⟨C₁ + C₂ * K, ?_⟩
  intro x hx N N1 hNlower hNx hNN1 hN1 q _ hq χ t ht
  have hxone : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hNone : 1 ≤ N := (Real.one_le_rpow hxone hε.le).trans hNlower
  have hN0 : 0 < N := by linarith
  have hfirst : N ^ (1 / 2 - η₁) ≤ N ^ (1 / 2 - min η₁ η₂) :=
    Real.rpow_le_rpow_of_exponent_le hNone (by linarith [min_le_left η₁ η₂])
  have hsecond : N ^ (1 / 2 - η₂) ≤ N ^ (1 / 2 - min η₁ η₂) :=
    Real.rpow_le_rpow_of_exponent_le hNone (by linarith [min_le_right η₁ η₂])
  have htail : 0 ≤ N ^ (1 / 2 : ℝ) / (1 + |t|) := by positivity
  by_cases hsplit : |t| ^ (1 / 2 : ℝ) * x ^ (ε / 4) < N
  · have hh := hlarge x hx N N1 hNlower hNx hNN1 hN1 q hq χ t ht hsplit
    refine hh.trans ?_
    calc
      _ ≤ C₁ * (N ^ (1 / 2 - min η₁ η₂) + N ^ (1 / 2 : ℝ) / (1 + |t|)) :=
        mul_le_mul_of_nonneg_left (add_le_add hfirst le_rfl) hC₁
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg hC₂ hK))
        (add_nonneg (Real.rpow_nonneg hN0.le _) htail)
  · have hprog := fun r => weighted_progression hN0 hNN1 hN1 hC₂ r
      (hsmall x hx N hNlower hNx q hq t ht (le_of_not_gt hsplit) r)
    have hh := character_of_progressions χ (Ioc ⌊N⌋₊ ⌊N1⌋₊)
      (fun n => (n : ℂ) ^ (-(half t)))
      (mul_nonneg hC₂ (Real.rpow_nonneg hN0.le _)) hprog
    have hqbound : (q : ℝ) ≤ K * N ^ η₂ := hq.trans (hmod x N hx hNlower)
    have hid : (K * N ^ η₂) * (C₂ * N ^ (1 / 2 - 2 * η₂)) =
        C₂ * K * N ^ (1 / 2 - η₂) := by
      rw [show (K * N ^ η₂) * (C₂ * N ^ (1 / 2 - 2 * η₂)) =
        C₂ * K * (N ^ η₂ * N ^ (1 / 2 - 2 * η₂)) by ring,
        ← Real.rpow_add hN0]
      congr 2
      ring
    calc
      _ ≤ (q : ℝ) * (C₂ * N ^ (1 / 2 - 2 * η₂)) := hh
      _ ≤ (K * N ^ η₂) * (C₂ * N ^ (1 / 2 - 2 * η₂)) :=
        mul_le_mul_of_nonneg_right hqbound (mul_nonneg hC₂ (Real.rpow_nonneg hN0.le _))
      _ = C₂ * K * N ^ (1 / 2 - η₂) := hid
      _ ≤ C₂ * K * N ^ (1 / 2 - min η₁ η₂) :=
        mul_le_mul_of_nonneg_left hsecond (mul_nonneg hC₂ hK)
      _ ≤ (C₁ + C₂ * K) * (N ^ (1 / 2 - min η₁ η₂) + N ^ (1 / 2 : ℝ) / (1 + |t|)) :=
        mul_le_mul (le_add_of_nonneg_left hC₁) (le_add_of_nonneg_right htail)
          (Real.rpow_nonneg hN0.le _) (add_nonneg hC₁ (mul_nonneg hC₂ hK))

#print axioms triangle_scale_not_LL

#print axioms derivative_saving_uniform

#print axioms derivative_order_of_ranges

#print axioms derivative_power_saving
#print axioms high_frequency_lower_bound
#print axioms derivative_order_crossing

#print axioms fgm_branch
#print axioms titchmarsh_branch
#print axioms abel_bound
#print axioms weighted_progression
#print axioms character_of_progressions
#print axioms logarithmic_absorption
#print axioms lemma6_decomposed

end LeanLab.BakerHarmanPintz1997.Decomp90
