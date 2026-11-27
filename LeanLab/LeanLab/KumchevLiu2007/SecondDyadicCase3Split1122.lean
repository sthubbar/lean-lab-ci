/-
BURST 2026-11-22, session S81, burst-20261122. SPLIT of the leaf
Split1122SecondDyadicBlock.case3_large_D, Case 3 of the proof of Lemma 3.4 of
Kumchev and Liu 2007, P0088, arXiv 0801.0130, page 12, applied on page 15 to the
second sum of display 52 in window form, t in [Y/4, Y] with the squareWindow Y
filter on m. Same cut at t = Y - 2H as SecondDyadicCases1122 for Cases 1 and 2,
for the same reason: the edge stretch needs a divisor moment bound the paper
does not state. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Split1122SecondDyadicBlock

namespace LeanLab.KumchevLiu2007.SecondDyadicCase3Split1122

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: P0088 page 12, Case 3 of the proof of Lemma 3.4 on the interior stretch
t in [Y/4, Y - 2H], D above V = H Y^(-1/2) L^(-B). Class HARD. On this stretch the
window filter is no restriction, as in Split1122KLLemma34M1.window_filter_eq, so
it is Case 3 in the general x, y form at x = Y/4 and x = Y/2 with the prime block
coefficient: the factorisation of d at the index s of page 12, the removal of
p' < p, pp'd1d2 in the block D and d1pp' at least V by Lemma 3.3, Kumchev 2006
Lemma 2.7, and Lemma 3.2 in u = mkp'd2, v = pd1. The M = 1 analogue is
Lemma34Case3General1122.case_three_of_leaves. Reduction not yet written. -/
theorem case3_interior (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        ∀ D : ℝ, H / (Real.sqrt (windowY X ε) * Real.log X ^ B) < D →
        (∫ t in windowY X ε / 4..windowY X ε - 2 * H,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry


private lemma card_multiples_Ioc_le (d a b : ℕ) (hd : 1 ≤ d) :
    ((Finset.Ioc a b).filter (fun m : ℕ => d ∣ m)).card ≤ (b - a) / d + 2 := by
  classical
  by_cases hba : b ≤ a
  · have hsub : (Finset.Ioc a b).filter (fun m : ℕ => d ∣ m) ⊆ ∅ := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hx
      omega
    have h : ((Finset.Ioc a b).filter (fun m : ℕ => d ∣ m)).card ≤ 0 := by
      simpa using Finset.card_le_card hsub
    exact h.trans (Nat.zero_le _)
  have hab : a ≤ b := by omega
  have hb : b / d ≤ a / d + (b - a) / d + 1 := by
    rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hd]
    show b < (a / d + (b - a) / d + 1 + 1) * d
    have hA : a < d * (a / d) + d := by
      calc a = d * (a / d) + a % d := (Nat.div_add_mod a d).symm
        _ < d * (a / d) + d := Nat.add_lt_add_left (Nat.mod_lt a hd) _
    have hB : b - a < d * ((b - a) / d) + d := by
      calc b - a = d * ((b - a) / d) + (b - a) % d := (Nat.div_add_mod (b - a) d).symm
        _ < d * ((b - a) / d) + d := Nat.add_lt_add_left (Nat.mod_lt (b - a) hd) _
    have hlin : a + (b - a) < (d * (a / d) + d) + (d * ((b - a) / d) + d) := add_lt_add hA hB
    have hring : (d * (a / d) + d) + (d * ((b - a) / d) + d) =
        (a / d + (b - a) / d + 1 + 1) * d := by ring
    calc b = a + (b - a) := (Nat.add_sub_of_le hab).symm
      _ < (a / d + (b - a) / d + 1 + 1) * d := by rw [← hring]; exact hlin
  have hstep : ((Finset.Ioc a b).filter (fun m : ℕ => d ∣ m)).card ≤ b / d + 1 - a / d := by
    refine (Finset.card_le_card_of_injOn (fun m : ℕ => m / d) ?_ ?_).trans
      (le_of_eq (Nat.card_Icc (a / d) (b / d)))
    · intro m hm
      obtain ⟨hmI, hdvd⟩ := Finset.mem_filter.mp hm
      obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hmI
      exact Finset.mem_Icc.mpr ⟨Nat.div_le_div_right h1.le, Nat.div_le_div_right h2⟩
    · intro m₁ hm₁ m₂ hm₂ he
      have h1 : d * (m₁ / d) = m₁ := Nat.mul_div_cancel' (Finset.mem_filter.mp hm₁).2
      have h2 : d * (m₂ / d) = m₂ := Nat.mul_div_cancel' (Finset.mem_filter.mp hm₂).2
      have h3 : d * (m₁ / d) = d * (m₂ / d) := congrArg (fun t => d * t) he
      rw [h1, h2] at h3
      exact h3
  have hfin : b / d + 1 - a / d ≤ (b - a) / d + 2 := by
    rw [Nat.sub_le_iff_le_add]
    omega
  exact hstep.trans hfin

private lemma card_divisors_le_two_mul (m : ℕ) :
    m.divisors.card ≤ 2 * (m.divisors.filter (fun d : ℕ => d * d ≤ m)).card := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · simp [hm]
  have hsplit : m.divisors.card =
      (m.divisors.filter (fun d : ℕ => d * d ≤ m)).card +
        (m.divisors.filter (fun d : ℕ => ¬ d * d ≤ m)).card := by
    rw [← Finset.card_filter_add_card_filter_not (fun d : ℕ => d * d ≤ m)]
  have hcard : (m.divisors.filter (fun d : ℕ => ¬ d * d ≤ m)).card ≤
      (m.divisors.filter (fun d : ℕ => d * d ≤ m)).card := by
    refine Finset.card_le_card_of_injOn (fun d : ℕ => m / d) ?_ ?_
    · intro d hd
      obtain ⟨hdvd, hgt⟩ := Finset.mem_filter.mp hd
      obtain ⟨hdvd', hne⟩ := Nat.mem_divisors.mp hdvd
      simp only [not_le] at hgt
      have hmul : d * (m / d) = m := Nat.mul_div_cancel' hdvd'
      have hpos : 0 < d := by
        rcases Nat.eq_zero_or_pos d with h | h
        · rw [h, zero_mul] at hmul
          omega
        · exact h
      have hk : m / d ∣ m := Nat.div_dvd_of_dvd hdvd'
      have hk0 : m / d ≠ 0 := by
        rintro h0
        rw [h0, mul_zero] at hmul
        omega
      refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hk, hm.ne'⟩, ?_⟩
      have hle : m / d ≤ d := by
        have h1 : m / d * d ≤ d * d := by rw [mul_comm (m / d) d, hmul]; omega
        exact Nat.le_of_mul_le_mul_right h1 hpos
      calc m / d * (m / d) ≤ d * (m / d) := Nat.mul_le_mul_right _ hle
        _ = m := hmul
    · intro d₁ hd₁ d₂ hd₂ he
      obtain ⟨hdvd₁, -⟩ := Finset.mem_filter.mp hd₁
      obtain ⟨hdvd₂, -⟩ := Finset.mem_filter.mp hd₂
      obtain ⟨h1', -⟩ := Nat.mem_divisors.mp hdvd₁
      obtain ⟨h2', -⟩ := Nat.mem_divisors.mp hdvd₂
      have h1 : d₁ * (m / d₁) = m := Nat.mul_div_cancel' h1'
      have h2 : d₂ * (m / d₂) = m := Nat.mul_div_cancel' h2'
      have hk : m / d₂ ≠ 0 := by
        rintro h0
        rw [h0, mul_zero] at h2
        omega
      have he' : m / d₁ = m / d₂ := he
      have h3 : d₁ * (m / d₂) = d₂ * (m / d₂) := by
        conv_lhs => rw [← he']
        rw [h1, h2]
      exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hk) h3
  omega

private lemma sum_tau_Ioc_le (a b : ℕ) (hb : 1 ≤ b) :
    ∑ m ∈ Finset.Ioc a b, (m.divisors.card : ℝ) ≤
      2 * ((b - a : ℕ) : ℝ) * (1 + Real.log (b : ℝ)) + 4 * Real.sqrt (b : ℝ) + 2 := by
  classical
  set F : ℕ → Finset ℕ := fun m => m.divisors.filter (fun d : ℕ => d * d ≤ m) with hF
  set s : Finset ℕ := Finset.Ioc a b with hs
  set N : ℕ := Nat.sqrt b with hN
  set T : Finset ℕ := Finset.Icc 1 N with hT
  -- step 1: pointwise comparison with a product count
  have hstep1 : ∑ m ∈ s, (m.divisors.card : ℝ) ≤
      2 * ∑ m ∈ s, ((T.filter (fun d : ℕ => d * d ≤ m ∧ d ∣ m)).card : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun m hm => ?_)
    obtain ⟨hm1, hm2⟩ := Finset.mem_Ioc.mp hm
    have hsub : F m ⊆ T.filter (fun d : ℕ => d * d ≤ m ∧ d ∣ m) := by
      intro d hd
      obtain ⟨hdvd, hle⟩ := Finset.mem_filter.mp hd
      obtain ⟨hdvd', hne⟩ := Nat.mem_divisors.mp hdvd
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd' (by omega)
      have hdN : d ≤ N := by
        rw [hN]
        exact Nat.le_sqrt.mpr (by omega)
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hdpos, hdN⟩, hle, hdvd'⟩
    have hcard : ((F m).card : ℝ) ≤ ((T.filter (fun d : ℕ => d * d ≤ m ∧ d ∣ m)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have h2 : (m.divisors.card : ℝ) ≤ 2 * ((F m).card : ℝ) := by
      have h3 : (m.divisors.card : ℕ) ≤ 2 * (F m).card := by simpa [hF] using card_divisors_le_two_mul m
      exact_mod_cast h3
    linarith
  -- step 2: swap the order of summation
  have hprod : ∑ m ∈ s, ((T.filter (fun d : ℕ => d * d ≤ m ∧ d ∣ m)).card : ℝ) =
      ∑ d ∈ T, ((s.filter (fun m : ℕ => d * d ≤ m ∧ d ∣ m)).card : ℝ) := by
    have h1 : ∀ m ∈ s, ((T.filter (fun d : ℕ => d * d ≤ m ∧ d ∣ m)).card : ℝ) =
        ∑ d ∈ T, (if (d * d ≤ m ∧ d ∣ m) then (1 : ℝ) else 0) := by
      intro m _
      have hc : ((T.filter (fun d : ℕ => d * d ≤ m ∧ d ∣ m)).card : ℝ) =
          ∑ d ∈ T.filter (fun d : ℕ => d * d ≤ m ∧ d ∣ m), (1 : ℝ) := by
        rw [Finset.card_eq_sum_ones]; push_cast; ring
      rw [hc, Finset.sum_filter]
    have h2 : ∀ d ∈ T, ((s.filter (fun m : ℕ => d * d ≤ m ∧ d ∣ m)).card : ℝ) =
        ∑ m ∈ s, (if (d * d ≤ m ∧ d ∣ m) then (1 : ℝ) else 0) := by
      intro d _
      have hc : ((s.filter (fun m : ℕ => d * d ≤ m ∧ d ∣ m)).card : ℝ) =
          ∑ m ∈ s.filter (fun m : ℕ => d * d ≤ m ∧ d ∣ m), (1 : ℝ) := by
        rw [Finset.card_eq_sum_ones]; push_cast; ring
      rw [hc, Finset.sum_filter]
    calc ∑ m ∈ s, ((T.filter (fun d : ℕ => d * d ≤ m ∧ d ∣ m)).card : ℝ)
        = ∑ m ∈ s, ∑ d ∈ T, (if (d * d ≤ m ∧ d ∣ m) then (1 : ℝ) else 0) :=
          Finset.sum_congr rfl h1
      _ = ∑ d ∈ T, ∑ m ∈ s, (if (d * d ≤ m ∧ d ∣ m) then (1 : ℝ) else 0) := Finset.sum_comm
      _ = ∑ d ∈ T, ((s.filter (fun m : ℕ => d * d ≤ m ∧ d ∣ m)).card : ℝ) :=
          (Finset.sum_congr rfl h2).symm
  -- step 3: bound each inner count
  have hfib : ∑ d ∈ T, ((s.filter (fun m : ℕ => d * d ≤ m ∧ d ∣ m)).card : ℝ) ≤
      ∑ d ∈ T, ((((b - a) / d + 2 : ℕ)) : ℝ) := by
    refine Finset.sum_le_sum (fun d hd => ?_)
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hsub : (s.filter (fun m : ℕ => d * d ≤ m ∧ d ∣ m)) ⊆
        (Finset.Ioc a b).filter (fun m : ℕ => d ∣ m) := by
      intro m hm
      obtain ⟨hms, -, hdvd⟩ := Finset.mem_filter.mp hm
      exact Finset.mem_filter.mpr ⟨by simpa [hs] using hms, hdvd⟩
    have hle : ((s.filter (fun m : ℕ => d * d ≤ m ∧ d ∣ m)).card : ℝ) ≤
        ((((b - a) / d + 2 : ℕ)) : ℝ) := by
      have h1 : (s.filter (fun m : ℕ => d * d ≤ m ∧ d ∣ m)).card ≤
          ((Finset.Ioc a b).filter (fun m : ℕ => d ∣ m)).card := Finset.card_le_card hsub
      have h2 := card_multiples_Ioc_le d a b hd1
      exact_mod_cast h1.trans h2
    exact hle
  -- step 4: evaluate the harmonic sum
  have hharm : ∑ d ∈ T, ((((b - a) / d + 2 : ℕ)) : ℝ) ≤
      ((b - a : ℕ) : ℝ) * (1 + Real.log (b : ℝ)) + 2 * Real.sqrt (b : ℝ) := by
    have hterm : ∑ d ∈ T, ((((b - a) / d + 2 : ℕ)) : ℝ) ≤
        ∑ d ∈ T, (((b - a : ℕ) : ℝ) * ((d : ℝ))⁻¹ + 2) := by
      refine Finset.sum_le_sum (fun d hd => ?_)
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hcast : ((((b - a) / d : ℕ)) : ℝ) ≤ ((b - a : ℕ) : ℝ) / (d : ℝ) := Nat.cast_div_le
      have hcast' : ((((b - a) / d : ℕ)) : ℝ) ≤ ((b - a : ℕ) : ℝ) * ((d : ℝ))⁻¹ := by
        rw [div_eq_mul_inv] at hcast
        exact hcast
      have heq : ((((b - a) / d + 2 : ℕ)) : ℝ) = ((((b - a) / d : ℕ)) : ℝ) + 2 := by
        push_cast; ring
      rw [heq]
      linarith
    have hcardT : T.card = N := by
      rw [hT, Nat.card_Icc]; omega
    have hcalc : ∑ d ∈ T, (((b - a : ℕ) : ℝ) * ((d : ℝ))⁻¹ + 2) =
        ((b - a : ℕ) : ℝ) * (∑ d ∈ T, ((d : ℝ))⁻¹) + 2 * (N : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      have h2s : ∑ x ∈ T, (2 : ℝ) = 2 * (N : ℝ) := by
        rw [Finset.sum_const, hcardT]; simp [mul_comm]
      rw [h2s]
    rw [hcalc] at hterm
    have hba0 : (0 : ℝ) ≤ ((b - a : ℕ) : ℝ) := by positivity
    have hNh : ∑ d ∈ T, ((d : ℝ))⁻¹ ≤ 1 + Real.log (b : ℝ) := by
      have h := harmonic_le_one_add_log N
      rw [harmonic_eq_sum_Icc] at h
      push_cast at h
      rw [show T = Finset.Icc 1 N from hT]
      have hNle : (N : ℝ) ≤ (b : ℝ) := by
        have h1 : N ≤ b := by
          rw [hN]; exact Nat.sqrt_le_self b
        exact_mod_cast h1
      have hNpos : (0 : ℝ) < (N : ℝ) := by
        have h1 : 1 ≤ N := by
          rw [hN]; exact Nat.le_sqrt.mpr (by omega)
        exact_mod_cast h1
      have hlog := Real.log_le_log hNpos hNle
      linarith
    have hNle : (N : ℝ) ≤ Real.sqrt (b : ℝ) := by
      apply Real.le_sqrt_of_sq_le
      have h1 : N ^ 2 ≤ b := by rw [hN]; exact Nat.sqrt_le' b
      have h2 : ((N : ℝ)) ^ 2 ≤ (b : ℝ) := by exact_mod_cast h1
      simpa using h2
    have hmul := mul_le_mul_of_nonneg_left hNh hba0
    nlinarith [hterm, hmul, hNle]
  have hchain : ∑ m ∈ s, (m.divisors.card : ℝ) ≤
      2 * (((b - a : ℕ) : ℝ) * (1 + Real.log (b : ℝ)) + 2 * Real.sqrt (b : ℝ)) := by
    have := hstep1.trans (mul_le_mul_of_nonneg_left (hprod.trans_le (hfib.trans hharm)) (by norm_num : (0:ℝ) ≤ 2))
    linarith [this]
  linarith [hchain]

/-- At most two primes exceeding `Y^(1/6+ε/2)` divide an `m` with `m^2 < Y`. -/
private lemma card_primes_le_two {ε Y : ℝ} {m : ℕ} (hY : 1 < Y) (hε : 0 < ε)
    (hm0 : 0 < m) (hm : (m : ℝ) ^ 2 < Y) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ Y ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧ p ∣ m) :
    P.card ≤ 2 := by
  classical
  set z : ℝ := Y ^ (1 / 6 + ε / 2) with hz
  have hzpos : 0 < z := Real.rpow_pos_of_pos (by linarith) _
  have hz1 : 1 ≤ z := by
    have h0 : (1 : ℝ) = Y ^ (0 : ℝ) := by simp
    rw [h0]
    exact Real.rpow_le_rpow_of_exponent_le hY.le (by positivity)
  by_contra hcon
  have h3 : 3 ≤ P.card := by omega
  have hsub : P ⊆ m.primeFactors := fun p hp =>
    Nat.mem_primeFactors.mpr ⟨(hP p hp).1, (hP p hp).2.2, hm0.ne'⟩
  have hdvd : (∏ p ∈ P, p) ∣ m :=
    (Finset.prod_dvd_prod_of_subset P m.primeFactors (fun p => p) hsub).trans
      (Nat.prod_primeFactors_dvd m)
  have hle : ((∏ p ∈ P, p : ℕ) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hm0 hdvd
  have hcast : ((∏ p ∈ P, p : ℕ) : ℝ) = ∏ p ∈ P, (p : ℝ) := by push_cast; ring
  have hprod_ge : ∀ Q ⊆ P, z ^ Q.card ≤ ∏ p ∈ Q, (p : ℝ) := by
    intro Q hQ
    induction Q using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        have hs : s ⊆ P := fun x hx => hQ (Finset.mem_insert_of_mem hx)
        have haP : a ∈ P := hQ (Finset.mem_insert_self a s)
        have ha1 : z ≤ (a : ℝ) := (hP a haP).2.1
        have htarget : z ^ s.card * z ≤ (a : ℝ) * ∏ p ∈ s, (p : ℝ) := by
          calc z ^ s.card * z ≤ z ^ s.card * (a : ℝ) :=
                mul_le_mul_of_nonneg_left ha1 (pow_nonneg hzpos.le _)
            _ ≤ (∏ p ∈ s, (p : ℝ)) * (a : ℝ) :=
                mul_le_mul_of_nonneg_right (ih hs) (by positivity)
            _ = (a : ℝ) * ∏ p ∈ s, (p : ℝ) := by ring
        rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ]
        exact htarget
  have hlb : z ^ 3 ≤ ((∏ p ∈ P, p : ℕ) : ℝ) := by
    rw [hcast]
    exact (pow_le_pow_right₀ hz1 h3).trans (hprod_ge P (fun _ hx => hx))
  have hub : ((∏ p ∈ P, p : ℕ) : ℝ) < z ^ 3 := by
    have hmY : (m : ℝ) < Real.sqrt Y := by
      rw [Real.lt_sqrt (by positivity)]
      exact hm
    have hsY : Real.sqrt Y < z ^ 3 := by
      have h1 : Real.sqrt Y = Y ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow Y
      rw [h1, hz]
      have h2 : (Y ^ (1 / 6 + ε / 2)) ^ 3 = Y ^ (1 / 2 + 3 * ε / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ Y)]
        congr 1
        ring
      rw [h2]
      exact (Real.rpow_lt_rpow_left_iff hY).mpr (by linarith)
    linarith
  linarith

/-- The modulus of the block coefficient of `m` is at most twice its divisor
count: at most two block primes divide `m`, and the Möbius block contributes at
most `tau (m / p) ≤ tau m`. -/
private lemma coeff_norm_le (Y ε M D X B : ℝ) (m : ℕ) (hY : 1 < Y) (hε : 0 < ε)
    (hm0 : 0 < m) (hm : (m : ℝ) ^ 2 < Y) :
    ‖∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
        Y ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
        (p : ℝ) < Y ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
        p ∣ m)).filter
        (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
        Finset.sum (((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
          (r : ℝ) < Y ^ (1 / 6 + ε / 2))).filter
          (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D))
          (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℂ))‖ ≤ 2 * (m.divisors.card : ℝ) := by
  classical
  set P : Finset ℕ := ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
        Y ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
        (p : ℝ) < Y ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
        p ∣ m)).filter (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M) with hPdef
  have hP : ∀ p ∈ P, p.Prime ∧ Y ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧ p ∣ m := by
    intro p hp
    obtain ⟨hp1, -⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, hprime, hz1, -, hdvd⟩ := Finset.mem_filter.mp hp1
    exact ⟨hprime, hz1, hdvd⟩
  have hcard : P.card ≤ 2 := card_primes_le_two hY hε hm0 hm P hP
  have hmu : ∀ d : ℕ, ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 1 := by
    intro d
    rw [Complex.norm_intCast]
    have h := ArithmeticFunction.abs_moebius_le_one (n := d)
    have h2 : ((|ArithmeticFunction.moebius d| : ℤ) : ℝ) ≤ 1 := by exact_mod_cast h
    rwa [Int.cast_abs] at h2
  have hinner : ∀ p ∈ P,
      ‖∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
          (r : ℝ) < Y ^ (1 / 6 + ε / 2))).filter
          (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ (m.divisors.card : ℝ) := by
    intro p hp
    set E : Finset ℕ := ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
          (r : ℝ) < Y ^ (1 / 6 + ε / 2))).filter
          (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D) with hE
    have h1 : ‖∑ d ∈ E, ((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ (E.card : ℝ) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ d ∈ E, ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ ∑ _d ∈ E, (1 : ℝ) :=
            Finset.sum_le_sum (fun d _ => hmu d)
        _ = (E.card : ℝ) := by rw [Finset.sum_const]; simp
    have hsub : E ⊆ (m / p).divisors := by
      intro d hd
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).1
    have h2 : E.card ≤ (m / p).divisors.card := Finset.card_le_card hsub
    have h3 : (m / p).divisors.card ≤ m.divisors.card := by
      apply Finset.card_le_card
      intro d hd
      obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
      have hpdvd : p ∣ m := (hP p hp).2.2
      refine Nat.mem_divisors.mpr ⟨hdvd.trans (Nat.div_dvd_of_dvd hpdvd), hm0.ne'⟩
    calc ‖∑ d ∈ E, ((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ (E.card : ℝ) := h1
      _ ≤ (m.divisors.card : ℝ) := by
          have : (E.card : ℝ) ≤ ((m / p).divisors.card : ℝ) := by exact_mod_cast h2
          have : ((m / p).divisors.card : ℝ) ≤ (m.divisors.card : ℝ) := by exact_mod_cast h3
          linarith
  have hmain : ‖∑ p ∈ P, ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
          (r : ℝ) < Y ^ (1 / 6 + ε / 2))).filter
          (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 2 * (m.divisors.card : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ p ∈ P, ‖∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
            (r : ℝ) < Y ^ (1 / 6 + ε / 2))).filter
            (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
          ((ArithmeticFunction.moebius d : ℤ) : ℂ)‖
        ≤ ∑ _p ∈ P, (m.divisors.card : ℝ) := Finset.sum_le_sum hinner
      _ = (P.card : ℝ) * (m.divisors.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (m.divisors.card : ℝ) := by
          have : (P.card : ℝ) ≤ 2 := by exact_mod_cast hcard
          have : (0 : ℝ) ≤ (m.divisors.card : ℝ) := by positivity
          nlinarith
  simpa [hPdef] using hmain

/-- On the edge, the `m` of the short sum lie in an interval of length at most
`H Y^(-1/2) + 1` below `sqrt Y`. -/
private lemma edge_length_le (Y H t : ℝ) (hY : 0 < Y) (hH0 : 0 ≤ H) (hHY : 4 * H ≤ Y)
    (ht1 : Y - 2 * H ≤ t) :
    (((⌊Real.sqrt (t + H)⌋₊ - ⌊Real.sqrt t⌋₊ : ℕ)) : ℝ) ≤ H / Real.sqrt Y + 2 := by
  have ht0 : 0 < t := by linarith
  have hs : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY
  have h0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hmono : ⌊Real.sqrt t⌋₊ ≤ ⌊Real.sqrt (t + H)⌋₊ :=
    Nat.floor_le_floor (Real.sqrt_le_sqrt (by linarith))
  have hb : ((⌊Real.sqrt (t + H)⌋₊ : ℕ) : ℝ) ≤ Real.sqrt (t + H) :=
    Nat.floor_le (Real.sqrt_nonneg _)
  have ha : Real.sqrt t < ((⌊Real.sqrt t⌋₊ : ℕ) : ℝ) + 1 := by
    have := Nat.lt_floor_add_one (Real.sqrt t)
    linarith
  have hcast : (((⌊Real.sqrt (t + H)⌋₊ - ⌊Real.sqrt t⌋₊ : ℕ)) : ℝ) =
      ((⌊Real.sqrt (t + H)⌋₊ : ℕ) : ℝ) - ((⌊Real.sqrt t⌋₊ : ℕ) : ℝ) := by
    rw [Nat.cast_sub hmono]
  have hprod : (Real.sqrt (t + H) - Real.sqrt t) * (Real.sqrt (t + H) + Real.sqrt t) = H := by
    have e1 := Real.sq_sqrt (show (0 : ℝ) ≤ t + H by linarith)
    have e2 := Real.sq_sqrt ht0.le
    nlinarith
  have hsqrtY : Real.sqrt Y ≤ 2 * Real.sqrt t := by
    have h1 : Y ≤ 4 * t := by linarith
    have h2 : Real.sqrt Y ≤ Real.sqrt (4 * t) := Real.sqrt_le_sqrt h1
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)
    have h3 : Real.sqrt (4 * t) = 2 * Real.sqrt t := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4]
    linarith [h3 ▸ h2]
  have hdiff : Real.sqrt (t + H) - Real.sqrt t ≤ H / Real.sqrt Y := by
    have hgt : 0 < Real.sqrt (t + H) + Real.sqrt t := by linarith
    have hd0 : 0 ≤ Real.sqrt (t + H) - Real.sqrt t := by
      have := Real.sqrt_le_sqrt (show t ≤ t + H by linarith)
      linarith
    have hstep : Real.sqrt (t + H) - Real.sqrt t ≤ H / (Real.sqrt (t + H) + Real.sqrt t) := by
      rw [le_div_iff₀ hgt]
      linarith [hprod]
    refine hstep.trans ?_
    have h2sqrt : 2 * Real.sqrt t ≤ Real.sqrt (t + H) + Real.sqrt t := by
      have := Real.sqrt_le_sqrt (show t ≤ t + H by linarith)
      linarith
    have hden : Real.sqrt Y ≤ Real.sqrt (t + H) + Real.sqrt t := le_trans hsqrtY (by linarith)
    exact div_le_div_of_nonneg_left hH0 hs hden
  linarith

/-- The squared short sum on the edge is bounded by the divisor sum over the
interval of `m` it lives in. -/
private lemma edge_short_sum_sq_le (Y ε M D X B α t H : ℝ) (hY1 : 2 ≤ Y) (hε : 0 < ε)
    (hH0 : 0 ≤ H) (hHY : 4 * H ≤ Y) (ht1 : Y - 2 * H ≤ t) (ht2 : t ≤ Y) :
    ‖∑ m ∈ (squareWindow Y).filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
            Y ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
            (p : ℝ) < Y ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
            p ∣ m)).filter
            (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
          ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
              (r : ℝ) < Y ^ (1 / 6 + ε / 2))).filter
              (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
            ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
          fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2 ≤
      (4 * (((⌊Real.sqrt (t + H)⌋₊ - ⌊Real.sqrt t⌋₊ : ℕ)) : ℝ) *
          (1 + Real.log (⌊Real.sqrt (t + H)⌋₊ : ℝ))
        + 8 * Real.sqrt (⌊Real.sqrt (t + H)⌋₊ : ℝ) + 4) ^ 2 := by
  classical
  set a : ℕ := ⌊Real.sqrt t⌋₊ with ha
  set b : ℕ := ⌊Real.sqrt (t + H)⌋₊ with hbdef
  set W : Finset ℕ := (squareWindow Y).filter
    (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H) with hW
  have hY0 : 0 < Y := by linarith
  have ht0 : 0 < t := by linarith
  -- the window sits in the interval of `m`
  have hsub : W ⊆ Finset.Ioc a b := by
    intro m hm
    obtain ⟨hmW, h1, h2⟩ := Finset.mem_filter.mp hm
    have hmsq : Real.sqrt Y / 2 ≤ (m : ℝ) ∧ (m : ℝ) < Real.sqrt Y := by
      obtain ⟨-, hlo, hhi⟩ := Finset.mem_filter.mp hmW
      exact ⟨hlo, hhi⟩
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hlt : Real.sqrt t < (m : ℝ) := by
      have := Real.sqrt_lt_sqrt ht0.le h1
      rwa [Real.sqrt_sq hm0] at this
    have hle : (m : ℝ) ≤ Real.sqrt (t + H) := Real.le_sqrt_of_sq_le h2
    refine Finset.mem_Ioc.mpr ⟨?_, ?_⟩
    · have := Nat.floor_le (Real.sqrt_nonneg t)
      exact_mod_cast (lt_of_le_of_lt this hlt)
    · exact Nat.le_floor hle
  -- each coefficient is at most twice the divisor count
  have hcoeff : ∀ m ∈ W, ‖(∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
            Y ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
            (p : ℝ) < Y ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
            p ∣ m)).filter
            (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
          ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
              (r : ℝ) < Y ^ (1 / 6 + ε / 2))).filter
              (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
            ((ArithmeticFunction.moebius d : ℤ) : ℂ))‖ ≤ 2 * (m.divisors.card : ℝ) := by
    intro m hm
    obtain ⟨hmW, -, -⟩ := Finset.mem_filter.mp hm
    obtain ⟨-, hlo, hhi⟩ := Finset.mem_filter.mp hmW
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hmsq : (m : ℝ) ^ 2 < Y := by
      have h := Real.lt_sqrt (y := Y) hm0
      exact h.mp hhi
    have hpos : 0 < m := by
      have hsqrt : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY0
      have : (0 : ℝ) < (m : ℝ) := by linarith
      exact_mod_cast this
    exact coeff_norm_le Y ε M D X B m (by linarith) hε hpos hmsq
  have hbound : ‖∑ m ∈ W,
        (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
            Y ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
            (p : ℝ) < Y ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
            p ∣ m)).filter
            (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
          ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
              (r : ℝ) < Y ^ (1 / 6 + ε / 2))).filter
              (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
            ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
          fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ≤
      4 * ((b - a : ℕ) : ℝ) * (1 + Real.log (b : ℝ)) + 8 * Real.sqrt (b : ℝ) + 4 := by
    have h1 : ‖∑ m ∈ W,
        (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
            Y ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
            (p : ℝ) < Y ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
            p ∣ m)).filter
            (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
          ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
              (r : ℝ) < Y ^ (1 / 6 + ε / 2))).filter
              (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
            ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
          fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ≤
      ∑ m ∈ W, 2 * (m.divisors.card : ℝ) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m hm => ?_))
      have h1 : ‖fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ = 1 := Circle.norm_coe _
      rw [norm_mul, h1, mul_one]
      exact hcoeff m hm
    have h2 : ∑ m ∈ W, 2 * (m.divisors.card : ℝ) ≤
        2 * ∑ m ∈ Finset.Ioc a b, (m.divisors.card : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => by positivity)
    have h3 : 2 * ∑ m ∈ Finset.Ioc a b, (m.divisors.card : ℝ) ≤
        4 * ((b - a : ℕ) : ℝ) * (1 + Real.log (b : ℝ)) + 8 * Real.sqrt (b : ℝ) + 4 := by
      have hb1 : 1 ≤ b := by
        have h2 : (1 : ℝ) ^ 2 ≤ t + H := by norm_num; linarith
        have h1 : (1 : ℝ) ≤ Real.sqrt (t + H) := Real.le_sqrt_of_sq_le h2
        exact Nat.le_floor (by simpa using h1)
      have h := sum_tau_Ioc_le a b hb1
      linarith
    linarith
  exact pow_le_pow_left₀ (norm_nonneg _) hbound 2

/-- For large `X`, the estimates used in the edge arithmetic. -/
private lemma edge_large_X (A B ε : ℝ) (hA : 0 < A) (hε : 0 < ε) (hε' : ε < 1 / 6)
    (hAB : A + 2 ≤ 4 * B) :
    ∃ X1 : ℝ, 2 ≤ X1 ∧ ∀ X : ℝ, X1 ≤ X →
      2 ≤ windowY X ε ∧
      10 ≤ Real.log X ∧
      4096 * Real.log X ^ (A + 2 + 4 * B) ≤ X ^ (7 / 18 + ε) ∧
      4096 * Real.log X ^ (A + 4 * B) ≤ X ^ (7 / 72 + 3 * ε / 4) ∧
      2 * windowY X ε ≤ X ∧
      4 ≤ (Real.log X ^ B) ^ 4 ∧
      2 * Real.sqrt (windowY X ε) ≤ X := by
  have e0 : ∀ᶠ X : ℝ in Filter.atTop, 2 ≤ X ^ (7 / 12 + ε / 2) :=
    (tendsto_rpow_atTop (by linarith : 0 < 7 / 12 + ε / 2)).eventually_ge_atTop 2
  have e1 : ∀ᶠ X : ℝ in Filter.atTop, 10 ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually_ge_atTop 10
  have e2 : ∀ᶠ X : ℝ in Filter.atTop,
      ‖Real.log X ^ (A + 2 + 4 * B)‖ ≤ 1 * ‖X ^ ((7 / 18 + ε) / 2)‖ :=
    (isLittleO_log_rpow_rpow_atTop (A + 2 + 4 * B) (by linarith : 0 < (7 / 18 + ε) / 2)).bound
      one_pos
  have e3 : ∀ᶠ X : ℝ in Filter.atTop,
      ‖Real.log X ^ (A + 4 * B)‖ ≤ 1 * ‖X ^ ((7 / 72 + 3 * ε / 4) / 2)‖ :=
    (isLittleO_log_rpow_rpow_atTop (A + 4 * B)
      (by linarith : 0 < (7 / 72 + 3 * ε / 4) / 2)).bound one_pos
  have e4 : ∀ᶠ X : ℝ in Filter.atTop, 4096 ≤ X ^ ((7 / 18 + ε) / 2) :=
    (tendsto_rpow_atTop (by linarith : 0 < (7 / 18 + ε) / 2)).eventually_ge_atTop 4096
  have e5 : ∀ᶠ X : ℝ in Filter.atTop, 4096 ≤ X ^ ((7 / 72 + 3 * ε / 4) / 2) :=
    (tendsto_rpow_atTop (by linarith : 0 < (7 / 72 + 3 * ε / 4) / 2)).eventually_ge_atTop 4096
  have e6 : ∀ᶠ X : ℝ in Filter.atTop, 2 * X ^ (7 / 12 + ε / 2) ≤ X := by
    have h : ∀ᶠ X : ℝ in Filter.atTop, 2 ≤ X ^ (1 / 12 - ε / 2) :=
      (tendsto_rpow_atTop (by linarith : 0 < 1 / 12 - ε / 2)).eventually_ge_atTop 2
    filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with X hX hX1
    have h0 : (0 : ℝ) < X := by linarith
    have hp : 0 < X ^ (7 / 12 + ε / 2) := Real.rpow_pos_of_pos h0 _
    have he : X ^ (1 / 12 - ε / 2) * X ^ (7 / 12 + ε / 2) = X ^ (2 / 3 : ℝ) := by
      have h := Real.rpow_add h0 (1 / 12 - ε / 2) (7 / 12 + ε / 2)
      rw [show 1 / 12 - ε / 2 + (7 / 12 + ε / 2) = 2 / 3 by ring] at h
      exact h.symm
    have hle : X ^ (2 / 3 : ℝ) ≤ X := by
      have h1 : X ^ (2 / 3 : ℝ) ≤ X ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num : (2 : ℝ) / 3 ≤ 1)
      rwa [Real.rpow_one] at h1
    calc 2 * X ^ (7 / 12 + ε / 2) ≤ X ^ (1 / 12 - ε / 2) * X ^ (7 / 12 + ε / 2) :=
          mul_le_mul_of_nonneg_right hX hp.le
      _ = X ^ (2 / 3 : ℝ) := he
      _ ≤ X := hle
  have e7 : ∀ᶠ X : ℝ in Filter.atTop, 4 ≤ (Real.log X ^ B) ^ 4 := by
    have h : ∀ᶠ X : ℝ in Filter.atTop, 2 ≤ Real.log X ^ B :=
      ((tendsto_rpow_atTop (by linarith : 0 < B)).comp Real.tendsto_log_atTop).eventually_ge_atTop 2
    filter_upwards [h] with X hX
    have h4 : (2 : ℝ) ^ 4 ≤ (Real.log X ^ B) ^ 4 := pow_le_pow_left₀ (by norm_num) hX 4
    norm_num at h4
    linarith
  have e8 : ∀ᶠ X : ℝ in Filter.atTop, 2 * Real.sqrt (X ^ (7 / 12 + ε / 2)) ≤ X := by
    have h : ∀ᶠ X : ℝ in Filter.atTop, 2 ≤ X ^ (1 / 24 - ε / 4) :=
      (tendsto_rpow_atTop (by linarith : 0 < 1 / 24 - ε / 4)).eventually_ge_atTop 2
    filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with X hX hX1
    have h0 : (0 : ℝ) < X := by linarith
    have hs : Real.sqrt (X ^ (7 / 12 + ε / 2)) = X ^ (7 / 24 + ε / 4) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul h0.le]
      ring_nf
    rw [hs]
    have hp : 0 < X ^ (7 / 24 + ε / 4) := Real.rpow_pos_of_pos h0 _
    have he : X ^ (1 / 24 - ε / 4) * X ^ (7 / 24 + ε / 4) = X ^ (1 / 3 : ℝ) := by
      have h := Real.rpow_add h0 (1 / 24 - ε / 4) (7 / 24 + ε / 4)
      rw [show 1 / 24 - ε / 4 + (7 / 24 + ε / 4) = 1 / 3 by ring] at h
      exact h.symm
    have hle : X ^ (1 / 3 : ℝ) ≤ X := by
      have h1 : X ^ (1 / 3 : ℝ) ≤ X ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num : (1 : ℝ) / 3 ≤ 1)
      rwa [Real.rpow_one] at h1
    calc 2 * X ^ (7 / 24 + ε / 4) ≤ X ^ (1 / 24 - ε / 4) * X ^ (7 / 24 + ε / 4) :=
          mul_le_mul_of_nonneg_right hX hp.le
      _ = X ^ (1 / 3 : ℝ) := he
      _ ≤ X := hle
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (e0.and (e1.and (e2.and (e3.and (e4.and (e5.and (e6.and (e7.and e8))))))))
  refine ⟨max N 2, le_max_right _ _, fun X hX => ?_⟩
  obtain ⟨h0', h1, h2, h3, h4, h5, h6, h7, h8⟩ := hN X ((le_max_left _ _).trans hX)
  have hX0 : (0 : ℝ) < X := by
    have h2 : (2 : ℝ) ≤ X := by linarith [le_max_right N 2, hX]
    linarith
  have hXp1 : (0 : ℝ) ≤ X ^ ((7 / 18 + ε) / 2) := Real.rpow_nonneg hX0.le _
  have hXp2 : (0 : ℝ) ≤ X ^ ((7 / 72 + 3 * ε / 4) / 2) := Real.rpow_nonneg hX0.le _
  refine ⟨by simpa [windowY] using h0', h1, ?_, ?_, ?_, h7, ?_⟩
  · have hn2 : 0 ≤ Real.log X ^ (A + 2 + 4 * B) := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_of_nonneg hn2, Real.norm_of_nonneg hXp1, one_mul] at h2
    have he : X ^ ((7 / 18 + ε) / 2) * X ^ ((7 / 18 + ε) / 2) = X ^ (7 / 18 + ε) := by
      have h := Real.rpow_add hX0 ((7 / 18 + ε) / 2) ((7 / 18 + ε) / 2)
      rw [show (7 / 18 + ε) / 2 + (7 / 18 + ε) / 2 = 7 / 18 + ε by ring] at h
      exact h.symm
    calc 4096 * Real.log X ^ (A + 2 + 4 * B)
        ≤ X ^ ((7 / 18 + ε) / 2) * X ^ ((7 / 18 + ε) / 2) :=
          mul_le_mul h4 h2 hn2 hXp1
      _ = X ^ (7 / 18 + ε) := he
  · have hn2 : 0 ≤ Real.log X ^ (A + 4 * B) := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_of_nonneg hn2, Real.norm_of_nonneg hXp2, one_mul] at h3
    have he : X ^ ((7 / 72 + 3 * ε / 4) / 2) * X ^ ((7 / 72 + 3 * ε / 4) / 2) =
        X ^ (7 / 72 + 3 * ε / 4) := by
      have h := Real.rpow_add hX0 ((7 / 72 + 3 * ε / 4) / 2) ((7 / 72 + 3 * ε / 4) / 2)
      rw [show (7 / 72 + 3 * ε / 4) / 2 + (7 / 72 + 3 * ε / 4) / 2 = 7 / 72 + 3 * ε / 4 by ring] at h
      exact h.symm
    calc 4096 * Real.log X ^ (A + 4 * B)
        ≤ X ^ ((7 / 72 + 3 * ε / 4) / 2) * X ^ ((7 / 72 + 3 * ε / 4) / 2) :=
          mul_le_mul h5 h3 hn2 hXp2
      _ = X ^ (7 / 72 + 3 * ε / 4) := he
  · simpa [windowY] using h6
  · simpa [windowY] using h8

set_option maxHeartbeats 4000000 in
/-- The pointwise edge bound in the form used by the integral estimate. -/
private lemma edge_pointwise (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α M D : ℝ, ∀ t : ℝ, windowY X ε - 2 * H ≤ t → t ≤ windowY X ε →
        ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2 ≤
            C * H / Real.log X ^ A := by
  refine ⟨(A + 3) / 4, by linarith, fun B hB ε hε hε' => ?_⟩
  have hAB : A + 2 ≤ 4 * B := by linarith
  obtain ⟨X1, hX1, hlarge⟩ := edge_large_X A B ε hA hε hε' hAB
  refine ⟨2400, max X1 2, by norm_num, hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hlo hhi α M D t ht1 ht2
  have hX1' : X1 ≤ X := le_trans (le_max_left X1 2) hX
  have hX2 : (2 : ℝ) ≤ X := le_trans (le_max_right X1 2) hX
  obtain ⟨hY2, hL10, hC1, hC2, hC3, hC4, hC5⟩ := hlarge X hX1'
  set Y : ℝ := windowY X ε with hYdef
  set L : ℝ := Real.log X with hLdef
  have hX0 : (0 : ℝ) < X := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hY0 : 0 < Y := by
    have h1 : 0 < X ^ (7 / 12 + ε / 2) := Real.rpow_pos_of_pos hX0 _
    simpa [Y, windowY] using h1
  -- rewrite the negative power
  have hzpow : (L ^ B) ^ (-4 : ℤ) = ((L ^ B) ^ 4)⁻¹ := by
    rw [zpow_neg]; norm_cast
  have hP4 : (0 : ℝ) < (L ^ B) ^ 4 := by
    have h : 0 < L ^ B := Real.rpow_pos_of_pos (by linarith) _
    positivity
  have hL4 : (L ^ B) ^ 4 = L ^ (4 * B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ L)]
    ring_nf
  rw [hzpow] at hlo hhi
  have hlo' : X ^ (7 / 18 + ε) / L ^ (4 * B) ≤ H := by
    rw [← hL4]
    calc X ^ (7 / 18 + ε) / (L ^ B) ^ 4 = X ^ (7 / 18 + ε) * ((L ^ B) ^ 4)⁻¹ := by
          rw [div_eq_mul_inv]
      _ ≤ H := hlo
  have hhi' : H ≤ Y / L ^ (4 * B) := by
    rw [← hL4]
    calc H ≤ Y * ((L ^ B) ^ 4)⁻¹ := hhi
      _ = Y / (L ^ B) ^ 4 := by rw [div_eq_mul_inv]
  have hH0 : 0 ≤ H := by
    have h1 : 0 < X ^ (7 / 18 + ε) := Real.rpow_pos_of_pos hX0 _
    have h2 : 0 < L ^ (4 * B) := Real.rpow_pos_of_pos (by linarith) _
    have h3 : 0 < X ^ (7 / 18 + ε) / L ^ (4 * B) := div_pos h1 h2
    linarith
  have hHle : 4 * H ≤ Y := by
    have h2 : H ≤ Y * (L ^ (4 * B))⁻¹ := by
      rw [div_eq_mul_inv] at hhi'; exact hhi'
    have h3 : (L ^ (4 * B))⁻¹ ≤ 1 / 4 := by
      rw [inv_le_iff_one_le_mul₀ (Real.rpow_pos_of_pos (by linarith) _)]
      have h4 : (4 : ℝ) ≤ L ^ (4 * B) := by
        rw [← hL4]; exact hC4
      linarith
    have h4 : H ≤ Y * (1 / 4) := by
      calc H ≤ Y * (L ^ (4 * B))⁻¹ := h2
        _ ≤ Y * (1 / 4) := by
            apply mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  -- the pointwise bound
  set l : ℝ := (((⌊Real.sqrt (t + H)⌋₊ - ⌊Real.sqrt t⌋₊ : ℕ)) : ℝ) with hldef
  set b : ℕ := ⌊Real.sqrt (t + H)⌋₊ with hbdef
  have hsh := edge_short_sum_sq_le Y ε M D X B α t H hY2 hε hH0 hHle ht1 ht2
  have hl : l ≤ H / Real.sqrt Y + 2 := edge_length_le Y H t hY0 hH0 hHle ht1
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := by
    have h2 : (1 : ℝ) ^ 2 ≤ t + H := by norm_num; linarith
    have h1 : (1 : ℝ) ≤ Real.sqrt (t + H) := Real.le_sqrt_of_sq_le h2
    have h3 : (1 : ℕ) ≤ b := by
      rw [hbdef]
      exact Nat.le_floor (n := 1) (by push_cast; exact h1)
    exact_mod_cast h3
  have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
  have hble : ((b : ℕ) : ℝ) ≤ 2 * Real.sqrt Y := by
    have h1 : ((b : ℕ) : ℝ) ≤ Real.sqrt (t + H) := Nat.floor_le (Real.sqrt_nonneg _)
    have h2 : t + H ≤ 2 * Y := by linarith
    have h3 : Real.sqrt (t + H) ≤ Real.sqrt (2 * Y) := Real.sqrt_le_sqrt h2
    have h4 : Real.sqrt (2 * Y) ≤ 2 * Real.sqrt Y := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2,
        Real.sqrt_nonneg Y, Real.sq_sqrt hY0.le]
    linarith
  have hbX : ((b : ℕ) : ℝ) ≤ X := by linarith [hble, hC5]
  have hlogb : Real.log (b : ℝ) ≤ L := by
    calc Real.log (b : ℝ) ≤ Real.log X := Real.log_le_log hbpos hbX
      _ = L := rfl
  have hlogb0 : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg hb1
  have hlog2 : 1 + Real.log (b : ℝ) ≤ 2 * L := by linarith
  have hsqrtb : Real.sqrt (b : ℝ) ≤ 2 * Y ^ (1 / 4 : ℝ) := by
    have h1 : Real.sqrt (b : ℝ) ≤ Real.sqrt (2 * Real.sqrt Y) := Real.sqrt_le_sqrt hble
    have h2 : Real.sqrt (2 * Real.sqrt Y) ≤ 2 * Y ^ (1 / 4 : ℝ) := by
      have hs : Real.sqrt (Real.sqrt Y) = Y ^ (1 / 4 : ℝ) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hY0.le]
        congr 1
        norm_num
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), hs]
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2,
        Real.rpow_nonneg hY0.le (1/4 : ℝ)]
    linarith
  have hKb1 : (4 * l * (1 + Real.log (b : ℝ)) + 8 * Real.sqrt (b : ℝ) + 4) ^ 2 ≤
      (8 * H * L / Real.sqrt Y + 16 * L + 16 * Y ^ (1 / 4 : ℝ) + 4) ^ 2 := by
    have h1 : 4 * l * (1 + Real.log (b : ℝ)) + 8 * Real.sqrt (b : ℝ) + 4 ≤
        8 * H * L / Real.sqrt Y + 16 * L + 16 * Y ^ (1 / 4 : ℝ) + 4 := by
      have ha : 4 * l * (1 + Real.log (b : ℝ)) ≤ 8 * H * L / Real.sqrt Y + 16 * L := by
        have h0 : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY0
        have h2 : 4 * l * (1 + Real.log (b : ℝ)) ≤ 4 * (H / Real.sqrt Y + 2) * (2 * L) := by
          apply mul_le_mul
          · linarith
          · exact hlog2
          · linarith [hlogb0]
          · linarith
        have h3 : 4 * (H / Real.sqrt Y + 2) * (2 * L) = 8 * H * L / Real.sqrt Y + 16 * L := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
        linarith [h3 ▸ h2]
      have hb2 : 8 * Real.sqrt (b : ℝ) ≤ 16 * Y ^ (1 / 4 : ℝ) := by linarith [hsqrtb]
      linarith
    exact pow_le_pow_left₀ (by positivity) h1 2
  have hsq : (8 * H * L / Real.sqrt Y + 16 * L + 16 * Y ^ (1 / 4 : ℝ) + 4) ^ 2 ≤
      256 * H ^ 2 * L ^ 2 / Y + 1024 * L ^ 2 + 1024 * Real.sqrt Y + 64 := by
    have hY14 : (Y ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt Y := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le, Real.sqrt_eq_rpow]
      congr 1
      norm_num
    have h1 : (8 * H * L / Real.sqrt Y + 16 * L + 16 * Y ^ (1 / 4 : ℝ) + 4) ^ 2 ≤
        2 * ((8 * H * L / Real.sqrt Y + 16 * L) ^ 2 + (16 * Y ^ (1 / 4 : ℝ) + 4) ^ 2) := by
      nlinarith [sq_nonneg (8 * H * L / Real.sqrt Y + 16 * L - (16 * Y ^ (1 / 4 : ℝ) + 4))]
    have h2 : (8 * H * L / Real.sqrt Y + 16 * L) ^ 2 ≤
        2 * ((8 * H * L / Real.sqrt Y) ^ 2 + (16 * L) ^ 2) := by
      nlinarith [sq_nonneg (8 * H * L / Real.sqrt Y - 16 * L)]
    have h3 : (16 * Y ^ (1 / 4 : ℝ) + 4) ^ 2 ≤ 2 * ((16 * Y ^ (1 / 4 : ℝ)) ^ 2 + 4 ^ 2) := by
      nlinarith [sq_nonneg (16 * Y ^ (1 / 4 : ℝ) - 4)]
    have e1 : (8 * H * L / Real.sqrt Y) ^ 2 = 64 * H ^ 2 * L ^ 2 / Y := by
      have hYsq : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY0.le
      rw [div_eq_mul_inv, mul_pow, inv_pow, hYsq, div_eq_mul_inv]
      ring
    have e2 : (16 * Y ^ (1 / 4 : ℝ)) ^ 2 = 256 * Real.sqrt Y := by
      rw [show (16 * Y ^ (1 / 4 : ℝ)) ^ 2 = 256 * (Y ^ (1 / 4 : ℝ)) ^ 2 by ring_nf, hY14]
    have e3 : (16 * L) ^ 2 = 256 * L ^ 2 := by ring
    have e4 : (4 : ℝ) ^ 2 = 16 := by norm_num
    have step1 : 2 * ((8 * H * L / Real.sqrt Y + 16 * L) ^ 2 + (16 * Y ^ (1 / 4 : ℝ) + 4) ^ 2) ≤
        256 * H ^ 2 * L ^ 2 / Y + 1024 * L ^ 2 + 1024 * Real.sqrt Y + 64 := by
      have g2 : 2 * (8 * H * L / Real.sqrt Y + 16 * L) ^ 2 ≤
          4 * ((8 * H * L / Real.sqrt Y) ^ 2 + (16 * L) ^ 2) := by linarith [h2]
      have g3 : 2 * (16 * Y ^ (1 / 4 : ℝ) + 4) ^ 2 ≤
          4 * ((16 * Y ^ (1 / 4 : ℝ)) ^ 2 + 4 ^ 2) := by linarith [h3]
      have g2' : 2 * (8 * H * L / Real.sqrt Y + 16 * L) ^ 2 ≤
          256 * H ^ 2 * L ^ 2 / Y + 1024 * L ^ 2 := by
        calc 2 * (8 * H * L / Real.sqrt Y + 16 * L) ^ 2
            ≤ 4 * ((8 * H * L / Real.sqrt Y) ^ 2 + (16 * L) ^ 2) := g2
          _ = 4 * (64 * H ^ 2 * L ^ 2 / Y + 256 * L ^ 2) := by rw [e1, e3]
          _ = 256 * H ^ 2 * L ^ 2 / Y + 1024 * L ^ 2 := by ring
      have g3' : 2 * (16 * Y ^ (1 / 4 : ℝ) + 4) ^ 2 ≤ 1024 * Real.sqrt Y + 64 := by
        calc 2 * (16 * Y ^ (1 / 4 : ℝ) + 4) ^ 2
            ≤ 4 * ((16 * Y ^ (1 / 4 : ℝ)) ^ 2 + 4 ^ 2) := g3
          _ = 4 * (256 * Real.sqrt Y + 16) := by rw [e2, e4]
          _ = 1024 * Real.sqrt Y + 64 := by ring
      linarith [g2', g3']
    linarith [h1, step1]
  -- key rpow facts
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL1
  have hL0 : (0 : ℝ) ≤ L := hLpos.le
  have hLA : (0 : ℝ) < L ^ A := Real.rpow_pos_of_pos hLpos _
  have hL4B : (0 : ℝ) < L ^ (4 * B) := Real.rpow_pos_of_pos hLpos _
  have hPA : L ^ (A + 2) ≤ L ^ (4 * B) :=
    Real.rpow_le_rpow_of_exponent_le hL1 hAB
  have hsplitA : L ^ A * L ^ 2 = L ^ (A + 2) := by
    rw [show (L : ℝ) ^ 2 = L ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast]]
    rw [← Real.rpow_add hLpos]
    push_cast
    norm_num
  have hsplitA4B : L ^ (A + 2 + 4 * B) * (L ^ (4 * B))⁻¹ = L ^ (A + 2) := by
    have h1 : L ^ (A + 2 + 4 * B) = L ^ (A + 2) * L ^ (4 * B) := by
      rw [← Real.rpow_add hLpos]
    calc L ^ (A + 2 + 4 * B) * (L ^ (4 * B))⁻¹
        = (L ^ (A + 2) * L ^ (4 * B)) * (L ^ (4 * B))⁻¹ := by rw [h1]
      _ = L ^ (A + 2) * (L ^ (4 * B) * (L ^ (4 * B))⁻¹) := by ring
      _ = L ^ (A + 2) * 1 := by rw [mul_inv_cancel₀ hL4B.ne']
      _ = L ^ (A + 2) := by ring
  have hH1 : 1024 * L ^ (A + 2) ≤ H := by
    have h1 : 1024 * L ^ (A + 2 + 4 * B) ≤ X ^ (7 / 18 + ε) := by
      calc 1024 * L ^ (A + 2 + 4 * B) ≤ 4096 * L ^ (A + 2 + 4 * B) := by
            apply mul_le_mul_of_nonneg_right (by norm_num : (1024:ℝ) ≤ 4096) (by positivity)
        _ ≤ X ^ (7 / 18 + ε) := hC1
    have h2 : 1024 * L ^ (A + 2 + 4 * B) * (L ^ (4 * B))⁻¹ ≤
        X ^ (7 / 18 + ε) * (L ^ (4 * B))⁻¹ :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : X ^ (7 / 18 + ε) * (L ^ (4 * B))⁻¹ ≤ H := by
      simpa [div_eq_mul_inv] using hlo'
    calc 1024 * L ^ (A + 2) = 1024 * (L ^ (A + 2 + 4 * B) * (L ^ (4 * B))⁻¹) := by
          rw [hsplitA4B]
      _ = 1024 * L ^ (A + 2 + 4 * B) * (L ^ (4 * B))⁻¹ := by ring
      _ ≤ H := h2.trans h3
  have hsqrtY : Real.sqrt Y = X ^ (7 / 24 + ε / 4) := by
    rw [hYdef, windowY, Real.sqrt_eq_rpow, ← Real.rpow_mul hX0.le]
    congr 1
    ring
  have hH2 : 1024 * Real.sqrt Y * L ^ A ≤ H := by
    have hsplitX : X ^ (7 / 18 + ε) = X ^ (7 / 72 + 3 * ε / 4) * Real.sqrt Y := by
      have h := Real.rpow_add hX0 (7 / 72 + 3 * ε / 4) (7 / 24 + ε / 4)
      rw [show 7 / 72 + 3 * ε / 4 + (7 / 24 + ε / 4) = 7 / 18 + ε by ring] at h
      rw [hsqrtY]
      exact h
    have h1 : 1024 * L ^ (A + 4 * B) ≤ X ^ (7 / 72 + 3 * ε / 4) := by
      calc 1024 * L ^ (A + 4 * B) ≤ 4096 * L ^ (A + 4 * B) := by
            apply mul_le_mul_of_nonneg_right (by norm_num : (1024:ℝ) ≤ 4096) (by positivity)
        _ ≤ X ^ (7 / 72 + 3 * ε / 4) := hC2
    have h2 : 1024 * L ^ (A + 4 * B) * Real.sqrt Y ≤
        X ^ (7 / 72 + 3 * ε / 4) * Real.sqrt Y :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : 1024 * L ^ (A + 4 * B) * Real.sqrt Y * (L ^ (4 * B))⁻¹ ≤
        X ^ (7 / 18 + ε) * (L ^ (4 * B))⁻¹ := by
      rw [hsplitX]
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    have h4 : X ^ (7 / 18 + ε) * (L ^ (4 * B))⁻¹ ≤ H := by
      simpa [div_eq_mul_inv] using hlo'
    have h5 : 1024 * L ^ (A + 4 * B) * Real.sqrt Y * (L ^ (4 * B))⁻¹ =
        1024 * Real.sqrt Y * L ^ A := by
      have h6 : L ^ (A + 4 * B) * (L ^ (4 * B))⁻¹ = L ^ A := by
        have h7 : L ^ (A + 4 * B) = L ^ A * L ^ (4 * B) := by
          rw [← Real.rpow_add hLpos]
        calc L ^ (A + 4 * B) * (L ^ (4 * B))⁻¹
            = (L ^ A * L ^ (4 * B)) * (L ^ (4 * B))⁻¹ := by rw [h7]
          _ = L ^ A * (L ^ (4 * B) * (L ^ (4 * B))⁻¹) := by ring
          _ = L ^ A * 1 := by rw [mul_inv_cancel₀ hL4B.ne']
          _ = L ^ A := by ring
      calc 1024 * L ^ (A + 4 * B) * Real.sqrt Y * (L ^ (4 * B))⁻¹
          = 1024 * Real.sqrt Y * (L ^ (A + 4 * B) * (L ^ (4 * B))⁻¹) := by ring
        _ = 1024 * Real.sqrt Y * L ^ A := by rw [h6]
    rw [h5] at h3
    exact h3.trans h4
  -- the four summands
  have hdom1 : 256 * H ^ 2 * L ^ 2 / Y * L ^ A ≤ 256 * H := by
    have h1 : H / Y ≤ (L ^ (4 * B))⁻¹ := by
      rw [div_le_iff₀ hY0]
      calc H ≤ Y * (L ^ (4 * B))⁻¹ := by rw [div_eq_mul_inv] at hhi'; exact hhi'
        _ = (L ^ (4 * B))⁻¹ * Y := by ring
    have h2 : 256 * H ^ 2 * L ^ 2 / Y * L ^ A = 256 * (H * (H / Y) * L ^ (A + 2)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, ← hsplitA]
      ring
    rw [h2]
    have h3 : H * (H / Y) * L ^ (A + 2) ≤ H * (L ^ (4 * B))⁻¹ * L ^ (4 * B) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left h1 hH0
      · exact hPA
      · positivity
      · positivity
    have h4 : H * (L ^ (4 * B))⁻¹ * L ^ (4 * B) = H := by
      rw [mul_assoc, inv_mul_cancel₀ hL4B.ne', mul_one]
    calc 256 * (H * (H / Y) * L ^ (A + 2)) ≤ 256 * (H * (L ^ (4 * B))⁻¹ * L ^ (4 * B)) := by
          linarith [h3]
      _ = 256 * H := by rw [h4]
  have hdom2 : 1024 * L ^ 2 * L ^ A ≤ 1024 * H := by
    have h2 : (1024 : ℝ) * L ^ 2 * L ^ A = 1024 * (L ^ A * L ^ 2) := by ring
    rw [h2, hsplitA]
    linarith [hH1]
  have hdom3 : 1024 * Real.sqrt Y * L ^ A ≤ 1024 * H := by linarith [hH2]
  have hdom4 : 64 * L ^ A ≤ 64 * H := by
    have h1 : L ^ A ≤ L ^ (A + 2) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    linarith [hH1]
  have hexpand : (256 * H ^ 2 * L ^ 2 / Y + 1024 * L ^ 2 + 1024 * Real.sqrt Y + 64) * L ^ A =
      256 * H ^ 2 * L ^ 2 / Y * L ^ A + 1024 * L ^ 2 * L ^ A +
        1024 * Real.sqrt Y * L ^ A + 64 * L ^ A := by ring
  have hkey : (8 * H * L / Real.sqrt Y + 16 * L + 16 * Y ^ (1 / 4 : ℝ) + 4) ^ 2 ≤
      2400 * H / L ^ A := by
    rw [le_div_iff₀ hLA]
    have h1 := mul_le_mul_of_nonneg_right hsq hLA.le
    rw [hexpand] at h1
    linarith [h1, hdom1, hdom2, hdom3, hdom4]
  exact le_trans (le_trans hsh hKb1) hkey


/-- LEAF: P0088 page 12, Case 3 of the proof of Lemma 3.4 on the edge stretch
t in [Y - 2H, Y], where the squareWindow Y filter cuts the short sum at m^2 < Y.
Class HARD. Not treated in the paper. As for Cases 1 and 2 in
SecondDyadicCases1122, the trivial bound fails since the coefficient is bounded
only by a power of tau of m; it needs a Shiu type mean bound for tau powers over
the short interval of m near Y^(1/2) of length about H Y^(-1/2), or a smoothing. -/
theorem case3_edge (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        ∀ D : ℝ, H / (Real.sqrt (windowY X ε) * Real.log X ^ B) < D →
        (∫ t in windowY X ε - 2 * H..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B0, hB0, hpt⟩ := edge_pointwise A hA
  refine ⟨B0, hB0, fun B hB ε hε hε' => ?_⟩
  obtain ⟨C, X0, hC, hX0, k⟩ := hpt B hB ε hε hε'
  refine ⟨2 * C, X0, by linarith, hX0, ?_⟩
  intro X H hX hlo hhi α q a hcop hqP hqQ hclose M hM htop hlow D hD
  have hX2 : (2 : ℝ) ≤ X := hX0.trans hX
  have hLpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hH0 : 0 ≤ H := by
    have h1 : 0 ≤ X ^ (7 / 18 + ε) := Real.rpow_nonneg (by linarith) _
    have h2 : 0 ≤ (Real.log X ^ B) ^ (-4 : ℤ) :=
      zpow_nonneg (Real.rpow_nonneg hLpos.le _) _
    exact (mul_nonneg h1 h2).trans hlo
  have hab : windowY X ε - 2 * H ≤ windowY X ε := by linarith
  rw [show 2 * C * H ^ 2 / Real.log X ^ A =
      ∫ _t in windowY X ε - 2 * H..windowY X ε, (C * H / Real.log X ^ A) by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring]
  refine intervalIntegral.integral_mono_on hab (short_sum_sq_intervalIntegrable _ _ _ _ _)
    intervalIntegrable_const ?_
  intro t ht
  exact k X H hX hlo hhi α M D t ht.1 ht.2

/-- PROVED from case3_interior and case3_edge, CONDITIONAL ON them. The exact
statement of Split1122SecondDyadicBlock.case3_large_D: the integral over [Y/4, Y] is the sum
of the integrals over [Y/4, Y - 2H] and [Y - 2H, Y]. -/
theorem case3_large_D_of_split (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        ∀ D : ℝ, H / (Real.sqrt (windowY X ε) * Real.log X ^ B) < D →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := case3_interior A hA
  obtain ⟨B2, hB2, h2⟩ := case3_edge A hA
  refine ⟨max B1 B2, lt_max_of_lt_left hB1, fun B hB ε hε hε' => ?_⟩
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε hε'
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B ((le_max_right _ _).trans hB) ε hε hε'
  refine ⟨C1 + C2, max X1 X2, add_pos hC1 hC2, hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hlo hhi α q a hcop hqP hqQ hclose M hM htop hlow D hD
  have e1 := k1 X H ((le_max_left _ _).trans hX) hlo hhi α q a hcop hqP hqQ hclose
    M hM htop hlow D hD
  have e2 := k2 X H ((le_max_right _ _).trans hX) hlo hhi α q a hcop hqP hqQ hclose
    M hM htop hlow D hD
  refine le_of_eq_of_le (intervalIntegral.integral_add_adjacent_intervals
    (b := windowY X ε - 2 * H) ?_ ?_).symm ?_
  · exact short_sum_sq_intervalIntegrable _ _ _ _ _
  · exact short_sum_sq_intervalIntegrable _ _ _ _ _
  · calc _ ≤ C1 * H ^ 2 / Real.log X ^ A + C2 * H ^ 2 / Real.log X ^ A := add_le_add e1 e2
      _ = (C1 + C2) * H ^ 2 / Real.log X ^ A := by ring

/-- PROVED. The assembly has the exact type of the leaf. -/
example : type_of% @Split1122SecondDyadicBlock.case3_large_D := case3_large_D_of_split

end LeanLab.KumchevLiu2007.SecondDyadicCase3Split1122

#print axioms LeanLab.KumchevLiu2007.SecondDyadicCase3Split1122.case3_large_D_of_split
