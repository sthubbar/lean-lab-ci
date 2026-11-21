/-
P0069 Baker Harman Pintz 1997, pages 48, 49 and 53. Deepening pass, cuts the four piece leaves
`upslack_piece_g_mean_square`, `upslack_piece_h_mean_square`, `upslack_piece_j_mean_square` and
`upslack_piece_kept_mean_square` of Prep1121UpslackLemma29. Page 53: "We use Lemma 34 to obtain
(5.1) and (5.2) for g_m, h_m and j_m", and Lemma 33 for the kept part of k_m. Lemma 34 on page
49, read from the page image: if `b_m = sum over nl = m, n <= Y^(1/2 + theta2/4 - 2 eps)` of
`a_n psi(l, Y^c1)` with `(a_n)` satisfying 3.1, then 5.1 and 5.2 hold. Here Lemma 34 is two
shared LEAFs, one per display, stated for any `b` that has that form on J for `Y >= 2`; g and h
are shown to have that form, PROVED, with `a_n` the indicator of `n = 1` and of the primes in
`[Y^c1, Y^c4)`; for j the form, with `a_n` counting `n = p1 p2`, is a MEDIUM leaf. The bridge of
Prep1121DUpslackBridge then gives the window mean square through Lemma 29.
New file, no new definition, no existing statement changed.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Prep1121DUpslackBridge

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open MeasureTheory

/-- LEAF: P0069 page 49, Lemma 34, the conclusion 5.1 on page 43, with the page 19 set E and its
size from page 3. If `b` is on J the sum over `nl = m`, `n <= Y^(1/2 + theta2/4 - 2 eps)`, of
`a_n psi(l, Y^c1)` with `(a_n)` satisfying 3.1, then 5.1 holds over `E^c` minus the principal
character. The paper's proof: Buchstab's identity, Lemma 30 for `f_m`, Lemma 5 for 3.2,
Lemma 33 when `P > Y^eps`, and the iterated decomposition of Lemma 13 case ii otherwise.
CONDITIONAL on the cited Theorem 4 and Lemma 9. HARD. -/
theorem upD_lemma34_51 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a b : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (hrep : ∀ x : ℝ, 2 ≤ x ^ (11 / 20 + ε) → ∀ k ∈ rightInterval ε x,
      b x k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * upperRough (k / n) ((x ^ (11 / 20 + ε)) ^ upperC1 ε)) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  sorry

/-- LEAF: P0069 page 49, Lemma 34, the conclusion 5.2 on page 43 for the principal character,
for `b` of the same form as in `upD_lemma34_51`. Same proof in the paper. CONDITIONAL on the
cited Theorem 4 and Lemma 9. HARD. -/
theorem upD_lemma34_52 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a b : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (hrep : ∀ x : ℝ, 2 ≤ x ^ (11 / 20 + ε) → ∀ k ∈ rightInterval ε x,
      b x k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * upperRough (k / n) ((x ^ (11 / 20 + ε)) ^ upperC1 ε)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A) := by
  sorry

/-- P0069 page 49: Lemma 34 with the bridge of Prep1121DUpslackBridge gives the non-principal
window mean square for any `b` of the Lemma 34 form that satisfies 3.1. PROVED from the leaves. -/
theorem upD_np_of_lemma34 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a b : ℝ → ℕ → ℝ) {B B' : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B')
    (hrep : ∀ x : ℝ, 2 ≤ x ^ (11 / 20 + ε) → ∀ k ∈ rightInterval ε x,
      b x k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * upperRough (k / n) ((x ^ (11 / 20 + ε)) ^ upperC1 ε)) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).erase 1,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((b x m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2 ≤
              C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  exact upD_np_of_lemma29 b hε hb (upD_lemma34_51 h4 h9 hε hε8 a b ha hrep)
    (upD_lemma34_52 h4 h9 hε hε8 a b ha hrep)

/-- A finite sum of terms at most `B` over a set of size at most `N` is at most `N B`. -/
theorem upD_sum_le (s : Finset ℕ) (f : ℕ → ℝ) {B N : ℝ} (hB : 0 ≤ B) (hf : ∀ i ∈ s, f i ≤ B)
    (hN : (s.card : ℝ) ≤ N) : ∑ i ∈ s, f i ≤ N * B := by
  calc ∑ i ∈ s, f i ≤ s.card • B := Finset.sum_le_card_nsmul _ _ _ hf
    _ = s.card * B := nsmul_eq_mul _ _
    _ ≤ N * B := mul_le_mul_of_nonneg_right hN hB

/-- The sifting indicator is at most one. -/
theorem upD_rough_le_one (n : ℕ) (w : ℝ) : upperRough n w ≤ 1 := by
  unfold upperRough; split_ifs <;> norm_num

/-- A filter of the prime factors of a divisor `m` of `k != 0` has at most `d(k)` elements. -/
theorem upD_card_pf_le {k m : ℕ} (hk : k ≠ 0) (hm : m ∣ k) (P : ℕ → Prop) [DecidablePred P] :
    ((m.primeFactors.filter P).card : ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) := by
  exact_mod_cast le_trans (Finset.card_filter_le _ _) (Finset.card_le_card fun p hp =>
    Nat.mem_divisors.mpr ⟨dvd_trans (Nat.dvd_of_mem_primeFactors hp) hm, hk⟩)

/-- P0069 page 53 with Lemma 34 on page 49: g_m = psi(m, Y^c1) has the Lemma 34 form on J,
with `a_n` the indicator of `n = 1`. PROVED. -/
theorem upD_g_rep {ε : ℝ} (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ x : ℝ, 2 ≤ x ^ (11 / 20 + ε) → ∀ k ∈ rightInterval ε x,
      upperG ε (x ^ (11 / 20 + ε)) k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        (if n = 1 then (1 : ℝ) else 0) * upperRough (k / n) ((x ^ (11 / 20 + ε)) ^ upperC1 ε) := by
  intro x hY k hk
  have hk0 : k ≠ 0 := by have := (Finset.mem_Ioc.mp hk).1; omega
  rw [Finset.sum_eq_single 1]
  · simp [upperG]
  · intro n _ hn; simp [hn]
  · intro h; exfalso; apply h
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨one_dvd _, hk0⟩, ?_⟩
    simp only [Nat.cast_one]
    exact Real.one_le_rpow (by linarith) (by linarith)

/-- P0069 page 3, 3.1 for the Lemma 34 coefficients of g: `|a_n| <= 1`. PROVED. -/
theorem upD_ag_bound : ∃ C : ℝ, ∀ (x : ℝ) (n : ℕ), |(if n = 1 then (1 : ℝ) else 0)| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ (0 : ℝ) :=
  ⟨1, fun x n => by rw [Real.rpow_zero, mul_one]; split_ifs <;> norm_num⟩

/-- P0069 page 3, 3.1 for g: `|g_m| <= 1`. PROVED. -/
theorem upD_g_bound {ε : ℝ} : ∃ C : ℝ, ∀ (x : ℝ) (k : ℕ), |upperG ε (x ^ (11 / 20 + ε)) k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ (0 : ℝ) :=
  ⟨1, fun x k => by rw [Real.rpow_zero, mul_one]; unfold upperG upperRough; split_ifs <;> norm_num⟩

/-- The exact statement of `upslack_piece_g_mean_square`, from Lemma 34 and the bridge. -/
theorem upD_piece_g (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).erase 1,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((upperG ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2 ≤
              C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
  upD_np_of_lemma34 h4 h9 hε hε8 (fun x n => (if n = 1 then (1 : ℝ) else 0)) (fun x m => upperG ε (x ^ (11 / 20 + ε)) m)
    upD_ag_bound upD_g_bound (upD_g_rep hε8)

/-- P0069 page 53 with Lemma 34 on page 49: h_m has the Lemma 34 form on J, with `a_n` the
indicator of the primes in `[Y^c1, Y^c4)`, since `Y^c4 <= Y^(1/2 + theta2/4 - 2 eps)`. PROVED. -/
theorem upD_h_rep {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ x : ℝ, 2 ≤ x ^ (11 / 20 + ε) → ∀ k ∈ rightInterval ε x,
      upperH ε (x ^ (11 / 20 + ε)) k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        (if n.Prime ∧ (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (n : ℝ) ∧ (n : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC4 ε then (1 : ℝ) else 0) * upperRough (k / n) ((x ^ (11 / 20 + ε)) ^ upperC1 ε) := by
  intro x hY k hk
  have hk0 : k ≠ 0 := by have := (Finset.mem_Ioc.mp hk).1; omega
  have hce : (x ^ (11 / 20 + ε)) ^ upperC4 ε ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by unfold upperC4; linarith)
  have hS : k.primeFactors.filter
      (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC4 ε) =
      k.divisors.filter
      (fun n : ℕ => n.Prime ∧ (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (n : ℝ) ∧ (n : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC4 ε) := by
    ext n
    simp only [Finset.mem_filter, Nat.mem_primeFactors, Nat.mem_divisors]
    tauto
  unfold upperH
  rw [hS, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hR : n.Prime ∧ (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (n : ℝ) ∧ (n : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC4 ε
  · have hQ : (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε) := le_trans hR.2.2.le hce
    rw [if_pos hR, if_pos hQ, if_pos hR, one_mul]
  · simp only [if_neg hR, zero_mul, ite_self]

/-- P0069 page 3, 3.1 for the Lemma 34 coefficients of h: `|a_n| <= 1`. PROVED. -/
theorem upD_ah_bound {ε : ℝ} : ∃ C : ℝ, ∀ (x : ℝ) (n : ℕ), |(if n.Prime ∧ (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (n : ℝ) ∧ (n : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC4 ε then (1 : ℝ) else 0)| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ (0 : ℝ) :=
  ⟨1, fun x n => by rw [Real.rpow_zero, mul_one]; split_ifs <;> norm_num⟩

/-- P0069 page 3, 3.1 for h: `|h_m|` is at most the number of prime factors of m, so at most the
number of divisors. PROVED. -/
theorem upD_h_bound {ε : ℝ} : ∃ C : ℝ, ∀ (x : ℝ) (k : ℕ), |upperH ε (x ^ (11 / 20 + ε)) k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ (1 : ℝ) := by
  refine ⟨1, fun x k => ?_⟩
  rw [Real.rpow_one, one_mul]
  unfold upperH
  rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => upperRough_nonneg _ _)]
  calc _ ≤ ∑ p ∈ k.primeFactors.filter
          (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC4 ε), (1 : ℝ) :=
        Finset.sum_le_sum fun p _ => by unfold upperRough; split_ifs <;> norm_num
    _ = ((k.primeFactors.filter
          (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC4 ε)).card : ℝ) := by
        simp
    _ ≤ ((k.divisors.card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_le_card ((Finset.filter_subset _ _).trans fun p hp =>
          Nat.mem_divisors.mpr ⟨(Nat.mem_primeFactors.mp hp).2.1, (Nat.mem_primeFactors.mp hp).2.2⟩)

/-- The exact statement of `upslack_piece_h_mean_square`, from Lemma 34 and the bridge. -/
theorem upD_piece_h (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).erase 1,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((upperH ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2 ≤
              C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
  upD_np_of_lemma34 h4 h9 hε hε8 (fun x n => (if n.Prime ∧ (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (n : ℝ) ∧ (n : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC4 ε then (1 : ℝ) else 0)) (fun x m => upperH ε (x ^ (11 / 20 + ε)) m)
    upD_ah_bound upD_h_bound (upD_h_rep hε hε8)

/-- LEAF: P0069 page 53 with Lemma 34 on page 49: j_m has the Lemma 34 form on J, with `a_n` the
number of ways to write `n = p1 p2` with `Y^c1 <= p2 < p1 < Y^c4`, so `n < Y^(2 c4)` and
`2 c4 = 1/2 + theta2/4 - 2 eps`. A reindexing of the double sum over the prime factors of m as a
sum over the divisors `n = p1 p2` of m. MEDIUM. -/
theorem upD_j_rep {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ x : ℝ, 2 ≤ x ^ (11 / 20 + ε) → ∀ k ∈ rightInterval ε x,
      upperJ ε (x ^ (11 / 20 + ε)) k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        (∑ p1 ∈ n.primeFactors.filter
            (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC4 ε),
          ∑ p2 ∈ (n / p1 : ℕ).primeFactors.filter
              (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p1 : ℝ)),
            if n / p1 / p2 = 1 then (1 : ℝ) else 0) * upperRough (k / n) ((x ^ (11 / 20 + ε)) ^ upperC1 ε) := by
  sorry

/-- P0069 page 3, 3.1 for the Lemma 34 coefficients of j: `a_n` is at most the number of
pairs of prime factors, so at most `d(n)^2`. PROVED. -/
theorem upD_aj_bound {ε : ℝ} : ∃ C : ℝ, ∀ (x : ℝ) (n : ℕ), |(∑ p1 ∈ n.primeFactors.filter
            (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC4 ε),
          ∑ p2 ∈ (n / p1 : ℕ).primeFactors.filter
              (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p1 : ℝ)),
            if n / p1 / p2 = 1 then (1 : ℝ) else 0)| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ (2 : ℝ) := by
  refine ⟨1, fun x n => ?_⟩
  rw [one_mul, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rcases eq_or_ne n 0 with rfl | hk
  · simp 
  have hD : (0 : ℝ) ≤ ((n.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
  
  rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)]
  calc _ ≤ ((n.divisors.card : ℕ) : ℝ) * (((n.divisors.card : ℕ) : ℝ) * 1) := by
        refine upD_sum_le _ _ (mul_nonneg hD zero_le_one) (fun p1 hp1 => ?_)
          (upD_card_pf_le hk dvd_rfl _)
        have d1 : n / p1 ∣ n :=
          Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp1).1)
        exact upD_sum_le _ _ zero_le_one (fun p2 _ => by split_ifs <;> norm_num) (upD_card_pf_le hk d1 _)
    _ = ((n.divisors.card : ℕ) : ℝ) ^ 2 := by ring

/-- P0069 page 3, 3.1 for j: `0 <= j_m <= d(m)^2`, a double sum of indicators over prime
factors. PROVED. -/
theorem upD_j_bound {ε : ℝ} : ∃ C : ℝ, ∀ (x : ℝ) (k : ℕ), |upperJ ε (x ^ (11 / 20 + ε)) k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ (2 : ℝ) := by
  refine ⟨1, fun x k => ?_⟩
  rw [one_mul, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rcases eq_or_ne k 0 with rfl | hk
  · simp [upperJ]
  have hD : (0 : ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold upperJ
  rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => upperRough_nonneg _ _)]
  calc _ ≤ ((k.divisors.card : ℕ) : ℝ) * (((k.divisors.card : ℕ) : ℝ) * 1) := by
        refine upD_sum_le _ _ (mul_nonneg hD zero_le_one) (fun p1 hp1 => ?_)
          (upD_card_pf_le hk dvd_rfl _)
        have d1 : k / p1 ∣ k :=
          Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp1).1)
        exact upD_sum_le _ _ zero_le_one (fun p2 _ => upD_rough_le_one _ _) (upD_card_pf_le hk d1 _)
    _ = ((k.divisors.card : ℕ) : ℝ) ^ 2 := by ring

/-- The exact statement of `upslack_piece_j_mean_square`, from Lemma 34 and the bridge. -/
theorem upD_piece_j (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).erase 1,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((upperJ ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2 ≤
              C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
  upD_np_of_lemma34 h4 h9 hε hε8 (fun x n => (∑ p1 ∈ n.primeFactors.filter
            (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC4 ε),
          ∑ p2 ∈ (n / p1 : ℕ).primeFactors.filter
              (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p1 : ℝ)),
            if n / p1 / p2 = 1 then (1 : ℝ) else 0)) (fun x m => upperJ ε (x ^ (11 / 20 + ε)) m)
    upD_aj_bound upD_j_bound (upD_j_rep hε hε8)

/-- LEAF: P0069 page 53 with Lemma 33 on page 48, display 5.1 on page 43 for the kept part of
k_m, with the page 19 set E and its size from page 3: each kept term is one for which Lemma 33,
case 5.13, the triangle R or the parallelograms P1, P2, applies to some arrangement of the
variables, after a dyadic split of p1, p2, p3 and n4. CONDITIONAL on the cited Theorem 4 and
Lemma 9. HARD. -/
theorem upD_kept_51 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x, (upperKept ε (x ^ (11 / 20 + ε)) m : ℂ) * χ (m : ZMod q) /
                (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  sorry

/-- LEAF: P0069 page 53 with Lemma 33 on page 48, display 5.2 on page 43 for the kept part of
k_m, the principal character, by the same argument. CONDITIONAL on the cited Theorem 4 and
Lemma 9. HARD. -/
theorem upD_kept_52 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (upperKept ε (x ^ (11 / 20 + ε)) m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (upperKept ε (x ^ (11 / 20 + ε)) m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A) := by
  sorry

/-- P0069 page 3, 3.1 for the kept part of k: `0 <= kept_m <= d(m)^3`, a triple sum of
indicators over prime factors. PROVED. -/
theorem upD_kept_bound {ε : ℝ} : ∃ C : ℝ, ∀ (x : ℝ) (k : ℕ), |upperKept ε (x ^ (11 / 20 + ε)) k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ (3 : ℝ) := by
  refine ⟨1, fun x k => ?_⟩
  rw [one_mul, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rcases eq_or_ne k 0 with rfl | hk
  · simp [upperKept]
  have hD : (0 : ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold upperKept
  rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => by split_ifs; exacts [upperRough_nonneg _ _, le_rfl])]
  calc _ ≤ ((k.divisors.card : ℕ) : ℝ) * (((k.divisors.card : ℕ) : ℝ) *
        (((k.divisors.card : ℕ) : ℝ) * 1)) := by
        refine upD_sum_le _ _ (mul_nonneg hD (mul_nonneg hD zero_le_one)) (fun p1 hp1 => ?_)
          (upD_card_pf_le hk dvd_rfl _)
        have d1 : k / p1 ∣ k :=
          Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp1).1)
        refine upD_sum_le _ _ (mul_nonneg hD zero_le_one) (fun p2 hp2 => ?_)
          (upD_card_pf_le hk d1 _)
        have d2 : k / p1 / p2 ∣ k := dvd_trans
          (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp2).1)) d1
        exact upD_sum_le _ _ zero_le_one
          (fun p3 _ => by split_ifs; exacts [upD_rough_le_one _ _, zero_le_one])
          (upD_card_pf_le hk d2 _)
    _ = ((k.divisors.card : ℕ) : ℝ) ^ 3 := by ring

/-- The exact statement of `upslack_piece_kept_mean_square`, from the Lemma 33 leaves and the
bridge. -/
theorem upD_piece_kept (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).erase 1,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((upperKept ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2 ≤
              C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
  upD_np_of_lemma29 (fun x m => upperKept ε (x ^ (11 / 20 + ε)) m) hε upD_kept_bound
    (upD_kept_51 h4 h9 hε hε8) (upD_kept_52 h4 h9 hε hε8)

end LeanLab.BHP1997.DecompC165d
