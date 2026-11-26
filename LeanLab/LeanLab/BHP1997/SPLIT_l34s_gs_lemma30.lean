/-
Burst burst-20261122, session S129, wave 13, second pass. P0069 Baker Harman Pintz 1997, proof of
Lemma 34 on page 50, the first Buchstab term of the iteration for w <= p1 < Y^eps.
`leaf_l34s_gs_lemma30_split` proves exactly the statement of the LEAF `leaf_l34s_gs_lemma30` of
SPLIT_l34s_g_small_iterate from one smaller cited LEAF, `leaf_l34s_lemma30_gen`, which is Lemma 30
of page 44 with condition 5.5 for a general coefficient b_n satisfying 3.1.
The glue, PROVED: `l34s_gs30_reindex` regroups the sum over n and p1 as a sum over k = n p1;
`l34s_gs30_bound` gives 3.1 for b_k from 3.1 for a_n with the exponent |B| + 1;
`l34s_gs30_support` gives 5.5, as n <= Y^(1/2 + theta2/4 - 2 eps) and p1 < Y^eps.
Lemma30.lean on main holds only the exponent arithmetic of the proof of Lemma 30, so it does not
give the analytic statement; that stays the cited LEAF here.
No new definition, no existing statement changed.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Prep1122Lemma34Split51

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open MeasureTheory

theorem l34s_gs30_reindex (m : ℕ) (F : ℕ → Prop) (G : ℕ → Prop) [DecidablePred G] (a : ℕ → ℝ) (ψ : ℕ → ℝ) :
    (∑ n ∈ m.divisors.filter F, a n * ∑ p ∈ (m / n).primeFactors.filter G, ψ (m / n / p)) =
      ∑ k ∈ m.divisors, (∑ n ∈ k.divisors.filter F,
        a n * (if (k / n).Prime ∧ G (k / n) then (1 : ℝ) else 0)) * ψ (m / k) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm' (t' := m.divisors.filter F) (s' := fun n => m.divisors.filter (n ∣ ·))]
  · refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn' := Finset.mem_filter.mp hn
    have hm0 : m ≠ 0 := (Nat.mem_divisors.mp hn'.1).2
    have hnm : n ∣ m := (Nat.mem_divisors.mp hn'.1).1
    have hn0 : 0 < n := Nat.pos_of_dvd_of_pos hnm (Nat.pos_of_ne_zero hm0)
    rw [Finset.mul_sum]
    simp_rw [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
    rw [← Finset.sum_filter]
    symm
    refine Finset.sum_nbij' (fun k => k / n) (fun p => n * p) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Nat.mem_primeFactors, Nat.mem_divisors] at hk ⊢
      obtain ⟨⟨⟨hkm, _⟩, hnk⟩, hpp, hG⟩ := hk
      refine ⟨⟨hpp, ?_, (Nat.div_ne_zero_iff_of_dvd hnm).mpr ⟨hm0, hn0.ne'⟩⟩, hG⟩
      exact Nat.div_dvd_div hnk hkm
    · intro p hp
      simp only [Finset.mem_filter, Nat.mem_primeFactors] at hp ⊢
      obtain ⟨⟨hpp, hpd, _⟩, hG⟩ := hp
      refine ⟨⟨Nat.mem_divisors.mpr ⟨?_, hm0⟩, dvd_mul_right n p⟩, ?_⟩
      · obtain ⟨c, hc⟩ := hpd
        exact ⟨c, by rw [mul_assoc, ← hc, Nat.mul_div_cancel' hnm]⟩
      · rw [Nat.mul_div_cancel_left p hn0]; exact ⟨hpp, hG⟩
    · intro k hk
      simp only [Finset.mem_filter] at hk
      exact Nat.mul_div_cancel' hk.1.2
    · intro p _; simp [Nat.mul_div_cancel_left p hn0]
    · intro k hk
      simp only [Finset.mem_filter] at hk
      rw [Nat.div_div_eq_div_mul, Nat.mul_div_cancel' hk.1.2]
  · intro k n
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hkm, hm⟩, ⟨hnk, hk⟩, hF⟩
      exact ⟨⟨⟨hkm, hm⟩, hnk⟩, ⟨dvd_trans hnk hkm, hm⟩, hF⟩
    · rintro ⟨⟨⟨hkm, hm⟩, hnk⟩, ⟨hnm, _⟩, hF⟩
      exact ⟨⟨hkm, hm⟩, ⟨hnk, fun h => hm (by subst h; exact Nat.eq_zero_of_zero_dvd hkm)⟩, hF⟩


theorem l34s_gs30_bound (a : ℕ → ℝ) {C B : ℝ}
    (ha : ∀ n, |a n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B) (k : ℕ) (F P : ℕ → Prop) [DecidablePred P] :
    |∑ n ∈ k.divisors.filter F, a n * (if P n then (1 : ℝ) else 0)| ≤
      |C| * ((k.divisors.card : ℕ) : ℝ) ^ (|B| + 1) := by
  have hterm : ∀ n ∈ k.divisors.filter F, |a n * (if P n then (1 : ℝ) else 0)| ≤
      |C| * ((k.divisors.card : ℕ) : ℝ) ^ |B| := by
    intro n hn
    have hnk : n ∣ k := (Nat.mem_divisors.mp (Finset.mem_filter.mp hn).1).1
    have hk0 : k ≠ 0 := (Nat.mem_divisors.mp (Finset.mem_filter.mp hn).1).2
    have hn0 : n ≠ 0 := fun h => hk0 (Nat.eq_zero_of_zero_dvd (h ▸ hnk))
    have h1 : (1 : ℝ) ≤ ((n.divisors.card : ℕ) : ℝ) := by
      have : 0 < n.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn0⟩
      exact_mod_cast this
    have h2 : ((n.divisors.card : ℕ) : ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hk0 hnk)
    have h3 : ((n.divisors.card : ℕ) : ℝ) ^ B ≤ ((k.divisors.card : ℕ) : ℝ) ^ |B| :=
      (Real.rpow_le_rpow_of_exponent_le h1 (le_abs_self B)).trans
        (Real.rpow_le_rpow (by linarith) h2 (abs_nonneg B))
    have h4 : |a n| ≤ |C| * ((k.divisors.card : ℕ) : ℝ) ^ |B| :=
      (ha n).trans ((mul_le_mul_of_nonneg_right (le_abs_self C)
        (Real.rpow_nonneg (by linarith) B)).trans
        (mul_le_mul_of_nonneg_left h3 (abs_nonneg C)))
    rw [abs_mul]
    split_ifs <;> simp [h4, abs_nonneg, mul_nonneg, Real.rpow_nonneg]
  calc _ ≤ ∑ n ∈ k.divisors.filter F, |a n * (if P n then (1 : ℝ) else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ k.divisors.filter F, |C| * ((k.divisors.card : ℕ) : ℝ) ^ |B| :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ n ∈ k.divisors, |C| * ((k.divisors.card : ℕ) : ℝ) ^ |B| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => mul_nonneg (abs_nonneg C) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    _ = |C| * ((k.divisors.card : ℕ) : ℝ) ^ (|B| + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul,
          Real.rpow_add_one' (Nat.cast_nonneg _) (by positivity)]
        ring

theorem l34s_gs30_support {Y e w Z : ℝ} (hY : 0 < Y) (a : ℕ → ℝ) (k : ℕ)
    (hk : Y ^ (e + Z) < (k : ℝ)) :
    (∑ n ∈ k.divisors.filter (fun n : ℕ => (n : ℝ) ≤ Y ^ e),
      a n * (if (k / n).Prime ∧ (w ≤ ((k / n : ℕ) : ℝ) ∧ ((k / n : ℕ) : ℝ) < Y ^ Z)
        then (1 : ℝ) else 0)) = 0 := by
  refine Finset.sum_eq_zero (fun n hn => ?_)
  obtain ⟨hnd, hnle⟩ := Finset.mem_filter.mp hn
  have hnk : n ∣ k := (Nat.mem_divisors.mp hnd).1
  refine mul_eq_zero_of_right _ ((ite_eq_right_iff).mpr ?_)
  rintro ⟨_, _, hlt⟩
  exfalso
  have hkeq : (k : ℝ) = (n : ℝ) * ((k / n : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_div_cancel' hnk).symm
  have hpos : 0 ≤ ((k / n : ℕ) : ℝ) := Nat.cast_nonneg _
  have : (k : ℝ) < Y ^ (e + Z) := by
    rw [hkeq, Real.rpow_add hY]
    calc (n : ℝ) * ((k / n : ℕ) : ℝ) ≤ Y ^ e * ((k / n : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hnle hpos
      _ < Y ^ e * Y ^ Z := mul_lt_mul_of_pos_left hlt (Real.rpow_pos_of_pos hY e)
  linarith

/-- LEAF: P0069 page 44, Lemma 30, with 5.5: if b_m is the sum over n l = m of a_n psi(l, w) where
a_n satisfies 3.1 and vanishes unless n <= Y^(1/2 + theta2/4 - eps), then 5.1 holds, here for 5.1
on page 43 with the page 19 set E and its size from page 3, the n range cut into O(L) dyadic
ranges n ~ N as on page 49. Y = x^(11/20 + eps), w = exp(log^(9/10) x) from page 25. The proof of
Lemma 30 on pages 44 and 45 runs as for Lemma 12 through 3.3 and Lemma 9. CONDITIONAL on the cited
Theorem 4 and Lemma 9. HARD. -/
theorem leaf_l34s_lemma30_gen (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (b : ℝ → ℕ → ℝ) {B : ℝ}
    (hb : ∃ C : ℝ, ∀ x n, |b x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (hsupp : ∀ x : ℝ, 0 < x → ∀ n : ℕ,
      (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - ε) < (n : ℝ) → b x n = 0) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x,
                ((∑ n ∈ m.divisors, b x n *
                  upperRough (m / n) (Real.exp (Real.log x ^ (9 / 10 : ℝ))) : ℝ) : ℂ) *
            χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  sorry

/-- P0069 page 50, proof of Lemma 34, the first Buchstab term n p1 psi(n1, w) of the iteration.
Exactly the statement of `leaf_l34s_gs_lemma30` of SPLIT_l34s_g_small_iterate. PROVED from
`leaf_l34s_lemma30_gen` applied to b_k, the sum over n p1 = k with n <= Y^(1/2 + theta2/4 - 2 eps)
and w <= p1 < Y^eps of a_n: `l34s_gs30_reindex` regroups the sum, `l34s_gs30_bound` gives 3.1 for
b and `l34s_gs30_support` gives 5.5, since n p1 < Y^(1/2 + theta2/4 - eps). CONDITIONAL on the
cited Theorem 4 and Lemma 9. -/
theorem leaf_l34s_gs_lemma30_split (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x,
                ((∑ n ∈ m.divisors.filter (fun n : ℕ =>
                    (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
                  a x n * ∑ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
                      Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ ε),
                    upperRough (m / n / p : ℕ) (Real.exp (Real.log x ^ (9 / 10 : ℝ))) : ℝ) : ℂ) *
            χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  obtain ⟨C, hC⟩ := ha
  have key := leaf_l34s_lemma30_gen h4 h9 hε hε8
    (fun x k => ∑ n ∈ k.divisors.filter (fun n : ℕ =>
        (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
      a x n * (if (k / n).Prime ∧ (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ ((k / n : ℕ) : ℝ) ∧
        ((k / n : ℕ) : ℝ) < (x ^ (11 / 20 + ε)) ^ ε) then (1 : ℝ) else 0))
    (B := |B| + 1) ⟨|C|, fun x k => l34s_gs30_bound (a x) (hC x) k
      (fun n : ℕ =>
        (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε))
      (fun n => (k / n).Prime ∧ (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ ((k / n : ℕ) : ℝ) ∧
        ((k / n : ℕ) : ℝ) < (x ^ (11 / 20 + ε)) ^ ε))⟩
    (fun x hx k hk => by
      have he : (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - ε : ℝ) =
          (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε) + ε := by ring
      rw [he] at hk
      exact l34s_gs30_support (Real.rpow_pos_of_pos hx _) (a x) k hk)
  have hid : ∀ (x : ℝ) (m : ℕ),
      (∑ n ∈ m.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
            Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ ε),
          upperRough (m / n / p : ℕ) (Real.exp (Real.log x ^ (9 / 10 : ℝ)))) =
      ∑ k ∈ m.divisors, (∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * (if (k / n).Prime ∧ (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ ((k / n : ℕ) : ℝ) ∧
          ((k / n : ℕ) : ℝ) < (x ^ (11 / 20 + ε)) ^ ε) then (1 : ℝ) else 0)) *
        upperRough (m / k) (Real.exp (Real.log x ^ (9 / 10 : ℝ))) := fun x m =>
    l34s_gs30_reindex m (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε))
      (fun p : ℕ =>
            Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ ε)
      (a x) (fun l => upperRough l (Real.exp (Real.log x ^ (9 / 10 : ℝ))))
  simp only [hid]
  exact key

end LeanLab.BHP1997.DecompC165d
