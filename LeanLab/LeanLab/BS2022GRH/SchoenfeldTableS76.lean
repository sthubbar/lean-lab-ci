/-
Schoenfeld 1976, Math. Comp. 30, p. 340: "(6.20) with 2.523 replaced by 2.444" for
`2659 ≤ x < 3169`. SchoenfeldFiniteS70.lean reduces this to the integer table LEAF
`table_6_20_low_int`, two columns: `li n - π n > 0` and
`(li (n+1) - π n) log n / √n < 2.444`.

Here the first column is PROVED from the enclosure `li 2657 ≥ 399.59`,
SchoenfeldLiS76.lean, by eight blocks of length 64: on a block `[A, B)`,
`li n ≥ li 2657 + (A - 2657) / 8.07` because `log t ≤ 8.07` for `t ≤ 3169`, and
`π n ≤ π (B - 1)`, where the eight values `π (B - 1)` are kernel computations.
The minimum slack over the blocks is about `1.7`.
The second column, whose margin is only about `0.0004`, stays one LEAF.

AI wrote this Lean code, Claude, ROUTE BURST S76 burst-20261122, step direct_2657_li.
Binary Goldbach is OPEN.
-/
import LeanLab.BS2022GRH.SchoenfeldLiS76

namespace LeanLab.BS2022GRH.SchoenfeldTableS76
open Real MeasureTheory intervalIntegral Set
open LeanLab.BS2022GRH.PaperInputs148

noncomputable section

/-- For `n < 57²`, trial division by `d < 57` with `d² ≤ n` decides primality. -/
lemma trial_iff {n : ℕ} (hn : n < 3249) :
    (decide (2 ≤ n) && (List.range 57).all (fun d => d < 2 || n < d * d || n % d != 0)) = true
      ↔ n.Prime := by
  rw [Nat.prime_def_le_sqrt]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm hms hdvd => ?_⟩
    have hmm : m * m ≤ n := Nat.le_sqrt.mp hms
    have hm57 : m < 57 := by
      by_contra hc
      have : 57 * 57 ≤ m * m := Nat.mul_le_mul (by omega) (by omega)
      omega
    have := h m hm57
    rcases this with (h1 | h1) | h1
    · omega
    · omega
    · exact h1 (Nat.mod_eq_zero_of_dvd hdvd)
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun d _ => ?_⟩
    by_cases hd : d < 2
    · left; left; exact hd
    by_cases hdn : n < d * d
    · left; right; exact hdn
    right
    intro hmod
    exact h d (by omega) (Nat.le_sqrt.mpr (by omega)) (Nat.dvd_of_mod_eq_zero hmod)

/-- The number of primes below `N ≤ 3249`, through the trial division test. -/
lemma card_primes_eq {N : ℕ} (hN : N ≤ 3249) [DecidablePred Nat.Prime] :
    ((Finset.range N).filter (fun n => n.Prime)).card =
      ((Finset.range N).filter (fun n => (decide (2 ≤ n) && (List.range 57).all
        (fun d => d < 2 || n < d * d || n % d != 0)) = true)).card := by
  rw [Finset.filter_congr (fun n hn => (trial_iff (by simp at hn; omega)).symm)]

/-- The eight block counts `π (B - 1)` for `B = 2723, 2787, ..., 3169`. PROVED by kernel
computation. -/
lemma block_counts [DecidablePred Nat.Prime] :
    ((Finset.range 2723).filter (fun n => n.Prime)).card = 397 ∧
    ((Finset.range 2787).filter (fun n => n.Prime)).card = 404 ∧
    ((Finset.range 2851).filter (fun n => n.Prime)).card = 413 ∧
    ((Finset.range 2915).filter (fun n => n.Prime)).card = 421 ∧
    ((Finset.range 2979).filter (fun n => n.Prime)).card = 429 ∧
    ((Finset.range 3043).filter (fun n => n.Prime)).card = 436 ∧
    ((Finset.range 3107).filter (fun n => n.Prime)).card = 442 ∧
    ((Finset.range 3169).filter (fun n => n.Prime)).card = 448 := by
  simp only [card_primes_eq (by norm_num : (2723 : ℕ) ≤ 3249),
    card_primes_eq (by norm_num : (2787 : ℕ) ≤ 3249),
    card_primes_eq (by norm_num : (2851 : ℕ) ≤ 3249),
    card_primes_eq (by norm_num : (2915 : ℕ) ≤ 3249),
    card_primes_eq (by norm_num : (2979 : ℕ) ≤ 3249),
    card_primes_eq (by norm_num : (3043 : ℕ) ≤ 3249),
    card_primes_eq (by norm_num : (3107 : ℕ) ≤ 3249),
    card_primes_eq (by norm_num : (3169 : ℕ) ≤ 3249)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- `π n ≤ #{p < B prime}` for `n < B`. -/
lemma primeCount_le_block (n B : ℕ) (h : n < B) :
    primeCount (n : ℝ) ≤ (((Finset.range B).filter (fun p => p.Prime)).card : ℝ) := by
  unfold primeCount
  rw [Nat.floor_natCast]
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _
    (Finset.range_subset_range.mpr (by omega)))

/-- `log t ≤ 8.07` for `0 < t ≤ 3169`, from `e⁸ > 2980` and `e^{0.07} ≥ 1.07`. -/
lemma log_le_807 {t : ℝ} (h0 : 0 < t) (ht : t ≤ 3169) : log t ≤ 8.07 := by
  rw [log_le_iff_le_exp h0]
  have h : exp 8 = exp 1 ^ 8 := by rw [← exp_nat_mul]; norm_num
  have h8 : 2980 < exp 8 := by
    rw [h]
    have h1 := exp_one_gt_d9
    calc (2980 : ℝ) < (2.7182818283 : ℝ) ^ 8 := by norm_num
      _ < exp 1 ^ 8 := by gcongr
  have he : exp 8 * exp 0.07 = exp 8.07 := by rw [← exp_add]; norm_num
  have h2 := add_one_le_exp (0.07 : ℝ)
  nlinarith

/-- `li x ≥ li 2657 + (x - 2657) / 8.07` for `2657 ≤ x ≤ 3169`. -/
lemma liPV_lower (x : ℝ) (hx : 2657 ≤ x) (hx2 : x ≤ 3169) :
    liPV 2657 + (x - 2657) / 8.07 ≤ liPV x := by
  rw [liPV_eq_add (show (2 : ℝ) ≤ x by linarith), liPV_eq_add (by norm_num : (2 : ℝ) ≤ 2657),
    SchoenfeldLiS76.split (a := 2) (b := 2657) (c := x) (by norm_num) (by norm_num) (by linarith)]
  have hI : ∫ t in (2657 : ℝ)..x, (1 / 8.07 : ℝ) ≤ (∫ t in (2657 : ℝ)..x, 1 / log t) := by
    apply intervalIntegral.integral_mono_on hx intervalIntegrable_const
      (SchoenfeldLiS76.ii_inv_log (by norm_num) (by linarith))
    intro t ht
    have hl := log_le_807 (t := t) (by linarith [ht.1]) (by linarith [ht.2])
    exact one_div_le_one_div_of_le (log_pos (by linarith [ht.1])) hl
  rw [intervalIntegral.integral_const, smul_eq_mul] at hI
  have : (x - 2657) * (1 / 8.07 : ℝ) = (x - 2657) / 8.07 := by ring
  linarith

/-- Schoenfeld 1976 p. 340, first column of the table: `li n - π n > 0` for
`2659 ≤ n < 3169`. PROVED from `liPV_2657_encl_S76` and the block counts. -/
theorem first_column : ∀ n : ℕ, 2659 ≤ n → n < 3169 → 0 < liPV n - primeCount n := by
  intro n h1 h2
  classical
  have hli := (SchoenfeldLiS76.liPV_2657_encl_S76).1
  have hnR1 : (2659 : ℝ) ≤ n := by exact_mod_cast h1
  have hnR2 : (n : ℝ) < 3169 := by exact_mod_cast h2
  have hlow := liPV_lower n (by linarith) hnR2.le
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := block_counts
  have key : ∀ A B : ℕ, A ≤ n → n < B → B ≤ 3169 →
      ((((Finset.range B).filter (fun p => p.Prime)).card : ℕ) : ℝ) <
        399.59 + ((A : ℝ) - 2657) / 8.07 → 0 < liPV n - primeCount n := by
    intro A B hA hB _ hc
    have hp := primeCount_le_block n B hB
    have hAR : (A : ℝ) ≤ n := by exact_mod_cast hA
    have : ((A : ℝ) - 2657) / 8.07 ≤ ((n : ℝ) - 2657) / 8.07 := by gcongr
    linarith
  rcases (show n < 2723 ∨ (2723 ≤ n ∧ n < 2787) ∨ (2787 ≤ n ∧ n < 2851) ∨
      (2851 ≤ n ∧ n < 2915) ∨ (2915 ≤ n ∧ n < 2979) ∨ (2979 ≤ n ∧ n < 3043) ∨
      (3043 ≤ n ∧ n < 3107) ∨ 3107 ≤ n by omega) with
    h | ⟨ha, h⟩ | ⟨ha, h⟩ | ⟨ha, h⟩ | ⟨ha, h⟩ | ⟨ha, h⟩ | ⟨ha, h⟩ | ha
  · exact key 2659 2723 h1 h (by norm_num) (by rw [c1]; norm_num)
  · exact key 2723 2787 ha h (by norm_num) (by rw [c2]; norm_num)
  · exact key 2787 2851 ha h (by norm_num) (by rw [c3]; norm_num)
  · exact key 2851 2915 ha h (by norm_num) (by rw [c4]; norm_num)
  · exact key 2915 2979 ha h (by norm_num) (by rw [c5]; norm_num)
  · exact key 2979 3043 ha h (by norm_num) (by rw [c6]; norm_num)
  · exact key 3043 3107 ha h (by norm_num) (by rw [c7]; norm_num)
  · exact key 3107 3169 ha h2 (by norm_num) (by rw [c8]; norm_num)

/-- LEAF: Schoenfeld 1976 p. 340, second column of the table behind "(6.20) with 2.523
replaced by 2.444" for `2659 ≤ x < 3169`. HARD. For every integer `n` with
`2659 ≤ n < 3169`: `(li (n+1) - π n) log n / √n < 2.444`. Numerically the maximum is about
`2.44362`, a margin of about `0.0004`. -/
theorem second_column : ∀ n : ℕ, 2659 ≤ n → n < 3169 →
    (liPV (n + 1) - primeCount n) * log n / √n < 2.444 := by
  sorry

/-- The exact statement of the LEAF `SchoenfeldFiniteS70.table_6_20_low_int`. PROVED from
`first_column`, which rests on the LEAFs of SchoenfeldLiS76.lean, and the LEAF
`second_column`. -/
theorem table_6_20_low_int_S76 : ∀ n : ℕ, 2659 ≤ n → n < 3169 →
    0 < liPV n - primeCount n ∧
      (liPV (n + 1) - primeCount n) * log n / √n < 2.444 :=
  fun n h1 h2 => ⟨first_column n h1 h2, second_column n h1 h2⟩

end

end LeanLab.BS2022GRH.SchoenfeldTableS76

#print axioms LeanLab.BS2022GRH.SchoenfeldTableS76.block_counts
#print axioms LeanLab.BS2022GRH.SchoenfeldTableS76.log_le_807
#print axioms LeanLab.BS2022GRH.SchoenfeldTableS76.liPV_lower
#print axioms LeanLab.BS2022GRH.SchoenfeldTableS76.first_column
#print axioms LeanLab.BS2022GRH.SchoenfeldTableS76.table_6_20_low_int_S76
