/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 51, display 5.17 with no character, the
E2 sum of display 5.15, page 50: the cofactor variable `n3`.

After the sum over `m` in a prefix of J is interchanged with the sum over the prime pairs
`p1 p2`, the cofactor `n3 = m / (p1 p2)` runs over an interval of integers. This file proves
that the sum of the Buchstab density `ω(log n / log p2) / log p2` over those integers is the
average over `m` of the same density at the real point `m / (p1 p2)`, up to a power saving.
No prime number theorem is used: the density is bounded, vanishes below `p2` and is Lipschitz
in `log n` above `p2`, so each pair costs `O(log Y)`; only the pairs with `p1 p2 ^ 2 ≤ 2 Y`
contribute and their reciprocal sum is a log power.

No new definition, nothing left open in this file. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp514a

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d Decomp514a
open scoped BigOperators

/-- P0069 page 51 display 5.17, the cofactor variable of the E2 sum of display 5.15. The
integers of `(d A, d B]` split into the blocks `(d (n - 1), d n]`, one for each cofactor `n`
in `(A, B]`. -/
theorem two_cofactor_block_sum (d A : ℕ) (g : ℕ → ℝ) {B : ℕ} (hAB : A ≤ B) :
    ∑ m ∈ Finset.Ioc (d * A) (d * B), g m =
      ∑ n ∈ Finset.Ioc A B, ∑ m ∈ Finset.Ioc (d * (n - 1)) (d * n), g m := by
  induction B, hAB using Nat.le_induction with
  | base => simp
  | succ B hAB ih =>
    rw [Finset.sum_Ioc_succ_top hAB, ← ih,
      ← Finset.sum_Ioc_consecutive g (Nat.mul_le_mul_left d hAB)
        (Nat.mul_le_mul_left d (Nat.le_succ B)), Nat.add_sub_cancel]

/-- P0069 page 51 display 5.17, the cofactor variable of the E2 sum of display 5.15, one outer
product `d`. For a function `φ` bounded by `M`, vanishing on `(0, q)` and with
`|φ s - φ t| ≤ K (t - s) / s` for `q ≤ s ≤ t`, the sum of `φ` over the cofactors `n` in
`(L0 / d, U / d]` is the average `(1 / d) ∑ φ (m / d)` over `m` in `(L0, U]`, up to
`2 K (1 + log U) + 4 M`: the Lipschitz part costs `2 K / n` in the block of `n`, the jump at
`q` costs `2 M` in one block, and the two incomplete blocks at the ends cost `M` each. -/
theorem two_cofactor_pair_bound (φ : ℝ → ℝ) {q K M : ℝ} (hq : 1 ≤ q) (hK : 0 ≤ K)
    (hM : 0 ≤ M) (hφM : ∀ t, |φ t| ≤ M) (hlow : ∀ t, 0 < t → t < q → φ t = 0)
    (hLip : ∀ s t, q ≤ s → s ≤ t → |φ s - φ t| ≤ K * ((t - s) / s))
    {d : ℕ} (hd : 1 ≤ d) {L0 U : ℕ} (hLU : L0 ≤ U) :
    |(∑ n ∈ Finset.Ioc (L0 / d) (U / d), φ (n : ℝ)) -
        ∑ m ∈ Finset.Ioc L0 U, φ ((m : ℝ) / (d : ℝ)) / (d : ℝ)| ≤
      2 * K * (1 + Real.log U) + 4 * M := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hAB : L0 / d ≤ U / d := Nat.div_le_div_right hLU
  have hA' : d * (L0 / d) ≤ L0 := Nat.mul_div_le L0 d
  have hB' : d * (U / d) ≤ U := Nat.mul_div_le U d
  have hgM : ∀ m : ℕ, |φ ((m : ℝ) / (d : ℝ)) / (d : ℝ)| ≤ M / d := fun m => by
    rw [abs_div, abs_of_pos hd0]
    exact div_le_div_of_nonneg_right (hφM _) hd0.le
  have hedge : ∀ a b : ℕ, b - a ≤ d →
      |∑ m ∈ Finset.Ioc a b, φ ((m : ℝ) / (d : ℝ)) / (d : ℝ)| ≤ M := by
    intro a b hab
    calc |∑ m ∈ Finset.Ioc a b, φ ((m : ℝ) / (d : ℝ)) / (d : ℝ)|
        ≤ ∑ m ∈ Finset.Ioc a b, |φ ((m : ℝ) / (d : ℝ)) / (d : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.Ioc a b, M / d := Finset.sum_le_sum fun m _ => hgM m
      _ = ((b - a : ℕ) : ℝ) * (M / d) := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
      _ ≤ (d : ℝ) * (M / d) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hab) (div_nonneg hM hd0.le)
      _ = M := by field_simp
  have he1 := Finset.sum_Ioc_consecutive (fun m : ℕ => φ ((m : ℝ) / (d : ℝ)) / (d : ℝ))
    hA' hLU
  have he2 := Finset.sum_Ioc_consecutive (fun m : ℕ => φ ((m : ℝ) / (d : ℝ)) / (d : ℝ))
    (Nat.mul_le_mul_left d hAB) hB'
  beta_reduce at he1 he2
  have hE1 := hedge (d * (L0 / d)) L0 (by
    have h1 := Nat.div_add_mod L0 d
    have h2 := Nat.mod_lt L0 hd
    omega)
  have hE2 := hedge (d * (U / d)) U (by
    have h1 := Nat.div_add_mod U d
    have h2 := Nat.mod_lt U hd
    omega)
  have hharm : ∑ n ∈ Finset.Ioc (L0 / d) (U / d), (1 : ℝ) / (n : ℝ) ≤ 1 + Real.log U := by
    have hh : ∑ n ∈ Finset.Icc 1 (U / d), (1 : ℝ) / (n : ℝ) ≤ 1 + Real.log ((U / d : ℕ) : ℝ) := by
      have h1 := harmonic_le_one_add_log (U / d)
      rw [harmonic_eq_sum_Icc] at h1
      push_cast at h1
      simpa [one_div] using h1
    have hsub : Finset.Ioc (L0 / d) (U / d) ⊆ Finset.Icc 1 (U / d) := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      rw [Finset.mem_Icc]
      exact ⟨Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hn.1), hn.2⟩
    have hlog : Real.log ((U / d : ℕ) : ℝ) ≤ Real.log U := by
      by_cases h0 : U / d = 0
      · rw [h0, Nat.cast_zero, Real.log_zero]
        exact Real.log_natCast_nonneg U
      · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero h0)
          (by exact_mod_cast Nat.div_le_self U d)
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun n : ℕ => (1 : ℝ) / (n : ℝ)) (fun _ _ _ => by positivity)
    linarith
  have hmain : |(∑ n ∈ Finset.Ioc (L0 / d) (U / d), φ (n : ℝ)) -
      ∑ m ∈ Finset.Ioc (d * (L0 / d)) (d * (U / d)), φ ((m : ℝ) / (d : ℝ)) / (d : ℝ)| ≤
      2 * K * (1 + Real.log U) + 2 * M := by
    rw [two_cofactor_block_sum d (L0 / d) (fun m : ℕ => φ ((m : ℝ) / (d : ℝ)) / (d : ℝ)) hAB,
      ← Finset.sum_sub_distrib]
    have hterm : ∀ n ∈ Finset.Ioc (L0 / d) (U / d),
        |φ (n : ℝ) - ∑ m ∈ Finset.Ioc (d * (n - 1)) (d * n),
            φ ((m : ℝ) / (d : ℝ)) / (d : ℝ)| ≤
          2 * K * (1 / (n : ℝ)) + (if n = ⌈q⌉₊ then 2 * M else 0) := by
      intro n hn
      have hn1 : 1 ≤ n :=
        Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1)
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
      have hcard : (Finset.Ioc (d * (n - 1)) (d * n)).card = d := by
        have h1 : d * n = d * (n - 1) + d := by
          obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
          simp [Nat.mul_succ]
        rw [Nat.card_Ioc]
        omega
      have hite : 0 ≤ (if n = ⌈q⌉₊ then 2 * M else 0) := by split_ifs <;> linarith
      have hKn : 0 ≤ 2 * K * (1 / (n : ℝ)) := by positivity
      have hconst : φ (n : ℝ) =
          ∑ m ∈ Finset.Ioc (d * (n - 1)) (d * n), φ (n : ℝ) / (d : ℝ) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        field_simp
      have hpt : ∀ m ∈ Finset.Ioc (d * (n - 1)) (d * n),
          |φ (n : ℝ) / (d : ℝ) - φ ((m : ℝ) / (d : ℝ)) / (d : ℝ)| ≤
            (2 * K * (1 / (n : ℝ)) + (if n = ⌈q⌉₊ then 2 * M else 0)) / (d : ℝ) := by
        intro m hm
        have hm' := Finset.mem_Ioc.mp hm
        rw [← sub_div, abs_div, abs_of_pos hd0]
        refine div_le_div_of_nonneg_right ?_ hd0.le
        have hs1 : ((n : ℝ) - 1) < (m : ℝ) / d := by
          rw [lt_div_iff₀ hd0]
          have h1 : ((d * (n - 1) : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast hm'.1
          rw [Nat.cast_mul, Nat.cast_sub hn1, Nat.cast_one] at h1
          calc ((n : ℝ) - 1) * d = d * ((n : ℝ) - 1) := by ring
            _ < m := h1
        have hs2 : (m : ℝ) / d ≤ (n : ℝ) := by
          rw [div_le_iff₀ hd0]
          have h1 : (m : ℝ) ≤ ((d * n : ℕ) : ℝ) := by exact_mod_cast hm'.2
          rw [Nat.cast_mul] at h1
          linarith [mul_comm (d : ℝ) (n : ℝ)]
        have hs0 : 0 < (m : ℝ) / d := by linarith
        by_cases hs : q ≤ (m : ℝ) / d
        · have h1 := hLip _ _ hs hs2
          rw [abs_sub_comm] at h1
          have h2 : ((n : ℝ) - (m : ℝ) / d) / ((m : ℝ) / d) ≤ 2 / (n : ℝ) := by
            rw [div_le_div_iff₀ hs0 hn0]
            rcases hn1.eq_or_lt with h1n | h2n
            · have hn1R : (n : ℝ) = 1 := by rw [← h1n]; norm_num
              rw [hn1R]
              linarith
            · have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2n
              have h3 := mul_le_mul_of_nonneg_right
                (show (n : ℝ) - (m : ℝ) / d ≤ 1 by linarith) hn0.le
              linarith
          have h3 := mul_le_mul_of_nonneg_left h2 hK
          have h4 : K * (2 / (n : ℝ)) = 2 * K * (1 / (n : ℝ)) := by ring
          linarith
        · push Not at hs
          rw [hlow _ hs0 hs, sub_zero]
          by_cases hnq : (n : ℝ) < q
          · rw [hlow _ hn0 hnq, abs_zero]
            linarith
          · have hce : n = ⌈q⌉₊ :=
              ((Nat.ceil_eq_iff (by omega)).mpr
                ⟨by rw [Nat.cast_sub hn1, Nat.cast_one]; linarith, not_lt.mp hnq⟩).symm
            have := hφM (n : ℝ)
            split_ifs
            linarith
      rw [hconst, ← Finset.sum_sub_distrib]
      calc |∑ m ∈ Finset.Ioc (d * (n - 1)) (d * n),
              (φ (n : ℝ) / (d : ℝ) - φ ((m : ℝ) / (d : ℝ)) / (d : ℝ))|
          ≤ ∑ m ∈ Finset.Ioc (d * (n - 1)) (d * n),
              |φ (n : ℝ) / (d : ℝ) - φ ((m : ℝ) / (d : ℝ)) / (d : ℝ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ Finset.Ioc (d * (n - 1)) (d * n),
              (2 * K * (1 / (n : ℝ)) + (if n = ⌈q⌉₊ then 2 * M else 0)) / (d : ℝ) :=
            Finset.sum_le_sum hpt
        _ = 2 * K * (1 / (n : ℝ)) + (if n = ⌈q⌉₊ then 2 * M else 0) := by
            rw [Finset.sum_const, hcard, nsmul_eq_mul]
            field_simp
    have hitesum : ∑ n ∈ Finset.Ioc (L0 / d) (U / d), (if n = ⌈q⌉₊ then 2 * M else 0) ≤
        2 * M := by
      rw [Finset.sum_ite_eq']
      split_ifs <;> linarith
    calc |∑ n ∈ Finset.Ioc (L0 / d) (U / d),
            (φ (n : ℝ) - ∑ m ∈ Finset.Ioc (d * (n - 1)) (d * n),
              φ ((m : ℝ) / (d : ℝ)) / (d : ℝ))|
        ≤ ∑ n ∈ Finset.Ioc (L0 / d) (U / d),
            |φ (n : ℝ) - ∑ m ∈ Finset.Ioc (d * (n - 1)) (d * n),
              φ ((m : ℝ) / (d : ℝ)) / (d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Ioc (L0 / d) (U / d),
            (2 * K * (1 / (n : ℝ)) + (if n = ⌈q⌉₊ then 2 * M else 0)) :=
          Finset.sum_le_sum hterm
      _ = 2 * K * ∑ n ∈ Finset.Ioc (L0 / d) (U / d), (1 : ℝ) / (n : ℝ) +
            ∑ n ∈ Finset.Ioc (L0 / d) (U / d), (if n = ⌈q⌉₊ then 2 * M else 0) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 2 * K * (1 + Real.log U) + 2 * M :=
          add_le_add (mul_le_mul_of_nonneg_left hharm (by positivity)) hitesum
  have a1 := abs_le.mp hmain
  have a2 := abs_le.mp hE1
  have a3 := abs_le.mp hE2
  rw [abs_le]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]

/-- P0069 page 51 display 5.17, the cofactor variable of the E2 sum of display 5.15. An outer
product `d` with `U < d q` contributes nothing on either side: every cofactor and every real
point `m / d` is below the level `q`, where the density vanishes. -/
theorem two_cofactor_pair_zero (φ : ℝ → ℝ) {q : ℝ}
    (hlow : ∀ t, 0 < t → t < q → φ t = 0) {d : ℕ} (hd : 1 ≤ d) (L0 U : ℕ)
    (hU : (U : ℝ) < (d : ℝ) * q) :
    (∑ n ∈ Finset.Ioc (L0 / d) (U / d), φ (n : ℝ)) -
        ∑ m ∈ Finset.Ioc L0 U, φ ((m : ℝ) / (d : ℝ)) / (d : ℝ) = 0 := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h1 : ∑ n ∈ Finset.Ioc (L0 / d) (U / d), φ (n : ℝ) = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    have hn' := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn'.1
      exact_mod_cast this
    have h2 : n * d ≤ U := (Nat.le_div_iff_mul_le hd).mp hn'.2
    have h3 : (n : ℝ) * d ≤ U := by exact_mod_cast h2
    refine hlow _ hn0 ?_
    have h4 : (d : ℝ) * n < d * q := by linarith [mul_comm (d : ℝ) (n : ℝ)]
    exact lt_of_mul_lt_mul_left h4 hd0.le
  have h2 : ∑ m ∈ Finset.Ioc L0 U, φ ((m : ℝ) / (d : ℝ)) / (d : ℝ) = 0 := by
    refine Finset.sum_eq_zero fun m hm => ?_
    have hm' := Finset.mem_Ioc.mp hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by
      have : 0 < m := by omega
      exact_mod_cast this
    have h3 : (m : ℝ) ≤ U := by exact_mod_cast hm'.2
    rw [hlow _ (div_pos hm0 hd0) (by rw [div_lt_iff₀ hd0]; linarith [mul_comm (d : ℝ) q]),
      zero_div]
  rw [h1, h2, sub_zero]

/-- P0069 page 51 display 5.17, the cofactor variable of the E2 sum of display 5.15. The
Buchstab density `ω(log t / log p) / log p` of the integers with no prime factor below a prime
`p ≥ 2` is bounded by 2, vanishes on `(0, p)` and satisfies
`|φ s - φ t| ≤ 4 (t - s) / s` for `p ≤ s ≤ t`. -/
theorem two_cofactor_density_props (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω) {p : ℕ} (hp : 2 ≤ p) :
    (∀ t : ℝ, |ω (Real.log t / Real.log (p : ℝ)) / Real.log (p : ℝ)| ≤ 2) ∧
    (∀ t : ℝ, 0 < t → t < (p : ℝ) →
      ω (Real.log t / Real.log (p : ℝ)) / Real.log (p : ℝ) = 0) ∧
    (∀ s t : ℝ, (p : ℝ) ≤ s → s ≤ t →
      |ω (Real.log s / Real.log (p : ℝ)) / Real.log (p : ℝ) -
        ω (Real.log t / Real.log (p : ℝ)) / Real.log (p : ℝ)| ≤ 4 * ((t - s) / s)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hl : (1 / 2 : ℝ) < Real.log (p : ℝ) := by
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_le_log (by norm_num) hp2
    linarith
  have hl0 : 0 < Real.log (p : ℝ) := by linarith
  refine ⟨fun t => ?_, fun t ht htp => ?_, fun s t hs hst => ?_⟩
  · rw [abs_div, abs_of_pos hl0, div_le_iff₀ hl0]
    have h0 := two_density_buchstab_nonneg hω hz (Real.log t / Real.log (p : ℝ))
    have h1 := LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz
      (Real.log t / Real.log (p : ℝ))
    rw [abs_of_nonneg h0]
    linarith
  · rw [hz _ ((div_lt_one hl0).mpr (Real.log_lt_log ht htp)), zero_div]
  · have hs0 : 0 < s := by linarith
    have ht0 : 0 < t := by linarith
    have hu : 1 ≤ Real.log s / Real.log (p : ℝ) :=
      (one_le_div hl0).mpr (Real.log_le_log (by linarith) hs)
    have huv : Real.log s / Real.log (p : ℝ) ≤ Real.log t / Real.log (p : ℝ) :=
      div_le_div_of_nonneg_right (Real.log_le_log hs0 hst) hl0.le
    have hL := two_density_buchstab_lipschitz hω hz hu huv
    have hlog : Real.log t - Real.log s ≤ (t - s) / s := by
      have h1 := Real.log_le_sub_one_of_pos (div_pos ht0 hs0)
      rw [Real.log_div ht0.ne' hs0.ne'] at h1
      have he : t / s - 1 = (t - s) / s := by field_simp
      linarith
    rw [← sub_div, abs_div, abs_of_pos hl0, div_le_iff₀ hl0]
    have hq0 : 0 ≤ (t - s) / s := div_nonneg (by linarith) hs0.le
    have h1 : Real.log t / Real.log (p : ℝ) - Real.log s / Real.log (p : ℝ) ≤
        ((t - s) / s) / Real.log (p : ℝ) := by
      rw [← sub_div]
      exact div_le_div_of_nonneg_right hlog hl0.le
    have h2 : ((t - s) / s) / Real.log (p : ℝ) ≤ 4 * ((t - s) / s) * Real.log (p : ℝ) := by
      rw [div_le_iff₀ hl0]
      have h3 : (1 / 4 : ℝ) < Real.log (p : ℝ) * Real.log (p : ℝ) := by nlinarith
      nlinarith [mul_nonneg hq0 (by linarith : (0 : ℝ) ≤ 4 * (Real.log (p : ℝ) *
        Real.log (p : ℝ)) - 1)]
    linarith

/-- P0069 page 51 display 5.17, the cofactor variable of the E2 sum of display 5.15, one prime
pair. For primes `p1`, `p2` with `p2 ≥ W` and a prefix end `U ≤ Y2`, the cofactor sum of the
Buchstab density at level `p2` differs from its average over `m` by at most
`(8 (1 + log Y2) + 8) (Y2 / W) / (p1 p2)`: the difference vanishes unless `p1 p2 ^ 2 ≤ U`,
and then `p1 p2 ≤ Y2 / W`. -/
theorem two_cofactor_pair_term (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {p1 p2 : ℕ} (L0 : ℕ) {U : ℕ} {Y2 W : ℝ} (hp1 : p1.Prime) (hp2 : p2.Prime) (hW : 0 < W)
    (hWp : W ≤ (p2 : ℝ)) (hUY : (U : ℝ) ≤ Y2) (hY2 : 1 ≤ Y2) :
    |(∑ n ∈ Finset.Ioc (L0 / (p1 * p2)) (U / (p1 * p2)),
          ω (Real.log (n : ℝ) / Real.log (p2 : ℝ)) / Real.log (p2 : ℝ)) -
        ∑ m ∈ Finset.Ioc L0 U,
          ω (Real.log ((m : ℝ) / ((p1 : ℝ) * (p2 : ℝ))) / Real.log (p2 : ℝ)) /
            Real.log (p2 : ℝ) / ((p1 : ℝ) * (p2 : ℝ))| ≤
      (8 * (1 + Real.log Y2) + 8) * (Y2 / W) * (1 / ((p1 * p2 : ℕ) : ℝ)) := by
  have hd : 1 ≤ p1 * p2 := Nat.mul_pos hp1.pos hp2.pos
  have hdR : (0 : ℝ) < ((p1 * p2 : ℕ) : ℝ) := by exact_mod_cast hd
  have hp2R : (2 : ℝ) ≤ (p2 : ℝ) := by exact_mod_cast hp2.two_le
  obtain ⟨hM, hlow, hLip⟩ := two_cofactor_density_props ω hω hz hp2.two_le
  have hR : 0 ≤ 8 * (1 + Real.log Y2) + 8 := by
    have := Real.log_nonneg hY2
    linarith
  have hY20 : 0 ≤ Y2 := by linarith
  have hRHS0 : 0 ≤ (8 * (1 + Real.log Y2) + 8) * (Y2 / W) * (1 / ((p1 * p2 : ℕ) : ℝ)) :=
    mul_nonneg (mul_nonneg hR (div_nonneg hY20 hW.le)) (div_nonneg zero_le_one hdR.le)
  by_cases hLU : L0 ≤ U
  swap
  · rw [Finset.Ioc_eq_empty (a := L0 / (p1 * p2)) (b := U / (p1 * p2)) (by
        have := Nat.div_le_div_right (c := p1 * p2) (le_of_not_ge hLU)
        omega),
      Finset.Ioc_eq_empty (a := L0) (b := U) (by omega), Finset.sum_empty, Finset.sum_empty,
      sub_zero, abs_zero]
    exact hRHS0
  by_cases hUq : (U : ℝ) < ((p1 * p2 : ℕ) : ℝ) * (p2 : ℝ)
  · have h0 := two_cofactor_pair_zero
      (fun t : ℝ => ω (Real.log t / Real.log (p2 : ℝ)) / Real.log (p2 : ℝ)) hlow hd L0 U hUq
    simp only [Nat.cast_mul] at h0
    rw [h0, abs_zero]
    exact hRHS0
  · push Not at hUq
    have hb := two_cofactor_pair_bound
      (fun t : ℝ => ω (Real.log t / Real.log (p2 : ℝ)) / Real.log (p2 : ℝ))
      (q := (p2 : ℝ)) (K := 4) (M := 2) (by linarith) (by norm_num) (by norm_num)
      hM hlow hLip hd hLU
    simp only [Nat.cast_mul] at hb
    refine hb.trans ?_
    have hU0 : (0 : ℝ) < (U : ℝ) := lt_of_lt_of_le (mul_pos hdR (by linarith)) hUq
    have hlog : Real.log U ≤ Real.log Y2 := Real.log_le_log hU0 hUY
    have hone : 1 ≤ (Y2 / W) * (1 / ((p1 * p2 : ℕ) : ℝ)) := by
      rw [div_mul_div_comm, mul_one, le_div_iff₀ (mul_pos hW hdR), one_mul]
      have h1 : ((p1 * p2 : ℕ) : ℝ) * W ≤ ((p1 * p2 : ℕ) : ℝ) * (p2 : ℝ) :=
        mul_le_mul_of_nonneg_left hWp hdR.le
      linarith [mul_comm W ((p1 * p2 : ℕ) : ℝ)]
    calc 2 * 4 * (1 + Real.log U) + 4 * 2 ≤ (8 * (1 + Real.log Y2) + 8) * 1 := by linarith
      _ ≤ (8 * (1 + Real.log Y2) + 8) * ((Y2 / W) * (1 / ((p1 * p2 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hone hR
      _ = _ := by ring

/-- P0069 page 51 display 5.17, the cofactor variable of the E2 sum of display 5.15. Summation
over the outer pairs: a family of terms each bounded by `RT / (p1 p2)` sums to at most `RT`
times the square of the harmonic sum. -/
theorem two_cofactor_sum_bound {I : Finset (ℕ × ℕ)} {N : ℕ}
    (hI : I ⊆ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)) (F : ℕ × ℕ → ℝ) {RT : ℝ} (hRT : 0 ≤ RT)
    (h : ∀ i ∈ I, |F i| ≤ RT * (1 / ((i.1 * i.2 : ℕ) : ℝ))) :
    |∑ i ∈ I, F i| ≤ RT * (1 + Real.log N) ^ 2 :=
  calc |∑ i ∈ I, F i| ≤ ∑ i ∈ I, |F i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ I, RT * (1 / ((i.1 * i.2 : ℕ) : ℝ)) := Finset.sum_le_sum h
    _ = RT * ∑ i ∈ I, (1 : ℝ) / ((i.1 * i.2 : ℕ) : ℝ) := by rw [Finset.mul_sum]
    _ ≤ RT * (1 + Real.log N) ^ 2 :=
        mul_le_mul_of_nonneg_left (pair_reciprocal_sum_le N I hI) hRT

/-- P0069 page 51, display 5.17, the E2 sum of display 5.15, the cofactor variable `n3`.
For each prime pair `p1 p2` with exponents in E2 the sum over the cofactors `n` in
`(Y / (p1 p2), U / (p1 p2)]` of the Buchstab density `ω(log n / log p2) / log p2` is the sum
over `m` in `(Y, U]` of the same density at the real point `m / (p1 p2)`, divided by `p1 p2`,
with a total error `O(Y ^ (9 / 10) log^3 Y)` over all pairs, hence with every log power
saved. No prime number theorem is used. -/
theorem two_cofactor_riemann (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ U : ℕ, U ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
            i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
              lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)),
          ((∑ n ∈ Finset.Ioc (⌊x ^ (11 / 20 + ε)⌋₊ / (i.1 * i.2)) (U / (i.1 * i.2)),
              ω (Real.log (n : ℝ) / Real.log (i.2 : ℝ)) / Real.log (i.2 : ℝ)) -
            ∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ U,
              ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2 : ℝ))) / Real.log (i.2 : ℝ)) /
                Real.log (i.2 : ℝ) / ((i.1 : ℝ) * (i.2 : ℝ)))| ≤
        C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C1, hC1⟩ := log_rpow_lt_rpow (A + 3)
  refine ⟨max (max 576 C1) ((2 : ℝ) ^ 36), fun x hx U hU => ?_⟩
  have hC576 : (576 : ℝ) ≤ max (max 576 C1) ((2 : ℝ) ^ 36) :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hxC1 : C1 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hx36 : (2 : ℝ) ^ 36 ≤ x := (le_max_right _ _).trans hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx36
  have hxpos : 0 < x := by linarith
  have hY49 : (4 : ℝ) ^ 9 ≤ x ^ (11 / 20 + ε) := by
    refine shortY_ge_of_sq_le hε hx1 ?_
    have h49 : ((4 : ℝ) ^ 9) ^ 2 = (2 : ℝ) ^ 36 := by norm_num
    rw [h49]
    exact hx36
  have hYpos : 0 < x ^ (11 / 20 + ε) := lt_of_lt_of_le (by norm_num) hY49
  have hY1 : (1 : ℝ) ≤ x ^ (11 / 20 + ε) := le_trans (by norm_num) hY49
  have hl1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hxpos]
    have h1 := Real.exp_one_lt_d9
    have h2 : (3 : ℝ) ≤ 2 ^ 36 := by norm_num
    linarith
  have hlam0 : 0 < Real.log x := by linarith
  obtain ⟨-, hlX2⟩ := log_scale_bounds hε hε8 hxpos hl1
  have hl0 : 0 ≤ Real.log (2 * x ^ (11 / 20 + ε)) := Real.log_nonneg (by linarith)
  have hW : 0 < (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hNle : (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
    Nat.floor_le (by linarith)
  have hN1 : 1 ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ :=
    Nat.le_floor (by rw [Nat.cast_one]; linarith)
  have hU' : (U : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := (Nat.cast_le.mpr hU).trans hNle
  have hlogN : Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ Real.log (2 * x ^ (11 / 20 + ε)) :=
    Real.log_le_log (by exact_mod_cast hN1) hNle
  have hlogN0 : 0 ≤ Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := Real.log_natCast_nonneg _
  have hR0 : 0 ≤ 8 * (1 + Real.log (2 * x ^ (11 / 20 + ε))) + 8 := by linarith
  have hT0 : 0 ≤ 2 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) :=
    div_nonneg (by linarith) hW.le
  have hRT : 0 ≤ (8 * (1 + Real.log (2 * x ^ (11 / 20 + ε))) + 8) *
      (2 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)) := mul_nonneg hR0 hT0
  refine (two_cofactor_sum_bound (Finset.filter_subset _ _) _ hRT (fun i hi => ?_)).trans ?_
  · obtain ⟨hp1, hp2, -, hE⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨-, hWp⟩ := lowerTwo_outer_bounds hε8 hY49 hp1 hp2 hE
    exact two_cofactor_pair_term ω hω hz _ hp1 hp2 hW hWp hU' (by linarith)
  -- the final comparison of sizes
  have ha : 8 * (1 + Real.log (2 * x ^ (11 / 20 + ε))) + 8 ≤ 32 * Real.log x := by linarith
  have hb : (1 + Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ)) ^ 2 ≤ 9 * Real.log x ^ 2 := by
    have h1 : 1 + Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 3 * Real.log x := by linarith
    have h2 := pow_le_pow_left₀ (by linarith) h1 2
    have h3 : (3 * Real.log x) ^ 2 = 9 * Real.log x ^ 2 := by ring
    linarith
  have hprod : (8 * (1 + Real.log (2 * x ^ (11 / 20 + ε))) + 8) *
      (2 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)) *
      (1 + Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ)) ^ 2 ≤
      32 * Real.log x * (2 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)) *
        (9 * Real.log x ^ 2) :=
    mul_le_mul (mul_le_mul_of_nonneg_right ha hT0) hb (sq_nonneg _)
      (mul_nonneg (by linarith) hT0)
  have hWge : x ^ (11 / 200 : ℝ) ≤ (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) := by
    have h1 : x ^ (11 / 20 : ℝ) ≤ x ^ (11 / 20 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    calc x ^ (11 / 200 : ℝ) = (x ^ (11 / 20 : ℝ)) ^ (1 / 10 : ℝ) := by
          rw [← Real.rpow_mul (by linarith)]; norm_num
      _ ≤ (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hxpos.le _) (by linarith) (by norm_num)
  have hPpos : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hlam0 _
  have h3 : Real.log x ^ (3 : ℝ) = Real.log x ^ 3 := by
    rw [← Real.rpow_natCast]; norm_num
  have hsplit : Real.log x ^ (A + 3) = Real.log x ^ A * Real.log x ^ 3 := by
    rw [Real.rpow_add hlam0, h3]
  have hsmall : Real.log x ^ 3 / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) ≤
      Real.log x ^ (-A) := by
    rw [Real.rpow_neg hlam0.le, div_le_iff₀ hW]
    have h4 : Real.log x ^ A * Real.log x ^ 3 ≤ (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) := by
      rw [← hsplit]
      exact (hC1 x hxC1).le.trans hWge
    calc Real.log x ^ 3 = (Real.log x ^ A)⁻¹ * (Real.log x ^ A * Real.log x ^ 3) := by
          field_simp
      _ ≤ (Real.log x ^ A)⁻¹ * (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) :=
          mul_le_mul_of_nonneg_left h4 (inv_nonneg.mpr hPpos.le)
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg hlam0.le _
  calc (8 * (1 + Real.log (2 * x ^ (11 / 20 + ε))) + 8) *
        (2 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)) *
        (1 + Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ)) ^ 2
      ≤ 32 * Real.log x * (2 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)) *
        (9 * Real.log x ^ 2) := hprod
    _ = 576 * x ^ (11 / 20 + ε) *
        (Real.log x ^ 3 / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)) := by ring
    _ ≤ 576 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
        mul_le_mul_of_nonneg_left hsmall (by linarith)
    _ ≤ max (max 576 C1) ((2 : ℝ) ^ 36) * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC576 hYpos.le) hL

end LeanLab.BHP1997.LowerShortC165
