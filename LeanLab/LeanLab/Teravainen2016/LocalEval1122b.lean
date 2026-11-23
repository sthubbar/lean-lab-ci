/-
P0076, Section 4, display 4.5. Attempted proof of the MEDIUM leaf vdecay_local_eval of
VDecay1122b.lean by the Chinese remainder theorem. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.VDecay1122b
import LeanLab.Teravainen2016.BohrFourier

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- Chinese remainder theorem for complex sums over a full period m n, m and n coprime. -/
theorem le_crt_sumC (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (h : Nat.Coprime m n)
    (f g : ℕ → ℂ) :
    ∑ r ∈ range (m * n), f (r % m) * g (r % n) =
      (∑ x ∈ range m, f x) * (∑ y ∈ range n, g y) := by
  rw [sum_mul_sum, ← sum_product']
  apply sum_nbij (fun r => (r % m, r % n))
  · intro r _
    simp only [mem_product, mem_range]
    exact ⟨Nat.mod_lt r hm, Nat.mod_lt r hn⟩
  · intro r1 h1 r2 h2 heq
    simp only [Prod.mk.injEq] at heq
    have hmod := (Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨heq.1, heq.2⟩
    have e1 := Nat.mod_eq_of_lt (mem_range.mp (mem_coe.mp h1))
    have e2 := Nat.mod_eq_of_lt (mem_range.mp (mem_coe.mp h2))
    unfold Nat.ModEq at hmod
    rw [e1, e2] at hmod
    exact hmod
  · rintro ⟨x, y⟩ hxy
    simp only [coe_product, Set.mem_prod, mem_coe, mem_range] at hxy
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder h x y
    refine ⟨k % (m * n), ?_, ?_⟩
    · exact mem_coe.mpr (mem_range.mpr (Nat.mod_lt _ (Nat.mul_pos hm hn)))
    · simp only [Prod.mk.injEq]
      constructor
      · rw [Nat.mod_mod_of_dvd _ (dvd_mul_right m n)]
        unfold Nat.ModEq at hk1
        rw [hk1, Nat.mod_eq_of_lt hxy.1]
      · rw [Nat.mod_mod_of_dvd _ (dvd_mul_left n m)]
        unfold Nat.ModEq at hk2
        rw [hk2, Nat.mod_eq_of_lt hxy.2]
  · intro r _
    rfl

/-- The additive character at a over q only depends on the residue of r mod q. -/
theorem le_eC_mod (a q r : ℕ) (hq : 0 < q) :
    eC ((a : ℝ) * r / q) = eC ((a : ℝ) * ((r % q : ℕ) : ℝ) / q) := by
  have hr : (r : ℝ) = (r % q : ℕ) + q * (r / q : ℕ) := by
    exact_mod_cast (Nat.mod_add_div r q).symm
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  generalize r / q = k at hr
  rw [hr, show (a : ℝ) * ((r % q : ℕ) + q * (k : ℕ)) / q =
      (a : ℝ) * ((r % q : ℕ) : ℝ) / q + (((a * k : ℕ) : ℤ) : ℝ) by
    push_cast; field_simp]
  rw [efs_eC_add, efs_eC_int, mul_one]

/-- The pair sum behind display 4.5: over a full period P of z, the product of the
indicators of A_d1 and A_d2 against e of a s over q is 0 unless q divides lcm d1 d2, and
then equals P over q times g of lcm d1 d2 over q times the local sum T at q. -/
theorem le_pair_sum {J w : ℕ} (hw : 5 ≤ w) (b : ℤ) (z : ℝ) {d1 d2 q a : ℕ}
    (hd1 : d1 ∣ envelopingPrimeProduct w z) (hd2 : d2 ∣ envelopingPrimeProduct w z)
    (hqP : q ∣ envelopingPrimeProduct w z) (ha : Nat.Coprime a q) :
    ∑ s ∈ range (envelopingPrimeProduct w z),
      (if EnvelopingSifted w d1 (WW J w * (s : ℤ) + b) then (1 : ℂ) else 0) *
        (if EnvelopingSifted w d2 (WW J w * (s : ℤ) + b) then (1 : ℂ) else 0) *
          eC ((a : ℝ) * s / q) =
      if q ∣ Nat.lcm d1 d2 then
        ((envelopingPrimeProduct w z : ℂ) / q) *
          (envelopingDensity w (Nat.lcm d1 d2 / q) : ℂ) *
            ∑ x ∈ range q, (if EnvelopingSifted w q (WW J w * (x : ℤ) + b) then (1 : ℂ) else 0) *
              eC ((a : ℝ) * x / q)
      else 0 := by
  have hP := envelopingPrimeProduct_ne_zero w z
  set P := envelopingPrimeProduct w z with hPdef
  set L := Nat.lcm d1 d2 with hLdef
  have hLP : L ∣ P := Nat.lcm_dvd hd1 hd2
  have hone : ∀ s : ℕ,
      (if EnvelopingSifted w d1 (WW J w * (s : ℤ) + b) then (1 : ℂ) else 0) *
        (if EnvelopingSifted w d2 (WW J w * (s : ℤ) + b) then (1 : ℂ) else 0) =
      (if EnvelopingSifted w L (WW J w * (s : ℤ) + b) then (1 : ℂ) else 0) := by
    intro s
    rw [hLdef, ← efs_sifted_lcm hw hd1 hd2]
    split_ifs <;> simp_all
  simp only [hone]
  split_ifs with hqL
  · have hq0 : 0 < q := Nat.pos_of_dvd_of_pos hqP (Nat.pos_of_ne_zero hP)
    have hL0 : 0 < L := Nat.pos_of_dvd_of_pos hLP (Nat.pos_of_ne_zero hP)
    obtain ⟨m, hm⟩ := hLP
    obtain ⟨n, hn⟩ := hqL
    have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have hsqL : Squarefree L := (enveloping_divisor_support (J := J) hw (Nat.lcm_dvd hd1 hd2)).1
    have hcop : Nat.Coprime q n := Nat.coprime_of_squarefree_mul (hn ▸ hsqL)
    have hnP : n ∣ P := dvd_trans (Dvd.intro_left q hn.symm) (Nat.lcm_dvd hd1 hd2)
    have hLn : L / q = n := by rw [hn, Nat.mul_div_cancel_left n hq0]
    rw [hLn]
    -- reduce the sum over P = L m to m copies of the sum over L
    rw [hm, efs_sum_range_mul]
    have hper : ∀ j r : ℕ,
        (if EnvelopingSifted w L (WW J w * ((L * j + r : ℕ) : ℤ) + b) then (1 : ℂ) else 0) *
          eC ((a : ℝ) * ((L * j + r : ℕ) : ℝ) / q) =
        (if EnvelopingSifted w L (WW J w * (r : ℤ) + b) then (1 : ℂ) else 0) *
          eC ((a : ℝ) * (r : ℝ) / q) := by
      intro j r
      rw [efs_sifted_shift w L (WW J w) b L r j dvd_rfl]
      congr 1
      rw [le_eC_mod a q (L * j + r) hq0, le_eC_mod a q r hq0]
      congr 4
      rw [hn, mul_assoc, Nat.mul_add_mod]
    rw [sum_congr rfl (fun j _ => sum_congr rfl (fun r _ => hper j r)), sum_const, card_range,
      nsmul_eq_mul]
    -- split the sum over L = q n by the Chinese remainder theorem
    have hsplit : ∀ r : ℕ,
        (if EnvelopingSifted w L (WW J w * (r : ℤ) + b) then (1 : ℂ) else 0) *
          eC ((a : ℝ) * (r : ℝ) / q) =
        ((if EnvelopingSifted w q (WW J w * ((r % q : ℕ) : ℤ) + b) then (1 : ℂ) else 0) *
            eC ((a : ℝ) * ((r % q : ℕ) : ℝ) / q)) *
          (if EnvelopingSifted w n (WW J w * ((r % n : ℕ) : ℤ) + b) then (1 : ℂ) else 0) := by
      intro r
      have hlcm : Nat.lcm q n = L := by rw [hn, hcop.lcm_eq_mul]
      have e1 : EnvelopingSifted w q (WW J w * (r : ℤ) + b) ↔
          EnvelopingSifted w q (WW J w * ((r % q : ℕ) : ℤ) + b) := by
        have := efs_sifted_shift w q (WW J w) b q (r % q) (r / q) dvd_rfl
        rw [Nat.div_add_mod] at this
        exact this
      have e2 : EnvelopingSifted w n (WW J w * (r : ℤ) + b) ↔
          EnvelopingSifted w n (WW J w * ((r % n : ℕ) : ℤ) + b) := by
        have := efs_sifted_shift w n (WW J w) b n (r % n) (r / n) dvd_rfl
        rw [Nat.div_add_mod] at this
        exact this
      have e3 : EnvelopingSifted w L (WW J w * (r : ℤ) + b) ↔
          (EnvelopingSifted w q (WW J w * (r : ℤ) + b) ∧
            EnvelopingSifted w n (WW J w * (r : ℤ) + b)) := by
        rw [← hlcm]
        exact (efs_sifted_lcm hw hqP hnP _).symm
      rw [le_eC_mod a q r hq0]
      have hL' := e3
      rw [e1, e2] at hL'
      by_cases h1 : EnvelopingSifted w q (WW J w * ((r % q : ℕ) : ℤ) + b) <;>
        by_cases h2 : EnvelopingSifted w n (WW J w * ((r % n : ℕ) : ℤ) + b) <;>
          simp only [hL', h1, h2, and_self, and_true, and_false, true_and, false_and,
            if_true, if_false, one_mul, mul_one, zero_mul, mul_zero]
    rw [sum_congr rfl (fun r _ => hsplit r), hn,
      le_crt_sumC q n hq0 hn0 hcop
        (fun x => (if EnvelopingSifted w q (WW J w * (x : ℤ) + b) then (1 : ℂ) else 0) *
          eC ((a : ℝ) * (x : ℝ) / q))
        (fun y => if EnvelopingSifted w n (WW J w * (y : ℤ) + b) then (1 : ℂ) else 0)]
    have hcnt := efs_count_period (J := J) hw b z hnP
    have hcntC : ∑ y ∈ range n,
        (if EnvelopingSifted w n (WW J w * (y : ℤ) + b) then (1 : ℂ) else 0) =
        ((n : ℝ) * envelopingDensity w n : ℝ) := by
      rw [← hcnt]
      push_cast
      apply sum_congr rfl
      intro y _
      split_ifs <;> simp
    rw [hcntC]
    have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
    push_cast
    field_simp
  · apply efs_periodic_vanish P L q a hP hLP hqP hqL ha
    intro j r
    simp only [efs_sifted_shift w L (WW J w) b L r j dvd_rfl]

/-- The MEDIUM leaf `vdecay_local_eval` of VDecay1122b.lean, proved: display 4.5 with the
trivial bound g of q on the local sum at q. -/
theorem vdecay_local_eval_proved {J w : ℕ} (hw : 5 ≤ w) (b : ℤ) (M : ℕ) {q a : ℕ}
    (hqP : q ∣ envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)))
    (ha : a < q) (hcop : Nat.Coprime a q) :
    ‖envelopingVraw w (WW J w) b M q a‖ ≤
      envelopingDensity w q *
        |envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) *
          ∑ d1 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
            ∑ d2 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
              if q ∣ Nat.lcm d1 d2 then
                envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) *
                  envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) *
                    envelopingDensity w (Nat.lcm d1 d2 / q)
              else 0| := by
  unfold envelopingVraw
  simp only [efs_F_expand]
  generalize (M : ℝ) ^ ((1 : ℝ) / 10) = z at hqP ⊢
  have hP := envelopingPrimeProduct_ne_zero w z
  have hq0 : 0 < q := Nat.pos_of_dvd_of_pos hqP (Nat.pos_of_ne_zero hP)
  set P := envelopingPrimeProduct w z with hPdef
  set T : ℂ := ∑ x ∈ range q,
    (if EnvelopingSifted w q (WW J w * (x : ℤ) + b) then (1 : ℂ) else 0) *
      eC ((a : ℝ) * x / q) with hTdef
  set Q : ℝ := ∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors,
    if q ∣ Nat.lcm d1 d2 then
      envelopingRho w d1 z * envelopingRho w d2 z * envelopingDensity w (Nat.lcm d1 d2 / q)
    else 0 with hQdef
  have hterm : ∀ s : ℕ,
      ((∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors,
          envelopingG w 1 z *
            (if EnvelopingSifted w d1 (WW J w * (s : ℤ) + b) then envelopingRho w d1 z else 0) *
            (if EnvelopingSifted w d2 (WW J w * (s : ℤ) + b) then envelopingRho w d2 z else 0)
          : ℝ) : ℂ) * eC ((a : ℝ) * s / q) =
        ∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors,
          ((envelopingG w 1 z * envelopingRho w d1 z * envelopingRho w d2 z : ℝ) : ℂ) *
            ((if EnvelopingSifted w d1 (WW J w * (s : ℤ) + b) then (1 : ℂ) else 0) *
              (if EnvelopingSifted w d2 (WW J w * (s : ℤ) + b) then (1 : ℂ) else 0) *
                eC ((a : ℝ) * s / q)) := by
    intro s
    push_cast
    rw [sum_mul]
    apply sum_congr rfl
    intro d1 _
    rw [sum_mul]
    apply sum_congr rfl
    intro d2 _
    split_ifs <;> push_cast <;> ring
  have hsum : ∑ s ∈ range P,
      ((∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors,
          envelopingG w 1 z *
            (if EnvelopingSifted w d1 (WW J w * (s : ℤ) + b) then envelopingRho w d1 z else 0) *
            (if EnvelopingSifted w d2 (WW J w * (s : ℤ) + b) then envelopingRho w d2 z else 0)
          : ℝ) : ℂ) * eC ((a : ℝ) * s / q) =
        ((P : ℂ) / q) * T * ((envelopingG w 1 z * Q : ℝ) : ℂ) := by
    rw [sum_congr rfl (fun s _ => hterm s), sum_comm]
    have h2 : ∀ d1 ∈ P.divisors, ∑ s ∈ range P, ∑ d2 ∈ P.divisors,
        ((envelopingG w 1 z * envelopingRho w d1 z * envelopingRho w d2 z : ℝ) : ℂ) *
            ((if EnvelopingSifted w d1 (WW J w * (s : ℤ) + b) then (1 : ℂ) else 0) *
              (if EnvelopingSifted w d2 (WW J w * (s : ℤ) + b) then (1 : ℂ) else 0) *
                eC ((a : ℝ) * s / q)) =
        ∑ d2 ∈ P.divisors, ((P : ℂ) / q) * T * ((envelopingG w 1 z *
          (if q ∣ Nat.lcm d1 d2 then
            envelopingRho w d1 z * envelopingRho w d2 z * envelopingDensity w (Nat.lcm d1 d2 / q)
          else 0) : ℝ) : ℂ) := by
      intro d1 hd1
      rw [sum_comm]
      apply sum_congr rfl
      intro d2 hd2
      rw [← mul_sum, le_pair_sum (J := J) hw b z (Nat.dvd_of_mem_divisors hd1)
        (Nat.dvd_of_mem_divisors hd2) hqP hcop]
      split_ifs <;> push_cast <;> ring
    rw [sum_congr rfl h2, hQdef]
    simp only [Finset.mul_sum P.divisors, Complex.ofReal_sum]
  rw [hsum]
  have hPC : (P : ℂ) ≠ 0 := by exact_mod_cast hP
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have heq : 1 / (P : ℂ) * ((P : ℂ) / q * T * ((envelopingG w 1 z * Q : ℝ) : ℂ)) =
      T / q * ((envelopingG w 1 z * Q : ℝ) : ℂ) := by
    field_simp
  rw [heq, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
  have hTle : ‖T‖ ≤ (q : ℝ) * envelopingDensity w q := by
    rw [← efs_count_period (J := J) hw b z hqP]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    apply sum_congr rfl
    intro x _
    rw [norm_mul, eC_norm, mul_one]
    split_ifs <;> simp
  have hq0r : (0 : ℝ) < q := by exact_mod_cast hq0
  calc ‖T‖ / q * |envelopingG w 1 z * Q| ≤ (q : ℝ) * envelopingDensity w q / q *
        |envelopingG w 1 z * Q| :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hTle hq0r.le) (abs_nonneg _)
    _ = envelopingDensity w q * |envelopingG w 1 z * Q| := by
      field_simp

/-- Twin check against the leaf statement. -/
theorem vdecay_local_eval_twin : type_of% @LeanLab.Teravainen2016.vdecay_local_eval :=
  @vdecay_local_eval_proved

/-- Assembly with the local evaluation leaf proved: `enveloping_v_decay` conditional only on
the Ramare and Ruzsa leaf vdecay_quadratic_bound. -/
theorem enveloping_v_decay_of_quadratic_bound :
    ∃ D : ℝ → ℝ, (∀ ε : ℝ, 0 < ε → 0 < D ε) ∧
      ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
        0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
          ∀ ε : ℝ, 0 < ε → ∀ q : ℕ, 1 ≤ q → ∀ a < q, Nat.Coprime a q →
            ‖envelopingV w (WW J w) b M q a‖ ≤ D ε * (q : ℝ) ^ (ε - 1) := by
  obtain ⟨K, hK1, HB⟩ := vdecay_quadratic_bound
  have hK2 : (1 : ℝ) ≤ 2 * K := by linarith
  choose C hC0 hC using fun (ε : ℝ) (hε : 0 < ε) => vdecay_omega_pow_le hK2 hε
  refine ⟨fun ε => if h : 0 < ε then C ε h else 1, ?_, ?_⟩
  · intro ε hε
    simp only [hε, dite_true]
    exact hC0 ε hε
  intro J w hJ hw b hb hbW hamen M hM ε hε q hq a ha hcop
  simp only [hε, dite_true]
  have hwBig : (5 : ℝ) ≤ wBig := by
    calc (5 : ℝ) ≤ 10 := by norm_num
      _ = (10 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (Real.one_le_rpow (by norm_num) (by positivity))
  have hw5 : 5 ≤ w := by exact_mod_cast (hwBig.trans hw)
  have hz : (1 : ℝ) ≤ (M : ℝ) ^ ((1 : ℝ) / 10) :=
    Real.one_le_rpow (by exact_mod_cast hM) (by norm_num)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  unfold envelopingV
  split_ifs with hs
  · obtain ⟨hqP, hsq, -, -, -⟩ := hs
    have hA := vdecay_local_eval_proved (J := J) hw5 b M hqP ha hcop
    have hBq := HB w hw _ hz q hqP
    have hD := vdecay_density_le w hsq
    have hc := hC ε hε q hq
    calc _ ≤ _ := hA
      _ ≤ (2 : ℝ) ^ q.primeFactors.card / q * K ^ q.primeFactors.card :=
          mul_le_mul hD hBq (abs_nonneg _) (by positivity)
      _ = (2 * K) ^ q.primeFactors.card / q := by rw [mul_pow]; ring
      _ ≤ C ε hε * (q : ℝ) ^ ε / q := div_le_div_of_nonneg_right hc hq0.le
      _ = C ε hε * (q : ℝ) ^ (ε - 1) := by
          rw [Real.rpow_sub_one hq0.ne', mul_div_assoc]
  · rw [norm_zero]
    exact mul_nonneg (hC0 ε hε).le (Real.rpow_nonneg hq0.le _)

/-- Twin check: the sharpened assembly has exactly the type of the original leaf. -/
theorem enveloping_v_decay_twin2 : type_of% @LeanLab.Teravainen2016.enveloping_v_decay :=
  enveloping_v_decay_of_quadratic_bound

end LeanLab.Teravainen2016
