/-
P0076, Theorem 1.1, wiring of the burst-20261122 splits into the route of theorem_1_1.
theorem_1_1_of_split_leaves has the statement Theorem11 of theorem_1_1 and is proved from the
new _of_leaves theorems, so it rests only on the LEAFs of the new split files, not on the
five OPEN and CITED inputs of MainInputs.lean and MainInputsRestriction.lean.
The Section 4 chain below repeats the proofs of paper_enveloping_domination_input,
paper_enveloping_fourier_input, paper_enveloping_mean_input and
paper_cross_scale_restriction_input with the split inputs in place of the old ones.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.Statements
import LeanLab.Teravainen2016.G1LowerClosed
import LeanLab.Teravainen2016.MertensMod4Bias
import LeanLab.Teravainen2016.LevelSetSplit
import LeanLab.Teravainen2016.SelbergIdentity
import LeanLab.Teravainen2016.Lemma53Density

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- Page 15, second inequality after display 4.3, routed through MertensMod4Bias:
the proof of leaf_euler_product_ge_log_ratio_of_leaves with leaf_mertens_mod4_bias_of_leaves. -/
theorem wired_log_ratio :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℕ, wBig ≤ w → ∀ z : ℝ, 1 ≤ z →
      (Real.log z / Real.log w) ^ ((3 : ℝ) / 2) ≤
        C * ∏ p ∈ (range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z),
          (1 - (envelopingOmega w p : ℝ) / p)⁻¹ := by
  obtain ⟨B, hB0, HB⟩ := leaf_mertens_mod4_bias_of_leaves
  refine ⟨Real.exp (6 + B / 2), Real.exp_pos _, ?_⟩
  intro w hw z hz1
  have hwBig1 : (10 : ℝ) ≤ wBig := by
    calc (10 : ℝ) = (10 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (Real.one_le_rpow (by norm_num) (by positivity))
  have hw10 : (10 : ℝ) ≤ w := hwBig1.trans hw
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogw1 : 1 ≤ Real.log w := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  set F := (range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z) with hF
  -- facts about primes in F
  have hFp : ∀ p ∈ F, p.Prime ∧ w < p ∧ (10 : ℝ) < p := by
    intro p hp
    have h := (mem_filter.mp hp).2
    exact ⟨h.1, h.2.1, lt_of_le_of_lt hw10 (by exact_mod_cast h.2.1)⟩
  have hx : ∀ p ∈ F, (envelopingOmega w p : ℝ) / p < 1 := by
    intro p hp
    obtain ⟨-, -, h10⟩ := hFp p hp
    have hω : (envelopingOmega w p : ℝ) ≤ 2 := by
      unfold envelopingOmega; split_ifs <;> norm_num
    rw [div_lt_one (by linarith)]; linarith
  have hfac1 : ∀ p ∈ F, 1 ≤ (1 - (envelopingOmega w p : ℝ) / p)⁻¹ := by
    intro p hp
    have h0 : 0 ≤ (envelopingOmega w p : ℝ) / p := by positivity
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp ((envelopingOmega w p : ℝ) / p) := Real.exp_le_exp.mpr h0
      _ ≤ _ := exp_le_inv_one_sub (hx p hp)
  have hP1 : 1 ≤ ∏ p ∈ F, (1 - (envelopingOmega w p : ℝ) / p)⁻¹ := one_le_prod₀ hfac1
  have hexpP : Real.exp (∑ p ∈ F, (envelopingOmega w p : ℝ) / p) ≤
      ∏ p ∈ F, (1 - (envelopingOmega w p : ℝ) / p)⁻¹ := by
    rw [Real.exp_sum]
    exact prod_le_prod₀ (fun p _ => (Real.exp_pos _).le) (fun p hp => exp_le_inv_one_sub (hx p hp))
  by_cases hzw : z < w
  · -- below w the ratio is below one and the product is at least one
    have hlz : 0 ≤ Real.log z := Real.log_nonneg hz1
    have hratio : Real.log z / Real.log w ≤ 1 := by
      rw [div_le_one hlogw]
      exact Real.log_le_log (by linarith) hzw.le
    have hr : (Real.log z / Real.log w) ^ ((3 : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one (div_nonneg hlz hlogw.le) hratio (by norm_num)
    have hC1 : 1 ≤ Real.exp (6 + B / 2) := Real.one_le_exp (by positivity)
    calc _ ≤ 1 := hr
      _ ≤ Real.exp (6 + B / 2) * 1 := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hP1 (Real.exp_pos _).le
  · push_neg at hzw
    have hz10 : (10 : ℝ) ≤ z := hw10.trans hzw
    have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
    -- F is the block of primes in mertens2_block
    have hFeq : F = (Ioc ⌊(w : ℝ)⌋₊ ⌊z⌋₊).filter Nat.Prime := by
      rw [Nat.floor_natCast]
      ext p
      simp only [hF, mem_filter, mem_range, mem_Ioc]
      constructor
      · rintro ⟨-, hp, hwp, hpz⟩
        exact ⟨⟨hwp, Nat.le_floor hpz⟩, hp⟩
      · rintro ⟨⟨hwp, hpz⟩, hp⟩
        refine ⟨by omega, hp, hwp, ?_⟩
        exact (Nat.le_floor_iff (by linarith)).mp hpz
    have hM := LeanLab.AlmostPrimes.Decomp1528b.mertens2_block (y := (w : ℝ)) (x := z) (le_trans (by norm_num) hw10) hzw
    rw [← hFeq] at hM
    have hS1 : Real.log (Real.log z) - Real.log (Real.log w) - 4 / Real.log w ≤
        ∑ p ∈ F, (1 : ℝ) / p := by
      have := (abs_le.mp hM).1; linarith
    have hbias := HB w z (le_trans (by norm_num) hw10) hzw
    rw [← hFeq] at hbias
    -- split the sum of 1/p by residue mod 4
    have hodd : ∀ p ∈ F, p % 4 = 1 ∨ p % 4 = 3 := by
      intro p hp
      obtain ⟨hpp, -, h10⟩ := hFp p hp
      have hne : p ≠ 2 := by
        intro h; rw [h] at h10; norm_num at h10
      have := hpp.eq_one_or_self_of_dvd 2
      rcases Nat.even_or_odd p with he | ho
      · exact absurd (this (even_iff_two_dvd.mp he)) (by omega)
      · have := Nat.odd_iff.mp ho; omega
    have hsplit : ∑ p ∈ F, (1 : ℝ) / p =
        ∑ p ∈ F.filter (fun p => p % 4 = 1), (1 : ℝ) / p +
          ∑ p ∈ F.filter (fun p => p % 4 = 3), (1 : ℝ) / p := by
      rw [← sum_filter_add_sum_filter_not F (fun p => p % 4 = 1)]
      congr 1
      apply sum_congr _ (fun _ _ => rfl)
      ext p
      simp only [mem_filter]
      constructor
      · rintro ⟨hp, h⟩; exact ⟨hp, by rcases hodd p hp with h' | h' <;> omega⟩
      · rintro ⟨hp, h⟩; exact ⟨hp, by omega⟩
    have hω : ∑ p ∈ F, (envelopingOmega w p : ℝ) / p =
        ∑ p ∈ F, (1 : ℝ) / p + ∑ p ∈ F.filter (fun p => p % 4 = 3), (1 : ℝ) / p := by
      rw [Finset.sum_filter (s := F) (fun p => p % 4 = 3), ← sum_add_distrib]
      apply sum_congr rfl
      intro p hp
      obtain ⟨-, hwp, -⟩ := hFp p hp
      unfold envelopingOmega
      rw [if_neg (by omega)]
      rcases hodd p hp with h | h
      · rw [if_pos h, if_neg (by omega)]; push_cast; ring
      · rw [if_neg (by omega), if_pos h]; push_cast; ring
    have hsum : (3 / 2 : ℝ) * (Real.log (Real.log z) - Real.log (Real.log w)) - (6 + B / 2) ≤
        ∑ p ∈ F, (envelopingOmega w p : ℝ) / p := by
      have h4 : 4 / Real.log w ≤ 4 := by
        rw [div_le_iff₀ hlogw]; linarith
      rw [hω]; linarith
    have hratio : (Real.log z / Real.log w) ^ ((3 : ℝ) / 2) =
        Real.exp ((3 / 2 : ℝ) * (Real.log (Real.log z) - Real.log (Real.log w))) := by
      rw [Real.rpow_def_of_pos (div_pos hlogz hlogw), Real.log_div hlogz.ne' hlogw.ne']
      ring_nf
    rw [hratio]
    calc Real.exp ((3 / 2 : ℝ) * (Real.log (Real.log z) - Real.log (Real.log w)))
        = Real.exp (6 + B / 2) *
            Real.exp ((3 / 2 : ℝ) * (Real.log (Real.log z) - Real.log (Real.log w)) - (6 + B / 2)) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (6 + B / 2) * Real.exp (∑ p ∈ F, (envelopingOmega w p : ℝ) / p) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum) (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left hexpP (Real.exp_pos _).le


/-- Proposition 4.2, routed through LevelSetSplit: the proof of
paper_enveloping_restriction_input_of_leaves with paper_enveloping_level_set_input_of_leaves. -/
theorem wired_restriction (A D : ℝ → ℝ)
    (hAD : ∀ ε : ℝ, 0 < ε → 0 < A ε ∧ 0 < D ε) :
    ∀ r : ℝ, 2 < r → ∃ C : ℝ, 0 < C ∧
      ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
        0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
          EnvelopingFourierBounds w (WW J w) b M A D →
          Restriction42 M (restrictionBeta w (WW J w) b M) r C := by
  intro r hr
  have hε : 0 < (r - 2) / 2 := by linarith
  obtain ⟨K, hK, H⟩ := paper_enveloping_level_set_input_of_leaves A D hAD ((r - 2) / 2) hε
  have hq : 0 < 2 + (r - 2) / 2 := by linarith
  have hqr : 2 + (r - 2) / 2 < r := by linarith
  have hr0 : 0 < r := by linarith
  set q : ℝ := 2 + (r - 2) / 2 with hqdef
  set Cst : ℝ := K * ((2 * K) ^ (1 / q)) ^ r * ((2 * K) ^ (1 / q)) ^ (-q) *
      (1 / 2 : ℝ) ^ (-q) * (1 - (1 / 2 : ℝ) ^ r * (1 / 2 : ℝ) ^ (-q))⁻¹ with hCst
  have hx1 : (1 / 2 : ℝ) ^ r * (1 / 2 : ℝ) ^ (-q) < 1 := by
    rw [← Real.rpow_add (by norm_num)]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  have hCpos : 0 < Cst := by
    have : 0 < (1 - (1 / 2 : ℝ) ^ r * (1 / 2 : ℝ) ^ (-q))⁻¹ := inv_pos.mpr (by linarith)
    positivity
  refine ⟨Cst ^ (1 / r), Real.rpow_pos_of_pos hCpos _, ?_⟩
  intro J w hJ hw b hb hbW hamen M hM hB a
  set E : ℝ := ((M : ℝ)⁻¹ * ∑ n ∈ range M,
      ‖a n‖ ^ 2 * restrictionBeta w (WW J w) b M n) ^ ((1 : ℝ) / 2) with hEdef
  have hE : 0 ≤ E := by
    apply Real.rpow_nonneg
    apply mul_nonneg (by positivity)
    exact sum_nonneg (fun n _ => mul_nonneg (by positivity)
      (restrictionBeta_nonneg w (WW J w) b M n))
  have hmom := dyadic_level_moment (range M)
    (fun ξ => ‖complexFhat M (fun n => a n * (restrictionBeta w (WW J w) b M n : ℂ)) ξ‖)
    (fun _ => norm_nonneg _) hE hK hq hqr (H J w hJ hw b hb hbW hamen M hM hB a)
  have hsum : 0 ≤ ∑ ξ ∈ range M,
      ‖complexFhat M (fun n => a n * (restrictionBeta w (WW J w) b M n : ℂ)) ξ‖ ^ r :=
    sum_nonneg (fun ξ _ => Real.rpow_nonneg (norm_nonneg _) r)
  have hroot := Real.rpow_le_rpow hsum hmom (by positivity : (0 : ℝ) ≤ 1 / r)
  rw [Real.mul_rpow hCpos.le (Real.rpow_nonneg hE r), ← Real.rpow_mul hE,
    mul_one_div_cancel hr0.ne', Real.rpow_one] at hroot
  exact hroot


/-- Proposition 4.1 v, v 1 0 = 1, the proof of enveloping_vraw_one_zero with the proved
Selberg identity efs_selberg_identity_proved. -/
theorem wired_vraw_one_zero {J w : ℕ} (hJ : 5 ≤ J) (hw : wBig ≤ w) {b : ℤ}
    (hb : 0 ≤ b) (hbW : b < WW J w) (hamen : Amenable (WW J w) b) {M : ℕ} (hM : 1 ≤ M) :
    envelopingVraw w (WW J w) b M 1 0 = 1 := by
  have hwBig : (5 : ℝ) ≤ wBig := by
    calc (5 : ℝ) ≤ 10 := by norm_num
      _ = (10 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (Real.one_le_rpow (by norm_num) (by positivity))
  have hw5 : 5 ≤ w := by exact_mod_cast (hwBig.trans hw)
  have hz : (1 : ℝ) ≤ (M : ℝ) ^ ((1 : ℝ) / 10) :=
    Real.one_le_rpow (by exact_mod_cast hM) (by norm_num)
  have hR : ∑ s ∈ range (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))),
      envelopingF w (WW J w) b M s =
        (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)) : ℝ) := by
    simp only [efs_F_expand]
    have hsel := efs_selberg_identity_proved hw5 hz
    generalize (M : ℝ) ^ ((1 : ℝ) / 10) = z at hsel ⊢
    rw [sum_comm]
    have hterm : ∀ d1 ∈ (envelopingPrimeProduct w z).divisors,
        ∑ s ∈ range (envelopingPrimeProduct w z),
          ∑ d2 ∈ (envelopingPrimeProduct w z).divisors,
            envelopingG w 1 z *
              (if EnvelopingSifted w d1 (WW J w * (s : ℤ) + b) then envelopingRho w d1 z else 0) *
              (if EnvelopingSifted w d2 (WW J w * (s : ℤ) + b) then envelopingRho w d2 z else 0) =
        ∑ d2 ∈ (envelopingPrimeProduct w z).divisors,
          (envelopingPrimeProduct w z : ℝ) * (envelopingG w 1 z *
            (envelopingRho w d1 z * envelopingRho w d2 z *
              envelopingDensity w (Nat.lcm d1 d2))) := by
      intro d1 hd1
      rw [sum_comm]
      apply sum_congr rfl
      intro d2 hd2
      have hc := efs_count_lcm (J := J) hw5 b z (Nat.dvd_of_mem_divisors hd1)
        (Nat.dvd_of_mem_divisors hd2)
      calc _ = envelopingG w 1 z * envelopingRho w d1 z * envelopingRho w d2 z *
            ∑ s ∈ range (envelopingPrimeProduct w z),
              ((if EnvelopingSifted w d1 (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0) *
                (if EnvelopingSifted w d2 (WW J w * (s : ℤ) + b) then (1 : ℝ) else 0)) := by
            rw [mul_sum]
            apply sum_congr rfl
            intro s _
            split_ifs <;> ring
        _ = _ := by rw [hc]; ring
    rw [sum_congr rfl hterm]
    conv_rhs => rw [← mul_one (envelopingPrimeProduct w z : ℝ), ← hsel]
    simp only [mul_sum]
  unfold envelopingVraw
  have he0 : ∀ s : ℕ, eC (((0 : ℕ) : ℝ) * s / ((1 : ℕ) : ℝ)) = 1 := by
    intro s
    simpa using efs_eC_int 0
  simp only [he0, mul_one]
  rw [← Complex.ofReal_sum, hR]
  have hP : (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)) : ℂ) ≠ 0 := by
    exact_mod_cast envelopingPrimeProduct_ne_zero _ _
  push_cast
  field_simp

/-- Proposition 4.1 iv and v, the proof of paper_enveloping_fourier_decay_input_of_leaves with
wired_vraw_one_zero, so only enveloping_v_decay remains. -/
theorem wired_fourier_decay :
    ∃ D : ℝ → ℝ, (∀ ε : ℝ, 0 < ε → 0 < D ε) ∧
      ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
        0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
          EnvelopingFourierExpansion w (WW J w) b M D := by
  obtain ⟨D, hD, Hdecay⟩ := enveloping_v_decay
  refine ⟨D, hD, ?_⟩
  intro J w hJ hw b hb hbW hamen M hM
  have hwBig : (5 : ℝ) ≤ wBig := by
    calc (5 : ℝ) ≤ 10 := by norm_num
      _ = (10 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (Real.one_le_rpow (by norm_num) (by positivity))
  have hw5 : 5 ≤ w := by exact_mod_cast (hwBig.trans hw)
  set P := envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)) with hPdef
  have hP0 : P ≠ 0 := by
    rw [hPdef, envelopingPrimeProduct]
    exact prod_ne_zero_iff.mpr (fun p hp => (mem_filter.mp hp).2.1.ne_zero)
  refine ⟨envelopingV w (WW J w) b M, ?_, ?_, ?_, ?_⟩
  · rw [envelopingV, if_pos ⟨one_dvd _, squarefree_one, Nat.coprime_one_left _,
      Nat.zero_lt_one, Nat.coprime_zero_left 1 |>.mpr rfl⟩]
    exact wired_vraw_one_zero hJ hw hb hbW hamen hM
  · intro q a h hq1
    rw [envelopingV, if_neg]
    rintro ⟨_, hsq, hcop, _, _⟩
    rcases h with h | h
    · exact h hsq
    · exact hq1 (Nat.Coprime.eq_one_of_dvd hcop (Int.natCast_dvd.mp h))
  · intro ε hε q hq a ha hcop
    exact Hdecay J w hJ hw b hb hbW hamen M hM ε hε q hq a ha hcop
  · intro n _
    rw [envelopingBeta_eq_F, enveloping_fourier_inversion]
    set t := if n = 0 then M else n
    set N := ⌊(M : ℝ) ^ ((1 : ℝ) / 5)⌋₊
    let g : ℕ → ℂ := fun q => ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      envelopingVraw w (WW J w) b M q a * eC (-((a : ℝ) * t / q))
    let h : ℕ → ℂ := fun q => ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      envelopingV w (WW J w) b M q a * eC (-((a : ℝ) * t / q))
    change ∑ q ∈ P.divisors, g q = ∑ q ∈ Icc 1 N, h q
    have h1 : ∑ q ∈ P.divisors ∩ Icc 1 N, g q = ∑ q ∈ P.divisors, g q := by
      apply sum_subset inter_subset_left
      intro q hq hqn
      have hqP : q ∣ P := Nat.dvd_of_mem_divisors hq
      have hq1 : 1 ≤ q := Nat.pos_of_mem_divisors hq
      have hqN : N < q := by
        by_contra hc
        exact hqn (mem_inter.mpr ⟨hq, mem_Icc.mpr ⟨hq1, by omega⟩⟩)
      apply sum_eq_zero
      intro a ha
      rw [enveloping_vraw_vanish w (WW J w) b M q a hqP hqN (mem_filter.mp ha).2, zero_mul]
    have h2 : ∑ q ∈ P.divisors ∩ Icc 1 N, h q = ∑ q ∈ Icc 1 N, h q := by
      apply sum_subset inter_subset_right
      intro q hq hqn
      have hqP : ¬ q ∣ P := by
        intro hd
        exact hqn (mem_inter.mpr ⟨Nat.mem_divisors.mpr ⟨hd, hP0⟩, hq⟩)
      apply sum_eq_zero
      intro a _
      rw [envelopingV, if_neg (fun hh => hqP hh.1), zero_mul]
    rw [← h1, ← h2]
    apply sum_congr rfl
    intro q hq
    have hqP : q ∣ P := Nat.dvd_of_mem_divisors (mem_inter.mp hq).1
    obtain ⟨hsq, hcop⟩ := enveloping_divisor_support (J := J) hw5 hqP
    apply sum_congr rfl
    intro a ha
    have ha' := mem_filter.mp ha
    rw [envelopingV, if_pos ⟨hqP, hsq, hcop, mem_range.mp ha'.1, ha'.2⟩]


namespace Lemma53Split

/-- Lemma 5.3, the proof of Lemma53Split.lemma53_of_leaves with local_density_of_leaves in place of
the LEAF local_density. -/
theorem wired_lemma53 : Lemma53 := by
  intro J w hJ hw b hb Q q a hQ hqQ hq1 ha haq
  by_cases hqW : IsCoprime (q : ℤ) (WW J w)
  swap
  · rw [sum_eq_zero_of_not_coprime J w b Q q a hQ hqQ haq hqW, norm_zero]
    apply mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at hqQ
    omega
  have hw100 : (100 : ℝ) ≤ w := wBig_ge_100.trans hw
  have hw32 : 32 ≤ w := by
    have : (32 : ℝ) ≤ w := by linarith
    exact_mod_cast this
  obtain ⟨q', Q', -, hQ'q, -, hmain⟩ :=
    sum_bound_of_coprime J w hJ hw b hb Q q a hQ hqQ hq1 ha haq hqW
  have hdens := Lemma53Split.local_density_of_leaves J w hJ hw b hb q Q' (Nat.pos_of_ne_zero hq0) hQ'q hqW
  have htau := divisor_card_le_fifth_of_coprime_WW hJ hw32 hq0 hqW
  have hwq : w < q := w_lt_of_coprime hJ hq1 hq0 hqW
  set S := ‖∑ c₀ ∈ QRes Q (WW J w) b, eC ((a : ℝ) * c₀ / q)‖
  set K : ℝ := (#(QRes Q (WW J w) b) : ℝ)
  set A : ℝ := (#(QRes q (WW J w * Q') b) : ℝ)
  have hS : 0 ≤ S := norm_nonneg _
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have hqpos : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have hwpos : (0 : ℝ) < w := by linarith
  have hqw : (w : ℝ) ≤ q := by exact_mod_cast hwq.le
  -- `S q^{9/10} ≤ S A ≤ τ(q) K ≤ q^{1/5} K`
  have h1 : S * (q : ℝ) ^ ((9 : ℝ) / 10) ≤ (q : ℝ) ^ ((1 : ℝ) / 5) * K := by
    calc S * (q : ℝ) ^ ((9 : ℝ) / 10) ≤ S * A := mul_le_mul_of_nonneg_left hdens hS
      _ ≤ (q.divisors.card : ℝ) * K := hmain
      _ ≤ (q : ℝ) ^ ((1 : ℝ) / 5) * K := mul_le_mul_of_nonneg_right htau hK
  have hpos9 : 0 < (q : ℝ) ^ ((9 : ℝ) / 10) := Real.rpow_pos_of_pos hqpos _
  have hsplit : (q : ℝ) ^ ((1 : ℝ) / 5) = (q : ℝ) ^ (-(7 : ℝ) / 10) * (q : ℝ) ^ ((9 : ℝ) / 10) := by
    rw [← Real.rpow_add hqpos]; norm_num
  have h2 : S ≤ (q : ℝ) ^ (-(7 : ℝ) / 10) * K := by
    rw [hsplit] at h1
    have : S * (q : ℝ) ^ ((9 : ℝ) / 10) ≤ ((q : ℝ) ^ (-(7 : ℝ) / 10) * K) * (q : ℝ) ^ ((9 : ℝ) / 10) := by
      linarith [h1]
    exact le_of_mul_le_mul_right this hpos9
  have h3 : (q : ℝ) ^ (-(7 : ℝ) / 10) ≤ (w : ℝ) ^ (-(1 : ℝ) / 2) := by
    calc (q : ℝ) ^ (-(7 : ℝ) / 10) ≤ (w : ℝ) ^ (-(7 : ℝ) / 10) :=
          Real.rpow_le_rpow_of_nonpos hwpos hqw (by norm_num)
      _ ≤ (w : ℝ) ^ (-(1 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  calc S ≤ (q : ℝ) ^ (-(7 : ℝ) / 10) * K := h2
    _ ≤ (w : ℝ) ^ (-(1 : ℝ) / 2) * K := mul_le_mul_of_nonneg_right h3 hK

end Lemma53Split

/-- Proposition 3.2, the proof of paper_weighted_prime_input_of_leaves with
Lemma53Split.lemma53_of_leaves in place of the LEAF lemma53. -/
theorem wired_weighted_prime : Prop32 := by
  apply prop32On_of_split dyad _ prop51_dyad lemma52_dyad Lemma53Split.wired_lemma53 qres_nonempty
  intro N
  refine ⟨Nat.ceil ((N : ℝ) / 3), fun n hn hnm => ?_⟩
  simp only [dyad, mem_filter] at hn
  refine ⟨lt_of_le_of_ne hn.2.1 ?_, hn.2.2⟩
  intro h
  apply hnm
  rw [h, Nat.ceil_natCast]

/-- The half interval Proposition 3.2, the proof of paper_half_interval_input_of_leaves with
Lemma53Split.lemma53_of_leaves in place of the LEAF lemma53. -/
theorem wired_half_interval : Prop32Half := by
  apply prop32On_of_split half _ prop51_half lemma52_half Lemma53Split.wired_lemma53 qres_nonempty
  intro N
  refine ⟨0, fun n hn _ => ?_⟩
  simp only [half, mem_filter] at hn
  refine ⟨hn.2.1, ?_⟩
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith [hn.2.2]


/-- Page 15, the normalization comparison, routed through G1LowerClosed and wired_log_ratio. -/
theorem wired_normalization :
    ∃ c : ℝ, 0 < c ∧ ∀ J w : ℕ, 5 ≤ J → wBig ≤ w →
      ∀ L M : ℕ, 1 ≤ L → L ≤ M → M ≤ 2 * L →
        Real.log L ^ ((3 : ℝ) / 2) *
          ((Nat.totient (WW J w).toNat : ℝ) / WW J w) ^ ((3 : ℝ) / 2) ≤
            c * envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) := by
  obtain ⟨c₀, hc₀, HA⟩ := G1_ge_euler_product_proved
  obtain ⟨CB, hCB, HB⟩ := wired_log_ratio
  refine ⟨(10 : ℝ) ^ ((3 : ℝ) / 2) * CB / c₀, by positivity, ?_⟩
  intro J w hJ hw L M hL hLM hML
  have hwBig1 : (10 : ℝ) ≤ wBig := by
    calc (10 : ℝ) = (10 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (Real.one_le_rpow (by norm_num) (by positivity))
  have hw10 : (10 : ℝ) ≤ w := hwBig1.trans hw
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (hL.trans hLM)
  have hMpos : (0 : ℝ) < M := by linarith
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  set z : ℝ := (M : ℝ) ^ ((1 : ℝ) / 10) with hz
  have hz1 : 1 ≤ z := Real.one_le_rpow hM1 (by norm_num)
  have hlogz : Real.log z = Real.log M / 10 := by
    rw [hz, Real.log_rpow hMpos]; ring
  set r : ℝ := (Nat.totient (WW J w).toNat : ℝ) / WW J w with hr
  have hW0 : (0 : ℤ) < WW J w := by
    unfold WW Wmod
    apply mul_pos (by positivity)
    apply prod_pos
    intro p hp
    exact_mod_cast (Sw_spec w p hp).1.pos
  have hr0 : 0 ≤ r := div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast hW0.le)
  have hrle : r ≤ 1 / Real.log w := totient_ratio_le_inv_log J w hJ hw
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg (by exact_mod_cast hL)
  have hlogLM : Real.log L ≤ Real.log M :=
    Real.log_le_log hLpos (by exact_mod_cast hLM)
  have hbase : Real.log L * r ≤ 10 * (Real.log z / Real.log w) := by
    calc Real.log L * r ≤ Real.log M * (1 / Real.log w) :=
          mul_le_mul hlogLM hrle hr0 (Real.log_nonneg hM1)
      _ = 10 * (Real.log z / Real.log w) := by rw [hlogz]; field_simp
  have hratio0 : 0 ≤ Real.log z / Real.log w :=
    div_nonneg (Real.log_nonneg hz1) hlogw.le
  have hB := HB w hw z hz1
  have hA := HA w hw z hz1
  calc Real.log L ^ ((3 : ℝ) / 2) * r ^ ((3 : ℝ) / 2)
      = (Real.log L * r) ^ ((3 : ℝ) / 2) := (Real.mul_rpow hlogL0 hr0).symm
    _ ≤ (10 * (Real.log z / Real.log w)) ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow (mul_nonneg hlogL0 hr0) hbase (by norm_num)
    _ = (10 : ℝ) ^ ((3 : ℝ) / 2) * (Real.log z / Real.log w) ^ ((3 : ℝ) / 2) :=
        Real.mul_rpow (by norm_num) hratio0
    _ ≤ (10 : ℝ) ^ ((3 : ℝ) / 2) * (CB * ∏ p ∈ (range (⌊z⌋₊ + 1)).filter
          (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z), (1 - (envelopingOmega w p : ℝ) / p)⁻¹) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
    _ = (10 : ℝ) ^ ((3 : ℝ) / 2) * CB / c₀ * (c₀ * ∏ p ∈ (range (⌊z⌋₊ + 1)).filter
          (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z), (1 - (envelopingOmega w p : ℝ) / p)⁻¹) := by
        field_simp
    _ ≤ (10 : ℝ) ^ ((3 : ℝ) / 2) * CB / c₀ * envelopingG w 1 z :=
        mul_le_mul_of_nonneg_left hA (by positivity)


/-- Proposition 4.1 i, pages 13 to 15, the proof of paper_enveloping_domination_input
with wired_normalization in place of paper_enveloping_normalization_input. -/
theorem wired_domination :
    ∃ c : ℝ, 0 < c ∧ ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
      0 ≤ b → b < WW J w → Amenable (WW J w) b →
      ∀ L M : ℕ, 1 ≤ L → L ≤ M → M ≤ 2 * L → ∀ n < M,
        fW (WW J w) b L n ≤ c * restrictionBeta w (WW J w) b M n := by
  obtain ⟨c, hc, H⟩ := wired_normalization
  refine ⟨max c 1, lt_of_lt_of_le hc (le_max_left c 1), ?_⟩
  intro J w hJ hw b hb hbW hamen L M hL hLM hML n hn
  have hraw : fW (WW J w) b L n ≤ c * envelopingBeta w (WW J w) b M n := by
    by_cases hf : fW (WW J w) b L n = 0
    · rw [hf]
      exact mul_nonneg hc.le (envelopingBeta_nonneg w (WW J w) b M n)
    · obtain hgood := fW_ne_zero hf
      have hn0 : n ≠ 0 := by
        intro hz
        simp only [hz, Nat.cast_zero] at hgood
        have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
        linarith [hgood.1]
      have hW0 : 0 < WW J w := lt_of_lt_of_le (by norm_num : (0 : ℤ) < 1) hamen.1
      have hW216 : (216 : ℤ) ≤ WW J w := Int.le_of_dvd hW0 (by simpa using hamen.2.1)
      have hwBig : (3 : ℝ) ≤ wBig := by
        calc (3 : ℝ) ≤ 10 := by norm_num
          _ = (10 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (Real.one_le_rpow (by norm_num) (by positivity))
      have hw3 : 3 ≤ w := by exact_mod_cast (hwBig.trans hw)
      have hsize := cross_scale_sieving_level_lt (by omega : (6 : ℤ) ≤ WW J w) hb hL hLM hML hgood.1
      rw [good_enveloping_plateau (hL.trans hLM) hw3 hn0 hgood.2.2 hsize]
      simpa only [fW, if_pos hgood] using H J w hJ hw L M hL hLM hML
  have hW : 0 < WW J w := lt_of_lt_of_le (by norm_num : (0 : ℤ) < 1) hamen.1
  have hleft : fW (WW J w) b L n ≤ max c 1 * envelopingBeta w (WW J w) b M n :=
    hraw.trans (mul_le_mul_of_nonneg_right (le_max_left c 1) (envelopingBeta_nonneg w (WW J w) b M n))
  have hright : fW (WW J w) b L n ≤ max c 1 * envelopingCap M := by
    apply (fW_le_envelopingCap hW hL hLM n).trans
    have h := mul_le_mul_of_nonneg_right (le_max_right c 1) (envelopingCap_nonneg M)
    simpa only [one_mul] using h
  change fW (WW J w) b L n ≤ max c 1 * min _ _
  rw [mul_min_of_nonneg _ _ (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right c 1))]
  exact le_min hleft hright

/-- Proposition 4.1 iv and v with the growth bound, the proof of paper_enveloping_fourier_input
with the Fourier decay split in place of paper_enveloping_fourier_decay_input. -/
theorem wired_fourier :
    ∃ A D : ℝ → ℝ, (∀ ε : ℝ, 0 < ε → 0 < A ε ∧ 0 < D ε) ∧
      ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
        0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
          EnvelopingFourierBounds w (WW J w) b M A D := by
  obtain ⟨D, hD, H⟩ := wired_fourier_decay
  refine ⟨envelopingGrowthConstant, D, fun ε hε => ⟨envelopingGrowthConstant_pos hε, hD ε hε⟩, ?_⟩
  intro J w hJ hw b hb hbW hamen M hM
  refine ⟨?_, H J w hJ hw b hb hbW hamen M hM⟩
  intro ε hε n hn
  exact (min_le_right _ _).trans (envelopingCap_le_rpow hε hM)

/-- Proposition 4.1 ii, page 13, the proof of paper_enveloping_mean_input with the split inputs. -/
theorem wired_mean :
    ∃ κ : ℝ, 0 < κ ∧ ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
      0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
        (M : ℝ)⁻¹ * ∑ n ∈ range M, restrictionBeta w (WW J w) b M n ≤ κ := by
  obtain ⟨A, D, hAD, hfourier⟩ := wired_fourier
  obtain ⟨C, hC, H⟩ := wired_restriction A D hAD 3 (by norm_num)
  refine ⟨C ^ 2, sq_pos_of_pos hC, ?_⟩
  intro J w hJ hw b hb hbW hamen M hM
  exact mean_le_sq_of_restriction M hM (restrictionBeta w (WW J w) b M)
    (restrictionBeta_nonneg w (WW J w) b M) (by norm_num : (2 : ℝ) < 3) hC.le
    (H J w hJ hw b hb hbW hamen M hM (hfourier J w hJ hw b hb hbW hamen M hM))

/-- Page 9, Proposition 3.3 with its pages 13 to 17 restriction argument, the proof of
paper_cross_scale_restriction_input with the split inputs. -/
theorem wired_cross_scale : Prop33Cross := by
  obtain ⟨c, hc, hdom⟩ := wired_domination
  obtain ⟨κ, hκ, hmean⟩ := wired_mean
  obtain ⟨A, D, hAD, hfourier⟩ := wired_fourier
  apply cross_scale_of_enveloping c κ hc hκ hdom hmean
  intro r hr
  obtain ⟨C, hC, H⟩ := wired_restriction A D hAD r hr
  exact ⟨C, hC, fun J w hJ hw b hb hbW hamen M hM =>
    H J w hJ hw b hb hbW hamen M hM (hfourier J w hJ hw b hb hbW hamen M hM)⟩

/-- Theorem 1.1, the statement of theorem_1_1, CONDITIONAL ON the LEAFs of the burst-20261122
split files only, routed through their deepest splits: leaf_mertens_chi4, paper_level_set_large_delta,
enveloping_v_decay, prop51_dyad, prop51_half, lemma52_dyad, lemma52_half, Lemma53Split.sum_bound_of_coprime and Lemma53Split.leaf_qres_count. -/
theorem theorem_1_1_of_split_leaves : Theorem11 :=
  theorem11_after_prop21 paper_smooth_cutoff_input wired_weighted_prime
    wired_half_interval (prop33_of_cross wired_cross_scale)

end LeanLab.Teravainen2016
