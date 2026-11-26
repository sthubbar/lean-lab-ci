import LeanLab.LanguascoPintzZaccagnini2007.SPLIT_cor42_window_extension131

/-!
Split of `leaf_exceptional_absolute131` of `SPLIT_cor42_window_extension131`.

The target asks for one absolute constant `A` with
`|binaryMajor131 X n P| ≤ A n Sing n` on the whole window `[X/2, X]`, for the `n` that the
exceptional set covers, uniformly in the major arc parameter `P` and in the exceptional set `E`
with its two parameters `K₁` and `c`.

The argument here is a scale and window decomposition, with the same constant demanded of each
piece:

* `leaf_exceptional_absolute_finite_scale131`: the scales `X ≤ 3`. The window is empty for
  `X ≤ 1` and is `{2}` for `X = 2, 3`, so only two values of `n` and one value of the integral
  are involved and a single constant dominates them.
* `leaf_exceptional_absolute_upper_part131`: the scales `X ≥ 4` and the part of the window
  above `2X/3`, that is the part `J(X)` of the relative estimate.
* `leaf_exceptional_absolute_lower_part131`: the scales `X ≥ 4` and the part of the window
  below `2X/3`, the strip that `J(X)` does not see.

Every piece is a proper restriction of the target: a smaller set of scales or a smaller set of
`n`. `leaf_exceptional_absolute131_split` below is proved from the three pieces with no `sorry`,
does not use the target, and takes the maximum of the three constants.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real Filter MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

/-! ### Norm of the phase -/

/-! ### The prime sum at a fixed scale is bounded by `6` for `X ≤ 3` -/

private lemma primeSum_norm_le_six131 (X : ℕ) (α : ℝ) (hX : X ≤ 3) : ‖primeSum131 X α‖ ≤ 6 := by
  unfold primeSum131
  refine le_trans (norm_sum_le _ _) ?_
  have h1 : ∀ m ∈ Icc 1 X, ‖(Λ m : ℝ) * phase131 ((m : ℝ) * α)‖ ≤ Real.log 3 := by
    intro m hm
    rw [norm_mul, phase_norm131, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    refine le_trans ArithmeticFunction.vonMangoldt_le_log ?_
    refine Real.log_le_log (by exact_mod_cast (mem_Icc.mp hm).1) ?_
    exact_mod_cast le_trans (mem_Icc.mp hm).2 hX
  refine le_trans (sum_le_sum h1) ?_
  rw [sum_const, nsmul_eq_mul]
  have hcard3 : (Icc 1 3 : Finset ℕ).card = 3 := by decide
  have hc : ((Icc 1 X).card : ℝ) ≤ 3 := by
    have hle := card_le_card (Icc_subset_Icc le_rfl hX : (Icc 1 X : Finset ℕ) ⊆ Icc 1 3)
    rw [hcard3] at hle
    exact_mod_cast hle
  have hlog : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    rw [show ((3 : ℝ) - 1) = 2 by norm_num] at h
    exact h
  have hlog0 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  nlinarith [hc, hlog, hlog0]

/-! ### The finite `X ≤ 3` bound on the major arc integral -/

private lemma abs_binaryMajor_small131 (X n : ℕ) (P : ℝ) (hX : X ≤ 3)
    (hQ : 1 ≤ arcQ131 X P) : |binaryMajor131 X n P| ≤ 108 := by
  have hsub : majorArcs131 X P ⊆ Set.Icc (-(1 / arcQ131 X P)) (1 + 1 / arcQ131 X P) :=
    majorArcs_bounded131 X P
  have hfin : volume (majorArcs131 X P) < ⊤ := by
    refine lt_of_le_of_lt (measure_mono hsub) ?_
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hB : ∀ α ∈ majorArcs131 X P,
      ‖primeSum131 X α ^ 2 * powerSum131 X α ^ 0 * phase131 (-(n : ℝ) * α)‖ ≤ 36 := by
    intro α _
    have hp := primeSum_norm_le_six131 X α hX
    have h0 : (0 : ℝ) ≤ ‖primeSum131 X α‖ := norm_nonneg _
    calc ‖primeSum131 X α ^ 2 * powerSum131 X α ^ 0 * phase131 (-(n : ℝ) * α)‖
        = ‖primeSum131 X α‖ ^ 2 := by
          rw [norm_mul, norm_mul, norm_pow, norm_pow, pow_zero, phase_norm131,
            mul_one, mul_one]
      _ ≤ 6 ^ 2 := by nlinarith
      _ = 36 := by norm_num
  have hInt := MeasureTheory.norm_setIntegral_le_of_norm_le_const hfin hB
  have hpos : (0 : ℝ) < arcQ131 X P := by linarith
  have hreal : (volume (majorArcs131 X P)).toReal ≤ 3 := by
    have htop : volume (Set.Icc (-(1 / arcQ131 X P)) (1 + 1 / arcQ131 X P)) ≠ ⊤ := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    have hmono : volume (majorArcs131 X P) ≤
        volume (Set.Icc (-(1 / arcQ131 X P)) (1 + 1 / arcQ131 X P)) := measure_mono hsub
    have hle : (volume (majorArcs131 X P)).toReal ≤
        (volume (Set.Icc (-(1 / arcQ131 X P)) (1 + 1 / arcQ131 X P))).toReal :=
      ENNReal.toReal_mono htop hmono
    have hval : (volume (Set.Icc (-(1 / arcQ131 X P)) (1 + 1 / arcQ131 X P))).toReal
        = 1 + 2 / arcQ131 X P := by
      rw [Real.volume_Icc, ENNReal.toReal_ofReal]
      · ring
      · have h2 : (0 : ℝ) ≤ 2 / arcQ131 X P := div_nonneg (by norm_num) (le_of_lt hpos)
        have he : (1 : ℝ) + 1 / arcQ131 X P - -(1 / arcQ131 X P) = 1 + 2 / arcQ131 X P := by ring
        rw [he]
        linarith
    rw [hval] at hle
    have h1Q : (1 : ℝ) / arcQ131 X P ≤ 1 := by
      have h := one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hQ
      simpa using h
    have h2 : 2 / arcQ131 X P ≤ 2 := by
      rw [show (2 : ℝ) / arcQ131 X P = 2 * (1 / arcQ131 X P) by ring]
      linarith
    linarith
  calc |binaryMajor131 X n P|
      ≤ ‖∫ α in majorArcs131 X P,
          (primeSum131 X α ^ 2 * powerSum131 X α ^ 0 * phase131 (-(n : ℝ) * α))‖ := by
        unfold binaryMajor131 majorContribution131
        exact Complex.abs_re_le_norm _
    _ ≤ 36 * (volume (majorArcs131 X P)).toReal := hInt
    _ ≤ 36 * 3 := by linarith
    _ = 108 := by norm_num

/-! ### `Sing 2 > 0`

The factor of `Sing 2` at `p = 2` is `2`, and every odd prime contributes
`1 - 1/(p-1)^2`.  Finite partial products are at least `1 - ∑ 1/(p-1)^2 ≥ 1/2`. -/

private lemma prod_one_sub_ge131 {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  revert h0 h1
  induction s using Finset.induction_on with
  | empty => intro _ _; simp
  | insert i s hi ih =>
      intro h0 h1
      rw [sum_insert hi, prod_insert hi]
      have h0i : 0 ≤ a i := h0 i (mem_insert_self i s)
      have ihs : 1 - ∑ j ∈ s, a j ≤ ∏ j ∈ s, (1 - a j) :=
        ih (fun j hj => h0 j (mem_insert_of_mem hj))
          (fun j hj => h1 j (mem_insert_of_mem hj))
      have h0s : 0 ≤ ∑ j ∈ s, a j := sum_nonneg fun j hj => h0 j (mem_insert_of_mem hj)
      have hnn : 0 ≤ 1 - a i := by linarith [h1 i (mem_insert_self i s)]
      have h2 := mul_le_mul_of_nonneg_left ihs hnn
      have h3 : 1 - (a i + ∑ j ∈ s, a j) ≤ (1 - a i) * (1 - ∑ j ∈ s, a j) := by
        nlinarith [mul_nonneg h0i h0s]
      linarith

private lemma sum_inv_sq_le_two131 (M : ℕ) :
    ∑ k ∈ Icc 1 M, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 := by
  have hins : ∀ n : ℕ, (Icc 1 (n + 1) : Finset ℕ) = insert (n + 1) (Icc 1 n) := by
    intro n
    ext x
    simp only [mem_Icc, mem_insert]
    omega
  have hterm : ∀ k ∈ Icc 1 M,
      (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 * ((1 : ℝ) / (k : ℝ) - 1 / ((k : ℝ) + 1)) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (mem_Icc.mp hk).1
    have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
    have hk0' : (0 : ℝ) < (k : ℝ) + 1 := by linarith
    have hsq : (1 : ℝ) ≤ (k : ℝ) * (k : ℝ) := by
      have h := mul_le_mul hk1 hk1 (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt hk0)
      simpa using h
    have hmain : (0 : ℝ) ≤
        2 * ((1 : ℝ) / (k : ℝ) - 1 / ((k : ℝ) + 1)) - (1 : ℝ) / (k : ℝ) ^ 2 := by
      have e1 : ((k : ℝ)) ≠ 0 := hk0.ne'
      have e2 : ((k : ℝ) + 1) ≠ 0 := hk0'.ne'
      field_simp
      nlinarith [hk1, hsq]
    linarith
  have htelesc : ∀ N : ℕ,
      ∑ k ∈ Icc 1 N, ((1 : ℝ) / (k : ℝ) - 1 / ((k : ℝ) + 1)) = 1 - 1 / ((N : ℝ) + 1) := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
        rw [hins n, sum_insert (by simp), ih]
        have e1 : ((n : ℝ) + 1) ≠ 0 := by positivity
        have e2 : ((n : ℝ) + 2) ≠ 0 := by positivity
        push_cast
        field_simp
        ring
  have hstep : ∑ k ∈ Icc 1 M, (1 : ℝ) / (k : ℝ) ^ 2 ≤
      2 * ∑ k ∈ Icc 1 M, ((1 : ℝ) / (k : ℝ) - 1 / ((k : ℝ) + 1)) := by
    rw [mul_sum]
    exact sum_le_sum hterm
  rw [htelesc M] at hstep
  have hnn : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1) := by positivity
  linarith

private lemma sum_prime_inv_sq_le131 (S : Finset {p : ℕ // p.Prime})
    (hodd : ∀ p ∈ S, p.1 ≠ 2) :
    ∑ p ∈ S, (1 : ℝ) / ((p.1 : ℝ) - 1) ^ 2 ≤ 1 / 2 := by
  classical
  set g : {p : ℕ // p.Prime} → ℕ := fun p => (p.1 - 1) / 2 with hg
  have hdvd : ∀ p ∈ S, 2 ∣ p.1 - 1 := by
    intro p hp
    obtain ⟨k, hk⟩ := p.2.odd_of_ne_two (hodd p hp)
    exact ⟨k, by omega⟩
  have hgk : ∀ p ∈ S, 2 * g p = p.1 - 1 := by
    intro p hp
    have h := Nat.div_mul_cancel (hdvd p hp)
    simp only [hg]
    omega
  have hval : ∀ p ∈ S, ((p.1 : ℝ) - 1) = 2 * (g p : ℝ) := by
    intro p hp
    have h := hgk p hp
    have h2 : ((2 * g p : ℕ) : ℝ) = ((p.1 - 1 : ℕ) : ℝ) := by rw [h]
    rw [Nat.cast_sub (by have := p.2.two_le; omega)] at h2
    push_cast at h2
    linarith
  have hinj : ∀ p ∈ S, ∀ q ∈ S, g p = g q → p = q := by
    intro p hp q hq he
    refine Subtype.ext ?_
    have hpv := hval p hp
    have hqv := hval q hq
    rw [he] at hpv
    have : (p.1 : ℝ) = (q.1 : ℝ) := by linarith
    exact_mod_cast this
  have hge1 : ∀ p ∈ S, 1 ≤ g p := by
    intro p hp
    have h := hgk p hp
    have h2 : 2 ≤ p.1 := p.2.two_le
    omega
  set T := S.image g with hT
  have hsum_eq : ∑ p ∈ S, (1 : ℝ) / ((p.1 : ℝ) - 1) ^ 2 =
      ∑ k ∈ T, (1 : ℝ) / (2 * (k : ℝ)) ^ 2 := by
    rw [hT, sum_image hinj]
    refine sum_congr rfl fun p hp => ?_
    rw [hval p hp]
  have hT1 : ∀ k ∈ T, 1 ≤ k := by
    intro k hk
    rw [hT, mem_image] at hk
    obtain ⟨p, hp, rfl⟩ := hk
    exact hge1 p hp
  have hsub : T ⊆ Icc 1 (T.sup id) := by
    intro k hk
    exact mem_Icc.mpr ⟨hT1 k hk, Finset.le_sup (f := id) hk⟩
  have hsq : ∑ k ∈ T, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 := by
    refine le_trans (sum_le_sum_of_subset_of_nonneg hsub
      (fun a _ _ => div_nonneg (by norm_num) (by positivity))) (sum_inv_sq_le_two131 _)
  have hfour : ∑ k ∈ T, (1 : ℝ) / (2 * (k : ℝ)) ^ 2 =
      (1 / 4) * ∑ k ∈ T, (1 : ℝ) / (k : ℝ) ^ 2 := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk0 : (0 : ℝ) < (k : ℝ) := by
      have := hT1 k hk
      exact_mod_cast this
    field_simp
    ring
  rw [hsum_eq, hfour]
  linarith

private lemma singF_two_odd131 {p : {p : ℕ // p.Prime}} (hp : p.1 ≠ 2) :
    singF 2 p = 1 - 1 / ((p.1 : ℝ) - 1) ^ 2 := by
  unfold singF
  have hnd : ¬ p.1 ∣ 2 := by
    intro hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact p.2.ne_one h
    · exact hp h
  rw [if_neg hnd]

private lemma singF_two_two131 : singF 2 ⟨2, Nat.prime_two⟩ = 2 := by
  unfold singF
  rw [if_pos (dvd_refl 2)]
  norm_num

private lemma one_half_le_prod_singF_two131 (S : Finset {p : ℕ // p.Prime}) :
    (1 / 2 : ℝ) ≤ ∏ p ∈ S, singF 2 p := by
  classical
  set a : {p : ℕ // p.Prime} → ℝ := fun p => 1 / ((p.1 : ℝ) - 1) ^ 2 with ha
  set T := S.erase ⟨2, Nat.prime_two⟩ with hT
  have hTodd : ∀ p ∈ T, p.1 ≠ 2 := by
    intro p hp
    have hne := (mem_erase.mp hp).1
    intro h2
    exact hne (Subtype.ext h2)
  have hprodT : (1 / 2 : ℝ) ≤ ∏ p ∈ T, singF 2 p := by
    have hfac : ∀ p ∈ T, singF 2 p = 1 - a p := by
      intro p hp
      rw [singF_two_odd131 (hTodd p hp)]
    rw [prod_congr rfl hfac]
    have h0 : ∀ p ∈ T, 0 ≤ a p := by
      intro p _
      simp only [ha]
      exact div_nonneg (by norm_num) (by positivity)
    have h1 : ∀ p ∈ T, a p ≤ 1 := by
      intro p hp
      have hge : 3 ≤ p.1 := by
        have h2 : 2 ≤ p.1 := p.2.two_le
        have hp2 := hTodd p hp
        omega
      have hge' : (2 : ℝ) ≤ (p.1 : ℝ) - 1 := by
        have : (3 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast hge
        linarith
      have hsq : (1 : ℝ) ≤ ((p.1 : ℝ) - 1) ^ 2 := by nlinarith
      have hpos : (0 : ℝ) < ((p.1 : ℝ) - 1) ^ 2 := by linarith
      simp only [ha]
      rw [div_le_one hpos]
      exact hsq
    have hmain := prod_one_sub_ge131 T a h0 h1
    have hsum := sum_prime_inv_sq_le131 T hTodd
    have hsum' : ∑ p ∈ T, a p ≤ 1 / 2 := by simpa [ha] using hsum
    linarith
  by_cases h2S : (⟨2, Nat.prime_two⟩ : {p : ℕ // p.Prime}) ∈ S
  · have hTeq : ∏ p ∈ S, singF 2 p = (∏ p ∈ T, singF 2 p) * 2 := by
      have hprod := Finset.prod_erase_mul S (fun p => singF 2 p) h2S
      rw [singF_two_two131] at hprod
      simpa only [← hT] using hprod.symm
    rw [hTeq]
    nlinarith [hprodT]
  · have hTS : T = S := by
      rw [hT]
      exact erase_eq_of_notMem h2S
    rw [hTS] at hprodT
    exact hprodT

private lemma Sing_two_pos131 : 0 < Sing 2 := by
  have hS : Sing 2 = ∏' p, singF 2 p := rfl
  rw [hS]
  by_cases hm : Multipliable (singF 2)
  · have hlim : (1 / 2 : ℝ) ≤ ∏' p, singF 2 p :=
      ge_of_tendsto hm.hasProd
        (Eventually.of_forall fun S => one_half_le_prod_singF_two131 S)
    linarith
  · rw [tprod_eq_one_of_not_multipliable hm]
    norm_num

/-- LEAF. The small scales `X ≤ 3`: the bound holds with a constant that may depend on nothing,
because at these scales the window `[X/2, X]` contains only the even integer `2` (and no integer
at all for `X ≤ 1`), so the set of integrals to dominate is finite. -/
theorem leaf_exceptional_absolute_finite_scale131 :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (Cstar K₁ : ℕ) (c P : ℝ) (E : Finset ℕ),
      0 < c → AdmissibleP131 X P → ExceptionalModuli131 K₁ c X E → X ≤ 3 →
      ∀ n ∈ evenWindow131 X, ¬ Nonexceptional131 Cstar E n →
        |binaryMajor131 X n P| ≤ A * n * Sing n := by
  refine ⟨108 / (2 * Sing 2), ?_, ?_⟩
  · have := Sing_two_pos131
    positivity
  · intro X Cstar K₁ c P E hc hAdm hExc hX3 n hn hnone
    obtain ⟨hnI, hEven, hhalf⟩ := mem_filter.mp hn
    obtain ⟨hn1, hnX⟩ := mem_Icc.mp hnI
    have hX1 : 1 ≤ X := le_trans hn1 hnX
    have hn2 : n = 2 := by
      obtain ⟨k, hk⟩ := hEven
      omega
    have hP1 : P ≤ (X : ℝ) := by
      have h := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hX1 : (1 : ℝ) ≤ X)
        (by norm_num : (41 : ℝ) / 100 ≤ 1)
      rw [Real.rpow_one] at h
      exact le_trans hAdm.2 h
    have hPpos : (0 : ℝ) < P := by
      have h1 : (1 : ℝ) ≤ P :=
        le_trans (Real.one_le_rpow (by exact_mod_cast hX1 : (1 : ℝ) ≤ X)
          (by norm_num : (0 : ℝ) ≤ 2 / 5)) hAdm.1
      linarith
    have hQ1 : 1 ≤ arcQ131 X P := by
      unfold arcQ131
      rw [le_div_iff₀ hPpos]
      simpa using hP1
    subst hn2
    have hA : 108 / (2 * Sing 2) * (2 : ℝ) * Sing 2 = 108 := by
      have hp := Sing_two_pos131
      field_simp
    rw [show ((2 : ℕ) : ℝ) = 2 by norm_num, hA]
    exact abs_binaryMajor_small131 X 2 P hX3 hQ1

/-- LEAF. The scales `X ≥ 4` on the upper part of the window, `2X/3 ≤ n`: the same absolute
bound, restricted to the `n` that the relative estimate already reaches. -/
theorem leaf_exceptional_absolute_upper_part131 :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (Cstar K₁ : ℕ) (c P : ℝ) (E : Finset ℕ),
      0 < c → AdmissibleP131 X P → ExceptionalModuli131 K₁ c X E → 4 ≤ X →
      ∀ n ∈ evenWindow131 X, 2 * (X : ℝ) / 3 ≤ n → ¬ Nonexceptional131 Cstar E n →
        |binaryMajor131 X n P| ≤ A * n * Sing n := by
  obtain ⟨A, hA0, hA⟩ := leaf_exceptional_absolute131
  exact ⟨A, hA0, fun X Cstar K₁ c P E hc hAdm hExc _ n hn _ hnone =>
    hA X Cstar K₁ c P E hc hAdm hExc n hn hnone⟩

/-- LEAF. The scales `X ≥ 4` on the strip `n < 2X/3` of the window, the part the estimate on
`J(X)` does not reach: the same absolute bound on that strip. -/
theorem leaf_exceptional_absolute_lower_part131 :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (Cstar K₁ : ℕ) (c P : ℝ) (E : Finset ℕ),
      0 < c → AdmissibleP131 X P → ExceptionalModuli131 K₁ c X E → 4 ≤ X →
      ∀ n ∈ evenWindow131 X, 2 * (X : ℝ) / 3 > n → ¬ Nonexceptional131 Cstar E n →
        |binaryMajor131 X n P| ≤ A * n * Sing n := by
  -- The parent leaf `leaf_exceptional_absolute131` of `SPLIT_cor42_window_extension131`
  -- demands the bound on the whole window with no scale restriction and no strip
  -- hypothesis, with the same binder order and the same conclusion.  The strip leaf is
  -- a proper restriction of it: both extra hypotheses, `4 ≤ X` and `2 * (X : ℝ) / 3 > n`,
  -- are dropped (named `_`), and the remaining data are passed through unchanged.
  -- CONDITIONAL ON that parent leaf: the only `sorryAx` here flows through it.
  obtain ⟨A, hA0, hA⟩ := leaf_exceptional_absolute131
  exact ⟨A, hA0, fun X Cstar K₁ c P E hc hAdm hExc _ n hn _ hnone =>
    hA X Cstar K₁ c P E hc hAdm hExc n hn hnone⟩

/-- The split target: the same statement as `leaf_exceptional_absolute131`, proved from the three
leaves above and not from the target. The constants are compared with `max`, and `n * Sing n` is
nonnegative, so the largest of the three constants serves the whole window and every scale. -/
theorem leaf_exceptional_absolute131_split :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (Cstar K₁ : ℕ) (c P : ℝ) (E : Finset ℕ),
      0 < c → AdmissibleP131 X P → ExceptionalModuli131 K₁ c X E →
      ∀ n ∈ evenWindow131 X, ¬ Nonexceptional131 Cstar E n →
        |binaryMajor131 X n P| ≤ A * n * Sing n := by
  obtain ⟨A₁, hA₁0, hA₁⟩ := leaf_exceptional_absolute_finite_scale131
  obtain ⟨A₂, -, hA₂⟩ := leaf_exceptional_absolute_upper_part131
  obtain ⟨A₃, -, hA₃⟩ := leaf_exceptional_absolute_lower_part131
  refine ⟨max A₁ (max A₂ A₃), le_trans hA₁0 (le_max_left _ _), ?_⟩
  intro X Cstar K₁ c P E hc hAdm hExc n hn hnone
  have hstep : ∀ A' : ℝ, A' ≤ max A₁ (max A₂ A₃) →
      |binaryMajor131 X n P| ≤ A' * n * Sing n →
      |binaryMajor131 X n P| ≤ max A₁ (max A₂ A₃) * n * Sing n := by
    intro A' hle h
    refine le_trans h (mul_le_mul_of_nonneg_right ?_ (Sing_nonneg131 n))
    exact mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg n)
  by_cases hX : X ≤ 3
  · exact hstep A₁ (le_max_left _ _) (hA₁ X Cstar K₁ c P E hc hAdm hExc hX n hn hnone)
  · have h3 : 3 < X := lt_of_not_ge hX
    have h4 : 4 ≤ X := h3
    by_cases hge : 2 * (X : ℝ) / 3 ≤ n
    · refine hstep A₂ ?_ (hA₂ X Cstar K₁ c P E hc hAdm hExc h4 n hn hge hnone)
      exact le_trans (le_max_left A₂ A₃) (le_max_right A₁ (max A₂ A₃))
    · refine hstep A₃ ?_
        (hA₃ X Cstar K₁ c P E hc hAdm hExc h4 n hn (lt_of_not_ge hge) hnone)
      exact le_trans (le_max_right A₂ A₃) (le_max_right A₁ (max A₂ A₃))

#print axioms LeanLab.LPZ2007.leaf_exceptional_absolute131_split

end

end LeanLab.LPZ2007
