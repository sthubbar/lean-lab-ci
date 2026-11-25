/-
Feed split of `prop14_error_bound`, burst-20261122 session S107.
Zinoviev 1997, J. Number Theory 65, Proposition 1.4, proof on pp. 340 to 341, papers/P0097.
Leaves: the Abel step (1.10) with the prime powers, the progression bound for psi of p. 341
in the modulus range of Lemma 1.3 and, separately, in the range the paper does not treat,
the remainder estimate for R of p. 341, Schoenfeld's bound of reference [4] for q = 1, 2,
and the elementary count for q = 2. The glue `prop14_error_bound_of_leaves` is sorry free.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.State1546

namespace LeanLab.Zinoviev1997.State1546
open MeasureTheory

/-- `ψ(x; q, l) = Σ_{n ≤ x, n ≡ l mod q} Λ(n)`, Zinoviev 1997, p. 340, the display after (1.10). -/
noncomputable def psiMod (x : ℝ) (q l : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Iic ⌊x⌋₊).filter (fun n => n % q = l % q), ArithmeticFunction.vonMangoldt n

section S145_prop14_abel
open MeasureTheory Finset Real

/-- The sum `Σ_{n ≤ x, n ≡ l mod q} Λ(n)/ln n`, left side of display (1.10). -/
noncomputable def s145_S (x : ℝ) (q l : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Iic ⌊x⌋₊).filter (fun n => n % q = l % q),
    ArithmeticFunction.vonMangoldt n / Real.log n

theorem s145_abel_identity {q l : ℕ} {x : ℝ} (hx : 2 ≤ x) :
    s145_S x q l = psiMod x q l / Real.log x +
      ∫ u in (2 : ℝ)..x, psiMod u q l / (u * Real.log u ^ 2) := by
  let a : ℕ → ℝ := fun n => if n % q = l % q then ArithmeticFunction.vonMangoldt n else 0
  have hS : s145_S x q l = ∑ n ∈ Icc 0 ⌊x⌋₊, (Real.log n)⁻¹ * a n := by
    unfold s145_S
    rw [sum_filter, Finset.Iic_eq_Icc, Nat.bot_eq_zero]
    refine sum_congr rfl fun n _ => ?_
    simp only [a]
    split_ifs <;> simp [div_eq_mul_inv, mul_comm]
  have hpsi : ∀ t : ℝ, psiMod t q l = ∑ k ∈ Icc 0 ⌊t⌋₊, a k := by
    intro t
    unfold psiMod
    rw [sum_filter, Finset.Iic_eq_Icc, Nat.bot_eq_zero]
  rw [hS, sum_mul_eq_sub_integral_mul₁ a (f := fun n ↦ (Real.log n)⁻¹) (by simp [a])
    (by simp [a]), ← intervalIntegral.integral_of_le hx]
  · have int_deriv :
        ∫ u in (2:ℝ)..x, deriv (fun x ↦ (Real.log x)⁻¹) u * ∑ k ∈ Icc 0 ⌊u⌋₊, a k =
        - ∫ u in (2:ℝ)..x, psiMod u q l / (u * Real.log u ^ 2) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun u _ ↦ ?_
      simp only [hpsi]
      rw [deriv_inv_log_apply]
      ring
    rw [int_deriv, hpsi x]
    ring
  · intro z ⟨_, _⟩
    have : z ≠ 0 := by linarith
    have : Real.log z ≠ 0 := by apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith
    fun_prop
  · refine ContinuousOn.integrableOn_Icc fun z ⟨_, _⟩ ↦ ContinuousWithinAt.congr ?_
      (fun _ _ ↦ deriv_inv_log_apply) deriv_inv_log_apply
    have : z ≠ 0 := by linarith
    have : Real.log z ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 <| Real.log_ne_zero_of_pos_of_ne_one ?_ ?_ <;> linarith
    exact ContinuousAt.continuousWithinAt <| by fun_prop

/-- The excess term `Λ(n)/ln n - 1_{n prime}`. -/
noncomputable def s145_g (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.log n - if n.Prime then 1 else 0

theorem s145_g_bounds (n : ℕ) :
    0 ≤ s145_g n ∧ s145_g n ≤ if IsPrimePow n ∧ ¬ n.Prime then (1 / 2 : ℝ) else 0 := by
  unfold s145_g
  by_cases hp : n.Prime
  · have hl : Real.log n ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one
      (by exact_mod_cast hp.pos) (by exact_mod_cast hp.ne_one)
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp, div_self hl]
    simp [hp]
  · by_cases hpp : IsPrimePow n
    · obtain ⟨p, k, hpr, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
      have hk2 : 2 ≤ k := by
        rcases Nat.lt_or_ge k 2 with h | h
        · interval_cases k; simp at hp; exact absurd hpr hp
        · exact h
      have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpr.one_lt)
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
        ArithmeticFunction.vonMangoldt_apply_prime hpr]
      push_cast
      rw [Real.log_pow]
      simp only [hp, ite_false, hpp, not_false_eq_true, and_self, ite_true, sub_zero]
      have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      rw [div_mul_cancel_right₀ hlp.ne']
      constructor
      · positivity
      · rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
    · rw [(ArithmeticFunction.vonMangoldt_eq_zero_iff).mpr hpp]
      simp [hp, hpp]

/-- The perfect prime powers up to `N` that are not primes. -/
theorem s145_card_A (N : ℕ) (hN : 10 ^ 9 ≤ N) :
    (((Finset.Iic N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)).card : ℝ) ≤
      (Nat.sqrt N + 1 : ℝ) + (Nat.sqrt N / 31 + 1 : ℝ) * (Nat.log 2 N + 1) := by
  classical
  let T : Finset (ℕ × ℕ) := (Finset.Iic (Nat.sqrt N) ×ˢ {2}) ∪
    (Finset.Iic (Nat.sqrt N / 31) ×ˢ Finset.Iic (Nat.log 2 N))
  have hsub : (Finset.Iic N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime) ⊆
      T.image (fun pk => pk.1 ^ pk.2) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Iic] at hn
    obtain ⟨hnN, hpp, hnp⟩ := hn
    obtain ⟨p, k, hpr, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with h | h
      · interval_cases k; simp at hnp; exact absurd hpr hnp
      · exact h
    have hp2 : 2 ≤ p := hpr.two_le
    rw [Finset.mem_image]
    refine ⟨(p, k), ?_, rfl⟩
    rcases Nat.eq_or_lt_of_le hk2 with h | h
    · subst h
      simp only [T, Finset.mem_union, Finset.mem_product, Finset.mem_Iic, Finset.mem_singleton]
      left; exact ⟨Nat.le_sqrt'.mpr hnN, trivial⟩
    · simp only [T, Finset.mem_union, Finset.mem_product, Finset.mem_Iic, Finset.mem_singleton]
      right
      have h3 : p ^ 3 ≤ N := le_trans (Nat.pow_le_pow_right (by omega) h) hnN
      refine ⟨?_, ?_⟩
      · rw [Nat.le_div_iff_mul_le (by norm_num), Nat.le_sqrt']
        rcases Nat.lt_or_ge p 961 with hp | hp
        · have : p ^ 2 ≤ 960 ^ 2 := Nat.pow_le_pow_left (by omega) 2
          nlinarith
        · have : p ^ 3 = p * p ^ 2 := by ring
          nlinarith
      · exact Nat.le_log_of_pow_le (by norm_num)
          (le_trans (Nat.pow_le_pow_left hp2 k) hnN)
  have h1 := (Finset.card_le_card hsub).trans Finset.card_image_le
  have h2 : T.card ≤ (Nat.sqrt N + 1) + (Nat.sqrt N / 31 + 1) * (Nat.log 2 N + 1) := by
    refine (Finset.card_union_le _ _).trans ?_
    simp [Finset.card_product]
  have h3 := h1.trans h2
  have : ((Nat.sqrt N / 31 : ℕ) : ℝ) ≤ (Nat.sqrt N : ℝ) / 31 := Nat.cast_div_le
  calc (((Finset.Iic N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)).card : ℝ)
      ≤ ((Nat.sqrt N + 1 + (Nat.sqrt N / 31 + 1) * (Nat.log 2 N + 1) : ℕ) : ℝ) := by
        exact_mod_cast h3
    _ ≤ _ := by
        push_cast
        gcongr

theorem s145_excess {q l : ℕ} {x : ℝ} (hx : 10 ^ 9 ≤ x) :
    |s145_S x q l - (piMod x q l : ℝ)| ≤ 0.1 * Real.sqrt x * Real.log x := by
  classical
  set N := ⌊x⌋₊ with hNdef
  set F := (Finset.Iic N).filter (fun n => n % q = l % q) with hF
  have hx0 : 0 ≤ x := by linarith
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hN9 : 10 ^ 9 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hpi : (piMod x q l : ℝ) = ∑ n ∈ F, (if n.Prime then (1 : ℝ) else 0) := by
    have : piMod x q l = (F.filter Nat.Prime).card := by
      unfold piMod
      rw [hF, Finset.filter_filter]
      congr 1
      exact Finset.filter_congr (fun n _ => by rw [and_comm])
    rw [this, Finset.card_filter]
    push_cast
    rfl
  have hdiff : s145_S x q l - (piMod x q l : ℝ) = ∑ n ∈ F, s145_g n := by
    rw [hpi]
    unfold s145_S s145_g
    rw [← Finset.sum_sub_distrib]
  set A := (Finset.Iic N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime) with hA
  have h0 : 0 ≤ ∑ n ∈ F, s145_g n := Finset.sum_nonneg fun n _ => (s145_g_bounds n).1
  have hle : ∑ n ∈ F, s145_g n ≤ (1 / 2 : ℝ) * A.card := by
    calc ∑ n ∈ F, s145_g n ≤ ∑ n ∈ Finset.Iic N, s145_g n :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun n _ _ => (s145_g_bounds n).1)
      _ ≤ ∑ n ∈ Finset.Iic N, (if IsPrimePow n ∧ ¬ n.Prime then (1 / 2 : ℝ) else 0) :=
          Finset.sum_le_sum fun n _ => (s145_g_bounds n).2
      _ = (1 / 2 : ℝ) * A.card := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hcard := s145_card_A N hN9
  -- numerics
  set r := Real.sqrt x
  set ℓ := Real.log x
  have hs : (Nat.sqrt N : ℝ) ≤ r :=
    Real.nat_sqrt_le_real_sqrt.trans (Real.sqrt_le_sqrt hNx)
  have hr : (1000 : ℝ) ≤ r := by
    rw [show (1000 : ℝ) = Real.sqrt (1000 ^ 2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by linarith)
  have hℓ : 20 ≤ ℓ := by
    have h29 : ((2 : ℝ) ^ 29) ≤ x := by norm_num at hx ⊢; linarith
    have := Real.log_le_log (by positivity) h29
    rw [Real.log_pow] at this
    push_cast at this
    linarith [Real.log_two_gt_d9]
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hL : (Nat.log 2 N : ℝ) ≤ 1.45 * ℓ := by
    have hp : ((2 : ℝ) ^ (Nat.log 2 N)) ≤ x := by
      have := Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
      calc ((2 : ℝ) ^ (Nat.log 2 N)) = ((2 ^ Nat.log 2 N : ℕ) : ℝ) := by push_cast; ring
        _ ≤ N := by exact_mod_cast this
        _ ≤ x := hNx
    have := Real.log_le_log (by positivity) hp
    rw [Real.log_pow] at this
    have h0' : (0 : ℝ) ≤ Nat.log 2 N := by positivity
    nlinarith
  have hs0 : (0 : ℝ) ≤ Nat.sqrt N := by positivity
  have hL0 : (0 : ℝ) ≤ Nat.log 2 N := by positivity
  have hprod : ((Nat.sqrt N : ℝ) / 31 + 1) * (Nat.log 2 N + 1) ≤ (r / 31 + 1) * (1.45 * ℓ + 1) := by
    apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have hfin : (1 / 2 : ℝ) * A.card ≤ 0.1 * r * ℓ := by
    have hrl : 20 * r ≤ r * ℓ := by nlinarith
    have hrl2 : 1000 * ℓ ≤ r * ℓ := by nlinarith
    nlinarith
  rw [hdiff, abs_of_nonneg h0]
  exact hle.trans hfin

theorem prop14_abel_s145 {q l : ℕ} (hq : 1 ≤ q) {x : ℝ} (hx : 10 ^ 9 ≤ x) :
    |(piMod x q l : ℝ) - (psiMod x q l / Real.log x +
        ∫ u in (2 : ℝ)..x, psiMod u q l / (u * Real.log u ^ 2))| ≤
      0.1 * Real.sqrt x * Real.log x := by
  rw [← s145_abel_identity (by linarith), abs_sub_comm]
  exact s145_excess hx

end S145_prop14_abel

/-- LEAF: display (1.10), p. 340, Abel's transformation together with the prime power count.
Class MEDIUM. `Σ_{n ≤ x, n ≡ l} Λ(n)/ln n = ψ(x;q,l)/ln x + ∫₂ˣ ψ(u;q,l)/(u ln² u) du`
exactly, and it exceeds `π(x;q,l)` by the prime powers `p^k`, `k ≥ 2`, each weighted `1/k`.
The paper bounds that excess by `√x ln x / φ(q)`; here the weaker constant `0.1 √x ln x`
is used, which already follows from `#{p^k ≤ x, k ≥ 2} ≤ √x + x^{1/3} log₂ x`. -/
theorem prop14_abel {q l : ℕ} (hq : 1 ≤ q) {x : ℝ} (hx : 10 ^ 9 ≤ x) :
    |(piMod x q l : ℝ) - (psiMod x q l / Real.log x +
        ∫ u in (2 : ℝ)..x, psiMod u q l / (u * Real.log u ^ 2))| ≤
      0.1 * Real.sqrt x * Real.log x := by
  exact prop14_abel_s145 hq hx

/-- LEAF: the display `ψ(x;q,l) = x/φ(q) + c √x ln² x`, `|c| ≤ 0.85`, p. 341, in the modulus
range of Lemma 1.3. Class HARD. The paper's route: orthogonality of characters, p. 340, the
reduction to primitive characters with error `Σ_{(n,q)>1} Λ(n) ln² x`, Lemma 1.3 for the
non principal characters and Schoenfeld [4] for `ψ(x)`. -/
theorem psiMod_grh_low (hG : LeanLab.DERZ1997.GRH) {q l : ℕ} (hq : 3 ≤ q)
    (hl : Nat.Coprime l q) {u : ℝ} (hu : 10 ^ 9 ≤ u) (hqu : (q : ℝ) ≤ u ^ (0.37 : ℝ)) :
    |psiMod u q l - u / (Nat.totient q : ℝ)| ≤ 0.85 * Real.sqrt u * Real.log u ^ 2 := by
  sorry

section S145_psiMod_orthogonality
open MeasureTheory

theorem s145_no_prim_two (ψ : DirichletCharacter ℂ 2) : ¬ ψ.IsPrimitive := by
  intro h
  have h1 : ψ = 1 := by
    apply MulChar.ext
    intro a
    have : a = 1 := by revert a; decide
    subst this; simp
  rw [DirichletCharacter.isPrimitive_def] at h
  have := (DirichletCharacter.eq_one_iff_conductor_eq_one (χ := ψ)).1 h1
  omega

theorem s145_sum_pdvd {p N : ℕ} (hp : p.Prime) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Iic N, (if p ∣ n then ArithmeticFunction.vonMangoldt n else 0) ≤
      Real.log N := by
  set m := Nat.log p N
  have hpm : p ^ m ≤ N := Nat.pow_log_le_self p (by omega)
  have hpm0 : p ^ m ≠ 0 := pow_ne_zero _ hp.ne_zero
  calc ∑ n ∈ Finset.Iic N, (if p ∣ n then ArithmeticFunction.vonMangoldt n else 0)
      ≤ ∑ n ∈ Finset.Iic N, (if n ∣ p ^ m then ArithmeticFunction.vonMangoldt n else 0) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [Finset.mem_Iic] at hn
        by_cases hpn : p ∣ n
        · rw [if_pos hpn]
          by_cases hL : ArithmeticFunction.vonMangoldt n = 0
          · rw [hL]; split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]
          · have hpp : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hL
            obtain ⟨r, k, hr, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
            have hpr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hpn)
            subst hpr
            have hkm : k ≤ m := Nat.le_log_of_pow_le hp.one_lt hn
            rw [if_pos (pow_dvd_pow p hkm)]
        · rw [if_neg hpn]; split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]
    _ = ∑ n ∈ (Finset.Iic N).filter (· ∣ p ^ m), ArithmeticFunction.vonMangoldt n := by
        rw [Finset.sum_filter]
    _ ≤ ∑ n ∈ (p ^ m).divisors, ArithmeticFunction.vonMangoldt n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          rw [Finset.mem_filter] at hn
          exact Nat.mem_divisors.mpr ⟨hn.2, hpm0⟩
        · intro _ _ _; exact ArithmeticFunction.vonMangoldt_nonneg
    _ = Real.log (p ^ m : ℕ) := ArithmeticFunction.vonMangoldt_sum
    _ ≤ Real.log N := by
        apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hpm0)
        exact_mod_cast hpm

theorem s145_E_le {q N : ℕ} (hq : 1 ≤ q) (hN : 1 ≤ N) :
    ∑ n ∈ (Finset.Iic N).filter (fun n => ¬ n.Coprime q), ArithmeticFunction.vonMangoldt n ≤
      (q.primeFactors.card : ℝ) * Real.log N := by
  calc ∑ n ∈ (Finset.Iic N).filter (fun n => ¬ n.Coprime q), ArithmeticFunction.vonMangoldt n
      ≤ ∑ n ∈ (Finset.Iic N).filter (fun n => ¬ n.Coprime q),
          ∑ p ∈ q.primeFactors, (if p ∣ n then ArithmeticFunction.vonMangoldt n else 0) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [Finset.mem_filter] at hn
        obtain ⟨p, hp, hpn, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn.2
        have hmem : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpq, by omega⟩
        calc ArithmeticFunction.vonMangoldt n
            = (if p ∣ n then ArithmeticFunction.vonMangoldt n else 0) := by rw [if_pos hpn]
          _ ≤ _ := Finset.single_le_sum (f := fun p => if p ∣ n then
                ArithmeticFunction.vonMangoldt n else 0)
                (fun p _ => by split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]) hmem
    _ = ∑ p ∈ q.primeFactors, ∑ n ∈ (Finset.Iic N).filter (fun n => ¬ n.Coprime q),
          (if p ∣ n then ArithmeticFunction.vonMangoldt n else 0) := Finset.sum_comm
    _ ≤ ∑ p ∈ q.primeFactors, Real.log N := by
        apply Finset.sum_le_sum
        intro p hp
        refine le_trans ?_ (s145_sum_pdvd (Nat.prime_of_mem_primeFactors hp) hN)
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro _ _ _; split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

theorem s145_omega_le {q : ℕ} (hq : 1 ≤ q) :
    (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log q := by
  have h1 : 2 ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have h2 : ∏ p ∈ q.primeFactors, p ≤ q := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)
  have h3 : ((2 : ℝ) ^ q.primeFactors.card) ≤ q := by exact_mod_cast h1.trans h2
  have := Real.log_le_log (by positivity) h3
  rwa [Real.log_pow] at this


theorem s145_diff {q N : ℕ} (f g : ℕ → ℂ) (hfg : ∀ n, n.Coprime q → f n = g n)
    (hg0 : ∀ n, ¬ n.Coprime q → g n = 0) (hf1 : ∀ n, ‖f n‖ ≤ 1) :
    ‖∑ n ∈ Finset.Iic N, f n * (ArithmeticFunction.vonMangoldt n : ℂ) -
      ∑ n ∈ Finset.Iic N, g n * (ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤
      ∑ n ∈ (Finset.Iic N).filter (fun n => ¬ n.Coprime q), ArithmeticFunction.vonMangoldt n := by
  rw [← Finset.sum_sub_distrib, Finset.sum_filter]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [← sub_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  by_cases h : n.Coprime q
  · rw [hfg n h, sub_self, norm_zero, zero_mul]; simp [h]
  · rw [hg0 n h, sub_zero]; simp only [h, not_false_eq_true, ite_true]
    exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (hf1 n)

theorem s145_orth {q l : ℕ} [NeZero q] (hl : Nat.Coprime l q) (u : ℝ) :
    ∑ χ : DirichletCharacter ℂ q, χ ((l : ZMod q)⁻¹) * psiChi χ u =
      (Nat.totient q : ℂ) * (psiMod u q l : ℂ) := by
  have ha : IsUnit (l : ZMod q) := (ZMod.isUnit_iff_coprime l q).mpr hl
  simp only [psiChi, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← Finset.sum_mul, DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) ha]
  rw [psiMod, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : n % q = l % q
  · have h' : (l : ZMod q) = n := (ZMod.natCast_eq_natCast_iff' l n q).mpr h.symm
    rw [if_pos h', if_pos h]
  · have h' : ¬ (l : ZMod q) = n := fun e => h ((ZMod.natCast_eq_natCast_iff' l n q).mp e).symm
    rw [if_neg h', if_neg h]; simp

theorem s145_psiMod_one (u : ℝ) :
    (psiMod u 1 0 : ℂ) = ∑ n ∈ Finset.Iic ⌊u⌋₊, (1 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) := by
  rw [psiMod, Finset.filter_true_of_mem (fun n _ => Nat.mod_one n), Complex.ofReal_sum]
  simp


theorem s145_no_prim_two' (k : ℕ) (ψ : DirichletCharacter ℂ k) (hk : k = 2) : ¬ ψ.IsPrimitive := by
  subst hk; exact s145_no_prim_two ψ

theorem s145_nonprincipal {q : ℕ} [NeZero q] {u : ℝ}
    (h13 : ∀ (k : ℕ) [NeZero k] (χ : DirichletCharacter ℂ k), χ.IsPrimitive → 3 ≤ k →
      k ∣ q → ‖psiChi χ u‖ ≤ 0.83 * Real.sqrt u * Real.log u ^ 2)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ‖psiChi χ u‖ ≤ 0.83 * Real.sqrt u * Real.log u ^ 2 +
      ∑ n ∈ (Finset.Iic ⌊u⌋₊).filter (fun n => ¬ n.Coprime q), ArithmeticFunction.vonMangoldt n := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hk3 : 3 ≤ χ.conductor := by
    have h0 := χ.conductor_ne_zero
    have h1 : χ.conductor ≠ 1 := fun h => hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)
    have h2 : χ.conductor ≠ 2 := fun h =>
      s145_no_prim_two' _ χ.primitiveCharacter h χ.primitiveCharacter_isPrimitive
    omega
  have hb := h13 χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hk3
    χ.conductor_dvd_level
  have hd := s145_diff (q := q) (N := ⌊u⌋₊) (fun n => χ.primitiveCharacter (n : ZMod χ.conductor))
    (fun n => χ (n : ZMod q)) ?_ ?_ ?_
  · have he : psiChi χ u = psiChi χ.primitiveCharacter u -
        (psiChi χ.primitiveCharacter u - psiChi χ u) := by ring
    rw [he]
    refine (norm_sub_le _ _).trans ?_
    exact add_le_add hb hd
  · intro n hn
    have hc : IsCoprime (n : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr hn
    have := χ.primitiveCharacter_apply_of_isCoprime hc
    simpa using this
  · intro n hn
    exact MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])
  · intro n; exact DirichletCharacter.norm_le_one _ _

theorem s145_E_bound {q : ℕ} (hq : 3 ≤ q) {u : ℝ} (hu : 10 ^ 9 ≤ u)
    (hqu : (q : ℝ) ≤ u ^ (0.37 : ℝ)) :
    ∑ n ∈ (Finset.Iic ⌊u⌋₊).filter (fun n => ¬ n.Coprime q), ArithmeticFunction.vonMangoldt n ≤
      2 * Real.log u ^ 2 := by
  have hu0 : 0 < u := by linarith
  have hN : 1 ≤ ⌊u⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hlogN : Real.log (⌊u⌋₊ : ℕ) ≤ Real.log u :=
    Real.log_le_log (by exact_mod_cast hN) (Nat.floor_le hu0.le)
  have hL0 : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have hω := s145_omega_le (q := q) (by omega)
  have hlq : Real.log q ≤ 0.37 * Real.log u := by
    have := Real.log_le_log (by exact_mod_cast (by omega : 0 < q)) hqu
    rwa [Real.log_rpow hu0] at this
  have hl2 := Real.log_two_gt_d9
  have hE := s145_E_le (q := q) (N := ⌊u⌋₊) (by omega) hN
  set ω : ℝ := (q.primeFactors.card : ℝ)
  have hω0 : 0 ≤ ω := by positivity
  have hω2 : ω ≤ 2 * Real.log u := by nlinarith
  calc _ ≤ ω * Real.log (⌊u⌋₊ : ℕ) := hE
    _ ≤ ω * Real.log u := mul_le_mul_of_nonneg_left hlogN hω0
    _ ≤ (2 * Real.log u) * Real.log u := mul_le_mul_of_nonneg_right hω2 hL0
    _ = 2 * Real.log u ^ 2 := by ring


theorem psiMod_orthogonality_s145 {q l : ℕ} (hq : 3 ≤ q) (hl : Nat.Coprime l q) {u : ℝ}
    (hu : 10 ^ 9 ≤ u) (hqu : (q : ℝ) ≤ u ^ (0.37 : ℝ))
    (h13 : ∀ (k : ℕ) [NeZero k] (χ : DirichletCharacter ℂ k), χ.IsPrimitive → 3 ≤ k →
      k ∣ q → ‖psiChi χ u‖ ≤ 0.83 * Real.sqrt u * Real.log u ^ 2) :
    |psiMod u q l - psiMod u 1 0 / (Nat.totient q : ℝ)| ≤
      ((Nat.totient q : ℝ) - 1) / (Nat.totient q : ℝ) * 0.83 * Real.sqrt u * Real.log u ^ 2 +
        2 * Real.log u ^ 2 := by
  haveI : NeZero q := ⟨by omega⟩
  set E := ∑ n ∈ (Finset.Iic ⌊u⌋₊).filter (fun n => ¬ n.Coprime q),
    ArithmeticFunction.vonMangoldt n with hEdef
  have hE2 : E ≤ 2 * Real.log u ^ 2 := s145_E_bound hq hu hqu
  set S := 0.83 * Real.sqrt u * Real.log u ^ 2 with hS
  have hS0 : 0 ≤ S := by positivity
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
  set φ : ℝ := (Nat.totient q : ℝ) with hφ
  have hφ1 : 1 ≤ φ := by
    have : 0 < q.totient := Nat.totient_pos.mpr (by omega)
    rw [hφ]; exact_mod_cast this
  have ha : IsUnit (l : ZMod q) := (ZMod.isUnit_iff_coprime l q).mpr hl
  have hai : IsUnit ((l : ZMod q)⁻¹) := ⟨⟨_, _, ZMod.inv_mul_of_unit _ ha, ZMod.mul_inv_of_unit _ ha⟩, rfl⟩
  -- the orthogonality identity, split at the principal character
  have hid := s145_orth (u := u) hl
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ q)),
    MulChar.one_apply hai, one_mul] at hid
  -- principal term
  have hP : ‖psiChi (1 : DirichletCharacter ℂ q) u - (psiMod u 1 0 : ℂ)‖ ≤ E := by
    rw [norm_sub_rev, s145_psiMod_one]
    refine s145_diff (fun _ => (1 : ℂ)) (fun n => (1 : DirichletCharacter ℂ q) (n : ZMod q))
      ?_ ?_ ?_
    · intro n hn
      exact (MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hn)).symm
    · intro n hn
      exact MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])
    · intro n; simp
  -- non principal terms
  have hcard : (((Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1).card : ℝ) = φ - 1 := by
    have h1 := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    rw [Nat.card_eq_fintype_card] at h1
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, h1, hφ]
    have : 1 ≤ q.totient := Nat.totient_pos.mpr (by omega)
    push_cast [this]; ring
  have hN : ‖∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
      χ ((l : ZMod q)⁻¹) * psiChi χ u‖ ≤ (φ - 1) * (S + E) := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, (S + E) := by
          apply Finset.sum_le_sum
          intro χ hχ
          rw [norm_mul]
          have h1 := DirichletCharacter.norm_le_one χ ((l : ZMod q)⁻¹)
          have h2 := s145_nonprincipal h13 χ (Finset.ne_of_mem_erase hχ)
          have h3 : 0 ≤ ‖psiChi χ u‖ := norm_nonneg _
          calc ‖χ ((l : ZMod q)⁻¹)‖ * ‖psiChi χ u‖ ≤ 1 * ‖psiChi χ u‖ :=
                mul_le_mul_of_nonneg_right h1 h3
            _ ≤ S + E := by rw [one_mul]; exact h2
      _ = (φ - 1) * (S + E) := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
  -- combine
  have hD : ‖(φ : ℂ) * (psiMod u q l : ℂ) - (psiMod u 1 0 : ℂ)‖ ≤ (φ - 1) * S + φ * E := by
    rw [hφ, Complex.ofReal_natCast, ← hid]
    have he : psiChi (1 : DirichletCharacter ℂ q) u + ∑ χ ∈ (Finset.univ : Finset
        (DirichletCharacter ℂ q)).erase 1, χ ((l : ZMod q)⁻¹) * psiChi χ u - (psiMod u 1 0 : ℂ) =
        (psiChi (1 : DirichletCharacter ℂ q) u - (psiMod u 1 0 : ℂ)) + ∑ χ ∈ (Finset.univ : Finset
        (DirichletCharacter ℂ q)).erase 1, χ ((l : ZMod q)⁻¹) * psiChi χ u := by ring
    rw [he]
    refine (norm_add_le _ _).trans ?_
    nlinarith
  have hφ0 : 0 < φ := by linarith
  have hreal : psiMod u q l - psiMod u 1 0 / φ = (φ * psiMod u q l - psiMod u 1 0) / φ := by
    field_simp
  rw [hreal, abs_div, abs_of_pos hφ0, div_le_iff₀ hφ0]
  have hc : |φ * psiMod u q l - psiMod u 1 0| =
      ‖(φ : ℂ) * (psiMod u q l : ℂ) - (psiMod u 1 0 : ℂ)‖ := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hc]
  refine hD.trans ?_
  have : (φ - 1) / φ * 0.83 * Real.sqrt u * Real.log u ^ 2 * φ = (φ - 1) * S := by
    rw [hS]; field_simp
  nlinarith

end S145_psiMod_orthogonality

/-- LEAF: the orthogonality step, p. 340: `ψ(x;q,l) = φ(q)⁻¹ Σ_χ ψ(x,χ) χ̄(l)`, the principal
term against `ψ(x)` and each non principal `χ` against its primitive `χ₁` with error
`Σ_{(n,q)>1} Λ(n) ≤ ln² x`, then Lemma 1.3 `lemma13`, given as `h13`, on the `φ(q) - 1` others; no primitive
character mod 2 exists. Class
HARD. The `(φ(q) - 1)/φ(q)` factor is kept; the paper rounds it to `|c| ≤ 0.84`. -/
theorem psiMod_orthogonality {q l : ℕ} (hq : 3 ≤ q) (hl : Nat.Coprime l q) {u : ℝ}
    (hu : 10 ^ 9 ≤ u) (hqu : (q : ℝ) ≤ u ^ (0.37 : ℝ))
    (h13 : ∀ (k : ℕ) [NeZero k] (χ : DirichletCharacter ℂ k), χ.IsPrimitive → 3 ≤ k →
      k ∣ q → ‖psiChi χ u‖ ≤ 0.83 * Real.sqrt u * Real.log u ^ 2) :
    |psiMod u q l - psiMod u 1 0 / (Nat.totient q : ℝ)| ≤
      ((Nat.totient q : ℝ) - 1) / (Nat.totient q : ℝ) * 0.83 * Real.sqrt u * Real.log u ^ 2 +
        2 * Real.log u ^ 2 := by
  exact psiMod_orthogonality_s145 hq hl hu hqu h13

/-- LEAF: Schoenfeld 1976, reference [4], as quoted on p. 341: under RH, for `x > 75`,
`|ψ(x) - x| ≤ √x ln² x / (8π)`. Class HARD, a cited result. RH is the case `q = 1` of GRH. -/
theorem schoenfeld_psi (hG : LeanLab.DERZ1997.GRH) {x : ℝ} (hx : 75 < x) :
    |psiMod x 1 0 - x| ≤ Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi) := by
  sorry

/-- The final numerics of p. 341, proved: the bounds of the orthogonality step and of
Schoenfeld combine to `|c| ≤ 0.85`. -/
theorem psiMod_low_numerics {Ψq ψ u φ : ℝ} (hφ : 1 ≤ φ) (hu : 10 ^ 9 ≤ u)
    (hA : |Ψq - ψ / φ| ≤ (φ - 1) / φ * 0.83 * Real.sqrt u * Real.log u ^ 2 +
      2 * Real.log u ^ 2)
    (hB : |ψ - u| ≤ Real.sqrt u * Real.log u ^ 2 / (8 * Real.pi)) :
    |Ψq - u / φ| ≤ 0.85 * Real.sqrt u * Real.log u ^ 2 := by
  have hφ0 : 0 < φ := by linarith
  have hL2n : 0 ≤ Real.log u ^ 2 := sq_nonneg _
  have hsq : (100 : ℝ) ≤ Real.sqrt u := by
    rw [show (100 : ℝ) = Real.sqrt (100 ^ 2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by linarith)
  obtain ⟨S, hS⟩ : ∃ S, S = Real.sqrt u * Real.log u ^ 2 := ⟨_, rfl⟩
  have hSn : 0 ≤ S := by rw [hS]; positivity
  have hdec : Ψq - u / φ = (Ψq - ψ / φ) + (ψ - u) / φ := by
    rw [sub_div]; ring
  have hB1 : |ψ - u| ≤ 0.83 * S := by
    refine hB.trans ?_
    rw [div_le_iff₀ (by positivity), ← hS]
    nlinarith [Real.pi_gt_three]
  have hB' : |(ψ - u) / φ| ≤ 0.83 * S / φ := by
    rw [abs_div, abs_of_pos hφ0]
    exact div_le_div_of_nonneg_right hB1 hφ0.le
  have hfac : (φ - 1) / φ * 0.83 * Real.sqrt u * Real.log u ^ 2 = 0.83 * S - 0.83 * S / φ := by
    rw [hS, sub_div, div_self hφ0.ne']; ring
  have h2 : 2 * Real.log u ^ 2 ≤ 0.02 * S := by rw [hS]; nlinarith
  rw [hdec]
  calc |(Ψq - ψ / φ) + (ψ - u) / φ| ≤ |Ψq - ψ / φ| + |(ψ - u) / φ| := abs_add_le _ _
    _ ≤ 0.85 * S := by linarith
    _ = 0.85 * Real.sqrt u * Real.log u ^ 2 := by rw [hS]; ring

/-- `psiMod_grh_low` from `lemma13` of Decomp575a, `psiMod_orthogonality` and `schoenfeld_psi`,
with the proved numerics. The statement of `psiMod_grh_low`, copied verbatim.
CONDITIONAL ON those three, `lemma13` resting on the leaf `lemma13_explicit_budget`. -/
theorem psiMod_grh_low_of_leaves (hG : LeanLab.DERZ1997.GRH) {q l : ℕ} (hq : 3 ≤ q)
    (hl : Nat.Coprime l q) {u : ℝ} (hu : 10 ^ 9 ≤ u) (hqu : (q : ℝ) ≤ u ^ (0.37 : ℝ)) :
    |psiMod u q l - u / (Nat.totient q : ℝ)| ≤ 0.85 * Real.sqrt u * Real.log u ^ 2 := by
  have hφ : (1 : ℝ) ≤ Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hq0 : (0 : ℝ) ≤ q := by positivity
  refine psiMod_low_numerics hφ hu ?_ (schoenfeld_psi hG (by linarith))
  refine psiMod_orthogonality hq hl hu hqu ?_
  intro k _ χ hχ hk hkq
  refine lemma13 hG hk χ hχ hu ?_
  exact le_trans (by exact_mod_cast Nat.le_of_dvd (by omega) hkq) hqu

/-- LEAF: the same display of p. 341 for heights `u ≥ 10⁹` with `q > u^0.37`. Class HARD.
The proof of Proposition 1.4 integrates the bound of p. 341 over `u ∈ [10⁹, x]` while
Lemma 1.3 only covers `q ≤ u^0.37`; the paper does not treat this range. For `q > √u` the
trivial bound suffices; for `u^0.37 < q ≤ √u` a GRH bound uniform in `q` is needed. -/
theorem psiMod_grh_high (hG : LeanLab.DERZ1997.GRH) {q l : ℕ} (hq : 3 ≤ q)
    (hl : Nat.Coprime l q) {u : ℝ} (hu : 10 ^ 9 ≤ u) (hqu : u ^ (0.37 : ℝ) < (q : ℝ)) :
    |psiMod u q l - u / (Nat.totient q : ℝ)| ≤ 0.85 * Real.sqrt u * Real.log u ^ 2 := by
  sorry

/-- The final numerics of the estimate of `R`, p. 341, proved: a piece below `x₀ = 10⁹` of size
at most `10⁸ - 3` and the piece `c ∫_{x₀}^x du/√u ≤ 0.85 · 2√x` above `x₀` give the bound of
`prop14_remainder`, since `ln x ≥ 29 ln 2 > 20` for `x ≥ 10⁹`. -/
theorem prop14_remainder_numerics {I₁ I₂ x : ℝ} (hx : 10 ^ 9 ≤ x)
    (h₁ : |I₁| ≤ 10 ^ 8 - 3) (h₂ : |I₂| ≤ 0.85 * (2 * Real.sqrt x)) :
    |I₁ + I₂| ≤ 0.15 * Real.sqrt x * Real.log x + (10 ^ 8 - 3) := by
  have hL : 20 ≤ Real.log x := by
    have h29 : ((2 : ℝ) ^ 29) ≤ x := by norm_num at hx ⊢; linarith
    have := Real.log_le_log (by positivity) h29
    rw [Real.log_pow] at this
    push_cast at this
    linarith [Real.log_two_gt_d9]
  have hs : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have : 0.85 * (2 * Real.sqrt x) ≤ 0.15 * Real.sqrt x * Real.log x := by nlinarith
  exact (abs_add_le _ _).trans (by linarith)

section S145_prop14_remainder
open MeasureTheory

theorem s145_psiMod_nonneg (u : ℝ) (q l : ℕ) : 0 ≤ psiMod u q l :=
  Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

theorem s145_psiMod_mono (q l : ℕ) : Monotone (fun u : ℝ => psiMod u q l) := by
  intro u v huv
  unfold psiMod
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Iic] at hn ⊢
    exact ⟨hn.1.trans (Nat.floor_mono huv), hn.2⟩
  · intro _ _ _; exact ArithmeticFunction.vonMangoldt_nonneg

theorem s145_psiMod_le (q l : ℕ) {u : ℝ} (hu : 1 ≤ u) : psiMod u q l ≤ u * Real.log u := by
  have hL : 0 ≤ Real.log u := Real.log_nonneg hu
  set N := ⌊u⌋₊ with hN
  have h1 : psiMod u q l ≤ ∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n := by
    unfold psiMod
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Iic] at hn
      simp only [Finset.mem_range]; omega
    · intro _ _ _; exact ArithmeticFunction.vonMangoldt_nonneg
  rw [Finset.sum_range_succ'] at h1
  simp only [ArithmeticFunction.map_zero, add_zero] at h1
  have h2 : ∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt (n + 1) ≤
      ∑ _n ∈ Finset.range N, Real.log u := by
    apply Finset.sum_le_sum
    intro n hn
    simp only [Finset.mem_range] at hn
    refine ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log (by positivity) ?_)
    have : ((n + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
    exact this.trans (Nat.floor_le (by linarith))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
  have hNu : (N : ℝ) ≤ u := Nat.floor_le (by linarith)
  nlinarith


theorem s145_log_ne {u : ℝ} (hu : 2 ≤ u) : Real.log u ≠ 0 := by
  have := Real.log_pos (show (1:ℝ) < u by linarith); exact this.ne'

theorem s145_cont (a b : ℝ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ContinuousOn (fun u : ℝ => 1 / (u * Real.log u ^ 2)) (Set.uIcc a b) := by
  have hmem : ∀ u ∈ Set.uIcc a b, 2 ≤ u := by
    intro u hu
    rcases Set.mem_uIcc.mp hu with h | h
    · linarith [h.1]
    · linarith [h.1]
  apply ContinuousOn.div continuousOn_const
  · apply ContinuousOn.mul continuousOn_id
    apply ContinuousOn.pow
    exact Real.continuousOn_log.mono (fun u hu => by
      have := hmem u hu; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith)
  · intro u hu
    have := hmem u hu
    have := s145_log_ne this
    positivity

theorem s145_cont2 (a b : ℝ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ContinuousOn (fun u : ℝ => 1 / Real.log u ^ 2) (Set.uIcc a b) := by
  have hmem : ∀ u ∈ Set.uIcc a b, 2 ≤ u := by
    intro u hu
    rcases Set.mem_uIcc.mp hu with h | h
    · linarith [h.1]
    · linarith [h.1]
  apply ContinuousOn.div continuousOn_const
  · apply ContinuousOn.pow
    exact Real.continuousOn_log.mono (fun u hu => by
      have := hmem u hu; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith)
  · intro u hu
    have := s145_log_ne (hmem u hu)
    positivity

theorem s145_ii1 (q l : ℕ) (a b : ℝ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun u => psiMod u q l / (u * Real.log u ^ 2)) volume a b := by
  have := ((s145_psiMod_mono q l).intervalIntegrable (μ := volume) (a := a) (b := b)).mul_continuousOn
    (s145_cont a b ha hb)
  refine this.congr ?_
  intro u _
  simp [div_eq_mul_inv]

theorem s145_ii (q l : ℕ) (φ : ℝ) (a b : ℝ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun u => psiMod u q l / (u * Real.log u ^ 2) - 1 / Real.log u ^ 2 / φ)
      volume a b :=
  (s145_ii1 q l a b ha hb).sub ((s145_cont2 a b ha hb).intervalIntegrable.div_const φ)

theorem s145_pt (q l : ℕ) {φ u : ℝ} (hu : 2 ≤ u) :
    psiMod u q l / (u * Real.log u ^ 2) - 1 / Real.log u ^ 2 / φ =
      (psiMod u q l - u / φ) / (u * Real.log u ^ 2) := by
  have := s145_log_ne hu
  have : u ≠ 0 := by linarith
  field_simp

theorem s145_lower_bd (q l : ℕ) {φ u L : ℝ} (hφ : 1 ≤ φ) (hu : 2 ≤ u) (hL : L ≤ Real.log u)
    (hL0 : 0 < L) :
    |psiMod u q l - u / φ| / (u * Real.log u ^ 2) ≤ 1 / L + 1 / L ^ 2 := by
  have hl := Real.log_pos (show (1:ℝ) < u by linarith)
  have h0 := s145_psiMod_nonneg u q l
  have h1 := s145_psiMod_le q l (show (1:ℝ) ≤ u by linarith)
  have hb0 : 0 ≤ u / φ := by positivity
  have hb1 : u / φ ≤ u := div_le_self (by linarith) hφ
  have habs : |psiMod u q l - u / φ| ≤ u * Real.log u + u := by
    rw [abs_le]; constructor <;> nlinarith
  have hpos : 0 < u * Real.log u ^ 2 := by positivity
  rw [div_le_iff₀ hpos]
  refine habs.trans ?_
  have e : (1 / L + 1 / L ^ 2) * (u * Real.log u ^ 2) =
      u * Real.log u * (Real.log u / L) + u * (Real.log u / L) ^ 2 := by
    field_simp
  rw [e]
  have hr : 1 ≤ Real.log u / L := by rw [le_div_iff₀ hL0]; linarith
  have hu0 : 0 ≤ u := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hr (mul_nonneg hu0 hl.le),
    mul_le_mul_of_nonneg_left (one_le_pow₀ (n := 2) hr) hu0]

theorem s145_mid_bd (q l : ℕ) {φ u L : ℝ} (hφ : 1 ≤ φ) (hu : 2 ≤ u) (hL : L ≤ Real.log u)
    (hL1 : 1 ≤ L) :
    |psiMod u q l - u / φ| / (u * Real.log u ^ 2) ≤ 1 / L := by
  have hl : 1 ≤ Real.log u := by linarith
  have h0 := s145_psiMod_nonneg u q l
  have h1 := s145_psiMod_le q l (show (1:ℝ) ≤ u by linarith)
  have hb0 : 0 ≤ u / φ := by positivity
  have hb1 : u / φ ≤ u := div_le_self (by linarith) hφ
  have hu0 : 0 ≤ u := by linarith
  have habs : |psiMod u q l - u / φ| ≤ u * Real.log u := by
    rw [abs_le]; constructor <;> nlinarith
  have hpos : 0 < u * Real.log u ^ 2 := by positivity
  rw [div_le_iff₀ hpos]
  refine habs.trans ?_
  have e : 1 / L * (u * Real.log u ^ 2) = u * Real.log u * (Real.log u / L) := by
    field_simp
  rw [e]
  have hr : 1 ≤ Real.log u / L := by rw [le_div_iff₀ (by linarith)]; linarith
  nlinarith [mul_le_mul_of_nonneg_left hr (mul_nonneg hu0 (by linarith : (0:ℝ) ≤ Real.log u))]


theorem s145_I1 (q l : ℕ) {φ : ℝ} (hφ : 1 ≤ φ) :
    |∫ u in (2 : ℝ)..(10 ^ 9), (psiMod u q l / (u * Real.log u ^ 2) - 1 / Real.log u ^ 2 / φ)|
      ≤ 10 ^ 8 - 3 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (10 ^ 6 : ℝ))
    (s145_ii q l φ _ _ le_rfl (by norm_num)) (s145_ii q l φ _ _ (by norm_num) (by norm_num))]
  have hA : ‖∫ u in (2 : ℝ)..(10 ^ 6),
      (psiMod u q l / (u * Real.log u ^ 2) - 1 / Real.log u ^ 2 / φ)‖ ≤ 4 * |10 ^ 6 - 2| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    rw [Set.uIoc_of_le (by norm_num)] at hu
    have hu2 : 2 ≤ u := hu.1.le
    rw [Real.norm_eq_abs, s145_pt q l hu2, abs_div, abs_of_pos (by
      have := s145_log_ne hu2; positivity : (0:ℝ) < u * Real.log u ^ 2)]
    refine (s145_lower_bd q l hφ hu2 (L := 0.69) ?_ (by norm_num)).trans (by norm_num)
    exact (Real.log_two_gt_d9.le.trans' (by norm_num)).trans
      (Real.log_le_log (by norm_num) hu2)
  have hB : ‖∫ u in (10 ^ 6 : ℝ)..(10 ^ 9),
      (psiMod u q l / (u * Real.log u ^ 2) - 1 / Real.log u ^ 2 / φ)‖ ≤
        (1 / 13) * |10 ^ 9 - 10 ^ 6| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    rw [Set.uIoc_of_le (by norm_num)] at hu
    have hu6 : 10 ^ 6 ≤ u := hu.1.le
    have hu2 : 2 ≤ u := by linarith
    rw [Real.norm_eq_abs, s145_pt q l hu2, abs_div, abs_of_pos (by
      have := s145_log_ne hu2; positivity : (0:ℝ) < u * Real.log u ^ 2)]
    refine s145_mid_bd q l hφ hu2 ?_ (by norm_num)
    have h19 : ((2 : ℝ) ^ 19) ≤ u := by linarith
    have := Real.log_le_log (by positivity) h19
    rw [Real.log_pow] at this
    push_cast at this
    linarith [Real.log_two_gt_d9]
  rw [Real.norm_eq_abs] at hA hB
  refine (abs_add_le _ _).trans ?_
  norm_num at hA hB ⊢
  linarith

theorem s145_I2 (q l : ℕ) {φ x : ℝ} (hx : 10 ^ 9 ≤ x)
    (hB : ∀ u ∈ Set.Icc (10 ^ 9 : ℝ) x,
      |psiMod u q l - u / φ| ≤ 0.85 * Real.sqrt u * Real.log u ^ 2) :
    |∫ u in (10 ^ 9 : ℝ)..x, (psiMod u q l / (u * Real.log u ^ 2) - 1 / Real.log u ^ 2 / φ)|
      ≤ 0.85 * (2 * Real.sqrt x) := by
  have hint : IntervalIntegrable (fun u : ℝ => 0.85 * u ^ (-(1/2) : ℝ)) volume (10 ^ 9) x :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
  have h := intervalIntegral.norm_integral_le_of_norm_le (f := fun u =>
      psiMod u q l / (u * Real.log u ^ 2) - 1 / Real.log u ^ 2 / φ) hx ?_ hint
  · rw [Real.norm_eq_abs] at h
    refine h.trans (le_of_eq_of_le
      (b := 0.85 * ((x ^ (1/2 : ℝ) - (10 ^ 9 : ℝ) ^ (1/2 : ℝ)) / (1/2))) ?_ ?_)
    · rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
      norm_num
    · rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      have := Real.sqrt_nonneg (1000000000 : ℝ)
      rw [div_eq_mul_inv]; norm_num
      linarith
  · refine Filter.Eventually.of_forall (fun u hu => ?_)
    have hu9 : 10 ^ 9 ≤ u := hu.1.le
    have hu2 : 2 ≤ u := by linarith
    have hpos : (0:ℝ) < u * Real.log u ^ 2 := by have := s145_log_ne hu2; positivity
    show ‖psiMod u q l / (u * Real.log u ^ 2) - 1 / Real.log u ^ 2 / φ‖ ≤ 0.85 * u ^ (-(1/2) : ℝ)
    rw [Real.norm_eq_abs, s145_pt q l hu2, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    refine (hB u ⟨hu9, hu.2⟩).trans (le_of_eq ?_)
    have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr (by linarith)
    rw [Real.rpow_neg (by linarith), ← Real.sqrt_eq_rpow]
    have hss : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt (by linarith)
    field_simp
    nlinarith [hss]

theorem prop14_remainder_s145 {q l : ℕ} (hq : 1 ≤ q) {x : ℝ} (hx : 10 ^ 9 ≤ x)
    (hB : ∀ u ∈ Set.Icc (10 ^ 9 : ℝ) x,
      |psiMod u q l - u / (Nat.totient q : ℝ)| ≤ 0.85 * Real.sqrt u * Real.log u ^ 2) :
    |(∫ u in (2 : ℝ)..x, psiMod u q l / (u * Real.log u ^ 2)) -
        (∫ u in (2 : ℝ)..x, 1 / Real.log u ^ 2) / (Nat.totient q : ℝ)| ≤
      0.15 * Real.sqrt x * Real.log x + (10 ^ 8 - 3) := by
  have hφ : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hx2 : (2 : ℝ) ≤ x := by linarith
  rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_sub (s145_ii1 q l _ _ le_rfl hx2)
    ((s145_cont2 _ _ le_rfl hx2).intervalIntegrable.div_const _),
    ← intervalIntegral.integral_add_adjacent_intervals (b := (10 ^ 9 : ℝ))
      (s145_ii q l _ _ _ le_rfl (by norm_num)) (s145_ii q l _ _ _ (by norm_num) hx2)]
  exact prop14_remainder_numerics hx (s145_I1 q l hφ) (s145_I2 q l hx hB)

end S145_prop14_remainder

/-- LEAF: the estimate of `R`, p. 341, with `x₀ = 10⁹`. Class MEDIUM. Given the bound of
p. 341 on `[x₀, x]`, the trivial bound `ψ(t;q,l) ≤ ψ(t)` below `x₀` and
`∫_{x₀}^x du/√u ≤ 2√x` give `|∫₂ˣ (ψ(u;q,l) - u/φ(q))/(u ln² u) du| ≤ 0.15 √x ln x + 10⁸ - 3`.
The paper's total `0.1 √x ln x + 10⁸` also absorbs `3/φ(q)`. -/
theorem prop14_remainder {q l : ℕ} (hq : 1 ≤ q) {x : ℝ} (hx : 10 ^ 9 ≤ x)
    (hB : ∀ u ∈ Set.Icc (10 ^ 9 : ℝ) x,
      |psiMod u q l - u / (Nat.totient q : ℝ)| ≤ 0.85 * Real.sqrt u * Real.log u ^ 2) :
    |(∫ u in (2 : ℝ)..x, psiMod u q l / (u * Real.log u ^ 2)) -
        (∫ u in (2 : ℝ)..x, 1 / Real.log u ^ 2) / (Nat.totient q : ℝ)| ≤
      0.15 * Real.sqrt x * Real.log x + (10 ^ 8 - 3) := by
  exact prop14_remainder_s145 hq hx hB

/-- LEAF: Schoenfeld 1976, reference [4] of the paper, Corollary 1, as used on p. 341 for
`q = 1, 2`: under RH, `|π(x) - li(x)| < √x ln x / (8π)` for `x ≥ 2657`. Class HARD, a cited
result. Schoenfeld's `li` integrates from `0`, so `li(x) = Li(x) + li(2)` with
`li(2) < 1.05`; the `+ 2` covers that shift. RH is the case `q = 1` of GRH. -/
theorem schoenfeld_pi (hG : LeanLab.DERZ1997.GRH) {x : ℝ} (hx : 2657 ≤ x) :
    |(piMod x 1 0 : ℝ) - zinLi x| ≤ Real.sqrt x * Real.log x / (8 * Real.pi) + 2 := by
  sorry

/-- `π(x; 2, l) = π(x) - 1` for odd `l` and `x ≥ 2`, p. 341 "If q = 1, 2 then
π(x; q, l) is π(x)". Proved. -/
theorem piMod_two {l : ℕ} (hl : Nat.Coprime l 2) {x : ℝ} (hx : 2 ≤ x) :
    (piMod x 2 l : ℝ) = piMod x 1 0 - 1 := by
  have hl2 : l % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one l with h | h
    · exfalso
      have : 2 ∣ Nat.gcd l 2 := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h) dvd_rfl
      rw [hl] at this; omega
    · exact h
  have h2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hset : (Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ p % 1 = 0 % 1) =
      insert 2 ((Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ p % 2 = l % 2)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_insert, Nat.mod_one, hl2]
    constructor
    · rintro ⟨hp, hpr, -⟩
      rcases hpr.eq_two_or_odd with h | h
      · left; exact h
      · right; exact ⟨hp, hpr, h⟩
    · rintro (rfl | ⟨hp, hpr, -⟩)
      · exact ⟨h2, Nat.prime_two, trivial⟩
      · exact ⟨hp, hpr, trivial⟩
  have hnot : 2 ∉ (Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ p % 2 = l % 2) := by
    simp [hl2]
  unfold piMod
  rw [hset, Finset.card_insert_of_notMem hnot]
  push_cast; ring


/-- `π(x; 1, l) = π(x)`, p. 341. -/
theorem piMod_one (x : ℝ) (l : ℕ) : piMod x 1 l = piMod x 1 0 := by
  simp [piMod, Nat.mod_one]

/-- Proposition 1.4 error form, Zinoviev 1997 pp. 339 to 341, from the leaves above.
The statement of `prop14_error_bound`, copied verbatim.
CONDITIONAL ON `prop14_abel`, `psiMod_grh_low`, `psiMod_grh_high`, `prop14_remainder`,
and `schoenfeld_pi`. -/
theorem prop14_error_bound_of_leaves (hG : LeanLab.DERZ1997.GRH) {q l : ℕ}
    (hq : 1 ≤ q) (hl : Nat.Coprime l q) {x : ℝ} (hx : 10 ^ 9 ≤ x)
    (hqx : (q : ℝ) ≤ x ^ (0.37 : ℝ)) :
    |(piMod x q l : ℝ) - zinLi x / (Nat.totient q : ℝ)| ≤
      1.3 * Real.sqrt x * Real.log x + 10 ^ 8 := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hS : 0 ≤ Real.sqrt x * Real.log x := mul_nonneg (Real.sqrt_nonneg x) hL.le
  rcases Nat.lt_or_ge q 3 with h3 | h3
  · -- q = 1 or q = 2, Schoenfeld
    have hsch := schoenfeld_pi hG (x := x) (by linarith)
    have hpi : Real.sqrt x * Real.log x / (8 * Real.pi) ≤ Real.sqrt x * Real.log x := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_gt_three]
    interval_cases q
    · rw [piMod_one]
      simp only [Nat.totient_one, Nat.cast_one, div_one]
      linarith
    · rw [piMod_two hl (by linarith)]
      simp only [Nat.totient_two, Nat.cast_one, div_one]
      rw [show (piMod x 1 0 : ℝ) - 1 - zinLi x = ((piMod x 1 0 : ℝ) - zinLi x) - 1 by ring]
      refine (abs_sub _ _).trans ?_
      rw [abs_one]
      linarith
  · have hφ : (1 : ℝ) ≤ Nat.totient q := by
      exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hφ0 : (0 : ℝ) < Nat.totient q := by linarith
    have hB : ∀ u ∈ Set.Icc (10 ^ 9 : ℝ) x,
        |psiMod u q l - u / (Nat.totient q : ℝ)| ≤ 0.85 * Real.sqrt u * Real.log u ^ 2 := by
      intro u hu
      rcases le_or_gt (q : ℝ) (u ^ (0.37 : ℝ)) with h | h
      · exact psiMod_grh_low hG h3 hl hu.1 h
      · exact psiMod_grh_high hG h3 hl hu.1 h
    have hA := prop14_abel (l := l) hq hx
    have hR := prop14_remainder (l := l) hq hx hB
    have hX := hB x ⟨hx, le_rfl⟩
    have hLi := zinLi_by_parts (x := x) (by linarith)
    have hlog2 : 0.69 < Real.log 2 := by linarith [Real.log_two_gt_d9]
    set P : ℝ := (piMod x q l : ℝ)
    set Ψ : ℝ := psiMod x q l
    set I : ℝ := ∫ u in (2 : ℝ)..x, psiMod u q l / (u * Real.log u ^ 2)
    set J : ℝ := ∫ u in (2 : ℝ)..x, 1 / Real.log u ^ 2
    set φ : ℝ := (Nat.totient q : ℝ)
    set L : ℝ := Real.log x
    have hdec : P - zinLi x / φ =
        (P - (Ψ / L + I)) + (Ψ - x / φ) / L + (I - J / φ) + 2 / (Real.log 2 * φ) := by
      rw [hLi]
      field_simp
      ring
    have hmid : |(Ψ - x / φ) / L| ≤ 0.85 * Real.sqrt x * L := by
      rw [abs_div, abs_of_pos hL, div_le_iff₀ hL]
      nlinarith
    have hlast : |2 / (Real.log 2 * φ)| ≤ 3 := by
      rw [abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
      nlinarith
    rw [hdec]
    have h4 := (abs_add_le (P - (Ψ / L + I) + (Ψ - x / φ) / L + (I - J / φ))
      (2 / (Real.log 2 * φ))).trans (add_le_add
        (abs_add_three (P - (Ψ / L + I)) ((Ψ - x / φ) / L) (I - J / φ)) le_rfl)
    have hR' : |I - J / φ| ≤ 0.15 * Real.sqrt x * L + (10 ^ 8 - 3) := hR
    have hA' : |P - (Ψ / L + I)| ≤ 0.1 * Real.sqrt x * L := hA
    nlinarith

end LeanLab.Zinoviev1997.State1546
