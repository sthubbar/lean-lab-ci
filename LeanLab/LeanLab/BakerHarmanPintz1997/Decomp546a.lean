/-
P0069 pages 28 to 31. Elementary infrastructure for the three prime ranges.
The dependent cutoff and analytic transfer are separate obligations.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Decomp1518

noncomputable section
namespace LeanLab.BakerHarmanPintz1997.Decomp546a
open Finset ArithmeticFunction Decomp1518
attribute [local instance] Classical.propDecidable

/-- Page 31 dyadic convention: M at most N gives m less than 2n. -/
theorem dyadic_order {M N : ℝ} {m n : ℕ} (hMN : M ≤ N)
    (hm : m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊) (hn : n ∈ Ioc ⌊N⌋₊ ⌊2 * N⌋₊) :
    (m : ℝ) < 2 * n := by
  have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hm).1
  have hM : 0 ≤ M := by
    by_contra h
    have hf : ⌊2 * M⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    have := (mem_Ioc.mp hm).2
    omega
  have hm2 : (m : ℝ) ≤ 2 * M :=
    (Nat.cast_le.mpr (mem_Ioc.mp hm).2).trans (Nat.floor_le (by linarith))
  have hnN : N < (n : ℝ) := (Nat.floor_lt (hM.trans hMN)).mp (mem_Ioc.mp hn).1
  linarith

/-- Page 31 cofactor display with the factor two required by dyadic ordering. -/
theorem dyadic_large_cofactor {x m n p h : ℝ} (hx : 0 < x)
    (hm : 0 ≤ m) (hp0 : 0 ≤ p) (hh : 0 ≤ h) (hmn : m ≤ 2 * n)
    (hprod : m * n * p * h ≤ x) (hp : p ≤ x ^ (0.1 : ℝ))
    (hmp : x ^ (0.46 : ℝ) < m * p) : h ≤ 2 * x ^ (0.18 : ℝ) := by
  have hm2 : m ^ 2 ≤ 2 * (m * n) := by
    nlinarith [mul_nonneg hm (sub_nonneg.mpr hmn)]
  have hb : (h / 2) * (m * p) ^ 2 ≤ x ^ (1.1 : ℝ) := by
    calc
      _ = (m ^ 2 * (p ^ 2 * h)) / 2 := by ring
      _ ≤ (2 * (m * n) * (p ^ 2 * h)) / 2 := by gcongr
      _ = (m * n * p * h) * p := by ring
      _ ≤ x * x ^ (0.1 : ℝ) := mul_le_mul hprod hp hp0 hx.le
      _ = x ^ (1.1 : ℝ) := by
        nth_rw 1 [← Real.rpow_one x]
        rw [← Real.rpow_add hx]
        norm_num
  have := cond422_z_le hx hmp hb
  linarith

/-- Page 31 ratio display with both dyadic constants retained. -/
theorem dyadic_large_ratios {x m n p : ℝ} (hx : 0 < x) (hn : 0 < n)
    (hp0 : 0 ≤ p) (hmn : m ≤ 2 * n) (hp : p ≤ x ^ (0.1 : ℝ))
    (hnx : n ≤ 2 * x ^ (0.4 : ℝ)) (hmp : x ^ (0.46 : ℝ) ≤ m * p) :
    m * p / n ≤ 2 * x ^ (0.1 : ℝ) ∧ n / (m * p) ≤ 2 * x ^ (-0.06 : ℝ) := by
  have hpow : 0 < x ^ (0.46 : ℝ) := Real.rpow_pos_of_pos hx _
  refine ⟨?_, ?_⟩
  · apply (div_le_iff₀ hn).mpr
    nlinarith [mul_le_mul_of_nonneg_right hmn hp0]
  · calc
      _ ≤ (2 * x ^ (0.4 : ℝ)) / x ^ (0.46 : ℝ) := by gcongr
      _ = 2 * x ^ (-0.06 : ℝ) := by
        rw [mul_div_assoc, ← Real.rpow_sub hx]
        congr 1
        norm_num

/- Verification instances. -/
example : (4 : ℝ) < 2 * (3 : ℕ) :=
  dyadic_order (M := 2) (N := 2) (by norm_num) (by norm_num) (by norm_num)

example : (1 / 2 : ℝ) ≤ 2 * (1 : ℝ) ^ (0.18 : ℝ) := by
  apply dyadic_large_cofactor (x := 1) (m := 2) (n := 1) (p := 1) <;> norm_num

example : (2 : ℝ) * 1 / 1 ≤ 2 * (1 : ℝ) ^ (0.1 : ℝ) ∧
    (1 : ℝ) / (2 * 1) ≤ 2 * (1 : ℝ) ^ (-0.06 : ℝ) := by
  apply dyadic_large_ratios (x := 1) <;> norm_num

/-- Page 31 exact grouping u = mp. The kernel remains allowed to depend on p. -/
theorem prime_divisor_regroup {L : ℕ} (hL : 0 < L) (F : ℕ → ℕ → ℕ → ℂ) :
    (∑ m ∈ L.divisors, ∑ p ∈ (L / m).primeFactors, F m p (L / m / p)) =
      ∑ u ∈ L.divisors, ∑ p ∈ u.primeFactors, F (u / p) p (L / u) := by
  rw [sum_sigma', sum_sigma']
  apply sum_bij (fun a _ => (⟨a.1 * a.2, a.2⟩ : (i : ℕ) × ℕ))
  · intro a ha
    obtain ⟨hm, hp⟩ := mem_sigma.mp ha
    have hpm := Nat.dvd_of_mem_primeFactors hp
    have hmp : a.1 * a.2 ∣ L := by
      have := Nat.mul_dvd_of_dvd_div (Nat.dvd_of_mem_divisors hm) hpm
      simpa [mul_comm] using this
    have hm0 : a.1 ≠ 0 := (Nat.pos_of_mem_divisors hm).ne'
    apply mem_sigma.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨hmp, hL.ne'⟩, ?_⟩
    exact (Nat.prime_of_mem_primeFactors hp).mem_primeFactors
      (dvd_mul_left _ _) (mul_ne_zero hm0 (Nat.prime_of_mem_primeFactors hp).ne_zero)
  · intro a ha b hb hab
    have hab2 : a.2 = b.2 := congrArg Sigma.snd hab
    have hpa : a.2 ≠ 0 := (Nat.prime_of_mem_primeFactors (mem_sigma.mp ha).2).ne_zero
    have hab1 : a.1 = b.1 := by
      have hh : a.1 * a.2 = b.1 * a.2 := by simpa [hab2] using congrArg Sigma.fst hab
      exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hpa) hh
    cases a
    cases b
    simp_all
  · intro b hb
    obtain ⟨hu, hp⟩ := mem_sigma.mp hb
    have hpu : b.2 ∣ b.1 := Nat.dvd_of_mem_primeFactors hp
    have huL := Nat.dvd_of_mem_divisors hu
    have hq : b.1 / b.2 ∣ L := (Nat.div_dvd_of_dvd hpu).trans huL
    have hqp : (b.1 / b.2) * b.2 = b.1 := Nat.div_mul_cancel hpu
    have hpL : b.2 ∣ L / (b.1 / b.2) := by
      apply (Nat.dvd_div_iff_mul_dvd hq).mpr
      rwa [hqp]
    have hqpos : 0 < b.1 / b.2 := Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_mem_divisors hu) hpu)
      (Nat.prime_of_mem_primeFactors hp).pos
    have hquot : L / (b.1 / b.2) ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hL hq) hqpos).ne'
    refine ⟨⟨b.1 / b.2, b.2⟩, mem_sigma.mpr
      ⟨Nat.mem_divisors.mpr ⟨hq, hL.ne'⟩,
        (Nat.prime_of_mem_primeFactors hp).mem_primeFactors hpL hquot⟩, ?_⟩
    cases b
    simp_all
  · intro a ha
    have hp : 0 < a.2 := (Nat.prime_of_mem_primeFactors (mem_sigma.mp ha).2).pos
    simp [Nat.mul_div_cancel _ hp, Nat.div_div_eq_div_mul]

example :
    (∑ m ∈ (12 : ℕ).divisors, ∑ _p ∈ (12 / m).primeFactors, (1 : ℂ)) =
      ∑ u ∈ (12 : ℕ).divisors, ∑ _p ∈ u.primeFactors, (1 : ℂ) := by
  simpa using prime_divisor_regroup (L := 12) (by norm_num) (fun _ _ _ => (1 : ℂ))


/-- Page 29 coefficient display: any restricted divisor regrouping costs one tau factor. -/
theorem restricted_divisor_coeff {B : ℝ} (hB : 0 ≤ B) (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ tau n ^ B) {k : ℕ} (hk : 0 < k)
    (S : Finset ℕ) (hS : S ⊆ k.divisors) :
    ‖∑ d ∈ S, a (k / d)‖ ≤ tau k ^ (B + 1) := by
  have ht : 0 < tau k := by
    simp only [tau, sigma_zero_apply, Nat.cast_pos]
    exact card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hk.ne'⟩
  have hterm : ∀ d ∈ S, ‖a (k / d)‖ ≤ tau k ^ B := by
    intro d hd
    have hdiv : k / d ∣ k := Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors (hS hd))
    have htau : tau (k / d) ≤ tau k := by
      simp only [tau, sigma_zero_apply]
      exact_mod_cast card_le_card (Nat.divisors_subset_of_dvd hk.ne' hdiv)
    exact (ha _).trans (Real.rpow_le_rpow (by simp [tau]) htau hB)
  calc
    _ ≤ ∑ d ∈ S, ‖a (k / d)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ S, tau k ^ B := sum_le_sum hterm
    _ ≤ ∑ d ∈ k.divisors, tau k ^ B :=
      sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => Real.rpow_nonneg ht.le _)
    _ = tau k * tau k ^ B := by simp [tau, sigma_zero_apply]
    _ = _ := by rw [Real.rpow_add ht, Real.rpow_one]; ring

/-- Page 29 repeated coefficients indexed by subsets of distinct prime factors. -/
theorem prime_subset_coeff {B : ℝ} (hB : 0 ≤ B) (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ tau n ^ B) {k : ℕ} (hk : 0 < k)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPk : (∏ p ∈ P, p) ∣ k)
    (R : ℕ → Prop) :
    ‖∑ T ∈ P.powerset, if R (∏ p ∈ T, p) then a (k / (∏ p ∈ T, p)) else 0‖ ≤
      tau k ^ (B + 1) := by
  rw [← sum_divisors_prime_product P hP (fun d => if R d then a (k / d) else 0),
    ← Finset.sum_filter]
  apply restricted_divisor_coeff hB a ha hk
  exact subset_trans (filter_subset _ _) (Nat.divisors_subset_of_dvd hk.ne' hPk)

example : ‖∑ _d ∈ ({1, 2} : Finset ℕ), (1 : ℂ)‖ ≤ tau 6 ^ ((0 : ℝ) + 1) := by
  simpa using restricted_divisor_coeff (B := 0) (by norm_num) (fun _ => (1 : ℂ))
    (by intro n; simp) (k := 6) (by norm_num) ({1, 2} : Finset ℕ)
    (by intro d hd; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl <;> norm_num [Nat.mem_divisors])

example :
    ‖∑ _T ∈ ({2, 3} : Finset ℕ).powerset,
      if True then (1 : ℂ) else 0‖ ≤ tau 6 ^ ((0 : ℝ) + 1) := by
  simpa using prime_subset_coeff (B := 0) (by norm_num) (fun _ => (1 : ℂ))
    (by intro n; simp) (k := 6) (by norm_num) ({2, 3} : Finset ℕ)
    (by intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl <;> norm_num)
    (by norm_num) (fun _ => True)

/-- Page 29 ordered Buchstab prime chains are determined by their product.
Strict decrease prevents repeated factors and removes permutation multiplicity. -/
theorem prime_chain_unique {a b : List ℕ} (ha : a.Pairwise (· > ·))
    (hb : b.Pairwise (· > ·)) (hpa : ∀ p ∈ a, p.Prime) (hpb : ∀ p ∈ b, p.Prime)
    (hprod : a.prod = b.prod) : a = b := by
  have hfa : a.prod.primeFactors = a.toFinset := by
    have he : a.toFinset.prod id = a.prod := by simpa using List.prod_toFinset id ha.nodup
    rw [← he]
    exact Nat.primeFactors_prod (fun p hp => hpa p (List.mem_toFinset.mp hp))
  have hfb : b.prod.primeFactors = b.toFinset := by
    have he : b.toFinset.prod id = b.prod := by simpa using List.prod_toFinset id hb.nodup
    rw [← he]
    exact Nat.primeFactors_prod (fun p hp => hpb p (List.mem_toFinset.mp hp))
  have hs := congrArg Nat.primeFactors hprod
  rw [hfa, hfb] at hs
  apply ha.eq_of_mem_iff hb
  intro p
  simpa only [List.mem_toFinset] using Finset.ext_iff.mp hs p

example : ([5, 3, 2] : List ℕ) = [5, 3, 2] := by
  apply prime_chain_unique <;> norm_num

/-- Page 29 repeated coefficient display used on page 31. A restricted collection
of strictly decreasing prime chains has a divisor bound independent of its depth. -/
theorem prime_chain_coeff {B : ℝ} (hB : 0 ≤ B) (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ tau n ^ B) {k : ℕ} (hk : 0 < k)
    (S : Finset (List ℕ)) (hord : ∀ l ∈ S, l.Pairwise (· > ·))
    (hprime : ∀ l ∈ S, ∀ p ∈ l, p.Prime) (hdiv : ∀ l ∈ S, l.prod ∣ k) :
    ‖∑ l ∈ S, a (k / l.prod)‖ ≤ tau k ^ (B + 1) := by
  have hinj : Set.InjOn List.prod (↑S : Set (List ℕ)) := by
    intro l hl r hr he
    exact prime_chain_unique (hord l hl) (hord r hr) (hprime l hl) (hprime r hr) he
  have heq : (∑ d ∈ S.image List.prod, a (k / d)) = ∑ l ∈ S, a (k / l.prod) :=
    Finset.sum_image hinj
  rw [← heq]
  apply restricted_divisor_coeff hB a ha hk
  intro d hd
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hd
  exact Nat.mem_divisors.mpr ⟨hdiv l hl, hk.ne'⟩

example : ‖∑ _l ∈ ({[3, 2], [2]} : Finset (List ℕ)), (1 : ℂ)‖ ≤ tau 6 ^ ((0 : ℝ) + 1) := by
  simpa using prime_chain_coeff (B := 0) (by norm_num) (fun _ => (1 : ℂ))
    (by intro n; simp) (k := 6) (by norm_num) ({[3, 2], [2]} : Finset (List ℕ))
    (by intro l hl; simp only [Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl <;> norm_num)
    (by intro l hl; simp only [Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl <;> norm_num)
    (by intro l hl; simp only [Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl <;> norm_num)

/-- Pages 29 and 31, the elementary depth bound for repeated Buchstab steps. -/
theorem buchstab_depth {ι : Type*} (S : Finset ι) (p : ι → ℝ) {x : ℝ}
    (hx : 1 < x) (hp : ∀ i ∈ S, wof x ≤ p i)
    (hprod : ∏ i ∈ S, p i ≤ x ^ (0.4 : ℝ)) :
    (S.card : ℝ) ≤ (0.4 : ℝ) * Real.log x ^ (0.1 : ℝ) := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have hw : 0 < wof x := Real.exp_pos _
  have hlower : wof x ^ S.card ≤ ∏ i ∈ S, p i := by
    simpa using Finset.prod_le_prod₀ (fun i (_ : i ∈ S) => hw.le) hp
  have hlog := Real.log_le_log (pow_pos hw _) (hlower.trans hprod)
  rw [Real.log_pow, Real.log_rpow (by linarith : 0 < x)] at hlog
  simp only [wof, Real.log_exp] at hlog
  have hid : Real.log x ^ (0.1 : ℝ) * Real.log x ^ (0.9 : ℝ) = Real.log x := by
    rw [← Real.rpow_add hl]
    norm_num
  have hpos : 0 < Real.log x ^ (0.9 : ℝ) := Real.rpow_pos_of_pos hl _
  have hn : (S.card : ℝ) * Real.log x ^ (0.9 : ℝ) ≤
      ((0.4 : ℝ) * Real.log x ^ (0.1 : ℝ)) * Real.log x ^ (0.9 : ℝ) := by
    norm_num at hlog
    nlinarith [hid]
  exact (mul_le_mul_iff_left₀ hpos).mp (by simpa [mul_comm] using hn)

example : (1 : ℝ) ≤ 0.4 * Real.log (Real.exp 59049) ^ (0.1 : ℝ) := by
  have hpow : (59049 : ℝ) ^ (9 / 10 : ℝ) = 19683 := by
    rw [show (59049 : ℝ) = 3 ^ (10 : ℝ) by norm_num,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  have hp : wof (Real.exp 59049) ≤ (Real.exp 59049) ^ (0.4 : ℝ) := by
    rw [wof, Real.log_exp, hpow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    exact Real.exp_le_exp.mpr (by norm_num)
  simpa using buchstab_depth (x := Real.exp 59049) ({0} : Finset ℕ) (fun _ => wof (Real.exp 59049))
    (by exact Real.one_lt_exp_iff.mpr (by norm_num))
    (by intro i hi; rfl) (by simpa using hp)

/-- Page 31 repeated 4.14, stopping when the grouped variable exceeds x to 0.4.
At n zero it returns the original indicator. Each recursive cofactor is smaller. -/
def buchstabTree (x w z : ℝ) (u n : ℕ) : ℂ :=
  if _hn : n = 0 then psi n z
  else if x ^ (0.4 : ℝ) < (u : ℝ) then psi n z
  else psi n w -
    ∑ p ∈ ((n.primeFactors.filter
      (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z)).attach),
      buchstabTree x w (p.val : ℝ) (u * p.val) (n / p.val)
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero _hn)
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp p.property).1).one_lt

/-- Page 31 the terminating repeated Buchstab computation preserves the indicator
exactly. This is finite algebra and asserts no short interval error estimate. -/
theorem buchstabTree_eq (x w z : ℝ) (u n : ℕ) (hwz : w ≤ z) :
    buchstabTree x w z u n = psi n z := by
  induction n using Nat.strong_induction_on generalizing u z with
  | h n ih =>
    rw [buchstabTree]
    split_ifs with hn hu
    · rfl
    · rfl
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hs :
          (∑ p ∈ ((n.primeFactors.filter
            (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z)).attach),
            buchstabTree x w (p.val : ℝ) (u * p.val) (n / p.val)) =
          ∑ p ∈ n.primeFactors.filter
            (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z), psi (n / p) (p : ℝ) := by
        calc
          _ = ∑ p ∈ ((n.primeFactors.filter
              (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z)).attach),
              psi (n / p.val) (p.val : ℝ) := by
            apply Finset.sum_congr rfl
            intro p hp
            exact ih _ (Nat.div_lt_self hnpos
              (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp p.property).1).one_lt)
              _ _ (Finset.mem_filter.mp p.property).2.1
          _ = _ := by
            simpa using (Finset.sum_attach
              (n.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z))
              (fun p : ℕ => psi (n / p) (p : ℝ)))
      rw [hs]
      exact (buchstab_identity hnpos hwz).symm

example : buchstabTree 1 2 7 1 30 = psi 30 7 :=
  buchstabTree_eq 1 2 7 1 30 (by norm_num)

/-- Page 28 after 4.16 and page 31: the dependent rough cutoff cannot in general
be replaced by a single rough indicator after grouping. This diagnoses a shortcut,
not the Perron argument printed in the paper. The p = 2 and q = 3 instance occurs at u = 6. -/
theorem varying_cutoff_not_single {p q : ℕ} (hp : p.Prime) (hpq : p < q) :
    ¬ ∃ (c : ℂ) (z : ℝ), ∀ h : ℕ, psi h (p : ℝ) + psi h (q : ℝ) = c * psi h z := by
  have h1 : ∀ z : ℝ, psi 1 z = 1 := by
    intro z
    have hr : Rough 1 z := fun p hp _ hd => hp.not_dvd_one hd
    simp [psi, hr]
  have hpp : psi p (p : ℝ) = 1 := by
    simp [psi, rough_iff_le_minFac hp.ne_one, hp.minFac_eq]
  have hpq' : psi p (q : ℝ) = 0 := by
    simp [psi, rough_iff_le_minFac hp.ne_one, hp.minFac_eq,
      not_le.mpr (show (p : ℝ) < q by exact_mod_cast hpq)]
  rintro ⟨c, z, h⟩
  have hc := (h 1).symm
  norm_num [h1] at hc
  have hh := h p
  rw [hpp, hpq', hc] at hh
  unfold psi at hh
  split_ifs at hh <;> norm_num at hh

example : ¬ ∃ (c : ℂ) (z : ℝ), ∀ h : ℕ, psi h 2 + psi h 3 = c * psi h z :=
  varying_cutoff_not_single (by norm_num : Nat.Prime 2) (by norm_num : (2 : ℕ) < 3)

example (h : ℕ) :
    (∑ p ∈ ({2, 3} : Finset ℕ), (1 : ℂ) * psi h (p : ℝ)) = psi h 2 + psi h 3 := by
  norm_num

/-- Pages 27 and 31, retain the full correction when replacing the dependent
prime cutoff by a common cutoff in one grouped coefficient. -/
theorem grouped_cutoff_expansion (S : Finset ℕ) (a : ℕ → ℂ) {h : ℕ}
    (hh : 0 < h) (w : ℝ) (hw : ∀ p ∈ S, w ≤ (p : ℝ)) :
    (∑ p ∈ S, a p * psi h (p : ℝ)) =
      (∑ p ∈ S, a p) * psi h w -
        ∑ p ∈ S, a p * ∑ q ∈ h.primeFactors.filter
          (fun q : ℕ => w ≤ (q : ℝ) ∧ (q : ℝ) < p), psi (h / q) (q : ℝ) := by
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [buchstab_identity hh (hw p hp)]
  ring

example (a : ℕ → ℂ) :
    (∑ p ∈ ({2, 3} : Finset ℕ), a p * psi 6 (p : ℝ)) =
      (∑ p ∈ ({2, 3} : Finset ℕ), a p) * psi 6 2 -
        ∑ p ∈ ({2, 3} : Finset ℕ), a p * ∑ q ∈ (6 : ℕ).primeFactors.filter
          (fun q : ℕ => (2 : ℝ) ≤ q ∧ (q : ℝ) < p), psi (6 / q) (q : ℝ) := by
  apply grouped_cutoff_expansion _ _ (by norm_num)
  intro p hp
  norm_num at hp
  rcases hp with rfl | rfl <;> norm_num

/-- Page 31 grouping u = mp, with p fixed and the original m interval retained. -/
def primeGroupedCoeff (a : ℕ → ℂ) (M : ℝ) (p u : ℕ) : ℂ :=
  if 0 < u ∧ p ∣ u ∧ u / p ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊ then a (u / p) else 0

/-- Pages 29 and 31, grouping with one fixed prime preserves the divisor exponent. -/
theorem primeGroupedCoeff_bound {B : ℝ} (hB : 0 ≤ B) (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ tau n ^ B) (M : ℝ) (p u : ℕ) :
    ‖primeGroupedCoeff a M p u‖ ≤ tau u ^ B := by
  unfold primeGroupedCoeff
  split_ifs with h
  · have hdiv : u / p ∣ u := Nat.div_dvd_of_dvd h.2.1
    have htau : tau (u / p) ≤ tau u := by
      simp only [tau, sigma_zero_apply]
      exact_mod_cast card_le_card (Nat.divisors_subset_of_dvd h.1.ne' hdiv)
    exact (ha _).trans (Real.rpow_le_rpow (by simp [tau]) htau hB)
  · simpa using Real.rpow_nonneg (by simp [tau] : 0 ≤ tau u) B

/-- Page 31 fixed prime blocks are covered by Lemma13 once their grouped lengths
and independent cutoff meet 4.18. CONDITIONAL ON the explicit Lemma13 input.
This does not sum over primes or remove the varying cutoff. -/
theorem lemma13_prime_block (h13 : Lemma13) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M U N : ℝ → ℝ) (p : ℝ → ℕ),
      0 ≤ B → (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      (Ev (fun x => x ^ (0.4 : ℝ) ≤ U x ∧ U x ≤ x ^ (0.46 : ℝ) ∧
        N x ≤ x ^ (0.46 : ℝ)) ∧ LL (fun x => (p x : ℝ)) (fun x => x / (U x * N x))) →
      Holds42 ε fun x k => conv2 (primeGroupedCoeff (a x) (M x) (p x)) (b x)
        (U x) (N x) (p x : ℝ) k := by
  obtain ⟨ε0, hε0, h13⟩ := h13
  refine ⟨ε0, hε0, ?_⟩
  intro ε hε hsmall B a b M U N p hB ha hb hcond
  exact h13 ε hε hsmall B (fun x => primeGroupedCoeff (a x) (M x) (p x)) b
    U N (fun x => (p x : ℝ)) (fun x k => primeGroupedCoeff_bound hB (a x) (ha x) _ _ _) hb hcond

example :
    (∀ _x : ℝ, ∀ k : ℕ, ‖(1 : ℂ)‖ ≤ tau k ^ (0 : ℝ)) ∧
    (Ev (fun x : ℝ => x ^ (0.4 : ℝ) ≤ x ^ (0.4 : ℝ) ∧
      x ^ (0.4 : ℝ) ≤ x ^ (0.46 : ℝ) ∧ (1 : ℝ) ≤ x ^ (0.46 : ℝ))) ∧
    LL (fun _ : ℝ => (2 : ℝ)) (fun x => x / (x ^ (0.4 : ℝ) * 1)) := by
  refine ⟨by intro x k; simp, ⟨1, ?_⟩, ?_⟩
  · intro x hx
    exact ⟨le_rfl, Real.rpow_le_rpow_of_exponent_le hx (by norm_num),
      Real.one_le_rpow hx (by norm_num)⟩
  · refine ⟨1, by norm_num, 4, ?_⟩
    intro x hx
    have hx0 : 0 < x := by linarith
    have hx1 : 1 ≤ x := by linarith
    have hid : x / (x ^ (0.4 : ℝ) * 1) = x ^ (0.6 : ℝ) := by
      rw [mul_one]
      nth_rw 1 [← Real.rpow_one x]
      rw [← Real.rpow_sub hx0]
      norm_num
    change 1 * 2 ≤ x / (x ^ (0.4 : ℝ) * 1)
    rw [hid, one_mul]
    have h4 : (4 : ℝ) ^ (0.5 : ℝ) = 2 := by
      rw [show (0.5 : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
      norm_num
    calc
      2 = (4 : ℝ) ^ (0.5 : ℝ) := h4.symm
      _ ≤ x ^ (0.5 : ℝ) := Real.rpow_le_rpow (by norm_num) hx (by norm_num)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)

example : primeGroupedCoeff (fun _ => 1) (1 / 2) 2 2 = 1 := by
  norm_num [primeGroupedCoeff]

/-- Pages 12 and 31, strict Theorem4 margins with room for dyadic constants.
The extra epsilon divided by six is implementation slack, not a printed constant. -/
theorem large_block_exponents {ε α1 α2 : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 100)
    (hdiff : |α1 - α2| ≤ 0.1 + ε / 6) (hcofactor : 1 - (α1 + α2) ≤ 0.18 + ε / 6) :
    1 / 2 + ε < 0.55 + 2 * ε / 3 ∧ (0.55 + 2 * ε / 3 : ℝ) < 7 / 12 ∧
    |α1 - α2| < 2 * (0.55 + 2 * ε / 3) - 1 - ε ∧
    1 - (α1 + α2) < gam (0.55 + 2 * ε / 3) - ε := by
  refine ⟨by linarith, by linarith, by linarith, ?_⟩
  unfold gam
  have h1 : 1 - (α1 + α2) + ε < 4 * (0.55 + 2 * ε / 3) - 2 := by linarith
  have h2 : 1 - (α1 + α2) + ε < (20 * (0.55 + 2 * ε / 3) - 9) / 11 := by linarith
  have h3 : 1 - (α1 + α2) + ε < (72 * (0.55 + 2 * ε / 3) - 37) / 11 := by linarith
  have := lt_min h1 (lt_min h2 h3)
  linarith

/-- Page 31 application of Theorem4 for a fixed pair of length exponents.
CONDITIONAL ON the explicit Theorem4 hypothesis and the supplied Cond32 estimate.
The conclusion is a polynomial norm estimate, not a coefficient transfer. -/
theorem theorem4_large_block (h4 : Theorem4) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∀ α1 α2 : ℝ, |α1 - α2| ≤ 0.1 + ε / 6 → 1 - (α1 + α2) ≤ 0.18 + ε / 6 →
    ∀ (B c1 c2 : ℝ) (M N Lp : ℝ → DP) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
      FamOK (fun x => [M x, N x, Lp x])
        [fun x => x ^ α1, fun x => x ^ α2, fun x => x ^ (1 - α1 - α2)] B c1 c2 →
      (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) * c.T = x ^ (1 - (0.55 + 2 * ε / 3))) →
      Cond32 Lp (fun x => x ^ (1 - α1 - α2)) 𝒮 →
      Concl39 (fun x => [M x, N x, Lp x]) 𝒮 := by
  obtain ⟨ε0, h0, h4⟩ := h4
  refine ⟨min ε0 (1 / 100), lt_min h0 (by norm_num), ?_⟩
  intro ε hε hsmall α1 α2 hdiff hcofactor B c1 c2 M N Lp 𝒮 hc1 hc2 hFam hCfg h32
  have hnum := large_block_exponents hε (hsmall.trans_le (min_le_right _ _)) hdiff hcofactor
  exact h4 ε hε (hsmall.trans_le (min_le_left _ _)) _ _ _
    hnum.1 hnum.2.1 hnum.2.2.1 hnum.2.2.2 B c1 c2 M N Lp 𝒮 hc1 hc2 hFam hCfg h32

example : 1 / 2 + (1 / 200 : ℝ) < 0.55 + 2 * (1 / 200 : ℝ) / 3 ∧
    (0.55 + 2 * (1 / 200 : ℝ) / 3) < 7 / 12 ∧
    |(0.41 : ℝ) - 0.41| < 2 * (0.55 + 2 * (1 / 200 : ℝ) / 3) - 1 - 1 / 200 ∧
    1 - ((0.41 : ℝ) + 0.41) < gam (0.55 + 2 * (1 / 200 : ℝ) / 3) - 1 / 200 :=
  large_block_exponents (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example :
    ∃ (P : ℝ → DP) (𝒮 : ℝ → Set Cfg),
      FamOK (fun x => [P x, P x, P x])
        [fun x => x ^ (0.41 : ℝ), fun x => x ^ (0.41 : ℝ),
          fun x => x ^ (1 - (0.41 : ℝ) - 0.41)] 0 1 2 ∧
      (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧
        (c.q : ℝ) * c.T = x ^ (1 - (0.55 + 2 * (1 / 200 : ℝ) / 3))) ∧
      Cond32 P (fun x => x ^ (1 - (0.41 : ℝ) - 0.41)) 𝒮 ∧
      (𝒮 256).Nonempty := by
  let P : ℝ → DP := fun _ => ⟨fun _ => 0, ∅⟩
  let θ : ℝ := 0.55 + 2 * (1 / 200 : ℝ) / 3
  let T : ℝ := (256 : ℝ) ^ (1 - θ)
  have hquarter : (256 : ℝ) ^ (1 / 4 : ℝ) = 4 := by
    rw [show (256 : ℝ) = 4 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hhalf : (256 : ℝ) ^ (1 / 2 : ℝ) = 16 := by
    rw [show (256 : ℝ) = 16 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hTlo : 4 ≤ T := by
    rw [← hquarter]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num [θ])
  have hThi : T ≤ 16 := by
    rw [← hhalf]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num [θ])
  let c : Cfg := ⟨1, T, {(T, 1)}⟩
  let 𝒮 : ℝ → Set Cfg := fun x => if x = 256 then {c} else ∅
  have hstd : c.Std 256 := by
    refine ⟨?_, by norm_num [c], by norm_num [c], ?_, ?_⟩
    · intro e he
      have heq : e = (T, 1) := Finset.mem_singleton.mp he
      subst e
      refine ⟨?_, ?_⟩
      · dsimp [c]
        rw [abs_of_nonneg (by linarith : 0 ≤ T)]
      · intro e' he' _ hne
        exact False.elim (hne (Finset.mem_singleton.mp he').symm)
    · dsimp [c]; linarith
    · dsimp [c]; linarith
  refine ⟨P, 𝒮, ?_, ?_, ?_, ?_⟩
  · intro x
    refine ⟨rfl, ?_⟩
    intro i hi hi'
    have hi3 : i < 3 := by simpa using hi
    interval_cases i <;> simp [P, DP.HasLen, DP.Coef31]
  · intro x c' hc'
    by_cases hx : x = 256
    · subst x
      have hcc : c' = c := by simpa [𝒮] using hc'
      subst c'
      exact ⟨hstd, by simp [c, T, θ]⟩
    · simp [𝒮, hx] at hc'
  · intro A hA
    refine ⟨0, 0, ?_⟩
    intro x hx c' hc' e he
    simp [P, DP.eval]
  · exact ⟨c, by simp [𝒮]⟩

/-- Page 31 grouping u = mp with the original m support retained exactly. -/
theorem restricted_prime_divisor_regroup {L : ℕ} (hL : 0 < L) (S : Finset ℕ)
    (F : ℕ → ℕ → ℕ → ℂ) :
    (∑ m ∈ S, if m ∣ L then ∑ p ∈ (L / m).primeFactors, F m p (L / m / p) else 0) =
      ∑ u ∈ L.divisors, ∑ p ∈ u.primeFactors,
        if u / p ∈ S then F (u / p) p (L / u) else 0 := by
  have heq :
      (∑ m ∈ S, if m ∣ L then ∑ p ∈ (L / m).primeFactors, F m p (L / m / p) else 0) =
      ∑ m ∈ L.divisors, if m ∈ S then ∑ p ∈ (L / m).primeFactors, F m p (L / m / p) else 0 := by
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    congr 1
    ext m
    simp [Nat.mem_divisors, hL.ne', and_comm]
  rw [heq]
  have hs := prime_divisor_regroup hL (fun m p h => if m ∈ S then F m p h else 0)
  convert hs using 1
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hms : m ∈ S <;> simp [hms]

example :
    (∑ m ∈ ({2, 3} : Finset ℕ),
      if m ∣ 12 then ∑ _p ∈ (12 / m).primeFactors, (1 : ℂ) else 0) =
      ∑ u ∈ (12 : ℕ).divisors, ∑ p ∈ u.primeFactors,
        if u / p ∈ ({2, 3} : Finset ℕ) then (1 : ℂ) else 0 := by
  simpa using restricted_prime_divisor_regroup (L := 12) (by norm_num) ({2, 3} : Finset ℕ)
    (fun _ _ _ => (1 : ℂ))

/-- Page 31 exact regrouping of a restricted prime error, including both original
coefficient supports, divisibility, the prime interval and its dependent cutoff. -/
theorem restricted_prime_error_regroup {k : ℕ} (hk : 0 < k) (S T : Finset ℕ)
    (a b : ℕ → ℂ) (w z : ℝ) (R : ℕ → ℕ → Prop) :
    (∑ m ∈ S, ∑ n ∈ T, if m * n ∣ k then a m * b n *
      ∑ p ∈ ((k / (m * n)).primeFactors.filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z)).filter (fun p => R m p),
          psi (k / (m * n) / p) (p : ℝ) else 0) =
    ∑ n ∈ T, if n ∣ k then ∑ u ∈ (k / n).divisors, ∑ p ∈ u.primeFactors,
      if u / p ∈ S ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z ∧ R (u / p) p then
        a (u / p) * b n * psi (k / n / u) (p : ℝ) else 0 else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hnk : n ∣ k
  · simp only [hnk, ite_true]
    have hnpos : 0 < n := Nat.pos_of_dvd_of_pos hnk hk
    have hL : 0 < k / n := Nat.div_pos (Nat.le_of_dvd hk hnk) hnpos
    have hd (m : ℕ) : m * n ∣ k ↔ m ∣ k / n := by
      rw [Nat.dvd_div_iff_mul_dvd hnk, mul_comm]
    have heq :
        (∑ m ∈ S, if m * n ∣ k then a m * b n *
          ∑ p ∈ ((k / (m * n)).primeFactors.filter
            (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z)).filter (fun p => R m p),
              psi (k / (m * n) / p) (p : ℝ) else 0) =
        ∑ m ∈ S, if m ∣ k / n then ∑ p ∈ (k / n / m).primeFactors,
          if w ≤ (p : ℝ) ∧ (p : ℝ) < z ∧ R m p then
            a m * b n * psi (k / n / m / p) (p : ℝ) else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [hd]
      by_cases hmd : m ∣ k / n
      · simp only [hmd, ite_true]
        have hdiv : k / (m * n) = k / n / m := by
          rw [Nat.div_div_eq_div_mul, mul_comm]
        rw [hdiv]
        simp only [Finset.filter_filter, Finset.sum_filter, Finset.mul_sum, mul_ite,
          mul_zero, and_assoc]
      · simp [hmd]
    rw [heq, restricted_prime_divisor_regroup hL S
      (fun m p h => if w ≤ (p : ℝ) ∧ (p : ℝ) < z ∧ R m p then
        a m * b n * psi h (p : ℝ) else 0)]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hs : u / p ∈ S <;> simp [hs]
  · simp only [hnk, ite_false]
    apply Finset.sum_eq_zero
    intro m hm
    have hd : ¬ m * n ∣ k := fun h => hnk ((dvd_mul_left n m).trans h)
    simp [hd]

example : ∃ lhs rhs : ℂ, lhs = rhs := by
  exact ⟨_, _, restricted_prime_error_regroup (k := 12) (by norm_num)
    ({1, 2} : Finset ℕ) ({1, 2} : Finset ℕ) (fun _ => 1) (fun _ => 1) 2 7
    (fun _ _ => True)⟩

example : (2 : ℕ) ∈ (((12 : ℕ).primeFactors.filter
    (fun p : ℕ => (2 : ℝ) ≤ p ∧ (p : ℝ) < 7)).filter (fun _ => True)) := by
  norm_num [Nat.mem_primeFactors]

/-- Pages 12 and 31, the dyadic factor two can be absorbed uniformly into the
strict Theorem4 exponent margins. This is only the numerical input to that theorem. -/
theorem large_power_block_parameters {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 100) :
    Ev fun x => ∀ α1 α2 : ℝ,
      x ^ α1 / x ^ α2 ≤ 2 * x ^ (0.1 : ℝ) →
      x ^ α2 / x ^ α1 ≤ 2 * x ^ (0.1 : ℝ) →
      x ^ (1 - α1 - α2) ≤ 2 * x ^ (0.18 : ℝ) →
      1 / 2 + ε < 0.55 + 2 * ε / 3 ∧ (0.55 + 2 * ε / 3 : ℝ) < 7 / 12 ∧
      |α1 - α2| < 2 * (0.55 + 2 * ε / 3) - 1 - ε ∧
      1 - (α1 + α2) < gam (0.55 + 2 * ε / 3) - ε := by
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (by linarith : 0 < ε / 6)).eventually_ge_atTop 2)
  refine ⟨max 2 X, ?_⟩
  intro x hx α1 α2 h12 h21 hH
  have hx1 : 1 < x := by linarith [le_trans (le_max_left 2 X) hx]
  have hx0 : 0 < x := by linarith
  have h2 : 2 ≤ x ^ (ε / 6) := hX x ((le_max_right _ _).trans hx)
  have hquot : ∀ u v b : ℝ, x ^ u / x ^ v ≤ 2 * x ^ b → u - v ≤ b + ε / 6 := by
    intro u v b hb
    have hp : x ^ (u - v) ≤ x ^ (b + ε / 6) := by
      calc
        _ = x ^ u / x ^ v := Real.rpow_sub hx0 _ _
        _ ≤ 2 * x ^ b := hb
        _ ≤ _ := by
          rw [Real.rpow_add hx0]
          nlinarith [mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hx0.le b)]
    exact (Real.rpow_le_rpow_left_iff hx1).mp hp
  have hdiff : |α1 - α2| ≤ 0.1 + ε / 6 := by
    apply abs_le.mpr
    exact ⟨by linarith [hquot α2 α1 0.1 h21], hquot α1 α2 0.1 h12⟩
  have hcofactor : 1 - (α1 + α2) ≤ 0.18 + ε / 6 := by
    have := hquot (1 - α1 - α2) 0 0.18 (by simpa using hH)
    linarith
  exact large_block_exponents hε hsmall hdiff hcofactor

example : Ev fun x => ∀ α1 α2 : ℝ,
    x ^ α1 / x ^ α2 ≤ 2 * x ^ (0.1 : ℝ) →
    x ^ α2 / x ^ α1 ≤ 2 * x ^ (0.1 : ℝ) →
    x ^ (1 - α1 - α2) ≤ 2 * x ^ (0.18 : ℝ) →
    1 / 2 + (1 / 200 : ℝ) < 0.55 + 2 * (1 / 200 : ℝ) / 3 ∧
      (0.55 + 2 * (1 / 200 : ℝ) / 3) < 7 / 12 ∧
      |α1 - α2| < 2 * (0.55 + 2 * (1 / 200 : ℝ) / 3) - 1 - 1 / 200 ∧
      1 - (α1 + α2) < gam (0.55 + 2 * (1 / 200 : ℝ) / 3) - 1 / 200 :=
  large_power_block_parameters (by norm_num) (by norm_num)

example {x : ℝ} (hx : 1 ≤ x) :
    x ^ (0.41 : ℝ) / x ^ (0.41 : ℝ) ≤ 2 * x ^ (0.1 : ℝ) ∧
    x ^ (0.41 : ℝ) / x ^ (0.41 : ℝ) ≤ 2 * x ^ (0.1 : ℝ) ∧
    x ^ (1 - (0.41 : ℝ) - 0.41) ≤ 2 * x ^ (0.18 : ℝ) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hp0 : 0 < x ^ (0.41 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hp1 : 1 ≤ x ^ (0.1 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have he : 1 - (0.41 : ℝ) - 0.41 = 0.18 := by norm_num
  rw [he]
  simp only [div_self hp0.ne']
  exact ⟨by linarith, by linarith, by nlinarith [Real.rpow_nonneg hx0.le (0.18 : ℝ)]⟩

/-- Pages 11 and 29, a real divisor exponent can be enlarged to a nonnegative one,
including the convention tau zero equals zero. -/
theorem tau_rpow_enlarge (B : ℝ) (n : ℕ) : tau n ^ B ≤ tau n ^ max B 0 := by
  by_cases hn : n = 0
  · subst n
    have ht : tau 0 = 0 := by simp [tau]
    rw [ht]
    by_cases hB : B = 0
    · simp [hB]
    · rw [Real.zero_rpow hB]
      positivity
  · have ht : 1 ≤ tau n := by
      simp only [tau, sigma_zero_apply]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Finset.card_ne_zero.mpr ⟨1, Nat.one_mem_divisors.mpr hn⟩)
    exact Real.rpow_le_rpow_of_exponent_le ht (le_max_left _ _)

/-- Page 31 conditional fixed prime transfer for every real input exponent.
Enlarge B to max B zero before using the divisor coefficient bound.
CONDITIONAL ON the explicit Lemma13 input. -/
theorem lemma13_prime_block_real (h13 : Lemma13) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M U N : ℝ → ℝ) (p : ℝ → ℕ),
      (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      (Ev (fun x => x ^ (0.4 : ℝ) ≤ U x ∧ U x ≤ x ^ (0.46 : ℝ) ∧
        N x ≤ x ^ (0.46 : ℝ)) ∧ LL (fun x => (p x : ℝ)) (fun x => x / (U x * N x))) →
      Holds42 ε fun x k => conv2 (primeGroupedCoeff (a x) (M x) (p x)) (b x)
        (U x) (N x) (p x : ℝ) k := by
  obtain ⟨ε0, h0, h⟩ := lemma13_prime_block h13
  refine ⟨ε0, h0, ?_⟩
  intro ε hε hsmall B a b M U N p ha hb hcond
  apply h ε hε hsmall (max B 0) a b M U N p (le_max_right _ _)
  · intro x k
    exact (ha x k).trans (tau_rpow_enlarge B k)
  · intro x k
    exact (hb x k).trans (tau_rpow_enlarge B k)
  · exact hcond

example : tau 0 ^ (-1 : ℝ) ≤ tau 0 ^ max (-1 : ℝ) 0 := tau_rpow_enlarge (-1) 0
example : tau 6 ^ (-1 : ℝ) ≤ tau 6 ^ max (-1 : ℝ) 0 := tau_rpow_enlarge (-1) 6

example : ∀ _x : ℝ, ∀ k : ℕ,
    ‖((tau k ^ (-1 : ℝ) : ℝ) : ℂ)‖ ≤ tau k ^ (-1 : ℝ) := by
  intro x k
  rw [Complex.norm_of_nonneg (Real.rpow_nonneg (by simp [tau] : 0 ≤ tau k) _)]

#print axioms dyadic_order
#print axioms dyadic_large_cofactor
#print axioms dyadic_large_ratios

#print axioms prime_divisor_regroup

#print axioms restricted_divisor_coeff
#print axioms prime_subset_coeff

#print axioms prime_chain_unique

#print axioms prime_chain_coeff

#print axioms buchstab_depth

#print axioms buchstabTree
#print axioms buchstabTree_eq

#print axioms varying_cutoff_not_single

#print axioms grouped_cutoff_expansion

#print axioms primeGroupedCoeff
#print axioms primeGroupedCoeff_bound
#print axioms lemma13_prime_block

#print axioms large_block_exponents
#print axioms theorem4_large_block

#print axioms restricted_prime_divisor_regroup

#print axioms restricted_prime_error_regroup

#print axioms large_power_block_parameters

#print axioms tau_rpow_enlarge
#print axioms lemma13_prime_block_real

end LeanLab.BakerHarmanPintz1997.Decomp546a
