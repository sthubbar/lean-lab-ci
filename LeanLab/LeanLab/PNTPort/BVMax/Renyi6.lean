import LeanLab.PNTPort.BVMax.Renyi7R

/-!
# Rényi's theorem with `K = 6`: Richert's logarithmic weights with three upper sieve levels

Unit U-6779, CLOUD 20261020T2317Z-cloud53. AI wrote the Lean code. Known mathematics, Richert's
logarithmic weights, Richert 1969, on top of the lab's block sieve; Pan K = 4 and Chen 1973 K = 2
are far stronger.

The weight of `a` is `1 - Σ_{q ∈ Q, q ∣ a} f(q)` with `f(q) = (23/61)(1 - log q/log y)`,
`Q` the primes `q ∤ N` in `(z, y]`, `z = N^{1/21}`, `y = N^{0.23}`. An element `a < N` with
`Ω(a) ≥ 7`, all prime factors above `z` and no square of a prime of `Q` has
`Σ_{q ∣ a} (1 - log q/log y) ≥ Ω(a) - log a/log y ≥ 7 - 100/23 = 61/23`, `omega_split_prod`, so
its weight is at most `0`. The middle primes are cut at `N^{0.101}` and `N^{0.165}` into three
groups with upper sieve levels `w = N^{0.03788}`, `N^{0.03165}`, `N^{0.02532}`; `xDen_geom_w` is
the lab's block Mertens bound with the weight `1 - log p/T`, piece by piece. The numbers,
`numerics/renyi7_design.py` and its output:

* weighted Mertens sums `≤ 0.52606, 0.21695, 0.05120`, pieces of ratio `1.01`;
* `Σ_{w_j < p ≤ z} 1/(p - 1) ≤ 0.230046, 0.410082, 0.635127`, pieces of ratio `1.005`;
* subtracted part `≤ 0.3194 + 0.1719 + 0.0656 = 0.5569` of `X V_z` against `0.6168`.

Binary Goldbach is `Ω(m) = 1` and stays OPEN.
-/

namespace LeanLab.PNTPort.BVMax

open Finset LeanLab.PNTSieve.Bonferroni

/-- **Splitting off the middle primes**, product form. -/
lemma omega_split_prod (a : ℕ) (ha : a ≠ 0) (D : Finset ℕ) (hD : ∀ q ∈ D, q.Prime ∧ q ∣ a)
    (hsq : ∀ q ∈ D, ¬ q ^ 2 ∣ a) (Y : ℕ) (hsmall : ∀ r, r.Prime → r ∣ a → r ≤ Y → r ∈ D) :
    D.card ≤ ArithmeticFunction.cardFactors a ∧
    (∏ q ∈ D, q) * (Y + 1) ^ (ArithmeticFunction.cardFactors a - D.card) ≤ a := by
  classical
  have hgd : (∏ q ∈ D, q) ∣ a :=
    Finset.prod_primes_dvd a (fun q hq => (hD q hq).1.prime) (fun q hq => (hD q hq).2)
  obtain ⟨h, hh⟩ := hgd
  set g := ∏ q ∈ D, q with hg
  have hg0 : g ≠ 0 := by rw [hh] at ha; exact left_ne_zero_of_mul ha
  have hh0 : h ≠ 0 := by rw [hh] at ha; exact right_ne_zero_of_mul ha
  have hΩ : ArithmeticFunction.cardFactors a = D.card + ArithmeticFunction.cardFactors h := by
    rw [hh, ArithmeticFunction.cardFactors_mul hg0 hh0, hg,
      cardFactors_prod_primes D (fun q hq => (hD q hq).1)]
  have hbig : ∀ r ∈ h.primeFactorsList, Y + 1 ≤ r := by
    intro r hr
    have hrp := Nat.prime_of_mem_primeFactorsList hr
    have hrd := Nat.dvd_of_mem_primeFactorsList hr
    by_contra hlt
    push Not at hlt
    have hra : r ∣ a := by rw [hh]; exact dvd_mul_of_dvd_right hrd g
    have hrD := hsmall r hrp hra (by omega)
    have hrg : r ∣ g := Finset.dvd_prod_of_mem _ hrD
    exact hsq r hrD (by rw [hh, pow_two]; exact mul_dvd_mul hrg hrd)
  have h1 := pow_bigOmega_le h (Y + 1) hh0 hbig
  rw [hΩ, Nat.add_sub_cancel_left, hh]
  exact ⟨Nat.le_add_right _ _, Nat.mul_le_mul le_rfl h1⟩

/-- **The lab's block Mertens bound with the weight `1 - log p/T`**, pieces of equal log ratio. -/
lemma xDen_geom_w (ℓ c r T : ℝ) (hc : 0 < c) (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (hcl : 10 ^ 20 ≤ c * ℓ)
    (hT : 0 < T) : ∀ n : ℕ, (∀ k < n, c * r ^ k * ℓ ≤ T) → ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime ∧ ⌊Real.exp (c * ℓ)⌋₊ < p ∧ p ≤ ⌊Real.exp (c * r ^ n * ℓ)⌋₊) →
      ∑ p ∈ S, xDen p * (1 - Real.log p / T) ≤
        (r - 1 + 1 / 10 ^ 6) * ∑ k ∈ range n, (1 - c * r ^ k * ℓ / T)
  | 0, _, S, hS => by
    have hF : ∀ p ∈ S, False := fun p hp => by
      obtain ⟨-, h1, h2⟩ := hS p hp
      rw [pow_zero, mul_one] at h2
      omega
    rw [sum_eq_zero (fun p hp => (hF p hp).elim)]
    simp
  | n + 1, hk, S, hS => by
    have hl : 0 ≤ c * ℓ := le_trans (by positivity) hcl
    have hrn : (1 : ℝ) ≤ r ^ n := one_le_pow₀ hr1
    have hcn : c * ℓ ≤ c * r ^ n * ℓ := by
      have := mul_le_mul_of_nonneg_left hrn hl
      linarith
    have hMT : c * r ^ n * ℓ ≤ T := hk n (by omega)
    have hM20 : 10 ^ 20 ≤ c * r ^ n * ℓ := le_trans hcl hcn
    rw [← sum_filter_add_sum_filter_not S (fun p => p ≤ ⌊Real.exp (c * r ^ n * ℓ)⌋₊)]
    have hA := xDen_geom_w ℓ c r T hc hr1 hr2 hcl hT n (fun k hkn => hk k (by omega))
      (S.filter (fun p => p ≤ ⌊Real.exp (c * r ^ n * ℓ)⌋₊)) (fun p hp => by
        obtain ⟨hp, hpa⟩ := mem_filter.mp hp
        obtain ⟨h1, h2, -⟩ := hS p hp
        exact ⟨h1, h2, hpa⟩)
    have hB := xDen_geom ℓ (c * r ^ n) r (by positivity) hr1 hr2 hM20 1
      (S.filter (fun p => ¬ p ≤ ⌊Real.exp (c * r ^ n * ℓ)⌋₊)) (fun p hp => by
        obtain ⟨hp, hpa⟩ := mem_filter.mp hp
        obtain ⟨h1, -, h3⟩ := hS p hp
        have e : c * r ^ n * r ^ 1 * ℓ = c * r ^ (n + 1) * ℓ := by ring
        rw [e]
        exact ⟨h1, by omega, h3⟩)
    simp only [Nat.cast_one, one_mul] at hB
    have hw0 : 0 ≤ 1 - c * r ^ n * ℓ / T := by
      rw [sub_nonneg, div_le_one hT]; exact hMT
    have hlast : ∑ p ∈ S.filter (fun p => ¬ p ≤ ⌊Real.exp (c * r ^ n * ℓ)⌋₊),
        xDen p * (1 - Real.log p / T) ≤
        (1 - c * r ^ n * ℓ / T) * ∑ p ∈ S.filter (fun p => ¬ p ≤ ⌊Real.exp (c * r ^ n * ℓ)⌋₊),
          xDen p := by
      rw [mul_sum]
      refine sum_le_sum (fun p hp => ?_)
      obtain ⟨hp, hpa⟩ := mem_filter.mp hp
      push Not at hpa
      have hfl := Nat.lt_floor_add_one (Real.exp (c * r ^ n * ℓ))
      have hpr : Real.exp (c * r ^ n * ℓ) < p := by
        have : ((⌊Real.exp (c * r ^ n * ℓ)⌋₊ : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast hpa
        linarith
      have hp0 : (0 : ℝ) < p := lt_trans (Real.exp_pos _) hpr
      have hlog : c * r ^ n * ℓ < Real.log p := (Real.lt_log_iff_exp_lt hp0).mpr hpr
      have hd : c * r ^ n * ℓ / T ≤ Real.log p / T :=
        div_le_div_of_nonneg_right hlog.le hT.le
      have hx := xDen_nonneg p
      nlinarith
    have hC := mul_le_mul_of_nonneg_left hB hw0
    rw [sum_range_succ, mul_add]
    linarith

/-- Evaluation of the piece weights as a geometric sum. -/
lemma geom_eval (c r Y ℓ : ℝ) (hℓ : 0 < ℓ) (hY : 0 < Y) (hr : r ≠ 1) (n : ℕ) :
    ∑ k ∈ range n, (1 - c * r ^ k * ℓ / (Y * ℓ)) = n - c / Y * ((r ^ n - 1) / (r - 1)) := by
  have e : ∀ k : ℕ, c * r ^ k * ℓ / (Y * ℓ) = c / Y * r ^ k := fun k => by
    field_simp
  simp_rw [e]
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one, ← mul_sum, geom_sum_eq hr]

lemma pieces_le (c r Y ℓ : ℝ) (hc : 0 ≤ c) (hr : 1 ≤ r) (hℓ : 0 ≤ ℓ) (m : ℕ)
    (h : c * r ^ m ≤ Y) : ∀ k < m + 1, c * r ^ k * ℓ ≤ Y * ℓ := by
  intro k hk
  have h1 : r ^ k ≤ r ^ m := pow_le_pow_right₀ hr (by omega)
  have h2 : c * r ^ k ≤ Y := le_trans (mul_le_mul_of_nonneg_left h1 hc) h
  exact mul_le_mul_of_nonneg_right h2 hℓ

/-- **One group of upper sieves with weights `0 ≤ f q ≤ 1`.** -/
lemma upper_group_w {B K : ℝ} (N : ℕ)
    (hR : ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p) → ∀ F : Finset (Finset ℕ),
      F ⊆ P.powerset → (∀ T ∈ F, ∏ p ∈ T, p ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊) →
      ∑ T ∈ F, |rem (goldbachSeq N) xDen (liD ((N - 1 : ℕ) : ℝ)) T| ≤
        K * N / Real.log N ^ (5 : ℝ))
    (Cs : List Block) (hG' : Good Cs) (hρ'5 : rhoSum xDen Cs ≤ 1 / 5) (z : ℕ) (hz3 : 3 ≤ z)
    (hmem' : ∀ p ∈ univB Cs, p ≤ z ∧ p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p)
    (Q : Finset ℕ) (hQmem : ∀ q ∈ Q, z < q ∧ q.Prime ∧ ¬ q ∣ N)
    (hlevQ : ∀ q ∈ Q, ∀ S, S ⊆ univB Cs → cU Cs S ≠ 0 →
      q * ∏ p ∈ S, p ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊)
    (f : ℕ → ℝ) (hf0 : ∀ q ∈ Q, 0 ≤ f q) (hf1 : ∀ q ∈ Q, f q ≤ 1) :
    ∑ q ∈ Q, f q * (sifted ((goldbachSeq N).filter (fun a => q ∣ a)) (univB Cs) : ℝ) ≤
      liD ((N - 1 : ℕ) : ℝ) * (∏ p ∈ univB Cs, (1 - xDen p)) * (1 + 5 / 4 * rhoSum xDen Cs) *
        ∑ q ∈ Q, f q * xDen q + K * N / Real.log N ^ (5 : ℝ) := by
  classical
  set A := goldbachSeq N with hAdef
  set X := liD ((N - 1 : ℕ) : ℝ) with hXdef
  set Ω' := univB Cs with hΩ'
  have hX : 0 ≤ X := by
    rw [hXdef]; unfold liD liN
    exact sum_nonneg (fun n _ => div_nonneg zero_le_one (Real.log_natCast_nonneg n))
  set F' := Ω'.powerset.filter (fun S => cU Cs S ≠ 0) with hF'
  have hup : ∀ q ∈ Q, (sifted (A.filter (fun a => q ∣ a)) Ω' : ℝ) ≤
      X * xDen q * (∏ p ∈ Ω', (1 - xDen p)) * (1 + 5 / 4 * rhoSum xDen Cs) +
        ∑ S ∈ F', |rem A xDen X (insert q S)| := by
    intro q hq
    obtain ⟨hzq, hqp, -⟩ := hQmem q hq
    have h := blocks_upper_rel5 (A.filter (fun a => q ∣ a)) Cs hG' xDen xDen_nonneg xDen_lt_one
      (X * xDen q) (mul_nonneg hX (xDen_nonneg q)) hρ'5
    refine h.trans (le_of_eq ?_)
    congr 1
    refine sum_congr rfl (fun S hS => ?_)
    rw [hF', mem_filter, mem_powerset] at hS
    rw [rem_filter_dvd A xDen X hqp S (fun p hp => (hmem' p (hS.1 hp)).2.1)
      (fun hqS => by have := (hmem' q (hS.1 hqS)).1; omega)]
  set G := (Q ×ˢ F').image (fun qs => insert qs.1 qs.2) with hGdef
  have hinj : Set.InjOn (fun qs : ℕ × Finset ℕ => insert qs.1 qs.2) ↑(Q ×ˢ F') := by
    rintro ⟨q1, S1⟩ h1 ⟨q2, S2⟩ h2 he
    simp only [coe_product, Set.mem_prod, mem_coe] at h1 h2
    simp only at he
    have hS1 : S1 ⊆ Ω' := mem_powerset.mp (mem_filter.mp h1.2).1
    have hS2 : S2 ⊆ Ω' := mem_powerset.mp (mem_filter.mp h2.2).1
    have hq1 := (hQmem q1 h1.1).1
    have hq2 := (hQmem q2 h2.1).1
    have hn1 : q1 ∉ S1 := fun h => by have := (hmem' q1 (hS1 h)).1; omega
    have hn2 : q2 ∉ S2 := fun h => by have := (hmem' q2 (hS2 h)).1; omega
    have hq : q1 = q2 := by
      have : q1 ∈ insert q2 S2 := by rw [← he]; exact mem_insert_self q1 S1
      rcases mem_insert.mp this with h | h
      · exact h
      · exact absurd (hmem' q1 (hS2 h)).1 (by omega)
    subst hq
    have e1 := erase_insert hn1
    have e2 := erase_insert hn2
    rw [he] at e1
    rw [e1] at e2
    rw [Prod.mk.injEq]
    exact ⟨rfl, e2⟩
  have hGR : ∑ T ∈ G, |rem A xDen X T| ≤ K * N / Real.log N ^ (5 : ℝ) := by
    refine hR (Ω' ∪ Q) (fun p hp => ?_) G ?_ ?_
    · rcases mem_union.mp hp with h | h
      · exact ⟨(hmem' p h).2.1, (hmem' p h).2.2.1, (hmem' p h).2.2.2⟩
      · obtain ⟨h1, h3, h4⟩ := hQmem p h
        exact ⟨h3, h4, by omega⟩
    · intro T hT
      obtain ⟨⟨q, S⟩, hqS, rfl⟩ := mem_image.mp hT
      rw [mem_product] at hqS
      have hS : S ⊆ Ω' := mem_powerset.mp (mem_filter.mp hqS.2).1
      rw [mem_powerset]
      intro p hp
      rcases mem_insert.mp hp with h | h
      · exact mem_union_right _ (h ▸ hqS.1)
      · exact mem_union_left _ (hS h)
    · intro T hT
      obtain ⟨⟨q, S⟩, hqS, rfl⟩ := mem_image.mp hT
      rw [mem_product] at hqS
      have hS : S ⊆ Ω' := mem_powerset.mp (mem_filter.mp hqS.2).1
      have hcU : cU Cs S ≠ 0 := (mem_filter.mp hqS.2).2
      have hzq := (hQmem q hqS.1).1
      have hn : q ∉ S := fun h => by have := (hmem' q (hS h)).1; omega
      simp only
      rw [prod_insert hn]
      exact hlevQ q hqS.1 S hS hcU
  have hupw : ∀ q ∈ Q, f q * (sifted (A.filter (fun a => q ∣ a)) Ω' : ℝ) ≤
      f q * xDen q * (X * (∏ p ∈ Ω', (1 - xDen p)) * (1 + 5 / 4 * rhoSum xDen Cs)) +
        ∑ S ∈ F', |rem A xDen X (insert q S)| := by
    intro q hq
    have h := mul_le_mul_of_nonneg_left (hup q hq) (hf0 q hq)
    have hS0 : 0 ≤ ∑ S ∈ F', |rem A xDen X (insert q S)| := sum_nonneg (fun _ _ => abs_nonneg _)
    have h2 : f q * ∑ S ∈ F', |rem A xDen X (insert q S)| ≤
        ∑ S ∈ F', |rem A xDen X (insert q S)| := by
      have := mul_le_mul_of_nonneg_right (hf1 q hq) hS0
      linarith
    have e : f q * (X * xDen q * (∏ p ∈ Ω', (1 - xDen p)) * (1 + 5 / 4 * rhoSum xDen Cs) +
        ∑ S ∈ F', |rem A xDen X (insert q S)|) =
        f q * xDen q * (X * (∏ p ∈ Ω', (1 - xDen p)) * (1 + 5 / 4 * rhoSum xDen Cs)) +
          f q * ∑ S ∈ F', |rem A xDen X (insert q S)| := by ring
    rw [e] at h
    linarith
  refine (sum_le_sum hupw).trans ?_
  rw [sum_add_distrib, ← sum_mul]
  have e2 : ∑ q ∈ Q, ∑ S ∈ F', |rem A xDen X (insert q S)| = ∑ T ∈ G, |rem A xDen X T| := by
    rw [hGdef, sum_image hinj, sum_product]
  rw [e2]
  have : (∑ q ∈ Q, f q * xDen q) * (X * (∏ p ∈ Ω', (1 - xDen p)) * (1 + 5 / 4 * rhoSum xDen Cs)) =
      X * (∏ p ∈ Ω', (1 - xDen p)) * (1 + 5 / 4 * rhoSum xDen Cs) * ∑ q ∈ Q, f q * xDen q := by
    ring
  linarith

lemma big_aux6 (ℓ : ℝ) (h : (2 : ℝ) ^ 2100 ≤ ℓ) :
    (2 : ℝ) ^ 2006 ≤ ℓ / 21 ∧ (2 : ℝ) ^ 2006 ≤ 3788 / 100000 * ℓ ∧
      (2 : ℝ) ^ 2006 ≤ 3165 / 100000 * ℓ ∧ (2 : ℝ) ^ 2006 ≤ 2532 / 100000 * ℓ ∧
      (10 : ℝ) ^ 30 ≤ ℓ := by
  have e : (2 : ℝ) ^ 2100 = 2 ^ 94 * 2 ^ 2006 := by rw [← pow_add]
  rw [e] at h
  clear e
  have h94 : (64 : ℝ) ≤ 2 ^ 94 :=
    calc (64 : ℝ) ≤ 2 ^ 6 := by norm_num
      _ ≤ 2 ^ 94 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have h20 : (10 : ℝ) ^ 30 ≤ 2 ^ 2006 :=
    calc (10 : ℝ) ^ 30 ≤ 2 ^ 100 := by norm_num
      _ ≤ 2 ^ 2006 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  generalize (2 : ℝ) ^ 2006 = A at *
  generalize (2 : ℝ) ^ 94 = C at *
  have hA : 0 ≤ A := le_trans (by norm_num) h20
  have hm := mul_le_mul_of_nonneg_right h94 hA
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **Rényi with `K = 6`, deterministic core with the count**, Richert weights
`1 - (23/61) Σ_{q ∣ a} (1 - log q/log y)` and three upper sieve levels. -/
theorem renyi6_count {B K : ℝ} (N : ℕ)
    (hR : ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p) → ∀ F : Finset (Finset ℕ),
      F ⊆ P.powerset → (∀ T ∈ F, ∏ p ∈ T, p ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊) →
      ∑ T ∈ F, |rem (goldbachSeq N) xDen (liD ((N - 1 : ℕ) : ℝ)) T| ≤
        K * N / Real.log N ^ (5 : ℝ))
    (hE : Even N) (hℓ6 : (2 : ℝ) ^ 2100 ≤ Real.log N)
    (hE2 : Real.exp (49 / 100 * Real.log N) ≤ Real.sqrt N / Real.log N ^ B)
    (hE3 : 100 * |K| * N / Real.log N ^ (3 : ℝ) + Real.exp (Real.log N / 3) + 2 ≤
      (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / Real.log N ^ 2) :
    Real.exp (-36) * N / (2 * Real.log N ^ 2) ≤
      ((((range N).filter Nat.Prime).filter
        (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 6)).card : ℝ) := by
  classical
  set ℓ := Real.log N with hℓ
  obtain ⟨hLbig0, hL1big0, hL2big0, hL3big0, h10⟩ := big_aux6 ℓ hℓ6
  clear hℓ6
  obtain ⟨Bs, hG, hmem, hcov, hlev, hρ, h3k⟩ := block_pack N (ℓ / 21) hLbig0
  obtain ⟨C1, hG1, hmem1, hcov1, hlev1, hρ1, -⟩ := block_pack N (3788 / 100000 * ℓ) hL1big0
  obtain ⟨C2, hG2, hmem2, hcov2, hlev2, hρ2, -⟩ := block_pack N (3165 / 100000 * ℓ) hL2big0
  obtain ⟨C3, hG3, hmem3, hcov3, hlev3, hρ3, -⟩ := block_pack N (2532 / 100000 * ℓ) hL3big0
  clear hLbig0 hL1big0 hL2big0 hL3big0
  have hℓpos : 0 < ℓ := by linarith
  have hN1 : (1 : ℝ) < N := by
    by_contra h; push Not at h
    have : Real.log N ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h
    linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hexpℓ : Real.exp ℓ = N := Real.exp_log hNpos
  have hN38 : (38 : ℝ) ≤ N := by
    rw [← hexpℓ]
    have := Real.add_one_le_exp ℓ
    linarith
  have h4 : 4 ≤ N := by exact_mod_cast (show (4 : ℝ) ≤ N by linarith)
  -- the limits
  set L := ℓ / 21 with hL
  obtain ⟨hz3, hzr, hz1, hlogz1, hlogz2, hlogz3⟩ := floor_exp_facts L (by linarith)
  obtain ⟨-, hy1r, -, -, -, -⟩ := floor_exp_facts (101 / 1000 * ℓ) (by linarith)
  obtain ⟨-, hy2r, -, -, -, -⟩ := floor_exp_facts (165 / 1000 * ℓ) (by linarith)
  obtain ⟨hy3, hyr, hy1, hlogy1, hlogy2, hlogy3⟩ := floor_exp_facts (23 / 100 * ℓ) (by linarith)
  set z := ⌊Real.exp L⌋₊ with hz
  set y₁ := ⌊Real.exp (101 / 1000 * ℓ)⌋₊ with hy₁
  set y₂ := ⌊Real.exp (165 / 1000 * ℓ)⌋₊ with hy₂
  set y := ⌊Real.exp (23 / 100 * ℓ)⌋₊ with hy
  have hzy : z ≤ y := Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith))
  set Ω := univB Bs with hΩ
  set Ω₁ := univB C1 with hΩ₁
  set Ω₂ := univB C2 with hΩ₂
  set Ω₃ := univB C3 with hΩ₃
  set Q := (Ioc z y).filter (fun q => q.Prime ∧ ¬ q ∣ N) with hQ
  set Q₁ := (Q.filter (fun q => q ≤ y₂)).filter (fun q => q ≤ y₁) with hQ₁
  set Q₂ := (Q.filter (fun q => q ≤ y₂)).filter (fun q => ¬ q ≤ y₁) with hQ₂
  set Q₃ := Q.filter (fun q => ¬ q ≤ y₂) with hQ₃
  have hsub1 : Ω₁ ⊆ Ω := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hmem1 p hp
    exact hcov p h2 h3 h4 (h1.trans (Real.exp_le_exp.mpr (by linarith)))
  have hsub2 : Ω₂ ⊆ Ω := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hmem2 p hp
    exact hcov p h2 h3 h4 (h1.trans (Real.exp_le_exp.mpr (by linarith)))
  have hsub3 : Ω₃ ⊆ Ω := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hmem3 p hp
    exact hcov p h2 h3 h4 (h1.trans (Real.exp_le_exp.mpr (by linarith)))
  have hmem3' : ∀ p ∈ Ω₃, p ≤ z ∧ p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p := fun p hp =>
    ⟨Nat.le_floor (((hmem3 p hp).1).trans (Real.exp_le_exp.mpr (by linarith))),
      (hmem3 p hp).2⟩
  have hmem1' : ∀ p ∈ Ω₁, p ≤ z ∧ p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p := fun p hp =>
    ⟨Nat.le_floor (((hmem1 p hp).1).trans (Real.exp_le_exp.mpr (by linarith))),
      (hmem1 p hp).2⟩
  have hmem2' : ∀ p ∈ Ω₂, p ≤ z ∧ p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p := fun p hp =>
    ⟨Nat.le_floor (((hmem2 p hp).1).trans (Real.exp_le_exp.mpr (by linarith))),
      (hmem2 p hp).2⟩
  have hQmem : ∀ q ∈ Q, z < q ∧ q ≤ y ∧ q.Prime ∧ ¬ q ∣ N := by
    intro q hq
    rw [hQ, mem_filter, mem_Ioc] at hq
    exact ⟨hq.1.1, hq.1.2, hq.2.1, hq.2.2⟩
  have hQ1 : ∀ q ∈ Q₁, q ∈ Q ∧ q ≤ y₁ := fun q hq =>
    ⟨(mem_filter.mp (mem_filter.mp hq).1).1, (mem_filter.mp hq).2⟩
  have hQ2 : ∀ q ∈ Q₂, q ∈ Q ∧ y₁ < q ∧ q ≤ y₂ := fun q hq =>
    ⟨(mem_filter.mp (mem_filter.mp hq).1).1, by have := (mem_filter.mp hq).2; omega,
      (mem_filter.mp (mem_filter.mp hq).1).2⟩
  have hQ3 : ∀ q ∈ Q₃, q ∈ Q ∧ y₂ < q := fun q hq =>
    ⟨(mem_filter.mp hq).1, by have := (mem_filter.mp hq).2; omega⟩
  -- the weight
  set T := 23 / 100 * ℓ with hT
  have hTpos : 0 < T := by rw [hT]; positivity
  set f : ℕ → ℝ := fun q => 23 / 61 * (1 - Real.log q / T) with hf
  have hf0 : ∀ q ∈ Q, 0 ≤ f q := by
    intro q hq
    have h1 := (hQmem q hq).2.1
    have hq0 : (0 : ℝ) < q := by have := (hQmem q hq).2.2.1.pos; exact_mod_cast this
    have hl : Real.log q ≤ T := by
      have : (q : ℝ) ≤ Real.exp T := le_trans (by exact_mod_cast h1) hyr
      have := Real.log_le_log hq0 this
      rwa [Real.log_exp] at this
    have : Real.log q / T ≤ 1 := by rw [div_le_one hTpos]; exact hl
    simp only [hf]
    nlinarith
  have hf1 : ∀ q ∈ Q, f q ≤ 1 := by
    intro q hq
    have hq1 : (1 : ℝ) ≤ q := by have := (hQmem q hq).2.2.1.one_lt.le; exact_mod_cast this
    have hl : 0 ≤ Real.log q := Real.log_nonneg hq1
    have : 0 ≤ Real.log q / T := div_nonneg hl hTpos.le
    simp only [hf]
    nlinarith
  -- the sequence
  set A := goldbachSeq N with hAdef
  set X := liD ((N - 1 : ℕ) : ℝ) with hXdef
  have hX : 0 ≤ X := by
    rw [hXdef]; unfold liD liN
    exact sum_nonneg (fun n _ => div_nonneg zero_le_one (Real.log_natCast_nonneg n))
  have hlevel : ∀ e : ℝ, e ≤ 49 / 100 * ℓ → ∀ n : ℕ, (n : ℝ) ≤ Real.exp e →
      n ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊ := fun e he n hn =>
    Nat.le_floor (hn.trans ((Real.exp_le_exp.mpr he).trans hE2))
  -- the lower sieve
  have hρ5 : rhoSum xDen Bs ≤ 1 / 5 := hρ.trans (by norm_num)
  have hρ15 : rhoSum xDen C1 ≤ 1 / 5 := hρ1.trans (by norm_num)
  have hρ25 : rhoSum xDen C2 ≤ 1 / 5 := hρ2.trans (by norm_num)
  have hρ35 : rhoSum xDen C3 ≤ 1 / 5 := hρ3.trans (by norm_num)
  have hlow := blocks_main_rel5 A Bs hG xDen xDen_nonneg xDen_lt_one X hX hρ5
  have hlowR := hR Ω (fun p hp => ⟨(hmem p hp).2.1, (hmem p hp).2.2.1, (hmem p hp).2.2.2⟩)
    (Ω.powerset.filter (fun S => cL Bs S ≠ 0)) (filter_subset _ _) (fun T hT => by
      rw [mem_filter, mem_powerset] at hT
      refine (support_prod Bs hG T hT.1 (Or.inl hT.2)).trans
        (hlevel (154 / 15 * L) (by linarith) _ hlev))
  -- the three groups of upper sieves
  have hup1 := upper_group_w N hR C1 hG1 hρ15 z hz3 hmem1' Q₁
    (fun q hq => by
      obtain ⟨h1, -, h3, h4⟩ := hQmem q (hQ1 q hq).1
      exact ⟨h1, h3, h4⟩)
    (fun q hq S hS hcU => by
      have hqy : q ≤ y₁ := (hQ1 q hq).2
      have hSl := support_prod C1 hG1 S hS (Or.inr hcU)
      apply hlevel ((101 / 1000 * ℓ) + 154 / 15 * (3788 / 100000 * ℓ)) (by linarith)
      rw [Real.exp_add]
      push_cast
      have hqr : (q : ℝ) ≤ Real.exp (101 / 1000 * ℓ) :=
        le_trans (by exact_mod_cast hqy) hy1r
      have hSr : ((∏ p ∈ S, p : ℕ) : ℝ) ≤ Real.exp (154 / 15 * (3788 / 100000 * ℓ)) :=
        le_trans (by exact_mod_cast hSl) hlev1
      push_cast at hSr
      exact mul_le_mul hqr hSr (by positivity) (Real.exp_pos _).le)
    f (fun q hq => hf0 q (hQ1 q hq).1) (fun q hq => hf1 q (hQ1 q hq).1)
  have hup2 := upper_group_w N hR C2 hG2 hρ25 z hz3 hmem2' Q₂
    (fun q hq => by
      obtain ⟨h1, -, h3, h4⟩ := hQmem q (hQ2 q hq).1
      exact ⟨h1, h3, h4⟩)
    (fun q hq S hS hcU => by
      have hqy : q ≤ y₂ := (hQ2 q hq).2.2
      have hSl := support_prod C2 hG2 S hS (Or.inr hcU)
      apply hlevel ((165 / 1000 * ℓ) + 154 / 15 * (3165 / 100000 * ℓ)) (by linarith)
      rw [Real.exp_add]
      push_cast
      have hqr : (q : ℝ) ≤ Real.exp (165 / 1000 * ℓ) :=
        le_trans (by exact_mod_cast hqy) hy2r
      have hSr : ((∏ p ∈ S, p : ℕ) : ℝ) ≤ Real.exp (154 / 15 * (3165 / 100000 * ℓ)) :=
        le_trans (by exact_mod_cast hSl) hlev2
      push_cast at hSr
      exact mul_le_mul hqr hSr (by positivity) (Real.exp_pos _).le)
    f (fun q hq => hf0 q (hQ2 q hq).1) (fun q hq => hf1 q (hQ2 q hq).1)
  have hup3 := upper_group_w N hR C3 hG3 hρ35 z hz3 hmem3' Q₃
    (fun q hq => by
      obtain ⟨h1, -, h3, h4⟩ := hQmem q (hQ3 q hq).1
      exact ⟨h1, h3, h4⟩)
    (fun q hq S hS hcU => by
      have hqy : q ≤ y := (hQmem q (hQ3 q hq).1).2.1
      have hSl := support_prod C3 hG3 S hS (Or.inr hcU)
      apply hlevel ((23 / 100 * ℓ) + 154 / 15 * (2532 / 100000 * ℓ)) (by linarith)
      rw [Real.exp_add]
      push_cast
      have hqr : (q : ℝ) ≤ Real.exp (23 / 100 * ℓ) :=
        le_trans (by exact_mod_cast hqy) hyr
      have hSr : ((∏ p ∈ S, p : ℕ) : ℝ) ≤ Real.exp (154 / 15 * (2532 / 100000 * ℓ)) :=
        le_trans (by exact_mod_cast hSl) hlev3
      push_cast at hSr
      exact mul_le_mul hqr hSr (by positivity) (Real.exp_pos _).le)
    f (fun q hq => hf0 q (hQ3 q hq).1) (fun q hq => hf1 q (hQ3 q hq).1)
  rw [← hℓ] at hup1 hup2 hup3
  -- the densities
  set V := ∏ p ∈ Ω, (1 - xDen p) with hVdef
  set W₁ := ∏ p ∈ Ω₁, (1 - xDen p) with hW₁def
  set W₂ := ∏ p ∈ Ω₂, (1 - xDen p) with hW₂def
  set W₃ := ∏ p ∈ Ω₃, (1 - xDen p) with hW₃def
  have hW₁0 : 0 ≤ W₁ := prod_nonneg (fun p _ => by linarith [xDen_le_one p])
  have hW₂0 : 0 ≤ W₂ := prod_nonneg (fun p _ => by linarith [xDen_le_one p])
  have hW₃0 : 0 ≤ W₃ := prod_nonneg (fun p _ => by linarith [xDen_le_one p])
  have hsw1 : ∑ p ∈ Ω \ Ω₁, xDen p ≤ 230046 / 1000000 := by
    have h := xDen_gap N ℓ (3788 / 100000) (201 / 200) 46 (by norm_num) (by norm_num)
      (by norm_num) (by linarith) (by norm_num) Bs C1 hmem hcov1
    refine h.trans ?_
    norm_num
  have hVW1 : W₁ * (769954 / 1000000) ≤ V := by
    have e : (∏ p ∈ Ω \ Ω₁, (1 - xDen p)) * W₁ = V := prod_sdiff hsub1
    have h1 := one_sub_sum_le_prod (Ω \ Ω₁) xDen xDen_nonneg xDen_le_one
    have hP : (769954 / 1000000 : ℝ) ≤ ∏ p ∈ Ω \ Ω₁, (1 - xDen p) := by linarith
    have := mul_le_mul_of_nonneg_left hP hW₁0
    calc W₁ * (769954 / 1000000) ≤ W₁ * ∏ p ∈ Ω \ Ω₁, (1 - xDen p) := this
      _ = V := by rw [← e]; ring
  have hsw2 : ∑ p ∈ Ω \ Ω₂, xDen p ≤ 410082 / 1000000 := by
    have h := xDen_gap N ℓ (3165 / 100000) (201 / 200) 82 (by norm_num) (by norm_num)
      (by norm_num) (by linarith) (by norm_num) Bs C2 hmem hcov2
    refine h.trans ?_
    norm_num
  have hVW2 : W₂ * (589918 / 1000000) ≤ V := by
    have e : (∏ p ∈ Ω \ Ω₂, (1 - xDen p)) * W₂ = V := prod_sdiff hsub2
    have h1 := one_sub_sum_le_prod (Ω \ Ω₂) xDen xDen_nonneg xDen_le_one
    have hP : (589918 / 1000000 : ℝ) ≤ ∏ p ∈ Ω \ Ω₂, (1 - xDen p) := by linarith
    have := mul_le_mul_of_nonneg_left hP hW₂0
    calc W₂ * (589918 / 1000000) ≤ W₂ * ∏ p ∈ Ω \ Ω₂, (1 - xDen p) := this
      _ = V := by rw [← e]; ring
  have hsw3 : ∑ p ∈ Ω \ Ω₃, xDen p ≤ 635127 / 1000000 := by
    have h := xDen_gap N ℓ (2532 / 100000) (201 / 200) 127 (by norm_num) (by norm_num)
      (by norm_num) (by linarith) (by norm_num) Bs C3 hmem hcov3
    refine h.trans ?_
    norm_num
  have hVW3 : W₃ * (364873 / 1000000) ≤ V := by
    have e : (∏ p ∈ Ω \ Ω₃, (1 - xDen p)) * W₃ = V := prod_sdiff hsub3
    have h1 := one_sub_sum_le_prod (Ω \ Ω₃) xDen xDen_nonneg xDen_le_one
    have hP : (364873 / 1000000 : ℝ) ≤ ∏ p ∈ Ω \ Ω₃, (1 - xDen p) := by linarith
    have := mul_le_mul_of_nonneg_left hP hW₃0
    calc W₃ * (364873 / 1000000) ≤ W₃ * ∏ p ∈ Ω \ Ω₃, (1 - xDen p) := this
      _ = V := by rw [← e]; ring
  have hzc : ⌊Real.exp (1 / 21 * ℓ)⌋₊ = z := by
    rw [hz]; congr 2; rw [hL]; ring
  have hsQ1 : ∑ q ∈ Q₁, f q * xDen q ≤ 23 / 61 * (52606 / 100000) := by
    have hk := pieces_le (1 / 21) (101 / 100) (23 / 100) ℓ (by norm_num) (by norm_num) hℓpos.le 75
      (by norm_num)
    have h := xDen_geom_w ℓ (1 / 21) (101 / 100) T (by norm_num) (by norm_num) (by norm_num)
      (by linarith) hTpos 76 hk Q₁ (fun q hq => by
        rw [hzc]
        obtain ⟨h1, -, h3, -⟩ := hQmem q (hQ1 q hq).1
        refine ⟨h3, h1, ((hQ1 q hq).2).trans (Nat.floor_le_floor
          (Real.exp_le_exp.mpr ?_))⟩
        have hY : (101 / 1000 : ℝ) ≤ 1 / 21 * (101 / 100) ^ 76 := by norm_num
        have := mul_le_mul_of_nonneg_right hY hℓpos.le
        linarith)
    have hg := geom_eval (1 / 21) (101 / 100) (23 / 100) ℓ hℓpos (by norm_num) (by norm_num) 76
    rw [← hT] at hg
    rw [hg] at h
    have h2 : (101 / 100 - 1 + 1 / 10 ^ 6 : ℝ) * (76 - 1 / 21 / (23 / 100) *
        (((101 / 100) ^ 76 - 1) / (101 / 100 - 1))) ≤ 52606 / 100000 := by norm_num
    have e : ∑ q ∈ Q₁, f q * xDen q = 23 / 61 * ∑ q ∈ Q₁, xDen q * (1 - Real.log q / T) := by
      rw [mul_sum]; refine sum_congr rfl (fun q _ => ?_); simp only [hf]; ring
    rw [e]
    push_cast at h
    linarith
  have hsQ2 : ∑ q ∈ Q₂, f q * xDen q ≤ 23 / 61 * (21695 / 100000) := by
    have hk := pieces_le (101 / 1000) (101 / 100) (23 / 100) ℓ (by norm_num) (by norm_num) hℓpos.le 49
      (by norm_num)
    have h := xDen_geom_w ℓ (101 / 1000) (101 / 100) T (by norm_num) (by norm_num) (by norm_num)
      (by linarith) hTpos 50 hk Q₂ (fun q hq => by
        obtain ⟨-, -, h3, -⟩ := hQmem q (hQ2 q hq).1
        refine ⟨h3, (hQ2 q hq).2.1, ((hQ2 q hq).2.2).trans (Nat.floor_le_floor
          (Real.exp_le_exp.mpr ?_))⟩
        have hY : (165 / 1000 : ℝ) ≤ 101 / 1000 * (101 / 100) ^ 50 := by norm_num
        have := mul_le_mul_of_nonneg_right hY hℓpos.le
        linarith)
    have hg := geom_eval (101 / 1000) (101 / 100) (23 / 100) ℓ hℓpos (by norm_num) (by norm_num) 50
    rw [← hT] at hg
    rw [hg] at h
    have h2 : (101 / 100 - 1 + 1 / 10 ^ 6 : ℝ) * (50 - 101 / 1000 / (23 / 100) *
        (((101 / 100) ^ 50 - 1) / (101 / 100 - 1))) ≤ 21695 / 100000 := by norm_num
    have e : ∑ q ∈ Q₂, f q * xDen q = 23 / 61 * ∑ q ∈ Q₂, xDen q * (1 - Real.log q / T) := by
      rw [mul_sum]; refine sum_congr rfl (fun q _ => ?_); simp only [hf]; ring
    rw [e]
    push_cast at h
    linarith
  have hsQ3 : ∑ q ∈ Q₃, f q * xDen q ≤ 23 / 61 * (5120 / 100000) := by
    have hk := pieces_le (165 / 1000) (101 / 100) (23 / 100) ℓ (by norm_num) (by norm_num) hℓpos.le 33
      (by norm_num)
    have h := xDen_geom_w ℓ (165 / 1000) (101 / 100) T (by norm_num) (by norm_num) (by norm_num)
      (by linarith) hTpos 34 hk Q₃ (fun q hq => by
        obtain ⟨-, h2, h3, -⟩ := hQmem q (hQ3 q hq).1
        refine ⟨h3, (hQ3 q hq).2, h2.trans (Nat.floor_le_floor
          (Real.exp_le_exp.mpr ?_))⟩
        have hY : (23 / 100 : ℝ) ≤ 165 / 1000 * (101 / 100) ^ 34 := by norm_num
        have := mul_le_mul_of_nonneg_right hY hℓpos.le
        linarith)
    have hg := geom_eval (165 / 1000) (101 / 100) (23 / 100) ℓ hℓpos (by norm_num) (by norm_num) 34
    rw [← hT] at hg
    rw [hg] at h
    have h2 : (101 / 100 - 1 + 1 / 10 ^ 6 : ℝ) * (34 - 165 / 1000 / (23 / 100) *
        (((101 / 100) ^ 34 - 1) / (101 / 100 - 1))) ≤ 5120 / 100000 := by norm_num
    have e : ∑ q ∈ Q₃, f q * xDen q = 23 / 61 * ∑ q ∈ Q₃, xDen q * (1 - Real.log q / T) := by
      rw [mul_sum]; refine sum_congr rfl (fun q _ => ?_); simp only [hf]; ring
    rw [e]
    push_cast at h
    linarith
  have hρ0 := rhoSum_nonneg xDen xDen_nonneg xDen_le_one Bs
  have hρ10 := rhoSum_nonneg xDen xDen_nonneg xDen_le_one C1
  have hρ20 := rhoSum_nonneg xDen xDen_nonneg xDen_le_one C2
  have hρ30 := rhoSum_nonneg xDen xDen_nonneg xDen_le_one C3
  have hsQ10 : 0 ≤ ∑ q ∈ Q₁, f q * xDen q :=
    sum_nonneg (fun q hq => mul_nonneg (hf0 q (hQ1 q hq).1) (xDen_nonneg q))
  have hsubtr1 : X * W₁ * (1 + 5 / 4 * rhoSum xDen C1) * ∑ q ∈ Q₁, f q * xDen q ≤
      X * V * (3194 / 10000) := by
    have h1 : (1 + 5 / 4 * rhoSum xDen C1) * ∑ q ∈ Q₁, f q * xDen q ≤
        (12395 / 10000) * (23 / 61 * (52606 / 100000)) :=
      mul_le_mul (by linarith) hsQ1 hsQ10 (by norm_num)
    have h2 : W₁ * ((1 + 5 / 4 * rhoSum xDen C1) * ∑ q ∈ Q₁, f q * xDen q) ≤
        W₁ * ((12395 / 10000) * (23 / 61 * (52606 / 100000))) := mul_le_mul_of_nonneg_left h1 hW₁0
    have h3 : W₁ * ((12395 / 10000) * (23 / 61 * (52606 / 100000))) ≤ V * (3194 / 10000) := by linarith
    have h4 := mul_le_mul_of_nonneg_left (h2.trans h3) hX
    calc X * W₁ * (1 + 5 / 4 * rhoSum xDen C1) * ∑ q ∈ Q₁, f q * xDen q
        = X * (W₁ * ((1 + 5 / 4 * rhoSum xDen C1) * ∑ q ∈ Q₁, f q * xDen q)) := by ring
      _ ≤ X * (V * (3194 / 10000)) := h4
      _ = X * V * (3194 / 10000) := by ring
  have hsQ20 : 0 ≤ ∑ q ∈ Q₂, f q * xDen q :=
    sum_nonneg (fun q hq => mul_nonneg (hf0 q (hQ2 q hq).1) (xDen_nonneg q))
  have hsubtr2 : X * W₂ * (1 + 5 / 4 * rhoSum xDen C2) * ∑ q ∈ Q₂, f q * xDen q ≤
      X * V * (1719 / 10000) := by
    have h1 : (1 + 5 / 4 * rhoSum xDen C2) * ∑ q ∈ Q₂, f q * xDen q ≤
        (12395 / 10000) * (23 / 61 * (21695 / 100000)) :=
      mul_le_mul (by linarith) hsQ2 hsQ20 (by norm_num)
    have h2 : W₂ * ((1 + 5 / 4 * rhoSum xDen C2) * ∑ q ∈ Q₂, f q * xDen q) ≤
        W₂ * ((12395 / 10000) * (23 / 61 * (21695 / 100000))) := mul_le_mul_of_nonneg_left h1 hW₂0
    have h3 : W₂ * ((12395 / 10000) * (23 / 61 * (21695 / 100000))) ≤ V * (1719 / 10000) := by linarith
    have h4 := mul_le_mul_of_nonneg_left (h2.trans h3) hX
    calc X * W₂ * (1 + 5 / 4 * rhoSum xDen C2) * ∑ q ∈ Q₂, f q * xDen q
        = X * (W₂ * ((1 + 5 / 4 * rhoSum xDen C2) * ∑ q ∈ Q₂, f q * xDen q)) := by ring
      _ ≤ X * (V * (1719 / 10000)) := h4
      _ = X * V * (1719 / 10000) := by ring
  have hsQ30 : 0 ≤ ∑ q ∈ Q₃, f q * xDen q :=
    sum_nonneg (fun q hq => mul_nonneg (hf0 q (hQ3 q hq).1) (xDen_nonneg q))
  have hsubtr3 : X * W₃ * (1 + 5 / 4 * rhoSum xDen C3) * ∑ q ∈ Q₃, f q * xDen q ≤
      X * V * (656 / 10000) := by
    have h1 : (1 + 5 / 4 * rhoSum xDen C3) * ∑ q ∈ Q₃, f q * xDen q ≤
        (12395 / 10000) * (23 / 61 * (5120 / 100000)) :=
      mul_le_mul (by linarith) hsQ3 hsQ30 (by norm_num)
    have h2 : W₃ * ((1 + 5 / 4 * rhoSum xDen C3) * ∑ q ∈ Q₃, f q * xDen q) ≤
        W₃ * ((12395 / 10000) * (23 / 61 * (5120 / 100000))) := mul_le_mul_of_nonneg_left h1 hW₃0
    have h3 : W₃ * ((12395 / 10000) * (23 / 61 * (5120 / 100000))) ≤ V * (656 / 10000) := by linarith
    have h4 := mul_le_mul_of_nonneg_left (h2.trans h3) hX
    calc X * W₃ * (1 + 5 / 4 * rhoSum xDen C3) * ∑ q ∈ Q₃, f q * xDen q
        = X * (W₃ * ((1 + 5 / 4 * rhoSum xDen C3) * ∑ q ∈ Q₃, f q * xDen q)) := by ring
      _ ≤ X * (V * (656 / 10000)) := h4
      _ = X * V * (656 / 10000) := by ring
  have hV0 : 0 ≤ V := prod_nonneg (fun p _ => by linarith [xDen_le_one p])
  have hXV0 : 0 ≤ X * V := mul_nonneg hX hV0
  have hlowmain : X * V * (6168 / 10000) ≤ X * V * (1 - 2 * rhoSum xDen Bs) :=
    mul_le_mul_of_nonneg_left (by linarith) hXV0
  -- absolute size of X V
  have hV2 : Real.exp (-36) * 21 / ℓ ≤ V := by
    have hV := LeanLab.PNTSieve.Mertens.prod_one_sub_inv_pred_ge z hz3 Ω
      (fun p hp => ⟨(hmem p hp).2.1, (hmem p hp).2.2.2, Nat.le_floor (hmem p hp).1⟩)
    have hV' : Real.exp (-36) / Real.log z ≤ V := by
      refine hV.trans (le_of_eq (prod_congr rfl (fun p hp => ?_)))
      simp only [xDen, if_pos (hmem p hp).2.2.2]
    refine le_trans ?_ hV'
    have hlz : 0 < Real.log z := by linarith
    rw [div_le_div_iff₀ hℓpos hlz]
    have := Real.exp_pos (-36 : ℝ)
    have : Real.log z * 21 ≤ ℓ := by linarith
    nlinarith
  have hliD := liD_ge N (by omega)
  have hliD0 : 0 ≤ ((N : ℝ) - 2) / ℓ := div_nonneg (by linarith) hℓpos.le
  have hXV : ((N : ℝ) - 2) / ℓ * (Real.exp (-36) * 21 / ℓ) ≤ X * V :=
    mul_le_mul hliD hV2 (by positivity) hX
  have hXV2 : ((N : ℝ) - 2) / ℓ * (Real.exp (-36) * 21 / ℓ) =
      21 * (Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2)) := by
    ring
  have hXV' : 21 * (Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2)) ≤ X * V := hXV2 ▸ hXV
  -- errors
  have h5r : ℓ ^ (5 : ℝ) = ℓ ^ 5 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h3r : ℓ ^ (3 : ℝ) = ℓ ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hKN : K * N / ℓ ^ (5 : ℝ) ≤ |K| * N / ℓ ^ 5 := by
    rw [h5r]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K) hNpos.le)
      (by positivity)
  have hK0 : 0 ≤ |K| * N / ℓ ^ 5 := by positivity
  have herr : ((3 : ℝ) ^ Bs.length + 3) * (|K| * N / ℓ ^ 5) ≤ |K| * N / ℓ ^ (3 : ℝ) := by
    rw [h3r]
    have h1 : (3 : ℝ) ^ Bs.length + 3 ≤ ℓ ^ 2 := by
      have : 4 * L ^ 2 + 3 ≤ ℓ ^ 2 := by rw [hL]; nlinarith
      linarith
    calc ((3 : ℝ) ^ Bs.length + 3) * (|K| * N / ℓ ^ 5) ≤ ℓ ^ 2 * (|K| * N / ℓ ^ 5) :=
          mul_le_mul_of_nonneg_right h1 hK0
      _ = |K| * N / ℓ ^ 3 := by field_simp
  have hlow3 : (3 : ℝ) ^ Bs.length *
      ∑ S ∈ Ω.powerset.filter (fun S => cL Bs S ≠ 0), |rem A xDen X S| ≤
      (3 : ℝ) ^ Bs.length * (|K| * N / ℓ ^ 5) :=
    mul_le_mul_of_nonneg_left (hlowR.trans hKN) (by positivity)
  -- the sifted set and the weight
  set Sz := A.filter (fun a => ∀ p ∈ Ω, ¬ p ∣ a) with hSz
  have hcardSz : (sifted A Ω : ℝ) = (Sz.card : ℝ) := by simp [sifted, hSz]
  have hswap : ∑ a ∈ Sz, ∑ q ∈ Q.filter (fun q => q ∣ a), f q =
      ∑ q ∈ Q, f q * ((Sz.filter (fun a => q ∣ a)).card : ℝ) := by
    simp_rw [sum_filter]
    rw [sum_comm]
    refine sum_congr rfl (fun q _ => ?_)
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    ring
  have hqle : ∀ Ω' : Finset ℕ, Ω' ⊆ Ω → ∀ q, ((Sz.filter (fun a => q ∣ a)).card : ℝ) ≤
      (sifted (A.filter (fun a => q ∣ a)) Ω' : ℝ) := by
    intro Ω' hsub q
    simp only [sifted]
    push_cast
    exact_mod_cast card_le_card (fun a ha => by
      simp only [hSz, mem_filter] at ha ⊢
      exact ⟨⟨ha.1.1, ha.2⟩, fun p hp => ha.1.2 p (hsub hp)⟩)
  have hqsum : ∑ q ∈ Q, f q * ((Sz.filter (fun a => q ∣ a)).card : ℝ) ≤
      ∑ q ∈ Q₁, f q * (sifted (A.filter (fun a => q ∣ a)) Ω₁ : ℝ) +
        ∑ q ∈ Q₂, f q * (sifted (A.filter (fun a => q ∣ a)) Ω₂ : ℝ) +
        ∑ q ∈ Q₃, f q * (sifted (A.filter (fun a => q ∣ a)) Ω₃ : ℝ) := by
    rw [← sum_filter_add_sum_filter_not Q (fun q => q ≤ y₂),
      ← sum_filter_add_sum_filter_not (Q.filter (fun q => q ≤ y₂)) (fun q => q ≤ y₁)]
    refine add_le_add (add_le_add ?_ ?_) ?_
    · exact sum_le_sum (fun q hq => mul_le_mul_of_nonneg_left (hqle Ω₁ hsub1 q)
        (hf0 q (hQ1 q hq).1))
    · exact sum_le_sum (fun q hq => mul_le_mul_of_nonneg_left (hqle Ω₂ hsub2 q)
        (hf0 q (hQ2 q hq).1))
    · exact sum_le_sum (fun q hq => mul_le_mul_of_nonneg_left (hqle Ω₃ hsub3 q)
        (hf0 q (hQ3 q hq).1))
  set SQ := A.filter (fun a => ∃ q ∈ Q, q ^ 2 ∣ a) with hSQ
  set small := (range (y + 1)).image (fun p => N - p) with hsmall_def
  have hsmall : small.card ≤ y + 1 := card_image_le.trans (by simp)
  set Gd := ((range N).filter Nat.Prime).filter
    (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 6) with hGd
  set U := small ∪ SQ ∪ Gd.image (fun p => N - p) with hU
  have hw : ∀ a ∈ Sz, 1 - ∑ q ∈ Q.filter (fun q => q ∣ a), f q ≤
      if a ∈ U then 1 else 0 := by
    intro a ha
    split_ifs with haU
    · have : (0 : ℝ) ≤ ∑ q ∈ Q.filter (fun q => q ∣ a), f q :=
        sum_nonneg (fun q hq => hf0 q (mem_filter.mp hq).1)
      linarith
    · rw [hSz, mem_filter] at ha
      obtain ⟨haA, haP⟩ := ha
      have haA' := haA
      rw [hAdef] at haA'
      unfold goldbachSeq at haA'
      obtain ⟨p, hp, rfl⟩ := mem_image.mp haA'
      rw [mem_filter, mem_range] at hp
      obtain ⟨hpN, hpp⟩ := hp
      simp only [hU, mem_union, not_or] at haU
      obtain ⟨⟨hns, hnsq⟩, hng⟩ := haU
      have hpy : y < p := by
        by_contra h
        push Not at h
        exact hns (mem_image.mpr ⟨p, mem_range.mpr (by omega), rfl⟩)
      have hpodd : Odd p := hpp.odd_of_ne_two (by omega)
      have hmodd : Odd (N - p) := by
        rcases hE with ⟨a, ha⟩
        rcases hpodd with ⟨b, hb⟩
        exact ⟨a - b - 1, by omega⟩
      have hm0 : N - p ≠ 0 := by omega
      have hsq : ∀ q ∈ Q.filter (fun q => q ∣ N - p), ¬ q ^ 2 ∣ N - p := fun q hq h2 =>
        hnsq (mem_filter.mpr ⟨haA, q, (mem_filter.mp hq).1, h2⟩)
      have hΩ8 : 7 ≤ ArithmeticFunction.cardFactors (N - p) := by
        by_contra hc
        push Not at hc
        exact hng (mem_image.mpr ⟨p, by
          rw [hGd, mem_filter, mem_filter, mem_range]; exact ⟨⟨hpN, hpp⟩, by omega⟩, rfl⟩)
      have hsmallD : ∀ r, r.Prime → r ∣ N - p → r ≤ y →
          r ∈ Q.filter (fun q => q ∣ N - p) := by
        intro r hrp hrd hry
        have hr2 : r ≠ 2 := by
          rintro rfl
          exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr hrd)
        have hr3 : 3 ≤ r := by have := hrp.two_le; omega
        have hrN : ¬ r ∣ N := by
          intro hrN
          have : r ∣ p := by
            have h1 := Nat.dvd_sub hrN hrd
            rwa [Nat.sub_sub_self hpN.le] at h1
          have := (Nat.prime_dvd_prime_iff_eq hrp hpp).mp this
          omega
        have hrz : z < r := by
          by_contra hle
          push Not at hle
          exact haP r (hcov r hrp hrN hr3
            ((show (r : ℝ) ≤ z by exact_mod_cast hle).trans hzr)) hrd
        rw [mem_filter, hQ, mem_filter, mem_Ioc]
        exact ⟨⟨⟨hrz, hry⟩, hrp, hrN⟩, hrd⟩
      obtain ⟨hcardle, hpow⟩ := omega_split_prod (N - p) hm0 (Q.filter (fun q => q ∣ N - p))
        (fun q hq => ⟨(hQmem q (mem_filter.mp hq).1).2.2.1, (mem_filter.mp hq).2⟩) hsq y hsmallD
      set D := Q.filter (fun q => q ∣ N - p) with hDdef
      set d := D.card with hd
      set Ωa := ArithmeticFunction.cardFactors (N - p) with hΩa
      have hDpos : ∀ q ∈ D, (0 : ℝ) < q := fun q hq => by
        have := (hQmem q (mem_filter.mp hq).1).2.2.1.pos; exact_mod_cast this
      have hpowr : ((∏ q ∈ D, q : ℕ) : ℝ) * ((y : ℝ) + 1) ^ (Ωa - d) ≤ N := by
        have : (∏ q ∈ D, q) * (y + 1) ^ (Ωa - d) ≤ N := hpow.trans (Nat.sub_le N p)
        exact_mod_cast this
      push_cast at hpowr
      have hprod0 : (0 : ℝ) < ∏ q ∈ D, (q : ℝ) := prod_pos hDpos
      have hlog := Real.log_le_log (by positivity) hpowr
      rw [Real.log_mul hprod0.ne' (by positivity), Real.log_pow, Real.log_prod
        (fun q hq => (hDpos q hq).ne'), Nat.cast_sub hcardle, ← hℓ] at hlog
      have hΩr : (7 : ℝ) ≤ Ωa := by exact_mod_cast hΩ8
      have hdΩ : (d : ℝ) ≤ Ωa := by exact_mod_cast hcardle
      have h2 : ((Ωa : ℝ) - d) * (23 / 100 * ℓ) ≤ ((Ωa : ℝ) - d) * Real.log ((y : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hlogy3.le (by linarith)
      have h4 := mul_nonneg (show (0 : ℝ) ≤ (Ωa : ℝ) - 7 by linarith) hℓpos.le
      have hsl : ∑ q ∈ D, Real.log q ≤ (d - 61 / 23) * T := by
        rw [hT]; linarith
      have hsum : ∑ q ∈ D, f q = 23 / 61 * (d - (∑ q ∈ D, Real.log q) / T) := by
        simp only [hf]
        rw [← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, sum_div]
      have hdiv : (∑ q ∈ D, Real.log q) / T ≤ d - 61 / 23 := by
        rw [div_le_iff₀ hTpos]; exact hsl
      rw [hsum]
      linarith
  have hsumw := sum_le_sum hw
  rw [sum_boole, sum_sub_distrib, hswap] at hsumw
  simp only [sum_const, nsmul_eq_mul, mul_one] at hsumw
  have hU1 : (Sz.filter (fun a => a ∈ U)).card ≤ U.card :=
    card_le_card (fun a ha => (mem_filter.mp ha).2)
  have hU2 : U.card ≤ small.card + SQ.card + Gd.card :=
    (card_union_le _ _).trans (Nat.add_le_add (card_union_le _ _) card_image_le)
  have hU3 : ((Sz.filter (fun a => a ∈ U)).card : ℝ) ≤ (y : ℝ) + 1 + SQ.card + Gd.card := by
    have : (Sz.filter (fun a => a ∈ U)).card ≤ (y + 1) + SQ.card + Gd.card := by omega
    exact_mod_cast this
  -- the squares
  have hSQ1 : (SQ.card : ℝ) ≤ 2 * N / ((z : ℝ) + 1) := by
    have h1 : SQ ⊆ Q.biUnion (fun q => (Ioc 0 N).filter (fun x => q ^ 2 ∣ x)) := by
      intro a ha
      rw [hSQ, mem_filter] at ha
      obtain ⟨haA, q, hq, hqa⟩ := ha
      rw [mem_biUnion]
      refine ⟨q, hq, mem_filter.mpr ⟨?_, hqa⟩⟩
      rw [hAdef] at haA
      unfold goldbachSeq at haA
      obtain ⟨p, hp, rfl⟩ := mem_image.mp haA
      rw [mem_filter, mem_range] at hp
      rw [mem_Ioc]
      omega
    have h2 := (card_le_card h1).trans card_biUnion_le
    have h3 : ∀ q ∈ Q, (((Ioc 0 N).filter (fun x => q ^ 2 ∣ x)).card : ℝ) ≤
        N * ((q : ℝ) ^ 2)⁻¹ := by
      intro q _
      rw [Nat.Ioc_filter_dvd_card_eq_div]
      have := Nat.cast_div_le (α := ℝ) (m := N) (n := q ^ 2)
      push_cast at this
      rw [div_eq_mul_inv] at this
      exact this
    have h4 : ∑ q ∈ Q, ((q : ℝ) ^ 2)⁻¹ ≤ 2 / ((z : ℝ) + 1) := by
      refine le_trans (sum_le_sum_of_subset_of_nonneg (?_ : Q ⊆ Ioo z (y + 1))
        (fun _ _ _ => by positivity)) (sum_Ioo_inv_sq_le z (y + 1))
      intro q hq
      obtain ⟨h1, h2, -, -⟩ := hQmem q hq
      rw [mem_Ioo]
      omega
    calc (SQ.card : ℝ) ≤ ∑ q ∈ Q, (((Ioc 0 N).filter (fun x => q ^ 2 ∣ x)).card : ℝ) := by
          exact_mod_cast h2
      _ ≤ ∑ q ∈ Q, (N : ℝ) * ((q : ℝ) ^ 2)⁻¹ := sum_le_sum h3
      _ = N * ∑ q ∈ Q, ((q : ℝ) ^ 2)⁻¹ := by rw [mul_sum]
      _ ≤ N * (2 / ((z : ℝ) + 1)) := mul_le_mul_of_nonneg_left h4 hNpos.le
      _ = 2 * N / ((z : ℝ) + 1) := by ring
  have hSQ2 : 2 * N / ((z : ℝ) + 1) ≤ Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2) / 4 := by
    have hcube := Real.pow_div_factorial_le_exp (x := L) (by linarith) 3
    have hT : ℓ ^ 3 / 55566 ≤ (z : ℝ) + 1 := by
      have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
      rw [h6] at hcube
      have e : ℓ ^ 3 / 55566 = L ^ 3 / 6 := by rw [hL]; ring
      linarith
    have hTpos : 0 < ℓ ^ 3 / 55566 := by positivity
    have hstep : 2 * N / ((z : ℝ) + 1) ≤ 2 * N / (ℓ ^ 3 / 55566) :=
      div_le_div_of_nonneg_left (by positivity) hTpos hT
    refine hstep.trans ?_
    rw [div_div_eq_mul_div, div_le_iff₀ (pow_pos hℓpos 3)]
    have e3 : ℓ ^ 3 = ℓ ^ 2 * ℓ := by ring
    have e : Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2) / 4 * ℓ ^ 3 =
        Real.exp (-36) * (((N : ℝ) - 2) * ℓ) / 4 := by
      rw [e3, show Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2) / 4 * (ℓ ^ 2 * ℓ) =
        Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2 * ℓ ^ 2) * ℓ / 4 by ring,
        div_mul_cancel₀ _ (pow_pos hℓpos 2).ne']
      ring
    rw [e]
    have hem : (1 : ℝ) / 10 ^ 18 ≤ Real.exp (-36) := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (Real.exp_pos 36) exp_36_le
    have h1 : ((N : ℝ) - 2) * 10 ^ 30 ≤ ((N : ℝ) - 2) * ℓ :=
      mul_le_mul_of_nonneg_left h10 (by linarith)
    have h2 : (1 / 10 ^ 18) * (((N : ℝ) - 2) * ℓ) ≤ Real.exp (-36) * (((N : ℝ) - 2) * ℓ) :=
      mul_le_mul_of_nonneg_right hem (mul_nonneg (by linarith) hℓpos.le)
    linarith
  -- y is small
  have hy50 : 50 * ((y : ℝ) + 1) ≤ Real.exp (ℓ / 3) + 2 := by
    have h1 : Real.exp (ℓ / 3) =
        Real.exp (23 / 100 * ℓ) * Real.exp ((1 / 3 - 23 / 100) * ℓ) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : (100 : ℝ) ≤ Real.exp ((1 / 3 - 23 / 100) * ℓ) := by
      have := Real.add_one_le_exp ((1 / 3 - 23 / 100) * ℓ); nlinarith
    have h3 : (1 : ℝ) ≤ Real.exp (23 / 100 * ℓ) := Real.one_le_exp (by linarith)
    have h4 := mul_le_mul_of_nonneg_left h2 (le_trans zero_le_one h3)
    linarith
  have hc0 : Real.exp (-36) - Real.exp (-37) ≤ Real.exp (-36) := by
    have := Real.exp_pos (-37 : ℝ); linarith
  have hD : 0 ≤ ((N : ℝ) - 2) / ℓ ^ 2 := div_nonneg (by linarith) (by positivity)
  have hcD : (Real.exp (-36) - Real.exp (-37)) * ((N : ℝ) - 2) / ℓ ^ 2 ≤
      Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2) := by
    rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_right hc0 hD
  have hK3 : 0 ≤ |K| * N / ℓ ^ (3 : ℝ) := by rw [h3r]; positivity
  have he36 := Real.exp_pos (-36 : ℝ)
  have hgoal : Real.exp (-36) * N / (2 * ℓ ^ 2) ≤
      57 / 100 * (Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2)) := by
    rw [div_le_iff₀ (by positivity)]
    have e : 57 / 100 * (Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2)) * (2 * ℓ ^ 2) =
        114 / 100 * Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2 * ℓ ^ 2) := by ring
    rw [e, div_mul_cancel₀ _ (pow_pos hℓpos 2).ne']
    nlinarith [mul_nonneg he36.le (show (0 : ℝ) ≤ (N : ℝ) - 38 by linarith)]
  have hE3' : 100 * (|K| * N / ℓ ^ (3 : ℝ)) + Real.exp (ℓ / 3) + 2 ≤
      Real.exp (-36) * (((N : ℝ) - 2) / ℓ ^ 2) := by
    have : 100 * |K| * N / ℓ ^ (3 : ℝ) = 100 * (|K| * N / ℓ ^ (3 : ℝ)) := by ring
    linarith
  rw [hcardSz] at hlow
  linarith

end LeanLab.PNTPort.BVMax
