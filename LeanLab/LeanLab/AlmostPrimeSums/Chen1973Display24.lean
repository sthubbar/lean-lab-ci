/-
AI-written Lean code, Claude, 2026-10-21, session 20261021T0217Z-cloud56, unit U-6814, track T1.
P0002 J.-R. Chen 1973, Sci. Sinica 16, 157-176, p. 171, display (24), the first two equalities,
read from the lab copy papers/P0002.pdf, page image rendered with pdftoppm.

Chen: since `1/φ(d₁d₂/(d₁,d₂)) = g(d₁)g(d₂) ∑_{d∣(d₁,d₂)} f(d)`, with `g = 1/φ` and `f = ψ`,
`ψ(d) = ∏_{p∣d}(p-2)`, one has
`∑_{d₁,d₂} λ_{d₁}λ_{d₂}/φ(d₁d₂/(d₁,d₂)) = ∑_k f(k) (∑_{k∣d} λ_d g(d))²`.
This file proves both steps for every finite set of squarefree moduli and every real `λ`, and the last
equality of (24), `= 1/S` for Chen's choice of `λ`, as `chen24_value` and `chen_display24`.
Binary Goldbach is OPEN.
-/
import LeanLab.AlmostPrimeSums.Chen1973Lemmas

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section
namespace LeanLab.AlmostPrimeSums.Chen1973Display24

open LeanLab.AlmostPrimeSums.Chen1973Lemmas

/-- `φ(lcm(a,b)) φ(gcd(a,b)) = φ(a) φ(b)` for squarefree `a`, `b`. -/
lemma totient_lcm_mul_gcd {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    (a.lcm b).totient * (a.gcd b).totient = a.totient * b.totient := by
  set g := a.gcd b with hgdef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero ha.ne_zero)
  have ha' : a = g * (a / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
  have hb' : b = g * (b / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm
  have hcop : (a / g).Coprime (b / g) := Nat.coprime_div_gcd_div_gcd hg0
  have hga : g.Coprime (a / g) := (Nat.squarefree_mul_iff.mp (ha' ▸ ha)).1
  have hgb : g.Coprime (b / g) := (Nat.squarefree_mul_iff.mp (hb' ▸ hb)).1
  have hab : a * b = g * (a / g) * (b / g) * g := by
    conv_lhs => rw [ha', hb']
    ring
  have hl : a.lcm b = g * (a / g) * (b / g) := by
    rw [Nat.lcm, ← hgdef, hab, Nat.mul_div_cancel _ hg0]
  have hA : a.totient = g.totient * (a / g).totient := by
    rw [← Nat.totient_mul hga, ← ha']
  have hB : b.totient = g.totient * (b / g).totient := by
    rw [← Nat.totient_mul hgb, ← hb']
  rw [hl, Nat.totient_mul (Nat.coprime_mul_iff_left.mpr ⟨hgb, hcop⟩), Nat.totient_mul hga, hA, hB]
  ring

/-- Chen's `ψ(d) = ∏_{p∣d} (p-2)`. -/
def ψ (d : ℕ) : ℝ := ∏ p ∈ d.primeFactors, ((p : ℝ) - 2)

/-- `φ(n) = ∑_{d∣n} ψ(d)` for squarefree `n`, Chen's `f = ψ` with `φ = 1 * f`. -/
lemma totient_eq_sum_psi {n : ℕ} (hn : Squarefree n) :
    (n.totient : ℝ) = ∑ d ∈ n.divisors, ψ d := by
  have h := IsMultiplicative.prodPrimeFactors_add_of_squarefree
    (IsMultiplicative.prodPrimeFactors (fun p : ℕ => (p : ℝ) - 2))
    (IsMultiplicative.prodPrimeFactors (fun _ : ℕ => (1 : ℝ))) hn
  rw [prodPrimeFactors_apply hn.ne_zero, mul_apply] at h
  have hl : ∀ p ∈ n.primeFactors,
      ((prodPrimeFactors fun p : ℕ => (p : ℝ) - 2) + (prodPrimeFactors fun _ : ℕ => (1 : ℝ))) p =
        (p : ℝ) - 1 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    rw [ArithmeticFunction.add_apply, prodPrimeFactors_apply hpp.ne_zero,
      prodPrimeFactors_apply hpp.ne_zero, hpp.primeFactors, prod_singleton, prod_singleton]
    ring
  rw [prod_congr rfl hl] at h
  have hφ : (n.totient : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
    have h1 := chen_inv_totient hn
    have hpos : (0 : ℝ) < n.totient := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn.ne_zero)
    have hP : ∏ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1) = (∏ p ∈ n.primeFactors, ((p : ℝ) - 1))⁻¹ := by
      rw [← prod_inv_distrib]; simp [one_div]
    rw [hP, one_div] at h1
    exact inv_injective h1
  rw [hφ, h, Nat.sum_divisorsAntidiagonal (fun x y =>
    (prodPrimeFactors fun p : ℕ => (p : ℝ) - 2) x * (prodPrimeFactors fun _ : ℕ => (1 : ℝ)) y)]
  refine sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  have hq0 : n / d ≠ 0 := by
    have := Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)
    omega
  rw [prodPrimeFactors_apply hd0, prodPrimeFactors_apply hq0, prod_const_one, mul_one]
  rfl

/-- **Chen (24), the "Since" identity**: for squarefree `d₁`, `d₂`,
`1/φ(lcm(d₁,d₂)) = (1/φ(d₁)) (1/φ(d₂)) ∑_{d∣(d₁,d₂)} ψ(d)`. -/
theorem inv_totient_lcm {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    1 / ((a.lcm b).totient : ℝ) = 1 / (a.totient : ℝ) * (1 / (b.totient : ℝ)) *
      ∑ d ∈ (a.gcd b).divisors, ψ d := by
  have hg : Squarefree (a.gcd b) := ha.squarefree_of_dvd (Nat.gcd_dvd_left a b)
  rw [← totient_eq_sum_psi hg]
  have h := totient_lcm_mul_gcd ha hb
  have hR : ((a.lcm b).totient : ℝ) * (a.gcd b).totient = (a.totient : ℝ) * b.totient := by
    exact_mod_cast h
  have hpa : (0 : ℝ) < a.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero ha.ne_zero)
  have hpb : (0 : ℝ) < b.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hb.ne_zero)
  have hpl : (0 : ℝ) < (a.lcm b).totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (Nat.lcm_ne_zero ha.ne_zero hb.ne_zero))
  field_simp
  linarith

/-- The diagonalization of a quadratic form with a gcd kernel:
`∑_{d₁,d₂ ∈ s} c(d₁)c(d₂) ∑_{k∣(d₁,d₂)} f(k) = ∑_{k} f(k) (∑_{d ∈ s, k∣d} c(d))²`,
`k` over all divisors of members of `s`. -/
theorem diag (s : Finset ℕ) (hs : ∀ d ∈ s, d ≠ 0) (c f : ℕ → ℝ) :
    ∑ d₁ ∈ s, ∑ d₂ ∈ s, c d₁ * c d₂ * ∑ k ∈ (d₁.gcd d₂).divisors, f k =
      ∑ k ∈ s.biUnion Nat.divisors, f k * (∑ d ∈ s.filter (k ∣ ·), c d) ^ 2 := by
  classical
  symm
  calc ∑ k ∈ s.biUnion Nat.divisors, f k * (∑ d ∈ s.filter (k ∣ ·), c d) ^ 2
      = ∑ k ∈ s.biUnion Nat.divisors, ∑ d₁ ∈ s, ∑ d₂ ∈ s,
          (if k ∣ d₁.gcd d₂ then f k * (c d₁ * c d₂) else 0) := by
        refine sum_congr rfl fun k _ => ?_
        rw [sq, sum_filter, sum_mul_sum, mul_sum]
        refine sum_congr rfl fun d₁ _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun d₂ _ => ?_
        by_cases h1 : k ∣ d₁ <;> by_cases h2 : k ∣ d₂ <;> simp [h1, h2, Nat.dvd_gcd_iff]
    _ = ∑ d₁ ∈ s, ∑ d₂ ∈ s, ∑ k ∈ s.biUnion Nat.divisors,
          (if k ∣ d₁.gcd d₂ then f k * (c d₁ * c d₂) else 0) := by
        rw [sum_comm]
        exact sum_congr rfl fun d₁ _ => sum_comm
    _ = _ := by
        refine sum_congr rfl fun d₁ h₁ => sum_congr rfl fun d₂ h₂ => ?_
        rw [← sum_filter]
        have e : (s.biUnion Nat.divisors).filter (· ∣ d₁.gcd d₂) = (d₁.gcd d₂).divisors := by
          ext k
          simp only [mem_filter, mem_biUnion, Nat.mem_divisors]
          constructor
          · rintro ⟨-, hk⟩
            exact ⟨hk, Nat.gcd_ne_zero_left (hs d₁ h₁)⟩
          · rintro ⟨hk, hg⟩
            exact ⟨⟨d₁, h₁, hk.trans (Nat.gcd_dvd_left _ _), hs d₁ h₁⟩, hk⟩
        rw [e, mul_sum]
        exact sum_congr rfl fun k _ => by ring

/-- **Chen 1973, display (24), the first two equalities, PROVED**: for a finite set `s` of
squarefree moduli and any real `λ`,
`∑_{d₁,d₂ ∈ s} λ_{d₁}λ_{d₂}/φ(d₁d₂/(d₁,d₂)) = ∑_k ψ(k) (∑_{d ∈ s, k∣d} λ_d/φ(d))²`. -/
theorem chen24_diag (s : Finset ℕ) (hs : ∀ d ∈ s, Squarefree d) (lam : ℕ → ℝ) :
    ∑ d₁ ∈ s, ∑ d₂ ∈ s, lam d₁ * lam d₂ / ((d₁ * d₂ / d₁.gcd d₂).totient : ℝ) =
      ∑ k ∈ s.biUnion Nat.divisors,
        ψ k * (∑ d ∈ s.filter (k ∣ ·), lam d * (1 / (d.totient : ℝ))) ^ 2 := by
  rw [← diag s (fun d hd => (hs d hd).ne_zero)]
  refine sum_congr rfl fun d₁ h₁ => sum_congr rfl fun d₂ h₂ => ?_
  rw [← Nat.lcm, div_eq_mul_one_div, inv_totient_lcm (hs d₁ h₁) (hs d₂ h₂)]
  ring

/-- Vacuity check: `s = {1, 3}` is a set of squarefree moduli. -/
theorem chen24_instance : ∀ d ∈ ({1, 3} : Finset ℕ), Squarefree d := by
  intro d hd
  simp only [mem_insert, mem_singleton] at hd
  rcases hd with rfl | rfl
  · exact squarefree_one
  · exact Nat.prime_three.prime.squarefree

/-! ### The value `1/S` -/

/-- `∑_{d∣n} μ(d) = [n = 1]`. -/
lemma sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, ((μ d : ℤ) : ℝ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun F : ArithmeticFunction ℤ => F n) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply, one_apply] at h
  have h' := congrArg (fun z : ℤ => (z : ℝ)) h
  push_cast at h'
  rw [h']

/-- `∑_{k∣d∣m} μ(m/d) = [m = k]` for `k ∣ m ≠ 0`. -/
lemma sum_moebius_interval {k m : ℕ} (hm : m ≠ 0) (hk : k ∣ m) :
    ∑ d ∈ m.divisors.filter (k ∣ ·), ((μ (m / d) : ℤ) : ℝ) = if m = k then 1 else 0 := by
  obtain ⟨n, rfl⟩ := hk
  have hk0 : k ≠ 0 := left_ne_zero_of_mul hm
  have hn0 : n ≠ 0 := right_ne_zero_of_mul hm
  have e : ∑ d ∈ (k * n).divisors.filter (k ∣ ·), ((μ (k * n / d) : ℤ) : ℝ) =
      ∑ t ∈ n.divisors, ((μ (n / t) : ℤ) : ℝ) := by
    symm
    refine sum_nbij' (fun t => k * t) (fun d => d / k) ?_ ?_ ?_ ?_ ?_
    · intro t ht
      simp only [Nat.mem_divisors, mem_filter] at ht ⊢
      exact ⟨⟨Nat.mul_dvd_mul_left k ht.1, hm⟩, dvd_mul_right k t⟩
    · intro d hd
      simp only [Nat.mem_divisors, mem_filter] at hd ⊢
      obtain ⟨⟨hdm, -⟩, t, rfl⟩ := hd
      rw [Nat.mul_div_cancel_left t (Nat.pos_of_ne_zero hk0)]
      exact ⟨(Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hk0)).mp hdm, hn0⟩
    · intro t _
      simp [Nat.mul_div_cancel_left t (Nat.pos_of_ne_zero hk0)]
    · intro d hd
      simp only [mem_filter] at hd
      obtain ⟨-, t, rfl⟩ := hd
      simp [Nat.mul_div_cancel_left t (Nat.pos_of_ne_zero hk0)]
    · intro t _
      rw [Nat.mul_div_mul_left n t (Nat.pos_of_ne_zero hk0)]
  rw [e, Nat.sum_div_divisors n (fun t => ((μ t : ℤ) : ℝ)), sum_moebius_divisors]
  congr 1
  apply propext
  constructor
  · rintro rfl; simp
  · intro h
    have := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk0) (h.trans (mul_one k).symm)
    exact this

/-- **Chen 1973, display (24), the last equality, PROVED** in abstract form: let `s` be a finite
divisor-closed set of positive integers, `f ≠ 0` on `s`, `S = ∑_{k ∈ s} μ²(k)/f(k) ≠ 0`, and
Chen's `λ_d g(d) = ∑_{m ∈ s, d∣m} μ(m/d) μ(m)/(S f(m))`, which is his
`(1/S) ∑_{k ≤ D/d, (k,xd)=1} μ(kd)μ(k)/f(kd)` with `m = kd`. Then
`∑_k f(k) (∑_{d ∈ s, k∣d} λ_d g(d))² = 1/S`. -/
theorem chen24_value (s : Finset ℕ) (h0 : ∀ m ∈ s, m ≠ 0)
    (hdc : ∀ m ∈ s, ∀ d, d ∣ m → d ∈ s) (f : ℕ → ℝ) (hf : ∀ k ∈ s, f k ≠ 0) (S : ℝ)
    (hS : S = ∑ k ∈ s, ((μ k : ℤ) : ℝ) ^ 2 / f k) (hS0 : S ≠ 0) :
    ∑ k ∈ s.biUnion Nat.divisors, f k * (∑ d ∈ s.filter (k ∣ ·),
      ∑ m ∈ s.filter (d ∣ ·), ((μ (m / d) : ℤ) : ℝ) * (((μ m : ℤ) : ℝ) / (S * f m))) ^ 2 =
        1 / S := by
  classical
  have hU : s.biUnion Nat.divisors = s := by
    ext k
    simp only [mem_biUnion, Nat.mem_divisors]
    constructor
    · rintro ⟨m, hm, hkm, -⟩; exact hdc m hm k hkm
    · intro hk; exact ⟨k, hk, dvd_refl k, h0 k hk⟩
  set Y : ℕ → ℝ := fun m => ((μ m : ℤ) : ℝ) / (S * f m) with hY
  have hin : ∀ k ∈ s, (∑ d ∈ s.filter (k ∣ ·),
      ∑ m ∈ s.filter (d ∣ ·), ((μ (m / d) : ℤ) : ℝ) * Y m) = Y k := by
    intro k hk
    rw [sum_comm' (t' := s) (s' := fun m => m.divisors.filter (k ∣ ·))]
    · simp_rw [← sum_mul]
      rw [sum_eq_single_of_mem k hk]
      · rw [sum_moebius_interval (h0 k hk) (dvd_refl k), if_pos rfl, one_mul]
      · intro m hm hmk
        by_cases hkm : k ∣ m
        · rw [sum_moebius_interval (h0 m hm) hkm, if_neg hmk, zero_mul]
        · have : m.divisors.filter (k ∣ ·) = ∅ := by
            apply eq_empty_of_forall_notMem
            intro d hd
            simp only [mem_filter, Nat.mem_divisors] at hd
            exact hkm (hd.2.trans hd.1.1)
          rw [this, sum_empty, zero_mul]
    · intro d m
      simp only [mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hd, hkd⟩, hm, hdm⟩
        exact ⟨⟨⟨hdm, h0 m hm⟩, hkd⟩, hm⟩
      · rintro ⟨⟨⟨hdm, -⟩, hkd⟩, hm⟩
        exact ⟨⟨hdc m hm d hdm, hkd⟩, hm, hdm⟩
  rw [hU, sum_congr rfl fun k hk => by rw [hin k hk]]
  have e : ∀ k ∈ s, f k * Y k ^ 2 = ((μ k : ℤ) : ℝ) ^ 2 / f k / S ^ 2 := by
    intro k hk
    simp only [hY]
    have := hf k hk
    field_simp
  rw [sum_congr rfl e, ← sum_div, ← hS]
  field_simp

/-- Chen's sieve set: squarefree `d ≤ D` prime to `x`. -/
def sv (x D : ℕ) : Finset ℕ := (Icc 1 D).filter (fun d => Squarefree d ∧ d.Coprime x)

lemma psi_pos_of_coprime {x k : ℕ} (hx : Even x) (hk : k.Coprime x) : 0 < ψ k := by
  unfold ψ
  refine prod_pos fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2k : 2 ∣ k := Nat.dvd_of_mem_primeFactors hp
    have := Nat.Coprime.coprime_dvd_left h2k hk
    rw [Nat.prime_two.coprime_iff_not_dvd] at this
    exact this (even_iff_two_dvd.mp hx)
  have : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := hpp.two_le; omega)
  linarith

/-- Chen's `S = ∑_{d ∈ sv} μ²(d)/ψ(d)`. -/
def Sv (x D : ℕ) : ℝ := ∑ k ∈ sv x D, ((μ k : ℤ) : ℝ) ^ 2 / ψ k

/-- Chen's `λ_d = φ(d) (1/S) ∑_{k ≤ D/d, (k,xd)=1} μ(kd)μ(k)/f(kd)`, written with `m = kd`. -/
def lamC (x D d : ℕ) : ℝ :=
  (d.totient : ℝ) * ∑ m ∈ (sv x D).filter (d ∣ ·),
    ((μ (m / d) : ℤ) : ℝ) * (((μ m : ℤ) : ℝ) / (Sv x D * ψ m))

lemma one_le_Sv {x D : ℕ} (hx : Even x) (hD : 1 ≤ D) : 1 ≤ Sv x D := by
  have h1 : 1 ∈ sv x D := by
    simp only [sv, mem_filter, mem_Icc]
    exact ⟨⟨le_rfl, hD⟩, squarefree_one, Nat.coprime_one_left x⟩
  have := single_le_sum (f := fun k => ((μ k : ℤ) : ℝ) ^ 2 / ψ k) (fun k hk => by
    simp only [sv, mem_filter] at hk
    exact div_nonneg (sq_nonneg _) (psi_pos_of_coprime hx hk.2.2).le) h1
  simp [ψ] at this
  exact this

/-- **Chen 1973, display (24), whole, PROVED**: for even `x` and `D ≥ 1`, with Chen's `λ`,
`∑_{d₁,d₂ ≤ D, (d₁d₂,x)=1} λ_{d₁}λ_{d₂}/φ(d₁d₂/(d₁,d₂)) = 1/S`, the sums over squarefree `d`. -/
theorem chen_display24 {x D : ℕ} (hx : Even x) (hD : 1 ≤ D) :
    ∑ d₁ ∈ sv x D, ∑ d₂ ∈ sv x D,
      lamC x D d₁ * lamC x D d₂ / ((d₁ * d₂ / d₁.gcd d₂).totient : ℝ) = 1 / Sv x D := by
  have hmem : ∀ d ∈ sv x D, 1 ≤ d ∧ d ≤ D ∧ Squarefree d ∧ d.Coprime x := by
    intro d hd; simp only [sv, mem_filter, mem_Icc] at hd; exact ⟨hd.1.1, hd.1.2, hd.2⟩
  rw [chen24_diag (sv x D) (fun d hd => (hmem d hd).2.2.1)]
  have e : ∀ k ∈ (sv x D).biUnion Nat.divisors,
      ψ k * (∑ d ∈ (sv x D).filter (k ∣ ·), lamC x D d * (1 / (d.totient : ℝ))) ^ 2 =
      ψ k * (∑ d ∈ (sv x D).filter (k ∣ ·), ∑ m ∈ (sv x D).filter (d ∣ ·),
        ((μ (m / d) : ℤ) : ℝ) * (((μ m : ℤ) : ℝ) / (Sv x D * ψ m))) ^ 2 := by
    intro k _
    congr 2
    refine sum_congr rfl fun d hd => ?_
    have hd1 := (hmem d (mem_filter.mp hd).1).1
    have hφ : (d.totient : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr hd1).ne'
    unfold lamC
    field_simp
  rw [sum_congr rfl e]
  refine chen24_value (sv x D) (fun m hm => by have := (hmem m hm).1; omega) ?_ ψ
    (fun k hk => (psi_pos_of_coprime hx (hmem k hk).2.2.2).ne') (Sv x D) rfl
    (by linarith [one_le_Sv hx hD])
  intro m hm d hdm
  obtain ⟨h1, h2, h3, h4⟩ := hmem m hm
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdm h1
  simp only [sv, mem_filter, mem_Icc]
  exact ⟨⟨hd0, (Nat.le_of_dvd h1 hdm).trans h2⟩, h3.squarefree_of_dvd hdm,
    Nat.Coprime.coprime_dvd_left hdm h4⟩

end LeanLab.AlmostPrimeSums.Chen1973Display24
