/-
P0069 Baker Harman Pintz 1997, pages 6 and 7, displays 2.4 and 2.5.
Raw form of the major arc coefficient replacement: under hypotheses i to iv of
Theorem 2 on page 3, for every A and every D at least 1, the mean square over even N in
[x, x + H] of the major arc integral of S1 S2 e(-Nt) minus the principal model of
display 2.6 with the original eta limits is at most C H Y² (log x)^(-A-7).
Every definition of Decomp512a is written out so that Decomp512a can import this file.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib
import LeanLab.BHP1997.Route512MajorFixed
import LeanLab.BHP1997.Route512MajorMoment

namespace LeanLab.BHP1997.Route512Major
open Classical Complex MeasureTheory Set

/-- P0069 page 6, the use of hypothesis iii of Theorem 2 in display 2.4: if `k` is
coprime to the product of the primes below `z`, then `k` is coprime to every `q` with
`1 ≤ q < z`. -/
theorem support_coprime512j (z : ℝ) (k q : ℕ) (hq1 : 1 ≤ q) (hq : (q : ℝ) < z)
    (hk : Nat.gcd k (Thm2.primorialBelow z) = 1) : Nat.Coprime k q := by
  apply Nat.coprime_of_dvd
  intro p hp hpk hpq
  have hple : p ≤ q := Nat.le_of_dvd hq1 hpq
  have hpz : (p : ℝ) < z := lt_of_le_of_lt (by exact_mod_cast hple) hq
  have hmem : p ∈ (Finset.range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) < z) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_ceil.mpr hpz), hp, hpz⟩
  have hdvd : p ∣ Thm2.primorialBelow z := Finset.dvd_prod_of_mem (fun p : ℕ => p) hmem
  have h1 : p ∣ 1 := hk ▸ Nat.dvd_gcd hpk hdvd
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

set_option maxHeartbeats 1600000 in
/-- P0069 Baker Harman Pintz 1997, pages 6 and 7, display 2.5 and the S2 replacement
after it, raw form of the major arc coefficient leaf: under hypotheses i to iv of
Theorem 2, for every A > 0, every D at least 1 and x large, the mean square over even N
in [x, x + H] of the major arc integral of S1 S2 e(-Nt) minus the principal model of
display 2.6 with the original eta limits is at most C H Y² (log x)^(-A-7), with
Y = x^(11/20+ε) and H = Y^(2(1/16 - 10^(-5))). -/
theorem major_coefficients_raw512j (B ε : ℝ) (hε : 0 < ε) (a b : ℝ → ℕ → ℂ) (u v : ℝ)
    (hi : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ x →
        ‖∑ k ∈ (Finset.Ioc ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊).filter
            (fun k : ℕ => (k : ℝ) ≤ t),
          (a x k * χ (k : ZMod q) - Thm2.delta χ * u / Real.log x)‖ ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    (hii : ∃ C : ℝ, ∀ x k, ‖a x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B ∧
      ‖b x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
    (hiii : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : ℕ,
      Nat.gcd k (Thm2.primorialBelow (Real.log x ^ A)) ≠ 1 → a x k = 0)
    (hiv : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
        t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊).filter
            (fun m : ℕ => (m : ℝ) ≤ t),
          (b x m * χ (m : ZMod q) - Thm2.delta χ * v / Real.log (x ^ (11 / 20 + ε)))‖ ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    (A : ℝ) (hA : 0 < A) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      ∑ N ∈ (Finset.Icc ⌈x⌉₊
          ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter (fun N => Even N),
        ‖(∫ t in Ioc
              (1 / ((⌊((x ^ (11 / 20 + ε)) ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ (1 / 2 : ℝ) /
                2⌋₊ : ℕ) : ℝ))
              (1 + 1 / ((⌊((x ^ (11 / 20 + ε)) ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^
                (1 / 2 : ℝ) / 2⌋₊ : ℕ) : ℝ)) ∩
            ⋃ q ∈ Finset.Icc 1
              (min ⌊((x ^ (11 / 20 + ε)) ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ (1 / 2 : ℝ) / 2⌋₊
                ⌊Real.log x ^ (2 * D)⌋₊),
              ⋃ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
                Icc ((r : ℝ) / q - Real.log x ^ (4 * D) / (q * x ^ (11 / 20 + ε)))
                  ((r : ℝ) / q + Real.log x ^ (4 * D) / (q * x ^ (11 / 20 + ε))),
            (∑ k ∈ Finset.Ioc ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊,
                a x k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) *
              (∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
                b x m * @fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ))) *
                @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))) -
          u * v / (Real.log x * Real.log (x ^ (11 / 20 + ε))) *
            ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
              (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
                (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
                  @fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ))) *
                ∫ t in (-(Real.log x ^ (4 * D) / (q * x ^ (11 / 20 + ε))))..
                  (Real.log x ^ (4 * D) / (q * x ^ (11 / 20 + ε))),
                  (∑ k ∈ Finset.Ioc ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊,
                      (1 : ℂ) * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) *
                    (∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
                      (1 : ℂ) * @fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ))) *
                      @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))‖ ^ 2 ≤
        C * (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) *
          (x ^ (11 / 20 + ε)) ^ 2 * Real.log x ^ (-A - 7)) := by
  obtain ⟨c, Cm, hmom⟩ := long_divisor_moment512j B ε hε
  obtain ⟨C₂, h2⟩ := hii
  refine ⟨1, fun D hD => ?_⟩
  have hD0 : 0 ≤ D := by linarith
  obtain ⟨A', hA'⟩ : ∃ A' : ℝ, A' = 16 * D + |c| + A + 7 := ⟨_, rfl⟩
  have hA'pos : 0 < A' := by linarith [abs_nonneg c]
  obtain ⟨C₁, h1⟩ := hi A' hA'pos
  obtain ⟨C₃, h3⟩ := hiii A' hA'pos
  obtain ⟨C₄, h4⟩ := hiv A' hA'pos
  have hθ : (0 : ℝ) < 11 / 20 + ε := by linarith
  have hθ₂ : (0 : ℝ) < 2 * (1 / 16 - 1 / 10 ^ 5) ∧ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ) < 1 := by
    norm_num
  obtain ⟨δ₁, hδ₁⟩ : ∃ δ₁ : ℝ, δ₁ = (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)) * (1 / 2) :=
    ⟨_, rfl⟩
  have hδ₁pos : 0 < δ₁ := by
    rw [hδ₁]
    exact mul_pos (mul_pos hθ hθ₂.1) (by norm_num)
  have hδ₂pos : 0 < 11 / 20 + ε - δ₁ := by
    rw [hδ₁]
    nlinarith [hθ₂.2]
  have e1 := Real.tendsto_log_atTop.eventually_ge_atTop 2
  have e3 := (isLittleO_log_rpow_rpow_atTop (2 * D) hδ₁pos).bound
    (by norm_num : (0 : ℝ) < 1 / 6)
  have e4 := (isLittleO_log_rpow_rpow_atTop (8 * D) hθ).bound (by norm_num : (0 : ℝ) < 1 / 4)
  have e5 := (isLittleO_log_rpow_rpow_atTop (4 * D) hδ₂pos).bound (by norm_num : (0 : ℝ) < 1)
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp (e1.and (e3.and (e4.and (e5.and
    (Filter.eventually_ge_atTop (max (max C₁ C₃) (max (max C₄ Cm) 4)))))))
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 40 * |C₁| * max C₂ 0 * |Cm| + 120 * |u| * |C₄| := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    positivity
  refine ⟨max x₀ (2 * K ^ 2), fun x hx => ?_⟩
  obtain ⟨a1, a3, a4, a5, a6⟩ := hx₀ x ((le_max_left _ _).trans hx)
  have hxC₁ : C₁ ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans a6)
  have hxC₃ : C₃ ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans a6)
  have hxC₄ : C₄ ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans a6))
  have hxCm : Cm ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans a6))
  have hx4 : (4 : ℝ) ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans a6)
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hL2 : 2 ≤ Real.log x := a1
  have hL1 : 1 ≤ Real.log x := by linarith
  have hL0 : 0 ≤ Real.log x := by linarith
  have hLpos : 0 < Real.log x := by linarith
  have hT : 1 ≤ Real.log x ^ D := Real.one_le_rpow hL1 hD0
  have hpow : ∀ n : ℕ, (Real.log x ^ D) ^ n = Real.log x ^ ((n : ℝ) * D) := fun n => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0, mul_comm]
  have hP2 : Real.log x ^ (2 * D) = (Real.log x ^ D) ^ 2 := by
    rw [hpow 2]
    norm_num
  have hP4 : Real.log x ^ (4 * D) = (Real.log x ^ D) ^ 4 := by
    rw [hpow 4]
    norm_num
  have hP8 : Real.log x ^ (8 * D) = (Real.log x ^ D) ^ 8 := by
    rw [hpow 8]
    norm_num
  have hY0 : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hx0 _
  have hY1 : 1 ≤ x ^ (11 / 20 + ε) := Real.one_le_rpow hx1 hθ.le
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hL0 _),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at a3 a4 a5
  have hQr : ((x ^ (11 / 20 + ε)) ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ (1 / 2 : ℝ) = x ^ δ₁ := by
    rw [← Real.rpow_mul hx0.le, ← Real.rpow_mul hx0.le, hδ₁]
  have hxδ : x ^ (11 / 20 + ε - δ₁) * x ^ δ₁ = x ^ (11 / 20 + ε) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hxδ0 : 0 ≤ x ^ δ₁ := Real.rpow_nonneg hx0.le _
  have hQhi : ((⌊x ^ δ₁ / 2⌋₊ : ℕ) : ℝ) ≤ x ^ δ₁ / 2 := Nat.floor_le (by positivity)
  have hQlo : x ^ δ₁ / 2 < ((⌊x ^ δ₁ / 2⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [hQr, hP2, hP4]
  rw [hP2] at a3
  rw [hP8] at a4
  rw [hP4] at a5
  have hT2 : 1 ≤ (Real.log x ^ D) ^ 2 := one_le_pow₀ hT
  have hc1 : 2 * (Real.log x ^ D) ^ 2 ≤ ((⌊x ^ δ₁ / 2⌋₊ : ℕ) : ℝ) := by linarith
  have hc2 : 2 * (Real.log x ^ D) ^ 8 < x ^ (11 / 20 + ε) := by linarith
  have hc3 : (Real.log x ^ D) ^ 4 * ((⌊x ^ δ₁ / 2⌋₊ : ℕ) : ℝ) ≤ x ^ (11 / 20 + ε) := by
    calc
      _ ≤ (1 * x ^ (11 / 20 + ε - δ₁)) * x ^ δ₁ :=
        mul_le_mul a5 (by linarith) (Nat.cast_nonneg _) (by positivity)
      _ = _ := by rw [one_mul, hxδ]
  have hmin : min ⌊x ^ δ₁ / 2⌋₊ ⌊(Real.log x ^ D) ^ 2⌋₊ = ⌊(Real.log x ^ D) ^ 2⌋₊ := by
    apply min_eq_right
    have h5 : ((⌊(Real.log x ^ D) ^ 2⌋₊ : ℕ) : ℝ) ≤ ((⌊x ^ δ₁ / 2⌋₊ : ℕ) : ℝ) :=
      (Nat.floor_le (by positivity)).trans (by linarith)
    exact_mod_cast h5
  rw [hmin]
  generalize ⌊x ^ δ₁ / 2⌋₊ = Q at hc1 hc3 ⊢
  -- the data at x
  have h1x := h1 x hxC₁
  have h3x := h3 x hxC₃
  have h4x := h4 x hxC₄
  have hmomx := hmom x hxCm
  have hqA : ∀ q ∈ Finset.Icc 1 ⌊(Real.log x ^ D) ^ 2⌋₊,
      1 ≤ q ∧ (q : ℝ) < Real.log x ^ A' := by
    intro q hq
    have hq1 := Finset.mem_Icc.mp hq
    refine ⟨hq1.1, ?_⟩
    calc
      (q : ℝ) ≤ ((⌊(Real.log x ^ D) ^ 2⌋₊ : ℕ) : ℝ) := by exact_mod_cast hq1.2
      _ ≤ (Real.log x ^ D) ^ 2 := Nat.floor_le (by positivity)
      _ = Real.log x ^ (2 * D) := hP2.symm
      _ < Real.log x ^ A' :=
        Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith [abs_nonneg c])
  have hnI : ((⌊x⌋₊ - ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) ≤ 3 * x ^ (11 / 20 + ε) := by
    have h5 : ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor (by linarith)
    rw [Nat.cast_sub h5]
    have h6 := Nat.floor_le hx0.le
    have h7 := Nat.lt_floor_add_one (x - 2 * x ^ (11 / 20 + ε))
    linarith
  have hnJ : ((⌊2 * x ^ (11 / 20 + ε)⌋₊ - ⌊x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) ≤
      3 * x ^ (11 / 20 + ε) := by
    have h5 : ⌊x ^ (11 / 20 + ε)⌋₊ ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ :=
      Nat.floor_le_floor (by linarith)
    rw [Nat.cast_sub h5]
    have h6 := Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * x ^ (11 / 20 + ε))
    have h7 := Nat.lt_floor_add_one (x ^ (11 / 20 + ε))
    linarith
  have hsupp : ∀ q ∈ Finset.Icc 1 ⌊(Real.log x ^ D) ^ 2⌋₊,
      ∀ k ∈ Finset.Ioc ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊, a x k ≠ 0 → Nat.Coprime k q := by
    intro q hq k _ hak
    apply support_coprime512j (Real.log x ^ A') k q (hqA q hq).1 (hqA q hq).2
    by_contra hne
    exact hak (h3x k hne)
  have hLA : 0 ≤ Real.log x ^ (-A') := Real.rpow_nonneg hL0 _
  have h1' : ∀ q ∈ Finset.Icc 1 ⌊(Real.log x ^ D) ^ 2⌋₊, ∀ χ : DirichletCharacter ℂ q,
      ∀ t : ℝ, t ≤ x →
      ‖∑ k ∈ (Finset.Ioc ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊).filter (fun k : ℕ => (k : ℝ) ≤ t),
        (a x k * χ (k : ZMod q) - Thm2.delta χ * ((u : ℂ) / (Real.log x : ℂ)))‖ ≤
        |C₁| * x ^ (11 / 20 + ε) * Real.log x ^ (-A') := by
    intro q hq χ t ht
    have h5 := h1x q (hqA q hq).1 (hqA q hq).2.le χ t ht
    rw [mul_div_assoc] at h5
    refine h5.trans ?_
    gcongr
    exact le_abs_self _
  have h4' : ∀ q ∈ Finset.Icc 1 ⌊(Real.log x ^ D) ^ 2⌋₊, ∀ χ : DirichletCharacter ℂ q,
      ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
      ‖∑ m ∈ (Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊).filter
          (fun m : ℕ => (m : ℝ) ≤ t),
        (b x m * χ (m : ZMod q) -
          Thm2.delta χ * ((v : ℂ) / (Real.log (x ^ (11 / 20 + ε)) : ℂ)))‖ ≤
        |C₄| * x ^ (11 / 20 + ε) * Real.log x ^ (-A') := by
    intro q hq χ t ht
    have h5 := h4x q (hqA q hq).1 (hqA q hq).2.le χ t ht
    rw [mul_div_assoc] at h5
    refine h5.trans ?_
    gcongr
    exact le_abs_self _
  have hV : ∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊, ‖b x m‖ ≤
      max C₂ 0 * (|Cm| * x ^ (11 / 20 + ε) * Real.log x ^ c) := by
    calc
      _ ≤ ∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
          max C₂ 0 * ((m.divisors.card : ℕ) : ℝ) ^ B := by
        apply Finset.sum_le_sum
        intro m _
        refine (h2 x m).2.trans ?_
        exact mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = max C₂ 0 * ∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
          ((m.divisors.card : ℕ) : ℝ) ^ B := by rw [Finset.mul_sum]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
        refine hmomx.trans ?_
        have h5 : 0 ≤ Real.log x ^ c := Real.rpow_nonneg hL0 _
        gcongr
        exact le_abs_self _
  -- the bound for one frequency
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = Real.log x ^ (-A - 7) := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ := by
    rw [hΛ]
    exact Real.rpow_nonneg hL0 _
  have hΛ1 : Λ ≤ 1 := by
    rw [hΛ]
    exact Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have hW : ‖(u : ℂ) / (Real.log x : ℂ)‖ ≤ |u| := by
    rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hLpos]
    exact div_le_self (abs_nonneg u) hL1
  have hE1 : (Real.log x ^ D) ^ 12 * Real.log x ^ (-A') * Real.log x ^ c ≤ Λ := by
    rw [hpow 12, ← Real.rpow_add hLpos, ← Real.rpow_add hLpos, hΛ]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    push_cast
    linarith [le_abs_self c]
  have hE2 : (Real.log x ^ D) ^ 16 * Real.log x ^ (-A') ≤ Λ := by
    rw [hpow 16, ← Real.rpow_add hLpos, hΛ]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    push_cast
    linarith [abs_nonneg c]
  have hBd : 40 * (Real.log x ^ D) ^ 12 * (|C₁| * x ^ (11 / 20 + ε) * Real.log x ^ (-A')) *
        (max C₂ 0 * (|Cm| * x ^ (11 / 20 + ε) * Real.log x ^ c)) / x ^ (11 / 20 + ε) +
      120 * ‖(u : ℂ) / (Real.log x : ℂ)‖ * (Real.log x ^ D) ^ 16 *
        (|C₄| * x ^ (11 / 20 + ε) * Real.log x ^ (-A')) ≤ K * x ^ (11 / 20 + ε) * Λ := by
    have h5 : 40 * (Real.log x ^ D) ^ 12 * (|C₁| * x ^ (11 / 20 + ε) * Real.log x ^ (-A')) *
        (max C₂ 0 * (|Cm| * x ^ (11 / 20 + ε) * Real.log x ^ c)) / x ^ (11 / 20 + ε) =
        40 * |C₁| * max C₂ 0 * |Cm| * x ^ (11 / 20 + ε) *
          ((Real.log x ^ D) ^ 12 * Real.log x ^ (-A') * Real.log x ^ c) := by
      field_simp
    have h6 : 120 * ‖(u : ℂ) / (Real.log x : ℂ)‖ * (Real.log x ^ D) ^ 16 *
        (|C₄| * x ^ (11 / 20 + ε) * Real.log x ^ (-A')) =
        120 * ‖(u : ℂ) / (Real.log x : ℂ)‖ * |C₄| * x ^ (11 / 20 + ε) *
          ((Real.log x ^ D) ^ 16 * Real.log x ^ (-A')) := by ring
    rw [h5, h6, hK]
    have h7 : 40 * |C₁| * max C₂ 0 * |Cm| * x ^ (11 / 20 + ε) *
          ((Real.log x ^ D) ^ 12 * Real.log x ^ (-A') * Real.log x ^ c) ≤
        40 * |C₁| * max C₂ 0 * |Cm| * x ^ (11 / 20 + ε) * Λ :=
      mul_le_mul_of_nonneg_left hE1 (by positivity)
    have h8 : 120 * ‖(u : ℂ) / (Real.log x : ℂ)‖ * |C₄| * x ^ (11 / 20 + ε) *
          ((Real.log x ^ D) ^ 16 * Real.log x ^ (-A')) ≤
        120 * |u| * |C₄| * x ^ (11 / 20 + ε) * Λ := by
      have h9 : (Real.log x ^ D) ^ 16 * Real.log x ^ (-A') ≥ 0 := by positivity
      gcongr
    linarith [h7, h8]
  have hN : ∀ N : ℕ, ‖(∫ t in Ioc (1 / (Q : ℝ)) (1 + 1 / (Q : ℝ)) ∩
            ⋃ q ∈ Finset.Icc 1 ⌊(Real.log x ^ D) ^ 2⌋₊,
              ⋃ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
                Icc ((r : ℝ) / q - (Real.log x ^ D) ^ 4 / (q * x ^ (11 / 20 + ε)))
                  ((r : ℝ) / q + (Real.log x ^ D) ^ 4 / (q * x ^ (11 / 20 + ε))),
            (∑ k ∈ Finset.Ioc ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊,
                a x k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) *
              (∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
                b x m * @fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ))) *
                @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))) -
          u * v / (Real.log x * Real.log (x ^ (11 / 20 + ε))) *
            ∑ q ∈ Finset.Icc 1 ⌊(Real.log x ^ D) ^ 2⌋₊,
              (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
                (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
                  @fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ))) *
                ∫ t in (-((Real.log x ^ D) ^ 4 / (q * x ^ (11 / 20 + ε))))..
                  ((Real.log x ^ D) ^ 4 / (q * x ^ (11 / 20 + ε))),
                  (∑ k ∈ Finset.Ioc ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊,
                      (1 : ℂ) * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) *
                    (∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
                      (1 : ℂ) * @fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ))) *
                      @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))‖ ≤
        K * x ^ (11 / 20 + ε) * Λ := by
    intro N
    have key := major_fixed512j (Real.log x ^ D) (x ^ (11 / 20 + ε)) hT hY0 Q
      ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊ ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊
      (a x) (b x) ((u : ℂ) / (Real.log x : ℂ))
      ((v : ℂ) / (Real.log (x ^ (11 / 20 + ε)) : ℂ))
      (|C₁| * x ^ (11 / 20 + ε) * Real.log x ^ (-A'))
      (|C₄| * x ^ (11 / 20 + ε) * Real.log x ^ (-A'))
      (max C₂ 0 * (|Cm| * x ^ (11 / 20 + ε) * Real.log x ^ c)) x (2 * x ^ (11 / 20 + ε)) N
      (Nat.floor_le hx0.le) (Nat.floor_le (by linarith)) hnI hnJ hc1 hc2 hc3 hsupp h1' h4' hV
    rw [div_mul_div_comm] at key
    exact key.trans hBd
  -- the sum over the frequencies
  have hH1 : 1 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) :=
    Real.one_le_rpow hx1 (mul_nonneg hθ.le hθ₂.1.le)
  have hcard : (((Finset.Icc ⌈x⌉₊
      ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
        (fun N => Even N)).card : ℝ) ≤
      2 * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) := by
    have h5 : (((Finset.Icc ⌈x⌉₊
        ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
          (fun N => Even N)).card : ℝ) ≤
        ((⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊ + 1 - ⌈x⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
    refine h5.trans ?_
    by_cases hle : ⌈x⌉₊ ≤ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊ + 1
    · rw [Nat.cast_sub hle]
      push_cast
      have h6 := Nat.floor_le (by linarith :
        (0 : ℝ) ≤ x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))))
      have h7 := Nat.le_ceil x
      linarith
    · rw [Nat.sub_eq_zero_of_le (not_le.mp hle).le]
      simp only [Nat.cast_zero]
      linarith
  rw [← hΛ]
  generalize x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) = H at hH1 hcard ⊢
  have hKY : 0 ≤ K * x ^ (11 / 20 + ε) * Λ := by positivity
  calc
    _ ≤ ∑ _N ∈ (Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊).filter (fun N => Even N),
        (K * x ^ (11 / 20 + ε) * Λ) ^ 2 :=
      Finset.sum_le_sum fun N _ => pow_le_pow_left₀ (norm_nonneg _) (hN N) 2
    _ = (((Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊).filter (fun N => Even N)).card : ℝ) *
        (K * x ^ (11 / 20 + ε) * Λ) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * H) * (K * x ^ (11 / 20 + ε) * Λ) ^ 2 :=
      mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = (2 * K ^ 2) * (H * (x ^ (11 / 20 + ε)) ^ 2 * (Λ * Λ)) := by ring
    _ ≤ (2 * K ^ 2) * (H * (x ^ (11 / 20 + ε)) ^ 2 * Λ) := by
      have h5 : Λ * Λ ≤ Λ := by nlinarith
      have h6 : 0 ≤ H * (x ^ (11 / 20 + ε)) ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 h6) (by positivity)
    _ ≤ max x₀ (2 * K ^ 2) * (H * (x ^ (11 / 20 + ε)) ^ 2 * Λ) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end LeanLab.BHP1997.Route512Major
