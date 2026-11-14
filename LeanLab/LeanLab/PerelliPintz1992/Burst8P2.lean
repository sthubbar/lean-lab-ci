/-
P0070. A. Perelli and J. Pintz, On the exceptional set for the 2k-twin primes problem,
Compositio Math. 82, 1992, pp. 355 to 372.

ROUTE BURST session 8, part 2, 2026-11-12. The Section 4 leaf `Burst4Split.major_arcs_estimate6`
split further along pp. 359 to 362:

* `siegel_walfisz_uniform`, proved from PNTPort, display 16, p. 361: the Siegel and Walfisz theorem,
  Davenport, Multiplicative Number Theory, Ch. 22, eqs 2 and 3, in residue class form.
* `shiu_d2`, LEAF, CITED: Theorem 2 of reference 12, P. Shiu, J. reine angew. Math. 313, 1980,
  as used on p. 362 for the first term of display 20.
* PROVED here: the window form of the Siegel and Walfisz input `hAP_of_SW`, the bound
  `R ≪ N L^{-D}` of display 18 from `Decomp1519.R_bound`, the bound on `E19`, that is
  `R₁ + R₂ + R₃` of display 12, the Shiu sum over the block, the overhang `N < 2k ≤ N + 2H`
  of the wide range, `overhang_estimate6`, through `T_orth_high`, `arc_integral_bound_high`,
  `eq19_high` and `S2k_le_divisors`, and the asymptotic assembly `estimate6Wide_of_split` of
  `Estimate6Wide` from `Decomp1519.estimate6_explicit`. So display 6 is CONDITIONAL ON
  the cited Shiu theorem only.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.PerelliPintz1992.Burst4Split
import LeanLab.PerelliPintz1992.Decomp544b
import LeanLab.PerelliPintz1992.Decomp1519
import LeanLab.VanDerCorput1939.Totient
import LeanLab.PerelliPintz1992.DivisorBound

namespace LeanLab.PerelliPintz1992.Burst8P2
open Real ArithmeticFunction MeasureTheory Set Filter Topology
open LeanLab.PerelliPintz1992 LeanLab.PerelliPintz1992.Decomp1519

noncomputable section

/-! ### Cited inputs -/

/-- `ψ(x; q, b) = Σ_{n ≤ x, n ≡ b mod q} Λ(n)`, for a residue `b < q`. -/
def psiAP (x q b : ℕ) : ℝ := ∑ n ∈ Finset.Ioc 0 x, if n % q = b then Λ n else 0

/-- Display 16, p. 361, the Siegel and Walfisz theorem, Davenport, Multiplicative Number
Theory, Ch. 22, eqs 2 and 3: for every `D, A' > 0`,
`ψ(x; q, b) = x/φ(q) + O(x exp(-c √log x))` uniformly for `q ≤ (log x)^D`, `(b, q) = 1`.
Read here in the standard uniform form `|ψ(x; q, b) - x/φ(q)| ≤ C Y (log Y)^{-A'}` for every
`x ≤ Y` and `q ≤ (log Y)^D`: the proof uses the existing PNTPort theorem and an elementary uniform cutoff conversion.
The small cutoff branch uses the finite bound psi at most x log Y. -/
theorem siegel_walfisz_uniform : ∀ D A' : ℝ, 0 < D → 0 < A' → ∃ C : ℝ, 0 ≤ C ∧
    ∀ Y : ℕ, 2 ≤ Y → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ L Y ^ D → ∀ b : ℕ, b < q →
      Nat.Coprime b q → ∀ x : ℕ, x ≤ Y →
        |psiAP x q b - x / (Nat.totient q : ℝ)| ≤ C * Y / L Y ^ A' := by
  intro D A hD hA
  obtain ⟨C, hC, hbound⟩ := Decomp544b.siegel_walfisz_uniform D A hD hA
  refine ⟨C, hC, ?_⟩
  intro Y hY q hq hqY b hb hcop x hx
  have heq : psiAP x q b = LeanLab.HeathBrown1985.psi x q b := by
    classical
    unfold psiAP LeanLab.HeathBrown1985.psi
    simp only [Nat.floor_natCast, Nat.mod_eq_of_lt hb, Finset.sum_filter]
    apply Finset.sum_congr
    · ext n
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    · intro n hn
      rfl
  rw [heq]
  exact hbound Y hY q hq hqY b hb hcop x hx

/-- LEAF: p. 362, first term of display 20, CITED, Theorem 2 of reference 12, P. Shiu, A
Brun-Titchmarsh theorem for multiplicative functions, J. reine angew. Math. 313, 1980,
pp. 161 to 170, for `f = d²`, so that `Σ_p f(p)/p = 4 log log x + O(1)`, with `β = 1/3`:
`Σ_{x-y < n ≤ x} d(n)² ≪ y (log x)³` for `x^{1/3} ≤ y`; for `y > x` the interval is cut at 0.
Not proved here. -/
theorem shiu_d2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℕ, 2 ≤ x → x ≤ y ^ 3 →
    ∑ n ∈ Finset.Ioc (x - y) x, ((n.divisors.card : ℝ)) ^ 2 ≤ C * y * Real.log x ^ 3 := by
  sorry

/-! ### The window form of display 16, PROVED -/

/-- From the uniform Siegel and Walfisz bound at `Y = 2N`, the hypothesis `hAP` of
`Decomp1519.R_bound` holds with `E = 4 C N / L^{A'}`: the window `[N, N + t]` is a difference
of two values of `ψ(x; q, b) - x/φ(q)`. p. 361, displays 15 and 16. PROVED. -/
theorem hAP_of_SW {D A' C : ℝ}
    (hSW : ∀ Y : ℕ, 2 ≤ Y → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ L Y ^ D → ∀ b : ℕ, b < q →
      Nat.Coprime b q → ∀ x : ℕ, x ≤ Y →
        |psiAP x q b - x / (Nat.totient q : ℝ)| ≤ C * Y / L Y ^ A')
    (hC : 0 ≤ C) (hA' : 0 ≤ A') {N q : ℕ} (hN : 2 ≤ N) (hq : 1 ≤ q)
    (hqD : (q : ℝ) ≤ L ((2 * N : ℕ) : ℝ) ^ D) :
    ∀ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q), ∀ t ≤ N,
      ‖∑ n ∈ Finset.Icc N (N + t), (((if n % q = b then Λ n else 0 : ℝ) : ℂ) -
        ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ))‖ ≤ 4 * C * N / L N ^ A' := by
  intro b hb t ht
  rw [Finset.mem_filter, Finset.mem_range] at hb
  obtain ⟨hbq, hcop⟩ := hb
  set f : ℕ → ℝ := fun n => (if n % q = b then Λ n else 0) - 1 / (Nat.totient q : ℝ) with hf
  have hcast : ∑ n ∈ Finset.Icc N (N + t), (((if n % q = b then Λ n else 0 : ℝ) : ℂ) -
      ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ)) = ((∑ n ∈ Finset.Icc N (N + t), f n : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [f, Complex.ofReal_sub]
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  have hIcc : Finset.Icc N (N + t) = Finset.Ioc (N - 1) (N + t) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hsplit : ∑ n ∈ Finset.Ioc (N - 1) (N + t), f n =
      ∑ n ∈ Finset.Ioc 0 (N + t), f n - ∑ n ∈ Finset.Ioc 0 (N - 1), f n := by
    rw [← Finset.sum_Ioc_consecutive f (Nat.zero_le (N - 1)) (by omega : N - 1 ≤ N + t)]
    ring
  have hpsi : ∀ x : ℕ, ∑ n ∈ Finset.Ioc 0 x, f n = psiAP x q b - x / (Nat.totient q : ℝ) := by
    intro x
    simp only [f, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ioc, psiAP, nsmul_eq_mul,
      Nat.sub_zero]
    ring
  rw [hIcc, hsplit, hpsi, hpsi]
  have hY : 2 ≤ 2 * N := by omega
  have h1 := hSW (2 * N) hY q hq hqD b hbq hcop (N + t) (by omega)
  have h2 := hSW (2 * N) hY q hq hqD b hbq hcop (N - 1) (by omega)
  have hL := L_pos hN
  have hLle : L N ≤ L ((2 * N : ℕ) : ℝ) := by
    unfold L
    have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    exact Real.log_le_log this (by push_cast; linarith)
  have hpow : L N ^ A' ≤ L ((2 * N : ℕ) : ℝ) ^ A' := Real.rpow_le_rpow hL.le hLle hA'
  have hpos : 0 < L N ^ A' := Real.rpow_pos_of_pos hL _
  have hmono : C * ((2 * N : ℕ) : ℝ) / L ((2 * N : ℕ) : ℝ) ^ A' ≤
      C * ((2 * N : ℕ) : ℝ) / L N ^ A' :=
    div_le_div_of_nonneg_left (by positivity) hpos hpow
  have hcast2 : C * ((2 * N : ℕ) : ℝ) / L N ^ A' = 2 * C * N / L N ^ A' := by
    push_cast; ring
  calc |psiAP (N + t) q b - ((N + t : ℕ) : ℝ) / (Nat.totient q : ℝ) -
        (psiAP (N - 1) q b - ((N - 1 : ℕ) : ℝ) / (Nat.totient q : ℝ))|
      ≤ |psiAP (N + t) q b - ((N + t : ℕ) : ℝ) / (Nat.totient q : ℝ)| +
        |psiAP (N - 1) q b - ((N - 1 : ℕ) : ℝ) / (Nat.totient q : ℝ)| := abs_sub _ _
    _ ≤ 2 * C * N / L N ^ A' + 2 * C * N / L N ^ A' := by
        rw [← hcast2]; exact add_le_add (h1.trans hmono) (h2.trans hmono)
    _ = 4 * C * N / L N ^ A' := by ring

/-! ### Display 18, PROVED: `R ≪ N L^{-D}` on the major arcs -/

/-- The algebra of display 18: with `φ ≤ q ≤ P ≤ v`, `q |η| N ≤ v`, `E = 4 C N/(u v ℓ)`,
`log 2N ≤ 2ℓ`, `128 C ≤ ℓ` and `16 P ℓ² u ≤ N`, the bound of `R_bound` is at most `N/u`.
PROVED. -/
theorem rho_alg {φ q P v u ℓ C N η lg : ℝ} (hφ0 : 0 ≤ φ) (hφq : φ ≤ q) (hqP : q ≤ P)
    (hPv : P ≤ v) (hq0 : 0 ≤ q) (hηv : q * (|η| * N) ≤ v) (hu : 0 < u) (hv : 0 < v)
    (hℓ : 0 < ℓ) (hC : 0 ≤ C) (hN : 0 ≤ N) (hlg0 : 0 ≤ lg) (hlg : lg ≤ 2 * ℓ)
    (hCℓ : 128 * C ≤ ℓ) (hbig : 16 * P * ℓ ^ 2 * u ≤ N) :
    φ * ((1 + 2 * π * |η| * N) * (4 * C * N / (u * v * ℓ))) + 2 * q * lg ^ 2 ≤ N / u := by
  have hηN : 0 ≤ |η| * N := mul_nonneg (abs_nonneg _) hN
  have hπ : π < 4 := Real.pi_lt_four
  have h1 : φ * (1 + 2 * π * |η| * N) ≤ 9 * v := by
    have : φ * (1 + 2 * π * |η| * N) ≤ q * (1 + 2 * π * |η| * N) :=
      mul_le_mul_of_nonneg_right hφq (by positivity)
    have h2 : q * (1 + 2 * π * |η| * N) = q + 2 * π * (q * (|η| * N)) := by ring
    nlinarith [Real.pi_pos]
  have hE0 : 0 ≤ 4 * C * N / (u * v * ℓ) := by positivity
  have hA : φ * ((1 + 2 * π * |η| * N) * (4 * C * N / (u * v * ℓ))) ≤ N / (2 * u) := by
    rw [← mul_assoc]
    calc φ * (1 + 2 * π * |η| * N) * (4 * C * N / (u * v * ℓ))
        ≤ 9 * v * (4 * C * N / (u * v * ℓ)) := mul_le_mul_of_nonneg_right h1 hE0
      _ = 36 * C * N / (u * ℓ) := by field_simp; ring
      _ ≤ N / (2 * u) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h3 := mul_le_mul_of_nonneg_left hCℓ (mul_nonneg hN hu.le)
        have h4 := mul_nonneg (mul_nonneg hC hN) hu.le
        nlinarith
  have hB : 2 * q * lg ^ 2 ≤ N / (2 * u) := by
    have hlg2 : lg ^ 2 ≤ 4 * ℓ ^ 2 := by nlinarith
    have : 2 * q * lg ^ 2 ≤ 8 * P * ℓ ^ 2 := by
      have := mul_le_mul hqP hlg2 (sq_nonneg _) (by linarith)
      linarith
    refine this.trans ?_
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have : N / (2 * u) + N / (2 * u) = N / u := by field_simp; ring
  linarith

/-- `ℓ^{(B/4) n} = (ℓ^{B/4})^n`. -/
lemma rpow_quarter {ℓ : ℝ} (hℓ : 0 < ℓ) (B : ℝ) (n : ℕ) :
    ℓ ^ (B / 4 * n) = (ℓ ^ (B / 4)) ^ n := Real.rpow_mul_natCast hℓ.le _ _

lemma rpow_half_eq {ℓ : ℝ} (hℓ : 0 < ℓ) (B : ℝ) : ℓ ^ (B / 2) = (ℓ ^ (B / 4)) ^ 2 := by
  rw [← rpow_quarter hℓ]; congr 1; push_cast; ring

lemma rpow_full_eq {ℓ : ℝ} (hℓ : 0 < ℓ) (B : ℝ) : ℓ ^ B = (ℓ ^ (B / 4)) ^ 4 := by
  rw [← rpow_quarter hℓ]; congr 1; push_cast; ring

/-- Display 18, p. 362: from the uniform Siegel and Walfisz bound with `D = B/2` and
`A' = 7B/4 + B + 1`, `|R(η, q, a)| ≤ N L^{-7B/4}` on every major arc, once `ℓ = L ≥ 128 C`
and `16 L^{9B/4 + 2} ≤ N`. From `Decomp1519.R_bound`, `hAP_of_SW` and `rho_alg`. PROVED. -/
theorem R_small {A C : ℝ} (hA : 0 < A) (hC : 0 ≤ C)
    (hSW : ∀ Y : ℕ, 2 ≤ Y → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ L Y ^ (Bexp A / 2) → ∀ b : ℕ, b < q →
      Nat.Coprime b q → ∀ x : ℕ, x ≤ Y →
        |psiAP x q b - x / (Nat.totient q : ℝ)| ≤
          C * Y / L Y ^ (7 * (Bexp A / 4) + Bexp A + 1))
    {N : ℕ} (hN : 3 ≤ N) (hℓ1 : 1 ≤ L N) (hCℓ : 128 * C ≤ L N)
    (hbig : 16 * (L N ^ (Bexp A / 4)) ^ 2 * L N ^ 2 * (L N ^ (Bexp A / 4)) ^ 7 ≤ N) :
    ∀ q ∈ Qs N A, ∀ a ∈ As q, ∀ η ∈ Ioo (-wq N A q) (wq N A q),
      ‖R N q a η‖ ≤ N / (L N ^ (Bexp A / 4)) ^ 7 := by
  intro q hq a ha η hη
  have hB : 0 < Bexp A := by unfold Bexp; linarith
  have hℓ : 0 < L N := by linarith
  set ℓ := L N with hℓdef
  set r := ℓ ^ (Bexp A / 4) with hr
  have hr1 : 1 ≤ r := Real.one_le_rpow hℓ1 (by linarith)
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
  have hqQ : (q : ℝ) ≤ r ^ 2 := by
    have h := (Finset.mem_Icc.mp hq).2
    have h2 : (q : ℝ) ≤ ℓ ^ (Bexp A / 2) :=
      (Nat.cast_le.mpr h).trans (Nat.floor_le (Real.rpow_nonneg hℓ.le _))
    rwa [rpow_half_eq hℓ] at h2
  have hcop : Nat.Coprime a q := (Finset.mem_filter.mp ha).2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hqD : (q : ℝ) ≤ L ((2 * N : ℕ) : ℝ) ^ (Bexp A / 2) := by
    have h1 : ℓ ≤ L ((2 * N : ℕ) : ℝ) := by
      simp only [hℓdef, L]
      exact Real.log_le_log hNpos (by push_cast; linarith)
    have h2 : ℓ ^ (Bexp A / 2) ≤ L ((2 * N : ℕ) : ℝ) ^ (Bexp A / 2) :=
      Real.rpow_le_rpow hℓ.le h1 (by linarith)
    rw [rpow_half_eq hℓ] at h2
    exact hqQ.trans h2
  have hAP := hAP_of_SW hSW hC (by linarith) (by omega : 2 ≤ N) hq1 hqD
  have hR := R_bound N q a (by omega) hq1 hcop η _ hAP
  refine hR.trans ?_
  have hpowA : L N ^ (7 * (Bexp A / 4) + Bexp A + 1) = r ^ 7 * r ^ 4 * ℓ := by
    rw [Real.rpow_add hℓ, Real.rpow_add hℓ, Real.rpow_one,
      show 7 * (Bexp A / 4) = Bexp A / 4 * ((7 : ℕ) : ℝ) by push_cast; ring,
      rpow_quarter hℓ (Bexp A) 7, rpow_full_eq hℓ (Bexp A)]
  rw [hpowA]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hw : wq N A q = r ^ 4 / (q * N) := by
    unfold wq; rw [rpow_full_eq hℓ]
  have hηv : (q : ℝ) * (|η| * N) ≤ r ^ 4 := by
    have h := abs_lt.mpr ⟨hη.1, hη.2⟩
    rw [hw, lt_div_iff₀ (by positivity)] at h
    nlinarith [abs_nonneg η]
  have hlg : Real.log (2 * N) ≤ 2 * ℓ := by
    simp only [hℓdef, L]
    rw [Real.log_mul (by norm_num) hNpos.ne']
    have : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ N))
    linarith
  have hlg0 : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith [show (1 : ℝ) ≤ N by exact_mod_cast (by omega : 1 ≤ N)])
  have hφq : (Nat.totient q : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hPv : r ^ 2 ≤ r ^ 4 := pow_le_pow_right₀ hr1 (by norm_num)
  have := rho_alg (φ := (Nat.totient q : ℝ)) (q := q) (P := r ^ 2) (v := r ^ 4) (u := r ^ 7)
    (ℓ := ℓ) (C := C) (N := N) (η := η) (lg := Real.log (2 * N)) (by positivity) hφq hqQ hPv
    hq0.le hηv (by positivity) (by positivity) hℓ hC hNpos.le hlg0 hlg hCℓ hbig
  convert this using 3

/-! ### Display 12, PROVED: `R₁ + R₂ + R₃ ≪ N L^{-B/4}` -/

/-- The per modulus algebra of `E19`: with `c ≤ q`, `m φ² ≤ 1`, `q³ ≤ 16 φ⁴`, `q ≤ r²`,
`ρ ≤ N r^{-7}`, the term of modulus `q` is at most `10 N r^{-3}`. PROVED. -/
theorem term_alg {c m μa q φ N r ρ : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ q) (hm0 : 0 ≤ m)
    (hm : m * φ ^ 2 ≤ 1) (hμa0 : 0 ≤ μa) (hμa : μa ≤ 1) (hq1 : 1 ≤ q) (hφ1 : 1 ≤ φ)
    (hcube : q ^ 3 ≤ 16 * φ ^ 4) (hqr : q ≤ r ^ 2) (hr : 1 ≤ r) (hN : 2 ≤ N)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ N / r ^ 7) :
    c * (m / (2 * (r ^ 4 / (q * N))) + 2 * (r ^ 4 / (q * N)) * (ρ ^ 2 + 2 * μa * (N + 1) * ρ))
      ≤ 10 * N / r ^ 3 := by
  have hr0 : 0 < r := by linarith
  have hq0 : 0 < q := by linarith
  have hN0 : 0 < N := by linarith
  have hφ0 : 0 < φ := by linarith
  -- the first term
  have hqm : q ^ 2 * m ≤ 4 * r := by
    have h1 : (q ^ 2 * m) ^ 2 * φ ^ 4 ≤ q ^ 4 := by
      have hmm : (m * φ ^ 2) ^ 2 ≤ 1 := by
        have : 0 ≤ m * φ ^ 2 := by positivity
        nlinarith
      calc (q ^ 2 * m) ^ 2 * φ ^ 4 = q ^ 4 * (m * φ ^ 2) ^ 2 := by ring
        _ ≤ q ^ 4 := mul_le_of_le_one_right (by positivity) hmm
    have h2 : q ^ 4 ≤ 16 * q * φ ^ 4 := by
      have := mul_le_mul_of_nonneg_left hcube hq0.le
      nlinarith
    have h3 : (q ^ 2 * m) ^ 2 ≤ 16 * q := by
      have h4 : (q ^ 2 * m) ^ 2 * φ ^ 4 ≤ (16 * q) * φ ^ 4 := by linarith
      exact le_of_mul_le_mul_right h4 (by positivity)
    have h5 : (q ^ 2 * m) ^ 2 ≤ (4 * r) ^ 2 := by nlinarith
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) h5
  have hT1 : c * (m / (2 * (r ^ 4 / (q * N)))) ≤ 2 * N / r ^ 3 := by
    have he : c * (m / (2 * (r ^ 4 / (q * N)))) = (c * q * m) * N / (2 * r ^ 4) := by
      field_simp
    rw [he]
    have hcqm : c * q * m ≤ 4 * r := by
      have : c * q * m ≤ q * q * m := by
        have := mul_le_mul_of_nonneg_right hc (mul_nonneg hq0.le hm0)
        nlinarith
      nlinarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_right hcqm (mul_nonneg hN0.le (pow_nonneg hr0.le 3))
    nlinarith
  -- the second term
  have hρN : ρ ≤ N := by
    refine hρ.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ r ^ 7 := one_le_pow₀ hr
    nlinarith
  have hX : ρ ^ 2 + 2 * μa * (N + 1) * ρ ≤ 4 * N * ρ := by
    have h1 : ρ ^ 2 ≤ N * ρ := by nlinarith
    have h2 : 2 * μa * (N + 1) * ρ ≤ 2 * (N + 1) * ρ := by
      have := mul_le_mul_of_nonneg_right hμa (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * (N + 1)) hρ0)
      nlinarith
    nlinarith
  have hT2 : c * (2 * (r ^ 4 / (q * N)) * (ρ ^ 2 + 2 * μa * (N + 1) * ρ)) ≤ 8 * N / r ^ 3 := by
    set X := ρ ^ 2 + 2 * μa * (N + 1) * ρ
    have hX0 : 0 ≤ X := by positivity
    have he : c * (2 * (r ^ 4 / (q * N)) * X) = (c / q) * (2 * r ^ 4 * X / N) := by
      field_simp
    rw [he]
    have hcq : c / q ≤ 1 := (div_le_one hq0).mpr hc
    have h1 : (c / q) * (2 * r ^ 4 * X / N) ≤ 2 * r ^ 4 * X / N :=
      mul_le_of_le_one_left (by positivity) hcq
    refine h1.trans ?_
    have h2 : 2 * r ^ 4 * X / N ≤ 8 * r ^ 4 * ρ := by
      rw [div_le_iff₀ hN0]
      have := mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ 2 * r ^ 4)
      nlinarith
    refine h2.trans ?_
    have h3 : 8 * r ^ 4 * ρ ≤ 8 * r ^ 4 * (N / r ^ 7) :=
      mul_le_mul_of_nonneg_left hρ (by positivity)
    refine h3.trans (le_of_eq ?_)
    field_simp
  calc _ = c * (m / (2 * (r ^ 4 / (q * N)))) +
        c * (2 * (r ^ 4 / (q * N)) * (ρ ^ 2 + 2 * μa * (N + 1) * ρ)) := by ring
    _ ≤ 2 * N / r ^ 3 + 8 * N / r ^ 3 := add_le_add hT1 hT2
    _ = 10 * N / r ^ 3 := by ring

/-- Display 12, p. 360, in explicit form: `E19 = R₁ + R₂ + R₃` bound, `E19 ≤ 10 N/r` with
`r = L^{B/4}`, for `|R| ≤ ρ ≤ N r^{-7}`. Uses van der Corput's `q³ ≤ 16 φ(q)⁴`,
`VanDerCorput1939.cube_le_totient_pow4`, in place of `Σ_q μ²/φ ≪ L^{B/2}`. PROVED. -/
theorem E19_le {N : ℕ} {A ρ : ℝ} (hN : 2 ≤ N) (hℓ1 : 1 ≤ L N) (hA : 0 < A)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ N / (L N ^ (Bexp A / 4)) ^ 7) :
    E19 N A ρ ≤ 10 * N / L N ^ (Bexp A / 4) := by
  have hB : 0 < Bexp A := by unfold Bexp; linarith
  have hℓ : 0 < L N := by linarith
  set r := L N ^ (Bexp A / 4) with hr
  have hr1 : 1 ≤ r := Real.one_le_rpow hℓ1 (by linarith)
  have hr0 : 0 < r := by linarith
  set Q0 := ⌊L N ^ (Bexp A / 2)⌋₊ with hQ0
  have hQr : (Q0 : ℝ) ≤ r ^ 2 := by
    rw [← rpow_half_eq hℓ]; exact Nat.floor_le (Real.rpow_nonneg hℓ.le _)
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  unfold E19
  have hper : ∀ q ∈ Qs N A, ((As q).card : ℝ) * errB N A ρ q ≤ 10 * N / r ^ 3 := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqQ : (q : ℝ) ≤ r ^ 2 := (Nat.cast_le.mpr (Finset.mem_Icc.mp hq).2).trans hQr
    have hw : wq N A q = r ^ 4 / (q * N) := by unfold wq; rw [rpow_full_eq hℓ]
    unfold errB
    rw [hw]
    have hφ1 : (1 : ℝ) ≤ Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hcard : ((As q).card : ℝ) ≤ q := by
      have : (As q).card ≤ q := (Finset.card_filter_le _ _).trans (by simp)
      exact_mod_cast this
    have hm : muφ q ^ 2 * (Nat.totient q : ℝ) ^ 2 ≤ 1 := by
      have h := muφ_sq_le (q := q)
      rw [le_div_iff₀ (by positivity)] at h
      linarith
    have hμa : |muφ q| ≤ 1 := by
      have h := muφ_sq_le_one hq1
      rw [← sq_abs] at h
      nlinarith [abs_nonneg (muφ q)]
    have hcube : (q : ℝ) ^ 3 ≤ 16 * (Nat.totient q : ℝ) ^ 4 := by
      exact_mod_cast LeanLab.VanDerCorput1939.cube_le_totient_pow4 q (by omega)
    exact term_alg (by positivity) hcard (sq_nonneg _) hm (abs_nonneg _) hμa
      (by exact_mod_cast hq1) hφ1 hcube hqQ hr1 hNr hρ0 hρ
  refine (Finset.sum_le_sum hper).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Qs N A).card : ℝ) = Q0 := by
    unfold Qs; rw [Nat.card_Icc]; simp [hQ0]
  rw [hcard]
  calc (Q0 : ℝ) * (10 * N / r ^ 3) ≤ r ^ 2 * (10 * N / r ^ 3) :=
        mul_le_mul_of_nonneg_right hQr (by positivity)
    _ = 10 * N / r := by field_simp

lemma E19_nonneg {N : ℕ} {A ρ : ℝ} (hN : 2 ≤ N) (hρ0 : 0 ≤ ρ) : 0 ≤ E19 N A ρ := by
  unfold E19
  refine Finset.sum_nonneg fun q hq => ?_
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
  have hw := wq_pos (A := A) hN hq1
  unfold errB
  positivity

/-! ### The Shiu sum over a block, PROVED from `shiu_d2` -/

/-- p. 362, first term of display 20: `Σ_{k ∈ K} d(2k)² ≤ C (2H + 1) 8 L³` for `K` inside the
block `[V, V + H]`, `V < N/2`, `H ≤ N`, `√N ≤ 2H + 1`. PROVED from `shiu_d2`. -/
theorem shiu_block {C : ℝ} (hC : 0 ≤ C)
    (hS : ∀ x y : ℕ, 2 ≤ x → x ≤ y ^ 3 →
      ∑ n ∈ Finset.Ioc (x - y) x, ((n.divisors.card : ℝ)) ^ 2 ≤ C * y * Real.log x ^ 3)
    {N V H : ℕ} (hN : 9 ≤ N) (hV : (V : ℝ) < N / 2) (hH : (H : ℝ) ≤ N)
    (hHs : √(N : ℝ) ≤ 2 * H + 1) (K : Finset ℕ)
    (hK : K ⊆ (Finset.Icc V (V + H)).filter (1 ≤ ·)) :
    ∑ k ∈ K, (((2 * k).divisors.card : ℝ)) ^ 2 ≤ C * (2 * H + 1) * (8 * L N ^ 3) := by
  have hNr : (9 : ℝ) ≤ N := by exact_mod_cast hN
  have hsq3 : (3 : ℝ) ≤ √(N : ℝ) := by
    rw [show (3 : ℝ) = √9 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hNr
  have hH1 : 1 ≤ H := by
    by_contra h
    have : H = 0 := by omega
    subst this
    simp at hHs; linarith
  set x := 2 * (V + H) with hx
  set y := 2 * H + 1 with hy
  have hx2 : 2 ≤ x := by omega
  have hxr : (x : ℝ) ≤ 3 * N := by
    simp only [hx]; push_cast; linarith
  have hxy : x ≤ y ^ 3 := by
    have hyr : √(N : ℝ) ≤ (y : ℝ) := by simp only [hy]; push_cast; linarith
    have h1 : (N : ℝ) * √(N : ℝ) ≤ (y : ℝ) ^ 3 := by
      have hs := Real.mul_self_sqrt (show (0 : ℝ) ≤ N by positivity)
      have h0 : 0 ≤ √(N : ℝ) := Real.sqrt_nonneg _
      have : (√(N : ℝ)) ^ 3 ≤ (y : ℝ) ^ 3 := pow_le_pow_left₀ h0 hyr 3
      nlinarith
    have h2 : (x : ℝ) ≤ (y : ℝ) ^ 3 := by nlinarith
    exact_mod_cast h2
  have hsum := hS x y hx2 hxy
  have himg : ∑ k ∈ K, (((2 * k).divisors.card : ℝ)) ^ 2 =
      ∑ n ∈ K.image (fun k => 2 * k), ((n.divisors.card : ℝ)) ^ 2 := by
    rw [Finset.sum_image]
    intro a _ b _ h; simp only at h; omega
  rw [himg]
  have hsub : K.image (fun k => 2 * k) ⊆ Finset.Ioc (x - y) x := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
    have := hK hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at this
    simp only [Finset.mem_Ioc, hx, hy]
    omega
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _).trans
    (hsum.trans ?_)
  have hlog : Real.log x ≤ 2 * L N := by
    unfold L
    have hNpos : (0 : ℝ) < N := by linarith
    have h1 : Real.log x ≤ Real.log (3 * N) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < x)) hxr
    have h2 : Real.log (3 * N) ≤ Real.log ((N : ℝ) ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x))
  have h3 : Real.log x ^ 3 ≤ 8 * L N ^ 3 := by
    have := pow_le_pow_left₀ hlog0 hlog 3
    nlinarith
  have hy0 : (0 : ℝ) ≤ C * y := by positivity
  calc C * (y : ℝ) * Real.log x ^ 3 ≤ C * y * (8 * L N ^ 3) := mul_le_mul_of_nonneg_left h3 hy0
    _ = C * (2 * H + 1) * (8 * L N ^ 3) := by simp only [hy]; push_cast; ring

/-! ### The overhang `N < 2k`, split along display 9, p. 360 -/

/-- Display 9, p. 360, the full integral for `N < 2k`: `∫_{-1/2}^{1/2} |T(η)|² e(-2kη) dη = 0`,
since no `N ≤ m, n ≤ 2N` has `n - m = 2k`. The companion of `Decomp1519.T_orth`. PROVED. -/
theorem T_orth_high {N k : ℕ} (hk : N < 2 * k) :
    (∫ η in Ioc (-(1 / 2 : ℝ)) (1 / 2), ((‖T N η‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * η))) = 0 := by
  have hexpand : ∀ η : ℝ, ((‖T N η‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * η)) =
      ∑ m ∈ Finset.Icc N (2 * N), ∑ n ∈ Finset.Icc N (2 * N),
        e ((((m : ℤ) - n - 2 * k : ℤ) : ℝ) * η) := by
    intro η
    rw [Complex.ofReal_pow, ← Complex.mul_conj', T, map_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [conj_e, ← e_add, ← e_add]
    congr 1; push_cast; ring
  have horth : ∀ j : ℤ, (∫ η in (-(1/2 : ℝ))..(1/2), e ((j : ℝ) * η)) =
      if j = 0 then 1 else 0 := by
    intro j
    have hi : e (j : ℝ) = 1 := by
      unfold e
      convert Complex.exp_int_mul_two_pi_mul_I j using 1 <;> push_cast <;> ring
    have hp : Function.Periodic (fun η : ℝ => e ((j : ℝ) * η)) 1 := by
      intro η; dsimp only; rw [mul_add, e_add, mul_one, hi, mul_one]
    have hs := hp.intervalIntegral_add_eq (-(1/2 : ℝ)) 0
    norm_num at hs
    rw [hs]
    exact LeanLab.CircleOrth.integral_ee_int j
  rw [← intervalIntegral.integral_of_le (by norm_num : -(1/2 : ℝ) ≤ 1/2)]
  simp_rw [hexpand]
  rw [intervalIntegral.integral_finsetSum (fun m _ => by
    apply Continuous.intervalIntegrable
    exact continuous_finsetSum _ fun n _ => continuous_e.comp (continuous_const.mul continuous_id))]
  have hci : ∀ j : ℤ, IntervalIntegrable (fun η : ℝ => e ((j : ℝ) * η)) volume (-(1/2 : ℝ)) (1/2) :=
    fun j => (continuous_e.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [intervalIntegral.integral_finsetSum (fun (n : ℕ) _ => hci ((m : ℤ)-(n : ℤ)-2*k))]
  refine Finset.sum_eq_zero fun n hn => ?_
  rw [horth, if_neg]
  simp only [Finset.mem_Icc] at hm hn
  omega

/-- Display 9 with 10, p. 360, for `N < 2k`: the arc integral has main term 0,
`|∫_{-w}^{w} |S(a/q+η)|² e(-2kη) dη| ≤ μ²/φ²/(2w) + 2w (ρ² + 2 |μ/φ| (N+1) ρ)`.
The companion of `Decomp1519.arc_integral_bound`, same proof with `T_orth_high`. PROVED. -/
theorem arc_integral_bound_high (N k q a : ℕ) (hk : N < 2 * k) {w ρ : ℝ} (hw : 0 < w)
    (hw2 : w ≤ 1 / 2) (hρ : ∀ η ∈ Ioo (-w) w, ‖R N q a η‖ ≤ ρ) :
    ‖∫ η in Ioo (-w) w, ((‖S N ((a : ℝ) / q + η)‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * η))‖ ≤
      muφ q ^ 2 / (2 * w) + 2 * w * (ρ ^ 2 + 2 * |muφ q| * (N + 1) * ρ) := by
  set m := muφ q
  set U : Set ℝ := Ioc (-(1 / 2 : ℝ)) (1 / 2)
  set W : Set ℝ := Ioo (-w) w
  have hWU : W ⊆ U := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  set g : ℝ → ℂ := fun η => ((‖S N ((a : ℝ) / q + η)‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * η))
  set h : ℝ → ℂ := fun η => ((‖T N η‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * η))
  have hce : Continuous fun η : ℝ => e (-(2 * k * η)) :=
    continuous_e.comp (continuous_const.mul continuous_id).neg
  have hg : Continuous g := by
    refine Continuous.mul ?_ hce
    exact Complex.continuous_ofReal.comp
      (((continuous_S N).comp (continuous_const.add continuous_id)).norm.pow 2)
  have hh : Continuous h := by
    refine Continuous.mul ?_ hce
    exact Complex.continuous_ofReal.comp ((continuous_T N).norm.pow 2)
  have hWfin : volume W < ⊤ := by simp [W]
  have hhU : IntegrableOn h U volume := hh.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hhW : IntegrableOn h W volume := hhU.mono_set hWU
  have hgW : IntegrableOn g W volume :=
    (hg.integrableOn_Icc (a := -w) (b := w)).mono_set Ioo_subset_Icc_self
  have hsplit : (∫ η in U, h η) = (∫ η in W, h η) + ∫ η in U \ W, h η := by
    rw [← setIntegral_union disjoint_sdiff_self_right (measurableSet_Ioc.diff measurableSet_Ioo)
      hhW (hhU.mono_set sdiff_subset), union_sdiff_cancel hWU]
  have horth : (∫ η in U, h η) = 0 := T_orth_high hk
  have htail : ‖∫ η in U \ W, h η‖ ≤ 1 / (2 * w) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have : ∀ η, ‖h η‖ = ‖T N η‖ ^ 2 := fun η => by
      simp only [h]; rw [norm_ofReal_mul_e, abs_of_nonneg (sq_nonneg _)]
    simp_rw [this]
    exact T_tail N hw hw2
  have hdiff : ‖∫ η in W, (g η - ((m ^ 2 : ℝ) : ℂ) * h η)‖ ≤
      (ρ ^ 2 + 2 * |m| * (N + 1) * ρ) * volume.real W := by
    refine norm_setIntegral_le_of_norm_le_const hWfin fun η hη => ?_
    have hR := hρ η hη
    have e1 : g η - ((m ^ 2 : ℝ) : ℂ) * h η =
        ((‖S N ((a : ℝ) / q + η)‖ ^ 2 - m ^ 2 * ‖T N η‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * η)) := by
      simp only [g, h]; push_cast; ring
    rw [e1, norm_ofReal_mul_e]
    refine (normSq_S_sub_le N q a η).trans ?_
    have hT := norm_T_le N η
    have hR0 := norm_nonneg (R N q a η)
    have h1 : ‖R N q a η‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hR0 hR 2
    have h2 : 2 * |m| * ‖T N η‖ * ‖R N q a η‖ ≤ 2 * |m| * (N + 1) * ρ := by
      have := mul_le_mul hT hR hR0 (by positivity)
      nlinarith [abs_nonneg m]
    linarith
  have hvol : volume.real W = 2 * w := by
    simp only [W, Measure.real, Real.volume_Ioo]
    rw [ENNReal.toReal_ofReal (by linarith)]; ring
  rw [hvol] at hdiff
  have hgsplit : (∫ η in W, g η) = (∫ η in W, (g η - ((m ^ 2 : ℝ) : ℂ) * h η)) +
      ((m ^ 2 : ℝ) : ℂ) * ∫ η in W, h η := by
    rw [integral_sub hgW (hhW.const_mul _), integral_const_mul]; ring
  have hkey : (∫ η in W, g η) = (∫ η in W, (g η - ((m ^ 2 : ℝ) : ℂ) * h η)) -
        ((m ^ 2 : ℝ) : ℂ) * ∫ η in U \ W, h η := by
    rw [hgsplit]
    have : (∫ η in W, h η) = 0 - ∫ η in U \ W, h η := by
      rw [← horth, hsplit]; ring
    rw [this]; ring
  show ‖∫ η in W, g η‖ ≤ _
  rw [hkey]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg m)]
  have hm2 : 0 ≤ m ^ 2 := sq_nonneg m
  have := mul_le_mul_of_nonneg_left htail hm2
  have e2 : m ^ 2 * (1 / (2 * w)) = m ^ 2 / (2 * w) := by ring
  linarith

/-- Display 11 for `N < 2k`, p. 360: `|∫_𝔐 |S|² e(-2kα) dα| ≤ E19`. The companion of
`Decomp1519.eq19_explicit` with main term 0. PROVED. -/
theorem eq19_high (N k : ℕ) {A ρ : ℝ} (hA : 0 < A) (hN : 2 ≤ N)
    (hbig : 2 * L N ^ (3 * Bexp A / 2) < N) (hk : N < 2 * k)
    (hw2 : ∀ q ∈ Qs N A, wq N A q ≤ 1 / 2)
    (hρ : ∀ q ∈ Qs N A, ∀ a ∈ As q, ∀ η ∈ Ioo (-wq N A q) (wq N A q), ‖R N q a η‖ ≤ ρ) :
    ‖∫ α in majorArcs N A, ((‖S N α‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * α))‖ ≤ E19 N A ρ := by
  rw [eq8 k hA hN hbig]
  refine (norm_sum_le _ _).trans ?_
  unfold E19
  refine Finset.sum_le_sum fun q hq => ?_
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun a ha => ?_
  rw [norm_mul, norm_e, one_mul]
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
  exact arc_integral_bound_high N k q a hk (wq_pos hN hq1) (hw2 q hq) (hρ q hq a ha)

/-- `𝔖(2k) ≤ 2 C₂ d(k)` for `k ≥ 1`: each factor `(p-1)/(p-2) ≤ 2` and `2^{ω(k)} ≤ d(k)`.
PROVED. -/
theorem S2k_le_divisors {k : ℕ} (hk : 1 ≤ k) :
    S2k k ≤ 2 * twinC * (k.divisors.card : ℝ) := by
  unfold S2k
  have ht := twinC_nonneg
  have h1 : ∏ p ∈ k.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2)) ≤
      ∏ p ∈ k.primeFactors.filter (2 < ·), (2 : ℝ) := by
    apply Finset.prod_le_prod₀
    · intro p hp
      have h3 : (3 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2
      exact div_nonneg (by linarith) (by linarith)
    · intro p hp
      have h3 : (3 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2
      rw [div_le_iff₀ (by linarith)]; linarith
  have h2 : ∏ p ∈ k.primeFactors.filter (2 < ·), (2 : ℝ) ≤ ∏ p ∈ k.primeFactors, (2 : ℝ) := by
    rw [Finset.prod_const, Finset.prod_const]
    exact pow_le_pow_right₀ (by norm_num) (Finset.card_filter_le _ _)
  have h3 : ∏ p ∈ k.primeFactors, (2 : ℝ) ≤ (k.divisors.card : ℝ) := by
    rw [Nat.card_divisors (by omega)]
    push_cast
    apply Finset.prod_le_prod₀ (fun _ _ => by norm_num)
    intro p hp
    have : 1 ≤ k.factorization p :=
      (Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) (by omega)
        (Nat.dvd_of_mem_primeFactors hp))
    have : (1 : ℝ) ≤ k.factorization p := by exact_mod_cast this
    linarith
  have := h1.trans (h2.trans h3)
  have h0 : 0 ≤ 2 * twinC := by positivity
  calc 2 * twinC * ∏ p ∈ k.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2))
      ≤ 2 * twinC * (k.divisors.card : ℝ) := mul_le_mul_of_nonneg_left this h0

lemma logpow_le_quarter (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, L N ^ A ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
  have h := (isLittleO_log_rpow_rpow_atTop A (by norm_num : (0 : ℝ) < 1 / 4)).def
    (by norm_num : (0 : ℝ) < 1)
  have h' := tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [h', eventually_ge_atTop 1] with N hN hN1
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hl : 0 ≤ Real.log N := Real.log_nonneg hx
  simp only [Real.norm_eq_abs] at hN
  rw [abs_of_nonneg (Real.rpow_nonneg hl _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _), one_mul] at hN
  exact hN

set_option maxHeartbeats 1000000 in
/-- p. 360, display 9 with its error `O(H)`: the shifts `N < 2k ≤ N + 2H` of the wide range,
`H = N^{1/2+ε}`. There `∫_{-1/2}^{1/2} |T(η)|² e(-2kη) dη = 0`, `T_orth_high`, so the major arcs
give `|∫_𝔐| ≤ E19 ≪ N L^{-B/4}`, `eq19_high` with `E19_le`, while the main term
`𝔖(2k)(N - 2k)` has size `≤ 2 C₂ d(k) 2H ≪ N^{7/8}`, `S2k_le_divisors` with the divisor bound
`Section6.divisors_card_le_rpow`. So each term is `≪ N² L^{-A}`. The Siegel and Walfisz input is now proved above
through its independent cutoff conversion. -/
theorem overhang_estimate6 : ∀ ε : ℝ, 0 < ε → ε < 1 / 4 → ∀ A : ℝ, 0 < A →
    ∃ C N0 : ℝ, ∀ N : ℕ, N0 ≤ N → ∀ k : ℕ, N < 2 * k →
      (k : ℝ) ≤ N / 2 + (N : ℝ) ^ (1 / 2 + ε) →
      ‖(∫ α in majorArcs N A, ((‖S N α‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * α))) -
        (S2k k * ((N : ℝ) - 2 * k) : ℝ)‖ ^ 2 ≤ C * N ^ 2 / L N ^ A := by
  intro ε hε hε4 A hA
  have hB : 0 < Bexp A := by unfold Bexp; linarith
  obtain ⟨CW, hCW0, hSW⟩ := siegel_walfisz_uniform (Bexp A / 2) (7 * (Bexp A / 4) + Bexp A + 1)
    (by positivity) (by positivity)
  obtain ⟨Kd, hKd0, hKd⟩ := LeanLab.PerelliPintz1992.Section6.divisors_card_le_rpow (1 / 16)
    (by norm_num)
  have hLtop : Tendsto (fun N : ℕ => L N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ N : ℕ in atTop,
      (2 ≤ N ∧ 2 * L N ^ (3 * Bexp A / 2) < N ∧ (∀ q ∈ Qs N A, wq N A q ≤ 1 / 2) ∧
        1 ≤ L N ^ (Bexp A / 2)) ∧ 16 ≤ N ∧ 128 * CW + 2 ≤ L N ∧
      L N ^ (9 * (Bexp A / 4) + 2) ≤ √(N : ℝ) / 4 ∧ L N ^ A ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
    filter_upwards [estimate6_hyps_vacuity hA, eventually_ge_atTop 16,
      hLtop.eventually_ge_atTop (128 * CW + 2), logpow_le_sqrt_div4 (9 * (Bexp A / 4) + 2),
      logpow_le_quarter A] with N h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hev
  set t := twinC with ht
  have ht0 : 0 ≤ t := twinC_nonneg
  refine ⟨200 + 32 * t ^ 2 * Kd ^ 2, N1, fun N hN k hk hkP => ?_⟩
  have hNN1 : N1 ≤ N := by exact_mod_cast hN
  obtain ⟨⟨hN2, hbig, hw2, hL1⟩, hN16, hℓC, hP1, hAq⟩ := hN1 N hNN1
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN16
  have hNpos : (0 : ℝ) < N := by linarith
  set ℓ := L N with hℓdef
  have hℓ0 : 0 < ℓ := by linarith
  set r := ℓ ^ (Bexp A / 4) with hrdef
  have hr1 : 1 ≤ r := Real.one_le_rpow (by linarith) (by linarith)
  have hr0 : 0 < r := by linarith
  have hsqrt4 : (4 : ℝ) ≤ √(N : ℝ) := by
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hNr
  have hss : √(N : ℝ) * √(N : ℝ) = N := Real.mul_self_sqrt hNpos.le
  have hbigR : 16 * r ^ 2 * ℓ ^ 2 * r ^ 7 ≤ N := by
    have he : ℓ ^ (9 * (Bexp A / 4) + 2) = r ^ 9 * ℓ ^ 2 := by
      rw [Real.rpow_add hℓ0, show 9 * (Bexp A / 4) = Bexp A / 4 * ((9 : ℕ) : ℝ) by push_cast; ring,
        rpow_quarter hℓ0 (Bexp A) 9, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [he] at hP1
    nlinarith
  set ρ : ℝ := N / r ^ 7 with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have hR := R_small hA hCW0 hSW (by omega) (by linarith) (by linarith) hbigR
  have hI := eq19_high N k hA hN2 hbig hk hw2 hR
  have hE := E19_le hN2 (by linarith) hA hρ0 le_rfl
  -- powers of `s = N^{1/16}`
  set s := (N : ℝ) ^ (1 / 16 : ℝ) with hsdef
  have hs0 : 0 ≤ s := by positivity
  have hspow : ∀ n : ℕ, s ^ n = (N : ℝ) ^ ((1 / 16 : ℝ) * n) := fun n =>
    (Real.rpow_mul_natCast hNpos.le _ _).symm
  have hs16 : s ^ 16 = N := by rw [hspow]; norm_num
  have hs4 : (N : ℝ) ^ (1 / 4 : ℝ) = s ^ 4 := by rw [hspow]; norm_num
  have hP12 : (N : ℝ) ^ (1 / 2 + ε) ≤ s ^ 12 := by
    rw [hspow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
  -- the singular series
  have hk1 : 1 ≤ k := by omega
  have hkr : (k : ℝ) ≤ (N : ℝ) ^ 2 := by
    have : (N : ℝ) ^ (1 / 2 + ε) ≤ N := by
      have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ N)
        (by linarith : 1 / 2 + ε ≤ 1)
      rw [Real.rpow_one] at this; exact this
    nlinarith
  have hS0 : 0 ≤ S2k k := le_trans (by positivity) (S2k_ge k)
  have hSd : S2k k ≤ 2 * t * (Kd * s ^ 2) := by
    refine (S2k_le_divisors hk1).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine (hKd k (by omega)).trans (mul_le_mul_of_nonneg_left ?_ hKd0.le)
    have h1 : (k : ℝ) ^ (1 / 16 : ℝ) ≤ ((N : ℝ) ^ 2) ^ (1 / 16 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hkr (by norm_num)
    rw [← Real.rpow_natCast_mul hNpos.le] at h1
    rw [hspow]
    convert h1 using 2; push_cast; ring
  have hgap : (2 * k : ℝ) - N ≤ 2 * s ^ 12 := by linarith
  have hgap0 : 0 ≤ (2 * k : ℝ) - N := by
    have : (N : ℝ) < 2 * k := by exact_mod_cast hk
    linarith
  -- the bound
  set I := ∫ α in majorArcs N A, ((‖S N α‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * α))
  have hmain : ‖I - ((S2k k * ((N : ℝ) - 2 * k) : ℝ) : ℂ)‖ ≤ 10 * N / r + 4 * t * Kd * s ^ 14 := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hS0,
      abs_of_nonpos (by linarith : (N : ℝ) - 2 * k ≤ 0)]
    have h2 : S2k k * (-((N : ℝ) - 2 * k)) ≤ 2 * t * (Kd * s ^ 2) * (2 * s ^ 12) :=
      mul_le_mul hSd (by linarith) (by linarith) (by positivity)
    have h3 : 2 * t * (Kd * s ^ 2) * (2 * s ^ 12) = 4 * t * Kd * s ^ 14 := by ring
    linarith [hI.trans hE]
  have hA0 : 0 < ℓ ^ A := Real.rpow_pos_of_pos hℓ0 _
  have hrA : ℓ ^ A ≤ r ^ 2 := by
    rw [← rpow_half_eq hℓ0]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by unfold Bexp; linarith)
  have hX : (10 * (N : ℝ) / r) ^ 2 ≤ 100 * ((N : ℝ) ^ 2 / ℓ ^ A) := by
    calc (10 * (N : ℝ) / r) ^ 2 = 100 * ((N : ℝ) ^ 2 / r ^ 2) := by ring
      _ ≤ 100 * ((N : ℝ) ^ 2 / ℓ ^ A) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) hA0 hrA)
          (by norm_num)
  have hY : (4 * t * Kd * s ^ 14) ^ 2 ≤ 16 * t ^ 2 * Kd ^ 2 * ((N : ℝ) ^ 2 / ℓ ^ A) := by
    rw [hs4] at hAq
    have h1 : s ^ 28 * ℓ ^ A ≤ s ^ 28 * s ^ 4 := mul_le_mul_of_nonneg_left hAq (by positivity)
    have h2 : s ^ 28 ≤ (N : ℝ) ^ 2 / ℓ ^ A := by
      rw [le_div_iff₀ hA0, ← hs16]
      calc s ^ 28 * ℓ ^ A ≤ s ^ 28 * s ^ 4 := h1
        _ = (s ^ 16) ^ 2 := by ring
    calc (4 * t * Kd * s ^ 14) ^ 2 = 16 * t ^ 2 * Kd ^ 2 * s ^ 28 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
  have hsq : ‖I - ((S2k k * ((N : ℝ) - 2 * k) : ℝ) : ℂ)‖ ^ 2 ≤
      (10 * N / r + 4 * t * Kd * s ^ 14) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hmain 2
  have hab : (10 * N / r + 4 * t * Kd * s ^ 14) ^ 2 ≤
      2 * (10 * N / r) ^ 2 + 2 * (4 * t * Kd * s ^ 14) ^ 2 := by
    nlinarith [sq_nonneg (10 * N / r - 4 * t * Kd * s ^ 14)]
  calc _ ≤ _ := hsq
    _ ≤ _ := hab
    _ ≤ 2 * (100 * ((N : ℝ) ^ 2 / ℓ ^ A)) + 2 * (16 * t ^ 2 * Kd ^ 2 * ((N : ℝ) ^ 2 / ℓ ^ A)) := by
        linarith
    _ = (200 + 32 * t ^ 2 * Kd ^ 2) * N ^ 2 / L N ^ A := by ring

/-! ### The assembly of 6, PROVED from the cited inputs -/

/-- The final algebra of display 20 with display 12. PROVED. -/
theorem final_alg {kl kh h P z E Q0 r ℓ a C6 CS Co D Sl Sh N : ℝ}
    (hkl0 : 0 ≤ kl) (hkl : kl ≤ h + 1) (hkh0 : 0 ≤ kh) (hkh : kh ≤ h + 1) (hh0 : 0 ≤ h)
    (hhP : h + 1 ≤ 2 * P) (hz : z = N ^ 2 / a) (ha : 0 < a) (hE0 : 0 ≤ E)
    (hE : E ^ 2 ≤ 100 * z) (hQ0 : 0 ≤ Q0) (hQr : r ^ 2 / 2 ≤ Q0) (hr : 1 ≤ r)
    (hQ4 : Q0 ^ 4 ≤ z) (hℓa : ℓ ^ 3 * a ≤ r ^ 2) (hℓ : 0 ≤ ℓ) (hCS : 0 ≤ CS) (hD0 : 0 ≤ D)
    (hD : D ≤ CS * (2 * h + 1) * (8 * ℓ ^ 3))
    (hSl : Sl ≤ 3 * kl * E ^ 2 + 3 * N ^ 2 * (C6 ^ 2 / Q0) * D + 3 * kl * Q0 ^ 4)
    (hSh : Sh ≤ kh * (Co * z)) :
    Sl + Sh ≤ 2 * (303 + 96 * C6 ^ 2 * CS + max Co 0) * P * z := by
  have hz0 : 0 ≤ z := by rw [hz]; positivity
  have hr0 : 0 < r := by linarith
  have hQpos : 0 < Q0 := by nlinarith
  have t1 : 3 * kl * E ^ 2 ≤ 3 * (h + 1) * (100 * z) :=
    mul_le_mul (by linarith) hE (sq_nonneg _) (by linarith)
  have t3 : 3 * kl * Q0 ^ 4 ≤ 3 * (h + 1) * z :=
    mul_le_mul (by linarith) hQ4 (by positivity) (by linarith)
  have hCQ : C6 ^ 2 / Q0 ≤ 2 * C6 ^ 2 / r ^ 2 := by
    rw [div_le_div_iff₀ hQpos (by positivity)]
    nlinarith [sq_nonneg C6]
  have hℓr : ℓ ^ 3 / r ^ 2 ≤ 1 / a := by
    rw [div_le_div_iff₀ (by positivity) ha]; linarith
  have t2 : 3 * N ^ 2 * (C6 ^ 2 / Q0) * D ≤ 96 * C6 ^ 2 * CS * (h + 1) * z := by
    have hN2 : 0 ≤ 3 * N ^ 2 := by positivity
    calc 3 * N ^ 2 * (C6 ^ 2 / Q0) * D ≤ 3 * N ^ 2 * (2 * C6 ^ 2 / r ^ 2) *
          (CS * (2 * h + 1) * (8 * ℓ ^ 3)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hCQ hN2) hD hD0 (by positivity)
      _ = 48 * C6 ^ 2 * CS * (2 * h + 1) * N ^ 2 * (ℓ ^ 3 / r ^ 2) := by ring
      _ ≤ 48 * C6 ^ 2 * CS * (2 * h + 1) * N ^ 2 * (1 / a) :=
          mul_le_mul_of_nonneg_left hℓr (by positivity)
      _ = 48 * C6 ^ 2 * CS * (2 * h + 1) * z := by rw [hz]; ring
      _ ≤ 96 * C6 ^ 2 * CS * (h + 1) * z := by
          have : 0 ≤ C6 ^ 2 * CS * z := by positivity
          nlinarith
  have t4 : kh * (Co * z) ≤ (h + 1) * (max Co 0 * z) := by
    have h1 : Co * z ≤ max Co 0 * z := mul_le_mul_of_nonneg_right (le_max_left _ _) hz0
    have h2 : 0 ≤ max Co 0 * z := mul_nonneg (le_max_right _ _) hz0
    calc kh * (Co * z) ≤ kh * (max Co 0 * z) := mul_le_mul_of_nonneg_left h1 hkh0
      _ ≤ (h + 1) * (max Co 0 * z) := mul_le_mul_of_nonneg_right hkh h2
  have hM : 0 ≤ 303 + 96 * C6 ^ 2 * CS + max Co 0 := by
    have := le_max_right Co 0; positivity
  calc Sl + Sh ≤ (h + 1) * ((303 + 96 * C6 ^ 2 * CS + max Co 0) * z) := by
        nlinarith
    _ ≤ (2 * P) * ((303 + 96 * C6 ^ 2 * CS + max Co 0) * z) :=
        mul_le_mul_of_nonneg_right hhP (by positivity)
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
/-- **Display 6, p. 359, in the wide form**, from the explicit form
`Decomp1519.estimate6_explicit`, the window Siegel and Walfisz bound `R_small`, the bound
`E19_le`, the Shiu block sum `shiu_block` and the overhang leaf. Same type as the burst 4 leaf
`Burst4Split.major_arcs_estimate6`. CONDITIONAL ON `shiu_d2`. The Siegel and Walfisz input and overhang bound are proved. -/
theorem estimate6Wide_of_split : Estimate6Wide := by
  refine ⟨1 / 4, by norm_num, fun ε hε hε4 A hA => ?_⟩
  have hB : 0 < Bexp A := by unfold Bexp; linarith
  obtain ⟨C6, -, h6⟩ := estimate6_explicit
  obtain ⟨CW, hCW0, hSW⟩ := siegel_walfisz_uniform (Bexp A / 2) (7 * (Bexp A / 4) + Bexp A + 1)
    (by positivity) (by positivity)
  obtain ⟨CS, hCS0, hS⟩ := shiu_d2
  obtain ⟨Co, No, hO⟩ := overhang_estimate6 ε hε hε4 A hA
  have hLtop : Tendsto (fun N : ℕ => L N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ N : ℕ in atTop,
      (2 ≤ N ∧ 2 * L N ^ (3 * Bexp A / 2) < N ∧ (∀ q ∈ Qs N A, wq N A q ≤ 1 / 2) ∧
        1 ≤ L N ^ (Bexp A / 2)) ∧ 16 ≤ N ∧ 128 * CW + 2 ≤ L N ∧
      L N ^ (9 * (Bexp A / 4) + 2) ≤ √(N : ℝ) / 4 ∧
      L N ^ (Bexp A / 4 * ((8 : ℕ) : ℝ) + A) ≤ √(N : ℝ) / 4 ∧ No ≤ N := by
    filter_upwards [estimate6_hyps_vacuity hA, eventually_ge_atTop 16,
      hLtop.eventually_ge_atTop (128 * CW + 2), logpow_le_sqrt_div4 (9 * (Bexp A / 4) + 2),
      logpow_le_sqrt_div4 (Bexp A / 4 * ((8 : ℕ) : ℝ) + A),
      tendsto_natCast_atTop_atTop.eventually_ge_atTop No] with N h1 h2 h3 h4 h5 h6'
    exact ⟨h1, h2, h3, h4, h5, h6'⟩
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hev
  refine ⟨2 * (303 + 96 * C6 ^ 2 * CS + max Co 0), N1, fun N V hN hV => ?_⟩
  have hNN1 : N1 ≤ N := by exact_mod_cast hN
  obtain ⟨⟨hN2, hbig, hw2, hL1⟩, hN16, hℓC, hP1, hP2, hNo⟩ := hN1 N hNN1
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN16
  have hNpos : (0 : ℝ) < N := by linarith
  set ℓ := L N with hℓdef
  have hℓ2 : 2 ≤ ℓ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  set r := ℓ ^ (Bexp A / 4) with hrdef
  have hr1 : 1 ≤ r := Real.one_le_rpow (by linarith) (by linarith)
  have hr0 : 0 < r := by linarith
  -- the square root of N
  have hsqrt4 : (4 : ℝ) ≤ √(N : ℝ) := by
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hNr
  have hss : √(N : ℝ) * √(N : ℝ) = N := Real.mul_self_sqrt hNpos.le
  have hsN : √(N : ℝ) / 4 ≤ N / 16 := by nlinarith
  have hbigR : 16 * r ^ 2 * ℓ ^ 2 * r ^ 7 ≤ N := by
    have he : ℓ ^ (9 * (Bexp A / 4) + 2) = r ^ 9 * ℓ ^ 2 := by
      rw [Real.rpow_add hℓ0, show 9 * (Bexp A / 4) = Bexp A / 4 * ((9 : ℕ) : ℝ) by push_cast; ring,
        rpow_quarter hℓ0 (Bexp A) 9, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [he] at hP1
    nlinarith
  have hz8 : r ^ 8 * ℓ ^ A ≤ (N : ℝ) ^ 2 := by
    have he : ℓ ^ (Bexp A / 4 * ((8 : ℕ) : ℝ) + A) = r ^ 8 * ℓ ^ A := by
      rw [Real.rpow_add hℓ0, rpow_quarter hℓ0 (Bexp A) 8]
    rw [he] at hP2
    nlinarith
  set ρ : ℝ := N / r ^ 7 with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have hR := R_small hA hCW0 hSW (by omega) (by linarith) (by linarith) hbigR
  -- the block
  set H' := ⌊(N : ℝ) ^ (1 / 2 + ε)⌋₊ with hH'
  set P := (N : ℝ) ^ (1 / 2 + ε) with hPdef
  have hP0 : 0 ≤ P := by positivity
  have hHP : (H' : ℝ) ≤ P := Nat.floor_le hP0
  have hPlt : P < H' + 1 := Nat.lt_floor_add_one P
  have hP1' : 1 ≤ P := Real.one_le_rpow (by linarith) (by linarith)
  have hPN : P ≤ N := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ N)
      (by linarith : 1 / 2 + ε ≤ 1)
    rw [Real.rpow_one] at this; exact this
  have hsP : √(N : ℝ) ≤ P := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  set K := (Finset.Icc V (V + H')).filter (1 ≤ ·) with hK
  have hKcard : (K.card : ℝ) ≤ H' + 1 := by
    have : K.card ≤ H' + 1 := (Finset.card_filter_le _ _).trans (by rw [Nat.card_Icc]; omega)
    exact_mod_cast this
  change ∑ k ∈ K, _ ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not K (fun k => 2 * k ≤ N)]
  set Kl := K.filter (fun k => 2 * k ≤ N) with hKl
  set Kh := K.filter (fun k => ¬ 2 * k ≤ N) with hKh
  have hKlK : Kl ⊆ K := Finset.filter_subset _ _
  have hKhK : Kh ⊆ K := Finset.filter_subset _ _
  -- the low range, by the explicit form
  have hKl : ∀ k ∈ Kl, 1 ≤ k ∧ 2 * k ≤ N := by
    intro k hk
    rw [hKl, Finset.mem_filter] at hk
    exact ⟨(Finset.mem_filter.mp hk.1).2, hk.2⟩
  have hlow := h6 N A ρ Kl hA hN2 hbig hw2 hL1 hKl hR
  have hE := E19_le hN2 (by linarith) hA hρ0 le_rfl
  have hE0 := E19_nonneg (A := A) hN2 hρ0
  have hQeq : (⌊L N ^ (Bexp A / 2)⌋₊ : ℝ) = (⌊r ^ 2⌋₊ : ℝ) := by
    rw [rpow_half_eq hℓ0]
  have hr2ℓ : ℓ ≤ r ^ 2 := by
    rw [← rpow_half_eq hℓ0]
    calc ℓ = ℓ ^ (1 : ℝ) := (Real.rpow_one ℓ).symm
      _ ≤ ℓ ^ (Bexp A / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by unfold Bexp; linarith)
  have hQr : r ^ 2 / 2 ≤ (⌊r ^ 2⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (r ^ 2)
    have h1 : (1 : ℝ) ≤ ⌊r ^ 2⌋₊ := by
      have : 1 ≤ ⌊r ^ 2⌋₊ := Nat.le_floor (by push_cast; linarith)
      exact_mod_cast this
    linarith
  have hQle : (⌊r ^ 2⌋₊ : ℝ) ≤ r ^ 2 := Nat.floor_le (by positivity)
  have hQ4 : (⌊r ^ 2⌋₊ : ℝ) ^ 4 ≤ N ^ 2 / ℓ ^ A := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hℓ0 _)]
    have h1 : (⌊r ^ 2⌋₊ : ℝ) ^ 4 ≤ r ^ 8 := by
      have := pow_le_pow_left₀ (by positivity) hQle 4
      rw [← pow_mul] at this; exact this
    have := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hℓ0.le A)
    linarith
  have hℓa : ℓ ^ 3 * ℓ ^ A ≤ r ^ 2 := by
    rw [← rpow_half_eq hℓ0, show ℓ ^ 3 = ℓ ^ ((3 : ℕ) : ℝ) by rw [Real.rpow_natCast],
      ← Real.rpow_add hℓ0]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by unfold Bexp; push_cast; linarith)
  have hEsq : E19 N A ρ ^ 2 ≤ 100 * (N ^ 2 / ℓ ^ A) := by
    have h1 : E19 N A ρ ^ 2 ≤ (10 * N / r) ^ 2 := pow_le_pow_left₀ hE0 hE 2
    have hrA : ℓ ^ A ≤ r ^ 2 := by
      rw [← rpow_half_eq hℓ0]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by unfold Bexp; linarith)
    refine h1.trans ?_
    have hA0 : 0 < ℓ ^ A := Real.rpow_pos_of_pos hℓ0 _
    calc (10 * (N : ℝ) / r) ^ 2 = 100 * ((N : ℝ) ^ 2 / r ^ 2) := by ring
      _ ≤ 100 * ((N : ℝ) ^ 2 / ℓ ^ A) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) hA0 hrA)
          (by norm_num)
  have hD := shiu_block hCS0 hS (by omega) hV (hHP.trans hPN) (by linarith) Kl
    (hKlK.trans (le_of_eq rfl))
  -- the high range, by the overhang leaf
  have hhigh : ∑ k ∈ Kh, ‖(∫ α in majorArcs N A, ((‖S N α‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * α))) -
        ((S2k k * ((N : ℝ) - 2 * k) : ℝ) : ℂ)‖ ^ 2 ≤ (Kh.card : ℝ) * (Co * (N ^ 2 / ℓ ^ A)) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [hKh, Finset.mem_filter] at hk
    have hk1 := Finset.mem_filter.mp hk.1
    have hkV := (Finset.mem_Icc.mp hk1.1).2
    have hkr : (k : ℝ) ≤ N / 2 + P := by
      have : (k : ℝ) ≤ V + H' := by exact_mod_cast hkV
      linarith
    have := hO N hNo k (by omega) hkr
    rw [mul_div_assoc] at this
    exact this
  rw [hQeq] at hlow
  have hfin := final_alg (kl := (Kl.card : ℝ)) (kh := (Kh.card : ℝ)) (h := (H' : ℝ)) (P := P)
    (z := N ^ 2 / ℓ ^ A) (E := E19 N A ρ) (Q0 := (⌊r ^ 2⌋₊ : ℝ)) (r := r) (ℓ := ℓ) (a := ℓ ^ A)
    (C6 := C6) (CS := CS) (Co := Co)
    (D := ∑ k ∈ Kl, (((2 * k).divisors.card : ℝ)) ^ 2) (N := N)
    (by positivity) ((Nat.cast_le.mpr (Finset.card_le_card hKlK)).trans hKcard)
    (by positivity) ((Nat.cast_le.mpr (Finset.card_le_card hKhK)).trans hKcard)
    (by positivity) (by linarith) rfl (Real.rpow_pos_of_pos hℓ0 _) hE0 hEsq (by positivity) hQr
    hr1 hQ4 hℓa hℓ0.le hCS0 (Finset.sum_nonneg fun _ _ => sq_nonneg _) hD hlow hhigh
  refine hfin.trans (le_of_eq ?_)
  ring


end
end LeanLab.PerelliPintz1992.Burst8P2
