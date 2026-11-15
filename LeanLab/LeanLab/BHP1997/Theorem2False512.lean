/-
P0069 Baker Harman Pintz 1997, Theorem 2 as printed on page 3, with the mean
square conclusion of page 6, the display after 2.1.
The lab statement `Theorem2With` with conclusion `MeanSquare` is refuted here,
CONDITIONAL ON a rough number input about the sequence a alone. The input is the
hypothesis `hrough` of `theorem2_meanSquare_false_of_rough512`. It is NOT proved
in this file. It is a statement of sieve theory about a(k) = e(k(1/9 + δ)) on the
integers k of I with no small prime factor, δ = Y^(-1/2).
The second sequence is b(m) = e(m(1/9 + δ)) on multiples of 3 and 0 elsewhere.
Theorem 2 puts no coprimality condition on b and tests b only against Dirichlet
characters, so b satisfies every hypothesis with v = 0, see `Theorem2False512a`.
The expected main term is then 0, while the convolution at every even N not
divisible by 3 has size about Y / log x by the input.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Theorem2False512a

namespace LeanLab.BHP1997.Section2MS
open Classical Complex Thm2 MeasureTheory Set
open scoped ComplexConjugate

/-- Part of the counterexample to P0069 Theorem 2 as printed on page 3, which is
CONDITIONAL ON the rough number input: an interval of integers from a to c holds
at least (c - a - 11)/6 even integers not divisible by 3, namely those congruent
to 2 mod 6. -/
private theorem count_even_not_three512c (a c : ℕ) :
    c ≤ 6 * (((Finset.Icc a c).filter (fun N : ℕ => Even N)).filter
      (fun N : ℕ => ¬ 3 ∣ N)).card + a + 11 := by
  have himg : (Finset.Ico (a / 6 + 1) (c / 6)).image (fun k : ℕ => 6 * k + 2) ⊆
      ((Finset.Icc a c).filter (fun N : ℕ => Even N)).filter (fun N : ℕ => ¬ 3 ∣ N) := by
    intro N hN
    rw [Finset.mem_image] at hN
    obtain ⟨k, hk, rfl⟩ := hN
    rw [Finset.mem_Ico] at hk
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
    rw [Nat.even_iff]
    omega
  have hcard : ((Finset.Ico (a / 6 + 1) (c / 6)).image (fun k : ℕ => 6 * k + 2)).card =
      c / 6 - (a / 6 + 1) := by
    rw [Finset.card_image_of_injective _ (fun x y h => by simpa using h), Nat.card_Ico]
  have hle := Finset.card_le_card himg
  rw [hcard] at hle
  omega

/-- SUSPECTED FALSE, proved CONDITIONAL ON the rough number input `hrough`: P0069
Theorem 2 as printed on page 3, in the lab form `Theorem2With` with the mean square
conclusion `MeanSquare` of page 6, fails. This theorem is part of the
counterexample to P0069 Theorem 2 as printed on page 3.

The input `hrough` concerns the sequence a only. It asks, for every small ε, for a
sequence a with: the first hypothesis of Theorem 2 with u = 0; norm at most 1; the
sieve support condition of Theorem 2; and a lower bound c Y / log x for the norm of
the convolution of a with the explicit sequence b(m) = e(m(1/9 + δ)) on multiples
of 3, δ = Y^(-1/2), at every even N in [x, x + H] not divisible by 3. The intended
a is a(k) = e(k(1/9 + δ)) on the integers of I free of prime factors below
exp(sqrt(log x)), for which the convolution is e(N(1/9 + δ)) times a count of rough
numbers in one residue class mod 3.

Given the input, b satisfies the remaining hypotheses with v = 0, the main term
u v Y 𝔖 / (log x log Y) vanishes, and the mean square over K is at least
(H/12) (c Y / log x)², which exceeds C H Y² (log x)^(-8) for large x. -/
theorem theorem2_meanSquare_false_of_rough512
    (hrough : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 100 → ∃ a : ℝ → ℕ → ℂ,
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q →
        (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ x →
          ‖∑ k ∈ (Finset.Ioc ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊).filter
              (fun k : ℕ => (k : ℝ) ≤ t), a x k * χ (k : ZMod q)‖ ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
      (∀ (x : ℝ) (k : ℕ), ‖a x k‖ ≤ 1) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : ℕ,
        Nat.gcd k (primorialBelow (Real.log x ^ A)) ≠ 1 → a x k = 0) ∧
      (∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, ∀ x : ℝ, X₀ ≤ x →
        ∀ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊,
          Even N → ¬ 3 ∣ N →
          c * x ^ (11 / 20 + ε) / Real.log x ≤
            ‖∑ k ∈ Finset.Ioc ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊,
              ∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
                if k + m = N then a x k * (if 3 ∣ m then
                  Complex.exp (2 * Real.pi * Complex.I *
                    (((m : ℝ) * (1 / 9 + (x ^ (11 / 20 + ε)) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ))
                  else 0) else 0‖)) :
    ¬ (∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Theorem2With ε B (fun a b u v _ => MeanSquare ε a b u v)) := by
  intro h
  obtain ⟨ε₀, hε₀, h⟩ := h 0
  have hεpos : 0 < min (ε₀ / 2) (1 / 100) := lt_min (by linarith) (by norm_num)
  have hεlt : min (ε₀ / 2) (1 / 100) < ε₀ :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hε1 : min (ε₀ / 2) (1 / 100) ≤ 1 / 100 := min_le_right _ _
  generalize min (ε₀ / 2) (1 / 100) = ε at hεpos hεlt hε1
  have hT := h ε hεpos hεlt
  obtain ⟨a, ha1, ha2, ha3, c, hc, X₀, hlow⟩ := hrough ε hεpos hε1
  obtain ⟨b, hb⟩ : ∃ b : ℝ → ℕ → ℂ, ∀ (x : ℝ) (m : ℕ), b x m = if 3 ∣ m then
      Complex.exp (2 * Real.pi * Complex.I *
        (((m : ℝ) * (1 / 9 + (x ^ (11 / 20 + ε)) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ)) else 0 :=
    ⟨_, fun _ _ => rfl⟩
  have h1 : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ x →
        ‖∑ k ∈ (Finset.Ioc ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊).filter
            (fun k : ℕ => (k : ℝ) ≤ t),
          (a x k * χ (k : ZMod q) - delta χ * ((0 : ℝ) : ℂ) / Real.log x)‖ ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
    intro A hA
    obtain ⟨C, hC⟩ := ha1 A hA
    refine ⟨C, fun x hx q hq hqA χ t ht => ?_⟩
    have := hC x hx q hq hqA χ t ht
    simp only [Complex.ofReal_zero, mul_zero, zero_div, sub_zero]
    exact this
  have hconc := hT a b 0 0 (fun _ _ _ => ∅) h1 (counter_hyp_ii512c ε a b ha2 hb) ha3
    (counter_hyp_iv512c ε hεpos b hb) (counter_hyp_v512c ε hεpos b hb)
  obtain ⟨C, hC⟩ := hconc 1 one_pos
  -- largeness of x
  have hθpos : (0 : ℝ) < (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)) :=
    mul_pos (by linarith) (by norm_num)
  have hev : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x ∧ C ≤ x ∧ X₀ ≤ x ∧
      26 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) ∧
      12 * max C 0 / c ^ 2 + 1 < Real.log x := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ), Filter.eventually_ge_atTop C,
      Filter.eventually_ge_atTop X₀, (tendsto_rpow_atTop hθpos).eventually_ge_atTop 26,
      Real.tendsto_log_atTop.eventually_gt_atTop (12 * max C 0 / c ^ 2 + 1)]
      with x h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨x, hx1, hxC, hxX, hH26, hlog⟩ := hev.exists
  have hkey := hC x hxC
  have hlowx := hlow x hxX
  have hxpos : 0 < x := by linarith
  have hM0 : 0 ≤ max C 0 := le_max_right _ _
  have hMC : C ≤ max C 0 := le_max_left _ _
  have hL1 : 1 < Real.log x := by
    have : 0 ≤ 12 * max C 0 / c ^ 2 := by positivity
    linarith
  have hL0 : 0 < Real.log x := by linarith
  have hYpos : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hxpos _
  have hP : Real.log x ^ (-1 - 7 : ℝ) ≤ (Real.log x ^ 3)⁻¹ := by
    have e1 : Real.log x ^ (-1 - 7 : ℝ) ≤ Real.log x ^ (-(3 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hL1.le (by norm_num)
    have e2 : Real.log x ^ (-(3 : ℝ)) = (Real.log x ^ 3)⁻¹ := by
      rw [Real.rpow_neg hL0.le, ← Real.rpow_natCast]
      norm_num
    exact e1.trans (le_of_eq e2)
  have hP0 : 0 ≤ Real.log x ^ (-1 - 7 : ℝ) := Real.rpow_nonneg hL0.le _
  -- the count of even N in K not divisible by 3
  have hcount := count_even_not_three512c ⌈x⌉₊
    ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊
  have hceil : ((⌈x⌉₊ : ℕ) : ℝ) < x + 1 := Nat.ceil_lt_add_one hxpos.le
  have hfloor : x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) <
      ((⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hcountR : ((⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊ : ℕ) : ℝ) ≤
      6 * ((((Finset.Icc ⌈x⌉₊
        ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
          (fun N : ℕ => Even N)).filter (fun N : ℕ => ¬ 3 ∣ N)).card : ℝ) +
        ((⌈x⌉₊ : ℕ) : ℝ) + 11 := by
    exact_mod_cast hcount
  -- lower bound for the mean square
  have hsumlow : ((((Finset.Icc ⌈x⌉₊
        ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
          (fun N : ℕ => Even N)).filter (fun N : ℕ => ¬ 3 ∣ N)).card : ℝ) *
        (c * x ^ (11 / 20 + ε) / Real.log x) ^ 2 ≤
      ∑ N ∈ (Finset.Icc ⌈x⌉₊
        ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
          (fun N : ℕ => Even N),
        ‖∑ k ∈ Finset.Ioc ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊,
          ∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
            if k + m = N then a x k * (if 3 ∣ m then
              Complex.exp (2 * Real.pi * Complex.I *
                (((m : ℝ) * (1 / 9 + (x ^ (11 / 20 + ε)) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ))
              else 0) else 0‖ ^ 2 := by
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset (fun N : ℕ => ¬ 3 ∣ N) _) (fun N _ _ => sq_nonneg _))
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum (fun N hN => ?_)
    rw [Finset.mem_filter, Finset.mem_filter] at hN
    exact pow_le_pow_left₀ (by positivity) (hlowx N hN.1.1 hN.1.2 hN.2) 2
  -- the upper bound from the mean square conclusion
  have hupper : ∑ N ∈ (Finset.Icc ⌈x⌉₊
        ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
          (fun N : ℕ => Even N),
        ‖∑ k ∈ Finset.Ioc ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊,
          ∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
            if k + m = N then a x k * (if 3 ∣ m then
              Complex.exp (2 * Real.pi * Complex.I *
                (((m : ℝ) * (1 / 9 + (x ^ (11 / 20 + ε)) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ))
              else 0) else 0‖ ^ 2 ≤
      C * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) * (x ^ (11 / 20 + ε)) ^ 2 *
        Real.log x ^ (-1 - 7 : ℝ) := by
    have hk := hkey
    simp only [hb, Complex.ofReal_zero, zero_mul, zero_div, sub_zero] at hk
    exact hk
  generalize x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) =
    H at hH26 hcountR hfloor hsumlow hupper
  generalize x ^ (11 / 20 + ε) = Y at hYpos hsumlow hupper
  generalize (((Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊).filter
    (fun N : ℕ => Even N)).filter (fun N : ℕ => ¬ 3 ∣ N)).card = n at hcountR hsumlow
  generalize Real.log x = L at hlog hL1 hL0 hP hP0 hsumlow hupper
  generalize L ^ (-1 - 7 : ℝ) = P at hP hP0 hupper
  have hHpos : 0 < H := by linarith
  have hn : H / 12 ≤ (n : ℝ) := by linarith
  have hG : 0 ≤ H * Y ^ 2 := by positivity
  have hZ : 0 < H * Y ^ 2 * (L ^ 3)⁻¹ := by positivity
  have hchain : H / 12 * (c * Y / L) ^ 2 ≤ max C 0 * (H * Y ^ 2 * (L ^ 3)⁻¹) := by
    calc H / 12 * (c * Y / L) ^ 2 ≤ (n : ℝ) * (c * Y / L) ^ 2 :=
          mul_le_mul_of_nonneg_right hn (sq_nonneg _)
      _ ≤ C * H * Y ^ 2 * P := le_trans hsumlow hupper
      _ = C * (H * Y ^ 2 * P) := by ring
      _ ≤ max C 0 * (H * Y ^ 2 * P) :=
          mul_le_mul_of_nonneg_right hMC (mul_nonneg hG hP0)
      _ ≤ max C 0 * (H * Y ^ 2 * (L ^ 3)⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP hG) hM0
  have he : H / 12 * (c * Y / L) ^ 2 = (c ^ 2 * L / 12) * (H * Y ^ 2 * (L ^ 3)⁻¹) := by
    field_simp
  rw [he] at hchain
  have hfin : c ^ 2 * L / 12 ≤ max C 0 := le_of_mul_le_mul_right hchain hZ
  have hc2 : 0 < c ^ 2 := by positivity
  have hdiv : 12 * max C 0 / c ^ 2 < L := by linarith
  rw [div_lt_iff₀ hc2] at hdiv
  linarith

end LeanLab.BHP1997.Section2MS
