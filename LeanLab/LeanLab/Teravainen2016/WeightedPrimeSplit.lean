/-
P0076 J. Teräväinen, arXiv 1611.08585, Section 5, pages 17 to 21: Proposition 3.2 and its
half interval variant from Proposition 5.1 together with Lemmas 5.2 and 5.3, by splitting the
sum over `n` into residue classes `c₀ (mod Q)`, `c₀ ∈ 𝒬`.
AI wrote this Lean code, Claude, session CLOUD-S62. Checked only by the Lean kernel.
The binary Goldbach conjecture is OPEN.
-/
import LeanLab.Teravainen2016.MainInputs

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- The set `𝒬` of display (5.1), page 18, as residues `0 ≤ c₀ < Q`:
`(W c₀ + b, Q) = (W c₀ + b - 1, s(Q)) = 1`, the second condition read prime by prime as in
`Amenable`, `s(Q)` being the product of the primes `p ∣ Q`, `p ≡ -1 (mod 4)`, `p ≠ 3`. -/
noncomputable def QRes (Q : ℕ) (W b : ℤ) : Finset ℕ :=
  (range Q).filter (fun c₀ => IsCoprime (W * c₀ + b) (Q : ℤ) ∧
    ∀ p : ℕ, p.Prime → p % 4 = 3 → p ≠ 3 → p ∣ Q → ¬ (p : ℤ) ∣ W * c₀ + b - 1)

/-- **Proposition 5.1**, page 18, on the summation range `R N`. For the dyadic range the paper's
`n ∼ N` is `n ∼ N/3` here, the rescaling of (5.3); `|t| ≤ 5 (N/3)`; the factor
`δ₁ (log N)^{-3/2} (W/φ(W))^{3/2}` is moved to the left as the weight of `fW`; the term
`o(N/Q)` inside the bracket is `- ε N / Q` for every `ε > 0` once `N ≥ N₀(w, C, ε)`, uniformly in
`χ`, `b`, `t`, `c₀`. `Q ≤ (log N)^B` depends only on `χ` and `N`, and `B ≪_C 1`. The shift is
restricted to `0 ≤ b < W` as in `Prop32On`. -/
def Prop51On (R : ℕ → Finset ℕ) : Prop :=
  ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ Cc : ℕ, ∃ B : ℕ, ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → (Cc : ℝ) ^ 20 ≤ w →
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ χ : ℤ → ℝ, (∀ n, 0 ≤ χ n) → FourierComplexityLE χ Cc →
    ∀ N : ℕ, N₀ ≤ N → ∃ Q : ℕ, 1 ≤ Q ∧ (Q : ℝ) ≤ Real.log N ^ B ∧
    ∀ b : ℤ, 0 ≤ b → b < WW J w → Amenable (WW J w) b →
    ∀ t : ℤ, |(t : ℝ)| ≤ 5 * (N : ℝ) / 3 → ∀ c₀ ∈ QRes Q (WW J w) b,
      δ₁ * ((Q : ℝ) / #(QRes Q (WW J w) b)) *
          (∑ n ∈ (R N).filter (fun n => n % Q = c₀), χ (t - n) - ε * N / Q) ≤
        Real.log N ^ ((3 : ℝ) / 2) * ((Nat.totient (WW J w).toNat : ℝ) / WW J w) ^ ((3 : ℝ) / 2) *
          ∑ n ∈ ((R N).filter (fun n : ℕ => Good (WW J w * (n : ℤ) + b))).filter
            (fun n => n % Q = c₀),
            χ (t - n)

/-- **Lemma 5.2**, page 18, quoting Matomäki and Shao Lemma 7.4, on the summation range `R N`:
the scale `n ∼ N` of the paper is `R N` here, so `N ≥ 2 Q²` becomes `6 Q² ≤ N` and the error
is stated with the larger `N`. The premise on `𝒬` is read for positive `a`, which loses nothing
since `e(a c₀/q)` depends on `a mod q`. `𝒬` is nonempty, as `Q/|𝒬|` requires. -/
def Lemma52On (R : ℕ → Finset ℕ) : Prop :=
  ∃ C' : ℝ, 0 < C' ∧ ∀ (Cc : ℕ) (χ : ℤ → ℝ), (∀ n, 0 ≤ χ n) → FourierComplexityLE χ Cc →
    ∀ N Q : ℕ, 1 ≤ Q → 6 * Q ^ 2 ≤ N → ∀ 𝒬 : Finset ℕ, 𝒬 ⊆ range Q → 𝒬.Nonempty →
    ∀ η₀ : ℝ, 0 < η₀ → (∀ q a : ℕ, q ∣ Q → q ≠ 1 → 0 < a → a.Coprime q →
        ‖∑ c₀ ∈ 𝒬, eC ((a : ℝ) * c₀ / q)‖ ≤ η₀ * #𝒬) →
    ∀ t : ℤ, (∑ n ∈ R N, χ (t - n)) - C' * (η₀ * (Cc : ℝ) ^ 2 * N + Q * (Cc : ℝ) ^ 2 * Real.sqrt N) ≤
      (Q : ℝ) / #𝒬 * ∑ c₀ ∈ 𝒬, ∑ n ∈ (R N).filter (fun n => n % Q = c₀), χ (t - n)

/-- **Lemma 5.3**, page 19, display (5.4), for `𝒬` of (5.1) with `W`, `w` as in (3.3). -/
def Lemma53 : Prop :=
  ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ, Amenable (WW J w) b →
    ∀ Q q a : ℕ, 1 ≤ Q → q ∣ Q → q ≠ 1 → 0 < a → a.Coprime q →
      ‖∑ c₀ ∈ QRes Q (WW J w) b, eC ((a : ℝ) * c₀ / q)‖ ≤
        (w : ℝ) ^ (-(1 : ℝ) / 2) * #(QRes Q (WW J w) b)

/-- `𝒬 ≠ ∅`, the positivity of the product (5.2), page 18. -/
def QResNonempty : Prop :=
  ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ, Amenable (WW J w) b →
    ∀ Q : ℕ, 1 ≤ Q → (QRes Q (WW J w) b).Nonempty

/-! ### The leaves -/

/-- LEAF: Proposition 5.1, page 18, for `n ∼ N/3`. Class HARD. Its proof occupies Sections 6 to
10, the weighted semilinear sieve Theorem 6.5 and the circle method, through the reduction to
(7.1) on page 30. -/
theorem prop51_dyad : Prop51On dyad := by sorry

/-- LEAF: Proposition 5.1, page 18, with `N/3 < n < N/2` in place of `n ∼ N/3`, the variant
behind the remark on page 11. Class HARD. Not printed: the paper's Proposition 5.1 is for
dyadic `n ∼ N` only, and Sections 6 to 10 are claimed to work for this interval as well. -/
theorem prop51_half : Prop51On half := by sorry

/-- LEAF: Lemma 5.2, page 18, which cites Matomäki and Shao Lemma 7.4, for `n ∼ N/3`.
Class MEDIUM. -/
theorem lemma52_dyad : Lemma52On dyad := by sorry

/-- LEAF: Lemma 5.2, page 18, which cites Matomäki and Shao Lemma 7.4, for `N/3 < n < N/2`.
Class MEDIUM. Matomäki and Shao Lemma 7.4 is an equidistribution in residue classes
whose proof works on any interval. -/
theorem lemma52_half : Lemma52On half := by sorry

/-- LEAF: Lemma 5.3, page 19, display (5.4), proved on pages 20 to 21 from Lemma 5.4 and (5.2).
Class MEDIUM. -/
theorem lemma53 : Lemma53 := by sorry

/-- The remark (5.2), page 18: `|𝒬| > 0`. A residue with `W c₀ + b ≡ 2` modulo every prime
`p ∣ Q`, `p ∤ W`, lies in `𝒬`; at the primes `p ∣ W` amenability does the work. -/
theorem qres_nonempty : QResNonempty := by
  intro J w _ _ b hamen Q hQ
  obtain ⟨_, h216, hbW, hb1, -⟩ := hamen
  set W : ℤ := WW J w
  set S : Finset ℕ := Q.primeFactors.filter (fun p : ℕ => ¬ (p : ℤ) ∣ W)
  set P : ℤ := ∏ p ∈ S, (p : ℤ)
  have hcop : IsCoprime W P := by
    apply IsCoprime.prod_right
    intro p hp
    obtain ⟨hpQ, hpW⟩ := mem_filter.mp hp
    have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Nat.prime_of_mem_primeFactors hpQ)
    exact ((Prime.coprime_iff_not_dvd hpp).mpr hpW).symm
  obtain ⟨u, v, huv⟩ := hcop
  set x : ℤ := u * (2 - b)
  have hQ0 : (Q : ℤ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  set c : ℤ := x % Q
  have hc0 : 0 ≤ c := Int.emod_nonneg x hQ0
  have hcQ : c < Q := Int.emod_lt_of_pos x (by exact_mod_cast (show 0 < Q by omega))
  have hct : ((c.toNat : ℕ) : ℤ) = c := Int.toNat_of_nonneg hc0
  have key : W * c + b = 2 - P * (v * (2 - b)) - (Q : ℤ) * (W * (x / Q)) := by
    simp only [c, Int.emod_def]
    linear_combination (2 - b) * huv
  have h2W : (2 : ℤ) ∣ W := dvd_trans (by norm_num) h216
  -- a prime `p ∣ Q`, `p ∤ W` divides `P`
  have hPdvd : ∀ p : ℕ, p.Prime → p ∣ Q → ¬ (p : ℤ) ∣ W → (p : ℤ) ∣ P := by
    intro p hp hpQ hpW
    apply dvd_prod_of_mem
    exact mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpQ, by omega⟩, hpW⟩
  have hQd : ∀ p : ℕ, p ∣ Q → (p : ℤ) ∣ (Q : ℤ) := fun p h => by exact_mod_cast h
  refine ⟨c.toNat, ?_⟩
  simp only [QRes, mem_filter, mem_range]
  refine ⟨by omega, ?_, ?_⟩
  · rw [hct, Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs]
    apply Nat.coprime_of_dvd
    intro p hp h1 h2
    have hpi : (p : ℤ) ∣ W * c + b := Int.ofNat_dvd_left.mpr h1
    have hpQ : p ∣ Q := by simpa using h2
    have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    by_cases hpW : (p : ℤ) ∣ W
    · have hpb : (p : ℤ) ∣ b := by
        have := dvd_sub hpi (dvd_mul_of_dvd_left hpW c)
        simpa using this
      exact hpp.not_isUnit (hbW.isUnit_of_dvd' hpb hpW)
    · have hP := hPdvd p hp hpQ hpW
      have h2 : (p : ℤ) ∣ 2 := by
        have := dvd_add (dvd_add hpi (dvd_mul_of_dvd_left hP (v * (2 - b))))
          (dvd_mul_of_dvd_left (hQd p hpQ) (W * (x / Q)))
        rwa [key, show 2 - P * (v * (2 - b)) - (Q : ℤ) * (W * (x / Q)) +
          P * (v * (2 - b)) + (Q : ℤ) * (W * (x / Q)) = 2 by ring] at this
      have h2' : p ∣ 2 := by exact_mod_cast h2
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2'
      subst hp2
      exact hpW (by exact_mod_cast h2W)
  · intro p hp h4 h3 hpQ hdiv
    rw [hct] at hdiv
    by_cases hpW : (p : ℤ) ∣ W
    · apply hb1 p hp h4 h3 hpW
      have := dvd_sub hdiv (dvd_mul_of_dvd_left hpW c)
      rwa [show W * c + b - 1 - W * c = b - 1 by ring] at this
    · have hP := hPdvd p hp hpQ hpW
      have h1 : (p : ℤ) ∣ 1 := by
        have := dvd_add (dvd_add hdiv (dvd_mul_of_dvd_left hP (v * (2 - b))))
          (dvd_mul_of_dvd_left (hQd p hpQ) (W * (x / Q)))
        rwa [key, show 2 - P * (v * (2 - b)) - (Q : ℤ) * (W * (x / Q)) - 1 +
          P * (v * (2 - b)) + (Q : ℤ) * (W * (x / Q)) = 1 by ring] at this
      exact (Nat.prime_iff_prime_int.mp hp).not_isUnit (isUnit_of_dvd_one h1)

/-! ### Assembly -/

/-- `(log N)^r` is eventually at most `√N / K`. -/
theorem eventually_log_rpow_le_sqrt (K r : ℝ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → K * Real.log N ^ r ≤ Real.sqrt N := by
  have hc : (0 : ℝ) < 1 / (|K| + 1) := by positivity
  have h := ((isLittleO_log_rpow_rpow_atTop r (by norm_num : (0 : ℝ) < 1 / 2)).bound hc)
  have h' := tendsto_natCast_atTop_atTop.eventually h
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp h'
  refine ⟨N₁, fun N hN => ?_⟩
  have hb := hN₁ N hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hsq : Real.sqrt N = (N : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hN0 _)] at hb
  rw [hsq]
  have hK1 : 0 < |K| + 1 := by positivity
  calc K * Real.log N ^ r ≤ |K| * |Real.log N ^ r| := by
        calc K * Real.log N ^ r ≤ |K * Real.log N ^ r| := le_abs_self _
          _ = |K| * |Real.log N ^ r| := abs_mul _ _
    _ ≤ (|K| + 1) * |Real.log N ^ r| := by
        apply mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ ≤ (|K| + 1) * (1 / (|K| + 1) * (N : ℝ) ^ ((1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hb hK1.le
    _ = (N : ℝ) ^ ((1 : ℝ) / 2) := by field_simp

/-- Splitting into residue classes `c₀ ∈ 𝒬 ⊆ [0, Q)` loses nothing for nonnegative terms. -/
theorem sum_residue_le (s 𝒬 : Finset ℕ) (Q : ℕ) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    ∑ c ∈ 𝒬, ∑ n ∈ s.filter (fun n => n % Q = c), f n ≤ ∑ n ∈ s, f n := by
  have h1 : ∑ c ∈ 𝒬, ∑ n ∈ s.filter (fun n => n % Q = c), f n =
      ∑ n ∈ s.filter (fun n => n % Q ∈ 𝒬), f n := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := s.filter (fun n => n % Q ∈ 𝒬)) (t := 𝒬)
      (g := fun n => n % Q) (fun n hn => (mem_filter.mp hn).2)]
    apply sum_congr rfl
    intro c hc
    apply sum_congr _ (fun _ _ => rfl)
    ext n
    simp only [mem_filter]
    constructor
    · rintro ⟨hn, rfl⟩; exact ⟨⟨hn, hc⟩, rfl⟩
    · rintro ⟨⟨hn, -⟩, h⟩; exact ⟨hn, h⟩
  rw [h1]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n _ _ => hf n)

/-- Generic assembly: `Prop32On R` from Proposition 5.1 and Lemmas 5.2, 5.3 on `R`, for a
range `R N` inside `(N/3, 2N/3)` up to one point. -/
theorem prop32On_of_split (R : ℕ → Finset ℕ)
    (hR : ∀ N : ℕ, ∃ m : ℕ, ∀ n ∈ R N, n ≠ m → (N : ℝ) / 3 < n ∧ (n : ℝ) < 2 * N / 3)
    (h51 : Prop51On R) (h52 : Lemma52On R) (h53 : Lemma53) (hne : QResNonempty) :
    Prop32On R := by
  obtain ⟨δ₁, hδ₁, H51⟩ := h51
  obtain ⟨C', hC', H52⟩ := h52
  refine ⟨δ₁, C' + 3, hδ₁, by linarith, ?_⟩
  intro Cc J w hJ hw hCw
  obtain ⟨B, HB⟩ := H51 Cc
  have hw1 : (1 : ℝ) ≤ w := by
    have : (1 : ℝ) ≤ wBig := Real.one_le_rpow (by norm_num) (by positivity)
    linarith
  have hw0 : (0 : ℝ) < w := by linarith
  set u : ℝ := (w : ℝ) ^ ((1 : ℝ) / 3) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hw0 _
  have hε : 0 < 1 / u := by positivity
  obtain ⟨N₀', HN⟩ := HB J w hJ hw hCw (1 / u) hε
  obtain ⟨N₁, A1⟩ := eventually_log_rpow_le_sqrt (C' * (Cc : ℝ) ^ 2 * u) (B : ℝ)
  obtain ⟨N₂, A2⟩ := eventually_log_rpow_le_sqrt (Real.sqrt 6) (B : ℝ)
  obtain ⟨N₃, A3⟩ := eventually_log_rpow_le_sqrt ((Cc : ℝ) ^ 2 * u / δ₁) ((3 : ℝ) / 2)
  refine ⟨max (max N₀' 1) (max N₁ (max N₂ N₃)), ?_⟩
  intro χ hχ0 hχC b hb0 hbW hamen N hN t ht1 ht2
  have hN0' : N₀' ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN1' : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNN₂ : N₂ ≤ N := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hN
  have hNN₃ : N₃ ≤ N := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) hN
  obtain ⟨Q, hQ1, hQB, HQ⟩ := HN χ hχ0 hχC N hN0'
  set W : ℤ := WW J w with hW
  set 𝒬 := QRes Q W b with h𝒬
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1'
  have hNr0 : (0 : ℝ) ≤ N := by linarith
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hNr
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
  have h𝒬ne : 𝒬.Nonempty := hne J w hJ hw b hamen Q hQ1
  have h𝒬pos : (0 : ℝ) < #𝒬 := by exact_mod_cast h𝒬ne.card_pos
  have hsqN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNr0
  have hsqN1 : Real.sqrt N ≤ N := by
    have h1 : 1 ≤ Real.sqrt N := by rw [Real.one_le_sqrt]; exact hNr
    nlinarith
  have hlogB : Real.log N ^ (B : ℝ) = Real.log N ^ B := Real.rpow_natCast _ _
  -- 6 Q² ≤ N
  have h6 : 6 * Q ^ 2 ≤ N := by
    have a2 := A2 N hNN₂
    rw [hlogB] at a2
    have hp0 : 0 ≤ Real.log N ^ B := pow_nonneg hlog0 _
    have hs6 : Real.sqrt 6 * Real.sqrt 6 = 6 := Real.mul_self_sqrt (by norm_num)
    have : (6 : ℝ) * Q ^ 2 ≤ N := by
      have hQ2 : (Q : ℝ) ^ 2 ≤ (Real.log N ^ B) ^ 2 := pow_le_pow_left₀ (by linarith) hQB 2
      have hsq0 : 0 ≤ Real.sqrt 6 * Real.log N ^ B := by positivity
      have := mul_self_le_mul_self hsq0 a2
      nlinarith
    exact_mod_cast this
  -- Lemma 5.3 supplies the premise of Lemma 5.2 with `η₀ = w^{-1/2}`.
  have hη : (0 : ℝ) < (w : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hw0 _
  have H2 := H52 Cc χ hχ0 hχC N Q hQ1 h6 𝒬 (filter_subset _ _) h𝒬ne _ hη
    (fun q a hq hq1 ha hco => h53 J w hJ hw b hamen Q q a hQ1 hq hq1 ha hco) t
  -- sum Proposition 5.1 over `c₀ ∈ 𝒬`
  have htabs : |(t : ℝ)| ≤ 5 * (N : ℝ) / 3 := abs_le.mpr ⟨by linarith, by linarith⟩
  set wt : ℝ := Real.log N ^ ((3 : ℝ) / 2) *
    ((Nat.totient W.toNat : ℝ) / W) ^ ((3 : ℝ) / 2) with hwt
  set T : ℕ → ℝ := fun c => ∑ n ∈ (R N).filter (fun n => n % Q = c), χ (t - n) with hT
  set G : ℝ := ∑ n ∈ (R N).filter (fun n : ℕ => Good (W * (n : ℤ) + b)), χ (t - n) with hG
  have hsum : ∑ c ∈ 𝒬, δ₁ * ((Q : ℝ) / #𝒬) * (T c - 1 / u * N / Q) ≤
      ∑ c ∈ 𝒬, wt * ∑ n ∈ ((R N).filter (fun n : ℕ => Good (W * (n : ℤ) + b))).filter
        (fun n => n % Q = c), χ (t - n) :=
    sum_le_sum (fun c hc => HQ b hb0 hbW hamen t htabs c hc)
  have hW1 : (1 : ℤ) ≤ W := hamen.1
  have hWr : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW1
  have hphi0 : (0 : ℝ) ≤ (Nat.totient W.toNat : ℝ) / W := by positivity
  have hphi1 : (Nat.totient W.toNat : ℝ) / W ≤ 1 := by
    rw [div_le_one (by linarith)]
    have h1 : (Nat.totient W.toNat : ℝ) ≤ (W.toNat : ℝ) := by
      exact_mod_cast Nat.totient_le _
    have h2 : ((W.toNat : ℕ) : ℝ) = (W : ℝ) := by
      have : ((W.toNat : ℕ) : ℤ) = W := Int.toNat_of_nonneg (by linarith)
      exact_mod_cast this
    linarith
  have hwt0 : 0 ≤ wt := mul_nonneg (Real.rpow_nonneg hlog0 _) (Real.rpow_nonneg hphi0 _)
  have hwtle : wt ≤ Real.log N ^ ((3 : ℝ) / 2) := by
    have := Real.rpow_le_one hphi0 hphi1 (by norm_num : (0 : ℝ) ≤ 3 / 2)
    calc wt ≤ Real.log N ^ ((3 : ℝ) / 2) * 1 :=
          mul_le_mul_of_nonneg_left this (Real.rpow_nonneg hlog0 _)
      _ = _ := mul_one _
  have hL : ∑ c ∈ 𝒬, δ₁ * ((Q : ℝ) / #𝒬) * (T c - 1 / u * N / Q) =
      δ₁ * ((Q : ℝ) / #𝒬 * ∑ c ∈ 𝒬, T c - 1 / u * N) := by
    rw [← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul]
    field_simp
  have hRgt : ∑ c ∈ 𝒬, wt * ∑ n ∈ ((R N).filter (fun n : ℕ => Good (W * (n : ℤ) + b))).filter
        (fun n => n % Q = c), χ (t - n) ≤ wt * G := by
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left
      (sum_residue_le _ 𝒬 Q (fun n => χ (t - n)) (fun n => hχ0 _)) hwt0
  -- boundary point
  obtain ⟨m, hm⟩ := hR N
  have hχb : ∀ n, χ n ≤ (Cc : ℝ) ^ 2 := fun n => (le_abs_self _).trans
    (fourierComplexity_abs_le hχC n)
  have hF : wt * G - wt * (Cc : ℝ) ^ 2 ≤ ∑ n ∈ R N, fW W b N n * χ (t - n) := by
    have hpt : ∀ n ∈ R N, wt * (if Good (W * (n : ℤ) + b) then χ (t - n) else 0) -
        (if n = m then wt * (Cc : ℝ) ^ 2 else 0) ≤ fW W b N n * χ (t - n) := by
      intro n hn
      by_cases hnm : n = m
      · have hfW : 0 ≤ fW W b N n := by unfold fW; split_ifs <;> [exact hwt0; exact le_refl _]
        have h1 : wt * (if Good (W * (n : ℤ) + b) then χ (t - n) else 0) ≤ wt * (Cc : ℝ) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hwt0
          split_ifs
          · exact hχb _
          · positivity
        rw [if_pos hnm]
        have := mul_nonneg hfW (hχ0 (t - n))
        linarith
      · obtain ⟨ha, hb'⟩ := hm n hn hnm
        rw [if_neg hnm, sub_zero]
        unfold fW
        by_cases hg : Good (W * (n : ℤ) + b)
        · rw [if_pos hg, if_pos ⟨ha, hb', hg⟩]
        · rw [if_neg hg, if_neg (fun h => hg h.2.2)]; simp
    have hs := sum_le_sum hpt
    rw [sum_sub_distrib, ← mul_sum, ← sum_filter, sum_ite_eq'] at hs
    have : (if m ∈ R N then wt * (Cc : ℝ) ^ 2 else 0) ≤ wt * (Cc : ℝ) ^ 2 := by
      split_ifs
      · exact le_refl _
      · positivity
    linarith
  -- the three error terms
  have hCc2 : (Cc : ℝ) ^ 2 * u ≤ (w : ℝ) ^ ((1 : ℝ) / 2) := by
    have hc0 : (0 : ℝ) ≤ Cc := Nat.cast_nonneg _
    have e1 : (Cc : ℝ) ^ 2 = ((Cc : ℝ) ^ 20) ^ ((1 : ℝ) / 10) := by
      rw [← Real.rpow_natCast (Cc : ℝ) 20, ← Real.rpow_mul hc0,
        show ((20 : ℕ) : ℝ) * (1 / 10) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have e2 : ((Cc : ℝ) ^ 20) ^ ((1 : ℝ) / 10) ≤ (w : ℝ) ^ ((1 : ℝ) / 10) :=
      Real.rpow_le_rpow (by positivity) hCw (by norm_num)
    have e3 : (w : ℝ) ^ ((1 : ℝ) / 10) * u = (w : ℝ) ^ ((1 : ℝ) / 10 + 1 / 3) := by
      rw [hu, ← Real.rpow_add hw0]
    have e4 : (w : ℝ) ^ ((1 : ℝ) / 10 + 1 / 3) ≤ (w : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hw1 (by norm_num)
    rw [e1]
    calc ((Cc : ℝ) ^ 20) ^ ((1 : ℝ) / 10) * u ≤ (w : ℝ) ^ ((1 : ℝ) / 10) * u :=
          mul_le_mul_of_nonneg_right e2 hu0.le
      _ ≤ _ := by rw [e3]; exact e4
  have hη1 : (w : ℝ) ^ (-(1 : ℝ) / 2) * (w : ℝ) ^ ((1 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hw0]; norm_num
  have E1 : (w : ℝ) ^ (-(1 : ℝ) / 2) * (Cc : ℝ) ^ 2 * N ≤ 1 / u * N := by
    have : (w : ℝ) ^ (-(1 : ℝ) / 2) * (Cc : ℝ) ^ 2 * u ≤ 1 := by
      calc (w : ℝ) ^ (-(1 : ℝ) / 2) * (Cc : ℝ) ^ 2 * u
          = (w : ℝ) ^ (-(1 : ℝ) / 2) * ((Cc : ℝ) ^ 2 * u) := by ring
        _ ≤ (w : ℝ) ^ (-(1 : ℝ) / 2) * (w : ℝ) ^ ((1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hCc2 hη.le
        _ = 1 := hη1
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hu0]
    nlinarith
  have E2 : C' * ((Q : ℝ) * (Cc : ℝ) ^ 2 * Real.sqrt N) ≤ 1 / u * N := by
    have a1 := A1 N hNN₁
    rw [hlogB] at a1
    have hsq0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
    have : C' * (Cc : ℝ) ^ 2 * u * Q ≤ Real.sqrt N :=
      le_trans (mul_le_mul_of_nonneg_left hQB (by positivity)) a1
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hu0]
    calc C' * ((Q : ℝ) * (Cc : ℝ) ^ 2 * Real.sqrt N) * u
        = (C' * (Cc : ℝ) ^ 2 * u * Q) * Real.sqrt N := by ring
      _ ≤ Real.sqrt N * Real.sqrt N := mul_le_mul_of_nonneg_right this hsq0
      _ = N := hsqN
  have E3 : wt * (Cc : ℝ) ^ 2 ≤ δ₁ * (1 / u * N) := by
    have a3 := A3 N hNN₃
    have h1 : (Cc : ℝ) ^ 2 * u / δ₁ * Real.log N ^ ((3 : ℝ) / 2) ≤ N := le_trans a3 hsqN1
    have h2 : wt * (Cc : ℝ) ^ 2 ≤ Real.log N ^ ((3 : ℝ) / 2) * (Cc : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hwtle (by positivity)
    have h3 : Real.log N ^ ((3 : ℝ) / 2) * (Cc : ℝ) ^ 2 ≤ δ₁ * (1 / u * N) := by
      have : Real.log N ^ ((3 : ℝ) / 2) * (Cc : ℝ) ^ 2 =
          ((Cc : ℝ) ^ 2 * u / δ₁ * Real.log N ^ ((3 : ℝ) / 2)) * (δ₁ / u) := by
        field_simp
      rw [this]
      calc ((Cc : ℝ) ^ 2 * u / δ₁ * Real.log N ^ ((3 : ℝ) / 2)) * (δ₁ / u)
          ≤ N * (δ₁ / u) := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = δ₁ * (1 / u * N) := by ring
    linarith
  -- combine
  have hS := H2
  have hkey : C' * ((w : ℝ) ^ (-(1 : ℝ) / 2) * (Cc : ℝ) ^ 2 * N + Q * (Cc : ℝ) ^ 2 * Real.sqrt N)
      + 1 / u * N ≤ (C' + 2) * (1 / u * N) := by
    have := mul_le_mul_of_nonneg_left E1 hC'.le
    have e := mul_add C' ((w : ℝ) ^ (-(1 : ℝ) / 2) * (Cc : ℝ) ^ 2 * N)
      ((Q : ℝ) * (Cc : ℝ) ^ 2 * Real.sqrt N)
    linarith only [this, e, E2]
  have hmain : δ₁ * ((∑ n ∈ R N, χ (t - n)) - (C' + 2) * (1 / u * N)) ≤ wt * G := by
    have h1 : δ₁ * ((∑ n ∈ R N, χ (t - n)) - (C' + 2) * (1 / u * N)) ≤
        δ₁ * ((Q : ℝ) / #𝒬 * ∑ c ∈ 𝒬, T c - 1 / u * N) := by
      apply mul_le_mul_of_nonneg_left _ hδ₁.le
      linarith only [H2, hkey]
    linarith only [h1, hsum, hL, hRgt]
  have hfinal : (C' + 3) * N / u = (C' + 2) * (1 / u * N) + 1 / u * N := by
    field_simp; ring
  rw [hfinal]
  linarith only [hmain, hF, E3]

/-- Proposition 3.2, page 9, from the leaves of Section 5. -/
theorem paper_weighted_prime_input_of_leaves : Prop32 := by
  apply prop32On_of_split dyad _ prop51_dyad lemma52_dyad lemma53 qres_nonempty
  intro N
  refine ⟨Nat.ceil ((N : ℝ) / 3), fun n hn hnm => ?_⟩
  simp only [dyad, mem_filter] at hn
  refine ⟨lt_of_le_of_ne hn.2.1 ?_, hn.2.2⟩
  intro h
  apply hnm
  rw [h, Nat.ceil_natCast]

/-- The half interval variant of Proposition 3.2, page 11, from the leaves of Section 5. -/
theorem paper_half_interval_input_of_leaves : Prop32Half := by
  apply prop32On_of_split half _ prop51_half lemma52_half lemma53 qres_nonempty
  intro N
  refine ⟨0, fun n hn _ => ?_⟩
  simp only [half, mem_filter] at hn
  refine ⟨hn.2.1, ?_⟩
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith [hn.2.2]

end LeanLab.Teravainen2016
