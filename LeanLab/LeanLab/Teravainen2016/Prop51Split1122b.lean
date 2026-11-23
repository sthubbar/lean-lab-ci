/-
P0076 J. Teräväinen, arXiv 1611.08585: the outermost layer of the proof of Proposition 5.1,
page 18, namely the reduction on pages 29 to 30 of Proposition 5.1 to display (7.1), the choice
of `Q` by Lemma 7.1 and the comparison of `𝔖(L)` with `(W/φ(W))^{3/2} Q/|𝒬|` from (5.2).
The leaves `prop51_dyad` and `prop51_half` of WeightedPrimeSplit.lean are proved here from three
cited LEAFs on each range. The deeper layers, Theorem 6.5 and the verification of Hypothesis 6.4
in Sections 8 to 10, stay inside the LEAF for display (7.1).
burst-20261122 S69. AI wrote the Lean code. The binary Goldbach conjecture is OPEN.
-/
import LeanLab.Teravainen2016.WeightedPrimeSplit

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- The local factor of the singular product `𝔖(L)` of Definition 6.1, page 21, at the prime `p`
for `L(n) = K n + c`: for `p ≡ -1 (mod 4)`, `p ≠ 3` it is
`(1 - |{n ∈ ℤ_p : L(n) ≡ 0 or 1}|/p)(1 - 2/p)^{-1}`; for `p ≢ -1 (mod 4)` it is
`(1 - |{n ∈ ℤ_p : L(n) ≡ 0}|/p)(1 - 1/p)^{-1}`; the prime `3` lies in neither product of
Definition 6.1, so its factor is `1`. -/
noncomputable def singularLocal (K c : ℤ) (p : ℕ) : ℝ :=
  if p % 4 = 3 then
    (if p = 3 then 1 else
      (1 - (#((range p).filter (fun n : ℕ => (K * n + c) % p = 0 ∨ (K * n + c) % p = 1)) : ℝ) / p) *
        (1 - 2 / (p : ℝ))⁻¹)
  else
    (1 - (#((range p).filter (fun n : ℕ => (K * n + c) % p = 0)) : ℝ) / p) * (1 - 1 / (p : ℝ))⁻¹

/-- The singular product `𝔖(L)` of Definition 6.1, page 21, for `L(n) = K n + c` with `K ≠ 0`.
At a prime `p ∤ K` the residues `n ∈ ℤ_p` with `L(n) ≡ 0` are one and those with `L(n) ≡ 0 or 1`
are two, so the factor of Definition 6.1 at `p ∤ K` is `1` and the product runs over `p ∣ K`. -/
noncomputable def singularS (K c : ℤ) : ℝ :=
  ∏ p ∈ K.natAbs.primeFactors, singularLocal K c p

/-- The conclusion of Lemma 7.1, page 29, for frequencies `α₁, …, α_C`, the modulus `W`, the
scale `N` and the constants `A`, `B`: each `α_k = W a_k / q_k + ε_k` with `(a_k, q_k) = 1`,
`1 ≤ q_k ≤ N / (log N)^{100 B}`, `|ε_k| ≤ (log N)^{100 B} W / (q_k N)`, and either `q_k ∣ Q` or
`q_k / (q_k, Q²) ≥ (log N)^A`. -/
def Lemma71Adapted {C : ℕ} (α : Fin C → ℝ) (W : ℤ) (N A B Q : ℕ) : Prop :=
  ∀ k : Fin C, ∃ a : ℤ, ∃ q : ℕ, ∃ εk : ℝ, α k = (W : ℝ) * a / q + εk ∧ IsCoprime a (q : ℤ) ∧
    1 ≤ q ∧ (q : ℝ) ≤ N / Real.log N ^ (100 * B) ∧
    |εk| ≤ Real.log N ^ (100 * B) * W / (q * N) ∧
    (q ∣ Q ∨ Real.log N ^ A ≤ (q : ℝ) / (Nat.gcd q (Q ^ 2) : ℝ))

/-- Lemma 7.1, page 29, which is Matomäki and Shao Lemma 3.2, with `B = A (3C)^C`; the threshold
`N₀` is read as uniform in the `α_k`, as Dirichlet approximation gives. -/
def Lemma71Choice : Prop :=
  ∀ (C A : ℕ) (W : ℤ), 1 ≤ W → ∃ N₀ : ℕ, ∀ α : Fin C → ℝ, ∀ N : ℕ, N₀ ≤ N →
    ∃ Q : ℕ, 1 ≤ Q ∧ (Q : ℝ) ≤ Real.log N ^ (A * (3 * C) ^ C) ∧
      Lemma71Adapted α W N (A * (3 * C) ^ C) A Q

/-- Display (7.1), page 30, on the summation range `R N`, for every `Q` that Lemma 7.1 allows.
With `n = Q m + c₀` the sum over `m ∼ x` of `χ(t - (Q m + c₀))` is the sum over `n ∈ R N`,
`n ≡ c₀ (mod Q)`; `L(m) = Q W m + W c₀ + b`, so `L(m) ∈ P`, `L(m) - 1 ∈ S` is `Good (W n + b)`.
The scale is `x = N / (3 Q)`, as `R N` is `n ∼ N/3` after the rescaling of (5.3). The inequality
is multiplied by `(log x)^{3/2}`; the term `o(x / (log x)^{3/2})` becomes `- ε N / Q` inside the
bracket for every `ε > 0` once `N ≥ N₀(w, C, ε)`, uniformly in `χ`, `Q`, `b`, `t`, `c₀`. The
constant `A` of Lemma 7.1 is taken large in terms of `C`, as on page 29. -/
def Display71On (R : ℕ → Finset ℕ) : Prop :=
  ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ Cc : ℕ, ∃ A : ℕ, ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → (Cc : ℝ) ^ 20 ≤ w →
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ χ : ℤ → ℝ, (∀ n, 0 ≤ χ n) →
    ∀ (c : Fin Cc → ℂ) (α : Fin Cc → ℝ), (∀ k, ‖c k‖ ≤ Cc) →
      (∀ n : ℤ, (χ n : ℂ) = ∑ k, c k * eC (α k * n)) →
    ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℕ, 1 ≤ Q → (Q : ℝ) ≤ Real.log N ^ (A * (3 * Cc) ^ Cc) →
    Lemma71Adapted α (WW J w) N (A * (3 * Cc) ^ Cc) A Q →
    ∀ b : ℤ, 0 ≤ b → b < WW J w → Amenable (WW J w) b →
    ∀ t : ℤ, |(t : ℝ)| ≤ 5 * (N : ℝ) / 3 → ∀ c₀ ∈ QRes Q (WW J w) b,
      δ₀ * singularS ((Q : ℤ) * WW J w) (WW J w * c₀ + b) *
          (∑ n ∈ (R N).filter (fun n => n % Q = c₀), χ (t - n) - ε * N / Q) ≤
        Real.log ((N : ℝ) / (3 * Q)) ^ ((3 : ℝ) / 2) *
          ∑ n ∈ ((R N).filter (fun n : ℕ => Good (WW J w * (n : ℤ) + b))).filter
            (fun n => n % Q = c₀), χ (t - n)

/-- The lower half of the display `𝔖(L) ≍ (W/φ(W))^{3/2} Q/|𝒬|` on page 30, from (5.2) and the
amenability of `W n + b`, with an absolute constant. -/
def SingularLower : Prop :=
  ∃ cS : ℝ, 0 < cS ∧ ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ, Amenable (WW J w) b →
    ∀ Q : ℕ, 1 ≤ Q → ∀ c₀ ∈ QRes Q (WW J w) b,
      cS * (((WW J w : ℝ) / (Nat.totient (WW J w).toNat : ℝ)) ^ ((3 : ℝ) / 2)) *
          ((Q : ℝ) / #(QRes Q (WW J w) b)) ≤
        singularS ((Q : ℤ) * WW J w) (WW J w * c₀ + b)

/-! ### The leaves -/

/-- LEAF: Lemma 7.1, page 29, cited there as Matomäki and Shao Lemma 3.2: Dirichlet
approximation of each `α_k` with denominators `q_k ≤ N/(log N)^{100B}` and a pigeonhole choice of
`Q ≤ (log N)^B`, `B = A (3C)^C`. Class MEDIUM. -/
theorem lemma71_choice : Lemma71Choice := by sorry

/-- LEAF: display (7.1), page 30, for `n ∼ N/3`. Class HARD. It follows from Theorem 6.5,
page 22, applied to `ω_m = χ(t - (Q m + c₀))` and `L(m) = Q W m + W c₀ + b`, once Hypothesis 6.4
holds with the parameters (7.2); by (2.2) and Lemma 7.1 this is Hypothesis 6.4 for `e(ξ m)` with
`ξ` as in (7.3), proved in Section 10 on the major arcs, Subsections 10.1 to 10.3, and on the
minor arcs, Subsections 10.4 and 10.5, from Lemmas 8.1, 8.2, 9.1 and 9.2; the numerical input is
`H(1/2 - ε, 3/7 - ε, 3 + ε)` of page 22. -/
theorem display71_dyad : Display71On dyad := by sorry

/-- LEAF: display (7.1), page 30, with `N/3 < n < N/2` in place of `n ∼ N/3`. Class HARD. Not
printed: the paper states (7.1) and Proposition 5.1 for dyadic ranges only; the remark on page 11
claims Sections 6 to 10 work for this interval as well. -/
theorem display71_half : Display71On half := by sorry

/-- LEAF: the comparison `𝔖(L) ≫ (W/φ(W))^{3/2} Q/|𝒬|` on page 30. Class MEDIUM. The primes
`p ∣ Q`, `p ∤ W` give exactly `Q/|𝒬|` by (5.2); the primes `p ∣ W` give
`∏ (1 - 2/p)^{-1}` over `p ≡ -1 (mod 4)`, `p ≠ 3`, times `∏ (1 - 1/p)^{-1}` over `p ≢ -1 (mod 4)`,
which is `≍ (W/φ(W))^{3/2}` uniformly in `w` by Mertens' theorem in the classes mod 4. -/
theorem singular_series_lower : SingularLower := by sorry

/-! ### Assembly -/

theorem WW_pos' (J w : ℕ) : 0 < WW J w := Wmod_pos (fun q hq => (Sw_spec w q hq).1)

/-- Proposition 5.1 on `R` from Lemma 7.1, display (7.1) on `R` and the singular series
comparison: the reduction on pages 29 to 30. -/
theorem prop51On_of_display71 (R : ℕ → Finset ℕ) (h71 : Lemma71Choice) (hD : Display71On R)
    (hS : SingularLower) : Prop51On R := by
  obtain ⟨δ₀, hδ₀, H71⟩ := hD
  obtain ⟨cS, hcS, HS⟩ := hS
  refine ⟨δ₀ * cS, mul_pos hδ₀ hcS, ?_⟩
  intro Cc
  obtain ⟨A, HA⟩ := H71 Cc
  set B : ℕ := A * (3 * Cc) ^ Cc with hB
  refine ⟨B, ?_⟩
  intro J w hJ hw hCw ε hε
  obtain ⟨N₀, HN⟩ := HA J w hJ hw hCw ε hε
  have hW1 : (1 : ℤ) ≤ WW J w := WW_pos' J w
  obtain ⟨N₁, HL⟩ := h71 Cc A (WW J w) hW1
  obtain ⟨N₂, HE⟩ := eventually_log_rpow_le_sqrt 3 (B : ℝ)
  refine ⟨max (max N₀ N₁) (max N₂ 1), ?_⟩
  intro χ hχ0 hχC N hN
  have hN0 : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN3 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨c, α, hc, hrep⟩ := hχC
  obtain ⟨Q, hQ1, hQB, hAd⟩ := HL α N hN1
  refine ⟨Q, hQ1, hQB, ?_⟩
  intro b hb0 hbW hamen t ht c₀ hc₀
  have h := HN χ hχ0 c α hc hrep N hN0 Q hQ1 hQB hAd b hb0 hbW hamen t ht c₀ hc₀
  have hs := HS J w hJ hw b hamen Q hQ1 c₀ hc₀
  set W : ℤ := WW J w with hWdef
  set S : ℝ := singularS ((Q : ℤ) * W) (W * c₀ + b) with hSdef
  set X : ℝ := ∑ n ∈ (R N).filter (fun n => n % Q = c₀), χ (t - n) - ε * N / Q with hX
  set G : ℝ := ∑ n ∈ ((R N).filter (fun n : ℕ => Good (W * (n : ℤ) + b))).filter
      (fun n => n % Q = c₀), χ (t - n) with hG
  set r : ℝ := (Q : ℝ) / #(QRes Q W b) with hr
  set φ : ℝ := (Nat.totient W.toNat : ℝ) with hφ
  have hG0 : 0 ≤ G := sum_nonneg (fun n _ => hχ0 _)
  have hr0 : 0 ≤ r := by positivity
  have hWr : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW1
  have hφ0 : 0 < φ := by
    have : 0 < W.toNat := by omega
    have h' : 0 < Nat.totient W.toNat := Nat.totient_pos.mpr this
    show (0 : ℝ) < (Nat.totient W.toNat : ℝ)
    exact_mod_cast h'
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN3
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNr
  -- `1 ≤ x = N / (3 Q) ≤ N`
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
  have h3Q : 3 * (Q : ℝ) ≤ N := by
    have e := HE N hN2
    rw [Real.rpow_natCast] at e
    have hsq : Real.sqrt N ≤ N := by
      have h1 : 1 ≤ Real.sqrt N := by rw [Real.one_le_sqrt]; exact hNr
      have := Real.mul_self_sqrt (show (0 : ℝ) ≤ N by linarith)
      nlinarith
    linarith
  have hx1 : (1 : ℝ) ≤ (N : ℝ) / (3 * Q) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hxN : (N : ℝ) / (3 * Q) ≤ N := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hlogx0 : 0 ≤ Real.log ((N : ℝ) / (3 * Q)) := Real.log_nonneg hx1
  have hlogxN : Real.log ((N : ℝ) / (3 * Q)) ≤ Real.log N :=
    Real.log_le_log (by linarith) hxN
  have hpow : Real.log ((N : ℝ) / (3 * Q)) ^ ((3 : ℝ) / 2) ≤ Real.log N ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow hlogx0 hlogxN (by norm_num)
  -- `(φ/W)^{3/2} (W/φ)^{3/2} = 1`
  set Φ : ℝ := (φ / W) ^ ((3 : ℝ) / 2) with hΦ
  set P : ℝ := ((W : ℝ) / φ) ^ ((3 : ℝ) / 2) with hP
  have hΦ0 : 0 ≤ Φ := Real.rpow_nonneg (by positivity) _
  have hΦP : Φ * P = 1 := by
    rw [hΦ, hP, ← Real.mul_rpow (by positivity) (by positivity)]
    rw [show φ / (W : ℝ) * ((W : ℝ) / φ) = 1 by field_simp]
    exact Real.one_rpow _
  show δ₀ * cS * r * X ≤ Real.log N ^ ((3 : ℝ) / 2) * Φ * G
  rcases le_or_gt X 0 with hX0 | hX0
  · have h1 : δ₀ * cS * r * X ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hX0
    have h2 : 0 ≤ Real.log N ^ ((3 : ℝ) / 2) * Φ * G := by
      have := Real.rpow_nonneg hlogN ((3 : ℝ) / 2)
      positivity
    linarith
  · have hs' : cS * P * r ≤ S := hs
    have e1 : δ₀ * cS * r * X = Φ * (δ₀ * (cS * P * r) * X) := by
      calc δ₀ * cS * r * X = (Φ * P) * (δ₀ * cS * r * X) := by rw [hΦP, one_mul]
        _ = Φ * (δ₀ * (cS * P * r) * X) := by ring
    have e2 : δ₀ * (cS * P * r) * X ≤ δ₀ * S * X := by
      apply mul_le_mul_of_nonneg_right _ hX0.le
      exact mul_le_mul_of_nonneg_left hs' hδ₀.le
    have e3 : δ₀ * S * X ≤ Real.log N ^ ((3 : ℝ) / 2) * G :=
      le_trans h (mul_le_mul_of_nonneg_right hpow hG0)
    rw [e1]
    calc Φ * (δ₀ * (cS * P * r) * X) ≤ Φ * (Real.log N ^ ((3 : ℝ) / 2) * G) :=
          mul_le_mul_of_nonneg_left (le_trans e2 e3) hΦ0
      _ = Real.log N ^ ((3 : ℝ) / 2) * Φ * G := by ring

/-- Proposition 5.1 for `n ∼ N/3`, the statement of `prop51_dyad`, from the leaves. -/
theorem prop51_dyad_of_leaves : Prop51On dyad :=
  prop51On_of_display71 dyad lemma71_choice display71_dyad singular_series_lower

/-- Proposition 5.1 for `N/3 < n < N/2`, the statement of `prop51_half`, from the leaves. -/
theorem prop51_half_of_leaves : Prop51On half :=
  prop51On_of_display71 half lemma71_choice display71_half singular_series_lower

/-- Twin check: the assembly has the type of the LEAF `prop51_dyad`. -/
theorem prop51_dyad_twin : type_of% @LeanLab.Teravainen2016.prop51_dyad := prop51_dyad_of_leaves

/-- Twin check: the assembly has the type of the LEAF `prop51_half`. -/
theorem prop51_half_twin : type_of% @LeanLab.Teravainen2016.prop51_half := prop51_half_of_leaves

end LeanLab.Teravainen2016
