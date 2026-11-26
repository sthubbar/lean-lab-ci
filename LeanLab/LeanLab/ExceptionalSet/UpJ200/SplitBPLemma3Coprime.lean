import LeanLab.ExceptionalSet.Prep1121SingSeries

/-!
Burst 2026-11-22, unit P1122-0121. Split of the named hypothesis
`DQLeafCoprimeSelected.BPLemma3CoprimeHyp`.

Source: P0082, Brudern and Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998), doi 10.5802/aif.1621, Lemma 3 on page 358 with
displays 12 to 15 on page 359, and case ii a on page 363.

`BPLemma3CoprimeHyp` is Lemma 3 after two in paper steps of page 363 case ii a:
the twisted term `Ĩ(m) 𝔖~(m)` is moved into the error by displays 12 and 13, and
the terms `X Γ₁(m) + X Γ₂(m)` are bounded by the envelopes 14 and 15. Here:
* `tildeSing` and `tildeI` are displays 12 and 13, new definitions that the
  printed Lemma 3 needs.
* `leaf_bp_lemma3_printed` is the LEAF, Lemma 3 as printed, with `Γ₁, Γ₂`
  existentially quantified subject to 14 and 15, specialised to the range of the
  hypothesis. It is Montgomery and Vaughan 1975 formulas 6.17, 6.19 and 7.1: a
  citation wall, CITED-LEFT.
* `tildeI_abs_le` and `tildeSing_norm_le` are the two bounds of page 363 case ii a,
  PROVED.
* `bpLemma3Coprime_of_printed` derives `BPLemma3CoprimeHyp` from the printed form,
  PROVED, no sorry.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.SplitBPLemma3Coprime

open Real Finset Filter
open LeanLab.ExceptionalSet.U1539 (R1)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)
open LeanLab.ExceptionalSet.UpJ200.Decomp559b (SelectedRealZero)
open LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected (singSeries BPLemma3CoprimeHyp)

/-- P0082 page 359 display 12, the twisted singular series
`𝔖~(m) = χ~(-1) μ(r~/(r~,m)) r~/(φ(r~) φ(r~/(r~,m))) ∏_{p ∤ r~ m} (1 - (p-1)⁻²) ∏_{p ∤ r~, p ∣ m} (1 + (p-1)⁻¹)`.
The two Euler products are written as one product over primes, factor one at `p ∣ r~`. -/
noncomputable def tildeSing (r : ℕ) (χ : DirichletCharacter ℂ r) (m : ℤ) : ℂ :=
  χ (-1) * (ArithmeticFunction.moebius (r / Nat.gcd r m.natAbs) : ℂ) *
    (((r : ℝ) / ((r.totient : ℝ) * ((r / Nat.gcd r m.natAbs).totient : ℝ)) : ℝ) : ℂ) *
    ((∏' p : Nat.Primes, (if (p : ℕ) ∣ r then (1 : ℝ)
      else if ((p : ℕ) : ℤ) ∣ m then 1 + 1 / (((p : ℕ) : ℝ) - 1)
      else 1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2) : ℝ) : ℂ)

/-- P0082 page 359 display 13, `Ĩ(m) = Σ_{P < k < m - P} (k (m - k))^{β~ - 1}`, over integers `k`. -/
noncomputable def tildeI (P : ℝ) (β : ℝ) (m : ℤ) : ℝ :=
  ∑ k ∈ (Finset.Ioo ⌊P⌋ m).filter (fun k : ℤ => (k : ℝ) < m - P),
    ((k : ℝ) * ((m : ℝ) - k)) ^ (β - 1)

/-- LEAF: P0082 page 358 Lemma 3 as printed, with displays 12 to 15 of page 359.
Class HARD, a citation wall: Montgomery and Vaughan 1975 formula 6.17 with the error of
6.19 kept explicit and their 7.1, CITED-LEFT.
`R₁(m) = m 𝔖(m) + Ĩ(m) 𝔖~(m) + X Γ₁(m) + X Γ₂(m) + O(χ~(m)² r~ m X / (φ(r~)² φ(m)))
  + O(m X / φ(m) (1 - β~) exp(-c₂ log X / log P) log P)`, with `Γ₁ ≪` display 14 and
`Γ₂ ≪` display 15; `P = X^θ` so `log X / log P = 1 / θ`. The sum of the envelopes 14 and 15
is `divisorError`. It is stated in the range of `BPLemma3CoprimeHyp`: the selected zero
region with parameter `a`, even `m` coprime to `r~`. -/
theorem leaf_bp_lemma3_printed :
    ∀ a : ℝ, 0 < a → ∃ C c₂ : ℝ, 0 < C ∧ 0 < c₂ ∧ ∃ P₀ : ℝ,
      ∀ θ : ℝ, 0 < θ → θ < 6 / 100 → ∀ X : ℝ, 0 < X → P₀ ≤ X ^ θ →
      ∀ r : ℕ, 1 ≤ r → r ≠ 1 → (r : ℝ) ≤ X ^ θ → SelectedRealZero a (X ^ θ) r →
      ∀ (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
        χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 1 - a / Real.log (X ^ θ) ≤ β → β < 1 →
        χ.LFunction β = 0 →
        ∀ m : ℤ, 1 ≤ m → (m : ℝ) ≤ X → Even m → Int.gcd m r = 1 →
          ∃ Γ₁ Γ₂ : ℝ, |Γ₁| + |Γ₂| ≤ C * divisorError r (X ^ θ) m ∧
            ‖R1 (X ^ θ) X m - ((m * singSeries m : ℝ) : ℂ) -
                (tildeI (X ^ θ) β m : ℂ) * tildeSing r χ m - ((X * Γ₁ + X * Γ₂ : ℝ) : ℂ)‖ ≤
              C * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) * m * X /
                  ((r.totient : ℝ) ^ 2 * (m.toNat.totient : ℝ)) +
                C * X * ((m.toNat : ℝ) / (m.toNat.totient : ℝ)) * (1 - β) *
                  Real.exp (-(c₂ / θ)) * Real.log (X ^ θ) := by
  sorry

/-- Display 13 and page 363 case ii a: `|Ĩ(m)| ≤ m` for `β ≤ 1`, `P ≥ 0`. PROVED. -/
theorem tildeI_abs_le (P β : ℝ) (hP : 0 ≤ P) (hβ : β ≤ 1) (m : ℤ) (hm : 1 ≤ m) :
    |tildeI P β m| ≤ m := by
  unfold tildeI
  have hterm : ∀ k ∈ (Finset.Ioo ⌊P⌋ m).filter (fun k : ℤ => (k : ℝ) < m - P),
      0 ≤ ((k : ℝ) * ((m : ℝ) - k)) ^ (β - 1) ∧
        ((k : ℝ) * ((m : ℝ) - k)) ^ (β - 1) ≤ 1 := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ioo] at hk
    obtain ⟨⟨hk1, _⟩, hk2⟩ := hk
    have hk0 : (0 : ℤ) ≤ ⌊P⌋ := Int.floor_nonneg.mpr hP
    have hkpos : (1 : ℝ) ≤ k := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
    have hmk : P < (m : ℝ) - k := by linarith
    have hmk' : (0 : ℝ) < (m : ℝ) - k := by linarith
    have hmkI : k < m := by
      have : (k : ℝ) < m := by linarith
      exact_mod_cast this
    have hmk1 : (1 : ℝ) ≤ (m : ℝ) - k := by
      have : (1 : ℤ) ≤ m - k := by omega
      have h : ((1 : ℤ) : ℝ) ≤ ((m - k : ℤ) : ℝ) := by exact_mod_cast this
      push_cast at h; linarith
    have hprod : (1 : ℝ) ≤ (k : ℝ) * ((m : ℝ) - k) := by nlinarith
    exact ⟨Real.rpow_nonneg (by linarith) _,
      Real.rpow_le_one_of_one_le_of_nonpos hprod (by linarith)⟩
  have hnn : 0 ≤ ∑ k ∈ (Finset.Ioo ⌊P⌋ m).filter (fun k : ℤ => (k : ℝ) < m - P),
      ((k : ℝ) * ((m : ℝ) - k)) ^ (β - 1) :=
    Finset.sum_nonneg (fun k hk => (hterm k hk).1)
  rw [abs_of_nonneg hnn]
  calc ∑ k ∈ (Finset.Ioo ⌊P⌋ m).filter (fun k : ℤ => (k : ℝ) < m - P),
        ((k : ℝ) * ((m : ℝ) - k)) ^ (β - 1)
      ≤ ∑ _k ∈ (Finset.Ioo ⌊P⌋ m).filter (fun k : ℤ => (k : ℝ) < m - P), (1 : ℝ) :=
        Finset.sum_le_sum (fun k hk => (hterm k hk).2)
    _ ≤ ∑ _k ∈ Finset.Ioo (0 : ℤ) m, (1 : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          simp only [Finset.mem_filter, Finset.mem_Ioo] at hk ⊢
          have hk0 : (0 : ℤ) ≤ ⌊P⌋ := Int.floor_nonneg.mpr hP
          exact ⟨by omega, hk.1.2⟩
        · intros; norm_num
    _ ≤ m := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Int.card_Ioo, sub_zero]
        have h1 : (((m - 1).toNat : ℤ)) = m - 1 := Int.toNat_of_nonneg (by omega)
        have h2 : (((m - 1).toNat : ℕ) : ℝ) = ((m - 1 : ℤ) : ℝ) := by exact_mod_cast h1
        rw [h2]; push_cast; linarith

/-- Partial products of the factor of `𝔖~` are at most `m / φ(m)`. -/
theorem partial_le (m : ℕ) (hm : 1 ≤ m) (r : ℕ) (s : Finset Nat.Primes) :
    0 ≤ ∏ p ∈ s, (if (p : ℕ) ∣ r then (1 : ℝ)
      else if (((p : ℕ) : ℤ) ∣ (m : ℤ)) then 1 + 1 / (((p : ℕ) : ℝ) - 1)
      else 1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2) ∧
    ∏ p ∈ s, (if (p : ℕ) ∣ r then (1 : ℝ)
      else if (((p : ℕ) : ℤ) ∣ (m : ℤ)) then 1 + 1 / (((p : ℕ) : ℝ) - 1)
      else 1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2) ≤ (m : ℝ) / (m.totient : ℝ) := by
  classical
  set g : Nat.Primes → ℝ := fun p => if (p : ℕ) ∣ r then (1 : ℝ)
      else if (((p : ℕ) : ℤ) ∣ (m : ℤ)) then 1 + 1 / (((p : ℕ) : ℝ) - 1)
      else 1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2 with hg
  set f : Nat.Primes → ℝ := fun p => if (p : ℕ) ∣ m then (p : ℝ) / ((p : ℝ) - 1) else 1
    with hf
  have hfac : ∀ p : Nat.Primes, 0 ≤ g p ∧ g p ≤ f p ∧ 1 ≤ f p := by
    intro p
    have hp : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
    have hp1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hinv : 1 / ((p : ℝ) - 1) ≤ 1 := by rw [div_le_one hpos]; exact hp1
    have hinv0 : 0 ≤ 1 / ((p : ℝ) - 1) := by positivity
    have hsq : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have hsq0 : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
    have hpq : (p : ℝ) / ((p : ℝ) - 1) = 1 + 1 / ((p : ℝ) - 1) := by
      field_simp; ring
    have hdvd : (((p : ℕ) : ℤ) ∣ (m : ℤ)) ↔ (p : ℕ) ∣ m := Int.natCast_dvd_natCast
    simp only [hg, hf, hdvd]
    split_ifs <;> constructor <;> (try constructor) <;> (try rw [hpq]) <;> linarith
  refine ⟨Finset.prod_nonneg (fun p _ => (hfac p).1), ?_⟩
  set S0 : Finset Nat.Primes := m.primeFactors.subtype Nat.Prime with hS0
  have hS0f : ∀ p : Nat.Primes, p ∉ S0 → f p = 1 := by
    intro p hp
    have : ¬ (p : ℕ) ∣ m := by
      intro hd; apply hp
      rw [hS0]
      exact (Finset.mem_subtype (p := Nat.Prime) (s := m.primeFactors)
        (a := (p : Subtype Nat.Prime))).mpr (Nat.mem_primeFactors.mpr ⟨p.2, hd, by omega⟩)
    simp [hf, this]
  have htf : ∏' p : Nat.Primes, f p = (m : ℝ) / (m.totient : ℝ) :=
    (LeanLab.ExceptionalSet.UpJ200.Prep1121SingSeries.leaf_prod_primeFactors_ratio m hm).2
  have htS : ∏' p : Nat.Primes, f p = ∏ p ∈ S0, f p := tprod_eq_prod hS0f
  calc ∏ p ∈ s, g p ≤ ∏ p ∈ s, f p :=
        Finset.prod_le_prod₀ (fun p _ => (hfac p).1) (fun p _ => (hfac p).2.1)
    _ ≤ ∏ p ∈ s ∪ S0, f p :=
        Finset.prod_le_prod_of_subset_of_one_le₀ Finset.subset_union_left
          (fun p _ => by linarith [(hfac p).2.2]) (fun p _ _ => (hfac p).2.2)
    _ = ∏ p ∈ S0, f p :=
        (Finset.prod_subset Finset.subset_union_right (fun p _ hp => hS0f p hp)).symm
    _ = (m : ℝ) / (m.totient : ℝ) := by rw [← htS, htf]

/-- Display 12 and page 363 case ii a: for `(m, r~) = 1`,
`|𝔖~(m)| ≤ (r~ / φ(r~)²) (m / φ(m))`. PROVED. -/
theorem tildeSing_norm_le (r : ℕ) (hr : 1 ≤ r) (χ : DirichletCharacter ℂ r) (m : ℤ)
    (hm : 1 ≤ m) (hg : Int.gcd m r = 1) :
    ‖tildeSing r χ m‖ ≤
      ((r : ℝ) / (r.totient : ℝ) ^ 2) * ((m.toNat : ℝ) / (m.toNat.totient : ℝ)) := by
  classical
  have hgcd : Nat.gcd r m.natAbs = 1 := by
    rw [Nat.gcd_comm]; simpa [Int.gcd] using hg
  have hmn : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (by omega)
  have hm1 : 1 ≤ m.toNat := by omega
  set G : Nat.Primes → ℝ := fun p => if (p : ℕ) ∣ r then (1 : ℝ)
      else if ((p : ℕ) : ℤ) ∣ m then 1 + 1 / (((p : ℕ) : ℝ) - 1)
      else 1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2 with hG
  have hGm : G = fun p : Nat.Primes => if (p : ℕ) ∣ r then (1 : ℝ)
      else if (((p : ℕ) : ℤ) ∣ ((m.toNat : ℕ) : ℤ)) then 1 + 1 / (((p : ℕ) : ℝ) - 1)
      else 1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2 := by
    rw [hmn]
  have hT : 0 ≤ ∏' p, G p ∧ ∏' p, G p ≤ (m.toNat : ℝ) / (m.toNat.totient : ℝ) := by
    by_cases hmul : Multipliable G
    · have hlim := hmul.hasProd
      have hpl := fun s => partial_le m.toNat hm1 r s
      rw [← hGm] at hpl
      exact ⟨ge_of_tendsto' hlim (fun s => (hpl s).1), le_of_tendsto' hlim (fun s => (hpl s).2)⟩
    · rw [tprod_eq_one_of_not_multipliable hmul]
      refine ⟨zero_le_one, ?_⟩
      have hφ : 0 < (m.toNat.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
      rw [one_le_div hφ]; exact_mod_cast Nat.totient_le _
  have hφr : 0 < (r.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hχ1 : ‖χ (-1)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  have hμ : ‖((ArithmeticFunction.moebius (r / Nat.gcd r m.natAbs) : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  unfold tildeSing
  rw [← hG, hgcd, Nat.div_one]
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hT.1, Real.norm_of_nonneg (by positivity)]
  have hq : (r : ℝ) / ((r.totient : ℝ) * (r.totient : ℝ)) = (r : ℝ) / (r.totient : ℝ) ^ 2 := by
    ring
  rw [hq]
  have hA : 0 ≤ (r : ℝ) / (r.totient : ℝ) ^ 2 := by positivity
  rw [hgcd, Nat.div_one] at hμ
  calc ‖χ (-1)‖ * ‖((ArithmeticFunction.moebius r : ℤ) : ℂ)‖ * ((r : ℝ) / (r.totient : ℝ) ^ 2) *
        ∏' p, G p ≤ 1 * 1 * ((r : ℝ) / (r.totient : ℝ) ^ 2) * ∏' p, G p := by
        have h1 := mul_le_mul hχ1 hμ (norm_nonneg _) zero_le_one
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hA) hT.1
    _ ≤ 1 * 1 * ((r : ℝ) / (r.totient : ℝ) ^ 2) *
        ((m.toNat : ℝ) / (m.toNat.totient : ℝ)) :=
        mul_le_mul_of_nonneg_left hT.2 (by positivity)
    _ = _ := by ring

/-- Page 363 case ii a: the printed Lemma 3 gives `BPLemma3CoprimeHyp`. The twisted term is
bounded by displays 12 and 13 and absorbed with `m ≤ X`, the factor `χ~(m)²` is at most one,
and the Gamma terms are bounded by `divisorError`. PROVED, no sorry. -/
theorem bpLemma3Coprime_of_printed (h : type_of% @leaf_bp_lemma3_printed) :
    BPLemma3CoprimeHyp := by
  intro a ha
  obtain ⟨C, c₂, hC, hc₂, P₀, hL⟩ := h a ha
  refine ⟨3 * C + 1, c₂, by positivity, hc₂, P₀, ?_⟩
  intro θ hθ hθ6 X hX hP0 r hr hr1 hrP hsel hrz χ β hχ hχ2 hχne hβlo hβ1 hβz m hm hmX hev hgcd
  obtain ⟨Γ₁, Γ₂, hΓ, hR⟩ := hL θ hθ hθ6 X hX hP0 r hr hr1 hrP hsel hrz χ β hχ hχ2 hχne hβlo
    hβ1 hβz m hm hmX hev hgcd
  set P : ℝ := X ^ θ with hPdef
  have hPpos : 0 < P := Real.rpow_pos_of_pos hX θ
  set M : ℝ := (m.toNat : ℝ) / (m.toNat.totient : ℝ) with hMdef
  set ρ : ℝ := (r : ℝ) / (r.totient : ℝ) ^ 2 with hρdef
  have hmn : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
    have : ((m.toNat : ℤ)) = m := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  have hφm : 0 < (m.toNat.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hφr : 0 < (r.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hM0 : 0 ≤ M := by positivity
  have hρ0 : 0 ≤ ρ := by positivity
  have hm0 : (0 : ℝ) ≤ m := by exact_mod_cast (show (0 : ℤ) ≤ m by omega)
  -- the twisted term
  have hI := tildeI_abs_le P β hPpos.le hβ1.le m hm
  have hS := tildeSing_norm_le r hr χ m hm hgcd
  have hTw : ‖(tildeI P β m : ℂ) * tildeSing r χ m‖ ≤ X * M * ρ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |tildeI P β m| * ‖tildeSing r χ m‖ ≤ (m : ℝ) * (ρ * M) :=
          mul_le_mul hI hS (norm_nonneg _) hm0
      _ ≤ X * (ρ * M) := mul_le_mul_of_nonneg_right hmX (by positivity)
      _ = X * M * ρ := by ring
  -- the first error term
  have hχm : ‖χ (m : ZMod r)‖ ^ 2 ≤ 1 := by
    have := DirichletCharacter.norm_le_one χ (m : ZMod r)
    have h0 := norm_nonneg (χ (m : ZMod r))
    nlinarith
  have hE1 : C * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) * m * X /
      ((r.totient : ℝ) ^ 2 * (m.toNat.totient : ℝ)) ≤ C * X * M * ρ := by
    have he : C * X * M * ρ = C * 1 * (r : ℝ) * m * X /
        ((r.totient : ℝ) ^ 2 * (m.toNat.totient : ℝ)) := by
      rw [hMdef, hρdef, hmn]; field_simp
    rw [he]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : 0 ≤ (r : ℝ) * m * X := by positivity
    have h2 : C * ‖χ (m : ZMod r)‖ ^ 2 ≤ C * 1 := mul_le_mul_of_nonneg_left hχm hC.le
    calc C * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) * m * X
        = (C * ‖χ (m : ZMod r)‖ ^ 2) * ((r : ℝ) * m * X) := by ring
      _ ≤ (C * 1) * ((r : ℝ) * m * X) := mul_le_mul_of_nonneg_right h2 this
      _ = C * 1 * (r : ℝ) * m * X := by ring
  -- the Gamma terms
  have hD0 : 0 ≤ C * divisorError r P m := le_trans (by positivity) hΓ
  have hG : |X * Γ₁ + X * Γ₂| ≤ X * (C * divisorError r P m) := by
    calc |X * Γ₁ + X * Γ₂| ≤ |X * Γ₁| + |X * Γ₂| := abs_add_le _ _
      _ = X * (|Γ₁| + |Γ₂|) := by rw [abs_mul, abs_mul, abs_of_pos hX]; ring
      _ ≤ X * (C * divisorError r P m) := mul_le_mul_of_nonneg_left hΓ hX.le
  have hDiv0 : 0 ≤ divisorError r P m := by
    by_contra hneg; push_neg at hneg; nlinarith
  -- assemble
  set E3 : ℝ := C * X * M * (1 - β) * Real.exp (-(c₂ / θ)) * Real.log P with hE3
  have h1β : 0 ≤ 1 - β := by linarith
  have hlogP : 0 ≤ Real.log P := by
    by_contra hl; push_neg at hl
    have : P ≤ 1 := by
      by_contra h'; push_neg at h'; exact absurd (Real.log_pos h') (by linarith)
    have : (r : ℝ) ≤ 1 := le_trans hrP this
    have : r ≤ 1 := by exact_mod_cast this
    omega
  have hbase : 0 ≤ X * M * (1 - β) * Real.exp (-(c₂ / θ)) * Real.log P :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hX.le hM0) h1β) (Real.exp_pos _).le) hlogP
  have hre : |(R1 P X m).re - m * singSeries m| ≤
      ‖R1 P X m - ((m * singSeries m : ℝ) : ℂ) - (tildeI P β m : ℂ) * tildeSing r χ m -
        ((X * Γ₁ + X * Γ₂ : ℝ) : ℂ)‖ + ‖(tildeI P β m : ℂ) * tildeSing r χ m‖ +
        |X * Γ₁ + X * Γ₂| := by
    set Z : ℂ := (tildeI P β m : ℂ) * tildeSing r χ m
    have hsplit : R1 P X m - ((m * singSeries m : ℝ) : ℂ) =
        (R1 P X m - ((m * singSeries m : ℝ) : ℂ) - Z - ((X * Γ₁ + X * Γ₂ : ℝ) : ℂ)) + Z +
          ((X * Γ₁ + X * Γ₂ : ℝ) : ℂ) := by ring
    have hreq : (R1 P X m).re - m * singSeries m =
        (R1 P X m - ((m * singSeries m : ℝ) : ℂ)).re := by simp
    rw [hreq]
    calc |(R1 P X m - ((m * singSeries m : ℝ) : ℂ)).re|
        ≤ ‖R1 P X m - ((m * singSeries m : ℝ) : ℂ)‖ := Complex.abs_re_le_norm _
      _ = ‖(R1 P X m - ((m * singSeries m : ℝ) : ℂ) - Z - ((X * Γ₁ + X * Γ₂ : ℝ) : ℂ)) + Z +
          ((X * Γ₁ + X * Γ₂ : ℝ) : ℂ)‖ := by rw [← hsplit]
      _ ≤ _ := by
          refine (norm_add_le _ _).trans ?_
          refine add_le_add (norm_add_le _ _) ?_
          rw [Complex.norm_real, Real.norm_eq_abs]
  have hCM : 0 ≤ X * M * ρ := by positivity
  calc |(R1 P X m).re - m * singSeries m|
      ≤ (C * X * M * ρ + E3) + X * M * ρ + X * (C * divisorError r P m) := by
        refine hre.trans ?_
        have h1 := hR.trans (add_le_add hE1 le_rfl)
        have h2 : |X * Γ₁ + X * Γ₂| ≤ X * (C * divisorError r P m) := hG
        linarith
    _ ≤ (3 * C + 1) * X * divisorError r P m + (3 * C + 1) * X * M * ρ +
        (3 * C + 1) * X * M * (1 - β) * Real.exp (-(c₂ / θ)) * Real.log P := by
        have hX0 := hX.le
        have hk1 : X * (C * divisorError r P m) ≤ (3 * C + 1) * X * divisorError r P m := by
          have h0 : 0 ≤ X * divisorError r P m := mul_nonneg hX0 hDiv0
          have he : (3 * C + 1) * X * divisorError r P m - X * (C * divisorError r P m) =
              (2 * C + 1) * (X * divisorError r P m) := by ring
          have : 0 ≤ (2 * C + 1) * (X * divisorError r P m) := mul_nonneg (by positivity) h0
          linarith
        have hk2 : C * X * M * ρ + X * M * ρ ≤ (3 * C + 1) * X * M * ρ := by
          have he : (3 * C + 1) * X * M * ρ - (C * X * M * ρ + X * M * ρ) =
              (2 * C) * (X * M * ρ) := by ring
          have : 0 ≤ (2 * C) * (X * M * ρ) := mul_nonneg (by positivity) hCM
          linarith
        have hk3 : E3 ≤ (3 * C + 1) * X * M * (1 - β) * Real.exp (-(c₂ / θ)) * Real.log P := by
          have hE : E3 = C * (X * M * (1 - β) * Real.exp (-(c₂ / θ)) * Real.log P) := by
            rw [hE3]; ring
          have hE' : (3 * C + 1) * X * M * (1 - β) * Real.exp (-(c₂ / θ)) * Real.log P =
              (3 * C + 1) * (X * M * (1 - β) * Real.exp (-(c₂ / θ)) * Real.log P) := by ring
          have h0 := hbase
          rw [hE, hE']
          have : C * (X * M * (1 - β) * Real.exp (-(c₂ / θ)) * Real.log P) ≤
              (3 * C + 1) * (X * M * (1 - β) * Real.exp (-(c₂ / θ)) * Real.log P) :=
            mul_le_mul_of_nonneg_right (by linarith) h0
          exact this
        linarith

/-- `BPLemma3CoprimeHyp` from the LEAF `leaf_bp_lemma3_printed`. Its only open input is that
LEAF, the citation wall Montgomery and Vaughan 1975 6.17, 6.19 and 7.1. -/
theorem bpLemma3Coprime_split : BPLemma3CoprimeHyp :=
  bpLemma3Coprime_of_printed leaf_bp_lemma3_printed

end LeanLab.ExceptionalSet.UpJ200.SplitBPLemma3Coprime

#print axioms LeanLab.ExceptionalSet.UpJ200.SplitBPLemma3Coprime.tildeI_abs_le
#print axioms LeanLab.ExceptionalSet.UpJ200.SplitBPLemma3Coprime.partial_le
#print axioms LeanLab.ExceptionalSet.UpJ200.SplitBPLemma3Coprime.tildeSing_norm_le
#print axioms LeanLab.ExceptionalSet.UpJ200.SplitBPLemma3Coprime.bpLemma3Coprime_of_printed
#print axioms LeanLab.ExceptionalSet.UpJ200.SplitBPLemma3Coprime.bpLemma3Coprime_split
