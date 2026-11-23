import LeanLab.ExceptionalSet.UpJ200.DQDisplay21P0082
import LeanLab.ExceptionalSet.UpJ200.DQLeafPrimeProductSelectedDecisions
import LeanLab.ExceptionalSet.Prep1121SingSeries

/-!
ROUTE for unit P1122-0125, burst-20261122 session S31. P0082, Bruedern and Perelli 1998,
Ann. Inst. Fourier 48, https://doi.org/10.5802/aif.1621, page 363 case ii b.

The wall `DQLeafPrimeProductSelected.PrimeProductSelectedP0082` is split into:
* `BPLemma3Hyp`: Lemma 3 of page 358, the CITED Montgomery and Vaughan 1975 formula 6.17 with
  the error of 6.19 kept explicit, the Gamma terms bounded by the envelopes of displays 14 and
  15, which is `divisorError`. Citation wall, stays a named hypothesis.
* `DQLeafCoprimeSelected.SingSeriesLowerHyp`: `𝔖(m) ≫ m / φ(m)` for even `m`, page 362 case
  i, the same named input the sibling case ii a uses.
* Display 21 and its consequence `|𝔖~(m)| ≤ 𝔖(m)/3`, and `|I~(m)| ≤ m`: PROVED in
  `DQDisplay21P0082`.
* The vanishing of the middle error term of display 20: `χ~(m) = 0` when `(m, r~) > 1`. PROVED
  below.

`leaf_prime_product_selected_of_hyps` proves the statement of the wall and of
`Decomp559b.leaf_prime_product_selected`, CONDITIONAL ON the two named hypotheses, with no
sorry. The Landau bound of display 10 is not needed in case ii b.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)
open LeanLab.ExceptionalSet.UpJ200.Decomp559b (SelectedRealZero)
open LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected (singSeries SingSeriesLowerHyp)
open LeanLab.ExceptionalSet.UpJ200.DQDisplay21P0082 (twistedSing Itilde)

/-- NAMED HYPOTHESIS, cited result. P0082 page 358 Lemma 3 with the definitions of page 359
displays 12 and 13: if the exceptional character `χ~` of modulus `r~` exists, with zero `β~`,
then for `m ≤ X`
`R₁(m) = m 𝔖(m) + I~(m) 𝔖~(m) + X Γ₁(m) + X Γ₂(m)
  + O(χ~(m)² r~ m X / (φ(r~)² φ(m))) + O(m X / φ(m) (1 - β~) exp(-c₂ log X / log P) log P)`.
Here `P = X^θ` with `θ = 6 δ < 6/100` as on page 357, so `log X / log P = 1/θ`, and the
terms `X Γ₁(m) + X Γ₂(m)` are bounded by the envelopes of displays 14 and 15, `divisorError`.
Stated for even `1 ≤ m ≤ X`, the only `m` the paper uses. The constants may depend on the
parameter `a` of the selected zero region, as in the sibling `BPLemma3CoprimeHyp`; the
threshold `P₀` may depend on `θ`, since the paper fixes `δ` on page 357 before taking `X`
large, and the divisor bound `d(m) ≪ X^ε` behind Montgomery and Vaughan 6.17 needs `X`
large in terms of `θ`. The constants `C` and `c₂` do not depend on `θ`. This is
Montgomery and Vaughan 1975 formula 6.17 with the error of 6.19 kept explicit, followed by
their 7.1; a citation wall. -/
def BPLemma3Hyp : Prop :=
  ∀ a : ℝ, 0 < a → ∃ C c₂ : ℝ, 0 < C ∧ 0 < c₂ ∧
    ∀ θ : ℝ, 0 < θ → θ < 6 / 100 → ∃ P₀ : ℝ, ∀ X : ℝ, 0 < X → P₀ ≤ X ^ θ →
    ∀ r : ℕ, 1 ≤ r → r ≠ 1 → (r : ℝ) ≤ X ^ θ → SelectedRealZero a (X ^ θ) r →
    ∀ (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 1 - a / Real.log (X ^ θ) ≤ β → β < 1 →
      χ.LFunction β = 0 →
      ∀ m : ℤ, 1 ≤ m → (m : ℝ) ≤ X → Even m →
        |(R1 (X ^ θ) X m).re - (m * singSeries m + Itilde β (X ^ θ) m * twistedSing χ m)| ≤
          C * X * divisorError r (X ^ θ) m +
          C * X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 *
            ((m.toNat : ℝ) / (m.toNat.totient : ℝ)) +
          C * X * ((m.toNat : ℝ) / (m.toNat.totient : ℝ)) * (1 - β) *
            Real.exp (-(c₂ / θ)) * Real.log (X ^ θ)

/-- P0082 page 363 case ii b, first sentence: if `(m, r~) > 1` then `χ~(m) = 0`, so the
middle error term of display 20 vanishes. PROVED. -/
theorem char_vanishes {r : ℕ} (χ : DirichletCharacter ℂ r) (m : ℤ) (hm : 0 ≤ m)
    (hg : 1 < Int.gcd m r) : χ (m : ZMod r) = 0 := by
  apply MulChar.map_nonunit
  intro hu
  have hcast : (m : ZMod r) = ((m.toNat : ℕ) : ZMod r) := by
    have h := congrArg (fun z : ℤ => (z : ZMod r)) (Int.toNat_of_nonneg hm)
    simp only [Int.cast_natCast] at h
    exact h.symm
  rw [hcast, ZMod.isUnit_iff_coprime] at hu
  have hgcd : Int.gcd m r = Nat.gcd m.toNat r := by
    have : m.natAbs = m.toNat := by omega
    show Nat.gcd m.natAbs r = _
    rw [this]
  rw [hgcd, Nat.Coprime.gcd_eq_one hu] at hg
  exact lt_irrefl _ hg

/-- Final arithmetic of page 363 case ii b. With `|R - (m𝔖 + I~𝔖~)| ≤ C X D + E`,
`|I~ 𝔖~| ≤ m𝔖/3`, `m𝔖 ≥ c₀ X M / 2`, `E ≤ c₀ X M / 8` and `M ≥ 1`:
`R + C X D ≥ (c₀/8) X`. PROVED. -/
theorem combine_ii_b (c₀ C X M mS IS R D E : ℝ) (hc₀ : 0 < c₀) (hX : 0 ≤ X) (hM : 1 ≤ M)
    (h : |R - (mS + IS)| ≤ C * X * D + E) (hIS : |IS| ≤ mS / 3)
    (hmS : c₀ * X * M / 2 ≤ mS) (hE : E ≤ X * M * c₀ / 8) :
    c₀ / 8 * X ≤ R + C * X * D := by
  have h' := (abs_le.mp h).1
  have hI := (abs_le.mp hIS).1
  have hk : 0 ≤ c₀ * X * (M - 1) := mul_nonneg (mul_nonneg hc₀.le hX) (sub_nonneg.mpr hM)
  nlinarith

/-- P0082 page 363 case ii b. The exact statement of `PrimeProductSelectedP0082`, the wall
for `Decomp559b.leaf_prime_product_selected`. CONDITIONAL ON `BPLemma3Hyp` and
`SingSeriesLowerHyp`; no sorry. -/
theorem leaf_prime_product_selected_of_hyps (hL3 : BPLemma3Hyp) (hS : SingSeriesLowerHyp) :
    DQLeafPrimeProductSelected.PrimeProductSelectedP0082 := by
  intro γ h1 h2 a ha
  obtain ⟨C, c₂, hC, hc₂, hL⟩ := hL3 a ha
  obtain ⟨c₀, hc₀, hSing⟩ := hS
  refine ⟨min (1 / 100) (c₀ * c₂ / (48 * C * a)), lt_min (by norm_num) (by positivity), ?_⟩
  intro δ hδ hδs
  have hδ1 : δ < 1 / 100 := lt_of_lt_of_le hδs (min_le_left _ _)
  have hδ2 : δ < c₀ * c₂ / (48 * C * a) := lt_of_lt_of_le hδs (min_le_right _ _)
  refine ⟨1, one_pos, ?_⟩
  obtain ⟨P₀, hL⟩ := hL (6 * δ) (by positivity) (by linarith)
  intro κ _ _
  refine ⟨c₀ / 8, C, by positivity, hC, ?_⟩
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hF : Tendsto (fun N : ℕ => F γ N) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by linarith : 0 < γ)).comp hlog)
  have hP : Tendsto (fun N : ℕ => F γ N ^ (6 * δ)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < 6 * δ)).comp hF
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hP.eventually_ge_atTop (max P₀ 2))
  refine ⟨N₀, ?_⟩
  intro N hN r hr hrP hsel j hj n hn heven hm hgcd hex
  have hPge := hN₀ N hN
  simp only [max_le_iff] at hPge
  obtain ⟨hP0, hP2⟩ := hPge
  have hX : 0 < F γ N := Real.exp_pos _
  have hlogPpos : 0 < Real.log (F γ N ^ (6 * δ)) := Real.log_pos (by linarith)
  have hr1 : r ≠ 1 := by
    rintro rfl
    simp at hgcd
  rcases id hsel with ⟨h1', _⟩ | ⟨hrz, χ, β, hχ, hχ2, hχne, _, hβlo, hβone, hβzero, _⟩
  · exact absurd h1' hr1
  -- the window gives X / 2 < m
  have hwin : F γ N / 2 < (nu γ n : ℝ) := by
    simp only [window, Finset.mem_filter] at hn; exact hn.2.1
  have hmR : F γ N / 2 < ((nu γ n + j : ℤ) : ℝ) := by
    rcases hj with rfl | rfl <;> push_cast <;> linarith
  have hm1 : (1 : ℤ) ≤ nu γ n + j := by
    have : (0 : ℝ) < ((nu γ n + j : ℤ) : ℝ) := by linarith
    have : (0 : ℤ) < nu γ n + j := by exact_mod_cast this
    omega
  have hbound := hL (F γ N) hX hP0 r hr hr1 hrP hsel
    hrz χ β hχ hχ2 hχne hβlo hβone hβzero (nu γ n + j) hm1 hm heven
  set m : ℤ := nu γ n + j with hmdef
  -- the middle error term vanishes
  have hχm : χ (m : ZMod r) = 0 := char_vanishes χ m (by omega) hgcd
  rw [hχm, norm_zero] at hbound
  set M : ℝ := (m.toNat : ℝ) / (m.toNat.totient : ℝ) with hMdef
  have hmt : 1 ≤ m.toNat := by omega
  have hφm : 0 < (m.toNat.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hM1 : 1 ≤ M := by
    rw [hMdef, one_le_div hφm]; exact_mod_cast Nat.totient_le _
  -- main term
  have hSm := hSing m hm1 heven
  have hS0 : 0 ≤ singSeries m := DQDisplay21P0082.singSeries_nonneg m
  have hmS : c₀ * F γ N * M / 2 ≤ (m : ℝ) * singSeries m := by
    have h0 : 0 ≤ c₀ * M := by positivity
    have hA : (m : ℝ) * (c₀ * M) ≤ (m : ℝ) * singSeries m :=
      mul_le_mul_of_nonneg_left hSm (by linarith)
    nlinarith
  -- display 21 and the trivial bound for `I~`
  have hm0 : m ≠ 0 := by omega
  have hmpos : (0 : ℝ) ≤ m := by
    have : (0 : ℤ) ≤ m := by omega
    exact_mod_cast this
  have hex' : ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ m := by
    obtain ⟨p, hp, hpr, hp3, hpm⟩ := hex
    exact ⟨p, hp, hpr, hp3, hpm⟩
  have h21 := DQDisplay21P0082.display21_third χ m hm0 heven hex'
  have hI := DQDisplay21P0082.Itilde_abs_le β (F γ N ^ (6 * δ)) hβone.le m (by omega)
  have hIS : |Itilde β (F γ N ^ (6 * δ)) m * twistedSing χ m| ≤ (m : ℝ) * singSeries m / 3 := by
    rw [abs_mul]
    calc |Itilde β (F γ N ^ (6 * δ)) m| * |twistedSing χ m| ≤ (m : ℝ) * (singSeries m / 3) :=
          mul_le_mul hI h21 (abs_nonneg _) hmpos
      _ = (m : ℝ) * singSeries m / 3 := by ring
  -- the exponential factor is small for small δ
  have hexp : Real.exp (-(c₂ / (6 * δ))) ≤ 6 * δ / c₂ := by
    have hx : 0 < c₂ / (6 * δ) := by positivity
    have hx2 : c₂ / (6 * δ) ≤ Real.exp (c₂ / (6 * δ)) := by
      have := Real.add_one_le_exp (c₂ / (6 * δ)); linarith
    rw [Real.exp_neg, ← one_div]
    calc 1 / Real.exp (c₂ / (6 * δ)) ≤ 1 / (c₂ / (6 * δ)) :=
          one_div_le_one_div_of_le hx hx2
      _ = 6 * δ / c₂ := by rw [one_div_div]
  have hβa : (1 - β) * Real.log (F γ N ^ (6 * δ)) ≤ a := by
    have : 1 - β ≤ a / Real.log (F γ N ^ (6 * δ)) := by linarith
    exact (le_div_iff₀ hlogPpos).mp this
  have hCX : 0 ≤ C * F γ N * M := by positivity
  have hE3 : C * F γ N * M * (1 - β) * Real.exp (-(c₂ / (6 * δ))) *
      Real.log (F γ N ^ (6 * δ)) ≤ F γ N * M * c₀ / 8 := by
    have hre : C * F γ N * M * (1 - β) * Real.exp (-(c₂ / (6 * δ))) *
        Real.log (F γ N ^ (6 * δ)) = C * F γ N * M *
          (((1 - β) * Real.log (F γ N ^ (6 * δ))) * Real.exp (-(c₂ / (6 * δ)))) := by ring
    have hprod : ((1 - β) * Real.log (F γ N ^ (6 * δ))) * Real.exp (-(c₂ / (6 * δ))) ≤
        a * (6 * δ / c₂) :=
      mul_le_mul hβa hexp (Real.exp_pos _).le ha.le
    have hsmall : C * (a * (6 * δ / c₂)) ≤ c₀ / 8 := by
      have h48 : δ * (48 * C * a) < c₀ * c₂ := (lt_div_iff₀ (by positivity)).mp hδ2
      rw [show C * (a * (6 * δ / c₂)) = (6 * C * a * δ) / c₂ by ring,
        div_le_iff₀ hc₂]
      nlinarith
    rw [hre]
    calc C * F γ N * M * (((1 - β) * Real.log (F γ N ^ (6 * δ))) *
          Real.exp (-(c₂ / (6 * δ)))) ≤ C * F γ N * M * (a * (6 * δ / c₂)) :=
          mul_le_mul_of_nonneg_left hprod hCX
      _ = F γ N * M * (C * (a * (6 * δ / c₂))) := by ring
      _ ≤ F γ N * M * (c₀ / 8) := mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = F γ N * M * c₀ / 8 := by ring
  have hb' : |(R1 (F γ N ^ (6 * δ)) (F γ N) m).re -
      ((m : ℝ) * singSeries m + Itilde β (F γ N ^ (6 * δ)) m * twistedSing χ m)| ≤
      C * F γ N * divisorError r (F γ N ^ (6 * δ)) m +
        C * F γ N * M * (1 - β) * Real.exp (-(c₂ / (6 * δ))) *
          Real.log (F γ N ^ (6 * δ)) := by
    have hz : C * F γ N * (0 : ℝ) ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M = 0 := by ring
    have := hbound
    rw [hz, add_zero] at this
    exact this
  exact combine_ii_b c₀ C (F γ N) M _ _ _ _ _ hc₀ hX.le hM1 hb' hIS hmS hE3

/-- Twin check: the conditional theorem gives `Decomp559b.leaf_prime_product_selected`'s
statement, through the wall's own conditional theorem. CONDITIONAL ON `BPLemma3Hyp` and
`SingSeriesLowerHyp`. -/
theorem leaf_prime_product_selected_twin (hL3 : BPLemma3Hyp) (hS : SingSeriesLowerHyp)
    (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) → ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n + j) r →
                (∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n + j) →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
  have h := DQLeafPrimeProductSelected.leaf_prime_product_selected_of_hyp
    (leaf_prime_product_selected_of_hyps hL3 hS) γ h1 h2 a ha
  have _sameType : type_of% h =
      type_of% (Decomp559b.leaf_prime_product_selected γ h1 h2 a ha) := rfl
  exact h

/-- P0082 page 363 case ii b with the proved singular series bound
`Prep1121SingSeries.singSeriesLowerHyp_split` plugged in: the wall
`PrimeProductSelectedP0082` follows from Lemma 3 alone. CONDITIONAL ON `BPLemma3Hyp`. -/
theorem prime_product_selected_of_lemma3 (hL3 : BPLemma3Hyp) :
    DQLeafPrimeProductSelected.PrimeProductSelectedP0082 :=
  leaf_prime_product_selected_of_hyps hL3 Prep1121SingSeries.singSeriesLowerHyp_split

end LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082

#print axioms LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082.char_vanishes
#print axioms LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082.combine_ii_b
#print axioms LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082.leaf_prime_product_selected_of_hyps
#print axioms LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082.leaf_prime_product_selected_twin
#print axioms LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082.prime_product_selected_of_lemma3
