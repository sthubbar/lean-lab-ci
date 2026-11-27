import LeanLab.ExceptionalSet.UpJ200.Decomp559b
import LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082
import LeanLab.ExceptionalSet.Prep1121SingSeries

/-!
Split of `leaf_prime_product_selected` of `LeanLab.ExceptionalSet.UpJ200.Decomp559b`
for FREE-nv-glm4 task3893.

The argument is split into one major arc estimate, three arithmetic facts used by that
estimate, and one final inequality. The major arc estimate is the only open leaf. The other
four leaves are proved here from the corresponding elementary results already available in
the lab. The assembly combines the five leaves with the exact constants and thresholds
needed by the original statement.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)
open LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected (singSeries)
open LeanLab.ExceptionalSet.UpJ200.DQDisplay21P0082 (twistedSing Itilde)

/-- LEAF. Major arc estimate for one even frequency. For a selected primitive real
character of conductor `r`, the real part of the major arc integral at an even integer
`m` differs from the main term plus the twisted term by the divisor envelope, the character
error, and the small zero term. This is one frequency estimate with no window index and no
shift parameter. -/
theorem leaf_major_arc_estimate_F3893 (a : ℝ) (ha : 0 < a) :
    ∃ C c₂ : ℝ, 0 < C ∧ 0 < c₂ ∧
      ∀ θ : ℝ, 0 < θ → θ < 6 / 100 →
        ∃ P₀ : ℝ, ∀ X : ℝ, 0 < X → P₀ ≤ X ^ θ →
          ∀ r : ℕ, 1 ≤ r → r ≠ 1 → (r : ℝ) ≤ X ^ θ →
            SelectedRealZero a (X ^ θ) r →
            ∀ (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
              χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
                1 - a / Real.log (X ^ θ) ≤ β → β < 1 →
                χ.LFunction β = 0 →
              ∀ m : ℤ, 1 ≤ m → (m : ℝ) ≤ X → Even m →
                |(R1 (X ^ θ) X m).re -
                    (m * singSeries m + Itilde β (X ^ θ) m * twistedSing χ m)| ≤
                  C * X * divisorError r (X ^ θ) m +
                  C * X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 *
                    ((m.toNat : ℝ) / (m.toNat.totient : ℝ)) +
                  C * X * ((m.toNat : ℝ) / (m.toNat.totient : ℝ)) * (1 - β) *
                    Real.exp (-(c₂ / θ)) * Real.log (X ^ θ) := by
  sorry

/-- LEAF. Character vanishing at a shared factor. If the even integer `m` and the conductor
`r` have gcd greater than one, then the selected character vanishes at `m`. -/
theorem leaf_character_vanishes_F3893 {r : ℕ} (χ : DirichletCharacter ℂ r) (m : ℤ)
    (hm : 0 ≤ m) (hg : 1 < Int.gcd m r) : χ (m : ZMod r) = 0 := by
  exact LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082.char_vanishes χ m hm hg

/-- LEAF. Twisted singular series estimate. If a prime greater than three divides the
conductor but not the even integer `m`, then the absolute value of the twisted singular
series at `m` is at most one third of the ordinary singular series. -/
theorem leaf_twisted_singular_third_F3893 {r : ℕ} [NeZero r]
    (χ : DirichletCharacter ℂ r) (m : ℤ) (hm : m ≠ 0) (he : Even m)
    (hex : ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ m) :
    |twistedSing χ m| ≤ singSeries m / 3 := by
  exact LeanLab.ExceptionalSet.UpJ200.DQDisplay21P0082.display21_third χ m hm he hex

/-- LEAF. Ordinary singular series lower bound. For every positive even integer `m`, the
ordinary singular series is at least a fixed positive constant times `m` divided by the
totient of `m`. -/
theorem leaf_singular_series_lower_F3893 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ m : ℤ, 1 ≤ m → Even m →
      c₀ * ((m.toNat : ℝ) / (m.toNat.totient : ℝ)) ≤ singSeries m := by
  exact LeanLab.ExceptionalSet.Prep1121SingSeries.singSeriesLowerHyp_split

/-- LEAF. Final error combination. If the absolute error is at most the divisor envelope
plus a small middle term, the main term is at least `c₀ X M / 2`, and the middle term is at
most `X M c₀ / 8`, then the real part plus the divisor envelope is at least `c₀ X / 8`. -/
theorem leaf_error_combination_F3893
    (c₀ C X M mS IS R D E : ℝ) (hc₀ : 0 < c₀) (hX : 0 ≤ X) (hM : 1 ≤ M)
    (h : |R - (mS + IS)| ≤ C * X * D + E) (hIS : |IS| ≤ mS / 3)
    (hmS : c₀ * X * M / 2 ≤ mS) (hE : E ≤ X * M * c₀ / 8) :
    c₀ / 8 * X ≤ R + C * X * D := by
  exact LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082.combine_ii_b
    c₀ C X M mS IS R D E hc₀ hX hM h hIS hmS hE

/-- Assembly. The original nonempty prime product case follows from the major arc estimate,
the character vanishing, the twisted singular series estimate, the ordinary singular series
lower bound, and the final error combination. The thresholds and constants are chosen so
that the small zero term is below one eighth of the main term. -/
theorem leaf_prime_product_selected_F3893 (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
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
  obtain ⟨C, c₂, hC, hc₂, hLθ⟩ := leaf_major_arc_estimate_F3893 a ha
  obtain ⟨c₀, hc₀, hSing⟩ := leaf_singular_series_lower_F3893
  refine ⟨min (1 / 100) (c₀ * c₂ / (48 * C * a)),
    lt_min (by norm_num) (by positivity), ?_⟩
  intro δ hδ hδs
  have hδ1 : δ < 1 / 100 := lt_of_lt_of_le hδs (min_le_left _ _)
  have hδ2 : δ < c₀ * c₂ / (48 * C * a) := lt_of_lt_of_le hδs (min_le_right _ _)
  have hθ : 0 < 6 * δ := by positivity
  have hθ6 : 6 * δ < 6 / 100 := by linarith
  obtain ⟨P₀, hL⟩ := hLθ (6 * δ) hθ hθ6
  refine ⟨1, one_pos, ?_⟩
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
  have hwin : F γ N / 2 < (nu γ n : ℝ) := by
    simp only [window, Finset.mem_filter] at hn
    exact hn.2.1
  have hmR : F γ N / 2 < ((nu γ n + j : ℤ) : ℝ) := by
    rcases hj with rfl | rfl <;> push_cast <;> linarith
  have hm1 : (1 : ℤ) ≤ nu γ n + j := by
    have hpos : (0 : ℝ) < ((nu γ n + j : ℤ) : ℝ) := by linarith
    have hpos' : (0 : ℤ) < nu γ n + j := by exact_mod_cast hpos
    omega
  have hbound := hL (F γ N) hX hP0 r hr hr1 hrP hsel
    hrz χ β hχ hχ2 hχne hβlo hβone hβzero (nu γ n + j) hm1 hm heven
  set m : ℤ := nu γ n + j with hmdef
  have hχm : χ (m : ZMod r) = 0 := by
    apply leaf_character_vanishes_F3893 χ m
    · omega
    · simpa [hmdef] using hgcd
  rw [hχm, norm_zero] at hbound
  set M : ℝ := (m.toNat : ℝ) / (m.toNat.totient : ℝ) with hMdef
  have hmt : 1 ≤ m.toNat := by omega
  have hφm : 0 < (m.toNat.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hM1 : 1 ≤ M := by
    rw [hMdef, one_le_div hφm]
    exact_mod_cast Nat.totient_le _
  have hSm := hSing m hm1 heven
  have hS0 : 0 ≤ singSeries m := LeanLab.ExceptionalSet.UpJ200.DQDisplay21P0082.singSeries_nonneg m
  have hmS : c₀ * F γ N * M / 2 ≤ (m : ℝ) * singSeries m := by
    have h0 : 0 ≤ c₀ * M := by positivity
    have hA : (m : ℝ) * (c₀ * M) ≤ (m : ℝ) * singSeries m :=
      mul_le_mul_of_nonneg_left hSm (by linarith)
    nlinarith
  have hm0 : m ≠ 0 := by omega
  have hmpos : (0 : ℝ) ≤ m := by
    have hm0' : (0 : ℤ) ≤ m := by omega
    exact_mod_cast hm0'
  have hex' : ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ m := by
    obtain ⟨p, hp, hpr, hp3, hpm⟩ := hex
    exact ⟨p, hp, hpr, hp3, hpm⟩
  have h21 := leaf_twisted_singular_third_F3893 χ m hm0 heven hex'
  have hI := LeanLab.ExceptionalSet.UpJ200.DQDisplay21P0082.Itilde_abs_le β
    (F γ N ^ (6 * δ)) hβone.le m (by omega)
  have hIS : |Itilde β (F γ N ^ (6 * δ)) m * twistedSing χ m| ≤
      (m : ℝ) * singSeries m / 3 := by
    rw [abs_mul]
    calc |Itilde β (F γ N ^ (6 * δ)) m| * |twistedSing χ m| ≤
          (m : ℝ) * (singSeries m / 3) :=
        mul_le_mul hI h21 (abs_nonneg _) hmpos
      _ = (m : ℝ) * singSeries m / 3 := by ring
  have hexp : Real.exp (-(c₂ / (6 * δ))) ≤ 6 * δ / c₂ := by
    have hx : 0 < c₂ / (6 * δ) := by positivity
    have hx2 : c₂ / (6 * δ) ≤ Real.exp (c₂ / (6 * δ)) := by
      have h := Real.add_one_le_exp (c₂ / (6 * δ))
      linarith
    rw [Real.exp_neg, ← one_div]
    calc 1 / Real.exp (c₂ / (6 * δ)) ≤ 1 / (c₂ / (6 * δ)) :=
          one_div_le_one_div_of_le hx hx2
      _ = 6 * δ / c₂ := by rw [one_div_div]
  have hβa : (1 - β) * Real.log (F γ N ^ (6 * δ)) ≤ a := by
    have hle : 1 - β ≤ a / Real.log (F γ N ^ (6 * δ)) := by linarith
    exact (le_div_iff₀ hlogPpos).mp hle
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
    have h := hbound
    rw [hz, add_zero] at h
    exact h
  exact leaf_error_combination_F3893 c₀ C (F γ N) M _ _ _ _ _ hc₀ hX.le hM1 hb' hIS hmS hE3

end LeanLab.ExceptionalSet.UpJ200.Decomp559b

#print axioms LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_character_vanishes_F3893
#print axioms LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_twisted_singular_third_F3893
#print axioms LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_singular_series_lower_F3893
#print axioms LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_error_combination_F3893
#print axioms LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_prime_product_selected_F3893
