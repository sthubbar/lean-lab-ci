import LeanLab.ExceptionalSet.UpJ200.Decomp559b
import LeanLab.Zinoviev1997.TotientTail

/-!
CITED WALL DECISION for `Decomp559b.leaf_coprime_selected`, session CLOUD-cited-leaf_coprime_selected,
2026-11-20. P0082, Brudern and Perelli 1998, Ann. Inst. Fourier 48, page 363 case ii a.

DECISION: NAMED HYPOTHESIS. Case ii a is a short deduction on page 363 from three cited inputs:
* `BPLemma3CoprimeHyp`: Lemma 3 on page 358, which is Montgomery and Vaughan 1975 formula 6.17
  with the error of their 6.19 kept explicit, specialised to an even m coprime to the exceptional
  modulus, with the twisted term absorbed by displays 12 and 13 as on page 363 case ii a and the
  Gamma terms bounded by the envelopes 14 and 15, which is `divisorError`.
* `SingSeriesLowerHyp`: the bound on page 362 case i that the singular series of display 11
  is at least a constant times m over phi of m for even m.
* `LandauRealZeroHyp`: the lower bound on 1 minus beta of display 10, Davenport chapter 14.

The conditional assembly below proves the exact statement of the leaf from these three Props,
with no sorry. The totient step uses the proved `Zinoviev1997.seventh_le_totient_eighth`.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)
open LeanLab.ExceptionalSet.UpJ200.Decomp559b (SelectedRealZero)

/-- P0082 page 358 display 11, the singular series
`𝔖(m) = ∏_{p ∤ m} (1 - 1/(p-1)^2) ∏_{p ∣ m} (1 + 1/(p-1))`, one factor per prime. -/
noncomputable def singSeries (m : ℤ) : ℝ :=
  ∏' p : Nat.Primes, (if ((p : ℕ) : ℤ) ∣ m then 1 + 1 / (((p : ℕ) : ℝ) - 1)
    else 1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2)

/-- NAMED HYPOTHESIS, cited standard bound. P0082 page 362 case i:
`𝔖(m) ≫ m / φ(m)` for `m ≡ 0 (mod 2)`. Montgomery and Vaughan 1975 section 6. -/
def SingSeriesLowerHyp : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ m : ℤ, 1 ≤ m → Even m →
    c₀ * ((m.toNat : ℝ) / (m.toNat.totient : ℝ)) ≤ singSeries m

/-- NAMED HYPOTHESIS, cited standard theorem. P0082 page 358 display 10, left inequality,
from Davenport, Multiplicative Number Theory, chapter 14: a real zero `β < 1` of the
L function of a real nonprincipal primitive character modulo `r` satisfies
`1 - β ≫ r^{-1/2} (log r)^{-2}`, with an absolute constant. -/
def LandauRealZeroHyp : Prop :=
  ∃ c₃ : ℝ, 0 < c₃ ∧ ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
    χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → β < 1 → χ.LFunction β = 0 →
      c₃ / (Real.sqrt r * Real.log r ^ 2) ≤ 1 - β

/-- NAMED HYPOTHESIS, cited result. P0082 page 358 Lemma 3, which is Montgomery and Vaughan
1975 formula 6.17 with the error of 6.19 kept explicit, here with `P = X^θ`,
`θ = 6 δ < 6/100` as on page 357. It is specialised to an even `1 ≤ m ≤ X` coprime to the
exceptional modulus `r`, where `χ(m)^2 = 1`. The term `I(m) 𝔖~(m)` is moved into the error
by displays 12 and 13 exactly as on page 363 case ii a, `|I(m)| ≤ m ≤ X` and
`|𝔖~(m)| ≤ (r / φ(r)^2) (m / φ(m))`, and the terms `X Γ₁(m) + X Γ₂(m)` are bounded by the
envelopes of displays 14 and 15, which are `divisorError`. The constants may depend on the
parameter `a` of the selected zero region, see the notes for why that is harmless. -/
def BPLemma3CoprimeHyp : Prop :=
  ∀ a : ℝ, 0 < a → ∃ C c₂ : ℝ, 0 < C ∧ 0 < c₂ ∧ ∃ P₀ : ℝ,
    ∀ θ : ℝ, 0 < θ → θ < 6 / 100 → ∀ X : ℝ, 0 < X → P₀ ≤ X ^ θ →
    ∀ r : ℕ, 1 ≤ r → r ≠ 1 → (r : ℝ) ≤ X ^ θ → SelectedRealZero a (X ^ θ) r →
    ∀ (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 1 - a / Real.log (X ^ θ) ≤ β → β < 1 →
      χ.LFunction β = 0 →
      ∀ m : ℤ, 1 ≤ m → (m : ℝ) ≤ X → Even m → Int.gcd m r = 1 →
        |(R1 (X ^ θ) X m).re - m * singSeries m| ≤
          C * X * divisorError r (X ^ θ) m +
          C * X * ((m.toNat : ℝ) / (m.toNat.totient : ℝ)) * ((r : ℝ) / (r.totient : ℝ) ^ 2) +
          C * X * ((m.toNat : ℝ) / (m.toNat.totient : ℝ)) * (1 - β) *
            Real.exp (-(c₂ / θ)) * Real.log (X ^ θ)

/-- Final arithmetic of page 363 case ii a, proved. -/
theorem combine_ii_a (c₀ C X M mS R D E2 E3 : ℝ) (hc₀ : 0 < c₀) (hX : 0 ≤ X) (hM : 1 ≤ M)
    (h : |R - mS| ≤ C * X * D + E2 + E3) (hmS : c₀ * X * M / 2 ≤ mS)
    (hE2 : E2 ≤ X * M * c₀ / 8) (hE3 : E3 ≤ X * M * c₀ / 8) :
    c₀ / 4 * X ≤ R + C * X * D := by
  have h' := (abs_le.mp h).1
  have hk : 0 ≤ c₀ * X * (M - 1) := mul_nonneg (mul_nonneg hc₀.le hX) (sub_nonneg.mpr hM)
  nlinarith

/-- Display 10 with the totient bound: a selected modulus `r ≥ 2` with
`c₃ / r^3 ≤ a / log P` and `log P` large has `r / φ(r)^2 ≤ ε`. Proved. -/
theorem ratio_small (r : ℕ) (hr : 2 ≤ r) (ε : ℝ) (hε : 0 < ε)
    (hr3 : 2401 / ε ^ 4 ≤ (r : ℝ) ^ 3) :
    (r : ℝ) / (r.totient : ℝ) ^ 2 ≤ ε := by
  have h7 := LeanLab.Zinoviev1997.seventh_le_totient_eighth r (by omega)
  have h7R : (r : ℝ) ^ 7 ≤ 2401 * (r.totient : ℝ) ^ 8 := by exact_mod_cast h7
  have hφ : 0 < (r.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  rw [div_le_iff₀ (by positivity)]
  by_contra hcon0
  have hcon := not_le.mp hcon0
  have h4 : (ε * (r.totient : ℝ) ^ 2) ^ 4 < (r : ℝ) ^ 4 :=
    pow_lt_pow_left₀ hcon (by positivity) (by norm_num)
  have hε4 : 0 < ε ^ 4 := by positivity
  have hA : 2401 ≤ ε ^ 4 * (r : ℝ) ^ 3 := by
    rw [div_le_iff₀ hε4] at hr3; linarith
  have hB : (ε * (r.totient : ℝ) ^ 2) ^ 4 = ε ^ 4 * (r.totient : ℝ) ^ 8 := by ring
  have hC : (r : ℝ) ^ 4 * 2401 ≤ (r : ℝ) ^ 4 * (ε ^ 4 * (r : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  have hD : ε ^ 4 * (r : ℝ) ^ 7 ≤ ε ^ 4 * (2401 * (r.totient : ℝ) ^ 8) :=
    mul_le_mul_of_nonneg_left h7R hε4.le
  have hr4 : 0 < (r : ℝ) ^ 4 := by positivity
  nlinarith

/-- `√r (log r)^2 ≤ r^3` for `r ≥ 1`. Proved. -/
theorem sqrt_log_sq_le (r : ℝ) (hr : 1 ≤ r) : Real.sqrt r * Real.log r ^ 2 ≤ r ^ 3 := by
  have hs : Real.sqrt r ≤ r := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hl0 : 0 ≤ Real.log r := Real.log_nonneg hr
  have hl : Real.log r ≤ r := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < r); linarith
  have hl2 : Real.log r ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hl0 hl 2
  calc Real.sqrt r * Real.log r ^ 2 ≤ r * r ^ 2 :=
        mul_le_mul hs hl2 (by positivity) (by linarith)
    _ = r ^ 3 := by ring

/-- P0082 page 363 case ii a. The exact statement of `Decomp559b.leaf_coprime_selected`.
CONDITIONAL ON `BPLemma3CoprimeHyp`, `SingSeriesLowerHyp` and `LandauRealZeroHyp`; no sorry. -/
theorem leaf_coprime_selected_of_hyps (hL3 : BPLemma3CoprimeHyp) (hS : SingSeriesLowerHyp)
    (hLa : LandauRealZeroHyp) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) → ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              r ≠ 1 → Int.gcd (nu γ n + j) r = 1 →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
  obtain ⟨C, c₂, hC, hc₂, P₀, hL⟩ := hL3 a ha
  obtain ⟨c₀, hc₀, hSing⟩ := hS
  obtain ⟨c₃, hc₃, hLand⟩ := hLa
  have hε : 0 < c₀ / (8 * C) := by positivity
  refine ⟨min (1 / 100) (c₀ * c₂ / (48 * C * a)), lt_min (by norm_num) (by positivity), ?_⟩
  intro δ hδ hδs
  have hδ1 : δ < 1 / 100 := lt_of_lt_of_le hδs (min_le_left _ _)
  have hδ2 : δ < c₀ * c₂ / (48 * C * a) := lt_of_lt_of_le hδs (min_le_right _ _)
  refine ⟨1, one_pos, ?_⟩
  intro κ _ _
  refine ⟨c₀ / 4, C, by positivity, hC, ?_⟩
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hF : Tendsto (fun N : ℕ => F γ N) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by linarith : 0 < γ)).comp hlog)
  have hP : Tendsto (fun N : ℕ => F γ N ^ (6 * δ)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < 6 * δ)).comp hF
  set L : ℝ := a * (2401 / (c₀ / (8 * C)) ^ 4) / c₃ with hLdef
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (hP.eventually_ge_atTop (max P₀ (max 2 (Real.exp L))))
  refine ⟨N₀, ?_⟩
  intro N hN r hr hrP hsel j hj n hn heven hm hr1 hgcd
  have hPge := hN₀ N hN
  simp only [max_le_iff] at hPge
  obtain ⟨hP0, hP2, hPL⟩ := hPge
  have hX : 0 < F γ N := Real.exp_pos _
  have hlogPpos : 0 < Real.log (F γ N ^ (6 * δ)) := Real.log_pos (by linarith)
  have hlogPL : L ≤ Real.log (F γ N ^ (6 * δ)) := by
    rw [← Real.log_exp L]; exact Real.log_le_log (Real.exp_pos _) hPL
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
  have hbound := hL (6 * δ) (by positivity) (by linarith) (F γ N) hX hP0 r hr hr1 hrP hsel
    hrz χ β hχ hχ2 hχne hβlo hβone hβzero (nu γ n + j) hm1 hm heven hgcd
  -- m / φ(m) ≥ 1
  set m : ℤ := nu γ n + j with hmdef
  set M : ℝ := (m.toNat : ℝ) / (m.toNat.totient : ℝ) with hMdef
  have hmt : 1 ≤ m.toNat := by omega
  have hφm : 0 < (m.toNat.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hM1 : 1 ≤ M := by
    rw [hMdef, one_le_div hφm]; exact_mod_cast Nat.totient_le _
  have hM0 : 0 ≤ M := by linarith
  -- main term
  have hS := hSing m hm1 heven
  have hmS : c₀ * F γ N * M / 2 ≤ (m : ℝ) * singSeries m := by
    have h0 : 0 ≤ c₀ * M := by positivity
    have hA : (m : ℝ) * (c₀ * M) ≤ (m : ℝ) * singSeries m :=
      mul_le_mul_of_nonneg_left hS (by linarith)
    nlinarith
  -- display 10 gives r / φ(r)^2 small
  have hr2 : 2 ≤ r := by omega
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hland := hLand r hrz χ β hχ hχ2 hχne hβone hβzero
  have hden : 0 < Real.sqrt r * Real.log r ^ 2 := by
    have : 0 < Real.log r := Real.log_pos (by exact_mod_cast (show 1 < r by omega))
    positivity
  have hβa : (1 - β) * Real.log (F γ N ^ (6 * δ)) ≤ a := by
    have : 1 - β ≤ a / Real.log (F γ N ^ (6 * δ)) := by linarith
    exact (le_div_iff₀ hlogPpos).mp this
  have hr3 : 2401 / (c₀ / (8 * C)) ^ 4 ≤ (r : ℝ) ^ 3 := by
    have hsl := sqrt_log_sq_le r hrR
    have hq : c₃ / (r : ℝ) ^ 3 ≤ c₃ / (Real.sqrt r * Real.log r ^ 2) :=
      div_le_div_of_nonneg_left hc₃.le hden hsl
    have hq2 : c₃ / (r : ℝ) ^ 3 * Real.log (F γ N ^ (6 * δ)) ≤ a := by
      have := mul_le_mul_of_nonneg_right (hq.trans hland) hlogPpos.le
      linarith
    have hr3pos : 0 < (r : ℝ) ^ 3 := by positivity
    have hq3 : c₃ * Real.log (F γ N ^ (6 * δ)) ≤ a * (r : ℝ) ^ 3 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hr3pos] at hq2; exact hq2
    have hq4 : c₃ * L ≤ a * (r : ℝ) ^ 3 :=
      le_trans (mul_le_mul_of_nonneg_left hlogPL hc₃.le) hq3
    have hcL : c₃ * L = a * (2401 / (c₀ / (8 * C)) ^ 4) := by
      rw [hLdef]; field_simp
    rw [hcL] at hq4
    exact le_of_mul_le_mul_left hq4 ha
  have hρ := ratio_small r hr2 _ hε hr3
  have hCX : 0 ≤ C * F γ N * M := by positivity
  have hE2 : C * F γ N * M * ((r : ℝ) / (r.totient : ℝ) ^ 2) ≤ F γ N * M * c₀ / 8 := by
    have := mul_le_mul_of_nonneg_left hρ hCX
    have he : C * F γ N * M * (c₀ / (8 * C)) = F γ N * M * c₀ / 8 := by
      field_simp
    linarith
  -- the exponential factor is small for small δ
  have hexp : Real.exp (-(c₂ / (6 * δ))) ≤ 6 * δ / c₂ := by
    have hx : 0 < c₂ / (6 * δ) := by positivity
    have hx2 : c₂ / (6 * δ) ≤ Real.exp (c₂ / (6 * δ)) := by
      have := Real.add_one_le_exp (c₂ / (6 * δ)); linarith
    rw [Real.exp_neg, ← one_div]
    calc 1 / Real.exp (c₂ / (6 * δ)) ≤ 1 / (c₂ / (6 * δ)) :=
          one_div_le_one_div_of_le hx hx2
      _ = 6 * δ / c₂ := by rw [one_div_div]
  have h1β : 0 ≤ 1 - β := by linarith
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
  have hb' : |(R1 (F γ N ^ (6 * δ)) (F γ N) m).re - m * singSeries m| ≤
      C * F γ N * divisorError r (F γ N ^ (6 * δ)) m +
        C * F γ N * M * ((r : ℝ) / (r.totient : ℝ) ^ 2) +
        C * F γ N * M * (1 - β) * Real.exp (-(c₂ / (6 * δ))) *
          Real.log (F γ N ^ (6 * δ)) := hbound
  exact combine_ii_a c₀ C (F γ N) M _ _ _ _ _ hc₀ hX.le hM1 hb' hmS hE2 hE3

/-- Twin check: the conditional theorem has the leaf's statement verbatim, so the leaf
follows from the three named hypotheses. -/
theorem leaf_coprime_selected_twin (hL3 : BPLemma3CoprimeHyp) (hS : SingSeriesLowerHyp)
    (hLa : LandauRealZeroHyp) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (a : ℝ) (ha : 0 < a) :
    (∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) → ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              r ≠ 1 → Int.gcd (nu γ n + j) r = 1 →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j)) := by
  have h := leaf_coprime_selected_of_hyps hL3 hS hLa γ h1 h2 a ha
  have _sameType : type_of% h = type_of% (Decomp559b.leaf_coprime_selected γ h1 h2 a ha) := rfl
  exact h

end LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected

#print axioms LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected.combine_ii_a
#print axioms LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected.ratio_small
#print axioms LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected.sqrt_log_sq_le
#print axioms LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected.leaf_coprime_selected_of_hyps
#print axioms LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected.leaf_coprime_selected_twin
