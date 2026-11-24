import LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082
import LeanLab.ExceptionalSet.UpJ200.SplitBPLemma3Coprime
import LeanLab.ExceptionalSet.RealZeroLower672

/-!
Unit caseIIa_lemma3, burst-20261122 session S67. P0082, Bruedern and Perelli 1998,
Ann. Inst. Fourier 48, https://doi.org/10.5802/aif.1621, page 363 case ii a.

The existing proof `Prep1121SingSeries.leaf_coprime_selected_of_two_hyps` rests on
`DQLeafCoprimeSelected.BPLemma3CoprimeHyp`, whose threshold `P₀` is chosen before `θ`. That is
stronger than the paper. Here the same leaf is proved from `DQCaseIIbP0082.BPLemma3Hyp`, whose
threshold `P₀` is chosen after `θ`, as on page 357 of the paper. The proof fixes `δ`, hence
`θ = 6 δ`, before it takes `N₀`, so the later choice of `P₀` costs nothing.

Steps, page 363 case ii a:
* display 12 with `(m, r~) = 1`: `|𝔖~(m)| ≤ (r~ / φ(r~)²) (m / φ(m))`, `twistedSing_abs_le_coprime`;
* display 13: `|I~(m)| ≤ m ≤ X`, `DQDisplay21P0082.Itilde_abs_le`;
* `|χ~(m)|² ≤ 1`, so the middle error of Lemma 3 is at most `C X (r~/φ(r~)²) (m/φ(m))`;
* the twisted term and the middle error are absorbed together, `coprime_bound_of_lemma3`;
* display 10 makes `r~/φ(r~)²` small, and the rest is the arithmetic of the existing proof.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.CaseIIaFromLemma3

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)
open LeanLab.ExceptionalSet.UpJ200.Decomp559b (SelectedRealZero)
open LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected
  (singSeries SingSeriesLowerHyp LandauRealZeroHyp combine_ii_a ratio_small sqrt_log_sq_le)
open LeanLab.ExceptionalSet.UpJ200.DQDisplay21P0082 (twistedSing Itilde singFactor Itilde_abs_le)
open LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082 (BPLemma3Hyp)

/-- P0082 page 359 display 12 and page 363 case ii a: for `(m, r~) = 1`,
`|𝔖~(m)| ≤ (r~ / φ(r~)²) (m / φ(m))`, for the real form `twistedSing` of display 12.
PROVED, from `SplitBPLemma3Coprime.partial_le`. -/
theorem twistedSing_abs_le_coprime {r : ℕ} (hr : 1 ≤ r) (χ : DirichletCharacter ℂ r) (m : ℤ)
    (hm : 1 ≤ m) (hg : Int.gcd m r = 1) :
    |twistedSing χ m| ≤
      ((r : ℝ) / (r.totient : ℝ) ^ 2) * ((m.toNat : ℝ) / (m.toNat.totient : ℝ)) := by
  classical
  have hmn : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg (by omega)
  have hm1 : 1 ≤ m.toNat := by omega
  set G : Nat.Primes → ℝ := fun p => if (p : ℕ) ∣ r then (1 : ℝ) else singFactor m p with hG
  have hGm : G = fun p : Nat.Primes => if (p : ℕ) ∣ r then (1 : ℝ)
      else if (((p : ℕ) : ℤ) ∣ ((m.toNat : ℕ) : ℤ)) then 1 + 1 / (((p : ℕ) : ℝ) - 1)
      else 1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2 := by
    rw [hmn, hG]
    funext p
    simp only [singFactor]
  have hT : 0 ≤ ∏' p, G p ∧ ∏' p, G p ≤ (m.toNat : ℝ) / (m.toNat.totient : ℝ) := by
    by_cases hmul : Multipliable G
    · have hlim := hmul.hasProd
      have hpl := fun s => SplitBPLemma3Coprime.partial_le m.toNat hm1 r s
      rw [← hGm] at hpl
      exact ⟨ge_of_tendsto' hlim (fun s => (hpl s).1), le_of_tendsto' hlim (fun s => (hpl s).2)⟩
    · rw [tprod_eq_one_of_not_multipliable hmul]
      refine ⟨zero_le_one, ?_⟩
      have hφ : 0 < (m.toNat.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
      rw [one_le_div hφ]; exact_mod_cast Nat.totient_le _
  have hφr : 0 < (r.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hχ1 : |(χ (-1)).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans (DirichletCharacter.norm_le_one χ _)
  have hμ : |(ArithmeticFunction.moebius r : ℝ)| ≤ 1 := by
    have := ArithmeticFunction.abs_moebius_le_one (n := r)
    exact_mod_cast this
  have hA : 0 ≤ (r : ℝ) / (r.totient : ℝ) ^ 2 := by positivity
  unfold twistedSing
  rw [← hG, hg, Nat.div_one]
  have hq : (r : ℝ) / ((r.totient : ℝ) * (r.totient : ℝ)) = (r : ℝ) / (r.totient : ℝ) ^ 2 := by
    ring
  rw [hq, abs_mul, abs_mul, abs_mul, abs_of_nonneg hA, abs_of_nonneg hT.1]
  calc |(χ (-1)).re| * |(ArithmeticFunction.moebius r : ℝ)| * ((r : ℝ) / (r.totient : ℝ) ^ 2) *
        ∏' p, G p ≤ 1 * 1 * ((r : ℝ) / (r.totient : ℝ) ^ 2) * ∏' p, G p := by
        have h1 := mul_le_mul hχ1 hμ (abs_nonneg _) zero_le_one
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hA) hT.1
    _ ≤ 1 * 1 * ((r : ℝ) / (r.totient : ℝ) ^ 2) *
        ((m.toNat : ℝ) / (m.toNat.totient : ℝ)) :=
        mul_le_mul_of_nonneg_left hT.2 (by positivity)
    _ = _ := by ring

/-- P0082 page 363 case ii a, first step: Lemma 3 of page 358 in the form `BPLemma3Hyp`, with
the twisted term `I~(m) 𝔖~(m)` bounded by displays 12 and 13 and `m ≤ X`, and with
`|χ~(m)|² ≤ 1`, gives for even `m` coprime to `r~` the bound with the main term `m 𝔖(m)` alone.
The twisted term and the middle error together cost `(C + 1) X (m/φ(m)) (r~/φ(r~)²)`.
The threshold `P₀` still depends on `θ`, as in `BPLemma3Hyp`. PROVED. -/
theorem coprime_bound_of_lemma3 (hL3 : BPLemma3Hyp) :
    ∀ a : ℝ, 0 < a → ∃ C c₂ : ℝ, 0 < C ∧ 0 < c₂ ∧
      ∀ θ : ℝ, 0 < θ → θ < 6 / 100 → ∃ P₀ : ℝ, ∀ X : ℝ, 0 < X → P₀ ≤ X ^ θ →
      ∀ r : ℕ, 1 ≤ r → r ≠ 1 → (r : ℝ) ≤ X ^ θ → SelectedRealZero a (X ^ θ) r →
      ∀ (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
        χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 1 - a / Real.log (X ^ θ) ≤ β → β < 1 →
        χ.LFunction β = 0 →
        ∀ m : ℤ, 1 ≤ m → (m : ℝ) ≤ X → Even m → Int.gcd m r = 1 →
          |(R1 (X ^ θ) X m).re - m * singSeries m| ≤
            C * X * divisorError r (X ^ θ) m +
            (C + 1) * X * ((m.toNat : ℝ) / (m.toNat.totient : ℝ)) *
              ((r : ℝ) / (r.totient : ℝ) ^ 2) +
            C * X * ((m.toNat : ℝ) / (m.toNat.totient : ℝ)) * (1 - β) *
              Real.exp (-(c₂ / θ)) * Real.log (X ^ θ) := by
  intro a ha
  obtain ⟨C, c₂, hC, hc₂, hL⟩ := hL3 a ha
  refine ⟨C, c₂, hC, hc₂, ?_⟩
  intro θ hθ hθ6
  obtain ⟨P₀, hL⟩ := hL θ hθ hθ6
  refine ⟨P₀, ?_⟩
  intro X hX hP0 r hr hr1 hrP hsel hrz χ β hχ hχ2 hχne hβlo hβ1 hβz m hm hmX hev hgcd
  have h := hL X hX hP0 r hr hr1 hrP hsel hrz χ β hχ hχ2 hχne hβlo hβ1 hβz m hm hmX hev
  set M : ℝ := (m.toNat : ℝ) / (m.toNat.totient : ℝ) with hMdef
  set ρ : ℝ := (r : ℝ) / (r.totient : ℝ) ^ 2 with hρdef
  have hφm : 0 < (m.toNat.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hφr : 0 < (r.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hM0 : 0 ≤ M := by positivity
  have hρ0 : 0 ≤ ρ := by positivity
  have hm0 : (0 : ℝ) ≤ m := by exact_mod_cast (show (0 : ℤ) ≤ m by omega)
  -- the twisted term, displays 12 and 13
  have hI := Itilde_abs_le β (X ^ θ) hβ1.le m (by omega)
  have hS := twistedSing_abs_le_coprime hr χ m hm hgcd
  have hTw : |Itilde β (X ^ θ) m * twistedSing χ m| ≤ X * M * ρ := by
    rw [abs_mul]
    calc |Itilde β (X ^ θ) m| * |twistedSing χ m| ≤ (m : ℝ) * (ρ * M) :=
          mul_le_mul hI hS (abs_nonneg _) hm0
      _ ≤ X * (ρ * M) := mul_le_mul_of_nonneg_right hmX (by positivity)
      _ = X * M * ρ := by ring
  -- the middle error term, `|χ~(m)|² ≤ 1`
  have hχm : ‖χ (m : ZMod r)‖ ^ 2 ≤ 1 := by
    have := DirichletCharacter.norm_le_one χ (m : ZMod r)
    have h0 := norm_nonneg (χ (m : ZMod r))
    nlinarith
  have hE1 : C * X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M ≤
      C * X * M * ρ := by
    have he : C * X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M =
        (C * X * M * ρ) * ‖χ (m : ZMod r)‖ ^ 2 := by
      rw [hρdef]; ring
    rw [he]
    have : 0 ≤ C * X * M * ρ := by positivity
    nlinarith
  have h' := abs_le.mp h
  have hT' := abs_le.mp hTw
  rw [abs_le]
  constructor <;> nlinarith

/-- P0082 page 363 case ii a. The exact statement of `Decomp559b.leaf_coprime_selected`,
CONDITIONAL ON `BPLemma3Hyp`, `SingSeriesLowerHyp` and `LandauRealZeroHyp`; no sorry.
The order of choices is the paper's: `δ`, so `θ = 6 δ`, is fixed first, then `P₀` of
Lemma 3, then `N₀`. -/
theorem leaf_coprime_selected_of_lemma3_hyps (hL3 : BPLemma3Hyp) (hS : SingSeriesLowerHyp)
    (hLa : LandauRealZeroHyp) :
    type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_coprime_selected := by
  intro γ h1 h2 a ha
  obtain ⟨C, c₂, hC, hc₂, hL⟩ := coprime_bound_of_lemma3 hL3 a ha
  obtain ⟨c₀, hc₀, hSing⟩ := hS
  obtain ⟨c₃, hc₃, hLand⟩ := hLa
  have hε : 0 < c₀ / (8 * (C + 1)) := by positivity
  refine ⟨min (1 / 100) (c₀ * c₂ / (48 * C * a)), lt_min (by norm_num) (by positivity), ?_⟩
  intro δ hδ hδs
  have hδ1 : δ < 1 / 100 := lt_of_lt_of_le hδs (min_le_left _ _)
  have hδ2 : δ < c₀ * c₂ / (48 * C * a) := lt_of_lt_of_le hδs (min_le_right _ _)
  obtain ⟨P₀, hL⟩ := hL (6 * δ) (by positivity) (by linarith)
  refine ⟨1, one_pos, ?_⟩
  intro κ _ _
  refine ⟨c₀ / 4, C, by positivity, hC, ?_⟩
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hF : Tendsto (fun N : ℕ => F γ N) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by linarith : 0 < γ)).comp hlog)
  have hP : Tendsto (fun N : ℕ => F γ N ^ (6 * δ)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < 6 * δ)).comp hF
  set L : ℝ := a * (2401 / (c₀ / (8 * (C + 1))) ^ 4) / c₃ with hLdef
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
  have hbound := hL (F γ N) hX hP0 r hr hr1 hrP hsel
    hrz χ β hχ hχ2 hχne hβlo hβone hβzero (nu γ n + j) hm1 hm heven hgcd
  set m : ℤ := nu γ n + j with hmdef
  set M : ℝ := (m.toNat : ℝ) / (m.toNat.totient : ℝ) with hMdef
  have hφm : 0 < (m.toNat.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hM1 : 1 ≤ M := by
    rw [hMdef, one_le_div hφm]; exact_mod_cast Nat.totient_le _
  -- main term, page 362 case i
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
  have hr3 : 2401 / (c₀ / (8 * (C + 1))) ^ 4 ≤ (r : ℝ) ^ 3 := by
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
    have hcL : c₃ * L = a * (2401 / (c₀ / (8 * (C + 1))) ^ 4) := by
      rw [hLdef]; field_simp
    rw [hcL] at hq4
    exact le_of_mul_le_mul_left hq4 ha
  have hρ := ratio_small r hr2 _ hε hr3
  have hCX : 0 ≤ (C + 1) * F γ N * M := by positivity
  have hE2 : (C + 1) * F γ N * M * ((r : ℝ) / (r.totient : ℝ) ^ 2) ≤ F γ N * M * c₀ / 8 := by
    have := mul_le_mul_of_nonneg_left hρ hCX
    have he : (C + 1) * F γ N * M * (c₀ / (8 * (C + 1))) = F γ N * M * c₀ / 8 := by
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
  have hCX' : 0 ≤ C * F γ N * M := by positivity
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
          mul_le_mul_of_nonneg_left hprod hCX'
      _ = F γ N * M * (C * (a * (6 * δ / c₂))) := by ring
      _ ≤ F γ N * M * (c₀ / 8) := mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = F γ N * M * c₀ / 8 := by ring
  have hb' : |(R1 (F γ N ^ (6 * δ)) (F γ N) m).re - m * singSeries m| ≤
      C * F γ N * divisorError r (F γ N ^ (6 * δ)) m +
        (C + 1) * F γ N * M * ((r : ℝ) / (r.totient : ℝ) ^ 2) +
        C * F γ N * M * (1 - β) * Real.exp (-(c₂ / (6 * δ))) *
          Real.log (F γ N ^ (6 * δ)) := hbound
  exact combine_ii_a c₀ C (F γ N) M _ _ _ _ _ hc₀ hX.le hM1 hb' hmS hE2 hE3

/-- P0082 page 363 case ii a, the exact type of `Decomp559b.leaf_coprime_selected`,
CONDITIONAL ON the cited `BPLemma3Hyp` only, Lemma 3 of page 358 with `P₀` chosen after `θ`.
The singular series bound of page 362 case i is `Prep1121SingSeries.singSeriesLowerHyp_split`
and display 10 is `Task672.landauRealZeroHyp_proved672`. -/
theorem leaf_coprime_selected_of_lemma3 (hL3 : BPLemma3Hyp) :
    type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_coprime_selected :=
  leaf_coprime_selected_of_lemma3_hyps hL3 Prep1121SingSeries.singSeriesLowerHyp_split
    LeanLab.ExceptionalSet.Task672.landauRealZeroHyp_proved672

end LeanLab.ExceptionalSet.UpJ200.CaseIIaFromLemma3

#print axioms LeanLab.ExceptionalSet.UpJ200.CaseIIaFromLemma3.twistedSing_abs_le_coprime
#print axioms LeanLab.ExceptionalSet.UpJ200.CaseIIaFromLemma3.coprime_bound_of_lemma3
#print axioms LeanLab.ExceptionalSet.UpJ200.CaseIIaFromLemma3.leaf_coprime_selected_of_lemma3_hyps
#print axioms LeanLab.ExceptionalSet.UpJ200.CaseIIaFromLemma3.leaf_coprime_selected_of_lemma3
