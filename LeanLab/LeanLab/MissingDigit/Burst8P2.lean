import LeanLab.MissingDigit.Burst4Split

/-!
# Burst 8, second split of Kim, Theorem 1.1

Paper: P0057, J. Kim, "Goldbach's problem in short intervals for numbers with a missing digit",
arXiv 2412.19975v1. AI wrote this Lean code. Binary Goldbach is OPEN; Theorem 1.1 is a divisor
sum bound over a missing digit set, not progress on binary Goldbach.

The Burst 4 split `Burst4Split.kim_thm1_1_of_split` left three sorry leaves, `prop_2_2`,
`major_arcs_bound` and `prop_2_5`. This file splits each further along the paper's own proof.

* Proposition 2.2 is proved here from Proposition 2.1, cited as MSTT Theorem 1.1 (iii), and
  Lemma 1.7, cited, by the paper's display (2.2): the trivial bound and the counting of the
  missing digit set.
* Proposition 2.5 is proved here from Proposition 3.5, cited, and Lemma 1.7, by the paper's
  one line proof on page 9.
* The major arc bound is split into Proposition 2.4, cited, with its explicit main term, the
  Section 2.2 bound of that main term, cited, and the comparison of the error term
  `X^{5ε} H^{3ε}` with `|[X,X+H]^*|`, proved.

The new top level theorem is `kim_thm1_1_of_p2 : D4Bound (3 / 5) 7`.
-/

namespace LeanLab.MissingDigit.Burst8P2

open Finset Real MeasureTheory Filter
open LeanLab.MissingDigit LeanLab.MissingDigit.Burst4Split

attribute [local instance] Classical.propDecidable

/-! ### The exponent of Lemma 1.7 -/

/-- Kim's exponent `log((log g) + 1) / log(g - 1)` from Lemma 1.7, page 5, with natural
logarithms. -/
noncomputable def thetaG (g : ℕ) : ℝ := Real.log (Real.log g + 1) / Real.log ((g : ℝ) - 1)

/-- The counting exponent `ρ_g = (log(g-1)/log g) (1 - θ_g)`: by `card_starSet_pow`,
`|[X,X+H]^*|^{1-θ_g} ≥ (H/g)^{ρ_g}`. -/
noncomputable def rhoG (g : ℕ) : ℝ := Real.log ((g : ℝ) - 1) / Real.log g * (1 - thetaG g)

/-! ### Counting the missing digit set from below -/

/-- For `1 ≤ H < X = g^k`, the set `[X,X+H]^*` has at least `(g-1)^j` elements, where
`j = ⌊log_g ⌊H⌋⌋`. This is the count behind the size `|[X,X+H]^*| ≍ H^{log(g-1)/log g}` quoted
on page 1 and used on page 7. -/
theorem card_starSet_ge {g b k : ℕ} (hg : 2 ≤ g) (hb : 2 ≤ b) (hbg : b < g) {H : ℝ}
    (hH1 : 1 ≤ H) (hHX : H < ((g ^ k : ℕ) : ℝ)) :
    (g - 1) ^ (Nat.log g ⌊H⌋₊) ≤ (starSet g b (g ^ k) H).card := by
  set j := Nat.log g ⌊H⌋₊
  have hfl0 : ⌊H⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊H⌋₊ := Nat.le_floor (by simpa using hH1)
    omega
  have hj : g ^ j ≤ ⌊H⌋₊ := Nat.pow_log_le_self g hfl0
  have hflk : ⌊H⌋₊ < g ^ k := (Nat.floor_lt (by linarith)).2 hHX
  have hjk : j < k := (Nat.pow_lt_pow_iff_right (by omega)).1 (lt_of_le_of_lt hj hflk)
  rw [← card_starSet_pow hg hb hbg hjk]
  apply Finset.card_le_card
  apply starSet_mono_H
  have : ((g ^ j : ℕ) : ℝ) ≤ (⌊H⌋₊ : ℝ) := by exact_mod_cast hj
  exact le_trans this (Nat.floor_le (by linarith))

/-- `H < g^{j+1}` for `j = ⌊log_g ⌊H⌋⌋`. -/
theorem lt_pow_log_succ {g : ℕ} (hg : 2 ≤ g) {H : ℝ} (hH : 0 ≤ H) :
    H < (g : ℝ) ^ (Nat.log g ⌊H⌋₊ + 1) := by
  have h1 : ⌊H⌋₊ < g ^ (Nat.log g ⌊H⌋₊).succ := Nat.lt_pow_succ_log_self (by omega) _
  have h2 : ⌊H⌋₊ + 1 ≤ g ^ (Nat.log g ⌊H⌋₊ + 1) := h1
  have h3 : ((⌊H⌋₊ + 1 : ℕ) : ℝ) ≤ ((g ^ (Nat.log g ⌊H⌋₊ + 1) : ℕ) : ℝ) := by exact_mod_cast h2
  push_cast at h3
  linarith [Nat.lt_floor_add_one H]

/-- The lower bound in real exponents: if `(g-1)^j ≤ N` and `H < g^{j+1}` then
`H^{ρ} / g^{ρ} ≤ N^{1-θ}` with `ρ = (log(g-1)/log g)(1-θ)`. -/
theorem rpow_card_lower {g : ℕ} (hg : 3 ≤ g) {j : ℕ} {H N θ : ℝ} (hθ1 : θ ≤ 1)
    (hH : 1 ≤ H) (hHj : H < (g : ℝ) ^ (j + 1)) (hN : ((g : ℝ) - 1) ^ j ≤ N) :
    H ^ (Real.log ((g : ℝ) - 1) / Real.log g * (1 - θ)) /
        (g : ℝ) ^ (Real.log ((g : ℝ) - 1) / Real.log g * (1 - θ)) ≤ N ^ (1 - θ) := by
  have hg3 : (3 : ℝ) ≤ g := by exact_mod_cast hg
  have hgm : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  have hgp : (0 : ℝ) < g := by linarith
  have hL : 0 < Real.log g := Real.log_pos (by linarith)
  have hM : 0 ≤ Real.log ((g : ℝ) - 1) := Real.log_nonneg (by linarith)
  have hHp : 0 < H := by linarith
  have hu : 0 ≤ 1 - θ := by linarith
  set ρ := Real.log ((g : ℝ) - 1) / Real.log g * (1 - θ) with hρ
  have hpow : 0 < ((g : ℝ) - 1) ^ j := pow_pos hgm j
  calc H ^ ρ / (g : ℝ) ^ ρ ≤ (((g : ℝ) - 1) ^ j) ^ (1 - θ) := by
        rw [Real.rpow_def_of_pos hHp, Real.rpow_def_of_pos hgp, Real.rpow_def_of_pos hpow,
          ← Real.exp_sub, Real.log_pow]
        apply Real.exp_le_exp.2
        have hlogH : Real.log H < (j + 1) * Real.log g := by
          have := Real.log_lt_log hHp hHj
          rw [Real.log_pow] at this; push_cast at this; exact this
        have key : (Real.log H - Real.log g) / Real.log g ≤ j := by
          rw [div_le_iff₀ hL]; push_cast at hlogH; nlinarith
        have e : Real.log H * ρ - Real.log g * ρ =
            (Real.log H - Real.log g) / Real.log g * (Real.log ((g : ℝ) - 1) * (1 - θ)) := by
          rw [hρ]; field_simp
        rw [e]
        have hMu : 0 ≤ Real.log ((g : ℝ) - 1) * (1 - θ) := mul_nonneg hM hu
        calc (Real.log H - Real.log g) / Real.log g * (Real.log ((g : ℝ) - 1) * (1 - θ))
            ≤ (j : ℝ) * (Real.log ((g : ℝ) - 1) * (1 - θ)) :=
              mul_le_mul_of_nonneg_right key hMu
          _ = (j : ℝ) * Real.log ((g : ℝ) - 1) * (1 - θ) := by ring
    _ ≤ N ^ (1 - θ) := Real.rpow_le_rpow hpow.le hN hu

/-! ### Choice of `g₀`: `θ_g → 0` and `ρ_g → 1` -/

/-- For every `κ > 0` there is `g₀` with `0 ≤ θ_g ≤ 1/2`, `0 ≤ ρ_g ≤ 1` and `1 - ρ_g < κ` for
all `g ≥ g₀`. This is the meaning of "g sufficiently large depending on ε" in Proposition 2.2,
page 8, where `log((log g)+1)/log(g-1)` must be small against `cε`. -/
theorem exists_g0 {κ : ℝ} (hκ : 0 < κ) : ∃ g₀ : ℕ, 3 ≤ g₀ ∧ ∀ g : ℕ, g₀ ≤ g →
    0 ≤ thetaG g ∧ thetaG g ≤ 1 / 2 ∧ 0 ≤ rhoG g ∧ rhoG g ≤ 1 ∧ 1 - rhoG g < κ := by
  set κ' := min κ 1 with hκ'
  have hκ'p : 0 < κ' := lt_min hκ one_pos
  have ht := Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1
    ((ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < κ' / 2))))
  set E : ℝ := max (max T 3) (2 * Real.log 2 / κ + 1)
  have hce : 0 < ⌈Real.exp E⌉₊ := Nat.ceil_pos.2 (Real.exp_pos E)
  refine ⟨⌈Real.exp E⌉₊ + 2, by omega, fun g hg => ?_⟩
  have hgE : Real.exp E + 1 < (g : ℝ) - 1 + 1 := by
    have : (⌈Real.exp E⌉₊ + 2 : ℕ) ≤ (g : ℝ) := by exact_mod_cast hg
    push_cast at this
    linarith [Nat.le_ceil (Real.exp E)]
  have hg1 : Real.exp E < (g : ℝ) - 1 := by linarith
  have hgm : 0 < (g : ℝ) - 1 := lt_trans (Real.exp_pos E) hg1
  set t := Real.log ((g : ℝ) - 1) with htdef
  have htE : E < t := by rw [htdef, Real.lt_log_iff_exp_lt hgm]; exact hg1
  have ht3 : 3 < t := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) htE
  have htT : T ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) htE.le
  have htK : 2 * Real.log 2 / κ + 1 < t := lt_of_le_of_lt (le_max_right _ _) htE
  have hgp : (0 : ℝ) < g := by linarith
  set L := Real.log (g : ℝ) with hLdef
  have htL : t ≤ L := Real.log_le_log hgm (by linarith)
  have hLt : L ≤ t + Real.log 2 := by
    rw [htdef, ← Real.log_mul hgm.ne' (by norm_num)]
    have hE1 : 1 < Real.exp E := Real.one_lt_exp_iff.2
      (lt_of_lt_of_le (by norm_num) (le_trans (le_max_right T 3) (le_max_left _ _)))
    exact Real.log_le_log hgp (by linarith)
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; norm_num at this; linarith
  have hlog2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLp : 0 < L := by linarith
  -- θ bounds
  have hθ0 : 0 ≤ thetaG g := by
    unfold thetaG
    exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  have hθt : thetaG g ≤ Real.log (t + 2) / t := by
    unfold thetaG
    rw [← htdef, ← hLdef]
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact Real.log_le_log (by linarith) (by linarith)
  have hθκ : thetaG g < κ' / 2 := by
    have h := hT (t + 2) (by linarith)
    have e : Real.log (t + 2) ^ 1 / (1 * (t + 2) + -2) = Real.log (t + 2) / t := by
      rw [pow_one]; congr 1; ring
    rw [e] at h
    linarith
  have hθhalf : thetaG g ≤ 1 / 2 := by
    have : κ' ≤ 1 := min_le_right _ _
    linarith
  have hθκ2 : thetaG g < κ / 2 := by
    have : κ' ≤ κ := min_le_left _ _
    linarith
  -- a = t / L
  have ha0 : 0 ≤ t / L := div_nonneg (by linarith) hLp.le
  have ha1 : t / L ≤ 1 := (div_le_one hLp).2 htL
  have h1a : 1 - t / L < κ / 2 := by
    have e : 1 - t / L = (L - t) / L := by field_simp
    rw [e, div_lt_iff₀ hLp]
    have h2 : 2 * Real.log 2 / κ < L := by linarith
    rw [div_lt_iff₀ hκ] at h2
    nlinarith
  have hρ : rhoG g = t / L * (1 - thetaG g) := rfl
  refine ⟨hθ0, hθhalf, ?_, ?_, ?_⟩
  · rw [hρ]; exact mul_nonneg ha0 (by linarith)
  · rw [hρ]
    calc t / L * (1 - thetaG g) ≤ 1 * 1 :=
          mul_le_mul ha1 (by linarith) (by linarith) (by norm_num)
      _ = 1 := by norm_num
  · rw [hρ]
    have : t / L * thetaG g ≤ thetaG g := by
      calc t / L * thetaG g ≤ 1 * thetaG g := mul_le_mul_of_nonneg_right ha1 hθ0
        _ = thetaG g := one_mul _
    nlinarith

/-! ### The final comparison in Propositions 2.2 and 2.5 -/

/-- The last step of the proofs of Proposition 2.2, page 8, and Proposition 2.5, page 9:
for `g` large in terms of `cε`, any bound of the shape `A H X^{-cε} |[X,X+H]^*|^{θ_g}` is
`o(|[X,X+H]^*|)` for `1 ≤ H < X = g^k`. Here `θ_g = log((log g)+1)/log(g-1)` is the exponent of
Lemma 1.7. -/
theorem tail_small {cε : ℝ} (hcε : 0 < cε) : ∃ g₀ : ℕ, 3 ≤ g₀ ∧ ∀ g b : ℕ, g₀ ≤ g → 2 ≤ b →
    b ≤ g - 1 → ∀ A η : ℝ, 0 < η → ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k → 1 ≤ H →
      H < ((g ^ k : ℕ) : ℝ) →
      A * H * ((g ^ k : ℕ) : ℝ) ^ (-cε) * ((starSet g b (g ^ k) H).card : ℝ) ^ thetaG g ≤
        η * (starSet g b (g ^ k) H).card := by
  obtain ⟨g₀, hg₀3, hg₀⟩ := exists_g0 hcε
  refine ⟨g₀, hg₀3, fun g b hg hb2 hbg A η hη => ?_⟩
  obtain ⟨hθ0, hθh, hρ0, hρ1, hρκ⟩ := hg₀ g hg
  have hg3 : 3 ≤ g := le_trans hg₀3 hg
  have hgR : (3 : ℝ) ≤ g := by exact_mod_cast hg3
  set θ := thetaG g
  set ρ := rhoG g with hρdef
  set κ := cε - (1 - ρ) with hκ
  have hκp : 0 < κ := by rw [hκ]; linarith
  set A' := max A 0
  have hX : Tendsto (fun k : ℕ => ((g ^ k : ℕ) : ℝ)) atTop atTop := by
    have : Tendsto (fun k : ℕ => (g : ℝ) ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by linarith)
    simpa using this
  obtain ⟨K₀, hK₀⟩ := Filter.eventually_atTop.1
    (((tendsto_rpow_atTop hκp).comp hX).eventually_ge_atTop (A' * (g : ℝ) ^ ρ / η))
  refine ⟨K₀, fun k H hk hH1 hHX => ?_⟩
  set X : ℝ := ((g ^ k : ℕ) : ℝ) with hXdef
  set N : ℝ := ((starSet g b (g ^ k) H).card : ℝ) with hNdef
  have hXκ : A' * (g : ℝ) ^ ρ / η ≤ X ^ κ := hK₀ k hk
  have hXp : 0 < X := by linarith
  have hHp : 0 < H := by linarith
  have hgp : (0 : ℝ) < g := by linarith
  -- counting
  have hcard := card_starSet_ge (by omega) hb2 (by omega) hH1 hHX
  set j := Nat.log g ⌊H⌋₊
  have hNj : ((g : ℝ) - 1) ^ j ≤ N := by
    have : (((g - 1) ^ j : ℕ) : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hcard
    push_cast [show 1 ≤ g by omega] at this; exact this
  have hN1 : 1 ≤ N := le_trans (one_le_pow₀ (by linarith)) hNj
  have hNp : 0 < N := by linarith
  have hlow := rpow_card_lower hg3 (θ := θ) (by linarith) hH1
    (lt_pow_log_succ (by omega) hHp.le) hNj
  have hρeq : Real.log ((g : ℝ) - 1) / Real.log g * (1 - θ) = ρ := rfl
  rw [hρeq] at hlow
  -- reduce to `A' H X^{-cε} ≤ η N^{1-θ}`
  have hsplitN : N = N ^ θ * N ^ (1 - θ) := by
    rw [← Real.rpow_add hNp, add_sub_cancel, Real.rpow_one]
  have hNθ : 0 ≤ N ^ θ := (Real.rpow_pos_of_pos hNp _).le
  have hgρ : 0 < (g : ℝ) ^ ρ := Real.rpow_pos_of_pos hgp _
  have hHρ : 0 < H ^ ρ := Real.rpow_pos_of_pos hHp _
  have hXcε : 0 < X ^ (-cε) := Real.rpow_pos_of_pos hXp _
  have hcore : A' * H * X ^ (-cε) ≤ η * N ^ (1 - θ) := by
    have hH1ρ : H ^ (1 - ρ) ≤ X ^ (1 - ρ) :=
      Real.rpow_le_rpow hHp.le hHX.le (by linarith)
    have hHsplit : H = H ^ ρ * H ^ (1 - ρ) := by
      rw [← Real.rpow_add hHp, add_sub_cancel, Real.rpow_one]
    have hXsplit : X ^ (1 - ρ) * X ^ (-cε) = (X ^ κ)⁻¹ := by
      rw [← Real.rpow_add hXp, ← Real.rpow_neg hXp.le, hκ]; congr 1; ring
    have hA' : 0 ≤ A' := le_max_right _ _
    have hXκp : 0 < X ^ κ := Real.rpow_pos_of_pos hXp _
    have step1 : A' * H * X ^ (-cε) ≤ A' * H ^ ρ * (X ^ κ)⁻¹ := by
      rw [← hXsplit]
      conv_lhs => rw [hHsplit]
      have : 0 ≤ A' * H ^ ρ := mul_nonneg hA' hHρ.le
      calc A' * (H ^ ρ * H ^ (1 - ρ)) * X ^ (-cε)
          = (A' * H ^ ρ) * (H ^ (1 - ρ) * X ^ (-cε)) := by ring
        _ ≤ (A' * H ^ ρ) * (X ^ (1 - ρ) * X ^ (-cε)) := by
          apply mul_le_mul_of_nonneg_left _ this
          exact mul_le_mul_of_nonneg_right hH1ρ hXcε.le
        _ = A' * H ^ ρ * (X ^ (1 - ρ) * X ^ (-cε)) := by ring
    have step2 : A' * H ^ ρ * (X ^ κ)⁻¹ ≤ η * (H ^ ρ / (g : ℝ) ^ ρ) := by
      rw [div_le_iff₀ hη] at hXκ
      rw [mul_inv_le_iff₀ hXκp]
      have e : η * (H ^ ρ / (g : ℝ) ^ ρ) * X ^ κ = H ^ ρ * (X ^ κ * η) / (g : ℝ) ^ ρ := by
        ring
      rw [e, le_div_iff₀ hgρ]
      nlinarith
    calc A' * H * X ^ (-cε) ≤ η * (H ^ ρ / (g : ℝ) ^ ρ) := le_trans step1 step2
      _ ≤ η * N ^ (1 - θ) := mul_le_mul_of_nonneg_left hlow hη.le
  have hAA : A * H * X ^ (-cε) * N ^ θ ≤ A' * H * X ^ (-cε) * N ^ θ := by
    have : 0 ≤ H * X ^ (-cε) * N ^ θ := mul_nonneg (mul_nonneg hHp.le hXcε.le) hNθ
    nlinarith [le_max_left A 0]
  calc A * H * X ^ (-cε) * N ^ θ ≤ A' * H * X ^ (-cε) * N ^ θ := hAA
    _ ≤ η * N ^ (1 - θ) * N ^ θ := mul_le_mul_of_nonneg_right hcore hNθ
    _ = η * N := by conv_rhs => rw [hsplitN]
                    ring

/-! ### The trivial bound of display (2.2) -/

theorem eC_neg (x : ℝ) : eC (-x) = starRingEnd ℂ (eC x) := by
  unfold eC
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast; ring

theorem norm_sum_eC_neg (S : Finset ℕ) (α : ℝ) :
    ‖∑ n ∈ S, eC (-(n * α))‖ = ‖∑ n ∈ S, eC (n * α)‖ := by
  simp_rw [eC_neg]
  rw [← map_sum, Complex.norm_conj]

theorem periodic_norm_sum_eC (S : Finset ℕ) :
    Function.Periodic (fun α : ℝ => ‖∑ n ∈ S, eC (n * α)‖) 1 := by
  intro α
  have hm : ∀ m : ℕ, eC (m * (α + 1)) = eC (m * α) := by
    intro m
    rw [mul_add, mul_one, eC_add]
    have := eC_int m; push_cast at this; rw [this, mul_one]
  simp only [hm]

/-- The trivial bound in display (2.2), page 8, and in the proof of Proposition 2.5, page 9:
`|∑_{n ∈ S} ∫_A F(α) e(-nα) dα| ≤ sup_A |F| ∫_A |∑_{n ∈ S} e(-nα)| dα`. -/
theorem norm_sum_setIntegral_le {A : Set ℝ} {a b : ℝ} (hA : MeasurableSet A)
    (hAs : A ⊆ Set.Icc a b) (F : ℝ → ℂ) (hF : Continuous F) (S : Finset ℕ) {M : ℝ}
    (hM : ∀ α ∈ A, ‖F α‖ ≤ M) :
    ‖∑ n ∈ S, ∫ α in A, F α * eC (-(n * α))‖ ≤
      M * ∫ α in A, ‖∑ n ∈ S, eC (-(n * α))‖ := by
  have hce := continuous_eC
  have hint : ∀ f : ℝ → ℂ, Continuous f → IntegrableOn f A :=
    fun f hf => (hf.integrableOn_Icc).mono_set hAs
  have hintR : ∀ f : ℝ → ℝ, Continuous f → IntegrableOn f A :=
    fun f hf => (hf.integrableOn_Icc).mono_set hAs
  rw [← integral_finset_sum S (fun n _ => hint _ (by fun_prop))]
  simp_rw [← Finset.mul_sum]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  rw [← integral_const_mul]
  apply setIntegral_mono_on (hintR _ (by fun_prop)) (hintR _ (by fun_prop)) hA
  intro α hα
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hM α hα) (norm_nonneg _)

/-- `∫_{(0,1]} |∑ e(-nα)| = ∫_0^1 |∑ e(nα)|`. -/
theorem setIntegral_Ioc01_norm (S : Finset ℕ) :
    ∫ α in Set.Ioc (0 : ℝ) 1, ‖∑ n ∈ S, eC (-(n * α))‖ =
      ∫ α in (0 : ℝ)..1, ‖∑ n ∈ S, eC (n * α)‖ := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  simp_rw [norm_sum_eC_neg]

/-- `∫_{(1/Q, 1+1/Q]} |∑ e(-nα)| = ∫_0^1 |∑ e(nα)|`, by periodicity. -/
theorem setIntegral_arcRange_norm (ε : ℝ) (X : ℕ) (S : Finset ℕ) :
    ∫ α in arcRange ε X, ‖∑ n ∈ S, eC (-(n * α))‖ =
      ∫ α in (0 : ℝ)..1, ‖∑ n ∈ S, eC (n * α)‖ := by
  unfold arcRange
  simp_rw [norm_sum_eC_neg]
  have h := (periodic_norm_sum_eC S).intervalIntegral_add_eq (1 / Qpar ε X) 0
  rw [zero_add] at h
  rw [← h, intervalIntegral.integral_of_le (by linarith), add_comm (1 / Qpar ε X) 1]

/-! ### Cited inputs -/

/-- LEAF: Kim, Proposition 2.1, page 7, which is MSTT, Higher uniformity of
arithmetic functions in short intervals I, Forum Math. Pi 11 (2023), Theorem 1.1 (iii):
for `X^{3/5+ε} ≤ H ≤ X^{1-ε}`,
`sup_α |∑_{X ≤ n ≤ X+H} (d₄(n) - d♯₄(n)) e(nα)| ≪ H X^{-cε}` for some `c > 0`.
Encoded with `ε` below some `ε₀`, as Section 1.1 assumes `ε` small, with `c` allowed to depend
on `ε`, and with the implied constant `C` and the threshold `X₀` explicit. -/
theorem prop_2_1 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ c : ℝ, 0 < c ∧
    ∃ C : ℝ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ H : ℝ,
      (X : ℝ) ^ ((3 : ℝ) / 5 + ε) ≤ H → H ≤ (X : ℝ) ^ (1 - ε) → ∀ α : ℝ,
        ‖S4 X H α - S4sharp ε X H α‖ ≤ C * H * (X : ℝ) ^ (-(c * ε)) := by
  sorry

private theorem norm_eC_w (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  have : 2 * (π : ℂ) * Complex.I * (x : ℂ) = ((2 * π * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

private theorem eC_nat_mul_w (d : ℕ) (θ : ℝ) : eC (d * θ) = eC θ ^ d := by
  induction d with
  | zero => simp [eC]
  | succ d ih => rw [pow_succ, ← ih, ← eC_add]; congr 1; push_cast; ring

private theorem norm_eC_sub_one_w (θ : ℝ) : ‖eC θ - 1‖ = 2 * |Real.sin (π * θ)| := by
  have : eC θ = Complex.exp (Complex.I * ((2 * π * θ : ℝ) : ℂ)) := by
    unfold eC; congr 1; push_cast; ring
  rw [this, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
    Real.norm_eq_abs]
  norm_num
  congr 2; ring

private theorem Gsum_w_le (g : ℕ) (θ : ℝ) : ‖∑ d ∈ range g, eC (d * θ)‖ ≤ g := by
  refine le_trans (norm_sum_le _ _) ?_
  simp [norm_eC_w]

/-- The exact size of the geometric sum: `|G_g(θ)| sin(πθ) = |sin(π g θ)|`, valid at `θ = 0`
where both sides vanish. -/
private theorem Gsum_w_mul_sin {g : ℕ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) :
    ‖∑ d ∈ range g, eC (d * θ)‖ * Real.sin (π * θ) = |Real.sin (π * (g : ℝ) * θ)| := by
  rcases h0.eq_or_lt with rfl | h0'
  · have hsum : (∑ d ∈ range g, eC (d * (0 : ℝ))) = (g : ℂ) := by
      simp [eC]
    rw [hsum]
    simp
  · have hs : 0 < Real.sin (π * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
    have hne : eC θ - 1 ≠ 0 := by
      intro h
      have := norm_eC_sub_one_w θ
      rw [h, norm_zero, abs_of_pos hs] at this
      linarith
    have hz : eC θ ≠ 1 := fun h => hne (by rw [h, sub_self])
    have hsum : (∑ d ∈ range g, eC (d * θ)) = ∑ d ∈ range g, eC θ ^ d :=
      Finset.sum_congr rfl (fun d _ => eC_nat_mul_w d θ)
    rw [hsum, geom_sum_eq hz, norm_div]
    have hnum : ‖eC θ ^ g - 1‖ = 2 * |Real.sin (π * ((g : ℝ) * θ))| := by
      rw [← eC_nat_mul_w g θ, norm_eC_sub_one_w]
    have hden : ‖eC θ - 1‖ = 2 * |Real.sin (π * θ)| := norm_eC_sub_one_w θ
    rw [hnum, hden, abs_of_pos hs, show π * ((g : ℝ) * θ) = π * (g : ℝ) * θ by ring]
    have h2 : (2 * Real.sin (π * θ)) ≠ 0 := by positivity
    field_simp

/-! ### The quadratic lower bound for `sin` and the sine reciprocal -/

private theorem sin_pi_ge_quad_half {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    π * x * (1 - x) ≤ Real.sin (π * x) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  set y := π * x with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ π / 2 := by rw [hy]; nlinarith
  have hcube : y - y ^ 3 / 6 ≤ Real.sin y := Real.sin_ge_sub_cube hy0
  have hp2 : π ^ 2 ≤ 12 := by nlinarith [Real.pi_lt_d4, hpi]
  have hy6 : y * π ≤ 6 := by nlinarith [hy1, hpi, hp2]
  have hkey : y ^ 3 / 6 ≤ y ^ 2 / π := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 6) hpi]
    have h1 : y ^ 2 * (y * π) ≤ y ^ 2 * 6 := mul_le_mul_of_nonneg_left hy6 (by positivity)
    nlinarith [h1]
  have e : π * x * (1 - x) = y - y ^ 2 / π := by
    rw [hy]
    field_simp
  rw [e]
  linarith [hkey]

private theorem sin_pi_ge_quad {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    π * x * (1 - x) ≤ Real.sin (π * x) := by
  rcases le_or_gt x (1 / 2) with hx | hx
  · exact sin_pi_ge_quad_half h0 hx
  · have h1x0 : 0 ≤ 1 - x := by linarith
    have h1x1 : 1 - x ≤ 1 / 2 := by linarith
    have h := sin_pi_ge_quad_half h1x0 h1x1
    have e : Real.sin (π * (1 - x)) = Real.sin (π * x) := by
      rw [show π * (1 - x) = π - π * x by ring, Real.sin_pi_sub]
    rw [e] at h
    nlinarith

private theorem inv_sin_pi_le_quad {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    1 / Real.sin (π * x) ≤ 1 / (π * x * (1 - x)) := by
  have hs : 0 < π * x * (1 - x) :=
    mul_pos (mul_pos Real.pi_pos h0) (by linarith)
  exact one_div_le_one_div_of_le hs (sin_pi_ge_quad h0.le h1.le)

/-! ### The harmonic bounds -/

private theorem sum_inv_range_w (g : ℕ) : ∑ c ∈ range g, (1 : ℝ) / c ≤ 1 + Real.log g := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · simp
  obtain ⟨n, rfl⟩ : ∃ n, g = n + 1 := ⟨g - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have e : ∑ i ∈ range n, (1 : ℝ) / ((i + 1 : ℕ) : ℝ) = ((harmonic n : ℚ) : ℝ) := by
    unfold harmonic; push_cast; simp [one_div]
  simp only [Nat.cast_zero, div_zero, add_zero]
  rw [e]
  refine le_trans (harmonic_le_one_add_log n) ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have : Real.log n ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hn) (by push_cast; linarith)
  linarith

private theorem sum_inv_shift_w {g : ℕ} {β : ℝ} (hβ : 0 ≤ β) :
    ∑ c ∈ range g, (1 : ℝ) / (β + c) ≤ 1 / β + 1 + Real.log g := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · rw [Finset.range_zero, Finset.sum_empty]
    have h0 : Real.log (((0 : ℕ)) : ℝ) = 0 := by simp
    rw [h0]
    have : 0 ≤ (1 : ℝ) / β := by positivity
    linarith
  obtain ⟨n, rfl⟩ : ∃ n, g = n + 1 := ⟨g - 1, by omega⟩
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, add_zero]
  have hfirst : ∑ i ∈ range n, (1 : ℝ) / (β + ((i + 1 : ℕ) : ℝ)) + 1 / β ≤
      (∑ i ∈ range n, (1 : ℝ) / ((i + 1 : ℕ) : ℝ)) + 1 / β := by
    have hle : ∑ i ∈ range n, (1 : ℝ) / (β + ((i + 1 : ℕ) : ℝ)) ≤
        ∑ i ∈ range n, (1 : ℝ) / ((i + 1 : ℕ) : ℝ) := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      have hi : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
      apply one_div_le_one_div_of_le hi
      push_cast
      linarith
    linarith
  have hsecond : ∑ i ∈ range n, (1 : ℝ) / ((i + 1 : ℕ) : ℝ) ≤ 1 + Real.log ((n : ℝ) + 1) := by
    have e : ∑ i ∈ range n, (1 : ℝ) / ((i + 1 : ℕ) : ℝ) = ((harmonic n : ℚ) : ℝ) := by
      unfold harmonic; push_cast; simp [one_div]
    rw [e]
    refine le_trans (harmonic_le_one_add_log n) ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have h : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := by
      apply Real.log_le_log (by exact_mod_cast hn) (by linarith)
    linarith
  have hcast : Real.log (((n + 1 : ℕ) : ℝ)) = Real.log ((n : ℝ) + 1) := by
    push_cast; ring_nf
  rw [hcast]
  linarith

/-- The reflected form: `∑_{c<g} 1/(g - β - c) ≤ 1/(1-β) + 1 + log g`. -/
private theorem sum_inv_sub_shift_w {g : ℕ} {β : ℝ} (hβ : β ≤ 1) :
    ∑ c ∈ range g, (1 : ℝ) / ((g : ℝ) - β - c) ≤ 1 / (1 - β) + 1 + Real.log g := by
  rcases Nat.eq_zero_or_pos g with rfl | hg0
  · rw [Finset.range_zero, Finset.sum_empty]
    have h0 : Real.log (((0 : ℕ)) : ℝ) = 0 := by simp
    rw [h0]
    have : 0 ≤ (1 : ℝ) / (1 - β) := by positivity
    linarith
  have hrefl : ∑ c ∈ range g, (1 : ℝ) / ((g : ℝ) - β - c) =
      ∑ c ∈ range g, (1 : ℝ) / (1 - β + c) := by
    conv_lhs => rw [← Finset.sum_range_reflect (fun c => (1 : ℝ) / ((g : ℝ) - β - c)) g]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    have hc' : c ≤ g - 1 := by
      have h := Finset.mem_range.1 hc
      omega
    have hcast : ((g - 1 - c : ℕ) : ℝ) = (g : ℝ) - 1 - (c : ℝ) := by
      have h1 : ((g - 1 - c : ℕ) : ℝ) = ((g - 1 : ℕ) : ℝ) - (c : ℝ) := by
        rw [Nat.cast_sub hc']
      have h2 : ((g - 1 : ℕ) : ℝ) = (g : ℝ) - 1 := by
        rw [Nat.cast_sub hg0]
        push_cast
        ring
      rw [h1, h2]
    rw [hcast]
    congr 1
    ring
  rw [hrefl]
  exact sum_inv_shift_w (by linarith)

/-! ### The exact size of the geometric sum at the shifted points -/

private theorem abs_sin_pi_add_cast {β : ℝ} {c : ℕ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    |Real.sin (π * (β + c))| = Real.sin (π * β) := by
  induction c with
  | zero =>
    rw [Nat.cast_zero, add_zero]
    exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
      (by nlinarith [Real.pi_pos]))
  | succ c ih =>
    rw [show π * (β + ((c + 1 : ℕ) : ℝ)) = π * (β + c) + π by push_cast; ring]
    rw [Real.sin_add_pi, abs_neg, ih]

/-- `‖G_g((β+c)/g)‖ = sin(πβ)/sin(π(β+c)/g)`, for `0 < β + c` (so that the point is not `0`)
and `β + c < g`. -/
private theorem Gsum_w_shift {g c : ℕ} {β : ℝ} (hg : 0 < g) (hc : c < g)
    (hβc : 0 < (β : ℝ) + c) (hβg : (β : ℝ) + c < (g : ℝ)) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ‖∑ d ∈ range g, eC (d * ((β + c) / g))‖ =
      Real.sin (π * β) / Real.sin (π * ((β + c) / g)) := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hθ0 : 0 ≤ (β + c) / g := by positivity
  have hθ1 : (β + c) / g < 1 := by
    rw [div_lt_one hgR]
    linarith
  have hmul := Gsum_w_mul_sin (g := g) (θ := (β + c) / g) hθ0 hθ1
  rw [show π * (g : ℝ) * ((β + c) / (g : ℝ)) = π * (β + (c : ℝ)) by
    field_simp] at hmul
  rw [show π * (β + (c : ℝ)) = π * (β + c) by push_cast; ring] at hmul
  rw [abs_sin_pi_add_cast hβ0 hβ1] at hmul
  have hs : 0 < Real.sin (π * ((β + c) / g)) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  exact (eq_div_iff hs.ne').mpr hmul

/-- The sharp per-`c` bound on the geometric sum at a point `(β+c)/g` of `(0,1)`. -/
private theorem Gsum_w_shift_bound {g c : ℕ} {β : ℝ} (hg : 0 < g) (hcg : c < g)
    (hβc : 0 < (β : ℝ) + c) (hβg : (β : ℝ) + c < (g : ℝ)) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ‖∑ d ∈ range g, eC (d * ((β + c) / g))‖ ≤
      (Real.sin (π * β) / π) * ((g : ℝ) * ((1 : ℝ) / (β + c) + 1 / ((g : ℝ) - β - c))) := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hu : 0 < (β : ℝ) + c := hβc
  have hv : 0 < (g : ℝ) - β - c := by linarith
  have hx0 : 0 < ((β : ℝ) + c) / g := div_pos hu hgR
  have hx1 : ((β : ℝ) + c) / g < 1 := by
    rw [div_lt_one hgR]
    linarith
  have hEq := Gsum_w_shift hg hcg hβc hβg hβ0 hβ1
  have hs0 : 0 ≤ Real.sin (π * β) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hinv : 1 / Real.sin (π * ((β + c) / g)) ≤
      1 / (π * ((β + c) / g) * (1 - (β + c) / g)) :=
    inv_sin_pi_le_quad hx0 hx1
  have hinv' : (Real.sin (π * ((β + c) / g)))⁻¹ ≤
      (π * ((β + c) / g) * (1 - (β + c) / g))⁻¹ := by
    simpa [one_div] using hinv
  have hxv2 : ((β + (c : ℝ)) / g) * (1 - (β + (c : ℝ)) / g) =
      ((β + c) * ((g : ℝ) - β - c)) / (g : ℝ) ^ 2 := by
    have hg' : (g : ℝ) ≠ 0 := ne_of_gt hgR
    field_simp
    ring
  have hx2 : 1 / (π * ((β + (c : ℝ)) / g) * (1 - (β + (c : ℝ)) / g)) =
      (g : ℝ) ^ 2 / (π * ((β + c) * ((g : ℝ) - β - c))) := by
    have hA : π * ((β + (c : ℝ)) / g) * (1 - (β + (c : ℝ)) / g) =
        π * (((β + (c : ℝ)) / g) * (1 - (β + (c : ℝ)) / g)) := by ring
    rw [hA, hxv2]
    have hu' : (β + (c : ℝ)) ≠ 0 := ne_of_gt hu
    have hv' : ((g : ℝ) - β - c) ≠ 0 := ne_of_gt hv
    have hg' : (g : ℝ) ≠ 0 := ne_of_gt hgR
    have hp' : (π : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
    field_simp
    try ring
  have hx3 : (g : ℝ) ^ 2 / (π * ((β + c) * ((g : ℝ) - β - c))) =
      (g : ℝ) * ((1 : ℝ) / (β + c) + 1 / ((g : ℝ) - β - c)) / π := by
    have hu' : (β + (c : ℝ)) ≠ 0 := ne_of_gt hu
    have hv' : ((g : ℝ) - β - c) ≠ 0 := ne_of_gt hv
    have hp' : (π : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
    field_simp
    try ring
  have hident : (π * ((β + c) / g) * (1 - (β + c) / g))⁻¹ =
      (g : ℝ) * ((1 : ℝ) / (β + c) + 1 / ((g : ℝ) - β - c)) / π := by
    rw [inv_eq_one_div]
    exact hx2.trans hx3
  rw [hEq, div_eq_mul_inv]
  calc Real.sin (π * β) * (Real.sin (π * ((β + c) / g)))⁻¹
      ≤ Real.sin (π * β) * (π * ((β + c) / g) * (1 - (β + c) / g))⁻¹ :=
        mul_le_mul_of_nonneg_left hinv' hs0
    _ = (Real.sin (π * β) / π) * ((g : ℝ) * ((1 : ℝ) / (β + c) + 1 / ((g : ℝ) - β - c))) := by
        rw [hident]
        ring

/-! ### The sharp digit average -/

/-- The digit average with the sharp constant `log g + 1`: for `β ∈ [0,1]`,
`∑_{c<g} |f_{g,b}((β+c)/g)| ≤ g (log g + 1)`. This is the `+1` of Kim's Lemma 1.7; the version
in `Burst8L17` has `log g + 4`. The two endpoint indices `c = 0` and `c = g-1` are bounded
crudely, since at `β = 0, 1` the corresponding point is `0, 1`. -/
private theorem digit_avg_le {g b : ℕ} (hg : 33554432 ≤ g) (hbg : b < g) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ∑ c ∈ range g, ‖∑ d ∈ (range g).filter (fun d => d ≠ b), eC (d * ((β + c) / g))‖ ≤
      (g : ℝ) * (Real.log g + 1) := by
  have hg1 : 1 ≤ g := by omega
  have hg2 : 2 ≤ g := by omega
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg1
  have hlog : 17 ≤ Real.log g := by
    have h1 : Real.log (33554432 : ℝ) = 25 * Real.log 2 := by
      rw [show (33554432 : ℝ) = 2 ^ 25 by norm_num, Real.log_pow]
      push_cast
      ring
    have h2 : Real.log (33554432 : ℝ) ≤ Real.log g :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hg)
    have h3 : 0.693 < Real.log 2 := by linarith [Real.log_two_gt_d9]
    linarith
  have hstep : ∀ c ∈ range g,
      ‖∑ d ∈ (range g).filter (fun d => d ≠ b), eC (d * ((β + c) / g))‖ ≤
        ‖∑ d ∈ range g, eC (d * ((β + c) / g))‖ + 1 := by
    intro c _
    have hsplit : (∑ d ∈ (range g).filter (fun d => d ≠ b), eC (d * ((β + c) / g)))
        = (∑ d ∈ range g, eC (d * ((β + c) / g))) - eC (b * ((β + c) / g)) := by
      rw [Finset.filter_ne', Finset.sum_erase_eq_sub (Finset.mem_range.2 hbg)]
    rw [hsplit]
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_eC_w]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  -- the geometric-sum part, with the two endpoints bounded crudely
  set S : ℝ := Real.sin (π * β) / π with hS
  have hs0 : 0 ≤ Real.sin (π * β) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hS0 : 0 ≤ S := div_nonneg hs0 Real.pi_pos.le
  have hg0 : (0 : ℝ) ≤ (g : ℝ) := by positivity
  set Mid := ((range g).erase 0).erase (g - 1) with hMid
  have hMem : ∀ c ∈ Mid, c ∈ range g := fun c hc =>
    Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc)
  have hmid_le : ∑ c ∈ Mid, ‖∑ d ∈ range g, eC (d * ((β + c) / g))‖ ≤
      ∑ c ∈ Mid, (S * g) * ((1 : ℝ) / (β + c) + 1 / ((g : ℝ) - β - c)) := by
    refine Finset.sum_le_sum (fun c hc => ?_)
    have hcr : c ∈ range g := hMem c hc
    have hc0 : c ≠ 0 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc)
    have hcl : c ≠ g - 1 := Finset.ne_of_mem_erase hc
    have hcg : c < g := Finset.mem_range.1 hcr
    have hcpos : 0 < (c : ℝ) := by
      have : 0 < c := Nat.pos_of_ne_zero hc0
      exact_mod_cast this
    have hclt : c < g - 1 := by
      rcases lt_or_gt_of_ne hcl with h | h
      · exact h
      · omega
    have hβc : 0 < (β : ℝ) + c := by linarith
    have hβg : (β : ℝ) + c < (g : ℝ) := by
      have hc2 : (c : ℝ) + 2 ≤ (g : ℝ) := by exact_mod_cast (show c + 2 ≤ g by omega)
      linarith
    have h1 := Gsum_w_shift_bound (g := g) (c := c) (β := β) (by omega) hcg hβc hβg hβ0 hβ1
    rw [hS]
    calc ‖∑ d ∈ range g, eC (d * ((β + c) / g))‖
        ≤ (Real.sin (π * β) / π) * ((g : ℝ) * ((1 : ℝ) / (β + c) + 1 / ((g : ℝ) - β - c))) := h1
      _ = (Real.sin (π * β) / π * g) * ((1 : ℝ) / (β + c) + 1 / ((g : ℝ) - β - c)) := by ring
  have hsub : ∑ c ∈ Mid, (S * g) * ((1 : ℝ) / (β + c) + 1 / ((g : ℝ) - β - c)) ≤
      ∑ c ∈ range g, (S * g) * ((1 : ℝ) / (β + c) + 1 / ((g : ℝ) - β - c)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (by intro c hc; exact hMem c hc) ?_
    intro c hc _
    have hcg : c < g := Finset.mem_range.1 hc
    have hcR1 : (c : ℝ) + 1 ≤ (g : ℝ) := by exact_mod_cast (show c + 1 ≤ g by omega)
    have h1 : (0 : ℝ) ≤ (1 : ℝ) / (β + c) := div_nonneg zero_le_one (by positivity)
    have h2 : (0 : ℝ) ≤ 1 / ((g : ℝ) - β - c) :=
      div_nonneg zero_le_one (by linarith)
    exact mul_nonneg (mul_nonneg hS0 hg0) (by linarith)
  -- split the total sum into the two endpoints and the middle
  have hmem0 : (0 : ℕ) ∈ range g := Finset.mem_range.2 (by omega)
  have hmeml : g - 1 ∈ range g := Finset.mem_range.2 (by omega)
  have htotal : ∑ c ∈ range g, ‖∑ d ∈ range g, eC (d * ((β + c) / g))‖ ≤
      2 * g + ∑ c ∈ range g, (S * g) * ((1 : ℝ) / (β + c) + 1 / ((g : ℝ) - β - c)) := by
    have hcrude : ∀ c : ℕ, ‖∑ d ∈ range g, eC (d * ((β + c) / g))‖ ≤ g :=
      fun c => Gsum_w_le g _
    have hpair : ({0, g - 1} : Finset ℕ) ⊆ range g := by
      intro c hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact Finset.mem_range.2 (by omega)
      · exact Finset.mem_range.2 (by omega)
    have hgl : ((g - 1 : ℕ) : ℝ) = (g : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ g)]
      push_cast
      ring
    have hMidEq : (range g) \ ({0, g - 1} : Finset ℕ) = Mid := by
      ext c
      simp only [hMid, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_range, Finset.mem_insert,
        Finset.mem_singleton]
      tauto
    have hsd := Finset.sum_sdiff (s₁ := ({0, g - 1} : Finset ℕ)) (s₂ := range g) hpair
      (f := fun c => ‖∑ d ∈ range g, eC (d * ((β + c) / g))‖)
    rw [hMidEq] at hsd
    have hpairsum : ∑ x ∈ ({0, g - 1} : Finset ℕ),
        ‖∑ d ∈ range g, eC (d * ((β + x) / g))‖ =
        ‖∑ d ∈ range g, eC (d * ((β + 0) / g))‖ +
          ‖∑ d ∈ range g, eC (d * ((β + (g - 1)) / g))‖ := by
      have h0mem : (0 : ℕ) ∉ ({g - 1} : Finset ℕ) := by
        simp only [Finset.mem_singleton]
        intro h
        omega
      rw [Finset.sum_insert h0mem, Finset.sum_singleton]
      simp only [Nat.cast_zero, add_zero, hgl]
    rw [hpairsum] at hsd
    have hb0 : ‖∑ d ∈ range g, eC (d * ((β + 0) / g))‖ ≤ (g : ℝ) := by
      have h := hcrude 0
      simpa using h
    have hbl : ‖∑ d ∈ range g, eC (d * ((β + ((g : ℝ) - 1)) / g))‖ ≤ (g : ℝ) := by
      have h := hcrude (g - 1)
      rw [hgl] at h
      exact h
    linarith [hsd, hb0, hbl, hsub]
  -- evaluate the sharp sum
  have h1 : ∑ c ∈ range g, (1 : ℝ) / (β + c) ≤ 1 / β + 1 + Real.log g := sum_inv_shift_w hβ0
  have h2 : ∑ c ∈ range g, 1 / ((g : ℝ) - β - c) ≤ 1 / (1 - β) + 1 + Real.log g :=
    sum_inv_sub_shift_w hβ1
  have hSg : 0 ≤ S * g := mul_nonneg hS0 hg0
  have hb1 : ∑ c ∈ range g, (S * g) * ((1 : ℝ) / (β + c)) ≤
      (S * g) * (1 / β + 1 + Real.log g) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left h1 hSg
  have hb2 : ∑ c ∈ range g, (S * g) * (1 / ((g : ℝ) - β - c)) ≤
      (S * g) * (1 / (1 - β) + 1 + Real.log g) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left h2 hSg
  have hcpi : (1 : ℝ) / π ≤ 0.32 := by
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_d4]
  have hp1 : S * g * (1 / β) ≤ (g : ℝ) := by
    rcases eq_or_lt_of_le hβ0 with hb | hb
    · have hzero : S = 0 := by rw [hS, ← hb]; simp
      rw [hzero]; simp
    · have hSb : S * (1 / β) ≤ 1 := by
        have hp : (0 : ℝ) < π * β := by positivity
        have he : S * (1 / β) = Real.sin (π * β) / (π * β) := by
          rw [hS]; field_simp
        rw [he, div_le_iff₀ hp]
        simpa only [one_mul] using Real.sin_le (show (0 : ℝ) ≤ π * β by positivity)
      have h := mul_le_mul_of_nonneg_right hSb hg0
      have e : S * g * (1 / β) = S * (1 / β) * g := by ring
      rw [e]
      simpa using h
  have hp2 : S * g * (1 / (1 - β)) ≤ (g : ℝ) := by
    rcases eq_or_lt_of_le hβ1 with hb | hb
    · have hzero : S = 0 := by rw [hS, hb]; simp
      rw [hzero]; simp
    · have h1b : 0 < 1 - β := by linarith
      have hSc : S * (1 / (1 - β)) ≤ 1 := by
        have hp : (0 : ℝ) < π * (1 - β) := by positivity
        have he : S * (1 / (1 - β)) = Real.sin (π * β) / (π * (1 - β)) := by
          rw [hS]; field_simp
        rw [he, div_le_iff₀ hp]
        have e : Real.sin (π * β) = Real.sin (π * (1 - β)) := by
          rw [show π * (1 - β) = π - π * β by ring, Real.sin_pi_sub]
        rw [e]
        simpa only [one_mul] using Real.sin_le (show (0 : ℝ) ≤ π * (1 - β) by positivity)
      have h := mul_le_mul_of_nonneg_right hSc hg0
      have e : S * g * (1 / (1 - β)) = S * (1 / (1 - β)) * g := by ring
      rw [e]
      simpa using h
  have hp3 : S * g ≤ (1 / π) * g := by
    have hSle : S ≤ 1 / π := by
      rw [hS]
      exact div_le_div_of_nonneg_right (Real.sin_le_one _) Real.pi_pos.le
    nlinarith
  have hp4 : S * g * Real.log g ≤ (1 / π) * g * Real.log g := by
    have hSle : S ≤ 1 / π := by
      rw [hS]
      exact div_le_div_of_nonneg_right (Real.sin_le_one _) Real.pi_pos.le
    have hl0 : (0 : ℝ) ≤ Real.log g := by linarith
    nlinarith
  have hgk : (S * g) * (1 / β + 1 + Real.log g) ≤ g + (1 / π) * g + (1 / π) * g * Real.log g := by
    have e : (S * g) * (1 / β + 1 + Real.log g) =
        S * g * (1 / β) + S * g + S * g * Real.log g := by ring
    rw [e]
    linarith [hp1, hp3, hp4]
  have hgk2 : (S * g) * (1 / (1 - β) + 1 + Real.log g) ≤
      g + (1 / π) * g + (1 / π) * g * Real.log g := by
    have e : (S * g) * (1 / (1 - β) + 1 + Real.log g) =
        S * g * (1 / (1 - β)) + S * g + S * g * Real.log g := by ring
    rw [e]
    linarith [hp2, hp3, hp4]
  have hl0 : (0 : ℝ) ≤ Real.log g := by linarith
  have key3 : 2 * g + ((g + (1 / π) * g + (1 / π) * g * Real.log g) +
      (g + (1 / π) * g + (1 / π) * g * Real.log g)) ≤ (g : ℝ) * Real.log g := by
    have e1 : (1 / π) * g ≤ 0.32 * g := mul_le_mul_of_nonneg_right hcpi hg0
    have e2 : (1 / π) * g * Real.log g ≤ 0.32 * g * Real.log g := by
      have h := mul_le_mul_of_nonneg_right hcpi (mul_nonneg hg0 hl0)
      nlinarith [h]
    nlinarith [e1, e2, hlog, hgR]
  have hsplit5 : ∑ c ∈ range g, (S * g) * ((1 : ℝ) / (β + c) + 1 / ((g : ℝ) - β - c)) =
      ∑ c ∈ range g, (S * g) * ((1 : ℝ) / (β + c)) +
        ∑ c ∈ range g, (S * g) * (1 / ((g : ℝ) - β - c)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun c _ => by ring)
  have htot2 : ∑ c ∈ range g, ‖∑ d ∈ range g, eC (d * ((β + c) / g))‖ ≤
      2 * g + (∑ c ∈ range g, (S * g) * ((1 : ℝ) / (β + c)) +
        ∑ c ∈ range g, (S * g) * (1 / ((g : ℝ) - β - c))) := by
    refine le_trans htotal ?_
    rw [hsplit5]
  linarith [htot2, hb1, hb2, hgk, hgk2, key3]

/-! ### The digit recursion for the truncated missing-digit sum -/

private theorem sum_range_mul_add (g q r : ℕ) (F : ℕ → ℂ) :
    ∑ m ∈ range (g * q + r), F m =
      ∑ y ∈ range q, ∑ x ∈ range g, F (x + g * y) + ∑ x ∈ range r, F (x + g * q) := by
  rw [Finset.sum_range_add]
  congr 1
  · induction q with
    | zero => simp
    | succ q ih =>
      rw [show g * (q + 1) = g * q + g by ring, Finset.sum_range_add, ih, Finset.sum_range_succ]
      congr 1
      exact Finset.sum_congr rfl fun x _ => by rw [add_comm]
  · exact Finset.sum_congr rfl fun x _ => by rw [add_comm]

/-- The digit recursion: `|E_N(α)| ≤ |f_{g,b}(α)| |E_{⌊N/g⌋}(gα)| + g`. -/
private theorem norm_EN_le {g b : ℕ} (hg : 2 ≤ g) (hb : 1 ≤ b) (N : ℕ) (α : ℝ) :
    ‖∑ m ∈ (range N).filter (NoDigit g b), eC (m * α)‖ ≤
      ‖∑ d ∈ (range g).filter (fun d => d ≠ b), eC (d * α)‖ *
        ‖∑ m ∈ (range (N / g)).filter (NoDigit g b), eC (m * (g * α))‖ + g := by
  have hg0 : 0 < g := by omega
  set q := N / g
  set r := N % g
  have hN : N = g * q + r := (Nat.div_add_mod N g).symm
  have hr : r < g := Nat.mod_lt _ hg0
  have key : ∀ y x : ℕ, x < g →
      (if NoDigit g b (x + g * y) then eC (((x + g * y : ℕ) : ℝ) * α) else 0) =
        (if x ≠ b then eC (x * α) else 0) *
          (if NoDigit g b y then eC (y * (g * α)) else 0) := by
    intro y x hx
    have hiff := md_add_mul (y := y) hg hb hx
    by_cases h1 : x = b
    · have : ¬ NoDigit g b (x + g * y) := fun h => (hiff.1 h).1 h1
      rw [if_neg this]; simp [h1]
    · by_cases h2 : NoDigit g b y
      · have : NoDigit g b (x + g * y) := hiff.2 ⟨h1, h2⟩
        simp only [this, h1, h2, if_true, ne_eq, not_false_eq_true]
        rw [← eC_add]; congr 1; push_cast; ring
      · have : ¬ NoDigit g b (x + g * y) := fun h => h2 (hiff.1 h).2
        simp [this, h2]
  have hEN : (∑ m ∈ (range N).filter (NoDigit g b), eC (m * α)) =
      (∑ d ∈ (range g).filter (fun d => d ≠ b), eC (d * α)) *
          (∑ m ∈ (range q).filter (NoDigit g b), eC (m * (g * α))) +
        ∑ x ∈ range r, (if NoDigit g b (x + g * q) then
          eC (((x + g * q : ℕ) : ℝ) * α) else 0) := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
    conv_lhs => rw [hN]
    rw [sum_range_mul_add]
    congr 1
    rw [Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y _ => ?_
    rw [key y x (Finset.mem_range.1 hx)]
  rw [hEN]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul]
  have hR : ‖∑ x ∈ range r, (if NoDigit g b (x + g * q) then
      eC (((x + g * q : ℕ) : ℝ) * α) else 0)‖ ≤ g := by
    refine le_trans (norm_sum_le _ _) ?_
    have : ∀ x ∈ range r, ‖(if NoDigit g b (x + g * q) then
        eC (((x + g * q : ℕ) : ℝ) * α) else 0)‖ ≤ 1 := by
      intro x _
      split_ifs
      · rw [norm_eC_w]
      · simp
    refine le_trans (Finset.sum_le_sum this) ?_
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact_mod_cast hr.le
  linarith

/-- The change of variables `α = (β + c)/g` on the `g` subintervals of `[0,1]`:
`∫_0^1 h(α) k(gα) dα ≤ D ∫_0^1 k` when `k ≥ 0` is `1`-periodic and
`∑_{c<g} h((β+c)/g) ≤ g D` on `[0,1]`. -/
private theorem integral_mul_comp_le {g : ℕ} (hg : 1 ≤ g) (h k : ℝ → ℝ) (hh : Continuous h)
    (hk : Continuous k) (hk0 : ∀ x, 0 ≤ k x) (hkper : Function.Periodic k 1) {D : ℝ}
    (hD : ∀ β ∈ Set.Icc (0 : ℝ) 1, ∑ c ∈ range g, h ((β + c) / g) ≤ g * D) :
    ∫ α in (0 : ℝ)..1, h α * k (g * α) ≤ D * ∫ β in (0 : ℝ)..1, k β := by
  have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hgp : (0 : ℝ) < g := by linarith
  set F : ℝ → ℝ := fun α => h α * k (g * α) with hFdef
  have hF : Continuous F := by fun_prop
  have hsplit : ∫ α in (0 : ℝ)..1, F α =
      ∑ c ∈ range g, ∫ α in ((c : ℝ) / g)..(((c + 1 : ℕ) : ℝ) / g), F α := by
    rw [intervalIntegral.sum_integral_adjacent_intervals
      (a := fun c : ℕ => (c : ℝ) / g) (fun _ _ => hF.intervalIntegrable _ _)]
    simp [hgp.ne']
  have hpiece : ∀ c : ℕ, ∫ α in ((c : ℝ) / g)..(((c + 1 : ℕ) : ℝ) / g), F α =
      (1 / (g : ℝ)) * ∫ β in (0 : ℝ)..1, h ((β + c) / g) * k β := by
    intro c
    have e1 : (fun β : ℝ => h ((β + c) / g) * k β) = fun β => F ((β + c) / g) := by
      funext β
      simp only [hFdef]
      congr 1
      rw [mul_div_cancel₀ _ hgp.ne']
      have := hkper.nat_mul c β
      simp only [mul_one] at this
      rw [this]
    rw [e1, intervalIntegral.integral_comp_add_right (fun y => F (y / g)),
      intervalIntegral.integral_comp_div F hgp.ne']
    rw [smul_eq_mul, ← mul_assoc, one_div_mul_cancel hgp.ne', one_mul]
    push_cast; ring_nf
  show ∫ α in (0 : ℝ)..1, F α ≤ _
  rw [hsplit]
  simp_rw [hpiece]
  have hsum : ∑ c ∈ range g, ∫ β in (0 : ℝ)..1, h ((β + c) / g) * k β =
      ∫ β in (0 : ℝ)..1, ∑ c ∈ range g, h ((β + c) / g) * k β := by
    rw [intervalIntegral.integral_finsetSum]
    intro c _
    exact (by fun_prop : Continuous fun β => h ((β + c) / g) * k β).intervalIntegrable _ _
  rw [← Finset.mul_sum, hsum]
  simp_rw [← Finset.sum_mul]
  have hmono : ∫ β in (0 : ℝ)..1, (∑ c ∈ range g, h ((β + c) / g)) * k β ≤
      ∫ β in (0 : ℝ)..1, (g * D) * k β := by
    apply intervalIntegral.integral_mono_on zero_le_one
    · exact (by fun_prop : Continuous fun β => (∑ c ∈ range g, h ((β + c) / g)) * k β)
        |>.intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun β => (g * D) * k β).intervalIntegrable _ _
    · intro β hβ
      exact mul_le_mul_of_nonneg_right (hD β hβ) (hk0 β)
  rw [intervalIntegral.integral_const_mul] at hmono
  calc 1 / (g : ℝ) * ∫ β in (0 : ℝ)..1, (∑ c ∈ range g, h ((β + c) / g)) * k β
      ≤ 1 / (g : ℝ) * ((g * D) * ∫ β in (0 : ℝ)..1, k β) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = D * ∫ β in (0 : ℝ)..1, k β := by field_simp

/-- One step of the recursion for `a(N) = ∫_0^1 |E_N|`: `a(N) ≤ (log g + 1) a(⌊N/g⌋) + g`. -/
private theorem int_EN_step {g b : ℕ} (hg : 33554432 ≤ g) (hb : 1 ≤ b) (hbg : b < g) (N : ℕ) :
    ∫ α in (0 : ℝ)..1, ‖∑ m ∈ (range N).filter (NoDigit g b), eC (m * α)‖ ≤
      (Real.log g + 1) * (∫ α in (0 : ℝ)..1,
        ‖∑ m ∈ (range (N / g)).filter (NoDigit g b), eC (m * α)‖) + g := by
  have hg2 : 2 ≤ g := by omega
  have hc1 : Continuous fun α => ‖∑ m ∈ (range N).filter (NoDigit g b), eC (m * α)‖ := by
    have := continuous_eC; fun_prop
  have hc2 : Continuous fun α =>
      ‖∑ d ∈ (range g).filter (fun d => d ≠ b), eC (d * α)‖ *
        ‖∑ m ∈ (range (N / g)).filter (NoDigit g b), eC (m * (g * α))‖ + g := by
    have := continuous_eC; fun_prop
  have hmono : ∫ α in (0 : ℝ)..1, ‖∑ m ∈ (range N).filter (NoDigit g b), eC (m * α)‖ ≤
      ∫ α in (0 : ℝ)..1, (‖∑ d ∈ (range g).filter (fun d => d ≠ b), eC (d * α)‖ *
        ‖∑ m ∈ (range (N / g)).filter (NoDigit g b), eC (m * (g * α))‖ + g) :=
    intervalIntegral.integral_mono_on zero_le_one (hc1.intervalIntegrable _ _)
      (hc2.intervalIntegrable _ _) (fun α _ => norm_EN_le hg2 hb N α)
  have hc3 : Continuous fun α => ‖∑ d ∈ (range g).filter (fun d => d ≠ b), eC (d * α)‖ *
      ‖∑ m ∈ (range (N / g)).filter (NoDigit g b), eC (m * (g * α))‖ := by
    have := continuous_eC; fun_prop
  rw [intervalIntegral.integral_add (hc3.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const, sub_zero, one_smul] at hmono
  have hper : Function.Periodic (fun α => ‖∑ m ∈ (range (N / g)).filter (NoDigit g b),
      eC (m * α)‖) 1 :=
    periodic_norm_sum_eC _
  have hcv := integral_mul_comp_le (g := g) (by omega)
    (fun α => ‖∑ d ∈ (range g).filter (fun d => d ≠ b), eC (d * α)‖)
    (fun α => ‖∑ m ∈ (range (N / g)).filter (NoDigit g b), eC (m * α)‖)
    (by have := continuous_eC; fun_prop) (by have := continuous_eC; fun_prop)
    (fun _ => norm_nonneg _) hper
    (D := Real.log g + 1) (fun β hβ => digit_avg_le hg hbg hβ.1 hβ.2)
  linarith

private theorem int_EN_le {g b : ℕ} (hg : 33554432 ≤ g) (hb : 1 ≤ b) (hbg : b < g) :
    ∀ j N : ℕ, N < g ^ j →
      ∫ α in (0 : ℝ)..1, ‖∑ m ∈ (range N).filter (NoDigit g b), eC (m * α)‖ ≤
        2 * g * (Real.log g + 1) ^ j - g := by
  have hg2 : 2 ≤ g := by omega
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg2
  have hL : 0 ≤ Real.log g := Real.log_nonneg (by linarith)
  have hlog : 17 ≤ Real.log g := by
    have h1 : Real.log (33554432 : ℝ) = 25 * Real.log 2 := by
      rw [show (33554432 : ℝ) = 2 ^ 25 by norm_num, Real.log_pow]
      push_cast
      ring
    have h2 : Real.log (33554432 : ℝ) ≤ Real.log g :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hg)
    have h3 : 0.693 < Real.log 2 := by linarith [Real.log_two_gt_d9]
    linarith
  intro j
  induction j with
  | zero =>
    intro N hN
    have : N = 0 := by simpa using hN
    subst this
    simp
    linarith
  | succ j ih =>
    intro N hN
    have hq : N / g < g ^ j := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; rwa [← pow_succ]
    have h1 := int_EN_step hg hb hbg N
    have h2 := ih _ hq
    have hD : 2 ≤ Real.log g + 1 := by linarith [hlog]
    have hDj : 0 ≤ (Real.log g + 1) ^ j := by positivity
    have h3 : (Real.log g + 1) * (∫ α in (0 : ℝ)..1,
        ‖∑ m ∈ (range (N / g)).filter (NoDigit g b), eC (m * α)‖) ≤
        (Real.log g + 1) * (2 * g * (Real.log g + 1) ^ j - g) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    rw [pow_succ]
    have hDj : (0 : ℝ) ≤ (Real.log g + 1) ^ j := by positivity
    have hgg : (0 : ℝ) ≤ (g : ℝ) := by positivity
    nlinarith [h1, h3, hDj, hgg]

/-! ### From `starSet` to the truncated sum -/

private theorem starSet_eq_map {g b k : ℕ} (hg : 2 ≤ g) (hb : 2 ≤ b) {H : ℝ}
    (hHX : ⌊H⌋₊ < g ^ k) :
    starSet g b (g ^ k) H =
      ((Ioc 0 ⌊H⌋₊).filter (NoDigit g b)).map (addLeftEmbedding (g ^ k)) := by
  have hS : ∀ m, m ≤ ⌊H⌋₊ → (NoDigit g b (g ^ k + m) ↔ NoDigit g b m) :=
    fun m hm => md_pow_add hg hb k m (by omega)
  ext n
  simp only [starSet, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_map, addLeftEmbedding_apply]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨n - g ^ k, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
    rw [← hS _ (by omega), show g ^ k + (n - g ^ k) = n by omega]; exact h3
  · rintro ⟨m, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
    exact ⟨⟨by omega, by omega⟩, (hS m h2).2 h3⟩

private theorem EN_succ_eq (g b M : ℕ) (α : ℝ) :
    (∑ m ∈ (range (M + 1)).filter (NoDigit g b), eC (m * α)) =
      1 + ∑ m ∈ (Ioc 0 M).filter (NoDigit g b), eC (m * α) := by
  have e2 : (Finset.range (M + 1)).filter (NoDigit g b) =
      insert 0 ((Finset.Ioc 0 M).filter (NoDigit g b)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.eq_zero_or_pos n with rfl | hp
      · exact Or.inl rfl
      · exact Or.inr ⟨⟨hp, by omega⟩, h2⟩
    · rintro (rfl | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨by omega, md_zero g b⟩
      · exact ⟨by omega, h3⟩
  have h0 : ¬ (0 : ℕ) ∈ (Ioc 0 M).filter (NoDigit g b) := by
    simp only [Finset.mem_filter, Finset.mem_Ioc]; omega
  rw [e2, Finset.sum_insert h0]
  have := eC_int 0
  push_cast at this
  simp [this]

private theorem norm_sum_starSet_le {g b k : ℕ} (hg : 2 ≤ g) (hb : 2 ≤ b) {H : ℝ}
    (hHX : ⌊H⌋₊ < g ^ k) (α : ℝ) :
    ‖∑ n ∈ starSet g b (g ^ k) H, eC (n * α)‖ ≤
      ‖∑ m ∈ (range (⌊H⌋₊ + 1)).filter (NoDigit g b), eC (m * α)‖ + 1 := by
  rw [starSet_eq_map hg hb hHX, Finset.sum_map]
  simp only [addLeftEmbedding_apply]
  have e : ∀ m : ℕ, eC (((g ^ k + m : ℕ) : ℝ) * α) =
      eC (((g ^ k : ℕ) : ℝ) * α) * eC (m * α) := by
    intro m; rw [← eC_add]; congr 1; push_cast; ring
  simp_rw [e]
  rw [← Finset.mul_sum, norm_mul, norm_eC_w, one_mul]
  have h := EN_succ_eq g b ⌊H⌋₊ α
  have : ∑ m ∈ (Ioc 0 ⌊H⌋₊).filter (NoDigit g b), eC (m * α) =
      (∑ m ∈ (range (⌊H⌋₊ + 1)).filter (NoDigit g b), eC (m * α)) - 1 := by
    rw [h]; ring
  rw [this]
  refine le_trans (norm_sub_le _ _) ?_
  simp

/-! ### Assembly: Kim's Lemma 1.7 with the exponent `thetaG` -/

private theorem lemma_1_7_wip : ∃ g₀ : ℕ, ∀ g b : ℕ, g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∃ C : ℝ,
    ∀ (k : ℕ) (H : ℝ), 1 ≤ H → H < ((g ^ k : ℕ) : ℝ) →
      ∫ α in (0 : ℝ)..1, ‖∑ n ∈ starSet g b (g ^ k) H, eC (n * α)‖ ≤
        C * ((starSet g b (g ^ k) H).card : ℝ) ^ thetaG g := by
  refine ⟨33554432, fun g b hg hb hbg => ?_⟩
  have hg3 : 3 ≤ g := by omega
  have hkg : 1 ≤ g := by omega
  have hgR3 : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg3
  set D : ℝ := Real.log g + 1 with hD
  have hL : 0 < Real.log g := Real.log_pos (by linarith)
  have hD1 : 1 ≤ D := by rw [hD]; linarith
  refine ⟨2 * g * D ^ 2 + 1, fun k H hH1 hHX => ?_⟩
  set M := ⌊H⌋₊ with hM
  have hMk : M < g ^ k := (Nat.floor_lt (by linarith)).2 hHX
  set j := Nat.log g M with hj
  have hMj : M < g ^ (j + 1) := Nat.lt_pow_succ_log_self (by omega) M
  have hMj2 : M + 1 < g ^ (j + 2) := by
    have : g ^ (j + 1) < g ^ (j + 2) := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have hc1 : Continuous fun α => ‖∑ n ∈ starSet g b (g ^ k) H, eC (n * α)‖ := by
    have := continuous_eC
    fun_prop
  have hc2 : Continuous fun α => ‖∑ m ∈ (range (M + 1)).filter (NoDigit g b), eC (m * α)‖ + 1 := by
    have := continuous_eC
    fun_prop
  have hint : ∫ α in (0 : ℝ)..1, ‖∑ n ∈ starSet g b (g ^ k) H, eC (n * α)‖ ≤
      2 * g * D ^ (j + 2) - g + 1 := by
    refine le_trans (intervalIntegral.integral_mono_on zero_le_one (hc1.intervalIntegrable _ _)
      (hc2.intervalIntegrable _ _) (fun α _ => norm_sum_starSet_le (by omega) hb hMk α)) ?_
    rw [intervalIntegral.integral_add
      ((by have := continuous_eC; fun_prop : Continuous fun α =>
        ‖∑ m ∈ (range (M + 1)).filter (NoDigit g b), eC (m * α)‖).intervalIntegrable _ _)
      intervalIntegrable_const, intervalIntegral.integral_const, sub_zero, one_smul]
    have hb2 := int_EN_le (g := g) (b := b) hg (by omega) (by omega) (j + 2) (M + 1) hMj2
    rw [hD]
    linarith
  set N : ℝ := ((starSet g b (g ^ k) H).card : ℝ) with hNdef
  have hcard := card_starSet_ge (by omega) hb (by omega) hH1 hHX
  have hNj : ((g : ℝ) - 1) ^ j ≤ N := by
    have : (((g - 1) ^ j : ℕ) : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hcard
    push_cast [show 1 ≤ g by omega] at this
    exact this
  have hN1 : 1 ≤ N := le_trans (one_le_pow₀ (by linarith : (1 : ℝ) ≤ (g : ℝ) - 1)) hNj
  have hNp : 0 < N := by linarith
  have hgm : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  have hLm : 0 < Real.log ((g : ℝ) - 1) := Real.log_pos (by linarith)
  have hθD : thetaG g = Real.log D / Real.log ((g : ℝ) - 1) := by
    unfold thetaG
    rw [← hD]
  have hθ0 : 0 ≤ thetaG g := by
    rw [hθD]
    exact div_nonneg (Real.log_nonneg hD1) hLm.le
  have hbase : ((g : ℝ) - 1) ^ thetaG g = D := by
    rw [Real.rpow_def_of_pos hgm, hθD, mul_div_cancel₀ _ hLm.ne', Real.exp_log (by linarith)]
  have hDj : D ^ j ≤ N ^ thetaG g := by
    calc D ^ j = (((g : ℝ) - 1) ^ thetaG g) ^ j := by rw [hbase]
      _ = (((g : ℝ) - 1) ^ j) ^ thetaG g := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hgm.le, mul_comm,
            Real.rpow_mul hgm.le, Real.rpow_natCast]
      _ ≤ N ^ thetaG g := Real.rpow_le_rpow (by positivity) hNj hθ0
  have hgj : 0 ≤ (g : ℝ) := by linarith
  have hD2 : 0 ≤ 2 * g * D ^ 2 := by positivity
  calc ∫ α in (0 : ℝ)..1, ‖∑ n ∈ starSet g b (g ^ k) H, eC (n * α)‖
      ≤ 2 * g * D ^ (j + 2) - g + 1 := hint
    _ ≤ (2 * g * D ^ 2 + 1) * D ^ j := by
        rw [pow_add]
        have hDj1 : 1 ≤ D ^ j := one_le_pow₀ hD1
        nlinarith [hDj1, hgj, hD2, pow_pos (by linarith : (0:ℝ) < D) j]
    _ ≤ (2 * g * D ^ 2 + 1) * N ^ thetaG g :=
        mul_le_mul_of_nonneg_left hDj (by positivity)

/-- LEAF: Kim, Lemma 1.7, page 5: for `g` sufficiently large,
`∫_{[0,1]} |F_{[X,X+H]}(α)| dα ≪ |[X,X+H]^*|^{-1 + log((log g)+1)/log(g-1)}`, with
`F_{[X,X+H]}(α) = |[X,X+H]^*|^{-1} ∑_{n ∈ [X,X+H]^*} e(nα)`. Multiplied through by
`|[X,X+H]^*|`, which is at least `1` here, this is the form below. The paper gives no proof;
the implied constant may depend on `g` and `b`. Encoded for `X = g^k` and `1 ≤ H < X`, the
setting of Sections 1 and 2. -/
theorem lemma_1_7 : ∃ g₀ : ℕ, ∀ g b : ℕ, g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∃ C : ℝ,
    ∀ (k : ℕ) (H : ℝ), 1 ≤ H → H < ((g ^ k : ℕ) : ℝ) →
      ∫ α in (0 : ℝ)..1, ‖∑ n ∈ starSet g b (g ^ k) H, eC (n * α)‖ ≤
        C * ((starSet g b (g ^ k) H).card : ℝ) ^ thetaG g :=
  lemma_1_7_wip

/-- LEAF: Kim, Proposition 3.5, page 13: for `α ∈ 𝔪`, `S♯₄(α; H) ≪ δH`, with
`δ = X^{-ε}` and `X^{3/5+ε} ≤ H ≤ X^{1-ε}` as in Section 2. It combines Lemma 3.3, which is
MRSTT II Lemma 2.19, with the inverse theorem Proposition 3.4 and Lemma 3.1. Encoded with `ε`
small and with the implied constant `C` and threshold `X₀` explicit. -/
theorem prop_3_5 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ C : ℝ, ∃ X₀ : ℕ,
    ∀ X : ℕ, X₀ ≤ X → ∀ H : ℝ,
      (X : ℝ) ^ ((3 : ℝ) / 5 + ε) ≤ H → H ≤ (X : ℝ) ^ (1 - ε) →
      ∀ α ∈ arcRange ε X \ majorArcs ε X H, ‖S4sharp ε X H α‖ ≤ C * (delta ε X * H) := by
  sorry

/-! ### Range facts for `X = g^k` -/

theorem range_facts {g k : ℕ} (hg : 3 ≤ g) (hk : 1 ≤ k) {ε a H : ℝ} (hε : 0 < ε) (ha : 0 ≤ a)
    (hlo : ((g ^ k : ℕ) : ℝ) ^ (a + ε) ≤ H) (hhi : H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε)) :
    1 ≤ H ∧ H < ((g ^ k : ℕ) : ℝ) ∧ k ≤ g ^ k := by
  have hX1 : (1 : ℝ) < ((g ^ k : ℕ) : ℝ) := by
    have : 1 < g ^ k := Nat.one_lt_pow (by omega) (by omega)
    exact_mod_cast this
  refine ⟨le_trans (Real.one_le_rpow hX1.le (by linarith)) hlo, ?_, (Nat.lt_pow_self (by omega)).le⟩
  calc H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) := hhi
    _ < ((g ^ k : ℕ) : ℝ) ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hX1 (by linarith)
    _ = _ := Real.rpow_one _

/-! ### Proposition 2.2 and Proposition 2.5, proved from the cited inputs -/

theorem S4_continuous (X : ℕ) (H : ℝ) : Continuous (fun α => S4 X H α) := by
  unfold S4; have := continuous_eC; fun_prop

theorem S4sharp_cont (ε : ℝ) (X : ℕ) (H : ℝ) : Continuous (fun α => S4sharp ε X H α) := by
  unfold S4sharp; have := continuous_eC; fun_prop

/-- Kim, Proposition 2.2 with display (2.1), page 8, PROVED from `prop_2_1` and `lemma_1_7`
by the paper's display (2.2). Same statement as `Burst4Split.prop_2_2`. -/
theorem prop_2_2_p2 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ g₀ : ℕ, ∀ g b : ℕ,
    g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∀ η : ℝ, 0 < η → ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      ((g ^ k : ℕ) : ℝ) ^ ((3 : ℝ) / 5 + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      ‖∑ n ∈ starSet g b (g ^ k) H,
          ∫ α in (0 : ℝ)..1, (S4 (g ^ k) H α - S4sharp ε (g ^ k) H α) * eC (-(n * α))‖ ≤
        η * (starSet g b (g ^ k) H).card := by
  obtain ⟨ε₁, hε₁, h21⟩ := prop_2_1
  obtain ⟨g₁, h17⟩ := lemma_1_7
  refine ⟨ε₁, hε₁, fun ε hε hεε => ?_⟩
  obtain ⟨c, hc, C, X₀, hC⟩ := h21 ε hε hεε
  obtain ⟨g₂, hg₂3, htail⟩ := tail_small (mul_pos hc hε)
  refine ⟨max g₁ g₂, fun g b hg hb2 hbg η hη => ?_⟩
  have hg1 : g₁ ≤ g := le_trans (le_max_left _ _) hg
  have hg2 : g₂ ≤ g := le_trans (le_max_right _ _) hg
  have hg3 : 3 ≤ g := le_trans hg₂3 hg2
  obtain ⟨C₂, hC₂⟩ := h17 g b hg1 hb2 hbg
  obtain ⟨K₁, hK₁⟩ := htail g b hg2 hb2 hbg (C * C₂) η hη
  refine ⟨max K₁ (max X₀ 1), fun k H hk hlo hhi => ?_⟩
  have hkK : K₁ ≤ k := le_trans (le_max_left _ _) hk
  have hkX : X₀ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk1 : 1 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  obtain ⟨hH1, hHX, hkg⟩ := range_facts hg3 hk1 hε (by norm_num) hlo hhi
  have hb := hC (g ^ k) (le_trans hkX hkg) H hlo hhi
  set X : ℝ := ((g ^ k : ℕ) : ℝ)
  set M : ℝ := C * H * X ^ (-(c * ε))
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hb 0)
  have hF : Continuous (fun α => S4 (g ^ k) H α - S4sharp ε (g ^ k) H α) :=
    (S4_continuous _ _).sub (S4sharp_cont _ _ _)
  simp_rw [intervalIntegral.integral_of_le (zero_le_one' ℝ)]
  refine le_trans (norm_sum_setIntegral_le (measurableSet_Ioc) Set.Ioc_subset_Icc_self _ hF _
    (fun α _ => hb α)) ?_
  rw [setIntegral_Ioc01_norm]
  have hL := hC₂ k H hH1 hHX
  have h2 := hK₁ k H hkK hH1 hHX
  calc M * ∫ α in (0 : ℝ)..1, ‖∑ n ∈ starSet g b (g ^ k) H, eC (n * α)‖
      ≤ M * (C₂ * ((starSet g b (g ^ k) H).card : ℝ) ^ thetaG g) :=
        mul_le_mul_of_nonneg_left hL hM0
    _ = C * C₂ * H * X ^ (-(c * ε)) * ((starSet g b (g ^ k) H).card : ℝ) ^ thetaG g := by
        ring
    _ ≤ _ := h2

/-- Kim, Proposition 2.5, page 9, PROVED from `prop_3_5` and `lemma_1_7` by the paper's
proof: the minor arc contribution is at most `sup_𝔪 |S♯₄| ∫_𝔪 |∑_{n ∈ [X,X+H]^*} e(-nα)| dα`.
Same statement as `Burst4Split.prop_2_5`. -/
theorem prop_2_5_p2 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ g₀ : ℕ, ∀ g b : ℕ,
    g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∀ η : ℝ, 0 < η → ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      ((g ^ k : ℕ) : ℝ) ^ ((3 : ℝ) / 5 + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      ‖∑ n ∈ starSet g b (g ^ k) H, minorInt ε (g ^ k) H n‖ ≤
        η * (starSet g b (g ^ k) H).card := by
  obtain ⟨ε₁, hε₁, h35⟩ := prop_3_5
  obtain ⟨g₁, h17⟩ := lemma_1_7
  refine ⟨ε₁, hε₁, fun ε hε hεε => ?_⟩
  obtain ⟨C, X₀, hC⟩ := h35 ε hε hεε
  obtain ⟨g₂, hg₂3, htail⟩ := tail_small hε
  refine ⟨max g₁ g₂, fun g b hg hb2 hbg η hη => ?_⟩
  have hg1 : g₁ ≤ g := le_trans (le_max_left _ _) hg
  have hg2 : g₂ ≤ g := le_trans (le_max_right _ _) hg
  have hg3 : 3 ≤ g := le_trans hg₂3 hg2
  obtain ⟨C₂, hC₂⟩ := h17 g b hg1 hb2 hbg
  obtain ⟨K₁, hK₁⟩ := htail g b hg2 hb2 hbg (max C 0 * C₂) η hη
  refine ⟨max K₁ (max X₀ 1), fun k H hk hlo hhi => ?_⟩
  have hkK : K₁ ≤ k := le_trans (le_max_left _ _) hk
  have hkX : X₀ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk1 : 1 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  obtain ⟨hH1, hHX, hkg⟩ := range_facts hg3 hk1 hε (by norm_num) hlo hhi
  have hb := hC (g ^ k) (le_trans hkX hkg) H hlo hhi
  set X : ℝ := ((g ^ k : ℕ) : ℝ) with hXdef
  have hXp : 0 < X := by linarith
  have hδ : delta ε (g ^ k) = X ^ (-ε) := rfl
  have hδH : 0 ≤ delta ε (g ^ k) * H := by
    rw [hδ]; exact mul_nonneg (Real.rpow_pos_of_pos hXp _).le (by linarith)
  set M : ℝ := max C 0 * (delta ε (g ^ k) * H)
  have hM0 : 0 ≤ M := mul_nonneg (le_max_right _ _) hδH
  have hbM : ∀ α ∈ arcRange ε (g ^ k) \ majorArcs ε (g ^ k) H, ‖S4sharp ε (g ^ k) H α‖ ≤ M :=
    fun α hα => le_trans (hb α hα) (mul_le_mul_of_nonneg_right (le_max_left _ _) hδH)
  have hmeas : MeasurableSet (arcRange ε (g ^ k) \ majorArcs ε (g ^ k) H) :=
    measurableSet_Ioc.diff (measurableSet_majorArcs _ _ _)
  have hsub : arcRange ε (g ^ k) \ majorArcs ε (g ^ k) H ⊆
      Set.Icc (1 / Qpar ε (g ^ k)) (1 + 1 / Qpar ε (g ^ k)) :=
    fun α hα => Set.Ioc_subset_Icc_self hα.1
  unfold minorInt
  refine le_trans (norm_sum_setIntegral_le hmeas hsub _ (S4sharp_cont _ _ _) _ hbM) ?_
  have hce := continuous_eC
  have hmono : ∫ α in arcRange ε (g ^ k) \ majorArcs ε (g ^ k) H,
        ‖∑ n ∈ starSet g b (g ^ k) H, eC (-(n * α))‖ ≤
      ∫ α in arcRange ε (g ^ k), ‖∑ n ∈ starSet g b (g ^ k) H, eC (-(n * α))‖ := by
    apply setIntegral_mono_set
    · have hc : Continuous (fun α : ℝ => ‖∑ n ∈ starSet g b (g ^ k) H, eC (-(n * α))‖) := by
        fun_prop
      exact (hc.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
    · exact Set.diff_subset.eventuallyLE
  rw [setIntegral_arcRange_norm] at hmono
  have hL := hC₂ k H hH1 hHX
  have h2 := hK₁ k H hkK hH1 hHX
  calc M * ∫ α in arcRange ε (g ^ k) \ majorArcs ε (g ^ k) H,
        ‖∑ n ∈ starSet g b (g ^ k) H, eC (-(n * α))‖
      ≤ M * (C₂ * ((starSet g b (g ^ k) H).card : ℝ) ^ thetaG g) :=
        mul_le_mul_of_nonneg_left (le_trans hmono hL) hM0
    _ = max C 0 * C₂ * H * X ^ (-ε) * ((starSet g b (g ^ k) H).card : ℝ) ^ thetaG g := by
        simp only [M]; rw [hδ]; ring
    _ ≤ _ := h2

/-! ### The major arcs: Proposition 2.4 and Section 2.2 -/

/-- The main term of Proposition 2.4, display (2.6), page 9, written before the paper's
regrouping of `b` and `m` through `l₁ ∣ q` and `l₂ ∣ q`: integrating display (2.5) of
Proposition 2.3 against `e(-nα)` over `|α - a/q| < β(δ)` gives
`∑_{q ≤ Q} ∑*_{a(q)} ∑_{m ≤ X^{3ε/20}} ∑_{b(q)} (1/(mq)) e(a(mb - n)/q)
  ∫_X^{X+H} P_m(log u) sin(2πβ(δ)(u-n)) / (π(u-n)) du`,
since `∫_{-β}^{β} e(ηt) dη = sin(2πβt)/(πt)`. The paper's kernel `K` omits the factor `1/π`;
this changes only the implied constant. Here `X^{3ε/20} = R₄⁶`. At `u = n` the integrand is `0`
in Lean, a single point, which changes no integral. -/
noncomputable def mainK (ε : ℝ) (X : ℕ) (H : ℝ) (n : ℕ) : ℂ :=
  ∑ q ∈ Icc 1 ⌊Qpar ε X⌋₊, ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
    ∑ m ∈ Icc 1 ⌊R4 ε X ^ 6⌋₊, ∑ b ∈ range q,
      (1 / ((m : ℂ) * q)) * eC ((a : ℝ) * ((m : ℝ) * b - n) / q) *
        (((∫ u in (X : ℝ)..(X + H), Pm (R4 ε X) m (Real.log u) *
            Real.sin (2 * π * betaDelta ε X H * (u - n)) / (π * (u - n))) : ℝ) : ℂ)

set_option maxHeartbeats 2000000 in
/-- LEAF: Kim, Proposition 2.4, display (2.6), page 9: for `X^{3/5+ε} ≤ H ≤ X^{1-ε}`,
`∑_{n ∈ [X,X+H]^*} ∫_{𝔐} S♯₄(α;H) e(-nα) dα` equals the main term `mainK` summed over
`n ∈ [X,X+H]^*` up to `O(X^{5ε} H^{3ε})`. Its proof uses Proposition 2.3, display (2.5), for
the approximation of `S♯₄(a/q + β; H)`, and Lemma 1.7 for the error terms, so it needs `g`
large. Encoded with `ε` small and with the constant `C` and threshold `K₀` explicit. -/
theorem prop_2_4 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ g₀ : ℕ, ∀ g b : ℕ,
    g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∃ C : ℝ, ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      ((g ^ k : ℕ) : ℝ) ^ ((3 : ℝ) / 5 + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      ‖(∑ n ∈ starSet g b (g ^ k) H, majorInt ε (g ^ k) H n) -
          ∑ n ∈ starSet g b (g ^ k) H, mainK ε (g ^ k) H n‖ ≤
        C * ((g ^ k : ℕ) : ℝ) ^ (5 * ε) * H ^ (3 * ε) := by
  have hhlr : ∀ {g : ℕ}, 3 ≤ g → 1 / 2 ≤ Real.log ((g : ℝ) - 1) / Real.log g ∧
      Real.log ((g : ℝ) - 1) / Real.log g ≤ 1 := by
    intro g hg
    have hgR : (3 : ℝ) ≤ g := by exact_mod_cast hg
    have hL : 0 < Real.log g := Real.log_pos (by linarith)
    constructor
    · rw [le_div_iff₀ hL]
      have h2 : Real.log g ≤ Real.log (((g : ℝ) - 1) ^ 2) :=
        Real.log_le_log (by linarith) (by nlinarith)
      rw [Real.log_pow] at h2
      push_cast at h2
      linarith
    · rw [div_le_one hL]
      exact Real.log_le_log (by linarith) (by linarith)
  have norm_eC : ∀ x : ℝ, ‖eC x‖ = 1 := by
    intro x
    unfold eC
    have h : 2 * (π : ℂ) * Complex.I * (x : ℂ) = ((2 * π * x : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  have eC_nat_mul : ∀ (d : ℕ) (θ : ℝ), eC (d * θ) = eC θ ^ d := by
    intro d θ
    induction d with
    | zero => simp [eC]
    | succ d ih => rw [pow_succ, ← ih, ← eC_add]; congr 1; push_cast; ring

  have eC_eq_one_iff (x : ℝ) : eC x = 1 ↔ ∃ n : ℤ, x = n := by
    unfold eC
    rw [Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have h2 : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have : (x : ℂ) = n := by
        apply mul_left_cancel₀ h2
        rw [hn]; ring
      exact_mod_cast this
    · rintro ⟨n, rfl⟩
      exact ⟨n, by push_cast; ring⟩
  /- The sum over `b` in display (2.5): for `(a, q) = 1`,
  `∑_{b mod q} e(amb/q) = q` if `q ∣ m` and `0` otherwise. -/
  have sum_b_eC {q a : ℕ} (hq : 1 ≤ q) (hcop : Nat.Coprime a q) (m : ℕ) : ∑ b ∈ range q, eC ((a : ℝ) * m * b / q) = if q ∣ m then (q : ℂ) else 0 := by
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hpow : ∀ b : ℕ, eC ((a : ℝ) * m * b / q) = eC ((a : ℝ) * m / q) ^ b := by
      intro b; rw [← eC_nat_mul]; congr 1; field_simp
    simp_rw [hpow]
    split_ifs with hdvd
    · obtain ⟨t, rfl⟩ := hdvd
      have : eC ((a : ℝ) * ((q * t : ℕ) : ℝ) / q) = 1 := by
        rw [eC_eq_one_iff]; refine ⟨a * t, ?_⟩; push_cast; field_simp
      rw [this]; simp
    · have hz : eC ((a : ℝ) * m / q) ≠ 1 := by
        intro h
        obtain ⟨n, hn⟩ := (eC_eq_one_iff _).1 h
        have h1 : ((a * m : ℕ) : ℤ) = q * n := by
          have : (a : ℝ) * m = q * n := by
            field_simp at hn; linarith
          exact_mod_cast this
        have h2 : (q : ℤ) ∣ ((a * m : ℕ) : ℤ) := ⟨n, h1⟩
        have h3 : q ∣ a * m := by exact_mod_cast h2
        exact hdvd ((Nat.Coprime.symm hcop).dvd_of_dvd_mul_left h3)
      rw [geom_sum_eq hz]
      have : eC ((a : ℝ) * m / q) ^ q = 1 := by
        rw [← eC_nat_mul, eC_eq_one_iff]; refine ⟨a * m, ?_⟩; push_cast; field_simp
      simp [this]
  /- `∫_{-β}^{β} e(tη) dη = sin(2πβt)/(πt)` for `t ≠ 0`; this is where the kernel `K` of
  display (2.6) comes from. -/
  have integral_eC_kernel {t : ℝ} (ht : t ≠ 0) (β : ℝ) : ∫ η in (-β)..β, eC (t * η) = ((Real.sin (2 * π * β * t) / (π * t) : ℝ) : ℂ) := by
      have hc : (2 * (π : ℂ) * Complex.I * t) ≠ 0 := by
        have : (t : ℂ) ≠ 0 := by exact_mod_cast ht
        simp [Real.pi_ne_zero, Complex.I_ne_zero, this]
      have h1 : (fun η : ℝ => eC (t * η)) =
          fun η : ℝ => Complex.exp ((2 * (π : ℂ) * Complex.I * t) * η) := by
        funext η; unfold eC; congr 1; push_cast; ring
      rw [h1, integral_exp_mul_complex hc]
      have e1 : (2 * (π : ℂ) * Complex.I * t) * (β : ℝ) = ((2 * π * β * t : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      have e2 : (2 * (π : ℂ) * Complex.I * t) * ((-β : ℝ) : ℂ) =
          ((-(2 * π * β * t) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [e1, e2, Complex.exp_mul_I, Complex.exp_mul_I]
      push_cast
      rw [Complex.cos_neg, Complex.sin_neg]
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
      field_simp
      ring_nf

    /- ### Proposition 2.3 -/
  /- The main term of display (2.5), page 9, at `a/q + β`:
  `∑_{m ≤ X^{3ε/20}} ∑_{b(q)} e(amb/q) (1/(mq)) ∫_X^{X+H} P_m(log u) e(uβ) du`. -/
  let mainArc := fun (ε : ℝ) (X : ℕ) (H : ℝ) (q a : ℕ) (β : ℝ) =>
      ∑ m ∈ Icc 1 ⌊R4 ε X ^ 6⌋₊, ∑ b ∈ range q,
        eC ((a : ℝ) * m * b / q) * (1 / ((m : ℂ) * q)) *
          ∫ u in (X : ℝ)..(X + H), (Pm (R4 ε X) m (Real.log u) : ℂ) * eC (u * β)

    /-
    ### Ported from Burst8P23: the proof chain of Proposition 2.3.

    This file cannot import Burst8P23, which imports this file, so the chain of lemmas behind
    Burst8P23.prop_2_3_p3 is ported here verbatim, with the same statements, to prove
    prop_2_3 below. AI wrote the Lean code. Binary Goldbach is OPEN.
    -/
  let Vset := fun (R : ℝ) (m j : ℕ) =>
    (Fintype.piFinset fun _ : Fin 3 => Icc 1 ⌊R ^ 2⌋₊).filter
      (fun v => v 0 * v 1 * v 2 = m ∧ (∀ i : Fin 3, i.val < j → (v i : ℝ) ≤ R) ∧
        (∀ i : Fin 3, j ≤ i.val → R < (v i : ℝ) ∧ (v i : ℝ) ≤ R ^ 2))
  /- The shift `log(n₁ ⋯ n_j R^{4-j})` in `P_m`. -/
  let Lsh := fun (R : ℝ) (j : ℕ) (v : Fin 3 → ℕ) =>
    Real.log ((∏ i ∈ (univ : Finset (Fin 3)).filter (fun i => i.val < j), (v i : ℝ)) * R ^ (4 - j))
  have Pm_eq (R : ℝ) (m : ℕ) (t : ℝ) : Pm R m t = ∑ j ∈ range 4, (Nat.choose 4 j : ℝ) *
    ∑ v ∈ Vset R m j, (t - Lsh R j v) ^ (3 - j) /
      ((Nat.factorial (3 - j) : ℝ) * Real.log R ^ (3 - j)) := by
    rfl
  /- The derivative of `P_m`. -/
  let Pmd := fun (R : ℝ) (m : ℕ) (t : ℝ) =>
    ∑ j ∈ range 4, (Nat.choose 4 j : ℝ) *
       ∑ v ∈ Vset R m j, ((3 - j : ℕ) : ℝ) * (t - Lsh R j v) ^ (3 - j - 1) /
         ((Nat.factorial (3 - j) : ℝ) * Real.log R ^ (3 - j))
  have hasDerivAt_Pm (R : ℝ) (m : ℕ) (t : ℝ) : HasDerivAt (Pm R m) (Pmd R m t) t := by
    have e : Pm R m = fun t => ∑ j ∈ range 4, (Nat.choose 4 j : ℝ) *
        ∑ v ∈ Vset R m j, (t - Lsh R j v) ^ (3 - j) /
          ((Nat.factorial (3 - j) : ℝ) * Real.log R ^ (3 - j)) := by
      funext t; exact Pm_eq R m t
    rw [e]
    unfold Pmd
    apply HasDerivAt.fun_sum
    intro j _
    apply HasDerivAt.const_mul
    apply HasDerivAt.fun_sum
    intro v _
    have h := (((hasDerivAt_id t).sub_const (Lsh R j v)).pow (3 - j)).div_const
      ((Nat.factorial (3 - j) : ℝ) * Real.log R ^ (3 - j))
    simp only [id, mul_one] at h
    exact h
  have card_Vset_le {R : ℝ} (hR : 1 ≤ R) (m j : ℕ) : ((Vset R m j).card : ℝ) ≤ R ^ 6 := by
    have h1 : (Vset R m j).card ≤ ⌊R ^ 2⌋₊ ^ 3 := by
      unfold Vset
      refine le_trans (Finset.card_filter_le _ _) ?_
      simp
    have h2 : ((⌊R ^ 2⌋₊ ^ 3 : ℕ) : ℝ) ≤ R ^ 6 := by
      push_cast
      have := Nat.floor_le (by positivity : (0 : ℝ) ≤ R ^ 2)
      calc (⌊R ^ 2⌋₊ : ℝ) ^ 3 ≤ (R ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) this 3
        _ = R ^ 6 := by ring
    exact le_trans (by exact_mod_cast h1) h2
  have Lsh_bounds {R : ℝ} (hR : 1 ≤ R) {m j : ℕ} (hj : j < 4) {v : Fin 3 → ℕ} (hv : v ∈ Vset R m j) : 0 ≤ Lsh R j v ∧ Lsh R j v ≤ 10 * Real.log R := by
    have hvi : ∀ i, 1 ≤ (v i : ℝ) ∧ (v i : ℝ) ≤ R ^ 2 := by
      intro i
      unfold Vset at hv
      rw [Finset.mem_filter, Fintype.mem_piFinset] at hv
      have h := hv.1 i
      rw [Finset.mem_Icc] at h
      exact ⟨by exact_mod_cast h.1, le_trans (by exact_mod_cast h.2) (Nat.floor_le (by positivity))⟩
    set P := ∏ i ∈ (univ : Finset (Fin 3)).filter (fun i => i.val < j), (v i : ℝ)
    have hP1 : 1 ≤ P := Finset.one_le_prod₀ (fun i _ => (hvi i).1)
    have hP2 : P ≤ (R ^ 2) ^ 3 := by
      calc P ≤ ∏ i ∈ (univ : Finset (Fin 3)).filter (fun i => i.val < j), R ^ 2 :=
            Finset.prod_le_prod₀ (fun i _ => by linarith [(hvi i).1]) (fun i _ => (hvi i).2)
        _ = (R ^ 2) ^ ((univ : Finset (Fin 3)).filter (fun i => i.val < j)).card := by
            rw [Finset.prod_const]
        _ ≤ (R ^ 2) ^ 3 := by
            apply pow_le_pow_right₀ (by nlinarith)
            exact le_trans (Finset.card_filter_le _ _) (by simp)
    have hR4 : 1 ≤ R ^ (4 - j) := one_le_pow₀ hR
    have hR4' : R ^ (4 - j) ≤ R ^ 4 := pow_le_pow_right₀ hR (by omega)
    have hRp : 0 < R := by linarith
    unfold Lsh
    constructor
    · exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le hP1 hR4)
    · have : P * R ^ (4 - j) ≤ R ^ 10 := by
        calc P * R ^ (4 - j) ≤ (R ^ 2) ^ 3 * R ^ 4 :=
              mul_le_mul hP2 hR4' (by positivity) (by positivity)
          _ = R ^ 10 := by ring
      calc Real.log (P * R ^ (4 - j)) ≤ Real.log (R ^ 10) :=
            Real.log_le_log (by positivity) this
        _ = 10 * Real.log R := by rw [Real.log_pow]; norm_num
  have sum_choose_four : ∑ j ∈ range 4, (Nat.choose 4 j : ℝ) = 15 := by
    simp [Finset.sum_range_succ, Nat.choose]; norm_num
  /- Generic bound for the double sum shape of `P_m` and its derivative. -/
  have abs_double_sum_le {R B : ℝ} (hR : 1 ≤ R) (hB : 0 ≤ B) (m : ℕ) (f : ℕ → (Fin 3 → ℕ) → ℝ) (hf : ∀ j < 4, ∀ v ∈ Vset R m j, |f j v| ≤ B) : |∑ j ∈ range 4, (Nat.choose 4 j : ℝ) * ∑ v ∈ Vset R m j, f j v| ≤ 15 * R ^ 6 * B := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have h : ∀ j ∈ range 4, |(Nat.choose 4 j : ℝ) * ∑ v ∈ Vset R m j, f j v| ≤
        (Nat.choose 4 j : ℝ) * (R ^ 6 * B) := by
      intro j hj
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum fun v hv => hf j (Finset.mem_range.1 hj) v hv) ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (card_Vset_le hR m j) hB
    refine le_trans (Finset.sum_le_sum h) ?_
    rw [← Finset.sum_mul, sum_choose_four]; ring_nf; rfl
  /- Crude bounds `|P_m(t)| ≤ 15 R⁶ K³` and `|P_m'(t)| ≤ 45 R⁶ K³` for `|t| ≤ T`, `R ≥ 3`, with
  `K = (T + 10 log R)/log R`. They are a crude form of the remark `P_m(log n) ≪_ε d₃(m)`,
  page 7. -/
  have Pm_bounds {R : ℝ} (hR : 3 ≤ R) {T : ℝ} (hT : 0 ≤ T) {t : ℝ} (ht : |t| ≤ T) (m : ℕ) : |Pm R m t| ≤ 15 * R ^ 6 * ((T + 10 * Real.log R) / Real.log R) ^ 3 ∧
      |Pmd R m t| ≤ 15 * R ^ 6 * (3 * ((T + 10 * Real.log R) / Real.log R) ^ 3) := by
      have hR1 : (1 : ℝ) ≤ R := by linarith
      have hℓ : 1 ≤ Real.log R := by
        rw [Real.le_log_iff_exp_le (by linarith)]
        exact le_trans (le_of_lt (lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num))) hR
      set ℓ := Real.log R
      set K := (T + 10 * ℓ) / ℓ with hK
      have hℓp : 0 < ℓ := by linarith
      have hK1 : 1 ≤ K := by rw [hK, le_div_iff₀ hℓp]; linarith
      have hdiff : ∀ j < 4, ∀ v ∈ Vset R m j, |t - Lsh R j v| ≤ K * ℓ := by
        intro j hj v hv
        obtain ⟨h0, h1⟩ := Lsh_bounds hR1 hj hv
        rw [hK, div_mul_cancel₀ _ hℓp.ne']
        rw [abs_le] at ht ⊢; constructor <;> linarith [ht.1, ht.2]
      have hpow : ∀ p : ℕ, p ≤ 3 → ∀ x : ℝ, |x| ≤ K * ℓ →
          |x ^ p / ((Nat.factorial p : ℝ) * ℓ ^ p)| ≤ K ^ 3 := by
        intro p hp x hx
        have hfac : (1 : ℝ) ≤ Nat.factorial p := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero p)
        have hd : 0 < (Nat.factorial p : ℝ) * ℓ ^ p := mul_pos (by linarith) (pow_pos hℓp p)
        rw [abs_div, abs_of_pos hd, abs_pow]
        rw [div_le_iff₀ hd]
        calc |x| ^ p ≤ (K * ℓ) ^ p := pow_le_pow_left₀ (abs_nonneg _) hx p
          _ = K ^ p * ℓ ^ p := by ring
          _ ≤ K ^ 3 * ℓ ^ p := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK1 hp) (by positivity)
          _ ≤ K ^ 3 * ((Nat.factorial p : ℝ) * ℓ ^ p) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              nlinarith [pow_pos hℓp p]
      constructor
      · rw [Pm_eq]
        exact abs_double_sum_le hR1 (by positivity) m _ fun j hj v hv =>
          hpow (3 - j) (by omega) _ (hdiff j hj v hv)
      · unfold Pmd
        refine abs_double_sum_le hR1 (by positivity) m _ fun j hj v hv => ?_
        have hx := hdiff j hj v hv
        rcases Nat.lt_or_ge j 3 with hj3 | hj3
        · -- `p = 3 - j ≥ 1`
          obtain ⟨p, hp⟩ : ∃ p, 3 - j = p + 1 := ⟨3 - j - 1, by omega⟩
          rw [hp, show p + 1 - 1 = p by omega]
          have hfac : (Nat.factorial (p + 1) : ℝ) = (p + 1) * Nat.factorial p := by
            push_cast [Nat.factorial_succ]; ring
          have e : ((p + 1 : ℕ) : ℝ) * (t - Lsh R j v) ^ p /
              ((Nat.factorial (p + 1) : ℝ) * ℓ ^ (p + 1)) =
              ((t - Lsh R j v) ^ p / ((Nat.factorial p : ℝ) * ℓ ^ p)) / ℓ := by
            rw [hfac]; push_cast
            have : (Nat.factorial p : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
            field_simp
            ring
          rw [e, abs_div, abs_of_pos hℓp]
          have h1 := hpow p (by omega) _ hx
          have h2 : |(t - Lsh R j v) ^ p / ((Nat.factorial p : ℝ) * ℓ ^ p)| / ℓ ≤
              |(t - Lsh R j v) ^ p / ((Nat.factorial p : ℝ) * ℓ ^ p)| :=
            div_le_self (abs_nonneg _) hℓ
          have h3 : 0 ≤ K ^ 3 := by positivity
          linarith
        · have : 3 - j = 0 := by omega
          rw [this]; simp; positivity

    /- ### Sums against integrals -/
  /- A sum over consecutive integers against an integral: for `h` with derivative `h'` on
  `[J₀ - 2, J₁ + 2]`, `|h| ≤ M₀` and `|h'| ≤ M₁` there, and endpoints `a ∈ [J₀ - 2, J₀]`,
  `b ∈ [J₁, J₁ + 2]`, `|∑_{J₀ ≤ j ≤ J₁} h(j) - ∫_a^b h| ≤ 3M₀ + (J₁ + 1 - J₀) M₁`. -/
  have sum_Icc_sub_integral_le {h h' : ℝ → ℂ} {J₀ J₁ : ℕ} (hJ : J₀ ≤ J₁ + 1) {a b : ℝ} (ha : (J₀ : ℝ) - 2 ≤ a) (ha' : a ≤ J₀) (hb : (J₁ : ℝ) ≤ b) (hb' : b ≤ J₁ + 2) {M₀ M₁ : ℝ} (hd : ∀ x ∈ Set.Icc ((J₀ : ℝ) - 2) (J₁ + 2), HasDerivAt h (h' x) x) (h0 : ∀ x ∈ Set.Icc ((J₀ : ℝ) - 2) (J₁ + 2), ‖h x‖ ≤ M₀) (h1 : ∀ x ∈ Set.Icc ((J₀ : ℝ) - 2) (J₁ + 2), ‖h' x‖ ≤ M₁) : ‖∑ j ∈ Icc J₀ J₁, h j - ∫ x in a..b, h x‖ ≤ 3 * M₀ + ((J₁ + 1 - J₀ : ℕ) : ℝ) * M₁ := by
      set I := Set.Icc ((J₀ : ℝ) - 2) (J₁ + 2)
      have hJR : (J₀ : ℝ) ≤ J₁ + 1 := by exact_mod_cast hJ
      have hcont : ContinuousOn h I := fun x hx => (hd x hx).continuousAt.continuousWithinAt
      have hii : ∀ u v : ℝ, u ∈ I → v ∈ I → IntervalIntegrable h volume u v := by
        intro u v hu hv
        exact (hcont.mono (Set.uIcc_subset_Icc hu hv)).intervalIntegrable
      have hmemI : ∀ x : ℝ, (J₀ : ℝ) - 2 ≤ x → x ≤ J₁ + 2 → x ∈ I := fun x h1 h2 => ⟨h1, h2⟩
      have hM₀ : 0 ≤ M₀ := le_trans (norm_nonneg _) (h0 J₀ (hmemI _ (by linarith) (by linarith)))
      have hM₁ : 0 ≤ M₁ := le_trans (norm_nonneg _) (h1 J₀ (hmemI _ (by linarith) (by linarith)))
      set N := J₁ + 1 - J₀ with hN
      -- the sum as a sum over `range N`
      have hsum : ∑ j ∈ Icc J₀ J₁, h j = ∑ i ∈ range N, h ((J₀ : ℝ) + i) := by
        have e : Icc J₀ J₁ = Ico J₀ (J₁ + 1) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
        rw [e, Finset.sum_Ico_eq_sum_range]
        push_cast; rfl
      -- the middle integral as a sum
      have hmid : ∫ x in (J₀ : ℝ)..(J₁ + 1 : ℝ), h x =
          ∑ i ∈ range N, ∫ x in ((J₀ : ℝ) + i)..((J₀ : ℝ) + (i + 1 : ℕ)), h x := by
        rw [intervalIntegral.sum_integral_adjacent_intervals (a := fun i : ℕ => (J₀ : ℝ) + i)]
        · simp only [Nat.cast_zero, add_zero]
          congr 1
          rw [hN]; push_cast [Nat.cast_sub hJ]; ring
        · intro k hk
          apply hii
          · exact hmemI _ (by push_cast; linarith) (by
              have : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
              have hN' : (N : ℝ) = J₁ + 1 - J₀ := by rw [hN]; push_cast [Nat.cast_sub hJ]; ring
              linarith)
          · exact hmemI _ (by push_cast; linarith) (by
              have : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
              have hN' : (N : ℝ) = J₁ + 1 - J₀ := by rw [hN]; push_cast [Nat.cast_sub hJ]; ring
              push_cast; linarith)
      have hNR : (N : ℝ) = J₁ + 1 - J₀ := by rw [hN]; push_cast [Nat.cast_sub hJ]; ring
      -- each unit step
      have hstep : ∀ i ∈ range N, ‖h ((J₀ : ℝ) + i) -
          ∫ x in ((J₀ : ℝ) + i)..((J₀ : ℝ) + (i + 1 : ℕ)), h x‖ ≤ M₁ := by
        intro i hi
        have hi' : (i : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.1 hi
        set c := (J₀ : ℝ) + i
        have hcI : Set.Icc c (c + 1) ⊆ I := by
          intro x hx; exact hmemI _ (by linarith [hx.1]) (by linarith [hx.2])
        have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := h) (a := c) (b := c + 1)
          (fun x hx => (hd x (hcI hx)).hasDerivWithinAt)
          (fun x hx => h1 x (hcI (Set.Ico_subset_Icc_self hx)))
        have e1 : ((J₀ : ℝ) + (i + 1 : ℕ)) = c + 1 := by push_cast; ring
        rw [e1]
        have e2 : h c = ∫ x in c..(c + 1), h c := by simp
        rw [e2, ← intervalIntegral.integral_sub intervalIntegrable_const
          (hii _ _ (hcI ⟨le_refl _, by linarith⟩) (hcI ⟨by linarith, le_refl _⟩))]
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := c) (b := c + 1)
          (C := M₁) (f := fun x => h c - h x) (fun x hx => by
            rw [Set.uIoc_of_le (by linarith)] at hx
            have := hmv x ⟨hx.1.le, hx.2⟩
            rw [norm_sub_rev]
            calc ‖h x - h c‖ ≤ M₁ * (x - c) := this
              _ ≤ M₁ * 1 := mul_le_mul_of_nonneg_left (by linarith [hx.2]) hM₁
              _ = M₁ := mul_one _)
        simpa using this
      -- assemble
      have hsplit : ∫ x in a..b, h x = (∫ x in a..(J₀ : ℝ), h x) +
          (∫ x in (J₀ : ℝ)..(J₁ + 1 : ℝ), h x) + ∫ x in (J₁ + 1 : ℝ)..b, h x := by
        rw [intervalIntegral.integral_add_adjacent_intervals
            (hii _ _ (hmemI _ ha (by linarith)) (hmemI _ (by linarith) (by linarith)))
            (hii _ _ (hmemI _ (by linarith) (by linarith)) (hmemI _ (by linarith) (by linarith))),
          intervalIntegral.integral_add_adjacent_intervals
            (hii _ _ (hmemI _ ha (by linarith)) (hmemI _ (by linarith) (by linarith)))
            (hii _ _ (hmemI _ (by linarith) (by linarith)) (hmemI _ (by linarith) hb'))]
      have hA : ‖∫ x in a..(J₀ : ℝ), h x‖ ≤ 2 * M₀ := by
        refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (C := M₀) fun x hx => ?_) ?_
        · rw [Set.uIoc_of_le ha'] at hx
          exact h0 x (hmemI _ (by linarith [hx.1]) (by linarith [hx.2]))
        · rw [abs_of_nonneg (by linarith)]; nlinarith
      have hB : ‖∫ x in (J₁ + 1 : ℝ)..b, h x‖ ≤ M₀ := by
        refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (C := M₀) fun x hx => ?_) ?_
        · have hx' := Set.uIoc_subset_uIcc hx
          rw [Set.mem_uIcc] at hx'
          rcases hx' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
          · exact h0 x (hmemI _ (by linarith) (by linarith))
          · exact h0 x (hmemI _ (by linarith) (by linarith))
        · have : |b - (J₁ + 1)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
          nlinarith
      rw [hsplit, hsum, hmid]
      have e : ∑ i ∈ range N, h ((J₀ : ℝ) + i) - ((∫ x in a..(J₀ : ℝ), h x) +
          (∑ i ∈ range N, ∫ x in ((J₀ : ℝ) + i)..((J₀ : ℝ) + (i + 1 : ℕ)), h x) +
            ∫ x in (J₁ + 1 : ℝ)..b, h x) =
          (∑ i ∈ range N, (h ((J₀ : ℝ) + i) -
            ∫ x in ((J₀ : ℝ) + i)..((J₀ : ℝ) + (i + 1 : ℕ)), h x)) -
            (∫ x in a..(J₀ : ℝ), h x) - ∫ x in (J₁ + 1 : ℝ)..b, h x := by
        rw [Finset.sum_sub_distrib]; ring
      rw [e]
      have hs : ‖∑ i ∈ range N, (h ((J₀ : ℝ) + i) -
          ∫ x in ((J₀ : ℝ) + i)..((J₀ : ℝ) + (i + 1 : ℕ)), h x)‖ ≤ N * M₁ := by
        refine le_trans (norm_sum_le _ _) ?_
        refine le_trans (Finset.sum_le_sum hstep) ?_
        simp
      calc ‖(∑ i ∈ range N, (h ((J₀ : ℝ) + i) -
            ∫ x in ((J₀ : ℝ) + i)..((J₀ : ℝ) + (i + 1 : ℕ)), h x)) -
            (∫ x in a..(J₀ : ℝ), h x) - ∫ x in (J₁ + 1 : ℝ)..b, h x‖
          ≤ ‖∑ i ∈ range N, (h ((J₀ : ℝ) + i) -
            ∫ x in ((J₀ : ℝ) + i)..((J₀ : ℝ) + (i + 1 : ℕ)), h x)‖ +
            ‖∫ x in a..(J₀ : ℝ), h x‖ + ‖∫ x in (J₁ + 1 : ℝ)..b, h x‖ := by
            refine le_trans (norm_sub_le _ _) ?_
            exact add_le_add (norm_sub_le _ _) le_rfl
        _ ≤ N * M₁ + 2 * M₀ + M₀ := by linarith
        _ = 3 * M₀ + (N : ℝ) * M₁ := by ring

    /- ### Rearranging `S♯₄(a/q + β)` -/
  have S4sharp_eq_sum_m (ε : ℝ) {X : ℕ} (hX : 1 ≤ X) (H α : ℝ) : S4sharp ε X H α = ∑ m ∈ Icc 1 ⌊R4 ε X ^ 6⌋₊,
      ∑ n ∈ (Icc X (X + ⌊H⌋₊)).filter (fun n => m ∣ n),
        (Pm (R4 ε X) m (Real.log n) : ℂ) * eC (n * α) := by
    have hR : 0 ≤ R4 ε X ^ 6 := by unfold R4; positivity
    unfold S4sharp d4sharp
    push_cast
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm']
    intro n m
    simp only [Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hn1, hn2⟩, ⟨hmn, hn0⟩, hmR⟩
      have hm0 : m ≠ 0 := fun h => by subst h; simp at hmn; omega
      exact ⟨⟨⟨by omega, hn2⟩, hmn⟩, by omega, Nat.le_floor hmR⟩
    · rintro ⟨⟨⟨hn1, hn2⟩, hmn⟩, hm1, hmR⟩
      exact ⟨⟨hn1, hn2⟩, ⟨hmn, by omega⟩, (Nat.le_floor_iff hR).1 hmR⟩
  /- The `j` range: `X ≤ m(qj + c) ≤ Y`. -/
  let Jset := fun (X Y m q c : ℕ) =>
    (range (Y + 1)).filter (fun j => X ≤ m * (q * j + c) ∧ m * (q * j + c) ≤ Y)
  have sum_dvd_eq_sum_c_j {X Y m q : ℕ} (hm : 1 ≤ m) (hq : 1 ≤ q) (G : ℕ → ℂ) : ∑ n ∈ (Icc X Y).filter (fun n => m ∣ n), G n =
      ∑ c ∈ range q, ∑ j ∈ Jset X Y m q c, G (m * (q * j + c)) := by
    have hm0 : 0 < m := by omega
    have hq0 : 0 < q := by omega
    have e : ∑ c ∈ range q, ∑ j ∈ Jset X Y m q c, G (m * (q * j + c)) =
        ∑ p ∈ (range q ×ˢ range (Y + 1)).filter
          (fun p => X ≤ m * (q * p.2 + p.1) ∧ m * (q * p.2 + p.1) ≤ Y),
          G (m * (q * p.2 + p.1)) := by
      rw [Finset.sum_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun c _ => ?_
      unfold Jset; rw [Finset.sum_filter]
    rw [e]
    symm
    apply Finset.sum_nbij' (fun p => m * (q * p.2 + p.1)) (fun n => ((n / m) % q, (n / m) / q))
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_Icc,
        Finset.mem_coe] at hp ⊢
      exact ⟨⟨hp.2.1, hp.2.2⟩, Dvd.intro _ rfl⟩
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_Icc,
        Finset.mem_coe] at hn ⊢
      have h1 : m * (n / m) = n := Nat.mul_div_cancel' hn.2
      have h2 : q * (n / m / q) + n / m % q = n / m := Nat.div_add_mod _ _
      rw [h2, h1]
      refine ⟨⟨Nat.mod_lt _ hq0, ?_⟩, hn.1.1, hn.1.2⟩
      have : n / m / q ≤ n := le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)
      omega
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_coe] at hp
      have h1 : m * (q * p.2 + p.1) / m = q * p.2 + p.1 := Nat.mul_div_cancel_left _ hm0
      simp only [h1]
      have h2 : (q * p.2 + p.1) % q = p.1 := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp.1.1]
      have h3 : (q * p.2 + p.1) / q = p.2 := by
        rw [Nat.add_comm, Nat.add_mul_div_left _ _ hq0, Nat.div_eq_of_lt hp.1.1, zero_add]
      rw [h2, h3]
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_coe] at hn
      have h1 : m * (n / m) = n := Nat.mul_div_cancel' hn.2
      have h2 : q * (n / m / q) + n / m % q = n / m := Nat.div_add_mod _ _
      simp only [h2, h1]
    · intro p _; rfl
  have Jset_eq {X Y m q c : ℕ} (hm : 1 ≤ m) (hq : 1 ≤ q) (hXY : X ≤ Y) (ha : 0 ≤ (((X : ℝ) / m - c) / q)) : Jset X Y m q c = Icc ⌈((X : ℝ) / m - c) / q⌉₊ ⌊((Y : ℝ) / m - c) / q⌋₊ := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hXYR : (X : ℝ) ≤ Y := by exact_mod_cast hXY
    have hb : 0 ≤ ((Y : ℝ) / m - c) / q := by
      refine le_trans ha ?_
      apply div_le_div_of_nonneg_right _ hqR.le
      have := div_le_div_of_nonneg_right hXYR hmR.le
      linarith
    ext j
    simp only [Jset, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    have k1 : X ≤ m * (q * j + c) ↔ ((X : ℝ) / m - c) / q ≤ j := by
      rw [div_le_iff₀ hqR, sub_le_iff_le_add, div_le_iff₀ hmR]
      constructor
      · intro h; have : (X : ℝ) ≤ ((m * (q * j + c) : ℕ) : ℝ) := by exact_mod_cast h
        push_cast at this; linarith
      · intro h; have : (X : ℝ) ≤ ((m * (q * j + c) : ℕ) : ℝ) := by push_cast; linarith
        exact_mod_cast this
    have k2 : m * (q * j + c) ≤ Y ↔ (j : ℝ) ≤ ((Y : ℝ) / m - c) / q := by
      rw [le_div_iff₀ hqR, le_sub_iff_add_le, le_div_iff₀ hmR]
      constructor
      · intro h; have : ((m * (q * j + c) : ℕ) : ℝ) ≤ Y := by exact_mod_cast h
        push_cast at this; linarith
      · intro h; have : ((m * (q * j + c) : ℕ) : ℝ) ≤ Y := by push_cast; linarith
        exact_mod_cast this
    rw [k1, k2, Nat.ceil_le, Nat.le_floor_iff hb]
    constructor
    · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h1, h2⟩
      have : m * (q * j + c) ≤ Y := k2.2 h2
      have : j ≤ q * j := Nat.le_mul_of_pos_left j (by omega)
      have : q * j ≤ m * (q * j + c) := by nlinarith
      omega
  /- `F_m(u) = P_m(log u) e(uβ)`. -/
  let Fm := fun (R : ℝ) (m : ℕ) (β u : ℝ) =>
    (Pm R m (Real.log u) : ℂ) * eC (u * β)
  /- Its derivative for `u ≠ 0`. -/
  let Fmd := fun (R : ℝ) (m : ℕ) (β u : ℝ) =>
    ((Pmd R m (Real.log u) * u⁻¹ : ℝ) : ℂ) * eC (u * β) +
      (Pm R m (Real.log u) : ℂ) * ((2 * π * Complex.I * β) * eC (u * β))
  have hasDerivAt_Fm (R : ℝ) (m : ℕ) (β : ℝ) {u : ℝ} (hu : u ≠ 0) : HasDerivAt (Fm R m β) (Fmd R m β u) u := by
    have h1 : HasDerivAt (fun u => Pm R m (Real.log u)) (Pmd R m (Real.log u) * u⁻¹) u :=
      (hasDerivAt_Pm R m (Real.log u)).comp u (Real.hasDerivAt_log hu)
    have h2 : HasDerivAt (fun u : ℝ => eC (u * β)) ((2 * π * Complex.I * β) * eC (u * β)) u := by
      have h3 : HasDerivAt (fun u : ℝ => (2 * π * Complex.I * β) * (u : ℂ))
          ((2 * π * Complex.I * β) * 1) u :=
        ((hasDerivAt_id u).ofReal_comp).const_mul _
      have h4 := h3.cexp
      have e : (fun u : ℝ => eC (u * β)) =
          fun u : ℝ => Complex.exp ((2 * π * Complex.I * β) * (u : ℂ)) := by
        funext u; unfold eC; congr 1; push_cast; ring
      rw [e]
      convert h4 using 1
      rw [mul_one, mul_comm]
      unfold eC; congr 2; push_cast; ring
    exact h1.ofReal_comp.mul h2
  have norm_Fm_le (R : ℝ) (m : ℕ) (β u : ℝ) : ‖Fm R m β u‖ = |Pm R m (Real.log u)| := by
    unfold Fm; rw [norm_mul, norm_eC, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have norm_Fmd_le (R : ℝ) (m : ℕ) (β : ℝ) {u : ℝ} (hu : 0 < u) : ‖Fmd R m β u‖ ≤ |Pmd R m (Real.log u)| / u + 2 * π * |β| * |Pm R m (Real.log u)| := by
    unfold Fmd
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_eC, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_inv, abs_of_pos hu, norm_mul, norm_mul, norm_eC, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    have : ‖(2 * π * Complex.I * β : ℂ)‖ = 2 * π * |β| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
      simp [abs_of_pos Real.pi_pos]
    rw [this, div_eq_mul_inv]
    nlinarith [abs_nonneg (Pm R m (Real.log u)), abs_nonneg β, Real.pi_pos]
  /- The comparison for one `m` and one residue `c`: the sum over the progression
  `n = m(qj + c)` in `[X, X+H]` against `(1/(mq)) ∫_X^{X+H} P_m(log u) e(uβ) du`. -/
  have mc_estimate {X : ℕ} {H : ℝ} {m q c : ℕ} (hm : 1 ≤ m) (hq : 1 ≤ q) (hc : c < q) (hX : 4 * (m * q : ℝ) ≤ X) (hH : 0 ≤ H) (hHX : H ≤ X) {R β B₀ B₁ : ℝ} (hB₀ : ∀ u ∈ Set.Icc ((X : ℝ) / 2) (3 * X), |Pm R m (Real.log u)| ≤ B₀) (hB₁ : ∀ u ∈ Set.Icc ((X : ℝ) / 2) (3 * X), |Pmd R m (Real.log u)| ≤ B₁) : ‖∑ j ∈ Jset X (X + ⌊H⌋₊) m q c, Fm R m β ((m * (q * j + c) : ℕ) : ℝ) -
        (1 / ((m : ℂ) * q)) * ∫ u in (X : ℝ)..(X + H), Fm R m β u‖ ≤
      3 * B₀ + (H + m * q) * (2 * B₁ / X + 2 * π * |β| * B₀) := by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hcR : (c : ℝ) + 1 ≤ q := by exact_mod_cast hc
    have hmq : (1 : ℝ) ≤ m * q := one_le_mul_of_one_le_of_one_le hmR hqR
    have hXR : (4 : ℝ) ≤ X := by nlinarith
    have hXp : (0 : ℝ) < X := by linarith
    set d : ℝ := m * q with hd
    have hdp : 0 < d := by linarith
    set a' : ℝ := ((X : ℝ) / m - c) / q with ha'
    set b : ℝ := (((X : ℝ) + H) / m - c) / q with hb
    set b'' : ℝ := (((X + ⌊H⌋₊ : ℕ) : ℝ) / m - c) / q with hb''
    have hfl : (⌊H⌋₊ : ℝ) ≤ H := Nat.floor_le hH
    have hfl' : H < ⌊H⌋₊ + 1 := Nat.lt_floor_add_one H
    -- the affine change of variables `u = d t + m c`
    have hu_a : d * a' + m * c = X := by rw [hd, ha']; field_simp; ring
    have hu_b : d * b + m * c = X + H := by rw [hd, hb]; field_simp; ring
    have ha0 : 0 ≤ a' := by
      rw [ha']; apply div_nonneg _ (by linarith)
      rw [sub_nonneg, le_div_iff₀ (by linarith)]; nlinarith
    have hab : b - a' = H / d := by rw [hb, ha', hd]; field_simp; ring
    have hb''b : b'' ≤ b := by
      rw [hb'', hb]; apply div_le_div_of_nonneg_right _ (by linarith)
      push_cast; have := div_le_div_of_nonneg_right (by linarith : (X : ℝ) + ⌊H⌋₊ ≤ X + H)
        (by linarith : (0 : ℝ) ≤ m)
      linarith
    have hbb'' : b ≤ b'' + 1 := by
      have : b - b'' = (H - ⌊H⌋₊) / d := by rw [hb, hb'', hd]; push_cast; field_simp; ring
      have : (H - ⌊H⌋₊) / d ≤ 1 := by rw [div_le_one hdp]; linarith
      linarith
    have hab'' : a' ≤ b'' := by
      rw [ha', hb'']; apply div_le_div_of_nonneg_right _ (by linarith)
      push_cast; have := div_le_div_of_nonneg_right (by linarith : (X : ℝ) ≤ X + ⌊H⌋₊)
        (by linarith : (0 : ℝ) ≤ m)
      linarith
    rw [Jset_eq hm hq (by omega) ha0]
    set J₀ := ⌈a'⌉₊
    set J₁ := ⌊b''⌋₊
    have hb''0 : 0 ≤ b'' := le_trans ha0 hab''
    have hJ₀a : a' ≤ J₀ := Nat.le_ceil a'
    have hJ₀a' : (J₀ : ℝ) < a' + 1 := Nat.ceil_lt_add_one ha0
    have hJ₁b : (J₁ : ℝ) ≤ b'' := Nat.floor_le hb''0
    have hJ₁b' : b'' < J₁ + 1 := Nat.lt_floor_add_one b''
    have hJ : J₀ ≤ J₁ + 1 := le_trans (Nat.ceil_le_ceil hab'') (Nat.ceil_le_floor_add_one b'')
    -- the function in `t`
    set h : ℝ → ℂ := fun t => Fm R m β (d * t + m * c) with hh
    have hsum : ∑ j ∈ Icc J₀ J₁, Fm R m β ((m * (q * j + c) : ℕ) : ℝ) = ∑ j ∈ Icc J₀ J₁, h j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hh, hd]; congr 1; push_cast; ring
    have hint : (1 / ((m : ℂ) * q)) * ∫ u in (X : ℝ)..(X + H), Fm R m β u =
        ∫ t in a'..b, h t := by
      simp only [hh]
      rw [intervalIntegral.integral_comp_mul_add (Fm R m β) hdp.ne' ((m : ℝ) * c), hu_a, hu_b]
      rw [Complex.real_smul, hd]; push_cast; field_simp
    rw [hsum, hint]
    -- range of `u`
    have hrange : ∀ t ∈ Set.Icc ((J₀ : ℝ) - 2) (J₁ + 2),
        d * t + m * c ∈ Set.Icc ((X : ℝ) / 2) (3 * X) := by
      intro t ht
      constructor
      · have : (J₀ : ℝ) - 2 ≥ a' - 2 := by linarith
        have h1 : d * t + m * c ≥ d * (a' - 2) + m * c := by nlinarith [ht.1]
        nlinarith
      · have : (J₁ : ℝ) + 2 ≤ b + 2 := by linarith
        have h1 : d * t + m * c ≤ d * (b + 2) + m * c := by nlinarith [ht.2]
        nlinarith
    have hB₀0 : 0 ≤ B₀ := le_trans (abs_nonneg _) (hB₀ X ⟨by linarith, by linarith⟩)
    have hB₁0 : 0 ≤ B₁ := le_trans (abs_nonneg _) (hB₁ X ⟨by linarith, by linarith⟩)
    set M₁ : ℝ := d * (2 * B₁ / X + 2 * π * |β| * B₀) with hM₁
    have hM₁0 : 0 ≤ M₁ := by
      have : 0 ≤ 2 * B₁ / X := by positivity
      have : 0 ≤ 2 * π * |β| * B₀ := by have := Real.pi_pos; positivity
      rw [hM₁]; positivity
    have hderiv : ∀ t ∈ Set.Icc ((J₀ : ℝ) - 2) (J₁ + 2),
        HasDerivAt h ((d : ℂ) * Fmd R m β (d * t + m * c)) t := by
      intro t ht
      have hu := hrange t ht
      have hu0 : d * t + m * c ≠ 0 := by have := hu.1; linarith
      have hin : HasDerivAt (fun t : ℝ => d * t + m * c) d t := by
        simpa using ((hasDerivAt_id t).const_mul d).add_const ((m : ℝ) * c)
      have h1 := (hasDerivAt_Fm R m β hu0).scomp t hin
      have h2 : HasDerivAt h (d • Fmd R m β (d * t + m * c)) t := h1
      rwa [Complex.real_smul] at h2
    have hbd0 : ∀ t ∈ Set.Icc ((J₀ : ℝ) - 2) (J₁ + 2), ‖h t‖ ≤ B₀ := by
      intro t ht
      simp only [hh]; rw [norm_Fm_le]; exact hB₀ _ (hrange t ht)
    have hbd1 : ∀ t ∈ Set.Icc ((J₀ : ℝ) - 2) (J₁ + 2),
        ‖(d : ℂ) * Fmd R m β (d * t + m * c)‖ ≤ M₁ := by
      intro t ht
      have hu := hrange t ht
      have hup : 0 < d * t + m * c := by have := hu.1; linarith
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdp, hM₁]
      apply mul_le_mul_of_nonneg_left _ hdp.le
      refine le_trans (norm_Fmd_le R m β hup) ?_
      have e1 : |Pmd R m (Real.log (d * t + m * c))| / (d * t + m * c) ≤ 2 * B₁ / X := by
        have s1 : |Pmd R m (Real.log (d * t + m * c))| / (d * t + m * c) ≤ B₁ / (d * t + m * c) :=
          div_le_div_of_nonneg_right (hB₁ _ hu) hup.le
        have s2 : B₁ / (d * t + m * c) ≤ B₁ / ((X : ℝ) / 2) :=
          div_le_div_of_nonneg_left hB₁0 (by linarith) hu.1
        have s3 : B₁ / ((X : ℝ) / 2) = 2 * B₁ / X := by field_simp
        linarith
      have e2 : 2 * π * |β| * |Pm R m (Real.log (d * t + m * c))| ≤ 2 * π * |β| * B₀ := by
        apply mul_le_mul_of_nonneg_left (hB₀ _ hu)
        have := Real.pi_pos; positivity
      linarith
    have key := sum_Icc_sub_integral_le hJ (by linarith) hJ₀a (le_trans hJ₁b hb''b)
      (by linarith [hbb'', hJ₁b']) hderiv hbd0 hbd1
    refine le_trans key ?_
    have hN : ((J₁ + 1 - J₀ : ℕ) : ℝ) ≤ H / d + 1 := by
      rw [Nat.cast_sub hJ]; push_cast
      linarith
    have : ((J₁ + 1 - J₀ : ℕ) : ℝ) * M₁ ≤ (H / d + 1) * M₁ := mul_le_mul_of_nonneg_right hN hM₁0
    have e : (H / d + 1) * M₁ = (H + m * q) * (2 * B₁ / X + 2 * π * |β| * B₀) := by
      rw [hM₁, hd]; field_simp
    linarith
  /- The exact identity behind display (2.5): the difference between `S♯₄(a/q + β)` and the main
  term `mainArc` is a sum over `m` and over residues `c` of progression sums minus integrals. -/
  have S4sharp_sub_mainArc (ε : ℝ) {X : ℕ} (hX : 1 ≤ X) (H : ℝ) {q : ℕ} (hq : 1 ≤ q) (a : ℕ) (β : ℝ) : S4sharp ε X H ((a : ℝ) / q + β) - mainArc ε X H q a β =
      ∑ m ∈ Icc 1 ⌊R4 ε X ^ 6⌋₊, ∑ c ∈ range q, eC ((a : ℝ) * m * c / q) *
        (∑ j ∈ Jset X (X + ⌊H⌋₊) m q c, Fm (R4 ε X) m β ((m * (q * j + c) : ℕ) : ℝ) -
          (1 / ((m : ℂ) * q)) * ∫ u in (X : ℝ)..(X + H), Fm (R4 ε X) m β u) := by
    have hqR : (q : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    rw [S4sharp_eq_sum_m ε hX]
    unfold mainArc
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
    rw [sum_dvd_eq_sum_c_j hm1 hq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hj : ∀ j : ℕ, (Pm (R4 ε X) m (Real.log ((m * (q * j + c) : ℕ) : ℝ)) : ℂ) *
        eC (((m * (q * j + c) : ℕ) : ℝ) * ((a : ℝ) / q + β)) =
        eC ((a : ℝ) * m * c / q) * Fm (R4 ε X) m β ((m * (q * j + c) : ℕ) : ℝ) := by
      intro j
      unfold Fm
      have e : ((m * (q * j + c) : ℕ) : ℝ) * ((a : ℝ) / q + β) =
          ((a * m * j : ℕ) : ℤ) + ((a : ℝ) * m * c / q + ((m * (q * j + c) : ℕ) : ℝ) * β) := by
        push_cast; field_simp; ring
      rw [e, eC_add, eC_int, one_mul, eC_add]; ring
    simp_rw [hj]
    rw [← Finset.mul_sum]
    unfold Fm
    ring
  have eventually_p23 {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2) : ∀ᶠ x : ℝ in atTop, 3 ≤ x ∧ 3 ≤ x ^ (ε / 40) ∧ 4 ≤ x ^ (1 - 23 * ε / 20) := by
    have h1 := (tendsto_rpow_atTop (by linarith : (0 : ℝ) < ε / 40)).eventually_ge_atTop 3
    have h2 := (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - 23 * ε / 20)).eventually_ge_atTop 4
    filter_upwards [eventually_ge_atTop 3, h1, h2] with x hx1 hx2 hx3
    exact ⟨hx1, hx2, hx3⟩
  /- LEAF: Kim, Proposition 2.3, display (2.5), page 9: for `X^{3/5+ε} ≤ H ≤ X^{1-ε}`,
  `∑_{n ∈ [X,X+H]} d♯₄(n) e(an/q) e(nβ)` equals the main term `mainArc` up to
  `O(q X^{2ε} (1 + H|β|))`. The paper states it for every `q` and `a`; it is encoded here, more
  weakly, for `1 ≤ q ≤ Q` and `(a, q) = 1`, the only case used, with `ε` small and with the
  constant `C` and threshold `X₀` explicit. -/
  have prop_2_3 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ C : ℝ, ∃ X₀ : ℕ,
    ∀ X : ℕ, X₀ ≤ X → ∀ H : ℝ,
      (X : ℝ) ^ ((3 : ℝ) / 5 + ε) ≤ H → H ≤ (X : ℝ) ^ (1 - ε) →
      ∀ q a : ℕ, 1 ≤ q → (q : ℝ) ≤ Qpar ε X → Nat.Coprime a q → ∀ β : ℝ,
        ‖S4sharp ε X H ((a : ℝ) / q + β) - mainArc ε X H q a β‖ ≤
          C * q * (X : ℝ) ^ (2 * ε) * (1 + H * |β|) := by
      refine ⟨1 / 2, by norm_num, fun ε hε hεε => ?_⟩
      set K₀ : ℝ := 80 / ε + 10 with hK₀
      have hK₀p : 0 < K₀ := by positivity
      obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.1
        (tendsto_natCast_atTop_atTop.eventually (eventually_p23 hε hεε))
      refine ⟨420 * K₀ ^ 3, X₀, fun X hX H hlo hhi q a hq hqQ _ β => ?_⟩
      obtain ⟨hX3, hR3, hX4⟩ := hX₀ X hX
      have hXp : (0 : ℝ) < X := by linarith
      have hX1 : 1 ≤ X := by exact_mod_cast (by linarith : (1 : ℝ) ≤ X)
      set R := R4 ε X with hRdef
      have hR3' : 3 ≤ R := hR3
      have hRp : 0 < R := by linarith
      have hR6 : R ^ 6 = (X : ℝ) ^ (3 * ε / 20) := by
        rw [hRdef]; unfold R4; rw [← Real.rpow_natCast, ← Real.rpow_mul hXp.le]; ring_nf
      have hR12 : R ^ 6 * R ^ 6 ≤ (X : ℝ) ^ (2 * ε) := by
        rw [hR6, ← Real.rpow_add hXp]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      have hLX : 0 < Real.log X := Real.log_pos (by linarith)
      have hlogR : Real.log R = ε / 40 * Real.log X := by
        rw [hRdef]; unfold R4; rw [Real.log_rpow hXp]
      have hK : (2 * Real.log X + 10 * Real.log R) / Real.log R = K₀ := by
        rw [hlogR, hK₀]; field_simp; ring
      set B₀ : ℝ := 15 * R ^ 6 * K₀ ^ 3 with hB₀def
      have hB₀p : 0 ≤ B₀ := by positivity
      have hbounds : ∀ (m : ℕ) u, u ∈ Set.Icc ((X : ℝ) / 2) (3 * X) →
          |Pm R m (Real.log u)| ≤ B₀ ∧ |Pmd R m (Real.log u)| ≤ 3 * B₀ := by
        intro m u hu
        have hu0 : 0 < u := by linarith [hu.1]
        have hlog : |Real.log u| ≤ 2 * Real.log X := by
          rw [abs_le]; constructor
          · have : 0 ≤ Real.log u := Real.log_nonneg (by linarith [hu.1])
            linarith
          · have : Real.log u ≤ Real.log ((X : ℝ) ^ 2) :=
              Real.log_le_log hu0 (by nlinarith [hu.2])
            rw [Real.log_pow] at this; push_cast at this; linarith
        have := Pm_bounds hR3' (by linarith) hlog m
        rw [hK] at this
        exact ⟨this.1, by rw [hB₀def]; linarith [this.2]⟩
      have hHX : H ≤ X := le_trans hhi (by
        calc (X : ℝ) ^ (1 - ε) ≤ (X : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
          _ = X := Real.rpow_one _)
      have hH0 : 0 ≤ H := le_trans (Real.rpow_nonneg hXp.le _) hlo
      have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
      -- the size of `m q`
      have hmq : ∀ m ∈ Icc 1 ⌊R ^ 6⌋₊, 4 * ((m : ℝ) * q) ≤ X ∧ (m : ℝ) * q ≤ H := by
        intro m hm
        have hm6 : (m : ℝ) ≤ R ^ 6 := by
          have := (Finset.mem_Icc.1 hm).2
          exact le_trans (by exact_mod_cast this) (Nat.floor_le (by positivity))
        have hmq' : (m : ℝ) * q ≤ (X : ℝ) ^ (23 * ε / 20) := by
          have : (X : ℝ) ^ (23 * ε / 20) = (X : ℝ) ^ (3 * ε / 20) * (X : ℝ) ^ ε := by
            rw [← Real.rpow_add hXp]; ring_nf
          rw [this, ← hR6]
          exact mul_le_mul hm6 hqQ (by linarith) (by positivity)
        constructor
        · have : (X : ℝ) = (X : ℝ) ^ (23 * ε / 20) * (X : ℝ) ^ (1 - 23 * ε / 20) := by
            rw [← Real.rpow_add hXp]; simp
          have hpos : 0 ≤ (X : ℝ) ^ (23 * ε / 20) := by positivity
          nlinarith
        · refine le_trans hmq' (le_trans ?_ hlo)
          exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      rw [S4sharp_sub_mainArc ε hX1 H hq a β]
      have hterm : ∀ m ∈ Icc 1 ⌊R ^ 6⌋₊, ∀ c ∈ range q,
          ‖eC ((a : ℝ) * m * c / q) *
            (∑ j ∈ Jset X (X + ⌊H⌋₊) m q c, Fm R m β ((m * (q * j + c) : ℕ) : ℝ) -
              (1 / ((m : ℂ) * q)) * ∫ u in (X : ℝ)..(X + H), Fm R m β u)‖ ≤
            28 * B₀ * (1 + H * |β|) := by
        intro m hm c hc
        obtain ⟨h4, hmH⟩ := hmq m hm
        rw [norm_mul, norm_eC, one_mul]
        have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
        refine le_trans (mc_estimate hm1 hq (Finset.mem_range.1 hc) h4 hH0 hHX
          (fun u hu => (hbounds m u hu).1) (fun u hu => (hbounds m u hu).2)) ?_
        have e1 : (H + m * q) * (2 * (3 * B₀) / X) ≤ 12 * B₀ := by
          rw [show (H + m * q) * (2 * (3 * B₀) / X) = (H + m * q) / X * (6 * B₀) by ring]
          have : (H + m * q) / X ≤ 2 := by rw [div_le_iff₀ hXp]; linarith
          nlinarith
        have e2 : (H + m * q) * (2 * π * |β| * B₀) ≤ 13 * (H * |β| * B₀) := by
          have hpi := Real.pi_lt_d2
          have : 0 ≤ |β| * B₀ := by positivity
          have h2 : (H + m * q) ≤ 2 * H := by linarith
          calc (H + m * q) * (2 * π * |β| * B₀) = (H + m * q) * (2 * π) * (|β| * B₀) := by ring
            _ ≤ (2 * H) * (2 * 3.15) * (|β| * B₀) := by
                apply mul_le_mul_of_nonneg_right _ this
                apply mul_le_mul h2 (by linarith) (by positivity) (by linarith)
            _ ≤ 13 * (H * |β| * B₀) := by nlinarith
        have : 0 ≤ H * |β| * B₀ := by positivity
        nlinarith
      refine le_trans (norm_sum_le _ _) ?_
      refine le_trans (Finset.sum_le_sum fun m hm => (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun c hc => hterm m hm c hc)) ?_
      simp only [Finset.sum_const, Finset.card_range, Nat.card_Icc, nsmul_eq_mul]
      have hcount : ((⌊R ^ 6⌋₊ + 1 - 1 : ℕ) : ℝ) ≤ R ^ 6 := by
        simp only [Nat.add_sub_cancel]; exact Nat.floor_le (by positivity)
      have hpos : 0 ≤ (q : ℝ) * (28 * B₀ * (1 + H * |β|)) := by positivity
      calc ((⌊R ^ 6⌋₊ + 1 - 1 : ℕ) : ℝ) * ((q : ℝ) * (28 * B₀ * (1 + H * |β|)))
          ≤ R ^ 6 * ((q : ℝ) * (28 * B₀ * (1 + H * |β|))) :=
            mul_le_mul_of_nonneg_right hcount hpos
        _ = 420 * K₀ ^ 3 * q * (R ^ 6 * R ^ 6) * (1 + H * |β|) := by rw [hB₀def]; ring
        _ ≤ 420 * K₀ ^ 3 * q * (X : ℝ) ^ (2 * ε) * (1 + H * |β|) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_left hR12 (by positivity)

    /- ### Proposition 2.4 and the major arc leaf without cited inputs beyond Section 2.2 -/

    /- ### Integrating the main term over one arc -/
  have Pm_continuous (R : ℝ) (m : ℕ) : Continuous (Pm R m) := by
    unfold Pm; fun_prop
  have continuous_Pm_log_max (R : ℝ) (m : ℕ) : Continuous fun u : ℝ => Pm R m (Real.log (max u 1)) := by
    have h : Continuous fun u : ℝ => Real.log (max u 1) :=
      (continuous_id.max continuous_const).log
        (fun u => ne_of_gt (lt_of_lt_of_le one_pos (le_max_right (id u) 1)))
    exact (Pm_continuous R m).comp h
  /- For a fixed `m`, the `η` integral of the inner `u` integral against `e(-nη)` over
  `|η| ≤ β₀` gives the kernel `sin(2πβ₀(u-n))/(π(u-n))`. -/
  have inner_arc_identity (R : ℝ) (m : ℕ) {X : ℕ} (hX : 1 ≤ X) {H : ℝ} (hH : 0 ≤ H) (n : ℕ) (β₀ : ℝ) : ∫ η in (-β₀)..β₀, (∫ u in (X : ℝ)..(X + H), (Pm R m (Real.log u) : ℂ) * eC (u * η)) *
        eC (-(n * η)) =
      ((∫ u in (X : ℝ)..(X + H), Pm R m (Real.log u) *
          Real.sin (2 * π * β₀ * (u - n)) / (π * (u - n)) : ℝ) : ℂ) := by
    have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
    have hce := continuous_eC
    have hP := continuous_Pm_log_max R m
    have hmax : ∀ u ∈ Set.uIcc (X : ℝ) (X + H), Real.log u = Real.log (max u 1) := by
      intro u hu
      rw [Set.uIcc_of_le (by linarith)] at hu
      rw [max_eq_left (by linarith [hu.1])]
    -- replace `log u` by `log (max u 1)` inside
    have hJ : ∀ η : ℝ, (∫ u in (X : ℝ)..(X + H), (Pm R m (Real.log u) : ℂ) * eC (u * η)) =
        ∫ u in (X : ℝ)..(X + H), (Pm R m (Real.log (max u 1)) : ℂ) * eC (u * η) := by
      intro η
      refine intervalIntegral.integral_congr fun u hu => ?_
      simp only [hmax u hu]
    simp_rw [hJ]
    simp_rw [← intervalIntegral.integral_mul_const]
    rw [intervalIntegral_intervalIntegral_swap]
    swap
    · have hc : Continuous (Function.uncurry fun (η u : ℝ) =>
          (Pm R m (Real.log (max u 1)) : ℂ) * eC (u * η) * eC (-(n * η))) := by
        show Continuous fun p : ℝ × ℝ =>
          (Pm R m (Real.log (max p.2 1)) : ℂ) * eC (p.2 * p.1) * eC (-(n * p.1))
        have h1 : Continuous fun p : ℝ × ℝ => (Pm R m (Real.log (max p.2 1)) : ℂ) :=
          Complex.continuous_ofReal.comp (hP.comp continuous_snd)
        have h2 : Continuous fun p : ℝ × ℝ => eC (p.2 * p.1) :=
          hce.comp (continuous_snd.mul continuous_fst)
        have h3 : Continuous fun p : ℝ × ℝ => eC (-(n * p.1)) :=
          hce.comp ((continuous_const.mul continuous_fst).neg)
        exact (h1.mul h2).mul h3
      exact (hc.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
        (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume (n : ℝ)] with u hun hu
    have hu' : u ∈ Set.uIcc (X : ℝ) (X + H) := Set.uIoc_subset_uIcc hu
    have hne : u - n ≠ 0 := sub_ne_zero.2 hun
    have e1 : (fun η : ℝ => (Pm R m (Real.log (max u 1)) : ℂ) * eC (u * η) * eC (-(n * η))) =
        fun η : ℝ => (Pm R m (Real.log (max u 1)) : ℂ) * eC ((u - n) * η) := by
      funext η; rw [mul_assoc, ← eC_add]; congr 2; ring
    rw [e1, intervalIntegral.integral_const_mul, integral_eC_kernel hne, ← hmax u hu']
    push_cast
    ring
  have J_continuous (R : ℝ) (m : ℕ) {X : ℕ} (hX : 1 ≤ X) {H : ℝ} (hH : 0 ≤ H) : Continuous fun η : ℝ =>
      ∫ u in (X : ℝ)..(X + H), (Pm R m (Real.log u) : ℂ) * eC (u * η) := by
    have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
    have hce := continuous_eC
    have hP := continuous_Pm_log_max R m
    have hJ : (fun η : ℝ => ∫ u in (X : ℝ)..(X + H), (Pm R m (Real.log u) : ℂ) * eC (u * η)) =
        fun η => ∫ u in (X : ℝ)..(X + H), (Pm R m (Real.log (max u 1)) : ℂ) * eC (u * η) := by
      funext η
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le (by linarith)] at hu
      simp only [max_eq_left (by linarith [hu.1] : (1 : ℝ) ≤ u)]
    rw [hJ]
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    show Continuous fun p : ℝ × ℝ => (Pm R m (Real.log (max p.2 1)) : ℂ) * eC (p.2 * p.1)
    exact (Complex.continuous_ofReal.comp (hP.comp continuous_snd)).mul
      (hce.comp (continuous_snd.mul continuous_fst))
  /- Integrating the main term `mainArc` of one arc against `e(-nα)` over `|α - a/q| ≤ β₀`
  gives the summand of `mainK`. -/
  have arc_main {ε : ℝ} {X : ℕ} (hX : 1 ≤ X) {H : ℝ} (hH : 0 ≤ H) (q a n : ℕ) (β₀ : ℝ) : ∫ η in (-β₀)..β₀, mainArc ε X H q a η * eC (-(n * ((a : ℝ) / q + η))) =
      ∑ m ∈ Icc 1 ⌊R4 ε X ^ 6⌋₊, ∑ b ∈ range q,
        (1 / ((m : ℂ) * q)) * eC ((a : ℝ) * ((m : ℝ) * b - n) / q) *
          (((∫ u in (X : ℝ)..(X + H), Pm (R4 ε X) m (Real.log u) *
            Real.sin (2 * π * β₀ * (u - n)) / (π * (u - n))) : ℝ) : ℂ) := by
      have hce := continuous_eC
      have hpt : ∀ η : ℝ, mainArc ε X H q a η * eC (-(n * ((a : ℝ) / q + η))) =
          ∑ m ∈ Icc 1 ⌊R4 ε X ^ 6⌋₊, ∑ b ∈ range q,
            ((1 / ((m : ℂ) * q)) * eC ((a : ℝ) * ((m : ℝ) * b - n) / q)) *
              ((∫ u in (X : ℝ)..(X + H), (Pm (R4 ε X) m (Real.log u) : ℂ) * eC (u * η)) *
                eC (-(n * η))) := by
        intro η
        unfold mainArc
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        have e : eC (-(n * ((a : ℝ) / q + η))) =
            eC (-((a : ℝ) * n / q)) * eC (-(n * η)) := by
          rw [← eC_add]; congr 1; ring
        have e2 : eC ((a : ℝ) * ((m : ℝ) * b - n) / q) =
            eC ((a : ℝ) * m * b / q) * eC (-((a : ℝ) * n / q)) := by
          rw [← eC_add]; congr 1; ring
        rw [e, e2]; ring
      simp_rw [hpt]
      have hcont : ∀ (m : ℕ), Continuous (fun η : ℝ =>
          (∫ u in (X : ℝ)..(X + H), (Pm (R4 ε X) m (Real.log u) : ℂ) * eC (u * η)) *
            eC (-(n * η))) := by
        intro m
        have := J_continuous (R4 ε X) m hX hH
        exact this.mul (hce.comp (continuous_const.mul continuous_id).neg)
      have hint : ∀ (m : ℕ), IntervalIntegrable (fun η : ℝ =>
          (∫ u in (X : ℝ)..(X + H), (Pm (R4 ε X) m (Real.log u) : ℂ) * eC (u * η)) *
            eC (-(n * η))) volume (-β₀) β₀ := fun m => (hcont m).intervalIntegrable _ _
      rw [intervalIntegral.integral_finsetSum (f := fun (m : ℕ) (η : ℝ) => ∑ b ∈ range q,
          ((1 / ((m : ℂ) * q)) * eC ((a : ℝ) * ((m : ℝ) * b - n) / q)) *
            ((∫ u in (X : ℝ)..(X + H), (Pm (R4 ε X) m (Real.log u) : ℂ) * eC (u * η)) *
              eC (-(n * η)))) (fun m _ =>
        (continuous_finsetSum _ fun b _ => continuous_const.mul (hcont m)).intervalIntegrable _ _)]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [intervalIntegral.integral_finsetSum (f := fun (b : ℕ) (η : ℝ) =>
          ((1 / ((m : ℂ) * q)) * eC ((a : ℝ) * ((m : ℝ) * b - n) / q)) *
            ((∫ u in (X : ℝ)..(X + H), (Pm (R4 ε X) m (Real.log u) : ℂ) * eC (u * η)) *
              eC (-(n * η)))) (fun b _ => (hint m).const_mul _)]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [intervalIntegral.integral_const_mul, inner_arc_identity _ m hX hH n β₀]

    /- ### The arcs -/
  /- For `q > X^{3ε/20}` the main term of display (2.5) vanishes: by `sum_b_eC` only `m`
  divisible by `q` contribute, and there are none with `1 ≤ m ≤ X^{3ε/20} < q`. -/
  have mainArc_eq_zero {ε : ℝ} {X : ℕ} {H : ℝ} {q a : ℕ} (hq : 1 ≤ q) (hcop : Nat.Coprime a q) (hqR : ⌊R4 ε X ^ 6⌋₊ < q) (η : ℝ) : mainArc ε X H q a η = 0 := by
    unfold mainArc
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [Finset.mem_Icc] at hm
    rw [← Finset.sum_mul, ← Finset.sum_mul, sum_b_eC hq hcop m]
    have : ¬ q ∣ m := fun h => by
      have := Nat.le_of_dvd (by omega) h
      omega
    simp [this]
  /- The arc `I'_{q,r} = [r/q - β, r/q + β]` of page 3. -/
  let arc := fun (β : ℝ) (q r : ℕ) =>
    Set.Icc ((r : ℝ) / q - β) ((r : ℝ) / q + β)
  have eq_of_frac_eq {q r q' r' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hr : Nat.Coprime r q) (hr' : Nat.Coprime r' q') (h : r * q' = r' * q) : q = q' ∧ r = r' := by
    have h1 : q ∣ q' := by
      have : q ∣ r * q' := ⟨r', by rw [h]; ring⟩
      exact (Nat.Coprime.symm hr).dvd_of_dvd_mul_left this
    have h2 : q' ∣ q := by
      have : q' ∣ r' * q := ⟨r, by rw [← h]; ring⟩
      exact (Nat.Coprime.symm hr').dvd_of_dvd_mul_left this
    have hqq : q = q' := Nat.dvd_antisymm h1 h2
    subst hqq
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (by omega) h⟩
  /- Distinct major arcs are disjoint once `2 β Q² < 1`, since distinct reduced fractions with
  denominators at most `Q` are at least `1/Q²` apart. -/
  have arcs_disjoint {β Qp : ℝ} (h2 : 2 * β * Qp ^ 2 < 1) {q r q' r' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hqQ : (q : ℝ) ≤ Qp) (hq'Q : (q' : ℝ) ≤ Qp) (hr : Nat.Coprime r q) (hr' : Nat.Coprime r' q') (hne : ¬ (q = q' ∧ r = r')) : Disjoint (arc β q r) (arc β q' r') := by
    rw [Set.disjoint_left]
    intro α h1 h2'
    unfold arc at h1 h2'
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hq'R : (1 : ℝ) ≤ q' := by exact_mod_cast hq'
    have hdist : |(r : ℝ) / q - (r' : ℝ) / q'| ≤ 2 * β := by
      rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2'.1, h2'.2]
    have hint : (r * q' : ℤ) ≠ r' * q := by
      intro h
      have : r * q' = r' * q := by exact_mod_cast h
      exact hne (eq_of_frac_eq hq hq' hr hr' this)
    have hone : (1 : ℝ) ≤ |(r : ℝ) * q' - r' * q| := by
      have : (1 : ℤ) ≤ |(r * q' : ℤ) - r' * q| := Int.one_le_abs (sub_ne_zero.2 hint)
      exact_mod_cast this
    have heq : (r : ℝ) / q - (r' : ℝ) / q' = ((r : ℝ) * q' - r' * q) / (q * q') := by
      field_simp
    rw [heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * q')] at hdist
    have hqq : (q : ℝ) * q' ≤ Qp ^ 2 := by nlinarith
    have : 1 ≤ 2 * β * (q * q') := by
      rw [div_le_iff₀ (by positivity)] at hdist; linarith
    have hβ : 0 ≤ β := by
      by_contra hb; push_neg at hb
      have : 2 * β * (q * q') < 0 := by
        have : (0 : ℝ) < q * q' := by positivity
        nlinarith
      linarith
    nlinarith
  /- Splitting a set integral over the major arcs into the arcs, by disjointness. -/
  have setIntegral_arcs {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (ε : ℝ) (X : ℕ) (H : ℝ) {A : Set ℝ} (hA : MeasurableSet A) {a b : ℝ} (hAs : A ⊆ Set.Icc a b) (hdisj : 2 * betaDelta ε X H * Qpar ε X ^ 2 < 1) (F : ℝ → E) (hF : Continuous F) : ∫ α in A ∩ majorArcs ε X H, F α =
      ∑ q ∈ Icc 1 ⌊Qpar ε X⌋₊, ∑ r ∈ (Icc 1 q).filter (fun r => Nat.Coprime r q),
        ∫ α in A ∩ arc (betaDelta ε X H) q r, F α := by
    set β := betaDelta ε X H
    have hQ : ∀ q ∈ Icc 1 ⌊Qpar ε X⌋₊, 1 ≤ q ∧ (q : ℝ) ≤ Qpar ε X := by
      intro q hq
      rw [Finset.mem_Icc] at hq
      refine ⟨hq.1, ?_⟩
      have hpos : 0 ≤ Qpar ε X := by unfold Qpar; positivity
      exact le_trans (by exact_mod_cast hq.2) (Nat.floor_le hpos)
    have hR : ∀ q, ∀ r ∈ (Icc 1 q).filter (fun r => Nat.Coprime r q), Nat.Coprime r q := by
      intro q r hr; exact (Finset.mem_filter.1 hr).2
    have hset : A ∩ majorArcs ε X H = ⋃ q ∈ Icc 1 ⌊Qpar ε X⌋₊,
        ⋃ r ∈ (Icc 1 q).filter (fun r => Nat.Coprime r q), A ∩ arc β q r := by
      unfold majorArcs arc
      simp only [Set.inter_iUnion₂]
      rfl
    have hint : ∀ S : Set ℝ, S ⊆ A → IntegrableOn F S :=
      fun S hS => (hF.integrableOn_Icc).mono_set (hS.trans hAs)
    have hmeas : ∀ q r, MeasurableSet (A ∩ arc β q r) := fun q r => hA.inter measurableSet_Icc
    rw [hset, integral_biUnion_finset]
    · refine Finset.sum_congr rfl fun q hq => ?_
      rw [integral_biUnion_finset]
      · exact fun r _ => hmeas q r
      · intro r hr r' hr' hne
        exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right
          (arcs_disjoint hdisj (hQ q hq).1 (hQ q hq).1 (hQ q hq).2 (hQ q hq).2 (hR q r hr)
            (hR q r' hr') (fun h => hne h.2))
      · exact fun r _ => hint _ Set.inter_subset_left
    · exact fun q _ => Finset.measurableSet_biUnion _ fun r _ => hmeas q r
    · intro q hq q' hq' hne
      simp only [Function.onFun]
      rw [Set.disjoint_iUnion₂_left]
      intro r hr
      rw [Set.disjoint_iUnion₂_right]
      intro r' hr'
      exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right
        (arcs_disjoint hdisj (hQ q hq).1 (hQ q' hq').1 (hQ q hq).2 (hQ q' hq').2 (hR q r hr)
          (hR q' r' hr') (fun h => hne h.1))
    · intro q _
      exact hint _ (Set.iUnion₂_subset fun r _ => Set.inter_subset_left)
  /- The main term of one arc, integrated against `e(-nα)` over the part of the arc inside
  `(1/Q, 1+1/Q]`: it is the whole arc when `q ≤ X^{3ε/20}`, and the main term vanishes otherwise. -/
  have arc_main_inter {ε : ℝ} {X : ℕ} (hX : 1 ≤ X) {H : ℝ} (hH : 0 ≤ H) (hQp : 0 < Qpar ε X) (hβ0 : 0 ≤ betaDelta ε X H) (hβQ : betaDelta ε X H < 1 / Qpar ε X) (hR6 : (⌊R4 ε X ^ 6⌋₊ : ℝ) * 2 ≤ Qpar ε X) {q r : ℕ} (hq : 1 ≤ q) (hr1 : 1 ≤ r) (hrq : r ≤ q) (hcop : Nat.Coprime r q) (n : ℕ) : ∫ α in arcRange ε X ∩ arc (betaDelta ε X H) q r,
        mainArc ε X H q r (α - r / q) * eC (-(n * α)) =
      ∑ m ∈ Icc 1 ⌊R4 ε X ^ 6⌋₊, ∑ b ∈ range q,
        (1 / ((m : ℂ) * q)) * eC ((r : ℝ) * ((m : ℝ) * b - n) / q) *
          (((∫ u in (X : ℝ)..(X + H), Pm (R4 ε X) m (Real.log u) *
            Real.sin (2 * π * betaDelta ε X H * (u - n)) / (π * (u - n))) : ℝ) : ℂ) := by
    set β := betaDelta ε X H
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hfull : ∫ α in arc β q r, mainArc ε X H q r (α - r / q) * eC (-(n * α)) =
        ∫ η in (-β)..β, mainArc ε X H q r η * eC (-(n * ((r : ℝ) / q + η))) := by
      unfold arc
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
      have := intervalIntegral.integral_comp_add_left
        (fun α => mainArc ε X H q r (α - r / q) * eC (-(n * α))) ((r : ℝ) / q) (a := -β) (b := β)
      simp only [add_sub_cancel_left] at this
      rw [this]; congr 1 <;> ring
    rw [← arc_main hX hH q r n β, ← hfull]
    by_cases hsmall : q ≤ ⌊R4 ε X ^ 6⌋₊
    · have hsub : arc β q r ⊆ arcRange ε X := by
        intro α hα
        unfold arc at hα
        unfold arcRange
        have h1 : (1 : ℝ) / q ≤ r / q := div_le_div_of_nonneg_right (by exact_mod_cast hr1) (by linarith)
        have h2 : (r : ℝ) / q ≤ 1 := (div_le_one (by linarith)).2 (by exact_mod_cast hrq)
        have h3 : 2 / Qpar ε X ≤ 1 / q := by
          rw [div_le_div_iff₀ hQp (by linarith)]
          have : (q : ℝ) ≤ ⌊R4 ε X ^ 6⌋₊ := by exact_mod_cast hsmall
          linarith
        constructor
        · have : 1 / Qpar ε X + β < 2 / Qpar ε X := by
            have e : 2 / Qpar ε X = 1 / Qpar ε X + 1 / Qpar ε X := by ring
            linarith
          linarith [hα.1]
        · linarith [hα.2]
      rw [Set.inter_eq_right.2 hsub]
    · push_neg at hsmall
      have h0 : ∀ α, mainArc ε X H q r (α - r / q) * eC (-(n * α)) = 0 := by
        intro α; rw [mainArc_eq_zero hq hcop hsmall, zero_mul]
      simp only [h0, integral_zero]
  have mainArc_continuous {ε : ℝ} {X : ℕ} (hX : 1 ≤ X) {H : ℝ} (hH : 0 ≤ H) (q a : ℕ) : Continuous (mainArc ε X H q a) := by
    unfold mainArc
    exact continuous_finsetSum _ fun m _ => continuous_finsetSum _ fun b _ =>
      continuous_const.mul (J_continuous _ m hX hH)
  /- The summand of `mainK` for the arc at `r/q`. -/
  let mainKterm := fun (ε : ℝ) (X : ℕ) (H : ℝ) (q r n : ℕ) =>
    ∑ m ∈ Icc 1 ⌊R4 ε X ^ 6⌋₊, ∑ b ∈ range q,
      (1 / ((m : ℂ) * q)) * eC ((r : ℝ) * ((m : ℝ) * b - n) / q) *
        (((∫ u in (X : ℝ)..(X + H), Pm (R4 ε X) m (Real.log u) *
          Real.sin (2 * π * betaDelta ε X H * (u - n)) / (π * (u - n))) : ℝ) : ℂ)
  have mainK_eq (ε : ℝ) (X : ℕ) (H : ℝ) (n : ℕ) : mainK ε X H n = ∑ q ∈ Icc 1 ⌊Qpar ε X⌋₊, ∑ r ∈ (Icc 1 q).filter (fun r => Nat.Coprime r q),
      mainKterm ε X H q r n := by
    rfl
  /- The error of display (2.5) on one arc. -/
  let errArc := fun (ε : ℝ) (X : ℕ) (H : ℝ) (q r : ℕ) (α : ℝ) =>
    S4sharp ε X H α - mainArc ε X H q r (α - r / q)
  /- The difference between the major arc contribution and the main term of display (2.6) is the
  sum over arcs of the integrals of the error of display (2.5). -/
  have major_sub_main {ε : ℝ} {X : ℕ} (hX : 1 ≤ X) {H : ℝ} (hH : 0 ≤ H) (hQp : 0 < Qpar ε X) (hβ0 : 0 ≤ betaDelta ε X H) (hβQ : betaDelta ε X H < 1 / Qpar ε X) (hR6 : (⌊R4 ε X ^ 6⌋₊ : ℝ) * 2 ≤ Qpar ε X) (hdisj : 2 * betaDelta ε X H * Qpar ε X ^ 2 < 1) (S : Finset ℕ) : (∑ n ∈ S, majorInt ε X H n) - ∑ n ∈ S, mainK ε X H n =
      ∑ q ∈ Icc 1 ⌊Qpar ε X⌋₊, ∑ r ∈ (Icc 1 q).filter (fun r => Nat.Coprime r q),
        ∫ α in arcRange ε X ∩ arc (betaDelta ε X H) q r,
          errArc ε X H q r α * ∑ n ∈ S, eC (-(n * α)) := by
    have hce := continuous_eC
    have hsplit : ∀ n, majorInt ε X H n = ∑ q ∈ Icc 1 ⌊Qpar ε X⌋₊,
        ∑ r ∈ (Icc 1 q).filter (fun r => Nat.Coprime r q),
          ∫ α in arcRange ε X ∩ arc (betaDelta ε X H) q r, S4sharp ε X H α * eC (-(n * α)) := by
      intro n
      unfold majorInt
      exact setIntegral_arcs ε X H measurableSet_Ioc Set.Ioc_subset_Icc_self hdisj _
        (S4sharp_continuous ε X H n)
    have hpiece : ∀ n : ℕ, ∀ q ∈ Icc 1 ⌊Qpar ε X⌋₊, ∀ r ∈ (Icc 1 q).filter (fun r => Nat.Coprime r q),
        ∫ α in arcRange ε X ∩ arc (betaDelta ε X H) q r, S4sharp ε X H α * eC (-(n * α)) =
          mainKterm ε X H q r n + ∫ α in arcRange ε X ∩ arc (betaDelta ε X H) q r,
            errArc ε X H q r α * eC (-(n * α)) := by
      intro n q hq r hr
      rw [Finset.mem_Icc] at hq
      rw [Finset.mem_filter, Finset.mem_Icc] at hr
      have hint : ∀ f : ℝ → ℂ, Continuous f →
          IntegrableOn f (arcRange ε X ∩ arc (betaDelta ε X H) q r) :=
        fun f hf => (hf.integrableOn_Icc).mono_set
          (Set.inter_subset_left.trans Set.Ioc_subset_Icc_self)
      have hmc : Continuous fun α : ℝ => mainArc ε X H q r (α - r / q) * eC (-(n * α)) :=
        ((mainArc_continuous hX hH q r).comp (continuous_id.sub continuous_const)).mul
          (hce.comp (continuous_const.mul continuous_id).neg)
      have hec : Continuous fun α : ℝ => errArc ε X H q r α * eC (-(n * α)) := by
        unfold errArc
        exact ((S4sharp_cont ε X H).sub ((mainArc_continuous hX hH q r).comp
          (continuous_id.sub continuous_const))).mul (hce.comp (continuous_const.mul continuous_id).neg)
      have e : (fun α => S4sharp ε X H α * eC (-(n * α))) = fun α =>
          mainArc ε X H q r (α - r / q) * eC (-(n * α)) + errArc ε X H q r α * eC (-(n * α)) := by
        funext α; unfold errArc; ring
      rw [e, integral_add (hint _ hmc) (hint _ hec),
        arc_main_inter hX hH hQp hβ0 hβQ hR6 hq.1 hr.1.1 hr.1.2 hr.2 n]
    have hR : ∀ q ∈ Icc 1 ⌊Qpar ε X⌋₊, ∀ r ∈ (Icc 1 q).filter (fun r => Nat.Coprime r q),
        ∫ α in arcRange ε X ∩ arc (betaDelta ε X H) q r,
            errArc ε X H q r α * ∑ n ∈ S, eC (-(n * α)) =
          ∑ n ∈ S, ((∫ α in arcRange ε X ∩ arc (betaDelta ε X H) q r,
            S4sharp ε X H α * eC (-(n * α))) - mainKterm ε X H q r n) := by
      intro q hq r hr
      have hec : ∀ n : ℕ, Continuous fun α : ℝ => errArc ε X H q r α * eC (-(n * α)) := by
        intro n
        unfold errArc
        exact ((S4sharp_cont ε X H).sub ((mainArc_continuous hX hH q r).comp
          (continuous_id.sub continuous_const))).mul (hce.comp (continuous_const.mul continuous_id).neg)
      have hi : ∀ n ∈ S, IntegrableOn (fun α : ℝ => errArc ε X H q r α * eC (-(n * α)))
          (arcRange ε X ∩ arc (betaDelta ε X H) q r) := fun n _ =>
        ((hec n).integrableOn_Icc).mono_set (Set.inter_subset_left.trans Set.Ioc_subset_Icc_self)
      simp_rw [Finset.mul_sum]
      rw [integral_finset_sum S hi]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hpiece n q hq r hr]; ring
    simp_rw [hsplit, mainK_eq]
    rw [← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r hr => ?_
    exact (hR q hq r hr).symm
  /- The error term of Proposition 2.4, as in its proof on page 9: the error of display (2.5) is
  at most `C q X^{2ε}(1 + Hβ(δ)) ≤ C Q X^{2ε}(1 + Hβ(δ))` on every arc, so the difference is at
  most that times `∫_𝔐 |∑_{n} e(-nα)| dα ≤ ∫_0^1 |∑_n e(nα)| dα`. -/
  have norm_major_sub_main_le {ε : ℝ} {X : ℕ} (hX : 1 ≤ X) {H : ℝ} (hH : 0 ≤ H) (hQp : 0 < Qpar ε X) (hβ0 : 0 ≤ betaDelta ε X H) (hβQ : betaDelta ε X H < 1 / Qpar ε X) (hR6 : (⌊R4 ε X ^ 6⌋₊ : ℝ) * 2 ≤ Qpar ε X) (hdisj : 2 * betaDelta ε X H * Qpar ε X ^ 2 < 1) {C : ℝ} (hP23 : ∀ q a : ℕ, 1 ≤ q → (q : ℝ) ≤ Qpar ε X → Nat.Coprime a q → ∀ β : ℝ,
      ‖S4sharp ε X H ((a : ℝ) / q + β) - mainArc ε X H q a β‖ ≤
        C * q * (X : ℝ) ^ (2 * ε) * (1 + H * |β|)) (S : Finset ℕ) : ‖(∑ n ∈ S, majorInt ε X H n) - ∑ n ∈ S, mainK ε X H n‖ ≤
      (max C 0 * Qpar ε X * (X : ℝ) ^ (2 * ε) * (1 + H * betaDelta ε X H)) *
        ∫ α in (0 : ℝ)..1, ‖∑ n ∈ S, eC (n * α)‖ := by
      have hce := continuous_eC
      set β := betaDelta ε X H
      set B := max C 0 * Qpar ε X * (X : ℝ) ^ (2 * ε) * (1 + H * β) with hBdef
      have hXp : (0 : ℝ) < X := by exact_mod_cast hX
      have hX2 : 0 ≤ (X : ℝ) ^ (2 * ε) := (Real.rpow_pos_of_pos hXp _).le
      have hB0 : 0 ≤ B := by
        have : 0 ≤ 1 + H * β := by nlinarith
        have := le_max_right C 0
        positivity
      have hQ : ∀ q ∈ Icc 1 ⌊Qpar ε X⌋₊, 1 ≤ q ∧ (q : ℝ) ≤ Qpar ε X := by
        intro q hq
        rw [Finset.mem_Icc] at hq
        exact ⟨hq.1, le_trans (by exact_mod_cast hq.2) (Nat.floor_le hQp.le)⟩
      have hbound : ∀ q ∈ Icc 1 ⌊Qpar ε X⌋₊, ∀ r ∈ (Icc 1 q).filter (fun r => Nat.Coprime r q),
          ∀ α ∈ arcRange ε X ∩ arc β q r, ‖errArc ε X H q r α‖ ≤ B := by
        intro q hq r hr α hα
        obtain ⟨hq1, hqQ⟩ := hQ q hq
        have hcop : Nat.Coprime r q := (Finset.mem_filter.1 hr).2
        have h := hP23 q r hq1 hqQ hcop (α - r / q)
        rw [add_sub_cancel] at h
        unfold errArc
        refine le_trans h ?_
        have hη : |α - r / q| ≤ β := by
          have := hα.2; unfold arc at this
          rw [abs_le]; constructor <;> linarith [this.1, this.2]
        have h1 : 1 + H * |α - r / q| ≤ 1 + H * β := by nlinarith
        have h2 : 0 ≤ 1 + H * |α - r / q| := by nlinarith [abs_nonneg (α - r / q)]
        have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
        calc C * q * (X : ℝ) ^ (2 * ε) * (1 + H * |α - r / q|)
            ≤ max C 0 * q * (X : ℝ) ^ (2 * ε) * (1 + H * |α - r / q|) := by
              have : 0 ≤ q * (X : ℝ) ^ (2 * ε) * (1 + H * |α - r / q|) := by positivity
              nlinarith [le_max_left C 0]
          _ ≤ max C 0 * Qpar ε X * (X : ℝ) ^ (2 * ε) * (1 + H * β) := by
              have hm : 0 ≤ max C 0 := le_max_right _ _
              have := mul_le_mul hqQ h1 h2 hQp.le
              have h3 : 0 ≤ max C 0 * (X : ℝ) ^ (2 * ε) := mul_nonneg hm hX2
              nlinarith
      have hsc : Continuous fun α : ℝ => ∑ n ∈ S, eC (-(n * α)) := by fun_prop
      have hnc : Continuous fun α : ℝ => ‖∑ n ∈ S, eC (-(n * α))‖ := hsc.norm
      rw [major_sub_main hX hH hQp hβ0 hβQ hR6 hdisj S]
      have hstep : ∀ q ∈ Icc 1 ⌊Qpar ε X⌋₊, ∀ r ∈ (Icc 1 q).filter (fun r => Nat.Coprime r q),
          ‖∫ α in arcRange ε X ∩ arc β q r, errArc ε X H q r α * ∑ n ∈ S, eC (-(n * α))‖ ≤
            B * ∫ α in arcRange ε X ∩ arc β q r, ‖∑ n ∈ S, eC (-(n * α))‖ := by
        intro q hq r hr
        have hint : ∀ f : ℝ → ℝ, Continuous f → IntegrableOn f (arcRange ε X ∩ arc β q r) :=
          fun f hf => (hf.integrableOn_Icc).mono_set
            (Set.inter_subset_left.trans Set.Ioc_subset_Icc_self)
        have hec : Continuous fun α : ℝ => ‖errArc ε X H q r α * ∑ n ∈ S, eC (-(n * α))‖ := by
          unfold errArc
          exact (((S4sharp_cont ε X H).sub ((mainArc_continuous hX hH q r).comp
            (continuous_id.sub continuous_const))).mul hsc).norm
        refine le_trans (norm_integral_le_integral_norm _) ?_
        rw [← integral_const_mul]
        apply setIntegral_mono_on (hint _ hec) (hint _ (continuous_const.mul hnc))
          ((measurableSet_Ioc).inter measurableSet_Icc)
        intro α hα
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hbound q hq r hr α hα) (norm_nonneg _)
      calc ‖∑ q ∈ Icc 1 ⌊Qpar ε X⌋₊, ∑ r ∈ (Icc 1 q).filter (fun r => Nat.Coprime r q),
            ∫ α in arcRange ε X ∩ arc β q r, errArc ε X H q r α * ∑ n ∈ S, eC (-(n * α))‖
          ≤ ∑ q ∈ Icc 1 ⌊Qpar ε X⌋₊, ∑ r ∈ (Icc 1 q).filter (fun r => Nat.Coprime r q),
            ‖∫ α in arcRange ε X ∩ arc β q r, errArc ε X H q r α * ∑ n ∈ S, eC (-(n * α))‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => norm_sum_le _ _)
        _ ≤ ∑ q ∈ Icc 1 ⌊Qpar ε X⌋₊, ∑ r ∈ (Icc 1 q).filter (fun r => Nat.Coprime r q),
            B * ∫ α in arcRange ε X ∩ arc β q r, ‖∑ n ∈ S, eC (-(n * α))‖ :=
            Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun r hr => hstep q hq r hr
        _ = B * ∫ α in arcRange ε X ∩ majorArcs ε X H, ‖∑ n ∈ S, eC (-(n * α))‖ := by
            have hA := setIntegral_arcs (E := ℝ) ε X H (A := arcRange ε X) measurableSet_Ioc
              Set.Ioc_subset_Icc_self hdisj _ hnc
            rw [hA]
            simp_rw [Finset.mul_sum]
            rfl
        _ ≤ B * ∫ α in arcRange ε X, ‖∑ n ∈ S, eC (-(n * α))‖ := by
            apply mul_le_mul_of_nonneg_left _ hB0
            apply setIntegral_mono_set
            · exact (hnc.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
            · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
            · exact Set.inter_subset_left.eventuallyLE
        _ = B * ∫ α in (0 : ℝ)..1, ‖∑ n ∈ S, eC (n * α)‖ := by
            rw [setIntegral_arcRange_norm]

    /- ### Proposition 2.4 from Proposition 2.3 -/
  have H_mul_betaDelta {ε : ℝ} {X : ℕ} (hX : 1 < (X : ℝ)) {H : ℝ} (hH : 0 < H) : H * betaDelta ε X H = (X : ℝ) ^ ε * Real.log X ^ (3 ^ 6 + 1 : ℕ) := by
    have hXp : (0 : ℝ) < X := by linarith
    have hL : 0 < Real.log X := Real.log_pos hX
    have hLp : 0 < Real.log X ^ (3 ^ 6 + 1 : ℕ) := pow_pos hL _
    unfold betaDelta delta Ddelta
    rw [Real.rpow_neg hXp.le]
    have hXe : 0 < (X : ℝ) ^ ε := Real.rpow_pos_of_pos hXp _
    field_simp
  /- The eventual size conditions on `X` used for the major arcs. -/
  have eventually_major {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 10) (X₀ : ℝ) : ∀ᶠ x : ℝ in atTop, X₀ ≤ x ∧ 3 ≤ x ∧ Real.log x ^ (3 ^ 6 + 1 : ℕ) ≤ x ^ ε ∧
      2 < x ^ ((3 : ℝ) / 5 - 3 * ε) ∧ 2 ≤ x ^ (17 * ε / 20) := by
    have h1 := (isLittleO_log_rpow_rpow_atTop ((3 ^ 6 + 1 : ℕ) : ℝ) hε).bound one_pos
    have h2 := (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 3 / 5 - 3 * ε)).eventually_gt_atTop 2
    have h3 := (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 17 * ε / 20)).eventually_ge_atTop 2
    filter_upwards [eventually_ge_atTop X₀, eventually_ge_atTop 3, h1, h2, h3,
      eventually_ge_atTop 1] with x hx0 hx3 hx1 hx2 hx4 hx5
    refine ⟨hx0, hx3, ?_, hx2, hx4⟩
    have hL : 0 ≤ Real.log x := Real.log_nonneg hx5
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity), one_mul, Real.rpow_natCast] at hx1
    exact hx1
  /- Kim, Proposition 2.4, display (2.6), page 9, PROVED from `prop_2_3` and the proved
  `lemma_1_7_weak`, following the paper's proof: integrate display (2.5) over the arcs, which are
  disjoint, and bound the error terms with the `L¹` bound. Same statement as
  `Burst8P2.prop_2_4`. -/
  have prop_2_4_p3 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ g₀ : ℕ, ∀ g b : ℕ,
    g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∃ C : ℝ, ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      ((g ^ k : ℕ) : ℝ) ^ ((3 : ℝ) / 5 + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      ‖(∑ n ∈ starSet g b (g ^ k) H, majorInt ε (g ^ k) H n) -
          ∑ n ∈ starSet g b (g ^ k) H, mainK ε (g ^ k) H n‖ ≤
        C * ((g ^ k : ℕ) : ℝ) ^ (5 * ε) * H ^ (3 * ε) := by
      obtain ⟨ε₁, hε₁, h23⟩ := prop_2_3
      refine ⟨min ε₁ (1 / 10), lt_min hε₁ (by norm_num), fun ε hε hεε => ?_⟩
      have hε1 : ε < ε₁ := lt_of_lt_of_le hεε (min_le_left _ _)
      have hε2 : ε < 1 / 10 := lt_of_lt_of_le hεε (min_le_right _ _)
      obtain ⟨C, X₀, hC⟩ := h23 ε hε hε1
      obtain ⟨g₁, hg₁⟩ := lemma_1_7
      obtain ⟨g₀', hg₀3', hg₀'⟩ := exists_g0 hε
      refine ⟨max (max g₀' g₁) 33554432, fun g b hg hb2 hbg => ?_⟩
      have hgg' : g₀' ≤ g := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hg
      have hgg₁ : g₁ ≤ g := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hg
      have hgbig : 33554432 ≤ g := le_trans (le_max_right _ _) hg
      have hg3 : 3 ≤ g := le_trans hg₀3' hgg'
      obtain ⟨hθ0, hθh, hρ0, hρ1, hρκ⟩ := hg₀' g hgg'
      obtain ⟨C₂, hC₂⟩ := hg₁ g b hgg₁ hb2 hbg
      -- `θ ≤ ε`
      have hθε : thetaG g ≤ ε := by
        obtain ⟨_, ha1⟩ := hhlr hg3
        have : rhoG g ≤ 1 - thetaG g := by
          unfold rhoG
          calc Real.log ((g : ℝ) - 1) / Real.log g * (1 - thetaG g) ≤ 1 * (1 - thetaG g) :=
                mul_le_mul_of_nonneg_right ha1 (by linarith)
            _ = 1 - thetaG g := one_mul _
        linarith
      have hX : Tendsto (fun k : ℕ => ((g ^ k : ℕ) : ℝ)) atTop atTop := by
        have : Tendsto (fun k : ℕ => (g : ℝ) ^ k) atTop atTop :=
          tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast (by omega : 1 < g))
        simpa using this
      obtain ⟨K₀, hK₀⟩ := Filter.eventually_atTop.1 (hX.eventually (eventually_major hε hε2 X₀))
      refine ⟨2 * max C 0 * max C₂ 0, max K₀ 1, fun k H hk hlo hhi => ?_⟩
      have hk0 : K₀ ≤ k := le_trans (le_max_left _ _) hk
      have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
      obtain ⟨hXX₀, hX3, hlog, hX2, hX4⟩ := hK₀ k hk0
      obtain ⟨hH1, hHX, -⟩ := range_facts hg3 hk1 hε (by norm_num) hlo hhi
      set X : ℝ := ((g ^ k : ℕ) : ℝ) with hXdef
      have hXp : 0 < X := by linarith
      have hX1 : 1 < X := by linarith
      have hXN : X₀ ≤ g ^ k := Nat.cast_le.1 hXX₀
      have hHp : 0 < H := by linarith
      set L := Real.log X ^ (3 ^ 6 + 1 : ℕ) with hLdef
      have hLp : 0 < L := pow_pos (Real.log_pos hX1) _
      have hHβ := H_mul_betaDelta (ε := ε) (X := g ^ k) hX1 hHp
      set β := betaDelta ε (g ^ k) H with hβdef
      have hQp : 0 < Qpar ε (g ^ k) := Real.rpow_pos_of_pos hXp _
      have hQ1 : 1 ≤ Qpar ε (g ^ k) := Real.one_le_rpow hX1.le hε.le
      have hβ0 : 0 ≤ β := by
        have : 0 ≤ H * β := by rw [hHβ]; positivity
        nlinarith
      -- the size conditions
      have hXe := Real.rpow_pos_of_pos hXp ε
      have hdisj : 2 * β * Qpar ε (g ^ k) ^ 2 < 1 := by
        have hQ2 : Qpar ε (g ^ k) ^ 2 = X ^ (2 * ε) := by
          unfold Qpar; rw [← Real.rpow_natCast, ← Real.rpow_mul hXp.le]; ring_nf
        rw [hQ2]
        -- `2 β X^{2ε} H = 2 X^{3ε} L ≤ 2 X^{4ε} < X^{3/5+ε} ≤ H`
        have e1 : 2 * β * X ^ (2 * ε) * H = 2 * X ^ (3 * ε) * L := by
          have : X ^ (3 * ε) = X ^ ε * X ^ (2 * ε) := by rw [← Real.rpow_add hXp]; ring_nf
          calc 2 * β * X ^ (2 * ε) * H = 2 * X ^ (2 * ε) * (H * β) := by ring
            _ = 2 * X ^ (3 * ε) * L := by rw [hHβ, this]; ring
        have e2 : 2 * X ^ (3 * ε) * L ≤ 2 * X ^ (4 * ε) := by
          have : X ^ (4 * ε) = X ^ (3 * ε) * X ^ ε := by rw [← Real.rpow_add hXp]; ring_nf
          rw [this]
          have : 0 < X ^ (3 * ε) := Real.rpow_pos_of_pos hXp _
          nlinarith
        have e3 : 2 * X ^ (4 * ε) < X ^ ((3 : ℝ) / 5 + ε) := by
          have : X ^ ((3 : ℝ) / 5 + ε) = X ^ ((3 : ℝ) / 5 - 3 * ε) * X ^ (4 * ε) := by
            rw [← Real.rpow_add hXp]; ring_nf
          rw [this]
          have : 0 < X ^ (4 * ε) := Real.rpow_pos_of_pos hXp _
          nlinarith
        have : 2 * β * X ^ (2 * ε) * H < 1 * H := by linarith
        exact lt_of_mul_lt_mul_right this hHp.le
      have hβQ : β < 1 / Qpar ε (g ^ k) := by
        rw [lt_div_iff₀ hQp]
        have h1 : β * Qpar ε (g ^ k) ≤ β * Qpar ε (g ^ k) * Qpar ε (g ^ k) :=
          le_mul_of_one_le_right (mul_nonneg hβ0 hQp.le) hQ1
        have h2 : β * Qpar ε (g ^ k) * Qpar ε (g ^ k) = β * Qpar ε (g ^ k) ^ 2 := by ring
        linarith
      have hR6 : (⌊R4 ε (g ^ k) ^ 6⌋₊ : ℝ) * 2 ≤ Qpar ε (g ^ k) := by
        have hR : R4 ε (g ^ k) ^ 6 = X ^ (3 * ε / 20) := by
          unfold R4; rw [← Real.rpow_natCast, ← Real.rpow_mul hXp.le]; ring_nf
        have hfl : (⌊R4 ε (g ^ k) ^ 6⌋₊ : ℝ) ≤ X ^ (3 * ε / 20) := by
          rw [← hR]; exact Nat.floor_le (by rw [hR]; positivity)
        have : Qpar ε (g ^ k) = X ^ (3 * ε / 20) * X ^ (17 * ε / 20) := by
          rw [show Qpar ε (g ^ k) = X ^ ε from rfl, ← Real.rpow_add hXp]; ring_nf
        rw [this]
        have : 0 ≤ X ^ (3 * ε / 20) := (Real.rpow_pos_of_pos hXp _).le
        nlinarith
      have hP23 := hC (g ^ k) hXN H hlo hhi
      have hmain := norm_major_sub_main_le (ε := ε) (X := g ^ k) (H := H)
        (Nat.one_le_iff_ne_zero.2 (by positivity)) hHp.le hQp hβ0 hβQ hR6 hdisj hP23
        (starSet g b (g ^ k) H)
      have hL1 := hC₂ k H hH1 hHX
      -- the final arithmetic
      set N : ℝ := ((starSet g b (g ^ k) H).card : ℝ) with hNdef
      have hN : N ≤ H := by
        have h1 : (starSet g b (g ^ k) H).card ≤ ⌊H⌋₊ := by
          unfold starSet
          refine le_trans (Finset.card_filter_le _ _) ?_
          simp
        have : N ≤ (⌊H⌋₊ : ℝ) := by rw [hNdef]; exact_mod_cast h1
        exact le_trans this (Nat.floor_le hHp.le)
      have hN0 : 0 ≤ N := Nat.cast_nonneg _
      have hNθ : N ^ thetaG g ≤ H ^ (3 * ε) := by
        calc N ^ thetaG g ≤ H ^ thetaG g := Real.rpow_le_rpow hN0 hN hθ0
          _ ≤ H ^ (3 * ε) := Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)
      have hNθ0 : 0 ≤ N ^ thetaG g := Real.rpow_nonneg hN0 _
      have hint0 : 0 ≤ ∫ α in (0 : ℝ)..1, ‖∑ n ∈ starSet g b (g ^ k) H, eC (n * α)‖ :=
        intervalIntegral.integral_nonneg zero_le_one (fun _ _ => norm_nonneg _)
      have hint : ∫ α in (0 : ℝ)..1, ‖∑ n ∈ starSet g b (g ^ k) H, eC (n * α)‖ ≤
          max C₂ 0 * H ^ (3 * ε) := by
        refine le_trans hL1 ?_
        calc C₂ * N ^ thetaG g ≤ max C₂ 0 * N ^ thetaG g :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hNθ0
          _ ≤ max C₂ 0 * H ^ (3 * ε) := mul_le_mul_of_nonneg_left hNθ (le_max_right _ _)
      have hB : max C 0 * Qpar ε (g ^ k) * X ^ (2 * ε) * (1 + H * β) ≤
          2 * max C 0 * X ^ (5 * ε) := by
        rw [hHβ]
        have hQ : Qpar ε (g ^ k) = X ^ ε := rfl
        rw [hQ]
        have h1 : 1 + X ^ ε * L ≤ 2 * X ^ (2 * ε) := by
          have : X ^ (2 * ε) = X ^ ε * X ^ ε := by rw [← Real.rpow_add hXp]; ring_nf
          have hXe1 : 1 ≤ X ^ ε := Real.one_le_rpow hX1.le hε.le
          rw [this]
          have a1 := mul_le_mul_of_nonneg_left hlog hXe.le
          have a2 : 1 ≤ X ^ ε * X ^ ε := one_le_mul_of_one_le_of_one_le hXe1 hXe1
          linarith
        have h5 : X ^ (5 * ε) = X ^ ε * X ^ (2 * ε) * X ^ (2 * ε) := by
          rw [← Real.rpow_add hXp, ← Real.rpow_add hXp]; ring_nf
        rw [h5]
        have hm : 0 ≤ max C 0 := le_max_right _ _
        have hP : 0 ≤ max C 0 * X ^ ε * X ^ (2 * ε) := by positivity
        calc max C 0 * X ^ ε * X ^ (2 * ε) * (1 + X ^ ε * L)
            ≤ max C 0 * X ^ ε * X ^ (2 * ε) * (2 * X ^ (2 * ε)) := mul_le_mul_of_nonneg_left h1 hP
          _ = 2 * max C 0 * (X ^ ε * X ^ (2 * ε) * X ^ (2 * ε)) := by ring
      have hBnn : 0 ≤ max C 0 * Qpar ε (g ^ k) * X ^ (2 * ε) * (1 + H * β) :=
        mul_nonneg (mul_nonneg (mul_nonneg (le_max_right _ _) hQp.le)
          (Real.rpow_pos_of_pos hXp _).le) (add_nonneg zero_le_one (mul_nonneg hHp.le hβ0))
      calc ‖(∑ n ∈ starSet g b (g ^ k) H, majorInt ε (g ^ k) H n) -
              ∑ n ∈ starSet g b (g ^ k) H, mainK ε (g ^ k) H n‖
          ≤ (max C 0 * Qpar ε (g ^ k) * X ^ (2 * ε) * (1 + H * β)) *
              ∫ α in (0 : ℝ)..1, ‖∑ n ∈ starSet g b (g ^ k) H, eC (n * α)‖ := hmain
        _ ≤ (2 * max C 0 * X ^ (5 * ε)) * (max C₂ 0 * H ^ (3 * ε)) :=
            mul_le_mul hB hint hint0 (by have := le_max_right C 0; positivity)
        _ = 2 * max C 0 * max C₂ 0 * X ^ (5 * ε) * H ^ (3 * ε) := by ring

    /- ### The main term after the sum over `b`, a check on Lemma 1.8 -/

  exact prop_2_4_p3


/-- LEAF: Kim, Section 2.2, displays (2.8) to (2.11), pages 10 and 11: the main term of
Proposition 2.4 is `≪ (log X)^7 |[X,X+H]^*|`. The kernel bound (2.8), (2.9) gives `d₃(m)/q`,
Lemma 1.8 bounds the sums over `a` and `b`, display (2.10) gives `(log X)^2`, display (2.11)
uses Lemma 2.6 of Dartyge and Mauduit and gives `(log X)^2`, and `∑_{m ≤ X^{3ε/20}} d₃(m)/m`
gives `(log X)^3`. -/
theorem main_term_bound : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ g₀ : ℕ, ∀ g b : ℕ,
    g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∃ C : ℝ, ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      ((g ^ k : ℕ) : ℝ) ^ ((3 : ℝ) / 5 + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      ‖∑ n ∈ starSet g b (g ^ k) H, mainK ε (g ^ k) H n‖ ≤
        C * Real.log ((g ^ k : ℕ) : ℝ) ^ 7 * (starSet g b (g ^ k) H).card := by
  -- OUT OF REACH: requires Lemma 1.8 and Dartyge-Mauduit Lemma 2.6, neither in scope.
  sorry

/-- `log g ≤ 2 log(g - 1)` for `g ≥ 3`, so the counting exponent `log(g-1)/log g` is at
least `1/2`. -/
theorem half_le_logratio {g : ℕ} (hg : 3 ≤ g) :
    1 / 2 ≤ Real.log ((g : ℝ) - 1) / Real.log g ∧ Real.log ((g : ℝ) - 1) / Real.log g ≤ 1 := by
  have hgR : (3 : ℝ) ≤ g := by exact_mod_cast hg
  have hL : 0 < Real.log g := Real.log_pos (by linarith)
  constructor
  · rw [le_div_iff₀ hL]
    have : Real.log g ≤ Real.log (((g : ℝ) - 1) ^ 2) :=
      Real.log_le_log (by linarith) (by nlinarith)
    rw [Real.log_pow] at this; push_cast at this; linarith
  · rw [div_le_one hL]; exact Real.log_le_log (by linarith) (by linarith)

/-- The error term of Proposition 2.4 is negligible: for `ε < 3/80`, `g ≥ 3` and any `C`,
`C X^{5ε} H^{3ε} ≤ |[X,X+H]^*|` once `k` is large, since `|[X,X+H]^*| ≥ (H/g)^{log(g-1)/log g}
≥ X^{3/10}/g`. -/
theorem err_small {ε : ℝ} (hε : 0 < ε) (hε' : ε < 3 / 80) {g b : ℕ} (hg : 3 ≤ g) (hb2 : 2 ≤ b)
    (hbg : b ≤ g - 1) (C : ℝ) : ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      ((g ^ k : ℕ) : ℝ) ^ ((3 : ℝ) / 5 + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      C * ((g ^ k : ℕ) : ℝ) ^ (5 * ε) * H ^ (3 * ε) ≤ (starSet g b (g ^ k) H).card := by
  have hgR : (3 : ℝ) ≤ g := by exact_mod_cast hg
  have hgp : (0 : ℝ) < g := by linarith
  set κ : ℝ := 3 / 10 - 8 * ε with hκ
  have hκp : 0 < κ := by rw [hκ]; linarith
  set C' := max C 0
  have hX : Tendsto (fun k : ℕ => ((g ^ k : ℕ) : ℝ)) atTop atTop := by
    have : Tendsto (fun k : ℕ => (g : ℝ) ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by linarith)
    simpa using this
  obtain ⟨K₁, hK₁⟩ := Filter.eventually_atTop.1
    (((tendsto_rpow_atTop hκp).comp hX).eventually_ge_atTop (C' * g))
  refine ⟨max K₁ 1, fun k H hk hlo hhi => ?_⟩
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
  obtain ⟨hH1, hHX, -⟩ := range_facts hg hk1 hε (by norm_num) hlo hhi
  set X : ℝ := ((g ^ k : ℕ) : ℝ) with hXdef
  set N : ℝ := ((starSet g b (g ^ k) H).card : ℝ) with hNdef
  have hXκ : C' * g ≤ X ^ κ := hK₁ k (le_trans (le_max_left _ _) hk)
  have hX1 : 1 ≤ X := le_trans hH1 hHX.le
  have hXp : 0 < X := by linarith
  have hHp : 0 < H := by linarith
  -- lower bound for N
  have hcard := card_starSet_ge (by omega) hb2 (by omega) hH1 hHX
  have hNj : ((g : ℝ) - 1) ^ (Nat.log g ⌊H⌋₊) ≤ N := by
    have : (((g - 1) ^ (Nat.log g ⌊H⌋₊) : ℕ) : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hcard
    push_cast [show 1 ≤ g by omega] at this; exact this
  have hlow := rpow_card_lower hg (θ := 0) (by norm_num) hH1
    (lt_pow_log_succ (by omega) hHp.le) hNj
  simp only [sub_zero, mul_one, Real.rpow_one] at hlow
  obtain ⟨ha1, ha2⟩ := half_le_logratio hg
  set a := Real.log ((g : ℝ) - 1) / Real.log g
  have hHa : X ^ ((3 : ℝ) / 10) ≤ H ^ a := by
    calc X ^ ((3 : ℝ) / 10) = (X ^ ((3 : ℝ) / 5)) ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_mul hXp.le]; norm_num
      _ ≤ H ^ ((1 : ℝ) / 2) := by
          apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
          exact le_trans (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)) hlo
      _ ≤ H ^ a := Real.rpow_le_rpow_of_exponent_le hH1 ha1
  have hga : (g : ℝ) ^ a ≤ g := by
    calc (g : ℝ) ^ a ≤ (g : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) ha2
      _ = g := Real.rpow_one _
  have hgap : 0 < (g : ℝ) ^ a := Real.rpow_pos_of_pos hgp _
  have hN : X ^ ((3 : ℝ) / 10) / g ≤ N := by
    calc X ^ ((3 : ℝ) / 10) / g ≤ H ^ a / (g : ℝ) ^ a := by
          apply div_le_div₀ (Real.rpow_pos_of_pos hHp _).le hHa hgap hga
      _ ≤ N := hlow
  -- upper bound for the error
  have hH3 : H ^ (3 * ε) ≤ X ^ (3 * ε) := Real.rpow_le_rpow hHp.le hHX.le (by linarith)
  have hE : C * X ^ (5 * ε) * H ^ (3 * ε) ≤ C' * X ^ (8 * ε) := by
    have h8 : X ^ (8 * ε) = X ^ (5 * ε) * X ^ (3 * ε) := by
      rw [← Real.rpow_add hXp]; ring_nf
    have hX5 : 0 ≤ X ^ (5 * ε) := (Real.rpow_pos_of_pos hXp _).le
    have hH3p : 0 ≤ H ^ (3 * ε) := (Real.rpow_pos_of_pos hHp _).le
    rw [h8]
    calc C * X ^ (5 * ε) * H ^ (3 * ε) ≤ C' * X ^ (5 * ε) * H ^ (3 * ε) := by
          have : 0 ≤ X ^ (5 * ε) * H ^ (3 * ε) := mul_nonneg hX5 hH3p
          nlinarith [le_max_left C 0]
      _ ≤ C' * (X ^ (5 * ε) * X ^ (3 * ε)) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hH3 hX5) (le_max_right _ _)
  have hfin : C' * X ^ (8 * ε) ≤ X ^ ((3 : ℝ) / 10) / g := by
    rw [le_div_iff₀ hgp]
    have hsplit : X ^ ((3 : ℝ) / 10) = X ^ (8 * ε) * X ^ κ := by
      rw [← Real.rpow_add hXp, hκ]; ring_nf
    rw [hsplit]
    have h8p : 0 ≤ X ^ (8 * ε) := (Real.rpow_pos_of_pos hXp _).le
    nlinarith
  linarith

/-- The major arc leaf, PROVED from `prop_2_4`, `main_term_bound` and `err_small`. Same
statement as `Burst4Split.major_arcs_bound`. -/
theorem major_arcs_bound_p2 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ g₀ : ℕ,
    ∀ g b : ℕ, g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∃ C : ℝ, ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      ((g ^ k : ℕ) : ℝ) ^ ((3 : ℝ) / 5 + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      ‖∑ n ∈ starSet g b (g ^ k) H, majorInt ε (g ^ k) H n‖ ≤
        C * Real.log ((g ^ k : ℕ) : ℝ) ^ 7 * (starSet g b (g ^ k) H).card := by
  obtain ⟨e1, he1, h24⟩ := prop_2_4
  obtain ⟨e2, he2, hmt⟩ := main_term_bound
  refine ⟨min (min e1 e2) (3 / 80), lt_min (lt_min he1 he2) (by norm_num),
    fun ε hε hεε => ?_⟩
  have hε1 : ε < e1 := lt_of_lt_of_le hεε (le_trans (min_le_left _ _) (min_le_left _ _))
  have hε2 : ε < e2 := lt_of_lt_of_le hεε (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε3 : ε < 3 / 80 := lt_of_lt_of_le hεε (min_le_right _ _)
  obtain ⟨g1, hg1⟩ := h24 ε hε hε1
  obtain ⟨g2, hg2⟩ := hmt ε hε hε2
  refine ⟨max (max g1 g2) 3, fun g b hg hb2 hbg => ?_⟩
  have hgg1 : g1 ≤ g := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hg
  have hgg2 : g2 ≤ g := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hg
  have hg3 : 3 ≤ g := le_trans (le_max_right _ _) hg
  obtain ⟨C1, K1, hK1⟩ := hg1 g b hgg1 hb2 hbg
  obtain ⟨C2, K2, hK2⟩ := hg2 g b hgg2 hb2 hbg
  obtain ⟨K3, hK3⟩ := err_small hε hε3 hg3 hb2 hbg C1
  refine ⟨1 + max C2 0, max (max K1 K2) (max K3 1), fun k H hk hlo hhi => ?_⟩
  have hk1 : K1 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hk2 : K2 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have hk3 : K3 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk4 : 1 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  obtain ⟨hH1, hHX, -⟩ := range_facts hg3 hk4 hε (by norm_num) hlo hhi
  have b1 := hK1 k H hk1 hlo hhi
  have b2 := hK2 k H hk2 hlo hhi
  have b3 := hK3 k H hk3 hlo hhi
  set X : ℝ := ((g ^ k : ℕ) : ℝ)
  set N : ℝ := ((starSet g b (g ^ k) H).card : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hX3 : (3 : ℝ) ≤ X := by
    have : 3 ≤ g ^ k := le_trans hg3 (Nat.le_self_pow (by omega) g)
    simp only [X]; exact_mod_cast this
  have hL : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact le_trans (le_of_lt (lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num))) hX3
  have hL7 : 1 ≤ Real.log X ^ 7 := one_le_pow₀ hL
  have htri : ‖∑ n ∈ starSet g b (g ^ k) H, majorInt ε (g ^ k) H n‖ ≤
      ‖(∑ n ∈ starSet g b (g ^ k) H, majorInt ε (g ^ k) H n) -
          ∑ n ∈ starSet g b (g ^ k) H, mainK ε (g ^ k) H n‖ +
        ‖∑ n ∈ starSet g b (g ^ k) H, mainK ε (g ^ k) H n‖ := by
    have := norm_add_le ((∑ n ∈ starSet g b (g ^ k) H, majorInt ε (g ^ k) H n) -
          ∑ n ∈ starSet g b (g ^ k) H, mainK ε (g ^ k) H n)
        (∑ n ∈ starSet g b (g ^ k) H, mainK ε (g ^ k) H n)
    rwa [sub_add_cancel] at this
  have hC2 : C2 * Real.log X ^ 7 * N ≤ max C2 0 * Real.log X ^ 7 * N := by
    have : 0 ≤ Real.log X ^ 7 * N := by positivity
    nlinarith [le_max_left C2 0]
  have hC20 : 0 ≤ max C2 0 := le_max_right _ _
  have hN7 : N ≤ Real.log X ^ 7 * N := by nlinarith
  calc ‖∑ n ∈ starSet g b (g ^ k) H, majorInt ε (g ^ k) H n‖
      ≤ N + max C2 0 * Real.log X ^ 7 * N := by linarith
    _ ≤ (1 + max C2 0) * Real.log X ^ 7 * N := by nlinarith

/-- Kim, Theorem 1.1, assembled from the Burst 8 split. Same statement as
`LeanLab.MissingDigit.kim_thm1_1` and the same assembly as `Burst4Split.kim_thm1_1_of_split`,
with the three Burst 4 leaves replaced by `prop_2_2_p2`, `major_arcs_bound_p2` and
`prop_2_5_p2`. CONDITIONAL ON the cited `prop_2_1`, `lemma_1_7`, `prop_3_5`, `prop_2_4` and
`main_term_bound`. -/
theorem kim_thm1_1_of_p2 : D4Bound (3 / 5) 7 := by
  obtain ⟨e1, he1, h1⟩ := prop_2_2_p2
  obtain ⟨e2, he2, h2⟩ := major_arcs_bound_p2
  obtain ⟨e3, he3, h3⟩ := prop_2_5_p2
  intro ε hε
  set ε' : ℝ := min ε (min e1 (min e2 e3)) / 2 with hε'
  have hmin_pos : 0 < min ε (min e1 (min e2 e3)) := lt_min hε (lt_min he1 (lt_min he2 he3))
  have hε'pos : 0 < ε' := by positivity
  have hε'lt : ε' < min ε (min e1 (min e2 e3)) := by rw [hε']; linarith
  have hε'1 : ε' < e1 := lt_of_lt_of_le hε'lt (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε'2 : ε' < e2 := lt_of_lt_of_le hε'lt
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hε'3 : ε' < e3 := lt_of_lt_of_le hε'lt
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hε'ε : ε' < ε := lt_of_lt_of_le hε'lt (min_le_left _ _)
  obtain ⟨g1, hg1⟩ := h1 ε' hε'pos hε'1
  obtain ⟨g2, hg2⟩ := h2 ε' hε'pos hε'2
  obtain ⟨g3, hg3⟩ := h3 ε' hε'pos hε'3
  refine ⟨max g1 (max g2 g3), fun g b hg hb2 hbg A₁ A₂ hA₁ hA₂ => ?_⟩
  have hgg1 : g1 ≤ g := le_trans (le_max_left _ _) hg
  have hgg2 : g2 ≤ g := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hg
  have hgg3 : g3 ≤ g := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hg
  have hg2' : 2 ≤ g := by omega
  obtain ⟨K1, hK1⟩ := hg1 g b hgg1 hb2 hbg 1 one_pos
  obtain ⟨C, K2, hK2⟩ := hg2 g b hgg2 hb2 hbg
  obtain ⟨K3, hK3⟩ := hg3 g b hgg3 hb2 hbg 1 one_pos
  -- `X = g^k` tends to infinity, so eventually `X^{ε-ε'} ≥ max (1/A₁) A₂` and `X ≥ 3`.
  have hX : Filter.Tendsto (fun k : ℕ => ((g ^ k : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    have : Filter.Tendsto (fun k : ℕ => (g : ℝ) ^ k) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast (by omega : 1 < g))
    simpa using this
  have hXc := (tendsto_rpow_atTop (by linarith : 0 < ε - ε')).comp hX
  obtain ⟨K4, hK4⟩ := Filter.eventually_atTop.1
    (hXc.eventually_ge_atTop (max (1 / A₁) A₂))
  obtain ⟨K5, hK5⟩ := Filter.eventually_atTop.1 (hX.eventually_ge_atTop 3)
  refine ⟨max C 0 + 2, max K1 (max K2 (max K3 (max K4 K5))), fun k H hk hlo hhi => ?_⟩
  have hk1 : K1 ≤ k := le_trans (le_max_left _ _) hk
  have hk2 : K2 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk3 : K3 ≤ k := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hk
  have hk4 : K4 ≤ k := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)))) hk
  have hk5 : K5 ≤ k := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)))) hk
  set X : ℝ := ((g ^ k : ℕ) : ℝ) with hXdef
  have hX3 : (3 : ℝ) ≤ X := hK5 k hk5
  have hXpos : 0 < X := by linarith
  have hXpow : max (1 / A₁) A₂ ≤ X ^ (ε - ε') := hK4 k hk4
  have hA1 : 1 / A₁ ≤ X ^ (ε - ε') := le_trans (le_max_left _ _) hXpow
  have hA2 : A₂ ≤ X ^ (ε - ε') := le_trans (le_max_right _ _) hXpow
  -- the hypotheses of the leaves at `ε'`
  have hlo' : X ^ ((3 : ℝ) / 5 + ε') ≤ H := by
    refine le_trans ?_ hlo
    have hsplit : X ^ ((3 : ℝ) / 5 + ε) = X ^ ((3 : ℝ) / 5 + ε') * X ^ (ε - ε') := by
      rw [← Real.rpow_add hXpos]; ring_nf
    rw [hsplit]
    have h1 : 1 ≤ A₁ * X ^ (ε - ε') := by
      have := mul_le_mul_of_nonneg_left hA1 hA₁.le
      rwa [mul_one_div_cancel hA₁.ne'] at this
    have hp : 0 ≤ X ^ ((3 : ℝ) / 5 + ε') := (Real.rpow_pos_of_pos hXpos _).le
    nlinarith
  have hhi' : H ≤ X ^ (1 - ε') := by
    refine le_trans hhi ?_
    have hsplit : X ^ (1 - ε') = X ^ (1 - ε) * X ^ (ε - ε') := by
      rw [← Real.rpow_add hXpos]; ring_nf
    rw [hsplit]
    have hp : 0 ≤ X ^ (1 - ε) := (Real.rpow_pos_of_pos hXpos _).le
    nlinarith
  have b1 := hK1 k H hk1 hlo' hhi'
  have b2 := hK2 k H hk2 hlo' hhi'
  have b3 := hK3 k H hk3 hlo' hhi'
  have hdec := sum_decomp ε' (g ^ k) g b H
  set N : ℝ := ((starSet g b (g ^ k) H).card : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hL : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact le_trans (le_of_lt (lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num))) hX3
  have hL7 : 1 ≤ Real.log X ^ 7 := one_le_pow₀ hL
  have hS : (∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ)) ≤
      1 * N + C * Real.log X ^ 7 * N + 1 * N := by
    have hnn : 0 ≤ ∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    calc (∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ))
        = ‖((∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ) : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hnn]
      _ ≤ _ := by
          rw [hdec]
          refine le_trans (norm_add₃_le) ?_
          linarith
  have hC : C * Real.log X ^ 7 * N ≤ max C 0 * Real.log X ^ 7 * N := by
    have : 0 ≤ Real.log X ^ 7 * N := by positivity
    nlinarith [le_max_left C 0]
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  calc (∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ))
      ≤ 1 * N + C * Real.log X ^ 7 * N + 1 * N := hS
    _ ≤ (max C 0 + 2) * Real.log X ^ 7 * N := by nlinarith

#check (kim_thm1_1_of_p2 : D4Bound (3 / 5) 7)

#print axioms card_starSet_ge
#print axioms rpow_card_lower
#print axioms exists_g0
#print axioms tail_small
#print axioms norm_sum_setIntegral_le
#print axioms setIntegral_arcRange_norm
#print axioms err_small
#print axioms prop_2_2_p2
#print axioms prop_2_5_p2
#print axioms major_arcs_bound_p2
#print axioms kim_thm1_1_of_p2

end LeanLab.MissingDigit.Burst8P2
