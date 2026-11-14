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

/-- LEAF: Kim, Lemma 1.7, page 5: for `g` sufficiently large,
`∫_{[0,1]} |F_{[X,X+H]}(α)| dα ≪ |[X,X+H]^*|^{-1 + log((log g)+1)/log(g-1)}`, with
`F_{[X,X+H]}(α) = |[X,X+H]^*|^{-1} ∑_{n ∈ [X,X+H]^*} e(nα)`. Multiplied through by
`|[X,X+H]^*|`, which is at least `1` here, this is the form below. The paper gives no proof;
the implied constant may depend on `g` and `b`. Encoded for `X = g^k` and `1 ≤ H < X`, the
setting of Sections 1 and 2. -/
theorem lemma_1_7 : ∃ g₀ : ℕ, ∀ g b : ℕ, g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∃ C : ℝ,
    ∀ (k : ℕ) (H : ℝ), 1 ≤ H → H < ((g ^ k : ℕ) : ℝ) →
      ∫ α in (0 : ℝ)..1, ‖∑ n ∈ starSet g b (g ^ k) H, eC (n * α)‖ ≤
        C * ((starSet g b (g ^ k) H).card : ℝ) ^ thetaG g := by
  sorry

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
  sorry

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
