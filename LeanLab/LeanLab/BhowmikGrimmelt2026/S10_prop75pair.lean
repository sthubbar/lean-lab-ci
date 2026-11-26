/-
S10-06, burst-20261124, CLOUD S10. Target: `leaf_zero_pair` of SPLIT_prop75.lean,
P0029 Bhowmik and Grimmelt 2026, Proposition 7.5, double zero sum `𝒵` of display 7.16, page 28.

Verdict: the leaf is not provable from the paper. It is FALSE-CONDITIONAL in the following
sense, proved here as an implication: it forces the absence of a real zero `β > 1 - ϑ / 4`
whose own diagonal pair term is not cancelled by the other pairs.

For a real primitive character `χ̃` of conductor `r̃ ≤ R` with a real zero `β̃`, the diagonal
pair `(β̃, β̃)` of `𝒵` contributes `Σ_{q ≤ R} A_q(N; χ̃, χ̃) I_q^φ(N; β̃, β̃)`. By Lemma 7.6,
display 7.20 page 29, `I_q^φ` is `B_φ(β̃, β̃) N ^ (2β̃ - 1)` up to a smaller error, `B_φ > 0`
since `φ ≥ 0`, and by (8.1) page 30, proved in the lab as `facts81`, the completed `q` sum is
`χ̃(-1) 𝔖(N)` when `r̃ ∣ N`, with `𝔖(N) ≥ 1` for even `N`. So on the multiples of `r̃` in
`[X / 2, X]` that term has size at least `c N ^ (2β̃ - 1)`. The theorems below take that lower
bound for a sequence `S` and the statement that the rest `𝒵 - S` is small in mean square as
hypotheses, the second being exactly what a cancellation free reading of the other pairs gives,
and prove `4β̃ - 1 ≤ max (3 - ϑ) (13 / 5)`.

No new sorry, no new definition. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology Asymptotics

/-- A positive power of `Y` cannot stay below a constant times `log (2 Y) ^ 5` along the
multiples `Y = r k`. PROVED. -/
theorem no_power_le_log_S10 (ε K : ℝ) (hε : 0 < ε) (r : ℕ) (hr : 0 < r) (k₀ : ℕ)
    (h : ∀ k : ℕ, k₀ ≤ k → ((r * k : ℕ) : ℝ) ^ ε ≤ K * Real.log (2 * ((r * k : ℕ) : ℝ)) ^ 5) :
    False := by
  have lo := isLittleO_log_rpow_rpow_atTop (5 : ℝ) hε
  set δ : ℝ := 1 / (2 * (|K| + 1) * (2 : ℝ) ^ ε) with hδ
  have h2ε : 0 < (2 : ℝ) ^ ε := Real.rpow_pos_of_pos two_pos ε
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hev := lo.def hδ0
  have htend : Tendsto (fun k : ℕ => 2 * ((r * k : ℕ) : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun k : ℕ => r * k) atTop atTop := tendsto_id.const_mul_atTop' hr
    have h2 : Tendsto (fun k : ℕ => ((r * k : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp h1
    exact h2.const_mul_atTop two_pos
  have hk := (htend.eventually hev).and (eventually_ge_atTop (max k₀ 1))
  obtain ⟨k, hk1, hk2⟩ := hk.exists
  have hkk₀ : k₀ ≤ k := le_trans (le_max_left _ _) hk2
  have hk1' : 1 ≤ k := le_trans (le_max_right _ _) hk2
  set Y : ℝ := ((r * k : ℕ) : ℝ) with hY
  have hY1 : 1 ≤ Y := by
    rw [hY]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hY0 : 0 < Y := by linarith
  have hlog : 0 ≤ Real.log (2 * Y) := Real.log_nonneg (by linarith)
  have hmain := h k hkk₀
  simp only [Real.norm_eq_abs] at hk1
  rw [abs_of_nonneg (Real.rpow_nonneg hlog _), abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
    Real.mul_rpow (by norm_num) hY0.le] at hk1
  have h5 : Real.log (2 * Y) ^ (5 : ℝ) = Real.log (2 * Y) ^ (5 : ℕ) := by
    exact_mod_cast Real.rpow_natCast (Real.log (2 * Y)) 5
  rw [h5] at hk1
  have hYε : 0 < Y ^ ε := Real.rpow_pos_of_pos hY0 ε
  have hL5 : 0 ≤ Real.log (2 * Y) ^ 5 := pow_nonneg hlog 5
  have hK : K * Real.log (2 * Y) ^ 5 ≤ |K| * Real.log (2 * Y) ^ 5 :=
    mul_le_mul_of_nonneg_right (le_abs_self K) hL5
  have hdK : |K| * (δ * ((2 : ℝ) ^ ε * Y ^ ε)) < Y ^ ε := by
    have : |K| * (δ * ((2 : ℝ) ^ ε * Y ^ ε)) = (|K| / (2 * (|K| + 1))) * Y ^ ε := by
      rw [hδ]; field_simp
    rw [this]
    have hfrac : |K| / (2 * (|K| + 1)) < 1 := by
      rw [div_lt_one (by positivity)]; linarith [abs_nonneg K]
    nlinarith
  have := mul_le_mul_of_nonneg_left hk1 (abs_nonneg K)
  linarith

/-- What the leaf forces, abstract form. Let `S X N` be a part of the double zero sum such that
`S X N` has norm at least `c N ^ (2β - 1)` at every multiple `N = r j` of `r` in
`[X / 2, X]`, for `X = 2 r k` and `k` large, and such that the mean square over `N ≤ X` of
`S` obeys the bound of `leaf_zero_pair`. Then `4β - 1 ≤ max (3 - ϑ) (13 / 5)`. PROVED. -/
theorem exponent_forced_S10 (S : ℕ → ℕ → ℂ) (ϑ : ℝ) (r : ℕ) (hr : 0 < r) (β c : ℝ)
    (hc : 0 < c) (hβ : 1 / 2 ≤ β)
    (hlow : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ j ∈ Finset.Icc k (2 * k),
      c * ((r * j : ℕ) : ℝ) ^ (2 * β - 1) ≤ ‖S (2 * r * k) (r * j)‖)
    (hS : ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X, ‖S X N‖ ^ 2 ≤
        C * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5) :
    4 * β - 1 ≤ max (3 - ϑ) (13 / 5) := by
  by_contra hcon
  replace hcon := lt_of_not_ge hcon
  set m := max (3 - ϑ) (13 / 5 : ℝ) with hm
  set ε := 4 * β - 1 - m with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨k₀, hk₀⟩ := hlow
  obtain ⟨C, hC⟩ := hS
  set C' := max C 0 with hC'
  have hm0 : 0 ≤ m := le_trans (by norm_num) (le_max_right _ _)
  refine no_power_le_log_S10 ε (2 * C' * (2 : ℝ) ^ m * r / c ^ 2) hε r hr (max k₀ 1) ?_
  intro k hk
  have hkk₀ : k₀ ≤ k := le_trans (le_max_left _ _) hk
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
  have hX2 : 2 ≤ 2 * r * k := by
    have : 1 ≤ r * k := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    nlinarith
  set Y : ℝ := ((r * k : ℕ) : ℝ) with hY
  have hY1 : 1 ≤ Y := by
    rw [hY]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hY0 : 0 < Y := by linarith
  have hXY : ((2 * r * k : ℕ) : ℝ) = 2 * Y := by rw [hY]; push_cast; ring
  -- lower bound for the mean square
  have hsub : (Finset.Icc k (2 * k)).image (fun j => r * j) ⊆ Finset.Icc 1 (2 * r * k) := by
    intro N hN
    simp only [Finset.mem_image, Finset.mem_Icc] at hN ⊢
    obtain ⟨j, ⟨hj1, hj2⟩, rfl⟩ := hN
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    · calc r * j ≤ r * (2 * k) := Nat.mul_le_mul_left _ hj2
        _ = 2 * r * k := by ring
  have hinj : Set.InjOn (fun j => r * j) (Finset.Icc k (2 * k) : Set ℕ) := by
    intro a _ b _ hab; exact Nat.eq_of_mul_eq_mul_left hr hab
  have hlowsum : ∑ j ∈ Finset.Icc k (2 * k), ‖S (2 * r * k) (r * j)‖ ^ 2 ≤
      ∑ N ∈ Finset.Icc 1 (2 * r * k), ‖S (2 * r * k) N‖ ^ 2 := by
    rw [← Finset.sum_image (f := fun N => ‖S (2 * r * k) N‖ ^ 2) hinj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have hterm : ∀ j ∈ Finset.Icc k (2 * k),
      c ^ 2 * Y ^ (4 * β - 2) ≤ ‖S (2 * r * k) (r * j)‖ ^ 2 := by
    intro j hj
    have hl := hk₀ k hkk₀ j hj
    have hjk : k ≤ j := (Finset.mem_Icc.mp hj).1
    have hYj : Y ≤ ((r * j : ℕ) : ℝ) := by rw [hY]; exact_mod_cast Nat.mul_le_mul_left _ hjk
    have hpow : Y ^ (2 * β - 1) ≤ ((r * j : ℕ) : ℝ) ^ (2 * β - 1) :=
      Real.rpow_le_rpow hY0.le hYj (by linarith)
    have hp0 : 0 ≤ c * Y ^ (2 * β - 1) := by positivity
    have h1 : c * Y ^ (2 * β - 1) ≤ ‖S (2 * r * k) (r * j)‖ :=
      le_trans (mul_le_mul_of_nonneg_left hpow hc.le) hl
    have hsq : (c * Y ^ (2 * β - 1)) ^ 2 = c ^ 2 * Y ^ (4 * β - 2) := by
      have hYp : (Y ^ (2 * β - 1)) ^ 2 = Y ^ (4 * β - 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le]; congr 1; push_cast; ring
      rw [mul_pow, hYp]
    rw [← hsq]
    exact pow_le_pow_left₀ hp0 h1 2
  have hcount : ((k : ℝ)) * (c ^ 2 * Y ^ (4 * β - 2)) ≤
      ∑ j ∈ Finset.Icc k (2 * k), ‖S (2 * r * k) (r * j)‖ ^ 2 := by
    have := Finset.card_nsmul_le_sum _ _ _ hterm
    rw [nsmul_eq_mul, Nat.card_Icc] at this
    have hk' : (k : ℝ) ≤ ((2 * k + 1 - k : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have hnn : 0 ≤ c ^ 2 * Y ^ (4 * β - 2) := by positivity
    nlinarith
  -- upper bound
  have hup := hC (2 * r * k) hX2
  rw [hXY] at hup
  have h2Y1 : 1 ≤ 2 * Y := by linarith
  have hb1 : (2 * Y) ^ (3 - ϑ) ≤ (2 * Y) ^ m := Real.rpow_le_rpow_of_exponent_le h2Y1 (le_max_left _ _)
  have hb2 : (2 * Y) ^ (13 / 5 : ℝ) ≤ (2 * Y) ^ m :=
    Real.rpow_le_rpow_of_exponent_le h2Y1 (le_max_right _ _)
  have hlog : 0 ≤ Real.log (2 * Y) ^ 5 := pow_nonneg (Real.log_nonneg h2Y1) 5
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hup' : ∑ N ∈ Finset.Icc 1 (2 * r * k), ‖S (2 * r * k) N‖ ^ 2 ≤
      2 * C' * (2 * Y) ^ m * Real.log (2 * Y) ^ 5 := by
    have hA : 0 ≤ ((2 * Y) ^ (3 - ϑ) + (2 * Y) ^ (13 / 5 : ℝ)) * Real.log (2 * Y) ^ 5 := by
      positivity
    have e1 : C * ((2 * Y) ^ (3 - ϑ) + (2 * Y) ^ (13 / 5 : ℝ)) * Real.log (2 * Y) ^ 5 ≤
        C' * ((2 * Y) ^ (3 - ϑ) + (2 * Y) ^ (13 / 5 : ℝ)) * Real.log (2 * Y) ^ 5 := by
      rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hA
    have e2 : C' * ((2 * Y) ^ (3 - ϑ) + (2 * Y) ^ (13 / 5 : ℝ)) ≤ C' * (2 * (2 * Y) ^ m) :=
      mul_le_mul_of_nonneg_left (by linarith) hC'0
    have e3 := mul_le_mul_of_nonneg_right e2 hlog
    linarith
  -- combine: k c² Y^(4β-2) ≤ 2 C' 2^m Y^m log^5
  have hYm : (2 * Y) ^ m = (2 : ℝ) ^ m * Y ^ m := Real.mul_rpow (by norm_num) hY0.le
  have hkY : (k : ℝ) * Y ^ (4 * β - 2) = Y ^ (4 * β - 1) / r := by
    have hYr : Y = (r : ℝ) * k := by rw [hY]; push_cast; ring
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    rw [show (4 * β - 1) = (4 * β - 2) + 1 by ring, Real.rpow_add hY0, Real.rpow_one]
    rw [hYr]; field_simp
  have hsplit : Y ^ (4 * β - 1) = Y ^ ε * Y ^ m := by
    rw [← Real.rpow_add hY0, hεdef]; ring_nf
  have hall : Y ^ ε * Y ^ m / r * c ^ 2 ≤ 2 * C' * ((2 : ℝ) ^ m * Y ^ m) * Real.log (2 * Y) ^ 5 := by
    rw [← hsplit, ← hkY, ← hYm]
    calc (k : ℝ) * Y ^ (4 * β - 2) * c ^ 2 = (k : ℝ) * (c ^ 2 * Y ^ (4 * β - 2)) := by ring
      _ ≤ _ := le_trans hcount (le_trans hlowsum hup')
  have hYm0 : 0 < Y ^ m := Real.rpow_pos_of_pos hY0 m
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hc2 : 0 < c ^ 2 := by positivity
  rw [show (2 * ((r * k : ℕ) : ℝ)) = 2 * Y from rfl]
  have key : Y ^ ε * Y ^ m ≤ (2 * C' * (2 : ℝ) ^ m * r / c ^ 2 * Real.log (2 * Y) ^ 5) * Y ^ m := by
    have : Y ^ ε * Y ^ m / r * c ^ 2 * (r / c ^ 2) ≤
        2 * C' * ((2 : ℝ) ^ m * Y ^ m) * Real.log (2 * Y) ^ 5 * (r / c ^ 2) :=
      mul_le_mul_of_nonneg_right hall (by positivity)
    have l : Y ^ ε * Y ^ m / r * c ^ 2 * (r / c ^ 2) = Y ^ ε * Y ^ m := by
      field_simp
    have rr : 2 * C' * ((2 : ℝ) ^ m * Y ^ m) * Real.log (2 * Y) ^ 5 * (r / c ^ 2) =
        (2 * C' * (2 : ℝ) ^ m * r / c ^ 2 * Real.log (2 * Y) ^ 5) * Y ^ m := by
      field_simp
    linarith
  exact le_of_mul_le_mul_right key hYm0

/-- Application to the leaf. If `leaf_zero_pair` holds for `ϕ, G, ϑ`, and `𝒵` splits as
`S + E` with `E` obeying the same mean square bound and `S` the diagonal term of a real zero
`β` with the lower bound of `exponent_forced_S10`, then `4β - 1 ≤ max (3 - ϑ) (13 / 5)`; for
`ϑ ≤ 2 / 5` this is `β ≤ 1 - ϑ / 4`. PROVED as an implication from the body of the leaf. -/
theorem zero_pair_forces_S10 (ϕ G : ℝ → ℝ) (ϑ : ℝ)
    (hleaf : ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖Zterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2 ≤
        C * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5)
    (S : ℕ → ℕ → ℂ)
    (hrest : ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖Zterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) - S X N‖ ^ 2 ≤
        C * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5)
    (r : ℕ) (hr : 0 < r) (β c : ℝ) (hc : 0 < c) (hβ : 1 / 2 ≤ β)
    (hlow : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ j ∈ Finset.Icc k (2 * k),
      c * ((r * j : ℕ) : ℝ) ^ (2 * β - 1) ≤ ‖S (2 * r * k) (r * j)‖) :
    4 * β - 1 ≤ max (3 - ϑ) (13 / 5) := by
  refine exponent_forced_S10 S ϑ r hr β c hc hβ hlow ?_
  obtain ⟨C₁, h₁⟩ := hleaf
  obtain ⟨C₂, h₂⟩ := hrest
  refine ⟨2 * C₁ + 2 * C₂, fun X hX => ?_⟩
  set Z := fun N : ℕ => Zterm ϕ G N ((X : ℝ) ^ ϑ)
    (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) with hZ
  have hpt : ∀ N ∈ Finset.Icc 1 X, ‖S X N‖ ^ 2 ≤ 2 * ‖Z N‖ ^ 2 + 2 * ‖Z N - S X N‖ ^ 2 := by
    intro N _
    have h : ‖S X N‖ ≤ ‖Z N‖ + ‖Z N - S X N‖ := by
      have := norm_sub_le (Z N) (Z N - S X N)
      simpa using this
    have h0 : 0 ≤ ‖S X N‖ := norm_nonneg _
    have hsq : ‖S X N‖ ^ 2 ≤ (‖Z N‖ + ‖Z N - S X N‖) ^ 2 := by
      rw [pow_two, pow_two]; exact mul_le_mul h h h0 (by positivity)
    nlinarith [sq_nonneg (‖Z N‖ - ‖Z N - S X N‖)]
  calc ∑ N ∈ Finset.Icc 1 X, ‖S X N‖ ^ 2
      ≤ ∑ N ∈ Finset.Icc 1 X, (2 * ‖Z N‖ ^ 2 + 2 * ‖Z N - S X N‖ ^ 2) :=
        Finset.sum_le_sum hpt
    _ = 2 * ∑ N ∈ Finset.Icc 1 X, ‖Z N‖ ^ 2 + 2 * ∑ N ∈ Finset.Icc 1 X, ‖Z N - S X N‖ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := by
        have a := h₁ X hX
        have b := h₂ X hX
        simp only [hZ] at a b ⊢
        nlinarith [a, b]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.no_power_le_log_S10
#print axioms LeanLab.BhowmikGrimmelt2026.exponent_forced_S10
#print axioms LeanLab.BhowmikGrimmelt2026.zero_pair_forces_S10
