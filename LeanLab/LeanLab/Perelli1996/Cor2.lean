/-
P0083 Perelli 1996, Corollary 2, page 479, from Theorem 2, in encoding A.
PC run 20261020T0503Z-11094, unit U-1177. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN.

The paper calls Corollary 2 an easy consequence of Theorem 2. The route here:
* `CF_ge`: `C(F) ≥ 𝔖/2 > 0` when `ρ_F(2) ≠ 0`, since `a_k ≥ 1` and every factor of the product is `≥ 1`;
* `R_bad_le`: if `m` is not an even Goldbach number then `R(m) ≤ 2 (#PP(m) + #E(m)) log² m`, with
  `PP` the proper prime powers and `E` the even prime powers up to `m`; so `R(m) ≪ √m log³ m`;
* `poly_upper`: `F(n) ≤ (3/2) a_k n^k` for large `n`, so `F(n) ≪ N` on the window;
* `corollary2_of_theorem2`: if no `n` in the window gave an even Goldbach `F(n)`, the window sum
  of `R(F(n))` would be `≪ H √N log³ N`, against Theorem 2's `C(F) H N (1 + o(1))`.
So Corollary 2 is CONDITIONAL ON Theorem 2 only.
-/
import LeanLab.Perelli1996.Merge

namespace LeanLab.Perelli1996
-- 2026-10-28 architect: encoding A now lives in StatementsA, namespace EncA
open LeanLab.Perelli1996.EncA
open Finset Real Polynomial Filter Topology Asymptotics
open scoped ArithmeticFunction.vonMangoldt

attribute [local instance] Classical.propDecidable

/-! ### `C(F) > 0` -/

theorem tprod_ge_one {ι : Type*} (f : ι → ℝ) (hf : ∀ i, 1 ≤ f i) : 1 ≤ ∏' i, f i := by
  by_cases hm : Multipliable f
  · apply ge_of_tendsto hm.hasProd
    filter_upwards with S
    calc (1 : ℝ) = ∏ i ∈ S, (1 : ℝ) := by simp
      _ ≤ ∏ i ∈ S, f i := by gcongr with i hi; exact hf i
  · rw [tprod_eq_one_of_not_multipliable hm]

theorem CF_ge {F : ℤ[X]} (hF : Admissible F) (hrho : rhoF F 2 ≠ 0) : SingConst / 2 ≤ CF F := by
  unfold CF
  have ha : (1 : ℝ) ≤ (F.leadingCoeff : ℝ) := by exact_mod_cast hF.2
  have hr : (1 : ℝ) / 2 ≤ (rhoF F 2 : ℝ) / 2 := by
    have : (1 : ℝ) ≤ rhoF F 2 := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hrho
    linarith
  have hP : (1 : ℝ) ≤ ∏' p : {p : ℕ // p.Prime ∧ 2 < p},
      (1 + (rhoF F p : ℝ) / ((p : ℝ) * ((p : ℝ) - 2))) := by
    apply tprod_ge_one
    intro p
    have h2 : (2 : ℝ) < p := by exact_mod_cast p.2.2
    have : (0 : ℝ) ≤ (rhoF F p : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)) := by
      apply div_nonneg (Nat.cast_nonneg _); apply mul_nonneg <;> linarith
    linarith
  have hS := SingConst_pos
  calc SingConst / 2 = 1 * (1 / 2) * SingConst * 1 := by ring
    _ ≤ (F.leadingCoeff : ℝ) * ((rhoF F 2 : ℝ) / 2) * SingConst * _ := by
        gcongr

theorem CF_pos {F : ℤ[X]} (hF : Admissible F) (hrho : rhoF F 2 ≠ 0) : 0 < CF F :=
  lt_of_lt_of_le (by have := SingConst_pos; linarith) (CF_ge hF hrho)

/-! ### `R(m)` is small unless `m` is an even Goldbach number -/

/-- Prime powers up to `m` that are not odd primes. -/
def Q (m : ℕ) : Finset ℕ :=
  (range (m + 1)).filter (fun k => IsPrimePow k ∧ (¬ k.Prime ∨ Even k))

theorem card_Q_le (m : ℕ) :
    ((Q m).card : ℝ) ≤ ((Nat.sqrt m + 1) * (Nat.log 2 m + 1) : ℕ) + (Nat.log 2 m + 1 : ℕ) := by
  have hsub : Q m ⊆ B.PP m ∪ (range (Nat.log 2 m + 1)).image (fun j => 2 ^ j) := by
    intro k hk
    simp only [Q, mem_filter, mem_range] at hk
    obtain ⟨hkm, hpp, h⟩ := hk
    rcases h with h | h
    · apply mem_union_left
      simp only [B.PP, mem_filter, mem_range]; exact ⟨hkm, hpp, h⟩
    · apply mem_union_right
      obtain ⟨p, j, hp, hj, rfl⟩ := hpp
      have hp' := hp.nat_prime
      have h2 : p = 2 := by
        rcases hp'.eq_two_or_odd' with h2 | hodd
        · exact h2
        · exfalso; exact (Nat.not_even_iff_odd.2 (hodd.pow)) h
      subst h2
      refine mem_image.2 ⟨j, mem_range.2 ?_, rfl⟩
      have : 2 ^ j ≤ m := by omega
      have := Nat.le_log_of_pow_le (by norm_num) this
      omega
  have h1 := card_le_card hsub
  have h2 := card_union_le (B.PP m) ((range (Nat.log 2 m + 1)).image (fun j => 2 ^ j))
  have h3 := card_image_le (s := range (Nat.log 2 m + 1)) (f := fun j => 2 ^ j)
  have h4 := B.card_PP_le m
  simp only [card_range] at h3
  have : (Q m).card ≤ (Nat.sqrt m + 1) * (Nat.log 2 m + 1) + (Nat.log 2 m + 1) := by omega
  exact_mod_cast this

theorem R_bad_le {m : ℕ} (hm : ¬ (Even m ∧ IsGoldbachSum m)) :
    R m ≤ 2 * ((Q m).card : ℝ) * Real.log m ^ 2 := by
  rw [R_eq_B, B.R_eq]
  set L := Real.log m
  have hL : 0 ≤ L := Real.log_natCast_nonneg m
  have hterm : ∀ k ∈ range (m + 1), Λ k * Λ (m - k) ≤
      ((if k ∈ Q m then 1 else 0) + (if m - k ∈ Q m then 1 else 0)) * L ^ 2 := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hΛk : Λ k ≤ L := le_trans ArithmeticFunction.vonMangoldt_le_log
      (B.log_nat_mono (by omega))
    have hΛs : Λ (m - k) ≤ L := le_trans ArithmeticFunction.vonMangoldt_le_log
      (B.log_nat_mono (Nat.sub_le m k))
    have h0k := ArithmeticFunction.vonMangoldt_nonneg (n := k)
    have h0s := ArithmeticFunction.vonMangoldt_nonneg (n := m - k)
    by_cases hz : Λ k * Λ (m - k) = 0
    · rw [hz]; positivity
    · have hk0 : Λ k ≠ 0 := left_ne_zero_of_mul hz
      have hs0 : Λ (m - k) ≠ 0 := right_ne_zero_of_mul hz
      have hpk : IsPrimePow k := ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hk0
      have hps : IsPrimePow (m - k) := ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hs0
      have hone : (¬ k.Prime ∨ Even k) ∨ (¬ (m - k).Prime ∨ Even (m - k)) := by
        by_contra h
        simp only [not_or, not_not, Nat.not_even_iff_odd] at h
        obtain ⟨⟨hkp, hko⟩, hsp, hso⟩ := h
        apply hm
        refine ⟨?_, ⟨k, m - k, hkp, hsp, by omega⟩⟩
        have : m = k + (m - k) := by omega
        rw [this]; exact hko.add_odd hso
      have hprod : Λ k * Λ (m - k) ≤ L ^ 2 := by
        rw [sq]; exact mul_le_mul hΛk hΛs h0s hL
      rcases hone with h | h
      · have : k ∈ Q m := by
          simp only [Q, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hpk, h⟩
        rw [if_pos this]
        have : (0 : ℝ) ≤ (if m - k ∈ Q m then 1 else 0) := by split_ifs <;> norm_num
        nlinarith [sq_nonneg L]
      · have : m - k ∈ Q m := by
          simp only [Q, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hps, h⟩
        rw [if_pos this]
        have : (0 : ℝ) ≤ (if k ∈ Q m then 1 else 0) := by split_ifs <;> norm_num
        nlinarith [sq_nonneg L]
  calc ∑ k ∈ range (m + 1), Λ k * Λ (m - k)
      ≤ ∑ k ∈ range (m + 1), ((if k ∈ Q m then 1 else 0) +
          (if m - k ∈ Q m then 1 else 0)) * L ^ 2 := Finset.sum_le_sum hterm
    _ = ((∑ k ∈ range (m + 1), (if k ∈ Q m then (1 : ℝ) else 0)) +
          ∑ k ∈ range (m + 1), (if m - k ∈ Q m then (1 : ℝ) else 0)) * L ^ 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_mul]
    _ = 2 * ((Q m).card : ℝ) * L ^ 2 := by
        have h1 : ∑ k ∈ range (m + 1), (if k ∈ Q m then (1 : ℝ) else 0) = (Q m).card := by
          rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one]
          congr 2
          exact Finset.inter_eq_right.2 (Finset.filter_subset _ _)
        have h2 : ∑ k ∈ range (m + 1), (if m - k ∈ Q m then (1 : ℝ) else 0) =
            ∑ k ∈ range (m + 1), (if k ∈ Q m then (1 : ℝ) else 0) := by
          rw [← Finset.sum_range_reflect]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mem_range] at hk
          congr 2
          omega
        rw [h2, h1]; ring

/-- The growth function `g(X) = 2 (√X + 2)(2 log X + 1) log² X`. -/
noncomputable def gB (X : ℝ) : ℝ := 2 * (Real.sqrt X + 2) * (2 * Real.log X + 1) * Real.log X ^ 2

theorem R_bad_le_g {m : ℕ} (hm1 : 1 ≤ m) (hm : ¬ (Even m ∧ IsGoldbachSum m)) :
    R m ≤ gB m := by
  refine (R_bad_le hm).trans ?_
  have hc := card_Q_le m
  have hl := B.natLog_le m hm1
  have hs : ((Nat.sqrt m : ℕ) : ℝ) ≤ Real.sqrt m := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    exact_mod_cast Nat.sqrt_le' m
  have hL : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have hsq : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have hQ : ((Q m).card : ℝ) ≤ (Real.sqrt m + 2) * (2 * Real.log m + 1) := by
    refine hc.trans ?_
    push_cast
    have h1 : ((Nat.sqrt m : ℝ) + 1) * ((Nat.log 2 m : ℝ) + 1) ≤
        (Real.sqrt m + 1) * (2 * Real.log m + 1) := by
      apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    nlinarith
  unfold gB
  have := mul_le_mul_of_nonneg_right hQ (sq_nonneg (Real.log m))
  nlinarith

theorem gB_mono {x X : ℝ} (hx : 1 ≤ x) (hxX : x ≤ X) : gB x ≤ gB X := by
  unfold gB
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlX : Real.log x ≤ Real.log X := Real.log_le_log (by linarith) hxX
  have hs : Real.sqrt x ≤ Real.sqrt X := Real.sqrt_le_sqrt hxX
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have h2 : Real.log x ^ 2 ≤ Real.log X ^ 2 := pow_le_pow_left₀ hl hlX 2
  have : 2 * (Real.sqrt x + 2) * (2 * Real.log x + 1) ≤ 2 * (Real.sqrt X + 2) * (2 * Real.log X + 1) := by
    apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have hlX0 : 0 ≤ Real.log X := le_trans hl hlX
  have hsX : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
  exact mul_le_mul this h2 (sq_nonneg _) (by positivity)

theorem gB_nonneg {X : ℝ} (hX : 1 ≤ X) : 0 ≤ gB X := by
  unfold gB
  have := Real.log_nonneg hX
  positivity

/-- `R(m) ≤ g(X)` for every `m ≤ X`, `X ≥ 1`, unless `m` is an even Goldbach number. -/
theorem R_bad_le_gX {m : ℕ} {X : ℝ} (hX : 1 ≤ X) (hmX : (m : ℝ) ≤ X)
    (hm : ¬ (Even m ∧ IsGoldbachSum m)) : R m ≤ gB X := by
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · have : R 0 = 0 := by
      rw [R_eq_B, B.R_eq]; simp
    rw [this]; exact gB_nonneg hX
  · exact (R_bad_le_g hm1 hm).trans (gB_mono (by exact_mod_cast hm1) hmX)

/-- `g(X) = o(X)`: for every `η > 0`, eventually `g(X) ≤ η X`. -/
theorem gB_small {η : ℝ} (hη : 0 < η) : ∀ᶠ X in atTop, gB X ≤ η * X := by
  have hlo := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by positivity : (0 : ℝ) < η / 18)
  filter_upwards [hlo, eventually_ge_atTop (4 : ℝ)] with X hX h4
  have hX0 : 0 < X := by linarith
  have hlog1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    have := Real.exp_one_lt_d9; linarith
  have hs2 : 2 ≤ Real.sqrt X := by
    rw [Real.le_sqrt (by norm_num) hX0.le]; linarith
  have hsqrt : Real.sqrt X = X ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow X
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)] at hX
  have hl3 : Real.log X ^ (3 : ℝ) = Real.log X ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hl3, ← hsqrt] at hX
  have hb : gB X ≤ 18 * Real.sqrt X * Real.log X ^ 3 := by
    unfold gB
    have h1 : Real.sqrt X + 2 ≤ 2 * Real.sqrt X := by linarith
    have h2 : 2 * Real.log X + 1 ≤ 3 * Real.log X := by linarith
    have hp : 0 ≤ Real.log X ^ 2 := sq_nonneg _
    calc 2 * (Real.sqrt X + 2) * (2 * Real.log X + 1) * Real.log X ^ 2
        ≤ 2 * (2 * Real.sqrt X) * (3 * Real.log X) * Real.log X ^ 2 := by gcongr
      _ = 12 * Real.sqrt X * Real.log X ^ 3 := by ring
      _ ≤ 18 * Real.sqrt X * Real.log X ^ 3 := by
          have : 0 ≤ Real.sqrt X * Real.log X ^ 3 := by positivity
          nlinarith
  have hss : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  calc gB X ≤ 18 * Real.sqrt X * Real.log X ^ 3 := hb
    _ ≤ 18 * Real.sqrt X * (η / 18 * Real.sqrt X) := by gcongr
    _ = η * (Real.sqrt X * Real.sqrt X) := by ring
    _ = η * X := by rw [hss]

/-- The window `[x, x + H]` holds at most `H + 1` integers. -/
theorem card_nRange_le {x H : ℝ} (hx : 0 ≤ x) (hH : 0 ≤ H) :
    ((nRange x H).card : ℝ) ≤ H + 1 := by
  unfold nRange
  rw [Nat.card_Icc]
  have h1 : (⌊x + H⌋₊ : ℝ) ≤ x + H := Nat.floor_le (by linarith)
  have h2 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  rcases Nat.lt_or_ge (⌊x + H⌋₊ + 1) ⌈x⌉₊ with h | h
  · rw [Nat.sub_eq_zero_of_le h.le]; push_cast; linarith
  · rw [Nat.cast_sub h]; push_cast; linarith

/-- **Growth on the window, upper**: `F(n) ≤ (3/2) a_k n^k` for large `n`. -/
theorem poly_upper (F : ℤ[X]) (hF : Admissible F) :
    ∃ X₀ : ℝ, 0 ≤ X₀ ∧ ∀ n : ℕ, X₀ ≤ n →
      (Fn F n : ℝ) ≤ 3 / 2 * (F.leadingCoeff : ℝ) * (n : ℝ) ^ F.natDegree := by
  set G := F.map (Int.castRingHom ℝ) with hGdef
  have hinj : Function.Injective (Int.castRingHom ℝ) := (Int.castRingHom ℝ).injective_int
  have hdeg : G.natDegree = F.natDegree := natDegree_map_eq_of_injective hinj F
  have hlc : G.leadingCoeff = (F.leadingCoeff : ℝ) := leadingCoeff_map_of_injective hinj F
  have hlc1 : (1 : ℝ) ≤ F.leadingCoeff := by exact_mod_cast hF.2
  have hE := (isEquivalent_atTop_lead (P := G)).isLittleO.bound (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 hE
  refine ⟨max X 1, by positivity, fun n hn => ?_⟩
  have hnX : X ≤ (n : ℝ) := le_trans (le_max_left _ _) hn
  have hn1 : (1 : ℝ) ≤ n := le_trans (le_max_right _ _) hn
  have hb := hX n hnX
  rw [hdeg, hlc] at hb
  have hev : eval (n : ℝ) G = (B.Fv F n : ℝ) := by
    have := eval_intCast_map (Int.castRingHom ℝ) F (n : ℤ)
    simp [B.Fv, hGdef]
  simp only [Pi.sub_apply, hev, Real.norm_eq_abs] at hb
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ F.natDegree := one_le_pow₀ hn1
  have hv : 0 < (F.leadingCoeff : ℝ) * (n : ℝ) ^ F.natDegree := by positivity
  rw [abs_of_pos hv] at hb
  have hup := (abs_le.1 hb).2
  have hFv : (B.Fv F n : ℝ) ≤ 3 / 2 * (F.leadingCoeff : ℝ) * (n : ℝ) ^ F.natDegree := by
    nlinarith
  rcases le_or_gt 0 (B.Fv F n) with h0 | h0
  · have : (Fn F n : ℝ) = (B.Fv F n : ℝ) := by
      rw [Fn_eq]; exact_mod_cast Int.toNat_of_nonneg h0
    rw [this]; exact hFv
  · have : Fn F n = 0 := by rw [Fn_eq]; omega
    rw [this]; push_cast; positivity

/-- **Corollary 2 from Theorem 2**, page 479: CONDITIONAL ON Theorem 2 for `F` only. -/
theorem corollary2_of_theorem2 {F : ℤ[X]} (h : Theorem2 F) : Corollary2 F := by
  intro hF hrho ε hε
  obtain ⟨C, N0, hC⟩ := h hF 1 ε one_pos hε
  obtain ⟨X₀, hX₀, hX⟩ := poly_upper F hF
  set k := F.natDegree with hk
  have hk0 : k ≠ 0 := by have := hF.1; omega
  have hdeg : deg F = (k : ℝ) := rfl
  set a := (F.leadingCoeff : ℝ) with ha
  have ha1 : (1 : ℝ) ≤ a := by rw [ha]; exact_mod_cast hF.2
  set K := 3 / 2 * a * 2 ^ k with hK
  have hK1 : 1 ≤ K := by
    have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have : (1 : ℝ) ≤ a * 2 ^ k := by nlinarith
    nlinarith
  set c0 := SingConst / 2 with hc0
  have hc0pos : 0 < c0 := by have := SingConst_pos; positivity
  have hCF := CF_ge hF hrho
  -- eventually `C / log N < c0/4`
  have htend : Tendsto (fun N : ℝ => C / Real.log N) atTop (𝓝 0) := by
    have := (Real.tendsto_log_atTop).inv_tendsto_atTop
    simpa [div_eq_mul_inv] using this.const_mul C
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 (htend.eventually (gt_mem_nhds (by positivity :
    (0 : ℝ) < c0 / 4)))
  -- eventually `g(K N) ≤ (c0/4) N`
  have hgs := gB_small (η := c0 / (4 * K)) (by positivity)
  have hKN : Tendsto (fun N : ℝ => K * N) atTop atTop :=
    tendsto_id.const_mul_atTop (by linarith)
  obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.1 (hKN.eventually hgs)
  refine ⟨max (max N0 N₂) (max N₃ (max (X₀ ^ k) 2)), fun N H hN h1 h2 => ?_⟩
  have hN0 : N0 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNX : X₀ ^ k ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hN2' : 2 ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNpos : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hroot0 : 0 ≤ N ^ (1 / (k : ℝ)) := Real.rpow_nonneg hNpos.le _
  -- `H ≥ 1` and `H ≤ N^{1/k}`
  have hH1 : 1 ≤ H := by
    refine le_trans ?_ h1
    exact Real.one_le_rpow (by linarith) (by rw [hdeg]; positivity)
  have hHroot : H ≤ N ^ (1 / (k : ℝ)) := by
    refine h2.trans ?_
    rw [hdeg]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  -- every `n` in the window has `F(n) ≤ K N`
  have hFle : ∀ n ∈ nRange (N ^ (1 / deg F)) H, (Fn F n : ℝ) ≤ K * N := by
    intro n hn
    simp only [nRange, Finset.mem_Icc] at hn
    rw [hdeg] at hn
    have hlo : N ^ (1 / (k : ℝ)) ≤ n := le_trans (Nat.le_ceil _) (by exact_mod_cast hn.1)
    have hhi : (n : ℝ) ≤ 2 * N ^ (1 / (k : ℝ)) := by
      have : (n : ℝ) ≤ N ^ (1 / (k : ℝ)) + H :=
        le_trans (by exact_mod_cast hn.2) (Nat.floor_le (by linarith))
      linarith
    have hXn : X₀ ≤ n := by
      have := Real.rpow_le_rpow (by positivity) hNX (by positivity : (0 : ℝ) ≤ 1 / (k : ℝ))
      rw [one_div, Real.pow_rpow_inv_natCast hX₀ hk0] at this
      rw [one_div] at hlo
      linarith
    have hpow : (n : ℝ) ^ k ≤ 2 ^ k * N := by
      have := pow_le_pow_left₀ (Nat.cast_nonneg n) hhi k
      rw [mul_pow, B.rpow_k N hNpos.le k hk0] at this
      exact this
    calc (Fn F n : ℝ) ≤ 3 / 2 * a * (n : ℝ) ^ k := hX n hXn
      _ ≤ 3 / 2 * a * (2 ^ k * N) := by gcongr
      _ = K * N := by rw [hK]; ring
  -- by contradiction
  by_contra hno
  push Not at hno
  have hbad : ∀ n ∈ nRange (N ^ (1 / deg F)) H, R (Fn F n) ≤ gB (K * N) := by
    intro n hn
    apply R_bad_le_gX (by nlinarith) (hFle n hn)
    rintro ⟨he, hg⟩
    exact hno n hn he hg
  have hsum_le : ∑ n ∈ nRange (N ^ (1 / deg F)) H, R (Fn F n) ≤ 2 * H * gB (K * N) := by
    calc ∑ n ∈ nRange (N ^ (1 / deg F)) H, R (Fn F n)
        ≤ ∑ n ∈ nRange (N ^ (1 / deg F)) H, gB (K * N) := Finset.sum_le_sum hbad
      _ = ((nRange (N ^ (1 / deg F)) H).card : ℝ) * gB (K * N) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (H + 1) * gB (K * N) := by
          apply mul_le_mul_of_nonneg_right _ (gB_nonneg (by nlinarith))
          exact card_nRange_le (by rw [hdeg]; exact hroot0) (by linarith)
      _ ≤ 2 * H * gB (K * N) := by
          apply mul_le_mul_of_nonneg_right (by linarith) (gB_nonneg (by nlinarith))
  have hg : gB (K * N) ≤ c0 / 4 * N := by
    have := hN₃ N hN3
    calc gB (K * N) ≤ c0 / (4 * K) * (K * N) := this
      _ = c0 / 4 * N := by field_simp
  have hmain := hC N H hN0 h1 h2
  rw [Real.rpow_one] at hmain
  have hlow : CF F * H * N - C * H * N / Real.log N ≤
      ∑ n ∈ nRange (N ^ (1 / deg F)) H, R (Fn F n) := by
    have := (abs_le.1 hmain).1; linarith
  have hCl : C / Real.log N < c0 / 4 := hN₂ N hN2
  have hHN : 0 < H * N := by positivity
  have e1 : C * H * N / Real.log N = (C / Real.log N) * (H * N) := by ring
  have e2 : CF F * H * N = CF F * (H * N) := by ring
  rw [e1, e2] at hlow
  have h3 : c0 * (H * N) ≤ CF F * (H * N) := mul_le_mul_of_nonneg_right hCF hHN.le
  have h4 : (C / Real.log N) * (H * N) ≤ c0 / 4 * (H * N) :=
    mul_le_mul_of_nonneg_right hCl.le hHN.le
  have h5 : 2 * H * gB (K * N) ≤ 2 * H * (c0 / 4 * N) :=
    mul_le_mul_of_nonneg_left hg (by linarith)
  nlinarith

/-- Vacuity: `F = X` is admissible with `ρ_F(2) = 1`, so `corollary2_of_theorem2` applies to it. -/
theorem vacuity_cor2 : Admissible (X : ℤ[X]) ∧ rhoF (X : ℤ[X]) 2 ≠ 0 := vacuity_merge

end LeanLab.Perelli1996
