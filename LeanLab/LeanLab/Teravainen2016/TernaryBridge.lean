/-
P0076 J. Teräväinen, arXiv 1611.08585, Remark 3.6: the ternary deduction of Theorem 1.2 from
Matomäki and Shao, Theorem 2.3, Proposition 3.2 as printed, and one RECONSTRUCTED input,
`Prop33Cross`, the restriction estimate of Proposition 3.3 for the function (3.4) at scale `L`
read on `ℤ_M` with `L ≤ M ≤ 2L`. Remark 3.6 gives no ternary statement; a three term sum of
points of `(N/3, 2N/3)` is never `≡ 0 (mod N)`, so the printed Propositions 3.2 and 3.3 at one
scale `N` cannot feed Theorem 2.3 at the point `N` directly, see `ternary_support_obstruction`.
Here `f₁` is (3.4) at scale `L'' = ⌊3M/5⌋` and `f₂`, `f₃` at scale `L = 3⌈M/4⌉ - 1`, all read
on `ℤ_M`, which is how Proposition 3.2, valid for every bounded complexity `χ : ℤ → ℝ≥0`, gives
conditions (2.2) and (2.3) of Theorem 2.3 with zero sorry.
AI-written Lean code, Claude, session 20261020T2317Z-cloud53, unit U-6761.
Checked only by the Lean kernel. Binary Goldbach is OPEN; ternary Goldbach is a theorem,
Helfgott 2013.
-/
import Mathlib
import LeanLab.Teravainen2016.TernaryCounting

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- Three points of `(N/3, 2N/3)` never sum to a multiple of `N`; why Remark 3.6 needs the
supports changed. -/
theorem ternary_support_obstruction {N a b c : ℕ} (ha : N < 3 * a ∧ 3 * a < 2 * N)
    (hb : N < 3 * b ∧ 3 * b < 2 * N) (hc : N < 3 * c ∧ 3 * c < 2 * N) : ¬ N ∣ a + b + c := by
  rintro ⟨q, hq⟩
  rcases Nat.lt_or_ge q 2 with h | h
  · interval_cases q <;> omega
  · have : N * 2 ≤ N * q := Nat.mul_le_mul_left N h
    omega

/-- **RECONSTRUCTED hypothesis**: Proposition 3.3 for `g ≤ f` with `f` the function (3.4) at
scale `L`, the Fourier transform taken on `ℤ_M`, `L ≤ M ≤ 2L`. For `M = L` it is `Prop33`. -/
def Prop33Cross : Prop :=
  ∀ r : ℝ, 2 < r → ∃ K : ℝ, 0 < K ∧ ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
    0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ L M : ℕ, 1 ≤ L → L ≤ M → M ≤ 2 * L →
    ∀ g : ℕ → ℝ, (∀ n, 0 ≤ g n) → (∀ n < M, g n ≤ fW (WW J w) b L n) →
    ∑ ξ ∈ range M, ‖fhat M g ξ‖ ^ r ≤ K

theorem prop33_of_cross (h : Prop33Cross) : Prop33 := by
  intro r hr
  obtain ⟨K, hK, H⟩ := h r hr
  exact ⟨K, hK, fun J w hJ hw b hb hb' hA N hN g hg hgf =>
    H J w hJ hw b hb hb' hA N N hN le_rfl (by omega) g hg hgf⟩

/-- `StepI` with a general summation set `D ⊆ ℤ_M` that covers `t + [0, M/10]` or
`t - [0, M/10]`. PROVED. -/
theorem stepGen (M : ℕ) (Ω : Finset ℕ) (η : ℝ) (χ : ℤ → ℝ) (f : ℕ → ℝ) (D : Finset ℕ)
    (δ₀ Y : ℝ) (tn : ℕ) (hM : 2 ≤ M) (hχ : ChiProps M Ω η χ) (h1Ω : 1 % M ∈ Ω) (hη0 : 0 < η)
    (hη : η ≤ 1 / 20) (hδ₀ : 0 < δ₀) (hD : D ⊆ range M) (_hf : ∀ n, 0 ≤ f n)
    (hfs : ∀ n < M, f n ≠ 0 → n ∈ D)
    (hcov : (∀ m, 10 * m ≤ M → tn + m ∈ D) ∨ (∀ m, 10 * m ≤ M → m ≤ tn ∧ tn - m ∈ D))
    (hY : Y ≤ M * chiNorm M χ / 4)
    (hb : δ₀ * (∑ n ∈ D, χ ((tn : ℤ) - n) - Y) ≤ ∑ n ∈ D, f n * χ ((tn : ℤ) - n)) :
    δ₀ / 20 * chiNorm M χ ≤ convChi M f χ tn := by
  obtain ⟨hnn, hsym, hper, -, hfar, hnorm⟩ := hχ
  set k := Ω.card with hkdef
  have hk : k ≠ 0 := (card_pos.mpr ⟨_, h1Ω⟩).ne'
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by linarith
  set X' := ∑ n ∈ range M, χ n with hX'def
  have hX'0 : 0 ≤ X' := sum_nonneg fun n _ => hnn n
  have hX' : chiNorm M χ = X' / M := by unfold chiNorm; rw [inv_mul_eq_div]
  have hconv : convChi M f χ tn = (M : ℝ)⁻¹ * ∑ n ∈ D, f n * χ ((tn : ℤ) - n) := by
    unfold convChi
    congr 1
    symm
    apply sum_subset hD
    intro n hn hnd
    have : f n = 0 := by
      by_contra h0
      exact hnd (hfs n (mem_range.mp hn) h0)
    rw [this, zero_mul]
  -- points far from `0` lie outside `B(Ω, 2η)`
  have h1 : 1 % M = 1 := Nat.mod_eq_of_lt (by omega)
  have hfarpt : ∀ n < M, M < 10 * n → M < 10 * (M - n) → χ n ≤ (η ^ 2 / 8) ^ k := by
    intro n hn h1n h2n
    apply hfar n hn
    intro hB
    have hd := hB 1 (by rwa [h1] at h1Ω)
    simp only [Nat.cast_one, one_mul] at hd
    have hnr : (n : ℝ) < M := by exact_mod_cast hn
    have hx0 : (0 : ℝ) ≤ (n : ℝ) / M := by positivity
    have hx1 : (n : ℝ) / M ≤ 1 := by rw [div_le_one hMpos]; exact hnr.le
    have hm := distInt_ge_min hx0 hx1
    have e1 : (1 : ℝ) / 10 < (n : ℝ) / M := by
      rw [lt_div_iff₀ hMpos]
      have : (M : ℝ) < 10 * n := by exact_mod_cast h1n
      linarith
    have e2 : (1 : ℝ) / 10 < 1 - (n : ℝ) / M := by
      have h3 : (M : ℝ) < 10 * ((M - n : ℕ) : ℝ) := by exact_mod_cast h2n
      rw [Nat.cast_sub hn.le] at h3
      have : (n : ℝ) / M < 9 / 10 := by rw [div_lt_iff₀ hMpos]; linarith
      linarith
    have := lt_min e1 e2
    linarith
  set L := M / 10 with hL
  set A := ∑ m ∈ range (L + 1), χ m with hAdef
  -- `X' ≤ 2 A + M (η²/8)^k`
  have hsplit : X' ≤ 2 * A + M * (η ^ 2 / 8) ^ k := by
    have hpt : ∀ n ∈ range M, χ n ≤ ((if 10 * n ≤ M then χ n else 0) +
        (if 10 * (M - n) ≤ M ∧ M < 10 * n then χ n else 0)) + (η ^ 2 / 8) ^ k := by
      intro n hn
      rw [mem_range] at hn
      have hc : 0 ≤ (η ^ 2 / 8) ^ k := by positivity
      have hn0 := hnn n
      by_cases h1n : 10 * n ≤ M
      · rw [if_pos h1n]
        split_ifs <;> linarith
      · rw [if_neg h1n]
        by_cases h2n : 10 * (M - n) ≤ M
        · rw [if_pos ⟨h2n, by omega⟩]; linarith
        · rw [if_neg (fun h => h2n h.1)]
          have := hfarpt n hn (by omega) (by omega)
          linarith
    have hs := sum_le_sum hpt
    rw [sum_add_distrib, sum_add_distrib, ← sum_filter, ← sum_filter, sum_const, card_range,
      nsmul_eq_mul] at hs
    have hA1 : ∑ n ∈ (range M).filter (fun n => 10 * n ≤ M), χ n ≤ A := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        simp only [mem_filter, mem_range] at hn ⊢
        omega
      · intro n _ _; exact hnn n
    have hA2 : ∑ n ∈ (range M).filter (fun n => 10 * (M - n) ≤ M ∧ M < 10 * n), χ n ≤ A := by
      have e : ∀ n ∈ (range M).filter (fun n => 10 * (M - n) ≤ M ∧ M < 10 * n),
          χ n = χ ((M - n : ℕ) : ℤ) := by
        intro n hn
        simp only [mem_filter, mem_range] at hn
        rw [hsym n, ← hper (-(n : ℤ))]
        congr 1
        omega
      rw [sum_congr rfl e]
      rw [← sum_image (f := fun m : ℕ => χ m) (g := fun n => M - n)]
      · apply sum_le_sum_of_subset_of_nonneg
        · intro m hm
          simp only [mem_image, mem_filter, mem_range] at hm ⊢
          obtain ⟨n, hn, rfl⟩ := hm
          omega
        · intro n _ _; exact hnn n
      · intro a ha b hb hab
        simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at ha hb
        simp only at hab
        omega
    linarith
  -- the far part is at most `X' / 80`
  have hfar' : (M : ℝ) * (η ^ 2 / 8) ^ k ≤ X' / 80 := by
    have e : (η ^ 2 / 8) ^ k = (η / 2) ^ k * (η / 4) ^ k := by rw [← mul_pow]; ring_nf
    have h2 : (η / 4) ^ k ≤ η / 4 := pow_le_of_le_one (by positivity) (by linarith) hk
    have h3 : (M : ℝ) * (η / 2) ^ k ≤ X' := by
      rw [hX'] at hnorm
      rw [le_div_iff₀ hMpos] at hnorm
      linarith
    have h4 : 0 ≤ (M : ℝ) * (η / 2) ^ k := by positivity
    have h5 : 0 ≤ (η / 4) ^ k := by positivity
    rw [e]
    calc (M : ℝ) * ((η / 2) ^ k * (η / 4) ^ k) = ((M : ℝ) * (η / 2) ^ k) * (η / 4) ^ k := by ring
      _ ≤ X' * (1 / 80) := by
        apply mul_le_mul h3 (by linarith) h5 hX'0
      _ = X' / 80 := by ring
  have hB : A ≤ ∑ n ∈ D, χ ((tn : ℤ) - n) := by
    rcases hcov with hcov | hcov
    · have e : A = ∑ m ∈ range (L + 1), χ ((tn : ℤ) - ((tn + m : ℕ) : ℤ)) := by
        apply sum_congr rfl
        intro m _
        rw [hsym m]
        congr 1
        push_cast; ring
      rw [e, ← sum_image (f := fun n : ℕ => χ ((tn : ℤ) - n)) (g := fun m => tn + m)]
      · apply sum_le_sum_of_subset_of_nonneg
        · intro n hn
          simp only [mem_image, mem_range] at hn
          obtain ⟨m, hm, rfl⟩ := hn
          exact hcov m (by omega)
        · intro n _ _; exact hnn _
      · intro a _ b _ hab
        simp only at hab
        omega
    · have e : A = ∑ m ∈ range (L + 1), χ ((tn : ℤ) - ((tn - m : ℕ) : ℤ)) := by
        apply sum_congr rfl
        intro m hm
        simp only [mem_range] at hm
        have := (hcov m (by omega)).1
        congr 1
        omega
      rw [e, ← sum_image (f := fun n : ℕ => χ ((tn : ℤ) - n)) (g := fun m => tn - m)]
      · apply sum_le_sum_of_subset_of_nonneg
        · intro n hn
          simp only [mem_image, mem_range] at hn
          obtain ⟨m, hm, rfl⟩ := hn
          exact (hcov m (by omega)).2
        · intro n _ _; exact hnn _
      · intro a ha b hb hab
        simp only [coe_range, Set.mem_Iio] at ha hb
        simp only at hab
        have := (hcov a (by omega)).1
        have := (hcov b (by omega)).1
        omega
  have hY' : Y ≤ X' / 4 := by
    rw [hX'] at hY
    have : (M : ℝ) * (X' / M) = X' := by field_simp
    rw [this] at hY
    exact hY
  have hS : δ₀ * X' / 20 ≤ ∑ n ∈ D, f n * χ ((tn : ℤ) - n) := by
    have : δ₀ * (X' / 5) ≤ δ₀ * (∑ n ∈ D, χ ((tn : ℤ) - n) - Y) := by
      apply mul_le_mul_of_nonneg_left _ hδ₀.le
      linarith
    nlinarith
  rw [hconv, hX']
  rw [show δ₀ / 20 * (X' / M) = (M : ℝ)⁻¹ * (δ₀ * X' / 20) by field_simp]
  exact mul_le_mul_of_nonneg_left hS (by positivity)

/-! ### Helpers -/

theorem nat_bounds_of_fW {W b : ℤ} {L n : ℕ} (h : fW W b L n ≠ 0) : L < 3 * n ∧ 3 * n < 2 * L := by
  obtain ⟨h1, h2, -⟩ := fW_ne_zero h
  constructor
  · have : (L : ℝ) < 3 * n := by linarith
    exact_mod_cast this
  · have : (3 : ℝ) * n < 2 * L := by linarith
    exact_mod_cast this

theorem mem_dyad_of {n L : ℕ} (h1 : n < L) (h2 : L ≤ 3 * n) (h3 : 3 * n < 2 * L) : n ∈ dyad L := by
  simp only [dyad, mem_filter, mem_range]
  refine ⟨h1, ?_, ?_⟩
  · have : (L : ℝ) ≤ 3 * n := by exact_mod_cast h2
    linarith
  · have : (3 : ℝ) * n < 2 * L := by exact_mod_cast h3
    linarith

theorem card_dyad_ge (L : ℕ) : (L : ℝ) / 3 - 2 ≤ #(dyad L) := by
  have hsub : Ico ((L + 2) / 3) ((2 * L + 2) / 3) ⊆ dyad L := by
    intro n hn
    simp only [mem_Ico] at hn
    exact mem_dyad_of (by omega) (by omega) (by omega)
  have h1 := card_le_card hsub
  rw [Nat.card_Ico] at h1
  have h2 : L ≤ 3 * ((2 * L + 2) / 3 - (L + 2) / 3) + 6 := by omega
  have h3 : (L : ℝ) ≤ 3 * (((2 * L + 2) / 3 - (L + 2) / 3 : ℕ) : ℝ) + 6 := by exact_mod_cast h2
  have h4 : (((2 * L + 2) / 3 - (L + 2) / 3 : ℕ) : ℝ) ≤ #(dyad L) := by exact_mod_cast h1
  linarith

/-- A positive triple convolution at `N` gives `N = n₁ + n₂ + n₃` once every sum of points of
the supports lies in `(0, 2N)`. -/
theorem rep3_gen {N : ℕ} {f₁ f₂ f₃ : ℕ → ℝ} (hN : 0 < N)
    (hsum : ∀ a b c, f₁ a ≠ 0 → f₂ b ≠ 0 → f₃ c ≠ 0 → 0 < a + b + c ∧ a + b + c < 2 * N)
    (h : 0 < conv3 N f₁ f₂ f₃ N) :
    ∃ n₁ n₂ n₃ : ℕ, n₁ + n₂ + n₃ = N ∧ f₁ n₁ ≠ 0 ∧ f₂ n₂ ≠ 0 ∧ f₃ n₃ ≠ 0 := by
  unfold conv3 at h
  have hs : 0 < ∑ n ∈ range N, ∑ k ∈ range N, f₁ n * f₂ k * f₃ ((N + 2 * N - n - k) % N) := by
    by_contra hc
    push Not at hc
    have : ((N : ℝ) ^ 2)⁻¹ * ∑ n ∈ range N, ∑ k ∈ range N,
        f₁ n * f₂ k * f₃ ((N + 2 * N - n - k) % N) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
    linarith
  obtain ⟨n, hn, hpos⟩ : ∃ n ∈ range N,
      0 < ∑ k ∈ range N, f₁ n * f₂ k * f₃ ((N + 2 * N - n - k) % N) := by
    by_contra hc
    push Not at hc
    exact absurd (sum_nonpos hc) (not_le.mpr hs)
  obtain ⟨k, hk, hpos'⟩ : ∃ k ∈ range N, 0 < f₁ n * f₂ k * f₃ ((N + 2 * N - n - k) % N) := by
    by_contra hc
    push Not at hc
    exact absurd (sum_nonpos hc) (not_le.mpr hpos)
  have a1 : f₁ n ≠ 0 := by intro h0; rw [h0] at hpos'; simp at hpos'
  have a2 : f₂ k ≠ 0 := by intro h0; rw [h0] at hpos'; simp at hpos'
  have a3 : f₃ ((N + 2 * N - n - k) % N) ≠ 0 := by intro h0; rw [h0] at hpos'; simp at hpos'
  set j := (N + 2 * N - n - k) % N with hj
  obtain ⟨e1, e2⟩ := hsum n k j a1 a2 a3
  rw [mem_range] at hn hk
  have hdm := Nat.div_add_mod (N + 2 * N - n - k) N
  rw [← hj] at hdm
  set q := (N + 2 * N - n - k) / N
  have hsum' : n + k + j = N := by
    rcases Nat.lt_or_ge q 3 with hq | hq
    · interval_cases q <;> omega
    · have : N * 3 ≤ N * q := Nat.mul_le_mul_left N hq
      omega
  exact ⟨n, k, j, hsum', a1, a2, a3⟩

/-! ### The ternary deduction -/

set_option maxHeartbeats 800000 in
/-- **The ternary class conclusion from Theorem 2.3 of Matomäki and Shao, Proposition 3.2 and
`Prop33Cross`, PROVED as an implication.** -/
theorem ternClass_of_props (hMS : MSThm23) (h32 : Prop32) (h33c : Prop33Cross) (J : ℕ)
    (hJ : 5 ≤ J) : ∃ w : ℕ, TernClass J w := by
  obtain ⟨δ₀, C, hδ₀, hC, H32⟩ := h32
  obtain ⟨K₅, hK₅, H5⟩ := h33c (5 / 2) (by norm_num)
  set K := max 1 K₅
  set δ := δ₀ / 40 with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨η, hη0, hη1, Ωb, Cc, N₀, HMS⟩ := hMS K δ (le_max_left _ _) hδ
  set c₀ := (η / 2) ^ Ωb / 4 with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  set R := max (max wBig ((Cc : ℝ) ^ 20)) (max ((C / c₀) ^ 3) ((C / (1 / 12)) ^ 3))
  refine ⟨⌈R⌉₊, ?_⟩
  have hR : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
  set w := ⌈R⌉₊
  have hw1 : wBig ≤ w := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hw2 : (Cc : ℝ) ^ 20 ≤ w := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hw3 : (C / c₀) ^ 3 ≤ (w : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR
  have hw4 : (C / (1 / 12)) ^ 3 ≤ (w : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hR
  have hw1' : ((1 : ℕ) : ℝ) ^ 20 ≤ w := by
    have : (1 : ℝ) ≤ wBig := by unfold wBig; exact Real.one_le_rpow (by norm_num) (by positivity)
    simp only [Nat.cast_one, one_pow]; linarith
  have hY : C / (w : ℝ) ^ ((1 : ℝ) / 3) ≤ c₀ := div_rpow_third_le hC hc₀pos hw3
  have hY₁ : C / (w : ℝ) ^ ((1 : ℝ) / 3) ≤ 1 / 12 := div_rpow_third_le hC (by norm_num) hw4
  have hYn : 0 ≤ C / (w : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  obtain ⟨N₁, HN₁⟩ := H32 Cc J w hJ hw1 hw2
  obtain ⟨N₂, HN₂⟩ := H32 1 J w hJ hw1 hw1'
  have hS := Sw_spec w
  have hSp : ∀ q ∈ Sw w, q.Prime := fun q hq => (hS q hq).1
  have hWpos : 0 < WW J w := Wmod_pos hSp
  intro B₁ B₂ B₃ hb1 hb1' hb2 hb2' hb3 hb3' hA₁ hA₂ hA₃
  refine ⟨max N₀ (2 * (N₁ + N₂) + 200), fun M hM => ?_⟩
  have hMN0 : N₀ ≤ M := le_trans (le_max_left _ _) hM
  have hM200 : 2 * (N₁ + N₂) + 200 ≤ M := le_trans (le_max_right _ _) hM
  have hMpos : 0 < M := by omega
  set L := 3 * ((M + 3) / 4) - 1 with hLdef
  set L2 := 3 * M / 5 with hL2def
  have hL1 : N₁ ≤ L := by omega
  have hL2 : N₂ ≤ L2 := by omega
  have hLM : L ≤ M := by omega
  have hML : M ≤ 2 * L := by omega
  have hL2M : L2 ≤ M := by omega
  have hML2 : M ≤ 2 * L2 := by omega
  set W := WW J w
  set f₁ := fW W B₁ L2
  set f₂ := fW W B₂ L
  set f₃ := fW W B₃ L
  have hf₁ : ∀ n, 0 ≤ f₁ n := fun n => fW_nonneg _ _ hWpos _ n
  have hf₂ : ∀ n, 0 ≤ f₂ n := fun n => fW_nonneg _ _ hWpos _ n
  have hf₃ : ∀ n, 0 ≤ f₃ n := fun n => fW_nonneg _ _ hWpos _ n
  obtain ⟨Ω, hΩ, h1Ω, hΩb, χ, hχp, hχc, HM⟩ := HMS M hMN0 f₁ hf₁
  have hnorm : (η / 2) ^ Ωb ≤ chiNorm M χ :=
    le_trans (pow_le_pow_of_le_one (by positivity) (by linarith) hΩb) hχp.2.2.2.2.2
  have hn0 : 0 ≤ chiNorm M χ := le_trans (by positivity) hnorm
  have hD : dyad L ⊆ range M := fun n hn =>
    mem_range.mpr (lt_of_lt_of_le (mem_range.mp (mem_filter.mp hn).1) hLM)
  have hYL : C * L / (w : ℝ) ^ ((1 : ℝ) / 3) ≤ M * chiNorm M χ / 4 := by
    have e : C * L / (w : ℝ) ^ ((1 : ℝ) / 3) = L * (C / (w : ℝ) ^ ((1 : ℝ) / 3)) := by ring
    rw [e]
    have h1 : C / (w : ℝ) ^ ((1 : ℝ) / 3) ≤ chiNorm M χ / 4 := by rw [hc₀] at hY; linarith
    have h2 : (L : ℝ) ≤ M := by exact_mod_cast hLM
    have h3 : (0 : ℝ) ≤ L := by positivity
    nlinarith
  -- condition (2.2)
  have gen : ∀ b : ℤ, 0 ≤ b → b < W → Amenable W b → ∀ tn : ℕ, M ≤ 4 * tn → 2 * tn < M →
      δ * chiNorm M χ ≤ convChi M (fW W b L) χ tn := by
    intro b hb hb' hA tn h4 h2
    have rt1 : (L : ℝ) / 3 < ((tn : ℤ) : ℝ) := by
      rw [Int.cast_natCast]
      have : L < 3 * tn := by omega
      have : (L : ℝ) < 3 * tn := by exact_mod_cast this
      linarith
    have rt2 : ((tn : ℤ) : ℝ) < 2 * L / 3 := by
      rw [Int.cast_natCast]
      have : 3 * tn < 2 * L := by omega
      have : (3 : ℝ) * tn < 2 * L := by exact_mod_cast this
      linarith
    have hcov : (∀ m, 10 * m ≤ M → tn + m ∈ dyad L) ∨
        (∀ m, 10 * m ≤ M → m ≤ tn ∧ tn - m ∈ dyad L) := by
      by_cases hc : 8 * tn < 3 * M
      · left; intro m hm; exact mem_dyad_of (by omega) (by omega) (by omega)
      · right; intro m hm; exact ⟨by omega, mem_dyad_of (by omega) (by omega) (by omega)⟩
    have hfs : ∀ n < M, fW W b L n ≠ 0 → n ∈ dyad L := by
      intro n _ hn
      obtain ⟨e1, e2⟩ := nat_bounds_of_fW hn
      exact mem_dyad_of (by omega) (by omega) e2
    have hb0 := HN₁ χ hχp.1 hχc b hb hb' hA L hL1 tn rt1 rt2
    have := stepGen M Ω η χ (fW W b L) (dyad L) δ₀ _ tn (by omega) hχp h1Ω hη0 hη1.le hδ₀ hD
      (fun n => fW_nonneg _ _ hWpos L n) hfs hcov hYL hb0
    have : δ ≤ δ₀ / 20 := by rw [hδdef]; linarith
    nlinarith
  have c22 : ∀ t : ℤ, (M : ℝ) / 4 ≤ t → (t : ℝ) < M / 2 →
      δ * chiNorm M χ ≤ convChi M f₂ χ t ∧ δ * chiNorm M χ ≤ convChi M f₃ χ t := by
    intro t ht1 ht2
    have ht0 : 0 ≤ t := by
      have : (0 : ℝ) ≤ t := le_trans (by positivity) ht1
      exact_mod_cast this
    obtain ⟨tn, rfl⟩ : ∃ tn : ℕ, t = tn := ⟨t.toNat, (Int.toNat_of_nonneg ht0).symm⟩
    rw [Int.cast_natCast] at ht1 ht2
    have h4 : M ≤ 4 * tn := by
      have : (M : ℝ) ≤ 4 * tn := by linarith
      exact_mod_cast this
    have h2 : 2 * tn < M := by
      have : (2 : ℝ) * tn < M := by linarith
      exact_mod_cast this
    exact ⟨gen B₂ hb2 hb2' hA₂ tn h4 h2, gen B₃ hb3 hb3' hA₃ tn h4 h2⟩
  -- condition (2.3)
  have c23 : δ * M ≤ ∑ n ∈ (range (M + 1)).filter
      (fun n : ℕ => (M : ℝ) / 10 ≤ n ∧ (n : ℝ) ≤ 2 * M / 5), f₁ n := by
    have rt1 : (L2 : ℝ) / 3 < (((L2 / 2 : ℕ) : ℤ) : ℝ) := by
      rw [Int.cast_natCast]
      have : L2 < 3 * (L2 / 2) := by omega
      have : (L2 : ℝ) < 3 * ((L2 / 2 : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    have rt2 : (((L2 / 2 : ℕ) : ℤ) : ℝ) < 2 * L2 / 3 := by
      rw [Int.cast_natCast]
      have : 3 * (L2 / 2) < 2 * L2 := by omega
      have : (3 : ℝ) * ((L2 / 2 : ℕ) : ℝ) < 2 * L2 := by exact_mod_cast this
      linarith
    have hb := HN₂ (fun _ => 1) (fun _ => zero_le_one) fourierComplexity_one B₁ hb1 hb1' hA₁ L2 hL2
      _ rt1 rt2
    simp only [mul_one, sum_const, nsmul_eq_mul] at hb
    have hsub : ∑ n ∈ dyad L2, f₁ n ≤ ∑ n ∈ (range (M + 1)).filter
        (fun n : ℕ => (M : ℝ) / 10 ≤ n ∧ (n : ℝ) ≤ 2 * M / 5), f₁ n := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        simp only [dyad, mem_filter, mem_range] at hn
        obtain ⟨hn1, hn2, hn3⟩ := hn
        have a1 : L2 ≤ 3 * n := by
          have : (L2 : ℝ) ≤ 3 * n := by linarith
          exact_mod_cast this
        have a2 : 3 * n < 2 * L2 := by
          have : (3 : ℝ) * n < 2 * L2 := by linarith
          exact_mod_cast this
        simp only [mem_filter, mem_range]
        refine ⟨by omega, ?_, ?_⟩
        · have : M ≤ 10 * n := by omega
          have : (M : ℝ) ≤ 10 * n := by exact_mod_cast this
          linarith
        · have : 5 * n ≤ 2 * M := by omega
          have : (5 : ℝ) * n ≤ 2 * M := by exact_mod_cast this
          linarith
      · intro n _ _; exact hf₁ n
    have hc := card_dyad_ge L2
    have e : C * L2 / (w : ℝ) ^ ((1 : ℝ) / 3) = L2 * (C / (w : ℝ) ^ ((1 : ℝ) / 3)) := by ring
    rw [e] at hb
    have hL20 : (0 : ℝ) ≤ L2 := by positivity
    have h12 : (L2 : ℝ) * (C / (w : ℝ) ^ ((1 : ℝ) / 3)) ≤ L2 / 12 := by nlinarith
    have hL2r : (3 : ℝ) * M ≤ 5 * L2 + 5 := by
      have : 3 * M ≤ 5 * L2 + 5 := by omega
      exact_mod_cast this
    have hMr : (200 : ℝ) ≤ M := by exact_mod_cast (le_trans (by omega) hM200)
    have key : (M : ℝ) / 10 ≤ (#(dyad L2) : ℝ) - L2 * (C / (w : ℝ) ^ ((1 : ℝ) / 3)) := by
      linarith
    calc δ * M = δ₀ / 40 * M := by rw [hδdef]
      _ ≤ δ₀ * (M / 10) := by linarith [mul_nonneg hδ₀.le (Nat.cast_nonneg (α := ℝ) M)]
      _ ≤ δ₀ * ((#(dyad L2) : ℝ) - L2 * (C / (w : ℝ) ^ ((1 : ℝ) / 3))) := by gcongr
      _ ≤ _ := hb
      _ ≤ _ := hsub
  -- condition (2.4)
  have hK5 : K₅ ≤ K := le_max_right _ _
  have c24 : ∑ ξ ∈ range M, ‖fhat M f₁ ξ‖ ^ ((5 : ℝ) / 2) ≤ K ∧
      ∑ ξ ∈ range M, ‖fhat M f₂ ξ‖ ^ ((5 : ℝ) / 2) ≤ K ∧
      ∑ ξ ∈ range M, ‖fhat M f₃ ξ‖ ^ ((5 : ℝ) / 2) ≤ K :=
    ⟨(H5 J w hJ hw1 B₁ hb1 hb1' hA₁ L2 M (by omega) hL2M hML2 f₁ hf₁ (fun n _ => le_rfl)).trans hK5,
     (H5 J w hJ hw1 B₂ hb2 hb2' hA₂ L M (by omega) hLM hML f₂ hf₂ (fun n _ => le_rfl)).trans hK5,
     (H5 J w hJ hw1 B₃ hb3 hb3' hA₃ L M (by omega) hLM hML f₃ hf₃ (fun n _ => le_rfl)).trans hK5⟩
  have hiv := HM f₂ f₃ hf₂ hf₃ c22 c23 c24
  have hpos : 0 < conv3 M f₁ f₂ f₃ M := lt_of_lt_of_le (by positivity) hiv
  have hsum : ∀ a b c, f₁ a ≠ 0 → f₂ b ≠ 0 → f₃ c ≠ 0 → 0 < a + b + c ∧ a + b + c < 2 * M := by
    intro a b c ha hb hc
    obtain ⟨a1, a2⟩ := nat_bounds_of_fW ha
    obtain ⟨b1, b2⟩ := nat_bounds_of_fW hb
    obtain ⟨c1, c2⟩ := nat_bounds_of_fW hc
    constructor <;> omega
  obtain ⟨n₁, n₂, n₃, hs, a1, a2, a3⟩ := rep3_gen hMpos hsum hpos
  exact ⟨n₁, n₂, n₃, hs, (fW_ne_zero a1).2.2, (fW_ne_zero a2).2.2, (fW_ne_zero a3).2.2⟩

/-- **Theorem 1.2, CONDITIONAL** on Matomäki and Shao, Theorem 2.3, Proposition 3.2 as printed,
and the RECONSTRUCTED restriction estimate `Prop33Cross`. -/
theorem theorem12_conditional (hMS : MSThm23) (h32 : Prop32) (h33c : Prop33Cross) :
    Theorem12 := by
  obtain ⟨w, hw⟩ := ternClass_of_props hMS h32 h33c 5 le_rfl
  exact theorem12_of_classes ⟨5, w, le_rfl, hw⟩

end LeanLab.Teravainen2016
