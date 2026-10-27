/-
P0076 J. Teräväinen, arXiv 1611.08585: the RECONSTRUCTED hypothesis `Prop33Cross` of
`theorem12_conditional` follows from Proposition 3.3 exactly as printed on page 9, where the
shift `b` of the amenable linear function `W n + b` is any integer, Definition 3.1. The lab's
`Prop33` restricted `b` to `0 ≤ b < W`; the printed statement has no such restriction.
The proof moves `g` from `ℤ_M` into the middle third of `ℤ_{3M}`, replacing `b` by `b - W M`,
which keeps `W n + b` amenable, and reads the Fourier transform on `ℤ_M` at the frequencies
`3ξ` of `ℤ_{3M}`, which costs a factor `3^r`.
Also: the precise page 11 gap between the printed Proposition 2.1 and the form with `η ≤ 0.05`.
AI-written Lean code, Claude, session 20261020T2317Z-cloud53, unit U-6781.
Checked only by the Lean kernel. Binary Goldbach is OPEN; ternary Goldbach is a theorem,
Helfgott 2013.
-/
import Mathlib
import LeanLab.Teravainen2016.TernaryBridge

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- **Proposition 3.3 as printed**, page 9: `W n + b` amenable with `W` as in (3.3), `b` any
integer as Definition 3.1 allows, `N ≥ 1`, `0 ≤ g ≤ f` on `[0, N)` with `f` of (3.4); then
`∑_{ξ ∈ ℤ_N} |ĝ(ξ)|^r ≤ K_r` for every `r > 2`. -/
def Prop33Printed : Prop :=
  ∀ r : ℝ, 2 < r → ∃ K : ℝ, 0 < K ∧ ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
    Amenable (WW J w) b → ∀ N : ℕ, 1 ≤ N → ∀ g : ℕ → ℝ, (∀ n, 0 ≤ g n) →
    (∀ n < N, g n ≤ fW (WW J w) b N n) → ∑ ξ ∈ range N, ‖fhat N g ξ‖ ^ r ≤ K

/-- The printed form implies the lab's restricted form. PROVED. -/
theorem prop33_of_printed (h : Prop33Printed) : Prop33 := by
  intro r hr
  obtain ⟨K, hK, H⟩ := h r hr
  exact ⟨K, hK, fun J w hJ hw b _ _ hA N hN g hg hgf => H J w hJ hw b hA N hN g hg hgf⟩

/-- Amenability of `K n + b` depends on `b` modulo `K` only. PROVED. -/
theorem amenable_add_mul {K b : ℤ} (h : Amenable K b) (c : ℤ) : Amenable K (b + K * c) := by
  obtain ⟨h1, h6, hcop, hp, j, t, hh, he, h3, hdiv⟩ := h
  refine ⟨h1, h6, ?_, ?_, ?_⟩
  · exact hcop.add_mul_left_left c
  · intro p pp p4 p3 pK hpd
    apply hp p pp p4 p3 pK
    have : (p : ℤ) ∣ K * c := dvd_mul_of_dvd_left pK c
    have e : b - 1 = (b + K * c - 1) - K * c := by ring
    rw [e]; exact dvd_sub hpd this
  · obtain ⟨d, hd⟩ := hdiv
    refine ⟨j, t, hh + 3 * d * c, ?_, ?_, ⟨d, hd⟩⟩
    · rw [hd]; linear_combination he
    · rintro ⟨q, hq⟩
      exact h3 ⟨q - 4 * d * c, by linarith⟩

/-- `e(x - ξ) = e(x)` for an integer `ξ`. -/
theorem eC_sub_nat (x : ℝ) (ξ : ℕ) : eC (x - ξ) = eC x := by
  unfold eC
  have h := Complex.exp_int_mul_two_pi_mul_I (-(ξ : ℤ))
  have e : 2 * (Real.pi : ℂ) * Complex.I * ((x - ξ : ℝ) : ℂ) =
      2 * Real.pi * Complex.I * (x : ℂ) + ((-(ξ : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [e, Complex.exp_add, h, mul_one]

/-- `g` moved from `[0, M)` to `[M, 2M)`. -/
noncomputable def shiftM (M : ℕ) (g : ℕ → ℝ) (n : ℕ) : ℝ :=
  if M ≤ n ∧ n < 2 * M then g (n - M) else 0

/-- The Fourier transform of the moved function on `ℤ_{3M}` at `3ξ` is a third of `ĝ(ξ)` on
`ℤ_M`. PROVED. -/
theorem fhat_shiftM (M : ℕ) (hM : 0 < M) (g : ℕ → ℝ) (ξ : ℕ) :
    fhat M g ξ = 3 * fhat (3 * M) (shiftM M g) (3 * ξ) := by
  unfold fhat
  have hsplit : ∑ n ∈ range (3 * M), (shiftM M g n : ℂ) * eC (-(((3 * ξ : ℕ) : ℝ) * n /
      ((3 * M : ℕ) : ℝ))) = ∑ k ∈ range M, (g k : ℂ) * eC (-((ξ : ℝ) * k / M)) := by
    rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le M) (by omega : M ≤ 3 * M),
      ← sum_Ico_consecutive _ (by omega : M ≤ 2 * M) (by omega : 2 * M ≤ 3 * M)]
    have z1 : ∑ n ∈ Ico 0 M, (shiftM M g n : ℂ) * eC (-(((3 * ξ : ℕ) : ℝ) * n /
        ((3 * M : ℕ) : ℝ))) = 0 := by
      apply sum_eq_zero; intro n hn; simp only [mem_Ico] at hn
      simp [shiftM, show ¬ M ≤ n by omega]
    have z3 : ∑ n ∈ Ico (2 * M) (3 * M), (shiftM M g n : ℂ) * eC (-(((3 * ξ : ℕ) : ℝ) * n /
        ((3 * M : ℕ) : ℝ))) = 0 := by
      apply sum_eq_zero; intro n hn; simp only [mem_Ico] at hn
      simp [shiftM, show ¬ n < 2 * M by omega]
    rw [z1, z3, zero_add, add_zero, sum_Ico_eq_sum_range, show 2 * M - M = M by omega]
    apply sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    have hs : shiftM M g (M + k) = g k := by
      simp only [shiftM]; rw [if_pos ⟨by omega, by omega⟩]; congr 1; omega
    rw [hs]
    congr 1
    have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    have e : -(((3 * ξ : ℕ) : ℝ) * ((M + k : ℕ) : ℝ) / ((3 * M : ℕ) : ℝ)) =
        -((ξ : ℝ) * k / M) - ξ := by
      push_cast; field_simp; ring
    rw [e, eC_sub_nat]
  rw [hsplit]
  push_cast
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp

/-- A sum over the frequencies `3ξ`, `ξ < M`, is at most the sum over `ℤ_{3M}`. -/
theorem sum_three_mul_le (M : ℕ) (h : ℕ → ℝ) (hh : ∀ n, 0 ≤ h n) :
    ∑ ξ ∈ range M, h (3 * ξ) ≤ ∑ η ∈ range (3 * M), h η := by
  rw [← sum_image (f := h) (g := fun ξ => 3 * ξ) (by intro a _ b _ hab; simp only at hab; omega)]
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [mem_image, mem_range] at hn ⊢
    obtain ⟨ξ, hξ, rfl⟩ := hn
    omega
  · intro n _ _; exact hh n

/-- The moved function lies below `f` of (3.4) for `b - W M` at scale `3M`. PROVED. -/
theorem shiftM_le_fW {W b : ℤ} (hW : 0 < W) {L M : ℕ} (hL : 1 ≤ L) (hLM : L ≤ 3 * M)
    {g : ℕ → ℝ} (hgf : ∀ n < M, g n ≤ fW W b L n) :
    ∀ n < 3 * M, shiftM M g n ≤ fW W (b - W * M) (3 * M) n := by
  intro n hn
  unfold shiftM
  split_ifs with hc
  · have hle := hgf (n - M) (by omega)
    by_cases h0 : fW W b L (n - M) = 0
    · rw [h0] at hle; exact hle.trans (fW_nonneg _ _ hW _ _)
    · obtain ⟨a1, a2, hgood⟩ := fW_ne_zero h0
      have hpos : (0 : ℝ) < ((n - M : ℕ) : ℝ) := lt_of_le_of_lt (by positivity) a1
      have hnM : M < n := by
        have : 0 < n - M := by exact_mod_cast hpos
        omega
      refine hle.trans ?_
      unfold fW
      rw [if_pos ⟨by linarith, by linarith, hgood⟩]
      rw [if_pos]
      · have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
        have hlog : Real.log L ≤ Real.log ((3 * M : ℕ) : ℝ) :=
          Real.log_le_log hL0 (by exact_mod_cast hLM)
        have h1 : Real.log L ^ ((3 : ℝ) / 2) ≤ Real.log ((3 * M : ℕ) : ℝ) ^ ((3 : ℝ) / 2) :=
          Real.rpow_le_rpow (Real.log_natCast_nonneg L) hlog (by norm_num)
        have h2 : (0 : ℝ) ≤ ((Nat.totient W.toNat : ℝ) / W) ^ ((3 : ℝ) / 2) := by
          apply Real.rpow_nonneg; apply div_nonneg (by positivity); exact_mod_cast hW.le
        exact mul_le_mul_of_nonneg_right h1 h2
      · refine ⟨?_, ?_, ?_⟩
        · push_cast
          have : (M : ℝ) < n := by exact_mod_cast hnM
          linarith
        · push_cast
          have : (n : ℝ) < 2 * M := by exact_mod_cast hc.2
          linarith
        · have e : W * (n : ℤ) + (b - W * M) = W * ((n - M : ℕ) : ℤ) + b := by
            rw [Nat.cast_sub hc.1]; ring
          rw [e]; exact hgood
  · exact fW_nonneg _ _ hW _ _

/-- **`Prop33Cross` from Proposition 3.3 as printed, PROVED**, with `K = 3^r K_r`. -/
theorem prop33Cross_of_printed (h : Prop33Printed) : Prop33Cross := by
  intro r hr
  obtain ⟨K, hK, H⟩ := h r hr
  refine ⟨3 ^ r * K, by positivity, ?_⟩
  intro J w hJ hw b _ _ hA L M hL hLM _ g hg hgf
  have hS := Sw_spec w
  have hSp : ∀ q ∈ Sw w, q.Prime := fun q hq => (hS q hq).1
  have hWpos : 0 < WW J w := Wmod_pos hSp
  have hM : 0 < M := by omega
  have hA' : Amenable (WW J w) (b - WW J w * M) := by
    have := amenable_add_mul hA (-(M : ℤ)); rwa [mul_neg, ← sub_eq_add_neg] at this
  have hg' : ∀ n, 0 ≤ shiftM M g n := by
    intro n; unfold shiftM; split_ifs
    · exact hg _
    · exact le_rfl
  have hB := H J w hJ hw _ hA' (3 * M) (by omega) (shiftM M g) hg'
    (shiftM_le_fW hWpos hL (by omega) hgf)
  have e : ∀ ξ ∈ range M, ‖fhat M g ξ‖ ^ r =
      3 ^ r * ‖fhat (3 * M) (shiftM M g) (3 * ξ)‖ ^ r := by
    intro ξ _
    rw [fhat_shiftM M hM g ξ, norm_mul, Real.mul_rpow (by norm_num) (norm_nonneg _)]
    norm_num
  rw [sum_congr rfl e, ← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine le_trans ?_ hB
  exact sum_three_mul_le M (fun η => ‖fhat (3 * M) (shiftM M g) η‖ ^ r)
    (fun _ => Real.rpow_nonneg (norm_nonneg _) _)

/-- **Theorem 1.2, CONDITIONAL** on Matomäki and Shao, Theorem 2.3, Proposition 3.2 with
`0 ≤ b < W`, and Proposition 3.3 as printed. No RECONSTRUCTED input remains. -/
theorem theorem12_printed (hMS : MSThm23) (h32 : Prop32) (h33 : Prop33Printed) : Theorem12 :=
  theorem12_conditional hMS h32 (prop33Cross_of_printed h33)

/-- **Theorem 1.1, CONDITIONAL** on the same inputs as `theorem11_conditional`, with
Proposition 3.3 as printed. -/
theorem theorem11_printed (h21 : Prop21With (1 / 20)) (hχ : ChiExists) (h32 : Prop32)
    (h32h : Prop32Half) (h33 : Prop33Printed) : Theorem11 :=
  theorem11_conditional h21 hχ h32 h32h (prop33_of_printed h33)


/-! ### The page 11 gap in Proposition 2.1

The printed Proposition 2.1 gives some `η ∈ (0, 1/2)` and asks condition (i) for a `χ` obeying
(2.1). Page 11 uses `η ≤ 0.05`, which only the proof's choice of `η` gives. The witness below
shows the gap is real at the level of (2.1): for `η ∈ [1/4, 1/2)`, which the printed statement
allows, the far condition of (2.1) is vacuous, and a `χ` with a spike at `M/2` obeys (2.1) while
condition (i) fails at every `t` of the middle third for every `f ≥ 0` supported there, whatever
`δ > 0`. So no argument from Proposition 3.2 and (2.1) alone gives (i) without a bound on `η`. -/

/-- `n ≡ k (mod 2k)` as a divisibility. -/
theorem spike_iff (k n : ℤ) (hk : 0 < k) : n % (2 * k) = k ↔ 2 * k ∣ k - n := by
  rw [← Int.modEq_iff_dvd, Int.ModEq, Int.emod_eq_of_lt hk.le (by linarith)]

/-- The spike function `χ(n) = 1 + A [n ≡ k (mod 2k)]`. -/
noncomputable def spikeChi (k : ℕ) (A : ℝ) (n : ℤ) : ℝ :=
  1 + A * (if n % (2 * (k : ℤ)) = k then 1 else 0)

theorem distInt_le_half (x : ℝ) : distInt x ≤ 1 / 2 := abs_sub_round x

theorem spikeChi_props (k : ℕ) (hk : 1 ≤ k) {A : ℝ} (hA : 0 ≤ A) {η : ℝ} (hη : 1 / 4 ≤ η)
    (hη2 : η < 1 / 2) :
    ChiProps (2 * k) {1 % (2 * k)} η (spikeChi k A) := by
  have hk0 : (0 : ℤ) < k := by exact_mod_cast hk
  have hge : ∀ n, 1 ≤ spikeChi k A n := by
    intro n; unfold spikeChi; split_ifs <;> nlinarith
  refine ⟨fun n => le_trans zero_le_one (hge n), ?_, ?_, fun n _ _ => hge n, ?_, ?_⟩
  · intro n
    unfold spikeChi
    have : n % (2 * (k : ℤ)) = k ↔ (-n) % (2 * (k : ℤ)) = k := by
      rw [spike_iff _ _ hk0, spike_iff _ _ hk0]
      constructor
      · intro h
        have : 2 * (k : ℤ) ∣ 2 * k - (k - n) := dvd_sub (dvd_refl _) h
        rwa [show 2 * (k : ℤ) - (k - n) = k - -n by ring] at this
      · intro h
        have : 2 * (k : ℤ) ∣ 2 * k - (k - -n) := dvd_sub (dvd_refl _) h
        rwa [show 2 * (k : ℤ) - (k - -n) = k - n by ring] at this
    simp only [this]
  · intro n
    unfold spikeChi
    push_cast
    rw [Int.add_emod_right]
  · intro n _ hB
    exfalso; apply hB
    intro ξ _
    exact (distInt_le_half _).trans (by linarith)
  · rw [card_singleton, pow_one]
    unfold chiNorm
    have hM : (0 : ℝ) < ((2 * k : ℕ) : ℝ) := by positivity
    have hs : ((2 * k : ℕ) : ℝ) ≤ ∑ n ∈ range (2 * k), spikeChi k A n := by
      have := sum_le_sum (s := range (2 * k)) (fun n _ => hge n)
      simpa using this
    have : (1 : ℝ) ≤ ((2 * k : ℕ) : ℝ)⁻¹ * ∑ n ∈ range (2 * k), spikeChi k A n := by
      rw [← div_eq_inv_mul, le_div_iff₀ hM]; linarith
    linarith

/-- **The page 11 gap, PROVED witness**: for `M = 2k`, `η ∈ [1/4, 1/2)` and `Ω = {1}`, for every
`f ≥ 0` supported in the middle third of `[0, M)` and every `δ > 0` there is `χ` obeying (2.1)
with condition (i) of Proposition 2.1 false at every integer `t ∈ (M/3, 2M/3)`. -/
theorem prop21_gap_witness (k : ℕ) (hk : 1 ≤ k) {η : ℝ} (hη : 1 / 4 ≤ η) (hη2 : η < 1 / 2)
    (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) (hfs : ∀ n, f n ≠ 0 → 2 * k < 3 * n ∧ 3 * n < 4 * k) {δ : ℝ}
    (hδ : 0 < δ) : ∃ χ : ℤ → ℝ, ChiProps (2 * k) {1 % (2 * k)} η χ ∧
      ∀ t : ℕ, 2 * k < 3 * t → 3 * t < 4 * k → convChi (2 * k) f χ t < δ * chiNorm (2 * k) χ := by
  have hk0 : (0 : ℤ) < k := by exact_mod_cast hk
  set M := 2 * k with hMdef
  have hM : (0 : ℝ) < M := by positivity
  set S := (M : ℝ)⁻¹ * ∑ n ∈ range M, f n with hSdef
  have hS : 0 ≤ S := mul_nonneg (by positivity) (sum_nonneg fun n _ => hf n)
  set A := M * (S / δ) + M with hAdef
  have hA : 0 ≤ A := by positivity
  refine ⟨spikeChi k A, spikeChi_props k hk hA hη hη2, ?_⟩
  intro t ht1 ht2
  -- the spike is never hit
  have hconv : convChi M f (spikeChi k A) t = S := by
    unfold convChi
    rw [hSdef]
    congr 1
    apply sum_congr rfl
    intro n _
    by_cases h0 : f n = 0
    · rw [h0, zero_mul]
    · obtain ⟨a1, a2⟩ := hfs n h0
      unfold spikeChi
      rw [if_neg, mul_zero, add_zero, mul_one]
      rw [spike_iff _ _ hk0]
      rintro ⟨q, hq⟩
      have e1 : (2 * k : ℤ) < 3 * t := by exact_mod_cast ht1
      have e2 : (3 * t : ℤ) < 4 * k := by exact_mod_cast ht2
      have e3 : (2 * k : ℤ) < 3 * n := by exact_mod_cast a1
      have e4 : (3 * n : ℤ) < 4 * k := by exact_mod_cast a2
      rcases le_or_gt q 0 with hq0 | hq0
      · nlinarith
      · nlinarith
  -- the norm sees the spike at `k`
  have hnorm : 1 + A / M ≤ chiNorm M (spikeChi k A) := by
    unfold chiNorm
    have hpt : ∀ n ∈ range M, (1 : ℝ) + A * (if n = k then 1 else 0) ≤ spikeChi k A n := by
      intro n hn
      unfold spikeChi
      split_ifs with h1 h2 h2
      · exact le_rfl
      · exfalso; apply h2; subst h1
        rw [Int.emod_eq_of_lt (by positivity) (by linarith)]
      · linarith
      · exact le_rfl
    have hs := sum_le_sum hpt
    rw [sum_add_distrib, sum_const, card_range, ← mul_sum, sum_ite_eq'] at hs
    rw [if_pos (mem_range.mpr (by omega))] at hs
    simp only [nsmul_eq_mul, mul_one] at hs
    rw [← div_eq_inv_mul, le_div_iff₀ hM]
    have : (1 + A / M) * M = M + A := by field_simp
    linarith
  rw [hconv]
  have hAM : A / M = S / δ + 1 := by rw [hAdef]; field_simp
  have : δ * (1 + A / M) = 2 * δ + S := by rw [hAM]; field_simp; ring
  nlinarith

end LeanLab.Teravainen2016
