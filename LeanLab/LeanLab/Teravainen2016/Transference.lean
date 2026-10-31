/-
P0076 J. Teräväinen, arXiv 1611.08585, Sections 2 and 3: Proposition 2.1, the transference type
result, Propositions 3.2 and 3.3, and the properties (2.1), (2.2) of the smoothed Bohr set
function `χ` quoted from Matomäki and Shao, all stated as Props, and the deduction of
Theorem 1.1 from them on pages 11 to 12 as a CONDITIONAL theorem with zero sorry.
Functions on `ℤ_N` are functions `ℕ → ℝ` read on the representatives `0, …, N - 1`.
AI-written Lean code, Claude, session 20261020T2317Z-cloud53, unit U-6761.
Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Teravainen2016.Counting

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-! ### Notation of Section 2 -/

/-- `e(x) = e^{2πix}`. -/
noncomputable def eC (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-- `f̂(ξ) = (1/N) ∑_{n ∈ ℤ_N} f(n) e(-ξn/N)`. -/
noncomputable def fhat (N : ℕ) (f : ℕ → ℝ) (ξ : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ range N, (f n : ℂ) * eC (-((ξ : ℝ) * n / N))

/-- `f ∗ g(n) = (1/N) ∑_{k ∈ ℤ_N} f(k) g(n - k)` on `ℤ_N`, for `n ≥ 0`. -/
noncomputable def conv (N : ℕ) (f g : ℕ → ℝ) (n : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ k ∈ range N, f k * g ((n + N - k) % N)

/-- `f ∗ χ(t) = (1/N) ∑_{k ∈ ℤ_N} f(k) χ(t - k)` for `χ : ℤ → ℝ`. -/
noncomputable def convChi (N : ℕ) (f : ℕ → ℝ) (χ : ℤ → ℝ) (t : ℤ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ k ∈ range N, f k * χ (t - k)

/-- `‖χ‖₁ = (1/N) ∑_{n ∈ ℤ_N} χ(n)`. -/
noncomputable def chiNorm (N : ℕ) (χ : ℤ → ℝ) : ℝ := (N : ℝ)⁻¹ * ∑ n ∈ range N, χ n

/-- The Bohr set `B(Ω, η) = {n ∈ ℤ_N : ‖ξn/N‖ ≤ η for all ξ ∈ Ω}`. -/
def Bohr (N : ℕ) (Ω : Finset ℕ) (η : ℝ) : Set ℕ :=
  {n | ∀ ξ ∈ Ω, distInt ((ξ : ℝ) * n / N) ≤ η}

/-- The properties (2.1) of `χ = χ_{Ω,η}`, quoted by the paper from Matomäki and Shao,
Lemma 3.1. The upper bound `χ ≪_{|Ω|} 1` is not used in the paper and is omitted, which only
widens the class of `χ` in Proposition 2.1. -/
def ChiProps (N : ℕ) (Ω : Finset ℕ) (η : ℝ) (χ : ℤ → ℝ) : Prop :=
  (∀ n, 0 ≤ χ n) ∧ (∀ n, χ n = χ (-n)) ∧ (∀ n, χ (n + N) = χ n) ∧
  (∀ n < N, n ∈ Bohr N Ω η → 1 ≤ χ n) ∧
  (∀ n < N, n ∉ Bohr N Ω (2 * η) → χ n ≤ (η ^ 2 / 8) ^ Ω.card) ∧
  (η / 2) ^ Ω.card ≤ chiNorm N χ

/-- Fourier complexity at most `C`, display (2.2): `χ(n) = ∑_{k ≤ C} c_k e(α_k n)`, `|c_k| ≤ C`. -/
def FourierComplexityLE (χ : ℤ → ℝ) (C : ℕ) : Prop :=
  ∃ c : Fin C → ℂ, ∃ α : Fin C → ℝ, (∀ k, ‖c k‖ ≤ C) ∧
    ∀ n : ℤ, (χ n : ℂ) = ∑ k, c k * eC (α k * n)

/-! ### Proposition 2.1 -/

/-- **Proposition 2.1**, with the extra parameter `ηmax`: the paper states `η ∈ (0, 1/2)`,
that is `Prop21With (1/2)`; the application on page 11 uses `η ≤ 0.05`, which the proof's
choice `η = δ⁴ε / (10 K₀²)` gives for `δ, ε ≤ 1`. The interval `[0.9N, N]` is
`9N ≤ 10n ≤ 10N`. -/
def Prop21With (ηmax : ℝ) : Prop :=
  ∀ K₀ δ ε : ℝ, 1 ≤ K₀ → 0 < δ → 0 < ε → ∃ η : ℝ, 0 < η ∧ η < ηmax ∧ ∃ Ωb : ℕ,
    ∀ N : ℕ, 0 < N → ∀ f₁ f₂ : ℕ → ℝ, (∀ n, 0 ≤ f₁ n) → (∀ n, 0 ≤ f₂ n) →
    ∃ Ω : Finset ℕ, Ω ⊆ range N ∧ 1 % N ∈ Ω ∧ Ω.card ≤ Ωb ∧
    ∀ χ : ℤ → ℝ, ChiProps N Ω η χ →
      (∀ t : ℤ, (N : ℝ) / 3 < t → (t : ℝ) < 2 * N / 3 → δ * chiNorm N χ ≤ convChi N f₂ χ t) →
      δ * N ≤ ∑ n ∈ (range N).filter (fun n : ℕ => (N : ℝ) / 3 < n ∧ (n : ℝ) < N / 2), f₁ n →
      (∀ r ∈ ({3, 4} : Finset ℕ), ∑ ξ ∈ range N, ‖fhat N f₁ ξ‖ ^ r ≤ K₀ ∧
        ∑ ξ ∈ range N, ‖fhat N f₂ ξ‖ ^ r ≤ K₀) →
      (#{n ∈ Icc 0 N | 9 * N ≤ 10 * n ∧ conv N f₁ f₂ n < δ ^ 2 / 3} : ℝ) ≤ ε * N

/-- Proposition 2.1 exactly as printed, `η ∈ (0, 1/2)`. -/
def Prop21 : Prop := Prop21With (1 / 2)

theorem prop21_of_small {a b : ℝ} (hab : a ≤ b) (h : Prop21With a) : Prop21With b := by
  intro K₀ δ ε hK hδ hε
  obtain ⟨η, h0, h1, rest⟩ := h K₀ δ ε hK hδ hε
  exact ⟨η, h0, lt_of_lt_of_le h1 hab, rest⟩

/-- Existence of `χ_{Ω,η}` with (2.1) and Fourier complexity `≪_{|Ω|,η} 1`, as quoted from
Matomäki and Shao on page 6. -/
def ChiExists : Prop :=
  ∀ (k : ℕ) (η : ℝ), 0 < η → η < 1 / 2 → ∃ Cc : ℕ, ∀ N : ℕ, 0 < N → ∀ Ω : Finset ℕ,
    Ω ⊆ range N → Ω.card ≤ k → ∃ χ : ℤ → ℝ, ChiProps N Ω η χ ∧ FourierComplexityLE χ Cc

/-! ### Propositions 3.2 and 3.3 -/

/-- `10^{10^{10}}`, the lower bound for `w` in (3.3). -/
noncomputable def wBig : ℝ := (10 : ℝ) ^ ((10 : ℝ) ^ (10 : ℝ))

/-- The function `f` of (3.4) for `W n + b` and `N`. -/
noncomputable def fW (W b : ℤ) (N n : ℕ) : ℝ :=
  if (N : ℝ) / 3 < n ∧ (n : ℝ) < 2 * N / 3 ∧ Good (W * n + b) then
    Real.log N ^ ((3 : ℝ) / 2) * ((Nat.totient W.toNat : ℝ) / W) ^ ((3 : ℝ) / 2) else 0

/-- `n ∼ N/3`, that is `N/3 ≤ n < 2N/3`. -/
noncomputable def dyad (N : ℕ) : Finset ℕ :=
  (range N).filter (fun n => (N : ℝ) / 3 ≤ n ∧ (n : ℝ) < 2 * N / 3)

/-- `N/3 < n < N/2`. -/
noncomputable def half (N : ℕ) : Finset ℕ :=
  (range N).filter (fun n : ℕ => (N : ℝ) / 3 < n ∧ (n : ℝ) < N / 2)

/-- The statement of Proposition 3.2 with the summation range `R N`. -/
def Prop32On (R : ℕ → Finset ℕ) : Prop :=
  ∃ δ₀ C : ℝ, 0 < δ₀ ∧ 0 < C ∧ ∀ Cc J w : ℕ, 5 ≤ J → wBig ≤ w → (Cc : ℝ) ^ 20 ≤ w →
    ∃ N₀ : ℕ, ∀ χ : ℤ → ℝ, (∀ n, 0 ≤ χ n) → FourierComplexityLE χ Cc →
    ∀ b : ℤ, 0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ N : ℕ, N₀ ≤ N →
    ∀ t : ℤ, (N : ℝ) / 3 < t → (t : ℝ) < 2 * N / 3 →
      δ₀ * (∑ n ∈ R N, χ (t - n) - C * N / (w : ℝ) ^ ((1 : ℝ) / 3)) ≤
        ∑ n ∈ R N, fW (WW J w) b N n * χ (t - n)

/-- **Proposition 3.2**, summation over `n ∼ N/3`. The shift is restricted to `0 ≤ b < W`, the
range of the `Bᵢ` on page 11: as printed, with `N₀ = N₀(w, C)` independent of `b`, a very
negative amenable `b` makes `f ≡ 0` on `[0, N)` and the bound fails for `χ ≡ 1`. -/
def Prop32 : Prop := Prop32On dyad

/-- The variant of Proposition 3.2 with `N/3 < n < N/2` in place of `n ∼ N/3`, which page 11
asserts "one could clearly" use; it is what condition (ii) of Proposition 2.1 needs. -/
def Prop32Half : Prop := Prop32On half

/-- **Proposition 3.3**: for amenable `W n + b`, `W` as in (3.3), and `0 ≤ g ≤ f` on `[0, N)`,
`∑_ξ |ĝ(ξ)|^r ≤ K_r` for every `r > 2`. -/
def Prop33 : Prop :=
  ∀ r : ℝ, 2 < r → ∃ K : ℝ, 0 < K ∧ ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
    0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ N : ℕ, 1 ≤ N → ∀ g : ℕ → ℝ, (∀ n, 0 ≤ g n) →
    (∀ n < N, g n ≤ fW (WW J w) b N n) → ∑ ξ ∈ range N, ‖fhat N g ξ‖ ^ r ≤ K

/-- The elementary step for condition (i) on page 12: from the Proposition 3.2 lower bound with
error `Y ≤ M‖χ‖₁/4` and the properties (2.1) with `1 ∈ Ω`, `η ≤ 0.05`, condition (i) holds with
`δ = δ₀/20`. -/
def StepI : Prop :=
  ∀ (M : ℕ) (Ω : Finset ℕ) (η : ℝ) (χ : ℤ → ℝ) (f : ℕ → ℝ) (δ₀ Y : ℝ) (t : ℤ),
    2 ≤ M → ChiProps M Ω η χ → 1 % M ∈ Ω → 0 < η → η ≤ 1 / 20 → 0 < δ₀ →
    (∀ n, 0 ≤ f n) → (∀ n, f n ≠ 0 → (M : ℝ) / 3 < n ∧ (n : ℝ) < 2 * M / 3) →
    Y ≤ M * chiNorm M χ / 4 → (M : ℝ) / 3 < t → (t : ℝ) < 2 * M / 3 →
    δ₀ * (∑ n ∈ dyad M, χ (t - n) - Y) ≤ ∑ n ∈ dyad M, f n * χ (t - n) →
    δ₀ / 20 * chiNorm M χ ≤ convChi M f χ t

/-! ### Elementary facts used in the deduction -/

theorem fW_nonneg (W b : ℤ) (hW : 0 < W) (N n : ℕ) : 0 ≤ fW W b N n := by
  unfold fW
  split_ifs
  · have h1 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have h2 : (0 : ℝ) ≤ (Nat.totient W.toNat : ℝ) / W := by
      apply div_nonneg (by positivity); exact_mod_cast hW.le
    positivity
  · exact le_rfl

theorem fW_ne_zero {W b : ℤ} {N n : ℕ} (h : fW W b N n ≠ 0) :
    (N : ℝ) / 3 < n ∧ (n : ℝ) < 2 * N / 3 ∧ Good (W * n + b) := by
  unfold fW at h
  split_ifs at h with hc
  · exact hc
  · exact absurd rfl h

/-- A positive value of `f₁ ∗ f₂` at `n ∈ [0.9M, M]` gives the representation (3.5), with
`n = n₁ + n₂` exactly, page 12. -/
theorem rep_of_conv_pos {W B₁ B₂ : ℤ} {M n : ℕ} (hM : 0 < M) (hnM : n ≤ M)
    (h9 : 9 * M ≤ 10 * n) (h : 0 < conv M (fW W B₁ M) (fW W B₂ M) n) : Rep W B₁ B₂ n := by
  unfold conv at h
  have hs : 0 < ∑ k ∈ range M, fW W B₁ M k * fW W B₂ M ((n + M - k) % M) := by
    by_contra hc
    push Not at hc
    have : (M : ℝ)⁻¹ * ∑ k ∈ range M, fW W B₁ M k * fW W B₂ M ((n + M - k) % M) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
    linarith
  obtain ⟨k, hk, hpos⟩ : ∃ k ∈ range M, 0 < fW W B₁ M k * fW W B₂ M ((n + M - k) % M) := by
    by_contra hc
    push Not at hc
    exact absurd (sum_nonpos hc) (not_le.mpr hs)
  have hk1 : fW W B₁ M k ≠ 0 := by intro h0; rw [h0, zero_mul] at hpos; exact lt_irrefl _ hpos
  have hk2 : fW W B₂ M ((n + M - k) % M) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hpos; exact lt_irrefl _ hpos
  obtain ⟨a1, a2, g1⟩ := fW_ne_zero hk1
  obtain ⟨c1, c2, g2⟩ := fW_ne_zero hk2
  set j := (n + M - k) % M with hj
  have e1 : M < 3 * k := by
    have : (M : ℝ) < 3 * k := by linarith
    exact_mod_cast this
  have e2 : 3 * k < 2 * M := by
    have : (3 : ℝ) * k < 2 * M := by linarith
    exact_mod_cast this
  have e3 : M < 3 * j := by
    have : (M : ℝ) < 3 * j := by linarith
    exact_mod_cast this
  have e4 : 3 * j < 2 * M := by
    have : (3 : ℝ) * j < 2 * M := by linarith
    exact_mod_cast this
  have hdm := Nat.div_add_mod (n + M - k) M
  rw [← hj] at hdm
  set q := (n + M - k) / M
  have hkj : k + j = n := by
    rcases Nat.lt_or_ge q 2 with hq | hq
    · interval_cases q <;> omega
    · have : M * 2 ≤ M * q := Nat.mul_le_mul_left M hq
      omega
  exact ⟨k, j, hkj, g1, g2⟩

theorem card_half_ge (M : ℕ) : (M : ℝ) / 6 - 3 / 2 ≤ #(half M) := by
  have hsub : Ico (M / 3 + 1) ((M + 1) / 2) ⊆ half M := by
    intro n hn
    simp only [mem_Ico] at hn
    simp only [half, mem_filter, mem_range]
    refine ⟨by omega, ?_, ?_⟩
    · have : M < 3 * n := by omega
      have : (M : ℝ) < 3 * n := by exact_mod_cast this
      linarith
    · have : 2 * n < M := by omega
      have : (2 : ℝ) * n < M := by exact_mod_cast this
      linarith
  have h1 := card_le_card hsub
  rw [Nat.card_Ico] at h1
  have h2 : M ≤ 6 * ((M + 1) / 2 - (M / 3 + 1)) + 9 := by omega
  have h3 : (M : ℝ) ≤ 6 * (((M + 1) / 2 - (M / 3 + 1) : ℕ) : ℝ) + 9 := by exact_mod_cast h2
  have h4 : (((M + 1) / 2 - (M / 3 + 1) : ℕ) : ℝ) ≤ #(half M) := by exact_mod_cast h1
  linarith

theorem fourierComplexity_one : FourierComplexityLE (fun _ => 1) 1 :=
  ⟨fun _ => 1, fun _ => 0, fun _ => by simp, fun n => by simp [eC]⟩

theorem rpow_third_ge {X w : ℝ} (hX : 0 ≤ X) (hw : X ^ 3 ≤ w) : X ≤ w ^ ((1 : ℝ) / 3) := by
  have h := Real.rpow_le_rpow (by positivity) hw (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have e : (X ^ 3) ^ ((1 : ℝ) / 3) = X := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX]; norm_num
  rwa [e] at h

/-- `C / w^{1/3} ≤ c` once `w ≥ (C/c)^3`. -/
theorem div_rpow_third_le {C c w : ℝ} (hC : 0 < C) (hc : 0 < c) (hw : (C / c) ^ 3 ≤ w) :
    C / w ^ ((1 : ℝ) / 3) ≤ c := by
  have h := rpow_third_ge (by positivity) hw
  have hpos : 0 < C / c := by positivity
  rw [div_le_iff₀ (lt_of_lt_of_le hpos h)]
  calc C = c * (C / c) := by field_simp
    _ ≤ c * w ^ ((1 : ℝ) / 3) := by gcongr

/-! ### `StepI` is PROVED -/

theorem distInt_ge_min {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : min x (1 - x) ≤ distInt x := by
  unfold distInt
  rcases le_or_gt (round x) 0 with h | h
  · have : ((round x : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    exact (min_le_left _ _).trans (by linarith)
  · have h' : (1 : ℤ) ≤ round x := by omega
    have : (1 : ℝ) ≤ ((round x : ℤ) : ℝ) := by exact_mod_cast h'
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    exact (min_le_right _ _).trans (by linarith)

/-- **`StepI`, PROVED**: the computation on page 12 that turns the Proposition 3.2 bound into
condition (i) of Proposition 2.1, using (2.1), `1 ∈ Ω`, `η ≤ 0.05` and the symmetry of `χ`. -/
theorem stepI_proved : StepI := by
  intro M Ω η χ f δ₀ Y t hM hχ h1Ω hη0 hη hδ₀ hf hfs hY ht1 ht2 hb
  obtain ⟨hnn, hsym, hper, -, hfar, hnorm⟩ := hχ
  set k := Ω.card with hkdef
  have hk : k ≠ 0 := (card_pos.mpr ⟨_, h1Ω⟩).ne'
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by linarith
  set X' := ∑ n ∈ range M, χ n with hX'def
  have hX'0 : 0 ≤ X' := sum_nonneg fun n _ => hnn n
  have hX' : chiNorm M χ = X' / M := by unfold chiNorm; rw [inv_mul_eq_div]
  -- the sum defining `f ∗ χ(t)` runs over `n ∼ M/3`
  have hconv : convChi M f χ t = (M : ℝ)⁻¹ * ∑ n ∈ dyad M, f n * χ (t - n) := by
    unfold convChi
    congr 1
    symm
    apply sum_subset (filter_subset _ _)
    intro n hn hnd
    have : f n = 0 := by
      by_contra h0
      obtain ⟨a, b⟩ := hfs n h0
      exact hnd (mem_filter.mpr ⟨hn, a.le, b⟩)
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
  -- `A ≤ ∑_{n ∼ M/3} χ(t - n)`
  have ht0 : 0 ≤ t := by
    have : (0 : ℝ) < t := by linarith [show (0 : ℝ) ≤ M / 3 by positivity]
    exact_mod_cast this.le
  obtain ⟨tn, rfl⟩ : ∃ tn : ℕ, t = tn := ⟨t.toNat, (Int.toNat_of_nonneg ht0).symm⟩
  have ht1' : M < 3 * tn := by
    have : (M : ℝ) < 3 * tn := by push_cast at ht1; linarith
    exact_mod_cast this
  have ht2' : 3 * tn < 2 * M := by
    have : (3 : ℝ) * tn < 2 * M := by push_cast at ht2; linarith
    exact_mod_cast this
  have hdy : ∀ n : ℕ, n < M → M ≤ 3 * n → 3 * n < 2 * M → n ∈ dyad M := by
    intro n h1n h2n h3n
    simp only [dyad, mem_filter, mem_range]
    refine ⟨h1n, ?_, ?_⟩
    · have : (M : ℝ) ≤ 3 * n := by exact_mod_cast h2n
      linarith
    · have : (3 : ℝ) * n < 2 * M := by exact_mod_cast h3n
      linarith
  have hB : A ≤ ∑ n ∈ dyad M, χ ((tn : ℤ) - n) := by
    by_cases hcase : 2 * tn < M
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
          apply hdy <;> omega
        · intro n _ _; exact hnn _
      · intro a _ b _ hab
        simp only at hab
        omega
    · have e : A = ∑ m ∈ range (L + 1), χ ((tn : ℤ) - ((tn - m : ℕ) : ℤ)) := by
        apply sum_congr rfl
        intro m hm
        simp only [mem_range] at hm
        congr 1
        omega
      rw [e, ← sum_image (f := fun n : ℕ => χ ((tn : ℤ) - n)) (g := fun m => tn - m)]
      · apply sum_le_sum_of_subset_of_nonneg
        · intro n hn
          simp only [mem_image, mem_range] at hn
          obtain ⟨m, hm, rfl⟩ := hn
          apply hdy <;> omega
        · intro n _ _; exact hnn _
      · intro a ha b hb hab
        simp only [coe_range, Set.mem_Iio] at ha hb
        simp only at hab
        omega
  -- conclusion
  have hY' : Y ≤ X' / 4 := by
    rw [hX'] at hY
    have : (M : ℝ) * (X' / M) = X' := by field_simp
    rw [this] at hY
    exact hY
  have hS : δ₀ * X' / 20 ≤ ∑ n ∈ dyad M, f n * χ ((tn : ℤ) - n) := by
    have : δ₀ * (X' / 5) ≤ δ₀ * (∑ n ∈ dyad M, χ ((tn : ℤ) - n) - Y) := by
      apply mul_le_mul_of_nonneg_left _ hδ₀.le
      linarith
    nlinarith
  rw [hconv, hX']
  rw [show δ₀ / 20 * (X' / M) = (M : ℝ)⁻¹ * (δ₀ * X' / 20) by field_simp]
  exact mul_le_mul_of_nonneg_left hS (by positivity)

/-! ### The deduction on pages 11 to 12 -/

/-- **The class conclusion from Propositions 2.1, 3.2, 3.3, PROVED as an implication.**
Conditions (ii) and (iii) of Proposition 2.1 come from Proposition 3.2 with `χ ≡ 1`, in the
variant `Prop32Half`, and from Proposition 3.3 with `g = f`; condition (i) comes from
Proposition 3.2 through `StepI`; the conclusion (iv) gives (3.5) by `rep_of_conv_pos`. -/
theorem classConclusion_of_props (h21 : Prop21With (1 / 20)) (hχ : ChiExists) (h32 : Prop32)
    (h32h : Prop32Half) (h33 : Prop33) (hI : StepI) :
    ∀ ε : ℝ, 0 < ε → ∀ J : ℕ, 5 ≤ J → ∃ w : ℕ, ClassConclusion ε J w := by
  intro ε hε J hJ
  obtain ⟨δ₀, C, hδ₀, hC, H32⟩ := h32
  obtain ⟨δ₁, C₁, hδ₁, hC₁, H32h⟩ := h32h
  obtain ⟨K₃, hK₃, H3⟩ := h33 3 (by norm_num)
  obtain ⟨K₄, hK₄, H4⟩ := h33 4 (by norm_num)
  set K₀ := max 1 (max K₃ K₄)
  set δ := min δ₀ δ₁ / 20 with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨η, hη0, hη1, Ωb, H21⟩ := h21 K₀ δ (ε / 2) (le_max_left _ _) hδ (by positivity)
  obtain ⟨Cc, HCc⟩ := hχ Ωb η hη0 (by linarith)
  set c₀ := (η / 2) ^ Ωb / 4 with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  set R := max (max wBig ((Cc : ℝ) ^ 20)) (max ((C / c₀) ^ 3) ((C₁ / (1 / 12)) ^ 3))
  refine ⟨⌈R⌉₊, ?_⟩
  have hR : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
  set w := ⌈R⌉₊
  have hw1 : wBig ≤ w := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hw2 : (Cc : ℝ) ^ 20 ≤ w := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hw3 : (C / c₀) ^ 3 ≤ (w : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR
  have hw4 : (C₁ / (1 / 12)) ^ 3 ≤ (w : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hR
  have hw1' : ((1 : ℕ) : ℝ) ^ 20 ≤ w := by
    have : (1 : ℝ) ≤ wBig := by unfold wBig; exact Real.one_le_rpow (by norm_num) (by positivity)
    simp only [Nat.cast_one, one_pow]; linarith
  have hY : C / (w : ℝ) ^ ((1 : ℝ) / 3) ≤ c₀ := div_rpow_third_le hC hc₀pos hw3
  have hY₁ : C₁ / (w : ℝ) ^ ((1 : ℝ) / 3) ≤ 1 / 12 := div_rpow_third_le hC₁ (by norm_num) hw4
  obtain ⟨N₀, HN₀⟩ := H32 Cc J w hJ hw1 hw2
  obtain ⟨N₁, HN₁⟩ := H32h 1 J w hJ hw1 hw1'
  have hS := Sw_spec w
  have hSp : ∀ q ∈ Sw w, q.Prime := fun q hq => (hS q hq).1
  have hWpos : 0 < WW J w := Wmod_pos hSp
  intro B₁ B₂ hb1 hb1' hb2 hb2' hA₁ hA₂
  refine ⟨max (max N₀ N₁) 100, fun M hM => ?_⟩
  have hM0 : N₀ ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hM1 : N₁ ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hM100 : 100 ≤ M := le_trans (le_max_right _ _) hM
  have hMpos : 0 < M := by omega
  set f₁ := fW (WW J w) B₁ M
  set f₂ := fW (WW J w) B₂ M
  have hf₁ : ∀ n, 0 ≤ f₁ n := fun n => fW_nonneg _ _ hWpos M n
  have hf₂ : ∀ n, 0 ≤ f₂ n := fun n => fW_nonneg _ _ hWpos M n
  obtain ⟨Ω, hΩ, h1Ω, hΩb, H⟩ := H21 M hMpos f₁ f₂ hf₁ hf₂
  obtain ⟨χ, hχp, hχc⟩ := HCc M hMpos Ω hΩ hΩb
  have hMr : (100 : ℝ) ≤ M := by exact_mod_cast hM100
  have hnorm : (η / 2) ^ Ωb ≤ chiNorm M χ :=
    le_trans (pow_le_pow_of_le_one (by positivity) (by linarith) hΩb) hχp.2.2.2.2.2
  -- condition (i)
  have ci : ∀ t : ℤ, (M : ℝ) / 3 < t → (t : ℝ) < 2 * M / 3 → δ * chiNorm M χ ≤ convChi M f₂ χ t := by
    intro t ht1 ht2
    have hb := HN₀ χ hχp.1 hχc B₂ hb2 hb2' hA₂ M hM0 t ht1 ht2
    have hYle : C * M / (w : ℝ) ^ ((1 : ℝ) / 3) ≤ M * chiNorm M χ / 4 := by
      have e : C * M / (w : ℝ) ^ ((1 : ℝ) / 3) = M * (C / (w : ℝ) ^ ((1 : ℝ) / 3)) := by ring
      rw [e]
      have : C / (w : ℝ) ^ ((1 : ℝ) / 3) ≤ chiNorm M χ / 4 := by
        rw [hc₀] at hY; linarith
      have hM0' : (0 : ℝ) ≤ M := by positivity
      nlinarith
    have := hI M Ω η χ f₂ δ₀ _ t (by omega) hχp h1Ω hη0 hη1.le hδ₀ hf₂
      (fun n hn => ⟨(fW_ne_zero hn).1, (fW_ne_zero hn).2.1⟩) hYle ht1 ht2 hb
    have hn0 : 0 ≤ chiNorm M χ := le_trans (by positivity) hnorm
    have : δ ≤ δ₀ / 20 := by rw [hδdef]; gcongr; exact min_le_left _ _
    nlinarith
  -- condition (ii)
  have cii : δ * M ≤ ∑ n ∈ (range M).filter (fun n : ℕ => (M : ℝ) / 3 < n ∧ (n : ℝ) < M / 2),
      f₁ n := by
    show δ * M ≤ ∑ n ∈ half M, f₁ n
    have ht1 : (M : ℝ) / 3 < (((M / 2 : ℕ) : ℤ) : ℝ) := by
      rw [Int.cast_natCast]
      have : M < 3 * (M / 2) := by omega
      have : (M : ℝ) < 3 * ((M / 2 : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    have ht2 : (((M / 2 : ℕ) : ℤ) : ℝ) < 2 * M / 3 := by
      rw [Int.cast_natCast]
      have : 3 * (M / 2) < 2 * M := by omega
      have : (3 : ℝ) * ((M / 2 : ℕ) : ℝ) < 2 * M := by exact_mod_cast this
      linarith
    have hb := HN₁ (fun _ => 1) (fun _ => zero_le_one) fourierComplexity_one B₁ hb1 hb1' hA₁ M hM1 _ ht1 ht2
    simp only [mul_one, sum_const, nsmul_eq_mul] at hb
    have hc := card_half_ge M
    have e : C₁ * M / (w : ℝ) ^ ((1 : ℝ) / 3) = M * (C₁ / (w : ℝ) ^ ((1 : ℝ) / 3)) := by ring
    rw [e] at hb
    have hM0' : (0 : ℝ) ≤ M := by positivity
    have h12 : (M : ℝ) * (C₁ / (w : ℝ) ^ ((1 : ℝ) / 3)) ≤ M / 12 := by nlinarith
    have hδ1 : δ ≤ δ₁ / 20 := by rw [hδdef]; gcongr; exact min_le_right _ _
    have key : (M : ℝ) / 20 ≤ (#(half M) : ℝ) - M * (C₁ / (w : ℝ) ^ ((1 : ℝ) / 3)) := by
      linarith
    calc δ * M ≤ δ₁ / 20 * M := by gcongr
      _ = δ₁ * (M / 20) := by ring
      _ ≤ δ₁ * ((#(half M) : ℝ) - M * (C₁ / (w : ℝ) ^ ((1 : ℝ) / 3))) := by gcongr
      _ ≤ _ := hb
  -- condition (iii)
  have ciii : ∀ r ∈ ({3, 4} : Finset ℕ), ∑ ξ ∈ range M, ‖fhat M f₁ ξ‖ ^ r ≤ K₀ ∧
      ∑ ξ ∈ range M, ‖fhat M f₂ ξ‖ ^ r ≤ K₀ := by
    intro r hr
    have hK3 : K₃ ≤ K₀ := le_trans (le_max_left _ _) (le_max_right _ _)
    have hK4 : K₄ ≤ K₀ := le_trans (le_max_right _ _) (le_max_right _ _)
    simp only [mem_insert, mem_singleton] at hr
    rcases hr with rfl | rfl
    · have a1 := H3 J w hJ hw1 B₁ hb1 hb1' hA₁ M (by omega) f₁ hf₁ (fun n _ => le_rfl)
      have a2 := H3 J w hJ hw1 B₂ hb2 hb2' hA₂ M (by omega) f₂ hf₂ (fun n _ => le_rfl)
      simp only [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at a1 a2
      exact ⟨a1.trans hK3, a2.trans hK3⟩
    · have a1 := H4 J w hJ hw1 B₁ hb1 hb1' hA₁ M (by omega) f₁ hf₁ (fun n _ => le_rfl)
      have a2 := H4 J w hJ hw1 B₂ hb2 hb2' hA₂ M (by omega) f₂ hf₂ (fun n _ => le_rfl)
      simp only [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at a1 a2
      exact ⟨a1.trans hK4, a2.trans hK4⟩
  have hiv := H χ hχp ci cii ciii
  refine le_trans ?_ hiv
  have hsub : {n ∈ Icc 0 M | 9 * M ≤ 10 * n ∧ ¬ Rep (WW J w) B₁ B₂ n} ⊆
      {n ∈ Icc 0 M | 9 * M ≤ 10 * n ∧ conv M f₁ f₂ n < δ ^ 2 / 3} := by
    intro n hn
    simp only [mem_filter, mem_Icc] at hn ⊢
    refine ⟨hn.1, hn.2.1, ?_⟩
    by_contra hc
    push Not at hc
    exact hn.2.2 (rep_of_conv_pos hMpos hn.1.2 hn.2.1 (lt_of_lt_of_le (by positivity) hc))
  exact_mod_cast card_le_card hsub

/-- **Theorem 1.1, CONDITIONAL** on Proposition 2.1 in the page 11 form `η < 0.05`, the quoted
existence of `χ` with (2.1) and bounded Fourier complexity, Proposition 3.2, its page 11 variant
over `N/3 < n < N/2`, and Proposition 3.3. Everything else on pages 10 to 12 is proved. -/
theorem theorem11_conditional (h21 : Prop21With (1 / 20)) (hχ : ChiExists) (h32 : Prop32)
    (h32h : Prop32Half) (h33 : Prop33) : Theorem11 :=
  theorem11_of_classes fun ε hε hε' =>
    classConclusion_of_props h21 hχ h32 h32h h33 stepI_proved ε hε _ (by
      apply Nat.le_floor
      rw [le_div_iff₀ hε]; push_cast; linarith)

/-! ### Non-vacuity checks -/

/-- The properties (2.1) are satisfiable: `N = 1`, `Ω = {0}`, `χ ≡ 1`. -/
theorem chiProps_satisfiable {η : ℝ} (h0 : 0 < η) (h1 : η < 2) :
    ChiProps 1 {0} η (fun _ => 1) := by
  refine ⟨fun _ => zero_le_one, fun _ => rfl, fun _ => rfl, fun _ _ _ => le_rfl, ?_, ?_⟩
  · intro n hn hB
    exfalso; apply hB
    intro ξ hξ
    simp only [mem_singleton] at hξ
    subst hξ
    simp [distInt]; linarith
  · simp [chiNorm]; linarith

/-- Amenable pairs exist for every `J ≥ 5`, `w` and admissible `m`, so the class conclusion is
not vacuous; this is `local_split` for `W` of (3.3). -/
theorem amenable_pair_exists (J w : ℕ) (hJ : 5 ≤ J) :
    ∃ B₁ B₂ : ℤ, 0 ≤ B₁ ∧ B₁ < WW J w ∧ 0 ≤ B₂ ∧ B₂ < WW J w ∧
      Amenable (WW J w) B₁ ∧ Amenable (WW J w) B₂ := by
  obtain ⟨B₁, B₂, a, b, c, d, -, e, f⟩ :=
    local_split J hJ (Sw w) (Sw_spec w) 0 (dvd_zero 2) (by decide) (by decide) (by
      intro h
      have h4 : (4 : ℤ) ∣ 2 ^ J := by
        rw [show J = (J - 2) + 2 by omega, pow_add]; exact dvd_mul_left _ _
      have := h4.trans (Int.ModEq.dvd h)
      omega)
  exact ⟨B₁, B₂, a, b, c, d, e, f⟩

end LeanLab.Teravainen2016
