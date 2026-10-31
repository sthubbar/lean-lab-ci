/-
P0076 J. Teräväinen, arXiv 1611.08585, Remark 3.6: the ternary analogue of the counting
argument of pages 10 to 12. Theorem 1.2 follows, with zero sorry, from the ternary class
conclusion: for each amenable triple `W n + Bᵢ`, every large `M` is `n₁ + n₂ + n₃` with all three
`W nᵢ + Bᵢ` good, which is what Matomäki and Shao, Theorem 2.3, gives at the single point `M`.
It uses `local_split_ternary` from Ternary36.lean. Also stated: Matomäki and Shao, Theorem 2.3,
the ternary transference result the remark cites, together with the lemma that a positive
triple convolution at `N` with supports in `[N/4, N/2)` gives `N = n₁ + n₂ + n₃` exactly.
The bridge from Propositions 3.2 and 3.3 to the hypotheses of Theorem 2.3 is in
TernaryBridge.lean; Remark 3.6 describes it in words only.
AI-written Lean code, Claude, session 20261020T2317Z-cloud53, unit U-6761.
Checked only by the Lean kernel. Binary Goldbach is OPEN; ternary Goldbach is a theorem,
Helfgott 2013.
-/
import Mathlib
import LeanLab.Teravainen2016.Ternary36
import LeanLab.Teravainen2016.Transference

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- `M = n₁ + n₂ + n₃` with `W n₁ + B₁`, `W n₂ + B₂`, `W n₃ + B₃` good. -/
def Rep3 (W B₁ B₂ B₃ : ℤ) (M : ℕ) : Prop :=
  ∃ n₁ n₂ n₃ : ℕ, n₁ + n₂ + n₃ = M ∧ Good (W * n₁ + B₁) ∧ Good (W * n₂ + B₂) ∧
    Good (W * n₃ + B₃)

/-- The ternary class conclusion: for each amenable triple, every large `M` is represented. -/
def TernClass (J w : ℕ) : Prop :=
  ∀ B₁ B₂ B₃ : ℤ, 0 ≤ B₁ → B₁ < WW J w → 0 ≤ B₂ → B₂ < WW J w → 0 ≤ B₃ → B₃ < WW J w →
    Amenable (WW J w) B₁ → Amenable (WW J w) B₂ → Amenable (WW J w) B₃ →
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → Rep3 (WW J w) B₁ B₂ B₃ M

theorem isPSum3_of_rep3 {W B₁ B₂ B₃ : ℤ} {M m : ℕ} (h : Rep3 W B₁ B₂ B₃ M)
    (hm : (m : ℤ) = W * M + B₁ + B₂ + B₃) : IsPSum3 m := by
  obtain ⟨n₁, n₂, n₃, hs, h₁, h₂, h₃⟩ := h
  obtain ⟨p₁, e₁⟩ := inP_of_good h₁
  obtain ⟨p₂, e₂⟩ := inP_of_good h₂
  obtain ⟨p₃, e₃⟩ := inP_of_good h₃
  refine ⟨_, _, _, p₁, p₂, p₃, ?_⟩
  have : ((((W * n₁ + B₁).toNat + (W * n₂ + B₂).toNat + (W * n₃ + B₃).toNat : ℕ)) : ℤ) = m := by
    push_cast; rw [e₁, e₂, e₃, hm, ← hs]; push_cast; ring
  exact_mod_cast this

/-- **Theorem 1.2 from the ternary class conclusion, PROVED.** -/
theorem theorem12_of_classes (h : ∃ J w : ℕ, 5 ≤ J ∧ TernClass J w) : Theorem12 := by
  obtain ⟨J, w, hJ, hw⟩ := h
  have hS := Sw_spec w
  have hSp : ∀ q ∈ Sw w, q.Prime := fun q hq => (hS q hq).1
  set W := WW J w with hWdef
  have hWpos : 0 < W := Wmod_pos hSp
  set Wn := W.toNat with hWndef
  have hWn : (Wn : ℤ) = W := Int.toNat_of_nonneg hWpos.le
  have hWnpos : 0 < Wn := by omega
  have h2W : (2 : ℤ) ∣ W := two_pow_dvd_Wmod (J := J) (k := 1) (Sw w) (by omega)
  have hB : ∀ a : ℕ, ∃ B : ℤ × ℤ × ℤ, ¬ (2 : ℤ) ∣ a → 0 ≤ B.1 ∧ B.1 < W ∧ 0 ≤ B.2.1 ∧
      B.2.1 < W ∧ 0 ≤ B.2.2 ∧ B.2.2 < W ∧ (a : ℤ) ≡ B.1 + B.2.1 + B.2.2 [ZMOD W] ∧
      Amenable W B.1 ∧ Amenable W B.2.1 ∧ Amenable W B.2.2 := by
    intro a
    by_cases hV : ¬ (2 : ℤ) ∣ a
    · obtain ⟨B₁, B₂, B₃, h⟩ := local_split_ternary J hJ (Sw w) hS a hV
      exact ⟨(B₁, B₂, B₃), fun _ => h⟩
    · exact ⟨(0, 0, 0), fun h => absurd h hV⟩
  choose Bf hBf using hB
  have hM : ∀ a : ℕ, ∃ M₀ : ℕ, ¬ (2 : ℤ) ∣ a → ∀ M : ℕ, M₀ ≤ M →
      Rep3 W (Bf a).1 (Bf a).2.1 (Bf a).2.2 M := by
    intro a
    by_cases hV : ¬ (2 : ℤ) ∣ a
    · obtain ⟨b1, b1', b2, b2', b3, b3', _, A1, A2, A3⟩ := hBf a hV
      obtain ⟨M₀, hM₀⟩ := hw _ _ _ b1 b1' b2 b2' b3 b3' A1 A2 A3
      exact ⟨M₀, fun _ => hM₀⟩
    · exact ⟨0, fun h => absurd h hV⟩
  choose M0f hM0f using hM
  set Mx := (range Wn).sup M0f
  refine ⟨Wn * (Mx + 3), fun m hm hodd => ?_⟩
  set a := m % Wn with ha
  have haZ : (a : ℤ) = (m : ℤ) % W := by rw [ha, Int.natCast_mod, hWn]
  have hma : (a : ℤ) ≡ m [ZMOD W] := by rw [haZ]; exact Int.mod_modEq _ _
  have hV : ¬ (2 : ℤ) ∣ a := by
    intro h2
    have h' := hma.of_dvd h2W
    obtain ⟨k, hk⟩ := hodd
    unfold Int.ModEq at h'
    omega
  obtain ⟨b1, b1', b2, b2', b3, b3', hmod, -, -, -⟩ := hBf a hV
  have hmod' : (m : ℤ) ≡ (Bf a).1 + (Bf a).2.1 + (Bf a).2.2 [ZMOD W] := hma.symm.trans hmod
  have hd : W ∣ (m : ℤ) - (Bf a).1 - (Bf a).2.1 - (Bf a).2.2 := by
    have := Int.ModEq.dvd hmod'.symm
    rwa [show (m : ℤ) - ((Bf a).1 + (Bf a).2.1 + (Bf a).2.2) =
      (m : ℤ) - (Bf a).1 - (Bf a).2.1 - (Bf a).2.2 by ring] at this
  obtain ⟨Mz, hMz⟩ := hd
  have hmZ : (Wn : ℤ) * (Mx + 3) ≤ m := by exact_mod_cast hm
  rw [hWn] at hmZ
  have hMz0 : (Mx : ℤ) ≤ Mz := by
    by_contra hc
    push Not at hc
    have : W * Mz ≤ W * (Mx - 1) := mul_le_mul_of_nonneg_left (by omega) hWpos.le
    nlinarith
  obtain ⟨M, rfl⟩ : ∃ M : ℕ, Mz = M := ⟨Mz.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hle : M0f a ≤ M := by
    have : M0f a ≤ Mx := le_sup (mem_range.mpr (Nat.mod_lt _ hWnpos))
    omega
  exact isPSum3_of_rep3 (hM0f a hV M hle) (by linarith)

/-! ### Matomäki and Shao, Theorem 2.3 -/

/-- `f₁ ∗ f₂ ∗ f₃ (t) = E_{n, k ∈ ℤ_N} f₁(n) f₂(k) f₃(t - n - k)` on `ℤ_N`, for `t ≥ 0`. -/
noncomputable def conv3 (N : ℕ) (f₁ f₂ f₃ : ℕ → ℝ) (t : ℕ) : ℝ :=
  ((N : ℝ) ^ 2)⁻¹ * ∑ n ∈ range N, ∑ k ∈ range N, f₁ n * f₂ k * f₃ ((t + 2 * N - n - k) % N)

/-- Matomäki and Shao, arXiv 1512.03213, Theorem 2.3, the ternary transference result cited in
Remark 3.6, in the form with any `χ` obeying (2.1) and of Fourier complexity at most `Cc(K, δ)`,
which their Lemma 3.1 and the remark after Definition 2.4 give for the smooth Bohr cutoff. -/
def MSThm23 : Prop :=
  ∀ K δ : ℝ, 1 ≤ K → 0 < δ → ∃ η : ℝ, 0 < η ∧ η < 1 / 20 ∧ ∃ Ωb Cc N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N → ∀ f₁ : ℕ → ℝ, (∀ n, 0 ≤ f₁ n) →
    ∃ Ω : Finset ℕ, Ω ⊆ range N ∧ 1 % N ∈ Ω ∧ Ω.card ≤ Ωb ∧
    ∃ χ : ℤ → ℝ, ChiProps N Ω η χ ∧ FourierComplexityLE χ Cc ∧
    ∀ f₂ f₃ : ℕ → ℝ, (∀ n, 0 ≤ f₂ n) → (∀ n, 0 ≤ f₃ n) →
      (∀ t : ℤ, (N : ℝ) / 4 ≤ t → (t : ℝ) < N / 2 →
        δ * chiNorm N χ ≤ convChi N f₂ χ t ∧ δ * chiNorm N χ ≤ convChi N f₃ χ t) →
      δ * N ≤ ∑ n ∈ (range (N + 1)).filter (fun n : ℕ => (N : ℝ) / 10 ≤ n ∧ (n : ℝ) ≤ 2 * N / 5),
        f₁ n →
      (∑ ξ ∈ range N, ‖fhat N f₁ ξ‖ ^ ((5 : ℝ) / 2) ≤ K ∧
        ∑ ξ ∈ range N, ‖fhat N f₂ ξ‖ ^ ((5 : ℝ) / 2) ≤ K ∧
        ∑ ξ ∈ range N, ‖fhat N f₃ ξ‖ ^ ((5 : ℝ) / 2) ≤ K) →
      δ ^ 3 / 200 ≤ conv3 N f₁ f₂ f₃ N

/-- A positive triple convolution at `N`, with each `fᵢ` supported in `[N/4, N/2)`, gives
`N = n₁ + n₂ + n₃` exactly with `fᵢ(nᵢ) ≠ 0`; the wrap around remark after Theorem 2.3. -/
theorem rep3_of_conv3_pos {N : ℕ} {f₁ f₂ f₃ : ℕ → ℝ} (hN : 0 < N)
    (s₁ : ∀ n, f₁ n ≠ 0 → N ≤ 4 * n ∧ 2 * n < N) (s₂ : ∀ n, f₂ n ≠ 0 → N ≤ 4 * n ∧ 2 * n < N)
    (s₃ : ∀ n, f₃ n ≠ 0 → N ≤ 4 * n ∧ 2 * n < N) (h : 0 < conv3 N f₁ f₂ f₃ N) :
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
  obtain ⟨e1, e2⟩ := s₁ n a1
  obtain ⟨e3, e4⟩ := s₂ k a2
  set j := (N + 2 * N - n - k) % N with hj
  obtain ⟨e5, e6⟩ := s₃ j a3
  have hdm := Nat.div_add_mod (N + 2 * N - n - k) N
  rw [← hj] at hdm
  set q := (N + 2 * N - n - k) / N
  have hsum : n + k + j = N := by
    rcases Nat.lt_or_ge q 3 with hq | hq
    · interval_cases q <;> omega
    · have : N * 3 ≤ N * q := Nat.mul_le_mul_left N hq
      omega
  exact ⟨n, k, j, hsum, a1, a2, a3⟩

end LeanLab.Teravainen2016
