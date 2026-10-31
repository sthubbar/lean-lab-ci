/-
P0070 Perelli-Pintz 1992: the cloud encoding `B`, from the repo, merged with the PC encoding.

* `psi_eq_B`, `sing_eq_B`, `delta_eq_B`: the two encodings define the same `Ψ(N, 2k)`,
  `𝔖(2k)` and error term.
* `mainTheorem_of_B`: the cloud's `B.Theorem`, real `H` and `V`, implies the PC's `MainTheorem`.
* `theoremB_of_wide`: `Estimate6Wide → Estimate7Wide → B.Theorem`, the block argument of
  `mainTheorem_of_wide` run on the integer window `[⌈V⌉, ⌊V + H⌋]`.
* `corollaryB_of_wide`: the cloud's `B.Corollary` CONDITIONAL ON the same two estimates.

AI-written Lean code, Claude, PC run 20261020T0603Z-352, unit U-1182. Checked only by the Lean
kernel. Binary Goldbach is OPEN.
-/
import LeanLab.PerelliPintz1992.MainAssembly
import LeanLab.PerelliPintz1992.B.Links
import LeanLab.PerelliPintz1992.B.SingPos

namespace LeanLab.PerelliPintz1992
open Real ArithmeticFunction MeasureTheory Set Filter

lemma psi_eq_B (N k : ℕ) : B.Psi N k = Psi N k := by
  unfold B.Psi Psi
  rw [Finset.sum_filter]

lemma sing_eq_B (k : ℕ) : B.Sing k = S2k k := by
  rw [B.sing_eq, S2k]

lemma delta_eq_B (N k : ℕ) : B.Delta N k = err N k := by
  unfold B.Delta err
  rw [psi_eq_B, sing_eq_B]

/-- The cloud's Theorem, real `H, V`, gives the PC's `MainTheorem`, natural `H, V`. -/
theorem mainTheorem_of_B (h : B.Theorem) : MainTheorem := by
  intro ε hε hε2 A hA
  obtain ⟨K, N₀, hK⟩ := h ε hε hε2 A hA
  refine ⟨K, max N₀ 2, fun N H V hN hH1 hH2 hV => ?_⟩
  have hN0 : N₀ ≤ N := by
    have : ((N₀ : ℕ) : ℝ) ≤ N := le_trans (by exact_mod_cast le_max_left N₀ 2) hN
    exact_mod_cast this
  have hN2 : (2 : ℝ) ≤ N := le_trans (by exact_mod_cast le_max_right N₀ 2) hN
  have hb := hK N hN0 H V hH1 hH2 (by positivity) hV
  have hKs : B.Ks (V : ℝ) (H : ℝ) = kRange V H := by
    unfold B.Ks kRange
    congr 1
    rw [Nat.ceil_natCast, show (V : ℝ) + H = ((V + H : ℕ) : ℝ) by push_cast; ring,
      Nat.floor_natCast]
  rw [hKs] at hb
  simp_rw [delta_eq_B] at hb
  refine hb.trans (le_of_eq ?_)
  have hl : 0 < Real.log N := Real.log_pos (by linarith)
  rw [Real.rpow_neg hl.le, L]
  field_simp

theorem theoremB_of_wide (h6 : Estimate6Wide) (h7 : Estimate7Wide) : B.Theorem := by
  intro ε hε hε2 A hA
  obtain ⟨ε1, hε1, h6⟩ := h6
  obtain ⟨ε2, hε2', h7⟩ := h7
  set ε' := min ε (min ε1 ε2) / 2 with hε'
  have hm1 : min ε (min ε1 ε2) ≤ ε := min_le_left _ _
  have hm2 : min ε (min ε1 ε2) ≤ ε1 := (min_le_right _ _).trans (min_le_left _ _)
  have hm3 : min ε (min ε1 ε2) ≤ ε2 := (min_le_right _ _).trans (min_le_right _ _)
  have hmpos : 0 < min ε (min ε1 ε2) := lt_min hε (lt_min hε1 hε2')
  have he'pos : 0 < ε' := by rw [hε']; linarith
  have he'1 : ε' < ε1 := by rw [hε']; linarith
  have he'2 : ε' < ε2 := by rw [hε']; linarith
  have he'e : ε' ≤ ε := by rw [hε']; linarith
  have hA' : 0 < 2 * A + 5 := by linarith
  obtain ⟨C6, N6, hC6⟩ := h6 ε' he'pos he'1 (2 * A + 5) hA'
  obtain ⟨C7, N7, hC7⟩ := h7 ε' he'pos he'2 (2 * A + 5) hA'
  have hev : ∀ᶠ N : ℕ in atTop, 16 ≤ N ∧ L N ^ Bexp (2 * A + 5) ≤ √(N : ℝ) / 4 ∧
      L N ^ (A + 4) ≤ √(N : ℝ) / 4 :=
    (eventually_ge_atTop 16).and ((eventually_logpow_le _).and (eventually_logpow_le _))
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hev
  set K := 640 * max C7 0 + 32 + 2 * max C6 0 with hK
  refine ⟨2 * K, max (max N1 ⌈N6⌉₊) ⌈N7⌉₊, fun N hN Hr Vr hH1 hH2 hV0 hV => ?_⟩
  have hNN1 : N1 ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  obtain ⟨hN16, hLB, hLδ⟩ := hN1 N hNN1
  have hN6 : N6 ≤ N := (Nat.le_ceil N6).trans
    (by exact_mod_cast le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN))
  have hN7 : N7 ≤ N := (Nat.le_ceil N7).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN16
  have hNpos : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ L N := by
    unfold L
    rw [Real.le_log_iff_exp_le hNpos]
    have := Real.exp_one_lt_d9
    linarith
  set h0 := (N : ℝ) ^ (1 / 2 + ε') with hh0
  have hsq : √(N : ℝ) ≤ h0 := by
    rw [Real.sqrt_eq_rpow, hh0]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hh0pos : 0 < h0 := Real.rpow_pos_of_pos hNpos _
  have hδ : L N ^ (A + 4) ≤ h0 / 2 := by
    have : 0 ≤ √(N : ℝ) := Real.sqrt_nonneg _
    linarith
  have hh0H : h0 < Hr := by
    refine lt_of_le_of_lt ?_ hH1
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  set H0 := ⌊h0⌋₊ with hH0
  -- the integer window
  set V := ⌈Vr⌉₊ with hVdef
  set H := ⌊Vr + Hr⌋₊ - ⌈Vr⌉₊ with hHdef
  have hHr0 : 0 ≤ Hr := le_trans hh0pos.le hh0H.le
  have hHle : (H : ℝ) ≤ Hr := by
    rcases le_or_gt ⌈Vr⌉₊ ⌊Vr + Hr⌋₊ with hc | hc
    · rw [hHdef, Nat.cast_sub hc]
      have h1 := Nat.floor_le (show 0 ≤ Vr + Hr by linarith)
      have h2 := Nat.le_ceil Vr
      linarith
    · rw [hHdef, Nat.sub_eq_zero_of_le hc.le]; simpa using hHr0
  have hVH : ((V + H : ℕ) : ℝ) < N / 2 := by
    rcases le_or_gt ⌈Vr⌉₊ ⌊Vr + Hr⌋₊ with hc | hc
    · rw [show V + H = ⌊Vr + Hr⌋₊ by omega]
      have := Nat.floor_le (show 0 ≤ Vr + Hr by linarith)
      linarith
    · rw [show V + H = ⌈Vr⌉₊ by omega]
      have := Nat.ceil_lt_add_one hV0
      linarith
  set P := L N ^ A with hP
  have hPpos : 0 < P := Real.rpow_pos_of_pos (by linarith) _
  have hK0 : 0 ≤ K := by positivity
  -- each block
  have hblock : ∀ i ∈ Finset.range (H / (H0 + 1) + 1),
      ∑ k ∈ kRange (V + i * (H0 + 1)) H0, err N k ^ 2 ≤ K * (h0 * N ^ 2 / P) := by
    intro i hi
    have hiH : i * (H0 + 1) ≤ H := by
      have : i ≤ H / (H0 + 1) := by simp only [Finset.mem_range] at hi; omega
      calc i * (H0 + 1) ≤ H / (H0 + 1) * (H0 + 1) := Nat.mul_le_mul_right _ this
        _ ≤ H := Nat.div_mul_le_self H (H0 + 1)
    have hVi : ((V + i * (H0 + 1) : ℕ) : ℝ) < N / 2 := by
      have : ((V + i * (H0 + 1) : ℕ) : ℝ) ≤ ((V + H : ℕ) : ℝ) := by exact_mod_cast (by omega : V + i * (H0 + 1) ≤ V + H)
      linarith
    have hX : 0 ≤ h0 * (N : ℝ) ^ 2 / L N ^ (2 * A + 5) := by
      have : 0 < L N ^ (2 * A + 5) := Real.rpow_pos_of_pos (by linarith) _
      positivity
    have hb6 := hC6 N (V + i * (H0 + 1)) hN6 hVi
    have hb6' : ∑ k ∈ (Finset.Icc (V + i * (H0 + 1)) (V + i * (H0 + 1) + ⌊(N : ℝ) ^ (1 / 2 + ε')⌋₊)).filter (1 ≤ ·),
      ‖(∫ α in majorArcs N (2 * A + 5), ((‖S N α‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * α))) -
        (S2k k * ((N : ℝ) - 2 * k) : ℝ)‖ ^ 2 ≤
      max C6 0 * (N : ℝ) ^ (1 / 2 + ε') * N ^ 2 / L N ^ (2 * A + 5) := by
      refine hb6.trans ?_
      have e1 : C6 * (N : ℝ) ^ (1 / 2 + ε') * N ^ 2 / L N ^ (2 * A + 5) =
          C6 * (h0 * (N : ℝ) ^ 2 / L N ^ (2 * A + 5)) := by rw [hh0]; ring
      have e2 : max C6 0 * (N : ℝ) ^ (1 / 2 + ε') * N ^ 2 / L N ^ (2 * A + 5) =
          max C6 0 * (h0 * (N : ℝ) ^ 2 / L N ^ (2 * A + 5)) := by rw [hh0]; ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX
    have hb7 : ∀ ξ : ℝ,
        ∫ α in Set.Ioo (ξ - 1 / (N : ℝ) ^ (1 / 2 + ε')) (ξ + 1 / (N : ℝ) ^ (1 / 2 + ε')) ∩
          minorArcs N (2 * A + 5), ‖S N α‖ ^ 2 ≤ max C7 0 * N / L N ^ (2 * A + 5 + 1) := by
      intro ξ
      refine (hC7 N hN7 ξ).trans ?_
      have : 0 < L N ^ (2 * A + 5 + 1) := Real.rpow_pos_of_pos (by linarith) _
      rw [div_le_div_iff_of_pos_right this]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hNpos.le
    exact block_bound hA hN16 (le_max_right _ _) (le_max_right _ _) hL1 hLB hδ hb6' hb7
  -- sum over blocks
  have hnonneg : ∀ k, 0 ≤ err N k ^ 2 := fun k => sq_nonneg _
  have hKs : B.Ks Vr Hr ⊆ kRange V H := by
    intro k hk
    simp only [B.Ks, kRange, Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    refine ⟨⟨hk.1.1, by omega⟩, hk.2⟩
  have hD : ∑ k ∈ B.Ks Vr Hr, B.Delta N k ^ 2 ≤ ∑ k ∈ kRange V H, err N k ^ 2 := by
    simp_rw [delta_eq_B]
    exact Finset.sum_le_sum_of_subset_of_nonneg hKs (fun k _ _ => hnonneg k)
  refine hD.trans ?_
  have hsum := (Finset.sum_le_sum_of_subset_of_nonneg (kRange_subset_blocks V H H0)
    (fun k _ _ => hnonneg k)).trans (sum_biUnion_range_le hnonneg _ _)
  refine hsum.trans ?_
  refine (Finset.sum_le_sum hblock).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- count of blocks
  have hnb : ((H / (H0 + 1) + 1 : ℕ) : ℝ) ≤ 2 * Hr / h0 := by
    push_cast
    have h1 : ((H / (H0 + 1) : ℕ) : ℝ) ≤ (H : ℝ) / ((H0 : ℝ) + 1) := by
      have := Nat.cast_div_le (α := ℝ) (m := H) (n := H0 + 1)
      push_cast at this; exact this
    have h2 : (H : ℝ) / ((H0 : ℝ) + 1) ≤ H / h0 := by
      apply div_le_div_of_nonneg_left (by positivity) hh0pos
      exact (Nat.lt_floor_add_one h0).le
    have h2' : (H : ℝ) / h0 ≤ Hr / h0 := div_le_div_of_nonneg_right hHle hh0pos.le
    have h3 : 1 ≤ Hr / h0 := by rw [le_div_iff₀ hh0pos]; linarith
    have : (2 : ℝ) * Hr / h0 = Hr / h0 + Hr / h0 := by ring
    linarith
  calc ((H / (H0 + 1) + 1 : ℕ) : ℝ) * (K * (h0 * N ^ 2 / P))
      ≤ 2 * Hr / h0 * (K * (h0 * N ^ 2 / P)) := by
        apply mul_le_mul_of_nonneg_right hnb; positivity
    _ = 2 * K * Hr * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
        rw [Real.rpow_neg (Real.log_nonneg (by linarith))]
        have : P = Real.log N ^ A := rfl
        rw [← this]; field_simp


/-- The cloud's Corollary, CONDITIONAL ON the wide forms of (6) and (7). -/
theorem corollaryB_of_wide (h6 : Estimate6Wide) (h7 : Estimate7Wide) : B.Corollary :=
  B.corollary_of (theoremB_of_wide h6 h7)

#print axioms psi_eq_B
#print axioms sing_eq_B
#print axioms delta_eq_B
#print axioms mainTheorem_of_B
#print axioms theoremB_of_wide
#print axioms corollaryB_of_wide

end LeanLab.PerelliPintz1992
