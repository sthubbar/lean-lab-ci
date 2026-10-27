/-
Helfgott and Platt 2013, P0006, unit U-1401, run 20261021T1203Z-6472.
The conditional dependence of Theorem 4.1 and of the top segment made explicit, each as one
Prop bundle, with vacuity instances showing that the bundle shape is satisfiable.

1. `Inputs`: binary Goldbach to 4e18 and the 492,700 range ladders of Section 4.
   `theorem4_1_of_inputs : Inputs → TernaryGoldbachUpTo T`.
2. `TopInputs`: binary Goldbach to 4e18 and ternary Goldbach to v0 + 2, about T - 2e21.
   `top_of_inputs : TopInputs → TernaryGoldbachUpTo T`. This is `Top.top_segment`, relabelled
   CONDITIONAL after verify unit U-1374; it is not an unconditional result.
3. `InputsG H W R`: the same bundle for a general half bound H, binary bound 2H, range width W
   and R ranges, with `ternary_of_inputsG` proved for even H and W. `inputs_iff` shows `Inputs`
   is exactly `InputsG (2e18) W 492700`, and `inputsG_small` is a kernel-checked instance with
   H = 50, W = 100, R = 3, giving ternary Goldbach to 351 through the range joins. So the
   bundle is not vacuous in shape; whether `Inputs` itself holds is the paper's computation.

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN.
-/
import LeanLab.HelfgottPlatt.HelfgottPlattU6816Sharp
import LeanLab.HelfgottPlatt.HelfgottPlattU6816Top

namespace LeanLab.HelfgottPlatt.U1401

open LeanLab.HelfgottPlatt LeanLab.HelfgottPlatt.Proth LeanLab.HelfgottPlatt.U6816

/-! ### The paper's bundles -/

/-- Everything Theorem 4.1 needs: binary Goldbach to 4e18 and the 492,700 range ladders. -/
def Inputs : Prop :=
  EvenGoldbachUpTo (4 * 10 ^ 18) ∧ ∃ L : ℕ → List ℕ, ∀ i < 492700, RangeOK i (L i)

/-- Theorem 4.1, CONDITIONAL ON `Inputs`. -/
theorem theorem4_1_of_inputs (h : Inputs) : TernaryGoldbachUpTo T :=
  let ⟨hB, L, hL⟩ := h
  theorem4_1_of_ranges hB L hL

/-- Everything the top segment needs: binary Goldbach to 4e18 and ternary Goldbach to v0 + 2. -/
def TopInputs : Prop :=
  EvenGoldbachUpTo (4 * 10 ^ 18) ∧ TernaryGoldbachUpTo (Top.v0 + 2)

/-- The top segment, CONDITIONAL ON `TopInputs`. -/
theorem top_of_inputs (h : TopInputs) : TernaryGoldbachUpTo T :=
  Top.top_segment h.1 h.2

/-! ### The general bundle -/

/-- The range condition for half bound `H`, binary bound `2 H`, and range width `W`. -/
def RangeOKG (H W i : ℕ) (l : List ℕ) : Prop :=
  ∃ h t, l = h :: t ∧ h.Prime ∧ 3 ≤ h ∧ (∀ p ∈ t, p.Prime) ∧
    (h :: t).IsChain (Step2 (2 * H)) ∧ h ≤ i * W + H ∧
    (i + 1) * W < t.getLastD h + H

/-- The general bundle: binary Goldbach to `2 H` and `R` range ladders. -/
def InputsG (H W R : ℕ) : Prop :=
  EvenGoldbachUpTo (2 * H) ∧ ∃ L : ℕ → List ℕ, ∀ i < R, RangeOKG H W i (L i)

/-- Ranges `0, ..., r - 1` give ternary Goldbach to `r W + H + 1`, for even `H` and `W`. -/
theorem upTo_rangesG {H W : ℕ} (hH : Even H) (hW : Even W) (hB : EvenGoldbachUpTo (2 * H))
    (L : ℕ → List ℕ) :
    ∀ r : ℕ, (∀ i < r, RangeOKG H W i (L i)) → TernaryGoldbachUpTo (r * W + H + 1) := by
  intro r
  induction r with
  | zero =>
    intro _ n hn h7 hnX
    exact base hB n hn h7 (by simp at hnX; omega)
  | succ r ih =>
    intro hL
    have hA := ih (fun i hi => hL i (by omega))
    obtain ⟨h, t, -, hp, h3, ht, hc, hstart, hend⟩ := hL r (by omega)
    have hm : Even (r * W) := hW.mul_left r
    have hsucc : (r + 1) * W = r * W + W := by ring
    rw [hsucc] at hend ⊢
    generalize r * W = m at hm hA hstart hend ⊢
    obtain ⟨a, ha⟩ := hH
    obtain ⟨b, hb⟩ := hm
    have hpA : h + 2 ≤ m + H + 1 := by
      obtain ⟨y, hy⟩ := hp.odd_of_ne_two (by omega)
      omega
    refine ternary_of_lower_and_ladder2 hB hA hp h3 hpA t ht hc ?_
    omega

/-- The general form of Theorem 4.1, CONDITIONAL ON `InputsG H W R`. -/
theorem ternary_of_inputsG {H W R : ℕ} (hH : Even H) (hW : Even W) (h : InputsG H W R) :
    TernaryGoldbachUpTo (R * W + H + 1) :=
  let ⟨hB, L, hL⟩ := h
  upTo_rangesG hH hW hB L R hL

/-- The paper's bundle is the general bundle at `H = 2e18`, `W = 2^54 · 10^9`, `R = 492700`. -/
theorem inputs_iff : Inputs ↔ InputsG (2 * 10 ^ 18) W 492700 := by
  have h4 : 2 * (2 * 10 ^ 18) = 4 * 10 ^ 18 := by norm_num
  unfold Inputs InputsG RangeOKG RangeOK
  rw [h4]

/-- Theorem 4.1 again, through the general bundle, as a cross check of `inputs_iff`. -/
theorem theorem4_1_of_inputs' (h : Inputs) : TernaryGoldbachUpTo T := by
  have := ternary_of_inputsG (by decide) (by unfold W; decide) (inputs_iff.mp h)
  rw [T_eq_RW]
  intro n hn h7 hnT
  exact this n hn h7 (le_trans hnT (by omega))

/-! ### Vacuity instances -/

/-- Small ladders for the vacuity instance: ranges of width 100, binary bound 100. -/
def Lsmall : ℕ → List ℕ
  | 0 => [3, 97]
  | 1 => [149, 151]
  | _ => [241, 251]

/-- The general bundle holds at `H = 50`, `W = 100`, `R = 3`, all kernel checked. -/
theorem inputsG_small : InputsG 50 100 3 := by
  refine ⟨LeanLab.allEvenGB_sound 100 (by decide), Lsmall, ?_⟩
  intro i hi
  interval_cases i
  · exact ⟨3, [97], rfl, by norm_num, le_rfl, by simp; norm_num,
      List.IsChain.cons_cons ⟨by norm_num, by norm_num⟩ (List.IsChain.singleton _),
      by norm_num, by simp⟩
  · exact ⟨149, [151], rfl, by norm_num, by norm_num, by simp; norm_num,
      List.IsChain.cons_cons ⟨by norm_num, by norm_num⟩ (List.IsChain.singleton _),
      by norm_num, by simp⟩
  · exact ⟨241, [251], rfl, by norm_num, by norm_num, by simp; norm_num,
      List.IsChain.cons_cons ⟨by norm_num, by norm_num⟩ (List.IsChain.singleton _),
      by norm_num, by simp⟩

/-- Vacuity of the Theorem 4.1 route: the bundle shape fires, ternary Goldbach to 351. -/
theorem vac_ranges : TernaryGoldbachUpTo 351 :=
  ternary_of_inputsG (H := 50) (W := 100) (R := 3) (by decide) (by decide) inputsG_small

/-- Vacuity of the top segment route: a lower ternary range to `p₀ + 2` with `p₀ = 349`, as in
`top_segment` where `p₀ = v0`, plus one more rung, gives ternary Goldbach to 453. -/
theorem vac_top : TernaryGoldbachUpTo 453 :=
  ternary_of_lower_and_ladder2 (LeanLab.allEvenGB_sound 100 (by decide)) vac_ranges
    (by norm_num : (349 : ℕ).Prime) (by norm_num) (by norm_num) [353]
    (by intro p hp; simp at hp; subst hp; norm_num)
    (List.IsChain.cons_cons ⟨by norm_num, by norm_num⟩ (List.IsChain.singleton _))
    (by simp)

end LeanLab.HelfgottPlatt.U1401
