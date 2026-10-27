/-
P0076 J. Teräväinen, arXiv 1611.08585, the counting argument on pages 10 to 12 in the proof of
Theorem 1.1 assuming Propositions 3.2 and 3.3. This file proves, with zero sorry, that Theorem 1.1
follows from the per residue class conclusion of the transference step: for each amenable pair
`W n + B₁`, `W n + B₂`, all but `≤ (ε/2) M` of the `n ∈ [0.9 M, M]` are `n₁ + n₂` with
`W nᵢ + Bᵢ ∈ ℙ` and `W nᵢ + Bᵢ - 1 ∈ 𝒮`, display (3.5). It uses `local_split` from Amenable.lean,
the bound for the `m ≡ 2 (mod 2^J)` and for the edge `[0.9N, 0.9N + 2W]`, the sum over the
residues `a mod W`, and the passage from `[0.9N, N]` to `[1, N]` that the paper leaves implicit.
The class conclusion itself is derived from Propositions 2.1, 3.2 and 3.3 in Transference.lean.
AI-written Lean code, Claude, session 20261020T2317Z-cloud53, unit U-6761.
Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Teravainen2016.Amenable

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-! ### The set `𝒮` of (3.2) and the good values of (3.5) -/

/-- `𝒮 = {a² + b² : a, b ∈ ℤ, (a, b) ∣ 6^∞}`, display (3.2). -/
def SSet : Set ℤ := {s | ∃ a b : ℤ, s = a ^ 2 + b ^ 2 ∧ ∃ k : ℕ, (Int.gcd a b : ℤ) ∣ 6 ^ k}

/-- `x ∈ ℙ` and `x - 1 ∈ 𝒮`, the condition in (3.4) and (3.5). -/
def Good (x : ℤ) : Prop := 0 < x ∧ x.toNat.Prime ∧ x - 1 ∈ SSet

/-- `n = n₁ + n₂` with `W n₁ + B₁` and `W n₂ + B₂` good, display (3.5). -/
def Rep (W B₁ B₂ : ℤ) (n : ℕ) : Prop :=
  ∃ n₁ n₂ : ℕ, n₁ + n₂ = n ∧ Good (W * n₁ + B₁) ∧ Good (W * n₂ + B₂)

/-- The primes `5 ≤ p ≤ w` of (3.3). -/
def Sw (w : ℕ) : Finset ℕ := (Icc 5 w).filter Nat.Prime

/-- `W = 2^J · 3^3 · ∏_{5 ≤ p ≤ w} p`, display (3.3). -/
def WW (J w : ℕ) : ℤ := Wmod J (Sw w)

theorem Sw_spec (w : ℕ) : ∀ q ∈ Sw w, q.Prime ∧ 5 ≤ q := by
  intro q hq
  simp only [Sw, mem_filter, mem_Icc] at hq
  exact ⟨hq.2, hq.1.1⟩

/-- The conclusion of the transference step for one residue class, page 12: for each amenable
pair, for `M` large, at most `(ε/2) M` of the `n ∈ [0.9 M, M]` fail (3.5). -/
def ClassConclusion (ε : ℝ) (J w : ℕ) : Prop :=
  ∀ B₁ B₂ : ℤ, 0 ≤ B₁ → B₁ < WW J w → 0 ≤ B₂ → B₂ < WW J w →
    Amenable (WW J w) B₁ → Amenable (WW J w) B₂ →
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      (#{n ∈ Icc 0 M | 9 * M ≤ 10 * n ∧ ¬ Rep (WW J w) B₁ B₂ n} : ℝ) ≤ ε / 2 * M

/-! ### Good values are primes of `𝒫` -/

theorem inP_of_good {x : ℤ} (h : Good x) : InP x.toNat ∧ ((x.toNat : ℕ) : ℤ) = x := by
  obtain ⟨hx, hp, a, b, hab, -⟩ := h
  have e : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg hx.le
  exact ⟨⟨hp, a, b, by rw [e]; linear_combination hab⟩, e⟩

theorem isPSum2_of_rep {W B₁ B₂ : ℤ} {n m : ℕ} (h : Rep W B₁ B₂ n)
    (hm : (m : ℤ) = W * n + B₁ + B₂) : IsPSum2 m := by
  obtain ⟨n₁, n₂, hs, h₁, h₂⟩ := h
  obtain ⟨p₁, e₁⟩ := inP_of_good h₁
  obtain ⟨p₂, e₂⟩ := inP_of_good h₂
  refine ⟨_, _, p₁, p₂, ?_⟩
  have : ((((W * n₁ + B₁).toNat + (W * n₂ + B₂).toNat : ℕ)) : ℤ) = m := by
    push_cast; rw [e₁, e₂, hm, ← hs]; push_cast; ring
  exact_mod_cast this

/-! ### From `[0.9 N, N]` to `[1, N]` -/

/-- The exceptional count in `[0.9 N, N]`. -/
noncomputable def excTop (R : ℕ → Prop) (N : ℕ) : ℕ :=
  #{n ∈ Icc 1 N | 9 * N ≤ 10 * n ∧ Even n ∧ n % 9 ≠ 5 ∧ n % 9 ≠ 8 ∧ ¬ R n}

theorem excCount_le_N (R : ℕ → Prop) (N : ℕ) : excCount R N ≤ N := by
  unfold excCount
  exact (card_filter_le _ _).trans (by simp)

theorem excCount_le_rec (R : ℕ → Prop) (N : ℕ) :
    excCount R N ≤ excCount R ((9 * N - 1) / 10) + excTop R N := by
  unfold excCount excTop
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro n hn
  simp only [mem_filter, mem_Icc, mem_union] at hn ⊢
  by_cases h : 9 * N ≤ 10 * n
  · exact Or.inr ⟨hn.1, h, hn.2⟩
  · exact Or.inl ⟨⟨hn.1.1, by omega⟩, hn.2⟩

theorem excCount_bound (R : ℕ → Prop) {ε : ℝ} (hε : 0 ≤ ε) (N₀ : ℕ)
    (h : ∀ N, N₀ ≤ N → (excTop R N : ℝ) ≤ ε * N) :
    ∀ N : ℕ, (excCount R N : ℝ) ≤ N₀ + 10 * ε * N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    by_cases hN : N < N₀ ∨ N = 0
    · have h1 : (excCount R N : ℝ) ≤ N := by exact_mod_cast excCount_le_N R N
      rcases hN with hN | hN
      · have : (N : ℝ) ≤ N₀ := by exact_mod_cast hN.le
        nlinarith [show (0 : ℝ) ≤ N by positivity]
      · subst hN; simp at h1 ⊢; nlinarith [show (0 : ℝ) ≤ N₀ by positivity]
    · push Not at hN
      set N' := (9 * N - 1) / 10 with hN'
      have hlt : N' < N := by omega
      have h10 : 10 * N' ≤ 9 * N := by omega
      have h10' : (10 : ℝ) * N' ≤ 9 * N := by exact_mod_cast h10
      have hrec : (excCount R N : ℝ) ≤ excCount R N' + excTop R N := by
        exact_mod_cast excCount_le_rec R N
      have := ih N' hlt
      have := h N hN.1
      nlinarith

theorem almostAll_of_top (R : ℕ → Prop)
    (h : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → (excTop R N : ℝ) ≤ ε * N) :
    AlmostAllAdmissible R := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := h (ε / 20) (by positivity)
  have hb := excCount_bound R (by positivity) N₀ hN₀
  refine ⟨⌈2 * N₀ / ε⌉₊, fun N hN => ?_⟩
  have h1 : 2 * (N₀ : ℝ) / ε ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have h2 : 2 * (N₀ : ℝ) ≤ ε * N := by rw [div_le_iff₀ hε] at h1; linarith
  have := hb N
  nlinarith

/-! ### Small arithmetic helpers -/

theorem natCast_modEq_two_iff {m P : ℕ} (hP : 2 < P) :
    (m : ℤ) ≡ 2 [ZMOD (P : ℤ)] ↔ m % P = 2 := by
  unfold Int.ModEq
  rw [Int.emod_eq_of_lt (a := 2) (by norm_num) (by exact_mod_cast hP), ← Int.natCast_mod]
  constructor
  · intro h; exact_mod_cast h
  · intro h; rw [h]; rfl

theorem card_mod_eq_two_le (N P : ℕ) (hP : 0 < P) :
    #{n ∈ Icc 1 N | n % P = 2} ≤ N / P + 1 := by
  have : #{n ∈ Icc 1 N | n % P = 2} ≤ #(range (N / P + 1)) := by
    refine card_le_card_of_injOn (fun n => n / P) ?_ ?_
    · intro n hn
      simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at hn
      simp only [coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right hn.1.2)
    · intro a ha b hb hab
      simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at ha hb
      simp only at hab
      rw [← Nat.div_add_mod a P, ← Nat.div_add_mod b P, hab, ha.2, hb.2]
  simpa using this

/-- The integer `n` attached to `m` in a class, page 12: `m = W n + B₁ + B₂` with
`n ∈ [0.9 M', M']`, `M' = ⌊N / W⌋`, once `m ∈ [0.9 N + 2W, N]`. -/
theorem index_facts {W B₁ B₂ : ℤ} (hW : 0 < W) (h1 : 0 ≤ B₁) (h1' : B₁ < W) (h2 : 0 ≤ B₂)
    (h2' : B₂ < W) {m N : ℕ} (hmod : (m : ℤ) ≡ B₁ + B₂ [ZMOD W]) (hmN : m ≤ N)
    (hm : 9 * (N : ℤ) + 20 * W ≤ 10 * m) :
    (m : ℤ) = W * (((m : ℤ) - B₁ - B₂) / W) + B₁ + B₂ ∧ 0 ≤ ((m : ℤ) - B₁ - B₂) / W ∧
      ((m : ℤ) - B₁ - B₂) / W ≤ (N : ℤ) / W ∧ 9 * ((N : ℤ) / W) ≤ 10 * (((m : ℤ) - B₁ - B₂) / W) := by
  have hd : W ∣ (m : ℤ) - B₁ - B₂ := by
    have := (Int.ModEq.dvd hmod.symm)
    rwa [show (m : ℤ) - (B₁ + B₂) = (m : ℤ) - B₁ - B₂ by ring] at this
  set n := ((m : ℤ) - B₁ - B₂) / W with hn
  have e : W * n = (m : ℤ) - B₁ - B₂ := Int.mul_ediv_cancel' hd
  have hM : (N : ℤ) / W * W ≤ N := Int.ediv_mul_le _ hW.ne'
  set M := (N : ℤ) / W
  refine ⟨by linarith, ?_, ?_, ?_⟩
  · by_contra hc
    push Not at hc
    nlinarith
  · apply Int.le_ediv_of_mul_le hW
    nlinarith
  · by_contra hc
    push Not at hc
    nlinarith

/-! ### The counting argument -/

/-- **Theorem 1.1 from the class conclusion, PROVED.** If for every `0 < ε ≤ 1/2` there is `w`
such that, with `J = ⌊10/ε⌋` and `W` as in (3.3), every amenable pair satisfies the class
conclusion of page 12, then Theorem 1.1 holds. -/
theorem theorem11_of_classes
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ w : ℕ, ClassConclusion ε ⌊10 / ε⌋₊ w) : Theorem11 := by
  apply almostAll_of_top
  intro ε hε
  set ε₁ := min ε (1 / 2) with hε₁def
  have hε₁ : 0 < ε₁ := lt_min hε (by norm_num)
  have hε₁h : ε₁ ≤ 1 / 2 := min_le_right _ _
  have hε₁e : ε₁ ≤ ε := min_le_left _ _
  obtain ⟨w, hw⟩ := h ε₁ hε₁ hε₁h
  set J := ⌊10 / ε₁⌋₊ with hJdef
  have hJ : 5 ≤ J := by
    apply Nat.le_floor
    rw [le_div_iff₀ hε₁]; push_cast; linarith
  have hS := Sw_spec w
  have hSp : ∀ q ∈ Sw w, q.Prime := fun q hq => (hS q hq).1
  set W := WW J w with hWdef
  have hWpos : 0 < W := Wmod_pos hSp
  set Wn := W.toNat with hWndef
  have hWn : (Wn : ℤ) = W := Int.toNat_of_nonneg hWpos.le
  have hWnpos : 0 < Wn := by omega
  have hPJ : (2 : ℕ) < 2 ^ J := by
    calc (2 : ℕ) < 2 ^ 5 := by norm_num
      _ ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) hJ
  -- the admissible residues
  let V : ℕ → Prop := fun a => (2 : ℤ) ∣ a ∧ ¬ (a : ℤ) ≡ 5 [ZMOD 9] ∧ ¬ (a : ℤ) ≡ 8 [ZMOD 9] ∧
    ¬ (a : ℤ) ≡ 2 [ZMOD 2 ^ J]
  have hB : ∀ a : ℕ, ∃ B : ℤ × ℤ, V a → 0 ≤ B.1 ∧ B.1 < W ∧ 0 ≤ B.2 ∧ B.2 < W ∧
      (a : ℤ) ≡ B.1 + B.2 [ZMOD W] ∧ Amenable W B.1 ∧ Amenable W B.2 := by
    intro a
    by_cases hV : V a
    · obtain ⟨B₁, B₂, h⟩ := local_split J hJ (Sw w) hS a hV.1 hV.2.1 hV.2.2.1 hV.2.2.2
      exact ⟨(B₁, B₂), fun _ => h⟩
    · exact ⟨(0, 0), fun h => absurd h hV⟩
  choose Bf hBf using hB
  have hM : ∀ a : ℕ, ∃ M₀ : ℕ, V a → ∀ M : ℕ, M₀ ≤ M →
      (#{n ∈ Icc 0 M | 9 * M ≤ 10 * n ∧ ¬ Rep W (Bf a).1 (Bf a).2 n} : ℝ) ≤ ε₁ / 2 * M := by
    intro a
    by_cases hV : V a
    · obtain ⟨b1, b1', b2, b2', _, A1, A2⟩ := hBf a hV
      obtain ⟨M₀, hM₀⟩ := hw _ _ b1 b1' b2 b2' A1 A2
      exact ⟨M₀, fun _ => hM₀⟩
    · exact ⟨0, fun h => absurd h hV⟩
  choose M0f hM0f using hM
  set Mx := (range Wn).sup M0f
  refine ⟨max (Wn * (Mx + 1)) ⌈(6 * Wn + 6) / ε₁⌉₊, fun N hN => ?_⟩
  have hN1 : Wn * (Mx + 1) ≤ N := (le_max_left _ _).trans hN
  have hN2 : (6 * (Wn : ℝ) + 6) / ε₁ ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hN)
  set M' := N / Wn with hM'def
  have hM'Mx : Mx + 1 ≤ M' := by
    rw [hM'def]; exact (Nat.le_div_iff_mul_le hWnpos).mpr (by linarith [hN1])
  -- the three pieces
  set T := (Icc 1 N).filter
    (fun n => 9 * N ≤ 10 * n ∧ Even n ∧ n % 9 ≠ 5 ∧ n % 9 ≠ 8 ∧ ¬ IsPSum2 n) with hT
  set A1 := (Icc 1 N).filter (fun n => n % 2 ^ J = 2)
  set A2 := Ico (9 * N / 10) (9 * N / 10 + 2 * Wn + 1)
  set A3 := T.filter (fun n => n % 2 ^ J ≠ 2 ∧ 9 * N + 20 * Wn ≤ 10 * n)
  have hsplit : T ⊆ A1 ∪ A2 ∪ A3 := by
    intro n hn
    have hn' := hn
    simp only [hT, mem_filter, mem_Icc] at hn'
    simp only [mem_union, A1, A2, A3, mem_filter, mem_Icc, mem_Ico]
    by_cases h2 : n % 2 ^ J = 2
    · exact Or.inl (Or.inl ⟨hn'.1, h2⟩)
    · by_cases h3 : 9 * N + 20 * Wn ≤ 10 * n
      · exact Or.inr ⟨hn, h2, h3⟩
      · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
  -- count of `A1`
  have hA1 : (#A1 : ℝ) ≤ ε₁ ^ 2 / 10 * N + 1 := by
    have h1 : #A1 ≤ N / 2 ^ J + 1 := card_mod_eq_two_le N (2 ^ J) (by positivity)
    have h2 : ((N / 2 ^ J : ℕ) : ℝ) ≤ (N : ℝ) / 2 ^ J := by
      have := Nat.cast_div_le (α := ℝ) (m := N) (n := 2 ^ J); push_cast at this; exact this
    have h3 : 10 ≤ ε₁ ^ 2 * 2 ^ J := two_pow_floor_bound hε₁
    have h4 : (N : ℝ) / 2 ^ J ≤ ε₁ ^ 2 / 10 * N := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [show (0 : ℝ) ≤ N by positivity]
    have : (#A1 : ℝ) ≤ ((N / 2 ^ J : ℕ) : ℝ) + 1 := by exact_mod_cast h1
    linarith
  have hA2 : (#A2 : ℝ) ≤ 2 * Wn + 1 := by
    have : #A2 = 2 * Wn + 1 := by simp only [A2]; rw [Nat.card_Ico]; omega
    rw [this]; push_cast; exact le_rfl
  -- count of `A3` through the residue classes
  set tgt := (range Wn ×ˢ Icc 0 M').filter
    (fun p => V p.1 ∧ 9 * M' ≤ 10 * p.2 ∧ ¬ Rep W (Bf p.1).1 (Bf p.1).2 p.2)
  have hA3 : #A3 ≤ #tgt := by
    refine card_le_card_of_injOn
      (fun m => (m % Wn, (((m : ℤ) - (Bf (m % Wn)).1 - (Bf (m % Wn)).2) / W).toNat)) ?_ ?_
    · intro m hm
      simp only [A3, hT, coe_filter, mem_filter, mem_Icc, Set.mem_ofPred_eq] at hm
      obtain ⟨⟨⟨hm1, hmN⟩, h9, hev, h5, h8, hnp⟩, h2J, hedge⟩ := hm
      set a := m % Wn with ha
      have haZ : (a : ℤ) = (m : ℤ) % W := by rw [ha, Int.natCast_mod, hWn]
      have hma : (a : ℤ) ≡ m [ZMOD W] := by rw [haZ]; exact Int.mod_modEq _ _
      have hV : V a := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · have h2W : (2 : ℤ) ∣ W := (two_pow_dvd_Wmod (J := J) (k := 1) (Sw w) (by omega))
          have := hma.of_dvd h2W
          obtain ⟨k, hk⟩ := hev
          have : (m : ℤ) % 2 = 0 := by omega
          exact Int.dvd_of_emod_eq_zero (by unfold Int.ModEq at *; omega)
        · intro hc
          have := (hma.symm.of_dvd ((by norm_num : (9 : ℤ) ∣ 27).trans (dvd27_Wmod J _))).trans hc
          unfold Int.ModEq at this; omega
        · intro hc
          have := (hma.symm.of_dvd ((by norm_num : (9 : ℤ) ∣ 27).trans (dvd27_Wmod J _))).trans hc
          unfold Int.ModEq at this; omega
        · intro hc
          have := (hma.symm.of_dvd (two_pow_dvd_Wmod (Sw w) le_rfl)).trans hc
          have h' : (m : ℤ) ≡ 2 [ZMOD ((2 ^ J : ℕ) : ℤ)] := by push_cast; exact this
          exact h2J ((natCast_modEq_two_iff hPJ).mp h')
      obtain ⟨b1, b1', b2, b2', hmod, -, -⟩ := hBf a hV
      have hmod' : (m : ℤ) ≡ (Bf a).1 + (Bf a).2 [ZMOD W] := hma.symm.trans hmod
      have hedge' : 9 * (N : ℤ) + 20 * W ≤ 10 * m := by rw [← hWn]; exact_mod_cast hedge
      obtain ⟨e, n0, nM, n9⟩ := index_facts hWpos b1 b1' b2 b2' hmod' hmN hedge'
      set nZ := ((m : ℤ) - (Bf a).1 - (Bf a).2) / W
      have hNW : (N : ℤ) / W = ((M' : ℕ) : ℤ) := by rw [hM'def, Int.natCast_div, hWn]
      have ent : ((nZ.toNat : ℕ) : ℤ) = nZ := Int.toNat_of_nonneg n0
      refine Finset.mem_coe.mpr (mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr
        (Nat.mod_lt _ hWnpos), mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩⟩, hV, ?_, ?_⟩)
      · have : ((nZ.toNat : ℕ) : ℤ) ≤ (M' : ℤ) := by rw [ent, ← hNW]; exact nM
        exact_mod_cast this
      · have : (9 * M' : ℤ) ≤ 10 * ((nZ.toNat : ℕ) : ℤ) := by rw [ent, ← hNW]; exact n9
        exact_mod_cast this
      · intro hrep
        apply hnp
        exact isPSum2_of_rep hrep (by rw [ent]; exact e)
    · intro m hm m' hm' heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨ha, hn⟩ := heq
      simp only [A3, hT, coe_filter, mem_filter, mem_Icc, Set.mem_ofPred_eq] at hm hm'
      -- recover `m` from its class and index
      have key : ∀ x : ℕ, x ∈ A3 → (x : ℤ) = W * ((((x : ℤ) - (Bf (x % Wn)).1 -
          (Bf (x % Wn)).2) / W).toNat : ℕ) + (Bf (x % Wn)).1 + (Bf (x % Wn)).2 := by
        intro x hx
        simp only [A3, hT, mem_filter, mem_Icc] at hx
        obtain ⟨⟨⟨hx1, hxN⟩, h9, hev, h5, h8, hnp⟩, h2J, hedge⟩ := hx
        set a := x % Wn with ha
        have haZ : (a : ℤ) = (x : ℤ) % W := by rw [ha, Int.natCast_mod, hWn]
        have hma : (a : ℤ) ≡ x [ZMOD W] := by rw [haZ]; exact Int.mod_modEq _ _
        have hV : V a := by
          refine ⟨?_, ?_, ?_, ?_⟩
          · have h2W : (2 : ℤ) ∣ W := (two_pow_dvd_Wmod (J := J) (k := 1) (Sw w) (by omega))
            have := hma.of_dvd h2W
            obtain ⟨k, hk⟩ := hev
            have : (x : ℤ) % 2 = 0 := by omega
            exact Int.dvd_of_emod_eq_zero (by unfold Int.ModEq at *; omega)
          · intro hc
            have := (hma.symm.of_dvd ((by norm_num : (9 : ℤ) ∣ 27).trans (dvd27_Wmod J _))).trans hc
            unfold Int.ModEq at this; omega
          · intro hc
            have := (hma.symm.of_dvd ((by norm_num : (9 : ℤ) ∣ 27).trans (dvd27_Wmod J _))).trans hc
            unfold Int.ModEq at this; omega
          · intro hc
            have := (hma.symm.of_dvd (two_pow_dvd_Wmod (Sw w) le_rfl)).trans hc
            have h' : (x : ℤ) ≡ 2 [ZMOD ((2 ^ J : ℕ) : ℤ)] := by push_cast; exact this
            exact h2J ((natCast_modEq_two_iff hPJ).mp h')
        obtain ⟨b1, b1', b2, b2', hmod, -, -⟩ := hBf a hV
        have hmod' : (x : ℤ) ≡ (Bf a).1 + (Bf a).2 [ZMOD W] := hma.symm.trans hmod
        have hedge' : 9 * (N : ℤ) + 20 * W ≤ 10 * x := by rw [← hWn]; exact_mod_cast hedge
        obtain ⟨e, n0, -, -⟩ := index_facts hWpos b1 b1' b2 b2' hmod' hxN hedge'
        rw [Int.toNat_of_nonneg n0]; exact e
      have k1 := key m (by simpa [A3, hT] using hm)
      have k2 := key m' (by simpa [A3, hT] using hm')
      rw [hn, ha] at k1
      exact_mod_cast k1.trans k2.symm
  have htgt : (#tgt : ℝ) ≤ Wn * (ε₁ / 2 * M') := by
    have e1 : #tgt = ∑ a ∈ range Wn,
        #{n ∈ Icc 0 M' | V a ∧ 9 * M' ≤ 10 * n ∧ ¬ Rep W (Bf a).1 (Bf a).2 n} := by
      rw [card_filter, sum_product]
      refine sum_congr rfl fun a _ => ?_
      rw [card_filter]
    rw [e1]; push_cast
    have : ∀ a ∈ range Wn,
        (#{n ∈ Icc 0 M' | V a ∧ 9 * M' ≤ 10 * n ∧ ¬ Rep W (Bf a).1 (Bf a).2 n} : ℝ) ≤
          ε₁ / 2 * M' := by
      intro a ha
      by_cases hV : V a
      · have hle : M0f a ≤ M' := (le_sup ha).trans (by omega)
        have := hM0f a hV M' hle
        refine le_trans (le_of_eq ?_) this
        congr 2
        exact filter_congr (fun n _ => by simp [hV])
      · have : #{n ∈ Icc 0 M' | V a ∧ 9 * M' ≤ 10 * n ∧ ¬ Rep W (Bf a).1 (Bf a).2 n} = 0 := by
          rw [card_eq_zero, filter_eq_empty_iff]; intro n _ h; exact hV h.1
        rw [this]; push_cast; positivity
    calc _ ≤ ∑ a ∈ range Wn, ε₁ / 2 * (M' : ℝ) := sum_le_sum this
      _ = _ := by simp
  have hWM : (Wn : ℝ) * M' ≤ N := by
    have : Wn * M' ≤ N := by rw [hM'def]; exact Nat.mul_div_le N Wn
    exact_mod_cast this
  -- assemble
  have hT_le : (#T : ℝ) ≤ #A1 + #A2 + #A3 := by
    have := (card_le_card hsplit).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le A1 A2) _))
    exact_mod_cast this
  have hA3r : (#A3 : ℝ) ≤ #tgt := by exact_mod_cast hA3
  have hN2' : 6 * (Wn : ℝ) + 6 ≤ ε₁ * N := by
    rw [div_le_iff₀ hε₁] at hN2; linarith
  have hsq : ε₁ ^ 2 / 10 ≤ ε₁ / 20 := by nlinarith
  have hNn : (0 : ℝ) ≤ N := by positivity
  show (#T : ℝ) ≤ ε * N
  have : (Wn : ℝ) * (ε₁ / 2 * M') ≤ ε₁ / 2 * N := by nlinarith
  nlinarith

end LeanLab.Teravainen2016
