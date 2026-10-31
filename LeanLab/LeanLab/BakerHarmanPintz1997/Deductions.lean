/-
P0069 Baker, Harman, Pintz 1997, the deductions that need no analytic input.

* Theorem 1 from (1.2): `S(n) > 0` gives a Goldbach sum, `θ₁θ₂ ≤ 11/160`, and a longer interval
  `[x, x + x^θ]` is covered by intervals `[Y_j, Y_j + Y_j^{θ'}]`, `Y_{j+1} = Y_j + Y_j^{θ'}`. PROVED.
* Theorem 1 gives the lab's `ExceptionalSet.LogPowerSaving` and `DensityZero`. PROVED.
* Theorem 3 (III) from Theorem 3 (II) and Baker and Harman's lower bound, p. 5. PROVED.
* Theorem 3 (II) as printed, with no upper bound on `λ`, fails at `λ = 2`. PROVED, PRELIMINARY.
* Lemma 31, p. 46, for `ε` small in terms of `φ` and `j`. PROVED.
* The vector sieve inequality `S ≥ S₀,₁ + S₁,₀ - S₁,₁` of p. 2. PROVED.

AI-written Lean code, Claude, 2026-10-18, run 20261018T1603Z-12862.
Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.BakerHarmanPintz1997.Statements

namespace LeanLab.BakerHarmanPintz1997
open Real Filter Topology

attribute [local instance] Classical.propDecidable

/-! ### Counting on intervals -/

/-- Even `n ∈ [⌈a⌉, ⌊b⌋]` that are not a sum of two primes. -/
noncomputable def cnt (a b : ℝ) : ℕ :=
  ((Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter (fun n => Even n ∧ ¬ IsGoldbachSum n)).card

theorem EH_eq_cnt (x H : ℝ) : EH x H = cnt x (x + H) := rfl

theorem cnt_mono_right {a b b' : ℝ} (h : b ≤ b') : cnt a b ≤ cnt a b' :=
  Finset.card_le_card (Finset.filter_subset_filter _
    (Finset.Icc_subset_Icc le_rfl (Nat.floor_mono h)))

theorem cnt_split {a b c : ℝ} (hb : 0 ≤ b) : cnt a c ≤ cnt a b + cnt b c := by
  unfold cnt
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
  by_cases h : n ≤ ⌊b⌋₊
  · exact Or.inl ⟨⟨hn.1.1, h⟩, hn.2⟩
  · right
    push Not at h
    have : b < n := (Nat.floor_lt hb).mp h
    exact ⟨⟨Nat.ceil_le.mpr this.le, hn.1.2⟩, hn.2⟩

/-- The covering sequence `Y₀ = a`, `Y_{j+1} = Y_j + Y_j^θ`. -/
noncomputable def Ys (a θ : ℝ) : ℕ → ℝ
  | 0 => a
  | j + 1 => Ys a θ j + Ys a θ j ^ θ

theorem Ys_ge {a θ : ℝ} (ha : 0 ≤ a) : ∀ j, a ≤ Ys a θ j
  | 0 => le_rfl
  | j + 1 => by
    have := Ys_ge (θ := θ) ha j
    have : 0 ≤ Ys a θ j ^ θ := Real.rpow_nonneg (by linarith) θ
    show a ≤ Ys a θ j + Ys a θ j ^ θ
    linarith

theorem Ys_ge_add {a θ : ℝ} (ha : 1 ≤ a) (hθ : 0 ≤ θ) : ∀ j : ℕ, a + j ≤ Ys a θ j
  | 0 => by simp [Ys]
  | j + 1 => by
    have ih := Ys_ge_add ha hθ j
    have h1 : 1 ≤ Ys a θ j := le_trans ha (Ys_ge (by linarith) j)
    have : 1 ≤ Ys a θ j ^ θ := Real.one_le_rpow h1 hθ
    show a + ((j + 1 : ℕ) : ℝ) ≤ Ys a θ j + Ys a θ j ^ θ
    push_cast; linarith

theorem cnt_cover (a θ : ℝ) (ha : 0 ≤ a) : ∀ m : ℕ,
    cnt a (Ys a θ (m + 1)) ≤ ∑ j ∈ Finset.range (m + 1), EH (Ys a θ j) (Ys a θ j ^ θ)
  | 0 => by simp [EH_eq_cnt, Ys]
  | m + 1 => by
    have ih := cnt_cover a θ ha m
    have hs := cnt_split (a := a) (b := Ys a θ (m + 1)) (c := Ys a θ (m + 1 + 1))
      (le_trans ha (Ys_ge ha _))
    rw [Finset.sum_range_succ]
    have : cnt (Ys a θ (m + 1)) (Ys a θ (m + 1 + 1)) =
      EH (Ys a θ (m + 1)) (Ys a θ (m + 1) ^ θ) := rfl
    omega

/-- The covering bound: if `E(Y, Y^θ) ≤ Y^θ/log^A Y` for `Y ≥ X0`, then for `X0 ≤ a ≤ b`, `1 < a`,
the count on `[a, b]` is at most `(b - a + b^θ)/log^A a`. -/
theorem cnt_bound {θ A X0 : ℝ} (hθ : 0 ≤ θ) (hA : 0 < A)
    (hyp : ∀ Y : ℝ, X0 ≤ Y → (EH Y (Y ^ θ) : ℝ) ≤ Y ^ θ / Real.log Y ^ A)
    {a b : ℝ} (ha0 : X0 ≤ a) (ha1 : 1 < a) (hab : a ≤ b) :
    (cnt a b : ℝ) ≤ (b - a + b ^ θ) / Real.log a ^ A := by
  have ha : 0 ≤ a := by linarith
  have hla : 0 < Real.log a := Real.log_pos ha1
  have hlaA : 0 < Real.log a ^ A := Real.rpow_pos_of_pos hla A
  -- stopping index
  have hex : ∃ m : ℕ, b ≤ Ys a θ (m + 1) := by
    refine ⟨⌈b⌉₊, ?_⟩
    have h1 := Ys_ge_add (a := a) (θ := θ) ha1.le hθ (⌈b⌉₊ + 1)
    have h2 : b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
    push_cast at h1; linarith
  set m := Nat.find hex with hm
  have hmb : b ≤ Ys a θ (m + 1) := Nat.find_spec hex
  have hYm : Ys a θ m ≤ b := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0]; exact hab
    · obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have := Nat.find_min hex (show k < m by omega)
      push Not at this
      rw [hk]; exact this.le
  have hYm0 : 0 ≤ Ys a θ m := le_trans ha (Ys_ge ha m)
  have htop : Ys a θ (m + 1) ≤ b + b ^ θ := by
    show Ys a θ m + Ys a θ m ^ θ ≤ b + b ^ θ
    have := Real.rpow_le_rpow hYm0 hYm hθ
    linarith
  -- each piece
  have hpiece : ∀ j, (EH (Ys a θ j) (Ys a θ j ^ θ) : ℝ) ≤
      (Ys a θ (j + 1) - Ys a θ j) / Real.log a ^ A := by
    intro j
    have hYj : a ≤ Ys a θ j := Ys_ge ha j
    have h1 := hyp (Ys a θ j) (le_trans ha0 hYj)
    have hlog : Real.log a ≤ Real.log (Ys a θ j) := Real.log_le_log (by linarith) hYj
    have hpow : Real.log a ^ A ≤ Real.log (Ys a θ j) ^ A := Real.rpow_le_rpow hla.le hlog hA.le
    have hnum : 0 ≤ Ys a θ j ^ θ := Real.rpow_nonneg (by linarith) θ
    have : Ys a θ j ^ θ / Real.log (Ys a θ j) ^ A ≤ Ys a θ j ^ θ / Real.log a ^ A :=
      div_le_div_of_nonneg_left hnum hlaA hpow
    have e : Ys a θ (j + 1) - Ys a θ j = Ys a θ j ^ θ := by show Ys a θ j + _ - _ = _; ring
    rw [e]; linarith
  have hcov := cnt_cover a θ ha m
  have hsum : (∑ j ∈ Finset.range (m + 1), (EH (Ys a θ j) (Ys a θ j ^ θ) : ℝ)) ≤
      (Ys a θ (m + 1) - a) / Real.log a ^ A := by
    calc (∑ j ∈ Finset.range (m + 1), (EH (Ys a θ j) (Ys a θ j ^ θ) : ℝ))
        ≤ ∑ j ∈ Finset.range (m + 1), (Ys a θ (j + 1) - Ys a θ j) / Real.log a ^ A :=
          Finset.sum_le_sum fun j _ => hpiece j
      _ = (Ys a θ (m + 1) - a) / Real.log a ^ A := by
          rw [← Finset.sum_div, Finset.sum_range_sub (fun j => Ys a θ j)]; rfl
  have h1 : (cnt a b : ℝ) ≤ cnt a (Ys a θ (m + 1)) := by exact_mod_cast cnt_mono_right hmb
  have h2 : (cnt a (Ys a θ (m + 1)) : ℝ) ≤
      ∑ j ∈ Finset.range (m + 1), (EH (Ys a θ j) (Ys a θ j ^ θ) : ℝ) := by exact_mod_cast hcov
  have h3 : (Ys a θ (m + 1) - a) / Real.log a ^ A ≤ (b - a + b ^ θ) / Real.log a ^ A := by
    apply div_le_div_of_nonneg_right _ hlaA.le; linarith
  linarith

/-- `(x + x^θ)^{θ'} ≤ 2 x^θ` for `x ≥ 1`, `0 ≤ θ' ≤ 1`, `θ' ≤ θ`. -/
theorem sum_rpow_le {x θ θ' : ℝ} (hx : 1 ≤ x) (h0 : 0 ≤ θ') (h1 : θ' ≤ 1) (hle : θ' ≤ θ) :
    (x + x ^ θ) ^ θ' ≤ 2 * x ^ θ := by
  have hx0 : 0 ≤ x := by linarith
  have hθ0 : 0 ≤ θ := le_trans h0 hle
  set M := max x (x ^ θ) with hM
  have hM1 : 1 ≤ M := le_trans hx (le_max_left _ _)
  have hsum : x + x ^ θ ≤ 2 * M := by
    have := le_max_left x (x ^ θ); have := le_max_right x (x ^ θ); linarith
  have hpos : 0 ≤ x + x ^ θ := by positivity
  calc (x + x ^ θ) ^ θ' ≤ (2 * M) ^ θ' := Real.rpow_le_rpow hpos hsum h0
    _ = 2 ^ θ' * M ^ θ' := Real.mul_rpow (by norm_num) (by linarith)
    _ ≤ 2 * M ^ θ' := by
        have : (2 : ℝ) ^ θ' ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
        rw [Real.rpow_one] at this
        have : 0 ≤ M ^ θ' := Real.rpow_nonneg (by linarith) _
        nlinarith
    _ ≤ 2 * x ^ θ := by
        have : M ^ θ' ≤ x ^ θ := by
          rcases le_total x (x ^ θ) with h | h
          · rw [hM, max_eq_right h, ← Real.rpow_mul hx0]
            apply Real.rpow_le_rpow_of_exponent_le hx
            nlinarith
          · rw [hM, max_eq_left h]
            exact Real.rpow_le_rpow_of_exponent_le hx hle
        linarith

/-- **Monotonicity**: almost all in `[x, x+x^{θ'}]`, `0 < θ' ≤ 1`, gives almost all in
`[x, x+x^θ]` for every `θ ≥ θ'`. -/
theorem almostAllShort_mono {θ' θ : ℝ} (h0 : 0 < θ') (h1 : θ' ≤ 1) (hle : θ' ≤ θ)
    (h : AlmostAllShort θ') : AlmostAllShort θ := by
  intro A hA
  obtain ⟨X0, hX0⟩ := h (A + 1) (by linarith)
  have hyp : ∀ Y : ℝ, X0 ≤ Y → (EH Y (Y ^ θ') : ℝ) ≤ Y ^ θ' / Real.log Y ^ (A + 1) :=
    fun Y hY => (hX0 Y hY).le
  refine ⟨max X0 (Real.exp 4), fun x hx => ?_⟩
  have hxX0 : X0 ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp 4 ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : 1 < x := lt_of_lt_of_le (by have := Real.add_one_le_exp 4; linarith) hxe
  have hlog : 4 ≤ Real.log x := by
    rw [← Real.log_exp 4]; exact Real.log_le_log (Real.exp_pos 4) hxe
  have hlpos : 0 < Real.log x := by linarith
  have hθ0 : 0 ≤ θ := by linarith
  have hxθ : 0 < x ^ θ := Real.rpow_pos_of_pos (by linarith) θ
  have hb := cnt_bound h0.le (by linarith) hyp hxX0 hx1 (b := x + x ^ θ) (by linarith)
  rw [EH_eq_cnt]
  have hs := sum_rpow_le hx1.le h0.le h1 hle
  have hLA : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hlpos A
  have hsplit : Real.log x ^ (A + 1) = Real.log x ^ A * Real.log x := by
    rw [Real.rpow_add hlpos, Real.rpow_one]
  rw [hsplit] at hb
  have hnum : x + x ^ θ - x + (x + x ^ θ) ^ θ' ≤ 3 * x ^ θ := by linarith
  calc (cnt x (x + x ^ θ) : ℝ) ≤ (x + x ^ θ - x + (x + x ^ θ) ^ θ') /
        (Real.log x ^ A * Real.log x) := hb
    _ ≤ 3 * x ^ θ / (Real.log x ^ A * Real.log x) :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ < x ^ θ / Real.log x ^ A := by
        rw [div_lt_div_iff₀ (by positivity) hLA]
        have : 3 * x ^ θ * Real.log x ^ A < x ^ θ * (Real.log x ^ A * Real.log x) := by
          have : 3 * (x ^ θ * Real.log x ^ A) < Real.log x * (x ^ θ * Real.log x ^ A) := by
            apply mul_lt_mul_of_pos_right (by linarith) (by positivity)
          linarith
        linarith

/-! ### Theorem 1 from (1.2) -/

/-- `S(n) > 0` makes `N = 2n` a sum of two primes. -/
theorem goldbach_of_Scount_pos {ε x : ℝ} {N : ℕ} (h : 0 < Scount ε x N) : IsGoldbachSum N := by
  unfold Scount at h
  obtain ⟨k, hk⟩ := Finset.card_pos.mp h
  simp only [Finset.mem_filter] at hk
  obtain ⟨_, hkN, hkp, hmp, _, _⟩ := hk
  exact ⟨k, N - k, hkp, hmp, by omega⟩

/-- (1.2) gives almost all in `[x, x+x^{θ₁θ₂}]`. -/
theorem almostAll_of_prop12 {ε : ℝ} (h : Prop12 ε) : AlmostAllShort (theta1 ε * theta2) := by
  intro A hA
  obtain ⟨X0, hX0⟩ := h A hA
  refine ⟨X0, fun x hx => lt_of_le_of_lt ?_ (hX0 x hx)⟩
  have : EH x (x ^ (theta1 ε * theta2)) ≤ ((Finset.Icc ⌈x⌉₊ ⌊x + x ^ (theta1 ε * theta2)⌋₊).filter
      (fun N => Even N ∧ Scount ε x N = 0)).card := by
    apply Finset.card_le_card
    intro N hN
    simp only [Finset.mem_filter] at hN ⊢
    refine ⟨hN.1, hN.2.1, ?_⟩
    by_contra hne
    exact hN.2.2 (goldbach_of_Scount_pos (Nat.pos_of_ne_zero hne))
  exact_mod_cast this

/-- **Theorem 1 from (1.2)**, p. 2: "Obviously Theorem 1 follows from (1.2)". PROVED. -/
theorem theorem1_of_prop12 {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 20000) (h : Prop12 ε) :
    Theorem1 := by
  intro θ hθ
  have hle := theta12_le h0.le h1
  have hpos := theta12_pos (ε := ε) h0.le
  exact almostAllShort_mono hpos (by linarith) (by linarith) (almostAll_of_prop12 h)

/-- Theorem 1, CONDITIONAL ON the cited (1.2). -/
theorem theorem1_via_prop12 : Theorem1 := by
  obtain ⟨ε0, hε0, h⟩ := prop12
  set ε := min (ε0 / 2) (1 / 20000) with hε
  have hpos : 0 < ε := lt_min (by linarith) (by norm_num)
  exact theorem1_of_prop12 hpos (min_le_right _ _) (h ε hpos (lt_of_le_of_lt (min_le_left _ _)
    (by linarith)))

/-- Li's `θ > 7/81` and Ramachandra's `θ > 3/5` from Theorem 1. -/
theorem li_of_theorem1 (h : Theorem1) : ∀ θ : ℝ, 7 / 81 < θ → AlmostAllShort θ :=
  fun θ hθ => h θ (by linarith)

theorem ramachandra_of_li (h : ∀ θ : ℝ, 7 / 81 < θ → AlmostAllShort θ) :
    ∀ θ : ℝ, 3 / 5 < θ → AlmostAllShort θ := fun θ hθ => h θ (by linarith)

/-! ### The vector sieve inequality of p. 2, after Brüdern and Fouvry -/

/-- (1.3), (1.4) give `ρ(k)ρ(m) ≥ a₀(k)b₁(m) + a₁(k)b₀(m) - a₁(k)b₁(m)`, p. 2. -/
theorem bruedern_fouvry {r a0 a1 s b0 b1 : ℝ} (hr : 0 ≤ r) (ha0 : a0 ≤ r) (ha1 : r ≤ a1)
    (hs : 0 ≤ s) (hb0 : b0 ≤ s) (hb1 : s ≤ b1) : a0 * b1 + a1 * b0 - a1 * b1 ≤ r * s := by
  nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1),
    mul_nonneg (le_trans hr ha1) (sub_nonneg.mpr hb0),
    mul_nonneg (le_trans hs hb1) (sub_nonneg.mpr ha0)]

/-- Summed over `k + m = N`, `k ∈ I`, `m ∈ J`: `S ≥ S₀,₁ + S₁,₀ - S₁,₁`, p. 2. -/
theorem vector_sieve_sum (ε x : ℝ) (r a0 a1 b0 b1 : ℕ → ℝ) (hr : ∀ k, 0 ≤ r k)
    (ha0 : ∀ k ∈ Iset ε x, a0 k ≤ r k) (ha1 : ∀ k ∈ Iset ε x, r k ≤ a1 k)
    (hb0 : ∀ m ∈ Jset ε x, b0 m ≤ r m) (hb1 : ∀ m ∈ Jset ε x, r m ≤ b1 m) (N : ℕ) :
    convIJ ε x a0 b1 N + convIJ ε x a1 b0 N - convIJ ε x a1 b1 N ≤ convIJ ε x r r N := by
  unfold convIJ
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro k hk
  simp only [Finset.mem_filter] at hk
  exact bruedern_fouvry (hr k) (ha0 k hk.1) (ha1 k hk.1) (hr _) (hb0 _ hk.2.2) (hb1 _ hk.2.2)

/-! ### Theorem 1 gives the lab's `E(X) ≪ X log^{-A} X` -/

theorem E_le_cnt (N : ℕ) : LeanLab.ExceptionalSet.E N ≤ cnt 4 N := by
  unfold LeanLab.ExceptionalSet.E cnt
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  refine ⟨⟨?_, ?_⟩, hn.2⟩
  · have : ⌈(4 : ℝ)⌉₊ = 4 := by norm_num
    rw [this]; exact hn.1.1
  · rw [Nat.floor_natCast]; exact hn.1.2

theorem cnt_le_floor {a b : ℝ} (ha : 0 < a) : cnt a b ≤ ⌊b⌋₊ := by
  unfold cnt
  have : 0 < ⌈a⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast ha)
  refine (Finset.card_filter_le _ _).trans ?_
  simp only [Nat.card_Icc]; omega

/-- `√N ≤ (2A)^A N / log^A N` for `N ≥ 2`. -/
theorem sqrt_le_log {A : ℝ} (hA : 0 < A) {N : ℝ} (hN : 2 ≤ N) :
    Real.sqrt N ≤ (2 * A) ^ A * N / Real.log N ^ A := by
  have hN0 : 0 < N := by linarith
  have hl : 0 < Real.log N := Real.log_pos (by linarith)
  have hε : 0 < 1 / (2 * A) := by positivity
  have h1 : Real.log N ≤ N ^ (1 / (2 * A)) / (1 / (2 * A)) := Real.log_le_rpow_div hN0.le hε
  have h2 : Real.log N ≤ 2 * A * N ^ (1 / (2 * A)) := by
    rw [div_eq_mul_inv, inv_div, div_one] at h1; linarith
  have h3 : Real.log N ^ A ≤ (2 * A) ^ A * N ^ (1 / 2 : ℝ) := by
    calc Real.log N ^ A ≤ (2 * A * N ^ (1 / (2 * A))) ^ A := Real.rpow_le_rpow hl.le h2 hA.le
      _ = (2 * A) ^ A * (N ^ (1 / (2 * A))) ^ A := Real.mul_rpow (by positivity) (by positivity)
      _ = (2 * A) ^ A * N ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_mul hN0.le]; congr 2; field_simp
  have hlA : 0 < Real.log N ^ A := Real.rpow_pos_of_pos hl A
  rw [le_div_iff₀ hlA, Real.sqrt_eq_rpow]
  have hsq : N ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ) = N := by
    rw [← Real.rpow_add hN0]; norm_num
  have hpos : 0 ≤ N ^ (1 / 2 : ℝ) := Real.rpow_nonneg hN0.le _
  calc N ^ (1 / 2 : ℝ) * Real.log N ^ A ≤ N ^ (1 / 2 : ℝ) * ((2 * A) ^ A * N ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left h3 hpos
    _ = (2 * A) ^ A * (N ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ)) := by ring
    _ = (2 * A) ^ A * N := by rw [hsq]

/-- **Almost all in short intervals gives the lab's `LogPowerSaving`**, for any `0 < θ ≤ 1`. -/
theorem logPowerSaving_of_almostAll {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ 1) (h : AlmostAllShort θ) :
    LeanLab.ExceptionalSet.LogPowerSaving := by
  intro A hA
  obtain ⟨X0, hX0⟩ := h A hA
  have hyp : ∀ Y : ℝ, X0 ≤ Y → (EH Y (Y ^ θ) : ℝ) ≤ Y ^ θ / Real.log Y ^ A :=
    fun Y hY => (hX0 Y hY).le
  set N1 : ℝ := max (max X0 2 ^ 2) 4 with hN1
  have hN1_4 : 4 ≤ N1 := le_max_right _ _
  set K : ℝ := (2 * A) ^ A + 2 * 2 ^ A with hK
  refine ⟨max K (Real.log N1 ^ A), fun X hX => ?_⟩
  have hXr : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0' : (0 : ℝ) < X := by linarith
  have hl : 0 < Real.log X := Real.log_pos (by linarith)
  have hlA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hl A
  have hK0 : 0 ≤ K := by positivity
  rcases lt_or_ge (X : ℝ) N1 with hsmall | hbig
  · -- small `X`: `E X ≤ X ≤ log^A N1 · X / log^A X`
    have hE : (LeanLab.ExceptionalSet.E X : ℝ) ≤ X := by
      exact_mod_cast LeanLab.ExceptionalSet.E_le X
    have hlog : Real.log X ≤ Real.log N1 := Real.log_le_log hX0' hsmall.le
    have hpow : Real.log X ^ A ≤ Real.log N1 ^ A := Real.rpow_le_rpow hl.le hlog hA.le
    rw [le_div_iff₀ hlA]
    calc (LeanLab.ExceptionalSet.E X : ℝ) * Real.log X ^ A ≤ X * Real.log N1 ^ A :=
          mul_le_mul hE hpow hlA.le (by linarith)
      _ ≤ max K (Real.log N1 ^ A) * X := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
  · -- large `X`: split at `√X`
    have hsqrt0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
    have hsq : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX0'.le
    have hsX0 : X0 ≤ Real.sqrt X := by
      have h2 : max X0 2 ^ 2 ≤ (X : ℝ) := le_trans (le_max_left _ _) hbig
      have : max X0 2 ≤ Real.sqrt X := by
        rw [show max X0 2 = Real.sqrt (max X0 2 ^ 2) from
          (Real.sqrt_sq (by have := le_max_right X0 2; linarith)).symm]
        exact Real.sqrt_le_sqrt h2
      exact le_trans (le_max_left _ _) this
    have hs2 : 2 ≤ Real.sqrt X := by
      have : (2 : ℝ) = Real.sqrt 4 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [this]; exact Real.sqrt_le_sqrt (le_trans hN1_4 hbig)
    have hsX : Real.sqrt X ≤ X := by nlinarith
    have hb := cnt_bound h0.le hA hyp hsX0 (by linarith) (b := (X : ℝ)) hsX
    have hsplit := cnt_split (a := 4) (b := Real.sqrt X) (c := (X : ℝ)) hsqrt0
    have hfirst : (cnt 4 (Real.sqrt X) : ℝ) ≤ Real.sqrt X :=
      le_trans (by exact_mod_cast cnt_le_floor (by norm_num)) (Nat.floor_le hsqrt0)
    have hE : (LeanLab.ExceptionalSet.E X : ℝ) ≤ cnt 4 (Real.sqrt X) + cnt (Real.sqrt X) X := by
      have := E_le_cnt X
      have : LeanLab.ExceptionalSet.E X ≤ cnt 4 (Real.sqrt X) + cnt (Real.sqrt X) X :=
        le_trans this hsplit
      exact_mod_cast this
    have hlogs : Real.log (Real.sqrt X) = Real.log X / 2 := Real.log_sqrt hX0'.le
    have hXθ : (X : ℝ) ^ θ ≤ X := by
      have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ X) h1
      rwa [Real.rpow_one] at this
    have hsecond : (cnt (Real.sqrt X) X : ℝ) ≤ 2 * 2 ^ A * X / Real.log X ^ A := by
      refine le_trans hb ?_
      rw [hlogs, Real.div_rpow hl.le (by norm_num)]
      have hnum : (X : ℝ) - Real.sqrt X + (X : ℝ) ^ θ ≤ 2 * X := by linarith
      have h2A : (0 : ℝ) < 2 ^ A := by positivity
      rw [div_div_eq_mul_div]
      calc ((X : ℝ) - Real.sqrt X + (X : ℝ) ^ θ) * 2 ^ A / Real.log X ^ A
          ≤ (2 * X) * 2 ^ A / Real.log X ^ A := by
            apply div_le_div_of_nonneg_right _ hlA.le
            exact mul_le_mul_of_nonneg_right hnum h2A.le
        _ = 2 * 2 ^ A * X / Real.log X ^ A := by ring
    have hroot := sqrt_le_log hA hXr
    calc (LeanLab.ExceptionalSet.E X : ℝ) ≤ Real.sqrt X + 2 * 2 ^ A * X / Real.log X ^ A := by
          linarith
      _ ≤ (2 * A) ^ A * X / Real.log X ^ A + 2 * 2 ^ A * X / Real.log X ^ A := by linarith
      _ = K * X / Real.log X ^ A := by rw [hK]; ring
      _ ≤ max K (Real.log N1 ^ A) * X / Real.log X ^ A := by
          apply div_le_div_of_nonneg_right _ hlA.le
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)

/-- Theorem 1 gives the lab's `LogPowerSaving` and `DensityZero`. PROVED. -/
theorem lab_of_theorem1 (h : Theorem1) :
    LeanLab.ExceptionalSet.LogPowerSaving ∧ LeanLab.ExceptionalSet.DensityZero := by
  have h1 := logPowerSaving_of_almostAll (θ := 11 / 160) (by norm_num) (by norm_num)
    (h _ le_rfl)
  exact ⟨h1, LeanLab.ExceptionalSet.densityZero_of_logPowerSaving h1⟩

/-- The same, CONDITIONAL ON the cited Theorem 1. -/
theorem lab_via_theorem1 :
    LeanLab.ExceptionalSet.LogPowerSaving ∧ LeanLab.ExceptionalSet.DensityZero :=
  lab_of_theorem1 theorem1

/-! ### Theorem 3 (III) from Theorem 3 (II) and Baker and Harman, p. 5 -/

theorem primeCounting_eq_card (n : ℕ) :
    Nat.primeCounting n = ((Finset.range (n + 1)).filter Nat.Prime).card := by
  simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

/-- `π(a) < π(b)` gives a prime in `(a, b]`. -/
theorem exists_prime_of_primeCounting_lt {a b : ℕ} (h : Nat.primeCounting a < Nat.primeCounting b) :
    ∃ p, p.Prime ∧ a < p ∧ p ≤ b := by
  by_contra hno
  push Not at hno
  have : Nat.primeCounting b ≤ Nat.primeCounting a := by
    rw [primeCounting_eq_card, primeCounting_eq_card]
    apply Finset.card_le_card
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
    refine ⟨?_, hn.2⟩
    by_contra hna
    exact absurd (hno n hn.2 (by omega)) (by omega)
  omega

/-- `π(b) ≤ π(a) + #{primes in (a, b]}`. -/
theorem primeCounting_le_add (a b : ℕ) :
    Nat.primeCounting b ≤ Nat.primeCounting a + ((Finset.Ioc a b).filter Nat.Prime).card := by
  rw [primeCounting_eq_card, primeCounting_eq_card]
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ioc] at hn ⊢
  by_cases hna : n ≤ a
  · exact Or.inl ⟨by omega, hn.2⟩
  · exact Or.inr ⟨⟨by omega, by omega⟩, hn.2⟩

set_option maxHeartbeats 2000000 in
/-- **Theorem 3 (III) from Theorem 3 (II) and Baker and Harman's bound**, the argument of p. 5
after Montgomery and Vaughan. PROVED. -/
theorem theorem3III_of_at (h2 : Theorem3IIAt) (hBH : BakerHarmanLower) : Theorem3III := by
  obtain ⟨C2, hC2⟩ := h2 2 (by norm_num)
  obtain ⟨c, hc, X0, hX0⟩ := hBH
  have hmu : 0.535 * lam0 < mu := (mu_gt).2
  have hlam_pos : 0 < lam0 := by unfold lam0; norm_num
  have hlam_half : lam0 ≤ 1 / 2 := by unfold lam0; norm_num
  have hmu_pos : 0 < mu := by unfold mu; norm_num
  have hmu_le : mu ≤ 0.535 := by unfold mu; norm_num
  set K : ℝ := 2 * max C2 0 / (0.286225 * c) with hK
  have ev : ∀ᶠ x : ℝ in atTop, X0 ≤ x ∧ 1 ≤ x ∧ 6 ≤ x ^ mu ∧ 3 ≤ x ^ (mu - 0.535 * lam0) ∧
      3 ≤ x ^ (0.465 : ℝ) ∧ K < Real.log x := by
    refine (eventually_ge_atTop X0).and ((eventually_ge_atTop 1).and
      (((tendsto_rpow_atTop hmu_pos).eventually_ge_atTop 6).and
      (((tendsto_rpow_atTop (by linarith)).eventually_ge_atTop 3).and
      (((tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop 3).and
      (Real.tendsto_log_atTop.eventually_gt_atTop K)))))
  obtain ⟨X1, hX1⟩ := ev.exists_forall_of_atTop
  refine ⟨X1, fun x hx => ?_⟩
  obtain ⟨hxX0, hx1, hxmu, hxgap, hx465, hxK⟩ := hX1 x hx.le
  have hx0 : 0 < x := by linarith
  set y : ℝ := x ^ (0.535 : ℝ) with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow hx1 (by norm_num)
  have hyx : y * x ^ (0.465 : ℝ) = x := by
    rw [hy, ← Real.rpow_add hx0]; norm_num
  have hxy : 2 * y ≤ x - y := by nlinarith
  have hyle : y ≤ x := by linarith
  have hmuy : x ^ mu ≤ y := Real.rpow_le_rpow_of_exponent_le hx1 hmu_le
  -- the primes `p ∈ (x - y, x]`
  set P := (Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊).filter Nat.Prime with hP
  have hcardP : c * y / Real.log x ≤ (P.card : ℝ) := by
    have h1 := hX0 x hxX0 y le_rfl hyle
    have h2 := primeCounting_le_add ⌊x - y⌋₊ ⌊x⌋₊
    have h2' : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ Nat.primeCounting ⌊x - y⌋₊ + P.card := by
      exact_mod_cast h2
    linarith
  set T : ℕ := ⌊x + x ^ mu⌋₊ with hT
  have hT1 : (T : ℝ) ≤ x + x ^ mu := Nat.floor_le (by positivity)
  have hT2 : x + x ^ mu < T + 1 := Nat.lt_floor_add_one _
  -- facts on `p ∈ P`
  have hPfacts : ∀ p ∈ P, p.Prime ∧ x - y < p ∧ (p : ℝ) ≤ x ∧ p ≤ T := by
    intro p hp
    simp only [hP, Finset.mem_filter, Finset.mem_Ioc] at hp
    have hlo : x - y < p := by
      have := (Nat.floor_lt (by linarith)).mp hp.1.1; exact this
    have hhi : (p : ℝ) ≤ x := le_trans (by exact_mod_cast hp.1.2) (Nat.floor_le hx0.le)
    refine ⟨hp.2, hlo, hhi, ?_⟩
    have : (p : ℝ) ≤ T := by linarith [show (x : ℝ) + x ^ mu - 1 < T by linarith,
      show (1 : ℝ) ≤ x ^ mu by linarith]
    · have hh : p ≤ T := by
        have := (Nat.floor_le (by positivity) : (⌊x⌋₊ : ℝ) ≤ x)
        exact Nat.le_floor (by linarith)
      exact hh
  -- `h = T - p` lies in `[x^μ - 1, 2y]`
  have hhfacts : ∀ p ∈ P, x ^ mu - 1 < ((T - p : ℕ) : ℝ) ∧ ((T - p : ℕ) : ℝ) ≤ 2 * y := by
    intro p hp
    obtain ⟨_, hlo, hhi, hpT⟩ := hPfacts p hp
    rw [Nat.cast_sub hpT]
    constructor <;> linarith
  -- some `h` is good
  have hgood : ∃ p ∈ P, GapGood lam0 (T - p) := by
    by_contra hno
    push Not at hno
    have hsub : P.image (fun p => T - p) ⊆
        (Finset.Icc 1 ⌊2 * y⌋₊).filter (fun h => ¬ GapGood lam0 h) := by
      intro h hh
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
      obtain ⟨hlo, hhi⟩ := hhfacts p hp
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, Nat.le_floor hhi⟩, hno p hp⟩
      have : (1 : ℝ) ≤ ((T - p : ℕ) : ℝ) := by linarith
      exact_mod_cast this
    have hinj : Set.InjOn (fun p => T - p) P := by
      intro p hp p' hp' he
      have := (hPfacts p hp).2.2.2; have := (hPfacts p' hp').2.2.2
      simp only at he; omega
    have hcard : P.card ≤ gapExc lam0 (2 * y) := by
      unfold gapExc
      rw [← Finset.card_image_of_injOn hinj]
      exact Finset.card_le_card hsub
    have hexc := hC2 (2 * y) (by linarith)
    have hcardR : (P.card : ℝ) ≤ C2 * (2 * y) / Real.log (2 * y) ^ (2 : ℝ) :=
      le_trans (by exact_mod_cast hcard) hexc
    -- the contradiction
    have hlx : 0 < Real.log x := lt_of_le_of_lt (by positivity) hxK
    have hly : Real.log y = 0.535 * Real.log x := by rw [hy, Real.log_rpow hx0]
    have hl2y : 0.535 * Real.log x ≤ Real.log (2 * y) := by
      rw [← hly]; exact Real.log_le_log (by linarith) (by linarith)
    have hl2y_pos : 0 < Real.log (2 * y) := by linarith
    have hsq : (0.535 * Real.log x) ^ 2 ≤ Real.log (2 * y) ^ (2 : ℝ) := by
      rw [Real.rpow_two]; exact pow_le_pow_left₀ (by positivity) hl2y 2
    have hy0 : 0 < y := by linarith
    have hupper : C2 * (2 * y) / Real.log (2 * y) ^ (2 : ℝ) ≤
        max C2 0 * (2 * y) / (0.535 * Real.log x) ^ 2 := by
      calc C2 * (2 * y) / Real.log (2 * y) ^ (2 : ℝ) ≤ max C2 0 * (2 * y) /
            Real.log (2 * y) ^ (2 : ℝ) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
        _ ≤ max C2 0 * (2 * y) / (0.535 * Real.log x) ^ 2 := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
    have hlt : max C2 0 * (2 * y) / (0.535 * Real.log x) ^ 2 < c * y / Real.log x := by
      have hKx : 2 * max C2 0 < 0.286225 * c * Real.log x := by
        have := hxK; rw [hK, div_lt_iff₀ (by positivity)] at this; linarith
      rw [div_lt_div_iff₀ (by positivity) hlx]
      have e : max C2 0 * (2 * y) * Real.log x = (2 * max C2 0) * (y * Real.log x) := by ring
      have e2 : c * y * (0.535 * Real.log x) ^ 2 = (0.286225 * c * Real.log x) *
          (y * Real.log x) := by ring
      rw [e, e2]
      exact mul_lt_mul_of_pos_right hKx (by positivity)
    linarith
  obtain ⟨p, hp, hgp⟩ := hgood
  obtain ⟨hpp, hplo, hphi, hpT⟩ := hPfacts p hp
  obtain ⟨hhlo, hhhi⟩ := hhfacts p hp
  set h := T - p with hh
  have hhR : (h : ℝ) = T - p := by rw [hh, Nat.cast_sub hpT]
  have hh5 : (5 : ℝ) < h := by linarith
  have hlogh : 0 < Real.log h := Real.log_pos (by linarith)
  have hhpow0 : 0 < (h : ℝ) ^ lam0 := Real.rpow_pos_of_pos (by linarith) _
  -- a prime `p' ∈ (h - h^λ, h]`
  have hπ : Nat.primeCounting ⌊(h : ℝ) - (h : ℝ) ^ lam0⌋₊ < Nat.primeCounting h := by
    have := hgp; unfold GapGood at this
    have hpos : 0 < 0.05 * (h : ℝ) ^ lam0 / Real.log h := by positivity
    have : (Nat.primeCounting ⌊(h : ℝ) - (h : ℝ) ^ lam0⌋₊ : ℝ) < Nat.primeCounting h := by linarith
    exact_mod_cast this
  obtain ⟨p', hp', hp'lo, hp'hi⟩ := exists_prime_of_primeCounting_lt hπ
  have hp'lo' : (h : ℝ) - (h : ℝ) ^ lam0 < p' := by
    have := Nat.lt_floor_add_one ((h : ℝ) - (h : ℝ) ^ lam0)
    have : ((⌊(h : ℝ) - (h : ℝ) ^ lam0⌋₊ : ℕ) : ℝ) + 1 ≤ p' := by exact_mod_cast hp'lo
    linarith
  -- `h^λ ≤ x^μ - 1`
  have hhpow : (h : ℝ) ^ lam0 ≤ x ^ mu - 1 := by
    have h1 : (h : ℝ) ^ lam0 ≤ (2 * y) ^ lam0 := Real.rpow_le_rpow (by linarith) hhhi hlam_pos.le
    have h2 : (2 * y) ^ lam0 = 2 ^ lam0 * x ^ (0.535 * lam0) := by
      rw [Real.mul_rpow (by norm_num) (by linarith), hy, ← Real.rpow_mul hx0.le]
    have h3 : (2 : ℝ) ^ lam0 ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (show lam0 ≤ 1 by linarith)
      rwa [Real.rpow_one] at this
    have h4 : 1 ≤ x ^ (0.535 * lam0) := Real.one_le_rpow hx1 (by positivity)
    have h5 : x ^ mu = x ^ (mu - 0.535 * lam0) * x ^ (0.535 * lam0) := by
      rw [← Real.rpow_add hx0]; ring_nf
    have h6 : 0 ≤ x ^ (0.535 * lam0) := by linarith
    rw [h2] at h1
    have h7 : 2 ^ lam0 * x ^ (0.535 * lam0) ≤ 2 * x ^ (0.535 * lam0) :=
      mul_le_mul_of_nonneg_right h3 h6
    have h8 : 3 * x ^ (0.535 * lam0) ≤ x ^ (mu - 0.535 * lam0) * x ^ (0.535 * lam0) :=
      mul_le_mul_of_nonneg_right hxgap h6
    linarith
  -- `h - h^λ ≥ 2`, so `p'` is odd
  have hhalf : (h : ℝ) ^ lam0 ≤ (h : ℝ) / 2 := by
    have h1 : (h : ℝ) ^ lam0 ≤ (h : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hlam_half
    have h2 : (h : ℝ) ^ (1 / 2 : ℝ) * (h : ℝ) ^ (1 / 2 : ℝ) = h := by
      rw [← Real.rpow_add (by linarith)]; norm_num
    have h3 : 2 ≤ (h : ℝ) ^ (1 / 2 : ℝ) := by
      have : (2 : ℝ) = (4 : ℝ) ^ (1 / 2 : ℝ) := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
      calc (2 : ℝ) = (4 : ℝ) ^ (1 / 2 : ℝ) := this
        _ ≤ (h : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
    nlinarith
  have hp'3 : (2 : ℝ) < p' := by linarith
  have hp3 : (2 : ℝ) < p := by linarith
  have hp'odd : Odd p' := by
    rcases hp'.eq_two_or_odd' with h2 | h2
    · exfalso; rw [h2] at hp'3; norm_num at hp'3
    · exact h2
  have hpodd : Odd p := by
    rcases hpp.eq_two_or_odd' with h2 | h2
    · exfalso; rw [h2] at hp3; norm_num at hp3
    · exact h2
  refine ⟨p + p', ?_, ?_, hpodd.add_odd hp'odd, ⟨p, p', hpp, hp', rfl⟩⟩
  · push_cast; linarith
  · have : (p' : ℝ) ≤ h := by exact_mod_cast hp'hi
    push_cast; linarith

/-- The earlier form, from Theorem 3 (II) for every `λ ∈ [λ₀, 1]`. -/
theorem theorem3III_of (h2 : Theorem3II) (hBH : BakerHarmanLower) : Theorem3III :=
  theorem3III_of_at (theorem3IIAt_of h2) hBH

/-- Theorem 3 (III), CONDITIONAL ON the cited Theorem 3 (II) at `λ₀` and Baker-Harman. -/
theorem theorem3III : Theorem3III := theorem3III_of_at theorem3IIAt bakerHarman

/-! ### Theorem 3 (II) as printed fails for `λ = 2`, PRELIMINARY -/

theorem log_le_fortieth {h : ℝ} (hh : 6400 ≤ h) : Real.log h ≤ h / 40 := by
  have h0 : 0 < h := by linarith
  have h1 : Real.log h ≤ h ^ (1 / 2 : ℝ) / (1 / 2) := Real.log_le_rpow_div h0.le (by norm_num)
  have h2 : h ^ (1 / 2 : ℝ) * h ^ (1 / 2 : ℝ) = h := by
    rw [← Real.rpow_add h0]; norm_num
  have h3 : 80 ≤ h ^ (1 / 2 : ℝ) := by
    have : (80 : ℝ) = (6400 : ℝ) ^ (1 / 2 : ℝ) := by
      rw [show (6400 : ℝ) = 80 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [this]; exact Real.rpow_le_rpow (by norm_num) hh (by norm_num)
  nlinarith

theorem not_gapGood_two {h : ℕ} (hh : 6400 ≤ h) : ¬ GapGood 2 h := by
  unfold GapGood
  have hr : (6400 : ℝ) ≤ h := by exact_mod_cast hh
  have hfl : ⌊(h : ℝ) - (h : ℝ) ^ (2 : ℝ)⌋₊ = 0 := by
    apply Nat.floor_eq_zero.mpr
    rw [Real.rpow_two]; nlinarith
  rw [hfl]
  have hπ : (Nat.primeCounting h : ℝ) ≤ h + 1 := by
    have : Nat.primeCounting h ≤ h + 1 := by
      rw [primeCounting_eq_card]
      exact (Finset.card_filter_le _ _).trans (by simp)
    exact_mod_cast this
  have hl := log_le_fortieth hr
  have hlpos : 0 < Real.log h := Real.log_pos (by linarith)
  have : (h : ℝ) + 1 ≤ 0.05 * (h : ℝ) ^ (2 : ℝ) / Real.log h := by
    rw [le_div_iff₀ hlpos, Real.rpow_two]
    have := mul_le_mul_of_nonneg_left hl (by linarith : (0 : ℝ) ≤ (h : ℝ) + 1)
    nlinarith
  push Not
  simp only [Nat.primeCounting_zero, Nat.cast_zero, sub_zero]
  linarith

/-- **Theorem 3 (II) as printed is false**: with no upper bound on `λ`, at `λ = 2` every
`h ≥ 6400` is exceptional. PROVED; the intended range is surely `λ ≤ 1`. PRELIMINARY. -/
theorem not_theorem3II_literal : ¬ Theorem3II_literal := by
  intro H
  obtain ⟨C, hC⟩ := H 2 (by unfold lam0; norm_num) 1 one_pos
  set Y : ℝ := max 12801 (Real.exp (2 * max C 1)) with hY
  have hY1 : 12801 ≤ Y := le_max_left _ _
  have hYe : Real.exp (2 * max C 1) ≤ Y := le_max_right _ _
  have hYpos : 0 < Y := by linarith
  have hlog : 2 * max C 1 ≤ Real.log Y := by
    rw [← Real.log_exp (2 * max C 1)]; exact Real.log_le_log (Real.exp_pos _) hYe
  have hlpos : 0 < Real.log Y := by have := le_max_right C 1; linarith
  have hexc : (⌊Y⌋₊ + 1 - 6400 : ℕ) ≤ gapExc 2 Y := by
    unfold gapExc
    have hsub : Finset.Icc 6400 ⌊Y⌋₊ ⊆ (Finset.Icc 1 ⌊Y⌋₊).filter (fun h => ¬ GapGood 2 h) := by
      intro h hh
      rw [Finset.mem_Icc] at hh
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨le_trans (by norm_num) hh.1, hh.2⟩, not_gapGood_two hh.1⟩
    have hc : (Finset.Icc 6400 ⌊Y⌋₊).card = ⌊Y⌋₊ + 1 - 6400 := Nat.card_Icc _ _
    rw [← hc]; exact Finset.card_le_card hsub
  have hfl : Y - 1 < ⌊Y⌋₊ := by have := Nat.lt_floor_add_one Y; linarith
  have hfl6400 : 6400 ≤ ⌊Y⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hexcR : Y - 6400 ≤ (gapExc 2 Y : ℝ) := by
    have : ((⌊Y⌋₊ + 1 - 6400 : ℕ) : ℝ) ≤ gapExc 2 Y := by exact_mod_cast hexc
    rw [Nat.cast_sub (by omega)] at this
    push_cast at this; linarith
  have hb := hC Y (by linarith)
  rw [Real.rpow_one] at hb
  have : C * Y / Real.log Y ≤ Y / 2 := by
    rw [div_le_iff₀ hlpos]
    have h1 : C ≤ max C 1 := le_max_left _ _
    have : C * Y ≤ max C 1 * Y := mul_le_mul_of_nonneg_right h1 hYpos.le
    nlinarith
  linarith

/-! ### Lemma 31, p. 46 -/

/-- `1/a + 1/b ≥ 4/(a+b)`. -/
theorem inv_add_inv_ge {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 4 / (a + b) ≤ 1 / a + 1 / b := by
  rw [div_add_div _ _ ha.ne' hb.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (a - b)]

/-- **Lemma 31**, p. 46. Let `1/(2j) ≥ φ > 1/(2j+2)`, `j ≥ 4`. For `ε` small in terms of `φ, j`,
every `0 < λ ≤ φ/(1-φ) + 1/(2j-1+2ε)` satisfies `2/(2h+α) ≤ λ ≤ φ/(1-φ) + 1/(2h-1+2α)` for some
`α ∈ [ε, 1]` and integer `j ≤ h ≤ 1/λ + 1`. The paper's `ε` is an absolute constant chosen small;
the first step of the proof, `2/(2j+1) - 1/(2j+1+ε) ≤ φ/(1-φ)`, needs `ε` small in terms of
`φ/(1-φ) - 1/(2j+1) > 0`. PROVED. -/
theorem lemma31 (j : ℕ) (hj : 4 ≤ j) (φ : ℝ) (hφ1 : 1 / (2 * (j : ℝ) + 2) < φ)
    (hφ2 : φ ≤ 1 / (2 * (j : ℝ))) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → ∀ lam : ℝ, 0 < lam →
      lam ≤ φ / (1 - φ) + 1 / (2 * j - 1 + 2 * ε) →
      ∃ (h : ℕ) (α : ℝ), ε ≤ α ∧ α ≤ 1 ∧ j ≤ h ∧ (h : ℝ) ≤ 1 / lam + 1 ∧
        2 / (2 * h + α) ≤ lam ∧ lam ≤ φ / (1 - φ) + 1 / (2 * h - 1 + 2 * α) := by
  have hjr : (4 : ℝ) ≤ j := by exact_mod_cast hj
  have hφpos : 0 < φ := lt_trans (by positivity) hφ1
  have hφlt : φ < 1 := by
    have : 1 / (2 * (j : ℝ)) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have h1φ : 0 < 1 - φ := by linarith
  set r := φ / (1 - φ) with hr
  have hr_gt : 1 / (2 * (j : ℝ) + 1) < r := by
    rw [hr, div_lt_div_iff₀ (by linarith) h1φ]
    rw [div_lt_iff₀ (by linarith)] at hφ1
    linarith
  have hr_le : r ≤ 1 / (2 * (j : ℝ) - 1) := by
    rw [hr, div_le_div_iff₀ h1φ (by linarith)]
    rw [le_div_iff₀ (by linarith)] at hφ2
    linarith
  set δ := r - 1 / (2 * (j : ℝ) + 1) with hδ
  have hδpos : 0 < δ := by linarith
  refine ⟨min (1 / 2) (δ / 2), lt_min (by norm_num) (by linarith), ?_⟩
  intro ε hε hε0 lam hlam hlamle
  have hε12 : ε ≤ 1 / 2 := le_trans hε0 (min_le_left _ _)
  have hεδ : ε ≤ δ / 2 := le_trans hε0 (min_le_right _ _)
  -- `λ ≤ 2/(2j-1)`
  have hlam2 : lam ≤ 2 / (2 * (j : ℝ) - 1) := by
    have : 1 / (2 * (j : ℝ) - 1 + 2 * ε) ≤ 1 / (2 * (j : ℝ) - 1) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    have e : 2 / (2 * (j : ℝ) - 1) = 1 / (2 * (j : ℝ) - 1) + 1 / (2 * (j : ℝ) - 1) := by ring
    linarith
  set h : ℕ := ⌊1 / lam + 1 / 2⌋₊ with hh
  have hinv : 0 < 1 / lam := by positivity
  have hh1 : (h : ℝ) ≤ 1 / lam + 1 / 2 := Nat.floor_le (by linarith)
  have hh2 : 1 / lam + 1 / 2 < h + 1 := Nat.lt_floor_add_one _
  have hjh : j ≤ h := by
    apply Nat.le_floor
    have : (2 * (j : ℝ) - 1) / 2 ≤ 1 / lam := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2), div_mul_eq_mul_div, le_div_iff₀ hlam]
      rw [le_div_iff₀ (by linarith)] at hlam2
      linarith
    linarith
  have hhr : (j : ℝ) ≤ h := by exact_mod_cast hjh
  have hh4 : (4 : ℝ) ≤ h := le_trans hjr hhr
  -- `2h - 1 ≤ 2/λ < 2h + 1`
  have hA : 2 * (h : ℝ) - 1 ≤ 2 / lam := by
    have : 2 / lam = 2 * (1 / lam) := by ring
    linarith
  have hB : 2 / lam < 2 * (h : ℝ) + 1 := by
    have : 2 / lam = 2 * (1 / lam) := by ring
    linarith
  have hlam_le : lam ≤ 2 / (2 * (h : ℝ) - 1) := by
    rw [le_div_iff₀ (by linarith)]
    rw [le_div_iff₀ hlam] at hA; linarith
  refine ⟨h, ?_⟩
  by_cases hcase : 2 / (2 * (h : ℝ) + ε) < lam
  · -- Case 1, `α = ε`
    refine ⟨ε, le_rfl, by linarith, hjh, by linarith, hcase.le, ?_⟩
    rcases Nat.eq_or_lt_of_le hjh with heq | hlt
    · rw [← heq]; exact hlamle
    · have hjh1 : (j : ℝ) + 1 ≤ h := by exact_mod_cast hlt
      -- `2/(2h-1) - 1/(2h-1+2ε) ≤ 1/(2j+1) + 2ε ≤ r`
      have hpos : 0 < 2 * (h : ℝ) - 1 := by linarith
      have hpos' : 0 < 2 * (h : ℝ) - 1 + 2 * ε := by linarith
      have e : 2 / (2 * (h : ℝ) - 1) - 1 / (2 * (h : ℝ) - 1 + 2 * ε) =
          1 / (2 * (h : ℝ) - 1) + 2 * ε / ((2 * (h : ℝ) - 1) * (2 * (h : ℝ) - 1 + 2 * ε)) := by
        field_simp; ring
      have t1 : 1 / (2 * (h : ℝ) - 1) ≤ 1 / (2 * (j : ℝ) + 1) :=
        one_div_le_one_div_of_le (by linarith) (by linarith)
      have t2 : 2 * ε / ((2 * (h : ℝ) - 1) * (2 * (h : ℝ) - 1 + 2 * ε)) ≤ 2 * ε := by
        rw [div_le_iff₀ (by positivity)]
        have : 1 ≤ (2 * (h : ℝ) - 1) * (2 * (h : ℝ) - 1 + 2 * ε) := by nlinarith
        nlinarith
      linarith
  · -- Case 2, `λ = 2/(2h+α)`
    push Not at hcase
    set α := 2 / lam - 2 * h with hα
    have hαε : ε ≤ α := by
      have : 2 * (h : ℝ) + ε ≤ 2 / lam := by
        rw [le_div_iff₀ hlam]
        rw [le_div_iff₀ (by linarith)] at hcase; linarith
      linarith
    have hα1 : α ≤ 1 := by linarith
    have hden : 2 * (h : ℝ) + α = 2 / lam := by rw [hα]; ring
    have hlam_eq : 2 / (2 * (h : ℝ) + α) = lam := by
      rw [hden]; field_simp
    refine ⟨α, hαε, hα1, hjh, by linarith, hlam_eq.le, ?_⟩
    have hconv := inv_add_inv_ge (a := 2 * (h : ℝ) - 1 + 2 * α) (b := 2 * (h : ℝ) + 1)
      (by linarith) (by linarith)
    have e4 : 4 / (2 * (h : ℝ) - 1 + 2 * α + (2 * (h : ℝ) + 1)) = 2 / (2 * (h : ℝ) + α) := by
      rw [show 2 * (h : ℝ) - 1 + 2 * α + (2 * (h : ℝ) + 1) = 2 * (2 * (h : ℝ) + α) by ring]
      field_simp; ring
    have t1 : 1 / (2 * (h : ℝ) + 1) ≤ 1 / (2 * (j : ℝ) + 1) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    rw [e4, hlam_eq] at hconv
    linarith

end LeanLab.BakerHarmanPintz1997

open LeanLab.BakerHarmanPintz1997 in
section
#print axioms EH_eq_cnt
#print axioms cnt_mono_right
#print axioms cnt_split
#print axioms Ys_ge
#print axioms Ys_ge_add
#print axioms cnt_cover
#print axioms cnt_bound
#print axioms sum_rpow_le
#print axioms almostAllShort_mono
#print axioms goldbach_of_Scount_pos
#print axioms almostAll_of_prop12
#print axioms theorem1_of_prop12
#print axioms theorem1_via_prop12
#print axioms li_of_theorem1
#print axioms ramachandra_of_li
#print axioms bruedern_fouvry
#print axioms vector_sieve_sum
#print axioms E_le_cnt
#print axioms cnt_le_floor
#print axioms sqrt_le_log
#print axioms logPowerSaving_of_almostAll
#print axioms lab_of_theorem1
#print axioms lab_via_theorem1
#print axioms primeCounting_eq_card
#print axioms exists_prime_of_primeCounting_lt
#print axioms primeCounting_le_add
#print axioms theorem3III_of
#print axioms theorem3III_of_at
#print axioms theorem3III
#print axioms log_le_fortieth
#print axioms not_gapGood_two
#print axioms not_theorem3II_literal
#print axioms inv_add_inv_ge
#print axioms lemma31
end
