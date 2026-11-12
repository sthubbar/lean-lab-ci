/-
KaracubaWSplit: a split of the LEAF `KaracubaCore.leaf_W_bound`, the case `n ≥ n0` of
Karacuba's Theorem 1, A. A. Karacuba, Trudy Mat. Inst. Steklov 112 (1971), p. 245-248, along
the text, read from the page images of `papers/Karacuba1971-TrudyMIAN112.pdf`.

p. 245: `f(a + yz) = B_0 + B_1 yz + ... + B_n y^n z^n + R` with `B_s = f^{(s)}(a)/s!`,
`|R| ≤ |f^{(n+1)}(ξ)| P2^{2n+2}/(n+1)! ≤ P^{-1/n²}`, so by `|e^{iφ} - 1| ≤ |φ|`,
display (4): `W(a) = W_1(a) + 2π (P2+1)² θ_1 P^{-1/n²}`, with
`W_1(a) = Σ_{y,z=0}^{P2} e(B_0 + B_1 yz + ... + B_n y^n z^n)`.
Then p. 245-248, displays (5) to (8) and the simple computations, bound `W_1(a)`.

This file imports `KaracubaCore`, so it cannot discharge the sorry of
`KaracubaCore.leaf_W_bound` without an import cycle. It proves
`karWBound_of_split`, the exact statement of that leaf, from
* `karW_taylor`, PROVED here, display (4) in the sharp Lagrange form: here the factor `n + 1`
  that the cruder Mathlib remainder bound gives would NOT be harmless, since `n` is
  unbounded in this case;
* `leafW1_bound`, LEAF, the bound of `W_1(a)` of p. 245-248.

AI wrote the Lean code, Claude. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.KaracubaCore

namespace LeanLab.ExceptionalSet.U1539.KaracubaCore

open LeanLab.ExceptionalSet.U1539

/-- `W_1(a) = Σ_{y=0}^{M} Σ_{z=0}^{M} e(B_0 + B_1 yz + ... + B_n y^n z^n)`, p. 245, with
`B_s = B_s(a)`. -/
noncomputable def karW1 (f : ℝ → ℝ) (n M a : ℕ) : ℂ :=
  ∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
    eC (∑ s ∈ Finset.range (n + 1), karB f s a * ((y * z : ℕ) : ℝ) ^ s)

/-- PROVED. Taylor's formula with the Lagrange remainder, inside `[N, N+P]`, p. 245:
for `N ≤ a` and `a + y ≤ N + P`, `|f(a + y) - Σ_{s=0}^{n} B_s(a) y^s| ≤ P^{-c1(n+1)} y^{n+1}`. -/
theorem karTaylor_sharp {c0 c1 c2 c3 : ℝ} {N P n : ℕ} {f : ℝ → ℝ} {T : Finset ℕ}
    (hK : KarHyp c0 c1 c2 c3 N P n f T) (a y : ℕ) (ha : N ≤ a) (hay : a + y ≤ N + P) :
    |f ((a + y : ℕ) : ℝ) - ∑ s ∈ Finset.range (n + 1), karB f s a * (y : ℝ) ^ s| ≤
      (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) * (y : ℝ) ^ (n + 1) := by
  obtain ⟨⟨U, hUo, hIU, hfU⟩, hD, -⟩ := hK
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp [Finset.sum_range_succ', karB]
  have haR : (N : ℝ) ≤ a := by exact_mod_cast ha
  have hayR : (a : ℝ) + y ≤ N + P := by exact_mod_cast hay
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hlt : (a : ℝ) < a + y := by linarith
  have hsub : Set.Icc (a : ℝ) (a + y) ⊆ Set.Icc (N : ℝ) (N + P) :=
    Set.Icc_subset_Icc haR hayR
  have hsubU : Set.Icc (a : ℝ) (a + y) ⊆ U := hsub.trans hIU
  have hcd : ContDiffOn ℝ (n + 1 : ℕ) f (Set.Icc (a : ℝ) (a + y)) := hfU.mono hsubU
  have hat : ∀ z ∈ Set.Icc (a : ℝ) (a + y), ContDiffAt ℝ (n + 1 : ℕ) f z := fun z hz =>
    hfU.contDiffAt (hUo.mem_nhds (hsubU hz))
  have huniq : UniqueDiffOn ℝ (Set.Icc (a : ℝ) (a + y)) := uniqueDiffOn_Icc hlt
  have hx : ((a + y : ℕ) : ℝ) = (a : ℝ) + y := by push_cast; ring
  have hne : (a : ℝ) ≠ ((a + y : ℕ) : ℝ) := by rw [hx]; exact hlt.ne
  have hI : Set.uIcc (a : ℝ) ((a + y : ℕ) : ℝ) = Set.Icc (a : ℝ) (a + y) := by
    rw [hx, Set.uIcc_of_le hlt.le]
  have hIoo : Set.uIoo (a : ℝ) ((a + y : ℕ) : ℝ) = Set.Ioo (a : ℝ) (a + y) := by
    rw [hx, Set.uIoo_of_lt hlt]
  have hcdn : ContDiffOn ℝ n f (Set.Icc (a : ℝ) (a + y)) :=
    hcd.of_le (by exact_mod_cast Nat.le_succ n)
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin n f (Set.Icc (a : ℝ) (a + y)))
      (Set.Ioo (a : ℝ) (a + y)) :=
    (hcd.differentiableOn_iteratedDerivWithin (by exact_mod_cast Nat.lt_succ_self n) huniq).mono
      Set.Ioo_subset_Icc_self
  obtain ⟨x', hx', heq⟩ := taylor_mean_remainder_lagrange hne (by rw [hI]; exact hcdn)
    (by rw [hI, hIoo]; exact hdiff)
  rw [hI, hIoo] at *
  have hx'I : x' ∈ Set.Icc (a : ℝ) (a + y) := Set.Ioo_subset_Icc_self hx'
  have htay : taylorWithinEval f n (Set.Icc (a : ℝ) (a + y)) a ((a + y : ℕ) : ℝ) =
      ∑ s ∈ Finset.range (n + 1), karB f s a * (y : ℝ) ^ s := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hs' : s ≤ n + 1 := by rw [Finset.mem_range] at hs; omega
    have hleft : (a : ℝ) ∈ Set.Icc (a : ℝ) (a + y) := ⟨le_rfl, hlt.le⟩
    rw [iteratedDerivWithin_eq_iteratedDeriv huniq
      ((hat _ hleft).of_le (by exact_mod_cast hs')) hleft]
    simp only [karB, smul_eq_mul]
    push_cast
    ring
  rw [← htay, heq, iteratedDerivWithin_eq_iteratedDeriv huniq (hat x' hx'I) hx'I]
  have h1 := hD x' (hsub hx'I)
  have hyy : ((a + y : ℕ) : ℝ) - a = y := by rw [hx]; ring
  rw [hyy, mul_div_right_comm, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (y : ℝ) ^ (n + 1))]
  exact mul_le_mul_of_nonneg_right h1 (by positivity)

/-- `P^{-c1(n+1)} (P2²)^{n+1} ≤ P^{-1/n²}` for `P2 = [P^{0.5 c1 - 0.5/(n²(n+1))}]`, p. 245,
"из условий теоремы следует, что |R| ≤ P^{-1/n²}". -/
theorem karP2_taylor_err {c1 : ℝ} {n P : ℕ} (hn : 1 ≤ n) (hP : 0 < P) :
    (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) * (((karP2 c1 n P : ℕ) : ℝ) ^ 2) ^ (n + 1) ≤
      (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set e := c1 / 2 - 1 / (2 * ((n : ℝ) ^ 2 * (n + 1)))
  have hM : ((karP2 c1 n P : ℕ) : ℝ) ≤ (P : ℝ) ^ e :=
    Nat.floor_le (Real.rpow_nonneg hP0.le _)
  have hMp : (((karP2 c1 n P : ℕ) : ℝ) ^ 2) ^ (n + 1) ≤
      (P : ℝ) ^ (2 * e * ((n + 1 : ℕ) : ℝ)) := by
    rw [Real.rpow_mul hP0.le, Real.rpow_natCast, mul_comm 2 e, Real.rpow_mul hP0.le,
      Real.rpow_two]
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (Nat.cast_nonneg _) hM 2) _
  calc (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) * (((karP2 c1 n P : ℕ) : ℝ) ^ 2) ^ (n + 1)
      ≤ (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) * (P : ℝ) ^ (2 * e * ((n + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hMp (Real.rpow_nonneg hP0.le _)
    _ = (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) := by
        rw [← Real.rpow_add hP0]
        congr 1
        simp only [e]
        push_cast
        field_simp
        ring

/-- PROVED. Display (4) of p. 245: `|W(a) - W_1(a)| ≤ 2π (P2+1)² P^{-1/n²}` for `N ≤ a` and
`a + P2² ≤ N + P`, every point `a + yz` inside `[N, N+P]`. -/
theorem karW_taylor {c0 c1 c2 c3 : ℝ} {N P n : ℕ} {f : ℝ → ℝ} {T : Finset ℕ}
    (hK : KarHyp c0 c1 c2 c3 N P n f T) (hn : 1 ≤ n) (hP : 0 < P) (a : ℕ) (ha : N ≤ a)
    (hay : a + karP2 c1 n P ^ 2 ≤ N + P) :
    ‖karW f (karP2 c1 n P) a - karW1 f n (karP2 c1 n P) a‖ ≤
      2 * Real.pi * (((karP2 c1 n P : ℕ) : ℝ) + 1) ^ 2 * (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) := by
  set M := karP2 c1 n P with hMdef
  have herr := karP2_taylor_err (c1 := c1) hn hP
  rw [← hMdef] at herr
  have hP0 : (0 : ℝ) ≤ (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) := Real.rpow_nonneg (by positivity) _
  have hterm : ∀ y ∈ Finset.range (M + 1), ∀ z ∈ Finset.range (M + 1),
      ‖eC (f ((a + y * z : ℕ) : ℝ)) -
        eC (∑ s ∈ Finset.range (n + 1), karB f s a * ((y * z : ℕ) : ℝ) ^ s)‖ ≤
      2 * Real.pi * (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) := by
    intro y hy z hz
    rw [Finset.mem_range] at hy hz
    have hyz : y * z ≤ M ^ 2 := by
      rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
    have ht := karTaylor_sharp hK a (y * z) ha (by omega)
    refine (norm_eC_sub_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine ht.trans ((mul_le_mul_of_nonneg_left ?_ hP0).trans herr)
    have : ((y * z : ℕ) : ℝ) ≤ (M : ℝ) ^ 2 := by exact_mod_cast hyz
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) this _
  rw [karW, karW1, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hcard : ((M : ℝ) + 1) ^ 2 =
      ((Finset.range (M + 1)).card : ℝ) * ((Finset.range (M + 1)).card : ℝ) := by
    simp [sq]
  rw [hcard]
  calc ∑ y ∈ Finset.range (M + 1), ‖∑ z ∈ Finset.range (M + 1), eC (f ((a + y * z : ℕ) : ℝ)) -
          ∑ z ∈ Finset.range (M + 1),
            eC (∑ s ∈ Finset.range (n + 1), karB f s a * ((y * z : ℕ) : ℝ) ^ s)‖
      ≤ ∑ y ∈ Finset.range (M + 1), ((Finset.range (M + 1)).card : ℝ) *
          (2 * Real.pi * (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2))) := by
        refine Finset.sum_le_sum (fun y hy => ?_)
        rw [← Finset.sum_sub_distrib]
        refine (norm_sum_le _ _).trans ?_
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_le_sum (fun z hz => hterm y hy z hz)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- LEAF. The bound of `W_1(a)` in the case `n ≥ n0`, Karacuba p. 245-248, from Lemmas 1, 3
and 4: the choice of `l` with `n(n+1)(1-1/n)^l ≤ ρ(s_1+...+s_r) < n(n+1)(1-1/n)^{l-1}`,
`ρ = min(c1/3, c3, c4)`, and `k = nl + [n(n+1)/4 + 1]`; Lemma 4 a and b with the integrals
`J_k(λ)`, displays (5) and (6); `|Σ_{m=1}^{U} e(αm)| ≤ min(U, 1/(α))` and Lemma 3 on the sums
`𝔖_s`, `s = s_j`, display (7), with `Q_s = [B_s^{-1}]`; Lemma 1 and display (8),
`|W_1(a)| ≤ B_1 P2² P^{-ρ(s_1+...+s_r)/(8k²)}`; and the simple computations of p. 248 that turn
(8) into `A (P2+1)² P^{-γ/n²}`, using `P ≥ e^{cn²}` to absorb `B_1`, which holds a power of
`log P`. Only the `a` with `a + P2² ≤ N + P` are asked. -/
theorem leafW1_bound (h1 : KarLemma1) (h3 : KarLemma3) (h4 : KarLemma4) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ A γ cc : ℝ, 0 < A ∧ 0 < γ ∧ 0 < cc ∧ ∀ N P n : ℕ, 0 < P → 2 ≤ n →
        karN0 c1 c2 c4 ≤ n → Real.exp (cc * (n : ℝ) ^ 2) ≤ P →
        ∀ (f : ℝ → ℝ) (T : Finset ℕ), KarHyp c0 c1 c2 c3 N P n f T →
          ∀ a : ℕ, N ≤ a → a + karP2 c1 n P ^ 2 ≤ N + P →
            ‖karW1 f n (karP2 c1 n P) a‖ ≤
              A * ((karP2 c1 n P : ℝ) + 1) ^ 2 * (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2)) := by sorry

/-- PROVED from the LEAF `leafW1_bound` and the PROVED display (4), `karW_taylor`: the exact
statement of `KaracubaCore.leaf_W_bound`, p. 245-248. -/
theorem karWBound_of_split (h1 : KarLemma1) (h3 : KarLemma3) (h4 : KarLemma4) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 → KarWBound c0 c1 c2 c3 c4 := by
  intro c0 c1 c2 c3 c4 h0 h1' h2' h3' h4' h0' h1'' hc
  obtain ⟨A, γ, cc, hA, hγ, hcc, hL⟩ :=
    leafW1_bound h1 h3 h4 c0 c1 c2 c3 c4 h0 h1' h2' h3' h4' h0' h1'' hc
  refine ⟨A + 2 * Real.pi, min γ 1, cc, by positivity, lt_min hγ one_pos, hcc, ?_⟩
  intro N P n hP hn hn0 hPe f T hK a ha hay
  set M := karP2 c1 n P with hMdef
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have hW1 := hL N P n hP hn hn0 hPe f T hK a ha hay
  have hT := karW_taylor hK (by omega) hP a ha hay
  set E := (P : ℝ) ^ (-(min γ 1 / (n : ℝ) ^ 2)) with hE
  have hEγ : (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2)) ≤ E := by
    apply Real.rpow_le_rpow_of_exponent_le hP1
    rw [neg_le_neg_iff]
    exact div_le_div_of_nonneg_right (min_le_left _ _) hn2.le
  have hE1 : (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) ≤ E := by
    apply Real.rpow_le_rpow_of_exponent_le hP1
    rw [neg_le_neg_iff]
    exact div_le_div_of_nonneg_right (min_le_right _ _) hn2.le
  have hM0 : (0 : ℝ) ≤ ((M : ℝ) + 1) ^ 2 := by positivity
  calc ‖karW f M a‖ ≤ ‖karW1 f n M a‖ + ‖karW f M a - karW1 f n M a‖ := by
        have := norm_add_le (karW1 f n M a) (karW f M a - karW1 f n M a)
        rwa [add_sub_cancel] at this
    _ ≤ A * ((M : ℝ) + 1) ^ 2 * E + 2 * Real.pi * ((M : ℝ) + 1) ^ 2 * E := by
        refine add_le_add (hW1.trans ?_) (hT.trans ?_)
        · exact mul_le_mul_of_nonneg_left hEγ (by positivity)
        · exact mul_le_mul_of_nonneg_left hE1 (by positivity)
    _ = (A + 2 * Real.pi) * ((M : ℝ) + 1) ^ 2 * E := by ring

end LeanLab.ExceptionalSet.U1539.KaracubaCore
