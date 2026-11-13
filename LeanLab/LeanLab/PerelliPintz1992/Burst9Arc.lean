/-
P0070. A. Perelli and J. Pintz, On the exceptional set for the 2k-twin primes problem,
Compositio Math. 82, 1992, pp. 355 to 372, Section 5, p. 364, displays 23 to 27.

ROUTE BURST session 9, 2026-11-12. The bound for one arc `a'/q` of a dyadic block:
`qr_bound`, PROVED from the averaged clipped window sums, taken here as a hypothesis on the
modulus `q` and discharged by `clip_average_proved` in `Burst9Main.lean`. The steps, in the order of p. 364 with the end
averaging of the route of `Decomp1624.reduction27A`:

1. `R = R_{[a,b]} + R_D` for every `a`, `b` in the end blocks, averaged over `a` and `b`.
2. Display 13 for `R_{[a,b]}`: the character sum plus the terms with `(n, q) > 1`.
3. Minkowski over the characters, the Cauchy and Schwarz step of display 27.
4. Gallagher's lemma at the radius `1/(qQ)`, window `qQ/2`.
5. The averaged clipped window sums, `clip_average_proved`, which give `WA` of `Decomp1624`.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.PerelliPintz1992.Burst9Pieces

namespace LeanLab.PerelliPintz1992.Burst9
open Real ArithmeticFunction MeasureTheory Set Filter Topology
open LeanLab.PerelliPintz1992 LeanLab.PerelliPintz1992.Decomp97 LeanLab.PerelliPintz1992.Decomp1624
open LeanLab.PerelliPintz1992.Burst8P2

noncomputable section

/-- The pairs `(a, b)` of the two end blocks. -/
def Pset (N K0 : ℕ) : Finset (ℕ × ℕ) := Aset N K0 ×ˢ Bset N K0

/-- The removed part `[N, 2N] \ [a, b]`. -/
def Dset (N : ℕ) (p : ℕ × ℕ) : Finset ℕ := Finset.Icc N (2 * N) \ Finset.Icc p.1 p.2

theorem card_Pset (N K0 : ℕ) (hK : K0 ≤ 2 * N) : (Pset N K0).card = K0 * K0 := by
  unfold Pset Aset Bset
  rw [Finset.card_product, Nat.card_Ico, Nat.card_Ioc]
  congr 1 <;> omega

theorem Icc_sub_of_mem {N K0 : ℕ} {p : ℕ × ℕ} (hp : p ∈ Pset N K0) :
    Finset.Icc p.1 p.2 ⊆ Finset.Icc N (2 * N) := by
  unfold Pset Aset Bset at hp
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
  have ha' := Finset.mem_Ico.mp ha
  have hb' := Finset.mem_Ioc.mp hb
  intro n hn
  have := Finset.mem_Icc.mp hn
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

theorem card_Dset_le {N K0 : ℕ} (hK : 4 * K0 ≤ N) {p : ℕ × ℕ} (hp : p ∈ Pset N K0) :
    (Dset N p).card ≤ 2 * K0 := by
  unfold Dset
  rw [Finset.card_sdiff_of_subset (Icc_sub_of_mem hp), Nat.card_Icc, Nat.card_Icc]
  unfold Pset Aset Bset at hp
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
  have ha' := Finset.mem_Ico.mp ha
  have hb' := Finset.mem_Ioc.mp hb
  omega

theorem Dset_sub (N : ℕ) (p : ℕ × ℕ) : Dset N p ⊆ Finset.Icc N (2 * N) := Finset.sdiff_subset

/-- `R = R_{[a,b]} + R_D`. PROVED. -/
theorem R_split {N K0 : ℕ} {p : ℕ × ℕ} (hp : p ∈ Pset N K0) (q a : ℕ) (η : ℝ) :
    Decomp1519.R N q a η = Rx (Finset.Icc p.1 p.2) q a η + Rx (Dset N p) q a η := by
  calc Decomp1519.R N q a η = Rx (Finset.Icc N (2 * N)) q a η := rfl
    _ = Rx (Finset.Icc p.1 p.2 ∪ Dset N p) q a η := by
        rw [Dset, Finset.union_sdiff_of_subset (Icc_sub_of_mem hp)]
    _ = _ := Rx_union _ _ Finset.disjoint_sdiff q a η

theorem sqrt_add_le' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : √(x + y) ≤ √x + √y := by
  have h : x + y ≤ (√x + √y) ^ 2 := by
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  calc √(x + y) ≤ √((√x + √y) ^ 2) := Real.sqrt_le_sqrt h
    _ = √x + √y := Real.sqrt_sq (by positivity)

/-- The weight `Σ_χ |τ(χ)| WA(χ)` of display 27 at the modulus `q`. -/
def Om (N : ℕ) (q : ℕ+) : ℝ :=
  ∑ χ : DirichletCharacter ℂ (q : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ * WA N χ

theorem WA_sq (N : ℕ) {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) :
    WA N χ ^ 2 = (1 / (((q : ℝ) * Q N) ^ 2 * N)) *
      (windowMean N χ (gallagherWindow N q) +
        (1 / gallagherWindow N q) * ∫ u in Ioc (0 : ℝ) (gallagherWindow N q), windowMean N χ u) := by
  unfold WA
  rw [Real.sq_sqrt]
  have h1 : 0 ≤ windowMean N χ (gallagherWindow N q) :=
    setIntegral_nonneg measurableSet_Ioc fun x _ => sq_nonneg _
  have h2 : 0 ≤ ∫ u in Ioc (0 : ℝ) (gallagherWindow N q), windowMean N χ u :=
    setIntegral_nonneg measurableSet_Ioc fun u _ =>
      setIntegral_nonneg measurableSet_Ioc fun x _ => sq_nonneg _
  have h3 : 0 ≤ 1 / gallagherWindow N q := by
    unfold gallagherWindow Q; positivity
  have h4 : 0 ≤ 1 / (((q : ℝ) * Q N) ^ 2 * N) := by unfold Q; positivity
  positivity

set_option maxHeartbeats 1000000 in
/-- **One arc of a dyadic block, displays 13 and 23 to 27, p. 364**, from the end averaging,
display 13, Minkowski, Gallagher and the averaged clipped window sums `hclip`, the leaf
`clip_average_proved` at the modulus `q`. PROVED from `hclip`. -/
theorem qr_bound {N K0 : ℕ} (hK1 : 1 ≤ K0) (hK4 : 4 * K0 ≤ N) (q : ℕ+) (hQ : 0 < Q N)
    {r : ℕ} (hr : Nat.Coprime r q) (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hclip : ∀ χ : DirichletCharacter ℂ (q : ℕ),
      (1 / (K0 : ℝ) ^ 2) * ∑ a ∈ Aset N K0, ∑ b ∈ Bset N K0,
          (∫ x : ℝ, ‖Burst9G.cwinSum (Finset.Icc a b) (cf χ) (gallagherWindow N q) x‖ ^ 2) ≤
        C₁ * (windowMean N χ (gallagherWindow N q) + (1 / (K0 : ℝ)) *
          (∫ u in Ioc (0 : ℝ) (gallagherWindow N q), windowMean N χ u) +
            (Real.log (2 * N) + 1) ^ 2)) :
    (∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), ‖Decomp1519.R N q r η‖ ^ 2) ≤
      (2 / (K0 : ℝ) ^ 2) * ∑ p ∈ Pset N K0,
          (∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), ‖Rx (Dset N p) q r η‖ ^ 2) +
        16 * π ^ 2 * C₁ * max 1 (gallagherWindow N q / K0) * N * Om N q ^ 2 /
          (Nat.totient (q : ℕ) : ℝ) ^ 2 +
        16 * π ^ 2 * C₁ * (Real.log (2 * N) + 1) ^ 2 / Q N ^ 2 +
        8 * (1 / ((q : ℝ) * Q N)) *
          (∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => ¬ Nat.Coprime n q), Λ n) ^ 2 := by
  -- notation
  set δ : ℝ := 1 / ((q : ℝ) * Q N) with hδ
  set h : ℝ := gallagherWindow N q with hh
  set lam : ℝ := max 1 (h / K0) with hlam
  set E : ℝ := ∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => ¬ Nat.Coprime n q), Λ n with hE
  set P := Pset N K0 with hP
  set φq : ℝ := (Nat.totient (q : ℕ) : ℝ) with hφq
  set L2 : ℝ := Real.log (2 * N) + 1 with hL2
  have hq0 : (0 : ℝ) < (q : ℕ) := by exact_mod_cast q.pos
  have hδ0 : 0 < δ := by positivity
  have hh0 : 0 < h := by simp only [hh, gallagherWindow]; positivity
  have hK0r : (0 : ℝ) < K0 := by exact_mod_cast hK1
  have hφ0 : 0 < φq := by simp only [hφq]; exact_mod_cast Nat.totient_pos.mpr q.pos
  have hcard : (P.card : ℝ) = (K0 : ℝ) ^ 2 := by
    rw [hP, card_Pset N K0 (by omega)]; push_cast; ring
  have hlam1 : 1 ≤ lam := le_max_left _ _
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun n _ => vonMangoldt_nonneg
  -- continuity
  have cR : Continuous fun η => ‖Decomp1519.R N q r η‖ ^ 2 :=
    (continuous_Rx (Finset.Icc N (2 * N)) q r).norm.pow 2
  have cRx : ∀ I : Finset ℕ, Continuous fun η => ‖Rx I q r η‖ ^ 2 := fun I =>
    (continuous_Rx I q r).norm.pow 2
  have hδδ : -δ ≤ δ := by linarith
  have cRx2 : ∀ I : Finset ℕ, Continuous fun η => 2 * ‖Rx I q r η‖ ^ 2 := fun I =>
    continuous_const.mul (cRx I)
  -- Step 1: the end averaging
  have step1 : (∫ η in (-δ)..δ, ‖Decomp1519.R N q r η‖ ^ 2) ≤
      (2 / (K0 : ℝ) ^ 2) * ∑ p ∈ P, (∫ η in (-δ)..δ, ‖Rx (Finset.Icc p.1 p.2) q r η‖ ^ 2) +
        (2 / (K0 : ℝ) ^ 2) * ∑ p ∈ P, (∫ η in (-δ)..δ, ‖Rx (Dset N p) q r η‖ ^ 2) := by
    have hp : ∀ p ∈ P, (∫ η in (-δ)..δ, ‖Decomp1519.R N q r η‖ ^ 2) ≤
        2 * (∫ η in (-δ)..δ, ‖Rx (Finset.Icc p.1 p.2) q r η‖ ^ 2) +
          2 * ∫ η in (-δ)..δ, ‖Rx (Dset N p) q r η‖ ^ 2 := by
      intro p hpP
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add ((cRx2 _).intervalIntegrable _ _)
          ((cRx2 _).intervalIntegrable _ _)]
      refine intervalIntegral.integral_mono_on hδδ (cR.intervalIntegrable _ _)
        (((cRx2 _).add (cRx2 _)).intervalIntegrable _ _) ?_
      intro η _
      rw [R_split hpP]
      exact norm_add_sq_le _ _
    have hsum := Finset.sum_le_sum hp
    rw [Finset.sum_const, nsmul_eq_mul, hcard, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum] at hsum
    have hK2 : (0 : ℝ) < (K0 : ℝ) ^ 2 := by positivity
    rw [show (2 / (K0 : ℝ) ^ 2) * ∑ p ∈ P, (∫ η in (-δ)..δ, ‖Rx (Finset.Icc p.1 p.2) q r η‖ ^ 2) +
        (2 / (K0 : ℝ) ^ 2) * ∑ p ∈ P, (∫ η in (-δ)..δ, ‖Rx (Dset N p) q r η‖ ^ 2) =
        (2 * ∑ p ∈ P, (∫ η in (-δ)..δ, ‖Rx (Finset.Icc p.1 p.2) q r η‖ ^ 2) +
          2 * ∑ p ∈ P, (∫ η in (-δ)..δ, ‖Rx (Dset N p) q r η‖ ^ 2)) / (K0 : ℝ) ^ 2 by ring]
    rw [le_div_iff₀ hK2]
    linarith
  -- Step 2: display 13 and the terms with `(n, q) > 1`
  set w : DirichletCharacter ℂ (q : ℕ) → ℂ := fun χ =>
    χ⁻¹ (r : ZMod (q : ℕ)) * gaussSum χ ZMod.stdAddChar with hw
  set f : DirichletCharacter ℂ (q : ℕ) → ℕ × ℕ → ℝ → ℂ := fun χ p η =>
    Psx (Finset.Icc p.1 p.2) χ⁻¹ η with hf
  have cf' : ∀ χ p, Continuous (f χ p) := fun χ p => continuous_Psx _ _
  have hmain_eq : ∀ p η, Rx (Finset.Icc p.1 p.2) q r η =
      (1 / (φq : ℂ)) * (∑ χ, w χ * f χ p η) + Ex (Finset.Icc p.1 p.2) q r η := by
    intro p η
    rw [display13 _ q hr η, hφq]
    push_cast
    rfl
  have step2 : ∀ p ∈ P, (∫ η in (-δ)..δ, ‖Rx (Finset.Icc p.1 p.2) q r η‖ ^ 2) ≤
      2 * (1 / φq ^ 2) * (∫ η in (-δ)..δ, ‖∑ χ, w χ * f χ p η‖ ^ 2) + 2 * (2 * δ * E ^ 2) := by
    intro p hpP
    have cM : Continuous fun η => ‖∑ χ, w χ * f χ p η‖ ^ 2 :=
      (continuous_finsetSum _ fun χ _ => continuous_const.mul (cf' χ p)).norm.pow 2
    have cM2 : Continuous fun η => 2 * (1 / φq ^ 2) * ‖∑ χ, w χ * f χ p η‖ ^ 2 :=
      continuous_const.mul cM
    have hpt : ∀ η, ‖Rx (Finset.Icc p.1 p.2) q r η‖ ^ 2 ≤
        2 * (1 / φq ^ 2) * ‖∑ χ, w χ * f χ p η‖ ^ 2 + 2 * E ^ 2 := by
      intro η
      rw [hmain_eq]
      refine (norm_add_sq_le _ _).trans ?_
      have h1 : ‖(1 / (φq : ℂ)) * (∑ χ, w χ * f χ p η)‖ ^ 2 =
          (1 / φq ^ 2) * ‖∑ χ, w χ * f χ p η‖ ^ 2 := by
        rw [norm_mul, mul_pow, norm_div, norm_one, Complex.norm_real,
          Real.norm_of_nonneg hφ0.le]
        ring
      have h2 : ‖Ex (Finset.Icc p.1 p.2) q r η‖ ^ 2 ≤ E ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_Ex_le N _ (Icc_sub_of_mem hpP) q r η) 2
      rw [h1]; linarith
    calc (∫ η in (-δ)..δ, ‖Rx (Finset.Icc p.1 p.2) q r η‖ ^ 2)
        ≤ ∫ η in (-δ)..δ, (2 * (1 / φq ^ 2) * ‖∑ χ, w χ * f χ p η‖ ^ 2 + 2 * E ^ 2) :=
          intervalIntegral.integral_mono_on hδδ ((cRx _).intervalIntegrable _ _)
            ((cM2.add continuous_const).intervalIntegrable _ _) fun η _ => hpt η
      _ = 2 * (1 / φq ^ 2) * (∫ η in (-δ)..δ, ‖∑ χ, w χ * f χ p η‖ ^ 2) + 2 * (2 * δ * E ^ 2) := by
          rw [intervalIntegral.integral_add (cM2.intervalIntegrable _ _)
            intervalIntegrable_const, intervalIntegral.integral_const_mul,
            intervalIntegral.integral_const]
          simp only [smul_eq_mul]; ring
  -- Step 3: Minkowski
  set Iχ : DirichletCharacter ℂ (q : ℕ) → ℝ := fun χ =>
    ∑ p ∈ P, ∫ η in (-δ)..δ, ‖f χ p η‖ ^ 2 with hIχ
  have step3 : (∑ p ∈ P, ∫ η in (-δ)..δ, ‖∑ χ, w χ * f χ p η‖ ^ 2) ≤
      (∑ χ, ‖w χ‖ * √(Iχ χ)) ^ 2 :=
    minkowski_fin P Finset.univ w f δ hδ0.le cf'
  -- Step 4: Gallagher and the leaf, for each character
  have step4 : ∀ χ : DirichletCharacter ℂ (q : ℕ), Iχ χ ≤
      2 * π ^ 2 * (K0 : ℝ) ^ 2 * C₁ * (lam * N * WA N χ⁻¹ ^ 2 + δ ^ 2 * L2 ^ 2) := by
    intro χ
    have hg : ∀ p ∈ P, (∫ η in (-δ)..δ, ‖f χ p η‖ ^ 2) ≤ 2 * π ^ 2 * δ ^ 2 *
        ∫ x : ℝ, ‖Burst9G.cwinSum (Finset.Icc p.1 p.2) (cf χ⁻¹) h x‖ ^ 2 :=
      fun p _ => gallagher_Psx N _ q χ⁻¹ hQ
    have hs := Finset.sum_le_sum hg
    rw [← Finset.mul_sum] at hs
    have hc := hclip χ⁻¹
    rw [show (∑ a ∈ Aset N K0, ∑ b ∈ Bset N K0,
        ∫ x : ℝ, ‖Burst9G.cwinSum (Finset.Icc a b) (cf χ⁻¹) (gallagherWindow N q) x‖ ^ 2) =
        ∑ p ∈ P, ∫ x : ℝ, ‖Burst9G.cwinSum (Finset.Icc p.1 p.2) (cf χ⁻¹) h x‖ ^ 2 by
      rw [hP, Pset, Finset.sum_product]] at hc
    set G := ∑ p ∈ P, ∫ x : ℝ, ‖Burst9G.cwinSum (Finset.Icc p.1 p.2) (cf χ⁻¹) h x‖ ^ 2
    have hK2 : (0 : ℝ) < (K0 : ℝ) ^ 2 := by positivity
    have hG : G ≤ (K0 : ℝ) ^ 2 * (C₁ * (windowMean N χ⁻¹ h + (1 / (K0 : ℝ)) *
        (∫ u in Ioc (0 : ℝ) h, windowMean N χ⁻¹ u) + L2 ^ 2)) := by
      have := mul_le_mul_of_nonneg_left hc hK2.le
      rwa [← mul_assoc, mul_one_div_cancel hK2.ne', one_mul] at this
    -- the window terms in `WA`
    have hw1 : 0 ≤ windowMean N χ⁻¹ h :=
      setIntegral_nonneg measurableSet_Ioc fun x _ => sq_nonneg _
    have hw2 : 0 ≤ ∫ u in Ioc (0 : ℝ) h, windowMean N χ⁻¹ u :=
      setIntegral_nonneg measurableSet_Ioc fun u _ =>
        setIntegral_nonneg measurableSet_Ioc fun x _ => sq_nonneg _
    have hlamK : 1 / (K0 : ℝ) ≤ lam * (1 / h) := by
      have : h / K0 ≤ lam := le_max_right _ _
      rw [div_le_iff₀ hK0r] at this
      rw [div_le_iff₀ hK0r, mul_one_div, div_mul_eq_mul_div, le_div_iff₀ hh0]
      nlinarith
    have hWA : windowMean N χ⁻¹ h + (1 / (K0 : ℝ)) * (∫ u in Ioc (0 : ℝ) h, windowMean N χ⁻¹ u) ≤
        lam * ((((q : ℕ) : ℝ) * Q N) ^ 2 * N * WA N χ⁻¹ ^ 2) := by
      rw [WA_sq]
      have hN0 : (0 : ℝ) < N := by
        have : (4 : ℝ) * K0 ≤ N := by exact_mod_cast hK4
        linarith
      have e1 : (((q : ℕ) : ℝ) * Q N) ^ 2 * N * ((1 / ((((q : ℕ) : ℝ) * Q N) ^ 2 * N)) *
          (windowMean N χ⁻¹ (gallagherWindow N q) + (1 / gallagherWindow N q) *
            ∫ u in Ioc (0 : ℝ) (gallagherWindow N q), windowMean N χ⁻¹ u)) =
          windowMean N χ⁻¹ h + (1 / h) * ∫ u in Ioc (0 : ℝ) h, windowMean N χ⁻¹ u := by
        rw [← hh]; field_simp
      rw [e1]
      have := mul_le_mul_of_nonneg_right hlamK hw2
      nlinarith
    have hδq : δ ^ 2 * ((((q : ℕ) : ℝ) * Q N) ^ 2) = 1 := by
      rw [hδ]; field_simp
    calc Iχ χ = ∑ p ∈ P, ∫ η in (-δ)..δ, ‖f χ p η‖ ^ 2 := rfl
      _ ≤ 2 * π ^ 2 * δ ^ 2 * G := hs
      _ ≤ 2 * π ^ 2 * δ ^ 2 * ((K0 : ℝ) ^ 2 * (C₁ * (lam * ((((q : ℕ) : ℝ) * Q N) ^ 2 * N *
            WA N χ⁻¹ ^ 2) + L2 ^ 2))) := by
          refine mul_le_mul_of_nonneg_left (hG.trans ?_) (by positivity)
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (by linarith) hC₁.le
      _ = 2 * π ^ 2 * (K0 : ℝ) ^ 2 * C₁ * (lam * N * WA N χ⁻¹ ^ 2 *
            (δ ^ 2 * ((((q : ℕ) : ℝ) * Q N) ^ 2)) + δ ^ 2 * L2 ^ 2) := by ring
      _ = _ := by rw [hδq, mul_one]
  -- Step 5: the square roots
  set c0 : ℝ := √(2 * π ^ 2 * (K0 : ℝ) ^ 2 * C₁) with hc0
  have hc00 : 0 ≤ c0 := Real.sqrt_nonneg _
  have hWA0 : ∀ χ : DirichletCharacter ℂ (q : ℕ), 0 ≤ WA N χ := fun χ => Real.sqrt_nonneg _
  have hL20 : 0 ≤ L2 := by
    simp only [hL2]
    have : 0 ≤ Real.log (2 * N) := by
      have : (4 : ℝ) * K0 ≤ N := by exact_mod_cast hK4
      have : (1 : ℝ) ≤ K0 := by exact_mod_cast hK1
      exact Real.log_nonneg (by linarith)
    linarith
  have step5 : ∀ χ : DirichletCharacter ℂ (q : ℕ),
      √(Iχ χ) ≤ c0 * (√(lam * N) * WA N χ⁻¹ + δ * L2) := by
    intro χ
    have h1 := Real.sqrt_le_sqrt (step4 χ)
    refine h1.trans ?_
    rw [Real.sqrt_mul (by positivity), hc0]
    refine mul_le_mul_of_nonneg_left ?_ hc00
    refine (sqrt_add_le' (by positivity) (by positivity)).trans (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (hWA0 _), Real.sqrt_mul (sq_nonneg _) _,
      Real.sqrt_sq hδ0.le, Real.sqrt_sq hL20]
  -- Step 6: reindex the characters
  have hnormw : ∀ χ : DirichletCharacter ℂ (q : ℕ), ‖w χ‖ ≤ ‖gaussSum χ ZMod.stdAddChar‖ := by
    intro χ
    simp only [hw, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)
  have hreidx : (∑ χ : DirichletCharacter ℂ (q : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ * WA N χ⁻¹) =
      Om N q := by
    unfold Om
    refine Fintype.sum_equiv (Equiv.inv _) _ _ fun χ => ?_
    simp only [Equiv.inv_apply]
    rw [← norm_gaussSum_inv χ]
  set T : ℝ := ∑ χ : DirichletCharacter ℂ (q : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun χ _ => norm_nonneg _
  have hTle : T ≤ φq * (q : ℕ) := by
    calc T ≤ ∑ _χ : DirichletCharacter ℂ (q : ℕ), (((q : ℕ) : ℕ) : ℝ) :=
          Finset.sum_le_sum fun χ _ => norm_gaussSum_le χ
      _ = φq * (q : ℕ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_chars]
  have hOm0 : 0 ≤ Om N q := Finset.sum_nonneg fun χ _ => mul_nonneg (norm_nonneg _) (hWA0 _)
  have step6 : (∑ χ, ‖w χ‖ * √(Iχ χ)) ≤ c0 * (√(lam * N) * Om N q + δ * L2 * T) := by
    calc (∑ χ, ‖w χ‖ * √(Iχ χ))
        ≤ ∑ χ : DirichletCharacter ℂ (q : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ *
            (c0 * (√(lam * N) * WA N χ⁻¹ + δ * L2)) :=
          Finset.sum_le_sum fun χ _ => mul_le_mul (hnormw χ) (step5 χ) (Real.sqrt_nonneg _)
            (norm_nonneg _)
      _ = c0 * (√(lam * N) * Om N q + δ * L2 * T) := by
          have e : ∀ χ : DirichletCharacter ℂ (q : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ *
              (c0 * (√(lam * N) * WA N χ⁻¹ + δ * L2)) =
              c0 * √(lam * N) * (‖gaussSum χ ZMod.stdAddChar‖ * WA N χ⁻¹) +
                c0 * (δ * L2) * ‖gaussSum χ ZMod.stdAddChar‖ := fun χ => by ring
          rw [Finset.sum_congr rfl fun χ _ => e χ, Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum, hreidx, ← hT]
          ring
  -- Step 7: assemble
  have hsq : (∑ χ, ‖w χ‖ * √(Iχ χ)) ^ 2 ≤
      2 * c0 ^ 2 * (lam * N * Om N q ^ 2 + δ ^ 2 * L2 ^ 2 * T ^ 2) := by
    have h0 : 0 ≤ ∑ χ, ‖w χ‖ * √(Iχ χ) :=
      Finset.sum_nonneg fun χ _ => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
    have h1 := pow_le_pow_left₀ h0 step6 2
    refine h1.trans ?_
    have hs : √(lam * N) ^ 2 = lam * N := Real.sq_sqrt (by positivity)
    set X := √(lam * N) * Om N q with hX
    set Z := δ * L2 * T with hZ
    have hXY : (X + Z) ^ 2 ≤ 2 * (X ^ 2 + Z ^ 2) := by linarith [sq_nonneg (X - Z)]
    have hX2 : X ^ 2 = lam * N * Om N q ^ 2 := by rw [hX, mul_pow, hs]
    have hZ2 : Z ^ 2 = δ ^ 2 * L2 ^ 2 * T ^ 2 := by rw [hZ]; ring
    calc (c0 * (X + Z)) ^ 2 = c0 ^ 2 * (X + Z) ^ 2 := by ring
      _ ≤ c0 ^ 2 * (2 * (X ^ 2 + Z ^ 2)) := mul_le_mul_of_nonneg_left hXY (sq_nonneg _)
      _ = _ := by rw [hX2, hZ2]; ring
  have hc0sq : c0 ^ 2 = 2 * π ^ 2 * (K0 : ℝ) ^ 2 * C₁ := Real.sq_sqrt (by positivity)
  have hTq : T ^ 2 / φq ^ 2 ≤ ((q : ℕ) : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have := pow_le_pow_left₀ hT0 hTle 2
    nlinarith
  have hδQ : δ ^ 2 * ((q : ℕ) : ℝ) ^ 2 = 1 / Q N ^ 2 := by
    rw [hδ]; field_simp
  -- the main part
  have hmainsum : (2 / (K0 : ℝ) ^ 2) * ∑ p ∈ P, (∫ η in (-δ)..δ, ‖Rx (Finset.Icc p.1 p.2) q r η‖ ^ 2) ≤
      16 * π ^ 2 * C₁ * lam * N * Om N q ^ 2 / φq ^ 2 +
        16 * π ^ 2 * C₁ * L2 ^ 2 / Q N ^ 2 + 8 * δ * E ^ 2 := by
    have hs := Finset.sum_le_sum step2
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard, ← Finset.mul_sum] at hs
    have hK2 : (0 : ℝ) < (K0 : ℝ) ^ 2 := by positivity
    have hA : (2 / (K0 : ℝ) ^ 2) * (2 * (1 / φq ^ 2) *
        ∑ p ∈ P, ∫ η in (-δ)..δ, ‖∑ χ, w χ * f χ p η‖ ^ 2) ≤
        16 * π ^ 2 * C₁ * lam * N * Om N q ^ 2 / φq ^ 2 +
          16 * π ^ 2 * C₁ * L2 ^ 2 / Q N ^ 2 := by
      have h1 := step3.trans hsq
      rw [hc0sq] at h1
      have e1 : (2 / (K0 : ℝ) ^ 2) * (2 * (1 / φq ^ 2) * (2 * (2 * π ^ 2 * (K0 : ℝ) ^ 2 * C₁) *
          (lam * N * Om N q ^ 2 + δ ^ 2 * L2 ^ 2 * T ^ 2))) =
          16 * π ^ 2 * C₁ * lam * N * Om N q ^ 2 / φq ^ 2 +
            16 * π ^ 2 * C₁ * L2 ^ 2 * (T ^ 2 / φq ^ 2) * δ ^ 2 := by
        field_simp
        ring
      have h2 : (2 / (K0 : ℝ) ^ 2) * (2 * (1 / φq ^ 2) *
          ∑ p ∈ P, ∫ η in (-δ)..δ, ‖∑ χ, w χ * f χ p η‖ ^ 2) ≤
          (2 / (K0 : ℝ) ^ 2) * (2 * (1 / φq ^ 2) * (2 * (2 * π ^ 2 * (K0 : ℝ) ^ 2 * C₁) *
            (lam * N * Om N q ^ 2 + δ ^ 2 * L2 ^ 2 * T ^ 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      rw [e1] at h2
      refine h2.trans ?_
      have h3 : 16 * π ^ 2 * C₁ * L2 ^ 2 * (T ^ 2 / φq ^ 2) * δ ^ 2 ≤
          16 * π ^ 2 * C₁ * L2 ^ 2 / Q N ^ 2 := by
        have : 0 ≤ 16 * π ^ 2 * C₁ * L2 ^ 2 * δ ^ 2 := by positivity
        calc 16 * π ^ 2 * C₁ * L2 ^ 2 * (T ^ 2 / φq ^ 2) * δ ^ 2
            = 16 * π ^ 2 * C₁ * L2 ^ 2 * δ ^ 2 * (T ^ 2 / φq ^ 2) := by ring
          _ ≤ 16 * π ^ 2 * C₁ * L2 ^ 2 * δ ^ 2 * ((q : ℕ) : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hTq this
          _ = 16 * π ^ 2 * C₁ * L2 ^ 2 * (δ ^ 2 * ((q : ℕ) : ℝ) ^ 2) := by ring
          _ = _ := by rw [hδQ]; ring
      linarith
    have hB : (2 / (K0 : ℝ) ^ 2) * ((K0 : ℝ) ^ 2 * (2 * (2 * δ * E ^ 2))) = 8 * δ * E ^ 2 := by
      field_simp; ring
    calc (2 / (K0 : ℝ) ^ 2) * ∑ p ∈ P, (∫ η in (-δ)..δ, ‖Rx (Finset.Icc p.1 p.2) q r η‖ ^ 2)
        ≤ (2 / (K0 : ℝ) ^ 2) * (2 * (1 / φq ^ 2) *
            ∑ p ∈ P, (∫ η in (-δ)..δ, ‖∑ χ, w χ * f χ p η‖ ^ 2) +
              (K0 : ℝ) ^ 2 * (2 * (2 * δ * E ^ 2))) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = (2 / (K0 : ℝ) ^ 2) * (2 * (1 / φq ^ 2) *
            ∑ p ∈ P, (∫ η in (-δ)..δ, ‖∑ χ, w χ * f χ p η‖ ^ 2)) +
            (2 / (K0 : ℝ) ^ 2) * ((K0 : ℝ) ^ 2 * (2 * (2 * δ * E ^ 2))) := by ring
      _ ≤ _ := by rw [hB]; linarith
  have := step1.trans (add_le_add hmainsum le_rfl)
  linarith

#print axioms card_Pset
#print axioms card_Dset_le
#print axioms R_split
#print axioms WA_sq
#print axioms qr_bound

end
end LeanLab.PerelliPintz1992.Burst9
