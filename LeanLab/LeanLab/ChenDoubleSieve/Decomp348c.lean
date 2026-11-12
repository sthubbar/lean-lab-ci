import LeanLab.ChenDoubleSieve.Decomp348a

/-!
Supply split for the F5 lower bound in Wu 2004.
Source: https://arxiv.org/pdf/0705.1652, page 39 equation 10.5.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set MeasureTheory
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task348
open Task275
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- The actual ordered coprime prime pair domain for Upsilon 5. -/
def lowerPairs5 (N : ℕ) : Finset (ℕ × ℕ) :=
  Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧ (p : ℝ) < (N : ℝ) ^ kappa2 ∧
      (N : ℝ) ^ kappa2 ≤ q ∧
      (q : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / p)

/-- The finite prime sum before passage to the F5 double integral. -/
def lowerSum5 (f : ℝ → ℝ) (B : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ lowerPairs5 N,
    f (lowerLevel B N (q.1 * q.2)) / (Nat.totient (q.1 * q.2) : ℝ)

/-- The unscaled double integral in equation 10.5 for F5. -/
def lowerIntegral5 (f : ℝ → ℝ) : ℝ :=
  ∫ t in kappa1..kappa2,
    (∫ u in kappa2..(1 / 2 - 2 * kappa1 - t), f ((1 / 2 - t - u) / kappa1) / u) / t

/-- The finite level main term for Upsilon 5. -/
def main5 (f : ℝ → ℝ) (B : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) / log N * lowerDensity N * lowerSum5 f B N

private lemma E2p_unfold (x : ℝ) :
    LeanLab.BS2022GRH.PortedMertens.Mertens.E₂p x = (∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun p => Nat.Prime p), (1:ℝ)/(p:ℝ))
      - Real.log (Real.log x) - LeanLab.BS2022GRH.PortedMertens.Mertens.M := rfl

private lemma E2p_tendsto_zero_rpow (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ => LeanLab.BS2022GRH.PortedMertens.Mertens.E₂p ((N:ℝ)^a)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun N : ℕ => (N:ℝ)^a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun N : ℕ => Real.log ((N:ℝ)^a)) atTop atTop :=
    tendsto_log_atTop.comp hpow
  have hC : Tendsto (fun N : ℕ => |log 4 + 6 + LeanLab.BS2022GRH.PortedMertens.Mertens.E₁| / Real.log ((N:ℝ)^a)) atTop (𝓝 0) :=
    hlog.const_div_atTop _
  refine tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (f := fun N : ℕ => ‖LeanLab.BS2022GRH.PortedMertens.Mertens.E₂p ((N:ℝ)^a)‖) ?_ ?_ hC)
  · filter_upwards with N
    exact norm_nonneg _
  · filter_upwards [hpow.eventually (eventually_ge_atTop 2)] with N hN
    have hlogpos : 0 < Real.log ((N:ℝ)^a) := Real.log_pos (by linarith)
    calc ‖LeanLab.BS2022GRH.PortedMertens.Mertens.E₂p ((N:ℝ)^a)‖ = |LeanLab.BS2022GRH.PortedMertens.Mertens.E₂p ((N:ℝ)^a)| := Real.norm_eq_abs _
      _ ≤ (log 4 + 6 + LeanLab.BS2022GRH.PortedMertens.Mertens.E₁) / Real.log ((N:ℝ)^a) := LeanLab.BS2022GRH.PortedMertens.Mertens.E₂p.abs_le hN
      _ ≤ |log 4 + 6 + LeanLab.BS2022GRH.PortedMertens.Mertens.E₁| / Real.log ((N:ℝ)^a) := by
          gcongr
          exact le_abs_self _

/-- Mertens' second theorem normalized at the scale `N ^ a`. -/
private lemma mertens_norm_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ =>
        (∑ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^a⌋₊).filter (fun p => Nat.Prime p), (1:ℝ)/(p:ℝ))
          - Real.log (Real.log ((N:ℝ)^a))) atTop (𝓝 LeanLab.BS2022GRH.PortedMertens.Mertens.M) := by
  have h := (E2p_tendsto_zero_rpow a ha).add (tendsto_const_nhds (x := LeanLab.BS2022GRH.PortedMertens.Mertens.M))
  have h' : Tendsto (fun N : ℕ => LeanLab.BS2022GRH.PortedMertens.Mertens.E₂p ((N:ℝ)^a) + LeanLab.BS2022GRH.PortedMertens.Mertens.M) atTop (𝓝 LeanLab.BS2022GRH.PortedMertens.Mertens.M) := by
    simpa using h
  refine h'.congr' ?_
  filter_upwards with N
  rw [E2p_unfold]
  ring


private lemma interval_sum_eq (a b : ℝ) (ha : 0 < a) (hab : a < b) {N : ℕ} (hN : 1 ≤ N) :
    (∑ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p ∧ (N:ℝ)^a < (p:ℝ)),
        ((p:ℝ))⁻¹)
      = (∑ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p), ((p:ℝ))⁻¹)
        - (∑ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^a⌋₊).filter (fun p => Nat.Prime p), ((p:ℝ))⁻¹) := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hmono : (N:ℝ)^a ≤ (N:ℝ)^b := Real.rpow_le_rpow_of_exponent_le hN1 (le_of_lt hab)
  have hKaKb : ⌊(N:ℝ)^a⌋₊ ≤ ⌊(N:ℝ)^b⌋₊ := Nat.floor_mono hmono
  set S := (Finset.Ioc 0 ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p) with hS
  set T := S.filter (fun p : ℕ => (N:ℝ)^a < (p:ℝ)) with hT
  have hTS : T ⊆ S := Finset.filter_subset _ _
  have hI : (∑ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^b⌋₊).filter
        (fun p => Nat.Prime p ∧ (N:ℝ)^a < (p:ℝ)), ((p:ℝ))⁻¹) = ∑ p ∈ T, ((p:ℝ))⁻¹ := by
    rw [hT, hS, Finset.filter_filter]
  rw [hI]
  have hs := Finset.sum_sdiff (s₁ := T) (s₂ := S) (f := fun p : ℕ => ((p:ℝ))⁻¹) hTS
  have hst : ∑ p ∈ S \ T, ((p:ℝ))⁻¹
      = ∑ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^a⌋₊).filter (fun p => Nat.Prime p), ((p:ℝ))⁻¹ := by
    congr 1
    rw [hT, hS]
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨⟨h0, hKb⟩, hP⟩, hT'⟩
      refine ⟨⟨h0, ?_⟩, hP⟩
      refine Nat.le_floor ?_
      by_contra hcon
      push_neg at hcon
      exact hT' ⟨⟨⟨h0, hKb⟩, hP⟩, hcon⟩
    · rintro ⟨⟨h0, hKa⟩, hP⟩
      refine ⟨⟨⟨h0, le_trans hKa hKaKb⟩, hP⟩, ?_⟩
      intro hcon
      obtain ⟨-, hlt⟩ := hcon
      have h1 : (p:ℝ) ≤ ⌊(N:ℝ)^a⌋₊ := by exact_mod_cast hKa
      have h2 : (⌊(N:ℝ)^a⌋₊ : ℝ) ≤ (N:ℝ)^a := Nat.floor_le (le_of_lt (rpow_pos_of_pos hNpos a))
      linarith
  rw [hst] at hs
  linarith [hs]


private lemma mertens_interval (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) :
    Tendsto (fun N : ℕ => ∑ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^b⌋₊).filter
        (fun p => Nat.Prime p ∧ (N:ℝ)^a < (p:ℝ)), ((p:ℝ))⁻¹) atTop
      (𝓝 (Real.log b - Real.log a)) := by
  have hzero : Tendsto (fun N : ℕ =>
      ((∑ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p), ((p:ℝ))⁻¹)
        - Real.log (Real.log ((N:ℝ)^b)))
      - ((∑ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^a⌋₊).filter (fun p => Nat.Prime p), ((p:ℝ))⁻¹)
        - Real.log (Real.log ((N:ℝ)^a)))) atTop (𝓝 0) := by
    have h := (mertens_norm_tendsto b hb).sub (mertens_norm_tendsto a ha)
    simpa using h
  have hlogeq : ∀ᶠ N : ℕ in atTop,
      Real.log (Real.log ((N:ℝ)^b)) - Real.log (Real.log ((N:ℝ)^a))
        = Real.log b - Real.log a := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hlogpos : 0 < Real.log (N:ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    rw [Real.log_rpow hNpos, Real.log_rpow hNpos,
      Real.log_mul hb.ne' hlogpos.ne', Real.log_mul ha.ne' hlogpos.ne']
    ring
  have hconst : Tendsto (fun N : ℕ =>
      Real.log (Real.log ((N:ℝ)^b)) - Real.log (Real.log ((N:ℝ)^a))) atTop
      (𝓝 (Real.log b - Real.log a)) := by
    refine (tendsto_const_nhds (x := Real.log b - Real.log a)).congr' ?_
    filter_upwards [hlogeq] with N hN
    exact hN.symm
  have hsum : Tendsto (fun N : ℕ =>
      (((∑ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p), ((p:ℝ))⁻¹)
        - Real.log (Real.log ((N:ℝ)^b)))
      - ((∑ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^a⌋₊).filter (fun p => Nat.Prime p), ((p:ℝ))⁻¹)
        - Real.log (Real.log ((N:ℝ)^a))))
      + (Real.log (Real.log ((N:ℝ)^b)) - Real.log (Real.log ((N:ℝ)^a)))) atTop
      (𝓝 (Real.log b - Real.log a)) := by
    have h := hzero.add hconst
    simpa using h
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [interval_sum_eq a b ha hab hN]
  ring



/-- The substitution `1 / p ↦ 1 / (p - 1)` does not change the interval limit. -/
private lemma mertens_interval_totient (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) :
    Tendsto (fun N : ℕ => ∑ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^b⌋₊).filter
        (fun p => Nat.Prime p ∧ (N:ℝ)^a < (p:ℝ)), (((p:ℝ) - 1))⁻¹) atTop
      (𝓝 (Real.log b - Real.log a)) := by
  have hsum := mertens_interval a b ha hb hab
  set hL : ℝ := Real.log b - Real.log a with hLdef
  -- eventual boundedness of the `1 / p` interval sum
  have hbound : ∀ᶠ N : ℕ in atTop,
      (∑ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^b⌋₊).filter
        (fun p => Nat.Prime p ∧ (N:ℝ)^a < (p:ℝ)), ((p:ℝ))⁻¹) ≤ hL + 1 :=
    (hsum.eventually (eventually_lt_nhds (lt_add_one hL))).mono fun N h => le_of_lt h
  -- the pointwise difference is dominated by `2 / (p * N ^ a)`
  have hdiff : Tendsto (fun N : ℕ =>
      ∑ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^b⌋₊).filter
        (fun p => Nat.Prime p ∧ (N:ℝ)^a < (p:ℝ)),
        ((((p:ℝ) - 1))⁻¹ - ((p:ℝ))⁻¹)) atTop (𝓝 0) := by
    have hpow : Tendsto (fun N : ℕ => (N:ℝ)^a) atTop atTop :=
      (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
    have hsmall : Tendsto (fun N : ℕ => (2 / (N:ℝ)^a) * (hL + 1)) atTop (𝓝 0) := by
      have hinv : Tendsto (fun N : ℕ => ((N:ℝ)^a)⁻¹) atTop (𝓝 0) :=
        hpow.inv_tendsto_atTop
      have h2 : Tendsto (fun N : ℕ => 2 * ((N:ℝ)^a)⁻¹ * (hL + 1)) atTop (𝓝 0) := by
        simpa using ((hinv.const_mul 2).mul_const (hL + 1))
      refine h2.congr' ?_
      filter_upwards with N
      field_simp
    refine squeeze_zero' (g := fun N : ℕ => (2 / (N:ℝ)^a) * (hL + 1)) ?_ ?_ hsmall
    · filter_upwards [eventually_ge_atTop 1, hpow.eventually (eventually_ge_atTop 2)]
        with N hN1 hN2
      refine sum_nonneg ?_
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
      obtain ⟨⟨h0, -⟩, hP, hgt⟩ := hp
      have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hP.two_le
      have : (0:ℝ) < ((p:ℝ) - 1) := by linarith
      have hle : ((p:ℝ))⁻¹ ≤ (((p:ℝ) - 1))⁻¹ :=
        inv_anti₀ (by linarith) (by linarith)
      linarith
    · filter_upwards [hbound, eventually_ge_atTop 1,
        hpow.eventually (eventually_ge_atTop 2)] with N hbN hN1 hN2
      have hNpos : (0:ℝ) < (N:ℝ)^a := lt_of_lt_of_le (by norm_num) hN2
      have hNpos' : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
      have hpt : ∀ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^b⌋₊).filter
          (fun p => Nat.Prime p ∧ (N:ℝ)^a < (p:ℝ)),
          (((p:ℝ) - 1))⁻¹ - ((p:ℝ))⁻¹ ≤ 2 / ((p:ℝ) * (N:ℝ)^a) := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
        obtain ⟨⟨h0, -⟩, hP, hgt⟩ := hp
        have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hP.two_le
        have hpN : (N:ℝ)^a < (p:ℝ) := hgt
        have h1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
        have h2 : (0:ℝ) < (p:ℝ) := by linarith
        have heq : (((p:ℝ) - 1))⁻¹ - ((p:ℝ))⁻¹ = 1 / ((p:ℝ) * ((p:ℝ) - 1)) := by
          field_simp
          ring
        rw [heq]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hpN, hNpos]
      calc ∑ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^b⌋₊).filter
            (fun p => Nat.Prime p ∧ (N:ℝ)^a < (p:ℝ)),
            ((((p:ℝ) - 1))⁻¹ - ((p:ℝ))⁻¹)
          ≤ ∑ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^b⌋₊).filter
            (fun p => Nat.Prime p ∧ (N:ℝ)^a < (p:ℝ)), 2 / ((p:ℝ) * (N:ℝ)^a) :=
            sum_le_sum hpt
        _ = (2 / (N:ℝ)^a) * ∑ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^b⌋₊).filter
            (fun p => Nat.Prime p ∧ (N:ℝ)^a < (p:ℝ)), ((p:ℝ))⁻¹ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p _
            field_simp
        _ ≤ (2 / (N:ℝ)^a) * (hL + 1) := by
            apply mul_le_mul_of_nonneg_left hbN
            positivity
  have hcombine : Tendsto (fun N : ℕ =>
      ((∑ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^b⌋₊).filter
        (fun p => Nat.Prime p ∧ (N:ℝ)^a < (p:ℝ)), ((p:ℝ))⁻¹)
      + ∑ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^b⌋₊).filter
        (fun p => Nat.Prime p ∧ (N:ℝ)^a < (p:ℝ)),
        ((((p:ℝ) - 1))⁻¹ - ((p:ℝ))⁻¹))) atTop (𝓝 (hL + 0)) :=
    hsum.add hdiff
  have hfin : Tendsto (fun N : ℕ =>
      ((∑ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^b⌋₊).filter
        (fun p => Nat.Prime p ∧ (N:ℝ)^a < (p:ℝ)), ((p:ℝ))⁻¹)
      + ∑ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^b⌋₊).filter
        (fun p => Nat.Prime p ∧ (N:ℝ)^a < (p:ℝ)),
        ((((p:ℝ) - 1))⁻¹ - ((p:ℝ))⁻¹))) atTop (𝓝 hL) := by
    simpa using hcombine
  have hfin' : Tendsto (fun N : ℕ =>
      ((∑ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^b⌋₊).filter
        (fun p => Nat.Prime p ∧ (N:ℝ)^a < (p:ℝ)), ((p:ℝ))⁻¹)
      + ∑ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^b⌋₊).filter
        (fun p => Nat.Prime p ∧ (N:ℝ)^a < (p:ℝ)),
        ((((p:ℝ) - 1))⁻¹ - ((p:ℝ))⁻¹))) atTop (𝓝 (Real.log b - Real.log a)) := by
    simpa [hLdef] using hfin
  refine hfin'.congr' ?_
  filter_upwards with N
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  ring


/-- A sum over a long interval splits into consecutive cells. -/
private lemma sum_Ioc_chain (K : ℕ → ℕ) (hK : Monotone K) :
    ∀ (m : ℕ) (f : ℕ → ℝ),
      ∑ p ∈ Finset.Ioc (K 0) (K m), f p
        = ∑ j ∈ Finset.range m, ∑ p ∈ Finset.Ioc (K j) (K (j+1)), f p := by
  intro m
  induction m with
  | zero => intro f; simp
  | succ n ih =>
    intro f
    rw [Finset.sum_range_succ, ← ih]
    have hunion : Finset.Ioc (K 0) (K (n+1))
        = Finset.Ioc (K 0) (K n) ∪ Finset.Ioc (K n) (K (n+1)) := by
      ext p
      simp only [Finset.mem_Ioc, Finset.mem_union]
      constructor
      · intro ⟨h1, h2⟩
        by_cases hc : p ≤ K n
        · exact Or.inl ⟨h1, hc⟩
        · push Not at hc
          exact Or.inr ⟨hc, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, le_trans h2 (hK (Nat.le_succ n))⟩
        · exact ⟨lt_of_le_of_lt (hK (Nat.zero_le n)) h1, h2⟩
    have hdisj : Disjoint (Finset.Ioc (K 0) (K n)) (Finset.Ioc (K n) (K (n+1))) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_Ioc] at hp1 hp2
      omega
    rw [hunion, Finset.sum_union hdisj]

/-- Below a floor, membership is decided by the real bound. -/
private lemma lt_floor_iff {x : ℝ} (hx : 0 ≤ x) {p : ℕ} : ⌊x⌋₊ < p ↔ x < (p : ℝ) := by
  constructor
  · intro h
    exact lt_of_lt_of_le (Nat.lt_floor_add_one x) (by exact_mod_cast h)
  · intro h
    have h1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
    have h2 : (⌊x⌋₊ : ℝ) < (p : ℝ) := lt_of_le_of_lt h1 h
    exact_mod_cast h2

/-- The cell form of the interval mass limit. -/
private lemma cell_mass_tendsto (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Tendsto (fun N : ℕ => ∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter
        (fun p => Nat.Prime p), (((p:ℝ) - 1))⁻¹) atTop
      (𝓝 (Real.log b - Real.log a)) := by
  have hb : 0 < b := lt_trans ha hab
  refine (mertens_interval_totient a b ha hb hab).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  have hNa : (0:ℝ) ≤ (N:ℝ)^a := le_of_lt (rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) a)
  constructor
  · rintro ⟨h_in, h_q⟩
    exact ⟨⟨(lt_floor_iff hNa).mpr h_q.2, h_in.2⟩, h_q.1⟩
  · rintro ⟨h_in, h_q⟩
    exact ⟨⟨h_q.pos, h_in.2⟩, h_q, (lt_floor_iff hNa).mp h_in.1⟩



/-- On a single logarithmic band, a weight within `D` of a fixed value has the
mass times that value as its limit. -/
private lemma cell_weight_close (a b v : ℝ) (ha : 0 < a) (hab : a < b)
    (hv : v ∈ Set.Icc a b) (g : ℝ → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hosc : ∀ u ∈ Set.Icc a b, |g u - g v| ≤ D)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      |(∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p),
          g (Real.log (p:ℝ) / Real.log (N:ℝ)) * (((p:ℝ) - 1))⁻¹)
        - g v * (Real.log b - Real.log a)|
      ≤ D * (Real.log b - Real.log a + η) + |g v| * η := by
  set W : ℕ → ℝ := fun N => ∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter
      (fun p => Nat.Prime p), (((p:ℝ) - 1))⁻¹ with hWdef
  have hWlim : Tendsto W atTop (𝓝 (Real.log b - Real.log a)) := by
    simpa only [hWdef] using cell_mass_tendsto a b ha hab
  have hWbound : ∀ᶠ N : ℕ in atTop, |W N - (Real.log b - Real.log a)| ≤ η := by
    have h0 : Tendsto (fun N => W N - (Real.log b - Real.log a)) atTop (𝓝 0) := by
      simpa using hWlim.sub_const (Real.log b - Real.log a)
    obtain ⟨N0, hN0⟩ := (Metric.tendsto_atTop.1 h0) η hη
    filter_upwards [eventually_ge_atTop N0] with N hN
    have h1 := hN0 N hN
    rw [Real.dist_eq, sub_zero] at h1
    exact le_of_lt h1
  filter_upwards [hWbound, eventually_ge_atTop 2] with N hWN hN2
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < Real.log (N:ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hLa : 0 ≤ Real.log b - Real.log a := by
    have : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) (le_of_lt hab)
    linarith
  -- the band membership puts every argument inside `[a, b]`
  have hmem : ∀ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p),
      Real.log (p:ℝ) / Real.log (N:ℝ) ∈ Set.Icc a b ∧ (0:ℝ) < ((p:ℝ) - 1)⁻¹ := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨hlo, hhi⟩, hP⟩ := hp
    have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hP.two_le
    have hppos : 0 < (p:ℝ) := by linarith
    constructor
    · refine ⟨?_, ?_⟩
      · rw [le_div_iff₀ hlogN]
        have hlt : (N:ℝ)^a < (p:ℝ) := (lt_floor_iff (le_of_lt (rpow_pos_of_pos hNpos a))).mp hlo
        have h1 : Real.log ((N:ℝ)^a) < Real.log (p:ℝ) :=
          Real.log_lt_log (rpow_pos_of_pos hNpos a) hlt
        rw [Real.log_rpow hNpos] at h1
        linarith
      · rw [div_le_iff₀ hlogN]
        have hle : (p:ℝ) ≤ (N:ℝ)^b := by
          have h2 : (p:ℝ) ≤ (⌊(N:ℝ)^b⌋₊ : ℝ) := by exact_mod_cast hhi
          exact le_trans h2 (Nat.floor_le (le_of_lt (rpow_pos_of_pos hNpos b)))
        have h1 : Real.log (p:ℝ) ≤ Real.log ((N:ℝ)^b) := Real.log_le_log hppos hle
        rwa [Real.log_rpow hNpos] at h1
    · have : (0:ℝ) < (p:ℝ) - 1 := by linarith
      positivity
  -- split the difference
  have hWS : g v * W N
      = ∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p),
          g v * (((p:ℝ) - 1))⁻¹ := by
    rw [hWdef, Finset.mul_sum]
  have hdif : (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p),
        g (Real.log (p:ℝ) / Real.log (N:ℝ)) * (((p:ℝ) - 1))⁻¹) - g v * W N
      = ∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p),
          (g (Real.log (p:ℝ) / Real.log (N:ℝ)) - g v) * (((p:ℝ) - 1))⁻¹ := by
    rw [hWS, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hstep1 : |(∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p),
        g (Real.log (p:ℝ) / Real.log (N:ℝ)) * (((p:ℝ) - 1))⁻¹)
        - g v * W N|
      ≤ (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p),
            |g (Real.log (p:ℝ) / Real.log (N:ℝ)) - g v| * (((p:ℝ) - 1))⁻¹) := by
    rw [hdif]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
    exact Finset.sum_congr rfl fun p hp => by rw [abs_mul, abs_of_pos (hmem p hp).2]
  have hstep2 : (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p),
        |g (Real.log (p:ℝ) / Real.log (N:ℝ)) - g v| * (((p:ℝ) - 1))⁻¹) ≤ D * W N := by
    rw [hWdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    exact mul_le_mul_of_nonneg_right (hosc _ (hmem p hp).1) (le_of_lt (hmem p hp).2)
  have hWle : W N ≤ Real.log b - Real.log a + η := by
    have h := abs_le.mp hWN
    linarith [h.2]
  calc |(∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p),
        g (Real.log (p:ℝ) / Real.log (N:ℝ)) * (((p:ℝ) - 1))⁻¹)
      - g v * (Real.log b - Real.log a)|
      ≤ |(∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p),
            g (Real.log (p:ℝ) / Real.log (N:ℝ)) * (((p:ℝ) - 1))⁻¹) - g v * W N|
          + |g v * W N - g v * (Real.log b - Real.log a)| := abs_sub_le _ _ _
    _ ≤ (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p),
          |g (Real.log (p:ℝ) / Real.log (N:ℝ)) - g v| * (((p:ℝ) - 1))⁻¹)
        + |g v| * |W N - (Real.log b - Real.log a)| := by
        apply add_le_add hstep1
        rw [show g v * W N - g v * (Real.log b - Real.log a)
          = g v * (W N - (Real.log b - Real.log a)) by ring, abs_mul]
    _ ≤ D * W N + |g v| * η := by
        apply add_le_add hstep2
        exact mul_le_mul_of_nonneg_left hWN (abs_nonneg _)
    _ ≤ D * (Real.log b - Real.log a + η) + |g v| * η := by
        have := mul_le_mul_of_nonneg_left hWle hD
        linarith


/-- A single band: the integral differs from the endpoint value times the log ratio
by at most the oscillation. -/
private lemma cell_integral_close (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Set.Icc a b)) {D : ℝ}
    (hosc : ∀ u ∈ Set.Icc a b, |g u - g a| ≤ D) :
    |(∫ u in a..b, g u / u) - g a * Real.log (b / a)| ≤ D * Real.log (b / a) := by
  have hpos : ∀ u ∈ Set.Icc a b, 0 < u := fun u hu => lt_of_lt_of_le ha hu.1
  have hcont1 : ContinuousOn (fun u : ℝ => (g u - g a) / u) (Set.Icc a b) := by
    refine ContinuousOn.div (hg.sub continuousOn_const) continuousOn_id ?_
    intro u hu
    exact ne_of_gt (hpos u hu)
  have hcont2 : ContinuousOn (fun u : ℝ => u⁻¹) (Set.Icc a b) := by
    refine ContinuousOn.inv₀ continuousOn_id ?_
    intro u hu
    exact ne_of_gt (hpos u hu)
  have hint1 : IntervalIntegrable (fun u : ℝ => (g u - g a) / u)
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]
  have hint2 : IntervalIntegrable (fun u : ℝ => u⁻¹) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]
  have hint4 : IntervalIntegrable (fun u : ℝ => g a * u⁻¹) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact continuousOn_const.mul hcont2
  have hdecomp : ∫ u in a..b, g u / u
      = (∫ u in a..b, (g u - g a) / u) + g a * Real.log (b / a) := by
    have hpt : ∀ u : ℝ, g u / u = (g u - g a) / u + g a * u⁻¹ := by
      intro u
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    calc ∫ u in a..b, g u / u
        = ∫ u in a..b, ((g u - g a) / u + g a * u⁻¹) := by
          exact intervalIntegral.integral_congr fun u _ => hpt u
      _ = (∫ u in a..b, (g u - g a) / u) + ∫ u in a..b, g a * u⁻¹ :=
          intervalIntegral.integral_add hint1 hint4
      _ = (∫ u in a..b, (g u - g a) / u) + g a * ∫ u in a..b, u⁻¹ := by
          rw [intervalIntegral.integral_const_mul]
      _ = (∫ u in a..b, (g u - g a) / u) + g a * Real.log (b / a) := by
          rw [integral_inv_of_pos ha hb]
  have hbound : |∫ u in a..b, (g u - g a) / u| ≤ D * Real.log (b / a) := by
    have hcont3 : ContinuousOn (fun u : ℝ => D * u⁻¹) (Set.Icc a b) :=
      continuousOn_const.mul hcont2
    have hint3 : IntervalIntegrable (fun u : ℝ => D * u⁻¹) MeasureTheory.volume a b := by
      apply ContinuousOn.intervalIntegrable
      rwa [Set.uIcc_of_le hab]
    calc |∫ u in a..b, (g u - g a) / u|
        ≤ ∫ u in a..b, |(g u - g a) / u| :=
          intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ u in a..b, D * u⁻¹ := by
          refine intervalIntegral.integral_mono_on hab hint1.abs hint3 ?_
          intro u hu
          rw [abs_div, abs_of_pos (hpos u hu), div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (hosc u hu) (le_of_lt (inv_pos.mpr (hpos u hu)))
      _ = D * Real.log (b / a) := by
          rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha hb]
  rw [hdecomp, add_sub_cancel_right]
  exact hbound



/-- The integral over a uniform mesh splits into its cells. -/
private lemma integral_chain (f : ℝ → ℝ) (s h : ℝ)
    (hf : ∀ (a b : ℝ), IntervalIntegrable f MeasureTheory.volume a b) (m : ℕ) :
    ∫ u in s..(s + (m:ℝ) * h), f u
      = ∑ j ∈ Finset.range m, ∫ u in (s + (j:ℝ)*h)..(s + ((j:ℝ)+1)*h), f u := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    have hcast : ((n:ℝ)+1) * h = (n:ℝ)*h + h := by ring
    rw [hcast, show s + ((n:ℝ)*h + h) = (s + (n:ℝ)*h) + h by ring]
    rw [intervalIntegral.integral_add_adjacent_intervals (hf _ _) (hf _ _)]
    simp only [Nat.cast_succ]
    rw [show s + (n:ℝ) * h + h = s + ((n:ℝ)+1)*h by ring]



/-- A prime-restricted sum over a long interval splits into consecutive cells. -/
private lemma chain_filter (K : ℕ → ℕ) (hK : Monotone K) (m : ℕ) (f : ℕ → ℝ) :
    (∑ p ∈ (Finset.Ioc (K 0) (K m)).filter (fun p => Nat.Prime p), f p)
      = ∑ j ∈ Finset.range m,
          ∑ p ∈ (Finset.Ioc (K j) (K (j+1))).filter (fun p => Nat.Prime p), f p := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    have hunion : Finset.Ioc (K 0) (K (n+1))
        = Finset.Ioc (K 0) (K n) ∪ Finset.Ioc (K n) (K (n+1)) := by
      ext p
      simp only [Finset.mem_Ioc, Finset.mem_union]
      constructor
      · intro ⟨h1, h2⟩
        by_cases hc : p ≤ K n
        · exact Or.inl ⟨h1, hc⟩
        · push Not at hc
          exact Or.inr ⟨hc, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, le_trans h2 (hK (Nat.le_succ n))⟩
        · exact ⟨lt_of_le_of_lt (hK (Nat.zero_le n)) h1, h2⟩
    have hdisj : Disjoint ((Finset.Ioc (K 0) (K n)).filter (fun p => Nat.Prime p))
        ((Finset.Ioc (K n) (K (n+1))).filter (fun p => Nat.Prime p)) := by
      rw [Finset.disjoint_left]
      intro p h1 h2
      simp only [Finset.mem_filter, Finset.mem_Ioc] at h1 h2
      omega
    rw [hunion, Finset.filter_union (fun p => Nat.Prime p), Finset.sum_union hdisj]

/-- The band sum splits into the cells of a uniform logarithmic mesh. -/
private lemma band_sum_chain (s t h : ℝ) (hs : 0 < s) (hhpos : 0 < h)
    (m : ℕ) (hmh : (m:ℝ)*h = t - s) (f : ℕ → ℝ) (N : ℕ) (hN : 2 ≤ N) :
    (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊).filter (fun p => Nat.Prime p), f p)
      = ∑ j ∈ Finset.range m,
          ∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^(s + (j:ℝ)*h)⌋₊ ⌊(N:ℝ)^(s + ((j:ℝ)+1)*h)⌋₊).filter
            (fun p => Nat.Prime p), f p := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hK : Monotone (fun j : ℕ => ⌊(N:ℝ)^(s + (j:ℝ)*h)⌋₊) := by
    intro i j hij
    apply Nat.floor_mono
    apply Real.rpow_le_rpow_of_exponent_le hN1
    have h1 : (i:ℝ) ≤ (j:ℝ) := by exact_mod_cast hij
    nlinarith [hhpos]
  have hK0 : ⌊(N:ℝ)^(s + ((0:ℕ):ℝ)*h)⌋₊ = ⌊(N:ℝ)^s⌋₊ := by simp
  have hKm : ⌊(N:ℝ)^(s + (m:ℝ)*h)⌋₊ = ⌊(N:ℝ)^t⌋₊ := by
    rw [hmh]
    ring_nf
  have hchain := chain_filter (fun j : ℕ => ⌊(N:ℝ)^(s + (j:ℝ)*h)⌋₊) hK m f
  rw [hK0, hKm] at hchain
  simp only [Nat.cast_add, Nat.cast_one] at hchain
  exact hchain


/-- The band integral splits over a uniform mesh. -/
private lemma integral_chain_cont (s t h : ℝ) (hs : 0 < s) (hhpos : 0 < h) (m : ℕ)
    (hmh : (m:ℝ)*h = t - s) (g : ℝ → ℝ) (hg : ContinuousOn g (Set.Icc s t)) :
    ∫ u in s..t, g u / u
      = ∑ j ∈ Finset.range m, ∫ u in (s + (j:ℝ)*h)..(s + ((j:ℝ)+1)*h), g u / u := by
  have hst : s + (m:ℝ) * h = t := by rw [hmh]; ring
  have hmono : ∀ n : ℕ, n ≤ m → s + (n:ℝ)*h ≤ t := by
    intro n hn
    have h1 : (n:ℝ) * h ≤ (m:ℝ) * h := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hhpos)
      exact_mod_cast hn
    linarith
  have hcont : ContinuousOn (fun u : ℝ => g u / u) (Set.Icc s t) := by
    refine ContinuousOn.div hg continuousOn_id ?_
    intro u hu
    exact ne_of_gt (lt_of_lt_of_le hs hu.1)
  have hint : ∀ a b : ℝ, s ≤ a → a ≤ b → b ≤ t →
      IntervalIntegrable (fun u : ℝ => g u / u) MeasureTheory.volume a b := by
    intro a b ha hab hb
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hcont.mono (Set.Icc_subset_Icc ha hb)
  have key : ∀ n : ℕ, n ≤ m →
      ∫ u in s..(s + (n:ℝ)*h), g u / u
        = ∑ j ∈ Finset.range n, ∫ u in (s + (j:ℝ)*h)..(s + ((j:ℝ)+1)*h), g u / u := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hk' : k ≤ m := le_trans (Nat.le_succ k) hk
      rw [Finset.sum_range_succ, ← ih hk']
      simp only [Nat.cast_add, Nat.cast_one]
      have hgoal : s + ((k:ℝ)+1)*h = (s + (k:ℝ)*h) + h := by ring
      have hle1 : s ≤ s + (k:ℝ)*h := by
        have h0 : (0:ℝ) ≤ (k:ℝ)*h := by positivity
        linarith
      have hle2 : s + (k:ℝ)*h ≤ (s + (k:ℝ)*h) + h := by linarith
      have hle3 : (s + (k:ℝ)*h) + h ≤ t := by
        rw [← hgoal]
        simpa only [Nat.cast_add, Nat.cast_one] using hmono (k+1) hk
      rw [hgoal, intervalIntegral.integral_add_adjacent_intervals
        (hint s (s + (k:ℝ)*h) le_rfl hle1 (by linarith))
        (hint (s + (k:ℝ)*h) ((s + (k:ℝ)*h) + h) hle1 hle2 hle3)]
  rw [← hst]
  exact key m (le_refl m)



/-- The weighted prime band sum converges to the logarithmic integral of the weight. -/
private lemma band_weight (s t : ℝ) (hs : 0 < s) (hst : s < t)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Set.Icc s t)) :
    Tendsto (fun N : ℕ => ∑ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^t⌋₊).filter
        (fun p => Nat.Prime p ∧ (N:ℝ)^s < (p:ℝ)),
        g (Real.log (p:ℝ) / Real.log (N:ℝ)) * (((p:ℝ) - 1))⁻¹) atTop
      (𝓝 (∫ u in s..t, g u / u)) := by
  have hts : 0 < t - s := by linarith
  have hlogst : 0 < Real.log (t / s) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hs]
    linarith
  have hCex : ∃ C : ℝ, ∀ u ∈ Set.Icc s t, |g u| ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hg).isBounded.exists_norm_le
    exact ⟨C, fun u hu => by
      have hmem : g u ∈ g '' Set.Icc s t := ⟨u, hu, rfl⟩
      simpa [Real.norm_eq_abs] using hC (g u) hmem⟩
  obtain ⟨C, hC⟩ := hCex
  have hCnonneg : 0 ≤ C := le_trans (abs_nonneg _) (hC s ⟨le_rfl, le_of_lt hst⟩)
  have hucomp : UniformContinuousOn g (Set.Icc s t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg
  rw [Metric.tendsto_atTop]
  intro ε hε
  set D : ℝ := ε / (8 * Real.log (t / s)) with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.uniformContinuousOn_iff.mp hucomp) D hDpos
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (t - s) / δ < (m:ℝ) := exists_nat_gt _
  have hm0 : 0 < m := by
    have h1 : (0:ℝ) ≤ (t - s) / δ := le_of_lt (div_pos hts hδpos)
    have h2 : (0:ℝ) < (m:ℝ) := lt_of_le_of_lt h1 hm
    exact_mod_cast h2
  have hmesh : (t - s) / (m:ℝ) < δ := by
    rw [div_lt_iff₀ (by exact_mod_cast hm0)]
    rw [div_lt_iff₀ hδpos] at hm
    linarith
  set h : ℝ := (t - s) / (m:ℝ) with hhdef
  have hhpos : 0 < h := by rw [hhdef]; exact div_pos hts (by exact_mod_cast hm0)
  have hhm : (m:ℝ) * h = t - s := by
    rw [hhdef]; field_simp
  have hhδ : h < δ := by rw [hhdef]; exact hmesh
  set η : ℝ := ε / (4 * ((m:ℝ) * (2 * D + C + 1) + 1)) with hηdef
  have hηpos : 0 < η := by rw [hηdef]; positivity
  -- the per-cell bound
  have hcell : ∀ᶠ N : ℕ in atTop, ∀ j ∈ Finset.range m,
      |(∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^(s + (j:ℝ)*h)⌋₊
            ⌊(N:ℝ)^(s + ((j:ℝ)+1)*h)⌋₊).filter (fun p => Nat.Prime p),
          g (Real.log (p:ℝ) / Real.log (N:ℝ)) * (((p:ℝ) - 1))⁻¹)
        - g (s + (j:ℝ)*h) *
            (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h))|
      ≤ D * ((Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h)) + η)
        + |g (s + (j:ℝ)*h)| * η := by
    rw [Finset.eventually_all]
    intro j hj
    have hjlt : j < m := Finset.mem_range.mp hj
    have hjm : (j:ℝ) + 1 ≤ (m:ℝ) := by
      have : j + 1 ≤ m := hjlt
      exact_mod_cast this
    have hj0 : (0:ℝ) ≤ (j:ℝ)*h := by positivity
    have ha_pos : 0 < s + (j:ℝ)*h := by linarith
    have hab : s + (j:ℝ)*h < s + ((j:ℝ)+1)*h := by
      have h1 : ((j:ℝ)+1)*h = (j:ℝ)*h + h := by ring
      nlinarith [hhpos]
    have hsub : Set.Icc (s + (j:ℝ)*h) (s + ((j:ℝ)+1)*h) ⊆ Set.Icc s t := by
      intro u hu
      refine ⟨by linarith [hu.1], ?_⟩
      have h1 : ((j:ℝ)+1)*h ≤ (m:ℝ)*h := by
        apply mul_le_mul_of_nonneg_right hjm (le_of_lt hhpos)
      linarith [hu.2, hhm]
    have hosc : ∀ u ∈ Set.Icc (s + (j:ℝ)*h) (s + ((j:ℝ)+1)*h),
        |g u - g (s + (j:ℝ)*h)| ≤ D := by
      intro u hu
      have h1 : |u - (s + (j:ℝ)*h)| < δ := by
        have h0 : 0 ≤ u - (s + (j:ℝ)*h) := by linarith [hu.1]
        rw [abs_of_nonneg h0]
        have h2 : ((j:ℝ)+1)*h - (j:ℝ)*h = h := by ring
        linarith [hu.2, h2, hhδ]
      have h3 := hδ u (hsub hu) (s + (j:ℝ)*h) (hsub ⟨le_rfl, le_of_lt hab⟩) h1
      exact le_of_lt h3
    exact cell_weight_close (s + (j:ℝ)*h) (s + ((j:ℝ)+1)*h) (s + (j:ℝ)*h) ha_pos hab
      ⟨le_rfl, le_of_lt hab⟩ g (le_of_lt hDpos) hosc hηpos
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 hcell
  refine ⟨max N1 2, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hbound := hN1 N (le_trans (le_max_left _ _) hN)
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  -- rewrite the target sum in band form
  have hconv : (∑ p ∈ (Finset.Ioc 0 ⌊(N:ℝ)^t⌋₊).filter
        (fun p => Nat.Prime p ∧ (N:ℝ)^s < (p:ℝ)),
        g (Real.log (p:ℝ) / Real.log (N:ℝ)) * (((p:ℝ) - 1))⁻¹)
      = ∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊).filter (fun p => Nat.Prime p),
          g (Real.log (p:ℝ) / Real.log (N:ℝ)) * (((p:ℝ) - 1))⁻¹ := by
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    have hNa : (0:ℝ) ≤ (N:ℝ)^s := le_of_lt (rpow_pos_of_pos hNpos s)
    constructor
    · rintro ⟨h_in, h_q⟩
      exact ⟨⟨(lt_floor_iff hNa).mpr h_q.2, h_in.2⟩, h_q.1⟩
    · rintro ⟨h_in, h_q⟩
      exact ⟨⟨h_q.pos, h_in.2⟩, h_q, (lt_floor_iff hNa).mp h_in.1⟩
  rw [hconv, band_sum_chain s t h hs hhpos m hhm
    (fun p => g (Real.log (p:ℝ) / Real.log (N:ℝ)) * (((p:ℝ) - 1))⁻¹) N hN2]
  rw [Real.dist_eq]
  -- the two telescoping sums
  have hLtel : ∑ j ∈ Finset.range m,
      (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h))
      = Real.log t - Real.log s := by
    have key := Finset.sum_range_sub (fun j : ℕ => Real.log (s + (j:ℝ)*h)) m
    have hmt : s + (m:ℝ)*h = t := by rw [hhm]; ring
    simpa only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one, hmt]
      using key
  -- bound the cell sum against the integral cell by cell
  have hLnonneg : ∀ j ∈ Finset.range m,
      0 ≤ Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h) := by
    intro j hj
    have hjlt : j < m := Finset.mem_range.mp hj
    have hjm : (j:ℝ) + 1 ≤ (m:ℝ) := by
      have : j + 1 ≤ m := hjlt
      exact_mod_cast this
    have hj0 : (0:ℝ) ≤ (j:ℝ)*h := by positivity
    have ha : 0 < s + (j:ℝ)*h := by linarith
    have hb : s + (j:ℝ)*h ≤ s + ((j:ℝ)+1)*h := by
      have h1 : ((j:ℝ)+1)*h = (j:ℝ)*h + h := by ring
      linarith [hhpos]
    exact sub_nonneg.mpr (Real.log_le_log ha hb)
  have hcellG : ∀ j ∈ Finset.range m,
      |g (s + (j:ℝ)*h) *
          (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h))
        - ∫ u in (s + (j:ℝ)*h)..(s + ((j:ℝ)+1)*h), g u / u|
      ≤ D * (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h)) := by
    intro j hj
    have hjlt : j < m := Finset.mem_range.mp hj
    have hjm : (j:ℝ) + 1 ≤ (m:ℝ) := by
      have : j + 1 ≤ m := hjlt
      exact_mod_cast this
    have hj0 : (0:ℝ) ≤ (j:ℝ)*h := by positivity
    have ha_pos : 0 < s + (j:ℝ)*h := by linarith
    have hab : s + (j:ℝ)*h < s + ((j:ℝ)+1)*h := by
      have h1 : ((j:ℝ)+1)*h = (j:ℝ)*h + h := by ring
      nlinarith [hhpos]
    have hb_pos : 0 < s + ((j:ℝ)+1)*h := lt_trans ha_pos hab
    have hsub : Set.Icc (s + (j:ℝ)*h) (s + ((j:ℝ)+1)*h) ⊆ Set.Icc s t := by
      intro u hu
      refine ⟨by linarith [hu.1], ?_⟩
      have h1 : ((j:ℝ)+1)*h ≤ (m:ℝ)*h :=
        mul_le_mul_of_nonneg_right hjm (le_of_lt hhpos)
      linarith [hu.2, hhm]
    have hosc : ∀ u ∈ Set.Icc (s + (j:ℝ)*h) (s + ((j:ℝ)+1)*h),
        |g u - g (s + (j:ℝ)*h)| ≤ D := by
      intro u hu
      have h1 : |u - (s + (j:ℝ)*h)| < δ := by
        have h0 : 0 ≤ u - (s + (j:ℝ)*h) := by linarith [hu.1]
        rw [abs_of_nonneg h0]
        have h2 : ((j:ℝ)+1)*h - (j:ℝ)*h = h := by ring
        linarith [hu.2, h2, hhδ]
      exact le_of_lt (hδ u (hsub hu) (s + (j:ℝ)*h) (hsub ⟨le_rfl, le_of_lt hab⟩) h1)
    have hcj := cell_integral_close (s + (j:ℝ)*h) (s + ((j:ℝ)+1)*h) ha_pos hb_pos
      (le_of_lt hab) g (hg.mono hsub) hosc
    have hlogeq : Real.log ((s + ((j:ℝ)+1)*h) / (s + (j:ℝ)*h))
        = Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h) :=
      Real.log_div hb_pos.ne' ha_pos.ne'
    rw [hlogeq] at hcj
    calc |g (s + (j:ℝ)*h) *
          (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h))
        - ∫ u in (s + (j:ℝ)*h)..(s + ((j:ℝ)+1)*h), g u / u|
        = |(∫ u in (s + (j:ℝ)*h)..(s + ((j:ℝ)+1)*h), g u / u)
            - g (s + (j:ℝ)*h) *
              (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h))| := by
          rw [abs_sub_comm]
      _ ≤ D * (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h)) := hcj
  have hGsum : (∑ j ∈ Finset.range m,
        (g (s + (j:ℝ)*h) *
            (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h))
          - ∫ u in (s + (j:ℝ)*h)..(s + ((j:ℝ)+1)*h), g u / u))
      = (∑ j ∈ Finset.range m,
          g (s + (j:ℝ)*h) * (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h)))
        - ∫ u in s..t, g u / u := by
    rw [Finset.sum_sub_distrib, integral_chain_cont s t h hs hhpos m hhm g hg]
  have hG : |(∑ j ∈ Finset.range m, g (s + (j:ℝ)*h) *
        (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h)))
      - ∫ u in s..t, g u / u| ≤ D * (Real.log t - Real.log s) := by
    rw [← hGsum, ← hLtel, Finset.mul_sum]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hcellG)
  -- sum the per-cell bounds
  have hsumcell : (∑ j ∈ Finset.range m,
        |(∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^(s + (j:ℝ)*h)⌋₊
            ⌊(N:ℝ)^(s + ((j:ℝ)+1)*h)⌋₊).filter (fun p => Nat.Prime p),
          g (Real.log (p:ℝ) / Real.log (N:ℝ)) * (((p:ℝ) - 1))⁻¹)
        - g (s + (j:ℝ)*h) *
            (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h))|)
      ≤ D * (Real.log t - Real.log s) + D * ((m:ℝ) * η) + C * ((m:ℝ) * η) := by
    refine le_trans (Finset.sum_le_sum hbound) ?_
    have hpart : ∑ j ∈ Finset.range m,
        D * ((Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h)) + η)
        = D * (∑ j ∈ Finset.range m,
            (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h))) + D * ((m:ℝ) * η) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
      ring
    have hsplit : ∑ j ∈ Finset.range m,
        (D * ((Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h)) + η)
          + |g (s + (j:ℝ)*h)| * η)
        = D * (∑ j ∈ Finset.range m,
            (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h))) + D * ((m:ℝ) * η)
          + ∑ j ∈ Finset.range m, |g (s + (j:ℝ)*h)| * η := by
      rw [Finset.sum_add_distrib, hpart]
    rw [hsplit, hLtel]
    have hgl : ∑ j ∈ Finset.range m, |g (s + (j:ℝ)*h)| * η ≤ C * ((m:ℝ) * η) := by
      rw [← Finset.sum_mul]
      have h1 : ∑ j ∈ Finset.range m, |g (s + (j:ℝ)*h)| ≤ C * (m:ℝ) := by
        calc ∑ j ∈ Finset.range m, |g (s + (j:ℝ)*h)|
            ≤ ∑ _j ∈ Finset.range m, C := by
              refine Finset.sum_le_sum fun j hj => ?_
              have hjlt : j < m := Finset.mem_range.mp hj
              have hjm : (j:ℝ) + 1 ≤ (m:ℝ) := by
                have : j + 1 ≤ m := hjlt
                exact_mod_cast this
              have hj0 : (0:ℝ) ≤ (j:ℝ)*h := by positivity
              refine hC _ ⟨by linarith, ?_⟩
              have h1 : ((j:ℝ)+1)*h ≤ (m:ℝ)*h :=
                mul_le_mul_of_nonneg_right hjm (le_of_lt hhpos)
              linarith [hhm]
          _ = C * (m:ℝ) := by
              rw [Finset.sum_const, Finset.card_range]; ring
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right h1 hηpos.le
    linarith [hgl]
  -- assemble
  have htri : |(∑ j ∈ Finset.range m,
        ∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^(s + (j:ℝ)*h)⌋₊
            ⌊(N:ℝ)^(s + ((j:ℝ)+1)*h)⌋₊).filter (fun p => Nat.Prime p),
          g (Real.log (p:ℝ) / Real.log (N:ℝ)) * (((p:ℝ) - 1))⁻¹)
      - ∫ u in s..t, g u / u|
      ≤ D * (Real.log t - Real.log s) + D * ((m:ℝ) * η) + C * ((m:ℝ) * η)
        + D * (Real.log t - Real.log s) := by
    have h1 : (∑ j ∈ Finset.range m,
        ∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^(s + (j:ℝ)*h)⌋₊
            ⌊(N:ℝ)^(s + ((j:ℝ)+1)*h)⌋₊).filter (fun p => Nat.Prime p),
          g (Real.log (p:ℝ) / Real.log (N:ℝ)) * (((p:ℝ) - 1))⁻¹)
        = ∑ j ∈ Finset.range m,
            (g (s + (j:ℝ)*h) * (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h))
              + ((∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^(s + (j:ℝ)*h)⌋₊
                  ⌊(N:ℝ)^(s + ((j:ℝ)+1)*h)⌋₊).filter (fun p => Nat.Prime p),
                  g (Real.log (p:ℝ) / Real.log (N:ℝ)) * (((p:ℝ) - 1))⁻¹)
                - g (s + (j:ℝ)*h) *
                    (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h)))) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h1, Finset.sum_add_distrib]
    have := abs_add_le (∑ j ∈ Finset.range m,
        g (s + (j:ℝ)*h) * (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h)))
      (∑ j ∈ Finset.range m,
        ((∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^(s + (j:ℝ)*h)⌋₊
            ⌊(N:ℝ)^(s + ((j:ℝ)+1)*h)⌋₊).filter (fun p => Nat.Prime p),
          g (Real.log (p:ℝ) / Real.log (N:ℝ)) * (((p:ℝ) - 1))⁻¹)
          - g (s + (j:ℝ)*h) *
              (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h))))
    have h2 : |∑ j ∈ Finset.range m,
        g (s + (j:ℝ)*h) * (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h))
        - ∫ u in s..t, g u / u| ≤ D * (Real.log t - Real.log s) := hG
    have h3 : |∑ j ∈ Finset.range m,
        ((∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^(s + (j:ℝ)*h)⌋₊
            ⌊(N:ℝ)^(s + ((j:ℝ)+1)*h)⌋₊).filter (fun p => Nat.Prime p),
          g (Real.log (p:ℝ) / Real.log (N:ℝ)) * (((p:ℝ) - 1))⁻¹)
          - g (s + (j:ℝ)*h) *
              (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h)))|
        ≤ D * (Real.log t - Real.log s) + D * ((m:ℝ) * η) + C * ((m:ℝ) * η) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) hsumcell
    calc |(∑ j ∈ Finset.range m,
          g (s + (j:ℝ)*h) * (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h)))
        + ∑ j ∈ Finset.range m,
          ((∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^(s + (j:ℝ)*h)⌋₊
              ⌊(N:ℝ)^(s + ((j:ℝ)+1)*h)⌋₊).filter (fun p => Nat.Prime p),
            g (Real.log (p:ℝ) / Real.log (N:ℝ)) * (((p:ℝ) - 1))⁻¹)
            - g (s + (j:ℝ)*h) *
                (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h)))
        - ∫ u in s..t, g u / u|
        = |(∑ j ∈ Finset.range m,
            g (s + (j:ℝ)*h) * (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h))
            - ∫ u in s..t, g u / u)
          + ∑ j ∈ Finset.range m,
            ((∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^(s + (j:ℝ)*h)⌋₊
                ⌊(N:ℝ)^(s + ((j:ℝ)+1)*h)⌋₊).filter (fun p => Nat.Prime p),
              g (Real.log (p:ℝ) / Real.log (N:ℝ)) * (((p:ℝ) - 1))⁻¹)
              - g (s + (j:ℝ)*h) *
                  (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h)))| := by
          congr 1; ring
      _ ≤ |(∑ j ∈ Finset.range m,
            g (s + (j:ℝ)*h) * (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h))
            - ∫ u in s..t, g u / u)|
          + |∑ j ∈ Finset.range m,
            ((∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^(s + (j:ℝ)*h)⌋₊
                ⌊(N:ℝ)^(s + ((j:ℝ)+1)*h)⌋₊).filter (fun p => Nat.Prime p),
              g (Real.log (p:ℝ) / Real.log (N:ℝ)) * (((p:ℝ) - 1))⁻¹)
              - g (s + (j:ℝ)*h) *
                  (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h)))| := abs_add_le _ _
      _ ≤ D * (Real.log t - Real.log s) + D * ((m:ℝ) * η) + C * ((m:ℝ) * η)
          + D * (Real.log t - Real.log s) := by
          linarith [add_le_add h2 h3]
  -- the final epsilon estimate
  have hlogsub : Real.log t - Real.log s = Real.log (t / s) := by
    rw [Real.log_div (ne_of_gt (lt_trans hs hst)) (ne_of_gt hs)]
  have hDval : D * (Real.log t - Real.log s) = ε / 8 := by
    rw [hDdef, hlogsub]
    field_simp
  have hmη : D * ((m:ℝ) * η) + C * ((m:ℝ) * η)
      = (D + C) * ((m:ℝ) * η) := by ring
  have hstep : (D + C) * ((m:ℝ) * η) ≤ ε / 4 := by
    have hden : 0 < 4 * ((m:ℝ) * (2 * D + C + 1) + 1) := by positivity
    have hkey : (m:ℝ) * (D + C) ≤ (m:ℝ) * (2 * D + C + 1) + 1 := by
      have h1 : D + C ≤ 2 * D + C + 1 := by linarith
      have h2 : (m:ℝ) * (D + C) ≤ (m:ℝ) * (2 * D + C + 1) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      linarith
    have hEq : (D + C) * ((m:ℝ) * η)
        = ε * ((m:ℝ) * (D + C)) / (4 * ((m:ℝ) * (2 * D + C + 1) + 1)) := by
      rw [hηdef]
      field_simp
    rw [hEq]
    have h3 : ε * ((m:ℝ) * (D + C)) / (4 * ((m:ℝ) * (2 * D + C + 1) + 1))
        ≤ ε * ((m:ℝ) * (2 * D + C + 1) + 1)
            / (4 * ((m:ℝ) * (2 * D + C + 1) + 1)) := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact mul_le_mul_of_nonneg_left hkey hε.le
    have h4 : ε * ((m:ℝ) * (2 * D + C + 1) + 1)
        / (4 * ((m:ℝ) * (2 * D + C + 1) + 1)) = ε / 4 := by
      field_simp
    rw [h4] at h3
    exact h3
  linarith [htri, hDval, hstep, hmη]


/-- For distinct primes the totient of the product is the product of the shifted primes. -/
private lemma totient_mul_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (Nat.totient (p * q) : ℝ) = ((p:ℝ) - 1) * ((q:ℝ) - 1) := by
  have hcop : p.Coprime q := by
    refine hp.coprime_iff_not_dvd.mpr ?_
    intro hdvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd)
  have hp1 : 1 ≤ p := hp.one_le
  have hq1 : 1 ≤ q := hq.one_le
  rw [Nat.totient_mul hcop, Nat.totient_prime hp, Nat.totient_prime hq]
  push_cast [Nat.cast_sub hp1, Nat.cast_sub hq1]
  ring



/-- The prime-pair mass of a rectangle is the product of its two band masses. -/
private lemma box_mass_tendsto (a b c d : ℝ) (ha : 0 < a) (hab : a < b)
    (hc : 0 < c) (hcd : c < d) :
    Tendsto (fun N : ℕ =>
      ∑ q ∈ ((Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊) ×ˢ
          (Finset.Ioc ⌊(N:ℝ)^c⌋₊ ⌊(N:ℝ)^d⌋₊)).filter
        (fun q : ℕ × ℕ => q.1.Prime ∧ q.2.Prime),
        (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹))) atTop
      (𝓝 ((Real.log b - Real.log a) * (Real.log d - Real.log c))) := by
  have hX := cell_mass_tendsto a b ha hab
  have hY := cell_mass_tendsto c d hc hcd
  have hprod := hX.mul hY
  refine hprod.congr' ?_
  filter_upwards with N
  have hfil : ((Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊) ×ˢ
      (Finset.Ioc ⌊(N:ℝ)^c⌋₊ ⌊(N:ℝ)^d⌋₊)).filter
        (fun q : ℕ × ℕ => q.1.Prime ∧ q.2.Prime)
      = (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p) ×ˢ
        (Finset.Ioc ⌊(N:ℝ)^c⌋₊ ⌊(N:ℝ)^d⌋₊).filter (fun p => Nat.Prime p) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  rw [hfil, Finset.sum_product]
  simp only [← Finset.mul_sum, Finset.sum_mul]



/-- At most one over kappa distinct prime divisors of `N` can exceed `N` to `kappa`. -/
private lemma large_prime_divisor_card_aux {N : ℕ} (hN : 2 ≤ N) (P : Finset ℕ)
    (hsub : P ⊆ N.primeFactors) {κ : ℝ} (hκ : 0 < κ)
    (hP : ∀ p ∈ P, (N : ℝ) ^ κ ≤ (p : ℝ)) : (P.card : ℝ) ≤ 1 / κ := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hprod : (∏ p ∈ P, p) ≤ N := by
    calc (∏ p ∈ P, p) ≤ ∏ p ∈ N.primeFactors, p := by
          apply Finset.prod_le_prod_of_subset_of_one_le₀ hsub
          · intros; exact Nat.zero_le _
          · intro p hp _
            exact (Nat.mem_primeFactors.mp hp).1.one_le
      _ ≤ N := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd N)
  have hprodR : (∏ p ∈ P, (p : ℝ)) ≤ N := by
    simpa only [Nat.cast_prod] using (Nat.cast_le (α := ℝ).mpr hprod)
  have hpow : ((N : ℝ) ^ κ) ^ P.card ≤ N := by
    calc _ = ∏ _p ∈ P, (N : ℝ) ^ κ := by simp
      _ ≤ ∏ p ∈ P, (p : ℝ) := Finset.prod_le_prod₀ (by intros; positivity) hP
      _ ≤ N := hprodR
  have hl := Real.log_le_log (pow_pos (rpow_pos_of_pos hpos _) _) hpow
  rw [Real.log_pow, Real.log_rpow hpos] at hl
  apply (le_div_iff₀ hκ).2
  nlinarith

/-- Primes above `N ^ kappa` that divide `N` carry at most `1 / (kappa * N ^ kappa)` mass. -/
private lemma exceptional_reciprocal_sum_aux (P : Finset ℕ) {N : ℕ} (hN : 2 ≤ N)
    {κ : ℝ} (hκ : 0 < κ)
    (hP : ∀ p ∈ P, p.Prime ∧ (N : ℝ) ^ κ ≤ (p : ℝ)) :
    (∑ p ∈ P.filter (fun p => ¬ p.Coprime N), 1 / (p : ℝ)) ≤
      1 / (κ * (N : ℝ) ^ κ) := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hz : 0 < (N : ℝ) ^ κ := rpow_pos_of_pos hpos _
  have hsub : P.filter (fun p => ¬ p.Coprime N) ⊆ N.primeFactors := by
    intro p hp
    obtain ⟨hpP, hbad⟩ := Finset.mem_filter.mp hp
    have hprime := (hP p hpP).1
    have hdvd : p ∣ N := by
      simpa only [hprime.coprime_iff_not_dvd, not_not] using hbad
    exact Nat.mem_primeFactors.mpr ⟨hprime, hdvd, by omega⟩
  have hc := large_prime_divisor_card_aux hN _ hsub hκ
    (fun p hp => (hP p (Finset.mem_filter.mp hp).1).2)
  calc _ ≤ ∑ _p ∈ P.filter (fun p => ¬ p.Coprime N), 1 / (N : ℝ) ^ κ := by
        apply Finset.sum_le_sum
        intro p hp
        exact one_div_le_one_div_of_le hz (hP p (Finset.mem_filter.mp hp).1).2
    _ = ((P.filter (fun p => ¬ p.Coprime N)).card : ℝ) / (N : ℝ) ^ κ := by
        simp [div_eq_mul_inv]
    _ ≤ (1 / κ) / (N : ℝ) ^ κ := div_le_div_of_nonneg_right hc hz.le
    _ = _ := by rw [div_div]



/-- Primes in a band above `N ^ a` that divide `N` carry at most `2 / (a * N ^ a)` of the
`1 / (p - 1)` mass. -/
private lemma band_bad_totient_mass {a b : ℝ} (ha : 0 < a) {N : ℕ} (hN : 2 ≤ N) :
    (∑ p ∈ ((Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p)).filter
        (fun p => ¬ p.Coprime N), (((p:ℝ) - 1))⁻¹) ≤ 2 / (a * (N:ℝ)^a) := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNa : 0 < (N:ℝ)^a := rpow_pos_of_pos hNpos a
  have hmem : ∀ p ∈ ((Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p)).filter
      (fun p => ¬ p.Coprime N), Nat.Prime p ∧ (N:ℝ)^a ≤ (p:ℝ) := by
    intro p hp
    have hp1 : p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p) :=
      (Finset.mem_filter.mp hp).1
    have hprime : Nat.Prime p := (Finset.mem_filter.mp hp1).2
    have hlo : ⌊(N:ℝ)^a⌋₊ < p := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp1).1).1
    exact ⟨hprime, le_of_lt ((lt_floor_iff (le_of_lt hNa)).mp hlo)⟩
  have hexc : (∑ p ∈ ((Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter
      (fun p => Nat.Prime p)).filter (fun p => ¬ p.Coprime N), 1 / (p : ℝ)) ≤
      1 / (a * (N:ℝ)^a) := by
    refine exceptional_reciprocal_sum_aux
      (P := (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p)) hN ha ?_
    intro p hp
    have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hlo : ⌊(N:ℝ)^a⌋₊ < p := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
    exact ⟨hprime, le_of_lt ((lt_floor_iff (le_of_lt hNa)).mp hlo)⟩
  have hpt : ∀ p ∈ ((Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter
      (fun p => Nat.Prime p)).filter (fun p => ¬ p.Coprime N),
      (((p:ℝ) - 1))⁻¹ ≤ 2 * (1 / (p : ℝ)) := by
    intro p hp
    obtain ⟨hprime, -⟩ := hmem p hp
    have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hprime.two_le
    have h1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
    have hhalf : (0:ℝ) < (p:ℝ) / 2 := by linarith
    have hle : (p:ℝ) / 2 ≤ (p:ℝ) - 1 := by linarith
    rw [inv_eq_one_div]
    calc 1 / ((p:ℝ) - 1) ≤ 1 / ((p:ℝ) / 2) := one_div_le_one_div_of_le hhalf hle
      _ = 2 / (p:ℝ) := by field_simp
      _ = 2 * (1 / (p:ℝ)) := by ring
  calc (∑ p ∈ ((Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p)).filter
        (fun p => ¬ p.Coprime N), (((p:ℝ) - 1))⁻¹)
      ≤ ∑ p ∈ ((Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p)).filter
        (fun p => ¬ p.Coprime N), 2 * (1 / (p : ℝ)) := Finset.sum_le_sum hpt
    _ = 2 * (∑ p ∈ ((Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p)).filter
        (fun p => ¬ p.Coprime N), 1 / (p : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ 2 * (1 / (a * (N:ℝ)^a)) := by linarith [hexc]
    _ = 2 / (a * (N:ℝ)^a) := by ring


/-- Removing the coprimality-to-`N` condition from a prime rectangle costs `o(1)` in mass. -/
private lemma bad_pair_mass_tendsto (a b c d : ℝ) (ha : 0 < a) (hab : a < b)
    (hc : 0 < c) (hcd : c < d) :
    Tendsto (fun N : ℕ =>
      ∑ q ∈ (((Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p)) ×ˢ
          ((Finset.Ioc ⌊(N:ℝ)^c⌋₊ ⌊(N:ℝ)^d⌋₊).filter (fun p => Nat.Prime p))).filter
        (fun q : ℕ × ℕ => ¬ q.1.Coprime N ∨ ¬ q.2.Coprime N),
        (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹))) atTop (𝓝 0) := by
  have hP := cell_mass_tendsto a b ha hab
  have hQ := cell_mass_tendsto c d hc hcd
  have hPb : ∀ᶠ N : ℕ in atTop, (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter
      (fun p => Nat.Prime p), (((p:ℝ) - 1))⁻¹) ≤ Real.log b - Real.log a + 1 :=
    (hP.eventually (eventually_lt_nhds (lt_add_one _))).mono fun N h => le_of_lt h
  have hQb : ∀ᶠ N : ℕ in atTop, (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^c⌋₊ ⌊(N:ℝ)^d⌋₊).filter
      (fun p => Nat.Prime p), (((p:ℝ) - 1))⁻¹) ≤ Real.log d - Real.log c + 1 :=
    (hQ.eventually (eventually_lt_nhds (lt_add_one _))).mono fun N h => le_of_lt h
  have hpow_a : Tendsto (fun N : ℕ => (N:ℝ)^a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hpow_c : Tendsto (fun N : ℕ => (N:ℝ)^c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  have hmaj : Tendsto (fun N : ℕ =>
      (2 / (a * (N:ℝ)^a)) * (Real.log d - Real.log c + 1)
        + (Real.log b - Real.log a + 1) * (2 / (c * (N:ℝ)^c))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => 2 / (a * (N:ℝ)^a)) atTop (𝓝 0) := by
      have hinv : Tendsto (fun N : ℕ => ((N:ℝ)^a)⁻¹) atTop (𝓝 0) := hpow_a.inv_tendsto_atTop
      have h2 : Tendsto (fun N : ℕ => (2 / a) * ((N:ℝ)^a)⁻¹) atTop (𝓝 0) := by
        simpa using hinv.const_mul (2 / a)
      refine h2.congr' ?_
      filter_upwards with N
      field_simp
    have h3 : Tendsto (fun N : ℕ => 2 / (c * (N:ℝ)^c)) atTop (𝓝 0) := by
      have hinv : Tendsto (fun N : ℕ => ((N:ℝ)^c)⁻¹) atTop (𝓝 0) := hpow_c.inv_tendsto_atTop
      have h2 : Tendsto (fun N : ℕ => (2 / c) * ((N:ℝ)^c)⁻¹) atTop (𝓝 0) := by
        simpa using hinv.const_mul (2 / c)
      refine h2.congr' ?_
      filter_upwards with N
      field_simp
    have h4 := (h1.mul_const (Real.log d - Real.log c + 1)).add
      (h3.const_mul (Real.log b - Real.log a + 1))
    simpa using h4
  refine squeeze_zero'
    (f := fun N : ℕ =>
      ∑ q ∈ (((Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p)) ×ˢ
          ((Finset.Ioc ⌊(N:ℝ)^c⌋₊ ⌊(N:ℝ)^d⌋₊).filter (fun p => Nat.Prime p))).filter
        (fun q : ℕ × ℕ => ¬ q.1.Coprime N ∨ ¬ q.2.Coprime N),
        (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)))
    (g := fun N : ℕ =>
      (2 / (a * (N:ℝ)^a)) * (Real.log d - Real.log c + 1)
        + (Real.log b - Real.log a + 1) * (2 / (c * (N:ℝ)^c))) ?_ ?_ hmaj
  · filter_upwards with N
    refine Finset.sum_nonneg fun q hq => ?_
    have hp_mem : q.1 ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p) :=
      (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1
    have hq_mem : q.2 ∈ (Finset.Ioc ⌊(N:ℝ)^c⌋₊ ⌊(N:ℝ)^d⌋₊).filter (fun p => Nat.Prime p) :=
      (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).2
    have hp : Nat.Prime q.1 := (Finset.mem_filter.mp hp_mem).2
    have hq' : Nat.Prime q.2 := (Finset.mem_filter.mp hq_mem).2
    have h1 : (2:ℝ) ≤ (q.1:ℝ) := by exact_mod_cast hp.two_le
    have h2 : (2:ℝ) ≤ (q.2:ℝ) := by exact_mod_cast hq'.two_le
    exact mul_nonneg (le_of_lt (inv_pos.mpr (by linarith)))
      (le_of_lt (inv_pos.mpr (by linarith)))
  · filter_upwards [hPb, hQb, eventually_ge_atTop 2] with N hPN hQN hN2
    have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hNa : 0 < (N:ℝ)^a := rpow_pos_of_pos hNpos a
    have hNc : 0 < (N:ℝ)^c := rpow_pos_of_pos hNpos c
    have hQnn : (0:ℝ) ≤ ∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^c⌋₊ ⌊(N:ℝ)^d⌋₊).filter
        (fun p => Nat.Prime p), (((q:ℝ) - 1))⁻¹ := by
      refine Finset.sum_nonneg fun q hq => ?_
      have hq' : Nat.Prime q := (Finset.mem_filter.mp hq).2
      have h2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq'.two_le
      exact le_of_lt (inv_pos.mpr (by linarith))
    have hbad_pt : ∀ q ∈ ((((Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter
          (fun p => Nat.Prime p)) ×ˢ ((Finset.Ioc ⌊(N:ℝ)^c⌋₊ ⌊(N:ℝ)^d⌋₊).filter
          (fun p => Nat.Prime p))).filter
        (fun q : ℕ × ℕ => ¬ q.1.Coprime N ∨ ¬ q.2.Coprime N)),
        (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹))
        ≤ (if ¬ q.1.Coprime N then (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)) else 0)
          + (if ¬ q.2.Coprime N then (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)) else 0) := by
      intro q hq
      have hmem := (Finset.mem_filter.mp hq).1
      have hp : Nat.Prime q.1 := (Finset.mem_filter.mp (Finset.mem_product.mp hmem).1).2
      have hq' : Nat.Prime q.2 := (Finset.mem_filter.mp (Finset.mem_product.mp hmem).2).2
      have h1 : (2:ℝ) ≤ (q.1:ℝ) := by exact_mod_cast hp.two_le
      have h2 : (2:ℝ) ≤ (q.2:ℝ) := by exact_mod_cast hq'.two_le
      have hnn : (0:ℝ) ≤ ((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹) :=
        mul_nonneg (le_of_lt (inv_pos.mpr (by linarith)))
          (le_of_lt (inv_pos.mpr (by linarith)))
      rcases (Finset.mem_filter.mp hq).2 with h | h
      · rw [if_pos h]
        split_ifs with h2' <;> linarith
      · rw [if_pos h]
        split_ifs with h1' <;> linarith
    have hstep1 : (∑ q ∈ ((((Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter
          (fun p => Nat.Prime p)) ×ˢ ((Finset.Ioc ⌊(N:ℝ)^c⌋₊ ⌊(N:ℝ)^d⌋₊).filter
          (fun p => Nat.Prime p))).filter
        (fun q : ℕ × ℕ => ¬ q.1.Coprime N ∨ ¬ q.2.Coprime N)),
        (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)))
      ≤ (∑ q ∈ ((Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p)) ×ˢ
          ((Finset.Ioc ⌊(N:ℝ)^c⌋₊ ⌊(N:ℝ)^d⌋₊).filter (fun p => Nat.Prime p)),
          (if ¬ q.1.Coprime N then (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)) else 0))
        + (∑ q ∈ ((Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p)) ×ˢ
          ((Finset.Ioc ⌊(N:ℝ)^c⌋₊ ⌊(N:ℝ)^d⌋₊).filter (fun p => Nat.Prime p)),
          (if ¬ q.2.Coprime N then (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)) else 0)) := by
      rw [← Finset.sum_add_distrib]
      refine le_trans (Finset.sum_le_sum hbad_pt) ?_
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
      intro q hq _
      have hp : Nat.Prime q.1 := (Finset.mem_filter.mp (Finset.mem_product.mp hq).1).2
      have hq' : Nat.Prime q.2 := (Finset.mem_filter.mp (Finset.mem_product.mp hq).2).2
      have h1 : (2:ℝ) ≤ (q.1:ℝ) := by exact_mod_cast hp.two_le
      have h2 : (2:ℝ) ≤ (q.2:ℝ) := by exact_mod_cast hq'.two_le
      have hw : (0:ℝ) ≤ ((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹) :=
        mul_nonneg (le_of_lt (inv_pos.mpr (by linarith)))
          (le_of_lt (inv_pos.mpr (by linarith)))
      split_ifs <;> linarith
    have hfac2 : (∑ q ∈ ((Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p)) ×ˢ
          ((Finset.Ioc ⌊(N:ℝ)^c⌋₊ ⌊(N:ℝ)^d⌋₊).filter (fun p => Nat.Prime p)),
          (if ¬ q.1.Coprime N then (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)) else 0))
        = (∑ p ∈ ((Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p)).filter
            (fun p => ¬ p.Coprime N), (((p:ℝ) - 1)⁻¹))
          * (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^c⌋₊ ⌊(N:ℝ)^d⌋₊).filter (fun p => Nat.Prime p),
              (((q:ℝ) - 1)⁻¹)) := by
      rw [Finset.sum_product]
      have hinner : ∀ p : ℕ,
          (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^c⌋₊ ⌊(N:ℝ)^d⌋₊).filter (fun p => Nat.Prime p),
              (if ¬ p.Coprime N then (((p:ℝ) - 1)⁻¹ * (((q:ℝ) - 1)⁻¹)) else 0))
            = (if ¬ p.Coprime N then (((p:ℝ) - 1)⁻¹ *
                (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^c⌋₊ ⌊(N:ℝ)^d⌋₊).filter (fun p => Nat.Prime p),
                  (((q:ℝ) - 1)⁻¹))) else 0) := by
        intro p
        by_cases h : ¬ p.Coprime N
        · simp [h, Finset.mul_sum]
        · simp [h]
      simp only [hinner]
      rw [← Finset.sum_filter, ← Finset.sum_mul]
    have hstep2 : (∑ q ∈ ((Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p)) ×ˢ
          ((Finset.Ioc ⌊(N:ℝ)^c⌋₊ ⌊(N:ℝ)^d⌋₊).filter (fun p => Nat.Prime p)),
          (if ¬ q.1.Coprime N then (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)) else 0))
        ≤ (2 / (a * (N:ℝ)^a)) * (Real.log d - Real.log c + 1) := by
      rw [hfac2]
      exact mul_le_mul (band_bad_totient_mass (b := b) ha hN2) hQN hQnn
        (le_of_lt (div_pos (by norm_num) (mul_pos ha hNa)))
    have hfac3 : (∑ q ∈ ((Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p)) ×ˢ
          ((Finset.Ioc ⌊(N:ℝ)^c⌋₊ ⌊(N:ℝ)^d⌋₊).filter (fun p => Nat.Prime p)),
          (if ¬ q.2.Coprime N then (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)) else 0))
        = (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p),
            (((p:ℝ) - 1)⁻¹))
          * (∑ q ∈ ((Finset.Ioc ⌊(N:ℝ)^c⌋₊ ⌊(N:ℝ)^d⌋₊).filter (fun p => Nat.Prime p)).filter
              (fun q => ¬ q.Coprime N), (((q:ℝ) - 1)⁻¹)) := by
      rw [Finset.sum_product]
      have hinner : ∀ p : ℕ,
          (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^c⌋₊ ⌊(N:ℝ)^d⌋₊).filter (fun p => Nat.Prime p),
              (if ¬ q.Coprime N then (((p:ℝ) - 1)⁻¹ * (((q:ℝ) - 1)⁻¹)) else 0))
            = (∑ q ∈ ((Finset.Ioc ⌊(N:ℝ)^c⌋₊ ⌊(N:ℝ)^d⌋₊).filter (fun p => Nat.Prime p)).filter
                (fun q => ¬ q.Coprime N), (((p:ℝ) - 1)⁻¹ * (((q:ℝ) - 1)⁻¹))) := by
        intro p
        conv_rhs => rw [Finset.sum_filter]
      simp only [hinner]
      have hpull : ∀ p : ℕ,
          (∑ q ∈ ((Finset.Ioc ⌊(N:ℝ)^c⌋₊ ⌊(N:ℝ)^d⌋₊).filter (fun p => Nat.Prime p)).filter
              (fun q => ¬ q.Coprime N), (((p:ℝ) - 1)⁻¹ * (((q:ℝ) - 1)⁻¹)))
            = ((p:ℝ) - 1)⁻¹ *
              (∑ q ∈ ((Finset.Ioc ⌊(N:ℝ)^c⌋₊ ⌊(N:ℝ)^d⌋₊).filter (fun p => Nat.Prime p)).filter
                (fun q => ¬ q.Coprime N), (((q:ℝ) - 1)⁻¹)) := by
        intro p
        rw [Finset.mul_sum]
      simp only [hpull]
      rw [Finset.sum_mul]
    have hstep3 : (∑ q ∈ ((Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p)) ×ˢ
          ((Finset.Ioc ⌊(N:ℝ)^c⌋₊ ⌊(N:ℝ)^d⌋₊).filter (fun p => Nat.Prime p)),
          (if ¬ q.2.Coprime N then (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)) else 0))
        ≤ (Real.log b - Real.log a + 1) * (2 / (c * (N:ℝ)^c)) := by
      rw [hfac3]
      have hPnn : (0:ℝ) ≤ ∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter
          (fun p => Nat.Prime p), (((p:ℝ) - 1))⁻¹ := by
        refine Finset.sum_nonneg fun q hq => ?_
        have hq' : Nat.Prime q := (Finset.mem_filter.mp hq).2
        have h2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq'.two_le
        exact le_of_lt (inv_pos.mpr (by linarith))
      have hQbadnn : (0:ℝ) ≤ ∑ q ∈ ((Finset.Ioc ⌊(N:ℝ)^c⌋₊ ⌊(N:ℝ)^d⌋₊).filter
          (fun p => Nat.Prime p)).filter (fun q => ¬ q.Coprime N), (((q:ℝ) - 1)⁻¹) := by
        refine Finset.sum_nonneg fun q hq => ?_
        have hq' : Nat.Prime q := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
        have h2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq'.two_le
        exact le_of_lt (inv_pos.mpr (by linarith))
      exact mul_le_mul hPN (band_bad_totient_mass (a := c) (b := d) hc hN2) hQbadnn
        (by linarith)
    linarith [hstep1, hstep2, hstep3]



/-- The finite level at a product of two primes is an explicit function of the two
normalized logarithms, up to the `B` loss. -/
private lemma lowerLevel_mul (B : ℝ) {N p q : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (hq : 0 < q) :
    lowerLevel B N (p * q)
      = (1 / 2 - Real.log (p:ℝ) / Real.log (N:ℝ) - Real.log (q:ℝ) / Real.log (N:ℝ)) / kappa1
        - (B / kappa1) * (Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ)) := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N:ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hpqR : (0:ℝ) < ((p*q : ℕ) : ℝ) := by
    have h0 : (0:ℕ) < p * q := Nat.mul_pos hp hq
    exact_mod_cast h0
  have hden : (0:ℝ) < (Real.log (N:ℝ))^B := by positivity
  have hnum : (0:ℝ) < (N:ℝ)^(1/2:ℝ) / (Real.log (N:ℝ))^B := by positivity
  have hk1 : kappa1 ≠ 0 := by norm_num [kappa1]
  unfold lowerLevel
  rw [Real.log_div hnum.ne' hpqR.ne', Nat.cast_mul,
    Real.log_mul hpR.ne' hqR.ne',
    Real.log_div (rpow_pos_of_pos hNpos (1/2:ℝ)).ne' hden.ne',
    Real.log_rpow hNpos, Real.log_rpow hlog, Real.log_rpow hNpos]
  field_simp
  ring


/-- On a fixed prime rectangle all of whose levels lie within `D` of one value, the weighted
prime sum is within `D` times the rectangle mass of that value times the mass. -/
private lemma box_weight_close (T T' U U' s D : ℝ) (B : ℝ) (hD : 0 ≤ D) (F : ℝ → ℝ)
    (hsmall : ∀ᶠ N : ℕ in atTop, ∀ p q : ℕ, ⌊(N:ℝ)^T⌋₊ < p → p ≤ ⌊(N:ℝ)^T'⌋₊ →
      ⌊(N:ℝ)^U⌋₊ < q → q ≤ ⌊(N:ℝ)^U'⌋₊ → |F (lowerLevel B N (p * q)) - F s| ≤ D) :
    ∀ᶠ N : ℕ in atTop,
      |(∑ q ∈ ((Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p)) ×ˢ
          ((Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun p => Nat.Prime p)),
          F (lowerLevel B N (q.1 * q.2)) * (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)))
        - F s * (∑ q ∈ ((Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p)) ×ˢ
          ((Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun p => Nat.Prime p)),
          (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)))|
      ≤ D * (∑ q ∈ ((Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p)) ×ˢ
          ((Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun p => Nat.Prime p)),
          (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹))) := by
  filter_upwards [hsmall] with N hN
  have hweighted : (∑ q ∈ ((Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p)) ×ˢ
          ((Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun p => Nat.Prime p)),
          F (lowerLevel B N (q.1 * q.2)) * (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)))
        - F s * (∑ q ∈ ((Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p)) ×ˢ
          ((Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun p => Nat.Prime p)),
          (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)))
      = ∑ q ∈ ((Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p)) ×ˢ
          ((Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun p => Nat.Prime p)),
          (F (lowerLevel B N (q.1 * q.2)) - F s) * (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [hweighted]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hpt : ∀ q ∈ ((Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p)) ×ˢ
          ((Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun p => Nat.Prime p)),
      |(F (lowerLevel B N (q.1 * q.2)) - F s) * (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹))|
        ≤ D * (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)) := by
    intro q hq
    have hmem := (Finset.mem_product.mp hq)
    have hp : Nat.Prime q.1 := (Finset.mem_filter.mp hmem.1).2
    have hq' : Nat.Prime q.2 := (Finset.mem_filter.mp hmem.2).2
    have h1 : (2:ℝ) ≤ (q.1:ℝ) := by exact_mod_cast hp.two_le
    have h2 : (2:ℝ) ≤ (q.2:ℝ) := by exact_mod_cast hq'.two_le
    have hw : (0:ℝ) ≤ ((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹) :=
      mul_nonneg (le_of_lt (inv_pos.mpr (by linarith)))
        (le_of_lt (inv_pos.mpr (by linarith)))
    have hlev := hN q.1 q.2 (Finset.mem_Ioc.mp (Finset.mem_filter.mp hmem.1).1).1
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hmem.1).1).2
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hmem.2).1).1
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hmem.2).1).2
    rw [abs_mul, abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_right hlev hw
  calc ∑ q ∈ ((Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p)) ×ˢ
          ((Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun p => Nat.Prime p)),
          |(F (lowerLevel B N (q.1 * q.2)) - F s) * (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹))|
      ≤ ∑ q ∈ ((Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p)) ×ˢ
          ((Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun p => Nat.Prime p)),
          D * (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)) := Finset.sum_le_sum hpt
    _ = D * (∑ q ∈ ((Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p)) ×ˢ
          ((Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun p => Nat.Prime p)),
          (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹))) := by rw [Finset.mul_sum]



/-- Uniform level closeness on a prime rectangle of the region, up to the `B` loss. -/
private lemma level_close (B : ℝ) (T T' U U' : ℝ) (hT : 0 < T) (hT' : T ≤ T')
    (hU : 0 < U) (hU' : U ≤ U') :
    ∀ᶠ N : ℕ in atTop, ∀ p q : ℕ, ⌊(N:ℝ)^T⌋₊ < p → p ≤ ⌊(N:ℝ)^T'⌋₊ →
      ⌊(N:ℝ)^U⌋₊ < q → q ≤ ⌊(N:ℝ)^U'⌋₊ →
      |lowerLevel B N (p * q) - (1 / 2 - T - U) / kappa1|
        ≤ ((T' - T) + (U' - U)) / kappa1
          + |B| * (Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ)) / kappa1 := by
  have hk1 : (0:ℝ) < kappa1 := by norm_num [kappa1]
  filter_upwards [eventually_ge_atTop 3] with N hN3
  intro p q hp1 hp2 hq1 hq2
  have hN2 : 2 ≤ N := by omega
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N:ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hp0 : 0 < p := by
    have h0 : 0 ≤ ⌊(N:ℝ)^T⌋₊ := Nat.zero_le _
    omega
  have hq0 : 0 < q := by
    have h0 : 0 ≤ ⌊(N:ℝ)^U⌋₊ := Nat.zero_le _
    omega
  have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp0
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq0
  have htp_lo : T < Real.log (p:ℝ) / Real.log (N:ℝ) := by
    rw [lt_div_iff₀ hlog]
    have hlt : (N:ℝ)^T < (p:ℝ) := (lt_floor_iff (le_of_lt (rpow_pos_of_pos hNpos T))).mp hp1
    have h1 : Real.log ((N:ℝ)^T) < Real.log (p:ℝ) :=
      Real.log_lt_log (rpow_pos_of_pos hNpos T) hlt
    rwa [Real.log_rpow hNpos] at h1
  have htp_hi : Real.log (p:ℝ) / Real.log (N:ℝ) ≤ T' := by
    rw [div_le_iff₀ hlog]
    have h2 : (p:ℝ) ≤ (N:ℝ)^T' :=
      le_trans (by exact_mod_cast hp2) (Nat.floor_le (le_of_lt (rpow_pos_of_pos hNpos T')))
    have h1 : Real.log (p:ℝ) ≤ Real.log ((N:ℝ)^T') := Real.log_le_log hpR h2
    rwa [Real.log_rpow hNpos] at h1
  have htq_lo : U < Real.log (q:ℝ) / Real.log (N:ℝ) := by
    rw [lt_div_iff₀ hlog]
    have hlt : (N:ℝ)^U < (q:ℝ) := (lt_floor_iff (le_of_lt (rpow_pos_of_pos hNpos U))).mp hq1
    have h1 : Real.log ((N:ℝ)^U) < Real.log (q:ℝ) :=
      Real.log_lt_log (rpow_pos_of_pos hNpos U) hlt
    rwa [Real.log_rpow hNpos] at h1
  have htq_hi : Real.log (q:ℝ) / Real.log (N:ℝ) ≤ U' := by
    rw [div_le_iff₀ hlog]
    have h2 : (q:ℝ) ≤ (N:ℝ)^U' :=
      le_trans (by exact_mod_cast hq2) (Nat.floor_le (le_of_lt (rpow_pos_of_pos hNpos U')))
    have h1 : Real.log (q:ℝ) ≤ Real.log ((N:ℝ)^U') := Real.log_le_log hqR h2
    rwa [Real.log_rpow hNpos] at h1
  have hll : 0 ≤ Real.log (Real.log (N:ℝ)) := by
    refine Real.log_nonneg ?_
    rw [Real.le_log_iff_exp_le hNpos]
    calc Real.exp 1 ≤ 3 := by
          have h := Real.exp_one_lt_d9
          linarith
      _ ≤ (N:ℝ) := by exact_mod_cast hN3
  have hlev := lowerLevel_mul (B := B) hN2 hp0 hq0
  have htp : Real.log (p:ℝ) / Real.log (N:ℝ) = _ := rfl
  have hid : (1 / 2 - Real.log (p:ℝ) / Real.log (N:ℝ) - Real.log (q:ℝ) / Real.log (N:ℝ)) / kappa1
        - (B / kappa1) * (Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ)) - (1 / 2 - T - U) / kappa1
      = ((T - Real.log (p:ℝ) / Real.log (N:ℝ)) + (U - Real.log (q:ℝ) / Real.log (N:ℝ))) / kappa1
        - (B / kappa1) * (Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ)) := by
    field_simp
    ring
  rw [hlev, hid, sub_eq_add_neg]
  refine le_trans (abs_add_le _ _) ?_
  have h1 : |((T - Real.log (p:ℝ) / Real.log (N:ℝ)) + (U - Real.log (q:ℝ) / Real.log (N:ℝ))) / kappa1|
      ≤ ((T' - T) + (U' - U)) / kappa1 := by
    rw [abs_div, abs_of_pos hk1, div_le_div_iff_of_pos_right hk1]
    have ha : T - Real.log (p:ℝ) / Real.log (N:ℝ) ≤ 0 := by linarith [htp_lo]
    have hb : U - Real.log (q:ℝ) / Real.log (N:ℝ) ≤ 0 := by linarith [htq_lo]
    rw [abs_of_nonpos (by linarith : (T - Real.log (p:ℝ) / Real.log (N:ℝ))
      + (U - Real.log (q:ℝ) / Real.log (N:ℝ)) ≤ 0)]
    linarith [htp_hi, htq_hi]
  have h2 : |-(B / kappa1 * (Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ)))|
      = |B| * (Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ)) / kappa1 := by
    rw [abs_neg, abs_mul, abs_div, abs_of_pos hk1]
    rw [abs_of_nonneg (div_nonneg hll (le_of_lt hlog))]
    ring
  rw [h2]
  linarith [h1]


/-- The data carried by a member of the `Upsilon 5` pair domain. -/
private lemma lowerPairs5_mem {N : ℕ} {q : ℕ × ℕ} (hq : q ∈ lowerPairs5 N) :
    q.1.Prime ∧ q.2.Prime ∧ (N:ℝ)^kappa1 ≤ (q.1:ℝ) ∧ (q.1:ℝ) < (N:ℝ)^kappa2 ∧
      (N:ℝ)^kappa2 ≤ (q.2:ℝ) ∧
      (q.2:ℝ) < (N:ℝ)^(1 / 2 - 2 * kappa1) / (q.1 : ℝ) := by
  unfold lowerPairs5 Wu08Sum.P2 at hq
  simp only [Finset.mem_filter] at hq
  obtain ⟨-, p1, p2, -, -, h1, h2, h3, h4⟩ := hq
  exact ⟨p1, p2, h1, h2, h3, h4⟩



/-- On the `Upsilon 5` domain the totient is the product of the two shifted primes. -/
private lemma region_totient {N : ℕ} {q : ℕ × ℕ} (hq : q ∈ lowerPairs5 N) (hN : 2 ≤ N) :
    (Nat.totient (q.1 * q.2) : ℝ) = ((q.1:ℝ) - 1) * ((q.2:ℝ) - 1) := by
  obtain ⟨p1, p2, h1, h2, h3, h4⟩ := lowerPairs5_mem hq
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlt : (q.1:ℝ) < (q.2:ℝ) := lt_of_lt_of_le h2 h3
  have hne : q.1 ≠ q.2 := by
    intro h
    rw [h] at hlt
    linarith
  exact totient_mul_prime p1 p2 hne



/-- The pairs of the `Upsilon 5` domain that fail coprimality to `N` carry `o(1)` of the sum. -/
private lemma region_bad_mass (B : ℝ) (F : ℝ → ℝ) {K : ℝ} (hKnn : 0 ≤ K)
    (hK : ∀ (N p q : ℕ), p.Prime → q.Prime → (N:ℝ)^kappa1 ≤ (p:ℝ) → (N:ℝ)^kappa2 ≤ (q:ℝ) →
      (q:ℝ) < (N:ℝ)^(1 / 2 - 2 * kappa1) / (p:ℝ) → |F (lowerLevel B N (p*q))| ≤ K) :
    Tendsto (fun N : ℕ => ∑ q ∈ (lowerPairs5 N).filter
        (fun q => ¬ q.1.Coprime N ∨ ¬ q.2.Coprime N),
        F (lowerLevel B N (q.1*q.2)) / (Nat.totient (q.1*q.2) : ℝ)) atTop (𝓝 0) := by
  have hk1 : 0 < kappa1 := by norm_num [kappa1]
  have hk2 : 0 < kappa2 := by norm_num [kappa2]
  have hc : 0 < 1 / 2 - 3 * kappa1 := by norm_num [kappa1]
  -- the enclosing rectangle and its bad part
  have hmasslim : Tendsto (fun N : ℕ =>
      ∑ q ∈ (((Finset.Ioc ⌊(N:ℝ)^(kappa1/2)⌋₊ ⌊(N:ℝ)^kappa2⌋₊).filter
          (fun p => Nat.Prime p)) ×ˢ
        ((Finset.Ioc ⌊(N:ℝ)^(kappa2/2)⌋₊ ⌊(N:ℝ)^(1/2-3*kappa1)⌋₊).filter
          (fun p => Nat.Prime p))).filter
        (fun q : ℕ × ℕ => ¬ q.1.Coprime N ∨ ¬ q.2.Coprime N),
        (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹))) atTop (𝓝 0) :=
    bad_pair_mass_tendsto (kappa1/2) kappa2 (kappa2/2) (1/2-3*kappa1)
      (by positivity) (by norm_num [kappa1, kappa2]) (by positivity)
      (by norm_num [kappa1, kappa2])
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  refine squeeze_zero' (g := fun N : ℕ => K * (∑ q ∈ (((Finset.Ioc ⌊(N:ℝ)^(kappa1/2)⌋₊
        ⌊(N:ℝ)^kappa2⌋₊).filter (fun p => Nat.Prime p)) ×ˢ
      ((Finset.Ioc ⌊(N:ℝ)^(kappa2/2)⌋₊ ⌊(N:ℝ)^(1/2-3*kappa1)⌋₊).filter
        (fun p => Nat.Prime p))).filter
      (fun q : ℕ × ℕ => ¬ q.1.Coprime N ∨ ¬ q.2.Coprime N),
      (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)))) ?_ ?_
      (by simpa using hmasslim.const_mul K)
  · filter_upwards with N
    simp
  · filter_upwards [eventually_ge_atTop 5] with N hN5
    have hN2 : 2 ≤ N := by omega
    have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hN1 : (1:ℝ) < (N:ℝ) := by exact_mod_cast (show 1 < N by omega)
    simp only [Real.norm_eq_abs]
    have hpt : ∀ q ∈ (lowerPairs5 N).filter
        (fun q => ¬ q.1.Coprime N ∨ ¬ q.2.Coprime N),
        ‖F (lowerLevel B N (q.1*q.2)) / (Nat.totient (q.1*q.2) : ℝ)‖
          ≤ K * (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)) := by
      intro q hq
      have hqR : q ∈ lowerPairs5 N := (Finset.mem_filter.mp hq).1
      obtain ⟨p1, p2, h1, h2, h3, h4⟩ := lowerPairs5_mem hqR
      have hp2 : (2:ℝ) ≤ (q.1:ℝ) := by exact_mod_cast p1.two_le
      have hq2 : (2:ℝ) ≤ (q.2:ℝ) := by exact_mod_cast p2.two_le
      have hF := hK N q.1 q.2 p1 p2 h1 h3 h4
      rw [region_totient hqR hN2]
      have ha : (0:ℝ) < (q.1:ℝ) - 1 := by linarith
      have hb : (0:ℝ) < (q.2:ℝ) - 1 := by linarith
      have hw : (0:ℝ) < ((q.1:ℝ) - 1) * ((q.2:ℝ) - 1) := mul_pos ha hb
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hw]
      have h1 : |F (lowerLevel B N (q.1*q.2))| / (((q.1:ℝ) - 1) * ((q.2:ℝ) - 1))
          = |F (lowerLevel B N (q.1*q.2))| * (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)) := by
        field_simp
      rw [h1]
      exact mul_le_mul_of_nonneg_right hF
        (le_of_lt (mul_pos (inv_pos.mpr ha) (inv_pos.mpr hb)))
    -- the region's bad part sits inside the enclosing rectangle's bad part
    have hsub : ((lowerPairs5 N).filter
        (fun q => ¬ q.1.Coprime N ∨ ¬ q.2.Coprime N)) ⊆
        (((Finset.Ioc ⌊(N:ℝ)^(kappa1/2)⌋₊ ⌊(N:ℝ)^kappa2⌋₊).filter
            (fun p => Nat.Prime p)) ×ˢ
          ((Finset.Ioc ⌊(N:ℝ)^(kappa2/2)⌋₊ ⌊(N:ℝ)^(1/2-3*kappa1)⌋₊).filter
            (fun p => Nat.Prime p))).filter
          (fun q : ℕ × ℕ => ¬ q.1.Coprime N ∨ ¬ q.2.Coprime N) := by
      intro q hq
      obtain ⟨hqR, hbad⟩ := Finset.mem_filter.mp hq
      obtain ⟨p1, p2, h1, h2, h3, h4⟩ := lowerPairs5_mem hqR
      have hpR : (0:ℝ) < (q.1:ℝ) := by exact_mod_cast p1.pos
      have hqR' : (0:ℝ) < (q.2:ℝ) := by exact_mod_cast p2.pos
      have hκ1 : (N:ℝ)^(kappa1/2) < (N:ℝ)^kappa1 :=
        Real.rpow_lt_rpow_of_exponent_lt hN1 (by linarith)
      have hp_lo : ⌊(N:ℝ)^(kappa1/2)⌋₊ < q.1 :=
        (lt_floor_iff (le_of_lt (rpow_pos_of_pos hNpos _))).mpr (lt_of_lt_of_le hκ1 h1)
      have hp_hi : q.1 ≤ ⌊(N:ℝ)^kappa2⌋₊ := by
        by_contra hcon
        push Not at hcon
        have hle : (N:ℝ)^kappa2 < (q.1:ℝ) := by
          calc (N:ℝ)^kappa2 < (⌊(N:ℝ)^kappa2⌋₊ : ℝ) + 1 := by
                have := Nat.lt_floor_add_one ((N:ℝ)^kappa2)
                linarith
            _ ≤ (q.1:ℝ) := by exact_mod_cast hcon
        linarith [h2]
      have hκ2 : (N:ℝ)^(kappa2/2) < (N:ℝ)^kappa2 :=
        Real.rpow_lt_rpow_of_exponent_lt hN1 (by linarith)
      have hq_lo : ⌊(N:ℝ)^(kappa2/2)⌋₊ < q.2 :=
        (lt_floor_iff (le_of_lt (rpow_pos_of_pos hNpos _))).mpr (lt_of_lt_of_le hκ2 h3)
      have hq_hi : q.2 ≤ ⌊(N:ℝ)^(1/2-3*kappa1)⌋₊ := by
        have hc1 : (N:ℝ)^(1/2-2*kappa1) / (q.1:ℝ) ≤ (N:ℝ)^(1/2-2*kappa1) / (N:ℝ)^kappa1 :=
          div_le_div_of_nonneg_left (le_of_lt (rpow_pos_of_pos hNpos _))
            (rpow_pos_of_pos hNpos _) h1
        have hsplit : (N:ℝ)^(1/2-2*kappa1) / (N:ℝ)^kappa1 = (N:ℝ)^(1/2-3*kappa1) := by
          rw [← Real.rpow_sub hNpos]
          ring_nf
        have hqlt : (q.2:ℝ) < (N:ℝ)^(1/2-3*kappa1) := by
          rw [← hsplit]
          exact lt_of_lt_of_le h4 hc1
        by_contra hcon
        push Not at hcon
        have hle : (N:ℝ)^(1/2-3*kappa1) < (q.2:ℝ) := by
          calc (N:ℝ)^(1/2-3*kappa1) < (⌊(N:ℝ)^(1/2-3*kappa1)⌋₊ : ℝ) + 1 := by
                have := Nat.lt_floor_add_one ((N:ℝ)^(1/2-3*kappa1))
                linarith
            _ ≤ (q.2:ℝ) := by exact_mod_cast hcon
        linarith
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨hp_lo, hp_hi⟩, p1⟩, Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨hq_lo, hq_hi⟩, p2⟩⟩, hbad⟩
    calc |∑ q ∈ (lowerPairs5 N).filter
          (fun q => ¬ q.1.Coprime N ∨ ¬ q.2.Coprime N),
          F (lowerLevel B N (q.1*q.2)) / (Nat.totient (q.1*q.2) : ℝ)|
        ≤ ∑ q ∈ (lowerPairs5 N).filter
          (fun q => ¬ q.1.Coprime N ∨ ¬ q.2.Coprime N),
          |F (lowerLevel B N (q.1*q.2)) / (Nat.totient (q.1*q.2) : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ (lowerPairs5 N).filter
          (fun q => ¬ q.1.Coprime N ∨ ¬ q.2.Coprime N),
          K * (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)) := Finset.sum_le_sum hpt
      _ = K * ∑ q ∈ (lowerPairs5 N).filter
          (fun q => ¬ q.1.Coprime N ∨ ¬ q.2.Coprime N),
          (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)) := by rw [Finset.mul_sum]
      _ ≤ K * ∑ q ∈ (((Finset.Ioc ⌊(N:ℝ)^(kappa1/2)⌋₊ ⌊(N:ℝ)^kappa2⌋₊).filter
            (fun p => Nat.Prime p)) ×ˢ
          ((Finset.Ioc ⌊(N:ℝ)^(kappa2/2)⌋₊ ⌊(N:ℝ)^(1/2-3*kappa1)⌋₊).filter
            (fun p => Nat.Prime p))).filter
          (fun q : ℕ × ℕ => ¬ q.1.Coprime N ∨ ¬ q.2.Coprime N),
          (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq _ => by
              have hq' := (Finset.mem_filter.mp hq).1
              have h1 : Nat.Prime q.1 :=
                (Finset.mem_filter.mp (Finset.mem_product.mp hq').1).2
              have h2 : Nat.Prime q.2 :=
                (Finset.mem_filter.mp (Finset.mem_product.mp hq').2).2
              have h3 : (2:ℝ) ≤ (q.1:ℝ) := by exact_mod_cast h1.two_le
              have h4 : (2:ℝ) ≤ (q.2:ℝ) := by exact_mod_cast h2.two_le
              exact mul_nonneg (le_of_lt (inv_pos.mpr (by linarith)))
                (le_of_lt (inv_pos.mpr (by linarith))))) hKnn


/-- A prime-pair sum over a rectangle splits into the cells of two meshes. -/
private lemma pair_chain (T L : ℕ → ℕ) (hT : Monotone T) (hL : Monotone L)
    (mt mu : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ q ∈ ((Finset.Ioc (T 0) (T mt)).filter (fun p => Nat.Prime p)) ×ˢ
        ((Finset.Ioc (L 0) (L mu)).filter (fun p => Nat.Prime p)), f q.1 q.2)
      = ∑ i ∈ Finset.range mt, ∑ j ∈ Finset.range mu,
          ∑ q ∈ ((Finset.Ioc (T i) (T (i+1))).filter (fun p => Nat.Prime p)) ×ˢ
            ((Finset.Ioc (L j) (L (j+1))).filter (fun p => Nat.Prime p)), f q.1 q.2 := by
  rw [Finset.sum_product]
  rw [chain_filter (K := T) hT mt
    (f := fun p => (∑ q ∈ (Finset.Ioc (L 0) (L mu)).filter (fun p => Nat.Prime p),
      f p q : ℝ))]
  have key : ∀ i ∈ Finset.range mt,
      (∑ p ∈ (Finset.Ioc (T i) (T (i+1))).filter (fun p => Nat.Prime p),
          ∑ q ∈ (Finset.Ioc (L 0) (L mu)).filter (fun p => Nat.Prime p), f p q)
        = ∑ j ∈ Finset.range mu,
            ∑ q ∈ ((Finset.Ioc (T i) (T (i+1))).filter (fun p => Nat.Prime p)) ×ˢ
              ((Finset.Ioc (L j) (L (j+1))).filter (fun p => Nat.Prime p)), f q.1 q.2 := by
    intro i _
    have hB : ∀ p : ℕ,
        (∑ q ∈ (Finset.Ioc (L 0) (L mu)).filter (fun p => Nat.Prime p), f p q : ℝ)
          = ∑ j ∈ Finset.range mu,
              ∑ q ∈ (Finset.Ioc (L j) (L (j+1))).filter (fun p => Nat.Prime p), f p q :=
      fun p => chain_filter (K := L) hL mu (f := fun q => f p q)
    simp only [hB]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (Finset.sum_product ((Finset.Ioc (T i) (T (i+1))).filter (fun p => Nat.Prime p))
      ((Finset.Ioc (L j) (L (j+1))).filter (fun p => Nat.Prime p))
      (fun q : ℕ × ℕ => f q.1 q.2)).symm
  exact Finset.sum_congr rfl key


/-- A single prime row carries `o(1)` of the pair mass. -/
private lemma line_mass_tendsto (p0 : ℕ → ℕ) {ql qh : ℝ} (hl : 0 < ql) (hh : ql < qh)
    (hp : ∀ᶠ N : ℕ in atTop, (N:ℝ)^kappa1 ≤ 2 * (p0 N : ℝ))
    (hp2 : ∀ᶠ N : ℕ in atTop, 2 ≤ p0 N) :
    Tendsto (fun N : ℕ => ((p0 N : ℝ) - 1)⁻¹ *
        (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^ql⌋₊ ⌊(N:ℝ)^qh⌋₊).filter (fun p => Nat.Prime p),
          ((q:ℝ) - 1)⁻¹)) atTop (𝓝 0) := by
  have hk1 : 0 < kappa1 := by norm_num [kappa1]
  have hmass := cell_mass_tendsto ql qh hl hh
  have hL : 0 ≤ Real.log qh - Real.log ql := by
    have : Real.log ql ≤ Real.log qh := Real.log_le_log (by linarith) (le_of_lt hh)
    linarith
  have hbound : ∀ᶠ N : ℕ in atTop, (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^ql⌋₊ ⌊(N:ℝ)^qh⌋₊).filter
      (fun p => Nat.Prime p), ((q:ℝ) - 1)⁻¹) ≤ Real.log qh - Real.log ql + 1 :=
    (hmass.eventually (eventually_lt_nhds (lt_add_one _))).mono fun N h => le_of_lt h
  have hpow : Tendsto (fun N : ℕ => (N:ℝ)^kappa1) atTop atTop :=
    (tendsto_rpow_atTop hk1).comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun N : ℕ => (4 / (N:ℝ)^kappa1) * (Real.log qh - Real.log ql + 1))
      atTop (𝓝 0) := by
    have hinv : Tendsto (fun N : ℕ => ((N:ℝ)^kappa1)⁻¹) atTop (𝓝 0) :=
      hpow.inv_tendsto_atTop
    have h2 : Tendsto (fun N : ℕ => (4 * ((N:ℝ)^kappa1)⁻¹) *
        (Real.log qh - Real.log ql + 1)) atTop (𝓝 0) := by
      simpa using (hinv.const_mul 4).mul_const (Real.log qh - Real.log ql + 1)
    refine h2.congr' ?_
    filter_upwards with N
    rw [div_eq_mul_inv]
  refine squeeze_zero' (g := fun N : ℕ =>
    (4 / (N:ℝ)^kappa1) * (Real.log qh - Real.log ql + 1)) ?_ ?_ hsmall
  · filter_upwards [hp2, eventually_ge_atTop 1] with N hpN2 hN1
    have h1 : (0:ℝ) < (p0 N : ℝ) - 1 := by
      have : (2:ℝ) ≤ (p0 N : ℝ) := by exact_mod_cast hpN2
      linarith
    have h4 : (0:ℝ) ≤ ∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^ql⌋₊ ⌊(N:ℝ)^qh⌋₊).filter
        (fun p => Nat.Prime p), ((q:ℝ) - 1)⁻¹ := by
      refine Finset.sum_nonneg fun q hq => ?_
      have hq' : Nat.Prime q := (Finset.mem_filter.mp hq).2
      have h5 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq'.two_le
      exact le_of_lt (inv_pos.mpr (by linarith))
    exact mul_nonneg (le_of_lt (inv_pos.mpr h1)) h4
  · filter_upwards [hbound, hp, hp2, eventually_ge_atTop 2] with N hN hpN hpN2 hN2
    have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
    have h1 : (0:ℝ) < (N:ℝ)^kappa1 := rpow_pos_of_pos hNpos _
    have hpc : (2:ℝ) ≤ (p0 N : ℝ) := by exact_mod_cast hpN2
    have hden : (0:ℝ) < (p0 N : ℝ) - 1 := by linarith
    have h4 : (0:ℝ) ≤ ∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^ql⌋₊ ⌊(N:ℝ)^qh⌋₊).filter
        (fun p => Nat.Prime p), ((q:ℝ) - 1)⁻¹ := by
      refine Finset.sum_nonneg fun q hq => ?_
      have hq' : Nat.Prime q := (Finset.mem_filter.mp hq).2
      have h5 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq'.two_le
      exact le_of_lt (inv_pos.mpr (by linarith))
    have hstep1 : ((p0 N : ℝ) - 1)⁻¹ ≤ 2 / (p0 N : ℝ) := by
      rw [inv_eq_one_div, div_le_div_iff₀ hden (by linarith : (0:ℝ) < (p0 N : ℝ))]
      nlinarith
    have hstep2 : (2:ℝ) / (p0 N : ℝ) ≤ 4 / (N:ℝ)^kappa1 := by
      rw [div_le_div_iff₀ (by linarith : (0:ℝ) < (p0 N : ℝ)) h1]
      linarith
    calc ((p0 N : ℝ) - 1)⁻¹ *
          (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^ql⌋₊ ⌊(N:ℝ)^qh⌋₊).filter (fun p => Nat.Prime p),
            ((q:ℝ) - 1)⁻¹)
        ≤ (4 / (N:ℝ)^kappa1) *
          (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^ql⌋₊ ⌊(N:ℝ)^qh⌋₊).filter (fun p => Nat.Prime p),
            ((q:ℝ) - 1)⁻¹) :=
          mul_le_mul_of_nonneg_right (le_trans hstep1 hstep2) h4
      _ ≤ (4 / (N:ℝ)^kappa1) * (Real.log qh - Real.log ql + 1) :=
          mul_le_mul_of_nonneg_left hN (by positivity)


/-- A single prime column carries `o(1)` of the pair mass. -/
private lemma col_mass_tendsto (q0 : ℕ → ℕ) {pl ph : ℝ} (hl : 0 < pl) (hh : pl < ph)
    (hq : ∀ᶠ N : ℕ in atTop, (N:ℝ)^kappa2 ≤ 2 * (q0 N : ℝ))
    (hq2 : ∀ᶠ N : ℕ in atTop, 2 ≤ q0 N) :
    Tendsto (fun N : ℕ =>
        (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^pl⌋₊ ⌊(N:ℝ)^ph⌋₊).filter (fun p => Nat.Prime p),
          ((p:ℝ) - 1)⁻¹) * ((q0 N : ℝ) - 1)⁻¹) atTop (𝓝 0) := by
  have hk2 : 0 < kappa2 := by norm_num [kappa2]
  have hmass := cell_mass_tendsto pl ph hl hh
  have hL : 0 ≤ Real.log ph - Real.log pl := by
    have : Real.log pl ≤ Real.log ph := Real.log_le_log (by linarith) (le_of_lt hh)
    linarith
  have hbound : ∀ᶠ N : ℕ in atTop, (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^pl⌋₊ ⌊(N:ℝ)^ph⌋₊).filter
      (fun p => Nat.Prime p), ((p:ℝ) - 1)⁻¹) ≤ Real.log ph - Real.log pl + 1 :=
    (hmass.eventually (eventually_lt_nhds (lt_add_one _))).mono fun N h => le_of_lt h
  have hpow : Tendsto (fun N : ℕ => (N:ℝ)^kappa2) atTop atTop :=
    (tendsto_rpow_atTop hk2).comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun N : ℕ => (Real.log ph - Real.log pl + 1) *
      (4 / (N:ℝ)^kappa2)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun N : ℕ => ((N:ℝ)^kappa2)⁻¹) atTop (𝓝 0) :=
      hpow.inv_tendsto_atTop
    have h2 : Tendsto (fun N : ℕ => (Real.log ph - Real.log pl + 1) *
        (4 * ((N:ℝ)^kappa2)⁻¹)) atTop (𝓝 0) := by
      simpa using (hinv.const_mul 4).const_mul (Real.log ph - Real.log pl + 1)
    refine h2.congr' ?_
    filter_upwards with N
    rw [div_eq_mul_inv]
  refine squeeze_zero' (g := fun N : ℕ =>
    (Real.log ph - Real.log pl + 1) * (4 / (N:ℝ)^kappa2)) ?_ ?_ hsmall
  · filter_upwards [hq2] with N hqN2
    have h1 : (0:ℝ) < (q0 N : ℝ) - 1 := by
      have : (2:ℝ) ≤ (q0 N : ℝ) := by exact_mod_cast hqN2
      linarith
    have h4 : (0:ℝ) ≤ ∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^pl⌋₊ ⌊(N:ℝ)^ph⌋₊).filter
        (fun p => Nat.Prime p), ((p:ℝ) - 1)⁻¹ := by
      refine Finset.sum_nonneg fun q hq' => ?_
      have hq'' : Nat.Prime q := (Finset.mem_filter.mp hq').2
      have h5 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq''.two_le
      exact le_of_lt (inv_pos.mpr (by linarith))
    exact mul_nonneg h4 (le_of_lt (inv_pos.mpr h1))
  · filter_upwards [hbound, hq, hq2, eventually_ge_atTop 2] with N hN hqN hqN2 hN2
    have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
    have h1 : (0:ℝ) < (N:ℝ)^kappa2 := rpow_pos_of_pos hNpos _
    have hqc : (2:ℝ) ≤ (q0 N : ℝ) := by exact_mod_cast hqN2
    have hden : (0:ℝ) < (q0 N : ℝ) - 1 := by linarith
    have h4 : (0:ℝ) ≤ ∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^pl⌋₊ ⌊(N:ℝ)^ph⌋₊).filter
        (fun p => Nat.Prime p), ((p:ℝ) - 1)⁻¹ := by
      refine Finset.sum_nonneg fun q hq' => ?_
      have hq'' : Nat.Prime q := (Finset.mem_filter.mp hq').2
      have h5 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq''.two_le
      exact le_of_lt (inv_pos.mpr (by linarith))
    have hstep1 : ((q0 N : ℝ) - 1)⁻¹ ≤ 2 / (q0 N : ℝ) := by
      rw [inv_eq_one_div, div_le_div_iff₀ hden (by linarith : (0:ℝ) < (q0 N : ℝ))]
      nlinarith
    have hstep2 : (2:ℝ) / (q0 N : ℝ) ≤ 4 / (N:ℝ)^kappa2 := by
      rw [div_le_div_iff₀ (by linarith : (0:ℝ) < (q0 N : ℝ)) h1]
      linarith
    calc (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^pl⌋₊ ⌊(N:ℝ)^ph⌋₊).filter (fun p => Nat.Prime p),
          ((p:ℝ) - 1)⁻¹) * ((q0 N : ℝ) - 1)⁻¹
        ≤ (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^pl⌋₊ ⌊(N:ℝ)^ph⌋₊).filter (fun p => Nat.Prime p),
          ((p:ℝ) - 1)⁻¹) * (4 / (N:ℝ)^kappa2) :=
          mul_le_mul_of_nonneg_left (le_trans hstep1 hstep2) h4
      _ ≤ (Real.log ph - Real.log pl + 1) * (4 / (N:ℝ)^kappa2) :=
          mul_le_mul_of_nonneg_right hN (by positivity)



/-- On a region rectangle the level stays in the compact range of `F` and close to the
corner value, so a continuity modulus transfers to the pair weights. -/
private lemma cell_osc (B : ℝ) (F : ℝ → ℝ) (T T' U U' : ℝ) (hTlo : kappa1 ≤ T)
    (hT' : T ≤ T') (hT'k : T' ≤ kappa2) (hUlo : kappa2 ≤ U) (hU' : U ≤ U')
    (hT'U' : T' + U' ≤ 1 / 2 - 2 * kappa1)
    {η ε : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 3 / 10)
    (hmod : ∀ u ∈ Set.Icc (3/2) 4, ∀ v ∈ Set.Icc (3/2) 4, |u - v| ≤ η → |F u - F v| ≤ ε)
    (hmesh : ((T' - T) + (U' - U)) / kappa1 ≤ η / 2) :
    ∀ᶠ N : ℕ in atTop, ∀ p q : ℕ, ⌊(N:ℝ)^T⌋₊ < p → p ≤ ⌊(N:ℝ)^T'⌋₊ →
      ⌊(N:ℝ)^U⌋₊ < q → q ≤ ⌊(N:ℝ)^U'⌋₊ →
      |F (lowerLevel B N (p * q)) - F ((1 / 2 - T - U) / kappa1)| ≤ ε := by
  have hk1 : 0 < kappa1 := by norm_num [kappa1]
  have hk2 : 0 < kappa2 := by norm_num [kappa2]
  have hTpos : 0 < T := lt_of_lt_of_le hk1 hTlo
  have hUpos : 0 < U := lt_of_lt_of_le hk2 hUlo
  -- the corner value lies in the compact range
  have hs2 : 2 ≤ (1 / 2 - T - U) / kappa1 := by
    rw [le_div_iff₀ hk1]
    have h1 : U ≤ 1 / 2 - 2 * kappa1 - T := by linarith
    linarith
  have hk1v : kappa1 = 1 / 12 := by norm_num [kappa1]
  have hk2v : kappa2 = 29 / 250 := by norm_num [kappa2]
  have hs4 : (1 / 2 - T - U) / kappa1 ≤ 37 / 10 := by
    rw [div_le_iff₀ hk1]
    have h1 : (1:ℝ)/2 - T - U ≤ 1/2 - kappa1 - kappa2 := by linarith
    have h2 : (1/2 - kappa1 - kappa2 : ℝ) ≤ 37/10 * kappa1 := by
      rw [hk1v, hk2v]
      norm_num
    linarith
  -- the logarithmic loss vanishes
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h2 : Tendsto (fun N : ℕ => Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ))
      atTop (𝓝 0) := h1.comp hlog
  have h3 : Tendsto (fun N : ℕ =>
      |B| * (Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ)) / kappa1) atTop (𝓝 0) := by
    have h4 := h2.const_mul (|B| / kappa1)
    have h5 : Tendsto (fun N : ℕ =>
        |B| * (Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ)) / kappa1) atTop (𝓝 (|B| / kappa1 * 0)) := by
      refine h4.congr' ?_
      filter_upwards with N
      rw [div_mul_eq_mul_div]
    simpa using h5
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 h3 (η / 2) (by linarith)
  filter_upwards [level_close B T T' U U' hTpos hT' hUpos hU',
    eventually_ge_atTop (max N0 3)] with N hlev hN3
  intro p q hp1 hp2 hq1 hq2
  have hBsmall : |B| * (Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ)) / kappa1 ≤ η / 2 := by
    have h := hN0 N (le_trans (le_max_left _ _) hN3)
    rw [Real.dist_eq, sub_zero] at h
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) h)
  have hclose := hlev p q hp1 hp2 hq1 hq2
  have hd : |lowerLevel B N (p * q) - (1 / 2 - T - U) / kappa1| ≤ η := by linarith [hclose, hBsmall, hmesh]
  have hlev2 : lowerLevel B N (p * q) ∈ Set.Icc (3/2) 4 := by
    obtain ⟨h1, h2⟩ := abs_le.mp hd
    exact ⟨by linarith, by linarith⟩
  have hsI : (1 / 2 - T - U) / kappa1 ∈ Set.Icc (3/2) 4 := ⟨by linarith, by linarith⟩
  exact hmod _ hlev2 _ hsI hd


/-! ### The pair domain as an explicit rectangle region

The vanishing of the finite logarithmic loss and the coprimality to `N` are separated from the
region bookkeeping: `lowerPairs5` is by definition the subset of `range N × range N` cut out by
four real inequalities together with the coprimality conditions. Writing it in that shape is what
lets the meshes of the two logarithms act on it. -/

/-- Membership in the `Upsilon 5` domain, with the conditions in the order used by the meshes. -/
private lemma lowerPairs5_eq_region (N : ℕ) :
    lowerPairs5 N =
      (((Finset.range N ×ˢ Finset.range N).filter
        (fun q : ℕ × ℕ => q.1.Prime ∧ q.2.Prime ∧ q.1.Coprime N ∧ q.2.Coprime N)).filter
        (fun q : ℕ × ℕ =>
          (N : ℝ) ^ kappa1 ≤ (q.1 : ℝ) ∧ (q.1 : ℝ) < (N : ℝ) ^ kappa2 ∧
            (N : ℝ) ^ kappa2 ≤ (q.2 : ℝ) ∧
            (q.2 : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / (q.1 : ℝ))) := by
  ext q
  simp only [lowerPairs5, Wu08Sum.P2, Finset.mem_filter, Finset.mem_product]
  tauto

/-- The finite sum over the explicit region. -/
private lemma lowerSum5_eq_region_sum (f : ℝ → ℝ) (B : ℝ) (N : ℕ) :
    lowerSum5 f B N =
      ∑ q ∈ (((Finset.range N ×ˢ Finset.range N).filter
        (fun q : ℕ × ℕ => q.1.Prime ∧ q.2.Prime ∧ q.1.Coprime N ∧ q.2.Coprime N)).filter
        (fun q : ℕ × ℕ =>
          (N : ℝ) ^ kappa1 ≤ (q.1 : ℝ) ∧ (q.1 : ℝ) < (N : ℝ) ^ kappa2 ∧
            (N : ℝ) ^ kappa2 ≤ (q.2 : ℝ) ∧
            (q.2 : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / (q.1 : ℝ))),
        f (lowerLevel B N (q.1 * q.2)) / (Nat.totient (q.1 * q.2) : ℝ) := by
  rw [lowerSum5, lowerPairs5_eq_region]

/-- A sum over a filtered product splits into a filtered `p` sum and, inside it, a filtered
`q` sum, whenever the predicate separates into a `p` part and a `p`,`q` part. -/
private lemma sum_filter_product_split {s : Finset ℕ} (P1 : ℕ → Prop) (P2 : ℕ → ℕ → Prop)
    [DecidablePred P1] [∀ p, DecidablePred (P2 p)] (g : ℕ → ℕ → ℝ) :
    (∑ x ∈ (s ×ˢ s).filter (fun x : ℕ × ℕ => P1 x.1 ∧ P2 x.1 x.2), g x.1 x.2)
      = ∑ p ∈ s.filter P1, ∑ q ∈ s.filter (P2 p), g p q := by
  simp only [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun p hp => ?_
  by_cases h : P1 p
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun q _ => ?_
    exact if_congr (by tauto) rfl rfl
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun q _ => ?_
    exact if_neg (by tauto)

/-- The finite sum as an iterated sum over the `p` band and, for each `p`, the `q` band. -/
private lemma lowerSum5_eq_nested (f : ℝ → ℝ) (B : ℝ) (N : ℕ) :
    lowerSum5 f B N =
      ∑ p ∈ (Finset.range N).filter (fun p : ℕ => p.Prime ∧ p.Coprime N ∧
          (N : ℝ) ^ kappa1 ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ kappa2),
        ∑ q ∈ (Finset.range N).filter (fun q : ℕ => q.Prime ∧ q.Coprime N ∧
            (N : ℝ) ^ kappa2 ≤ (q : ℝ) ∧
            (q : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / (p : ℝ)),
          f (lowerLevel B N (p * q)) / (Nat.totient (p * q) : ℝ) := by
  rw [lowerSum5_eq_region_sum, Finset.filter_filter]
  have hcongr : ((Finset.range N ×ˢ Finset.range N).filter (fun q : ℕ × ℕ =>
        (q.1.Prime ∧ q.2.Prime ∧ q.1.Coprime N ∧ q.2.Coprime N) ∧
        ((N : ℝ) ^ kappa1 ≤ (q.1 : ℝ) ∧ (q.1 : ℝ) < (N : ℝ) ^ kappa2 ∧
          (N : ℝ) ^ kappa2 ≤ (q.2 : ℝ) ∧
          (q.2 : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / (q.1 : ℝ))))
      = (Finset.range N ×ˢ Finset.range N).filter (fun x : ℕ × ℕ =>
        (x.1.Prime ∧ x.1.Coprime N ∧ (N : ℝ) ^ kappa1 ≤ (x.1 : ℝ) ∧
            (x.1 : ℝ) < (N : ℝ) ^ kappa2) ∧
          (x.2.Prime ∧ x.2.Coprime N ∧ (N : ℝ) ^ kappa2 ≤ (x.2 : ℝ) ∧
            (x.2 : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / (x.1 : ℝ))) :=
    Finset.filter_congr fun x _ => by tauto
  rw [hcongr]
  exact sum_filter_product_split
    (P1 := fun p : ℕ => p.Prime ∧ p.Coprime N ∧ (N : ℝ) ^ kappa1 ≤ (p : ℝ) ∧
      (p : ℝ) < (N : ℝ) ^ kappa2)
    (P2 := fun p q : ℕ => q.Prime ∧ q.Coprime N ∧ (N : ℝ) ^ kappa2 ≤ (q : ℝ) ∧
      (q : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / (p : ℝ))
    (g := fun p q => f (lowerLevel B N (p * q)) / (Nat.totient (p * q) : ℝ))

/-! ### Boundary price of the real cuts

The `Upsilon 5` region is cut out by the real inequalities `a ≤ q < u`, while the mesh lemmas of
this file sum over the integer boxes `Ioc ⌊a⌋ ⌊u⌋`. The two sums differ by at most the two
boundary integers, which is where the boundary error of the mesh argument enters. -/

/-- A real band `a ≤ q < u` and the integer box `⌊a⌋ < q ≤ ⌊u⌋` differ by at most the two
boundary integers. -/
private lemma range_filter_band_diff {N : ℕ} {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u)
    (hN : ⌊u⌋₊ < N) (A : ℕ → Prop) [DecidablePred A] (w : ℕ → ℝ) :
    |(∑ q ∈ (Finset.range N).filter (fun q => A q ∧ a ≤ (q : ℝ) ∧ (q : ℝ) < u), w q)
        - (∑ q ∈ (Finset.Ioc ⌊a⌋₊ ⌊u⌋₊).filter A, w q)|
      ≤ |w ⌊a⌋₊| + |w ⌊u⌋₊| := by
  classical
  set X : Finset ℕ := (Finset.range N).filter (fun q => A q ∧ a ≤ (q : ℝ) ∧ (q : ℝ) < u)
  set Y : Finset ℕ := (Finset.Ioc ⌊a⌋₊ ⌊u⌋₊).filter A
  have hXY : X \ Y ⊆ {⌊a⌋₊} := by
    intro q hq
    obtain ⟨hqX, hqY⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨-, hA, haq, hqu⟩ := Finset.mem_filter.mp hqX
    have hqle : q ≤ ⌊a⌋₊ := by
      by_contra hcon
      rw [not_le] at hcon
      exact hqY (Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨hcon, Nat.le_floor (le_of_lt hqu)⟩, hA⟩)
    have hfloor : (⌊a⌋₊ : ℝ) ≤ (q : ℝ) := le_trans (Nat.floor_le ha) haq
    have hcast : (q : ℝ) ≤ (⌊a⌋₊ : ℝ) := by exact_mod_cast hqle
    exact Finset.mem_singleton.mpr (by exact_mod_cast le_antisymm hcast hfloor)
  have hYX : Y \ X ⊆ {⌊u⌋₊} := by
    intro q hq
    obtain ⟨hqY, hqX⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨hIoc, hA⟩ := Finset.mem_filter.mp hqY
    obtain ⟨hlt, hle⟩ := Finset.mem_Ioc.mp hIoc
    have hqN : q < N := lt_of_le_of_lt hle hN
    have haq : a ≤ (q : ℝ) := le_of_lt ((lt_floor_iff ha).mp hlt)
    have hqnu : ¬ ((q : ℝ) < u) := by
      intro hltu
      exact hqX (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hqN, hA, haq, hltu⟩)
    have hcast : (q : ℝ) ≤ (⌊u⌋₊ : ℝ) := by exact_mod_cast hle
    have hfloor : (⌊u⌋₊ : ℝ) ≤ (q : ℝ) := le_trans (Nat.floor_le hu) (le_of_not_gt hqnu)
    exact Finset.mem_singleton.mpr (by exact_mod_cast le_antisymm hcast hfloor)
  have hbound : ∀ (S : Finset ℕ) (c : ℕ), S ⊆ {c} → |∑ q ∈ S, w q| ≤ |w c| := by
    intro S c hS
    rcases Finset.eq_empty_or_nonempty S with h | ⟨q, hq⟩
    · rw [h]; simp
    · have hSc : S = {c} := by
        ext r
        simp only [Finset.mem_singleton]
        constructor
        · exact fun hr => Finset.mem_singleton.mp (hS hr)
        · intro hr
          have hqc : q = c := Finset.mem_singleton.mp (hS hq)
          rw [hr, ← hqc]
          exact hq
      rw [hSc, Finset.sum_singleton]
  have hmain := Finset.sum_sdiff_sub_sum_sdiff (s₁ := Y) (s₂ := X) (f := w)
  rw [← hmain]
  calc |(∑ q ∈ X \ Y, w q) - ∑ q ∈ Y \ X, w q|
      = |(∑ q ∈ X \ Y, w q) + -(∑ q ∈ Y \ X, w q)| := by rw [sub_eq_add_neg]
    _ ≤ |∑ q ∈ X \ Y, w q| + |-(∑ q ∈ Y \ X, w q)| := abs_add_le _ _
    _ = |∑ q ∈ X \ Y, w q| + |∑ q ∈ Y \ X, w q| := by rw [abs_neg]
    _ ≤ |w ⌊a⌋₊| + |w ⌊u⌋₊| := add_le_add (hbound _ _ hXY) (hbound _ _ hYX)



/-! ### The logarithmic rectangle rule

The final passage in `lowerSum5_tendsto` is from a mesh sum `∑ᵢ log (Tᵢ₊₁/Tᵢ) · G (ξᵢ)` to the
integral `∫ G u / u`, with `G` continuous.  The two lemmas below are that passage: the cell
error is exactly the mean oscillation of `G` against the logarithmic weight, and the errors
add up to the integral of `|G u - G (ξᵢ)| / u` cell by cell. -/

/-- The logarithmic rectangle rule on one cell, measured against the true integral. -/
private lemma cell_rule_le {a b v : ℝ} (ha : 0 < a) (hab : a ≤ b) (G : ℝ → ℝ)
    (hG : ContinuousOn G (Set.uIcc a b)) :
    |Real.log (b / a) * G v - (∫ u in a..b, G u / u)|
      ≤ ∫ u in a..b, |G u - G v| / u := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hmem : ∀ u ∈ Set.uIcc a b, 0 < u := by
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    linarith [hu.1]
  have hcont : ContinuousOn (fun u : ℝ => G u / u) (Set.uIcc a b) :=
    hG.div continuousOn_id (fun u hu => ne_of_gt (hmem u hu))
  have hone : (∫ u in a..b, G v / u) = Real.log (b / a) * G v := by
    rw [show (fun u : ℝ => G v / u) = (fun u : ℝ => G v * u⁻¹) from rfl,
      intervalIntegral.integral_const_mul, integral_inv_of_pos ha hb, mul_comm]
  have hcont3 : ContinuousOn (fun u : ℝ => (G v - G u) / u) (Set.uIcc a b) :=
    (continuousOn_const.sub hG).div continuousOn_id (fun u hu => ne_of_gt (hmem u hu))
  have hsplit : (∫ u in a..b, G v / u)
      = (∫ u in a..b, (G v - G u) / u) + (∫ u in a..b, G u / u) := by
    rw [← intervalIntegral.integral_add hcont3.intervalIntegrable hcont.intervalIntegrable]
    exact intervalIntegral.integral_congr fun u _ => by ring
  have hval : Real.log (b / a) * G v - (∫ u in a..b, G u / u)
      = ∫ u in a..b, (G v - G u) / u := by
    rw [← hone, hsplit]
    ring
  rw [hval]
  refine (intervalIntegral.abs_integral_le_integral_abs hab).trans (le_of_eq ?_)
  exact intervalIntegral.integral_congr fun u hu => by
    rw [abs_div, abs_of_pos (hmem u hu), abs_sub_comm]

/-- The logarithmic rectangle sum over a uniform mesh differs from `∫ G u / u` by at most the
summed cell oscillation. -/
private lemma riemann_log_error_le (s t h : ℝ) (hs : 0 < s) (hh : 0 < h) (m : ℕ)
    (hmh : (m : ℝ) * h = t - s) (G : ℝ → ℝ) (hG : ContinuousOn G (Set.Icc s t))
    (ξ : ℕ → ℝ)
    (hξ : ∀ j ∈ Finset.range m, ξ j ∈ Set.Icc (s + (j:ℝ)*h) (s + ((j:ℝ)+1)*h)) :
    |(∑ j ∈ Finset.range m,
        Real.log ((s + ((j:ℝ)+1)*h) / (s + (j:ℝ)*h)) * G (ξ j))
      - (∫ u in s..t, G u / u)|
      ≤ ∑ j ∈ Finset.range m,
          ∫ u in (s + (j:ℝ)*h)..(s + ((j:ℝ)+1)*h), |G u - G (ξ j)| / u := by
  have hm : (0 : ℝ) ≤ (m : ℝ) * h := by positivity
  have hst : s ≤ t := by linarith
  have key : ∀ j ∈ Finset.range m,
      |Real.log ((s + ((j:ℝ)+1)*h) / (s + (j:ℝ)*h)) * G (ξ j)
        - (∫ u in (s + (j:ℝ)*h)..(s + ((j:ℝ)+1)*h), G u / u)|
      ≤ ∫ u in (s + (j:ℝ)*h)..(s + ((j:ℝ)+1)*h), |G u - G (ξ j)| / u := by
    intro j hj
    have hjm : (j : ℝ) + 1 ≤ (m : ℝ) := by
      have hjm' : j + 1 ≤ m := by
        have := Finset.mem_range.mp hj
        omega
      exact_mod_cast hjm'
    have hjnn : (0 : ℝ) ≤ (j : ℝ) * h := by positivity
    have ha : 0 < s + (j:ℝ)*h := by linarith
    have hle : s + (j:ℝ)*h ≤ s + ((j:ℝ)+1)*h := by nlinarith
    have hbt : s + ((j:ℝ)+1)*h ≤ t := by
      have h1 : ((j:ℝ)+1) * h ≤ (m:ℝ) * h := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hh)
        linarith
      nlinarith
    have hsl : s ≤ s + (j:ℝ)*h := by nlinarith
    have hmono : Set.uIcc (s + (j:ℝ)*h) (s + ((j:ℝ)+1)*h) ⊆ Set.Icc s t := fun u hu => by
      rw [Set.uIcc_of_le hle] at hu
      exact ⟨le_trans hsl hu.1, le_trans hu.2 hbt⟩
    exact cell_rule_le ha hle G (hG.mono hmono)
  have hsplit := integral_chain_cont s t h hs hh m hmh G hG
  have hre : (∑ j ∈ Finset.range m,
        Real.log ((s + ((j:ℝ)+1)*h) / (s + (j:ℝ)*h)) * G (ξ j))
      - (∫ u in s..t, G u / u)
      = ∑ j ∈ Finset.range m,
          (Real.log ((s + ((j:ℝ)+1)*h) / (s + (j:ℝ)*h)) * G (ξ j)
            - (∫ u in (s + (j:ℝ)*h)..(s + ((j:ℝ)+1)*h), G u / u)) := by
    rw [hsplit, Finset.sum_sub_distrib]
  rw [hre]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum key)

/-- The logarithmic cell widths of a uniform mesh on `[s, t]` add up to `log (t / s)`. -/
private lemma sum_log_ratio (s t h : ℝ) (hs : 0 < s) (hh : 0 < h) (m : ℕ)
    (hmh : (m : ℝ) * h = t - s) :
    ∑ j ∈ Finset.range m, Real.log ((s + ((j:ℝ)+1)*h) / (s + (j:ℝ)*h))
      = Real.log (t / s) := by
  have hpos : ∀ j : ℕ, (0 : ℝ) < s + (j:ℝ)*h := by
    intro j
    have h1 : (0:ℝ) ≤ (j:ℝ)*h := by positivity
    linarith
  have hterm : ∀ j : ℕ, Real.log ((s + ((j:ℝ)+1)*h) / (s + (j:ℝ)*h))
      = Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h) := by
    intro j
    have hpos1 : (0:ℝ) < s + ((j:ℝ)+1)*h := by
      have h := hpos (j + 1)
      simpa only [Nat.cast_add, Nat.cast_one] using h
    exact Real.log_div (ne_of_gt hpos1) (ne_of_gt (hpos j))
  have htel : ∑ j ∈ Finset.range m,
      (Real.log (s + ((j:ℝ)+1)*h) - Real.log (s + (j:ℝ)*h))
      = Real.log (s + (m:ℝ)*h) - Real.log s := by
    have h := Finset.sum_range_sub (fun j : ℕ => Real.log (s + (j:ℝ)*h)) m
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero, zero_mul, add_zero]
      using h
  have ht : (0:ℝ) < t := by
    have h1 : (0:ℝ) ≤ (m:ℝ)*h := by positivity
    linarith
  rw [Finset.sum_congr rfl (fun j _ => hterm j), htel, hmh,
    show s + (t - s) = t by ring]
  exact (Real.log_div (ne_of_gt ht) (ne_of_gt hs)).symm

/-- A fine enough uniform mesh makes the logarithmic rectangle sum `ε`-close to `∫ G u / u`
for `G` continuous on `[s, t]`. -/
private lemma riemann_log_close (s t : ℝ) (hs : 0 < s) (hst : s < t) (G : ℝ → ℝ)
    (hG : ContinuousOn G (Set.Icc s t)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (h : ℝ) (m : ℕ), 0 < h → h ≤ δ → (m : ℝ) * h = t - s →
      ∀ ξ : ℕ → ℝ,
      (∀ j ∈ Finset.range m, ξ j ∈ Set.Icc (s + (j:ℝ)*h) (s + ((j:ℝ)+1)*h)) →
      |(∑ j ∈ Finset.range m,
          Real.log ((s + ((j:ℝ)+1)*h) / (s + (j:ℝ)*h)) * G (ξ j))
        - (∫ u in s..t, G u / u)| ≤ ε := by
  have ht : 0 < t := lt_trans hs hst
  have hlogd : 0 < Real.log t - Real.log s := by
    rw [← Real.log_div (ne_of_gt ht) (ne_of_gt hs)]
    exact Real.log_pos (by rw [lt_div_iff₀ hs]; linarith)
  have hε' : 0 < ε / (Real.log t - Real.log s) := div_pos hε hlogd
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff_le.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hG) (ε / (Real.log t - Real.log s)) hε'
  refine ⟨δ, hδ0, fun h m hh hhδ hmh ξ hξ => ?_⟩
  have hcell : ∀ j ∈ Finset.range m,
      (∫ u in (s + (j:ℝ)*h)..(s + ((j:ℝ)+1)*h), |G u - G (ξ j)| / u)
        ≤ (ε / (Real.log t - Real.log s)) *
            Real.log ((s + ((j:ℝ)+1)*h) / (s + (j:ℝ)*h)) := by
    intro j hj
    have hjm : (j : ℝ) + 1 ≤ (m : ℝ) := by
      have hjm' : j + 1 ≤ m := by
        have := Finset.mem_range.mp hj
        omega
      exact_mod_cast hjm'
    have hjnn : (0:ℝ) ≤ (j:ℝ)*h := by positivity
    have hA : 0 < s + (j:ℝ)*h := by linarith
    have hB : 0 < s + ((j:ℝ)+1)*h := by
      have h1 : (0:ℝ) < ((j:ℝ)+1)*h := by
        have h2 : (0:ℝ) < (j:ℝ)+1 := by positivity
        exact mul_pos h2 hh
      linarith
    have hle : s + (j:ℝ)*h ≤ s + ((j:ℝ)+1)*h := by nlinarith
    have hbt : s + ((j:ℝ)+1)*h ≤ t := by
      have h1 : ((j:ℝ)+1) * h ≤ (m:ℝ) * h := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hh)
        linarith
      nlinarith
    have hsl : s ≤ s + (j:ℝ)*h := by linarith
    have hmem : ∀ u ∈ Set.Icc (s + (j:ℝ)*h) (s + ((j:ℝ)+1)*h), 0 < u := by
      intro u hu
      linarith [hu.1]
    have hbound : ∀ u ∈ Set.Icc (s + (j:ℝ)*h) (s + ((j:ℝ)+1)*h),
        |G u - G (ξ j)| / u ≤ (ε / (Real.log t - Real.log s)) / u := by
      intro u hu
      have hu1 : u ∈ Set.Icc s t := ⟨le_trans hsl hu.1, le_trans hu.2 hbt⟩
      have hmξ := hξ j hj
      have hξ1 : ξ j ∈ Set.Icc s t := ⟨le_trans hsl hmξ.1, le_trans hmξ.2 hbt⟩
      have hdist : dist u (ξ j) ≤ δ := by
        rw [Real.dist_eq]
        have h1 : |u - ξ j| ≤ h := by
          rw [abs_le]
          constructor
          · linarith [hu.1, hmξ.2]
          · linarith [hu.2, hmξ.1]
        linarith
      have hcl := hδ u hu1 (ξ j) hξ1 hdist
      rw [Real.dist_eq] at hcl
      exact div_le_div_of_nonneg_right hcl (le_of_lt (hmem u hu))
    have hmono : Set.uIcc (s + (j:ℝ)*h) (s + ((j:ℝ)+1)*h) ⊆ Set.Icc s t := by
      rw [Set.uIcc_of_le hle]
      exact Set.Icc_subset_Icc hsl hbt
    have hcont1 : ContinuousOn (fun u : ℝ => |G u - G (ξ j)| / u)
        (Set.uIcc (s + (j:ℝ)*h) (s + ((j:ℝ)+1)*h)) := by
      refine ((hG.mono hmono).sub continuousOn_const).abs.div continuousOn_id ?_
      intro u hu
      rw [Set.uIcc_of_le hle] at hu
      exact ne_of_gt (hmem u hu)
    have hcont2 : ContinuousOn (fun u : ℝ => (ε / (Real.log t - Real.log s)) / u)
        (Set.uIcc (s + (j:ℝ)*h) (s + ((j:ℝ)+1)*h)) := by
      refine continuousOn_const.div continuousOn_id ?_
      intro u hu
      rw [Set.uIcc_of_le hle] at hu
      exact ne_of_gt (hmem u hu)
    have hnn : 0 ≤ ∫ u in (s + (j:ℝ)*h)..(s + ((j:ℝ)+1)*h),
        ((ε / (Real.log t - Real.log s)) / u - |G u - G (ξ j)| / u) := by
      refine intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) hle ?_
      intro u hu
      linarith [hbound u hu]
    have hsub := intervalIntegral.integral_sub (μ := MeasureTheory.volume) hcont2.intervalIntegrable
      hcont1.intervalIntegrable
    have hone : (∫ u in (s + (j:ℝ)*h)..(s + ((j:ℝ)+1)*h),
        (ε / (Real.log t - Real.log s)) / u)
        = (ε / (Real.log t - Real.log s)) *
            Real.log ((s + ((j:ℝ)+1)*h) / (s + (j:ℝ)*h)) := by
      rw [show (fun u : ℝ => (ε / (Real.log t - Real.log s)) / u)
          = (fun u : ℝ => (ε / (Real.log t - Real.log s)) * u⁻¹) from rfl,
        intervalIntegral.integral_const_mul, integral_inv_of_pos hA hB]
    rw [hsub, hone] at hnn
    linarith [hnn, hone]
  have hD : Real.log t - Real.log s ≠ 0 := ne_of_gt hlogd
  have hval : (ε / (Real.log t - Real.log s)) * (Real.log t - Real.log s) = ε :=
    div_mul_cancel₀ ε hD
  have hb := riemann_log_error_le s t h hs hh m hmh G hG ξ hξ
  have hsum : (∑ j ∈ Finset.range m,
        (∫ u in (s + (j:ℝ)*h)..(s + ((j:ℝ)+1)*h), |G u - G (ξ j)| / u))
      ≤ (ε / (Real.log t - Real.log s)) * (Real.log t - Real.log s) := by
    have h1 := Finset.sum_le_sum hcell
    have h2 := sum_log_ratio s t h hs hh m hmh
    calc (∑ j ∈ Finset.range m,
          (∫ u in (s + (j:ℝ)*h)..(s + ((j:ℝ)+1)*h), |G u - G (ξ j)| / u))
        ≤ ∑ j ∈ Finset.range m,
            (ε / (Real.log t - Real.log s)) *
              Real.log ((s + ((j:ℝ)+1)*h) / (s + (j:ℝ)*h)) := h1
      _ = (ε / (Real.log t - Real.log s)) *
            (∑ j ∈ Finset.range m,
              Real.log ((s + ((j:ℝ)+1)*h) / (s + (j:ℝ)*h))) := by
          rw [Finset.mul_sum]
      _ = (ε / (Real.log t - Real.log s)) * Real.log (t / s) := by rw [h2]
      _ = (ε / (Real.log t - Real.log s)) * (Real.log t - Real.log s) := by
          rw [Real.log_div (ne_of_gt ht) (ne_of_gt hs)]
  rw [hval] at hsum
  exact hb.trans hsum

private lemma kappa1_val : kappa1 = 1 / 12 := rfl
private lemma kappa2_val : kappa2 = 29 / 250 := rfl

/-- The kernel `f ((1/2 - t - u)/kappa1)` is continuous on the closed exponent rectangle. -/
private lemma kernel_continuousOn (F f : ℝ → ℝ) (h : Wu04Functional.IsLinearSieve F f) :
    ContinuousOn (fun x : ℝ × ℝ => f ((1 / 2 - x.1 - x.2) / kappa1))
      (Set.Icc kappa1 kappa2 ×ˢ Set.Icc kappa2 (1 / 2 - 3*kappa1)) := by
  apply h.2.1.comp
    (((continuous_const.sub continuous_fst).sub continuous_snd).div_const kappa1).continuousOn
  intro x hx
  have hx1 := hx.1
  have hx2 := hx.2
  have hx2' : x.2 ≤ 1 / 4 := by
    have h3 : (1:ℝ) / 2 - 2 * kappa1 - kappa1 = 1 / 4 := by norm_num [kappa1_val]
    linarith [hx2.2]
  have hx1' : x.1 ≤ (29:ℝ) / 250 := by linarith [hx1.2, kappa2_val]
  have hpos : (0:ℝ) < 1 / 2 - x.1 - x.2 := by linarith
  have hk : (0:ℝ) < kappa1 := by norm_num [kappa1_val]
  simpa using div_pos hpos hk


/-- The exponent rectangle used for the F5 kernel. -/
private lemma box_arg_bounds {t u : ℝ} (ht : t ∈ Set.Icc kappa1 kappa2)
    (hu : u ∈ Set.Icc kappa2 (1 / 2 - 3*kappa1)) :
    (1 / 2 - t - u) / kappa1 ∈ Set.Icc (3 / 2) 4 := by
  have hk : kappa1 = 1 / 12 := kappa1_val
  have hk2 : kappa2 = 29 / 250 := kappa2_val
  have ht1 := ht.1; have ht2 := ht.2
  have hu1 := hu.1; have hu2 := hu.2
  constructor
  · rw [le_div_iff₀ (by norm_num [hk])]
    nlinarith [ht1, ht2, hu1, hu2]
  · rw [div_le_iff₀ (by norm_num [hk])]
    nlinarith [ht1, ht2, hu1, hu2]

/-- Uniform modulus of the F5 kernel on the closed exponent rectangle. -/
private lemma kernel_modulus (F f : ℝ → ℝ) (h : Wu04Functional.IsLinearSieve F f) :
    ∀ ε : ℝ, 0 < ε → ∃ γ : ℝ, 0 < γ ∧
      ∀ t ∈ Set.Icc kappa1 kappa2,
      ∀ u ∈ Set.Icc kappa2 (1 / 2 - 3*kappa1),
      ∀ t' ∈ Set.Icc kappa1 kappa2,
      ∀ u' ∈ Set.Icc kappa2 (1 / 2 - 3*kappa1),
      |t - t'| + |u - u'| ≤ γ →
      |f ((1 / 2 - t - u) / kappa1) - f ((1 / 2 - t' - u') / kappa1)| ≤ ε := by
  intro ε hε
  have hcont : ContinuousOn f (Set.Icc (3 / 2 : ℝ) 4) := by
    apply h.2.1.mono
    intro x hx
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Ioi]
    linarith [hx.1]
  have huc : UniformContinuousOn f (Set.Icc (3 / 2 : ℝ) 4) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hcont
  obtain ⟨δ, hδ, hδprop⟩ := Metric.uniformContinuousOn_iff_le.mp huc ε hε
  have hkpos : (0:ℝ) < kappa1 := by norm_num [kappa1_val]
  refine ⟨kappa1 * δ, by positivity, ?_⟩
  intro t ht u hu t' ht' u' hu' hdist
  have ha := box_arg_bounds ht hu
  have ha' := box_arg_bounds ht' hu'
  have hd : dist ((1 / 2 - t - u) / kappa1) ((1 / 2 - t' - u') / kappa1) ≤ δ := by
    rw [Real.dist_eq, div_sub_div_same, abs_div, abs_of_pos hkpos, div_le_iff₀ hkpos]
    have e : (1 / 2 - t - u) - (1 / 2 - t' - u') = (t' - t) + (u' - u) := by ring
    rw [e]
    have h1 : |(t' - t) + (u' - u)| ≤ |t - t'| + |u - u'| := by
      calc |(t' - t) + (u' - u)| ≤ |t' - t| + |u' - u| := abs_add_le _ _
        _ = |t - t'| + |u - u'| := by rw [abs_sub_comm t' t, abs_sub_comm u' u]
    linarith
  have := hδprop _ ha _ ha' hd
  simpa [Real.dist_eq] using this

/-- The F5 kernel is bounded on the closed exponent rectangle. -/
private lemma kernel_bounded (F f : ℝ → ℝ) (h : Wu04Functional.IsLinearSieve F f) :
    ∃ C : ℝ, ∀ x ∈ Set.Icc kappa1 kappa2 ×ˢ Set.Icc kappa2 (1 / 2 - 3*kappa1),
      |f ((1 / 2 - x.1 - x.2) / kappa1)| ≤ C := by
  have hc := kernel_continuousOn F f h
  have hcomp : IsCompact (Set.Icc kappa1 kappa2 ×ˢ Set.Icc kappa2 (1 / 2 - 3*kappa1)) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hc
  exact ⟨C, fun x hx => by simpa [Real.norm_eq_abs] using hC x hx⟩


/-- The cell form of the interval mass limit, uniform in the second argument of the weight.
This is `cell_weight_close` with the weight allowed to depend on a further real parameter,
the oscillation and the size at the reference point being bounded uniformly. -/
private lemma cell_weight_close_family (a b v : ℝ) (ha : 0 < a) (hab : a < b)
    (hv : v ∈ Set.Icc a b) (G : ℝ → ℝ → ℝ) {D C : ℝ} (hD : 0 ≤ D)
    (hosc : ∀ u : ℝ, ∀ t ∈ Set.Icc a b, |G u t - G u v| ≤ D)
    (hC : ∀ u : ℝ, |G u v| ≤ C)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ u : ℝ,
      |(∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p),
          G u (Real.log (p:ℝ) / Real.log (N:ℝ)) * (((p:ℝ) - 1))⁻¹)
        - G u v * (Real.log b - Real.log a)|
      ≤ D * (Real.log b - Real.log a + η) + C * η := by
  set W : ℕ → ℝ := fun N => ∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter
      (fun p => Nat.Prime p), (((p:ℝ) - 1))⁻¹ with hWdef
  have hWlim : Tendsto W atTop (𝓝 (Real.log b - Real.log a)) := by
    simpa only [hWdef] using cell_mass_tendsto a b ha hab
  have hWbound : ∀ᶠ N : ℕ in atTop, |W N - (Real.log b - Real.log a)| ≤ η := by
    have h0 : Tendsto (fun N => W N - (Real.log b - Real.log a)) atTop (𝓝 0) := by
      simpa using hWlim.sub_const (Real.log b - Real.log a)
    obtain ⟨N0, hN0⟩ := (Metric.tendsto_atTop.1 h0) η hη
    filter_upwards [eventually_ge_atTop N0] with N hN
    have h1 := hN0 N hN
    rw [Real.dist_eq, sub_zero] at h1
    exact le_of_lt h1
  filter_upwards [hWbound, eventually_ge_atTop 2] with N hWN hN2
  intro u
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < Real.log (N:ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hmem : ∀ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p),
      Real.log (p:ℝ) / Real.log (N:ℝ) ∈ Set.Icc a b ∧ (0:ℝ) < ((p:ℝ) - 1)⁻¹ := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨hlo, hhi⟩, hP⟩ := hp
    have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hP.two_le
    have hppos : 0 < (p:ℝ) := by linarith
    constructor
    · refine ⟨?_, ?_⟩
      · rw [le_div_iff₀ hlogN]
        have hlt : (N:ℝ)^a < (p:ℝ) := (lt_floor_iff (le_of_lt (rpow_pos_of_pos hNpos a))).mp hlo
        have h1 : Real.log ((N:ℝ)^a) < Real.log (p:ℝ) :=
          Real.log_lt_log (rpow_pos_of_pos hNpos a) hlt
        rw [Real.log_rpow hNpos] at h1
        linarith
      · rw [div_le_iff₀ hlogN]
        have hle : (p:ℝ) ≤ (N:ℝ)^b := by
          have h2 : (p:ℝ) ≤ (⌊(N:ℝ)^b⌋₊ : ℝ) := by exact_mod_cast hhi
          exact le_trans h2 (Nat.floor_le (le_of_lt (rpow_pos_of_pos hNpos b)))
        have h1 : Real.log (p:ℝ) ≤ Real.log ((N:ℝ)^b) := Real.log_le_log hppos hle
        rwa [Real.log_rpow hNpos] at h1
    · have : (0:ℝ) < (p:ℝ) - 1 := by linarith
      positivity
  have hWS : G u v * W N
      = ∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p),
          G u v * (((p:ℝ) - 1))⁻¹ := by
    rw [hWdef, Finset.mul_sum]
  have hdif : (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p),
        G u (Real.log (p:ℝ) / Real.log (N:ℝ)) * (((p:ℝ) - 1))⁻¹) - G u v * W N
      = ∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p),
          (G u (Real.log (p:ℝ) / Real.log (N:ℝ)) - G u v) * (((p:ℝ) - 1))⁻¹ := by
    rw [hWS, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hstep1 : |(∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p),
        G u (Real.log (p:ℝ) / Real.log (N:ℝ)) * (((p:ℝ) - 1))⁻¹) - G u v * W N|
      ≤ (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p),
            |G u (Real.log (p:ℝ) / Real.log (N:ℝ)) - G u v| * (((p:ℝ) - 1))⁻¹) := by
    rw [hdif]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
    exact Finset.sum_congr rfl fun p hp => by rw [abs_mul, abs_of_pos (hmem p hp).2]
  have hstep2 : (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p),
        |G u (Real.log (p:ℝ) / Real.log (N:ℝ)) - G u v| * (((p:ℝ) - 1))⁻¹) ≤ D * W N := by
    rw [hWdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    exact mul_le_mul_of_nonneg_right (hosc _ _ (hmem p hp).1) (le_of_lt (hmem p hp).2)
  have hWle : W N ≤ Real.log b - Real.log a + η := by
    have h := abs_le.mp hWN
    linarith [h.2]
  calc |(∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p),
        G u (Real.log (p:ℝ) / Real.log (N:ℝ)) * (((p:ℝ) - 1))⁻¹)
      - G u v * (Real.log b - Real.log a)|
      ≤ |(∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p),
            G u (Real.log (p:ℝ) / Real.log (N:ℝ)) * (((p:ℝ) - 1))⁻¹) - G u v * W N|
          + |G u v * W N - G u v * (Real.log b - Real.log a)| := abs_sub_le _ _ _
    _ ≤ (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p),
          |G u (Real.log (p:ℝ) / Real.log (N:ℝ)) - G u v| * (((p:ℝ) - 1))⁻¹)
        + |G u v| * |W N - (Real.log b - Real.log a)| := by
        apply add_le_add hstep1
        rw [show G u v * W N - G u v * (Real.log b - Real.log a)
          = G u v * (W N - (Real.log b - Real.log a)) by ring, abs_mul]
    _ ≤ D * W N + C * η := by
        apply add_le_add hstep2
        exact le_trans (mul_le_mul_of_nonneg_left hWN (abs_nonneg _)) (by
          apply mul_le_mul_of_nonneg_right (hC u) (le_of_lt hη))
    _ ≤ D * (Real.log b - Real.log a + η) + C * η := by
        have := mul_le_mul_of_nonneg_left hWle hD
        linarith

/-- The `Upsilon 5` pair domain sits inside one fixed exponent rectangle. -/
private lemma lowerPairs5_subset_box {N : ℕ} (hN : 2 ≤ N) :
    ∀ x ∈ lowerPairs5 N,
      x ∈ ((Finset.Ioc ⌊(N:ℝ)^(kappa1/2)⌋₊ ⌊(N:ℝ)^kappa2⌋₊) ×ˢ
          (Finset.Ioc ⌊(N:ℝ)^(kappa2/2)⌋₊ ⌊(N:ℝ)^(1/2 - 3*kappa1)⌋₊)) := by
  intro x hx
  obtain ⟨hprime, hprime2, hp1, hp2, hq1, hq2⟩ := lowerPairs5_mem hx
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hk1 : (0:ℝ) < kappa1 := by norm_num [kappa1_val]
  have hk2 : (0:ℝ) < kappa2 := by norm_num [kappa2_val]
  have hN1 : (1:ℝ) < (N:ℝ) := by exact_mod_cast (show 1 < N by omega)
  have h2k1 : (N:ℝ)^(kappa1/2) < (N:ℝ)^kappa1 := by
    apply Real.rpow_lt_rpow_of_exponent_lt hN1
    linarith
  have h2k2 : (N:ℝ)^(kappa2/2) < (N:ℝ)^kappa2 := by
    apply Real.rpow_lt_rpow_of_exponent_lt hN1
    linarith
  have hppos : (0:ℝ) < (x.1:ℝ) := by
    have := hprime.two_le
    have : (2:ℝ) ≤ (x.1:ℝ) := by exact_mod_cast this
    linarith
  have hqpos : (0:ℝ) < (x.2:ℝ) := by
    have := hprime2.two_le
    have : (2:ℝ) ≤ (x.2:ℝ) := by exact_mod_cast this
    linarith
  have hle : (N:ℝ)^(1/2 - 2*kappa1) / (x.1:ℝ) ≤ (N:ℝ)^(1/2 - 3*kappa1) := by
    rw [div_le_iff₀ hppos]
    have hstep : (N:ℝ)^(1/2 - 2*kappa1) ≤ (N:ℝ)^(1/2 - 3*kappa1) * (N:ℝ)^kappa1 := by
      rw [← Real.rpow_add hNpos]
      have : 1/2 - 3*kappa1 + kappa1 = 1/2 - 2*kappa1 := by ring
      rw [this]
    calc (N:ℝ)^(1/2 - 2*kappa1) ≤ (N:ℝ)^(1/2 - 3*kappa1) * (N:ℝ)^kappa1 := hstep
      _ ≤ (N:ℝ)^(1/2 - 3*kappa1) * (x.1:ℝ) := by
          apply mul_le_mul_of_nonneg_left hp1 (le_of_lt (rpow_pos_of_pos hNpos _))
  simp only [Finset.mem_product, Finset.mem_Ioc]
  exact ⟨⟨(lt_floor_iff (le_of_lt (rpow_pos_of_pos hNpos _))).mpr
      (lt_of_lt_of_le h2k1 hp1), Nat.le_floor (le_of_lt hp2)⟩,
    ⟨(lt_floor_iff (le_of_lt (rpow_pos_of_pos hNpos _))).mpr
      (lt_of_lt_of_le h2k2 hq1), Nat.le_floor (le_of_lt (lt_of_lt_of_le hq2 hle))⟩⟩

/-- The mass of the `Upsilon 5` domain is bounded. -/
private lemma lowerPairs5_mass_bounded :
    ∃ M : ℝ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∑ q ∈ lowerPairs5 N, (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)) ≤ M := by
  have hk1 : (0:ℝ) < kappa1 := by norm_num [kappa1_val]
  have hk2 : (0:ℝ) < kappa2 := by norm_num [kappa2_val]
  set B : ℕ → ℝ := fun N => ∑ q ∈ ((Finset.Ioc ⌊(N:ℝ)^(kappa1/2)⌋₊ ⌊(N:ℝ)^kappa2⌋₊) ×ˢ
          (Finset.Ioc ⌊(N:ℝ)^(kappa2/2)⌋₊ ⌊(N:ℝ)^(1/2 - 3*kappa1)⌋₊)).filter
        (fun q : ℕ × ℕ => q.1.Prime ∧ q.2.Prime),
        (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)) with hB
  set L : ℝ := (Real.log kappa2 - Real.log (kappa1/2)) *
      (Real.log (1/2 - 3*kappa1) - Real.log (kappa2/2)) with hL
  have hlim : Tendsto B atTop (𝓝 L) := by
    rw [hB, hL]
    exact box_mass_tendsto (kappa1/2) kappa2 (kappa2/2) (1/2 - 3*kappa1)
      (by linarith) (by norm_num [kappa1_val, kappa2_val])
      (by linarith) (by norm_num [kappa1_val, kappa2_val])
  have hev : ∀ᶠ N : ℕ in atTop, B N ≤ L + 1 := by
    have h0 : Tendsto (fun N => B N - L) atTop (𝓝 0) := by simpa using hlim.sub_const L
    obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.1 h0) 1 (by norm_num)
    filter_upwards [eventually_ge_atTop N1] with N hNN
    have h1 := hN1 N hNN
    rw [Real.dist_eq, sub_zero] at h1
    have h2 := abs_le.mp (le_of_lt h1)
    linarith [h2.2]
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 hev
  refine ⟨L + 1, max N0 2, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  refine le_trans ?_ (hN0 N (le_trans (le_max_left _ _) hN))
  rw [hB]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) (fun x hx _ => ?_)
  · obtain ⟨hpr, hpr2, -, -, -, -⟩ := lowerPairs5_mem hx
    exact Finset.mem_filter.mpr ⟨lowerPairs5_subset_box hN2 x hx, hpr, hpr2⟩
  · obtain ⟨-, hpr, hpr2⟩ := Finset.mem_filter.mp hx
    have h1 : (2:ℝ) ≤ (x.1:ℝ) := by exact_mod_cast hpr.two_le
    have h2 : (2:ℝ) ≤ (x.2:ℝ) := by exact_mod_cast hpr2.two_le
    have h3 : (0:ℝ) < (x.1:ℝ) - 1 := by linarith
    have h4 : (0:ℝ) < (x.2:ℝ) - 1 := by linarith
    positivity

/-- The logarithmic loss vanishes. -/
private lemma loglog_div_tendsto :
    Tendsto (fun N : ℕ => Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  exact h1.comp hlog

/-- The two logarithmic coordinates of a pair in the `Upsilon 5` domain, with room to spare. -/
private lemma box_arg_bounds_margin {t u : ℝ} (ht : t ∈ Set.Icc kappa1 kappa2)
    (hu : u ∈ Set.Icc kappa2 (1 / 2 - 3*kappa1)) :
    (1 / 2 - t - u) / kappa1 ∈ Set.Icc (3 / 2 + 1 / 20) (4 - 1 / 20) := by
  have hk : (0:ℝ) < kappa1 := by norm_num [kappa1_val]
  have ht1 := ht.1; have ht2 := ht.2
  have hu1 := hu.1; have hu2 := hu.2
  have hk2v : kappa2 = 29 / 250 := kappa2_val
  have hk1v : kappa1 = 1 / 12 := kappa1_val
  constructor
  · rw [le_div_iff₀ hk]
    nlinarith [ht1, ht2, hu1, hu2]
  · rw [div_le_iff₀ hk]
    nlinarith [ht1, ht2, hu1, hu2]

/-- Uniform continuity of the sieve weight on the argument range of the kernel. -/
private lemma f_uniform (F f : ℝ → ℝ) (h : Wu04Functional.IsLinearSieve F f) (ε : ℝ) (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 / 20 ∧
      ∀ a b : ℝ, a ∈ Set.Icc (3 / 2 : ℝ) 4 → b ∈ Set.Icc (3 / 2 : ℝ) 4 →
        |a - b| ≤ γ → |f a - f b| ≤ ε := by
  have hcont : ContinuousOn f (Set.Icc (3 / 2 : ℝ) 4) := by
    apply h.2.1.mono
    intro x hx
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Ioi]
    linarith [hx.1]
  have huc : UniformContinuousOn f (Set.Icc (3 / 2 : ℝ) 4) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hcont
  obtain ⟨δ, hδ, hδprop⟩ := Metric.uniformContinuousOn_iff_le.mp huc ε hε
  refine ⟨min δ (1 / 20), lt_min hδ (by norm_num), min_le_right _ _, ?_⟩
  intro a b ha hb hab
  have hab' : dist a b ≤ δ := by
    rw [Real.dist_eq]
    exact le_trans hab (min_le_left _ _)
  have := hδprop _ ha _ hb hab'
  simpa [Real.dist_eq] using this

/-- The level of a pair in the `Upsilon 5` domain, and the kernel argument, are within any `ε`
once `N` is large: the logarithmic loss is the only difference. -/
private lemma level_kernel_close (F f : ℝ → ℝ) (h : Wu04Functional.IsLinearSieve F f) (B : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ p q : ℕ, p.Prime → q.Prime →
      (N:ℝ)^kappa1 ≤ (p:ℝ) → (p:ℝ) < (N:ℝ)^kappa2 → (N:ℝ)^kappa2 ≤ (q:ℝ) →
      (q:ℝ) < (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ) →
      |f (lowerLevel B N (p*q)) -
        f ((1 / 2 - Real.log (p:ℝ)/Real.log (N:ℝ) - Real.log (q:ℝ)/Real.log (N:ℝ)) / kappa1)|
        ≤ ε := by
  obtain ⟨γ, hγ, hγ20, hγprop⟩ := f_uniform F f h ε hε
  have hk : (0:ℝ) < kappa1 := by norm_num [kappa1_val]
  have hB : Tendsto (fun N : ℕ => |B| / kappa1 *
      (Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ))) atTop (𝓝 0) := by
    have := loglog_div_tendsto.const_mul (|B| / kappa1)
    simpa using this
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.1 hB γ hγ
  filter_upwards [eventually_ge_atTop (max N1 3)] with N hN
  intro p q hp hq hp1 hp2 hq1 hq2
  have hN2 : 2 ≤ N := le_trans (le_trans (by norm_num : (2:ℕ) ≤ 3) (le_max_right N1 3)) hN
  have hN1' : N1 ≤ N := le_trans (le_max_left N1 3) hN
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1r : (1:ℝ) < (N:ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N:ℝ) := Real.log_pos hN1r
  have hppos : (0:ℝ) < (p:ℝ) := by
    have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
    linarith
  have hqpos : (0:ℝ) < (q:ℝ) := by
    have : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq.two_le
    linarith
  -- the two coordinates of the pair
  have ht : Real.log (p:ℝ)/Real.log (N:ℝ) ∈ Set.Icc kappa1 kappa2 := by
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ hlogN]
      have h1 : Real.log ((N:ℝ)^kappa1) ≤ Real.log (p:ℝ) :=
        Real.log_le_log (rpow_pos_of_pos hNpos _) hp1
      rwa [Real.log_rpow hNpos] at h1
    · rw [div_le_iff₀ hlogN]
      have h1 : Real.log (p:ℝ) < Real.log ((N:ℝ)^kappa2) :=
        Real.log_lt_log hppos hp2
      rw [Real.log_rpow hNpos] at h1
      linarith
  have hu : Real.log (q:ℝ)/Real.log (N:ℝ) ∈ Set.Icc kappa2 (1/2 - 3*kappa1) := by
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ hlogN]
      have h1 : Real.log ((N:ℝ)^kappa2) ≤ Real.log (q:ℝ) :=
        Real.log_le_log (rpow_pos_of_pos hNpos _) hq1
      rwa [Real.log_rpow hNpos] at h1
    · rw [div_le_iff₀ hlogN]
      have hpu : Real.log (q:ℝ) < Real.log ((N:ℝ)^(1/2 - 2*kappa1) / (p:ℝ)) :=
        Real.log_lt_log hqpos hq2
      rw [Real.log_div (ne_of_gt (rpow_pos_of_pos hNpos _)) (ne_of_gt hppos),
        Real.log_rpow hNpos] at hpu
      -- log p >= kappa1 log N
      have hplog : kappa1 * Real.log (N:ℝ) ≤ Real.log (p:ℝ) := by
        have h1 : Real.log ((N:ℝ)^kappa1) ≤ Real.log (p:ℝ) :=
          Real.log_le_log (rpow_pos_of_pos hNpos _) hp1
        rwa [Real.log_rpow hNpos] at h1
      nlinarith [hpu, hplog]
  have hbox := box_arg_bounds_margin ht hu
  -- the level and the kernel argument
  have hlev := lowerLevel_mul B hN2 hp.pos hq.pos
  set t : ℝ := Real.log (p:ℝ)/Real.log (N:ℝ) with htdef
  set u : ℝ := Real.log (q:ℝ)/Real.log (N:ℝ) with hudef
  have hsmall : |B / kappa1 * (Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ))| ≤ γ := by
    have h := hN1 N hN1'
    rw [Real.dist_eq, sub_zero] at h
    have hlog3 : (1:ℝ) < Real.log 3 := by
      have h1 := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      rwa [Real.log_exp] at h1
    have hlogN3 : Real.log 3 ≤ Real.log (N:ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (show 3 ≤ N by omega))
    have hloglog : 0 ≤ Real.log (Real.log (N:ℝ)) :=
      Real.log_nonneg (le_trans (le_of_lt hlog3) hlogN3)
    have hX : 0 ≤ Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ) := div_nonneg hloglog (le_of_lt hlogN)
    have heq : |B / kappa1 * (Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ))|
        = |B| / kappa1 * (Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ)) := by
      rw [abs_mul, abs_div, abs_of_pos hk, abs_of_nonneg hX]
    have hgoal : |B / kappa1 * (Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ))|
        = |(|B| / kappa1 * (Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ)))| := by
      rw [heq, abs_of_nonneg (mul_nonneg (by positivity) hX)]
    rw [hgoal]
    exact le_of_lt h
  have hval : |lowerLevel B N (p*q) - (1/2 - t - u)/kappa1|
      = |B / kappa1 * (Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ))| := by
    rw [hlev]
    have hring : (1/2 - t - u)/kappa1 - B/kappa1*(Real.log (Real.log (N:ℝ))/Real.log (N:ℝ))
        - (1/2 - t - u)/kappa1
        = -(B/kappa1*(Real.log (Real.log (N:ℝ))/Real.log (N:ℝ))) := by ring
    rw [hring, abs_neg]
  have hnear : |lowerLevel B N (p*q) - (1/2 - t - u)/kappa1| ≤ γ := by
    rw [hval]; exact hsmall
  have hmem1 : (1/2 - t - u)/kappa1 ∈ Set.Icc (3/2 : ℝ) 4 :=
    ⟨le_trans (by norm_num) hbox.1, le_trans hbox.2 (by norm_num)⟩
  have hmem2 : lowerLevel B N (p*q) ∈ Set.Icc (3/2 : ℝ) 4 := by
    constructor
    · have h := abs_le.mp hnear
      linarith [hbox.1, h.1, hγ20]
    · have h := abs_le.mp hnear
      linarith [hbox.2, h.2, hγ20]
  exact hγprop _ _ hmem2 hmem1 hnear

/-- The inner `u`-integral of the `Upsilon 5` main term is bounded on the exponent interval. -/
private lemma psi_bounded (F f : ℝ → ℝ) (h : Wu04Functional.IsLinearSieve F f) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc kappa1 kappa2,
      |(∫ u in kappa2..(1 / 2 - 2*kappa1 - t), f ((1 / 2 - t - u)/kappa1)/u)|
        ≤ C * (1 / 2 - 3*kappa1 - kappa2) := by
  obtain ⟨C0, hC0⟩ := kernel_bounded F f h
  have hk2 : (0:ℝ) < kappa2 := by norm_num [kappa2_val]
  have hCnn : 0 ≤ C0 := by
    have hK := hC0 (kappa1, kappa2) ⟨⟨le_refl _, by norm_num [kappa1_val, kappa2_val]⟩,
      ⟨le_refl _, by norm_num [kappa1_val, kappa2_val]⟩⟩
    exact le_trans (abs_nonneg _) hK
  refine ⟨C0 / kappa2, ?_⟩
  intro t ht
  have hc1 : kappa2 ≤ 1 / 2 - 2*kappa1 - t := by
    have h1 := ht.2
    norm_num [kappa1_val, kappa2_val] at h1 ⊢
    linarith
  have hpt : ∀ u ∈ Set.uIoc kappa2 (1 / 2 - 2*kappa1 - t),
      ‖f ((1 / 2 - t - u)/kappa1)/u‖ ≤ C0 / kappa2 := by
    intro u hu
    rw [Set.uIoc_of_le hc1] at hu
    obtain ⟨hu1, hu2⟩ := hu
    have hu1' : kappa2 < u := hu1
    have hupos : (0:ℝ) < u := lt_trans hk2 hu1'
    have hub : u ∈ Set.Icc kappa2 (1 / 2 - 3*kappa1) := by
      refine ⟨le_of_lt hu1', ?_⟩
      linarith [hu2, ht.1]
    have hK := hC0 (t, u) ⟨ht, hub⟩
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hupos]
    have hle : |f ((1 / 2 - t - u)/kappa1)| / u ≤ C0 / u := by
      apply div_le_div_of_nonneg_right hK (le_of_lt hupos)
    have hle2 : C0 / u ≤ C0 / kappa2 := by
      rw [div_le_div_iff₀ hupos hk2]
      exact mul_le_mul_of_nonneg_left (le_of_lt hu1') hCnn
    linarith
  have hInt := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  have hnn : (0:ℝ) ≤ 1 / 2 - 2*kappa1 - t - kappa2 := by linarith [hc1]
  have hdiff : 1 / 2 - 2*kappa1 - t - kappa2 ≤ 1 / 2 - 3*kappa1 - kappa2 := by
    have h4 := ht.1
    linarith
  have hstep : C0 / kappa2 * |1 / 2 - 2*kappa1 - t - kappa2|
      ≤ C0 / kappa2 * (1 / 2 - 3*kappa1 - kappa2) := by
    rw [abs_of_nonneg hnn]
    apply mul_le_mul_of_nonneg_left hdiff
    positivity
  calc |(∫ u in kappa2..(1 / 2 - 2*kappa1 - t), f ((1 / 2 - t - u)/kappa1)/u)|
      = ‖∫ u in kappa2..(1 / 2 - 2*kappa1 - t), f ((1 / 2 - t - u)/kappa1)/u‖ := by
        rw [Real.norm_eq_abs]
    _ ≤ C0 / kappa2 * |1 / 2 - 2*kappa1 - t - kappa2| := hInt
    _ ≤ _ := hstep


open MeasureTheory

/-- The `u`-integrand of the F5 inner integral is continuous on every band inside the box. -/
private lemma psiIntegrand_continuous {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0))
    {t a b : ℝ} (ht : t ∈ Set.Icc kappa1 kappa2) (ha : kappa2 ≤ a) (hb : a ≤ b)
    (hb2 : b ≤ 1 / 2 - 3*kappa1) :
    ContinuousOn (fun u : ℝ => f ((1 / 2 - t - u)/kappa1)/u) (Set.Icc a b) := by
  have hk : (0:ℝ) < kappa1 := by norm_num [kappa1_val]
  have hk2 : (0:ℝ) < kappa2 := by norm_num [kappa2_val]
  have hupper : ∀ u ∈ Set.Icc a b, (1 / 2 - t - u)/kappa1 ∈ Set.Ioi (0:ℝ) := by
    intro u hu
    simp only [Set.mem_Ioi]
    apply div_pos _ hk
    have ht2 := ht.2
    have hu1 := hu.2
    have h1 : u ≤ 1 / 2 - 3*kappa1 := le_trans hu1 hb2
    have h2 : kappa1 = 1 / 12 := kappa1_val
    have h3 : kappa2 = 29 / 250 := kappa2_val
    linarith
  have hfc : ContinuousOn (fun u : ℝ => f ((1 / 2 - t - u)/kappa1)) (Set.Icc a b) :=
    hf.comp (((continuous_const.sub continuous_const).sub continuous_id).div_const kappa1).continuousOn
      hupper
  exact hfc.div continuous_id.continuousOn (fun u hu =>
    ne_of_gt (lt_of_lt_of_le hk2 (le_trans ha hu.1)))


/-- One fixed band has mass at most its logarithmic length plus `η`, eventually. -/
private lemma cell_mass_le {a b : ℝ} (ha : 0 < a) (hab : a < b) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p),
        (((p:ℝ) - 1))⁻¹) ≤ Real.log b - Real.log a + η := by
  have h := cell_mass_tendsto a b ha hab
  have h0 : Tendsto (fun N : ℕ =>
      (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p => Nat.Prime p),
        (((p:ℝ) - 1))⁻¹) - (Real.log b - Real.log a)) atTop (𝓝 0) := by
    simpa using h.sub_const (Real.log b - Real.log a)
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 h0 η hη
  filter_upwards [eventually_ge_atTop N0] with N hN
  have h1 := hN0 N hN
  rw [Real.dist_eq, sub_zero] at h1
  linarith [(abs_le.mp (le_of_lt h1)).2]

/-- A prime in the integer box of a band has its logarithmic coordinate in that band. -/
private lemma log_div_mem_band {N : ℕ} (hN : 2 ≤ N) {a b : ℝ} (ha : 0 < a)
    {p : ℕ} (hp : p ∈ Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊) :
    Real.log (p:ℝ) / Real.log (N:ℝ) ∈ Set.Icc a b := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1:ℝ) < (N:ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N:ℝ) := Real.log_pos hN1
  simp only [Finset.mem_Ioc] at hp
  have hppos : (0:ℝ) < (p:ℝ) := by
    have : 0 < p := lt_of_le_of_lt (Nat.zero_le _) hp.1
    exact_mod_cast this
  constructor
  · rw [le_div_iff₀ hlogN]
    have hlt : (N:ℝ)^a < (p:ℝ) := (lt_floor_iff (le_of_lt (rpow_pos_of_pos hNpos a))).mp hp.1
    have h1 : Real.log ((N:ℝ)^a) < Real.log (p:ℝ) := Real.log_lt_log (rpow_pos_of_pos hNpos a) hlt
    rw [Real.log_rpow hNpos] at h1
    linarith
  · rw [div_le_iff₀ hlogN]
    have hle : (p:ℝ) ≤ (⌊(N:ℝ)^b⌋₊ : ℝ) := by exact_mod_cast hp.2
    have h2 : (p:ℝ) ≤ (N:ℝ)^b := le_trans hle (Nat.floor_le (le_of_lt (rpow_pos_of_pos hNpos b)))
    have h1 : Real.log (p:ℝ) ≤ Real.log ((N:ℝ)^b) := Real.log_le_log hppos h2
    rw [Real.log_rpow hNpos] at h1
    linarith

/-- The double cell sum is the mass of the `p`-cell times the reference value, up to the
`p`-cell closure error `E`, uniformly in `q`. This is the swap of the two band sums plus the
`q`-band mass bound. -/
private lemma cell_pair_sum_close {K : ℝ → ℝ → ℝ} {T T' U U' ξ E η : ℝ}
    (hT : 0 < T) (hTT' : T < T') (hU : 0 < U) (hUU' : U < U')
    (hξ : ξ ∈ Set.Icc T T') (hE : 0 ≤ E) (hη : 0 < η)
    (hnear : ∀ᶠ N : ℕ in atTop, ∀ u : ℝ,
      |(∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p),
          K (Real.log (p:ℝ)/Real.log (N:ℝ)) u * (((p:ℝ) - 1))⁻¹)
        - K ξ u * (Real.log T' - Real.log T)| ≤ E)
    (hmass : ∀ᶠ N : ℕ in atTop,
      (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
          (((q:ℝ) - 1))⁻¹) ≤ Real.log U' - Real.log U + η) :
    ∀ᶠ N : ℕ in atTop,
      |(∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p),
          ∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
            K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
              * (((p:ℝ) - 1))⁻¹ * (((q:ℝ) - 1))⁻¹)
        - (Real.log T' - Real.log T)
            * (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
                K ξ (Real.log (q:ℝ)/Real.log (N:ℝ)) * (((q:ℝ) - 1))⁻¹)|
      ≤ (Real.log U' - Real.log U + η) * E := by
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.1 hnear
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.1 hmass
  filter_upwards [eventually_ge_atTop (max N1 N2)] with N hN
  have hnear' := hN1 N (le_trans (le_max_left _ _) hN)
  have hmass' := hN2 N (le_trans (le_max_right _ _) hN)
  have hWpos : ∀ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
      (0:ℝ) < (((q:ℝ) - 1))⁻¹ := by
    intro q hq
    obtain ⟨-, hprim⟩ := Finset.mem_filter.mp hq
    have h2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hprim.two_le
    have : (0:ℝ) < (q:ℝ) - 1 := by linarith
    positivity
  have hrewrite :
      (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p),
        ∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
          K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
            * (((p:ℝ) - 1))⁻¹ * (((q:ℝ) - 1))⁻¹)
        = ∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
            (((q:ℝ) - 1))⁻¹ *
              (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p),
                K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
                  * (((p:ℝ) - 1))⁻¹) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hfac :
      (Real.log T' - Real.log T)
          * (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
              K ξ (Real.log (q:ℝ)/Real.log (N:ℝ)) * (((q:ℝ) - 1))⁻¹)
        = ∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
            (((q:ℝ) - 1))⁻¹ *
              (K ξ (Real.log (q:ℝ)/Real.log (N:ℝ)) * (Real.log T' - Real.log T)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [hrewrite, hfac, ← Finset.sum_sub_distrib]
  have hbd : ∀ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
      |(((q:ℝ) - 1))⁻¹ *
              (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p),
                K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
                  * (((p:ℝ) - 1))⁻¹)
          - (((q:ℝ) - 1))⁻¹ *
              (K ξ (Real.log (q:ℝ)/Real.log (N:ℝ)) * (Real.log T' - Real.log T))|
        ≤ (((q:ℝ) - 1))⁻¹ * E := by
    intro q hq
    have hw := hWpos q hq
    rw [show (((q:ℝ) - 1))⁻¹ *
              (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p),
                K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
                  * (((p:ℝ) - 1))⁻¹)
          - (((q:ℝ) - 1))⁻¹ *
              (K ξ (Real.log (q:ℝ)/Real.log (N:ℝ)) * (Real.log T' - Real.log T))
          = (((q:ℝ) - 1))⁻¹ *
              ((∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p),
                K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
                  * (((p:ℝ) - 1))⁻¹)
                - K ξ (Real.log (q:ℝ)/Real.log (N:ℝ)) * (Real.log T' - Real.log T)) by ring,
        abs_mul, abs_of_pos hw]
    exact mul_le_mul_of_nonneg_left (hnear' _) (le_of_lt hw)
  calc |∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
        ((((q:ℝ) - 1))⁻¹ *
              (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p),
                K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
                  * (((p:ℝ) - 1))⁻¹)
          - (((q:ℝ) - 1))⁻¹ *
              (K ξ (Real.log (q:ℝ)/Real.log (N:ℝ)) * (Real.log T' - Real.log T)))|
      ≤ ∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
          |(((q:ℝ) - 1))⁻¹ *
              (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p),
                K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
                  * (((p:ℝ) - 1))⁻¹)
          - (((q:ℝ) - 1))⁻¹ *
              (K ξ (Real.log (q:ℝ)/Real.log (N:ℝ)) * (Real.log T' - Real.log T))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
          (((q:ℝ) - 1))⁻¹ * E := Finset.sum_le_sum hbd
    _ = (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
          (((q:ℝ) - 1))⁻¹) * E := by rw [Finset.sum_mul]
    _ ≤ (Real.log U' - Real.log U + η) * E := mul_le_mul_of_nonneg_right hmass' hE

/-- The inner `u`-integral of the `Upsilon 5` main term is continuous on the exponent interval. -/
private lemma psi_continuousOn (F f : ℝ → ℝ) (h : Wu04Functional.IsLinearSieve F f) :
    ContinuousOn (fun t : ℝ => ∫ u in kappa2..(1 / 2 - 2*kappa1 - t),
      f ((1 / 2 - t - u)/kappa1)/u) (Set.Icc kappa1 kappa2) := by
  obtain ⟨C0, hC0⟩ := kernel_bounded F f h
  have hCnn : 0 ≤ C0 := by
    have hK := hC0 (kappa1, kappa2) ⟨⟨le_refl _, by norm_num [kappa1_val, kappa2_val]⟩,
      ⟨le_refl _, by norm_num [kappa1_val, kappa2_val]⟩⟩
    exact le_trans (abs_nonneg _) hK
  have hk2 : (0:ℝ) < kappa2 := by norm_num [kappa2_val]
  have hU : (0:ℝ) < 1 / 2 - 3*kappa1 - kappa2 := by norm_num [kappa1_val, kappa2_val]
  have hk2U : kappa2 ≤ 1 / 2 - 3*kappa1 := by norm_num [kappa1_val, kappa2_val]
  rw [Metric.continuousOn_iff]
  intro t0 ht0 ε hε
  -- budgets: `ε1` for the oscillation inside a `u`-band, `δ` for the moving band
  obtain ⟨ε1, hε1, hε1U⟩ : ∃ ε1 : ℝ, 0 < ε1 ∧
      ε1 * (1 / 2 - 3*kappa1 - kappa2) / kappa2 ≤ ε / 4 := by
    refine ⟨ε * kappa2 / (8 * (1 / 2 - 3*kappa1 - kappa2)), ?_, ?_⟩
    · positivity
    · have hcalc : ε * kappa2 / (8 * (1 / 2 - 3*kappa1 - kappa2))
          * (1 / 2 - 3*kappa1 - kappa2) / kappa2 = ε / 8 := by
        field_simp
        exact div_self (ne_of_gt (by linarith [hU]))
      rw [hcalc]
      linarith
  obtain ⟨γ1, hγ1, hγ1prop⟩ := kernel_modulus F f h ε1 hε1
  obtain ⟨δ, hδ, hδγ1, hδC⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ γ1 ∧ C0 * δ / kappa2 ≤ ε / 4 := by
    refine ⟨min γ1 (ε * kappa2 / (4 * (C0 + 1))), lt_min hγ1 (by positivity),
      min_le_left _ _, ?_⟩
    have hle : min γ1 (ε * kappa2 / (4 * (C0 + 1))) ≤ ε * kappa2 / (4 * (C0 + 1)) :=
      min_le_right _ _
    have hC1 : (0:ℝ) < C0 + 1 := by linarith
    have hstep : C0 * min γ1 (ε * kappa2 / (4 * (C0 + 1)))
        ≤ C0 * (ε * kappa2 / (4 * (C0 + 1))) := mul_le_mul_of_nonneg_left hle hCnn
    have hstep2 : C0 * (ε * kappa2 / (4 * (C0 + 1))) ≤ ε * kappa2 / 4 := by
      rw [← mul_div_assoc]
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 4 * (C0 + 1)) (by norm_num : (0:ℝ) < 4)]
      nlinarith [mul_pos hε hk2, hCnn]
    rw [div_le_iff₀ hk2]
    nlinarith [hstep, hstep2]
  refine ⟨δ, hδ, ?_⟩
  intro t ht hdist
  have hdist' : |t - t0| ≤ δ := by
    rw [Real.dist_eq] at hdist
    exact le_of_lt hdist
  have htbox : t ∈ Set.Icc kappa1 kappa2 := ht
  -- the ranges
  have hc0lo : kappa2 ≤ 1 / 2 - 2*kappa1 - t0 := by
    have h2 := ht0.2
    norm_num [kappa1_val, kappa2_val] at h2 ⊢
    linarith
  have hc0hi : 1 / 2 - 2*kappa1 - t0 ≤ 1 / 2 - 3*kappa1 := by linarith [ht0.1]
  have hclo : kappa2 ≤ 1 / 2 - 2*kappa1 - t := by
    have h2 := ht.2
    norm_num [kappa1_val, kappa2_val] at h2 ⊢
    linarith
  have hchi : 1 / 2 - 2*kappa1 - t ≤ 1 / 2 - 3*kappa1 := by linarith [ht.1]
  -- pointwise facts on the whole box
  have hosc : ∀ u ∈ Set.Icc kappa2 (1 / 2 - 3*kappa1),
      |f ((1 / 2 - t - u)/kappa1) - f ((1 / 2 - t0 - u)/kappa1)| ≤ ε1 := by
    intro u hu
    exact hγ1prop t htbox u hu t0 ht0 u hu
      (by rw [sub_self, abs_zero, add_zero]; exact le_trans hdist' hδγ1)
  have hbd_t : ∀ u ∈ Set.Icc kappa2 (1 / 2 - 3*kappa1),
      |f ((1 / 2 - t - u)/kappa1)| ≤ C0 := fun u hu => hC0 (t, u) ⟨htbox, hu⟩
  have hbd_t0 : ∀ u ∈ Set.Icc kappa2 (1 / 2 - 3*kappa1),
      |f ((1 / 2 - t0 - u)/kappa1)| ≤ C0 := fun u hu => hC0 (t0, u) ⟨ht0, hu⟩
  -- the band bounds
  have hpt_t : ∀ a b : ℝ, kappa2 ≤ a → a ≤ b → b ≤ 1 / 2 - 3*kappa1 →
      ∀ u ∈ Set.uIoc a b, ‖f ((1 / 2 - t - u)/kappa1)/u‖ ≤ C0 / kappa2 := by
    intro a b ha hab hb u hu
    rw [Set.uIoc_of_le hab] at hu
    have huI : u ∈ Set.Icc kappa2 (1 / 2 - 3*kappa1) :=
      ⟨le_trans ha (le_of_lt hu.1), le_trans hu.2 hb⟩
    have hupos : (0:ℝ) < u := lt_of_lt_of_le hk2 huI.1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hupos, div_le_div_iff₀ hupos hk2]
    have h1 : |f ((1 / 2 - t - u)/kappa1)| * kappa2 ≤ C0 * kappa2 :=
      mul_le_mul_of_nonneg_right (hbd_t u huI) (le_of_lt hk2)
    have h2 : C0 * kappa2 ≤ C0 * u := mul_le_mul_of_nonneg_left huI.1 hCnn
    linarith
  have hpt_t0 : ∀ a b : ℝ, kappa2 ≤ a → a ≤ b → b ≤ 1 / 2 - 3*kappa1 →
      ∀ u ∈ Set.uIoc a b, ‖f ((1 / 2 - t0 - u)/kappa1)/u‖ ≤ C0 / kappa2 := by
    intro a b ha hab hb u hu
    rw [Set.uIoc_of_le hab] at hu
    have huI : u ∈ Set.Icc kappa2 (1 / 2 - 3*kappa1) :=
      ⟨le_trans ha (le_of_lt hu.1), le_trans hu.2 hb⟩
    have hupos : (0:ℝ) < u := lt_of_lt_of_le hk2 huI.1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hupos, div_le_div_iff₀ hupos hk2]
    have h1 : |f ((1 / 2 - t0 - u)/kappa1)| * kappa2 ≤ C0 * kappa2 :=
      mul_le_mul_of_nonneg_right (hbd_t0 u huI) (le_of_lt hk2)
    have h2 : C0 * kappa2 ≤ C0 * u := mul_le_mul_of_nonneg_left huI.1 hCnn
    linarith
  have hpt_d : ∀ a b : ℝ, kappa2 ≤ a → a ≤ b → b ≤ 1 / 2 - 3*kappa1 →
      ∀ u ∈ Set.uIoc a b,
        ‖f ((1 / 2 - t - u)/kappa1)/u - f ((1 / 2 - t0 - u)/kappa1)/u‖ ≤ ε1 / kappa2 := by
    intro a b ha hab hb u hu
    rw [Set.uIoc_of_le hab] at hu
    have huI : u ∈ Set.Icc kappa2 (1 / 2 - 3*kappa1) :=
      ⟨le_trans ha (le_of_lt hu.1), le_trans hu.2 hb⟩
    have hupos : (0:ℝ) < u := lt_of_lt_of_le hk2 huI.1
    have hβ : f ((1 / 2 - t - u)/kappa1)/u - f ((1 / 2 - t0 - u)/kappa1)/u
        = (f ((1 / 2 - t - u)/kappa1) - f ((1 / 2 - t0 - u)/kappa1))/u := by ring
    rw [Real.norm_eq_abs, hβ, abs_div, abs_of_pos hupos, div_le_div_iff₀ hupos hk2]
    have h1 : |f ((1 / 2 - t - u)/kappa1) - f ((1 / 2 - t0 - u)/kappa1)| * kappa2
        ≤ ε1 * kappa2 := mul_le_mul_of_nonneg_right (hosc u huI) (le_of_lt hk2)
    have h2 : ε1 * kappa2 ≤ ε1 * u := mul_le_mul_of_nonneg_left huI.1 (le_of_lt hε1)
    linarith
  -- continuity of the two integrands
  have hcont_t : ContinuousOn (fun u : ℝ => f ((1 / 2 - t - u)/kappa1)/u)
      (Set.Icc kappa2 (1 / 2 - 3*kappa1)) :=
    psiIntegrand_continuous h.2.1 htbox (le_refl kappa2) hk2U (le_refl _)
  have hcont_t0 : ContinuousOn (fun u : ℝ => f ((1 / 2 - t0 - u)/kappa1)/u)
      (Set.Icc kappa2 (1 / 2 - 3*kappa1)) :=
    psiIntegrand_continuous h.2.1 ht0 (le_refl kappa2) hk2U (le_refl _)
  have mono_int : ∀ (g : ℝ → ℝ) (a b : ℝ),
      ContinuousOn g (Set.Icc kappa2 (1 / 2 - 3*kappa1)) →
      kappa2 ≤ a → a ≤ b → b ≤ 1 / 2 - 3*kappa1 → IntervalIntegrable g volume a b := by
    intro g a b hg ha hab hb
    exact (hg.mono (fun x hx => ⟨le_trans ha hx.1, le_trans hx.2 hb⟩)).intervalIntegrable_of_Icc hab
  rcases le_total t0 t with hle | hle
  · -- `t0 ≤ t`: the cutoff `c` is below `c0`
    have hcc : 1 / 2 - 2*kappa1 - t ≤ 1 / 2 - 2*kappa1 - t0 := by linarith
    have h1 : IntervalIntegrable (fun u => f ((1 / 2 - t - u)/kappa1)/u) volume
        kappa2 (1/2 - 2*kappa1 - t) := mono_int _ _ _ hcont_t (le_refl _) hclo hchi
    have h2 : IntervalIntegrable (fun u => f ((1 / 2 - t - u)/kappa1)/u) volume
        (1/2 - 2*kappa1 - t) (1/2 - 2*kappa1 - t0) := mono_int _ _ _ hcont_t hclo hcc hc0hi
    have h3 : IntervalIntegrable (fun u => f ((1 / 2 - t0 - u)/kappa1)/u) volume
        kappa2 (1/2 - 2*kappa1 - t) := mono_int _ _ _ hcont_t0 (le_refl _) hclo hchi
    have h4 : IntervalIntegrable (fun u => f ((1 / 2 - t0 - u)/kappa1)/u) volume
        (1/2 - 2*kappa1 - t) (1/2 - 2*kappa1 - t0) := mono_int _ _ _ hcont_t0 hclo hcc hc0hi
    have hA : (∫ u in kappa2..(1/2 - 2*kappa1 - t0), f ((1 / 2 - t0 - u)/kappa1)/u)
        = (∫ u in kappa2..(1/2 - 2*kappa1 - t), f ((1 / 2 - t0 - u)/kappa1)/u)
          + ∫ u in (1/2 - 2*kappa1 - t)..(1/2 - 2*kappa1 - t0), f ((1 / 2 - t0 - u)/kappa1)/u := by
      rw [intervalIntegral.integral_add_adjacent_intervals h3 h4]
    have hB : (∫ u in kappa2..(1/2 - 2*kappa1 - t), f ((1 / 2 - t - u)/kappa1)/u)
        - (∫ u in kappa2..(1/2 - 2*kappa1 - t), f ((1 / 2 - t0 - u)/kappa1)/u)
        = ∫ u in kappa2..(1/2 - 2*kappa1 - t),
            (f ((1 / 2 - t - u)/kappa1)/u - f ((1 / 2 - t0 - u)/kappa1)/u) := by
      rw [intervalIntegral.integral_sub h1 h3]
    have hb1 : |(∫ u in kappa2..(1/2 - 2*kappa1 - t),
        (f ((1 / 2 - t - u)/kappa1)/u - f ((1 / 2 - t0 - u)/kappa1)/u))|
        ≤ ε1 / kappa2 * (1 / 2 - 2*kappa1 - t - kappa2) := by
      rw [← Real.norm_eq_abs]
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (hpt_d kappa2 (1/2 - 2*kappa1 - t) (le_refl _) hclo hchi)
      calc ‖∫ u in kappa2..(1/2 - 2*kappa1 - t),
            (f ((1 / 2 - t - u)/kappa1)/u - f ((1 / 2 - t0 - u)/kappa1)/u)‖
          ≤ ε1 / kappa2 * |(1/2 - 2*kappa1 - t) - kappa2| := h
        _ = ε1 / kappa2 * (1 / 2 - 2*kappa1 - t - kappa2) := by
            rw [abs_of_nonneg (by linarith)]
    have hb2 : |(∫ u in (1/2 - 2*kappa1 - t)..(1/2 - 2*kappa1 - t0),
        f ((1 / 2 - t0 - u)/kappa1)/u)| ≤ C0 / kappa2 * (t - t0) := by
      rw [← Real.norm_eq_abs]
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (hpt_t0 (1/2 - 2*kappa1 - t) (1/2 - 2*kappa1 - t0) hclo hcc hc0hi)
      calc ‖∫ u in (1/2 - 2*kappa1 - t)..(1/2 - 2*kappa1 - t0),
            f ((1 / 2 - t0 - u)/kappa1)/u‖
          ≤ C0 / kappa2 * |(1/2 - 2*kappa1 - t0) - (1/2 - 2*kappa1 - t)| := h
        _ = C0 / kappa2 * (t - t0) := by
            rw [show (1/2 - 2*kappa1 - t0) - (1/2 - 2*kappa1 - t) = t - t0 by ring,
              abs_of_nonneg (by linarith)]
    have hsplit : (∫ u in kappa2..(1 / 2 - 2*kappa1 - t), f ((1 / 2 - t - u)/kappa1)/u)
        - (∫ u in kappa2..(1 / 2 - 2*kappa1 - t0), f ((1 / 2 - t0 - u)/kappa1)/u)
        = (∫ u in kappa2..(1/2 - 2*kappa1 - t),
              (f ((1 / 2 - t - u)/kappa1)/u - f ((1 / 2 - t0 - u)/kappa1)/u))
            - ∫ u in (1/2 - 2*kappa1 - t)..(1/2 - 2*kappa1 - t0), f ((1 / 2 - t0 - u)/kappa1)/u := by
      rw [hA]
      have he : (∫ u in kappa2..(1 / 2 - 2*kappa1 - t), f ((1 / 2 - t - u)/kappa1)/u)
            - ((∫ u in kappa2..(1 / 2 - 2*kappa1 - t), f ((1 / 2 - t0 - u)/kappa1)/u)
              + ∫ u in (1/2 - 2*kappa1 - t)..(1/2 - 2*kappa1 - t0),
                  f ((1 / 2 - t0 - u)/kappa1)/u)
          = ((∫ u in kappa2..(1 / 2 - 2*kappa1 - t), f ((1 / 2 - t - u)/kappa1)/u)
              - (∫ u in kappa2..(1 / 2 - 2*kappa1 - t), f ((1 / 2 - t0 - u)/kappa1)/u))
            - ∫ u in (1/2 - 2*kappa1 - t)..(1/2 - 2*kappa1 - t0),
                f ((1 / 2 - t0 - u)/kappa1)/u := by ring
      rw [he, hB]
    have hmain : |(∫ u in kappa2..(1 / 2 - 2*kappa1 - t), f ((1 / 2 - t - u)/kappa1)/u)
        - (∫ u in kappa2..(1 / 2 - 2*kappa1 - t0), f ((1 / 2 - t0 - u)/kappa1)/u)|
        ≤ ε1 / kappa2 * (1 / 2 - 2*kappa1 - t - kappa2) + C0 / kappa2 * (t - t0) := by
      rw [hsplit, sub_eq_add_neg]
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_neg]
      exact add_le_add hb1 hb2
    have hst1 : ε1 / kappa2 * (1 / 2 - 2*kappa1 - t - kappa2)
        ≤ ε1 * (1 / 2 - 3*kappa1 - kappa2) / kappa2 := by
      have hle' : 1 / 2 - 2*kappa1 - t - kappa2 ≤ 1 / 2 - 3*kappa1 - kappa2 := by
        linarith [ht.1]
      calc ε1 / kappa2 * (1 / 2 - 2*kappa1 - t - kappa2)
          ≤ ε1 / kappa2 * (1 / 2 - 3*kappa1 - kappa2) :=
            mul_le_mul_of_nonneg_left hle' (by positivity)
        _ = ε1 * (1 / 2 - 3*kappa1 - kappa2) / kappa2 := by ring
    have hsm : C0 / kappa2 * (t - t0) ≤ ε / 4 := by
      have h1 : t - t0 ≤ δ := le_trans (le_abs_self _) hdist'
      have h2 : C0 / kappa2 * δ = C0 * δ / kappa2 := by ring
      have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ C0 / kappa2)
      linarith [hδC, h3, h2]
    have hlt : ε1 / kappa2 * (1 / 2 - 2*kappa1 - t - kappa2) + C0 / kappa2 * (t - t0) < ε := by
      linarith [hst1, hε1U, hsm, hε]
    rw [Real.dist_eq]
    exact lt_of_le_of_lt hmain hlt
  · -- `t ≤ t0`: the cutoff `c0` is below `c`
    have hcc : 1 / 2 - 2*kappa1 - t0 ≤ 1 / 2 - 2*kappa1 - t := by linarith
    have h1 : IntervalIntegrable (fun u => f ((1 / 2 - t - u)/kappa1)/u) volume
        kappa2 (1/2 - 2*kappa1 - t0) := mono_int _ _ _ hcont_t (le_refl _) hc0lo hc0hi
    have h2 : IntervalIntegrable (fun u => f ((1 / 2 - t - u)/kappa1)/u) volume
        (1/2 - 2*kappa1 - t0) (1/2 - 2*kappa1 - t) := mono_int _ _ _ hcont_t hc0lo hcc hchi
    have h3 : IntervalIntegrable (fun u => f ((1 / 2 - t0 - u)/kappa1)/u) volume
        kappa2 (1/2 - 2*kappa1 - t0) := mono_int _ _ _ hcont_t0 (le_refl _) hc0lo hc0hi
    have hA : (∫ u in kappa2..(1/2 - 2*kappa1 - t), f ((1 / 2 - t - u)/kappa1)/u)
        = (∫ u in kappa2..(1/2 - 2*kappa1 - t0), f ((1 / 2 - t - u)/kappa1)/u)
          + ∫ u in (1/2 - 2*kappa1 - t0)..(1/2 - 2*kappa1 - t), f ((1 / 2 - t - u)/kappa1)/u := by
      rw [intervalIntegral.integral_add_adjacent_intervals h1 h2]
    have hB : (∫ u in kappa2..(1/2 - 2*kappa1 - t0), f ((1 / 2 - t - u)/kappa1)/u)
        - (∫ u in kappa2..(1/2 - 2*kappa1 - t0), f ((1 / 2 - t0 - u)/kappa1)/u)
        = ∫ u in kappa2..(1/2 - 2*kappa1 - t0),
            (f ((1 / 2 - t - u)/kappa1)/u - f ((1 / 2 - t0 - u)/kappa1)/u) := by
      rw [intervalIntegral.integral_sub h1 h3]
    have hb1 : |(∫ u in kappa2..(1/2 - 2*kappa1 - t0),
        (f ((1 / 2 - t - u)/kappa1)/u - f ((1 / 2 - t0 - u)/kappa1)/u))|
        ≤ ε1 / kappa2 * (1 / 2 - 2*kappa1 - t0 - kappa2) := by
      rw [← Real.norm_eq_abs]
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (hpt_d kappa2 (1/2 - 2*kappa1 - t0) (le_refl _) hc0lo hc0hi)
      calc ‖∫ u in kappa2..(1/2 - 2*kappa1 - t0),
            (f ((1 / 2 - t - u)/kappa1)/u - f ((1 / 2 - t0 - u)/kappa1)/u)‖
          ≤ ε1 / kappa2 * |(1/2 - 2*kappa1 - t0) - kappa2| := h
        _ = ε1 / kappa2 * (1 / 2 - 2*kappa1 - t0 - kappa2) := by
            rw [abs_of_nonneg (by linarith)]
    have hb2 : |(∫ u in (1/2 - 2*kappa1 - t0)..(1/2 - 2*kappa1 - t),
        f ((1 / 2 - t - u)/kappa1)/u)| ≤ C0 / kappa2 * (t0 - t) := by
      rw [← Real.norm_eq_abs]
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (hpt_t (1/2 - 2*kappa1 - t0) (1/2 - 2*kappa1 - t) hc0lo hcc hchi)
      calc ‖∫ u in (1/2 - 2*kappa1 - t0)..(1/2 - 2*kappa1 - t),
            f ((1 / 2 - t - u)/kappa1)/u‖
          ≤ C0 / kappa2 * |(1/2 - 2*kappa1 - t) - (1/2 - 2*kappa1 - t0)| := h
        _ = C0 / kappa2 * (t0 - t) := by
            rw [show (1/2 - 2*kappa1 - t) - (1/2 - 2*kappa1 - t0) = t0 - t by ring,
              abs_of_nonneg (by linarith)]
    have hsplit : (∫ u in kappa2..(1 / 2 - 2*kappa1 - t), f ((1 / 2 - t - u)/kappa1)/u)
        - (∫ u in kappa2..(1 / 2 - 2*kappa1 - t0), f ((1 / 2 - t0 - u)/kappa1)/u)
        = (∫ u in kappa2..(1/2 - 2*kappa1 - t0),
              (f ((1 / 2 - t - u)/kappa1)/u - f ((1 / 2 - t0 - u)/kappa1)/u))
            + ∫ u in (1/2 - 2*kappa1 - t0)..(1/2 - 2*kappa1 - t), f ((1 / 2 - t - u)/kappa1)/u := by
      rw [hA]
      have he : ((∫ u in kappa2..(1 / 2 - 2*kappa1 - t0), f ((1 / 2 - t - u)/kappa1)/u)
              + ∫ u in (1/2 - 2*kappa1 - t0)..(1/2 - 2*kappa1 - t),
                  f ((1 / 2 - t - u)/kappa1)/u)
            - (∫ u in kappa2..(1 / 2 - 2*kappa1 - t0), f ((1 / 2 - t0 - u)/kappa1)/u)
          = ((∫ u in kappa2..(1 / 2 - 2*kappa1 - t0), f ((1 / 2 - t - u)/kappa1)/u)
              - (∫ u in kappa2..(1 / 2 - 2*kappa1 - t0), f ((1 / 2 - t0 - u)/kappa1)/u))
            + ∫ u in (1/2 - 2*kappa1 - t0)..(1/2 - 2*kappa1 - t),
                f ((1 / 2 - t - u)/kappa1)/u := by ring
      rw [he, hB]
    have hmain : |(∫ u in kappa2..(1 / 2 - 2*kappa1 - t), f ((1 / 2 - t - u)/kappa1)/u)
        - (∫ u in kappa2..(1 / 2 - 2*kappa1 - t0), f ((1 / 2 - t0 - u)/kappa1)/u)|
        ≤ ε1 / kappa2 * (1 / 2 - 2*kappa1 - t0 - kappa2) + C0 / kappa2 * (t0 - t) := by
      rw [hsplit]
      refine le_trans (abs_add_le _ _) ?_
      exact add_le_add hb1 hb2
    have hst1 : ε1 / kappa2 * (1 / 2 - 2*kappa1 - t0 - kappa2)
        ≤ ε1 * (1 / 2 - 3*kappa1 - kappa2) / kappa2 := by
      have hle' : 1 / 2 - 2*kappa1 - t0 - kappa2 ≤ 1 / 2 - 3*kappa1 - kappa2 := by
        linarith [ht0.1]
      calc ε1 / kappa2 * (1 / 2 - 2*kappa1 - t0 - kappa2)
          ≤ ε1 / kappa2 * (1 / 2 - 3*kappa1 - kappa2) :=
            mul_le_mul_of_nonneg_left hle' (by positivity)
        _ = ε1 * (1 / 2 - 3*kappa1 - kappa2) / kappa2 := by ring
    have hsm : C0 / kappa2 * (t0 - t) ≤ ε / 4 := by
      have h1 : t0 - t ≤ δ := by
        have h2 : |t0 - t| ≤ δ := by
          rw [abs_sub_comm]
          exact hdist'
        exact le_trans (le_abs_self (t0 - t)) h2
      have h2 : C0 / kappa2 * δ = C0 * δ / kappa2 := by ring
      have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ C0 / kappa2)
      linarith [hδC, h3, h2]
    have hlt : ε1 / kappa2 * (1 / 2 - 2*kappa1 - t0 - kappa2) + C0 / kappa2 * (t0 - t) < ε := by
      linarith [hst1, hε1U, hsm, hε]
    rw [Real.dist_eq]
    exact lt_of_le_of_lt hmain hlt

/-- Uniform modulus of the inner `u`-integral on the exponent interval. -/
private lemma psi_uniform (F f : ℝ → ℝ) (h : Wu04Functional.IsLinearSieve F f) :
    ∀ ε : ℝ, 0 < ε → ∃ γ : ℝ, 0 < γ ∧
      ∀ t ∈ Set.Icc kappa1 kappa2, ∀ t' ∈ Set.Icc kappa1 kappa2, |t - t'| ≤ γ →
        |(∫ u in kappa2..(1 / 2 - 2*kappa1 - t), f ((1 / 2 - t - u)/kappa1)/u)
          - (∫ u in kappa2..(1 / 2 - 2*kappa1 - t'), f ((1 / 2 - t' - u)/kappa1)/u)| ≤ ε := by
  have hc := psi_continuousOn F f h
  have huc : UniformContinuousOn (fun t : ℝ => ∫ u in kappa2..(1 / 2 - 2*kappa1 - t),
      f ((1 / 2 - t - u)/kappa1)/u) (Set.Icc kappa1 kappa2) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hc
  intro ε hε
  obtain ⟨γ, hγ, hγp⟩ := Metric.uniformContinuousOn_iff_le.mp huc ε hε
  refine ⟨γ, hγ, ?_⟩
  intro t ht t' ht' hd
  have h := hγp t ht t' ht' (by rwa [Real.dist_eq])
  simpa [Real.dist_eq] using h

/-- The `q`-band sum with a fixed continuous weight converges to its integral. This is
`band_weight` rewritten in the integer-box form used by the mesh. -/
private lemma q_band_limit {K : ℝ → ℝ → ℝ} {U U' ξ : ℝ} (hU : 0 < U) (hUU' : U < U')
    (hcont : ContinuousOn (fun u : ℝ => K ξ u) (Set.Icc U U')) :
    Tendsto (fun N : ℕ =>
      ∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
        K ξ (Real.log (q:ℝ)/Real.log (N:ℝ)) * (((q:ℝ) - 1))⁻¹) atTop
      (𝓝 (∫ u in U..U', K ξ u / u)) := by
  have h := band_weight U U' hU hUU' (fun u => K ξ u) hcont
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNval : (0:ℝ) ≤ (N:ℝ)^U := le_of_lt (rpow_pos_of_pos hNpos U)
  have hset : (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q)
      = (Finset.Ioc 0 ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q ∧ (N:ℝ)^U < (q:ℝ)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp⟩
      exact ⟨⟨hp.pos, h2⟩, hp, (lt_floor_iff hNval).mp h1⟩
    · rintro ⟨⟨h0, h2⟩, hp, h1⟩
      exact ⟨⟨(lt_floor_iff hNval).mpr h1, h2⟩, hp⟩
  rw [hset]

/-- One mesh cell: the double sum over the `p`-cell and the `q`-band is the log length of the
`p`-cell times the inner integral, up to the two mesh errors. -/
private lemma cell_limit_close {K : ℝ → ℝ → ℝ} {T T' U U' ξ E η εR : ℝ}
    (hT : 0 < T) (hTT' : T < T') (hU : 0 < U) (hUU' : U < U')
    (hξ : ξ ∈ Set.Icc T T') (hE : 0 ≤ E) (hη : 0 < η)
    (hnear : ∀ᶠ N : ℕ in atTop, ∀ u : ℝ,
      |(∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p),
          K (Real.log (p:ℝ)/Real.log (N:ℝ)) u * (((p:ℝ) - 1))⁻¹)
        - K ξ u * (Real.log T' - Real.log T)| ≤ E)
    (hmass : ∀ᶠ N : ℕ in atTop,
      (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
          (((q:ℝ) - 1))⁻¹) ≤ Real.log U' - Real.log U + η)
    (hR : ∀ᶠ N : ℕ in atTop,
      |(∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
          K ξ (Real.log (q:ℝ)/Real.log (N:ℝ)) * (((q:ℝ) - 1))⁻¹)
        - (∫ u in U..U', K ξ u / u)| ≤ εR) :
    ∀ᶠ N : ℕ in atTop,
      |(∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p),
          ∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
            K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
              * (((p:ℝ) - 1))⁻¹ * (((q:ℝ) - 1))⁻¹)
        - (Real.log T' - Real.log T) * (∫ u in U..U', K ξ u / u)|
      ≤ (Real.log U' - Real.log U + η) * E + |Real.log T' - Real.log T| * εR := by
  have h1 := cell_pair_sum_close (K := K) hT hTT' hU hUU' hξ hE hη hnear hmass
  filter_upwards [h1, hR] with N hN1 hN2
  have h2 : |(Real.log T' - Real.log T) *
        (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
          K ξ (Real.log (q:ℝ)/Real.log (N:ℝ)) * (((q:ℝ) - 1))⁻¹)
      - (Real.log T' - Real.log T) * (∫ u in U..U', K ξ u / u)|
      ≤ |Real.log T' - Real.log T| * εR := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left hN2 (abs_nonneg _)
  exact le_trans (abs_sub_le _ _ _) (add_le_add hN1 h2)

/-- The `p`-side of the region sum splits into the mesh cells. -/
private lemma box_cell_split {K : ℝ → ℝ → ℝ} {h : ℝ} (hhpos : 0 < h) {m : ℕ}
    (hmh : (m:ℝ)*h = kappa2 - kappa1) (N : ℕ) (hN : 2 ≤ N) :
    (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^kappa1⌋₊ ⌊(N:ℝ)^kappa2⌋₊).filter (fun p => Nat.Prime p),
      ∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^(1/2-2*kappa1)⌋₊).filter (fun q => Nat.Prime q),
        K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
          * (((p:ℝ) - 1))⁻¹ * (((q:ℝ) - 1))⁻¹)
      = ∑ i ∈ Finset.range m,
          ∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^(kappa1 + (i:ℝ)*h)⌋₊
              ⌊(N:ℝ)^(kappa1 + ((i:ℝ)+1)*h)⌋₊).filter (fun p => Nat.Prime p),
            ∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^(1/2-2*kappa1)⌋₊).filter
                (fun q => Nat.Prime q),
              K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
                * (((p:ℝ) - 1))⁻¹ * (((q:ℝ) - 1))⁻¹ := by
  have hk1 : (0:ℝ) < kappa1 := by norm_num [kappa1_val]
  exact band_sum_chain kappa1 kappa2 h hk1 hhpos m hmh _ N hN


/-- A uniform logarithmic mesh with a uniformly continuous weight: the mesh sum differs from the
integral by at most the oscillation bound times `log (κ₂/κ₁)`. -/
private lemma mesh_vs_integral {Ψ : ℝ → ℝ} {h ω : ℝ} (hhpos : 0 < h) {m : ℕ}
    (hmh : (m:ℝ)*h = kappa2 - kappa1) (ξ : ℕ → ℝ)
    (hξ : ∀ i ∈ Finset.range m,
      ξ i ∈ Set.Icc (kappa1 + (i:ℝ)*h) (kappa1 + ((i:ℝ)+1)*h))
    (hcont : ContinuousOn Ψ (Set.Icc kappa1 kappa2))
    (hω : ∀ t ∈ Set.Icc kappa1 kappa2, ∀ t' ∈ Set.Icc kappa1 kappa2,
      |t - t'| ≤ h → |Ψ t - Ψ t'| ≤ ω) :
    |(∑ i ∈ Finset.range m,
        Real.log ((kappa1 + ((i:ℝ)+1)*h)/(kappa1 + (i:ℝ)*h)) * Ψ (ξ i))
      - (∫ t in kappa1..kappa2, Ψ t / t)| ≤ ω * Real.log (kappa2 / kappa1) := by
  have hk1 : (0:ℝ) < kappa1 := by norm_num [kappa1_val]
  -- the mesh points
  have hstep : ∀ i : ℕ, (kappa1 + ((i:ℝ)+1)*h) - (kappa1 + (i:ℝ)*h) = h := by
    intro i; ring
  have hsucc : ∀ i (hi : i ∈ Finset.range m), ((i:ℝ)+1) ≤ (m:ℝ) := by
    intro i hi
    have hlt : i < m := Finset.mem_range.mp hi
    have h2 : ((i + 1 : ℕ) : ℝ) ≤ ((m : ℕ) : ℝ) := by
      exact_mod_cast (show i + 1 ≤ m from hlt)
    simpa [Nat.cast_add, Nat.cast_one] using h2
  have hTle : ∀ i ∈ Finset.range m, kappa1 + ((i:ℝ)+1)*h ≤ kappa2 := by
    intro i hi
    have h3 : ((i:ℝ)+1)*h ≤ (m:ℝ)*h :=
      mul_le_mul_of_nonneg_right (hsucc i hi) (le_of_lt hhpos)
    calc kappa1 + ((i:ℝ)+1)*h ≤ kappa1 + (m:ℝ)*h := by linarith
      _ = kappa2 := by rw [hmh]; ring
  have hTlo : ∀ i : ℕ, kappa1 ≤ kappa1 + (i:ℝ)*h := by
    intro i
    have h0 : (0:ℝ) ≤ (i:ℝ)*h := mul_nonneg (by positivity) (le_of_lt hhpos)
    linarith
  have hTmono : ∀ i : ℕ, kappa1 + (i:ℝ)*h ≤ kappa1 + ((i:ℝ)+1)*h := by
    intro i
    have h0 : (i:ℝ) ≤ (i:ℝ)+1 := by linarith
    have h1 : (i:ℝ)*h ≤ ((i:ℝ)+1)*h := mul_le_mul_of_nonneg_right h0 (le_of_lt hhpos)
    linarith
  have hTpos : ∀ i ∈ Finset.range m,
      (0:ℝ) < kappa1 + (i:ℝ)*h ∧ (0:ℝ) < kappa1 + ((i:ℝ)+1)*h := by
    intro i hi
    constructor
    · have := hTlo i; linarith
    · have h1 := hTmono i
      have h2 := hTlo i
      linarith
  -- each reference term is the integral of the constant weight
  have hterms : ∀ i ∈ Finset.range m,
      Real.log ((kappa1 + ((i:ℝ)+1)*h)/(kappa1 + (i:ℝ)*h)) * Ψ (ξ i)
        = ∫ t in (kappa1 + (i:ℝ)*h)..(kappa1 + ((i:ℝ)+1)*h), Ψ (ξ i) / t := by
    intro i hi
    obtain ⟨ha, hb⟩ := hTpos i hi
    have hlog : Real.log ((kappa1 + ((i:ℝ)+1)*h)/(kappa1 + (i:ℝ)*h))
        = Real.log (kappa1 + ((i:ℝ)+1)*h) - Real.log (kappa1 + (i:ℝ)*h) :=
      Real.log_div (ne_of_gt hb) (ne_of_gt ha)
    rw [hlog, show (fun t : ℝ => Ψ (ξ i) / t) = (fun t : ℝ => Ψ (ξ i) * t⁻¹) from by
      funext t; rw [div_eq_mul_inv]]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha hb]
    have hb' : kappa1 + ((i:ℝ)+1)*h = kappa1 + (i:ℝ)*h + h := by ring
    have hb0 : (0:ℝ) < kappa1 + (i:ℝ)*h + h := by linarith [ha, hhpos]
    rw [hb', Real.log_div (ne_of_gt hb0) (ne_of_gt ha)]
    ring
  -- the cell error
  have hcell : ∀ i ∈ Finset.range m,
      |(∫ t in (kappa1 + (i:ℝ)*h)..(kappa1 + ((i:ℝ)+1)*h), Ψ (ξ i) / t)
        - (∫ t in (kappa1 + (i:ℝ)*h)..(kappa1 + ((i:ℝ)+1)*h), Ψ t / t)|
      ≤ ω * Real.log ((kappa1 + ((i:ℝ)+1)*h)/(kappa1 + (i:ℝ)*h)) := by
    intro i hi
    obtain ⟨ha, hb⟩ := hTpos i hi
    have hab : kappa1 + (i:ℝ)*h ≤ kappa1 + ((i:ℝ)+1)*h := hTmono i
    have hineq := hTle i hi
    have hne : ∀ t ∈ Set.Icc (kappa1 + (i:ℝ)*h) (kappa1 + ((i:ℝ)+1)*h), t ≠ 0 :=
      fun t ht => ne_of_gt (lt_of_lt_of_le ha ht.1)
    have hcont1 : ContinuousOn (fun t : ℝ => Ψ (ξ i) / t)
        (Set.Icc (kappa1 + (i:ℝ)*h) (kappa1 + ((i:ℝ)+1)*h)) :=
      continuousOn_const.div continuous_id.continuousOn hne
    have hcont2 : ContinuousOn (fun t : ℝ => Ψ t / t)
        (Set.Icc (kappa1 + (i:ℝ)*h) (kappa1 + ((i:ℝ)+1)*h)) :=
      (hcont.mono (fun t ht => ⟨by linarith [ht.1, hTlo i], le_trans ht.2 hineq⟩)).div
        continuous_id.continuousOn hne
    rw [← intervalIntegral.integral_sub
      (ContinuousOn.intervalIntegrable_of_Icc hab hcont1)
      (ContinuousOn.intervalIntegrable_of_Icc hab hcont2)]
    refine le_trans (intervalIntegral.abs_integral_le_integral_abs hab) ?_
    have hpt : ∀ t ∈ Set.Icc (kappa1 + (i:ℝ)*h) (kappa1 + ((i:ℝ)+1)*h),
        |Ψ (ξ i) / t - Ψ t / t| ≤ ω * t⁻¹ := by
      intro t ht
      have htpos : (0:ℝ) < t := lt_of_lt_of_le ha ht.1
      have htI : t ∈ Set.Icc kappa1 kappa2 :=
        ⟨by linarith [ht.1, hTlo i], le_trans ht.2 hineq⟩
      have hξI := hξ i hi
      have hξI' : ξ i ∈ Set.Icc kappa1 kappa2 :=
        ⟨by linarith [hξI.1, hTlo i], le_trans hξI.2 hineq⟩
      have hd : |ξ i - t| ≤ h := by
        have hs := hstep i
        rw [abs_le]
        constructor <;> linarith [hξI.1, hξI.2, ht.1, ht.2, hs]
      have hosc := hω (ξ i) hξI' t htI hd
      rw [show Ψ (ξ i) / t - Ψ t / t = (Ψ (ξ i) - Ψ t) / t by ring, abs_div,
        abs_of_pos htpos, div_le_iff₀ htpos]
      rw [show ω * t⁻¹ * t = ω by field_simp]
      exact hosc
    have hg : ContinuousOn (fun t : ℝ => ω * t⁻¹)
        (Set.Icc (kappa1 + (i:ℝ)*h) (kappa1 + ((i:ℝ)+1)*h)) :=
      continuousOn_const.mul (continuousOn_id.inv₀ hne)
    refine le_trans (intervalIntegral.integral_mono_on hab
      ((hcont1.sub hcont2).abs.intervalIntegrable_of_Icc hab)
      (hg.intervalIntegrable_of_Icc hab) hpt) ?_
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha hb]
  -- assemble
  have h1 : (∑ i ∈ Finset.range m,
        Real.log ((kappa1 + ((i:ℝ)+1)*h)/(kappa1 + (i:ℝ)*h)) * Ψ (ξ i))
      = ∑ i ∈ Finset.range m,
          ∫ t in (kappa1 + (i:ℝ)*h)..(kappa1 + ((i:ℝ)+1)*h), Ψ (ξ i) / t :=
    Finset.sum_congr rfl hterms
  have hsplit := integral_chain_cont kappa1 kappa2 h hk1 hhpos m hmh Ψ hcont
  rw [h1, hsplit, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hcell) ?_
  rw [← Finset.mul_sum]
  rw [sum_log_ratio kappa1 kappa2 h hk1 hhpos m hmh]


/-- The `q`-boundary band of one mesh cell has mass `O(h)`: this is the price of replacing the
moving cutoff `1/2 - 2κ₁ - t_p` by the cell cutoff `1/2 - 2κ₁ - T`. -/
private lemma boundary_band_mass {T T' : ℝ} (hT : 0 < T) (hTT' : T < T')
    (hT' : T' ≤ kappa2) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^(1/2 - 2*kappa1 - T')⌋₊
          ⌊(N:ℝ)^(1/2 - 2*kappa1 - T)⌋₊).filter (fun p => Nat.Prime p),
        (((p:ℝ) - 1))⁻¹) ≤ 2 * (T' - T) / kappa2 + η := by
  have hk2 : (0:ℝ) < kappa2 := by norm_num [kappa2_val]
  have hcore : (0:ℝ) < 1/2 - 2*kappa1 - kappa2 := by norm_num [kappa1_val, kappa2_val]
  have ha : (0:ℝ) < 1/2 - 2*kappa1 - T' := by linarith
  have hab : 1/2 - 2*kappa1 - T' < 1/2 - 2*kappa1 - T := by linarith
  have hhalf : kappa2 / 2 ≤ 1/2 - 2*kappa1 - T' := by
    have h1 : kappa2 / 2 ≤ 1/2 - 2*kappa1 - kappa2 := by norm_num [kappa1_val, kappa2_val]
    linarith
  have hquot : (1/2 - 2*kappa1 - T)/(1/2 - 2*kappa1 - T')
      = 1 + (T' - T)/(1/2 - 2*kappa1 - T') := by
    have hb_eq : 1/2 - 2*kappa1 - T = (1/2 - 2*kappa1 - T') + (T' - T) := by ring
    rw [hb_eq, add_div, div_self (ne_of_gt ha)]
  have hlog : Real.log ((1/2 - 2*kappa1 - T)/(1/2 - 2*kappa1 - T'))
      ≤ 2 * (T' - T) / kappa2 := by
    rw [hquot]
    have hx0 : (0:ℝ) ≤ (T' - T)/(1/2 - 2*kappa1 - T') := by positivity
    have hx : (0:ℝ) < 1 + (T' - T)/(1/2 - 2*kappa1 - T') := by linarith
    have h1 := Real.log_le_sub_one_of_pos hx
    have h2 : (T' - T)/(1/2 - 2*kappa1 - T') ≤ (T' - T)/(kappa2/2) := by
      apply div_le_div_of_nonneg_left (by linarith) (by linarith) hhalf
    have h3 : (T' - T)/(kappa2/2) = 2 * (T' - T) / kappa2 := by
      field_simp
    linarith
  filter_upwards [cell_mass_le ha hab hη] with N hN
  refine le_trans hN ?_
  have hdiff : Real.log (1/2 - 2*kappa1 - T) - Real.log (1/2 - 2*kappa1 - T')
      = Real.log ((1/2 - 2*kappa1 - T)/(1/2 - 2*kappa1 - T')) :=
    (Real.log_div (ne_of_gt (by linarith : (0:ℝ) < 1/2 - 2*kappa1 - T))
      (ne_of_gt ha)).symm
  rw [hdiff]
  linarith

/-- The `p`-side of one cell: the real-cut band of the domain and the integer box used by the mesh
differ by the two boundary terms. -/
private lemma cell_p_diff (K : ℝ → ℝ → ℝ) {c h : ℝ} {i : ℕ} (N : ℕ)
    (hN : 2 ≤ N) (hNle : ⌊(N:ℝ)^(kappa1 + ((i:ℝ)+1)*h)⌋₊ < N) :
    |(∑ p ∈ (Finset.range N).filter (fun p => Nat.Prime p ∧
          (N:ℝ)^(kappa1 + (i:ℝ)*h) ≤ (p:ℝ) ∧ (p:ℝ) < (N:ℝ)^(kappa1 + ((i:ℝ)+1)*h)),
        ∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^c⌋₊).filter (fun q => Nat.Prime q),
          K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
            * (((p:ℝ) - 1))⁻¹ * (((q:ℝ) - 1))⁻¹)
      - (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^(kappa1 + (i:ℝ)*h)⌋₊
            ⌊(N:ℝ)^(kappa1 + ((i:ℝ)+1)*h)⌋₊).filter (fun p => Nat.Prime p),
        ∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^c⌋₊).filter (fun q => Nat.Prime q),
          K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
            * (((p:ℝ) - 1))⁻¹ * (((q:ℝ) - 1))⁻¹)|
    ≤ |(∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^c⌋₊).filter (fun q => Nat.Prime q),
          K (Real.log (⌊(N:ℝ)^(kappa1 + (i:ℝ)*h)⌋₊ : ℝ)/Real.log (N:ℝ))
            (Real.log (q:ℝ)/Real.log (N:ℝ))
            * (((⌊(N:ℝ)^(kappa1 + (i:ℝ)*h)⌋₊ : ℝ) - 1))⁻¹ * (((q:ℝ) - 1))⁻¹)|
      + |(∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^c⌋₊).filter (fun q => Nat.Prime q),
          K (Real.log (⌊(N:ℝ)^(kappa1 + ((i:ℝ)+1)*h)⌋₊ : ℝ)/Real.log (N:ℝ))
            (Real.log (q:ℝ)/Real.log (N:ℝ))
            * (((⌊(N:ℝ)^(kappa1 + ((i:ℝ)+1)*h)⌋₊ : ℝ) - 1))⁻¹ * (((q:ℝ) - 1))⁻¹)| := by
  classical
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  exact range_filter_band_diff (le_of_lt (rpow_pos_of_pos hNpos _))
    (le_of_lt (rpow_pos_of_pos hNpos _)) hNle Nat.Prime _

/-- Moving the `q`-cutoff down from `c₂` to `c₁` costs at most `C·(p-1)⁻¹` times the mass of the
band `(⌊N^{c₁}⌋, ⌊N^{c₂}⌋]`. -/
private lemma inner_q_diff_le {K : ℝ → ℝ → ℝ} {C c₁ c₂ : ℝ} {N p : ℕ} (hN : 2 ≤ N)
    (hp : 1 ≤ p) (hCnn : 0 ≤ C) (hK : ∀ t u : ℝ, |K t u| ≤ C) (h12 : c₁ ≤ c₂) (hc1 : 0 ≤ c₁) :
    |(∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^c₁⌋₊).filter (fun q => Nat.Prime q),
        K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
          * (((p:ℝ) - 1))⁻¹ * (((q:ℝ) - 1))⁻¹)
      - (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^c₂⌋₊).filter (fun q => Nat.Prime q),
        K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
          * (((p:ℝ) - 1))⁻¹ * (((q:ℝ) - 1))⁻¹)|
    ≤ C * (((p:ℝ) - 1))⁻¹ *
        (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^c₁⌋₊ ⌊(N:ℝ)^c₂⌋₊).filter (fun q => Nat.Prime q),
          (((q:ℝ) - 1))⁻¹) := by
  classical
  have hN1 : (1:ℝ) < (N:ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hmono : ⌊(N:ℝ)^c₁⌋₊ ≤ ⌊(N:ℝ)^c₂⌋₊ :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hN1.le h12)
  set S₁ := (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^c₁⌋₊).filter (fun q => Nat.Prime q) with hS1
  set S₂ := (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^c₂⌋₊).filter (fun q => Nat.Prime q) with hS2
  set w : ℕ → ℝ := fun q =>
    K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
      * (((p:ℝ) - 1))⁻¹ * (((q:ℝ) - 1))⁻¹ with hw
  have hsub : S₁ ⊆ S₂ := by
    intro q hq
    simp only [hS1, hS2, Finset.mem_filter, Finset.mem_Ioc] at hq ⊢
    exact ⟨⟨hq.1.1, le_trans hq.1.2 hmono⟩, hq.2⟩
  have hsdiff : (∑ q ∈ S₁, w q) - (∑ q ∈ S₂, w q) = -(∑ q ∈ S₂ \ S₁, w q) := by
    have h := Finset.sum_sdiff (s₁ := S₁) (s₂ := S₂) (f := w) hsub
    linarith
  have hdiff : |(∑ q ∈ S₁, w q) - (∑ q ∈ S₂, w q)| ≤ ∑ q ∈ S₂ \ S₁, |w q| := by
    rw [hsdiff, abs_neg]
    exact Finset.abs_sum_le_sum_abs _ _
  have hterm : ∀ q ∈ S₂ \ S₁, |w q| ≤ C * (((p:ℝ) - 1))⁻¹ * (((q:ℝ) - 1))⁻¹ := by
    intro q hq
    have hq2 : q ∈ S₂ := (Finset.mem_sdiff.mp hq).1
    obtain ⟨-, hprime⟩ := Finset.mem_filter.mp hq2
    have hq3 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hprime.two_le
    have hqpos : (0:ℝ) < ((q:ℝ) - 1) := by linarith
    have hinv : (0:ℝ) ≤ (((q:ℝ) - 1))⁻¹ := le_of_lt (inv_pos.mpr hqpos)
    have hpinv : (0:ℝ) ≤ (((p:ℝ) - 1))⁻¹ := by
      apply inv_nonneg.mpr
      have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
      linarith
    have hKb : |K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))| ≤ C :=
      hK _ _
    rw [hw, abs_mul, abs_mul, abs_of_nonneg hinv, abs_of_nonneg hpinv]
    apply mul_le_mul_of_nonneg_right _ hinv
    exact mul_le_mul_of_nonneg_right hKb hpinv
  have hsub2 : S₂ \ S₁ ⊆ (Finset.Ioc ⌊(N:ℝ)^c₁⌋₊ ⌊(N:ℝ)^c₂⌋₊).filter (fun q => Nat.Prime q) := by
    intro q hq
    obtain ⟨hq2, hq1⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨hqI, hprime⟩ := Finset.mem_filter.mp hq2
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hqI
    have hgt : ⌊(N:ℝ)^c₁⌋₊ < q := by
      by_contra hcon
      exact hq1 (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hlo, le_of_not_gt hcon⟩, hprime⟩)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hgt, hhi⟩, hprime⟩
  have hnonneg : ∀ q ∈ (Finset.Ioc ⌊(N:ℝ)^c₁⌋₊ ⌊(N:ℝ)^c₂⌋₊).filter (fun q => Nat.Prime q),
      (0:ℝ) ≤ (((q:ℝ) - 1))⁻¹ := by
    intro q hq
    obtain ⟨-, hprime⟩ := Finset.mem_filter.mp hq
    have h2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hprime.two_le
    exact le_of_lt (inv_pos.mpr (by linarith))
  have hmass : (∑ q ∈ S₂ \ S₁, |w q|)
      ≤ C * (((p:ℝ) - 1))⁻¹ *
        (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^c₁⌋₊ ⌊(N:ℝ)^c₂⌋₊).filter (fun q => Nat.Prime q),
          (((q:ℝ) - 1))⁻¹) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum (s := S₂ \ S₁)]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub2
      (fun q hq _ => hnonneg q hq)) (by
        apply mul_nonneg hCnn
        apply inv_nonneg.mpr
        have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
        linarith)
  calc |(∑ q ∈ S₁, w q) - (∑ q ∈ S₂, w q)| ≤ ∑ q ∈ S₂ \ S₁, |w q| := hdiff
    _ ≤ C * (((p:ℝ) - 1))⁻¹ *
        (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^c₁⌋₊ ⌊(N:ℝ)^c₂⌋₊).filter (fun q => Nat.Prime q),
          (((q:ℝ) - 1))⁻¹) := hmass

/-! ## Reopened working section: assembly of the F5 two dimensional limit -/

open Wu04Functional (IsLinearSieve)
/-- Splitting a real cutoff band of integers into the mesh cells of step `h`. -/
private lemma range_band_chain {s h : ℝ} {N : ℕ} (hN : 2 ≤ N) (hh : 0 < h) :
    ∀ (m : ℕ) (t : ℝ), (m:ℝ) * h = t - s → ∀ (A : ℕ → Prop) [DecidablePred A] (g : ℕ → ℝ),
      (∑ p ∈ (Finset.range N).filter (fun p : ℕ => A p ∧ (N:ℝ)^s ≤ (p:ℝ) ∧ (p:ℝ) < (N:ℝ)^t), g p)
        = ∑ i ∈ Finset.range m, ∑ p ∈ (Finset.range N).filter (fun p : ℕ => A p ∧ (N:ℝ)^(s + (i:ℝ)*h) ≤ (p:ℝ) ∧
              (p:ℝ) < (N:ℝ)^(s + ((i:ℝ)+1)*h)), g p := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  intro m
  induction m with
  | zero =>
      intro t ht A _ g
      have hts : t = s := by
        have h0 : (0:ℝ) = t - s := by simpa using ht
        linarith
      rw [hts]
      rw [Finset.sum_eq_zero (s := (Finset.range N).filter (fun p : ℕ => A p ∧ (N:ℝ)^s ≤ (p:ℝ) ∧ (p:ℝ) < (N:ℝ)^s)) ?_]
      · simp
      · intro p hp
        simp only [Finset.mem_filter] at hp
        linarith [hp.2.2.1, hp.2.2.2]
  | succ n ih =>
      intro t ht A _ g
      set w : ℝ := s + (n:ℝ) * h with hw
      have htw : t = w + h := by
        have h1 : ((n:ℝ) + 1) * h = t - s := by
          simpa only [Nat.cast_succ] using ht
        simp only [hw]; linarith
      have hnw : (n:ℝ) * h = w - s := by simp only [hw]; ring
      have ih' := ih w hnw A g
      rw [htw]
      have hsp : (Finset.range N).filter (fun p : ℕ => A p ∧ (N:ℝ)^s ≤ (p:ℝ) ∧ (p:ℝ) < (N:ℝ)^(w+h)) = (Finset.range N).filter (fun p : ℕ => A p ∧ (N:ℝ)^s ≤ (p:ℝ) ∧ (p:ℝ) < (N:ℝ)^w) ∪ (Finset.range N).filter (fun p : ℕ => A p ∧ (N:ℝ)^w ≤ (p:ℝ) ∧ (p:ℝ) < (N:ℝ)^(w+h)) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union]
        constructor
        · rintro ⟨h1, hA, hlo, hup⟩
          by_cases hc : (p:ℝ) < (N:ℝ)^w
          · exact Or.inl ⟨h1, hA, hlo, hc⟩
          · exact Or.inr ⟨h1, hA, not_lt.mp hc, hup⟩
        · rintro (⟨h1, hA, hlo, hup⟩ | ⟨h1, hA, hlo, hup⟩)
          · exact ⟨h1, hA, hlo, lt_of_lt_of_le hup
              (le_of_lt (Real.rpow_lt_rpow_of_exponent_lt hN1 (by linarith)))⟩
          · refine ⟨h1, hA, le_trans (Real.rpow_le_rpow_of_exponent_le (le_of_lt hN1) ?_) hlo, hup⟩
            rw [hw]
            have hp0 : (0:ℝ) ≤ (n:ℝ) * h := by positivity
            linarith
      have hdisj : Disjoint ((Finset.range N).filter (fun p : ℕ => A p ∧ (N:ℝ)^s ≤ (p:ℝ) ∧ (p:ℝ) < (N:ℝ)^w)) ((Finset.range N).filter (fun p : ℕ => A p ∧ (N:ℝ)^w ≤ (p:ℝ) ∧ (p:ℝ) < (N:ℝ)^(w+h))) := by
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        simp only [Finset.mem_filter] at hp1 hp2
        linarith [hp1.2.2.2, hp2.2.2.1]
      rw [hsp, Finset.sum_union hdisj, ih', Finset.sum_range_succ]
      have hcell : (Finset.range N).filter (fun p : ℕ => A p ∧ (N:ℝ)^w ≤ (p:ℝ) ∧ (p:ℝ) < (N:ℝ)^(w+h)) = (Finset.range N).filter (fun p : ℕ => A p ∧ (N:ℝ)^(s + (n:ℝ)*h) ≤ (p:ℝ) ∧ (p:ℝ) < (N:ℝ)^(s + ((n:ℝ)+1)*h)) := by
        simp only [hw]
        rw [show s + (n:ℝ) * h + h = s + ((n:ℝ)+1)*h from by ring]
      rw [hcell]
/-- The logarithmic coordinate of an integer recovers the integer. -/
private lemma rpow_log_coord {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p) :
    (N:ℝ)^(Real.log (p:ℝ)/Real.log (N:ℝ)) = (p:ℝ) := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : Real.log (N:ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < N by omega)))
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp
  rw [Real.rpow_def_of_pos hN0]
  have hmul : Real.log (N:ℝ) * (Real.log (p:ℝ) / Real.log (N:ℝ)) = Real.log (p:ℝ) := by
    field_simp
  rw [hmul, Real.exp_log hp0]
/-- Lower bound on a logarithmic coordinate from a power bound. -/
private lemma coord_ge_of_le {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p) {a : ℝ}
    (h : (N:ℝ)^a ≤ (p:ℝ)) : a ≤ Real.log (p:ℝ)/Real.log (N:ℝ) := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp
  have hL : 0 < Real.log (N:ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have h1 : a * Real.log (N:ℝ) ≤ Real.log (p:ℝ) := by
    rw [← Real.log_rpow hN0]
    exact Real.log_le_log (rpow_pos_of_pos hN0 a) h
  rw [le_div_iff₀ hL]
  linarith
/-- Upper bound on a logarithmic coordinate from a power bound. -/
private lemma coord_le_of_le {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p) {a : ℝ}
    (h : (p:ℝ) ≤ (N:ℝ)^a) : Real.log (p:ℝ)/Real.log (N:ℝ) ≤ a := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp
  have hL : 0 < Real.log (N:ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have h1 : Real.log (p:ℝ) ≤ a * Real.log (N:ℝ) := by
    rw [← Real.log_rpow hN0]
    exact Real.log_le_log hp0 h
  rw [div_le_iff₀ hL]
  linarith
/-- The region's `q` column against the fixed cell band, with the moving cutoff. -/
private lemma q_region_diff {K : ℝ → ℝ → ℝ} {C c T T' : ℝ} {N p : ℕ}
    (hN : 2 ≤ N) (hC0 : 0 ≤ C) (hK : ∀ t u : ℝ, |K t u| ≤ C)
    (hTT' : T ≤ T') (hpT : (N:ℝ)^T ≤ (p:ℝ)) (hpT' : (p:ℝ) ≤ (N:ℝ)^T')
    (hp2 : 2 ≤ p) (hcp : 0 ≤ c - T) (hctp : c - T' ≤ c - T) (hT'c : T' ≤ c)
    (hNlt : ⌊(N:ℝ)^(c - T')⌋₊ < N) (hNlt2 : ⌊(N:ℝ)^c / (p:ℝ)⌋₊ < N)
    (h2κ : 2 ≤ ⌊(N:ℝ)^kappa2⌋₊) (h2c : 2 ≤ ⌊(N:ℝ)^(c - T')⌋₊) :
    |(∑ q ∈ (Finset.range N).filter (fun q : ℕ => q.Prime ∧ q.Coprime N ∧
          (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^c / (p:ℝ)),
        K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
          * (((p:ℝ) - 1))⁻¹ * (((q:ℝ) - 1))⁻¹) - (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^(c - T)⌋₊).filter (fun q : ℕ => Nat.Prime q),
        K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
          * (((p:ℝ) - 1))⁻¹ * (((q:ℝ) - 1))⁻¹)| ≤ C * (((p:ℝ) - 1))⁻¹ *
        (2 * (((⌊(N:ℝ)^kappa2⌋₊ : ℝ) - 1))⁻¹
          + 4 * (((⌊(N:ℝ)^(c - T')⌋₊ : ℝ) - 1))⁻¹
          + 2 / (kappa2 * (N:ℝ)^kappa2)
          + 2 * (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^(c - T')⌋₊ ⌊(N:ℝ)^(c - T)⌋₊).filter (fun q : ℕ => Nat.Prime q), (((q:ℝ) - 1))⁻¹)) := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log (N:ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hκ2 : (0:ℝ) < kappa2 := by norm_num [kappa2]
  have hp0 : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp1 : (1:ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hCoef : 0 < ((p:ℝ) - 1)⁻¹ := by
    apply inv_pos.mpr
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  set t1 : ℝ := (((⌊(N:ℝ)^kappa2⌋₊ : ℝ) - 1))⁻¹ with ht1
  set t2 : ℝ := (((⌊(N:ℝ)^(c - T')⌋₊ : ℝ) - 1))⁻¹ with ht2
  set t3 : ℝ := 2 / (kappa2 * (N:ℝ)^kappa2) with ht3
  set t4 : ℝ := ∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^(c - T')⌋₊ ⌊(N:ℝ)^(c - T)⌋₊).filter (fun q : ℕ => Nat.Prime q), (((q:ℝ) - 1))⁻¹ with ht4
  have h2κr : (2:ℝ) ≤ (⌊(N:ℝ)^kappa2⌋₊ : ℝ) := by exact_mod_cast h2κ
  have h2cr : (2:ℝ) ≤ (⌊(N:ℝ)^(c - T')⌋₊ : ℝ) := by exact_mod_cast h2c
  have ht1nn : 0 ≤ t1 := by
    rw [ht1]; apply inv_nonneg.mpr; linarith
  have ht2nn : 0 ≤ t2 := by
    rw [ht2]; apply inv_nonneg.mpr; linarith
  have ht3nn : 0 ≤ t3 := by rw [ht3]; positivity
  have ht4nn : 0 ≤ t4 := by
    rw [ht4]
    apply Finset.sum_nonneg
    intro q hq
    have hq2 : (2:ℝ) ≤ q := by
      have := (Finset.mem_filter.mp hq).2.two_le
      exact_mod_cast this
    apply inv_nonneg.mpr; linarith
  set tp : ℝ := Real.log (p:ℝ)/Real.log (N:ℝ) with htp
  set w : ℕ → ℝ := fun q : ℕ => K tp (Real.log (q:ℝ)/Real.log (N:ℝ)) * ((p:ℝ)-1)⁻¹
    * ((q:ℝ)-1)⁻¹ with hw
  have hp0n : 0 < p := by omega
  have htpT' : tp ≤ T' := coord_le_of_le hN hp0n hpT'
  have htpT : T ≤ tp := coord_ge_of_le hN hp0n hpT
  have hcut : (N:ℝ)^c / (p:ℝ) = (N:ℝ)^(c - tp) := by
    rw [Real.rpow_sub hN0, htp, rpow_log_coord hN hp0n]
  have hcutf : ⌊(N:ℝ)^c / (p:ℝ)⌋₊ = ⌊(N:ℝ)^(c - tp)⌋₊ := by rw [hcut]
  have hset0 : (Finset.range N).filter (fun q : ℕ => q.Prime ∧ q.Coprime N ∧ (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^c / (p:ℝ)) = (Finset.range N).filter (fun q : ℕ => (q.Prime ∧ q.Coprime N) ∧ (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^c / (p:ℝ)) := by
    apply Finset.filter_congr
    intro q _
    tauto
  have hwle : ∀ x : ℕ, 2 ≤ x → |w x| ≤ C * ((p:ℝ)-1)⁻¹ * ((x:ℝ)-1)⁻¹ := by
    intro x hx
    have hx1 : (0:ℝ) < ((x:ℝ) - 1)⁻¹ := by
      have hx3 : (2:ℝ) ≤ x := by exact_mod_cast hx
      have : (0:ℝ) < (x:ℝ) - 1 := by linarith
      positivity
    simp only [hw]
    rw [abs_mul, abs_mul, abs_of_pos hCoef, abs_of_pos hx1]
    have h1 : |K tp (Real.log (x:ℝ)/Real.log (N:ℝ))| ≤ C := hK _ _
    have h2 : 0 ≤ ((x:ℝ) - 1)⁻¹ := le_of_lt (by positivity)
    have hmul : |K tp (Real.log (x:ℝ)/Real.log (N:ℝ))| * ((p:ℝ)-1)⁻¹ ≤ C * ((p:ℝ)-1)⁻¹ :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hCoef)
    exact mul_le_mul_of_nonneg_right hmul h2
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hx2 : 2 ≤ ⌊(N:ℝ)^c / (p:ℝ)⌋₊ := by
    rw [hcutf]
    exact le_trans h2c (Nat.floor_mono
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [htpT'])))
  have hxle : ⌊(N:ℝ)^(c - T')⌋₊ ≤ ⌊(N:ℝ)^c / (p:ℝ)⌋₊ := by
    rw [hcutf]
    exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [htpT']))
  -- (a) the real filter against its floor band
  have hA1 : |(∑ q ∈ (Finset.range N).filter (fun q : ℕ => (q.Prime ∧ q.Coprime N) ∧ (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^c / (p:ℝ)), w q) - (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^c / (p:ℝ)⌋₊).filter (fun q : ℕ => q.Prime ∧ q.Coprime N), w q)| ≤ C * ((p:ℝ)-1)⁻¹ * (2 * t1 + 2 * t2) := by
    have hA := range_filter_band_diff (by positivity : (0:ℝ) ≤ (N:ℝ)^kappa2)
      (by positivity) hNlt2 (fun q : ℕ => q.Prime ∧ q.Coprime N) w
    refine le_trans hA ?_
    have hb1 : |w ⌊(N:ℝ)^kappa2⌋₊| ≤ C * ((p:ℝ)-1)⁻¹ * t1 := by
      have := hwle ⌊(N:ℝ)^kappa2⌋₊ h2κ
      rwa [ht1]
    have hb2 : |w ⌊(N:ℝ)^c / (p:ℝ)⌋₊| ≤ C * ((p:ℝ)-1)⁻¹ * t2 := by
      have h2' := hwle ⌊(N:ℝ)^c / (p:ℝ)⌋₊ hx2
      have hinv : (((⌊(N:ℝ)^c / (p:ℝ)⌋₊ : ℝ) - 1))⁻¹ ≤ t2 := by
        rw [ht2]
        apply inv_anti₀
        · linarith
        · have hA2 : (2:ℝ) ≤ (⌊(N:ℝ)^(c - T')⌋₊ : ℝ) := by exact_mod_cast h2c
          have hA3 : (⌊(N:ℝ)^(c - T')⌋₊ : ℝ) ≤ (⌊(N:ℝ)^c / (p:ℝ)⌋₊ : ℝ) := by
            exact_mod_cast hxle
          linarith
      calc |w ⌊(N:ℝ)^c / (p:ℝ)⌋₊| ≤ C * ((p:ℝ)-1)⁻¹ * (((⌊(N:ℝ)^c / (p:ℝ)⌋₊ : ℝ) - 1))⁻¹ := h2'
        _ ≤ C * ((p:ℝ)-1)⁻¹ * t2 := by
            apply mul_le_mul_of_nonneg_left hinv (by positivity)
    have hsum := add_le_add hb1 hb2
    have hnn : (0:ℝ) ≤ C * ((p:ℝ)-1)⁻¹ * t1 := by positivity
    have hnn2 : (0:ℝ) ≤ C * ((p:ℝ)-1)⁻¹ * t2 := by positivity
    calc |w ⌊(N:ℝ)^kappa2⌋₊| + |w ⌊(N:ℝ)^c / (p:ℝ)⌋₊| ≤ C * ((p:ℝ)-1)⁻¹ * t1 + C * ((p:ℝ)-1)⁻¹ * t2 := hsum
      _ ≤ C * ((p:ℝ)-1)⁻¹ * (2 * t1 + 2 * t2) := by
          nlinarith [hnn, hnn2]
  -- (b) dropping the coprimality restriction
  have hB : |(∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^c / (p:ℝ)⌋₊).filter (fun q : ℕ => q.Prime ∧ q.Coprime N), w q) - (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^(c - tp)⌋₊).filter (fun q : ℕ => Nat.Prime q), w q)| ≤ C * ((p:ℝ)-1)⁻¹ * t3 := by
    rw [hcutf]
    set I : Finset ℕ := Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^(c - tp)⌋₊ with hI
    set Bad : Finset ℕ := (I.filter (fun q : ℕ => Nat.Prime q)).filter (fun q : ℕ => ¬ q.Coprime N) with hBad
    have hbad_eq : (∑ q ∈ I.filter (fun q : ℕ => Nat.Prime q), w q)
        = (∑ q ∈ I.filter (fun q : ℕ => q.Prime ∧ q.Coprime N), w q) + ∑ q ∈ Bad, w q := by
      rw [hBad, ← Finset.sum_filter_add_sum_filter_not (s := I.filter (fun q : ℕ => Nat.Prime q)) (p := fun q : ℕ => q.Coprime N) (f := w)]
      congr 1
      rw [Finset.filter_filter]
    have hdiff : (∑ q ∈ I.filter (fun q : ℕ => q.Prime ∧ q.Coprime N), w q)
        - (∑ q ∈ I.filter (fun q : ℕ => Nat.Prime q), w q) = -(∑ q ∈ Bad, w q) := by
      rw [hbad_eq]; ring
    rw [hdiff, abs_neg]
    have hbadtot : (∑ q ∈ Bad, (((q:ℝ) - 1))⁻¹) ≤ 2 / (kappa2 * (N:ℝ)^kappa2) := by
      have hbb := band_bad_totient_mass (a := kappa2) (b := c - tp) (by norm_num [kappa2]) hN
      rw [hBad, hI]
      exact hbb
    have hterm : ∀ q ∈ Bad, |w q| ≤ C * ((p:ℝ)-1)⁻¹ * (((q:ℝ) - 1))⁻¹ := by
      intro q hq
      exact hwle q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.two_le
    have hstep1 : |(∑ q ∈ Bad, w q)| ≤ ∑ q ∈ Bad, |w q| := Finset.abs_sum_le_sum_abs _ _
    have hstep2 : (∑ q ∈ Bad, |w q|) ≤ ∑ q ∈ Bad, C * ((p:ℝ)-1)⁻¹ * (((q:ℝ) - 1))⁻¹ :=
      Finset.sum_le_sum hterm
    have hstep3 : (∑ q ∈ Bad, C * ((p:ℝ)-1)⁻¹ * (((q:ℝ) - 1))⁻¹)
        = C * ((p:ℝ)-1)⁻¹ * (∑ q ∈ Bad, (((q:ℝ) - 1))⁻¹) := by
      rw [Finset.mul_sum]
    have hstep4 : C * ((p:ℝ)-1)⁻¹ * (∑ q ∈ Bad, (((q:ℝ) - 1))⁻¹)
        ≤ C * ((p:ℝ)-1)⁻¹ * t3 := by
      rw [ht3]
      exact mul_le_mul_of_nonneg_left hbadtot (by positivity)
    linarith [hstep1, hstep2, hstep3, hstep4]
  -- (c) monotone cutoff
  have hC : |(∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^(c - tp)⌋₊).filter (fun q : ℕ => Nat.Prime q), w q) - (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^(c - T)⌋₊).filter (fun q : ℕ => Nat.Prime q), w q)| ≤ C * ((p:ℝ)-1)⁻¹ * (2 * t4) := by
    have hmono := inner_q_diff_le (K := K) (C := C) (c₁ := c - tp) (c₂ := c - T)
      (N := N) (p := p) hN (by omega) hC0 hK (by linarith [htpT]) (by linarith [htpT', hT'c])
    have hsub : (Finset.Ioc ⌊(N:ℝ)^(c - tp)⌋₊ ⌊(N:ℝ)^(c - T)⌋₊).filter (fun q : ℕ => Nat.Prime q) ⊆ (Finset.Ioc ⌊(N:ℝ)^(c - T')⌋₊ ⌊(N:ℝ)^(c - T)⌋₊).filter (fun q : ℕ => Nat.Prime q) := by
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hq ⊢
      exact ⟨⟨lt_of_le_of_lt (Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [htpT']))) hq.1.1, hq.1.2⟩, hq.2⟩
    refine le_trans hmono ?_
    have hle : (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^(c - tp)⌋₊ ⌊(N:ℝ)^(c - T)⌋₊).filter (fun q : ℕ => Nat.Prime q), (((q:ℝ) - 1))⁻¹) ≤ t4 := by
      rw [ht4]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq1 _ => by
        have hq2' : (2:ℝ) ≤ q := by
          have := (Finset.mem_filter.mp hq1).2.two_le
          exact_mod_cast this
        have hq3 : (0:ℝ) < (q:ℝ) - 1 := by linarith
        positivity)
    have s1 : C * ((p:ℝ)-1)⁻¹ * (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^(c - tp)⌋₊ ⌊(N:ℝ)^(c - T)⌋₊).filter (fun q : ℕ => Nat.Prime q), (((q:ℝ) - 1))⁻¹)
        ≤ C * ((p:ℝ)-1)⁻¹ * t4 := mul_le_mul_of_nonneg_left hle (by positivity)
    have s2 : C * ((p:ℝ)-1)⁻¹ * t4 ≤ C * ((p:ℝ)-1)⁻¹ * (2 * t4) := by
      have hs : (0:ℝ) ≤ C * ((p:ℝ)-1)⁻¹ * t4 := by positivity
      nlinarith [hs]
    linarith [s1, s2]
  -- combine the three column estimates
  rw [hset0]
  have h1 : |(∑ q ∈ (Finset.range N).filter (fun q : ℕ => (q.Prime ∧ q.Coprime N) ∧ (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^c / (p:ℝ)), w q) - (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^c / (p:ℝ)⌋₊).filter (fun q : ℕ => q.Prime ∧ q.Coprime N), w q)| ≤ C * ((p:ℝ)-1)⁻¹ * (2 * t1 + 2 * t2) := hA1
  have h2 : |(∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^c / (p:ℝ)⌋₊).filter (fun q : ℕ => q.Prime ∧ q.Coprime N), w q) - (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^(c - tp)⌋₊).filter (fun q : ℕ => Nat.Prime q), w q)| ≤ C * ((p:ℝ)-1)⁻¹ * t3 := hB
  have h3 : |(∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^(c - tp)⌋₊).filter (fun q : ℕ => Nat.Prime q), w q) - (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^(c - T)⌋₊).filter (fun q : ℕ => Nat.Prime q), w q)| ≤ C * ((p:ℝ)-1)⁻¹ * (2 * t4) := hC
  have htri1 : |(∑ q ∈ (Finset.range N).filter (fun q : ℕ => (q.Prime ∧ q.Coprime N) ∧ (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^c / (p:ℝ)), w q) - (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^(c - T)⌋₊).filter (fun q : ℕ => Nat.Prime q), w q)| ≤ |(∑ q ∈ (Finset.range N).filter (fun q : ℕ => (q.Prime ∧ q.Coprime N) ∧ (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^c / (p:ℝ)), w q) - (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^c / (p:ℝ)⌋₊).filter (fun q : ℕ => q.Prime ∧ q.Coprime N), w q)| + |(∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^c / (p:ℝ)⌋₊).filter (fun q : ℕ => q.Prime ∧ q.Coprime N), w q) - (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^(c - T)⌋₊).filter (fun q : ℕ => Nat.Prime q), w q)| := abs_sub_le _ _ _
  have htri2 : |(∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^c / (p:ℝ)⌋₊).filter (fun q : ℕ => q.Prime ∧ q.Coprime N), w q) - (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^(c - T)⌋₊).filter (fun q : ℕ => Nat.Prime q), w q)| ≤ |(∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^c / (p:ℝ)⌋₊).filter (fun q : ℕ => q.Prime ∧ q.Coprime N), w q) - (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^(c - tp)⌋₊).filter (fun q : ℕ => Nat.Prime q), w q)| + |(∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^(c - tp)⌋₊).filter (fun q : ℕ => Nat.Prime q), w q) - (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^(c - T)⌋₊).filter (fun q : ℕ => Nat.Prime q), w q)| := abs_sub_le _ _ _
  have hn2 : (0:ℝ) ≤ C * ((p:ℝ)-1)⁻¹ * t2 := by positivity
  have hn3 : (0:ℝ) ≤ C * ((p:ℝ)-1)⁻¹ * t3 := by positivity
  linarith [htri1, htri2, h1, h2, h3, hn2, hn3]

/-- The doubly clamped kernel is bounded by the box bound, uniformly in both variables. -/
private lemma clampK_bounded {f : ℝ → ℝ} {C : ℝ}
    (hCb : ∀ x ∈ Set.Icc kappa1 kappa2 ×ˢ Set.Icc kappa2 (1/2 - 3*kappa1),
      |f ((1/2 - x.1 - x.2)/kappa1)| ≤ C) (hC0 : 0 ≤ C) :
    ∀ t u : ℝ, |(if t ∈ Set.Icc kappa1 kappa2 ∧ u ∈ Set.Icc kappa2 (1/2 - 3*kappa1)
      then f ((1/2 - t - u)/kappa1) else 0)| ≤ C := by
  intro t u
  by_cases h : t ∈ Set.Icc kappa1 kappa2 ∧ u ∈ Set.Icc kappa2 (1/2 - 3*kappa1)
  · rw [if_pos h]
    exact hCb (t, u) h
  · rw [if_neg h, abs_zero]
    exact hC0

/-- The doubly clamped kernel has the kernel modulus in its first coordinate. -/
private lemma clampK_osc {f : ℝ → ℝ} {D γf hs a b v : ℝ} (hD0 : 0 ≤ D)
    (hmod : ∀ x y : ℝ, x ∈ Set.Icc (3/2) 4 → y ∈ Set.Icc (3/2) 4 →
      |x - y| ≤ γf → |f x - f y| ≤ D)
    (ha : kappa1 ≤ a) (hb : b ≤ kappa2) (hv : v ∈ Set.Icc a b)
    (hvt : ∀ t ∈ Set.Icc a b, |v - t| ≤ hs) (hhs : hs ≤ kappa1 * γf) :
    ∀ u : ℝ, ∀ t ∈ Set.Icc a b,
      |(if t ∈ Set.Icc kappa1 kappa2 ∧ u ∈ Set.Icc kappa2 (1/2 - 3*kappa1)
          then f ((1/2 - t - u)/kappa1) else 0)
        - (if v ∈ Set.Icc kappa1 kappa2 ∧ u ∈ Set.Icc kappa2 (1/2 - 3*kappa1)
          then f ((1/2 - v - u)/kappa1) else 0)| ≤ D := by
  have hκ1pos : (0:ℝ) < kappa1 := by norm_num [kappa1]
  have hvI : v ∈ Set.Icc kappa1 kappa2 := ⟨le_trans ha hv.1, le_trans hv.2 hb⟩
  intro u t ht
  have htI : t ∈ Set.Icc kappa1 kappa2 := ⟨le_trans ha ht.1, le_trans ht.2 hb⟩
  by_cases hu : u ∈ Set.Icc kappa2 (1/2 - 3*kappa1)
  · rw [if_pos ⟨htI, hu⟩, if_pos ⟨hvI, hu⟩]
    have ha1 := box_arg_bounds htI hu
    have ha2 := box_arg_bounds hvI hu
    refine hmod _ _ ha1 ha2 ?_
    have heq : (1/2 - t - u)/kappa1 - (1/2 - v - u)/kappa1 = (v - t)/kappa1 := by
      field_simp
      ring
    rw [heq, abs_div, abs_of_pos hκ1pos]
    rw [div_le_iff₀ hκ1pos]
    have := hvt t ht
    nlinarith [this, hhs]
  · rw [if_neg (fun h => hu h.2), if_neg (fun h => hu h.2), sub_self, abs_zero]
    exact hD0

/-- The crossing condition puts the `q` coordinate strictly below `1/2 - 3κ₁`. -/
private lemma coord_lt_of_cross {N p q : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (hq : 0 < q)
    (hpq : (N:ℝ)^kappa1 ≤ (p:ℝ))
    (hq2 : (q:ℝ) < (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ)) :
    Real.log (q:ℝ)/Real.log (N:ℝ) < 1/2 - 3*kappa1 := by
  have hN1 : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hL : 0 < Real.log (N:ℝ) := Real.log_pos hN1
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hlt : (q:ℝ) * (p:ℝ) < (N:ℝ)^(1/2 - 2*kappa1) := by
    rw [lt_div_iff₀ hp0] at hq2
    linarith [hq2]
  have hlog : Real.log (q:ℝ) + Real.log (p:ℝ) < (1/2 - 2*kappa1) * Real.log (N:ℝ) := by
    have h1 := Real.log_lt_log (by positivity : (0:ℝ) < (q:ℝ) * (p:ℝ)) hlt
    rw [Real.log_mul hq0.ne' hp0.ne'] at h1
    rwa [Real.log_rpow (by positivity : (0:ℝ) < (N:ℝ)) (1/2 - 2*kappa1)] at h1
  have hpκ : kappa1 * Real.log (N:ℝ) ≤ Real.log (p:ℝ) := by
    have h2 := Real.log_le_log (by positivity : (0:ℝ) < (N:ℝ)^kappa1) hpq
    rw [Real.log_rpow (by positivity : (0:ℝ) < (N:ℝ)) kappa1] at h2
    linarith [h2]
  rw [div_lt_iff₀ hL]
  nlinarith [hlog, hpκ]

/-- A `q` column of the region has reciprocal totient mass bounded independently of `N`'s size. -/
private lemma q_col_mass {Lu : ℝ} (hLu : Lu = Real.log ((1/2 - 3*kappa1)/kappa2)) :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, (N:ℝ)^kappa1 ≤ (p:ℝ) →
      (∑ q ∈ (Finset.range N).filter (fun q : ℕ => q.Prime ∧ q.Coprime N ∧
          (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ)), (((q:ℝ) - 1))⁻¹)
        ≤ Lu + 7 := by
  have hmass := cell_mass_le (a := kappa1/2) (b := 1/2 - 3*kappa1) (η := 1)
    (by norm_num [kappa1]) (by norm_num [kappa1, kappa2]) (by norm_num)
  have hratio : (1/2 - 3*kappa1)/(kappa1/2)
      = ((1/2 - 3*kappa1)/kappa2) * (2*kappa2/kappa1) := by
    rw [show kappa1 = 1/12 from rfl, show kappa2 = 29/250 from rfl]
    norm_num
  have hlog : Real.log (1/2 - 3*kappa1) - Real.log (kappa1/2) = Lu + Real.log (2*kappa2/kappa1) := by
    rw [← Real.log_div (by norm_num [kappa1, kappa2]) (by norm_num [kappa1])]
    rw [hratio, Real.log_mul (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2]), hLu]
  have hlogb : Real.log (2*kappa2/kappa1) ≤ 2*kappa2/kappa1 - 1 :=
    Real.log_le_sub_one_of_pos (by norm_num [kappa1, kappa2])
  have hv : 2*kappa2/kappa1 - 1 ≤ 6 := by norm_num [kappa1, kappa2]
  filter_upwards [hmass, eventually_ge_atTop 2] with N hN1 hN
  intro p hp
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp0 : (0:ℝ) < p := lt_of_lt_of_le (by positivity) hp
  have hltN : (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ) ≤ (N:ℝ)^(1/2 - 3*kappa1) := by
    rw [div_le_iff₀ hp0]
    calc (N:ℝ)^(1/2 - 2*kappa1) = (N:ℝ)^(1/2 - 3*kappa1) * (N:ℝ)^kappa1 := by
          rw [← Real.rpow_add hN0]; ring_nf
      _ ≤ (N:ℝ)^(1/2 - 3*kappa1) * (p:ℝ) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
  have hsub : (Finset.range N).filter (fun q : ℕ => q.Prime ∧ q.Coprime N ∧
        (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ))
      ⊆ (Finset.Ioc ⌊(N:ℝ)^(kappa1/2)⌋₊ ⌊(N:ℝ)^(1/2 - 3*kappa1)⌋₊).filter (fun q => Nat.Prime q) := by
    intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨-, hqp, -, hq1, hq2⟩ := hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hqp⟩
    · apply (Nat.floor_lt (by positivity)).mpr
      have hq2' : (2:ℝ) ≤ q := by exact_mod_cast hqp.two_le
      have hx : (N:ℝ)^(kappa1/2) < (N:ℝ)^kappa2 :=
        Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (show 1 < N by omega))
          (by norm_num [kappa1, kappa2])
      linarith
    · exact Nat.le_floor (le_of_lt (lt_of_lt_of_le hq2 hltN))
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq _ => ?_)) ?_
  · have hq2 : (2:ℝ) ≤ q := by
      have := (Finset.mem_filter.mp hq).2.two_le
      exact_mod_cast this
    have hpos : (0:ℝ) < (q:ℝ) - 1 := by linarith
    positivity
  linarith [hN1, hlog, hlogb, hv]

/-- A reciprocal floor comparison: `(⌊x⌋ - 1)⁻¹ ≤ 2 / x` for `x ≥ 4`. -/
private lemma floor_sub_inv_le {x : ℝ} (hx : 4 ≤ x) :
    (((⌊x⌋₊ : ℝ) - 1))⁻¹ ≤ 2 / x := by
  have hx0 : (0:ℝ) < x := by linarith
  have hfl : x / 2 ≤ ((⌊x⌋₊ : ℝ) - 1) := by
    have h := Nat.lt_floor_add_one x
    linarith
  have hhalf : (0:ℝ) < x / 2 := by linarith
  have h1 : 1 / ((⌊x⌋₊ : ℝ) - 1) ≤ 1 / (x / 2) := one_div_le_one_div_of_le hhalf hfl
  have e1 : (((⌊x⌋₊ : ℝ) - 1))⁻¹ = 1 / ((⌊x⌋₊ : ℝ) - 1) := by rw [one_div]
  have e2 : (1:ℝ) / (x / 2) = 2 / x := by rw [one_div_div]
  linarith [h1, e1, e2]

/-- The totient mass of a real-cut prime band is its logarithmic length, plus `η`. -/
private lemma real_band_mass_le {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb1 : b < 1) {η : ℝ}
    (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      (∑ p ∈ (Finset.range N).filter
          (fun p : ℕ => Nat.Prime p ∧ (N:ℝ)^a ≤ (p:ℝ) ∧ (p:ℝ) < (N:ℝ)^b),
        (((p:ℝ) - 1))⁻¹) ≤ Real.log b - Real.log a + η := by
  have hη2 : (0:ℝ) < η/2 := by linarith
  have hη4 : (0:ℝ) < η/4 := by linarith
  have hbox := cell_mass_le (a := a) (b := b) ha hab hη2
  have hpowv : ∀ c : ℝ, 0 < c → Tendsto (fun N : ℕ => (N:ℝ)^c) atTop atTop :=
    fun c hc => (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  have hb1' : ∀ᶠ N : ℕ in atTop, 2 / (N:ℝ)^a ≤ η/4 :=
    ((tendsto_const_nhds.div_atTop (hpowv a ha)).eventually
      (eventually_lt_nhds hη4)).mono (fun N h => le_of_lt h)
  have hb2' : ∀ᶠ N : ℕ in atTop, 2 / (N:ℝ)^b ≤ η/4 :=
    ((tendsto_const_nhds.div_atTop (hpowv b (lt_trans ha hab))).eventually
      (eventually_lt_nhds hη4)).mono (fun N h => le_of_lt h)
  have hbig4 : ∀ᶠ N : ℕ in atTop, (4:ℝ) ≤ (N:ℝ)^a ∧ (4:ℝ) ≤ (N:ℝ)^b := by
    have h1 := (hpowv a ha).eventually (eventually_ge_atTop (4:ℝ))
    have h2 := (hpowv b (lt_trans ha hab)).eventually (eventually_ge_atTop (4:ℝ))
    filter_upwards [h1, h2] with N hN1 hN2
    exact ⟨hN1, hN2⟩
  filter_upwards [hbox, hb1', hb2', hbig4, eventually_ge_atTop 2] with N hboxN hbN1 hbN2 hbigN hN2
  have hxa : (4:ℝ) ≤ (N:ℝ)^a := hbigN.1
  have hxb : (4:ℝ) ≤ (N:ℝ)^b := hbigN.2
  have hxa0 : (0:ℝ) < (N:ℝ)^a := rpow_pos_of_pos (by positivity) a
  have hxb0 : (0:ℝ) < (N:ℝ)^b := rpow_pos_of_pos (by positivity) b
  have hN1 : (1:ℝ) < (N:ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hfla : (N:ℝ)^a / 2 ≤ ((⌊(N:ℝ)^a⌋₊ : ℝ) - 1) := by
    have h := Nat.lt_floor_add_one ((N:ℝ)^a)
    linarith
  have hflb : (N:ℝ)^b / 2 ≤ ((⌊(N:ℝ)^b⌋₊ : ℝ) - 1) := by
    have h := Nat.lt_floor_add_one ((N:ℝ)^b)
    linarith
  have hpa : (0:ℝ) < ((⌊(N:ℝ)^a⌋₊ : ℝ) - 1) := by linarith
  have hpb : (0:ℝ) < ((⌊(N:ℝ)^b⌋₊ : ℝ) - 1) := by linarith
  have hwa : (((⌊(N:ℝ)^a⌋₊ : ℝ) - 1))⁻¹ ≤ η/4 := by
    have hle : (((⌊(N:ℝ)^a⌋₊ : ℝ) - 1))⁻¹ ≤ (((N:ℝ)^a/2))⁻¹ := by
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le (by linarith) hfla
    have h2 : (((N:ℝ)^a/2))⁻¹ = 2 / (N:ℝ)^a := by
      field_simp
    linarith [hle, h2, hbN1]
  have hwb : (((⌊(N:ℝ)^b⌋₊ : ℝ) - 1))⁻¹ ≤ η/4 := by
    have hle : (((⌊(N:ℝ)^b⌋₊ : ℝ) - 1))⁻¹ ≤ (((N:ℝ)^b/2))⁻¹ := by
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le (by linarith) hflb
    have h2 : (((N:ℝ)^b/2))⁻¹ = 2 / (N:ℝ)^b := by
      field_simp
    linarith [hle, h2, hbN2]
  have hdiff := range_filter_band_diff (N := N) (a := (N:ℝ)^a) (u := (N:ℝ)^b)
    (le_of_lt hxa0) (le_of_lt hxb0) (by
      have hlt : (N:ℝ)^b < (N:ℝ) := by
        have h := Real.rpow_lt_rpow_of_exponent_lt hN1 hb1
        rwa [Real.rpow_one] at h
      have hfr : (⌊(N:ℝ)^b⌋₊ : ℝ) ≤ (N:ℝ)^b := Nat.floor_le (le_of_lt hxb0)
      have hcast : (⌊(N:ℝ)^b⌋₊ : ℝ) < (N:ℝ) := lt_of_le_of_lt hfr hlt
      exact_mod_cast hcast)
    (fun p : ℕ => Nat.Prime p) (fun p : ℕ => (((p:ℝ) - 1))⁻¹)
  have hstep : (∑ p ∈ (Finset.range N).filter
        (fun p : ℕ => Nat.Prime p ∧ (N:ℝ)^a ≤ (p:ℝ) ∧ (p:ℝ) < (N:ℝ)^b),
        (((p:ℝ) - 1))⁻¹)
      - (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter (fun p : ℕ => Nat.Prime p),
        (((p:ℝ) - 1))⁻¹) ≤ η/2 := by
    have h := (abs_le.mp hdiff).2
    have hwa' : |(((⌊(N:ℝ)^a⌋₊ : ℝ) - 1))⁻¹| = (((⌊(N:ℝ)^a⌋₊ : ℝ) - 1))⁻¹ :=
      abs_of_pos (inv_pos.mpr hpa)
    have hwb' : |(((⌊(N:ℝ)^b⌋₊ : ℝ) - 1))⁻¹| = (((⌊(N:ℝ)^b⌋₊ : ℝ) - 1))⁻¹ :=
      abs_of_pos (inv_pos.mpr hpb)
    rw [hwa', hwb'] at h
    linarith [h, hwa, hwb]
  have hboxN' : (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^a⌋₊ ⌊(N:ℝ)^b⌋₊).filter
        (fun p : ℕ => Nat.Prime p), (((p:ℝ) - 1))⁻¹) ≤ Real.log b - Real.log a + η/2 := hboxN
  linarith [hboxN', hstep]

/-- A mesh step below a prescribed cap with an integral number of cells. -/
private lemma hstep_choice {hcap : ℝ} (hh : 0 < hcap) (hk : kappa1 < kappa2) :
    ∃ (m : ℕ) (hs : ℝ), 0 < m ∧ 0 < hs ∧ (m:ℝ) * hs = kappa2 - kappa1 ∧ hs ≤ hcap := by
  have hpos : 0 < kappa2 - kappa1 := by linarith
  refine ⟨⌈(kappa2 - kappa1)/hcap⌉₊ + 1, (kappa2 - kappa1)/((⌈(kappa2 - kappa1)/hcap⌉₊ + 1 : ℕ) : ℝ),
    by omega, ?_, ?_, ?_⟩
  · apply div_pos hpos
    exact_mod_cast Nat.succ_pos _
  · push_cast
    field_simp
  · push_cast
    rw [div_le_iff₀ (by positivity : (0:ℝ) < ((⌈(kappa2 - kappa1)/hcap⌉₊ : ℝ) + 1))]
    have h2 : (kappa2 - kappa1)/hcap ≤ (⌈(kappa2 - kappa1)/hcap⌉₊ : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hh] at h2
    nlinarith [h2]

/-! ## Global assembly of the F5 two dimensional limit -/


/-- The accumulated `p`-cell error is inside three `K0 δ` budgets. -/
private theorem budget_S1 (C hL δ Br K0 : ℝ) (N : ℕ) (m : ℕ) (lg : ℕ → ℝ)
    (hC0 : 0 ≤ C) (hL0 : 0 ≤ hL) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hm0 : 0 < m) (hBr0 : 0 ≤ Br) (hκ2 : 0 < kappa2) (hN0 : (0 : ℝ) < N)
    (hK01 : 1 ≤ K0)
    (hsumlg : (∑ i ∈ Finset.range m, lg i) = hL)
    (hBrB : Br ≤ 40 / (N : ℝ) ^ kappa2 + 8 * δ / kappa2 + 4 * δ / (m : ℝ))
    (hKb : 16 * C * (hL + 1) / kappa2 ≤ K0)
    (hKb2 : 8 * (C * (hL + 1)) ≤ K0)
    (hKb0 : 80 * C * (hL + 1) / (N : ℝ) ^ kappa2 ≤ δ) :
    (∑ i ∈ Finset.range m, C * (lg i + δ / (m : ℝ)) * Br) ≤ 3 * K0 * δ := by
  have hm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have hLn1 : (0 : ℝ) ≤ hL + 1 := by linarith
  have hCLn : (0 : ℝ) ≤ C * (hL + 1) := mul_nonneg hC0 hLn1
  have hsplit : (∑ i ∈ Finset.range m, C * (lg i + δ / (m : ℝ)) * Br)
      = C * Br * (hL + δ) := by
    have h1 : ∀ i ∈ Finset.range m, C * (lg i + δ / (m : ℝ)) * Br
        = (C * Br) * (lg i + δ / (m : ℝ)) := by
      intro i hi; ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
    have hdel : (∑ i ∈ Finset.range m, δ / (m : ℝ)) = δ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    rw [Finset.sum_add_distrib, hsumlg, hdel]
  rw [hsplit]
  have hcoef : C * (hL + δ) ≤ 2 * (C * (hL + 1)) := by nlinarith [hδ1, hC0]
  have hstep1 : C * (hL + δ) * Br
      ≤ 2 * (C * (hL + 1)) * (40 / (N : ℝ) ^ kappa2 + 8 * δ / kappa2 + 4 * δ / (m : ℝ)) := by
    apply mul_le_mul hcoef hBrB hBr0 (by linarith)
  have hbrk : C * Br * (hL + δ)
      ≤ 2 * (C * (hL + 1)) * (40 / (N : ℝ) ^ kappa2 + 8 * δ / kappa2 + 4 * δ / (m : ℝ)) := by
    rw [show C * Br * (hL + δ)
      = C * (hL + δ) * Br from by ring]
    exact hstep1
  have hexp : 2 * (C * (hL + 1)) * (40 / (N : ℝ) ^ kappa2 + 8 * δ / kappa2 + 4 * δ / (m : ℝ))
      = 80 * C * (hL + 1) / (N : ℝ) ^ kappa2 + 16 * (C * (hL + 1)) / kappa2 * δ
        + 8 * (C * (hL + 1)) / (m : ℝ) * δ := by
    field_simp
    ring
  have hp1 : 16 * (C * (hL + 1)) / kappa2 * δ ≤ K0 * δ := by
    apply mul_le_mul_of_nonneg_right _ hδ0.le
    have he : 16 * (C * (hL + 1)) / kappa2 = 16 * C * (hL + 1) / kappa2 := by ring
    rw [he]; exact hKb
  have hp2 : 8 * (C * (hL + 1)) / (m : ℝ) * δ ≤ K0 * δ := by
    apply mul_le_mul_of_nonneg_right _ hδ0.le
    have h1 : 8 * (C * (hL + 1)) / (m : ℝ) ≤ 8 * (C * (hL + 1)) := by
      rw [div_le_iff₀ hm]
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm0
      nlinarith
    exact le_trans h1 hKb2
  have hpos1 : (0 : ℝ) ≤ 80 * C * (hL + 1) / (N : ℝ) ^ kappa2 :=
    div_nonneg (by linarith) (le_of_lt (Real.rpow_pos_of_pos hN0 _))
  have hpos2 : (0 : ℝ) ≤ 16 * (C * (hL + 1)) / kappa2 * δ :=
    mul_nonneg (div_nonneg (by linarith) hκ2.le) hδ0.le
  have hpos3 : (0 : ℝ) ≤ 8 * (C * (hL + 1)) / (m : ℝ) * δ :=
    mul_nonneg (div_nonneg (by linarith) hm.le) hδ0.le
  calc C * Br * (hL + δ)
      ≤ 2 * (C * (hL + 1)) * (40 / (N : ℝ) ^ kappa2 + 8 * δ / kappa2 + 4 * δ / (m : ℝ)) := hbrk
    _ = 80 * C * (hL + 1) / (N : ℝ) ^ kappa2 + 16 * (C * (hL + 1)) / kappa2 * δ
        + 8 * (C * (hL + 1)) / (m : ℝ) * δ := hexp
    _ ≤ 3 * K0 * δ := by
        have hd : (0 : ℝ) ≤ δ := hδ0.le
        have hK0 : (0 : ℝ) ≤ K0 := by linarith
        have hK0d : (0 : ℝ) ≤ K0 * δ := mul_nonneg hK0 hd
        nlinarith [hp1, hp2, hKb0, hK0d, hpos1, hpos2, hpos3]

/-- The accumulated box error is inside `δ`. -/
private theorem budget_S2 (C Lu δ : ℝ) (N : ℕ) (m : ℕ)
    (hC0 : 0 ≤ C) (hLu0 : 0 ≤ Lu) (hδ0 : 0 < δ) (hm0 : 0 < m)
    (hN0 : (0 : ℝ) < N) (hN1 : (1 : ℝ) ≤ (N : ℝ))
    (hIV : 8 * (C + 1) * (Lu + 7) * ((m : ℝ) + 1) / (N : ℝ) ^ kappa1 ≤ δ) :
    (∑ i ∈ Finset.range m, 4 * C * (Lu + 7) / (N : ℝ) ^ kappa1) ≤ δ := by
  have hm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hEq : (m : ℝ) * (4 * C * (Lu + 7) / (N : ℝ) ^ kappa1)
      = 4 * (m : ℝ) * C * (Lu + 7) / (N : ℝ) ^ kappa1 := by
    field_simp
  rw [hEq]
  refine le_trans ?_ hIV
  apply div_le_div_of_nonneg_right _ (le_of_lt (Real.rpow_pos_of_pos hN0 _))
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hLp : (0 : ℝ) ≤ Lu + 7 := by linarith
  have hX : (0 : ℝ) ≤ (C + 1) * (Lu + 7) := by nlinarith
  have hCL : C * (Lu + 7) ≤ (C + 1) * (Lu + 7) := by nlinarith
  have hmnn : (0 : ℝ) ≤ 4 * (m : ℝ) := by positivity
  have hstep1 : 4 * (m : ℝ) * C * (Lu + 7) ≤ 4 * (m : ℝ) * ((C + 1) * (Lu + 7)) := by
    calc 4 * (m : ℝ) * C * (Lu + 7) = 4 * (m : ℝ) * (C * (Lu + 7)) := by ring
      _ ≤ 4 * (m : ℝ) * ((C + 1) * (Lu + 7)) := mul_le_mul_of_nonneg_left hCL hmnn
  have hpos2 : (0 : ℝ) ≤ (m : ℝ) * ((C + 1) * (Lu + 7)) := mul_nonneg hm.le hX
  have hstep2 : 4 * (m : ℝ) * ((C + 1) * (Lu + 7)) ≤ 8 * ((m : ℝ) + 1) * ((C + 1) * (Lu + 7)) := by
    have h4 : 4 * (m : ℝ) * ((C + 1) * (Lu + 7)) ≤ 8 * (m : ℝ) * ((C + 1) * (Lu + 7)) := by
      nlinarith [hpos2]
    have h5 : 8 * (m : ℝ) * ((C + 1) * (Lu + 7)) ≤ 8 * ((m : ℝ) + 1) * ((C + 1) * (Lu + 7)) := by
      have hm1' : (0 : ℝ) ≤ (m : ℝ) + 1 := by linarith
      nlinarith [hX, hm, mul_nonneg hX hm.le, mul_nonneg hX hm1']
    linarith [h4, h5]
  linarith [hstep1, hstep2]

/-- The accumulated mesh error is inside `K0 δ`. -/
private theorem budget_S3 (C Lc hL δ K0 : ℝ) (m : ℕ) (lg ecc : ℕ → ℝ)
    (hC0 : 0 ≤ C) (hLc0 : 0 ≤ Lc) (hL0 : 0 ≤ hL) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hm0 : 0 < m)
    (hecc : ∀ i ∈ Finset.range m, ecc i ≤ (Lc + δ / (m : ℝ)) * (δ * (lg i + δ / (m : ℝ))
      + C * (δ / (m : ℝ))) + lg i * δ)
    (hlgN : ∀ i, i ≤ m → 0 ≤ lg i)
    (hsumlg : (∑ i ∈ Finset.range m, lg i) = hL)
    (hK : (Lc + 1) * (hL + 1 + C) + hL ≤ K0) :
    (∑ i ∈ Finset.range m, ecc i) ≤ K0 * δ := by
  have hm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm0
  have hdm : (0 : ℝ) ≤ δ / (m : ℝ) := div_nonneg hδ0.le hm.le
  have hLc1 : (0 : ℝ) ≤ Lc + 1 := by linarith
  have hdm1 : δ / (m : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hm]; nlinarith
  have hfac : Lc + δ / (m : ℝ) ≤ Lc + 1 := by linarith
  have hterm : ∀ i ∈ Finset.range m, ecc i
      ≤ (Lc + 1) * (δ * lg i + δ * (δ / (m : ℝ)) + C * (δ / (m : ℝ))) + lg i * δ := by
    intro i hi
    have hlgi : (0 : ℝ) ≤ lg i := hlgN i (le_of_lt (Finset.mem_range.mp hi))
    have hA : (0 : ℝ) ≤ δ * lg i + δ * (δ / (m : ℝ)) + C * (δ / (m : ℝ)) := by nlinarith
    calc ecc i ≤ (Lc + δ / (m : ℝ)) * (δ * lg i + δ * (δ / (m : ℝ)) + C * (δ / (m : ℝ)))
          + lg i * δ := by
          refine le_trans (hecc i hi) ?_
          have : δ * (lg i + δ / (m : ℝ)) + C * (δ / (m : ℝ))
              = δ * lg i + δ * (δ / (m : ℝ)) + C * (δ / (m : ℝ)) := by ring
          rw [this]
      _ ≤ (Lc + 1) * (δ * lg i + δ * (δ / (m : ℝ)) + C * (δ / (m : ℝ))) + lg i * δ := by
          have hh := mul_le_mul_of_nonneg_right hfac hA
          linarith [hh]
  have hsum1 : (∑ i ∈ Finset.range m, ecc i)
      ≤ ∑ i ∈ Finset.range m,
          ((Lc + 1) * (δ * lg i + δ * (δ / (m : ℝ)) + C * (δ / (m : ℝ))) + lg i * δ) :=
    Finset.sum_le_sum hterm
  have hsplit : (∑ i ∈ Finset.range m,
        ((Lc + 1) * (δ * lg i + δ * (δ / (m : ℝ)) + C * (δ / (m : ℝ))) + lg i * δ))
      = (Lc + 1) * (δ * (∑ i ∈ Finset.range m, lg i) + (m : ℝ) * (δ * (δ / (m : ℝ)))
          + (m : ℝ) * (C * (δ / (m : ℝ)))) + δ * (∑ i ∈ Finset.range m, lg i) := by
    have h1 : ∀ i ∈ Finset.range m,
        ((Lc + 1) * (δ * lg i + δ * (δ / (m : ℝ)) + C * (δ / (m : ℝ))) + lg i * δ)
        = ((Lc + 1) * (δ * lg i) + (Lc + 1) * (δ * (δ / (m : ℝ)))
            + (Lc + 1) * (C * (δ / (m : ℝ))) + δ * lg i) := by
      intro i hi; ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hsplit, hsumlg] at hsum1
  have hfin : (Lc + 1) * (δ * hL + (m : ℝ) * (δ * (δ / (m : ℝ))) + (m : ℝ) * (C * (δ / (m : ℝ))))
      + δ * hL ≤ K0 * δ := by
    have hm' : (m : ℝ) * (δ * (δ / (m : ℝ))) = δ * δ := by field_simp
    have hm'' : (m : ℝ) * (C * (δ / (m : ℝ))) = C * δ := by field_simp
    rw [hm', hm'']
    have hexp2 : (Lc + 1) * (δ * hL + δ * δ + C * δ) + δ * hL
        = δ * ((Lc + 1) * (hL + δ + C) + hL) := by ring
    rw [hexp2]
    have h1 : (Lc + 1) * (hL + δ + C) + hL ≤ K0 := by nlinarith [hδ1, hLc1, hK]
    calc δ * ((Lc + 1) * (hL + δ + C) + hL) ≤ δ * K0 := mul_le_mul_of_nonneg_left h1 hδ0.le
      _ = K0 * δ := by ring
  linarith [hsum1, hfin]

/-- The `p`-coprimality error is inside `K0 δ`. -/
private theorem budget_P1 (C Lu δ K0 : ℝ) (N : ℕ)
    (hC0 : 0 ≤ C) (hLu0 : 0 ≤ Lu) (hδ0 : 0 < δ) (hN0 : (0 : ℝ) < N)
    (hnumI : 4 / (N : ℝ) ^ kappa1 ≤ δ) (hKbig : 6 * C * (Lu + 7) ≤ K0) :
    C * (Lu + 7) * (2 / (kappa1 * (N : ℝ) ^ kappa1)) ≤ K0 * δ := by
  have hCL : (0 : ℝ) ≤ C * (Lu + 7) := by nlinarith
  have hx0 : (0 : ℝ) < (N : ℝ) ^ kappa1 := Real.rpow_pos_of_pos hN0 _
  have h1 : 2 / (kappa1 * (N : ℝ) ^ kappa1) = (24 : ℝ) / (N : ℝ) ^ kappa1 := by
    rw [show kappa1 = (1 / 12 : ℝ) from rfl]
    field_simp
    norm_num
  have hnb : 24 / (N : ℝ) ^ kappa1 ≤ 6 * δ := by
    have he : 24 / (N : ℝ) ^ kappa1 = 6 * (4 / (N : ℝ) ^ kappa1) := by ring
    rw [he]; linarith [hnumI]
  have hstep : C * (Lu + 7) * (24 / (N : ℝ) ^ kappa1) ≤ C * (Lu + 7) * (6 * δ) :=
    mul_le_mul_of_nonneg_left hnb hCL
  rw [h1]
  calc C * (Lu + 7) * (24 / (N : ℝ) ^ kappa1) ≤ C * (Lu + 7) * (6 * δ) := hstep
    _ = (6 * C * (Lu + 7)) * δ := by ring
    _ ≤ K0 * δ := mul_le_mul_of_nonneg_right hKbig hδ0.le

/-- The five accumulated errors fit in half of epsilon. -/
private theorem budget_final (M K0 hL S1 S2 S3 δ ε : ℝ) (hM : M ≤ K0) (hL' : hL ≤ K0)
    (hS1 : S1 ≤ 3 * K0 * δ) (hS2 : S2 ≤ δ) (hS3 : S3 ≤ K0 * δ)
    (hδ0 : 0 < δ) (hK01 : 1 ≤ K0) (hE : 1000 * K0 * δ ≤ ε) :
    (δ * M + K0 * δ) + S1 + S2 + S3 + δ * hL ≤ ε / 2 := by
  have hd0 : (0 : ℝ) ≤ δ := hδ0.le
  have hK0d : (0 : ℝ) ≤ K0 * δ := by nlinarith [hK01, hδ0.le]
  have h1 : δ * M ≤ K0 * δ := by nlinarith [hM, hK0d, hd0]
  have h2 : δ * hL ≤ K0 * δ := by nlinarith [hL', hK0d, hd0]
  have h3 : δ ≤ K0 * δ := by nlinarith [hK01, hK0d, hd0]
  nlinarith [h1, h2, h3, hS1, hS2, hS3, hE, hK0d, hd0]



private lemma cell_pair_sum_close_pt {K : ℝ → ℝ → ℝ} {T T' U U' ξ E η : ℝ} {N : ℕ}
    (hT : 0 < T) (hTT' : T < T') (hU : 0 < U) (hUU' : U < U')
    (hξ : ξ ∈ Set.Icc T T') (hE : 0 ≤ E) (hη : 0 < η)
    (hnear : ∀ u : ℝ,
      |(∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p),
          K (Real.log (p:ℝ)/Real.log (N:ℝ)) u * (((p:ℝ) - 1))⁻¹)
        - K ξ u * (Real.log T' - Real.log T)| ≤ E)
    (hmass :
      (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
          (((q:ℝ) - 1))⁻¹) ≤ Real.log U' - Real.log U + η) :
      |(∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p),
          ∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
            K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
              * (((p:ℝ) - 1))⁻¹ * (((q:ℝ) - 1))⁻¹)
        - (Real.log T' - Real.log T)
            * (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
                K ξ (Real.log (q:ℝ)/Real.log (N:ℝ)) * (((q:ℝ) - 1))⁻¹)|
      ≤ (Real.log U' - Real.log U + η) * E := by
  have hnear' := hnear
  have hmass' := hmass
  have hWpos : ∀ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
      (0:ℝ) < (((q:ℝ) - 1))⁻¹ := by
    intro q hq
    obtain ⟨-, hprim⟩ := Finset.mem_filter.mp hq
    have h2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hprim.two_le
    have : (0:ℝ) < (q:ℝ) - 1 := by linarith
    positivity
  have hrewrite :
      (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p),
        ∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
          K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
            * (((p:ℝ) - 1))⁻¹ * (((q:ℝ) - 1))⁻¹)
        = ∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
            (((q:ℝ) - 1))⁻¹ *
              (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p),
                K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
                  * (((p:ℝ) - 1))⁻¹) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hfac :
      (Real.log T' - Real.log T)
          * (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
              K ξ (Real.log (q:ℝ)/Real.log (N:ℝ)) * (((q:ℝ) - 1))⁻¹)
        = ∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
            (((q:ℝ) - 1))⁻¹ *
              (K ξ (Real.log (q:ℝ)/Real.log (N:ℝ)) * (Real.log T' - Real.log T)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [hrewrite, hfac, ← Finset.sum_sub_distrib]
  have hbd : ∀ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
      |(((q:ℝ) - 1))⁻¹ *
              (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p),
                K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
                  * (((p:ℝ) - 1))⁻¹)
          - (((q:ℝ) - 1))⁻¹ *
              (K ξ (Real.log (q:ℝ)/Real.log (N:ℝ)) * (Real.log T' - Real.log T))|
        ≤ (((q:ℝ) - 1))⁻¹ * E := by
    intro q hq
    have hw := hWpos q hq
    rw [show (((q:ℝ) - 1))⁻¹ *
              (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p),
                K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
                  * (((p:ℝ) - 1))⁻¹)
          - (((q:ℝ) - 1))⁻¹ *
              (K ξ (Real.log (q:ℝ)/Real.log (N:ℝ)) * (Real.log T' - Real.log T))
          = (((q:ℝ) - 1))⁻¹ *
              ((∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p),
                K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
                  * (((p:ℝ) - 1))⁻¹)
                - K ξ (Real.log (q:ℝ)/Real.log (N:ℝ)) * (Real.log T' - Real.log T)) by ring,
        abs_mul, abs_of_pos hw]
    exact mul_le_mul_of_nonneg_left (hnear' _) (le_of_lt hw)
  calc |∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
        ((((q:ℝ) - 1))⁻¹ *
              (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p),
                K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
                  * (((p:ℝ) - 1))⁻¹)
          - (((q:ℝ) - 1))⁻¹ *
              (K ξ (Real.log (q:ℝ)/Real.log (N:ℝ)) * (Real.log T' - Real.log T)))|
      ≤ ∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
          |(((q:ℝ) - 1))⁻¹ *
              (∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p),
                K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
                  * (((p:ℝ) - 1))⁻¹)
          - (((q:ℝ) - 1))⁻¹ *
              (K ξ (Real.log (q:ℝ)/Real.log (N:ℝ)) * (Real.log T' - Real.log T))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
          (((q:ℝ) - 1))⁻¹ * E := Finset.sum_le_sum hbd
    _ = (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
          (((q:ℝ) - 1))⁻¹) * E := by rw [Finset.sum_mul]
    _ ≤ (Real.log U' - Real.log U + η) * E := mul_le_mul_of_nonneg_right hmass' hE

private lemma cell_limit_close_pt {K : ℝ → ℝ → ℝ} {T T' U U' ξ E η εR : ℝ} {N : ℕ}
    (hT : 0 < T) (hTT' : T < T') (hU : 0 < U) (hUU' : U < U')
    (hξ : ξ ∈ Set.Icc T T') (hE : 0 ≤ E) (hη : 0 < η)
    (hnear : ∀ u : ℝ,
      |(∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p),
          K (Real.log (p:ℝ)/Real.log (N:ℝ)) u * (((p:ℝ) - 1))⁻¹)
        - K ξ u * (Real.log T' - Real.log T)| ≤ E)
    (hmass :
      (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
          (((q:ℝ) - 1))⁻¹) ≤ Real.log U' - Real.log U + η)
    (hR :
      |(∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
          K ξ (Real.log (q:ℝ)/Real.log (N:ℝ)) * (((q:ℝ) - 1))⁻¹)
        - (∫ u in U..U', K ξ u / u)| ≤ εR) :
      |(∑ p ∈ (Finset.Ioc ⌊(N:ℝ)^T⌋₊ ⌊(N:ℝ)^T'⌋₊).filter (fun p => Nat.Prime p),
          ∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
            K (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
              * (((p:ℝ) - 1))⁻¹ * (((q:ℝ) - 1))⁻¹)
        - (Real.log T' - Real.log T) * (∫ u in U..U', K ξ u / u)|
      ≤ (Real.log U' - Real.log U + η) * E + |Real.log T' - Real.log T| * εR := by
  have h1 := cell_pair_sum_close_pt (K := K) (N := N) hT hTT' hU hUU' hξ hE hη hnear hmass
  have hN1 := h1
  have hN2 := hR
  have h2 : |(Real.log T' - Real.log T) *
        (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^U⌋₊ ⌊(N:ℝ)^U'⌋₊).filter (fun q => Nat.Prime q),
          K ξ (Real.log (q:ℝ)/Real.log (N:ℝ)) * (((q:ℝ) - 1))⁻¹)
      - (Real.log T' - Real.log T) * (∫ u in U..U', K ξ u / u)|
      ≤ |Real.log T' - Real.log T| * εR := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left hN2 (abs_nonneg _)
  exact le_trans (abs_sub_le _ _ _) (add_le_add hN1 h2)


set_option maxHeartbeats 40000000 in
/-- The main term of the assembly: the kernel sum with reciprocal weights. -/
private theorem lowerSum5_tendsto_all (F f : ℝ → ℝ) (h : IsLinearSieve F f) (B : ℝ) (hB : 0 < B) :
    Tendsto (fun N : ℕ => lowerSum5 f B N) atTop (𝓝 (lowerIntegral5 f)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨C₀, hC₀⟩ := kernel_bounded F f h
  obtain ⟨M₀, N0M, hM₀⟩ := lowerPairs5_mass_bounded
  set C : ℝ := max C₀ 0 with hCdef
  set M : ℝ := max M₀ 0 with hMdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hM0 : 0 ≤ M := le_max_right _ _
  have hCb : ∀ x ∈ Set.Icc kappa1 kappa2 ×ˢ Set.Icc kappa2 (1/2 - 3*kappa1),
      |f ((1/2 - x.1 - x.2)/kappa1)| ≤ C := by
    intro x hx
    exact le_trans (hC₀ x hx) (le_max_left _ _)
  have hMb : ∀ N : ℕ, N0M ≤ N →
      ∑ q ∈ lowerPairs5 N, (((q.1:ℝ) - 1)⁻¹ * (((q.2:ℝ) - 1)⁻¹)) ≤ M := by
    intro N hN
    exact le_trans (hM₀ N hN) (le_max_left _ _)
  -- the numerical budget
  have hκ1pos : (0:ℝ) < kappa1 := by norm_num [kappa1]
  have hκ2pos : (0:ℝ) < kappa2 := by norm_num [kappa2]
  have hκ12 : kappa1 < kappa2 := by norm_num [kappa1, kappa2]
  set hL : ℝ := Real.log (kappa2/kappa1) with hLdef
  set Lu : ℝ := Real.log ((1/2 - 3*kappa1)/kappa2) with hLudef
  have hL0 : 0 ≤ hL := by
    rw [hLdef]
    apply Real.log_nonneg
    rw [le_div_iff₀ hκ1pos]
    norm_num [kappa1, kappa2]
  have hLu0 : 0 ≤ Lu := by
    rw [hLudef]
    apply Real.log_nonneg
    rw [le_div_iff₀ hκ2pos]
    norm_num [kappa1, kappa2]
  set Lc : ℝ := Real.log ((1/2 - 3*kappa1)/kappa2) with hLcdef
  have hLc0 : 0 ≤ Lc := by
    rw [hLcdef]
    apply Real.log_nonneg
    rw [le_div_iff₀ hκ2pos]
    norm_num [kappa1, kappa2]
  set K0 : ℝ := 4000 * ((C+1)*(M+1)*(hL+1)*(Lu+1) + 42*C*(Lu+7) + 32*C*(hL+1)/kappa2
      + 8*C*(hL+1) + 4*C*Lc + 4*Lc*hL + 4*(hL+1) + 4*M + 4*C + 4*hL + 4*Lc + 1) + 1 with hK0def
  have hCn1 : (0:ℝ) ≤ C+1 := by linarith
  have hMn1 : (0:ℝ) ≤ M+1 := by linarith
  have hLn1 : (0:ℝ) ≤ hL+1 := by linarith
  have hun1 : (0:ℝ) ≤ Lu+1 := by linarith
  have hprod4 : (0:ℝ) ≤ (C+1)*(M+1)*(hL+1)*(Lu+1) :=
    mul_nonneg (mul_nonneg (mul_nonneg hCn1 hMn1) hLn1) hun1
  have hCL7 : (0:ℝ) ≤ 42*C*(Lu+7) := by nlinarith [hC0, hLu0]
  have hCLh : (0:ℝ) ≤ 32*C*(hL+1)/kappa2 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0) hLn1) hκ2pos.le
  have hCLh2 : (0:ℝ) ≤ 8*C*(hL+1) := by nlinarith [hC0, hLn1]
  have hCLc : (0:ℝ) ≤ 4*C*Lc := by nlinarith [hC0, hLc0]
  have hLch : (0:ℝ) ≤ 4*Lc*hL := by nlinarith [hLc0, hL0]
  have hK00 : 0 < K0 := by
    rw [hK0def]
    linarith
  set δ : ℝ := min 1 (ε/(1000*K0)) with hδdef
  have hδ0 : 0 < δ := by
    rw [hδdef]; exact lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := by rw [hδdef]; exact min_le_left _ _
  have hδE : 1000*K0*δ ≤ ε := by
    have hle := min_le_right (1:ℝ) (ε/(1000*K0))
    rw [← hδdef] at hle
    have h2 : 1000*K0*(ε/(1000*K0)) = ε := by field_simp
    nlinarith [hle, h2, hK00.le]
  -- moduli of the kernel in `t` and of the inner integral
  obtain ⟨γf, hγf0, hγf1, hγf⟩ := f_uniform F f h δ hδ0
  obtain ⟨γψ, hγψ0, hγψ⟩ := psi_uniform F f h δ hδ0
  set hcap : ℝ := min (min δ (kappa1*γf)) γψ with hcapdef
  have hcap0 : 0 < hcap := by
    rw [hcapdef]
    exact lt_min (lt_min hδ0 (by positivity)) hγψ0
  obtain ⟨m, hstep, hm0, hhs0, hmh, hhcap⟩ := hstep_choice hcap0 hκ12
  have hhcap1 : hcap ≤ δ := by
    rw [hcapdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hhcap2 : hcap ≤ kappa1*γf := by
    rw [hcapdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hhcap3 : hcap ≤ γψ := by rw [hcapdef]; exact min_le_right _ _
  have hhsδ : hstep ≤ δ := le_trans hhcap hhcap1
  have hhsγ : hstep ≤ kappa1*γf := le_trans hhcap hhcap2
  have hhsψ : hstep ≤ γψ := le_trans hhcap hhcap3
  -- the inner integral
  set Ψ : ℝ → ℝ := fun t => ∫ u in kappa2..(1/2 - 2*kappa1 - t),
    f ((1/2 - t - u)/kappa1)/u with hΨdef
  have hΨ_cont : ContinuousOn Ψ (Set.Icc kappa1 kappa2) := psi_continuousOn F f h
  have hΨ_mod : ∀ t ∈ Set.Icc kappa1 kappa2, ∀ t' ∈ Set.Icc kappa1 kappa2,
      |t - t'| ≤ hstep → |Ψ t - Ψ t'| ≤ δ := by
    intro t ht t' ht' hd
    exact hγψ t ht t' ht' (le_trans hd hhsψ)
  -- numerical slacks, all of the form `const / N^a`
  have hpow : ∀ a : ℝ, 0 < a → Tendsto (fun N : ℕ => (N:ℝ)^a) atTop atTop :=
    fun a ha => (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hnumI : ∀ᶠ N : ℕ in atTop, 4 / (N:ℝ)^kappa1 ≤ δ :=
    ((tendsto_const_nhds.div_atTop (hpow kappa1 hκ1pos)).eventually (eventually_lt_nhds hδ0)).mono (fun N h => le_of_lt h)
  have hnumII : ∀ᶠ N : ℕ in atTop, 8 / (N:ℝ)^kappa2 ≤ δ :=
    ((tendsto_const_nhds.div_atTop (hpow kappa2 hκ2pos)).eventually (eventually_lt_nhds hδ0)).mono (fun N h => le_of_lt h)
  have hnumIII : ∀ᶠ N : ℕ in atTop, 4 / (kappa2 * (N:ℝ)^kappa2) ≤ δ := by
    have h2 : Tendsto (fun N : ℕ => 4 / (kappa2 * (N:ℝ)^kappa2)) atTop (𝓝 0) := by
      have h3 := (tendsto_const_nhds (x := 4/kappa2)).div_atTop (hpow kappa2 hκ2pos)
      refine h3.congr' (Filter.Eventually.of_forall (fun N => ?_))
      simp only [Pi.div_apply, div_div]
    exact (h2.eventually (eventually_lt_nhds hδ0)).mono (fun N h => le_of_lt h)
  have hnumIV : ∀ᶠ N : ℕ in atTop,
      8 * (C+1) * (Lu+7) * ((m:ℝ)+1) / (N:ℝ)^kappa1 ≤ δ :=
    ((tendsto_const_nhds.div_atTop (hpow kappa1 hκ1pos)).eventually (eventually_lt_nhds hδ0)).mono (fun N h => le_of_lt h)
  have hnumV : ∀ᶠ N : ℕ in atTop,
      200 * (C+1) * (hL+2) * ((m:ℝ)+1) / (N:ℝ)^kappa2 ≤ δ :=
    ((tendsto_const_nhds.div_atTop (hpow kappa2 hκ2pos)).eventually (eventually_lt_nhds hδ0)).mono (fun N h => le_of_lt h)
  have hbig : ∀ᶠ N : ℕ in atTop, (4:ℝ) ≤ (N:ℝ)^kappa1 :=
    (hpow kappa1 hκ1pos).eventually (eventually_ge_atTop 4)
  have hfloor : ∀ᶠ N : ℕ in atTop,
      2 ≤ ⌊(N:ℝ)^kappa2⌋₊ ∧ ⌊(N:ℝ)^(1/2 - 3*kappa1)⌋₊ < N := by
    filter_upwards [hbig, eventually_ge_atTop 2] with N hb hN
    have hN1 : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    constructor
    · apply Nat.le_floor
      have h2 : (2:ℝ) ≤ (N:ℝ)^kappa1 := le_trans (by norm_num) hb
      exact le_trans h2
        (Real.rpow_le_rpow_of_exponent_le (le_of_lt hN1) (by norm_num [kappa1, kappa2]))
    · have hx : (N:ℝ)^(1/2 - 3*kappa1) < (N:ℝ)^(1:ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt hN1 (by norm_num [kappa1])
      rw [Real.rpow_one] at hx
      have h1 : (⌊(N:ℝ)^(1/2 - 3*kappa1)⌋₊ : ℝ) ≤ (N:ℝ)^(1/2 - 3*kappa1) :=
        Nat.floor_le (by positivity)
      have h2 : (⌊(N:ℝ)^(1/2 - 3*kappa1)⌋₊ : ℝ) < (N:ℝ) := lt_of_le_of_lt h1 hx
      exact_mod_cast h2
  -- the per cell parameters live in the fixed window
  have hiR : ∀ i ∈ Finset.range m, (i:ℝ) ≤ (m:ℝ) - 1 := by
    intro i hi
    have h2 : ((i:ℕ):ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show i ≤ m - 1 by
        have := Finset.mem_range.mp hi
        omega)
    have h3 : ((m - 1 : ℕ) : ℝ) = (m:ℝ) - 1 := by
      have hm1 : 1 ≤ m := by omega
      push_cast [hm1]
      ring
    linarith
  have hiT : ∀ i ∈ Finset.range m, kappa1 + (i:ℝ)*hstep ∈ Set.Icc kappa1 kappa2 := by
    intro i hi
    have hi1 := hiR i hi
    constructor
    · have : (0:ℝ) ≤ (i:ℝ)*hstep := by positivity
      linarith
    · nlinarith [hmh, hi1, hhs0.le]
  -- per cell mass ceilings
  have hcellmass := Filter.eventually_all_finset (Finset.range m) |>.mpr
    (fun i hi => cell_mass_le (a := kappa2) (b := 1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep))
      hκ2pos
      (by
        have hb : (i:ℝ)*hstep ≤ kappa2 - kappa1 := by
          have hi1 := hiR i hi
          nlinarith [hmh, hhs0.le, hi1]
        have hk1 : kappa1 = 1/12 := rfl
        have hk2 : kappa2 = 29/250 := rfl
        rw [hk1, hk2] at hb ⊢
        nlinarith [hb])
      (by positivity : (0:ℝ) < δ/m))
  -- the upper end of each cell stays inside the window
  have hib : ∀ i ∈ Finset.range m, kappa1 + ((i:ℝ)+1)*hstep ≤ kappa2 := by
    intro i hi
    have hi1 : ((i:ℝ)+1) ≤ (m:ℝ) := by
      have := Finset.mem_range.mp hi
      have h2 : i + 1 ≤ m := by omega
      exact_mod_cast h2
    nlinarith [hmh, hhs0.le, hi1]
  -- the cell limits for the `p` direction, uniform in the weight variable
  have hnear := Filter.eventually_all_finset (Finset.range m) |>.mpr
    (fun i hi =>
      cell_weight_close_family (a := kappa1 + (i:ℝ)*hstep) (b := kappa1 + ((i:ℝ)+1)*hstep)
        (v := kappa1 + (i:ℝ)*hstep)
        (by linarith [hκ1pos, (hiT i hi).1])
        (by nlinarith [hhs0])
        ⟨le_rfl, by linarith [hhs0]⟩
        (fun u t => if t ∈ Set.Icc kappa1 kappa2 ∧ u ∈ Set.Icc kappa2 (1/2 - 3*kappa1)
          then f ((1/2 - t - u)/kappa1) else 0)
        hδ0.le
        (fun u t ht =>
          clampK_osc hδ0.le hγf (hiT i hi).1 (hib i hi) ⟨le_rfl, by linarith [hhs0]⟩
            (fun t' ht' => by
              rw [abs_sub_comm, abs_of_nonneg (by linarith [ht'.1])]
              have hba : kappa1 + ((i:ℝ)+1)*hstep - (kappa1 + (i:ℝ)*hstep) = hstep := by ring
              linarith [ht'.2, hba])
            hhsγ u t ht)
        (fun u => clampK_bounded hCb hC0 (kappa1 + (i:ℝ)*hstep) u)
        (by positivity : (0:ℝ) < δ/m))
  -- the inner integral limits for each cell
  have hcontK : ∀ i ∈ Finset.range m, ContinuousOn
      (fun u : ℝ => f ((1/2 - (kappa1 + (i:ℝ)*hstep) - u)/kappa1))
      (Set.Icc kappa2 (1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep))) := by
    intro i hi
    refine h.2.1.comp (by fun_prop) (fun u hu => ?_)
    show (0:ℝ) < (1/2 - (kappa1 + (i:ℝ)*hstep) - u)/kappa1
    apply div_pos _ hκ1pos
    linarith [hu.2]
  have hR : ∀ᶠ N : ℕ in atTop, ∀ i ∈ Finset.range m,
      |(∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊ ⌊(N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep))⌋₊).filter (fun q : ℕ => Nat.Prime q),
          f ((1/2 - (kappa1 + (i:ℝ)*hstep) - Real.log (q:ℝ)/Real.log (N:ℝ))/kappa1) * (((q:ℝ) - 1))⁻¹)
        - (∫ u in kappa2..(1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep)),
            f ((1/2 - (kappa1 + (i:ℝ)*hstep) - u)/kappa1)/u)| ≤ δ := by
    refine Filter.eventually_all_finset (Finset.range m) |>.mpr (fun i hi => ?_)
    have hlim := q_band_limit (K := fun t u => f ((1/2 - t - u)/kappa1))
      (U := kappa2) (U' := 1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep))
      (ξ := kappa1 + (i:ℝ)*hstep) hκ2pos
      (by
        have h1 := (hiT i hi).2
        have hk1 : kappa1 = 1/12 := rfl
        have hk2 : kappa2 = 29/250 := rfl
        rw [hk1, hk2] at h1 ⊢
        linarith)
      (hcontK i hi)
    simpa only [Real.dist_eq] using hlim.eventually (Metric.closedBall_mem_nhds _ hδ0)
  -- the diagonal band mass of each cell
  have hbmass := Filter.eventually_all_finset (Finset.range m) |>.mpr
    (fun i hi => boundary_band_mass (T := kappa1 + (i:ℝ)*hstep)
      (T' := kappa1 + ((i:ℝ)+1)*hstep)
      (by linarith [hκ1pos, (hiT i hi).1]) (by nlinarith [hhs0]) (hib i hi)
      (by positivity : (0:ℝ) < δ/m))
  -- the non coprime primes of the whole lower band
  have hbadall : ∀ᶠ N : ℕ in atTop,
      (∑ p ∈ ((Finset.Ioc ⌊(N:ℝ)^kappa1⌋₊ ⌊(N:ℝ)^kappa2⌋₊).filter
        (fun p => Nat.Prime p)).filter (fun p => ¬ p.Coprime N), (((p:ℝ) - 1))⁻¹)
        ≤ 2 / (kappa1 * (N:ℝ)^kappa1) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact band_bad_totient_mass (a := kappa1) (b := kappa2) hκ1pos hN
  -- the level replacement, uniform over the region
  have hlev : ∀ᶠ N : ℕ in atTop, ∀ p q : ℕ, p.Prime → q.Prime →
      (N:ℝ)^kappa1 ≤ (p:ℝ) → (p:ℝ) < (N:ℝ)^kappa2 →
      (N:ℝ)^kappa2 ≤ (q:ℝ) → (q:ℝ) < (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ) →
      |f (lowerLevel B N (p*q)) -
        f ((1/2 - Real.log (p:ℝ)/Real.log (N:ℝ) - Real.log (q:ℝ)/Real.log (N:ℝ))/kappa1)| ≤ δ :=
    level_kernel_close F f h B hδ0
  have hcolmass := q_col_mass (Lu := Lu) hLudef
  have hrealmass : ∀ᶠ N : ℕ in atTop, ∀ i ∈ Finset.range m,
      (∑ p ∈ (Finset.range N).filter (fun p : ℕ => p.Prime ∧
          (N:ℝ)^(kappa1 + (i:ℝ)*hstep) ≤ (p:ℝ) ∧ (p:ℝ) < (N:ℝ)^(kappa1 + ((i:ℝ)+1)*hstep)),
        (((p:ℝ)-1))⁻¹)
        ≤ Real.log (kappa1 + ((i:ℝ)+1)*hstep) - Real.log (kappa1 + (i:ℝ)*hstep) + δ/m :=
    Filter.eventually_all_finset (Finset.range m) |>.mpr (fun i hi =>
      real_band_mass_le (a := kappa1 + (i:ℝ)*hstep) (b := kappa1 + ((i:ℝ)+1)*hstep)
        (by linarith [hκ1pos, (hiT i hi).1])
        (by nlinarith [hhs0])
        (by
          have hk : kappa2 < 1 := by norm_num [kappa2]
          linarith [hib i hi, hk])
        (by positivity : (0:ℝ) < δ/m))
  have hfloorb : ∀ᶠ N : ℕ in atTop, 2 ≤ ⌊(N:ℝ)^(kappa2/2)⌋₊ := by
    have h2 := (hpow (kappa2/2) (by linarith [hκ2pos])).eventually (eventually_ge_atTop (2:ℝ))
    filter_upwards [h2] with N hN
    exact (Nat.le_floor_iff' (by norm_num : (2:ℕ) ≠ 0)).2 hN
  have hmain : ∀ᶠ N : ℕ in atTop, |lowerSum5 f B N - lowerIntegral5 f| ≤ ε/2 := by
    filter_upwards [hlev, hnear, hR, hbmass, hcellmass, hbadall, hcolmass, hrealmass,
      hnumI, hnumII, hnumIII, hnumIV, hnumV, hbig, hfloor, hfloorb,
      eventually_ge_atTop 2, eventually_ge_atTop N0M]
      with N hlevN hnearN hRN hbmassN hcellmassN hbadallN hcolN hrealmassN
        hnumI hnumII hnumIII hnumIV hnumV hbigN hfloorN hfloorbN hN hNM
    have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    set Sp : Finset ℕ := (Finset.range N).filter (fun p : ℕ => p.Prime ∧ p.Coprime N ∧
      (N:ℝ)^kappa1 ≤ (p:ℝ) ∧ (p:ℝ) < (N:ℝ)^kappa2) with hSp
    set K2 : ℝ → ℝ → ℝ := fun t u => if t ∈ Set.Icc kappa1 kappa2 ∧
      u ∈ Set.Icc kappa2 (1/2 - 3*kappa1) then f ((1/2 - t - u)/kappa1) else 0 with hK2
    -- (1) level replacement, totient evaluation, clamps
    have hS1 : |lowerSum5 f B N - ∑ p ∈ Sp, ∑ q ∈ (Finset.range N).filter (fun q : ℕ => q.Prime ∧ q.Coprime N ∧ (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ)), K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ)) * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹))| ≤ δ * M := by
      rw [lowerSum5_eq_nested f B N, ← hSp]
      have hpt : ∀ p ∈ Sp, ∀ q ∈ (Finset.range N).filter (fun q : ℕ => q.Prime ∧ q.Coprime N ∧ (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ)),
          |f (lowerLevel B N (p*q)) / (Nat.totient (p*q) : ℝ)
            - K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ)) * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹))|
          ≤ δ * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹)) := by
        intro p hp q hq
        rw [Finset.mem_filter] at hp hq
        obtain ⟨-, hpp, hpc, hp1, hp2⟩ := hp
        obtain ⟨-, hqp, hqc, hq1, hq2⟩ := hq
        have hp0 : (0:ℝ) < p := by exact_mod_cast hpp.pos
        have hq0 : (0:ℝ) < q := by exact_mod_cast hqp.pos
        have hpq : p ≠ q := by
          have hlt : (p:ℝ) < (q:ℝ) := lt_of_lt_of_le hp2 hq1
          intro hh; rw [hh] at hlt; linarith
        have hφ : (Nat.totient (p*q) : ℝ) = ((p:ℝ)-1)*((q:ℝ)-1) := totient_mul_prime hpp hqp hpq
        -- coordinates
        have hN1 : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
        have hL : 0 < Real.log (N:ℝ) := Real.log_pos hN1
        have htp1 : kappa1 ≤ Real.log (p:ℝ)/Real.log (N:ℝ) := coord_ge_of_le hN hpp.pos hp1
        have htp2 : Real.log (p:ℝ)/Real.log (N:ℝ) < kappa2 := by
          rw [div_lt_iff₀ hL]
          have h1 := Real.log_lt_log (by positivity : (0:ℝ) < (p:ℝ)) hp2
          rwa [Real.log_rpow (by positivity : (0:ℝ) < (N:ℝ)) kappa2] at h1
        have hqc1 : kappa2 ≤ Real.log (q:ℝ)/Real.log (N:ℝ) := coord_ge_of_le hN hqp.pos hq1
        have hqc2 : Real.log (q:ℝ)/Real.log (N:ℝ) < 1/2 - 3*kappa1 :=
          coord_lt_of_cross hN hpp.pos hqp.pos hp1 hq2
        have hclamp : K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
            = f ((1/2 - Real.log (p:ℝ)/Real.log (N:ℝ) - Real.log (q:ℝ)/Real.log (N:ℝ))/kappa1) := by
          rw [hK2]
          exact if_pos ⟨⟨htp1, le_of_lt htp2⟩, ⟨hqc1, le_of_lt hqc2⟩⟩
        have hlevel := hlevN p q hpp hqp hp1 hp2 hq1 hq2
        rw [hclamp, hφ, div_eq_mul_inv, mul_inv]
        have hp2' : (2:ℝ) ≤ p := by exact_mod_cast hpp.two_le
        have hq2'' : (2:ℝ) ≤ q := by exact_mod_cast hqp.two_le
        have hw : (0:ℝ) ≤ (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹)) := by
          have h1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
          have h2 : (0:ℝ) < (q:ℝ) - 1 := by linarith
          positivity
        rw [← sub_mul, abs_mul, abs_of_nonneg hw]
        exact mul_le_mul_of_nonneg_right hlevel hw
      have hsplit : (∑ p ∈ Sp, ∑ q ∈ (Finset.range N).filter (fun q : ℕ => q.Prime ∧ q.Coprime N ∧ (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ)), f (lowerLevel B N (p*q)) / (Nat.totient (p*q) : ℝ))
          - (∑ p ∈ Sp, ∑ q ∈ (Finset.range N).filter (fun q : ℕ => q.Prime ∧ q.Coprime N ∧ (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ)), K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ)) * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹)))
          = ∑ p ∈ Sp, ∑ q ∈ (Finset.range N).filter (fun q : ℕ => q.Prime ∧ q.Coprime N ∧ (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ)),
              (f (lowerLevel B N (p*q)) / (Nat.totient (p*q) : ℝ)
                - K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ)) * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹))) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [← Finset.sum_sub_distrib]
      rw [hsplit]
      have hstep1 : |∑ p ∈ Sp, ∑ q ∈ (Finset.range N).filter (fun q : ℕ => q.Prime ∧ q.Coprime N ∧ (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ)),
            (f (lowerLevel B N (p*q)) / (Nat.totient (p*q) : ℝ)
              - K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ)) * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹)))|
          ≤ ∑ p ∈ Sp, ∑ q ∈ (Finset.range N).filter (fun q : ℕ => q.Prime ∧ q.Coprime N ∧ (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ)),
            |f (lowerLevel B N (p*q)) / (Nat.totient (p*q) : ℝ)
              - K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ)) * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹))| := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        exact Finset.sum_le_sum (fun p _ => Finset.abs_sum_le_sum_abs _ _)
      have hstep2 : (∑ p ∈ Sp, ∑ q ∈ (Finset.range N).filter (fun q : ℕ => q.Prime ∧ q.Coprime N ∧ (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ)),
            |f (lowerLevel B N (p*q)) / (Nat.totient (p*q) : ℝ)
              - K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ)) * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹))|)
          ≤ ∑ p ∈ Sp, ∑ q ∈ (Finset.range N).filter (fun q : ℕ => q.Prime ∧ q.Coprime N ∧ (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ)), δ * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹)) :=
        Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun q hq => hpt p hp q hq))
      have hstep3 : (∑ p ∈ Sp, ∑ q ∈ (Finset.range N).filter (fun q : ℕ => q.Prime ∧ q.Coprime N ∧ (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ)), δ * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹)))
          = δ * (∑ p ∈ Sp, ∑ q ∈ (Finset.range N).filter (fun q : ℕ => q.Prime ∧ q.Coprime N ∧ (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ)), (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹))) := by
        simp only [Finset.mul_sum]
      have hstep4 : (∑ p ∈ Sp, ∑ q ∈ (Finset.range N).filter (fun q : ℕ => q.Prime ∧ q.Coprime N ∧ (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ)), (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹))) ≤ M := by
        have hpair : (Finset.range N ×ˢ Finset.range N).filter
            (fun x : ℕ × ℕ =>
              (x.1.Prime ∧ x.1.Coprime N ∧ (N:ℝ)^kappa1 ≤ (x.1:ℝ) ∧ (x.1:ℝ) < (N:ℝ)^kappa2) ∧
              (fun p q : ℕ => q.Prime ∧ q.Coprime N ∧ (N:ℝ)^kappa2 ≤ (q:ℝ) ∧
                (q:ℝ) < (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ)) x.1 x.2) = lowerPairs5 N := by
          simp only [lowerPairs5, Wu08Sum.P2]
          apply Finset.filter_congr
          intro x _
          tauto
        have hsplit2 := sum_filter_product_split (s := Finset.range N)
          (P1 := fun p : ℕ => p.Prime ∧ p.Coprime N ∧ (N:ℝ)^kappa1 ≤ (p:ℝ) ∧ (p:ℝ) < (N:ℝ)^kappa2)
          (P2 := fun p q : ℕ => q.Prime ∧ q.Coprime N ∧ (N:ℝ)^kappa2 ≤ (q:ℝ) ∧
            (q:ℝ) < (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ))
          (g := fun p q => (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹)))
        rw [hSp, ← hsplit2, hpair]
        exact hMb N hNM
      have hfin : δ * (∑ p ∈ Sp, ∑ q ∈ (Finset.range N).filter (fun q : ℕ => q.Prime ∧ q.Coprime N ∧ (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ)), (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹))) ≤ δ * M :=
        mul_le_mul_of_nonneg_left hstep4 hδ0.le
      linarith [hstep1, hstep2, hstep3, hfin]
    -- ================= the `q`-fibre at fixed `p` =================
    set Fq : ℕ → ℝ := fun p =>
      ∑ q ∈ (Finset.range N).filter (fun q : ℕ => q.Prime ∧ q.Coprime N ∧
          (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ)),
        K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
          * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹)) with hFq
    have hlink1 : |lowerSum5 f B N - ∑ p ∈ Sp, Fq p| ≤ δ * M := by
      have hh := hS1
      simp only [hFq] at hh ⊢
      exact hh
    -- ================= (2) drop the coprimality condition on `p` =================
    set Sp2 : Finset ℕ := (Finset.range N).filter
      (fun p : ℕ => p.Prime ∧ (N:ℝ)^kappa1 ≤ (p:ℝ) ∧ (p:ℝ) < (N:ℝ)^kappa2) with hSp2
    have hSp2eq : Sp = Sp2.filter (fun p => p.Coprime N) := by
      rw [hSp, hSp2]
      ext p
      simp only [Finset.mem_filter, Finset.mem_range]
      tauto
    have hSp2mem : ∀ p ∈ Sp2, p.Prime ∧ (N:ℝ)^kappa1 ≤ (p:ℝ) := by
      intro p hp
      rw [hSp2, Finset.mem_filter] at hp
      exact ⟨hp.2.1, hp.2.2.1⟩
    have hbad2 : (∑ p ∈ Sp2.filter (fun p => ¬ p.Coprime N), (((p:ℝ)-1))⁻¹)
        ≤ 2 / (kappa1 * (N:ℝ)^kappa1) := by
      have hex := exceptional_reciprocal_sum_aux Sp2 hN hκ1pos
        (fun p hp => hSp2mem p hp)
      have hstep : (∑ p ∈ Sp2.filter (fun p => ¬ p.Coprime N), (((p:ℝ)-1))⁻¹)
          ≤ 2 * (∑ p ∈ Sp2.filter (fun p => ¬ p.Coprime N), 1/(p:ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro p hp
        have hp2 : 2 ≤ p := (hSp2mem p (Finset.mem_filter.mp hp).1).1.two_le
        have hpR : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
        have h1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
        have h2 : (0:ℝ) < (p:ℝ)/2 := by linarith
        have h3 : (p:ℝ)/2 ≤ (p:ℝ) - 1 := by linarith
        have h4 : 1/((p:ℝ)-1) ≤ 1/((p:ℝ)/2) := one_div_le_one_div_of_le h2 h3
        have e1 : (((p:ℝ)-1))⁻¹ = 1/((p:ℝ)-1) := by rw [one_div]
        have e2 : (1:ℝ)/((p:ℝ)/2) = 2 * (1/(p:ℝ)) := by
          rw [one_div_div]; ring
        linarith [h4, e1, e2]
      calc (∑ p ∈ Sp2.filter (fun p => ¬ p.Coprime N), (((p:ℝ)-1))⁻¹)
          ≤ 2 * (∑ p ∈ Sp2.filter (fun p => ¬ p.Coprime N), 1/(p:ℝ)) := hstep
        _ ≤ 2 * (1 / (kappa1 * (N:ℝ)^kappa1)) := by linarith [hex]
        _ = 2 / (kappa1 * (N:ℝ)^kappa1) := by ring
    have hP1 : |(∑ p ∈ Sp, Fq p) - (∑ p ∈ Sp2, Fq p)|
        ≤ C * (Lu + 7) * (2 / (kappa1 * (N:ℝ)^kappa1)) := by
      have hCL : (0:ℝ) ≤ C * (Lu + 7) := by nlinarith [hC0, hLu0]
      have hpt : ∀ p ∈ Sp2.filter (fun p => ¬ p.Coprime N),
          |Fq p| ≤ C * (Lu + 7) * (((p:ℝ)-1)⁻¹) := by
        intro p hp
        have hp2 := Finset.mem_filter.mp hp
        have hprime : p.Prime := (hSp2mem p hp2.1).1
        have hge : (N:ℝ)^kappa1 ≤ (p:ℝ) := (hSp2mem p hp2.1).2
        have hpR : (2:ℝ) ≤ (p:ℝ) := by
          have := hprime.two_le
          exact_mod_cast this
        have hp1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
        have hcol := hcolN p hge
        rw [hFq]
        have hq : ∀ q ∈ (Finset.range N).filter (fun q : ℕ => q.Prime ∧ q.Coprime N ∧
            (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ)),
            |K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
              * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹))|
              ≤ C * (((p:ℝ)-1)⁻¹) * (((q:ℝ)-1)⁻¹) := by
          intro q hq
          have hq2 : 2 ≤ q := (Finset.mem_filter.mp hq).2.1.two_le
          have hqR : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq2
          have hq1 : (0:ℝ) < (q:ℝ) - 1 := by linarith
          have hK := clampK_bounded hCb hC0 (Real.log (p:ℝ)/Real.log (N:ℝ))
            (Real.log (q:ℝ)/Real.log (N:ℝ))
          have hpos2 : (0:ℝ) < (((p:ℝ)-1)⁻¹) * (((q:ℝ)-1)⁻¹) :=
            mul_pos (inv_pos.mpr hp1) (inv_pos.mpr hq1)
          calc |K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
                * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹))|
              = |K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))|
                * |(((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹))| := abs_mul _ _
            _ = |K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))|
                * ((((p:ℝ)-1)⁻¹) * (((q:ℝ)-1)⁻¹)) := by rw [abs_of_pos hpos2]
            _ ≤ C * ((((p:ℝ)-1)⁻¹) * (((q:ℝ)-1)⁻¹)) :=
                mul_le_mul_of_nonneg_right hK hpos2.le
            _ = C * (((p:ℝ)-1)⁻¹) * (((q:ℝ)-1)⁻¹) := by ring
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        refine le_trans (Finset.sum_le_sum hq) ?_
        have hsum : (∑ q ∈ (Finset.range N).filter (fun q : ℕ => q.Prime ∧ q.Coprime N ∧
            (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ)),
              C * (((p:ℝ)-1)⁻¹) * (((q:ℝ)-1)⁻¹))
            = C * (((p:ℝ)-1)⁻¹) * (∑ q ∈ (Finset.range N).filter (fun q : ℕ => q.Prime ∧ q.Coprime N ∧
            (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ)),
              (((q:ℝ)-1)⁻¹)) := by
          rw [Finset.mul_sum]
        rw [hsum]
        calc C * (((p:ℝ)-1)⁻¹) * (∑ q ∈ (Finset.range N).filter (fun q : ℕ => q.Prime ∧ q.Coprime N ∧
              (N:ℝ)^kappa2 ≤ (q:ℝ) ∧ (q:ℝ) < (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ)), (((q:ℝ)-1)⁻¹))
            ≤ C * (((p:ℝ)-1)⁻¹) * (Lu + 7) := by
              exact mul_le_mul_of_nonneg_left hcol (mul_nonneg hC0 (le_of_lt (inv_pos.mpr hp1)))
          _ = C * (Lu + 7) * (((p:ℝ)-1)⁻¹) := by ring
      have hsplit : (∑ p ∈ Sp2.filter (fun p => p.Coprime N), Fq p)
          + (∑ p ∈ Sp2.filter (fun p => ¬ p.Coprime N), Fq p) = ∑ p ∈ Sp2, Fq p :=
        Finset.sum_filter_add_sum_filter_not Sp2 (fun p => p.Coprime N) Fq
      rw [hSp2eq]
      have hdiffeq : (∑ p ∈ Sp2.filter (fun p => p.Coprime N), Fq p) - (∑ p ∈ Sp2, Fq p)
          = -∑ p ∈ Sp2.filter (fun p => ¬ p.Coprime N), Fq p := by
        rw [← hsplit]; ring
      rw [hdiffeq, abs_neg]
      calc |∑ p ∈ Sp2.filter (fun p => ¬ p.Coprime N), Fq p|
          ≤ ∑ p ∈ Sp2.filter (fun p => ¬ p.Coprime N), |Fq p| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p ∈ Sp2.filter (fun p => ¬ p.Coprime N), C * (Lu + 7) * (((p:ℝ)-1)⁻¹) :=
            Finset.sum_le_sum hpt
        _ = C * (Lu + 7) * (∑ p ∈ Sp2.filter (fun p => ¬ p.Coprime N), (((p:ℝ)-1)⁻¹)) := by
            rw [Finset.mul_sum]
        _ ≤ C * (Lu + 7) * (2 / (kappa1 * (N:ℝ)^kappa1)) :=
            mul_le_mul_of_nonneg_left hbad2 hCL
    -- the `p`-coprimality error is inside the budget
    have hP1b : C * (Lu + 7) * (2 / (kappa1 * (N:ℝ)^kappa1)) ≤ K0 * δ := by
      refine budget_P1 C Lu δ K0 N hC0 hLu0 hδ0 hNpos hnumI ?_
      have h42 : 6*C*(Lu+7) ≤ 42*C*(Lu+7) := by nlinarith [hC0, hLu0]
      have hbig : 42*C*(Lu+7) ≤ 4000*(42*C*(Lu+7)) := by nlinarith [hCL7]
      have hK : 4000*(42*C*(Lu+7)) ≤ K0 := by
        rw [hK0def]; linarith [hprod4, hCL7, hCLh, hCLh2, hCLc, hLch, hM0, hC0, hL0]
      linarith [h42, hbig, hK]
    -- ================= (3) the logarithmic mesh =================
    have hk2pow : (4:ℝ) ≤ (N:ℝ)^kappa2 := by
      have h1 : (N:ℝ)^kappa1 ≤ (N:ℝ)^kappa2 :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num [kappa1, kappa2])
      linarith [hbigN]
    have h1N : (1:ℝ) < (N:ℝ) := by
      rcases lt_or_ge (1:ℝ) (N:ℝ) with h' | h'
      · exact h'
      · exfalso
        have hN1' : (N:ℝ) = 1 := le_antisymm h' hN1
        rw [hN1'] at hk2pow
        simpa using hk2pow
    have hTb : ∀ j : ℕ, j ≤ m →
        kappa1 ≤ kappa1 + (j:ℝ)*hstep ∧ kappa1 + (j:ℝ)*hstep ≤ kappa2 := by
      intro j hj
      constructor
      · have : (0:ℝ) ≤ (j:ℝ)*hstep := mul_nonneg (by positivity) hhs0.le
        linarith
      · have hle : (j:ℝ) ≤ (m:ℝ) := by exact_mod_cast hj
        nlinarith [hmh, hhs0.le, hle]
    have hlwb : ∀ j : ℕ, j ≤ m →
        kappa2 ≤ 1/2 - 2*kappa1 - (kappa1 + (j:ℝ)*hstep) ∧
          1/2 - 2*kappa1 - (kappa1 + (j:ℝ)*hstep) ≤ 1/2 - 3*kappa1 := by
      intro j hj
      have hj1 := hTb j hj
      constructor
      · have h : kappa2 ≤ 1/2 - 2*kappa1 - kappa2 := by norm_num [kappa1, kappa2]
        linarith [hj1.2]
      · linarith [hj1.1]
    have hTbSucc : ∀ i : ℕ, i < m →
        kappa1 ≤ kappa1 + ((i:ℝ)+1)*hstep ∧ kappa1 + ((i:ℝ)+1)*hstep ≤ kappa2 := by
      intro i hi
      have h := hTb (i+1) hi
      simpa only [Nat.cast_add, Nat.cast_one] using h
    have hlwbSucc : ∀ i : ℕ, i < m →
        kappa2 ≤ 1/2 - 2*kappa1 - (kappa1 + ((i:ℝ)+1)*hstep) ∧
          1/2 - 2*kappa1 - (kappa1 + ((i:ℝ)+1)*hstep) ≤ 1/2 - 3*kappa1 := by
      intro i hi
      have h := hlwb (i+1) hi
      simpa only [Nat.cast_add, Nat.cast_one] using h
    set lg : ℕ → ℝ := fun i => Real.log (kappa1 + ((i:ℝ)+1)*hstep) - Real.log (kappa1 + (i:ℝ)*hstep) with hlg
    set cellN : ℕ → Finset ℕ := fun i => (Finset.range N).filter
      (fun p : ℕ => p.Prime ∧ (N:ℝ)^(kappa1 + (i:ℝ)*hstep) ≤ (p:ℝ) ∧
        (p:ℝ) < (N:ℝ)^(kappa1 + ((i:ℝ)+1)*hstep)) with hcellN
    set boxI : ℕ → Finset ℕ := fun i => (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊
      ⌊(N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep))⌋₊).filter (fun q : ℕ => Nat.Prime q) with hboxI
    set iocP : ℕ → Finset ℕ := fun i => (Finset.Ioc ⌊(N:ℝ)^(kappa1 + (i:ℝ)*hstep)⌋₊
      ⌊(N:ℝ)^(kappa1 + ((i:ℝ)+1)*hstep)⌋₊).filter (fun p : ℕ => Nat.Prime p) with hiocP
    set Br : ℝ := 40/(N:ℝ)^kappa2 + 8*hstep/kappa2 + 4*δ/m with hBr
    have hBr0 : (0:ℝ) ≤ Br := by
      rw [hBr]
      have hm : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm0
      have h1 : (0:ℝ) ≤ 40/(N:ℝ)^kappa2 :=
        div_nonneg (by norm_num) (Real.rpow_pos_of_pos hNpos _).le
      have h2 : (0:ℝ) ≤ 8*hstep/kappa2 := div_nonneg (by linarith [hhs0.le]) hκ2pos.le
      have h3 : (0:ℝ) ≤ 4*δ/m := div_nonneg (by linarith [hδ0.le]) hm.le
      linarith
    have hsplit3 : (∑ p ∈ Sp2, Fq p) = ∑ i ∈ Finset.range m, ∑ p ∈ cellN i, Fq p := by
      have h := range_band_chain (s := kappa1) (h := hstep) hN hhs0 m kappa2 hmh
        (fun p : ℕ => p.Prime) Fq
      simpa only [hSp2, hcellN] using h
    -- one mesh cell: the `q`-region becomes a fixed-cutoff box
    have hcell1 : ∀ i ∈ Finset.range m,
        |(∑ p ∈ cellN i, Fq p) - (∑ p ∈ cellN i, ∑ q ∈ boxI i,
            K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
              * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹)))| ≤ C*(lg i + δ/m)*Br := by
      intro i hi
      have hi_lt : i < m := Finset.mem_range.mp hi
      have hTi := hTb i (le_of_lt hi_lt)
      have hTi1 := hTbSucc i hi_lt
      have hcfi := hlwb i (le_of_lt hi_lt)
      have hcfi1 := hlwbSucc i hi_lt
      have hTgi : kappa1 + (i:ℝ)*hstep < kappa1 + ((i:ℝ)+1)*hstep := by
        have : (0:ℝ) < hstep := hhs0
        nlinarith
      have hbandm : (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + ((i:ℝ)+1)*hstep))⌋₊
            ⌊(N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep))⌋₊).filter
          (fun q : ℕ => Nat.Prime q), (((q:ℝ)-1))⁻¹) ≤ 2*hstep/kappa2 + δ/m := by
        have h := hbmassN i hi
        have hTsub2 : (2*(kappa1 + ((i:ℝ)+1)*hstep - (kappa1 + (i:ℝ)*hstep))/kappa2 + δ/m)
            = 2*hstep/kappa2 + δ/m := by ring
        rw [hTsub2] at h
        exact h
      have hpow4 : (4:ℝ) ≤ (N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + ((i:ℝ)+1)*hstep)) :=
        le_trans hk2pow (Real.rpow_le_rpow_of_exponent_le hN1 hcfi1.1)
      have hpow4' : (4:ℝ) ≤ (N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep)) :=
        le_trans hk2pow (Real.rpow_le_rpow_of_exponent_le hN1 hcfi.1)
      have hb1 : 2*((⌊(N:ℝ)^kappa2⌋₊ : ℝ) - 1)⁻¹ ≤ 4/(N:ℝ)^kappa2 := by
        have h := floor_sub_inv_le hk2pow
        simp only [div_eq_mul_inv] at h ⊢
        linarith [h]
      have hb2 : 4*((⌊(N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + ((i:ℝ)+1)*hstep))⌋₊ : ℝ) - 1)⁻¹
          ≤ 8/(N:ℝ)^kappa2 := by
        have h := floor_sub_inv_le hpow4
        have h2 : 8/(N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + ((i:ℝ)+1)*hstep)) ≤ 8/(N:ℝ)^kappa2 := by
          have hp1 : (0:ℝ) < (N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + ((i:ℝ)+1)*hstep)) :=
            Real.rpow_pos_of_pos hNpos _
          have hp2 : (0:ℝ) < (N:ℝ)^kappa2 := Real.rpow_pos_of_pos hNpos _
          have hle : (N:ℝ)^kappa2 ≤ (N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + ((i:ℝ)+1)*hstep)) :=
            Real.rpow_le_rpow_of_exponent_le hN1 hcfi1.1
          exact div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 8) hp2 hle
        simp only [div_eq_mul_inv] at h h2 ⊢
        linarith [h, h2]
      have hb3 : 2/(kappa2*(N:ℝ)^kappa2) ≤ 18/(N:ℝ)^kappa2 := by
        have hkx : (0:ℝ) < (N:ℝ)^kappa2 := Real.rpow_pos_of_pos hNpos _
        have hkinv : 2/kappa2 ≤ 18 := by
          rw [div_le_iff₀ hκ2pos]; norm_num [kappa2]
        have he : 2/(kappa2*(N:ℝ)^kappa2) = (2/kappa2)/(N:ℝ)^kappa2 := by field_simp
        rw [he]
        exact div_le_div_of_nonneg_right hkinv hkx.le
      have hb2' : 4*((⌊(N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep))⌋₊ : ℝ) - 1)⁻¹
          ≤ 8/(N:ℝ)^kappa2 := by
        have h := floor_sub_inv_le hpow4'
        have h2 : 8/(N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep)) ≤ 8/(N:ℝ)^kappa2 := by
          have hp1 : (0:ℝ) < (N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep)) :=
            Real.rpow_pos_of_pos hNpos _
          have hp2 : (0:ℝ) < (N:ℝ)^kappa2 := Real.rpow_pos_of_pos hNpos _
          have hle : (N:ℝ)^kappa2 ≤ (N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep)) :=
            Real.rpow_le_rpow_of_exponent_le hN1 hcfi.1
          exact div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 8) hp2 hle
        simp only [div_eq_mul_inv] at h h2 ⊢
        linarith [h, h2]
      have hbracket : 2*((⌊(N:ℝ)^kappa2⌋₊ : ℝ) - 1)⁻¹
          + 4*((⌊(N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + ((i:ℝ)+1)*hstep))⌋₊ : ℝ) - 1)⁻¹
          + 2/(kappa2*(N:ℝ)^kappa2)
          + 2*(∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + ((i:ℝ)+1)*hstep))⌋₊
              ⌊(N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep))⌋₊).filter
              (fun q : ℕ => Nat.Prime q), (((q:ℝ)-1))⁻¹) ≤ Br := by
        have hb4 : 2*(∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + ((i:ℝ)+1)*hstep))⌋₊
              ⌊(N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep))⌋₊).filter
              (fun q : ℕ => Nat.Prime q), (((q:ℝ)-1))⁻¹) ≤ 4*hstep/kappa2 + 2*δ/m := by
          simp only [div_eq_mul_inv] at hbandm ⊢
          linarith [hbandm]
        rw [hBr]
        have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm0
        have hdm4 : (0:ℝ) ≤ 4*δ/m := div_nonneg (by linarith [hδ0.le]) hmpos.le
        have hh8 : (0:ℝ) ≤ 8*hstep/kappa2 := div_nonneg (by linarith [hhs0.le]) hκ2pos.le
        have hfl1 : (2:ℝ) ≤ ((⌊(N:ℝ)^kappa2⌋₊ : ℝ)) := by
          exact_mod_cast (Nat.le_floor (le_trans (by norm_num) hk2pow))
        have hfl2 : (2:ℝ) ≤ ((⌊(N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + ((i:ℝ)+1)*hstep))⌋₊ : ℝ)) := by
          exact_mod_cast (Nat.le_floor (le_trans (by norm_num) hpow4))
        have ht1 : (0:ℝ) ≤ 2*((⌊(N:ℝ)^kappa2⌋₊ : ℝ) - 1)⁻¹ := by
          have hh : (0:ℝ) < ((⌊(N:ℝ)^kappa2⌋₊ : ℝ) - 1) := by linarith
          exact mul_nonneg (by norm_num) (inv_pos.mpr hh).le
        have ht2 : (0:ℝ) ≤ 4*((⌊(N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + ((i:ℝ)+1)*hstep))⌋₊ : ℝ) - 1)⁻¹ := by
          have hh : (0:ℝ) < ((⌊(N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + ((i:ℝ)+1)*hstep))⌋₊ : ℝ) - 1) :=
            by linarith
          exact mul_nonneg (by norm_num) (inv_pos.mpr hh).le
        have hXinv : (0:ℝ) ≤ ((N:ℝ)^kappa2)⁻¹ :=
          (inv_pos.mpr (Real.rpow_pos_of_pos hNpos _)).le
        have hdm4' : (0:ℝ) ≤ 4*δ*(m:ℝ)⁻¹ := by simpa only [div_eq_mul_inv] using hdm4
        have hh8' : (0:ℝ) ≤ 8*hstep*kappa2⁻¹ := by simpa only [div_eq_mul_inv] using hh8
        simp only [div_eq_mul_inv] at hb1 hb2 hb3 hb4 ⊢
        nlinarith [hb1, hb2, hb3, hb4, hXinv, hdm4', hh8', ht1, ht2]
      have hpt : ∀ p ∈ cellN i,
          |Fq p - (∑ q ∈ boxI i,
            K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
              * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹)))|
            ≤ C * (((p:ℝ)-1)⁻¹) * Br := by
        intro p hp
        obtain ⟨-, hprime, hpge, hplt⟩ := Finset.mem_filter.mp hp
        have hp2 : 2 ≤ p := hprime.two_le
        have hp1R : (0:ℝ) < (p:ℝ) - 1 := by
          have h2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
          linarith
        have hqr := q_region_diff (K := K2) (C := C) (c := 1/2 - 2*kappa1)
          (T := kappa1 + (i:ℝ)*hstep) (T' := kappa1 + ((i:ℝ)+1)*hstep)
          (N := N) (p := p) hN hC0
          (fun t u => clampK_bounded hCb hC0 t u) hTgi.le hpge (le_of_lt hplt) hp2
          (by linarith [hcfi.1, hκ2pos])
          (by linarith)
          (by
            have h : kappa2 ≤ 1/2 - 2*kappa1 := by norm_num [kappa1, kappa2]
            linarith [hTi1.2])
          (by
            have hb1' : 1/2 - 2*kappa1 - (kappa1 + ((i:ℝ)+1)*hstep) < 1 := by
              have h : 1/2 - 2*kappa1 - (kappa1 + ((i:ℝ)+1)*hstep) ≤ 1/2 - 3*kappa1 := hcfi1.2
              have hk : (1:ℝ)/2 - 3*kappa1 < 1 := by norm_num [kappa1]
              linarith
            have h : (N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + ((i:ℝ)+1)*hstep)) < (N:ℝ) := by
              calc (N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + ((i:ℝ)+1)*hstep)) < (N:ℝ)^1 :=
                    Real.rpow_lt_rpow_of_exponent_lt h1N hb1'
                _ = (N:ℝ) := Real.rpow_one _
            have hfr : (⌊(N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + ((i:ℝ)+1)*hstep))⌋₊ : ℝ)
                ≤ (N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + ((i:ℝ)+1)*hstep)) :=
              Nat.floor_le (Real.rpow_pos_of_pos hNpos _).le
            have : (⌊(N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + ((i:ℝ)+1)*hstep))⌋₊ : ℝ) < (N:ℝ) :=
              lt_of_le_of_lt hfr h
            exact_mod_cast this)
          (by
            have hp1 : (N:ℝ)^kappa1 ≤ (p:ℝ) :=
              le_trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [hTi.1])) hpge
            have hle : (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ) ≤ (N:ℝ)^(1/2 - 3*kappa1) := by
              rw [div_le_iff₀ (by positivity)]
              calc (N:ℝ)^(1/2 - 2*kappa1)
                  = (N:ℝ)^((1/2 - 3*kappa1) + kappa1) := by
                    rw [show (1/2:ℝ) - 2*kappa1 = (1/2 - 3*kappa1) + kappa1 by ring]
                _ = (N:ℝ)^(1/2 - 3*kappa1) * (N:ℝ)^kappa1 := Real.rpow_add hNpos _ _
                _ ≤ (N:ℝ)^(1/2 - 3*kappa1) * (p:ℝ) :=
                    mul_le_mul_of_nonneg_left hp1 (Real.rpow_pos_of_pos hNpos _).le
            have hltN : (N:ℝ)^(1/2 - 3*kappa1) < (N:ℝ) := by
              calc (N:ℝ)^(1/2 - 3*kappa1) < (N:ℝ)^1 :=
                    Real.rpow_lt_rpow_of_exponent_lt h1N (by norm_num [kappa1])
                _ = (N:ℝ) := Real.rpow_one _
            have hlt : (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ) < (N:ℝ) := lt_of_le_of_lt hle hltN
            have hfr : (⌊(N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ)⌋₊ : ℝ) ≤ (N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ) :=
              Nat.floor_le (div_nonneg (Real.rpow_pos_of_pos hNpos _).le (by positivity))
            have : (⌊(N:ℝ)^(1/2 - 2*kappa1)/(p:ℝ)⌋₊ : ℝ) < (N:ℝ) := lt_of_le_of_lt hfr hlt
            exact_mod_cast this)
          hfloorN.1
          (by
            have h1 : (N:ℝ)^(kappa2/2) ≤ (N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + ((i:ℝ)+1)*hstep)) :=
              Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [hcfi1.1])
            exact le_trans hfloorbN (Nat.floor_mono h1))
        simp only [mul_assoc] at hqr ⊢
        exact le_trans hqr (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hbracket (le_of_lt (inv_pos.mpr hp1R))) hC0)
      calc |(∑ p ∈ cellN i, Fq p) - (∑ p ∈ cellN i, ∑ q ∈ boxI i,
            K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
              * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹)))|
          = |∑ p ∈ cellN i, (Fq p - ∑ q ∈ boxI i,
              K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
                * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹)))| := by
            rw [Finset.sum_sub_distrib]
        _ ≤ ∑ p ∈ cellN i, |Fq p - ∑ q ∈ boxI i,
              K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
                * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p ∈ cellN i, C * (((p:ℝ)-1)⁻¹) * Br := Finset.sum_le_sum hpt
        _ = C * Br * (∑ p ∈ cellN i, (((p:ℝ)-1)⁻¹)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p hp
            ring
        _ ≤ C * Br * (lg i + δ/m) := by
            apply mul_le_mul_of_nonneg_left _ (by nlinarith [hC0, hBr0])
            have h := hrealmassN i hi
            have hlg' : lg i + δ/m = Real.log (kappa1 + ((i:ℝ)+1)*hstep)
                - Real.log (kappa1 + (i:ℝ)*hstep) + δ/m := by rw [hlg]
            rw [hlg'] at h ⊢
            exact h
        _ = C * (lg i + δ/m) * Br := by ring
    -- one mesh cell: the real `p`-band becomes the integer box
    have hcell2 : ∀ i ∈ Finset.range m,
        |(∑ p ∈ cellN i, ∑ q ∈ boxI i,
            K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
              * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹)))
          - (∑ p ∈ iocP i, ∑ q ∈ boxI i,
            K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
              * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹)))| ≤ 4*C*(Lu+7)/(N:ℝ)^kappa1 := by
      intro i hi
      have hi_lt : i < m := Finset.mem_range.mp hi
      have hTb1 := hTbSucc i hi_lt
      have hlwb1 := hlwb i (le_of_lt hi_lt)
      have hTi := hTb i (le_of_lt hi_lt)
      have hTi1 := hTbSucc i hi_lt
      have hNle : ⌊(N:ℝ)^(kappa1 + ((i:ℝ)+1)*hstep)⌋₊ < N := by
        have hb1 : kappa1 + ((i:ℝ)+1)*hstep < 1 := by
          have hk : kappa2 < 1 := by norm_num [kappa2]
          linarith [hTb1.2, hk]
        have hlt : (N:ℝ)^(kappa1 + ((i:ℝ)+1)*hstep) < (N:ℝ) := by
          calc (N:ℝ)^(kappa1 + ((i:ℝ)+1)*hstep) < (N:ℝ)^1 :=
                Real.rpow_lt_rpow_of_exponent_lt h1N hb1
            _ = (N:ℝ) := Real.rpow_one _
        have hfr : (⌊(N:ℝ)^(kappa1 + ((i:ℝ)+1)*hstep)⌋₊ : ℝ) ≤
            (N:ℝ)^(kappa1 + ((i:ℝ)+1)*hstep) := Nat.floor_le (Real.rpow_pos_of_pos hNpos _).le
        have : (⌊(N:ℝ)^(kappa1 + ((i:ℝ)+1)*hstep)⌋₊ : ℝ) < (N:ℝ) := lt_of_le_of_lt hfr hlt
        exact_mod_cast this
      have h := cell_p_diff K2 (c := 1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep))
        (h := hstep) (i := i) N hN hNle
      -- each boundary sum is at most `C (2 / N^{κ₁}) (Lu + 1)`
      have hbd : ∀ A : ℝ, (N:ℝ)^kappa1 - 1 ≤ A →
          A ≤ (N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep)) →
          |(∑ q ∈ boxI i, K2 (Real.log A/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
              * (((A:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹)))|
            ≤ C * (2/(N:ℝ)^kappa1) * (Lu + 7) := by
        intro A hA hAb
        have hxA : (2:ℝ) ≤ A := by linarith [hbigN]
        have hApos : (0:ℝ) < A - 1 := by linarith
        have hfinv : (((A:ℝ)-1))⁻¹ ≤ 2/(N:ℝ)^kappa1 := by
          have e2 : (2:ℝ)/(N:ℝ)^kappa1 = (((N:ℝ)^kappa1)/2)⁻¹ := by rw [inv_div]
          rw [e2, ← one_div, ← one_div]
          apply one_div_le_one_div_of_le (by linarith [hbigN] : (0:ℝ) < (N:ℝ)^kappa1/2)
          nlinarith [hbigN, hA]
        have hmass₀ : (∑ q ∈ boxI i, (((q:ℝ)-1))⁻¹) ≤ Lc + 1 := by
          have hcm := hcellmassN i hi
          have hm : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm0
          have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm0
          have hdm1 : δ/m ≤ 1 := by
            rw [div_le_iff₀ hm]; linarith [hm1, hδ1]
          have h1 : (0:ℝ) < 1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep) := by
            linarith [hlwb1.1, hκ2pos]
          have hlogU : Real.log (1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep)) - Real.log kappa2 ≤ Lc := by
            rw [hLcdef, ← Real.log_div h1.ne' hκ2pos.ne']
            exact Real.log_le_log (div_pos h1 hκ2pos) (div_le_div_of_nonneg_right hlwb1.2 hκ2pos.le)
          linarith [hcm, hdm1, hlogU]
        have hmass : (∑ q ∈ boxI i, (((q:ℝ)-1))⁻¹) ≤ Lu + 7 := by
          refine le_trans hmass₀ ?_
          have : Lc = Lu := by rw [hLcdef, hLudef]
          rw [this]; linarith [hLu0]
        have hterm : ∀ q ∈ boxI i,
            |K2 (Real.log A/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
              * (((A:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹))|
              ≤ C * (((A:ℝ)-1)⁻¹) * (((q:ℝ)-1)⁻¹) := by
          intro q hq
          have hq2 : 2 ≤ q := (Finset.mem_filter.mp hq).2.two_le
          have hq1 : (0:ℝ) < (q:ℝ) - 1 := by
            have : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq2
            linarith
          have hKb := clampK_bounded hCb hC0 (Real.log A/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
          have hpos : (0:ℝ) < (((A:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹)) :=
            mul_pos (inv_pos.mpr hApos) (inv_pos.mpr hq1)
          calc |K2 (Real.log A/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
              * (((A:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹))|
              = |K2 (Real.log A/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))|
                * |(((A:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹))| := abs_mul _ _
            _ = |K2 (Real.log A/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))|
                * ((((A:ℝ)-1)⁻¹) * (((q:ℝ)-1)⁻¹)) := by rw [abs_of_pos hpos]
            _ ≤ C * ((((A:ℝ)-1)⁻¹) * (((q:ℝ)-1)⁻¹)) :=
                mul_le_mul_of_nonneg_right hKb hpos.le
            _ = C * (((A:ℝ)-1)⁻¹) * (((q:ℝ)-1)⁻¹) := by ring
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        have hsum1 : (∑ q ∈ boxI i, |K2 (Real.log A/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
              * (((A:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹))|)
            ≤ C * (((A:ℝ)-1)⁻¹) * (∑ q ∈ boxI i, (((q:ℝ)-1)⁻¹)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum hterm
        refine le_trans hsum1 ?_
        have hAn : (0:ℝ) ≤ C * (((A:ℝ)-1)⁻¹) :=
          mul_nonneg hC0 (le_of_lt (inv_pos.mpr hApos))
        calc C * (((A:ℝ)-1)⁻¹) * (∑ q ∈ boxI i, (((q:ℝ)-1)⁻¹))
            ≤ C * (((A:ℝ)-1)⁻¹) * (Lu + 7) := mul_le_mul_of_nonneg_left hmass hAn
          _ ≤ C * (2/(N:ℝ)^kappa1) * (Lu + 7) := by
              apply mul_le_mul_of_nonneg_right _ (by linarith [hLu0])
              exact mul_le_mul_of_nonneg_left hfinv hC0
      simp only [mul_assoc] at h ⊢
      refine le_trans h ?_
      have e1 := hbd (⌊(N:ℝ)^(kappa1 + (i:ℝ)*hstep)⌋₊ : ℝ)
        (by
          have hbase : (N:ℝ)^kappa1 ≤ (N:ℝ)^(kappa1 + (i:ℝ)*hstep) :=
            Real.rpow_le_rpow_of_exponent_le hN1 hTi.1
          have h := Nat.lt_floor_add_one ((N:ℝ)^(kappa1 + (i:ℝ)*hstep))
          linarith)
        (by
          have hle : (⌊(N:ℝ)^(kappa1 + (i:ℝ)*hstep)⌋₊ : ℝ) ≤ (N:ℝ)^(kappa1 + (i:ℝ)*hstep) :=
            Nat.floor_le (Real.rpow_pos_of_pos hNpos _).le
          exact le_trans hle (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)))
      have e2 := hbd (⌊(N:ℝ)^(kappa1 + ((i:ℝ)+1)*hstep)⌋₊ : ℝ)
        (by
          have hbase : (N:ℝ)^kappa1 ≤ (N:ℝ)^(kappa1 + ((i:ℝ)+1)*hstep) :=
            Real.rpow_le_rpow_of_exponent_le hN1 hTi1.1
          have h := Nat.lt_floor_add_one ((N:ℝ)^(kappa1 + ((i:ℝ)+1)*hstep))
          linarith)
        (by
          have hle : (⌊(N:ℝ)^(kappa1 + ((i:ℝ)+1)*hstep)⌋₊ : ℝ) ≤
              (N:ℝ)^(kappa1 + ((i:ℝ)+1)*hstep) := Nat.floor_le (Real.rpow_pos_of_pos hNpos _).le
          exact le_trans hle (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)))
      refine le_trans (add_le_add e1 e2) ?_
      have hEq2 : (C * (2/(N:ℝ)^kappa1) * (Lu + 7)) + (C * (2/(N:ℝ)^kappa1) * (Lu + 7))
          = 4*C*(Lu+7)/(N:ℝ)^kappa1 := by
        field_simp
        ring
      rw [hEq2]
      exact le_of_eq (by ring)
    -- one mesh cell: the box sum tends to its integral
    obtain ⟨ecc, hecc⟩ : ∃ e : ℕ → ℝ, ∀ i, e i =
        (Real.log (1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep)) - Real.log kappa2
          + δ/m)*(δ*(lg i + δ/m) + C*(δ/m)) + lg i*δ :=
      ⟨fun i => (Real.log (1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep)) - Real.log kappa2
          + δ/m)*(δ*(lg i + δ/m) + C*(δ/m)) + lg i*δ, fun i => rfl⟩
    have hcell3 : ∀ i ∈ Finset.range m,
        |(∑ p ∈ iocP i, ∑ q ∈ boxI i,
            K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
              * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹))) - lg i * Ψ (kappa1 + (i:ℝ)*hstep)| ≤ ecc i := by
      intro i hi
      have hi_lt : i < m := Finset.mem_range.mp hi
      have hTi := hTb i (le_of_lt hi_lt)
      have hTi1 := hTbSucc i hi_lt
      have hlwb1 := hlwb i (le_of_lt hi_lt)
      have hlg0 : 0 ≤ lg i := by
        rw [hlg]
        apply sub_nonneg.mpr
        apply Real.log_le_log (by linarith [hTi.1, hκ1pos])
        linarith
      -- the `q`-sum against the clamped kernel
      have hRK : |(∑ q ∈ boxI i, K2 (kappa1 + (i:ℝ)*hstep) (Real.log (q:ℝ)/Real.log (N:ℝ))
            * (((q:ℝ)-1))⁻¹)
          - (∫ u in kappa2..(1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep)),
              K2 (kappa1 + (i:ℝ)*hstep) u / u)| ≤ δ := by
        have h := hRN i hi
        have eA : (∑ q ∈ boxI i, K2 (kappa1 + (i:ℝ)*hstep) (Real.log (q:ℝ)/Real.log (N:ℝ))
              * (((q:ℝ)-1))⁻¹)
            = (∑ q ∈ (Finset.Ioc ⌊(N:ℝ)^kappa2⌋₊
                  ⌊(N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep))⌋₊).filter
                (fun q : ℕ => Nat.Prime q),
                f ((1/2 - (kappa1 + (i:ℝ)*hstep) - Real.log (q:ℝ)/Real.log (N:ℝ))/kappa1)
                  * (((q:ℝ)-1))⁻¹) := by
          rw [hboxI]
          apply Finset.sum_congr rfl
          intro q hq
          have hq' := Finset.mem_filter.mp hq
          have hqp : q.Prime := hq'.2
          have hqI := Finset.mem_Ioc.mp hq'.1
          have hx : (N:ℝ)^kappa2 < (q:ℝ) := by
            have h1 : ((⌊(N:ℝ)^kappa2⌋₊ : ℝ)) + 1 ≤ (q:ℝ) := by
              exact_mod_cast (show ⌊(N:ℝ)^kappa2⌋₊ + 1 ≤ q from hqI.1)
            have h2 := Nat.lt_floor_add_one ((N:ℝ)^kappa2)
            linarith
          have hqle : (q:ℝ) ≤ (N:ℝ)^(1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep)) :=
            le_trans (by exact_mod_cast hqI.2) (Nat.floor_le (Real.rpow_pos_of_pos hNpos _).le)
          have hu1 : kappa2 ≤ Real.log (q:ℝ)/Real.log (N:ℝ) :=
            coord_ge_of_le hN hqp.pos (le_of_lt hx)
          have hu2 : Real.log (q:ℝ)/Real.log (N:ℝ) ≤ 1/2 - 3*kappa1 :=
            le_trans (coord_le_of_le hN hqp.pos hqle) hlwb1.2
          have hKq : K2 (kappa1 + (i:ℝ)*hstep) (Real.log (q:ℝ)/Real.log (N:ℝ))
              = f ((1/2 - (kappa1 + (i:ℝ)*hstep) - Real.log (q:ℝ)/Real.log (N:ℝ))/kappa1) := by
            show (if (kappa1 + (i:ℝ)*hstep) ∈ Set.Icc kappa1 kappa2 ∧
                (Real.log (q:ℝ)/Real.log (N:ℝ)) ∈ Set.Icc kappa2 (1/2 - 3*kappa1)
                then f ((1/2 - (kappa1 + (i:ℝ)*hstep) - Real.log (q:ℝ)/Real.log (N:ℝ))/kappa1)
                else 0)
              = f ((1/2 - (kappa1 + (i:ℝ)*hstep) - Real.log (q:ℝ)/Real.log (N:ℝ))/kappa1)
            rw [if_pos]
            exact ⟨hTi, ⟨hu1, hu2⟩⟩
          change K2 (kappa1 + (i:ℝ)*hstep) (Real.log (q:ℝ)/Real.log (N:ℝ)) * (((q:ℝ)-1))⁻¹
            = f ((1/2 - (kappa1 + (i:ℝ)*hstep) - Real.log (q:ℝ)/Real.log (N:ℝ))/kappa1) * (((q:ℝ)-1))⁻¹
          rw [hKq]
        have eB : (∫ u in kappa2..(1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep)),
              K2 (kappa1 + (i:ℝ)*hstep) u / u)
            = (∫ u in kappa2..(1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep)),
                f ((1/2 - (kappa1 + (i:ℝ)*hstep) - u)/kappa1)/u) := by
          apply intervalIntegral.integral_congr
          intro u hu
          rw [Set.uIcc_of_le hlwb1.1] at hu
          have hu1 : kappa2 ≤ u := hu.1
          have hu2 : u ≤ 1/2 - 3*kappa1 := le_trans hu.2 hlwb1.2
          have hKq : K2 (kappa1 + (i:ℝ)*hstep) u
              = f ((1/2 - (kappa1 + (i:ℝ)*hstep) - u)/kappa1) := by
            show (if (kappa1 + (i:ℝ)*hstep) ∈ Set.Icc kappa1 kappa2 ∧
                u ∈ Set.Icc kappa2 (1/2 - 3*kappa1)
                then f ((1/2 - (kappa1 + (i:ℝ)*hstep) - u)/kappa1) else 0)
              = f ((1/2 - (kappa1 + (i:ℝ)*hstep) - u)/kappa1)
            rw [if_pos]
            exact ⟨hTi, ⟨hu1, hu2⟩⟩
          change K2 (kappa1 + (i:ℝ)*hstep) u / u
            = f ((1/2 - (kappa1 + (i:ℝ)*hstep) - u)/kappa1)/u
          rw [hKq]
        rw [eA, eB]
        exact h
      have hneare : ∀ u : ℝ,
          |(∑ p ∈ iocP i, K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) u * (((p:ℝ) - 1))⁻¹)
            - K2 (kappa1 + (i:ℝ)*hstep) u
              * (Real.log (kappa1 + ((i:ℝ)+1)*hstep) - Real.log (kappa1 + (i:ℝ)*hstep))|
          ≤ δ*(lg i + δ/m) + C*(δ/m) := by
        intro u
        have hh := hnearN i hi u
        rw [hlg]
        exact hh
      have hE0 : (0:ℝ) ≤ δ*(lg i + δ/m) + C*(δ/m) := by
        have hm : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm0
        have h1 : (0:ℝ) ≤ δ/m := div_nonneg hδ0.le hm.le
        nlinarith [hδ0.le, hlg0, hC0, h1]
      have hcl := cell_limit_close_pt (K := K2) (N := N) (T := kappa1 + (i:ℝ)*hstep)
        (T' := kappa1 + ((i:ℝ)+1)*hstep) (U := kappa2)
        (U' := 1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep)) (ξ := kappa1 + (i:ℝ)*hstep)
        (E := δ*(lg i + δ/m) + C*(δ/m)) (η := δ/(m:ℝ)) (εR := δ)
        (by linarith [hTi.1, hκ1pos])
        (by linarith)
        hκ2pos
        (by
          have h1 : (i:ℝ)*hstep ≤ kappa2 - kappa1 := by
            have hi1 := hiR i hi
            nlinarith [hmh, hhs0.le, hi1]
          have h2 : kappa2 < 1/2 - 2*kappa1 - kappa2 := by norm_num [kappa1, kappa2]
          linarith)
        ⟨le_rfl, by linarith⟩ hE0
        (by
          have hm : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm0
          exact div_pos hδ0 hm)
        hneare (hcellmassN i hi) hRK
      have hPsi : (∫ u in kappa2..(1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep)),
            K2 (kappa1 + (i:ℝ)*hstep) u / u) = Ψ (kappa1 + (i:ℝ)*hstep) := by
        rw [hΨdef]
        apply intervalIntegral.integral_congr
        intro u hu
        rw [Set.uIcc_of_le hlwb1.1] at hu
        have hu1 : kappa2 ≤ u := hu.1
        have hu2 : u ≤ 1/2 - 3*kappa1 := le_trans hu.2 hlwb1.2
        have hKq : K2 (kappa1 + (i:ℝ)*hstep) u
            = f ((1/2 - (kappa1 + (i:ℝ)*hstep) - u)/kappa1) := by
          show (if (kappa1 + (i:ℝ)*hstep) ∈ Set.Icc kappa1 kappa2 ∧
              u ∈ Set.Icc kappa2 (1/2 - 3*kappa1)
              then f ((1/2 - (kappa1 + (i:ℝ)*hstep) - u)/kappa1) else 0)
            = f ((1/2 - (kappa1 + (i:ℝ)*hstep) - u)/kappa1)
          rw [if_pos]
          exact ⟨hTi, ⟨hu1, hu2⟩⟩
        change K2 (kappa1 + (i:ℝ)*hstep) u / u
          = f ((1/2 - (kappa1 + (i:ℝ)*hstep) - u)/kappa1)/u
        rw [hKq]
      rw [hPsi] at hcl
      have hlogT : Real.log (kappa1 + ((i:ℝ)+1)*hstep) - Real.log (kappa1 + (i:ℝ)*hstep) = lg i := by
        rw [hlg]
      simp only [hiocP, hboxI, hlogT, mul_assoc] at hcl ⊢
      refine le_trans hcl ?_
      rw [abs_of_nonneg hlg0]
      exact le_of_eq (hecc i).symm
    -- ================= (4) summing the cells =================
    have hsumlg : (∑ i ∈ Finset.range m, lg i) = hL := by
      have h := sum_log_ratio kappa1 kappa2 hstep hκ1pos hhs0 m hmh
      rw [hLdef, ← h]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i + 1 ≤ m := Finset.mem_range.mp hi
      have h1 : (0:ℝ) < kappa1 + ((i:ℝ)+1)*hstep := by
        have h := (hTbSucc i (Finset.mem_range.mp hi)).1
        linarith [h, hκ1pos]
      have h2 : (0:ℝ) < kappa1 + (i:ℝ)*hstep := by
        have h := (hTb i (le_of_lt (Finset.mem_range.mp hi))).1
        linarith [h, hκ1pos]
      rw [hlg, Real.log_div h1.ne' h2.ne']
    have hlgN : ∀ i : ℕ, i ≤ m → 0 ≤ lg i := by
      intro i hi
      rw [hlg]
      have hT := hTb i hi
      have h1 : (0:ℝ) < kappa1 + (i:ℝ)*hstep := by linarith [hT.1, hκ1pos]
      have h2 : kappa1 + (i:ℝ)*hstep ≤ kappa1 + ((i:ℝ)+1)*hstep := by
        nlinarith [hhs0.le]
      exact sub_nonneg.mpr (Real.log_le_log h1 h2)
    have hdel : (∑ i ∈ Finset.range m, δ/(m:ℝ)) = δ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hm : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm0
      field_simp
    -- the accumulated errors of the three cell steps
    -- the ceilings entering the `p`-cell budget
    have hCLnB : (0:ℝ) ≤ C * (hL + 1) := mul_nonneg hC0 hLn1
    have hCLkB : (0:ℝ) ≤ C*(hL+1)/kappa2 := div_nonneg hCLnB hκ2pos.le
    have hKb : 16*C*(hL+1)/kappa2 ≤ K0 := by
      have h16 : 16*C*(hL+1)/kappa2 ≤ 32*C*(hL+1)/kappa2 := by
        have e : 32*C*(hL+1)/kappa2 = 2*(16*C*(hL+1)/kappa2) := by ring
        have h0 : (0:ℝ) ≤ 16*C*(hL+1)/kappa2 := div_nonneg (by nlinarith [hCLnB]) hκ2pos.le
        rw [e]; linarith
      have h2 : 32*C*(hL+1)/kappa2 ≤ K0 := by
        have h0 : (0:ℝ) ≤ 32*C*(hL+1)/kappa2 := div_nonneg (by nlinarith [hCLnB]) hκ2pos.le
        have h : 32*C*(hL+1)/kappa2 ≤ 4000*(32*C*(hL+1)/kappa2) := by linarith
        have h3 : 4000*(32*C*(hL+1)/kappa2) ≤ K0 := by
          rw [hK0def]; linarith [hprod4, hCL7, hCLh, hCLh2, hCLc, hLch, hM0, hC0, hL0, hLc0]
        linarith [h, h3]
      linarith [h16, h2]
    have hKb2 : 8*(C*(hL+1)) ≤ K0 := by
      have h2 : 8*C*(hL+1) ≤ K0 := by
        have h : 8*C*(hL+1) ≤ 4000*(8*C*(hL+1)) := by linarith [hCLh2]
        have h3 : 4000*(8*C*(hL+1)) ≤ K0 := by
          rw [hK0def]; linarith [hprod4, hCL7, hCLh, hCLh2, hCLc, hLch, hM0, hC0, hL0, hLc0]
        linarith [h, h3]
      simpa only [mul_assoc] using h2
    have hKb0 : 80*C*(hL+1)/(N:ℝ)^kappa2 ≤ δ := by
      have hm : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm0
      have hV : 200*(C+1)*(hL+2)*((m:ℝ)+1)/(N:ℝ)^kappa2 ≤ δ := hnumV
      refine le_trans ?_ hV
      apply div_le_div_of_nonneg_right _ (Real.rpow_pos_of_pos hNpos _).le
      have hm0' : (0:ℝ) ≤ (m:ℝ) := hm.le
      have h2 : 80*C*(hL+1) ≤ 80*(C+1)*(hL+2) := by nlinarith [hC0, hLn1]
      have h0 : (0:ℝ) ≤ 80*(C+1)*(hL+2) := by nlinarith [hC0, hLn1]
      have h3 : 80*(C+1)*(hL+2) ≤ 80*(C+1)*(hL+2)*((m:ℝ)+1) := by
        nlinarith [h0, hm0', mul_nonneg h0 hm0']
      have h4 : 80*(C+1)*(hL+2)*((m:ℝ)+1) ≤ 200*(C+1)*(hL+2)*((m:ℝ)+1) := by
        have hpos : (0:ℝ) ≤ (C+1)*(hL+2)*((m:ℝ)+1) := by
          have h1 : (0:ℝ) ≤ C + 1 := by linarith
          have h2' : (0:ℝ) ≤ hL + 2 := by linarith
          have h3' : (0:ℝ) ≤ (m:ℝ) + 1 := by linarith
          nlinarith [mul_nonneg h1 h2', h3']
        nlinarith [hpos]
      linarith [h2, h3, h4]
    have hBrB : Br ≤ 40/(N:ℝ)^kappa2 + 8*δ/kappa2 + 4*δ/m := by
      rw [hBr]
      have h8 : 8*hstep/kappa2 ≤ 8*δ/kappa2 :=
        div_le_div_of_nonneg_right (by linarith [hhsδ]) hκ2pos.le
      linarith
    have hS1e : (∑ i ∈ Finset.range m, C*(lg i + δ/m)*Br) ≤ 3*K0*δ :=
      budget_S1 C hL δ Br K0 N m lg hC0 hL0 hδ0 hδ1 hm0 hBr0 hκ2pos hNpos
        (by linarith [hK00] : (1:ℝ) ≤ K0) hsumlg hBrB hKb hKb2 hKb0
    have hS2e : (∑ i ∈ Finset.range m, 4*C*(Lu+7)/(N:ℝ)^kappa1) ≤ δ :=
      budget_S2 C Lu δ N m hC0 hLu0 hδ0 hm0 hNpos hN1 hnumIV
    have hKtot : (Lc + 1) * (hL + 1 + C) + hL ≤ K0 := by
      have h2 : Lc*hL + Lc*C + Lc + hL + 1 + C + hL ≤ K0 := by
        rw [hK0def]
        linarith [hprod4, hCL7, hCLh, hCLh2, hCLc, hLch, hM0, hC0, hL0, hLc0]
      have hexp : (Lc + 1) * (hL + 1 + C) + hL
          = Lc*hL + Lc*C + Lc + hL + 1 + C + hL := by ring
      rw [hexp]; exact h2
    have hecc_le : ∀ i ∈ Finset.range m,
        ecc i ≤ (Lc + δ/m)*(δ*(lg i + δ/m) + C*(δ/m)) + lg i*δ := by
      intro i hi
      have hi_lt : i < m := Finset.mem_range.mp hi
      have hlwb1 := hlwb i (le_of_lt hi_lt)
      have h1 : (0:ℝ) < 1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep) := by
        linarith [hlwb1.1, hκ2pos]
      have hlogU : Real.log (1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep)) - Real.log kappa2 ≤ Lc := by
        rw [hLcdef, ← Real.log_div h1.ne' hκ2pos.ne']
        exact Real.log_le_log (div_pos h1 hκ2pos) (div_le_div_of_nonneg_right hlwb1.2 hκ2pos.le)
      have hlgi : (0:ℝ) ≤ lg i := hlgN i (le_of_lt hi_lt)
      have hm : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm0
      have hdm : (0:ℝ) ≤ δ/m := div_nonneg hδ0.le hm.le
      have hfac : Real.log (1/2 - 2*kappa1 - (kappa1 + (i:ℝ)*hstep)) - Real.log kappa2 + δ/m
          ≤ Lc + δ/m := by linarith
      have hA : (0:ℝ) ≤ δ*(lg i + δ/m) + C*(δ/m) := by nlinarith
      rw [hecc i]
      have hh := mul_le_mul_of_nonneg_right hfac hA
      linarith [hh]
    have hS3e : (∑ i ∈ Finset.range m, ecc i) ≤ K0*δ :=
      budget_S3 C Lc hL δ K0 m lg ecc hC0 hLc0 hL0 hδ0 hδ1 hm0 hecc_le hlgN hsumlg hKtot
    -- the mesh comparison
    have hmesh : |(∑ i ∈ Finset.range m,
          Real.log ((kappa1 + ((i:ℝ)+1)*hstep)/(kappa1 + (i:ℝ)*hstep)) * Ψ (kappa1 + (i:ℝ)*hstep))
        - lowerIntegral5 f| ≤ δ*hL := by
      have hF : lowerIntegral5 f = ∫ t in kappa1..kappa2, Ψ t / t := by
        rw [hΨdef]
        rfl
      rw [hF]
      have := mesh_vs_integral (Ψ := Ψ) (h := hstep) (ω := δ) hhs0 hmh
        (fun i => kappa1 + (i:ℝ)*hstep)
        (fun i hi => ⟨le_rfl, by linarith⟩) hΨ_cont (fun t ht t' ht' hd => hΨ_mod t ht t' ht' hd)
      exact this
    have hLpos : (0:ℝ) ≤ hL := hL0
    -- ================= (5) the epsilon assembly =================
    have hA1 : |lowerSum5 f B N - ∑ p ∈ Sp, Fq p| ≤ δ*M := hlink1
    have hA2 : |(∑ p ∈ Sp, Fq p) - (∑ p ∈ Sp2, Fq p)| ≤ K0 * δ := le_trans hP1 hP1b
    have hA3 : |(∑ p ∈ Sp2, Fq p) - (∑ i ∈ Finset.range m, ∑ p ∈ cellN i, Fq p)| = 0 := by
      rw [hsplit3]; simp
    have hA4 : |(∑ i ∈ Finset.range m, ∑ p ∈ cellN i, Fq p)
        - (∑ i ∈ Finset.range m, ∑ p ∈ cellN i, ∑ q ∈ boxI i,
            K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
              * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹)))| ≤ ∑ i ∈ Finset.range m, C*(lg i + δ/m)*Br := by
      rw [← Finset.sum_sub_distrib]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      exact Finset.sum_le_sum hcell1
    have hA5 : |(∑ i ∈ Finset.range m, ∑ p ∈ cellN i, ∑ q ∈ boxI i,
            K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
              * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹)))
        - (∑ i ∈ Finset.range m, ∑ p ∈ iocP i, ∑ q ∈ boxI i,
            K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
              * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹)))| ≤ ∑ i ∈ Finset.range m, 4*C*(Lu+7)/(N:ℝ)^kappa1 := by
      rw [← Finset.sum_sub_distrib]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      exact Finset.sum_le_sum hcell2
    have hA6 : |(∑ i ∈ Finset.range m, ∑ p ∈ iocP i, ∑ q ∈ boxI i,
            K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
              * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹)))
        - (∑ i ∈ Finset.range m, lg i * Ψ (kappa1 + (i:ℝ)*hstep))| ≤ ∑ i ∈ Finset.range m, ecc i := by
      rw [← Finset.sum_sub_distrib]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      exact Finset.sum_le_sum hcell3
    have hA7 : |(∑ i ∈ Finset.range m, lg i * Ψ (kappa1 + (i:ℝ)*hstep))
        - lowerIntegral5 f| ≤ δ*hL := by
      have hsumEq : (∑ i ∈ Finset.range m, lg i * Ψ (kappa1 + (i:ℝ)*hstep))
          = (∑ i ∈ Finset.range m,
              Real.log ((kappa1 + ((i:ℝ)+1)*hstep)/(kappa1 + (i:ℝ)*hstep))
                * Ψ (kappa1 + (i:ℝ)*hstep)) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i + 1 ≤ m := Finset.mem_range.mp hi
        have h1 : (0:ℝ) < kappa1 + ((i:ℝ)+1)*hstep := by
          have h := (hTbSucc i (Finset.mem_range.mp hi)).1
          linarith [h, hκ1pos]
        have h2 : (0:ℝ) < kappa1 + (i:ℝ)*hstep := by
          have h := (hTb i (le_of_lt (Finset.mem_range.mp hi))).1
          linarith [h, hκ1pos]
        rw [hlg, Real.log_div h1.ne' h2.ne']
      rw [hsumEq]
      exact hmesh
    -- the chain
    have htot : |lowerSum5 f B N - lowerIntegral5 f|
        ≤ (δ*M + K0*δ) + (∑ i ∈ Finset.range m, C*(lg i + δ/m)*Br)
          + (∑ i ∈ Finset.range m, 4*C*(Lu+7)/(N:ℝ)^kappa1)
          + (∑ i ∈ Finset.range m, ecc i) + δ*hL := by
      have hA2' : |(∑ p ∈ Sp, Fq p) - (∑ i ∈ Finset.range m, ∑ p ∈ cellN i, Fq p)| ≤ K0 * δ := by
        refine le_trans ?_ hA2
        exact le_of_eq (by rw [← hsplit3])
      have h1 := abs_sub_le (lowerSum5 f B N) (∑ p ∈ Sp, Fq p) (lowerIntegral5 f)
      have e1 := abs_sub_le (∑ p ∈ Sp, Fq p) (∑ i ∈ Finset.range m, ∑ p ∈ cellN i, Fq p)
        (lowerIntegral5 f)
      have e5 := abs_sub_le (∑ i ∈ Finset.range m, ∑ p ∈ cellN i, Fq p)
        (∑ i ∈ Finset.range m, ∑ p ∈ cellN i, ∑ q ∈ boxI i,
            K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
              * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹))) (lowerIntegral5 f)
      have e2 := abs_sub_le (∑ i ∈ Finset.range m, ∑ p ∈ cellN i, ∑ q ∈ boxI i,
            K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
              * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹)))
        (∑ i ∈ Finset.range m, ∑ p ∈ iocP i, ∑ q ∈ boxI i,
            K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
              * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹))) (lowerIntegral5 f)
      have e6 := abs_sub_le (∑ i ∈ Finset.range m, ∑ p ∈ iocP i, ∑ q ∈ boxI i,
            K2 (Real.log (p:ℝ)/Real.log (N:ℝ)) (Real.log (q:ℝ)/Real.log (N:ℝ))
              * (((p:ℝ)-1)⁻¹ * (((q:ℝ)-1)⁻¹)))
        (∑ i ∈ Finset.range m, lg i * Ψ (kappa1 + (i:ℝ)*hstep)) (lowerIntegral5 f)
      linarith [h1, e1, e5, e2, e6, hA1, hA2', hA4, hA5, hA6, hA7]
    -- the total budget
    have hbudget : (δ*M + K0*δ) + (∑ i ∈ Finset.range m, C*(lg i + δ/m)*Br)
          + (∑ i ∈ Finset.range m, 4*C*(Lu+7)/(N:ℝ)^kappa1)
          + (∑ i ∈ Finset.range m, ecc i) + δ*hL ≤ ε/2 := by
      have hM1 : M ≤ K0 := by
        have h : 4*M ≤ K0 := by
          rw [hK0def]; linarith [hprod4, hCL7, hCLh, hCLh2, hCLc, hLch, hM0, hC0, hL0, hLc0]
        linarith
      have hL1 : hL ≤ K0 := by
        have h : 4*hL ≤ K0 := by
          rw [hK0def]; linarith [hprod4, hCL7, hCLh, hCLh2, hCLc, hLch, hM0, hC0, hL0, hLc0]
        linarith
      exact budget_final M K0 hL _ _ _ δ ε hM1 hL1 hS1e hS2e hS3e hδ0 (by linarith [hK00] : (1:ℝ) ≤ K0) hδE
    linarith [htot, hbudget]

  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hmain
  refine ⟨N0, fun N hN => ?_⟩
  rw [Real.dist_eq]
  have h := hN0 N hN
  linarith

/-- LEAF. Wu 2004 page 39 equation 10.5, application of Lemmas 2.2 and 2.3.
This estimates only the count by its finite prime sum main term.
The replacement of li N by N over log N is included in the normalized error. -/
theorem main5_lower (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        main5 f B N - η * Θ N ≤ sieveTerms N 5 := by
  sorry

/-- LEAF. Wu 2004 page 39 equation 10.5, replacement of prime sums by integrals.
The coprimality removal and finite logarithmic level loss belong to this limit.
There is no sieve count or Euler product in this statement. -/
theorem lowerSum5_tendsto (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) :
    Tendsto (lowerSum5 f B) evenAtTop (𝓝 (lowerIntegral5 f)) := by
  have ht : Tendsto (fun N : ℕ => lowerSum5 f B N) atTop (𝓝 (lowerIntegral5 f)) :=
    lowerSum5_tendsto_all F f h B hB
  exact tendsto_inf_left (x₂ := principal {N : ℕ | Even N}) ht

/-- Exact normalization of the finite Upsilon 5 main term. -/
theorem main5_ratio (f : ℝ → ℝ) (B : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    main5 f B N / Θ N = scaledDensity N * lowerSum5 f B N := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  unfold main5 scaledDensity Θ
  field_simp [(CN_pos N).ne', hlog.ne', hpos.ne']
  <;> ring

/-- The finite Upsilon 5 main term tends to its exact integral coefficient.
CONDITIONAL ON the two OPEN normalization limits and IsLinearSieve. -/
theorem main5_tendsto (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) :
    Tendsto (fun N => main5 f B N / Θ N) evenAtTop
      (𝓝 (integralTerms F f ω 5)) := by
  have ht := scaledDensity_tendsto.mul (lowerSum5_tendsto F f h B hB)
  have ht' : Tendsto (fun N => scaledDensity N * lowerSum5 f B N)
      evenAtTop (𝓝 (integralTerms F f ω 5)) := by
    convert ht using 1
    change 𝓝 (2 / (kappa1 * exp eulerMascheroniConstant) * lowerIntegral5 f) = _
    rfl
  apply ht'.congr'
  filter_upwards [(eventually_ge_atTop (2 : ℕ)).filter_mono inf_le_left] with N hN
  exact (main5_ratio f B hN).symm

/-- The exact lower_F5 conclusion follows from strictly smaller analytic leaves.
OPEN through main5_lower, lowerSum5_tendsto and scaledDensity_tendsto. -/
theorem lower_F5_supplied (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 5 - ε) * Θ N ≤ sieveTerms N 5 := by
  exact lower_of_main _ _ (main5 f) (main5_lower F f h)
    (fun B hB => main5_tendsto F f ω h B hB)

end LeanLab.ChenDoubleSieve.Task348
