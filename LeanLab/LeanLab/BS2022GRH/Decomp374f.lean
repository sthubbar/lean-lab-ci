/- AI wrote this Lean code for CODEX task374. Goldbach is open.
Separate the dyadic sum for one cofactor from the outer totient sum in display 16.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Decomp374a
import LeanLab.BS2022GRH.PublishedInputs232

namespace LeanLab.BS2022GRH.Decomp374f
open Real Finset Classical ChenThresholdGRH Decomp148a
noncomputable section

/-- The per block scalar bound on the last line of display 15, journal p. 1225. -/
def largeFactor (X Y D D₀ : ℝ) : ℝ :=
  4 * D * √(X * Y) + 2 * (√X + √Y) * √(X * Y) + X * Y / D₀

/-! ### The analytic block bound -/

/-- `√(A+B) ≤ √A + √B` for nonnegative `A`, `B`. -/
private lemma sqrt_add_le_add_sqrt {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    √(A + B) ≤ √A + √B := by
  have h2 : 0 ≤ √A + √B := by positivity
  have h1 : A + B ≤ (√A + √B) ^ 2 := by
    rw [add_sq, Real.sq_sqrt hA, Real.sq_sqrt hB]
    nlinarith [mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B)]
  calc √(A + B) ≤ √((√A + √B) ^ 2) := Real.sqrt_le_sqrt h1
    _ = √A + √B := Real.sqrt_sq h2

/-- `√(Y + 4R²) ≤ √Y + 2R`. -/
private lemma sqrt_add_four_sq_le {Y R : ℝ} (hY : 0 ≤ Y) (hR : 0 ≤ R) :
    √(Y + 4 * R ^ 2) ≤ √Y + 2 * R := by
  have hsq : 4 * R ^ 2 = (2 * R) ^ 2 := by ring
  rw [hsq]
  calc √(Y + (2 * R) ^ 2) ≤ √Y + √((2 * R) ^ 2) :=
        sqrt_add_le_add_sqrt hY (by positivity)
    _ = √Y + 2 * R := by
        rw [Real.sqrt_sq (by positivity : (0:ℝ) ≤ 2 * R)]

/-- The one-block estimate: the `hblock` right side at a block size `R` with
`D₀ ≤ R ≤ D` is at most `largeFactor X Y D D₀`. -/
private lemma block_bound_le_largeFactor {X Y D D₀ R : ℝ}
    (hX : 25 ≤ X) (hY : 25 ≤ Y) (hD₀ : 1 < D₀) (hD₀D : D₀ ≤ D)
    (hR₀ : D₀ ≤ R) (hRD : R ≤ D) :
    √((X + 4 * R ^ 2) * (Y + 4 * R ^ 2) * X * Y) / R ≤
      largeFactor X Y D D₀ := by
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hRpos : 0 < R := by linarith
  have hXY : 0 ≤ X * Y := by positivity
  have hw : 0 ≤ √(X * Y) := Real.sqrt_nonneg _
  have hXY0 : 0 < X * Y := by positivity
  -- split the square root of the product
  have hsplit : √((X + 4 * R ^ 2) * (Y + 4 * R ^ 2) * X * Y) =
      √(X + 4 * R ^ 2) * √(Y + 4 * R ^ 2) * √(X * Y) := by
    conv_lhs => rw [show (X + 4 * R ^ 2) * (Y + 4 * R ^ 2) * X * Y =
      (X + 4 * R ^ 2) * ((Y + 4 * R ^ 2) * (X * Y)) by ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    ring
  rw [hsplit]
  have hb1 : √(X + 4 * R ^ 2) ≤ √X + 2 * R := sqrt_add_four_sq_le hX0.le hRpos.le
  have hb2 : √(Y + 4 * R ^ 2) ≤ √Y + 2 * R := sqrt_add_four_sq_le hY0.le hRpos.le
  have hb10 : 0 ≤ √(X + 4 * R ^ 2) := Real.sqrt_nonneg _
  have hb20 : 0 ≤ √(Y + 4 * R ^ 2) := Real.sqrt_nonneg _
  have hR2 : 0 ≤ √X + 2 * R := by positivity
  have hstep : √(X + 4 * R ^ 2) * √(Y + 4 * R ^ 2) * √(X * Y) / R ≤
      (√X + 2 * R) * (√Y + 2 * R) * √(X * Y) / R := by
    gcongr
  refine hstep.trans ?_
  -- the expansion identity
  have hsqrtmul : √(X * Y) = √X * √Y := Real.sqrt_mul hX0.le Y
  have hexp : (√X + 2 * R) * (√Y + 2 * R) * √(X * Y) / R =
      X * Y / R + 2 * (√X + √Y) * √(X * Y) + 4 * R * √(X * Y) := by
    have hXu : √X * √X = X := by
      rw [← sq]; exact Real.sq_sqrt hX0.le
    have hYu : √Y * √Y = Y := by
      rw [← sq]; exact Real.sq_sqrt hY0.le
    rw [hsqrtmul]
    field_simp
    nlinarith [hXu, hYu]
  rw [hexp]
  have hA : X * Y / R ≤ X * Y / D₀ := by
    rw [div_le_div_iff₀ hRpos (by linarith : (0:ℝ) < D₀)]
    nlinarith [hXY]
  have hC : 4 * R * √(X * Y) ≤ 4 * D * √(X * Y) := by
    have h := mul_le_mul_of_nonneg_right (by linarith : 4 * R ≤ 4 * D) hw
    linarith
  have := largeFactor
  simp only [largeFactor]
  linarith


/-! ### Dyadic covering of the conductor range -/

/-- Every `r ≥ S ≥ 1` lies in the dyadic block `[S·2^k, S·2^(k+1))`. -/
private lemma dyadic_cover {S r : ℕ} (hS : 0 < S) (hr : S ≤ r) :
    S * 2 ^ Nat.log 2 (r / S) ≤ r ∧ r < S * 2 ^ (Nat.log 2 (r / S) + 1) := by
  set k := Nat.log 2 (r / S) with hk
  have hdiv : 0 < r / S := Nat.div_pos hr hS
  constructor
  · have h1 : 2 ^ k ≤ r / S := Nat.pow_log_le_self 2 (Nat.ne_of_gt hdiv)
    calc S * 2 ^ k ≤ S * (r / S) := Nat.mul_le_mul_left S h1
      _ = r / S * S := Nat.mul_comm _ _
      _ ≤ r := Nat.div_mul_le_self r S
  · have h1 : r / S < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) (r / S)
    have h2 : r / S + 1 ≤ 2 ^ (k + 1) := h1
    have hmod : r % S < S := Nat.mod_lt r hS
    have hdecomp : r = S * (r / S) + r % S := by
      exact (Nat.div_add_mod r S).symm
    calc r = S * (r / S) + r % S := hdecomp
      _ < S * (r / S) + S := by omega
      _ = S * (r / S + 1) := by ring
      _ ≤ S * 2 ^ (k + 1) := Nat.mul_le_mul_left S h2

/-- Membership in the block of size `S·2^k`. -/
private lemma mem_block_iff {S k r : ℕ} :
    r ∈ Decomp374a.blockModuli ((S * 2 ^ k : ℕ) : ℝ) ↔
      3 ≤ r ∧ S * 2 ^ k ≤ r ∧ r < S * 2 ^ (k + 1) := by
  have hceil : ⌈2 * ((S * 2 ^ k : ℕ) : ℝ)⌉₊ = S * 2 ^ (k + 1) := by
    have hcast : 2 * ((S * 2 ^ k : ℕ) : ℝ) = ((S * 2 ^ (k + 1) : ℕ) : ℝ) := by
      push_cast
      rw [pow_succ]
      ring
    rw [hcast, Nat.ceil_natCast]
  unfold Decomp374a.blockModuli
  rw [mem_filter, mem_Ico, hceil, Nat.cast_le]
  constructor
  · rintro ⟨⟨h3, hlt⟩, hle⟩
    exact ⟨h3, hle, hlt⟩
  · rintro ⟨h3, hle, hlt⟩
    exact ⟨⟨h3, hlt⟩, hle⟩

/-- A finset of naturals whose elements satisfy `k + 1 < L` has at most `L` elements. -/
private lemma card_le_of_succ_lt (K : Finset ℕ) {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ k ∈ K, (k : ℝ) + 1 < L) : (K.card : ℝ) ≤ L := by
  by_cases hK : K = ∅
  · rw [hK]
    simpa using hL
  · obtain ⟨m, hm⟩ := Finset.nonempty_iff_ne_empty.mpr hK
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hL1 : 1 ≤ L := by
      have := h m hm
      linarith
    have hsub : K ⊆ Finset.range ⌈L - 1⌉₊ := by
      intro k hk
      rw [mem_range, Nat.lt_ceil]
      have := h k hk
      linarith
    have hcard : K.card ≤ ⌈L - 1⌉₊ := by
      have hle := Finset.card_le_card hsub
      simpa using hle
    have hlt' : ((⌈L - 1⌉₊ : ℕ) : ℝ) < L := by
      have h1 : ((⌈L - 1⌉₊ : ℕ) : ℝ) < (L - 1) + 1 := Nat.ceil_lt_add_one (by linarith)
      linarith
    calc (K.card : ℝ) ≤ ((⌈L - 1⌉₊ : ℕ) : ℝ) := by exact_mod_cast hcard
      _ ≤ L := hlt'.le

/-! ### The leaf -/

/-- LEAF. Journal pp. 1225 and 1226, dyadic counting from display 15 to display 16.
For one fixed cofactor sum the conductor blocks, with no outer cofactor sum.
The hypothesis supplies the two moment assembly separately. -/
theorem dyadic_conductor_slice (c : ℕ → ℂ) (X Y Z D D₀ : ℝ) (a : ℤ) (s : ℕ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hX : 25 ≤ X) (hY : 25 ≤ Y) (hZ : 25 ≤ Z)
    (hZY : Z < Y) (hD : 1 < D) (hDX : D < √(X * Y))
    (hD₀ : 1 < D₀) (hD₀D : D₀ ≤ D) (hbal : √(X * Y) / D ≤ D₀)
    (hblock : ∀ R : ℝ, 1 ≤ R →
      (∑ r ∈ Decomp374a.blockModuli R,
        (r.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s) ≤
        √((X + 4 * R ^ 2) * (Y + 4 * R ^ 2) * X * Y) / R) :
    (∑ r ∈ (conductors D a).filter (fun r : ℕ => D₀ < (r : ℝ)),
      (r.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s) ≤
      log D / log 2 * largeFactor X Y D D₀ := by
  classical
  -- the dyadic base point
  set S : ℕ := max 2 ⌈D₀⌉₊ with hSdef
  have hS2 : 2 ≤ S := le_max_left 2 ⌈D₀⌉₊
  have hS0 : 0 < S := by omega
  have hSceil : ⌈D₀⌉₊ ≤ S := le_max_right 2 ⌈D₀⌉₊
  have hSD₀ : D₀ ≤ (S : ℝ) := by
    have h1 : D₀ ≤ ((⌈D₀⌉₊ : ℕ) : ℝ) := Nat.le_ceil D₀
    have h2 : ((⌈D₀⌉₊ : ℕ) : ℝ) ≤ (S : ℝ) := by exact_mod_cast hSceil
    linarith
  set f : ℕ → ℝ := fun r => (r.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s with hfdef
  have hf0 : ∀ r, 0 ≤ f r := by
    intro r
    have : f r = (r.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s := rfl
    rw [this]
    refine mul_nonneg (by positivity) ?_
    unfold primitiveTerm
    exact Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  set T : Finset ℕ := (conductors D a).filter (fun r : ℕ => D₀ < (r : ℝ)) with hTdef
  -- facts about the conductor range
  have hTmem : ∀ r ∈ T, 3 ≤ r ∧ D₀ < (r : ℝ) ∧ (r : ℝ) < D := by
    intro r hr
    have hr' : r ∈ (conductors D a).filter (fun r : ℕ => D₀ < (r : ℝ)) := hr
    obtain ⟨hrc, hrD⟩ := mem_filter.mp hr'
    obtain ⟨hIco, -, -⟩ := mem_filter.mp hrc
    exact ⟨(mem_Ico.mp hIco).1, hrD, Nat.lt_ceil.mp (mem_Ico.mp hIco).2⟩
  have hTS : ∀ r ∈ T, S ≤ r := by
    intro r hr
    have h2r : 2 ≤ r := le_trans (by norm_num) (hTmem r hr).1
    have hcr : ⌈D₀⌉₊ ≤ r := Nat.ceil_le.mpr (le_of_lt (hTmem r hr).2.1)
    exact max_le h2r hcr
  set KS : Finset ℕ := T.image (fun r => Nat.log 2 (r / S)) with hKSdef
  set BR : ℕ → Finset ℕ := fun k => Decomp374a.blockModuli ((S * 2 ^ k : ℕ) : ℝ) with hBRdef
  -- the blocks cover the conductor range
  have hcover : T ⊆ KS.biUnion BR := by
    intro r hr
    obtain ⟨h1, h2⟩ := dyadic_cover hS0 (hTS r hr)
    refine mem_biUnion.mpr ⟨Nat.log 2 (r / S), ?_, ?_⟩
    · exact mem_image.mpr ⟨r, hr, rfl⟩
    · exact (mem_block_iff (S := S) (k := Nat.log 2 (r / S)) (r := r)).mpr
        ⟨(hTmem r hr).1, h1, h2⟩
  -- blocks with different indices are disjoint
  have hdisj : (↑KS : Set ℕ).PairwiseDisjoint BR := by
    intro k hk l hl hkl
    rcases lt_or_gt_of_ne hkl with hlt | hlt
    · apply Finset.disjoint_left.mpr
      intro x hx1 hx2
      have h1 := (mem_block_iff.mp hx1).2.2
      have h2 := (mem_block_iff.mp hx2).2.1
      have hp : S * 2 ^ (k + 1) ≤ S * 2 ^ l :=
        Nat.mul_le_mul_left S (Nat.pow_le_pow_right (by norm_num) (by omega))
      omega
    · refine Finset.disjoint_left.mpr ?_
      intro x hx1 hx2
      have h1 := (mem_block_iff.mp hx2).2.2
      have h2 := (mem_block_iff.mp hx1).2.1
      have hp : S * 2 ^ (l + 1) ≤ S * 2 ^ k :=
        Nat.mul_le_mul_left S (Nat.pow_le_pow_right (by norm_num) (by omega))
      omega
  -- each block is bounded by `largeFactor`
  have hblockb : ∀ k ∈ KS, ∑ r ∈ BR k, f r ≤ largeFactor X Y D D₀ := by
    intro k hk
    obtain ⟨r, hrT, hrk⟩ := mem_image.mp hk
    obtain ⟨hr3, hrD₀, hrD⟩ := hTmem r hrT
    have hrS : S ≤ r := hTS r hrT
    have h1 : S * 2 ^ k ≤ r := by
      rw [← hrk]
      exact (dyadic_cover hS0 hrS).1
    have h2 : r < S * 2 ^ (k + 1) := by
      rw [← hrk]
      exact (dyadic_cover hS0 hrS).2
    have hR0 : D₀ ≤ ((S * 2 ^ k : ℕ) : ℝ) := by
      have hle1 : (S : ℝ) ≤ ((S * 2 ^ k : ℕ) : ℝ) := by
        have hpk : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
        have hmul : S * 1 ≤ S * 2 ^ k := Nat.mul_le_mul_left S hpk
        have hc : ((S * 1 : ℕ) : ℝ) ≤ ((S * 2 ^ k : ℕ) : ℝ) := by exact_mod_cast hmul
        simpa using hc
      linarith
    have hRr : ((S * 2 ^ k : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast h1
    have hRD : ((S * 2 ^ k : ℕ) : ℝ) ≤ D := by linarith
    have hR1 : 1 ≤ ((S * 2 ^ k : ℕ) : ℝ) := by linarith
    calc ∑ x ∈ BR k, f x
        = ∑ x ∈ Decomp374a.blockModuli ((S * 2 ^ k : ℕ) : ℝ),
            (x.totient : ℝ)⁻¹ * primitiveTerm c X Y Z x s := rfl
      _ ≤ √((X + 4 * ((S * 2 ^ k : ℕ) : ℝ) ^ 2) *
            (Y + 4 * ((S * 2 ^ k : ℕ) : ℝ) ^ 2) * X * Y) /
            ((S * 2 ^ k : ℕ) : ℝ) := hblock _ hR1
      _ ≤ largeFactor X Y D D₀ :=
          block_bound_le_largeFactor hX hY hD₀ hD₀D hR0 hRD
  have hKfac : 0 ≤ largeFactor X Y D D₀ := by
    have hXp : (0 : ℝ) < √(X * Y) := Real.sqrt_pos.mpr (by nlinarith)
    have h4 : 0 ≤ 4 * D * √(X * Y) := by positivity
    have h2 : 0 ≤ 2 * (√X + √Y) * √(X * Y) := by positivity
    have h3 : 0 ≤ X * Y / D₀ := by positivity
    simp only [largeFactor]
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLD : 0 ≤ Real.log D / Real.log 2 := by
    have := Real.log_pos hD
    positivity
  have hcard : ∀ k ∈ KS, (k : ℝ) + 1 < Real.log D / Real.log 2 := by
    intro k hk
    obtain ⟨r, hrT, hrk⟩ := mem_image.mp hk
    obtain ⟨hr3, hrD₀, hrD⟩ := hTmem r hrT
    have hrS : S ≤ r := hTS r hrT
    have h1 : S * 2 ^ k ≤ r := by
      rw [← hrk]
      exact (dyadic_cover hS0 hrS).1
    have h2N : 2 ^ (k + 1) ≤ r := by
      calc 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
        _ ≤ S * 2 ^ k := Nat.mul_le_mul_right (2 ^ k) hS2
        _ ≤ r := h1
    have h2 : ((2 : ℝ) ^ (k + 1)) ≤ (r : ℝ) := by exact_mod_cast h2N
    have h3 : ((2 : ℝ) ^ (k + 1)) < D := lt_of_le_of_lt h2 hrD
    have h4 := Real.log_lt_log (by positivity) h3
    rw [Real.log_pow] at h4
    rw [lt_div_iff₀ hlog2]
    push_cast at h4 ⊢
    linarith
  calc ∑ r ∈ T, f r
      ≤ ∑ r ∈ KS.biUnion BR, f r :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover (fun r _ _ => hf0 r)
    _ = ∑ k ∈ KS, ∑ r ∈ BR k, f r := Finset.sum_biUnion hdisj
    _ ≤ ∑ k ∈ KS, largeFactor X Y D D₀ := Finset.sum_le_sum hblockb
    _ = (KS.card : ℝ) * largeFactor X Y D D₀ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Real.log D / Real.log 2) * largeFactor X Y D D₀ :=
        mul_le_mul_of_nonneg_right (card_le_of_succ_lt KS hLD hcard) hKfac


/-- Enlarge a cofactor range to the full squarefree support, journal display 16. -/
theorem cofactor_subset (D : ℝ) (a : ℤ) (r : ℕ) (hD : 0 ≤ D) (hr : 1 ≤ r) :
    moduli (D / r) a ⊆ moduli D a := by
  intro s hs
  obtain ⟨hsI, hsQ⟩ := mem_filter.mp hs
  obtain ⟨hs1, hsU⟩ := mem_Ico.mp hsI
  apply mem_filter.mpr
  refine ⟨mem_Ico.mpr ⟨hs1, ?_⟩, hsQ⟩
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hslt : (s : ℝ) < D / r := Nat.lt_ceil.mp hsU
  exact Nat.lt_ceil.mpr (hslt.trans_le (div_le_self hD hrR))

/-- The outer squarefree cofactor weight is the existing Lemma 5 input, display 16.
CONDITIONAL ON PublishedInputs232.lemma5_phi. -/
theorem cofactor_totient_sum (D : ℝ) (a : ℤ) (hD : 1 < D) :
    (∑ s ∈ moduli D a, (s.totient : ℝ)⁻¹) ≤ Mphi D * log D := by
  have hsub : moduli D a ⊆ (Icc 1 ⌊D⌋₊).filter (fun s => Squarefree s) := by
    intro s hs
    obtain ⟨hsI, hsQ⟩ := mem_filter.mp hs
    obtain ⟨hs1, hsU⟩ := mem_Ico.mp hsI
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hs1, Nat.le_floor (Nat.lt_ceil.mp hsU).le⟩, hsQ.1⟩
  have h := sum_le_sum_of_subset_of_nonneg hsub
    (fun s _ _ => by positivity : ∀ s ∈ (Icc 1 ⌊D⌋₊).filter (fun s => Squarefree s),
      s ∉ moduli D a → 0 ≤ (s.totient : ℝ)⁻¹)
  exact h.trans (by simpa only [one_div] using PublishedInputs232.lemma5_phi D hD)

/-- Exact statement of Decomp148c.large_conductors with the outer sum proved.
CONDITIONAL ON the dyadic conductor slice, the two moments and the existing Lemma 5 input. -/
theorem large_conductors (c : ℕ → ℂ) (X Y Z D D₀ : ℝ) (a : ℤ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hX : 25 ≤ X) (hY : 25 ≤ Y) (hZ : 25 ≤ Z)
    (hZY : Z < Y) (hD : 1 < D) (hDX : D < √(X * Y))
    (hD₀ : 1 < D₀) (hD₀D : D₀ ≤ D) (hbal : √(X * Y) / D ≤ D₀) (ha : Even a) :
    largeMass c X Y Z D D₀ a ≤ largeBound X Y D D₀ := by
  let T := (conductors D a).filter (fun r : ℕ => D₀ < (r : ℝ))
  let K := log D / log 2 * largeFactor X Y D D₀
  have hK : 0 ≤ K := by
    have hlog := (log_pos hD).le
    dsimp [K, largeFactor]
    positivity
  have hp (r s : ℕ) : 0 ≤ primitiveTerm c X Y Z r s := by
    unfold primitiveTerm
    exact sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hinner (r : ℕ) (hr : r ∈ T) :
      (∑ s ∈ moduli (D / r) a, (s.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s) ≤
      ∑ s ∈ moduli D a, (s.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s := by
    have hr3 : 3 ≤ r := (mem_Ico.mp (mem_filter.mp (mem_filter.mp hr).1).1).1
    exact sum_le_sum_of_subset_of_nonneg (cofactor_subset D a r (by linarith) (by omega))
      (fun s _ _ => mul_nonneg (by positivity) (hp r s))
  have hslices (s : ℕ) : (∑ r ∈ T,
      (r.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s) ≤ K := by
    apply dyadic_conductor_slice c X Y Z D D₀ a s hc hX hY hZ hZY hD hDX hD₀ hD₀D hbal
    intro R hR
    exact Decomp374a.dyadic_block c X Y Z R s hc hX hY hZ hZY hR
  calc
    largeMass c X Y Z D D₀ a ≤ ∑ r ∈ T, (r.totient : ℝ)⁻¹ *
        ∑ s ∈ moduli D a, (s.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s := by
      exact sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left (hinner r hr) (by positivity))
    _ = ∑ s ∈ moduli D a, (s.totient : ℝ)⁻¹ *
        ∑ r ∈ T, (r.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro s hs
      apply sum_congr rfl
      intro r hr
      ring
    _ ≤ ∑ s ∈ moduli D a, (s.totient : ℝ)⁻¹ * K :=
      sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hslices s) (by positivity))
    _ = (∑ s ∈ moduli D a, (s.totient : ℝ)⁻¹) * K := by rw [sum_mul]
    _ ≤ (Mphi D * log D) * K :=
      mul_le_mul_of_nonneg_right (cofactor_totient_sum D a hD) hK
    _ = largeBound X Y D D₀ := by dsimp [K, largeFactor, largeBound]; ring

end
end LeanLab.BS2022GRH.Decomp374f

#print axioms LeanLab.BS2022GRH.Decomp374f.dyadic_conductor_slice
#print axioms LeanLab.BS2022GRH.Decomp374f.cofactor_subset
#print axioms LeanLab.BS2022GRH.Decomp374f.cofactor_totient_sum
#print axioms LeanLab.BS2022GRH.Decomp374f.large_conductors
