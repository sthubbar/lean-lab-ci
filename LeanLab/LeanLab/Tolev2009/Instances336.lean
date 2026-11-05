/-
AI wrote this Lean code. Codex task336.
Binary Goldbach is open.
Source context: Tolev 2009 page 3 major and minor arcs and page 4 display 12.
These are nonvacuity instances for the proved Type I supply.
-/
import LeanLab.Tolev2009.Decomp336c

open Finset Real Filter

namespace LeanLab.Tolev2009.Instances336

open LeanLab.Tolev2009.Faithful LeanLab.Tolev2009.Dyadic
open LeanLab.Tolev2009.Decomp310a LeanLab.Tolev2009.Decomp286b
open LeanLab.Tolev2009.Displays14to16

/-- A concrete rational point outside every major arc in the shifted interval. -/
theorem rational_minor_point (Q τ : ℝ) (hQ : 1 ≤ Q) (hτ : Q+2 ≤ τ) :
    let q := ⌊Q⌋₊+1
    (1/(q : ℝ)) ∈ Set.Ioo (-1/τ) (1-1/τ) ∧
      (1/(q : ℝ)) ∉ majorArcs Q τ := by
  dsimp only
  let q := ⌊Q⌋₊+1
  change (1/(q : ℝ)) ∈ Set.Ioo (-1/τ) (1-1/τ) ∧ (1/(q : ℝ)) ∉ majorArcs Q τ
  have hq : (2 : ℕ) ≤ q := by
    have hh : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by simpa using hQ)
    dsimp [q]
    omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have ht0 : 0 < τ := by linarith
  have hqt : (q : ℝ) < τ := by
    have hh := Nat.floor_le (by linarith : 0 ≤ Q)
    dsimp [q]
    push_cast
    linarith
  have hinv : 1/τ < 1/(q : ℝ) := one_div_lt_one_div_of_lt hq0 hqt
  have hhalf : 1/(q : ℝ) ≤ 1/2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    exact_mod_cast hq
  constructor
  · constructor
    · have hh : 0 < 1/(q : ℝ) := by positivity
      exact (div_neg_of_neg_of_pos (by norm_num : (-1:ℝ)<0) ht0).trans hh
    · linarith
  · intro hh
    simp only [majorArcs, Set.mem_iUnion] at hh
    obtain ⟨k, hk, a, ha, hlo, hhi⟩ := hh
    have hk' := mem_Icc.mp hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hkq : (k : ℝ) + 1 ≤ q := by
      dsimp [q]
      exact_mod_cast (by omega : k+1 ≤ ⌊Q⌋₊+1)
    have hsum : (k : ℝ)/q + 1/τ < 1 := by
      have hh : (k : ℝ)/q + 1/q ≤ 1 := by
        rw [← add_div, div_le_one hq0]
        exact hkq
      linarith
    by_cases ha0 : a = 0
    · subst a
      simp only [Nat.cast_zero, zero_div, zero_add] at hhi
      have hi : (k : ℝ) / q ≤ 1/τ := by
        have hh := mul_le_mul_of_nonneg_left hhi hk0.le
        convert hh using 1 <;> field_simp <;> ring
      have hloinv : 1/(q : ℝ) ≤ (k : ℝ)/q := div_le_div_of_nonneg_right
        (by exact_mod_cast hk'.1) hq0.le
      linarith
    · have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
      have hi : (a : ℝ) ≤ (k : ℝ)/q + 1/τ := by
        have hh := mul_le_mul_of_nonneg_left hlo hk0.le
        have heq : (k : ℝ) * ((a : ℝ)/k - 1/((k : ℝ)*τ)) = a-1/τ := by field_simp
        rw [heq] at hh
        have heq2 : (k : ℝ) * (1/(q : ℝ)) = (k : ℝ)/q := by ring
        rw [heq2] at hh
        linarith
      linarith
/-- The arc and positive cutoff hypotheses hold together for all sufficiently large N. -/
theorem eventual_nonvacuity_parameters (A : ℝ) (hA : 0 ≤ A) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      2 ≤ Real.log N ∧ Qof A N + 2 ≤ τof A N ∧ 1 ≤ cutoff3 (10000*A) N := by
  have he := (isLittleO_log_rpow_rpow_atTop (30000*A) (by norm_num : (0:ℝ)<1)).bound
    (by norm_num : (0:ℝ)<1/8)
  obtain ⟨X₀,hX⟩ := eventually_atTop.mp he
  refine ⟨max X₀ (Real.exp 2),?_⟩
  intro N hN
  have hNe : Real.exp 2 ≤ N := (le_max_right _ _).trans hN
  have hNp : (0:ℝ)<N := (Real.exp_pos 2).trans_le hNe
  have hL : 2 ≤ Real.log N := (Real.le_log_iff_exp_le hNp).mpr hNe
  have hLp : 0 < Real.log N := by linarith
  have hQ : 1 ≤ Qof A N := by
    unfold Qof
    exact Real.one_le_rpow (by linarith) (by positivity)
  have hQp : 0 < Qof A N := by linarith
  have hb := hX (N:ℝ) ((le_max_left _ _).trans hN)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,Real.rpow_one,
    abs_of_nonneg (Real.rpow_nonneg hLp.le _),abs_of_pos hNp] at hb
  have hbig : 8 * Real.log N ^ (30000*A) ≤ N := by linarith
  have hQsq : Qof A N ^ 2 ≤ Real.log N ^ (30000*A) := by
    rw [Qof,←Real.rpow_natCast,←Real.rpow_mul hLp.le]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    norm_num
    nlinarith
  have ht : Qof A N+2 ≤ τof A N := by
    unfold τof
    apply (le_div_iff₀ hQp).mpr
    nlinarith
  have hLN : Real.log N ^ (30000*A) ≤ N := by
    have hh := Real.rpow_nonneg hLp.le (30000*A)
    linarith
  have hc : Real.log N ^ (10000*A) ≤ (N:ℝ)^((1:ℝ)/3) := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hLp.le _) hLN (by norm_num : (0:ℝ)≤1/3)
    rw [←Real.rpow_mul hLp.le] at hh
    convert hh using 1 <;> congr 1 <;> ring
  have hprod : 1 ≤ (N:ℝ)^((1:ℝ)/3) * Real.log N ^ (-(10000*A)) := by
    calc
      1 = Real.log N ^ (10000*A) * Real.log N ^ (-(10000*A)) := by
        rw [←Real.rpow_add hLp]
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hLp.le _)
  refine ⟨hL,ht,?_⟩
  unfold cutoff3
  exact Nat.le_floor (by simpa using hprod)
/-- The full analytic hypotheses have arbitrarily large odd instances.
The point is one over floor Q plus one and the third cutoff is positive. -/
theorem minor_arc_instances (A : ℝ) (hA : 10000 ≤ A) (T : ℝ) :
    ∃ N : ℕ, Odd N ∧ T ≤ N ∧ 2 ≤ Real.log N ∧
      1 ≤ cutoff3 (10000*A) N ∧
      ∃ α ∈ Set.Ioo (-1/τof A N) (1-1/τof A N),
        α ∉ majorArcs (Qof A N) (τof A N) := by
  obtain ⟨N₀,hN₀⟩ := eventual_nonvacuity_parameters A (by linarith)
  obtain ⟨n,hn⟩ := exists_nat_gt (max N₀ T)
  let N := 2*n+1
  have hnn : (n : ℝ) ≤ N := by exact_mod_cast (show n ≤ N by dsimp [N]; omega)
  have hN0 : N₀ ≤ N := ((le_max_left _ _).trans hn.le).trans hnn
  have hNT : T ≤ N := ((le_max_right _ _).trans hn.le).trans hnn
  obtain ⟨hL,hτ,hK⟩ := hN₀ N hN0
  have hQ : 1 ≤ Qof A N := by
    unfold Qof
    exact Real.one_le_rpow (by linarith) (by linarith)
  have hm := rational_minor_point (Qof A N) (τof A N) hQ hτ
  refine ⟨N,?_,hNT,hL,hK,1/((⌊Qof A N⌋₊+1 : ℕ):ℝ),hm.1,hm.2⟩
  exact ⟨n,by dsimp [N]⟩

/-- The nonzero indicator weight is one at every frequency for a positive cutoff. -/
theorem unit_weight_eq_one (N K : ℕ) (hK : 1 ≤ K) :
    LeanLab.Tolev2009.L2Bound.weight (fun k => if k=1 then 1 else 0) 1 K N = 1 := by
  classical
  unfold LeanLab.Tolev2009.L2Bound.weight
  rw [sum_eq_single 1]
  · simp
  · intro k hk hne
    simp [hne]
  · intro hnot
    exfalso
    apply hnot
    simp [hK, Nat.mod_one]

/-- A one frequency row keeps every product cutoff and has a nonzero phase. -/
theorem terminal_rows (N K : ℕ) (hN : 2 ≤ N) (hK : 1 ≤ K) (α : ℝ) :
    row (fun k => if k=1 then 1 else 0) 1 K N α (N-1 : ℕ) (N-1 : ℕ) N (fun _ => 1) 1 =
      ee (α*N) ∧
    row (fun k => if k=1 then 1 else 0) 1 K N α (N-1 : ℕ) (N-1 : ℕ) N (fun l : ℕ => (Real.log l : ℂ)) 1 =
      (Real.log N : ℂ) * ee (α*N) := by
  have hs : Ioc (N-1) N = {N} := by
    ext n
    simp only [mem_Ioc,mem_singleton]
    omega
  have hx : ((N-1 : ℕ) : ℝ) < N := by exact_mod_cast (show N-1 < N by omega)
  have hhi : (N : ℝ) ≤ 2*((N-1 : ℕ):ℝ) := by exact_mod_cast (show N ≤ 2*(N-1) by omega)
  simp only [row,Nat.floor_natCast,hs,sum_singleton,one_mul,hx,hhi,le_refl,and_self,
    ite_true,unit_weight_eq_one N K hK,Complex.ofReal_one,mul_one]

/-- The constant and logarithmic row majorants equal log N and log N squared. -/
theorem terminal_majorants (N K : ℕ) (hN : 2 ≤ N) (hK : 1 ≤ K) (α : ℝ) :
    (∑ m ∈ Ioc ⌊(1/2 : ℝ)⌋₊ ⌊(1:ℝ)⌋₊, ((tau5 m : ℝ)*Real.log N) *
      ‖row (fun k => if k=1 then 1 else 0) 1 K N α (N-1 : ℕ) (N-1 : ℕ) N (fun _ => 1) m‖) = Real.log N ∧
    (∑ m ∈ Ioc ⌊(1/2 : ℝ)⌋₊ ⌊(1:ℝ)⌋₊, ((tau5 m : ℝ)*Real.log N) *
      ‖row (fun k => if k=1 then 1 else 0) 1 K N α (N-1 : ℕ) (N-1 : ℕ) N
        (fun l : ℕ => (Real.log l : ℂ)) m‖) = Real.log N ^ 2 := by
  obtain ⟨h₁,h₂⟩ := terminal_rows N K hN hK α
  norm_num only [show ⌊(1/2:ℝ)⌋₊ = 0 by norm_num,show ⌊(1:ℝ)⌋₊=1 by norm_num,
    show Ioc 0 1 = {1} by decide,sum_singleton,tau5_one,Nat.cast_one,one_mul]
  rw [h₁,h₂,norm_ee,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.log_natCast_nonneg _),norm_ee]
  constructor <;> ring
/-- Both row targets have nonzero instances under all analytic shell hypotheses. -/
theorem nonzero_row_instances (A : ℝ) (hA : 10000 ≤ A) (T : ℝ) :
    ∃ (N : ℕ) (α : ℝ), Odd N ∧ T ≤ N ∧
      α ∈ Set.Ioo (-1/τof A N) (1-1/τof A N) ∧ α ∉ majorArcs (Qof A N) (τof A N) ∧
      let K := cutoff3 (10000*A) N
      let x : ℝ := (N-1 : ℕ)
      1 ≤ K ∧ (N:ℝ)*Real.log N^(-4*A) ≤ x ∧ x ≤ N ∧ 2 < x ∧ N ≤ 2*x ∧
      x/4 ≤ (1/2:ℝ)*x ∧ (1/2:ℝ)*x ≤ 2*x ∧ x^((249:ℝ)/500) ≤ x ∧
      (∑ m ∈ Ioc ⌊(1/2:ℝ)⌋₊ ⌊(1:ℝ)⌋₊, ((tau5 m:ℝ)*Real.log N)*
        ‖row (fun k => if k=1 then 1 else 0) 1 K N α x x N (fun _ => 1) m‖) = Real.log N ∧
      (∑ m ∈ Ioc ⌊(1/2:ℝ)⌋₊ ⌊(1:ℝ)⌋₊, ((tau5 m:ℝ)*Real.log N)*
        ‖row (fun k => if k=1 then 1 else 0) 1 K N α x x N (fun l:ℕ => (Real.log l:ℂ)) m‖) = Real.log N^2 ∧
      0 < Real.log N := by
  obtain ⟨N,hodd,hNT,hL,hK,α,hα,hminor⟩ := minor_arc_instances A hA (max T 4)
  have hN4r : (4:ℝ) ≤ N := (le_max_right _ _).trans hNT
  have hN4 : 4 ≤ N := by exact_mod_cast hN4r
  have hN2 : 2 ≤ N := by omega
  have hNp : (0:ℝ) < N := by linarith
  have hLp : 0 < Real.log N := by linarith
  let x : ℝ := (N-1:ℕ)
  have hNx : (N:ℝ) = x+1 := by
    dsimp [x]
    exact_mod_cast (show N = (N-1)+1 by omega)
  have hx : 2 < x := by linarith
  have hxN : x ≤ N := by linarith
  have hH₁ : (N:ℝ) ≤ 2*x := by linarith
  have hinv : Real.log N^(-4*A) ≤ (1:ℝ)/2 := by
    calc
      _ ≤ Real.log N^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ (2:ℝ)^(-1:ℝ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hL (by norm_num)
      _ = _ := by norm_num
  have hxlo : (N:ℝ)*Real.log N^(-4*A) ≤ x := by
    have hh := mul_le_mul_of_nonneg_left hinv hNp.le
    linarith
  have hsize : x^((249:ℝ)/500) ≤ x := by
    calc
      _ ≤ x^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = x := Real.rpow_one _
  obtain ⟨h₁,h₂⟩ := terminal_majorants N (cutoff3 (10000*A) N) hN2 hK α
  refine ⟨N,α,hodd,(le_max_left _ _).trans hNT,hα,hminor,?_⟩
  dsimp only
  change 1 ≤ cutoff3 (10000*A) N ∧ (N:ℝ)*Real.log N^(-4*A) ≤ x ∧ x ≤ N ∧
    2 < x ∧ N ≤ 2*x ∧ x/4 ≤ (1/2:ℝ)*x ∧ (1/2:ℝ)*x ≤ 2*x ∧ x^((249:ℝ)/500) ≤ x ∧ _
  exact ⟨hK,hxlo,hxN,hx,hH₁,by linarith,by linarith,hsize,h₁,h₂,hLp⟩
/-- A Fourier shift of a minor arc point can be the integer frequency one.
This records why pointwise minor arc estimates cannot be applied to every residue shift. -/
theorem minor_shift_resonance (Q τ : ℝ) (hQ : 1 ≤ Q) (hτ : Q+2 ≤ τ) :
    let q := ⌊Q⌋₊+1
    (1/(q:ℝ)) ∈ Set.Ioo (-1/τ) (1-1/τ) ∧
    (1/(q:ℝ)) ∉ majorArcs Q τ ∧ 1/(q:ℝ) + ((q-1:ℕ):ℝ)/q = 1 := by
  dsimp only
  have hh := rational_minor_point Q τ hQ hτ
  refine ⟨hh.1,hh.2,?_⟩
  have hq : 1 ≤ ⌊Q⌋₊+1 := by omega
  have hq0 : ((⌊Q⌋₊+1:ℕ):ℝ) ≠ 0 := by positivity
  rw [Nat.cast_sub hq]
  push_cast
  field_simp
  <;> ring

/-- An arbitrary second coefficient can cancel the phase in a single row.
All product cutoffs are retained. The Type I coefficient restriction is essential. -/
theorem row_cancelled_phase (lam : ℕ → ℝ) (l₃ K N m : ℕ) (α x H H₁ : ℝ) :
    row lam l₃ K N α x H H₁ (fun l => ee (-(α*(m*l:ℕ)))) m =
      ∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊,
        if x < (m*l:ℕ) ∧ (m*l:ℕ) ≤ 2*x ∧ m*l ≤ N then
          (LeanLab.Tolev2009.L2Bound.weight lam l₃ K (m*l):ℂ) else 0 := by
  unfold row
  apply sum_congr rfl
  intro l hl
  split_ifs
  · rw [←ee_add,neg_add_cancel,ee_zero,one_mul]
  · rfl

end LeanLab.Tolev2009.Instances336
