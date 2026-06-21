import Mathlib

open scoped BigOperators Topology

/-- `e` defined as the series `∑ 1/n!`. -/
noncomputable def e : ℝ := ∑' n : ℕ, 1 / n.factorial

/-- The series `∑ 1/n!` is summable (it is the exponential series at `x = 1`). -/
lemma is_summable : Summable (fun n : ℕ ↦ (1 : ℝ) / n.factorial) := by
  simpa using Real.summable_pow_div_factorial (1 : ℝ)

-- Split the series at index `s`: the first `s` terms plus the tail starting at `s`. -/
lemma split_sum (s : ℕ) :
    ∑' n : ℕ, (1 : ℝ) / n.factorial
      = (∑ n ∈ Finset.range s, (1 : ℝ) / n.factorial)
        + ∑' n : ℕ, (1 : ℝ) / (n + s).factorial :=
  (is_summable.sum_add_tsum_nat_add s).symm

/-- `s! * (r/s - ∑_{n ≤ s} 1/n!)` is an integer.
Every term `s!/n!` for `n ≤ s` is a natural number, and `s! * (r/s) = r * (s-1)!`. -/
lemma A_times_s_factorial_integer (r : ℤ) (s : ℕ) (hs : 0 < s) :
    ∃ z : ℤ,
      (s.factorial : ℝ)
        * ((r : ℝ) / s - ∑ n ∈ Finset.range (s + 1), (1 : ℝ) / n.factorial) = z := by
  use r * (s - 1).factorial - (∑ n ∈ Finset.range (s + 1), s.factorial / n.factorial : ℕ)
  push_cast
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · have h_s : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    rw [← Nat.mul_factorial_pred hs.ne']
    push_cast
    calc (s : ℝ) * (s - 1).factorial * (r / s)
        = r * (s - 1).factorial * (s / s) := by ring
      _ = r * (s - 1).factorial := by rw [div_self h_s, mul_one]
  · refine Finset.sum_congr rfl fun n hn ↦ ?_
    rw [Finset.mem_range] at hn
    have hns : n ≤ s := by omega
    have hn0 : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
    rw [mul_one_div]
    exact (Nat.cast_div (Nat.factorial_dvd_factorial hns) hn0).symm

/-- The scaled tail `s! * ∑_{n ≥ s+1} 1/n!` is strictly positive. -/
lemma tail_pos (s : ℕ) :
    (s.factorial : ℝ) * ∑' n : ℕ, (1 : ℝ) / (n + (s + 1)).factorial > 0 := by
  -- The tail is summable: it is `1/n!` reindexed by `n ↦ n + (s + 1)`.
  have hsum : Summable fun n : ℕ ↦ (1 : ℝ) / (n + (s + 1)).factorial := by
    simpa using (summable_nat_add_iff (s + 1)).mpr is_summable
  -- Every term is strictly positive.
  have hpos : ∀ n : ℕ, (0 : ℝ) < (1 : ℝ) / (n + (s + 1)).factorial := fun n ↦
    div_pos one_pos (by exact_mod_cast Nat.factorial_pos (n + (s + 1)))
  have htsum : 0 < ∑' n : ℕ, (1 : ℝ) / (n + (s + 1)).factorial :=
    hsum.tsum_pos (fun n ↦ (hpos n).le) 0 (hpos 0)
  exact mul_pos (by exact_mod_cast Nat.factorial_pos s) htsum

/-- The scaled tail `s! * ∑_{n ≥ s+1} 1/n!` is strictly below `1`.

This is where splitting at `s + 1` (rather than `s`) is essential: the geometric bound
`s! * ∑_{n ≥ s+1} 1/n! = 1/(s+1) + 1/((s+1)(s+2)) + ... < ∑_{k ≥ 1} 1/(s+1)^k = 1/s ≤ 1`
only holds when the tail starts one term past `s`. -/
lemma tail_lt_one (s : ℕ) (hs : 0 < s) :
    (s.factorial : ℝ) * (∑' n : ℕ, (1 : ℝ) / (n + (s + 1)).factorial) < 1 := by

  -- Move s! inside the sum
  rw [← tsum_mul_left]

  -- Define our explicit sequences
  let u := fun n : ℕ ↦ (s.factorial : ℝ) * (1 / (n + (s + 1)).factorial)
  let v := fun n : ℕ ↦ (1 : ℝ) / (s + 1) * (1 / (s + 2)) ^ n

  have h_r_nonneg : 0 ≤ (1 : ℝ) / (s + 2) := by positivity
  have h_r_lt_one : (1 : ℝ) / (s + 2) < 1 := by
    rw [div_lt_one (by positivity)]
    have : (0 : ℝ) < s := by exact_mod_cast hs
    linarith

  -- Prove the term-by-term bound: u n ≤ v n
  have h_le : ∀ n, u n ≤ v n := by
    intro n
    -- 1. Integer bound: a direct instance of `Nat.factorial_mul_pow_le_factorial`.
    have h_int : (s + 1) * (s + 2) ^ n * s.factorial ≤ (n + (s + 1)).factorial :=
      calc (s + 1) * (s + 2) ^ n * s.factorial
          = (s + 1).factorial * (s + 1 + 1) ^ n := by rw [Nat.factorial_succ]; ring
        _ ≤ (s + 1 + n).factorial := Nat.factorial_mul_pow_le_factorial
        _ = (n + (s + 1)).factorial := by rw [Nat.add_comm (s + 1) n]

    -- 2. Cast down to reals and rearrange to match u n ≤ v n
    change (s.factorial : ℝ) * (1 / (n + (s + 1)).factorial) ≤ (1 : ℝ) / (s + 1) * (1 / (s + 2)) ^ n
    calc (s.factorial : ℝ) * (1 / (n + (s + 1)).factorial)
      _ = (s.factorial : ℝ) / (n + (s + 1)).factorial := mul_one_div _ _
      _ ≤ (1 : ℝ) / ((s + 1) * (s + 2) ^ n : ℝ) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        calc (s.factorial : ℝ) * ((s + 1) * (s + 2) ^ n : ℝ)
          _ = (((s + 1) * (s + 2) ^ n * s.factorial : ℕ) : ℝ) := by push_cast; ring
          _ ≤ ((n + (s + 1)).factorial : ℝ) := Nat.cast_le.mpr h_int
          _ = 1 * ((n + (s + 1)).factorial : ℝ) := by ring
      _ = (1 : ℝ) / (s + 1) * (1 / (s + 2)) ^ n := by
        rw [div_pow, one_pow, div_mul_div_comm, one_mul]

  -- Prove summability
  have h_v_sum : Summable v :=
    (summable_geometric_of_lt_one h_r_nonneg h_r_lt_one).mul_left _
  have h_u_sum : Summable u :=
    Summable.of_nonneg_of_le (fun n ↦ by positivity) h_le h_v_sum

  -- Evaluate the geometric sum explicitly
  have h_tsum_v : ∑' n, v n = (s + 2) / (s + 1) ^ 2 := by
    have hs2 : (s + 2 : ℝ) ≠ 0 := by positivity
    have hsub : (1 : ℝ) - 1 / (s + 2) = (s + 1) / (s + 2) := by
      rw [eq_div_iff hs2, sub_mul, one_mul, one_div_mul_cancel hs2]; ring
    change (∑' n : ℕ, (1 : ℝ) / (s + 1) * (1 / (s + 2)) ^ n) = (s + 2) / (s + 1) ^ 2
    rw [tsum_mul_left, tsum_geometric_of_lt_one h_r_nonneg h_r_lt_one, hsub, inv_div,
      div_mul_div_comm, one_mul, ← pow_two]

  -- Tie it all together: tsum u ≤ tsum v = (s + 2) / (s + 1)² < 1
  calc ∑' n, u n
    _ ≤ ∑' n, v n := Summable.tsum_le_tsum h_le h_u_sum h_v_sum
    _ = (s + 2) / (s + 1) ^ 2 := h_tsum_v
    _ < 1 := by
      rw [div_lt_one (by positivity)]
      have : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
      nlinarith

theorem e_irrational : Irrational e := by
  -- Suppose, for contradiction, that `e = q` for some rational `q = r/s`.
  rintro ⟨q, hq⟩
  have hs : 0 < q.den := q.pos
  have hre : e = (q.num : ℝ) / (q.den : ℝ) := by
    rw [← hq]; exact Rat.cast_def q

  -- The finite part scaled by `s!` is an integer `z`.
  obtain ⟨z, hz⟩ := A_times_s_factorial_integer q.num q.den hs

  -- The scaled tail equals that same integer `z`.
  have key :
      (q.den.factorial : ℝ) * (∑' n : ℕ, (1 : ℝ) / (n + (q.den + 1)).factorial) = (z : ℝ) := by
    rw [← hz]
    have he : e = (∑ n ∈ Finset.range (q.den + 1), (1 : ℝ) / n.factorial)
                    + ∑' n : ℕ, (1 : ℝ) / (n + (q.den + 1)).factorial :=
      split_sum (q.den + 1)
    rw [hre] at he
    have htail :
        (q.num : ℝ) / q.den - (∑ n ∈ Finset.range (q.den + 1), (1 : ℝ) / n.factorial)
          = ∑' n : ℕ, (1 : ℝ) / (n + (q.den + 1)).factorial := by
      rw [he]; ring
    rw [htail]

  -- But `0 < z < 1`, so `z` is an integer strictly between `0` and `1`: contradiction.
  have hlow : (0 : ℝ) < z := key ▸ tail_pos q.den
  have hup : (z : ℝ) < 1 := key ▸ tail_lt_one q.den hs
  have hz0 : (0 : ℤ) < z := by exact_mod_cast hlow
  have hz1 : z < 1 := by exact_mod_cast hup
  omega
