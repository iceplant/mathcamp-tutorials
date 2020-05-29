import data.nat.basic 
import data.int.parity
import tactic

open int

/-lifted from tutorial project. I think there's potential to explain and 
develop these lemmas and parity in detail, but it could make the tutorial pretty long-/
def odd (n : ℤ) : Prop := ∃ k, n = 2*k + 1

#check int.not_even_iff

theorem not_even_iff_odd (n : ℤ) : ¬ even n ↔ odd n := 
begin 
  rw int.not_even_iff,
  split ; intro h,
  use n/2,
  conv_rhs { rw add_comm, congr, rw ← h },
  exact (int.mod_add_div n 2).symm,
  rcases h with ⟨k, rfl⟩,
  simp [add_comm],
  refl,
end


theorem square_even_iff_even (n : ℤ) : even (n^2) ↔ even n :=
begin
  -- sorry
  split,
  { contrapose,
    rw not_even_iff_odd,
    rw not_even_iff_odd,
    rintro ⟨k, rfl⟩,
    use 2*k*(k+1),
    ring },
  { rintro ⟨k, rfl⟩,
    use 2*k^2,
    ring },
  -- sorry
end

def int_divides (a b : ℤ) : Prop := b % a = 0

def rel_prime (a b : ℤ) : Prop := 
    ¬ ∃ k:ℕ, (int_divides k a ∧ int_divides  k b ∧ k>1)

lemma even_imp_square_even (a : ℤ) : even a → even (a^2) := 
begin 
unfold even,
rintro ⟨k, h⟩,
use (2*k^2),
rw h,
ring,
end

def rational (n : ℤ) : Prop := ∃ a b : ℤ, (rel_prime a b ∧ a^2 = n*b^2)

--I feel like this exists in mathlib. I'm trying to find it.
lemma div_both_sides {a b k : ℤ} (h : k*a = k*b) (hk : k ≠ 0) : a = b := 
begin 
  sorry,
end

--this could probably be cleaner/broken into smaller steps
theorem root_two_not_rational : ¬ rational 2 :=
begin 
    rintros ⟨a, b, a_b_rel_prime, h⟩,
    unfold rel_prime at a_b_rel_prime,
    have a_squared_even : even (a^2),
        rw h,
        use b^2,
    have a_even : even a, 
        exact (square_even_iff_even a).mp a_squared_even,
    cases a_even with c a_even,
    rw a_even at h,
    have b_squared_even : even (b^2),
        unfold even,
        use c^2,
        rw mul_pow 2 c 2 at h,
        rw pow_succ at h,
        rw mul_assoc 2 (2^1) (c^2) at h,
        have h' := div_both_sides h (by linarith),
        simp at h',
        rw h',
    have b_even : even b, 
        exact (square_even_iff_even b).mp b_squared_even,
    apply a_b_rel_prime,
    use 2,
    split,
    unfold int_divides,
    rw a_even,
    simp,
    split,
    rcases b_even with ⟨b_2, b_even⟩,
    rw b_even,
    unfold int_divides,
    simp,
    linarith,
end





--me trying to find lemmas in mathlib
-- example (a b c : ℕ) (h : a*c = b*c) (h' : c ≠ 0) (h'' : a ≠ 0) (h''' : b ≠ 0)
--    : a = b := 
-- begin 
--   library_search,
--   sorry,
-- end 

example (a b c : ℕ) (h : a = b) : a*c = b*c :=
begin 
  exact congr_fun (congr_arg has_mul.mul h) c,
end

example (a b : ℕ) (h : 2*a = 2*b) : a = b := 
begin 
  refine eq.symm _,
  sorry,
end

example (a : ℕ) : (2*a)^2 = 2^2 * a^2 := 
begin 
  exact nat.mul_pow 2 a 2, 
end