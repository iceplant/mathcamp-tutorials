import data.nat.basic 
import data.int.parity
import tactic

open int

-- inductive even : ℕ → Prop
-- | even_zero : even 0
-- | even_ss : ∀ {n}, even n → even (n + 2)

-- def even (n : ℕ) : Prop := ∃ (k:ℕ), n = 2*k

-- def odd (n : ℕ) : Prop := ¬ (even n)

-- lemma even_or_odd (n : ℕ) : even n ∨ odd n := 
-- begin 
--     exact classical.em (even n),
-- end 

-- lemma odd_imp_even_plus_one (n : ℕ) : odd n → ∃ k, 2*k + 1 = n := 
-- begin 
--     intro h',
--     by_cases (2 ∣ n),
--         exfalso,
--         apply h',
--         exact h,



-- end




#eval gcd 1 2 
#eval gcd 10 15



-- lemma square_even_imp_even {a : ℤ} : even (a^2) → even a := 
-- begin 
-- -- rintro ⟨k, h⟩,
-- -- unfold even,
-- -- suggest,

-- unfold even,
-- contrapose,
-- push_neg,
-- intros h1 k h2,
-- specialize h1 (k/a),


-- sorry,
-- end 

--lifted from tutorial project 
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

def rational (n : ℤ) : Prop := ∃ a b : ℤ, (rel_prime a b ∧ a^2 = 2*b^2)

theorem root_two_not_rational : ¬ rational 2 :=
begin 
    rintros ⟨a, b, a_b_rel_prime, h⟩,
    unfold rel_prime at a_b_rel_prime,
    have a_squared_even : even (a^2),
        rw h,
        use b^2,
    have a_even : even a, exact square_even_iff_even a_squared_even,
    cases a_even with c a_even,
    rw a_even at h,
    have b_squared_even : even (b^2),
        sorry,
    have b_even : even b, 
        exact square_even_imp_even b_squared_even,
    apply a_b_rel_prime,
    use 2,
    split,
    use c,
    exact a_even,
    split,
    rcases b_even with ⟨b_2, b_even⟩,
    use b_2,
    exact b_even,
    linarith,
end