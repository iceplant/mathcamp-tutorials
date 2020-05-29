import data.nat.basic 
import tactic 

--Problems taken from https://www.math.upenn.edu/~peal/files/Proof.by.Induction[2018][Eng]-ALEXANDERSSON.pdf

open nat

--explanation of how guards work and pattern matching. Maybe give more examples
def mysum (f : ℕ → ℕ) : ℕ → ℕ
| 0 := (f 0)
| (succ k) := (f (succ k)) + (mysum k)

def factorial : ℕ → ℕ 
| 0 := 1
| (succ n) := (succ n)*(factorial n)

--TODO: these but using finset instead for comparison. Maybe implement the stuff below using finset as well

--putting 2 on LHS because nat division is weird and I think it's best to 
--avoid it at this level. Could be a good example of "this thing you took 
--for granted in math hasn't been implemented yet so you have to find a 
--way to say the same thing without using it"
theorem sum_identity_1 (n : ℕ) : 2 * mysum id n = n*(n+1) := 
begin 
    induction n with k hk,
    {refl}, 
    {rw mysum,
    rw mul_add,
    rw hk,
    repeat {rw succ_eq_add_one},
    simp only [add_assoc, add_zero, id.def],
    ring}
end 

def square (n : ℕ) : ℕ := n^2 

theorem sum_identity_2 (n : ℕ) : 6 * mysum square n =  n*(n+1)*(2*n+1)  := 
begin 
    induction n with k hk,
    {refl}, 
    {rw mysum,
    rw mul_add,
    rw hk,
    unfold square,
    repeat {rw succ_eq_add_one},
    simp only [add_assoc, add_zero],
    ring}
end 

--could have more similar identities. The proofs are almost all the same. Could be a good confidence building goal to have some examples and then similar problems without solutions.



#eval factorial 0
#eval factorial 10

/-discussion of how @[simp] lets you give simp more stuff. Show that before
the @[simp] statements the example below doesn't work, but it does after
-/

-- example : factorial 4 = 4 * factorial 3 := 
-- begin 
--     simp,
--     ring,
-- end 

@[simp]
lemma factorial0 : factorial 0 = 1 := rfl
@[simp]
lemma factorial1 : factorial 1 = 1 := rfl
@[simp]
lemma factorial2 : factorial 2 = 2 := rfl
@[simp]
lemma factorial3 : factorial 3 = 6 := rfl
@[simp]
lemma factorial4 : factorial 4 = 24 := rfl

example : factorial 4 = 4 * factorial 3 := 
begin 
    simp,
    ring,
end 

--these feel unnecessary, but could be a good teaching moment if we can't fix it?
@[simp]
lemma stupid1 (h : 2 ≥ 4) : false := 
begin
    linarith,
end
@[simp]
lemma stupid2 (h : 3 ≥ 4) : false :=  --idk why linarith isn't resolving this in my proof
begin
    linarith,
end

lemma two_pow_nonneg (n : ℕ) : 2 ^ n ≥ 0 := 
begin 
linarith,
end



--this is a bit long but conceptually I think it's within reach. 
--How could we break it up into multiple steps/subgoals?
theorem identity_3 (n : ℕ) (h : n ≥ 4) : factorial n ≥ 2^n := 
begin 
cases n, linarith,
cases n, linarith,
cases n, 
    simp only [ge_iff_le, factorial2, nat_zero_eq_zero, nat.pow_succ], 
    norm_num,
    apply stupid1,
    exact h,
cases n, 
    simp only [ge_iff_le, factorial2, nat_zero_eq_zero, nat.pow_succ], 
    norm_num,
    apply stupid2,
    exact h,
repeat {rw succ_eq_add_one},
ring,
clear h,
induction n with k hk,
simp,
exact le_add_left (2 ^ 4) (5 + 3),
rw succ_add,
rw factorial,
rw nat.pow_succ,
have h1 : succ (k+4) ≥ 2, 
    rw succ_eq_add_one,
    linarith,
calc succ (k + 4) * factorial (k + 4) ≥ succ (k+4) * 2 ^ (k + 4) : by sorry
    ... ≥ 2*2^(k+4) : by refine mul_mono_nonneg (by linarith) h1
    ... = 2^(k+4) * 2 : by rw mul_comm
    ... = 2^succ (k+4) : by rw ← nat.pow_succ,
end 

#check mul_mono_nonneg




--me trying to find these identities in mathlib
example (a b c d: ℕ) (h1 : a > b) (h2 : c > d) : a*c > b*d := 
begin 
    simp,
    sorry,
end

example (a b c : ℕ) (h : a < b) : a*c < b*c := 
begin 
    sorry,
end

#check pow_two_nonneg