import data.equiv.basic
import group_theory.perm.cycles

open function

namespace equiv

universe u

def has_fixed_point {α : Type u} (f : α → α) := ∃ x, f x = x

@[simp]
lemma symm_involution {α : Type u} (f : perm α) (inv : involutive f) : f.symm = f :=
begin
  ext,
  calc f.symm x = f.symm (f (f x)) : by rw inv x
            ... = (f.symm ∘ f) (f x) : by refl
            ... = id (f x) : by rw symm_comp_self
            ... = f x : by refl,
end

@[simp]
lemma involution_comp_involution {α : Type u} (f : perm α) (inv : involutive f) : f ∘ f = id :=
begin
  ext, exact inv x,
end

lemma involution_pow_nat_reduce {α : Type u} (f : perm α) (inv : involutive f) (n : ℕ) : f ^ n = 1 ∨ f ^ n = f :=
begin
  induction n,
  left, simp,
  rw [nat.succ_eq_add_one, pow_succ'],
  cases n_ih,
  right, rw n_ih, simp,
  left, rw n_ih, ext, simp, rw inv,
end

lemma involution_pow_reduce {α : Type u} (f : perm α) (inv : involutive f) (n : ℤ) : f ^ n = 1 ∨ f ^ n = f :=
begin
  induction n, 
  exact involution_pow_nat_reduce f inv n,
  have h : f ^-[1+n] = f⁻¹^(1+n), {
    rw gpow_neg_succ_of_nat,
    change (f ^ (↑(n.succ):ℤ))⁻¹ = _,
    rw ← inv_gpow,
    change f⁻¹ ^ (n+1) = _,
    rw add_comm,
  },
  change _ = f.symm ^ (1 + n) at h,
  conv at h { to_rhs, rw symm_involution f inv, },
  rw h,
  exact involution_pow_nat_reduce f inv (1+n),
end

lemma involution_same_cycle {α : Type u} (f : perm α) (inv : involutive f) {x y : α} (h : perm.same_cycle f x y) : x = y ∨ f x = y :=
begin
  rcases h with ⟨n, h⟩,
  have h' := involution_pow_reduce f inv n,
  cases h',
  left, rwa h' at h,
  right, rwa h' at h,
end

@[simp]
lemma symm_trans_eq_trans_sym {α : Type u} (f g : equiv α α) : (f.trans g).symm = g.symm.trans f.symm :=
begin
  ext, simp,
end

namespace perm

lemma same_cycle.equiv {β : Type u} (f : perm β) : equivalence (perm.same_cycle f) :=
⟨perm.same_cycle.refl f, (λ _ _ r, perm.same_cycle.symm f r), (λ _ _ _ r1 r2, perm.same_cycle.trans f r1 r2)⟩


def psetoid {α : Type u} (f : perm α) : setoid α := ⟨perm.same_cycle f, equiv.perm.same_cycle.equiv f⟩

instance psetoid.quotient.fintype {α : Type u} (f : perm α) [fintype α] [decidable_eq α]
: fintype (quotient (psetoid f)) :=
begin
  have rel_inst : decidable_rel (psetoid f).r, change decidable_rel (perm.same_cycle _), apply_instance,
  apply @quotient.fintype _ _ (psetoid f) rel_inst,
end


end perm


end equiv
