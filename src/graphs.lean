-- graphs as 1D CW complexes

import data.list.perm
import algebra.big_operators
import data.nat.parity
import data.zmod.basic
import tactic
import myequiv

namespace graphs

open function
open equiv
open_locale big_operators

universe u
variables {V : Type u}

-- For this definition of a graph, V is the edge set and D is the set
-- of "darts," which comprise the two ends of an edge.  An edge is
-- modeled as an orbit of a fixed-point-free involution of the darts.
--
-- In the language of CW complexes, ϕ is the attachment map for the
-- boundary of each 1-cell.
structure graph (V : Type u) :=
(D : Type u) (ε : perm D) (ϕ : D → V) (ε_inv : involutive ε) (ε_fp_free : ¬has_fixed_point ε)

-- Vertex adjacency relation
def graph.adj (g : graph V) (v w : V) : Prop := ∃ (d : g.D), v = g.ϕ d ∧ w = g.ϕ (g.ε d)

def swap {α : Type u} (p : α × α) : α × α := ⟨p.2, p.1⟩

inductive sym2_rel (α : Type u) : (α × α) → (α × α) → Prop
| refl (x y : α) : sym2_rel ⟨x,y⟩ ⟨x,y⟩
| swap (x y : α) : sym2_rel ⟨x,y⟩ ⟨y,x⟩

-- The symmetric square is the cartesian product α × α modulo `swap`.
def sym2 (α : Type u) := quot (sym2_rel α)

-- The type sym2 α is the same thing as sets with exactly one or two elements.
def sym2_to_finset {α : Type u} [decidable_eq α] (s : sym2 α) : finset α :=
begin
  induction s,
  exact {s.1, s.2},
  cases s_p, refl,
  ext, simp, rw or_comm,
end

def sym2_to_finset_card_eq {α : Type u} [decidable_eq α] (s : sym2 α) : (sym2_to_finset s).card = 1 ∨ (sym2_to_finset s).card = 2 :=
begin
  induction s,
  cases s,
  by_cases heq : s_fst = s_snd,
  left, rw heq, simp [sym2_to_finset, quot.rec],
  right,
  change ({s_fst, s_snd} : finset α).card = 2,
  dsimp only [has_insert.insert, finset.val],
  have nmem : s_fst ∉ ({s_snd} : multiset α), by simpa,
  have h := multiset.ndinsert_of_not_mem nmem,
  simp_rw [h], simp [finset.card],
end

-- def sym2_to_finset_equiv {α : Type u} [decidable_eq α] : sym2 α ≃ {x : finset α // x.card = 1 ∨ x.card = 2} :=
-- begin
--   use (λ s, ⟨sym2_to_finset s, sym2_to_finset_card_eq s⟩),
-- end

@[reducible] def edge_setoid (g : graph V) := perm.psetoid g.ε
@[reducible] def graph.edges (g : graph V) := quotient (edge_setoid g)

@[reducible] def graph.dart_edge (g : graph V) (d : g.D) : g.edges := @quotient.mk _ (edge_setoid g) d

instance {g : graph V} [decidable_eq g.D] [fintype g.D] (d₁ d₂ : g.D) : decidable (@setoid.r _ (edge_setoid g) d₁ d₂) :=
begin
  change decidable (perm.same_cycle g.ε d₁ d₂),
  apply_instance,
end

-- There is a map g.edges → sym2 V given by taking the vertices
-- incident to the given edge's darts.
def graph.edges.boundary {g : graph V} (e : g.edges) : sym2 V :=
begin
  induction e, exact quot.mk (sym2_rel V) ⟨g.ϕ e, g.ϕ (g.ε e)⟩,
  simp, apply quot.sound,
  have h := involution_same_cycle g.ε g.ε_inv e_p,
  cases h,
  rw h, exact sym2_rel.refl _ _,
  rw ← h, rw g.ε_inv, exact sym2_rel.swap _ _,
end

-- Get the boundary as a 1- or 2-element set.
def graph.edges.boundary_set {g : graph V} [decidable_eq V] (e : g.edges) : {x : finset V // x.card = 1 ∨ x.card = 2} :=
⟨sym2_to_finset e.boundary, sym2_to_finset_card_eq e.boundary⟩

inductive rel_darts (r : V → V → Prop) : Type u
| loop (v : V) (h : r v v) : bool → rel_darts
| edge (v w : V) (neq : v ≠ w) (h : r v w) : rel_darts

def rel_darts.ε₀ {r : V → V → Prop} (sym : symmetric r) : rel_darts r → rel_darts r
| (rel_darts.loop v h b) := rel_darts.loop v h (!b)
| (rel_darts.edge v w neq h) := rel_darts.edge w v (ne.symm neq) (sym h)

lemma rel_darts.ε₀.involutive {r : V → V → Prop} (sym : symmetric r) : involutive (rel_darts.ε₀ sym) :=
begin
  intro x,
  cases x,
  simp_rw [rel_darts.ε₀, bnot_bnot], tauto,
  simp [rel_darts.ε₀],
end

lemma rel_darts.ε₀.fixed_point_free {r : V → V → Prop} (sym : symmetric r) : ¬has_fixed_point (rel_darts.ε₀ sym) :=
begin
  rintro ⟨x, h⟩,
  cases x, simp [rel_darts.ε₀] at h, cases x_a, tauto, tauto,
  simp [rel_darts.ε₀] at h, tauto,
end

def rel_darts.ε {r : V → V → Prop} (sym : symmetric r) : perm (rel_darts r) :=
involutive.to_equiv (rel_darts.ε₀ sym) (rel_darts.ε₀.involutive sym)

def rel_darts.ϕ (r : V → V → Prop) : rel_darts r → V
| (rel_darts.loop v _ _) := v
| (rel_darts.edge v _ _ _) := v

-- Construct a graph from a relation.  There is exactly one edge
-- between x and y if r x y.  This includes the case of having exactly
-- one loop edge at x if r x x.
def from_rel {r : V → V → Prop} (sym : symmetric r) : graph V :=
⟨rel_darts r, rel_darts.ε sym, rel_darts.ϕ r, rel_darts.ε₀.involutive sym, rel_darts.ε₀.fixed_point_free sym⟩

-- This theorem asserts that the graph produced by from_rel has the correct adjacency relation.
theorem from_rel_recover_adj [decidable_eq V] {r : V → V → Prop} (sym : symmetric r) : ∀ (v w : V), r v w ↔ (from_rel sym).adj v w :=
begin
  intros v w,
  by_cases heq : v = w, {
    rw ←heq,
    split,
    intro h,
    use rel_darts.loop v h tt,
    dsimp [from_rel, rel_darts.ε, rel_darts.ε₀, involutive.to_equiv, rel_darts.ϕ],
    tauto,
    rintro ⟨d, h⟩,
    cases d;
    dsimp [from_rel, rel_darts.ϕ, rel_darts.ε, involutive.to_equiv, rel_darts.ε₀] at h,
    rwa h.1,
    rwa [←h.1, ←h.2] at d_h,
  }, {
    split,
    intro h,
    use rel_darts.edge v w heq h,
    dsimp [from_rel, rel_darts.ε, rel_darts.ε₀, involutive.to_equiv, rel_darts.ϕ],
    tauto,
    rintro ⟨d, h⟩,
    cases d;
    dsimp [from_rel, rel_darts.ϕ, rel_darts.ε, involutive.to_equiv, rel_darts.ε₀] at h,
    rw [h.1, h.2] at heq, tauto,
    rwa [h.1, h.2],
  },
end

def graph.darts_at (g : graph V) (v : V) := {d : g.D | g.ϕ d = v}

lemma graph.darts_at.as_filter (g : graph V) [decidable_eq g.D] [decidable_eq V] [fintype g.D] (v : V)
: g.darts_at v = ↑(finset.univ.filter (λ d, g.ϕ d = v)) :=
begin
  dunfold graph.darts_at,
  simp,
end

instance fintype.darts_at (g : graph V) [decidable_eq g.D] [decidable_eq V] [fintype g.D] (v : V) : fintype (g.darts_at v) :=
begin
  rw graph.darts_at.as_filter g v,
  apply_instance,
end

lemma graph.darts_at.as_filter_card (g : graph V) [decidable_eq g.D] [decidable_eq V] [fintype g.D]  (v : V)
: fintype.card (g.darts_at v) = (finset.univ.filter (λ d, g.ϕ d = v)).card :=
begin
  simp_rw [graph.darts_at.as_filter g v],
  set fs := finset.filter (λ (d : g.D), g.ϕ d = v) finset.univ with fs_eq,
  set fss : set g.D := ↑fs with fss_eq,
  set fst : Type u := ↥fss with fst_eq,
  have equ_card : fintype.card fst = fintype.card fss, refl,
  transitivity (fintype.card fst),
  congr,
  rw equ_card, simp, refl,
end

-- The degree of a vertex is the number of incident darts.  For
-- non-loop edges, this works out as one would expect.  Loop edges are
-- counted twice, also as one would expect.
def graph.deg (g : graph V) [decidable_eq g.D] [decidable_eq V] [fintype g.D] (v : V) : ℕ := fintype.card (g.darts_at v)

def graph.nverts [fintype V] (g : graph V) : ℕ := fintype.card V
def graph.nedges (g : graph V) [fintype g.D] [decidable_eq g.D] : ℕ := fintype.card g.edges
def graph.ndarts (g : graph V) [fintype g.D] : ℕ := fintype.card g.D

lemma edges_have_two_darts (g : graph V) [fintype g.D] [decidable_eq g.D] (e : g.edges)
: (finset.univ.filter (λ d, g.dart_edge d = e)).card = 2 :=
begin
  induction e,
  have h : (finset.univ.filter (λ d, g.dart_edge d = g.dart_edge e)) = {e, g.ε e}, {
    ext, split, {
      intro h,
      rw finset.mem_filter at h,
      have h₂ := h.2,
      simp at h₂,
      change perm.same_cycle g.ε a e at h₂,
      cases equiv.involution_same_cycle g.ε g.ε_inv h₂,
      rw h_1, simp,
      rw ← h_1, rw g.ε_inv, simp,
    }, {
      intro h,
      simp at h, cases h,
      rw h, simp,
      rw finset.mem_filter, use fintype.complete a, simp, use 1, rw h, simp, rw g.ε_inv,
    },
  },
  change (finset.filter (λ (d : g.D), g.dart_edge d = g.dart_edge e) finset.univ).card = 2,
  rw h,
  have hneq : e ≠ g.ε e := λ heq, g.ε_fp_free ⟨e, eq.symm heq⟩,
  have nmem : e ∉ ({g.ε e} : multiset g.D), by simpa,
  have h := multiset.ndinsert_of_not_mem nmem,
  simp [finset.card], simp at h, rw h, simp,
end

lemma graph.dart_edge_is_fintype_surj (g : graph V) [fintype g.D] [decidable_eq g.D] : finset.univ.image g.dart_edge = finset.univ :=
begin
  ext, split, intro h,
  apply fintype.complete,
  intro h,
  rw finset.mem_image,
  induction a, use a, split, apply fintype.complete, refl, refl,  
end

lemma graph.ndarts_eq_twice_nedges (g : graph V) [fintype g.D] [decidable_eq g.D] : g.ndarts = 2 * g.nedges :=
begin
  calc g.ndarts = ∑ (d : g.D), 1 : by simp; refl
            ... = ∑ d, (λ e, 1) (g.dart_edge d) : by simp
            ... = ∑ e in finset.univ.image g.dart_edge, (finset.univ.filter (λ d, g.dart_edge d = e)).card •ℕ ((λ e, 1) e)
                : by rw finset.sum_comp
            ... = ∑ e in finset.univ.image g.dart_edge, (finset.univ.filter (λ d, g.dart_edge d = e)).card
                : by dsimp; simp
            ... = ∑ (e : g.edges), (finset.univ.filter (λ d, g.dart_edge d = e)).card : by rw g.dart_edge_is_fintype_surj
            ... = ∑ (e : g.edges), 2 : by simp_rw [edges_have_two_darts]
            ... = 2 * g.nedges : by simp; ring,
end

lemma graph.ndarts_eq_sum_degrees (g : graph V) [fintype g.D] [decidable_eq g.D] [fintype V] [decidable_eq V]
: g.ndarts = ∑ (v : V), g.deg v :=
begin
  have him : finset.univ.image g.ϕ ⊆ finset.univ, apply finset.subset_univ,
  rw ← finset.sum_sdiff him,
  have hzero : ∑ (x : V) in finset.univ \ finset.image g.ϕ finset.univ, (finset.univ.filter (λ (d : g.D), g.ϕ d = x)).card = 0, {
    rw ← finset.sum_filter_ne_zero, simp,
    intros v hd hnf,
    simp [hd],
  },
  dunfold graph.deg,
  simp_rw [graph.darts_at.as_filter_card g, hzero],
  rw ← finset.card_eq_sum_card_image,
  simp,
  refl,
end

lemma graph.handshake (g : graph V) [fintype g.D] [decidable_eq g.D] [fintype V] [decidable_eq V]
: ∑ (v : V), g.deg v = 2 * g.nedges :=
begin
  rw ← graph.ndarts_eq_sum_degrees,
  rw ← graph.ndarts_eq_twice_nedges,
end

lemma zmod_nz (n : zmod 2) : n ≠ 0 ↔ n = 1 :=
begin
  split,
  intro h,
  cases n, cases n_val, norm_cast at h,
  cases n_val, refl,
  change n_val + 2 < 2 at n_is_lt, exfalso, linarith [n_is_lt],
  intro h, subst n,
  intro abs, cases abs,
end

lemma zmod_red_opts (n : ℕ) : (↑n : zmod 2) = 0 ∨ (↑n : zmod 2) = 1 :=
begin
  by_cases h : (↑n : zmod 2) = 0,
  left, exact h,
  right, rwa ←zmod_nz,
end

lemma zmod_even (n : ℕ) : (↑n : zmod 2) = 0 ↔ n.even :=
begin
  rw nat.even_iff,
  split,
  intro h,
  have h'' := congr_arg (λ (x : zmod 2), x.val) h,
  change (↑n : zmod 2).val = 0 at h'',
  rwa zmod.val_cast_nat at h'',
  intro h,
  rw ←zmod.val_cast_nat at h,
  simp at h,
  exact h,
end

lemma zmod_odd (n : ℕ) : (↑n : zmod 2) = 1 ↔ ¬n.even :=
begin
  have h := not_iff_not_of_iff (zmod_even n),
  rw ←zmod_nz,
  exact h,
end

-- A finite graph has an even number of odd-degree vertices
lemma graph.handshake_mod_2 (g : graph V) [fintype g.D] [decidable_eq g.D] [fintype V] [decidable_eq V]
: (finset.univ.filter (λ v, ¬(g.deg v).even)).card.even :=
begin
  have h₁ := graph.handshake g,
  let red : ℕ →+ zmod 2 := nat.cast_add_monoid_hom _,
  have h₂ := congr_arg red h₁,
  rw add_monoid_hom.map_sum red g.deg finset.univ at h₂,
  have him : finset.univ.filter (λ v, red (g.deg v) = 1) ⊆ finset.univ, apply finset.subset_univ,
  rw ← finset.sum_sdiff him at h₂,
  have hzero : ∑ (x : V) in finset.univ \ finset.univ.filter (λ (v : V), red (g.deg v) = 1), red (g.deg x) = 0, {
    rw ← finset.sum_filter_ne_zero, simp,
    have hfilt : finset.filter (λ (x : V), ¬red (g.deg x) = 0) (finset.univ \ finset.filter (λ (v : V), red (g.deg v) = 1) finset.univ) = ∅, {
      ext, simp, intro h, rw ←zmod_nz at h, simp at h, exact h,
    },
    simp at hfilt,
    rw hfilt,
    simp,
  },
  rw hzero at h₂,
  have h₃ : ∑ (x : V) in finset.univ.filter (λ (v : V), red (g.deg v) = 1), red (g.deg x) = ∑ (x : V) in finset.univ.filter (λ (v : V), red (g.deg v) = 1), 1, {
    rw finset.sum_filter,
    have hite : ∀ n : ℕ, (if red n = 1 then red n else 0) = red n, {
      intro n, split_ifs, refl, rw ←zmod_nz at h, simp at h, simp [h],
    },
    simp_rw [hite],
    rw finset.sum_filter,
    have hite' : ∀ n : ℕ, (if red n = 1 then 1 else 0) = red n, {
      intro n, split_ifs, cc, rw ←zmod_nz at h, simp at h, simp [h],
    },
    simp_rw [hite'],
  },
  rw h₃ at h₂,
  simp at h₂,
  rw ← zmod_even,
  simp_rw [zmod_odd] at h₂,
  simp at h₂,
  exact h₂,
end

-- Given an odd-degree vertex v, the number of odd-degree vertices not equal to v is odd.
lemma graph.card_other_odd_vertices_is_odd (g : graph V) [fintype g.D] [decidable_eq g.D] [fintype V] [decidable_eq V]
(v : V) (hv : ¬(g.deg v).even)
: ¬(finset.univ.filter (λ w, ¬(g.deg w).even ∧ v ≠ w)).card.even :=
begin
  rw ←finset.filter_filter,
  rw finset.filter_ne,
  rcases graph.handshake_mod_2 g with ⟨k, h⟩,
  set s := finset.univ.filter (λ v : V, ¬(g.deg v).even) with s_eq,
  have hmem : v ∈ s, {
    simpa,
  },
  have h'' := finset.card_erase_of_mem hmem,
  have hnz := finset.card_ne_zero_of_mem hmem,
  rw ←s_eq at h ⊢,
  rw h at hnz h'', cases k, exfalso, simp at hnz, exact hnz,
  change _ = 2 * k + 1 at h'',
  rw h'',
  exact nat.two_not_dvd_two_mul_add_one k,
end

-- Given an odd-degree vertex, there is another odd-degree vertex.
lemma graph.exist_other_odd_vertex (g : graph V) [fintype g.D] [decidable_eq g.D] [fintype V] [decidable_eq V]
(v : V) (hv : ¬(g.deg v).even)
: ∃ (w : V), w ≠ v ∧ ¬(g.deg w).even :=
begin
  have h := graph.card_other_odd_vertices_is_odd g v hv,
  rw ← nat.even_succ at h,
  rcases h with ⟨k, h⟩,
  change _ + 1 = _ at h,
  cases k,
  exfalso, linarith,
  rw nat.succ_eq_add_one at h,
  have ne : (finset.univ.filter (λ (w : V), ¬(g.deg w).even ∧ v ≠ w)).nonempty, {
    rw ← finset.card_pos,
    linarith,
  },
  induction ne,
  use ne_w,
  simp at ne_h, tauto,
end

end graphs
